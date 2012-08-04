{-# Language TemplateHaskell, QuasiQuotes, TypeSynonymInstances, FlexibleInstances, UndecidableInstances, OverlappingInstances, IncoherentInstances #-}

module Language.Egison.Quote(egison, TypeSignature) where

import Language.Haskell.TH
import Language.Haskell.TH.Syntax
import Language.Haskell.TH.Quote

import Text.Parsec

import Language.Egison.Core
import Language.Egison.Types hiding (Type)
import Language.Egison.Parser
import Language.Egison.Variables

import Data.Either
import Data.Ratio
import Control.Monad.Error hiding (lift)
import Control.Monad.Trans hiding (lift)
import Control.Arrow
import Control.Applicative hiding ((<|>), many)

import System.IO.Unsafe (unsafePerformIO)

class IsEgisonExpr a where
    toEgisonExpr :: a -> EgisonExpr

instance Integral i => IsEgisonExpr i where toEgisonExpr = NumberExpr . fromIntegral
instance IsEgisonExpr Char where toEgisonExpr = CharExpr
instance IsEgisonExpr String where toEgisonExpr = StringExpr
instance IsEgisonExpr Bool where toEgisonExpr = BoolExpr
instance IsEgisonExpr Float where toEgisonExpr = FloatExpr . realToFrac
instance IsEgisonExpr Double where toEgisonExpr = FloatExpr
instance IsEgisonExpr a => IsEgisonExpr [a] where toEgisonExpr = CollectionExpr . map (ElementExpr . toEgisonExpr)
instance (IsEgisonExpr a, IsEgisonExpr b) => IsEgisonExpr (a, b) where
  toEgisonExpr (x, y) = TupleExpr $ [ElementExpr . toEgisonExpr $ x, ElementExpr . toEgisonExpr $ y]
instance (IsEgisonExpr a, IsEgisonExpr b, IsEgisonExpr c) => IsEgisonExpr (a, b, c) where
  toEgisonExpr (x, y, z) = TupleExpr $ [ElementExpr . toEgisonExpr $ x, ElementExpr . toEgisonExpr $ y, ElementExpr . toEgisonExpr $ z]
instance (IsEgisonExpr a, IsEgisonExpr b, IsEgisonExpr c, IsEgisonExpr d) => IsEgisonExpr (a, b, c, d) where
  toEgisonExpr (w, x, y, z) = TupleExpr $ [ElementExpr . toEgisonExpr $ w, ElementExpr . toEgisonExpr $ x, ElementExpr . toEgisonExpr $ y, ElementExpr . toEgisonExpr $ z]

runIOThrowsError :: IOThrowsError a -> IO a
runIOThrowsError = fmap ignore . runErrorT
    where ignore = either (error . show) id

-- * QuasiQuoter

-- | QuasiQuoter for egison expression
-- The format is: [egison | <egison-expression> :: <type-signature>]
-- Type signature is defined as follows
-- > <Typ> = Bool | Int | Double | Float | Double | Char | String | [<Typ>] | (<Typ>, <Typ>, ..., <Typ>) | <Typ> -> <Typ> -> ... <Typ>
-- The constant expression is compile-time evaluated.
-- lambda abstraction(egison function) is run-time evaluated by using 'Language.Egison.Core.eval' and 'System.Unsafe.unsafePerformIO'.
-- For more detailed usage, please refer to <https://github.com/xenophobia/Egison-Quote>. 
egison :: QuasiQuoter
egison = QuasiQuoter {
           quoteExp = (\q -> do
                         let (expr, typ) = extractValue . readQuote $ q
                         val <- evalEgison expr
                         toHaskellExpQ val typ),
           quotePat = error "Not implemented pat-quote.",
           quoteType = error "Not implemented type-quote.",
           quoteDec = error "Not implemented dec-quote."
         }

-- * Type

-- | The type of type signature of egison expression
data TypeSignature = CharTS | StringTS | BoolTS | IntTS | IntegerTS | FloatTS | DoubleTS
                   | TupleTS [TypeSignature] | ListTS TypeSignature 
                   | ArrowTS [TypeSignature] TypeSignature deriving (Show)

-- Generate [ EgisonVal -> (corresponding Haskell Value) ] function from TypeSignature
converter :: TypeSignature -> ExpQ
converter CharTS = [| \(Char x) -> x |]
converter StringTS = [| \(String x) -> x |]
converter BoolTS = [| \(Bool x) -> x |]
converter IntTS = [| \(Number x) -> (fromIntegral x) :: Int |]
converter IntegerTS = [| \(Number x) -> x |]
converter DoubleTS = [| \(Float x) -> x |]
converter FloatTS = [| \(Float x) -> (realToFrac x) :: Float |]
converter (TupleTS ts) = do
  patvars <- replicateM (length ts) $ newName "x"
  lamE [conP 'Tuple [listP $ map varP patvars]] (foldl (\acc (x, t) -> appE acc (appE (converter t) (varE x))) (conE $ tupleDataName (length ts)) (zip patvars ts))
converter (ListTS t) = [| \(Collection vs) -> map $(converter t) vs |]
converter (ArrowTS _ _) = error "Invarid return type: t1 -> t2."

-- TypeSignature -> (corresponding Haskell Type)
tsToType :: TypeSignature -> TypeQ
tsToType CharTS = [t| Char |]
tsToType StringTS = [t| String |]
tsToType BoolTS = [t| Bool |]
tsToType IntTS = [t| Int |]
tsToType IntegerTS = [t| Integer |]
tsToType DoubleTS = [t| Double |]
tsToType FloatTS = [t| Float |]
tsToType (TupleTS ts) = foldl appT (tupleT (length ts)) (map tsToType ts)
tsToType (ListTS t) = appT listT (tsToType t)
tsToType (ArrowTS t1 t2) = appT (foldl appT arrowT (map tsToType t1)) (tsToType t2)

-- Parser for TypeSignature
parseType = do
  t1_ <- many (try $ lexeme parseType' <* lexeme (string "->"))
  t2 <- lexeme parseType'
  case t1_ of
    [] -> return t2
    t1 -> return (ArrowTS t1 t2)

parseType' = (string "Char" >> return CharTS)
             <|> (string "String" >> return StringTS)
             <|> (string "Bool" >> return BoolTS)
             <|> (string "Int" >> return IntTS)
             <|> (string "Integer" >> return IntegerTS)
             <|> (string "Float" >> return FloatTS)
             <|> (string "Double" >> return DoubleTS)
             <|> parens (do thd <- lexeme parseType'
                            ttl <- many (lexeme (char ',') >> lexeme parseType')
                            return $ if null ttl then thd else TupleTS (thd:ttl))
             <|> brackets (ListTS <$> lexeme parseType')

readQuote :: String -> ThrowsError (EgisonExpr, TypeSignature)
readQuote = readOrThrow $ do
  spaces
  expr <- lexeme parseExpr
  lexeme (string "::")
  typ <- lexeme parseType
  return (expr, typ)

instance Lift InnerExpr where
  lift (ElementExpr x) = appE (conE 'ElementExpr) (lift x)
  lift (SubCollectionExpr x) = appE (conE 'SubCollectionExpr) (lift x)

instance Lift ArrayElementExpr where
  lift (AElementExpr x) = appE (conE 'AElementExpr) (lift x)
  lift (AInnerArrayExpr l) = appE (conE 'AInnerArrayExpr) (lift l)

instance Lift Args where
  lift (AVar x) = appE (conE 'AVar) (lift x)
  lift (ATuple l) = appE (conE 'ATuple) (lift l)

instance Lift EgisonExpr where
  lift (CharExpr x) = appE (conE 'CharExpr) (lift x)
  lift (BoolExpr x) = appE (conE 'BoolExpr) (lift x)
  lift (NumberExpr x) = appE (conE 'NumberExpr) (lift x)
  lift (FloatExpr x) = let (n, d) = (numerator &&& denominator) (realToFrac x) in
                       (appE (conE 'FloatExpr)
                        (appE (varE 'fromRational)
                         (appsE [(varE '(%)),
                                 (litE (integerL n)),
                                 (litE (integerL d))])))
  lift (VarExpr x l) = appsE [conE 'VarExpr, lift x, lift l]
  lift (MacroVarExpr x l) = appsE [conE 'MacroVarExpr, lift x, lift l]
  lift (PatVarOmitExpr x) = appE (conE 'PatVarOmitExpr) (lift x)
  lift (VarOmitExpr x) = appE (conE 'VarOmitExpr) (lift x)
  lift (PatVarExpr x l) = appsE [conE 'PatVarExpr, lift x, lift l]
  lift WildCardExpr = conE 'WildCardExpr
  lift (ValuePatExpr x) = appE (conE 'ValuePatExpr) (lift x)
  lift (CutPatExpr x) = appE (conE 'CutPatExpr) (lift x)
  lift (NotPatExpr x) = appE (conE 'NotPatExpr) (lift x)
  lift (AndPatExpr l) = appE (conE 'AndPatExpr) (lift l)
  lift (OrPatExpr l) = appE (conE 'OrPatExpr) (lift l)
  lift (PredPatExpr x l) = appsE [conE 'PredPatExpr, lift x, lift l]
  lift (InductiveDataExpr x y) = appsE [conE 'InductiveDataExpr, lift x, lift y]
  lift (TupleExpr l) = appsE [conE 'TupleExpr, lift l]
  lift (CollectionExpr l) = appsE [conE 'CollectionExpr, lift l]
  lift (ArrayExpr l) = appsE [conE 'ArrayExpr, lift l]
  lift (FuncExpr l x) = appsE [conE 'FuncExpr, lift l, lift x]
  lift (MacroExpr l x) = appsE [conE 'MacroExpr, lift l, lift x]
  lift (LoopExpr v w x y z) = appsE [conE 'LoopExpr, lift v, lift w, lift x, lift y, lift z]
  lift (ParamsExpr x y z) = appsE [conE 'ParamsExpr, lift x, lift y, lift z]
  lift (IfExpr x y z) = appsE [conE 'IfExpr, lift x, lift y, lift z]
  lift (LetExpr l x) = appsE [conE 'LetExpr, lift l, lift x]
  lift (LetRecExpr l x) = appsE [conE 'LetRecExpr, lift l, lift x]
  lift (DoExpr l x) = appsE [conE 'DoExpr, lift l, lift x]
  -- lift (TypeExpr x) = (appE (conE 'TypeExpr) (lift x))
  lift (MatchExpr x y z) = appsE [conE 'MatchExpr, lift x, lift y, lift z]
  lift (MatchAllExpr x y l) = appsE [conE 'MatchAllExpr, lift x, lift y, lift l]
  lift (GenerateArrayExpr x y) = appsE [conE 'GenerateArrayExpr, lift x, lift y]
  lift (ApplyExpr x l) = appsE [conE 'ApplyExpr, lift x, lift l]
  lift SomethingExpr = conE 'SomethingExpr
  lift x = error "Not implemented lift"

toHaskellExpQ :: EgisonVal -> TypeSignature -> ExpQ
toHaskellExpQ (Char c) CharTS = litE (charL c)
toHaskellExpQ (String s) StringTS = litE (stringL s)
toHaskellExpQ (Bool b) BoolTS = conE (if b then 'True else 'False)
toHaskellExpQ (Number n) IntegerTS = (litE (integerL n))
toHaskellExpQ (Number n) IntTS = appE (varE 'fromIntegral) (litE (integerL n))
toHaskellExpQ (Float b) FloatTS = litE (rationalL . toRational $ b)
toHaskellExpQ (Float b) DoubleTS = litE (rationalL . toRational $ b)
toHaskellExpQ (Collection xs) (ListTS t) = listE $ map (flip toHaskellExpQ t) xs
toHaskellExpQ (Tuple xs) (TupleTS ts) = tupE $ zipWith toHaskellExpQ xs ts
toHaskellExpQ (Func (ATuple args) expr _) (ArrowTS t1 t2) | length args == length t1 = do
  env <- newName "env"
  let (argsName, argsType) = unzip . concat $ zipWith argsExpand args t1
      argsExpr = zipWith (\aname atype -> sigE (varE (mkName aname)) atype) argsName argsType
      bindEnv = bindS (varP env) [|liftIO primitiveBindings|]
      loadEnv = noBindS [|liftIO (loadLibraries $(varE env))|]
      bindExprs = zipWith (\aname aexpr -> noBindS [|defineVar $(varE env) (aname, []) =<< (liftIO $ makeClosure $(varE env) (toEgisonExpr $(aexpr)))|]) argsName argsExpr
  (lamE (map toHaskellArgsPat args)
   (appE (varE 'unsafePerformIO) 
    (appE (varE 'runIOThrowsError)
     (doE $ bindEnv : loadEnv : (bindExprs ++ [noBindS (appE (appE (varE 'fmap) (converter t2)) [|eval $(varE env) expr|])])))))
toHaskellExpQ e t = error $ "Invarid expression or type: " ++ show e ++ " :: " ++ show t

argsExpand :: Args -> TypeSignature -> [(String, TypeQ)]
argsExpand (AVar a) t = [(a, tsToType t)]
argsExpand (ATuple as) (TupleTS ts) = concat $ zipWith argsExpand as ts
argsExpand _ _ = error "Invarid type."

toHaskellArgsPat :: Args -> PatQ
toHaskellArgsPat (AVar a) = varP (mkName a)
toHaskellArgsPat (ATuple as) = tupP $ map toHaskellArgsPat as

evalEgison :: EgisonExpr -> Q EgisonVal
evalEgison expr = do
  env <- runIO primitiveBindings
  runIO $ loadLibraries env
  runIO $ runIOThrowsError $ eval env expr
