-----------------------------------------------------------------------------
-- |
-- Module      :  Language.Egison.Quote
-- Copyright   :  (c) Takuya Kuwahara 2012
-- License     :  MIT
-- 
-- Maintainer  :  kuwahara111011@gmail.com
-- Stability   :  unstable
-- Portability :  non-portable (GHC-7.4.0 for GHC's extensions)
-- 
-- The quasi quotes for egison expression
-- 
-----------------------------------------------------------------------------   

{-# Language TemplateHaskell, QuasiQuotes, TypeSynonymInstances, FlexibleInstances, UndecidableInstances, ViewPatterns, OverlappingInstances, IncoherentInstances #-}

module Language.Egison.Quote(egison,
                             TypeSignature,
                             parseType,
                             parseQuote,
                             readQuote,
                             toHaskellExp) where

import Language.Haskell.TH
import Language.Haskell.TH.Syntax
import Language.Haskell.TH.Quote

import Text.Parsec
import Text.Parsec.String (Parser)

import Language.Egison.Core
import Language.Egison.Types hiding (Type, Parser)
import Language.Egison.Parser
import Language.Egison.Variables

import Data.Either
import Data.Ratio
import Data.Maybe
import Data.List

import Control.Monad.Error hiding (lift)
import Control.Monad.Trans hiding (lift)
import Control.Arrow
import Control.Applicative hiding ((<|>), many)

import System.IO.Unsafe (unsafePerformIO)

class IsEgisonExpr a where
    toEgisonExpr :: a -> EgisonExpr

instance IsEgisonExpr Int where toEgisonExpr = NumberExpr . fromIntegral
instance IsEgisonExpr Integer where toEgisonExpr = NumberExpr . fromIntegral
instance IsEgisonExpr Char where toEgisonExpr = CharExpr
instance IsEgisonExpr Bool where toEgisonExpr = BoolExpr
instance IsEgisonExpr Float where toEgisonExpr = FloatExpr . realToFrac
instance IsEgisonExpr Double where toEgisonExpr = FloatExpr
instance IsEgisonExpr String where toEgisonExpr = StringExpr
instance IsEgisonExpr a => IsEgisonExpr [a] where toEgisonExpr = CollectionExpr . map (ElementExpr . toEgisonExpr)
instance (IsEgisonExpr a, IsEgisonExpr b) => IsEgisonExpr (a, b) where
  toEgisonExpr (x, y) = TupleExpr $ [toEgisonExpr $ x, toEgisonExpr $ y]
instance (IsEgisonExpr a, IsEgisonExpr b, IsEgisonExpr c) => IsEgisonExpr (a, b, c) where
  toEgisonExpr (x, y, z) = TupleExpr $ [toEgisonExpr $ x, toEgisonExpr $ y, toEgisonExpr $ z]
instance (IsEgisonExpr a, IsEgisonExpr b, IsEgisonExpr c, IsEgisonExpr d) => IsEgisonExpr (a, b, c, d) where
  toEgisonExpr (w, x, y, z) = TupleExpr $ [toEgisonExpr $ w, toEgisonExpr $ x, toEgisonExpr $ y, toEgisonExpr $ z]

runIOThrowsError :: IOThrowsError a -> IO a
runIOThrowsError = fmap ignore . runErrorT
    where ignore = either (error . show) id

-- * QuasiQuoter

-- | 
-- QuasiQuoter for egison expression
--
-- The format is:
--
-- > expr := [egison | <egison-expression> :: <type-signature> |]
--
-- Type signature is defined as follows
--
-- > <Typ> = Bool | Int | Double | Float | Char | String | [<Typ>] | (<Typ>, <Typ>, ..., <Typ>) | <Typ> -> <Typ> -> ... <Typ>
--
-- Embedded Egison expression is run-time evaluated by using 'Language.Egison.Core.eval' and 'System.Unsafe.unsafePerformIO'.
-- For more detailed usage, please refer to <https://github.com/xenophobia/Egison-Quote>. 
egison :: QuasiQuoter
egison = QuasiQuoter {
           quoteExp = uncurry toHaskellExp . extractValue . readQuote,
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

-- * Parser

-- | Parser for TypeSignature
parseType :: Parser TypeSignature
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

-- | Parser for egison-quote
parseQuote :: Parser (EgisonExpr, TypeSignature)
parseQuote = do
  spaces
  expr <- lexeme parseExpr
  lexeme (string "::")
  typ <- lexeme parseType
  return (expr, typ)

-- | Read function for egison-quote
readQuote :: String -> ThrowsError (EgisonExpr, TypeSignature)
readQuote = readOrThrow parseQuote

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
  lift UndefinedExpr = conE 'UndefinedExpr
  lift x = error "Not implemented lift"

-- * Construction Exp

-- | construct Exp from Egison-expression and type signature
toHaskellExp :: EgisonExpr -> TypeSignature -> ExpQ
toHaskellExp (FuncExpr (TupleExpr args) expr) (ArrowTS t1 t2) | length args == length t1 = do
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
toHaskellExp expr typ = appE (converter typ) (evalEgisonTopLevel expr)
-- toHaskellExp expr typ = appE (converter typ) (appE (varE 'evalEgison) (lift expr))

childExpr :: EgisonExpr -> [EgisonExpr]
childExpr (CharExpr _) = []
childExpr (StringExpr _) = []
childExpr (BoolExpr _) = []
childExpr (NumberExpr _) = []
childExpr (FloatExpr _) = []
childExpr (VarExpr _ cs) = cs
childExpr (MacroVarExpr _ cs) = cs
childExpr (PatVarOmitExpr c) = [c]
childExpr (VarOmitExpr c) = [c]
childExpr (PatVarExpr _ cs) = cs
childExpr WildCardExpr = []
childExpr (ValuePatExpr c) = [c]
childExpr (CutPatExpr c) = [c]
childExpr (NotPatExpr c) = [c]
childExpr (AndPatExpr cs) = cs
childExpr (OrPatExpr cs) = cs
childExpr (PredPatExpr c cs) = c:cs
childExpr (InductiveDataExpr _ cs) = cs
childExpr (TupleExpr cs) = cs
childExpr (CollectionExpr cs) = map go cs
    where go (ElementExpr x) = x
          go (SubCollectionExpr x) = x
childExpr (ArrayExpr cs) = concatMap go cs
    where go (AElementExpr x) = [x]
          go (AInnerArrayExpr xs) = concatMap go xs
childExpr (FuncExpr c1 c2) = [c1, c2]
childExpr (MacroExpr _ c) = [c]
childExpr (LoopExpr _ _ c1 c2 c3) = [c1, c2, c3]
childExpr (ParamsExpr _ c1 c2) = [c1, c2]
childExpr (IfExpr c1 c2 c3) = [c1, c2, c3]
childExpr (LetExpr bs c) = c:concatMap go bs
    where go (x, y) = [x, y]
childExpr (LetRecExpr bs c) = c:map snd bs
childExpr (DoExpr bs c) = c:concatMap go bs
    where go (x, y) = [x, y]
-- childExpr (TypeExpr DestructInfoExpr)
childExpr (MatchExpr c1 c2 ms) = c1:c2:concatMap go ms
    where go (x, y) = [x, y]
childExpr (MatchAllExpr c1 c2 (c3, c4)) = [c1, c2, c3, c4]
childExpr (GenerateArrayExpr c1 c2) = [c1, c2]
childExpr (ApplyExpr c1 c2) = [c1, c2]
childExpr SomethingExpr = []
childExpr UndefinedExpr = []

variables :: EgisonExpr -> [String]
variables (VarExpr var cs) = var:concatMap variables cs
variables (MacroVarExpr var cs) = var:concatMap variables cs
variables (childExpr -> cs) = concatMap variables cs

argsExpand :: EgisonExpr -> TypeSignature -> [(String, TypeQ)]
argsExpand (PatVarExpr a _) t = [(a, tsToType t)]
argsExpand (TupleExpr as) (TupleTS ts) = concat $ zipWith argsExpand as ts
argsExpand _ _ = error "Invarid type."

toHaskellArgsPat :: EgisonExpr -> PatQ
toHaskellArgsPat (PatVarExpr a _) = varP (mkName a)
toHaskellArgsPat (TupleExpr as) = tupP $ map toHaskellArgsPat as

evalEgison :: EgisonExpr -> EgisonVal
evalEgison expr = unsafePerformIO $ do
  env <- primitiveBindings
  loadLibraries env
  runIOThrowsError $ eval env expr

toEgisonName :: String -> String
toEgisonName (reverse -> name) = reverse . tail . dropWhile (/= '_') $ name

evalEgisonTopLevel :: EgisonExpr -> ExpQ
evalEgisonTopLevel expr = do
  env <- newName "env"
  vars <- concatMap maybeToList <$> mapM lookupValueName (nub $ variables expr)
  let exprs = map (\var -> (varE var)) vars
  (appE (varE 'unsafePerformIO)
   (doE (
     [(varP env) `bindS` (varE 'primitiveBindings),
      noBindS (appE (varE 'loadLibraries) (varE env))] ++ 
     zipWith (\vname vexpr -> noBindS [|runIOThrowsError $ defineVar $(varE env) (toEgisonName vname, []) =<< (liftIO $ makeClosure $(varE env) (toEgisonExpr $(vexpr)))|]) (map show vars) exprs ++
     [noBindS (appE (varE 'runIOThrowsError) (appsE [varE 'eval, varE env, [|expr|]]))]
    )))