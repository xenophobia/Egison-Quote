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
                             parseType,
                             pickupAntiquote,
                             parseAntiquote,
                             parseQuote,
                             readQuote,
                             toHaskellExp,
                             evalEgisonTopLevel) where

import Language.Haskell.TH
import Language.Haskell.TH.Syntax
import Language.Haskell.TH.Quote

import Text.Parsec
import Text.Parsec.String (Parser)

import Language.Egison.Core
import Language.Egison.Types hiding (Type, Parser)
import Language.Egison.Parser
import Language.Egison.Variables

import Data.Either (either)
import Data.Ratio (numerator, denominator, (%))
import Data.IORef (newIORef)
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
-- For example, with Egison pattern matching, /powerset function/ can be expressed easily as follows.
--
-- >>> [egison|(lambda [$l] (match-all l (Multiset Integer) [<join $l _> l])) :: [Int] -> [[Int]]|] [1..3]
-- [[],[1],[2],[1,2],[3],[1,3],[2,3],[1,2,3]]
--
-- Type signature is defined as follows
--
-- > <Typ> = Bool | Int | Double | Float | Char | String | [<Typ>] | (<Typ>, <Typ>, ..., <Typ>) | <Typ> -> <Typ> -> ... <Typ>
--
-- Embedded Egison expression is run-time evaluated by using 'Language.Egison.Core.eval' and 'System.Unsafe.unsafePerformIO'.
-- For more detailed usage, please refer to <https://github.com/xenophobia/Egison-Quote>.
egison :: QuasiQuoter
egison = QuasiQuoter {
           quoteExp = \input ->
                      let (antiquotes, input') = pickupAntiquote input
                          (expr, typ) = extractValue . readQuote $ input'
                      in do
                        toHaskellExp expr antiquotes typ,
           quotePat = error "Not implemented pat-quote.",
           quoteType = error "Not implemented type-quote.",
           quoteDec = error "Not implemented dec-quote."
         }

-- * Type

matchAppType :: Type -> Maybe ([Type], Type)
matchAppType t@(AppT (AppT ArrowT _) _) = Just . matchAppType' $ t
    where
      matchAppType' (AppT (AppT ArrowT arg) rest) = first (++[arg]) $ matchAppType' rest
      matchAppType' ret = ([], ret)
matchAppType _ = Nothing

matchTupleType :: Type -> Maybe [Type]
matchTupleType (AppT (TupleT _) ret) = return [ret]
matchTupleType (AppT rest element) = (++[element]) <$> matchTupleType rest
matchTupleType _ = Nothing

matchListType :: Type -> Maybe Type
matchListType t = case t of {AppT ListT typ -> return typ; _ -> Nothing}

matchConstType :: Type -> Maybe String
matchConstType t= case t of {ConT t -> Just . nameBase $ t; _ -> Nothing}

-- Generate [ EgisonVal -> (corresponding Haskell Value) ] function from TypeSignature
converter :: Type -> ExpQ
converter (matchConstType -> Just "Char") = [| \(Char x) -> x |]
converter (matchConstType -> Just "String") = [| \(String x) -> x |]
converter (matchConstType -> Just "Bool") = [| \(Bool x) -> x |]
converter (matchConstType -> Just "Int") = [| \(Number x) -> (fromIntegral x) :: Int |]
converter (matchConstType -> Just "Integer") = [| \(Number x) -> x |]
converter (matchConstType -> Just "Double") = [| \(Float x) -> x |]
converter (matchConstType -> Just "Float") = [| \(Float x) -> (realToFrac x) :: Float |]
converter (matchTupleType -> Just ts) = do
  patvars <- replicateM (length ts) $ newName "x"
  lamE [conP 'Tuple [listP $ map varP patvars]] (foldl (\acc (x, t) -> appE acc (appE (converter t) (varE x))) (conE $ tupleDataName (length ts)) (zip patvars ts))
converter (matchListType -> Just t) = [| \(Collection vs) -> map $(converter t) vs |]
converter (matchAppType -> Just (args, ret)) = [| \func@(Func _ _ env) -> $(wrap 'func 'env) |]
    where
      wrap (varE -> funcVal) (varE -> env) = do
        (funcName, (func, funcP)) <- (show &&& varE &&& varP) <$> newName "func"
        argsName <- mapM newName $ map (("x"++) . show) [1..length args]
        let (args, argsP) = (map varE &&& map varP) argsName
        (lamE argsP
         (appE (converter ret)
          (appE (varE 'unsafePerformIO)
           (doE $
                bindS funcP (appE (varE 'newIORef) (appE (conE 'Value) funcVal)) :
                noBindS [| runIOThrowsError $ defineVar $(env) (funcName, []) $(func) |] :
                makeBinding (map show argsName) args env ++
                [noBindS [| runIOThrowsError (eval $(env) (ApplyExpr (VarExpr funcName []) (TupleExpr (map toEgisonExpr $(listE args))))) |]]))))
converter t = error $ "Invarid type: " ++ show t

-- * Parser

-- | Parser for TypeSignature
parseType :: Parser Type
parseType = do
  t1_ <- many (try $ lexeme parseType' <* lexeme (string "->"))
  t2 <- lexeme parseType'
  case t1_ of
    [] -> return t2
    t1 -> return $ foldr AppT t2 (map (AppT ArrowT) t1)

parseType' :: Parser Type
parseType' = (string "Char" >> return (ConT ''Char))
             <|> (string "String" >> return (ConT ''String))
             <|> (string "Bool" >> return (ConT ''Bool))
             <|> (string "Int" >> return (ConT ''Int))
             <|> (string "Integer" >> return (ConT ''Integer))
             <|> (string "Float" >> return (ConT ''Float))
             <|> (string "Double" >> return (ConT ''Double))
             <|> (try $ parens $ do thd <- lexeme parseType'
                                    ttl <- many (lexeme (char ',') >> lexeme parseType')
                                    return $ if null ttl
                                               then thd
                                               else foldl AppT (TupleT (length $ thd:ttl)) (thd:ttl))
             <|> brackets (AppT ListT <$> lexeme parseType')
             <|> parens parseType

-- | Pick up antiquoted variables and delete notation @#{~}@
-- 
-- > "(+ #{x} y)"  ---> ([x], "(+ x y)")
pickupAntiquote :: String -> ([String], String)
pickupAntiquote input = either (error.show) id $ parse parseAntiquote "Antiquote" input

-- | Parser for 'pickupAntiquote'
parseAntiquote :: Parser ([String], String)
parseAntiquote = (try $ do lexeme (char '#')
                           lexeme (char '{')
                           antiquote <- identifier
                           lexeme (char '}')
                           (antiquotes, rest) <- parseAntiquote
                           return $ (antiquote:antiquotes, ' ':antiquote++" "++rest))
                 <|> (try $ do c <- anyChar
                               (antiquotes, rest) <- parseAntiquote
                               return $ (antiquotes, c:rest))
                 <|> (eof >> return ([], ""))

-- | Parser for egison-quote
parseQuote :: Parser (EgisonExpr, Type)
parseQuote = do
  spaces
  expr <- lexeme parseExpr
  lexeme (string "::")
  typ <- lexeme parseType
  return (expr, typ)

-- | Read function for egison-quote
readQuote :: String -> ThrowsError (EgisonExpr, Type)
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
  lift (MacroVarExpr x) = appsE [conE 'MacroVarExpr, lift x]
  lift (PatVarOmitExpr x l) = appsE [conE 'PatVarOmitExpr, lift x, lift l]
  lift (VarOmitExpr x l) = appsE [conE 'VarOmitExpr, lift x, lift l]
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

-- | make do-binding
makeBinding :: [String] -- ^ variable names
            -> [ExpQ] -- ^ binding expressions
            -> ExpQ -- ^ environmental name
            -> [StmtQ]
makeBinding names exprs env = zipWith (\name expr -> noBindS [|runIOThrowsError $ defineVar $(env) (name, []) =<< (liftIO $ makeClosure $(env) (toEgisonExpr $(expr)))|]) names exprs

nameExprWithType :: String -> TypeQ -> ExpQ
nameExprWithType name typ = sigE (varE (mkName name)) typ

-- | construct Exp from Egison-expression and type signature
toHaskellExp :: EgisonExpr -> [String] -> Type -> ExpQ
toHaskellExp (FuncExpr (TupleExpr args) expr) antiquotes (nArgsApp (length args) -> (t1, t2)) = do
  let (argsName, argsType) = unzip . concat $ zipWith argsExpand args t1
      argsExpr = zipWith nameExprWithType argsName argsType
      bindnames = antiquotes ++ argsName
      bindexprs = map (varE . mkName) antiquotes ++ argsExpr
  (lamE (map toHaskellArgsPat args)
        (appE (converter t2) (evalEgisonTopLevel expr bindnames bindexprs)))
toHaskellExp expr antiquotes typ = appE (converter typ) (evalEgisonTopLevel expr antiquotes (map (varE . mkName) antiquotes))

childExpr :: EgisonExpr -> [EgisonExpr]
childExpr (CharExpr _) = []
childExpr (StringExpr _) = []
childExpr (BoolExpr _) = []
childExpr (NumberExpr _) = []
childExpr (FloatExpr _) = []
childExpr (VarExpr _ cs) = cs
childExpr (MacroVarExpr _) = []
childExpr (PatVarOmitExpr _ cs) = cs
childExpr (VarOmitExpr _ cs) = cs
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

nArgsApp :: Int -> Type -> ([Type], Type)
nArgsApp 0 ret = ([], ret)
nArgsApp n (AppT (AppT ArrowT arg) rest) = first (arg:) $ nArgsApp (n-1) rest
nArgsApp _ _ = error "Invarid Args."

-- | Expand binding
--
-- > [a1 [a2 a3]] :: (Int, (Char, Char)) -->  [(a1, Int), (a2, Char), (a3, Char)]
argsExpand :: EgisonExpr -> Type -> [(String, TypeQ)]
argsExpand (PatVarExpr a _) t = [(a, return t)]
argsExpand (TupleExpr as) (matchTupleType -> Just ts) | length as == length ts = concat $ zipWith argsExpand as ts
                                                      | otherwise = error "Wrong number of args."
argsExpand e t = error $ "Invarid argument: \n" ++ show e ++ "\n" ++ show t

-- | Egison binding to Haskell binding
--
-- > [a1 [a2 a3]] -->  (a1, (a2, a3))
toHaskellArgsPat :: EgisonExpr -> PatQ
toHaskellArgsPat (PatVarExpr a _) = varP (mkName a)
toHaskellArgsPat (TupleExpr as) = tupP $ map toHaskellArgsPat as

evalEgisonTopLevel :: EgisonExpr -- ^ evaluated expression
                   -> [String] -- ^ variable names
                   -> [ExpQ] -- ^ binding expressions
                   -> ExpQ
evalEgisonTopLevel expr bindvars bindexprs = do
  (env, envP) <- (varE &&& varP) <$> newName "env"
  (appE (varE 'unsafePerformIO)
   (doE (
     envP `bindS` (varE 'primitiveBindings) : 
     noBindS (appE (varE 'loadLibraries) env) :
     makeBinding bindvars bindexprs env ++
     [noBindS [| runIOThrowsError $ eval $(env) expr |]  ])))
