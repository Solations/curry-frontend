{- |
    Module      :  $Header$
    Description :  Checks splices
    Copyright   :  (c) 2026 Johannes Reick
    License     :  BSD-3-clause

    Maintainer  :  stu244291@mail.uni-kiel.de
    Stability   :  experimental
    Portability :  portable

   The SpliceCheck checks for splices starts their compilation, runs them and 
   writes back their result to the original module.
-}
module Curry.Frontend.Checks.SpliceCheck (spliceCheck) where

import System.Process (readCreateProcess, proc, CreateProcess (cwd))

import Text.Read (readMaybe)

import Control.Monad (unless)
import Control.Monad.Extra (concatMapM)
import Control.Monad.IO.Class (liftIO)

import Curry.Syntax.Type
import Curry.Base.Ident
import Curry.Base.SpanInfo
import Curry.Base.Span
import Curry.Base.Position
import Curry.Base.Monad (CYIO, failMessages, runCYIO)

import qualified Curry.FlatCurry as FC (Prog, writeFlatCurry)
import qualified Curry.AbstractCurry as AC (CExpr, CFuncDecl, CTypeExpr)
import Curry.Files.Filenames (flatName, addOutDirModule)
import System.FilePath (takeDirectory, (</>))

import Curry.Frontend.Base.Messages (Message)
import Curry.Frontend.CompilerOpts (Options (..), OptimizationOpts (..))
import Curry.Frontend.CompilerEnv (CompilerEnv (..))
import Curry.Frontend.Imports (importModules)
import Curry.Frontend.Generators (genAnnotatedFlatCurry, genFlatCurry)
import Curry.Frontend.Transformations
  (qual, derive, desugar, insertDicts, removeNewtypes, simplify, lift, ilTrans, completeCase)

-- These are the individual checks, imported directly rather than through the
-- 'Curry.Frontend.Checks' umbrella module -- see the comment on
-- 'compileSplice' below for why.
import qualified Curry.Frontend.Checks.SyntaxCheck as SC (syntaxCheck)
import qualified Curry.Frontend.Checks.PrecCheck   as PC (precCheck)
import qualified Curry.Frontend.Checks.TypeCheck   as TC (typeCheck)
import qualified Curry.Frontend.Checks.ExportCheck as EC (expandExports)
import Curry.AbstractCurry.Type
  ( CExpr (..), CLiteral (..), CPattern (..), CLocalDecl (..), CStatement (..)
  , CRhs (..), CFuncDecl (..), CRule (..), CCaseType (..), CQualTypeExpr (..)
  , CTypeExpr (..), CContext (..), QName, CVarIName
  )

resultStartMarker, resultEndMarker:: String
resultStartMarker = "===SPLICE-RESULT-START==="
resultEndMarker = "===SPLICE-RESULT-END==="

spliceCheck :: Options -> CompilerEnv -> Module () -> IO (Module (), [Message])
spliceCheck opts env m = do
  (result, warnings) <- runCYIO (resolveSplice opts env m)
  case result of
    Left errs -> return(m, errs)
    Right m' -> return (m', warnings)

resolveSplice :: Options -> CompilerEnv -> Module () -> CYIO (Module ())
resolveSplice opts env (Module x1 x2 x3 x4 x5 x6 ds) =
  Module x1 x2 x3 x4 x5 x6 <$> concatMapM (declResolveSplice opts env x6) ds

declResolveSplice :: Options -> CompilerEnv -> [ImportDecl] -> Decl () -> CYIO [Decl ()]
declResolveSplice opts env is (DataDecl x1 x2 x3 cs x5) =
  (:[]) . (\cs' -> DataDecl x1 x2 x3 cs' x5) <$> mapM (constrDeclResolveSplice opts env is) cs
declResolveSplice opts env is (NewtypeDecl x1 x2 x3 nc x5) =
  (:[]) . (\nc' -> NewtypeDecl x1 x2 x3 nc' x5) <$> newConstrDeclResolveSplice opts env is nc
declResolveSplice opts env is (TypeDecl x1 x2 x3 ty) =
  (:[]) . TypeDecl x1 x2 x3 <$> typeExprResolveSplice opts env is ty
declResolveSplice opts env is (TypeSig x1 x2 qty) =
  (:[]) . TypeSig x1 x2 <$> qualTypeExprResolveSplice opts env is qty
declResolveSplice opts env is (FunctionDecl x1 x2 x3 eqs) =
  (:[]) . FunctionDecl x1 x2 x3 <$> mapM (eqResolveSplice opts env is) eqs
declResolveSplice opts env is (PatternDecl x1 x2 rhs) =
  (:[]) . PatternDecl x1 x2 <$> rhsResolveSplice opts env is rhs
declResolveSplice opts env is (DefaultDecl x1 tys) =
  (:[]) . DefaultDecl x1 <$> mapM (typeExprResolveSplice opts env is) tys
declResolveSplice opts env is (ClassDecl x1 x2 cx x4 x5 x6 ds) = do
  cx' <- contextResolveSplice opts env is cx
  ds' <- concatMapM (declResolveSplice opts env is) ds
  return [ClassDecl x1 x2 cx' x4 x5 x6 ds']
declResolveSplice opts env is (InstanceDecl x1 x2 cx x4 tys ds) = do
  cx'  <- contextResolveSplice opts env is cx
  tys' <- mapM (typeExprResolveSplice opts env is) tys
  ds'  <- concatMapM (declResolveSplice opts env is) ds
  return [InstanceDecl x1 x2 cx' x4 tys' ds']
declResolveSplice opts env is (TopLevelSplice sp e) 
  | mkMIdent ["templateCurry"] `elem` [m | ImportDecl _ m _ _ _ <- is] = do
    -- Here expression splices are run and evaluated to an actual expression.
    let typ = ListType NoSpanInfo (ConstructorType NoSpanInfo (qualify (mkIdent "CFuncDecl")))
    sDecl <- turnSpliceIntoSpring sp opts env is e typ
    case readMaybe sDecl :: Maybe [AC.CFuncDecl] of
      Just acDecl -> return (buildAstDecl acDecl)
      Nothing     -> error "Error compiling splice."
  | otherwise = error "Please use languge-extension template-curry to use splices."
declResolveSplice _ _ _ decl = return [decl]

eqResolveSplice :: Options -> CompilerEnv -> [ImportDecl] -> Equation () -> CYIO (Equation ())
eqResolveSplice opts env is (Equation x1 x2 x3 rhs) =
  Equation x1 x2 x3 <$> rhsResolveSplice opts env is rhs

rhsResolveSplice :: Options -> CompilerEnv -> [ImportDecl] -> Rhs () -> CYIO (Rhs ())
rhsResolveSplice opts env is (SimpleRhs x1 x2 e ds) =
  SimpleRhs x1 x2 <$> exprResolveSplice opts env is e
                  <*> concatMapM (declResolveSplice opts env is) ds
rhsResolveSplice opts env is (GuardedRhs x1 x2 ces ds) =
  GuardedRhs x1 x2 <$> mapM (condExprResolveSplice opts env is) ces
                   <*> concatMapM (declResolveSplice opts env is) ds

condExprResolveSplice :: Options -> CompilerEnv -> [ImportDecl] -> CondExpr () -> CYIO (CondExpr ())
condExprResolveSplice opts env is (CondExpr x1 g e) =
  CondExpr x1 <$> exprResolveSplice opts env is g <*> exprResolveSplice opts env is e

exprResolveSplice :: Options -> CompilerEnv -> [ImportDecl] -> Expression () -> CYIO (Expression ())
exprResolveSplice opts env is (ExprSplice sp e)
  | mkMIdent ["templateCurry"] `elem` [m | ImportDecl _ m _ _ _ <- is] = do
    -- Here expression splices are run and evaluated to an actual expression.
    let typ = ConstructorType NoSpanInfo (qualify (mkIdent "CExpr"))
    sExp <- turnSpliceIntoSpring sp opts env is e typ
    case readMaybe sExp :: Maybe AC.CExpr of
      Just acExpr -> return (buildAstExpr acExpr)
      Nothing     -> error "Error compiling splice."
  | otherwise = error "Please use languge-extension template-curry to use splices."
exprResolveSplice opts env is (Paren x1 e) =
  Paren x1 <$> exprResolveSplice opts env is e
exprResolveSplice opts env is (Typed x1 e ty) =
  Typed x1 <$> exprResolveSplice opts env is e
           <*> qualTypeExprResolveSplice opts env is ty
exprResolveSplice opts env is (Record x1 x2 x3 fs) =
  Record x1 x2 x3 <$> mapM (fieldResolveSplice opts env is) fs
exprResolveSplice opts env is (RecordUpdate x1 e fs) =
  RecordUpdate x1 <$> exprResolveSplice opts env is e
                  <*> mapM (fieldResolveSplice opts env is) fs
exprResolveSplice opts env is (Tuple x1 es) =
  Tuple x1 <$> mapM (exprResolveSplice opts env is) es
exprResolveSplice opts env is (List x1 x2 es) =
  List x1 x2 <$> mapM (exprResolveSplice opts env is) es
exprResolveSplice opts env is (ListCompr x1 e ss) =
  ListCompr x1 <$> exprResolveSplice opts env is e
               <*> mapM (stmtResolveSplice opts env is) ss
exprResolveSplice opts env is (EnumFrom x1 e) =
  EnumFrom x1 <$> exprResolveSplice opts env is e
exprResolveSplice opts env is (EnumFromThen x1 e1 e2) =
  EnumFromThen x1 <$> exprResolveSplice opts env is e1
                  <*> exprResolveSplice opts env is e2
exprResolveSplice opts env is (EnumFromTo x1 e1 e2) =
  EnumFromTo x1 <$> exprResolveSplice opts env is e1
                <*> exprResolveSplice opts env is e2
exprResolveSplice opts env is (EnumFromThenTo x1 e1 e2 e3) =
  EnumFromThenTo x1 <$> exprResolveSplice opts env is e1
                    <*> exprResolveSplice opts env is e2
                    <*> exprResolveSplice opts env is e3
exprResolveSplice opts env is (UnaryMinus x1 e) =
  UnaryMinus x1 <$> exprResolveSplice opts env is e
exprResolveSplice opts env is (Apply x1 e1 e2) =
  Apply x1 <$> exprResolveSplice opts env is e1
           <*> exprResolveSplice opts env is e2
exprResolveSplice opts env is (InfixApply x1 e1 x2 e2) =
  (\e1' e2' -> InfixApply x1 e1' x2 e2')
    <$> exprResolveSplice opts env is e1
    <*> exprResolveSplice opts env is e2
exprResolveSplice opts env is (LeftSection x1 e x2) =
  (\e' -> LeftSection x1 e' x2) <$> exprResolveSplice opts env is e
exprResolveSplice opts env is (RightSection x1 x2 e) =
  RightSection x1 x2 <$> exprResolveSplice opts env is e
exprResolveSplice opts env is (Lambda x1 x2 e) =
  Lambda x1 x2 <$> exprResolveSplice opts env is e
exprResolveSplice opts env is (Let x1 x2 ds e) =
  Let x1 x2 <$> concatMapM (declResolveSplice opts env is) ds
            <*> exprResolveSplice opts env is e
exprResolveSplice opts env is (Do x1 x2 ss e) =
  Do x1 x2 <$> mapM (stmtResolveSplice opts env is) ss
           <*> exprResolveSplice opts env is e
exprResolveSplice opts env is (IfThenElse x1 e1 e2 e3) =
  IfThenElse x1 <$> exprResolveSplice opts env is e1
                <*> exprResolveSplice opts env is e2
                <*> exprResolveSplice opts env is e3
exprResolveSplice opts env is (Case x1 x2 x3 e as) =
  Case x1 x2 x3 <$> exprResolveSplice opts env is e
                <*> mapM (altResolveSplice opts env is) as
exprResolveSplice _ _ _ e = return e -- Literal, Variable, Constructor

fieldResolveSplice :: Options -> CompilerEnv -> [ImportDecl]
                    -> Field (Expression ()) -> CYIO (Field (Expression ()))
fieldResolveSplice opts env is (Field x1 x2 e) =
  Field x1 x2 <$> exprResolveSplice opts env is e

stmtResolveSplice :: Options -> CompilerEnv -> [ImportDecl] -> Statement () -> CYIO (Statement ())
stmtResolveSplice opts env is (StmtExpr x1 e) =
  StmtExpr x1 <$> exprResolveSplice opts env is e
stmtResolveSplice opts env is (StmtDecl x1 x2 ds) =
  StmtDecl x1 x2 <$> concatMapM (declResolveSplice opts env is) ds
stmtResolveSplice opts env is (StmtBind x1 x2 e) =
  StmtBind x1 x2 <$> exprResolveSplice opts env is e

altResolveSplice :: Options -> CompilerEnv -> [ImportDecl] -> Alt () -> CYIO (Alt ())
altResolveSplice opts env is (Alt x1 x2 rhs) =
  Alt x1 x2 <$> rhsResolveSplice opts env is rhs

typeExprResolveSplice :: Options -> CompilerEnv -> [ImportDecl] -> TypeExpr -> CYIO TypeExpr
typeExprResolveSplice _ _ _ ty@(ConstructorType _ _) = return ty
typeExprResolveSplice opts env is (ApplyType x1 ty1 ty2) =
  ApplyType x1 <$> typeExprResolveSplice opts env is ty1
               <*> typeExprResolveSplice opts env is ty2
typeExprResolveSplice _ _ _ ty@(VariableType _ _) = return ty
typeExprResolveSplice opts env is (TupleType x1 tys) =
  TupleType x1 <$> mapM (typeExprResolveSplice opts env is) tys
typeExprResolveSplice opts env is (ListType x1 ty) =
  ListType x1 <$> typeExprResolveSplice opts env is ty
typeExprResolveSplice opts env is (ArrowType x1 ty1 ty2) =
  ArrowType x1 <$> typeExprResolveSplice opts env is ty1
               <*> typeExprResolveSplice opts env is ty2
typeExprResolveSplice opts env is (ParenType x1 ty) =
  ParenType x1 <$> typeExprResolveSplice opts env is ty
typeExprResolveSplice opts env is (ForallType x1 vs ty) =
  ForallType x1 vs <$> typeExprResolveSplice opts env is ty
typeExprResolveSplice opts env is (TypeExprSplice sp e) 
  | mkMIdent ["templateCurry"] `elem` [m | ImportDecl _ m _ _ _ <- is] = do
    let typ = ConstructorType NoSpanInfo (qualify (mkIdent "CTypeExpr"))
    sTyp <- turnSpliceIntoSpring sp opts env is e typ
    case readMaybe sTyp :: Maybe AC.CTypeExpr of
      Just acTyp -> return (buildAstTypeExpr acTyp)
      Nothing   -> error "Error compiling splice."
  | otherwise = error "Please use languge-extension template-curry to use splices."

qualTypeExprResolveSplice :: Options -> CompilerEnv -> [ImportDecl] -> QualTypeExpr -> CYIO QualTypeExpr
qualTypeExprResolveSplice opts env is (QualTypeExpr x1 cx ty) =
  QualTypeExpr x1 <$> contextResolveSplice opts env is cx
                  <*> typeExprResolveSplice opts env is ty

contextResolveSplice :: Options -> CompilerEnv -> [ImportDecl] -> Context -> CYIO Context
contextResolveSplice opts env is = mapM (constraintResolveSplice opts env is)

constraintResolveSplice :: Options -> CompilerEnv -> [ImportDecl] -> Constraint -> CYIO Constraint
constraintResolveSplice opts env is (Constraint x1 qcls tys) =
  Constraint x1 qcls <$> mapM (typeExprResolveSplice opts env is) tys

constrDeclResolveSplice :: Options -> CompilerEnv -> [ImportDecl] -> ConstrDecl -> CYIO ConstrDecl
constrDeclResolveSplice opts env is (ConstrDecl x1 c tys) =
  ConstrDecl x1 c <$> mapM (typeExprResolveSplice opts env is) tys
constrDeclResolveSplice opts env is (ConOpDecl x1 ty1 op ty2) =
  (\ty1' ty2' -> ConOpDecl x1 ty1' op ty2')
    <$> typeExprResolveSplice opts env is ty1
    <*> typeExprResolveSplice opts env is ty2
constrDeclResolveSplice opts env is (RecordDecl x1 c fs) =
  RecordDecl x1 c <$> mapM (fieldDeclResolveSplice opts env is) fs

newConstrDeclResolveSplice :: Options -> CompilerEnv -> [ImportDecl] -> NewConstrDecl -> CYIO NewConstrDecl
newConstrDeclResolveSplice opts env is (NewConstrDecl x1 c ty) =
  NewConstrDecl x1 c <$> typeExprResolveSplice opts env is ty
newConstrDeclResolveSplice opts env is (NewRecordDecl x1 c (l, ty)) =
  (\ty' -> NewRecordDecl x1 c (l, ty')) <$> typeExprResolveSplice opts env is ty

fieldDeclResolveSplice :: Options -> CompilerEnv -> [ImportDecl] -> FieldDecl -> CYIO FieldDecl
fieldDeclResolveSplice opts env is (FieldDecl x1 ls ty) =
  FieldDecl x1 ls <$> typeExprResolveSplice opts env is ty

buildAstExpr :: CExpr -> Expression ()
buildAstExpr (CVar vn) =
  Variable NoSpanInfo () (qualify (buildAstIdent vn))
buildAstExpr (CLit lit) =
  Literal NoSpanInfo () (buildAstLit lit)
buildAstExpr (CSymbol qn) =
  Variable NoSpanInfo () (buildAstQualIdent qn)
buildAstExpr (CApply e1 e2) =
  Apply NoSpanInfo (buildAstExpr e1) (buildAstExpr e2)
buildAstExpr (CLambda ps e) =
  Lambda NoSpanInfo (map buildAstPattern ps) (buildAstExpr e)
buildAstExpr (CLetDecl ds e) =
  Let NoSpanInfo WhitespaceLayout (map buildAstLocalDecl ds) (buildAstExpr e)
buildAstExpr (CDoExpr sts) =
  uncurry (Do NoSpanInfo WhitespaceLayout) (buildAstDoBody sts)
buildAstExpr (CListComp e sts) =
  ListCompr NoSpanInfo (buildAstExpr e) (map buildAstStatement sts)
buildAstExpr (CCase ct e alts) =
  Case NoSpanInfo WhitespaceLayout (buildAstCaseType ct) (buildAstExpr e)
       (map buildAstAlt alts)
buildAstExpr (CTyped e qty) =
  Typed NoSpanInfo (buildAstExpr e) (buildAstQualTypeExpr qty)
buildAstExpr (CRecConstr qn fs) =
  Record NoSpanInfo () (buildAstQualIdent qn) (map (buildAstField buildAstExpr) fs)
buildAstExpr (CRecUpdate e fs) =
  RecordUpdate NoSpanInfo (buildAstExpr e) (map (buildAstField buildAstExpr) fs)

buildAstDoBody :: [CStatement] -> ([Statement ()], Expression ())
buildAstDoBody sts = case reverse sts of
  (CSExpr e : rest) -> (map buildAstStatement (reverse rest), buildAstExpr e)
  _                 -> error
    "SpliceCheck.buildAstDoBody: do-block must end in an expression statement"

buildAstPattern :: CPattern -> Pattern ()
buildAstPattern (CPVar vn) =
  VariablePattern NoSpanInfo () (buildAstIdent vn)
buildAstPattern (CPLit lit) =
  LiteralPattern NoSpanInfo () (buildAstLit lit)
buildAstPattern (CPComb qn ps) =
  ConstructorPattern NoSpanInfo () (buildAstQualIdent qn) (map buildAstPattern ps)
buildAstPattern (CPAs vn p) =
  AsPattern NoSpanInfo (buildAstIdent vn) (buildAstPattern p)
buildAstPattern (CPFuncComb qn ps) =
  FunctionPattern NoSpanInfo () (buildAstQualIdent qn) (map buildAstPattern ps)
buildAstPattern (CPLazy p) =
  LazyPattern NoSpanInfo (buildAstPattern p)
buildAstPattern (CPRecord qn fs) =
  RecordPattern NoSpanInfo () (buildAstQualIdent qn) (map (buildAstField buildAstPattern) fs)

buildAstLocalDecl :: CLocalDecl -> Decl ()
buildAstLocalDecl (CLocalFunc fd)   = buildAstFuncDecl fd
buildAstLocalDecl (CLocalPat p rhs) = PatternDecl NoSpanInfo (buildAstPattern p) (buildAstRhs rhs)
buildAstLocalDecl (CLocalVars vns)  = FreeDecl NoSpanInfo (map (Var () . buildAstIdent) vns)

-- Doesn't emit a separate 'TypeSig' for the function's 'CQualTypeExpr' --
-- local (let/where) functions don't need one, and it keeps this a clean
-- one-'CLocalDecl'-to-one-'Decl' mapping.
buildAstFuncDecl :: CFuncDecl -> Decl ()
buildAstFuncDecl (CFunc qn _arity _vis _qty rules) =
  FunctionDecl NoSpanInfo () name (map (buildAstRule name) rules)
  where
  name = mkIdent (snd qn)
  buildAstRule n (CRule ps rhs) =
    Equation NoSpanInfo Nothing
      (FunLhs NoSpanInfo n (map buildAstPattern ps))
      (buildAstRhs rhs)

buildAstDecl :: [CFuncDecl] -> [Decl ()]
buildAstDecl = map buildAstFuncDecl

buildAstRhs :: CRhs -> Rhs ()
buildAstRhs (CSimpleRhs e ds) =
  SimpleRhs NoSpanInfo WhitespaceLayout (buildAstExpr e) (map buildAstLocalDecl ds)
buildAstRhs (CGuardedRhs gs ds) =
  GuardedRhs NoSpanInfo WhitespaceLayout
    [CondExpr NoSpanInfo (buildAstExpr g) (buildAstExpr e) | (g, e) <- gs]
    (map buildAstLocalDecl ds)

buildAstStatement :: CStatement -> Statement ()
buildAstStatement (CSExpr e)  = StmtExpr NoSpanInfo (buildAstExpr e)
buildAstStatement (CSPat p e) = StmtBind NoSpanInfo (buildAstPattern p) (buildAstExpr e)
buildAstStatement (CSLet ds)  = StmtDecl NoSpanInfo WhitespaceLayout (map buildAstLocalDecl ds)

buildAstAlt :: (CPattern, CRhs) -> Alt ()
buildAstAlt (p, rhs) = Alt NoSpanInfo (buildAstPattern p) (buildAstRhs rhs)

buildAstCaseType :: CCaseType -> CaseType
buildAstCaseType CRigid = Rigid
buildAstCaseType CFlex  = Flex

buildAstQualTypeExpr :: CQualTypeExpr -> QualTypeExpr
buildAstQualTypeExpr (CQualType (CContext cs) ty) =
  QualTypeExpr NoSpanInfo (map buildAstConstraint cs) (buildAstTypeExpr ty)

buildAstConstraint :: (QName, [CTypeExpr]) -> Constraint
buildAstConstraint (qn, tys) =
  Constraint NoSpanInfo (buildAstQualIdent qn) (map buildAstTypeExpr tys)

buildAstTypeExpr :: CTypeExpr -> TypeExpr
buildAstTypeExpr (CTVar vn)        = VariableType NoSpanInfo (buildAstIdent vn)
buildAstTypeExpr (CFuncType t1 t2) = ArrowType NoSpanInfo (buildAstTypeExpr t1) (buildAstTypeExpr t2)
buildAstTypeExpr (CTCons qn)       = ConstructorType NoSpanInfo (buildAstQualIdent qn)
buildAstTypeExpr (CTApply t1 t2)   = ApplyType NoSpanInfo (buildAstTypeExpr t1) (buildAstTypeExpr t2)

buildAstField :: (a -> b) -> (QName, a) -> Field b
buildAstField f (qn, x) = Field NoSpanInfo (buildAstQualIdent qn) (f x)

buildAstQualIdent :: QName -> QualIdent
buildAstQualIdent ("", n) = qualify (mkIdent n)
buildAstQualIdent (m, n)  = qualifyWith (mkMIdent (splitModuleName m)) (mkIdent n)

buildAstIdent :: CVarIName -> Ident
buildAstIdent (_, n) = mkIdent n

buildAstLit :: CLiteral -> Literal
buildAstLit (CIntc n)    = Int n
buildAstLit (CFloatc f)  = Float f
buildAstLit (CCharc c)   = Char c
buildAstLit (CStringc s) = String s

turnSpliceIntoSpring :: SpanInfo -> Options -> CompilerEnv -> [ImportDecl] -> Expression () -> TypeExpr -> CYIO String
turnSpliceIntoSpring sp opts env is e typ = do
  let useSubDir = addOutDirModule (optUseOutDir opts) (optOutDir opts) (moduleIdent env)
      spliceDir = takeDirectory (filePath env)
      modName     = moduleName (moduleIdent env) ++ "Splice" ++ positionTag sp
      spliceFcy = useSubDir (flatName (spliceDir </> modName))
  fcy <- compileSplice opts env is modName e typ
  _ <- liftIO $ FC.writeFlatCurry spliceFcy fcy
  liftIO $ runSplice spliceDir modName
  where 
    positionTag sp = show (line (start (srcSpan sp))) ++  "_" ++
      show (column (start (srcSpan sp)))

splitModuleName :: String -> [String]
splitModuleName s = case break (== '.') s of
  (m, '.':rest) -> m : splitModuleName rest
  (m, _)        -> [m]

runSplice :: FilePath -> String -> IO String
runSplice spliceDir ident = do
  out <- readCreateProcess (proc "pakcs" []) { cwd = Just spliceDir }
    (unlines
    [ ":l " ++ ident
    , ":main"
    , ":q"
    ])
  return (extractResult out)

extractResult :: String -> String
extractResult output = 
  let afterStart = drop 1 $ dropWhile (/=resultStartMarker) (lines output)
  in unlines (takeWhile (/=resultEndMarker) afterStart)

-- For now we don't need more code than the expression itself.
-- We do still of course need imports... 
-----------------------------------------------------------
createModule :: [ImportDecl] -> String -> Expression () -> TypeExpr -> Module ()
createModule imports name e typ = Module
  NoSpanInfo
  WhitespaceLayout              -- LayoutInfo
  []                            -- [ModulePragma]
  (mkMIdent [name])             -- ModuleIdent
  Nothing                       -- Maybe ExportSpec
  imports                      -- [ImportDecl]
  [ FunctionDecl
      NoSpanInfo
      ()                        -- Type
      (mkIdent "main")          -- Ident
      [ Equation
          NoSpanInfo
          Nothing               -- Type
          (FunLhs NoSpanInfo (mkIdent "main") [])
          (SimpleRhs
            NoSpanInfo
            WhitespaceLayout
            mainBody
            []
          )
      ]
  ]
  where
  -- main = putStrLn resultStartMarker
  --     >> (qtoIO (e :: Q CExpr) >>= print
  --     >> putStrLn resultEndMarker)

  mainBody = putStrLnExpr resultStartMarker `seqExpr`
               (qtoIOPrint `seqExpr` putStrLnExpr resultEndMarker)

  qtoIOPrint = InfixApply NoSpanInfo
                 (Apply NoSpanInfo
                    (Variable NoSpanInfo () (qualify (mkIdent "qtoIO")))
                    (Typed NoSpanInfo e (QualTypeExpr NoSpanInfo [] qExpType)))
                 (InfixOp () (qualify (mkIdent ">>=")))
                 (Variable NoSpanInfo () (qualify (mkIdent "print")))

  putStrLnExpr s = Apply NoSpanInfo
                     (Variable NoSpanInfo () (qualify (mkIdent "putStrLn")))
                     (Literal NoSpanInfo () (String s))

  seqExpr e1 e2 = InfixApply NoSpanInfo e1 (InfixOp () (qualify (mkIdent ">>"))) e2

  qExpType = ApplyType NoSpanInfo
               (ConstructorType NoSpanInfo (qualify (mkIdent "Q"))) typ

withPrelude :: CompilerEnv -> [ImportDecl] -> [ImportDecl]
withPrelude env imports
  | NoImplicitPrelude `elem` extensions env = imports
  | preludeMIdent `elem` importedModules    = imports
  | otherwise                               = preludeImport : imports
  where
  importedModules = [m | ImportDecl _ m _ _ _ <- imports]
  preludeImport   = ImportDecl NoSpanInfo preludeMIdent False Nothing Nothing

-- Runs pretty much the same pipeline Modules.hs does, but less checks
-- this might have to change later, however we won't ever need the splice check ofc...
compileSplice :: Options -> CompilerEnv -> [ImportDecl] -> String -> Expression () -> TypeExpr
              -> CYIO FC.Prog
compileSplice opts env imports modName e typ = do
  let imports' = withPrelude env imports
      mdl0     = createModule imports' modName e typ
  env0 <- importModules mdl0 (interfaceEnv env) imports'

  let env0' = env0 { extensions = extensions env }

  let ((mdl1, exts1), msgs1) =
        SC.syntaxCheck (extensions env0') (tyConsEnv env0') (valueEnv env0') mdl0
  unless (null msgs1) $ failMessages msgs1
  let env1 = env0' { extensions = exts1 }

  let Module spi li ps mid es is ds1 = mdl1
      (ds2, pEnv2, msgs2)            = PC.precCheck mid (opPrecEnv env1) ds1
  unless (null msgs2) $ failMessages msgs2
  let env2 = env1 { opPrecEnv = pEnv2 }

  let (ds3, vEnv3, msgs3) = TC.typeCheck
        (extensions env2) mid (tyConsEnv env2) (valueEnv env2)
        (classEnv env2) (instEnv env2) ds2
  unless (null msgs3) $ failMessages msgs3
  let env3 = env2 { valueEnv = vEnv3 }
      es'  = EC.expandExports mid (aliasEnv env3) (tyConsEnv env3) vEnv3 es
      mdl3 = Module spi li ps mid (Just es') is ds3

  let optOpts             = optOptimizations opts
      qualified           = qual (env3, mdl3)
      derived             = derive qualified
      desugared           = desugar derived
      dicts               = insertDicts (optInlineDictionaries optOpts) desugared
      newtypes@(_, ntMdl)  = removeNewtypes (optDesugarNewtypes optOpts) dicts
      simplified          = simplify newtypes
      lifted              = lift simplified
      il                  = ilTrans lifted
      (ilEnv, ilMdl)      = completeCase (optAddFailed optOpts) il

      afcy = genAnnotatedFlatCurry (optRemoveUnusedImports optOpts) ilEnv ntMdl ilMdl

  return $ genFlatCurry afcy