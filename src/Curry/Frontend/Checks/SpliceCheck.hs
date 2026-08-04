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

import Control.Monad (unless)
import Control.Monad.IO.Class (liftIO)


import Curry.Syntax.Type
import Curry.Base.Ident
import Curry.Base.SpanInfo
import Curry.Base.Monad (CYIO, failMessages, runCYIO)

import qualified Curry.FlatCurry as FC (Prog, writeFlatCurry)
import Curry.Files.Filenames (flatName)
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


spliceCheck :: Options -> CompilerEnv -> Module () -> IO (Module (), [Message])
spliceCheck opts env m = do
  (result, warnings) <- runCYIO (resolveSplice opts env m)
  case result of
    Left errs -> return(m, errs)
    Right m' -> return (m', warnings)

-- For now we don't need more code than the expression itself.
-- We do still of course need imports... 
-----------------------------------------------------------
createModule :: [ImportDecl] -> Expression () -> Module ()
createModule imports e = Module
  NoSpanInfo
  WhitespaceLayout              -- LayoutInfo
  []                            -- [ModulePragma]
  (mkMIdent ["Splice"])         -- ModuleIdent
  Nothing                       -- Maybe ExportSpec
  imports                       -- [ImportDecl]
  [ TypeSig
      NoSpanInfo
      [mkIdent "main"]
      (QualTypeExpr NoSpanInfo [] qExpType)
  , FunctionDecl
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
            e
            []
          )
      ]
  ]
  where
  qExpType = ApplyType NoSpanInfo
               (ConstructorType NoSpanInfo (qualify (mkIdent "Q")))
               (ConstructorType NoSpanInfo (qualify (mkIdent "CExpr")))

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
compileSplice :: Options -> CompilerEnv -> [ImportDecl] -> Expression ()
              -> CYIO FC.Prog
compileSplice opts env imports0 e = do
  let imports = withPrelude env imports0
      mdl0    = createModule imports e
  env0 <- importModules mdl0 (interfaceEnv env) imports

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

resolveSplice :: Options -> CompilerEnv -> Module () -> CYIO (Module ())
resolveSplice opts env (Module x1 x2 x3 x4 x5 x6 ds) =
  Module x1 x2 x3 x4 x5 x6 <$> mapM (declResolveSplice opts env x6) ds

declResolveSplice :: Options -> CompilerEnv -> [ImportDecl] -> Decl () -> CYIO (Decl ())
declResolveSplice opts env is (FunctionDecl x1 x2 x3 eqs) =
  FunctionDecl x1 x2 x3 <$> mapM (eqResolveSplice opts env is) eqs
declResolveSplice opts env is (PatternDecl x1 x2 rhs) =
  PatternDecl x1 x2 <$> rhsResolveSplice opts env is rhs
declResolveSplice opts env is (ClassDecl x1 x2 x3 x4 x5 x6 ds) =
  ClassDecl x1 x2 x3 x4 x5 x6 <$> mapM (declResolveSplice opts env is) ds
declResolveSplice opts env is (InstanceDecl x1 x2 x3 x4 x5 ds) =
  InstanceDecl x1 x2 x3 x4 x5 <$> mapM (declResolveSplice opts env is) ds
declResolveSplice _ _ _ decl = return decl

eqResolveSplice :: Options -> CompilerEnv -> [ImportDecl] -> Equation () -> CYIO (Equation ())
eqResolveSplice opts env is (Equation x1 x2 x3 rhs) =
  Equation x1 x2 x3 <$> rhsResolveSplice opts env is rhs

rhsResolveSplice :: Options -> CompilerEnv -> [ImportDecl] -> Rhs () -> CYIO (Rhs ())
rhsResolveSplice opts env is (SimpleRhs x1 x2 e ds) =
  SimpleRhs x1 x2 <$> exprResolveSplice opts env is e
                  <*> mapM (declResolveSplice opts env is) ds
rhsResolveSplice opts env is (GuardedRhs x1 x2 ces ds) =
  GuardedRhs x1 x2 <$> mapM (condExprResolveSplice opts env is) ces
                   <*> mapM (declResolveSplice opts env is) ds

condExprResolveSplice :: Options -> CompilerEnv -> [ImportDecl] -> CondExpr () -> CYIO (CondExpr ())
condExprResolveSplice opts env is (CondExpr x1 g e) =
  CondExpr x1 <$> exprResolveSplice opts env is g <*> exprResolveSplice opts env is e

exprResolveSplice :: Options -> CompilerEnv -> [ImportDecl] -> Expression () -> CYIO (Expression ())
exprResolveSplice opts env is (ExprSplice _ e) = do
  -- Doesn't run the splice yet ofc...
  _fcy <- compileSplice opts env is e
  _ <- liftIO $ FC.writeFlatCurry (flatName (takeDirectory (filePath env) </> "Splice")) _fcy
  return e
exprResolveSplice opts env is (Paren x1 e) =
  Paren x1 <$> exprResolveSplice opts env is e
exprResolveSplice opts env is (Typed x1 e x2) =
  (\e' -> Typed x1 e' x2) <$> exprResolveSplice opts env is e
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
  Let x1 x2 <$> mapM (declResolveSplice opts env is) ds
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
  StmtDecl x1 x2 <$> mapM (declResolveSplice opts env is) ds
stmtResolveSplice opts env is (StmtBind x1 x2 e) =
  StmtBind x1 x2 <$> exprResolveSplice opts env is e

altResolveSplice :: Options -> CompilerEnv -> [ImportDecl] -> Alt () -> CYIO (Alt ())
altResolveSplice opts env is (Alt x1 x2 rhs) =
  Alt x1 x2 <$> rhsResolveSplice opts env is rhs