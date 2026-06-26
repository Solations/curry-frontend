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

import Curry.Syntax.Type
import Curry.Base.Ident
import Curry.Base.SpanInfo

import Curry.Frontend.Base.Messages (Message)


--Env übergeben
spliceCheck :: [KnownExtension] -> Module a -> (Module a, [Message])
spliceCheck _ m = (resolveSplice m, [])
    



    -- extensionCheck :: Options -> Module a -> ([KnownExtension], [Message])
    -- => typeSyntaxCheck :: [KnownExtension] -> TCEnv -> ClassEnv -> Module a -> (Module a, [Message])
    -- => kindCheck :: TCEnv -> ClassEnv -> Module a -> ((TCEnv, ClassEnv), [Message])

-- This is max stupidity I'd say, there must be a better way
-- Also ofc works only for Spliced expressions and really easy ones of those
-- So very limited for now, but let's see...
resolveSplice :: Module a -> Module a
resolveSplice (Module x1 x2 x3 x4 x5 x6 ds) = Module x1 x2 x3 x4 x5 x6 (map declRsolveSplice ds)

declRsolveSplice :: Decl a -> Decl a
declRsolveSplice (FunctionDecl x1 x2 x3 eqs)    = FunctionDecl x1 x2 x3 (map eqResolveSplice eqs)
declRsolveSplice (PatternDecl x1 x2 rhs)       = PatternDecl x1 x2 (rhsResolveSplice rhs)
declRsolveSplice (ClassDecl x1 x2 x3 x4 x5 x6 ds)  = ClassDecl x1 x2 x3 x4 x5 x6 (map declRsolveSplice ds)
declRsolveSplice (InstanceDecl x1 x2 x3 x4 x5 ds) = InstanceDecl x1 x2 x3 x4 x5 (map declRsolveSplice ds)
declRsolveSplice decl                           = decl

eqResolveSplice :: Equation a -> Equation a
eqResolveSplice (Equation x1 x2 x3 rhs) = Equation x1 x2 x3 (rhsResolveSplice rhs)

rhsResolveSplice :: Rhs a -> Rhs a
rhsResolveSplice (SimpleRhs x1 x2 e ds) = SimpleRhs x1 x2 (exprResolveSplice e) (map declRsolveSplice ds)
rhsResolveSplice (GuardedRhs x1 x2 ces ds) = GuardedRhs x1 x2 (map condExprResolveSplice ces) (map declRsolveSplice ds)

condExprResolveSplice :: CondExpr a -> CondExpr a
condExprResolveSplice (CondExpr x1 g e) = CondExpr x1 (exprResolveSplice g) (exprResolveSplice e)

exprResolveSplice :: Expression a -> Expression a
exprResolveSplice (ExprSplice _ e)        = e
exprResolveSplice (Paren x1 e)         = Paren x1 (exprResolveSplice e)
exprResolveSplice (Typed x1 e x2)       = Typed x1 (exprResolveSplice e) x2
exprResolveSplice (Record x1 x2 x3 fs)   = Record x1 x2 x3 (map fieldResolveSplice fs)
exprResolveSplice (RecordUpdate x1 e fs) = RecordUpdate x1 (exprResolveSplice e) (map fieldResolveSplice fs)
exprResolveSplice (Tuple x1 es)        = Tuple x1 (map exprResolveSplice es)
exprResolveSplice (List x1 x2 es)       = List x1 x2 (map exprResolveSplice es)
exprResolveSplice (ListCompr x1 e ss)  = ListCompr x1 (exprResolveSplice e) (map stmtResolveSplice ss)
exprResolveSplice (EnumFrom x1 e)      = EnumFrom x1 (exprResolveSplice e)
exprResolveSplice (EnumFromThen x1 e1 e2) = EnumFromThen x1 (exprResolveSplice e1) (exprResolveSplice e2)
exprResolveSplice (EnumFromTo x1 e1 e2)   = EnumFromTo x1 (exprResolveSplice e1) (exprResolveSplice e2)
exprResolveSplice (EnumFromThenTo x1 e1 e2 e3) =
  EnumFromThenTo x1 (exprResolveSplice e1) (exprResolveSplice e2) (exprResolveSplice e3)
exprResolveSplice (UnaryMinus x1 e)    = UnaryMinus x1 (exprResolveSplice e)
exprResolveSplice (Apply x1 e1 e2)     = Apply x1 (exprResolveSplice e1) (exprResolveSplice e2)
exprResolveSplice (InfixApply x1 e1 x2 e2) = InfixApply x1 (exprResolveSplice e1) x2 (exprResolveSplice e2)
exprResolveSplice (LeftSection x1 e x2) = LeftSection x1 (exprResolveSplice e) x2
exprResolveSplice (RightSection x1 x2 e) = RightSection x1 x2 (exprResolveSplice e)
exprResolveSplice (Lambda x1 x2 e)      = Lambda x1 x2 (exprResolveSplice e)
exprResolveSplice (Let x1 x2 ds e)      = Let x1 x2 (map declRsolveSplice ds) (exprResolveSplice e)
exprResolveSplice (Do x1 x2 ss e)       = Do x1 x2 (map stmtResolveSplice ss) (exprResolveSplice e)
exprResolveSplice (IfThenElse x1 e1 e2 e3) =
  IfThenElse x1 (exprResolveSplice e1) (exprResolveSplice e2) (exprResolveSplice e3)
exprResolveSplice (Case x1 x2 x3 e as)   = Case x1 x2 x3 (exprResolveSplice e) (map altResolveSplice as)
exprResolveSplice e                   = e -- Literal, Variable, Constructor

fieldResolveSplice :: Field (Expression a) -> Field (Expression a)
fieldResolveSplice (Field x1 x2 exp) = Field x1 x2 (exprResolveSplice exp)

stmtResolveSplice :: Statement a -> Statement a
stmtResolveSplice (StmtExpr x1 e)   = StmtExpr x1 (exprResolveSplice e)
stmtResolveSplice (StmtDecl x1 x2 ds) = StmtDecl x1 x2 (map declRsolveSplice ds)
stmtResolveSplice (StmtBind x1 x2 e) = StmtBind x1 x2 (exprResolveSplice e)

altResolveSplice :: Alt a -> Alt a
altResolveSplice (Alt x1 x2 rhs) = Alt x1 x2 (rhsResolveSplice rhs)

createModule :: Expression () -> Module ()
createModule e = Module
  NoSpanInfo
  WhitespaceLayout              -- LayoutInfo
  []                            -- [ModulePragma]
  (mkMIdent ["Splice"])         -- ModuleIdent
  Nothing                       -- Maybe ExportSpec
  []                            -- [ImportDecl]
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
            e
            []
          )
      ]
  ]