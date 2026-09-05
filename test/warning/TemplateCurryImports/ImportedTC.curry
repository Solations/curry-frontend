module TemplateCurryImports.ImportedTC (xOR) where

import TemplateCurry

xOR :: Int -> Q [CFuncDecl]
xOR n = newName "x" >>= \var -> return [CFunc ("Main", "xOr" ++ show n) 1 Public
  (CQualType (CContext []) (CFuncType (CTCons ("Prelude", "Int")) (CTCons ("Prelude", "Int"))))
  [CRule [CPVar var] (CSimpleRhs (CVar var) []),
  CRule [CPVar (mkName "_")] (CSimpleRhs (CLit (CIntc n)) [])]]