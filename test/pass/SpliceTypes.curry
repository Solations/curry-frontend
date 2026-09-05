module SpliceTypes where

import TemplateCurry

three :: $(pure ((CTCons ("Prelude", "Int")))) -> $(pure ((CTCons ("Prelude", "Int"))))
three _ = 3
