module SimpleSplice where

import TemplateCurry

f :: Int
f = $(pure (CLit (CIntc 10)))
