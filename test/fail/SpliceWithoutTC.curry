module SpliceWithoutTC where

f :: Int
f = $(pure (CLit (CIntc 10)))