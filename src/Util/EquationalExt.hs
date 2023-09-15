
module Util.EquationalExt where

import Language.Haskell.Liquid.Equational

-- More proof combinators.

{-@ (<=.) :: x:a -> y:{a | x <= y} -> {v:a | v == y} @-}
(<=.) :: a -> a -> a 
x <=. y = y 
{-# INLINE (<=.) #-} 
infixl 3 <=.
