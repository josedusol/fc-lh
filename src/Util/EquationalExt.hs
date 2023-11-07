
module Util.EquationalExt where

import Language.Haskell.Liquid.Equational

-- More proof combinators.

{-@ (<=.) :: x:a -> y:{x <= y} -> {v:a | v == y} @-}
(<=.) :: a -> a -> a 
x <=. y = y 
{-# INLINE (<=.) #-} 
infixl 3 <=.

-- From falsehood, anything follows
{-@ impossible :: {v:a | false} -> b @-}
impossible :: a -> b
impossible _ = undefined

-- Proofs conjunction
-- Useful to justify multiple transformations in one step
(&&&) :: Proof -> Proof -> Proof
x &&& _ = x

-- Proof by SMT
trivial :: Proof
trivial = ()