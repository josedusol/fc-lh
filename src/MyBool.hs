{-# LANGUAGE GADTs #-}
{-@ LIQUID "--reflection" @-}

module MyBool where

import Language.Haskell.Liquid.Equational
import Prelude hiding (Bool)

------------------------------------------------------------------------
-- Data type for boolean values
------------------------------------------------------------------------
data Bool where
  F :: Bool
  T :: Bool
  deriving (Show)


------------------------------------------------------------------------
-- Functions on Bool
------------------------------------------------------------------------
-- NOTE: We can't use common names and symbols like not, && and || because LH
-- confuses them with the Prelude versions. So, not is neg, and for the rest
-- we prefix and suffix them with a dot, e.g. && is .&&. and || is .||.
{-@ inline neg @-}
{-@ neg :: Bool -> Bool @-}     
neg :: Bool -> Bool
neg = \b -> case b of {F -> T; T -> F}
-- Alt. with pattern matching:
-- neg F = T
-- neg T = F

{-@ infixr 4 .&&. @-}
{-@ inline .&&.   @-}
{-@ (.&&.) :: Bool -> Bool -> Bool @-}
(.&&.) = \b1 b2 -> case b1 of {F -> F; T -> b2}
-- Alt. with pattern matching:
-- F .&&. _  = F
-- T .&&. b2 = b2

{-@ infixr 3 .||. @-}
{-@ inline .||.   @-}
{-@ (.||.) :: Bool -> Bool -> Bool @-}
(.||.) = \b1 b2 -> case b1 of {F -> b2; T -> T}
-- Alt. with pattern matching:
-- F .||. b2 = b2
-- T .||. _  = T

{-@ infixr 2 .>>. @-}
{-@ inline .>>.   @-}
{-@ (.>>.) :: Bool -> Bool -> Bool @-}
(.>>.) = \b1 b2 -> case b1 of {F -> T; T -> b2}
-- Alt. with pattern matching:
-- F .>>. _  = T
-- T .>>. b2 = b2

{-@ infixr 3 .<=>. @-}
{-@ inline .<=>.   @-}
{-@ (.<=>.) :: Bool -> Bool -> Bool @-}
(.<=>.) :: Bool -> Bool -> Bool
(.<=>.) = \b1 b2 -> case b1 of {F -> b2; T -> neg b2}
-- Alt. with pattern matching:
-- F .<=>. b2 = b2
-- T .<=>. b2 = neg b2 


------------------------------------------------------------------------
-- Proofs
------------------------------------------------------------------------
-- neg is an involutive function.
-- Lemma:  ∀ b:Bool. neg (neg b) = b
{-@ prp_NegInv :: b:Bool -> { neg (neg b) = b } @-}
prp_NegInv :: Bool -> Proof
-- Proceed by cases on b:Bool
-- Case b=F:
prp_NegInv F = 
      neg (neg F)                                      ? neg   
  ==. neg ((\b -> case b of {F -> T; T -> F }) F)      -- ? case  , produces warning: [-Woverlapping-patterns]
  ==. neg (case F of {F -> T; T -> F })                ? neg
  ==. neg T                                           
  ==. F            
  *** QED
-- Case b=T:
prp_NegInv T = 
      neg (neg T)     ? neg   
  ==. neg F           ? neg
  ==. T              
  *** QED

-- F dominates/absorbs to the left of conjunction.
-- Lemma:  ∀ b:Bool. F && b = F
{-@ prp_AndZeroLeft :: b:Bool -> { F .&&. b = F } @-}
prp_AndZeroLeft :: Bool -> Proof
prp_AndZeroLeft b = 
      F .&&. b        ? (.&&.) 
  ==. F                   
  *** QED

-- F dominates/absorbs to the right of conjunction.
-- Lemma:  ∀ b:Bool. b && F = F
{-@ prp_AndZeroRight :: b:Bool -> { b .&&. F = F } @-}
prp_AndZeroRight :: Bool -> Proof
-- Proceed by cases on b:Bool
-- Case b=F:
prp_AndZeroRight F = 
      F .&&. F        ? (.&&.)   
  ==. F                 
  *** QED  
-- Case b=T:
prp_AndZeroRight T = 
      T .&&. F        ? (.&&.)  
  ==. F                  
  *** QED    

-- T is identity to the left of conjunction.
-- Lemma:  ∀ b:Bool. T && b = b
{-@ prp_AndIdLeft :: b:Bool -> { T .&&. b = b } @-}
prp_AndIdLeft :: Bool -> Proof
prp_AndIdLeft b = undefined         -- TODO

-- T is identity to the right of conjunction.
-- Lema:  ∀ b:Bool. b && T = b
{-@ prp_AndIdRight :: b:Bool -> { b .&&. T = b } @-}
prp_AndIdRight :: Bool -> Proof
prp_AndIdRight b = undefined         -- TODO

-- Conjunction is commutative.
-- Lemma:  ∀ b1,b2:Bool. b1 && b2 = b2 && b1
{-@ prp_AndCommutativity :: b1:Bool -> b2:Bool -> { b1 .&&. b2 = b2 .&&. b1 } @-}
prp_AndCommutativity :: Bool -> Bool -> Proof  
-- Proceed by cases on b1:Bool
-- Case b1=F:
prp_AndCommutativity F b2 = 
      F .&&. b2             ? prp_AndZeroLeft  
  ==. F                     ? prp_AndZeroRight       
  ==. b2 .&&. F            
  *** QED    
-- Case b1=T:
prp_AndCommutativity T b2 = 
      T .&&. b2             ? prp_AndIdLeft 
  ==. b2                    ? prp_AndIdRight     
  ==. b2 .&&. T           
  *** QED      

-- Disjunction is commutative.
-- Lemma:  ∀ b1,b2:Bool. b1 || b2 = b2 || b1
{-@ prp_OrCommutativity :: b1:Bool -> b2:Bool -> { (b1 .||. b2) = (b2 .||. b1) } @-}
prp_OrCommutativity :: Bool -> Bool -> Proof  
-- Proceed by cases on b1:Bool, and then on b2:Bool.
-- That is, we need to consider the four posible cases.  
-- TODO: ¿Can we set this proof in a more hierarchical style?
-- Case b1=F y b2=F:
prp_OrCommutativity F F = 
      F .||. F 
  ==. F .||. F             -- ? trivial, equality is reflexive    
  *** QED    
-- Case b1=F y b2=T:
prp_OrCommutativity F T = 
      F .||. T             ? (.||.) 
  ==. T                    ? (.||.)       
  ==. T .||. F             
  *** QED    
-- Case b1=T y b2=F:
prp_OrCommutativity T F = 
      T .||. F             ? (.||.)   
  ==. T                    ? (.||.)  
  ==. F .||. T                 
  *** QED    
-- Case b1=T y b2=T:
prp_OrCommutativity T T = 
      T .||. T  
  ==. T .||. T             -- ? trivial, equality is reflexive    
  *** QED      