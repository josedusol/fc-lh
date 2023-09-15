{-# LANGUAGE GADTs #-}
{-@ LIQUID "--higherorder"    @-}
{-@ LIQUID "--no-termination" @-}
{-@ LIQUID "--reflection"     @-}

module MyList where

import MyBool
import MyNat
import Util.EquationalExt

import Language.Haskell.Liquid.Equational
import Prelude (Show, undefined)

------------------------------------------------------------------------
-- Data type for lists of some type
------------------------------------------------------------------------
data List a where
  E :: List a
  C :: a -> List a -> List a
  deriving (Show)

infixr 5 `C`

{-@ inline single @-}
{-@ single :: a -> List a @-}
single :: a -> List a
single a = a`C`E


------------------------------------------------------------------------
-- Functions on lists
------------------------------------------------------------------------
{-@ inline null @-}
{-@ null :: List a -> Bool @-}
null :: List a -> Bool
null = \l -> case l of { E -> T ; x`C`xs -> F}

{-@ reflect sum @-}
{-@ sum :: List N -> N @-}
sum :: List N -> N
sum = \l -> case l of { E -> O; x`C`xs -> x .+. sum xs }

{-@ reflect length @-}
{-@ length :: List a -> N @-}
length :: List a -> N
length = \l -> case l of { E -> O; x`C`xs -> S (length xs) }

-- TODO: generalize "elem" for any type implementing type class Eq
{-@ reflect elemN @-}
{-@ elemN :: N -> List N -> Bool @-}
elemN :: N -> List N -> Bool
elemN = \e l -> case l of { E -> F; x`C`xs -> (x .==. e) .||. elemN e xs }

{-@ reflect elemB @-}
{-@ elemB :: Bool -> List Bool -> Bool @-}
elemB :: Bool -> List Bool -> Bool
elemB = \e l -> case l of { E -> F; x`C`xs -> (x .<=>. e) .||. elemB e xs }

{-@ reflect map @-}
{-@ map :: (a -> b) -> List a -> List b @-}
map :: (a -> b) -> List a -> List b
map = \f l -> case l of { E -> E; x`C`xs -> f x `C` map f xs }

{-@ reflect filter @-}
{-@ filter :: (a -> Bool) -> List a -> List a @-}
filter :: (a -> Bool) -> List a -> List a
filter = \p l -> case l of
  E      -> E
  x`C`xs -> case p x of { F -> filter p xs; T -> x `C` filter p xs }

{-@ infixl 7 ++ @-}   
{-@ reflect ++ @-}
{-@ (++) :: List a -> List a -> List a @-}
(++) :: List a -> List a -> List a
(++) = \l1 l2 -> case l1 of { E -> l2; x`C`xs -> x `C` (xs ++ l2) }

{-@ reflect rev @-}
rev :: List a -> List a
rev = \l -> case l of { E -> E; x`C`xs -> rev xs ++ single x }


------------------------------------------------------------------------
-- Proofs
------------------------------------------------------------------------
-- [] is identity to the left of concatenation.
-- Proposition. ∀ l:List a. [] ++ l = l
{-@ prp_ConcatIdLeft :: l:List a -> { E ++ l = l } @-}
prp_ConcatIdLeft :: List a -> Proof
prp_ConcatIdLeft l = 
      E ++ l         ? (++)    
  ==. l                      
  *** QED      

-- [] is identity to the right of concatenation.
-- Proposition. ∀ l:List a. l ++ [] = l
{-@ prp_ConcatIdRight :: l:List a -> { l ++ E = l } @-}
prp_ConcatIdRight :: List a -> Proof
-- Proceed by induction on l:List a
-- CB) l = []
prp_ConcatIdRight E = 
      E ++ E                ? (++)    
  ==. E                      
  *** QED      
-- l = x:xs 
-- HI) xs ++ [] = xs
-- TI) x:xs ++ [] =? x:xs
prp_ConcatIdRight (x`C`xs) =
      (x`C`xs) ++ E         ? (++)    
  ==. x `C` (xs ++ E)       ? prp_ConcatIdRight xs -- HI 
  ==. x `C` xs  
  *** QED  

-- We need to redefine the .+. position again to be used on refinements
-- because their position is not exported across modules.
{-@ infixl 5 .+. @-}  

-- Proposition. ∀ l1,l2:List a. len (l1 ++ l2) = len l1 + len l2
{-@ prp_ConcatLen :: l1:List a -> l2:List a -> { length (l1 ++ l2) = (length l1) .+. (length l2) } @-}
prp_ConcatLen :: List a -> List a -> Proof
-- Proceed by induction on l1:List a and let l2 be any list
-- CB) l1 = []
prp_ConcatLen E l2 = 
      length (E ++ l2)                      ? prp_ConcatIdLeft l2
  ==. length l2                             ? prp_AddIdLeft (length l2)
  ==. O .+. length l2                       ? length
  ==. length E .+. length l2             
  *** QED      
-- l1 = x:xs 
-- HI) len (xs ++ l2) = len xs + len l2
-- TI) len (x:xs ++ l2) =? len x:xs + len l2
prp_ConcatLen (x`C`xs) l2 =
      length ((x`C`xs) ++ l2)               ? (++)    
  ==. length (x `C` (xs ++ l2))             ? length
  ==. S (length (xs ++ l2))                 ? prp_ConcatLen xs l2 -- HI 
  ==. S ((length xs) .+. (length l2))       ? (.+.)
  ==. S (length xs) .+. length l2           ? length
  ==. length (x`C`xs) .+. length l2  
  *** QED    

-- Proposition. ∀ l1,l2,l3:List a. l1 ++ (l2 ++ l3) = (l1 ++ l2) ++ l3
{-@ prp_ConcatAssoc :: l1:List a -> l2:List a -> l3:List a -> { l1 ++ (l2 ++ l3) = (l1 ++ l2) ++ l3 } @-}
prp_ConcatAssoc :: List a -> List a -> List a  -> Proof  
-- Proceed by induction on l1:List a and let l2,l3 be any lists
-- CB) l1 = []
prp_ConcatAssoc E l2 l3 =
      E ++ (l2 ++ l3)                       ? (++)
  ==. l2 ++ l3                              ? (++)
  ==. (E ++ l2) ++ l3                            
  *** QED   
-- l1 = x:xs 
-- HI) xs ++ (l2 ++ l3) = (xs ++ l2) ++ l3
-- TI) x:xs ++ (l2 ++ l3) =? (x:xs ++ l2) ++ l3
prp_ConcatAssoc (x`C`xs) l2 l3 =
      (x`C`xs) ++ (l2 ++ l3)                ? (++)
  ==. x`C`(xs ++ (l2 ++ l3))                ? prp_ConcatAssoc xs l2 l3 -- HI
  ==. x`C`((xs ++ l2) ++ l3)                ? (++)
  ==. (x`C`(xs ++ l2)) ++ l3                ? (++)
  ==. ((x`C`xs) ++ l2) ++ l3   
  *** QED   

-- Proposition. ∀ x:a. rev [x] = [x]
{-@ prp_RevSingle :: x:a -> { rev (single x) = single x } @-}
prp_RevSingle :: a -> Proof
prp_RevSingle x =
      rev (single x)           ? rev
  ==. rev E ++ single x        ? rev
  ==. E ++ single x            ? (++)
  ==. single x
  *** QED   

-- rev distribuye contravariante sobre la concatenación
-- Proposition. ∀ l1,l2:List a. rev (l1 ++ l2) = rev l2 ++ rev l1
{-@ prp_RevConcat :: l1:List a -> l2:List a -> { rev (l1 ++ l2) = rev l2 ++ rev l1 } @-}
prp_RevConcat :: List a -> List a -> Proof
-- Proceed by induction on l1:List a and let l2 be any list
-- CB) l1 = []
prp_RevConcat E l2 =
      rev (E ++ l2)                     ? (++)
  ==. rev l2                            ? prp_ConcatIdRight (rev l2)
  ==. rev l2 ++ E                       ? rev
  ==. rev l2 ++ rev E  
  *** QED   
-- l1 = x:xs 
-- HI) rev (xs ++ l2) = rev l2 ++ rev xs
-- TI) rev (x:xs ++ l2) =? rev l2 ++ rev x:xs
prp_RevConcat (x`C`xs) l2 = 
      rev ((x`C`xs) ++ l2)              ? (++)
  ==. rev (x`C`(xs ++ l2))              ? rev
  ==. rev (xs ++ l2) ++ single x        ? prp_RevConcat xs l2 -- HI
  ==. (rev l2 ++ rev xs) ++ single x    ? prp_ConcatAssoc (rev l2) (rev xs) (single x)
  ==. rev l2 ++ (rev xs ++ single x)    ? rev
  ==. rev l2 ++ (rev (x`C`xs))
  *** QED     

-- rev is an involutive function.
-- This depends on multiple previously proved lemmas. In fact, because rev is defined
-- in terms of ++, and ++ is not a measure, rev is also not a measure and
-- then is not possible to reason automatically about rev or ++.
-- Proposition. ∀ l:List a. rev (rev l) = l
{-@ prp_RevInv :: l:List a -> { rev (rev l) = l } @-}
prp_RevInv :: List a -> Proof
-- Proceed by induction on l:List 
-- CB) l = []
prp_RevInv E =
      rev (rev E)                       ? rev 
  ==. rev E                             ? rev 
  ==. E      
  *** QED  
-- l = x:xs 
-- HI) rev (rev xs) = xs
-- TI) rev (rev x:xs) =? x:xs
prp_RevInv (x`C`xs) = 
      rev (rev (x`C`xs))                ? rev
  ==. rev (rev xs ++ single x)          ? prp_RevConcat (rev xs) (single x)
  ==. rev (single x) ++ rev (rev xs)    ? prp_RevInv xs -- HI
  ==. rev (single x) ++ xs              ? prp_RevSingle x
  ==. single x ++ xs                    ? (++)
  ==. x`C`(E ++ xs)                     ? prp_ConcatIdLeft xs
  ==. x`C`xs
  *** QED 

-- To filter twice is the same as filter only once
-- Proposition. ∀ p:(a -> Bool) a. ∀ l:List a. filter p (filter p l) = filter p l
{-@ prp_FilterIdempotence ::  p:(a -> Bool) -> l:List a -> { filter p (filter p l) = filter p l } @-}
prp_FilterIdempotence :: (a -> Bool) -> List a -> Proof  
-- Proceed by induction on l:List and let p:(a->Bool) be any predicate
-- CB) l = []
prp_FilterIdempotence p E =
      filter p (filter p E)             ? filter p E
  ==. filter p E               
  *** QED 
-- l = x:xs 
-- HI) filter p (filter p xs) = filter p xs
-- TI) filter p (filter p x:xs) =? filter p x:xs
prp_FilterIdempotence p (x`C`xs) =
--     Now proceed by cases on (p x):Bool 
  case p x of 
    F ->      filter p (filter p (x`C`xs))           ? filter p (x`C`xs)
          ==. filter p (filter p xs)                 ? prp_FilterIdempotence p xs  -- HI
          ==. filter p xs                            ? filter p (x`C`xs)
          ==. filter p (x`C`xs)                      
          *** QED 
    T ->      filter p (filter p (x`C`xs))           ? filter p (x`C`xs)
          ==. filter p (x`C`(filter p xs))           ? filter p (x`C`(filter p xs))
          ==. x`C`(filter p (filter p xs))           ? prp_FilterIdempotence p xs   -- HI
          ==. x`C`(filter p xs)                      ? filter p (x`C`xs)
          ==. filter p (x`C`xs)                
          *** QED 

-- Proposition. ∀ p:(a -> Bool) a. ∀ l:List a. length (filter p l) <= length l
{-@ prp_FilterLength :: p:(a -> Bool) -> l:List a -> { length (filter p l) <= length l } @-}
prp_FilterLength :: (a -> Bool) -> List a -> Proof  
-- Proceed by induction on l:List and let p:(a->Bool) be any predicate
-- CB) l = []
prp_FilterLength p E =
      length (filter p E)             ? filter p E
  ==. length E                        ? length E  
  ==. O                               ? prp_LeqZero (length E)
  <=. length E               
  *** QED 
-- l = x:xs 
-- HI) length (filter p xs) <= length xs
-- TI) length (filter p x:xs) <=? length x:xs
prp_FilterLength p (x`C`xs) =
--     Now proceed by cases on (p x):Bool 
  case p x of 
    F ->      length (filter p (x`C`xs))             ? filter
          ==. length (filter p xs)                   ? prp_FilterLength p xs  -- HI 
          <=. length xs                              ? prp_LeqSuc (length xs)   
          <=. S (length xs)                          ? length  
          ==. length (x`C`xs)
          *** QED 
    T ->      length (filter p (x`C`xs))             ? filter
          ==. length (x`C`(filter p xs))             ? length 
          ==. S (length (filter p xs))               ? prp_LeqSucMono (length (filter p xs)) (length xs) (prp_FilterLength p xs) 
          <=. S (length xs)                          ? length
          ==. length (x`C`xs)
          *** QED