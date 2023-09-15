{-# LANGUAGE GADTs #-}
{-@ LIQUID "--extensionality" @-}
{-@ LIQUID "--higherorder"    @-}
{-@ LIQUID "--no-termination" @-}
{-@ LIQUID "--reflection"     @-}

module MyNat where

import MyBool

import Language.Haskell.Liquid.Equational
import Prelude (Show, undefined)

------------------------------------------------------------------------
-- Data type for natural numbers
------------------------------------------------------------------------
data N where 
  O :: N
  S :: N -> N
  deriving (Show)


------------------------------------------------------------------------
-- Functions on natural numbers
------------------------------------------------------------------------
-- Some introductory functions
{-@ inline pos @-}
{-@ pos :: N -> Bool @-}
pos = \n -> case n of { O -> F; S k -> T }

{-@ reflect pred @-}    -- TODO: ¿Why inline doesn't work here?
{-@ pred :: N -> N @-}
pred = \n -> case n of { O -> O; S k -> k }

{-@ reflect par @-}
{-@ par :: N -> Bool @-}
par = \n -> case n of { O -> T; S k -> neg (par k) }

{-@ reflect doble @-}
{-@ doble :: N -> N @-}
doble = \n -> case n of { O -> O; S k -> S(S(doble k)) }

-- Some higher-order functions on intervals
{-@ reflect existe @-}
{-@ existe :: N -> (N -> Bool) -> Bool @-}
existe :: N -> (N -> Bool) -> Bool
existe = \n p -> case n of
    O   -> p O
    S k -> case p (S k) of { F -> existe k p; T -> T }

{-@ reflect todos @-}
{-@ todos :: N -> (N -> Bool) -> Bool @-}
todos :: N -> (N -> Bool) -> Bool
todos = \n p -> case n of
    O   -> p O
    S k -> case p (S k) of { F -> F; T -> todos k p }

{-@ reflect contar @-}
{-@ contar :: N -> (N -> Bool) -> N @-}
contar :: N -> (N -> Bool) -> N
contar = \n p -> case n of
    O   -> case p O of { F -> O; T -> S O }
    S k -> case p (S k) of { F -> contar k p; T -> S (contar k p) }

-- Formalizing arithmetic   
-- NOTE: We can't use the common symbols like + or *, because LH confuses them with the Prelude versions   
--       So, we prefix and suffix them with a dot, e.g. + is .+. and * is .*.
{-@ infixr 2 .+. @-}         
{-@ reflect .+. @-}
{-@ (.+.) :: N -> N -> N @-}
(.+.) = \m n -> case m of { O -> n; S k -> S (k .+. n) }
-- Alt. with pattern matching:
-- O     .+. n = n
-- (S k) .+. n = S (k .+. n)

{-@ infixl 3 .*. @-}
{-@ reflect .*.  @-}
{-@ (.*.) :: N -> N -> N @-}
(.*.) = \m n -> case m of { O -> O; S k -> n .+. (k .*. n) }
-- Alt. with pattern matching:
-- O     .*. n = O
-- (S k) .*. n = n .+. (k .*. n)

{-@ reflect sumfi @-}
{-@ sumfi :: N -> (N -> N) -> N @-}
sumfi :: N -> (N -> N) -> N
sumfi = \n f -> case n of {O -> f O; S k -> sumfi k f .+. f (S k) }

{-@ infixr 8 .==. @-}
{-@ reflect .==. @-}
{-@ (.==.) :: N -> N -> Bool @-}
(.==.) :: N -> N -> Bool
(.==.) = \m n -> case m of 
    O   -> case n of { O -> T; S k -> F }
    S k -> case n of { O -> F; S h -> k .==. h }

{-@ infixr 8 ./=. @-}
{-@ reflect ./=. @-}
(./=.) :: N -> N -> Bool
(./=.) = \m n -> neg (m .==. n)

-- TODO: ¿Is it possible to define and lift Eq type class ?

{-@ infixr 7 .<=. @-}
{-@ reflect .<=. @-}
{-@ (.<=.) :: N -> N -> Bool @-}
(.<=.) :: N -> N -> Bool
(.<=.) = \m n -> case m of 
    O   -> T
    S k -> case n of { O -> F; S h -> k .<=. h }    


------------------------------------------------------------------------
-- Proofs
------------------------------------------------------------------------
-- Proposition. ∀ n:N. par (doble n) = T
{-@ prp_ParDoble :: n:N -> { par (doble n) = T } @-}
prp_ParDoble :: N -> Proof
-- Proceed by induction on n:N
-- CB) n = O
prp_ParDoble O =
      par (doble O)     ? doble
  ==. par O             ? par
  ==. T  
  *** QED
-- n = S k
-- HI) par (doble k) = T
-- TI) par (doble (S k)) =? T
prp_ParDoble (S k) =
      par (doble (S k))           ? doble
  ==. par (S (S (doble k)))       ? par      
  ==. neg (par (S (doble k)))     ? par   
  ==. neg (neg (par (doble k)))   ? prp_ParDoble k -- HI 
  ==. neg (neg T)                 ? prp_NegInv
  ==. T
  *** QED

-- Proposition. ∀ m,n:N. m + (S n) = S(m + n)
{-@ prp_AddSucRight :: m:N -> n:N ->  { m .+. (S n) = S (m .+. n) } @-}
prp_AddSucRight :: N -> N -> Proof
prp_AddSucRight m n = undefined   -- TODO

-- Proposition. ∀ n:N. doble n = n + n
{-@ prp_DobleAdd :: n:N -> { doble n = n .+. n } @-}
prp_DobleAdd :: N -> Proof
-- Proceed by induction on n:N
-- CB) n = O
prp_DobleAdd O =
      doble O                ? doble
  ==. O                      ? (.+.)
  ==. O .+. O  
  *** QED
-- n = S k  
-- HI) doble k = k + k
-- TI) doble (S k) =? (S k) + (S k)
prp_DobleAdd (S k) =
      doble (S k)            ? doble
  ==. S (S (doble k))        ? prp_DobleAdd k  -- HI     
  ==. S (S (k .+. k))        ? prp_AddSucRight k k  
  ==. S (k .+. (S k))        ? (.+.)
  ==. (S k) .+. (S k)
  *** QED

-- Proposition. ∀ n:N. O + n = n
{-@ prp_AddIdLeft :: n:N -> { O .+. n = n } @-}
prp_AddIdLeft :: N -> Proof
prp_AddIdLeft n =
      O .+. n      ? (.+.)
  ==. n         
  *** QED

-- Proposition. ∀ n:N. n + O = n
{-@ prp_AddIdRight :: n:N -> { n .+. O = n } @-}
prp_AddIdRight :: N -> Proof
-- Proceed by induction on n:N
-- CB) n = O
prp_AddIdRight O = 
      O .+. O          ? (.+.)
  ==. O                
  *** QED
-- n = S k  
-- HI) k + O = k
-- TI) (S k) + O =? S k
prp_AddIdRight (S k) = 
      (S k) .+. O      ? (.+.)
  ==. S (k .+. O)      ? prp_AddIdRight k -- HI 
  ==. S k
  *** QED

-- Our equality (.==.) on N reflects mathematical equality.

-- Proposition. ∀ n:N. n == n = T
{-@ prp_EqNrefl :: n:N -> { n .==. n = T } @-}
prp_EqNrefl :: N -> Proof
-- Proceed by induction on n:N
-- CB) n = O
prp_EqNrefl O =
      O .==. O               ? (.==.)
  ==. T
  *** QED
-- n = S k  
-- HI) k == k = T
-- TI) (S k) == (S k) =? T
prp_EqNrefl (S k) =
      (S k) .==. (S k)       ? (.==.)
  ==. k .==. k               ? prp_EqNrefl k  -- HI     
  ==. T       
  *** QED  

-- Proposition. ∀ m,n:N. m == n = n == m 
{-@ prp_EqNComm :: m:N -> n:N -> { m .==. n = n .==. m } @-}
prp_EqNComm :: N -> N -> Proof
-- Proceed by induction on m:N
-- TODO: ¿Can we set this proof in a more hierarchical style?
-- CB) m=O, ∀ n:N
--   Proceed by induction on n:N
--   CB) n=O
prp_EqNComm O O =
      O .==. O               -- trivial, equality is reflexive 
  ==. O .==. O
  *** QED
--   n = S k  
--   HI) O == k = k == O
--   TI) O == (S k) =? (S k) == O
prp_EqNComm O (S k) =
      O .==. (S k)            ? (.==.)
  ==. F                       ? (.==.)
  ==. (S k) .==. O
  *** QED
-- m = S k  
-- HI) ∀ n:N. k == n = n == k
-- TI) ∀ n:N. (S k) == n =? n == (S k)
--   Proceed by induction on n:N
--   CB) n=O
prp_EqNComm (S k) O = 
      (S k) .==. O           ? (.==.)
  ==. F                      ? (.==.)
  ==. O .==. (S k)
  *** QED
--   n = S h  
--   HI2) (S k) == h = h == (S k)
--   TI2) (S k) == (S h) =? (S h) == (S k)
prp_EqNComm (S k) (S h) =
      (S k) .==. (S h)       ? (.==.)
  ==. k .==. h               ? prp_EqNComm k h  -- HI, with n=h  
  ==. h .==. k               ? (.==.)
  ==. (S h) .==. (S k)       
  *** QED    

-- Proposition. ∀ m,n:N. (m <= n = T) <=> (∃ k:N. m+k = n)
-- TODO: we can't use quantifiers in the SMT logic
-- {-@ prp_LeqNCorr :: m:N -> n:N -> { (m .<=. n = T) <=> (exists k:N. m .+. k = n) } @-}  
-- prp_LeqNCorr :: N -> N -> Proof  
-- prp_LeqNCorr m n = undefined

-- Next, the behaviour of the <= relation is postulated.

-- Proposition. ∀ n:N. O <= n
{-@ assume prp_LeqZero :: n:N -> { O <= n } @-}
prp_LeqZero :: N -> Proof
prp_LeqZero n = ()

-- Proposition. ∀ n:N. n <= S n
{-@ assume prp_LeqSuc :: n:N -> { n <= S n } @-}
prp_LeqSuc :: N -> Proof
prp_LeqSuc n = ()

-- Proposition. ∀ m,n:N. m <= n  ==>  S m <= S n 
{-@ assume prp_LeqSucMono :: m:N -> n:N -> ({ m <= n }) -> { (S m) <= (S n) } @-}
prp_LeqSucMono :: N -> N -> Proof -> Proof
prp_LeqSucMono m n pf = ()

