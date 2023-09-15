{-# LANGUAGE GADTs #-}
{-@ LIQUID "--no-termination" @-}
{-@ LIQUID "--reflection"     @-}

module MyAB where

import MyBool
import MyList
import MyNat

import Language.Haskell.Liquid.Equational
import Prelude (Show, undefined)

------------------------------------------------------------------------
-- Data type for ABs of some type
------------------------------------------------------------------------
data AB a where
  H :: a -> AB a
  Nodo :: AB a -> AB a -> AB a
  deriving (Show)


------------------------------------------------------------------------
-- Functions on ABs
------------------------------------------------------------------------
{-@ reflect cantH @-}
{-@ cantH :: AB a -> N @-}
cantH :: AB a -> N
cantH = \t -> case t of { H x -> S O; Nodo ti td -> cantH ti .+. cantH td }

{-@ reflect cantN @-}
{-@ cantN :: AB a -> N @-}
cantN :: AB a -> N
cantN = \t -> case t of { H x -> O; Nodo ti td -> S (cantN ti .+. cantN td) }

{-@ reflect hojas @-}
{-@ hojas :: AB a -> List a @-}
hojas :: AB a -> List a
hojas = \t -> case t of { H x -> single x; Nodo ti td -> hojas ti ++ hojas td }


------------------------------------------------------------------------
-- Proofs
------------------------------------------------------------------------

-- Lemma: ∀ t:AB a. cantH t = S (cantN t)
{-@ prp_HojasNodos :: t:AB a -> { cantH t = S (cantN t) } @-}
prp_HojasNodos :: AB a -> Proof
-- Proceed by induction on t:AB a
-- CB) t = H x
prp_HojasNodos (H x) = 
      cantH (H x)                             ? cantH  
  ==. S O                                     ? cantN 
  ==. S (cantN (H x))    
  *** QED      
-- t = Nodo t1 t2 
-- HI1) cantH t1 = S (cantN t1)
-- HI2) cantH t2 = S (cantN t2)
-- TI)  cantH (Nodo t1 t2) =? S (cantN (Nodo t1 t2))
prp_HojasNodos (Nodo t1 t2) =
      cantH (Nodo t1 t2)                      ? cantH  
  ==. cantH t1 .+. cantH t2                   ? prp_HojasNodos t1   -- HI1
  ==. S (cantN t1) .+. cantH t2               ? prp_HojasNodos t2   -- HI2  
  ==. S (cantN t1) .+. S (cantN t2)           ? (.+.)
  ==. S (cantN t1 .+. S (cantN t2))           ? prp_AddSucRight (cantN t1) (cantN t2)
  ==. S (S (cantN t1 .+. cantN t2))           ? cantN
  ==. S (cantN (Nodo t1 t2))    
  *** QED