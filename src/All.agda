
module All where

open import Foundations.Base

open import Data.List

private variable
  A : 𝒰
  a : A
  as : List A
  P Q : A → 𝒰

data All {A : 𝒰} (P : A → 𝒰) : List A → 𝒰 where
  []  :                  All P []
  _∷_ : P a → All P as → All P (a ∷ as)

map-all : (f : ∀{a} → P a → Q a) (xs : All P as) → All Q as
map-all f [] = []
map-all f (x ∷ xs) = f x ∷ map-all f xs
