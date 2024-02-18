
module Kind where

open import Foundations.Base

data Kindₛ : 𝒰 where
  ∗ # : Kindₛ
  _⇒_ : (dom cod : Kindₛ) → Kindₛ

infixr 5 _⇒_
