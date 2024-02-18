
module In where

open import Foundations.Base

open import Data.String
open import Data.List
open import Data.Nat
open import Data.Unit
open import Data.Float.Base

private variable
  A  : 𝒰
  b  : A
  as bs : List A

data _∈_ (a : A) : List A → 𝒰 where
  𝟙   :          a ∈ (a ∷ as)
  𝟘∷_ : a ∈ as → a ∈ (b ∷ as)

𝟘⋯𝟘∷_ : b ∈ bs → b ∈ (as ++ bs)
𝟘⋯𝟘∷_ {as = []} ptr = ptr
𝟘⋯𝟘∷_ {as = x ∷ as} ptr = 𝟘∷ 𝟘⋯𝟘∷ ptr

_∷𝟘⋯𝟘 : b ∈ bs → b ∈ (bs ++ as)
𝟙 ∷𝟘⋯𝟘 = 𝟙
(𝟘∷ ptr) ∷𝟘⋯𝟘 = 𝟘∷ (ptr ∷𝟘⋯𝟘)


infixr 4.5 𝟘⋯𝟘∷_ 𝟘∷_
infixl 4.5 _∷𝟘⋯𝟘
