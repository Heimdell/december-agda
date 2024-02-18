
module Info where

open import Foundations.Base
open import Data.String
open import Data.Nat
open import Data.List

open import Thin

record Info : 𝒰 where
  field
    file   : String
    line   : ℕ
    column : ℕ
open Info public

record ᵢ_ (S : 𝒰) : 𝒰 where
  constructor _at_
  field
    body : S
    info : Info
open ᵢ_ public

infix 4.2 ᵢ_

instance
  Thin-ᵢ : {A : 𝒰} {S : List A → 𝒰} ⦃ _ : Thin S ⦄ → Thin λ T → ᵢ S T
  Thin-ᵢ .thin Γ⊂Δ (body₁ at info₁) = (thin Γ⊂Δ body₁) at info₁
