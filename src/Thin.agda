
module Thin where

open import Foundations.Base

open import Data.List

open import Sub

private variable
  A   : 𝒰
  Γ Δ : List A

record Thin {A : 𝒰} (S : List A → 𝒰) : 𝒰 where
  field
    thin : (Γ⊂Δ : Γ ⊂ Δ) (SΓ : S Γ) → S Δ
open Thin ⦃...⦄ public

instance
  Thin-List : {S : List A → 𝒰} ⦃ _ : Thin S ⦄ → Thin (List ∘ S)
  Thin-List .thin = map ∘ thin

  Thin-Second : {S : List A → 𝒰} {T : 𝒰} ⦃ _ : Thin S ⦄ → Thin λ G → T × S G
  Thin-Second .thin th (t , s) = t , thin th s

open import All

instance
  Thin-All :
    {B  : 𝒰}
    {P  : List B → A → 𝒰}
    ⦃ _ : ∀{a} → Thin λ T → P T a ⦄
    {xs : List A}
         → Thin λ T → All (P T) xs
  Thin-All .thin Γ⊂Δ [] = []
  Thin-All .thin Γ⊂Δ (x ∷ SΓ) = thin Γ⊂Δ x ∷ thin Γ⊂Δ SΓ