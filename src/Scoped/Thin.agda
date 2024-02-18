
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