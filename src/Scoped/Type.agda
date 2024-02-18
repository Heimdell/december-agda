
module Scoped.Type where

open import Foundations.Base

open import Data.List
open import Data.String

open import Names
open import Info
open import In

data Typeₛ (Γ : 𝕋) : 𝒰 where
  Var : (ref     : t ∈ Γ)   → Typeₛ Γ
  App : (f   x   : Typeₛ Γ) → Typeₛ Γ
  _⇒_ : (dom cod : Typeₛ Γ) → Typeₛ Γ
  ??? : ᵢ ⊤                 → Typeₛ Γ

record Schemeₛ (S : 𝕋 → 𝒰) (Γ : 𝕋) : 𝒰 where
  constructor Forall
  field
    args : 𝕋
    ctx  : List (Typeₛ (args ++ Γ))
    body : S (args ++ Γ)
open Schemeₛ public

data TypeCtorₛ (Γ : 𝕋) : 𝒰 where
  Sum  : List (CtorNameₛ  × ᵢ Typeₛ Γ) → TypeCtorₛ Γ
  Prod : List (FieldNameₛ × ᵢ Typeₛ Γ) → TypeCtorₛ Γ
  FFI  : ᵢ String → TypeCtorₛ Γ
  Abs  : ᵢ ⊤ → TypeCtorₛ Γ

open import Thin
open import Sub

private variable
  Γ Δ : 𝕋

th-type : (Γ⊂Δ : Γ ⊂ Δ) (ty : Typeₛ Γ) → Typeₛ Δ
th-type Γ⊂Δ (Var ref)    = Var (ref ◂ Γ⊂Δ)
th-type Γ⊂Δ (App SΓ SΓ₁) = App (th-type Γ⊂Δ SΓ) (th-type Γ⊂Δ SΓ₁)
th-type Γ⊂Δ (SΓ ⇒ SΓ₁)   = th-type Γ⊂Δ SΓ ⇒ th-type Γ⊂Δ SΓ₁
th-type Γ⊂Δ (??? x)      = ??? x

instance
  Thin-Typeₛ : Thin Typeₛ
  Thin-Typeₛ .thin = th-type

  Thin-Schemeₛ : {S : 𝕋 → 𝒰} ⦃ _ : Thin S ⦄ → Thin (Schemeₛ S)
  Thin-Schemeₛ .thin Γ⊂Δ (Forall args₁ ctx₁ body₁) =
    Forall args₁ (thin (𝟙⋯𝟙 ⊕ Γ⊂Δ) ctx₁) (thin (𝟙⋯𝟙 ⊕ Γ⊂Δ) body₁)

  Thin-TypeCtorₛ : Thin TypeCtorₛ
  Thin-TypeCtorₛ .thin Γ⊂Δ (Sum  x) = Sum  (thin Γ⊂Δ x)
  Thin-TypeCtorₛ .thin Γ⊂Δ (Prod x) = Prod (thin Γ⊂Δ x)
  Thin-TypeCtorₛ .thin Γ⊂Δ (FFI  x) = FFI x
  Thin-TypeCtorₛ .thin Γ⊂Δ (Abs  x) = Abs x