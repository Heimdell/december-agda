
module Scoped where

open import Foundations.Base

open import Data.String
open import Data.List
open import Data.Nat
open import Data.Unit
open import Data.Float.Base

open import In
open import Info
open import Kind
open import Names
open import Thin
open import Sub
open import Scoped.Type
open import Scoped.Expr

record TypeDeclₛ (t : TyNameₛ) (Γ : 𝕋) : 𝒰 where
  constructor TypeDecl
  field
    expr : Schemeₛ TypeCtorₛ Γ
open TypeDeclₛ public

instance
  Thin-TypeDeclₛ : Thin (TypeDeclₛ t)
  Thin-TypeDeclₛ .thin Γ⊂Δ (TypeDecl expr₁) = TypeDecl (thin Γ⊂Δ expr₁)

record TypeSigₛ (t : TyNameₛ) : 𝒰 where
  constructor TypeSig
  field
    sig : Kindₛ
open TypeSigₛ public


open import All

record ClassBodyₛ (T : 𝕋) (t : TyNameₛ) (Δ : 𝔼) : 𝒰 where
  constructor Class
  field
    args    : 𝕋
    header  : Typeₛ (t ∷ T)
    deps    : List (Typeₛ T)
    methods : All (λ _ → Schemeₛ Typeₛ T) Δ
open ClassBodyₛ public

Classₛ : (T : 𝕋) (t : TyNameₛ) (Δ : 𝔼) → 𝒰
Classₛ T t Δ = Schemeₛ (λ T → ClassBodyₛ T t Δ) T

instance
  Thin-Classₛ : ∀{Δ} → Thin λ T → ClassBodyₛ T t Δ
  Thin-Classₛ .thin Γ⊂Δ (Class args₁ header₁ deps₁ methods₁) =
    Class
      args₁
      (thin (𝟙⋯𝟙 ⊕ Γ⊂Δ) header₁)
      (thin Γ⊂Δ deps₁)
      (thin Γ⊂Δ methods₁)

record InstanceBodyₛ (t : TyNameₛ) (T : 𝕋) (Γ : 𝔼) : 𝒰 where
  constructor Instance
  field
    class      : t ∈ T
    header     : Typeₛ (t ∷ T)
    deps       : List (Typeₛ T)
    {captured} : 𝔼
    capture    : captured ⊂ Γ
    methods    : All (λ _ → Exprₛ T Γ) captured
open InstanceBodyₛ public

Instanceₛ : (T : 𝕋) (t : TyNameₛ) (Δ : 𝔼) → 𝒰
Instanceₛ T t Δ = Schemeₛ (λ T → InstanceBodyₛ t T Δ) T

instance
  Thin-Instanceₛ : ∀{Δ} → Thin λ T → InstanceBodyₛ t T Δ
  Thin-Instanceₛ .thin Γ⊂Δ (Instance class₁ header₁ deps₁ capt methods₁) =
    Instance
      (class₁ ◂ Γ⊂Δ)
      (thin (𝟙⋯𝟙 ⊕ Γ⊂Δ) header₁)
      (thin        Γ⊂Δ  deps₁)
      capt
      (thin        Γ⊂Δ  methods₁)

record TopExprDeclₛ (T : 𝕋) (Γ Δ : 𝔼) : 𝒰 where
  constructor TopExprDecl
  field
    decl : ExprDeclₛ T Γ Δ
open TopExprDeclₛ public

instance
  Thin-TopExprDeclₛ : ∀{Γ Δ} → Thin λ T → TopExprDeclₛ T Γ Δ
  Thin-TopExprDeclₛ .thin Γ⊂Δ (TopExprDecl decl₁) =
    TopExprDecl (thin Γ⊂Δ decl₁)

private variable
  T U : 𝕋
  Γ Δ Ε : 𝔼

data Programₛ (T : 𝕋) (Γ : 𝔼) : 𝕋 → 𝔼 → 𝒰 where
  Start          : Programₛ T Γ U Δ
  _,value_       : Programₛ T Γ U Δ        → TopExprDeclₛ T Γ Ε → Programₛ T Γ U (Δ ++ Ε)
  _,type⟨_⟩_     : Programₛ T Γ U Δ → t ∈ T → TypeDeclₛ    t T   → Programₛ T Γ U Δ
  _,sig_         : Programₛ T Γ U Δ         → TypeSigₛ     t     → Programₛ T Γ (t ∷ U) Δ
  _,class_       : Programₛ T Γ U Δ         → Classₛ       T t Ε → Programₛ T Γ (t ∷ U) (Ε ++ Δ)
  _,instance⟨_⟩_ : Programₛ T Γ U Δ → t ∈ T → Instanceₛ    T t Ε → Programₛ T Γ (t ∷ U) (Ε ++ Δ)

instance
  {-# TERMINATING #-}
  Thin-Programₛ : Thin λ T → Programₛ T Γ U Δ
  Thin-Programₛ .thin Γ⊂Δ Start = Start
  Thin-Programₛ .thin Γ⊂Δ (SΓ ,value x) = thin Γ⊂Δ SΓ ,value thin Γ⊂Δ x
  Thin-Programₛ .thin Γ⊂Δ (SΓ ,type⟨ x ⟩ x₁) = thin Γ⊂Δ SΓ ,type⟨ x ◂ Γ⊂Δ ⟩ thin Γ⊂Δ x₁
  Thin-Programₛ .thin Γ⊂Δ (SΓ ,sig x) = thin Γ⊂Δ SΓ ,sig x
  Thin-Programₛ .thin Γ⊂Δ (SΓ ,class x) = thin Γ⊂Δ SΓ ,class thin Γ⊂Δ x
  Thin-Programₛ .thin Γ⊂Δ (SΓ ,instance⟨ x ⟩ x₁) = thin Γ⊂Δ SΓ ,instance⟨ x ◂ Γ⊂Δ ⟩ thin Γ⊂Δ x₁