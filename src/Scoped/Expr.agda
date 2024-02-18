
module Scoped.Expr where

open import Foundations.Base
open import Data.String
open import Data.Float.Base
open import Data.List

open import Names
open import Info
open import In

open import Scoped.Type

private variable
  es : 𝔼
  -- Δ  : 𝔼

data Literalₛ : 𝒰 where
  S : String → Literalₛ
  F : Float  → Literalₛ

mutual
  data Exprₛ (T : 𝕋) (Γ : 𝔼) : 𝒰 where
    Var : (ref : ᵢ e ∈ Γ) → Exprₛ T Γ

    App : (f x : ᵢ Exprₛ T Γ) → Exprₛ T Γ
    Lam : (body : ᵢ Exprₛ T (e ∷ Γ)) → Exprₛ T Γ

    Ctor : (sym : ᵢ CtorNameₛ) (arg : ᵢ Exprₛ T Γ) → Exprₛ T Γ
    Case : (subj : ᵢ Exprₛ T Γ) (alts : List (Altₛ T Γ)) → Exprₛ T Γ

    Rec : (fields : List (FieldNameₛ × ᵢ Exprₛ T Γ)) → Exprₛ T Γ
    Get : (obj : ᵢ Exprₛ T Γ) (field₀ : ᵢ FieldNameₛ) → Exprₛ T Γ

    Lit : (lit : ᵢ Literalₛ) → Exprₛ T Γ
    FFI : (name : ᵢ String) → Exprₛ T Γ

    _∶_ : (expr : Exprₛ T Γ) (ty : Typeₛ T) → Exprₛ T Γ

    Let : {Δ : 𝔼} (decl : ᵢ ExprDeclₛ T Γ Δ) (body : Exprₛ T (Δ ++ Γ)) → Exprₛ T Γ

    ??? : Exprₛ T Γ

  record Altₛ (T : 𝕋) (Γ : 𝔼) : 𝒰 where
    inductive
    constructor Alt
    field
      ctor : ᵢ CtorNameₛ
      arg  :   ExprNameₛ
      body : ᵢ Exprₛ T (arg ∷ Γ)

  data ExprDeclₛ (T : 𝕋) (Γ : 𝔼) : 𝔼 → 𝒰 where
    Sig  : (sig : Schemeₛ Typeₛ T) → ExprDeclₛ T Γ (e ∷ [])
    Decl : (for : ᵢ e ∈ Γ) (body : Exprₛ T Γ) → ExprDeclₛ T Γ []

open Altₛ public

private variable
  Γ Δ : 𝕋
  G D : 𝔼

open import Sub
open import Thin

instance
  mutual
    {-# TERMINATING #-}
    Thin-Exprₛ : Thin λ T → Exprₛ T G
    Thin-Exprₛ .thin Γ⊂Δ (Var ref) = Var ref
    Thin-Exprₛ .thin Γ⊂Δ (App f x) = App (thin Γ⊂Δ f) (thin Γ⊂Δ x)
    Thin-Exprₛ .thin Γ⊂Δ (Lam body₁) = Lam (thin Γ⊂Δ body₁)
    Thin-Exprₛ .thin Γ⊂Δ (Ctor sym₁ arg₁) = Ctor sym₁ (thin Γ⊂Δ arg₁)
    Thin-Exprₛ .thin Γ⊂Δ (Case subj alts) = Case (thin Γ⊂Δ subj) (thin Γ⊂Δ alts)
    Thin-Exprₛ .thin Γ⊂Δ (Rec fields) = Rec (thin Γ⊂Δ fields)
    Thin-Exprₛ .thin Γ⊂Δ (Get obj field₀) = Get (thin Γ⊂Δ obj) field₀
    Thin-Exprₛ .thin Γ⊂Δ (Lit lit) = Lit lit
    Thin-Exprₛ .thin Γ⊂Δ (FFI name₁) = FFI name₁
    Thin-Exprₛ .thin Γ⊂Δ (SΓ ∶ ty) = thin Γ⊂Δ SΓ ∶ thin Γ⊂Δ ty
    Thin-Exprₛ .thin Γ⊂Δ (Let decl SΓ) = Let (thin Γ⊂Δ decl) (thin Γ⊂Δ SΓ)
    Thin-Exprₛ .thin Γ⊂Δ ??? = ???

    Thin-Altₛ : Thin λ T → Altₛ T G
    Thin-Altₛ .thin Γ⊂Δ (Alt ctor₁ arg₁ body₁) =
      Alt ctor₁ arg₁ (thin Γ⊂Δ body₁)

    Thin-ExprDeclₛ : Thin λ T → ExprDeclₛ T G D
    Thin-ExprDeclₛ .thin Γ⊂Δ (Sig  sig)       = Sig      (thin Γ⊂Δ sig)
    Thin-ExprDeclₛ .thin Γ⊂Δ (Decl for body₁) = Decl for (thin Γ⊂Δ body₁)