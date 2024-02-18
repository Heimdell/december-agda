
module Sub where

open import Foundations.Base
open import Data.List
open import Data.String

open import In
open import All

private variable
  A : 𝒰
  a : A
  Γ Δ Ε Φ : List A

_⊂_ : List A → List A → 𝒰
Γ ⊂ Δ = All (_∈ Δ) Γ

_◂_ : (ptr : a ∈ Γ) (sub : Γ ⊂ Δ) → a ∈ Δ
𝟙 ◂ (x ∷ sub) = x
(𝟘∷ ptr) ◂ (x ∷ sub) = ptr ◂ sub

_•_ : (Γ⊂Δ : Γ ⊂ Δ) (Δ⊂Ε : Δ ⊂ Ε) → Γ ⊂ Ε
[] • Δ⊂Ε = []
(x ∷ Γ⊂Δ) • Δ⊂Ε = (x ◂ Δ⊂Ε) ∷ (Γ⊂Δ • Δ⊂Ε)

⟨𝟘⋯𝟘⟩∷_ : (Γ⊂Δ : Γ ⊂ Δ) → Γ ⊂ (Ε ++ Δ)
⟨𝟘⋯𝟘⟩∷_ {Ε = []} Γ⊂Δ = Γ⊂Δ
⟨𝟘⋯𝟘⟩∷_ {Ε = x ∷ Ε} [] = []
⟨𝟘⋯𝟘⟩∷_ {Ε = x ∷ Ε} (x₁ ∷ Γ⊂Δ) = (𝟘⋯𝟘∷ x₁) ∷ (⟨𝟘⋯𝟘⟩∷ Γ⊂Δ)

infixr 4.5 ⟨𝟘⋯𝟘⟩∷_

⟨𝟘⟩∷_ : (Γ⊂Δ : Γ ⊂ Δ) → Γ ⊂ (a ++ Δ)
⟨𝟘⟩∷_ = ⟨𝟘⋯𝟘⟩∷_

_⊕_ : (Γ⊂Δ : Γ ⊂ Δ) (Ε⊂Φ : Ε ⊂ Φ) → (Γ ++ Ε) ⊂ (Δ ++ Φ)
[] ⊕ Ε⊂Φ = ⟨𝟘⋯𝟘⟩∷ Ε⊂Φ
(x ∷ Γ⊂Δ) ⊕ Ε⊂Φ = (x ∷𝟘⋯𝟘) ∷ (Γ⊂Δ ⊕ Ε⊂Φ)

𝟙⋯𝟙 : Γ ⊂ Γ
𝟙⋯𝟙 {Γ = []} = []
𝟙⋯𝟙 {Γ = x ∷ Γ} = 𝟙 ∷ map-all 𝟘∷_ 𝟙⋯𝟙
