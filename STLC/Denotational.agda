{-# OPTIONS --safe #-}
module STLC.Denotational where

open import STLC.Syntax
open import STLC.Typing
open import Data.Nat using (ℕ; suc)
open import Data.Fin using (Fin) renaming (zero to fzero; suc to fsuc)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Data.Unit using (⊤; tt)

private
  variable
    n : ℕ
    Γ : Ctx n
    A : Type

⟦_⟧ : Type → Set
⟦ A ⇒ B ⟧ = ⟦ A ⟧ → ⟦ B ⟧
⟦ unit ⟧ = ⊤
⟦ A ×' B ⟧ = ⟦ A ⟧ × ⟦ B ⟧

data Env : Ctx n → Set where
  ∅ : Env ●
  ⟨_,_⟩ : Env Γ → ⟦ A ⟧ → Env (Γ ,- A)

lookup : Env {n} Γ → (v : Fin n) → ⟦ find Γ v ⟧
lookup ⟨ ρ , term ⟩ fzero = term
lookup ⟨ ρ , term ⟩ (fsuc n) = lookup ρ n

⟦_⟧⟨_⟩ : ∀ {term : Term n} {type : Type} → (Γ ⊢ term ∈ type) → Env Γ → ⟦ type ⟧
⟦ ty-abs body ⟧⟨ ρ ⟩ = λ x → ⟦ body ⟧⟨ ⟨ ρ , x ⟩ ⟩
⟦ ty-app f x ⟧⟨ ρ ⟩ = ⟦ f ⟧⟨ ρ ⟩ ⟦ x ⟧⟨ ρ ⟩
⟦ ty-var v ⟧⟨ ρ ⟩ = lookup ρ v
⟦ ty-⋆ ⟧⟨ _ ⟩ = tt
⟦ ty-pair l r ⟧⟨ ρ ⟩ = ⟦ l ⟧⟨ ρ ⟩ , ⟦ r ⟧⟨ ρ ⟩
⟦ ty-projₗ p ⟧⟨ ρ ⟩ = proj₁ ⟦ p ⟧⟨ ρ ⟩
⟦ ty-projᵣ p ⟧⟨ ρ ⟩ = proj₂ ⟦ p ⟧⟨ ρ ⟩
