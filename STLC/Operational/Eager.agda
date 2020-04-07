{-# OPTIONS --safe --sized-types #-}
module STLC.Operational.Eager where

open import STLC.Syntax
open import STLC.Operational.Base
open import Data.Product using (∃-syntax; _,_)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Nat using (ℕ; suc)
open import Data.Fin renaming (zero to fzero; suc to fsuc)

private
  variable
    n : ℕ
    L M M' N N' : Term n
    A B : Type
    Γ : Ctx n
    v : Fin n

data Value {n} : Term n → Set where
  abs-value
      -----------------
    : Value (abs A M)
  ⋆-value
      -----------------
    : Value ⋆
  pair-value
    : Value M → Value N
      -----------------
    → Value (pair M N)

infix 6 _↦_

data _↦_ : Term n → Term n → Set where
  red-head
    : M ↦ M'
      ------------------
    → app M N ↦ app M' N
  red-arg
    : Value M → N ↦ N'
      ------------------
    → app M N ↦ app M N'
  red-β
    : Value N
      -----------------------------------
    → app (abs A M) N ↦ M [ fzero ≔ N ]
  red-left
    : M ↦ M'
      --------------------
    → pair M N ↦ pair M' N
  red-right
    : Value M     → N ↦ N'
      --------------------
    → pair M N ↦ pair M N'
  red-projₗ-inner
    : M ↦ M'
      ------------------
    → projₗ M ↦ projₗ M'
  red-projₗ
    : Value M → Value N
      --------------------
    → projₗ (pair M N) ↦ M
  red-projᵣ-inner
    : M ↦ M'
      ------------------
    → projᵣ M ↦ projᵣ M'
  red-projᵣ
    : Value M → Value N
      --------------------
    → projᵣ (pair M N) ↦ N

data  _↦*_ : Term n → Term n → Set where
  pure : M ↦ N → M ↦* N
  id : M ↦* M
  comp : L ↦* M → M ↦* N → L ↦* N

open import STLC.Typing

progress : ● ⊢ M ∈ A → Value M ⊎ (∃[ N ] (M ↦ N))
progress (ty-abs _) = inj₁ abs-value
progress (ty-app {f = f} {x = x} t u) with progress u | progress t
... | inj₁ u-value | inj₁ (abs-value {M = M}) = inj₂ (M [ fzero ≔ x ] , red-β u-value)
... | inj₂ (u' , u-step) | inj₁ t-value = inj₂ (app f u' , red-arg t-value u-step)
... | inj₁ _ | inj₂ (t' , t-step) = inj₂ (app t' x , red-head t-step)
... | inj₂ _ | inj₂ (t' , t-step) = inj₂ (app t' x , red-head t-step)
progress ty-⋆ = inj₁ ⋆-value
progress (ty-pair {a = a} {b = b} t u) with progress t | progress u
... | inj₁ t-value | inj₁ u-value = inj₁ (pair-value t-value u-value)
... | inj₁ t-value | inj₂ (u' , u-step) = inj₂ (pair a u' , red-right t-value u-step)
... | inj₂ (t' , t-step) | _ = inj₂ (pair t' b , red-left t-step)
progress (ty-projₗ t) with progress t
... | inj₁ (pair-value {M = M} M-value N-value) = inj₂ (M , red-projₗ M-value N-value)
... | inj₂ (t' , t-step) = inj₂ (projₗ t' , red-projₗ-inner t-step)
progress (ty-projᵣ t) with progress t
... | inj₁ (pair-value {N = N} M-value N-value) = inj₂ (N , red-projᵣ M-value N-value)
... | inj₂ (t' , t-step) = inj₂ (projᵣ t' , red-projᵣ-inner t-step)

{-preservation : ● ⊢ M ∈ A → M ↦ N → ● ⊢ N ∈ A
preservation (ty-app M-ty N-ty) (red-head M-step) = ty-app (preservation M-ty M-step) N-ty
preservation (ty-app M-ty N-ty) (red-arg M-val N-step) =
  ty-app M-ty (preservation N-ty N-step)
preservation (ty-app (ty-abs body-ty) N-ty) (red-β N-value) = {!!}
preservation (ty-pair M-ty N-ty) (red-left M-step) = ty-pair (preservation M-ty M-step) N-ty
preservation (ty-pair M-ty N-ty) (red-right _ N-step) =
  ty-pair M-ty (preservation N-ty N-step)
preservation (ty-projₗ M-ty) (red-projₗ-inner M-step) = ty-projₗ (preservation M-ty M-step)
preservation (ty-projₗ (ty-pair M-ty _)) (red-projₗ _ _) = M-ty
preservation (ty-projᵣ M-ty) (red-projᵣ-inner M-step) = ty-projᵣ (preservation M-ty M-step)
preservation (ty-projᵣ (ty-pair _ N-ty)) (red-projᵣ _ _) = N-ty-}
