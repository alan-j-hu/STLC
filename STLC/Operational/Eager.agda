{-# OPTIONS --safe #-}
module STLC.Operational.Eager where

open import STLC.Syntax
open import STLC.Operational.Base
open import Data.Empty using (⊥-elim)
open import Data.Product using (∃-syntax; _,_)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Nat using (ℕ; zero; suc; _+_)
open import Data.Fin using (Fin; _≟_) renaming (zero to fzero; suc to fsuc)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; cong)
open import Relation.Nullary using (yes; no; ¬_)

private
  variable
    m n : ℕ
    L M M' N N' : Term n
    A B C : Type
    Γ Δ : Ctx n
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
      ---------------------------------
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

progress : ● ⊢ M ⦂ A → Value M ⊎ (∃[ N ] (M ↦ N))
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

weakening-var
  : ∀ {Γ : Ctx n} {v' : Fin (suc n)} → Γ ∋ v ⦂ A → liftΓ Γ v' B ∋ Data.Fin.punchIn v' v ⦂ A
weakening-var {v' = fzero} vzero = vsuc vzero
weakening-var {v' = fsuc n} vzero = vzero
weakening-var {v' = fzero} (vsuc v) = vsuc (vsuc v)
weakening-var {v' = fsuc n} (vsuc v) = vsuc (weakening-var v)

-- | The weakening lemma: A term typeable in a context is typeable in an extended context.
--
-- https://www.seas.upenn.edu/~sweirich/dsss17/html/Stlc.Lec2.html
weakening
  : ∀ {Γ : Ctx n} {v : Fin (suc n)} {t : Type} → Γ ⊢ M ⦂ A → liftΓ Γ v t ⊢ lift M v ⦂ A
weakening (ty-abs body) = ty-abs (weakening body)
weakening (ty-app f x) = ty-app (weakening f) (weakening x)
weakening (ty-var v) = ty-var (weakening-var v)
weakening ty-⋆ = ty-⋆
weakening (ty-pair l r) = ty-pair (weakening l) (weakening r)
weakening (ty-projₗ p) = ty-projₗ (weakening p)
weakening (ty-projᵣ p) = ty-projᵣ (weakening p)

lemma : ∀ {Γ : Ctx n} → (v : Fin (suc n)) → liftΓ Γ v B ∋ v ⦂ A → A ≡ B
lemma fzero vzero = refl
lemma {Γ = _ ,- _} (fsuc fin) (vsuc v) = lemma fin v

subst-eq
  : (v : Fin (suc n))
  → liftΓ Γ v B ∋ v ⦂ A
  → Γ ⊢ M ⦂ B
  → Γ ⊢ var v [ v ≔ M ] ⦂ A
subst-eq fzero vzero typing = typing
subst-eq {Γ = Γ ,- C} (fsuc fin) (vsuc v) typing with fin ≟ fin
... | yes refl rewrite lemma fin v = typing
... | no neq = ⊥-elim (neq refl)

subst-neq
  : (v v' : Fin (suc n))
  → liftΓ Γ v B ∋ v' ⦂ A
  → (prf : ¬ v ≡ v')
  → Γ ∋ (Data.Fin.punchOut prf) ⦂ A
subst-neq v v' v-typing neq with v ≟ v'
... | yes refl = ⊥-elim (neq refl)
subst-neq fzero fzero _ _ | no neq = ⊥-elim (neq refl)
subst-neq {Γ = Γ ,- C} fzero (fsuc fin) (vsuc v-typing) _ | no neq = v-typing
subst-neq {Γ = Γ ,- C} (fsuc fin) fzero vzero _ | no neq = vzero
subst-neq {Γ = Γ ,- C} (fsuc fin) (fsuc fin') (vsuc v-typing) neq | no _ =
  vsuc (subst-neq fin fin' v-typing λ { assump → neq (cong fsuc assump) })

-- | The substitution lemma: Substitution preserves typing.
subst
  : ∀ {Γ : Ctx n}
  → liftΓ Γ v B ⊢ M ⦂ A → Γ ⊢ N ⦂ B
  → Γ ⊢ M [ v ≔ N ] ⦂ A
subst (ty-abs body) typing = ty-abs (subst body (weakening typing))
subst (ty-app f x) typing = ty-app (subst f typing) (subst x typing)
subst {v = v} {Γ = _} (ty-var {v = v'} v-typing) typing with v' ≟ v
... | yes refl = subst-eq v v-typing typing
subst {v = fzero} (ty-var {v = fzero} v-typing) typing | no neq = ⊥-elim (neq refl)
subst {v = fzero} (ty-var {v = fsuc v'} (vsuc v-typing)) typing | no neq = ty-var v-typing
subst {v = fsuc v} {Γ = Γ ,- C} (ty-var {v = fzero} vzero) typing | no neq = ty-var vzero
subst {v = fsuc v} {Γ = Γ ,- C} (ty-var {v = fsuc v'} (vsuc v-typing)) typing | no neq
  with v ≟ v'
... | yes eq = ⊥-elim (neq (cong fsuc (sym eq)))
... | no neq' = ty-var (vsuc (subst-neq v v' v-typing _))
subst ty-⋆ _ = ty-⋆
subst (ty-pair l r) typing = ty-pair (subst l typing) (subst r typing)
subst (ty-projₗ p) typing = ty-projₗ (subst p typing)
subst (ty-projᵣ p) typing = ty-projᵣ (subst p typing)

preservation : ● ⊢ M ⦂ A → M ↦ N → ● ⊢ N ⦂ A
preservation (ty-app M-ty N-ty) (red-head M-step) = ty-app (preservation M-ty M-step) N-ty
preservation (ty-app M-ty N-ty) (red-arg M-val N-step) =
  ty-app M-ty (preservation N-ty N-step)
preservation (ty-app (ty-abs body-ty) N-ty) (red-β N-value) = subst body-ty N-ty
preservation (ty-pair M-ty N-ty) (red-left M-step) = ty-pair (preservation M-ty M-step) N-ty
preservation (ty-pair M-ty N-ty) (red-right _ N-step) =
  ty-pair M-ty (preservation N-ty N-step)
preservation (ty-projₗ M-ty) (red-projₗ-inner M-step) = ty-projₗ (preservation M-ty M-step)
preservation (ty-projₗ (ty-pair M-ty _)) (red-projₗ _ _) = M-ty
preservation (ty-projᵣ M-ty) (red-projᵣ-inner M-step) = ty-projᵣ (preservation M-ty M-step)
preservation (ty-projᵣ (ty-pair _ N-ty)) (red-projᵣ _ _) = N-ty
