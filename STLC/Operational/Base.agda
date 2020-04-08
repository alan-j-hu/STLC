{-# OPTIONS --safe #-}
module STLC.Operational.Base where

open import STLC.Syntax
open import Data.Empty using (⊥-elim)
open import Data.Nat using (ℕ; suc)
open import Data.Fin using (Fin; _≟_; punchOut; punchIn)
  renaming (zero to fzero; suc to fsuc)
open import Relation.Binary.PropositionalEquality using (_≢_; refl; sym)
open import Relation.Nullary using (yes; no)
open import Function.Base using (_∘_)

private
  variable
    n : ℕ
    a : Type
    fin : Fin n

-- | Increments the variables that are free relative to the inserted "pivot" variable.
lift : Term n → Fin (suc n) → Term (suc n)
lift (abs ty body) v = abs ty (lift body (fsuc v))
lift (app f x) v = app (lift f v) (lift x v)
lift (var n) v = var (punchIn v n)
lift ⋆ v = ⋆
lift (pair x y) v = pair (lift x v) (lift y v)
lift (projₗ p) v = projₗ (lift p v)
lift (projᵣ p) v = projᵣ (lift p v)

-- | Inserts a binding in the middle of the context.
liftΓ : Ctx n → Fin (suc n) → Type → Ctx (suc n)
liftΓ Γ fzero t = Γ ,- t
liftΓ (Γ ,- A) (fsuc v) t = (liftΓ Γ v t) ,- A

infix 7 _[_≔_]

_[_≔_] : Term (suc n) → Fin (suc n) → Term n → Term n
(abs ty body) [ v ≔ def ] = abs ty (body [ fsuc v ≔ lift def fzero ])
(app f x)     [ v ≔ def ] = app (f [ v ≔ def ]) (x [ v ≔ def ])
(var n)       [ v ≔ def ] with v ≟ n
... | yes refl = def
... | no neq = var (punchOut {i = v} {j = n} λ { refl → neq (sym refl)})
⋆             [ v ≔ def ] = ⋆
(pair x y)    [ v ≔ def ] = pair (x [ v ≔ def ]) (y [ v ≔ def ])
(projₗ p)     [ v ≔ def ] = projₗ (p [ v ≔ def ])
(projᵣ p)     [ v ≔ def ] = projᵣ (p [ v ≔ def ])
