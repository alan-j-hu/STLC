module STLC.Syntax where

open import Data.Nat using (ℕ; suc)
open import Data.Fin using (Fin) renaming (zero to fzero; suc to fsuc)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Relation.Nullary using (Dec; yes; no)

private
  variable
    n : ℕ

data Type : Set where
  `_⇒_ : Type → Type → Type
  `_×_ : Type → Type → Type
  `unit : Type

data Term : ℕ → Set where
  abs : Type → Term (suc n) → Term n
  app : Term n → Term n → Term n
  var : Fin n → Term n
  ⋆ : Term n
  pair : Term n → Term n → Term n
  projₗ : Term n → Term n
  projᵣ : Term n → Term n

data Ctx : ℕ → Set where
  `● : Ctx 0
  `_,_ : Ctx n → Type → Ctx (suc n)

find : Ctx n → Fin n → Type
find (` Γ , A) fzero = A
find (` Γ , A) (fsuc n) = find Γ n

_=?=_ : (x : Type) → (y : Type) → Dec (x ≡ y)
`unit     =?= `unit       = yes refl
(` a ⇒ b) =?= (` c ⇒ d) with a =?= c | b =?= d
... | yes refl | yes refl = yes refl
... | yes refl | no ne    = no λ { refl → ne refl }
... | no ne    | _        = no λ { refl → ne refl }
(` a × b) =?= (` c × d) with a =?= c | b =?= d
... | yes refl | yes refl = yes refl
... | yes refl | no ne    = no λ { refl → ne refl }
... | no ne    | _        = no λ { refl → ne refl }
`unit     =?= (` _ × _)   = no λ ()
`unit     =?= (` _ ⇒ _)   = no λ ()
(` _ × _) =?= `unit       = no λ ()
(` _ × _) =?= (` _ ⇒ _)   = no λ ()
(` _ ⇒ _) =?= `unit       = no λ ()
(` _ ⇒ _) =?= (` _ × _)   = no λ ()
