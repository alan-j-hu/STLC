{-# OPTIONS --safe --sized-types #-}
module STLC.Operational.Base where

open import STLC.Syntax
open import Data.Nat using (ℕ; suc)
open import Data.Fin using (Fin; _≟_; punchOut) renaming (suc to fsuc)
open import Data.Fin.Properties renaming (<-cmp to fin-cmp)
open import Relation.Binary.Definitions using (tri<; tri≈; tri>)
open import Relation.Binary.PropositionalEquality using (refl)

private
  variable
    n : ℕ
    a : Type
    fin : Fin n

rename : Term n → Term (suc n)
rename (abs ty body) = abs ty (rename body)
rename (app f x) = app (rename f) (rename x)
rename (var n) = var (fsuc n)
rename ⋆ = ⋆
rename (pair x y) = pair (rename x) (rename y)
rename (projₗ p) = projₗ (rename p)
rename (projᵣ p) = projᵣ (rename p)

infix 7 _[_≔_]

_[_≔_] : Term (suc n) → Fin (suc n) → Term n → Term n
(abs ty body) [ v ≔ def ] = abs ty (body [ fsuc v ≔ rename def ])
(app f x)     [ v ≔ def ] = app (f [ v ≔ def ]) (x [ v ≔ def ])
(var n)       [ v ≔ def ] with fin-cmp n v
... | tri< _ neq _ = var (punchOut neq)
... | tri≈ _ refl _ = def
... | tri> _ neq _ = var (punchOut neq)
⋆             [ v ≔ def ] = ⋆
(pair x y)    [ v ≔ def ] = pair (x [ v ≔ def ]) (y [ v ≔ def ])
(projₗ p)     [ v ≔ def ] = projₗ (p [ v ≔ def ])
(projᵣ p)     [ v ≔ def ] = projᵣ (p [ v ≔ def ])
