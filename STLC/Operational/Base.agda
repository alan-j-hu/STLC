{-# OPTIONS --safe --sized-types #-}
module STLC.Operational.Base where

open import STLC.Syntax
open import Data.Nat using (ℕ; suc)
open import Data.Fin using (Fin; _≟_; punchOut; punchIn) renaming (suc to fsuc)
open import Data.Fin.Properties using (<-cmp)
open import Relation.Binary.Definitions using (tri<; tri≈; tri>)
open import Relation.Binary.PropositionalEquality using (refl)

private
  variable
    n : ℕ
    a : Type
    fin : Fin n

lift : Term n → Fin (suc n) → Term (suc n)
lift (abs ty body) v = abs ty (lift body (fsuc v))
lift (app f x) v = app (lift f v) (lift x v)
lift (var n) v = var (punchIn v n)
lift ⋆ v = ⋆
lift (pair x y) v = pair (lift x v) (lift y v)
lift (projₗ p) v = projₗ (lift p v)
lift (projᵣ p) v = projᵣ (lift p v)

infix 7 _[_≔_]

_[_≔_] : Term (suc n) → Fin (suc n) → Term n → Term n
(abs ty body) [ v ≔ def ] = abs ty (body [ fsuc v ≔ lift def v ])
(app f x)     [ v ≔ def ] = app (f [ v ≔ def ]) (x [ v ≔ def ])
(var n)       [ v ≔ def ] with <-cmp n v
... | tri< _ neq _ = var (punchOut neq)
... | tri≈ _ refl _ = def
... | tri> _ neq _ = var (punchOut neq)
⋆             [ v ≔ def ] = ⋆
(pair x y)    [ v ≔ def ] = pair (x [ v ≔ def ]) (y [ v ≔ def ])
(projₗ p)     [ v ≔ def ] = projₗ (p [ v ≔ def ])
(projᵣ p)     [ v ≔ def ] = projᵣ (p [ v ≔ def ])
