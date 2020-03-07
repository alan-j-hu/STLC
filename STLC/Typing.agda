{-# OPTIONS --safe #-}
module STLC.Typing where

open import STLC.Syntax
open import Data.Nat using (ℕ)
open import Data.Fin using (Fin)
open import Data.Product using (Σ-syntax; _,_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; subst)
open import Relation.Nullary using (Dec; yes; no; ¬_)

private
  variable
    n : ℕ
    v : Fin n
    Γ : Ctx n
    A B : Type
    a b f x p : Term n

data _⊢_∈_ : Ctx n → Term n → Type → Set where
  ty-abs : (Γ ,- A) ⊢ b ∈ B → Γ ⊢ abs A b ∈ (A ⇒ B)
  ty-app : Γ ⊢ f ∈ (A ⇒ B) → Γ ⊢ x ∈ A → Γ ⊢ app f x ∈ B
  ty-var : Γ ⊢ var v ∈ find Γ v
  ty-⋆ : Γ ⊢ ⋆ ∈ unit
  ty-pair : Γ ⊢ a ∈ A → Γ ⊢ b ∈ B → Γ ⊢ pair a b ∈ (A ×' B)
  ty-projₗ : Γ ⊢ p ∈ (A ×' B) → Γ ⊢ projₗ p ∈ A
  ty-projᵣ : Γ ⊢ p ∈ (A ×' B) → Γ ⊢ projᵣ p ∈ B

principal : Γ ⊢ x ∈ A → Γ ⊢ x ∈ B → A ≡ B
principal (ty-abs {A = A} body₁) (ty-abs {A = (.A)} body₂) =
  cong (λ B → A ⇒ B) (principal body₁ body₂)
principal (ty-app f x) (ty-app g y) with principal f g
... | refl = refl
principal ty-var ty-var = refl
principal ty-⋆ ty-⋆ = refl
principal (ty-pair a₁ b₁) (ty-pair a₂ b₂) rewrite principal a₁ a₂ | principal b₁ b₂ = refl
principal (ty-projₗ p₁) (ty-projₗ p₂) with principal p₁ p₂
... | refl = refl
principal (ty-projᵣ p₁) (ty-projᵣ p₂) with principal p₁ p₂
... | refl = refl

ill-typed-fun
  : (Γ ⊢ f ∈ A)
  → ¬ (Σ[ B ∈ Type ] Σ[ C ∈ Type ] (A ≡ (B ⇒ C)))
  → ¬ (Σ[ T ∈ Type ] (Γ ⊢ app f x ∈ T))
ill-typed-fun f-ill-typed ineq (_ , ty-app {A = A} {B = B} f-typing _)
  with principal f-ill-typed f-typing
... | eq = ineq (A , B , eq)

ill-typed-pairₗ
  : (Γ ⊢ p ∈ A)
  → ¬ (Σ[ B ∈ Type ] Σ[ C ∈ Type ] (A ≡ (B ×' C)))
  → ¬ (Σ[ T ∈ Type ] (Γ ⊢ projₗ p ∈ T))
ill-typed-pairₗ pair-ill-typed ineq (_ , ty-projₗ {A = A} {B = B} pair-typing)
  with principal pair-ill-typed pair-typing
... | eq = ineq (A , B , eq)

ill-typed-pairᵣ
  : (Γ ⊢ p ∈ A)
  → ¬ (Σ[ B ∈ Type ] Σ[ C ∈ Type ] (A ≡ (B ×' C)))
  → ¬ (Σ[ T ∈ Type ] (Γ ⊢ projᵣ p ∈ T))
ill-typed-pairᵣ pair-ill-typed ineq (_ , ty-projᵣ {A = A} {B = B} pair-typing)
  with principal pair-ill-typed pair-typing
... | eq = ineq (A , B , eq)

typecheck : (Γ : Ctx n) → (t : Term n) → Dec (Σ[ T ∈ Type ] (Γ ⊢ t ∈ T))
typecheck Γ (var v) = yes (find Γ v , ty-var)
typecheck Γ (abs A t) with typecheck (Γ ,- A) t
... | yes (B , well-typed) = yes (A ⇒ B , ty-abs well-typed)
... | no ill-typed = no λ { (ty , ty-abs {B = B} ty-body) → ill-typed ((B , ty-body)) }
typecheck Γ (app f x) with typecheck Γ f | typecheck Γ x
... | yes (_ ×' _ , f-wrong-typing) | _ = no (ill-typed-fun f-wrong-typing λ ())
... | yes (unit , f-wrong-typing) | _ = no (ill-typed-fun f-wrong-typing λ ())
... | yes (_ ⇒ _ , _) | no ill-typed =
        no λ { (_ , ty-app {A = A} _ x) → ill-typed (A , x)}
... | no ill-typed | _ =
        no λ { (_ , ty-app {A = A} {B = B} f _) → ill-typed (A ⇒ B , f)}
... | yes (A ⇒ B , f-typing) | yes (A' , x-typing) with A' =?= A
...     | yes eq = yes (B , ty-app f-typing (subst (λ A → Γ ⊢ x ∈ A) eq x-typing))
...     | no neq = no (helper neq)
  where helper : ¬ A' ≡ A → ¬ (Σ[ B ∈ Type ] (Γ ⊢ app f x ∈ B))
        helper neq (B'' , ty-app {A = A''} f'' x'')
          with principal f-typing f'' | principal x-typing x''
        ... | refl | refl = neq refl
typecheck _ ⋆ = yes (unit , ty-⋆)
typecheck Γ (pair l r) with typecheck Γ l | typecheck Γ r
... | yes (A , l-typing) | yes (B , r-typing) = yes (A ×' B , ty-pair l-typing r-typing)
... | yes _ | no ill-typed = no λ { (A ×' B , ty-pair _ r) → ill-typed (B , r) }
... | no ill-typed | _ = no λ { (A ×' B , ty-pair l _) → ill-typed (A , l)}
typecheck Γ (projₗ p) with typecheck Γ p
... | yes (A ×' _ , typing) = yes ((A , ty-projₗ typing))
... | yes (_ ⇒ _ , typing) = no (ill-typed-pairₗ typing λ ())
... | yes (unit , typing) = no (ill-typed-pairₗ typing λ ())
... | no ill-typed = no λ { (_ , ty-projₗ {A = A} {B = B} p) → ill-typed ((A ×' B) , p) }
typecheck Γ (projᵣ p) with typecheck Γ p
... | yes (_ ×' B , typing) = yes ((B , ty-projᵣ typing))
... | yes (_ ⇒ _ , typing) = no (ill-typed-pairᵣ typing λ ())
... | yes (unit , typing) = no (ill-typed-pairᵣ typing λ ())
... | no ill-typed = no λ { (_ , ty-projᵣ {A = A} {B = B} p) → ill-typed ((A ×' B) , p) }
