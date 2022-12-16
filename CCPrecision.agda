{- Precision relation of the cast calculus -}

open import Types

module CCPrecision where

open import Data.Nat
open import Data.Product renaming (_,_ to ⟨_,_⟩)
open import Data.Maybe
open import Data.List
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import Syntax
open import Utils
open import Types
open import HeapContext
open import TypeBasedCast
open import CC

{- M ⊑ M′ always implies A ⊑ A′ if ⊢ M ⦂ A and ⊢ M′ ⦂ A′ -}
infix 4 _;_;_;_∣_;_;_;_⊢_⊑_⊢_

data _;_;_;_∣_;_;_;_⊢_⊑_⊢_ : ∀ Γ Σ gc pc Γ′ Σ′ gc′ pc′ {A A′ M M′}
  → Γ  ; Σ  ; gc  ; pc  ⊢ M  ⦂ A
  → Γ′ ; Σ′ ; gc′ ; pc′ ⊢ M′ ⦂ A′
  → A ⊑ A′ → Set where

  ⊑-var : ∀ {Γ Γ′ Σ Σ′ gc gc′ pc pc′} {A A′ x}
    → (Γ∋x  : Γ  ∋ x ⦂ A )
    → (Γ′∋x : Γ′ ∋ x ⦂ A′)
    → (A⊑A′ : A ⊑ A′)
      ----------------------------------------------------------------------
    → Γ ; Σ ; gc ; pc ∣ Γ′ ; Σ′ ; gc′ ; pc′ ⊢ ⊢var Γ∋x ⊑ ⊢var Γ′∋x ⊢ A⊑A′

  ⊑-const : ∀ {Γ Γ′ Σ Σ′ gc gc′ pc pc′} {ι} {k : rep ι} {ℓ}
      ----------------------------------------------------------------------
    → Γ ; Σ ; gc ; pc ∣ Γ′ ; Σ′ ; gc′ ; pc′ ⊢ ⊢const {k = k} ⊑ ⊢const {k = k} ⊢
         ⊑-ty (l⊑l {ℓ}) ⊑-ι

  ⊑-addr : ∀ {Γ Γ′ Σ Σ′ gc gc′ pc pc′} {T T′} {n ℓ ℓ̂}
    → (Σ[a]≡T   : lookup-Σ Σ  (a⟦ ℓ̂ ⟧ n) ≡ just T )
    → (Σ′[a]≡T′ : lookup-Σ Σ′ (a⟦ ℓ̂ ⟧ n) ≡ just T′)
    → (T⊑T′ : T ⊑ᵣ T′)
      ----------------------------------------------------------------------
    → Γ ; Σ ; gc ; pc ∣ Γ′ ; Σ′ ; gc′ ; pc′ ⊢ ⊢addr Σ[a]≡T ⊑ ⊢addr Σ′[a]≡T′ ⊢
         ⊑-ty (l⊑l {ℓ}) (⊑-ref (⊑-ty (l⊑l {ℓ̂}) T⊑T′))

  ⊑-lam : ∀ {Γ Γ′ Σ Σ′ gc gc′ pc pc′} {A A′ B B′ N N′} {ℓᶜ ℓ}
    → (⊢N  : ∀ {pc} → A  ∷ Γ  ; Σ  ; l ℓᶜ ; pc ⊢ N  ⦂ B )
    → (⊢N′ : ∀ {pc} → A′ ∷ Γ′ ; Σ′ ; l ℓᶜ ; pc ⊢ N′ ⦂ B′)
    → (A⊑A′ : A ⊑ A′)
    → (B⊑B′ : B ⊑ B′)
    → A ∷ Γ ; Σ ; l ℓᶜ ; pc ∣ A′ ∷ Γ′ ; Σ′ ; l ℓᶜ ; pc′ ⊢ ⊢N ⊑ ⊢N′ ⊢ B⊑B′
      ----------------------------------------------------------------------
    → Γ ; Σ ; gc ; pc ∣ Γ′ ; Σ′ ; gc′ ; pc′ ⊢ ⊢lam ⊢N ⊑ ⊢lam ⊢N′ ⊢
         ⊑-ty (l⊑l {ℓ}) (⊑-fun (l⊑l {ℓᶜ}) A⊑A′ B⊑B′)

  ⊑-app : ∀ {Γ Γ′ Σ Σ′ gc gc′ pc pc′} {A A′ B B′ L L′ M M′} {g g′}
    → (⊢L : Γ ; Σ ; gc ; pc ⊢ L ⦂ ⟦ gc ⋎̃ g ⟧ A ⇒ B of g)
    → (⊢M : Γ ; Σ ; gc ; pc ⊢ M ⦂ A)
    → (⊢L′ : Γ′ ; Σ′ ; gc′ ; pc′ ⊢ L′ ⦂ ⟦ gc′ ⋎̃ g′ ⟧ A′ ⇒ B′ of g′)
    → (⊢M′ : Γ′ ; Σ′ ; gc′ ; pc′ ⊢ M′ ⦂ A′)
    → (gc⊑gc′ : gc ⊑ₗ gc′) → (g⊑g′ : g ⊑ₗ g′) → (A⊑A′ : A ⊑ A′) → (B⊑B′ : B ⊑ B′)
    → Γ ; Σ ; gc ; pc ∣ Γ′ ; Σ′ ; gc′ ; pc′ ⊢ ⊢L ⊑ ⊢L′ ⊢
         ⊑-ty g⊑g′ (⊑-fun (consis-join-⊑ₗ gc⊑gc′ g⊑g′) A⊑A′ B⊑B′)
    → Γ ; Σ ; gc ; pc ∣ Γ′ ; Σ′ ; gc′ ; pc′ ⊢ ⊢M ⊑ ⊢M′ ⊢ A⊑A′
      -----------------------------------------------------------------------------
    → Γ ; Σ ; gc ; pc ∣ Γ′ ; Σ′ ; gc′ ; pc′ ⊢ ⊢app ⊢L ⊢M ⊑ ⊢app ⊢L′ ⊢M′ ⊢
         stamp-⊑ B⊑B′ g⊑g′

  ⊑-if : ∀ {Γ Γ′ Σ Σ′ gc gc′ pc pc′} {A A′ L L′ M M′ N N′} {g g′}
    → (⊢L : Γ ; Σ ; gc ; pc ⊢ L ⦂ ` Bool of g)
    → (⊢M : ∀ {pc} → Γ ; Σ ; gc ⋎̃ g ; pc ⊢ M ⦂ A)
    → (⊢N : ∀ {pc} → Γ ; Σ ; gc ⋎̃ g ; pc ⊢ N ⦂ A)
    → (⊢L′ : Γ′ ; Σ′ ; gc′ ; pc′ ⊢ L′ ⦂ ` Bool of g′)
    → (⊢M′ : ∀ {pc} → Γ′ ; Σ′ ; gc′ ⋎̃ g′ ; pc ⊢ M′ ⦂ A′)
    → (⊢N′ : ∀ {pc} → Γ′ ; Σ′ ; gc′ ⋎̃ g′ ; pc ⊢ N′ ⦂ A′)
    → (g⊑g′ : g ⊑ₗ g′) → (A⊑A′ : A ⊑ A′)
    → Γ ; Σ ; gc ; pc ∣ Γ′ ; Σ′ ; gc′ ; pc′ ⊢ ⊢L ⊑ ⊢L′ ⊢ ⊑-ty g⊑g′ ⊑-ι
    → Γ ; Σ ; gc ⋎̃ g ; pc ∣ Γ′ ; Σ′ ; gc′ ⋎̃ g′ ; pc′ ⊢ ⊢M ⊑ ⊢M′ ⊢ A⊑A′
    → Γ ; Σ ; gc ⋎̃ g ; pc ∣ Γ′ ; Σ′ ; gc′ ⋎̃ g′ ; pc′ ⊢ ⊢N ⊑ ⊢N′ ⊢ A⊑A′
      ------------------------------------------------------------------------------
    → Γ ; Σ ; gc ; pc ∣ Γ′ ; Σ′ ; gc′ ; pc′ ⊢ ⊢if ⊢L ⊢M ⊢N ⊑ ⊢if ⊢L′ ⊢M′ ⊢N′ ⊢
         stamp-⊑ A⊑A′ g⊑g′

  ⊑-let : ∀ {Γ Γ′ Σ Σ′ gc gc′ pc pc′} {A A′ B B′ M M′ N N′}
    → (⊢M : Γ ; Σ ; gc ; pc ⊢ M ⦂ A)
    → (⊢N : ∀ {pc} → A ∷ Γ ; Σ ; gc ; pc ⊢ N ⦂ B)
    → (⊢M′ : Γ′ ; Σ′ ; gc′ ; pc′ ⊢ M′ ⦂ A′)
    → (⊢N′ : ∀ {pc} → A′ ∷ Γ′ ; Σ′ ; gc′ ; pc ⊢ N′ ⦂ B′)
    → (A⊑A′ : A ⊑ A′) → (B⊑B′ : B ⊑ B′)
    → Γ ; Σ ; gc ; pc ∣ Γ′ ; Σ′ ; gc′ ; pc′ ⊢ ⊢M ⊑ ⊢M′ ⊢ A⊑A′
    → A ∷ Γ ; Σ ; gc ; pc ∣ A′ ∷ Γ′ ; Σ′ ; gc′ ; pc′ ⊢ ⊢N ⊑ ⊢N′ ⊢ B⊑B′
      -----------------------------------------------------------------------
    → Γ ; Σ ; gc ; pc ∣ Γ′ ; Σ′ ; gc′ ; pc′ ⊢ ⊢let ⊢M ⊢N ⊑ ⊢let ⊢M′ ⊢N′ ⊢ B⊑B′

  ⊑-castl : ∀ {Γ Γ′ Σ Σ′ gc gc′ pc pc′} {A A′ B M M′} {c : Cast A ⇒ B}
    → (⊢M : Γ ; Σ ; gc ; pc ⊢ M ⦂ A)
    → (⊢M′ : Γ′ ; Σ′ ; gc′ ; pc′ ⊢ M′ ⦂ A′)
    → (A⊑A′ : A ⊑ A′) → (B⊑A′ : B ⊑ A′)
    → Γ ; Σ ; gc ; pc ∣ Γ′ ; Σ′ ; gc′ ; pc′ ⊢ ⊢M ⊑ ⊢M′ ⊢ A⊑A′
      --------------------------------------------------------------------------
    → Γ ; Σ ; gc ; pc ∣ Γ′ ; Σ′ ; gc′ ; pc′ ⊢ ⊢cast {c = c} ⊢M ⊑ ⊢M′ ⊢ B⊑A′

  ⊑-castr : ∀ {Γ Γ′ Σ Σ′ gc gc′ pc pc′} {A A′ B′ M M′} {c′ : Cast A′ ⇒ B′}
    → (⊢M : Γ ; Σ ; gc ; pc ⊢ M ⦂ A)
    → (⊢M′ : Γ′ ; Σ′ ; gc′ ; pc′ ⊢ M′ ⦂ A′)
    → (A⊑A′ : A ⊑ A′) → (A⊑B′ : A ⊑ B′)
    → Γ ; Σ ; gc ; pc ∣ Γ′ ; Σ′ ; gc′ ; pc′ ⊢ ⊢M ⊑ ⊢M′ ⊢ A⊑A′
      --------------------------------------------------------------------------
    → Γ ; Σ ; gc ; pc ∣ Γ′ ; Σ′ ; gc′ ; pc′ ⊢ ⊢M ⊑ ⊢cast {c = c′} ⊢M′ ⊢ A⊑B′
