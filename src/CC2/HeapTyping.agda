{- Well-typedness of the heap -}

module CC2.HeapTyping where

open import Data.Nat
open import Data.Nat.Properties using (n≮n; <-trans; n<1+n; ≤-refl)
open import Data.List
open import Data.Product renaming (_,_ to ⟨_,_⟩)
open import Data.Maybe
open import Relation.Nullary using (¬_; Dec; yes; no)
open import Relation.Nullary.Negation using (contradiction)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; trans; sym; subst; cong)
open import Function using (case_of_)

open import Common.Utils
open import Common.Types
open import CC2.Statics
open import Memory.HeapTyping Term Value _;_;_;_⊢_⇐_ public


relax-Σ : ∀ {Γ Σ Σ′ gc pc M A}
    → Γ ; Σ ; gc ; pc ⊢ M ⇐ A
    → Σ′ ⊇ Σ
      -----------------------------------
    → Γ ; Σ′ ; gc ; pc ⊢ M ⇐ A
relax-Σ ⊢const Σ′⊇Σ = ⊢const
relax-Σ (⊢addr {n = n} {ℓ̂ = ℓ̂} eq) Σ′⊇Σ = ⊢addr (Σ′⊇Σ (a⟦ ℓ̂ ⟧ n) eq)
relax-Σ (⊢var Γ∋x) Σ′⊇Σ = ⊢var Γ∋x
relax-Σ (⊢lam ⊢M) Σ′⊇Σ = ⊢lam (relax-Σ ⊢M Σ′⊇Σ)
relax-Σ (⊢app ⊢L ⊢M eq) Σ′⊇Σ = ⊢app (relax-Σ ⊢L Σ′⊇Σ) (relax-Σ ⊢M Σ′⊇Σ) eq
relax-Σ (⊢app⋆ ⊢L ⊢M) Σ′⊇Σ = ⊢app⋆ (relax-Σ ⊢L Σ′⊇Σ) (relax-Σ ⊢M Σ′⊇Σ)
relax-Σ (⊢if ⊢L ⊢M ⊢N eq) Σ′⊇Σ = ⊢if (relax-Σ ⊢L Σ′⊇Σ) (relax-Σ ⊢M Σ′⊇Σ) (relax-Σ ⊢N Σ′⊇Σ) eq
relax-Σ (⊢if⋆ ⊢L ⊢M ⊢N) Σ′⊇Σ = ⊢if⋆ (relax-Σ ⊢L Σ′⊇Σ) (relax-Σ ⊢M Σ′⊇Σ) (relax-Σ ⊢N Σ′⊇Σ)
relax-Σ (⊢let ⊢M ⊢N) Σ′⊇Σ = ⊢let (relax-Σ ⊢M Σ′⊇Σ) (relax-Σ ⊢N Σ′⊇Σ)
relax-Σ (⊢ref ⊢M x) Σ′⊇Σ = ⊢ref (relax-Σ ⊢M Σ′⊇Σ) x
relax-Σ (⊢ref? ⊢M) Σ′⊇Σ = ⊢ref? (relax-Σ ⊢M Σ′⊇Σ)
relax-Σ (⊢deref ⊢M eq) Σ′⊇Σ = ⊢deref (relax-Σ ⊢M Σ′⊇Σ) eq
relax-Σ (⊢deref⋆ ⊢M) Σ′⊇Σ = ⊢deref⋆ (relax-Σ ⊢M Σ′⊇Σ)
relax-Σ (⊢assign ⊢L ⊢M x y) Σ′⊇Σ = ⊢assign (relax-Σ ⊢L Σ′⊇Σ) (relax-Σ ⊢M Σ′⊇Σ) x y
relax-Σ (⊢assign? ⊢L ⊢M) Σ′⊇Σ = ⊢assign? (relax-Σ ⊢L Σ′⊇Σ) (relax-Σ ⊢M Σ′⊇Σ)
relax-Σ (⊢prot ⊢M ⊢PC x eq) Σ′⊇Σ = ⊢prot (relax-Σ ⊢M Σ′⊇Σ) ⊢PC x eq
relax-Σ (⊢cast ⊢M) Σ′⊇Σ = ⊢cast (relax-Σ ⊢M Σ′⊇Σ)
relax-Σ ⊢blame Σ′⊇Σ = ⊢blame


⊇-fresh : ∀ {Σ μ} a T → Σ ⊢ μ → a FreshIn μ → cons-Σ a T Σ ⊇ Σ
⊇-fresh {Σ} {⟨ μᴸ , μᴴ ⟩} (a⟦ high ⟧ n₁) T ⊢μ fresh (a⟦ high ⟧ n) eq
  with n ≟ n₁
... | yes refl =
  case ⊢μ n high eq of λ where
  ⟨ wfᴴ n<len , _ ⟩ →
    let len<len = subst (λ □ → □ < length μᴴ) fresh n<len in
    contradiction len<len (n≮n _)
... | no _ = eq
⊇-fresh {Σ} {μ} (a⟦ high ⟧ n₁) T ⊢μ fresh (a⟦ low ⟧ n) eq = eq
⊇-fresh {Σ} {⟨ μᴸ , μᴴ ⟩} (a⟦ low ⟧ n₁) T ⊢μ fresh (a⟦ low ⟧ n) eq
  with n ≟ n₁
... | yes refl =
  case ⊢μ n low eq of λ where
  ⟨ wfᴸ n<len , _ ⟩ →
    let len<len = subst (λ □ → □ < length μᴸ) fresh n<len in
    contradiction len<len (n≮n _)
... | no _ = eq
⊇-fresh {Σ} {μ} (a⟦ low ⟧ n₁) T ⊢μ fresh (a⟦ high ⟧ n) eq = eq


{- Properties about Σ ⊢ μ : -}
⊢μ-nil : ∅ ⊢ ∅
⊢μ-nil n low  ()
⊢μ-nil n high ()

⊢μ-new : ∀ {Σ V n T ℓ μ}
  → [] ; Σ ; l low ; low ⊢ V ⇐ T of l ℓ
  → (v : Value V)
  → Σ ⊢ μ
  → a⟦ ℓ ⟧ n FreshIn μ
    -----------------------------------------------
  → cons-Σ (a⟦ ℓ ⟧ n) T Σ ⊢ cons-μ (a⟦ ℓ ⟧ n) V v μ
⊢μ-new {⟨ Σᴸ , Σᴴ ⟩} {V₁} {n₁} {T₁} {low} {μ} ⊢V₁ v₁ ⊢μ refl n low {T} eq with n ≟ n₁
... | yes refl =
  case eq of λ where
  refl → ⟨ wfᴸ ≤-refl , V₁ , v₁ , refl , relax-Σ ⊢V₁ (⊇-fresh (a⟦ low ⟧ n₁) T ⊢μ refl) ⟩
... | no  _    =
  let ⟨ wf , V , v , eq′ , ⊢V ⟩ = ⊢μ n low eq in
  ⟨ wf-relaxᴸ V₁ v₁ wf , V , v , eq′ , relax-Σ ⊢V (⊇-fresh (a⟦ low ⟧ n₁) T₁ ⊢μ refl) ⟩
⊢μ-new {Σ} {V₁} {n₁} {T₁} {low} {μ} ⊢V₁ v₁ ⊢μ refl n high {T} eq =
  case ⊢μ n high eq of λ where
  ⟨ wfᴴ n<len , V , v , eq′ , ⊢V ⟩ →
    ⟨ wfᴴ n<len , V , v , eq′ , relax-Σ ⊢V (⊇-fresh (a⟦ low ⟧ n₁) T₁ ⊢μ refl) ⟩
⊢μ-new {⟨ Σᴸ , Σᴴ ⟩} {V₁} {n₁} {T₁} {high} {μ} ⊢V₁ v₁ ⊢μ refl n high {T} eq with n ≟ n₁
... | yes refl =
  case eq of λ where
  refl → ⟨ wfᴴ ≤-refl , V₁ , v₁ , refl , relax-Σ ⊢V₁ (⊇-fresh (a⟦ high ⟧ n₁) T ⊢μ refl) ⟩
... | no  _    =
  let ⟨ wf , V , v , eq′ , ⊢V ⟩ = ⊢μ n high eq in
  ⟨ wf-relaxᴴ V₁ v₁ wf , V , v , eq′ , relax-Σ ⊢V (⊇-fresh (a⟦ high ⟧ n₁) T₁ ⊢μ refl) ⟩
⊢μ-new {Σ} {V₁} {n₁} {T₁} {high} {μ} ⊢V₁ v₁ ⊢μ refl n low {T} eq =
  case ⊢μ n low eq of λ where
  ⟨ wfᴸ n<len , V , v , eq′ , ⊢V ⟩ →
    ⟨ wfᴸ n<len , V , v , eq′ , relax-Σ ⊢V (⊇-fresh (a⟦ high ⟧ n₁) T₁ ⊢μ refl) ⟩

⊢μ-update : ∀ {Σ V n T ℓ μ}
  → [] ; Σ ; l low ; low ⊢ V ⇐ T of l ℓ
  → (v : Value V)
  → Σ ⊢ μ
  → lookup-Σ Σ (a⟦ ℓ ⟧ n) ≡ just T  {- updating a -}
    -----------------------------------------------
  → Σ ⊢ cons-μ (a⟦ ℓ ⟧ n) V v μ
⊢μ-update {Σ} {V₁} {n₁} {T₁} {low} {μ} ⊢V₁ v₁ ⊢μ eq₁ n low eq with n ≟ n₁
... | yes refl =
  case trans (sym eq) eq₁ of λ where
    refl →
      let ⟨ wf , _ ⟩ = ⊢μ n₁ low eq₁ in
      ⟨ wf-relaxᴸ V₁ v₁ wf , V₁ , v₁ , refl , ⊢V₁ ⟩
... | no  _ =
  case ⊢μ n low eq of λ where
  ⟨ wf , rest ⟩ → ⟨ wf-relaxᴸ V₁ v₁ wf , rest ⟩
⊢μ-update {Σ} {V₁} {n₁} {T₁} {low} {μ} ⊢V₁ v₁ ⊢μ eq₁ n high eq =
  case ⊢μ n high eq of λ where
  ⟨ wfᴴ n<len , rest ⟩ → ⟨ wfᴴ n<len , rest ⟩
⊢μ-update {Σ} {V₁} {n₁} {T₁} {high} {μ} ⊢V₁ v₁ ⊢μ eq₁ n high eq with n ≟ n₁
... | yes refl =
  case trans (sym eq) eq₁ of λ where
    refl →
      let ⟨ wf , _ ⟩ = ⊢μ n₁ high eq₁ in
      ⟨ wf-relaxᴴ V₁ v₁ wf , V₁ , v₁ , refl , ⊢V₁ ⟩
... | no  _ =
  case ⊢μ n high eq of λ where
  ⟨ wf , rest ⟩ → ⟨ wf-relaxᴴ V₁ v₁ wf , rest ⟩
⊢μ-update {Σ} {V₁} {n₁} {T₁} {high} {μ} ⊢V₁ v₁ ⊢μ eq₁ n low eq =
  case ⊢μ n low eq of λ where
  ⟨ wfᴸ n<len , rest ⟩ → ⟨ wfᴸ n<len , rest ⟩
