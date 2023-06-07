{- Syntactical composition of coercion expressions -}

module LabelCoercionCalculus.SyntacComp where

open import Data.Nat
open import Data.Unit using (⊤; tt)
open import Data.Bool using (true; false) renaming (Bool to 𝔹)
open import Data.List hiding ([_])
open import Data.Product renaming (_,_ to ⟨_,_⟩)
open import Data.Sum using (_⊎_)
open import Data.Maybe
open import Relation.Nullary using (¬_; Dec; yes; no)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Function using (case_of_)

open import Common.Utils
open import Common.SecurityLabels
open import Common.BlameLabels
open import LabelCoercionCalculus.CoercionExp
open import LabelCoercionCalculus.Precision


_⨟_ : ∀ {g₁ g₂ g₃} (c̅₁ : CoercionExp g₁ ⇒ g₂) (c̅₂ : CoercionExp g₂ ⇒ g₃) → CoercionExp g₁ ⇒ g₃
c̅₁ ⨟ ⊥ g₂ g₃ p = ⊥ _ g₃ p
c̅₁ ⨟ id g      = c̅₁ ⨾ id g
c̅₁ ⨟ (c̅₂ ⨾ c)  = (c̅₁ ⨟ c̅₂) ⨾ c


comp-pres-prec : ∀ {g₁ g₁′ g₂ g₂′ g₃ g₃′}
     {c̅₁ : CoercionExp g₁ ⇒ g₂}    {c̅₂ : CoercionExp g₂ ⇒ g₃}
     {c̅₁′ : CoercionExp g₁′ ⇒ g₂′} {c̅₂′ : CoercionExp g₂′ ⇒ g₃′}
  → ⊢ c̅₁ ⊑ c̅₁′
  → ⊢ c̅₂ ⊑ c̅₂′
    -----------------------------
  → ⊢ c̅₁ ⨟ c̅₂ ⊑ c̅₁′ ⨟ c̅₂′
comp-pres-prec c̅₁⊑c̅₁′ (⊑-⊥ x g₃⊑g₃′) =
  let ⟨ g₁⊑g₁′ , _ ⟩ = prec→⊑ _ _ c̅₁⊑c̅₁′ in
  ⊑-⊥ g₁⊑g₁′ g₃⊑g₃′
comp-pres-prec c̅₁⊑c̅₁′ (⊑-id g⊑g′) = ⊑-cast c̅₁⊑c̅₁′ g⊑g′ g⊑g′
comp-pres-prec c̅₁⊑c̅₁′ (⊑-cast c̅₂⊑c̅₂′ g⊑g₃ g′⊑g₃′) =
  ⊑-cast (comp-pres-prec c̅₁⊑c̅₁′ c̅₂⊑c̅₂′) g⊑g₃ g′⊑g₃′
comp-pres-prec c̅₁⊑c̅₁′ (⊑-castl c̅₂⊑c̅₂′ g⊑g₃′ g₃⊑g₃′) =
  ⊑-castl (comp-pres-prec c̅₁⊑c̅₁′ c̅₂⊑c̅₂′) g⊑g₃′ g₃⊑g₃′
comp-pres-prec c̅₁⊑c̅₁′ (⊑-castr c̅₂⊑c̅₂′ g₃⊑g′ g₃⊑g₃′) =
  ⊑-castr (comp-pres-prec c̅₁⊑c̅₁′ c̅₂⊑c̅₂′) g₃⊑g′ g₃⊑g₃′


comp-pres-⊑-ll : ∀ {g₁ g₂ g₃ g′}
     {c̅₁ : CoercionExp g₁ ⇒ g₂}    {c̅₂ : CoercionExp g₂ ⇒ g₃}
  → ⊢l c̅₁ ⊑ g′
  → ⊢l c̅₂ ⊑ g′
    -----------------------------
  → ⊢l c̅₁ ⨟ c̅₂ ⊑ g′
comp-pres-⊑-ll c̅₁⊑c̅₁′ (⊑-id g⊑g′) = ⊑-cast c̅₁⊑c̅₁′ g⊑g′ g⊑g′
comp-pres-⊑-ll c̅₁⊑c̅₁′ (⊑-cast c̅₂⊑c̅₂′ g⊑g₃′ g₃⊑g₃′) =
  ⊑-cast (comp-pres-⊑-ll c̅₁⊑c̅₁′ c̅₂⊑c̅₂′) g⊑g₃′ g₃⊑g₃′

comp-pres-⊑-l : ∀ {g₁ g₁′ g₂ g₂′ g₃}
     {c̅₁ : CoercionExp g₁ ⇒ g₂}    {c̅₂ : CoercionExp g₂ ⇒ g₃}
     {c̅′ : CoercionExp g₁′ ⇒ g₂′}
  → ⊢l c̅₁ ⊑ g₁′
  → ⊢  c̅₂ ⊑ c̅′
    -----------------------------
  → ⊢ c̅₁ ⨟ c̅₂ ⊑ c̅′
comp-pres-⊑-l c̅₁⊑g₁ (⊑-id g⊑g′) = ⊑-castl (⊑-left-expand c̅₁⊑g₁) g⊑g′ g⊑g′
comp-pres-⊑-l c̅₁⊑g₁ (⊑-cast c̅⊑c̅′ g₁⊑g₁′ g₂⊑g₂′) = ⊑-cast (comp-pres-⊑-l c̅₁⊑g₁ c̅⊑c̅′) g₁⊑g₁′ g₂⊑g₂′
comp-pres-⊑-l c̅₁⊑g₁ (⊑-castl c̅⊑c̅′ g₁⊑g′ g₂⊑g′) = ⊑-castl (comp-pres-⊑-l c̅₁⊑g₁ c̅⊑c̅′) g₁⊑g′ g₂⊑g′
comp-pres-⊑-l c̅₁⊑g₁ (⊑-castr c̅⊑c̅′ g⊑g₁′ g⊑g₂′) = ⊑-castr (comp-pres-⊑-l c̅₁⊑g₁ c̅⊑c̅′) g⊑g₁′ g⊑g₂′
comp-pres-⊑-l c̅₁⊑g₁ (⊑-⊥ g₁⊑g₁′ g₂⊑g₂′) = ⊑-⊥ (proj₁ (prec-left→⊑ _ c̅₁⊑g₁)) g₂⊑g₂′
