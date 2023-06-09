module LabelCoercionCalculus.LCCSim where

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
open import LabelCoercionCalculus.LabelCC

open import LabelCoercionCalculus.SyntacComp
open import LabelCoercionCalculus.GG renaming (catchup to catchupₗ)
open import LabelCoercionCalculus.LCCCatchUp


sim : ∀ {g g′} {M M′ N′} {g⊑g′ : g ⊑ₗ g′}
  → ⊢ M ⊑ M′ ⇐ g⊑g′
  → M′ —→ₑ N′
    ---------------------------------------------
  → ∃[ N ] (M —↠ₑ N) × (⊢ N ⊑ N′ ⇐ g⊑g′)


sim-cast : ∀ {g₁ g₁′ g₂ g₂′} {M M′ N′} {g₁⊑g₁′ : g₁ ⊑ₗ g₁′} {g₂⊑g₂′ : g₂ ⊑ₗ g₂′}
             {c̅ : CoercionExp g₁ ⇒ g₂} {c̅′ : CoercionExp g₁′ ⇒ g₂′}
  → ⊢ M ⊑ M′ ⇐ g₁⊑g₁′
  → ⊢ c̅ ⊑ c̅′
  → M′ ⟪ c̅′ ⟫ —→ₑ N′
    ---------------------------------------------------
  → ∃[ N ] (M ⟪ c̅ ⟫ —↠ₑ N) × (⊢ N ⊑ N′ ⇐ g₂⊑g₂′)
sim-cast {g₁⊑g₁′ = g₁⊑g₁′} {g₂⊑g₂′} {c̅} {c̅′} M⊑M′ c̅⊑c̅′ (ξ M′→N′)
  with sim {g⊑g′ = g₁⊑g₁′} M⊑M′ M′→N′
... | ⟨ N , M→N , N⊑N′ ⟩ =
  ⟨ N ⟪ c̅ ⟫ , plug-congₑ M→N , ⊑-cast {g₁⊑g₁′ = g₁⊑g₁′} {g₂⊑g₂′} N⊑N′ c̅⊑c̅′ ⟩
sim-cast {g₁⊑g₁′ = g₁⊑g₁′} {g₂⊑g₂′} M⊑M′ c̅⊑c̅′ ξ-blame =
  ⟨ _ , _ ∎ , ⊑-blame {g⊑g′ = g₂⊑g₂′} (⊢cast (proj₁ (prec→⊢ {g⊑g′ = g₁⊑g₁′} M⊑M′))) ⟩
sim-cast {g₁⊑g₁′ = g₁⊑g₁′} {g₂⊑g₂′} {c̅} {c̅′} M⊑M′ c̅⊑id β-id
  with catchup {g⊑g′ = g₁⊑g₁′} v-l M⊑M′
... | ⟨ l ℓ , v-l , M↠V , ⊑-l ⟩ =
  case catchupₗ _ _ id c̅⊑id of λ where
  ⟨ c̅₁ , id , c̅↠c̅₁ , ⊑-id l⊑l ⟩ →
    let ♥ = ↠ₑ-trans (plug-congₑ M↠V) (_ —→⟨ cast c̅↠c̅₁ id ⟩ _ —→⟨ β-id ⟩ _ ∎) in
    ⟨ l ℓ , ♥ , ⊑-l ⟩
  ⟨ c̅₁ , inj 𝓋 , c̅↠c̅₁ , c̅₁⊑id ⟩ →
    let ♣ = ↠ₑ-trans (plug-congₑ M↠V) (_ —→⟨ cast c̅↠c̅₁ (inj 𝓋) ⟩ _ ∎) in
    ⟨ l ℓ ⟪ c̅₁ ⟫ , ♣ , ⊑-castl {g₁⊑g′ = l⊑l} {⋆⊑} ⊑-l (⊑-left-contract c̅₁⊑id) ⟩
  ⟨ c̅₁ , up 𝓋 , c̅↠c̅₁ , c̅₁⊑id ⟩ →
    let ♣ = ↠ₑ-trans (plug-congₑ M↠V) (_ —→⟨ cast c̅↠c̅₁ (up 𝓋) ⟩ _ ∎) in
    ⟨ l ℓ ⟪ c̅₁ ⟫ , ♣ , ⊑-castl {g₁⊑g′ = l⊑l} {g₂⊑g₂′} ⊑-l (⊑-left-contract c̅₁⊑id) ⟩
... | ⟨ l ℓ ⟪ c̅₁ ⟫ , v-cast i , M↠V , prec ⟩ =
  {!!}
sim-cast {g₁⊑g₁′ = g₁⊑g₁′} {g₂⊑g₂′} {c̅} {c̅′} M⊑M′ c̅⊑c̅′ (cast c̅′↠c̅ₙ 𝓋′)
  with catchup {g⊑g′ = g₁⊑g₁′} v-l M⊑M′
... | ⟨ l ℓ , v-l , M↠V , ⊑-l ⟩ =
  let ⟨ c̅₁ , 𝓋 , c̅↠c̅₁ , c̅₁⊑c̅ₙ ⟩ = sim-mult c̅⊑c̅′ 𝓋′ c̅′↠c̅ₙ in
  let ♣ = ↠ₑ-trans (plug-congₑ M↠V) (_ —→⟨ cast c̅↠c̅₁ 𝓋 ⟩ _ ∎) in
  ⟨ l ℓ ⟪ c̅₁ ⟫ , ♣ , ⊑-cast {g₁⊑g₁′ = g₁⊑g₁′} {g₂⊑g₂′} ⊑-l c̅₁⊑c̅ₙ ⟩
... | ⟨ l ℓ ⟪ c̅₁ ⟫ , v-cast i , M↠V , ⊑-castl ⊑-l c̅₁⊑ℓ ⟩ =
  let c̅₁⨟c̅⊑c̅′ : ⊢ c̅₁ ⨟ c̅ ⊑ c̅′
      c̅₁⨟c̅⊑c̅′ = comp-pres-⊑-lb c̅₁⊑ℓ c̅⊑c̅′ in
  let ⟨ c̅₂ , 𝓋 , c̅₁⨟c̅↠c̅₂ , c̅₂⊑c̅ₙ ⟩ = sim-mult c̅₁⨟c̅⊑c̅′ 𝓋′ c̅′↠c̅ₙ in
  let ♥ = ↠ₑ-trans (plug-congₑ M↠V)
                    (_ —→⟨ comp i ⟩ _ —→⟨ cast c̅₁⨟c̅↠c̅₂ 𝓋 ⟩ _ ∎) in
  ⟨ l ℓ ⟪ c̅₂ ⟫ , ♥ , ⊑-cast {g₁⊑g₁′ = l⊑l} {g₂⊑g₂′} ⊑-l c̅₂⊑c̅ₙ ⟩
sim-cast {g₁⊑g₁′ = g₁⊑g₁′} {g₂⊑g₂′} M⊑M′ c̅⊑c̅′ (blame x)
  with prec→⊢ {g⊑g′ = g₁⊑g₁′} M⊑M′
... | ⟨ ⊢M , ⊢l ⟩ = ⟨ _ , _ ∎ , ⊑-blame {g⊑g′ = g₂⊑g₂′} (⊢cast ⊢M) ⟩
sim-cast {g₁⊑g₁′ = g₁⊑g₁′} {g₂⊑g₂′} {c̅ = c̅} {c̅′} M⊑M′ c̅⊑c̅′ (comp i′)
  with catchup {g⊑g′ = g₁⊑g₁′} (v-cast i′) M⊑M′
... | ⟨ l ℓ , v-l , M↠V , ⊑-castr ⊑-l ℓ⊑c̅ᵢ ⟩ =
  ⟨ l ℓ ⟪ c̅ ⟫ , plug-congₑ M↠V , ⊑-cast {g₁⊑g₁′ = l⊑l} {g₂⊑g₂′} ⊑-l (comp-pres-⊑-rb ℓ⊑c̅ᵢ c̅⊑c̅′) ⟩
... | ⟨ l ℓ ⟪ c̅₁ ⟫ , v-cast i , M↠V , prec ⟩
  with prec→⊢ {g⊑g′ = g₁⊑g₁′} prec
... | ⟨ ⊢cast ⊢l , ⊢cast ⊢l ⟩
  with prec-inv {g⊑g′ = g₁⊑g₁′} prec
... | ⟨ refl , c̅₁⊑c̅ᵢ ⟩ =
  let ♣ = ↠ₑ-trans (plug-congₑ M↠V)
                    (l ℓ ⟪ c̅₁ ⟫ ⟪ c̅ ⟫ —→⟨ comp i ⟩ _ ∎) in
  ⟨ l ℓ ⟪ c̅₁ ⨟ c̅ ⟫ , ♣ ,
    ⊑-cast {g₁⊑g₁′ = l⊑l} {g₂⊑g₂′} ⊑-l (comp-pres-prec c̅₁⊑c̅ᵢ c̅⊑c̅′) ⟩


sim (⊑-cast {g₁⊑g₁′ = g₁⊑g₁′} {g₂⊑g₂′} M⊑M′ c̅⊑c̅′) M′→N′ =
  sim-cast {g₁⊑g₁′ = g₁⊑g₁′} {g₂⊑g₂′} M⊑M′ c̅⊑c̅′ M′→N′
sim (⊑-castl M⊑M′ x) M′→N′ = {!!}
sim (⊑-castr M⊑M′ x) M′→N′ = {!!}
