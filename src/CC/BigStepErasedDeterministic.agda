module CC.BigStepErasedDeterministic where

open import Data.Empty using (β₯; β₯-elim)
open import Data.Bool using (true; false) renaming (Bool to πΉ)
open import Data.Sum using (_β_; injβ; injβ)
open import Data.Product using (_Γ_; β; β-syntax; Ξ£; Ξ£-syntax) renaming (_,_ to β¨_,_β©)
open import Relation.Nullary using (Β¬_; Dec; yes; no)
open import Relation.Nullary.Negation using (contradiction)
open import Relation.Binary.PropositionalEquality using (_β‘_; _β’_; refl; trans; cong; sym)
open import Function using (case_of_)

open import Common.Utils
open import Common.Types
open import Memory.Heap
open import CC.CCStatics
open import CC.BigStepErased


ββ-deterministic : β {M ΞΌ ΞΌβ ΞΌβ pc} {Vβ Vβ}
  β ΞΌ β£ pc β’ M ββ Vβ β£ ΞΌβ
  β ΞΌ β£ pc β’ M ββ Vβ β£ ΞΌβ
    -------------------------------------
  β Vβ β‘ Vβ Γ ΞΌβ β‘ ΞΌβ
ββ-deterministic (ββ-val _) (ββ-val _) = β¨ refl , refl β©
ββ-deterministic (ββ-app LβΖN MβV N[V]βW) (ββ-app LβΖNβ  MβVβ  N[V]βWβ ) =
  case ββ-deterministic LβΖN LβΖNβ  of Ξ» where
  β¨ refl , refl β© β
    case ββ-deterministic MβV MβVβ  of Ξ» where
    β¨ refl , refl β© β
      case ββ-deterministic N[V]βW N[V]βWβ  of Ξ» where
      β¨ refl , refl β© β β¨ refl , refl β©
ββ-deterministic (ββ-app LβΖN _ _) (ββ-app-β Lββ _) =
  contradiction (ββ-deterministic LβΖN Lββ) (Ξ» ())
ββ-deterministic (ββ-app-β Lββ _) (ββ-app LβΖN _ _) =
  contradiction (ββ-deterministic Lββ LβΖN) (Ξ» ())
ββ-deterministic (ββ-app-β Lββ MβV) (ββ-app-β Lβββ  MβVβ ) =
  case ββ-deterministic Lββ Lβββ  of Ξ» where
  β¨ refl , refl β© β
    case ββ-deterministic MβV MβVβ  of Ξ» where
    β¨ refl , refl β© β β¨ refl , refl β©
ββ-deterministic (ββ-if-true Lβtrue MβV) (ββ-if-true Lβtrueβ  MβVβ ) =
  case ββ-deterministic Lβtrue Lβtrueβ  of Ξ» where
  β¨ refl , refl β© β
    case ββ-deterministic MβV MβVβ  of Ξ» where
    β¨ refl , refl β© β β¨ refl , refl β©
ββ-deterministic (ββ-if-true Lβtrue _) (ββ-if-false Lβfalse _) =
  contradiction (ββ-deterministic Lβtrue Lβfalse) (Ξ» ())
ββ-deterministic (ββ-if-true Lβtrue _) (ββ-if-β Lββ) =
  contradiction (ββ-deterministic Lβtrue Lββ) (Ξ» ())
ββ-deterministic (ββ-if-false Lβfalse NβV) (ββ-if-false Lβfalseβ  NβVβ ) =
  case ββ-deterministic Lβfalse Lβfalseβ  of Ξ» where
  β¨ refl , refl β© β
    case ββ-deterministic NβV NβVβ  of Ξ» where
    β¨ refl , refl β© β β¨ refl , refl β©
ββ-deterministic (ββ-if-false Lβfalse _) (ββ-if-true Lβtrue _) =
  contradiction (ββ-deterministic Lβfalse Lβtrue) (Ξ» ())
ββ-deterministic (ββ-if-false Lβfalse _) (ββ-if-β Lββ) =
  contradiction (ββ-deterministic Lβfalse Lββ) (Ξ» ())
ββ-deterministic (ββ-if-β Lββ) (ββ-if-true Lβtrue _) =
  contradiction (ββ-deterministic Lββ Lβtrue ) (Ξ» ())
ββ-deterministic (ββ-if-β Lββ) (ββ-if-false Lβfalse _) =
  contradiction (ββ-deterministic Lββ Lβfalse) (Ξ» ())
ββ-deterministic (ββ-if-β Lββ) (ββ-if-β Lβββ ) =
  case ββ-deterministic Lββ Lβββ  of Ξ» where
  β¨ refl , refl β© β β¨ refl , refl β©
ββ-deterministic (ββ-let MβV N[V]βW) (ββ-let MβVβ  N[V]βWβ ) =
  case ββ-deterministic MβV MβVβ  of Ξ» where
  β¨ refl , refl β© β
    case ββ-deterministic N[V]βW N[V]βWβ  of Ξ» where
    β¨ refl , refl β© β β¨ refl , refl β©
ββ-deterministic (ββ-ref? MβV fresh _) (ββ-ref? MβVβ  freshβ  _) =
  case ββ-deterministic MβV MβVβ  of Ξ» where
  β¨ refl , refl β© β
    case trans fresh (sym freshβ ) of Ξ» where
      refl β β¨ refl , refl β©
ββ-deterministic (ββ-ref?-β MβV) (ββ-ref?-β MβVβ ) =
  case ββ-deterministic MβV MβVβ  of Ξ» where
  β¨ refl , refl β© β β¨ refl , refl β©
ββ-deterministic (ββ-ref MβV fresh) (ββ-ref MβVβ  freshβ ) =
  case ββ-deterministic MβV MβVβ  of Ξ» where
  β¨ refl , refl β© β
    case trans fresh (sym freshβ ) of Ξ» where
      refl β β¨ refl , refl β©
ββ-deterministic (ββ-ref-β MβV) (ββ-ref-β MβVβ ) =
  case ββ-deterministic MβV MβVβ  of Ξ» where
  β¨ refl , refl β© β β¨ refl , refl β©
ββ-deterministic (ββ-deref Mβa eq) (ββ-deref Mβaβ  eqβ ) =
  case ββ-deterministic Mβa Mβaβ  of Ξ» where
  β¨ refl , refl β© β
    case trans (sym eq) eqβ  of Ξ» where
    refl β β¨ refl , refl β©
ββ-deterministic (ββ-deref Mβa _) (ββ-deref-β Mββ) =
  contradiction (ββ-deterministic Mβa Mββ) (Ξ» ())
ββ-deterministic (ββ-deref-β Mββ) (ββ-deref Mβa _) =
  contradiction (ββ-deterministic Mββ Mβa) (Ξ» ())
ββ-deterministic (ββ-deref-β Mββ) (ββ-deref-β Mβββ ) =
  case ββ-deterministic Mββ Mβββ  of Ξ» where
  β¨ refl , refl β© β β¨ refl , refl β©
ββ-deterministic (ββ-assign? Lβa MβV _) (ββ-assign? Lβaβ  MβVβ  _) =
  case ββ-deterministic Lβa Lβaβ  of Ξ» where
  β¨ refl , refl β© β
    case ββ-deterministic MβV MβVβ  of Ξ» where
    β¨ refl , refl β© β β¨ refl , refl β©
ββ-deterministic (ββ-assign? Lβa _ _) (ββ-assign?-β Lββ _) =
  contradiction (ββ-deterministic Lβa Lββ) (Ξ» ())
ββ-deterministic (ββ-assign?-β Lββ _) (ββ-assign? Lβa _ _) =
  contradiction (ββ-deterministic Lββ Lβa) (Ξ» ())
ββ-deterministic (ββ-assign?-β Lββ MβV) (ββ-assign?-β Lβββ  MβVβ ) =
  case ββ-deterministic Lββ Lβββ  of Ξ» where
  β¨ refl , refl β© β
    case ββ-deterministic MβV MβVβ  of Ξ» where
    β¨ refl , refl β© β β¨ refl , refl β©
ββ-deterministic (ββ-assign Lβa MβV) (ββ-assign Lβaβ  MβVβ ) =
  case ββ-deterministic Lβa Lβaβ  of Ξ» where
  β¨ refl , refl β© β
    case ββ-deterministic MβV MβVβ  of Ξ» where
    β¨ refl , refl β© β β¨ refl , refl β©
ββ-deterministic (ββ-assign Lβa _) (ββ-assign-β Lββ _) =
  contradiction (ββ-deterministic Lβa Lββ) (Ξ» ())
ββ-deterministic (ββ-assign-β Lββ _) (ββ-assign Lβa _) =
  contradiction (ββ-deterministic Lββ Lβa) (Ξ» ())
ββ-deterministic (ββ-assign-β Lββ MβV) (ββ-assign-β Lβββ  MβVβ ) =
  case ββ-deterministic Lββ Lβββ  of Ξ» where
  β¨ refl , refl β© β
    case ββ-deterministic MβV MβVβ  of Ξ» where
    β¨ refl , refl β© β β¨ refl , refl β©
