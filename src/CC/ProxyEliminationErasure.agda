module CC.ProxyEliminationErasure where

open import Data.Nat
open import Data.Unit using (β€; tt)
open import Data.Bool using (true; false) renaming (Bool to πΉ)
open import Data.List
open import Data.Product using (_Γ_; β-syntax; projβ; projβ) renaming (_,_ to β¨_,_β©)
open import Data.Maybe
open import Relation.Nullary using (Β¬_; Dec; yes; no)
open import Relation.Nullary.Negation using (contradiction)
open import Relation.Binary.PropositionalEquality using (_β‘_; refl; sym; trans; subst; substβ)
open import Function using (case_of_)

open import Common.Utils
open import Common.Types
open import CC.CCStatics
open import CC.WellTyped
open import CC.ProxyElimination
open import CC.Erasure


elim-fun-proxy-erase : β {A B C D gcβ gcβ gβ gβ} {M}
  β β {c : Cast (β¦ gcβ β§ A β B of gβ) β (β¦ gcβ β§ C β D of gβ)}
  β β V W (i : Inert c) pc
  β M β‘ elim-fun-proxy V W i pc
  β Β¬ Err M
    ----------------------------------------------------
  β erase M β‘ erase (V Β· W)
elim-fun-proxy-erase V W (I-fun c I-label I-label) pc refl Β¬err with c
... | cast (β¦ l pcβ β§ A β B of l ββ) (β¦ l pcβ β§ C β D of gβ) p _ = refl
... | cast (β¦ l pcβ β§ A β B of l ββ) (β¦ β     β§ C β D of gβ) p _
  with pc β ββ βΌ? pcβ
...   | yes _ = refl
...   | no  _ = contradiction E-error Β¬err

elim-ref-proxy-erase : β {A B gβ gβ} {N} {_β_}
  β β {c : Cast Ref A of gβ β Ref B of gβ}
  β β V M (i : Inert c)
  β RefAssign _β_
  β N β‘ elim-ref-proxy V M i _β_
  β Β¬ Err N
    ----------------------------------------------------
  β erase N β‘ erase (V β M)
elim-ref-proxy-erase V M (I-ref c I-label I-label) static refl Β¬err with c
... | cast (Ref (S of l ββ) of l β) (Ref (T of l ββ) of g) p _ = refl
... | cast (Ref (S of l ββ) of l β) (Ref (T of β   ) of g) p _
  with β βΌ? ββ
...   | yes _ = refl
...   | no  _ = contradiction E-error Β¬err
elim-ref-proxy-erase V M (I-ref c I-label I-label) checked refl Β¬err with c
... | cast (Ref (S of l ββ) of l β) (Ref (T of l ββ) of g) p _ = refl
... | cast (Ref (S of l ββ) of l β) (Ref (T of β   ) of g) p _
  with β βΌ? ββ
...   | yes _ = refl
...   | no  _ = contradiction E-error Β¬err
elim-ref-proxy-erase V M (I-ref c I-label I-label) unchecked refl Β¬err with c
... | cast (Ref (S of l ββ) of l β) (Ref (T of l ββ) of g) p _ = refl
... | cast (Ref (S of l ββ) of l β) (Ref (T of β   ) of g) p _
  with β βΌ? ββ
...   | yes _ = refl
...   | no  _ = contradiction E-error Β¬err
