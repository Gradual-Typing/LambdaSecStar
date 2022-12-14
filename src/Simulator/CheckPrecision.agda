module Simulator.CheckPrecision where

open import Data.Nat
open import Data.Bool renaming (Bool to πΉ; _β_ to _βα΅_)
open import Data.Unit using (β€; tt)
open import Data.Maybe
open import Data.Product using (_Γ_; β; β-syntax) renaming (_,_ to β¨_,_β©)
open import Data.List hiding ([_])
open import Function using (case_of_)
open import Relation.Nullary using (Β¬_; Dec; yes; no)
open import Relation.Nullary.Decidable using (isYes)
open import Relation.Nullary.Negation using (contradiction)
open import Relation.Binary.PropositionalEquality
  using (_β‘_; _β’_; refl; trans; sym; subst; cong; congβ)

open import Common.Utils
open import Common.Types
open import Memory.Addr
open import Simulator.AST


{- Each case of the `check` function below reflects
   its corresponding rule in `Precision` -}
check-β? : (tβ tβ : AST) β πΉ
-- first get rid of all the `cast-pc`s
check-β? (castpc _ t _) tβ² = check-β? t tβ²
check-β? t (castpc _ tβ² _) = check-β? t tβ²
-- in most cases we expect the two sides to be syntactically equal
-- Var
check-β? (var x _) (var y _) = isYes (x β y)
-- Const
check-β? (const {ΞΉ} k β _) (const {ΞΉβ²} kβ² ββ² _) =
  case ` ΞΉ β‘α΅£? ` ΞΉβ² of Ξ» where
  (yes refl) β (isYes (const-eq? k kβ²)) β§ (isYes (β =? ββ²))
  (no  _)    β false
-- Addr
check-β? (addr a β _) (addr aβ² ββ² _) =
  (isYes (addr-eq? a aβ²)) β§ (isYes (β =? ββ²))
-- Lam
check-β? (lam βαΆ A t β _) (lam βαΆβ² Aβ² tβ² ββ² _) =
  (isYes (βαΆ =? βαΆβ²)) β§ (isYes (β =? ββ²)) β§
  (isYes (A β? Aβ²))   β§ (check-β? t tβ²)
-- App
check-β? (app tβ tβ _) (app tββ² tββ² _) = (check-β? tβ tββ²) β§ (check-β? tβ tββ²)
-- If
check-β? (cond tβ tβ tβ _) (cond tββ² tββ² tββ² _) =
  (check-β? tβ tββ²) β§ (check-β? tβ tββ²) β§ (check-β? tβ tββ²)
-- Let
check-β? (let-bind tβ tβ _) (let-bind tββ² tββ² _) =
  (check-β? tβ tββ²) β§ (check-β? tβ tββ²)
-- Ref, Ref?, and Refβ
check-β? (ref β t _) (ref ββ² tβ² _) = isYes (β =? ββ²) β§ (check-β? t tβ²)
check-β? (ref? β t _) (ref? ββ² tβ² _) = isYes (β =? ββ²) β§ (check-β? t tβ²)
check-β? (refβ β t _) (refβ ββ² tβ² _) = isYes (β =? ββ²) β§ (check-β? t tβ²)
-- -- Deref
check-β? (deref t _) (deref tβ² _) = check-β? t tβ²
-- Assign, Assign?, and Assignβ
check-β? (assign tβ tβ _) (assign tββ² tββ² _) = check-β? tβ tββ² β§ check-β? tβ tββ²
check-β? (assign? tβ tβ _) (assign? tββ² tββ² _) = check-β? tβ tββ² β§ check-β? tβ tββ²
check-β? (assignβ tβ tβ _) (assignβ tββ² tββ² _) = check-β? tβ tββ² β§ check-β? tβ tββ²
-- Prot
check-β? (protect β t _) (protect ββ² tβ² _) =
  isYes (β =? ββ²) β§ check-β? t tβ²
-- Cast
check-β? (cast t A B) (cast tβ² Aβ² Bβ²) =
  (isYes (A β? Aβ²) β§ isYes (B β? Bβ²) β§ check-β? t tβ²) β¨
  (isYes (A β? Bβ²) β§ isYes (B β? Bβ²) β§ check-β? t (cast tβ² Aβ² Bβ²)) β¨
  (isYes (B β? Aβ²) β§ isYes (B β? Bβ²) β§ check-β? (cast t A B) tβ²)
-- CastL
check-β? (cast t A B) tβ² =
  let Aβ² = get-type tβ² in
  isYes (A β? Aβ²) β§ isYes (B β? Aβ²) β§ check-β? t tβ²
-- CastR
check-β? t (cast tβ² Aβ² Bβ²) =
  let A = get-type t in
  isYes (A β? Aβ²) β§ isYes (A β? Bβ²) β§ check-β? t tβ²
check-β? t (err Aβ²) =
  let A = get-type t in
  isYes (A β? Aβ²)
-- Otherwise
check-β? _ _ = false
