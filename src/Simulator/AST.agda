module Simulator.AST where

open import Data.Nat
open import Data.Unit using (β€; tt)
open import Data.Bool using (true; false) renaming (Bool to πΉ)
open import Data.List
open import Data.Product using (_Γ_; β-syntax; projβ; projβ) renaming (_,_ to β¨_,_β©)
open import Data.Sum using (_β_; injβ; injβ)
open import Data.Maybe
open import Relation.Nullary using (Β¬_; Dec; yes; no)
open import Relation.Nullary.Negation using (contradiction)
open import Relation.Binary.PropositionalEquality using (_β‘_; refl; trans; subst; sym)
open import Function using (case_of_)

open import Common.Utils
open import Common.Types
open import Memory.Addr
open import CC.CCStatics


{- Each AST node embeds its type -}
data AST : Set where
  var : (n : β) β Type β AST
  const : β {ΞΉ} β (k : rep ΞΉ) β StaticLabel β Type β AST
  addr : Addr β StaticLabel β Type β AST
  lam : StaticLabel β Type β AST β StaticLabel β Type β AST
  app : AST β AST β Type β AST
  cond : AST β AST β AST β Type β AST
  let-bind : AST β AST β Type β AST
  ref : StaticLabel β AST β Type β AST
  ref? : StaticLabel β AST β Type β AST
  refβ : StaticLabel β AST β Type β AST
  deref : AST β Type β AST
  assign : AST β AST β Type β AST
  assign? : AST β AST β Type β AST
  assignβ : AST β AST β Type β AST
  protect : StaticLabel β AST β Type β AST
  cast : AST β Type β Type β AST
  castpc : Label β AST β Type β AST
  err : Type β AST
  -- sub : AST β Type β Type β AST

get-type : AST β Type
get-type (var _ A) = A
get-type (const _ _ A) = A
get-type (addr _ _ A) = A
get-type (lam _ _ _ _ A) = A
get-type (app _ _ A) = A
get-type (cond _ _ _ A) = A
get-type (let-bind _ _ A) = A
get-type (ref _ _ A) = A
get-type (ref? _ _ A) = A
get-type (refβ _ _ A) = A
get-type (deref _ A) = A
get-type (assign _ _ A) = A
get-type (assign? _ _ A) = A
get-type (assignβ _ _ A) = A
get-type (protect _ _ A) = A
get-type (cast _ _ A) = A
get-type (castpc _ _ A) = A
get-type (err A) = A
-- get-type (sub _ _ A) = A

{- Translates a typing derivation into an AST -}
to-ast : β {Ξ Ξ£ gc pc A} M β Ξ ΝΎ Ξ£ ΝΎ gc ΝΎ pc β’ M β¦ A β AST
to-ast {A = A} (` x) (β’var _) = var x A
to-ast {A = A} ($ k of β) β’const = const k β A
to-ast {A = A} (addr_of_ a β) (β’addr _) = addr a β A
to-ast {A = B} (Ζβ¦ pc β§ A Λ N of β) (β’lam β’N) =
  lam pc A (to-ast {pc = low} N β’N) β B
to-ast {A = A} (L Β· M) (β’app β’L β’M) = app (to-ast L β’L) (to-ast M β’M) A
to-ast {A = A} (if L _ M N) (β’if β’L β’M β’N) =
  cond (to-ast L β’L) (to-ast {pc = low} M β’M) (to-ast {pc = low} N β’N) A
to-ast {A = A} (`let M N) (β’let β’M β’N) =
  let-bind (to-ast M β’M) (to-ast {pc = low} N β’N) A
to-ast {A = A} (refβ¦ β β§ M) (β’ref β’M _) = ref β (to-ast M β’M) A
to-ast {A = A} (ref?β¦ β β§ M) (β’ref? β’M) = ref? β (to-ast M β’M) A
to-ast {A = A} (refββ¦ β β§ M) (β’refβ β’M _) = refβ β (to-ast M β’M) A
to-ast {A = A} (! M) (β’deref β’M) = deref (to-ast M β’M) A
to-ast {A = A} (L := M) (β’assign β’L β’M _) = assign (to-ast L β’L) (to-ast M β’M) A
to-ast {A = A} (L :=? M) (β’assign? β’L β’M) =
  assign? (to-ast L β’L) (to-ast {pc = low} M β’M) A
to-ast {A = A} (L :=β M) (β’assignβ β’L β’M _) =
  assignβ (to-ast L β’L) (to-ast M β’M) A
to-ast {A = A} (prot β M) (β’prot β’M) = protect β (to-ast M β’M) A
to-ast {A = B} (M β¨ c β©) (β’cast {A = A} {.B} β’M) = cast (to-ast M β’M) A B
to-ast {A = A} (cast-pc g M) (β’cast-pc β’M _) = castpc g (to-ast M β’M) A
to-ast {A = A} (error e) β’err = err A
to-ast {A = B} M (β’sub β’M _) = to-ast M β’M
-- to-ast {A = B} M (β’sub {A = A} {.B} β’M _) = sub (to-ast M β’M) A B
to-ast M (β’sub-pc β’M _) = to-ast M β’M

M : Term
M = (Ζβ¦ low β§ ` Bool of l high Λ ` 0 of low) Β· ($ true of low)

β’M : [] ΝΎ β ΝΎ l low ΝΎ low β’ M β¦ ` Bool of l high
β’M = β’app (β’lam (β’var refl)) (β’sub β’const (<:-ty (<:-l lβΌh) <:-ΞΉ))

t = to-ast M β’M
