module Surface.SurfaceSyntax where

open import Data.List
open import Data.Bool renaming (Bool to πΉ)

open import Syntax
open import Common.BlameLabels
open import Common.Types


data Op : Set where
  op-lam    : (pc : StaticLabel) β Type β (β : StaticLabel) β Op
  op-app    : BlameLabel β Op
  op-const  : β {ΞΉ} β rep ΞΉ β StaticLabel β Op
  op-if     : BlameLabel β Op
  op-ann    : Type β BlameLabel β Op
  op-let    : Op
  op-ref    : StaticLabel β BlameLabel β Op
  op-deref  : Op
  op-assign : BlameLabel β Op

sig : Op β List Sig
sig (op-lam pc A β)    = (Ξ½ β ) β· []
sig (op-app p)         = β  β· β  β· []
sig (op-const k β)     = []
sig (op-if p)          = β  β· β  β· β  β· []
sig (op-ann A p)       = β  β· []
sig op-let             = β  β· (Ξ½ β ) β· []
sig (op-ref β p)       = β  β· []
sig op-deref           = β  β· []
sig (op-assign p)      = β  β· β  β· []

open Syntax.OpSig Op sig renaming (ABT to Term) hiding (plug; rename) public

infixl 7  _Β·_at_

pattern Ζβ¦_β§_Λ_of_ pc A N β      = (op-lam pc A β) β¦ cons (bind (ast N)) nil β¦
pattern _Β·_at_ L M p             = (op-app p) β¦ cons (ast L) (cons (ast M) nil) β¦
pattern $_of_ k β                = (op-const k β) β¦ nil β¦
pattern if_then_else_at_ L M N p = (op-if p) β¦ cons (ast L) (cons (ast M) (cons (ast N) nil)) β¦
pattern _βΆ_at_ M A p             = (op-ann A p) β¦ cons (ast M) nil β¦
pattern `let_`in_ M N            = op-let β¦ cons (ast M) (cons (bind (ast N)) nil) β¦
pattern refβ¦_β§_at_ β M p         = (op-ref β p) β¦ cons (ast M) nil β¦
pattern !_ M                     = op-deref β¦ cons (ast M) nil β¦
pattern _:=_at_ L M p            = (op-assign p) β¦ cons (ast L) (cons (ast M) nil) β¦
