open import Common.Types

module CC.CCSyntax (Cast_β_ : Type β Type β Set) where

open import Data.List
open import Data.Bool renaming (Bool to πΉ)

open import Syntax
open import Common.BlameLabels
open import Memory.Addr


data Error : Set where
  blame     : BlameLabel β Error
  nsu-error : Error

data Op : Set where
  op-addr         : (a : Addr) β (β : StaticLabel) β Op
  op-lam          : (pc : StaticLabel) β Type β (β : StaticLabel) β Op
  op-app          : Op
  op-const        : β {ΞΉ} β rep ΞΉ β StaticLabel β Op
  op-if           : Type β Op
  op-let          : Op
  op-ref          : StaticLabel β Op
  op-ref?         : StaticLabel β Op
  op-refβ         : StaticLabel β Op
  op-deref        : Op
  op-assign       : Op
  op-assign?      : Op
  op-assignβ      : Op
  op-cast         : β {A B} β Cast A β B β Op
  op-prot         : StaticLabel β Op
  op-cast-pc      : Label β Op
  op-error        : Error β Op
  {- Terms that only appear in erasure -}
  op-opaque       : Op

sig : Op β List Sig
sig (op-addr a β)      = []
sig (op-lam pc A β)    = (Ξ½ β ) β· []
sig op-app             = β  β· β  β· []
sig (op-const k β)     = []
sig (op-if A)          = β  β· β  β· β  β· []
sig op-let             = β  β· (Ξ½ β ) β· []
sig (op-ref  β)        = β  β· []
sig (op-ref? β)        = β  β· []
sig (op-refβ β)        = β  β· []
sig op-deref           = β  β· []
sig op-assign          = β  β· β  β· []
sig op-assign?         = β  β· β  β· []
sig op-assignβ         = β  β· β  β· []
sig (op-cast c)        = β  β· []
sig (op-prot β)        = β  β· []
sig (op-cast-pc g)     = β  β· []
sig (op-error e)       = []
sig op-opaque          = []

open Syntax.OpSig Op sig renaming (ABT to Term) hiding (plug) public

infixl 7  _Β·_
infix 8 _β¨_β©

pattern addr_of_ a β             = (op-addr a β) β¦ nil β¦
pattern Ζβ¦_β§_Λ_of_ pc A N β      = (op-lam pc A β) β¦ cons (bind (ast N)) nil β¦
pattern _Β·_ L M                  = op-app β¦ cons (ast L) (cons (ast M) nil) β¦
pattern $_of_ k β                = (op-const k β) β¦ nil β¦
pattern if L A M N               = (op-if A) β¦ cons (ast L) (cons (ast M) (cons (ast N) nil)) β¦
pattern `let M N                 = op-let β¦ cons (ast M) (cons (bind (ast N)) nil) β¦
pattern refβ¦_β§_ β M              = (op-ref β) β¦ cons (ast M) nil β¦
pattern ref?β¦_β§_ β M             = (op-ref? β) β¦ cons (ast M) nil β¦
pattern refββ¦_β§_ β M             = (op-refβ β) β¦ cons (ast M) nil β¦
pattern !_ M                     = op-deref β¦ cons (ast M) nil β¦
pattern _:=_  L M                = op-assign β¦ cons (ast L) (cons (ast M) nil) β¦
pattern _:=?_ L M                = op-assign? β¦ cons (ast L) (cons (ast M) nil) β¦
pattern _:=β_ L M                = op-assignβ β¦ cons (ast L) (cons (ast M) nil) β¦
pattern _β¨_β© M c                 = (op-cast c) β¦ cons (ast M) nil β¦
pattern prot β M                 = (op-prot β) β¦ cons (ast M) nil β¦      {- protection term -}
pattern cast-pc g M              = (op-cast-pc g) β¦ cons (ast M) nil β¦
pattern error e                  = (op-error e) β¦ nil β¦                  {- blame / nsu error -}
pattern β                        = op-opaque β¦ nil β¦                    {- opaque value -}


{- There are 3 forms of reference creation: static, not-yet-checked, and checked -}
data RefCreation : (StaticLabel β Term β Term) β Set where
  static    : RefCreation refβ¦_β§_
  unchecked : RefCreation ref?β¦_β§_
  checked   : RefCreation refββ¦_β§_

{- There are 3 forms of reference assignment: static, not-yet-checked, and checked -}
data RefAssign : (Term β Term β Term) β Set where
  static    : RefAssign _:=_
  unchecked : RefAssign _:=?_
  checked   : RefAssign _:=β_
