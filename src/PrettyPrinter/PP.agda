module PrettyPrinter.PP where

open import Data.Bool renaming (Bool to š¹)
open import Data.Unit using (ā¤; tt)
open import Agda.Builtin.String
open import Text.Printf


{- Pretty printing types -}
open import Common.Types
open import Common.BlameLabels

pprint-label : Label ā String
pprint-label ā = printf "\ESC[35m%s\ESC[0m" "ā"
pprint-label (l low) = printf "\ESC[32m%s\ESC[0m" "L"
pprint-label (l high) = printf "\ESC[31m%s\ESC[0m" "H"

pprint-blame-label : BlameLabel ā String
pprint-blame-label (pos x) = printf "\ESC[90m@%u\ESC[0m" x
pprint-blame-label (neg x) = printf "\ESC[90m@%u\ESC[0m" x

pprint-raw-type : RawType ā String
pprint-type : Type ā String

pprint-raw-type (` Bool) = "š¹"
pprint-raw-type (` Unit) = "ā¤"
pprint-raw-type (Ref A) = printf "Ref (%s)" (pprint-type A)
pprint-raw-type (ā¦ gc ā§ A ā B) = printf "ā¦%sā§ (%s) ā (%s)" (pprint-label gc) (pprint-type A) (pprint-type B)

pprint-type (T of g) = printf "%s of %s" (pprint-raw-type T) (pprint-label g)


{- Pretty printing the surface language -}
open import Surface.SurfaceLang

pprint-const : ā {Ī¹} (k : rep Ī¹) ā String
pprint-const {Bool} true  = "true"
pprint-const {Bool} false = "false"
pprint-const {Unit} tt    = "()"

pprint-term : Term ā String
pprint-term (` x)      = printf "\ESC[4m%u\ESC[0m" x
pprint-term ($ k of ā) = printf "%s of %s" (pprint-const k) (pprint-label (l ā))
pprint-term (Ęā¦ pc ā§ A Ė N of ā) =
  printf "Ī»ā¦%sā§ %s. %s of %s" (pprint-label (l pc)) (pprint-type A) (pprint-term N) (pprint-label (l ā))
pprint-term (L Ā· M at p) =
  printf "(%s) (%s) %s" (pprint-term L) (pprint-term M) (pprint-blame-label p)
pprint-term (if L then M else N at p) =
  printf "\ESC[1mif\ESC[0m (%s) \ESC[1mthen\ESC[0m (%s) \ESC[1melse\ESC[0m (%s) %s"
    (pprint-term L) (pprint-term M) (pprint-term N) (pprint-blame-label p)
pprint-term (M ā¶ A at p) =
  printf "(%s) \ESC[1m:\ESC[0m %s %s" (pprint-term M) (pprint-type A) (pprint-blame-label p)
pprint-term (`let M `in N) =
  printf "\ESC[1mlet\ESC[0m %s \ESC[1min\ESC[0m\n%s" (pprint-term M) (pprint-term N)
pprint-term (refā¦ ā ā§ M at p) =
  printf "\ESC[1mref\ESC[0m %s (%s) %s" (pprint-label (l ā)) (pprint-term M) (pprint-blame-label p)
pprint-term (! M) = printf "\ESC[1m!\ESC[0m (%s)" (pprint-term M)
pprint-term (L := M at p) =
  printf "(%s) \ESC[1m:=\ESC[0m (%s) %s" (pprint-term L) (pprint-term M) (pprint-blame-label p)

{- Pretty printing the cast calculus -}
open import CC.CCStatics renaming (Term to CCTerm)
open import Memory.Heap CCTerm Value

pprint-addr : Addr ā String
pprint-addr (aā¦ āĢ ā§ n) = printf "ā¦%sā§ \ESC[7m%u\ESC[0m" (pprint-label (l āĢ)) n

pprint-cast : ā {A B} ā Cast A ā B ā String
pprint-cast (cast A B p A~B) = printf "%s ā %s %s" (pprint-type A) (pprint-type B) (pprint-blame-label p)

pprint-error : CC.CCStatics.Error ā String
pprint-error (blame p) = printf "\ESC[93mblame\ESC[0m %s" (pprint-blame-label p)
pprint-error nsu-error = "\ESC[93mnsu-error\ESC[0m"

pprint-cc : CCTerm ā String
pprint-cc (` x) = printf "\ESC[4m%u\ESC[0m" x
pprint-cc (addr a of ā) = printf "%s of %s" (pprint-addr a) (pprint-label (l ā))
pprint-cc ($ k of ā) = printf "%s of %s" (pprint-const k) (pprint-label (l ā))
pprint-cc (Ęā¦ pc ā§ A Ė N of ā) =
  printf "Ī»ā¦%sā§ %s. %s of %s" (pprint-label (l pc)) (pprint-type A) (pprint-cc N) (pprint-label (l ā))
pprint-cc (L Ā· M) =
  printf "(%s) (%s)" (pprint-cc L) (pprint-cc M)
pprint-cc (if L A M N) =
  printf "\ESC[1mif\ESC[0m (%s) \ESC[1mthen\ESC[0m (%s) \ESC[1melse\ESC[0m (%s)"
    (pprint-cc L) (pprint-cc M) (pprint-cc N)
pprint-cc (`let M N) =
  printf "\ESC[1mlet\ESC[0m %s \ESC[1min\ESC[0m\n%s" (pprint-cc M) (pprint-cc N)
pprint-cc (refā¦ ā ā§ M) =
  printf "\ESC[1mref\ESC[0m %s (%s)" (pprint-label (l ā)) (pprint-cc M)
pprint-cc (ref?ā¦ ā ā§ M) =
  printf "\ESC[1mref?\ESC[0m %s (%s)" (pprint-label (l ā)) (pprint-cc M)
pprint-cc (refāā¦ ā ā§ M) =
  printf "\ESC[1mrefā\ESC[0m %s (%s)" (pprint-label (l ā)) (pprint-cc M)
pprint-cc (! M) =
 printf "\ESC[1m!\ESC[0m (%s)" (pprint-cc M)
pprint-cc (L := M) =
  printf "(%s) \ESC[1m:=\ESC[0m (%s)" (pprint-cc L) (pprint-cc M)
pprint-cc (L :=? M) =
  printf "(%s) \ESC[1m:=?\ESC[0m (%s)" (pprint-cc L) (pprint-cc M)
pprint-cc (L :=ā M) =
  printf "(%s) \ESC[1m:=ā\ESC[0m (%s)" (pprint-cc L) (pprint-cc M)
pprint-cc (prot ā M) =
  printf "\ESC[1mprot\ESC[0m %s (%s)" (pprint-label (l ā)) (pprint-cc M)
pprint-cc (M āØ c ā©) =
  printf "(%s) \ESC[1māØ\ESC[0m %s \ESC[1mā©\ESC[0m" (pprint-cc M) (pprint-cast c)
pprint-cc (cast-pc g M) =
  printf "\ESC[1mcast-pc\ESC[0m %s (%s)" (pprint-label g) (pprint-cc M)
pprint-cc (error e) =
  printf "\ESC[1merror\ESC[0m %s" (pprint-error e)
pprint-cc ā = "ā"


{- Pretty printing single and multi step reductions -}
open import CC.Reduction

print-red-rule : ā {M Mā² Ī¼ Ī¼ā² pc} ā M ā£ Ī¼ ā£ pc āā Mā² ā£ Ī¼ā² ā String
print-red-rule (Ī¾ MāMā²)           = printf "Ī¾(%s)" (print-red-rule MāMā²)
print-red-rule Ī¾-err               = "Ī¾-err"
print-red-rule (prot-val _)        = "prot-val"
print-red-rule (prot-ctx MāMā²)    = printf "prot-ctx(%s)" (print-red-rule MāMā²)
print-red-rule prot-err            = "prot-err"
print-red-rule (Ī² _)               = "Ī²"
print-red-rule Ī²-if-true           = "Ī²-if-true"
print-red-rule Ī²-if-false          = "Ī²-if-false"
print-red-rule (Ī²-let _)           = "Ī²-let"
print-red-rule ref-static          = "ref-static"
print-red-rule (ref?-ok _)         = "ref?-ok"
print-red-rule (ref?-fail _)       = "ref?-fail"
print-red-rule (ref _ _)           = "ref"
print-red-rule (deref _)           = "deref"
print-red-rule assign-static       = "assign-static"
print-red-rule (assign?-ok _)      = "assign?-ok"
print-red-rule (assign?-fail _)    = "assign?-fail"
print-red-rule (assign _)          = "assign"
print-red-rule (cast _ _ _)        = "cast"
print-red-rule (if-cast-true _)    = "if-cast-true"
print-red-rule (if-cast-false _)   = "if-cast-false"
print-red-rule (fun-cast _ _ _)    = "fun-cast"
print-red-rule (deref-cast _ _)    = "deref-cast"
print-red-rule (assign?-cast _ _)  = "assign?-cast"
print-red-rule (assign-cast _ _ _) = "assign-cast"
print-red-rule (Ī²-cast-pc _)       = "Ī²-cast-pc"

pprint-reduction : ā {M Mā² Ī¼ Ī¼ā² pc} ā M ā£ Ī¼ ā£ pc āā Mā² ā£ Ī¼ā² ā String
pprint-reduction {M} {Mā²} MāMā² =
  printf "(%s āāāØ %s ā© %s)" (pprint-cc M) (print-red-rule MāMā²) (pprint-cc Mā²)

pprint-mult-reduction : ā {M Mā² Ī¼ Ī¼ā² pc} ā M ā£ Ī¼ ā£ pc āā  Mā² ā£ Ī¼ā² ā String
pprint-mult-reduction (M ā£ Ī¼ ā£ pc ā) =
  printf "%s\n  \ESC[90mā\ESC[0m" (pprint-cc M)
pprint-mult-reduction {L} {N} (L ā£ Ī¼ ā£ pc āāāØ LāM ā© Mā N) =
  printf "%s\n  \ESC[90mā āØ %s ā©\ESC[0m\n%s"
    (pprint-cc L) (print-red-rule LāM) (pprint-mult-reduction Mā N)
