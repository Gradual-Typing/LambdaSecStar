open import Data.Nat
open import Data.Unit using (â¤; tt)
open import Data.Bool using (true; false) renaming (Bool to ð¹)
open import Data.List hiding ([_])
open import Data.Product renaming (_,_ to â¨_,_â©)
open import Data.Maybe
open import Relation.Nullary using (Â¬_; Dec; yes; no)
open import Relation.Binary.PropositionalEquality using (_â¡_; refl; sym)

open import Utils
open import Heap
open import Types
open import TypeBasedCast
open import CC


module ErasedReduction where

open import Reduction public

infix 2 _â£_â£_âââ_â£_

data _â£_â£_âââ_â£_ : Term â Heap â StaticLabel â Term â Heap â Set where

  Î¾ : â {M Mâ² F Î¼ Î¼â² pc}
    â M        â£ Î¼ â£ pc âââ Mâ²        â£ Î¼â²
      ---------------------------------------------- Î¾
    â plug M F â£ Î¼ â£ pc âââ plug Mâ² F â£ Î¼â²

  Î¾-err : â {F Î¼ pc e}
      ---------------------------------------------- Î¾-error
    â plug (error e) F â£ Î¼ â£ pc âââ error e â£ Î¼

  discard-ctx : â {M Mâ² Î¼ Î¼â² pc}
    â M         â£ Î¼ â£ high âââ Mâ²         â£ Î¼â²
      --------------------------------------------------- DiscardContext
    â discard M â£ Î¼ â£ pc   âââ discard Mâ² â£ Î¼â²

  discard-err : â {Î¼ pc e}
      --------------------------------------------------- DiscardError
    â discard (error e) â£ Î¼ â£ pc âââ error e â£ Î¼

  discard-val : â {V Î¼ pc}
    â Value V
      ------------------------------------ Discard
    â discard V â£ Î¼ â£ pc âââ â â£ Î¼

  Î² : â {V N Î¼ pc pcâ² A}
    â Value V
      ------------------------------------------------------------------- Î²
    â (Æ[ pcâ² ] A Ë N of low) Â· V â£ Î¼ â£ pc âââ N [ V ] â£ Î¼

  Î²-if-true : â {M N Î¼ pc A}
      ----------------------------------------------------------- IfTrue
    â if ($ true of low) A M N â£ Î¼ â£ pc âââ M â£ Î¼

  Î²-if-false : â {M N Î¼ pc A}
      ----------------------------------------------------------- IfFalse
    â if ($ false of low) A M N â£ Î¼ â£ pc âââ N â£ Î¼

  Î²-let : â {V N Î¼ pc}
    â Value V
      -------------------------------------- Let
    â `let V N â£ Î¼ â£ pc âââ N [ V ] â£ Î¼

  ref-static : â {M Î¼ pc â}
      ------------------------------------------------- RefStatic
    â ref[ â ] M â£ Î¼ â£ pc âââ refâ[ â ] M â£ Î¼

  ref?-ok : â {M Î¼ pc â}
      ------------------------------------------------- RefNSUSuccess
    â ref?[ â ] M â£ Î¼ â£ pc âââ refâ[ â ] M â£ Î¼

  ref?-fail : â {M Î¼ pc â}
      ------------------------------------------------- RefNSUFail
    â ref?[ â ] M â£ Î¼ â£ pc âââ error nsu-error â£ Î¼

  ref : â {V Î¼ pc a â}
    â Value V
      ----------------------------------------------------------------- Ref
    â refâ[ â ] V â£ Î¼ â£ pc âââ addr a of low â£ â¨ a , V , â â© â· Î¼

  deref-low : â {V Î¼ pc a}
    â key _â_ Î¼ a â¡ just â¨ V , low â©
      ------------------------------------------------------- DerefLow
    â ! (addr a of low) â£ Î¼ â£ pc âââ V â£ Î¼

  deref-high : â {V Î¼ pc a}
      ------------------------------------------------------- DerefHigh
    â ! (addr a of low) â£ Î¼ â£ pc âââ discard V â£ Î¼

  assign-static : â {L M Î¼ pc}
      ----------------------------------------- AssignStatic
    â L := M â£ Î¼ â£ pc âââ L :=â M â£ Î¼

  assign?-ok : â {M Î¼ pc a}
      -------------------------------------------------------------------- AssignNSUSuccess
    â (addr a of low) :=? M â£ Î¼ â£ pc âââ (addr a of low) :=â M â£ Î¼

  assign?-fail : â {M Î¼ pc a}
      -------------------------------------------------------------------- AssignNSUFail
    â (addr a of low) :=? M â£ Î¼ â£ pc âââ error nsu-error â£ Î¼

  assign : â {V Î¼ pc a â}
    â Value V
      ------------------------------------------------------------------------ Assign
    â (addr a of low) :=â V â£ Î¼ â£ pc âââ $ tt of low â£ â¨ a , V , â â© â· Î¼

  {- Special rules that consume â -}
  app-â : â {V M Î¼ pc}
    â Value V
      -------------------------------------- Appâ
    â â Â· V â£ Î¼ â£ pc âââ discard M â£ Î¼

  if-true-â : â {M N Î¼ pc A}
      -------------------------------------------- IfTrueâ
    â if â A M N â£ Î¼ â£ pc âââ discard M â£ Î¼

  if-false-â : â {M N Î¼ pc A}
      -------------------------------------------- IfFalseâ
    â if â A M N â£ Î¼ â£ pc âââ discard N â£ Î¼

  deref-â : â {M Î¼ pc}
      ----------------------------------- Derefâ
    â ! â â£ Î¼ â£ pc âââ discard M â£ Î¼

  assign?-okâ : â {M Î¼ pc}
      ---------------------------------------------- AssignNSUSuccessâ
    â â :=? M â£ Î¼ â£ pc âââ â :=â M â£ Î¼

  assign?-failâ : â {M Î¼ pc}
      ---------------------------------------------- AssignNSUFailâ
    â â :=? M â£ Î¼ â£ pc âââ error nsu-error â£ Î¼

  assign-â : â {V Î¼ pc}
    â Value V
      ------------------------------------------------------------------------ Assignâ
    â â :=â V â£ Î¼ â£ pc âââ $ tt of low â£ Î¼ {- skip the assignment -}


infix  2 _â£_â£_ââ â_â£_
infixr 2 _â£_â£_âââ¨_â©_
infix  3 _â£_â£_â

data _â£_â£_ââ â_â£_ : Term â Heap â StaticLabel â Term â Heap â Set where

    _â£_â£_â : â M Î¼ pc
        -----------------------------------
      â M â£ Î¼ â£ pc ââ â M â£ Î¼

    _â£_â£_âââ¨_â©_ : â L Î¼ pc {M N Î¼â² Î¼â³}
      â L â£ Î¼  â£ pc âââ M â£ Î¼â²
      â M â£ Î¼â² â£ pc ââ â N â£ Î¼â³
        -----------------------------------
      â L â£ Î¼  â£ pc ââ â N â£ Î¼â³

_â£_â£_â¡â : â {M Mâ²} â M â¡ Mâ² â â Î¼ pc â M â£ Î¼ â£ pc ââ â Mâ² â£ Î¼
Mâ¡Mâ² â£ Î¼ â£ pc â¡â rewrite Mâ¡Mâ² = _ â£ _ â£ _ â

plug-mult : â {M Mâ² Î¼ Î¼â² pc} (F : Frame)
  â M        â£ Î¼ â£ pc ââ â Mâ²        â£ Î¼â²
  â plug M F â£ Î¼ â£ pc ââ â plug Mâ² F â£ Î¼â²
plug-mult F (_ â£ _ â£ _ â)            = _ â£ _ â£ _ â
plug-mult F (_ â£ _ â£ _ âââ¨ R â© R*) = _ â£ _ â£ _ âââ¨ Î¾ {F = F} R â© plug-mult F R*

discard-mult : â {M Mâ² Î¼ Î¼â² pc}
  â M         â£ Î¼ â£ high ââ â Mâ²         â£ Î¼â²
  â discard M â£ Î¼ â£ pc   ââ â discard Mâ² â£ Î¼â²
discard-mult (_ â£ _ â£ _ â)            = _ â£ _ â£ _ â
discard-mult (_ â£ _ â£ _ âââ¨ R â© R*) = _ â£ _ â£ _ âââ¨ discard-ctx R â© discard-mult R*

{- Address does not reduce -}
addrâ¿ââ : â {M Mâ² Î¼ Î¼â² pc a â} â M â¡ addr a of â â Â¬ (M â£ Î¼ â£ pc âââ Mâ² â£ Î¼â²)
addrâ¿ââ eq (Î¾ {F = F} _)       = plug-not-addr _ F eq
addrâ¿ââ eq (Î¾-err {F} {e = e}) = plug-not-addr (error e) F eq

Æâ¿ââ : â {M Mâ² Î¼ Î¼â² pc pcâ² A N â} â M â¡ Æ[ pcâ² ] A Ë N of â â Â¬ (M â£ Î¼ â£ pc âââ Mâ² â£ Î¼â²)
Æâ¿ââ eq (Î¾ {F = F} _)       = plug-not-lam _ F eq
Æâ¿ââ eq (Î¾-err {F} {e = e}) = plug-not-lam (error e) F eq

constâ¿ââ : â {M Mâ² Î¼ Î¼â² pc Î¹} {k : rep Î¹} {â} â M â¡ $ k of â â Â¬ (M â£ Î¼ â£ pc âââ Mâ² â£ Î¼â²)
constâ¿ââ eq (Î¾ {F = F} _)       = plug-not-const _ F eq
constâ¿ââ eq (Î¾-err {F} {e = e}) = plug-not-const (error e) F eq

ââ¿ââ : â {M Mâ² Î¼ Î¼â² pc} â M â¡ â â Â¬ (M â£ Î¼ â£ pc âââ Mâ² â£ Î¼â²)
ââ¿ââ eq (Î¾ {F = F} _)       = plug-not-â _ F eq
ââ¿ââ eq (Î¾-err {F} {e = e}) = plug-not-â (error e) F eq

errorâ¿ââ : â {M Mâ² Î¼ Î¼â² pc e} â M â¡ error e â Â¬ (M â£ Î¼ â£ pc âââ Mâ² â£ Î¼â²)
errorâ¿ââ eq (Î¾ {F = F} _)       = plug-not-error _ F eq
errorâ¿ââ eq (Î¾-err {F} {e = e}) = plug-not-error (error e) F eq
