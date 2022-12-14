module CC.Reduction where

open import Data.Nat
open import Data.Unit using (â¤; tt)
open import Data.Bool using (true; false) renaming (Bool to ð¹)
open import Data.List hiding ([_])
open import Data.Product renaming (_,_ to â¨_,_â©)
open import Data.Maybe
open import Relation.Nullary using (Â¬_; Dec; yes; no)
open import Relation.Binary.PropositionalEquality using (_â¡_; refl)

open import Common.Utils
open import Common.Types
open import CC.CCStatics
open import Memory.Heap Term Value

open import CC.ApplyCast        public
open import CC.ProxyElimination public
open import CC.Frame            public


infix 2 _â£_â£_ââ_â£_

data _â£_â£_ââ_â£_ : Term â Heap â StaticLabel â Term â Heap â Set where

  Î¾ : â {M Mâ² F Î¼ Î¼â² pc}
    â M        â£ Î¼ â£ pc ââ Mâ²        â£ Î¼â²
      ---------------------------------------------- Î¾
    â plug M F â£ Î¼ â£ pc ââ plug Mâ² F â£ Î¼â²

  Î¾-err : â {F Î¼ pc e}
      ---------------------------------------------- Î¾-error
    â plug (error e) F â£ Î¼ â£ pc ââ error e â£ Î¼

  prot-val : â {V Î¼ pc â}
    â (v : Value V)
      --------------------------------------------------- ProtectVal
    â prot â V â£ Î¼ â£ pc ââ stamp-val V v â â£ Î¼

  prot-ctx : â {M Mâ² Î¼ Î¼â² pc â}
    â M        â£ Î¼ â£ pc â â ââ Mâ²        â£ Î¼â²
      --------------------------------------------------- ProtectContext
    â prot â M â£ Î¼ â£ pc     ââ prot â Mâ² â£ Î¼â²

  prot-err : â {Î¼ pc â e}
      --------------------------------------------------- ProtectContext
    â prot â (error e) â£ Î¼ â£ pc ââ error e â£ Î¼

  Î² : â {V N Î¼ pc pcâ² A â}
    â Value V
      ------------------------------------------------------------------- Î²
    â (Æâ¦ pcâ² â§ A Ë N of â) Â· V â£ Î¼ â£ pc ââ prot â (N [ V ]) â£ Î¼

  Î²-if-true : â {M N Î¼ pc A â}
      ----------------------------------------------------------------------- IfTrue
    â if ($ true of â) A M N â£ Î¼ â£ pc ââ prot â M â£ Î¼

  Î²-if-false : â {M N Î¼ pc A â}
      ----------------------------------------------------------------------- IfFalse
    â if ($ false of â) A M N â£ Î¼ â£ pc ââ prot â N â£ Î¼

  Î²-let : â {V N Î¼ pc}
    â Value V
      -------------------------------------- Let
    â `let V N â£ Î¼ â£ pc ââ N [ V ] â£ Î¼

  ref-static : â {M Î¼ pc â}
      ------------------------------------------------- RefStatic
    â refâ¦ â â§ M â£ Î¼ â£ pc ââ refââ¦ â â§ M â£ Î¼

  ref?-ok : â {M Î¼ pc â}
    â pc â¼ â
      ------------------------------------------------- RefNSUSuccess
    â ref?â¦ â â§ M â£ Î¼ â£ pc ââ refââ¦ â â§ M â£ Î¼

  ref?-fail : â {M Î¼ pc â}
    â Â¬ pc â¼ â
      ------------------------------------------------- RefNSUFail
    â ref?â¦ â â§ M â£ Î¼ â£ pc ââ error nsu-error â£ Î¼

  ref : â {V Î¼ pc n â}
    â (v : Value V)
    â aâ¦ â â§ n FreshIn Î¼  {- address is fresh -}
      -------------------------------------------------------------------------------- Ref
    â refââ¦ â â§ V â£ Î¼ â£ pc ââ addr (aâ¦ â â§ n) of low â£ cons-Î¼ (aâ¦ â â§ n) V v Î¼

  deref : â {V Î¼ pc v n â âÌ}
    â lookup-Î¼ Î¼ (aâ¦ âÌ â§ n) â¡ just (V & v)
      --------------------------------------------------------------------- Deref
    â ! (addr (aâ¦ âÌ â§ n) of â) â£ Î¼ â£ pc ââ prot (âÌ â â) V â£ Î¼

  assign-static : â {L M Î¼ pc}
      ------------------------------------------------------- AssignStatic
    â L := M â£ Î¼ â£ pc ââ L :=â M â£ Î¼

  assign?-ok : â {M Î¼ pc n â âÌ}
    â pc â¼ âÌ
      ----------------------------------------------------------------------------- AssignNSUSuccess
    â (addr (aâ¦ âÌ â§ n) of â) :=? M â£ Î¼ â£ pc ââ (addr (aâ¦ âÌ â§ n) of â) :=â M â£ Î¼

  assign?-fail : â {M Î¼ pc n â âÌ}
    â Â¬ pc â¼ âÌ
      ----------------------------------------------------------------------------- AssignNSUFail
    â (addr (aâ¦ âÌ â§ n) of â) :=? M â£ Î¼ â£ pc ââ error nsu-error â£ Î¼

  assign : â {V Î¼ pc n â âÌ}
    â (v : Value V)
      ---------------------------------------------------------------------------------------------- Assign
    â (addr (aâ¦ âÌ â§ n) of â) :=â V â£ Î¼ â£ pc ââ $ tt of low â£ cons-Î¼ (aâ¦ âÌ â§ n) V v Î¼

  {- Reduction rules about casts, active and inert: -}
  cast : â {A B V M Î¼ pc} {c : Cast A â B}
    â Value V â Active c
    â ApplyCast V , c â M
      -------------------------------------------------- Cast
    â V â¨ c â© â£ Î¼ â£ pc ââ M â£ Î¼

  if-cast-true : â {M N Î¼ pc A g â} {c : Cast (` Bool of g) â (` Bool of â)}
    â Inert c
      --------------------------------------------------------------------------------------------- IfCastTrue
    â if ($ true of â â¨ c â©) A M N â£ Î¼ â£ pc ââ prot â (cast-pc â M) â¨ branch/c A c â© â£ Î¼

  if-cast-false : â {M N Î¼ pc A g â} {c : Cast (` Bool of g) â (` Bool of â)}
    â Inert c
      --------------------------------------------------------------------------------------------- IfCastFalse
    â if ($ false of â â¨ c â©) A M N â£ Î¼ â£ pc ââ prot â (cast-pc â N) â¨ branch/c A c â© â£ Î¼

  fun-cast : â {V W Î¼ pc A B C D gcâ gcâ gâ gâ} {c : Cast (â¦ gcâ â§ A â B of gâ) â (â¦ gcâ â§ C â D of gâ)}
    â Value V â Value W
    â (i : Inert c)
      ---------------------------------------------------------------- FunCast
    â (V â¨ c â©) Â· W â£ Î¼ â£ pc ââ elim-fun-proxy V W i pc â£ Î¼

  deref-cast : â {V Î¼ pc A B gâ gâ} {c : Cast (Ref A of gâ) â (Ref B of gâ)}
    â Value V
    â Inert c
      ------------------------------------------------------ DerefCast
    â ! (V â¨ c â©) â£ Î¼ â£ pc ââ ! V â¨ out/c c â© â£ Î¼

  assign?-cast : â {V M Î¼ pc A B gâ gâ} {c : Cast (Ref A of gâ) â (Ref B of gâ)}
    â Value V
    â (i : Inert c)
      ----------------------------------------------------------------------------- AssignNSUCast
    â (V â¨ c â©) :=? M â£ Î¼ â£ pc ââ elim-ref-proxy V M i _:=?_ â£ Î¼

  assign-cast : â {V W Î¼ pc A B gâ gâ} {c : Cast (Ref A of gâ) â (Ref B of gâ)}
    â Value V â Value W
    â (i : Inert c)
      --------------------------------------------------------------------------------------------- AssignCast
    â (V â¨ c â©) :=â W â£ Î¼ â£ pc ââ elim-ref-proxy V W i _:=â_ {- V := (W â¨ in/c c â©) -} â£ Î¼

  Î²-cast-pc : â {V Î¼ pc g}
    â Value V
      ------------------------------------- CastPC
    â cast-pc g V â£ Î¼ â£ pc ââ V â£ Î¼


{- Multi-step reduction -}
infix  2 _â£_â£_ââ _â£_
infixr 2 _â£_â£_âââ¨_â©_
infix  3 _â£_â£_â

data _â£_â£_ââ _â£_ : Term â Heap â StaticLabel â Term â Heap â Set where

    _â£_â£_â : â M Î¼ pc
        -----------------------------------
      â M â£ Î¼ â£ pc ââ  M â£ Î¼

    _â£_â£_âââ¨_â©_ : â L Î¼ pc {M N Î¼â² Î¼â³}
      â L â£ Î¼  â£ pc ââ M â£ Î¼â²
      â M â£ Î¼â² â£ pc ââ  N â£ Î¼â³
        -----------------------------------
      â L â£ Î¼  â£ pc ââ  N â£ Î¼â³
