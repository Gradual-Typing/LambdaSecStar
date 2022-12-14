module CC.BigStep where

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


infix 2 _â£_â¢_â_â£_
data _â£_â¢_â_â£_ : Heap â StaticLabel â (M V : Term) â Heap â Set

â-value : â {Î¼ Î¼â² pc M V} â Î¼ â£ pc â¢ M â V â£ Î¼â² â Value V

{- only consider evaluation to values -}
data _â£_â¢_â_â£_ where

  â-val : â {Î¼ pc V}
    â Value V
      --------------------------- Value
    â Î¼ â£ pc â¢ V â V â£ Î¼

  â-app : â {Î¼ Î¼â Î¼â Î¼â pc pcâ² L M N V W A â}
    â Î¼  â£ pc     â¢ L       â Æâ¦ pcâ² â§ A Ë N of â â£ Î¼â
    â Î¼â â£ pc     â¢ M       â V â£ Î¼â
    â (âW : Î¼â â£ pc â â â¢ N [ V ] â W â£ Î¼â)
      ---------------------------------------------------------------------- Application
    â Î¼  â£ pc     â¢ L Â· M   â stamp-val W (â-value âW) â â£ Î¼â

  â-if-true : â {Î¼ Î¼â Î¼â pc L M N V A â}
    â Î¼  â£ pc     â¢ L â $ true of â â£ Î¼â
    â (âV : Î¼â â£ pc â â â¢ M â V â£ Î¼â)
      ---------------------------------------------------------------------- IfTrue
    â Î¼  â£ pc     â¢ if L A M N â stamp-val V (â-value âV) â â£ Î¼â

  â-if-false : â {Î¼ Î¼â Î¼â pc L M N V A â}
    â Î¼  â£ pc     â¢ L â $ false of â â£ Î¼â
    â (âV : Î¼â â£ pc â â â¢ N â V â£ Î¼â)
      ---------------------------------------------------------------------- IfFalse
    â Î¼  â£ pc     â¢ if L A M N â stamp-val V (â-value âV) â â£ Î¼â

  â-let : â {Î¼ Î¼â Î¼â pc M N V W}
    â Î¼  â£ pc â¢ M        â V â£ Î¼â
    â Î¼â â£ pc â¢ N [ V ]  â W â£ Î¼â
      ----------------------------------------- Let
    â Î¼  â£ pc â¢ `let M N â W â£ Î¼â

  â-ref? : â {Î¼ Î¼â pc M V n â}
    â (âV : Î¼ â£ pc â¢ M â V â£ Î¼â)
    â aâ¦ â â§ n FreshIn Î¼â
    â pc â¼ â
      -------------------------------------------------------------------------------------- RefNSU
    â Î¼ â£ pc â¢ ref?â¦ â â§ M â addr aâ¦ â â§ n of low â£ cons-Î¼ (aâ¦ â â§ n) V (â-value âV) Î¼â

  â-ref : â {Î¼ Î¼â pc M V n â}
    â (âV : Î¼ â£ pc â¢ M â V â£ Î¼â)
    â aâ¦ â â§ n FreshIn Î¼â
      -------------------------------------------------------------------------------------- Ref
    â Î¼ â£ pc â¢ refâ¦ â â§ M â addr aâ¦ â â§ n of low â£ cons-Î¼ (aâ¦ â â§ n) V (â-value âV) Î¼â

  â-deref : â {Î¼ Î¼â pc M V v n â âÌ}
    â Î¼ â£ pc â¢ M â addr aâ¦ âÌ â§ n of â â£ Î¼â
    â lookup-Î¼ Î¼â (aâ¦ âÌ â§ n) â¡ just (V & v)
      ---------------------------------------------------------------------------- Deref
    â Î¼ â£ pc â¢ ! M â stamp-val V v (âÌ â â) â£ Î¼â

  â-assign? : â {Î¼ Î¼â Î¼â pc L M V n â âÌ}
    â Î¼  â£ pc â¢ L â addr aâ¦ âÌ â§ n of â â£ Î¼â
    â (âV : Î¼â â£ pc â¢ M â V â£ Î¼â)
    â pc â¼ âÌ
      -------------------------------------------------------------------------- AssignNSU
    â Î¼ â£ pc â¢ L :=? M â $ tt of low â£ cons-Î¼ (aâ¦ âÌ â§ n) V (â-value âV) Î¼â

  â-assign : â {Î¼ Î¼â Î¼â pc L M V n â âÌ}
    â Î¼  â£ pc â¢ L â addr aâ¦ âÌ â§ n of â â£ Î¼â
    â (âV : Î¼â â£ pc â¢ M â V â£ Î¼â)
      -------------------------------------------------------------------------- Assign
    â Î¼  â£ pc â¢ L := M â $ tt of low â£ cons-Î¼ (aâ¦ âÌ â§ n) V (â-value âV) Î¼â

  â-cast : â {Î¼ Î¼â Î¼â pc M N V W A B} {c : Cast A â B}
    â Active c
    â Î¼  â£ pc â¢ M â V â£ Î¼â
    â ApplyCast V , c â N
    â Î¼â â£ pc â¢ N â W â£ Î¼â
      --------------------------------------------------------- Cast
    â Î¼  â£ pc â¢ M â¨ c â© â W â£ Î¼â

  â-if-cast-true : â {Î¼ Î¼â Î¼â Î¼â pc L M N V W A g â}
                      {c : Cast (` Bool of g) â (` Bool of â)}
    â Inert c
    â Î¼  â£ pc     â¢ L                    â $ true of â â¨ c â© â£ Î¼â
    â (âV : Î¼â â£ pc â â â¢ M â V â£ Î¼â)
      {- don't need casting PC to â in big step -}
    â Î¼â â£ pc     â¢ stamp-val V (â-value âV) â â¨ branch/c A c â© â W â£ Î¼â
      --------------------------------------------------------- IfCastTrue
    â Î¼  â£ pc     â¢ if L A M N           â W â£ Î¼â

  â-if-cast-false : â {Î¼ Î¼â Î¼â Î¼â pc L M N V W A g â}
                       {c : Cast (` Bool of g) â (` Bool of â)}
    â Inert c
    â Î¼  â£ pc     â¢ L                    â $ false of â â¨ c â© â£ Î¼â
    â (âV : Î¼â â£ pc â â â¢ N â V â£ Î¼â)
    â Î¼â â£ pc     â¢ stamp-val V (â-value âV) â â¨ branch/c A c â© â W â£ Î¼â
      --------------------------------------------------------- IfCastFalse
    â Î¼  â£ pc     â¢ if L A M N           â W â£ Î¼â

  â-fun-cast : â {Î¼ Î¼â Î¼â Î¼â pc L M V Vâ² W A B C D gcâ gcâ gâ gâ}
                  {c : Cast (â¦ gcâ â§ A â B of gâ) â (â¦ gcâ â§ C â D of gâ)}
    â (i : Inert c)
    â Î¼  â£ pc â¢ L                       â V â¨ c â© â£ Î¼â
    â Î¼â â£ pc â¢ M                       â W  â£ Î¼â
    â Î¼â â£ pc â¢ elim-fun-proxy V W i pc â Vâ² â£ Î¼â
      --------------------------------------------------------- FunCast
    â Î¼  â£ pc â¢ L Â· M                   â Vâ² â£ Î¼â

  â-deref-cast : â {Î¼ Î¼â Î¼â pc M V W A B gâ gâ}
                    {c : Cast (Ref A of gâ) â (Ref B of gâ)}
    â Inert c
    â Î¼  â£ pc â¢ M               â V â¨ c â© â£ Î¼â
    â Î¼â â£ pc â¢ ! V â¨ out/c c â© â W â£ Î¼â
      --------------------------------------------------------- DerefCast
    â Î¼  â£ pc â¢ ! M             â W â£ Î¼â

  â-assign?-cast : â {Î¼ Î¼â Î¼â pc L M V W A B gâ gâ}
                      {c : Cast (Ref A of gâ) â (Ref B of gâ)}
    â (i : Inert c)
    â Î¼  â£ pc â¢ L                          â V â¨ c â© â£ Î¼â
    â Î¼â â£ pc â¢ elim-ref-proxy V M i _:=?_ â W â£ Î¼â
      ----------------------------------------------------------- AssignNSUCast
    â Î¼  â£ pc â¢ L :=? M                    â W â£ Î¼â

  â-assign-cast : â {Î¼ Î¼â Î¼â pc L M V W A B gâ gâ}
                     {c : Cast (Ref A of gâ) â (Ref B of gâ)}
    â (i : Inert c)
    â Î¼  â£ pc â¢ L                         â V â¨ c â© â£ Î¼â
    â Î¼â â£ pc â¢ elim-ref-proxy V M i _:=_ â W â£ Î¼â
      ----------------------------------------------------------- AssignCast
    â Î¼  â£ pc â¢ L := M                    â W â£ Î¼â


{- If M â V then V is Value -}
â-value (â-val v) = v
â-value (â-app _ _ âW) = stamp-val-value (â-value âW)
â-value (â-if-true  _ âV) = stamp-val-value (â-value âV)
â-value (â-if-false _ âV) = stamp-val-value (â-value âV)
â-value (â-let _ âV) = â-value âV
â-value (â-ref? _ _ _) = V-addr
â-value (â-ref _ _) = V-addr
â-value (â-deref {v = v} _ _) = stamp-val-value v
â-value (â-assign? _ _ _) = V-const
â-value (â-assign _ _) = V-const
â-value (â-cast          _ _ _ âV) = â-value âV
â-value (â-if-cast-true  _ _ _ âV) = â-value âV
â-value (â-if-cast-false _ _ _ âV) = â-value âV
â-value (â-fun-cast      _ _ _ âV) = â-value âV
â-value (â-deref-cast      _ _ âV) = â-value âV
â-value (â-assign?-cast    _ _ âV) = â-value âV
â-value (â-assign-cast     _ _ âV) = â-value âV

{- If M â V then M is not Error -}
error-not-â : â {Î¼ Î¼â² pc M V} â Î¼ â£ pc â¢ M â V â£ Î¼â² â Â¬ Err M
error-not-â (â-val ()) E-error
