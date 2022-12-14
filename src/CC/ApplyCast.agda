module CC.ApplyCast where

open import Data.Bool renaming (Bool to ð¹)
open import Data.Product renaming (_,_ to â¨_,_â©)
open import Relation.Nullary using (Â¬_; Dec; yes; no)
open import Relation.Nullary.Negation using (contradiction)
open import Relation.Binary.PropositionalEquality using (_â¡_; _â¢_; refl)
open import Function using (case_of_)

open import Common.Utils
open import Common.Types
open import CC.CCStatics


infix 4 ApplyCast_,_â_

data ApplyCast_,_â_ : â {A B} (V : Term) â (c : Cast A â B) â Term â Set where

  cast-base-id : â {V Î¹ g} {c : Cast ` Î¹ of g â ` Î¹ of g}
    â ApplyCast V , c â V

  cast-base-proj : â {V Î¹ ââ ââ p q c~ d~}
    â ââ â¼ ââ
    â let câ = cast (` Î¹ of l ââ) (` Î¹ of â) p c~ in
       let câ = cast (` Î¹ of â) (` Î¹ of l ââ) q d~ in
         ApplyCast V â¨ câ â© , câ â V

  cast-base-proj-blame : â {V Î¹ ââ ââ p q c~ d~}
    â Â¬ ââ â¼ ââ
    â let câ = cast (` Î¹ of l ââ) (` Î¹ of â) p c~ in
       let câ = cast (` Î¹ of â) (` Î¹ of l ââ) q d~ in
         ApplyCast V â¨ câ â© , câ â error (blame q)

  cast-fun-idâ : â {V Aâ Aâ Aâ Aâ Bâ Bâ Bâ Bâ gcâ gcâ gcâ gcâ â p q c~ d~ c~â² d~â²}
    â let câ  = cast (â¦ gcâ â§ Aâ â Bâ of l â) (â¦ gcâ â§ Aâ â Bâ of â   ) p c~  in
       let câ  = cast (â¦ gcâ â§ Aâ â Bâ of â   ) (â¦ gcâ â§ Aâ â Bâ of â   ) q d~  in
       let cââ² = cast (â¦ gcâ â§ Aâ â Bâ of l â) (â¦ gcâ â§ Aâ â Bâ of l â) p c~â² in
       let cââ² = cast (â¦ gcâ â§ Aâ â Bâ of l â) (â¦ gcâ â§ Aâ â Bâ of â   ) q d~â² in
         ApplyCast V â¨ câ â© , câ â V â¨ cââ² â© â¨ cââ² â©

  cast-fun-proj : â {V Aâ Aâ Aâ Aâ Bâ Bâ Bâ Bâ gcâ gcâ gcâ gcâ ââ ââ p q c~ d~ c~â² d~â²}
    â ââ â¼ ââ
    â let câ  = cast (â¦ gcâ â§ Aâ â Bâ of l ââ) (â¦ gcâ â§ Aâ â Bâ of â   ) p c~  in
       let câ  = cast (â¦ gcâ â§ Aâ â Bâ of â   ) (â¦ gcâ â§ Aâ â Bâ of l ââ) q d~  in
       let cââ² = cast (â¦ gcâ â§ Aâ â Bâ of l ââ) (â¦ gcâ â§ Aâ â Bâ of l ââ) p c~â² in
       let cââ² = cast (â¦ gcâ â§ Aâ â Bâ of l ââ) (â¦ gcâ â§ Aâ â Bâ of l ââ) q d~â² in
         ApplyCast V â¨ câ â© , câ â V â¨ cââ² â© â¨ cââ² â©

  cast-fun-proj-blame : â {V Aâ Aâ Aâ Aâ Bâ Bâ Bâ Bâ gcâ gcâ gcâ gcâ ââ ââ p q c~ d~}
    â Â¬ ââ â¼ ââ
    â let câ  = cast (â¦ gcâ â§ Aâ â Bâ of l ââ) (â¦ gcâ â§ Aâ â Bâ of â   ) p c~  in
       let câ  = cast (â¦ gcâ â§ Aâ â Bâ of â   ) (â¦ gcâ â§ Aâ â Bâ of l ââ) q d~  in
         ApplyCast V â¨ câ â© , câ â error (blame q)

  cast-fun-pc-idâ : â {V Aâ Aâ Aâ Aâ Bâ Bâ Bâ Bâ gâ gâ ââ gâ pc p q c~ d~ c~â² d~â²}
    â let câ  = cast (â¦ l pc â§ Aâ â Bâ of gâ  ) (â¦ â    â§ Aâ â Bâ of gâ) p c~  in
       let câ  = cast (â¦ â    â§ Aâ â Bâ of l ââ) (â¦ â    â§ Aâ â Bâ of gâ) q d~  in
       let cââ² = cast (â¦ l pc â§ Aâ â Bâ of gâ  ) (â¦ l pc â§ Aâ â Bâ of gâ) p c~â² in
       let cââ² = cast (â¦ l pc â§ Aâ â Bâ of l ââ) (â¦ â    â§ Aâ â Bâ of gâ) q d~â² in
         ApplyCast V â¨ câ â© , câ â V â¨ cââ² â© â¨ cââ² â©

  cast-fun-pc-proj : â {V Aâ Aâ Aâ Aâ Bâ Bâ Bâ Bâ gâ gâ ââ gâ pcâ pcâ p q c~ d~ c~â² d~â²}
    â pcâ â¼ pcâ
    â let câ  = cast (â¦ l pcâ â§ Aâ â Bâ of gâ  ) (â¦ â     â§ Aâ â Bâ of gâ) p c~  in
       let câ  = cast (â¦ â     â§ Aâ â Bâ of l ââ) (â¦ l pcâ â§ Aâ â Bâ of gâ) q d~  in
       let cââ² = cast (â¦ l pcâ â§ Aâ â Bâ of gâ  ) (â¦ l pcâ â§ Aâ â Bâ of gâ) p c~â² in
       let cââ² = cast (â¦ l pcâ â§ Aâ â Bâ of l ââ) (â¦ l pcâ â§ Aâ â Bâ of gâ) q d~â² in
         ApplyCast V â¨ câ â© , câ â V â¨ cââ² â© â¨ cââ² â©

  cast-fun-pc-proj-blame : â {V Aâ Aâ Aâ Aâ Bâ Bâ Bâ Bâ gâ gâ ââ gâ pcâ pcâ p q c~ d~}
    â Â¬ pcâ â¼ pcâ
    â let câ  = cast (â¦ l pcâ â§ Aâ â Bâ of gâ  ) (â¦ â     â§ Aâ â Bâ of gâ) p c~  in
       let câ  = cast (â¦ â     â§ Aâ â Bâ of l ââ) (â¦ l pcâ â§ Aâ â Bâ of gâ) q d~  in
         ApplyCast V â¨ câ â© , câ â error (blame q)

  cast-ref-idâ : â {V A B C D â p q c~ d~ c~â² d~â²}
    â let câ  = cast (Ref A of l â) (Ref B of â  ) p c~  in
       let câ  = cast (Ref C of â  ) (Ref D of â  ) q d~  in
       let cââ² = cast (Ref A of l â) (Ref B of l â) p c~â² in
       let cââ² = cast (Ref C of l â) (Ref D of â  ) q d~â² in
         ApplyCast V â¨ câ â© , câ â V â¨ cââ² â© â¨ cââ² â©

  cast-ref-proj : â {V A B C D ââ ââ p q c~ d~ c~â² d~â²}
    â ââ â¼ ââ
    â let câ  = cast (Ref A of l ââ) (Ref B of â   ) p c~  in
       let câ  = cast (Ref C of â   ) (Ref D of l ââ) q d~  in
       let cââ² = cast (Ref A of l ââ) (Ref B of l ââ) p c~â² in
       let cââ² = cast (Ref C of l ââ) (Ref D of l ââ) q d~â² in
         ApplyCast V â¨ câ â© , câ â V â¨ cââ² â© â¨ cââ² â©

  cast-ref-proj-blame : â {V A B C D ââ ââ p q c~ d~}
    â Â¬ ââ â¼ ââ
    â let câ  = cast (Ref A of l ââ) (Ref B of â   ) p c~  in
       let câ  = cast (Ref C of â   ) (Ref D of l ââ) q d~  in
         ApplyCast V â¨ câ â© , câ â error (blame q)

  cast-ref-ref-idâ : â {V Tâ Tâ Tâ Tâ gâ gâ ââ gâ â p q c~ d~ c~â² d~â²}
    â let câ  = cast (Ref (Tâ of l â) of gâ  ) (Ref (Tâ of â  ) of gâ) p c~  in
       let câ  = cast (Ref (Tâ of â  ) of l ââ) (Ref (Tâ of â  ) of gâ) q d~  in
       let cââ² = cast (Ref (Tâ of l â) of gâ  ) (Ref (Tâ of l â) of gâ) p c~â² in
       let cââ² = cast (Ref (Tâ of l â) of l ââ) (Ref (Tâ of â  ) of gâ) q d~â² in
         ApplyCast V â¨ câ â© , câ â V â¨ cââ² â© â¨ cââ² â©

  cast-ref-ref-proj : â {V Tâ Tâ Tâ Tâ gâ gâ ââ gâ ââ ââ p q c~ d~ c~â² d~â²}
    â ââ â¡ ââ
    â let câ  = cast (Ref (Tâ of l ââ) of gâ  ) (Ref (Tâ of â   ) of gâ) p c~  in
       let câ  = cast (Ref (Tâ of â   ) of l ââ) (Ref (Tâ of l ââ) of gâ) q d~  in
       let cââ² = cast (Ref (Tâ of l ââ) of gâ  ) (Ref (Tâ of l ââ) of gâ) p c~â² in
       let cââ² = cast (Ref (Tâ of l ââ) of l ââ) (Ref (Tâ of l ââ) of gâ) q d~â² in
         ApplyCast V â¨ câ â© , câ â V â¨ cââ² â© â¨ cââ² â©

  cast-ref-ref-proj-blame : â {V Tâ Tâ Tâ Tâ gâ gâ ââ gâ ââ ââ p q c~ d~}
    â Â¬ ââ â¡ ââ
    â let câ  = cast (Ref (Tâ of l ââ) of gâ  ) (Ref (Tâ of â   ) of gâ) p c~  in
       let câ  = cast (Ref (Tâ of â   ) of l ââ) (Ref (Tâ of l ââ) of gâ) q d~  in
         ApplyCast V â¨ câ â© , câ â error (blame q)
