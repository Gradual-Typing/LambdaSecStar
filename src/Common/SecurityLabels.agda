module Common.SecurityLabels where

open import Data.Maybe
open import Data.Bool renaming (Bool to ð¹; _â_ to _âáµ_)
open import Data.Unit using (â¤; tt)
open import Data.Product using (_Ã_; â; â-syntax) renaming (_,_ to â¨_,_â©)
open import Data.List using (List)
open import Function using (case_of_)
open import Relation.Nullary using (Â¬_; Dec; yes; no)
open import Relation.Nullary.Negation using (contradiction)
open import Relation.Binary.PropositionalEquality
  using (_â¡_; _â¢_; refl; trans; sym; subst; cong; congâ)

open import Common.Utils


{- **** Security labels **** -}
data StaticLabel : Set where
  high : StaticLabel
  low  : StaticLabel

data Label : Set where
  â : Label
  l : StaticLabel â Label

infix 4 _=?_
infix 4 _==?_

_=?_ : â (ââ ââ : StaticLabel) â Dec (ââ â¡ ââ)
low  =? low  = yes refl
high =? high = yes refl
low  =? high = no Î» ()
high =? low  = no Î» ()

_==?_ : â (gâ gâ : Label) â Dec (gâ â¡ gâ)
â ==? â = yes refl
â ==? l â = no Î» ()
l â ==? â = no Î» ()
l ââ ==? l ââ with ââ =? ââ
... | yes refl = yes refl
... | no  neq = no (Î» { refl â contradiction refl neq })


{- **** Label partial order **** -}
infix 5 _â¼_

data _â¼_ : StaticLabel â StaticLabel â Set where
  lâ¼l : low  â¼ low
  lâ¼h : low  â¼ high
  hâ¼h : high â¼ high

lowâ¼ : â â â low â¼ â
lowâ¼ low  = lâ¼l
lowâ¼ high = lâ¼h

_â¼high : â â â â â¼ high
low  â¼high = lâ¼h
high â¼high = hâ¼h

â¼-refl : â {â} â â â¼ â
â¼-refl {high}  = hâ¼h
â¼-refl {low}   = lâ¼l

â¼-trans : â {ââ ââ ââ}
  â ââ â¼ ââ â ââ â¼ ââ â ââ â¼ ââ
â¼-trans lâ¼l lâ¼l = lâ¼l
â¼-trans lâ¼l lâ¼h = lâ¼h
â¼-trans lâ¼h hâ¼h = lâ¼h
â¼-trans hâ¼h hâ¼h = hâ¼h

â¼-antisym : â {ââ ââ}
  â ââ â¼ ââ â ââ â¼ ââ â ââ â¡ ââ
â¼-antisym lâ¼l lâ¼l = refl
â¼-antisym hâ¼h hâ¼h = refl

infix 4 _â¼?_

_â¼?_ : â ââ ââ â Dec (ââ â¼ ââ)
low  â¼? low  = yes lâ¼l
low  â¼? high = yes lâ¼h
high â¼? high = yes hâ¼h
high â¼? low  = no Î» ()


{- **** Label subtyping **** -}
infix 5 _<:â_

data _<:â_ : Label â Label â Set where
  <:-â : â <:â â      {- â is neutral -}
  <:-l : â {ââ ââ} â ââ â¼ ââ â l ââ <:â l ââ

<:â-refl : â {g} â g <:â g
<:â-refl {â}   = <:-â
<:â-refl {l â} = <:-l â¼-refl

<:â-trans : â {gâ gâ gâ} â gâ <:â gâ â gâ <:â gâ â gâ <:â gâ
<:â-trans <:-â <:-â = <:-â
<:â-trans (<:-l âââ¼ââ) (<:-l âââ¼ââ) = <:-l (â¼-trans âââ¼ââ âââ¼ââ)

<:â-antisym : â {gâ gâ}
  â gâ <:â gâ â gâ <:â gâ â gâ â¡ gâ
<:â-antisym <:-â <:-â = refl
<:â-antisym (<:-l âââ¼ââ) (<:-l âââ¼ââ) = cong l (â¼-antisym âââ¼ââ âââ¼ââ)


{- **** Label consistency **** -}
infix 5 _~â_

data _~â_ : Label â Label â Set where
  â~ : â {g} â â ~â g
  ~â : â {g} â g ~â â
  l~ : â {â} â l â ~â l â

~â-refl : â {g} â g ~â g
~â-refl {â}   = â~
~â-refl {l _} = l~

~â-sym : â {gâ gâ} â gâ ~â gâ â gâ ~â gâ
~â-sym â~ = ~â
~â-sym ~â = â~
~â-sym l~ = l~


{- **** Label consistent subtyping **** -}
infix 5 _â¾_

data _â¾_ : Label â Label â Set where
  â¾-âr : â {g}     â g â¾ â
  â¾-âl : â {g}     â â â¾ g
  â¾-l  : â {ââ ââ} â ââ â¼ ââ â l ââ â¾ l ââ

lowâ¾ : â g â l low â¾ g
lowâ¾ â = â¾-âr
lowâ¾ (l â) = â¾-l (lowâ¼ â)

_â¾high : â g â g â¾ l high
â â¾high = â¾-âl
(l â) â¾high = â¾-l (â â¼high)

â¾-refl : â {g} â g â¾ g
â¾-refl {â}   = â¾-âr
â¾-refl {l x} = â¾-l â¼-refl

â¾-antisym : â {gâ gâ}
  â gâ â¾ gâ â gâ â¾ gâ â gâ ~â gâ
â¾-antisym â¾-âr _ = ~â
â¾-antisym â¾-âl _ = â~
â¾-antisym (â¾-l âââ¼ââ) (â¾-l âââ¼ââ)
  rewrite â¼-antisym âââ¼ââ âââ¼ââ = ~â-refl

-- Properties of label consistent subtyping
â¾-prop : â {gâ gâ : Label}
  â gâ â¾ gâ
  â â[ g ] (gâ ~â g) Ã (g <:â gâ)
â¾-prop {g} {â} â¾-âr = â¨ â , ~â , <:-â â©
â¾-prop {â} {g} â¾-âl = â¨ g , â~ , <:â-refl â©
â¾-prop {l ââ} {l ââ} (â¾-l âââ¼ââ) =
  â¨ l ââ , ~â-refl , <:-l âââ¼ââ â©

â¾-propâ² : â {gâ gâ : Label}
  â gâ â¾ gâ
  â â[ g ] (gâ <:â g) Ã (g ~â gâ)
â¾-propâ² {g} {â} â¾-âr = â¨ g , <:â-refl , ~â â©
â¾-propâ² {â} {g} â¾-âl = â¨ â , <:-â , â~ â©
â¾-propâ² {l ââ} {l ââ} (â¾-l âââ¼ââ) =
  â¨ l ââ , <:-l âââ¼ââ , ~â-refl â©

-- Consistency implies consistent subtyping
~âââ¾ : â {gâ gâ} â gâ ~â gâ â gâ â¾ gâ Ã gâ â¾ gâ
~âââ¾ â~ = â¨ â¾-âl , â¾-âr â©
~âââ¾ ~â = â¨ â¾-âr , â¾-âl â©
~âââ¾ (l~ {low}) = â¨ â¾-l lâ¼l , â¾-l lâ¼l â©
~âââ¾ (l~ {high}) = â¨ â¾-l hâ¼h , â¾-l hâ¼h â©


{- **** Label join **** -}
_â_ : StaticLabel â StaticLabel â StaticLabel
low â low = low
_   â _   = high

{- **** Label meet **** -}
_â_ : StaticLabel â StaticLabel â StaticLabel
high â high = high
_    â _    = low

â-assoc : â {ââ ââ ââ} â (ââ â ââ) â ââ â¡ ââ â (ââ â ââ)
â-assoc {high} = refl
â-assoc {low} {high} = refl
â-assoc {low} {low} {high} = refl
â-assoc {low} {low} {low} = refl

ââââ¡â : â {â} â â â â â¡ â
ââââ¡â {high} = refl
ââââ¡â {low} = refl

âââ[ââââ]â¡ââââ : â {â ââ} â ââ â (ââ â â) â¡ ââ â â
âââ[ââââ]â¡ââââ {â} {ââ}
  rewrite sym (â-assoc {ââ} {ââ} {â})
  rewrite (ââââ¡â {ââ}) = refl

ââhighâ¡high : â {â} â â â high â¡ high
ââhighâ¡high {low}  = refl
ââhighâ¡high {high} = refl

ââlowâ¡â : â {â} â â â low â¡ â
ââlowâ¡â {low}  = refl
ââlowâ¡â {high} = refl

-- TODO: better names
join-â¼ : â {ââ ââ â}
  â ââ â ââ â¼ â
  â ââ â¼ â Ã ââ â¼ â
join-â¼ {high} {high} {high} _ = â¨ hâ¼h , hâ¼h â©
join-â¼ {high} {low} {high} _ = â¨ hâ¼h , lâ¼h â©
join-â¼ {low} {high} {high} _ = â¨ lâ¼h , hâ¼h â©
join-â¼ {low} {low} {high} _ = â¨ lâ¼h , lâ¼h â©
join-â¼ {low} {low} {low} _ = â¨ lâ¼l , lâ¼l â©

meet-â¼ : â {ââ ââ â}
  â â â¼ ââ â ââ
  â â â¼ ââ Ã â â¼ ââ
meet-â¼ {high} {high} {high} _ = â¨ hâ¼h , hâ¼h â©
meet-â¼ {high} {high} {low} _ = â¨ lâ¼h , lâ¼h â©
meet-â¼ {high} {low} {low} _ = â¨ lâ¼h , lâ¼l â©
meet-â¼ {low} {high} {low} _ = â¨ lâ¼l , lâ¼h â©
meet-â¼ {low} {low} {low} _ = â¨ lâ¼l , lâ¼l â©

join-â¼â² : â {ââ âââ² ââ âââ²}
  â ââ â¼ âââ² â ââ â¼ âââ² â (ââ â ââ) â¼ (âââ² â âââ²)
join-â¼â² lâ¼l lâ¼l = lâ¼l
join-â¼â² lâ¼l lâ¼h = lâ¼h
join-â¼â² lâ¼l hâ¼h = hâ¼h
join-â¼â² lâ¼h lâ¼l = lâ¼h
join-â¼â² lâ¼h lâ¼h = lâ¼h
join-â¼â² lâ¼h hâ¼h = hâ¼h
join-â¼â² hâ¼h _ = hâ¼h


{- **** Label consistent join **** -}
_âÌ_ : Label â Label â Label
l ââ     âÌ l ââ   = l (ââ â ââ)
-- l high   âÌ â      = l high
_        âÌ â      = â
-- â        âÌ l high = l high
â        âÌ _      = â

{- **** Label consistent meet **** -}
_âÌ_ : Label â Label â Label
l ââ     âÌ l ââ   = l (ââ â ââ)
-- l low    âÌ â      = l low
_        âÌ â      = â
-- â        âÌ l low  = l low
â        âÌ _      = â

gâÌgâ¡g : â {g} â g âÌ g â¡ g
gâÌgâ¡g {â} = refl
gâÌgâ¡g {l â} = cong l ââââ¡â

gâÌââ¡â : â {g} â g âÌ â â¡ â
gâÌââ¡â {â} = refl
gâÌââ¡â {l â} = refl

gâÌlowâ¡g : â {g} â g âÌ l low â¡ g
gâÌlowâ¡g {â} = refl
gâÌlowâ¡g {l â} = cong l ââlowâ¡â

consis-join-~â : â {gâ gâ gâ gâ} â gâ ~â gâ â gâ ~â gâ â gâ âÌ gâ ~â gâ âÌ gâ
consis-join-~â {gâ = â} â~ _ = â~
consis-join-~â {gâ = l _} â~ _ = â~
consis-join-~â {gâ = â} ~â _ = ~â
consis-join-~â {gâ = l _} ~â _ = ~â
consis-join-~â l~ â~ = â~
consis-join-~â l~ ~â = ~â
consis-join-~â l~ l~ = l~

consis-join-â¾ : â {gâ gâ gâ gâ} â gâ â¾ gâ â gâ â¾ gâ â gâ âÌ gâ â¾ gâ âÌ gâ
consis-join-â¾ {gâ = â} â¾-âr y = â¾-âr
consis-join-â¾ {gâ = l _} â¾-âr y = â¾-âr
consis-join-â¾ {gâ = â} â¾-âl y = â¾-âl
consis-join-â¾ {gâ = l _} â¾-âl y = â¾-âl
consis-join-â¾ (â¾-l _) â¾-âr = â¾-âr
consis-join-â¾ (â¾-l _) â¾-âl = â¾-âl
consis-join-â¾ (â¾-l âââ¼ââ) (â¾-l âââ¼ââ) = â¾-l (join-â¼â² âââ¼ââ âââ¼ââ)

consis-join-â¾-inv : â {gâ gâ g} â gâ âÌ gâ â¡ g â gâ â¾ g Ã gâ â¾ g
consis-join-â¾-inv {g = â} eq = â¨ â¾-âr , â¾-âr â©
consis-join-â¾-inv {l ââ} {l ââ} {l â} refl =
  case join-â¼ {ââ} {ââ} {â} â¼-refl of Î» where
    â¨ âââ¼âââââ , âââ¼âââââ â© â â¨ â¾-l âââ¼âââââ , â¾-l âââ¼âââââ â©
consis-join-â¾-inv {â} {l ââ} {l â} ()

consis-meet-â¾-inv : â {gâ gâ g} â g â¡ gâ âÌ gâ â g â¾ gâ Ã g â¾ gâ
consis-meet-â¾-inv {g = â} eq = â¨ â¾-âl , â¾-âl â©
consis-meet-â¾-inv {l ââ} {l ââ} {l â} refl =
  case meet-â¼ {ââ} {ââ} {â} â¼-refl of Î» where
    â¨ ââââââ¼ââ , ââââââ¼ââ â© â â¨ â¾-l ââââââ¼ââ , â¾-l ââââââ¼ââ â©
consis-meet-â¾-inv {l ââ} {â} {l â} ()

consis-join-<:â : â {gâ gââ² gâ gââ²} â gâ <:â gââ² â gâ <:â gââ² â gâ âÌ gâ <:â gââ² âÌ gââ²
consis-join-<:â <:-â <:-â = <:-â
consis-join-<:â <:-â (<:-l x) = <:-â
consis-join-<:â (<:-l x) <:-â = <:-â
consis-join-<:â (<:-l âââ¼âââ²) (<:-l âââ¼âââ²) = <:-l (join-â¼â² âââ¼âââ² âââ¼âââ²)

consis-join-<:â-inv : â {gâ gâ â} â gâ âÌ gâ <:â l â â (gâ <:â l â) Ã (gâ <:â l â)
consis-join-<:â-inv {â} {â} ()
consis-join-<:â-inv {l ââ} {l ââ} (<:-l ââââââ¼â) =
  let â¨ âââ¼â , âââ¼â â© = join-â¼ ââââââ¼â in â¨ <:-l âââ¼â , <:-l âââ¼â â©

â¾-<: : â {gâ gâ g} â gâ â¾ gâ â gâ <:â g â gâ â¾ g
â¾-<: {gâ = â} gââ¾gâ <:-â = â¾-âr
â¾-<: {â} {l ââ} gââ¾gâ gâ<:g = â¾-âl
â¾-<: {l ââ} {l ââ} {l â} (â¾-l âââ¼ââ) (<:-l âââ¼â) = â¾-l (â¼-trans âââ¼ââ âââ¼â)


{- **** Label gradual meet **** -}
infix 5 _ââ_

_ââ_ : Label â Label â Maybe Label
l high ââ l high = just (l high)
l low  ââ l low  = just (l low)
â      ââ g      = just g
g      ââ â      = just g
_      ââ _      = nothing

grad-meet-~â : â {gâ gâ g}
  â gâ ââ gâ â¡ just g
  â gâ ~â g Ã gâ ~â g
grad-meet-~â {â} {â} {â} refl = â¨ â~ , â~ â©
grad-meet-~â {â} {l low} {l low} refl = â¨ â~ , l~ â©
grad-meet-~â {â} {l high} {l high} refl = â¨ â~ , l~ â©
grad-meet-~â {l high} {â} {l high} refl = â¨ l~ , â~ â©
grad-meet-~â {l high} {l high} {l high} refl = â¨ l~ , l~ â©
grad-meet-~â {l low} {â} {l low} refl = â¨ l~ , â~ â©
grad-meet-~â {l low} {l low} {l low} refl = â¨ l~ , l~ â©


{- **** Precision **** -}
data _ââ_ : Label â Label â Set where
  ââ : â {g} â â ââ g
  lâl : â {â} â l â ââ l â

infix 4 _ââ_

_ââ?_ : â (gâ gâ : Label) â Dec (gâ ââ gâ)
â ââ? â = yes ââ
â ââ? l _ = yes ââ
l x ââ? â = no Î» ()
l ââ ââ? l ââ =
  case ââ =? ââ of Î» where
  (yes refl) â yes lâl
  (no âââ¢ââ) â no Î» { lâl â contradiction refl âââ¢ââ }

consis-join-ââ : â {gâ gââ² gâ gââ²}
  â gâ ââ gââ² â gâ ââ gââ² â gâ âÌ gâ ââ gââ² âÌ gââ²
consis-join-ââ ââ  ââ  = ââ
consis-join-ââ ââ  lâl = ââ
consis-join-ââ lâl ââ  = ââ
consis-join-ââ lâl lâl = lâl
