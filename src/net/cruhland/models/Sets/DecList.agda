open import Data.List.Base
  using (List) renaming ([] to []ᴸ; _∷_ to _∷ᴸ_)
open import Data.List.Relation.Unary.All
  using (All; uncons) renaming ([] to []ᴬ; _∷_ to _∷ᴬ_)
open import Data.List.Relation.Unary.Any using (Any; here; there)
open import net.cruhland.axioms.DecEq using (_≃?_)
open import net.cruhland.axioms.Eq using (_≃_)
open import net.cruhland.models.Logic
  using ( _∧?_; uncurry; _∨_; _∨?_; ∨-introᴸ; ∨-introᴿ
        ; ¬-intro; Dec; dec-map; no; yes)
open import net.cruhland.models.Setoid using (DecSetoid; DecSetoid₀)

-- Replacement for some standard library functions that require a DecSetoid
module net.cruhland.models.Sets.DecList (DS : DecSetoid₀) where

open DecSetoid DS using () renaming (Carrier to A)

private
  variable
    P : A → Set

toSum : ∀ {x xs} → Any P (x ∷ᴸ xs) → P x ∨ Any P xs
toSum (here px)   = ∨-introᴸ px
toSum (there pxs) = ∨-introᴿ pxs

fromSum : ∀ {x xs} → P x ∨ Any P xs → Any P (x ∷ᴸ xs)
fromSum (∨-introᴸ px)  = here px
fromSum (∨-introᴿ pxs) = there pxs

all? : (∀ a → Dec (P a)) → ∀ xs → Dec (All P xs)
all? P? []ᴸ       = yes []ᴬ
all? P? (x ∷ᴸ xs) = dec-map (uncurry _∷ᴬ_) uncons (P? x ∧? all? P? xs)

any? : (∀ a → Dec (P a)) → ∀ xs → Dec (Any P xs)
any? P? []ᴸ       = no (¬-intro λ ())
any? P? (x ∷ᴸ xs) = dec-map fromSum toSum (P? x ∨? any? P? xs)

infix 4 _∈_
_∈_ : A → List A → Set _
x ∈ xs = Any (x ≃_) xs

infix 4 _∈?_
_∈?_ : ∀ x xs → Dec (x ∈ xs)
x ∈? xs = any? (x ≃?_) xs
