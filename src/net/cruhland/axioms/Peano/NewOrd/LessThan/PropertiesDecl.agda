open import net.cruhland.axioms.NewOrd using (_<_; _≮_; LessThan)
open import net.cruhland.axioms.Peano.Base
  using () renaming (Peano to PeanoBase)
open import net.cruhland.models.Literals

module net.cruhland.axioms.Peano.NewOrd.LessThan.PropertiesDecl
  (PB : PeanoBase) where

open PeanoBase PB using (ℕ; step)
import net.cruhland.axioms.Peano.Literals PB as ℕL

record Properties {{_ : LessThan ℕ}} : Set where
  field
    n<sn : {n : ℕ} → n < step n
    n≮0 : {n : ℕ} → n ≮ 0
