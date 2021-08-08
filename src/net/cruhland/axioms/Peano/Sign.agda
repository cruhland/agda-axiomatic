open import net.cruhland.axioms.Cast using (_As_; _as_; cast)
open import net.cruhland.axioms.Eq using (_≄_)
open import net.cruhland.axioms.Peano.Base
  using () renaming (Peano to PeanoBase)
import net.cruhland.axioms.Peano.Literals as Literals
import net.cruhland.axioms.Sign as S
open import net.cruhland.models.Literals

module net.cruhland.axioms.Peano.Sign (PB : PeanoBase) where

open PeanoBase PB using (ℕ)
private module ℕLit = Literals PB

record Sign : Set₁ where
  field
    {{positivity}} : S.Positivity ℕ
    Pos-intro-≄0 : {n : ℕ} → n ≄ 0 → S.Positive n
