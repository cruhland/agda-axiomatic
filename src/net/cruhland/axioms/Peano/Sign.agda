module net.cruhland.axioms.Peano.Sign where

open import net.cruhland.axioms.Cast using (_As_; _as_; cast)
open import net.cruhland.axioms.Eq using (_≄_)
open import net.cruhland.axioms.Peano.Base
  using () renaming (Peano to PeanoBase)
import net.cruhland.axioms.Peano.Literals as Literals
open import net.cruhland.axioms.Sign using (Positive; Positivity)
open import net.cruhland.models.Literals

record Sign (PB : PeanoBase) : Set₁ where
  open PeanoBase PB using (ℕ)
  private module ℕLit = Literals PB

  field
    {{positivity}} : Positivity 0
    {{from-n≄0}} : {n : ℕ} → (n ≄ 0) As Positive n

  mkPositive : {A : Set} {n : ℕ} {{_ : A As Positive n}} → A → Positive n
  mkPositive = cast
