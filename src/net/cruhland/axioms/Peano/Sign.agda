module net.cruhland.axioms.Peano.Sign where

import net.cruhland.axioms.AbstractAlgebra as AA
open import net.cruhland.axioms.Cast using (_As_; _as_; cast)
open import net.cruhland.axioms.Eq using (_≃_; _≄_; sym; trans)
open import net.cruhland.axioms.DecEq using (_≃?_)
open import net.cruhland.axioms.Operators using (_+_)
open import net.cruhland.axioms.Peano.Addition using (Addition)
open import net.cruhland.axioms.Peano.Base
  using () renaming (Peano to PeanoBase)
import net.cruhland.axioms.Peano.Inspect as Inspect
import net.cruhland.axioms.Peano.Literals as Literals
open import net.cruhland.axioms.Sign using (nonzero; Positive; Positivity)
open import net.cruhland.models.Function using (_∘_)
open import net.cruhland.models.Literals
open import net.cruhland.models.Logic using
  (_∧_; _∨_; ∨-introᴸ; ∨-introᴿ; ¬_; ¬[¬a∨¬b]→a∧b)

record Sign (PB : PeanoBase) (PA : Addition PB) : Set₁ where
  open PeanoBase PB using (ℕ; ind; step; step-case; step≄zero)
  private module ℕ+ = Addition PA
  private module ℕI = Inspect PB
  private module ℕLit = Literals PB

  field
    {{positivity}} : Positivity 0
    {{from-n≄0}} : {n : ℕ} → (n ≄ 0) As Positive n

  mkPositive : {A : Set} {n : ℕ} {{_ : A As Positive n}} → A → Positive n
  mkPositive = cast

  +-positive : {a b : ℕ} → Positive a → Positive (a + b)
  +-positive {a} {b} pos-a = ind P P0 Ps b
    where
      P = λ x → Positive (a + x)

      P0 : P 0
      P0 = AA.subst₁ (sym AA.ident) pos-a

      Ps : step-case P
      Ps {k} _ = mkPositive λ a+sk≃0 → step≄zero (trans AA.fnOpComm a+sk≃0)

  +-nonzero : {x y : ℕ} → x ≄ 0 → x + y ≄ 0
  +-nonzero = nonzero ∘ +-positive ∘ mkPositive

  +-both-zero : {a b : ℕ} → a + b ≃ 0 → a ≃ 0 ∧ b ≃ 0
  +-both-zero {a} {b} a+b≃0 =
    ¬[¬a∨¬b]→a∧b (a ≃? 0) (b ≃? 0) neither-positive
      where
        neither-positive : ¬ (a ≄ 0 ∨ b ≄ 0)
        neither-positive (∨-introᴸ a≄0) = +-nonzero a≄0 a+b≃0
        neither-positive (∨-introᴿ b≄0) = +-nonzero b≄0 (trans AA.comm a+b≃0)
