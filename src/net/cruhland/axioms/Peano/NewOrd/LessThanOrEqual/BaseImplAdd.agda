import net.cruhland.axioms.AbstractAlgebra as AA
open import net.cruhland.axioms.Eq as Eq using (_≃_)
open Eq.≃-Reasoning
open import net.cruhland.axioms.NewOrd using (_≤_; LessThanOrEqual)
open import net.cruhland.axioms.Operators using (_+_)
open import net.cruhland.axioms.Peano.Addition using (Addition)
open import net.cruhland.axioms.Peano.Base
  using () renaming (Peano to PeanoBase)
import net.cruhland.axioms.Peano.NewOrd.LessThanOrEqual.AddDecl as AddDecl
open import net.cruhland.axioms.Peano.Sign using (Sign)

module net.cruhland.axioms.Peano.NewOrd.LessThanOrEqual.BaseImplAdd
  (PB : PeanoBase) (PS : Sign PB) (PA : Addition PB PS) where

private module AD = AddDecl PB PS PA
private module ℕ+ = Addition PA
open PeanoBase PB using (ℕ; step)

instance
  lessThanOrEqual : LessThanOrEqual ℕ
  lessThanOrEqual = record { _≤_ = AD._+d≃_ }

diff : {n m : ℕ} → n ≤ m → ℕ
diff = AD.diff

≤-intro-diff : {n m d : ℕ} → n + d ≃ m → n ≤ m
≤-intro-diff = AD.+d≃-intro

≤-elim-diff : {n m : ℕ} (n≤m : n ≤ m) → n + diff n≤m ≃ m
≤-elim-diff = AD.+d≃-elim

instance
  ≤-reflexive : Eq.Reflexive _≤_
  ≤-reflexive = Eq.reflexive (≤-intro-diff AA.ident)

≤-step : {n m : ℕ} → n ≤ m → n ≤ step m
≤-step {n} {m} n≤m = ≤-intro-diff n+sd≃sm
  where
    n+sd≃sm =
      begin
        n + step (diff n≤m)
      ≃˘⟨ AA.fnOpComm ⟩
        step (n + diff n≤m)
      ≃⟨ AA.subst₁ (≤-elim-diff n≤m) ⟩
        step m
      ∎
