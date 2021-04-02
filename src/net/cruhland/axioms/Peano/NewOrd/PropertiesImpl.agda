import net.cruhland.axioms.AbstractAlgebra as AA
open import net.cruhland.axioms.Eq as Eq using (_≃_; _≄_)
open Eq.≃-Reasoning
open import net.cruhland.axioms.NewOrd using (_≤_; _<_)
open import net.cruhland.axioms.Operators using (_+_)
open import net.cruhland.axioms.Peano.Addition using (Addition)
open import net.cruhland.axioms.Peano.Base
  using () renaming (Peano to PeanoBase)
open import net.cruhland.axioms.Peano.NewOrd.LessThan.BaseDecl using (LtBase)
open import net.cruhland.axioms.Peano.NewOrd.LessThanOrEqual.BaseDecl
  using (LteBase)
open import net.cruhland.axioms.Peano.NewOrd.LessThanOrEqual.PropertiesDecl
  using (LteProperties)
open import net.cruhland.axioms.Peano.Sign using (Sign)
open import net.cruhland.models.Literals
open import net.cruhland.models.Logic using
  (_∨_; ∨-comm; ∨-introᴸ; ∨-introᴿ; ∨-mapᴿ; contra)

module net.cruhland.axioms.Peano.NewOrd.PropertiesImpl
  (PB : PeanoBase)
  (PS : Sign PB)
  (PA : Addition PB PS)
  (LTEB : LteBase PB PS PA)
  (LTEP : LteProperties PB PS PA LTEB)
  (LTB : LtBase PB PS PA LTEB) where

private module ℕ+ = Addition PA
private open module ℕ = PeanoBase PB using (ℕ; step)
import net.cruhland.axioms.Peano.Inspect PB as ℕI
import net.cruhland.axioms.Peano.Literals PB as ℕL
private module ℕ< = LtBase LTB
private module ℕ≤ = LteBase LTEB
private module ℕ≤P = LteProperties LTEP

≤-dec-≃ : {n m : ℕ} → n ≤ m → n ≃ m ∨ n ≄ m
≤-dec-≃ {n} {m} n≤m with ℕI.case (ℕ≤.≤-diff n≤m)
... | ℕI.case-zero d≃0 = ∨-introᴸ (ℕ≤P.zero-diff n≤m d≃0)
... | ℕI.case-step (ℕI.pred-intro d′ d≃sd′) = ∨-introᴿ n≄m
  where
    n≄m = λ n≃m →
      let n+d≃n+0 =
            begin
              n + ℕ≤.≤-diff n≤m
            ≃⟨ ℕ≤.≤-elim-diff n≤m ⟩
              m
            ≃˘⟨ n≃m ⟩
              n
            ≃˘⟨ AA.ident ⟩
              n + 0
            ∎
          d≃0 = AA.cancel n+d≃n+0
       in contra (Eq.trans (Eq.sym d≃sd′) d≃0) ℕ.step≄zero

≤-split : {n m : ℕ} → n ≤ m → n < m ∨ n ≃ m
≤-split n≤m = ∨-comm (∨-mapᴿ (ℕ<.<-intro-≤≄ n≤m) (≤-dec-≃ n≤m))

s≤-from-< : {n m : ℕ} → n < m → step n ≤ m
s≤-from-< {n} {m} n<m =
  let n≤m = ℕ<.<-elim-≤ n<m
      n≄m = ℕ<.<-elim-≄ n<m
      d≄0 = λ d≃0 → contra (ℕ≤P.zero-diff n≤m d≃0) n≄m
      ℕI.pred-intro pd d≃spd = ℕI.pred d≄0
      sn+pd≃m =
        begin
          step n + pd
        ≃⟨ AA.fnOpCommSwap ⟩
          n + step pd
        ≃˘⟨ AA.subst₂ d≃spd ⟩
          n + ℕ≤.≤-diff n≤m
        ≃⟨ ℕ≤.≤-elim-diff n≤m ⟩
          m
        ∎
   in ℕ≤.≤-intro-diff sn+pd≃m

<-from-s≤ : {n m : ℕ} → step n ≤ m → n < m
<-from-s≤ {n} {m} sn≤m =
  let n≤m = Eq.trans ℕ≤P.n≤sn sn≤m
      n≄m = λ n≃m →
        let n+sd≃n+0 =
              begin
                n + step (ℕ≤.≤-diff sn≤m)
              ≃˘⟨ AA.fnOpCommSwap ⟩
                step n + ℕ≤.≤-diff sn≤m
              ≃⟨ ℕ≤.≤-elim-diff sn≤m ⟩
                m
              ≃˘⟨ n≃m ⟩
                n
              ≃˘⟨ AA.ident ⟩
                n + 0
              ∎
         in contra (AA.cancel n+sd≃n+0) ℕ.step≄zero
   in ℕ<.<-intro-≤≄ n≤m n≄m
