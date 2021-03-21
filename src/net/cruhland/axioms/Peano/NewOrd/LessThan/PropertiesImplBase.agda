open import net.cruhland.axioms.NewOrd using (_<_; _≮_)
open import net.cruhland.axioms.Peano.Addition using (Addition)
open import net.cruhland.axioms.Peano.Base
  using () renaming (Peano to PeanoBase)
open import net.cruhland.axioms.Peano.NewOrd.LessThan.BaseDecl using (LtBase)
open import net.cruhland.axioms.Peano.NewOrd.LessThanOrEqual.BaseDecl using
  (LteBase)
import net.cruhland.axioms.Peano.NewOrd.LessThanOrEqual.PropertiesImplBase
  as LteProps
open import net.cruhland.axioms.Peano.Sign using (Sign)
open import net.cruhland.models.Literals
open import net.cruhland.models.Logic using (∧-intro; contra)

module net.cruhland.axioms.Peano.NewOrd.LessThan.PropertiesImplBase
  (PB : PeanoBase)
  (PS : Sign PB)
  (PA : Addition PB PS)
  (LTEB : LteBase PB PS PA)
  (LTB : LtBase PB PS PA LTEB) where

module ℕ+ = Addition PA
open PeanoBase PB using (ℕ; step)
import net.cruhland.axioms.Peano.Literals PB as ℕL
module ℕ< = LtBase LTB
module ℕ≤ = LteBase LTEB
module ℕ≤P = LteProps PB PS PA LTEB

n<sn : {n : ℕ} → n < step n
n<sn = ℕ<.<-intro-≤≄ ℕ≤P.n≤sn ℕ+.n≄sn

n≮0 : {n : ℕ} → n ≮ 0
n≮0 n<0 =
  let n≤0 = ℕ<.<-elim-≤ n<0
      n≄0 = ℕ<.<-elim-≄ n<0
      n+d≃0 = ℕ≤.≤-elim-diff n≤0
      ∧-intro n≃0 _ = ℕ+.+-both-zero n+d≃0
   in contra n≃0 n≄0
