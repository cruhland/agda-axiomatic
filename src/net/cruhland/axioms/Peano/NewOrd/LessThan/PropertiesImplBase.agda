import net.cruhland.axioms.AbstractAlgebra as AA
import net.cruhland.axioms.Eq as Eq
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

instance
  <-transitive : Eq.Transitive _<_
  <-transitive = Eq.transitive <-trans
    where
      <-trans : {n m k : ℕ} → n < m → m < k → n < k
      <-trans n<m m<k =
        let n≤m = ℕ<.<-elim-≤ n<m
            m≤k = ℕ<.<-elim-≤ m<k
            n≤k = Eq.trans n≤m m≤k
            pos[d[n<m]] = ℕ<.<-diff-pos n<m
            pos[d[n≤m]] = AA.subst₁ (ℕ<.<-diff-from-≤-diff n<m) pos[d[n<m]]
            pos[d[n≤m]+d[m≤k]] = ℕ+.+-positive pos[d[n≤m]]
            d[n≤m]+d[m≤k]≃d[n≤k] = Eq.sym (ℕ≤P.diff-trans n≤m m≤k)
            pos[d[n≤k]] = AA.subst₁ d[n≤m]+d[m≤k]≃d[n≤k] pos[d[n≤m]+d[m≤k]]
         in ℕ<.<-intro-≤pd n≤k pos[d[n≤k]]

n<sn : {n : ℕ} → n < step n
n<sn = ℕ<.<-intro-≤≄ ℕ≤P.n≤sn ℕ+.n≄sn

n≮0 : {n : ℕ} → n ≮ 0
n≮0 n<0 =
  let n≤0 = ℕ<.<-elim-≤ n<0
      n≄0 = ℕ<.<-elim-≄ n<0
      n+d≃0 = ℕ≤.≤-elim-diff n≤0
      ∧-intro n≃0 _ = ℕ+.+-both-zero n+d≃0
   in contra n≃0 n≄0
