import net.cruhland.axioms.AbstractAlgebra as AA
open import net.cruhland.axioms.Eq as Eq using (_≃_; _≄_)
open Eq.≃-Reasoning
open import net.cruhland.axioms.NewOrd using (_≤_; _<_; _>_)
open import net.cruhland.axioms.Operators using (_+_)
open import net.cruhland.axioms.Peano.Addition using (Addition)
open import net.cruhland.axioms.Peano.Base
  using () renaming (Peano to PeanoBase)
open import net.cruhland.axioms.Peano.NewOrd.LessThan.BaseDecl using (LtBase)
open import net.cruhland.axioms.Peano.NewOrd.LessThan.PropertiesDecl
  using (LtProperties)
open import net.cruhland.axioms.Peano.NewOrd.LessThanOrEqual.BaseDecl
  using (LteBase)
open import net.cruhland.axioms.Peano.NewOrd.LessThanOrEqual.PropertiesDecl
  using (LteProperties)
open import net.cruhland.axioms.Peano.Sign using (Sign)
open import net.cruhland.models.Function using (_∘_)
open import net.cruhland.models.Literals
open import net.cruhland.models.Logic using
  (_∨_; ∨-comm; ∨-introᴸ; ∨-introᴿ; ∨-mapᴸ; ∨-mapᴿ; ¬_; contra; Dec; dec-map)

module net.cruhland.axioms.Peano.NewOrd.PropertiesImpl
  (PB : PeanoBase)
  (PS : Sign PB)
  (PA : Addition PB PS)
  (LTEB : LteBase PB PS PA)
  (LTEP : LteProperties PB PS PA LTEB)
  (LTB : LtBase PB PS PA LTEB)
  (LTP : LtProperties PB PS PA LTEB LTB)
  where

private module ℕ+ = Addition PA
private open module ℕ = PeanoBase PB using (ℕ; step)
import net.cruhland.axioms.Peano.Inspect PB as ℕI
import net.cruhland.axioms.Peano.Literals PB as ℕL
private module ℕ< = LtBase LTB
private module ℕ≤ = LteBase LTEB
private open module ℕ≤P = LteProperties LTEP using (_≤?_)
private module ℕ<P = LtProperties LTP

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

order-trichotomy : {n m : ℕ} → AA.ExactlyOneOfThree (n < m) (n ≃ m) (n > m)
order-trichotomy = record { at-least-one = 1of3 ; at-most-one = ¬2of3 }
  where
    1of3 : {n m : ℕ} → AA.OneOfThree (n < m) (n ≃ m) (n > m)
    1of3 {n} {m} = ℕ.ind P P0 Ps n
      where
        P = λ x → AA.OneOfThree (x < m) (x ≃ m) (x > m)

        P0 : P 0
        P0 with ℕI.case m
        ... | ℕI.case-zero m≃0 =
            AA.2nd (Eq.sym m≃0)
        ... | ℕI.case-step (ℕI.pred-intro p m≃sp) =
            AA.1st (ℕ<.<-intro-≤≄ ℕ≤.≤-zeroᴸ 0≄m)
          where 0≄m = λ 0≃m → ℕ.step≄zero (Eq.sym (Eq.trans 0≃m m≃sp))

        Ps : ℕ.step-case P
        Ps {k} (AA.1st k<m) with ≤-split (s≤-from-< k<m)
        ... | ∨-introᴸ sk<m = AA.1st sk<m
        ... | ∨-introᴿ sk≃m = AA.2nd sk≃m
        Ps {k} (AA.2nd k≃m) =
          let sm≃sk = AA.subst₁ (Eq.sym k≃m)
           in AA.3rd (<-from-s≤ (ℕ≤P.≤-intro-≃ sm≃sk))
        Ps (AA.3rd k>m) =
          AA.3rd (Eq.trans k>m ℕ<P.n<sn)

    ¬2of3 : {n m : ℕ} → ¬ AA.TwoOfThree (n < m) (n ≃ m) (n > m)
    ¬2of3 (AA.1∧2 n<m n≃m) =
      contra n≃m (ℕ<.<-elim-≄ n<m)
    ¬2of3 (AA.1∧3 n<m m<n) =
      let n≤m = ℕ<.<-elim-≤ n<m
          m≤n = ℕ<.<-elim-≤ m<n
          n≄m = ℕ<.<-elim-≄ n<m
       in contra (AA.antisym n≤m m≤n) n≄m
    ¬2of3 (AA.2∧3 n≃m m<n) =
      contra (Eq.sym n≃m) (ℕ<.<-elim-≄ m<n)

≤s-split : ∀ {n m} → n ≤ step m → n ≤ m ∨ n ≃ step m
≤s-split {n} {m} n≤sm =
  ∨-mapᴸ (AA.inject ∘ s≤-from-<) (≤-split n≤sm)

<s-split : ∀ {n m} → n < step m → n < m ∨ n ≃ m
<s-split {n} {m} = ≤-split ∘ AA.inject ∘ s≤-from-<

_<?_ : ∀ n m → Dec (n < m)
n <? m = dec-map <-from-s≤ s≤-from-< (step n ≤? m)

strong-ind :
  (P : ℕ → Set) (b : ℕ) →
  (∀ m → b ≤ m → (∀ k → b ≤ k → k < m → P k) → P m) → ∀ n → b ≤ n → P n
strong-ind P b Pm n b≤n = Pm n b≤n (ℕ.ind Q Q0 Qs n)
  where
    Q = λ x → ∀ j → b ≤ j → j < x → P j
    Q0 = λ j b≤j j<0 → contra j<0 ℕ<P.n≮0

    Q-subst : ∀ {x₁ x₂} → x₁ ≃ x₂ → Q x₁ → Q x₂
    Q-subst x₁≃x₂ Qx₁ j b≤j j<x₂ = Qx₁ j b≤j (AA.subst₂ (Eq.sym x₁≃x₂) j<x₂)

    Qs : ℕ.step-case Q
    Qs Qk j b≤j j<sk with <s-split j<sk
    ... | ∨-introᴸ j<k = Qk j b≤j j<k
    ... | ∨-introᴿ j≃k = Pm j b≤j (Q-subst (Eq.sym j≃k) Qk)
