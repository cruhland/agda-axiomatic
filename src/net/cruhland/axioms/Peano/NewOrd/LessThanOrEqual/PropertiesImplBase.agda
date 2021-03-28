import net.cruhland.axioms.AbstractAlgebra as AA
open import net.cruhland.axioms.Eq as Eq using (_≃_)
open Eq.≃-Reasoning
open import net.cruhland.axioms.NewOrd using (_≤_; _≰_)
open import net.cruhland.axioms.Operators using (_+_)
open import net.cruhland.axioms.Peano.Addition using (Addition)
open import net.cruhland.axioms.Peano.Base
  using () renaming (Peano to PeanoBase)
open import net.cruhland.axioms.Peano.NewOrd.LessThanOrEqual.BaseDecl using
  (LteBase)
open import net.cruhland.axioms.Peano.Sign using (Sign)
open import net.cruhland.models.Function using (_∘_; _⟨→⟩_)
open import net.cruhland.models.Literals
open import net.cruhland.models.Logic using
  (∧-intro; contra; Dec; dec-map; no; yes)

module net.cruhland.axioms.Peano.NewOrd.LessThanOrEqual.PropertiesImplBase
  (PB : PeanoBase)
  (PS : Sign PB)
  (PA : Addition PB PS)
  (LTEB : LteBase PB PS PA) where

private module ℕ+ = Addition PA
private open module ℕ = PeanoBase PB using (ℕ; step)
import net.cruhland.axioms.Peano.Inspect PB as ℕI
import net.cruhland.axioms.Peano.Literals PB as ℕL
private module ℕ≤ = LteBase LTEB

instance
  ≤-transitive : Eq.Transitive _≤_
  ≤-transitive = Eq.transitive ≤-trans
    where
      ≤-trans : {n m p : ℕ} → n ≤ m → m ≤ p → n ≤ p
      ≤-trans n≤m m≤p =
        let n+a≃m = ℕ≤.≤-elim-diff n≤m
            m+b≃p = ℕ≤.≤-elim-diff m≤p
         in ℕ≤.≤-intro-diff (AA.a[bc]-chain n+a≃m m+b≃p)

  ≤-antisymmetric : AA.Antisymmetric _≤_
  ≤-antisymmetric = AA.antisymmetric ≤-antisym
    where
      ≤-antisym : {n m : ℕ} → n ≤ m → m ≤ n → n ≃ m
      ≤-antisym {n} {m} n≤m m≤n =
        let a = ℕ≤.diff n≤m
            b = ℕ≤.diff m≤n
            n+a≃m = ℕ≤.≤-elim-diff n≤m
            m+b≃n = ℕ≤.≤-elim-diff m≤n
            n+a+b≃n+0 =
              begin
                n + (a + b)
              ≃⟨ AA.a[bc]-chain n+a≃m m+b≃n ⟩
                n
              ≃˘⟨ AA.ident ⟩
                n + 0
              ∎
            ∧-intro a≃0 _ = ℕ+.+-both-zero (AA.cancel n+a+b≃n+0)
         in begin
              n
            ≃˘⟨ AA.ident ⟩
              n + 0
            ≃˘⟨ AA.subst₂ a≃0 ⟩
              n + a
            ≃⟨ n+a≃m ⟩
              m
            ∎

  ≤-substitutive-≃ᴸ : AA.Substitutive₂ AA.handᴸ _≤_ _≃_ _⟨→⟩_
  ≤-substitutive-≃ᴸ = AA.substitutive₂ ≤-substᴸ
    where
      ≤-substᴸ : {n₁ n₂ m : ℕ} → n₁ ≃ n₂ → n₁ ≤ m → n₂ ≤ m
      ≤-substᴸ {n₁} {n₂} {m} n₁≃n₂ n₁≤m =
        let d = ℕ≤.diff n₁≤m
            n₁+d≃m = ℕ≤.≤-elim-diff n₁≤m
            n₂+d≃m =
              begin
                n₂ + d
              ≃˘⟨ AA.subst₂ n₁≃n₂ ⟩
                n₁ + d
              ≃⟨ n₁+d≃m ⟩
                m
              ∎
         in ℕ≤.≤-intro-diff n₂+d≃m

  ≤-substitutive-≃ᴿ : AA.Substitutive₂ AA.handᴿ _≤_ _≃_ _⟨→⟩_
  ≤-substitutive-≃ᴿ = AA.substitutive₂ ≤-substᴿ
    where
      ≤-substᴿ : {n₁ n₂ m : ℕ} → n₁ ≃ n₂ → m ≤ n₁ → m ≤ n₂
      ≤-substᴿ n₁≃n₂ m≤n₁ =
        let d = ℕ≤.diff m≤n₁
            m+d≃n₁ = ℕ≤.≤-elim-diff m≤n₁
         in ℕ≤.≤-intro-diff (Eq.trans m+d≃n₁ n₁≃n₂)

  ≤-substitutive-≃ : AA.Substitutive₂² _≤_ _≃_ _⟨→⟩_
  ≤-substitutive-≃ = AA.substitutive₂²

  ≤-injective-step : AA.Injective step _≤_ _≤_
  ≤-injective-step = AA.injective ≤-inject
    where
      ≤-inject : {n m : ℕ} → step n ≤ step m → n ≤ m
      ≤-inject {n} {m} sn≤sm =
        let d = ℕ≤.diff sn≤sm
            sn+d≃sm = ℕ≤.≤-elim-diff sn≤sm
            s[n+d]≃sm =
              begin
                step (n + d)
              ≃⟨ AA.fnOpComm ⟩
                step n + d
              ≃⟨ sn+d≃sm ⟩
                step m
              ∎
         in ℕ≤.≤-intro-diff (AA.inject s[n+d]≃sm)

  ≤-substitutive-+ᴸ : AA.Substitutive₂ AA.handᴸ _+_ _≤_ _≤_
  ≤-substitutive-+ᴸ = AA.substitutive₂ ≤-subst-+ᴸ
    where
      ≤-subst-+ᴸ : {n₁ n₂ m : ℕ} → n₁ ≤ n₂ → n₁ + m ≤ n₂ + m
      ≤-subst-+ᴸ {n₁} {n₂} {m} n₁≤n₂ =
        let d = ℕ≤.diff n₁≤n₂
            n₁+d≃n₂ = ℕ≤.≤-elim-diff n₁≤n₂
            n₁+m+d≃n₂+m =
              begin
                n₁ + m + d
              ≃⟨ AA.substᴿ-with-assoc AA.comm ⟩
                n₁ + d + m
              ≃⟨ AA.subst₂ n₁+d≃n₂ ⟩
                n₂ + m
              ∎
         in ℕ≤.≤-intro-diff n₁+m+d≃n₂+m

  ≤-substitutive-+ᴿ : AA.Substitutive₂ AA.handᴿ _+_ _≤_ _≤_
  ≤-substitutive-+ᴿ = AA.substitutiveᴿ-from-substitutiveᴸ
    where instance +-swappable = AA.swappable-from-commutative

  ≤-substitutive-+ : AA.Substitutive₂² _+_ _≤_ _≤_
  ≤-substitutive-+ = AA.substitutive₂²

  ≤-cancellative-+ᴸ : AA.Cancellative AA.handᴸ _+_ _≤_
  ≤-cancellative-+ᴸ = AA.cancellative λ {n₁ n₂ m} → ≤-cancelᴸ
    where
      ≤-cancelᴸ : {n₁ n₂ m : ℕ} → m + n₁ ≤ m + n₂ → n₁ ≤ n₂
      ≤-cancelᴸ m+n₁≤m+n₂ =
        let d = ℕ≤.diff m+n₁≤m+n₂
            m+n₁+d≃m+n₂ = ℕ≤.≤-elim-diff m+n₁≤m+n₂
            m+[n₁+d]≃m+n₂ = Eq.trans (Eq.sym AA.assoc) m+n₁+d≃m+n₂
         in ℕ≤.≤-intro-diff (AA.cancel m+[n₁+d]≃m+n₂)

  ≤-cancellative-+ᴿ : AA.Cancellative AA.handᴿ _+_ _≤_
  ≤-cancellative-+ᴿ = AA.cancellativeᴿ-from-cancellativeᴸ
    where instance +-swap = AA.swappable-from-commutative

  ≤-cancellative-+ : AA.Cancellative² _+_ _≤_
  ≤-cancellative-+ = AA.cancellative²

≤-intro-≃ : {n m : ℕ} → n ≃ m → n ≤ m
≤-intro-≃ n≃m = AA.subst₂ n≃m Eq.refl

n≤sn : {n : ℕ} → n ≤ step n
n≤sn = ℕ≤.≤-widenᴿ Eq.refl

≤-widenᴸ : {n m : ℕ} → step n ≤ m → n ≤ m
≤-widenᴸ = AA.inject ∘ ℕ≤.≤-widenᴿ

_≤?_ : (n m : ℕ) → Dec (n ≤ m)
_≤?_ n m = ℕ.ind P P0 Ps n m
  where
    P = λ x → ∀ y → Dec (x ≤ y)
    P0 = λ y → yes ℕ≤.≤-zeroᴸ

    Ps : ℕ.step-case P
    Ps {k} k≤?y y with ℕI.case y
    ... | ℕI.case-zero y≃0 = no sk≰y
      where
        sk≰y : step k ≰ y
        sk≰y sk≤y =
          let d = ℕ≤.diff sk≤y
              sk+d≃y = ℕ≤.≤-elim-diff sk≤y
              s[k+d]≃0 =
                begin
                  step (k + d)
                ≃⟨ AA.fnOpComm ⟩
                  step k + d
                ≃⟨ sk+d≃y ⟩
                  y
                ≃⟨ y≃0 ⟩
                  0
                ∎
           in contra s[k+d]≃0 ℕ.step≄zero
    ... | ℕI.case-step (ℕI.pred-intro j y≃sj) =
      let k≤j→sk≤y = AA.subst₂ (Eq.sym y≃sj) ∘ AA.subst₁
          sk≤y→k≤j = AA.inject ∘ AA.subst₂ y≃sj
       in dec-map k≤j→sk≤y sk≤y→k≤j (k≤?y j)
