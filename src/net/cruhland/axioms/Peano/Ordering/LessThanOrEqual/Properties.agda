import net.cruhland.axioms.AbstractAlgebra as AA
open import net.cruhland.axioms.Eq as Eq using (_≃_)
open Eq.≃-Reasoning
open import net.cruhland.axioms.NewOrd using (_≤_; _≰_)
open import net.cruhland.axioms.Operators using (_+_)
open import net.cruhland.axioms.Peano.Addition using (Addition)
open import net.cruhland.axioms.Peano.Base
  using () renaming (Peano to PeanoBase)
open import net.cruhland.axioms.Peano.Sign using (Sign)
open import net.cruhland.models.Function using (_∘_)
open import net.cruhland.models.Literals
open import net.cruhland.models.Logic using
  (∧-intro; contra; Dec; dec-map; no; yes)

module net.cruhland.axioms.Peano.Ordering.LessThanOrEqual.Properties
    (PB : PeanoBase) (PS : Sign PB) (PA : Addition PB PS) where

private module ℕ+ = Addition PA
private open module ℕ = PeanoBase PB using (ℕ; step)
import net.cruhland.axioms.Peano.Inspect PB as ℕI
import net.cruhland.axioms.Peano.Literals PB as ℕLit
import net.cruhland.axioms.Peano.Ordering.LessThanOrEqual.Base PB PS PA as ℕ≤

record LessThanOrEqualProperties : Set₁ where
  field
    {{lessThanOrEqualBase}} : ℕ≤.LteBase
    {{≤-transititve}} : Eq.Transitive _≤_
    {{≤-antisymmetric}} : AA.Antisymmetric _≤_
    {{injective-step}} : AA.Injective step _≤_ _≤_
    {{+-substitutive₂²-≤}} : AA.Substitutive₂² _+_ _≤_ _≤_
    {{cancellativeᴸ-+}} : AA.Cancellative AA.handᴸ _+_ _≤_
    {{cancellativeᴿ-+}} : AA.Cancellative AA.handᴿ _+_ _≤_

    ≤-from-≃ : {n m : ℕ} → n ≃ m → n ≤ m
    n≤sn : {n : ℕ} → n ≤ step n
    _≤?_ : (n m : ℕ) → Dec (n ≤ m)

module _ {{_ : ℕ≤.LteBase}} where

  private
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

      injective-step : AA.Injective step _≤_ _≤_
      injective-step = AA.injective s≤s→≤
        where
          s≤s→≤ : ∀ {n m} → step n ≤ step m → n ≤ m
          s≤s→≤ {n} {m} sn≤sm =
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

      +-substitutiveᴸ : AA.Substitutive₂ AA.handᴸ _+_ _≤_ _≤_
      +-substitutiveᴸ = AA.substitutive₂ ≤-subst-+ᴸ
        where
          ≤-subst-+ᴸ : {a b c : ℕ} → a ≤ b → a + c ≤ b + c
          ≤-subst-+ᴸ {a} {b} {c} a≤b =
            let d = ℕ≤.diff a≤b
                a+d≃b = ℕ≤.≤-elim-diff a≤b
                a+c+d≃b+c =
                  begin
                    a + c + d
                  ≃⟨ AA.substᴿ-with-assoc AA.comm ⟩
                    a + d + c
                  ≃⟨ AA.subst₂ a+d≃b ⟩
                    b + c
                  ∎
             in ℕ≤.≤-intro-diff a+c+d≃b+c

      +-substitutiveᴿ : AA.Substitutive₂ AA.handᴿ _+_ _≤_ _≤_
      +-substitutiveᴿ = AA.substitutive₂ ≤-subst-+ᴿ
        where
          ≤-subst-+ᴿ : {a b c : ℕ} → a ≤ b → c + a ≤ c + b
          ≤-subst-+ᴿ {a} {b} {c} a≤b =
            let d = ℕ≤.diff a≤b
                a+d≃b = ℕ≤.≤-elim-diff a≤b
                c+a+d≃c+b =
                  begin
                    c + a + d
                  ≃⟨ AA.assoc ⟩
                    c + (a + d)
                  ≃⟨ AA.subst₂ a+d≃b ⟩
                    c + b
                  ∎
             in ℕ≤.≤-intro-diff c+a+d≃c+b

      +-substitutive₂²-≤ : AA.Substitutive₂² _+_ _≤_ _≤_
      +-substitutive₂²-≤ = AA.substitutive₂²

      cancellativeᴸ-+ : AA.Cancellative AA.handᴸ _+_ _≤_
      cancellativeᴸ-+ = AA.cancellative λ {a b c} → ≤-cancel-+ᴸ
        where
          ≤-cancel-+ᴸ : ∀ {a b c} → c + a ≤ c + b → a ≤ b
          ≤-cancel-+ᴸ {a} {b} {c} c+a≤c+b =
            let d = ℕ≤.diff c+a≤c+b
                c+a+d≃c+b = ℕ≤.≤-elim-diff c+a≤c+b
                c+[a+d]≃c+b =
                  begin
                    c + (a + d)
                  ≃˘⟨ AA.assoc ⟩
                    c + a + d
                  ≃⟨ c+a+d≃c+b ⟩
                    c + b
                  ∎
                a+d≃b = AA.cancel c+[a+d]≃c+b
             in ℕ≤.≤-intro-diff a+d≃b

      cancellativeᴿ-+ : AA.Cancellative AA.handᴿ _+_ _≤_
      cancellativeᴿ-+ = AA.cancellative λ {a b c} → ≤-cancel-+ᴿ
        where
          ≤-cancel-+ᴿ : ∀ {a b c} → a + c ≤ b + c → a ≤ b
          ≤-cancel-+ᴿ {a} {b} {c} a+c≤b+c =
            let d = ℕ≤.diff a+c≤b+c
                a+c+d≃b+c = ℕ≤.≤-elim-diff a+c≤b+c
                a+d+c≃b+c =
                  begin
                    a + d + c
                  ≃⟨ AA.substᴿ-with-assoc AA.comm ⟩
                    a + c + d
                  ≃⟨ a+c+d≃b+c ⟩
                    b + c
                  ∎
                a+d≃b = AA.cancel a+d+c≃b+c
             in ℕ≤.≤-intro-diff a+d≃b

  ≤-from-≃ : {n m : ℕ} → n ≃ m → n ≤ m
  ≤-from-≃ n≃m = AA.subst₂ n≃m Eq.refl

  n≤sn : {n : ℕ} → n ≤ step n
  n≤sn = ℕ≤.≤-step Eq.refl

  _≤?_ : (n m : ℕ) → Dec (n ≤ m)
  _≤?_ n m = ℕ.ind P P0 Ps n m
    where
      P = λ x → ∀ y → Dec (x ≤ y)
      P0 = λ y → yes ℕ≤.0≤n

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

  properties-from-base : LessThanOrEqualProperties
  properties-from-base =
    record { ≤-from-≃ = ≤-from-≃ ; n≤sn = n≤sn ; _≤?_ = _≤?_ }
