import net.cruhland.axioms.AbstractAlgebra as AA
open import net.cruhland.axioms.Eq as Eq using (_≃_)
open import net.cruhland.axioms.NewOrd using (_≤_; _<_; _>_; _≮_; BaseOrd)
open import net.cruhland.axioms.Operators using (_+_)
open import net.cruhland.axioms.Peano.Addition using (Addition)
open import net.cruhland.axioms.Peano.Base
  using () renaming (Peano to PeanoBase)
open import net.cruhland.axioms.Peano.Sign using (Sign)
open import net.cruhland.models.Function using (_∘_; _⟨→⟩_; flip)
open import net.cruhland.models.Literals
open import net.cruhland.models.Logic using (_∨_; ∨-mapᴸ; ¬_; Dec)

module net.cruhland.axioms.Peano.NewOrd
  (PB : PeanoBase) (PS : Sign PB) (PA : Addition PB PS) where
open PeanoBase PB using (ℕ; step)
import net.cruhland.axioms.Peano.Literals PB as ℕLit

-- Define a "top-level" record that contains all properties of _≤_ and
-- _<_ that we want to have.
record AllOrd : Set₁ where
  field
    {{baseOrd}} : BaseOrd ℕ
    {{≤-reflexive}} : Eq.Reflexive _≤_
    {{≤-transititve}} : Eq.Transitive _≤_
    {{≤-antisymmetric}} : AA.Antisymmetric _≤_
    {{≤-substitutive₂²}} : AA.Substitutive₂² _≤_ _≃_ _⟨→⟩_
    {{<-transitive}} : Eq.Transitive _<_
    {{<-substitutive₂²}} : AA.Substitutive₂² _<_ _≃_ _⟨→⟩_
    {{trichotomy}} : {n m : ℕ} → AA.ExactlyOneOfThree (n < m) (n ≃ m) (n > m)
    ≤-from-< : {n m : ℕ} → n < m → n ≤ m
    ≤-from-≃ : {n m : ℕ} → n ≃ m → n ≤ m
    ≤-split : {n m : ℕ} → n ≤ m → n < m ∨ n ≃ m

    0≤n : {n : ℕ} → 0 ≤ n
    n≮0 : {n : ℕ} → n ≮ 0
    n≤sn : {n : ℕ} → n ≤ step n
    n<sn : {n : ℕ} → n < step n
    s≤-from-< : {n m : ℕ} → n < m → step n ≤ m
    <-from-s≤ : {n m : ℕ} → step n ≤ m → n < m
    ≤s-split : {n m : ℕ} → n ≤ step m → n ≤ m ∨ n ≃ step m
    <s-split : {n m : ℕ} → n < step m → n < m ∨ n ≃ m
    _≤?_ : (n m : ℕ) → Dec (n ≤ m)
    _<?_ : (n m : ℕ) → Dec (n < m)
    {{substitutive-step}} : AA.Substitutive₁ step _≤_ _≤_
    {{injective-step}} : AA.Injective step _≤_ _≤_

    {{+-substitutive₂²-≤}} : AA.Substitutive₂² _+_ _≤_ _≤_
    {{cancellativeᴸ-+}} : AA.Cancellative AA.handᴸ _+_ _≤_
    {{cancellativeᴿ-+}} : AA.Cancellative AA.handᴿ _+_ _≤_

    strong-ind :
      (P : ℕ → Set) (b : ℕ) →
        (∀ m → b ≤ m → (∀ k → b ≤ k → k < m → P k) → P m) →
          ∀ n → b ≤ n → P n

-- Then, define "minimal" records that start with a small number of
-- fields and define all of the others; show that the top-level record
-- can be defined from them.

-- Finally, define concrete data types that can satisfy the minimal
-- records. This shows that all the properties of _≤_ and _<_ can come
-- from a small set of definitions.
