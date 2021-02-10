import net.cruhland.axioms.AbstractAlgebra as AA
open import net.cruhland.axioms.DecEq using (DecEq)
open import net.cruhland.axioms.Eq as Eq using (_≃_)
open import net.cruhland.axioms.NewOrd using (_≤_; _<_; _>_; BaseOrd)
open import net.cruhland.axioms.Operators using (_+_; -_; _-_; _*_)
open import net.cruhland.axioms.Peano using (PeanoArithmetic)
import net.cruhland.axioms.Sign as Sign
open import net.cruhland.models.Literals

module net.cruhland.models.Integers.NewOrd (PA : PeanoArithmetic) where
import net.cruhland.models.Integers.Addition PA as ℤ+
open import net.cruhland.models.Integers.Base PA using (ℤ)
import net.cruhland.models.Integers.Equality PA as ℤ≃
import net.cruhland.models.Integers.Literals PA as ℤLit
import net.cruhland.models.Integers.Multiplication PA as ℤ*
import net.cruhland.models.Integers.Negation PA as ℤ-

-- Define a "top-level" record that contains all properties of _≤_ and
-- _<_ that we want to have.
record AllOrd : Set₁ where
  field
    {{baseOrd}} : BaseOrd ℤ
    {{positivity}} : Sign.Positivity 0
    {{≤-transitive}} : Eq.Transitive _≤_
    {{<-transitive}} : Eq.Transitive _<_
    {{≤-antisymmetric}} : AA.Antisymmetric _≤_
    {{trichotomy}} : {a b : ℤ} → AA.ExactlyOneOfThree (a < b) (a ≃ b) (a > b)
    {{decEq}} : DecEq ℤ  -- Maybe this should go somewhere else?

    {{<-substitutive₂²}} : AA.Substitutive₂² _+_ _<_ _<_
    {{+-preserves-pos}} : AA.Preserves {A = ℤ} Sign.Positive _+_

    <-intro-pos : {a b : ℤ} → Sign.Positive (b - a) → a < b
    <-elim-pos : {a b : ℤ} → a < b → Sign.Positive (b - a)
    <-reverse-neg : {a b : ℤ} → a < b → - b < - a

    <-substitutive₂-*ᴸ : {a b c : ℤ} → Sign.Positive c → a < b → a * c < b * c
    <-substitutive₂-*ᴿ : {a b c : ℤ} → Sign.Positive c → a < b → c * a < c * b
    {{*-preserves-pos}} : AA.Preserves {A = ℤ} Sign.Positive _*_

-- Then, define "minimal" records that start with a small number of
-- fields and define all of the others; show that the top-level record
-- can be defined from them.

-- Finally, define concrete data types that can satisfy the minimal
-- records. This shows that all the properties of _≤_ and _<_ can come
-- from a small set of definitions.
