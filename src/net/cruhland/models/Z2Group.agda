module net.cruhland.models.Z2Group where

import net.cruhland.axioms.AbstractAlgebra as AA
import net.cruhland.axioms.Eq as Eq

open import net.cruhland.axioms.CoreAlgebra.Monoid using (Monoid)
open import net.cruhland.models.Function using (const)
open import net.cruhland.models.Logic using (⊤)
open import net.cruhland.axioms.Operators using (Star; star; _*_)
open import Relation.Binary.PropositionalEquality as PropEq using (_≡_; cong )

data Z2Set : Set where
  ee : Z2Set
  aa : Z2Set

groupOperation : Z2Set → Z2Set → Z2Set
groupOperation ee ee = ee
groupOperation ee aa = aa
groupOperation aa ee = aa
groupOperation aa aa = ee

_⊕_ : Z2Set → Z2Set → Z2Set
_⊕_ = groupOperation

groupIdentity : Z2Set
groupIdentity = ee

Z2Invert_ : Z2Set → Z2Set 
Z2Invert_ = λ x → x
  
instance
  ≡-reflexive : Eq.Reflexive _≡_
  ≡-reflexive = Eq.reflexive {A = Z2Set} PropEq.refl

  ≡-symmetric : Eq.Symmetric _≡_
  ≡-symmetric = Eq.symmetric {A = Z2Set} PropEq.sym

  ≡-transitive : Eq.Transitive _≡_
  ≡-transitive = Eq.transitive {A = Z2Set} PropEq.trans

  eq-Z2Set : Eq.Eq Z2Set
  eq-Z2Set = Eq.equivalence _≡_

  private
    opEqSubstᴸ : AA.Substitutive₂ AA.handᴸ _⊕_ _≡_ _≡_
    opEqSubstᴸ = AA.substitutive₂ λ {_ _ b} → cong (_⊕ b)

    opEqSubstᴿ : AA.Substitutive₂ AA.handᴿ _⊕_ _≡_ _≡_
    opEqSubstᴿ = AA.substitutive₂ λ {_ _ b} → cong (b ⊕_)

  opEqSubst : AA.Substitutive² _⊕_ _≡_ _≡_
  opEqSubst = AA.substitutive² {A = Z2Set}

  opAssociative : AA.Associative _⊕_
  opAssociative = record { assoc = opassoc }
    where
      opassoc : {a b c : Z2Set} → (a ⊕ b) ⊕ c ≡ a ⊕ (b ⊕ c)
      opassoc {ee} {ee} {ee} = PropEq.refl
      opassoc {ee} {ee} {aa} = PropEq.refl
      opassoc {ee} {aa} {ee} = PropEq.refl
      opassoc {ee} {aa} {aa} = PropEq.refl
      opassoc {aa} {ee} {ee} = PropEq.refl
      opassoc {aa} {ee} {aa} = PropEq.refl
      opassoc {aa} {aa} {ee} = PropEq.refl
      opassoc {aa} {aa} {aa} = PropEq.refl

  private
    ⊕-identityᴸ : AA.Identity AA.handᴸ _⊕_ ee
    ⊕-identityᴸ = AA.identity  ⊕-identᴸ
      where
        ⊕-identᴸ : {a : Z2Set} → ee ⊕ a ≡ a
        ⊕-identᴸ {ee} = PropEq.refl
        ⊕-identᴸ {aa} = PropEq.refl

    ⊕-identityᴿ : AA.Identity AA.handᴿ _⊕_ ee
    ⊕-identityᴿ = AA.identity ⊕-identᴿ
      where
        ⊕-identᴿ : {a : Z2Set} → a ⊕ ee ≡ a
        ⊕-identᴿ {ee} = PropEq.refl
        ⊕-identᴿ {aa} = PropEq.refl

  ⊕-identity : AA.Identity² _⊕_ ee
  ⊕-identity = AA.identity² {A = Z2Set}

  private
    neg-inverseᴸ : AA.Inverse AA.handᴸ (Z2Invert_) (const ⊤) _⊕_ ee
    neg-inverseᴸ = AA.inverse neg-invᴸ
      where
        neg-invᴸ : {x : Z2Set} → ((Z2Invert_) x) ⊕ x ≡ ee
        neg-invᴸ {ee} = PropEq.refl
        neg-invᴸ {aa} = PropEq.refl

    neg-inverseᴿ : AA.Inverse AA.handᴿ (Z2Invert_) (const ⊤) _⊕_ ee
    neg-inverseᴿ = AA.inverse neg-invᴿ
      where
        neg-invᴿ : {x : Z2Set} → ((Z2Invert_) x) ⊕ x ≡ ee
        neg-invᴿ {ee} = PropEq.refl
        neg-invᴿ {aa} = PropEq.refl

  neg-inverse : AA.Inverse² (Z2Invert_) (const ⊤) _⊕_ ee
  neg-inverse = AA.inverse²

Z2Moniod : (Monoid Z2Set)
Z2Moniod = record { _⊙_ = _⊕_
                  ; identity = groupIdentity }

open import net.cruhland.axioms.CoreAlgebra.Group Z2Set Z2Moniod using (Group)

Z2Group : Group 
Z2Group = record { invert_ = Z2Invert_ }
