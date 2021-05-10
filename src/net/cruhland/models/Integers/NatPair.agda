open import net.cruhland.axioms.Peano using (PeanoArithmetic)

module net.cruhland.models.Integers.NatPair (PA : PeanoArithmetic) where

open import net.cruhland.axioms.Integers PA using (Integers)
open import net.cruhland.axioms.Integers.AdditionDecl PA using (Addition)
open import net.cruhland.axioms.Integers.BaseDecl PA using (Base)
open import net.cruhland.axioms.Integers.Negation.BaseDecl PA
  using (NegationBase)
open import net.cruhland.axioms.Integers.Negation.PropertiesDecl PA
  using (NegationProperties)
open import net.cruhland.axioms.Integers.NegationDecl PA using (Negation)
import net.cruhland.models.Integers.NatPair.AdditionImpl PA as AdditionImpl
import net.cruhland.models.Integers.NatPair.BaseImpl PA as BaseImpl
import net.cruhland.models.Integers.NatPair.Negation.BaseImpl PA
  as NegationBaseImpl
import net.cruhland.models.Integers.NatPair.Negation.PropertiesImpl PA
  as NegationPropertiesImpl

base : Base
base = record { BaseImpl }

addition : Addition base
addition = record { AdditionImpl }

negationBase : NegationBase base addition
negationBase = record { NegationBaseImpl }

negationProperties : NegationProperties base addition negationBase
negationProperties = record { NegationPropertiesImpl  }

negation : Negation base addition
negation = record { NB = negationBase ; NP = negationProperties }

integers : Integers
integers = record { ZB = base ; Z+ = addition ; Z- = negation }
