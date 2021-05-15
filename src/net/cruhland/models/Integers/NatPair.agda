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
open import net.cruhland.axioms.Integers.Sign.BaseDecl PA using (SignBase)
open import net.cruhland.axioms.Integers.Sign.PropertiesDecl PA
  using (SignProperties)
import net.cruhland.axioms.Integers.Sign.PropertiesImplBase PA
  as SignPropertiesImplBase
open import net.cruhland.axioms.Integers.SignDecl PA using (Sign)
import net.cruhland.models.Integers.NatPair.AdditionImpl PA as AdditionImpl
import net.cruhland.models.Integers.NatPair.BaseImpl PA as BaseImpl
import net.cruhland.models.Integers.NatPair.Negation.BaseImpl PA
  as NegationBaseImpl
import net.cruhland.models.Integers.NatPair.Negation.PropertiesImpl PA
  as NegationPropertiesImpl
import net.cruhland.models.Integers.NatPair.SignBaseImplLt PA as SignBaseImplLt
import net.cruhland.models.Integers.NatPair.SignBaseImplNat PA
  as SignBaseImplNat

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

signBaseLt : SignBase base addition negation
signBaseLt = record { SignBaseImplLt }

signBaseNat : SignBase base addition negation
signBaseNat = record { SignBaseImplNat }

signBase : SignBase base addition negation
signBase = signBaseLt

signProperties : SignProperties base addition negation signBase
signProperties =
  record { SignPropertiesImplBase base addition negation signBase }

sign : Sign base addition negation
sign = record { SB = signBase ; SP = signProperties }

integers : Integers
integers = record { ZB = base ; Z+ = addition ; Z- = negation ; ZS = sign }
