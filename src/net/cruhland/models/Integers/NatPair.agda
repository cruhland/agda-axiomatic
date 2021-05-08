open import net.cruhland.axioms.Peano using (PeanoArithmetic)

module net.cruhland.models.Integers.NatPair (PA : PeanoArithmetic) where

open import net.cruhland.axioms.Integers PA using (Integers)
open import net.cruhland.axioms.Integers.AdditionDecl PA using (Addition)
open import net.cruhland.axioms.Integers.BaseDecl PA using (Base)
open import net.cruhland.axioms.Integers.NegationDecl PA using (Negation)
import net.cruhland.models.Integers.NatPair.AdditionImpl PA as AdditionImpl
import net.cruhland.models.Integers.NatPair.BaseImpl PA as BaseImpl
import net.cruhland.models.Integers.NatPair.NegationImpl PA as NegationImpl

base : Base
base = record { BaseImpl }

addition : Addition base
addition = record { AdditionImpl }

negation : Negation base
negation = record { NegationImpl }

integers : Integers
integers = record { ZB = base ; Z+ = addition ; Z- = negation }
