open import net.cruhland.axioms.Peano using (PeanoArithmetic)

module net.cruhland.models.Integers.NatPair (PA : PeanoArithmetic) where

open import net.cruhland.axioms.Integers PA using (Integers)
open import net.cruhland.axioms.Integers.AdditionDecl PA using (Addition)
open import net.cruhland.axioms.Integers.BaseDecl PA using (Base)
import net.cruhland.models.Integers.NatPair.AdditionImpl PA as AdditionImpl
import net.cruhland.models.Integers.NatPair.BaseImpl PA as BaseImpl

base : Base
base = record { BaseImpl }

addition : Addition base
addition = record { AdditionImpl }

integers : Integers
integers = record { ZB = base ; Z+ = addition }
