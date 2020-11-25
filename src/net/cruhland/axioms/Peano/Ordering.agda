open import net.cruhland.axioms.Peano.Addition
  using () renaming (Addition to PeanoAddition)
open import net.cruhland.axioms.Peano.Base
  using () renaming (Peano to PeanoBase)

module net.cruhland.axioms.Peano.Ordering
    (PB : PeanoBase) (PA : PeanoAddition PB) where

-- Export contents of all child modules
open import net.cruhland.axioms.Peano.Ordering.LessThan PB PA public
open import net.cruhland.axioms.Peano.Ordering.LessThanOrEqual PB PA public
