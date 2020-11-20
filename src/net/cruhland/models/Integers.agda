open import net.cruhland.axioms.Peano using (PeanoArithmetic)

module net.cruhland.models.Integers (PA : PeanoArithmetic) where

-- Export contents of all child modules
open import net.cruhland.models.Integers.Addition PA public
open import net.cruhland.models.Integers.Base PA public
open import net.cruhland.models.Integers.Equality PA public
open import net.cruhland.models.Integers.Literals PA public
open import net.cruhland.models.Integers.Multiplication PA public
open import net.cruhland.models.Integers.Negation PA public
open import net.cruhland.models.Integers.Ordering PA public
