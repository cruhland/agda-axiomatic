module net.cruhland.axioms.Peano where

open import net.cruhland.axioms.Peano.Addition using (Addition)
open import net.cruhland.axioms.Peano.Base using (Peano)
open import net.cruhland.axioms.Peano.Exponentiation using (Exponentiation)
import net.cruhland.axioms.Peano.Inspect as Inspect
import net.cruhland.axioms.Peano.Literals as Literals
open import net.cruhland.axioms.Peano.Multiplication using (Multiplication)
import net.cruhland.axioms.Peano.Ordering as Ordering

-- Bundle all child modules together for convenience
record PeanoArithmetic : Set₁ where
  field
    PB : Peano
    PA : Addition PB
    PM : Multiplication PB PA
    PE : Exponentiation PB PA PM

  open Addition PA public
  open Exponentiation PE public
  open Inspect PB public
  open Literals PB public
  open Multiplication PM public
  open Ordering PB PA public
  open Peano PB public
