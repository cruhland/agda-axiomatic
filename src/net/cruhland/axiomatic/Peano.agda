module net.cruhland.axiomatic.Peano where

open import net.cruhland.axiomatic.Peano.Addition using (Addition)
open import net.cruhland.axiomatic.Peano.Base using (Peano)
open import net.cruhland.axiomatic.Peano.Exponentiation using (Exponentiation)
import net.cruhland.axiomatic.Peano.Literals as Literals
open import net.cruhland.axiomatic.Peano.Multiplication using (Multiplication)
import net.cruhland.axiomatic.Peano.Ordering as Ordering

-- Bundle all child modules together for convenience
record PeanoArithmetic : Set₁ where
  field
    PB : Peano
    PA : Addition PB
    PM : Multiplication PB PA
    PE : Exponentiation PB PA PM

  open Addition PA public
  open Exponentiation PE public
  open Literals PB public
  open Multiplication PM public
  open Ordering PB PA public
  open Peano PB public
