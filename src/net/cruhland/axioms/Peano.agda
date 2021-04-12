module net.cruhland.axioms.Peano where

open import net.cruhland.axioms.Peano.Addition using (Addition)
open import net.cruhland.axioms.Peano.Base using (Peano)
open import net.cruhland.axioms.Peano.Exponentiation using (Exponentiation)
import net.cruhland.axioms.Peano.Inspect as Inspect
import net.cruhland.axioms.Peano.Literals as Literals
open import net.cruhland.axioms.Peano.Multiplication using (Multiplication)
open import net.cruhland.axioms.Peano.NewOrd using (Ordering)
open import net.cruhland.axioms.Peano.Sign using (Sign)

-- Bundle all child modules together for convenience
record PeanoArithmetic : Set₁ where
  field
    PB : Peano
    PS : Sign PB
    PA : Addition PB PS
    PO : Ordering PB PS PA
    PM : Multiplication PB PS PA PO
    PE : Exponentiation PB PS PA PO PM

  open Addition PA public
  open Exponentiation PE public
  open Inspect PB public
  open Literals PB public
  open Multiplication PM public
  open Ordering PO public
  open Peano PB public
  open Sign PS public
