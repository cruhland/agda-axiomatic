module net.cruhland.models.Setoid where

open import Level using (0ℓ) renaming (suc to sℓ)

-- Export standard library definitions
open import Relation.Binary public using (DecSetoid; module DecSetoid; Setoid)
open Setoid public using () renaming (Carrier to El)

Setoid₀ : Set (sℓ 0ℓ)
Setoid₀ = Setoid 0ℓ 0ℓ

DecSetoid₀ : Set (sℓ 0ℓ)
DecSetoid₀ = DecSetoid 0ℓ 0ℓ
