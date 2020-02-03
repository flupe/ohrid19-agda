-- Values and primitive operations; environments.

module V3.Value where

open import Library
open import V3.AST using (eqBoolean)
open import V3.WellTypedSyntax

-- Well-typed values.

Val : Type → Set
Val int    = ℤ
Val bool   = Boolean

instance
  PrintVal : ∀ {t} → Print (Val t)
  print {{PrintVal {int} }} i = print {{PrintInt}} i
  print {{PrintVal {bool}}} b = print {{PrintBoolean}} b

-- Well-typed Environments.

Env : Cxt → Set
Env = All Val

lookupEnv : ∀ {Γ t} → Env Γ → Var Γ t → Val t
lookupEnv (v ∷ ρ) here      = v
lookupEnv (v ∷ ρ) (there x) = lookupEnv ρ x

-- Semantics of operations.

-- Boolean negation.

bNot : Boolean → Boolean
bNot true  = false
bNot false = true

toBool : Boolean → Bool
toBool true = true
toBool false = false

-- Greater-than on integers.

iGt : (i j : ℤ) → Boolean
iGt i j = case i Integer.<= j of λ where
  false → true
  true  → false

instance
  eqVal : ∀{t} → Eq (Val t)
  _≟_ ⦃ eqVal {bool} ⦄ = _≟_ ⦃ eqBoolean ⦄
  _≟_ ⦃ eqVal {int} ⦄  = _≟_ ⦃ eqℤ ⦄
