-- Type checker for the WHILE language.

{-# OPTIONS --postfix-projections #-}

module V1.TypeChecker where

open import Library

import V1.AST as A
open import V1.WellTypedSyntax

-- Type errors.
--
-- Currently, these errors do not carry enough evidence that
-- something is wrong.  The type checker does not produce
-- evidence of ill-typedness in case of failure,
-- only of well-typedness in case of success.

data TypeError : Set where
  typeMismatch : (tinf texp : Type)  → tinf ≢ texp → TypeError

instance
  PrintError : Print TypeError
  print {{PrintError}} = λ where
    (typeMismatch tinf texp _) → String.concat $
      "type mismatch: expected " ∷ print texp ∷
      ", but inferred " ∷ print tinf ∷ []

-- Type error monad.

open ErrorMonad {E = TypeError}

-- Checking expressions
---------------------------------------------------------------------------

mutual

  -- Type inference.

  inferExp : (e : A.Exp) → Error (Σ Type (λ t → Exp t))
  inferExp (A.eInt i)  = return (int  , eInt  i)
  inferExp (A.eBool b) = return (bool , eBool b)
  inferExp (A.ePlus e₁ e₂) = do
    e₁' ← checkExp e₁ int
    e₂' ← checkExp e₂ int
    return (int , ePlus e₁' e₂')
  inferExp (A.eMinus e₁ e₂) = do
    e₁' ← checkExp e₁ int
    e₂' ← checkExp e₂ int
    return (int , eMinus e₁' e₂')
  inferExp (A.eMul e₁ e₂) = do
    e₁' ← checkExp e₁ int
    e₂' ← checkExp e₂ int
    return (int , eMul e₁' e₂')
  inferExp (A.eDiv e₁ e₂) = do
    e₁' ← checkExp e₁ int
    e₂' ← checkExp e₂ int
    return (int , eDiv e₁' e₂')
  inferExp (A.eGt   e₁ e₂) = do
    e₁' ← checkExp e₁ int
    e₂' ← checkExp e₂ int
    return (bool , eGt e₁' e₂')
  inferExp (A.eAnd  e₁ e₂) = do
    e₁' ← checkExp e₁ bool
    e₂' ← checkExp e₂ bool
    return (bool , eAnd e₁' e₂')
  inferExp (A.eCond e₁ e₂ e₃) = do
    e₁' ← checkExp e₁ bool
    (t , e₂') ← inferExp e₂
    e₃' ← checkExp e₃ t
    return (t , eCond e₁' e₂' e₃')
  inferExp (A.eNot e₁) = do
    e₁' ← checkExp e₁ bool
    return (bool , eNot e₁')
  inferExp (A.eOr e₁ e₂) = do
    e₁' ← checkExp e₁ bool
    e₂' ← checkExp e₂ bool
    return (bool , eOr e₁' e₂')
  inferExp (A.eEq e₁ e₂) = do
    (t₁ , e₁') ← inferExp e₁
    (t₂ , e₂') ← inferExp e₂
    case t₁ ≟ t₂ of λ where
      (yes refl) → return (bool , eEq e₁' e₂')
      (no t₁≢t₂) → throwError (typeMismatch t₁ t₂ t₁≢t₂)

  -- Type checking.
  -- Calls inference and checks inferred type against given type.

  checkExp : (e : A.Exp) (t : Type) → Error (Exp t)
  checkExp e t = do
    (t' , e') ← inferExp e
    case t' ≟ t of λ where
      (yes refl) → return e'
      (no  t'≢t) → throwError (typeMismatch t' t t'≢t)

-- Checking the program.
---------------------------------------------------------------------------

checkProgram : (prg : A.Program) → Error Program
checkProgram (A.program e) = do
  e' ← checkExp e int
  return $ program e'


-- -}
-- -}
-- -}
-- -}
-- -}
-- -}
