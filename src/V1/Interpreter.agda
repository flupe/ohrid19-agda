-- Interpreter for WHILE language.

-- As computation is not guaranteed to terminate,
-- execution of statements is placed in the Delay monad.

module V1.Interpreter where

open import Library
open import V1.WellTypedSyntax
open import V1.Value
open Integer using (_div'_)

eq : (a : Type) → Val a → Val a → Val bool
eq bool true true = true
eq bool false false = true
eq bool _ _ = false
eq int x y = case x == y of λ where true → true
                                    false → false

-- Evaluation of expressions in fixed environment ρ.

eval : ∀{t} (e : Exp t) → Val t
eval (eInt  i)        = i
eval (eBool b)        = b
eval (ePlus e₁ e₂)    = eval e₁ + eval e₂
eval (eGt  e₁ e₂)     = iGt (eval e₁) (eval e₂)
eval (eAnd e₁ e₂)     = case eval e₁ of λ where
                          true  → eval e₂
                          false → false
eval (eCond e₁ e₂ e₃) = case eval e₁ of λ where
                          true  → eval e₂
                          false → eval e₃
eval (eMinus e₁ e₂)   = eval e₁ - eval e₂
eval (eMul e₁ e₂)     =  eval e₁ * eval e₂
eval (eDiv e₁ e₂)     =  eval e₁ div' eval e₂
eval (eNot e)         = case eval e of λ where
                          true → false
                          false → true
eval (eOr e₁ e₂)      = case eval e₁ of λ where
                          true → true
                          false → eval e₂
eval (eEq {a} e₁ e₂) = eq a (eval e₁) (eval e₂)

-- Execution of the program (main loop).

runProgram : (prg : Program) → ℤ
runProgram (program e) =
  -- Evaluate the main expression to yield result.
  eval e
