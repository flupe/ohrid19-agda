-- Untyped interpreter for the WHILE language.
--
-- * Runs directly on the unchecked abstract syntax tree.
-- * May fail due to scope and other runtime errors.
-- * while loops may not terminate.

module V3.UntypedInterpreter where

open import Library
open import V3.AST

-- Untyped values.

data Val : Set where
  intV  : ℤ       → Val
  boolV : Boolean → Val

instance
  PrintVal : Print Val
  print {{PrintVal}} = λ where
    (intV i)  → print i
    (boolV b) → print b

  eqVal : Eq Val
  _≟_ ⦃ eqVal ⦄ (intV a) (intV b) = case a ≟ b of λ where
    (yes a≡b) → yes (cong intV a≡b)
    (no a≢b)  → no (a≢b ∘ λ where refl → refl)

  _≟_ ⦃ eqVal ⦄ (boolV a) (boolV b) = case a ≟ b of λ where
    (yes a≡b) → yes (cong boolV a≡b)
    (no a≢b)  → no (a≢b ∘ λ where refl → refl)

  _≟_ ⦃ eqVal ⦄ (intV a) (boolV b) = no λ ()
  _≟_ ⦃ eqVal ⦄ (boolV a) (intV b) = no λ ()

-- Poor man's environments (association list).

Env : Set
Env = List (Id × Val)

-- Looking up the value bound to a variable in an environment.

lookupId : Env → Id → Maybe Val
lookupId []             y = nothing
lookupId ((x , v) ∷ xs) y =
  if x == y
  then just v
  else lookupId xs y

-- Adding or updating a binding in the environment.

updateEnv : Id → Val → Env → Env
updateEnv x v []            = (x , v) ∷ []
updateEnv x v ((y , w) ∷ ρ) =
  if x == y
  then (x , v) ∷ ρ
  else (y , w) ∷ updateEnv x v ρ

-- -- Poor man's version, keeps history of bindings.
-- updateEnv x v ρ = (x , v) ∷ ρ
-- updateEnv : Id → Val → Env → Env

-- Semantics of operations.

-- Boolean negation.

bNot : Boolean → Boolean
bNot true = false
bNot false = true

-- Boolean conjunction.

bAnd : Boolean → Boolean → Boolean
bAnd true  b = b
bAnd false _ = false

-- Boolean conditional

bIf : {A : Set} → Boolean → A → A → A
bIf true  x y = x
bIf false x y = y

-- Greater-than on integers.

iGt : (i j : ℤ) → Boolean
iGt i j = case i Integer.<= j of λ where
  false → true
  true  → false

-- Evaluation of expressions.  The environment is fixed.

module EvalExp (ρ : Env) where

  -- Evaluation may fail due to scope or type errors, thus eval is partial.
  -- E.g. eval (eNot (eInt zero)) ≡ nothing.

  eval : Exp → Maybe Val
  eval (eId x)   = lookupId ρ x
  eval (eInt i)  = just (intV i)
  eval (eBool b) = just (boolV b)
  eval (ePlus e₁ e₂) = case (eval e₁ , eval e₂) of λ where
    (just (intV i) , just (intV j)) → just (intV (i + j))
    _ → nothing
  eval (eGt e₁ e₂) = case (eval e₁ , eval e₂) of λ where
    (just (intV i) , just (intV j)) → just (boolV (iGt i j))
    _ → nothing
  eval (eAnd e₁ e₂) = case (eval e₁ , eval e₂) of λ where
    (just (boolV b₁) , just (boolV b₂)) → just (boolV (bAnd b₁ b₂))
    _ → nothing
  eval (eCond e₁ e₂ e₃) = case (eval e₁) of λ where
    (just (boolV b)) → bIf b (eval e₂) (eval e₃)
    _ → nothing

open EvalExp

-- The execution of a declaration adds a new binding
-- to the environment.

execDecl : Decl → Env → Maybe Env
execDecl (dInit t x e) ρ = case eval ρ e of λ where
  (just v) → just ((x , v) ∷ ρ)
  nothing  → nothing

-- Execution of declarations returns the extended environment.

execDecls : List Decl → Env → Maybe Env
execDecls [] ρ = just ρ
execDecls (d ∷ ds) ρ = case execDecl d ρ of λ where
  (just ρ') → execDecls ds ρ'
  nothing   → nothing

-- Execution of statements can change values in the environment
-- and can diverge.

module ExecStm where

  -- Execution is parameterized by a number (fuel : ℕ)
  -- that limits the number of executions of while loops.
  -- This is necessary to please Agda's termination checker.

  mutual

    execStm : (fuel : ℕ) → Stm → Env → Maybe Env

    execStm _ (sAss x e) ρ = case eval ρ e of λ where
      (just v) → just (updateEnv x v ρ)
      nothing  → nothing

    execStm 0          (sWhile e ss) ρ = nothing
    execStm (suc fuel) (sWhile e ss) ρ = case eval ρ e of λ where
      (just (boolV true)) → case execStms fuel ss ρ of λ where
        (just ρ') → execStm fuel (sWhile e ss) ρ'
        nothing   → nothing
      (just (boolV false)) → just ρ
      _                    → nothing

    execStm fuel (sIfElse e ss ss') ρ =
      case eval ρ e of λ where
        (just (boolV true))  → execStms fuel ss  ρ
        (just (boolV false)) → execStms fuel ss' ρ
        _                    → nothing

    execStm 0          (sDoWhile ss e) ρ = nothing
    execStm (suc fuel) (sDoWhile ss e) ρ = case execStms fuel ss ρ of λ where
      (just ρ′) → case eval ρ′ e of λ where
        (just (boolV true))  → execStm fuel (sDoWhile ss e) ρ′
        (just (boolV false)) → just ρ′
        _                    → nothing
      nothing   → nothing

    execStm fuel (sSwitch e cs) ρ = case eval ρ e of λ where
      (just e′) → execSwitch fuel e′ ρ cs
      (nothing) → nothing

    execSwitch : (fuel : ℕ) → Val → Env → List SwitchCase → Maybe Env
    execSwitch (suc fuel) e ρ (sCase v ss ∷ cs) =
      case eval ρ v of λ where
        (just v′) →
          if e == v′
          then execStms fuel ss ρ
          else execSwitch fuel e ρ cs
        (nothing) → nothing

    execSwitch _          e ρ _ = nothing


    -- Execution of a statement sequence, passes the fuel
    -- to every statement.

    execStms : (fuel : ℕ) → List Stm → Env → Maybe Env
    execStms _    []       ρ = just ρ
    execStms fuel (s ∷ ss) ρ = case execStm fuel s ρ of λ where
      (just ρ') → execStms fuel ss ρ'
      nothing   → nothing

  -- We evaluate a program by first executing the declarations,
  -- then the statements, and finally evaluating the main expression.

  evalPrg : (fuel : ℕ) → Program → Maybe ℤ
  evalPrg fuel (program ds ss e) = case execDecls ds [] of λ where
    (just ρ₀) → case execStms fuel ss ρ₀ of λ where
      (just ρ) → case eval ρ e of λ where
        (just (intV v)) → just v
        _               → nothing
      nothing  → nothing
    nothing   → nothing
