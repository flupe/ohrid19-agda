-- Type checker for the WHILE language.

{-# OPTIONS --postfix-projections #-}

module V2.TypeChecker where

open import Library
open import Data.Sum

import V2.AST as A
open import V2.WellTypedSyntax

-- Names as coming from the abstract syntax are just strings.

Name = String

idToName : A.Id → Name
idToName (A.mkId x) = String.fromList x

-- Local context for the type checker.

TCCxt : (Γ : Cxt) → Set
TCCxt Γ = AssocList Name Γ

-- Querying the local context.

-- Type errors.
--
-- Currently, these errors do not carry enough evidence that
-- something is wrong.  The type checker does not produce
-- evidence of ill-typedness in case of failure,
-- only of well-typedness in case of success.

data TypeError : Set where
  alreadyDeclaredVariable : Name → TypeError
  unboundVariable         : Name → TypeError
  typeMismatch            : (tinf texp : Type)  → tinf ≢ texp → TypeError

instance
  PrintError : Print TypeError
  print {{PrintError}} = λ where
    (alreadyDeclaredVariable x) → "already declared variable " String.++ x
    (unboundVariable x)         → "unbound variable " String.++ x
    (typeMismatch tinf texp _)  → String.concat $
      "type mismatch: expected " ∷ print texp ∷
      ", but inferred " ∷ print tinf ∷ []

-- Type error monad.

open ErrorMonad {E = TypeError}

-- Checking variables
---------------------------------------------------------------------------


lookupVar : {Γ : Cxt} (γ : TCCxt Γ) (x : Name)
          → Error (Σ Type (λ t → Var Γ t))
lookupVar {[]}    []       x = throwError $ unboundVariable x
lookupVar {t ∷ Γ} (x' ∷ γ) x = case x ≟ x' of λ where
  (yes refl) → ok (t , here)
  (no _)     → case lookupVar γ x of λ where
    (ok (t , i)) → ok (t , there i)
    (fail err)   → fail err

-- Checking expressions
---------------------------------------------------------------------------

module CheckExpressions {Γ : Cxt} (γ : TCCxt Γ) where

  mutual

    -- Type inference.

    inferExp : (e : A.Exp) → Error (Σ Type (λ t → Exp Γ t))

    inferExp (A.eInt i)  = return (int  , eInt  i)
    inferExp (A.eBool b) = return (bool , eBool b)

    inferExp (A.eId x) = do
      (t , x') ← lookupVar γ (idToName x)
      return (t , eVar x')

    inferExp (A.ePlus e₁ e₂) = do
      e₁' ← checkExp e₁ int
      e₂' ← checkExp e₂ int
      return (int , ePlus e₁' e₂')

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

    -- Type checking.
    -- Calls inference and checks inferred type against given type.

    checkExp : (e : A.Exp) (t : Type) → Error (Exp Γ t)
    checkExp e t = do
      (t' , e') ← inferExp e
      case t' ≟ t of λ where
        (yes refl) → return e'
        (no  t'≢t) → throwError (typeMismatch t' t t'≢t)


-- The declaration checker calls the expression checker.
-- Exported interface of expression checker:

-- Monad for checking expressions

record TCExp Γ (A : Set) : Set where
  field
    runTCExp : TCCxt Γ → Error A
open TCExp

checkExp : ∀{Γ} (e : A.Exp) (t : Type) → TCExp Γ (Exp Γ t)
checkExp e t .runTCExp γ = CheckExpressions.checkExp γ e t

-- Checking declarations.
---------------------------------------------------------------------------

-- Monad for checking declarations.

-- Variable declarations can be inserted into the top block, thus,
-- we need to treat the top block as mutable state.

record TCDecl Γ Γ' (A : Set) : Set where
  field
    runTCDecl : TCCxt Γ → Error (A × TCCxt Γ')
open TCDecl

module CheckDeclarations where

  -- TCDecl is a monad.

  private

    returnTCDecl : ∀ {Γ A} (a : A) → TCDecl Γ Γ A
    returnTCDecl a .runTCDecl γ = ok (a , γ)

    bindTCDecl : ∀{Γ Γ′ Γ″ A B}
      (m :     TCDecl Γ  Γ′ A)
      (k : A → TCDecl Γ′ Γ″ B)
             → TCDecl Γ  Γ″ B

    bindTCDecl m k .runTCDecl γ =
      case m .runTCDecl γ of λ where
        (fail err)    → fail err
        (ok (a , γ′)) → k a .runTCDecl γ′


  instance
    functorTCDecl : ∀ {Γ Γ′} → Functor (TCDecl Γ Γ′)
    fmap {{functorTCDecl}} f m = bindTCDecl m (returnTCDecl ∘′ f)

    iApplicativeTCDecl : IApplicative TCDecl
    pure  {{iApplicativeTCDecl}}       = returnTCDecl
    _<*>_ {{iApplicativeTCDecl}} mf mx = bindTCDecl mf (_<$> mx)

    iMonadTCDecl : IMonad TCDecl
    _>>=_ {{iMonadTCDecl}} = bindTCDecl

  -- Lifting a TCExp computation into TCDecl.

  lift : ∀{Γ A} (m : TCExp Γ A) → TCDecl Γ Γ A
  lift m .runTCDecl γ =
    case m .runTCExp γ of λ where
      (fail err) → fail err
      (ok a)     → ok (a , γ)

  -- Add a variable declaration.

  addVar : ∀{Γ} (x : Name) t → TCDecl Γ (t ∷ Γ) ⊤
  addVar {Γ = Γ} x t .runTCDecl γ = ok (_ , (t ↦ x ∷ γ))

  mutual

    checkDefined : ∀ {Γ} → Name → (t : Type) → TCDecl Γ Γ (Var Γ t)
    checkDefined x t .runTCDecl γ =
      case lookupVar γ x of λ where
        (ok (t′ , x′)) →
          case t′ ≟ t of λ where
            (yes refl) → ok (x′ , γ)
            (no t′≢t) → throwError (typeMismatch t′ t t′≢t)
        (fail err) → fail err

    -- bypassing TCDecl for now

    testDecl : ∀ {Γ Δ}
         → TCCxt Γ × TCCxt Δ
         → (d : A.Decl)
         → Error ((Σ Cxt (λ Γ′ → TCCxt Γ′ × Maybe (Decl Γ Γ′))))

    testDecl {Γ} {Δ} (γ , δ) (A.dDecl t x) = do
      let x′ = idToName x
      case lookupVar δ x′ of λ where
        (ok _)   → throwError (alreadyDeclaredVariable x′)
        (fail _) → ok (t ∷ Δ , t ↦ x′ ∷ δ , nothing)

    testDecl {Γ} (γ , δ) (A.dInit t x e) = do
      e′ ← CheckExpressions.checkExp γ e t
      let x′ = idToName x
      case lookupVar δ x′ of λ where
        (ok _)   → throwError (alreadyDeclaredVariable x′)
        (fail _) → ok (t ∷ Γ , t ↦ x′ ∷ γ , (just $ dInit e′))

    testDecl {Γ} {Δ} (γ , δ) (A.dAssign x e) = do
      let x′ = idToName x
      case lookupVar γ x′ of λ where
        (ok (t , x″)) → do
          e′ ← CheckExpressions.checkExp γ e t
          return (Γ , γ , just (dAssign x″ e′))

        (fail _) →
          case lookupVar δ x′ of λ where
            (ok (t , _)) → do
              e′ ← CheckExpressions.checkExp γ e t
              return (t ∷ Γ , t ↦ x′ ∷ γ , just (dInit e′))

            (fail _) → throwError (unboundVariable x′)

    testDecl {Γ} (γ , δ) (A.dIncr x) = do
      (x′ , _) ← checkDefined (idToName x) int .runTCDecl γ
      return (Γ , γ , just (dIncr x′))

    testDecl {Γ} (γ , δ) (A.dAdd x e) = do
      (x′ , _) ← checkDefined (idToName x) int .runTCDecl γ
      e′ ← CheckExpressions.checkExp γ e int
      return (Γ , γ , just (dAdd x′ e′))

    testDecls : ∀ {Γ Δ} → TCCxt Γ × TCCxt Δ → List A.Decl → Error (Σ Cxt (λ Γ′ → TCCxt Γ′ × Decls Γ Γ′))
    testDecls {Γ} (γ , _) [] = return (Γ , (γ , []))
    testDecls (γ , δ) (x ∷ xs) =
      case testDecl (γ , δ) x of λ where
        (fail err) → fail err

        -- new variables have been initiated
        (ok (Γ′ , (γ′ , just d))) → do
          (Γ″ , (γ‴ , decls)) ← testDecls (γ′ , δ) xs
          return (Γ″ , (γ‴ , d ∷ decls))

        -- new variables have been declared
        (ok (Δ′ , (δ′ , nothing))) → do
          (Γ″ , (γ″ , decls)) ← testDecls (γ , δ′) xs
          return (Γ″ , (γ″ , decls))


  checkProgram : (prg : A.Program)
    → Error Program

  checkProgram (A.program ds e) = do
    (Γ , (γ , ds′)) ← testDecls ([] , []) ds
    e′  ← CheckExpressions.checkExp γ e int
    return (program ds′ e′)

-- Checking the program.
---------------------------------------------------------------------------

checkProgram : (prg : A.Program) → Error Program
checkProgram prg = CheckDeclarations.checkProgram prg

-- -}
-- -}
-- -}
-- -}
-- -}
-- -}
