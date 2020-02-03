-- Intrinsically well-typed WHILE syntax.

module V2.WellTypedSyntax where

open import Library
open import V2.AST public using (Type; bool; int; Boolean; true; false; PrintBoolean)

-- Variables are de Bruijn indices into the context, a list of types.

Cxt = List Type

data Var : (Γ : Cxt) (t : Type) → Set where
  here  : ∀ {Γ t} → Var (t ∷ Γ) t
  there : ∀ {Γ t t'} → Var Γ t → Var (t' ∷ Γ) t

-- Well-typed expressions: context is fixed.

data Exp (Γ : Cxt) : Type → Set where
  -- Literals:
  eInt  : (i : ℤ)                                  → Exp Γ int
  eBool : (b : Boolean)                            → Exp Γ bool
  -- Operators:
  ePlus : (e e' : Exp Γ int)                       → Exp Γ int
  eGt   : (e e' : Exp Γ int)                       → Exp Γ bool
  eAnd  : (e e' : Exp Γ bool)                      → Exp Γ bool
  -- Conditionals:
  eCond : ∀{t} (e : Exp Γ bool) (e' e'' : Exp Γ t) → Exp Γ t
  -- Variables:
  eVar  : ∀{t}    (x : Var Γ t)                    → Exp Γ t
-- Well-typed declarations (extending the context).

data Decl (Γ : Cxt) : Cxt → Set where
  dInit   : ∀ {t}           → Exp Γ t   → Decl Γ (t ∷ Γ)
  dAssign : ∀ {t} → Var Γ t → Exp Γ t   → Decl Γ Γ 
  dIncr   : Var Γ int                   → Decl Γ Γ
  dAdd    : Var Γ int       → Exp Γ int → Decl Γ Γ

data Decls (Γ : Cxt) : Cxt → Set where
  []  : Decls Γ Γ
  _∷_ : ∀ {Γ₁ Γ₂} (s : Decl Γ Γ₁) (ss : Decls Γ₁ Γ₂) → Decls Γ Γ₂

-- A program is a list of statements and a final expression.

record Program : Set where
  constructor program
  field
    {Γ}      : Cxt
    theDecls : Decls [] Γ
    theMain  : Exp Γ int

open Program public


-- -}
