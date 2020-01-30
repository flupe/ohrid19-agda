-- Intrinsically well-typed WHILE syntax.

module V1.WellTypedSyntax where

open import Library
open import V1.AST public using (Type; bool; int; Boolean; true; false; PrintBoolean)

-- Well-typed expressions: context is fixed.

data Exp : Type → Set where
  -- Literals:
  eInt   : (i : ℤ)           → Exp int
  eBool  : (b : Boolean)     → Exp bool
  -- Operators:
  ePlus  : (e e' : Exp int)  → Exp int
  eMinus : (e e' : Exp int)  → Exp int
  eMul   : (e e' : Exp int)  → Exp int
  eDiv   : (e e' : Exp int)  → Exp int
  eGt    : (e e' : Exp int)  → Exp bool
  eNot   : (e    : Exp bool) → Exp bool
  eOr    : (e e' : Exp bool) → Exp bool
  eAnd   : (e e' : Exp bool) → Exp bool
  eEq    : ∀ {a} → (e e' : Exp a) → Exp bool
  -- Conditionals:
  eCond  : ∀{t} (e : Exp bool) (e' e'' : Exp t) → Exp t

-- For now, a program is just a final expression.

record Program : Set where
  constructor program
  field
    theMain  : Exp int

open Program public


-- -}
