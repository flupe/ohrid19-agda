-- Imports from the standard library and additional Haskell bindings.

module Library where

open import Data.Bool.Base                        public using (Bool; true; false; not; if_then_else_) hiding (module Bool)
open import Data.Char.Base                        public using (Char)
open import Data.Empty                            public using (⊥)
open import Data.Integer.Base                     public using (ℤ; -[1+_]; +_; _+_; _-_; _*_)
open import Data.Integer.DivMod                   public using (_div_)
open import Data.List.Base                        public using (List; []; _∷_; _++_) hiding (module List)
open import Data.List.All                         public using ([]; _∷_)
open import Data.Maybe.Base                       public using (Maybe; nothing; just)
open import Data.Nat.Base                         public using (ℕ; zero; suc)
open import Data.Product                          public using (Σ; Σ-syntax; _×_; _,_; proj₁; proj₂; map₁; map₂)
open import Data.String.Base                      public using (String)
open import Data.Sum.Base                         public using (_⊎_; inj₁; inj₂)
open import Data.Unit.Base                        public using (⊤)

open import Function                              public using (id; _∘_; _∘′_; _$_; case_of_)
open import Level                                 public using (_⊔_)

open import Library.Error                         public
open import Library.Eq                            public
open import Library.IO                            public
open import Library.List                          public
open import Library.Monad                         public
open import Library.Print                         public

open import Relation.Binary.PropositionalEquality public using (_≡_; _≢_; refl; cong; cong₂; subst)
open import Relation.Binary                       public using (Decidable; Rel)
open import Relation.Nullary                      public using (¬_; Dec; yes; no)
open import Relation.Nullary.Decidable            public using (⌊_⌋)

open import Size                                  public

-- Qualified imports

module Bool where
  open import Data.Bool.Base public

module Character where
  open import Data.Char public

module Integer where
  open import Data.Integer public
  open import Data.Nat using () renaming (_≟_ to _ℕ≟_)
  open import Relation.Nullary.Decidable using (fromWitnessFalse)

  _<=_ : (i j : ℤ) → Bool
  i <= j = ⌊ i ≤? j ⌋

  _div'_ : ℤ → ℤ → ℤ
  a div' b with (∣ b ∣) ℕ≟ 0
  ...         | yes _    = +0
  ...         | no  b≢0 = _div_ a b {fromWitnessFalse b≢0}
  
module String where
  open import Data.String.Base public

-- -}
