
module Library.Eq where

open import Data.Bool using (Bool)
open import Data.Char using (Char)
open import Data.Integer using (ℤ)
open import Data.List.Base using (List; []; _∷_)
open import Data.String using (String)

open import Data.Product using (_×_; _,_)

open import Function using (case_of_)

open import Relation.Binary using (Decidable)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; cong₂)
open import Relation.Nullary using (¬_; Dec; yes; no)
open import Relation.Nullary.Decidable using (⌊_⌋)

-- Type class for decidable equality.

record Eq {ℓ} (A : Set ℓ) : Set ℓ where
  field
    _≟_ : Decidable (_≡_ {A = A})

  _==_ : A → A → Bool
  x == y = ⌊ x ≟ y ⌋

open Eq {{...}} public

-- Instances for basic types

instance
  eqBool : Eq Bool
  _≟_ {{eqBool}} = Data.Bool._≟_

instance
  eqℤ : Eq ℤ
  _≟_ {{eqℤ}} = Data.Integer._≟_

instance
  eqChar : Eq Char
  _≟_ {{eqChar}} = Data.Char._≟_

instance
  eqString : Eq String
  _≟_ {{eqString}} = Data.String._≟_

instance
  eqList : ∀ {ℓ} {A : Set ℓ} {{_ : Eq A}} → Eq (List A)
  _≟_ {{eqList}} = λ where
    []       []       → yes refl
    []       (y ∷ ys) → no λ ()
    (x ∷ xs) []       → no λ ()
    (x ∷ xs) (y ∷ ys) → case (x ≟ y , xs ≟ ys) of λ where
      (yes p , yes q) → yes (cong₂ _∷_ p q)
      (yes _ , no ¬q) → no (λ { refl → ¬q refl })
      (no ¬p , _    ) → no (λ { refl → ¬p refl })
