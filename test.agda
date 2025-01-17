
{-# OPTIONS --guardedness #-}

module test where

import AVL

open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Product
import Data.Nat.Properties as ℕ
open import Agda.Builtin.Nat
open import Data.Nat.Show using (show)
open import Data.String using (String; head; _<+>_)
open import Relation.Binary using (module StrictTotalOrder)
open import Data.List using (List; _∷_ ; [])

open import IO
open import Agda.Builtin.Unit using (⊤)
open import Function using (_$_)
open import System.Exit using (exitSuccess ; exitFailure ; isFailure ; die)

open AVL (Nat)
 (StrictTotalOrder.isStrictTotalOrder ℕ.<-strictTotalOrder)

-- Empty

t₀ : Bag (Nat)
t₀ = emptyᴮ

_ : (sizeᴮ t₀) ≡ 0
_ = refl

_ : (toListᴮ t₀) ≡ []
_ = refl

-- Creating singleton (1 , 10)

t₁ = singletonᴮ 1 10

_ : (sizeᴮ t₁) ≡ 1
_ = refl

_ : (lookupᴮ 1 t₁) ≡ (just 10)
_ = refl

_ : (lookupᴮ 2 t₁) ≡ nothing
_ = refl

_ : (toListᴮ t₁) ≡ (10 ∷ [])
_ = refl


-- Inserting (2 , 20)

t₂ = insertᴮ 2 20 t₁

_ : (sizeᴮ t₂) ≡ 2
_ = refl

_ : (lookupᴮ 2 t₂) ≡ (just 20)
_ = refl

-- Tree of pairs

t₅ = insertᴮ 5 50 $ insertᴮ 4 40 $ insertᴮ 3 30 t₂

_ : (sizeᴮ t₅) ≡ 5
_ = refl

_ : (toListᴮ t₅) ≡ (10 ∷ 20 ∷ 30 ∷ 40 ∷ 50 ∷ [])
_ = refl

-- map elements to String

t₅‵ : Bag (String)
t₅‵ = mapᴮ (λ e → show e) t₅

_ : (sizeᴮ t₅‵) ≡ 5
_ = refl

_ : (lookupᴮ 5 t₅‵) ≡ (just "50")
_ = refl

_ : (foldlᴮ (λ r v → r <+> v) "" t₅‵) ≡ "50 30 40 10 20"
_ = refl

_ : (foldrᴮ (λ r v → r <+> v) "" t₅‵) ≡ "20 40 50 30 10"
_ = refl
 
_ : (toListᴮ t₅‵) ≡ ("10" ∷ "20" ∷ "30" ∷ "40" ∷ "50" ∷ [])
_ = refl

-- delete element

t₄‵ = deleteᴮ 3 t₅‵

_ : (sizeᴮ t₄‵) ≡ 4
_ = refl

_ : (toListᴮ t₄‵) ≡ ("10" ∷ "20" ∷ "40" ∷ "50" ∷ [])
_ = refl