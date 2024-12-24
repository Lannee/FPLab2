open import Data.Nat as ℕ using (ℕ; suc)

module AVL.Height where

infix 5 〈_⊔_〉≡_

data 〈_⊔_〉≡_ : ℕ → ℕ → ℕ → Set where
    ∼+ : ∀ {n} → 〈 suc n ⊔ n 〉≡ suc n
    ∼0 : ∀ {n} → 〈 n ⊔ n 〉≡ n 
    ∼- : ∀ {n} → 〈 n ⊔ suc n 〉≡ suc n

max∼ : ∀ {i j m} → 〈 i ⊔ j 〉≡ m → 〈 m ⊔ i 〉≡ m
max∼ ∼+ = ∼0
max∼ ∼0 = ∼0
max∼ ∼- = ∼+

∼max : ∀ {i j m} → 〈 i ⊔ j 〉≡ m → 〈 j ⊔ m 〉≡ m
∼max ∼+ = ∼-
∼max ∼0 = ∼0
∼max ∼- = ∼0