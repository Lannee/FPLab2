open import Relation.Binary
open import Relation.Binary.PropositionalEquality
open import Level using (Level; Lift; lift; _⊔_; lower)
open import Data.Nat as ℕ using (ℕ; suc; zero; pred)
open import Data.Nat.Properties as ℕProps using (≤-refl)
open import Data.Product
open import Data.Unit
open import Data.Maybe
open import Function
open import Data.Bool
open import Data.Empty

open import AVL.Height

module AVL
    {k r} (Key : Set k)
    {_<_ : Rel Key r}
    (isStrictTotalOrder : IsStrictTotalOrder _≡_ _<_)
    where

open IsStrictTotalOrder isStrictTotalOrder
    
infix 5 [_]

data [●] : Set k where
    ⌊⌋ ⌈⌉ : [●]
    [_] : (k : Key) → [●]

infix 4 _[<]_
_[<]_ : [●] → [●] → Set r
⌊⌋ [<] ⌊⌋ = Lift r ⊥
⌊⌋ [<] ⌈⌉ = Lift r ⊤
⌊⌋ [<] [ _ ] = Lift r ⊤
⌈⌉ [<] _ = Lift r ⊥
[ _ ] [<] ⌊⌋ = Lift r ⊥
[ _ ] [<] ⌈⌉ = Lift r ⊤
[ x ] [<] [ y ] = x < y

infix 4 _<_<_
_<_<_ : [●] → Key → [●] → Set r
l < x < u = l [<] [ x ] × [ x ] [<] u

x≮⌊⌋ : ∀ {x} → x [<] ⌊⌋ → Lift r ⊥
x≮⌊⌋ {⌊⌋}     = lift ∘ lower
x≮⌊⌋ {⌈⌉}     = lift ∘ lower
x≮⌊⌋ {[ _ ]} = lift ∘ lower

[<]-trans : ∀ x {y z} → x [<] y → y [<] z → x [<] z
[<]-trans ⌊⌋     {  y  } {  ⌊⌋  } _ y<z = x≮⌊⌋ {x = y} y<z
[<]-trans ⌊⌋     {  _  } {  ⌈⌉  } _  _  = _
[<]-trans ⌊⌋     {  _  } {[ _ ]} _  _  = _
[<]-trans ⌈⌉     {  _  } {  _  } (lift ()) _ 
[<]-trans [ _ ] {  y  } {  ⌊⌋  } _ y<z = x≮⌊⌋ {x = y} y<z
[<]-trans [ _ ] {  _  } {  ⌈⌉  } _ _ = _
[<]-trans [ _ ] {  ⌊⌋  } {[ _ ]} (lift ()) _ 
[<]-trans [ _ ] {  ⌈⌉  } {[ _ ]} _ (lift ())
[<]-trans [ x ] {[ y ]} {[ z ]} x<y y<z = 
    IsStrictTotalOrder.trans isStrictTotalOrder x<y y<z


data Tree {v} 
          (V : Key → Set v) 
          (l u : [●]) : ℕ → 
          Set (k ⊔ v ⊔ r) where
    leaf : (l<u : l [<] u) → Tree V l u 0
    node : ∀ {h lh rh}
             (k : Key)
             (v : V k)
             (bl : 〈 lh ⊔ rh 〉≡ h )
             (lk : Tree V l [ k ] lh)
             (ku : Tree V [ k ] u rh) →
             Tree V l u (suc h)

_1?+〈_〉 : ∀ {ℓ} (T : ℕ → Set ℓ) → ℕ → Set ℓ
T 1?+〈 n 〉 = ∃[ inc? ] T (if inc? then suc n else n)

pattern 0+_ tr = false , tr
pattern 1+_ tr = true , tr

data _〈_〉?-1 {ℓ} (T : ℕ → Set ℓ) : ℕ → Set ℓ where
    _–0 : ∀ {n} → T n → T 〈 n 〉?-1
    _–1 : ∀ {n} → T n → T 〈 suc n 〉?-1

1?+〈_〉⇒?-1 : ∀ {n ℓ} {T : ℕ → Set ℓ} 
             → T 1?+〈 n 〉
             → T 〈 suc n 〉?-1
1?+〈 0+ x 〉⇒?-1 = x –1
1?+〈 1+ x 〉⇒?-1 = x –0
        

rotʳ : ∀ {lb ub rh v} {V : Key → Set v}
     → (k : Key)
     → V k
     → Tree V lb [ k ] (suc (suc rh))
     → Tree V [ k ] ub rh
     → Tree V lb ub 1?+〈 (suc (suc rh)) 〉
rotʳ x xv (node y yv ∼+ a b) c = 
    0+ (node y yv ∼0 a (node x xv ∼0 b c))
rotʳ x xv (node y yv ∼0 a b) c = 
    1+ (node y yv ∼- a (node x xv ∼+ b c))
rotʳ x xv (node y yv ∼- a (node z zv bl b c)) d = 
    0+ (node z zv ∼0 (node y yv (max∼ bl) a b) (node x xv (∼max bl) c d)) 

rotˡ : ∀ {lb ub lh v} {V : Key → Set v}
     → (k : Key)
     → V k
     → Tree V lb [ k ] lh
     → Tree V [ k ] ub (suc (suc lh))
     → Tree V lb ub 1?+〈 (suc (suc lh)) 〉
rotˡ x xv c (node y yv ∼- b a) = 
    0+ (node y yv ∼0 (node x xv ∼0 c b) a)
rotˡ x xv c (node y yv ∼0 b a) = 
    1+ (node y yv ∼+ (node x xv ∼- c b) a)
rotˡ x xv d (node y yv ∼+ (node z zv bl c b) a) = 
    0+ (node z zv ∼0 (node x xv (max∼ bl) d c) (node y yv (∼max bl) b a)) 


insert : ∀ {l u h v} {V : Key → Set v} (k : Key) 
       → V k
       → (V k → V k → V k)
       → Tree V l u h
       → l < k < u
       → Tree V l u 1?+〈 h 〉
insert v vc f (leaf l<u) (l , u) = 1+ (node v vc ∼0 (leaf l) (leaf u))
insert v vc f (node k kc bl tl tr) prf with compare v k
insert v vc f (node k kc bl tl tr) (l , _)
    | tri< a _ _ with insert v vc f tl (l , a)
... | 0+ tl′ = 0+ (node k kc bl tl′ tr)
... | 1+ tl′ with bl
... | ∼+ = rotʳ k kc tl′ tr
... | ∼0 = 1+ (node k kc ∼+ tl′ tr)
... | ∼- = 0+ (node k kc ∼0 tl′ tr)
insert v vc f (node k kc bl tl tr) _
    | tri≈ _ refl _ = 0+ (node k (f vc kc) bl tl tr)
insert v vc f (node k kc bl tl tr) (_ , u)
    | tri> _ _ c with insert v vc f tr (c , u)
... | 0+ tr′ = 0+ (node k kc bl tl tr′)
... | 1+ tr′ with bl
... | ∼+ = 0+ (node k kc ∼0 tl tr′)
... | ∼0 = 1+ (node k kc ∼- tl tr′)
... | ∼- = rotˡ k kc tl tr′


lookup : (k : Key)
       → ∀ {l u s v} {V : Key → Set v}
       → Tree V l u s 
       → Maybe (V k)
lookup k (leaf l<u) = nothing
lookup k (node v vc _ tl tr) with compare k v
... | tri< _ _    _ = lookup k tl
... | tri≈ _ refl _ = just vc
... | tri> _ _    _ = lookup k tr


record Cons {v}
            (V : Key → Set v)
            (lb ub : [●])
            (h : ℕ) : Set (k ⊔ v ⊔ r) where
    constructor cons
    field 
        head : Key
        val  : V head
        l<u  : lb [<] [ head ]
        tail : Tree V [ head ] ub 1?+〈 h 〉

uncons : ∀ {lb ub h lh rh v} {V : Key → Set v}
         → (k : Key)
         → V k
         → 〈 lh ⊔ rh 〉≡ h
         → Tree V lb [ k ] lh
         → Tree V [ k ] ub rh
         → Cons V lb ub h
uncons k v b (leaf l<u) tr = cons k v l<u (case b of
    λ { ∼- → 0+ tr
      ; ∼0 → 0+ tr})
uncons k v b (node kₗ vₗ bₗ tlₗ trₗ) tr with uncons kₗ vₗ bₗ tlₗ trₗ
... | cons k′ v′ l<u tail = cons k′ v′ l<u (case tail of
    λ { (1+ tl′) → 1+ (node k v b tl′ tr)
      ; (0+ tl′) → case b of
        λ { ∼+ → 0+ node k v ∼0 tl′ tr
          ; ∼0 → 1+ node k v ∼- tl′ tr
          ; ∼- → rotˡ k v tl′ tr }})

ext : ∀ {lb ub ub′ h v} {V : Key → Set v}
      → ub [<] ub′
      → Tree V lb ub  h
      → Tree V lb ub′ h
ext {lb} ub<ub′ (leaf l<u) = leaf ([<]-trans lb l<u ub<ub′)
ext ub<ub′ (node k v bl tl tr) = node k v bl tl (ext ub<ub′ tr)

join : ∀ {lb ub lh rh h v k} {V : Key → Set v}
       → Tree V [ k ] ub rh
       → 〈 lh ⊔ rh 〉≡ h
       → Tree V lb [ k ] lh
       → Tree V lb ub 1?+〈 h 〉
join (leaf k<ub) ∼+ tl = 0+ ext k<ub tl
join {lb} (leaf k<ub) ∼0 (leaf lb<k) =
    0+ leaf ([<]-trans lb lb<k k<ub) 
join (node kᵣ vᵣ bᵣ tlᵣ rtᵣ) b tl with uncons kᵣ vᵣ bᵣ tlᵣ rtᵣ
... | cons k′ v′ l<u (1+ tr′) = 1+ node k′ v′ b (ext l<u tl) tr′
... | cons k′ v′ l<u (0+ tr′) with b
... | ∼+ = rotʳ k′ v′ (ext l<u tl) tr′
... | ∼0 = 1+ node k′ v′ ∼+ (ext l<u tl) tr′
... | ∼- = 0+ node k′ v′ ∼0 (ext l<u tl) tr′

delete : ∀ {lb ub h v} {V : Key → Set v}
         → (k : Key)
         → Tree V lb ub h
         → Tree V lb ub 〈 h 〉?-1
delete x (leaf l<u) = leaf l<u –0
delete x (node y  yv b l r) with compare x y
delete x (node .x yv b l r) | tri≈ _ refl _ = 1?+〈 join r b l 〉⇒?-1
delete x (node y  yv b l r) | tri< a _ _ with delete x l
... | l′ –0 = node y yv b l′ r –0
... | l′ –1 with b
... | ∼+ = node y yv ∼0 l′ r –1
... | ∼0 = node y yv ∼- l′ r –0
... | ∼- = 1?+〈 rotˡ y yv l′ r 〉⇒?-1
delete x (node y  yv b l r) | tri> _ _ c with delete x r
... | r′ –0 = node y yv b l r′ –0
... | r′ –1 with b
... | ∼+ = 1?+〈 rotʳ y yv l r′ 〉⇒?-1
... | ∼0 = node y yv ∼+ l r′ –0
... | ∼- = node y yv ∼0 l r′ –1 



mapᵗ : ∀ {v w} {V : Key → Set v} {W : Key → Set w}
    → (∀ {k} → V k → W k)
    → ∀ {l u h}
    → Tree V l u h
    → Tree W l u h
mapᵗ f (leaf l<u) = leaf l<u
mapᵗ f (node x xv b l r) = node x (f xv) b (mapᵗ f l) (mapᵗ f r)


foldr : ∀ {l u h v} {V : Key → Set v} {A : Set v} → (∀ {k} → V k → A → A) → A → Tree V l u h → A
foldr _ z (leaf l<u) = z
foldr f z (node x xv _ tl tr) = f xv (foldr f (foldr f z tl) tr)


foldl : ∀ {l u h v} {V : Key → Set v} {A : Set v} → (∀ {k} → V k → A → A) → A → Tree V l u h → A
foldl _ z (leaf l<u) = z
foldl f z (node x xv _ tl tr) = foldl f (foldl f (f xv z) tl) tr


module Bag where

    data Bag {v} (V : Set v) : Set (k ⊔ v ⊔ r) where
        tree : ∀ {h}
                → Tree (const V) ⌊⌋ ⌈⌉ h
                → Bag V

    insertWithᴮ : ∀ {v} {V : Set v} (k : Key)
                 → V
                 → (V → V → V)
                 → Bag V
                 → Bag V
    insertWithᴮ k v f (tree tr) = 
        tree (proj₂ (insert k v f tr (lift tt , lift tt)))

    insertᴮ : ∀ {v} {V : Set v} (k : Key) → V → Bag V → Bag V
    insertᴮ k v = insertWithᴮ k v const

    lookupᴮ : (k : Key) → ∀ {v} {V : Set v} → Bag V → Maybe V
    lookupᴮ k (tree tr) = lookup k tr

    deleteᴮ : (k : Key) → ∀ {v} {V : Set v} → Bag V → Bag V
    deleteᴮ k (tree tr) with delete k tr
    ... | tr′ –0 = tree tr′
    ... | tr′ –1 = tree tr′

    mapᴮ : ∀ {v w} {V : Set v} {W : Set w} → (V → W) → Bag V → Bag W
    mapᴮ f (tree tr) = tree (mapᵗ f tr)

    foldrᴮ : ∀ {v} {V : Set v} → (V → V → V) → V → Bag V → V
    foldrᴮ f nil (tree tr) = foldr f nil tr
 