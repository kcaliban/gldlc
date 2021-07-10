------------------------------------------------------------------------
-- Auxiliary lemmas/functions
------------------------------------------------------------------------

module Aux where

open import Data.Nat
open import Level renaming (zero to lzero)
open import Data.Fin
open import Data.Fin.Properties
open import Data.Fin.Subset renaming (∣_∣ to ∣_∣ˢ) hiding (⊤)
open import Data.Fin.Subset.Properties
open import Data.Vec
open import Data.Bool
open import Data.Bool.Properties
open import Data.Product
open import Data.Sum
open import Relation.Unary hiding (_∈_ ; _⊆_)
open import Relation.Nullary
open import Relation.Nullary.Negation
open import Relation.Nullary.Sum
open import Relation.Nullary.Decidable
open import Relation.Binary.PropositionalEquality hiding (Extensionality)
open import Data.Empty renaming (⊥ to ⊥')
open import Data.Maybe
open import Data.Maybe.Relation.Unary.All
open import Data.Maybe.Relation.Unary.Any
open import Data.Unit

------------------------------------------------------------------------
-- Extensionality

postulate
  ext : {A : Set}{B : A → Set}{f : (x : A) → B x} {g : (x : A) → B x} →
    (∀ x → f x ≡ g x) → f ≡ g

------------------------------------------------------------------------
-- Various properties

¬∃⇒∀¬ : {A : Set} {B : A → Set} → ¬ (∃[ a ](B a)) → ∀ a → ¬ (B a)
¬∃⇒∀¬ ¬∃ a b = ¬∃ (a , b)

A≢B→B≢A : {A : Set} → {a b : A} → ¬ (a ≡ b) → ¬ (b ≡ a)
A≢B→B≢A {A} {a} {b} neq = λ x → contradiction (sym x) neq

sum-eq : {A B : Set} {x y : A} → (inj₁{B = B} x) ≡ (inj₁{B = B} y) → x ≡ y
sum-eq {A} {B} {x} {.x} refl = refl

isnothing⇒¬isjust : {A : Set} {a : Maybe A} → Is-nothing a → ¬ (Is-just a)
isnothing⇒¬isjust {A} {.nothing} nothing = λ ()

¬isjust⇒isnothing : {A : Set} {a : Maybe A} → ¬ (Is-just a) → Is-nothing a
¬isjust⇒isnothing {A} {nothing} ju = nothing
¬isjust⇒isnothing {A} {just x} ju = contradiction (just Data.Unit.tt) ju

------------------------------------------------------------------------
-- Various subset properties

x∷xs≡y∷ys⇒x≡y : {n : ℕ} {xs ys : Subset n} {x y : Bool} → (x ∷ xs) ≡ (y ∷ ys) → x ≡ y
x∷xs≡y∷ys⇒x≡y {n} {xs} {.xs} {x} {.x} refl = refl

x∷xs≡y∷ys⇒xs≡ys : {n : ℕ} {xs ys : Subset n} {x y : Bool} → (x ∷ xs) ≡ (y ∷ ys) → xs ≡ ys
x∷xs≡y∷ys⇒xs≡ys {n} {xs} {.xs} {x} {.x} refl = refl

empty-subset-outside : {n : ℕ} → (x : Fin n) → ¬ (⊥ [ x ]= inside)
empty-subset-outside {.(ℕ.suc _)} zero ()
empty-subset-outside {.(ℕ.suc _)} (Fin.suc x) (there ins) = empty-subset-outside x ins

x∈[l]⇒x≡l : {n : ℕ} {x l : Fin n} → x ∈ ⁅ l ⁆ → x ≡ l
x∈[l]⇒x≡l {.(ℕ.suc _)} {zero} {zero} ins = refl
x∈[l]⇒x≡l {.(ℕ.suc _)} {Fin.suc x} {zero} (there ins) = contradiction ins (empty-subset-outside x)
x∈[l]⇒x≡l {.(ℕ.suc _)} {Fin.suc x} {Fin.suc l} (there ins) = cong Fin.suc (x∈[l]⇒x≡l ins)

l∈L⇒[l]⊆L : {n : ℕ} {l : Fin n} {L : Subset n} → l ∈ L → ⁅ l ⁆ ⊆ L
l∈L⇒[l]⊆L {n} {l} {L} ins x rewrite (x∈[l]⇒x≡l x) = ins

[l]⊆L⇒l∈L : {n : ℕ} {l : Fin n} {L : Subset n} → ⁅ l ⁆ ⊆ L → l ∈ L 
[l]⊆L⇒l∈L {n} {l} {L} sub = sub (x∈⁅x⁆ l)

in-subset-uniqueness : {n : ℕ} {x : Fin n} {s : Subset n} → (l l' : x ∈ s) → l ≡ l'
in-subset-uniqueness {.(ℕ.suc _)} {.zero} here here = refl
in-subset-uniqueness {.(ℕ.suc _)} {.(Fin.suc _)} (there l) (there l') = cong there (in-subset-uniqueness l l')

------------------------------------------------------------------------
-- Decidable equality of functions (f : l → l ∈ s → A)

dec-manipulate : {n : ℕ} {A : Set} → (dec : (a a' : A) → Dec (a ≡ a')) → ((a a' : A ⊎ ⊤) → Dec (a ≡ a'))
dec-manipulate {n} {A} dec (inj₁ x) (inj₁ x₁)
  with dec x x₁
...  | yes p = yes (cong inj₁ p)
...  | no ¬p = no λ x₂ → contradiction (sum-eq x₂) ¬p
dec-manipulate {n} {A} dec (inj₁ x) (inj₂ y) = no λ ()
dec-manipulate {n} {A} dec (inj₂ y) (inj₁ x) = no λ ()
dec-manipulate {n} {A} dec (inj₂ tt) (inj₂ tt) = yes (cong inj₂ refl)

f-manipulate : {n : ℕ} {A : Set} {s : Subset n} → ((l : Fin n) → l ∈ s → A) → (Fin n → (A ⊎ ⊤))
f-manipulate {n} {A} {s} f l
  with l ∈? s
...  | yes p = inj₁ (f l p)
...  | no ¬p = inj₂ tt

f-equal : {n : ℕ} {A : Set} {dec : (a a' : A) → Dec (a ≡ a')} → (f f' : (l : Fin n) → A) → Dec (f ≡ f')
f-equal {n} {A} {dec} f f'
  with all?{n} λ x → dec (f x) (f' x)
...  | yes p = yes (ext p)
...  | no ¬p = no λ x → contradiction (cong-app x) ¬p

f-manipulate-eq⇒f-eq : {n : ℕ} {A : Set} {s : Subset n} {f f' : (l : Fin n) → l ∈ s → A} → (f-manipulate f) ≡ (f-manipulate f') → f ≡ f'
f-manipulate-eq⇒f-eq {n} {A} {s} {f} {f'} eq
  with (cong-app eq)
...  | eq' = ext (λ x → ext (ϱ x))
     where ϱ : (l : Fin n) → (i : l ∈ s) → f l i ≡ f' l i
           ϱ l i
             with (eq' l)
           ...  | eq''
                with l ∈? s
           ...     | yes p rewrite (in-subset-uniqueness i p) = sum-eq eq''
           ...     | no ¬p = contradiction i ¬p

f-eq⇒f-manipulate-eq : {n : ℕ} {A : Set} {s : Subset n} {f f' : (l : Fin n) → l ∈ s → A} → f ≡ f' → (f-manipulate f) ≡ (f-manipulate f')
f-eq⇒f-manipulate-eq {n} {A} {s} {f} {f'} eq
  with (cong-app eq)
...  | eq' = ext (λ x → ϱ x)
     where ϱ : (l : Fin n) → (f-manipulate f l) ≡ (f-manipulate f' l)
           ϱ l
             with (eq' l)
           ...  | eq''
                 with l ∈? s
           ...      | yes p = cong inj₁ ((cong-app eq'') p)
           ...      | no ¬p = refl

_≡ᶠ?_ : {n : ℕ} {s : Subset n} {A : Set} {dec : (a a' : A) → Dec (a ≡ a')} (f f' : (l : Fin n) → s Data.Vec.[ l ]= inside → A) → Dec (f ≡ f')
_≡ᶠ?_ {n} {s} {A} {dec} f f'
  with (f-equal{dec = dec-manipulate{n} dec} (f-manipulate f) (f-manipulate f'))
...     | yes p = yes (f-manipulate-eq⇒f-eq p)
...     | no ¬p = no (contraposition f-eq⇒f-manipulate-eq ¬p)

------------------------------------------------------------------------
-- Decidable subset equality

_≡ˢ?_ : {n : ℕ} → (s s' : Subset n) → Dec (s ≡ s')
_≡ˢ?_ {zero} [] [] = yes refl
_≡ˢ?_ {suc n} (x ∷ s) (x₁ ∷ s')
  with _≡ˢ?_ {n} s s' | x Data.Bool.Properties.≟ x₁
...  | yes p | yes p' rewrite p | p' = yes refl
...  | yes p | no ¬p' rewrite p = no λ x₂ → contradiction (x∷xs≡y∷ys⇒x≡y x₂) ¬p'
...  | no ¬p | _ = no (λ x₂ → contradiction (x∷xs≡y∷ys⇒xs≡ys x₂) ¬p)



