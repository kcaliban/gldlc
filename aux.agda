module aux where

open import Data.Nat
open import Data.Fin
open import Data.Fin.Subset renaming (∣_∣ to ∣_∣ˢ)
open import Data.Fin.Subset.Properties
open import Data.Vec
open import Data.Bool
open import Data.Bool.Properties
open import Relation.Nullary
open import Relation.Nullary.Negation
open import Relation.Binary.PropositionalEquality

x∷xs≡y∷ys⇒x≡y : {n : ℕ} {xs ys : Subset n} {x y : Bool} → (x ∷ xs) ≡ (y ∷ ys) → x ≡ y
x∷xs≡y∷ys⇒x≡y {n} {xs} {.xs} {x} {.x} refl = refl

x∷xs≡y∷ys⇒xs≡ys : {n : ℕ} {xs ys : Subset n} {x y : Bool} → (x ∷ xs) ≡ (y ∷ ys) → xs ≡ ys
x∷xs≡y∷ys⇒xs≡ys {n} {xs} {.xs} {x} {.x} refl = refl

_≡ˢ?_ : {n : ℕ} → (s s' : Subset n) → Dec (s ≡ s')
_≡ˢ?_ {zero} [] [] = yes refl
_≡ˢ?_ {suc n} (x ∷ s) (x₁ ∷ s')
  with _≡ˢ?_ {n} s s' | x Data.Bool.Properties.≟ x₁
...  | yes p | yes p' rewrite p | p' = yes refl
...  | yes p | no ¬p' rewrite p = no λ x₂ → contradiction (x∷xs≡y∷ys⇒x≡y x₂) ¬p'
...  | no ¬p | _ = no (λ x₂ → contradiction (x∷xs≡y∷ys⇒xs≡ys x₂) ¬p)

empty-subset-outside : {n : ℕ} → (x : Fin n) → ¬ (⊥ [ x ]= inside)
empty-subset-outside {.(ℕ.suc _)} zero ()
empty-subset-outside {.(ℕ.suc _)} (Fin.suc x) (there ins) = empty-subset-outside x ins

x∈[l]⇒x≡l : {n : ℕ} {x l : Fin n} → x ∈ ⁅ l ⁆ → x ≡ l
x∈[l]⇒x≡l {.(ℕ.suc _)} {zero} {zero} ins = refl
x∈[l]⇒x≡l {.(ℕ.suc _)} {Fin.suc x} {zero} (there ins) = contradiction ins (empty-subset-outside x)
x∈[l]⇒x≡l {.(ℕ.suc _)} {Fin.suc x} {Fin.suc l} (there ins) = cong Fin.suc (x∈[l]⇒x≡l ins)

l∈L⇒[l]⊆L : {n : ℕ} {l : Fin n} {L : Subset n} → l ∈ L → ⁅ l ⁆ ⊆ L
l∈L⇒[l]⊆L {n} {l} {L} ins x rewrite (x∈[l]⇒x≡l x) = ins
