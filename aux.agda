module aux where

open import Data.Nat
open import Data.Fin
open import Data.Fin.Subset renaming (∣_∣ to ∣_∣ˢ)
open import Data.Vec
open import Relation.Nullary
open import Relation.Nullary.Negation
open import Relation.Binary.PropositionalEquality

empty-subset-outside : {n : ℕ} → (x : Fin n) → ¬ (⊥ [ x ]= inside)
empty-subset-outside {.(ℕ.suc _)} zero ()
empty-subset-outside {.(ℕ.suc _)} (Fin.suc x) (there ins) = empty-subset-outside x ins

x∈[l]⇒x≡l : {n : ℕ} {x l : Fin n} → x ∈ ⁅ l ⁆ → x ≡ l
x∈[l]⇒x≡l {.(ℕ.suc _)} {zero} {zero} ins = refl
x∈[l]⇒x≡l {.(ℕ.suc _)} {Fin.suc x} {zero} (there ins) = contradiction ins (empty-subset-outside x)
x∈[l]⇒x≡l {.(ℕ.suc _)} {Fin.suc x} {Fin.suc l} (there ins) = cong Fin.suc (x∈[l]⇒x≡l ins)

l∈L⇒[l]⊆L : {n : ℕ} {l : Fin n} {L : Subset n} → l ∈ L → ⁅ l ⁆ ⊆ L
l∈L⇒[l]⊆L {n} {l} {L} ins x rewrite (x∈[l]⇒x≡l x) = ins
