------------------------------------------------------------------------
-- Determinism of reduction relation
------------------------------------------------------------------------

{-# OPTIONS --sized-types #-}
module Determinism-of-Reduction where

open import Data.Nat renaming (_+_ to _+ᴺ_ ; _≤_ to _≤ᴺ_ ; _≥_ to _≥ᴺ_ ; _<_ to _<ᴺ_ ; _>_ to _>ᴺ_ ; _≟_ to _≟ᴺ_)
open import Data.Integer renaming (_+_ to _+ᶻ_ ; _≤_ to _≤ᶻ_ ; _≥_ to _≥ᶻ_ ; _<_ to _<ᶻ_ ; _>_ to _>ᶻ_ ; ∣_∣ to ∣_∣ᴺ)
open import Data.Fin hiding (cast)
open import Data.Fin.Properties
open import Data.Vec hiding (_++_ ; length)
open import Data.Fin.Subset renaming (∣_∣ to ∣_∣ˢ ; ⊤ to ⊤ˢ ; ⊥ to ⊥ˢ)
open import Data.Fin.Subset.Properties
open import Data.List hiding (_++_ ; length)
open import Data.List.Relation.Unary.All
open import Relation.Nullary
open import Relation.Nullary.Negation
open import Relation.Binary.PropositionalEquality renaming (trans to ≡-trans)
open import Data.Product
open import Data.Sum
open import Relation.Nullary.Decidable
open import Data.Maybe
open import Data.Maybe.Relation.Unary.All renaming (All to Allᵐ)
open import Data.Maybe.Relation.Unary.Any renaming (Any to Anyᵐ)
open import Data.Unit using (⊤)
open import Data.Empty
open import Size renaming (↑_ to ↑ˡ)

open import Aux

open import Syntax
open import Substitution
open import Typing-Semantics

⇨-determinism : {n : ℕ} {e e' e'' : Exp {n}} → e ⇨ e' → e ⇨ e'' → e' ≡ e''
⇨-determinism {n} {.(App _ _)} {.(App _ _)} {.(App _ _)} (ξ-App₁ r) (ξ-App₁ r') = cong₂ App (⇨-determinism r r') refl
⇨-determinism {n} {.(App _ _)} {.(App _ _)} {.(App _ _)} (ξ-App₁{e₁' = e₁'} r) (ξ-App₂{v = v} r') = contradiction r (⇨-Val-noreduce v e₁')
⇨-determinism {n} {(App (Cast e (Pi A B) (Pi A' B')) e')} {.(App _ _)} {.(Cast (App _ (Cast _ _ _)) ([ 0 ↦ Cast _ _ _ ]ᵀ _) ([ 0 ↦ _ ]ᵀ _))} (ξ-App₁{e₁' = e₁'} r) (Cast-Func{v = v}) = contradiction r (⇨-Val-noreduce (VCastFun v) e₁')
⇨-determinism {n} {.(App _ Blame)} {.(App _ Blame)} {.Blame} (ξ-App₁{e₁' = e₁'} r) (App₂-Blame{v = v}) = contradiction r (⇨-Val-noreduce v e₁')

⇨-determinism {n} {.(App _ _)} {.(App _ _)} {.(App _ _)} (ξ-App₂{v = v} r) (ξ-App₁{e₁' = e₁'} r') = contradiction r' (⇨-Val-noreduce v e₁')
⇨-determinism {n} {.(App _ _)} {.(App _ _)} {.(App _ _)} (ξ-App₂ r) (ξ-App₂ r') = cong₂ App refl (⇨-determinism r r')
⇨-determinism {n} {.(App (Abs _) _)} {.(App (Abs _) _)} {e*} (ξ-App₂{e₂' = e₂'} r) (β-App v) = contradiction r (⇨-Val-noreduce v e₂')
⇨-determinism {n} {.(App (Cast _ (Pi _ _) (Pi _ _)) _)} {.(App (Cast _ (Pi _ _) (Pi _ _)) _)} {.(Cast (App _ (Cast _ _ _)) ([ 0 ↦ Cast _ _ _ ]ᵀ _) ([ 0 ↦ _ ]ᵀ _))} (ξ-App₂{e₂' = e₂'} r) (Cast-Func{w = w}) = contradiction r (⇨-Val-noreduce w e₂')

⇨-determinism {n} {.(LetE _ _)} {.(LetE _ _)} {.(LetE _ _)} (ξ-LetE r) (ξ-LetE r') = cong₂ LetE (⇨-determinism r r') refl
⇨-determinism {n} {.(LetE _ _)} {.(LetE _ _)} {e*} (ξ-LetE{e₁' = e₁'} r) (β-LetE v) = contradiction r (⇨-Val-noreduce v e₁')

⇨-determinism {n} {.(Prod _ _)} {.(Prod _ _)} {.(Prod _ _)} (ξ-Prod r) (ξ-Prod r') = cong₂ Prod (⇨-determinism r r') refl
⇨-determinism {n} {.(Prod _ _)} {.(Prod _ _)} {.(ProdV _ ↑⁻¹[ [ 0 ↦ ↑¹[ _ ] ] _ ])} (ξ-Prod{e₁' = e₁'} r) (β-Prod{v = v}) = contradiction r (⇨-Val-noreduce v e₁')

⇨-determinism {n} {.(ProdV _ _)} {.(ProdV _ _)} {.(ProdV _ _)} (ξ-ProdV r) (ξ-ProdV r') = cong₂ ProdV refl (⇨-determinism r r')

⇨-determinism {n} {.(LetP _ _)} {.(LetP _ _)} {.(LetP _ _)} (ξ-LetP r) (ξ-LetP r') = cong₂ LetP (⇨-determinism r r') refl
⇨-determinism {n} {.(LetP (ProdV _ _) _)} {.(LetP _ _)} {.(↑ -[1+ 1 ] , 0 [ [ 0 ↦ ↑¹[ _ ] ] ([ 0 ↦ ↑ + 1 , 1 [ _ ] ] _) ])} (ξ-LetP{e₁' = e₁'} r) (β-LetP v v') = contradiction r (⇨-Val-noreduce (VProd v v') e₁')

⇨-determinism {n} {.(Cast _ _ _)} {.(Cast _ _ _)} {.(Cast _ _ _)} (ξ-Cast r) (ξ-Cast r') = cong₃ Cast (⇨-determinism r r') refl refl
⇨-determinism {n} {.(Cast e'' Dyn Dyn)} {.(Cast _ Dyn Dyn)} {e''} (ξ-Cast{e₂ = e₂} r) (Cast-Dyn{v = v}) = contradiction r (⇨-Val-noreduce v e₂)
⇨-determinism {n} {.(Cast e'' _ _)} {.(Cast _ _ _)} {e''} (ξ-Cast{e₂ = e₂} r) (Cast-Sub{v = v} x) = contradiction r (⇨-Val-noreduce v e₂)
⇨-determinism {n} {.(Cast _ _ _)} {.(Cast _ _ _)} {.Blame} (ξ-Cast{e₂ = e₂} r) (Cast-Fail{v = v} x) = contradiction r (⇨-Val-noreduce v e₂)
⇨-determinism {n} {.(Cast (Cast e'' _ Dyn) Dyn _)} {.(Cast _ Dyn _)} {e''} (ξ-Cast{e₂ = e₂} r) (Cast-Collapse{v = v}{tygG = tygG} x) = contradiction r (⇨-Val-noreduce (VCast v tygG) e₂)
⇨-determinism {n} {.(Cast (Cast _ _ Dyn) Dyn _)} {.(Cast _ Dyn _)} {.Blame} (ξ-Cast{e₂ = e₂} r) (Cast-Collide{v = v}{tygG = tygG} x) = contradiction r (⇨-Val-noreduce (VCast v tygG) e₂)
⇨-determinism {n} {.(Cast (ProdV _ _) (Sigma _ _) (Sigma _ _))} {.(Cast _ (Sigma _ _) (Sigma _ _))} {.(Prod (Cast _ _ _) (Cast _ _ _))} (ξ-Cast{e₂ = e₂} r) (Cast-Pair{v = v}{w = w}) = contradiction r (⇨-Val-noreduce (VProd v w) e₂)
⇨-determinism {n} {.(Cast _ _ _)} {.(Cast _ _ _)} {.(Cast _ _ _)} (ξ-Cast{e₂ = e₂} r) (Cast-Reduce-L{v = v} x) = contradiction r (⇨-Val-noreduce v e₂)
⇨-determinism {n} {.(Cast _ _ _)} {.(Cast _ _ _)} {.(Cast _ _ _)} (ξ-Cast{e₂ = e₂} r) (Cast-Reduce-R{v = v} x x₁) = contradiction r (⇨-Val-noreduce v e₂)
⇨-determinism {n} {.(Cast _ _ Dyn)} {.(Cast _ _ Dyn)} {.(Cast (Cast _ _ (proj₁ (_ match))) (proj₁ (_ match)) Dyn)} (ξ-Cast{e₂ = e₂} r) (Cast-Factor-L{v = v} neq) = contradiction r (⇨-Val-noreduce v e₂)
⇨-determinism {n} {.(Cast _ Dyn _)} {.(Cast _ Dyn _)} {.(Cast (Cast _ Dyn (proj₁ (_ match))) (proj₁ (_ match)) _)} (ξ-Cast{e₂ = e₂} r) (Cast-Factor-R{v = v} neq) = contradiction r (⇨-Val-noreduce v e₂)
⇨-determinism {n} {.(Cast _ _ Bot)} {.(Cast _ _ Bot)} {.Blame} (ξ-Cast{e₂ = e₂} r) (Cast-Bot-R{v = v} x) = contradiction r (⇨-Val-noreduce v e₂)

⇨-determinism {n} {.(CaseE _ _)} {.(CaseE _ _)} {.(CaseE _ _)} (ξ-Case r) (ξ-Case r') = cong₂ CaseE (⇨-determinism r r') refl

⇨-determinism {n} {.(App (Abs _) _)} {e*} {.(App (Abs _) _)} (β-App v) (ξ-App₂{e₂' = e₂'} r') = contradiction r' (⇨-Val-noreduce v e₂')
⇨-determinism {n} {.(App (Abs _) _)} {e*} {e*} (β-App v) (β-App v₁) = refl

⇨-determinism {n} {.(Prod _ _)} {.(ProdV _ ↑⁻¹[ [ 0 ↦ ↑¹[ _ ] ] _ ])} {.(Prod _ _)} (β-Prod{v = v}) (ξ-Prod{e₁' = e₁'} r') = contradiction r' (⇨-Val-noreduce v e₁')
⇨-determinism {n} {.(Prod _ _)} {.(ProdV _ ↑⁻¹[ [ 0 ↦ ↑¹[ _ ] ] _ ])} {.(ProdV _ ↑⁻¹[ [ 0 ↦ ↑¹[ _ ] ] _ ])} β-Prod β-Prod = refl

⇨-determinism {n} {.(LetE _ _)} {e*} {.(LetE _ _)} (β-LetE v) (ξ-LetE{e₁' = e₁'} r') = contradiction r' (⇨-Val-noreduce v e₁')
⇨-determinism {n} {.(LetE _ _)} {e*} {e*} (β-LetE v) (β-LetE v₁) = refl

⇨-determinism {n} {.(LetP (ProdV _ _) _)} {.(↑ -[1+ 1 ] , 0 [ [ 0 ↦ ↑¹[ _ ] ] ([ 0 ↦ ↑ + 1 , 1 [ _ ] ] _) ])} {.(LetP _ _)} (β-LetP v v') (ξ-LetP{e₁' = e₁'} r') = contradiction r' (⇨-Val-noreduce (VProd v v') e₁')
⇨-determinism {n} {.(LetP (ProdV _ _) _)} {.(↑ -[1+ 1 ] , 0 [ [ 0 ↦ ↑¹[ _ ] ] ([ 0 ↦ ↑ + 1 , 1 [ _ ] ] _) ])} {.(↑ -[1+ 1 ] , 0 [ [ 0 ↦ ↑¹[ _ ] ] ([ 0 ↦ ↑ + 1 , 1 [ _ ] ] _) ])} (β-LetP v v') (β-LetP v₁ v'') = refl

⇨-determinism {n} {.(CaseE (LabI _) _)} {.(_ _ ins)} {.(_ _ ins₁)} (β-LabE ins) (β-LabE ins₁) rewrite (ins-refl ins ins₁) = refl

⇨-determinism {n} {.(Cast e' Dyn Dyn)} {e'} {.(Cast _ Dyn Dyn)} (Cast-Dyn{v = v}) (ξ-Cast{e₂ = e₂} r') = contradiction r' (⇨-Val-noreduce v e₂)
⇨-determinism {n} {.(Cast e' Dyn Dyn)} {e'} {.e'} Cast-Dyn Cast-Dyn = refl
⇨-determinism {n} {.(Cast e' Dyn Dyn)} {e'} {.Blame} Cast-Dyn (Cast-Fail{tynfA = ()} x)
⇨-determinism {n} {.(Cast e' Dyn Dyn)} {e'} {.(Cast (Cast e' Dyn (proj₁ (_ match))) (proj₁ (_ match)) Dyn)} Cast-Dyn (Cast-Factor-L{nfA = ()} neq)
⇨-determinism {n} {.(Cast e' Dyn Dyn)} {e'} {.(Cast (Cast e' Dyn (proj₁ (_ match))) (proj₁ (_ match)) Dyn)} Cast-Dyn (Cast-Factor-R{nfB = ()} neq)

⇨-determinism {n} {.(Cast e' _ _)} {e'} {.(Cast _ _ _)} (Cast-Sub{v = v} x) (ξ-Cast{e₂ = e₂} r') = contradiction r' (⇨-Val-noreduce v e₂)
⇨-determinism {n} {.(Cast e' _ _)} {e'} {.e'} (Cast-Sub x) (Cast-Sub x₁) = refl
⇨-determinism {n} {.(Cast e' _ _)} {e'} {.Blame} (Cast-Sub{v = v}{tygG = tygG}{tygH = tygH} x) (Cast-Fail{tynfA = tynfA}{tynfB = tynfB} x₁)
  rewrite (TyG×TyNf-lim⇒match-equiv tygG tynfA) | (TyG×TyNf-lim⇒match-equiv tygH tynfB) = contradiction x x₁
⇨-determinism {n} {.(Cast (ProdV _ _) (Sigma _ _) (Sigma _ _))} {.(ProdV _ _)} {.(Prod (Cast _ _ _) (Cast _ _ _))} (Cast-Sub{v = v}{tygG = GSigma}{neqG = neq , neq'} x) (Cast-Pair) = contradiction refl neq'
⇨-determinism {n} {.(Cast e' _ _)} {e'} {.(Cast e' _ _)} (Cast-Sub{v = v}{tygG = tygG}{tygH = tygH} x) (Cast-Reduce-L{A' = A'} x₁) = contradiction x₁ (↠-TyNf-noreduce (TyG⊂TyNf tygG) A')
⇨-determinism {n} {.(Cast e' _ _)} {e'} {.(Cast e' _ _)} (Cast-Sub{v = v}{tygG = tygG}{tygH = tygH} x) (Cast-Reduce-R{B' = B'} x₁ x₂) = contradiction x₂ (↠-TyNf-noreduce (TyG⊂TyNf tygH) B')

⇨-determinism {n} {.(Cast _ _ _)} {.Blame} {.(Cast _ _ _)} (Cast-Fail{v = v} x) (ξ-Cast{e₂ = e₂} r') = contradiction r' (⇨-Val-noreduce v e₂)
⇨-determinism {n} {.(Cast e'' Dyn Dyn)} {.Blame} {e''} (Cast-Fail{v = v}{tynfA = ()} x) Cast-Dyn
⇨-determinism {n} {.(Cast e'' _ _)} {.Blame} {e''} (Cast-Fail{tynfA = tynfA}{tynfB = tynfB} x₁) (Cast-Sub{v = v}{tygG = tygG}{tygH = tygH} x)
  rewrite (TyG×TyNf-lim⇒match-equiv tygG tynfA) | (TyG×TyNf-lim⇒match-equiv tygH tynfB) = contradiction x x₁
⇨-determinism {n} {.(Cast _ _ _)} {.Blame} {.Blame} (Cast-Fail{v = v} x) (Cast-Fail x₁) = refl
⇨-determinism {n} {.(Cast (Cast e'' _ Dyn) Dyn _)} {.Blame} {e''} (Cast-Fail{v = v}{tynfA = ()} x) (Cast-Collapse x₁)
⇨-determinism {n} {.(Cast (Cast _ _ Dyn) Dyn _)} {.Blame} {.Blame} (Cast-Fail{v = v}{tynfA = ()} x) (Cast-Collide x₁)
⇨-determinism {n} {.(Cast (ProdV _ _) (Sigma _ _) (Sigma _ _))} {.Blame} {.(Prod (Cast _ _ _) (Cast _ _ _))} (Cast-Fail{v = v}{tynfA = NfSigma}{tynfB = NfSigma} x) Cast-Pair = contradiction (ASubSigma ASubDyn ASubDyn) x
⇨-determinism {n} {.(Cast _ _ _)} {.Blame} {.(Cast _ _ _)} (Cast-Fail{v = v}{tynfA = nfA} x) (Cast-Reduce-L{A' = A'} x₁) = contradiction x₁ (↠-TyNf-noreduce (TyNf-lim⊂TyNf nfA) A')
⇨-determinism {n} {.(Cast _ _ _)} {.Blame} {.(Cast _ _ _)} (Cast-Fail{v = v}{tynfB = nfB} x) (Cast-Reduce-R{B' = B'} x₁ x₂) = contradiction x₂ (↠-TyNf-noreduce (TyNf-lim⊂TyNf nfB) B')
⇨-determinism {n} {.(Cast _ _ Dyn)} {.Blame} {.(Cast (Cast _ _ (proj₁ (_ match))) (proj₁ (_ match)) Dyn)} (Cast-Fail{v = v}{tynfB = ()} x) (Cast-Factor-L neq)
⇨-determinism {n} {.(Cast _ Dyn _)} {.Blame} {.(Cast (Cast _ Dyn (proj₁ (_ match))) (proj₁ (_ match)) _)} (Cast-Fail{v = v}{tynfA = ()} x) (Cast-Factor-R neq)
⇨-determinism {n} {.(Cast _ _ Bot)} {.Blame} {.Blame} (Cast-Fail{v = v}{tynfB = ()} x) (Cast-Bot-R x₁)

⇨-determinism {n} {.(Cast (Cast e' _ Dyn) Dyn _)} {e'} {.(Cast _ Dyn _)} (Cast-Collapse{v = v}{tygG = tygG} x) (ξ-Cast{e₂ = e₂} r') = contradiction r' (⇨-Val-noreduce (VCast v tygG) e₂)
⇨-determinism {n} {.(Cast (Cast e' _ Dyn) Dyn _)} {e'} {.Blame} (Cast-Collapse x) (Cast-Fail{tynfA = ()} x₁)
⇨-determinism {n} {.(Cast (Cast e' _ Dyn) Dyn _)} {e'} {.e'} (Cast-Collapse x) (Cast-Collapse x₁) = refl
⇨-determinism {n} {.(Cast (Cast e' _ Dyn) Dyn _)} {e'} {.Blame} (Cast-Collapse x) (Cast-Collide x₁) = contradiction x x₁
⇨-determinism {n} {.(Cast (Cast e' _ Dyn) Dyn _)} {e'} {.(Cast (Cast e' _ Dyn) Dyn _)} (Cast-Collapse{tygH = tygH} x) (Cast-Reduce-R{B' = B'} x₁ x₂) = contradiction x₂ ((↠-TyNf-noreduce (TyG⊂TyNf tygH) B'))
⇨-determinism {n} {.(Cast (Cast e' _ Dyn) Dyn _)} {e'} {e''} (Cast-Collapse{tygH = tygH} x) (Cast-Factor-R{nfB = tynfH} neq) = contradiction (sym (TyG×TyNf-lim⇒match-equiv tygH tynfH)) neq

⇨-determinism {n} {.(Cast (Cast _ _ Dyn) Dyn _)} {.Blame} {.(Cast _ Dyn _)} (Cast-Collide{v = v}{tygG = tygG} x) (ξ-Cast{e₂ = e₂} r') = contradiction r' (⇨-Val-noreduce (VCast v tygG) e₂)
⇨-determinism {n} {.(Cast (Cast _ _ Dyn) Dyn _)} {.Blame} {.Blame} (Cast-Collide x) (Cast-Fail{tynfA = ()} x₁)
⇨-determinism {n} {.(Cast (Cast e'' _ Dyn) Dyn _)} {.Blame} {e''} (Cast-Collide x) (Cast-Collapse x₁) = contradiction x₁ x
⇨-determinism {n} {.(Cast (Cast _ _ Dyn) Dyn _)} {.Blame} {.Blame} (Cast-Collide x) (Cast-Collide x₁) = refl
⇨-determinism {n} {.(Cast (Cast _ _ Dyn) Dyn _)} {.Blame} {.(Cast (Cast _ _ Dyn) Dyn _)} (Cast-Collide{tygH = tygH} x) (Cast-Reduce-R{B' = B'} x₁ x₂) = contradiction x₂ ((↠-TyNf-noreduce (TyG⊂TyNf tygH) B'))
⇨-determinism {n} {.(Cast (Cast _ _ Dyn) Dyn _)} {.Blame} {.(Cast (Cast (Cast _ _ Dyn) Dyn (proj₁ (_ match))) (proj₁ (_ match)) _)} (Cast-Collide{tygH = tygH} x) (Cast-Factor-R{nfB = tynfH} neq) = contradiction (sym (TyG×TyNf-lim⇒match-equiv tygH tynfH)) neq

⇨-determinism {n} {.(Cast (ProdV _ _) (Sigma _ _) (Sigma _ _))} {.(Prod (Cast _ _ _) (Cast _ _ _))} {.(Cast _ (Sigma _ _) (Sigma _ _))} (Cast-Pair{v = v}{w = w}) (ξ-Cast{e₂ = e₂} r') = contradiction r' (⇨-Val-noreduce (VProd v w) e₂)
⇨-determinism {n} {.(Cast (ProdV _ _) (Sigma _ _) (Sigma _ _))} {.(Prod (Cast _ _ _) (Cast _ _ _))} {.(ProdV _ _)} Cast-Pair (Cast-Sub{tygG = GSigma}{tygH = GSigma}{neqH = neq , neq'} x) = contradiction refl neq'
⇨-determinism {n} {.(Cast (ProdV _ _) (Sigma _ _) (Sigma _ _))} {.(Prod (Cast _ _ _) (Cast _ _ _))} {.Blame} Cast-Pair (Cast-Fail{tynfA = NfSigma}{tynfB = NfSigma} neq) = contradiction (ASubSigma ASubDyn ASubDyn) neq
⇨-determinism {n} {.(Cast (ProdV _ _) (Sigma _ _) (Sigma _ _))} {.(Prod (Cast _ _ _) (Cast _ _ _))} {.(Prod (Cast _ _ _) (Cast _ _ _))} Cast-Pair Cast-Pair = refl

⇨-determinism {n} {.(App (Cast _ (Pi _ _) (Pi _ _)) _)} {.(Cast (App _ (Cast _ _ _)) ([ 0 ↦ Cast _ _ _ ]ᵀ _) ([ 0 ↦ _ ]ᵀ _))} {.(App _ _)} (Cast-Func{v = v}) (ξ-App₁{e₁' = e₁'} r') = contradiction r' (⇨-Val-noreduce (VCastFun v ) e₁')
⇨-determinism {n} {.(App (Cast _ (Pi _ _) (Pi _ _)) _)} {.(Cast (App _ (Cast _ _ _)) ([ 0 ↦ Cast _ _ _ ]ᵀ _) ([ 0 ↦ _ ]ᵀ _))} {.(App (Cast _ (Pi _ _) (Pi _ _)) _)} (Cast-Func{w = w}) (ξ-App₂{e₂' = e₂'} r') = contradiction r' (⇨-Val-noreduce w e₂')
⇨-determinism {n} {.(App (Cast _ (Pi _ _) (Pi _ _)) _)} {.(Cast (App _ (Cast _ _ _)) ([ 0 ↦ Cast _ _ _ ]ᵀ _) ([ 0 ↦ _ ]ᵀ _))} {.(Cast (App _ (Cast _ _ _)) ([ 0 ↦ Cast _ _ _ ]ᵀ _) ([ 0 ↦ _ ]ᵀ _))} Cast-Func Cast-Func = refl

⇨-determinism {n} {.(Cast _ _ _)} {.(Cast _ _ _)} {.(Cast _ _ _)} (Cast-Reduce-L{v = v} x) (ξ-Cast{e₂ = e₂} r') = contradiction r' (⇨-Val-noreduce v e₂)
⇨-determinism {n} {.(Cast e'' _ _)} {.(Cast e'' _ _)} {e''} (Cast-Reduce-L{A' = A'} x) (Cast-Sub{tygG = tygA} x₁) = contradiction x (↠-TyNf-noreduce (TyG⊂TyNf tygA) A')
⇨-determinism {n} {.(Cast _ _ _)} {.(Cast _ _ _)} {.Blame} (Cast-Reduce-L{A' = A'} x) (Cast-Fail{tynfA = tynfA} x₁) = contradiction x (↠-TyNf-noreduce (TyNf-lim⊂TyNf tynfA) A')
⇨-determinism {n} {.(Cast _ _ _)} {.(Cast _ _ _)} {.(Cast _ _ _)} (Cast-Reduce-L x) (Cast-Reduce-L x₁) = {!!}
⇨-determinism {n} {.(Cast _ _ _)} {.(Cast _ _ _)} {.(Cast _ _ _)} (Cast-Reduce-L{A' = A'} x) (Cast-Reduce-R x₁ x₂) = contradiction x (↠-TyNf-noreduce x₁ A')
⇨-determinism {n} {.(Cast _ _ Dyn)} {.(Cast _ _ Dyn)} {.(Cast (Cast _ _ (proj₁ (_ match))) (proj₁ (_ match)) Dyn)} (Cast-Reduce-L{A' = A'} x) (Cast-Factor-L{nfA = tynfA} neq) = contradiction x (↠-TyNf-noreduce (TyNf-lim⊂TyNf tynfA) A')
⇨-determinism {n} {.(Cast _ _ Bot)} {.(Cast _ _ Bot)} {.Blame} (Cast-Reduce-L{A' = A'} x) (Cast-Bot-R x₁) = contradiction x (↠-TyNf-noreduce x₁ A')

⇨-determinism {n} {.(Cast _ _ _)} {.(Cast _ _ _)} {.(Cast _ _ _)} (Cast-Reduce-R{v = v} x x₁) (ξ-Cast{e₂ = e₂} r') = contradiction r' (⇨-Val-noreduce v e₂)
⇨-determinism {n} {.(Cast e'' _ _)} {.(Cast e'' _ _)} {e''} (Cast-Reduce-R{B' = B'} x x₁) (Cast-Sub{tygH = tygB} x₂) = contradiction x₁ (↠-TyNf-noreduce (TyG⊂TyNf tygB) B')
⇨-determinism {n} {.(Cast _ _ _)} {.(Cast _ _ _)} {.Blame} (Cast-Reduce-R{B' = B'} x x₁) (Cast-Fail{tynfB = tynfB} x₂) = contradiction x₁ (↠-TyNf-noreduce (TyNf-lim⊂TyNf tynfB) B')
⇨-determinism {n} {.(Cast (Cast e'' _ Dyn) Dyn _)} {.(Cast (Cast e'' _ Dyn) Dyn _)} {e''} (Cast-Reduce-R{B' = B'} x x₁) (Cast-Collapse{tygH = tygB} x₂) = contradiction x₁ (↠-TyNf-noreduce (TyG⊂TyNf tygB) B')
⇨-determinism {n} {.(Cast (Cast _ _ Dyn) Dyn _)} {.(Cast (Cast _ _ Dyn) Dyn _)} {.Blame} (Cast-Reduce-R{B' = B'} x x₁) (Cast-Collide{tygH = tygB} x₂) = contradiction x₁ (↠-TyNf-noreduce (TyG⊂TyNf tygB) B')
⇨-determinism {n} {.(Cast _ _ _)} {.(Cast _ _ _)} {.(Cast _ _ _)} (Cast-Reduce-R x x₁) (Cast-Reduce-L{A' = A'} x₂) = contradiction x₂ (↠-TyNf-noreduce x A')
⇨-determinism {n} {.(Cast _ _ _)} {.(Cast _ _ _)} {.(Cast _ _ _)} (Cast-Reduce-R x x₁) (Cast-Reduce-R x₂ x₃) = {!!}
⇨-determinism {n} {.(Cast _ Dyn _)} {.(Cast _ Dyn _)} {.(Cast (Cast _ Dyn (proj₁ (_ match))) (proj₁ (_ match)) _)} (Cast-Reduce-R{B' = B'} x x₁) (Cast-Factor-R{nfB = nfB} neq) = contradiction x₁ (↠-TyNf-noreduce (TyNf-lim⊂TyNf nfB) B')

⇨-determinism {n} {.(Cast _ _ Dyn)} {.(Cast (Cast _ _ (proj₁ (_ match))) (proj₁ (_ match)) Dyn)} {.(Cast _ _ Dyn)} (Cast-Factor-L{v = v} neq) (ξ-Cast{e₂ = e₂} r') = contradiction r' (⇨-Val-noreduce v e₂)
⇨-determinism {n} {.(Cast e'' Dyn Dyn)} {.(Cast (Cast e'' Dyn (proj₁ (_ match))) (proj₁ (_ match)) Dyn)} {e''} (Cast-Factor-L{nfA = ()} neq) Cast-Dyn
⇨-determinism {n} {.(Cast _ _ Dyn)} {.(Cast (Cast _ _ (proj₁ (_ match))) (proj₁ (_ match)) Dyn)} {.Blame} (Cast-Factor-L neq) (Cast-Fail{tynfB = ()} x₁)
⇨-determinism {n} {.(Cast _ _ Dyn)} {.(Cast (Cast _ _ (proj₁ (_ match))) (proj₁ (_ match)) Dyn)} {.(Cast _ _ Dyn)} (Cast-Factor-L{nfA = nfA} neq) (Cast-Reduce-L{A' = A'} x₁) = contradiction x₁ (↠-TyNf-noreduce (TyNf-lim⊂TyNf nfA) A')
⇨-determinism {n} {.(Cast _ _ Dyn)} {.(Cast (Cast _ _ (proj₁ (_ match))) (proj₁ (_ match)) Dyn)} {.(Cast (Cast _ _ (proj₁ (_ match))) (proj₁ (_ match)) Dyn)} (Cast-Factor-L{nfA = nfA} neq) (Cast-Factor-L{nfA = nfA'} neq₁) rewrite (TyNf-lim-uniqueness nfA nfA') = refl
⇨-determinism {n} {.(Cast _ Dyn Dyn)} {.(Cast (Cast _ Dyn (proj₁ (_ match))) (proj₁ (_ match)) Dyn)} {.(Cast (Cast _ Dyn (proj₁ (_ match))) (proj₁ (_ match)) Dyn)} (Cast-Factor-L neq) (Cast-Factor-R{nfB = ()} neq')

⇨-determinism {n} {.(Cast _ Dyn _)} {.(Cast (Cast _ Dyn (proj₁ (_ match))) (proj₁ (_ match)) _)} {.(Cast _ Dyn _)} (Cast-Factor-R{v = v} neq) (ξ-Cast{e₂ = e₂} r') = contradiction r' (⇨-Val-noreduce v e₂)
⇨-determinism {n} {.(Cast e'' Dyn Dyn)} {.(Cast (Cast e'' Dyn (proj₁ (_ match))) (proj₁ (_ match)) Dyn)} {e''} (Cast-Factor-R{nfB = ()} neq) Cast-Dyn
⇨-determinism {n} {.(Cast _ Dyn _)} {.(Cast (Cast _ Dyn (proj₁ (_ match))) (proj₁ (_ match)) _)} {.Blame} (Cast-Factor-R neq) (Cast-Fail{tynfA = ()} x₁)
⇨-determinism {n} {.(Cast (Cast e'' _ Dyn) Dyn _)} {.(Cast (Cast (Cast e'' _ Dyn) Dyn (proj₁ (_ match))) (proj₁ (_ match)) _)} {e''} (Cast-Factor-R{nfB = nfB} neq) (Cast-Collapse{tygH = tygH} x₁) = contradiction (sym (TyG×TyNf-lim⇒match-equiv tygH nfB)) neq
⇨-determinism {n} {.(Cast (Cast _ _ Dyn) Dyn _)} {.(Cast (Cast (Cast _ _ Dyn) Dyn (proj₁ (_ match))) (proj₁ (_ match)) _)} {.Blame} (Cast-Factor-R{nfB = nfB} neq) (Cast-Collide{tygH = tygH} x₁) = contradiction (sym (TyG×TyNf-lim⇒match-equiv tygH nfB)) neq
⇨-determinism {n} {.(Cast _ Dyn _)} {.(Cast (Cast _ Dyn (proj₁ (_ match))) (proj₁ (_ match)) _)} {.(Cast _ Dyn _)} (Cast-Factor-R{nfB = nfB} neq) (Cast-Reduce-R{B' = B'} x₁ x₂) = contradiction x₂ (↠-TyNf-noreduce (TyNf-lim⊂TyNf nfB) B')
⇨-determinism {n} {.(Cast _ Dyn Dyn)} {.(Cast (Cast _ Dyn (proj₁ (_ match))) (proj₁ (_ match)) Dyn)} {.(Cast (Cast _ Dyn (proj₁ (_ match))) (proj₁ (_ match)) Dyn)} (Cast-Factor-R{nfB = ()} neq) (Cast-Factor-L neq')
⇨-determinism {n} {.(Cast _ Dyn _)} {.(Cast (Cast _ Dyn (proj₁ (_ match))) (proj₁ (_ match)) _)} {.(Cast (Cast _ Dyn (proj₁ (_ match))) (proj₁ (_ match)) _)} (Cast-Factor-R{nfB = nfB} neq) (Cast-Factor-R{nfB = nfB'} neq₁) rewrite (TyNf-lim-uniqueness nfB nfB') = refl
⇨-determinism {n} {.(Cast _ Dyn Bot)} {.(Cast (Cast _ Dyn (proj₁ (_ match))) (proj₁ (_ match)) Bot)} {.Blame} (Cast-Factor-R{nfB = ()} neq) (Cast-Bot-R x₁)

⇨-determinism {n} {.(App Blame _)} {.Blame} {.Blame} App₁-Blame App₁-Blame = refl

⇨-determinism {n} {.(App _ Blame)} {.Blame} {.(App _ Blame)} (App₂-Blame{v = v}) (ξ-App₁{e₁' = e₁'} r') = contradiction r' (⇨-Val-noreduce v e₁')
⇨-determinism {n} {.(App _ Blame)} {.Blame} {.Blame} App₂-Blame App₂-Blame = refl

⇨-determinism {n} {.(LetE Blame _)} {.Blame} {.Blame} LetE-Blame LetE-Blame = refl

⇨-determinism {n} {.(Prod Blame _)} {.Blame} {.Blame} Prod-Blame Prod-Blame = refl

⇨-determinism {n} {.(ProdV _ Blame)} {.Blame} {.Blame} ProdV-Blame ProdV-Blame = refl

⇨-determinism {n} {.(LetP Blame _)} {.Blame} {.Blame} LetP-Blame LetP-Blame = refl

⇨-determinism {n} {.(Cast Blame _ _)} {.Blame} {.Blame} Cast-Blame Cast-Blame = refl

⇨-determinism {n} {.(Cast _ _ Bot)} {.Blame} {.(Cast _ _ Bot)} (Cast-Bot-R{v = v} x) (ξ-Cast{e₂ = e₂} r') = contradiction r' (⇨-Val-noreduce v e₂)
⇨-determinism {n} {.(Cast _ _ Bot)} {.Blame} {.Blame} (Cast-Bot-R x) (Cast-Fail{tynfB = ()} x₁)
⇨-determinism {n} {.(Cast _ _ Bot)} {.Blame} {.(Cast _ _ Bot)} (Cast-Bot-R x) (Cast-Reduce-L{A' = A'} x₁) = contradiction x₁ (↠-TyNf-noreduce x A')
⇨-determinism {n} {.(Cast _ Dyn Bot)} {.Blame} {.(Cast (Cast _ Dyn (proj₁ (_ match))) (proj₁ (_ match)) Bot)} (Cast-Bot-R x) (Cast-Factor-R{nfB = ()} neq)
⇨-determinism {n} {.(Cast _ _ Bot)} {.Blame} {.Blame} (Cast-Bot-R x) (Cast-Bot-R x₁) = refl

⇨-determinism {n} {.(CaseE Blame _)} {.Blame} {.Blame} Case-Blame Case-Blame = refl

