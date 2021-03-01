------------------------------------------------------------------------
-- Some examples
------------------------------------------------------------------------

module Examples where

open import Data.Fin hiding (cast)
open import Data.Fin.Properties
open import Data.Fin.Subset renaming (∣_∣ to ∣_∣ˢ ; ⊤ to ⊤ˢ ; ⊥ to ⊥ˢ)
open import Data.Fin.Subset.Properties
open import Data.List hiding (_++_ ; length)
open import Data.List.Relation.Unary.All
open import Data.Vec hiding (_++_ ; length)
open import Relation.Nullary
open import Relation.Nullary.Negation
open import Relation.Binary.PropositionalEquality renaming (trans to ≡-trans)
open import Data.Product
open import Data.Maybe
open import Data.Maybe.Relation.Unary.All renaming (All to Allᵐ)
open import Data.Maybe.Relation.Unary.Any renaming (Any to Anyᵐ)
open import Data.Unit using (⊤)

open import Syntax
open import Substitution
open import Typing-Semantics
open import Aux

------------------------------------------------------------------------
-- Global definitions

[l] : Subset 2
[l] = inside ∷ (outside ∷ [])

[l'] : Subset 2
[l'] = outside ∷ (inside ∷ [])

[l,l'] : Subset 2
[l,l'] = inside ∷ (inside ∷ [])

f : (l : Fin 2) → l ∈ [l,l'] → Exp {2}
f zero i = UnitE
f (Fin.suc zero) i = LabI (Fin.suc zero)

fᵀ : (l : Fin 2) → l ∈ [l,l'] → Ty {2}
fᵀ zero i = UnitT
fᵀ (Fin.suc zero) i = Single (VLab{x = Fin.suc zero}) (Label [l'])


------------------------------------------------------------------------
-- Big step semantics

-- (λx . case (x : * => {l}) {l : ()}) (l : {l} => *) ⇓ ()
example-case : proj₁ ([] ∶ App (Abs (CaseE{s = [l]} (UCast{G = Label [l]} (VVar{i = 0}) GLabel) λ l x → UnitE))
                                 (VCast{e = LabI zero}{G = (Label ⁅ zero ⁆)} VLab GLabel) ⇓) ≡ UnitE
example-case = refl

-- (λx . case (x : * => {l, l'}) {l : (), l' : (LabI l')}) (l' : {l'} => *) ⇓ ()
g : (l : Fin 2) → l ∈ [l,l'] → Exp {2}
g zero i = UnitE
g (Fin.suc zero) i = LabI (Fin.suc zero)

example-case' : proj₁ ([] ∶ App (Abs (CaseE{s = [l,l']} (UCast{G = Label [l,l']} (VVar{i = 0}) GLabel) g))
                               (VCast{e = LabI (Fin.suc zero)}{G = (Label ⁅ Fin.suc zero ⁆)} VLab GLabel) ⇓) ≡ (LabI (Fin.suc zero))
example-case' = refl

--  l : S{l : {l}} => Unit ⇓ Blame
example-bad : proj₁ ([] ∶ Cast (LabI zero) (Single (VLab{x = zero}) (Label [l])) UnitT ⇓) ≡ Blame
example-bad = refl    

-- (λx . (case (x : * => [l,l']) of {l : (), l' : LabI l'}) : Π(x : *)(case ...) => Π(x : {l, l'})(case ...)) l
--                                                                                                              ⇓ ()
example-function-f : Exp {2}
example-function-f = Abs (CaseE (UCast{e = Var 0}{G = Label [l,l']} VVar GLabel) f)

example-function-f-cast : Exp {2}
example-function-f-cast = Cast example-function-f (Pi Dyn ((CaseT (UCast{e = Var 0}{G = Label [l,l']} VVar GLabel) fᵀ))) (Pi (Label [l,l']) (CaseT (UVal (VVar{i = 0})) fᵀ))

example-function : proj₁ ([] ∶ App example-function-f-cast (VLab{x = zero}) ⇓) ≡ UnitE
example-function = refl

-- ⟨ l , (case x of {l : (), l' : LabI l'}) ⟩ ⇓ ⟨⟨ l , () ⟩⟩
example-product : Exp {2}
example-product = Prod (LabI zero) (CaseE (UVal (VVar{i = 0})) f)

example-product-result : proj₁ ([] ∶ Prod (LabI zero) (CaseE (UVal (VVar{i = 0})) f) ⇓) ≡ ProdV (VLab{x = zero}) UnitE
example-product-result = refl

-- let ⟨⟨ x , y ⟩⟩ = ⟨ l' , (case x of {l : (), l' : LabI l'}) ⟩ in (case y of {l : (), l' : (Abs z)}) ⇓ Abs z
f' : (l : Fin 2) → l ∈ [l,l'] → Exp {2}
f' zero i = UnitE
f' (Fin.suc zero) i = Abs (Var 0)

example-product' : Exp {2}
example-product' = Prod (LabI (Fin.suc zero)) (CaseE (UVal (VVar{i = 0})) f)

example-letp : Exp {2}
example-letp = LetP example-product' (CaseE (UVal (VVar{i = 0})) f')

example-letp-result : proj₁ ([] ∶ example-letp ⇓) ≡ Abs (Var 0)
example-letp-result = refl

------------------------------------------------------------------------
-- Cast function

-- cast S{l : {l}} {l} {l, l'}  =  S{l : {l, l'}}
cast-example : Data.Maybe.fromMaybe Bot (cast (Single (VLab{x = zero}) (Label [l])) (Label [l]) (Label [l,l'])) ≡ Single (VLab{x = zero}) (Label [l,l'])
cast-example = refl

-- cast {l} {l} *  =  *
cast-example' : Data.Maybe.fromMaybe Bot (cast (Label [l]) (Label [l]) Dyn) ≡ Dyn
cast-example' = refl

------------------------------------------------------------------------
-- Typing

-- Well-formedness of dependent product which is cast
-- ∅ ⊢ ⟨ l : S{l : {l}} ⇒ * , case (0 : * => {l, l'}) of {l : (), l' : LabI l'} ⟩
--     : Σ(0 : *)(case (0 : * => {l, l'}) of {l : Unit, l' : S{l' : {l'}}}) ⇒ Σ(0 : {l, l'})(case 0 of {l : Unit, l' : S{l' : {l'}}}
--     ▷ Σ(0 : {l, l'})(case 0 of {l : Unit, l' : S{l' : {l'}}}
B : Ty {2}
B = CaseT (UCast{G = Label [l,l']} (VVar{i = 0}) GLabel) fᵀ

B' : Ty {2}
B' = CaseT (UVal (VVar{i = 0})) fᵀ

T : Ty {2}
T = Sigma Dyn B

T' : Ty {2}
T' = Sigma (Label [l,l']) B'

e : Exp {2}
e = Cast (Prod (Cast (LabI zero) (Single (VLab{x = zero}) (Label [l])) Dyn) (CaseE{s = [l,l']} (UCast{G = Label [l,l']} (VVar{i = 0}) GLabel) f))
    T T' 

fᵀ-ok : {A : Ty {2}} {ok : [] ⊢ A} →
        (l : Fin 2) (i : l ∈ [l,l']) → ⟨ A , [] ⟩ ⊢ fᵀ l i

fᵀ-ok {A} {ok} zero i = UnitF (entry empty ok)
fᵀ-ok {A} {ok} (Fin.suc zero) i = SingleF{ok = LabF (entry empty ok)} (entry empty ok) (SubTypeA (LabAI (entry empty ok)) (ASubSingle (ASubLabel (λ x → x)) notsingle-label notcase-label)) notsingle-label

T-ok : [] ⊢ T
T-ok = SigmaF (DynF empty) (CaseF{f-ok = fᵀ-ok {A = Dyn}{ok = DynF empty}} (SubTypeA (CastA{ok = DynF (entry empty (DynF empty))}{ok' = LabF (entry empty (DynF empty))} (VarA (entry empty (DynF empty)) here) (AConsDynL (entry empty (AConsRefl empty) (DynF empty) (DynF empty))) (just Data.Unit.tt) refl) (ASubLabel (λ x → x))))

T'-ok : [] ⊢ T'
T'-ok = SigmaF (LabF empty) (CaseF{f-ok = fᵀ-ok {A = Label [l,l']}{ok = LabF empty}} (SubTypeA (VarA (entry empty (LabF empty)) here) (ASubLabel (λ x → x))))

cast-rw : ∀ l → l ∈ [l,l'] → (Data.Maybe.fromMaybe UnitT (cast (Single (VLab{x = l}) (Label ⁅ l ⁆)) (Label ⁅ l ⁆) (Label [l,l']))) ≡ Single (VLab{x = l}) (Label [l,l'])
cast-rw zero i = refl
cast-rw (Fin.suc zero) i = refl

single-ok : ∀ l → l ∈ [l,l'] → [] ⊢ Single (VLab{x = l}) (Label [l,l'])
single-ok l i = SingleF {ok = LabF empty} empty (SubTypeA (LabAI empty) (ASubSingle (ASubLabel (l∈L⇒[l]⊆L i)) notsingle-label notcase-label)) notsingle-label

single-ok' : ∀ l → l ∈ [l,l'] → [] ⊢ Single (VCast (VLab{x = l}) (GLabel{s = ⁅ l ⁆})) Dyn
single-ok' zero i = SingleF {ok = DynF empty} empty (SubTypeA (CastA{ok = LabF empty}{ok' = DynF empty} (LabAI empty) (AConsDynR empty) (just Data.Unit.tt) refl) (ASubSingle ASubDyn notsingle-dyn notcase-dyn)) notsingle-dyn
single-ok' (Fin.suc zero) i = SingleF {ok = DynF empty} empty (SubTypeA (CastA{ok = LabF empty}{ok' = DynF empty} (LabAI empty) (AConsDynR empty) (just Data.Unit.tt) refl) (ASubSingle ASubDyn notsingle-dyn notcase-dyn)) notsingle-dyn

function-j : (l : Fin 2) (i : l ∈ [l,l']) → ⟨  Single (VCast{G = (Label ⁅ l ⁆)} (VLab{x = l}) (GLabel)) (Dyn) , [] ⟩ ⊢ f l i ▷ fᵀ l i
function-j zero i = UnitAI (entry empty (single-ok' zero i))
function-j (Fin.suc zero) i = LabAI (entry empty (single-ok' (Fin.suc zero) i))

cons-premise-env-ok' : ∀ l → l ∈ [l,l'] → ⊢ ⟨ Single (VCast{G = (Label ⁅ l ⁆)} (VLab{x = l}) GLabel) Dyn , [] ⟩ ∣ ⟨ Single (VLab{x = l}) (Label [l,l']) , [] ⟩ ok
cons-premise-env-ok' zero i = entry empty (AConsSingleL (AConsDynL empty) (SubTypeA (CastA{ok = LabF empty}{ok' = DynF empty} (LabAI empty) (AConsDynR empty) (just Data.Unit.tt) refl)
                              (ASubSingle ASubDyn notsingle-dyn notcase-dyn))) (single-ok' zero i) (single-ok zero i)
cons-premise-env-ok' (Fin.suc zero) i = entry empty (AConsSingleL (AConsDynL empty) (SubTypeA (CastA{ok = LabF empty}{ok' = DynF empty} (LabAI empty) (AConsDynR empty) (just Data.Unit.tt) refl)
                                        (ASubSingle ASubDyn notsingle-dyn notcase-dyn))) (single-ok' (Fin.suc zero) i) (single-ok (Fin.suc zero) i)

function-cons : ∀ l → (i : l ∈ [l,l']) → ⟨ Single (VCast (VLab{x = l}) (GLabel{s = ⁅ l ⁆})) Dyn , [] ⟩ ∣
                                         ⟨ Single (VLab{x = l}) (Label (inside ∷ inside ∷ [])) , [] ⟩ ⊢ fᵀ l i ~ fᵀ l i
function-cons zero i = AConsRefl (cons-premise-env-ok' zero i)
function-cons (Fin.suc zero) i = AConsRefl (cons-premise-env-ok' (Fin.suc zero) i)

B-B'-cons-LR : (l : Fin 2) (i : l ∈ [l,l']) →
    {D° : Ty {2}} {p : Is-just (cast (Single (VLab{x = l}) (Label ⁅ l ⁆)) (Label ⁅ l ⁆) (Label [l,l']))} {env-ty : (Data.Maybe.fromMaybe UnitT (cast (Single (VLab{x = l}) (Label ⁅ l ⁆)) (Label ⁅ l ⁆) (Label [l,l']))) ≡ D°}
    → 
    ⟨  Single (VCast{G = (Label ⁅ l ⁆)} (VLab{x = l}) (GLabel)) (Dyn) , [] ⟩ ∣
    ⟨ D° , [] ⟩
    ⊢ fᵀ l i ~ B'
B-B'-cons-LR l i {D°} {p} {env-ty} rewrite (cast-rw l i) | sym (env-ty)
  = AConsCaseLR {ins = i} (VarA (entry empty (SingleF {ok = LabF empty} empty (SubTypeA (LabAI empty) (ASubSingle (ASubLabel (l∈L⇒[l]⊆L i)) notsingle-label notcase-label)) notsingle-label)) here) (λ x → x) (function-cons l i)

B-B'-cons :  ⟨ Dyn , [] ⟩ ∣ ⟨ Label [l,l'] , [] ⟩ ⊢ B ~ B'
B-B'-cons = AConsCaseXLDyn{Δ = []}{Δ' = []}{eq = refl}{eq' = refl}  B-B'-cons-LR

j : [] ⊢ e ▷ T'
j = CastA{ok = T-ok}{ok' = T'-ok}
    (SigmaAI (SubTypeA (CastA
      {ok = SingleF{ok = LabF empty} empty (SubTypeA (LabAI empty) (ASubSingle (ASubLabel (λ x → x)) notsingle-label notcase-label)) notsingle-label}
      {ok' = DynF empty}
      (LabAI empty) (AConsDynR empty) (just Data.Unit.tt) refl) ASubDyn) (LabAExDyn{eq = refl} function-j)) (AConsSigma (AConsDynL empty) B-B'-cons)
    (cast-trivial-just{A = T}{C = T'} refl) (cast-trivial{A = T}{B = T}{C = T'} refl)

