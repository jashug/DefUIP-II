From DefUIP_II Require Import Prelude.

Section example.
Context
  (X : Set)
.

(*
Constructing the inductive-inductive type
A : U
B : A → U
eta : X → A
ext : (a : A) → B a → A
inj : (a : A) → B a
*)

Inductive preA : Set :=
  | pre_eta : X → preA
  | pre_ext : preA → preB → preA
with preB : Set :=
  | pre_inj : preA → preB
.

Fixpoint goodA (pa : preA) : SProp :=
  match pa with
  | pre_eta x => ⊤
  | pre_ext pa pb => goodA pa ∧ goodB pb pa
  end
with goodB (pb : preB) : preA → SProp :=
  match pb with
  | pre_inj pa => λ phi ↦ goodA pa ∧ Id pa phi
  end
.

Definition A := sub preA goodA.
Definition B (a : A) := sub preB λ pb ↦ goodB pb a.(wit).
Definition eta (x : X) : A := sub_in (pre_eta x) I.
Definition ext (a : A) (b : B a) : A :=
  sub_in (pre_ext a.(wit) b.(wit)) (conj a.(prf) b.(prf)).
Definition inj (a : A) : B a :=
  sub_in (pre_inj a.(wit)) (conj a.(prf) refl).

Section induction.
Universe i.
Context
  (PA : A → Type@{i})
  (PB : ∀ a, B a → PA a → Type@{i})
  (Peta : ∀ x, PA (eta x))
  (Pext : ∀ a b, ∀ (Pa : PA a), PB a b Pa → PA (ext a b))
  (Pinj : ∀ a, ∀ (Pa : PA a), PB a (inj a) Pa)
.

Definition stage1_inj_step
  (pa : preA) (pb := pre_inj pa)
  (IHa : ∀ (ga : goodA pa), Σ (Q : SProp), Q → PA (sub_in pa ga)) :
  ∀ (phi : A) (gb : goodB pb phi.(wit)) (Pa : PA phi),
  Σ (Q : SProp), Q → PB phi (sub_in pb gb) Pa :=
  λ '(sub_in pphi gphi) '(conj ga pe : goodB (pre_inj pa) (sub_in pphi _).(wit))
      (Pphi : PA (sub_in pphi gphi)) ↦
    match pe in Id _ pphi
    return
      ∀ (gphi : goodA pphi) (Pphi : PA (sub_in pphi gphi)),
      Σ (Q : SProp), Q → PB (sub_in pphi gphi) (sub_in (pre_inj pa) (conj ga pe)) Pphi
    with refl => λ (gphi : goodA pa) Pphi ↦
      let a : A := sub_in pa ga in
      let (Qa, Pa) := IHa ga in
      (dep_and Qa (λ q ↦ Id (Pa q) Pphi), λ '(conj qa Pe) ↦
       match Pe in Id _ Pphi return PB _ _ Pphi with refl =>
         Pinj a (Pa qa)
       end)
    end gphi Pphi.

Fixpoint stage1A (pa : preA) :
  ∀ (ga : goodA pa), Σ (Q : SProp), Q → PA (sub_in pa ga) :=
  match pa with
  | pre_eta x => λ ga ↦ (⊤, λ _ ↦ Peta x)
  | pre_ext pa pb => λ '(conj ga gb) ↦
    let a : A := sub_in pa ga in let b : B a := sub_in pb gb in
    let (Qa, Pa) := stage1A pa ga in
    let QPb (q : Qa) := stage1B pb a gb (Pa q) in
    (dep_and Qa (λ q ↦ (QPb q).1), λ '(conj qa qb) ↦
     Pext a b (Pa qa) ((QPb qa).2 qb))
  end
with stage1B (pb : preB) :
  ∀ (phi : A) (gb : goodB pb phi.(wit)) (Pa : PA phi),
  Σ (Q : SProp), Q → PB phi (sub_in pb gb) Pa :=
  match pb with
  | pre_inj pa =>
    stage1_inj_step pa (stage1A pa)
  end
.

Definition QA (a : A) : SProp := (stage1A a.(wit) a.(prf)).1.
Definition QA_to_PA {a : A} : QA a → PA a := (stage1A a.(wit) a.(prf)).2.
Definition QB (a : A) (b : B a) (Qa : QA a) : SProp :=
  (stage1B b.(wit) a b.(prf) (QA_to_PA Qa)).1.
Definition QB_to_PB {a b} {Qa : QA a} : QB a b Qa → PB a b (QA_to_PA Qa) :=
  (stage1B b.(wit) a b.(prf) (QA_to_PA Qa)).2.
Definition Qeta (x : X) : QA (eta x) := I.
Definition Qeta_eq {x} := convertible (QA_to_PA (Qeta x)) (Peta x).
Definition Qext a b (Qa : QA a) (Qb : QB a b Qa) : QA (ext a b) :=
  conj Qa Qb.
Definition Qext_eq {a b} {Qa : QA a} {Qb : QB a b Qa} := convertible
  (QA_to_PA (Qext a b Qa Qb)) (Pext a b (QA_to_PA Qa) (QB_to_PB Qb)).
Definition Qinj a (Qa : QA a) : QB a (inj a) Qa :=
  conj Qa refl.
Definition Qinj_eq {a} {Qa : QA a} :=
  convertible (QB_to_PB (Qinj a Qa)) (Pinj a (QA_to_PA Qa)).

Definition QA_to_PA_constant {a : A} (x y : QA a) :=
  convertible (QA_to_PA x) (QA_to_PA y).
(* The relevances for Qa and Qb are apparently wrongly inferred *)
Fixpoint stage2A (pa : preA) : ∀ (ga : goodA pa), QA (sub_in pa ga) :=
  match pa with
  | pre_eta x => λ ga ↦ I
  | pre_ext pa pb => λ '(conj ga gb) ↦
    let Qa := stage2A pa ga in
    let Qb := stage2B pb (sub_in pa ga) gb Qa in
    conj Qa Qb
  end
with stage2B (pb : preB) :
  ∀ (phi : A) (gb : goodB pb phi.(wit)) (Qa : QA phi), QB phi (sub_in pb gb) Qa :=
  match pb with
  | pre_inj pa => λ phi (gb : goodB (pre_inj pa) phi.(wit)) Qphi ↦
    let ga := gb.(proj1) in
    let Qa : QA (sub_in pa ga) := stage2A pa ga in
    match gb.(proj2) as e in Id _ phi_wit
    return
      ∀ (phi_prf : goodA phi_wit) (Qphi : QA (sub_in phi_wit phi_prf)),
      QB (sub_in phi_wit phi_prf) (sub_in (pre_inj pa) (conj ga e)) Qphi
    with refl => λ phi_prf (Qphi : QA _) ↦
      conj Qa (QA_to_PA_constant Qa Qphi : QA_to_PA Qa = QA_to_PA Qphi)
    end phi.(prf) Qphi
  end
.

Definition rectA_Q (a : A) : QA a := stage2A a.(wit) a.(prf).
Definition rectA (a : A) : PA a := QA_to_PA (rectA_Q a).
Definition rectB_Q {a : A} (b : B a) : QB a b (rectA_Q a) :=
  stage2B b.(wit) a b.(prf) (rectA_Q a).
Definition rectB {a : A} (b : B a) : PB a b (rectA a) :=
  QB_to_PB (rectB_Q b).
Definition rect_eta_eq (x : X) := convertible (rectA (eta x)) (Peta x).
Definition rect_ext_eq a b := convertible (rectA (ext a b)) (Pext a b (rectA a) (rectB b)).
Definition rect_inj_eq a := convertible (rectB (inj a)) (Pinj a (rectA a)).
End induction.
End example.