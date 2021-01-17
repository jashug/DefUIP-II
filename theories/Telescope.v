From DefUIP_II Require Import Prelude.

Module Tele.

Inductive structure := nil_ | arg_ (s : structure) | sarg_ (s : structure).

Section telescope.
Universe i.

Inductive t : structure → Type@{i+1} :=
  | nil : t nil_
  | arg {s} (A : Type@{i}) (B : A → t s) : t (arg_ s)
  | sarg {s} (A : SProp) (B : A → t s) : t (sarg_ s)
.

(* ought to use a specialized sigma with SProp on the left *)
Fixpoint as_sigma {s} (tele : t s) : Type@{i} :=
  match tele with
  | nil => 1
  | arg A B => Σ (a : A), as_sigma (B a)
  | sarg A B => Σ (a : Box A), as_sigma (B (unbox a))
  end.

End telescope.
End Tele.
