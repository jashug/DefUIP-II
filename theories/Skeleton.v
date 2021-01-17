From DefUIP_II Require Import Prelude Telescope.

(*
The "skeleton" of the specification of an inductive-inductive type,
obtained by forgetting to specify the indices of inductive arguments.
*)

Module Skel.

Section skeleton.
Universe i.

Inductive Con : Type@{i+1} :=
  | emp
  | ext (Γ : Con) (A : Ty)
with Ty : Type@{i+1} :=
  | nil
  | arg (A : Type@{i}) (B : A → Ty)
  | sarg (A : SProp) (B : A → Ty)
  | ind {s} (A : Tele.t@{i} s) (B : Ty)
.

End skeleton.
End Skel.