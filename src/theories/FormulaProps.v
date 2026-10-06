From stdpp Require Export countable strings. (* Countability from stdpp *)
Require Import HA.Autosubst.Formulas.

Notation "¬ φ" := (Implies φ Bot) (at level 75, φ at level 75).
Notation " ⊥ " := Bot.
Notation " ⊤ " := (Implies Bot Bot).
Notation " A ∧ B" := (And A B) (at level 80, B at level 80).
Notation " A ∨ B" := (Or A B) (at level 85, B at level 85).
Notation " A → B" := (Implies A B) (at level 99, B at level 200).
Notation " ∀ A" := (Core.ForAll A) (at level 200, right associativity).
Notation " ∃ A" := (Core.Exists A) (at level 200, right associativity).
Infix " φ ⇔ ψ " := (And (Implies φ ψ) (Implies ψ φ)) (at level 100).

Ltac solve_trivial_decision :=
  match goal with
  | |- Decision (?P) => apply _
  | |- sumbool ?P (¬?P) => change (Decision P); apply _
  end.

Ltac solve_decision :=
  unfold EqDecision; intros;
  first [ solve_trivial_decision | unfold Decision; decide equality; solve_trivial_decision ].

Global Instance term_eq_dec : EqDecision term.
Proof. unfold EqDecision. unfold Decision. solve_decision. Defined.

Global Instance form_eq_dec : EqDecision form.
Proof. solve_decision. Defined.

Section CountablyManyFormulas.
  Local Fixpoint term_to_gen_tree (t : term) : gen_tree nat :=
    match t with
    | var_term i => GenNode 0 [GenLeaf i]
    | zero => GenNode 1 []
    | succ t1 => GenNode 2 [ term_to_gen_tree t1 ]
    | add t1 t2 => GenNode 3 [term_to_gen_tree t1; term_to_gen_tree t2] 
    | mul t1 t2 => GenNode 4 [term_to_gen_tree t1; term_to_gen_tree t2] 
    end.

  (*; We can similarly specify a decoding procedure which does the reverse ;*)
  Local Fixpoint gen_tree_to_term (t : gen_tree nat) : option term :=
    match t with
    | GenNode 0 [ GenLeaf k ] => Some (var_term k)
    | GenNode 1 [ ] => Some (zero)
    | GenNode 2 [ t1 ] =>
        gen_tree_to_term t1 ≫= fun x => Some (succ x)
    | GenNode 3 [ t1 ; t2 ] =>
        gen_tree_to_term t1 ≫= fun x => gen_tree_to_term t2 ≫= fun y => Some (add x y)
    | GenNode 4 [ t1 ; t2 ] =>
        gen_tree_to_term t1 ≫= fun x => gen_tree_to_term t2 ≫= fun y => Some (mul x y)
    | _ => None
    end.

  (*{ Terms are countable }*)
  (*; $\term \xhookrightarrow{} \nat$ ;*)
  Global Instance term_count : Countable term.
  Proof.
    eapply inj_countable with (f := term_to_gen_tree) (g := gen_tree_to_term); intros.
    induction x; try easy; simpl.
    - rewrite IHx; easy.
    - rewrite IHx1, IHx2; easy.
    - rewrite IHx1, IHx2; easy.
  Defined.

  Local Fixpoint form_to_gen_tree (φ : form) : gen_tree nat :=
    match φ with
    | Eq t s => GenNode 0 [ GenLeaf (encode_nat t ) ; GenLeaf (encode_nat s) ]
    (*: - $\bot$ to nodes labelled 1 without any leaves :*)
    | Bot => GenNode 1 []
    (*: - $A \land B$ to nodes labelled 2 with branches to A and B's tree :*) 
    | And φ ψ => GenNode 2 [form_to_gen_tree φ ; form_to_gen_tree ψ]
    (*: - $A \lor B$ to nodes labelled 3 with branches to A and B's tree :*)
    | Or φ ψ => GenNode 3 [form_to_gen_tree φ ; form_to_gen_tree ψ]
    (*: - $A \to B$ to nodes labelled 4 with branches to A and B's tree :*)
    | Implies φ ψ => GenNode 4 [form_to_gen_tree φ ; form_to_gen_tree ψ]
    (*: - $\forall A$ to nodes labelled 5 with a branch to A's tree :*)
    | ForAll ψ => GenNode 5 [form_to_gen_tree ψ]
    (*: - $\forall A$ to nodes labelled 6 with a branch to A's tree ;*)
    | Exists ψ => GenNode 6 [form_to_gen_tree ψ]
    end.

  (*; Again we can similarly obtain a decoding procedure. ;*)
  Local Fixpoint gen_tree_to_form (t : gen_tree nat) : option form :=
    match t with
    | GenNode 0 [ GenLeaf n; GenLeaf m ] =>
        decode_nat n ≫= fun t => decode_nat m ≫= fun s => Some (Eq t s)
    | GenNode 1 [] => Some Bot
    | GenNode 2 [t1 ; t2] =>
        gen_tree_to_form t1 ≫= fun φ => gen_tree_to_form t2≫= fun ψ => Some (φ ∧ ψ)
    | GenNode 3 [t1 ; t2] =>
        gen_tree_to_form t1 ≫= fun φ => gen_tree_to_form t2 ≫= fun ψ => Some (φ ∨ ψ)
    | GenNode 4 [t1 ; t2] =>
        gen_tree_to_form t1 ≫= fun φ => gen_tree_to_form t2 ≫= fun ψ => Some (φ →  ψ)
    | GenNode 5 [t1] => 
        gen_tree_to_form t1 ≫= fun φ => Some (ForAll φ)
    | GenNode 6 [t1] => 
        gen_tree_to_form t1 ≫= fun φ => Some (Exists φ)
    | _=> None
    end.

  (*{ Formulae are countable }*)
  (*; $\form \xhookrightarrow{} \nat$ ;*)
  Global Instance form_count : Countable form.
  Proof.
    (*; We again exhibit an injection from formulae to the naturals. :*)
    eapply inj_countable with (f := form_to_gen_tree) (g := gen_tree_to_form).
    (*: This follows from the encoding procedure and decoding procedure. ;*)
    intro φ; induction φ; cbn;
      repeat rewrite decode_encode_nat;
      try (rewrite IHφ1, IHφ2);
      try (rewrite IHφ); easy.
  Defined.
End CountablyManyFormulas.


(*## Weight of formulae ##*)

(*; Here we define the weight function on formulas, following (Dyckhoff Negri 2000) ;*)
Fixpoint weight (φ : form) : nat := (*= Weight of a formula =*)
  (*; We define the weight of a formula $w(\varphi)$ as: :*)
  match φ with
  | Eq _ _ => 1                     (*: - $w(P_i(t_1, \dots)) = 1$ :*)
  | ⊥ => 1                           (*: - $w(\bot) = 1$ :*)
  | φ → ψ => 1 + weight φ + weight ψ (*: - $w(\varphi \to \psi) = 1 + w(\varphi) + w(\psi)$ :*)
  | φ ∧ ψ => 2 + weight φ + weight ψ (*: - $w(\varphi \land \psi) = 2 + w(\varphi) + w(\psi)$ :*)
  | φ ∨ ψ => 3 + weight φ + weight ψ (*: - $w(\varphi \lor \psi) = 3 + w(\varphi) + w(\psi)$ :*)
  | ForAll φ => 1 + weight φ          (*: - $w(\forall \varphi) = 1 + w(\varphi)$ :*)
  | Exists φ => 2 + weight φ          (*: - $w(\exists \varphi) = 2 + w(\varphi)$ ;*)
  end.

Lemma weight_pos φ : weight φ > 0. (*{ Positivity of weight }*)(*; $w(\varphi) > 0$ ;*)
Proof. induction φ; simpl; lia. Qed. (*; Trivial by definition ;*)

(*; We can obtain a transitive and irreflexive order over formulae. ;*)
Definition form_order φ ψ := weight φ > weight ψ.

Global Instance transitive_form_order : Transitive form_order.
Proof. unfold form_order. auto with *. Qed.

Global Instance irreflexive_form_order : Irreflexive form_order.
Proof. unfold form_order. intros x y. lia. Qed.

Notation "φ ≺f ψ" := (form_order ψ φ) (at level 149).

Fixpoint occurs_in_term (i : nat) t :=
  match t with
  | var_term i => i = i
  | zero => False
  | succ x => (occurs_in_term i x)
  | add x y => or (occurs_in_term i x) (occurs_in_term i y)
  | mul x y => or (occurs_in_term i x) (occurs_in_term i y)
  end.

Fixpoint occurs_in_form i φ :=
  match φ with
  | Eq t s => or (occurs_in_term i t) (occurs_in_term i s)
  | Bot => False
  | And φ1 φ2 => or (occurs_in_form i φ1) (occurs_in_form i φ2)
  | Or φ1 φ2 => or (occurs_in_form i φ1) (occurs_in_form i φ2)
  | Implies φ1 φ2 => or (occurs_in_form i φ1) (occurs_in_form i φ2)
  | ForAll φ1 => occurs_in_form i φ1
  | Exists φ1 => occurs_in_form i φ1
  end.

(*### Substitution on weight ###*)

(*{ Substitutions don't affect weight }*)
(*; $w(\varphi[\up^n(f)]) = w(\varphi)$ ;*)
Lemma weight_subst_f (f : nat -> term) (A : form):
  weight (subst_form f A) = weight A.
Proof.
  (*; Induction on the formula's structure. :*)
  revert f.
  induction A; intros f; asimpl; cbn;
    try rewrite IHA1, IHA2;
    try rewrite IHA; easy.
Qed.
