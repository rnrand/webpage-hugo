(** * Complex: Complex Numbers in Coq *)

Require Export Reals.
Require Export Psatz.

Open Scope R_scope.
Notation "√ n" := (sqrt n) (at level 20) : R_scope.

(* ################################################################# *)
(** * Basic Definitions *)

(** A complex number is simply a pair of reals *)

Definition C : Type := R * R.

(** We give names to three generally useful constants *)

Definition C0 : C := (0,0).
Definition C1 : C := (1,0).
Definition Ci : C := (0,1).

Definition RtoC (r : R) : C := (r,0).

Coercion RtoC : R >-> C.

(** We can define plus component-wise *)

Definition Cplus (c1 c2 : C) : C := (fst c1 + fst c2, snd c1 + snd c2).

(** And then define minus and opp together: *)

Definition Copp (c : C) : C := (- fst c, - snd c).
Definition Cminus (c1 c2 : C) : C := Cplus c1 (Copp c2).

(** Multiplication and division are a bit harder. Again, we'll define
    division in terms of an inverse: *)

Definition Cmult (c1 c2 : C) : C :=
    (fst c1 * fst c2 - snd c1 * snd c2, fst c1 * snd c2 + snd c1 * fst c2).

Definition Cinv (c : C) : C :=
  (fst c / (fst c ^ 2 + snd c ^ 2), - snd c / (fst c ^ 2 + snd c ^ 2)).

Definition Cdiv (c1 c2 : C) : C := Cmult c1 (Cinv c2).

(** Finally, we'll define the _norm_ (or _modulus_) of a complex
    number. This is simply the Euclidean norm, treating c as
    coordinates in the cartesian plane. We can define the norm in
    terms of the norm squared: *)

Definition Cnorm2 (c : C) : R := fst c ^ 2 + snd c ^ 2. 
Definition Cnorm (c : C) : R := √ (Cnorm2 c).
Arguments Cnorm2 c /.
Arguments Cnorm c /.

Infix "+" := Cplus : C_scope.
Notation "- x" := (Copp x) : C_scope.
Infix "-" := Cminus : C_scope.
Infix "*" := Cmult : C_scope.
Notation "/ x" := (Cinv x) : C_scope.
Infix "/" := Cdiv : C_scope.

(* ################################################################# *)
(** * Interlude: Psatz *)

(** We would like to prove that all of the field equations from the
    previous chapter hold of complex numbers. However, we'd rather not
    _prove_ these manually.  Instead, we will make use of the powerful
    [lra] tactic, which we will extent to reason about complex numbers
    in the most straightforward way possible. *)

Lemma c_proj_eq : forall (c1 c2 : C), 
  fst c1 = fst c2 -> snd c1 = snd c2 -> c1 = c2.
Proof. intros. destruct c1, c2. simpl in *. subst. reflexivity. Qed.

Ltac lca := eapply c_proj_eq; simpl; lra.

(** [lra] (for Linear Real Arithmetic) is a member of the Psatz
    family of tactics, which include [nra] (for Nonlinear Real
    Arithmetic), [lia] (for Linear Integer Arithmetic) and
    [nia]. These tactics are generally very powerful but not
    well-understood (unlike Omega): It's hard to characterize the
    exact set of equations these tactics can solve.

    The same holds of [lca] and subsequent tactics that we will build
    on top of [lra]. *)

(* ################################################################# *)
(** * C is a field *)

Open Scope C_scope.

Lemma C1_neq_C0 : C1 <> C0. Proof. intros F. inversion F. lra. Qed.

Lemma Cplus_comm : forall c1 c2 : C, c1 + c2 = c2 + c1. Proof. intros. lca. Qed.
Lemma Cplus_assoc : forall c1 c2 c3 : C, c1 + c2 + c3 = c1 + (c2 + c3).
Proof. intros. lca. Qed.

Lemma Cplus_opp_r : forall c : C, c + - c = 0. Proof. intros. lca. Qed.

Lemma Cplus_0_l : forall c : C, 0 + c = c. Proof. intros. lca. Qed.

Lemma Cmult_comm : forall c1 c2:C, c1 * c2 = c2 * c1. Proof. intros. lca. Qed.

Lemma Cmult_assoc : forall c1 c2 c3:C, c1 * c2 * c3 = c1 * (c2 * c3).
Proof. intros. lca. Qed.

Lemma Cmult_1_l : forall c:C, 1 * c = c. Proof. intros. lca. Qed.

Lemma Cmult_plus_distr_r : forall c1 c2 c3:C, (c1 + c2) * c3 = c1 * c3 + c2 * c3.
Proof. intros. lca. Qed.

Lemma Cinv_l : forall c:C, c <> 0 -> / c * c = 1.
Proof.
  intros.
  eapply c_proj_eq; simpl; unfold Rminus, Rdiv.
  - repeat rewrite <- Ropp_mult_distr_l.
    rewrite Ropp_involutive.
    repeat rewrite Rmult_1_r.
    rewrite (Rmult_comm (fst c)). rewrite Rmult_assoc.
    rewrite (Rmult_comm (snd c) (/ _)). rewrite Rmult_assoc.
    rewrite <- Rmult_plus_distr_l.
    rewrite Rinv_l; try lra.
    contradict H. apply Rplus_sqr_eq_0 in H. lca.
  - repeat rewrite Rmult_1_r.
    rewrite (Rmult_comm (fst c)). rewrite Rmult_assoc.
    rewrite (Rmult_comm (- snd c)). rewrite Rmult_assoc.
    rewrite <- Rmult_plus_distr_l.
    lra.
Qed.       

Lemma C_Field_Theory : @field_theory C 0 1 Cplus Cmult Cminus Copp Cdiv Cinv eq.
Proof.
  constructor. constructor.
  (* addition *)
  (* left identity *) apply Cplus_0_l.
  (* commutativity *) apply Cplus_comm.
  (* associativity *) intros; rewrite Cplus_assoc; easy.
  (* multiplication *)
  (* left identity *) apply Cmult_1_l.
  (* commutativity *) apply Cmult_comm.
  (* associativity *) intros; rewrite Cmult_assoc; easy.
  (* distributivity *) apply Cmult_plus_distr_r.
  (* sub = opp *) reflexivity.
  (* additive inverse *) apply Cplus_opp_r.  
  (* 0 <> 1 *) apply C1_neq_C0.
  (* div = inv *) reflexivity.
  (* multiplicative inverse *) apply Cinv_l.
Defined.

Add Field CField : C_Field_Theory.  

(** Some additional useful lemmas *)

Lemma Cplus_opp_l : forall c : C, - c + c = 0. Proof. intros. lca. Qed.
Lemma Cplus_0_r : forall c : C, c + 0 = c. Proof. intros. lca. Qed.
Lemma Cmult_0_l : forall c:C, 0 * c = 0. Proof. intros. lca. Qed.
Lemma Cmult_0_r : forall c:C, c * 0 = 0. Proof. intros. lca. Qed.
Lemma Cmult_1_r : forall c:C, c * 1 = c. Proof. intros. lca. Qed.
Lemma Cmult_plus_distr_l : forall c1 c2 c3:C, c1 * (c2 + c3) = c1 * c2 + c1 * c3.
Proof. intros. lca. Qed.
Lemma Cinv_r : forall c:C, c <> 0 -> c * /c = 1.
Proof. intros. rewrite Cmult_comm. apply Cinv_l. easy. Qed.

Lemma Copp_mult_distr_r : forall c1 c2 : C, - (c1 * c2) = c1 * - c2.
Proof. intros; lca. Qed.
Lemma Copp_mult_distr_l : forall c1 c2 : C, - (c1 * c2) = - c1 * c2.
Proof. intros; lca. Qed.
Lemma Copp_involutive: forall c : C, - - c = c. Proof. intros; lca. Qed.
  
Lemma Csqrt2_square : √2 * √2 = 2. 
Proof.
  eapply c_proj_eq; simpl; try lra.
  rewrite Rmult_0_r, Rminus_0_r.
  apply sqrt_def.
  lra.
Qed.

Lemma RtoC_neq : forall (r1 r2 : R), r1 <> r2 -> RtoC r1 <> RtoC r2.
Proof. intros r1 r2 H F. inversion F. easy. Qed.

(* ################################################################# *)
(** * The complex conjugate *)

(** One unique operation on complex numbers is the complex conjugate.
    The complex conjugate [c^*] of [c = a + bi] is [a - bi].  This
    operation will frequently appear in a quantum setting in the
    context of the adjoint operation on complex matrices. *)

Definition Cconj (x : C) : C := (fst x, (- snd x)%R).

Notation "a ^*" := (Cconj a) (at level 10) : C_scope.

Lemma Cconj_R : forall r : R, r^* = r.         Proof. intros; lca. Qed.
Lemma Cconj_0 : 0^* = 0.                  Proof. lca. Qed.
Lemma Cconj_opp : forall C, (- C)^* = - (C^*). Proof. reflexivity. Qed.
Lemma Cconj_rad2 : (/ √2)^* = / √2.       Proof. lca. Qed.
Lemma Cconj_involutive : forall c, (c^*)^* = c. Proof. intros; lca. Qed.
Lemma Cconj_plus_distr : forall (x y : C), (x + y)^* = x^* + y^*. Proof. intros; lca. Qed.
Lemma Cconj_mult_distr : forall (x y : C), (x * y)^* = x^* * y^*. Proof. intros; lca. Qed.

(** **** Exercise: 1 star, standard, recommended (Conj_mult_norm2)  

    Show that when you multiply a complex number by its conjugate,
    you obtain the norm-squared. *)

Lemma Conj_mult_norm2 : forall c, c * c^* = Cnorm2 c.
Proof.
  (* FILL IN HERE *) Admitted.
(** [] *)

(* ################################################################# *)
(** * Sums over Complex Numbers *)

(** One important function we will care about when reasoning about
    matrices in upcoming chapter is the sum of complex numbers. Let's
    try proving a few things about these sums. *)

Fixpoint Csum (f : nat -> C) (n : nat) : C := 
  match n with
  | O => 0
  | S n' => Csum f n' +  f n'
  end.

Lemma Csum_0 : forall (f : nat -> C) (n : nat),
    (forall x, (x < n)%nat -> f x = 0) ->
    Csum f n = 0.  
Proof.  
  (* WORKED IN CLASS *)
  intros. 
  induction n.  
  - reflexivity.  
  - simpl.  
    rewrite H by lia. 
    rewrite IHn. lca.  
    intros. apply H; lia.  
Qed.
  
Lemma Csum_eq : forall (f g : nat -> C) (n : nat),
  (forall x, (x < n)%nat -> f x = g x) ->
  Csum f n = Csum g n.
Proof. 
  (* WORKED IN CLASS *)
  intros f g n H. 
  induction n.
  + simpl. reflexivity.
  + simpl. 
    rewrite H by lia.
    rewrite IHn by (intros; apply H; lia).
    reflexivity.
Qed.
  

Lemma Csum_plus : forall (f g : nat -> C) (n : nat),
    Csum (fun x => f x + g x) n = Csum f n + Csum g n.  
Proof. 
  intros f g n.  
  induction n.  
  - simpl. lca.  
  - simpl. rewrite IHn. lca.  
Qed.

Lemma Csum_mult_l : forall (c : C) (f : nat -> C) (n : nat),
    c * Csum f n = Csum (fun x => c * f x) n.  
Proof.  
  intros c f n.  
  induction n.  
  - simpl; lca.  
  - simpl.  
    rewrite Cmult_plus_distr_l.  
    rewrite IHn.  
    reflexivity.  
Qed.

Lemma Csum_mult_r : forall (c : C) (f : nat -> C) (n : nat),
    Csum f n * c = Csum (fun x => f x * c) n.  
Proof.  
  intros c f n.  
  induction n.  
  - simpl; lca.  
  - simpl.  
    rewrite Cmult_plus_distr_r.  
    rewrite IHn.  
    reflexivity.  
Qed.

(** **** Exercise: 2 stars, standard, recommended (Csum_conj_distr)  *)
Lemma Csum_conj_distr : forall (f : nat -> C) (n : nat),
    (Csum f n) ^* = Csum (fun x => (f x)^*) n.
Proof. 
  (* FILL IN HERE *) Admitted.
(** [] *)

(** **** Exercise: 3 stars, standard, recommended (Csum_unique)  *)
Lemma Csum_unique : forall (f : nat -> C) (k : C) (n x : nat), 
  (x < n)%nat ->
  f x = k ->
  (forall x', x <> x' -> f x' = 0) ->
  Csum f n = k.
Proof.
  (* FILL IN HERE *) Admitted.
(** [] *)

(** We'll make C opaque so Coq doesn't treat it as a pair. *)
Opaque C.

(* Thu Aug 1 13:45:52 EDT 2019 *)
