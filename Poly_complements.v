From mathcomp Require Import all_ssreflect all_algebra.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

Import GRing.Theory.
Local Open Scope ring_scope.

Definition rm0 :=
 (mulr0, mul0r, subr0, sub0r, add0r, addr0, mul0rn, mulr0n, oppr0,
  scale0r, scaler0).

Definition rm1 := (mulr1, mul1r, mulr1n).

Section Poly_complements.
Variable R : ringType.

Lemma gtn_size (p : {poly R}) i : p`_i != 0 -> (i < size p)%N.
Proof.
rewrite leqNgt; apply: contra.
by rewrite ltnS => /leq_sizeP/(_ i)->.
Qed.
Lemma coef_Xn_eq (p: {poly R}):
	p = \sum_(i < size p) p`_i *: 'X^i.
Proof.
by rewrite -[LHS]coefK poly_def.
Qed.

Lemma polyseq_eq (p q: {poly R}):
	polyseq p = polyseq q <-> p = q.
Proof.
by split => [eqn | ->]; first rewrite -[LHS]polyseqK eqn polyseqK.
Qed.

Lemma coef_eq (p q: {poly R}):
	p = q <-> forall i, p`_i = q`_i.
Proof.
split => [-> | prp] //.
apply /subr0_eq /eqP.
by rewrite -lead_coef_eq0 lead_coefE coefB prp addrC -[_ + _]add0r addrA subrK.
Qed.

Lemma XnX i:
	('X^i * 'X =('X^i.+1: {poly R}))%R.
Proof.
apply coef_eq => n.
rewrite coefMX !coefXn.
by case: ifP => /=[/eqP -> | ] //; case: n.
Qed.

Lemma cons_poly_inj:
	forall a p b q, cons_poly (a: R) p = cons_poly b q -> a = b /\ p = q.
Proof.
move => a p b q /= eq.
suffices: size (cons_poly (a - b) (p - q)) = 0%nat.
	rewrite size_cons_poly.
	case: nilP => //.
	rewrite -polyseq0 => /poly_inj /subr0_eq ->.
	by case: eqP => // /subr0_eq -> //.
rewrite cons_poly_def mulrBl polyC_sub.
rewrite addrAC addrA -cons_poly_def eq.
by rewrite cons_poly_def addrK subrr polyseq0.
Qed.

Lemma cons_poly_inj0:
	forall a p, cons_poly (a: R) p = 0 -> a = 0 /\ p = 0.
Proof.
move => a p.
rewrite (_ : 0 = 0 * 'X + 0); last by rewrite !rm0.
rewrite -cons_poly_def.
move => /cons_poly_inj [-> ->].
by rewrite cons_poly_def !rm0.
Qed.
End Poly_complements.