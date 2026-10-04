(** Load required packages.  Not all of these packages are needed right away,
    but they may be useful later. **)

Require Export Setoid List Ring Sorted Constructive_sets Utf8_core Wf_nat
        ProofIrrelevance Permutation IndefiniteDescription ChoiceFacts
        Description ssrfun ssrbool ssreflect.

(** Math symbols for cut and paste: ∀ ∃ → ↔ ∧ ∨ ¬ ≠ ≤ ≥ ∅ ℕ ℤ ∈ ∉ ⊂ ∑ ∏ λ **)

(** Axioms for the integers. **)

Parameter Z : Set.

Parameter add mult : Z → Z → Z.
Parameter neg : Z → Z.
Parameter zero one : Z.
Notation "0" := zero.
Notation "1" := one.
Infix "+" := add.
Infix "*" := mult.
Notation "- x" := (neg x).
Notation "- 0" := (neg 0).
Notation "- 1" := (neg 1).
Definition sub a b := a + -b.
Infix "-" := sub.

Axiom A1 : ∀ a b   : Z, a + b = b + a.
Axiom A2 : ∀ a b c : Z, a + (b + c) = (a + b) + c.
Axiom A3 : ∀ a     : Z, a + 0 = a.
Axiom A4 : ∀ a     : Z, a + -a = 0.
Axiom M1 : ∀ a b   : Z, a * b = b * a.
Axiom M2 : ∀ a b c : Z, a * (b * c) = (a * b) * c.
Axiom M3 : ∀ a     : Z, a * 1 = a.
Axiom D1 : ∀ a b c : Z, (a + b) * c = a * c + b * c.



Require Export Ring. 



Parameter N : Z → Prop.

Axiom N1 : ∃ z, N z.
Axiom N2 : ∀ a b, N a → N b → N (a+b).
Axiom N3 : ∀ a b, N a → N b → N (a*b).
Axiom N4 : ∀ a, (N a ∧ a ≠ 0 ∧ ¬ N (-a)) ∨ (¬ N a ∧ a = 0 ∧ ¬ N (-a)) ∨
                (¬ N a ∧ a ≠ 0 ∧ N (-a)).
Axiom N5 : ∀ S : Z → Prop, (∃ x, S x) → (∀ x, S x → N x) →
                           ∃ s, S s ∧ ∀ x, S x → x - s = 0 ∨ N (x - s).



Notation "a ∈ 'N'" := (N a) (at level 70).
  



Require Export ClassicalEpsilon.


(** Some useful lemmas. **)

Lemma S1 : ∀ a b c : Z, a = b → a + c = b + c. 

Proof. 

  intros a b c H. 

  rewrite H. 

  reflexivity. 

Qed. 

  

Lemma S2 : ∀ a b c : Z, a = b → a * c = b * c. 

Proof. 

  intros a b c H. 

  rewrite H. 

  reflexivity. 

Qed. 

  

Lemma S3: ∀ a b c : Z, a = b → a - c = b - c. 

Proof. 

intros a b c H. 

rewrite H. 

reflexivity. 

Qed. 

(** Homework assignment problems are given below. **) 

  

Lemma S4:∀ a : Z, (0+0)*a=0*a. 

intros a. 

rewrite A3. 

reflexivity. 

Qed. 

  

Lemma S5: 0=0. 

reflexivity. 

Qed. 

Lemma S7: ∀ a b : Z,(-a) * (-b) = (-a) * (-b). 

reflexivity. 

Qed. 

  

Theorem A1P1 : ∀ a : Z, 0 + a = a. 

Proof. 

intros a. 

rewrite A1. 

rewrite A3. 

reflexivity. 

Qed. 

  

  

Theorem A1P2 : ∀ a : Z, -a + a = 0. 

Proof. 

intros a. 

rewrite A1. 

rewrite A4. 

reflexivity. 

Qed. (* replace "Admitted." with "Qed." when your proof is finished. *) 

  

Theorem A1P3 : ∀ a : Z, 1 * a = a. 

Proof. 

intros a. 

rewrite M1. 

rewrite M3. 

reflexivity. 

Qed. (* replace "Admitted." with "Qed." when your proof is finished. *) 

  

Theorem A1P4 : ∀ a b : Z, a + b = 0 → b = -a. 

Proof. 

intros a b H. 

apply (S3 (a+b) 0 a) in H. 

rewrite A1 in H. 

unfold sub in H. 

rewrite -A2 in H. 

rewrite A4 in H. 

rewrite A3 in H. 

symmetry in H. 

rewrite A1 in H. 

rewrite A3 in H. 

symmetry in H. 

exact H. 

Qed. 




Theorem A1P5 : ∀ a : Z, -(-a) = a. 

Proof. 

intros a. 

pose proof (A4 (-a)). 

apply (S1 ((-a)+(--a)) 0 a) in H. 

rewrite A1 in H. 

rewrite A2 in H. 

rewrite A4 in H. 

rewrite A1 in H. 

rewrite A3 in H. 

symmetry in H. 

rewrite A1 in H. 

rewrite A3 in H. 

symmetry in H. 

exact H. 

Qed. 

  

Theorem A1P6 : ∀ a : Z, 0 * a = 0. 

Proof. 

intros a. 

pose proof S4. 

assert (∀ a, 0 * a + 0 * a = 0 * a). 

{ intros. 

  rewrite -D1 H. 

  reflexivity. } 

apply (S3 (0 * a + 0 * a) (0*a) (0*a)) in H0. 

unfold sub in H0. 

rewrite -A2 in H0. 

rewrite A4 in H0. 

rewrite A3 in H0. 

exact H0. 

Qed. 

  

Theorem A1P7 : ∀ a : Z, -1 * a = -a. 

Proof. 

intros a. 

pose proof A1P6. 

rewrite  -{1}(A4 1) in H. 

assert (∀ a, 1*a+(-1)*a=0). 

{ intros. 

  rewrite -D1 H. 

  reflexivity. } 

assert (∀ a : Z, a * 1 + -1 * a = 0). 

{ intros. 

rewrite M1. 

apply H0. } 

assert (∀ a : Z, a + -1 * a = 0). 

{intros. 
rewrite -{1}(M3 a0). 
apply H1. } 
apply (S3 (a + -1 * a) 0 (a)) in H2. 
rewrite A1 in H2. 
unfold sub in H2. 
rewrite -A2 in H2. 
rewrite A4 in H2. 
symmetry in H2. 
rewrite A1 in H2. 
rewrite A3 in H2. 
symmetry in H2. 
rewrite A3 in H2. 
exact H2. 
Qed. 



Theorem A1P8 : ∀ a b : Z, -a * -b = a * b. 

Proof. 

intros a b. 

rewrite -A1P7. 

rewrite (M1 (-1)). 

rewrite -M2. 

rewrite A1P7. 

rewrite A1P5. 

reflexivity. 

Qed. 

  

Theorem A1P9 : ∀ a b : Z, a + b = a → b = 0. 

Proof. 

intros a b H. 

apply (S3 (a+b) (a) (a)) in H. 

rewrite A1 in H. 

unfold sub in H. 

rewrite -A2 in H. 

rewrite A4 in H. 

rewrite A3 in H. 

exact H. 

Qed. 



(** The proof below is INCORRECT, even though Coq thinks it is correct.
    Find the error, and correct it. **)
Theorem Z5 : ∀ a : Z, a ≠ 0 → N a∨ N (-a).
intros.
pose proof (N4 a).
destruct H0.
destruct H0.
left.
exact.
destruct H0.
destruct H0.
destruct H1.
contradiction.
destruct H0.
destruct H1.
right.
exact.
Qed.

Theorem Z1: ∀ a : Z, N a -> ¬(a=0)∧ ¬(N (-a)) .
intros.
pose proof (N4 a).
destruct H0.
destruct H0.
exact H1.
destruct H0.
destruct H0.
contradiction.
destruct H0.
destruct H1.
contradiction.
Qed.

Theorem Z2: ∀ a : Z, -a ∈ N -> ¬(a∈N) ∧ ¬(a=0).
intros.
pose proof (N4 a).
destruct H0.
destruct H0.
destruct H1.
contradiction.
destruct H0.
destruct H0.
destruct H1.
contradiction.
destruct H0.
destruct H1.
split.
exact.
exact.
Qed.

Theorem Z4: ∀ a : Z, a=0 ∨ a∈N ∨ -a∈N.
intros.
pose proof (N4 a).
destruct H.
destruct H.
right.
left.
exact.
destruct H.
destruct H.
destruct H0.
left.
exact.
destruct H.
destruct H0.
right.
right.
exact.
Qed.

Theorem Ns1: ∀ a, a = 0 → ¬ a ∈N ∧ ¬ (-a)∈N.
intros.
pose proof (N4 a).
destruct H0.
destruct H0.
destruct H1.
contradiction.
destruct H0.
destruct H0.
destruct H1.
split.
exact.
exact.
destruct H0.
destruct H1.
contradiction.
Qed.


Theorem N_one: N 1.
intros.
pose proof (N4 1).
destruct H.
destruct H.
exact.
destruct H.
destruct H.
destruct H0.
assert(∀ a, a = 0). {
intros.
rewrite -(M3 a).
rewrite H0.
rewrite M1.
rewrite A1P6.
reflexivity.
}
pose proof N1.
rewrite H0 in H.
destruct H3.
replace x with 0 in H3.
contradiction.
rewrite (H2 x).
reflexivity.
destruct H.
destruct H0.
pose proof (N3 (-1) (-1) H1 H1).
pose proof (eq_refl ((-1)*(-1))).
rewrite A1P8 in H2.
rewrite (M3 1) in H2.
contradiction.
Qed.




Theorem A1P11 : ∀ a b : Z, a * b = 0 → a = 0 ∨ b = 0.
Proof. 

intros a b H. 

destruct (classic (a = 0)). 

by left. 

apply Z5 in H0. 

destruct H0. 

destruct (classic (b = 0)). 

right. 

exact H1. 

apply Z5 in H1. 

destruct H1. 

pose proof N3 a b H0 H1. 

pose proof Z1 (a*b) H2. 

destruct H3. 

contradiction. 

  

pose proof N3 a (-b) H0 H1. 

rewrite -A1P7 in H2.

rewrite M2 in H2. 

rewrite (M1 a) in H2. 

rewrite -M2 in H2. 

rewrite A1P7 in H2. 

pose proof Z2 (a*b) H2. 

destruct H3. 

contradiction. 

  

destruct (classic (b = 0)). 

right. 

exact H1. 

apply Z5 in H1. 

destruct H1. 

pose proof N3 (-a) (b) H0 H1. 

rewrite -A1P7 in H2. 

rewrite -M2 in H2. 

rewrite A1P7 in H2. 

pose proof Z2 (a*b) H2. 

destruct H3. 

contradiction. 

  

pose proof N3 (-a) (-b) H0 H1. 

rewrite A1P8 in H2. 

pose proof Z1 (a*b) H2. 

destruct H3. 

contradiction. 

Qed.

Theorem A1P10 : ∀ a b : Z, a * b = a ∧ a ≠ 0 → b = 1. 

Proof. 

intros a b H. 

destruct H.  

apply (S3 (a*b) a a) in H. 

unfold sub in H. 

rewrite A4 in H.	 

rewrite -A1P7 in H. 

rewrite (M1 (-1)) in H. 

rewrite (M1 a b) in H. 

rewrite (M1 a (-1)) in H. 

rewrite -D1 in H. 

apply A1P11 in H. 

destruct H. 

apply (S1 (b + -1) 0 1) in H. 

rewrite -A2 in H. 

rewrite (A1 (-1)) in H. 

rewrite A4 in H. 

rewrite (A1 0) in H. 

rewrite A3 in H. 

rewrite A3 in H. 

exact H. 

contradiction (H0 H). 

Qed. 

Require Export Ring.
Theorem E1 : ∀ a b, a-b = a-b. 

Proof. 

  reflexivity. 

Qed.  

Add Ring Z_ring : (mk_rt _ _ _ _ _ _ _ A1P1 A1 A2 A1P3 M1 M2 D1 E1 A4). 




  


Definition lt a b := (b - a) ∈ N.
Infix "<" := lt.
  

Notation "a > b" := (b < a) (only parsing). 

  

Require Export ClassicalEpsilon.  

  


  

Theorem add_lt_r : ∀ a b c, a < b → a + c < b + c. 

Proof. 

  intros. 

  unfold lt in *. 

  replace (b+c-(a+c)) with (b-a). 

  - exact H. 

  - ring. 

Qed. 


Definition divide (x y : Z) := ∃ z : Z, y = z * x.
Notation "( x | y )" := (divide x y).
Theorem A2P1 : ∀ a m n x y : Z, (a | m) → (a | n) → (a | m * x + n * y). 
Proof. 
intros. 
destruct H. 
destruct H0. 
rewrite H. 
rewrite H0. 
rewrite -M2. 
rewrite (M1 a). 
rewrite M2. 
rewrite -(M2 x1 a y). 
rewrite (M1 a y). 
rewrite M2. 
rewrite -D1.
unfold divide. 
exists(x0 * x + x1 * y). 
reflexivity. 
Qed.

Theorem A2P2: ∀ a b c : Z, (a | b) → (b | c) → (a | c). 
Proof. 
intros. 
destruct H. 
destruct H0. 
rewrite H in H0. 
rewrite H0. 
rewrite M2. 
exists (x0 * x). 
reflexivity. 
Qed. 


Theorem A2P3 : ∀ a b : Z, a < b ∨ a = b ∨ b < a. 
Proof. 
intros. 
unfold lt. 
pose proof (Z4 (a-b)). 
destruct H. 
apply (S1 (a-b) 0 b) in H. 
rewrite -A2 in H. 
rewrite (A1 (-b)) in H. 
rewrite A4 in H. 
rewrite (A1 0) in H. 
rewrite A3 in H. 
rewrite A3 in H. 
right. 
left. 
exact. 
destruct H. 
right. 
right. 
exact. 
rewrite -A1P7 in H. 
rewrite M1 in H. 
rewrite D1 in H. 
rewrite M1 in H. 
rewrite (M1 (-b)) in H. 
rewrite A1P7 in H. 
rewrite A1P7 in H. 
rewrite A1P5 in H. 
rewrite A1 in H. 
left. 
unfold sub. 
exact. 
Qed. 



Theorem A2P4 : ∀ a b c : Z, a < b → 0 < c → a * c < b * c. 
Proof. 
intros. 
unfold lt in *. 
rewrite -(A3 c) in H0. 
unfold sub in *. 
rewrite -A2 in H0. 
rewrite A4 in H0. 
rewrite A3 in H0. 
rewrite -A1P7. 
rewrite M2. 
rewrite -D1. 
rewrite A1P7. 
apply (N3 (b + -a) c). 
exact H. 
exact H0. 
Qed. 

Theorem A2P4_neg : ∀ a b c : Z, a < b → 0 > c → a * c > b * c.
Proof.
intros a b c H H0.
unfold lt in H0.
replace (0-c) with (-c-0) in H0 by ring.
pose proof A2P4 a b (-c) H H0 as H1.
unfold lt in *.
by replace (a * c - b * c) with (b * - c - a * - c) by ring.
Qed.

Theorem A2P5 : ∀ a b c : Z, a * c = b * c → c ≠ 0 → a = b. 
Proof. 
intros.
apply(S1 (a*c) (b*c) (-(b*c)))in H. 
rewrite A4 in H. 
rewrite -A1P7 in H. 
rewrite M2 in H. 
rewrite -D1 in H. 
rewrite A1P7 in H. 
apply (A1P11) in H. 
destruct H. 
apply (S1 (a+ -b) 0 b) in H. 
rewrite -A2 in H. 
rewrite (A1 (-b)) in H. 
rewrite A4 in H. 
rewrite (A1 0) in H. 
rewrite A3 in H. 
rewrite A3 in H. 
exact H. 
contradiction. 
Qed. 

Theorem A2P6 : ∀ a b c : Z, a < b → b < c → a < c. 
Proof. 
intros. 
unfold lt in *. 
replace (c-a) with (b-a+c-b). 
unfold sub in *. 
rewrite -A2. 
apply N2. 
exact H. 
exact H0. 
unfold sub. 
ring. 
Qed.
  
Theorem A2P7 : ∀ a : Z, ¬ a < a. 
Proof. 
intros. 
pose proof (eq_refl a). 
pose proof (Ns1 (a-a)). 
unfold lt. 
destruct H0. 
ring. 
exact. 
Qed.

(* A2P8 after A3P2 *)

Theorem MultG1: ∀ a b : Z, N a ∧ N b ∧ (1 < b ∨ 1 = b) -> (a * b > a ∨ a * b = a).
Proof.
intros.
destruct H.
destruct H0.
destruct H1.
apply (A2P4 1 b a) in H1.
unfold lt.
rewrite M1 M3 in H1.
unfold lt in H1.
rewrite M1 in H1.
left.
exact.
unfold lt.
replace (a-0) with a by ring.
exact.
apply (S2 1 b a) in H1.
rewrite M1 M3 in H1.
right.
symmetry.
rewrite M1.
exact.
Qed.



Definition le a b := a < b ∨ a = b.
Infix "≤" := le (at level 70).
Notation "a ≥ b" := (b ≤ a) (at level 70, only parsing).
Notation "a < b < c" := (a < b ∧ b < c).
Notation "a ≤ b < c" := (a ≤ b ∧ b < c) (at level 70, b at next level).
Notation "a < b ≤ c" := (a < b ∧ b ≤ c) (at level 70, b at next level).
Notation "a ≤ b ≤ c" := (a ≤ b ∧ b ≤ c) (at level 70, b at next level).

Definition pm (a b : Z) := (a = b ∨ a = -b).
Notation "a = ± b" := (pm a b) (at level 60).
Notation "x ≠ ± y" := (¬ (x = ± y)) (at level 60).
Definition assoc (a b : Z) := (a | b) ∧ (b | a).
Infix "~" := assoc (at level 70).
Definition unit a := (a | 1).

Theorem Nrange: ∀ a : Z, N a -> a ≥ 1.
Proof.
intros.
pose proof (A2P3 a 1).
unfold le.
pose proof (N5 N). 
destruct H1 as [s H1].
by (exists a).
auto.
destruct H1.
pose proof (A2P3 s 1).
pose proof N_one.
destruct H3.
apply (A2P4 s 1 s) in H3.
replace (1*s) with s in H3 by ring.
pose proof (N3 s s H1 H1).
apply H2 in H5.
destruct H5.
unfold lt in H3.
replace (s-s*s) with (-(s*s-s)) in H3 by ring.
apply Z2 in H3.
destruct H3.
contradiction.
unfold lt in H3.
replace (s-s*s) with (-(s*s-s)) in H3 by ring.
apply Z2 in H3.
destruct H3.
contradiction.
unfold lt.
replace (s-0) with s by ring.
exact.
destruct H3.
destruct H0.
apply H2 in H.
rewrite H3 in H.
unfold lt in H0.
destruct H.
replace (1-a) with (-(a-1)) in H0 by ring.
apply Z2 in H0.
destruct H0.
contradiction.
replace (1-a) with (-(a-1)) in H0 by ring.
apply Z2 in H0.
destruct H0.
contradiction.
destruct H0.
symmetry in H0.
right.
exact.
left.
exact.
apply H2 in H4.
unfold lt in H3.
destruct H4.
replace (s-1) with (-(1-s)) in H3 by ring.
apply Z2 in H3.
destruct H3.
contradiction.
replace (s-1) with (-(1-s)) in H3 by ring.
apply Z2 in H3.
destruct H3.
contradiction.
Qed.

Theorem A3S1: ∀ a b : Z, a<b → ¬(a = b) ∧ ¬(b < a).
split.
unfold not.
intros.
apply Z1 in H.
apply (S1 a b (-a)) in H0.
rewrite A4 in H0.
unfold sub in H.
symmetry in H0.
destruct H.
contradiction.
unfold lt in *.
apply Z1 in H.
destruct H.
replace (a-b)  with (- (b - a)) by ring.
exact.
Qed.

 
Theorem A3P1 : 0 ≠ 1.
Proof.
unfold not.
intros.
pose proof N_one.
apply Z1 in H0.
destruct H0.
symmetry in H.
contradiction.
Qed.



Theorem A3P2 : ∀ a b : Z, 0 < a → (0 < b ↔ 0 < a * b).
Proof.
split.
intros.
unfold lt in *.
unfold sub in *.
rewrite -A1P7 M1 A1P6 A3 in H.
rewrite -A1P7 M1 A1P6 A3 in H0.
rewrite -A1P7.
rewrite (M1 (-1)).
rewrite A1P6 A3.
apply (N3 a b H H0).
intros.
unfold lt in *.
unfold sub in *.
rewrite -A1P7 M1 A1P6 A3 in H.
rewrite -A1P7 M1 A1P6 A3.
rewrite -A1P7 in H0.
rewrite (M1 (-1)) in H0.
rewrite A1P6 A3 in H0.
pose proof (Z4 b).
destruct H1.
rewrite H1 in H0.
rewrite M1 A1P6 in H0.
pose proof (Ns1 b H1).
destruct H2.
rewrite H1 in H2.
contradiction.
destruct H1.
exact.
pose proof (N3 a (-b) H H1).
rewrite -A1P7 in H2.
rewrite M2 in H2.
rewrite (M1 a) in H2.
rewrite -M2 in H2.
rewrite A1P7 in H2.
apply Z2 in H2.
destruct H2.
contradiction.
Qed.
Notation "2" := (1+1). 

Theorem A2P8 : ¬ (2 | 1). 
Proof. 
unfold not.
intros.
unfold divide in H.
destruct H as [z].
pose proof (MultG1 2 z).
pose proof (Z4 z).
destruct H1.
rewrite H1 in H.
replace (0*2) with 0 in H by ring.
pose proof A3P1.
symmetry in H.
contradiction.
destruct H1.
destruct H0.
split.
apply N2.
by pose proof N_one.
by pose proof N_one.
split.
exact.
pose proof (Nrange z H1).
exact.
rewrite M1 in H.
rewrite -H in H0.
unfold lt in H0.
replace (1-2) with (-1) in H0.
pose proof N_one.
apply Z2 in H2.
exact.
exact.
by ring.
pose proof A1P10 2 z.
destruct H2.
split.
exact.
assert(N 2). {
pose proof N_one.
by pose proof (N2 1 1 H2 H2).
}
apply Z1 in H2.
destruct H2.
exact.
rewrite M1 in H.
rewrite H0 in H.
apply (S1 z (z+z) (-z)) in H.
replace (z+-z) with 0 in H by ring.
replace (z+z+-z) with z in H by ring.
apply Z1 in H1.
destruct H1.
symmetry in H.
contradiction.
pose proof A3P2 2 z.
destruct H2.
unfold lt.
replace (2-0) with 2 by ring.
pose proof N_one.
apply (N2 1 1 H2 H2).
rewrite M1 in H.
unfold lt in *.
pose proof N_one.
rewrite H in H4.
replace (2*z-0) with (2*z) in H3 by ring.
apply H3 in H4.
replace (z-0) with z in H4 by ring.
apply Z2 in H1.
destruct H1.
contradiction.
Qed.

Theorem A3P3a : ∀ a b, a < b ↔ ¬ b ≤ a.
Proof.
unfold not.
split.
intros.
apply A3S1 in H.
unfold le in *.
destruct H0.
destruct H.
contradiction.
destruct H.
symmetry in H0.
contradiction.
intros.
unfold le in H.
pose proof (A2P3 a b).
destruct H0.
exact.
apply or_comm in H0.
destruct H.
destruct H0.
left.
exact.
symmetry in H.
right.
exact.
Qed.

Theorem A3P3b : ∀ a b, a ≤ b ↔ ¬ b < a.
Proof.
intros.
pose proof (A3P3a b a).
assert ((a ≤ b) → ¬ ( b < a)) by tauto.
split.
exact.
assert(¬ b < a → a ≤ b) by tauto.
exact.
Qed.


Theorem A3P4 : ∀ a : Z, 0 < a → ¬ a < 1.
Proof.
unfold not.
intros.
unfold lt in *.
unfold sub in H.
pose proof Nrange(a).
rewrite -A1P7 M1 A1P6 A3 in H.
apply H1 in H.
unfold le in H.
destruct H.
unfold lt in *.
replace (1-a) with (-(a-1)) in H0 by ring.
apply Z2 in H0.
destruct H0.
contradiction.
replace (1-a) with (-(a-1)) in H0 by ring.
apply Z2 in H0.
destruct H0.
apply (S1 1 a (-a)) in H.
replace (a+(-a)) with 0 in H by ring.
replace (1+(-a)) with (-(a-1)) in H by ring.
apply (S2 (- (a - 1)) 0 (-1)) in H.
replace (0*(-1)) with 0 in H by ring.
replace (- (a - 1) * -1) with (a-1) in H by ring.
contradiction.
Qed.

Theorem OneDivideZero: (1 | 0).
Proof.
unfold divide.
exists 0.
by rewrite A1P6.
Qed.

Theorem not_A3P5 : ¬(∀ a b : Z, (a | b) → a ≤ b).
Proof.
unfold not.
intros.
pose proof OneDivideZero.
unfold divide in *.
apply H in H0.
unfold le in H0.
unfold lt in *.
destruct H0.
replace (0-1) with (-1) in H0 by ring.
apply Z2 in H0.
pose proof  N_one.
destruct H0.
contradiction.
pose proof A3P1.
symmetry in H0.
contradiction.
Qed.

Theorem A3P5 : ∀ a b : Z, (a | b) ∧ b>0 → a ≤ b.
Proof.
intros.
unfold divide in H.
unfold le.
destruct H.
unfold lt in H0.
replace (b-0) with b in H0.
apply Z1 in H0.
destruct H0.
rename H1 into H88.
destruct H as [z].
pose proof (Z4 b).
pose proof (Z4 a).
pose proof (Z4 z).
destruct H1 as [ | [ | ]], H2 as [ | [ | ]], H3 as [ | [ | ]]; auto.
rewrite -H2 in H1.
symmetry in H1.
right.
exact.
rewrite -H2 in H1.
symmetry in H1.
right.
exact.
rewrite -H2 in H1.
symmetry in H1.
right.
exact.
contradiction.
contradiction.
contradiction.
contradiction.
contradiction.
contradiction.
rewrite H2 in H.
rewrite H3 in H.
rewrite A1P6 in H.
contradiction.
rewrite H2 in H.
rewrite M1 A1P6 in H.
contradiction.
rewrite H2 in H.
rewrite M1 A1P6 in H.
contradiction.
rewrite H3 in H.
rewrite A1P6 in H.
contradiction.
pose proof Nrange z H3.
pose proof (MultG1 a z).
destruct H5.
split.
exact.
split.
exact.
exact.
rewrite M1 in H.
rewrite -H in H5.
left.
exact.
rewrite M1 in H.
rewrite -H in H5.
right.
symmetry.
exact.
replace (z*a) with (-((-z)*a)) in H by ring.
pose proof (N3 (-z) a  H3 H2).
apply (S2 b (- (- z * a)) (-1)) in H.
replace (- (- z * a) * -1) with (- z * a) in H by ring.
replace (b * -1) with (-b) in H by ring.
rewrite -H in H4.
apply Z2 in H4.
destruct H4.
contradiction.
rewrite H3 in H.
rewrite A1P6 in H.
contradiction.
pose proof (N3 (-a) z H2 H3).
replace (z*a) with (-(z*(-a))) in H by ring.
apply (S2 b (- ( z * - a)) (-1)) in H.
replace (- ( z * -a) * -1) with ( z * -a) in H by ring.
replace (b * -1) with (-b) in H by ring.
rewrite M1 in H.
rewrite -H in H4.
apply Z2 in H4.
destruct H4.
contradiction.
pose proof Nrange (-z) H3.
pose proof (MultG1 (-a) (-z)).
destruct H5.
split.
exact.
split.
exact.
exact.
replace (z*a) with (-a * -z) in H by ring.
rewrite -H in H5.
left.
assert(a<0). {
unfold lt.
unfold sub.
rewrite A1 A3.
exact.
}
assert(b>0). {
unfold lt.
replace (b-0) with b by ring.
exact.
}
pose proof (A2P6 a 0 b H6 H7).
exact.
replace (z*a) with (-a * -z) in H by ring.
rewrite -H in H5.
assert(a<0). {
unfold lt.
unfold sub.
rewrite A1 A3.
exact.
}
assert(b>0). {
unfold lt.
replace (b-0) with b by ring.
exact.
}
pose proof (A2P6 a 0 b H6 H7).
left.
exact.
rewrite H2 in H.
rewrite M1 A1P6 in H.
contradiction.
rewrite H2 in H.
rewrite M1 A1P6 in H.
contradiction.
rewrite H2 in H.
rewrite M1 A1P6 in H.
contradiction.
rewrite H3 in H.
rewrite A1P6 in H.
contradiction.
pose proof (N3 a z H2 H3).
rewrite M1 in H.
rewrite -H in H4.
apply Z2 in H1.
destruct H1.
contradiction.
contradiction.
contradiction.
contradiction.
contradiction.
by ring.
Qed.


Theorem A3P6 : ∀ a, unit a ↔ a = ± 1.
Proof.
unfold unit.
unfold pm.
split.
intros.
pose proof H as Hd.
unfold divide in H.
destruct H as [z].
pose proof (Z4 z).
destruct H0.
rewrite H0 in H.
rewrite A1P6 in H.
contradiction A3P1.
symmetry.
exact.
destruct H0.
pose proof H0 as Hd2.
apply Nrange in H0.
pose proof (Z4 a).
destruct H1.
rewrite H1 in H.
rewrite M1 A1P6 in H.
contradiction A3P1.
symmetry.
exact.
destruct H1.
pose proof MultG1 a z.
destruct H2.
split.
exact.
split.
exact.
exact.
rewrite M1 in H.
rewrite -H in H2.
apply Nrange in H1.
apply A3P3a in H2.
contradiction.
rewrite M1 in H2.
rewrite H2 in H.
symmetry in H.
left.
exact.
pose proof A3P2 z a.
destruct H2.
unfold lt.
replace (z-0) with z.
exact.
by ring.
pose proof N_one.
rewrite H in H4.
assert(z*a>0). {
unfold lt.
replace (z*a-0) with (z*a) by ring.
exact.
}
apply H3 in H5.
unfold lt in H5.
replace (a-0) with a in H5 by ring.
apply Z2 in H1.
destruct H1.
contradiction.
pose proof (Z4 a).
destruct H1.
rewrite H1 in H.
rewrite M1 A1P6 in H.
contradiction A3P1.
symmetry.
exact.
destruct H1.
pose proof A3P2 a z.
destruct H2.
unfold lt.
replace (a-0) with a by ring.
exact.
assert(a*z>0). {
unfold lt.
replace (a*z-0) with (a*z) by ring.
pose proof N_one.
rewrite H in H4.
rewrite M1.
exact.
}
apply H3 in H4.
unfold lt in H4.
replace (z-0) with z in H4.
apply Z2 in H0.
destruct H0.
contradiction.
by ring.
pose proof MultG1 (-a) (-z).
destruct H2.
split.
exact.
split.
exact.
pose proof Nrange (-z) H0.
exact.
replace (z*a) with (-a*-z) in H by ring.
rewrite -H in H2.
apply Nrange in H1.
apply A3P3a in H2.
contradiction.
replace (z*a) with (-a*-z) in H by ring.
rewrite -H in H2.
apply (S2 1 (-a) (-1)) in H2.
replace (1*-1) with (-1) in H2 by ring.
replace (-a*-1) with a in H2 by ring.
right.
symmetry.
exact.

intros.
destruct H.
exists 1.
rewrite H.
by rewrite M3.
exists (-1).
rewrite H.
by replace (-1*-1) with 1 by ring.
Qed.


(* Well-ordering principle *)

Theorem A3P7 : ∀ S : Z → Prop,
    (∀ x, S x → 0 < x) → (∃ x, S x) → ∃ s, S s ∧ ∀ t, S t → s ≤ t.
Proof.
unfold le.
unfold lt.
unfold sub in *.
intros.
pose proof (N5 S).
destruct H1.
exact.
intros.
replace x with (x+-0) by ring.
by apply H.
exists x.
split.
destruct H1.
exact.
destruct H1.
intros.
pose proof (H2 t H3).
destruct H4.
apply (S1 (t-x) 0 x) in H4.
replace (t-x+x) with t in H4 by ring.
replace (0+x) with x in H4 by ring.
right.
symmetry.
exact.
unfold sub in H4.
left.
exact.
Qed.



(* Definition and properties of absolute value. *)

Require Export ClassicalDescription.

Section absolute_value.

  Definition abs a : Z :=
    if excluded_middle_informative (0 < a) then a else (-a).

  Notation "| a |" := (abs a) (at level 35, format "'|' a '|'").
  Notation "|- a |" := (abs (neg a)) (at level 35, format "'|-' a '|'").

  Lemma abs_pos : ∀ a : Z, 0 < a → |a| = a.
  Proof.
    intros a H.
    unfold abs.
    destruct excluded_middle_informative; simpl; auto.
    contradiction.
  Qed.

  Lemma abs_neg : ∀ a : Z, a < 0 → |a| = -a.
  Proof.
    intros a H.
    unfold abs.
    destruct excluded_middle_informative; simpl; auto.
    contradiction (A2P7 a); eauto using A2P6.
  Qed.

  Lemma abs_zero : |0| = 0.
  Proof.
    unfold abs.
    destruct excluded_middle_informative; simpl; auto.
    ring.
  Qed.

  Lemma abs_pm : ∀ a : Z, |a| = ± a.
  Proof.
    intros a.
    unfold abs, pm.
    destruct excluded_middle_informative; auto.
  Qed.

End absolute_value.

Notation "| a |" := (abs a) (at level 35, format "'|' a '|'").
Notation "|- a |" := (abs (neg a)) (at level 35, format "'|-' a '|'").

Theorem A4P1 : ∀ a : Z, |a| = |-a|.
Proof.
intros.
pose proof Z4 a.
destruct H.
rewrite H.
by replace (-0) with 0 by ring.
destruct H.
assert(a>0). {
unfold lt.
by replace (a-0) with a by ring. }
apply abs_pos in H0.
rewrite H0.
assert(-a<0). {
unfold lt.
by replace (0--a) with a by ring. }
apply abs_neg in H1.
replace (--a) with a in H1 by ring.
rewrite H1.
exact.
assert(a<0). {
unfold lt.
by replace (0-a) with (-a) by ring. }
apply abs_neg in H0.
rewrite H0.
assert(-a>0). {
unfold lt.
by replace (-a-0) with (-a) by ring. }
apply abs_pos in H1.
rewrite H1.
exact.
Qed.

Theorem A4P2 : ∀ a : Z, 0 ≤ |a|.
Proof.
intros.
pose proof Z4 a.
destruct H.
unfold le.
right.
rewrite H.
symmetry.
apply abs_zero.
destruct H.
unfold le.
unfold lt.
left.
replace (|a| -0) with (|a|) by ring.
assert (a>0). {
unfold lt.
by replace (a-0) with a by ring. }
apply abs_pos in H0.
by rewrite H0.
unfold le.
left.
unfold lt.
replace (|a| - 0) with (|a|) by ring.
assert (a<0). {
unfold lt.
by replace (0-a) with (-a) by ring. }
apply abs_neg in H0.
by rewrite H0.
Qed.


Theorem A4P3 : ∀ a : Z, a ≤ |a|.
Proof.
intros.
pose proof Z4 a.
unfold le.
unfold lt.
destruct H.
right.
rewrite H.
symmetry.
by apply abs_zero.
destruct H.
right.
assert (a>0). {
unfold lt.
by replace (a-0) with a by ring. }
apply abs_pos in H0.
by symmetry.
left.
unfold sub.
assert (a<0). {
unfold lt.
by replace (0-a) with (-a) by ring. }
apply abs_neg in H0.
rewrite H0.
apply (N2 (-a) (-a) H H).
Qed.

Theorem Divide_neg : ∀ a b : Z, (a|b) -> (a|(-b)).
intros.
unfold divide in *.
destruct H as [z].
exists (-z).
apply (S2 (b) (z*a) (-1)) in H.
replace (b*-1) with (-b) in H by ring.
replace (z*a*-1) with (-z*a) in H by ring.
exact.
Qed.

Theorem Divide_neg2 : ∀ a b : Z, (a|b) -> ((-a)|b).
intros.
unfold divide in *.
destruct H as [z].
exists (-z).
replace (-z*-a) with (z*a) by ring.
exact.
Qed.

Theorem Divide_neg3 : ∀ a b : Z, (a|b) -> ((-a)|(-b)).
intros.
unfold divide in *.
destruct H as [z].
exists (z).
apply (S2 b (z*a) (-1)) in H.
replace (z*a*-1) with (z*-a) in H by ring.
replace (b*-1) with (-b) in H by ring.
exact.
Qed.

Theorem A4P4 : ∀ a b : Z, a ~ b ↔ ∃ u : Z, unit u ∧ b = a * u.
Proof.
split.
intros.
unfold assoc in *.
destruct H.
pose proof (A2P3 a b).
pose proof (Z4 a).
pose proof (Z4 b).
destruct H2.
destruct H3.
rewrite H2 H3.
exists 1.
split.
exists 1.
by ring.
by ring.
destruct H3.
rewrite H2.
replace (0*1) with 0 by ring.
assert(b>0). {
unfold lt.
replace (b-0) with b by ring.
exact. }
unfold divide in *.
rewrite H2 in H.
rewrite H2 in H0.
destruct H, H0 as [z].
rewrite M1 A1P6 in H.
apply Z1 in H3.
destruct H3.
absurd (b=0).
exact.
exact.
rewrite H2.
replace (0*1) with 0 by ring.
unfold divide in *.
rewrite H2 in H.
rewrite H2 in H0.
destruct H, H0 as [z].
rewrite M1 A1P6 in H.
exists 1.
split.
exists 1.
by ring.
rewrite A1P6.
exact.
destruct H2.
destruct H3.
rewrite H3.
exists 1.
split.
exists 1.
rewrite M3.
exact.
unfold divide in *.
rewrite H3 in H.
rewrite H3 in H0.
destruct H, H0 as [z].
rewrite M1 A1P6 in H0.
rewrite H0.
by ring.
destruct H3.
assert(b>0). {
unfold lt.
replace (b-0) with b by ring.
exact. }
pose proof A3P5 a b.
destruct H5.
split.
exact.
exact.
pose proof A3P5 b a.
destruct H6.
split.
exact.
unfold lt.
replace (a-0) with a by ring.
exact.
pose proof A3P3b a b.
destruct H7.
destruct H7.
unfold le.
left.
exact.
exact.
exists 1.
split.
exists 1.
by ring.
rewrite H6.
by ring.
exists 1.
split.
exists 1.
by ring.
rewrite H5.
by ring.
pose proof A3P5 a (-b).
destruct H4.
split.
apply Divide_neg.
exact.
unfold lt.
replace (-b-0) with (-b) by ring.
exact.
pose proof A3P5 (-b) a.
destruct H5.
split.
apply Divide_neg2.
exact.
unfold lt.
replace (-b-0) with (-b) by ring.
replace (a-0) with a by ring.
exact.
pose proof A3P3b a (-b).
destruct H6.
destruct H6.
unfold le.
left.
exact.
exact.
exists (-1).
split.
exists (-1).
by ring.
apply (S2 (-b) a (-1)) in H5.
replace (-b*-1) with b in H5 by ring.
exact.
exists (-1).
split.
exists (-1).
by ring.
apply (S2 a (-b) (-1)) in H4.
replace (-b*-1) with b in H4 by ring.
by symmetry.
destruct H3.
exists 1.
split.
exists 1.
by ring.
rewrite H3.
unfold divide in *.
rewrite H3 in H.
rewrite H3 in H0.
destruct H, H0 as [z].
rewrite M1 A1P6 in H0.
rewrite H0.
by ring.
destruct H3.
pose proof A3P5 (-a) b.
destruct H4.
split.
apply Divide_neg2.
exact.
unfold lt.
replace (b-0) with b by ring.
exact.
pose proof A3P5 b (-a).
destruct H5.
split.
apply Divide_neg.
exact.
unfold lt.
replace (-a-0) with (-a) by ring.
exact.
pose proof A3P3b (-a) b.
destruct H6.
destruct H6.
unfold le.
left.
exact.
exact.
exists (-1).
split.
exists (-1).
by ring.
rewrite H5.
by ring.
exists (-1).
split.
exists (-1).
by ring.
rewrite -H4.
by ring.
pose proof A3P5 (-a) (-b).
destruct H4.
split.
apply Divide_neg3.
exact.
unfold lt.
replace (-b-0) with (-b) by ring.
exact.
pose proof A3P5 (-b) (-a).
destruct H5.
split.
apply Divide_neg3.
exact.
unfold lt.
replace (-a-0) with (-a) by ring.
exact.
pose proof A3P3b (-a) (-b).
destruct H6.
destruct H6.
unfold le.
left.
exact.
exact.
exists 1.
split.
exists 1.
by ring.
apply (S2 (-b) (-a) (-1)) in H5.
replace (-b*-1) with (b) in H5 by ring.
replace (-a*-1) with (a*1) in H5 by ring.
exact.
exists 1.
split.
exists 1.
by ring.
apply (S2 (-a) (-b) (-1)) in H4.
replace (-b*-1) with (b) in H4 by ring.
replace (-a*-1) with (a*1) in H4 by ring.
exact.
intros.
unfold assoc.
unfold divide.
destruct H.
destruct H.
apply A3P6 in H.
unfold pm in H.
destruct H.
rewrite H in H0.
rewrite M3 in H0.
split.
exists 1.
rewrite H0.
by ring.
exists 1.
rewrite -H0.
by ring.
rewrite H in H0.
split.
exists (-1).
rewrite H0.
by ring.
exists (-1).
rewrite H0.
by ring.
Qed.

Theorem A4P5 : ∀ a b : Z, a ~ b ↔ a = ± b.
Proof.
split.
intros.
apply A4P4 in H.
destruct H.
destruct H.
apply A3P6 in H.
unfold pm in *.
destruct H.
rewrite H in H0.
left.
rewrite H0.
by ring.
rewrite H in H0.
right.
rewrite H0.
by ring.
intros.
unfold assoc.
unfold pm in H.
split.
destruct H.
exists 1.
rewrite H.
by ring.
exists (-1).
rewrite H.
by ring.
destruct H.
exists 1.
rewrite H.
by ring.
exists (-1).
rewrite H.
by ring.
Qed.


Theorem A4P6 : ∀ a b : Z, (a | b) → b ≠ 0 → a ≤ |b|.
Proof.
intros.
pose proof Z4 b.
unfold le.
destruct H1.
contradiction.
destruct H1.
pose proof Nrange b H1.
pose proof A3P5 a b.
destruct H3.
split.
exact.
destruct H2.
pose proof A2P6 0 1 b.
assert(0<1). {
unfold lt.
replace (1-0) with 1 by ring.
apply N_one. }
apply H3 in H4.
exact.
exact.
rewrite -H2.
unfold lt.
replace (1-0) with 1 by ring.
by apply N_one.
left.
rewrite abs_pos.
destruct H2.
pose proof A2P6 0 1 b.
assert(0<1). {
unfold lt.
replace (1-0) with 1 by ring.
apply N_one. }
apply H4 in H5.
exact.
exact.
rewrite -H2.
unfold lt.
replace (1-0) with 1 by ring.
by apply N_one.
exact.
right.
rewrite abs_pos.
destruct H2.
pose proof A2P6 0 1 b.
assert(0<1). {
unfold lt.
replace (1-0) with 1 by ring.
apply N_one. }
apply H4 in H5.
exact.
exact.
rewrite -H2.
unfold lt.
replace (1-0) with 1 by ring.
by apply N_one.
exact.
pose proof Nrange (-b) H1.
pose proof A3P5 a (-b).
apply Divide_neg in H.
destruct H3.
split.
exact.
destruct H2.
pose proof A2P6 0 1 (-b).
assert(0<1). {
unfold lt.
replace (1-0) with 1 by ring.
apply N_one. }
apply H3 in H4.
exact.
exact.
rewrite -H2.
unfold lt.
replace (1-0) with 1 by ring.
by apply N_one.
left.
rewrite abs_neg.
unfold lt.
replace (0-b) with (-b) by ring.
exact.
exact.
right.
rewrite abs_neg.
unfold lt.
replace (0-b) with (-b) by ring.
exact.
exact.
Qed.


Theorem WOP : ∀ S : Z → Prop,
    (∀ x, S x → 0 ≤ x) → (∃ x, S x) → ∃ s, S s ∧ ∀ t, S t → s ≤ t.
intros.
unfold le in H.
firstorder.
pose proof (classic (S 0)).
destruct H1.
exists 0.
split.
exact.
intros.
unfold le.
apply H in H2.
destruct H2.
by left.
by right.
pose proof A3P7 S.
destruct H2.
intros.
destruct (H x0).
exact.
exact.
rewrite -H3 in H2.
contradiction.
exists x.
exact.
exists x0.
exact.
Qed.

(* Division algorithm *)
Theorem A4P7 : ∀ a b, 0 < a → 0 < b → ∃ q r : Z, a = b * q + r ∧ 0 ≤ r < b.
Proof.
intros.
Definition S := (∀ x a b: Z, b-x*a>0).
set (S := λ r, 0 ≤ r ∧ ∃ q, r = a - b * q).
pose proof WOP S.
destruct H1.
assert (∀ x : Z, S x → 0 ≤ x).
{ unfold S.
  intros.
  destruct H1.
exact. }
exact.
unfold S.
exists a.
split.
unfold le.
left.
exact.
exists 0.
by ring.
destruct H1.
pose proof A2P3 x b.
destruct H3.
unfold S in H1.
destruct H1.
destruct H4 as [q].
exists q.
exists x.
split.
rewrite H4.
by ring_simplify.
exact.
destruct H3.
unfold S in H1.
destruct H1.
destruct H4 as [q].
assert (a - b * q -b<x). {
rewrite -H4.
unfold lt.
replace (x - (x - b)) with b by ring.
unfold lt in H0.
replace (b-0) with b in H0 by ring.
exact. }
replace (a - b * q - b) with (a-b*(q+1)) in H5 by ring.
assert (S (a - b * (q + 1))). {
unfold S.
split.
replace (a-b*(q+1)) with (a - b * q - b) by ring.
rewrite -H4.
rewrite H3.
ring_simplify.
unfold le.
right.
exact.
exists (q+1).
exact. }
apply H2 in H6.
pose proof A3P3b x (a - b * (q + 1)).
destruct H7.
destruct H7.
exact.
exact.
unfold S in H1.
destruct H1.
destruct H4 as [q].
rewrite H4 in H3.
apply (add_lt_r (b) (a - b * q) (-b)) in H3.
replace ( b + - b) with 0 in H3 by ring.
assert (x > a - b * q + - b). {
rewrite -H4.
unfold lt.
replace (x - (x + - b)) with b by ring.
unfold lt in H0.
replace (b-0) with b in H0 by ring.
exact. }
assert (S (a - b * q + - b)). {
unfold S.
split.
unfold le.
left.
exact.
exists (q+1).
by ring. }
apply H2 in H6.
pose proof A3P3b x (a - b * q + - b).
destruct H7.
destruct H7.
exact.
exact.
Qed.

(* "Relatively prime" *)
Definition rel_prime (a b : Z) := ∀ d : Z, (d | a) → (d | b) → unit d.

Theorem rel_prime_sym : ∀ a b : Z, rel_prime a b ↔ rel_prime b a.
Proof.
  firstorder.
Qed.

Theorem rel_prime_1 : ∀ a : Z, rel_prime a 1.
Proof.
  firstorder.
Qed.

Theorem A5P1 : ∀ a : Z, rel_prime a 0 ↔ unit a.
Proof.
split.
unfold rel_prime in *.
intros.
unfold unit.
destruct (H a).
exists 1.
by ring.
exists 0.
by ring.
exists x.
exact.
intros.
unfold unit in *.
unfold rel_prime.
apply A3P6 in H.
unfold pm in H.
destruct H.
rewrite H.
intros.
unfold unit.
exact.
intros.
rewrite H in H0.
unfold unit.
unfold divide in *.
destruct H0 as [z].
exists (-z).
replace (-z*d) with (-(z*d)) by ring.
rewrite -H0.
by ring.
Qed.


Theorem A5P2 : ∀ a b : Z, rel_prime a b ↔ rel_prime a (-b).
Proof.
split.
intros.
unfold rel_prime in *.
intros.
destruct (H d).
exact.
unfold divide in *.
destruct H1 as [z].
exists (-z).
replace (-z*d) with (-(z*d)) by ring.
rewrite -H1.
by ring.
exists x.
exact.
unfold rel_prime.
intros.
destruct (H d).
exact.
unfold divide in *.
destruct H1 as [z].
exists (-z).
apply (S2 b (z*d) (-1)) in H1.
ring_simplify in H1.
exact.
exists x.
exact.
Qed.

Theorem A5P3 : ∀ a b c : Z, (a | b) → rel_prime b c → rel_prime a c.
Proof.
unfold rel_prime.
intros.
destruct (H0 d).
firstorder.
unfold divide.
exists (x1*x0).
replace (x1 * x0 * d) with (x0*(x1*d)) by ring.
rewrite -H1.
exact.
exact.
exists x.
exact.
Qed.

Definition bezout a b d := ∃ x y, a * x + b * y = d.
Add Morphism bezout with signature pm ==> pm ==> pm ==> iff as Z_pm_bezout.
Proof.
  unfold bezout.
  intros a1 a2 [H | H] b1 b2 [H0 | H0] d1 d2 [H1 | H1]; subst; intuition; destruct H as [x [y]]; rewrite -? H -1 ? (A1P5 d2) -? H;
  try (exists x, y; ring);
  try (exists x, (-y); ring);
  try (exists (-x), y; ring);
  try (exists (-x), (-y); ring).
Qed.


Theorem Div_alg : ∀ a b, 0 < b → ∃ q r : Z, a = b * q + r ∧ 0 ≤ r < b.
Proof.
pose proof A1P1.
intros.
set (S := λ r, 0 ≤ r ∧ ∃ q, r = a - b * q).
pose proof WOP S.
destruct H1.
assert (∀ x : Z, S x → 0 ≤ x).
{ unfold S.
  intros.
  destruct H1.
exact. }
exact.
unfold S.
pose proof Z4 a as H100.
destruct H100.
exists a.
split.
unfold le.
right.
exact.
exists 0.
by ring.
destruct H1.
exists a.
split.
unfold le.
left.
unfold lt.
replace (a-0) with a by ring.
exact.
exists 0.
ring_simplify.
exact.
exists (a-b*a).
split.
replace (a-b*a) with (a*(1-b)) by ring.
pose proof Nrange b.
destruct H2.
unfold lt in H0.
replace (b-0) with b in H0 by ring.
exact.
unfold lt in H2.
replace (a * (1 - b)) with ((-a*(b-1))) by ring.
unfold le.
left.
unfold lt.
pose proof N3 (-a) (b-1) H1 H2.
replace (- a * (b - 1) - 0) with (- a * (b - 1)) by ring.
exact.
rewrite -H2.
unfold le.
right.
by ring.
exists a.
exact.
destruct H1.
pose proof A2P3 x b.
destruct H3.
unfold S in H1.
destruct H1.
destruct H4 as [q].
exists q.
exists x.
split.
rewrite H4.
by ring_simplify.
exact.
destruct H3.
unfold S in H1.
destruct H1.
destruct H4 as [q].
assert (a - b * q -b<x). {
rewrite -H4.
unfold lt.
replace (x - (x - b)) with b by ring.
unfold lt in H0.
replace (b-0) with b in H0 by ring.
exact. }
replace (a - b * q - b) with (a-b*(q+1)) in H5 by ring.
assert (S (a - b * (q + 1))). {
unfold S.
split.
replace (a-b*(q+1)) with (a - b * q - b) by ring.
rewrite -H4.
rewrite H3.
ring_simplify.
unfold le.
right.
exact.
exists (q+1).
exact. }
apply H2 in H6.
pose proof A3P3b x (a - b * (q + 1)).
destruct H7.
destruct H7.
exact.
exact.
unfold S in H1.
destruct H1.
destruct H4 as [q].
rewrite H4 in H3.
apply (add_lt_r (b) (a - b * q) (-b)) in H3.
replace ( b + - b) with 0 in H3 by ring.
assert (x > a - b * q + - b). {
rewrite -H4.
unfold lt.
replace (x - (x + - b)) with b by ring.
unfold lt in H0.
replace (b-0) with b in H0 by ring.
exact. }
assert (S (a - b * q + - b)). {
unfold S.
split.
unfold le.
left.
exact.
exists (q+1).
by ring. }
apply H2 in H6.
pose proof A3P3b x (a - b * q + - b).
destruct H7.
destruct H7.
exact.
exact.
Qed.
(* Euclidean algorithm / Bezout's lemma *)
Theorem A5P4 : ∀ a b : Z, rel_prime a b → ∃ x y, a * x + b * y = 1.
Proof.
intros.
unfold rel_prime in H.
Definition Set1 := (∀ x y a b: Z, a * x + b * y>0).
set (Set1 := λ r, 0 < r ∧ ∃ x y, r = a * x + b * y).
pose proof A3P7 Set1.
destruct H0.
assert(∀ x : Z, Set1 x → 0 < x). {
unfold Set1.
intros.
destruct H0.
exact. }
exact.
unfold Set1.
pose proof Z4 a.
pose proof Z4 b.
destruct H0.
destruct H1.
destruct (H 0).
exists 0.
rewrite H0.
by ring.
exists 0.
rewrite H1.
by ring.
ring_simplify in H2.
contradiction A3P1.
exact.
destruct H1.
exists b.
split.
unfold lt.
replace (b-0) with b by ring.
exact.
exists 0.
exists 1.
ring_simplify.
exact.
exists (-b).
split.
unfold lt.
replace (-b-0) with (-b) by ring.
exact.
exists 0.
exists (-1).
ring_simplify.
exact.
destruct H0.
destruct H1.
exists a.
split.
unfold lt.
replace (a-0) with a by ring.
exact.
exists 1.
exists 0.
ring_simplify.
exact.
destruct H1.
exists (a+b).
split.
unfold lt.
replace (a+b-0) with (a+b) by ring.
by pose proof N2 a b H0 H1.
exists 1.
exists 1.
by ring.
exists (a-b).
split.
unfold lt.
replace (a-b-0) with (a-b) by ring.
unfold sub.
by pose proof N2 a (-b) H0 H1.
exists 1.
exists (-1).
by ring.
destruct H1.
exists (-a).
split.
unfold lt.
replace (-a-0) with (-a) by ring.
exact.
exists (-1).
exists 0.
by ring.
destruct H1.
exists (-a+b).
split.
unfold lt.
replace (-a+b-0) with (-a+b) by ring.
by pose proof N2 (-a) b H0 H1.
exists (-1).
exists 1.
by ring.
exists (-a-b).
split.
unfold lt.
replace (-a-b-0) with (-a-b) by ring.
by pose proof N2 (-a) (-b) H0 H1.
exists (-1).
exists (-1).
by ring.
destruct H0.
unfold Set1 in *.
assert(1|x). {
exists x.
by ring. }
destruct (H x).
pose proof Div_alg a x.
destruct H3.
destruct H0.
exact.
destruct H3.
destruct H3.
destruct H4.
destruct H4.
destruct H0.
destruct H6.
destruct H6.
apply (S1 a (x*x0+x1) (-x*x0)) in H3.
ring_simplify in H3.
rewrite H6 in H3.
ring_simplify in H3.
replace (- a * x2 * x0 + a - b * x3 * x0) with (a*(-x2*x0+1)+b*(-x3*x0)) in H3 by ring.
assert(Set1 x1). {
unfold Set1.
split.
exact.
exists (- x2 * x0 + 1).
exists (- x3 * x0).
exact. }
unfold Set1 in H7.
destruct H7.
destruct (H1 x1).
split.
exact.
exact.
unfold lt in *.
pose proof Z1 (x-x1).
destruct H10.
exact.
replace (x1-x) with (-(x-x1)) in H9 by ring.
contradiction.
apply Z1 in H5.
destruct H5.
rewrite H9 in H5.
replace (x1 - x1) with 0 in H5 by ring.
contradiction (eq_refl 0).
rewrite -H4 in H3.
ring_simplify in H3.
unfold divide.
exists x0.
rewrite M1.
exact.
pose proof Div_alg b x.
destruct H3.
destruct H0.
exact.
destruct H3.
destruct H3.
destruct H4.
destruct H4.
destruct H0.
destruct H6.
destruct H6.
apply (S1 b (x*x0+x1) (-x*x0)) in H3.
ring_simplify in H3.
rewrite H6 in H3.
ring_simplify in H3.
replace (- b * x3 * x0 + b - a * x2 * x0) with (b*(-x3*x0+1)+a*(-x2*x0)) in H3 by ring.
assert(Set1 x1). {
unfold Set1.
split.
exact.
exists (- x2 * x0).
exists (- x3 * x0 + 1).
rewrite A1.
exact. }
unfold Set1 in H7.
destruct H7.
destruct (H1 x1).
split.
exact.
exact.
unfold lt in *.
pose proof Z1 (x-x1).
destruct H10.
exact.
replace (x1-x) with (-(x-x1)) in H9 by ring.
contradiction.
apply Z1 in H5.
destruct H5.
rewrite H9 in H5.
replace (x1 - x1) with 0 in H5 by ring.
contradiction (eq_refl 0).
rewrite -H4 in H3.
ring_simplify in H3.
unfold divide.
exists x0.
rewrite M1.
exact.
pose proof A4P5 x 1.
destruct H4.
destruct H4.
unfold assoc.
split.
unfold divide.
exists x0.
exact.
exact.
destruct H0.
destruct H6.
destruct H6.
rewrite H4 in H6.
exists x1.
exists x2.
exact.
destruct H0.
rewrite H4 in H0.
unfold lt in H0.
replace (-1-0) with (-1) in H0.
assert (N (--1)). {
replace (-(-1)) with 1 by ring.
by pose proof N_one. }
pose proof Z2 (-1) H7.
destruct H8.
contradiction.
by ring.
Qed.


(* Gauss's lemma *)
Theorem A5P5 : ∀ a b c : Z, rel_prime a b → (a | b * c) → (a | c).
Proof.
intros.
pose proof A5P4 a b .
destruct H1.
exact.
firstorder.
apply (S2 (a * x + b * x0) 1 c) in H1.
replace ((a * x + b * x0) * c) with (a*x*c+b*c*x0) in H1 by ring.
rewrite H0 in H1.
unfold divide.
replace (a * x * c + x1 * a * x0) with ((x*c+x1*x0)*a) in H1 by ring.
exists (x * c + x1 * x0).
replace c with (1*c) by ring.
symmetry.
replace (x * (1 * c) + x1 * x0) with (x * c + x1 * x0) by ring.
exact.
Qed.


Theorem A5P6 : ∀ a b c : Z, rel_prime a b → (a | c) → (b | c) → (a * b | c).
Proof.
intros.
pose proof A5P4 a b H.
firstorder.
apply (S2 (a * x + b * x0) 1 c) in H2.
ring_simplify in H2.
rewrite {2}(H0) in H2.
rewrite {1}(H1) in H2.
ring_simplify in H2.
replace (a * x * x2 * b + a * b * x0 * x1) with ((a*b)*(x*x2+x0*x1)) in H2 by ring.
exists (x * x2 + x0 * x1).
by rewrite M1.
Qed.

Theorem A5P7 : ∀ a b c : Z, rel_prime a c → rel_prime b c → rel_prime (a*b) c.
Proof.
intros.
unfold rel_prime.
intros.
pose proof A5P4 a c H.
pose proof A5P4 b c H0.
firstorder.
apply (S2 (b * x + c * x0) 1 1) in H4.
rewrite -{1}(H3) in H4.
ring_simplify in H4.
rewrite {1 2 4}(H2) in H4.
replace (b * x * (x1 * d) * x3 + b * x * a * x2 + x1 * d * c * x0 * x3 + x1 * d * x0 * a * x2)
with (b * x * (x1 * d) * x3 + a*b * x  * x2 + x1 * d * c * x0 * x3 + x1 * d * x0 * a * x2) in H4 by ring.
rewrite H1 in H4.
replace (b * x * (x1 * d) * x3 + x4 * d * x * x2 + x1 * d * c * x0 * x3 + x1 * d * x0 * a * x2) with
(d*(b * x * x1*x3+x4*x*x2+x1*c*x0*x3+x1*x0*a*x2)) in H4 by ring.
exists (b * x * x1 * x3 + x4 * x * x2 + x1 * c * x0 * x3 + x1 * x0 * a * x2).
by rewrite M1.
Qed.

Definition prime (p : Z) := ¬ unit p ∧ ∀ d : Z, (d | p) → unit d ∨ d ~ p.

Theorem A6P1 : ¬ prime 0.
Proof.
unfold prime.
unfold not.
intros.
destruct H.
destruct (H0 2).
exists 0.
by ring.
unfold unit in H1.
firstorder.
pose proof Z4 x.
destruct H2.
rewrite H2 in H1.
ring_simplify in H1.
contradiction A3P1.
exact.
destruct H2.
pose proof Nrange x H2.
destruct H3.
assert(x<2*x). {
unfold lt.
replace (2*x-x) with x by ring.
exact. }
pose proof A2P6 1 x (2*x) H3 H4.
unfold lt in H5.
pose proof Z1 (2*x-1) H5.
destruct H6.
apply (S1 1 (x*2) (-1)) in H1.
ring_simplify in H1.
symmetry in H1.
contradiction.
rewrite -H3 in H1.
apply (S1 1 (1*2) (-1)) in H1.
ring_simplify in H1.
contradiction A3P1.
apply (S2 1 (x*2) (-1)) in H1.
ring_simplify in H1.
replace ( - (2) * x) with (-x*2) in H1 by ring.
pose proof N2 1 1 N_one N_one.
pose proof N3 (-x) 2 H2 H3.
rewrite -H1 in H4.
assert (N (-(-1))). {
replace (-(-1)) with 1 by ring.
by pose proof N_one. }
apply Z1 in H4.
destruct H4.
contradiction.
unfold assoc in H1.
destruct H1.
firstorder.
replace (x*0) with 0 in H2 by ring.
assert (N 2). {
pose proof N_one.
pose proof N2 1 1 H3 H3.
exact. }
apply Z1 in H3.
destruct H3.
contradiction.
Qed.

Theorem greaterRange : ∀a b:Z, a < b -> a + 1 ≤ b.
intros.
unfold le.
assert(∀n:Z,n>0->1≤n).
intros.
pose proof Nrange n.
unfold lt in H0.
replace (n-0) with n in H0 by ring.
apply H1 in H0.
exact.
apply (add_lt_r a b (-a)) in H.
ring_simplify in H.
destruct (H0 (-a+b)).
exact.
apply (add_lt_r 1 (-a+b) a) in H1.
ring_simplify in H1.
by left.
right.
apply (S1 1 (-a+b) a) in H1.
ring_simplify in H1.
exact.
Qed.


Theorem assoc1: ∀ p q d : Z, d~p -> d~q -> p~q.
intros.
apply A4P5 in H.
apply A4P5 in H0.
unfold assoc.
split.
destruct H.
destruct H0.
exists 1.
rewrite -H.
rewrite -H0.
by ring.
exists (-1).
rewrite -H.
apply (S2 d (-q) (-1)) in H0.
ring_simplify in H0.
rewrite -H0.
by ring.
destruct H0.
exists (-1).
apply (S2 d (-p) (-1)) in H.
ring_simplify in H.
rewrite -H.
rewrite -H0.
by ring.
exists 1.
apply (S2 d (-p) (-1)) in H.
apply (S2 d (-q) (-1)) in H0.
ring_simplify in H.
ring_simplify in H0.
rewrite -H.
rewrite -H0.
by ring.
destruct H.
destruct H0.
exists 1.
rewrite -H.
rewrite -H0.
by ring.
exists (-1).
rewrite -H.
apply (S2 d (-q) (-1)) in H0.
ring_simplify in H0.
rewrite -H0.
by ring.
destruct H0.
exists (-1).
apply (S2 d (-p) (-1)) in H.
ring_simplify in H.
rewrite -H.
rewrite -H0.
by ring.
exists 1.
apply (S2 d (-p) (-1)) in H.
apply (S2 d (-q) (-1)) in H0.
ring_simplify in H.
ring_simplify in H0.
rewrite -H.
rewrite -H0.
by ring.
Qed.

Theorem A6P3 : ∀ p q : Z, prime p → prime q → rel_prime p q ∨ p ~ q.
Proof.
intros.
unfold prime in *.
destruct H.
destruct H0.
unfold rel_prime.
intros.
pose proof (classic (p ~ q)).
destruct H3.
right.
exact.
left.
intros.
destruct (H1 d).
exact.
exact.
destruct (H2 d).
exact.
exact.
pose proof assoc1 p q d H6 H7.
contradiction.
Qed.

Theorem A6P4 : ∀ p a : Z, prime p → (p | a) ∨ rel_prime p a.
Proof.
intros.
unfold prime in H.
destruct H.
pose proof (classic (p|a)).
destruct H1.
left.
exact.
right.
unfold rel_prime.
intros.
destruct (H0 d).
exact.
exact.
unfold assoc in H4.
destruct H4.
destruct H5.
destruct H3.
rewrite H5 in H3.
assert(p|a). {
exists (x0*x).
replace (x0 * (x * p)) with (x0 * x * p) in H3 by ring.
exact. }
contradiction.
Qed.

Theorem notA6P5 : ¬ (∀ p : Z, ¬ prime p → ∃ n, 1 < n < p ∧ (n | p)).
Proof.
unfold not.
intros.
pose proof A6P1.
apply H in H0.
destruct H0.
destruct H0.
destruct H0.
assert (0<1).
unfold lt.
replace (1-0) with 1 by ring.
by pose proof N_one.
pose proof A2P6 x 0 1.
apply H4 in H2.
pose proof A2P6 x 1 x.
apply H5 in H2.
unfold lt in H2.
replace (x-x) with 0 in H2 by ring.
apply Z1 in H2.
destruct H2.
assert (0=0).
exact.
contradiction.
exact.
exact.
Qed.

Theorem divideRange: ∀ a b : Z, (a | b) ->b>1->a>0-> a≤b.
intros.
destruct (A2P3 a b).
unfold le.
by left.
destruct H2.
by right.
destruct H.
pose proof A2P3 x 0.
pose proof A2P6.
assert (b>0).
assert (1>0).
unfold lt.
replace (1-0) with 1 by ring.
by pose proof N_one.
firstorder.
destruct H3.
pose proof A3P2 a x H1.
destruct H6.
assert (a*x>0).
rewrite M1.
rewrite -H.
exact.
apply H7 in H8.
apply Z1 in H8.
destruct H8.
unfold lt in H3.
replace (-(x-0)) with (0-x) in H9 by ring.
contradiction.
destruct H3.
rewrite H3 in H.
ring_simplify in H.
apply Z1 in H5.
destruct H5.
replace (b-0) with b in H5 by ring.
contradiction.
apply greaterRange in H3.
ring_simplify in H3.
destruct H3.
apply (A2P4 1 x a) in H3.
ring_simplify in H3.
assert (x*a>b).
rewrite M1.
firstorder.
apply Z1 in H6.
destruct H6.
apply (S1 b (x*a) (-b)) in H.
ring_simplify in H.
replace (-b+x*a) with (x*a-b) in H by ring.
symmetry in H.
contradiction.
exact.
rewrite -H3 in H.
ring_simplify in H.
apply Z1 in H2.
destruct H2.
apply (S1 b a (-b)) in H.
ring_simplify in H.
rewrite A1 in H.
unfold sub in H2.
symmetry in H.
contradiction.
Qed.

Theorem A6P5 : ∀ p : Z, p>1 -> ¬ prime p → ∃ n, 1 < n < p ∧ (n | p).
Proof.
intros.
unfold prime in *.
firstorder.
destruct (classic (unit p)).
apply A3P6 in H1.
destruct H1.
apply Z1 in H.
apply (S1 p 1 (-1)) in H1.
ring_simplify in H1.
destruct H.
contradiction.
pose proof A2P6.
assert (1>-1).
unfold lt.
replace (1--1) with (1+1) by ring.
by pose proof N2 1 1 N_one N_one.
assert (p>-1) by firstorder.
apply Z1 in H4.
destruct H4.
apply (S1 p (-1) 1) in H1.
ring_simplify in H1.
replace (p--1) with (p+1) in H4 by ring.
contradiction.
destruct (classic (∀ d : Z, (d | p) → unit d ∨ d ~ p)).
contradiction H0.
apply not_all_ex_not in H2.
destruct H2.
assert (¬ ((x | p) → unit x ∨ x ~ p)) by exact.
apply not_imply_elim in H2.
apply not_imply_elim2 in H3.
apply not_or_and in H3.
destruct H3.
pose proof  A2P3 x 0.
destruct H5.
exists (-x).
apply (A2P4_neg x 0 (-1)) in H5.
ring_simplify in H5.
split.
split.
apply greaterRange in H5.
ring_simplify in H5.
destruct H5.
exact.
assert (unit x).
exists (-1).
rewrite {1}(H5).
by ring.
contradiction.
pose proof divideRange (-x) p.
assert (-x|p).
destruct H2.
exists (-x0).
rewrite H2.
by ring.
apply H6 in H7.
destruct H7.
exact.
assert (x~p).
unfold assoc.
split.
exists (-1).
rewrite -H7.
by ring.
exists (-1).
rewrite -H7.
by ring.
contradiction.
exact.
exact.
destruct H2.
exists (-x0).
rewrite H2.
by ring.
unfold lt.
replace (0--1) with 1 by ring.
by pose proof N_one.
destruct H5.
destruct H2.
rewrite H5 in H2.
ring_simplify in H2.
assert (p>0).
pose proof A2P6.
assert (1>0).
unfold lt.
replace (1-0) with 1 by ring.
by pose proof N_one.
firstorder.
apply Z1 in H6.
destruct H6.
replace (p-0) with p in H6 by ring.
contradiction.
exists x.
split.
split.
apply greaterRange in H5.
ring_simplify in H5.
destruct H5.
exact.
assert (unit x).
exists (1).
rewrite {1}(H5).
by ring.
contradiction.
pose proof divideRange (x) p.
apply H6 in H2.
destruct H2.
exact.
assert (x~p).
unfold assoc.
split.
exists (1).
rewrite -H2.
by ring.
exists (1).
rewrite -H2.
by ring.
contradiction.
exact.
exact.
exact.
Qed.



Theorem A6P6 : ∀ p x : Z, prime p → 0 < p → 0 < x → (p | x) →
                          ∃ k, k * p = x ∧ 0 < k < x.
Proof.
intros.
destruct H2.
exists x0.
split.
exact.
split.
pose proof A3P2 p x0.
apply H3 in H0.
destruct H0.
rewrite H2 in H1.
replace (x0*p) with (p*x0) in H1 by ring.
apply H4 in H1.
exact.
pose proof Nrange p.
assert(N p). {
unfold lt in H0.
replace (p-0) with p in H0 by ring.
exact. }
apply H3 in H4.
destruct H4.
pose proof Z4 x0.
destruct H5.
rewrite H5 in H2.
replace (0*p) with 0 in H2 by ring.
pose proof Z1 x.
destruct H6.
unfold lt in H1.
replace (x-0) with x in H1 by ring.
exact.
contradiction.
destruct H5.
pose proof (classic (x0<x)).
destruct H6.
exact.
apply A3P3b in H6.
destruct H6.
assert (x0>0). {
unfold lt.
replace (x0-0) with x0 by ring.
exact. }
pose proof A2P4 1 p x0 H4 H7.
replace (1*x0) with x0 in H8 by ring.
pose proof A2P6 x (x0) (p*x0) H6 H8.
apply A3P3a in H9.
unfold le in H9.
assert (¬(p * x0 < x) ∧ ¬(p * x0 = x)) by tauto.
destruct H10.
symmetry in H2.
rewrite M1 in H2.
contradiction.
pose proof A1P10.
rewrite H6 in H2.
destruct (H7 x0 p).
split.
exact.
rewrite H6 in H1.
apply Z1 in H1.
destruct H1.
replace (x0-0) with x0 in H1.
exact.
by ring.
pose proof A2P7 p.
contradiction.
pose proof A3P2 p x0 H0.
destruct H6.
rewrite H2 in H1.
replace (p*x0) with (x0*p) in H7 by ring.
apply H7 in H1.
apply Z1 in H1.
destruct H1.
replace (-x0) with (-(x0-0)) in H5 by ring.
contradiction.
assert (¬(prime 1)). {
intuition.
unfold prime in H5.
destruct H5.
assert(unit 1). {
exists 1.
by ring. }
contradiction. }
rewrite -H4 in H.
contradiction.
Qed.

Theorem notA6P7 : ¬(∀ n : Z, ∃ p : Z, 0 < p ∧ prime p ∧ (p | n)).
unfold not.
intros.
destruct (H 1).
destruct H0.
destruct H1.
unfold prime in H1.
destruct H1.
unfold unit in H1.
contradiction.
Qed.

(*
Corrected A6P7 after strong induction
*)




(* Euclid's lemma *)
Theorem A6P8 : ∀ p a b : Z, prime p → (p | a * b) → (p | a) ∨ (p | b).
intros.
pose proof (classic (p | a)).
destruct H1.
by left.
pose proof (classic (p | b)).
destruct H2.
by right.
pose proof A6P4 p a H.
destruct H3.
contradiction.
pose proof A6P4 p b H.
destruct H4.
contradiction.
pose proof A5P4 p a H3.
pose proof A5P4 p b H4.
destruct H5.
destruct H5.
destruct H6.
destruct H6.
apply (S2 (p * x1 + b * x2) 1 1) in H6.
rewrite -{1}H5 in H6.
ring_simplify in H6.
replace (p * p * x1 * x + p * x1 * a * x0 + p * b * x2 * x + b * x2 * a * x0)
with (p*(p*x1*x+x1*a*x0+b*x2*x)+a*b*x2*x0) in H6 by ring.
assert (rel_prime p (a*b)). {
unfold rel_prime.
intros.
destruct H7.
destruct H8.
rewrite {1}H7 in H6.
rewrite H8 in H6.
replace (x3 * d * (p * x1 * x + x1 * a * x0 + b * x2 * x) + x4 * d * x2 * x0)
with (d*(x3 * (p * x1 * x + x1 * a * x0 + b * x2 * x) + x4 * x2 * x0)) in H6 by ring.
exists (x3 * (p * x1 * x + x1 * a * x0 + b * x2 * x) + x4 * x2 * x0).
by rewrite M1. }
unfold rel_prime in H7.
unfold prime in H.
destruct H.
destruct (H7 p).
exists 1.
by ring.
destruct H0.
exists x3.
exact.
assert(unit p). {
exists x3.
exact. }
contradiction.
Qed.


Fixpoint product (L : list Z) :=
  match L with
  | nil => 1
  | p :: L => p * product L
  end.

Notation "∏ L" := (product L) (at level 50).

Fixpoint length (L : list Z) :=
  match L with
  | nil => 0
  | p :: L => length L + 1
  end.

Infix "∈" := List.In (at level 70).

Theorem A7P1 : ∀ a, a < a + 1.
Proof.
intros.
unfold lt.
replace (a+1-a) with (1) by ring.
by pose proof N_one.
Qed.

Theorem length_nonneg : ∀ L, 0 ≤ length L.
Proof.
  induction L; simpl; first by right.
  case IHL => [H | ->]; left; eauto using A2P6, A7P1.
Qed.

Theorem length_zero : ∀ L, length L = 0 ↔ L = nil.
Proof.
  split; intros H; subst; auto.
  induction L; auto.
  assert (0 < length (a :: L)) as H0; simpl.
  { destruct (length_nonneg L); [ | rewrite -H0]; firstorder using A2P6, A7P1. }
  rewrite H in H0.
  contradiction (A2P7 0).
Qed.

Theorem length_one : ∀ L, length L = 1 ↔ ∃ a, L = a :: nil.
Proof.
  split => [ | [a ->]] /=; auto using A1P1.
  case L => /= [/A3P1 | ] // z {}L.
  exists z.
  apply f_equal, length_zero.
  rewrite -(A4 1) -{1}H.
  ring.
Qed.

Theorem length_n : ∀ n L,
    0 < n → length L = n → ∃ a L', L = a :: L' ∧ length L = length L' + 1.
Proof.
  intros n L H H0.
  destruct L; simpl in *; subst.
  - contradiction (A2P7 0).
  - by exists z, L.
Qed.

(* Induction*)
Theorem Induction :  ∀ P : Z → Prop,
   P 1 → (∀ n, P n → P (n + 1)) → ∀ n, 0 < n → P n.
Proof.
intros.
set (S := λ k, k>0∧¬P(k)).
pose proof A3P7 S.
pose proof (classic (∃ x : Z, S x)).
destruct H3.
destruct H2.
firstorder.
exact.
destruct H2.
destruct H3.
assert (¬(S (x-1))).
pose proof (classic (S (x-1))).
destruct H5.
destruct (H4 (x-1)).
exact.
unfold lt in H6.
replace (x-1-x) with (-1) in H6 by ring.
pose proof N_one.
apply Z1 in H7.
destruct H7.
contradiction.
apply (S1 x (x-1) (-x+1)) in H6.
ring_simplify in H6.
pose proof A3P1.
symmetry in H6.
contradiction.
exact.
unfold S in H2.
destruct H2.
pose proof Nrange x.
destruct H7.
unfold lt in H2.
replace (x-0) with x in H2 by ring.
exact.
apply (add_lt_r 1 x (-1)) in H7.
ring_simplify in H7.
pose proof (classic (P (x-1))).
destruct H8.
apply H0 in H8.
replace (x-1+1) with x in H8 by ring.
contradiction.
unfold S in H5.

destruct H5.
exact.
rewrite -H7 in H6.
contradiction.
unfold S in H3.
assert (forall x : Z, 0 < x ∧ P x ∨  ¬(0 < x) ∧ ¬ P x∨ ¬(0 < x) ∧ P x).
intuition.
pose proof (classic (0<x)).
pose proof (classic (P x)).
destruct H4.
destruct H5.
left.
exact.
destruct H3.
exists x.
exact.
destruct H5.
right.
right.
exact.
right.
left.
exact.
destruct (H4 n).
destruct H5.
exact.
destruct H5.
destruct H5.
contradiction.
destruct H5.
contradiction.
Qed.


Theorem induction_with_lt : ∀ P : Z → Prop,
P 1 → (∀ n : Z, 0 < n → P n → P (n + 1)) → ∀ z : Z, 0 < z → P z.
Proof.
intros.
set (S := λ k, k>0∧¬P(k)).
pose proof A3P7 S.
pose proof (classic (∃ x : Z, S x)).
destruct H3.
destruct H2.
firstorder.
exact.
destruct H2.
destruct H3.
assert (¬(S (x-1))).
pose proof (classic (S (x-1))).
destruct H5.
destruct (H4 (x-1)).
exact.
unfold lt in H6.
replace (x-1-x) with (-1) in H6 by ring.
pose proof N_one.
apply Z1 in H7.
destruct H7.
contradiction.
apply (S1 x (x-1) (-x+1)) in H6.
ring_simplify in H6.
pose proof A3P1.
symmetry in H6.
contradiction.
exact.
unfold S in H2.
destruct H2.
pose proof Nrange x.
destruct H7.
unfold lt in H2.
replace (x-0) with x in H2 by ring.
exact.
apply (add_lt_r 1 x (-1)) in H7.
ring_simplify in H7.
pose proof (classic (P (x-1))).
destruct H8.
apply H0 in H8.
replace (x-1+1) with x in H8 by ring.
contradiction.
unfold S in H5.
exact.
destruct H5.
exact.
rewrite -H7 in H6.
contradiction.
unfold S in H3.
assert (forall x : Z, 0 < x ∧ P x ∨  ¬(0 < x) ∧ ¬ P x∨ ¬(0 < x) ∧ P x).
intuition.
pose proof (classic (0<x)).
pose proof (classic (P x)).
destruct H4.
destruct H5.
left.
exact.
destruct H3.
exists x.
exact.
destruct H5.
right.
right.
exact.
right.
left.
exact.
firstorder.
Qed.


(* Strong induction *)
Theorem A7P2 : ∀ P : Z → Prop,
    (∀ n, (∀ k, 0 < k < n → P k) → P n) → ∀ n : Z, P n.
Proof.
intros.
set (S := λ k, k>0∧¬P(k)).
pose proof A3P7 S.
pose proof (classic (∃ x : Z, S x)).
destruct H1.
destruct H0.
firstorder.
exact.
destruct H0.
assert (∀ k : Z, 0 < k < x → ¬(S k)).
intros.
pose proof (classic (S k)).
destruct H4.
apply H2 in H4.
destruct H3.
pose proof A3P3a k x.
destruct H6.
apply H6 in H5.
contradiction.
exact.
assert (∀ k : Z, k>0 ∧ ¬ S k -> P k).
intros.
unfold S in H4.
destruct H4.
rename H5 into H9.
assert (0 < k ∧ P k∨¬ 0 < k ∧ P k ∨ ¬0 < k ∧ ¬P k).
pose proof (classic (0<k)).
pose proof (classic (P k)).
destruct H5.
destruct H6.
by left.
destruct H9.
exact.
destruct H6.
right.
by left.
right.
by right.
destruct H5.
by destruct H5.
destruct H5.
by destruct H5.
destruct H5.
contradiction.
firstorder.
unfold S in H1.
assert (forall x : Z, 0 < x ∧ P x ∨  ¬(0 < x) ∧ ¬ P x∨ ¬(0 < x) ∧ P x).
intuition.
pose proof (classic (0<x)).
pose proof (classic (P x)).
destruct H2.
destruct H3.
left.
exact.
destruct H1.
exists x.
exact.
destruct H3.
right.
right.
exact.
right.
left.
exact.
destruct (H2 n).
destruct H3.
exact.
destruct H3.
destruct H3.
firstorder.
destruct H3.
exact.
Qed.
Theorem A6P2 : prime 2.
Proof.
unfold prime.
unfold not.
split.
intros.
firstorder.
pose proof Z4 x.
rename H into H1.
rename H0 into H2.
pose proof A1P1.
pose proof A1P1.
destruct H2.
rewrite H2 in H1.
ring_simplify in H1.
contradiction A3P1.
exact.
destruct H2.
pose proof Nrange x H2.
destruct H3.
assert(x<2*x). {
unfold lt.
replace (2*x-x) with x by ring.
exact. }
pose proof A2P6 1 x (2*x) H3 H4.
unfold lt in H5.
pose proof Z1 (2*x-1) H5.
destruct H6.
apply (S1 1 (x*2) (-1)) in H1.
ring_simplify in H1.
symmetry in H1.
contradiction.
rewrite -H3 in H1.
apply (S1 1 (1*2) (-1)) in H1.
ring_simplify in H1.
contradiction A3P1.
apply (S2 1 (x*2) (-1)) in H1.
ring_simplify in H1.
replace ( - (2) * x) with (-x*2) in H1 by ring.
pose proof N2 1 1 N_one N_one.
pose proof N3 (-x) 2 H2 H3.
rewrite -H1 in H4.
assert (N (-(-1))). {
replace (-(-1)) with 1 by ring.
by pose proof N_one. }
apply Z1 in H4.
destruct H4.
contradiction.
intros.
pose proof A4P6 d 2 H as H10.
assert (2 ≠ 0) as H11.
assert (N 2).
by pose proof N2 1 1 N_one N_one.
apply Z1 in H0.
destruct H0.
exact.
apply H10 in H11.
destruct H.
pose proof abs_pm 2 as H12.
pose proof (classic (unit d)).
pose proof (classic (d ~ 2)).
destruct H0.
left.
exact.
destruct H1.
right.
exact.
pose proof A2P3 d 0.
pose proof A2P3 x 0.
destruct H2.
apply greaterRange in H2.
destruct H2.
apply (add_lt_r (d+1) 0 (-1)) in H2.
ring_simplify in H2.
apply greaterRange in H2.
destruct H2.
apply (add_lt_r (d+1) (-1) (-1)) in H2.
ring_simplify in H2.
destruct H3.
pose proof A2P4_neg d (-(2)) x H2 H3.
apply greaterRange in H3.
destruct H3.
apply (add_lt_r (x+1) 0 (-1)) in H3.
ring_simplify in H3.
assert((-(2))<0).
unfold lt.
replace (0--(2)) with (2) by ring.
by pose proof N2 1 1  N_one N_one.
pose proof A2P4_neg x (-1) (-(2)) H3 H5.
ring_simplify in H6.
pose proof A2P6.
assert (2<d*x).
firstorder.
apply Z1 in H8.
destruct H8.
apply (S1 2 (x*d) (-(2))) in H.
ring_simplify in H.
rewrite M1 in H.
symmetry in H.
contradiction.
apply (S1 (x+1) 0 (-1)) in H3.
ring_simplify in H3.
rewrite H3 in H4.
ring_simplify in H4.
rewrite H3 in H.
ring_simplify in H.
apply Z1 in H4.
destruct H4.
apply (S1 2 (-d) (-(2))) in H.
ring_simplify in H.
symmetry in H.
contradiction.
destruct H3.
rewrite H3 in H.
ring_simplify in H.
pose proof N2 1 1 N_one N_one.
apply Z1 in H4.
destruct H4.
contradiction.
assert (N (-d)).
assert (d<0).
assert ((-(2)<0)).
unfold lt.
replace (0 - - (2)) with 2 by ring.
by pose proof N2 1 1 N_one N_one.
pose proof A2P6.
firstorder.
unfold lt in H4.
replace (0-d) with (-d) in H4 by ring.
exact.
unfold lt in H3.
replace (x-0) with x in H3 by ring.
pose proof N3 x (-d) H3 H4.
assert (N (x*d)).
rewrite -H.
by pose proof N2 1 1 N_one N_one.
replace (x*-d) with (-(x*d)) in H5 by ring.
apply Z1 in H5.
destruct H5.
replace (x*d) with (--(x*d)) in H6 by ring.
contradiction.
apply (S1 (d+1) (-1) (-1)) in H2.
ring_simplify in H2.
right.
unfold assoc.
split.
exists (-1).
rewrite H2.
by ring.
exists (-1).
rewrite H2.
by ring.
apply (S1 (d+1) 0 (-1)) in H2.
ring_simplify in H2.
left.
unfold unit.
exists (-1).
rewrite H2.
by ring.
destruct H2.
rewrite H2 in H.
ring_simplify in H.
assert (N 2).
by pose proof N2 1 1 N_one N_one.
apply Z1 in H4.
destruct H4.
contradiction.
destruct H12.
rewrite H4 in H11.
destruct H11.
apply greaterRange in H2.
ring_simplify in H2.
destruct H2.
apply greaterRange in H2.
destruct H2.
unfold lt in *.
apply Z1 in H2.
destruct H2.
replace (2-d) with (-(d-2)) in H5 by ring.
contradiction.
unfold lt in H5.
apply Z1 in H5.
destruct H5.
apply (S1 2 d (-d)) in H2.
ring_simplify in H2.
replace (-d+2) with (2-d) in H2 by ring.
contradiction.
left.
exists 1.
rewrite -H2.
by ring.
right.
unfold assoc.
split.
exists 1.
rewrite H5.
by ring.
exists 1.
rewrite H5.
by ring.
rewrite H4 in H11.
destruct H11.
unfold lt in H2.
replace (d-0) with (--d) in H2 by ring.
assert (d<0).
pose proof A2P6.
assert ((-(2))<0).
unfold lt.
replace (0--(2)) with 2 by ring.
by pose proof N2 1 1 N_one N_one.
firstorder.
unfold lt in H6.
replace (0-d) with (-d) in H6 by ring.
apply Z1 in H6.
destruct H6.
contradiction.
right.
split.
exists (-1).
rewrite H5.
by ring.
exists (-1).
rewrite H5.
by ring.
Qed.


Theorem A6P7pos : ∀ n : Z, n>1 -> ∃ p : Z, 0 < p ∧ prime p ∧ (p | n).
intros.
induction n using A7P2.
destruct (classic (prime n)).
exists n.
pose proof A2P6.
assert (1>0).
unfold lt.
replace (1-0) with 1 by ring.
by pose proof N_one.
split.
firstorder.
split.
exact.
exists 1.
by ring.
apply A6P5 in H1.
destruct H1.
destruct (H0 x).
destruct H1.
destruct H1.
split.
pose proof A2P6.
assert (1>0).
unfold lt.
replace (1-0) with 1 by ring.
by pose proof N_one.
firstorder.
exact.
destruct H1.
destruct H1.
exact.
exists x0.
destruct H2.
split.
exact.
split.
destruct H3.
exact.
destruct H3.
destruct H1.
destruct H5.
destruct H4.
exists (x2*x1).
replace (x2*x1*x0) with (x1*(x2*x0)) by ring.
rewrite -H4.
rewrite H5.
exact.
exact.
Qed.

Theorem A6P7 : ∀ n : Z,  n=0∨n>1∨n<(-1) -> ∃ p : Z,0 < p ∧ prime p ∧ (p | n).
intros.
destruct H.
exists 2.
split.
unfold lt.
replace (2-0) with 2 by ring.
pose proof N2 1 1 N_one N_one.
exact.
split.
pose proof A6P2.
exact.
exists 0.
rewrite H.
by ring.
destruct H.
pose proof A6P7pos n.
destruct H0.
unfold lt.
replace (n-0) with n by ring.
exact.
exists x.
exact.
pose proof A6P7pos (-n).
destruct H0.
unfold lt.
replace (-n-0) with (-n) by ring.
unfold lt in *.
replace (-n-1) with (-1-n) by ring.
exact.
exists x.
destruct H0.
destruct H1.
split.
exact.
split.
exact.
destruct H2.
unfold divide.
exists (-x0).
apply (S2 (-n) (x0*x) (-1)) in H2.
ring_simplify in H2.
exact.
Qed.

Theorem A7P3 : ∀ a b c, b < c → a + b < a + c.
Proof.
intros.
apply (add_lt_r b c a) in H.
rewrite A1 in H.
replace (c+a) with (a+c) in H by ring.
exact.
Qed.

Theorem power_construction : ∀ a n,
    0 ≤ n → exists ! L, length L = n ∧ ∀ x, x ∈ L → x = a.
Proof.
  move=> a n [H | H].
  - induction n using A7P2.
    case (A2P3 n 1) => [? | [-> | /(A7P3 (-1))]]; first firstorder using A3P4.
    + exists (a :: nil).
      (repeat split; simpl; try by intuition (ring || congruence)) =>
      x' [/length_one [z ->] H1].
      f_equal; firstorder.
    + rewrite (A1 (-1) 1) A4 A1 => H1.
      destruct (H0 (n-1)) as [L' [[H2 H3] H4]]; repeat split; auto.
      * pose proof (A7P1 (n-1)) as H2.
          by rewrite ?/sub ?/subZ -A2 (A1 (-1)) A4 A3 in H2.
      * exists (a :: L').
        repeat split; simpl; firstorder; first by ring [H2]; subst.
        eapply length_n in H as [z [L [H]]]; eauto; subst.
        f_equal; simpl in *; firstorder.
        apply H4; firstorder; ring.
  - (exists nil; subst; split; try by firstorder) => x' [H H0].
      by apply length_zero in H.
Qed.

Definition pow : Z → Z → Z.
Proof.
  intros a n.
  destruct (excluded_middle_informative (0 ≤ n)) as [H | H].
  - destruct (constructive_definite_description
                _ (power_construction a n H)) as [L [H0 H1]].
    exact (∏ L).
  - exact 1.
Defined.

Infix "^" := pow.

Theorem pow_1_r : ∀ a, a^1 = a.
  rewrite /pow => a.
  case excluded_middle_informative => [H | []].
  - elim constructive_definite_description => [L [/length_one [z ->]]] /= H1.
    ring_simplify.
    intuition.
  - rewrite -(A1P1 1).
    firstorder using A7P1.
Qed.

Theorem pow_0_r : ∀ a, a^0 = 1.
Proof.
  rewrite /pow => a.
  case excluded_middle_informative => [H | H]; auto.
  elim constructive_definite_description => [L [/length_zero -> /(_ a) /=]] //.
Qed.

Theorem pow_spec : ∀ a L, (∀ x, x ∈ L → x = a) → a^(length L) = ∏ L.
Proof.
  rewrite /pow => a L H.
  case excluded_middle_informative => [H0 | H0]; firstorder using length_nonneg.
  elim constructive_definite_description => [L' [H1 H2]].
  f_equal.
  eapply power_construction in H0 as [L'' [H0 H3]].
  have <-: L'' = L; try have <-: L'' = L'; eauto.
Qed.

Theorem pow_pos_r : ∀ a n, 0 < n → a^n = a * a^(n-1).
Proof.
  rewrite {1}/pow => a n H.
  case excluded_middle_informative => [H0 | H0]; firstorder.
  elim constructive_definite_description => [L [H1 H2]]; subst.
  elim (length_n (length L) L) => // [z [L' []]] /= *; subst.
  rewrite ?/sub ?/subZ -A2 A4 A3 pow_spec; try have ->: z = a; firstorder.
Qed.

Theorem pow_neg_l : ∀ a n, n < 0 → a^n = 1.
Proof.
  rewrite /pow => a n /[dup] H /A3P3a H0.
  destruct excluded_middle_informative; intuition.
Qed.

Theorem pow_1_l : ∀ n, 1^n = 1.
Proof.
  intros n.
  destruct (classic (0 ≤ n)) as [H | H].
  - apply (power_construction 1) in H as [L [[<- H0] _]].
    rewrite pow_spec; auto.
    induction L; simpl; auto.
    rewrite (H0 a) ? IHL ? M3 //; firstorder.
  - rewrite pow_neg_l //.
      by apply A3P3a.
Qed.

Theorem pow_0_l : ∀ n, 0 < n → 0^n = 0.
Proof.
  move=> n /pow_pos_r ->.
  ring.
Qed.

Theorem A7P4 : ∀ a b c, 0 ≤ b → 0 ≤ c → a^(b+c) = a^b * a^c.
Proof.
intros.
destruct H.
destruct H0.
unfold lt in *.
replace (b-0) with b in H by ring.
replace (c-0) with c in H0 by ring.
assert(b>0).
unfold lt.
replace (b-0) with b by ring.
exact.
elim/induction_with_lt: H1.
pose proof pow_pos_r a (1+c).
assert (0<1+c).
unfold lt.
replace (1+c-0) with (1+c) by ring.
by pose proof N2 1 c N_one H0.
apply H1 in H2.
pose proof pow_1_r a.
intros.
rewrite -{2}(H3) in H2.
replace (1+c-1) with c in H2 by ring.
exact.
intros.
apply (S2 (a ^ (n + c)) (a ^ n * a ^ c) a) in H2.
pose proof pow_pos_r a (n+c+1).
unfold lt in H1.
replace (n-0) with n in H1 by ring.
assert(n+c+1>0).
unfold lt.
replace (n+c+1-0) with (n+c+1) by ring.
assert (N (n+c)).
by pose proof N2 n c H1 H0.
by pose proof N2 (n+c) 1 H4 N_one.
apply H3 in H4.
replace (n+c+1-1) with (n+c) in H4 by ring.
rewrite M1 in H4.
rewrite -H4 in H2.
pose proof pow_pos_r a (n+1).
assert (0<n+1).
unfold lt.
replace (n+1-0) with (n+1) by ring.
by pose proof N2 n 1 H1 N_one.
apply H5 in H6.
replace (n+1-1) with n in H6 by ring.
replace (a ^ n * a ^ c * a) with (a*a ^ n * a ^ c) in H2 by ring.
rewrite -H6 in H2.
replace ((n + c + 1)) with ((n + 1 + c)) in H2 by ring.
exact.
rewrite -H0.
replace (b+0) with b by ring.
pose proof pow_0_r a.
rewrite H1.
by ring.
rewrite -H.
pose proof pow_0_r a.
rewrite H1.
replace (0+c) with c by ring.
by ring.
Qed.


Theorem A7P5 : ∀ a b c, 0 ≤ c → (a*b)^c = a^c * b^c.
Proof.
intros.
destruct H.
elim/induction_with_lt: H.
pose proof pow_1_r (a*b).
pose proof pow_1_r (a).
pose proof pow_1_r (b).
rewrite H.
rewrite H1.
rewrite H0.
by ring.
intros.
apply (S2 ((a * b) ^ n) (a ^ n * b ^ n) (a*b)) in H0.
pose proof pow_pos_r (a*b) (n+1).
unfold lt in H.
replace (n-0) with n in H by ring.
assert(0<n+1).
unfold lt.
replace (n+1-0) with (n+1) by ring.
by pose proof N2 n 1 H N_one.
apply H1 in H2.
replace (n+1-1) with n in H2 by ring.
replace (a * b * (a * b) ^ n) with ((a * b) ^ n * (a * b)) in H2 by ring.
rewrite -H2 in H0.
pose proof pow_pos_r (a) (n+1).
unfold lt in H.
replace (n-0) with n in H by ring.
assert(0<n+1).
unfold lt.
replace (n+1-0) with (n+1) by ring.
by pose proof N2 n 1 H N_one.
apply H3 in H4.
replace (n+1-1) with n in H4 by ring.
replace (a ^ n * b ^ n * (a * b)) with (a*a ^ n * (b*b ^ n)) in H0 by ring.
rewrite -H4 in H0.
pose proof pow_pos_r (b) (n+1).
unfold lt in H.
replace (n-0) with n in H by ring.
assert(0<n+1).
unfold lt.
replace (n+1-0) with (n+1) by ring.
by pose proof N2 n 1 H N_one.
apply H5 in H6.
replace (n+1-1) with n in H5 by ring.
rewrite -H5 in H0.
unfold lt.
replace (n+1-0) with (n+1) by ring.
by pose proof N2 n 1 H N_one.
exact.
rewrite -H.
pose proof pow_0_r (a*b).
pose proof pow_0_r (a).
pose proof pow_0_r (b).
rewrite H0.
rewrite H1.
rewrite H2.
by ring.
Qed.

Theorem A7P6 : ∀ a b c, 0 ≤ b → 0 ≤ c → a^(b*c) = (a^b)^c.
Proof.
intros.
destruct H.
destruct H0.
elim/induction_with_lt: H.
replace (1*c) with c by ring.
pose proof pow_1_r a.
rewrite H.
exact.
intros.
elim/induction_with_lt: H0.
replace ((n+1)*1) with (n+1) by ring.
pose proof pow_1_r (a ^ (n + 1)).
rewrite H0.
exact.
intros.
apply (S2 (a ^ ((n + 1) * n0))  ((a ^ (n + 1)) ^ n0) (a ^ (n + 1))) in H2.
pose proof A7P4 a ((n + 1) * n0) (n + 1).
unfold lt in H0.
replace (n0-0) with n0 in H0 by ring.
unfold lt in H.
replace (n-0) with n in H by ring.
assert (n+1>0).
unfold lt.
replace (n+1-0) with (n+1) by ring.
by pose proof N2 n 1 H N_one.
assert (0 ≤ (n + 1) * n0).
unfold le.
left.
unfold lt in H4.
replace (n+1-0) with (n+1) in H4 by ring.
unfold lt.
replace ((n + 1) * n0 - 0) with ((n + 1) * n0) by ring.
by pose proof N3 (n+1) n0 H4 H0.
assert (0 ≤ n + 1).
unfold le.
left.
unfold lt.
replace (n+1-0) with (n+1) by ring.
by pose proof N2 n 1 H N_one.
apply H3 in H5.
replace ((n + 1) * n0 + (n + 1)) with ((n + 1) * (n0 + 1)) in H5 by ring.
rewrite -H5 in H2.
pose proof pow_pos_r (a ^ (n + 1)) (n0+1).
assert (0<n0+1).
unfold lt.
replace (n0+1-0) with (n0+1) by ring.
by pose proof N2 n0 1 H0 N_one.
apply H7 in H8.
replace (n0+1-1) with n0 in H8 by ring.
rewrite M1 in H8.
rewrite -H8 in H2.
exact.
exact.
rewrite -H0.
replace (b*0) with 0 by ring.
pose proof pow_0_r a.
pose proof pow_0_r (a^b).
rewrite H1.
rewrite H2.
exact.
rewrite -H.
replace (0*c) with 0 by ring.
pose proof pow_0_r a.
rewrite H1.
pose proof pow_1_l c.
rewrite H2.
exact.
Qed.



Theorem A7P7 : ∀ p L, prime p → (p | ∏ L) → ∃ x, x ∈ L ∧ (p | x).
Proof.
intros.
induction L.
simpl in H0.
assert(unit p).
firstorder.
firstorder.
simpl in H0.
pose proof A6P8 p a (∏ L) H H0.
destruct H1.
exists a.
firstorder.
apply IHL in H1.
firstorder.
Qed.

Definition prime_factorization n L :=
  n = ∏ L ∧ (∀ p, p ∈ L → 0 < p ∧ prime p).

Notation "n = ∏' L" := (prime_factorization n L) (at level 50).

Lemma prime_facts_are_facts : ∀ n L, n = ∏' L → n = ∏ L.
Proof.
  intros n L H.
  destruct H.
  exact H.
Qed.

Lemma prod_app : ∀ L L' : list Z, (∏ L) * (∏ L') = ∏ (L ++ L').
Proof.
  induction L; simpl; intros L'; rewrite -? IHL; ring.
Qed.

Lemma prod_cons_app :
  ∀ (L L' : list Z) (p : Z), ∏ (L ++ p :: L') = p * (∏ (L ++ L')).
Proof.
  induction L; auto => L' p /=.
  rewrite IHL; ring.
Qed.

Lemma length_app : ∀ L L' : list Z, length L + length L' = length (L ++ L').
Proof.
  induction L; simpl; intros L'; rewrite -? IHL; ring.
Qed.

Lemma length_cons_app :
  ∀ (L L' : list Z) (p : Z), length (L ++ p :: L') = 1 + length (L ++ L').
Proof.
  induction L; auto; intros L' p; simpl; rewrite ? IHL; ring.
Qed.

Lemma perm_prod : ∀ L1 L2 : list Z, Permutation L1 L2 → ∏ L1 = ∏ L2.
Proof.
  intros L1 L2 H.
  induction H; simpl; (ring || congruence).
Qed.

Lemma perm_prime_fact : ∀ (n : Z) (L1 L2 : list Z),
    Permutation L1 L2 → n = ∏' L1 → n = ∏' L2.
Proof.
  intros n L1 L2 H [H0 H1].
  split; eauto using eq_trans, perm_prod, Permutation_in, Permutation_sym.
Qed.

Add Morphism product with signature (@Permutation Z) ==> eq as perm_prod_morph.
Proof.
  exact perm_prod.
Qed.

Add Morphism prime_factorization with signature
    eq ==> (@Permutation Z) ==> iff as perm_prime_fact_morph.
Proof.
  split; eauto using perm_prime_fact, Permutation_sym.
Qed.

Theorem A8P1 : ∀ p n m, prime p → (p | n^m) → (p | n).
Proof.
intros.
pose proof A2P3 m 0.
destruct H1.
pose proof pow_neg_l n m H1.
rewrite H2 in H0.
pose proof A3P6 p.
destruct H3.
destruct H3.
firstorder.
exists n.
firstorder.
exists (-n).
firstorder.
destruct H1.
pose proof pow_0_r n.
rewrite H1 in H0.
rewrite H2 in H0.
pose proof A3P6 p.
firstorder.
pose proof power_construction n m.
pose proof pow_spec n.
assert (0 ≤ m).
unfold le.
by left.
apply H2 in H4.
destruct H4.
pose proof A7P7 p x H.
assert ((p | ∏ x)).
destruct (H3 x).
firstorder.
assert (length x = m) by firstorder.
rewrite H6.
exact.
apply H5 in H6.
destruct H6.
destruct H6.
assert(x0=n) by firstorder.
by rewrite -H8.
Qed.


Theorem A8P2 : ∀ n, 0 < n → ∃ L : list Z, n = ∏' L.
Proof.
intros.
induction n using A7P2.
pose proof (classic (prime n)).
destruct H1.
exists (n :: nil).
unfold prime_factorization.
split.
simpl.
by ring.
intros.
simpl in H2.
destruct H2.
rewrite -H2.
exact.
exact.
pose proof A6P5 n.
assert (N n).
unfold lt in H.
by replace (n-0) with n in H by ring. 
pose proof Nrange n H3.
destruct H4.
apply H2 in H4.
destruct H4.
destruct H4.
destruct H5.
assert(x0>0).
pose proof A3P2 x x0.
destruct H6.
assert(1>0).
unfold lt.
replace (1-0) with 1 by ring.
by pose proof N_one.
pose proof A2P6.
firstorder.
assert (x*x0>0).
unfold lt.
replace (x*x0-0) with (x*x0) by ring.
rewrite H5 in H3.
by rewrite M1.
by apply H7 in H8.
assert(n>x0).
unfold lt.
assert (n=x0*x) as H82.
exact.
apply (S1 n (x0*x) (-x0*x)) in H5.
ring_simplify in H5.
destruct H4.
pose proof A2P4 1 x x0 H4 H6.
rewrite M1 in H82.
rewrite -H82 in H8.
ring_simplify in H8.
by unfold lt in H8.
destruct (H0 x).
assert(1>0).
unfold lt.
replace (1-0) with 1 by ring.
by pose proof N_one.
pose proof A2P6.
firstorder.
assert(1>0).
unfold lt.
replace (1-0) with 1 by ring.
by pose proof N_one.
pose proof A2P6.
firstorder.
destruct (H0 x0).
assert(1>0).
unfold lt.
replace (1-0) with 1 by ring.
by pose proof N_one.
pose proof A2P6.
firstorder.
assert(1>0).
unfold lt.
replace (1-0) with 1 by ring.
by pose proof N_one.
pose proof A2P6.
firstorder.
unfold prime_factorization in *.
destruct H8.
destruct H9.
exists (x2 ++ x1).
split.
rewrite H8 in H5.
rewrite H9 in H5.
rewrite prod_app in H5.
exact.
intros p H12.
rewrite -> in_app_iff in H12.
destruct H12.
apply H11 in H12.
exact.
apply H10 in H12.
exact.
exact.
unfold prime_factorization.
exists nil.
split.
firstorder.
firstorder.
Qed.

Theorem A8P3 : ∀ n L, n = ∏' L → 0 < n.
Proof.
intros.
firstorder.
induction L.
assert(1 = ∏nil).
auto.
rewrite -H1 in H.
rewrite H.
pose proof N_one.
unfold lt.
by replace (1-0) with 1 by ring.
simpl in *.
destruct (H0 a).
firstorder.
assert (∀ L, (∀ p : Z, p ∈ L → 0 < p ∧ prime p)-> ∏ L>0).
intros.
induction L0.
assert(1 = ∏nil).
auto.
rewrite -H4.
unfold lt.
replace (1-0) with 1 by ring.
by pose proof N_one.
assert ((∀ p : Z, p ∈ L0 → 0 < p ∧ prime p)).
simpl in H3.
intros.
destruct (H3 p).
by right.
exact.
apply IHL0 in H4.
simpl in *.
destruct (H3 a0).
by left.
unfold lt in *.
replace (∏ L0 - 0) with (∏ L0) in H4 by ring.
replace (a0-0) with a0 in H5 by ring.
replace (a0*(∏ L0) -0) with (a0*(∏ L0)) by ring.
by pose proof N3 a0 (∏ L0) H5 H4.
assert(0 < ∏ L).
firstorder.
unfold lt in H1.
replace (a-0) with a in H1 by ring.
unfold lt in H4.
replace (∏ L - 0) with (∏ L) in H4 by ring.
pose proof N3 a (∏ L) H1 H4.
rewrite -H in H5.
unfold lt.
replace (n-0) with n by ring.
exact.
Qed.


Theorem primeRange : ∀ p : Z, 0 < p -> prime p -> p>1.
intros.
unfold lt in H.
replace (p-0) with p in H by ring.
pose proof Nrange p H.
destruct H1.
exact.
rewrite -H1 in H0.
unfold prime in H0.
destruct H0.
assert (unit 1).
exists 1.
by ring.
contradiction.
Qed.


Theorem A8P4 : ∀ L, 1 = ∏' L ↔ L = nil.
Proof.
split.
intros.
assert(1 = ∏nil).
exact. 
firstorder.
pose proof (classic (L=nil)).
destruct H2.
exact.
assert(∀ p : Z, p ∈ L → p>1).
intros.
destruct (H1 p).
exact.
pose proof primeRange p H4 H5.
exact.
assert (∏ L>1).
induction L.
firstorder.
destruct (H1 a).
firstorder.
simpl in H.
assert (unit a).
exists (∏ L).
rewrite M1. 
exact.
unfold prime in H5.
destruct H5.
contradiction.
apply (S1 1 (∏ L) (-1)) in H.
apply (add_lt_r 1 (∏ L) (-1)) in H4.
ring_simplify in H.
ring_simplify in H4.
apply Z1 in H4.
destruct H4.
replace (∏ L - 1 - 0) with (∏ L - 1 ) in H4 by ring.
symmetry in H.
contradiction.
intros.
rewrite H.
firstorder.
Qed.

Theorem A8P5 : ∀ p n L, 0 < p → n = ∏' L → prime p → (p | n) → p ∈ L.
Proof.
intros.
unfold prime_factorization in H0.
destruct H0.
rewrite H0 in H2.
pose proof A7P7 p L H1 H2.
destruct H4.
destruct H4.
destruct (H3 x).
exact.
unfold prime in H7.
destruct H7.
destruct (H8 p).
exact.
unfold prime in H1.
destruct H1.
contradiction.
apply A4P5 in H9.
destruct H9.
rewrite -H9 in H4.
exact.
rewrite H9 in H.
assert (N x).
unfold lt in H6.
replace (x-0) with x in H6 by ring.
exact.
assert (N (-x)).
unfold lt in H.
replace (-x-0) with (-x) in H by ring.
exact.
apply Z2 in H11.
destruct H11.
contradiction.
Qed.


Theorem A8P6 : ∀ n p L, n * p = ∏' (p :: L) → n = ∏' L.
Proof.
intros.
destruct H.
simpl in H.
firstorder.
assert (p>0).
destruct (H0 p).
firstorder.
exact.
apply (S1 ( n * p) (p * (∏ L)) (-p * (∏ L))) in H.
ring_simplify in H.
replace (n * p - p * (∏ L)) with (p*(n-(∏ L))) in H by ring.
pose proof A1P11 p (n - (∏ L)) H.
destruct H2.
assert (N p).
unfold lt in H1.
replace (p-0) with p in H1 by ring.
exact.
apply Z1 in H3.
destruct H3.
contradiction.
apply (S1 (n - (∏ L)) 0 (∏ L)) in H2.
ring_simplify in H2.
exact.
Qed.

Theorem belongDiv : ∀ x1 L2, x1 ∈ L2 → (x1 | ∏ L2).
Proof.
intros x1 L2 H.
apply in_split in H as [l1 [l2]].
rewrite H prod_cons_app.
unfold divide.
eauto using M1, eq_trans.
Qed.

Theorem division : ∀ a b c : Z, a*b=a*c -> not(a=0) -> b=c.
Proof.
intros.
apply (S1 (a*b) (a*c) (-a*c)) in H.
ring_simplify in H.
replace (a * b - a * c) with (a * (b - c)) in H by ring.
apply A1P11 in H.
destruct H.
contradiction.
apply (S1 (b-c) 0 c) in H.
ring_simplify in H.
exact.
Qed.

Theorem existssublist : ¬ (∀ (x1 : Z) L2 (H10 : x1 ∈ L2), ∃ L : list Z, L2 = x1 :: L).
Proof.
intros H.
destruct (H 1 (0 :: 1 :: nil)).
- simpl; tauto.
- inversion H0.
contradiction A3P1.
Qed.

(* Fundamental theorem of arithmetic, a.k.a. unique prime factorization. *)
Theorem A8P7 : ∀ n L1 L2, n = ∏' L1 → n = ∏' L2 → Permutation L1 L2.
Proof.
induction n using A7P2.
intros.
firstorder.
simpl in *.
firstorder.
pose proof length_nonneg L1.
destruct H4.
apply (length_n (length L1) L1) in H4.
destruct H4.
destruct H4.
destruct H4.
assert (x ∈ L1).
subst; firstorder.
destruct (H3 x).
exact.
pose proof belongDiv x L1 H6.
rewrite -H0 in H9.
rewrite H1 in H9.
pose proof A7P7 x L2 H8 H9.
destruct H10.
destruct H10.
assert (x=x1).
destruct (H2 x1).
exact.
unfold prime in *.
destruct H13.
destruct (H14 x).
exact.
destruct H8.
contradiction.
apply A4P5 in H15.
destruct H15.
exact.
rewrite H15 in H7.
apply Z1 in H7.
destruct H7.
unfold lt in H12.
replace (- (- x1 - 0)) with (x1) in H16 by ring.
replace (x1-0) with x1 in H12 by ring.
contradiction.
assert (0<(∏x0)<n).
split.
assert (∀ p : Z, p ∈ x0 → 0 < p ∧ prime p).
intros.
rewrite H4 in H3.
apply H3.
simpl.
by right.
pose proof A8P3 (∏ x0) x0.
assert ((∏ x0) = ∏' x0).
unfold prime_factorization.
exact.
apply H14 in H15.
exact.
assert (n= ∏ (x::x0)).
rewrite -H4.
exact.
simpl in H13.
unfold lt.
rewrite H13.
replace (x * (∏ x0) - (∏ x0)) with ((∏ x0)*(x-1)) by ring.
unfold lt in H7.
replace (x-0) with x in H7 by ring.
apply Nrange in H7.
destruct H7.
unfold lt in H7.
pose proof A8P3 (∏ x0) x0.
assert((∏ x0) = ∏' x0).
unfold prime_factorization.
split.
exact.
intros.
apply H3.
rewrite H4.
simpl.
by right.
apply H14 in H15.
unfold lt in H15.
replace (∏ x0 - 0) with (∏ x0) in H15 by ring.
by pose proof N3 (∏ x0) (x-1) H15 H7.
unfold prime in H8.
destruct H8.
assert (unit x).
unfold unit.
exists 1.
rewrite -H7.
by ring.
contradiction.
assert(∃ L : list Z, (∀ p : Z, p ∈ L → 0 < p ∧ prime p)∧ (∏L2 = ∏(x1 :: L))).
apply in_split in H10 as [l1 [l2]].
rewrite H10 prod_cons_app.
simpl.
exists (l1++l2).
split.
intros.
destruct (H2 p).
subst.
apply in_app_iff.
apply in_app_iff in H14.
destruct H14.
by left.
right.
simpl.
by right.
exact.
exact.  
destruct H14.
assert (∏ L1 = ∏ (x :: x0)).
rewrite H4.
exact.
assert (∀ p : Z, p ∈ x0 → 0 < p ∧ prime p).
intros.
destruct (H3 p).
subst.
simpl.
by right.
exact.
destruct H14.
assert(x1 * (∏ x2) =  x * (∏ x0)).
simpl in *.
rewrite -H17.
rewrite -H15.
rewrite -H1.
rewrite -H0.
exact.
rewrite H12 in H18.
apply division in H18.
apply in_split in H10.
destruct H10 as [L2a].
destruct H10 as [L2b].
subst.
apply Permutation_cons_app.
eapply (H (∏ x0)).
exact.
unfold prime_factorization.
split.
exact.
exact.
unfold prime_factorization.
split.
pose proof prod_cons_app L2a L2b x1.
rewrite H1 in H17.
simpl in H17.
apply division in H17.
rewrite H18 in H17.
exact.
apply Z1 in H7.
destruct H7.
replace (x1-0) with x1 in H4.
exact.
by ring.
intros.
apply H2.
apply in_app_iff.
apply in_app_iff in H1.
destruct H1.
by left.
right.
simpl.
by right.
destruct (H2 x1).
exact.
apply Z1 in H19.
destruct H19.
replace (x1-0) with x1 in H19 by ring.
exact.
exact.
pose proof length_zero L1.
destruct H5.
symmetry in H4.
apply H5 in H4.
assert (n = ∏ L1).
exact.
assert (n = ∏ L2).
exact.
rewrite H4 in H0.
rewrite H0 in H1.
assert (L1=nil) as H120.
exact.
apply A8P4 in H4. 
unfold prime_factorization in H4.
destruct H4.
simpl in H1.
pose proof A8P4 L2.
destruct H10.
assert (1 = ∏' L2).
unfold prime_factorization.
exact.
apply H10 in H12.
rewrite -H12 in H120.
rewrite H120.
exact.
Qed.

Definition eqm n a b := (n | b - a).

Notation "a ≡ b (mod  n )" := (eqm n a b) (at level 70).
  
Section Zn.

  Variable n : Z.

  Theorem eqm_refl : ∀ a : Z, a ≡ a (mod n).
  Proof.
    rewrite /eqm /divide => a.
    exists 0.
    ring.
  Qed.

  Theorem eqm_sym : ∀ a b : Z, a ≡ b (mod n) → b ≡ a (mod n).
  Proof.
    rewrite /eqm /divide => a b [z /(@eq_sym Z) H].
    exists (-z).
    ring [H].
  Qed.

  Theorem eqm_trans : ∀ a b c : Z,
      a ≡ b (mod n) → b ≡ c (mod n) → a ≡ c (mod n).
  Proof.
    rewrite /eqm /divide => a b c [x /(@eq_sym Z) H] [y /(@eq_sym Z) H0].
    exists (x+y).
    ring [H H0].
  Qed.

  Add Parametric Relation : Z (eqm n)
      reflexivity proved by (eqm_refl)
      symmetry proved by (eqm_sym)
      transitivity proved by (eqm_trans) as Z_mod_n.

  Add Morphism add with signature (eqm n) ==> (eqm n) ==> (eqm n) as Zn_add.
  Proof.
    rewrite /eqm /divide => x y [z /(@eq_sym Z) H] x0 y0 [z0 /(@eq_sym Z) H0].
    exists (z+z0).
    ring [H H0].
  Qed.

  Add Morphism mult with signature (eqm n) ==> (eqm n) ==> (eqm n) as Zn_mul.
  Proof.
    rewrite /eqm /divide => x y [z /(@eq_sym Z) H] x0 y0 [z0 /(@eq_sym Z) H0].
    apply (eqm_trans _ (y*x0)); [exists (z*x0) | exists (y*z0)]; ring [H H0].
  Qed.

  Add Morphism neg with signature (eqm n) ==> (eqm n) as Zn_neg.
  Proof.
    rewrite /eqm /divide => x y [z /(@eq_sym Z) H].
    exists (-z).
    ring [H].
  Qed.

  Add Morphism sub with signature (eqm n) ==> (eqm n) ==> (eqm n) as Zn_sub.
  Proof.
    now rewrite /sub => x y /[swap] x0 /[swap] y0 -> ->.
  Qed.

  Add Morphism pow with signature (eqm n) ==> eq ==> (eqm n) as Zn_pow.
  Proof.
    intros x y H k.
    induction k using A7P2.
    destruct (A2P3 k 0) as [ | [ | ]]; subst;
      try by (rewrite ? pow_0_r ? pow_neg_l; auto using eqm_refl).
    destruct (A2P3 k 1) as [ | [ | ]]; subst;
      rewrite ? pow_1_r //; first by contradiction (A3P4 k).
    rewrite ? (pow_pos_r _ k) ? H0 ? H /lt; auto using eqm_refl.
    (have ->: k-1-0 = k-1 by ring); (have ->: k-(k-1) = 1 by ring);
    eauto using N_one.
  Qed.

  Theorem A9P1 : ∀ a b, 0 ≤ a < n → 0 ≤ b < n → a ≡ b (mod n) → a = b.
  Proof.
intros.
unfold eqm in H1.
firstorder.
pose proof A2P6.
pose proof add_lt_r b n (-a) H2.
assert(n-a<n).
unfold lt.
replace (n-(n-a)) with a by ring.
unfold lt in H.
replace (a-0) with a in H by ring.
exact.
assert (b-a<n) by firstorder.
pose proof add_lt_r a n (-b) H3.
apply (A2P4_neg (a+-b) (n+-b) (-1)) in H8.
ring_simplify in H8.
assert (-n+b>-n).
unfold lt.
replace (-n+b--n) with b by ring.
unfold lt in H0.
replace (b-0) with b in H0 by ring.
exact.
assert (-n<b-a) by firstorder.
pose proof A2P3 x 0.
destruct H11.
apply greaterRange in H11.  
destruct H11.
apply (add_lt_r (x+1) 0 (-1)) in H11.
ring_simplify in H11.
pose proof A2P3 n 0.
destruct H12.
assert (n>0) by firstorder.
unfold lt in *.
apply Z1 in H13.
destruct H13.
replace (0-n) with (-(n-0)) in H12 by ring.
contradiction.
destruct H12.
rewrite H12 in H1.
ring_simplify in H1.
apply (S1 (b-a) 0 a) in H1.
ring_simplify in H1.
exact.
apply (A2P4 x (-1) n) in H12.
ring_simplify in H12.
rewrite -H1 in H12.
unfold lt in *.
apply Z1 in H12.
destruct H12.
replace (b - a - - n) with (- (- n - (b - a))) in H10 by ring.
contradiction.
exact.
apply (S1 (x+1) 0 (-1)) in H11.
ring_simplify in H11.
rewrite H11 in H1.
ring_simplify in H1.
apply Z1 in H10.
destruct H10.
apply (S1 (b-a) (-n) n) in H1.
ring_simplify in H1.
replace (b-a+n) with (b-a--n) in H1 by ring.
contradiction.
destruct H11.
rewrite H11 in H1.
ring_simplify in H1.
apply (S1 (b-a) 0 a) in H1.
ring_simplify in H1.
exact.
apply greaterRange in H11.
ring_simplify in H11.
destruct H11.
pose proof A2P3 n 0.
destruct H12.
assert (n>0) by firstorder.
apply Z1 in H12.
destruct H12.
unfold lt in H13.
replace (n-0) with (-(0-n)) in H13 by ring.
contradiction.
destruct H12.
rewrite H12 in H1.
ring_simplify in H1.
apply (S1 (b-a) 0 a) in H1.
by ring_simplify in H1.
apply (A2P4 1 x n) in H11.
ring_simplify in H11.
rewrite M1 in H1.
rewrite -H1 in H11.
apply Z1 in H11.
destruct H11.
unfold lt in H7.
replace (n-(b-a)) with (-(b-a-n)) in H7 by ring.
contradiction.
exact.
rewrite -H11 in H1.
ring_simplify in H1.
apply Z1 in H7.
destruct H7.
apply (S1 (b-a) n (-(b-a))) in H1.
ring_simplify in H1.
symmetry in H1.
replace (-b+a+n) with (n-(b-a)) in H1 by ring.
contradiction.
unfold lt.
replace (0--1) with 1 by ring.
by pose proof N_one.
rewrite -H0 in H1.
ring_simplify in H1.
pose proof A2P6.
assert (n>0) by firstorder.
pose proof A2P3 x 0.
destruct H6.
apply greaterRange in H6.
destruct H6.
apply (add_lt_r (x+1) 0 (-1)) in H6.
ring_simplify in H6.
apply (A2P4 x (-1) n) in H6.
apply (A2P4_neg (x*n) (-1*n) (-1)) in H6.
apply (S2 (-a) (x*n) (-1)) in H1.
ring_simplify in H1.
ring_simplify in H6.
replace (-x*n) with (-n*x) in H1 by ring.
rewrite -H1 in H6.
apply Z1 in H6.
destruct H6.
unfold lt in H3.
replace (n-a) with (-(a-n)) in H3 by ring.
contradiction.
unfold lt.
replace (0--1) with 1 by ring.
by pose proof N_one.
exact.
apply (S1 (x+1) 0 (-1)) in H6.
ring_simplify in H6.
rewrite H6 in H1.
ring_simplify in H1.
apply Z1 in H3.
destruct H3.
apply (S2 (-a) (-n) (-1)) in H1.
apply (S1 (-a*-1) (-n*-1) (-a*1)) in H1.
ring_simplify in H1.
rewrite A1 in H1.
unfold sub in *.
by symmetry in H1.
destruct H6.
rewrite  H6 in H1.
apply (S2 (-a) (0*n) (-1)) in H1.
ring_simplify in H1.
rewrite -H0.
exact.
apply greaterRange in H6.
replace (0+1) with 1 in H6 by ring.
destruct H6.
apply (A2P4 1 x n) in H6.
apply (A2P4_neg (1*n) (x*n) (-1)) in H6.
ring_simplify in H6.
replace (-x*n) with (-(x*n)) in H6 by ring.
rewrite -H1 in H6.
ring_simplify in H6.
assert (-n<0).
unfold lt.
replace (0--n) with n by ring.
unfold lt in H5.
replace (n-0) with n in H5.
exact.
by ring.
assert (a<0) by firstorder.
apply Z1 in H8.
destruct H8.
unfold lt in H.
replace (a-0) with (-(0-a)) in H by ring.
contradiction.
unfold lt.
replace (0--1) with 1 by ring.
by pose proof N_one.
exact.
rewrite -H6 in H1.
ring_simplify in H1.
rewrite -H1 in H3.
unfold lt in H3.
replace (-a-a) with (-(a+a)) in H3 by ring.
unfold lt in H.
replace (a-0) with a in H by ring.
pose proof N2 a a H H.
apply Z1 in H7.
destruct H7.
contradiction.
pose proof A2P6.
assert (n>0) by firstorder.
rewrite  -H in H1.
ring_simplify in H1.
pose proof A2P3 x 0.
destruct H6.
apply greaterRange in H6.
destruct H6.
apply (add_lt_r (x+1) 0 (-1)) in H6.
ring_simplify in H6.
apply (A2P4 x (-1) n) in H6.
rewrite -H1 in H6.
ring_simplify in H6.
assert (-n<0).
unfold lt.
replace (0--n) with n by ring.
unfold lt in H5.
replace (n-0) with n in H5 by ring.
exact.
assert (b<0) by firstorder.
apply Z1 in H8.
destruct H8.
unfold lt in H0.
replace (b-0) with (-(0-b)) in H0 by ring.
contradiction.
exact.
apply (S1 (x+1) 0 (-1)) in H6.
ring_simplify in H6.
rewrite H6 in H1.
ring_simplify in H1.
assert (-n<0).
unfold lt.
replace (0--n) with n by ring.
unfold lt in H5.
replace (n-0) with n in H5 by ring.
exact.
rewrite -H1 in H7.
apply Z1 in H7.
destruct H7.
unfold lt in H0.
replace (b-0) with (-(0-b)) in H0 by ring.
contradiction.
destruct H6.
rewrite H6 in H1.
ring_simplify in H1.
rewrite -H.
exact.
apply greaterRange in H6.
ring_simplify in H6.
destruct H6.
apply (A2P4 1 x n) in H6.
rewrite -H1 in H6.
ring_simplify in H6.
apply Z1 in H6.
destruct H6.
unfold lt in H2.
replace (n-b) with (-(b-n)) in H2 by ring.
contradiction.
exact.
rewrite -H6 in H1.
ring_simplify in H1.
apply Z1 in H2.
destruct H2.
apply (S1 b n (-b)) in H1.
ring_simplify in H1.
rewrite A1 in H1.
unfold sub in *.
by symmetry in H1.
rewrite -H.
exact.
Qed.


  Definition mod_unit a := ∃ b, a * b ≡ 1 (mod n).

  Theorem A9P2 : ∀ a, mod_unit a ↔ rel_prime n a.
  Proof.
split.
intros.
unfold mod_unit in *.
destruct H.
unfold rel_prime.
intros.
unfold eqm in *.
destruct H.
firstorder.
apply (S1 (1-a*x) (x0*n) (a*x)) in H.
ring_simplify in H.
rewrite H1 in H.
rewrite H0 in H.
replace (x1 * d * x + x0 * (x2 * d)) with (d*(x1*x+x0*x2)) in H by ring.
exists (x1 * x + x0 * x2).
rewrite H.
by ring.
intros.
unfold mod_unit.
apply A5P4 in H.
unfold eqm.
unfold divide.
firstorder.
exists x0.
exists x.
rewrite -H.
by ring.
Qed.

Theorem A9P3 : ∀ a b, mod_unit a → mod_unit b → mod_unit (a * b).
Proof.
intros.
apply A9P2 in H.
apply A9P2 in H0.
assert (rel_prime a n).
firstorder.
assert(rel_prime b n) by firstorder.
pose proof A5P7 a b n H1 H2.
pose proof A9P2 (a*b).
destruct H4.
assert (rel_prime n (a*b)) by firstorder.
apply H5 in H6.
exact.
Qed.


Theorem A9P4 : ∀ a b, mod_unit a → ∃ x, b ≡ a * x (mod n).
Proof.
intros.
unfold mod_unit in H.
destruct H.
exists (x*b).
replace (a*(x*b)) with (a*x*b) by ring.
rewrite H.
unfold eqm.
exists 0.
by ring.
Qed.

Theorem A9P5 : ∀ a b c, mod_unit a → a * b ≡ a * c (mod n) → b ≡ c (mod n).
Proof.
intros.
pose proof A9P2 a.
destruct H1.
apply H1 in H.
unfold eqm in H0.
unfold eqm.
replace (a*c-a*b) with (a*(c-b)) in H0 by ring.
pose proof A5P5 n a (c-b) H H0.
exact.
Qed.

 Hypothesis positive_modulus : 0 < n.

Theorem A9P6 : ∀ a, exists ! r, 0 ≤ r < n ∧ a ≡ r (mod n).
Proof.
intros.
pose proof A9P1.
unfold unique.
pose proof Div_alg a n positive_modulus.
destruct H0.
destruct H0.
destruct H0.
exists x0.
split.
split.
exact.
unfold eqm.
unfold divide.
exists (-x).
apply (S1 a (n*x+x0) (-a)) in H0.
apply (S1 (a+-a) (n*x+x0+-a) (-n*x)) in H0.
ring_simplify in H0.
rewrite A1 in H0.
unfold sub.
symmetry in H0.
replace (-x*n) with (-n*x) by ring.
exact.
intros.
destruct H2.
destruct (H x0 x').
exact.
exact.
assert ( a ≡ x0 (mod n)).
unfold eqm.
unfold divide.
exists (-x).
apply (S1 a (n*x+x0) (-a)) in H0.
apply (S1 (a+-a) (n*x+x0+-a) (-n*x)) in H0.
ring_simplify in H0.
rewrite A1 in H0.
unfold sub.
symmetry in H0.
replace (-x*n) with (-n*x) by ring.
exact.
pose proof eqm_sym a x0 H4.
pose proof eqm_trans x0 a x' H5 H3.
exact.
exact.
Qed.

 Notation "'p'" := n (at level 0).
Hypothesis prime_modulus : prime p.
Theorem A9P7 : ∀ a, mod_unit a ↔ ¬ a ≡ 0 (mod p).
Proof.
split.
intros.
unfold not.
intros.
apply A9P2 in H.
unfold rel_prime in H.
assert (a ≡ 0 (mod p)).
exact.
destruct H0.
apply (S2 (0-a) (x*p) (-1)) in H0.
ring_simplify in H0.
destruct (H p).
exists 1.
by ring.
exists (-x).
exact.
assert (unit p).
unfold unit.
exists x0.
exact.
unfold prime in prime_modulus.
destruct prime_modulus.
contradiction.
intros.
pose proof A9P6 a.
unfold unique in *.
destruct H0.
destruct H0.
destruct H0.
destruct H0.
destruct H0.
pose proof A6P4 p x prime_modulus.
destruct H4.
destruct H4.
assert (x0*p>p).
pose proof A2P3 x0 0.
pose proof A2P6.
destruct H5.
pose proof A3P2 p x0 positive_modulus.
destruct H7.
rewrite H4 in H0.
rewrite M1 in H0.
apply H8 in H0.
apply Z1 in H0.
destruct H0.
unfold lt in H5.
replace (0-x0) with (-(x0-0)) in H5 by ring.
contradiction.
destruct H5.
rewrite H5 in H4.
ring_simplify in H4.
apply Z1 in H0.
destruct H0.
replace (x-0) with x in H0 by ring.
contradiction.
apply greaterRange in H5.
ring_simplify in H5.
destruct H5.
apply (A2P4 1 x0 p) in H5.
ring_simplify in H5.
rewrite M1.
exact.
exact.
rewrite -H5 in H4.
ring_simplify in H4.
apply Z1 in H3.
destruct H3.
apply (S1 x p (-x)) in H4.
ring_simplify in H4.
rewrite A1 in H4.
unfold sub in *.
symmetry in H4.
contradiction.
pose proof A2P6.
rewrite -H4 in H5.
assert (x<x) by firstorder.
unfold lt in H7.
replace (x-x) with 0 in H7 by ring.
apply Z1 in H7.
destruct H7.
assert (0=0).
exact.
contradiction.
assert (rel_prime p a).
unfold rel_prime in *.
intros.
destruct H2.
destruct H5.
destruct H6.
rewrite H5 in H2.
rewrite H6 in H2.
apply (S1 (x - x2 * d) (x0 * (x1 * d)) (x2 * d)) in H2.
ring_simplify in H2.
replace  (x2 * d + d * x0 * x1) with (d*(x2+x0*x1)) in H2 by ring.
assert (d|x).
exists (x2+x0*x1).
rewrite M1.
exact.
destruct (H4 d).
exists x1.
exact.
exact.
exists x3.
exact.
apply A9P2 in H5.
exact.
rewrite -H0 in H2.
contradiction.
Qed.

 Theorem A10P1 : ∀ a, mod_unit a → exists ! r, 0 < r < p ∧ a ≡ r (mod p).
Proof.
intros.
unfold unique.
pose proof A9P6 a.
apply A9P7 in H.
destruct H0.
unfold unique in H0.
destruct H0.
exists x.
split.
split.
destruct H0.
destruct H0.
destruct H0.
exact.
destruct H.
rewrite -H0 in H2.
exact.
destruct H0.
exact.
intros.
destruct (H1 x').
split.
unfold le.
split.
left.
destruct H2.
destruct H2.
exact.
destruct H2.
destruct H2.
exact.
destruct H2.
exact.
exact.
Qed.

 Theorem A10P2 : ∀ a, 0 < a ≤ p - 1 → mod_unit a.
Proof.
intros.
assert (¬ a ≡ 0 (mod p)).
unfold not.
intros.
unfold eqm in H0.
destruct H0.
destruct H.
destruct H1.
ring_simplify in H0.
pose proof A2P3 x 0.
pose proof A2P6.
destruct H2.
apply greaterRange in H2.
destruct H2.
apply (add_lt_r (x+1) 0 (-1)) in H2.
ring_simplify in H2.
apply (A2P4  x (-1) p) in H2.
rewrite -H0 in H2.
ring_simplify in H2.
apply (A2P4_neg (-a) (-p) (-1)) in H2.
ring_simplify in H2.
assert (p-1<p).
unfold lt.
replace (p-(p-1)) with 1 by ring.
by pose proof N_one.
assert (a<p) by firstorder.
apply Z1 in H5.
destruct H5.
unfold lt in H2.
replace (a-p) with (-(p-a)) in H2 by ring.
contradiction.
unfold lt.
replace (0--1) with 1  by ring.
by pose proof N_one.
exact.
apply (S1 (x+1) 0 (-1)) in H2 .
ring_simplify in H2.
rewrite H2 in H0.
ring_simplify in H0.
apply (S2 (-a) (-p) (-1)) in H0.
ring_simplify in H0.
assert (p-1<p).
unfold lt.
replace (p-(p-1)) with 1 by ring.
by pose proof N_one.
assert (a<p) by firstorder.
apply Z1 in H5.
destruct H5.
apply (S1 a p (-a)) in H0.
ring_simplify in H0.
rewrite A1 in H0.
unfold sub in * .
by symmetry in H0.
destruct H2.
rewrite H2 in H0.
ring_simplify in H0.
apply Z1 in H.
destruct H.
replace (a-0) with a in H by ring.
apply (S1 (-a) 0 a) in H0.
ring_simplify in H0.
by symmetry in H0.
unfold lt in *.
replace (x-0) with x in H2 by ring.
replace (p-0) with p in positive_modulus by ring.
pose proof N3 x p H2 positive_modulus.
rewrite -H0 in H4.
apply Z1 in H4.
destruct H4.
by replace (--a) with (a-0) in H5 by ring.
ring_simplify in H0.
apply (S1 a (p-1) (-a-p+1)) in H1.
ring_simplify in H1.
rewrite H0 in H1.
apply (S1 (-p+1) (x*p) p) in H1.
ring_simplify in H1.
replace (p*x+p) with (p*(x+1)) in H1 by ring.
assert (unit p).
exists (x+1).
by rewrite M1.
unfold prime in *.
by destruct prime_modulus.
apply A9P7 in H0.
exact.
Qed.

End Zn.

Section partial_sequence.

  Variable f : Z → Z.

  Inductive is_partial_seq : list Z → Prop :=
  | seq_empty : is_partial_seq nil
  | seq_succ L : is_partial_seq L →
                 is_partial_seq (L ++ (f (length L + 1) :: nil)).

  Theorem partial_seq_construction :
    ∀ l, 0 ≤ l → exists ! L, is_partial_seq L ∧ length L = l.
  Proof.
    induction l using A7P2 => [[H0 | <-]].
    2: { exists nil.
         subst; split; auto using seq_empty => x' [? /length_zero] //. }
    destruct (A2P3 l 1) as [ | [ | ]]; subst; first by contradiction (A3P4 l).
    - exists (nil ++ (f (length nil + 1)) :: nil).
      split; simpl; intuition try ring.
      + rewrite -(app_nil_l (f(0+1)::nil)) -[0]/(length nil).
        auto using seq_succ, seq_empty.
      + inversion H2; subst; simpl in *; try by contradiction A3P1.
        rewrite -length_app /= A1P1 in H3.
        rewrite H3 A1P1 -(app_nil_l (f 1 :: nil)) in H2 |-*.
        f_equal.
        apply eq_sym, length_zero.
        rewrite -(A3 (length L)) -(A4 1) A2 H3 //.
    - apply (A7P3 (-1)) in H1.
      ring_simplify in H1.
      destruct (H (l-1)) as [L [H2 H3]]; firstorder.
      { (have {2}->: l = l-1+1 by ring); auto using A7P1. }
      exists (L ++ (f (length L + 1)) :: nil).
      (repeat split; auto using seq_succ;
       rewrite -? length_app ? H4 /=; try ring) => L' [H5 H6].
      inversion H5; subst; simpl in *.
      + move: H4 (length_nonneg L) -> => /A3P3b [].
        rewrite -{2}(A4 1) /sub ? (A1 _ (-1)) -{3}(A1P1 1) A2.
        auto using A7P1.
      + have ?: L = L0; [ apply H3 | repeat f_equal; auto ];
          rewrite -length_app /=; intuition ring.
  Qed.

  Definition partial_seq : Z → list Z.
  Proof.
    intros n.
    destruct (excluded_middle_informative (0 ≤ n)).
    - destruct (constructive_definite_description
                  _ (partial_seq_construction _ l)) as [L [H H0]].
      exact L.
    - exact nil.
  Defined.

  Theorem partial_seq_0 : partial_seq 0 = nil.
  Proof.
    unfold partial_seq.
    destruct excluded_middle_informative; auto.
    destruct constructive_definite_description as [L [H0 H1]].
    firstorder using length_zero.
  Qed.

  Theorem partial_seq_succ : ∀ n,
      0 ≤ n → partial_seq (n + 1) =
                (partial_seq n) ++ (f (n + 1) :: nil).
  Proof.
    rewrite {1}/partial_seq => n H.
    case excluded_middle_informative => [l | n0].
    - elim constructive_definite_description => [L [H0 H1]].
      inversion H0; subst.
      + move: H1 H => /= -> /A3P3b []; auto using A7P1.
      + have H3: length L0 = n
          by rewrite -(A3 n) -(A4 1) A2 -H1 -length_app /=; ring.
        repeat f_equal; auto.
        rewrite /partial_seq.
        (case excluded_middle_informative; try by firstorder) =>
          /partial_seq_construction [L [[H4 H5] H6]].
        elim constructive_definite_description => [L' [H7 H8]].
        rewrite -(H6 L0) // -(H6 L') //.
    - contradict n0.
      destruct H as [H | H]; subst; firstorder using A2P6, A7P1.
  Qed.

End partial_sequence.

Theorem A10P3 : ∀ f n, 0 < n → f n ∈ partial_seq f n.
Proof.
intros.
pose proof partial_seq_succ f.
assert ( 0 ≤ n-1).
apply (add_lt_r 0 n (-1)) in H.
ring_simplify in H.
apply greaterRange in H.
ring_simplify in H.
exact.
apply H0 in H1.
replace (n-1+1) with n in H1 by ring.
rewrite H1.
rewrite in_app_iff.
right.
simpl.
by left.
Qed.

Lemma A10P4sup : ∀ m n, m<n → ∃a, a>0 ∧ n=m+a.
intros.
exists (n-m).
split.
apply (add_lt_r m n (-m)) in H.
ring_simplify in H.
rewrite A1 in H.
unfold sub.
exact.
by ring.
Qed.

Lemma undoSplit: ∀ y x : Z, (∀ L, y ∈ (L ++ x :: nil) → y ∈ L ∨ y = x).
Proof.
intros.
apply In_rev in H.
rewrite rev_unit in H.
simpl in H.
destruct H; firstorder.
apply In_rev in H.
by left.
Qed.

Theorem partial_seq_neg : ∀ n f, ¬ 0 ≤ n → partial_seq f n = nil.
 Proof.
intros n H.
unfold partial_seq.
destruct excluded_middle_informative; tauto.
Qed.

Lemma negNil: ∀ f m, m<0 -> partial_seq f m = nil.
intros.
pose proof partial_seq_neg m f.
assert (¬ 0 ≤ m).
unfold not.
intros.
destruct H1.
apply Z1 in H1.
destruct H1.
unfold lt in H.
replace (0-m) with (-(m-0)) in H by ring.
exact.
apply Z1 in H.
destruct H.
apply (S1 0 m (-m)) in H1.
ring_simplify in H1.
replace (0-m) with (-m) in H by ring.
exact.
by apply H0 in H1.
Qed.

Theorem A10P4 : ∀ m f n x, m < n → x ∈ partial_seq f m → x ∈ partial_seq f n.
Proof.
intros.
pose proof partial_seq_succ f.
apply A10P4sup in H.
destruct H as [a].
destruct H.
subst.
elim/induction_with_lt: H.
pose proof A2P3 m 0.
destruct H.
pose proof negNil f m.
apply H2 in H.
rewrite H in H0.
firstorder.
assert(0 ≤ m).
unfold le.
destruct H.
by right.
by left.
apply H1 in H2.
rewrite H2.
apply in_app_iff.
by left.
intros.
pose proof A2P3 m 0.
destruct H3.
pose proof negNil f m.
apply H4 in H3.
rewrite H3 in H0.
firstorder.
assert(0 ≤ m+n).
unfold le.
destruct H3.
rewrite H3.
left.
ring_simplify.
exact.
left.
unfold lt.
replace (m+n-0) with (m+n) by ring.
unfold lt in *.
replace (n-0) with n in H by ring.
replace (m-0) with m in H3 by ring.
by pose proof N2 m n H3 H.
apply H1 in H4.
replace (m+n+1) with (m+(n+1)) in H4 by ring.
rewrite H4.
apply in_app_iff.
by left.
Qed.

Theorem lengthPartial_seq : ∀ f n, 0≤n ->length(partial_seq f n)=n.
Proof.
intros.
destruct H.
elim/induction_with_lt: H.
replace 1 with (0+1) by ring.
rewrite partial_seq_succ.
unfold le.
by right.
rewrite partial_seq_0.
simpl.
by ring.
intros.
rewrite partial_seq_succ.
by left.
rewrite -{3}(H0).
rewrite -length_app.
simpl.
by ring.
subst.
rewrite partial_seq_0.
firstorder.
Qed.


Theorem A10P5 : ∀ f n y, y ∈ (partial_seq f n) ↔ ∃ x, 0 < x ≤ n ∧ f x = y.
Proof.
split.
intros.
pose proof length_nonneg (partial_seq f n).
pose proof lengthPartial_seq f.
pose proof A2P3 n 0.
destruct H2.
pose proof negNil f n.
apply H3 in H2.
rewrite H2 in H.
firstorder.
assert (0 ≤ n ).
unfold le.
destruct H2.
by right.
by left.
apply H1 in H3.
rewrite H3 in H0.
destruct H0.
clear H1 H2 H3.
revert H.
elim/induction_with_lt: H0.
intros.
pose proof partial_seq_succ f.
exists 1.
split.
split.
unfold lt.
replace (1-0) with 1 by ring.
by pose proof N_one.
by right.
pose proof partial_seq_0 f.
assert (0 ≤ 0).
by right.
apply H0 in H2.
replace (0+1) with 1 in H2 by ring.
rewrite H2 in H.
apply in_app_iff in H.
destruct H.
rewrite H1 in H.
firstorder.
firstorder.
clear n.
intros.
pose proof partial_seq_succ f.
assert (0 ≤ n).
by left.
apply H2 in H3.
rewrite H3 in H1.
apply in_app_iff in H1.
destruct H1.
apply H0 in H1.
destruct H1.
exists x.
split.
split.
destruct H1.
destruct H1.
exact.
destruct H1.
destruct H1.
destruct H5.
left.
unfold lt in *.
pose proof N2 (n-x) 1 H5 N_one.
replace (n+1-x) with (n-x+1) by ring.
exact.
rewrite H5.
left.
unfold lt.
replace (n+1-n) with 1 by ring.
by pose proof N_one.
destruct H1.
exact.
exists (n+1).
split.
split.
unfold lt in *.
pose proof N2 (n-0) 1 H N_one.
replace (n+1-0) with (n-0+1) by ring.
exact.
by right.
firstorder.
pose proof partial_seq_0 f.
rewrite -H0 in H.
rewrite H4 in H.
firstorder.
intros.
destruct H.
pose proof A10P3 f.
repeat destruct H.
apply H0 in H.
rewrite H1 in H.
destruct H2.
pose proof A10P4 x f n y.
apply H3.
exact.
exact.
rewrite H2 in H.
exact.
Qed.

Theorem A10P6 :
  ∀ a n, 0 ≤ n → ∏ (partial_seq (λ x, a * x) n) = a^n * ∏ (partial_seq id n).
Proof.
intros.
destruct H.
elim/induction_with_lt: H.
pose proof partial_seq_succ [eta mult a].
assert (0 ≤ 0).
by right.
assert (1=0+1).
by ring.
apply H in H0.
rewrite -H1 in H0.
pose proof partial_seq_0 [eta mult a].
rewrite H2 in H0.
pose proof prod_cons_app nil nil (a*1).
assert (∏(partial_seq [eta mult a] 1) = ∏(nil ++ a * 1 :: nil)).
rewrite H0.
exact.
rewrite H3 in H4.
rewrite app_nil_r in H4.
simpl in H4.
ring_simplify in H4.
rewrite H4.
pose proof partial_seq_succ id.
assert (0 ≤ 0).
by right.
apply H5 in H6.
rewrite -H1 in H6.
pose proof partial_seq_0 id.
rewrite H7 in H6.
pose proof prod_cons_app nil nil 1.
assert ( ∏(partial_seq id 1) = ∏(nil ++ 1 :: nil)).
rewrite H6.
exact.
rewrite H8 in H9.
rewrite app_nil_r in H9.
simpl in H9.
rewrite H9.
ring_simplify.
pose proof pow_1_r a.
rewrite H10.
exact.
intros.
pose proof partial_seq_succ (λ x, a * x).
assert (0 ≤ n0).
unfold le.
by left.
apply H1 in H2.
assert (∏ partial_seq [eta mult a] (n0 + 1) = ∏ (partial_seq [eta mult a] n0 ++ a * (n0 + 1) :: nil)).
rewrite H2.
exact.
pose proof prod_cons_app (partial_seq [eta mult a] n0) nil (a * (n0 + 1)).
rewrite H4 in H3.
assert ((partial_seq [eta mult a] n0 ++ nil)=(partial_seq [eta mult a] n0)).
rewrite app_nil_r.
exact.
rewrite H5 in H3.
pose proof partial_seq_succ (id).
assert (0 ≤ n0).
unfold le.
by left.
apply H6 in H7.
assert(∏partial_seq id (n0 + 1)=∏(partial_seq id n0 ++ n0 + 1 :: nil)).
rewrite H7.
exact.
pose proof prod_cons_app (partial_seq id n0) nil (n0 + 1).
rewrite H9 in H8.
assert ((partial_seq id n0 ++ nil)=(partial_seq id n0)).
rewrite app_nil_r.
exact.
rewrite H10 in H8.
apply (S2 (∏ partial_seq [eta mult a] n0) (a ^ n0 * (∏ partial_seq id n0)) (n0 + 1)) in H0.
replace (a ^ n0 * (∏ partial_seq id n0) * (n0 + 1)) with (a ^ n0 * ((n0 + 1) * (∏ partial_seq id n0))) in H0 by ring.
rewrite -H8 in H0.
apply (S2 ((∏ partial_seq [eta mult a] n0) * (n0 + 1)) (a ^ n0 * (∏ partial_seq id (n0 + 1))) a) in H0.
replace ((∏ partial_seq [eta mult a] n0) * (n0 + 1) * a) with (a * (n0 + 1) * (∏ partial_seq [eta mult a] n0)) in H0 by ring.
rewrite -H3 in H0.
pose proof pow_1_r a.
rewrite -{3}(H11) in H0.
assert (0 ≤ n0).
unfold le.
by left.
assert(0 ≤ 1 ).
unfold le.
pose proof N_one.
unfold lt.
left.
replace (1-0) with 1 by ring.
exact.
pose proof A7P4 a n0 1 H12 H13.
replace (a ^ n0 * (∏ partial_seq id (n0 + 1)) * a ^ 1) with (a ^ n0 * a ^ 1* (∏ partial_seq id (n0 + 1)) ) in H0 by ring.
rewrite -H14 in H0.
exact.
rewrite -H.
pose proof partial_seq_0 [eta mult a].
rewrite H0.
pose proof partial_seq_0 id.
rewrite H1.
simpl.
pose proof pow_0_r a.
rewrite H2.
by ring.
Qed.

Require Export SetoidList SetoidPermutation.

Section Fermat's_Little_Theorem.

  Variable p : Z.
  Hypothesis prime_p : prime p.
  Hypothesis positive_p : N p.

  Add Parametric Relation : Z (eqm p)
      reflexivity proved by (eqm_refl p)
      symmetry proved by (eqm_sym p)
      transitivity proved by (eqm_trans p) as Z_mod_p.

  Add Morphism mult with signature (eqm p) ==> (eqm p) ==> (eqm p) as Zp_mul.
  Proof.
    auto using Zn_mul.
  Qed.

  Theorem A11P1 : ∀ L, (∀ a, a ∈ L → mod_unit p a) → mod_unit p (∏ L).
  Proof.
intros.
unfold mod_unit in *.
induction L.
simpl.
exists 1.
replace (1*1) with 1 by ring.
unfold eqm.
exists 0.
by ring.
simpl in *.
destruct (H a).
left.
exact.
assert(∀ a0 : Z, a0 ∈ L → ∃ b : Z, a0 * b ≡ 1 (mod p)).
firstorder.
destruct IHL.
exact.
exists(x*x0).
replace (a * (∏ L) * (x * x0)) with (a*x*((∏ L) * x0)) by ring.
rewrite H0.
rewrite H2.
ring_simplify.
exists 0.
by ring.
Qed.


  Theorem A11P2 : ∀ L L', PermutationA (eqm p) L L' → ∏ L ≡ ∏ L' (mod p).
  Proof.
intros L L' H.
induction H.
simpl.
exists 0.
by ring.
simpl.
rewrite IHPermutationA.
rewrite H.
exists 0.
by ring.
simpl.
exists 0.
by ring.
pose proof eqm_trans p (∏ l₁) (∏ l₂) (∏ l₃).
apply H1 in IHPermutationA1.
exact.
exact.
Qed.

  Definition injectiveA (f : Z → Z) n :=
    ∀ x y, 0 < x ≤ n → 0 < y ≤ n → f x ≡ f y (mod p) → x = y.
  
  Theorem A11P3 : ∀ f n, injectiveA f n → NoDupA (eqm p) (partial_seq f n).
  Proof.
intros.
pose proof length_nonneg (partial_seq f n).
pose proof lengthPartial_seq f n.
pose proof A2P3 n 0.
destruct H2.
assert (¬ 0 ≤ n).
apply Z1 in H2.
unfold not.
intros.
unfold le in *.
destruct H3.
unfold lt in H3.
destruct H2.
replace (-(0-n)) with (n-0) in H4 by ring.
contradiction.
apply (S1 0 n (-n)) in H3.
ring_simplify in H3.
destruct H2.
replace (0-n) with (-n) in H2 by ring.
contradiction.
pose proof partial_seq_neg n f H3.
rewrite H4.
firstorder.
destruct H2.
rewrite H2.
rewrite  partial_seq_0.
firstorder.
revert H.
clear H0 H1.
elim/induction_with_lt: H2.
intros.
pose proof partial_seq_succ f 0.
assert ( 0 ≤ 0 ).
unfold le.
by right.
apply H0 in H1.
assert (1=0+1).
by ring.
symmetry in H2.
rewrite H2 in H1.
pose proof partial_seq_0 f.
rewrite H3 in H1.
simpl in H1.
pose proof NoDupA_singleton (eqm p) (f 1).
rewrite H1.
exact.
clear n.
intros.
assert(0 ≤ n).
left.
exact.
pose proof partial_seq_succ f n H2.
unfold injectiveA in *.
assert (∀ x y : Z, 0 < x ≤ n + 1 → 0 < y ≤ n + 1 → ¬(x = y) → ¬(f x ≡ f y (mod p))).
intros.
unfold not.
intros.
pose proof H1 x y H4 H5 H7.
contradiction.
assert ((∀ x y : Z, 0 < x ≤ n → 0 < y ≤ n → f x ≡ f y (mod p) → x = y)).
intros.
pose proof A2P6.
unfold le.
assert (n<n+1).
unfold lt.
replace (n+1-n) with 1 by ring.
by pose proof N_one.
apply H1.
clear H H0 H1 H2 H3 H4 H7.
unfold le.
split.
destruct H5.
exact.
destruct H5.
destruct H0.
left.
firstorder.
left.
rewrite H0.
exact.
split.
destruct H6.
exact.
unfold le.
clear H H0 H1 H2 H3 H4 H7.
destruct H6.
destruct H0.
left.
firstorder.
left.
rewrite H0.
exact.
exact.
apply H0 in H5.
rewrite H3.
assert (∀ x : Z, 0 < x < n + 1 -> ¬ f x ≡ f (n+1) (mod p)).
intros.
apply H4.
split.
destruct H6.
exact.
unfold le.
left.
destruct H6.
exact.
split.
pose proof A2P6.
assert (n<n+1).
unfold lt.
replace (n+1-n) with 1 by ring.
by pose proof N_one.
clear H0 H1 H2 H3 H4 H5 H6.
firstorder.
right.
exact.
unfold not.
intros.
destruct H6.
apply Z1 in H8.
destruct H8.
apply (S1 x (n+1) (-x)) in H7.
ring_simplify in H7.
symmetry in H7.
replace (- x + n + 1) with (n + 1 - x) in H7 by ring.
contradiction.
pose proof NoDupA_singleton (eqm p) (f(n+1)).
pose proof NoDupA_app.
assert ((∀ x : Z, InA (eqm p) x (f (n + 1) :: nil) → InA (eqm p) x (partial_seq f n) → False)).
intros.
apply InA_singleton in H9.
apply InA_alt in H10.
destruct H10.
destruct H10.
apply (A10P5 f n x0) in H11.
destruct H11.
destruct H11.
assert (0<x1<n+1).
destruct H11.
split.
exact.
assert (n<n+1).
unfold lt.
replace (n+1-n) with 1 by ring.
by pose proof N_one.
pose proof A2P6.
destruct H13.
clear H H0 H1 H2 H3 H4 H5 H6 H7 H8 H9 H10.
firstorder.
clear H H0 H1 H2 H3 H4 H5 H6 H7 H8 H9 H10.
rewrite H13.
exact.
apply H6 in H13.
rewrite H12 in H13.
assert (x0 ≡ x  (mod p)).
apply eqm_sym in H10.
exact.
pose proof eqm_trans p x0 x (f(n+1)).
apply H15 in H14.
contradiction.
exact.
pose proof H8 Z (eqm p).
assert (NoDupA (eqm p) ((f (n + 1) :: nil) ++ (partial_seq f n))).
apply H10.
split; eauto using eqm_refl, eqm_sym, eqm_trans.
exact.
exact.
exact.
assert (PermutationA (eqm p) ((f (n + 1) :: nil) ++ partial_seq f n) ((partial_seq f n) ++ (f (n + 1) :: nil))).
apply PermutationA_app_comm.
split; eauto using eqm_refl, eqm_sym, eqm_trans.
assert (NoDupA (eqm p) ((f (n + 1) :: nil) ++ partial_seq f n) -> NoDupA (eqm p) (partial_seq f n ++ f (n + 1) :: nil)).
apply PermutationA_preserves_NoDupA.
split; eauto using eqm_refl, eqm_sym, eqm_trans.
exact.
apply H13 in H11.
exact.
Qed.

  Theorem A11P4 : ∀ a, mod_unit p a →
                       PermutationA (eqm p) (partial_seq id (p-1))
                                    (partial_seq (λ x, a * x) (p-1)).
  Proof.
intros.
destruct (classic (PermutationA (eqm p) (partial_seq id (p - 1)) (partial_seq [eta mult a] (p - 1)))).
exact.
assert (∃ e b c d, (PermutationA (eqm p) (e++b) (partial_seq id (p - 1))) /\
(PermutationA (eqm p) (c++d) (partial_seq [eta mult a] (p - 1))) /\
(PermutationA (eqm p) e c) /\
∃x, (not (InA (eqm p) x b) /\ (InA (eqm p) x d))).
admit.
destruct H1.
destruct H1.
destruct H1.
destruct H1.
destruct H1.
destruct H2.
destruct H3.
destruct H4.
destruct H4.

apply InA_alt in H5.
destruct H5.
destruct H5.
destruct (classic ((eqm p) x3 0)).
admit.
apply A9P7 in H7.
apply A10P1 in H7.
destruct H7.
destruct H7.
destruct H7.
assert (∃ x, 0 < x ≤ p-1 ∧ id x = x5).
exists x5.
split.
destruct H7.
split.
exact.
apply greaterRange in H10.
unfold le.
destruct H10.
apply (add_lt_r (x5+1) p (-1)) in H10.
ring_simplify in H10.
by left.
apply (S1 (x5+1) p (-1)) in H10.
ring_simplify in H10.
by right.
exact.
apply A10P5 in H10.
assert (InA (eqm p) x5 x0).
auto.




  Admitted.

  Theorem A11P5 : ∀ a, mod_unit p a → a^(p-1) ≡ 1 (mod p).
  Proof.
  Admitted.

End Fermat's_Little_Theorem.
