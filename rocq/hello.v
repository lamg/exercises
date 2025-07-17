Inductive day : Type :=
  | monday
  | tuesday
  | wednesday
  | thursday
  | friday
  | saturday
  | sunday.

Definition next_working_day (d:day) : day :=
  match d with
  | monday => tuesday
  | tuesday => wednesday
  | wednesday => thursday
  | thursday => friday
  | friday => monday
  | saturday => monday
| sunday => monday
  end.

Example test_next_working_day:
  (next_working_day (next_working_day saturday)) = tuesday.
Proof. simpl. reflexivity. Qed.

Inductive bool: Type :=
  | true
  | false.

Definition negb (b: bool): bool :=
  match b with
  | true => false
  | false => true
  end.

Definition andb (x: bool) (y: bool): bool :=
  match x with
  | true => y
  | false => false
  end.

Definition orb (x: bool) (y: bool): bool :=
  match x with
  | true => true
  | false => y
  end.

Example not_true_and_false:
  (andb (negb true) false) = false.
Proof. simpl. reflexivity. Qed.

Example true_or_false:
  orb true false = true.
Proof. simpl. reflexivity. Qed.


Notation "x && y" := (andb x y).

Notation "x || y" := (orb x y).

Example or_notation:
  true || false = true.
Proof.  reflexivity. Qed.

Example and_notation:
  true && false = false.
Proof. reflexivity. Qed.

Definition negb' (b: bool): bool :=
  if b then false else true.

Example negs_are_equal:
  negb = negb'.
Proof. reflexivity. Qed.

Inductive black_white: Type :=
  | black
  | white.

Definition invert (x: black_white): black_white :=
  if x then white else black.

Example invert_white :
  invert white = black.
Proof. reflexivity. Qed.

Definition nandb (b1:bool) (b2:bool) : bool
  := negb (andb b1 b2).
Example test_nandb1: (nandb true false) = true.
Proof. reflexivity. Qed.
Example test_nandb2: (nandb false false) = true.
Proof. reflexivity. Qed.
Example test_nandb3: (nandb false true) = true.
Proof. reflexivity. Qed.
Example test_nandb4: (nandb true true) = false.
Proof. reflexivity. Qed.

Definition andb3 (b1:bool) (b2:bool) (b3:bool) : bool :=
  andb b1 (andb b2 b3).
Example test_andb31: (andb3 true true true) = true.
Proof. reflexivity. Qed.
Example test_andb32: (andb3 false true true) = false.
Proof. reflexivity. Qed.
Example test_andb33: (andb3 true false true) = false.
Proof. reflexivity. Qed.
Example test_andb34: (andb3 true true false) = false.
Proof. reflexivity. Qed.

Check (negb true):bool.

Check negb: bool -> bool.

Inductive rgb: Type :=
  | red 
  | green
  | blue.

Inductive color: Type :=
  | bw (b: black_white)
  | primary (p: rgb).

Definition monochrome (c: color): bool :=
  match c with
  | bw _ => true
  | _ => false
  end.

Definition is_red (c: color): bool :=
  match c with
  | primary red => true
  | _ => false
  end.

Example blue_is_not_red:
 (is_red (primary blue) = false).
Proof. simpl. reflexivity. Qed.

Module Playground.
  Definition foo: rgb := blue.
End Playground.

Definition foo : bool := true.

Check Playground.foo: rgb.
Check foo:bool.

Module TuplePlayground.
  Inductive bit: Type :=
    | B₁
    | B₀.

  Inductive nybble: Type := 
  | bits (b₀ b₁ b₂ b₃ : bit).

  Check (bits B₀ B₁ B₀ B₁: nybble).

  Definition all_zero (nb: nybble) :=
    match nb with
    | bits B₀ B₀ B₀ B₀ => true
    | _ => false
    end.

  Example not_all_zero:
   all_zero (bits B₀ B₁ B₀ B₁) = false.
  Proof. reflexivity. Qed.
End TuplePlayground.

Module NatPlayground.
  Inductive nat : Type :=
    | zero
    | succ (n: nat).
  
  Definition pred (n: nat): nat :=
    match n with
    | zero => zero 
    | succ n => n
    end.
  
  Definition minustwo (n : nat) : nat :=
    match n with
    | zero => zero
    | succ zero => zero
    | succ (succ n) => n
    end.      
  
  
  Fixpoint is_even (n: nat): bool :=
    match n with
    | zero => true
    | succ(succ n) => is_even n
    | _ => false
    end.
  
  Definition one: nat := succ zero.
  Definition three: nat := succ (succ (succ (zero))).
  Definition four : nat := succ (succ (succ (succ zero))). 
  Definition five: nat := succ four.
  Definition two :nat  := succ (succ zero).
  Definition nine: nat := succ(  succ (succ (succ (succ (succ (succ (succ (succ zero)))))))).  
  
  Example four_minus_two_is_two:
    minustwo four = two.
  Proof. simpl. reflexivity. Qed. 
  
  Example four_is_even:
    is_even four = true.
  Proof. reflexivity. Qed.

  Example three_is_not_even:
    is_even three = false.
  Proof. reflexivity. Qed.
    
  Definition is_odd (n:nat) := negb (is_even n).

  Example three_is_odd:
    is_odd three = true.
  Proof. reflexivity. Qed.    
  
  Fixpoint plus (n:nat) (m:nat): nat :=
    match n with
    | zero => m
    | succ n => succ (plus n m)
  end.

  Example two_plus_two_is_four:
    plus two two = four.
  Proof. reflexivity. Qed.

  Fixpoint mult (n m :nat ): nat :=
    match n with
    | zero => zero
    | succ n => plus m (mult n m)
  end.
  
  Example three_times_three_is_nine:
    mult three three = nine.
  Proof. reflexivity. Qed.
  
  Fixpoint minus (n m : nat) :=
    match n, m with
    | zero, _ => zero
    | _ , zero => n
    | succ n, succ m => minus n m
    end.
   
  Example three_minus_one_is_two :
    minus three one = two.
  Proof. reflexivity. Qed.

  Fixpoint exp (base power: nat) :=
    match power with
    | zero => one
    | succ p => mult base (exp base p)
    end.
  
  Example square_of_three_is_nine: 
    exp three two = nine.
  Proof. reflexivity. Qed.
  
  Fixpoint factorial (n: nat) :=
    match n with
    | zero => one
    | succ n' => mult n (factorial n')
  end.

  Example factorial_three_is_six:
    factorial three = plus three three.
  Proof. reflexivity. Qed.
  
  Definition ten := mult five two.
  Definition twelve := plus ten two.

  Example factorial_five_is_120:
    factorial five = mult ten twelve.
  Proof. reflexivity. Qed.
    
  Notation "x + y" := (plus x y).
  Notation "x - y" := (minus x y).
  Notation "x * y" := (mult x y).
  
  Check one + two: nat.
  
  Fixpoint eqb (n m: nat) :=
    match n, m with
    | zero, zero => true
    | succ n', succ m' => eqb n' m'
    | _, _ => false
    end.
  
  Example two_differs_from_three:
    eqb two three = false.
  Proof. reflexivity. Qed.
  
  Fixpoint leb (n m :nat) :=
    match n, m with
    | zero, _ => true
    | succ n', succ m' => leb n' m'
    | _, _ => false
    end.
  
  Example two_leb_three:
    leb two three = true.
  Proof. reflexivity. Qed.
  
  Example not_three_leb_two:
    leb three two = false.
  Proof. reflexivity. Qed.

  Fixpoint gt(n m :nat) :=
    match n,m with
    | succ n', zero => true
    | succ n', succ m' => gt n' m'
    | _, _ => false
  end.
  
  Notation "x =? y" := (eqb x y) (at level 70): nat_scope.
  Notation "x <=? y" := (leb x y) (at level 70): nat_scope.
  Notation "x >? y" := (gt x y) (at level 70): nat_scope.

  Example notation_test:
    three <=? two = false.
  Proof. reflexivity. Qed.
  
  Definition ltb (n m : nat) := andb (n <=? m) (negb (n =? m)).
  Notation "x <? y" := (ltb x y) (at level 70): nat_scope.
  
  Example ltb_two_three:
    ltb two three = true.
  Proof. reflexivity. Qed.

  Example ltw_two_two:
    ltb two two = false.
  Proof. reflexivity. Qed.

  Example ltw_four_two:
    ltb four two = false.
  Proof. reflexivity. Qed.
  
  Theorem plus_zero_n:
    forall n:nat, zero + n = n.
  Proof. intros n. simpl. reflexivity. Qed. 
  
  Theorem mult_zero_n:
    forall n: nat, zero * n = zero.
  Proof. intros n. reflexivity. Qed.

  Theorem plus_id_example:
    forall n m : nat, 
    n = m -> n + n = m + m.
  Proof. intros n m. intros antecedent. rewrite antecedent. reflexivity. Qed.

  Theorem plus_id_exercise:
    forall n m p: nat,
      n = m -> m = p -> n + m = m + p.
    Proof.
      intros n m p.
      intros antecedent0.
      intros antecedent1.
      rewrite antecedent0.
      rewrite antecedent1.
      reflexivity.
    Qed.
  
  Check mult_zero_n.
  
  Theorem mult_n_zero: 
    forall n:nat, 
    n * zero = zero.
  Proof. Admitted. 
  
  Theorem mult_n_succ_m:
    forall n m: nat,
    n * m + n = n * succ m.
  Proof. Admitted.

  Theorem mult_n_zero_m_zero:
    forall p q: nat,
    (p * zero) + (q * zero) = zero.
    Proof.
      intros p q.
      rewrite mult_n_zero.
      rewrite mult_n_zero.
      reflexivity.
    Qed.
  
  Lemma one_is_succ_zero:
    one = succ zero.
  Proof. reflexivity. Qed.

  Theorem mult_p_one:
    forall p:nat,
    p * one = p.
  Proof.
    intros p.
    rewrite one_is_succ_zero.
    rewrite <- mult_n_succ_m.
    rewrite mult_n_zero.
    simpl.
    reflexivity.
  Qed.

  (* proof by case analysis *)

  Theorem plus_one_neq_zero:
    forall n: nat,
    (n + one) =? zero = false.
    Proof.
      intros n.
      destruct n as [| n' ] eqn:E.
      - reflexivity.
      - reflexivity.
    Qed.
  
  Theorem negb_is_involutive:
    forall b: bool,
    negb (negb b) = b.
  Proof. 
    intros b.
    destruct b eqn:E.
    - reflexivity.
    - reflexivity.
  Qed.
  
  Theorem andb_is_commutative:
    forall x y: bool,
    andb x y = andb y x.
  Proof.
    intros x y.
    destruct x eqn:E.
    - destruct y eqn:F.
      + reflexivity.
      + reflexivity.
    - destruct y eqn:F.
      + reflexivity.
      + reflexivity.
  Qed.
  
  Theorem andb3_exchange :
    forall x y z, andb (andb x y) z = andb (andb x z) y.
  Proof.
    intros x y z.
    destruct x eqn:E.
    - destruct y eqn:F.
      + destruct z eqn:G.
        ++ reflexivity.
        ++ reflexivity.
      + destruct z eqn:G.
        ++ reflexivity.
        ++ reflexivity.
    - destruct y eqn: F.
      + destruct z eqn:G.
        ++ reflexivity.
        ++ reflexivity.
      + destruct z eqn:G.
        ++ reflexivity.
        ++ reflexivity.
    Qed.

  Theorem andb_true_elim2:
    forall x y, andb x y = true -> y = true.
  Proof.
    intros x y.
    destruct x eqn:E.
    - destruct y eqn:F.
      + reflexivity.
      + simpl. intro a. rewrite a. reflexivity.
    - destruct y eqn:F.
      + reflexivity.
      + simpl. intro a. rewrite a. reflexivity. 
  Qed.
 

  Theorem plus_one_neq_zero':
    forall n, n + one =? zero = false.
  Proof.
    intros [|n].
    - reflexivity.
    - reflexivity.
  Qed.

  Theorem andb_is_commutative'' :
    forall x y, andb x y =  andb y x.
  Proof.
    intros [] [].
    - reflexivity.
    - reflexivity.
    - reflexivity.
    - reflexivity.
  Qed.

  Theorem zero_nbeq_plus_one:
    forall n,
    zero =? (n + one) = false.
  Proof.
    intros [|n'].
    - reflexivity.
    - reflexivity.
  Qed.

  (* gcd terminates but Rocq doesn't know how *)
  (* Fixpoint gcd (m n : nat) := *)
  (*   if m =? n then *)
  (*     m *)
  (*   else *)
  (*     if gt m n then gcd (m - n) n *)
  (*     else gcd m (n - m). *)
  (*   . *)
  (* end. *)


  Theorem identity_fn_applied_twice:
    forall f: bool -> bool,
    (forall x, f x = x) ->
    forall b, f (f b) = b.
  Proof.
    intro f.
    intro a.
    intro b.
    rewrite a.
    rewrite a.
    reflexivity.
  Qed.

  Theorem negation_fn_applied_twice:
    forall f: bool -> bool,
    (forall x, f x = negb x) ->
    forall b, f (f b) = b.
  Proof.
    intro f.
    intro a.
    intro b.
    rewrite a.
    rewrite a.
    rewrite negb_is_involutive.
    reflexivity.
  Qed.
  
  Theorem andb_eq_orb:

    forall x y,
    (andb x y = orb x y) ->
    x = y.
  Proof.
    intros x y.
    destruct x eqn:E.
    - simpl.
      + intro a. rewrite a. reflexivity.
    - simpl.
      + intro a. rewrite a. reflexivity.
  Qed.
End NatPlayground.

Module LateDays.
  Inductive letter: Type := A | B | C | D | F.
  Inductive modifier: Type := Plus | Natural | Minus.

  Inductive grade: Type := Grade (l: letter) (m: modifier).

  Inductive comparison: Type := Eq | Lt | Gt.

  Definition letter_comparison (l1 l2 : letter) : comparison :=
  match l1, l2 with
  | A, A => Eq
  | A, _ => Gt
  | B, A => Lt
  | B, B => Eq
  | B, _ => Gt
  | C, (A | B) => Lt
  | C, C => Eq
  | C, _ => Gt
  | D, (A | B | C) => Lt
  | D, D => Eq
  | D, _ => Gt
  | F, (A | B | C | D) => Lt
  | F, F => Eq
  end.

  Theorem letter_comparison_eq:
    forall l, letter_comparison l l = Eq.
  Proof.
    intros l.
    destruct l eqn:E.
    - reflexivity.
    - reflexivity.
    - reflexivity.
    - reflexivity.
    - reflexivity.
  Qed.

  Definition modifier_comparison (m₀ m₁ : modifier) : comparison :=
    match m₀, m₁ with
    | Plus, Plus => Eq
    | Plus, _ => Gt
    | Natural, Plus => Lt
    | Natural, Natural => Eq
    | Natural, _ => Gt
    | Minus, (Plus | Natural) => Lt
    | Minus, Minus => Eq
  end.

  Definition grade_comparison (g₀ g₁ : grade) :=
    match g₀, g₁ with
    | Grade l₀ m₀, Grade l₁ m₁ =>
      match letter_comparison l₀ l₁ with
      | Eq => modifier_comparison m₀ m₁
      | r => r
      end
  end.

  Example test_grade_comparison1 :
    (grade_comparison (Grade A Minus) (Grade B Plus)) = Gt.
  Proof.
    reflexivity.
  Qed.

  Example test_grade_comparison2 :
    (grade_comparison (Grade A Minus) (Grade A Plus)) = Lt.
  Proof.
    reflexivity.
  Qed.
  
  Example test_grade_comparison3 :
    (grade_comparison (Grade F Plus) (Grade F Plus)) = Eq.
  Proof.
    reflexivity.
  Qed.

  Example test_grade_comparison4 :
    (grade_comparison (Grade B Minus) (Grade C Plus)) = Gt.
  Proof.
    reflexivity.
  Qed.
  
  Definition lower_letter (l : letter) : letter :=
    match l with
    | A => B
    | B => C
    | C => D
    | D => F
    | F => F (* Can't go lower than F! *)
  end.

  Theorem lower_letter_lowers:
    forall (l : letter),
    letter_comparison F l = Lt ->
    letter_comparison (lower_letter l) l = Lt.
  Proof.
    intro l.
    intro a.
    destruct l eqn:E.
    - reflexivity. 
    - reflexivity.
    - reflexivity.
    - reflexivity.
    - rewrite <- a. reflexivity.
  Qed.
  
  Definition lower_grade (g : grade) : grade :=
    match g with
    | Grade F Minus => Grade F Minus
    | Grade l Minus => Grade (lower_letter l) Plus
    | Grade l Plus => Grade l Natural
    | Grade l Natural => Grade l Minus
  end.
  
  Example lower_grade_A_Plus :
    lower_grade (Grade A Plus) = (Grade A Natural).
  Proof.
    reflexivity.
  Qed.
  
  Example lower_grade_A_Natural :
    lower_grade (Grade A Natural) = (Grade A Minus).
  Proof. reflexivity. Qed.
 
  Example lower_grade_A_Minus :
    lower_grade (Grade A Minus) = (Grade B Plus).
  Proof. reflexivity. Qed.
 
  Example lower_grade_B_Plus :
    lower_grade (Grade B Plus) = (Grade B Natural).
  Proof. reflexivity. Qed.
  
  Example lower_grade_F_Natural :
    lower_grade (Grade F Natural) = (Grade F Minus).
  Proof. reflexivity. Qed.
 
  Example lower_grade_twice :
    lower_grade (lower_grade (Grade B Minus)) = (Grade C Natural).
  Proof. reflexivity. Qed.

  Example lower_grade_thrice :
    lower_grade (lower_grade (lower_grade (Grade B Minus))) = (Grade C Minus).
  Proof. reflexivity. Qed.
  
  Theorem lower_grade_F_Minus : 
    lower_grade (Grade F Minus) = (Grade F Minus).
  Proof. reflexivity. Qed.
  
  Theorem lower_grade_lowers :
    forall (g : grade),
    grade_comparison (Grade F Minus) g = Lt ->
    grade_comparison (lower_grade g) g = Lt.
  Proof.
    intros g.
    intros a.
    rewrite <-a.
    destruct g,l,m eqn:E.
    - reflexivity.
    - reflexivity.
    - reflexivity.
    - reflexivity.
    - reflexivity.
    - reflexivity.
    - reflexivity.
    - reflexivity.
    - reflexivity.
    - reflexivity.
    - reflexivity.
    - reflexivity.
    - reflexivity.
    - reflexivity.
    - reflexivity.
  Qed.
  
  Import NatPlayground.
  Definition seventeen := twelve + five.
  Definition twentyone := seventeen + four.
  
  Definition apply_late_policy (late_days : nat) (g : grade) : grade :=
    if late_days <? nine then g
    else if late_days <? seventeen then lower_grade g
    else if late_days <? twentyone then lower_grade (lower_grade g)
    else lower_grade (lower_grade (lower_grade g)).
  
  Theorem apply_late_policy_unfold :
    forall (late_days : nat) (g : grade),
    (apply_late_policy late_days g)
    =
    if late_days <? nine then g
    else if late_days <? seventeen then lower_grade g
    else if late_days <? twentyone then lower_grade (lower_grade g)
    else lower_grade (lower_grade (lower_grade g)).
   Proof.
    intros. reflexivity.
  Qed.

  Theorem no_penalty_for_mostly_on_time :
    forall (late_days : nat) (g : grade),
    (late_days <? nine = true) ->
    apply_late_policy late_days g = g.
  Proof.
    intros late_days g.
    intro a.
    rewrite apply_late_policy_unfold.
    rewrite a.
    reflexivity.
  Qed.
End LateDays.
