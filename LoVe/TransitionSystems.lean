import Mathlib
import Aesop

def fact (n : ℕ) : ℕ :=
  match n with
  | 0 => 1
  | Nat.succ n' => fact n' * (Nat.succ n')

inductive fact_state where
| AnswerIs (answer : ℕ)
| WithAccumulator (input accumulator : ℕ)

inductive fact_init (original_input : ℕ) : fact_state → Prop where
| FactInit : fact_init original_input (fact_state.WithAccumulator original_input 1)

inductive fact_final : fact_state -> Prop where
| FactFinal : forall ans, fact_final (fact_state.AnswerIs ans)

/- The most important part: the relation to step between states -/

inductive fact_step : fact_state -> fact_state -> Prop where
| FactDone : forall acc,
  fact_step (fact_state.WithAccumulator 0 acc) (fact_state.AnswerIs acc)
| FactStep : forall n acc,
  fact_step (fact_state.WithAccumulator (Nat.succ n) acc) (fact_state.WithAccumulator n (acc * (Nat.succ n)))

inductive trc {A : Type} (R : A → A → Prop) : A → A → Prop where
| TrcRefl : forall x, trc R x x
| TrcFront : forall x y z,
  R x y
  -> trc R y z
  -> trc R x z

/- Ironically, this definition is not obviously transitive!
  Let's prove transitivity as a lemma -/


theorem trc_trans : forall {A: Type} (R : A → A → Prop) x y,
trc R x y → forall z, (trc R y z → trc R x z) := by
  intro A R x y hxy z hyz
  induction hxy with
  | TrcRefl x1 => assumption
  | TrcFront h x x1 ih h2 h3  =>
    have h4 : trc R x z := h3 hyz
    apply trc.TrcFront h x z ih h4


theorem factorial_3 : trc fact_step (fact_state.WithAccumulator 3 1) (fact_state.AnswerIs 6)
:= by
eapply trc.TrcFront
apply fact_step.FactStep
simp
eapply trc.TrcFront
apply fact_step.FactStep
simp
eapply trc.TrcFront
apply fact_step.FactStep
simp
eapply trc.TrcFront
apply fact_step.FactDone
eapply trc.TrcRefl


theorem factorial_3_new : trc fact_step (fact_state.WithAccumulator 3 1) (fact_state.AnswerIs 6)
:= by
repeat econstructor
