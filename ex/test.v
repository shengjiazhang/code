Require Import Coq.Logic.Classical_Prop.
Module Type test.
Inductive day : Type := 
| monday : day 
| tuesday : day 
| wednesday : day 
| thursday : day 
| friday : day 
| saturday : day 
| sunday : day. 
 
Definition next_weekday (d:day) : day := 
match d with 
| monday => tuesday
| tuesday => wednesday
| wednesday => thursday
| thursday => friday
| friday => monday
| saturday => monday
| sunday => monday
end.
 
Eval compute in (next_weekday friday). 
Eval compute in (next_weekday (next_weekday saturday)).

Lemma notnot : forall P : Prop, ~~P -> P.
Proof.
  unfold not.
  intros P H.
  destruct (classic P) as [HP | HnP].
  - assumption.
  - exfalso. apply H. assumption.
Qed.

Check classic.
End  test.


