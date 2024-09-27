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
| friday => saturday
| saturday => sunday
| sunday => monday
end.

Compute (next_weekday monday).

Theorem next_weekday_test : 
(next_weekday(next_weekday monday)) = wednesday.
Proof.
simpl.
reflexivity.
Qed.

