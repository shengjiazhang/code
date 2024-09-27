Inductive bool : Type :=
| true
| false.

Definition andb (b1:bool) (b2:bool) : bool := 
match b1 with
| true => b2
| false => false
end.

(*if-else表达式*)
Definition andb' (b1:bool) (b2:bool) : bool :=  
if b1 then b2
else false.


Notation "x && y" := (andb x y).

Compute true && false.

Compute andb(true)(false).

Check true.

Check andb.
(*andb
     : bool -> bool -> bool*)

