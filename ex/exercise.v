Module NatPlayground.
Inductive nat:Type:=
  | O
  | S(n:nat).
End NatPlayground.

Definition pre (n:nat):nat:=
  match n with
  |O=>O
  |S n'=>n'
  end.

Compute(pre 4).