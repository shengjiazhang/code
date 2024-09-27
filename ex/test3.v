Inductive rgb : Type :=
  | red
  | green
  | blue .

Inductive color : Type :=
  | black
  | white
  | primary(p:rgb).

Definition isRed(c:color) : bool := 
match c with
|black=>false
|white=>false
|primary red=>true
|primary _=>false
end.

Compute isRed(primary red).
(*这里的模式 primary _ 是“构造子 primary 应用到除 red 之外的任何 rgb 构造子上”的简写形式*)
(*     = true
     : bool*)

Check primary.

Theorem test_proof:(isRed(black))=false.
Proof.
simpl.
reqf
Qed.
