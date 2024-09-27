(*我们首先定义一个 bit 数据类型 来类比 bool 数据。并且使用 B0 和 B1 两种构造子来表示其可能的取值*)
Inductive bit : Type := 
|B0
|B1.

(*最后定义 nybble 这种数据类型，也就是一个四比特的元组*)
Inductive nubble : Type :=
|bits(b1 b2 b3 b4 : bit).

Check (bits B1 B1 B1 B1).
(* bits B1 B1 B1 B1
     : nubble *)

Definition isAllZero (nb:nubble) : bool := 
match nb with
|(bits B0 B0 B0 B0)=>true
|(bits _ _ _ _)=>false
end.

Compute isAllZero(bits B1 B1 B1 B1).
(* = false
     : bool*)
Compute isAllZero(bits B0 B0 B0 B0).
(* = true
     : bool*)