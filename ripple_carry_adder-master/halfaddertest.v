Require Import Arith.
Require Import String.
Require Import Arith.
Require Import Lia.
Require Import List.
Require Import Ascii String.
Import ListNotations.
Local Open Scope string_scope.

Inductive Signal : Set :=
  | Bit1  : Signal
  | Bit0  : Signal
  | Bitv  : string -> Signal
  | And2  : Signal -> Signal -> Signal
  | Or2   : Signal -> Signal -> Signal
  | Xor2  : Signal -> Signal -> Signal
  | Nand2 : Signal -> Signal -> Signal
  | Nor2  : Signal -> Signal -> Signal
  | Not1  : Signal -> Signal
  | Letb  : string -> Signal -> Signal -> Signal
with Signal_Pair : Set :=
  | Spair : Signal -> Signal -> Signal_Pair
  | Letb2 : string -> Signal -> Signal_Pair -> Signal_Pair.