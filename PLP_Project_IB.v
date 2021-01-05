(* Nu am reusit sa implementez mare lucru din cauza timpului.
   Tot ce am lucrat la proiect a fost facut cu o seara in urma. 
   Pana saptamana viitoare voi face mult mai mult din proiect *)

Include Nat.
Require Import Omega.
Set Nested Proofs Allowed.
Local Open Scope list_scope.
Open Scope list_scope.
Require Import Strings.String.
Local Open Scope string_scope.
Scheme Equality for string.


Definition Env := string -> Type.
Definition Natenv := string -> nat.
Definition Boolenv := string -> bool.

Definition updatenat (env : Natenv) (x : string) (v : nat) : Natenv :=
  fun y =>
    if (string_beq y x)
    then v
    else (env y).

Definition updatebool (env : Boolenv) (x : string) (v : bool) : Boolenv :=
  fun y =>
    if (string_beq y x)
    then v
    else (env y).

Definition Env0 : Natenv := fun _ => 0.

Definition Envfalse : Boolenv := fun _ => false.

Definition Envtest := updatenat Env0 "x" 7.

Definition Envtest2 := updatebool Envfalse "x" true.

Compute Env0 "x".
Compute Envfalse "x".
Compute Envtest "x".
Compute Envtest2 "x".

Inductive ErrorNat :=
  | error_nat : ErrorNat
  | num : nat -> ErrorNat.

Inductive ErrorBool :=
  | error_bool : ErrorBool
  | boolean : bool -> ErrorBool.

Coercion num: nat >-> ErrorNat.
Coercion boolean: bool >-> ErrorBool.

Inductive AExp :=
| aplus : AExp -> AExp -> AExp
| aint : ErrorNat -> AExp
| avar : string -> AExp
| amul : AExp -> AExp -> AExp
| adiv : AExp -> AExp -> AExp
| amod : AExp -> AExp -> AExp.

Inductive FnctieAExp :=
| amin: AExp -> AExp -> FnctieAExp
| amax: AExp -> AExp -> FnctieAExp
| apow: AExp -> AExp -> FnctieAExp.


Inductive BExp :=
| bequal : AExp -> AExp -> BExp
| btrue : BExp
| bfalse : BExp
| bnot : BExp -> BExp
| band : BExp -> BExp -> BExp
| blessthan : AExp -> AExp -> BExp
| bmorethan : AExp -> AExp -> BExp.


Coercion aint : ErrorNat >-> AExp.
Coercion avar : string >-> AExp.

Inductive Vector :=
| vector_decl : string -> AExp -> Vector
| vector_assign : string -> AExp -> Vector.


Reserved Notation "B ={ S }=> B'" (at level 70).

Notation " A ==' B" := (bequal A B) (at level 30).
Notation "A <' B" := (blessthan A B) (at level 70).
Notation "A >' B" := (blessthan B A) (at level 70).
Notation "! A" := (bnot A) (at level 65).
Infix "and'" := band (at level 60).
Notation "!' A <' B" := (bnot (blessthan A B)) (at level 68).


Notation "A +' B" := (aplus A B) (at level 70, right associativity).
Notation "A -' B" := (amin A B) (at level 70, right associativity).
Notation "A *' B" := (amul A B) (at level 50, left associativity).
Notation "A /' B" := (adiv A B) (at level 50, left associativity).
Notation "A %' B" := (amod A B) (at level 40, no associativity).
Notation "A >>= B" := (bmorethan A B) (at level 50).
Notation "A <<= B" := (blessthan A B) (at level 50).


Check btrue.
Check bfalse.
Check bnot.
Check band.
Check blessthan.
Check bmorethan.
Check aplus.
Check amin.
Check amax.
Check apow.
Check aint.
Check avar.
Check amul.
Check adiv.
Check amod.


Inductive Stmt :=
| assignment : string -> AExp -> Stmt
| while : BExp -> Stmt -> Stmt
| sequence : Stmt -> Stmt -> Stmt
| ifthen : BExp -> Stmt -> Stmt
| break : Stmt
| continue : Stmt 
| ifthenelse : BExp -> Stmt -> Stmt -> Stmt
| fordo : Stmt ->BExp -> Stmt -> Stmt -> Stmt
| adecnull : string -> Stmt
| switch : BExp -> Stmt -> Stmt -> Stmt
| adec : string -> AExp -> Stmt.


Notation "A ::= B" := (assignment A B) (at level 87).
Notation "S1 ;; S2" := (sequence S1 S2) (at level 90).
Notation "'While' '(' A ')' '(' B ')'" := (while A B) (at level 98).
Notation "If; A Then; B Else; C" := (ifthenelse A B C) (at level 97).
Notation "{ A , B }" := (pair A B) (at level 30).
Notation "'If' A 'Then' B 'Else' C" := (ifthenelse A B C) (at level 90).
Notation "'For' '(' A ; B ; C ')' '(' D ')'" := (fordo A B C D) (at level 90).
Notation "Break!" := (break) (at level 50).
Notation "Continue!" := (continue) (at level 50).
Notation "'declare*' A" := (adecnull A) (at level 50).
Notation "'decl' A =' B" := (adec A B) (at level 50).
Notation " A 'MaX' B " := (amax A B) (at level 60).
Notation "A 'MiN' B" := (amin A B) (at level 60).
Notation "A 'PoW' B" := (apow A B) (at level 60).
Notation "'switch' '(' A ')' '(' 'first_case' B 'second_case' C ')'" := (switch A B C)(at level 90).

Check break.
Check continue.
Check (declare* "n").
Check (decl "n" =' 4).
Check 1 MaX 2.
Check 1 MiN 2.
Check 1 PoW 2. 


Definition break_pgm := 
     decl "n" =' 0 ;;
     decl "numar" =' 5 ;;
     decl "x" =' 0 ;;
     While ("n" <' 12)
         (
           "x" ::= ("x" +' "n") ;;
           "n" ::= ("n" +' "numar") ;;
           break
         ).

Check break_pgm.

Definition continue_pgm :=
   decl "i" =' 0;;
   For( "i" ::= 0 ; "i" <' 7 ; "i" ::= ("i" +' 1))
   (
If ( "i" ==' 3)
    Then "x" ::= 1
Else
    "x" ::= 0
);;
continue.

Check continue_pgm.



Definition switch_pgm :=
    
    decl "i" =' 0;;
    decl "n" =' 0 ;;
   switch ("i" ==' 6) 
        ( first_case
           "sum" ::= "i" +' 2 
        second_case 
           "sum" ::= "i" +' 1 ;;
      "i"::="i" +' 1
     ).
Check switch_pgm.







 


 


