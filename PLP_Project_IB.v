Include Nat.
Require Import Omega.
Set Nested Proofs Allowed.
Local Open Scope list_scope.
Open Scope list_scope.
Require Import Strings.String.
Local Open Scope string_scope.
Scheme Equality for string.

Inductive ErrorNat :=
  | error_nat : ErrorNat
  | num : nat -> ErrorNat.

Coercion num: nat >-> ErrorNat.


Inductive ErrorBool :=
  | error_bool : ErrorBool
  | boolean : bool -> ErrorBool.

Coercion boolean: bool >-> ErrorBool.

(* Tipuri de rezultate *)
Inductive Results :=
| err_undecl : Results
| err_assign : Results
| rint : ErrorNat -> Results
| rbool : ErrorBool -> Results
| Default : Results.
Scheme Equality for Results.

Coercion rint: ErrorNat >-> Results.
Coercion rbool: ErrorBool >-> Results.

Definition eqb_string (x y : string) : bool :=
if string_beq x y 
then true
else false.

Definition Env := string -> Results.

Definition update (env : Env) (x : string) (v : Results) : Env :=
  fun y =>
    if (eqb_string y x)
    then v
    else (env y).

Definition Env0 : Env := fun _ => 0.

Definition Envfalse : Env := fun _ => false.

Definition Envtest := update Env0 "x" 7.

Definition Envtest2 := update Envfalse "x" true.

Compute Env0 "x".
Compute Envfalse "x".
Compute Envtest "x".
Compute Envtest2 "x".


Inductive AExp :=
| aplus : AExp -> AExp -> AExp
| amin : AExp -> AExp -> AExp
| aint : ErrorNat -> AExp
| avar : string -> AExp
| amul : AExp -> AExp -> AExp
| adiv : AExp -> AExp -> AExp
| amod : AExp -> AExp -> AExp.

Inductive FnctieGenerala :=
| aminim: AExp -> AExp -> FnctieGenerala
| amax: AExp -> AExp -> FnctieGenerala
| apow: AExp -> AExp -> FnctieGenerala.


Inductive BExp :=
| bequal : AExp -> AExp -> BExp
| btrue : BExp
| bfalse : BExp
| bnot : BExp -> BExp
| band : BExp -> BExp -> BExp
| bor : BExp -> BExp -> BExp
| blessthan : AExp -> AExp -> BExp
| bmorethan : AExp -> AExp -> BExp.


Coercion aint : ErrorNat >-> AExp.
Coercion avar : string >-> AExp.

Inductive Vector :=
| vector_decl : string -> AExp -> Vector
| vector_assign : string -> AExp -> Vector.

Notation " A ==' B" := (bequal A B) (at level 30).
Notation "A <' B" := (blessthan A B) (at level 70).
Notation "A >' B" := (bmorethan B A) (at level 70).
Notation "! A" := (bnot A) (at level 65).
Infix "and'" := band (at level 60).
Notation "!' A <' B" := (bnot (blessthan A B)) (at level 68).


Notation "A +' B" := (aplus A B) (at level 70, right associativity).
Notation "A -' B" := (amin A B) (at level 70, right associativity).
Notation "A *' B" := (amul A B) (at level 50, left associativity).
Notation "A /' B" := (adiv A B) (at level 50, left associativity).
Notation "A %' B" := (amod A B) (at level 40, no associativity).


Check btrue.
Check bfalse.
Check bnot.
Check band.
Check blessthan.
Check bmorethan.
Check aplus.
Check aminim.
Check amax.
Check apow.
Check aint.
Check avar.
Check amul.
Check adiv.
Check amod.


(* Definitii AExp *)
Definition plus_err (n1 n2 : ErrorNat) : ErrorNat :=
  match n1, n2 with
    | error_nat, _ => error_nat
    | _, error_nat => error_nat
    | num v1, num v2 => num (v1 + v2)
    end.
Compute plus_err error_nat 2.
Compute plus_err 1 2.


Definition minus_err (n1 n2 : ErrorNat) : ErrorNat :=
  match n1, n2 with
    | error_nat, _ => error_nat
    | _, error_nat => error_nat
    | num v1, num v2 => num (v1 + v2)
    end.
Compute minus_err 3 error_nat .
Compute minus_err 3 1.


Definition mul_err (n1 n2 : ErrorNat) : ErrorNat :=
  match n1, n2 with
    | error_nat, _ => error_nat
    | _, error_nat => error_nat
    | num v1, num v2 => num (v1 * v2)
    end.
Compute mul_err 4 3.


Definition div_err (n1 n2 : ErrorNat) : ErrorNat :=
  match n1, n2 with
    | error_nat, _ => error_nat
    | _, error_nat => error_nat
    | _, num 0 => error_nat
    | num v1, num v2 => num (div v1 v2)
    end.
Compute div_err 5 0.


Definition mod_err (n1 n2 : ErrorNat) : ErrorNat :=
  match n1, n2 with
    | error_nat, _ => error_nat
    | _, error_nat => error_nat
    | _, num 0 => error_nat
    | num v1, num v2 => num (modulo v1 v2)
    end.
Compute mod_err 4 0.
Compute mod_err 35 2.


(* Definitii BExp *)
Definition eq_err (n1 n2 : ErrorNat) : ErrorBool :=
  match n1, n2 with
    | error_nat, _ => error_bool
    | _, error_nat => error_bool
    | num v1, num v2 => boolean (Nat.eqb v1 v2)
    end.
Check eq_err 2 2.


Definition lt_err (n1 n2 : ErrorNat) : ErrorBool :=
  match n1, n2 with
    | error_nat, _ => error_bool
    | _, error_nat => error_bool
    | num v1, num v2 => boolean (ltb v1 v2)
    end.
Check lt_err 5 2.


Definition le_err (n1 n2 : ErrorNat) : ErrorBool :=
  match n1, n2 with
    | error_nat, _ => error_bool
    | _, error_nat => error_bool
    | num v1, num v2 => boolean (leb v1 v2)
    end.
Check le_err 1 1.


Definition gt_err (n1 n2 : ErrorNat) : ErrorBool :=
  match n1, n2 with
    | error_nat, _ => error_bool
    | _, error_nat => error_bool
    | num v1, num v2 => boolean (negb (leb v1 v2))
    end.
Check gt_err 5 2.

Definition ge_err (n1 n2 : ErrorNat) : ErrorBool :=
  match n1, n2 with
    | error_nat, _ => error_bool
    | _, error_nat => error_bool
    | num v1, num v2 => boolean (negb (ltb v1 v2))
    end.
Check gt_err 6 6.


Definition not_err (n : ErrorBool) : ErrorBool :=
  match n with
    | error_bool  => error_bool
    | boolean v => boolean (negb v)
    end.
Check not_err true.

Definition and_err (n1 n2 : ErrorBool) : ErrorBool :=
  match n1, n2 with
    | error_bool, _ => error_bool
    | _, error_bool => error_bool
    | boolean v1, boolean v2 => boolean (andb v1 v2)
    end.
Check and_err true false.


Definition or_err (n1 n2 : ErrorBool) : ErrorBool :=
  match n1, n2 with
    | error_bool, _ => error_bool
    | _, error_bool => error_bool
    | boolean v1, boolean v2 => boolean (orb v1 v2)
    end.
Check or_err true false.


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
| switch : string -> list Cases -> Stmt
| adec : string -> AExp -> Stmt
with Cases:=
| default: Stmt -> Cases
| Case: AExp -> Stmt -> Cases.


Notation "A ::= B" := (assignment A B) (at level 87).
Notation "S1 ;; S2" := (sequence S1 S2) (at level 90).
Notation "'While' '(' A ')' '(' B ')'" := (while A B) (at level 98).
Notation "If; A Then; B Else; C" := (ifthenelse A B C) (at level 97).
Notation "{ A , B }" := (pair A B) (at level 30).
Notation "'If' A 'Then' B 'Else' C" := (ifthenelse A B C) (at level 90).
Notation "'For' '(' A ; B ; C ')' '{(' D ')}'" := (fordo A B C D) (at level 90).
Notation "Break!" := (break) (at level 50).
Notation "Continue!" := (continue) (at level 50).
Notation "'declare*' A" := (adecnull A) (at level 50).
Notation "'decl' A =' B" := (adec A B) (at level 50).
Notation " A 'MaX' B " := (amax A B) (at level 60).
Notation "A 'MiN' B" := (aminim A B) (at level 60).
Notation "A 'PoW' B" := (apow A B) (at level 60).
Notation "'default' ':->' S" := (default S) (at level 40).
Notation "'case' E ':->' S" := (Case E S) (at level 40).
Notation "'Switch' '[(' E ')]' '{{' C1 ';/' .. ';/' C2 '}}'" := (switch E (cons C1 .. (cons C2 nil) .. )) (at level 40).

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
   For( "i" ::= 0 ; "i" <' 7 ; "i" ::= ("i" +' 1) )
   {(
If ( "i" ==' 3)
    Then "x" ::= 1
Else
    "x" ::= 0
)};;
continue.

Check continue_pgm.


(* Primul switch care nu este extrem de bun
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
*)

(* Testez noul switch: *)

Definition switch_pgm :=
    
    decl "i" =' 5;;
    decl "sum" =' 0 ;;
   Switch [( "i" )]
        {{ case 1 :-> (
           "sum" ::= "i" +' 3 ) ;/
        	 case 2 :-> (
           "sum" ::= "i" +' 1 ) ;/
      		 case 5 :-> (
           "sum" ::= "i" +' 7 ) ;/
           default :-> (
           "sum" ::= "i" +' 10 )
        }}
     .
Check switch_pgm.

Definition plus_ErrorNat (n1 n2 : ErrorNat) : ErrorNat :=
  match n1, n2 with
    | error_nat, _ => error_nat
    | _, error_nat => error_nat
    | num v1, num v2 => num (v1 + v2)
    end.

Compute plus_ErrorNat 3 4.
Compute plus_ErrorNat 3 error_nat.

Definition sub_ErrorNat (n1 n2 : ErrorNat) : ErrorNat :=
  match n1, n2 with
    | error_nat, _ => error_nat
    | _, error_nat => error_nat
    | num n1, num n2 => if Nat.ltb n1 n2
                        then error_nat
                        else num (n1 - n2)
    end.

Compute sub_ErrorNat 5 2.
Compute sub_ErrorNat 3 error_nat.


Definition mul_ErrorNat (n1 n2 : ErrorNat) : ErrorNat :=
  match n1, n2 with
    | error_nat, _ => error_nat
    | _, error_nat => error_nat
    | num v1, num v2 => num (v1 * v2)
    end.

Compute mul_ErrorNat 2 2.
Compute mul_ErrorNat 4 error_nat.

Definition div_ErrorNat (n1 n2 : ErrorNat) : ErrorNat :=
  match n1, n2 with
    | error_nat, _ => error_nat
    | _, error_nat => error_nat
    | _, num 0 => error_nat
    | num v1, num v2 => num (Nat.div v1 v2)
    end.

Compute div_ErrorNat 9 3.
Compute div_ErrorNat 3 error_nat.

Definition mod_ErrorNat (n1 n2 : ErrorNat) : ErrorNat :=
  match n1, n2 with
    | error_nat, _ => error_nat
    | _, error_nat => error_nat
    | _, num 0 => error_nat
    | num v1, num v2 => num (v1 - v2 * (Nat.div v1 v2))
    end.

Compute mod_ErrorNat 8 2.
Compute mod_ErrorNat 0 error_nat.

Definition lt_ErrorBool (n1 n2 : ErrorNat) : ErrorBool :=
  match n1, n2 with
    | error_nat, _ => error_bool
    | _, error_nat => error_bool
    | num v1, num v2 => boolean (Nat.ltb v1 v2)
    end.

Compute lt_ErrorBool 5 1.
Compute lt_ErrorBool 5 error_nat.

Definition gt_ErrorBool (n1 n2 : ErrorNat) : ErrorBool :=
  match n1, n2 with
    | error_nat, _ => error_bool
    | _, error_nat => error_bool
    | num v1, num v2 => boolean (negb (Nat.leb v1 v2))
    end.

Compute gt_ErrorBool 0 5.
Compute gt_ErrorBool 5 error_nat.

Definition not_ErrorBool (n :ErrorBool) : ErrorBool :=
  match n with
    | error_bool => error_bool
    | boolean v => boolean (negb v)
    end.

Compute gt_ErrorBool 0.

Definition and_ErrorBool (n1 n2 : ErrorBool) : ErrorBool :=
  match n1, n2 with
    | error_bool, _ => error_bool
    | _, error_bool => error_bool
    | boolean v1, boolean v2 => boolean (andb v1 v2)
    end.

Compute and_ErrorBool.

Definition or_ErrorBool (n1 n2 : ErrorBool) : ErrorBool :=
  match n1, n2 with
    | error_bool, _ => error_bool
    | _, error_bool => error_bool
    | boolean v1, boolean v2 => boolean (orb v1 v2)
    end.

Compute or_ErrorBool.

Definition eq_ErrorBool (n1 n2 : ErrorNat) : ErrorBool :=
  match n1, n2 with
    | error_nat, _ => error_bool
    | _, error_nat => error_bool
    | num v1, num v2 => Nat.eqb v1 v2
    end.

Compute eq_ErrorBool.

Reserved Notation "A =[ S ]=> N" (at level 60).
Inductive aeval : AExp -> Env -> ErrorNat -> Prop :=
| const : forall n sigma, aint n =[ sigma ]=> n
| var : forall v sigma, avar v =[ sigma ]=> match sigma v with
																						| num n => n
																						| _ => error_nat
																						end
| add' : forall a1 a2 i1 i2 sigma n,
    a1 =[ sigma ]=> i1 ->
    a2 =[ sigma ]=> i2 ->
    n = plus_ErrorNat i1 i2 ->
    (a1 +' a2) =[ sigma ]=> n
| sub' : forall a1 a2 i1 i2 sigma n,
    a1 =[ sigma ]=> i1 ->
    a2 =[ sigma ]=> i2 ->
    n = sub_ErrorNat i1 i2 ->
    (a1 -' a2) =[ sigma ]=> n
| mul' : forall a1 a2 i1 i2 sigma n,
    a1 =[ sigma ]=> i1 ->
    a2 =[ sigma ]=> i2 ->
    n = mul_ErrorNat i1 i2 ->
    a1 *' a2 =[sigma]=> n
| div' : forall a1 a2 i1 i2 sigma n,
    a1 =[ sigma ]=> i1 ->
    a2 =[ sigma ]=> i2 ->
    n = div_ErrorNat i1 i2 ->
    a1 /' a2 =[ sigma ]=> n
| mod' : forall a1 a2 i1 i2 sigma n,
    a1 =[ sigma ]=> i1 ->
    a2 =[ sigma ]=> i2 ->
    n = mod_ErrorNat i1 i2 ->
    a1 %' a2 =[ sigma ]=> n
where "a =[ sigma ]=> n" := (aeval a sigma n).

Reserved Notation "B ={ S }=> B'" (at level 70).
Inductive beval : BExp -> Env -> ErrorBool -> Prop :=
| e_true : forall sigma, btrue ={ sigma }=> true
| e_false : forall sigma, bfalse ={ sigma }=> false
| e_lessthan : forall a1 a2 i1 i2 sigma b,
    a1 =[ sigma ]=> i1 ->
    a2 =[ sigma ]=> i2 ->
    b = lt_ErrorBool i1 i2 ->
    a1 <' a2 ={ sigma }=> b
| e_greaterthan : forall a1 a2 i1 i2 sigma b,
    a1 =[ sigma ]=> i1 ->
    a2 =[ sigma ]=> i2 ->
    b = gt_ErrorBool i1 i2 ->
    a1 >' a2 ={ sigma }=> b
| e_equal : forall a1 a2 i1 i2 sigma b,
    a1 =[ sigma ]=> i1 ->
    a2 =[ sigma ]=> i2 ->
    b = eq_ErrorBool i1 i2 ->
    a1 ==' a2 ={ sigma }=> b
| e_nottrue : forall b sigma,
    b ={ sigma }=> true ->
    (bnot b) ={ sigma }=> false
| e_notfalse : forall b sigma,
    b ={ sigma }=> false ->
    (bnot b) ={ sigma }=> true
| e_andtrue : forall b1 b2 sigma t,
    b1 ={ sigma }=> true ->
    b2 ={ sigma }=> t ->
    band b1 b2 ={ sigma }=> t
| e_andfalse : forall b1 b2 sigma,
    b1 ={ sigma }=> false ->
    band b1 b2 ={ sigma }=> false
| e_ortrue : forall b1 b2 sigma,
    b1 ={ sigma }=> true ->
    bor b1 b2 ={ sigma }=> true
| e_orfalse : forall b1 b2 sigma t,
    b1 ={ sigma }=> true ->
    b2 ={ sigma }=> t ->
    bor b1 b2 ={ sigma }=> t
where "B ={ S }=> B'" := (beval B S B').


Example substract_error : (1 -' 5) =[ Env0 ]=> error_nat.
Proof.
  eapply sub'.
  - apply const.
  - apply const.
  - simpl. reflexivity.
Qed.

Example division_error : (3 /' 0) =[ Env0 ]=> error_nat.
Proof.
  eapply div'.
  - apply const.
  - apply const.
  - simpl. reflexivity.
Qed.

Example modulo_error : (3 %' 0) =[ Env0 ]=> error_nat.
Proof.
  eapply mod'.
  - apply const.
  - apply const.
  - simpl. reflexivity.
Qed.

Reserved Notation "B -{ S }-> B'" (at level 70).
Inductive eval : Stmt -> Env -> Env -> Prop :=
| e_nat_decl: forall a i x sigma sigma',
   a =[ sigma ]=> i ->
   sigma' = (update sigma x i) ->
   (x ::= a) -{ sigma }-> sigma'
| e_nat_assign: forall a i x sigma sigma',
    a =[ sigma ]=> i ->
    sigma' = (update sigma x i) ->
    (x ::= a) -{ sigma }-> sigma'
| e_seq : forall s1 s2 sigma sigma1 sigma2,
    s1 -{ sigma }-> sigma1 ->
    s2 -{ sigma1 }-> sigma2 ->
    (s1 ;; s2) -{ sigma }-> sigma2
| e_if_then : forall b s sigma,
    ifthen b s -{ sigma }-> sigma
| e_if_then_elsetrue : forall b s1 s2 sigma sigma',
    b ={ sigma }=> true ->
    s1 -{ sigma }-> sigma' ->
    ifthenelse b s1 s2 -{ sigma }-> sigma' 
| e_if_then_elsefalse : forall b s1 s2 sigma sigma',
    b ={ sigma }=> false ->
    s2 -{ sigma }-> sigma' ->
    ifthenelse b s1 s2 -{ sigma }-> sigma' 
| e_whilefalse : forall b s sigma,
    b ={ sigma }=> false ->
    while b s -{ sigma }-> sigma
| e_whiletrue : forall b s sigma sigma',
    b ={ sigma }=> true ->
    (s ;; while b s) -{ sigma }-> sigma' ->
    while b s -{ sigma }-> sigma'
where "s -{ sigma }-> sigma'" := (eval s sigma sigma').
 


