
Require Import Bool.Bvector.
Require Import ZArith.
Require Import QArith.
Require Import ZArith.Znumtheory.
Require Import ZArith.BinInt.
Require Import QArith.Qabs.
Require Import Vectors.Fin.
Require Import Vectors.VectorDef.
Require Import Vectors.VectorSpec.
Require Import Vectors.Vector.

Open Scope nat_scope.

Definition div_eucl_z := BinIntDef.Z.div_eucl.

Fixpoint getAcc (n:nat) : Q :=
match n with
|O => 1#1
|S m => Qmult (1#10) (getAcc m)
end.

(*double*)

Definition lenExp : nat := 11. 
Definition lenSign : nat :=52. 
Definition sqrtEps : Q := getAcc 50.

(*single*)
(*
Definition lenExp : nat := 8. 
Definition lenSign : nat :=23.
(*1e-10*)
Definition sqrtEps : Q := getAcc 25.
*)
Fixpoint getPowerTwo (power : nat) :=
match power with
|O => 1
|S m => 2* (getPowerTwo m)
end.

Fixpoint getMaxExp (lenExp : nat) : nat :=
match lenExp with
|O => O
|S m => let result := getPowerTwo m in
        match result with
        |O => O
        |S n => n
        end
end.

Fixpoint getAllFalseVector (len : nat) : Bvector len :=
match len with
|O => Vector.nil bool
|S m => Vector.cons bool false m (getAllFalseVector m)
end.

Fixpoint getAllTrueVector (len : nat) : Bvector len :=
match len with
|O => Vector.nil bool
|S m => Vector.cons bool true m (getAllTrueVector m)
end.

Fixpoint getNotAllFalseVector (len:nat) : Bvector len :=
match len with
|O => Vector.nil bool
|S m => Vector.cons bool true m (getAllFalseVector m)
end.

Fixpoint getBiasVector (len:nat) : Bvector len :=
match len with
|O => Vector.nil bool
|S m => Vector.cons bool false m (getAllTrueVector m)
end.

Definition shiftExp : nat := getMaxExp lenExp.
Definition maxExp : nat := getMaxExp lenExp.

Definition allTrueExp : Bvector lenExp := getAllTrueVector lenExp.

Definition allFalseExp : Bvector lenExp := getAllFalseVector lenExp.

Definition zeroExp : Bvector lenExp := getBiasVector lenExp.

Definition bias : Bvector lenExp := getBiasVector lenExp.

Definition allFalseSignificant : Bvector lenSign := getAllFalseVector lenSign.


Definition notAllFalseSignificant : Bvector lenSign := 
getNotAllFalseVector lenSign.


Record fp_num : Set := mkFp
{
 sign : bool;
 exp : Bvector lenExp;
 significant : Bvector lenSign
}.



Definition NaN : fp_num := mkFp true allTrueExp notAllFalseSignificant.
Definition plusInfinity : fp_num := mkFp false allTrueExp allFalseSignificant.
Definition minusInfinity : fp_num := mkFp true allTrueExp allFalseSignificant.
Definition plusZero : fp_num := mkFp false allFalseExp allFalseSignificant.
Definition minusZero : fp_num := mkFp true allFalseExp allFalseSignificant.


(* BEGIN *)
(* determine type number *)
Fixpoint isVectAllTrue (n:nat) (v : Bvector n) : bool :=
 match v with 
  | Vector.nil => true
  | Vector.cons h m w => if h then (isVectAllTrue m w) else false
 end.

Fixpoint isVectAllFalse (n:nat) (v : Bvector n) : bool :=
 match v with 
  | Vector.nil => true
  | Vector.cons h m w => if h  then false else (isVectAllFalse m w)
 end.

Fixpoint isExpforZero (v : Bvector lenExp) : bool :=
 isVectAllFalse lenExp v.

Fixpoint isNaN (fp : fp_num) : bool := 
if isVectAllTrue lenExp fp.(exp) then 
  negb (isVectAllFalse lenSign fp.(significant) )
else false.

Fixpoint isInfinite (fp : fp_num) : bool :=
if isVectAllTrue lenExp fp.(exp) then 
  isVectAllFalse lenSign fp.(significant) 
else false.

Fixpoint isFinite (fp : fp_num) : bool := negb (isNaN fp || isInfinite fp).

Fixpoint isZero (fp : fp_num) : bool := 
 (isExpforZero fp.(exp) && isVectAllFalse lenSign fp.(significant)).

(* determine type number *)
(* END *)


(* BEGIN *)
(* compare fp_num *)
Fixpoint compareSys (n:nat) (m:nat) (v1 : Bvector n) (v2 : Bvector m) : comparison :=
match v1 with
  | Vector.nil => Eq
  | Vector.cons h1 m1 w1 => 
  match v2 with
   | Vector.nil => Eq
   | Vector.cons h2 m2 w2 => if eqb h1 h2 then compareSys m1 m2 w1 w2 else if h1 then Gt else Lt
  end
 end.

Fixpoint compareVect (n:nat) (v1 v2 : Bvector n) : comparison := compareSys n n v1 v2.

Fixpoint compareExp (fp1 fp2 : fp_num) : comparison := compareVect lenExp fp1.(exp) fp2.(exp).

Fixpoint compareSignificant (fp1 : fp_num) (fp2 : fp_num) : comparison := 
compareVect lenSign fp1.(significant) fp2.(significant).

Fixpoint compareSign (fp1 fp2 : fp_num) : comparison :=
if eqb fp1.(sign) fp2.(sign) then Eq
else if fp1.(sign) then Lt else Gt.

Fixpoint compareAbs (fp1 fp2 : fp_num) : comparison :=
match compareExp fp1 fp2 with
   | Lt => Lt
   | Gt => Gt
   | Eq => compareSignificant fp1 fp2
end.

Fixpoint compare (fp1 fp2 : fp_num) : comparison :=
match compareSign fp1 fp2 with 
| Lt => Lt
| Gt => Gt
| Eq => match compareExp fp1 fp2 with
   | Lt => Lt
   | Gt => Gt
   | Eq => compareSignificant fp1 fp2
  end
end.

(*<*)
Fixpoint isLt (c:comparison) : bool :=
match c with
|Lt => true
|_ => false
end.

(*==*)
Fixpoint isEq (c:comparison) : bool :=
match c with
|Eq => true
|_ => false
end.

(*>*)
Fixpoint isGt (c:comparison) : bool :=
match c with
|Gt => true
|_ => false
end.

(*<=*)
Fixpoint isLE (c:comparison) : bool :=
match c with
|Gt => false
|_ => true
end.

(*!=*)
Fixpoint isNE (c:comparison) : bool :=
match c with
|Eq => false
|_ => true
end.

(*>=*)
Fixpoint isGE (c:comparison) : bool :=
match c with
|Lt => false
|_ => true
end.

Fixpoint isGeFp_bool (x y :fp_num) : bool := isGE (compare x y).
Fixpoint isNeFp_bool (x y :fp_num) : bool := isNE (compare x y).
Fixpoint isLeFp_bool (x y :fp_num) : bool := isLE (compare x y).
Fixpoint isGtFp_bool (x y :fp_num) : bool := isGt (compare x y).
Fixpoint isLtFp_bool (x y :fp_num) : bool := isLt (compare x y).
Fixpoint isEqFp_bool (x y :fp_num) : bool := isEq (compare x y).

(* compare fp_num *)
(* END *)

(* compare Q*)
(* BEGIN *)
Fixpoint isGeQ_bool (x y :Q) : bool := isGE (Qcompare x y).
Fixpoint isNeQ_bool (x y :Q) : bool := isNE (Qcompare x y).
Fixpoint isLeQ_bool (x y :Q) : bool := isLE (Qcompare x y).
Fixpoint isGtQ_bool (x y :Q) : bool := isGt (Qcompare x y).
Fixpoint isLtQ_bool (x y :Q) : bool := isLt (Qcompare x y).
Fixpoint isEqQ_bool (x y :Q) : bool := isEq (Qcompare x y).
(* compare Q*)
(* END *)

Definition invertV (n : nat) := nat_rect (fun n => Bvector n -> Bvector n) 
(fun v => Bnil)
(fun k x v => Bcons (Vector.last v) _ (x (Vector.shiftout v))).

Definition neg (fp : fp_num) : fp_num := mkFp (negb fp.(sign)) fp.(exp) fp.(significant).

Fixpoint abs (fp:fp_num) : fp_num := mkFp false fp.(exp) fp.(significant).

Definition sumDigits (carry a b : bool) : bool * bool :=
if carry then 
  if a then
   if b then (true,true)
   else (true,false)
  else
   if b then (true,false)
   else (false,true)
else
 if a then 
   if b then (true,false)
   else (false,true)
 else
   if b then (false,true)
   else (false,false).

(* a -(b+carry) *)
Definition diffDigits (carry a b : bool) : bool * bool :=
if carry then
  if b then 
    if a then (true,true)
    else (true,false)
  else 
    if a then (false,false)
    else (true,true)
else
 if b then 
   if a then (false,false)
   else (true,true)
 else
   if a then (false,true)
   else (false,false).

Fixpoint plusBoolInvV (n:nat) (b:bool) (v :Bvector n) : Bvector n :=
if b then
 match v with
  | Vector.nil => []
  | Vector.cons h m w => let res := sumDigits b h false in
     if fst res 
     then Vector.cons bool (snd res) m  (plusBoolInvV m (fst res) w)
     else Vector.cons bool (snd res) m w
 end 
else v.

Fixpoint minusBoolInvV (n:nat) (b:bool) (v :Bvector n) : Bvector n :=
if b then
 match v with
  | Vector.nil => []
  | Vector.cons h m w => let res:=diffDigits b h false in 
     if fst res  
     then Vector.cons bool (snd res) m (minusBoolInvV m (fst res) w)
     else Vector.cons bool (snd res) m w
 end 
else v.

Fixpoint plusBoolV (n:nat) (b:bool) (v :Bvector n) : Bvector n := 
invertV n n (plusBoolInvV n b (invertV n n v)).

Fixpoint minusBoolV (n:nat) (b:bool) (v :Bvector n) : Bvector n := 
invertV n n (minusBoolInvV n b (invertV n n v)).

Fixpoint plusTrueToExp (fp : fp_num) : fp_num :=
mkFp fp.(sign) (plusBoolV lenExp true fp.(exp) ) fp.(significant).

Fixpoint minusTrueFromExp (fp : fp_num) : fp_num :=
mkFp fp.(sign) (minusBoolV lenExp true fp.(exp) ) fp.(significant).

(* remove last shift right add head *)
Definition shiftReplaceR (val : bool) : forall n : nat, (Bvector n -> Bvector n) := 
nat_rect (fun n => (Bvector n -> Bvector n)) 
(fun x => Bnil)
(fun k x w => Bcons val _ (Vector.shiftout w)).

(* remove head shift left add last *)
Definition shiftReplaceL (val : bool) (n:nat) (v : Bvector n) : Bvector n := 
invertV n n (shiftReplaceR val n (invertV n n v)).


Definition shiftSignificantR (val : bool) (fp:fp_num) : fp_num := 
mkFp fp.(sign) fp.(exp) (shiftReplaceR val lenSign fp.(significant)).  

Definition shiftSignificantL (val : bool) (fp:fp_num) : fp_num := 
mkFp fp.(sign) fp.(exp) (shiftReplaceL val lenSign fp.(significant)).  

Fixpoint vect2NatSys (pow :nat) (n:nat) (v:Bvector n) : nat :=
match v with
 |Vector.nil => O
 |Vector.cons h m w => if h then pow + (vect2NatSys (2*pow) m w)%nat else vect2NatSys (2*pow) m w
end.

Fixpoint vect2Nat (n:nat) (v:Bvector n) : nat := vect2NatSys 1 n (invertV n n v).

Fixpoint exp2Nat (fp: fp_num) : nat := vect2Nat lenExp  fp.(exp).

Fixpoint nat2Vect (n len:nat) (v:Bvector len) (minus:bool) :Bvector len :=
match n with 
|O => v
|S m => let newV := if minus then 
                       minusBoolV len true v 
                    else plusBoolV len true v 
        in nat2Vect m len newV minus
end.
 

(* fp1.(exp) < fp2.(exp) *)
Fixpoint difExp (fp1 fp2 : fp_num) : nat :=(exp2Nat fp2 - exp2Nat fp1)%nat.

Fixpoint countZero (n:nat) (v: Bvector n) : nat := 
match v with
|Vector.nil => O
|Vector.cons h m w => if h then O else S (countZero m w)
end.

Fixpoint alignmentExpSys (n:nat) (val:bool) (fp: fp_num) : fp_num :=
match n with
| O => fp
| S m => alignmentExpSys m false (shiftSignificantR val (plusTrueToExp fp))
end.

Fixpoint normalizeFpSys (n:nat) (val:bool) (fp: fp_num) : fp_num :=
match n with
| O => fp
| S m => normalizeFpSys m false (shiftSignificantL val (minusTrueFromExp fp))
end. 

(* fp1.(exp) < fp2.(exp)*)
Fixpoint alignmentExp (fp1 fp2 :fp_num) : fp_num :=
alignmentExpSys (difExp fp1 fp2) true fp1.

Fixpoint normalizeFp (count:nat) (fp : fp_num) : fp_num :=
normalizeFpSys count false fp.

Fixpoint sumVectors (n : nat) := Vector.rect2 (n:=n) (fun n l r => prod bool (Bvector n)) 
(false, [])
(fun n l r prev a b => let (carry, result) := (sumDigits (fst prev) a b) in (carry, result :: (snd prev))).

(* abs fp1 > abs fp2 *)
Fixpoint diffVectors (n : nat) := Vector.rect2 (n:=n) (fun n l r => prod bool (Bvector n)) 
(false, [])
(fun n l r prev a b => let (carry, result) := (diffDigits (fst prev) a b) in (carry, result :: (snd prev))).

(* fp1.(exp) < fp2.(exp) *)
Fixpoint sumOneSignFpSysNotEq (fp1 : fp_num) (fp2 : fp_num) : fp_num :=
let sumRes := sumVectors lenSign (alignmentExp fp1 fp2).(significant) fp2.(significant) in 
if fst sumRes then mkFp fp1.(sign) (plusBoolV lenExp true fp2.(exp) ) (shiftReplaceR false lenSign (snd sumRes)) 
else mkFp fp2.(sign) fp2.(exp) (snd sumRes).

(* fp1.(exp) = fp2.(exp) *)
Fixpoint sumOneSignFpSysEq (fp1 : fp_num) (fp2 : fp_num) : fp_num :=
let sumRes := sumVectors lenSign fp1.(significant) fp2.(significant) in 
if fst sumRes then mkFp fp1.(sign) (plusBoolV lenExp true fp1.(exp) ) (shiftReplaceR true lenSign (snd sumRes)) 
else mkFp fp1.(sign) (plusBoolV lenExp true fp1.(exp) ) (shiftReplaceR false lenSign (snd sumRes)).

Fixpoint sumOneSignFp (fp1 : fp_num) (fp2 : fp_num) : fp_num :=
match compareExp fp1 fp2 with 
|Lt => sumOneSignFpSysNotEq fp1 fp2
|Gt => sumOneSignFpSysNotEq fp2 fp1
|Eq => sumOneSignFpSysEq fp2 fp1
end.

(* abs fp1 > abs fp2 *)
Fixpoint diffNotEqExpFp (fp1 : fp_num) (fp2 : fp_num) : fp_num :=
let res := diffVectors lenSign fp1.(significant) (alignmentExp fp2 fp1).(significant)  in 
if fst res then normalizeFp (S (countZero lenSign (snd res))) (mkFp fp1.(sign) fp1.(exp) (snd res))
else normalizeFp (countZero lenSign (snd res)) (mkFp fp1.(sign) fp1.(exp) (snd res)).

(* abs fp1 > abs fp2 *)
Fixpoint diffEqExpFp (fp1 : fp_num) (fp2 : fp_num) : fp_num :=
let res := diffVectors lenSign  fp1.(significant) fp2.(significant) in 
normalizeFp (S (countZero lenSign (snd res))) (mkFp fp1.(sign) fp1.(exp) (snd res)).

(* abs fp1 > abs fp2 *)
Fixpoint diffFpSys (fp1 : fp_num) (fp2 : fp_num) : fp_num :=
match compareExp fp1 fp2 with 
|Lt =>  diffNotEqExpFp fp2 fp1
|Gt =>  diffNotEqExpFp fp1 fp2
|Eq =>  diffEqExpFp fp1 fp2
end.

Fixpoint diffFp2 (fp1 : fp_num) (fp2 : fp_num) : fp_num :=
match compareAbs fp1 fp2 with
     | Lt => diffFpSys fp2 fp1
     | Gt => diffFpSys fp1 fp2
     | Eq => if fp1.(sign) then minusZero else plusZero
end.

Fixpoint sumFinite (fp1 : fp_num) (fp2 : fp_num) : fp_num :=
if isZero fp1 then
   fp2
else
   if isZero fp2 then
      fp1
   else 
      match compareSign fp1 fp2 with
      |Eq => sumOneSignFp fp1 fp2
      | _ => diffFp2 fp1 fp2
      end.

Fixpoint sumInfinite (fp1 : fp_num) (fp2 : fp_num) : fp_num :=
if isInfinite fp1 then 
   if isInfinite fp2 then 
      match compareSign fp1 fp2 with 
       | Eq => fp1
       | _ => NaN
      end
   else fp1
else fp2.





Fixpoint sumFp (fp1 fp2 : fp_num) : fp_num :=
if isNaN fp1 || isNaN fp2 then NaN
else if isInfinite fp1 || isInfinite fp2 then sumInfinite fp1 fp2
     else sumFinite fp1 fp2.

Fixpoint diffFp (fp1 fp2 : fp_num) : fp_num := sumFp fp1 (neg fp2).


Fixpoint minusExponents (v1:Bvector lenExp) (v2 : Bvector lenExp) : Bvector lenExp := 
let v2New := Vector.cons bool false lenExp v2 in
let v1New := Vector.cons bool false lenExp v1 in
let biasNew := Vector.cons bool false lenExp bias in
let tmp := snd (sumVectors (S lenExp) v1New biasNew) in
let result := snd (diffVectors (S lenExp) tmp v2New) in
Vector.tl result.

Fixpoint SSVector (lenV:nat) (w:Bvector 2) (v:Bvector lenV)  : Bvector (S (S lenV)) :=
let v1 := Vector.cons bool (Vector.last w) lenV v in
Vector.cons bool (Vector.hd w) (S lenV) v1.

Fixpoint PPVector (v:Bvector (S (S lenSign))) : (Bvector 2)*(Bvector lenSign) :=
let v1 := Vector.tl v in
([(Vector.hd v);(Vector.hd v1)],(Vector.tl v1)).


Fixpoint divBit (n:nat) (div1:Bvector n) (div2:Bvector n) :bool*(Bvector n):=
match compareVect n div1 div2 with
|Lt => let w := shiftReplaceL false n div1 in 
       (false,w)
|_ => let tmp := snd (diffVectors n div1 div2) in
      (true,(shiftReplaceL false n tmp))
end.

(*head - number before floating point
  last - for accuracy*)
Fixpoint divSys (m:nat) (div1:Bvector m) (div2:Bvector m) (result:Bvector m) (n:nat): 
         Bvector m :=
let res := divBit m div1 div2 in
match n with
|O =>  shiftReplaceL (fst res) m result
|S l => divSys m (snd res) div2 (shiftReplaceL (fst res) m result) l
end.

Fixpoint removeLast (n:nat) (v:Bvector (S n)) : Bvector n :=
let vv := invertV (S n) (S n) v in
invertV n n (Vector.tl vv).

Fixpoint divFinite (fp1 fp2: fp_num) : fp_num :=
let n := S (S lenSign) in
let v1 := SSVector lenSign [false;true] fp1.(significant) in
let v2 := SSVector lenSign [false;true] fp2.(significant) in
let zeroRes := SSVector lenSign [false;false] allFalseSignificant in
let res:= divSys n v1 v2 zeroRes (S lenSign) in
let resExp:= minusExponents fp1.(exp) fp2.(exp) in
let leftPart := Vector.hd res in
if leftPart then
 let significantRes := removeLast lenSign (Vector.tl res) in
 mkFp (xorb fp1.(sign) fp2.(sign)) resExp significantRes
else
 let significantRes := Vector.tl (Vector.tl res) in
 mkFp (xorb fp1.(sign) fp2.(sign)) (minusBoolV lenExp true resExp) significantRes.


Fixpoint divideFp (fp1 fp2: fp_num) : fp_num :=
if((isNaN fp1) || (isNaN fp2)) then NaN
else 
 if (isZero fp1 && isZero fp2) then NaN 
 else 
  if isZero fp2 then mkFp (xorb fp2.(sign) fp1.(sign)) plusInfinity.(exp) plusInfinity.(significant)
  else 
   if isZero fp1 then
      fp1
   else
      divFinite fp1 fp2.

(**********************************MULTIPLICATION**********************************)


Fixpoint sumExponents (v1:Bvector lenExp) (v2 : Bvector lenExp) : Bvector lenExp := 
let v2New := Vector.cons bool false lenExp v2 in
let v1New := Vector.cons bool false lenExp v1 in
let biasNew := Vector.cons bool false lenExp bias in
let tmp := snd (sumVectors (S lenExp) v1New v2New) in
let result := snd (diffVectors (S lenExp) tmp biasNew) in
Vector.tl result.

(*num*bit+result
  leftPoint,significant *)
Fixpoint multOnBitSignificant  (num:Bvector lenSign) (bit:bool) (result:Bvector lenSign) 
(leftPoint:Bvector 2) :(Bvector 2)*(Bvector lenSign) := 
let shiftResult := shiftReplaceR (Vector.last leftPoint) lenSign result in
match bit with
|false => ([false;Vector.hd leftPoint],shiftResult)
|true => 
 let sum := sumVectors lenSign shiftResult num in
 let resultLeft := sumDigits true (fst sum) (Vector.hd leftPoint) in
 ([fst resultLeft;snd resultLeft],snd sum)
end.



(* num1*num2
   num2 - reverse*)
Fixpoint multSignificantSysR (num1:Bvector lenSign) (n:nat) (num2:Bvector n) 
(result:Bvector lenSign) (leftPoint:Bvector 2) : (Bvector 2)*(Bvector lenSign) :=
match num2 with 
|Vector.nil => multOnBitSignificant  num1 true result leftPoint
|Vector.cons h m w => 
let nextResult := multOnBitSignificant num1 h result leftPoint in
multSignificantSysR num1 m w (snd nextResult) (fst nextResult)
end.  


Fixpoint getAllFalseVect (n:nat) : Bvector n :=
match n with
|O => []
|S m => Vector.cons bool false m (getAllFalseVect m)
end.

Fixpoint multSignificant (num1 num2 : Bvector lenSign):Bvector (S (S lenSign)):=
let num2R:= invertV lenSign lenSign num2 in
let res := multSignificantSysR num1 lenSign num2R allFalseSignificant [false;false] in
SSVector lenSign (fst res) (snd res).



Fixpoint multFinite (fp1 fp2 : fp_num) : fp_num:=
let signRes := xorb fp1.(sign) fp2.(sign) in
let expRes := sumExponents fp1.(exp) fp2.(exp) in
let multRes := multSignificant fp1.(significant) fp2.(significant) in
let newRes := Vector.tl multRes in
let needShift := Vector.hd multRes in
if needShift then
 let newExpRes := plusBoolV lenExp true expRes in
 let newSignificant := 
     shiftReplaceR (Vector.hd newRes) lenSign (Vector.tl newRes) in
 mkFp signRes newExpRes newSignificant
else
 mkFp signRes expRes (Vector.tl newRes).
  
Fixpoint multFp (fp1 fp2 :fp_num) : fp_num :=
if (isNaN fp1) || (isNaN fp2) then NaN 
else 
 if(isInfinite fp1) then 
  if(isInfinite fp2) then
   mkFp (xorb fp1.(sign) fp2.(sign)) fp1.(exp) fp1.(significant)
  else
   if(isZero fp2) then
    NaN
   else  
    fp1
 else 
  if(isInfinite fp2) then
   if(isZero fp1) then
    NaN
   else
    fp2
  else
   if isZero fp1 || isZero fp2 then
      plusZero
   else
      multFinite fp1 fp2.



(*******************************SQRT*******************************)

Fixpoint expSqrt (v:Bvector lenExp) : bool*(Bvector lenExp) :=
match compareVect lenExp v bias with
|Lt => let res := diffVectors lenExp bias v in 
       let tmp := shiftReplaceR false lenExp (snd res) in
       let newRes := diffVectors lenExp bias tmp in
       if (Vector.last v) then
           (false,snd newRes)
       else
          (true,minusBoolV lenExp true (snd newRes))
|_ =>  let res := diffVectors lenExp v bias in 
       let tmp := shiftReplaceR false lenExp (snd res) in
       let newRes := sumVectors lenExp bias tmp in
       if (Vector.last v) then
           (false,snd newRes)
       else
           (true,snd newRes)
end. 


Fixpoint setValToNPositionVect (n:nat) (val:bool) (lenV:nat) (v:Bvector lenV) : Bvector lenV :=
match nat_compare lenV n with
|Lt => v
|Eq => match v with
       |Vector.nil => []
       |Vector.cons h m w => Vector.cons bool val m w
       end
|Gt => match v with
       |Vector.nil => []
       |Vector.cons h m w => 
        let ww:= setValToNPositionVect n val m w in
        Vector.cons bool h m ww
       end
end.

Fixpoint setTrueToNPositionVect (n:nat) (lenV:nat) (v:Bvector lenV) : Bvector lenV :=
setValToNPositionVect n true lenV v.

Fixpoint significantSqrtSys (evenExp:bool) (stepNum:nat) (num res:Bvector lenSign)  
                            : Bvector lenSign :=
match stepNum with
|O=> res
|S m => let newRes := setTrueToNPositionVect (S m) lenSign res in 
        let tmp :=  multSignificant newRes newRes in
        let head := Vector.hd tmp in
        let tmp2 := Vector.tl tmp in
        if eqb head evenExp then
           let squaredRes := shiftReplaceR (Vector.hd tmp2) lenSign (Vector.tl tmp2) in
           match compareVect lenSign num squaredRes with
              |Lt => significantSqrtSys evenExp m num res
              |_ => significantSqrtSys evenExp m num newRes
           end
        else if(evenExp) then
           significantSqrtSys evenExp m num newRes
        else
           significantSqrtSys evenExp m num res
end.




Fixpoint significantSqrt (evenExp:bool) (significant:Bvector lenSign) : Bvector lenSign :=
significantSqrtSys evenExp lenSign significant allFalseSignificant.




Fixpoint sqrtFpPos (fp:fp_num) : fp_num :=
let newExp := expSqrt fp.(exp) in
let evenExp := fst newExp in
let newSignificant := significantSqrt evenExp fp.(significant) in
mkFp false (snd newExp) newSignificant.

Fixpoint sqrtFp(fp:fp_num) : fp_num :=
if isNaN fp then fp
else 
 if isZero fp then 
  fp
 else
  if fp.(sign) then
   NaN
  else
   if isInfinite fp then 
    fp
   else
    sqrtFpPos fp.


(***************************CONVERSATION***************************)

Open Scope Z_scope.
Open Scope positive_scope.
Open Scope Q_scope.



Fixpoint Qgcd (q:Q) : Q :=
let qnum := q.(Qnum) in
let qden := Zpos q.(Qden) in
let gcdRes := Z.gcd qnum qden in
match Z.compare gcdRes 1 with 
|Eq => q
|_ => 
  let newNum := fst (div_eucl_z qnum gcdRes) in
  let newDen := fst (div_eucl_z qden gcdRes) in
  Qmake newNum (Z.to_pos newDen)
end.

Close Scope  Z_scope.
Close Scope positive_scope.

Fixpoint vector2QSys (res:Q) (pow:Q) (n:nat) (v: Bvector n) : Q :=
match v with
|Vector.nil => res
|Vector.cons h m w => let newPow := Qmult (1#2) pow in
let newRes := 
 if h then
  Qplus res newPow
 else
  res
in if h then
 vector2QSys (Qgcd newRes) newPow m w
else
 vector2QSys newRes newPow m w
end.

Fixpoint vector2Q (n:nat) (v:Bvector n) : Q := vector2QSys 1 1 n v.

Fixpoint significant2Q (fp : fp_num) : Q :=
vector2Q lenSign fp.(significant).

Fixpoint power (base: Q) (pow:nat) : Q :=
match pow with
|O => 1
|S m => Qmult base (power base m)
end.


Fixpoint exp2Q (fp: fp_num) : Q :=
if isExpforZero fp.(exp) then
 0#1
else
 let expNat := exp2Nat fp in
 let biasNat := vect2Nat lenExp bias in
 match nat_compare expNat biasNat with
  |Lt => power (1#2) (biasNat - expNat) 
  |_ => power (2#1) (expNat-biasNat)
 end.

Fixpoint fp2Q (fp:fp_num) : Q :=
let qsign := significant2Q fp in
let qexp := exp2Q fp in
let res := Qgcd (Qmult qsign qexp) in
if fp.(sign) then
 Qmult (-1#1) res
else
 res.

Fixpoint getSignificantFromQSys (num curPow:Q) (iter:nat)  : Bvector iter :=
let newPow := Qmult (1#2) curPow in
match iter with
|O => []
|S m => match Qcompare num curPow with
       |Lt => Vector.cons bool false m (getSignificantFromQSys num newPow m)
       |_  => let newNum := Qgcd (Qminus num curPow) in 
           Vector.cons bool true m (getSignificantFromQSys newNum newPow m)
       end
end.  

Fixpoint getSignificantFromQ (num:Q) : Bvector lenSign :=
getSignificantFromQSys num (1#2) lenSign.

Fixpoint computeExpSmallSys (num:Q) (iter:nat) :nat*Q :=
match iter with
|O => (O,num)
|S m => let newNum := Qmult num (2#1) in
   match Qcompare newNum (1#1) with
      |Lt => let res := computeExpSmallSys newNum m in (S (fst res),snd res)
      |_ => (S O, newNum)
   end
end.


Fixpoint computeExpSmall (num:Q) : (Bvector lenExp)*Q :=
let res := computeExpSmallSys num shiftExp in
let secondRes := nat2Vect (fst res) lenExp bias true in
(secondRes,snd res).


Fixpoint computeExpBigSys (num:Q) (iter:nat) :nat*Q :=
match iter with
|O => (O,num)
|S m => let newNum := Qmult num (1#2) in
   match Qcompare newNum (2#1) with
      |Lt => (S O,newNum)
      | _ => let res := computeExpBigSys newNum m in (S (fst res),snd res)
   end
end.

Fixpoint computeExpBig (num:Q) : (Bvector lenExp)*Q :=
let res :=computeExpBigSys num shiftExp in
let secondRes := nat2Vect (fst res) lenExp bias false in
(secondRes,snd res).


Fixpoint getExp (num:Q) : (Bvector lenExp)*Q :=
let newNum := Qabs num in
match Qcompare newNum (2#1) with
|Lt => match Qcompare newNum (1#1) with
       |Lt => computeExpSmall newNum
       | _ => (bias,num)
       end
| _ => computeExpBig newNum
end.

Fixpoint Q2Fp (num:Q): fp_num :=
match Qcompare num (0#1) with
|Eq => plusZero
|_ => 
  let sign := match Qcompare num (0#1) with
    |Lt => true
    | _ => false
   end in 
  let res := getExp num in
  let significant := getSignificantFromQ (Qminus (snd res) (1#1)) in
  mkFp sign (fst res) significant
end.

Fixpoint sqrtStepQ (a res eps : Q) (step:nat) : Q := 
let gcdRes := Qgcd res in
match step with
|O => gcdRes
|S m => let sq:=Qabs (gcdRes*gcdRes-a) in 
 match  Qcompare sq eps with
  |Lt => gcdRes
  | _ => let newRes := (1#2)*(gcdRes + a/gcdRes) in sqrtStepQ a newRes eps m
 end
end.

Fixpoint sqrtAccQ ( acc a : Q) : Q :=
match Qcompare a (0#1) with
|Lt => (-1#1)
| _ => match Qcompare acc (0#1) with
 |Gt => sqrtStepQ  a a acc lenSign
 | _ => (-1#1)
 end
end.

Definition sqrtQ(a:Q) : Q :=
sqrtAccQ  sqrtEps a.

Definition sqrtAccFp (acc:Q) (fp:fp_num) : fp_num:=
sqrtFp fp.

Fixpoint reflectQ (num:Q) : Q := num.

Fixpoint max (n m:nat) : nat :=
match n, m with
  | O, _ => m
  | S n', O => n
  | S n', S m' => S (max n' m')
end.


Record ApproxArith := mkApproxArith
{
 Num : Set;
 sum  : Num -> Num -> Num;
 diff : Num -> Num -> Num;
 mult : Num -> Num -> Num;
 div  : Num -> Num -> Num;
 sqrt : Num -> Num;
 from_rational : Q -> Num;
 to_rational : Num -> Q; 
 lt : Num -> Num -> bool;
 le : Num -> Num -> bool;
 eq : Num -> Num -> bool;
 ge : Num -> Num -> bool;
 gt : Num -> Num -> bool
}.


Definition approxFp := mkApproxArith fp_num sumFp diffFp multFp divideFp sqrtFp Q2Fp fp2Q 
                                     isLtFp_bool isLeFp_bool isEqFp_bool isGeFp_bool isGtFp_bool.
Definition approxQ := mkApproxArith Q Qplus Qminus Qmult Qdiv sqrtQ reflectQ reflectQ 
                                      isLtQ_bool isLeQ_bool isEqQ_bool isGeQ_bool isGtQ_bool.

Inductive ArithExp (n: nat):=
|Get (i: Fin.t n)
|Const (c: Q)
|Add(a b :ArithExp n)
|Diff(a b:ArithExp n)
|Mult(a b:ArithExp n)
|Div(a b:ArithExp n)
|Sqrt(a :ArithExp n)
|Noting
|If(cond:BoolExp n) (onTrue: ArithExp n) (onFalse: ArithExp n)
with BoolExp(n:nat) :=
|And (a b : BoolExp n)
|Or (a b :BoolExp n)
|Eq (a b : ArithExp n)
|Gt (a b : ArithExp n)
|Ge (a b : ArithExp n)
|Lt (a b : ArithExp n)
|Le (a b : ArithExp n).

Close Scope Q_scope.
(*result_code,result*)
(*result_code: 0-ok,1-don't put,x>1 - error *)
Definition ok_code: nat := 0.
Definition nothing_code : nat := 1.
Definition error_code : nat := 2.

Fixpoint computeExp (n:nat) (arith: ApproxArith) (exp: ArithExp n) 
                       (init : t (Num arith) n) : nat*(Num arith) :=
let error:= from_rational arith (-1#1) in
let zero := from_rational arith 0 in
match exp with
 |Get x => (0,nth init x)
 |Const x => (0,from_rational arith x)
 |Add x1 x2 =>
  let res1 := computeExp n arith x1 init in
  let code_1 := fst res1 in
  let result_1 := snd res1 in
  let res2 := computeExp n arith x2 init in
  let code_2 := fst res2 in
  let result_2 := snd res2 in
  if andb (leb code_1 ok_code) (leb code_2 ok_code) then
   (ok_code, sum arith result_1 result_2)
  else
   (max code_1 code_2,error)
 |Diff x1 x2 =>
  let res1 := computeExp n arith x1 init in
  let code_1 := fst res1 in
  let result_1 := snd res1 in
  let res2 := computeExp n arith x2 init in
  let code_2 := fst res2 in
  let result_2 := snd res2 in
  if andb (leb code_1 ok_code) (leb code_2 ok_code) then
   (ok_code, diff arith result_1 result_2)
  else
   (max code_1 code_2,error)
 |Mult x1 x2 =>
  let res1 := computeExp n arith x1 init in
  let code_1 := fst res1 in
  let result_1 := snd res1 in
  let res2 := computeExp n arith x2 init in
  let code_2 := fst res2 in
  let result_2 := snd res2 in
  if andb (leb code_1 ok_code) (leb code_2 ok_code) then
   (ok_code, mult arith result_1 result_2)
  else
   (max code_1 code_2,error)
 |Div x1 x2 =>
  let res1 := computeExp n arith x1 init in
  let code_1 := fst res1 in
  let result_1 := snd res1 in
  let res2 := computeExp n arith x2 init in
  let code_2 := fst res2 in
  let result_2 := snd res2 in
  if andb (leb code_1 ok_code) (leb code_2 ok_code) then
   if (eq arith result_2 zero) then
    (error_code,error)
   else
   (ok_code, div arith result_1 result_2)
  else
   (max code_1 code_2,error)
 |Sqrt x => 
  let res := computeExp n arith x init in
  let code := fst res in
  let result := snd res in
  if (leb code ok_code) then
   if (ge arith result zero) then
    (ok_code,sqrt arith result)
   else
    (error_code,error)
  else
   (code,error)
 |If cond onTrue onFalse => 
  let cond_res := computeBoolExp n arith cond init in
  let cond_code := fst cond_res in
  let cond_val := snd cond_res in
  if (leb cond_code ok_code) then
   if cond_val then
    computeExp n arith onTrue init
   else
    computeExp n arith onFalse init 
  else
   (error_code,error)
 |Nothing => (nothing_code,error)
end
with computeBoolExp (n:nat) (arith: ApproxArith) (exp: BoolExp n) 
                     (init : t (Num arith) n) : nat*bool :=
match exp with
|And x y => 
 let res1 := computeBoolExp n arith x init in
 let res2 := computeBoolExp n arith y init in
 let code_1 := fst res1 in
 let code_2 := fst res2 in
 let result_1 := snd res1 in
 let result_2 := snd res2 in
 if  andb (leb code_1 ok_code) (leb code_2 ok_code) then
  (ok_code,andb result_1 result_2)
 else
  (error_code,false)
|Or x y =>
 let res1 := computeBoolExp n arith x init in
 let res2 := computeBoolExp n arith y init in
 let code_1 := fst res1 in
 let code_2 := fst res2 in
 let result_1 := snd res1 in
 let result_2 := snd res2 in
 if  andb (leb code_1 ok_code) (leb code_2 ok_code) then
  (ok_code,orb result_1 result_2)
 else
  (error_code,false)
|Eq x y => 
 let res1 := computeExp n arith x init in
 let code_1 := fst res1 in
 let result_1 := snd res1 in
 let res2 := computeExp n arith y init in
 let code_2 := fst res2 in
 let result_2 := snd res2 in
 if andb (leb code_1 ok_code) (leb code_2 ok_code) then
  (ok_code, eq arith result_1 result_2)
 else
  (error_code,false)
|Gt x y => 
 let res1 := computeExp n arith x init in
 let code_1 := fst res1 in
 let result_1 := snd res1 in
 let res2 := computeExp n arith y init in
 let code_2 := fst res2 in
 let result_2 := snd res2 in
 if andb (leb code_1 ok_code) (leb code_2 ok_code) then
  (ok_code, gt arith result_1 result_2)
 else
  (error_code,false)
|Ge x y => 
 let res1 := computeExp n arith x init in
 let code_1 := fst res1 in
 let result_1 := snd res1 in
 let res2 := computeExp n arith y init in
 let code_2 := fst res2 in
 let result_2 := snd res2 in
 if andb (leb code_1 ok_code) (leb code_2 ok_code) then
  (ok_code, ge arith result_1 result_2)
 else
  (error_code,false)
|Lt x y => 
 let res1 := computeExp n arith x init in
 let code_1 := fst res1 in
 let result_1 := snd res1 in
 let res2 := computeExp n arith y init in
 let code_2 := fst res2 in
 let result_2 := snd res2 in
 if andb (leb code_1 ok_code) (leb code_2 ok_code) then
  (ok_code, lt arith result_1 result_2)
 else
  (error_code,false)
|Le x y => 
 let res1 := computeExp n arith x init in
 let code_1 := fst res1 in
 let result_1 := snd res1 in
 let res2 := computeExp n arith y init in
 let code_2 := fst res2 in
 let result_2 := snd res2 in
 if andb (leb code_1 ok_code) (leb code_2 ok_code) then
  (ok_code, le arith result_1 result_2)
 else
  (error_code,false)
end.


Fixpoint interp (n:nat) (arith :ApproxArith) (prog : list ((Fin.t n) *(ArithExp n)))
                  (init: t (Num arith) n) : nat*(t (Num arith) n)  := 
match prog with
|List.nil => (ok_code,init)
|List.cons h tl => 
 let pos := fst h in
 let exp := snd h in
 let res := computeExp n arith exp init in 
 let code := fst res in
 let val := snd res in
 if leb code ok_code then
  interp n arith tl (replace init pos val)
 else
  if leb code nothing_code then
   interp n arith tl init
  else
   (error_code,init)
end.



