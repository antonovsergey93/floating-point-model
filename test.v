Definition kf0 := Q2Fp 0.
Definition kf1 := Q2Fp (1#1).
Definition kfp5 := Q2Fp (1#2).
Definition visc := Q2Fp (316#100).

Fixpoint getNewPart ( f_tin f_tout part1 part2 dtt : fp_num ) :fp_num*fp_num :=
let tmp3 := diffFp f_tin part1 in
let newPart1 := multFp dtt tmp3 in
let tmp4 := diffFp f_tout part2 in
let newPart2 := multFp dtt tmp4 in
( newPart1 , newPart2 ) .

(* part1 , part2 , nf *)
Fixpoint ysparg ( p_out p_in_out p_in_in d1 d2 dtt part1 part2 : fp_num ) :
(fp_num*fp_num ) *fp_num:=
let nf := kf1 in
let f_8 := multFp visc (sqrtFp d1) in
let f_9 := multFp visc (sqrtFp d2) in
let compare_1 := compare p_in_out p_out in
let compare_2 := compare p_in_in p_out in
if ( isGt compare_1 && isGE compare_2 ) then
 let tmp1 := diffFp p_in_out p_out in
 let tmp2 := sumFp tmp1 f_8 in
 let f_tin := divideFp tmp1 tmp2 in
 let f_tout := kf0 in
 ( getNewPart f_tin f_tout part1 part2 dtt , nf )
else
 if ( isLt compare_1 && isLE compare_2 ) then
  let f_tin := kf0 in
  let tmp1 := diffFp p_out p_in_in in
  let tmp2 := sumFp tmp1 f_9 in
  let f_tout := divideFp tmp1 tmp2 in
  ( getNewPart f_tin f_tout part1 part2 dtt , nf )
 else
  let tmp0 := diffFp p_in_out p_in_in in
  match compare tmp0 kf0 with
  | Lt =>
   let f_tin := kfp5 in
   let f_tout := kfp5 in
   ( getNewPart f_tin f_tout part1 part2 dtt , kf0 )
  |_ =>
   let tmp1 := diffFp p_in_out p_out in
   let tmp2 := diffFp p_in_out p_in_in in
   let tmp3 := sumFp tmp2 f_8 in
   let f_tin := divideFp tmp1 tmp3 in
   let tmp4 := diffFp p_out p_in_in in
   let tmp5 := sumFp tmp2 f_9 in
   let f_tout := divideFp tmp4 tmp5 in
   ( getNewPart f_tin f_tout part1 part2 dtt , nf )
end .