(* programm *) 

(* p_out p_in_out p_in_in d1 d2 dtt | *part1 *part2 *nf | f_8 f_9 f_tin f_tout *)
Definition n := 13.
Definition fin_1 : Fin.t n := F1.
Definition fin_2 : Fin.t n := FS F1.
Definition fin_3 : Fin.t n := FS (FS F1).
Definition fin_4 : Fin.t n := FS (FS (FS F1)).
Definition fin_5 : Fin.t n := FS (FS (FS (FS F1))).
Definition fin_6 : Fin.t n := FS (FS (FS (FS (FS F1)))).
Definition fin_7 : Fin.t n := FS (FS (FS (FS (FS (FS F1))))).
Definition fin_8 : Fin.t n := FS (FS (FS (FS (FS (FS (FS F1)))))).
Definition fin_9 : Fin.t n := FS (FS (FS (FS (FS (FS (FS (FS F1))))))).
Definition fin_10 : Fin.t n := FS (FS (FS (FS (FS (FS (FS (FS (FS F1)))))))).
Definition fin_11 : Fin.t n := FS (FS (FS (FS (FS (FS (FS (FS (FS (FS F1))))))))).
Definition fin_12 : Fin.t n := FS (FS (FS (FS (FS (FS (FS (FS (FS (FS (FS F1)))))))))).
Definition fin_13 : Fin.t n := FS (FS (FS (FS (FS (FS (FS (FS (FS (FS (FS (FS F1))))))))))).

Definition kf0 := Const n 0.
Definition kf1 := Const n (1#1).
Definition kfp5 := Const n (1#2).
Definition visc := Const n (316#100).

Definition p_out := Get n fin_1. 
Definition p_in_out := Get n fin_2.
Definition p_in_in := Get n fin_3. 
Definition d1 := Get n fin_4. 
Definition d2 := Get n fin_5. 
Definition dtt := Get n fin_6. 
Definition line1 := (fin_9, kf1).
Definition f_8 := Mult n visc (Sqrt n d1).
Definition f_9 := Mult n visc (Sqrt n d2).
Definition expr1 := Diff n p_in_out p_out (* p_in_out-p_out *). 
Definition expr2 := Diff n p_out p_in_in (* p_out-p_in_in *).
Definition expr3 := Diff n p_in_out p_in_in (* p_in_out-p_in_in *).
Definition cond1 := And n (Gt n p_in_out p_out) (Ge n p_in_in p_out) (* (p_in_out > p_out) && (p_in_in >= p_out) *).
Definition cond2 := And n (Lt n p_in_out p_out) (Le n p_in_in p_out)(* (p_in_out < p_out) && (p_in_in <= p_out) *).
Definition cond3 := Lt n (Diff n p_in_out p_in_in) kf0 (* (p_in_out - p_in_in) < kf0 *).
Definition c1t_1 := Div n expr1 (Add n (Diff n p_in_out p_out) f_8) (* f_tin = (p_in_out-p_out)/(p_in_out-p_out+f_8)*)  .
Definition c1t_2 := kf0 (* f_tout = kf0 *).
Definition c1f_c2t_1 :=  kf0 (* f_tin = kf0; *).
Definition c1f_c2t_2 := Div n expr2 (Add n expr2 f_9)(* f_tout = (p_out-p_in_in)/(p_out-p_in_in+f_9); *).
Definition c1f_c2f_c3t_1 := kfp5 (* f_tin = kfp5; *).
Definition c1f_c2f_c3t_2 := kfp5 (* f_tout = kfp5; *).
Definition c1f_c2f_c3t_3 := kf0 (*  nf = kf0; *).
Definition c1f_c2f_c3f_1 := Div n expr1 (Add n expr3 f_8) (* f_tin = (p_in_out-p_out)/(p_in_out-p_in_in+f_8); *).
Definition c1f_c2f_c3f_2 := Div n expr2 (Add n expr3 f_9) (* f_tout = (p_out-p_in_in)/(p_in_out-p_in_in+f_9); *).
Definition ife3_1 := If n cond3 c1f_c2f_c3t_1 c1f_c2f_c3f_1.
Definition ife3_2 := If n cond3 c1f_c2f_c3t_2 c1f_c2f_c3f_2.
Definition ife3_3 := If n cond3 c1f_c2f_c3t_3 (Noting n).
Definition ife2_1 := If n cond2 c1f_c2t_1 ife3_1.
Definition ife2_2 := If n cond2 c1f_c2t_2 ife3_2.
Definition ife2_3 := If n cond2 (Noting n) ife3_3.
Definition line2 := (fin_12,If n cond1 c1t_1 ife2_1).
Definition line3 := (fin_13,If n cond1 c1t_2 ife2_2).
Definition line4 := (fin_9,If n cond1 (Noting n) ife2_3).
Definition line5_1 := Mult n dtt (Diff n (Get n fin_12) (Get n fin_7)) (* dtt*(f_tin-*part1); *).
Definition line5 := (fin_7,Add n (Get n fin_7) line5_1) (* *part1+=dtt*(f_tin-*part1); *).
Definition line6_1 := Mult n dtt (Diff n (Get n fin_13) (Get n fin_8)) (* dtt*(f_tout-*part2);*).
Definition line6 :=  (fin_8,Add n (Get n fin_8) line6_1) (* *part2+=dtt*(f_tout-*part2);*).

Definition prog := List.cons line1 (List.cons line2 (List.cons line3 (List.cons line4 (List.cons line5 (List.cons line6 List.nil))))).

Open Scope Q_scope.

(*   1      2        3     4  5  6  |   7       8    9  |  10  11  12    13    *)
(* p_out p_in_out p_in_in d1 d2 dtt | *part1 *part2 *nf | f_8 f_9 f_tin f_tout *)

Definition init : t Q n := (350#1)::(400#1)::(300#1)::(1024#1)::(729#1)::(1#100)::0::0::(-1#1)::(-1#1)::(-1#1)::(-1#1)::(-1#1)::(Vector.nil Q).
Definition result := snd (interp n approxFp prog  (map Q2Fp init)).
Definition vect := (Qminus (fp2Q (nth result fin_7)) (50#20112),Qminus  (fp2Q (nth result fin_8)) (50#18532)).
Eval compute in vect.

