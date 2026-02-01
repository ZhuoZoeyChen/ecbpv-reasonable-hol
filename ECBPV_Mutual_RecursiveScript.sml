(* See:
    Paul Blain Levy
    "Call-by-Push-Value: A Subsuming Paradigm", 1999;

     Forster, Schafer, Spies and Stark,
     "Call-By-Push-Value in Coq: Operational, Equational, and Denotational Theory", CPP 2019;

     Dylan McDermott and Alan Mycroft,
     Extended call-by-push-value: reasoning about effectful programs and evaluation order;
        
   for inspiration
*)
open HolKernel Parse boolLib bossLib;
open arithmeticTheory;
open listTheory;

val _ = new_theory "ECBPV_Mutual_Recursive";

(* ==========================
             Syntax
   ========================== *)

(* CBPV terms defined mutual recursively *)
Datatype:
        val = var num | thunk comp ;
        comp = force val | lam comp | app comp val | ret val |
               seq comp comp | letin val comp | pseq comp comp comp |
               need comp comp | needvar num
End

(* val val_induction = fetch "-" "val_induction";*)

Definition sizeVal_def:
  (sizeVal (var n) = 1 + n) ∧
  (sizeVal (thunk c) = 1 + sizeComp c) ∧
  (sizeComp (force v) = 1 + sizeVal v) ∧
  (sizeComp (lam m) = 1 + sizeComp m) ∧
  (sizeComp (app m v) = 1 + sizeComp m + sizeVal v) ∧
  (sizeComp (ret v) = 1 + sizeVal v) ∧
  (sizeComp (seq m n) = 1 + sizeComp m + sizeComp n) ∧
  (sizeComp (letin v m) = 1 + sizeVal v + sizeComp m) ∧
  (sizeComp (pseq m2 m1 n) = 1 + sizeComp m2 + sizeComp m1 + sizeComp n) ∧
  (sizeComp (need m1 m2) = 1 + sizeComp m1 + sizeComp m2) ∧
  (sizeComp (needvar n) = 1 + n)
End

(* substVal s k u:
     substitutes all the occurences of (var k) in s with u *)
Definition substVal_def:
  (substVal (var n) k u = if (n = k) then u else (var n)) ∧
  (substVal (thunk m) k u = thunk (substComp m k u)) ∧
  (substComp (force v) k u = force (substVal v k u)) ∧
  (substComp (lam m) k u = lam (substComp m (SUC k) u)) ∧
  (substComp (app m v) k u = app (substComp m k u) (substVal v k u)) ∧
  (substComp (ret v) k u = ret (substVal v k u)) ∧
  (substComp (seq m n) k u = seq (substComp m k u) (substComp n (SUC k) u)) ∧
  (substComp (letin v m) k u = letin (substVal v k u) (substComp m (SUC k) u)) ∧
  (substComp (pseq m2 m1 n) k u = pseq (substComp m2 k u) (substComp m1 k u) (substComp n (SUC (SUC k)) u)) ∧
  (substComp (need m n) k u = need (substComp m k u) (substComp n k u)) ∧
  (substComp (needvar x) k u = needvar x)
End

Definition substNeedVal_def:
  (substNeedVal (var n) k u = var n) ∧
  (substNeedVal (thunk m) k u = thunk (substNeedComp m k u)) ∧
  (substNeedComp (force v) k u = force (substNeedVal v k u)) ∧
  (substNeedComp (lam m) k u = lam (substNeedComp m k u)) ∧
  (substNeedComp (app m v) k u = app (substNeedComp m k u) (substNeedVal v k u)) ∧
  (substNeedComp (ret v) k u = ret (substNeedVal v k u)) ∧
  (substNeedComp (seq m n) k u = seq (substNeedComp m k u) (substNeedComp n k u)) ∧
  (substNeedComp (letin v m) k u = letin (substNeedVal v k u) (substNeedComp m k u)) ∧
  (substNeedComp (pseq m2 m1 n) k u = pseq (substNeedComp m2 k u) (substNeedComp m1 k u) (substNeedComp n k u)) ∧
  (substNeedComp (need m n) k u = need (substNeedComp m k u) (substNeedComp n (SUC k) u)) ∧
  (substNeedComp (needvar n) k u = if (n = k) then u else (needvar n))
End

val t1 = ``force (thunk (app (lam (ret (var 0))) (var 1)))``

Inductive is_terminal:
        (is_terminal (ret s)) ∧
        (is_terminal (lam t))
End

(* ==========================
      Small-step Semantics
   ========================== *)

Inductive primitive_step:
        (∀m. primitive_step (force (thunk m)) m) ∧
        (∀m m' v. substComp m 0 v = m' ⇒ primitive_step (app (lam m) v) m') ∧
        (∀m m' v. (substComp m 0 v) = m' ⇒ (primitive_step (letin v m) m')) ∧
        (∀n n' v.  (substComp n 0 v) = n' ⇒ (primitive_step (seq (ret v) n) n')) ∧
        (∀v1 v2 n n'.  (substComp (substComp n 0 v1) 1 v2) = n' ⇒ (primitive_step (pseq (ret v2) (ret v1) n) n')) ∧
        (∀n n' v.  (substNeedComp n 0 (ret v)) = n' ⇒ (primitive_step (need (ret v) n) n'))
End

(*Datatype:
  ctxt = hole
       | cseq ctxt comp
       | cpseq1 ctxt comp comp
       | cpseq2 comp ctxt comp
       (* TODO: something with Need *)
End

Definition fill_def:
  fill hole m = m ∧
  fill (cseq c m) m' = seq (fill c m') m ∧
  fill (cpseq1 c m m') m'' = pseq (fill c m'') m m' ∧
  fill (cpseq2 m c m') m'' = pseq m (fill c m'') m'
End*)

Definition is_ret_def:
  is_ret (ret x) = T ∧
  is_ret _ = F
End

(* demands m n:
   m is a ecbpv term;
   n here is a number that represents the de bruijn index;
   demands m n means whether m is "demanded" (it needs to be evaluated now) *)
(* TODO: complexity of demand is O(n) each time,
 which means usage of this function will incur a big time cost.
       How do we reason about this in the final complexity proof .
       I think we need to delay this check until the very end... *)
Inductive demands:
[~needvar:]
  (∀k. demands (needvar k) k)
[~app:]
  (∀m v k. demands m k ⇒ demands (app m v) k)
[~seq:]
  (∀m m' k. demands m k ⇒ demands (seq m m') k)
[~pseq1:]
  (∀m1 m2 n k. demands m1 k ⇒ demands (pseq m2 m1 n) k)
[~pseq2:]
  (∀v m2 n k. demands m2 k ⇒ demands (pseq m2 (ret v) n) k)
[~need1:]
  (∀m m' k. demands m k ∧ demands m' 0 ⇒ demands (need m m') k)
[~need2:]
  (∀m m' k. demands m' (SUC k) ⇒ demands (need m m') k)
End

Inductive small_step:
        (∀m m'. primitive_step m m' ⇒ small_step m m') ∧
        (∀m m' v. small_step m m' ⇒ small_step (app m v) (app m' v)) ∧
        (∀m m' n. small_step m m' ⇒ small_step (seq m n) (seq m' n)) ∧
        (∀m1 m1' m2 n. small_step m1 m1' ⇒ small_step (pseq m2 m1 n) (pseq m2 m1' n)) ∧
        (∀v m2 m2' n. small_step m2 m2' ⇒ small_step (pseq m2 (ret v) n) (pseq m2' (ret v)  n)) ∧
        (∀m m' n. demands n 0 ∧ small_step m m' ⇒ small_step (need m n) (need m' n))
 (* evaluates m if m is needed in n (note that demands only true if m will not be thrown away during the evaluation )*)
        ∧   
        (∀m n n'. small_step n n' ∧ ¬is_ret m ⇒ small_step (need m n) (need m n'))
       (* During evaluation of an ECBPV, the reduction of n happens before reduction of m *)
End

val v = “thunk $ lam $ ret $ var 0”

Theorem example1:
  RTC small_step
      (need (letin ^v (ret $ var 0))
            (letin ^v (needvar 0)))
      (ret ^v)
Proof
  irule_at Any relationTheory.RTC_TRANS >>
  irule_at Any relationTheory.RTC_SINGLE >>
  irule_at Any $ cj 7 small_step_rules >>
  rw[Once small_step_cases,is_ret_def] >>
  rw[Once primitive_step_cases] >>
  rw[substVal_def] >>
  irule_at Any relationTheory.RTC_TRANS >>
  irule_at Any relationTheory.RTC_SINGLE >>
  irule_at Any $ cj 6 small_step_rules >>
  rw[Once demands_cases] >>
  rw[Once small_step_cases,is_ret_def] >>
  rw[Once primitive_step_cases] >>
  rw[substVal_def] >>
  irule_at Any relationTheory.RTC_TRANS >>
  irule_at Any relationTheory.RTC_SINGLE >>
  irule_at Any $ cj 1 small_step_rules >>
  rw[Once primitive_step_cases,PULL_EXISTS] >>
  rw[substNeedVal_def]
QED

(* human readable ver: *)
Theorem example2:
  RTC small_step
      (need (letin ^v (ret $ var 0))
            (need (ret ^v) (needvar 1)))
      (ret ^v)
Proof
  irule_at Any relationTheory.RTC_TRANS >>
  irule_at Any relationTheory.RTC_SINGLE >>
  irule_at Any $ cj 6 small_step_rules >>
  rw[Once demands_cases] >>
  rw[Once demands_cases] >>
  rw[Once demands_cases] >>
  rw[Once small_step_cases,is_ret_def] >>
  rw[Once primitive_step_cases] >>
  rw[substVal_def] >>
  irule_at Any relationTheory.RTC_TRANS >>
  irule_at Any relationTheory.RTC_SINGLE >>
  irule_at Any $ cj 1 small_step_rules >>
  rw[Once primitive_step_cases,PULL_EXISTS] >>
  rw[substNeedVal_def] >>
  irule_at Any relationTheory.RTC_TRANS >>
  irule_at Any relationTheory.RTC_SINGLE >>
  irule_at Any $ cj 1 small_step_rules >>
  rw[Once primitive_step_cases,PULL_EXISTS] >>
  rw[substNeedVal_def]
QED

(* ==========================
       Big-step Semantics
   ========================== *)

   (* todo : big_step *)
   (*
Inductive big_step:
        (∀v. big_step (ret v) (ret v)) ∧
        (∀m. big_step (lam m) (lam m)) ∧
        (∀m m'. big_step m m' ⇒ big_step (force (thunk m)) m') ∧
        (∀m n v n'. (big_step m (lam n) ∧ big_step (substComp n 0 v) n') ⇒
                                 big_step (app m v) n') ∧
        (∀m m' v. big_step (substComp m' 0 v) m ⇒ big_step (letin v m') m)      ∧
        (∀m n n' v. big_step m (ret v) ∧ big_step (substComp n 0 v) n' ⇒
                                 big_step (seq m n) n') ∧
        (∀m1 m2 v1 v2 n n'. big_step m1 (ret v1) ∧ big_step m2 (ret v2) ∧ big_step (substComp (substComp n 0 v1) 1 v2) n' ⇒
                                 big_step (pseq m1 m2 n) n')
End
*)

(* -- Big-Step Semantics with Time Cost -- *)
 (*
Definition will_demand_def:
  will_demand n v = (∃n'. small_step n n' ∧ demands n' v)
End
 *)
 
Inductive timeBS:
[~Lam:]
  (∀s. timeBS (0:num) (lam s) (lam s))
[~Ret:]
  (∀s. timeBS (0:num) (ret s) (ret s))
[~NeedVar:]
  (∀x. timeBS (0:num) (needvar x) (needvar x))
[~App:]
  (∀m m' v u i k l.
    timeBS i m (lam m') ∧
    timeBS k (substComp m' 0 v) u ∧
    l = i+1+k ⇒
    timeBS l (app m v) u)
[~App2:]
  (∀m v u i l x.
    timeBS i m u ∧
    demands u x ∧
    l = i ⇒
    timeBS l (app m v) (app u v))
[~Seq:]
  (∀m n v u i k l.
    timeBS i m (ret v) ∧
    timeBS k (substComp n 0 v) u ∧
    l = i+1+k ⇒
    timeBS l (seq m n) u)
[~Seq2:]
(* the first machine (whose value will be substituted into the second machine) has a needvar that is pending evaluation *)
  (∀m n u i l x.
    timeBS i m u ∧
    demands u x ∧
    l = i ⇒
    timeBS l (seq m n) (seq u n))
[~Pseq:]
  (∀m1 m2 v1 v2 n u i j k l.
    timeBS i m1 (ret v1) ∧
    timeBS j m2 (ret v2) ∧
    timeBS k (substComp (substComp n 0 v1) 1 v2) u ∧
    l = i+j+1+k ⇒
    timeBS l (pseq m2 m1 n) u)
[~Pseq2:]
(* the first machine (whose value will be substituted into the third machine) has a needvar that is pending evaluation *)
  (∀m1 m2 u1 n i l x1.
    timeBS i m1 u1 ∧
    demands u1 x1 ∧
    l = i ⇒
    timeBS l (pseq m2 m1 n) (pseq m2 u1 n))
[~Pseq3:]
  (* the second machine (whose value will be substituted into the third machine) has a needvar that is pending evaluation *)
  (∀m1 m2 u2 n j l x2.
    timeBS i m1 (ret u1) ∧
    timeBS j m2 u2 ∧
    demands u2 x2 ∧
    l = i + j ⇒
    timeBS l (pseq m2 m1 n) (pseq u2 (ret u1) n))
[~Letin:]
  (∀m v u k l.
    timeBS k (substComp m 0 v) u ∧
    l = 1+k ⇒
    timeBS l (letin v m) u)
[~Force:]
  (∀m u k l.
    timeBS k m u ∧
    l = 2+k ⇒
    timeBS l (force (thunk m)) u)
[~Need1:]
  (*if m is needed then:*)
  (* Reduce n to u, then if u demands m, then evaluate m to (ret v) and substitute in.
     This order feel more correct than *)
  (∀m n v u i k l.
    timeBS i n u ∧
    demands u 0 ∧
    timeBS j m (ret v) ∧
    timeBS k (substNeedComp u 0 (ret v)) w ∧
    l = i+1+k+j ⇒
    timeBS l (need m n) w)
[~Need2:]
  (*if m is not needed then, but something else is:*)
  (∀m n u i l.
    timeBS i n u ∧
    ¬is_ret u ∧
    ¬demands u 0 ∧
    l = i ⇒
    timeBS l (need m n) (need m u))
[~NotNeed:]
  (*if m is NOT needed then: dont need to add i *)
  (∀m n u i l.
    timeBS i n (ret u) ∧
    l = i ⇒
    timeBS l (need m n) (ret u))
End


(* -- Big-Step Semantics with Space Cost -- *)

Inductive spaceBS:
[~Lam:]
  (∀s. spaceBS (sizeComp (lam s)) (lam s) (lam s))
[~Ret:]
  (∀s. spaceBS (sizeComp (ret s)) (ret s) (ret s))
[~App:]
  (∀s s' v u k1 k2 k.
    spaceBS k1 s (lam s') ∧
    spaceBS k2 (substComp s' 0 v) u ∧
    k = MAX (k1 + 1 + sizeVal v) k2 ⇒
    spaceBS k (app s v) u)
[~App2:]
  (∀s s' v k1 k x.
    spaceBS k1 s s' ∧
    demands s' x ∧
    k = k1 + 1 + sizeVal v ⇒
    spaceBS k (app s v) (app s' v)) 
[~Seq:]
  (∀s n v u k1 k2 k.
    spaceBS k1 s (ret v) ∧
    spaceBS k2 (substComp n 0 v) u ∧
    k = MAX (k1 + 1 + sizeComp n) k2 ⇒
    spaceBS k (seq s n) u)
[~Seq2:]
  (∀s s' n k1 k x.
    spaceBS k1 s s' ∧
    demands s' x ∧
    k = k1 + 1 + sizeComp n ⇒
    spaceBS k (seq s n) (seq s' n))
[~PSeq:]
  (∀m1 m2 v1 v2 n u k1 k2 k3 k.
    spaceBS k1 m1 (ret v1) ∧
    spaceBS k2 m2 (ret v2) ∧
    spaceBS k3 (substComp (substComp n 0 v1) 1 v2) u ∧
    k = MAX (k1 + sizeComp m2 + 1 + sizeComp n) $ MAX (k2 + sizeVal v1 + 1 + sizeComp n) k3 ⇒
    spaceBS k (pseq m2 m1 n) u)
[~PSeq2:]
  (∀m1 m2 m1' n k1 k.
    spaceBS k1 m1 m1' ∧
    k = k1 + sizeComp m2 + 1 + sizeComp n ⇒
    spaceBS k (pseq m2 m1 n) (pseq m2 m1' n))
[~PSeq3:]
  (∀m1 m2 m2' n k2 k.
    spaceBS k1 m1 (ret v1) ∧
    spaceBS k2 m2 m2' ∧
    k = MAX (k1 + sizeComp m2 + 1 + sizeComp n) (k2 + 1 + sizeVal v1 + 1 + sizeComp n) ⇒
    spaceBS k (pseq m2 m1 n) (pseq m2' (ret v1) n))
[~Letin:]
  (∀m v u k0 k.
    spaceBS k0 (substComp m 0 v) u ∧
    k = MAX k0 (1 + sizeVal v + sizeComp m) ⇒
    spaceBS k (letin v m) u)
[~Force:]
  (∀m u k0 k.
    spaceBS k0 m u ∧
    k = MAX k0 (sizeComp m + 2) ⇒
    spaceBS k (force (thunk m)) u)
[~Need1:]
  (*if m is needed then:*)
  (* Reduce n to u, then if u demands m, then evaluate m to (ret v) and substitute in.
     This order feel more correct than.
     *)
  (∀m n v u k1 k2 k3 k w.
    spaceBS k1 m (ret v) ∧
    spaceBS k2 n u ∧
    demands u 0 ∧
    spaceBS k3 (substNeedComp u 0 (ret v)) w ∧
    k = MAX (MAX (1 + k1 + sizeComp n) (1 + sizeVal v + k2)) k3 ⇒
    spaceBS k (need m n) w)
[~Need2:]
  (*if m is not needed then, but something else is:*)
  (∀m n u k0 k.
    spaceBS k0 n u ∧
    ¬is_ret u ∧
    ¬demands u 0 ∧
    k = 1 + sizeComp m + k0  ⇒
    spaceBS k (need m n) (need m u))
[~NotNeed:]
  (*if m is NOT needed then: dont need to add i *)
  (∀m n u k0 k.
    spaceBS k0 n (ret u) ∧
    k = MAX (1 + sizeComp m + 1 + sizeComp n) (1 + sizeComp m + k0) ⇒
    spaceBS k (need m n) (ret u))
    (* Note that the second stage of this computation
       takes space (1+|m|+k0) instead of just k0
       because we still need to keep m around during the reduction of n.
       Because we don't know if m will be demanded until we finish
       reducing n to (ret u). *)
End

        (*
Theorem big_step_iff_spaceBS:
  big_step s s' ⇔ ∃k. spaceBS k s s'
Proof
  eq_tac
  >- (Induct_on `big_step` >> rw[] >> rw[Once spaceBS_cases] >>
      metis_tac[])
  >> Induct_on `spaceBS` >> rw[] >> rw[Once big_step_cases] >>
  metis_tac[]
QED
        *)

        
Theorem spaceBS_ge:
  ∀m s t.
    spaceBS m s t ⇒ sizeComp s ≤ m ∧ sizeComp t ≤ m
Proof
  Induct_on `spaceBS` >> rw[] >>
  fs[sizeVal_def] 
QED

        
(*----------------------------------
                Bound
  ----------------------------------*)

Inductive boundVal:
  (∀k n. n < k ⇒ boundVal k (var n)) ∧
  (∀k c. boundComp k c ⇒ boundVal k (thunk c)) ∧
  (∀k c v. boundComp k c ∧ boundVal k v ⇒ boundComp k (app c v)) ∧
  (∀k c. boundComp (SUC k) c ⇒ boundComp k (lam c)) ∧
  (∀k v. boundVal k v ⇒ boundComp k (ret v)) ∧
  (∀k v. boundVal k v ⇒ boundComp k (force v)) ∧
  (∀k m n. boundComp k m ∧ boundComp (SUC k) n ⇒ boundComp k (seq m n)) ∧
  (∀k m1 m2 n. boundComp k m1 ∧ boundComp k m2 ∧ boundComp (SUC (SUC k)) n ⇒ boundComp k (pseq m2 m1 n)) ∧
  (∀k v m. boundVal k v ∧ boundComp (SUC k) m ⇒ boundComp k (letin v m)) ∧
  (∀k m n. boundComp k m ∧ boundComp k n ⇒ boundComp k (need m n)) ∧
  (∀k n. boundComp k (needvar n)) 
End

Definition closedVal_def:
  (closedVal v = boundVal 0 v)
End

Definition closedComp_def:
  (closedComp m = boundComp 0 m)
End

Theorem bound_closed_k:
  (∀v k u. boundVal k v ⇒ substVal v k u = v) ∧
  (∀m k u. boundComp k m ⇒ substComp m k u = m)
Proof
  Induct >> rw[] >> (* 8 *)
  pop_assum mp_tac >> rw[Once boundVal_cases, Once substVal_def]
QED

Theorem bound_ge:
  (∀v k. boundVal k v ⇒ ∀j. k ≤ j ⇒ boundVal j v) ∧
  (∀m k. boundComp k m ⇒ ∀j. k ≤ j ⇒ boundComp j m)
Proof
  Induct >> rw[]
  (* var *)
  >- fs[Once boundVal_cases]
  (* thunk *)
  >- (qpat_x_assum (`boundVal _ _`) mp_tac >>
      rw[Once boundVal_cases] >>
      first_x_assum drule_all >> rw[] >>
      rw[Once boundVal_cases])
  (* force *)
  >- (qpat_x_assum (`boundComp _ _`) mp_tac >>
      rw[Once boundVal_cases] >>
      first_x_assum drule_all >> rw[] >>
      rw[Once boundVal_cases])
     (* lam *)
  >- (qpat_x_assum (`boundComp _ _`) mp_tac >>
      rw[Once boundVal_cases] >>
      first_x_assum drule >> rw[] >>
      rw[Once boundVal_cases])
  (* app *)
  >- (qpat_x_assum (`boundComp _ _`) mp_tac >>
      rw[Once boundVal_cases] >>
      first_x_assum drule_all >> rw[] >>
      first_x_assum drule_all >> rw[] >>
      rw[Once boundVal_cases])
  (* ret *)
  >- (qpat_x_assum (`boundComp _ _`) mp_tac >>
      rw[Once boundVal_cases] >>
      first_x_assum drule >> rw[] >>
      rw[Once boundVal_cases])
  (* seq, letin, pseq, need *)
  >- (qpat_x_assum (`boundComp _ _`) mp_tac >>
      rw[Once boundVal_cases] >>
      first_x_assum drule_all >> rw[] >>
      first_x_assum $ drule_at $ Pos hd >> rw[] >>
      rw[Once boundVal_cases]
      >> metis_tac[])
  >- (qpat_x_assum (`boundComp _ _`) mp_tac >>
      rw[Once boundVal_cases] >>
      first_x_assum drule_all >> rw[] >>
      first_x_assum $ drule_at $ Pos hd >> rw[] >>
      rw[Once boundVal_cases]
      >> metis_tac[])
  >- (qpat_x_assum (`boundComp _ _`) mp_tac >>
      rw[Once boundVal_cases] >>
      first_x_assum drule_all >> rw[] >>
      first_x_assum $ drule_at $ Pos hd >> rw[] >>
      rw[Once boundVal_cases]
      >> metis_tac[])
  >- (qpat_x_assum (`boundComp _ _`) mp_tac >>
      rw[Once boundVal_cases] >>
      first_x_assum drule_all >> rw[] >>
      first_x_assum $ drule_at $ Pos hd >> rw[] >>
      rw[Once boundVal_cases]
      >> metis_tac[])
  >> qpat_x_assum (`boundComp _ _`) mp_tac >>
  rw[Once boundVal_cases] >>
  rw[Once boundVal_cases] >> fs[]
QED

Theorem bound_closed:
  (∀v k u. boundVal 0 v ⇒ substVal v k u = v) ∧
  (∀m k u. boundComp 0 m ⇒ substComp m k u = m)
Proof
  rw[]
  >- (drule (cj 1 bound_ge) >> rw[] >>
      metis_tac[bound_closed_k])
  >> drule (cj 2 bound_ge) >> rw[] >>
  metis_tac[bound_closed_k]
QED

        
(*----------------------------------
                BoundNeed
  ----------------------------------*)
     
Inductive boundNeedVal:
  (∀k n. boundNeedVal k (var n)) ∧
  (∀k c. boundNeedComp k c ⇒ boundNeedVal k (thunk c)) ∧
  (∀k c v. boundNeedComp k c ∧ boundNeedVal k v ⇒ boundNeedComp k (app c v)) ∧
  (∀k c. boundNeedComp k c ⇒ boundNeedComp k (lam c)) ∧
  (∀k v. boundNeedVal k v ⇒ boundNeedComp k (ret v)) ∧
  (∀k v. boundNeedVal k v ⇒ boundNeedComp k (force v)) ∧
  (∀k m n. boundNeedComp k m ∧ boundNeedComp k n ⇒ boundNeedComp k (seq m n)) ∧
  (∀k m1 m2 n. boundNeedComp k m1 ∧ boundNeedComp k m2 ∧ boundNeedComp k n ⇒ boundNeedComp k (pseq m2 m1 n)) ∧
  (∀k v m. boundNeedVal k v ∧ boundNeedComp k m ⇒ boundNeedComp k (letin v m)) ∧
  (∀k m n. boundNeedComp k m ∧ boundNeedComp (SUC k) n ⇒ boundNeedComp k (need m n)) ∧
  (∀k n. n < k ⇒ boundNeedComp k (needvar n)) 
End

Theorem boundNeed_closed_k:
  (∀v k u. boundNeedVal k v ⇒ substNeedVal v k u = v) ∧
  (∀m k u. boundNeedComp k m ⇒ substNeedComp m k u = m)
Proof
  Induct >> rw[] >> (* 8 *)
  pop_assum mp_tac >> rw[Once boundNeedVal_cases, Once substNeedVal_def]
QED

Theorem boundNeed_ge:
  (∀v k. boundNeedVal k v ⇒ ∀j. k ≤ j ⇒ boundNeedVal j v) ∧
  (∀m k. boundNeedComp k m ⇒ ∀j. k ≤ j ⇒ boundNeedComp j m)
Proof
  Induct >> rw[]
  (* var *)
  >- fs[Once boundNeedVal_cases]
  (* thunk *)
  >- (qpat_x_assum (`boundNeedVal _ _`) mp_tac >>
      rw[Once boundNeedVal_cases] >>
      first_x_assum drule_all >> rw[] >>
      rw[Once boundNeedVal_cases])
  (* force *)
  >- (qpat_x_assum (`boundNeedComp _ _`) mp_tac >>
      rw[Once boundNeedVal_cases] >>
      first_x_assum drule_all >> rw[] >>
      rw[Once boundNeedVal_cases])
     (* lam *)
  >- (qpat_x_assum (`boundNeedComp _ _`) mp_tac >>
      rw[Once boundNeedVal_cases] >>
      first_x_assum drule >> rw[] >>
      rw[Once boundNeedVal_cases])
  (* app *)
  >- (qpat_x_assum (`boundNeedComp _ _`) mp_tac >>
      rw[Once boundNeedVal_cases] >>
      first_x_assum drule_all >> rw[] >>
      first_x_assum drule_all >> rw[] >>
      rw[Once boundNeedVal_cases])
  (* ret *)
  >- (qpat_x_assum (`boundNeedComp _ _`) mp_tac >>
      rw[Once boundNeedVal_cases] >>
      first_x_assum drule >> rw[] >>
      rw[Once boundNeedVal_cases])
  (* seq, letin, pseq, need *)
  >- (qpat_x_assum (`boundNeedComp _ _`) mp_tac >>
      rw[Once boundNeedVal_cases] >>
      first_x_assum drule_all >> rw[] >>
      first_x_assum $ drule_at $ Pos hd >> rw[] >>
      rw[Once boundNeedVal_cases]
      >> metis_tac[])
  >- (qpat_x_assum (`boundNeedComp _ _`) mp_tac >>
      rw[Once boundNeedVal_cases] >>
      first_x_assum drule_all >> rw[] >>
      first_x_assum $ drule_at $ Pos hd >> rw[] >>
      rw[Once boundNeedVal_cases]
      >> metis_tac[])
  >- (qpat_x_assum (`boundNeedComp _ _`) mp_tac >>
      rw[Once boundNeedVal_cases] >>
      first_x_assum drule_all >> rw[] >>
      first_x_assum $ drule_at $ Pos hd >> rw[] >>
      rw[Once boundNeedVal_cases]
      >> metis_tac[])
  >- (qpat_x_assum (`boundNeedComp _ _`) mp_tac >>
      rw[Once boundNeedVal_cases] >>
      first_x_assum drule_all >> rw[] >>
      first_x_assum $ drule_at $ Pos hd >> rw[] >>
      rw[Once boundNeedVal_cases]
      >> metis_tac[])
  >> qpat_x_assum (`boundNeedComp _ _`) mp_tac >>
  rw[Once boundNeedVal_cases] >>
  rw[Once boundNeedVal_cases] >> fs[]
QED

Theorem boundNeed_closed:
  (∀v k u. boundNeedVal 0 v ⇒ substNeedVal v k u = v) ∧
  (∀m k u. boundNeedComp 0 m ⇒ substNeedComp m k u = m)
Proof
  rw[]
  >- (drule (cj 1 boundNeed_ge) >> rw[] >>
      metis_tac[boundNeed_closed_k])
  >> drule (cj 2 boundNeed_ge) >> rw[] >>
  metis_tac[boundNeed_closed_k]
QED
        
val _ = export_theory ()
