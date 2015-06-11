theory Sort

imports Main 

begin

fun ins::"nat ⇒ nat list ⇒ nat list" where
  "ins x [] = [x]" |
  "ins x (y#ys) = (if x≤y then x # y # ys else y # (ins x ys))"

(* zdefiniuj poprawnie funkcje sort *)
fun  sort::"nat list ⇒ nat list" where
  "sort [] = []" |
  "sort (x#xs) = ins x (sort xs)"

(* definicja predykatu sorted *)
fun sorted :: "nat list ⇒ bool" where 
"sorted [] = True" |
"sorted [x]= True" |
"sorted (x#(y#xs)) =  ( (x <= y) &  sorted (y#xs )) "

lemma sort_tail: "sorted(a # list) ⟹ sorted(list)"
apply(case_tac list)
apply(simp)
apply(simp)
done

lemma ins_sort: "sorted(list) ⟶ sorted(ins x list)"
apply(induct_tac "list")
apply(auto simp add: sort_tail)
apply(case_tac list)
apply(auto)
done

fun rem:: "nat ⇒ nat list ⇒ nat list" where
"rem n []= []"|
"rem n (x#xs)= (if (n=x) then xs else  (x#(rem n xs)))"

(* pierwsze twierdzenie do udowodnienia *)


theorem "sorted(sort x)"
  apply(induct_tac x)
  apply(simp)
apply(simp add: ins_sort)
done

(* definicja funkcji pomocniczej dla predykatu sprawdzajacego czy podane listy sa swoimi permutacjami, funkcja probuje usunac element z listy, zwraca wartosc typu nat list option *)
(* typ option dziala jak typ Maybe w Haskellu, przyjmuje wartosci "Some wartosc" lub "None", w dowodach przydaje sie strategia "split option.split" *)

fun tryDel::"nat ⇒ nat list ⇒ nat list option"
where 
"tryDel x []= None" |
"tryDel x (y#ys)= (if (x=y) then (Some ys) else (case (tryDel x ys) of
  None ⇒ None |
  Some res ⇒ Some (y#res)))"

(* definicja predykatu sprawdzajacego czy podane listy sa swoimi permutacjami *)

fun perm::"nat list ⇒ nat list ⇒ bool"
where 
"perm [] ys= (if (ys=[]) then True else False)"|
"perm (x#xs) ys = ( case (tryDel x ys) of
  None ⇒ False |
  Some res ⇒  perm xs res)"

(* do rozbicia case na przypadki przyda sie strategia case_tac *)

lemma del_ins: "tryDel a (ins a unk) = Some unk"
apply(induct_tac unk)
apply(simp)
apply(auto)
done

(* drugie twierdzenie do udowodnienia *)
theorem "perm  xs ( sort xs)"
apply(induct_tac xs)
apply(simp)
apply(auto simp add: del_ins)
done

fun merge::"nat list ⇒ nat list ⇒ nat list" where
"merge [] b = b" |
"merge a [] = a" |
"merge (a#as) (b#bs) = (if a≤b then a # merge as (b#bs) else b # merge (a#as) bs)"


function (sequential) mergeSort::"nat list ⇒ nat list" where
"mergeSort [] = []" |
"mergeSort [x] = [x]" |
"mergeSort l = merge (mergeSort (take ((length l) div 2) l)) (mergeSort (drop ((length l) div 2) l))"
apply(pat_completeness)
apply(auto)
done

termination mergeSort
apply(relation "measures[λ (list::nat list).(size list)]")
apply(auto)
done

fun less::"nat ⇒ nat list ⇒ bool" where
"less n [] = True" |
"less n (x#r) = (if (n>x) then False else less n r)"

lemma "first_in_sorted": "sorted(a # r) ⟹ less a r"
apply(induct r rule: sorted.induct)
apply(auto)
done

lemma sorted_prep: "sorted r & less a r ⟹ sorted(a # r)"
apply(auto)
apply(induction r rule: sorted.induct)
apply(simp)
apply(simp)
apply(split split_if_asm)
apply(simp)
apply(simp)
apply(auto)
apply(split split_if_asm)
apply(simp)
apply(simp)
done

lemma first_in_merge: "less n as & less n bs ⟹ less n (merge as bs)"
apply(auto)
apply(induct as bs rule:merge.induct)
apply(auto)
done

lemma less_is_transitive: "a≤b & less b bs ⟹ less a bs"
apply(auto)
apply(induct bs rule:less.induct)
apply(auto)
apply(split split_if_asm)
apply(auto)
done

lemma almost_sorted1: "sorted(a#as) & sorted(b#bs) & a≤b & sorted(merge as (b#bs)) ⟹ sorted(a # merge as (b#bs))"
apply(auto)
apply(rule sorted_prep)
apply(auto)
apply(rule first_in_merge)
apply(auto simp add: first_in_sorted)
apply(rule less_is_transitive)
apply(auto simp add: first_in_sorted)
done

lemma almost_sorted2: "sorted(a#as) & sorted(b#bs) & b≤a & sorted(merge (a#as) bs) ⟹ sorted(b#merge (a # as) bs)"
apply(auto)
apply(rule sorted_prep)
apply(auto)
apply(rule first_in_merge)
apply(auto)
apply(rule less_is_transitive)
apply(auto simp add: first_in_sorted)
done

lemma merge_sorted_with_pre: "sorted(a) & sorted(b) & less x a & less x b ⟹ sorted(x # merge a b)"
apply(auto)
apply(induction a b rule: merge.induct)
apply(simp)
apply(simp only:sorted_prep)
apply(simp)
apply(split split_if_asm)
apply(simp)
apply(simp)
apply(auto)
apply(split split_if_asm)
apply(auto)
apply(split split_if_asm)
apply(auto)
apply(rule almost_sorted1)
apply(auto)
apply(simp add:sort_tail)
apply(split split_if_asm)
apply(auto)
apply(split split_if_asm)
apply(auto)
apply(split split_if_asm)
apply(auto)
apply(split split_if_asm)
apply(auto)
apply(rule almost_sorted2)
apply(auto)
apply(simp add:sort_tail)
done

lemma merge_sorted: "sorted(a::nat list) & sorted (b::nat list) ⟹ sorted(merge a b)"
apply(auto)
apply(induct a b rule: merge.induct)
apply(simp)
apply(simp)
apply(auto)
apply(rule merge_sorted_with_pre)
apply(auto simp add: first_in_sorted)
apply(simp only:sort_tail)
apply(rule less_is_transitive)
apply(auto simp add: first_in_sorted)
apply(rule almost_sorted2)
apply(auto)
apply(frule_tac list=bs in sort_tail)
apply(simp)
done

theorem "sorted(mergeSort(list))"
apply(induct list rule: mergeSort.induct)
apply(simp)
apply(simp)
apply(auto simp add: merge_sorted)
done

lemma remove_selected: "tryDel a (mergeSort (a # list)) = Some (mergeSort list)"
apply(induct list rule: mergeSort.induct)
apply(simp,simp)

oops

lemma "perm (a@b) (merge a b)"
apply(induct a b rule: merge.induct)
apply(auto)
oops

lemma "perm list (merge (take n list) (drop n list))"
apply(induct list rule: perm.induct)
oops

theorem "perm list (mergeSort list)"
apply(induct list rule: tryDel.induct)
apply(auto)
oops

(* Ile jest wystąpień c w liście *)
fun count::"nat list ⇒ nat ⇒ nat" where
"count [] _ = 0" |
"count (a#b) c = ((if (a=c) then 1 else 0) + (count b c))"

(* Czy obiekty wymienione w (a#b) występują w tych samych ilościach w l1 i l2 *)
fun checkTail::"nat list ⇒ nat list ⇒ nat list ⇒ bool" where
"checkTail [] _ _ = True" |
"checkTail (a#b) l1 l2 = (if count l1 a = count l2 a then checkTail b l1 l2 else False)"

(* Czy a i b mają tą samą zawartość (z dokładnością do kolejności) *)
fun (sequential) eqContent::"nat list ⇒ nat list ⇒ bool" where
"eqContent a b = ((length a = length b) & (checkTail a a b))"

lemma count_step: "count (a#b) a = 1 + count b a"
apply(auto)
done

lemma length_empty1: "length (merge a []) = length a"
 using [[simp_trace_new]]
apply(induct_tac a)
apply(auto)
done

lemma length_empty2: "length (merge [] a) = length a"
 using [[simp_trace_new]]
apply(auto)
done

lemma length_sum: "length (merge a b) = length a + length b"
 using [[simp_trace_new]]
apply(induct a b rule: merge.induct)
apply(simp,simp)
apply(auto)
done

(* Czemu użycie zawsze zapętla? *)
lemma mergeSort_length: "length list = length (mergeSort list)"
apply(induct list rule: mergeSort.induct)
apply(auto simp add: length_sum)
done

lemma empty_list_count: "(∀ x. count list x = 0) ⟹ (list = [])"
 using [[simp_trace_new]]
apply(case_tac list)
apply(simp)
apply(auto)
apply(split split_if_asm)
apply(auto)
done

lemma empty_checkTail: "y=[] ⟹ checkTail x [] y"
apply(auto)
apply(induct_tac x)
apply(simp)
apply(simp)
done

lemma count_lemma: "( ∀x. count a x = count b x) ⟹ checkTail x a b"
apply(induct_tac x)
apply(auto)
done

lemma count_merge: "count (merge l1 l2) x = count l1 x + count l2 x"
 using [[simp_trace_new]]
apply(induction l1 l2 rule: merge.induct)
apply(auto)
done

lemma count_cat: "count l1 x + count l2 x = count ((l1::nat list) @ (l2::nat list)) x "
apply(induct_tac l1)
apply(auto)
done


lemma count_mergeSort: "count (mergeSort l1) x = count l1 x"
 using [[simp_trace_new]]
apply(induction l1 rule: mergeSort.induct)
apply(simp,simp)
apply(simp add:count_merge)
apply(simp add:count_cat)
done

theorem "eqContent list (mergeSort list)"
 using [[simp_trace_new]]
apply(auto)
apply(rule mergeSort_length)
apply(rule count_lemma)
apply(simp add: count_mergeSort)
done
