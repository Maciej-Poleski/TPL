theory ToyArith

imports Main (* tym razem importujemy cale Main *)

begin

(* pierwszy prosy lemat *)
lemma "Suc 0 = 1"
(* to jest tylko kwestia notacji wiec simp powinien wystarczyc *)
apply(simp)
done


lemma "(m ~= (n::nat) ) ==> (  n < m | n > m )"
(*tutaj simp nie wystarcza, uzywamy strategii arith, ktora niezle sobie radzi z twierdzeniami arytmetyki, konieczne bylo doprecyzowanie typow zmiennych aby bylo wiadomo ze mowimy o liczbach  *)
apply(arith)
done

(* cos trudniejszego dla arith *)
lemma "ALL x. EX y. x+y> x+x -->  x=(0::nat)"
apply(arith)
done


(* funkcje hd, tl zwracaja odpowiednio glowe i ogon listy *)
lemma hd_Cons_tl[simp]: "xs ~= [] ==> hd xs # tl xs = xs"
(* indukcja na xs sie powiedzie ale nie jest konieczna, wystarczy rozwazyc przypadki *)
apply (case_tac xs)
(* rozbicie nastapilo zgodnie z rekurencyjna definicja typu danych *)

(* pierwszy cel jest trywialny *)
apply(simp)

(* w Isabelle->Setting wlacz TraceSimplifier, jesli juz miales wlaczony to wyczysc bufor trace (Buffers-> trace) *)
apply(simp)
(* udalo sie, sprobuj sie przesledzic w buforze trace uproszczenia wykonane przez strategie simp *)
done

(* przyklad twierdzenia z if-then-else *)
lemma " ALL xs. if xs = [] then rev xs = [] else rev xs ~= []"
(* strategia ktora zamienia if-then-else na implikacje: *)
apply(split split_if)
(* teraz juz latwo *)
apply(simp)
done

(* kolejny przyklad, uwaga na nawiasowanie *)

lemma "if xs = [] then ys ~= [] else ys = [] ==> xs @ ys ~= []"
apply(split split_if_asm)
(* strategia podobna do poprzedniej, ale rozbija od razu na podzadania *)

apply(simp)
apply(simp)
done

end