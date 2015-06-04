theory ToyList (*nazwa teorii/modulu powinna sie zgadzac z nazwa pliku*)

imports Main (*importowane teorie/moduly zwykle importujemy Main, ktory zawiera podstawowe typy danych i ich wlasnosci*)
(* toria PreList to odopowiednik main z usunietymi definicjami listy *)

begin
(* zaczynamy *)
datatype 'a list0 = Nil0 | Cons0 'a "'a list0"
(* deklaracja typu algebraicznego parametryzowanego, jeden konstruktor nullarny - Nil0 i jeden binarny Cons0 *)

(* mozemy dodac alternatywne zapisy konstruktorow *)
datatype 'a list = Nil ("[]")
  | Cons 'a "'a list" (infixr "#" 65)
(* czyli zamiast "Nil" mozemy pisac "[]" oraz uzywac infixowego zapisu dla Cons*)
(* 65 oznacza priorytet infixowego konstruktora #, ostatnia litera infixr wskazuje na prawostronna lacznosc operatora *)



(* tutaj nastepuja definicja funkcji app*)
(*podobnie jak dla konstruktorow dodajemy notacje infixowa *)
fun app:: "'a list => 'a list => 'a list"  (infixr "@" 65) where
"app [] ys = ys" |
"app (x # xs) ys = x #(app xs ys)"


(*deklaracja funckji rev na listach  *)
fun rev :: "'a list => 'a list" where
"rev [] = []" |
"rev (x # xs)= app (rev xs) (x # [])"

(* powyzsze rownosci wraz z wszystkimi mozliwymi podstawieniami staja sie czescia  budowanej teorii*)

(*przyklad wywolania funkcji *)
value "rev (True # False # [])"
(* True i False sa stalymi zdefiniowanymi w teorii PreList *)
value "rev (a # b # c # xs)"



(* formulujemy pierwszy lemat *)
lemma app_Nil: " app xs [] = xs"
(* jestesmy w trybie dowodowym, w oknie goals pojawiaja sie cele do udowodnienia *)
(* bedziemy dowodzic indukcyjnie ze wzgledu na xs *)
apply(induct_tac xs) 
using [[simp_trace_new]]
(* teraz mamy dwa cele baze indukcji i krok indukcyjny *)
(* baza wynika wprost z definicji app., uzywamy strategii simp, ktora probuje dopasowac pierwszy z celow do znanych faktow *)
apply(simp)
(* teraz powinnismy po prawej stronie dwukrotnie wykorzytac definicje # oraz uzyc zalozenia indukcyjnego i aksjomatow rownosci, na razie sie nie rozdrabniamy wszystko zrobi za nas strategia simp*)
apply(simp)

(*dowod skonczony*)
done

(* naszemy lematowi nadalismy nazwe, mozemy go teraz zobaczyc za pomoca ponizszej instrukcji *)

thm app_Nil


(* sprobujmy pokazac takie twierdzenie: *)
theorem "rev (rev xs) = xs"
(*narzuca sie indukcja na xs *)
apply(induct_tac xs)

(*baza jest prosta *)
apply(simp)
(* sprobujmy krok *)
apply(simp)
(* nie wystarczylo, mozcniejsza strategia (auto) rowniez nie pomaga *)
(* przerwiemy na razie dowod i pokazemy kolejny lemat *)
oops


(* [simp] oznacza ze rownosc, z lematu ma byc automatycznie stosowana przez strategie simp *) 
lemma rev_app [simp]:" rev ( app xs ys) = app (rev ys) (rev xs)"
(* indukcja na xs *)
apply(induct_tac xs)

apply(simp)
(* tym razem baza nie jest trywialna, ale mamy na szczescie lemat app_Nil *)
apply(simp add:app_Nil)

(*pozostal krok indukcyjny *)
apply(simp)
(* widac, ze potrzebna jest lacznosc app, przerywamy dowod *)
oops


(* i dowodzimy lacznosc app *)
lemma app_assoc [simp]:"app (app xs ys) zs= app xs (app ys zs)"
apply(induct_tac xs)
apply(simp)
apply(simp)
done

(* sprobujmy teraz dowiesc rev_app *)
lemma rev_app [simp]:"rev (app xs ys) = app (rev ys) (rev xs)"
apply(induct_tac xs)
apply(simp add:app_Nil)

apply(simp)
(* nie musimy jawnie wkazywac na lemat app_assoc bo przy jego postawieniu uzylismy [simp] *)
done


(*wrocmy do twierdzenia *)
theorem rev_rev [simp]: "rev (rev xs) = xs"
apply(induct_tac xs)
apply(simp)
apply(simp)
done

(*udowodnione, od tej pory rownosc z twierdzenia bedzie uzywana do upraszczania wyrazen *)

thm rev_rev

(* uwaga na [simp] przy lematach i twierdzeniach: *)
(* poza ewidentnymi przypadkami lepiej nie uzywac, nietrudno zapetlic strategie simp *)

end


