theory Termination

imports Main

begin

function sum :: "nat \<Rightarrow> nat \<Rightarrow> nat"
where
  "sum i N = (if i>N then 0 else i + sum (Suc i) N)"
apply pat_completeness
apply auto
done

termination sum
apply(relation "measure (\<lambda>(i,N).N+1-i)")
apply(simp)+
done

function foo :: "nat \<Rightarrow> nat \<Rightarrow> nat"
where
  "foo i N = ( if i>N 
    then (if  N=0 then 0 else sum 0 (N - 1) )
    else i + sum (Suc i) N ) "
apply pat_completeness
apply simp
done

termination foo
apply(relation "measures [\<lambda>(i,N). N, \<lambda>(i,N).N+1-i]")
apply simp
done




end
