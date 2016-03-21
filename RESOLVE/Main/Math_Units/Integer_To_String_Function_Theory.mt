Precis Integer_To_String_Function_Theory;
	uses String_Theory, Integer_Domain_Function_Theory;

	-- Stringifies elements and concatenates
	-- n is an offset value representing the length of the range value.
	-- lowest accessed index is m
	-- highest accessed index is m + n - 1 
    Definition Iterated_Concatenation(m : Z, n : Z, F: Z->Entity): SStr;
	
	Theorem Iterated_Concat_of_Prime_Str_Length_1:
		For all m,n:Z,
		For all F:Z->Entity,
			(n <= 0) = (Iterated_Concatenation(m,n,F) = Empty_String);
			
	Theorem Iterated_Concat_of_Prime_Str_Length_2:
		For all m,n:Z,
		For all F:Z->Entity,
			(0 <= n) = (|Iterated_Concatenation(m,n,F)| = n);
			
	Theorem Iterated_Concat_of_Prime_Str_Contents_1:
		For all m:Z,
		For all F:Z->Entity,
			Iterated_Concatenation(m,1,F) = <F(m)>;
			
	Theorem Iterated_Concat_Pre_Cat:
		For all m, n: Z,
		For all F: Z->Entity,	
			(1 <= n) implies
				Iterated_Concatenation(m, n, F) = 
				<F(m)> o Iterated_Concatenation(m + 1 ,n + (-1) ,F);

	Theorem Iterated_Concat_Pre_Cat_no_Negation:
		For all m, n: Z,
		For all F: Z->Entity,	
			(0 <= n) implies
				Iterated_Concatenation(m, n + 1, F) = 
				<F(m)> o Iterated_Concatenation(m + 1 ,n ,F);
				
	Theorem Iterated_Concat_Post_Cat:
		For all m, n: Z,
		For all F: Z->Entity,	
			(1 <= n) implies
				Iterated_Concatenation(m, n, F) = 
				Iterated_Concatenation(m, n + (-1), F) o <F(m + n + -1)>;

(*	Theorem Iterated_Concat_Post_Cat_1_idx:
		For all n: Z,
		For all F: Z->Entity,	
			(1 <= n) implies
				Iterated_Concatenation(1, n, F) = 
				Iterated_Concatenation(1, n + (-1), F) o <F(n)>;
*)				
	Theorem Iterated_Concat_Post_Cat_no_Negation:
		For all m, n: Z,
		For all F: Z->Entity,	
			(0 <= n) implies
				Iterated_Concatenation(m, n + 1, F) = 
				Iterated_Concatenation(m, n, F) o <F(m + n)>;
				
	Theorem Iterated_Concat_Eq_On_Interval_1:
		For all m, n, i: Z,
		For all F: Z->Entity,
		For all E:Entity,
		(i + 1 <= m) implies 
			Iterated_Concatenation(m,n,Store(F,i,E)) = Iterated_Concatenation(m,n,F);
			
	Theorem Iterated_Concat_Eq_On_Interval_2:
		For all m, n, i: Z,
		For all F: Z->Entity,
		For all E: Entity,
		(m + n <= i) implies
			Iterated_Concatenation(m,n,Store(F,i,E)) = Iterated_Concatenation(m,n,F);
			
end Integer_To_String_Function_Theory;