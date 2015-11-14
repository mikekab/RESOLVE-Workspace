(*
 * This software is released under the new BSD 2006 license.
 * 
 * Note the new BSD license is equivalent to the MIT License, except for the
 * no-endorsement final clause.
 * 
 * Copyright (c) 2007, Clemson University
 * 
 * All rights reserved.
 * 
 * Redistribution and use in source and binary forms, with or without
 * modification, are permitted provided that the following conditions are met:
 * 
 *   * Redistributions of source code must retain the above copyright notice,
 *     this list of conditions and the following disclaimer. 
 *   * Redistributions in binary form must reproduce the above copyright
 *     notice, this list of conditions and the following disclaimer in the
 *     documentation and/or other materials provided with the distribution. 
 *   * Neither the name of the Clemson University nor the names of its
 *     contributors may be used to endorse or promote products derived from
 *     this software without specific prior written permission. 
 * 
 * THIS SOFTWARE IS PROVIDED BY THE COPYRIGHT HOLDERS AND CONTRIBUTORS
 * "AS IS" AND ANY EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT
 * LIMITED TO, THE IMPLIED WARRANTIES OF MERCHANTABILITY AND FITNESS FOR
 * A PARTICULAR PURPOSE ARE DISCLAIMED. IN NO EVENT SHALL THE COPYRIGHT OWNER
 * OR CONTRIBUTORS BE LIABLE FOR ANY DIRECT, INDIRECT, INCIDENTAL, SPECIAL,
 * EXEMPLARY, OR CONSEQUENTIAL DAMAGES (INCLUDING, BUT NOT LIMITED TO,
 * PROCUREMENT OF SUBSTITUTE GOODS OR SERVICES; LOSS OF USE, DATA, OR
 * PROFITS; OR BUSINESS INTERRUPTION) HOWEVER CAUSED AND ON ANY THEORY OF
 * LIABILITY, WHETHER IN CONTRACT, STRICT LIABILITY, OR TORT (INCLUDING
 * NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY OUT OF THE USE OF THIS
 * SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF SUCH DAMAGE.
 * 
 * This software has been developed by past and present members of the
 * Reusable Software Research Groups (RSRG) at Clemson University and
 * The Ohio State University.
 *)


Precis String_Theory;
    uses Integer_Theory;

	--The type of all strings of heterogenous type
	Definition SStr : MType;
	Definition Empty_String : SStr;

	--A function that restricts SStr to the type of all strings of some homogenous
	--type
	Definition Str : MType -> MType;
	--Definition Empty_String_In(T : MType) : Str(T);

	Type Theorem Empty_String_In_All_Strs:
		For all T : MType,
			Empty_String : Str(T);

	Type Theorem All_Strs_In_SStr:
		For all T : MType,
		For all S : Str(T),
			S : SStr;

	--If R is a subset of T, then Str(R) is a subset of Str(T)
	Type Theorem Str_Subsets:
		For all T : MType,
		For all R : Powerset(T),
		For all s : Str(R),
			s : Str(T);

	Definition DeString(s : SStr) : Entity;

	
	Definition (s : SStr) o (t : SStr) : SStr;

	Type Theorem Concatenation_Preserves_Generic_Type:
		For all T : MType,
		For all U, V : Str(T),
			U o V : Str(T);
	Type Theorem DeString_Extracts_Generic_Type:
		For all T : MType,
		For all S : Str(T),
			DeString(S) : Str(T);

	Definition Reverse(s : SStr) : SStr;

	Type Theorem Reverse_Preserves_Generic_Type:
		For all T : MType,
		For all S : Str(T),
			Reverse(S) : Str(T);
	Definition min(m:Z,n:Z):Z;
	Definition max(m:Z,n:Z):Z;
(*
	Theorem min_Expanded_Definition_a:
    	For all m,n:Z,
    		(min(m,n) = m) = (m <= n);

    Theorem min_Expanded_Definition_b:
    	For all m,n:Z,
    		(min(m,n) = n) = (n <= m);

	Theorem max_Expanded_Definition_a:
    	For all m,n:Z,
    		(max(m,n) = m) = (n <= m);

    Theorem max_Expanded_Definition_b:
    	For all m,n:Z,
    		(max(m,n) = n) = (m <= n);
*)

(*	Inductive Definition (alpha:SStr) o (beta:SStr) is
	(i) alpha o Empty_String = alpha;
	(ii) alpha o ext(beta,x) = ext(alpha o beta, x); *)

	Corollary Concatenation_1_a: -- Is_Identity_for(o,Empty_String);
		For all S:SStr,
			Empty_String o S = S;

	Corollary Concatenation_1_b: -- Is_Identity_for(o,Empty_String);
		For all S:SStr,
			S o Empty_String = S;

	Corollary Concatenation_2: -- Is_Associative(o);
		For all S,T,U:SStr,
			S o (T o U) = (S o T) o U;

	Corollary Concatenation_3: -- Is_Right_Cancellative(o)
		For all S,T,U:SStr,
			((S o U) = (T o U)) = (S = T); -- check with file
			

(* Inductive Definition |(alpha:SStr)|:N is
		(i) |Empty_String| = 0;
		(ii) |ext(alpha,x)| = suc(|alpha|); *)

	Definition |(alpha:SStr)|:N; 

	Theorem Str_Length_Expanded_Def_i:
		|Empty_String| = 0;

	Corollary Str_Length_1_a:
		For all alpha:SStr,
			(|alpha| = 0) implies (alpha = Empty_String);

	Corollary Str_Length_1_b:
		For all alpha:SStr,
			 (alpha = Empty_String) implies (|alpha| = 0);
			 
	Corollary Str_Length_1c:
		For all alpha:SStr,
			not(alpha = Empty_String) implies 1 <= |alpha|;

	Corollary Str_Length_2: 
		For all alpha,beta:SStr,
			|alpha o beta| = |alpha| + |beta|;
			
	Corollary Str_Length2_without_Length_Op:
		For all alpha,beta,gamma:SStr,
			alpha o beta = gamma implies |gamma| = |alpha o beta|;
	
	Corollary Str_Length_Lt:
		For all alpha,beta,gamma:SStr,
			|alpha o beta| = |gamma| and 1 <= |beta| implies 1 + |alpha| <= |gamma|;
	
	Corollary Str_Length_2_1: 
		For all alpha,beta,gamma:SStr,
			|alpha o beta| = |gamma| implies |alpha| = |gamma| + (- |beta|);
		
	Corollary Str_Length_3:
		For all alpha,beta,gamma,delta:SStr,
			((alpha o beta) = (gamma o delta) and |beta| = |delta|)
				implies (beta = delta and alpha = gamma);


(*	Definition <(x:Entity)>:Str = (ext(Empty_String,x)); *)
--	Definition <(e : (U : MType))> : Str(U);
	Definition Prime_Str : MType;
	Definition <(e : Entity)> : Prime_Str;
	Type Theorem Prime_Str_is_SSTR:
		For all p : Prime_Str,
			p : SStr;
	
	Type Theorem Stringleton_Preserves_Generic_Type:
		For all T : MType,
		For all e : T,
			<e> : Str(T);
				
	Corollary Singleton_Str_1:
		For all p:Prime_Str,
			not(p = Empty_String);

	Corollary Singleton_Str_2:
		For all p:Prime_Str,
			|p| = 1;
			
	Corollary Singleton_Str_3a: -- Is_Bijective(op<>); Changed from Is_Injective
		For all x,y:Entity,
			(<x> = <y>) = (x = y);

	-- For length comparisons where + is not in the alphabet
	Corollary Prime_Str_Cat_Length_1:
		For all p: Prime_Str,
		For all s: SStr,
			|s| <= |(p o s)|; 
			
	Corollary Prime_Str_Cat_Length_2:
		For all p: Prime_Str,
		For all s: SStr,
		For all n: N,
			|(p o s)| = n implies |s| <= n; 
			
	Corollary Prime_Str_Cat_Length_3:
		For all p,q: Prime_Str,
		For all s,t: SStr,
		For all n: N,
			|(p o s)| = |q o t| implies |s| = |t|; 
	
	Corollary Prime_Str_Cat_Length_4:
		For all p:Prime_Str,
		For all s:SStr,
			1 <= |p o s|;
			
	Corollary Prime_Str_Cat_Length_5: -- delete
		For all p:Prime_Str,
		For all s,t:SStr,
			(|s| + |t|) + 1 = |(s o p) o t|;
(*
	Corollary Prime_Str_Cat_Length_5:
		For all p:Prime_Str,
		For all s:SStr,
		For all n:N,		
			(not(|s| = n)  = (|s| <= n)) = (|(s o p)| <= n);
*)		
(*	Corollary Singleton_Str 4:
		Is_Proper_Class(SStr); *)

(*	Corollary Singleton_Str 6:
		For all alpha:SStr,
		For all x:Entity,
			alpha o x = ext(alpha,x); *)

(*	Inductive Definition Reverse(alpha:SStr):SStr is
	(i) Reverse(Empty_String) = Empty_String;
	(ii) Reverse(ext(alpha,x)) = <x> o Reverse(alpha); *)

	Theorem Reverse_Expanded_Definition_i:
		Reverse(Empty_String) = Empty_String;

	Corollary Reverse_1:
		For all p:Prime_Str,
			Reverse(p) = p;

	Corollary Reverse_2:
		For all alpha,beta:SStr,
			Reverse(alpha o beta) = Reverse(beta) o Reverse(alpha);

	Corollary Reverse_3:
		For all alpha:SStr,
			Reverse(Reverse(alpha)) = alpha;

	Corollary Reverse_4: -- Is_Bijective(Reverse);
		For all alpha,beta:SStr,
			(Reverse(alpha) = Reverse(beta)) = (alpha = beta);

	Corollary Reverse_5:
		For all alpha,beta:SStr,
			Reverse(alpha) = beta implies Reverse(beta) = alpha;

	Corollary Reverse_6: -- Is_Left_Cancellative( o )
		For all S,T,U:SStr,
			((U o S) = (U o T)) = (S = T);

	Corollary Reverse_7:
		For all alpha,beta,gamma,delta:SStr,
			((alpha o beta) = (gamma o delta)) and ((|alpha| = |gamma|) or (|beta| = |delta|))  implies
				(alpha = gamma and beta = delta);

	Corollary Reverse_8:
		For all alpha:SStr,
			|Reverse(alpha)| = |alpha|;

(*	Inductive Definition Prt_Btwn(m:Z,n:Z,alpha:SStr):SStr is
	(i) Prt_Btwn(m,n,Empty_String) = Empty_String);
	(ii) (m <= |alpha| < n) implies Prt_Btwn(m,n,ext(alpha,x)) = ext(Prt_btwn(m,n,alpha));
	(iii) not(m <= |alpha| < n) implies Prt_Btwn(m,n,ext(alpha,x)) = Prt_btwn(m,n,alpha); *)

	Definition Prt_Btwn(m:Z,n:Z,alpha:SStr):SStr;

	Theorem Prt_Btwn_Expanded_Def_i:
		For all m,n:Z,
			Prt_Btwn(m,n,Empty_String) = Empty_String;
			
	Corollary Prt_Btwn_1:
		For all alpha, beta:SStr,
		For all n:Z,
			(|alpha| <= n) and Prt_Btwn(0,n,alpha) = beta implies beta = alpha;

	Corollary Prt_Btwn_2:
		For all alpha:SStr,
		For all m,n:Z,
			(Prt_Btwn(m,n,alpha) = alpha and alpha /= Empty_String) implies (m <= 0 and |alpha| <= n);

	Corollary Prt_Btwn_3:
		For all alpha:SStr,
		For all m,n:Z,
			(Prt_Btwn(m,n,alpha) = Empty_String) = (alpha = Empty_String or |alpha| <= m or n <= m);

	Corollary Prt_Btwn_4:
		For all alpha:SStr,
		For all n:Z,
			Prt_Btwn(n,n,alpha) = Empty_String;

	Corollary Prt_Btwn_5:
		For all alpha:SStr,
		For all m,n:Z,
			|Prt_Btwn(m,n,alpha)| = max( min(n,|alpha|) + -( max(m,0))  ,0);
			
	Corollary Prt_Btwn_6a:
		For all alpha:SStr,
		For all i,m,n:N,
			(|Prt_Btwn(m,n,alpha)| = i and m <= n <= |alpha|) implies i = n + (-m);

	Corollary Prt_Btwn_6b: -- 6a without negatives
		For all alpha:SStr,
		For all i,m,n:N,
			(|Prt_Btwn(m,n,alpha)| = i and m <= n <= |alpha|) implies i <= n;
			
	Corollary Prt_Btwn_6c: -- 6a without negatives
		For all alpha:SStr,
		For all i,m,n:N,
			(m + |Prt_Btwn(m,n,alpha)| = i and m <= n <= |alpha|) implies i = n;
		
	Corollary Prt_Btwn_7:
		For all alpha:SStr,
		For all m,n:Z,
			Prt_Btwn(0,m,alpha) o Prt_Btwn(m,n,alpha) o Prt_Btwn(max(m,n),|alpha|,alpha) = alpha;

	Corollary Prt_Btwn_8:
		For all alpha:SStr,
		For all n:Z,
			Prt_Btwn(0,n,alpha) o Prt_Btwn(n,|alpha|,alpha) = alpha;

	Corollary Prt_Btwn_9_a:
		For all alpha,beta,gamma,delta:SStr,
		For all m,n:Z,
			Prt_Btwn(m,n,alpha o beta) = gamma and Prt_Btwn(m,n,alpha) = delta and n <= |alpha|
				implies gamma = delta;

	Corollary Prt_Btwn_9_b:
		For all alpha,beta,gamma,delta:SStr,
		For all m,n:Z,
			Prt_Btwn(m,n,alpha o beta) = gamma and Prt_Btwn(m + (- |alpha|),n + (- |alpha|),beta) = delta and |alpha| <= m
				implies gamma = delta;

	Corollary Prt_Btwn_10_a:
		For all alpha,beta:SStr,
			Prt_Btwn(0,|alpha|,alpha o beta) = alpha;

	Corollary Prt_Btwn_10_b:
		For all alpha,beta:SStr,
			Prt_Btwn(|alpha|,|alpha o beta|, alpha o beta) = beta;

	Corollary Prt_Btwn_11_a:
		For all alpha,beta:SStr,
		For all x:Entity,
			Prt_Btwn(|alpha|,|alpha| + 1, alpha o <x>) = <x>;

	Corollary Prt_Btwn_11_b:
		For all alpha,beta:SStr,
		For all x:Entity,
			Prt_Btwn(0,1,<x> o alpha) = <x>;

	Corollary Prt_Btwn_11_c:
		For all alpha,beta:SStr,
		For all x:Entity,
			Prt_Btwn(0,|alpha|,alpha o <x>) = alpha;

	Corollary Prt_Btwn_11_d:
		For all alpha,beta:SStr,
		For all x:Entity,
			Prt_Btwn(1,|alpha| + 1,<x> o alpha) = alpha;

	Corollary Prt_Btwn_12_a:
		For all alpha:SStr,
		For all m,n,p,q:Z,
			Prt_Btwn(m,n,Prt_Btwn(p,q,alpha)) = Prt_Btwn(m + p, min(n + p, q), alpha);
			

	Corollary Prt_Btwn_12_b:
		For all alpha:SStr,
		For all n:Z,
			Reverse(Prt_Btwn(n,n+1,alpha)) = Prt_Btwn(n,n+1,alpha);
			
	-- We won't always have "+"
	Corollary Prt_Btwn_12_c:
		For all alpha:SStr,
			Reverse(Prt_Btwn(0,1,alpha)) = Prt_Btwn(0,1,alpha);
(*
-- causes contrad
	Corollary Prt_Btwn_13_a:
		For all alpha:SStr,
		For all m,n:Z,
			Reverse(Prt_Btwn(m,n,alpha)) = Prt_Btwn(|alpha| - n, |alpha| - m, Reverse(alpha));
-- causes contrad
	Corollary Prt_Btwn_13_b:
		For all alpha:SStr,
		For all m,n:Z,
			Prt_Btwn(m,n,Reverse(alpha)) = Reverse(Prt_Btwn(|alpha| - n, |alpha| - m, alpha));
*)

	--Determines if for every pairing of elements from s and t, the given predicate
	--holds
	Definition Is_Universally_Related(s : SStr, t : SStr,
		f : (Entity * Entity) -> B) : B;

(*	Theorem Empty_String_Universally_Related_1:
		For all beta : SStr,
		For all f : (Entity * Entity) -> B,
			Is_Universally_Related(Empty_String, beta, f) = (beta = Empty_String);
*)
	Theorem DeString_Expanded_Definition:
		For all rho: Prime_Str,
			<DeString(rho)> = rho;

	Corollary DeString_1:
		For all x:Entity,
			DeString(<x>) = x;

	Corollary DeString_2:
		For all alpha:SStr,
		For all n:Z,
			1 <= n + 1 <= |alpha| implies <DeString(Prt_Btwn(n, n + 1, alpha))> = Prt_Btwn(n,n+1,alpha);
			
	Corollary DeString_2_no_addition_no_Length:
		For all alpha:SStr,
			not(alpha = Empty_String) implies <DeString(Prt_Btwn(0, 1, alpha))> = Prt_Btwn(0,1,alpha);
			
			
	Definition Is_Substring(a:SStr,b:SStr):B;
	
	Corollary Is_Substring_1a:
		For all a,b:SStr,
			Is_Substring(a,a o b);
			
	Corollary Is_Substring_1b:
		For all a,b:SStr,
			Is_Substring(b, a o b);
	-- Is_Partial_Ordering(Is_Substring)
	--	means it is reflexive, transitive, and antisymmetric,
	
	Corollary Is_Substring_3_reflexive:
		For all a:SStr,
			Is_Substring(a,a);
			
	Corollary Is_Substring_3_transitive:
		For all a,b,c:SStr,
			Is_Substring(a,b) and Is_Substring(b,c) implies Is_Substring(a,c);
	
	-- Will be able to state these as: (not(Is_Substring(a,c)) implies Is_Substring(a, b o c) = Is_Substring(a, b);
	Corollary Is_Substring_3_transitive_contrapositive_a:
		For all a,b,c:SStr,
		For all p:B,
			(not(Is_Substring(a,c)) and Is_Substring(a, b o c) = p ) implies p = Is_Substring(a, b);	
			
	Corollary Is_Substring_3_transitive_contrapositive_b:
		For all a,b,c:SStr,
		For all p:B,
			(not(Is_Substring(a,c)) and Is_Substring(a, c o b) = p ) implies p = Is_Substring(a, b);	
				
	Corollary Is_Substring_3_antisymmetric:
		For all a,b:SStr,
			(Is_Substring(a,b) and Is_Substring(b,a)) = (a = b);
					
	Corollary Is_Substring_4:
		For all a,b:SStr,
			Is_Substring(a,b) implies |a| <= |b|;
	
	Corollary Is_Substring_4_Without_Length_Operator:
		For all a:SStr,		
			Is_Substring(a,Empty_String) = (a = Empty_String);
					
	Corollary Is_Substring_5:
		For all a:SStr,
		For all m,n:N,
			Is_Substring(Prt_Btwn(m,n,a),a);
			
	-- These are specialized versions for Prime_Str
	
	Corollary Is_Substring_Primes_1:
		For all p,s:Prime_Str,		
			(p = s) = Is_Substring(p,s);

	Definition Stringify_Z_Entity: (Z->Entity)->(Z->Prime_Str);
	
	Theorem Stringify_Z_Entity_1: -- (Stringify_Z_Entity(F))(i) = <F(i)>
		For all F:Z->Entity,
		For all G:Z->Prime_Str,
		For all e:Entity,
		For all i:Z,
			Stringify_Z_Entity(F) = G and
			F(i) = e implies
				G(i) = <e>;

	Theorem Z_Entity_Stringify_Composition:
		For all i:Z,
		For all F,G:Z->Entity,
			Eq_Except_At(F,G,i) =
			Eq_Except_At(Stringify_Z_Entity(F),Stringify_Z_Entity(G),i) ;
	
	Definition Stringify_Mod_Z_Entity: (Z * (Z->Entity))->(Z->Prime_Str);
	-- (Stringify_Mod_Z_Entity(m,F))(i) = <F(i mod m)>	
	
	Theorem Stringify_Mod_Z_Entity_1:
		For all i,m:Z,
		For all F,G:Z->Entity,
		For all e:Entity,
			Stringify_Mod_Z_Entity(m,F) = G and
			F(i mod m) = e implies
				G(i mod m) = <e>;
				
	Theorem Mod_Z_Entity_Stringify_Composition:
		For all i,m:Z,
		For all F,G:Z->Entity,
			Eq_Except_At(F,G,i mod m) =
			Eq_Except_At(Stringify_Z_Entity(F),Stringify_Z_Entity(G),i mod m) ;	
					
    Definition Iterated_Concatenation(m : Z, n : Z, F: Z->SStr): SStr;
	
	Theorem Iterated_Concat_of_Prime_Str_Length_1:
		For all i:Z,
		For all n:N,
		For all F:Z->Prime_Str,
			0 <= i and |Iterated_Concatenation(1,i,F)| = n 
				implies n = i;
	
	Theorem Iterated_Concat_of_Prime_Str_Length_2:
		For all n:Z,
		For all F:Z->Prime_Str,
			|Iterated_Concatenation(n,n,F)| = 1;

	Theorem Iterated_Concat_of_Prime_Str_Length_3:
		For all m,n,i:Z,
		For all F:Z->Prime_Str,
			m <= n and |Iterated_Concatenation(m,n,F)| = i implies i = 1 + m + (-n);	
								
	Theorem Iterated_Concat_of_Prime_Str_Length_4_a:
		For all i,j,k:Z,
		For all F:Z->Prime_Str,
			j + 1 <= i and |Iterated_Concatenation(i,j,F)| = k implies k = 0;	
			
	Theorem Iterated_Concat_of_Prime_Str_Length_4_b:
		For all i,j:Z,
		For all s:SStr,
		For all F:Z->Prime_Str,
			j + 1 <= i and Iterated_Concatenation(i,j,F) = s implies s = Empty_String;
	
	-- 	For VCs where <= or + not used	
	Theorem Iterated_Concat_of_Prime_Str_3_c:
		For all s:SStr,
		For all F:Z->Prime_Str,
			Iterated_Concatenation(1,0,F) = Empty_String;
			
	Theorem Iterated_Concat_End_Cat:
		For all m, n: Z,
		For all F: Z->Prime_Str,	
			Iterated_Concatenation(m, n + 1, F) = 
			Iterated_Concatenation(m, n, F) o F(n + 1);

	Theorem Iterated_Concat_Eq_On_Interval_1:
		For all m, n, i: Z,
		For all F,G: Z->Prime_Str,
		Eq_Except_At(F,G,i) and
		(m <= n + 1 <=i) implies
			Iterated_Concatenation(m,n,F) = Iterated_Concatenation(m,n,G);
			
	Theorem Iterated_Concat_Eq_On_Interval_2:
		For all m, n, i: Z,
		For all F,G: Z->Prime_Str,
		Eq_Except_At(F,G,i) and
		(i + 1 <= m <= n) implies
			Iterated_Concatenation(m,n,F) = Iterated_Concatenation(m,n,G);
						
	Corollary Not_Eq_Str_Length:
		For all S,T:SStr,
			|S| /= |T| implies S /= T;

end;