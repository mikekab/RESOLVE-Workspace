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
			((S o U) = (T o U)) implies (S = T);

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

	Corollary Str_Length_2: -- will not introduce |_| on its own, see add_ons at end
		For all alpha,beta:SStr,
			|alpha o beta| = |alpha| + |beta|;
			
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
	Definition <(e : Entity)> : SStr;
	
	Type Theorem Stringleton_Preserves_Generic_Type:
		For all T : MType,
		For all e : T,
			<e> : Str(T);

	Corollary Str_Length_Singlton_Cat:
		For all alpha,beta: SStr,
		For all x: Entity, 
			(alpha = <x> o beta) implies (1 + |beta| <= |alpha|);
				
	Corollary Singleton_Str_1:
		For all x:Entity,
			<x> /= Empty_String;

	Corollary Singleton_Str_2:
		For all x:Entity,
			|<x>| = 1;
			
	Corollary Str_Length_Singelton:
		For all alpha: SStr,
		For all x: Entity,
			1 + |alpha| <= |<x> o alpha|;
			
	Corollary Singleton_Str_3: -- Is_Injective(op<>);
		For all x,y:Entity,
			(<x> = <y>) implies (x = y);

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
		For all x:Entity,
			Reverse(<x>) = <x>;

	Corollary Reverse_2:
		For all alpha,beta:SStr,
			Reverse(alpha o beta) = Reverse(beta) o Reverse(alpha);

	Corollary Reverse_3:
		For all alpha:SStr,
			Reverse(Reverse(alpha)) = alpha;

	Corollary Reverse_4: -- Is_Bijective(Reverse); (only stating injectivity)
		For all alpha,beta:SStr,
			(Reverse(alpha) = Reverse(beta)) implies (alpha = beta);

	Corollary Reverse_5:
		For all alpha,beta:SStr,
			Reverse(alpha) = beta implies Reverse(beta) = alpha;

	Corollary Reverse_6: -- Is_Left_Cancellative( o )
		For all S,T,U:SStr,
			((U o S) = (U o T)) implies (S = T);

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
	(* 0 a 1 b 2 c 3 d 4 e 5 *)

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
-- this one is wrong
--	Corollary Prt_Btwn_11_d:
--		For all alpha,beta:SStr,
--		For all x:Entity,
--			Prt_Btwn(1,|alpha| + 1,<x> o alpha) = alpha;

	Corollary Prt_Btwn_12_a:
		For all alpha:SStr,
		For all m,n,p,q:Z,
			Prt_Btwn(m,n,Prt_Btwn(p,q,alpha)) = Prt_Btwn(m + p, min(n + p, q), alpha);
			

	Corollary Prt_Btwn_12_b:
		For all alpha:SStr,
		For all n:Z,
			Reverse(Prt_Btwn(n,n+1,alpha)) = Prt_Btwn(n,n+1,alpha);
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
(*	Definition Is_Universally_Related(s : SStr, t : SStr,
		f : (Entity * Entity) -> B) : B;

	Theorem Empty_String_Universally_Related_1:
		For all beta : SStr,
		For all f : (Entity * Entity) -> B,
			Is_Universally_Related(Empty_String, beta, f) = (beta = Empty_String);
*)
	Theorem DeString_Expanded_Definition:
		For all rho:SStr, -- should be typed as Prime_Str
			|rho| = 1 implies <DeString(rho)> = rho;

	Corollary DeString_1:
		For all x:Entity,
			DeString(<x>) = x;

	Corollary DeString_2:
		For all alpha:SStr,
		For all n:Z,
			1 <= n + 1 <= |alpha| implies <DeString(Prt_Btwn(n, n + 1, alpha))> = Prt_Btwn(n,n+1,alpha);
			
	-- Big Pi (Iterated Concatenation) Parameter of F is implicitly (m,m + n]
	-- Theorems assume it is defined this way: F(m + 1) o ... o F(m + n)
 Definition Iterated_Concatenation(m : Z, n : Z, F: Z->SStr): SStr;
(*
	Theorem Iterated_Concatenation_Expanded_Def_i:
		For all m:Z,
		For all F: Z->SStr,
		For all alpha: SStr,
			Iterated_Concatenation(m,0,F) = Empty_String; 
*)
(*		
	Theorem Iterated_Concatenation_Expanded_Def_ii:
		For all m,n:Z,
		For all F: Z->SStr,
		For all alpha: SStr,
			Iterated_Concatenation(m,suc(n),F) = Iterated_Concatenation(m,n,F) o F(m + 1 + suc(n));
	Corollary Iterated_Concatenation_1:
		For all m,n,p:Z,
		For all F: Z->SStr,
			Iterated_Concatenation(m,n,F) o Iterated_Concatenation(m+n,p,F) = 
				Iterated_Concatenation(m,n+p,F);
*)				
(*	Corollary Iterated_Concatenation_2:
		For all m,n:Z,
		For all F:Z -> SStr,
			|Iterated_Concatenation(m,n,F)| = Summation(m,n,Composition_of_Z_SStr_Z(F,Length));
*)
	---------------------------------------------------------------
	-- Potential Addons                                
	---------------------------------------------------------------
(*
    -- Generate contradiction if negative numbers are used for bounds
	Theorem Iterated_Concatenation_Z_Params_are_N:
		For all m,n:Z,
		For all F: Z->SStr,
		For all alpha: SStr,
			Iterated_Concatenation(m,n,F) = alpha implies m >= 0 and n >= 0;
*)	

	
	Corollary Str_Length_forced_introduction:
		For all alpha,beta,gamma:SStr,
			alpha o beta = gamma implies |gamma| = |alpha| + |beta|;

			
	Corollary Length_Cat_Natural_Ineq_1:
		For all alpha, beta: SStr,
			|alpha| <= |alpha o beta|;

	Corollary Length_Cat_Natural_Ineq_2:
		For all alpha, beta: SStr,
			|beta| <= |alpha o beta|;
			
end;