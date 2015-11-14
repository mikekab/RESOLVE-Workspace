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
 * This sofware has been developed by past and present members of the
 * Reusable Sofware Research Groups (RSRG) at Clemson University and
 * The Ohio State University.
 *)

Theory Conditional_Function_Theory;
	uses Integer_Theory;

--- + Sets
Definition ZSet:Powerset(Z);
Definition ZSetCons(x:Z):ZSet;		
Definition ZSetConB(f:Z->B):ZSet;
Definition ZSetComplement(s:ZSet): ZSet;
Definition Empty_Set: ZSet;
(*
	read "ZSetCons(x) = ZSetConB(c)" as ZSetCons(x) is set of all values x that satisfy c"
*)
Theorem Set_Constructor_False:
	For all x:Z,
	For all c:Z->B,
		(ZSetCons(x) = ZSetConB(c) and not(c(x))) = (ZSetCons(x) = Empty_Set);
-- it should follow that ZSetCons(x) = ZSetConB(c) implies (c(x) or ZSetConB(c) = Empty_Set)
				
Theorem Set_Constructor_Equality: -- for single point functions, (arrays use these)
	For all x,y:Z,
	For all c:Z->B,
		ZSetCons(x) = ZSetConB(c) and c(x) = (x = y) implies ZSetCons(x) = ZSetCons(y);

-- Can't make this iff, consider f = g, and c(x) = not(d(x))
Theorem Condition_Equality:
	For all c,d: Z->B,
	For all f,g,h: Z->Entity,
	For all x,y: Z,
		ZSetCons(x) = ZSetConB(c) and
		ZSetCons(y) = ZSetConB(d) and
		c(x) = d(x) and
		c(y) = d(y) implies
			c = d;				
Definition CF(c:Z->B,f:Z->Entity,g:Z->Entity):Z->Entity;

	
Theorem CF_Implicit_Def_1:
	For all c: Z->B,
	For all f,g,h: Z->Entity,
	For all i: Z,	
		CF(c,f,g) = h and c(i) implies h(i) = f(i);

Theorem CF_Implicit_Def_2:
	For all c: Z->B,
	For all f,g,h: Z->Entity,
	For all i: Z,	
		CF(c,f,g) = h and not(c(i)) implies h(i) = g(i);
		
Corollary CF_1:
	For all c: Z->B,
	For all f: Z->Entity,
		CF(c,f,f) = f;
	
Corollary CF_2a:
	For all c,d,e: Z->B,
	For all f,g,h: Z->MType,
	For all x,y: Z,
		-- f |^ {x : c(x)} = g |^ {x : c(x)} implies CF(d,f,g) = CF(lambda(i:Z).(c(i) or d(i)),f,g);
		ZSetConB(c) = ZSetCons(x) and 
		f(x) = g(x) and
		CF(c,f,g) = h and -- best to make sure f and g are args of a CF first 
		ZSetConB(e) = ZSetCons(y) and 
		e(y) = (c(y) or d(y)) implies
			h = CF(e,f,g);

Corollary CF_3:
	For all c: Z->B,
	For all x,y: Z,
	For all f,g,h: Z->Entity,
		(f = CF(c,g,h)) =
		(
			ZSetConB(c) = ZSetCons(x) and
			f(x) = g(x) and
			ZSetCons(y) = ZSetComplement(ZSetCons(x)) and
			f(y) = h(y)
		);		
		
Corollary CF_3_No_Complement:
	For all c,d: Z->B,
	For all x,y: Z,
	For all f,g,h: Z->Entity,
		(f = CF(c,g,h)) =
		(
			ZSetConB(c) = ZSetCons(x) and
			f(x) = g(x) and
			ZSetConB(d) = ZSetCons(y) and
			d(y) = not(c(y)) and
			f(y) = h(y)
		);	

-- Specialized.  Like argument in CF nested .

Corollary CF_Special_1:
	For all c,d,e: Z->B,
	For all x,y: Z,
	For all f,g: Z->Entity,
		(CF(c,f,CF(d,f,g)) = CF(e,f,g)) =
		(
			ZSetCons(x) = ZSetConB(c) and   -- {x:Z | For all x:Z, c(x)}
			ZSetCons(y) = ZSetConB(e) and
			e(y) = ((c(y) and d(y)) = (c(y) = d(y))) -- For all k:Z, e(k) = c(k) or d(k)
		);
Corollary CF_Special_1_with_or:
	For all c,d,e: Z->B,
	For all x,y: Z,
	For all f,g: Z->Entity,
		(CF(c,f,CF(d,f,g)) = CF(e,f,g)) =
		(
			ZSetCons(x) = ZSetConB(c) and   -- {x:Z | For all x:Z, c(x)}
			ZSetCons(y) = ZSetConB(e) and
			-- y is the set that s.t. c(y) or d(y)
			e(y) = c(y) or d(y) -- For all k:Z, e(k) = c(k) or d(k)
		);
 Corollary Special_Interval_Expansion:
	For all i,j,x:Z,
		(((i <= j) and (j <= x)) or (i <= j and j <= x + 1)) = (i <= j and j <= x + 1);	
		
Theorem Special_Logic_1:
	For all p:B,
		p or true; 	
		
Theorem Special_Logic_2:
	For all p:B,
		(p or false) = p; 
							
Corollary CF_4_a1: -- Without FR
	For all c: Z->B,
	For all f,g,h: Z->Entity,
	For all x:Z,
		(ZSetCons(x) = ZSetConB(c) and f(x) = g(x)) implies CF(c,f,h) = CF(c,g,h);

Corollary CF_4_b1: -- Without FR
	For all c: Z->B,
	For all f,g,h: Z->Entity,
	For all x,y:Z,
		ZSetCons(x) = ZSetConB(c) and 
		ZSetCons(y) = ZSetComplement(ZSetCons(x)) and
		g(y) = h(y) implies
		CF(c,f,h) = CF(c,f,g);
		
Corollary CF_13_a:
	For all c,d: Z->B,
	For all f,g,h,k: Z->Entity,
	For all x:Z,
		-- (for all y: d(y) implies c(y)) implies CF(c,f,CF(d,g,h)) = CF(c,f,h)
		ZSetConB(d) = ZSetCons(x) and
		d(x) = c(x) and CF(c,f,CF(d,g,h)) = k implies
			k = CF(c,f,h);		--d(x) is true by definition., no need for implies.

Corollary CF_13_b:
	For all c,d: Z->B,
	For all f,g,h,k: Z->Entity,
	For all x:Z,
		-- (for all y: d(y) implies c(y)) implies CF(c,f,CF(d,g,h)) = CF(c,f,h)
		ZSetConB(d) = ZSetCons(x) and
		(d(x) = not(c(x))) and CF(c,f,CF(d,g,h)) = k implies
			k = CF(c,f,g);		

Corollary CF_14_a:
	For all c: Z->B,
	For all f,g,h: Z->Entity,
		CF(c,f,CF(c,g,h)) = CF(c,f,h);		
		
Corollary CF_14_b: -- Bill may cover this with Cor. 9
	For all c: Z->B,
	For all f,g,h: Z->Entity,
		CF(c,CF(c,f,g),h) = CF(c,f,h);
		
Definition ElemOf(i:Z,s:ZSet):B;
Theorem ZSetConB_Def:
	For all x:Z,
	For all f:Z->B,
		f(x) = ElemOf(x,ZSetConB(f));


end Conditional_Function_Theory;
