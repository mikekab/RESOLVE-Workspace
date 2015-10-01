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

Definition unionMakesZ (p1: Z, p2: Z) : B;
(* isBinaryPartition is automatically generated
Theorem unionMakesZ_Def:
	For all f: Z->B,
	For all x,y:Z, 	
		f(x) and not(f(y)) implies unionMakesZ(x,y)
*)
		
Theorem CombineParts_Z_Dom:
	For all f,g: Z -> Entity,
	For all p1,p2: Z,
		(unionMakesZ(p1,p2) and f(p1) = g(p1) and f(p2) = g(p2)) implies
			f = g;

--- + Sets
Definition ZSet:Powerset(Z);
Definition ZSetCons(x:Z):ZSet; --auto with P(x) in VC SuchThat(For all x:Z,(x /= S.Top + 1) : Powerset(Z)
Definition isSubsetOrEq:ZSet * ZSet -> B;
Definition isElem: Z * ZSet -> B;
Theorem isSubsetOrEqDef:
	For all i,x,y:Z,
		isElem(i,ZSetCons(x)) implies isElem(i,ZSetCons(y)) = isSubsetOrEq(ZSetCons(x),ZSetCons(y));
		
Definition FR(f:Z->(R:MType),s:ZSet):Z->R; -- partial if s /= Z

Theorem FR_Cons:
	For all F,G: Z->Entity,
	For all x: Z, -- using fact this must be the arg of ZSetCons to ensure it represents a set.
	For all s:ZSet,	
		ZSetCons(x) = s and F(x) = G(x) implies FR(F,s) = FR(G,s);
Definition Union_Z(s1:ZSet, s2:ZSet): B;
-- Union & FR may be auto generated
Theorem CombineParts_Union_FR:
	For all s1,s2:ZSet,
	For all f:Z->Entity,
	For all g:Z->Entity,
		Union_Z(s1,s2) and FR(f,s1) = FR(g,s1) and FR(f,s2) = FR(g,s2) implies f = g; 
		
Theorem CombineParts_Union_Without_FR:
	For all x1,x2:Z,
	For all f:Z->Entity,
	For all g:Z->Entity,
		Union_Z(ZSetCons(x1),ZSetCons(x2)) and f(x1) = g(x1) and f(x2) = g(x2) implies f = g; 

Definition ZSetConB(f:Z->B):ZSet;
Definition ElemOf(i:Z,s:ZSet):B;
Theorem ZSetConB_Def:
	For all x:Z,
	For all f:Z->B,
		f(x) = ElemOf(x,ZSetConB(f));
(*
Theorem Equal_Under_Sub_Domain:
	For all f,g:Z->B,	
	(lambda(k:Z).(f(k) implies g(k) ) = lambda(k:Z).(true) = IsSubsetOrEq(ZSetConsB(f),ZSetConsB(g));		

Theorem FR_With_ConditionalSet:
	For all a,b:Z->B,
	For all f,g:Z->Entity,
		FR(f,ZSetConB(a)) = FR(g,ZSetConB(b)) = (lambda(k:Z).(a(k) implies b(k)) = lambda(k:Z).(true));
*)	
Theorem FR_Def:
	For all f,g: Z -> Entity,
	For all c: Z -> B,
	For all x: Z,	
		FR(f,ZSetConB(c)) = FR(g,ZSetConB(c)) and c(x) implies f(x) = g(x);	
		
Theorem FR_Def_2:
	For all f,g: Z -> Entity,
	For all c: Z -> B,
	For all x: Z,	
	For all e: Entity,
		FR(f,ZSetConB(c)) = FR(g,ZSetConB(c)) and f(x) = e implies (c(x) and (g(x) = e)) = c(x);	

Theorem FR_Def_3:
	For all f,g: Z -> Entity,
	For all x: Z,	
	For all e: Entity,
		FR(f,ZSetCons(x)) = FR(g,ZSetCons(x)) implies f(x) = g(x);	


-- Entering some simple logic theory that may be built in later.

Theorem False_1:
	not(true) = false;
	
Theorem False_2:
	For all p:B,
		not(p) = false implies p = true;

Theorem False_3:
	For all p:B,
		not(p) = true implies p = false;		
end Conditional_Function_Theory;
