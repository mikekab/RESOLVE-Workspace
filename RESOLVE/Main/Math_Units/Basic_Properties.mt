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
 
Precis Basic_Properties;

Definition (a : B) implies (b : B) : B;

Definition Is_Bijective(f : (D : SSet) -> (R : SSet)) : B;
Definition Is_Associative(f : (D : SSet) -> (R : SSet)) : B;
Definition Is_Commutative(f : (D : SSet) * D -> D) : B = 
	For all x, y : D,
		f(x, y) = f(y, x);
Definition Is_Right_Cancelative(f : (D : SSet) -> (R : SSet)) : B;
Definition Is_Total_Ordering(f : (D : SSet) -> (R : SSet)) : B;

Definition Is_Preserved_by(f : (D : SSet) -> (R : SSet), g : D -> B) : B;

Definition Is_Right_Identity_for(f : (D : SSet) * D -> D, i : D) : B;
Definition Is_Left_Identity_for(f : (D : SSet) * D -> D, i : D) : B;
Definition Is_Identity_for(f : (D : SSet) * D -> D, i : D) : B;
Definition Is_Factorable_for(f : (D : SSet) * D -> D, i : D) : B;

Definition Is_Homomorphism_for(f : (D : SSet) * D -> D, g : D -> D) : B;
Definition Is_Inverse_for(f : (D : SSet) * D -> D, g : D -> D) : B;

Definition Is_Monoid(D : SSet, i : D, f : D * D -> D) : B;
Definition Is_Abelian_Monoid(D : SSet, i : D, f : D * D -> D) : B;
Definition Is_Abelian_Group(D : SSet, i : D, f : D * D -> D, g : D -> D) : B;

-----------------------------------------------------------------------------------------
Definition Is_Transitive(f : (D : SSet) * D -> B) : B;
Theorem Is_Transitive_def:
	For all D:SSet,
	For all f:(D * D)->B,
	For all x,y,z:D,
		(Is_Transitive(f) and f(x,y) and f(y,z)) implies f(x,z);
		
Definition Is_Total(f : (D : SSet) * D -> B) : B;
Theorem Is_Total_def:
	For all D:SSet,
	For all f:(D * D)->B,
	For all x,y:D,
	For all p,q:B,
		Is_Total(f) and f(x,y) = p and f(y,x) = q implies (p or q);
		
Definition Is_Antisymmetric(f : (D : SSet) * D -> B) : B;
Theorem Is_Antisymmetric_def:
	For all D:SSet,
	For all f:(D * D)->B,
	For all x,y:D,
		Is_Antisymmetric(f) and f(x,y) and f(y,x) implies x = y;
end Basic_Properties;