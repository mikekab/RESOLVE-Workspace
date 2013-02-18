(*
 * This softare is released under the new BSD 2006 license.
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

Precis Integer_Theory;
    uses Boolean_Theory, Set_Theory;

	(* Note that the type Z is built-in.  No need to introduce it here. *)

	Definition N : Powerset(Z);

	Definition 0: N;
	Definition 1: N;

	Definition z : Z;

	Type Theorem N_Subset_of_Z:
		For all n : N,
			n : Z;

    Definition neg: Z -> Z;

    Definition suc: Z -> Z;

    --------------------------------------------------------------

    Definition (i: Z) + (j: Z): Z = 0;

    Definition (i: Z) - (j: Z): Z = 0;

    Definition (i: Z) * (j: Z) : Z = 0;

    Definition (i: Z) ** (j: Z) : Z = 0;

    Definition (i: Z) / (j: Z) : Z = 0;

    Definition (i: Z) mod (j: Z) : Z = 0;

    Definition (i: Z) rem (j: Z) : Z = 0;

    Definition (i: Z) div (j: Z) : Z = 0;

    Definition (i: Z) <= (j: Z) : B = true;

    Definition (i: Z) >= (j: Z) : B = true;

    Definition (i: Z) < (j: Z) : B = true;

    Definition (i: Z) > (j: Z) : B = true;

    Definition |(i: Z)| : Z = 0;

    Definition (i: Z) .. (j: Z) : Set(Z) = Empty_Set;

	Definition Sum(a : Z, s : Set(Z)) : Z;

    Definition Summation(s: Set(Z), f: Z -> Z) : Z = 0;

	Definition isEven(i : Z) : B = true;

end Integer_Theory;
