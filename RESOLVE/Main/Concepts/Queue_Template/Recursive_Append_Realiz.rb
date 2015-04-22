Realization Recursive_Append_Realiz for Append_Capability of Queue_Template;
    Recursive Procedure Append(updates P: Queue; clears Q: Queue);
		decreasing |Q|;

		Var E: Entry;
		Var Len: Integer;
		
		Len := Length(Q);
		If ( Is_Not_Zero(Len) ) then
			Dequeue(E,Q);
			Enqueue(E,P);
			Append(P,Q);
		end;
	end Append;
end Recursive_Append_Realiz;