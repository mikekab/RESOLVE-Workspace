Realization Obvious_Writing_Realiz (Operation Write_Entry(evaluates E: Entry);)
		for Writing_Capability of Stack_Template;

	Procedure Write(clears S: Stack);
		Var Next_Entry: Entry;
		Var D: Integer;

		D := Depth(S);
		While (D /= 0)
			changing S, Next_Entry, D;
			maintaining D = |S|;
			decreasing |S|;
		do
			Pop(Next_Entry, S);
			Write_Entry(Next_Entry);
			D := Depth(S);
		end;
	end Write;
end Obvious_Writing_Realiz;