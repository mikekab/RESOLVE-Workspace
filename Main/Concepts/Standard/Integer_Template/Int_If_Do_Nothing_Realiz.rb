Realization Int_If_Do_Nothing_Realiz for Int_Do_Nothing_Capability of Integer_Template;
	uses Std_Boolean_Fac;

	Procedure Do_Nothing(restores I: Integer);
		Var J: Integer;

		If (Is_Zero(I)) then
			I :=: J;
		else
			If (Greater(I, J)) then
				Increment(I);
				Decrement(I);
			end;
		end;
	end Do_Nothing;
end Int_If_Do_Nothing_Realiz;
