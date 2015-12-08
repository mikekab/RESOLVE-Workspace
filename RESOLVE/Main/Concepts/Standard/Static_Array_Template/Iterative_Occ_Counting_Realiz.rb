Realization Iterative_Occ_Counting_Realiz (
            Operation Equal(restores X,Y: Entry): Boolean;
            ensures Equal = (X = Y);
    ) for Occurence_Count_Capability of Static_Array_Template;
    Procedure Occ_Count(restores A: Static_Array; restores key: Entry):Integer;
        Var Temp: Entry;
        Var idx: Integer;
        Var loopCt: Integer;
        Occ_Count := 0;
        idx := Lower_Bound;
        Decrement(idx);
        While (idx + 1 <= Upper_Bound)
        	changing A,Temp,idx,Occ_Count;
            maintaining 
            Occ_Count = 
            	Occ_Ct_In_Range(A,key,Lower_Bound,idx) and
            Lower_Bound + (-1) <= idx and
            Occ_Count <= loopCt and
            idx <= Upper_Bound and
            #A = A;
            decreasing Upper_Bound + (-idx);
        do
        	Increment(idx);
        	Increment(loopCt);
            Swap_Entry(A,Temp,idx);
            if (Equal(key,Temp)) then
                Occ_Count := Occ_Count + 1;
            end;
            Swap_Entry(A,Temp,idx);
            
        end;
    end Occ_Count;
end Iterative_Occ_Counting_Realiz;