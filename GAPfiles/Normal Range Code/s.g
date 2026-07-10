CandidateOrders := function(G)
    local expG, candidates, d;
    expG := Exponent(G);
    candidates := [];
    for d in DivisorsInt(Order(G)) do
        if d < Order(G) and d mod expG = 0 then
            Add(candidates, d);
        fi;
    od;
    return candidates;
end;


SubgroupsByOrder := function(G)
    local allSubs, buckets, s, o;
    allSubs := AllSubgroups(G);
    buckets := rec();
    for s in allSubs do
        o := String(Order(s));
        if IsBound(buckets.(o)) then
            Add(buckets.(o), s);
        else
            buckets.(o) := [s];
        fi;
    od;
    return buckets;
end;


CoversGroup := function(subs, allEltsList, n)
    local covered, count, s, e, pos;
    covered := BlistList([1 .. n], []);
    count := 0;
    for s in subs do
        for e in AsSet(s) do
            pos := PositionSorted(allEltsList, e);
            if not covered[pos] then
                covered[pos] := true;
                count := count + 1;
            fi;
        od;
        if count = n then
            return true;
        fi;
    od;
    return false;
end;


HasEqualCovering := function(G)
    local candidates, buckets, allEltsList, n, d, key;

    if IsCyclic(G) then
        return false;
    fi;

    candidates := CandidateOrders(G);
    if Length(candidates) = 0 then
        return false;
    fi;

    buckets     := SubgroupsByOrder(G);
    allEltsList := AsSortedList(G);
    n           := Length(allEltsList);

    for d in candidates do
        key := String(d);
        if IsBound(buckets.(key)) then
            if CoversGroup(buckets.(key), allEltsList, n) then
                return true;
            fi;
        fi;
    od;

    return false;
end;

ShowCovering := function(G)
    local candidates, buckets, allEltsList, n, d, key, subs, i;

    Print("\n");
    Print("============================================================\n");
    Print("Group    : ", StructureDescription(G), "\n");
    Print("Order    : ", Order(G), "\n");
    Print("Exponent : ", Exponent(G), "\n");

    if IsCyclic(G) then
        Print("Result   : CYCLIC — no covering exists (Theorem 1)\n");
        Print("============================================================\n\n");
        return fail;
    fi;

    candidates := CandidateOrders(G);

    if Length(candidates) = 0 then
        Print("Result   : No valid candidate orders found — no equal covering\n");
        Print("============================================================\n\n");
        return false;
    fi;

    buckets     := SubgroupsByOrder(G);
    allEltsList := AsSortedList(G);
    n           := Length(allEltsList);

    for d in candidates do
        key := String(d);
        if IsBound(buckets.(key)) then
            subs := buckets.(key);
            if CoversGroup(subs, allEltsList, n) then
                Print("Result   : *** EQUAL COVERING FOUND ***\n");
                Print("------------------------------------------------------------\n");
                Print("Covering subgroup order : ", d, "\n");
                Print("Number of subgroups     : ", Length(subs), "\n");
                Print("------------------------------------------------------------\n");
                for i in [1 .. Length(subs)] do
                    Print("  Subgroup ", i, " : ", StructureDescription(subs[i]), "\n");
                    Print("  Elements  : ", AsSet(subs[i]), "\n");
                    Print("\n");
                od;
                Print("============================================================\n\n");
                return true;
            fi;
        fi;
    od;

    Print("Result   : No equal covering exists for this group\n");
    Print("============================================================\n\n");
    return false;
end;


ScanRange := function(lo, hi)
    local n, k, numGroups, G, result, total_yes, total_no;

    total_yes := 0;
    total_no  := 0;

    Print("\n");
    Print("============================================================\n");
    Print("  SCANNING GROUPS: order ", lo, " to ", hi, "\n");
    Print("  (Reproducing Velasquez-Berroteran 2022, aiming past 60)\n");
    Print("============================================================\n");
    Print(String("Order", 7), "  ",
          String("ID",   4), "  ",
          String("Group",          20), "  ",
          "Equal Covering?\n");
    Print("------------------------------------------------------------\n");

    for n in [lo .. hi] do
        numGroups := NumberSmallGroups(n);
        for k in [1 .. numGroups] do
            G := SmallGroup(n, k);
            if IsCyclic(G) then
                result := "cyclic — skip";
            elif HasEqualCovering(G) then
                result := "YES";
                total_yes := total_yes + 1;
            else
                result := "no";
                total_no  := total_no  + 1;
            fi;
            Print(String(n,       7), "  ",
                  String(k,       4), "  ",
                  String(StructureDescription(G), 20), "  ",
                  result, "\n");
        od;
    od;

    Print("------------------------------------------------------------\n");
    Print("Summary: ", total_yes, " groups have an equal covering, ",
          total_no, " do not (cyclic groups excluded)\n");
    Print("============================================================\n\n");
end;


TestDihedralTheorem := function()
    local n, G, result, parity;

    Print("\n");
    Print("============================================================\n");
    Print("  THEOREM 14 CHECK: D_{2n} has equal covering iff n is even\n");
    Print("============================================================\n");

    for n in [3 .. 10] do
        G := DihedralGroup(2 * n);

        if n mod 2 = 0 then
            parity := "even";
        else
            parity := "odd";
        fi;

        if HasEqualCovering(G) then
            result := "YES — has equal covering";
        else
            result := "no  — no equal covering";
        fi;

        Print("  D", 2 * n, " (n=", n, ", n is ", parity, ")  ->  ", result, "\n");
    od;

    Print("============================================================\n\n");
end;
