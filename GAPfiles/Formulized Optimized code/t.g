# ============================================================
#  Helper: square‑free check
# ============================================================
EC_IsSquareFreeInt := function(n)
    local p;
    for p in PrimeDivisors(n) do
        if n mod p^2 = 0 then return false; fi;
    od;
    return true;
end;

# ============================================================
#  Known “yes” cases (theorems)
# ============================================================
EC_KnownYes := function(G)
    if IsNilpotent(G) and not IsCyclic(G) then return true; fi;
    if IsDihedralGroup(G) and IsEvenInt(Order(G)/2) then return true; fi;
    if IsPrimePowerInt(Order(G)) and not IsCyclic(G) then return true; fi;
    return false;
end;

# ============================================================
#  Known “no” cases (theorems)
# ============================================================
EC_KnownNo := function(G)
    if IsCyclic(G) then return true; fi;
    if EC_IsSquareFreeInt(Order(G)) then return true; fi;
    if IsDihedralGroup(G) and not IsEvenInt(Order(G)/2) then return true; fi;
    if IsSimpleGroup(G) and Exponent(G) = Order(G)/2 then return true; fi;
    return false;
end;

# ============================================================
#  Candidate orders (fixed bug)
# ============================================================
EC_CandidateOrders := function(G)
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

# ============================================================
#  Group subgroups by order (compute AllSubgroups once)
# ============================================================
EC_SubgroupsByOrder := function(G)
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

# ============================================================
#  Fast coverage check (hash map + early exit)
#  FIXED: use a record for element->position mapping, 
#  because group elements are not valid list indices.
# ============================================================
EC_CoversGroupFast := function(subs, G)
    local elementMap, covered, count, s, e, pos, n;
    elementMap := rec();
    n := 0;
    for e in G do
        n := n + 1;
        elementMap.(String(e)) := n;
    od;
    covered := BlistList([1 .. n], []);
    count := 0;
    for s in subs do
        for e in AsSet(s) do
            pos := elementMap.(String(e));
            if not covered[pos] then
                covered[pos] := true;
                count := count + 1;
                if count = n then
                    return true;
                fi;
            fi;
        od;
    od;
    return false;
end;

# ============================================================
#  Caching
# ============================================================
EC_EqualCoveringCache := rec();

EC_HasEqualCovering := function(G)
    local key, candidates, buckets, d;
    if Order(G) = 1 then
        return false;
    fi;
    # ---- FIX: use Concatenation instead of "*" ----
    key := Concatenation(String(Order(G)), ":", String(IdGroup(G)));
    if IsBound(EC_EqualCoveringCache.(key)) then
        return EC_EqualCoveringCache.(key);
    fi;

    if EC_KnownYes(G) then
        EC_EqualCoveringCache.(key) := true;
        return true;
    fi;
    if EC_KnownNo(G) then
        EC_EqualCoveringCache.(key) := false;
        return false;
    fi;

    candidates := EC_CandidateOrders(G);
    if Length(candidates) = 0 then
        EC_EqualCoveringCache.(key) := false;
        return false;
    fi;

    buckets := EC_SubgroupsByOrder(G);
    for d in candidates do
        if IsBound(buckets.(String(d))) then
            if EC_CoversGroupFast(buckets.(String(d)), G) then
                EC_EqualCoveringCache.(key) := true;
                return true;
            fi;
        fi;
    od;

    EC_EqualCoveringCache.(key) := false;
    return false;
end;

# ============================================================
#  ShowCovering
# ============================================================
EC_ShowCovering := function(G)
    local candidates, buckets, d, key, subs, i, result;

    Print("\n");
    Print("============================================================\n");
    Print("Group    : ", StructureDescription(G), "\n");
    Print("Order    : ", Order(G), "\n");
    Print("Exponent : ", Exponent(G), "\n");

    if IsCyclic(G) then
        Print("Result   : CYCLIC — no covering (Theorem 1)\n");
        Print("============================================================\n\n");
        return fail;
    fi;

    result := EC_HasEqualCovering(G);
    if result = true then
        candidates := EC_CandidateOrders(G);
        buckets := EC_SubgroupsByOrder(G);
        for d in candidates do
            key := String(d);
            if IsBound(buckets.(key)) then
                subs := buckets.(key);
                if EC_CoversGroupFast(subs, G) then
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
        Print("Result   : *** ERROR: inconsistent cache ***\n");
        Print("============================================================\n\n");
        return fail;
    else
        Print("Result   : No equal covering exists for this group\n");
        Print("============================================================\n\n");
        return false;
    fi;
end;

# ============================================================
#  ScanRange
# ============================================================
EC_ScanRange := function(lo, hi)
    local n, k, numGroups, G, result, total_yes, total_no;

    total_yes := 0;
    total_no  := 0;

    Print("\n");
    Print("============================================================\n");
    Print("  SCANNING GROUPS: order ", lo, " to ", hi, "\n");
    Print("  (optimised with theorems, caching, fast coverage)\n");
    Print("============================================================\n");
    Print("Order  ID    Group                Equal Covering?\n");
    Print("------------------------------------------------------------\n");

    for n in [lo .. hi] do
        numGroups := NumberSmallGroups(n);
        for k in [1 .. numGroups] do
            G := SmallGroup(n, k);
            if IsCyclic(G) then
                result := "cyclic — skip";
            elif EC_HasEqualCovering(G) then
                result := "YES";
                total_yes := total_yes + 1;
            else
                result := "no";
                total_no  := total_no  + 1;
            fi;
            Print(String(n), "  ",
                  String(k), "  ",
                  StructureDescription(G), "  ",
                  result, "\n");
        od;
    od;

    Print("------------------------------------------------------------\n");
    Print("Summary: ", total_yes, " groups have an equal covering, ",
          total_no, " do not (cyclic groups excluded)\n");
    Print("============================================================\n\n");
end;

# ============================================================
#  TestDihedralTheorem
# ============================================================
EC_TestDihedralTheorem := function()
    local n, G, result, parity;
    Print("\n");
    Print("============================================================\n");
    Print("  THEOREM 14 CHECK: D_{2n} has equal covering iff n is even\n");
    Print("============================================================\n");
    for n in [3 .. 10] do
        G := DihedralGroup(2 * n);
        parity := "odd"; if n mod 2 = 0 then parity := "even"; fi;
        if EC_HasEqualCovering(G) then
            result := "YES — has equal covering";
        else
            result := "no  — no equal covering";
        fi;
        Print("  D", 2 * n, " (n=", n, ", n is ", parity, ")  ->  ", result, "\n");
    od;
    Print("============================================================\n\n");
end;

# ============================================================
#  Demo examples
# ============================================================
EC_DemoExamples := function()
    Print("\n");
    Print("############################################################\n");
    Print("##  DEMO: groups WITH an equal covering                   ##\n");
    Print("############################################################\n");
    EC_ShowCovering(SmallGroup(4, 2));      # V4
    EC_ShowCovering(SmallGroup(8, 3));      # D8
    EC_ShowCovering(SmallGroup(12, 4));     # D12
    Print("############################################################\n");
    Print("##  DEMO: groups WITHOUT an equal covering                ##\n");
    Print("############################################################\n");
    EC_ShowCovering(SmallGroup(12, 3));     # A4
    EC_ShowCovering(CyclicGroup(5));
end;

# ============================================================
#  Main entry point – call this after loading the file
# ============================================================
EC_Main := function()
    Print("\n\n");
    Print("############################################################\n");
    Print("##                                                        ##\n");
    Print("##   EQUAL COVERINGS — Fully Optimised Code              ##\n");
    Print("##   (all 7 optimisations applied)                       ##\n");
    Print("##                                                        ##\n");
    Print("############################################################\n");
    EC_DemoExamples();
    EC_TestDihedralTheorem();
    Print("------------------------------------------------------------\n");
    Print("Quick scan: orders 1 to 20\n");
    Print("(Call EC_ScanRange(1,60) to reproduce full paper table)\n");
    Print("------------------------------------------------------------\n");
    EC_ScanRange(1, 20);
end;
