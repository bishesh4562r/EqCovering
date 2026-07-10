# ---- 1a & 1b ----
IsSquareFreeInt := function(n)
    local p;
    for p in PrimeDivisors(n) do
        if n mod p^2 = 0 then return false; fi;
    od;
    return true;
end;

KnownYes := function(G)
    if IsNilpotent(G) and not IsCyclic(G) then return true; fi;
    if IsDihedralGroup(G) and IsEvenInt(Order(G)/2) then return true; fi;
    if IsPrimePowerInt(Order(G)) and not IsCyclic(G) then return true; fi;
    return false;
end;

KnownNo := function(G)
    if IsCyclic(G) then return true; fi;
    if IsSquareFreeInt(Order(G)) then return true; fi;
    if IsDihedralGroup(G) and not IsEvenInt(Order(G)/2) then return true; fi;
    if IsSimpleGroup(G) and Exponent(G) = Order(G)/2 then return true; fi;
    return false;
end;

# Modified HasEqualCovering
HasEqualCovering := function(G)
    local candidates, d, subs, allElts, union, s;
    if KnownYes(G) then return true; fi;      # pruned
    if KnownNo(G) then return false; fi;      # pruned
    # fallback to original search (but we'll improve it next)
    if IsCyclic(G) then return false; fi;
    candidates := CandidateOrders(G);
    allElts    := AsSet(G);
    for d in candidates do
        subs  := Filtered(AllSubgroups(G), H -> Order(H) = d);
        union := [];
        for s in subs do
            Append(union, AsSet(s));
        od;
        if AsSet(union) = allElts then
            return true;
        fi;
    od;
    return false;
end;