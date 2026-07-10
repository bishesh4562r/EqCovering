CandidateOrders := function(G)
    local expG, candidates, d;
    expG := Exponent(G);
    candidates := [];
    for d in DivisorsInt(Order(G)) do
        if d < Order(G) and expG mod d = 0 then   # BUG: should be d mod expG
            Add(candidates, d);
        fi;
    od;
    return candidates;
end;

HasEqualCovering := function(G)
    local candidates, d, subs, allElts, union, s;
    if IsCyclic(G) then
        return false;
    fi;
    candidates := CandidateOrders(G);
    allElts    := AsSet(G);
    for d in candidates do
        subs  := Filtered(AllSubgroups(G), H -> Order(H) = d);   # Computed repeatedly!
        union := [];
        for s in subs do
            Append(union, AsSet(s));          # No early exit, slow lookup
        od;
        if AsSet(union) = allElts then
            return true;
        fi;
    od;
    return false;
end;