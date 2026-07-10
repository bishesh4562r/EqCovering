# ---- 2a ----
SubgroupsByOrder := function(G)
    local allSubs, buckets, s, o;
    allSubs := AllSubgroups(G);            # once per group
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

# Update HasEqualCovering
HasEqualCovering := function(G)
    local candidates, buckets, d, subs, allElts, union, s;
    if KnownYes(G) then return true; fi;
    if KnownNo(G) then return false; fi;
    if IsCyclic(G) then return false; fi;
    candidates := CandidateOrders(G);
    if Length(candidates) = 0 then return false; fi;
    buckets := SubgroupsByOrder(G);        # now computed once
    allElts := AsSet(G);
    for d in candidates do
        key := String(d);
        if IsBound(buckets.(key)) then
            subs := buckets.(key);
            union := [];
            for s in subs do
                Append(union, AsSet(s));
            od;
            if AsSet(union) = allElts then
                return true;
            fi;
        fi;
    od;
    return false;
end;