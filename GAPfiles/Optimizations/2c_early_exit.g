# ---- 2c ----
# modified CoversGroupFast
CoversGroupFast := function(subs, G)
    local elementMap, covered, count, s, e, pos, n;
    elementMap := [];
    n := 0;
    for e in G do
        n := n + 1;
        elementMap[e] := n;
    od;
    covered := BlistList([1 .. n], []);
    count := 0;
    for s in subs do
        for e in AsSet(s) do
            pos := elementMap[e];
            if not covered[pos] then
                covered[pos] := true;
                count := count + 1;
                if count = n then          # EARLY EXIT
                    return true;
                fi;
            fi;
        od;
    od;
    return false;
end;