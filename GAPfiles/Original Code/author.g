# Author's algorithm (paraphrased from pages 23-24)
FindEqualCovering := function(G)
    local expG, orders, d, S, union, s;
    
    expG := Exponent(G);
    orders := [];
    
    for d in DivisorsInt(Order(G)) do
        if d < Order(G) and d mod expG = 0 then
            Add(orders, d);
        fi;
    od;
    
    for d in orders do
        union := [];
        for s in AllSubgroups(G) do
            if Order(s) = d then
                Append(union, AsSet(s));
            fi;
        od;
        if Size(AsSet(union)) = Order(G) then
            return true;  # Found an equal covering
        fi;
    od;
    return false;
end;