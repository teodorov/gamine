namespace tr 

-- TR structure
structure TR (C : Type) :=
    (initial : set C)
    (next : C -> set C) 
    (accepting : C -> Prop)

end tr