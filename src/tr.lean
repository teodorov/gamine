import algebra.big_operators.basic
namespace tr 


-- TR structure
structure TR (C : Type) :=
    (initial : set C)
    (next : C -> set C) 
    (accepting : C -> Prop)

structure M (C : Type) :=
    (initial : set C)
    (next : C -> set C) 
    (accepting : C -> bool)

structure MH (C : Type) := 
    (initial : set (C × bool))
    (next : C → set (C × bool))

-- def TR2TRm (C: Type) (m : TR C) : TRm C
-- :=  {
--         initial :=      { (i, m.accepting(i)) | ∀ i ∈ m.initial },
--         next    := λ s, { (n, m.accepting(n)) | ∀ n ∈ m.next s },
--     }

def M2MH (C : Type) (m : M C): MH C 
:= {
    initial :=      { ia | ∀ i ∈ m.initial, ia = (i, m.accepting i) },
    next    := λ s, { ta | ∀ t ∈ m.next s,  ta = (t, m.accepting t) },
}

structure MHG (C : Type) :=
    (initial : set (C × bool))
    (next : set C  → set (C × bool))

def MH2MHG (C : Type) (m : MH C) : MHG C 
:= {
    initial :=    m.initial,
    next    := λ A, ⋃ c ∈ A, m.next c,
}


end tr