import tr
import data.fintype.basic
open tr

namespace frontier

structure M (C: Type) := 
    (ini : set C)
    (next : set C → set C)

def TR2M (C : Type) (tr : TR C) : M C :=
    ⟨ 
        tr.initial,
        λ S, { t | ∀ s ∈ S, t ∈ tr.next s }
    ⟩ 

def initialPredicate 
    (C : Type)
    (m : M C)
    (K F : set C) : Prop 
:= K = m.ini ∧ F = K

def stepPredicate
    (C : Type)
    (m : M C)
    (K F K' F': set C) : Prop
:= ∃ A ∈ 𝒫 F, 
        A ≠ ∅ 
    ∧   let 
            N := m.next A 
        in    K' = K ∪ N 
            ∧ F' = (F \ A) ∪ N

def endPredicate
    (C : Type)
    (K F K' F': set C) : Prop
:= F = ∅ ∧ K' = K ∧ F' = F

def NextPredicate (C : Type)
    (m : M C)
    (K F K' F': set C) : Prop
:= stepPredicate C m K F K' F' ∨ endPredicate C K F K' F'

end frontier

namespace recursive

structure M (C: Type) := 
    (ini : set C)
    (next : set C → set C)

meta
def reach{C: Type} 
    [h₀ : ∀ F : set C, decidable (F = ∅)]
    : set C → set C → M C → set C
| F K M :=
    if F = ∅ then K else 
    let
        A := {x | ∃ pF ∈ (𝒫 F), pF ≠ ∅ ∧ x ∈ pF},
        N := M.next A,
        F' := (F \ A) ∪ (N \ K),
        K' := K ∪ N
    in
        reach F' K' M
-- using_well_founded by {
--     sorry
-- }
            
                

meta
def safe₀ {C : Type}
    [h₀ : ∀ F :set C, decidable (F ≠ ∅)]
: set C → set C → TR C → bool
| F K m :=
    if (F ≠ ∅) then 
        let 
            N := { n | ∀ x ∈ F, n ∈ m.next x}
        in
            if (N ∩ m.accepting) ≠ ∅ 
            then ff
            else let 
                F' := N \ K,
                K' := K ∪ N
            in (safe₀ F' K' m)
    else 
        tt
end recursive