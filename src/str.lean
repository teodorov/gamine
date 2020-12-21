import init.data.set data.set

namespace str

-- Semantic Transition Relation structure
structure STR (C A : Type) :=
    (initial : set C)
    (actions : C → set A) 
    (execute : C → A → set C)

-- Atomic Proposition Evaluator structure
structure APE (C A L : Type) :=
    (eval : L → C → A → C → bool)

-- Atomic Propositon Collector structure
structure APC (C A L : Type) :=
    (eval : C → A → set L)

-- Accepting structure
structure Acc (C : Type) :=
    (is_accepting : C -> Prop)

--projections
structure Projector (C A Vc Va: Type) :=
    (project_c : C → Vc) 
    (project_a : A → Va)


namespace non_blocking

open STR
structure NonBlockingSTR 
    (C A : Type)    
extends STR C A :=
    (execute_does_not_block : 
        ∀ c a, 
            a ∈ actions c → execute c a ≠ ∅
    )

structure CompleteSTR₁ 
    (C A : Type)
extends NonBlockingSTR C A :=
    (no_deadlock : ∀ c, actions c ≠ ∅)

structure CompleteSTR₀
    (C A : Type)
extends STR C A :=
    (no_deadlock : 
        ∀ c, 
            actions c ≠ ∅ 
            ∧ ∃ a, a ∈ actions c → execute c a ≠ ∅
    )

def CompleteNonBlocking2Complete 
    (C A : Type) 
    [hA : inhabited A]
    (str₁ : CompleteSTR₁ C A) 
: (CompleteSTR₀ C A) :=
{
    initial := str₁.initial,
    actions := str₁.actions,
    execute := str₁.execute,
    no_deadlock := 
        begin
            intros, 
            simp,
            split,
                apply str₁.no_deadlock,
                existsi arbitrary A, apply str₁.execute_does_not_block,                 
        end,
}

end non_blocking
end str