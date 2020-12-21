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


namespace complete
variables (C A : Type) (str : STR C A)

def is_nonblocking : Prop := ∀ c a, a ∈ str.actions c → str.execute c a ≠ ∅

structure NonBlockingSTR 
extends STR C A :=
    (nonblocking : is_nonblocking C A to_STR)

def is_actions_complete : Prop :=  ∀ c, str.actions c ≠ ∅

structure CompleteNonBlockingSTR
extends NonBlockingSTR C A :=
    (complete : is_actions_complete C A to_STR)

def is_complete : Prop := 
    ∀ c, 
            str.actions c ≠ ∅ 
            ∧ ∃ a, a ∈ str.actions c → str.execute c a ≠ ∅

structure CompleteSTR
extends STR C A :=
    (complete : is_complete C A to_STR)

def CompleteNonBlocking2Complete 
    [hA : inhabited A]
    (str₁ : CompleteNonBlockingSTR C A) 
: (CompleteSTR C A) :=
{
    initial := str₁.initial,
    actions := str₁.actions,
    execute := str₁.execute,
    complete := 
        begin
            unfold is_complete,
            intro,
            simp,
            split,
                apply str₁.complete,
                existsi arbitrary A, apply str₁.nonblocking,
        end,
}

end complete
end str