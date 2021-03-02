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

structure SLI (C A L Vc Va : Type) :=
    (str  : STR C A)
    (ape  : APE  C A L)
    (acc  : Acc C)
    (proj : Projector C A Vc Va)


namespace complete
variables (C A : Type) (str : STR C A)

-- a STR is nonblocking if the execute step always produces at least on target
def is_nonblocking : Prop := ∀ c a, a ∈ str.actions c → str.execute c a ≠ ∅

-- a nonblocking STR is a STR with the proof that the execute always produces a non empty set of targets
structure NonBlockingSTR 
extends STR C A :=
    (nonblocking : is_nonblocking C A to_STR)

-- a STR is "actions-complete" if it has at least one action for any configurations 
def is_actions_complete : Prop :=  ∀ c, str.actions c ≠ ∅

-- a complete nonblocking STR is a nonblocking STR with the proof that is actions-complete
structure ActionCompleteNonBlockingSTR
extends NonBlockingSTR C A :=
    (complete : is_actions_complete C A to_STR)

-- a STR is complete if from any configuration we can get at least one target
def is_complete : Prop := 
    ∀ c, 
            str.actions c ≠ ∅ 
            ∧ ∃ a, a ∈ str.actions c -> str.execute c a ≠ ∅

structure CompleteSTR
extends STR C A :=
    (complete : is_complete C A to_STR)

-- an action-complete nonblocking STR is a also a complete STR
def CompleteNonBlocking2Complete 
    [hA : inhabited A]
    (str₁ : ActionCompleteNonBlockingSTR C A) 
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
                existsi arbitrary A,  apply str₁.nonblocking,
        end,
}

end complete
end str