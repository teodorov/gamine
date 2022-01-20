import init.data.set data.set

namespace str

/-!
    Semantic Transition Relation structure
    `actions` captures the `ENABLED` relation between the configurations and the actions
    in other words the `actions` functions returns the set of `ENABLED` action in a configuration
-/
structure STR (C A : Type) :=
    (initial : set C)
    (actions : C → set A) 
    (execute : C → A → set C)

/-!
    The step predicate defines the an a-step. 
    For a pair `c` `c'` of configurations and an atomic action `a`
    the step predicate holds if executing the action a in c produces the configuration c'
    Relation to **TLA+**: This matches the notion of 𝒜-step 
-/
def step {C A : Type} (s : STR C A) : C → A → C → Prop
| c a c' := ∃ c a c', a ∈ s.actions c ∧ c' ∈ (s.execute c a)

notation c `—{` a `}` s `→` c' := step s c a c' 
/-!
    Lamport, Leslie. "The temporal logic of actions." 
    ACM Transactions on Programming Languages and Systems (TOPLAS) 
    16, no. 3 (1994): 872-923.

    For any atomic action `a`, enabled c a holds for the configurations where it is 
    possible to perfom the action `a`.
    Relation to **TLA+**: The enabled predicate matches the definition of ENABLED
-/
def enabled{C A : Type} (s : STR C A) : C → A → Prop 
| c a := ∃ c', step s c a c'

-- Atomic Proposition Evaluator structure
structure APE (C A L : Type) :=
    (eval : L → C → A → C → bool)
def APE' (C A L : Type) := L → C → A → C → bool

-- Atomic Propositon Collector structure
structure APC (C A L : Type) :=
    (eval : C → A → set L)
def APC' (C A L : Type):= C → A → L

-- Accepting structure
structure Acc (C : Type) :=
    (is_accepting : C -> Prop)
def Acc' (C : Type) := C → Prop

--projections
structure Projector (C A Vc Va: Type) :=
    (project_c : C → Vc) 
    (project_a : A → Va)

structure SLI (C A L₀ L₁ : Type) :=
    (str  : STR C A)
    (ape  : L₀ → C → A → C → bool)
    (apc  : C → A → set L₁)
    (acc  : C → bool)
    -- (πc   : C → array byte)
    -- (πa   : C → array byte)


structure SLI' (C A L₀ L₁ : Type) :=
    (str  : STR C A)
    (ape  : L₀ → C → A → C → bool)
    (apc  : C → A → L₁)
    (acc  : C → bool)
    -- (πc   : C → array byte)
    -- (πa   : C → array byte)


namespace complete
variables (C A : Type) (str : STR C A)

-- a STR is nonblocking if the execute step always produces at least on target
def is_nonblocking : Prop := ∀ c a, a ∈ str.actions c → str.execute c a ≠ ∅

-- a nonblocking STR is a STR with the proof that the execute always produces a non empty set of targets
structure NonBlockingSTR 
extends STR C A :=
    (nonblocking : is_nonblocking C A to_STR)

-- a STR is "actions-complete" if it has at least one enabled action for any configurations 
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
            intro, simp,
            split,
                { apply str₁.complete },
                { existsi arbitrary A,  apply str₁.nonblocking }
        end,
}

end complete
end str