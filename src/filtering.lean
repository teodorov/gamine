import str
namespace operators

namespace filtering
open str 

-- Filtering policy
structure FilteringPolicy (C A S : Type) := 
    (initial : S)
    (selector : A → Prop)
    (apply : S → C → set A → set (S × A)) 
    (subset : ∀ s c 𝔸 (sa ∈ (apply s c 𝔸)), prod.snd sa ∈ 𝔸)

def StatelessFilteringPolicy (C A : Type) := FilteringPolicy C A unit

-- Scheduling policy
structure SchedulingPolicy (C A S : Type) extends (FilteringPolicy C A S) := 
    (unique : ∀ s c 𝔸 (a ∈ (apply s c 𝔸)) (b ∈ (apply s c 𝔸)), a = b) 

def StatelessSchedulingPolicy (C A : Type) := SchedulingPolicy C A unit

-- Filtering operator
def filter
    (C A S: Type)
    (m : STR C A)
    (s : FilteringPolicy C A S) 
: STR (C × S) (S × A) := 
{
    initial := {cs | ∀ (c ∈ m.initial), cs = (c, s.initial)},
    actions := λ cs, 
        let toFilter := { a ∈ m.actions (prod.fst cs) | s.selector a },
            toForward := { fa | ∀ a ∈ m.actions (prod.fst cs), 
            	¬ s.selector a → fa = (prod.snd cs, a)}
        in (s.apply (prod.snd cs) (prod.fst cs) toFilter) ∪ toForward,
    execute := λ cs sa, 
        let r := m.execute (prod.fst cs) (prod.snd sa) 
        in {x | ∀ c ∈ r, x = (c, (prod.fst sa))}
}

-- Used to cast a scheduling policy into a filtering policy with the ↑ notation
instance scheduling_to_filtering (C A S : Type): 
    has_coe (SchedulingPolicy C A S)(FilteringPolicy C A S) := ⟨ SchedulingPolicy.to_FilteringPolicy ⟩ 

-- Scheduling operator
def scheduler 
    (C A S : Type)
    (m : STR C A)
    (s : SchedulingPolicy C A S) 
: STR (C × S) (S × A) := filter C A S m ↑s

end filtering

end operators