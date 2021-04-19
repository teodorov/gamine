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
        let toFilter := { a ∈ m.actions cs.1 | s.selector a },
            toForward := { fa | ∀ a ∈ m.actions cs.1, 
            	¬ s.selector a → fa = (cs.2, a)}
        in (s.apply cs.2 cs.1 toFilter) ∪ toForward,
    execute := λ cs sa, 
        let r := m.execute cs.1 sa.2
        in {x | ∀ c ∈ r, x = (c, sa.1)}
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