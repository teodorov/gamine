import str
namespace coverage

open str 

structure CoverageC (C A : Type) :=
    (current : C)
    (actions : set A)

def unreachable_global (C A : Type) (str : STR C A) (actions : set A) : (STR (CoverageC C A) A) :=
{
  initial := { x | ∀ c ∈ str.initial, x = ⟨ c, actions ⟩ },
  actions := λ c, { x | ∀ a ∈ str.actions c.1, x = a },
  execute := λ c a, {x | ∀ t ∈ str.execute c.1 a, x = ⟨ t, c.2 \ { a } ⟩},
}

end coverage