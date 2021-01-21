import str data.hash_map

namespace profile
open str

def update {α : Type} [hα : decidable_eq α]: α → list (α×ℕ) → list (α×ℕ) 
| a [] := (a, 1)::[]
| a (x::l) := if a = x.1 then (x.1, x.2+1)::l else update a l

structure ProfileConfig(C A : Type) [hA : decidable_eq A] :=
  (base : C)
  (profile : list (A×ℕ))

inductive ProfileAction {C A : Type}
|  a : A → ProfileAction

def profile
  (C A : Type)
  [hA : decidable_eq A]
  (o : STR C A)
: STR (ProfileConfig C A) A :=
{
  initial := { c | ∀ cb ∈ o.initial, c = { base := cb, profile := [] } },
  actions := λ c, o.actions c.base,
  execute := λ c a, 
    { x | ∀ t ∈ o.execute c.base a, x = { base := t, profile := update a c.profile } }
}

end profile