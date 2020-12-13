import str
namespace operators
open str 

-- Asynchronous composition operator
def asynchronous_composition  { C₁ A₁ C₂ A₂ : Type }
    (l : STR C₁ A₁) 
    (r : STR C₂ A₂) 
: STR (C₁ × C₂) (A₁ ⊕ A₂) :=
{
    initial := {c | ∀ (c₁ ∈ l.initial) (c₂ ∈ r.initial), c = (c₁, c₂)},
    actions := λ c, {a | match c : ∀ C, Prop with
        | (c₁, c₂) := ∀ (a₁ ∈ l.actions c₁) (a₂ ∈ r.actions c₂), 
        	a = sum.inl a₁ ∨ a = sum.inr a₂
        end},
    execute := λ c a, {a' | match c : ∀ C, Prop with
        | (c₁, c₂) := match a with 
            | (sum.inl a₁) := ∀ c₁' ∈ l.execute c₁ a₁, a' = (c₁', c₂ )
            | (sum.inr a₂) := ∀ c₂' ∈ r.execute c₂ a₂, a' = (c₁ , c₂')
            end
        end}
}

notation l `⊗ₐ` r := asynchronous_composition l r

end operators