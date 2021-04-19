import str
namespace operators
open str 
-- Synchronous composition operator
def synchronous_composition (C₁ C₂ A₁ A₂ L₁ : Type)
    (lhs : STR C₁ A₁)
    (ape : APE C₁ A₁ L₁)
    (rhs : STR C₂ A₂)
    (apc : APC C₂ A₂ L₁)
: STR (C₁ × C₂) (A₁ × A₂) :=
{
    initial := { c | ∀ (c₁ ∈ lhs.initial) (c₂ ∈ rhs.initial), c = (c₁, c₂) },
    actions := λ c, { a | 
        match c with
        | (c₁, c₂) := ∀ (a₁ ∈ lhs.actions c₁) (a₂ ∈ rhs.actions c₂)
            (t₁ ∈ lhs.execute c₁ a₁) (t₂ ∈ rhs.execute c₂ a₂),
            match t₁, t₂ : ∀ t₁ t₂, Prop with 
            | t₁, t₂ := ∀ l ∈ apc.eval c₂ a₂, 
            	ape.eval l c₁ a₁ t₁ → a = (a₁, a₂)
            end
        end    
    },
    execute := λ c a, { t | 
        match c, a with 
        | (c₁, c₂), (a₁, a₂) :=  ∀ (t₁ ∈ lhs.execute c₁ a₁) 
        	(t₂ ∈ rhs.execute c₂ a₂), t = (t₁, t₂)
        end
    }  
}

def synchronous_composition' (C₁ C₂ A₁ A₂ L₁ : Type)
    (lhs : STR C₁ A₁)
    (ape : APE' C₁ A₁ L₁)
    (rhs : STR C₂ A₂)
    (apc : APC' C₂ A₂ L₁)
: STR (C₁ × C₂) (A₁ × A₂) :=
{
    initial := { c | ∀ (c₁ ∈ lhs.initial) (c₂ ∈ rhs.initial), c = (c₁, c₂) },
    actions := λ c, { a | 
        match c with
        | (c₁, c₂) := ∀ (a₁ ∈ lhs.actions c₁) (a₂ ∈ rhs.actions c₂)
            (t₁ ∈ lhs.execute c₁ a₁) (t₂ ∈ rhs.execute c₂ a₂),
            match t₁, t₂ : ∀ t₁ t₂, Prop with 
            | t₁, t₂ :=  
            	ape (apc c₂ a₂) c₁ a₁ t₁ → a = (a₁, a₂)
            end
        end    
    },
    execute := λ c a, { t | 
        match c, a with 
        | (c₁, c₂), (a₁, a₂) :=  ∀ (t₁ ∈ lhs.execute c₁ a₁) 
        	(t₂ ∈ rhs.execute c₂ a₂), t = (t₁, t₂)
        end
    }  
}

end operators