
variables {C A : Type}

def step (s s' : C) (a : A) : Prop := sorry 


notation s `—{` a `}→` s' := step s s' a 

/-!
`wp` is the weakest precondition of an action `aᵢ` wrt a set `X`
-/
def wp(aᵢ : A) (X : set C) := { s | ∀ s' ∈ X,  s —{ aᵢ }→ s' }

/-!
`sp` is the weakest precondition of an action `aᵢ` wrt a set `X`
-/
def sp(aᵢ : A) (X : set C) := { s' | ∃ s ∈ X, s —{ aᵢ }→ s' }

