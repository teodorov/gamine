import str init.data.set
namespace operators
open str 
-- Type to know if some actions are available or if there is a deadlock
universe u
inductive completed (α : Type u)
	| deadlock {} : completed
	| some    : α → completed

-- Operator used to complete a STR by adding implicit transitions
def add_implicit_transitions
    (C A : Type)
    (str : STR C A)
    [∀ c, decidable (str.actions c = ∅)]
: STR C (completed A) := 
{ 
    initial := str.initial,
    actions := λ c, if str.actions c = ∅ then 
            (singleton completed.deadlock) 
        else 
            { oa | ∀ a ∈ str.actions c, oa = completed.some a }, 
    execute := λ c oa, match oa with
        | completed.deadlock  := singleton c
        | completed.some a := { oc | ∀ t ∈ str.execute c a, oc = t }
        
    end
} 

-- deadlock = exists a configuration without fanout
-- three potential sources of deadlock
-- + actions, if from a source there is no action fireable
-- + execute, ∀ a ∈ str.actions c, str.execute c a = ∅ , all action from c lead to empty sets when executed

def no_deadlock 
  (C A : Type)
  (str : STR C A)
: Prop := 
  ∀ c, 
    str.actions c ≠ ∅ 
  ∧ ∀ a ∈ str.actions c, str.execute c a = ∅

def add_implicit_steps
  (C A : Type)
  (str : STR C A)
  [∀ c, decidable (str.actions c = ∅)]
  [∀ c, decidable (∀ (a : A), a ∈ str.actions c → str.execute c a = ∅)]
: STR C (completed A) :=
{
  initial := str.initial,
  actions := λ c, 
              if str.actions c = ∅ then
                singleton completed.deadlock
              else
                if ∀ a ∈ str.actions c, str.execute c a = ∅ then 
                  singleton completed.deadlock
                else
                  { x | ∀ a ∈ str.actions c, x = completed.some a },
  execute := λ c oa, match oa with
        | completed.deadlock  := singleton c
        | completed.some a := { oc | ∀ t ∈ str.execute c a, oc = t }
        end 
}

theorem add_imp_rem_deadlock 
  (C A : Type)
  (str : STR C A)
  [∀ c, decidable (str.actions c = ∅)]
  [∀ c, decidable (∀ (a : A), a ∈ str.actions c → str.execute c a = ∅)]
: 
  no_deadlock C (completed A) (add_implicit_steps C A str)
:= 
by {
  unfold no_deadlock, intros, simp *,
  split,rw add_implicit_steps, simp * at *, 
  have h : (str.actions c = ∅), 
    sorry, 
    simp *, sorry,
  intros, rw add_implicit_steps, simp *,  sorry,
}

end operators