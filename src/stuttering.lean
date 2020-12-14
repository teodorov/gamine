import str init.data.set data.set
namespace operators
open str 
-- Type to know if some actions are available or if there is a deadlock
universe u
inductive completed (α : Type u)
	| deadlock {} : completed
	| some   {} : α → completed

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
    (str.actions c).nonempty
  ∧ ∃ a ∈ str.actions c, (str.execute c a).nonempty

def has_deadlock 
  (C A : Type)
  (str : STR C A)
: Prop := 
  ∃ c, 
    str.actions c = ∅ 
  ∨ ∀ a ∈ str.actions c, str.execute c a = ∅

def deadlock_configuration 
  {C A : Type}
  (str : STR C A)
  (c : C)
: Prop :=
  str.actions c = ∅ 
  ∨ ∀ a ∈ str.actions c, str.execute c a = ∅



@[simp]
def add_implicit_steps
  (C A : Type)
  (str : STR C A)
  -- [∀ c, decidable (str.actions c = ∅)]
  -- [∀ c, decidable (∀ (a : A), a ∈ str.actions c → str.execute c a = ∅)]
  [∀ c, decidable (deadlock_configuration str c)]
: STR C (completed A) :=
{
  initial := str.initial,
  actions := λ c, 
              if h : deadlock_configuration str c then 
                  singleton completed.deadlock
                else
                  { x | ∀ a ∈ str.actions c, x = completed.some a },
  execute := λ c oa, match oa with
        | completed.deadlock  := singleton c
        | completed.some a := { oc | ∀ t ∈ str.execute c a, oc = t }
        end 
}


theorem add_imp_rem_deadlock 
  (C: Type)
  (A: Type)
  (str : STR C A)
  (deadlock : ¬ no_deadlock C A str)
  -- [∀ c, decidable (str.actions c = ∅)]
  -- [∀ c, decidable (∀ (a : A), a ∈ str.actions c → str.execute c a = ∅)]
  [∀ c, decidable (deadlock_configuration str c)]
: 
  no_deadlock C (completed A) (add_implicit_steps C A str)
:= 
begin
  simp * at *, intro, simp at *, split_ifs, 
    finish *, 
  --   split, exact not_empty_when_no_deadlock C A str c h,
  
  --   revert h, simp at *, unfold deadlock_configuration, 
  --   refine classical.skolem.mpr _, refine ex_of_psig _, refine ⟨_, _⟩, 
  --   intro, exact completed.deadlock,
    
  -- refine imp_and_distrib.mpr _, split, 
  -- revert deadlock, unfold no_deadlock,

  -- simp * at *, intros, revert ᾰ_1, refine not_imp.mpr _, split, 
  -- revert ᾰ, refine imp_or_distrib.mpr _, refine or.inl _, safe *, revert ᾰ_1,
  -- -- hint, 
  -- refine not_imp.mpr _, norm_num, revert ᾰ, exact set.not_nonempty_iff_eq_empty.mp, simp [not_nonempty_iff_eq_empty], 
  
  sorry,
end

end operators