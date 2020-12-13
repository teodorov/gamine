import str filtering asynchronous_composition
namespace architectures

open str
open operators.filtering

variables 
    (C : Type) -- configurations
    (A : Type) -- actions
    (L : Type) -- atomic propositions
    (S : Type) -- filtering policy execution states
------------------------------------------------------------------------------
--                   Software architecture formalisation                    --
------------------------------------------------------------------------------

-- Runtime execution with statefull scheduling policy 
def runtime_execution 
    (system : STR C A)
    (scheduling_policy : SchedulingPolicy C A S)
: STR (C × S) ( S × A) := scheduler C A S system scheduling_policy

-- Model-checking with filtering
def model_checking_with_filtering
    (sys_and_env : STR C A)
    (filtering_policy : FilteringPolicy C A S)
: STR (C × S) (S × A) := filter C A S sys_and_env filtering_policy

-- Model-checking with scheduler in the verification loop 
def model_checking_with_scheduling (S₁ S₂ : Type)
    (sys_and_env : STR C A)
    (scheduling_policy : SchedulingPolicy C A S₁)
    (filtering_policy : FilteringPolicy (C×S₁) (S₁×A) S₂)
: STR ((C×S₁)×S₂) (S₂×(S₁×A)) :=  
    filter (C×S₁) (S₁×A) S₂
        (scheduler C A S₁ sys_and_env scheduling_policy)
        filtering_policy

-- Model-checking with decoupled environment
def model_checking_with_decoupled_env (C₁ C₂ A₁ A₂ S₁ S₂ : Type)
    (system : STR C₁ A₁)
    (env : STR C₂ A₂)
    (scheduling_policy : SchedulingPolicy C₁ A₁ S₁)
    (filtering_policy : FilteringPolicy ((C₁×S₁)×C₂) ((S₁×A₁) ⊕ A₂) S₂)
: STR (((C₁×S₁)×C₂)×S₂) (S₂×((S₁×A₁) ⊕ A₂))  := 
    filter ((C₁ × S₁) × C₂) ((S₁×A₁) ⊕ A₂) S₂
        ((scheduler C₁ A₁ S₁ system scheduling_policy) ⊗ₐ env)
        filtering_policy


end architectures