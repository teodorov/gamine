import str

namespace emi

------------------------------------------------------------------------------
--                        The EMI to STR conversion                         --
------------------------------------------------------------------------------

-- Abstract types needed for defining EMI (more complex in reality)
def EMIModel := ℕ 
def EMIDynamicMemory := list ℕ
def EMITransition := ℕ

-- EMI memory structure
structure EMI : Type := 
    (model : EMIModel)
    (dynamic : EMIDynamicMemory)

-- EMIState monad
@[reducible] def EMIState := state EMI 

-- EMI API functions (not described here because their implementation depends on the language semantics and on implementation choices)
def get_configuration : EMIState EMIDynamicMemory:= sorry
def set_configuration (n : EMIDynamicMemory) : EMIState unit := sorry
def get_executable_steps : EMIState (set EMITransition) := sorry 
def execute_step (t : EMITransition) : EMIState unit := sorry
def reset : EMIState unit := sorry

--Adapter functions for STR
def emi_initial : EMIState EMIDynamicMemory :=
do reset, c ← get_configuration, return c

def emi_actions (c : EMIDynamicMemory) : EMIState (set EMITransition) :=
do set_configuration c, a ← get_executable_steps, return a

def emi_execute (c : EMIDynamicMemory) (t : EMITransition) : EMIState EMIDynamicMemory :=
do set_configuration c, execute_step t, x ← get_configuration, return x

open str 
-- Conversion from EMI to STR
def EMI2STR (emi : EMI) : STR EMIDynamicMemory EMITransition  := 
{ 
    initial := { prod.fst (emi_initial.run emi) },
    actions := λ c, prod.fst ((emi_actions c).run emi),
    execute := λ c a, { prod.fst ((emi_execute c a).run emi) }
}

end emi