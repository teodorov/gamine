import str

namespace debug
open str

------------------------------------------------------------------------------
--                                Debugging                                 --
------------------------------------------------------------------------------

-- DebugConfig structure
structure DebugConfig (C : Type) :=
    (current : option C)
    (trace : set C)
    (options : set C)

-- DebugAction inductive type
inductive DebugAction {C A : Type}
	| step : A → DebugAction
	| select : C → DebugAction
	| jump : C → DebugAction
	| run_to_breakpoint : DebugAction

def debugInitial 
	(C A : Type) 
	(o : STR C A)
	: set (DebugConfig C)
:= { { DebugConfig . current := none, trace := ∅, options := o.initial } }

def debugActions 
	(C A : Type) 
	(o : STR C A)
	(dc : DebugConfig C) : set (@DebugAction C A) 
	:= match dc.current with 
        | (some c) := 
            let
                oa := { x : @DebugAction C A  | 
                	∀ a ∈ (o.actions c), x = DebugAction.step a },
                ja := { x : @DebugAction C A  | 
                	∀ c ∈ dc.trace,    x = DebugAction.jump c }
            in
                oa ∪ ja ∪ { DebugAction.run_to_breakpoint }
        | none := { sa | ∀ c ∈ dc.options, sa = DebugAction.select c }
        end

def debugExecute
	(C A : Type) 
	(o : STR C A)
	(find_counterexample : set C → STR C A → set C → list C)
	(breakpoints : set C)
	(dc : DebugConfig C) 
	(da : @DebugAction C A) 
	: set (DebugConfig C)
:= match dc.current, da with 
		| (some c), (DebugAction.step a) := { { DebugConfig . current := none,
			trace :=    dc.trace, options := o.execute c a} }
    	| (none)  , (DebugAction.step a) := ∅
    	| _       , (DebugAction.select c) := { { DebugConfig . current := c,
    		trace := {c} ∪ dc.trace, options := ∅ } }
   		| _       , (DebugAction.jump c) := { { DebugConfig . current := c, 
   			trace := {c} ∪ dc.trace, options := ∅ } }
    	| (some c), (DebugAction.run_to_breakpoint) := 
        	match (find_counterexample { c } o breakpoints) with 
        		| []        := { { DebugConfig . current := dc.current, 
        			trace := dc.trace, options := ∅ } }
        		| a::ctrace := { { DebugConfig . current := a,
        			trace := {a} ∪ { x | x ∈ ctrace } ∪ dc.trace, options := ∅ } }
        	end
    	| none, (DebugAction.run_to_breakpoint) := 
        	match (find_counterexample dc.options o breakpoints) with 
        		| []        := { { DebugConfig . current := dc.current,
        			trace := dc.trace, options := ∅ } }
        		| a::ctrace := { { DebugConfig . current := a,
        			trace := {a} ∪ { x | x ∈ ctrace } ∪ dc.trace, options := ∅ } }
        end
    end

def unified_debugging
	(C A : Type)
    (o : STR C A)
    (find_counterexample : set C → STR C A → set C → list C)
    (breakpoints : set C)
: STR (DebugConfig C) (@DebugAction C A) := 
{
	initial := 					debugInitial C A o,
	actions := λ dc, 		debugActions C A o dc,
	execute := λ dc da, debugExecute C A o find_counterexample breakpoints dc da
}

-- Formal definition for interactive multiverse debugging
def interactive_multiverse_debugging 
    (C A : Type)
    (o : STR C A)
    (find_counterexample : set C → STR C A → set C → list C)
    (breakpoints : set C)
: STR (DebugConfig C) (@DebugAction C A) :=
{
    initial := { { DebugConfig . current := none, 
    	trace := ∅, options := o.initial } }, 
    actions := λ dc, match dc.current with 
        | (some c) := 
            let
                oa := { x : @DebugAction C A  | 
                	∀ a ∈ (o.actions c), x = DebugAction.step a },
                ja := { x : @DebugAction C A  | 
                	∀ c ∈ dc.trace,    x = DebugAction.jump c }
            in
                oa ∪ ja ∪ { DebugAction.run_to_breakpoint }
        | none := { sa | ∀ c ∈ dc.options, sa = DebugAction.select c }
        end,
    execute := λ dc da, match dc.current, da with 
		| (some c), (DebugAction.step a) := { { DebugConfig . current := none,
			trace :=    dc.trace, options := o.execute c a} }
    	| (none)  , (DebugAction.step a) := ∅
    	| _       , (DebugAction.select c) := { { DebugConfig . current := c,
    		trace := {c} ∪ dc.trace, options := ∅ } }
   		| _       , (DebugAction.jump c) := { { DebugConfig . current := c, 
   			trace := {c} ∪ dc.trace, options := ∅ } }
    	| (some c), (DebugAction.run_to_breakpoint) := 
        	match (find_counterexample { c } o breakpoints) with 
        		| []        := { { DebugConfig . current := dc.current, 
        			trace := dc.trace, options := ∅ } }
        		| a::ctrace := { { DebugConfig . current := a,
        			trace := {a} ∪ { x | x ∈ ctrace } ∪ dc.trace, options := ∅ } }
        	end
    	| none, (DebugAction.run_to_breakpoint) := 
        	match (find_counterexample dc.options o breakpoints) with 
        		| []        := { { DebugConfig . current := dc.current,
        			trace := dc.trace, options := ∅ } }
        		| a::ctrace := { { DebugConfig . current := a,
        			trace := {a} ∪ { x | x ∈ ctrace } ∪ dc.trace, options := ∅ } }
        end
    end
}

end debug