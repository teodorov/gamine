import str propositional

namespace debug
open str propositional

------------------------------------------------------------------------------
--                                Debugging                                 --
------------------------------------------------------------------------------

-- DebugConfig structure
structure DebugConfig (C : Type) :=
    (current : option C)
    (trace : set C)
    (options : set C)

-- DebugAction inductive type
inductive DebugAction (C A : Type)
	| step : A → DebugAction
	| select : C → DebugAction
	| jump : C → DebugAction
	| run_to_breakpoint : DebugAction
open DebugAction

def CounterExampleFinder (C A) := set C → STR C A → set C → list C
def CounterExampleFinder' (C A L₀ : Type) := (APE' C A (L₁ L₀)) → STR C A → L₁ L₀ → set C → list C

def Finder (C A L₀ : Type) := (APE' C A (L₁ L₀)) → STR C A → L₁ L₀ → set C → list C
def Finder' (C A L₀ : Type) := STR C A → L₁ L₀ → set C → list C
def Finder'' (C L₀ : Type) := L₁ L₀ → set C → list C
def Finder''' (C : Type) := set C → list C


def debugInitial 
	(C A : Type) 
	(o : STR C A)
	: set (DebugConfig C)
:= { { DebugConfig . current := none, trace := ∅, options := o.initial } }

def debugActions'
	(C A : Type) 
	(o : STR C A)
	(dc : DebugConfig C) : set (DebugAction C A) 
	:= 
	let
		oa := { x : DebugAction C A | ∀ c, dc.current = some c -> ∀ a ∈ (o.actions c), x = step a },
		ja := { x : DebugAction C A | ∀ c ∈ dc.trace, x = jump c }, --∃ world ∈ 𝒫 dc.trace, ∀ c ∈ world, x = jump c },
		sa := { x : DebugAction C A | ∀ c ∈ dc.options, x = select c }
	in oa ∪ ja ∪ { run_to_breakpoint  }

def debugExecute''
	(C A L₀: Type) 
	(o : STR C A)
	(finder : Finder' C A L₀)
	(breakpoints : L₁ L₀)
	(dc : DebugConfig C) 
	(da : @DebugAction C A) 
	: set (DebugConfig C)
:= match da with 
	| DebugAction.step a :=   { x  | ∀ c options, dc.current = some c -> 
																		options = o.execute c a ∧ options ≠ ∅ ->
																		x = ⟨ none, dc.trace, options ⟩  }
	| DebugAction.select c := { { DebugConfig . current := c, trace := { c } ∪ dc.trace, options := ∅ } }
	| DebugAction.jump c   := { { DebugConfig . current := c, trace := { c } ∪ dc.trace, options := ∅ } }
	| DebugAction.run_to_breakpoint := 
				match dc.current with
				| some c  := { x | 
						∀ a l, finder o breakpoints { c }  = a::l →
							x = ⟨ a, dc.trace ∪ { x | x ∈ a::l }, ∅ ⟩ }
				| none		:= { x |
						∀ a l, finder o breakpoints dc.options = a::l ->
							x = ⟨ a, dc.trace ∪ { x | x ∈ a::l }, ∅ ⟩ }
				end
	end

def unified_debugging''
		(C A L₀: Type)
    (o : STR C A)
		(ape : APE' C A (L₁ L₀))
    (finder : Finder C A L₀)
    (breakpoints : L₁ L₀)
: STR (DebugConfig C) (@DebugAction C A) := 
{
	initial := 					debugInitial C A o,
	actions := λ dc, 		debugActions' C A o dc,
	execute := λ dc da, debugExecute'' C A L₀ o (finder ape) breakpoints dc da
}





def debugActions 
	(C A : Type) 
	(o : STR C A)
	(dc : DebugConfig C) : set (DebugAction C A) 
	:= match dc.current with 
        | (some c) := 
            let
                oa := { x : DebugAction C A  | 
                	∀ a ∈ (o.actions c), x = DebugAction.step a },
                ja := { x : DebugAction C A  | 
                	∀ c ∈ dc.trace,    x = DebugAction.jump c }
            in
                oa ∪ ja ∪ { DebugAction.run_to_breakpoint }
        | none := { sa | ∀ c ∈ dc.options, sa = DebugAction.select c }
        end

def debugActions'
	(C A : Type) 
	(o : STR C A)
	(dc : DebugConfig C) : set (DebugAction C A) 
	:= 
	let
		oa := { x : DebugAction C A | ∀ c, dc.current = some c -> ∀ a ∈ (o.actions c), x = step a },
		ja := { x : DebugAction C A | ∀ c ∈ dc.trace, x = jump c },
		sa := { x : DebugAction C A | ∀ c ∈ dc.options, x = select c }
	in oa ∪ ja ∪ { run_to_breakpoint  }

def debugRunToBreakpoint 
	(C A: Type)
	(o : STR C A)
	(finder : CounterExampleFinder C A)
	(breakpoints : set C)
	(start : set C)
	(current : DebugConfig C)
	: set (DebugConfig C) 
:= match (finder start o breakpoints) with 
	| []        := { current }
	| a::ctrace := { { DebugConfig . current := a, trace := {a} ∪ { x | x ∈ ctrace } ∪ current.trace, options := ∅ } }
end

def debugExecute
	(C A : Type) 
	(o : STR C A)
	(finder : CounterExampleFinder C A)
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
					debugRunToBreakpoint C A o finder breakpoints { c } dc
        	-- match (finder { c } o breakpoints) with 
        	-- 	| []        := { { DebugConfig . current := dc.current, 
        	-- 		trace := dc.trace, options := ∅ } }
        	-- 	| a::ctrace := { { DebugConfig . current := a,
        	-- 		trace := {a} ∪ { x | x ∈ ctrace } ∪ dc.trace, options := ∅ } }
        	-- end
    	| none, (DebugAction.run_to_breakpoint) := 
					debugRunToBreakpoint C A o finder breakpoints dc.options dc
        	-- match (finder dc.options o breakpoints) with 
        	-- 	| []        := { { DebugConfig . current := dc.current,
        	-- 		trace := dc.trace, options := ∅ } }
        	-- 	| a::ctrace := { { DebugConfig . current := a,
        	-- 		trace := {a} ∪ { x | x ∈ ctrace } ∪ dc.trace, options := ∅ } }
        	-- end
    end

def debugExecute'
	(C A : Type) 
	(o : STR C A)
	(finder : CounterExampleFinder C A)
	(breakpoints : set C)
	(dc : DebugConfig C) 
	(da : @DebugAction C A) 
	: set (DebugConfig C)
:= match da with 
	| DebugAction.step a :=   { x  | ∀ c, dc.current = some c -> x = ⟨ none, dc.trace, o.execute c a ⟩  }
	| DebugAction.select c := { { DebugConfig . current := c, trace := { c } ∪ dc.trace, options := ∅ } }
	| DebugAction.jump c   := { { DebugConfig . current := c, trace := { c } ∪ dc.trace, options := ∅ } }
	| DebugAction.run_to_breakpoint := 
				match dc.current with
				| some c  := debugRunToBreakpoint C A o finder breakpoints { c } 			dc
				| none		:= debugRunToBreakpoint C A o finder breakpoints dc.options dc
				end
	end

def debugExecute''
	(C A : Type) 
	(o : STR C A)
	(finder : CounterExampleFinder C A)
	(breakpoints : set C)
	(dc : DebugConfig C) 
	(da : @DebugAction C A) 
	: set (DebugConfig C)
:= match da with 
	| DebugAction.step a :=   { x  | ∀ c options, dc.current = some c -> 
																		options = o.execute c a ∧ options ≠ ∅ ->
																		x = ⟨ none, dc.trace, options ⟩  }
	| DebugAction.select c := { { DebugConfig . current := c, trace := { c } ∪ dc.trace, options := ∅ } }
	| DebugAction.jump c   := { { DebugConfig . current := c, trace := { c } ∪ dc.trace, options := ∅ } }
	| DebugAction.run_to_breakpoint := 
				match dc.current with
				| some c  := { x | 
						∀ a l, finder { c } o breakpoints = a::l →
							x = ⟨ a, dc.trace ∪ { x | x ∈ a::l }, ∅ ⟩ }
				| none		:= { x |
						∀ a l, finder dc.options o breakpoints = a::l ->
							x = ⟨ a, dc.trace ∪ { x | x ∈ a::l }, ∅ ⟩ }
				end
	end


def unified_debugging
	(C A : Type)
    (o : STR C A)
    (finder : CounterExampleFinder C A)
    (breakpoints : set C)
: STR (DebugConfig C) (@DebugAction C A) := 
{
	initial := 					debugInitial C A o,
	actions := λ dc, 		debugActions C A o dc,
	execute := λ dc da, debugExecute C A o finder breakpoints dc da
}

-- Formal definition for interactive multiverse debugging
def interactive_multiverse_debugging 
    (C A : Type)
    (o : STR C A)
    (finder : CounterExampleFinder C A)
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
        	match (finder { c } o breakpoints) with 
        		| []        := { { DebugConfig . current := dc.current, 
        			trace := dc.trace, options := ∅ } }
        		| a::ctrace := { { DebugConfig . current := a,
        			trace := {a} ∪ { x | x ∈ ctrace } ∪ dc.trace, options := ∅ } }
        	end
    	| none, (DebugAction.run_to_breakpoint) := 
        	match (finder dc.options o breakpoints) with 
        		| []        := { { DebugConfig . current := dc.current,
        			trace := dc.trace, options := ∅ } }
        		| a::ctrace := { { DebugConfig . current := a,
        			trace := {a} ∪ { x | x ∈ ctrace } ∪ dc.trace, options := ∅ } }
        end
    end
}

end debug