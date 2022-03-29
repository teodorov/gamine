import data.set data.set.finite

/-!
  # A reachability algorithm as STR
-/
structure ReachConfig (C α : Type) :=
  (known : set C)
  (frontier : list C)
  (init : bool)

inductive ReachAction (C : Type)
| meet : ReachAction
| expand : C → ReachAction
| the_end : ReachAction

def toList { C : Type }[fintype C] (s : set C) : list C := sorry

open ReachAction
def ReachabilitySTR (C α : Type)[fintype C] (abstraction : C → α) (o : TR C) : STR (ReachConfig C α) (ReachAction C) :=
{
  initial := { ⟨ ∅, ∅, true ⟩ },
  actions := λ rc,
    match rc with
    | ⟨_,     _, tt⟩ := { meet     }
    | ⟨_,    [], ff⟩ := { the_end  }
    | ⟨_, c::cs, ff⟩ := { expand c }
    end,

  execute := λ rc ra, let abs := λ N : set C, {x | ∃ y ∈ N, abstraction x = abstraction y } in
    match rc, ra with
    | ⟨K, F, I⟩,    meet      := let N := o.initial in { ⟨ K ∪ abs N, F ++ toList N, ff⟩ }
    | ⟨K, c::F, I⟩, expand oc := let N := o.next c  in { ⟨ K ∪ abs N, F ++ toList (N \ K), ff⟩ }
    | ⟨K, [], I⟩,   expand oc := {} -- cannot get here, actions cannot generate this case
    | ⟨K, F, I⟩,    the_end      := { ⟨ K, F, ff⟩ }
    end
}


def xecute {C A α : Type} : STR C A → C → set C 
| o c := {x | ∀ a ∈ o.actions c, ∀ t ∈ (STR.execute o c a), x = xecute o t}