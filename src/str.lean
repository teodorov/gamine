namespace str

-- Semantic Transition Relation structure
structure STR (C A : Type) :=
    (initial : set C)
    (actions : C → set A) 
    (execute : C → A → set C)

-- Atomic Proposition Evaluator structure
structure APE (C A L : Type) :=
    (eval : L → C → A → C → bool)

-- Atomic Propositon Collector structure
structure APC (C A L : Type) :=
    (eval : C → A → set L)

-- Accepting structure
structure Acc (C : Type) :=
    (is_accepting : C -> Prop)

--projections
structure Projector (C A Vc Va: Type) :=
    (project_c : C → Vc) 
    (project_a : A → Va)

end str