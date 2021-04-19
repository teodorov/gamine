import str str2tr tr synchronous_composition propositional
namespace assert

open str str2tr tr operators propositional

def predicate_asserter (L₀ : Type) (pred : L₁ L₀) : STR bool (L₁ L₀ × bool) :=
{
  initial := { false },
  actions := λ c, 
    if c 
    then ∅
    else 
      {(       pred, true),
       (L₁.not pred, false)},
  execute := λ c a, { a.2 }
}

def assert_SLI (L₀ : Type) (assert : L₁ L₀) : SLI' bool (L₁ L₀ × bool) unit (L₁ L₀):=
{
  str := predicate_asserter L₀ assert,
  ape := λ x s a t, false,
  apc := λ c a, a.1,
  acc := λ c, c
}

def assert_sapc (L₀ : Type) : bool → (L₁ L₀ × bool) → L₁ L₀ 
| _ a := a.1

def apc (L₀ : Type) : bool → (L₁ L₀ × bool) → L₁ L₀ := λ c a, a.1
def assert_APC' (L₀:Type) : APC' bool (L₁ L₀ × bool) (L₁ L₀) := λ c a, a.1

def assert_APC (L₀ : Type) : APC bool (L₁ L₀ × bool) (L₁ L₀) :=
{ eval := λ c a, { a.1 } }

def collector (L₀ : Type) : L₁ L₀ → set L₀
| (L₁.not e)     := collector e
| (L₁.and e₁ e₂) := collector e₁ ∪ collector e₂
| (L₁.var e)     := { e }

def assert_apc (L₀ : Type) : bool → (L₁ L₀ × bool) → set L₀ 
| _ a := collector L₀ a.1

def preinitialized (C A : Type) (initial : set C) (s : STR C A) : STR C A :=
{
  initial := initial,
  actions := s.actions,
  execute := s.execute
}

def finder (C A L₀ : Type) (ape : APE' C A (L₁ L₀)) (o : STR C A) (breakpoints : L₁ L₀) (start : set C) : TR (C×bool) :=
  STR2TR' (C×bool) (A × (L₁ L₀ × bool))
    (synchronous_composition' C bool A (L₁ L₀ × bool) (L₁ L₀)
      (preinitialized C A start o)
      (ape) 
      (predicate_asserter L₀ breakpoints) 
      (λ c a, a.1)) 
    (λ c,  c.2)

end assert