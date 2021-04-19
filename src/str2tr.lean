import str tr
namespace str2tr

open str 
open tr 
------------------------------------------------------------------------------
--                         The STR to TR conversion                         --
------------------------------------------------------------------------------

-- Conversion from STR to TR
def STR2TR 
    (C A : Type)
    (str : STR C A)
    (acc : Acc C) 
: @TR C  := 
{ 
    initial := str.initial,
    next := λ c, { t | ∀ a ∈ str.actions c, t ∈ str.execute c a },
    accepting := acc.is_accepting
}

def STR2TR'
    (C A : Type)
    (str : STR C A)
    (acc : Acc' C) 
: @TR C := 
{ 
    initial := str.initial,
    next := λ c, { t | ∀ a ∈ str.actions c, t ∈ str.execute c a },
    accepting := acc
}
end str2tr
 