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
    next := λ c, { n | ∀ a ∈ str.actions c, ∀ t ∈ str.execute c a, n = t },
    accepting := acc.is_accepting
}
end str2tr
