import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Combinatorics.SimpleGraph.Basic

variable {V' : Type*} [Fintype V'] [DecidableEq V']
local notation "V" => @Finset.univ V' _
abbrev E' := Sym2 V'

#check {v : V' | v = v}          -- Set V'
#check {v : V' | v = v}.toFinset -- Finset V'
#check {v ∈ V | v = v}           -- Finset V'


variable (e : E')

#check e
#check {v : V' | v ∈ e}            -- Set V'
#check {v : V' | v ∈ e}.toFinset   -- Finset V'
#check {v ∈ V | v ∈ e}             -- Finset V'
