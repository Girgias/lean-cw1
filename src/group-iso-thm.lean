import tactic
import group_theory.subgroup.basic

-- Proof wiki link: https://proofwiki.org/wiki/Isomorphism_Theorems

namespace my_group_iso

variables {G H : Type} [group G] [group H]
variable {φ : G →* H}

def K := φ.ker

#check @K
/-
K : Π {G H : Type} [_inst_1 : group G] [_inst_2 : group H] {φ : G →* H}, 
  subgroup G
-/

end my_group_iso