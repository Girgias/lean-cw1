import tactic
import group_theory.quotient_group
import group_theory.subgroup.basic
import category_theory.isomorphism

-- Proof wiki link: https://proofwiki.org/wiki/Isomorphism_Theorems

namespace my_group_iso

variables {G H : Type} [group G] [group H]
--variable {φ : G →* H}

--def K := φ.ker

variables {S N T : subgroup G}

theorem first_iso {φ : G →* H}{I : subgroup H} : G⧸φ.ker ≃* I :=
begin
  split, {-- left inverse
    sorry,},
    {
      -- right inverse
      sorry,
    }, {
      intros x y,
      sorry,
      ---refine map_mul _ x y,
      ---exact G,
      --refine {coe := _, coe_injective' := _, map_mul := _},
      --dsimp,
      --intro g,
      --intro gqk,
      --apply I.comap φ,
    }, {
      by subgroup.comap φ,
    }
end


--- ∩ ⊓

--- Quotient by doing ⧸ (not a normal slash) ∣ 


--def S ⊓ N : subgroup G

-- Given by Kevin try to understand def
 --S/S∩N ≅ SN/N :=
#check @subgroup.comap
-- S ⊔ N is the smallest subgroup of G containing S and N.
-- Which corresponds to SN
#check S ⊔ N

#check S.subtype
#check @N.comap

-- No working
-- theorem sec_iso_again {S N : subgroup G} [N.normal]: S ⧸ S ⊓ N ≃* S ⊔ N ⧸ N :=

/- φ is the natural homomorphism S →* (SN)/N. -/
def f : S →* _ ⧸ (N.comap (S ⊔ N).subtype) := 


theorem second_iso {S N : subgroup G} [N.normal]:
S ⧸ (N.comap S.subtype) ≃* _ ⧸ (N.comap (S ⊔ N).subtype) :=
--  (mk' $ N.comap (S ⊔ N).subtype).comp (inclusion le_sup_left)
begin
  split, {
    intro SqN,
    apply id,
    sorry,
  }, {
    sorry,
  }, {
    sorry,
  }, {
    -- → implication
    sorry,
  }, {
    intro hs,
    sorry,
  },
end

instance : has_inter G :=
{ inter := begin
  intro g,
  intro g,
  exact g,
end }

lemma intersection_of_subgroup_is_subgroup {S N : subgroup G} : S∩N subgroup G :=

-- Let R be an equivalence relation on X
variables (R : G → (G → Prop)) (h : equivalence R)

def s : setoid G := {r := R, iseqv := h }

-- how does Lean make the set Y such that f:X→Y is a surjection
-- and f(x₁) = f(x₂) ↔ R(x₁,x₂)


#check @quotient G
#check (s R h)


def N := @quotient G (s R h)
def S := @quotient G (s R h)



#check @quot.mk G

#check @K
/-
K : Π {G H : Type} [_inst_1 : group G] [_inst_2 : group H] {φ : G →* H}, 
  subgroup G
-/
/-
lemma theta_well_defined : :=
begin
end
-/



--#check Y X R h

end my_group_iso