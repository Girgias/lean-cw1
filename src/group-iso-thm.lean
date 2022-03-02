import tactic
import group_theory.quotient_group
import group_theory.subgroup.basic
import category_theory.isomorphism

-- Proof wiki link: https://proofwiki.org/wiki/Isomorphism_Theorems

namespace my_group_iso

variables {G H : Type} [group G] [group H]
--variable {φ : G →* H}

--def K := φ.ker

variables {S N T : subgroup G} [subgroup.normal N]

def first_iso {φ : G →* H}{I : subgroup H} : G⧸φ.ker ≃* I :=
{ to_fun := _,
  inv_fun := _,
  left_inv := _,
  right_inv := _,
  map_mul' := _ }

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
--#check @N.comap

-- No working
-- theorem sec_iso_again {S N : subgroup G} [N.normal]: S ⧸ S ⊓ N ≃* S ⊔ N ⧸ N :=

/- i is the natural homomorphism S →* (SN)/N. -/
--def i : S →* _ ⧸ (N.comap (S ⊔ N).subtype) :=

example {S N : subgroup G} [N.normal] : S →* (S ⊔ N : subgroup G) :=
begin
  refine subgroup.inclusion _,
  show_term{ intro s },
  show_term{intro hs},
  show_term{exact subgroup.mem_sup_left hs},
end

/- i is the natural homomorphism S → (SN) -/ ∈ 

-- See quotient_group.map maybe?
def i {G} [group G] {S N : subgroup G} [N.normal] :
  S →* (S ⊔ N : subgroup G) :=
    subgroup.inclusion le_sup_left

lemma intersection_is_subgroup {G} [group G] {S N : subgroup G} [N.normal] :
  S.subgroup (S⧸((S ⊓ N).comap S.subtype)) 

def i2 {G} [group G] {S N : subgroup G} [N.normal] :
-- .comap S.subtype changes it to be a subgroup of G to be a subgroup of S
  S⧸((S ⊓ N).comap S.subtype) →* (S ⊔ N : subgroup G) :=
begin
  refine i,
end

def i3 {G} [group G] {S N : subgroup G} [N.normal] :
-- .comap S.subtype changes it to be a subgroup of G to be a subgroup of S
  S⧸((S ⊓ N).comap S.subtype) →* (S ⊔ N : subgroup G)⧸(N.comap (S ⊔ N).subtype) :=

/- φ is the natural homomorphism S → (SN)⧸N -/
def φ {G} [group G] {S N : subgroup G} [N.normal] :
  --S →* (((S ⊔ N : subgroup G))⧸N : subgroup G) :=
  S →* _ ⧸ (N.comap (S ⊔ N).subtype) :=
  begin
    refine monoid_hom.restrict _ S,
    refine mul_equiv.to_monoid_hom _,
    refine mul_equiv.symm _,
  end

--#check quotient_group.lift i

#check quotient_group.map i N

#check φ '' ↑S
#check φ ⁻¹' ↑(S ⊔ N)

def f {G} [group G] {S: subgroup G} : S →* G :=
begin
  exact S.subtype,
end
def g {G} [group G] {N: subgroup G} [N.normal] : N →* G :=
begin
  exact N.subtype,
end
def h {G} [group G] {S N : subgroup G} [N.normal] : (S ⊔ N : subgroup G) →* G :=
begin
  refine f,
end

def second_iso {S N : subgroup G} [N.normal]:
S ⧸ (N.comap S.subtype) ≃* _ ⧸ (N.comap (S ⊔ N).subtype) :=
{
  to_fun := begin
    suggest,
  end,
  inv_fun := _,
  left_inv := _,
  right_inv := _,
  map_mul' := _
}


#check S.comap S.subtype

theorem third_iso_1 {S N : subgroup G} [S.normal] [N.normal] (h: N ≤ S) :
  subgroup.normal (S.comap S.subtype)⧸N) :=

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