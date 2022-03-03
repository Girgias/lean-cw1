import tactic
import data.quot
import group_theory.quotient_group
import group_theory.subgroup.basic

-- Proof wiki link: https://proofwiki.org/wiki/Isomorphism_Theorems

namespace my_group_iso

variables {G H : Type} [group G] [group H]
--variable {φ : G →* H}

--def K := φ.ker

variables {S N T : subgroup G} [subgroup.normal N]

/-
def first_iso {φ : G →* H}{I : subgroup H} : G⧸φ.ker ≃* I :=
{ to_fun := _,
  inv_fun := _,
  left_inv := _,
  right_inv := _,
  map_mul' := _ }

-/
--- ∩ ⊓

--- Quotient by doing ⧸ (not a normal slash) ∣ 


--def S ⊓ N : subgroup G

-- Given by Kevin try to understand def
 --S/S∩N ≅ SN/N :=
#check subgroup.comap
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
  intro s,
  intro hs,
  exact subgroup.mem_sup_left hs,
end

/- i is the natural homomorphism S → (SN) -/
example {S N : subgroup G} [N.normal] : S →* (S ⊔ N : subgroup G) :=
begin
  refine subgroup.inclusion _,
  intro s,
  intro hs,
  exact subgroup.mem_sup_left hs,
end

#check @quotient_group.mk' S ((S ⊓ N).comap S.subtype)

#check quotient_group.mk' ((S ⊓ N).comap S.subtype)

#check S⧸((S ⊓ N).comap S.subtype)

def i {G} [group G] {S N : subgroup G} [N.normal] :
  S →* (S ⊔ N : subgroup G) :=
    subgroup.inclusion le_sup_left

#check monoid_hom.comp

def i2 {G} [group G] (S N : subgroup G) [N.normal] :
  S →* (S ⊔ N : subgroup G)⧸(N.comap (S ⊔ N).subtype) :=
begin
  apply monoid_hom.comp (quotient_group.mk' (N.comap (S ⊔ N).subtype)),
  exact i,
end

--#check (S ⧸ (N.comap S.subtype)).lift i2
#check quotient_group.lift (N.comap S.subtype) (i2 S N)

def i3 {G} [group G] {S N : subgroup G} [N.normal] :
--  (S⧸((S ⊓ N).comap S.subtype)) →* (S ⊔ N : subgroup G)⧸(N.comap (S ⊔ N).subtype) :=
  (S ⧸ (N.comap S.subtype)) →* (S ⊔ N : subgroup G)⧸(N.comap (S ⊔ N).subtype) :=
begin
  apply quotient_group.lift (N.comap S.subtype) (i2 S N),
  -- TODO
  sorry,
end

lemma i2_is_surjective : function.surjective (i2 S N) :=
begin
  -- rewrite def
  --rw function.surjective,
  -- deconstruct ∀ to y is an element of the group G and the hyp as to why it's in SN
  rintro ⟨y, (hy : y ∈ ↑(S ⊔ N))⟩,
  -- change y ∈ ↑(S ⊔ N) to y ∈ ↑S*↑N
  rw subgroup.mul_normal S N at hy,
  rcases hy with ⟨s, n, hs, hn, rfl⟩,
  -- Why need the square brackets?
  --use [s, hs],
  use s,
  exact hs,
  -- not sure what this does
  apply quotient.eq.mpr,
  change s⁻¹ * (s * n) ∈ N,
  rw ← mul_assoc,
  rw inv_mul_self,
  rw one_mul,
  exact hn,
end

-- See quotient_group.map maybe?

def i4 {G} [group G] {S N : subgroup G} [N.normal] :
-- .comap S.subtype changes it to be a subgroup of G to be a subgroup of S
  S⧸((S ⊓ N).comap S.subtype) →* (S ⊔ N : subgroup G)⧸(N.comap (S ⊔ N).subtype) :=
begin sorry end

/- φ is the natural homomorphism S → (SN)⧸N -/
def φ {G} [group G] {S N : subgroup G} [N.normal] :
  --S →* (((S ⊔ N : subgroup G))⧸N : subgroup G) :=
  S →* _ ⧸ (N.comap (S ⊔ N).subtype) :=
  begin
    refine monoid_hom.restrict _ S,
    refine mul_equiv.to_monoid_hom _,
    refine mul_equiv.symm _,
    sorry,
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
S ⧸ (N.comap S.subtype) ≃* (S ⊔ N : subgroup G) ⧸ (N.comap (S ⊔ N).subtype) :=
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