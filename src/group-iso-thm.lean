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

--def S ⊓ N : subgroup G

-- Given by Kevin try to understand def
 --S/S∩N ≅ SN/N :=
#check subgroup.comap
-- S ⊔ N is the smallest subgroup of G containing S and N.
-- Which corresponds to SN
#check S ⊔ N

/- i is the natural homomorphism S → (SN) -/
example {S N : subgroup G} [N.normal] : S →* (S ⊔ N : subgroup G) :=
begin
  refine subgroup.inclusion _,
  intro s,
  intro hs,
  exact subgroup.mem_sup_left hs,
end

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

--
--  (S⧸((S ⊓ N).comap S.subtype)) →* (S ⊔ N : subgroup G)⧸(N.comap (S ⊔ N).subtype) :=
def i3 {G} [group G] (S N : subgroup G) [N.normal] :
  (S ⧸ (N.comap S.subtype)) →* (S ⊔ N : subgroup G)⧸(N.comap (S ⊔ N).subtype) :=
begin
  apply quotient_group.lift (N.comap S.subtype) (i2 S N),
  intro s,
  intro hs,
  rw subgroup.mem_comap at hs,
  rw subgroup.coe_subtype at hs,
  dsimp [i2],
  rw quotient_group.eq_one_iff,
  rw subgroup.mem_comap,
  rw subgroup.coe_subtype,
  exact hs,
end

#check quotient_group.quotient_ker_equiv_of_surjective (i3 S N)

lemma i3_is_bijective : function.bijective (i3 S N) :=
begin
  --refine function.bijective_iff_has_inverse.mpr _,
  rw function.bijective,
  split, {
    -- proof function is injective
    rw function.injective,
    intros x y,
    dsimp[i3],
    intro h,
    --rw subgroup.mem_comap at h,
    --rw subgroup.coe_subtype at h,
    apply quotient.induction_on₂ x y,
    sorry,
  }, {
    -- proof function is surjective
    rw function.surjective,
    --rintro ⟨y, (hy : y ∈ (S ⊔ N : subgroup G))⟩,
    --have hys : y ∈ S, 
    intro y,
    dsimp[i3],
    sorry,
  },
end

def second_iso (S N : subgroup G) [N.normal]:
  S ⧸ (N.comap S.subtype) ≃* (S ⊔ N : subgroup G) ⧸ (N.comap (S ⊔ N).subtype) :=
{
  to_fun := (i3 S N),
  inv_fun := _,
  left_inv := _,
  right_inv := _,
  map_mul' := _
}

#check quotient_group.map (N.comap S.subtype) (N.comap (S⊔N).subtype) i

def i4 {G} [group G] {S N : subgroup G} [N.normal] :
-- .comap S.subtype changes it to be a subgroup of G to be a subgroup of S
  S⧸((S ⊓ N).comap S.subtype) →* (S ⊔ N : subgroup G)⧸(N.comap (S ⊔ N).subtype) :=
begin sorry end


#check i '' ↑S
#check i ⁻¹' ↑(S ⊔ N)

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

#check S.comap S.subtype

theorem third_iso_1 {S N : subgroup G} [S.normal] [N.normal] (h: N ≤ S) :
  subgroup.normal ((S.comap S.subtype)⧸(N.comap S.subtype)) := sorry

end my_group_iso