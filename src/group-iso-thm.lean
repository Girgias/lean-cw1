import tactic
import group_theory.quotient_group
import group_theory.subgroup.basic

namespace my_group_iso

variables {G : Type} [group G]

/-- f is the natural embedding of S in SN -/
def f {G : Type} [group G] {S N : subgroup G} [N.normal] :
  S →* (S ⊔ N : subgroup G) :=
    subgroup.inclusion le_sup_left

/-- g is the map from S to SN⧸N -/
def g {G : Type} [group G] (S N : subgroup G) [N.normal] :
  S →* (S ⊔ N : subgroup G)⧸(N.comap (S ⊔ N).subtype) :=
    -- Composition of the map f: S → SN with the quotient homomorphism SN → SN/N
    monoid_hom.comp (quotient_group.mk' (N.comap (S ⊔ N).subtype)) f

/-- The group homomorphism g: S → SN⧸N is surjective
  The proof is based on the one from mathlib -/
lemma g_is_surjective {S N : subgroup G} [N.normal] :
  function.surjective (g S N) :=
begin
  rw function.surjective,
  -- deconstruct ∀
  -- · y : G
  -- · hypothesis y ∈ SN
  rintro ⟨y, (hy : y ∈ ↑(S ⊔ N))⟩,
  -- As N normal, y ∈ (S ⊔ N) means y ∈ S*N
  rw subgroup.mul_normal S N at hy,
  -- Deconstruct y ∈ S*N
  -- s,n : G such that s ∈ S and n ∈ N
  -- s*n = y
  -- rfl changes instances of y to s*n
  rcases hy with ⟨s, n, hs, hn, rfl⟩,
  use s,
  exact hs,
  -- Pullback on the quotient map and move from g(s) to f(s)
  apply quotient.eq.mpr,
  -- I do not totally understand why it is definitionally equivalent to
  change s⁻¹ * (s * n) ∈ N,
  -- Rebracket
  rw ← mul_assoc,
  -- Cancel inverses
  rw inv_mul_self,
  -- simplify multiplication by identity
  rw one_mul,
  exact hn,
end

/- Proof that the kernel of g is S∩N -/
lemma g_ker_eq_S_intersect_N (S N : subgroup G) [N.normal] :
  ((g S N).ker : subgroup S) = (N.comap S.subtype) :=
begin
  ext,
  simp,
  split, {
    -- ker(g) ⊆ S∩N
    -- x ∈ ker(g)
    intro hxk,
    -- Being in the kernel is definitionally equal to sending an element
    -- to the identity
    change (g S N) x = 1 at hxk,
    -- Simplify g(x) = 1 to f(x) = 1
    dsimp [g] at hxk,
    simp at hxk,
    exact hxk,
  }, {
    -- S∩N ⊆ ker(g)
    -- hx : x ∈ N
    intro hx,
    -- Being in the kernel is definitionally equal to sending an element
    -- to the identity
    change (g S N) x = 1,
    -- Simplify g(x) = 1 to f(x) = 1
    dsimp [g],
    simp,
    exact hx,
  }
end

/--!
 - # The second isomorphism theorem for groups
 - If S, N ≤ G, and N is normal, then S⧸(S∩N) ≅ (SN)⧸N
 -/
noncomputable def second_iso (S N : subgroup G) [N.normal]:
  S ⧸ (N.comap S.subtype) ≃* (S ⊔ N : subgroup G) ⧸ (N.comap (S ⊔ N).subtype) :=
begin
  -- Get the isomorphism via the 1st isomorphism theorem where the LHS
  -- is quotiented by the kernel of the surjective homomorphism
  let e1 := quotient_group.quotient_ker_equiv_of_surjective (g S N) g_is_surjective,
  -- Claim that S⧸(S∩N) ≅ S⧸(ker(g))
  have h : ↥S ⧸ subgroup.comap S.subtype N ≃* ↥S ⧸ (g S N).ker,
  let e2 := quotient_group.equiv_quotient_of_eq (g_ker_eq_S_intersect_N S N),
  exact e2.symm,
  -- Transitivity of isomorphisms
  exact mul_equiv.trans h e1,
end

end my_group_iso