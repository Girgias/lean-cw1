import tactic
import data.nat.basic
import combinatorics.simple_graph.connectivity
import combinatorics.simple_graph.subgraph

namespace simple_graph

-- Stolen from sheet 12 of the lecture notes
def is_connected {V : Type} (G : simple_graph V) : Prop :=
nonempty V ∧ ∀ u v : V, ∃ p : G.walk u v, p.is_path

lemma walk_id_eq {V : Type} {a b c : V} {G : simple_graph V} (he : a = b) (p : G.walk a c) :
  G.walk b c := begin
    rw he at p, exact p,
end

namespace box_product

/--
For non-empty simple graphs G and H, the box product graph G□H is the graph
with vertex set V_G × V_H, where the edge relation is given by
(g₂, h₁)E(g₂, h₂) ↔ (h₁ = h₂ ∧ g₁Eg₂) ∨ (g₁ = g₂ ∧ h₁Eh₂)
-/
def box_product {V W : Type} (G : simple_graph V) (H : simple_graph W) :
  simple_graph (V × W) :=
{
  -- a b : U × V;
  -- `.1` corresponds to an element of G `.2` corresponds to an element of H
  adj := λ (a b), (a.2 = b.2 ∧ G.adj a.1 b.1) ∨ (a.1 = b.1 ∧ H.adj a.2 b.2),
  symm := begin
    intros a b,
    cases a;
    cases b;
    simp,
    intro h,
    cases h with hg hh,
    -- First handle the reflexivity of edge relation on G
    {
      left,
      cases hg with hconst gadj,
      exact ⟨hconst.symm, gadj.symm⟩,
    },
    -- Second handle the reflexivity of edge relation on H
    {
      right,
      cases hh with gconst hadj,
      exact ⟨gconst.symm, hadj.symm⟩,
    }
  end,
  -- copied from the definition of complete_bipartite_graph in simple_graph.basic
  loopless := begin
    intro v,
    cases v; simp,
  end
}

/-!
Define the binary operator □ (typed with ``\square``) which gives the box product
of two graphs. 
-/
infix `□`:50 := box_product

def is_box_product {V W : Type} (B : simple_graph (V × W)) (G : simple_graph V) (H : simple_graph W) : Prop :=
  ∀ x y : V×W, B.adj x y ↔ ((x.2=y.2 ∧ G.adj x.1 y.1) ∨ (x.1=y.1 ∧ H.adj x.2 y.2))

lemma box_product_is_box_product {V W : Type} (G : simple_graph V) (H : simple_graph W) :
  is_box_product (G□H) G H :=
begin
  intros x y,
  refl,
end

/-- The adjacency relation of the box product when vetices are in terms of V and W -/
lemma box_adj_rel {V W : Type} {a b : V} {x y : W} {G : simple_graph V} {H : simple_graph W} :
  (G□H).adj (a, x) (b, y) ↔ (x = y ∧ G.adj a b) ∨ (a = b ∧ H.adj x y) :=
begin
  refl,
end

/-- The adjacency relation of the box product when vetices are in terms of V×W -/
lemma box_adj_rel_prod {V W : Type} {a b : V×W} {G : simple_graph V} {H : simple_graph W} :
  (G□H).adj a b ↔ (a.snd = b.snd ∧ G.adj a.fst b.fst) ∨ (a.fst = b.fst ∧ H.adj a.snd b.snd) :=
begin
  refl,
end

/-- Proof that the two different agency relations are equivalent -/
lemma box_adj_rels_equiv {V W : Type} {v w : V×W}
  {G : simple_graph V} {H : simple_graph W} :
  (G□H).adj (v.fst, v.snd) (w.fst, w.snd) ↔ (G□H).adj v w :=
begin
  refl,
end

/-- The box product is commutative up to isomorphism -/
def box_product_comm {V W : Type} (G : simple_graph V) (H : simple_graph W) :
  G□H ≃g (H□G) :=
{
to_equiv := equiv.prod_comm V W,
map_rel_iff' := begin
  intros a b,
  split, {
    rw [box_adj_rel_prod, equiv.prod_comm_apply, prod.snd_swap, prod.fst_swap],
    intro hHGadj,
    cases hHGadj with hHadj hGadj, {
      right,
      exact hHadj,
    },{
      left,
      exact hGadj,
    },
  }, {
    intro hHGadj,
    rw [box_adj_rel_prod, equiv.prod_comm_apply, prod.snd_swap, prod.fst_swap],
    cases hHGadj with hGadj hHadj, {
      right,
      exact hGadj,
    }, {
      left, exact hHadj,
    }
  }
end,
}

/-- The box product is commutative up to isomorphism -/
def box_product_assoc {U V W : Type} (G : simple_graph U)
  (H : simple_graph V) (K : simple_graph W) :
  ((G□H)□K) ≃g (G□(H□K)) := 
{
  to_equiv := equiv.prod_assoc U V W,
  map_rel_iff' := begin
    intros a b,
    rw [equiv.prod_assoc_apply, box_adj_rel_prod, equiv.prod_assoc_apply, prod.mk.inj_iff],
    split, {
      intro h,
      cases h with hBGadj hBHK, {
        left,
        rcases hBGadj with ⟨⟨eq_b, eq_c⟩, hGadj⟩,
        exact ⟨eq_c, or.inl ⟨eq_b, hGadj⟩⟩,
      }, {
        rcases hBHK with ⟨eq_a, hBHKadj⟩,
        dsimp at *,
        cases hBHKadj with hBHadj hBKadj, {
          left,
          dsimp only at hBHadj,
          cases hBHadj with eq_c hHadj,
          exact ⟨eq_c, or.inr ⟨eq_a, hHadj⟩⟩,
        }, {
          right,
          simp at hBKadj,
          cases hBKadj with eq_b hKadj,
          exact ⟨prod.ext eq_a eq_b, hKadj⟩,
        },
      },
    }, {
      intro h,
      rw box_adj_rel_prod at *,
      simp only,
      cases h with hBGH rhs, {
        --rcases hBGH with ⟨eq_c, ⟨eq_b, hGadj⟩, hHadj⟩,
        cases hBGH with eq_c hGHadj,
        cases hGHadj with hGadj hHadj, {
          left,
          cases hGadj with eq_b hG,
          rw [eq_b, eq_self_iff_true, true_and],
          exact ⟨eq_c, hG⟩,
        }, {
          cases hHadj with eq_a hH,
          right,
          split, {
            exact eq_a,
          }, {
            left,
            exact ⟨eq_c, hH⟩,
          }
        },
      }, {
        right,
        cases rhs with eq_a_and_b hKadj,
        rw [eq_a_and_b, eq_self_iff_true, true_and],
        simp only [irrefl, and_false, eq_self_iff_true, true_and, false_or],
        exact hKadj,
      },
    },
  end
}

-- Adjacency relations move between the simple graph and the box product
lemma lift_adj_lhs {V W : Type} {a b : V} {G : simple_graph V} {H : simple_graph W} (w : W)
  (hGadj : G.adj a b) : (G□H).adj (a, w) (b, w) :=
begin
  left,
  rw [eq_self_iff_true, true_and],
  exact hGadj,
end

lemma descend_adj_lhs {V W : Type} {a b : V} {G : simple_graph V} {H : simple_graph W}
  (w : W) :
  (G□H).adj (a, w) (b, w) → G.adj a b :=
begin
  rw box_adj_rel,
  intro h,
  cases h with hGB hHB, { 
    exact hGB.2,
  }, {
    -- H is a simple graph so there is no edge between w and w
    -- This is the condition irrefel,
    -- and_false simplifies the hyp as if one side of an AND is false than the prop is false
    simp only [irrefl, and_false] at hHB,
    exfalso,
    exact hHB,
  }
end

lemma adj_lhs_equiv {V W : Type} {a b : V} (y : W)
  (G : simple_graph V) (H : simple_graph W) :
  (G□H).adj (a, y) (b, y) ↔ G.adj a b := ⟨descend_adj_lhs y, lift_adj_lhs y⟩

lemma lift_adj_rhs {V W : Type} {a b : W} {G : simple_graph V} {H : simple_graph W}
  (v : V) (hHadj : H.adj a b) : (G□H).adj (v, a) (v, b) :=
begin
  right,
  rw [eq_self_iff_true, true_and],
  exact hHadj,
end

lemma descend_adj_rhs {V W : Type} {a b : W} {G : simple_graph V}
  {H : simple_graph W} (v : V) :
  (G□H).adj (v, a) (v, b) → H.adj a b :=
begin
  intro h,
  cases h with hGB hHB, {
    simp only [irrefl, and_false] at hGB,
    exfalso,
    exact hGB,
  }, {
    exact hHB.2,
  }
end

lemma adj_rhs_equiv {V W : Type} {a b : W} {G : simple_graph V}
  {H : simple_graph W} (x : V) :
  (G□H).adj (x, a) (x, b) ↔ H.adj a b := ⟨descend_adj_rhs x, lift_adj_rhs x⟩

-- Lifts of walks from the simple graph to the box product

-- Kevin helped with writting the inductive type here
def lift_walk_lhs {V W : Type} (y : W) (G : simple_graph V) (H : simple_graph W)
  : Π {a b : V},
  (G.walk a b) → (G□H).walk (a, y) (b, y)
| _ _ simple_graph.walk.nil := walk.nil
| a b (@simple_graph.walk.cons _ _ _ c _ hGadj w)
  := walk.cons (lift_adj_lhs y hGadj) (lift_walk_lhs w)

def lift_walk_rhs {V W : Type} (x : V) (G : simple_graph V) (H : simple_graph W)
  : Π {a b : W},
  (H.walk a b) → (G□H).walk (x, a) (x, b)
| _ _ simple_graph.walk.nil := walk.nil
| a b (@simple_graph.walk.cons _ _ _ c _ hHadj p)
  := walk.cons (lift_adj_rhs x hHadj) (lift_walk_rhs p)

/--
  The box product G□H is connected if and only if G and H are connected
  The proof is to compose a lifted path of G with a lifted path of H
-/
lemma G_box_H_is_connected_if_G_H_connected {V W : Type} (G : simple_graph V) (H : simple_graph W) :
  G.is_connected ∧ H.is_connected → (G□H).is_connected :=
begin
  intro h,
  cases h with hG_connected hH_connected,
  rw is_connected at *,
  cases hG_connected with hG_not_empty hg,
  cases hH_connected with hH_not_empty hh,
  split, {
    -- Proof that the vertex set of G□H is not empty
    rw nonempty_prod,
    exact ⟨hG_not_empty, hH_not_empty⟩,
  }, {
    rintros ⟨g1, h1⟩ ⟨g2, h2⟩,
    -- ∃ a path from g₁ to g₂
    specialize hg g1 g2,
    -- ∃ a path from h₁ to h₂
    specialize hh h1 h2,
    -- extract the walks
    cases hg with pg _,
    cases hh with ph _,
    -- lift the walk in G along the vertex h₁
    set wg := lift_walk_lhs h1 G H pg,
    -- lift the walk in H along the vertex g₂
    set wh := lift_walk_rhs g2 G H ph,
    -- Get a walk from (g₁, h₁) to (g₂, h₂)
    set w := walk.append wg wh,
    -- Fix decidability
    classical,
    -- Create a path from the walk
    set p := (simple_graph.walk.to_path w),
    use p,
    -- p.2 is the field which has the proof that p is a path
    exact p.2,
  }
end

-- Thanks Kenny Lau
def descend_walk_lhs {V W : Type} [decidable_eq V] [decidable_eq W]
  {G : simple_graph V} {H : simple_graph W} [decidable_rel G.adj] [decidable_rel H.adj]
  : Π {vw1 vw2 : V × W},
  (G□H).walk vw1 vw2 → (G.walk vw1.1 vw2.1)
| _ _ simple_graph.walk.nil := walk.nil
| vw1 vw3 (@simple_graph.walk.cons _ _ _ vw2 _ hGHadj p) :=
or.by_cases hGHadj (λ hBG, walk.cons hBG.2 (descend_walk_lhs p))
  (λ hBH, show G.walk vw1.1 vw3.1, by rw hBH.1; exact descend_walk_lhs p)

def descend_walk_rhs {V W : Type} [decidable_eq V] [decidable_eq W]
  {G : simple_graph V} {H : simple_graph W} [decidable_rel G.adj] [decidable_rel H.adj]
  : Π {vw1 vw2 : V × W},
  (G□H).walk vw1 vw2 → (H.walk vw1.2 vw2.2)
| _ _ simple_graph.walk.nil := walk.nil
| vw1 vw3 (@simple_graph.walk.cons _ _ _ vw2 _ hGHadj p) :=
or.by_cases hGHadj (λ hGB, show H.walk vw1.2 vw3.2, by rw hGB.1; exact descend_walk_rhs p)
  (λ hHB, walk.cons hHB.2 (descend_walk_rhs p))
  

lemma G_and_H_connected_if_G_box_H_connected {V W : Type} /-[decidable_eq V] [decidable_eq W]-/
  (G : simple_graph V) (H : simple_graph W) /-[decidable_rel G.adj] [decidable_rel H.adj]-/ :
  (G□H).is_connected → G.is_connected ∧ H.is_connected :=
begin
  intros hGH_connected,
  cases hGH_connected with hGH_not_empty hGH_has_path,
  rw nonempty_prod at hGH_not_empty,
  cases hGH_not_empty with hG_not_empty hH_not_empty,
  split, {
    -- G is connected
    split, {
      exact hG_not_empty,
    }, {
      -- G has a path for all g₁ g2
      intros g1 g2,
      set h := hH_not_empty.some,
      specialize hGH_has_path (g1, h) (g2, h),
      cases hGH_has_path with GHw hGHw_p,
      classical,
      set w := descend_walk_lhs GHw,
      -- Create a path from the walk
      set p := (simple_graph.walk.to_path w),
      use p,
      -- p.2 is the field which has the proof that p is a path
      exact p.2,
    },
  }, {
    split, {
      exact hH_not_empty,
    }, {
      -- H has a path for all h₁ h2
      intros h1 h2,
      set g := hG_not_empty.some,
      specialize hGH_has_path (g, h1) (g, h2),
      cases hGH_has_path with GHw hGHw_p,
      classical,
      set w := descend_walk_rhs GHw,
      -- Create a path from the walk
      set p := (simple_graph.walk.to_path w),
      use p,
      -- p.2 is the field which has the proof that p is a path
      exact p.2,
    },
  },
end

theorem G_box_H_is_connected_iff_G_H_connected {V W : Type} (G : simple_graph V) (H : simple_graph W) :
  G.is_connected ∧ H.is_connected ↔ (G□H).is_connected :=
begin
  split,
  { exact G_box_H_is_connected_if_G_H_connected G H, },
  { exact G_and_H_connected_if_G_box_H_connected G H, },
end


----- More stuff that IDK if I want/need

variables {U V W : Type} (G : simple_graph U) (H : simple_graph V)

-- TODO prove that (g_i, h) is iso to G and (g, h_i) is iso to H

lemma lhs_embedded_in_box {V W : Type} (G : simple_graph V) (H : simple_graph W) :
  G ↪g (G□H) :=
begin
  sorry,
end

/- Can't write this yet? Need is_box_product?
lemma lhs_induced_box {V W : Type} (G : simple_graph V) (H : simple_graph W) :
  G (G□H) :=
begin
end
-/

lemma left_induced_box_product {V W : Type} (G : simple_graph V) (H : simple_graph W)
  (B : simple_graph V×W) : Prop := sorry

end box_product
end simple_graph