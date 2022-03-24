import tactic
import data.nat.basic
import combinatorics.simple_graph.connectivity
import combinatorics.simple_graph.subgraph

namespace simple_graph

-- Stolen from sheet 12 of the lecture notes
def is_connected {V : Type} (G : simple_graph V) : Prop :=
nonempty V ∧ ∀ u v : V, ∃ p : G.walk u v, p.is_path

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

lemma box_adj_rel {V W : Type} {a b : V} {x y : W} {G : simple_graph V} {H : simple_graph W} :
  (G□H).adj (a, x) (b, y) ↔ (x = y ∧ G.adj a b) ∨ (a = b ∧ H.adj x y) :=
begin
  refl,
end

lemma box_adj_rel_prod {V W : Type} {a b : V×W} {G : simple_graph V} {H : simple_graph W} :
  (G□H).adj a b ↔ (a.snd = b.snd ∧ G.adj a.fst b.fst) ∨ (a.fst = b.fst ∧ H.adj a.snd b.snd) :=
begin
  refl,
end

lemma box_adj_rels_equiv_extra {V W : Type} {a b : V} {x y : W} {g h : V×W}
  {G : simple_graph V} {H : simple_graph W} :
  ((G□H).adj (a, x) (b, y) ↔ (x = y ∧ G.adj a b) ∨ (a = b ∧ H.adj x y)) ↔
  ((G□H).adj g h ↔ (g.snd = h.snd ∧ G.adj g.fst h.fst) ∨ (g.fst = h.fst ∧ H.adj g.snd h.snd)) :=
begin
  split, {
    intro _,
    rw box_adj_rel_prod,
  }, {
    intro _,
    rw box_adj_rel,
  },
end

lemma box_adj_rels_equiv {V W : Type} {v w : V×W}
  {G : simple_graph V} {H : simple_graph W} :
  (G□H).adj (v.fst, v.snd) (w.fst, w.snd) ↔ (G□H).adj v w :=
begin
  refl,
end

theorem box_product_comm {V W : Type} (G : simple_graph V) (H : simple_graph W) :
  G□H ≃g (H□G) :=
{
to_equiv := equiv.prod_comm V W,
map_rel_iff' := begin
  intros a b,
  split, {
    rw box_adj_rel_prod,
    simp,
    intro h,
    cases h with hh hg, {
      right,
      exact hh,
    },{
      left,
      exact hg,
    },
  }, {
    intro h,
    rw box_adj_rel_prod at *,
    simp,
    cases h with hg hh, {
      right,
      exact hg,
    }, {
      left, exact hh,
    }
  }
end,
}

theorem box_product_assoc {U V W : Type} (G : simple_graph U)
  (H : simple_graph V) (K : simple_graph W) :
  ((G□H)□K) ≃g (G□(H□K)) :=
{
  to_equiv := equiv.prod_assoc U V W,
  map_rel_iff' := begin
    intros a b,
    simp,
    split,
    rw box_adj_rel_prod,
    {
      simp,
      intro h,
      cases h with lhs rhs, {
        cases lhs with eq hGadj,
        cases eq with eq1 eq2,
        left,
        split, {
          exact eq2,
        }, {
          left,
          exact ⟨eq1, hGadj⟩,
        },
      }, {
        cases rhs with eq hHKadj,
        cases hHKadj with hHadj hKadj,
        {
          simp at hHadj,
          cases hHadj with eq2 hH,
          left,
          split, {
            exact eq2,
          }, {
            right,
            exact ⟨eq, hH⟩,
          },
        }, {
          right,
          simp at hKadj,
          cases hKadj with eq2 hK,
          exact ⟨prod.ext eq eq2, hK⟩,
        },
      },
    }, {
      intro h,
      cases h with lhs rhs, {
        cases lhs with eq hGHadj,
        cases hGHadj with hGadj hHadj, {
          left,
          cases hGadj with eq2 hG,
          rw eq2,
          simp,
          exact ⟨eq, hG⟩,
        }, {
          cases hHadj with eq2 hH,
          right,
          simp,
          split, {
            exact eq2,
          }, {
            left,
            simp,
            exact ⟨eq, hH⟩,
          }
        },
      }, {
        cases rhs with eq hKadj,
        rw eq,
        right,
        simp,
        right,
        simp,
        exact hKadj,
      },
    },
  end
}

lemma lift_adj_lhs {V W : Type} {a b : V} {w : W} {G : simple_graph V} {H : simple_graph W} :
  G.adj a b → (G□H).adj (a, w) (b, w) :=
begin
  intro h,
  left,
  simp only [eq_self_iff_true, true_and],
  exact h,
end

lemma lift_adj_rhs {V W : Type} {v : V} {a b : W} {G : simple_graph V} {H : simple_graph W} :
  H.adj a b → (G□H).adj (v, a) (v, b) :=
begin
  intro h,
  right,
  simp only [eq_self_iff_true, true_and],
  exact h,
end

-- Kevin helped with writting the inductive type here
def lift_walk_lhs {V W : Type} (w : W) (G : simple_graph V) (H : simple_graph W)
  : Π {a b : V},
  (G.walk a b) → (G□H).walk (a, w) (b, w)
| a _ simple_graph.walk.nil := walk.nil
| a b (@simple_graph.walk.cons _ _ _ c _ h p)
  := walk.cons (lift_adj_lhs h) (lift_walk_lhs p)

def lift_walk_rhs {V W : Type} (v : V) (G : simple_graph V) (H : simple_graph W)
  : Π {a b : W},
  (H.walk a b) → (G□H).walk (v, a) (v, b)
| a _ simple_graph.walk.nil := walk.nil
| a b (@simple_graph.walk.cons _ _ _ c _ h p)
  := walk.cons (lift_adj_rhs h) (lift_walk_rhs p)

lemma G_box_H_is_connected_if_G_H_connected {V W : Type} (G : simple_graph V) (H : simple_graph W) :
  G.is_connected ∧ H.is_connected → (G□H).is_connected :=
begin
  intro h,
  cases h with hG_connected hH_connected,
  rw is_connected at *,
  cases hG_connected with hG_not_empty hg,
  cases hH_connected with hH_not_empty hh,
  split,
  {
    rw nonempty_prod,
    exact ⟨hG_not_empty, hH_not_empty⟩,
  }, {
    intros a b,
    set g1 := a.1,
    set h1 := a.2,
    set g2 := b.1,
    set h2 := b.2,
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
    -- Helpers for Lean to understand that the walk is actually in V×W
    have eq1 : a = (g1, h1),
    { simp only [prod.mk.eta], },
    have eq2 : b = (g2, h2),
    { simp only [prod.mk.eta], },
    rw ← eq1 at w,
    rw ← eq2 at w,
    -- Fix decidability
    classical,
    -- Create a path from the walk
    set p := (simple_graph.walk.to_path w),
    use p,
    -- p.2 is the field which has the proof that p is a path
    exact p.2,
  }
end

--- `simple_graph.walk.to_path` MEMO
#check @simple_graph.walk.to_path

lemma descend_adj_lhs {V W : Type} {a b : V} (w : W) (G : simple_graph V)
  (H : simple_graph W) :
  (G□H).adj (a, w) (b, w) → G.adj a b :=
begin
  rw box_adj_rel,
  intro h,
  cases h with hGB hHB,
  { 
    cases hGB with _ hG,
    exact hG,
  },
  {
    -- H is a simple graph so there is no edge between w and w
    -- This is the condition irrefel,
    -- and_false simplifies the hyp as if one side of an AND is false than the prop is false
    simp only [irrefl, and_false] at hHB,
    exfalso,
    exact hHB,
  }
end

lemma descend_adj_lhs_prod {V W : Type} {a b : V×W} {G : simple_graph V}
  {H : simple_graph W} (he : a.snd = b.snd) :
  (G□H).adj a b → G.adj a.fst b.fst :=
begin
  intro h,
  cases h with hGB hHB,
  { 
    cases hGB with _ hG,
    exact hG,
  }, {
    cases hHB with eq hH,
    rw he at hH,
    exfalso,
    apply irrefl,
    exact hH,
  }
end

lemma descend_adj_rhs {V W : Type} {v : V} {a b : W} {G : simple_graph V}
  {H : simple_graph W} :
  (G□H).adj (v, a) (v, b) → H.adj a b :=
begin
  rw box_adj_rel,
  intro h,
  cases h with hGB hHB,
  { 
    -- Need to get explanation on
    simp only [irrefl, and_false] at hGB,
    exfalso,
    exact hGB,
  },
  {
    cases hHB with _ hH,
    exact hH,
  }
end

lemma descend_adj_rhs_prod {V W : Type} {a b : V×W} {G : simple_graph V}
  {H : simple_graph W} (he : a.fst = b.fst) :
  (G□H).adj a b → H.adj a.snd b.snd :=
begin
  intro h,
  cases h with hGB hHB,
  {
    cases hGB with eq hG,
    rw he at hG,
    exfalso,
    apply irrefl,
    exact hG,
  },
  {
    cases hHB with _ hH,
    exact hH,
  }
end

def decend_walk_lhs_prod {V W : Type} (G : simple_graph V) (H : simple_graph W)
  : Π {a b : V×W},
  (G□H).walk a b → (G.walk a.fst b.fst)
| _ _ simple_graph.walk.nil := walk.nil
| a b (@simple_graph.walk.cons fff ggg tttt c oooo h p) := begin
  ---set f:= descend_adj_lhs_prod _ h,
  by_cases he: a.snd = c.snd,
  {
    set f:= descend_adj_lhs_prod he h,
    set wd:= decend_walk_lhs_prod p,
    set w := walk.cons f wd,
    exact w,
  },
  {
    set wd:= decend_walk_lhs_prod p,
    have hw : H.walk a.2 c.2, {
      -- TODO
      rw box_adj_rel_prod at h,
      sorry,
    },
    set w2 := lift_walk_rhs a.1 G H hw,
    --set w := walk.append w2 p,
    --set w := walk.cons p w2
    --set w := walk.cons (descend_adj_lhs h) (decend_walk_lhs p)
    sorry,
  }
end
--walk.cons (descend_adj_lhs h) (decend_walk_lhs p)

-- TODO Pass hypo that there exist a path in G□H
def decend_walk_lhs {V W : Type} {G : simple_graph V} {H : simple_graph W}
  (w : W) (hc : (G□H).is_connected)
  : Π {a b : V},
  (G□H).walk (a, w) (b, w) → (G.walk a b)
| _ _ simple_graph.walk.nil := walk.nil
| a b (@simple_graph.walk.cons _ _ _ c _ h p) :=
begin
  by_cases he: w = c.snd, {
    have heq : (c.fst, w) = c := prod.ext rfl he,
    set cd := (c.fst, w),
    rw ← heq at h,
    rw ← heq at p,
    set f:= descend_adj_lhs w G H h,
    set wd:= decend_walk_lhs p,
    set w := walk.cons f wd,
    exact w,
  }, {
    cases hc with _ hp,
    set x := (a, w),
    specialize hp x c,
    set p2 := hp.some,
    set walk := walk.append p2 p,
    set d := decend_walk_lhs walk,
    exact d,
  }
end

lemma G_and_H_connected_if_G_box_H_connected {V W : Type} (G : simple_graph V)
  (H : simple_graph W) :
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
      sorry,
    },
  }, {
    split, {
      exact hH_not_empty,
    }, {
      -- H has a path for all h₁ h2
      intros h1 h2,
      set g := hG_not_empty.some,
      specialize hGH_has_path (g, h1) (g, h2),
      sorry,
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

def is_box_product {V W : Type} (B : simple_graph (V × W)) (G : simple_graph V) (H : simple_graph W) : Prop :=
  ∀ x y : V×W, B.adj x y ↔ (G.adj x.1 y.1 ∧ x.2=y.2) ∧ B.adj x y ↔ (x.1=y.1 ∧ H.adj x.2 y.2)

lemma box_product_is_box_product {V W : Type} (G : simple_graph V) (H : simple_graph W) :
  is_box_product (G□H) G H :=
begin
  intros x y,
  split,
  {
    rw box_adj_rel_prod,
    intros h,
    cases h with lhs rhs,
    ---apply rhs,
    sorry,
    ---cases h with aaa bbb ccc ddd,
  }, {
    sorry,
  },
end

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

#check walk.cons_append 

variables {u v : V} {w : W}

#check (u, w)

lemma left_induced_box_product {V W : Type} (G : simple_graph V) (H : simple_graph W)
  (B : simple_graph V×W) : Prop := sorry

end box_product
end simple_graph