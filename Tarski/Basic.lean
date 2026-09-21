class Geom where
    Point : Type
    EQ : Point → Point → Point → Point → Prop --- d(a,b) = d(c,d)
    B : Point → Point → Point → Prop --- the middle point is between the outer points, inclusive
    eq_comm {x y : Point} : EQ x y y x
    eq_id {x y z : Point} : (EQ x y z z) → x = y
    eq_eucl {x y z u v w : Point} : EQ x y z w → EQ x y u v → EQ z w u v
    btwn_id {x y : Point} : B x y x → x = y
    /- This is so-called inner inner_pasch: It says, if you have a triangle u y z, with
    x u y exterior to the triangle v on y z, then the line x v crosses side u y at
    some point a -/
    inner_pasch {x y z u v : Point} : B x u z → B y v z → ∃ a, (B u a y ∧ B v a x)
    as_cont {φ ψ : Point → Prop} :
        (∃ a, ∀ x y, φ x → ψ y → B a x y) → ∃ b, ∀ x y, φ x → ψ y → B x b y
/-
    Let r be a ray with endpoint a. Let the first order formulae φ and ψ define
    subsets X and Y of r, such that every point in Y is to the right of every
    point of X (with respect to a). Then there exists a point b in r lying between
    X and Y. This is essentially the Dedekind cut construction, carried out in a
    way that avoids quantification over sets.
-/
    lo_dim : ∃ a b c, ¬ B a b c ∧ ¬ B b c a ∧ ¬ B c a b --- forces at least 2 dimensions
    hi_dim {x y z u v : Point} : EQ x u x v → EQ y u y v → EQ z u z v → u ≠ v →
        B x y z ∨ B y z x ∨ B z x y --- forces at most 2 dimensions
    ax_euclid {x y z u v : Point} : B x u v → B y u z → x ≠ u → ∃ a b, B x y a ∧ B x z b ∧ B a v b
/-
    Given any angle and any point v in its interior, there exists a line segment
    including v, with an endpoint on each side of the angle.
-/
    five_sgmt {x y z u x' y' z' u' : Point} : x ≠ y → B x y z → B x' y' z' → EQ x y x' y' →
        EQ y z y' z' → EQ x u x' u' → EQ y u y' u' → EQ z u z' u'
/-
    Begin with two triangles, xuz and x'u'z'. Draw the line segments yu and y'u', connecting a
    vertex of each triangle to a point on the side opposite to the vertex. The result is two
    divided triangles, each made up of five segments. If four segments of one triangle are each
    congruent to a segment in the other triangle, then the fifth segments in both triangles must
    be congruent.

    This is equivalent to the side-angle-side rule for determining that two triangles are congruent;
    if the angles uxz and u'x'z' are congruent (there exist congruent triangles xuz and x'u'z'),
    and the two pairs of incident sides are congruent (xu ≡ x'u' and xz ≡ x'z'), then the remaining
    pair of sides is also congruent (uz ≡ u'z').
-/
    sgmt_const (x y a b : Point) : ∃ z, B x y z ∧ EQ y z a b


section Congruence

variable (G : Geom)

theorem Geom.eq_refl {x y : G.Point} : EQ x y x y := G.eq_eucl G.eq_comm G.eq_comm

theorem Geom.eq_symm {x y z w : G.Point} : EQ x y z w → EQ z w x y :=
    fun φ ↦ G.eq_eucl φ G.eq_refl

theorem Geom.EQ.symm {x y z w : G.Point} (h : EQ x y z w) : EQ z w x y := G.eq_symm h

theorem Geom.eq_trans {x y z u v w : G.Point} : EQ x y z w → EQ z w u v → EQ x y u v :=
    fun φ ψ ↦ G.eq_eucl (G.eq_symm φ) ψ

theorem Geom.eq_flip_right {x y z w : G.Point} : EQ x y z w → EQ x y w z :=
    fun φ ↦ G.eq_trans φ G.eq_comm

theorem Geom.eq_flip_left {x y z w : G.Point} : EQ x y z w → EQ y x z w :=
    fun φ ↦ G.eq_trans G.eq_comm φ

theorem Geom.eq_flip_both {x y z w : G.Point} : EQ x y z w → EQ y x w z :=
    fun φ ↦ G.eq_flip_right <| G.eq_flip_left φ

--- from reading Michael Besson's proof of this
theorem Geom.degen_sgmts {x y : G.Point} : EQ x x y y := by
    have ⟨z, hz1, hz2⟩ : ∃ z, B x x z ∧ EQ x z y y := sgmt_const x x y y
    have heq : x = z := eq_id hz2; rwa [←heq] at hz2

theorem Geom.sgmt_add {x y z x' y' z': G.Point} : B x y z → B x' y' z' →
    EQ x y x' y' → EQ y z y' z' → EQ x z x' z' := by
    intro hb1 hb2 he1 he2; apply G.eq_flip_both; by_cases h : x = y
    ·   subst h; have he1 := he1.symm; have he2 := he2.symm
        have hx'y' : x' = y' := eq_id he1; subst hx'y'; exact (G.eq_flip_both he2.symm)
    apply G.five_sgmt h (hb1) hb2 he1 he2 (G.degen_sgmts) (G.eq_flip_both he1)

theorem Geom.unique_sgmt_const {q a x b c y : G.Point} :
    q ≠ a → B q a x → EQ a x b c → B q a y → EQ a y b c → x = y := by
        intro hne hb1 he1 hb2 he2; sorry --- look at Besson; uses five_sgmt

end Congruence

section Betweenness

variable (G : Geom)

def Geom.Collinear (x y z : G.Point) := B x y z ∨ B y z x ∨ B z x y

theorem Geom.btwn_triv (x : G.Point) : B x x x := by
    have ⟨a, ha, ha'⟩ := sgmt_const x x x x
    rwa [G.eq_id ha'] at ha ⊢

theorem Geom.btwn_refl' {x y : G.Point} : B y x x := by
    have ⟨a, ha, ha'⟩ := G.sgmt_const y x x x
    have hax : x = a := G.eq_id ha'; subst hax; exact ha

theorem Geom.btwn_symm {x y z : G.Point} : B x y z → B z y x := by
    intro h; have ⟨a, ha, ha'⟩ : ∃ a, B z a x ∧ B y a y := G.inner_pasch G.btwn_refl' h
    have hay : y = a := G.btwn_id ha'; rwa [hay]

theorem Geom.btwn_refl {x y : G.Point} : B x x y := G.btwn_symm G.btwn_refl'

theorem Geom.btwn_trans {x y z w : G.Point} : B x y w → B y z w → B x y z := by
    intro h1 h2; have ⟨a, ha, ha'⟩ := G.inner_pasch h1 h2
    rw [G.btwn_id ha]; apply G.btwn_symm ha'

theorem Geom.B.symm {x y z : G.Point} (h : B x y z) : B z y x := G.btwn_symm h

theorem Geom.dist_of_not_btwn {x y z : G.Point} : ¬ B x y z → x ≠ y ∧ y ≠ z := by
    intro h; refine ⟨?_, ?_⟩ <;> intro h' <;> subst h'
    · exact h G.btwn_refl
    · exact h G.btwn_refl'

theorem Geom.three_dist_pts : ∃ a b c : Point, a ≠ b ∧ a ≠ c ∧ b ≠ c := by
    have ⟨a, b, c, h1, h2, _⟩ := G.lo_dim
    refine ⟨a, b, c, ?_, ?_, ?_⟩
    · exact (G.dist_of_not_btwn h1).1
    · exact (G.dist_of_not_btwn h2).2.symm
    · exact (G.dist_of_not_btwn h1).2

theorem Geom.another_pt {x : G.Point} : ∃ y, x ≠ y := by
    have ⟨a, b, _, h1, _⟩ := G.lo_dim; by_cases h : x = a
    · subst h; have ⟨h',_⟩ := G.dist_of_not_btwn h1; exact ⟨b, h'⟩
    · exact ⟨a, h⟩

theorem Geom.outer_pasch {x y z u v} : B x u z → B y z v → ∃ a, (B y u a ∧ B x a v) := by
    sorry --- This can be proven from inner Pasch somehow? (Gupta)

theorem Geom.ext_pt {x y : G.Point} : x ≠ y → ∃ u, ¬G.Collinear x y u := by
    intro hxy; have ⟨a, b, c, h1, h2, h3⟩ := G.lo_dim
    sorry
/-
    some sort of plane separation?
-/
theorem Geom.plane_sep {x y : G.Point} : x ≠ y → ∃ u v, ¬ G.Collinear x y u ∧ ¬ G.Collinear x y v ∧
    ∃ a, G.Collinear x y a ∧ B u a v := by sorry

theorem Geom.hi_dim_conv {x y z : G.Point} : B x y z → ∃ u v,
u ≠ v ∧ EQ x u x v ∧ EQ y u y v ∧ EQ z u z v := by
    sorry

/-
    I need something like EQ x u x v → EQ z u z v → B x y z → EQ y u y v
-/

theorem Geom.btwn_connect {x y z w : G.Point} : B x y w → B x z w → (B x y z ∨ B x z y) := by
    intro h1 h2; sorry

end Betweenness

/-
    TO DO:
    Define lines as equivalence classes of { ⟨a, b⟩ : Point × Point // a ≠ b }

    ⟨a, b⟩ ≃ ⟨c, d⟩ if a b and c are collinear and a b and d are collinear
    Collinear a b c : (assuming a ≠ b) B a b c ∨ B a c b ∨ B b a c
-/
