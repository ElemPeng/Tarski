class Geom where
    Point : Type
    EQ : Point → Point → Point → Point → Prop --- d(a,b) = d(c,d)
    B : Point → Point → Point → Prop --- the middle point is between the outer points, inclusive
    eq_comm {x y : Point} : EQ x y y x -- beeson A1
    eq_id {x y z : Point} : (EQ x y z z) → x = y -- beeson A3
    eq_eucl {x y z u v w : Point} : EQ x y z w → EQ x y u v → EQ z w u v --beeson A2
    btwn_id {x y : Point} : B x y x → x = y -- beeson A6
    /- This is so-called inner pasch: It says, if you have a triangle u y z, with
    x u y exterior to the triangle v on y z, then the line x v crosses side u y at
    some point a -/
    inner_pasch {x y z u v : Point} : B x u z → B y v z → ∃ a, (B u a y ∧ B v a x) --beeson A7

    as_cont {φ ψ : Point → Prop} : -- beeson A11
        (∃ a, ∀ x y, φ x → ψ y → B a x y) → ∃ b, ∀ x y, φ x → ψ y → B x b y
/-
    Let r be a ray with endpoint a. Let the first order formulae φ and ψ define
    subsets X and Y of r, such that every point in Y is to the right of every
    point of X (with respect to a). Then there exists a point b in r lying between
    X and Y. This is essentially the Dedekind cut construction, carried out in a
    way that avoids quantification over sets.

    I probably should replace this with bespoke instances of it so this remains a first-order
    theory but I don't have to decide until chapter 12 anyway.
-/
    lo_dim : ∃ a b c, ¬ B a b c ∧ ¬ B b c a ∧ ¬ B c a b --- forces at least 2 dimensions; beeson A8
    hi_dim {x y z u v : Point} : EQ x u x v → EQ y u y v → EQ z u z v → u ≠ v →
        B x y z ∨ B y z x ∨ B z x y --- forces at most 2 dimensions; beeson A9
    ax_euclid {x y z u v : Point} : B x u v → B y u z → x ≠ u →
        ∃ a b, B x y a ∧ B x z b ∧ B a v b -- beeson A10
/-
    Given any angle and any point v in its interior, there exists a line segment
    including v, with an endpoint on each side of the angle.
-/
    five_sgmt {x y z u x' y' z' u' : Point} : x ≠ y → B x y z → B x' y' z' → EQ x y x' y' →
        EQ y z y' z' → EQ x u x' u' → EQ y u y' u' → EQ z u z' u' --beeson A5
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
    sgmt_const (x y a b : Point) : ∃ z, B x y z ∧ EQ y z a b --beeson A4

-- Satz numbering based on Michael beeson's Tarski Formalization Project
section Congruence

variable (G : Geom)

--Satz 2.1
theorem Geom.eq_refl {x y : G.Point} : EQ x y x y := G.eq_eucl G.eq_comm G.eq_comm

--Satz 2.2
theorem Geom.eq_symm {x y z w : G.Point} : EQ x y z w → EQ z w x y :=
    fun φ ↦ G.eq_eucl φ G.eq_refl

theorem Geom.EQ.symm {x y z w : G.Point} (h : EQ x y z w) : EQ z w x y := G.eq_symm h

--Satz 2.3
theorem Geom.eq_trans {x y z u v w : G.Point} : EQ x y z w → EQ z w u v → EQ x y u v :=
    fun φ ψ ↦ G.eq_eucl (G.eq_symm φ) ψ

--Satz 2.5
theorem Geom.eq_flip_right {x y z w : G.Point} : EQ x y z w → EQ x y w z :=
    fun φ ↦ G.eq_trans φ G.eq_comm

theorem Geom.EQ.r {x y z w : G.Point} (h : EQ x y z w) : EQ x y w z := G.eq_flip_right h

theorem Geom.eq_flip_right_iff {x y z w : G.Point} : EQ x y z w ↔ EQ x y w z := by
    constructor; all_goals exact G.eq_flip_right

--Satz 2.4
theorem Geom.eq_flip_left {x y z w : G.Point} : EQ x y z w → EQ y x z w :=
    fun φ ↦ G.eq_trans G.eq_comm φ

theorem Geom.EQ.l {x y z w : G.Point} (h : EQ x y z w) : EQ y x z w := G.eq_flip_left h

theorem Geom.eq_flip_left_iff {x y z w : G.Point} : EQ x y z w ↔ EQ y x z w := by
    constructor; all_goals exact G.eq_flip_left

--Satz 2.14
theorem Geom.eq_flip_both {x y z w : G.Point} : EQ x y z w → EQ y x w z :=
    fun φ ↦ G.eq_flip_right <| G.eq_flip_left φ

theorem Geom.EQ.lr {x y z w : G.Point} (h : EQ x y z w) : EQ y x w z := h.l.r

theorem Geom.eq_flip_both_iff {x y z w : G.Point} : EQ x y z w ↔ EQ y x w z := by
    constructor; all_goals exact G.eq_flip_both

--- Satz 2.8
theorem Geom.degen_sgmts {x y : G.Point} : EQ x x y y := by
    have ⟨z, hz1, hz2⟩ : ∃ z, B x x z ∧ EQ x z y y := sgmt_const x x y y
    have heq : x = z := eq_id hz2; rwa [←heq] at hz2

--- Satz 2.11
theorem Geom.sgmt_add {x y z x' y' z': G.Point} : B x y z → B x' y' z' →
    EQ x y x' y' → EQ y z y' z' → EQ x z x' z' := by
    intro hb1 hb2 he1 he2; apply G.eq_flip_both; by_cases h : x = y
    ·   subst h; have he1 := he1.symm; have he2 := he2.symm
        have hx'y' : x' = y' := eq_id he1; subst hx'y'; exact (he2.lr.symm)
    apply G.five_sgmt h (hb1) hb2 he1 he2 (G.degen_sgmts) (he1.lr)

--- Satz 2.12
theorem Geom.unique_sgmt_const {q a x b c y : G.Point} :
    q ≠ a → B q a x → EQ a x b c → B q a y → EQ a y b c → x = y := by
        intro hne hb1 he1 hb2 he2
        have h1 : EQ a x a y := G.eq_trans he1 he2.symm
        have h2 : EQ x y y y :=
            G.five_sgmt hne hb1 hb2 G.eq_refl h1 G.eq_refl G.eq_refl
        exact eq_id h2

end Congruence

section Betweenness

variable (G : Geom)

def Geom.Collinear (x y z : G.Point) := B x y z ∨ B y z x ∨ B z x y

-- Satz 3.1
theorem Geom.btwn_refl' {x y : G.Point} : B y x x := by
    have ⟨a, ha, ha'⟩ := G.sgmt_const y x x x
    have hax : x = a := G.eq_id ha'; subst hax; exact ha

-- Satz 3.2
theorem Geom.btwn_symm {x y z : G.Point} : B x y z → B z y x := by
    intro h; have ⟨a, ha, ha'⟩ : ∃ a, B z a x ∧ B y a y := G.inner_pasch G.btwn_refl' h
    have hay : y = a := G.btwn_id ha'; rwa [hay]

theorem Geom.B.symm {x y z : G.Point} (h : B x y z) : B z y x := G.btwn_symm h

theorem Geom.btwn_symm_iff {x y z : G.Point} : B x y z ↔ B z y x := by
    constructor; all_goals exact G.btwn_symm
-- Satz 2.15 : Proven in the book with symmetry but easy with it

theorem Geom.sgmt_add' {x y z x' y' z' : G.Point} :
    B x y z → B x' y' z' → EQ x y y' z' → EQ y z x' y' → EQ x z x' z' := by
    intro hb1 hb2 he1 he2; rw [G.eq_flip_right_iff] at he1 he2 ⊢
    exact G.sgmt_add hb1 hb2.symm he1 he2

-- Satz 3.3
theorem Geom.btwn_refl {x y : G.Point} : B x x y := G.btwn_symm G.btwn_refl'

-- Satz 3.4
theorem Geom.eq_of_xyz_yxz {x y z : G.Point} : B x y z → B y x z → x = y := by
    intro hb1 hb2; have ⟨a, ha1, ha2⟩ := G.inner_pasch hb1 hb2
    exact (G.btwn_id ha1) ▸ (G.btwn_id ha2)

-- Satz 3.5a
theorem Geom.btwn_xyz_of_xyw_yzw {x y z w : G.Point} : B x y w → B y z w → B x y z := by
    intro hb1 hb2; have ⟨a, ha1, ha2⟩ := G.inner_pasch hb1 hb2
    rw [G.btwn_id ha1]; apply G.btwn_symm ha2

-- Satz 3.6a
theorem Geom.btwn_yzw_of_xyz_xzw {x y z w : G.Point} : B x y z → B x z w → B y z w := by
    intro hb1 hb2; rw [G.btwn_symm_iff] at hb1 hb2 ⊢
    exact G.btwn_xyz_of_xyw_yzw hb2 hb1

-- Satz 3.7a
theorem Geom.btwn_xzw_of_xyz_yzw_ne {x y z w} : B x y z → B y z w → y ≠ z → B x z w := by
    intro hb1 hb2 heq; have ⟨a, ha1, ha2⟩ : ∃ a, B x z a ∧ EQ z a z w := sgmt_const x z z w
    have hb3 : B y z a := btwn_yzw_of_xyz_xzw G hb1 ha1
    have he1 : EQ w a a a := G.five_sgmt heq hb2 hb3 (G.eq_refl) (ha2).symm (G.eq_refl) (G.eq_refl)
    exact (G.eq_id he1) ▸ ha1


-- Satz 3.13abc, essentially.
/-  In Beeson's work, the a b c in lo_dim are constants that
    just exist as part of the Skolemization; these three results show that a b and c are distinct.
    We show the more general result that if y is not on the interval xz, then y is not
    equal to either x nor z -/
theorem Geom.dist_of_not_btwn {x y z : G.Point} : ¬ B x y z → x ≠ y ∧ y ≠ z := by
    intro h; refine ⟨?_, ?_⟩
    · intro h'; subst h'; exact h G.btwn_refl
    · intro h'; subst h'; exact h G.btwn_refl'
end Betweenness
