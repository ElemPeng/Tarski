class Geom where
    Point : Type
    E : Point → Point → Point → Point → Prop --- d(a,b) = d(c,d)
    B : Point → Point → Point → Prop --- the middle point is between the outer points, inclusive
    E_comm {x y : Point} : E x y y x -- beeson A1
    E_id {x y z : Point} : (E x y z z) → x = y -- beeson A3
    E_eucl {x y z u v w : Point} : E x y z w → E x y u v → E z w u v --beeson A2
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
    hi_dim {x y z u v : Point} : E x u x v → E y u y v → E z u z v → u ≠ v →
        B x y z ∨ B y z x ∨ B z x y --- forces at most 2 dimensions; beeson A9
    ax_euclid {x y z u v : Point} : B x u v → B y u z → x ≠ u →
        ∃ a b, B x y a ∧ B x z b ∧ B a v b -- beeson A10
/-
    Given any angle and any point v in its interior, there exists a line segment
    including v, with an endpoint on each side of the angle.
-/
    five_sgmt {x y z u x' y' z' u' : Point} : x ≠ y → B x y z → B x' y' z' → E x y x' y' →
        E y z y' z' → E x u x' u' → E y u y' u' → E z u z' u' --beeson A5
/-
    Begin with two triangles, xuz and x'u'z'. Draw the line segments yu and y'u', connecting a
    vertex of each triangle to a point on the side opposite to the vertex. The result is two
    divided triangles, each made up of five segments. If four segments of one triangle are each
    congruent to a segment in the other triangle, then the fifth segments in both triangles must
    be congruent.

    This is Euivalent to the side-angle-side rule for determining that two triangles are congruent;
    if the angles uxz and u'x'z' are congruent (there exist congruent triangles xuz and x'u'z'),
    and the two pairs of incident sides are congruent (xu ≡ x'u' and xz ≡ x'z'), then the remaining
    pair of sides is also congruent (uz ≡ u'z').
-/
    sgmt_const (x y a b : Point) : ∃ z, B x y z ∧ E y z a b --beeson A4

-- Satz numbering based on Michael beeson's Tarski Formalization Project
section Congruence

variable (G : Geom)

--Satz 2.1
theorem Geom.E_refl {x y : G.Point} : E x y x y := G.E_eucl G.E_comm G.E_comm

--Satz 2.2
theorem Geom.E_symm {x y z w : G.Point} : E x y z w → E z w x y :=
    fun φ ↦ G.E_eucl φ G.E_refl

theorem Geom.E.symm {x y z w : G.Point} (h : E x y z w) : E z w x y := G.E_symm h

--Satz 2.3
theorem Geom.E_trans {x y z u v w : G.Point} : E x y z w → E z w u v → E x y u v :=
    fun φ ψ ↦ G.E_eucl (G.E_symm φ) ψ

--Satz 2.5
theorem Geom.E_flip_right {x y z w : G.Point} : E x y z w → E x y w z :=
    fun φ ↦ G.E_trans φ G.E_comm

theorem Geom.E.r {x y z w : G.Point} (h : E x y z w) : E x y w z := G.E_flip_right h

theorem Geom.E_flip_right_iff {x y z w : G.Point} : E x y z w ↔ E x y w z := by
    constructor; all_goals exact G.E_flip_right

--Satz 2.4
theorem Geom.E_flip_left {x y z w : G.Point} : E x y z w → E y x z w :=
    fun φ ↦ G.E_trans G.E_comm φ

theorem Geom.E.l {x y z w : G.Point} (h : E x y z w) : E y x z w := G.E_flip_left h

theorem Geom.E_flip_left_iff {x y z w : G.Point} : E x y z w ↔ E y x z w := by
    constructor; all_goals exact G.E_flip_left

--Satz 2.14
theorem Geom.E_flip_both {x y z w : G.Point} : E x y z w → E y x w z :=
    fun φ ↦ G.E_flip_right <| G.E_flip_left φ

theorem Geom.E.lr {x y z w : G.Point} (h : E x y z w) : E y x w z := h.l.r

theorem Geom.E_flip_both_iff {x y z w : G.Point} : E x y z w ↔ E y x w z := by
    constructor; all_goals exact G.E_flip_both

--- Satz 2.8
theorem Geom.degen_sgmts {x y : G.Point} : E x x y y := by
    have ⟨z, hz1, hz2⟩ : ∃ z, B x x z ∧ E x z y y := sgmt_const x x y y
    have hE : x = z := E_id hz2; rwa [←hE] at hz2

--- Satz 2.11
theorem Geom.sgmt_add {x y z x' y' z': G.Point} : B x y z → B x' y' z' →
    E x y x' y' → E y z y' z' → E x z x' z' := by
    intro hb1 hb2 he1 he2; apply G.E_flip_both; by_cases h : x = y
    ·   subst h; have he1 := he1.symm; have he2 := he2.symm
        have hx'y' : x' = y' := E_id he1; subst hx'y'; exact (he2.lr.symm)
    apply G.five_sgmt h (hb1) hb2 he1 he2 (G.degen_sgmts) (he1.lr)

--- Satz 2.12
theorem Geom.unique_sgmt_const {q a x b c y : G.Point} :
    q ≠ a → B q a x → E a x b c → B q a y → E a y b c → x = y := by
        intro hne hb1 he1 hb2 he2
        have h1 : E a x a y := G.E_trans he1 he2.symm
        have h2 : E x y y y :=
            G.five_sgmt hne hb1 hb2 G.E_refl h1 G.E_refl G.E_refl
        exact E_id h2

end Congruence

section Betweenness

variable (G : Geom)

def Geom.Collinear (x y z : G.Point) := B x y z ∨ B y z x ∨ B z x y

-- Satz 3.1
theorem Geom.btwn_refl' {x y : G.Point} : B y x x := by
    have ⟨a, ha, ha'⟩ := G.sgmt_const y x x x
    have hax : x = a := G.E_id ha'; subst hax; exact ha

-- Satz 3.2
theorem Geom.btwn_symm {x y z : G.Point} : B x y z → B z y x := by
    intro h; have ⟨a, ha, ha'⟩ : ∃ a, B z a x ∧ B y a y := G.inner_pasch G.btwn_refl' h
    have hay : y = a := G.btwn_id ha'; rwa [hay]

theorem Geom.B.symm {x y z : G.Point} (h : B x y z) : B z y x := G.btwn_symm h

theorem Geom.btwn_symm_iff {x y z : G.Point} : B x y z ↔ B z y x := by
    constructor; all_goals exact G.btwn_symm

-- Satz 2.15 : Proven in the book without symmetry but much easier with it

theorem Geom.sgmt_add' {x y z x' y' z' : G.Point} :
    B x y z → B x' y' z' → E x y y' z' → E y z x' y' → E x z x' z' := by
    intro hb1 hb2 he1 he2; rw [G.E_flip_right_iff] at he1 he2 ⊢
    exact G.sgmt_add hb1 hb2.symm he1 he2

-- Satz 3.3
theorem Geom.btwn_refl {x y : G.Point} : B x x y := G.btwn_symm G.btwn_refl'

-- Satz 3.4
theorem Geom.E_of_xyz_yxz {x y z : G.Point} : B x y z → B y x z → x = y := by
    intro hb1 hb2; have ⟨a, ha1, ha2⟩ := G.inner_pasch hb1 hb2
    exact (G.btwn_id ha1) ▸ (G.btwn_id ha2)

-- Satz 3.5a
theorem Geom.btwn_xyz_of_xyw_yzw {x y z w : G.Point} : B x y w → B y z w → B x y z := by
    intro hb1 hb2; have ⟨a, ha1, ha2⟩ := G.inner_pasch hb1 hb2
    rw [G.btwn_id ha1]; apply G.btwn_symm ha2

-- Satz 3.6a
theorem Geom.btwn_yzw_of_xyz_xzw {x y z w : G.Point} : B x y z → B x z w → B y z w :=
    fun hb1 hb2 ↦ (G.btwn_xyz_of_xyw_yzw hb2.symm hb1.symm).symm

-- Satz 3.7a
theorem Geom.btwn_xzw_of_xyz_yzw_ne {x y z w} : B x y z → B y z w → y ≠ z → B x z w := by
    intro hb1 hb2 hne; have ⟨a, ha1, ha2⟩ : ∃ a, B x z a ∧ E z a z w := sgmt_const x z z w
    have hb3 : B y z a := btwn_yzw_of_xyz_xzw G hb1 ha1
    have he1 : E w a a a := G.five_sgmt hne hb2 hb3 (G.E_refl) (ha2).symm (G.E_refl) (G.E_refl)
    exact (G.E_id he1) ▸ ha1

-- Satz 3.5b
theorem Geom.btwn_xzw_of_xyw_yzw {x y z w : G.Point} : B x y w → B y z w → B x z w := by
    intro hb1 hb2; have h := G.btwn_xyz_of_xyw_yzw hb1 hb2
    by_cases h' : y = z
    · exact h' ▸ hb1
    · exact G.btwn_xzw_of_xyz_yzw_ne h hb2 h'

-- Satz 3.6b
theorem Geom.btwn_xyw_of_xyz_xzw {x y z w : G.Point} : B x y z → B x z w → B x y w :=
    fun hb1 hb2 ↦ (G.btwn_xzw_of_xyw_yzw hb2.symm hb1.symm).symm

-- Satz 3.7b
theorem Geom.btwn_xyw_of_xyz_yzw_ne {x y z w} : B x y z → B y z w → y ≠ z → B x y w := by
    intro hb1 hb2 hne; have hb3 : B x z w := G.btwn_xzw_of_xyz_yzw_ne hb1 hb2 hne
    exact G.btwn_xyw_of_xyz_xzw hb1 hb3

-- Satz 3.13abc, essentially.
/-  In Beeson's work, the a b c in lo_dim are constants that
    just exist as part of the Skolemization; these three results show that a b and c are distinct.
    We show the more general result that if y is not on the interval xz, then y is not
    Eual to either x nor z , and that this implies the existence of two and three distinct points-/
theorem Geom.dist_of_not_btwn {x y z : G.Point} : ¬ B x y z → x ≠ y ∧ y ≠ z := by
    intro h; refine ⟨?_, ?_⟩
    · intro h'; subst h'; exact h G.btwn_refl
    · intro h'; subst h'; exact h G.btwn_refl'

theorem Geom.three_dist : ∃ a b c : G.Point, a ≠ b ∧ b ≠ c ∧ a ≠ c := by
    have ⟨a, b, c, h1, h2, _⟩ := G.lo_dim; refine ⟨a, b, c, ?_, ?_, ?_⟩
    · exact (G.dist_of_not_btwn h1).1
    · exact (G.dist_of_not_btwn h1).2
    · exact (G.dist_of_not_btwn h2).2.symm

theorem Geom.two_dist : ∃ a b : G.Point, a ≠ b := by
    have ⟨a, b, _, h, _⟩ := G.three_dist; exact ⟨a, b, h⟩

-- Satz 3.14ab, essentially
/-  Beeson defines three specific α β γ that are not collinear; then shows that they are unEual
    These results shows that if you use segment construction to construct a segment from y on the
    opposite side of x so that ya ≡ αβ, then B x y a and y ≠ a; The first result is obvious from
    the definition of sgmt_const so I'm skipping it; the only content here for us is that if
    a ≠ b and E x y a b, then x ≠ y. -/

theorem Geom.E_id_mt {x y a b : G.Point} : a ≠ b → E x y a b → x ≠ y :=
    fun hE1 he1 hE2 ↦ hE1 (G.E_id (hE2 ▸ he1.symm))

-- Satz 3.17
/-  Suppose you have a triangle A B C, with points X on AB, Y on BC, and Z on AC. Then the line
    segments ZB and XY intersect at some point P; basically the converse of ax_euclid
    update : I'm an idiot, this is the crossbar theorem -/
theorem Geom.crossbar {a b c x y z : G.Point} :
    B a x b → B c y b → B a z c → (∃ p, B z p b ∧ B x p y) := by
    intro hb1 hb2 hb3; have ⟨e, hb4, hb5⟩ := G.inner_pasch hb2.symm hb3
    have ⟨p, hb6, hb7⟩ := inner_pasch hb1.symm hb4
    refine ⟨p, ?_, hb6⟩; apply G.btwn_xzw_of_xyw_yzw hb5 hb7

end Betweenness

section Ch4

/-
    Notes about Chapter 4: There is a function called insert: What it is doing is
    given a ray a'c', constructing a point b' on it so that ab ≡ a'b'.
    further (a, b, c) ≃ (a', b', c') or E3 (a, b, c, a', b', c') is shorthand for
    ab ≡ a'b' ∧ bc ≡ b'c' ∧ ac ≡ a'c'.

    AFS is shorthand for "the premises of the five segment axiom"
    IFS is shorthand for "the premises of the inner five segment theorem (Satz 4.1)"

-/

-- this is definition 4.3 in Beeson (basically side side side premises?)
def E3 {G : Geom} {x y z a b c : G.Point} := G.E x y a b ∧ G.E y z b c ∧ G.E x z a c

-- this is definition 4.10 in Beeson
def Col {G : Geom} {x y z : G.Point} := G.B x y z ∨ G.B y z x ∨ G.B z x y

end Ch4
