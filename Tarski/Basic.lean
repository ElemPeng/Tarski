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

    This is equivalent to the side-angle-side rule for determining that two triangles are congruent;
    if the angles uxz and u'x'z' are congruent (there exist congruent triangles xuz and x'u'z'),
    and the two pairs of incident sides are congruent (xu ≡ x'u' and xz ≡ x'z'), then the remaining
    pair of sides is also congruent (uz ≡ u'z').
-/
    sgmt_const (x y a b : Point) : ∃ z, B x y z ∧ E y z a b --beeson A4

-- Satz numbering based on Michael Beeson's Tarski Formalization Project
section Congruence

namespace Geom
--Satz 2.1
theorem E_refl {G : Geom} {x y : Point} : E x y x y := E_eucl E_comm E_comm

--Satz 2.2
theorem E.symm {G : Geom} {x y z w : Point} (h : E x y z w) : E z w x y :=
    E_eucl h E_refl

theorem E_symm_iff {G : Geom} {x y z w : Point} : E x y z w ↔ E z w x y := by
    constructor; all_goals exact fun x ↦ x.symm
--Satz 2.3
theorem E_trans {G : Geom} {x y z u v w : Point} : E x y z w → E z w u v → E x y u v :=
    fun φ ψ ↦ E_eucl (φ.symm) ψ

--Satz 2.5
theorem E_flip_right {G : Geom} {x y z w : Point} : E x y z w → E x y w z :=
    fun φ ↦ E_trans φ E_comm

theorem E.r {G : Geom} {x y z w : Point} (h : E x y z w) : E x y w z := E_flip_right h

theorem E_flip_right_iff {G : Geom} {x y z w : Point} : E x y z w ↔ E x y w z := by
    constructor; all_goals exact E_flip_right

--Satz 2.4
theorem E_flip_left {G : Geom} {x y z w : Point} : E x y z w → E y x z w :=
    fun φ ↦ E_trans E_comm φ

theorem E.l {G : Geom} {x y z w : Point} (h : E x y z w) : E y x z w := E_flip_left h

theorem E_flip_left_iff {G : Geom} {x y z w : Point} : E x y z w ↔ E y x z w := by
    constructor; all_goals exact E_flip_left

--Satz 2.14
theorem E_flip_both {G : Geom} {x y z w : Point} : E x y z w → E y x w z :=
    fun φ ↦ E_flip_right <| E_flip_left φ

theorem E.lr {G : Geom} {x y z w : Point} (h : E x y z w) : E y x w z := h.l.r

theorem E_flip_both_iff {G : Geom} {x y z w : Point} : E x y z w ↔ E y x w z := by
    constructor; all_goals exact E_flip_both

--- Satz 2.8
theorem degen_sgmts {G : Geom} {x y : Point} : E x x y y := by
    have ⟨z, hz1, hz2⟩ : ∃ z, B x x z ∧ E x z y y := sgmt_const x x y y
    have hE : x = z := E_id hz2; rwa [←hE] at hz2

--- Satz 2.11
theorem sgmt_add {G : Geom} {x y z x' y' z' : Point} : B x y z → B x' y' z' →
    E x y x' y' → E y z y' z' → E x z x' z' := by
    intro hb1 hb2 he1 he2; apply E_flip_both; by_cases h : x = y
    ·   subst h; have he1 := he1.symm; have he2 := he2.symm
        have hx'y' : x' = y' := E_id he1; subst hx'y'; exact (he2.lr.symm)
    apply five_sgmt h (hb1) hb2 he1 he2 (degen_sgmts) (he1.lr)

--- Satz 2.12
theorem unique_sgmt_const {G : Geom} {q a x b c y : Point} :
    q ≠ a → B q a x → E a x b c → B q a y → E a y b c → x = y := by
        intro hne hb1 he1 hb2 he2
        have h1 : E a x a y := E_trans he1 he2.symm
        have h2 : E x y y y :=
            five_sgmt hne hb1 hb2 E_refl h1 E_refl E_refl
        exact E_id h2
end Geom
end Congruence

section Betweenness
namespace Geom
-- Satz 3.1
theorem btwn_refl' {G : Geom} {x y : Point} : B y x x := by
    have ⟨a, ha, ha'⟩ := sgmt_const y x x x
    have hax : x = a := E_id ha'; subst hax; exact ha

-- Satz 3.2
theorem btwn_symm {G : Geom} {x y z : Point} : B x y z → B z y x := by
    intro h; have ⟨a, ha, ha'⟩ : ∃ a, B z a x ∧ B y a y := inner_pasch btwn_refl' h
    have hay : y = a := btwn_id ha'; rwa [hay]

theorem B.symm {G : Geom}  {x y z : Point} (h : B x y z) : B z y x := btwn_symm h

theorem btwn_symm_iff {G : Geom} {x y z : Point} : B x y z ↔ B z y x := by
    constructor; all_goals exact btwn_symm

-- Satz 2.15 : Proven in the book without symmetry but much easier with it

theorem sgmt_add' {G : Geom} {x y z x' y' z' : Point} :
    B x y z → B x' y' z' → E x y y' z' → E y z x' y' → E x z x' z' := by
    intro hb1 hb2 he1 he2; rw [E_flip_right_iff] at he1 he2 ⊢
    exact sgmt_add hb1 hb2.symm he1 he2

-- Satz 3.3
theorem btwn_refl {G : Geom} {x y : Point} : B x x y := btwn_symm btwn_refl'

-- Satz 3.4
theorem E_of_xyz_yxz {G : Geom} {x y z : Point} : B x y z → B y x z → x = y := by
    intro hb1 hb2; have ⟨a, ha1, ha2⟩ := inner_pasch hb1 hb2
    exact (btwn_id ha1) ▸ (btwn_id ha2)

-- Satz 3.5a
theorem btwn_xyz_of_xyw_yzw {G : Geom} {x y z w : Point} : B x y w → B y z w → B x y z := by
    intro hb1 hb2; have ⟨a, ha1, ha2⟩ := inner_pasch hb1 hb2
    rw [btwn_id ha1]; apply btwn_symm ha2

-- Satz 3.6a
theorem btwn_yzw_of_xyz_xzw {G : Geom} {x y z w : Point} : B x y z → B x z w → B y z w :=
    fun hb1 hb2 ↦ (btwn_xyz_of_xyw_yzw hb2.symm hb1.symm).symm

-- Satz 3.7a
theorem btwn_xzw_of_xyz_yzw_ne {G : Geom} {x y z w} : B x y z → B y z w → y ≠ z → B x z w := by
    intro hb1 hb2 hne; have ⟨a, ha1, ha2⟩ : ∃ a, B x z a ∧ E z a z w := sgmt_const x z z w
    have hb3 : B y z a := btwn_yzw_of_xyz_xzw hb1 ha1
    have he1 : E w a a a := five_sgmt hne hb2 hb3 (E_refl) (ha2).symm (E_refl) (E_refl)
    exact (E_id he1) ▸ ha1

-- Satz 3.5b
theorem btwn_xzw_of_xyw_yzw {G : Geom} {x y z w : Point} : B x y w → B y z w → B x z w := by
    intro hb1 hb2; have h := btwn_xyz_of_xyw_yzw hb1 hb2
    by_cases h' : y = z
    · exact h' ▸ hb1
    · exact btwn_xzw_of_xyz_yzw_ne h hb2 h'

-- Satz 3.6b
theorem btwn_xyw_of_xyz_xzw {G : Geom} {x y z w : Point} : B x y z → B x z w → B x y w :=
    fun hb1 hb2 ↦ (btwn_xzw_of_xyw_yzw hb2.symm hb1.symm).symm

-- Satz 3.7b
theorem btwn_xyw_of_xyz_yzw_ne {G : Geom} {x y z w} : B x y z → B y z w → y ≠ z → B x y w := by
    intro hb1 hb2 hne; have hb3 : B x z w := btwn_xzw_of_xyz_yzw_ne hb1 hb2 hne
    exact btwn_xyw_of_xyz_xzw hb1 hb3

-- Satz 3.13abc, essentially.
/-  In Beeson's work, the a b c in lo_dim are constants that
    just exist as part of the Skolemization; these three results show that a b and c are distinct.
    We show the more general result that if y is not on the interval xz, then y is not
    Eual to either x nor z , and that this implies the existence of two and three distinct points-/
theorem dist_of_not_btwn {G : Geom} {x y z : Point} : ¬ B x y z → x ≠ y ∧ y ≠ z := by
    intro h; refine ⟨?_, ?_⟩
    · intro h'; subst h'; exact h btwn_refl
    · intro h'; subst h'; exact h btwn_refl'

theorem three_dist (G : Geom) : ∃ a b c : Point, a ≠ b ∧ b ≠ c ∧ a ≠ c := by
    have ⟨a, b, c, h1, h2, _⟩ := lo_dim; refine ⟨a, b, c, ?_, ?_, ?_⟩
    · exact (dist_of_not_btwn h1).1
    · exact (dist_of_not_btwn h1).2
    · exact (dist_of_not_btwn h2).2.symm

theorem two_dist (G : Geom) : ∃ a b : Point, a ≠ b := by
    have ⟨a, b, _, h, _⟩ := G.three_dist; exact ⟨a, b, h⟩

-- Satz 3.14ab, essentially
/-  Beeson defines three specific α β γ that are not collinear; then shows that they are unEual
    These results shows that if you use segment construction to construct a segment from y on the
    opposite side of x so that ya ≡ αβ, then B x y a and y ≠ a; The first result is obvious from
    the definition of sgmt_const so I'm skipping it; the only content here for us is that if
    a ≠ b and E x y a b, then x ≠ y. -/

theorem E_id_mt {G : Geom} {x y a b : Point} : a ≠ b → E x y a b → x ≠ y :=
    fun hE1 he1 hE2 ↦ hE1 (E_id (hE2 ▸ he1.symm))

theorem sgmt_const' {G : Geom} (x y : Point) : ∃ z, B x y z ∧ y ≠ z := by
    have ⟨a, b, hab⟩ := G.two_dist;
    have ⟨z, h1, h2⟩ := sgmt_const x y a b
    exact ⟨z, h1, E_id_mt hab h2⟩

-- Satz 3.17
/-  Suppose you have a triangle A B C, with points X on AB, Y on BC, and Z on AC. Then the line
    segments ZB and XY intersect at some point P; basically the converse of ax_euclid
    update : I'm an idiot, this is the crossbar theorem -/
theorem crossbar {G : Geom} {a b c x y z : Point} :
    B a x b → B c y b → B a z c → (∃ p, B z p b ∧ B x p y) := by
    intro hb1 hb2 hb3; have ⟨e, hb4, hb5⟩ := inner_pasch hb2.symm hb3
    have ⟨p, hb6, hb7⟩ := inner_pasch hb1.symm hb4
    refine ⟨p, ?_, hb6⟩; apply btwn_xzw_of_xyw_yzw hb5 hb7

end Geom
end Betweenness

section Ch4

namespace Geom
/-
    Notes about Chapter 4: There is a function called insert: What it is doing is
    given a ray a'c', constructing a point b' on it so that ab ≡ a'b'.
    further (a, b, c) ≃ (a', b', c') or E3 (a, b, c, a', b', c') is shorthand for
    ab ≡ a'b' ∧ bc ≡ b'c' ∧ ac ≡ a'c'.

    AFS is shorthand for "the premises of the five segment axiom"
    IFS is shorthand for "the premises of the inner five segment theorem (Satz 4.1)"

-/

-- Satz 4.2; this is basically SSS to five_sgmt's SAS
/- This is actually very clever so I feel the need to explain it: The way it works is
we know xz = x'z', xu=x'u' and zu = z'u' so we construct w and w' so that B xzw and
B x'z'w', use five_sgmt to get wu = w'u', and then use it again backwards on the
triangles w y u and w' y' u' to get yu = y'u'.-/
theorem inner_five_sgmt {G : Geom} {x y z u x' y' z' u' : Point} : B x y z → B x' y' z' →
    E x y x' y' → E y z y' z' → E x u x' u' → E z u z' u' → E y u y' u' := by
    intro hb1 hb'1 he1 he2 he3 he4
    by_cases heq : x = z
    ·   subst heq; rw [btwn_id hb1] at he1 he3; rwa [E_id he1.symm] at he3
    have ⟨w, hw1, heq2⟩ := sgmt_const' x z
    have ⟨w', hw'1, he6⟩ := sgmt_const x' z' z w
    have he5 : E x z x' z' := sgmt_add hb1 hb'1 he1 he2
    have he7 : E w u w' u' := five_sgmt heq hw1 hw'1 he5 he6.symm he3 he4
    have hb2 : B w z y := (btwn_yzw_of_xyz_xzw hb1 hw1).symm
    have hb'2 : B w' z' y' := (btwn_yzw_of_xyz_xzw hb'1 hw'1).symm
    apply five_sgmt heq2.symm hb2 hb'2 he6.lr.symm he2.lr he7 he4

-- Satz 4.3: segment subtraction
/-  Same trick as above; if y = z we're done, so assume y ≠ z and extend ray yz
    and ray y'z' to w and w', then use five_sgmt with w z y x and w' z' y' x' -/

theorem sgmt_sub {G : Geom} {x y z x' y' z' : Point} : B x y z → B x' y' z' →
    E x z x' z' → E y z y' z' → E x y x' y' := by
    intro hb1 hb'1 he1 he2; by_cases heq : y = z
    · subst heq; exact (E_id he2.symm) ▸ he1
    have heq' : y' ≠ z' := E_id_mt heq he2.symm
    have ⟨w, hb2, heq2⟩ := sgmt_const' y z
    have ⟨w', hb'2, he3⟩ := sgmt_const y' z' z w
    rw [E_symm_iff] at he3
    have hb3 : B x z w := btwn_xzw_of_xyz_yzw_ne hb1 hb2 heq
    have hb'3 : B x' z' w' := btwn_xzw_of_xyz_yzw_ne hb'1 hb'2 heq'
    have he4 : E x w x' w' := sgmt_add hb3 hb'3 he1 he3
    rw [btwn_symm_iff] at hb2 hb'2
    rw [E_flip_both_iff] at he1 he2 he3 he4 ⊢
    apply five_sgmt heq2.symm hb2 hb'2 he3 he2 he4 he1


-- this is definition 4.3 in Beeson (basically side side side premises?)
def E3 {G : Geom} (x y z a b c : Point) := E x y a b ∧ E y z b c ∧ E x z a c

-- Satz 4.5 and 4.6
/-  if ac ≡ a'c' and B a b c there is some b' so that B a' b' c'
    and ab ≡ a'b' and bc ≡ b'c'; 4.6 shows that you don't need to know what c is
    to construct b' but this is not interesting to me; Beeson uses a function
    E3 here to capture all the congruences but I think this way is easier in
    Lean-/
theorem sgmt_split {G : Geom} {a b c a' c' : Point} : B a b c → E a c a' c' →
    (∃ b', B a' b' c' ∧ E a b a' b' ∧ E b c b' c') := by
        intro hb1 he1; have ⟨w', hb'2, heq2⟩ := sgmt_const' c' a'
        have ⟨w, hb2, he2⟩ := sgmt_const c a a' w'
        have ⟨b', hb'3, he3⟩ := sgmt_const w' a' a b
        have ⟨c'', hb'4, he4⟩ := sgmt_const w' b' b c
        have hb'5 : B a' b' c'' := btwn_yzw_of_xyz_xzw hb'3 hb'4
        have he5 : E a c a' c'' := sgmt_add hb1 hb'5 he3.symm he4.symm
        have he6 : E a' c' a' c'' := E_eucl he1 he5
        have hb'6 : B w' a' c'' := btwn_xyw_of_xyz_xzw hb'3 hb'4
        have heq3 : c' = c'' := unique_sgmt_const heq2.symm hb'2.symm (E_refl) hb'6 he6.symm
        subst heq3; exact ⟨b', hb'5, he3.symm, he4.symm⟩

-- this is definition 4.10 in Beeson
def Col {G : Geom} (x y z : Point) := B x y z ∨ B y z x ∨ B z x y

-- Satz 4.11 : Collinear is symmetric in all of its inputs
theorem Col.xy {G : Geom} {x y z : Point} (h : Col x y z) : Col y x z := by
    unfold Col at h ⊢; rcases h with h' | h' | h'
    ·   exact Or.inr <| Or.inr h'.symm
    ·   exact Or.inr <| Or.inl h'.symm
    ·   exact Or.inl h'.symm

theorem Col.xz {G : Geom} {x y z : Point} (h : Col x y z) : Col z y x := by
    unfold Col at h ⊢; rcases h with h' | h' | h'
    ·   exact Or.inl h'.symm
    ·   exact Or.inr <| Or.inr h'.symm
    ·   exact Or.inr <| Or.inl h'.symm

theorem Col.yz {G : Geom} {x y z : Point} (h : Col x y z) : Col x z y := h.xz.xy.xz

theorem Col.l {G : Geom} {x y z : Point} {h : Col x y z} : Col y z x := h.xy.yz

theorem Col.r {G : Geom} {x y z : Point} {h : Col x y z} : Col z x y := h.xz.yz

theorem col_xy_iff {G : Geom} {x y z : Point} : Col x y z ↔ Col y x z := by
    constructor; all_goals exact fun x ↦ x.xy

theorem col_xz_iff {G : Geom} {x y z : Point} : Col x y z ↔ Col z y x := by
    constructor; all_goals exact fun x ↦ x.xz

theorem col_yz_iff {G : Geom} {x y z : Point} : Col x y z ↔ Col x z y := by
    constructor; all_goals exact fun x ↦ x.yz

theorem col_shift_iff {G : Geom} {x y z : Point} : Col x y z ↔ Col y z x := by
    constructor; exact fun x ↦ x.l; exact fun x ↦ x.r

-- Satz 4.12ab
theorem col_triv_xxy {G : Geom} {x y : Point} : Col x x y := by
    unfold Col; exact Or.inl (btwn_refl)

theorem col_triv_xyx {G : Geom} {x y : Point} : Col x y x := by
    unfold Col; exact Or.inr (Or.inr btwn_refl)

end Geom
end Ch4
