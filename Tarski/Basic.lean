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

class Congruence (α : Type u) where
    congr : α → α → Prop

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

-- Satz 2.15 : The proof in Beeson basically derives Satz 3.1 in its proof;
-- makes more sense to just prove it first.

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
theorem xyz_of_xyw_yzw {G : Geom} {x y z w : Point} : B x y w → B y z w → B x y z := by
    intro hb1 hb2; have ⟨a, ha1, ha2⟩ := inner_pasch hb1 hb2
    rw [btwn_id ha1]; apply btwn_symm ha2

-- Satz 3.6a
theorem yzw_of_xyz_xzw {G : Geom} {x y z w : Point} : B x y z → B x z w → B y z w :=
    fun hb1 hb2 ↦ (xyz_of_xyw_yzw hb2.symm hb1.symm).symm

-- Satz 3.7a
theorem xzw_of_xyz_yzw_ne {G : Geom} {x y z w} : B x y z → B y z w → y ≠ z → B x z w := by
    intro hb1 hb2 hne; have ⟨a, ha1, ha2⟩ : ∃ a, B x z a ∧ E z a z w := sgmt_const x z z w
    have hb3 : B y z a := yzw_of_xyz_xzw hb1 ha1
    have he1 : E w a a a := five_sgmt hne hb2 hb3 (E_refl) (ha2).symm (E_refl) (E_refl)
    exact (E_id he1) ▸ ha1

-- Satz 3.5b
theorem xzw_of_xyw_yzw {G : Geom} {x y z w : Point} : B x y w → B y z w → B x z w := by
    intro hb1 hb2; have h := xyz_of_xyw_yzw hb1 hb2
    by_cases h' : y = z
    · exact h' ▸ hb1
    · exact xzw_of_xyz_yzw_ne h hb2 h'

-- Satz 3.6b
theorem xyw_of_xyz_xzw {G : Geom} {x y z w : Point} : B x y z → B x z w → B x y w :=
    fun hb1 hb2 ↦ (xzw_of_xyw_yzw hb2.symm hb1.symm).symm

-- Satz 3.7b
theorem xyw_of_xyz_yzw_ne {G : Geom} {x y z w} : B x y z → B y z w → y ≠ z → B x y w := by
    intro hb1 hb2 hne; have hb3 : B x z w := xzw_of_xyz_yzw_ne hb1 hb2 hne
    exact xyw_of_xyz_xzw hb1 hb3

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
    opposite side of x so that ya ≡ αβ, then B x y a and y ≠ a; I've added more general results;
    a contrapositive to E_id, and a variant of sgmt_const that constructs a nontrivial segment
    without specifying which interval it is congruent to-/

theorem E_id_mt {G : Geom} {x y a b : Point} : a ≠ b → E x y a b → x ≠ y :=
    fun hE1 he1 hE2 ↦ hE1 (E_id (hE2 ▸ he1.symm))

/- This theorem -/
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
    refine ⟨p, ?_, hb6⟩; apply xzw_of_xyw_yzw hb5 hb7

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
    have hb2 : B w z y := (yzw_of_xyz_xzw hb1 hw1).symm
    have hb'2 : B w' z' y' := (yzw_of_xyz_xzw hb'1 hw'1).symm
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
    have hb3 : B x z w := xzw_of_xyz_yzw_ne hb1 hb2 heq
    have hb'3 : B x' z' w' := xzw_of_xyz_yzw_ne hb'1 hb'2 heq'
    have he4 : E x w x' w' := sgmt_add hb3 hb'3 he1 he3
    rw [btwn_symm_iff] at hb2 hb'2
    rw [E_flip_both_iff] at he1 he2 he3 he4 ⊢
    apply five_sgmt heq2.symm hb2 hb'2 he3 he2 he4 he1


-- this is definition 4.3 in Beeson (basically side side side premises?)
def E3 {G : Geom} (x y z a b c : Point) := E x y a b ∧ E y z b c ∧ E x z a c

-- Satz 4.5
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
        have hb'5 : B a' b' c'' := yzw_of_xyz_xzw hb'3 hb'4
        have he5 : E a c a' c'' := sgmt_add hb1 hb'5 he3.symm he4.symm
        have he6 : E a' c' a' c'' := E_eucl he1 he5
        have hb'6 : B w' a' c'' := xyw_of_xyz_xzw hb'3 hb'4
        have heq3 : c' = c'' :=
            unique_sgmt_const heq2.symm hb'2.symm (E_refl) hb'6 he6.symm
        subst heq3; exact ⟨b', hb'5, he3.symm, he4.symm⟩

-- Satz 4.6; basically a uniqueness result for Satz 4.5 (misstated on the website)
theorem btwn_of_btwn_e3 {G : Geom} {x y z x' y' z' : Point} :
    B x y z → E3 x y z x' y' z' → B x' y' z' := by
    intro hb ⟨he1, he2, he3⟩; have ⟨z'', hz'1, hz'2⟩ := sgmt_const x' y' y z
    by_cases h : x' = y'
    · subst h; exact btwn_refl
    have h' : E z'' z' z z := five_sgmt h hz'1 hb he1.symm hz'2 he3.symm he2.symm
    exact (E_id h')▸ hz'1

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

-- Satz 4.14
theorem col_of_col_e3 {G : Geom} {x y z x' y' z' : Point} :
    Col x y z → E3 x y z x' y' z' → Col x' y' z' := by
    intro hcol ⟨he1, he2, he3⟩; rcases hcol with h' | h' | h'
    ·   apply Or.inl; exact btwn_of_btwn_e3 h' ⟨he1, he2, he3⟩
    ·   apply Or.inr; apply Or.inl; exact btwn_of_btwn_e3 h' ⟨he2, he3.lr, he1.lr⟩
    ·   apply Or.inr; apply Or.inr; exact btwn_of_btwn_e3 h' ⟨he3.lr, he1, he2.lr⟩

-- Satz 4.15
theorem e3_of_col_eq {G : Geom} {x y z x' y' : Point} : Col x y z → E x y x' y' →
    ∃ z', E3 x y z x' y' z' := by
    intro hcol he1; rcases hcol with h' | h' | h'
    ·   have ⟨z', hb'1, he2⟩ := sgmt_const x' y' y z; rw [E_symm_iff] at he2
        have he3 : E x z x' z' := sgmt_add h' hb'1 he1 he2
        exact ⟨z', he1, he2, he3⟩
    ·   have ⟨z', hb'1, he2, he3⟩ := sgmt_split h' he1.lr
        exact ⟨z', he1, he2, he3.lr⟩
    ·   have ⟨z', hb'1, he2⟩ := sgmt_const y' x' x z
        have he3 := sgmt_add h' hb'1.symm he2.lr.symm he1
        exact ⟨z', he1, he3.lr, he2.symm⟩

-- Satz 4.16 (I thought this was pretty straightforward)
theorem sgmt_extend {G : Geom} {x y z w x' y' z' w' : Point} :
x ≠ y → Col x y z → E3 x y z x' y' z' → E x w x' w' → E y w y' w' → E z w z' w' := by
    intro hne1 hcol ⟨he1, he2, he3⟩ he4 he5
    rcases hcol with hb1 | hb1 | hb1
    ·   have hb'1 := btwn_of_btwn_e3 hb1 ⟨he1, he2, he3⟩
        exact five_sgmt hne1 hb1 hb'1 he1 he2 he4 he5
    ·   have hb'1 := btwn_of_btwn_e3 hb1 ⟨he2, he3.lr, he1.lr⟩
        exact inner_five_sgmt hb1 hb'1 he2 he3.lr he5 he4
    ·   have hb'1 := btwn_of_btwn_e3 hb1 ⟨he3.lr, he1, he2.lr⟩
        exact five_sgmt hne1.symm hb1.symm hb'1.symm he1.lr he3 he5 he4

theorem e3_triv {G : Geom} (x y z : Point) : E3 x y z x y z := ⟨E_refl, E_refl, E_refl⟩

-- Satz 4.17; a converse of hi_dim
theorem E_of_ne_col_E {G : Geom} {x y z u v : Point} : x ≠ y → Col x y z →
    E x u x v → E y u y v → E z u z v :=
    fun hne1 hcol he1 he2 ↦ sgmt_extend hne1 hcol (e3_triv x y z) he1 he2

-- Satz 4.18
theorem eq_of_ne_col_E {G : Geom} {x y z z' : Point} : x ≠ y →
Col x y z → E x z x z' → E y z y z' → z = z' :=
    fun hne hcol he1 he2 ↦ E_id (E_of_ne_col_E hne hcol he1 he2).symm

-- Satz 4.19
theorem eq_of_btwn_E {G : Geom} {x y z z' : Point} : B x z y → E x z x z' →
E y z y z' → z = z' := by
    intro hb he1 he2; by_cases heq : x = y
    ·   subst heq; have heq2 : x = z := btwn_id hb
        subst heq2; exact E_id he2.symm
    ·   have hcol : Col x y z := Or.inr <| Or.inl hb.symm
        exact eq_of_ne_col_E heq hcol he1 he2

end Geom
end Ch4

section Ch5
namespace Geom

-- Satz 5.1, due to Gupta (1965); this one is a mess.
theorem xzw_or_xwz_of_ne_xyz_xyw {G : Geom} {x y z w : Point} :
x ≠ y → B x y z → B x y w → (B x z w ∨ B x w z) := by
    sorry

-- Satz 5.2
theorem yzw_or_ywz_of_ne_xyz_xyw {G : Geom} {x y z w : Point} :
x ≠ y → B x y z → B x y w → (B y z w ∨ B y w z) := by
    intro hne hb1 hb2; rcases (xzw_or_xwz_of_ne_xyz_xyw hne hb1 hb2) with h | h
    ·   exact Or.inl (yzw_of_xyz_xzw hb1 h)
    ·   exact Or.inr (yzw_of_xyz_xzw hb2 h)

-- Satz 5.3
theorem xyz_or_xzy_of_xyw_xzw {G : Geom} {x y z w : Point} :
B x y w → B x z w → (B x y z ∨ B x z y) := by
    intro hb1 hb2; have ⟨u, hu1, hu2⟩ := sgmt_const' x w
    have hywu : B y w u := yzw_of_xyz_xzw hb1 hu1
    have hzwu : B z w u := yzw_of_xyz_xzw hb2 hu1
    have h1 : B w z y ∨ B w y z := yzw_or_ywz_of_ne_xyz_xyw hu2.symm hzwu.symm hywu.symm
    rw [btwn_symm_iff] at hb1 hb2; rcases h1 with h | h
    ·   exact Or.inl (yzw_of_xyz_xzw h hb1).symm
    ·   exact Or.inr (yzw_of_xyz_xzw h hb2).symm

-- Def 5.4: less than or equal to

def le {G : Geom} (x y z w : Point) := ∃ a, (B z a w ∧ E x y z a)

-- Satz 5.5
theorem sgmt_of_le {G : Geom} {x y z w : Point} :
    le x y z w → ∃ a, B x y a ∧ E x a z w := by
    intro ⟨b, hb1, he1⟩; have ⟨a, hb2, he2⟩ := sgmt_const x y b w
    exact ⟨a, hb2, sgmt_add hb2 hb1 he1 he2⟩

theorem le_of_sgmt {G : Geom} {x y z w : Point} :
    (∃ a, B x y a ∧ E x a z w) → le x y z w := by
    intro ⟨b, hb1, he1⟩; have ⟨a, hb2, he2, he3⟩ := sgmt_split hb1 he1
    exact ⟨a, hb2, he2⟩

theorem le_iff {G : Geom} {x y z w : Point} : le x y z w ↔ (∃ a, B x y a ∧ E x a z w) :=
    Iff.intro sgmt_of_le le_of_sgmt

-- Satz 5.6
theorem le_of_le_E {G : Geom} {x y z w x' y' z' w': Point} :
    le x y z w → E x y x' y' → E z w z' w' → le x' y' z' w' := by
    intro ⟨a, ha1, ha2⟩ he1 he2; have ⟨a', ha'1, ha'2, _⟩ := sgmt_split ha1 he2
    refine ⟨a', ha'1, E_trans (E_trans he1.symm ha2) ha'2⟩

theorem le.l {G : Geom} {x y z w : Point} (h : le x y z w) : le y x z w :=
    le_of_le_E h E_comm E_refl

theorem le.r {G : Geom} {x y z w : Point} (h : le x y z w) : le x y w z :=
    le_of_le_E h E_refl E_comm

theorem le.lr {G : Geom} {x y z w : Point} (h : le x y z w) : le y x w z := h.l.r

-- Satz 5.7
theorem le_refl {G : Geom} {x y : Point} : le x y x y := ⟨y, btwn_refl', E_refl⟩

-- Satz 5.8
theorem le_trans {G : Geom} {x y z w u v : Point} : le x y z w → le z w u v → le x y u v := by
    intro ⟨a, ha1, ha2⟩ ⟨b, hb1, hb2⟩; have ⟨c, hc1, hc2, hc3⟩ := sgmt_split ha1 hb2
    exact ⟨c, xyw_of_xyz_xzw hc1 hb1, E_trans ha2 hc2⟩

-- Satz 5.9; moved out narboux's lemma and added eq_of_xyz_xzy myself; easy enough.
theorem narboux_lemma {G : Geom} {x y z : Point} : B x y z → E x y x z → y = z := by
    intro hb1 he1; by_cases h : x = y
    ·   subst h; exact E_id he1.symm
    have ⟨w, hw1, hw2⟩ := sgmt_const' y x; rw [btwn_symm_iff] at hw1
    have hw3 : B w x z := xyw_of_xyz_yzw_ne hw1 hb1 h
    apply unique_sgmt_const hw2.symm hw1 he1 hw3 E_refl

theorem eq_of_xyz_xzy {G : Geom} {x y z : Point} : B x y z → B x z y → y = z :=
    fun hb1 hb2 ↦ btwn_id <| yzw_of_xyz_xzw hb1 hb2

theorem le_antisymm {G : Geom} {x y z w : Point} : le x y z w → le z w x y → E x y z w := by
    intro ⟨a, ha1, ha2⟩ ⟨b, hb1, hb2⟩; have ⟨c, hc1, hc2, hc3⟩ := sgmt_split ha1 hb2
    have he1 : E x y x c := E_trans ha2 hc2
    have hb3 : B x c y := xyw_of_xyz_xzw hc1 hb1
    have heq1 : c = y := narboux_lemma hb3 he1.symm
    subst heq1; have heq2 : c = b := eq_of_xyz_xzy hc1 hb1
    subst heq2; exact hb2.symm

-- Satz 5.10
theorem le_total {G : Geom} {x y z w : Point} : le x y z w ∨ le z w x y := by
    have ⟨b, ha1, ha2⟩ := sgmt_const' w z; rw [btwn_symm_iff] at ha1
    have ⟨a, hb1, hb2⟩ := sgmt_const b z x y
    have h := yzw_or_ywz_of_ne_xyz_xyw ha2.symm ha1 hb1
    rcases h with h' | h'
    ·   apply Or.inr; rw [le_iff]; exact ⟨a, h', hb2⟩
    ·   apply Or.inl; exact ⟨a, h', hb2.symm⟩

-- Satz 5.11
theorem nonneg {G : Geom} {x y z : Point} : le z z x y := ⟨x, btwn_refl, degen_sgmts⟩

-- Satz 5.12
theorem le_of_btwn_left {G : Geom} {x y z : Point} : B x y z → le x y x z := by
    intro hb1; exact ⟨y, hb1, E_refl⟩

theorem le_of_btwn_right {G : Geom} {x y z : Point} : B x y z → le y z x z := by
    intro hb1; unfold le; rw [btwn_symm_iff] at hb1;
    have ⟨a, ha1, ha2, ha3⟩ := sgmt_split hb1 E_comm; exact ⟨a, ha1, ha2.l⟩

theorem btwn_of_col_le {G : Geom} {x y z : Point} :
    Col x y z → le x y x z → le y z x z → B x y z := by
    intro hcol hle1 hle2; rcases hcol with h | h | h
    ·   exact h
    ·   have hle3 : le x z x y := (le_of_btwn_right h).lr; rw [btwn_symm_iff] at h
        have heq1 : E x y x z := le_antisymm hle1 hle3
        have heq2 : z = y := narboux_lemma h <| heq1.symm
        subst heq2; exact btwn_refl'
    ·   have hle3 : le x z y z := (le_of_btwn_left h).lr; rw [btwn_symm_iff] at h
        have heq1 : E y z x z := le_antisymm hle2 hle3
        have heq2 : x = y := narboux_lemma h.symm heq1.lr.symm
        subst heq2; exact btwn_refl

theorem xyz_iff_xy_le_and_yz_le_of_col {G : Geom} {x y z : Point} :
    Col x y z → (B x y z ↔ (le x y x z ∧ le y z x z)) := fun hcol ↦ Iff.intro
        (fun hb ↦ ⟨le_of_btwn_left hb, le_of_btwn_right hb⟩)
        (fun ⟨hl1, hl2⟩ ↦ btwn_of_col_le hcol hl1 hl2)

end Geom
end Ch5

section Ch6
namespace Geom

-- sameside x y z means ray x y = ray x z and neither y nor z = x
def Point.sameside {G : Geom} (x y z : Point) := y ≠ x ∧ z ≠ x ∧ (B x y z ∨ B x z y)

-- Satz 6.2;
theorem ssxy_of_xaz_yaz {G : Geom} {x y z a : Point} : x ≠ a → y ≠ a → z ≠ a →
    B x a z → B y a z → a.sameside x y := by
    intro h1 h2 h3 hb1 hb2; unfold Point.sameside
    rw [btwn_symm_iff] at hb1 hb2
    exact ⟨h1, h2, (yzw_or_ywz_of_ne_xyz_xyw h3 hb1 hb2)⟩

theorem yaz_of_xaz_ssxy {G : Geom} {x y z a : Point} :
    B x a z → a.sameside x y → B y a z := by
    intro hb1 ⟨h1, _, hss1⟩; rcases hss1 with h | h
    ·   exact xzw_of_xyz_yzw_ne h.symm hb1 h1
    ·   exact yzw_of_xyz_xzw h.symm hb1

theorem ssxy_iff_yaz_of_xaz {G : Geom} {x y z a : Point} :
    x ≠ a → y ≠ a → z ≠ a → B x a z → (a.sameside x y ↔ B y a z) := by
    intro h1 h2 h3 hb1; constructor
    ·   exact yaz_of_xaz_ssxy hb1
    ·   exact ssxy_of_xaz_yaz h1 h2 h3 hb1

-- Satz 6.3
theorem exists_os_of_ss {G : Geom} {x y a : Point} :
    a.sameside x y → (∃ z, z ≠ a ∧ B x a z ∧ B y a z) := by
    intro ⟨h1, h2, hb1⟩; have ⟨z, hz1, hz2⟩ := sgmt_const' x a
    rcases hb1 with h | h
    ·   exact ⟨z, hz2.symm, hz1, xzw_of_xyz_yzw_ne h.symm hz1 h1⟩
    ·   exact ⟨z, hz2.symm, hz1, yzw_of_xyz_xzw h.symm hz1⟩

theorem ss_of_exists_os {G : Geom} {x y a : Point} : x ≠ a → y ≠ a →
    (∃ z, z ≠ a ∧ B x a z ∧ B y a z) → a.sameside x y := by
    intro h1 h2 ⟨z, h3, hb1, hb2⟩; refine ⟨h1, h2, ?_⟩
    exact yzw_or_ywz_of_ne_xyz_xyw h3 hb1.symm hb2.symm

theorem exists_os_iff_ss {G : Geom} {x y a : Point} : x ≠ a → y ≠ a →
    ((∃ z, z ≠ a ∧ B x a z ∧ B y a z) ↔ a.sameside x y) := by
    intro h1 h2; constructor
    · exact ss_of_exists_os h1 h2
    · exact exists_os_of_ss
-- Satz 6.4

end Geom
end Ch6
