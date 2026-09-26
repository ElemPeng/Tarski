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
