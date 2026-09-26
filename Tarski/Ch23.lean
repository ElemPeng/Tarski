import Tarski.Foundations

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

-- Satz 3.4 (and a symmetric form)
theorem eq_of_xyz_yxz {G : Geom} {x y z : Point} : B x y z → B y x z → x = y := by
    intro hb1 hb2; have ⟨a, ha1, ha2⟩ := inner_pasch hb1 hb2
    exact (btwn_id ha1) ▸ (btwn_id ha2)

theorem eq_of_xyz_xzy {G : Geom} {x y z : Point} : B x y z → B x z y → y = z :=
    fun hb1 hb2 ↦ eq_of_xyz_yxz (hb2.symm) (hb1.symm)

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
