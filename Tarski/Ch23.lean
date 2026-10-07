import Tarski.Foundations

section Congruence
namespace Geom

--Satz 2.1
theorem E_refl {G : Geom} {x y : Point} : E x y x y := E_eucl E_comm E_comm

--Satz 2.2
@[symm] theorem E.symm {G : Geom} {x y z w : Point} (h : E x y z w) : E z w x y :=
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
theorem E_triv {G : Geom} {x y : Point} : E x x y y := by
    have ⟨z, hz1, hz2⟩ : ∃ z, B x x z ∧ E x z y y := sgmt_const x x y y
    have hE : x = z := E_id hz2; rwa [←hE] at hz2

--- Satz 2.11
theorem sgmt_add {G : Geom} {x y z x' y' z' : Point} : B x y z → B x' y' z' →
    E x y x' y' → E y z y' z' → E x z x' z' := by
    intro hb1 hb2 he1 he2; apply E_flip_both; by_cases h : x = y
    ·   subst h; have he1 := he1.symm; have he2 := he2.symm
        have hx'y' : x' = y' := E_id he1; subst hx'y'; exact (he2.lr.symm)
    apply outer_five_sgmt h (hb1) hb2 he1 he2 (E_triv) (he1.lr)

--- Satz 2.12
theorem unique_sgmt_const {G : Geom} {q a x b c y : Point} :
    q ≠ a → B q a x → E a x b c → B q a y → E a y b c → x = y := by
        intro hne hb1 he1 hb2 he2
        have h1 : E a x a y := E_trans he1 he2.symm
        have h2 : E x y y y :=
            outer_five_sgmt hne hb1 hb2 E_refl h1 E_refl E_refl
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
@[symm] theorem btwn_symm {G : Geom} {x y z : Point} : B x y z → B z y x := by
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
    have he1 : E w a a a := outer_five_sgmt hne hb2 hb3 (E_refl) (ha2).symm (E_refl) (E_refl)
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

-- Def 3.8: n-fold Betweenness

def Bn {G : Geom} (L : List Point) := ∀ x y z : Point, [x, y, z].Sublist L → B x y z

theorem Bn.to_btwn {_G : Geom} {L : List Point} (h : Bn L) (x y z : Point)
(h' : [x,y,z].Sublist L := by grind) : B x y z := h x y z h'

example {G : Geom} {x y z w: Point}: Bn [x, y, z, w] → B x y z := by
    intro h; exact h.to_btwn x y z

-- Satz 3.9
theorem Bn_symm {G : Geom} {L : List Point} : Bn L → Bn L.reverse := by
    intro h x y z hxyz; symm
    have h' : [z, y, x].Sublist L := List.reverse_sublist.mp hxyz
    exact h z y x h'

theorem Bn.symm {G : Geom} {L : List Point} (h : Bn L) : Bn L.reverse := Bn_symm h

-- Satz 3.10
theorem Bn_sublist {G : Geom} {L M : List Point} : M.Sublist L → Bn L → Bn M :=
    fun hML hL x y z hxyz ↦ hL x y z (hxyz.trans hML)

-- Satz 3.11 lmao this is a huge pain

theorem four_cases {G : Geom} {L1 L2 : List Point} {a b c : Point} : [a, b, c].Sublist (L1 ++ L2) →
[a, b, c].Sublist L1 ∨ ([a, b].Sublist L1 ∧ c ∈ L2) ∨
(a ∈ L1 ∧ [b, c].Sublist L2) ∨ [a, b, c].Sublist L2 := by
    intro h; rw [List.sublist_append_iff] at h
    obtain ⟨l1, l2, h1, hl1, hl2⟩ := h
    rw [List.cons_eq_append_iff] at h1; rcases h1 with ⟨ha, hb⟩ | ⟨l3, ha, hb⟩
    ·   subst hb; simp [← or_assoc]; exact Or.inr hl2
    ·   subst ha; rw [List.cons_eq_append_iff] at hb; rcases hb with ⟨hc, hd⟩ | ⟨l4, hc, hd⟩
        ·   apply Or.inr ∘ Or.inr ∘ Or.inl; subst hc hd; refine ⟨?_,hl2⟩
            exact List.mem_of_cons_sublist hl1
        ·   subst hc; rw [List.singleton_eq_append_iff] at hd
            rcases hd with ⟨he, hf⟩ | ⟨he, hf⟩ <;> subst he hf
            ·   apply Or.inr ∘ Or.inl; refine ⟨hl1, ?_⟩
                exact List.mem_of_cons_sublist hl2
            ·   exact Or.inl hl1

theorem two_cases_3 {G : Geom} {L : List Point} {a b c p : Point} : [a, b, c].Sublist (p :: L) →
(a = p ∧ [b, c].Sublist L) ∨ [a, b, c].Sublist L := by
    intro h; rw [List.sublist_cons_iff] at h
    rcases h with ha | ⟨N, ha, hb⟩
    ·   exact Or.inr ha
    ·   rw [List.cons_eq_cons] at ha; obtain ⟨hc, hd⟩ := ha
        subst hc hd; simp only [true_and]; exact Or.inl hb

theorem two_cases_2 {G : Geom} {L : List Point} {a b p : Point} : [a, b].Sublist (p :: L) →
(a = p ∧ [b].Sublist L) ∨ [a, b].Sublist L := by
    intro h; rw [List.sublist_cons_iff] at h
    rcases h with ha | ⟨N, ha, hb⟩
    ·   exact Or.inr ha
    ·   rw [List.cons_eq_cons] at ha; obtain ⟨hc, hd⟩ := ha
        subst hc hd; simp only [true_and]; exact Or.inl hb

theorem two_cases_1 {G : Geom} {L: List Point} {a p : Point} : a ∈ (p :: L) →
(a = p) ∨ [a].Sublist L := by
    intro h; rw [List.mem_cons] at h
    rcases h with ha | ha
    ·   exact Or.inl ha
    ·   exact Or.inr <| List.singleton_sublist.mpr ha

theorem three_cases {G : Geom} {L1 L2 : List Point} {a b : Point} : [a, b].Sublist (L1 ++ L2) →
[a, b].Sublist L1 ∨ (a ∈ L1 ∧ b ∈ L2) ∨ [a, b].Sublist L2 := by
    intro h; rw [List.sublist_append_iff] at h
    obtain ⟨l1, l2, h1, h2, h3⟩ := h
    rw [List.cons_eq_append_iff] at h1; rcases h1 with ⟨ha, hb⟩ | ⟨l3, ha, hb⟩
    ·   subst ha hb; exact Or.inr <| Or.inr h3
    ·   subst ha; rw [List.cons_eq_append_iff] at hb
        rcases hb with ⟨hc, hd⟩ | ⟨l4, hc, hd⟩ <;> subst hc
        ·   rw [hd] at h3; apply Or.inr ∘ Or.inl; constructor
            ·   exact List.mem_of_cons_sublist h2
            ·   exact List.mem_of_cons_sublist h3
        ·   simp_all

theorem Bn_insert {G : Geom} (L1' L2' : List Point) {x p y : Point} :
Bn (L1' ++ [x] ++ y :: L2') → B x p y → Bn (L1' ++ [x] ++ p :: y :: L2') := by
    intro hBn hBxpy a b c habc
    have hL1Bn : Bn (L1' ++ [x]) :=
        Bn_sublist (List.sublist_append_left (L1' ++ [x]) (y :: L2') ) hBn
    have hL2Bn : Bn (y :: L2') :=
        Bn_sublist (List.sublist_append_right (L1' ++ [x]) (y :: L2')) hBn
    rcases (four_cases habc) with ha | ⟨ha, hb⟩ | ⟨ha, hb⟩ | ha
    ·   exact hL1Bn a b c ha
    ·   rcases (two_cases_1 hb) with hc | hc
        ·   subst hc; have haby : B a b y := by
                refine hBn.to_btwn a b y <| List.sublist_append_iff.mpr ⟨[a, b], [y], ?_, ha, by simp⟩
                ·   exact List.self_eq_append_right.mpr rfl
            rcases (three_cases ha) with hd | ⟨hd, he⟩ | hd
            ·   have hbxy : B b x y := by
                    refine hBn.to_btwn b x y <| List.sublist_append_iff.mpr ⟨[b, x], [y], ?_, ?_, ?_⟩
                    ·   exact List.self_eq_append_right.mpr rfl
                    ·   refine List.sublist_append_iff.mpr ⟨[b], [x], by simp, ?_, by simp⟩
                        ·   exact List.sublist_of_cons_sublist hd
                    ·   exact List.singleton_sublist.mpr (List.mem_cons_self)
                have hbcy := xzw_of_xyw_yzw hbxy hBxpy
                exact xyz_of_xyw_yzw haby hbcy
            ·   simp at he; subst he; exact xyz_of_xyw_yzw haby hBxpy
            ·   exact absurd (List.Sublist.length_le hd) (by simp)
        ·   refine hBn a b c (List.sublist_append_iff.mpr ?_)
            exact ⟨[a, b], [c], List.self_eq_append_right.mpr rfl, ha, hc⟩
    ·   rcases (two_cases_2 hb) with ⟨hc, hd⟩ | hc
        ·   subst hc; simp at hd; have hayc : B a y c := by
                rcases hd with h | h
                ·   subst h; exact btwn_refl'
                ·   refine hBn.to_btwn a y c <|
                    List.sublist_append_iff.mpr ⟨[a], [y, c], by simp, ?_, ?_⟩
                    ·   exact List.singleton_sublist.mpr ha
                    ·   refine List.Sublist.cons_cons y ?_
                        exact List.singleton_sublist.mpr h
            rw [List.mem_append] at ha; simp at ha
            rcases ha with h | h
            ·   have haxy : B a x y := by
                    refine hBn.to_btwn a x y <|
                    List.sublist_append_iff.mpr ⟨[a, x], [y], by simp, ?_, by simp⟩
                    rw [List.sublist_append_iff]
                    refine ⟨[a], [x], by simp, ?_, by simp⟩
                    exact List.singleton_sublist.mpr h
                have haby : B a b y := xzw_of_xyw_yzw haxy hBxpy
                exact xyw_of_xyz_xzw haby hayc
            ·   subst h; exact xyw_of_xyz_xzw hBxpy hayc
        ·   refine hBn a b c (List.sublist_append_iff.mpr ?_)
            exact ⟨[a], [b, c], List.self_eq_append_left.mpr rfl,
                 List.singleton_sublist.mpr ha, hc⟩
    ·   rcases (two_cases_3 ha) with ⟨hc, hd⟩ | hc
        ·   subst hc; have hxbc : B x b c := by
                refine hBn.to_btwn x b c <|
                    List.sublist_append_iff.mpr ⟨[x], [b, c], by simp, by simp, hd⟩
            rcases (two_cases_2 hd) with ⟨he, hf⟩ | he
            ·   subst he; exact yzw_of_xyz_xzw hBxpy hxbc
            ·   have hxyb : B x y b := by
                    refine hBn.to_btwn x y b <|
                        List.sublist_append_iff.mpr ⟨[x], [y, b], by simp, by simp, ?_⟩
                    refine List.Sublist.cons_cons y ?_
                    rw [List.singleton_sublist]; exact List.mem_of_cons_sublist he
                have hxab : B x a b := xyw_of_xyz_xzw hBxpy hxyb
                exact yzw_of_xyz_xzw hxab hxbc
        ·   exact hL2Bn a b c hc

-- Some simple cases to get started
theorem Bn3_of_btwn {G : Geom} {a b c : Point} : B a b c → (Bn [a, b, c]) := by
    intro h x y z h'; have h'' : [x , y, z] = [a, b, c] := (List.Sublist.length_eq h').mp rfl
    simp at h''; have ⟨ha, hb, hc⟩ := h''; rwa [ha, hb, hc]

theorem B.Bn {G : Geom} {a b c : Point} (h : B a b c) : Bn [a, b, c] := Bn3_of_btwn h

-- Bn4 version of Satz 3.5
theorem Bn4_of_xyw_yzw {G : Geom} {x y z w : Point} : B x y w → B y z w → Bn [x, y, z, w] :=
    fun hb1 hb2 ↦ Bn_insert [x] [] (hb1.Bn) hb2

-- Bn4 version of Satz 3.6
theorem Bn4_of_xyz_xzw {G : Geom} {x y z w : Point} : B x y z → B x z w → Bn [x, y, z, w] :=
    fun hb1 hb2 ↦ Bn_insert [] [w] (hb2.Bn) hb1

--Bn4 version of Satz 3.7
theorem Bn4_of_xyz_yzw_ne {G : Geom} {x y z w : Point} : B x y z → B y z w → y ≠ z → Bn [x, y, z, w] :=
    fun hb1 hb2 ne ↦ Bn4_of_xyz_xzw hb1 <|xzw_of_xyz_yzw_ne hb1 hb2 ne

-- an application from the SST proof of Satz 5.1
theorem Bn5_of_xyz_xzw_xwv {G : Geom} {x y z w v : Point} :  B x y z → B x z w → B x w v → Bn [x, y, z, w, v] :=
    fun hb1 hb2 hb3 ↦ Bn_insert [] [w, v] (Bn4_of_xyz_xzw hb2 hb3) hb1

-- possibly another helper, not in SST but should be true.
theorem Bn_concat {G : Geom} {L1' L2' : List Point} {x y : Point} :
    Bn (L1' ++ [x, y]) → Bn (x :: y :: L2') → x ≠ y → Bn (L1' ++ x :: y :: L2') := by sorry

-- Satz 3.12, flipped (easier to add to the head than the tail) (use reverse to get tail?)
theorem Bn_head {G : Geom} {L1' L2' : List Point} {p x y : Point} :
    Bn (x :: L1' ++ y :: L2') → B p x y → Bn (p :: x :: L1' ++ [y]) := by sorry

theorem Bn_head_ne {G : Geom} {L1' L2' : List Point} {p x y : Point} :
    Bn (x :: L1' ++ y :: L2') → B p x y → x ≠ y → Bn (p :: x :: L1' ++ y :: L2') := by sorry

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

-- This one is Satz 3.13 specifically
theorem two_dist (G : Geom) : ∃ a b : Point, a ≠ b := by
    have ⟨a, b, _, h, _⟩ := G.three_dist; exact ⟨a, b, h⟩

theorem another_pt {G : Geom} (a : Point) : ∃ b : Point, a ≠ b := by
    have ⟨b, b', hbb'⟩ := two_dist G
    by_cases h: a = b
    ·   subst h; exact ⟨b', hbb'⟩
    exact ⟨b, h⟩

theorem btwn_id_mt {G : Geom} {x y z : Point} : x ≠ y → B x y z → x ≠ z := by
    intro h1 h2 h3; subst h3; exact h1 <| btwn_id h2

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
