import Tarski.Ch6

section Ch7
namespace Geom

-- Def 7.1
/- m is the midpoint of the segment ab if m lies on segment ab and ma ≡ mb
-/
def M {G : Geom} (a m b : Point) := B a m b ∧ E m a m b

-- Satz 7.2

@[symm] theorem midpt_symm {G : Geom} {a m b : Point} : M a m b → M b m a :=
  fun ⟨hb, he⟩ ↦ ⟨hb.symm, he.symm⟩

theorem M.symm {G : Geom} {a m b : Point} (h : M a m b) : M b m a := midpt_symm h

-- Satz 7.3

theorem midpt_triv {G : Geom} {a m : Point} : M a m a ↔ m = a := by
  constructor
  · exact fun ⟨h, _⟩ ↦ (btwn_id h).symm
  · intro h; subst h; exact ⟨btwn_refl, E_refl⟩

-- Satz 7.4
theorem refl_thru_pt {G : Geom} (a : Point) : ∀ p, ∃ p', M p a p' := by
  intro p; by_cases hap : a = p
  · subst hap; exact ⟨a, midpt_triv.mpr rfl⟩
  · have ⟨p', hb, he⟩ := sgmt_const p a a p; exact ⟨p', hb, he.symm⟩

theorem unique_refl_thru_pt {G : Geom} {a : Point} : ∀ p q1 q2, M p a q1 → M p a q2 → q1 = q2 := by
  intro p q1 q2 ⟨hb1, he1⟩ ⟨hb2, he2⟩; by_cases hap : a = p
  · subst hap; exact (E_id he2.symm.l) ▸ (E_id he1.symm.l)
  · exact unique_sgmt_const (Ne.symm hap) hb1 he1.symm hb2 he2.symm

-- Satz 7.5 : definition of the reflection of p through a
noncomputable def Point.R {G : Geom} (a : Point) : Point → Point := fun p ↦
  Exists.choose (refl_thru_pt a p)

-- Satz 7.6
theorem aRp_q_of_Mpaq {G : Geom} {a p q: Point} : M p a q → a.R p = q := by
  intro h; unfold Point.R; let P := refl_thru_pt a p; symm
  apply unique_refl_thru_pt p q (Exists.choose P) h (Exists.choose_spec P)

theorem Mpaq_of_aRp_q {G : Geom} {a p q: Point} : a.R p = q → M p a q := by
  intro h; unfold Point.R at h; rw [←h]; exact Exists.choose_spec (refl_thru_pt a p)

theorem aRp_q_iff_Mpaq {G : Geom} {a p q: Point} : a.R p = q ↔ M p a q :=
  Iff.intro Mpaq_of_aRp_q aRp_q_of_Mpaq

attribute [irreducible] Point.R -- should always use Satz 7.6 to do this

-- Satz 7.7
theorem double_reflect {G : Geom} (a p : Point) : a.R (a.R p) = p := by
  rw [aRp_q_iff_Mpaq]; symm; unfold Point.R
  exact Exists.choose_spec (refl_thru_pt a p)

-- Satz 7.8 : In the book the claim is uniqueness but that follows from Satz 7.9
theorem R_surj {G : Geom} {a : Point} : (a.R).Surjective :=
  fun p' ↦ ⟨a.R p', double_reflect a p'⟩

-- Satz 7.9
theorem R_inj {G : Geom} {a : Point} : (a.R).Injective :=
  fun x y hxy ↦
  calc x = a.R (a.R x) := (double_reflect a x).symm
  _ = a.R (a.R y) := congrArg a.R hxy
  _ = y := double_reflect a y

-- Satz 7.10
theorem R_self {G : Geom} (a : Point) : (a.R) a = a := by
  rw [aRp_q_iff_Mpaq]; exact midpt_triv.mpr rfl

theorem R_eq_self_iff {G : Geom} {a p : Point} : a.R p = p ↔ p = a := by
  rw [aRp_q_iff_Mpaq, midpt_triv, eq_comm]

-- Satz 7.11
theorem R_bijection {G : Geom} {a : Point} :
  (a.R).Injective ∧ (a.R).Surjective := ⟨R_inj, R_surj⟩

-- Satz 7.12
theorem R_involution {G : Geom} {a : Point} : a.R ∘ a.R = id :=
funext (double_reflect a)

-- Satz 7.13

theorem xax'_of_pap'_p'px_xp'x {G : Geom} {x p a p' x' : Point}
(hpap' : B p a p') (hp'px : B p' p x) (hxp'x' : B x p' x') : B x a x' := by
  have hxap' : B x a p' := xzw_of_xyw_yzw hp'px.symm hpap'; symm
  exact xzw_of_xyw_yzw hxp'x'.symm hxap'.symm

theorem R_isometry {G : Geom} {a p q : Point} : E p q (a.R p) (a.R q) := by
  generalize hp' : a.R p = p'
  generalize hq' : a.R q = q'
/-  if p = a then p' = a and E a q a q' follows from the definitions of
    a.R and M
-/
  by_cases hpa : p = a
  · subst hpa; rw [R_self] at hp'; subst hp'
    rw [aRp_q_iff_Mpaq] at hq'; exact hq'.2
/-
  Otherwise construct x, y, x' and y' as follows: We end up with two
  congruent triangles a x y and a x' y',
-/
  have hp'1 := hp'; have hq'1 := hq'
  rw [aRp_q_iff_Mpaq] at hp'1 hq'1
  obtain ⟨hp'2, hp'3⟩ := hp'1; obtain ⟨hq'2, hq'3⟩ := hq'1
  have ⟨x, hx1, hx2⟩ := sgmt_const p' p q a; have ⟨y, hy1, hy2⟩ := sgmt_const q' q p a
  have ⟨x', hx'1, hx'2⟩ := sgmt_const x p' q a; have ⟨y', hy'1, hy'2⟩ := sgmt_const y q' p a
/-  we have x * p * a * p' * x' and y * q * a * q' * y'
    we also have ax ≡ ay ≡ ay' ≡ ax' -/
  have hxax' : B x a x' := xax'_of_pap'_p'px_xp'x hp'2 hx1 hx'1
  have hyay' : B y a y' := xax'_of_pap'_p'px_xp'x hq'2 hy1 hy'1
  change p ≠ a at hpa; have hp'a : p' ≠ a := E_id_mt hpa hp'3.symm.lr
  have hqy : q ≠ y := E_id_mt hpa hy2; have hq'y' : q' ≠ y' := E_id_mt hpa hy'2
-- maybe I should have proven the stuff about B_n back in Ch 2
-- do outer FS with x a x' y' / y' a y x
  have hapx : B a p x := yzw_of_xyz_xzw hp'2.symm hx1
  have hx'p'p : B x' p' p := (yzw_of_xyz_xzw hx1.symm hx'1).symm
  have hx'p'a : B x' p' a := (xyz_of_xyw_yzw hx'p'p hp'2.symm)
  have haqy : B a q y := yzw_of_xyz_xzw hq'2.symm hy1
  have hy'q'q : B y' q' q := (yzw_of_xyz_xzw hy1.symm hy'1).symm
  have hy'q'a : B y' q' a := (xyz_of_xyw_yzw hy'q'q hq'2.symm)
  have hxay'a : E x a y' a := (sgmt_add hapx hy'q'a hy'2.symm.lr (E_trans hx2 hq'3.lr)).l
  have hax'ay : E a x' a y := (sgmt_add hx'p'a haqy hx'2.lr (E_trans hp'3.symm.lr hy2.symm)).l
  have hax : a ≠ x := by intro h; subst h; exact hpa.symm (btwn_id hapx)
  have hx'y'yx : E x' y' y x :=
    outer_five_sgmt hax.symm hxax' hyay'.symm hxay'a hax'ay E_comm hxay'a.symm.lr
/-  then inner FS with y q a x / y' q' a x' (get qx ≡ q'x')-/
  have hyqy'q' : E y q y' q' := E_trans hy2.l hy'2.symm.r
  have haxax' : E a x a x' := sgmt_add hapx hx'p'a.symm hp'3 (E_trans hx2 hx'2.symm)
  have hqxq'x' : E q x q' x' :=
    inner_five_sgmt haqy.symm hy'q'a hyqy'q' hq'3.lr hx'y'yx.symm.r haxax'
/-  and inner FS with x p a q / x' p' a q' (get pq ≡ p'q') -/
  have hxpx'p' : E x p x' p' := E_trans hx2.l hx'2.symm.r
  exact inner_five_sgmt hapx.symm hx'p'a hxpx'p' hp'3.lr hqxq'x'.lr hq'3

-- Satz 7.14 : a.R is an isometry of the space, and therefore an automorphism
-- Satz 7.15
theorem btwn_R {G : Geom} {a p q r : Point} : B p q r → B (a.R p) (a.R q) (a.R r) :=
  fun hpqr ↦ btwn_of_btwn_e3 hpqr ⟨R_isometry, R_isometry, R_isometry⟩

theorem btwn_R_iff {G : Geom} {a p q r : Point} : B p q r ↔ B (a.R p) (a.R q) (a.R r) := by
  constructor
  · exact btwn_R
  · intro h; rw [←double_reflect a p, ←double_reflect a q, ←double_reflect a r]
    exact btwn_R h

-- Satz 7.16
theorem E_R {G : Geom} {a p q r s : Point} :
  E p q r s → E (a.R p) (a.R q) (a.R r) (a.R s) :=
  fun h ↦  E_eucl (E_trans h.symm R_isometry) R_isometry

theorem E_R_iff {G : Geom} {a p q r s : Point} :
  E p q r s ↔ E (a.R p) (a.R q) (a.R r) (a.R s) := by
  constructor
  · exact E_R
  · intro h; rw [← double_reflect a p, ←double_reflect a q]
    rw [← double_reflect a r, ← double_reflect a s]; exact E_R h

-- Satz 7.17
theorem unique_M {G : Geom} {a b p p' : Point} : M p a p' → M p b p' → a = b := by
  intro ha ⟨hb1, hb2⟩; have ha' := ha; symm at ha
  rw [← aRp_q_iff_Mpaq] at ha ha'
  have h1 : E p' b (a.R p') (a.R b) := R_isometry
  rw [ha] at h1; have h2 : E p b p (a.R b) := E_trans hb2.lr h1
  have h3 : E p b (a.R p) (a.R b) := R_isometry
  rw [ha'] at h3; have h4 : E p' b p' (a.R b) := E_trans hb2.lr.symm h3
  have h5 : b = (a.R b) := eq_of_btwn_E hb1 h2 h4
  exact (R_eq_self_iff.mp h5.symm).symm

-- Satz 7.18
theorem unique_M' {G : Geom} {a b p : Point} : (a.R p = b.R p) → a = b :=
  fun h ↦ unique_M (Mpaq_of_aRp_q rfl) (h ▸ Mpaq_of_aRp_q (a := b) rfl)

-- Satz 7.19 : Different reflection maps don't commute
theorem R_M {G : Geom} {a p q r: Point} : M p q r ↔ M (a.R p) (a.R q) (a.R r) := by
  unfold M; rw [btwn_R_iff (a := a), E_R_iff]

theorem R_noncomm {G : Geom} {a b p : Point} :
  a.R (b.R p) = b.R (a.R p) → a = b := by
  intro LHS; generalize hp' : a.R p = p' at *
  rw [aRp_q_iff_Mpaq, R_M (a := b), double_reflect, double_reflect] at LHS
  rw [aRp_q_iff_Mpaq] at hp'; rw [←R_eq_self_iff]; symm
  exact unique_M hp' LHS

-- Satz 7.20
theorem Mamb_of_ne_col_Emamb {G : Geom} {a m b : Point} :
  a ≠ b → Col a m b → E m a m b → M a m b := by
  intro hab hcol hmamb; rcases hcol with h | h | h
  · exact ⟨h, hmamb⟩
  · exact absurd (narboux_lemma h hmamb.symm).symm hab
  · exact absurd (narboux_lemma h.symm hmamb) hab

-- Lemma 7.21
/-incredibly, if abcd is a quadrilateral so that a b and c are no collinear
and d is not b, then the diagonals ac and bd cross at their midpoints.-/

theorem central_symm_quad {G : Geom} {a b c d p : Point} :
¬ Col a b c → b ≠ d → E a b c d → E b c d a → Col a p c → Col b p d →
M a p c ∧ M b p d := by
  intro htri_abc hbd he1 he2 hcol1 hcol2
  have ⟨p', hE1⟩ := e3_of_col_eq hcol2.yz E_comm
  have hcol3 : Col b d p' := (col_of_col_e3 hcol2 hE1.yz).r
  have he3 := five_sgmt hbd hcol2.yz hE1 he1.lr he2.symm
  have he4 := five_sgmt hbd hcol2.yz hE1 he2 he1.symm.lr
  have hE2 : E3 a p c c p' a:= ⟨he3.lr, he4, E_comm⟩
  have hcol4 : Col c p' a := col_of_col_e3 hcol1 hE2
  have hne : Line a c ≠ Line b d := by
    intro h; have hb : b ∈ Line b d := (line_gen_pt_mem hbd).1
    rw [← h] at hb; exact htri_abc hb.2.yz
  have hac : a ≠ c := (dist_of_not_col htri_abc).2.2
  have hpp' : p = p' :=
    unique_isect_pt (line_is_line hbd) (line_is_line hac) hne.symm ⟨hbd, hcol2.yz⟩
    ⟨hac, hcol1.yz⟩ ⟨hbd, hcol3⟩ ⟨hac, hcol4.r⟩
  subst hpp'; constructor
  · exact Mamb_of_ne_col_Emamb hac hcol1 he3
  · exact Mamb_of_ne_col_Emamb hbd hcol2 hE1.2.2.lr

-- Lemma 7.22 Krippenlemma
theorem krippenlemma_wlog {G : Geom} {a1 a2 b1 b2 m1 m2 c : Point} (hlea : le c a1 c a2 ):
B a1 c a2 → B b1 c b2 → E c a1 c b1 → E c a2 c b2 → M a1 m1 b1 → M a2 m2 b2 → B m1 c m2 := by
  intro hb1 hb2 he1 he2 hm1 hm2; by_cases hca1 : c = a1
  · subst hca1; rw [E_id he1.symm] at *
    rw [midpt_triv.mp hm1] at *; exact btwn_refl
  by_cases hca2 : c = a2
  · subst hca2; exact absurd (le_triv hlea).symm hca1
  have hcb1 : c ≠ b1 := E_id_mt hca1 he1.symm
  have ⟨a, hb3, he3⟩ := sgmt_of_le hlea
  have hleb : le c b1 c b2 := le_of_le_E hlea he1 he2
  have ⟨b, hb4, he4⟩ := sgmt_of_le hleb
  have ha : c.R a2 = a := by
    rw [aRp_q_iff_Mpaq]; constructor
    · exact xyw_of_xyz_yzw_ne hb1.symm hb3 hca1
    · exact he3.symm
  have hb : c.R b2 = b := by
    rw[aRp_q_iff_Mpaq]; constructor
    · exact xyw_of_xyz_yzw_ne hb2.symm hb4 hcb1
    · exact he4.symm
  generalize hm : c.R m2 = m
  have hm3 := (R_M (a := c)).mp hm2
  rw [ha, hb, hm] at hm3
  have ⟨q, hq1, hq2⟩ := crossbar hb3.symm hb4.symm hm3.1
  have hqcm2 : B q c m2 := yzw_of_xyz_xzw hq1 (aRp_q_iff_Mpaq.mp hm).1.symm
  have he5 : E a1 a b1 b :=
    (sgmt_sub hb3.symm hb4.symm (E_trans (E_trans he3 he2) he4.symm).lr he1.lr).lr
  have hifs1 := inner_five_sgmt hb3 hb4 he1 he5 E_refl hm3.2.lr
  have hifs2 := inner_five_sgmt hq1.symm hq1.symm E_refl E_refl he1 hifs1.lr
  have hm4 : M a1 q b1 := ⟨hq2, hifs2⟩
  have hqm1 : q = m1 := unique_M hm4 hm1; rwa [←hqm1]

theorem krippenlemma {G : Geom} {a1 a2 b1 b2 m1 m2 c : Point} :
B a1 c a2 → B b1 c b2 → E c a1 c b1 → E c a2 c b2 → M a1 m1 b1 → M a2 m2 b2 → B m1 c m2 := by
  intro hb1 hb2 he1 he2 hm1 hm2; rcases (le_total c a1 c a2) with h | h
  · exact krippenlemma_wlog h hb1 hb2 he1 he2 hm1 hm2
  · exact (krippenlemma_wlog h hb1.symm hb2.symm he2 he1 hm2 hm1).symm

-- Satz 7.23

theorem Mamb_of_cacb {G : Geom} {a b c : Point} : E c a c b → ∃ m, M a m b := by
  intro hcacb; by_cases h: Col a c b
  · rcases h with h' | h' | h'
    · exact ⟨c, h', hcacb⟩
    · have hba : b = a := narboux_lemma h' hcacb.symm
      subst hba; exact ⟨b, midpt_triv.mpr rfl⟩
    · have hab : a = b := narboux_lemma h'.symm hcacb
      subst hab; exact ⟨a, midpt_triv.mpr rfl⟩
  have ⟨p, hp1, hap⟩ := sgmt_const' c a -- p lies on Line c a, beyond a
  have ⟨q, hq1, hq2⟩ := sgmt_const c b a p -- q lies on Line c b, beyond b
  have ⟨r, hr1, hr2⟩ := inner_pasch hq1.symm hp1.symm
  have ⟨x, hx1, hx2⟩ := inner_pasch hp1 hr1
  have hca : c ≠ a := by intro h'; subst h'; exact h col_triv_xxy
  have hafs := outer_five_sgmt hca hp1 hq1 hcacb hq2.symm hcacb.symm E_comm
  have ⟨r', hr'1, hr'2, hr'3⟩ := sgmt_split hr1 hafs.lr
  have hifs1 := inner_five_sgmt hr1 hr'1 hr'2 hr'3 E_comm hq2.lr.symm
  have hifs2 := inner_five_sgmt hr1 hr'1 hr'2 hr'3 hq2 E_comm
  have hcol_brp : Col b r p := hr1.col
  have hcol_br'p : Col b r' p := col_of_col_e3 hr2.col ⟨hifs1.lr, hifs2, hafs.lr.symm⟩
  have hcol_arq := hr2.col
  have hcol_ar'q := hr'1.col
  have haq : a ≠ q := by intro h'; subst h'; exact absurd hq1.col.r h
  have hbp : b ≠ p := by intro h'; subst h'; exact absurd hp1.col.xy h
  have hL1 : r ∈ Line a q := ⟨haq, hcol_arq.yz⟩
  have hL2 : r' ∈ Line a q := ⟨haq, hcol_ar'q.yz⟩
  have hL3 : r ∈ Line b p := ⟨hbp, hcol_brp.yz⟩
  have hL4 : r' ∈ Line b p := ⟨hbp, hcol_br'p.yz⟩
  have h' : r = r' := by
      refine unique_isect_pt (?_) (?_) (?_) hL1 hL3 hL2 hL4
      ·   exact line_is_line haq
      ·   exact line_is_line hbp
      ·   intro h'; suffices hacb : Col a c b from (h hacb)
          rw [col_iff_on_same_line]
          refine ⟨Line a p, line_is_line hap, ?_, ?_, ?_⟩
          · exact (line_gen_pt_mem hap).1
          · exact ⟨hap, hp1.col.l⟩
          · have ⟨hb, hp⟩ := line_gen_pt_mem hbp
            rw [←h'] at hb hp
            have hleq : Line a q = Line a p := by
              exact line_eq (Ne.symm hap) hp
            rwa [← hleq]
  subst h'; refine ⟨x, hx1, ?_⟩
  exact inner_five_sgmt hx2 hx2 E_refl E_refl hifs1 hcacb

end Geom
end Ch7
