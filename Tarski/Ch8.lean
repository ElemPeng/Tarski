import Tarski.Ch7

section Ch8
namespace Geom
-- Def 8.1 : Right angles
/- ∠ abc is a right angle if a is equidistant from c and the reflection of
c through the point b. (insert picture of isosceles triangle a c c' with
base midpoint b here.)
-/
def Right {G : Geom} (a b c : Point) := E a c a (b.R c)

-- Satz 8.2
@[symm] theorem right_symm {G : Geom} {a b c : Point} : Right a b c → Right c b a := by
  intro h; have h1 : E a (b.R c) (b.R a) c := by
    conv in (occs := 2) c => rw [←double_reflect b c]
    exact R_isometry
  unfold Right at h ⊢; exact (E_trans h h1).lr

theorem Right.symm {G : Geom} {a b c : Point} (h : Right a b c) : Right c b a := right_symm h
-- Satz 8.3
/-  if a ≠ b ∧ ∠abc is a right angle, then so is ∠a'bc for any point
    a' on Line a b
-/
theorem right_extend {G : Geom} {a b c a' : Point} : Right a b c → a ≠ b → Col a b a' →
  Right a' b c := by
  intro hr1 hne1 hcol1; unfold Right at hr1 ⊢
  apply E_of_ne_col_E hne1 hcol1 hr1 (?_)
  conv in (occs := 2) b => rw [←R_self b]
  exact R_isometry

-- Satz 8.4
theorem right_abRc_of_Rabc {G : Geom} {a b c : Point} : Right a b c → Right a b (b.R c) := by
  intro h; unfold Right at h ⊢
  conv in (b.R (b.R c)) => rw [double_reflect b c]
  exact h.symm

-- Satz 8.5
theorem right_abb {G : Geom} {a b : Point} : Right a b b := by
  unfold Right; rw [R_self b]; exact E_refl

theorem right_aab {G : Geom} {a b : Point} : Right a a b := (right_abb).symm

-- Satt 8.6
/- This is saying, more or less, that if you drop a perpendicular from a point
c to the line a a', then it has a unique foot b-/
theorem eq_of_Rabc_Ra'bc_aca' {G : Geom} {a a' b c : Point} :
Right a b c → Right a' b c → B a c a' → b = c := by
  intro hr1 hr2 hb1; unfold Right at hr1 hr2
  have heq : c = b.R c := eq_of_btwn_E hb1 hr1 hr2
  symm at heq ⊢; rwa [← R_eq_self_iff]

-- Satz 8.7
theorem eq_of_Rabc_Racb {G : Geom} {a b c : Point} :
Right a b c → Right a c b → b = c := by
  intro hr1 hr2; generalize hc' : b.R c = c'; generalize ha' : c.R a = a'
  have hcol1 : Col b c c' := by rw [aRp_q_iff_Mpaq] at hc'; exact hc'.1.col.xy
  apply Classical.byContradiction; intro hbc
  have hr3 : Right a c c' := right_symm <| right_extend (hr2.symm) (hbc) hcol1
  have he1 : E a c a' c := by rw [aRp_q_iff_Mpaq] at ha'; exact ha'.2.lr
  have he2 : E a c' a' c' := by rw [←ha']; apply E_flip_both; exact hr3.symm
  have he3 : E a c a c' := by rwa [←hc']
  have hr4 : Right a' b c := by
    unfold Right; rw [hc']; exact E_trans he1.symm <| E_trans he3 he2
  have hb1 : B a c a' := by rw [aRp_q_iff_Mpaq] at ha'; exact ha'.1
  exact hbc <| eq_of_Rabc_Ra'bc_aca' hr1 hr4 hb1

-- Satz 8.8
theorem eq_of_Raba {G : Geom} {a b : Point} : Right a b a → a = b :=
  fun h ↦ (eq_of_Rabc_Racb h right_abb.symm).symm

-- Satz 8.9
theorem eq_or_eq_of_right_col {G : Geom} {a b c : Point} :
Right a b c → Col a b c → a = b ∨ c = b := by
  intro hr hc; rw [Classical.or_iff_not_imp_left]; intro hab
  have hr2 : Right c b c := right_extend hr hab hc
  exact eq_of_Raba hr2

-- Satz 8.10 -- basically side side side but only for right triangles
theorem right_of_right_E3 {G : Geom} {a b c a' b' c' : Point} :
Right a b c → E3 a b c a' b' c' → Right a' b' c' := by
  intro hr1 ⟨he1, he2, he3⟩; by_cases hbc : b = c
  · subst hbc; have hbc' : b' = c' := E_id he2.symm; subst hbc'
    exact right_abb
  have hbc' : b' ≠ c' := E_id_mt hbc he2.symm; change b ≠ c at hbc
  generalize hd : b.R c = d; generalize hd' : b'.R c' = d'
  rw [aRp_q_iff_Mpaq] at hd hd'
  have he4 := E_trans (E_trans hd.2.symm he2) hd'.2
  have hafs := outer_five_sgmt hbc.symm hd.1 hd'.1 he2.lr he4 he3.lr he1.lr
  rw [← aRp_q_iff_Mpaq] at hd hd'; unfold Right at hr1 ⊢
  subst hd hd'; exact E_trans (E_trans he3.symm hr1) hafs.lr

-- Def 8.11
def PSet.perp_at_x {G : Geom} (A A' : PSet G) (x : Point) :=
IsLine A ∧ IsLine A' ∧ x ∈ A ∧ x ∈ A' ∧ ∀ u v : Point, (u ∈ A → v ∈ A' → Right u x v)

notation:80 A:81 " ⟂[" x "] " B:81 => PSet.perp_at_x A B x

example {G : Geom} (A B : PSet G) (x : Point) :
  A ⟂[x] B ↔ A.perp_at_x B x := by rfl

def PSet.perp {G : Geom} (A A' : PSet G) := ∃ x : Point, A.perp_at_x A' x

infix:80 " ⟂ " => PSet.perp
/- SST has another notation ab ⟂ cd for Line ab ⟂ Line cd but i'll just
write Line ab and Line cd
-/

-- Satz 8.12
@[symm] theorem perpx_symm {G : Geom} {A B : PSet G} {x : Point} : (A ⟂[x] B) → (B ⟂[x] A) :=
  fun ⟨hA, hB, hxA, hxB, hxR⟩ ↦ ⟨hB, hA, hxB, hxA, fun u v hu hv ↦ (hxR v u hv hu).symm⟩

theorem PSet.perp_at_x.symm {G : Geom} {A B : PSet G} {x : Point} (h : A ⟂[x] B) :
  B ⟂[x] A := perpx_symm h

@[symm] theorem perp_symm {G : Geom} {A B : PSet G} : A ⟂ B → B ⟂ A :=
fun ⟨x, hx⟩ ↦ ⟨x, hx.symm⟩

theorem perp.symm {G : Geom} {A B : PSet G} (h : A ⟂ B) : B ⟂ A := perp_symm h

-- Satz 8.13 : perpendicular lines form nontrivial right angles

theorem nontriv_of_perpx {G : Geom} {A B : PSet G} {x : Point} : (A ⟂[x] B) →
  IsLine A ∧ IsLine B ∧ x ∈ A ∧ x ∈ B ∧ (∃ u v : Point,
  u ∈ A ∧ v ∈ B ∧ u ≠ x ∧ v ≠ x ∧ Right u x v) := by
  intro ⟨hA, hB, hxA, hxB, hxR⟩; refine ⟨hA, hB, hxA, hxB, ?_⟩
  have ⟨u, hux, huA⟩ := another_pt_on_line hA hxA
  have ⟨v, hvx, hvB⟩ := another_pt_on_line hB hxB
  refine ⟨u, v, huA, hvB, hux, hvx, hxR u v huA hvB⟩

theorem perpx_of_nontriv {G : Geom} {A B : PSet G} {x : Point} :
IsLine A → IsLine B → x ∈ A → x ∈ B → (∃ u v : Point,
  u ∈ A ∧ v ∈ B ∧ u ≠ x ∧ v ≠ x ∧ Right u x v) → (A ⟂[x] B) := by
  intro hA hB hxA hxB ⟨u, v, huA, hvB, hux, hvx, hR⟩
  refine ⟨hA, hB, hxA, hxB, ?_⟩; intro u' v' hu'A hv'B
  have h' : Right u' x v := right_extend hR hux <|
  col_iff_on_same_line.mpr ⟨A, hA, huA, hxA, hu'A⟩; symm at h' ⊢
  exact right_extend h' hvx <| col_iff_on_same_line.mpr ⟨B, hB, hvB, hxB, hv'B⟩

theorem perpx_iff_nontriv {G : Geom} {A B : PSet G} {x : Point} : (A ⟂[x] B) ↔
  IsLine A ∧ IsLine B ∧ x ∈ A ∧ x ∈ B ∧ (∃ u v : Point,
  u ∈ A ∧ v ∈ B ∧ u ≠ x ∧ v ≠ x ∧ Right u x v) := by
  constructor
  · exact nontriv_of_perpx
  · exact fun ⟨hA, hB, hxA, hxB, hE⟩ ↦ perpx_of_nontriv hA hB hxA hxB hE

-- Satz 8.14i
theorem ne_of_perp {G : Geom} {A B : PSet G} : A ⟂ B → A ≠ B := by
  intro ⟨x, ⟨hA, hB, hxA, hxB, huv⟩⟩ hAB
  have ⟨u, hux, huA⟩ := another_pt_on_line hA hxA
  have ⟨v, hvx, hvB⟩ := another_pt_on_line hB hxB
  have hR := huv u v huA hvB
  subst hAB; have hcol : Col u x v := by
    rw [col_iff_on_same_line]; exact ⟨A, hA, huA, hxA, hvB⟩
  have h_or := eq_or_eq_of_right_col hR hcol
  exact hvx <| Or.resolve_left h_or hux

-- Satz 8.14ii

theorem perpx_iff_perp_isectx {G : Geom} {A B : PSet G} {x : Point} :
   (A ⟂[x] B) ↔ (A ⟂ B ∧ x.Is A B) := by
    constructor
    · intro ⟨hA, hB, hxA, hxB, huv⟩
      have hperp : A ⟂ B := ⟨x, hA, hB, hxA, hxB, huv⟩
      exact ⟨hperp, ⟨hA, hB, ne_of_perp hperp, hxA, hxB⟩⟩
    · intro ⟨⟨y, hA, hB, hyA, hyB, huv⟩, ⟨_, _, _, hxA, hxB⟩⟩
      have hxy : x = y := eq_of_Raba (huv x x hxA hxB) --- hah!
      subst hxy; exact ⟨hA, hB, hyA, hyB, huv⟩

-- Satz 8.14iii
theorem unique_of_perpx {G : Geom} {A B : PSet G} {x y : Point} :
  (A ⟂[x] B) → (A ⟂[y] B) → x = y :=
  fun ⟨_, _, hxA, hxB, _⟩ ⟨_, _, _, _, huyb⟩ ↦ eq_of_Raba (huyb x x hxA hxB)
  --- hah!!

--Satz 8.15
theorem perp_iff_perpx_of_col_abx_ne {G : Geom} {a b c x : Point} :
a ≠ b → Col a b x → ( Line a b ⟂ Line c x ↔ Line a b ⟂[x] Line c x) := by
  intro hne hcol; constructor
  · intro hperp; rw [perpx_iff_perp_isectx]; refine ⟨hperp, ?_⟩
    have ⟨y, hA, hB, hxA, hxB, huvx⟩ := hperp
    have hcx : c ≠ x := ne_of_isline hB
    have hxy : x = y := unique_isect_pt hA hB (ne_of_perp hperp)
      ⟨hne, hcol⟩ (line_pt_mem_right hcx) hxA hxB
    subst hxy; exact ⟨hA, hB, ne_of_perp hperp, hxA, hxB⟩
  · intro h; rw [perpx_iff_perp_isectx] at h; exact h.1

-- Satz 8.16 (no idea what to call this one lol)
/- it's saying that if the line a b is perpendicular to the line c x,
x lies in Line a b and u is any point on Line a b besides x,
then c does not lie on Line a b, and the points c x and b form a
right angle; a better way to think about it is that it's saying that all
you need to show ab ⟂ cx is to show that (1) x ∈ ab, (2) there is some point
u ∈ ab so that u ≠ x (3) ∠cxu is a right angle and (4) c ∉ ab
-/
theorem dropped_perp_iff {G : Geom} {a b c x u : Point} : a ≠ b → Col a b x →
  Col a b u → u ≠ x → (Line a b ⟂ Line c x ↔ (¬ Col a b c ∧ Right c x u)) := by
    intro hab hcol1 hcol2 hux; constructor
    · intro hperp; have hxA : x ∈ Line a b := ⟨hab, hcol1⟩
      have hneAB : Line a b ≠ Line c x := ne_of_perp hperp
      have ⟨y, hA, hB, hyA, hyB, huyv⟩ := hperp;
      have hcx : c ≠ x := ne_of_isline hB
      have hxB : x ∈ Line c x := (line_pt_mem_right hcx);  constructor
      · intro hcol3; have hcA : c ∈ Line a b := ⟨hab, hcol3⟩
        have hcB : c ∈ Line c x := line_pt_mem_left hcx
        exact hneAB <| line_incid_unique (ne_of_isline hB) hA hB hcA hcB hxA hxB
      · have hxy : x = y := eq_of_Raba <| huyv x x hxA hxB
        subst hxy; exact (huyv u c ⟨hab, hcol2⟩ (line_pt_mem_left hcx)).symm
    · intro ⟨hncol, hR⟩; have hcx : c ≠ x := by intro h'; subst h'; exact hncol hcol1
      refine ⟨x, ?_⟩; rw [perpx_iff_nontriv]
      refine ⟨line_is_line hab, line_is_line hcx, ⟨hab, hcol1⟩, line_pt_mem_right hcx, ?_⟩
      exact ⟨u, c, ⟨hab, hcol2⟩, line_pt_mem_left hcx, hux, hcx, hR.symm⟩

-- Def 8.17
/- If ab ⟂ cx and Col abc, then Line cx is the perpendicular to Line ab at x,
or the perpendicular dropped from c with foot x. -/

-- Satz 8.18 (Lotsatz : Plumb-line Theorem)

theorem perp_exist_of_ext_pt {G : Geom} {a b c : Point} : ¬ (Col a b c) →
∃ x, (Col a b x ∧ Line a b ⟂ Line c x) := by
  intro hncol; have ⟨y, hy1, hy2⟩ := sgmt_const b a a c
  have ⟨p, hp⟩ := Mamb_of_cacb hy2
  have hr1 : Right a p y := by rw [← aRp_q_iff_Mpaq] at hp; rwa [←hp] at hy2
  have ⟨z, hz1, hz2⟩ := sgmt_const a y y p; have ⟨q, hq1, hq2⟩ := sgmt_const p y y a
  generalize hq' : z.R q = q'; have ⟨c', hc'1, hc'2⟩ := sgmt_const q' y y c
  have hay : a ≠ y := E_id_mt (dist_xz_of_not_col hncol) hy2
  have hafs := outer_five_sgmt hay hz1 hq1.symm hq2.symm.lr hz2 E_comm hq2
  have hE1 : E3 a p y q z y := ⟨hafs.symm.lr,hz2.symm.lr,hq2.lr.symm⟩
  -- Setting up the Krippenlemma
  have hr2 : Right q z y := right_of_right_E3 hr1 hE1
  symm at hr2; unfold Right at hr2; rw [hq'] at hr2
  have ⟨x, hx1⟩ : ∃ x, M c x c' := Mamb_of_cacb hc'2.symm
  have hM1 : M q z q' := Mpaq_of_aRp_q hq'
  have hqy : q ≠ y := E_id_mt hay hq2.lr; have hq'y : q' ≠ y := E_id_mt hqy hr2.symm.lr
  by_cases hpy : p = y
  · subst hpy; have ⟨h1, h2⟩ := hp; have hpc : p = c := E_id h2.symm; subst hpc
    exact absurd hy1.col.xy hncol
  have hb1 : B q y c := xyw_of_xyz_yzw_ne hq1.symm hp.1 (Ne.symm hpy)
  have hzyx := krippenlemma hb1 hc'1 hr2 hc'2.symm hM1 hx1
  -- need to show Line a b = Line y z
  have hab : a ≠ b := dist_xy_of_not_col hncol; have hA := line_is_line (hab)
  have hyz : y ≠ z := E_id_mt hpy hz2.r; have hB := line_is_line (hyz)
  have hAB : Line a b = Line y z := line_incid_unique hay hA hB (line_pt_mem_left hab) ⟨hyz, hz1.col.l⟩
     ⟨hab, hy1.col.xy⟩ (line_pt_mem_left hyz)
  have hxB : x ∈ Line y z := ⟨hyz, hzyx.col.xy⟩;
  have hxA : x ∈ Line a b := by rw [hAB]; exact hxB
  have hcx : c ≠ x := by intro h; subst h; exact hncol hxA.2
  have hxC : x ∈ Line c x := line_pt_mem_right hcx
  rw [hAB]; refine ⟨x, hxA.2, ⟨x,?_⟩⟩
  rw [perpx_iff_nontriv]; refine ⟨hB, line_is_line hcx, hxB, hxC,?_⟩
  refine ⟨y, c, line_pt_mem_left hyz, line_pt_mem_left hcx , ?_⟩
  have hyx : y ≠ x := by -- if y = x the whole cradle collapses
    intro h; subst h; have hyc' : y ≠ c' := E_id_mt hcx.symm hc'2
    have hb'1 : B y q c' ∨ B y c' q :=
      yzw_or_ywz_of_ne_xyz_xyw hcx hb1.symm hx1.1
    have hb'2 : B q y q' := by
      rcases hb'1 with h'' | h''
      · exact yzw_of_xyz_xzw h''.symm hc'1.symm
      · exact xzw_of_xyz_yzw_ne h''.symm hc'1.symm hyc'.symm
    have hM3 : M q y q' := ⟨hb'2, hr2⟩
    exact hyz <| unique_M hM3 hM1
  refine ⟨hyx, hcx, ?_⟩; unfold Right; rw [← aRp_q_iff_Mpaq] at hx1
  rw [hx1]; exact hc'2.symm


theorem unique_foot_of_perp {G : Geom} {a b c x y: Point} : ¬ (Col a b c) →
Col a b x → Line a b ⟂ Line c x → Col a b y → Line a b ⟂ Line c y → x = y := by
  intro hncol hcol1 hperp1 hcol2 hperp2; have hab : a ≠ b := (dist_of_not_col hncol).1
  by_cases hxy : x = y; exact hxy; change x ≠ y at hxy
  rw [dropped_perp_iff hab hcol1 hcol2 hxy.symm] at hperp1
  rw [dropped_perp_iff hab hcol2 hcol1 hxy] at hperp2
  exact eq_of_Rabc_Racb hperp1.2 hperp2.2

-- Lemma 8.20
theorem lemma_8_20 {G : Geom} {a b c p : Point} : Right a b c →
M (a.R c) p (b.R c) → (Right b a p ∧ (b ≠ c → a ≠ p)) := by
  intro hr1 hM1; generalize hd : b.R c = d
  generalize hb' : a.R b = b'; generalize hc' : a.R c = c'
  generalize hd' : a.R d = d'; generalize hp' : a.R p = p'
  rw [hc', hd] at hM1; have ⟨hb1, he1⟩ := hM1
  have ha : a.R a = a := R_self a; by_cases hab : a = b
  -- if a = b the whole thing collapses
  · subst hab; refine ⟨right_aab, ?_⟩; intro hac hap
    subst hap; rw [ha] at hb' hp'; subst hp'
    rw [hc'] at hd; subst hd; have hac' : c' = a := btwn_id hb1
    subst hac'; rw [R_comm] at hc' ha; exact hac (ha.symm ▸ hc'.symm)
  have hr2 : Right b' b c := by
    rw [aRp_q_iff_Mpaq] at hb'; exact right_extend hr1 hab hb'.1.col.xy
  have hd'' : b'.R c' = d' := by
      rw [aRp_q_iff_Mpaq] at hd ⊢; simp [← hb', ← hc', ← hd']; rwa [← R_M]
  have hr3 : Right b b' c' := by
    unfold Right at hr2; rw [hd, E_R_iff (a := a), hc', hd', ←(R_comm.mp hb')] at hr2
    rwa [←hd''] at hr2
  have he2 : E b c' b d' := by unfold Right at hr3; rwa [hd''] at hr3
  have hb3 : B c' p d := hM1.1; have hb4 : B c p' d' := by
    rwa [(R_comm.mp hc'), ← hp', ← hd', ← btwn_R_iff]
  have hafs : E p b p' b := by
    refine inner_five_sgmt hb3 hb4.symm ?_ ?_ ?_ ?_
    · rw [←hd', ←hp']; exact E_trans he1.lr R_isometry
    · rw [← hp', (R_comm.mp hc')]; exact E_trans he1.symm R_isometry
    · unfold Right at hr3; rwa [←hd'', E_flip_both_iff]
    · rw [E_symm_iff, E_flip_both_iff]; rw [aRp_q_iff_Mpaq] at hd
      exact hd.2
  rw [←hp'] at hafs; refine ⟨hafs.lr, ?_⟩; apply mt; intro h
  -- to show b ≠ c → a ≠ p we show a = p → b = c
  subst h; rw [ha] at hp'; subst hp'; have hcd : c = d := by
    rw [← aRp_q_iff_Mpaq] at hM1; exact hM1 ▸ (R_comm.mp hc')
  subst hcd; symm; rwa [R_eq_self_iff] at hd

  -- Satz 8.21
  /- the beginning of plane separation
  -- note that Line a b ⟂ Line p a forces p ≠ a because it forces
    IsLine Line p a
  -/
  theorem plane_sep_perp {G : Geom} {a b c : Point} : ¬ Col a b c → ∃ p t,
    (Line a b ⟂ Line p a ∧ Col a b t ∧ B c t p) := by
    intro hncol; have hab : a ≠ b := dist_xy_of_not_col hncol
    have ⟨x, hx1, hx2⟩ := perp_exist_of_ext_pt hncol
    generalize hd : x.R c = d; generalize hc' : a.R c = c'
    by_cases hax : a = x
    · subst hax; refine ⟨c', a, ?_, col_triv_xyx, ?_⟩
      · have hac : a ≠ c := dist_xz_of_not_col hncol
        rw [aRp_q_iff_Mpaq] at hc'
        have hac' : a ≠ c' := E_id_mt hac hc'.2.symm
        have heq : Line c a = Line c' a := line_incid_unique hac
          (line_is_line hac.symm) (line_is_line hac'.symm) (line_pt_mem_right hac.symm)
          (line_pt_mem_right hac'.symm) (line_pt_mem_left hac.symm)
          ⟨hac'.symm, hc'.1.col.xz⟩
        rwa [heq] at hx2
      · exact (aRp_q_iff_Mpaq.mp hc').1
    rw [dropped_perp_iff hab hx1 col_triv_xyx hax] at hx2
    have ⟨_, hr2⟩ := hx2
    symm at hr2; unfold Right at hr2
    have ⟨hb1, he1⟩ := Mpaq_of_aRp_q hc'
    have he2 := E_eucl he1 hr2; rw [←hc'] at he2
    have ⟨p, hp⟩ := Mamb_of_cacb he2
    have ⟨h1, h2⟩ := lemma_8_20 hx2.2.symm hp
    have ⟨hb2, he3⟩ := Mpaq_of_aRp_q hd
    rw [hc', hd] at hp
    have ⟨t, ht1, ht2⟩ := crossbar hb2.symm hb1.symm hp.1.symm
    have hxc : x ≠ c := by intro h; subst h; exact hncol hx1
    have hap : a ≠ p := h2 hxc
    refine ⟨p, t, ?_, ?_, ht1.symm⟩
    · rw [dropped_perp_iff hab col_triv_xyx hx1 (Ne.symm hax)]
      refine ⟨?_, h1.symm⟩
      have hr3 : Right b a p := right_extend h1 (Ne.symm hax) hx1.r
      intro hcol; have h := (eq_or_eq_of_right_col) hr3 hcol.xy
      exact hap.symm <| Or.resolve_left h hab.symm
    · exact col_iff_on_same_line.mpr
        ⟨Line a x, line_is_line hax, line_pt_mem_left hax, ⟨hax, hx1.yz⟩, ⟨hax, ht2.col.r⟩⟩

  theorem plane_sep_perp' {G : Geom} {a b c : Point} : a ≠ b → ∃ p t,
    (Line a b ⟂ Line p a ∧ Col a b t ∧ B c t p) := by
    intro hab; by_cases hcol : Col a b c
    · have ⟨c', hc'⟩ := ext_of_Lab hab; change ¬ (a ≠ b ∧ Col a b c') at hc'
      rw [Classical.not_and_iff_not_or_not] at hc'
      have hncol : ¬ Col a b c' := Or.neg_resolve_left hc' hab
      have ⟨p, _, hperp, _⟩ := plane_sep_perp hncol
      refine ⟨p, c, hperp, hcol, btwn_refl⟩
    exact plane_sep_perp hcol




end Geom
end Ch8
