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
        exact hneAB <| line_incid_unique (ne_of_isline hB) (Line a b) (Line c x)
          hA hB hcA hcB hxA hxB
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
  sorry
  /- what's left : Show L(yz) = L(ab)
  -/


theorem unique_foot_of_perp {G : Geom} {a b c x y: Point} : ¬ (Col a b c) →
Col a b x → Line a b ⟂ Line c x → Col a b y → Line a b ⟂ Line c y → x = y := by
  intro hncol hcol1 hperp1 hcol2 hperp2; have hab : a ≠ b := (dist_of_not_col hncol).1
  by_cases hxy : x = y; exact hxy; change x ≠ y at hxy
  rw [dropped_perp_iff hab hcol1 hcol2 hxy.symm] at hperp1
  rw [dropped_perp_iff hab hcol2 hcol1 hxy] at hperp2
  exact eq_of_Rabc_Racb hperp1.2 hperp2.2



end Geom
end Ch8
