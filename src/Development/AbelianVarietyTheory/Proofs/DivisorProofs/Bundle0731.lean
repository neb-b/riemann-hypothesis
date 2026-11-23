module

public import Mathlib
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.LevelLossDegreeBounds
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FockDegreeGapBound
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0715
public import Development.AbelianVarietyTheory.Definitions.Divisors.ToRingActOpOfRingAct
public import Development.AbelianVarietyTheory.Definitions.Divisors.NonemptyHomFixRepTrivial
public import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.IsGaloisCover
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.BCTools
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0007
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0024
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0021
public import Development.AbelianVarietyTheory.Definitions.Divisors.DatumOfIsIntegersLattice
public import Formalism.LocalToGlobal.TorsionIntegrality.EisensteinTranslationProducts.MulStableIntegral
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.IsDiscreteValuationRingValuationSubringAtPrime
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.AddMonoidHomEqZeroOfEventually
public import Development.AbelianVarietyTheory.Definitions.Divisors.OneMemH0WeightZero
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.NotIsCompactUnivFv
public import GroundTheory.GlobalFields.IdeleGroups.IdeleNorms

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.NuAbsPlaceFine
section
open Formalism.BasicNotions Formalism.BasicNotions.DV Formalism.MainNotions Formalism.MainNotions.G NumberField GlobalTheory.IndefiniteRowSideFullHecke.LevelLossDegreeBounds

namespace GlobalTheory.FockDegreeFine

open Classical GlobalTheory.FockDegreeGap

variable {D : D7} {L : SizeData₂ D}

noncomputable def topConst (D : D7) (c : ℝ) (τ : D.what₂.Tau) : ℝ :=
  ∑ t : D.host.TT, if (D.eTau τ : D.R.GG) = D.R.tau1 t then c else 0

theorem topConst_top (c : ℝ) {τ : D.what₂.Tau} {t : D.host.TT}
    (h : (D.eTau τ : D.R.GG) = D.R.tau1 t) : topConst D c τ = c := by
  unfold topConst
  rw [Finset.sum_eq_single t, if_pos h]
  · intro s _ hs
    exact if_neg fun h' => hs (Subtype.ext (tau1_injective (h'.symm.trans h)))
  · simp

theorem topConst_nonneg {c : ℝ} (hc : 0 ≤ c) (τ : D.what₂.Tau) : 0 ≤ topConst D c τ := by
  unfold topConst
  refine Finset.sum_nonneg fun t _ => ?_
  split_ifs
  · exact hc
  · exact le_rfl

theorem sum_topConst (c : ℝ) : ∑ τ, topConst D c τ = (D.host.TT.card : ℝ) * c := by
  unfold topConst
  rw [Finset.sum_comm]
  have : ∀ t ∈ (Finset.univ : Finset D.host.TT),
      (∑ τ : D.what₂.Tau, if (D.eTau τ : D.R.GG) = D.R.tau1 t then c else 0) = c := by
    intro t _
    rw [Finset.sum_eq_single (D.eTau.symm ⟨D.R.tau1 t, (Formalism.HC.Frame.mem_Psi_iff _).2 rfl⟩)]
    · simp
    · intro τ _ hτ
      refine if_neg fun h' => hτ ?_
      rw [Equiv.eq_symm_apply]
      exact Subtype.ext h'
    · simp
  rw [Finset.sum_congr rfl this]
  simp

noncomputable def offWt (D : D7) (j : ℕ) (τ : D.what₂.Tau) : ℝ :=
  if τ ∉ topsOf D.host D.eTau then wj D j τ else 0

theorem mem_topsOf (τ : D.what₂.Tau) :
    τ ∈ topsOf D.host D.eTau ↔ (D.eTau τ : D.R.GG) ∈ D.host.topPlaces := by
  unfold topsOf
  simp

theorem sum_offWt (j : ℕ) : ∑ τ, offWt D j τ = sizeOffTops D j := by
  unfold offWt sizeOffTops
  rw [Finset.sum_filter]

theorem end_rows (P : ParameterChoice' D L) (u : D.what₂.Word) (i : ℕ) (hi : i < D.R.m) (τ : D.what₂.Tau) :
    |nuRow D u (i + 1) τ 0 + nuRow D u (i + 1) τ (D.R.k - 1) - wj D (i + 1) τ -
        (topWt L τ + offWt D (i + 1) τ)| ≤
      4 * L.Sc + 2 * D.R.N D.R.m + 1 + L.etaSz + topConst D (L.sc.b' / L.sc.x) τ := by
  have hk : 5 ≤ D.R.k := by have := D.R.m_add_three_le_k; have := D.R.two_le_m; omega
  have hk0 : 0 < D.R.k := by omega
  have hS := L.Sc_pos
  have he := L.etaSz_pos
  have hNm : (0 : ℝ) ≤ D.R.N D.R.m := Nat.cast_nonneg _
  have hc : 0 ≤ L.sc.b' / L.sc.x :=
    div_nonneg (GlobalTheory.HCEntries.b'_pos L).le (by linarith [L.sc.one_lt_alt])
  obtain ⟨a1, a2⟩ := head_row u i hi τ 0 hk0
  obtain ⟨b1, b2⟩ := head_row u i hi τ (D.R.k - 1) (by omega)
  rw [D.hcW_first u τ hk0] at a1 a2
  rw [D.hcW_last u τ hk0] at b1 b2
  rw [abs_le]
  unfold offWt
  by_cases ha : (D.eTau τ : D.R.GG) ∈ D.host.topPlaces
  · obtain ⟨t, ht⟩ := GlobalTheory.HCEntries.exists_top ha
    rw [topWt_top L ht, topConst_top _ ht, if_neg (not_not.2 ((mem_topsOf τ).2 ha))]
    rw [(L.top_u τ t hk0 ht).1] at a1 a2
    rw [(L.top_u τ t hk0 ht).2] at b1 b2
    obtain ⟨c1, c2⟩ := L.win_top (i + 1) (by omega) hi τ t ht
    constructor <;> linarith
  · rw [topWt_off L ha, if_pos (fun h => ha ((mem_topsOf τ).1 h))]
    rw [P.uk_extreme τ (by omega) ha] at b1 b2
    have h0 := topConst_nonneg hc τ
    have h1 := P.cloud_place_bound τ (by omega) ha
    have h2 := L.cloud_v τ ⟨0, by omega⟩
    have h3 : (((D.hc τ).v ⟨0, by omega⟩ : ℚ) : ℝ) < (((D.hc τ).u ⟨0, hk0⟩ : ℚ) : ℝ) := by
      exact_mod_cast (D.hc τ).u_gt_v ⟨0, by omega⟩
    have h4 := L.cloud_v τ ⟨D.R.k - 2, by omega⟩
    push_cast at h1 b1 b2
    constructor <;> linarith [h2.1, h2.2, h4.1, h4.2]

theorem nuAbs_place_fine (P : ParameterChoice' D L) (u : D.what₂.Word) (i : ℕ) (hi : i < D.R.m) (τ : D.what₂.Tau) :
    |nuAbs D u (i + 1) τ - ((D.R.k : ℝ) - 1) * wj D (i + 1) τ - (topWt L τ + offWt D (i + 1) τ)| ≤
      D.R.k * (L.Sc + D.R.N D.R.m) + D.R.m * ((D.R.t : ℝ) + 1) * (2 * L.etaSz) +
        (4 * L.Sc + 2 * D.R.N D.R.m + 1 + L.etaSz + topConst D (L.sc.b' / L.sc.x) τ) := by
  obtain ⟨n, hn⟩ : ∃ n, D.R.k = n + 2 := ⟨D.R.k - 2, by have := D.R.m_add_three_le_k; omega⟩
  have hN : D.R.N (i + 1 - 1) = n + 1 + 1 + i * (D.R.t + 1) := by unfold Ranks.N; rw [hn]; rfl
  have hS := L.Sc_pos
  have he := L.etaSz_pos
  have hNm : (0 : ℝ) ≤ D.R.N D.R.m := Nat.cast_nonneg _
  have hkn : (D.R.k : ℝ) = n + 2 := by exact_mod_cast hn
  have s0 := abs_le.1 (end_rows P u i hi τ)
  rw [show D.R.k - 1 = n + 1 by omega] at s0
  unfold nuAbs
  rw [hN, Finset.sum_range_add, Finset.sum_range_succ, Finset.sum_range_succ']
  have hmid : ∀ r < n, |nuRow D u (i + 1) τ (r + 1) - wj D (i + 1) τ| ≤ L.Sc + D.R.N D.R.m := by
    intro r hr
    obtain ⟨a1, a2⟩ := head_row u i hi τ (r + 1) (by omega)
    obtain ⟨b1, b2⟩ := L.cloud_u u τ ⟨r + 1, by omega⟩ (by show 1 ≤ r + 1; omega) (by show r + 1 + 1 < D.R.k; omega)
    rw [abs_le]
    constructor <;> linarith
  have s1 := abs_le.1 (abs_sum_range_sub _ n _ _ hmid)
  have s2 := abs_le.1 (abs_sum_range_sub (fun r => nuRow D u (i + 1) τ (n + 1 + 1 + r)) (i * (D.R.t + 1)) 0 _
    (fun r hr => block_row L u i hi τ _ (by omega) (by unfold Ranks.N; omega)))
  have hi' : (i : ℝ) ≤ D.R.m := by exact_mod_cast hi.le
  have s8 : (i : ℝ) * ((D.R.t : ℝ) + 1) * (2 * L.etaSz) ≤ D.R.m * ((D.R.t : ℝ) + 1) * (2 * L.etaSz) := by gcongr
  push_cast at s2
  rw [mul_zero] at s2
  rw [hkn, abs_le]
  constructor <;> linarith [s0.1, s0.2, s1.1, s1.2, s2.1, s2.2]

theorem arith (k m t N S η : ℝ) (hm : 1 ≤ m) (hk : 1 ≤ k) (hkm : k + m ≤ N) (ht : 1 ≤ t) (hS : 0 ≤ S) (hη : 0 ≤ η) :
    k * (S + N) + m * (t + 1) * (2 * η) + (4 * S + 2 * N + 1 + η) + (k * (S + 2 * N) + 2 * m * (η + 2 * N)) ≤
      20 * (k * S + N ^ 2 + m * t * η) := by
  have h1 : S ≤ k * S := le_mul_of_one_le_left hS hk
  have h2 : k * N ≤ N * N := mul_le_mul_of_nonneg_right (by linarith) (by linarith)
  have h3 : m * N ≤ N * N := mul_le_mul_of_nonneg_right (by linarith) (by linarith)
  have h4 : N ≤ N * N := le_mul_of_one_le_left (by linarith) (by linarith)
  have h5 : η ≤ m * η := le_mul_of_one_le_left hη hm
  have h6 : m * η ≤ t * (m * η) := le_mul_of_one_le_left (by linarith) ht
  nlinarith

theorem degree_fine : ∀ {D : D7} (L : SizeData₂ D), SizesAt L → ParameterChoice' D L → KapDef D → 2 ≤ L.sc.x → ∀ (u : D.what₂.Word), ∀ j ∈ SizeData₂.lifts D, |degPi D u j - (fockDeg D j : ℝ) - (topSum L + sizeOffTops D j)| ≤ 20 * degErr L := by
  intro D L h P hK hx u j hj
  obtain ⟨j1, j2⟩ := Finset.mem_Icc.1 hj
  obtain ⟨i, rfl⟩ : ∃ i, j = i + 1 := ⟨j - 1, by omega⟩
  have hc : 0 ≤ L.sc.b' / L.sc.x :=
    div_nonneg (GlobalTheory.HCEntries.b'_pos L).le (by linarith [L.sc.one_lt_alt])
  have hm : (1 : ℝ) ≤ D.R.m := by exact_mod_cast (by have := D.R.two_le_m; omega : 1 ≤ D.R.m)
  have har := arith D.R.k D.R.m D.R.t (D.R.N D.R.m) L.Sc L.etaSz hm (GlobalTheory.HCEntries.one_le_k D) (ranks_le D).1
    L.t_win.1 L.Sc_pos.le L.etaSz_pos.le
  unfold degPi fockDeg topSum degErr Nm
  rw [← sum_topWt, ← sum_offWt, Int.cast_sum, ← Finset.sum_add_distrib, ← Finset.sum_sub_distrib,
    ← Finset.sum_sub_distrib]
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  refine (Finset.sum_le_sum (g := fun τ => 20 * ((D.R.k : ℝ) * L.Sc + (D.R.N D.R.m : ℝ) ^ 2 +
    (D.R.m : ℝ) * (D.R.t : ℝ) * L.etaSz) + topConst D (L.sc.b' / L.sc.x) τ) fun τ _ => ?_).trans ?_
  · obtain ⟨w0, -⟩ := GlobalTheory.HCEntries.wj_bounds h hx (i + 1) j1 j2 τ
    have a := abs_le.1 (nuAbs_place_fine P u i j2 τ)
    have b := abs_le.1 (letters_place L hK i j2 τ w0)
    rw [abs_le]
    constructor <;> linarith [a.1, a.2, b.1, b.2]
  · rw [Finset.sum_add_distrib, sum_topConst, Finset.sum_const, Finset.card_univ, D.what₂.card_Tau, nsmul_eq_mul,
      mul_div_assoc]
    have : 0 ≤ (D.host.TT.card : ℝ) * (L.sc.b' / L.sc.x) := mul_nonneg (Nat.cast_nonneg _) hc
    linarith

end GlobalTheory.FockDegreeFine
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.OfGroupPullbackDataBase
section
set_option autoImplicit false
noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj Opposite
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.EndLoc
open scoped CategoryTheory.Obj

namespace GlobalTheory.EndLoc.HomGlue

theorem lbIso_pull {P Q Xa Xb Xa' Xb' : Scheme.{0}} {L : LB P} {M : LB Q} (hL : L.IsLB) (hM : M.IsLB)
    {a : Xa ⟶ P} {b : Xb ⟶ Q} {c : Xa ⟶ Xb} {a' : Xa' ⟶ P} {b' : Xb' ⟶ Q} {c' : Xa' ⟶ Xb'} (e : Xa' ⟶ Xa)
    (ha : a' = e ≫ a) (hc : c' ≫ b' = e ≫ c ≫ b) (H : LBIso (L.pull a) ((M.pull b).pull c)) :
    LBIso (L.pull a') ((M.pull b').pull c') := by
  have h1 : LBIso ((M.pull b).pull c) (M.pull (c ≫ b)) :=
    LBIso.chartPull (chartPullLinComb M b (fun _ : PUnit => c) (fun _ => c ≫ b) (fun _ => 1) (𝟙 _)
      fun _ => (Category.id_comp _).symm) (chartPullId _) (GlobalTheory.PolBaseChange.lbIso_refl (pull_isLB hM _))
  have h2 : LBIso (L.pull a) (M.pull (c ≫ b)) :=
    LBIso.trans (pull_isLB hL _) (pull_isLB (pull_isLB hM _) _) (pull_isLB hM _) H h1
  exact LBIso.chartPull (chartPullSame L (fun _ : PUnit => a') (fun _ => a) (fun _ => 1) e fun _ => ha)
    (chartPullLinComb M b' (fun _ : PUnit => c') (fun _ => c ≫ b) (fun _ => 1) e fun _ => hc) h2

variable {S : Scheme.{0}} (A B : Over S) [GrpObj A] [GrpObj B] (L : LB A.left) (M : LB B.left)

def Wit {Z : Scheme.{0}} (t : Z ⟶ S) (f : pullback A.hom t ⟶ B.left) : Prop :=
  ∃ (A' B' : Over Z) (_ : GrpObj A') (_ : GrpObj B') (φA : A'.left ⟶ A.left) (φB : B'.left ⟶ B.left) (Φ : A' ⟶ B'),
    IsGrpPullback A' A t φA ∧ IsGrpPullback B' B t φB ∧ IsMonHom Φ ∧ LBIso (L.pull φA) ((M.pull φB).pull Φ.left) ∧
    ∃ e : A'.left ⟶ pullback A.hom t, e ≫ pullback.fst _ _ = φA ∧ e ≫ pullback.snd _ _ = A'.hom ∧ e ≫ f = Φ.left ≫ φB

abbrev pmap {Z Z' : Scheme.{0}} (t : Z ⟶ S) (g : Z' ⟶ Z) : pullback A.hom (g ≫ t) ⟶ pullback A.hom t :=
  pullback.lift (pullback.fst _ _) (pullback.snd _ _ ≫ g) (by rw [pullback.condition, Category.assoc])

variable {A B L M}

theorem wit_pull (hL : L.IsLB) (hM : M.IsLB) {Z Z' : Scheme.{0}} {t : Z ⟶ S} {f : pullback A.hom t ⟶ B.left}
    (h : Wit A B L M t f) (g : Z' ⟶ Z) : Wit A B L M (g ≫ t) (pmap A t g ≫ f) := by
  obtain ⟨A', B', _, _, φA, φB, Φ, hA, hB, hΦ, hI, e, e1, e2, e3⟩ := h
  refine ⟨(Over.pullback g).obj A', (Over.pullback g).obj B', inferInstance, inferInstance,
    pullback.fst _ _ ≫ φA, pullback.fst _ _ ≫ φB, (Over.pullback g).map Φ,
    (isGrpPullback_pullback A' g).comp hA, (isGrpPullback_pullback B' g).comp hB, inferInstance, ?_, ?_⟩
  · refine lbIso_pull hL hM (pullback.fst _ _) rfl ?_ hI
    rw [← Category.assoc, show ((Over.pullback g).map Φ).left ≫ pullback.fst B'.hom g =
      pullback.fst A'.hom g ≫ Φ.left from pullback.lift_fst _ _ _, Category.assoc]
  · have hw : (pullback.fst A'.hom g ≫ φA) ≫ A.hom = pullback.snd A'.hom g ≫ g ≫ t := by
      rw [Category.assoc, hA.1.w, ← Category.assoc, pullback.condition, Category.assoc]
    have key : pullback.lift (pullback.fst A'.hom g ≫ φA) (pullback.snd A'.hom g) hw ≫ pmap A t g =
        pullback.fst A'.hom g ≫ e := by
      apply pullback.hom_ext
      · rw [Category.assoc, pullback.lift_fst, pullback.lift_fst, Category.assoc, e1]
      · rw [Category.assoc, pullback.lift_snd, pullback.lift_snd_assoc, Category.assoc, e2, pullback.condition]
    refine ⟨pullback.lift (pullback.fst _ _ ≫ φA) (pullback.snd _ _) hw, pullback.lift_fst _ _ _,
      pullback.lift_snd _ _ _, ?_⟩
    rw [← Category.assoc, key, Category.assoc, e3, ← Category.assoc, ← Category.assoc,
      show ((Over.pullback g).map Φ).left ≫ pullback.fst B'.hom g =
        pullback.fst A'.hom g ≫ Φ.left from pullback.lift_fst _ _ _]


variable (A B L M) in
structure Pt (Z : Scheme.{0}) where

  t : Z ⟶ S

  f : pullback A.hom t ⟶ B.left
  wit : Wit A B L M t f

theorem Pt.ext' {Z : Scheme.{0}} {x y : Pt A B L M Z} (e : x.t = y.t)
    (h : pullback.lift (pullback.fst _ _) (pullback.snd _ _) (by rw [pullback.condition, e]) ≫ x.f = y.f) :
    x = y := by
  obtain ⟨t, f, w⟩ := x
  obtain ⟨t', f', w'⟩ := y
  dsimp only at e h
  revert h
  subst e
  intro h
  rw [pullback.lift_fst_snd, Category.id_comp] at h
  cases h
  rfl

theorem lift_pmap_id {Z : Scheme.{0}} (t : Z ⟶ S) (h : pullback.fst A.hom t ≫ A.hom = pullback.snd A.hom t ≫ 𝟙 Z ≫ t) :
    pullback.lift (pullback.fst A.hom t) (pullback.snd A.hom t) h ≫ pmap A t (𝟙 Z) = 𝟙 _ := by
  apply pullback.hom_ext
  · rw [Category.assoc, pullback.lift_fst, pullback.lift_fst, Category.id_comp]
  · rw [Category.assoc, pullback.lift_snd, pullback.lift_snd_assoc, Category.id_comp, Category.comp_id]

theorem lift_pmap_comp {Z Z' Z'' : Scheme.{0}} (t : Z ⟶ S) (g : Z' ⟶ Z) (g' : Z'' ⟶ Z')
    (h : pullback.fst A.hom (g' ≫ g ≫ t) ≫ A.hom = pullback.snd A.hom (g' ≫ g ≫ t) ≫ (g' ≫ g) ≫ t) :
    pullback.lift (pullback.fst A.hom (g' ≫ g ≫ t)) (pullback.snd A.hom (g' ≫ g ≫ t)) h ≫ pmap A t (g' ≫ g) =
      pmap A (g ≫ t) g' ≫ pmap A t g := by
  apply pullback.hom_ext
  · rw [Category.assoc, pullback.lift_fst, pullback.lift_fst, Category.assoc, pullback.lift_fst, pullback.lift_fst]
  · rw [Category.assoc, pullback.lift_snd, pullback.lift_snd_assoc, Category.assoc, pullback.lift_snd,
      pullback.lift_snd_assoc, Category.assoc]

def Pt.map (hL : L.IsLB) (hM : M.IsLB) {Z Z' : Scheme.{0}} (g : Z' ⟶ Z) (x : Pt A B L M Z) : Pt A B L M Z' :=
  ⟨g ≫ x.t, pmap A x.t g ≫ x.f, wit_pull hL hM x.wit g⟩

theorem Pt.map_id (hL : L.IsLB) (hM : M.IsLB) {Z : Scheme.{0}} (x : Pt A B L M Z) : x.map hL hM (𝟙 Z) = x := by
  refine Pt.ext' (Category.id_comp _) ?_
  show _ ≫ pmap A x.t (𝟙 Z) ≫ x.f = x.f
  refine (Category.assoc _ _ _).symm.trans ((congrArg (· ≫ x.f) (lift_pmap_id x.t _)).trans (Category.id_comp _))

theorem Pt.map_comp (hL : L.IsLB) (hM : M.IsLB) {Z Z' Z'' : Scheme.{0}} (g : Z' ⟶ Z) (g' : Z'' ⟶ Z')
    (x : Pt A B L M Z) : x.map hL hM (g' ≫ g) = (x.map hL hM g).map hL hM g' := by
  refine Pt.ext' (Category.assoc _ _ _) ?_
  show _ ≫ pmap A x.t (g' ≫ g) ≫ x.f = pmap A (g ≫ x.t) g' ≫ pmap A x.t g ≫ x.f
  exact (Category.assoc _ _ _).symm.trans ((congrArg (· ≫ x.f) (lift_pmap_comp x.t g g' _)).trans
    (Category.assoc _ _ _))


variable (A B L M) in
def homFun (hL : L.IsLB) (hM : M.IsLB) : Scheme.{0}ᵒᵖ ⥤ Type where
  obj Z := Pt A B L M Z.unop
  map g := TypeCat.ofHom (Pt.map hL hM g.unop)
  map_id Z := by
    ext x
    exact Pt.map_id hL hM x
  map_comp g g' := by
    ext x
    exact Pt.map_comp hL hM _ _ x


variable (A B L M) in
def homProj (hL : L.IsLB) (hM : M.IsLB) : homFun A B L M hL hM ⟶ yoneda.obj S where
  app Z := TypeCat.ofHom fun x => x.t

@[simp] theorem Pt.map_t (hL : L.IsLB) (hM : M.IsLB) {Z Z' : Scheme.{0}} (g : Z' ⟶ Z) (x : Pt A B L M Z) :
    (x.map hL hM g).t = g ≫ x.t := rfl

def Pt.ofData {Z : Scheme.{0}} (t : Z ⟶ S) (A' B' : Over Z) [GrpObj A'] [GrpObj B'] (φA : A'.left ⟶ A.left)
    (φB : B'.left ⟶ B.left) (Φ : A' ⟶ B') (hA : IsGrpPullback A' A t φA) (hB : IsGrpPullback B' B t φB)
    (hΦ : IsMonHom Φ) (hI : LBIso (L.pull φA) ((M.pull φB).pull Φ.left)) : Pt A B L M Z :=
  ⟨t, hA.1.isoPullback.inv ≫ Φ.left ≫ φB, A', B', inferInstance, inferInstance, φA, φB, Φ, hA, hB, hΦ, hI,
    hA.1.isoPullback.hom, by simp, by simp, by simp⟩

end GlobalTheory.EndLoc.HomGlue
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ProdKernelMultiplierTranslateNeg
section
open NumberField IsDedekindDomain WeierstrassCurve GlobalTheory GlobalTheory.Published GlobalTheory.CMModel Formalism.L2.Th1.F
open scoped IntermediateField BigOperators Topology

namespace GlobalTheory.KerPerm

theorem prod_eq_of_perm_mod (Λ : Submodule ℤ ℂ) (T : Finset ℂ) (f ψ : ℂ → ℂ)
    (hψ : ∀ z l, l ∈ Λ → ψ (z + l) = ψ z)
    (hsep : ∀ a ∈ T, ∀ b ∈ T, a - b ∈ Λ → a = b)
    (hmap : ∀ t ∈ T, ∃ u ∈ T, f t - u ∈ Λ)
    (hinj : ∀ a b, f a - f b ∈ Λ → a - b ∈ Λ) :
    ∏ t ∈ T, ψ (f t) = ∏ t ∈ T, ψ t := by
  classical
  choose g hgT hg using hmap
  have ginj : ∀ a (ha : a ∈ T) b (hb : b ∈ T), g a ha = g b hb → a = b := by
    intro a ha b hb h
    apply hsep a ha b hb
    apply hinj
    have := Λ.sub_mem (hg a ha) (hg b hb)
    rw [h] at this
    simpa using this
  refine Finset.prod_bij g hgT ginj ?_ ?_
  · intro b hb
    obtain ⟨a, ha, h⟩ := Finset.surj_on_of_inj_on_of_card_le g hgT
      (fun a b ha hb h => ginj a ha b hb h) le_rfl b hb
    exact ⟨a, ha, h.symm⟩
  · intro a ha
    have := hψ (g a ha) _ (hg a ha)
    simpa using this

theorem prod_ker_translate_neg : ∀ (L : PeriodPair) (α : ℂ) (S : Finset ℂ) (φ : ℂ → ℂ), IsKerReps L α S → MulStable L α → (∀ z l, l ∈ L.lattice → φ (z + l) = φ z) → (∀ z s, α * s ∈ L.lattice → φ (z + s) * ∏ t ∈ S, φ (z + s + t) = φ z * ∏ t ∈ S, φ (z + t)) ∧ ∀ z, ∏ t ∈ S, φ (z - t) = ∏ t ∈ S, φ (z + t) := by
  classical
  intro L α S φ ⟨h1, h2, h3⟩ _ hφ
  have h0 : (0 : ℂ) ∉ S := fun h => (h1 0 h).2 L.lattice.zero_mem
  have hψ : ∀ z : ℂ, ∀ x l, l ∈ L.lattice → φ (z + (x + l)) = φ (z + x) := by
    intro z x l hl
    rw [← add_assoc, hφ _ _ hl]
  refine ⟨fun z s hs => ?_, fun z => ?_⟩
  · have key := prod_eq_of_perm_mod L.lattice (insert 0 S) (fun t => s + t) (fun x => φ (z + x)) (hψ z)
      (by
        intro a ha b hb hab
        rcases Finset.mem_insert.1 ha with rfl | ha <;> rcases Finset.mem_insert.1 hb with rfl | hb
        · rfl
        · exact absurd (by simpa using hab) (h1 b hb).2
        · exact absurd (by simpa using hab) (h1 a ha).2
        · exact h2 a ha b hb hab)
      (by
        intro t ht
        have hk : α * (s + t) ∈ L.lattice := by
          rw [mul_add]
          refine L.lattice.add_mem hs ?_
          rcases Finset.mem_insert.1 ht with rfl | ht
          · simp
          · exact (h1 t ht).1
        by_cases hm : s + t ∈ L.lattice
        · exact ⟨0, Finset.mem_insert_self _ _, by simpa using hm⟩
        · obtain ⟨P, hP, h⟩ := h3 _ hk hm
          exact ⟨P, Finset.mem_insert_of_mem hP, h⟩)
      (by
        intro a b h
        simpa using h)
    rw [Finset.prod_insert h0, Finset.prod_insert h0] at key
    simpa [add_assoc] using key
  · have key := prod_eq_of_perm_mod L.lattice S (fun t => -t) (fun x => φ (z + x)) (hψ z) h2
      (by
        intro t ht
        refine h3 (-t) ?_ ?_
        · rw [mul_neg]; exact L.lattice.neg_mem (h1 t ht).1
        · intro h; exact (h1 t ht).2 (by simpa using h))
      (by
        intro a b h
        have := L.lattice.neg_mem h
        convert this using 1
        ring)
    simpa [sub_eq_add_neg] using key

end GlobalTheory.KerPerm
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.QuaternionAlgebraTopologicalRing
section
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.QSA GlobalTheory.Published
open Matrix
open scoped Quaternion Topology TensorProduct

namespace GlobalTheory.QuatTop

variable {R : Type} [CommRing R] [TopologicalSpace R] {a b : R}

theorem continuous_coord_re : Continuous (fun x : ℍ[R, a, b] => x.re) :=
  (continuous_apply (0 : Fin 4)).comp (continuous_induced_dom (f := (coords : ℍ[R, a, b] → Fin 4 → R)))

theorem continuous_coord_imI : Continuous (fun x : ℍ[R, a, b] => x.imI) :=
  (continuous_apply (1 : Fin 4)).comp (continuous_induced_dom (f := (coords : ℍ[R, a, b] → Fin 4 → R)))

theorem continuous_coord_imJ : Continuous (fun x : ℍ[R, a, b] => x.imJ) :=
  (continuous_apply (2 : Fin 4)).comp (continuous_induced_dom (f := (coords : ℍ[R, a, b] → Fin 4 → R)))

theorem continuous_coord_imK : Continuous (fun x : ℍ[R, a, b] => x.imK) :=
  (continuous_apply (3 : Fin 4)).comp (continuous_induced_dom (f := (coords : ℍ[R, a, b] → Fin 4 → R)))

theorem continuous_of_coords {X : Type*} [TopologicalSpace X] {g : X → ℍ[R, a, b]}
    (h0 : Continuous fun x => (g x).re) (h1 : Continuous fun x => (g x).imI)
    (h2 : Continuous fun x => (g x).imJ) (h3 : Continuous fun x => (g x).imK) : Continuous g := by
  refine continuous_induced_rng.2 (continuous_pi fun i => ?_)
  fin_cases i
  · exact h0
  · exact h1
  · exact h2
  · exact h3

theorem isTopologicalRing [IsTopologicalRing R] : IsTopologicalRing ℍ[R, a, b] := by
  have c0 := (continuous_coord_re (R := R) (a := a) (b := b))
  have c1 := (continuous_coord_imI (R := R) (a := a) (b := b))
  have c2 := (continuous_coord_imJ (R := R) (a := a) (b := b))
  have c3 := (continuous_coord_imK (R := R) (a := a) (b := b))
  have p0 := c0.comp (continuous_fst (X := ℍ[R, a, b]) (Y := ℍ[R, a, b]))
  have p1 := c1.comp (continuous_fst (X := ℍ[R, a, b]) (Y := ℍ[R, a, b]))
  have p2 := c2.comp (continuous_fst (X := ℍ[R, a, b]) (Y := ℍ[R, a, b]))
  have p3 := c3.comp (continuous_fst (X := ℍ[R, a, b]) (Y := ℍ[R, a, b]))
  have q0 := c0.comp (continuous_snd (X := ℍ[R, a, b]) (Y := ℍ[R, a, b]))
  have q1 := c1.comp (continuous_snd (X := ℍ[R, a, b]) (Y := ℍ[R, a, b]))
  have q2 := c2.comp (continuous_snd (X := ℍ[R, a, b]) (Y := ℍ[R, a, b]))
  have q3 := c3.comp (continuous_snd (X := ℍ[R, a, b]) (Y := ℍ[R, a, b]))
  have hadd : ContinuousAdd ℍ[R, a, b] := ⟨continuous_of_coords
    (by simp only [QuaternionAlgebra.re_add]; exact p0.add q0) (by simp only [QuaternionAlgebra.imI_add]; exact p1.add q1) (by simp only [QuaternionAlgebra.imJ_add]; exact p2.add q2) (by simp only [QuaternionAlgebra.imK_add]; exact p3.add q3)⟩
  have hmul : ContinuousMul ℍ[R, a, b] := ⟨continuous_of_coords
    (by simp only [QuaternionAlgebra.re_mul]; fun_prop)
    (by simp only [QuaternionAlgebra.imI_mul]; fun_prop)
    (by simp only [QuaternionAlgebra.imJ_mul]; fun_prop)
    (by simp only [QuaternionAlgebra.imK_mul]; fun_prop)⟩
  have hneg : ContinuousNeg ℍ[R, a, b] := ⟨continuous_of_coords
    (by simp only [QuaternionAlgebra.re_neg]; exact c0.neg) (by simp only [QuaternionAlgebra.imI_neg]; exact c1.neg) (by simp only [QuaternionAlgebra.imJ_neg]; exact c2.neg) (by simp only [QuaternionAlgebra.imK_neg]; exact c3.neg)⟩
  exact {}

end GlobalTheory.QuatTop

open GlobalTheory.QuatTop in
theorem GlobalTheory.quaternion_isTopologicalRing_nrm_re_t2 : ∀ (R : Type) [CommRing R] [TopologicalSpace R] [IsTopologicalRing R] (a b : R), IsTopologicalRing ℍ[R, a, b] ∧ Continuous (nrm : ℍ[R, a, b] → R) ∧ Continuous (fun x : ℍ[R, a, b] => x.re) ∧ (T2Space R → T2Space ℍ[R, a, b]) := by
  intro R _ _ _ a b
  have c0 := (continuous_coord_re (R := R) (a := a) (b := b))
  have c1 := (continuous_coord_imI (R := R) (a := a) (b := b))
  have c2 := (continuous_coord_imJ (R := R) (a := a) (b := b))
  have c3 := (continuous_coord_imK (R := R) (a := a) (b := b))
  refine ⟨isTopologicalRing, ?_, c0, fun _ => ?_⟩
  · unfold nrm; fun_prop
  · have hinj : Function.Injective (coords : ℍ[R, a, b] → Fin 4 → R) := by
      intro x y h
      have e0 := congrFun h 0
      have e1 := congrFun h 1
      have e2 := congrFun h 2
      have e3 := congrFun h 3
      simp [coords] at e0 e1 e2 e3
      ext <;> assumption
    exact (Topology.IsEmbedding.mk ⟨rfl⟩ hinj).t2Space
end

