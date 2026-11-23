module

public import Formalism.SharpRestriction.GlobalSchurBounds.Bundle0002
public import Formalism.SharpRestriction.Bundle0002
public import Formalism.SharpRestriction.GlobalSchurBounds.FirstClaimLemmaTwoFourOfLemmaTwoThree
public import Formalism.SharpRestriction.GlobalSchurBounds.ThickPlacesCorollaryOfAnyTranslate
public import Formalism.SharpRestriction.GlobalSchurBounds.TopDensityNGeSixteen
public import Formalism.SharpRestriction.GlobalSchurBounds.JointsL

@[expose] public section

noncomputable section

namespace Formalism.MainNotions

open Formalism.BasicNotions

theorem Closed.of_all {𝒞 : FamClass} {P : ∀ {eps : ℝ}, FamP eps → ℝ → Prop}
    (h : ∀ {eps : ℝ} (Fm : FamP eps) (CH : ℝ), P Fm CH) : Closed 𝒞 P :=
  ⟨1, one_pos, fun _ _ _ => ⟨⟨0, fun _ => 0, fun _ => 0, fun _ => 0⟩, fun Fm CH _ _ => h Fm CH⟩⟩

theorem logNE_le_of_rows (D : D7) {Y x eps : ℝ} (he : 0 < eps) (h1 : 1 < Y) (hY : Y ≤ x) (h : QDRows_at D Y eps) :
    Real.log (GlobalTheoryTheory.NE D) ≤ 2 * x ^ (eps / 5) * Real.log x ^ 2 := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, hlog⟩ := h
  have hY0 : 0 < Y := by linarith
  have hNE : Real.log (GlobalTheoryTheory.NE D) ≤ 2 * Y ^ (eps / 5) * Real.log Y ^ 2 := by
    first
      | (unfold GlobalTheoryTheory.NE; push_cast; exact hlog)
      | simpa [GlobalTheoryTheory.NE] using hlog
  have ha : Y ^ (eps / 5) ≤ x ^ (eps / 5) := Real.rpow_le_rpow hY0.le hY (by linarith)
  have hl0 : 0 ≤ Real.log Y := Real.log_nonneg h1.le
  have hl : Real.log Y ≤ Real.log x := Real.log_le_log hY0 hY
  have hsq : Real.log Y ^ 2 ≤ Real.log x ^ 2 := by nlinarith
  have hp : 0 ≤ Y ^ (eps / 5) := Real.rpow_nonneg hY0.le _
  have hm : Y ^ (eps / 5) * Real.log Y ^ 2 ≤ x ^ (eps / 5) * Real.log x ^ 2 :=
    mul_le_mul ha hsq (by positivity) (le_trans hp ha)
  linarith

theorem one_lt_of_win {eps : ℝ} (Fm : FamP eps) {x Y : ℝ} (hx : 1 < x) (h : x ^ (1 / Fm.J) ≤ Y) : 1 < Y := by
  obtain ⟨i⟩ := Fm.Ix_zero
  have hJ : 1 ≤ Fm.J := by
    have h0 := (Fm.L 0 i).sc.one_le_J
    rwa [Fm.L_J 0 i] at h0
  have hp : 0 < 1 / Fm.J := one_div_pos.mpr (by linarith)
  exact lt_of_lt_of_le (Real.one_lt_rpow hx hp) h

theorem eps_pos_of_fam {eps : ℝ} (Fm : FamP eps) : 0 < eps := by
  obtain ⟨i⟩ := Fm.Ix_zero
  have h0 := (Fm.L 0 i).sc.eps_pos
  rwa [Fm.L_eps 0 i] at h0

theorem pair_and_box_hypothesis_of_congruence_data_and_boxes {eps : ℝ} (Fm : FamP eps) (hR : QDRowsF Fm) (hB : BoxesF Fm) :
    ∃ x0 : ℝ, ∀ x ≥ x0, ∀ i : Fm.Ix x,
      (∃ Y : ℝ, 1 < Y ∧ Y ≤ x ∧ ShortIntervalPrimes.PairAt Y eps (Fm.D x i).host.q (Fm.D x i).host.d) ∧ ShortIntervalPrimes.PropTwoSixBoxHypothesis (Fm.D x i) x eps := by
  obtain ⟨xR, hR⟩ := hR
  obtain ⟨xB, hB⟩ := hB
  refine ⟨max (max xR xB) 2, fun x hx i => ?_⟩
  have hxR : xR ≤ x := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hx
  have hxB : xB ≤ x := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hx
  have hx1 : 1 < x := by linarith [le_max_right (max xR xB) 2]
  obtain ⟨Y, ⟨hY1, hY2⟩, hQ⟩ := hR x hxR i
  obtain ⟨Y', ⟨hY1', hY2'⟩, -, hE⟩ := hB x hxB i
  have hY : 1 < Y := one_lt_of_win Fm hx1 hY1
  have hY' : 1 < Y' := one_lt_of_win Fm hx1 hY1'
  have hlog := logNE_le_of_rows (Fm.D x i) (eps_pos_of_fam Fm) hY hY2 hQ
  obtain ⟨a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, -⟩ := hQ
  exact ⟨⟨Y, hY, hY2, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10⟩, ⟨Y', hY', hY2', hE⟩, hlog⟩

def LitThin : Prop :=
  (∃ C1 c : ℝ, 0 < C1 ∧ 0 < c ∧ ∀ D : D7, ShortIntervalPrimes.adm6 D C1 c) ∧ (∃ C : ℝ, 0 < C ∧ ∀ D : D7, ShortIntervalPrimes.adm7 D C) ∧
    ∃ C : ℝ, 0 < C ∧ ∀ D : D7, ShortIntervalPrimes.adm11 D C

theorem prop_two_six_congruence_family_of_literature {eps : ℝ} (Fm : FamP eps) (hL : LitThin) : ShortIntervalPrimes.FamilyPropTwoSixCongruenceForm Fm := by
  obtain ⟨⟨C1, c, hC1, hc, h6⟩, ⟨C7, hC7, h7⟩, C11, hC11, h11⟩ := hL
  exact ShortIntervalPrimes.proposition_six_norm_family_of_admitted Fm ⟨C1, c, hC1, hc, fun _ _ _ => h6 _⟩ ⟨C7, hC7, fun _ _ _ => h7 _⟩ ⟨C11, hC11, fun _ _ _ => h11 _⟩

theorem chosenThin_of_boxesN {eps : ℝ} (Fm : FamP eps) (hL : LitThin) (hB : BoxesF Fm) (hR : QDRowsF Fm) :
    ∃ c6 : ℝ, 0 < c6 ∧ ChosenThin Fm c6 := by
  obtain ⟨c, hc, x0, -, h⟩ := prop_two_six_congruence_family_of_literature Fm hL
  obtain ⟨xa, ha⟩ := pair_and_box_hypothesis_of_congruence_data_and_boxes Fm hR hB
  refine ⟨c, hc, max x0 xa, fun x hx i => ?_⟩
  have h1 : x0 ≤ x := le_trans (le_max_left _ _) hx
  have h2 : xa ≤ x := le_trans (le_max_right _ _) hx
  have hn := h x h1 i
  unfold ShortIntervalPrimes.PropTwoSixThinScales at hn
  exact hn (ha x h2 i).2

theorem chosenThin_closed (𝒞 : FamClass) (hL : LitThin) :
    Closed 𝒞 (fun Fm _ => BoxesF Fm → QDRowsF Fm → (∃ C5 : ℝ, 0 < C5 ∧ ChosenQD Fm C5) →
      ∃ c6 : ℝ, 0 < c6 ∧ ChosenThin Fm c6) :=
  Closed.of_all fun Fm _ hB hR _ => chosenThin_of_boxesN Fm hL hB hR

section Proviso

variable {D : D7}

theorem proviso_e (L : SizeData₂ D) (h4f : LinkB.RankM D) (hDu : StandardLattice.FactDuStar D) (hDs : StandardLattice.FactDstar D) :
    ChProviso_at L (Real.exp 1) := by
  intro u
  have hΓ : 1 < (D.mem u).A.GamP := (D.mem u).A.one_lt_gammaP
  have hΓ0 : 0 < (D.mem u).A.GamP := lt_trans one_pos hΓ
  have hD : 0 < StandardLattice.DstarD D := by rw [← hDs, ← D.Dstar_eq u]; exact (D.mem u).A.Dstar_pos
  have hd : 0 < StandardLattice.duStarU D u := by rw [← hDu u]; exact_mod_cast (D.mem u).A.duStar_pos
  have hk := D.R.k_ge
  have hf : 1 ≤ D.R.f := by
    have hm : D.R.m ≤ D.R.f := D.R.m_le_f
    have hm2 := D.R.two_le_m
    omega
  have hfk : 2 * D.R.f ≤ 2 ^ D.R.k := by
    have h1 : D.R.f ≤ D.R.k := D.R.f_le_k
    have h2 : D.R.k - 1 < 2 ^ (D.R.k - 1) := Nat.lt_two_pow_self
    have h3 : 2 ^ D.R.k = 2 * 2 ^ (D.R.k - 1) := by
      rw [← pow_succ']; congr 1; omega
    omega
  have hfR : (0 : ℝ) < D.R.f := by exact_mod_cast hf
  have hkR : (0 : ℝ) < D.R.k := by exact_mod_cast (by omega : 0 < D.R.k)
  have hX : Real.exp (StandardLattice.logXuD D u) ^ (D.R.f * D.R.k) = StandardLattice.DstarD D / StandardLattice.duStarU D u := by
    rw [← Real.exp_nat_mul]
    unfold StandardLattice.logXuD StandardLattice.logXu
    push_cast
    rw [show (D.R.f : ℝ) * D.R.k * (1 / ((D.R.f : ℝ) * D.R.k) * Real.log (StandardLattice.DstarD D / StandardLattice.duStarU D u)) =
      Real.log (StandardLattice.DstarD D / StandardLattice.duStarU D u) by field_simp]
    exact Real.exp_log (div_pos hD hd)
  have hT : (2 : ℝ) ≤ ((D.mem u).A.T : ℝ) := by exact_mod_cast (D.mem u).A.T_prime.two_le
  have hw := D.T_win u
  have hXe := LinkB.exp_logXu hDu hDs u
  have h1 : Real.exp (StandardLattice.logXuD D u) * (D.mem u).A.GamP ^ (-(2 : ℝ) / (D.R.f * D.R.k)) =
      (D.mem u).A.Tstar := by rw [hXe]; rfl
  obtain ⟨c1, c2, -, -⟩ := Formalism.HermitianLattices.GenusMassVolumes.mass_corollary D.R.f D.R.k ((D.mem u).A.T : ℝ)
    (Real.exp (StandardLattice.logXuD D u)) (D.mem u).A.GamP (StandardLattice.DstarD D) (StandardLattice.duStarU D u) (D.duS u : ℝ)
    (StandardLattice.logXuD D u) (StandardLattice.logXuD D u) hf (by omega) hfk hT (Real.exp_pos _) hΓ.le hD hd hX
    (by rw [h1]; exact hw.1) (by rw [h1, mul_comm]; exact hw.2) (h4f u)
    (by rw [Real.log_exp]) (by rw [Real.log_exp])
  rw [LinkB.gamL_eq L u, hDs]
  have hG2 : 0 ≤ (D.mem u).A.GamP ^ 2 := by positivity
  constructor
  · have he : (2 : ℝ) ≤ Real.exp 1 := by have := Real.add_one_le_exp (1 : ℝ); linarith
    refine (inv_anti₀ (by norm_num) he).trans ?_
    rw [le_div_iff₀ hD]
    calc (2 : ℝ)⁻¹ * StandardLattice.DstarD D = StandardLattice.DstarD D * ((D.mem u).A.GamP⁻¹) ^ 2 / 2 * (D.mem u).A.GamP ^ 2 := by
          field_simp
      _ ≤ (D.duS u : ℝ) * (D.mem u).A.GamP ^ 2 := mul_le_mul_of_nonneg_right c1 hG2
  · rw [div_le_iff₀ hD]
    calc (D.duS u : ℝ) * (D.mem u).A.GamP ^ 2
        ≤ Real.exp 1 * (StandardLattice.DstarD D * ((D.mem u).A.GamP⁻¹) ^ 2) * (D.mem u).A.GamP ^ 2 :=
          mul_le_mul_of_nonneg_right c2 hG2
      _ = Real.exp 1 * StandardLattice.DstarD D := by field_simp

end Proviso

def RankTiesF {eps : ℝ} (Fm : FamP eps) : Prop :=
  ∃ x0 : ℝ, ∀ x ≥ x0, ∀ i : Fm.Ix x, (∀ j, StandardLattice.SplitsF (Fm.D x i) ((Fm.D x i).host.g j)) ∧
    ∀ u : (Fm.D x i).what₂.Word, StandardLattice.SplitsF (Fm.D x i) ((Fm.D x i).mem u).A.T ∧ StandardLattice.Mu0Tie (Fm.D x i) u

theorem rankHypF_of {eps : ℝ} (Fm : FamP eps) (h : RankTiesF Fm) : LinkB.RankHypF Fm := by
  obtain ⟨x0, h⟩ := h
  unfold LinkB.RankHypF
  refine ⟨max (max x0 3) (Fm.x1 + 1), fun x hx i => ?_⟩
  have h0 : x0 ≤ x := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hx
  have h3 : 3 ≤ x := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hx
  have h1 : Fm.x1 < x := by linarith [le_max_right (max x0 3) (Fm.x1 + 1)]
  obtain ⟨hg, hu⟩ := h x h0 i
  unfold LinkB.RankHyp
  exact ⟨GlobalTheoryTheory.JDB.gBig_fam Fm x h3 h1 i, hg, hu⟩

end Formalism.MainNotions

end
