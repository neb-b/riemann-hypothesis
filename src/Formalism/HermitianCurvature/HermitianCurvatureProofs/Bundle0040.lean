module

public import Formalism.HermitianCurvature.HermitianCurvatureProofs.SplLen
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.UnipotentCorrectionU1.Bundle0006
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0037
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.OrbitalIntegralAeConvergenceContinuity
public import Formalism.HermitianCurvature.StatementJF
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.RegularisedPairingViaPhase
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0028
public import Formalism.FormalDegreeBessel.Bundle0002
public import Formalism.HermitianCurvature.Bundle0008

@[expose] public section

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.AdmissibleOfUnitWords
section
open Matrix
open scoped ComplexConjugate ContDiff

noncomputable section

namespace Formalism.FourierDecayAlt.P.AdmissibleLieWords

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.P.BetaSesquilinearity PI.UnitaryCorollaryDerivatives.CRH

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

def sc (ε x : ℝ) : ℝ := Real.smoothTransition ((x - ε / 4) / (ε / 4))

lemma sc_zero {ε x : ℝ} (hε : 0 < ε) (hx : x ≤ ε / 4) : sc ε x = 0 := by
  unfold sc
  exact Real.smoothTransition.zero_of_nonpos (div_nonpos_iff.2 (Or.inr ⟨by linarith, by linarith⟩))

lemma sc_one {ε x : ℝ} (hε : 0 < ε) (hx : ε / 2 ≤ x) : sc ε x = 1 := by
  unfold sc
  apply Real.smoothTransition.one_of_one_le
  rw [le_div_iff₀ (by linarith)]
  linarith

lemma sc_cd (ε : ℝ) : ContDiff ℝ ∞ (sc ε) := by
  show ContDiff ℝ ∞ (fun x => Real.smoothTransition ((x - ε / 4) / (ε / 4)))
  exact Real.smoothTransition.contDiff.comp ((contDiff_id.sub contDiff_const).div_const _)

def hh (ε x : ℝ) : ℝ := sc ε x * x ^ (-(1 / 2 : ℝ))

lemma hh_cd {ε : ℝ} (hε : 0 < ε) : ContDiff ℝ ∞ (hh ε) := by
  rw [contDiff_iff_contDiffAt]
  intro x
  by_cases hx : ε / 8 < x
  · have hx0 : 0 < x := by linarith
    show ContDiffAt ℝ ∞ (fun y => sc ε y * y ^ (-(1 / 2 : ℝ))) x
    exact ((sc_cd ε).contDiffAt).mul (Real.contDiffAt_rpow_const_of_ne hx0.ne')
  · have h0 : hh ε =ᶠ[nhds x] fun _ => 0 := by
      filter_upwards [Iio_mem_nhds (show x < ε / 4 by linarith)] with y hy
      simp [hh, sc_zero hε (le_of_lt hy)]
    exact contDiffAt_const.congr_of_eventuallyEq h0

lemma hh_ev {ε x : ℝ} (hε : 0 < ε) (hx : ε / 2 < x) :
    hh ε =ᶠ[nhds x] fun y => y ^ (-(1 / 2 : ℝ)) := by
  filter_upwards [Ioi_mem_nhds hx] with y hy
  simp only [hh, sc_one hε (le_of_lt hy), one_mul]

lemma hh_bound {ε : ℝ} (hε : 0 < ε) (j : ℕ) {x : ℝ} (hx : ε ≤ x) :
    ‖iteratedFDeriv ℝ j (hh ε) x‖ ≤ |(descPochhammer ℝ j).eval (-(1 / 2 : ℝ))| * ε ^ (-(1 / 2 : ℝ) - j) := by
  have hx0 : 0 < x := lt_of_lt_of_le hε hx
  have h2 : ε / 2 < x := by linarith
  have heq : iteratedFDeriv ℝ j (hh ε) x = iteratedFDeriv ℝ j (fun y : ℝ => y ^ (-(1 / 2 : ℝ))) x := by
    first
    | exact ((hh_ev hε h2).iteratedFDeriv ℝ j).eq_of_nhds
    | exact (hh_ev hε h2).iteratedFDeriv_eq j
  rw [heq, norm_iteratedFDeriv_eq_norm_iteratedDeriv, iteratedDeriv_eq_iterate]
  simp only [Real.iter_deriv_rpow_const]
  rw [norm_mul, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos (Real.rpow_pos_of_pos hx0 _)]
  have hj : (0 : ℝ) ≤ j := Nat.cast_nonneg j
  have hexp : -(1 / 2 : ℝ) - j ≤ 0 := by linarith
  apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
  first
  | exact Real.rpow_le_rpow_of_exponent_nonpos hε hx hexp
  | exact Real.rpow_le_rpow_of_nonpos hε hx hexp

def Phh (ε : ℝ) (z : ℂ) : ℂ := ((hh ε z.re : ℝ) : ℂ)

lemma Phh_cd {ε : ℝ} (hε : 0 < ε) : ContDiff ℝ ∞ (Phh ε) := by
  show ContDiff ℝ ∞ (fun z : ℂ => ((hh ε z.re : ℝ) : ℂ))
  exact Complex.ofRealCLM.contDiff.comp ((hh_cd hε).comp Complex.reCLM.contDiff)

lemma Phh_bound {ε : ℝ} (hε : 0 < ε) (j : ℕ) :
    ∃ B : ℝ, ∀ z ∈ {z : ℂ | ε ≤ z.re}, ‖iteratedFDeriv ℝ j (Phh ε) z‖ ≤ B := by
  refine ⟨‖Complex.ofRealCLM‖ * (|(descPochhammer ℝ j).eval (-(1 / 2 : ℝ))| * ε ^ (-(1 / 2 : ℝ) - j) *
    ‖Complex.reCLM‖ ^ j), fun z hz => ?_⟩
  have hh' : ContDiff ℝ ∞ (hh ε ∘ Complex.reCLM) := (hh_cd hε).comp Complex.reCLM.contDiff
  have e : Phh ε = Complex.ofRealCLM ∘ (hh ε ∘ Complex.reCLM) := rfl
  rw [e]
  calc ‖iteratedFDeriv ℝ j (Complex.ofRealCLM ∘ (hh ε ∘ Complex.reCLM)) z‖
      ≤ ‖Complex.ofRealCLM‖ * ‖iteratedFDeriv ℝ j (hh ε ∘ Complex.reCLM) z‖ :=
        by
          first
          | exact Complex.ofRealCLM.norm_iteratedFDeriv_comp_left hh'.contDiffAt (by exact_mod_cast le_top)
          | exact Complex.ofRealCLM.norm_iteratedFDeriv_comp_left hh' z (by exact_mod_cast le_top)
          | exact Complex.ofRealCLM.norm_iteratedFDeriv_comp_left hh'.contDiffAt z (by exact_mod_cast le_top)
    _ ≤ _ := by
        gcongr
        calc ‖iteratedFDeriv ℝ j (hh ε ∘ Complex.reCLM) z‖
            = ‖(iteratedFDeriv ℝ j (hh ε) (Complex.reCLM z)).compContinuousLinearMap
                fun _ => Complex.reCLM‖ := by
              first
              | rw [Complex.reCLM.iteratedFDeriv_comp_right (hh_cd hε) z (by exact_mod_cast le_top)]
              | rw [Complex.reCLM.iteratedFDeriv_comp_right (hh_cd hε).contDiffAt (by exact_mod_cast le_top)]
              | rw [Complex.reCLM.iteratedFDeriv_comp_right (hh_cd hε) (by exact_mod_cast le_top)]
          _ ≤ ‖iteratedFDeriv ℝ j (hh ε) (Complex.reCLM z)‖ * ∏ _i : Fin j, ‖Complex.reCLM‖ :=
              ContinuousMultilinearMap.norm_compContinuousLinearMap_le _ _
          _ = ‖iteratedFDeriv ℝ j (hh ε) (Complex.reCLM z)‖ * ‖Complex.reCLM‖ ^ j := by
              rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
          _ ≤ _ := by
              gcongr
              exact hh_bound hε j hz

lemma sqrt_div_eq {T x : ℝ} (hT : 0 < T) (hx : 0 < x) : Real.sqrt (T / x) = Real.sqrt T * x ^ (-(1 / 2 : ℝ)) := by
  rw [Real.sqrt_div hT.le x, Real.rpow_neg hx.le, ← Real.sqrt_eq_rpow, div_eq_mul_inv]

end Formalism.FourierDecayAlt.P.AdmissibleLieWords

namespace Formalism.FourierDecayAlt.P

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.P.BetaSesquilinearity PI.UnitaryCorollaryDerivatives.CRH Formalism.FourierDecayAlt.P.AdmissibleLieWords

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

lemma admissible_of_unit_words {k r i : ℕ} {u v : List (Mat k r)} (h : C6.UnitWords k r u v i) : admitted i (wL u ++ wR v) := by
  obtain ⟨h1, h2, h3⟩ := h
  exact ⟨u, v, h1, h2, h3.le, rfl⟩

lemma poly_adm {k r d n : ℕ} {P : Mat k r → ℂ} (hP : U.IsPolyDeg d P) :
    ContDiff ℝ ∞ P ∧ ∃ C : ℝ, 0 ≤ C ∧ ∀ w, admitted n w → ∀ g ∈ GV k r, ‖Dw w P g‖ ≤ C * gN g ^ d := by
  obtain ⟨hc, hb⟩ := PI.UnitaryCorollaryDerivatives.polynomial_bound k r d P hP
  refine ⟨hc, ?_⟩
  obtain ⟨C, hC⟩ := hb n
  refine ⟨max C 0, le_max_right _ _, fun w hw g hg => ?_⟩
  obtain ⟨u, v, hu, hv, hl, rfl⟩ := hw
  have := hC u v hu hv hl g hg
  simp only [List.map_const', List.sum_replicate, smul_zero, Nat.cast_zero, add_zero, Real.rpow_natCast] at this
  rw [← dLR_eq]
  exact this.trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (by have := gN_pos hg; positivity))

theorem fibre_unit_normalization : C6.FibUnit := by
  intro k r m om Gp T hom hGp hT _ ε hε i
  set ψ : Mat k r → ℂ := fun g => ((Gp g : ℝ) : ℂ) with hψdef
  obtain ⟨hψc, CG, hCG0, hCG⟩ := poly_adm (n := i) hGp
  have hGpc : Continuous Gp := by
    have : Gp = fun g => (ψ g).re := by funext g; simp [hψdef]
    rw [this]; exact Complex.continuous_re.comp hψc.continuous

  obtain ⟨C₁, hC₁0, hC₁⟩ := fdb ψ hψc {g | g ∈ GV k r ∧ ε ≤ Gp g} {z : ℂ | ε ≤ z.re}
    (fun g hg => by simpa [hψdef] using hg.2) gN (fun g hg => gN_ge_one hg.1) (2 * r + 2) 0 CG i
    (by
      intro w hw hne g hg
      have h1 := hCG w hw g hg.1
      have hl : 1 ≤ w.length := List.length_pos_iff.mpr hne
      refine h1.trans (mul_le_mul_of_nonneg_left (pow_le_pow_right₀ (gN_ge_one hg.1) ?_) hCG0)
      nlinarith)
    i ℂ (Phh ε) (Phh_cd hε) (Phh_bound hε)

  have hoa : ∀ a, ContDiff ℝ ∞ (fun g => om g a) ∧ ∃ C : ℝ, 0 ≤ C ∧ ∀ w, admitted i w → ∀ g ∈ GV k r,
      ‖Dw w (fun g => om g a) g‖ ≤ C * gN g ^ (r + 1) := fun a => poly_adm (hom a)
  choose hoc Co hCo0 hCo using hoa
  set C₂ : ℝ := ∑ a, Co a with hC₂
  have hC₂0 : 0 ≤ C₂ := Finset.sum_nonneg fun a _ => hCo0 a
  have hCoa : ∀ a, Co a ≤ C₂ := fun a => Finset.single_le_sum (fun b _ => hCo0 b) (Finset.mem_univ a)
  refine ⟨Real.sqrt T * (2 ^ i * (C₁ * C₂)), fun u v huv g hg hεg => ?_⟩
  set w := wL u ++ wR v with hw
  have hwA : admitted i w := admissible_of_unit_words huv
  have hwl : w.length = i := by rw [hw, len_LR]; exact huv.2.2
  have hlie : ∀ x ∈ w, inLie k r x.2 := lie_LR (unit_lie huv.1) (unit_lie huv.2.1)

  set Ut : Mat k r → (Fin m → ℂ) := fun g a => (Real.sqrt T : ℂ) * (Phh ε (ψ g) * om g a) with hUt
  have hUtc : ContDiff ℝ ∞ Ut :=
    contDiff_pi.2 fun a => contDiff_const.mul (((Phh_cd hε).comp hψc).mul (hoc a))
  have hO : IsOpen {g : Mat k r | ε / 2 < Gp g} := isOpen_lt continuous_const hGpc
  have heq : ∀ g' ∈ GV k r, g' ∈ {g : Mat k r | ε / 2 < Gp g} →
      (fun g' => C6.unitOf T (Gp g') (om g')) g' = Ut g' := by
    intro g' _ hg'
    have hp : 0 < Gp g' := by simp only [Set.mem_setOf_eq] at hg'; linarith
    funext a
    simp only [C6.unitOf, hUt, Phh, hψdef, Complex.ofReal_re, Pi.smul_apply, smul_eq_mul]
    rw [AdmissibleLieWords.hh, sc_one hε (le_of_lt hg'), one_mul, sqrt_div_eq hT hp]
    push_cast; ring
  rw [dLR_eq, Dw_congr_loc hlie hO heq g hg (by show ε / 2 < Gp g; linarith)]
  apply (pi_norm_le_iff_of_nonneg (mul_nonneg (mul_nonneg (Real.sqrt_nonneg _) (mul_nonneg (by positivity) (mul_nonneg hC₁0 hC₂0))) (pow_nonneg (gN_pos hg).le _))).2
  intro a
  have e1 : Dw w Ut g a = Dw w (fun g => Ut g a) g := by
    have := dw_clm (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin m => ℂ) a) w hUtc
    exact (congrFun this g).symm
  rw [e1]
  have e2 : (fun g => Ut g a) = fun g => (Real.sqrt T : ℂ) • (Phh ε (ψ g) * om g a) := by
    funext g; simp [hUt, smul_eq_mul]
  rw [e2, Dw_smul, norm_smul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _)]
  rw [mul_assoc]
  apply mul_le_mul_of_nonneg_left _ (Real.sqrt_nonneg _)
  have hL := leibB g (C₁ * C₂ * gN g ^ ((r + 1) * (2 * i + 1))) w (fun g => Phh ε (ψ g)) (fun g => om g a)
    ((Phh_cd hε).comp hψc) (hoc a) (by
      intro w₁ w₂ hs
      have hlen := spl_len hs
      obtain ⟨h₁, h₂, _⟩ := hs
      have b1 := hC₁ w₁ (Adm_sub h₁ hwA) (by have := h₁.length_le; omega) g ⟨hg, hεg⟩
      have b2 := (hCo a w₂ (Adm_sub h₂ hwA) g hg).trans
        (mul_le_mul_of_nonneg_right (hCoa a) (pow_nonneg (gN_pos hg).le _))
      have hexp : (2 * r + 2 + 0) * w₁.length + (r + 1) ≤ (r + 1) * (2 * i + 1) := by
        have := h₁.length_le; rw [hwl] at this; nlinarith
      calc ‖Dw w₁ (fun g => Phh ε (ψ g)) g‖ * ‖Dw w₂ (fun g => om g a) g‖
          ≤ (C₁ * gN g ^ ((2 * r + 2 + 0) * w₁.length)) * (C₂ * gN g ^ (r + 1)) :=
            mul_le_mul b1 b2 (norm_nonneg _) (mul_nonneg hC₁0 (pow_nonneg (gN_pos hg).le _))
        _ = C₁ * C₂ * gN g ^ ((2 * r + 2 + 0) * w₁.length + (r + 1)) := by rw [pow_add]; ring
        _ ≤ C₁ * C₂ * gN g ^ ((r + 1) * (2 * i + 1)) :=
            mul_le_mul_of_nonneg_left (pow_le_pow_right₀ (gN_ge_one hg) hexp) (mul_nonneg hC₁0 hC₂0))
  rw [hwl] at hL
  calc ‖Dw w (fun g => Phh ε (ψ g) * om g a) g‖ ≤ 2 ^ i * (C₁ * C₂ * gN g ^ ((r + 1) * (2 * i + 1))) := hL
    _ = 2 ^ i * (C₁ * C₂) * gN g ^ ((r + 1) * (2 * i + 1)) := by ring

end Formalism.FourierDecayAlt.P
end
end

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.BigCellOrbitSet
section
open MeasureTheory

noncomputable section

namespace Formalism.FourierDecayAlt.P.JFxA3

open Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.JF

theorem _root_.Formalism.FourierDecayAlt.P.big_cell_orbit_set : GqOm := by
  intro k r Wp Wq _ _ _ _ D
  have hnull : (volume : Measure ((Fin r → ℂ) × ℂ))
      (Set.univ ×ˢ {w : ℂ | Complex.normSq w = Formalism.QuantumDeterminants.Tz k r D.z * Formalism.QuantumDeterminants.Tz k r D.z'}) = 0 := by
    rw [Measure.volume_eq_prod, Measure.prod_prod]
    have h0 : (volume : Measure ℂ)
        {w : ℂ | Complex.normSq w = Formalism.QuantumDeterminants.Tz k r D.z * Formalism.QuantumDeterminants.Tz k r D.z'} = 0 := by
      apply measure_mono_null (t := Metric.sphere (0 : ℂ)
        (Real.sqrt (Formalism.QuantumDeterminants.Tz k r D.z * Formalism.QuantumDeterminants.Tz k r D.z')))
      · intro w hw
        simp only [Set.mem_setOf_eq] at hw
        simp only [Metric.mem_sphere, dist_zero_right]
        rw [← hw, Complex.normSq_eq_norm_sq, Real.sqrt_sq (norm_nonneg _)]
      · exact Measure.addHaar_sphere _ _ _
    rw [h0, mul_zero]
  rw [ae_restrict_iff' (Formalism.FourierDecayAlt.P.B7.measurableSet_Qset D)]
  filter_upwards [compl_mem_ae_iff.mpr hnull] with q hq hqQ
  apply Formalism.FourierDecayAlt.P.BigCellHermitian.gqDom D
  simp only [B.Qset, Set.mem_setOf_eq] at hqQ
  unfold Formalism.QuantumDeterminants.bcWeight at hqQ
  split_ifs at hqQ with hle
  · refine ⟨?_, ?_⟩
    · intro a ha
      have hp : (∏ b : Fin r, ‖q.1 b‖ ^ (2 * (Formalism.QuantumDeterminants.Mdim k r b - 2))) = 0 := by
        apply Finset.prod_eq_zero (Finset.mem_univ a)
        rw [ha, norm_zero]
        apply zero_pow
        have := a.isLt
        unfold Formalism.QuantumDeterminants.Mdim
        omega
      rw [hp, zero_mul] at hqQ
      exact lt_irrefl _ hqQ
    · refine lt_of_le_of_ne hle ?_
      intro heq
      exact hq ⟨Set.mem_univ _, heq.symm⟩
  · exact absurd hqQ (lt_irrefl _)

end Formalism.FourierDecayAlt.P.JFxA3
end
end

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.BigCellZetaMinors
section
open Matrix MeasureTheory Filter

noncomputable section

namespace Formalism.FourierDecayAlt.P.BigCellZetaMinors

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.JF

variable {k r : ℕ}

theorem one_uw (z : Fin (2 * r + k + 1) → ℂ) : (1 : Mat k r) ∈ UWset k r z := by
  refine ⟨?_, fun a => by simp, by simp⟩
  simp [UH]

variable {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
  [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq]

theorem dmin_sgs (D : RealPlaceData k r Wp Wq) {p : SS k r} (hp : D.inSS p) (g : Mat k r) (l : Fin (r + 2)) :
    Dmin k r D.z D.z' (sgs p g) l = Dmin k r D.z D.z' g l := by
  obtain ⟨h1, h2, h3, h4⟩ := hp
  have hs : (Matrix.of p.1.2 * Matrix.of p.1.1 : Mat k r)⁻¹ ∈ Sset k r D.z := by
    rw [Matrix.mul_inv_rev]
    exact ⟨_, BigCellInversePair.uw_inv h1, _, WeylGroupFacts.mem_n_inv h2, rfl⟩
  have hs' : (Matrix.of p.2.2 * Matrix.of p.2.1 : Mat k r) ∈ Sset k r D.z' :=
    (sGroup k r D.z' D.z'_mem).2.1 _ ⟨1, one_uw _, _, h4, (Matrix.one_mul _).symm⟩ _
      ⟨_, h3, 1, WeylGroupFacts.mem_n_one, (Matrix.mul_one _).symm⟩
  rw [B5.sgs_eq]
  exact dInv k r D.z D.z' D.z_mem D.z'_mem _ hs _ hs' g l

theorem cmin_gq (D : RealPlaceData k r Wp Wq) {q : (Fin r → ℂ) × ℂ} (hq : q ∈ QDom k r D.z D.z') (a : Fin r) :
    cmin k r D.z D.z' (gq D q) a = q.1 a :=
  (bigCellMinors k r D.z D.z' q.1 (D.μsec q.2) D.z_mem D.z'_mem).2.1 hq.1 a

theorem zeta_gq (D : RealPlaceData k r Wp Wq) {q : (Fin r → ℂ) × ℂ} (hq : q ∈ QDom k r D.z D.z') :
    zeta k r D.z D.z' (gq D q) = q.2 := by
  have hz := (bigCellMinors k r D.z D.z' q.1 (D.μsec q.2) D.z_mem D.z'_mem).2.2 hq.1
  rw [BigCellHermitian.herm_bigCell _ _ D.z_mem D.z'_mem, (D.sec.2 q.2 hq.2).2] at hz
  exact hz

end Formalism.FourierDecayAlt.P.BigCellZetaMinors

namespace Formalism.FourierDecayAlt.P

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.JF

end Formalism.FourierDecayAlt.P
end
end

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.CutGCoreKLExistsOfAlg
section
open Finset

noncomputable section

namespace Formalism.FourierDecayAlt.P.CutMP.Gauge.GC.KLExA

open Formalism.REAL Formalism.FourierDecayAlt Formalism.FourierDecayAlt.Qr

section Int

variable {V V' : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup V'] [Module ℂ V']

theorem ofFn_prod_int {t : ℕ} (F : Fin t → Module.End ℂ V) (F' : Fin t → Module.End ℂ V') (f : V →ₗ[ℂ] V')
    (h : ∀ k x, f (F k x) = F' k (f x)) (x : V) : f ((List.ofFn F).prod x) = (List.ofFn F').prod (f x) := by
  induction t generalizing x with
  | zero => simp
  | succ t ih =>
    rw [List.ofFn_succ, List.ofFn_succ, List.prod_cons, List.prod_cons, Module.End.mul_apply, Module.End.mul_apply,
      h, ih (fun k => F k.succ) (fun k => F' k.succ) (fun k y => h k.succ y)]

theorem tm_int {n : ℕ} {E : Fin n → Fin n → Module.End ℂ V} {E' : Fin n → Fin n → Module.End ℂ V'} (f : V →ₗ[ℂ] V')
    (hf : ∀ a b x, f (E a b x) = E' a b (f x)) (u : ℂ) (a b : Fin n) (x : V) :
    f (Tm E u a b x) = Tm E' u a b (f x) := by
  unfold Tm
  split_ifs <;> simp [Module.algebraMap_end_apply, hf]

theorem qminor_int {n t : ℕ} {E : Fin n → Fin n → Module.End ℂ V} {E' : Fin n → Fin n → Module.End ℂ V'}
    (f : V →ₗ[ℂ] V') (hf : ∀ a b x, f (E a b x) = E' a b (f x)) (a b : Fin t → Fin n) (u : ℂ) (x : V) :
    f (qminor E a b u x) = qminor E' a b u (f x) := by
  unfold qminor
  set_option synthInstance.maxHeartbeats 100000 in
    rw [LinearMap.sum_apply, LinearMap.sum_apply, map_sum]
  refine Finset.sum_congr rfl fun σ _ => ?_
  rw [Module.End.mul_apply, Module.End.mul_apply, Module.End.intCast_apply, Module.End.intCast_apply, map_zsmul,
    ofFn_prod_int _ _ f (fun k y => tm_int f hf _ _ _ y)]

theorem qdet_int {n : ℕ} {E : Fin n → Fin n → Module.End ℂ V} {E' : Fin n → Fin n → Module.End ℂ V'}
    (f : V →ₗ[ℂ] V') (hf : ∀ a b x, f (E a b x) = E' a b (f x)) (u : ℂ) (x : V) :
    f (qdet E u x) = qdet E' u (f x) :=
  qminor_int f hf id id u x

end Int

section Restr

variable {V : Type} [AddCommGroup V] [Module ℂ V] {n : ℕ}

def resE (E : Fin n → Fin n → Module.End ℂ V) (S : Submodule ℂ V) (hS : Stab E S) : Fin n → Fin n → Module.End ℂ S :=
  fun a b => (E a b).restrict (hS a b)

theorem resE_apply (E : Fin n → Fin n → Module.End ℂ V) (S : Submodule ℂ V) (hS : Stab E S) (a b : Fin n) (x : S) :
    ((resE E S hS a b x : S) : V) = E a b x := rfl

theorem glRel_resE {E : Fin n → Fin n → Module.End ℂ V} (hE : GlRel E) (S : Submodule ℂ V) (hS : Stab E S) :
    GlRel (resE E S hS) := by
  intro a b c d
  apply LinearMap.ext
  intro x
  apply Subtype.ext
  have h := LinearMap.congr_fun (hE a b c d) (x : V)
  by_cases hbc : b = c <;> by_cases hda : d = a <;>
    simp only [hbc, hda, if_true, if_false, Module.End.mul_apply, LinearMap.sub_apply, LinearMap.zero_apply,
      Submodule.coe_sub, Submodule.coe_zero, sub_zero, zero_sub, resE_apply] at h ⊢ <;> exact h

theorem irr_resE {E : Fin n → Fin n → Module.End ℂ V} (S : Submodule ℂ V) (hS : Stab E S) (hne : S ≠ ⊥)
    (hirr : ∀ S' : Submodule ℂ V, S' ≤ S → Stab E S' → S' = ⊥ ∨ S' = S) : Irr (resE E S hS) := by
  refine ⟨Submodule.nontrivial_iff_ne_bot.2 hne, fun T hT => ?_⟩
  have hinj := Submodule.map_injective_of_injective S.injective_subtype
  have hst : Stab E (T.map S.subtype) := by
    intro a b v hv
    obtain ⟨x, hx, rfl⟩ := Submodule.mem_map.1 hv
    exact Submodule.mem_map.2 ⟨resE E S hS a b x, hT a b x hx, rfl⟩
  rcases hirr (T.map S.subtype) (Submodule.map_subtype_le S T) hst with h | h
  · left
    exact hinj (h.trans (Submodule.map_bot _).symm)
  · right
    exact hinj (h.trans (Submodule.map_subtype_top S).symm)

theorem cap_resE {E : Fin n → Fin n → Module.End ℂ V} (m : Fin n → ℂ) (hS : Stab E (CapSp E m)) (w : ℂ)
    (x : CapSp E m) : qdet (resE E (CapSp E m) hS) w x = cpol m w • x := by
  apply Subtype.ext
  rw [Submodule.coe_smul]
  have := qdet_int (CapSp E m).subtype (E := resE E (CapSp E m) hS) (E' := E) (fun a b y => rfl) w x
  simp only [Submodule.subtype_apply] at this
  rw [this]
  exact mem_CapSp.1 x.2 w

end Restr

section Proj

variable {V : Type} [AddCommGroup V] [Module ℂ V] {ι : Type} [Fintype ι] [DecidableEq ι] {S : ι → Submodule ℂ V}

def projI (h : DirectSum.IsInternal S) (i : ι) : V →ₗ[ℂ] S i :=
  (DirectSum.component ℂ ι (fun j => S j) i).comp (LinearEquiv.ofBijective (DirectSum.coeLinearMap S) h).symm.toLinearMap

theorem projI_apply (h : DirectSum.IsInternal S) (i : ι) (v : V) :
    projI h i v = (LinearEquiv.ofBijective (DirectSum.coeLinearMap S) h).symm v i := rfl

theorem projI_self (h : DirectSum.IsInternal S) {i : ι} (x : S i) : projI h i (x : V) = x := by
  rw [projI_apply]
  exact DirectSum.IsInternal.ofBijective_coeLinearMap_same h x

theorem projI_ne (h : DirectSum.IsInternal S) {i j : ι} (hij : j ≠ i) (x : S j) : projI h i (x : V) = 0 := by
  rw [projI_apply]
  exact DirectSum.IsInternal.ofBijective_coeLinearMap_of_ne h hij x

theorem projI_sum (h : DirectSum.IsInternal S) (y : ∀ j, S j) (i : ι) : projI h i (∑ j, (y j : V)) = y i := by
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sum, Finset.sum_eq_single i (fun j _ hj => projI_ne h hj (y j)) (fun hi => absurd (Finset.mem_univ i) hi)]
  exact projI_self h (y i)

theorem sum_projI (h : DirectSum.IsInternal S) (v : V) : ∑ j, (projI h j v : V) = v := by
  set e := LinearEquiv.ofBijective (DirectSum.coeLinearMap S) h with he
  have h1 : DirectSum.coeLinearMap S (e.symm v) = v := e.apply_symm_apply v
  conv_rhs => rw [← h1, ← DirectSum.sum_univ_of (e.symm v)]
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [DirectSum.coeLinearMap_of]
  rfl

theorem projI_comm (h : DirectSum.IsInternal S) (T : Module.End ℂ V) (hT : ∀ j, ∀ v ∈ S j, T v ∈ S j) (i : ι) (v : V) :
    projI h i (T v) = T.restrict (hT i) (projI h i v) := by
  have e : T v = ∑ j, ((T.restrict (hT j) (projI h j v) : S j) : V) := by
    conv_lhs => rw [← sum_projI h v]
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum]
    rfl
  rw [e, projI_sum]

end Proj

end Formalism.FourierDecayAlt.P.CutMP.Gauge.GC.KLExA
end
end

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.CutJAPRTWNeAlgSt
section
open Matrix Finset

noncomputable section

namespace Formalism.FourierDecayAlt.P.CutMP.JA.SSn.Rep.Core.TC.PR.TW

open Formalism.REAL Formalism.FourierDecayAlt Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.Qr

def TWNeAlg : Prop :=
  ∀ (V V' : Type) [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V] [AddCommGroup V'] [Module ℂ V']
    [FiniteDimensional ℂ V'] (n : ℕ) (E : Fin (n + 1) → Fin (n + 1) → Module.End ℂ V)
    (E' : Fin (n + 1) → Fin (n + 1) → Module.End ℂ V') (β β' : ℂ) (L L' : Fin (n + 1) → ℤ) (M M' : Fin n → ℤ) (i : Fin n),
    Hyp E β L → Hyp E' β' L' → Box L M → Box L' M' → Box L (Function.update M i (M i + 1)) →
    Box L' (Function.update M' i (M' i + 1)) → shf β M = shf β' M' →
    ∀ J : V' →ₗ[ℂ] V, J ≠ 0 → (∀ a b v, J (subA E' a b v) = subA E a b (J v)) →
    (∀ v, J v ∈ CapSp (subA E) (shf β M)) →
    ∃ v' : V', (∑ c, etaK E c (J (yK E' c v'))) ≠ 0 ∧
      (∑ c, etaK E c (J (yK E' c v'))) ∈ CapSp (subA E) (shf β (Function.update M i (M i + 1)))

end Formalism.FourierDecayAlt.P.CutMP.JA.SSn.Rep.Core.TC.PR.TW
end
end

