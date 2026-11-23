module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0010
public import Development.AbelianVarietyTheory.Definitions.Jets.SumIoPr
public import Formalism.SharpRestriction.CuspSpanNormBounds.LeadMinorK
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0013
public import Formalism.LocalRingCardinality.Bundle0003
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0045
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0042
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0094
public import Development.AbelianVarietyTheory.Definitions.Jets.Bundle0002
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.NormSqUnitNormalizationLe
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0112
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0197
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0159
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.MomentPieriNumericsOfSizeHyps
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.DiscreteSeriesBesselGap
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0353
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0271
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.NGAnalytic
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.DataInst
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerVolume.InVolumesAtOfSWS
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.GlobSet
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.NcAllC
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.Bundle0078
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.Bundle0026
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.AlTiePl
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedVolumeStatements.RealBracketOfRowBlock
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.Bundle0096
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.GaugeVolUD
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.Bundle0053
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.Bundle0051
public import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.Bundle0005
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.Bundle0079
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.Bundle0012
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.CovolumeFrames.Bundle0001
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.LocVolPrim
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.RhsWLimOfLeaves
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.HermRepUnram

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.LintegralTranslate
section
open BranchingSupport GlobalTheory.CellAmp GlobalTheory.Amp Formalism.BasicNotions Formalism.MainNotions.S Formalism.QuantumDeterminants Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal Pointwise

noncomputable section

namespace GlobalTheory.AmpMoments

theorem lenA_mul {k r : ℕ} (z : Fin (2 * r + k + 1) → ℂ) (t x : MatKR k r) (s : Fin (r + 1) → ℂ)
    (hs : ∀ a, s a ≠ 0) (ht : ∀ a, t⁻¹ *ᵥ fvec k r z a = s a • fvec k r z a) (a : Fin (r + 1)) :
    lenA k r z (t * x) a = ‖s a‖ * lenA k r z x a := by
  have e : ∀ b, (WithLp.toLp 2 ((t * x)⁻¹ *ᵥ fvec k r z b) : EuclideanSpace ℂ (Fin (2 * r + k + 1))) =
      s b • WithLp.toLp 2 (x⁻¹ *ᵥ fvec k r z b) := fun b => by
    rw [Matrix.mul_inv_rev, ← Matrix.mulVec_mulVec, ht, Matrix.mulVec_smul, WithLp.toLp_smul]
  unfold lenA
  simp only [e]
  set v : Fin (r + 1) → EuclideanSpace ℂ (Fin (2 * r + k + 1)) := fun b => WithLp.toLp 2 (x⁻¹ *ᵥ fvec k r z b)
  have hsp : Submodule.span ℂ ((fun b => s b • v b) '' {b | b < a}) = Submodule.span ℂ (v '' {b | b < a}) := by
    apply le_antisymm <;> refine Submodule.span_le.2 ?_ <;> rintro _ ⟨b, hb, rfl⟩
    · exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨b, hb, rfl⟩)
    · have := Submodule.smul_mem (Submodule.span ℂ ((fun b => s b • v b) '' {b | b < a})) (s b)⁻¹
        (Submodule.subset_span ⟨b, hb, rfl⟩)
      simp only [smul_smul, inv_mul_cancel₀ (hs b), one_smul] at this
      exact this
  rw [hsp, ← infDist_smul₀ (s a)]
  congr 1
  ext y
  rw [Set.mem_smul_set_iff_inv_smul_mem₀ (hs a)]
  exact ((Submodule.smul_mem_iff _ (inv_ne_zero (hs a)))).symm

theorem lintegral_translate {k r : ℕ} (ν : Measure (Mt k r)) (t : MatKR k r) (ht : IsUnit t.det)
    (F : Mt k r → ℝ≥0∞) :
    ∫⁻ y, F y ∂ν = ∫⁻ x, F (fun i j => (t * Matrix.of x) i j) ∂(ν.map fun x => fun i j => (t⁻¹ * Matrix.of x) i j) := by
  have hc : ∀ g : MatKR k r, Continuous fun x : Mt k r => (fun i j => (g * Matrix.of x) i j : Mt k r) := fun g =>
    (continuous_const.matrix_mul continuous_id : Continuous fun x : MatKR k r => g * x)
  let e : Mt k r ≃ₜ Mt k r :=
    { toFun := fun x => fun i j => (t⁻¹ * Matrix.of x) i j
      invFun := fun x => fun i j => (t * Matrix.of x) i j
      left_inv := fun x => (Matrix.mul_nonsing_inv_cancel_left t (Matrix.of x) ht :)
      right_inv := fun x => (Matrix.nonsing_inv_mul_cancel_left t (Matrix.of x) ht :)
      continuous_toFun := hc _
      continuous_invFun := hc _ }
  have := lintegral_map_equiv (μ := ν) (fun x => F (e.symm x)) e.toMeasurableEquiv
  refine Eq.trans ?_ this.symm
  exact lintegral_congr fun y => congrArg F (e.symm_apply_apply y).symm

theorem sq_nnnorm {V : Type} [NormedAddCommGroup V] (v : V) : (‖v‖₊ : ℝ≥0∞) ^ 2 = ENNReal.ofReal (‖v‖ ^ 2) := by
  rw [← ENNReal.coe_pow, ← ENNReal.ofReal_coe_nnreal]; rfl

theorem haar_of_conj {k r : ℕ} {μ : Measure (Mt k r)} {t : MatKR k r} (ht : IsUnit t.det)
    (hN : ∀ n, n ∈ Nset k r ↔ t * n * t⁻¹ ∈ Nset k r)
    (h : PI.BesselPeriodGGP.IsHaarOn (Nset k r) (μ.map fun x => fun i j => (t⁻¹ * Matrix.of x * t) i j)) :
    PI.BesselPeriodGGP.IsHaarOn (Nset k r) μ := by
  have hc : ∀ g g' : MatKR k r, Continuous fun x : Mt k r => (fun i j => (g * Matrix.of x * g') i j : Mt k r) :=
    fun g g' => ((continuous_const.matrix_mul continuous_id).matrix_mul continuous_const :
      Continuous fun x : MatKR k r => g * x * g')
  have hl : ∀ g : MatKR k r, Measurable (lmulM g : Mt k r → Mt k r) := fun g =>
    (show Continuous (lmulM g : Mt k r → Mt k r) from
      (continuous_const.matrix_mul continuous_id : Continuous fun x : MatKR k r => g * x)).measurable
  have i1 : ∀ x : MatKR k r, t * (t⁻¹ * x * t) * t⁻¹ = x := fun x => by
    rw [← Matrix.mul_assoc, Matrix.mul_nonsing_inv_cancel_left t x ht, Matrix.mul_nonsing_inv_cancel_right t x ht]
  have i2 : ∀ x : MatKR k r, t⁻¹ * (t * x * t⁻¹) * t = x := fun x => by
    rw [← Matrix.mul_assoc, Matrix.nonsing_inv_mul_cancel_left t x ht, Matrix.nonsing_inv_mul_cancel_right t x ht]
  let e0 : Mt k r ≃ₜ Mt k r :=
    { toFun := fun x => fun i j => (t⁻¹ * Matrix.of x * t) i j
      invFun := fun x => fun i j => (t * Matrix.of x * t⁻¹) i j
      left_inv := fun x => (i1 (Matrix.of x) :)
      right_inv := fun x => (i2 (Matrix.of x) :)
      continuous_toFun := hc _ _
      continuous_invFun := hc _ _ }
  let e := e0.toMeasurableEquiv
  obtain ⟨h1, h2, h3, h4⟩ : PI.BesselPeriodGGP.IsHaarOn (Nset k r) (μ.map e) := h
  refine ⟨?_, fun h0 => h2 (by rw [h0, Measure.map_zero]), ?_, fun s hs => ?_⟩
  · rw [← e.map_symm_map (μ := μ)]
    exact e.symm.sigmaFinite_map
  · rw [e.map_apply] at h3
    rw [← h3]
    congr 1
    ext x
    have := hN (t⁻¹ * Matrix.of x * t)
    rw [i1] at this
    exact not_congr this.symm
  · have hs' : t⁻¹ * s * t ∈ Nset k r := (hN _).2 (by rwa [i1])
    apply e.map_measurableEquiv_injective
    show (μ.map (lmulM s)).map e = μ.map e
    rw [← h4 _ hs', Measure.map_map e.measurable (hl _), Measure.map_map (hl _) e.measurable]
    congr 1
    funext x
    show t⁻¹ * (s * Matrix.of x) * t = t⁻¹ * s * t * (t⁻¹ * Matrix.of x * t)
    simp only [Matrix.mul_assoc, Matrix.mul_nonsing_inv_cancel_left t _ ht]

theorem size_bound {b v g T x Cg Cu CT : ℝ} {r q : ℕ} (hb : Real.exp 1 < b) (hv : 1 ≤ v) (hvb : 2 * v ≤ b)
    (hg : 1 ≤ g) (hgb : g ≤ b ^ (2 * Cg)) (hCg : 8 ≤ Cg) (hT : T ≤ b ^ (CT * (2 * r + 2 : ℝ))) (hx0 : 0 ≤ x)
    (hx : x ≤ max (Real.pi / v / g) (Real.pi / v / g)⁻¹ ^ r) :
    x ^ (2 * q) * Hsq r T (b ^ max 2 Cu) ^ q ≤
      b ^ (2 * (2 * Cg + 2 + |CT| + 10 * max 2 Cu) * (2 * r + 2 : ℝ) * q) := by
  have hb2 : 2 < b := lt_trans (by have := Real.exp_one_gt_d9; linarith) hb
  have hb1 : 1 ≤ b := by linarith
  have hb0 : 0 < b := by linarith
  have hr : (0 : ℝ) ≤ r := Nat.cast_nonneg r
  have hB : (2 : ℝ) ≤ max 2 Cu := le_max_left _ _
  have hp := Real.pi_gt_three
  have hg2 : 1 ≤ b ^ (2 * Cg) := hg.trans hgb
  have hM : max (Real.pi / v / g) (Real.pi / v / g)⁻¹ ≤ b ^ (2 * Cg + 2) := by
    rw [Real.rpow_add hb0, Real.rpow_two]
    refine max_le ?_ ?_
    · have : Real.pi / v / g ≤ Real.pi :=
        (div_le_self (by positivity) hg).trans (div_le_self (by positivity) hv)
      have := Real.pi_le_four
      nlinarith
    · rw [div_div, inv_div, div_le_iff₀ (by positivity)]
      have h1 : v * g ≤ b ^ 2 * b ^ (2 * Cg) := mul_le_mul (by nlinarith) hgb (by linarith) (by positivity)
      have : 0 ≤ b ^ (2 * Cg) * b ^ 2 := by positivity
      nlinarith
  have h1 : x ≤ b ^ ((2 * Cg + 2) * r) := by
    rw [Real.rpow_mul_natCast hb0.le]
    exact hx.trans (pow_le_pow_left₀ (le_max_of_le_left (by positivity)) hM r)
  have h2 : max 1 T ≤ b ^ (|CT| * (2 * r + 2 : ℝ)) :=
    max_le (Real.one_le_rpow hb1 (by positivity))
      (hT.trans (Real.rpow_le_rpow_of_exponent_le hb1 (mul_le_mul_of_nonneg_right (le_abs_self _) (by positivity))))
  have h3 : x ^ 2 * Hsq r T (b ^ max 2 Cu) ≤
      b ^ (2 * (2 * Cg + 2 + |CT| + 10 * max 2 Cu) * (2 * r + 2 : ℝ)) := by
    unfold Hsq
    calc x ^ 2 * (max 1 T * (b ^ max 2 Cu) ^ (20 * (r + 1)))
        ≤ (b ^ ((2 * Cg + 2) * r)) ^ 2 * (b ^ (|CT| * (2 * r + 2 : ℝ)) * (b ^ max 2 Cu) ^ (20 * (r + 1))) := by
          gcongr
      _ = b ^ ((2 * Cg + 2) * r * (2 : ℕ) + (|CT| * (2 * r + 2 : ℝ) + max 2 Cu * (20 * (r + 1) : ℕ))) := by
          rw [Real.rpow_add hb0, Real.rpow_add hb0, Real.rpow_mul_natCast hb0.le _ 2,
            Real.rpow_mul_natCast hb0.le (max 2 Cu)]
      _ ≤ _ := by
          refine Real.rpow_le_rpow_of_exponent_le hb1 ?_
          push_cast
          have := abs_nonneg CT
          nlinarith [mul_nonneg this hr, mul_nonneg (by linarith : 0 ≤ Cg) hr, mul_nonneg (by linarith : 0 ≤ max 2 Cu) hr]
  rw [pow_mul, ← mul_pow, Real.rpow_mul_natCast hb0.le]
  exact pow_le_pow_left₀ (by unfold Hsq; positivity) h3 q

theorem radius_bound {k r m N q : ℕ} {Cn Cq : ℝ} (hm : m = 2 * r + 2) (hk : m ^ 4 ≤ k) (hC : |Cn| + |Cq| ≤ m)
    (hN : (N : ℝ) ≤ Cn * k * (m : ℝ) ^ 3) (hq : (q : ℝ) ≤ Cq * (r : ℝ) ^ 3) :
    N + (r + 1) * q ≤ k * m ^ 5 ∧ (r + 1) * q ≤ 2 * (2 * r + k + 1) ^ 2 := by
  have a1 := abs_nonneg Cn
  have a2 := abs_nonneg Cq
  have hN' : N ≤ m * k * m ^ 3 := by
    have : (N : ℝ) ≤ m * k * (m : ℝ) ^ 3 := hN.trans (by gcongr; linarith [le_abs_self Cn])
    exact_mod_cast this
  have hq' : q ≤ m * r ^ 3 := by
    have : (q : ℝ) ≤ m * (r : ℝ) ^ 3 := hq.trans (by gcongr; linarith [le_abs_self Cq])
    exact_mod_cast this
  have h1 : (r + 1) * q ≤ m * k :=
    calc (r + 1) * q ≤ m * (m * m ^ 3) :=
          Nat.mul_le_mul (by omega) (hq'.trans (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by omega) 3)))
      _ = m * m ^ 4 := by ring
      _ ≤ m * k := Nat.mul_le_mul_left _ hk
  have h2 : m ≤ m ^ 4 := Nat.le_self_pow (by norm_num) m
  constructor
  · calc N + (r + 1) * q ≤ m * k * m ^ 3 + m ^ 4 * k := Nat.add_le_add hN' (h1.trans (Nat.mul_le_mul_right _ h2))
      _ = k * m ^ 4 * 2 := by ring
      _ ≤ k * m ^ 4 * m := Nat.mul_le_mul_left _ (by omega)
      _ = k * m ^ 5 := by ring
  · have : m * k ≤ k * k := Nat.mul_le_mul_right _ (h2.trans hk)
    nlinarith

theorem isBesselMapSm_of {k r : ℕ} {H Wp : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] {z : Fin (2 * r + k + 1) → ℂ} {ψ : MatKR k r → ℂ}
    {σ : MatKR k r → (H →L[ℂ] H)} {π : MatKR k r → (Wp →L[ℂ] Wp)} {B : H → Wp}
    (h : IsBesselMapSm (k := k) (r := r) z ψ σ π B) : PI.BesselMapUniq.IsBesselMapSm (k := k) (r := r) z ψ σ π B := by
  have e : ∀ (w : List (MatKR k r)) (v : H), PI.UpqRep.dsigW (k := k) (r := r) σ w v = dsigW (k := k) (r := r) σ w v := by
    intro w v
    induction w with
    | nil => rfl
    | cons X w ih =>
      show PI.UpqRep.dsig σ X (PI.UpqRep.dsigW σ w v) = dsig σ X (dsigW σ w v)
      rw [ih]; rfl
  obtain ⟨h1, h2, h3, C, Ws, h4, h5⟩ := h
  exact ⟨h1, h2, h3, C, Ws, h4, fun v hv => by simp only [e]; exact h5 v hv⟩

end GlobalTheory.AmpMoments
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.MeanCountConstantEqUnscaledMainConstant
section
open NumberField MeasureTheory Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.HidaSetting Formalism.L2.SG.Full Formalism.L2.SG.TermLoc Formalism.L2.SG.RowsConc Formalism.L2.SG.NGCut Formalism.L2.SG.NGAnalytic Formalism.FourierDecayAlt GlobalTheory.Unfold GlobalTheory.LocOver GlobalTheory.GenMass
open scoped Classical ENNReal
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.CountConst

def emptyPairs {D : D7} (u u' : D.what₂.Word) (F0 : FlagG (VS D) D.R.rS ((Tu D u : ℕ) : D.host.E))
    (what₂ : Finset (Submodule (𝓞 D.host.E) (VS D).V)) : Formalism.L2.SG.PairVal.PairSys D u u' F0 what₂ where
  P := Empty
  fst := Empty.elim
  snd := Empty.elim
  row := fun p => p.elim
  inj := fun p => p.elim
  gscal := fun _ => False


set_option maxHeartbeats 4000000 in
theorem countConst_eq_unscaledConst : PI.VolStabS.MassDataS.SWXS → ∀ (Cg cb Cw cT CT C0 C' Cl : ℝ) (D : D7) (large₂ : SizeData₂ D) (X : HidaSetting D) (Y : Full X) (u u' : D.what₂.Word), Ctx Cg cb Cw cT CT C0 C' Cl D large₂ X Y u u' → 2 * D.R.rS + 2 + D.R.f + 5 ≤ D.R.k → (D.mem u).A.T ≡ (D.mem u').A.T [MOD (gS D) ^ 2] → ∀ (hb : Formalism.L2.SG.AdBridge.AdBridgeIso X.B.I) (X0 : Fin (2 * D.R.rS + 2) → Fin X.B.I.n → X.B.I.E) (ψ : AddChar (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF X.B.I.F) ℂ), MassDataTie X hb X0 ψ → ∀ (sd C Th : ℝ) (F0 : FlagG (VS D) D.R.rS ((Tu D u : ℕ) : D.host.E)) (what₂ : Finset (Submodule (𝓞 D.host.E) (VS D).V)) (vR : Formalism.L2.SG.TermDef.Term D u u' F0 what₂ → ℝ) (Q : Formalism.L2.SG.PairVal.PairSys D u u' F0 what₂) (i0 i0' : ∀ _ : InfinitePlace X.B.I.F, Fin D.R.k) (νq : X.B.I.Ginf → Measure X.B.I.Ginf), 0 < Formalism.L2.SG.MassDataConc.ngFac D ∧ Formalism.L2.SG.Pf.Cnt.cExpl D (X.Fu u) (Y.what₂ u) * Formalism.MainNotions.S.Cnt.massRows D (X.Fu u) (Y.what₂ u) * ∏' p, Formalism.L2.SG.DataInst.alpD u u' p = (bkU X hb Y u u' X0 ψ sd C Th vR Q i0 i0' νq).AA * Formalism.L2.SG.MassDataConc.ngFac D := by
  intro hSW Cg cb Cw cT CT C0 C' Cl D large₂ X Y u u' hc hk hcong hb X0 ψ hT sd C Th F0 what₂ vR Q i0 i0' νq
  obtain ⟨hMT, hI, hS, hMC, hLC, hLT, hdet⟩ := hT
  set Q0 := emptyPairs u u' (X.Fu u) (Y.what₂ u) with hQ0
  set vR0 : Formalism.L2.SG.TermDef.Term D u u' (X.Fu u) (Y.what₂ u) → ℝ := fun _ => 0 with hvR0
  have hK2 := Formalism.L2.SG.Closed.level_subgroup_properties X
  have hV : 0 < X.volK2 := ENNReal.toReal_pos (ne_of_gt hK2.2.2.1) (ne_of_lt hK2.2.2.2)
  have hH : Formalism.L2.SG.TypedSets.HypX X hb (Y.FN u) (Y.FN u') u u' := ⟨hMT, hK2, Y.FN_fund u, Y.FN_fund u'⟩
  have hStd : Formalism.L2.SG.LocVol.StdHyp X.B.I.cm.sig X.B.I.J ψ :=
    ⟨MassDataVolumesW.stepCM X, MassDataVolumesW.stepHerm X, hI, hS⟩
  have hlat : ∃ L : Submodule (NumberField.RingOfIntegers X.B.I.E) (Fin X.B.I.n → X.B.I.E),
      Submodule.IsFullLattice X.B.I.E L ∧
      (L : Set (Fin X.B.I.n → X.B.I.E)) = (X.B.I.L : Set (Fin X.B.I.n → X.B.I.E)) :=
    ⟨X.B.I.L, ⟨{ toIsLattice := Submodule.IsLattice.of_fg X.B.I.E X.B.I.L_fg,
                     span_eq_top := X.B.I.L_span }, rfl⟩⟩
  have hdet' : (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.gramE X.B.I.cm.sig X.B.I.J
      (Formalism.L2.SG.Sub.tupH (Formalism.L2.SG.TypedSets.frameOf X u'))).det ≠ 0 :=
    Formalism.L2.SG.Pf.Rescale.standard_gram_nondegenerate X.B.I.F X.B.I.E X.B.I.cm.sig X.B.I.n X.B.I.J _ _ _
      (fun x => star_star x) hStd.2.1 (Formalism.L2.SG.Pf.Rescale.frame_stdX X u')
  have hPC := Formalism.L2.SG.Pf.ProdConvCut2.prodConv_holds_gen X hb ψ hI hS hLC u u'
  have hL := Formalism.L2.SG.LocVol.locTieX_of X ψ u (hLC u) (Formalism.L2.SG.Pf.LocVolPrim.primX X u locFramePrim)
  have hL' := Formalism.L2.SG.LocVol.locTieX_of X ψ u' (hLC u') (Formalism.L2.SG.Pf.LocVolPrim.primX X u' locFramePrim)
  have hTF := Formalism.L2.SG.Pf.typFacts_holds X hb u u'
  have hQ := Formalism.L2.SG.Pf.MassDataPos.quotVolPosC_of X hb Y u u' X0 ψ (Y.tO u u') 0 0 1 vR0 Q0 Y.M Y.δ i0 i0' νq hK2 hV
  have hN := Formalism.L2.SG.Pf.NcAllC.ncTieC_of_closed X hb Y.hK (Y.FN u) (Y.FN u') u u' X0 ψ (Y.tO u u') 0 0 1 vR0 Q0
    Y.M Y.δ i0 i0' νq Formalism.L2.SG.Closed.CovolRef_outright hSW hH hMC hStd hlat hdet' hdet hPC hL hL' hTF hQ le_rfl le_rfl
    one_pos hcong (Y.rowsOK u)
  have hρ := Formalism.L2.SG.MassDataConc.RhoTieC_closed X hb Y u u' X0 ψ 0 0 1 vR0 Q0 Y.M Y.δ i0 i0' νq
  have hal := Formalism.L2.SG.Pf.AlTie.locOf_al_eq X (Formalism.L2.SG.Pf.AlTie.etaTie_of X hLT) hk u u' ψ
  have hκ := Formalism.L2.SG.WConst.kapN_pos (D := D)
  have hng := Formalism.L2.SG.Pf.ngFac_pos D
  have hρp := Formalism.L2.SG.RhoPf.massRows_pos X Y u
  have hαp := Formalism.L2.SG.PoincareAmplitudeLowerBounds.tprod_alpD_pos D hk u u'
  refine ⟨hng, ?_⟩
  set B0 := Formalism.L2.SG.MassDataConc.bCF X hb Y.hK (Y.FN u) (Y.FN u') u u' X0 ψ (Y.tO u u') 0 0 1 vR0 Q0 Y.M Y.δ i0 i0' νq
    with hB0
  have eU : kapU D = Formalism.L2.SG.MassDataConc.kapN D := if_pos hκ
  have eA : (bkU X hb Y u u' X0 ψ sd C Th vR Q i0 i0' νq).AA = B0.AA / kapU D := by
    show B0.volB * (B0.Coo / kapU D) * (B0.MM / B0.volZZ) / B0.μK =
      B0.volB * B0.Coo * (B0.MM / B0.volZZ) / B0.μK / kapU D
    ring
  have en : B0.n0c = B0.AA / B0.ρ0 := rfl
  have eal : B0.al = ∏' q, Formalism.L2.SG.DataInst.alpD u u' q := hal
  have eρ : B0.ρ0 = Formalism.MainNotions.S.Cnt.massRows D (X.Fu u) (Y.what₂ u) := hρ
  have key : Formalism.L2.SG.Pf.Cnt.cExpl D (X.Fu u) (Y.what₂ u) =
      B0.n0c * Formalism.L2.SG.MassDataConc.ngFac D / (B0.al * Formalism.L2.SG.MassDataConc.kapN D) := hN
  rw [key, en, eρ, eal, eA, eU]
  field_simp

end GlobalTheory.CountConst
end

