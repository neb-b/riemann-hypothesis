module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0015
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0315
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0346
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0342
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0353
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0348
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0171
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.EqZeroOfInnerSmooth
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0006
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.BesselFormConvergesEquivariantHermitian
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0242
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0115
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0159
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0259
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0352
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0121
public import Development.AbelianVarietyTheory.Statements.CuspFrameWeights.Bundle0001
public import Development.AbelianVarietyTheory.Statements.CuspFrameWeights.DiscreteSpectrumKFiniteDecomposition
public import Formalism.HarderNarasimhan.ShiftInvariance
public import Formalism.RealPlaceAnalysis.FinalF
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0162
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0354
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0183
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0351
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0314
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0178
public import Formalism.SharpRestriction.CuspSpanNormBounds.RelevantZeroGramTerms
public import Formalism.PeriodIntegrals.Bundle0011
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0010
public import Development.AbelianVarietyTheory.Definitions.Jets.SumIoPr
public import Formalism.SharpRestriction.CuspSpanNormBounds.LeadMinorK
public import Formalism.LocalRingCardinality.Bundle0003
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0101
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0087
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0045
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0056
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0069
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0250
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0197
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.MomentPieriNumericsOfSizeHyps
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.DiscreteSeriesBesselGap
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LowerSmoothStability.ExistsFinStableOfMemSSup
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0039
public import Development.AbelianVarietyTheory.Statements.CuspFrameWeights.CuspFrame
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0229
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0185
public import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.RowsDef
public import CompanionTheory.HarishChandraModules.KFiniteAnalyticVectors.FundamentalDomainCusps.AutomorphicFormsFiniteDimensional

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.ColDictCoreHolds
section
open MeasureTheory NumberField IsDedekindDomain Matrix Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.ColDict GlobalTheory.St
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.St

theorem colDictCore_holds : ∀ D : D7, ColDictCore D := by
  intro D
  unfold ColDictCore
  intro X u F Tr hK hLev hStab

  have hConj : ∀ a, Tr.ιA (sigA X.B.I a) = Formalism.UG.sigR (Formalism.L2.Forms.sigD D)
      (FiniteAdeleRing (𝓞 D.host.F) D.host.F) (Tr.ιA a) :=
    GlobalTheory.St.G.IotaSigmaCompatibility.iotaA_sigA D X Tr.ιA ⟨Tr.ιA_rat, Tr.ιA_int⟩
  refine ⟨(_root_.GlobalTheory.ColClass.classes_and_weight D X u F Tr hK hConj hLev).1, _root_.GlobalTheory.St.colDictInto_of_levelMatch D X u F Tr hK hConj hLev,
    _root_.GlobalTheory.St.colDict_bij_of_levelMatch D X u F Tr hK hConj hLev, ?_⟩
  intro what₂ cs hinj hReps
  exact _root_.GlobalTheory.St.colDict_isometric_of_reps D X u F Tr hK hConj hLev hStab what₂ cs hinj hReps

end GlobalTheory.St
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.DerivativeAlongLieAlgebraPreservesSmoothSpaceStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Matrix
open scoped TensorProduct ContDiff
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.derivative_along_lie_algebra_preserves_smooth_space : ∀ (D : D7) (θ : D.what₂.Tau → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)) (V : HSp D), IsInfFam θ → ∀ W : Set (GA D V → ℂ), (∀ f ∈ W, Continuous f ∧ ∀ τ, ∃ L : Matrix (Fin V.rank) (Fin V.rank) ℂ → GA D V → ℂ, (∀ X ∈ lieAt V τ, L X ∈ W ∧ ∀ x, HasDerivAt (fun t : ℝ => f (x * oneP θ V τ X t)) (L X x) 0) ∧ ∀ (a : ℝ), ∀ X ∈ lieAt V τ, ∀ Y ∈ lieAt V τ, L (a • X + Y) = (a : ℂ) • L X + L Y) → ∀ f ∈ W, ∀ (k : ℕ) (τs : Fin k → D.what₂.Tau) (Xs : Fin k → Matrix (Fin V.rank) (Fin V.rank) ℂ), (∀ i, Xs i ∈ lieAt V (τs i)) → ∀ g, ContDiff ℝ ∞ fun t : Fin k → ℝ => f (g * (List.ofFn fun i => oneP θ V (τs i) (Xs i) (t i)).prod) := by
  first | exact @GlobalTheory.DerClosedSmooth.smooth_of_closed | exact GlobalTheory.DerClosedSmooth.smooth_of_closed | (intros; apply GlobalTheory.DerClosedSmooth.smooth_of_closed <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsContinuousBesselMapSmoothVectors
section
open MeasureTheory Matrix Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgInf
open scoped InnerProductSpace

namespace GlobalTheory.SgInf.BesselExt

variable {k r : ℕ}

theorem one_memG : (1 : Mat k r) ∈ GG k r := by
  show (1 : Mat k r)ᴴ * Hpk k r * 1 = Hpk k r
  simp

theorem mul_memG {x y : Mat k r} (hx : x ∈ GG k r) (hy : y ∈ GG k r) : x * y ∈ GG k r := by
  show (x * y)ᴴ * Hpk k r * (x * y) = Hpk k r
  have hx' : xᴴ * Hpk k r * x = Hpk k r := hx
  have hy' : yᴴ * Hpk k r * y = Hpk k r := hy
  calc (x * y)ᴴ * Hpk k r * (x * y) = yᴴ * (xᴴ * Hpk k r * x) * y := by
        rw [Matrix.conjTranspose_mul]; simp only [Matrix.mul_assoc]
    _ = Hpk k r := by rw [hx', hy']

section Sm
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

theorem smooth_add {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    {σ : Mat k r → (H →L[ℂ] H)} {u u' : H} (hu : IsSmoothVec σ u) (hu' : IsSmoothVec σ u') :
    IsSmoothVec σ (u + u') := by
  intro g₀ hg₀
  obtain ⟨U, F, hU, hg, hF, hFe⟩ := hu g₀ hg₀
  obtain ⟨U', F', hU', hg', hF', hFe'⟩ := hu' g₀ hg₀
  refine ⟨U ∩ U', F + F', hU.inter hU', ⟨hg, hg'⟩, (hF.mono Set.inter_subset_left).add
    (hF'.mono Set.inter_subset_right), fun g hg hgH => ?_⟩
  have e1 := hFe g hg.1 hgH
  have e2 := hFe' g hg.2 hgH
  simp only at e1 e2
  simp only [map_add (f := _), Pi.add_apply, e1, e2]

theorem smooth_smul {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    {σ : Mat k r → (H →L[ℂ] H)} {u : H} (b : ℂ) (hu : IsSmoothVec σ u) :
    IsSmoothVec σ (b • u) := by
  intro g₀ hg₀
  obtain ⟨U, F, hU, hg, hF, hFe⟩ := hu g₀ hg₀
  refine ⟨U, b • F, hU, hg, hF.const_smul b, fun g hg hgH => ?_⟩
  have e1 := hFe g hg hgH
  simp only at e1
  simp only [map_smul, Pi.smul_apply, e1]

end Sm

theorem ae_rtrans {B : Type*} {μG : Measure (Mt k r)} (hU : IsUnimod (GG k r) μG) {y : Mat k r}
    (hy : y ∈ GG k r) {f g : Mat k r → B}
    (h : (fun x : Mt k r => f (Matrix.of x)) =ᵐ[μG] fun x => g (Matrix.of x)) :
    (fun x : Mt k r => f (Matrix.of x * y)) =ᵐ[μG] fun x => g (Matrix.of x * y) := by
  have hmp : MeasurePreserving (rmulM y : Mt k r → Mt k r) μG μG :=
    ⟨(continuous_rmulM y).measurable, hU.1 y hy⟩
  exact hmp.quasiMeasurePreserving.ae_eq_comp h

theorem ae_ltrans {B : Type*} {μG : Measure (Mt k r)} (hH : IsHaarOn (GG k r) μG) {y : Mat k r}
    (hy : y ∈ GG k r) {f g : Mat k r → B}
    (h : (fun x : Mt k r => f (Matrix.of x)) =ᵐ[μG] fun x => g (Matrix.of x)) :
    (fun x : Mt k r => f (y * Matrix.of x)) =ᵐ[μG] fun x => g (y * Matrix.of x) := by
  have hc : Continuous (lmulM y : Mt k r → Mt k r) :=
    (continuous_const (y := y)).matrix_mul (continuous_id (X := Mat k r))
  have hmp : MeasurePreserving (lmulM y : Mt k r → Mt k r) μG μG :=
    ⟨hc.measurable, hH.2.2.2 y hy⟩
  exact hmp.quasiMeasurePreserving.ae_eq_comp h

end GlobalTheory.SgInf.BesselExt

open GlobalTheory.SgInf.BesselExt in
theorem GlobalTheory.SgInf.exists_besselExt : ∀ (k r : ℕ) {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] {Wp : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [FiniteDimensional ℂ Wp] [CompleteSpace Wp] (σ : Mat k r → (H →L[ℂ] H)) (w : H) (a : ℝ) (μG : Measure (Mt k r)) (d : ℝ) (z : Fin (2 * r + k + 1) → ℂ) (c : Fin r → ℂ) (π : Mat k r → (Wp →L[ℂ] Wp)) (μS : Measure (Mt k r)) , Std σ w a μG d → Side z π μS → IsSmoothVec σ w → ∀ v ∈ DD σ w, ∀ ξ : Wp, ∃ l : H → Wp, IsBesselMapSm z (psiGen k r z c) σ π l ∧ ∀ u ∈ DD σ w, l u = be (psiGen k r z c) π μS σ u v ξ := by
  intro k r H _ _ _ Wp _ _ _ _ σ w a μG d z c π μS hStd hSide hw v hv ξ
  obtain ⟨T, hTD, hadd, hsmul, hloc, hR, hL⟩ := _root_.GlobalTheory.SgInf.bessel_ext_bounded k r σ w a μG d z c π μS hStd hSide v hv ξ
  have hrep : IsURepOn (GG k r) σ := hStd.2.1
  have hHaar : IsHaarOn (GG k r) μG := hStd.2.2.2.2.1
  have hUni : IsUnimod (GG k r) μG := _root_.GlobalTheory.SgInf.isUnimod_GG k r μG hHaar
  have hDDi := _root_.GlobalTheory.SgInfDD.DD_stable_dense k r σ w hrep
  have hPi := _root_.GlobalTheory.SgInf.PiUnitary.piS_unitary k r z c π hSide.1 hSide.2.1 hSide.2.2.1
  obtain ⟨C, Ws, hWs, hreg⟩ := _root_.GlobalTheory.SgInf.reg_main k r σ μG T hrep hHaar hadd hsmul hloc hR
  classical
  let F : H → Mat k r → Wp := fun u => if h : IsSmoothVec σ u then (hreg u h).choose else 0
  have hF : ∀ u, IsSmoothVec σ u → ContinuousOn (F u) (GG k r) ∧
      (fun x : Mt k r => F u (Matrix.of x)) =ᵐ[μG] (fun x => T u (Matrix.of x)) ∧
      ‖F u 1‖ ≤ C * (Ws.map fun ws => ‖dsigW σ ws u‖).sum := by
    intro u hu
    have := (hreg u hu).choose_spec
    simp only [F, dif_pos hu]
    exact this
  have hDDsm : ∀ u ∈ DD σ w, IsSmoothVec σ u := fun u hu => (hDDi.2.2.2.2 hw).1 u (hDDi.2.2.1 hu)
  refine ⟨fun u => F u 1, ⟨?_, ?_, ?_, ?_⟩, ?_⟩
  · intro u hu u' hu'
    have hs := smooth_add hu hu'
    refine GlobalTheory.T.besselModel_eqOn_of_continuousOn_ae_eq k r μG (F (u + u')) (fun x => F u x + F u' x) hHaar (hF _ hs).1
      ((hF u hu).1.add (hF u' hu').1) ?_ 1 one_memG
    filter_upwards [(hF _ hs).2.1, hadd u u', (hF u hu).2.1, (hF u' hu').2.1] with x h1 h2 h3 h4
    rw [h1, h2, h3, h4]
  · intro b u hu
    have hs := smooth_smul b hu
    refine GlobalTheory.T.besselModel_eqOn_of_continuousOn_ae_eq k r μG (F (b • u)) (fun x => b • F u x) hHaar (hF _ hs).1
      ((hF u hu).1.const_smul b) ?_ 1 one_memG
    filter_upwards [(hF _ hs).2.1, hsmul b u, (hF u hu).2.1] with x h1 h2 h3
    rw [h1, h2, h3]
  · intro h hh m hm u hu
    have hhG : h ∈ GG k r := hh.1
    have hmG : m ∈ GG k r := hm.1
    have htG : h * m ∈ GG k r := mul_memG hhG hmG
    have htS : h * m ∈ Sset k r z := ⟨h, hh, m, hm, rfl⟩
    have hsu : IsSmoothVec σ (σ (h * m) u) := ((hDDi.2.2.2.1 u hu).1 _ htG)

    have h1 : ∀ x ∈ GG k r, F (σ (h * m) u) x = F u (x * (h * m)) := by
      refine GlobalTheory.T.besselModel_eqOn_of_continuousOn_ae_eq k r μG _ _ hHaar (hF _ hsu).1 ?_ ?_
      · exact (hF u hu).1.comp ((continuous_id.mul continuous_const).continuousOn)
          (fun x hx => mul_memG hx htG)
      · filter_upwards [(hF _ hsu).2.1, hR _ htG u, ae_rtrans hUni htG (hF u hu).2.1] with x h1 h2 h3
        rw [h1, h2, h3]

    have h2 : ∀ x ∈ GG k r, F u ((h * m) * x) = PiS (psiGen k r z c) π (h * m) (F u x) := by
      refine GlobalTheory.T.besselModel_eqOn_of_continuousOn_ae_eq k r μG (fun x => F u ((h * m) * x)) (fun x => PiS (psiGen k r z c) π (h * m) (F u x))
        hHaar ?_ ?_ ?_
      · exact (hF u hu).1.comp ((continuous_const.mul continuous_id).continuousOn)
          (fun x hx => mul_memG htG hx)
      · exact (PiS (psiGen k r z c) π (h * m)).continuous.comp_continuousOn (hF u hu).1
      · filter_upwards [ae_ltrans hHaar htG (hF u hu).2.1, hL _ htS u, (hF u hu).2.1] with x h1 h2 h3
        rw [h1, h2, h3]
    show F (σ (h * m) u) 1 = psiGen k r z c m • π h (F u 1)
    rw [h1 1 one_memG, Matrix.one_mul, ← Matrix.mul_one (h * m), h2 1 one_memG, (hPi.1 h hh m hm).2]
    rfl
  · refine ⟨C, Ws, hWs, fun u hu => (hF u hu).2.2⟩
  · intro u hu
    have hsu := hDDsm u hu
    have hcont : ContinuousOn (Afun (psiGen k r z c) π μS σ u v ξ) (GG k r) := by
      have hD1 := _root_.GlobalTheory.SgInf.BeForm.be_converges_equivariant_hermitian_continuous k r σ w a μG d z c π μS hStd hSide (DD σ w) hDDi.1 hStd.2.2.2.2.2.2.2.1 u hu v hv
      exact (ContinuousLinearMap.apply ℂ Wp ξ).continuous.comp_continuousOn hD1.2.2.2
    have := GlobalTheory.T.besselModel_eqOn_of_continuousOn_ae_eq k r μG (F u) _ hHaar (hF u hsu).1 hcont
      (by rw [← hTD u hu]; exact (hF u hsu).2.1) 1 one_memG
    show F u 1 = _
    rw [this]
    simp only [Afun, hrep.1.1, ContinuousLinearMap.one_apply]
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.IsStarProjectionOfIsOrthProjOnto
section
open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S Formalism.REAL Formalism.QuantumDeterminants GlobalTheory.Count GlobalTheory.Dec GlobalTheory.DSId
open scoped InnerProductSpace ComplexOrder ContDiff

noncomputable section

namespace GlobalTheory.Dec.ProjCuspGap

theorem rank_le_dim {n : ℕ} (ε : Fin n → Bool) : rkR ε ≤ n := by
  refine (min_le_left _ _).trans ((Finset.card_filter_le _ _).trans ?_)
  simp

theorem gap_numeric {n : ℕ} (ε : Fin n → Bool) (h : ℝ)
    (hh : 120 * (n : ℝ) * ((rkR ε : ℕ) : ℝ) ^ ((3 : ℝ) / 2) ≤ h) :
    rkR ε = 0 ∨ 8 * Real.sqrt (rkR ε) * (0 + 4 * n * rkR ε) < h := by
  rcases Nat.eq_zero_or_pos (rkR ε) with h0 | h0
  · exact Or.inl h0
  right
  have hq : (0 : ℝ) < rkR ε := by exact_mod_cast h0
  have hn : (0 : ℝ) < n := by exact_mod_cast h0.trans_le (rank_le_dim ε)
  have e : ((rkR ε : ℕ) : ℝ) ^ ((3 : ℝ) / 2) = Real.sqrt (rkR ε) * rkR ε := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_add_one hq.ne']
    norm_num
  rw [e] at hh
  have hp : 0 < (n : ℝ) * (Real.sqrt (rkR ε) * rkR ε) := by positivity
  nlinarith

theorem rank_pos_of_ne {n : ℕ} (ε : Fin n → Bool) {a b : Fin n} (hab : ε a ≠ ε b) : 0 < rkR ε := by
  unfold rkR
  refine lt_min (Finset.card_pos.2 ?_) (Finset.card_pos.2 ?_)
  · by_cases ha : ε a = true
    · exact ⟨a, by simp [ha]⟩
    · exact ⟨b, by revert hab ha; cases ε a <;> cases hb : ε b <;> simp [hb]⟩
  · by_cases ha : ε a = true
    · exact ⟨b, by revert hab ha; cases ε a <;> cases hb : ε b <;> simp [hb]⟩
    · exact ⟨a, by simp [ha]⟩

theorem two_mul_lt {n : ℕ} (ε : Fin n → Bool) (h : ℝ)
    (hh : 120 * (n : ℝ) * ((rkR ε : ℕ) : ℝ) ^ ((3 : ℝ) / 2) ≤ h) (h0 : 0 < rkR ε) : 2 * (n : ℝ) < h := by
  have hq : (1 : ℝ) ≤ rkR ε := by exact_mod_cast h0
  have hn : (0 : ℝ) < n := by exact_mod_cast h0.trans_le (rank_le_dim ε)
  have h1 : (1 : ℝ) ≤ ((rkR ε : ℕ) : ℝ) ^ ((3 : ℝ) / 2) := Real.one_le_rpow hq (by norm_num)
  nlinarith

theorem isStarProjection_of_isOrthProjOnto {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [CompleteSpace H] {T : H →L[ℂ] H} {S : Submodule ℂ H} (hT : IsOrthProjOnto T S) : IsStarProjection T :=
  ⟨hT.1, ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.2 fun x y => hT.2.1 x y⟩

theorem projector_rank_cuspidal : ∀ (B : RowsAut) (d : InfinitePlace B.I.F → ℝ) (h : ℝ), IsDSData B d → GapGe B h → (∀ v, 120 * (B.I.n : ℝ) * ((rkR (B.I.ε v) : ℕ) : ℝ) ^ ((3 : ℝ) / 2) ≤ h) → Integrable (ph B d) (muInf B.I) ∧ (HBig B 40 h → FiniteDimensional ℂ (B.I.eHom B.σs B.μf B.fund B.R B.Re) → ∀ T, B.I.IsRConv B.μf B.fund B.R (phe B d) T → IsStarProjection T ∧ FiniteDimensional ℂ (LinearMap.range (T : B.I.L2 B.μf B.fund →ₗ[ℂ] B.I.L2 B.μf B.fund)) ∧ Module.finrank ℂ (LinearMap.range (T : B.I.L2 B.μf B.fund →ₗ[ℂ] B.I.L2 B.μf B.fund)) = B.D ∧ ∀ Fv ∈ LinearMap.range (T : B.I.L2 B.μf B.fund →ₗ[ℂ] B.I.L2 B.μf B.fund), B.I.IsCuspFn (B.I.muA B.μf) (B.I.ext Fv)) := by
  intro B d h hds hgap hh
  have hD : DecGap := GlobalTheory.DecGapBound.decGap_of_formulaGap GlobalTheory.Jet.FormGapFree.formulaGap
  have hloc : LocDec B h := GlobalTheory.Dec.locDec_of_decGap_gapGe hD B d h hds hgap hh
  have hK : ∀ v, IsKTypeOf (B.I.ε v) (B.σ v) (lowK (B.I.ε v) (B.lam v))
      (lowKSub (B.I.ε v) (B.lam v) (B.σ v)) := fun v =>
    GlobalTheory.Jet.MultGap.isKTypeOf_lowKSub _ _ _ _ _ (hds v).1 (hds v).2.1 fun a b hab =>
      (two_mul_lt _ h (hh v) (rank_pos_of_ne _ hab)).trans_le (hgap v a b hab)
  obtain ⟨hc, hle, hint⟩ := GlobalTheory.Dec.PhMajProof.phMaj B d h hds hloc
  have hI := hint 0 le_rfl fun v => gap_numeric _ h (hh v)
  have hph : Integrable (ph B d) (muInf B.I) := by
    refine hI.mono' hc.aestronglyMeasurable (Filter.Eventually.of_forall fun g => ?_)
    simpa using hle g
  refine ⟨hph, fun hb hfin T hT => ?_⟩
  obtain ⟨h1, -, -, h4, h5⟩ := (GlobalTheory.GlobProj.globalProj_holds B d hds hph).2.2.2 T hT
  refine ⟨isStarProjection_of_isOrthProjOnto h1, h4 hfin, h5, ?_⟩
  rintro _ ⟨y, rfl⟩
  exact (_root_.GlobalTheory.Dec.range_cuspidal_of_lowKType B d h hds hK hh hloc hb hfin T hT y).2

end GlobalTheory.Dec.ProjCuspGap
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.KFinDense
section
open Formalism.MainNotions.S

namespace GlobalTheory.KFinDenseDS

theorem kFin_dense : ∀ (k r : ℕ) (ε : Fin (2 * r + k + 1) → Bool) (lam : Fin (2 * r + k + 1) → ℝ) (H : Type) [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] [CompleteSpace H] (σ : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ → (H →L[ℂ] H)),
    Formalism.QuantumDeterminants.IsHCParam lam → PI.UpqRep.IsDSHpk k r ε lam σ →
    ∀ v ∈ smoothVecs (k := k) (r := r) σ,
    ∀ Ws : List (List (Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ)), (∀ w ∈ Ws, ∀ X ∈ w, InLieHpk k r X) →
    ∀ δ : ℝ, 0 < δ → ∃ a : H, PI.UpqRep.IsKFinHpk (k := k) (r := r) σ a ∧
      (Ws.map fun w => ‖dsigW σ w (v - a)‖).sum < δ := by
  intro k r ε lam H _ _ _ σ hl hds v hv Ws hWs δ hδ
  obtain ⟨a, ha, hs⟩ := GlobalTheory.KFinAvg.kDense k r ε lam H σ hl hds v hv Ws hWs δ hδ
  refine ⟨a, ha, ?_⟩
  simpa only [Formalism.MainNotions.BridgeCS3d.dsigW_eq] using hs

end GlobalTheory.KFinDenseDS
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.MeasurableEmbeddingLmul
section
open BranchingSupport GlobalTheory.CellAmp GlobalTheory.Amp Formalism.BasicNotions Formalism.MainNotions.S Formalism.QuantumDeterminants Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal

namespace GlobalTheory.BesselSchur

theorem fdegHC_pos {n : ℕ} {mu : Fin n → ℝ} (h : StrictAnti mu) : 0 < Formalism.QuantumDeterminants.fdegHC mu := by
  unfold Formalism.QuantumDeterminants.fdegHC
  refine div_pos (Finset.prod_pos fun a _ => Finset.prod_pos fun b hb => ?_)
    (Finset.prod_pos fun a _ => Finset.prod_pos fun b hb => ?_)
  · have := h (Finset.mem_filter.1 hb).2
    exact abs_pos.2 (sub_ne_zero.2 this.ne')
  · have : (a : ℕ) < b := (Finset.mem_filter.1 hb).2
    have : ((a : ℕ) : ℝ) < ((b : ℕ) : ℝ) := by exact_mod_cast this
    linarith

theorem measurableEmbedding_lmul {k r : ℕ} {t : MatKR k r} (ht : IsUnit t.det) :
    MeasurableEmbedding (fun x : Mt k r => (fun i j => (t⁻¹ * Matrix.of x) i j : Mt k r)) := by
  have hc : ∀ s : MatKR k r, Continuous (fun x : Mt k r => (fun i j => (s * Matrix.of x) i j : Mt k r)) := fun s => by
    have h1 : Continuous (fun x : Mt k r => (Matrix.of x : MatKR k r)) := continuous_id
    exact continuous_const.matrix_mul h1
  let e : Mt k r ≃ᵐ Mt k r :=
    { toFun := fun x => fun i j => (t⁻¹ * Matrix.of x) i j
      invFun := fun x => fun i j => (t * Matrix.of x) i j
      left_inv := fun x => by
        show t * (t⁻¹ * Matrix.of x) = Matrix.of x
        rw [← Matrix.mul_assoc, Matrix.mul_nonsing_inv _ ht, Matrix.one_mul]
      right_inv := fun x => by
        show t⁻¹ * (t * Matrix.of x) = Matrix.of x
        rw [← Matrix.mul_assoc, Matrix.nonsing_inv_mul _ ht, Matrix.one_mul]
      measurable_toFun := (hc _).measurable
      measurable_invFun := (hc _).measurable }
  exact e.measurableEmbedding

theorem isBesselMapSm_of {k r : ℕ} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] {Wp : Type}
    [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] {z : Fin (2 * r + k + 1) → ℂ} {ψ : MatKR k r → ℂ}
    {σ : MatKR k r → (H →L[ℂ] H)} {π : MatKR k r → (Wp →L[ℂ] Wp)} {B : H → Wp} (h : IsBesselMapSm z ψ σ π B) :
    PI.BesselMapUniq.IsBesselMapSm (k := k) (r := r) z ψ σ π B := by
  have e : ∀ (w : List (MatKR k r)) (v : H), PI.UpqRep.dsigW (k := k) (r := r) σ w v = dsigW σ w v := fun w v => by
    induction w with
    | nil => rfl
    | cons X w ih => exact congrArg (dsig σ X) ih
  obtain ⟨h1, h2, h3, C, Ws, h4, h5⟩ := h
  refine ⟨h1, h2, h3, C, Ws, h4, fun v hv => ?_⟩
  simpa only [e] using h5 v hv

theorem theta_pos (D : D7) {τ : D.what₂.Tau} {w w' : D.what₂.Word} {θ : ℝ} {W : LocW D.R.k D.R.rS}
    (hv : 0 ≤ D.host.v) (hW : GoodW D τ w w' θ W) : 0 < θ := by
  by_contra hθ
  obtain ⟨-, -, -, -, -, -, hG, -, -, -, -, hN, q1, -⟩ := hW
  have hk : kapN D θ = 0 :=
    ENNReal.ofReal_eq_zero.2 (mul_nonpos_of_nonneg_of_nonpos (Real.rpow_nonneg (by positivity) _) (not_lt.1 hθ))
  have hN0 : W.μN = 0 := by rw [hN, hk]; unfold haarLie; exact zero_smul _ _
  have h1 := q1 (fun _ => 1) measurable_const
  rw [hN0] at h1
  simp only [muS, Measure.prod_zero, Measure.map_zero, lintegral_const, one_mul, Measure.coe_zero,
    Pi.zero_apply, zero_mul] at h1
  exact hG.2.1 (Measure.measure_univ_eq_zero.1 h1)

end GlobalTheory.BesselSchur
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.PtBoundAndFarBoundAndDecGap
section
namespace GlobalTheory.Deep

theorem ptBound_and_farBound_and_decGap :
    GlobalTheory.Deep.PtBound ∧ GlobalTheory.Deep.FarBound ∧ GlobalTheory.DSId.DecGap :=
  have hd : GlobalTheory.DSId.DecGap :=
    GlobalTheory.DecGapBound.decGap_of_formulaGap GlobalTheory.Jet.FormGapFree.formulaGap
  have hp : GlobalTheory.Deep.PtBound := GlobalTheory.Deep.ptBound_of_decGap hd
  ⟨hp, GlobalTheory.FarTerms.farBound_of_ptBound hp, hd⟩

end GlobalTheory.Deep
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.RowsFinDimLink
section
namespace GlobalTheory

theorem rowsFinDim_link : Formalism.L2.SG.RowsDef.RowsFinDim :=
  CompanionTheory.D.gk.RF.automorphic_forms_finite_dimensional

end GlobalTheory
end

