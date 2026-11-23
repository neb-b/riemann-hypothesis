module

public import Mathlib
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0006
public import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.DeRhamJacobian.IsdRJ
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0206
public import Development.WeilBound.CoreStatements.PlaceConnectedComponents.IsOpenQuotientMapArt0
public import GroundTheory.LocalFields.Bundle0016
public import GroundTheory.LocalFields.KroneckerWeber
public import GroundTheory.PAdicHodge.FieldOfNormsCyclBase
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0099
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0666
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0335
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ValuationLtOneOfEq
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0498
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0502
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ThetaNormCommutation.LocalComparisonSplitting.EulerFactorLevels.LocCompareSplit
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1232
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.T2SpaceFiniteAdeleRing
public import Development.WeilBound.CoreStatements.AutomorphicKernels.UnitarySchrodingerModel.UnitarySchrodingerLemmas.UnramifiedSchwartzDensity.SchCut
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0500
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0488
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0506
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0483

@[expose] public section

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsUniformizerGaloisAction
section
noncomputable section
open NumberField IsDedekindDomain Neutral.B1 Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.L2.Host Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations
open GlobalTheory.HeckeGal GlobalTheory.Pst GlobalTheory.TripleGal GlobalTheory.CompanionTheory.LTHodge
open scoped Classical
open ValuativeRel GroundTheory.LocalField GroundTheory.LocalField.FormalGroup
open scoped GroundTheory.PAdicHodge.CyclNorms

namespace GlobalTheory.CompanionTheory.LTHodge.UnitAct

section Ring

variable {l : ℕ} [Fact l.Prime] {K : FinExt l}
variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  [Algebra F (Om l)] [ValuativeExtension F (Om l)]

theorem valuation_le_one_iff (x : F) :
    valuation F x ≤ 1 ↔ ‖algebraMap F (Om l) x‖ ≤ 1 := by
  rw [← map_one (valuation F), ← (valuation F).vle_iff_le, ← ValuativeExtension.vle_iff_vle (B := Om l),
    GroundTheory.PAdicHodge.CyclNorms.vle_iff_norm_le, map_one, norm_one]

theorem exists_ringEquiv (hR : Set.range (algebraMap F (Om l)) = (K.1 : Set (Om l))) :
    ∃ ρ : 𝒪[F] ≃+* ↥(OL K), ∀ a : 𝒪[F],
      (((ρ a : ↥(OL K)) : ↥K.1) : Om l) = algebraMap F (Om l) (a : F) := by
  have hmem : ∀ a : 𝒪[F], algebraMap F (Om l) (a : F) ∈ K.1 := fun a => by
    have h : algebraMap F (Om l) (a : F) ∈ (K.1 : Set (Om l)) := hR ▸ ⟨_, rfl⟩
    exact h
  have hO : ∀ a : 𝒪[F], (⟨_, hmem a⟩ : ↥K.1) ∈ OL K := fun a =>
    (GlobalTheory.IntNormFinExt.mem_OL_iff_norm_le_one l K _).mpr ((valuation_le_one_iff (a : F)).mp a.2)
  let f : 𝒪[F] →+* ↥(OL K) :=
    { toFun := fun a => ⟨⟨_, hmem a⟩, hO a⟩
      map_one' := Subtype.ext (Subtype.ext (by simp))
      map_mul' := fun a b => Subtype.ext (Subtype.ext (by simp))
      map_zero' := Subtype.ext (Subtype.ext (by simp))
      map_add' := fun a b => Subtype.ext (Subtype.ext (by simp)) }
  have hinj : Function.Injective f := fun a b hab => by
    have h : algebraMap F (Om l) (a : F) = algebraMap F (Om l) (b : F) :=
      congrArg (fun c : ↥(OL K) => ((c : ↥K.1) : Om l)) hab
    exact Subtype.ext ((algebraMap F (Om l)).injective h)
  have hsurj : Function.Surjective f := fun b => by
    have hb : ((b : ↥K.1) : Om l) ∈ (K.1 : Set (Om l)) := (b : ↥K.1).2
    rw [← hR] at hb
    obtain ⟨y, hy⟩ := hb
    have hn : ‖algebraMap F (Om l) y‖ ≤ 1 := by
      rw [hy]
      exact (GlobalTheory.IntNormFinExt.mem_OL_iff_norm_le_one l K _).mp b.2
    exact ⟨⟨y, (valuation_le_one_iff y).mpr hn⟩, Subtype.ext (Subtype.ext hy)⟩
  exact ⟨RingEquiv.ofBijective f ⟨hinj, hsurj⟩, fun a => rfl⟩

theorem card_quot (ρ : 𝒪[F] ≃+* ↥(OL K)) {π : 𝒪[F]} (hπ : Irreducible π) :
    Nat.card (↥(OL K) ⧸ Ideal.span {ρ π}) = Nat.card 𝓀[F] := by
  have e1 : (𝒪[F] ⧸ Ideal.span {π}) ≃ (↥(OL K) ⧸ Ideal.span {ρ π}) :=
    (Ideal.quotientEquiv (Ideal.span {π}) (Ideal.span {ρ π}) ρ
      (by rw [Ideal.map_span, Set.image_singleton]; simp)).toEquiv
  have e2 : 𝓀[F] ≃ (𝒪[F] ⧸ Ideal.span {π}) :=
    (Ideal.quotEquivOfEq hπ.maximalIdeal_eq).toEquiv
  exact Nat.card_congr (e2.trans e1).symm

theorem map_ltPoly (ρ : 𝒪[F] ≃+* ↥(OL K)) {π : 𝒪[F]} (hπ : Irreducible π) :
    PowerSeries.map (ρ : 𝒪[F] →+* ↥(OL K)) (ltPoly π : PowerSeries 𝒪[F]) = ltSeries (ρ π) := by
  rw [ltSeries, card_quot ρ hπ, ltPoly]
  simp

end Ring

theorem main : ∀ {l : ℕ} [Fact l.Prime] {K : FinExt l} {χ : ↥(GK K) →* (↥K.1)ˣ}, IsLTChar K χ →
    ∀ {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
    [Algebra F (Om l)] [ValuativeExtension F (Om l)] [Algebra.IsAlgebraic F (Om l)],
    Set.range (algebraMap F (Om l)) = (K.1 : Set (Om l)) →
    ∃ (π : 𝒪[F]) (hπ : Irreducible π), ∀ (g : Om l ≃ₐ[F] Om l) (g' : ↥(GK K)), (∀ y, g y = (g' : GQ l) y) →
      ∃ u : 𝒪[F]ˣ, algebraMap F (Om l) ((u : 𝒪[F]) : F) = (((χ g' : (↥K.1)ˣ) : ↥K.1) : Om l) ∧
        ∀ n, ∀ x ∈ lubinTateTorsion (Om l) (hπ := hπ) (isLubinTateSeries_ltPoly π) n,
          lubinTateGalPointMap (hπ := hπ) (isLubinTateSeries_ltPoly π) g x = (u : 𝒪[F]) • x := by
  intro l _ K χ hχ F _ _ _ _ _ _ _ hR
  obtain ⟨πK, z, hπK, h0, h1, hs, hch⟩ := hχ
  obtain ⟨ρ, hρ⟩ := exists_ringEquiv (K := K) (F := F) hR
  have hρπ : ρ (ρ.symm πK) = πK := ρ.apply_symm_apply πK
  obtain ⟨π, hπdef⟩ : ∃ π : 𝒪[F], π = ρ.symm πK := ⟨_, rfl⟩
  rw [← hπdef] at hρπ
  have hπ : Irreducible π := hπdef ▸ (MulEquiv.irreducible_iff ρ.symm).mpr hπK
  have hf := isLubinTateSeries_ltPoly π
  have hcard : Nat.card (↥(OL K) ⧸ Ideal.span {πK}) = Nat.card 𝓀[F] := by
    have h := card_quot ρ hπ
    rwa [hρπ] at h
  have hcoe : ((πK : ↥K.1) : Om l) = algebraMap F (Om l) (π : F) := by
    rw [← hρ π, hρπ]
  have hs' : ∀ n, algebraMap F (Om l) (π : F) * z (n + 1) + z (n + 1) ^ Nat.card 𝓀[F] = z n :=
    fun n => by
      rw [← hcoe, ← hcard, add_comm]
      exact hs n
  have hv : ∀ n, valuation (Om l) (z n) < 1 := by
    intro n
    induction n with
    | zero => simp [h0]
    | succ n ih => exact CharEx.valuation_lt_one_of_eq hπ ih (hs' n)
  let Z : ℕ → IdealPoint (Om l) (lubinTateFormalGroup hπ hf) := fun n => IdealPoint.mk (z n) (hv n)
  have heval : ∀ (a : 𝒪[F]) (h : ↥(GK K)),
      (((ρ a : ↥(OL K)) : ↥K.1)) = ((χ h : (↥K.1)ˣ) : ↥K.1) →
      ∀ n, (a • Z n).val = (h : GQ l) (z n) := by
    intro a h ha n
    let Φ : PowerSeries 𝒪[F] := (lubinTateHom hπ hf hf a).toPowerSeries
    let ψ : PowerSeries ↥(OL K) := PowerSeries.map (ρ : 𝒪[F] →+* ↥(OL K)) Φ
    have hΦ0 : PowerSeries.constantCoeff Φ = 0 := (lubinTateHom hπ hf hf a).constantCoeff_eq_zero'
    have hψ0 : PowerSeries.constantCoeff ψ = 0 := by
      rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply, PowerSeries.coeff_map,
        PowerSeries.coeff_zero_eq_constantCoeff_apply, hΦ0, map_zero]
    have hψ1 : ((PowerSeries.coeff 1 ψ : ↥(OL K)) : ↥K.1) = ((χ h : (↥K.1)ˣ) : ↥K.1) := by
      rw [PowerSeries.coeff_map, coeff_one_lubinTateHom]
      exact ha
    have hF0 : PowerSeries.constantCoeff (ltPoly π : PowerSeries 𝒪[F]) = 0 :=
      hf.constantCoeff_eq_zero
    have hsub : PowerSeries.subst ψ (ltSeries πK) = PowerSeries.subst (ltSeries πK) ψ := by
      have h2 := congrArg (MvPowerSeries.map (ρ : 𝒪[F] →+* ↥(OL K)))
        (subst_lubinTateHom hπ hf hf a)
      rw [PowerSeries.map_subst (PowerSeries.HasSubst.of_constantCoeff_zero hΦ0),
        PowerSeries.map_subst (PowerSeries.HasSubst.of_constantCoeff_zero hF0)] at h2
      change PowerSeries.subst ψ (PowerSeries.map (ρ : 𝒪[F] →+* ↥(OL K)) (ltPoly π : PowerSeries 𝒪[F])) =
        PowerSeries.subst (PowerSeries.map (ρ : 𝒪[F] →+* ↥(OL K)) (ltPoly π : PowerSeries 𝒪[F])) ψ at h2
      rwa [map_ltPoly ρ hπ, hρπ] at h2
    have hsum := hch h ψ hψ0 hψ1 hsub n
    have hsum2 := CharEx.hasSum_coeff_mul_pow (K := F) Φ (hv n)
    rw [lubinTate_smul_val]
    refine hsum2.unique ?_
    convert hsum using 2 with k
    simp only [ψ, PowerSeries.coeff_map]
    rw [← hρ]
    rfl
  have hZ0 : Z 0 = 0 := IdealPoint.ext h0
  have hZ1 : Z 1 ≠ 0 := fun h => h1 (congrArg IdealPoint.val h)
  have hstep : ∀ n, π • Z (n + 1) = Z n := fun n => IdealPoint.ext (by
    rw [lubinTate_uniformizer_smul_val]
    change psEval ((ltPoly π : Polynomial 𝒪[F]) : PowerSeries 𝒪[F]) (fun _ => z (n + 1)) = z n
    rw [psEval_polynomial, aeval_ltPoly]
    exact hs' n)
  have hpow : ∀ n, π ^ n • Z (n + 1) = Z 1 := by
    intro n
    induction n with
    | zero => simp
    | succ n ih => rw [pow_succ, mul_smul, hstep, ih]
  have hunit : ∀ (a : 𝒪[F]) (h : ↥(GK K)),
      (((ρ a : ↥(OL K)) : ↥K.1)) = ((χ h : (↥K.1)ˣ) : ↥K.1) → IsUnit a := by
    intro a h ha
    by_contra hnu
    have hm := (IsLocalRing.mem_maximalIdeal a).mpr hnu
    rw [hπ.maximalIdeal_eq, Ideal.mem_span_singleton'] at hm
    obtain ⟨b, rfl⟩ := hm
    have h2 : (b * π) • Z 1 = 0 := by rw [mul_smul, hstep, hZ0, smul_zero]
    have h3 := heval _ h ha 1
    rw [h2] at h3
    exact h1 ((map_eq_zero_iff _ (h : GQ l).injective).mp h3.symm)
  refine ⟨π, hπ, fun g g' hg => ?_⟩
  obtain ⟨u, hu⟩ : ∃ u : 𝒪[F]ˣ,
      algebraMap F (Om l) ((u : 𝒪[F]) : F) = (((χ g' : (↥K.1)ˣ) : ↥K.1) : Om l) := by
    have hy : (((χ g' : (↥K.1)ˣ) : ↥K.1) : Om l) ∈ (K.1 : Set (Om l)) :=
      ((χ g' : (↥K.1)ˣ) : ↥K.1).2
    rw [← hR] at hy
    obtain ⟨y, hy⟩ := hy
    have hy0 : y ≠ 0 := by
      rintro rfl
      rw [map_zero] at hy
      exact (χ g').ne_zero (Subtype.ext hy.symm)
    rcases le_total (valuation F y) 1 with hle | hle
    · obtain ⟨w, hw⟩ := hunit ⟨y, hle⟩ g' (Subtype.ext (by rw [hρ]; exact hy))
      exact ⟨w, by rw [hw]; exact hy⟩
    · have hle' : valuation F y⁻¹ ≤ 1 := by
        rw [map_inv₀]
        exact inv_le_one_of_one_le₀ hle
      have hinv : (((χ (g'⁻¹) : (↥K.1)ˣ) : ↥K.1) : Om l) = algebraMap F (Om l) y⁻¹ := by
        rw [map_inv, map_inv₀, hy, Units.val_inv_eq_inv_val, IntermediateField.coe_inv]
      obtain ⟨w, hw⟩ := hunit ⟨y⁻¹, hle'⟩ g'⁻¹ (Subtype.ext (by rw [hρ, hinv]))
      refine ⟨w⁻¹, ?_⟩
      have hw2 : ((w : 𝒪[F]) : F) = y⁻¹ := by rw [hw]
      have hw3 : (((w⁻¹ : 𝒪[F]ˣ) : 𝒪[F]) : F) * ((w : 𝒪[F]) : F) = 1 := by
        have h5 : ((w⁻¹ : 𝒪[F]ˣ) : 𝒪[F]) * (w : 𝒪[F]) = 1 := Units.inv_mul w
        exact congrArg Subtype.val h5
      rw [hw2] at hw3
      rw [← hy, (eq_of_mul_inv_eq_one hw3)]
  refine ⟨u, hu, fun n x hx => ?_⟩
  have hgZ : lubinTateGalPointMap (hπ := hπ) hf g (Z (n + 1)) = (u : 𝒪[F]) • Z (n + 1) :=
    IdealPoint.ext (by
      rw [lubinTateGalPointMap_val, heval (u : 𝒪[F]) g' (Subtype.ext (by rw [hρ]; exact hu))]
      exact hg _)
  have hZt : Z (n + 1) ∈ lubinTateTorsion (Om l) (hπ := hπ) hf (n + 1) :=
    CharEx.mem_torsion hπ h0 hs' (n + 1) _ rfl
  have hZn : Z (n + 1) ∉ lubinTateTorsion (Om l) (hπ := hπ) hf (n + 1 - 1) := by
    rw [Nat.add_sub_cancel, mem_lubinTateTorsion, hpow]
    exact hZ1
  obtain ⟨-, hgen⟩ := primitive_spec hπ hf hZt hZn
  obtain ⟨a, rfl⟩ := hgen x (lubinTateTorsion_mono hπ hf n.le_succ hx)
  rw [map_smul, hgZ, smul_smul, smul_smul, mul_comm]

end GlobalTheory.CompanionTheory.LTHodge.UnitAct
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FibreVolumeCompactBound
section
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix
open GlobalTheory.CompanionTheory.WeilSiegel.Frame GlobalTheory.CompanionTheory.WeilSiegel.Free

namespace GlobalTheory.CompanionTheory.WeilSiegel.Free.FibreBound

theorem compactOpen_mass_le : ∀ (V K : Type) [TopologicalSpace V] [MeasurableSpace V] [BorelSpace V] [T2Space V] [TopologicalSpace K] [MeasurableSpace K] [BorelSpace K] [T2Space K] (μ : Measure V) (lam : Measure K) (Q : V → K) (Z : Set V) (m : K → Measure V), Continuous Q → Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.IsFibreFamily μ Q id Z lam Set.univ m → ∀ P : Set V, IsCompact P → IsOpen P → P ⊆ Z → ∃ c : ℝ≥0, ∀ S : Set K, MeasurableSet S → μ (P ∩ Q ⁻¹' S) ≤ (c : ℝ≥0∞) * lam S := by
  intro V K _ _ _ _ _ _ _ _ μ lam Q Z m hQ h P hPc hPo hPZ
  have hPm : MeasurableSet P := hPo.measurableSet
  let φ : V → ℝ := P.indicator fun _ => 1
  have hφc : Continuous φ := by
    refine continuous_indicator ?_ continuous_const.continuousOn
    simp [hPo.frontier_eq, hPc.isClosed.closure_eq]
  have hφs : HasCompactSupport φ := by
    refine HasCompactSupport.intro hPc fun x hx => ?_
    exact Set.indicator_of_notMem hx _
  have hts : tsupport φ ⊆ Z := by
    refine subset_trans (closure_minimal (fun x hx => ?_) hPc.isClosed) hPZ
    by_contra h
    exact hx (Set.indicator_of_notMem h _)
  obtain ⟨hI, hC⟩ := h.2.2 φ hφc hφs hts
  have hint : ∀ s, ∫ x, φ x ∂(m s) = (m s P).toReal := fun s => by
    simp [φ, integral_indicator hPm, Measure.real]
  have hfin : ∀ s, m s P ≠ ⊤ := fun s => by
    have h := hI s (Set.mem_univ s)
    rw [integrable_indicator_iff hPm] at h
    rcases (integrableOn_const_iff (C := (1 : ℝ)) (by simp)).1 h with h | h
    · simp at h
    · exact h.ne
  have hcont : ContinuousOn (fun s => (m s P).toReal) (Q '' P) := by
    have h' : ContinuousOn (fun s => (m s P).toReal) Set.univ := by
      simpa only [hint] using hC
    exact h'.mono (Set.subset_univ _)
  obtain ⟨C, hCb⟩ := (hPc.image hQ).exists_bound_of_continuousOn hcont
  have hoff : ∀ s, s ∉ Q '' P → m s P = 0 := fun s hs => by
    have hae := GlobalTheory.CompanionTheory.SiegelND.Coef.AvgV.ae_lift_eq h (g := Q) (fun _ => rfl) Function.injective_id s
    refine measure_mono_null (t := {x | ¬ Q x = s}) ?_ hae
    intro x hx hxs
    exact hs ⟨x, hx, hxs⟩
  have hbd : ∀ s, m s P ≤ (C.toNNReal : ℝ≥0∞) := fun s => by
    by_cases hs : s ∈ Q '' P
    · have h1 : (m s P).toReal ≤ C := le_trans (le_abs_self _) (by simpa using hCb s hs)
      rw [← ENNReal.ofReal_toReal (hfin s)]
      exact ENNReal.ofReal_le_ofReal h1
    · rw [hoff s hs]
      exact bot_le
  refine ⟨C.toNNReal, fun S hS => ?_⟩
  rw [GlobalTheory.CompanionTheory.SiegelND.Coef.AvgV.fibre_mass_on h (g := Q) (fun _ => rfl) Function.injective_id hQ.measurable hPm hS
    (fun x hx => hPZ hx.1)]
  calc ∫⁻ s in S, m s P ∂lam ≤ ∫⁻ _ in S, (C.toNNReal : ℝ≥0∞) ∂lam := lintegral_mono hbd
    _ = (C.toNNReal : ℝ≥0∞) * lam S := by rw [setLIntegral_const]

end GlobalTheory.CompanionTheory.WeilSiegel.Free.FibreBound
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FibreVolumeCompactLowerBound
section
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix
open GlobalTheory.CompanionTheory.WeilSiegel.Frame GlobalTheory.CompanionTheory.WeilSiegel.Free

noncomputable section

namespace GlobalTheory.CompanionTheory.WeilSiegel.FibreMass

theorem fibre_mass_le_of_pushforward : ∀ (V K : Type) [TopologicalSpace V] [MeasurableSpace V] [BorelSpace V] [T2Space V] [TopologicalSpace K] [MeasurableSpace K] [BorelSpace K] [T2Space K] (μ : Measure V) (lam : Measure K) (Q : V → K) (Z : Set V) (m : K → Measure V), Continuous Q → Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.IsFibreFamily μ Q id Z lam Set.univ m → ∀ [lam.IsOpenPosMeasure] [IsLocallyFiniteMeasure lam] (P : Set V), IsCompact P → IsOpen P → P ⊆ Z → ∀ c : ℝ≥0, (∀ S : Set K, MeasurableSet S → μ (P ∩ Q ⁻¹' S) ≤ (c : ℝ≥0∞) * lam S) → ∀ s, m s P ≤ (c : ℝ≥0∞) := by
  intro V K _ _ _ _ _ _ _ _ μ lam Q Z m hQ hfam _ _ P hPc hPo hPZ c hc s
  classical
  obtain ⟨hconc, hdis, hcont⟩ := hfam
  have hPm : MeasurableSet P := hPo.measurableSet
  have hφc : Continuous (P.indicator (fun _ => (1 : ℝ))) :=
    IsClopen.continuous_indicator ⟨hPc.isClosed, hPo⟩ continuous_const
  have hφs : HasCompactSupport (P.indicator (fun _ => (1 : ℝ))) :=
    HasCompactSupport.intro hPc (fun x hx => by simp [hx])
  have hφt : tsupport (P.indicator (fun _ => (1 : ℝ))) ⊆ Z :=
    (closure_minimal Set.support_indicator_subset hPc.isClosed).trans hPZ
  obtain ⟨hint, hgc⟩ := hcont _ hφc hφs hφt
  have hfin : ∀ b, m b P < ∞ := by
    intro b
    have h2 : IntegrableOn (fun _ => (1 : ℝ)) P (m b) :=
      (integrable_indicator_iff hPm).1 (hint b (Set.mem_univ b))
    exact ((integrableOn_const_iff (by simp)).1 h2).resolve_left (by simp)
  have hgeq : ∀ b, ∫ v, P.indicator (fun _ => (1 : ℝ)) v ∂(m b) = (m b P).toReal := by
    intro b
    rw [integral_indicator hPm, setIntegral_const]
    simp [Measure.real]
  have hgcont : Continuous (fun b => (m b P).toReal) := by
    have h := continuousOn_univ.1 hgc
    simpa only [hgeq] using h
  by_contra hlt
  rw [not_le] at hlt
  have hcs : (c : ℝ) < (m s P).toReal := by
    have h := (ENNReal.toReal_lt_toReal ENNReal.coe_ne_top (hfin s).ne).2 hlt
    simpa using h
  obtain ⟨d, hcd, hds⟩ := exists_between hcs
  obtain ⟨N, ⟨hsN, hNo⟩, hNfin⟩ := (lam.finiteAt_nhds s).exists_mem_basis (nhds_basis_opens s)
  have hWo : IsOpen ({b | d < (m b P).toReal} ∩ N) :=
    (isOpen_lt continuous_const hgcont).inter hNo
  have hWm : MeasurableSet ({b | d < (m b P).toReal} ∩ N) := hWo.measurableSet
  have hpos : lam ({b | d < (m b P).toReal} ∩ N) ≠ 0 :=
    (hWo.measure_pos lam ⟨s, hds, hsN⟩).ne'
  have hfinW : lam ({b | d < (m b P).toReal} ∩ N) ≠ ∞ :=
    ((measure_mono Set.inter_subset_right).trans_lt hNfin).ne
  have hAm : MeasurableSet (P ∩ Q ⁻¹' ({b | d < (m b P).toReal} ∩ N)) :=
    hPm.inter (hQ.measurable hWm)
  have key : ∀ b, m b (P ∩ Q ⁻¹' ({b | d < (m b P).toReal} ∩ N)) =
      ({b | d < (m b P).toReal} ∩ N).indicator (fun b => m b P) b := by
    intro b
    have hcb := hconc b
    rw [← measure_inter_conull hcb]
    by_cases hb : b ∈ ({b | d < (m b P).toReal} ∩ N)
    · rw [Set.indicator_of_mem hb, ← measure_inter_conull (s := P) hcb]
      congr 1
      ext v
      constructor
      · rintro ⟨⟨hvP, _⟩, hvT⟩
        exact ⟨hvP, hvT⟩
      · rintro ⟨hvP, hvT⟩
        refine ⟨⟨hvP, ?_⟩, hvT⟩
        have hQv : Q v = b := hvT.1
        show Q v ∈ ({b | d < (m b P).toReal} ∩ N)
        rw [hQv]
        exact hb
    · rw [Set.indicator_of_notMem hb]
      have hE : (P ∩ Q ⁻¹' ({b | d < (m b P).toReal} ∩ N)) ∩ (Q ⁻¹' {id b} ∩ Z) = ∅ := by
        ext v
        simp only [Set.mem_empty_iff_false, iff_false]
        rintro ⟨⟨_, hvW⟩, hvT⟩
        have hQv : Q v = b := hvT.1
        apply hb
        rw [← hQv]
        exact hvW
      rw [hE, measure_empty]
  have hlhs : ∫⁻ v in Z, (P ∩ Q ⁻¹' ({b | d < (m b P).toReal} ∩ N)).indicator 1 v ∂μ =
      μ (P ∩ Q ⁻¹' ({b | d < (m b P).toReal} ∩ N)) := by
    rw [lintegral_indicator_one hAm, Measure.restrict_apply hAm,
      Set.inter_eq_left.2 (Set.inter_subset_left.trans hPZ)]
  have hrhs : ∫⁻ b, ∫⁻ v, (P ∩ Q ⁻¹' ({b | d < (m b P).toReal} ∩ N)).indicator 1 v ∂(m b) ∂lam =
      ∫⁻ b in ({b | d < (m b P).toReal} ∩ N), m b P ∂lam := by
    simp_rw [lintegral_indicator_one hAm, key]
    rw [lintegral_indicator hWm]
  have hmain : ∫⁻ b in ({b | d < (m b P).toReal} ∩ N), m b P ∂lam ≤
      (c : ℝ≥0∞) * lam ({b | d < (m b P).toReal} ∩ N) := by
    rw [← hrhs, ← hdis _ (measurable_one.indicator hAm), hlhs]
    exact hc _ hWm
  have hlow : ENNReal.ofReal d * lam ({b | d < (m b P).toReal} ∩ N) ≤
      ∫⁻ b in ({b | d < (m b P).toReal} ∩ N), m b P ∂lam := by
    calc ENNReal.ofReal d * lam ({b | d < (m b P).toReal} ∩ N)
        = ∫⁻ _ in ({b | d < (m b P).toReal} ∩ N), ENNReal.ofReal d ∂lam :=
          (setLIntegral_const _ _).symm
      _ ≤ ∫⁻ b in ({b | d < (m b P).toReal} ∩ N), m b P ∂lam :=
          setLIntegral_mono' hWm (fun b hb => ENNReal.ofReal_le_of_le_toReal hb.1.le)
  have hd0 : 0 ≤ d := (NNReal.coe_nonneg c).trans hcd.le
  have h := ENNReal.toReal_mono (ENNReal.mul_ne_top ENNReal.coe_ne_top hfinW) (hlow.trans hmain)
  rw [ENNReal.toReal_mul, ENNReal.toReal_mul, ENNReal.toReal_ofReal hd0, ENNReal.coe_toReal] at h
  have hLpos : 0 < (lam ({b | d < (m b P).toReal} ∩ N)).toReal := ENNReal.toReal_pos hpos hfinW
  have h' : d ≤ (c : ℝ) := le_of_mul_le_mul_right h hLpos
  linarith

end GlobalTheory.CompanionTheory.WeilSiegel.FibreMass
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FiniteEulerProductOf
section
noncomputable section
open NumberField IsDedekindDomain Matrix Polynomial Filter
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host
open GlobalTheory.BCT
open scoped Classical
open PositivityTheory.Rg.BcB.G8 PositivityTheory.Rg.BcB.G8.Fin

namespace GlobalTheory.CompanionTheory.EulerAsm

theorem exists_above {E : Type} [Field E] [NumberField E] [IsCMField E] (v : PlF E) :
    ∃ w : Pl E, w.under (𝓞 (maximalRealSubfield E)) = v := by
  obtain ⟨Q, hQm, hQo⟩ := Ideal.exists_maximal_ideal_liesOver_of_isIntegral (S := 𝓞 E) v.asIdeal
  have hQ0 : Q ≠ ⊥ := Ideal.ne_bot_of_liesOver_of_ne_bot v.ne_bot Q
  refine ⟨⟨Q, hQm.isPrime, hQ0⟩, ?_⟩
  apply HeightOneSpectrum.ext
  exact (hQo.over).symm

theorem eulerFinOf' : EulerFinOf' := by
  intro hC hR hG hL hH hI E _ _ _ hU a b S hS φ₁ φ₂ h1 h2 δ₁ δ₂ e1 e2
  obtain ⟨hr, hth, hK, hKm⟩ := hR hC E a b
  have hKeq : (Kf E a).prod (Kf E b) = ⨅ v, (Kv (E := E) a b v).comap (pv a b v) := by
    ext x
    rw [Subgroup.mem_iInf]
    exact hKm x
  obtain ⟨H1, H2, H3, H4, H5⟩ := hH hC E hU a b S hS φ₁ φ₂ h1 h2 δ₁ δ₂ e1 e2
  set_option synthInstance.maxHeartbeats 200000 in
  have main := _root_.GlobalTheory.EulerAbs.twOrb_restr_eq_finprod (pv (E := E) a b) (Kv a b) hr (thP E a b) (thv a b) hth hK
    (ratF E a δ₁, ratF E b δ₂) (finFn S φ₁ φ₂) (fv S φ₁ φ₂) (hG E a b S hS φ₁ φ₂ h1 h2) H1 H2 H3 H4 H5
  rw [hKeq, main, hI E S hS]
  refine finprod_congr fun v => ?_
  have key : ∀ w ∈ S, w.under (𝓞 (maximalRealSubfield E)) = v →
      twOrb (thv a b v) (Kv a b v) (pv a b v (ratF E a δ₁, ratF E b δ₂)) (fv S φ₁ φ₂ v) =
        twOrb ((thL a w).prodMap (thL b w)) (K2 a b w) (locEl a w δ₁, locEl b w δ₂) (seen φ₁ φ₂ w) := by
    rintro w hw rfl
    exact hL hC E hU a b S hS φ₁ φ₂ h1 h2 δ₁ δ₂ e1 e2 w hw
  obtain ⟨w0, hw0⟩ := exists_above v
  have h : ∃ w ∈ S, w.under (𝓞 (maximalRealSubfield E)) = v := by
    obtain ⟨u, ⟨huS, hu⟩, -⟩ := hS w0
    exact ⟨u, huS, hu.trans hw0⟩
  simp only [secPl, dif_pos h, Option.elim]
  exact key _ h.choose_spec.1 h.choose_spec.2

end GlobalTheory.CompanionTheory.EulerAsm
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FinitePartOpen
section
noncomputable section
open HeckeCharacterZeroLocus.SiegelWeilU NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix

namespace GlobalTheory.CompanionTheory.SW.FinOpenGram

theorem finOpen : PositivityTheory.PfSWUS.SchInf.FinOpen := by
  intro F E _ _ _ _ _ σ hCM M J hJ n μ ν m hμ hν hm f hf hfin U hU hne
  have : BorelSpace (HermR (Ainf F) σ n) := ⟨rfl⟩
  by_contra hcon
  push Not at hcon
  have hpos : ν U ≠ 0 := (hU.measure_pos ν hne).ne'
  have h2 := hm
  unfold GlobalTheory.CompanionTheory.SW.IsGramFib Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.IsFibreFamily at h2
  have hfib := h2.2.1 f hf
  have hle : (⊤ : ℝ≥0∞) * ν U ≤ ∫⁻ S, ∫⁻ X, f X ∂(m S) ∂ν := by
    rw [← lintegral_indicator_const hU.measurableSet]
    refine lintegral_mono fun S => ?_
    by_cases hS : S ∈ U
    · rw [Set.indicator_of_mem hS, hcon S hS]
    · rw [Set.indicator_of_notMem hS]
      exact bot_le
  rw [ENNReal.top_mul hpos, top_le_iff, ← hfib] at hle
  exact hfin (top_le_iff.1 (hle ▸ setLIntegral_le_lintegral _ _))

end GlobalTheory.CompanionTheory.SW.FinOpenGram
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LeviNormalizesUnipotentTerStatement
section
open NumberField MeasureTheory Matrix Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet PositivityTheory.ThKR GlobalTheory.CompanionTheory.RedCov GlobalTheory.CompanionTheory.ParCocompact
open Formalism.UG (cT)
open scoped TensorProduct NNReal ENNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.levi_normalizes_unipotent_ter : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (n : ℕ) (J : Matrix (Fin n) (Fin n) E), IsHermND σ J → ∀ (r : ℕ) (X Y : Matrix (Fin n) (Fin r) E), IsWittFrame σ J X Y → ∀ m ∈ leviMin σ J X Y, ∀ u ∈ unipMin σ J X, m⁻¹ * u * m ∈ unipMin σ J X := by
  first | exact @GlobalTheory.CompanionTheory.ParCocompact.UnipNormal.leviMin_normalises_unipMin | exact GlobalTheory.CompanionTheory.ParCocompact.UnipNormal.leviMin_normalises_unipMin | (intros; apply GlobalTheory.CompanionTheory.ParCocompact.UnipNormal.leviMin_normalises_unipMin <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SmoothCutoffTranslateContDiffStatement
section
open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter GlobalTheory.CuspGeneric GlobalTheory.CuspRep PositivityTheory.jumpWindows PositivityTheory.AdelicQuotientData GroundTheory.Automorphic.FourierWhittaker GlobalTheory.CompanionTheory.CutOff
open scoped ContDiff
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.smooth_cutoff_translate_contDiff : ∀ {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] {k : ℕ} {φ : XB E k}, SmV (repI E k) φ → ∀ {b : (Fin k → Cinf E) → ℝ}, ContDiff ℝ ∞ b → (∀ x ∈ tsupport b, IsUnit (lastEnt x)) → ContDiff ℝ ∞ fun x => (b x : ℂ) • Rt E k (infGL E k (rowGL x))⁻¹ φ := by
  first | exact @GlobalTheory.CompanionTheory.CutOff.contDiff_cut_orbit | exact GlobalTheory.CompanionTheory.CutOff.contDiff_cut_orbit | (intros; apply GlobalTheory.CompanionTheory.CutOff.contDiff_cut_orbit <;> assumption)
end

