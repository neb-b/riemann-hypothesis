module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.ThetaMod
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0018
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0010
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.DepthZeroSupport
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0026
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0210
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0005
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0139
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.SplitExEveryDatum
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.CmFieldSplitPlaceEqOfPlaceEq
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PropEOfAdmissible
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0323
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0208
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0191
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0219
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SplitPlaceLocalComponentExistsUniqueClass
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.RingSpecNormalisedCharacterEq
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0228
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0008
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0078
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsIrreducibleFixed
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0416
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0196
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0841
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0834
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsAddHaarMeasureVolumeLie
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.StrongMultiplicityOne
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0025
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0020
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsCellPartUnfoldedIntegralPositive
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0618
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0763
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0808
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0828
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LintegralUnipotentCellPosLtTopContinuous
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0030
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0717
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsEquivariantProj
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0833
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0900
public import GroundTheory.AutomorphicForms.MultiplicityOne.Injective
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0846
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0840
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsIsLiftOfMemKO
public import Formalism.PadicSubsetSums.CentralIdempotents.Bundle0002
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0842

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DepthZeroOfHyp
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open scoped Pointwise

namespace GlobalTheory.DepthZeroType

theorem isSplitPl_of_over (D : D7) (k : Fin 2) (w : PlE D.host) (hw : w ∈ placesOver D.host.E (D.host.g k)) :
    IsSplitPl D.host w := by
  haveI : IsGalois ℚ D.host.E := D.host.hostE_isGalois
  have hP := (GlobalTheory.Mem.Chr.splitsC_place (p := D.host.g k) (D.host.g_prime k) (D.nd.g_split k) w hw).2.2
  by_contra hn
  have hle : ∀ x ∈ w.asIdeal, D.host.conj • x ∈ w.asIdeal := by
    intro x hx
    by_contra hy
    refine hn ⟨x, hx, fun y e hy' => hy ?_⟩
    have : y = D.host.conj • x := Subtype.ext e
    rwa [← this]
  refine GlobalTheory.TypePlace.conj_ne_one D.host (hP _ ?_)
  have h1 : D.host.conj • w.asIdeal ≤ w.asIdeal := by
    intro y hy
    rw [Ideal.mem_pointwise_smul_iff_inv_smul_mem] at hy
    simpa using hle _ hy
  have hm : (D.host.conj • w.asIdeal).IsMaximal :=
    Ideal.map_isMaximal_of_equiv (MulSemiringAction.toRingEquiv _ (𝓞 D.host.E) D.host.conj) (hp := w.isMaximal)
  exact hm.eq_of_le w.isMaximal.ne_top h1

theorem mem_Ine_of_wild (D : D7) (w : PlE D.host) {σ} (hσ : σ ∈ wildSet D.nd (D.nd.plOm.1 w)) :
    σ ∈ Ine (F := D.host.E) (D.nd.plOm.1 w) := GlobalTheory.TameGenPowers.wild_mem_Ine hσ

end GlobalTheory.DepthZeroType
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.EqOfOverTwo
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.MuUnrTie

theorem eq_of_over_two {E : Type} [Field E] [NumberField E] {p q : ℕ} (hp : p.Prime) (hq : q.Prime)
    (v : HeightOneSpectrum (𝓞 E)) (h1 : ((p : ℕ) : 𝓞 E) ∈ v.asIdeal) (h2 : ((q : ℕ) : 𝓞 E) ∈ v.asIdeal) : p = q := by
  by_contra hne
  have hc : Nat.Coprime p q := (Nat.coprime_primes hp hq).2 hne
  obtain ⟨a, b, h⟩ := (Nat.isCoprime_iff_coprime.2 hc).map (Int.castRingHom (𝓞 E))
  simp only [eq_intCast, Int.cast_natCast] at h
  apply v.isPrime.ne_top
  rw [Ideal.eq_top_iff_one, ← h]
  exact add_mem (Ideal.mul_mem_left _ _ h1) (Ideal.mul_mem_left _ _ h2)

theorem unrAt_inv {E : Type} [Field E] [NumberField E] {χ : HChar E} {w : HeightOneSpectrum (𝓞 E)}
    (h : χ.UnrAt w) : (χ⁻¹).UnrAt w := by
  exact HChar.UnrAt.inv h

end GlobalTheory.MuUnrTie
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsArchimedeanBumpIdealRowOrbitStatement
section
open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.CuspRep GlobalTheory.JSW GroundTheory.Global.IdeleGroup Formalism.L2.Host Formalism.UG GlobalTheory.LFun
open scoped ENNReal nonZeroDivisors Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_archimedeanBump_ideal_rowOrbit : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a : ℕ) (ℓ : Fin a)
    (T : Finset (HeightOneSpectrum (𝓞 E))) (U : Subgroup (GL (Fin a) (Af E))), IsOpen (U : Set (GL (Fin a) (Af E))) →
    ∃ (Φ : (Fin a → Cinf E) → ℂ) (J : (FractionalIdeal (𝓞 E)⁰ E)ˣ),
      ContDiff ℝ (⊤ : ℕ∞) Φ ∧ HasCompactSupport Φ ∧ tsupport Φ ⊆ GlobalTheory.RSTheta.rowSet E ℓ ∧
      (∀ u, 0 ≤ (Φ u).re ∧ (Φ u).im = 0) ∧ 0 < (Φ (Pi.single ℓ 1)).re ∧
      (∀ w ∉ T, FractionalIdeal.count E w (J : FractionalIdeal (𝓞 E)⁰ E) = 0) ∧
      ∀ y : Fin a → Af E, y - Pi.single ℓ 1 ∈ GlobalTheory.ThetaPoisson.latt a J →
        ∃ κ ∈ U, (∀ w, GeneralLinearGroup.map (pLoc E w) κ ∈ KGL w (n := a)) ∧
          (∀ w ∉ T, GeneralLinearGroup.map (pLoc E w) κ = 1) ∧
          ∀ w ∈ T, ∀ j, (GeneralLinearGroup.map (pLoc E w) κ : Matrix (Fin a) (Fin a) (w.adicCompletion E)) ℓ j = pLoc E w (y j) := by
  first | (exact @GlobalTheory.BumpOrbit.exists_bump_ideal_rowGL) | (exact GlobalTheory.BumpOrbit.exists_bump_ideal_rowGL) | (intros; apply GlobalTheory.BumpOrbit.exists_bump_ideal_rowGL  <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsCellPartUnfoldedIntegralPositiveStatement
section
open NumberField IsDedekindDomain MeasureTheory GlobalTheory.CuspRep Formalism.L2.Host Formalism.UG GlobalTheory.LFun
open scoped ENNReal ComplexConjugate nonZeroDivisors
open GlobalTheory.CellBump GlobalTheory.CellDec GlobalTheory.RSJ in
set_option synthInstance.maxHeartbeats 100000 in
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_cellPart_unfoldedIntegral_positive : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (m : ℕ)
    (S : Finset (HeightOneSpectrum (𝓞 E))) (b : GA E (m + 1) → ℂ) (φ : GA E (m + 1) → ℂ)
    (N : ℕ) (J : (FractionalIdeal (𝓞 E)⁰ E)ˣ) (Φ : (Fin (m + 1) → Cinf E) → ℂ),
    0 < N → (∀ v ∈ S, 0 < FractionalIdeal.count E v (J : FractionalIdeal (𝓞 E)⁰ E)) →
    (∀ z ∈ GlobalTheory.RSJ.natLat E N, ∀ v ∈ S,
        Valued.v (z v) ≤ WithZero.exp (-FractionalIdeal.count E v (J : FractionalIdeal (𝓞 E)⁰ E))) →
    Continuous Φ → HasCompactSupport Φ → tsupport Φ ⊆ GlobalTheory.RSTheta.rowSet E (Fin.last m) →
    (∀ u, 0 ≤ (Φ u).re ∧ (Φ u).im = 0) → Φ (Pi.single (Fin.last m) 1) ≠ 0 →
    Continuous (GlobalTheory.JSW.whit φ) →
    (∀ u ∈ GlobalTheory.JSW.NA (E := E) (a := (m + 1)), ∀ g, GlobalTheory.JSW.whit φ (u * g) = GlobalTheory.JSW.psiN u * GlobalTheory.JSW.whit φ g) →
    (∀ κ ∈ GlobalTheory.RSLocalPart.levelAt (m + 1) S J, ∀ g, GlobalTheory.JSW.whit φ (g * finGL E (m + 1) κ) = GlobalTheory.JSW.whit φ g) →
    b 1 = 1 → (∃ C : Set (GA E (m + 1)), IsCompact C ∧ ∀ p ∈ (GlobalTheory.JSW.supS (E := E) (a := m + 1) S ∩ GlobalTheory.JSW.mirSet (GlobalTheory.CuspRep.Ad E) m), b p ≠ 0 →
      ∃ u ∈ GlobalTheory.JSW.NA (E := E) (a := (m + 1)), u⁻¹ * p ∈ C) →
    (∀ p ∈ (GlobalTheory.JSW.supS (E := E) (a := m + 1) S ∩ GlobalTheory.JSW.mirSet (GlobalTheory.CuspRep.Ad E) m), GlobalTheory.JSW.whit φ p = b p) →
    ∀ (μ : Measure (GA E (m + 1))) [μ.IsHaarMeasure] (𝓕₀ : Set (GA E (m + 1))),
    IsFundamentalDomain (GlobalTheory.CellDec.NE E (m + 1)) 𝓕₀ μ →
    ∃ f t : GA E (m + 1) → ℝ, Measurable f ∧ Measurable t ∧ (∀ g, 0 ≤ f g) ∧ IntegrableOn f 𝓕₀ μ ∧
      0 < ∫ g in 𝓕₀, f g ∂μ ∧ (∃ R : ℝ, ∀ g, f g ≠ 0 → |t g| ≤ R) ∧
      (∀ g ∉ GlobalTheory.CellDec.C0 E (m + 1) S, f g = 0) ∧
      (∀ g ∈ GlobalTheory.CellDec.C0 E (m + 1) S, GlobalTheory.ZEul.uInt φ φ Φ N 0 g = (f g : ℂ)) ∧
      ∀ (x : ℝ) (g : GA E (m + 1)), (GlobalTheory.RSJ.detPow E (m + 1) x g : ℂ) = Complex.exp (x * t g) := by
  intro E _ _ _ m S b φ N J Φ hN0 hJ hNJ hΦ hΦc hs hΦr hΦ1 hWc hN hK hb1 hb hW μ _ 𝓕₀ h𝓕
  have hO := isOpen_adelicUnipotentTimesIntegralOutsideSet E (m + 1) S
  have hre := fun g => uInt_self_zero hΦr φ N g
  have hc : Continuous (GlobalTheory.ZEul.uInt φ φ Φ N 0) := continuous_uInt hN0 hWc hWc hΦ hs 0
  have hBc : Continuous fun g => (GlobalTheory.ZEul.uInt φ φ Φ N 0 g).re := Complex.continuous_re.comp hc
  obtain ⟨K, hKc, hKs⟩ := exists_compact_support hJ hNJ hΦc hs hN hK hb hW

  have hS1 : (1 : GA E (m + 1)) ∈ (GlobalTheory.JSW.supS (E := E) (a := m + 1) S ∩ GlobalTheory.JSW.mirSet (GlobalTheory.CuspRep.Ad E) m) :=
    ⟨fun w _ => map_one _, fun j => by simp [Matrix.one_apply, eq_comm]⟩
  have hy1 : (fun i => pInf E (GlobalTheory.ZEul.lastRow (1 : GA E (m + 1)) i)) = Pi.single (Fin.last m) 1 := by
    funext i
    by_cases h : i = Fin.last m
    · subst h; simp [GlobalTheory.ZEul.lastRow]
    · simp [GlobalTheory.ZEul.lastRow, Matrix.one_apply_ne (Ne.symm h), h]
  have hyl : (Pi.single (Fin.last m) 1 : Fin (m + 1) → Cinf E) = GlobalTheory.RSJ.Model.eLast (Cinf E) (m + 1) := by
    funext i; rw [single_last_eq]; rfl
  have hf1 : indN N (fun i => GlobalTheory.RSJ.pFin E (GlobalTheory.ZEul.lastRow (1 : GA E (m + 1)) i)) = 1 := by
    unfold indN
    refine ite_eq_left fun i => ?_
    have : GlobalTheory.RSJ.pFin E (GlobalTheory.ZEul.lastRow (1 : GA E (m + 1)) i) = if (i : ℕ) + 1 = m + 1 then 1 else 0 := by
      rw [← single_last_eq (R := Af E)]
      by_cases h : i = Fin.last m
      · subst h; simp [GlobalTheory.ZEul.lastRow]
      · simp [GlobalTheory.ZEul.lastRow, Matrix.one_apply_ne (Ne.symm h), h]
    show GlobalTheory.RSJ.pFin E (GlobalTheory.ZEul.lastRow (1 : GA E (m + 1)) i) - _ ∈ _
    rw [this, sub_self]
    exact ⟨0, fun v => zero_mem _, by simp⟩
  have hB1 : 0 < (GlobalTheory.ZEul.uInt φ φ Φ N 0 1).re := by
    have e : GlobalTheory.ZEul.uInt φ φ Φ N 0 1 = Φ (Pi.single (Fin.last m) 1) := by
      change GlobalTheory.JSW.whit φ (1 * infGL E (m + 1) (secInv fun i => pInf E (GlobalTheory.ZEul.lastRow (1 : GA E (m + 1)) i))) *
        conj (GlobalTheory.JSW.whit φ (1 * infGL E (m + 1) (secInv fun i => pInf E (GlobalTheory.ZEul.lastRow (1 : GA E (m + 1)) i)))) *
        Φ (fun i => pInf E (GlobalTheory.ZEul.lastRow (1 : GA E (m + 1)) i)) *
        indN N (fun i => GlobalTheory.RSJ.pFin E (GlobalTheory.ZEul.lastRow (1 : GA E (m + 1)) i)) *
        (detPow E (m + 1) 0 1 : ℂ) = _
      rw [hf1, hy1, hyl, GlobalTheory.RSJ.Model.secInv_eLast, map_one, one_mul, hW 1 hS1, hb1, detPow_eq, ← hyl]
      simp
    rw [e]
    refine lt_of_le_of_ne (hΦr _).1 fun h => hΦ1 (Complex.ext h.symm (hΦr _).2)

  obtain ⟨hpos, -⟩ := GlobalTheory.RSLocalPart.lintegral_cell_pos_lt_top_continuous E (m + 1) μ S 𝓕₀ h𝓕
    (fun _ g => (GlobalTheory.ZEul.uInt φ φ Φ N 0 g).re) (hBc.comp continuous_snd) (fun _ g => (hre g).2) (fun _ => hB1)
    (fun _ u hu g => by simp only [uInt_unip_mul hN Φ N 0 hu g])
    ⟨K, hKc, fun _ g hg h0 => hKs g hg fun h => h0 (by rw [h, Complex.zero_re])⟩
  obtain ⟨hlpos, hltop⟩ := hpos 0
  have hIB : IntegrableOn (fun g => (GlobalTheory.ZEul.uInt φ φ Φ N 0 g).re) (𝓕₀ ∩ C0 E (m + 1) S) μ :=
    ⟨hBc.aestronglyMeasurable, (hasFiniteIntegral_iff_ofReal (ae_of_all _ fun g => (hre g).2)).2 hltop⟩

  set t : GA E (m + 1) → ℝ := fun g => GlobalTheory.Mem.Chr.CharModel.logNorm E (Matrix.GeneralLinearGroup.det g) with ht
  have htc : Continuous t := (GlobalTheory.Mem.Chr.CharModel.continuous_logNorm E).comp Matrix.GeneralLinearGroup.continuous_det
  have htu : ∀ u ∈ NA E (m + 1), ∀ g, t (u * g) = t g := fun u hu g => by
    simp only [ht, map_mul, show Matrix.GeneralLinearGroup.det u = 1 from Units.ext (GlobalTheory.RSLocalPart.det_eq_one hu),
      one_mul]
  obtain ⟨R, hR⟩ := hKc.exists_bound_of_continuousOn htc.continuousOn
  refine ⟨(C0 E (m + 1) S).indicator fun g => (GlobalTheory.ZEul.uInt φ φ Φ N 0 g).re, t,
    hBc.measurable.indicator hO.measurableSet, htc.measurable,
    fun g => Set.indicator_nonneg (fun g _ => (hre g).2) g, ?_, ?_, ⟨R, fun g hg => ?_⟩,
    fun g hg => Set.indicator_of_notMem hg _, fun g hg => ?_, fun x g => ?_⟩
  · unfold IntegrableOn
    rw [integrable_indicator_iff hO.measurableSet]
    unfold IntegrableOn
    rw [Measure.restrict_restrict hO.measurableSet, Set.inter_comm]
    exact hIB
  · rw [integral_indicator hO.measurableSet, Measure.restrict_restrict hO.measurableSet, Set.inter_comm,
      integral_eq_lintegral_of_nonneg_ae (ae_of_all _ fun g => (hre g).2) hBc.aestronglyMeasurable]
    exact ENNReal.toReal_pos hlpos.ne' hltop.ne
  · have hgC : g ∈ C0 E (m + 1) S := by
      by_contra h
      exact hg (Set.indicator_of_notMem h _)
    rw [Set.indicator_of_mem hgC] at hg
    obtain ⟨u, hu, hk⟩ := hKs g hgC fun h => hg (by rw [h, Complex.zero_re])
    have := hR _ hk
    rwa [htu u hu, Real.norm_eq_abs] at this
  · rw [Set.indicator_of_mem hg]
    exact (hre g).1
  · rw [detPow_eq, Complex.ofReal_exp]
    push_cast
    rfl
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsCoefScale
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.ExportSeries GlobalTheory.ConjTwist

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.CoefLatConj

open MvPolynomial


set_option maxHeartbeats 800000 in
set_option synthInstance.maxHeartbeats 400000 in
open GlobalTheory.SeriesTie.Scale in
theorem exists_coef_scale : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T0 : Type) (A : FamIn D.what₂.LL G Pl0 T0 D.R.m) (T : CoreJ D) [Algebra T.Q.c.F D.what₂.LL] (R : RealDat D A T.Q.c.F) (F : Face D A) (κw : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)) (v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec) (O : ∀ i, OMDat T.toCore R i Unit (fun _ => A.μ0)), GlobalTheory.Hk3.Core R F → Nonempty (FWTie T R κw v₀) → IoExt R → ∀ i : Fin D.R.m, OMPins T R κw v₀ O i → ∀ (c : VsV D i ℂ →ₗ[ℂ] (R.cV i).W), ExtC R i (inC (O i).c') (O i).c0' c → ∀ u : (∀ ρ, lowT (R.MW i (sg0 D A)) ρ), (∀ ρ, (u ρ : (R.MW i (sg0 D A)).sm ρ) = v₀ i (sg0 D A) ρ) → ∀ (B : Base (Vc D i) (Wc D i)), B.Good → BaseOf R i B → ∃ κ : ℂ, κ ≠ 0 ∧ (∀ x : VsV D i ℂ, R.ioP i (PiTensorProduct.tprod ℂ u) (c x) ∈ B.valSpace) ∧ ∀ x : VsV D i ℂ, harmFn (Wc D i).rank B.w B.F.BS (R.ioP i (PiTensorProduct.tprod ℂ u) (c x)) = κ • coefFn (RingHom.id ℂ) (lamV D i) (x : Pol ℂ D.what₂.Tau (Vc D i).rank) := by
  intro D G _ _ Pl0 T0 A T _ R F κw v₀ O hC _ hio i hO c hc u hu B hB hBo
  have hcV : (R.cV i).Is := hC.models.cV i
  have hinf : IsInfFam R.θ := hBo.θ ▸ hB.frame.vac.2.inf

  obtain ⟨gramR, c0R, c0L, hft, hbc⟩ := hO.2.lift.c0
  have hfield : (inC (O i).c').comp (O i).jL = D.what₂.embLL := hO.2.lift.field
  obtain ⟨e, he0, he⟩ := GlobalTheory.CoefReal.exists_real_model (Vc D i) R.θ (R.cV i) (lamV D i) (c0L i) hinf hcV (hft.mapL i)
  have hce : c = e.toLinearMap := by
    refine LinearMap.ext_on_range (GlobalTheory.CoefModel.span_mapVV D.what₂.embLL (lamV D i)) fun k => ?_
    obtain ⟨v', hv', hv0⟩ := hbc (bVV D.what₂.LL (lamV D i) k)
    refine (hc v' _ ?_).trans (hv0.trans (he0 _).symm)
    change MvPolynomial.map D.what₂.embLL _ = _
    rw [hv', MvPolynomial.map_map, hfield]

  obtain ⟨u', w₀, hu', -, hw⟩ := FWT.IsChosenExtremalVector.io _ hO.2.lift.v0 hio
  have huu : u' = u := funext fun ρ => Subtype.ext ((hu' ρ).trans (hu ρ).symm)
  rw [huu] at hw

  have hT := io_act hC.lev hC.thP hB hBo.ψ hBo.θ hBo.sT hBo.BS hBo.BT hBo.mu0 hBo.eta (PiTensorProduct.tprod ℂ u)
  have hlam : B.w.lam = lamV D i := hBo.lam
  have hΔ : B.w.delta (Wc D i).rank = RealDat.Delta i := hBo.delta
  have hpq := GlobalTheory.CoefLatConj.pq_le hB
  have hirr : ∀ U : Submodule ℂ (R.cV i).W, (∀ h : GinfC (Vc D i), U.map ((R.cV i).ρ h) ≤ U) → U = ⊥ ∨ U = ⊤ :=
    fun U hU => hcV.2.2.2.2 U fun h => by
      obtain ⟨a, ha, k, hk, rfl⟩ := (GlobalTheory.UnitarySplit.real_finite_split D _).1 h
      rw [map_mul, hcV.1 k hk, mul_one]
      exact hU ⟨a, ha⟩
  have hΔ0 := GlobalTheory.AdTh.IoExtPf.Delta_ne (D := D) i
  set x := PiTensorProduct.tprod ℂ u
  have hharm : ∀ w, R.ioP i x w ∈ harm (Wc D i).rank B.w B.F.BS := by
    rcases hirr ((harm (Wc D i).rank B.w B.F.BS).comap (R.ioP i x)) (fun h => by
      rintro _ ⟨w, hw', rfl⟩
      rw [Submodule.mem_comap, hT h h.2]
      exact fockGL_mem_harm _ _ _ hw') with h | h
    · have h0 : w₀ ∈ (harm (Wc D i).rank B.w B.F.BS).comap (R.ioP i x) := by
        rw [Submodule.mem_comap, hw, ← hΔ]
        exact delta_mem_harm _ _
      rw [h, Submodule.mem_bot] at h0
      rw [h0, map_zero] at hw
      exact absurd hw.symm hΔ0
    · exact fun w => (h ▸ Submodule.mem_top : w ∈ (harm (Wc D i).rank B.w B.F.BS).comap (R.ioP i x))

  haveI := hcV.2.2.2.1
  obtain ⟨κ, hcc⟩ := _root_.GlobalTheory.schur_proportional (GinfC (Vc D i)) (R.cV i).W (GLR D (Vc D i).rank → ℂ) (fun h => (R.cV i).ρ h)
    (fun h => LinearMap.funLeft ℂ ℂ fun y => (realGL R.θ (Vc D i) h)⁻¹ * y)
    (harmFn (Wc D i).rank B.w B.F.BS ∘ₗ R.ioP i x) (coefLin (lamV D i) ∘ₗ e.symm.toLinearMap) hirr
    ((coefLin_injective _).comp e.symm.injective)
    (by
      rintro _ ⟨w, rfl⟩
      have h1 : harmFn (Wc D i).rank B.w B.F.BS (R.ioP i x w) ∈
          (harm (Wc D i).rank B.w B.F.BS).map (harmFn (Wc D i).rank B.w B.F.BS) := Submodule.mem_map_of_mem (hharm w)
      rw [GlobalTheory.T.fockHarmonicValueSpace_map_eq_dualWeylModuleFunctions D _ _ B.w B.F.BS hB.wt hpq, hlam] at h1
      refine Submodule.span_le.2 ?_ h1
      rintro _ ⟨G', rfl⟩
      exact ⟨e G', congrArg (coefLin _) (e.symm_apply_apply G')⟩)
    (fun h w => funext fun y => by
      change harmFn _ B.w B.F.BS (R.ioP i x ((R.cV i).ρ h w)) y = harmFn _ B.w B.F.BS (R.ioP i x w) _
      rw [hT h h.2, ← hBo.θ]
      exact harmFn_fockGL _ _ _ _ _)
    (fun h w => funext fun y => by
      obtain ⟨v, rfl⟩ := e.surjective w
      change coefLin _ (e.symm ((R.cV i).ρ h (e v))) y = coefLin _ (e.symm (e v)) _
      rw [he h h.2, e.symm_apply_apply, e.symm_apply_apply]
      exact coefFn_translate _ _ _ _)
  subst hce
  refine ⟨κ, fun h0 => hΔ0 ?_, fun y => hharm _, fun y => ?_⟩
  · have h1 := LinearMap.congr_fun hcc w₀
    rw [h0, zero_smul, LinearMap.comp_apply, hw] at h1
    exact _root_.GlobalTheory.ExportSeries.HarmInj.harm_inj D _ _ B.w B.F.BS hB.wt hpq _ (hw ▸ hharm w₀) h1
  · have h1 := LinearMap.congr_fun hcc (e y)
    simp only [LinearMap.comp_apply, LinearMap.smul_apply, LinearEquiv.coe_coe, LinearEquiv.symm_apply_apply] at h1
    exact h1


set_option maxHeartbeats 4000000 in
theorem coefLat_conj : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T0 : Type) (A : FamIn D.what₂.LL G Pl0 T0 D.R.m) (T : CoreJ D) [Algebra T.Q.c.F D.what₂.LL] (R : RealDat D A T.Q.c.F) (F : Face D A) (κw : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)) (v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec) (O : ∀ i, OMDat T.toCore R i Unit (fun _ => A.μ0)), GlobalTheory.Hk3.Core R F → Nonempty (FWTie T R κw v₀) → IoExt R → ∀ i : Fin D.R.m, OMPins T R κw v₀ O i → ∀ (c : VsV D i ℂ →ₗ[ℂ] (R.cV i).W), ExtC R i (inC (O i).c') (O i).c0' c → ∀ u : (∀ ρ, lowT (R.MW i (sg0 D A)) ρ), (∀ ρ, (u ρ : (R.MW i (sg0 D A)).sm ρ) = v₀ i (sg0 D A) ρ) → ∀ (B : Base (Vc D i) (Wc D i)), B.Good → BaseOf R i B → ∃ κ : ℂ, κ ≠ 0 ∧ (∀ x : VsV D i ℂ, harmFn (Wc D i).rank B.w B.F.BS (R.ioP i (PiTensorProduct.tprod ℂ u) (c x)) = κ • coefFn (RingHom.id ℂ) (lamV D i) (x : Pol ℂ D.what₂.Tau (Vc D i).rank)) ∧ (∀ P ∈ B.valSpace, ∃! x : VsV D i ℂ, P = R.ioP i (PiTensorProduct.tprod ℂ u) (c x)) ∧ ∀ (K : Type) [Field K] [NumberField K] (σ : K →+* ℂ) (emb : D.what₂.Tau → (D.host.E →+* K)) (Oc : Subring ℂ), IsCoefRing σ emb Oc → (∀ h : Bridge.Gf (Vc D i), B.coefLat σ emb Oc h = Submodule.span Oc {P | ∃ Fv ∈ nabAtr emb (lamV D i) (B.latAt h), P = R.ioP i (PiTensorProduct.tprod ℂ u) (c (κ⁻¹ • GlobalTheory.CoefModel.mapVV σ (lamV D i) Fv))}) ∧ ∀ τ : ℂ ≃+* ℂ, (∀ a : K, τ (σ a) = σ a) → (∀ (h : Bridge.Gf (Vc D i)) (x x' : VsV D i ℂ), ConjVec i τ x x' → (R.ioP i (PiTensorProduct.tprod ℂ u) (c x) ∈ B.coefLat σ emb Oc h ↔ R.ioP i (PiTensorProduct.tprod ℂ u) (c ((τ κ / κ) • x')) ∈ B.coefLat σ emb (Oc.map (τ : ℂ →+* ℂ)) h)) ∧ ∀ (ψ1 ψ1' : Twist D Circle), ψ1.Good → ψ1'.Good → ConjChar τ ψ1 ψ1' → FixDat B τ → ∀ f f' : Bridge.Gf (Vc D i) → PolF D (Wc D i).rank (Vc D i).rank, (∀ h, ∃ x x' : VsV D i ℂ, ConjVec i τ x x' ∧ f h = R.ioP i (PiTensorProduct.tprod ℂ u) (c x) ∧ f' h = R.ioP i (PiTensorProduct.tprod ℂ u) (c ((τ κ / κ) • x'))) → (f ∈ B.mtLat σ emb Oc ψ1 ↔ f' ∈ B.mtLat σ emb (Oc.map (τ : ℂ →+* ℂ)) ψ1') := by
  intro D G _ _ Pl0 T0 A T _ R F κw v₀ O hC hFW hio i hO c hc u hu B hB hBo
  obtain ⟨κ, hκ0, hval, hκ⟩ := exists_coef_scale D G Pl0 T0 A T R F κw v₀ O hC hFW hio i hO c hc u hu B hB hBo
  let Φ : VsV D i ℂ →ₗ[ℂ] PolF D (Wc D i).rank (Vc D i).rank := R.ioP i (PiTensorProduct.tprod ℂ u) ∘ₗ c
  have hlam := hBo.lam
  refine ⟨κ, hκ0, hκ, existsUnique_eq Φ hB hlam hκ0 hval hκ, fun K _ _ σ emb Oc hcoef =>
    ⟨fun h => coefLat_eq_span Φ hB hlam hκ0 hval hκ σ emb Oc h,
      fun τ hτ => ⟨fun h x x' hx => conj_mem_iff Φ hlam hκ0 hval hκ σ emb Oc τ hτ h hx, ?_⟩⟩⟩
  intro ψ1 ψ1' h1 h1' hcc hfd f f' hff
  constructor
  · exact GlobalTheory.MtLatConj.mtLat_conj D i B hB hlam Φ κ hκ0 hval hκ K σ emb Oc hcoef τ hτ ψ1 ψ1' h1 h1' hcc hfd f f' hff
  · intro hf'
    have hτ' : ∀ a : K, τ.symm (σ a) = σ a := fun a => by rw [τ.symm_apply_eq, hτ]
    have hcoef' : IsCoefRing σ emb (Oc.map (τ : ℂ →+* ℂ)) :=
      ⟨hcoef.emb, fun a => Subring.mem_map.2 ⟨_, hcoef.int a, hτ _⟩⟩
    have hOO : (Oc.map (τ : ℂ →+* ℂ)).map (τ.symm : ℂ →+* ℂ) = Oc := by
      ext z
      constructor
      · intro hz
        obtain ⟨_, hw, rfl⟩ := Subring.mem_map.1 hz
        obtain ⟨b, hb, rfl⟩ := Subring.mem_map.1 hw
        simpa using hb
      · intro hz
        exact Subring.mem_map.2 ⟨τ z, Subring.mem_map.2 ⟨z, hz, rfl⟩, by simp⟩
    have hτ0 : τ.symm κ ≠ 0 := (map_ne_zero _).2 hκ0
    have key := GlobalTheory.MtLatConj.mtLat_conj D i B hB hlam Φ κ hκ0 hval hκ K σ emb (Oc.map (τ : ℂ →+* ℂ)) hcoef' τ.symm hτ' ψ1' ψ1 h1' h1
      hcc.symm hfd.symm f' f (fun h => by
        obtain ⟨x, x', hx, e1, e2⟩ := hff h
        have hx' : x' = GlobalTheory.CoefModel.mapVV (τ : ℂ →+* ℂ) (lamV D i) x := Subtype.ext hx
        have e3 : GlobalTheory.CoefModel.mapVV (τ.symm : ℂ →+* ℂ) (lamV D i) ((τ κ / κ) • x') = (κ / τ.symm κ) • x := by
          rw [map_smulₛₗ, hx', mapVV_symm_mapVV]
          congr 1
          simp [map_div₀]
        refine ⟨(τ κ / κ) • x', (κ / τ.symm κ) • x, (congrArg Subtype.val e3).symm, e2, ?_⟩
        rw [e1, smul_smul, show τ.symm κ / κ * (κ / τ.symm κ) = 1 by field_simp, one_smul]
        rfl) hf'
    rwa [hOO] at key

end GlobalTheory.CoefLatConj
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsCuspRepBumpDataSatakeUnitaryStatement
section
open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.CuspRep GlobalTheory.JSW GroundTheory.Global.IdeleGroup Formalism.L2.Host Formalism.UG GlobalTheory.LFun
open scoped ENNReal nonZeroDivisors Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_cuspRep_bump_data_satake_unitary : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a : ℕ) (π : CG E a), π.IsUnitary →
    ∀ T : Finset (HeightOneSpectrum (𝓞 E)), UnrOutside T π →
    ∃ (α : {w : HeightOneSpectrum (𝓞 E) // w ∉ T} → Fin a → ℂˣ) (π₀ : CuspSub E a) (ω : HChar E),
      (∀ w, Finset.univ.val.map (α w) = sat π w) ∧ CG.mk π₀ = π ∧ ω.IsUnitary ∧ π₀.HasCentChar ω ∧ π₀.IsUnitary ∧
      ∀ w : {w : HeightOneSpectrum (𝓞 E) // w ∉ T}, HasSatGL w.1 (π₀.locRep w.1) (Finset.univ.val.map (α w)) := by
  first | (exact @GlobalTheory.BumpData.bumpData) | (exact GlobalTheory.BumpData.bumpData) | (intros; apply GlobalTheory.BumpData.bumpData  <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsEquivariantMapOfLevelTypeVector
section
noncomputable section

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.SplitRead GlobalTheory.PendOf GlobalTheory.LevelType
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.LevelType

theorem exists_map_of_typeVec (F : Type) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
    (p : ℕ) [Fact p.Prime] (n : Type) [Fintype n] [DecidableEq n] (W : Type) [AddCommGroup W] [Module ℂ W]
    (π : Representation ℂ (GL n F) W) (ρ : FDRep ℂ (GL n (ZMod p))) (y : W) :
    resCard F = p → TypeVec π (Formalism.IrreducibleCountingLemmas.TYPES.zIdem ρ) y → ∃ φ : ρ →ₗ[ℂ] W, φ ≠ 0 ∧
      ∀ (g : GL n (ZMod p)) (h : GL n F), IsLift g h → ∀ w, π h (φ w) = φ (ρ.ρ g w) := by
  intro hp hy
  obtain ⟨h1, ℓ, hℓ, h0⟩ := hy
  let Φ : Module.Dual ℂ ρ → (ρ →ₗ[ℂ] W) := fun μ =>
    ∑ g : GL n (ZMod p), LinearMap.smulRight (μ ∘ₗ ρ.ρ g⁻¹) (π (ℓ g) y)
  have hΦ : ∀ μ w, Φ μ w = ∑ g, μ (ρ.ρ g⁻¹ w) • π (ℓ g) y := by
    intro μ w
    simp [Φ, LinearMap.sum_apply]
  have heq : ∀ μ (g₀ : GL n (ZMod p)) (h : GL n F), IsLift g₀ h → ∀ w, π h (Φ μ w) = Φ μ (ρ.ρ g₀ w) := by
    intro μ g₀ h H w
    set_option synthInstance.maxHeartbeats 100000 in
      rw [hΦ, hΦ, map_sum]
    refine Fintype.sum_equiv (Equiv.mulLeft g₀) _ _ fun g => ?_
    rw [map_smul, ← Module.End.mul_apply, ← map_mul, IsLift.apply_eq hp h1 (H.mul hp (hℓ g)) (hℓ _)]
    simp [mul_inv_rev, map_mul, Module.End.mul_apply]
  by_contra hne
  have hz : ∀ μ, Φ μ = 0 := fun μ => by
    by_contra e
    exact hne ⟨_, e, heq μ⟩
  apply h0
  let b := Module.finBasis ℂ ρ
  have key : ∑ g, LinearMap.trace ℂ ρ (ρ.ρ g⁻¹) • π (ℓ g) y = 0 := by
    have : ∑ i, Φ (b.coord i) (b i) = 0 := by simp [hz]
    rw [← this]
    simp_rw [hΦ]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun g _ => ?_
    rw [← Finset.sum_smul, LinearMap.trace_eq_matrix_trace ℂ b, Matrix.trace]
    congr 1
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Matrix.diag_apply, LinearMap.toMatrix_apply]
    rfl
  rw [Finsupp.sum_fintype _ _ (by simp)]
  simp_rw [Formalism.IrreducibleCountingLemmas.TYPES.zIdem_coeff, mul_smul]
  rw [← Finset.smul_sum, key, smul_zero]

end GlobalTheory.LevelType
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsMirabolicWhittakerReductionCellStatement
section
open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.CuspRep GlobalTheory.JSW GroundTheory.Global.IdeleGroup Formalism.L2.Host Formalism.UG GlobalTheory.LFun
open scoped ENNReal nonZeroDivisors Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_mirabolic_whittaker_reduction_cell : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (m : ℕ) (T : Finset (HeightOneSpectrum (𝓞 E)))
    (ϖ : ∀ w : HeightOneSpectrum (𝓞 E), (w.adicCompletion E)ˣ) (F : GA E (m + 1) → ℂ)
    (U : Subgroup (GL (Fin (m + 1)) (Af E))) (J : (FractionalIdeal (𝓞 E)⁰ E)ˣ),
    (∀ u ∈ U, ∀ g, GlobalTheory.JSW.whit F (g * finGL E (m + 1) u) = GlobalTheory.JSW.whit F g) →
    (∀ k ∈ GlobalTheory.CellDec.US E (m + 1) T, GeneralLinearGroup.map (pInf E) k = 1 →
      (∀ w ∈ T, GlobalTheory.CellDec.compV E (m + 1) w k = 1) → ∀ g, GlobalTheory.JSW.whit F (g * k) = GlobalTheory.JSW.whit F g) →
    (∀ u ∈ GlobalTheory.CellDec.NA E (m + 1), ∀ g, ‖GlobalTheory.JSW.whit F (u * g)‖ = ‖GlobalTheory.JSW.whit F g‖) →
    (∀ y : Fin (m + 1) → Af E, y - Pi.single (Fin.last m) 1 ∈ GlobalTheory.ThetaPoisson.latt (m + 1) J →
      ∃ κ ∈ U, (∀ w ∉ T, GeneralLinearGroup.map (pLoc E w) κ = 1) ∧
        ∀ w ∈ T, ∀ j, (GeneralLinearGroup.map (pLoc E w) κ : Matrix (Fin (m + 1)) (Fin (m + 1)) (w.adicCompletion E)) (Fin.last m) j =
          pLoc E w (y j)) →
    ∀ g ∈ GlobalTheory.CellDec.C0 E (m + 1) T, IsUnit (pInf E (g.val (Fin.last m) (Fin.last m))) →
      (fun i => pFin E (g.val (Fin.last m) i)) - Pi.single (Fin.last m) 1 ∈ GlobalTheory.ThetaPoisson.latt (m + 1) J →
      ∃ p ∈ (GlobalTheory.JSW.supS (E := E) (a := m + 1) T ∩ GlobalTheory.JSW.mirSet (GlobalTheory.CuspRep.Ad E) m), ∀ l : GlobalTheory.CellDec.abelian₂ E (m + 1) T,
        ‖GlobalTheory.JSW.whit F (GlobalTheory.CellDec.tl (m + 1) ϖ l.1 * g *
          (infGL E (m + 1) (GlobalTheory.RSTheta.rowGL (Fin.last m) (fun i => pInf E (g.val (Fin.last m) i))))⁻¹)‖ =
        ‖GlobalTheory.JSW.whit F (p * GlobalTheory.CellDec.tl (m + 1) ϖ l.1)‖ := by
  first | exact @GlobalTheory.WhitRed.exists_mirabolic | exact GlobalTheory.WhitRed.exists_mirabolic | (intros; apply GlobalTheory.WhitRed.exists_mirabolic <;> assumption)
end

