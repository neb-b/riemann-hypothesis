module

public import Mathlib
public import Formalism.RealPlaceAnalysis.Bundle0004
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.SubsingletonRankZero
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.T2SpaceAdelicGeneralLinearGroupNumberField
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0008
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.CuspDiscreteDecompositionGL
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.Bundle0004
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0147
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FinGLMemOfPow
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0114
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0002
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0002
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.DiscreteSpectrumGLTwoOfCuspidalSpectrum
public import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.ClozelPurity.EopV
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0501
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0508
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0509
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0519
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0001
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0036
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1277
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0026
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0001
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.StrongMultiplicityOne
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.IsTemperedGLOfIsUnitaryLSeg
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0010
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.ExistsCellOfIsSubquotient
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.RadfordShufflePolynomialHolds
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsUniqueHcharOfFiniteOrder
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0006
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0009
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HeckeLEntireAndNonzeroAtOne
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.QuadraticClassFieldTheory
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.ExistsOrthonormalOfUnimodular
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IwahoriProjSurjective
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0512
public import Development.AutomorphicSpectrum.Proofs.GlobalProofs.Bundle0026
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0511
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0461
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0476
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0492
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0520
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0012
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.Bundle0010
public import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.Birational
public import GroundTheory.HeightsAndTheta.Heights.HeightsOfSets.IsSmoothHermConstLine
public import GroundTheory.GlobalFields.AnalyticClassNumber.HeckeContinued
public import GroundTheory.GlobalFields.TateThesis.RootNumberLocalFinite
public import GroundTheory.GlobalFields.IdeleGroups.ClassGroup
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.PartialZetaFunctionalEquation
public import GroundTheory.GlobalFields.TateThesis.HeckeCharRayClass
public import Development.WeilBound.RepresentationTheoryGL.RegularisedSiegelWeil.SingularNullSets.WeakApproximationFinitePlace
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0510
public import CompanionTheory.SpectralGeometry.CountingDefinitions.AdelicEulerProducts.IsEulerProd
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0187

@[expose] public section

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.AuxiliaryCuspLemma
section
open NumberField GlobalTheory.CuspRep GlobalTheory.CuspRep.CuspidalL2GL MeasureTheory PositivityTheory.S2.Clozel

namespace GlobalTheory.CompanionTheory.Clozel

theorem exists_twist_isNormalised : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a : ℕ), 1 ≤ a →
    ∀ π : CuspSub E a, (∀ τ : E →+* ℂ, ∃ m, π.HasInfChar τ m) →
    ∃ s : ℂ, GlobalTheory.DiscSpec.IsNormalised (π.twist (GlobalTheory.CuspRep.Model.absC E s)) := by
  intro E _ _ _ a ha π hm
  choose m hm using hm
  have hN : (Fintype.card (E →+* ℂ) : ℂ) ≠ 0 := Nat.cast_ne_zero.2 Fintype.card_ne_zero
  have ha' : (a : ℂ) ≠ 0 := Nat.cast_ne_zero.2 (by omega)
  refine ⟨-(∑ τ, (m τ).sum) / (a * Fintype.card (E →+* ℂ)), ?_⟩
  set s : ℂ := -(∑ τ, (m τ).sum) / (a * Fintype.card (E →+* ℂ)) with hs
  intro φ hφ t g
  have hsum : ∀ τ : E →+* ℂ, (∑ i : Fin a, Eop τ i i) φ = ((m τ).sum + a * s) • φ := fun τ => by
    have h1 := (hm τ).twist (GlobalTheory.CuspRep.Model.absC E s)
    rw [GlobalTheory.CuspRep.Model.expo_absC] at h1
    rw [_root_.GlobalTheory.CompanionTheory.CapelliTrace.trace_Eop_eq E a _ τ _ h1 φ hφ, Multiset.sum_map_add]
    simp [(hm τ).1]
  have hc : ∑ τ : E →+* ℂ, ((m τ).sum + a * s) = 0 := by
    rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, hs]
    field_simp
    ring
  have hlie : lie E a (oneL E a) φ = (0 : ℂ) • φ := by
    rw [_root_.GlobalTheory.CompanionTheory.ClozelLie.lie_oneL_eq_sum_Eop E a, LinearMap.sum_apply, Finset.sum_congr rfl fun τ _ => hsum τ, ← Finset.sum_smul, hc]
  simpa using GlobalTheory.T.central_eigen_exponential E a φ 0 hlie t g

end GlobalTheory.CompanionTheory.Clozel
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CmConjugationProperties
section
open NumberField Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.CompanionTheory.SiegelND.Integ.Hua GlobalTheory.CompanionTheory.SiegelND.Integ.Hua.HS
open scoped Matrix

noncomputable section

namespace GlobalTheory.CompanionTheory.SiegelND.Integ.Hua.HS

theorem isCMExt_conj_fixed_integers : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E]
    [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → (∀ x, σ (σ x) = x) ∧
      (∀ x, σ x = x → ∃ y : F, algebraMap F E y = x) ∧
      (∀ (o : 𝓞 E), ((sO σ o : 𝓞 E) : E) = σ (o : E)) ∧
      (∀ I : Ideal (𝓞 E), Ideal.absNorm (I.map (sO σ)) = Ideal.absNorm I) := by
  intro F E _ _ _ _ _ σ h
  obtain ⟨τ⟩ : Nonempty (E →+* ℂ) := inferInstance
  have hinv : ∀ x, σ (σ x) = x := by
    intro x
    apply τ.injective
    rw [h.2.2.2, h.2.2.2, star_star]
  have hval : ∀ o : 𝓞 E, ((sO σ o : 𝓞 E) : E) = σ (o : E) := fun o => rfl
  have hmoved : ∃ θ : E, σ θ ≠ θ := by
    by_contra hc
    push_neg at hc
    have hc' := h.2.1
    refine IsTotallyComplex.complexEmbedding_not_isReal τ ?_
    rw [ComplexEmbedding.isReal_iff]
    ext y
    have := h.2.2.2 τ y
    rw [hc y] at this
    simpa using this.symm
  refine ⟨hinv, ?_, hval, ?_⟩
  · intro x hx
    by_contra hne
    haveI : Module.Finite F E := Module.finite_of_finrank_pos (by rw [h.2.2.1]; norm_num)
    have hli : LinearIndependent F ![(1 : E), x] := by
      rw [LinearIndependent.pair_iff]
      intro s t hst
      by_cases ht : t = 0
      · subst ht
        refine ⟨?_, rfl⟩
        simpa using hst
      · exfalso
        apply hne
        refine ⟨-s / t, ?_⟩
        have h1 : algebraMap F E s + algebraMap F E t * x = 0 := by
          simpa [Algebra.smul_def] using hst
        have ht' : algebraMap F E t ≠ 0 := by simpa using ht
        rw [map_div₀, map_neg, div_eq_iff ht']
        linear_combination -h1
    have hspan : Submodule.span F (Set.range ![(1 : E), x]) = ⊤ :=
      hli.span_eq_top_of_card_eq_finrank' (by rw [h.2.2.1]; simp)
    have hid : σ.toLinearMap = LinearMap.id := by
      refine LinearMap.ext_on_range hspan ?_
      intro i
      fin_cases i
      · simp
      · simpa using hx
    obtain ⟨θ, hθ⟩ := hmoved
    exact hθ (by simpa using LinearMap.congr_fun hid θ)
  · intro I
    have hs : ∀ o : 𝓞 E, sO σ (sO σ o) = o := by
      intro o
      apply RingOfIntegers.ext
      rw [hval, hval, hinv]
    let e : 𝓞 E ≃+* 𝓞 E := RingEquiv.ofRingHom (sO σ) (sO σ)
      (RingHom.ext hs) (RingHom.ext hs)
    exact GlobalTheory.absNorm_map_ringEquiv_self e I

end GlobalTheory.CompanionTheory.SiegelND.Integ.Hua.HS
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CompactElementEigenvaluesUnits
section
open NumberField IsDedekindDomain Matrix Polynomial GlobalTheory.BCT GlobalTheory.UnitaryBC Formalism.UG
open scoped Classical
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.CompanionTheory.DiagBd

theorem valued_eq_one_of_isCompact_closure_zpowers (E : Type) [Field E] [NumberField E] [IsCMField E]
    (w : Pl E) (n : ℕ) (H : Subgroup (GLw n w)) (g : H) (p : GLw n w)
    (s : Fin n → (w.adicCompletion E)ˣ) (hg : g.1 = p * GlobalTheory.SmGL.diagT (w.adicCompletion E) (Fin n) s * p⁻¹)
    (hc : IsCompact (closure (Subgroup.zpowers g : Set H))) (i : Fin n) :
    Valued.v (s i : w.adicCompletion E) = 1 := by
  set φ : H → w.adicCompletion E :=
    fun x => ((p⁻¹ * x.1 * p : GLw n w) : Matrix (Fin n) (Fin n) _) i i with hφdef
  have hφ : Continuous φ := by
    have h1 : Continuous fun x : H => (p⁻¹ * x.1 * p : GLw n w) :=
      (continuous_const.mul continuous_subtype_val).mul continuous_const
    have h2 : Continuous fun x : H => ((p⁻¹ * x.1 * p : GLw n w) : Matrix (Fin n) (Fin n) (w.adicCompletion E)) :=
      Units.continuous_val.comp h1
    exact (continuous_apply i).comp ((continuous_apply i).comp h2)
  have hpow : ∀ m : ℤ, φ (g ^ m) = ((s i ^ m : (w.adicCompletion E)ˣ) : w.adicCompletion E) := by
    intro m
    have h1 : p⁻¹ * ((g ^ m : H) : GLw n w) * p = GlobalTheory.SmGL.diagT (w.adicCompletion E) (Fin n) (s ^ m) := by
      rw [Subgroup.coe_zpow, hg, map_zpow]
      rw [show p * GlobalTheory.SmGL.diagT (w.adicCompletion E) (Fin n) s * p⁻¹ =
        MulAut.conj p (GlobalTheory.SmGL.diagT (w.adicCompletion E) (Fin n) s) from rfl, ← map_zpow]
      simp [MulAut.conj_apply, mul_assoc]
    simp only [hφdef, h1, GlobalTheory.SmGL.val_diagT, Matrix.diagonal_apply_eq, Pi.pow_apply]
  obtain ⟨R, hR⟩ := (hc.image hφ).isBounded.exists_norm_le
  have hb : ∀ m : ℤ, ‖((s i ^ m : (w.adicCompletion E)ˣ) : w.adicCompletion E)‖ ≤ R := by
    intro m
    rw [← hpow m]
    exact hR _ ⟨g ^ m, subset_closure (Subgroup.zpow_mem_zpowers g m), rfl⟩
  have hne : (s i : w.adicCompletion E) ≠ 0 := (s i).ne_zero
  have hpos : 0 < ‖(s i : w.adicCompletion E)‖ := norm_pos_iff.mpr hne
  have hnorm : ‖(s i : w.adicCompletion E)‖ = 1 := by
    rcases lt_trichotomy ‖(s i : w.adicCompletion E)‖ 1 with h | h | h
    · exfalso
      have h' : 1 < ‖(s i : w.adicCompletion E)‖⁻¹ := (one_lt_inv₀ hpos).mpr h
      obtain ⟨k, hk⟩ := pow_unbounded_of_one_lt R h'
      have := hb (-(k : ℤ))
      rw [Units.val_zpow_eq_zpow_val, norm_zpow, _root_.zpow_neg, zpow_natCast, ← inv_pow] at this
      linarith
    · exact h
    · exfalso
      obtain ⟨k, hk⟩ := pow_unbounded_of_one_lt R h
      have := hb (k : ℤ)
      rw [Units.val_zpow_eq_zpow_val, norm_zpow, zpow_natCast] at this
      linarith
  refine le_antisymm (Valued.toNormedField.norm_le_one_iff.1 hnorm.le) (not_lt.1 fun h => ?_)
  exact absurd (Valued.toNormedField.norm_lt_one_iff.2 h) (by rw [hnorm]; exact lt_irrefl _)

end GlobalTheory.CompanionTheory.DiagBd
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CompactSetContainedInLattice
section
open scoped Matrix NNReal ENNReal TensorProduct
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.WhitFree GlobalTheory.CompanionTheory.WeilSiegel.Frame GlobalTheory.CompanionTheory.AvgFree MeasureTheory

namespace GlobalTheory.CompanionTheory.AvgFree

theorem exists_lattice_of_compact {K : Type} [CommRing K] [TopologicalSpace K] [IsTopologicalRing K]
    (O : Subring K) (hOc : IsCompact (O : Set K)) (hOo : IsOpen (O : Set K)) {C : Set K} (hC : IsCompact C) :
    ∃ L : Submodule O K, IsCompact (L : Set K) ∧ IsOpen (L : Set K) ∧ C ⊆ (L : Set K) := by
  classical
  obtain ⟨t, ht⟩ := hC.elim_finite_subcover (fun x : K => (fun y => y - x) ⁻¹' (O : Set K))
    (fun x => hOo.preimage (continuous_id.sub continuous_const))
    (fun x _ => Set.mem_iUnion.2 ⟨x, by simpa using O.zero_mem⟩)
  let s : Finset K := insert 1 t
  let L : Submodule O K := Submodule.span O (s : Set K)
  have h1 : (1 : K) ∈ L := Submodule.subset_span (by simp [s])
  have hO : ∀ a ∈ O, a ∈ L := fun a ha => by
    have := L.smul_mem (⟨a, ha⟩ : O) h1
    simpa [Subring.smul_def] using this
  refine ⟨L, ?_, ?_, ?_⟩
  · haveI : CompactSpace O := isCompact_iff_compactSpace.1 hOc
    have hr : (L : Set K) = Set.range (fun c : s → O => ∑ i, (c i : K) * (i : K)) := by
      ext x
      have hs : (s : Set K) = Set.range (Subtype.val : s → K) := by simp
      change x ∈ Submodule.span O (s : Set K) ↔ _
      rw [hs, Submodule.mem_span_range_iff_exists_fun]
      rfl
    rw [hr]
    refine isCompact_range ?_
    fun_prop
  · have hopen : IsOpen ((L.toAddSubgroup : AddSubgroup K) : Set K) := by
      refine AddSubgroup.isOpen_mono (H₁ := O.toAddSubgroup) (fun a ha => hO a ha) hOo
    exact hopen
  · intro x hx
    obtain ⟨y, hy, hxy⟩ := Set.mem_iUnion₂.1 (ht hx)
    have hyL : y ∈ L := Submodule.subset_span (by simp [s, hy])
    have : x = (x - y) + y := by ring
    rw [this]
    exact L.add_mem (hO _ hxy) hyL

end GlobalTheory.CompanionTheory.AvgFree

theorem GlobalTheory.CompanionTheory.AvgFree.exists_lattice_tupIn : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers F)) (O : Subring (Fv F v ⊗[F] E)), IsCompact (O : Set (Fv F v ⊗[F] E)) → IsOpen (O : Set (Fv F v ⊗[F] E)) → ∀ (n M : ℕ) (A : Set (Fin n → Fin M → (Fv F v ⊗[F] E))), IsCompact A → ∃ L : Submodule O (Fv F v ⊗[F] E), IsCompact (L : Set (Fv F v ⊗[F] E)) ∧ IsOpen (L : Set (Fv F v ⊗[F] E)) ∧ A ⊆ tupIn (Fv F v) (L : Set (Fv F v ⊗[F] E)) := by
  intro F E _ _ _ _ _ σ hσ v O hOc hOo n M A hA
  obtain ⟨r1, r2, r3, r4, -⟩ := GlobalTheory.CompanionTheory.SW.LocFv.isLocR_Fv F v
  haveI := r1
  haveI := r2
  haveI := r3
  haveI := r4
  obtain ⟨a1, -⟩ := GlobalTheory.CompanionTheory.SW.TopK.topTens_props F E σ hσ (Fv F v)
  haveI := a1
  have hC : IsCompact (⋃ i : Fin n, ⋃ k : Fin M, (fun X : Fin n → Fin M → Fv F v ⊗[F] E => X i k) '' A) :=
    isCompact_iUnion fun i => isCompact_iUnion fun k => hA.image (by fun_prop)
  obtain ⟨L, h1, h2, h3⟩ := exists_lattice_of_compact O hOc hOo hC
  refine ⟨L, h1, h2, fun X hX i k => h3 ?_⟩
  exact Set.mem_iUnion₂.2 ⟨i, k, X, hX, rfl⟩
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CompactSupportSplitCentreFactorStatement
section
open NumberField MeasureTheory Topology GlobalTheory.AutomorphicL2Unitary GlobalTheory.DiscreteSum GlobalTheory.OpTrace GlobalTheory.CuspRep GlobalTheory.CuspRep.CuspidalL2GL GlobalTheory.UnitaryBC
open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.CuspidalSpectrum GlobalTheory.CompanionTheory.CuspTransfer
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.compact_support_split_centre_factor : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a : ℕ), 0 < a → ∀ (μ : Measure (GA E a)) [μ.IsHaarMeasure] (ν : Measure (normOneGL (K := E) (n := a))) [ν.IsHaarMeasure] (c : ENNReal), c ≠ 0 → c ≠ ⊤ → Measure.map (fun p : normOneGL (K := E) (n := a) × ℝ => splitCentre E a p.2 * (p.1 : GA E a)) (ν.prod volume) = c • μ → ∀ f : GA E a → ℂ, Continuous f → HasCompactSupport f → ∃ f₁ : CompactlySupportedContinuousMap (normOneGL (K := E) (n := a)) ℂ, ∀ (K : Type) [NormedAddCommGroup K] [NormedSpace ℂ K] [CompleteSpace K] (W : GA E a → K), Continuous W → (∀ t g, W (splitCentre E a t * g) = W g) → ∫ g, f g • W g ∂μ = ∫ x, f₁ x • W (x : GA E a) ∂ν := by
  first | exact @GlobalTheory.CompanionTheory.CuspTransfer.FubiniCentre.exists_normOne_integral | exact GlobalTheory.CompanionTheory.CuspTransfer.FubiniCentre.exists_normOne_integral | (intros; apply GlobalTheory.CompanionTheory.CuspTransfer.FubiniCentre.exists_normOne_integral <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ComplexPointHasNonzeroLift
section
set_option autoImplicit false
noncomputable section
open CategoryTheory AlgebraicGeometry Limits TopologicalSpace MvPolynomial
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.ProjSpace GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.ArInt
open GroundTheory.Arith.SchemeCoh GroundTheory.Arith.SchemeCoh.ProjSpace
open GlobalTheory.ArithmeticHeightTower GlobalTheory.CompanionTheory.MPDict
open GlobalTheory

namespace GlobalTheory.CompanionTheory.MPDict

theorem exists_isUnder_of_cxPt (m : ℕ) (n : Fin (m + 1) → ℕ) (y : CxPts (mpStr ℤ m n) σ₀) :
    ∃ z : (Σ k, Bk n k) → ℂ, (∀ k, ∃ i, z ⟨k, i⟩ ≠ 0) ∧ IsUnder y z := by
  have hc : ∀ k, ∃ i, y ∈ ptsIn (mpStr ℤ m n) σ₀ (blockChart n k i) := fun k =>
    ⟨ptChart _ k, CxPts.mem_ptsIn.2 (mem_ptChart _ k)⟩
  choose c hc using hc
  let z : (Σ k, Bk n k) → ℂ := fun p =>
    CxPts.ev (mpStr ℤ m n) σ₀ (blockChart n p.1 (c p.1)) (pullRatio (prB n p.1) _ (c p.1) le_rfl p.2) y
  have hz1 : ∀ k, z ⟨k, c k⟩ = 1 := fun k => by
    change CxPts.ev (mpStr ℤ m n) σ₀ (blockChart n k (c k)) (pullRatio (prB n k) _ (c k) le_rfl (c k)) y = 1
    rw [pullRatio_self, CxPts.ev_eq (hc k), map_one]
  refine ⟨z, fun k => ⟨c k, by rw [hz1]; exact one_ne_zero⟩, fun k i => ?_⟩
  have hmem : y ∈ ptsIn (mpStr ℤ m n) σ₀ (blockChart n k i) ↔ z ⟨k, i⟩ ≠ 0 := by
    have e := CxPts.mem_ptsIn_basicOpen (hc k) (pullRatio (prB n k) _ (c k) le_rfl i)
    rw [basicOpen_pullRatio, CxPts.mem_ptsIn_inf] at e
    exact ⟨fun h => e.1 ⟨hc k, h⟩, fun h => (e.2 h).2⟩
  refine ⟨hmem, fun j hi => ?_⟩
  have hW : y ∈ ptsIn (mpStr ℤ m n) σ₀ (blockChart n k (c k) ⊓ blockChart n k i) :=
    CxPts.mem_ptsIn_inf.2 ⟨hc k, hi⟩
  have r1 : ∀ l, CxPts.ev (mpStr ℤ m n) σ₀ (blockChart n k (c k) ⊓ blockChart n k i)
      (pullRatio (prB n k) _ (c k) inf_le_left l) y = z ⟨k, l⟩ := fun l => by
    rw [← resG_pullRatio (φ := prB n k) (W := blockChart n k (c k)) (i := c k) (hi := le_rfl) inf_le_left]
    exact CxPts.ev_res inf_le_left hW _
  have r2 : CxPts.ev (mpStr ℤ m n) σ₀ (blockChart n k (c k) ⊓ blockChart n k i)
      (pullRatio (prB n k) _ i inf_le_right j) y =
      CxPts.ev (mpStr ℤ m n) σ₀ (blockChart n k i) (pullRatio (prB n k) _ i le_rfl j) y := by
    rw [← resG_pullRatio (φ := prB n k) (W := blockChart n k i) (i := i) (hi := le_rfl) inf_le_right]
    exact CxPts.ev_res inf_le_right hW _
  have e := congrArg (fun f => CxPts.ev (mpStr ℤ m n) σ₀ (blockChart n k (c k) ⊓ blockChart n k i) f y)
    (pullRatio_mul_pullRatio (φ := prB n k) (W := blockChart n k (c k) ⊓ blockChart n k i) (i := c k) (j := i)
      (k := j) (hi := inf_le_left) (hj := inf_le_right))
  simp only [CxPts.ev_mul, r1, r2] at e
  rw [eq_div_iff (hmem.1 hi), mul_comm]
  exact e

end GlobalTheory.CompanionTheory.MPDict
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ConductorEqTopOfStandardOpen
section
open NumberField GroundTheory.Global GroundTheory.Global.IdeleGroup
open scoped nonZeroDivisors

namespace GlobalTheory.CompanionTheory.PartialZeta

theorem conductor_eq_top_of_standardOpen {F : Type} [Field F] [NumberField F]
    (χ : HeckeCharacter F) (h : standardOpenSubgroup F ≤ χ.toIdele.ker) : χ.conductor = ⊤ := by
  have h1 : χ.conductor ∣ (⊤ : Ideal (𝓞 F)) :=
    (χ.map_idealLevel_le_ker_iff (𝔪 := ⊤) top_ne_bot).1
      ((map_idealLevel_le_standardOpenSubgroup ⊤).trans h)
  rw [← Ideal.one_eq_top] at h1
  exact Ideal.isUnit_iff.1 (isUnit_of_dvd_one h1)

theorem toIdele_inv_apply {F : Type} [Field F] [NumberField F]
    (χ : HeckeCharacter F) (x : IdeleGroup F) : (χ⁻¹).toIdele x = (χ.toIdele x)⁻¹ :=
  rfl

theorem coeff_inv_mul_coeff : ∀ (F : Type) [Field F] [NumberField F] (χ : HeckeCharacter F),
    standardOpenSubgroup F ≤ χ.toIdele.ker → ∀ J : Ideal (𝓞 F), J ≠ ⊥ →
      (χ⁻¹).coeff J * χ.coeff J = 1 := by
  intro F _ _ χ hχ J hJ
  have hc : χ.conductor = ⊤ := conductor_eq_top_of_standardOpen χ hχ
  have hc' : (χ⁻¹).conductor = ⊤ := by
    refine conductor_eq_top_of_standardOpen _ fun x hx ↦ ?_
    have h1 : χ.toIdele x = 1 := hχ hx
    rw [MonoidHom.mem_ker, toIdele_inv_apply, h1, inv_one]
  have h1 : J ≠ ⊥ ∧ IsCoprime J χ.conductor :=
    ⟨hJ, by rw [hc, ← Ideal.one_eq_top]; exact isCoprime_one_right⟩
  have h2 : J ≠ ⊥ ∧ IsCoprime J (χ⁻¹).conductor :=
    ⟨hJ, by rw [hc', ← Ideal.one_eq_top]; exact isCoprime_one_right⟩
  obtain ⟨x, hx, hxJ⟩ := exists_mem_primeToLevel (idealUnit_mem_idealsPrimeTo h1.1 h1.2)
  have hx' : x ∈ primeToLevel (χ⁻¹).conductor := by rw [hc', ← hc]; exact hx
  rw [HeckeCharacter.coeff_of_mem _ h1, HeckeCharacter.coeff_of_mem _ h2,
    HeckeCharacter.idealCharacter_apply _ hx _ hxJ,
    HeckeCharacter.idealCharacter_apply _ hx' _ hxJ, toIdele_inv_apply, ← Circle.coe_mul,
    inv_mul_cancel, Circle.coe_one]

end GlobalTheory.CompanionTheory.PartialZeta
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ContinuousThetaKernelComponents
section
noncomputable section
open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct Topology
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory Filter
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC PositivityTheory.PfSWUS PositivityTheory.Rg.Rsw PositivityTheory.Rg.Rsw.L
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.CompanionTheory.RCellCont

theorem continuity_characters_projection : ∀ {D : D7} {t ρ : ℕ} {ψ : AddChar (AF D.host.F) ℂ} (hψ : IsCharAF D.host.F ψ) (V : HSp D) (b₀ : HermE D ρ) (b : hermA D t), Continuous (fun z : Mx D V.rank ρ × Mx D V.rank t => pch ψ b.1 (ip V z.2 z.2)) ∧ Continuous (fun z : Mx D V.rank ρ × Mx D V.rank t => yv V b₀ z) ∧ Continuous (fun q : Mx D ρ t × (Mx D V.rank ρ × Mx D V.rank t) => ψ (trA (Matrix.trace (pr b₀ q.1 (yv V b₀ q.2))))) ∧ Continuous (fun z : Mx D V.rank ρ × Mx D V.rank t => pch ψ b.1 (qv V b₀ z)) ∧ (∀ T, ‖pch ψ b.1 T‖ = 1) ∧ ∀ u, ‖ψ u‖ = 1 := by
  intro D t ρ ψ hψ V b₀ b
  have hψc : Continuous ψ := hψ.1
  have hψn : ∀ u, ‖ψ u‖ = 1 := hψ.2.1
  have htr : Continuous (trA (D := D)) := by unfold trA; fun_prop
  have hhalf : Continuous (halfTr (D := D)) := by
    unfold halfTr
    exact continuous_const.mul htr
  have hpch : ∀ {n : ℕ} (x : Mx D n n), Continuous (fun T : Mx D n n => pch ψ x T) := by
    intro n x
    unfold pch mm
    exact hψc.comp (hhalf.comp ((continuous_const.matrix_mul continuous_id).matrix_trace))
  have hip : ∀ {a c : ℕ} {X : Type} [TopologicalSpace X] (f : X → Mx D V.rank a) (g : X → Mx D V.rank c),
      Continuous f → Continuous g → Continuous (fun x => ip V (f x) (g x)) := by
    intro a c X _ f g hf hg
    unfold ip mm
    exact (GlobalTheory.MixModel.continuous_adj.comp hf).matrix_mul (continuous_const.matrix_mul hg)
  have hyv : Continuous (fun z : Mx D V.rank ρ × Mx D V.rank t => yv V b₀ z) := by
    unfold yv mm
    exact continuous_const.matrix_mul (hip _ _ continuous_fst continuous_snd)
  have hpr : ∀ {p : ℕ} {X : Type} [TopologicalSpace X] (f g : X → Mx D ρ p),
      Continuous f → Continuous g → Continuous (fun x => pr b₀ (f x) (g x)) := by
    intro p X _ f g hf hg
    unfold pr
    exact (GlobalTheory.MixModel.continuous_adj.comp hf).matrix_mul (continuous_const.matrix_mul hg)
  refine ⟨?_, hyv, ?_, ?_, ?_, hψn⟩
  · exact (hpch b.1).comp (hip _ _ continuous_snd continuous_snd)
  · exact hψc.comp (htr.comp (hpr _ _ continuous_fst (hyv.comp continuous_snd)).matrix_trace)
  · have hq : Continuous (fun z : Mx D V.rank ρ × Mx D V.rank t => qv V b₀ z) := by
      unfold qv
      set_option synthInstance.maxHeartbeats 200000 in
        exact (hip _ _ continuous_snd continuous_snd).sub (hpr _ _ hyv hyv)
    exact (hpch b.1).comp hq
  · intro T
    unfold pch
    exact hψn _

end GlobalTheory.CompanionTheory.RCellCont

end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CuspidalRestrictMemCuspidalL2Statement
section
open NumberField MeasureTheory Topology GlobalTheory.AutomorphicL2Unitary GlobalTheory.DiscreteSum GlobalTheory.OpTrace GlobalTheory.CuspRep GlobalTheory.CuspRep.CuspidalL2GL GlobalTheory.UnitaryBC
open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.CuspidalSpectrum GlobalTheory.CompanionTheory.CuspTransfer
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cuspidal_restrict_mem_cuspidal_l2 : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a : ℕ) (ν : Measure (normOneGL (K := E) (n := a))) [ν.IsHaarMeasure] (φ : GA E a → ℂ), φ ∈ cuspCont E a → ∀ h : MemLp (resQ φ) 2 (RightCosetSpace.quotientMeasure (rationalGLOne (K := E) (n := a)) ν), h.toLp (resQ φ) ∈ cuspidalL2 ν := by
  first | exact @GlobalTheory.CompanionTheory.CuspTransfer.toLp_restrict_mem_cuspidalL2 | exact GlobalTheory.CompanionTheory.CuspTransfer.toLp_restrict_mem_cuspidalL2 | (intros; apply GlobalTheory.CompanionTheory.CuspTransfer.toLp_restrict_mem_cuspidalL2 <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsRealCoords
section
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix

namespace GlobalTheory.CompanionTheory.SW.SchwartzFib


set_option synthInstance.maxHeartbeats 400000 in
set_option synthInstance.maxSize 2000 in
theorem exists_real_coords : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (n M : ℕ),
    ∃ (N : ℕ) (e : (Fin n → Fin M → Ainf F ⊗[F] E) ≃+ (Fin N → ℝ)), Continuous e ∧ Continuous e.symm := by
  intro F E _ _ _ _ _ n M
  haveI : Module.Finite F E := Module.Finite.of_restrictScalars_finite ℚ F E
  let t := GlobalTheory.Core.Rk.RapidInt.tupEquiv F E (Module.finBasis F E) M n
  let L := (Module.finBasis ℝ (Fin n → Fin M → Fin (Module.finrank F E) → mixedEmbedding.mixedSpace F)).equivFun.toContinuousLinearEquiv
  refine ⟨_, t.toAddEquiv.trans L.toLinearEquiv.toAddEquiv, ?_, ?_⟩
  · exact L.continuous.comp t.continuous
  · exact t.symm.continuous.comp L.symm.continuous

end GlobalTheory.CompanionTheory.SW.SchwartzFib
end

