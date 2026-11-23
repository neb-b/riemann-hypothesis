module

public import Mathlib
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.CuspDiscreteDecompositionGL
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.NotIsFinitePartOfBot
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0012
public import GroundTheory.AutomorphicForms.CuspidalDiscreteness
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0007
public import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.MirabolicDerivatives.UnipotentDerivatives.DerUnipLeUnipB
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0355
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0348
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0349
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0432
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0297
public import Development.WeilBound.ThetaLifts.LatticeBasics.Bundle0007
public import Development.WeilBound.ThetaLifts.LatticeBasics.Bundle0014
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0434
public import Development.AutomorphicSpectrum.Proofs.GlobalProofs.ContinuousCompOfIsOpenKer

@[expose] public section

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CuspidalDecompositionOfCompact
section
noncomputable section

open NumberField MeasureTheory Topology GlobalTheory.AutomorphicL2Unitary GlobalTheory.DiscreteSum GlobalTheory.OpTrace GlobalTheory.CuspRep GlobalTheory.CuspRep.CuspidalL2GL GlobalTheory.UnitaryBC

namespace GlobalTheory.CompanionTheory.CuspGL

theorem cuspDiscreteDecompositionGL_of_compact
    (hc : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a : ℕ) (μ : Measure (GA E a)) [μ.IsHaarMeasure]
      [μ.IsMulRightInvariant] (f : GA E a → ℂ), Continuous f → HasCompactSupport f →
      IsCompactOperator (repOp (Rcusp μ) μ f)) :
    GlobalTheory.Published.CuspDiscreteDecompositionGL := by
  intro E _ _ _ a μ _ _
  have : BorelSpace (GA E a) := GlobalTheory.CuspRep.CuspidalL2GL.borelSpace_GA E a
  have : LocallyCompactSpace (GA E a) := GlobalTheory.CuspRep.CuspidalL2GL.locallyCompactSpace_GA E a
  have : T2Space (GA E a) := GlobalTheory.CuspRep.CuspidalL2GL.t2Space_GA E a
  have : CompleteSpace (L2cusp μ) := GlobalTheory.CuspRep.CuspidalL2GL.completeSpace_L2cusp μ
  have hU := GlobalTheory.CuspRep.CuspidalL2GL.isUnitaryRep_Rcusp μ
  refine GlobalTheory.CuspSpectrum.isDiscreteSum_of_repOp hU μ fun v hv => ?_
  have hpos : 0 < ‖v‖ := norm_pos_iff.mpr hv
  have cc : Continuous fun g => inner ℂ v ((Rcusp μ g) v) := continuous_const.inner (hU.continuous_apply v)
  have h1pos : 0 < (inner ℂ v ((Rcusp μ 1) v)).re := by
    rw [map_one, ContinuousLinearMap.one_apply]
    have h3 : RCLike.re (inner ℂ v v) = ‖v‖ ^ 2 := inner_self_eq_norm_sq v
    have h4 : (inner ℂ v v).re = ‖v‖ ^ 2 := h3
    rw [h4]
    exact pow_pos hpos 2
  have hN : {g | 0 < (inner ℂ v ((Rcusp μ g) v)).re} ∈ 𝓝 (1 : GA E a) :=
    (isOpen_lt continuous_const (Complex.continuous_re.comp cc)).mem_nhds h1pos
  obtain ⟨φ, hφc, hφs, hφ0, hφ1, hφN⟩ := GlobalTheory.CompanionTheory.Bump.exists_nonneg_bump (1 : GA E a) _ hN
  have hfc : Continuous fun g => (φ g : ℂ) := Complex.continuous_ofReal.comp hφc
  have hfs : HasCompactSupport fun g => (φ g : ℂ) := hφs.comp_left Complex.ofReal_zero
  refine ⟨fun g => (φ g : ℂ), hfc, hfs, hc E a μ _ hfc hfs, fun h0 => ?_⟩
  have key := hU.inner_repOp (μ := μ) hfc hfs v v
  rw [h0, inner_zero_right] at key
  have hint : Integrable (fun g => (φ g : ℂ) * inner ℂ v ((Rcusp μ g) v)) μ :=
    (hfc.mul cc).integrable_of_hasCompactSupport hfs.mul_right
  have h8 := Complex.reCLM.integral_comp_comm hint
  simp only [Complex.reCLM_apply, Complex.re_ofReal_mul] at h8
  rw [← key, Complex.zero_re] at h8
  have h9 : 0 < ∫ g, φ g * (inner ℂ v ((Rcusp μ g) v)).re ∂μ := by
    refine Continuous.integral_pos_of_hasCompactSupport_nonneg_nonzero (x := 1)
      (hφc.mul (Complex.continuous_re.comp cc)) hφs.mul_right (fun g => ?_) (mul_ne_zero hφ1 h1pos.ne')
    by_cases hg : φ g = 0
    · simp [hg]
    · exact mul_nonneg (hφ0 g) (hφN hg).le
  linarith

end GlobalTheory.CompanionTheory.CuspGL

end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CuspidalIsGeneric
section
noncomputable section

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.BZMir

namespace GlobalTheory.CompanionTheory.BZDeriv

theorem isSmooth_resM {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    {N : ℕ} {V : Type} [AddCommGroup V] [Module ℂ V] (π : Representation ℂ (GL (Fin (N + 1)) k) V)
    (hπ : IsSmooth π) : IsSmooth (resM k π).ρ := by
  intro v
  exact (hπ v).preimage continuous_subtype_val

theorem isGenericFor_of_isCuspidal_of
    (hNZ : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
      (ψ : AddChar k Circle), Continuous ψ → ψ ≠ 1 → ∀ (m : ℕ) (V : Type) [AddCommGroup V] [Module ℂ V]
      (τ : Representation ℂ (Mir k m) V), IsSmooth τ → Nontrivial V →
      ∃ n ≤ m, Nontrivial (TwJacquet τ (derUnipM k m n) (derCharM k ψ m n)))
    (hRes : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
      (ψ : AddChar k Circle) (m n : ℕ) (V : Type) [AddCommGroup V] [Module ℂ V]
      (π : Representation ℂ (GL (Fin (m + 1)) k) V),
      twKer (resM k π).ρ (derUnipM k m n) (derCharM k ψ m n) = twKer π (derUnip k (m + 1) n) (derChar k ψ (m + 1) n))
    (hVan : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
      (ψ : AddChar k Circle) (N n : ℕ) (V : Type) [AddCommGroup V] [Module ℂ V]
      (π : Representation ℂ (GL (Fin N) k) V), IsCuspidal π → 1 ≤ n → n < N →
      twKer π (derUnip k N n) (derChar k ψ N n) = ⊤)
    (hW0 : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
      (ψ : AddChar k Circle) (N : ℕ) (V : Type) [AddCommGroup V] [Module ℂ V]
      (π : Representation ℂ (GL (Fin N) k) V),
      twKer π (derUnip k N 0) (derChar k ψ N 0) = twKer π (unipB k (Fin N)) (whitChar ψ N)) :
    ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
      (ψ : AddChar k Circle), Continuous ψ → ψ ≠ 1 → ∀ (N : ℕ) (V : Type) [AddCommGroup V] [Module ℂ V]
      (π : Representation ℂ (GL (Fin (N + 1)) k) V), IsCuspidal π → Nontrivial V → IsGenericFor ψ π := by
  intro k _ _ _ _ ψ hψc hψ1 N V _ _ π hπ hV
  have hV' : Nontrivial (resM k π).V := hV
  obtain ⟨n, hn, hnt⟩ := hNZ k ψ hψc hψ1 N (resM k π).V (resM k π).ρ (isSmooth_resM π hπ.1) hV'
  rw [Submodule.Quotient.nontrivial_iff, hRes k ψ N n V π] at hnt
  rcases Nat.eq_zero_or_pos n with rfl | hpos
  · rw [hW0 k ψ (N + 1) V π] at hnt
    exact Submodule.Quotient.nontrivial_iff.2 hnt
  · exact absurd (hVan k ψ (N + 1) n V π hπ hpos (Nat.lt_succ_of_le hn)) hnt

theorem isGenericFor_of_isCuspidal :
    ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
      (ψ : AddChar k Circle), Continuous ψ → ψ ≠ 1 → ∀ (N : ℕ) (V : Type) [AddCommGroup V] [Module ℂ V]
      (π : Representation ℂ (GL (Fin (N + 1)) k) V), IsCuspidal π → Nontrivial V → IsGenericFor ψ π :=
  isGenericFor_of_isCuspidal_of GlobalTheory.T.exists_nontrivial_derivative (fun k _ _ _ _ ψ m n V _ _ π =>
    GlobalTheory.CompanionTheory.BZMirDer.twKer_resM_derUnipM (k := k) ψ m n V π) _root_.GlobalTheory.CompanionTheory.BZMir.twKer_derUnip_eq_top_of_isCuspidal
    (fun k _ _ _ _ ψ N V _ _ π => GlobalTheory.CompanionTheory.DerWhit.twKer_derUnip_zero (k := k) ψ N V π)

end GlobalTheory.CompanionTheory.BZDeriv
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CuspidalOfL2CuspidalMem
section
open NumberField MeasureTheory Topology Matrix GlobalTheory.AutomorphicL2Unitary GlobalTheory.DiscreteSum GlobalTheory.OpTrace GlobalTheory.UnitaryBC GlobalTheory.DiscSpec GlobalTheory.CuspRep GlobalTheory.CuspRep.CuspidalL2GL
open scoped ENNReal Pointwise

noncomputable section

namespace GlobalTheory.CompanionTheory.CuspL2

theorem exists_lintegral_enorm_lift_le {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [SecondCountableTopology G] [LocallyCompactSpace G] [T2Space G] [MeasurableSpace G] [BorelSpace G] (Γ : Subgroup G)
    [DiscreteTopology Γ] (μ : Measure G) [μ.IsHaarMeasure] [μ.IsMulRightInvariant] {C : Set G} (hC : IsCompact C) :
    ∃ M : ℝ≥0∞, M ≠ ∞ ∧ ∀ F : L2 Γ μ, ∫⁻ g in C, ‖lift Γ F g‖ₑ ∂μ ≤ M * ‖F‖ₑ := by
  have hS : {γ : Γ | (γ : G) ∈ C * C⁻¹}.Finite := finite_mem_compact (hC.mul hC.inv)
  obtain ⟨N, hNdef⟩ : ∃ N : ℝ≥0∞, N = ({γ : Γ | (γ : G) ∈ C * C⁻¹}.encard : ℝ≥0∞) := ⟨_, rfl⟩
  have hN : N ≠ ∞ := by simpa [hNdef] using hS
  have hfin : μ C ≠ ∞ := hC.measure_lt_top.ne
  refine ⟨N ^ (1 / 2 : ℝ) * μ C ^ (1 / 2 : ℝ), ENNReal.mul_ne_top (ENNReal.rpow_ne_top_of_nonneg (by norm_num) hN)
    (ENNReal.rpow_ne_top_of_nonneg (by norm_num) hfin), fun F => ?_⟩
  have hm : AEStronglyMeasurable (lift Γ F) μ :=
    aestronglyMeasurable_quotMeasure_iff_lift.1 (Lp.aestronglyMeasurable F)
  have h2 : ∫⁻ g in C, ‖lift Γ F g‖ₑ ^ (2 : ℝ≥0∞).toReal ∂μ ≤
      N * ∫⁻ q, ‖F q‖ₑ ^ (2 : ℝ≥0∞).toReal ∂GlobalTheory.AutomorphicL2Unitary.quotMeasure Γ μ := by
    rw [← lintegral_indicator hC.measurableSet,
      lintegral_eq_lintegral_tsum (Γ := Γ) ((hm.enorm.pow_const _).indicator hC.measurableSet),
      ← lintegral_const_mul' _ _ hN]
    refine lintegral_mono fun q => ?_
    rw [hNdef]
    refine le_trans (le_of_eq (tsum_congr fun γ => ?_)) (GlobalTheory.AutomorphicL2Local.tsum_indicator_le Γ C q.out _)
    by_cases hγ : (γ : G) * q.out ∈ C
    · rw [Set.indicator_of_mem hγ, Set.indicator_of_mem hγ]
      simp only [GlobalTheory.AutomorphicL2Unitary.lift, mk_mul, Quotient.out_eq]
    · rw [Set.indicator_of_notMem hγ, Set.indicator_of_notMem hγ]
  have h3 : eLpNorm (lift Γ F) 2 (μ.restrict C) ≤ N ^ (1 / 2 : ℝ) * ‖F‖ₑ := by
    rw [Lp.enorm_def, eLpNorm_eq_lintegral_rpow_enorm_toReal (by simp) (by simp),
      eLpNorm_eq_lintegral_rpow_enorm_toReal (f := F) (by simp) (by simp)]
    refine (ENNReal.rpow_le_rpow h2 (by simp)).trans (le_of_eq ?_)
    rw [ENNReal.mul_rpow_of_nonneg _ _ (by simp)]
    simp
    exact Lp.aestronglyMeasurable F
    exact hm.restrict
  have h4 := eLpNorm_le_eLpNorm_mul_rpow_measure_univ (μ := μ.restrict C) (p := 1) (q := 2) (by norm_num) hm.restrict
  have e : (1 / (1 : ℝ≥0∞).toReal - 1 / (2 : ℝ≥0∞).toReal) = (1 / 2 : ℝ) := by norm_num
  rw [eLpNorm_one_eq_lintegral_enorm, e, Measure.restrict_apply_univ] at h4
  calc _ ≤ N ^ (1 / 2 : ℝ) * ‖F‖ₑ * μ C ^ (1 / 2 : ℝ) := h4.trans (by gcongr)
    _ = _ := by ring
  exact hm.restrict

section Adelic

variable {E : Type} [Field E] [NumberField E] {a r : ℕ}

theorem exists_mem_apply_unip_eq {X : Type*} {u : GA E a → X} (hl : ∀ γ g, u (ratGL E a γ * g) = u g)
    {K : Set (BlockIx a r → Ad E)} (hcov : ∀ x, ∃ γ ∈ ratN E a r, γ + x ∈ K) (x : BlockIx a r → Ad E) :
    ∃ k ∈ K, ∀ g, u (unip x * g) = u (unip k * g) := by
  obtain ⟨_, ⟨y, rfl⟩, hk⟩ := hcov x
  refine ⟨_, hk, fun g => ?_⟩
  rw [unip_add, mul_assoc]
  exact ((congrArg (fun v => u (v * _)) (unip_algebraMap y)).trans (hl _ _)).symm

variable [MeasurableSpace (BlockIx a r → Ad E)] [BorelSpace (BlockIx a r → Ad E)]

theorem lintegral_constTerm_le [_root_.NumberField.IsTotallyComplex E] (μ : Measure (GA E a)) [μ.IsHaarMeasure]
    (ν : Measure (BlockIx a r → Ad E)) {𝓕 : Set (BlockIx a r → Ad E)} (hν𝓕 : ν 𝓕 ≠ ∞)
    {K : Set (BlockIx a r → Ad E)} (hK : IsCompact K) (hcov : ∀ x, ∃ γ ∈ ratN E a r, γ + x ∈ K) {C : Set (GA E a)}
    (hC : IsCompact C) {u : GA E a → ℂ} (hc : Continuous u) (hl : ∀ γ g, u (ratGL E a γ * g) = u g) :
    ∫⁻ g in C, ‖∫ x in 𝓕, u (unip x * g) ∂ν‖ₑ ∂μ ≤ ν 𝓕 * ∫⁻ g in (unip '' K) * C, ‖u g‖ₑ ∂μ := by
  haveI := GlobalTheory.AdelicUnitaryTop.secondCountable_adele E
  haveI : IsFiniteMeasure (ν.restrict 𝓕) := isFiniteMeasure_restrict.2 hν𝓕
  haveI : IsFiniteMeasure (μ.restrict C) := isFiniteMeasure_restrict.2 hC.measure_lt_top.ne
  have hC' : IsCompact ((unip '' K) * C) := (hK.image continuous_unip).mul hC
  have hb : ∀ x, ∫⁻ g in C, ‖u (unip x * g)‖ₑ ∂μ ≤ ∫⁻ g in (unip '' K) * C, ‖u g‖ₑ ∂μ := fun x => by
    obtain ⟨k, hk, e⟩ := exists_mem_apply_unip_eq hl hcov x
    simp only [e]
    rw [← (measurePreserving_mul_left μ (unip k)).setLIntegral_comp_preimage hC'.measurableSet
      hc.enorm.measurable]
    exact lintegral_mono_set fun g hg => Set.mul_mem_mul ⟨k, hk, rfl⟩ hg
  have hj : Continuous fun p : GA E a × (BlockIx a r → Ad E) => ‖u (unip p.2 * p.1)‖ₑ :=
    (hc.comp ((continuous_unip.comp continuous_snd).mul continuous_fst)).enorm
  calc ∫⁻ g in C, ‖∫ x in 𝓕, u (unip x * g) ∂ν‖ₑ ∂μ
      ≤ ∫⁻ g in C, ∫⁻ x in 𝓕, ‖u (unip x * g)‖ₑ ∂ν ∂μ :=
        lintegral_mono fun g => enorm_integral_le_lintegral_enorm _
    _ = ∫⁻ x in 𝓕, ∫⁻ g in C, ‖u (unip x * g)‖ₑ ∂μ ∂ν := lintegral_lintegral_swap hj.aemeasurable
    _ ≤ ∫⁻ x in 𝓕, (∫⁻ g in (unip '' K) * C, ‖u g‖ₑ ∂μ) ∂ν := lintegral_mono hb
    _ = _ := by rw [setLIntegral_const, mul_comm]

theorem continuous_constTerm [_root_.NumberField.IsTotallyComplex E] (ν : Measure (BlockIx a r → Ad E)) {𝓕 : Set (BlockIx a r → Ad E)}
    (hν𝓕 : ν 𝓕 ≠ ∞) {K : Set (BlockIx a r → Ad E)} (hK : IsCompact K) (hcov : ∀ x, ∃ γ ∈ ratN E a r, γ + x ∈ K)
    {u : GA E a → ℂ} (hc : Continuous u) (hl : ∀ γ g, u (ratGL E a γ * g) = u g) :
    Continuous fun g => ∫ x in 𝓕, u (unip x * g) ∂ν := by
  haveI := GlobalTheory.AdelicUnitaryTop.secondCountable_adele E
  haveI : IsFiniteMeasure (ν.restrict 𝓕) := isFiniteMeasure_restrict.2 hν𝓕
  refine continuous_iff_continuousAt.2 fun g₀ => ?_
  obtain ⟨C, hC, hg⟩ := exists_compact_mem_nhds g₀
  obtain ⟨B, hB⟩ := ((hK.image continuous_unip).mul hC).exists_bound_of_continuousOn hc.continuousOn
  refine continuousAt_of_dominated (bound := fun _ => B)
    (.of_forall fun g => (hc.comp (continuous_unip.mul continuous_const)).aestronglyMeasurable) ?_
    (integrable_const _) (.of_forall fun x => (hc.comp (continuous_const.mul continuous_id)).continuousAt)
  filter_upwards [hg] with g hg'
  refine .of_forall fun x => ?_
  obtain ⟨k, hk, e⟩ := exists_mem_apply_unip_eq hl hcov x
  rw [e]
  exact hB _ (Set.mul_mem_mul ⟨k, hk, rfl⟩ hg')

end Adelic

theorem isCuspidal_of_toL2_mem : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a : ℕ)
    (μ : Measure (GA E a)) [μ.IsHaarMeasure] [μ.IsMulRightInvariant] (φ : GA E a → ℂ), Continuous φ →
    (∀ γ g, φ (ratGL E a γ * g) = φ g) → (∀ t g, φ (splitCentre E a t * g) = φ g) →
    ∀ h : MemL2Quotient (latticeGL E a) μ φ, h.toL2 ∈ L2cusp μ → IsCuspidal φ := by
  intro E _ _ _ a μ _ _ φ hc hl hs h hF r h0 h1 _ _ ν 𝓕 hν h𝓕 g
  haveI := GlobalTheory.AdelicUnitaryTop.secondCountable_adele E
  haveI := GlobalTheory.ConstNotCusp.discreteTopology_ratN E a r
  haveI : Countable (ratN E a r) := TopologicalSpace.separableSpace_iff_countable.1 inferInstance
  obtain ⟨K, hK, hcov⟩ := GlobalTheory.ConstNotCusp.exists_compact_ratN E a r
  have hν𝓕 : ν 𝓕 ≠ ∞ := (GlobalTheory.measure_addFundamentalDomain_lt_top_of_cocompact _ hK hcov ν h𝓕).ne
  have hcont := continuous_constTerm ν hν𝓕 hK hcov hc hl
  have key : ∀ C : Set (GA E a), IsCompact C → ∫⁻ g in C, ‖∫ x in 𝓕, φ (unip x * g) ∂ν‖ₑ ∂μ = 0 := fun C hC => by
    obtain ⟨M, hM, hb⟩ := exists_lintegral_enorm_lift_le (latticeGL E a) μ ((hK.image continuous_unip).mul hC)
    have step : ∀ F' ∈ cuspContinuousL2 μ, ∫⁻ g in C, ‖∫ x in 𝓕, φ (unip x * g) ∂ν‖ₑ ∂μ ≤ ν 𝓕 * (M * ‖h.toL2 - F'‖ₑ) := by
      rintro F' ⟨ψ, hψ, e⟩
      have hcomp : ∀ g, ∫ x in 𝓕, (φ (unip x * g) - ψ (unip x * g)) ∂ν = ∫ x in 𝓕, φ (unip x * g) ∂ν := fun g => by
        rw [integral_sub (integrableOn_unip hc hl ν h𝓕 g) (integrableOn_unip hψ.1 hψ.2.1 ν h𝓕 g),
          hψ.2.2.2 r h0 h1 ν 𝓕 hν h𝓕 g, sub_zero]
      have h2 := lintegral_constTerm_le μ ν hν𝓕 hK hcov hC (u := fun g => φ g - ψ g) (hc.sub hψ.1)
        (fun γ g => by rw [hl, hψ.2.1])
      simp only [hcomp] at h2
      have e' : lift (latticeGL E a) (h.toL2 - F') =ᵐ[μ] fun g => φ g - ψ g :=
        Filter.EventuallyEq.trans (ae_quotMeasure_iff.1 (Lp.coeFn_sub h.toL2 F')) (h.lift_toL2_ae_eq.sub e)
      refine h2.trans ?_
      gcongr
      refine le_trans (le_of_eq (lintegral_congr_ae (ae_restrict_of_ae ?_))) (hb (h.toL2 - F'))
      exact e'.mono fun g eg => by rw [eg]
    obtain ⟨u, hu, hlim⟩ := mem_closure_iff_seq_limit.1 (show h.toL2 ∈ closure (cuspContinuousL2 μ : Set _) from hF)
    have ht : Filter.Tendsto (fun n => ν 𝓕 * (M * ‖h.toL2 - u n‖ₑ)) Filter.atTop (𝓝 0) := by
      have h3 : Filter.Tendsto (fun n => h.toL2 - u n) Filter.atTop (𝓝 0) := by
        simpa using (tendsto_const_nhds (x := h.toL2)).sub hlim
      have h4 : Filter.Tendsto (fun n => ‖h.toL2 - u n‖ₑ) Filter.atTop (𝓝 0) := by
        simpa [Function.comp_def] using (continuous_enorm.tendsto _).comp h3
      simpa using ENNReal.Tendsto.const_mul (ENNReal.Tendsto.const_mul h4 (Or.inr hM)) (Or.inr hν𝓕)
    exact le_antisymm (ge_of_tendsto' ht fun n => step _ (hu n)) zero_le
  have hae : (fun g => ∫ x in 𝓕, φ (unip x * g) ∂ν) =ᵐ[μ] 0 := by
    have h5 : ∀ n, ∀ᵐ g ∂μ.restrict (compactCovering (GA E a) n), ∫ x in 𝓕, φ (unip x * g) ∂ν = 0 := fun n => by
      have := (lintegral_eq_zero_iff' hcont.enorm.aemeasurable).1 (key _ (isCompact_compactCovering _ n))
      exact this.mono fun g eg => by simpa using eg
    have h6 := ae_restrict_iUnion_iff _ _ |>.2 h5
    rwa [iUnion_compactCovering, Measure.restrict_univ] at h6
  exact congrFun ((Continuous.ae_eq_iff_eq μ hcont continuous_zero).1 hae) g

end GlobalTheory.CompanionTheory.CuspL2

end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.DenominatorBoundByHeight
section
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl
open GlobalTheory.Doubling (absE)
open GlobalTheory.CompanionTheory.GodementH

noncomputable section

namespace GlobalTheory.CompanionTheory.GodementH.Den

theorem local_exponent {F : Type} [Field F] [NumberField F] (v : Pl (F := F)) {y : F} (hy : y ≠ 0) :
    ∃ e : ℕ, v.valuation F y ≤ WithZero.exp (e : ℤ) ∧
      max 1 ‖algebraMap F (Fv F v) y‖₊ = (Ideal.absNorm v.asIdeal : ℝ≥0) ^ e := by
  have ha : v.valuation F y ≠ 0 := (Valuation.ne_zero_iff _).2 hy
  have hq : (1 : ℝ≥0) < (Ideal.absNorm v.asIdeal : ℝ≥0) := HeightOneSpectrum.one_lt_absNorm_nnreal v
  have hnorm : ‖algebraMap F (Fv F v) y‖₊ =
      WithZeroMulInt.toNNReal (HeightOneSpectrum.absNorm_ne_zero v) (v.valuation F y) :=
    NNReal.eq (FinitePlace.norm_embedding' v y)
  obtain ⟨n, hn⟩ : ∃ n : ℤ, v.valuation F y = WithZero.exp n := ⟨_, (WithZero.exp_log ha).symm⟩
  have hval : WithZeroMulInt.toNNReal (HeightOneSpectrum.absNorm_ne_zero v) (WithZero.exp n) =
      (Ideal.absNorm v.asIdeal : ℝ≥0) ^ n := by
    rw [WithZeroMulInt.toNNReal_neg_apply _ WithZero.exp_ne_zero]
    rw [WithZero.log_exp]
  refine ⟨n.toNat, ?_, ?_⟩
  · rw [hn]
    exact WithZero.exp_le_exp.2 (Int.self_le_toNat n)
  · rw [hnorm, hn, hval]
    rcases le_total n 0 with h | h
    · rw [Int.toNat_of_nonpos h, pow_zero]
      exact max_eq_left (zpow_le_one_of_nonpos₀ hq.le h)
    · have h1 : (Ideal.absNorm v.asIdeal : ℝ≥0) ^ n = (Ideal.absNorm v.asIdeal : ℝ≥0) ^ n.toNat := by
        rw [← zpow_natCast, Int.toNat_of_nonneg h]
      rw [h1]
      exact max_eq_right (one_le_pow₀ hq.le)

theorem finite_mulSupport {F : Type} [Field F] [NumberField F] {y : F} (hy : y ≠ 0) :
    (Function.mulSupport fun v : Pl F => max 1 ‖algebraMap F (Fv F v) y‖₊).Finite := by
  have h := (FinitePlace.hasFiniteMulSupport hy).comp_of_injective
    (FinitePlace.equivHeightOneSpectrum (K := F)).symm.injective
  refine Set.Finite.subset h ?_
  intro v hv
  simp only [Function.mem_mulSupport] at hv ⊢
  intro h1
  apply hv
  have h2 : ‖algebraMap F (Fv F v) y‖₊ = 1 := by
    apply NNReal.eq
    have h3 : ‖FinitePlace.embedding v y‖ = 1 := by
      simpa [FinitePlace.equivHeightOneSpectrum_symm_apply] using h1
    exact h3
  rw [h2, max_self]

theorem denominator_le (F : Type) [Field F] [NumberField F] (y : F) :
    ∃ m : ℕ, 0 < m ∧ (m : ℝ≥0) ≤ ∏ᶠ v : Pl (F := F), max 1 ‖algebraMap F (Fv F v) y‖₊ ∧
      IsIntegral ℤ ((m : F) * y) := by
  classical
  by_cases hy : y = 0
  · subst hy
    exact ⟨1, one_pos, by simp, by simpa using isIntegral_zero⟩
  choose e he1 he2 using fun v : Pl F => local_exponent v hy
  have hfin := finite_mulSupport hy
  set S : Finset (Pl (F := F)) := hfin.toFinset with hS
  set b : Ideal (𝓞 F) := ∏ v ∈ S, v.asIdeal ^ e v with hb
  have hb0 : b ≠ ⊥ := by
    rw [hb, ← Ideal.zero_eq_bot, Finset.prod_ne_zero_iff]
    intro v _
    exact pow_ne_zero _ v.ne_bot
  have hm : 0 < Ideal.absNorm b :=
    Nat.pos_of_ne_zero fun h => hb0 (Ideal.absNorm_eq_zero_iff.1 h)
  refine ⟨Ideal.absNorm b, hm, le_of_eq ?_, ?_⟩
  · rw [finprod_eq_prod_of_mulSupport_subset _ (s := S) (by simp [hS])]
    simp only [he2]
    simp [hb, map_prod, map_pow]
  · have key : ∀ v : Pl (F := F), v.valuation F ((Ideal.absNorm b : F) * y) ≤ 1 := by
      intro v
      have hmem : ((Ideal.absNorm b : ℕ) : 𝓞 F) ∈ v.asIdeal ^ e v := by
        by_cases hv : v ∈ S
        · exact Ideal.le_of_dvd (Finset.dvd_prod_of_mem _ hv) (Ideal.absNorm_mem b)
        · have h1 : max 1 ‖algebraMap F (Fv F v) y‖₊ = 1 := by
            simpa [hS] using hv
          have h0 : e v = 0 := by
            by_contra hne
            have hq : (1 : ℝ≥0) < (Ideal.absNorm v.asIdeal : ℝ≥0) :=
              HeightOneSpectrum.one_lt_absNorm_nnreal v
            have := one_lt_pow₀ hq hne
            rw [← he2 v, h1] at this
            exact lt_irrefl _ this
          simp [h0]
      have h2 := (v.intValuation_le_pow_iff_mem _ (e v)).2 hmem
      have h3 : v.valuation F (Ideal.absNorm b : F) ≤ WithZero.exp (-(e v : ℤ)) := by
        have : (Ideal.absNorm b : F) = algebraMap (𝓞 F) F ((Ideal.absNorm b : ℕ) : 𝓞 F) := by simp
        rw [this, HeightOneSpectrum.valuation_of_algebraMap]
        exact h2
      rw [map_mul]
      calc _ ≤ WithZero.exp (-(e v : ℤ)) * WithZero.exp (e v : ℤ) := mul_le_mul' h3 (he1 v)
        _ = 1 := by rw [← WithZero.exp_add]; simp
    obtain ⟨c, hc⟩ := HeightOneSpectrum.mem_integers_of_valuation_le_one F _ key
    rw [← hc]
    exact c.isIntegral_coe

end GlobalTheory.CompanionTheory.GodementH.Den

end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.DoubleAnnihilatorEqSelf
section
namespace GlobalTheory.CompanionTheory.FiniteDuality

private theorem card_dual_zmod_le_card' (n : ℕ) [NeZero n] (M : Type) [AddCommGroup M]
    [Module (ZMod n) M] [Finite M] :
    Nat.card (M →ₗ[ZMod n] ZMod n) ≤ Nat.card M := by
  classical
  have := Fintype.ofFinite M
  let φ : (M →ₗ[ZMod n] ZMod n) → AddChar M ℂ := fun f =>
    Circle.coeHom.compAddChar ((ZMod.toCircle (N := n)).compAddMonoidHom f.toAddMonoidHom)
  have hφ : Function.Injective φ := by
    intro f g h
    ext x
    have hx := congrArg (fun ψ : AddChar M ℂ => ψ x) h
    have hx' : Circle.coeHom (ZMod.toCircle (f x)) = Circle.coeHom (ZMod.toCircle (g x)) := hx
    exact ZMod.injective_toCircle (Circle.ext hx')
  calc Nat.card (M →ₗ[ZMod n] ZMod n) ≤ Nat.card (AddChar M ℂ) :=
        Nat.card_le_card_of_injective φ hφ
    _ = Nat.card M := by
        rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card, AddChar.card_eq]

private theorem card_le_of_injective_pairing_zmod (n : ℕ) [NeZero n] (Z W : Type) [AddCommGroup Z]
    [Module (ZMod n) Z] [AddCommGroup W] [Module (ZMod n) W] [Finite W]
    (g : Z →ₗ[ZMod n] W →ₗ[ZMod n] ZMod n) (hg : Function.Injective g) :
    Nat.card Z ≤ Nat.card W := by
  have : Finite (W →ₗ[ZMod n] ZMod n) :=
    Finite.of_injective (fun f : W →ₗ[ZMod n] ZMod n => (f : W → ZMod n)) DFunLike.coe_injective
  exact (Nat.card_le_card_of_injective g hg).trans (card_dual_zmod_le_card' n W)

theorem double_annihilator (n : ℕ) [NeZero n] (X Y : Type) [AddCommGroup X] [Module (ZMod n) X]
    [Finite X] [AddCommGroup Y] [Module (ZMod n) Y] [Finite Y]
    (B : Y →ₗ[ZMod n] X →ₗ[ZMod n] ZMod n) (hB : Function.Injective B)
    (hB' : Function.Injective B.flip) (U : Submodule (ZMod n) X) :
    (⨅ y ∈ (⨅ x ∈ U, LinearMap.ker (B.flip x)), LinearMap.ker (B y)) = U := by
  set A : Submodule (ZMod n) Y := ⨅ x ∈ U, LinearMap.ker (B.flip x) with hAdef
  set W : Submodule (ZMod n) X := ⨅ y ∈ A, LinearMap.ker (B y) with hWdef
  have memA : ∀ y, y ∈ A ↔ ∀ x ∈ U, B y x = 0 := by
    intro y
    simp [hAdef, Submodule.mem_iInf]
  have memW : ∀ x, x ∈ W ↔ ∀ y ∈ A, B y x = 0 := by
    intro x
    simp only [hWdef, Submodule.mem_iInf, LinearMap.mem_ker]
  have hUW : U ≤ W := by
    intro x hx
    rw [memW]
    intro y hy
    exact (memA y).1 hy x hx
  let f1 : Y →ₗ[ZMod n] U →ₗ[ZMod n] ZMod n := B.compl₂ U.subtype
  have hA1 : A ≤ LinearMap.ker f1 := by
    intro y hy
    rw [LinearMap.mem_ker]
    ext u
    simp [f1, (memA y).1 hy u u.2]
  have hA1' : LinearMap.ker f1 ≤ A := by
    intro y hy
    rw [LinearMap.mem_ker] at hy
    rw [memA]
    intro x hx
    have := LinearMap.congr_fun hy ⟨x, hx⟩
    simpa [f1] using this
  let P1 : (Y ⧸ A) →ₗ[ZMod n] U →ₗ[ZMod n] ZMod n := A.liftQ f1 hA1
  have hP1 : Function.Injective P1 :=
    LinearMap.ker_eq_bot.mp (Submodule.ker_liftQ_eq_bot A f1 hA1 hA1')
  let f2 : Y →ₗ[ZMod n] W →ₗ[ZMod n] ZMod n := B.compl₂ W.subtype
  have hA2 : A ≤ LinearMap.ker f2 := by
    intro y hy
    rw [LinearMap.mem_ker]
    ext w
    simp [f2, (memW w).1 w.2 y hy]
  let P2 : (Y ⧸ A) →ₗ[ZMod n] W →ₗ[ZMod n] ZMod n := A.liftQ f2 hA2
  have hP2 : Function.Injective P2.flip := by
    set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
    intro w hw
    have hz : B.flip (w : X) = 0 := by
      ext y
      have := LinearMap.congr_fun hw (Submodule.Quotient.mk y)
      simpa [P2, f2] using this
    have : (w : X) = 0 := hB' (by rw [hz, map_zero])
    exact Subtype.ext this
  have : Finite (Y ⧸ A) := Finite.of_surjective _ (Submodule.mkQ_surjective A)
  have c1 : Nat.card (Y ⧸ A) ≤ Nat.card U := card_le_of_injective_pairing_zmod n _ _ P1 hP1
  have c2 : Nat.card W ≤ Nat.card (Y ⧸ A) := card_le_of_injective_pairing_zmod n _ _ P2.flip hP2
  have hle : Nat.card (W.toAddSubgroup) ≤ Nat.card (U.toAddSubgroup) := c2.trans c1
  exact (Submodule.toAddSubgroup_injective
    (AddSubgroup.eq_of_le_of_card_ge (show U.toAddSubgroup ≤ W.toAddSubgroup from hUW) hle)).symm

end GlobalTheory.CompanionTheory.FiniteDuality
end

