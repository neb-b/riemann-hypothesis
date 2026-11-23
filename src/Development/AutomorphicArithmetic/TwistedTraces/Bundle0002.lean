module

public import Development.AutomorphicArithmetic.Foundations.Convolution.PowerSumTraces.CuspidalMultiplicityOneTotallyComplex
public import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Basic
public import Mathlib.Analysis.CStarAlgebra.ContinuousLinearMap
public import Mathlib.Topology.ContinuousMap.StoneWeierstrass
public import GroundTheory.AutomorphicForms.Bundle0001
public import Mathlib.Analysis.InnerProductSpace.Spectrum
public import GroundTheory.AutomorphicForms.HarishChandraRegularity.CartanBasis

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.TwistedTraces.CasimirEqOfOrthonormalBases
section
open MeasureTheory NumberField GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace
open GroundTheory.Automorphic.AutomorphicForm GroundTheory.Automorphic.CuspidalSpectrum UpperTheory.ConvolutionTheory.C Polynomial Topology

theorem UpperTheory.casimir_eq_of_orthonormal_bases :
    ∀ (L : Type) [LieRing L] [LieAlgebra ℝ L] (B : LinearMap.BilinForm ℝ L) (ι ι' : Type) [Fintype ι] [DecidableEq ι] [Fintype ι'] [DecidableEq ι'] (b : Module.Basis ι ℝ L) (ε : ι → ℝ) (b' : Module.Basis ι' ℝ L) (ε' : ι' → ℝ), (∀ X Y, B X Y = B Y X) → (∀ i, ε i * ε i = 1) → (∀ i j, B (b i) (b j) = if i = j then ε i else 0) → (∀ i, ε' i * ε' i = 1) → (∀ i j, B (b' i) (b' j) = if i = j then ε' i else 0) → casimir b ε = casimir b' ε' := by
  intro L _ _ B ι ι' _ _ _ _ b ε b' ε' hs hε hb hε' hb'
  set u := UniversalEnvelopingAlgebra.ι ℝ (L := L) with hu
  have e1 : ∀ i, u (b i) = ∑ j, (ε' j * B (b' j) (b i)) • u (b' j) := by
    intro i
    conv_lhs => rw [eq_sum_of_orthogonal hε' hb' (b i)]
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [map_sum, map_smul]
  have e2 : ∀ j, u (b' j) = ∑ i, (ε i * B (b i) (b' j)) • u (b i) := by
    intro j
    conv_lhs => rw [eq_sum_of_orthogonal hε hb (b' j)]
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [map_sum, map_smul]
  simp only [casimir]
  calc ∑ i, ε i • (u (b i) * u (b i))
      = ∑ i, ∑ j, (ε i * (ε' j * B (b' j) (b i))) • (u (b i) * u (b' j)) := by
        refine Finset.sum_congr rfl fun i _ => ?_
        have h : u (b i) * u (b i) = u (b i) * ∑ j, (ε' j * B (b' j) (b i)) • u (b' j) :=
          congrArg (fun x => u (b i) * x) (e1 i)
        rw [h, Finset.mul_sum, Finset.smul_sum]
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [mul_smul_comm, smul_smul]
    _ = ∑ j, ∑ i, (ε i * (ε' j * B (b' j) (b i))) • (u (b i) * u (b' j)) := Finset.sum_comm
    _ = ∑ j, ε' j • (u (b' j) * u (b' j)) := by
        refine Finset.sum_congr rfl fun j _ => ?_
        have h : u (b' j) * u (b' j) = (∑ i, (ε i * B (b i) (b' j)) • u (b i)) * u (b' j) :=
          congrArg (fun x => x * u (b' j)) (e2 j)
        rw [h, Finset.sum_mul, Finset.smul_sum]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [smul_mul_assoc, smul_smul, hs (b' j) (b i)]
        congr 1
        ring
end

-- bundled from Development.AutomorphicArithmetic.TwistedTraces.CfcApplyOfEigenvector
section
open MeasureTheory NumberField GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace
open GroundTheory.Automorphic.AutomorphicForm GroundTheory.Automorphic.CuspidalSpectrum UpperTheory.ConvolutionTheory.C

theorem UpperTheory.cfc_apply_of_eigenvector :
    ∀ (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] (A : H →L[ℂ] H), IsSelfAdjoint A → ∀ (φ : ℝ → ℝ), Continuous φ → ∀ (x : ℝ) (v : H), A v = (x : ℂ) • v → (cfc φ A : H →L[ℂ] H) v = (φ x : ℂ) • v := by
  intro H _ _ _ A hA φ hφ x v hv
  by_cases hv0 : v = 0
  · simp [hv0]
  have halg : ∀ r : ℝ, (algebraMap ℝ (H →L[ℂ] H) r) v = (r : ℂ) • v := by
    intro r
    rw [Algebra.algebraMap_eq_smul_one]
    simp
  have hx : x ∈ spectrum ℝ A := by
    rw [spectrum.mem_iff]
    rintro ⟨u, hu⟩
    apply hv0
    have h0 : (u : H →L[ℂ] H) v = 0 := by
      rw [hu, ContinuousLinearMap.sub_apply, halg, hv, sub_self]
    have h1 : ((↑u⁻¹ * ↑u : H →L[ℂ] H)) v = v := by
      rw [Units.inv_mul]; rfl
    rw [← h1, ContinuousLinearMap.mul_apply, h0, map_zero]
  have key : ∀ f : C(spectrum ℝ A, ℝ), (cfcHom hA f : H →L[ℂ] H) v = ((f ⟨x, hx⟩ : ℝ) : ℂ) • v := by
    intro f
    induction f using ContinuousMap.induction_on_of_compact with
    | const r =>
      have : (ContinuousMap.const (spectrum ℝ A) r) = algebraMap ℝ C(spectrum ℝ A, ℝ) r := rfl
      rw [this, AlgHomClass.commutes, halg]
      simp
    | id =>
      rw [cfcHom_id hA, hv]; rfl
    | star_id =>
      rw [star_trivial, cfcHom_id hA, hv]; rfl
    | add f g hf hg =>
      rw [map_add (f := _), ContinuousLinearMap.add_apply, hf, hg]
      simp [add_smul]
    | mul f g hf hg =>
      rw [map_mul, ContinuousLinearMap.mul_apply, hg, map_smul, hf, smul_smul]
      simp [mul_comm]
    | frequently f hf =>
      have hc : IsClosed {g : C(spectrum ℝ A, ℝ) | (cfcHom hA g : H →L[ℂ] H) v = ((g ⟨x, hx⟩ : ℝ) : ℂ) • v} := by
        apply isClosed_eq
        · exact (cfcHom_continuous hA).clm_apply continuous_const
        · exact (Complex.continuous_ofReal.comp (continuous_eval_const _)).smul continuous_const
      exact hc.closure_subset (mem_closure_iff_frequently.mpr hf)
  rw [cfc_apply φ A hA hφ.continuousOn, key]
  rfl
end

-- bundled from Development.AutomorphicArithmetic.TwistedTraces.EigInFiniteAboveOfIsCompactOperator
section
open MeasureTheory NumberField GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace
open GroundTheory.Automorphic.AutomorphicForm GroundTheory.Automorphic.CuspidalSpectrum UpperTheory.ConvolutionTheory.C

theorem UpperTheory.eigIn_finite_above_of_isCompactOperator :
    ∀ (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] (W : Submodule ℂ H) (A : H →L[ℂ] H), IsClosed (W : Set H) → IsSelfAdjoint A → (∀ v ∈ W, A v ∈ W) → IsCompactOperator (A ∘L prj W) → ∀ η : ℝ, 0 < η → {x : ℝ | η < x ∧ eigIn W A x ≠ ⊥}.Finite ∧ ∀ x : ℝ, η < x → FiniteDimensional ℂ (eigIn W A x) := by
  intro H _ _ _ W A hW hA hAW hC η hη
  have hWc : W.topologicalClosure = W := hW.submodule_topologicalClosure_eq
  have hPW : ∀ v, prj W v ∈ W := by
    intro v
    have : prj W v ∈ W.topologicalClosure := Submodule.starProjection_apply_mem _ v
    rwa [hWc] at this
  have hperp : ∀ v, ∀ w ∈ W, inner ℂ w (v - prj W v) = 0 := by
    intro v w hw
    have : v - prj W v ∈ W.topologicalClosureᗮ := Submodule.sub_starProjection_mem_orthogonal v
    exact this w (W.le_topologicalClosure hw)
  have hfix : ∀ w ∈ W, prj W w = w := by
    intro w hw
    refine Submodule.eq_starProjection_of_mem_orthogonal
      (W.le_topologicalClosure hw) ?_
    simp
  have hmem : ∀ x : ℝ, ∀ w, w ∈ eigIn W A x ↔ w ∈ W ∧ A w = (x : ℂ) • w := by
    intro x w
    simp [eigIn, Module.End.mem_eigenspace_iff]
  have hB : IsSelfAdjoint (A ∘L prj W) := by
    rw [ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric]
    intro u v
    change inner ℂ (A (prj W u)) v = inner ℂ u (A (prj W v))
    have h1 : inner ℂ (A (prj W u)) v = inner ℂ (A (prj W u)) (prj W v) := by
      have := hperp v _ (hAW _ (hPW u))
      rw [inner_sub_right, sub_eq_zero] at this
      exact this
    have h2 : inner ℂ u (A (prj W v)) = inner ℂ (prj W u) (A (prj W v)) := by
      have := hperp u _ (hAW _ (hPW v))
      rw [inner_sub_right, sub_eq_zero] at this
      rw [← inner_conj_symm, this, inner_conj_symm]
    rw [h1, h2]
    exact hA.isSymmetric _ _
  have hle : ∀ x : ℝ, eigIn W A x ≤
      Module.End.eigenspace ((A ∘L prj W : H →L[ℂ] H) : H →ₗ[ℂ] H) (x : ℂ) := by
    intro x w hw
    obtain ⟨hwW, hwA⟩ := (hmem x w).1 hw
    rw [Module.End.mem_eigenspace_iff]
    change A (prj W w) = _
    rw [hfix w hwW, hwA]
  have hfin := GroundTheory.Automorphic.CompactSelfAdjoint.finite_eigenvalues_norm_ge hC hB hη
  refine ⟨?_, ?_⟩
  · refine Set.Finite.of_finite_image (f := fun x : ℝ => (x : ℂ)) (hfin.subset ?_)
      (Complex.ofReal_injective.injOn)
    rintro _ ⟨x, ⟨hx, hne⟩, rfl⟩
    refine ⟨?_, ?_⟩
    · obtain ⟨w, hw, hw0⟩ := (Submodule.ne_bot_iff _).1 hne
      exact Module.End.hasEigenvalue_of_hasEigenvector ⟨hle x hw, hw0⟩
    · have : η ≤ |x| := hx.le.trans (le_abs_self x)
      simpa using this
  · intro x hx
    have hx0 : (x : ℂ) ≠ 0 := by
      have : x ≠ 0 := (hη.trans hx).ne'
      exact_mod_cast this
    haveI : FiniteDimensional ℂ (Module.End.eigenspace ((A ∘L prj W : H →L[ℂ] H) : H →ₗ[ℂ] H) (x : ℂ)) :=
      ContinuousLinearMap.finite_dimensional_eigenspace hC _ hx0
    exact Submodule.finiteDimensional_of_le (hle x)
end

-- bundled from Development.AutomorphicArithmetic.TwistedTraces.ExistsApproximateIdentityIntegrated
section
open MeasureTheory NumberField GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace
open GroundTheory.Automorphic.AutomorphicForm GroundTheory.Automorphic.CuspidalSpectrum UpperTheory.ConvolutionTheory.C Polynomial Topology

theorem UpperTheory.exists_approximate_identity_integrated :
    ∀ (G H : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G] [T2Space G] [MeasurableSpace G] [OpensMeasurableSpace G] [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] (π : UnitaryRep G H) (μ : Measure G) [IsFiniteMeasureOnCompacts μ] [μ.IsOpenPosMeasure] (N : Set G), N ∈ 𝓝 (1 : G) → ∃ f : CompactlySupportedContinuousMap G ℂ, ∀ (v : H) (r : ℝ), (∀ g ∈ N, ‖π g v - v‖ ≤ r) → ‖π.integrated μ (UnitaryRep.ccToL1 μ f) v - v‖ ≤ r := by
  intro G H _ _ _ _ _ _ _ _ _ _ π μ _ _ N hN
  obtain ⟨U, hUsub, hUo, h1U⟩ := mem_nhds_iff.1 hN
  obtain ⟨h, h1, h0, hcs, hrange⟩ := exists_continuous_one_zero_of_isCompact
    (isCompact_singleton (x := (1 : G))) hUo.isClosed_compl
    (Set.disjoint_singleton_left.2 fun h => h h1U)
  have hnn : ∀ g, 0 ≤ h g := fun g => (hrange g).1
  set c : ℝ := ∫ g, h g ∂μ with hc
  have hcpos : 0 < c := h.continuous.integral_pos_of_hasCompactSupport_nonneg_nonzero hcs hnn
    (by rw [h1 (Set.mem_singleton 1)]; exact one_ne_zero)
  let k : G → ℝ := fun g => c⁻¹ * h g
  have hkc : Continuous k := continuous_const.mul h.continuous
  have hkcs : HasCompactSupport k := by
    have : k = (fun _ => c⁻¹) * (h : G → ℝ) := rfl
    rw [this]
    exact hcs.mul_left
  have hknn : ∀ g, 0 ≤ k g := fun g => mul_nonneg (inv_nonneg.2 hcpos.le) (hnn g)
  have hkint : Integrable k μ := hkc.integrable_of_hasCompactSupport hkcs
  have hk1 : ∫ g, k g ∂μ = 1 := by
    simp only [k]
    rw [integral_const_mul, ← hc, inv_mul_cancel₀ hcpos.ne']
  let f : CompactlySupportedContinuousMap G ℂ :=
    ⟨⟨fun g => (k g : ℂ), by fun_prop⟩, hkcs.comp_left Complex.ofReal_zero⟩
  have hfg : ∀ g, f g = (k g : ℂ) := fun _ => rfl
  refine ⟨f, fun v r hr => ?_⟩
  have hint1 : Integrable (fun g => f g • π g v) μ :=
    (f.continuous.smul (π.continuous_orbit v)).integrable_of_hasCompactSupport
      f.hasCompactSupport.smul_right
  have hint2 : Integrable (fun g => f g • v) μ :=
    (f.continuous.smul continuous_const).integrable_of_hasCompactSupport
      f.hasCompactSupport.smul_right
  have hv : ∫ g, f g • v ∂μ = v := by
    rw [integral_smul_const]
    simp only [hfg]
    have : ∫ g, (k g : ℂ) ∂μ = ((1 : ℝ) : ℂ) := by
      rw [← hk1]; exact integral_ofReal
    rw [this]
    simp
  have key : π.integrated μ (UnitaryRep.ccToL1 μ f) v - v = ∫ g, f g • (π g v - v) ∂μ := by
    simp only [smul_sub]
    rw [integral_sub hint1 hint2, hv, UnitaryRep.integrated_ccToL1_apply]
  have hbound : ‖∫ g, f g • (π g v - v) ∂μ‖ ≤ ∫ g, k g * r ∂μ := by
    refine norm_integral_le_of_norm_le (hkint.mul_const _) (Filter.Eventually.of_forall fun g => ?_)
    rw [norm_smul, hfg, Complex.norm_real, Real.norm_of_nonneg (hknn g)]
    by_cases hg : g ∈ U
    · exact mul_le_mul_of_nonneg_left (hr g (hUsub hg)) (hknn g)
    · have : k g = 0 := by
        simp only [k]
        rw [h0 hg]
        simp
      rw [this]
      simp
  rw [key]
  rw [integral_mul_const, hk1, one_mul] at hbound
  exact hbound
end

-- bundled from Development.AutomorphicArithmetic.TwistedTraces.ExistsBoundOfIsRootExpMulForall
section
open MeasureTheory NumberField GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace
open GroundTheory.Automorphic.AutomorphicForm GroundTheory.Automorphic.CuspidalSpectrum UpperTheory.ConvolutionTheory.C Polynomial Topology

theorem UpperTheory.exists_bound_of_isRoot_exp_mul_forall :
    ∀ (d : ℕ) (p : ℝ → ℂ[X]), (∀ t, p t ≠ 0 ∧ (p t).natDegree ≤ d) → ∃ M : ℝ, ∀ z : ℂ, (∀ t : ℝ, (p t).IsRoot (Complex.exp (z * t))) → ‖z‖ ≤ M := by
  intro d p hp
  classical
  have hfin : Set.Finite {z : ℂ | ∀ t : ℝ, (p t).IsRoot (Complex.exp (z * t))} := by
    by_contra hinf
    obtain ⟨F, hF, hcard⟩ := Set.Infinite.exists_subset_card_eq hinf (d + 1)
    obtain ⟨R, hR⟩ := (F.finite_toSet.isBounded).exists_norm_le
    set S : ℝ := |R| + 1 with hS
    have hSpos : 0 < S := by positivity
    have hRS : ∀ z ∈ F, ‖z‖ ≤ S := fun z hz => by
      have h1 := hR z (Finset.mem_coe.mpr hz)
      have h2 := le_abs_self R
      linarith
    set t : ℝ := S⁻¹ with ht
    have htpos : 0 < t := inv_pos.mpr hSpos
    have hn : ∀ z ∈ F, ‖z * (t : ℂ)‖ ≤ 1 := fun z hz => by
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos htpos, ht]
      rw [mul_inv_le_iff₀ hSpos, one_mul]
      exact hRS z hz
    have hinj : Set.InjOn (fun z : ℂ => Complex.exp (z * (t : ℂ))) F := by
      intro z hz w hw h
      obtain ⟨n, hn'⟩ := Complex.exp_eq_exp_iff_exists_int.mp h
      have h1 := hn z hz
      have h2 := hn w hw
      have h3 : ‖(n : ℂ) * (2 * Real.pi * Complex.I)‖ ≤ 2 := by
        have : (n : ℂ) * (2 * Real.pi * Complex.I) = z * t - w * t := by rw [hn']; ring
        rw [this]
        have := norm_sub_le (z * (t : ℂ)) (w * t)
        linarith
      have hn0 : n = 0 := by
        by_contra hne
        have h4 : (1 : ℝ) ≤ |(n : ℝ)| := by exact_mod_cast Int.one_le_abs hne
        have h5 : ‖(n : ℂ) * (2 * Real.pi * Complex.I)‖ = |(n : ℝ)| * (2 * Real.pi) := by
          simp [abs_of_pos Real.pi_pos]
        have h6 := Real.pi_gt_three
        rw [h5] at h3
        nlinarith
      rw [hn0] at hn'
      have htne : (t : ℂ) ≠ 0 := by exact_mod_cast htpos.ne'
      have : z * (t : ℂ) = w * t := by simpa using hn'
      exact mul_right_cancel₀ htne this
    have hsub : (F.image (fun z : ℂ => Complex.exp (z * (t : ℂ)))).val ⊆ (p t).roots := by
      intro x hx
      obtain ⟨z, hz, rfl⟩ := Finset.mem_image.mp (Finset.mem_val.mp hx)
      exact (Polynomial.mem_roots (hp t).1).mpr (hF (Finset.mem_coe.mpr hz) t)
    have hle := Polynomial.card_le_degree_of_subset_roots hsub
    rw [Finset.card_image_of_injOn hinj, hcard] at hle
    have := (hp t).2
    omega
  obtain ⟨M, hM⟩ := hfin.isBounded.exists_norm_le
  exact ⟨M, fun z hz => hM z hz⟩
end

-- bundled from Development.AutomorphicArithmetic.TwistedTraces.ExistsHilbertBasisPrjEigenvectorsOfIsCompactOper
section
open MeasureTheory NumberField GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace
open GroundTheory.Automorphic.AutomorphicForm GroundTheory.Automorphic.CuspidalSpectrum UpperTheory.ConvolutionTheory.C

theorem UpperTheory.exists_hilbertBasis_prj_eigenvectors_of_isCompactOperator :
    ∀ (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] (W : Submodule ℂ H) (A : H →L[ℂ] H), IsClosed (W : Set H) → IsSelfAdjoint A → (∀ v ∈ W, A v ∈ W) → IsCompactOperator (A ∘L prj W) → ∃ (s : Set H) (b : HilbertBasis s ℂ H), ∀ i, ∃ μ : ℝ, A (prj W (b i)) = (μ : ℂ) • prj W (b i) := by
  intro H _ _ _ W A hW hsa hinv hK
  have hcl : W.topologicalClosure = W := hW.submodule_topologicalClosure_eq
  have hmem : ∀ u, prj W u ∈ W := fun u =>
    hcl.le (Submodule.starProjection_apply_mem W.topologicalClosure u)
  have hfix : ∀ w ∈ W, prj W w = w := fun w hw =>
    Submodule.starProjection_eq_self_iff.mpr (W.le_topologicalClosure hw)
  have hPsym : ∀ x y : H, inner ℂ (prj W x) y = inner ℂ x (prj W y) := fun x y =>
    Submodule.inner_starProjection_left_eq_right W.topologicalClosure x y
  have hAsym : ∀ x y : H, inner ℂ (A x) y = inner ℂ x (A y) :=
    ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mp hsa
  have hBsa : IsSelfAdjoint (A ∘L prj W) := by
    refine ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mpr fun u v => ?_
    change inner ℂ (A (prj W u)) v = inner ℂ u (A (prj W v))
    calc inner ℂ (A (prj W u)) v = inner ℂ (prj W (A (prj W u))) v := by
          rw [hfix _ (hinv _ (hmem u))]
      _ = inner ℂ (A (prj W u)) (prj W v) := hPsym _ _
      _ = inner ℂ (prj W u) (A (prj W v)) := hAsym _ _
      _ = inner ℂ u (prj W (A (prj W v))) := hPsym _ _
      _ = inner ℂ u (A (prj W v)) := by rw [hfix _ (hinv _ (hmem v))]
  obtain ⟨s, b, hb, hev⟩ :=
    GroundTheory.Automorphic.CompactSelfAdjoint.exists_hilbertBasis_eigenvectors hK hBsa
  refine ⟨s, b, fun i => ?_⟩
  have hbi : b i ∈ s := by
    rw [hb]
    exact i.2
  obtain ⟨μ, hμ⟩ := hev (b i) hbi
  have hμ' : A (prj W (b i)) = (μ : ℂ) • b i := hμ
  refine ⟨μ, ?_⟩
  have h2 : prj W (A (prj W (b i))) = (μ : ℂ) • prj W (b i) := by
    rw [hμ', map_smul]
  rw [← h2, hfix _ (hinv _ (hmem _))]
end

-- bundled from Development.AutomorphicArithmetic.TwistedTraces.ExistsNhdsOneNormOneGLFactorization
section
open MeasureTheory NumberField GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace
open GroundTheory.Automorphic.AutomorphicForm GroundTheory.Automorphic.CuspidalSpectrum UpperTheory.ConvolutionTheory.C Polynomial Topology

theorem UpperTheory.exists_nhds_one_normOneGL_factorization :
    ∀ (K : Type) [Field K] [NumberField K] (n : ℕ) (N : Set (archGroup K n)) (U : Subgroup (AdelicGLn.integralFiniteGL K n)), N ∈ 𝓝 (1 : archGroup K n) → IsOpen (U : Set (AdelicGLn.integralFiniteGL K n)) → ∃ N' ∈ 𝓝 (1 : normOneGL (K := K) (n := n)), ∀ g ∈ N', ∃ a ∈ N, ∃ u ∈ U, g = archP K n a * retractOne (finEmb K n (u : AdelicGLn.integralFiniteGL K n)) := by
  intro K _ _ n N U hN hU
  have hU' : IsOpen (Subtype.val '' (U : Set (AdelicGLn.integralFiniteGL K n))) :=
    (AdelicGLn.isOpen_integralFiniteGL K n).isOpenMap_subtype_val _ hU
  have hp : Continuous fun g : normOneGL (K := K) (n := n) => AdelicGLn.prodEquiv K n (g : AdelicGLn.AdelicGL K n) :=
    (AdelicGLn.prodEquiv K n).continuous.comp continuous_subtype_val
  have ha : Continuous fun g : normOneGL (K := K) (n := n) =>
      archEquiv K n (AdelicGLn.prodEquiv K n (g : AdelicGLn.AdelicGL K n)).1 :=
    (archEquiv K n).continuous.comp hp.fst
  have hf : Continuous fun g : normOneGL (K := K) (n := n) =>
      (AdelicGLn.prodEquiv K n (g : AdelicGLn.AdelicGL K n)).2 := hp.snd
  refine ⟨(fun g : normOneGL (K := K) (n := n) =>
      archEquiv K n (AdelicGLn.prodEquiv K n (g : AdelicGLn.AdelicGL K n)).1) ⁻¹' N ∩
    (fun g : normOneGL (K := K) (n := n) => (AdelicGLn.prodEquiv K n (g : AdelicGLn.AdelicGL K n)).2) ⁻¹'
      (Subtype.val '' (U : Set (AdelicGLn.integralFiniteGL K n))), Filter.inter_mem ?_ ?_, ?_⟩
  · refine ha.continuousAt.preimage_mem_nhds ?_
    simpa only [OneMemClass.coe_one, map_one, Prod.fst_one] using hN
  · refine (hU'.preimage hf).mem_nhds ⟨1, U.one_mem, ?_⟩
    simp only [OneMemClass.coe_one, map_one, Prod.snd_one]
  · rintro g ⟨hg, u, hu, e⟩
    refine ⟨_, hg, u, hu, ?_⟩
    have e' : (u : AdelicGLn.FiniteAdelicGL K n) = (AdelicGLn.prodEquiv K n (g : AdelicGLn.AdelicGL K n)).2 := e
    rw [e']
    calc g = retractOne (g : AdelicGLn.AdelicGL K n) := (retractOne_coe g).symm
      _ = retractOne (infEmb K n (archEquiv K n (AdelicGLn.prodEquiv K n g).1) *
            finEmb K n (AdelicGLn.prodEquiv K n g).2) := by rw [infEmb_mul_finEmb]
      _ = _ := by rw [retractOne_mul, retract_infEmb]
end

-- bundled from Development.AutomorphicArithmetic.TwistedTraces.ExistsSignedOrthonormalBasisOfIsCompl
section
open MeasureTheory NumberField GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace
open GroundTheory.Automorphic.AutomorphicForm GroundTheory.Automorphic.CuspidalSpectrum UpperTheory.ConvolutionTheory.C Polynomial Topology

theorem UpperTheory.exists_signed_orthonormal_basis_of_isCompl :
    ∀ (V : Type) [AddCommGroup V] [Module ℝ V] [FiniteDimensional ℝ V] (B : LinearMap.BilinForm ℝ V) (k p : Submodule ℝ V), IsCompl k p → (∀ X Y, B X Y = B Y X) → (∀ X ∈ k, X ≠ 0 → B X X < 0) → (∀ X ∈ p, X ≠ 0 → 0 < B X X) → (∀ X ∈ k, ∀ Y ∈ p, B X Y = 0) → ∃ (d : ℕ) (b : Module.Basis (Fin d) ℝ V) (ε : Fin d → ℝ), (∀ i, ε i = 1 ∨ ε i = -1) ∧ (∀ i j, B (b i) (b j) = if i = j then ε i else 0) ∧ ∀ i, ε i = -1 → b i ∈ k := by
  intro V _ _ _ B k p hc hsymm hneg hpos hzero
  classical
  obtain ⟨bk, hbk⟩ := exists_signed_basis (B.restrict k)
    (fun x y => hsymm (x : V) y) (s := -1)
    (by norm_num) (fun v hv => by
      have h0 : (v : V) ≠ 0 := fun e => hv (Subtype.ext e)
      have := hneg v v.2 h0
      change 0 < _ * B (v : V) v
      linarith)
  obtain ⟨bp, hbp⟩ := exists_signed_basis (B.restrict p)
    (fun x y => hsymm (x : V) y) (s := 1)
    (by norm_num) (fun v hv => by
      have h0 : (v : V) ≠ 0 := fun e => hv (Subtype.ext e)
      have := hpos v v.2 h0
      change 0 < _ * B (v : V) v
      linarith)
  set e := Submodule.prodEquivOfIsCompl k p hc
  set b0 := (bk.prod bp).map e
  set f : Fin (Module.finrank ℝ k) ⊕ Fin (Module.finrank ℝ p) → V :=
    Sum.elim (fun i => (bk i : V)) (fun j => (bp j : V))
  have hb0 : ∀ x, b0 x = f x := by
    rintro (i | j)
    · simp [b0, e, f, Submodule.coe_prodEquivOfIsCompl']
    · simp [b0, e, f, Submodule.coe_prodEquivOfIsCompl']
  set ε0 : Fin (Module.finrank ℝ k) ⊕ Fin (Module.finrank ℝ p) → ℝ :=
    Sum.elim (fun _ => -1) (fun _ => 1)
  have horth : ∀ x y, B (b0 x) (b0 y) = if x = y then ε0 x else 0 := by
    intro x y
    rw [hb0, hb0]
    rcases x with i | i <;> rcases y with j | j
    · have := hbk i j
      change B _ _ = _ at this
      simp only [f, ε0, Sum.elim_inl, Sum.inl.injEq]
      exact this
    · simp only [f, ε0, Sum.elim_inl, Sum.elim_inr, reduceCtorEq, if_false]
      exact hzero _ (bk i).2 _ (bp j).2
    · simp only [f, ε0, Sum.elim_inl, Sum.elim_inr, reduceCtorEq, if_false]
      rw [hsymm]
      exact hzero _ (bk j).2 _ (bp i).2
    · have := hbp i j
      change B _ _ = _ at this
      simp only [f, ε0, Sum.elim_inr, Sum.inr.injEq]
      exact this
  set σ := finSumFinEquiv (m := Module.finrank ℝ k) (n := Module.finrank ℝ p)
  refine ⟨_, b0.reindex σ, ε0 ∘ σ.symm, fun i => ?_, fun i j => ?_, fun i hi => ?_⟩
  · rcases hx : σ.symm i with a | a <;> simp [ε0, hx]
  · rw [Module.Basis.reindex_apply, Module.Basis.reindex_apply, horth]
    simp only [Function.comp_apply, σ.symm.injective.eq_iff]
  · rw [Module.Basis.reindex_apply, hb0]
    simp only [Function.comp_apply] at hi
    rcases hx : σ.symm i with a | a
    · simp only [f, Sum.elim_inl]
      exact (bk a).2
    · rw [hx] at hi
      simp [ε0] at hi
      norm_num at hi
end

-- bundled from Development.AutomorphicArithmetic.TwistedTraces.FiniteDimensionalOfCompactNearIdentity
section
open MeasureTheory NumberField GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace
open GroundTheory.Automorphic.AutomorphicForm GroundTheory.Automorphic.CuspidalSpectrum UpperTheory.ConvolutionTheory.C Polynomial Topology

theorem UpperTheory.finiteDimensional_of_compact_near_identity :
    ∀ (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] (T : H →L[ℂ] H) (S : Submodule ℂ H), IsCompactOperator T → (∀ v ∈ S, ‖T v - v‖ ≤ 1 / 2 * ‖v‖) → FiniteDimensional ℂ S := by
  intro H _ _ _ T S hT hS
  have hcl : IsClosed {v : H | ‖T v - v‖ ≤ 1 / 2 * ‖v‖} :=
    isClosed_le (by fun_prop) (by fun_prop)
  have hS' : ∀ v ∈ S.topologicalClosure, ‖T v - v‖ ≤ 1 / 2 * ‖v‖ := by
    intro v hv
    have : closure (S : Set H) ⊆ {v : H | ‖T v - v‖ ≤ 1 / 2 * ‖v‖} :=
      closure_minimal (fun w hw => hS w hw) hcl
    exact this hv
  haveI : CompleteSpace S.topologicalClosure :=
    S.isClosed_topologicalClosure.completeSpace_coe
  let f : S.topologicalClosure →L[ℂ] H := T.comp S.topologicalClosure.subtypeL
  have hf : ∀ x : S.topologicalClosure, ‖x‖ ≤ ((2 : NNReal) : ℝ) * ‖f x‖ := by
    intro x
    have h1 := hS' x.1 x.2
    have h2 : ‖(x : H)‖ ≤ ‖T x‖ + ‖T x - x‖ := by
      have : (x : H) = T x - (T x - x) := by abel
      calc ‖(x : H)‖ = ‖T x - (T x - x)‖ := congrArg norm this
        _ ≤ _ := norm_sub_le _ _
    have h3 : ‖x‖ = ‖(x : H)‖ := rfl
    have h4 : f x = T x := rfl
    rw [h3, h4]
    push_cast
    linarith
  have hanti : AntilipschitzWith 2 f := f.antilipschitz_of_bound hf
  have hemb : IsClosedEmbedding f := hanti.isClosedEmbedding f.uniformContinuous
  obtain ⟨K, hK, hKsub⟩ := IsCompactOperator.image_closedBall_subset_compact (f := (T : H →ₗ[ℂ] H)) hT 1
  have hc : IsCompact (Metric.closedBall (0 : S.topologicalClosure) 1) := by
    refine (hemb.isCompact_preimage hK).of_isClosed_subset Metric.isClosed_closedBall ?_
    intro x hx
    apply hKsub
    refine ⟨(x : H), ?_, rfl⟩
    rw [mem_closedBall_zero_iff] at hx ⊢
    exact hx
  haveI : FiniteDimensional ℂ S.topologicalClosure :=
    FiniteDimensional.of_isCompact_closedBall₀ ℂ one_pos hc
  exact Submodule.finiteDimensional_of_le S.le_topologicalClosure
end

