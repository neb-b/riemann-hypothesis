module

public import Mathlib
public import Development.AutomorphicArithmetic.Foundations.Convolution.TraceSplitting.NormCharSplit
public import Development.AutomorphicArithmetic.Foundations.Convolution.PowerSumTraces.Bundle0001
public import Development.AutomorphicArithmetic.Foundations.Convolution.PowerSumTraces.Bundle0002
public import Development.AutomorphicArithmetic.Foundations.Convolution.CentreSplitting.CuspidalMultiplicityOneTotallyComplex
public import Development.AutomorphicArithmetic.Foundations.Convolution.ConvolutionKernels.KernelTransforms.Bundle0008
public import Development.AutomorphicArithmetic.Foundations.Convolution.ConvolutionKernels.KernelTransforms.Bundle0004
public import Development.AutomorphicArithmetic.Foundations.Convolution.ConvolutionKernels.KernelTransforms.RrTens
public import GroundTheory.AutomorphicForms.Bundle0001
public import Development.AutomorphicArithmetic.Foundations.Convolution.IntegrableConvolution.LineRank
public import Development.AutomorphicArithmetic.Foundations.Convolution.PowerSumTraces.Bundle0005
public import Development.AutomorphicArithmetic.Foundations.Convolution.CentreSplitting.Bundle0004
public import Development.AutomorphicArithmetic.Foundations.Convolution.CentreSplitting.Bundle0005
public import Development.AutomorphicArithmetic.Foundations.Convolution.TwistedLocalOrbits.HoweLine
public import Development.AutomorphicArithmetic.Foundations.Convolution.TwistedLocalOrbits.Bundle0001
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.GL4HoweTheory.Bundle0003
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.GL4HoweTheory.Bundle0001
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.OrbitalIntegrals.TwistedOrbitalIntegrals.Bundle0003
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.OrbitalIntegrals.TwistedOrbitalIntegrals.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0679
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1025
public import Development.AutomorphicArithmetic.Foundations.Convolution.IntegrableConvolution.TypedEx
public import Development.AutomorphicArithmetic.Foundations.Convolution.IntegrableConvolution.EigBasic
public import Development.AutomorphicArithmetic.Foundations.Convolution.GeneralizedMeasures.Bundle0002

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.Foundations.Convolution.TraceSplitting.AmpFin
section
open MeasureTheory NumberField IsDedekindDomain
open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace
open GroundTheory.Automorphic.AutomorphicForm GroundTheory.Automorphic.CuspidalSpectrum UpperTheory.ConvolutionTheory UpperTheory.ConvolutionTheory.C
open scoped InnerProductSpace

private theorem exists_pos_eig {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (W V : Submodule ℂ H) (hV : IsClosed (V : Set H)) (hVW : V ≤ W) (A : H →L[ℂ] H) (hA : 0 ≤ A)
    (hAV : ∀ v ∈ V, A v ∈ V) (hc : IsCompactOperator (A ∘L prj W)) (h : ∃ v ∈ V, A v ≠ 0) :
    ∃ x : ℝ, 0 < x ∧ eigIn V A x ≠ ⊥ := by
  have hs : IsSelfAdjoint A := GroundTheory.Automorphic.isSelfAdjoint_of_nonneg hA
  have hcl : V.topologicalClosure = V := hV.submodule_topologicalClosure_eq
  have hPV : ∀ v, prj V v ∈ V := fun v => by
    have h1 : prj V v ∈ V.topologicalClosure := V.topologicalClosure.starProjection_apply_mem v
    rwa [hcl] at h1
  have hPfix : ∀ v ∈ V, prj V v = v := fun v hv =>
    Submodule.starProjection_eq_self_iff.2 (by rw [hcl]; exact hv)
  have hWfix : ∀ v, prj W (prj V v) = prj V v := fun v =>
    Submodule.starProjection_eq_self_iff.2 (W.le_topologicalClosure (hVW (hPV v)))
  have hPs : ContinuousLinearMap.adjoint (prj V) = prj V :=
    (ContinuousLinearMap.isSelfAdjoint_iff'.1 (isSelfAdjoint_starProjection _))
  set B : H →L[ℂ] H := prj V ∘L A ∘L prj V with hB
  have hBc : IsCompactOperator B := by
    have e : B = prj V ∘L ((A ∘L prj W) ∘L prj V) := by
      refine ContinuousLinearMap.ext fun v => ?_
      simp only [hB, ContinuousLinearMap.comp_apply, hWfix]
    rw [e]
    exact (hc.comp_clm (prj V)).clm_comp (prj V)
  have hBs : IsSelfAdjoint B := by
    have h1 := hs.conj_adjoint (prj V)
    rwa [hPs] at h1
  have hBv : ∀ v ∈ V, B v = A v := fun v hv => by
    simp only [hB, ContinuousLinearMap.comp_apply, hPfix v hv, hPfix _ (hAV v hv)]
  obtain ⟨s, b, l, -, hTb₀, hsum, -⟩ := GroundTheory.Automorphic.CompactSelfAdjoint.exists_hilbertBasis_eigenvectors_hasSum hBc hBs
  have hTb : ∀ i, B (b i) = ((l i : ℝ) : ℂ) • b i := fun i => by
    rw [hTb₀ i]
    rfl
  obtain ⟨v, hv, hv0⟩ := h
  obtain ⟨i, hi⟩ : ∃ i, l i ≠ 0 := by
    by_contra hcon
    push_neg at hcon
    have h0 : HasSum (fun i => (((l i : ℝ) : ℂ) * ⟪b i, v⟫_ℂ) • b i) (0 : H) := by
      simp only [hcon, Complex.ofReal_zero, zero_mul, zero_smul]
      exact hasSum_zero
    exact hv0 (by rw [← hBv v hv]; exact (hsum v).unique h0)
  have hw0 : b i ≠ 0 := b.orthonormal.ne_zero i
  have hli : ((l i : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hi
  have hwV : b i ∈ V := by
    have h1 : b i = ((l i : ℝ) : ℂ)⁻¹ • B (b i) := by
      rw [hTb i, smul_smul, inv_mul_cancel₀ hli, one_smul]
    rw [h1]
    exact V.smul_mem _ (hPV _)
  have hAw : A (b i) = ((l i : ℝ) : ℂ) • b i := by rw [← hBv _ hwV, hTb i]
  have hpos : 0 < l i := by
    have h1 := ((ContinuousLinearMap.nonneg_iff_isPositive).1 hA).re_inner_nonneg_right (b i)
    have hn : ⟪b i, b i⟫_ℂ = 1 := by
      rw [inner_self_eq_norm_sq_to_K, b.orthonormal.1 i]
      simp
    rw [hAw, inner_smul_right, hn] at h1
    simp only [mul_one, RCLike.re_to_complex, Complex.ofReal_re] at h1
    exact lt_of_le_of_ne h1 hi.symm
  refine ⟨l i, hpos, (Submodule.ne_bot_iff _).2 ⟨b i, Submodule.mem_inf.2 ⟨hwV, ?_⟩, hw0⟩⟩
  exact Module.End.mem_eigenspace_iff.2 hAw

theorem UpperTheory.ConvolutionTheory.T.ampFin :
    UpperTheory.ConvolutionTheory.T.AmpFin := by
  intro K _ _ _ n hn μ _ 𝔞
  obtain ⟨hA0, -, -, -⟩ := UpperTheory.ConvolutionTheory.evEx K n hn μ 𝔞
  have hUc : IsCompact (𝔞.U : Set (AdelicGLn.FiniteAdelicGL K n)) :=
    (AdelicGLn.isCompact_integralFiniteGL K n).of_isClosed_subset (𝔞.U.isClosed_of_isOpen 𝔞.isOpen)
      fun _ h => 𝔞.le h
  obtain ⟨m, hm, hC⟩ := (UpperTheory.ConvolutionTheory.Tf.compatEx K n hn).2.1 μ 𝔞.ν
  haveI := hm
  obtain ⟨e, -, he⟩ := UpperTheory.ConvolutionTheory.Tf.prjFix K n μ m 𝔞.U 𝔞.isOpen hUc
  have hAR : RR μ (tens 𝔞.a₀ e) = 𝔞.A := by
    rw [UpperTheory.ConvolutionTheory.Tf.rrTens K n hn μ 𝔞.ν m hC, he]
    rfl
  obtain ⟨hsum, hcusp, hcpt⟩ := opBasics K n μ (tens 𝔞.a₀ e)
  rw [hAR] at hsum hcusp hcpt
  have hs : IsSelfAdjoint 𝔞.A := GroundTheory.Automorphic.isSelfAdjoint_of_nonneg hA0
  refine ⟨fun x hx => ?_, fun V hV hv =>
    exists_pos_eig (cuspidalL2 μ) V hV.closed hV.le 𝔞.A hA0 (hsum V hV) hcpt hv⟩
  have hfd : FiniteDimensional ℂ (eigIn (cuspidalL2 μ) 𝔞.A x) := by
    obtain ⟨S, hS, hf, -⟩ := eigSplit (LL μ) (cuspidalL2 μ) 𝔞.A (isClosed_cuspidalL2 μ) hA0 hcusp hcpt (x / 2) (by linarith)
    by_cases h : eigIn (cuspidalL2 μ) 𝔞.A x = ⊥
    · rw [h]
      infer_instance
    · exact hf x ((hS x).2 ⟨by linarith, h⟩)
  obtain ⟨s, hs', -⟩ := eigSummands (LL μ) {V : Submodule ℂ (LL μ) // IsSummand μ V} (fun i => i.1) (cuspidalL2 μ) 𝔞.A x
    (fun i => i.2.closed) (fun i j hij => Dp.multiplicity_one_cuspidal_spectrum_normOneGL K n μ i.1 j.1 i.2 j.2 fun h => hij (Subtype.ext h))
    (summandsSpan K n μ) hs (fun i => hsum i.1 i.2) hfd
  classical
  refine (s.image Subtype.val).finite_toSet.subset ?_
  rintro V ⟨hV, hne⟩
  exact Finset.mem_coe.2 (Finset.mem_image.2 ⟨⟨V, hV⟩, (hs' _).2 hne, rfl⟩)
end

-- bundled from Development.AutomorphicArithmetic.Foundations.Convolution.TraceSplitting.GoodEx
section
theorem UpperTheory.ConvolutionTheory.T.goodEx :
    UpperTheory.ConvolutionTheory.T.GoodEx := by
  intro n hn
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  set S : ℤ := ∑ k : Fin m, ((m : ℤ) + 1 - (k : ℕ)) with hS
  have hS0 : 0 ≤ S := by
    refine Finset.sum_nonneg fun k _ => ?_
    have := k.isLt
    omega
  let ν : Fin (m + 1) → ℤ := fun i => if i = Fin.last m then -S else (m : ℤ) + 1 - (i : ℕ)
  have hlast : ν (Fin.last m) = -S := by simp [ν]
  have hcast : ∀ k : Fin m, ν k.castSucc = (m : ℤ) + 1 - (k : ℕ) := by
    intro k
    have : k.castSucc ≠ Fin.last m := (Fin.castSucc_lt_last k).ne
    simp [ν, this]
  have hne : ∀ i : Fin (m + 1), i ≠ Fin.last m → ν i = (m : ℤ) + 1 - (i : ℕ) := by
    intro i hi
    simp [ν, hi]
  have hpos : ∀ i : Fin (m + 1), i ≠ Fin.last m → 0 < ν i := by
    intro i hi
    rw [hne i hi]
    have := i.isLt
    omega
  have hsum : ∑ i, ν i = 0 := by
    rw [Fin.sum_univ_castSucc, hlast]
    simp only [hcast]
    rw [← hS]
    ring
  have hJ : ∀ J : Finset (Fin (m + 1)), J.Nonempty → Fin.last m ∉ J → 0 < ∑ i ∈ J, ν i := by
    intro J hJ hl
    refine Finset.sum_pos (fun i hi => hpos i ?_) hJ
    rintro rfl
    exact hl hi
  refine ⟨ν, ?_, hsum, ?_⟩
  · intro i j hij
    by_cases hj : j = Fin.last m
    · have hi : i ≠ Fin.last m := by
        rintro rfl
        subst hj
        exact lt_irrefl _ hij
      have h1 := hpos i hi
      have h2 : ν j = -S := by rw [hj, hlast]
      show ν j < ν i
      omega
    · have hi : i ≠ Fin.last m := by
        rintro rfl
        exact absurd (Fin.le_last j) (not_le.mpr hij)
      show ν j < ν i
      rw [hne i hi, hne j hj]
      have : (i : ℕ) < (j : ℕ) := hij
      omega
  · intro J hJne hJu
    by_cases hl : Fin.last m ∈ J
    · have hc : Jᶜ.Nonempty := by
        rw [Finset.nonempty_iff_ne_empty]
        intro h
        exact hJu (by simpa using h)
      have h1 := hJ Jᶜ hc (by simpa using hl)
      have h2 : ∑ i ∈ J, ν i + ∑ i ∈ Jᶜ, ν i = 0 := by
        rw [Finset.sum_add_sum_compl, hsum]
      omega
    · exact (hJ J hJne hl).ne'
end

-- bundled from Development.AutomorphicArithmetic.Foundations.Convolution.TraceSplitting.HoweType
section
open MeasureTheory NumberField IsDedekindDomain ValuativeRel GroundTheory.Global GroundTheory.Global.SemiLocal
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil UpperTheory.ConvolutionTheory.C UpperTheory.ConvolutionTheory.L1 UpperTheory.ConvolutionTheory.Loc UpperTheory.V.Z.Tf.L4

private theorem ball_sub_nhds (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (n : ℕ) (N : Set (GL (Fin n) k)) (hN : N ∈ nhds (1 : GL (Fin n) k)) :
    ∃ ρ : ValueGroupWithZero k, 0 < ρ ∧ ball n ρ ⊆ N := by
  obtain ⟨d, -, h⟩ := GlobalTheory.GamMul.NearOne.one_add_small_near_one k n N hN
  refine ⟨valuation k (d : k), ?_, fun g hg => ?_⟩
  · exact zero_lt_iff.2 ((Valuation.ne_zero_iff _).2 d.ne_zero)
  · obtain ⟨A, hA, hAN, -⟩ := h ((g : Matrix (Fin n) (Fin n) k) - 1) (fun i j => hg i j)
    have e : A = g := Units.ext (by rw [hA]; simp)
    exact e ▸ hAN

private theorem local_type (k E : Type) [Field k] [CharZero k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    [Field E] [ValuativeRel E] [TopologicalSpace E] [IsNonarchimedeanLocalField E]
    [Algebra k E] [ValuativeExtension k E] [FiniteDimensional k E] [IsGalois k E] (s : E ≃ₐ[k] E)
    (n : ℕ) (W : Type) [AddCommGroup W] [Module ℂ W] (π : Representation ℂ (GL (Fin n) E) W) (hs : IsSmooth π)
    (hi : π.IsIrreducible) (hg : GlobalTheory.LocGL.IsGeneric π) (N : Set (GL (Fin n) E)) (hN : N ∈ nhds (1 : GL (Fin n) E)) :
    ∃ (J : Subgroup (GL (Fin n) E)) (χ : GL (Fin n) E → ℂ) (e : W), CO J ∧ IsChr J χ ∧ (J : Set (GL (Fin n) E)) ⊆ N ∧
      e ≠ 0 ∧ (∀ g ∈ J, π g e = χ g • e) ∧ (∀ x : W, (∀ g ∈ J, π g x = χ g • x) → ∃ c : ℂ, x = c • e) ∧
      ∀ y ∈ J, Matrix.GeneralLinearGroup.map (s : E →+* E) y ∈ J ∧
        χ (Matrix.GeneralLinearGroup.map (s : E →+* E) y) = χ y := by
  obtain ⟨ϖ, hϖ⟩ : ∃ ϖ : Eˣ, valuation E (ϖ : E) = uniformizer E := by
    obtain ⟨x, hx⟩ := valuation_surjective (K := E) (uniformizer E)
    exact ⟨Units.mk0 x fun h => uniformizer_ne_zero (R := E) (by rw [← hx, h, map_zero]), hx⟩
  obtain ⟨ρ, hρ, hρN⟩ := ball_sub_nhds E n N hN
  obtain ⟨c, hc⟩ := psiInv k E ϖ hϖ
  obtain ⟨a₁, h₁⟩ := howeLine E n W π hs hi hg ϖ hϖ c
  obtain ⟨a₂, h₂⟩ := howeBall E n ϖ hϖ c ρ hρ
  obtain ⟨a, ha, ψ, hψ, hinv⟩ := hc (max 1 (max a₁ a₂))
  have ha1 : 1 ≤ a := le_trans (le_max_left _ _) ha
  obtain ⟨J, hJ, ho, hk⟩ := howeGroup E n ϖ hϖ a c ha1
  obtain ⟨hlc, hmul⟩ := howeChar E n ϖ hϖ a c ha1 ψ hψ
  have hmem : ∀ x, x ∈ J ↔ x ∈ howeSet n ϖ a c := fun x => by rw [← hJ]; rfl
  have hline := h₁ a (le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) ha) ψ hψ
  obtain ⟨⟨e, he⟩, he0, hspan⟩ := finrank_eq_one_iff'.1 hline
  refine ⟨J, fun x => (ψ (GlobalTheory.Whittaker.superDiag x) : ℂ), e, ⟨hk, ho⟩, ⟨hlc, fun x _ => Circle.norm_coe _, fun x hx y hy => ?_⟩, ?_,
    fun h => he0 (Subtype.ext h), fun g hgJ => he g ((hmem g).1 hgJ), fun x hx => ?_, fun y hy => ?_⟩
  · beta_reduce
    rw [hmul x ((hmem x).1 hx) y ((hmem y).1 hy), Circle.coe_mul]
  · rw [hJ]
    exact (h₂ a (le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) ha)).trans hρN
  · obtain ⟨t, ht⟩ := hspan ⟨x, fun g hg => hx g ((hmem g).2 hg)⟩
    exact ⟨t, (congrArg Subtype.val ht).symm⟩
  · have hy' := (hmem y).1 hy
    have hent : ∀ i j, ((Matrix.GeneralLinearGroup.map (s : E →+* E) y : GL (Fin n) E) : Matrix (Fin n) (Fin n) E) i j =
        s ((y : Matrix (Fin n) (Fin n) E) i j) := fun _ _ => rfl
    refine ⟨(hmem _).2 fun i j => ?_, ?_⟩
    · have e1 : ((Matrix.GeneralLinearGroup.map (s : E →+* E) y : GL (Fin n) E) : Matrix (Fin n) (Fin n) E) i j -
          (1 : Matrix (Fin n) (Fin n) E) i j = s ((y : Matrix (Fin n) (Fin n) E) i j - (1 : Matrix (Fin n) (Fin n) E) i j) := by
        rw [hent, map_sub, Matrix.one_apply, apply_ite s, map_one, map_zero]
      rw [e1, galIsom k E]
      exact hy' i j
    · have hsd : GlobalTheory.Whittaker.superDiag (Matrix.GeneralLinearGroup.map (s : E →+* E) y) = s (GlobalTheory.Whittaker.superDiag y) := by
        set_option synthInstance.maxHeartbeats 100000 in
          simp only [GlobalTheory.Whittaker.superDiag, map_sum, hent]
      change ((ψ (GlobalTheory.Whittaker.superDiag (Matrix.GeneralLinearGroup.map (s : E →+* E) y)) : Circle) : ℂ) = _
      rw [hsd, hinv]

theorem UpperTheory.ConvolutionTheory.T.howeType :
    UpperTheory.ConvolutionTheory.T.HoweType := by
  intro F E _ _ _ _ _ _ _ _ σ hσ _ n _ μ _ V hV v w hw N hN
  obtain ⟨iA, iV, iFD, iG, s, -, -, -, hgal, -⟩ := UpperTheory.V.Z.Tf.Orb.placeData F E σ hσ v w hw
  haveI : CharZero (v.adicCompletion F) := algebraRat.charZero _
  obtain ⟨π, hπ, -⟩ : ∃! π : GlobalTheory.CuspRep.CuspSub E n,
      UpperTheory.ConvolutionTheory.Dp.Carries μ π V :=
    UpperTheory.ConvolutionTheory.Dp.exCusp E n μ V hV
  obtain ⟨hl, -, -, -⟩ := UpperTheory.V.Z.Tf.Orb.gLTop (w.1.adicCompletion E) n
  letI : MeasurableSpace (Gw n w.1) := borel _
  haveI : BorelSpace (Gw n w.1) := ⟨rfl⟩
  obtain ⟨⟨τ, hτ⟩, -, -⟩ := occursBasics E n μ V w.1 MeasureTheory.Measure.haar hV
  have hloc : (UpperTheory.CBC.Cusp.cx π).locComp w.1 τ :=
    (UpperTheory.ConvolutionTheory.Dp.locIff E n μ π V hπ w.1 τ).2 ((occursIff E n μ V hV w.1 τ).1 hτ)
  have hgen : GlobalTheory.LocGL.IsGeneric τ.ρ := GlobalTheory.CuspRep.Generic.isGeneric_of_isLocComp E n π w.1 τ hloc
  obtain ⟨J, χ, e, hCO, hchr, hJN, he0, heJ, hline, hst⟩ :=
    local_type (v.adicCompletion F) (w.1.adicCompletion E) s n τ.V τ.ρ τ.smooth τ.irred hgen N hN
  have hrank := lineRank E n μ V hV w.1 τ hτ J χ hCO hchr ⟨e, hline⟩
  obtain ⟨f, hf0, hfV, hfe⟩ := hτ
  have hinj : Function.Injective f := by
    let K : Subrepresentation τ.ρ := ⟨LinearMap.ker f, fun g x hx => by
      rw [LinearMap.mem_ker] at hx ⊢
      rw [hfe, hx, map_zero]⟩
    haveI := τ.irred
    rcases eq_bot_or_eq_top K with h | h
    · refine LinearMap.ker_eq_bot.1 ?_
      exact congrArg Subrepresentation.toSubmodule h
    · exfalso
      apply hf0
      have h' : LinearMap.ker f = ⊤ := congrArg Subrepresentation.toSubmodule h
      exact LinearMap.ker_eq_top.1 h'
  refine ⟨J, χ, hCO, hchr, hJN, hrank, fun h => ?_, fun x hx => ?_⟩
  · have hm : f e ∈ V ⊓ eigL μ w.1 J χ := by
      refine ⟨hfV e, ?_⟩
      simp only [eigL, SetLike.mem_coe, Submodule.mem_iInf]
      intro x hx
      change rhoL μ w.1 x (f e) = χ x • f e
      rw [← hfe, heJ x hx, map_smul]
    rw [h, Submodule.mem_bot] at hm
    exact he0 (hinj (by rw [hm, map_zero]))
  · have hcm : UpperTheory.ConvolutionTheory.GM.cmp w (PositivityTheory.Rg.Tf.Geo.mapGL n (PositivityTheory.Rg.Tf.Geo.galFin σ v) x) =
        Matrix.GeneralLinearGroup.map (s : w.1.adicCompletion E →+* w.1.adicCompletion E) (UpperTheory.ConvolutionTheory.GM.cmp w x) :=
      Units.ext (Matrix.ext fun i j => hgal _)
    rw [hcm]
    exact hst _ hx
end

-- bundled from Development.AutomorphicArithmetic.Foundations.Convolution.TraceSplitting.LevelEx
section
noncomputable section

open MeasureTheory NumberField IsDedekindDomain Filter
open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace GroundTheory.Automorphic.AutomorphicForm
open GroundTheory.Automorphic.CuspidalSpectrum GroundTheory.Global GroundTheory.Global.SemiLocal
open PositivityTheory.Rg.Tf.Core PositivityTheory.Rg.Tf.Geo UpperTheory.ConvolutionTheory.C UpperTheory.ConvolutionTheory.L1 Formalism.BasicNotions GlobalTheory.PRep GlobalTheory.CuspRep GlobalTheory.SmGL GlobalTheory.IndefiniteRowSideFullHecke.IwahoriDoubleCosets
open Formalism.L2.Host UpperTheory.V.Published UpperTheory.CBC
open scoped Classical

namespace UpperTheory.ConvolutionTheory.T

variable {K : Type} [Field K] [NumberField K] {n : ℕ}

private lemma mem_fixL_iff (μ : Measure (normOneGL (K := K) (n := n))) [μ.IsHaarMeasure] (w : Pl K) (J : Subgroup (Gw n w))
    (v : LL μ) : v ∈ fixL μ w J ↔ ∀ g ∈ J, rhoL μ w g v = v := by
  simp [fixL, fixF, rhoL, Submodule.mem_iInf, LinearMap.mem_eqLocus, Subgroup.mem_map]

private lemma co_integral (w : Pl K) : CO (GLnLocal.integralGL (w.adicCompletion K) n) :=
  ⟨GLnLocal.isCompact_integralGL _ n, GLnLocal.isOpen_integralGL _ n⟩

private lemma isChr_one {G : Type} [Group G] [TopologicalSpace G] (J : Subgroup G) : IsChr J (1 : G → ℂ) :=
  ⟨IsLocallyConstant.const (1 : ℂ), fun _ _ => by simp, fun _ _ _ _ => by simp⟩

private lemma exists_local_level (μ : Measure (normOneGL (K := K) (n := n))) [μ.IsHaarMeasure] (V : Submodule ℂ (LL μ))
    (hV : IsSummand μ V) (w : Pl K) :
    ∃ U : Subgroup (Gw n w), CO U ∧ U ≤ GLnLocal.integralGL (w.adicCompletion K) n ∧ V ⊓ fixL μ w U ≠ ⊥ := by
  letI : MeasurableSpace (Gw n w) := borel _
  haveI : BorelSpace (Gw n w) := ⟨rfl⟩
  let P : TopologicalSpace.PositiveCompacts (Gw n w) :=
    { carrier := GLnLocal.integralGL (w.adicCompletion K) n
      isCompact' := GLnLocal.isCompact_integralGL _ n
      interior_nonempty' := by
        rw [(GLnLocal.isOpen_integralGL _ n).interior_eq]
        exact ⟨1, Subgroup.one_mem _⟩ }
  obtain ⟨⟨σ, f, hf0, hfV, hfe⟩, -, -⟩ := occursBasics K n μ V w (Measure.haarMeasure P) hV
  obtain ⟨x, hx⟩ : ∃ x, f x ≠ 0 := by
    by_contra h
    push_neg at h
    exact hf0 (LinearMap.ext h)
  let U : Subgroup (Gw n w) := stabilizerOf σ.ρ x ⊓ GLnLocal.integralGL (w.adicCompletion K) n
  have hUo : IsOpen (U : Set (Gw n w)) := by
    rw [Subgroup.coe_inf]
    exact (σ.smooth x).inter (GLnLocal.isOpen_integralGL _ n)
  have hUc : IsCompact (U : Set (Gw n w)) :=
    (GLnLocal.isCompact_integralGL _ n).of_isClosed_subset (Subgroup.isClosed_of_isOpen U hUo)
      (by rw [Subgroup.coe_inf]; exact Set.inter_subset_right)
  refine ⟨U, ⟨hUc, hUo⟩, inf_le_right, fun hb => hx ?_⟩
  have hm : f x ∈ V ⊓ fixL μ w U := by
    refine Submodule.mem_inf.2 ⟨hfV x, (mem_fixL_iff μ w U _).2 fun g hg => ?_⟩
    rw [← hfe g x]
    exact congrArg f hg.1
  rw [hb] at hm
  exact (Submodule.mem_bot ℂ).1 hm

end UpperTheory.ConvolutionTheory.T

theorem UpperTheory.ConvolutionTheory.T.levelEx :
    UpperTheory.ConvolutionTheory.T.LevelEx := by
  intro K _ _ n μ _ V hV S hS
  choose U₀ hU₀ hU₀le hU₀ne using fun w : Pl K => exists_local_level μ V hV w
  let J : ∀ w : Pl K, Subgroup (Gw n w) := fun w =>
    if w ∈ S then U₀ w else GLnLocal.integralGL (w.adicCompletion K) n
  have hJin : ∀ w ∈ S, J w = U₀ w := fun w hw => if_pos hw
  have hJout : ∀ w, w ∉ S → J w = GLnLocal.integralGL (w.adicCompletion K) n := fun w hw => if_neg hw
  have hco : ∀ w, CO (J w) := fun w => by
    by_cases hw : w ∈ S
    · rw [hJin w hw]; exact hU₀ w
    · rw [hJout w hw]; exact co_integral w
  have hle : ∀ w, J w ≤ GLnLocal.integralGL (w.adicCompletion K) n := fun w => by
    by_cases hw : w ∈ S
    · rw [hJin w hw]; exact hU₀le w
    · rw [hJout w hw]
  have heig : ∀ w, eigL μ w (J w) 1 = fixL μ w (J w) := fun w =>
    (eigBasic K n μ w (J w) 1 (hco w) (isChr_one _)).2.1
  have hloc : ∀ w, V ⊓ eigL μ w (J w) 1 ≠ ⊥ := fun w => by
    rw [heig w]
    by_cases hw : w ∈ S
    · rw [hJin w hw]; exact hU₀ne w
    · rw [hJout w hw]; exact hS w hw
  have hall := typedEx K n μ V hV J (fun _ => 1) (fun w => ⟨hco w, isChr_one _⟩)
    ((S.finite_toSet.eventually_cofinite_notMem).mono fun w hw => ⟨hJout w hw, rfl⟩) hloc
  refine ⟨J, fun w => ⟨hco w, hle w⟩, fun hb => hall (eq_bot_iff.2 ?_)⟩
  rw [← hb]
  refine le_inf (le_inf inf_le_left ?_) ?_
  · refine inf_le_right.trans (le_iInf₂ fun w hw => (iInf_le _ w).trans ?_)
    rw [heig w, hJout w hw]
  · refine inf_le_right.trans (le_iInf₂ fun w _ => (iInf_le _ w).trans ?_)
    rw [heig w]
end
end

-- bundled from Development.AutomorphicArithmetic.Foundations.Convolution.TraceSplitting.MatchOne
section
theorem UpperTheory.ConvolutionTheory.T.matchOne :
    UpperTheory.ConvolutionTheory.T.MatchOne := by
  intro F E _ _ _ _ _ σ n v aE bE aF bF
  obtain ⟨⟨aE', bE', aF', bF', mE, mF, hE, hF, hE1, hF1⟩, h2⟩ := UpperTheory.ConvolutionTheory.GM.matchOne F E σ n v
  obtain rfl : aE = aE' := bE.measurable_eq.trans bE'.measurable_eq.symm
  obtain rfl : aF = aF' := bF.measurable_eq.trans bF'.measurable_eq.symm
  exact ⟨mE, mF, hE, hF, hE1, hF1, fun c φ f hM => @h2 _ bE' _ bF' mE mF hE hF hE1 hF1 c φ f hM⟩
end

