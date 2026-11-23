module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.IntegralCompression.LAbove
public import Development.AutomorphicArithmetic.Foundations.Convolution.IntegrableConvolution.Bundle0005
public import Development.AutomorphicArithmetic.Foundations.Convolution.IntegrableConvolution.PositionOf

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.IntegralCompression.ContinuousEntryCharacters.ContinuousEntCSymm
section
open MeasureTheory NumberField Filter Topology Matrix
open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace GroundTheory.Automorphic.AutomorphicForm
open GroundTheory.Automorphic.CuspidalSpectrum GroundTheory.Automorphic.ArchWhittakerC UpperTheory.ConvolutionTheory UpperTheory.ConvolutionTheory.C UpperTheory.ConvolutionTheory.L1 PositivityTheory.Rg.Tf.Core PositivityTheory.Rg.Tf.Adel
open UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial.E UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial.EA
open scoped ComplexConjugate Classical InnerProductSpace

noncomputable section

namespace UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial.EA

open mixedEmbedding

section mk

variable {K : Type} [Field K] [NumberField K] {ι : Type}

private def entM (c : mixedSpace K ≃+* (ι → ℂ)) (n : ℕ) :
    Matrix (Fin n) (Fin n) (mixedSpace K) ≃+* (ι → Matrix (Fin n) (Fin n) ℂ) where
  toFun X i := Matrix.of fun a b => c (X a b) i
  invFun Y := Matrix.of fun a b => c.symm fun i => Y i a b
  left_inv X := by
    ext1 a b
    exact c.symm_apply_apply (X a b)
  right_inv Y := by
    funext i
    ext a b
    simp
  map_mul' X Y := by
    funext i
    ext a b
    set_option synthInstance.maxHeartbeats 100000 in
      simp [Matrix.mul_apply, map_sum, Finset.sum_apply]
  map_add' X Y := by
    funext i
    ext a b
    simp

private def entC (c : mixedSpace K ≃+* (ι → ℂ)) (n : ℕ) : ArchMatrix K n ≃+* (ι → Matrix (Fin n) (Fin n) ℂ) := entM c n

private theorem continuous_entC {c : mixedSpace K ≃+* (ι → ℂ)} (hc : Continuous c) (n : ℕ) : Continuous (entC c n) := by
  refine continuous_pi fun i => ?_
  refine continuous_matrix fun a b => ?_
  have h : Continuous fun X : Matrix (Fin n) (Fin n) (mixedSpace K) => X a b := continuous_id.matrix_elem a b
  exact (continuous_apply i).comp (hc.comp h)

private theorem continuous_entC_symm {c : mixedSpace K ≃+* (ι → ℂ)} (hs : Continuous c.symm) (n : ℕ) :
    Continuous (entC c n).symm := by
  change Continuous fun Y : ι → Matrix (Fin n) (Fin n) ℂ =>
    (Matrix.of fun a b => c.symm fun i => Y i a b : Matrix (Fin n) (Fin n) (mixedSpace K))
  refine continuous_matrix fun a b => ?_
  exact hs.comp (continuous_pi fun i => ((continuous_apply i).matrix_elem a b))

private def psiC (c : mixedSpace K ≃+* (ι → ℂ)) (hc : Continuous c) (hs : Continuous c.symm) (n : ℕ) :
    archGroup K n ≃ₜ* (ι → GL (Fin n) ℂ) :=
  (ContinuousMulEquiv.trans
    { toMulEquiv := Subgroup.topEquiv
      continuous_toFun := continuous_subtype_val
      continuous_invFun := continuous_id.subtype_mk _ }
    (unitsCongr (entC c n).toMulEquiv (continuous_entC hc n) (continuous_entC_symm hs n))).trans
    ContinuousMulEquiv.piUnits

private theorem psiC_val (c : mixedSpace K ≃+* (ι → ℂ)) (hc : Continuous c) (hs : Continuous c.symm) (n : ℕ)
    (g : archGroup K n) (i : ι) :
    ((psiC c hc hs n g i : GL (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ) = entC c n ((g : (ArchMatrix K n)ˣ) : ArchMatrix K n) i := rfl

private theorem continuous_toUnits (n : ℕ) :
    Continuous fun u : unitaryGroup (Fin n) ℂ => (Unitary.toUnits u : GL (Fin n) ℂ) := by
  refine Units.continuous_iff.2 ⟨continuous_subtype_val, ?_⟩
  exact continuous_star.comp continuous_subtype_val

private def mkCo (c : mixedSpace K ≃+* (ι → ℂ)) (hc : Continuous c) (hs : Continuous c.symm)
    (hu : ∀ (n : ℕ) (g : archGroup K n), g ∈ archCompact K n ↔
      ∀ i, entC c n ((g : (ArchMatrix K n)ˣ) : ArchMatrix K n) i ∈ unitaryGroup (Fin n) ℂ) : Co K ι where
  c := c
  Ψ := psiC c hc hs
  Φ n :=
    { toFun := fun k i => ⟨_, (hu n k.1).1 k.2 i⟩
      invFun := fun u => ⟨(psiC c hc hs n).symm fun i => Unitary.toUnits (u i), (hu n _).2 fun i => by
        rw [← psiC_val c hc hs, ContinuousMulEquiv.apply_symm_apply]
        exact (u i).2⟩
      left_inv := fun k => by
        refine Subtype.ext ?_
        change (psiC c hc hs n).symm _ = k.1
        rw [ContinuousMulEquiv.symm_apply_eq]
        funext i
        exact Units.ext rfl
      right_inv := fun u => by
        funext i
        refine Subtype.ext ?_
        change ((psiC c hc hs n ((psiC c hc hs n).symm fun i => Unitary.toUnits (u i)) i : GL (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ) = _
        rw [ContinuousMulEquiv.apply_symm_apply]
        rfl
      map_mul' := fun k l => by
        funext i
        refine Subtype.ext ?_
        change ((psiC c hc hs n (k.1 * l.1) i : GL (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ) = _
        rw [map_mul]
        rfl
      continuous_toFun := by
        refine continuous_pi fun i => Continuous.subtype_mk ?_ _
        exact Units.continuous_val.comp ((continuous_apply i).comp
          ((psiC c hc hs n).continuous.comp continuous_subtype_val))
      continuous_invFun := by
        refine Continuous.subtype_mk ?_ _
        exact (psiC c hc hs n).symm.continuous.comp
          (continuous_pi fun i => (continuous_toUnits n).comp (continuous_apply i)) }
  Ψ_val n g i a b := rfl
  Φ_val n k i := rfl

end mk

section co

private def cF (F : Type) [Field F] [NumberField F] [_root_.NumberField.IsTotallyComplex F] : mixedSpace F ≃+* (InfinitePlace F → ℂ) where
  toFun a w := a.2 ⟨w, IsTotallyComplex.isComplex w⟩
  invFun z := (fun v => absurd v.2 (InfinitePlace.not_isReal_iff_isComplex.2 (IsTotallyComplex.isComplex v.1)), fun v => z v.1)
  left_inv a := Prod.ext (funext fun v => absurd v.2 (InfinitePlace.not_isReal_iff_isComplex.2 (IsTotallyComplex.isComplex v.1))) rfl
  right_inv z := rfl
  map_mul' _ _ := rfl
  map_add' _ _ := rfl

variable (F : Type) [Field F] [NumberField F] [_root_.NumberField.IsTotallyComplex F]

private theorem continuous_cF : Continuous (cF F) := by
  refine continuous_pi fun w => ?_
  exact continuous_complexComp ⟨w, IsTotallyComplex.isComplex w⟩

private theorem continuous_cF_symm : Continuous (cF F).symm := by
  refine Continuous.prodMk (continuous_pi fun v => ?_) (continuous_pi fun v => continuous_apply _)
  exact absurd v.2 (InfinitePlace.not_isReal_iff_isComplex.2 (IsTotallyComplex.isComplex v.1))

private theorem unitary_cF (n : ℕ) (g : archGroup F n) : g ∈ archCompact F n ↔
    ∀ w, entC (cF F) n ((g : (ArchMatrix F n)ˣ) : ArchMatrix F n) w ∈ unitaryGroup (Fin n) ℂ := by
  constructor
  · intro h w
    exact complexCompM_mem_unitaryGroup h ⟨w, IsTotallyComplex.isComplex w⟩
  · intro h
    exact mem_archCompact_of_unitary g
      (fun v => absurd v.2 (InfinitePlace.not_isReal_iff_isComplex.2 (IsTotallyComplex.isComplex v.1))) fun v => h v.1

private theorem continuous_psi (K : Type) [Field K] [NumberField K] :
    Continuous (InfiniteAdeleRing.ringEquiv_mixedSpace K) := by
  have e : ⇑(InfiniteAdeleRing.ringEquiv_mixedSpace K) = ⇑(GroundTheory.Global.homeomorphMixedSpace K) :=
    funext fun x => (GroundTheory.Global.homeomorphMixedSpace_apply K x).symm
  rw [e]
  exact (GroundTheory.Global.homeomorphMixedSpace K).continuous

private theorem continuous_psi_symm (K : Type) [Field K] [NumberField K] :
    Continuous (InfiniteAdeleRing.ringEquiv_mixedSpace K).symm := by
  have e : ⇑(InfiniteAdeleRing.ringEquiv_mixedSpace K).symm = ⇑(GroundTheory.Global.homeomorphMixedSpace K).symm := by
    funext x
    apply (InfiniteAdeleRing.ringEquiv_mixedSpace K).injective
    rw [RingEquiv.apply_symm_apply, ← GroundTheory.Global.homeomorphMixedSpace_apply, Homeomorph.apply_symm_apply]
  rw [e]
  exact (GroundTheory.Global.homeomorphMixedSpace K).symm.continuous

variable {F} {E : Type} [Field E] [NumberField E] [Algebra F E] {σ : E ≃ₐ[F] E}

private def unc (κ ι : Type) : (κ → ι → ℂ) ≃+* (κ × ι → ℂ) where
  toFun f p := f p.1 p.2
  invFun z s u := z (s, u)
  left_inv _ := rfl
  right_inv _ := rfl
  map_mul' _ _ := rfl
  map_add' _ _ := rfl

private def cE (D : InfD σ 1) : mixedSpace E ≃+* (Fin 2 × InfinitePlace F → ℂ) :=
  ((InfiniteAdeleRing.ringEquiv_mixedSpace E).symm.trans D.e).trans
    ((RingEquiv.piCongrRight fun _ : Fin (1 + 1) => (InfiniteAdeleRing.ringEquiv_mixedSpace F).trans (cF F)).trans
      (unc (Fin (1 + 1)) (InfinitePlace F)))

private theorem continuous_cE (D : InfD σ 1) : Continuous (cE D) := by
  refine continuous_pi fun p => ?_
  exact (continuous_apply p.2).comp ((continuous_cF F).comp ((continuous_psi F).comp
    ((continuous_apply p.1).comp (D.cont.comp (continuous_psi_symm E)))))

private theorem continuous_cE_symm (D : InfD σ 1) : Continuous (cE D).symm := by
  refine (continuous_psi E).comp (D.cont_symm.comp (continuous_pi fun s => ?_))
  exact (continuous_psi_symm F).comp ((continuous_cF_symm F).comp
    (continuous_pi fun u => continuous_apply (s, u)))

private theorem ent_comp (D : InfD σ 1) (n : ℕ) (g : archGroup E n) (s : Fin 2) (u : InfinitePlace F) :
    entC (cF F) n (((compA D n s g : archGroup F n) : (ArchMatrix F n)ˣ) : ArchMatrix F n) u =
      entC (cE D) n ((g : (ArchMatrix E n)ˣ) : ArchMatrix E n) (s, u) := rfl

private theorem unitary_cE (D : InfD σ 1) (n : ℕ) (g : archGroup E n) : g ∈ archCompact E n ↔
    ∀ p, entC (cE D) n ((g : (ArchMatrix E n)ˣ) : ArchMatrix E n) p ∈ unitaryGroup (Fin n) ℂ := by
  rw [(UpperTheory.ConvolutionTheory.L1.positionOf F E σ 1 D).2 n g]
  constructor
  · rintro h ⟨s, u⟩
    rw [← ent_comp]
    exact (unitary_cF F n _).1 (h s) u
  · intro h s
    refine (unitary_cF F n _).2 fun u => ?_
    rw [ent_comp D n g s u]
    exact h (s, u)

end co

end UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial.EA

theorem UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial.EA.coEx :
    ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] [_root_.NumberField.IsTotallyComplex F] [_root_.NumberField.IsTotallyComplex E] (σ : E ≃ₐ[F] E) (D : InfD σ 1), ∃ (CF : Co F (InfinitePlace F)) (CE : Co E (Fin 2 × InfinitePlace F)),
      ∀ n (g : archGroup E n) s u, CE.Ψ n g (s, u) = CF.Ψ n (compA D n s g) u := by
  intro F E _ _ _ _ _ _ _ σ D
  refine ⟨mkCo (cF F) (continuous_cF F) (continuous_cF_symm F) (unitary_cF F),
    mkCo (cE D) (continuous_cE D) (continuous_cE_symm D) (unitary_cE D), fun n g s u => ?_⟩
  exact Units.ext (ent_comp D n g s u).symm
end
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.IntegralCompression.ContinuousEntryCharacters.ExpMul
section
open MeasureTheory NumberField Filter Topology Matrix
open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace GroundTheory.Automorphic.AutomorphicForm
open GroundTheory.Automorphic.CuspidalSpectrum GroundTheory.Automorphic.ArchWhittakerC UpperTheory.ConvolutionTheory UpperTheory.ConvolutionTheory.C UpperTheory.ConvolutionTheory.L1 PositivityTheory.Rg.Tf.Core PositivityTheory.Rg.Tf.Adel
open UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial.E UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial.EA
open scoped ComplexConjugate Classical InnerProductSpace

private lemma chi_add (ν ν' : Fin (2 + 2) → ℤ) (θ : Fin (2 + 2) → ℝ) :
    chi (ν + ν') θ = chi ν θ * chi ν' θ := by
  unfold chi
  rw [← Complex.exp_add, ← mul_add, ← Finset.sum_add_distrib]
  congr 2
  refine Finset.sum_congr rfl fun i _ => ?_
  simp only [Pi.add_apply, Int.cast_add, add_mul]

private lemma weak (π : Equiv.Perm (Fin (2 + 2))) (ν μ : Fin (2 + 2) → ℤ)
    (h : ∀ (w : Equiv.Perm (Fin (2 + 2))) (y : Fin (2 + 2) → ℤ), Antitone (y ∘ π) →
      ∑ i, ν i * y (w i) ≤ ∑ i, μ i * y i) :
    ∑ i, ν (π i) * (-((i : ℕ) : ℤ)) ≤ ∑ i, μ (π i) * (-((i : ℕ) : ℤ)) := by
  have h1 := h 1 (fun i => -(((π.symm i : Fin (2 + 2)) : ℕ) : ℤ)) (by
    intro a b hab
    simp only [Function.comp_apply, Equiv.symm_apply_apply, neg_le_neg_iff, Nat.cast_le]
    exact hab)
  rw [← Equiv.sum_comp π, ← Equiv.sum_comp π (fun i => μ i * _)] at h1
  simpa only [Equiv.Perm.one_apply, Equiv.symm_apply_apply] using h1

theorem UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial.EA.expMul :
    ∀ π ψ ψ' μ μ', OExp π ψ μ → OExp π ψ' μ' → OExp π (fun k => ψ k * ψ' k) (μ + μ') := by
  rintro π ψ ψ' μ μ' ⟨J, _, j₀, a, b, ν, hc, he, ha, hb, hν, hw, hg, hg'⟩
    ⟨J', _, j₀', a', b', ν', hc', he', ha', hb', hν', hw', hf, hf'⟩
  refine ⟨J × J', inferInstance, (j₀, j₀'), fun j h => a j.1 h * a' j.2 h, fun j h => b j.1 h * b' j.2 h,
    fun j => ν j.1 + ν' j.2, fun j => ⟨(hc j.1).1.mul (hc' j.2).1, (hc j.1).2.mul (hc' j.2).2⟩,
    fun h k => ?_, ?_, ?_, ?_, fun j θ h => ?_, fun j w y hy => ?_, fun j hj => ?_⟩
  · simp only [he, he', Finset.sum_mul_sum, Fintype.sum_prod_type]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    ring
  · simp only [ha, ha']
  · simp only [hb, hb']
  · simp only [hν, hν']
  · obtain ⟨h1, h2, h3⟩ := hw j.1 θ h
    obtain ⟨h1', h2', h3'⟩ := hw' j.2 θ h
    simp only [h1, h2, h3, h1', h2', h3', chi_add]
    refine ⟨by ring, by ring, by ring⟩
  · simp only [Pi.add_apply, add_mul, Finset.sum_add_distrib]
    exact add_le_add (hg j.1 w y hy) (hf j.2 w y hy)
  · simp only [Pi.add_apply, add_mul, Finset.sum_add_distrib]
    by_cases h1 : j.1 = j₀
    · have h2 : j.2 ≠ j₀' := fun h2 => hj (Prod.ext h1 h2)
      exact add_lt_add_of_le_of_lt (weak π _ _ (hg j.1)) (hf' j.2 h2)
    · exact add_lt_add_of_lt_of_le (hg' j.1 h1) (weak π _ _ (hf j.2))
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.IntegralCompression.ContinuousEntryCharacters.ExpNorm
section
open MeasureTheory NumberField Filter Topology Matrix
open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace GroundTheory.Automorphic.AutomorphicForm
open GroundTheory.Automorphic.CuspidalSpectrum GroundTheory.Automorphic.ArchWhittakerC UpperTheory.ConvolutionTheory UpperTheory.ConvolutionTheory.C UpperTheory.ConvolutionTheory.L1 PositivityTheory.Rg.Tf.Core PositivityTheory.Rg.Tf.Adel
open UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial.E UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial.EA
open scoped ComplexConjugate Classical InnerProductSpace

private lemma sq_sum_le_of_dom (π : Equiv.Perm (Fin (2 + 2))) (μ ν : Fin (2 + 2) → ℤ)
    (h : ∀ (w : Equiv.Perm (Fin (2 + 2))) (y : Fin (2 + 2) → ℤ), Antitone (y ∘ π) →
      ∑ i, ν i * y (w i) ≤ ∑ i, μ i * y i) :
    ∑ i, ν i ^ 2 ≤ ∑ i, μ i ^ 2 := by
  have hm : Monotone ((fun i => -ν i) ∘ Tuple.sort (fun i => -ν i)) := Tuple.monotone_sort _
  obtain ⟨τ, hτ⟩ : ∃ τ : Equiv.Perm (Fin (2 + 2)), Monotone ((fun i => -ν i) ∘ τ) := ⟨_, hm⟩
  obtain ⟨s, hs⟩ : ∃ s : Equiv.Perm (Fin (2 + 2)), s = τ * π⁻¹ := ⟨_, rfl⟩
  have hanti : Antitone ((fun i => ν (s i)) ∘ π) := by
    intro a b hab
    have := hτ hab
    simp only [Function.comp, neg_le_neg_iff] at this
    simpa [hs, Equiv.Perm.mul_apply] using this
  have h1 := h s⁻¹ (fun i => ν (s i)) hanti
  have h2 : ∑ i, ν i * ν (s (s⁻¹ i)) = ∑ i, ν i ^ 2 := by
    refine Finset.sum_congr rfl fun i _ => ?_
    simp [sq]
  rw [h2] at h1
  have h3 : ∑ i, ν (s i) ^ 2 = ∑ i, ν i ^ 2 := Equiv.sum_comp s fun i => ν i ^ 2
  have h4 := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ μ fun i => ν (s i)
  rw [h3] at h4
  have hA : 0 ≤ ∑ i, ν i ^ 2 := Finset.sum_nonneg fun i _ => sq_nonneg _
  have hB : 0 ≤ ∑ i, μ i ^ 2 := Finset.sum_nonneg fun i _ => sq_nonneg _
  obtain ⟨A, hAe⟩ : ∃ A, A = ∑ i, ν i ^ 2 := ⟨_, rfl⟩
  obtain ⟨B, hBe⟩ : ∃ B, B = ∑ i, μ i ^ 2 := ⟨_, rfl⟩
  obtain ⟨C, hCe⟩ : ∃ C, C = ∑ i, μ i * ν (s i) := ⟨_, rfl⟩
  rw [← hAe, ← hCe] at h1
  rw [← hAe, ← hBe, ← hCe] at h4
  rw [← hAe] at hA
  rw [← hBe] at hB
  rw [← hAe, ← hBe]
  rcases hA.eq_or_lt with h0 | h0
  · rw [← h0]; exact hB
  · have h5 : A * A ≤ B * A := by nlinarith
    exact le_of_mul_le_mul_right h5 h0

theorem UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial.EA.expNorm :
    ∀ π ψ μ, OExp π ψ μ → WExp ψ μ := by
  intro π ψ μ h
  obtain ⟨J, hJ, j₀, a, b, ν, hc, he, ha, hb, hν, hw, hg, hg'⟩ := h
  refine ⟨J, hJ, j₀, a, b, ν, hc, he, ha, hb, hν, hw, fun j => sq_sum_le_of_dom π μ (ν j) (hg j), ?_⟩
  intro j hj hEq
  have := hg' j hj
  rw [hEq] at this
  exact lt_irrefl _ this
end

