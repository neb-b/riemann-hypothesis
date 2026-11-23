module

public import Mathlib
public import Development.AutomorphicArithmetic.Foundations.Convolution.IntegrableConvolution.Bundle0004
public import Development.AutomorphicArithmetic.Foundations.Convolution.IntegrableConvolution.Bundle0005
public import Development.AutomorphicArithmetic.Foundations.Convolution.IntegrableConvolution.Bundle0006
public import Development.AutomorphicArithmetic.Foundations.Convolution.IntegrableConvolution.Bundle0007
public import Development.AutomorphicArithmetic.Foundations.Convolution.ConvolutionKernels.KernelTransforms.Bundle0003
public import Development.AutomorphicArithmetic.Foundations.Convolution.IntegrableConvolution.Bundle0001
public import Development.AutomorphicArithmetic.Foundations.Convolution.IntegrableConvolution.PushTens
public import Development.AutomorphicArithmetic.Foundations.Convolution.IntegrableConvolution.Bundle0003
public import Development.AutomorphicArithmetic.Foundations.Convolution.IntegrableConvolution.DiagOnly
public import Development.AutomorphicArithmetic.Foundations.Convolution.IntegrableConvolution.JointTrace

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.Foundations.Convolution.IntegrableConvolution.LactGen
section
noncomputable section

open MeasureTheory NumberField IsDedekindDomain
open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace
open GroundTheory.Automorphic.AutomorphicForm GroundTheory.Automorphic.CuspidalSpectrum UpperTheory.ConvolutionTheory UpperTheory.ConvolutionTheory.C
open scoped TensorProduct

namespace UpperTheory.ConvolutionTheory.L1

section
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  {σ : E ≃ₐ[F] E} {m : ℕ}

private def compR (D : InfD σ m) (i : Fin (m + 1)) :
    mixedEmbedding.mixedSpace E →+* mixedEmbedding.mixedSpace F :=
  (InfiniteAdeleRing.ringEquiv_mixedSpace F).toRingHom.comp
    ((Pi.evalRingHom (fun _ : Fin (m + 1) => InfiniteAdeleRing F) i).comp
      (D.e.toRingHom.comp (InfiniteAdeleRing.ringEquiv_mixedSpace E).symm.toRingHom))

private theorem continuous_compR (D : InfD σ m) (i : Fin (m + 1)) : Continuous (compR D i) := by
  have he : ⇑(GroundTheory.Global.homeomorphMixedSpace E).symm =
      ⇑(InfiniteAdeleRing.ringEquiv_mixedSpace E).symm := by
    funext x
    apply (InfiniteAdeleRing.ringEquiv_mixedSpace E).injective
    rw [RingEquiv.apply_symm_apply, ← GroundTheory.Global.homeomorphMixedSpace_apply,
      Homeomorph.apply_symm_apply]
  have h1 : Continuous (InfiniteAdeleRing.ringEquiv_mixedSpace E).symm := by
    rw [← he]; exact (GroundTheory.Global.homeomorphMixedSpace E).symm.continuous
  have h2 : Continuous (InfiniteAdeleRing.ringEquiv_mixedSpace F) := by
    have : ⇑(InfiniteAdeleRing.ringEquiv_mixedSpace F) = ⇑(GroundTheory.Global.homeomorphMixedSpace F) := by
      funext x; rw [GroundTheory.Global.homeomorphMixedSpace_apply]
    rw [this]; exact (GroundTheory.Global.homeomorphMixedSpace F).continuous
  exact h2.comp ((continuous_apply i).comp (D.cont.comp h1))

private def compM (D : InfD σ m) (n : ℕ) (i : Fin (m + 1)) : ArchMatrix E n →+* ArchMatrix F n :=
  RingHom.mapMatrix (m := Fin n) (compR D i)

private theorem continuous_compM (D : InfD σ m) (n : ℕ) (i : Fin (m + 1)) : Continuous (compM D n i) := by
  change Continuous fun M : Matrix (Fin n) (Fin n) (mixedEmbedding.mixedSpace E) => M.map (compR D i)
  exact continuous_id.matrix_map (continuous_compR D i)

private theorem coe_compA (D : InfD σ m) (n : ℕ) (i : Fin (m + 1)) (g : archGroup E n) :
    (((compA D n i g : archGroup F n) : (ArchMatrix F n)ˣ) : ArchMatrix F n) =
      compM D n i (((g : (ArchMatrix E n)ˣ) : ArchMatrix E n)) := by
  rfl

private theorem compA_expG (D : InfD σ m) (n : ℕ) (i : Fin (m + 1)) (Y : archLie E n) (Y' : archLie F n)
    (h : compM D n i (Y : ArchMatrix E n) = Y') :
    compA D n i ((isExpLieAlgebra E n).expG Y) = (isExpLieAlgebra F n).expG Y' := by
  apply Subtype.ext
  apply Units.ext
  rw [coe_compA, IsExpLieAlgebra.coe_expG, IsExpLieAlgebra.coe_expG, ← h]
  exact NormedSpace.map_exp_of_mem_ball (𝕂 := ℝ) (compM D n i) (continuous_compM D n i) _
    ((NormedSpace.expSeries_radius_eq_top ℝ (ArchMatrix E n)).symm ▸ edist_lt_top _ _)

private theorem compR_along (D : InfD σ m) {τ : E →+* ℂ} {k : Fin (m + 1)} (h : InSlot D τ k) (z : ℂ)
    (i : Fin (m + 1)) :
    compR D i (along τ z) = if i = k then along (τ.comp (algebraMap F E)) z else 0 := by
  have e : D.e ((InfiniteAdeleRing.ringEquiv_mixedSpace E).symm (along τ z)) =
      Pi.single k ((InfiniteAdeleRing.ringEquiv_mixedSpace F).symm (along (τ.comp (algebraMap F E)) z)) := by
    rw [h z, RingEquiv.apply_symm_apply]
  change InfiniteAdeleRing.ringEquiv_mixedSpace F
    (D.e ((InfiniteAdeleRing.ringEquiv_mixedSpace E).symm (along τ z)) i) = _
  rw [e]
  by_cases hik : i = k
  · subst hik
    rw [Pi.single_eq_same, RingEquiv.apply_symm_apply, if_pos rfl]
  · rw [Pi.single_eq_of_ne hik, map_zero, if_neg hik]

private def xL {K : Type} [Field K] [NumberField K] (n : ℕ) (τ : K →+* ℂ) (p q : Fin n) (z : ℂ) : archLie K n :=
  ⟨(Matrix.single p q (along τ z) : Matrix (Fin n) (Fin n) (mixedEmbedding.mixedSpace K)), Submodule.mem_top⟩

private theorem compM_xL (D : InfD σ m) (n : ℕ) {τ : E →+* ℂ} {k : Fin (m + 1)} (h : InSlot D τ k)
    (p q : Fin n) (z : ℂ) (i : Fin (m + 1)) :
    compM D n i (xL n τ p q z : ArchMatrix E n) =
      if i = k then (xL n (τ.comp (algebraMap F E)) p q z : ArchMatrix F n) else 0 := by
  change (Matrix.single p q (along τ z) : Matrix (Fin n) (Fin n) (mixedEmbedding.mixedSpace E)).map (compR D i) = _
  by_cases hik : i = k
  · rw [if_pos hik]
    ext1 a b
    change _ = (Matrix.single p q (along (τ.comp (algebraMap F E)) z) : Matrix (Fin n) (Fin n) (mixedEmbedding.mixedSpace F)) a b
    simp only [Matrix.map_apply, Matrix.single_apply]
    split_ifs
    · rw [compR_along D h, if_pos hik]
    · simp
  · rw [if_neg hik]
    ext1 a b
    change _ = (0 : Matrix (Fin n) (Fin n) (mixedEmbedding.mixedSpace F)) a b
    simp only [Matrix.map_apply, Matrix.single_apply, Matrix.zero_apply]
    split_ifs
    · rw [compR_along D h, if_neg hik]
    · simp

private theorem compA_exp_self (D : InfD σ m) (n : ℕ) {τ : E →+* ℂ} {k : Fin (m + 1)} (h : InSlot D τ k)
    (p q : Fin n) (z : ℂ) (t : ℝ) :
    compA D n k ((isExpLieAlgebra E n).expG (t • xL n τ p q z)) =
      (isExpLieAlgebra F n).expG (t • xL n (τ.comp (algebraMap F E)) p q z) := by
  apply compA_expG
  change compM D n k (t • (xL n τ p q z : ArchMatrix E n)) = t • (xL n (τ.comp (algebraMap F E)) p q z : ArchMatrix F n)
  rw [map_real_smul (compM D n k) (continuous_compM D n k), compM_xL D n h, if_pos rfl]

private theorem compA_exp_ne (D : InfD σ m) (n : ℕ) {τ : E →+* ℂ} {k i : Fin (m + 1)} (h : InSlot D τ k)
    (hi : i ≠ k) (p q : Fin n) (z : ℂ) (t : ℝ) :
    compA D n i ((isExpLieAlgebra E n).expG (t • xL n τ p q z)) = 1 := by
  rw [compA_expG D n i _ 0, IsExpLieAlgebra.expG_zero]
  change compM D n i (t • (xL n τ p q z : ArchMatrix E n)) = 0
  rw [map_real_smul (compM D n i) (continuous_compM D n i), compM_xL D n h, if_neg hi, smul_zero]

private theorem lact_elem {K : Type} [Field K] [NumberField K] {n : ℕ} (β : TI K n) (hβ : SmoothT β)
    (τ : K →+* ℂ) (p q : Fin n) (z : ℂ) (x : archGroup K n) :
    HasDerivAt (fun t : ℝ => β (x * (isExpLieAlgebra K n).expG (t • xL n τ p q z))⁻¹)
      (lact ((1 : ℂ) ⊗ₜ elem τ p q z) β x⁻¹) 0 := by
  obtain ⟨h, -, -, -, -, -, -, e⟩ := UpperTheory.ConvolutionTheory.Tf.lactSpec K n β hβ
  rw [e, inv_inv, elem, IsExpLieAlgebra.rightUAction_ι]
  exact (isExpLieAlgebra K n).hasDerivAt_rightDeriv
    (f := fun g => β g⁻¹) h (xL n τ p q z) x

private theorem leftAction_tensor_generator (D : InfD σ m) [_root_.NumberField.IsTotallyComplex F] (n : ℕ) (τ : E →+* ℂ) (k : Fin (m + 1)) (hk : InSlot D τ k)
    (φ : Fin (m + 1) → TI F n) (β : TI E n) (hφ : ∀ i, SmoothT (φ i)) (hβ : IsTens D φ β) (p q : Fin n) (z : ℂ) :
    IsTens D (Function.update φ k (lact ((1 : ℂ) ⊗ₜ elem (τ.comp (algebraMap F E)) p q z) (φ k)))
      (lact ((1 : ℂ) ⊗ₜ elem τ p q z) β) := by
  have hsm : SmoothT β := (UpperTheory.ConvolutionTheory.L1.tensSmooth F E σ m D n φ β hβ).1 hφ
  intro g
  set x := g⁻¹ with hx
  have hg : g = x⁻¹ := by rw [hx, inv_inv]
  set τ' := τ.comp (algebraMap F E)
  set C : ℂ := ∏ i ∈ Finset.univ.erase k, φ i (compA D n i g) with hC
  have h1 := lact_elem β hsm τ p q z x
  have h2 := lact_elem (φ k) (hφ k) τ' p q z (compA D n k x)
  have e : (fun t : ℝ => β (x * (isExpLieAlgebra E n).expG (t • xL n τ p q z))⁻¹) =
      fun t : ℝ => φ k (compA D n k x * (isExpLieAlgebra F n).expG (t • xL n τ' p q z))⁻¹ * C := by
    funext t
    rw [hβ, ← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ k), map_inv (compA D n k), map_mul (compA D n k),
      compA_exp_self D n hk]
    congr 1
    refine Finset.prod_congr rfl fun i hi => ?_
    rw [map_inv (compA D n i), map_mul (compA D n i), compA_exp_ne D n hk (Finset.ne_of_mem_erase hi), mul_one, hx,
      map_inv (compA D n i), inv_inv]
  rw [e] at h1
  have h3 := h1.unique (h2.mul_const C)
  have hxk : (compA D n k x)⁻¹ = compA D n k g := by rw [hx, map_inv (compA D n k), inv_inv]
  rw [hxk, ← hg] at h3
  rw [h3, ← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ k), Function.update_self]
  congr 1
  rw [hC]
  exact Finset.prod_congr rfl fun i hi => by rw [Function.update_of_ne (Finset.ne_of_mem_erase hi)]

end

end UpperTheory.ConvolutionTheory.L1

theorem UpperTheory.ConvolutionTheory.L1.lactGen :
    UpperTheory.ConvolutionTheory.L1.LactGen := by
  intro F E _ _ _ _ _ _ σ m D n τ k hk φ β hφ hβ p q z
  exact UpperTheory.ConvolutionTheory.L1.leftAction_tensor_generator D n τ k hk φ β hφ hβ p q z
end
end

-- bundled from Development.AutomorphicArithmetic.Foundations.Convolution.IntegrableConvolution.MatchFin
section
open MeasureTheory NumberField IsDedekindDomain
open GroundTheory.Global.SemiLocal PositivityTheory.Rg.Tf.Geo

theorem UpperTheory.ConvolutionTheory.L1.matchFin :
    UpperTheory.ConvolutionTheory.L1.MatchFin := by
  intro F E _ _ _ _ _ σ m v D n _ _ _ _ μE μF hE hF
  have hreg : UpperTheory.ConvolutionTheory.L1.RegOk (v.adicCompletion F) n := UpperTheory.ConvolutionTheory.L1.regOkPi.1 _ n
  obtain ⟨c, hc, hμ, hφ⟩ := UpperTheory.ConvolutionTheory.L1.matchSplit (v.adicCompletion F) (CompletionsOver E v)
    (incFin E v) (galFin σ v) m D n μE μF hE hF hreg
  refine ⟨c, hc, hμ, fun φ h1 h2 => (hφ φ h1 h2).2.2, fun φ h => ?_⟩
  obtain ⟨hcomp, hglue, -, hgc, hcc, -⟩ :=
    UpperTheory.ConvolutionTheory.L1.glueBasic (v.adicCompletion F) (CompletionsOver E v) (incFin E v) (galFin σ v) m D n
  let e : (Fin (m + 1) → GL (Fin n) (v.adicCompletion F)) ≃ₜ GL (Fin n) (CompletionsOver E v) :=
    { toFun := D.glue n
      invFun := fun x i => D.comp n i x
      left_inv := fun g => funext fun i => hcomp g i
      right_inv := hglue
      continuous_toFun := hgc
      continuous_invFun := continuous_pi hcc }
  have hΨc : Continuous fun g : Fin (m + 1) → GL (Fin n) (v.adicCompletion F) => ∏ i, φ i (g i) :=
    continuous_finsetProd _ fun i _ => (h i).1.comp (continuous_apply i)
  have hΨs : HasCompactSupport fun g : Fin (m + 1) → GL (Fin n) (v.adicCompletion F) => ∏ i, φ i (g i) := by
    refine HasCompactSupport.intro' (K := Set.pi Set.univ fun i => tsupport (φ i))
      (isCompact_univ_pi fun i => (h i).2) (isClosed_set_pi fun i _ => isClosed_tsupport _) ?_
    intro g hg
    obtain ⟨i, -, hi⟩ : ∃ i, i ∈ Set.univ ∧ g i ∉ tsupport (φ i) := by
      simpa [Set.mem_pi] using hg
    exact Finset.prod_eq_zero (Finset.mem_univ i) (image_eq_zero_of_notMem_tsupport hi)
  have htens : D.tens n φ = (fun g : Fin (m + 1) → GL (Fin n) (v.adicCompletion F) => ∏ i, φ i (g i)) ∘ e.symm :=
    rfl
  refine ⟨?_, ?_, ?_⟩
  · rw [htens]
    exact hΨc.comp e.symm.continuous
  · rw [htens]
    exact hΨs.comp_isClosedEmbedding e.symm.isClosedEmbedding
  · have hpush := UpperTheory.ConvolutionTheory.L1.pushTens (GL (Fin n) (v.adicCompletion F)) μF m φ
      (fun i => (h i).1) (fun i => (h i).2)
    rw [← hpush]
    unfold UpperTheory.ConvolutionTheory.L1.Split.transfer
    congr 1
    funext g
    rw [htens]
    change (∏ i, φ i ((e.symm (e g)) i)) = _
    rw [e.symm_apply_apply]
end

-- bundled from Development.AutomorphicArithmetic.Foundations.Convolution.IntegrableConvolution.MatchInf
section
open MeasureTheory NumberField

private theorem UpperTheory.ConvolutionTheory.L1.matchInf_tens (R S : Type) [CommRing R] [CommRing S] [TopologicalSpace R]
    [TopologicalSpace S] [IsTopologicalRing R] [IsTopologicalRing S] [LocallyCompactSpace R] [T2Space R]
    [SecondCountableTopology R] [T2Space S] (ι : R →+* S) (s : S →+* S) (m : ℕ) (D : UpperTheory.ConvolutionTheory.L1.Split ι s m) (n : ℕ)
    [MeasurableSpace (GL (Fin n) R)] [BorelSpace (GL (Fin n) R)] (μ : Measure (GL (Fin n) R)) [μ.IsHaarMeasure]
    (φ : Fin (m + 1) → GL (Fin n) R → ℂ) (hφ : ∀ i, Continuous (φ i) ∧ HasCompactSupport (φ i)) :
    Continuous (D.tens n φ) ∧ HasCompactSupport (D.tens n φ) ∧
      D.transfer n μ (D.tens n φ) = UpperTheory.ConvolutionTheory.L1.cvAll μ m φ := by
  obtain ⟨h1, h2, -, h4, h5, -⟩ := UpperTheory.ConvolutionTheory.L1.glueBasic R S ι s m D n
  haveI : LocallyCompactSpace (Matrix (Fin n) (Fin n) R) :=
    inferInstanceAs (LocallyCompactSpace (Fin n → Fin n → R))
  haveI : SecondCountableTopology (Matrix (Fin n) (Fin n) R) :=
    inferInstanceAs (SecondCountableTopology (Fin n → Fin n → R))
  haveI : LocallyCompactSpace (Matrix (Fin n) (Fin n) R)ᵐᵒᵖ :=
    MulOpposite.opHomeomorph.symm.isClosedEmbedding.locallyCompactSpace
  haveI : SecondCountableTopology (Matrix (Fin n) (Fin n) R)ᵐᵒᵖ :=
    MulOpposite.opHomeomorph.symm.isEmbedding.secondCountableTopology
  haveI : LocallyCompactSpace (GL (Fin n) R) :=
    (Units.isClosedEmbedding_embedProduct (α := Matrix (Fin n) (Fin n) R)).locallyCompactSpace
  haveI : SecondCountableTopology (GL (Fin n) R) :=
    (Units.isEmbedding_embedProduct (M := Matrix (Fin n) (Fin n) R)).secondCountableTopology
  refine ⟨?_, ?_, ?_⟩
  · exact continuous_finsetProd _ fun i _ => (hφ i).1.comp (h5 i)
  · have hK : IsCompact (D.glue n '' Set.pi Set.univ fun i => tsupport (φ i)) :=
      (isCompact_univ_pi fun i => (hφ i).2.isCompact).image h4
    refine HasCompactSupport.intro hK fun x hx => ?_
    by_contra hne
    apply hx
    refine ⟨fun i => D.comp n i x, fun i _ => subset_tsupport _ ?_, h2 x⟩
    intro h0
    exact hne (Finset.prod_eq_zero (Finset.mem_univ i) h0)
  · rw [← UpperTheory.ConvolutionTheory.L1.pushTens (GL (Fin n) R) μ m φ (fun i => (hφ i).1) (fun i => (hφ i).2)]
    unfold UpperTheory.ConvolutionTheory.L1.Split.transfer UpperTheory.ConvolutionTheory.L1.Split.tens
    simp only [h1]

private theorem UpperTheory.ConvolutionTheory.L1.t2Space_infiniteAdeleRing' (F : Type) [Field F] [NumberField F] : T2Space (InfiniteAdeleRing F) :=
  inferInstanceAs (T2Space ((v : InfinitePlace F) → v.Completion))

private theorem UpperTheory.ConvolutionTheory.L1.matchInf_sc (F : Type) [Field F] [NumberField F] :
    SecondCountableTopology (InfiniteAdeleRing F) := by
  haveI : ∀ v : InfinitePlace F, SecondCountableTopology v.Completion := fun v =>
    (InfinitePlace.Completion.isometry_extensionEmbedding v).isEmbedding.secondCountableTopology
  exact inferInstanceAs (SecondCountableTopology ((v : InfinitePlace F) → v.Completion))

theorem UpperTheory.ConvolutionTheory.L1.matchInf :
    UpperTheory.ConvolutionTheory.L1.MatchInf := by
  intro F E _ _ _ _ _ σ m D n _ _ _ _ μE μF hE hF
  haveI := UpperTheory.ConvolutionTheory.L1.t2Space_infiniteAdeleRing' F
  haveI := UpperTheory.ConvolutionTheory.L1.t2Space_infiniteAdeleRing' E
  haveI := UpperTheory.ConvolutionTheory.L1.matchInf_sc F
  obtain ⟨c, hc, hμ, hM⟩ := UpperTheory.ConvolutionTheory.L1.matchSplit _ _ _ _ m D n μE μF hE hF (UpperTheory.ConvolutionTheory.L1.regOkPi.2.2 F n)
  exact ⟨c, hc, hμ, fun φ h1 h2 => (hM φ h1 h2).2.2,
    fun φ hφ => UpperTheory.ConvolutionTheory.L1.matchInf_tens _ _ _ _ m D n μF φ hφ⟩
end

-- bundled from Development.AutomorphicArithmetic.Foundations.Convolution.IntegrableConvolution.TwTrace
section
open GroundTheory.Automorphic UpperTheory.ConvolutionTheory.C
open scoped InnerProductSpace

private theorem trace_starProjection {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (K : Submodule ℂ H) [K.HasOrthogonalProjection] [FiniteDimensional ℂ K] :
    trace K.starProjection = (Module.finrank ℂ K : ℂ) := by
  classical
  let e := stdOrthonormalBasis ℂ K
  have hP : ∀ x : H, K.starProjection x = ∑ j, ⟪(e j : H), x⟫_ℂ • (e j : H) := by
    intro x
    have h := congrArg (fun v : K => (v : H)) (e.sum_repr' ⟨K.starProjection x, K.starProjection_apply_mem x⟩)
    simp only [Submodule.coe_sum, Submodule.coe_smul, Submodule.coe_inner] at h
    rw [← h]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [← Submodule.inner_starProjection_left_eq_right, Submodule.starProjection_eq_self_iff.2 (e j).2]
  have h1 : ∀ j, ⟪(e j : H), (e j : H)⟫_ℂ = 1 := by
    intro j
    rw [← Submodule.coe_inner, inner_self_eq_norm_sq_to_K, e.orthonormal.1 j]
    simp
  have hs := hasSum_sum (s := Finset.univ)
    (fun j _ => (stdHilbertBasis ℂ H).hasSum_inner_mul_inner (e j : H) (e j : H))
  simp only [h1, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one] at hs
  rw [← hs.tsum_eq, trace]
  refine tsum_congr fun i => ?_
  rw [hP, inner_sum]
  simp only [inner_smul_right]

private theorem trOn_one {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (W : Submodule ℂ H) [FiniteDimensional ℂ W] :
    trOn W 1 = (Module.finrank ℂ W : ℂ) := by
  have hc : W.topologicalClosure = W := W.closed_of_finiteDimensional.submodule_topologicalClosure_eq
  haveI : FiniteDimensional ℂ W.topologicalClosure := by rw [hc]; infer_instance
  have hp : prj W ∘L (1 : H →L[ℂ] H) ∘L prj W = W.topologicalClosure.starProjection := by
    ext x
    simp only [prj, ContinuousLinearMap.comp_apply, ContinuousLinearMap.one_apply]
    exact Submodule.starProjection_eq_self_iff.2 (Submodule.starProjection_apply_mem _ x)
  rw [trOn, hp, trace_starProjection, hc]

theorem UpperTheory.ConvolutionTheory.L1.twTrace :
    UpperTheory.ConvolutionTheory.L1.TwTrace := by
  intro Γ G H _ _ _ _ _ _ π V m ι E A U hS y hy hfin
  obtain ⟨hle, hdiag⟩ := UpperTheory.ConvolutionTheory.L1.diagOnly Γ G H π V m ι E A U hS y hy hfin
  haveI hfin' : FiniteDimensional ℂ (UpperTheory.ConvolutionTheory.L1.jointEig V E A y) := Submodule.finiteDimensional_of_le hle
  obtain ⟨c, hc, htr⟩ := UpperTheory.ConvolutionTheory.L1.jointTrace Γ G H π V m ι E A U hS y hfin'
  refine ⟨c, hc, ?_, fun i₀ S h1 h2 => (hdiag i₀ S h1).trans (htr i₀ S h1 h2)⟩
  have h := (hdiag 0 1 fun _ _ _ => rfl).trans (htr 0 1 (fun _ _ _ => rfl) fun _ _ _ _ => rfl)
  rw [trOn_one] at h
  exact h
end

