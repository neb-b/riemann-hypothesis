module

public import CompanionTheory.SpectralGeometry.CountingDefinitions.AdelicEulerProducts.CountData
public import Mathlib

@[expose] public section

-- bundled from CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.LatticeFundamentalDomainVolume
section
open NumberField IsDedekindDomain MeasureTheory Matrix Topology GlobalTheory.CompanionTheory.SW.Core
open scoped ENNReal NNReal MatrixGroups

noncomputable section

namespace GlobalTheory.CompanionTheory.SW.FD

open scoped Pointwise

variable {F : Type} [Field F] [NumberField F]

def scaleMap (ρ : InfinitePlace F → (F →+* ℝ)) (N : ℕ) : 𝓞 F →+ (InfinitePlace F → ℝ) where
  toFun r := fun w => ρ w ((N : F) * (r : F))
  map_zero' := by ext w; simp
  map_add' a b := by ext w; simp [mul_add]

theorem latR_eq_range (ρ : InfinitePlace F → (F →+* ℝ)) (N : ℕ) :
    latR ρ N = (scaleMap ρ N).range := by
  have h : {y | ∃ r : 𝓞 F, y = fun w => ρ w ((N : F) * (r : F))}
      = ((scaleMap ρ N).range : Set (InfinitePlace F → ℝ)) := by
    ext y
    constructor
    · rintro ⟨r, rfl⟩
      exact ⟨r, rfl⟩
    · rintro ⟨r, rfl⟩
      exact ⟨r, rfl⟩
  rw [latR, h, AddSubgroup.closure_eq]

theorem mem_latR_iff (ρ : InfinitePlace F → (F →+* ℝ)) (N : ℕ) (y : InfinitePlace F → ℝ) :
    y ∈ latR ρ N ↔ ∃ r : 𝓞 F, y = fun w => ρ w ((N : F) * (r : F)) := by
  rw [latR_eq_range]
  constructor
  · rintro ⟨r, rfl⟩
    exact ⟨r, rfl⟩
  · rintro ⟨r, rfl⟩
    exact ⟨r, rfl⟩

theorem embedding_bijective (hF : IsTotallyReal F) :
    Function.Bijective (fun w : InfinitePlace F => (w.embedding : F →+* ℂ)) := by
  constructor
  · intro w w' h
    have := congrArg InfinitePlace.mk h
    simpa using this
  · intro φ
    have hr : ComplexEmbedding.IsReal φ :=
      InfinitePlace.isReal_mk_iff.1 (hF.isReal (InfinitePlace.mk φ))
    exact ⟨InfinitePlace.mk φ, InfinitePlace.embedding_mk_eq_of_isReal hr⟩

def placeEquiv (hF : IsTotallyReal F) : InfinitePlace F ≃ (F →ₐ[ℚ] ℂ) :=
  (Equiv.ofBijective _ (embedding_bijective hF)).trans (RingHom.equivRatAlgHom F ℂ)

theorem card_places (hF : IsTotallyReal F) :
    Fintype.card (InfinitePlace F) = Module.finrank ℚ F := by
  rw [Fintype.card_congr (placeEquiv hF), AlgHom.card]

theorem exists_integral_basis [DecidableEq (InfinitePlace F)] (hF : IsTotallyReal F) (ρ : InfinitePlace F → (F →+* ℝ))
    (hρ : ∀ w x, ((ρ w x : ℝ) : ℂ) = w.embedding x) :
    ∃ B : Module.Basis (InfinitePlace F) ℤ (𝓞 F),
      (Matrix.det (Matrix.of fun i w => ρ w ((B i : 𝓞 F) : F))) ^ 2 = (discr F : ℝ) := by
  classical
  have hc : Fintype.card (Module.Free.ChooseBasisIndex ℤ (𝓞 F)) = Fintype.card (InfinitePlace F) := by
    rw [card_places hF, ← Module.finrank_eq_card_chooseBasisIndex, RingOfIntegers.rank]
  let e0 := Fintype.equivOfCardEq hc
  let bq := (integralBasis F).reindex e0
  refine ⟨(RingOfIntegers.basis F).reindex e0, ?_⟩
  have h := Algebra.discr_eq_det_embeddingsMatrixReindex_pow_two ℚ ℂ bq (placeEquiv hF)
  have hd : Algebra.discr ℚ bq = (discr F : ℚ) := by
    rw [coe_discr]
    have h0 := Algebra.discr_reindex ℚ (integralBasis F) e0
    rwa [← Module.Basis.coe_reindex] at h0
  have hM : Algebra.embeddingsMatrixReindex ℚ ℂ bq (placeEquiv hF) =
      (Matrix.of fun i w => ρ w (((RingOfIntegers.basis F).reindex e0 i : 𝓞 F) : F)).map
        Complex.ofRealHom := by
    ext i w
    simp [Algebra.embeddingsMatrixReindex, Algebra.embeddingsMatrix, placeEquiv, bq, hρ,
      integralBasis_apply, Module.Basis.reindex_apply]
  rw [hM, hd, ← RingHom.mapMatrix_apply, ← RingHom.map_det] at h
  have h2 : (((discr F : ℝ)) : ℂ) = (((Matrix.det (Matrix.of fun i w =>
      ρ w (((RingOfIntegers.basis F).reindex e0 i : 𝓞 F) : F))) ^ 2 : ℝ) : ℂ) := by
    simpa using h
  exact_mod_cast h2.symm

theorem exists_real_basis {ι : Type} [Fintype ι] [DecidableEq ι] [Nonempty ι] (A : Matrix ι ι ℝ) (h : A.det ≠ 0) :
    ∃ b : Module.Basis ι ℝ (ι → ℝ), ∀ i, b i = A i := by
  have hl : LinearIndependent ℝ A.row :=
    Matrix.linearIndependent_rows_iff_isUnit.2 ((Matrix.isUnit_iff_isUnit_det A).2 (isUnit_iff_ne_zero.2 h))
  refine ⟨basisOfLinearIndependentOfCardEqFinrank hl (by simp), fun i => ?_⟩
  rw [coe_basisOfLinearIndependentOfCardEqFinrank]
  rfl

theorem sum_places_int (hF : IsTotallyReal F) (ρ : InfinitePlace F → (F →+* ℝ))
    (hρ : ∀ w x, ((ρ w x : ℝ) : ℂ) = w.embedding x) (a : 𝓞 F) :
    ∃ z : ℤ, ∑ w, ρ w (a : F) = (z : ℝ) := by
  obtain ⟨z, hz⟩ : ∃ z : ℤ, algebraMap ℤ ℚ z = Algebra.trace ℚ F (a : F) :=
    IsIntegrallyClosed.isIntegral_iff.1
      (Algebra.isIntegral_trace (R := ℤ) (L := ℚ) (F := F) (RingOfIntegers.isIntegral_coe a))
  refine ⟨z, ?_⟩
  have h := trace_eq_sum_embeddings (K := ℚ) (L := F) ℂ (x := (a : F))
  rw [← (placeEquiv hF).sum_comp, ← hz] at h
  have h2 : ((z : ℝ) : ℂ) = ((∑ w, ρ w (a : F) : ℝ) : ℂ) := by
    push_cast
    simp only [hρ]
    simpa [placeEquiv] using h
  exact_mod_cast h2.symm

theorem integral_char_eq_zero (hF : IsTotallyReal F) (ρ : InfinitePlace F → (F →+* ℝ))
    (hρ : ∀ w x, ((ρ w x : ℝ) : ℂ) = w.embedding x) (N : ℕ)
    [Countable (latR ρ N)]
    (D : Set (InfinitePlace F → ℝ)) (hD : IsAddFundamentalDomain (latR ρ N) D volume)
    (β : F) (hβ : β ≠ 0) (hint : ∃ r : 𝓞 F, (r : F) = (N : F) * β) :
    ∫ x in D, Complex.exp ((2 * (Real.pi : ℂ) * Complex.I) * ((∑ w, ρ w β * x w : ℝ) : ℂ)) = 0 := by
  classical
  set f : (InfinitePlace F → ℝ) → ℂ := fun x =>
    Complex.exp ((2 * (Real.pi : ℂ) * Complex.I) * ((∑ w, ρ w β * x w : ℝ) : ℂ)) with hf
  have hadd : ∀ x y, f (x + y) = f x * f y := by
    intro x y
    simp only [hf, Pi.add_apply, mul_add, Finset.sum_add_distrib, Complex.ofReal_add, Complex.exp_add]
  have hper : ∀ (g : latR ρ N) x, f (g +ᵥ x) = f x := by
    rintro ⟨g, hg⟩ x
    obtain ⟨s, rfl⟩ := (mem_latR_iff ρ N g).1 hg
    obtain ⟨r, hr⟩ := hint
    obtain ⟨z, hz⟩ := sum_places_int hF ρ hρ (r * s)
    have hrs : ((r * s : 𝓞 F) : F) = (N : F) * β * (s : F) := by
      rw [← hr]
      first
        | rfl
        | simp
    have h1 : f (fun w => ρ w ((N : F) * (s : F))) = 1 := by
      have : (∑ w, ρ w β * ρ w ((N : F) * (s : F))) = (z : ℝ) := by
        rw [← hz]
        refine Finset.sum_congr rfl fun w _ => ?_
        rw [← map_mul]
        congr 1
        rw [hrs]
        ring
      simp only [hf, this]
      have := Complex.exp_int_mul_two_pi_mul_I z
      rw [← this]
      congr 1
      push_cast
      ring
    show f ((fun w => ρ w ((N : F) * (s : F))) + x) = f x
    rw [hadd, h1, one_mul]
  obtain ⟨w0⟩ : Nonempty (InfinitePlace F) := inferInstance
  have hρ0 : ρ w0 β ≠ 0 := by
    simpa using hβ
  let x0 : InfinitePlace F → ℝ := Pi.single w0 (1 / (2 * ρ w0 β))
  have hx0 : f x0 = -1 := by
    have : (∑ w, ρ w β * x0 w) = 1 / 2 := by
      rw [Finset.sum_eq_single w0]
      · simp only [x0, Pi.single_eq_same]
        field_simp
      · intro b _ hb
        simp [x0, Pi.single_eq_of_ne hb]
      · simp
    simp only [hf, this]
    rw [← Complex.exp_pi_mul_I]
    congr 1
    push_cast
    ring
  have hD' : IsAddFundamentalDomain (latR ρ N) (x0 +ᵥ D) volume := hD.vadd_of_comm x0
  have heq : ∫ x in x0 +ᵥ D, f x = ∫ x in D, f x := hD'.setIntegral_eq hD hper
  have htr : ∫ x in x0 +ᵥ D, f x = ∫ x in D, f (x0 + x) := by
    have := (measurePreserving_add_left (volume : Measure (InfinitePlace F → ℝ)) x0).setIntegral_image_emb
      (measurableEmbedding_addLeft x0) f D
    rw [← this, ← Set.image_vadd]
    rfl
  have hmul : ∫ x in D, f (x0 + x) = - ∫ x in D, f x := by
    simp only [hadd, hx0]
    rw [integral_const_mul]
    ring
  have h2 : ∫ x in D, f x = - ∫ x in D, f x := by
    rw [← hmul, ← htr, heq]
  have h3 : (2 : ℂ) * ∫ x in D, f x = 0 := by
    linear_combination h2
  simpa using h3

end GlobalTheory.CompanionTheory.SW.FD

theorem GlobalTheory.CompanionTheory.SW.FD.main : ∀ (F : Type) [Field F] [NumberField F], IsTotallyReal F → ∀ ρ : InfinitePlace F → (F →+* ℝ), (∀ w x, ((ρ w x : ℝ) : ℂ) = w.embedding x) → ∀ N : ℕ, 0 < N → (∃ D : Set (InfinitePlace F → ℝ), IsAddFundamentalDomain (latR ρ N) D volume) ∧ Countable (latR ρ N) ∧ (∀ y, y ∈ latR ρ N ↔ ∃ r : 𝓞 F, y = fun w => ρ w ((N : F) * (r : F))) ∧ ∀ D : Set (InfinitePlace F → ℝ), IsAddFundamentalDomain (latR ρ N) D volume → volume D = ENNReal.ofReal ((N : ℝ) ^ Module.finrank ℚ F * (kap F)⁻¹) ∧ ∀ β : F, β ≠ 0 → (∃ r : 𝓞 F, (r : F) = (N : F) * β) → ∫ x in D, Complex.exp ((2 * (Real.pi : ℂ) * Complex.I) * ((∑ w, ρ w β * x w : ℝ) : ℂ)) = 0 := by
  intro F _ _ hF ρ hρ N hN
  classical
  obtain ⟨B, hB⟩ := GlobalTheory.CompanionTheory.SW.FD.exists_integral_basis hF ρ hρ
  set M : Matrix (InfinitePlace F) (InfinitePlace F) ℝ :=
    Matrix.of fun i w => ρ w ((B i : 𝓞 F) : F) with hM
  have hN' : (N : ℝ) ≠ 0 := by exact_mod_cast hN.ne'
  have hdisc : (discr F : ℝ) ≠ 0 := by exact_mod_cast discr_ne_zero F
  have hdet : M.det ≠ 0 := by
    intro h
    apply hdisc
    rw [← hB, h]
    simp
  have hAdet : ((N : ℝ) • M).det ≠ 0 := by
    rw [Matrix.det_smul]
    exact mul_ne_zero (pow_ne_zero _ hN') hdet
  obtain ⟨b, hb⟩ := GlobalTheory.CompanionTheory.SW.FD.exists_real_basis _ hAdet
  have hbi : ∀ i, b i = GlobalTheory.CompanionTheory.SW.FD.scaleMap ρ N (B i) := by
    intro i
    rw [hb]
    ext w
    simp [GlobalTheory.CompanionTheory.SW.FD.scaleMap, hM]
  have hspan : latR ρ N = (Submodule.span ℤ (Set.range b)).toAddSubgroup := by
    rw [GlobalTheory.CompanionTheory.SW.FD.latR_eq_range, Submodule.span_int_eq_addSubgroupClosure]
    apply le_antisymm
    · rintro _ ⟨r, rfl⟩
      set_option synthInstance.maxHeartbeats 100000 in
        rw [← B.sum_repr r, map_sum]
      refine AddSubgroup.sum_mem _ fun i _ => ?_
      rw [map_zsmul, ← hbi]
      exact AddSubgroup.zsmul_mem _ (AddSubgroup.subset_closure (Set.mem_range_self i)) _
    · rw [AddSubgroup.closure_le]
      rintro _ ⟨i, rfl⟩
      exact ⟨B i, (hbi i).symm⟩
  have hfd : IsAddFundamentalDomain (latR ρ N) (ZSpan.fundamentalDomain b) volume := by
    rw [hspan]
    exact ZSpan.isAddFundamentalDomain' b volume
  have hcount : Countable (latR ρ N) := by
    haveI : Countable (𝓞 F) := B.equivFun.toEquiv.injective.countable
    rw [GlobalTheory.CompanionTheory.SW.FD.latR_eq_range]
    exact (Set.countable_range (GlobalTheory.CompanionTheory.SW.FD.scaleMap ρ N)).to_subtype
  refine ⟨⟨_, hfd⟩, hcount, GlobalTheory.CompanionTheory.SW.FD.mem_latR_iff ρ N, fun D hD => ⟨?_, fun β hβ hint =>
    GlobalTheory.CompanionTheory.SW.FD.integral_char_eq_zero hF ρ hρ N D hD β hβ hint⟩⟩
  rw [hD.measure_eq hfd, ZSpan.volume_fundamentalDomain]
  have hof : Matrix.of (b : InfinitePlace F → InfinitePlace F → ℝ) = (N : ℝ) • M := by
    ext i w
    rw [Matrix.of_apply, hb]
  rw [hof, Matrix.det_smul, GlobalTheory.CompanionTheory.SW.FD.card_places hF, abs_mul, abs_of_nonneg (by positivity)]
  congr 2
  rw [kap, inv_inv, ← hB, abs_of_nonneg (sq_nonneg M.det), Real.sqrt_sq_eq_abs]
end
end

-- bundled from CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.MobiusActionUpperHalfPlane
section
open NumberField IsDedekindDomain MeasureTheory Matrix Topology GlobalTheory.CompanionTheory.SW.Core
open scoped ENNReal NNReal MatrixGroups

noncomputable section

namespace GlobalTheory.CompanionTheory.SW.Core.Mobius

theorem den_ne (a b c d : ℝ) (hdet : a * d - b * c = 1) (τ : ℂ) (h : 0 < τ.im) :
    (c : ℂ) * τ + d ≠ 0 := by
  intro h0
  have him := congrArg Complex.im h0
  have hre := congrArg Complex.re h0
  simp at him hre
  rcases him with hc | hτ
  · subst hc
    have hd : d = 0 := by simpa using hre
    subst hd
    simp at hdet
  · exact h.ne' hτ

theorem im_frac (a b c d : ℝ) (hdet : a * d - b * c = 1) (τ : ℂ) (h : 0 < τ.im) :
    (((a : ℂ) * τ + b) / ((c : ℂ) * τ + d)).im = τ.im / ‖(c : ℂ) * τ + d‖ ^ 2 := by
  rw [Complex.div_im, ← Complex.normSq_eq_norm_sq, ← sub_div]
  congr 1
  simp
  linear_combination τ.im * hdet

theorem comp_frac (a b c d a' b' c' d' : ℝ) (hdet : a * d - b * c = 1)
    (hdet' : a' * d' - b' * c' = 1) (τ : ℂ) (h : 0 < τ.im) :
    (((a * a' + b * c' : ℝ) : ℂ) * τ + ((a * b' + b * d' : ℝ) : ℂ)) /
        (((c * a' + d * c' : ℝ) : ℂ) * τ + ((c * b' + d * d' : ℝ) : ℂ)) =
      ((a : ℂ) * (((a' : ℂ) * τ + b') / ((c' : ℂ) * τ + d')) + b) /
        ((c : ℂ) * (((a' : ℂ) * τ + b') / ((c' : ℂ) * τ + d')) + d) := by
  have h' := den_ne a' b' c' d' hdet' τ h
  have hX : 0 < (((a' : ℂ) * τ + b') / ((c' : ℂ) * τ + d')).im := by
    rw [im_frac a' b' c' d' hdet' τ h]
    have : 0 < ‖(c' : ℂ) * τ + d'‖ := norm_pos_iff.mpr h'
    positivity
  have h2 := den_ne a b c d hdet _ hX
  have e1 : (c : ℂ) * (((a' : ℂ) * τ + b') / ((c' : ℂ) * τ + d')) + d =
      (((c * a' + d * c' : ℝ) : ℂ) * τ + ((c * b' + d * d' : ℝ) : ℂ)) / ((c' : ℂ) * τ + d') := by
    rw [eq_div_iff h', add_mul, mul_assoc, div_mul_cancel₀ _ h']
    push_cast
    ring
  have e2 : (a : ℂ) * (((a' : ℂ) * τ + b') / ((c' : ℂ) * τ + d')) + b =
      (((a * a' + b * c' : ℝ) : ℂ) * τ + ((a * b' + b * d' : ℝ) : ℂ)) / ((c' : ℂ) * τ + d') := by
    rw [eq_div_iff h', add_mul, mul_assoc, div_mul_cancel₀ _ h']
    push_cast
    ring
  rw [e1, e2, div_div_div_cancel_right₀ h']

variable {F : Type} [Field F]

theorem det_emb (σ : F →+* ℝ) (γ : SL(2, F)) :
    σ (γ 0 0) * σ (γ 1 1) - σ (γ 0 1) * σ (γ 1 0) = 1 := by
  have h := γ.det_coe
  rw [Matrix.det_fin_two] at h
  have := congrArg σ h
  simpa using this

theorem main : ∀ (F : Type) [Field F] [NumberField F], ∀ (ρ : InfinitePlace F → (F →+* ℝ)) (τ : InfinitePlace F → ℂ), (∀ w, 0 < (τ w).im) → (∀ (γ : SL(2, F)) w, (mob ρ γ τ w).im = (τ w).im / ‖((ρ w (γ 1 0) : ℝ) : ℂ) * τ w + (ρ w (γ 1 1) : ℝ)‖ ^ 2 ∧ 0 < (mob ρ γ τ w).im) ∧ (∀ γ γ' : SL(2, F), mob ρ (γ * γ') τ = mob ρ γ (mob ρ γ' τ)) ∧ (∀ b : F, mob ρ (nMat b) τ = fun w => τ w + (ρ w b : ℝ)) ∧ (∀ a : Fˣ, mob ρ (mMat a) τ = fun w => ((ρ w (a : F) : ℝ) : ℂ) ^ 2 * τ w) ∧ mob ρ wMat τ = fun w => -(τ w)⁻¹ := by
  intro F _ _ ρ τ hτ
  have him : ∀ (γ : SL(2, F)) w, (mob ρ γ τ w).im =
      (τ w).im / ‖((ρ w (γ 1 0) : ℝ) : ℂ) * τ w + (ρ w (γ 1 1) : ℝ)‖ ^ 2 := fun γ w =>
    im_frac _ _ _ _ (det_emb (ρ w) γ) (τ w) (hτ w)
  refine ⟨fun γ w => ⟨him γ w, ?_⟩, ?_, ?_, ?_, ?_⟩
  · rw [him]
    have h1 := den_ne _ _ _ _ (det_emb (ρ w) γ) (τ w) (hτ w)
    have : 0 < ‖((ρ w (γ 1 0) : ℝ) : ℂ) * τ w + (ρ w (γ 1 1) : ℝ)‖ := norm_pos_iff.mpr h1
    have := hτ w
    positivity
  · intro γ γ'
    funext w
    have := comp_frac _ _ _ _ _ _ _ _ (det_emb (ρ w) γ) (det_emb (ρ w) γ') (τ w) (hτ w)
    simp only [mob, Matrix.SpecialLinearGroup.coe_mul, Matrix.mul_apply, Fin.sum_univ_two, map_add (f := _), map_mul]
    exact this
  · intro b
    funext w
    simp [mob, nMat]
  · intro a
    funext w
    have ha : (ρ w (a : F) : ℝ) ≠ 0 := by simp
    have hinv : ρ w ((a⁻¹ : Fˣ) : F) = (ρ w (a : F))⁻¹ := by simp
    have hc : ((ρ w (a : F) : ℝ) : ℂ) ≠ 0 := by exact_mod_cast ha
    simp [mob, mMat, hinv]
    field_simp
  · funext w
    simp [mob, wMat, neg_div, div_neg]

end GlobalTheory.CompanionTheory.SW.Core.Mobius
end
end

-- bundled from CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.SL2BruhatDecompositionIdentities
section
open NumberField IsDedekindDomain MeasureTheory Matrix Topology GlobalTheory.CompanionTheory.SW.Core
open scoped ENNReal NNReal MatrixGroups

namespace GlobalTheory.CompanionTheory.SW.Core.SL2BruhatDecomposition

private theorem coe_n {R : Type} [CommRing R] (b : R) :
    ((nMat b : SL(2, R)) : Matrix (Fin 2) (Fin 2) R) = !![1, b; 0, 1] := rfl

private theorem coe_m {R : Type} [CommRing R] (a : Rˣ) :
    ((mMat a : SL(2, R)) : Matrix (Fin 2) (Fin 2) R) = !![(a : R), 0; 0, ((a⁻¹ : Rˣ) : R)] := rfl

private theorem coe_w {R : Type} [CommRing R] :
    ((wMat : SL(2, R)) : Matrix (Fin 2) (Fin 2) R) = !![0, 1; -1, 0] := rfl

private theorem SL2_eq_of_entries_eq_matrix {R : Type} [CommRing R] {g : SL(2, R)} {p q r s : R}
    {h : SL(2, R)} (hh : (h : Matrix (Fin 2) (Fin 2) R) = !![p, q; r, s])
    (h0 : g 0 0 = p) (h1 : g 0 1 = q) (h2 : g 1 0 = r) (h3 : g 1 1 = s) : g = h := by
  apply Subtype.ext
  change (g : Matrix (Fin 2) (Fin 2) R) = (h : Matrix (Fin 2) (Fin 2) R)
  rw [hh, Matrix.eta_fin_two (g : Matrix (Fin 2) (Fin 2) R), h0, h1, h2, h3]

theorem decompositions : ∀ (R : Type) [CommRing R] (g : SL(2, R)), (∀ c : Rˣ, g 1 0 = (c : R) → g = nMat (g 0 0 * ((c⁻¹ : Rˣ) : R)) * mMat (-c⁻¹) * wMat * nMat (g 1 1 * ((c⁻¹ : Rˣ) : R))) ∧ (∀ a : Rˣ, g 0 0 = (a : R) → g = wMat⁻¹ * nMat (-(g 1 0 * ((a⁻¹ : Rˣ) : R))) * wMat * mMat a * nMat (g 0 1 * ((a⁻¹ : Rˣ) : R))) ∧ (∀ a : Rˣ, g 0 0 = (a : R) → g 1 0 = 0 → g = nMat (g 0 1 * (a : R)) * mMat a) ∧ (wMat : SL(2, R))⁻¹ = wMat * wMat * wMat := by
  intro R _ g
  have hdet : g 0 0 * g 1 1 - g 0 1 * g 1 0 = 1 := by
    have h := g.det_coe
    rwa [Matrix.det_fin_two] at h
  have hw : (wMat : SL(2, R))⁻¹ = wMat * wMat * wMat := by
    apply inv_eq_of_mul_eq_one_right
    apply Subtype.ext
    change (((wMat * (wMat * wMat * wMat) : SL(2, R))) : Matrix (Fin 2) (Fin 2) R) = ((1 : SL(2, R)) : Matrix (Fin 2) (Fin 2) R)
    simp only [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_one, coe_w,
      Matrix.mul_fin_two, Matrix.one_fin_two]
    simp
  refine ⟨?_, ?_, ?_, hw⟩
  · intro c hc
    have hu : (c : R) * ((c⁻¹ : Rˣ) : R) = 1 := by simp
    have hinv : ((-c⁻¹ : Rˣ) : R) = -((c⁻¹ : Rˣ) : R) := by simp
    have hinv2 : (((-c⁻¹ : Rˣ)⁻¹ : Rˣ) : R) = -(c : R) := by simp
    refine SL2_eq_of_entries_eq_matrix (p := g 0 0) (q := g 0 1) (r := g 1 0) (s := g 1 1) ?_ rfl rfl rfl rfl
    simp only [Matrix.SpecialLinearGroup.coe_mul, coe_n, coe_m, coe_w, Matrix.mul_fin_two, hinv, hinv2]
    generalize ((c⁻¹ : Rˣ) : R) = u at hu
    rw [hc] at hdet ⊢
    congr
    · linear_combination (g 0 0) * hu
    · linear_combination (g 0 0 * g 1 1 * u + g 0 1) * hu + u * hdet
    · ring
    · linear_combination (g 1 1) * hu
  · intro a ha
    have hu : (a : R) * ((a⁻¹ : Rˣ) : R) = 1 := by simp
    rw [hw]
    refine SL2_eq_of_entries_eq_matrix (p := g 0 0) (q := g 0 1) (r := g 1 0) (s := g 1 1) ?_ rfl rfl rfl rfl
    simp only [Matrix.SpecialLinearGroup.coe_mul, coe_n, coe_m, coe_w, Matrix.mul_fin_two]
    generalize ((a⁻¹ : Rˣ) : R) = u at hu
    rw [ha] at hdet ⊢
    congr
    · ring
    · linear_combination (g 0 1) * hu
    · linear_combination (g 1 0) * hu
    · linear_combination (g 1 0 * g 0 1 * u + g 1 1) * hu - u * hdet
  · intro a ha hc
    have hu : (a : R) * ((a⁻¹ : Rˣ) : R) = 1 := by simp
    refine SL2_eq_of_entries_eq_matrix (p := g 0 0) (q := g 0 1) (r := g 1 0) (s := g 1 1) ?_ rfl rfl rfl rfl
    simp only [Matrix.SpecialLinearGroup.coe_mul, coe_n, coe_m, Matrix.mul_fin_two]
    generalize ((a⁻¹ : Rˣ) : R) = u at hu
    rw [ha, hc] at hdet ⊢
    congr
    · ring
    · linear_combination (g 0 1) * hu
    · ring
    · linear_combination (g 1 1) * hu - u * hdet

end GlobalTheory.CompanionTheory.SW.Core.SL2BruhatDecomposition
end

-- bundled from CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.SbEqSumCosetIndicators
section
open NumberField IsDedekindDomain MeasureTheory Matrix Topology GlobalTheory.CompanionTheory.SW.Core
open scoped ENNReal NNReal MatrixGroups

namespace GlobalTheory.CompanionTheory.SW.Span

theorem sb_eq_sum_coset_indicators :
    ∀ (V : Type) [AddCommGroup V] [TopologicalSpace V] [MeasurableSpace V] (χ : V → V → ℂ)
      (μ : Measure V), NADual V χ μ → ∀ φ : V → ℂ, SB φ → ∀ L' : AddSubgroup V,
      IsOpen (L' : Set V) → (∀ x, ∀ l ∈ L', φ (x + l) = φ x) →
      ∃ s : Finset V, ∀ x, φ x = ∑ a ∈ s, φ a * Set.indicator {y | y - a ∈ L'} (fun _ => (1 : ℂ)) x := by
  intro V _ _ _ χ μ h φ hφ L' hL' hinv
  classical
  haveI : IsTopologicalAddGroup V := h.1
  obtain ⟨t, ht⟩ := hφ.2.isCompact.elim_finite_subcover (fun a : V => {y | y - a ∈ L'})
    (fun a => hL'.preimage (continuous_id.sub continuous_const))
    (fun x _ => Set.mem_iUnion.2 ⟨x, by simp [L'.zero_mem]⟩)
  let T : Finset (V ⧸ L') := t.image (QuotientAddGroup.mk : V → V ⧸ L')
  refine ⟨T.image Quotient.out, fun x => ?_⟩
  rw [Finset.sum_image (fun a _ b _ hab => Quotient.out_injective hab)]
  have key : ∀ q : V ⧸ L', x - q.out ∈ L' ↔ q = (x : V ⧸ L') := by
    intro q
    conv_rhs => rw [← QuotientAddGroup.out_eq' q]
    rw [QuotientAddGroup.eq, neg_add_eq_sub]
  have hval : φ ((x : V ⧸ L').out) = φ x := by
    have hm : x - ((x : V ⧸ L')).out ∈ L' := (key _).2 rfl
    have := hinv ((x : V ⧸ L')).out _ hm
    rw [← this]
    congr 1
    abel
  have hterm : ∀ q : V ⧸ L', φ q.out * Set.indicator {y | y - q.out ∈ L'} (fun _ => (1 : ℂ)) x
      = if q = (x : V ⧸ L') then φ x else 0 := by
    intro q
    by_cases hq : q = (x : V ⧸ L')
    · subst hq
      rw [if_pos rfl, Set.indicator_of_mem (show x ∈ {y | y - ((x : V ⧸ L')).out ∈ L'} from (key _).2 rfl),
        hval, mul_one]
    · rw [if_neg hq, Set.indicator_of_notMem (show x ∉ {y | y - q.out ∈ L'} from fun hx => hq ((key _).1 hx)),
        mul_zero]
  simp only [hterm, Finset.sum_ite_eq']
  split_ifs with hx
  · rfl
  · by_contra hne
    have hmem : x ∈ tsupport φ := subset_tsupport φ hne
    obtain ⟨a, ha, hxa⟩ := Set.mem_iUnion₂.1 (ht hmem)
    apply hx
    refine Finset.mem_image.2 ⟨a, ha, ?_⟩
    rw [QuotientAddGroup.eq, neg_add_eq_sub]
    exact hxa

end GlobalTheory.CompanionTheory.SW.Span
end

