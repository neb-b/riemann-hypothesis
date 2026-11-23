module

public import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.FockOperators.XApply
public import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.FockOperators.Bundle0005
public import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.FockOperators.Bundle0009
public import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.FockOperators.Bundle0007
public import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.FockOperators.Bundle0006
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.ArchimedeanCompact.OneTmulMemCenter
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.RingEquivPlaceCorrespondencePlaceUnder
public import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.FockOperators.Bundle0001

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.FockOperators.Entries
section
open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2 UpperTheory.ConvolutionTheory.R2.Fo
open scoped Classical

private theorem entries {F : Type} [Field F] [NumberField F] [IsTotallyReal F] (k : G1 F) (hk : InfOrth k)
    (w : InfinitePlace F) : cw w (k 1 0) = -cw w (k 0 1) ∧ cw w (k 1 1) = cw w (k 0 0) := by
  let pw : A F →+* ℝ := (Pi.evalRingHom (fun _ : InfinitePlace F => ℝ) w).comp (TR.pInf F)
  have hO : ∀ i j, pw ((k.1 * k.1ᵀ) i j) = pw ((1 : Matrix (Fin 2) (Fin 2) (A F)) i j) := fun i j =>
    congrFun (congrArg (TR.infEq F).symm (hk i j)) w
  have h00 := hO 0 0
  have h01 := hO 0 1
  have hd : pw (k 0 0) * pw (k 1 1) - pw (k 0 1) * pw (k 1 0) = 1 := by
    have h := k.det_coe
    rw [Matrix.det_fin_two] at h
    have := congrArg pw h
    simpa using this
  simp only [Matrix.mul_apply, Fin.sum_univ_two, Matrix.transpose_apply, map_add (f := _), map_mul] at h00 h01
  simp only [Matrix.one_apply_eq, map_one] at h00
  simp only [Matrix.one_apply_ne (zero_ne_one : (0 : Fin 2) ≠ 1), map_zero] at h01
  change pw (k 0 0) * pw (k 0 0) + pw (k 0 1) * pw (k 0 1) = 1 at h00
  have hc : pw (k 1 0) = -pw (k 0 1) := by
    linear_combination (-pw (k 1 0)) * h00 + pw (k 0 0) * h01 - pw (k 0 1) * hd
  have he : pw (k 1 1) = pw (k 0 0) := by
    linear_combination (-pw (k 1 1)) * h00 + pw (k 0 1) * h01 + pw (k 0 0) * hd
  constructor
  · change ((pw (k 1 0) : ℝ) : ℂ) = -((pw (k 0 1) : ℝ) : ℂ)
    rw [hc]; push_cast; rfl
  · change ((pw (k 1 1) : ℝ) : ℂ) = ((pw (k 0 0) : ℝ) : ℂ)
    rw [he]

private theorem step {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    [IsTotallyReal F] [_root_.NumberField.IsTotallyComplex E] (D : Dat F E) (W : Weil D) (O : Ops F) (k : G1 F)
    (w : InfinitePlace F) (i j : Fin 4) (s : ℂ) (hs : s * s = -1)
    (hc : cw w (k 1 0) = -cw w (k 0 1)) (he : cw w (k 1 1) = cw w (k 0 0)) (φ : S4 F)
    (h1 : O.d w i φ = s • O.p D.δ w j φ) (h2 : O.d w j φ = s • O.p D.δ w i φ) :
    O.d w i (W.Om k φ) = s • O.p D.δ w j (W.Om k φ) := by
  have e1 := congrArg (fun T : Module.End ℂ (S4 F) => T φ) (Heisenberg₂ F E D W O k w i).1
  have e2 := congrArg (fun T : Module.End ℂ (S4 F) => T φ) (Heisenberg₂ F E D W O k w j).2
  simp only [Module.End.mul_apply, LinearMap.add_apply, LinearMap.smul_apply, map_add (f := _), map_smul] at e1 e2
  rw [e1, e2, hc, he, h1, h2]
  simp only [map_smul, smul_add, smul_smul]
  have : s * (-cw w (k 0 1) * s) = cw w (k 0 1) := by linear_combination (-cw w (k 0 1)) * hs
  rw [this, add_comm]
  congr 1
  rw [mul_comm]

private theorem scal {F : Type} [Field F] [NumberField F] [IsTotallyReal F] (δ : F) (O : Ops F)
    (w : InfinitePlace F) (f : S4 F) :
    ((-2 * Real.pi * kap δ w 0 : ℂ) • O.x w 0 f = Complex.I • O.p δ w 1 f) ∧
    ((-2 * Real.pi * kap δ w 1 : ℂ) • O.x w 1 f = Complex.I • O.p δ w 0 f) ∧
    ((-2 * Real.pi * kap δ w 2 : ℂ) • O.x w 2 f = (-Complex.I) • O.p δ w 2 f) ∧
    ((-2 * Real.pi * kap δ w 3 : ℂ) • O.x w 3 f = (-Complex.I) • O.p δ w 3 f) := by
  have hI := Complex.I_mul_I
  refine ⟨?_, ?_, ?_, ?_⟩ <;>
    simp only [Ops.p, kap, cc, Matrix.cons_val, LinearMap.smul_apply, smul_smul] <;>
    congr 1
  · linear_combination (-2 * (Real.pi : ℂ)) * hI
  · linear_combination (-2 * (Real.pi : ℂ)) * hI
  · linear_combination (-4 * (Real.pi : ℂ)) * hI
  · linear_combination (4 * (Real.pi : ℂ) * cw w (rt δ)) * hI

theorem UpperTheory.ConvolutionTheory.R2.Fo.vacOm :
    ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] [IsTotallyReal F] [_root_.NumberField.IsTotallyComplex E] (D : Dat F E) (W : Weil D) (k : G1 F), InfOrth k → ∀ φ ∈ Vac D.δ, W.Om k φ ∈ Vac D.δ := by
  intro F E _ _ _ _ _ _ _ D W k hk φ hφ
  obtain ⟨O⟩ := opsEx F
  have hv := vacAnn F D.δ O φ hφ
  refine annVac F D.δ O (W.Om k φ) fun w i => ?_
  obtain ⟨hc, he⟩ := entries k hk w
  have hI : Complex.I * Complex.I = -1 := Complex.I_mul_I
  have hJ : (-Complex.I) * (-Complex.I) = -1 := by rw [neg_mul_neg, hI]
  obtain ⟨s0, s1, s2, s3⟩ := scal D.δ O w φ
  obtain ⟨t0, t1, t2, t3⟩ := scal D.δ O w (W.Om k φ)
  have v0 := (hv w 0).trans s0
  have v1 := (hv w 1).trans s1
  have v2 := (hv w 2).trans s2
  have v3 := (hv w 3).trans s3
  fin_cases i
  · exact (step D W O k w 0 1 _ hI hc he φ v0 v1).trans t0.symm
  · exact (step D W O k w 1 0 _ hI hc he φ v1 v0).trans t1.symm
  · exact (step D W O k w 2 2 _ hJ hc he φ v2 v2).trans t2.symm
  · exact (step D W O k w 3 3 _ hJ hc he φ v3 v3).trans t3.symm
end

-- bundled from Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.FockOperators.EopLift
section
open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2 UpperTheory.ConvolutionTheory.R2.Fo
open scoped Classical

private theorem coord_half {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (σ τ : E →+* ℂ) :
    (1 / 2 : ℂ) * (coord σ (atEmb τ 1) - Complex.I * coord σ (atEmb τ Complex.I)) = if σ = τ then 1 else 0 := by
  by_cases h : InfinitePlace.mk σ = InfinitePlace.mk τ
  · rcases InfinitePlace.mk_eq_iff.1 h with e | e
    · subst e
      rw [if_pos rfl, coord_atEmb, coord_atEmb, Complex.I_mul_I]
      norm_num
    · have hne : ComplexEmbedding.conjugate τ ≠ τ := fun h' =>
        InfinitePlace.not_isReal_iff_isComplex.2 (IsTotallyComplex.isComplex (InfinitePlace.mk τ))
          (InfinitePlace.isReal_mk_iff.2 (ComplexEmbedding.isReal_iff.2 h'))
      obtain rfl : σ = ComplexEmbedding.conjugate τ := by
        rw [← e]; exact (star_star σ).symm
      rw [if_neg hne, GlobalTheory.IsoPull.coord_conj, GlobalTheory.IsoPull.coord_conj, coord_atEmb, coord_atEmb]
      simp
  · rw [GlobalTheory.IsoPull.coord_atEmb_of_ne h, GlobalTheory.IsoPull.coord_atEmb_of_ne h, if_neg (fun e => h (by rw [e]))]
    simp

private theorem coord_single {E : Type} [Field E] (σ : E →+* ℂ) (i j k l : Fin 2) (c : Cinf E) :
    coord σ ((toL (Matrix.single i j c) : Lie E 2) k l) = if k = i ∧ l = j then coord σ c else 0 := by
  change coord σ (Matrix.single i j c k l) = _
  rw [Matrix.single_apply]
  by_cases h : k = i ∧ l = j
  · obtain ⟨rfl, rfl⟩ := h
    simp
  · rw [if_neg h, if_neg (fun e => h ⟨e.1.symm, e.2.symm⟩), map_zero]

private theorem half_comb {E N : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] [AddCommGroup N] [Module ℂ N]
    (R : (E →+* ℂ) → Fin 2 → Fin 2 → N) (τ : E →+* ℂ) (i j : Fin 2) (x y : N)
    (hx : x = ∑ σ : E →+* ℂ, ∑ k, ∑ l, coord σ ((toL (Matrix.single i j (atEmb τ 1)) : Lie E 2) k l) • R σ k l)
    (hy : y = ∑ σ : E →+* ℂ, ∑ k, ∑ l, coord σ ((toL (Matrix.single i j (atEmb τ Complex.I)) : Lie E 2) k l) • R σ k l) :
    (1 / 2 : ℂ) • (x - Complex.I • y) = R τ i j := by
  have e : ∀ c : Cinf E, ∀ σ : E →+* ℂ, ∑ k, ∑ l, coord σ ((toL (Matrix.single i j c) : Lie E 2) k l) • R σ k l = coord σ c • R σ i j := by
    intro c σ
    simp only [coord_single, ite_smul, zero_smul, ite_and]
    simp
  simp only [e] at hx hy
  have hz : ∀ σ : E →+* ℂ, (1 / 2 : ℂ) • (coord σ (atEmb τ 1) • R σ i j - Complex.I • coord σ (atEmb τ Complex.I) • R σ i j) =
      if σ = τ then R σ i j else 0 := by
    intro σ
    rw [smul_smul, ← sub_smul, smul_smul, coord_half]
    split_ifs <;> simp
  rw [hx, hy, Finset.smul_sum, ← Finset.sum_sub_distrib, Finset.smul_sum]
  simp only [hz]
  simp

theorem UpperTheory.ConvolutionTheory.R2.Fo.eopLift :
    ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] [IsTotallyReal F] [_root_.NumberField.IsTotallyComplex E] (D : Dat F E) (W : Weil D) (M : Meas F) (π : TR.CuspSub F 2) (O : Ops F) (Λ : TR.Sm F 2 →ₗ[ℂ] S4 F →ₗ[ℂ] Sm E 2), (∀ f ∈ π.V, ∀ φ ∈ Fock D.δ, (Λ f φ).1 = lift W M f.1 φ) → LieLift O W M π →
    ∀ (τ : E →+* ℂ) i j, ∀ f ∈ π.V, ∀ φ ∈ Fock D.δ, Eop τ i j (Λ f φ) = Λ f (O.dE D τ i j φ) + if i = j then Λ (TR.Eop (pl F τ) 1 1 f) φ else 0 := by
  intro F E _ _ _ _ _ _ _ D W M π O Λ hΛ hL τ i j f hf φ hφ
  have hE : ∀ σ : E →+* ℂ, TR.Eop (pl F σ) 1 1 f ∈ π.V := fun σ => π.stable (.lie _) f hf
  have key : ∀ Y : Lie E 2, lie E 2 Y (Λ f φ) = ∑ σ : E →+* ℂ, ∑ k, ∑ l, coord σ (Y k l) •
      (Λ f (O.dE D σ k l φ) + if k = l then Λ (TR.Eop (pl F σ) 1 1 f) φ else 0) := by
    intro Y
    have h1 := (fockOps F E D O φ hφ).2.2.2.2.2.2 Y
    have h2 : lie E 2 Y (Λ f φ) = Λ f (O.dL D Y φ) +
        ∑ σ : E →+* ℂ, coord σ (Y 0 0 + Y 1 1) • Λ (TR.Eop (pl F σ) 1 1 f) φ := by
      refine Subtype.ext (funext fun h => ?_)
      rw [hL f hf φ hφ (Λ f φ) (hΛ f hf φ hφ) Y h]
      simp only [Submodule.coe_add, Submodule.coe_sum, Submodule.coe_smul, Pi.add_apply, Finset.sum_apply, Pi.smul_apply,
        smul_eq_mul, hΛ _ (hE _) φ hφ, hΛ f hf _ h1]
    have h3 : Λ f (O.dL D Y φ) = ∑ σ : E →+* ℂ, ∑ k, ∑ l, coord σ (Y k l) • Λ f (O.dE D σ k l φ) := by
      set_option synthInstance.maxHeartbeats 100000 in
        simp only [Ops.dL, LinearMap.sum_apply, LinearMap.smul_apply, map_sum, map_smul]
    rw [h2, h3, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun σ _ => ?_
    simp only [Fin.sum_univ_two, smul_add, map_add (f := _), add_smul]
    simp
    abel
  have hEop : Eop τ i j = (1 / 2 : ℂ) • (lie E 2 (toL (Matrix.single i j (atEmb τ 1))) -
      Complex.I • lie E 2 (toL (Matrix.single i j (atEmb τ Complex.I)))) := rfl
  rw [hEop]
  exact half_comb (fun σ k l => Λ f (O.dE D σ k l φ) + if k = l then Λ (TR.Eop (pl F σ) 1 1 f) φ else 0) τ i j _ _
    (key _) (key _)
end

-- bundled from Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.FockOperators.OmX
section
open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2 UpperTheory.ConvolutionTheory.R2.Fo
open scoped Classical

theorem UpperTheory.ConvolutionTheory.R2.Fo.omX :
    ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] [IsTotallyReal F] [_root_.NumberField.IsTotallyComplex E] (D : Dat F E) (W : Weil D) (O : Ops F) (g : G1 F) w i φ, W.Om g (O.x w i φ) ∈ Submodule.span ℂ {χ : S4 F | ∃ w' j, χ = O.x w' j (W.Om g φ) ∨ χ = O.d w' j (W.Om g φ)} := by
  intro F E _ _ _ _ _ _ _ D W O g w i φ
  have hcc : cc ≠ 0 := by
    simp [cc, Real.pi_ne_zero]
  have hδ : cw w (rt D.δ) ≠ 0 := (coordMk F E D).2.2.1 w
  have key : ∀ i : Fin 4, ∃ (j : Fin 4) (c : ℂ), c ≠ 0 ∧ O.p D.δ w j = c • O.x w i := by
    intro i
    fin_cases i
    · exact ⟨1, -cc, neg_ne_zero.2 hcc, rfl⟩
    · exact ⟨0, -cc, neg_ne_zero.2 hcc, rfl⟩
    · exact ⟨2, 2 * cc, mul_ne_zero two_ne_zero hcc, rfl⟩
    · exact ⟨3, -2 * cw w (rt D.δ) * cc,
        mul_ne_zero (mul_ne_zero (neg_ne_zero.2 two_ne_zero) hδ) hcc, rfl⟩
  obtain ⟨j, c, hc, hp⟩ := key i
  have h := (Heisenberg₂ F E D W O g⁻¹ w j).2
  have h1 : W.Om g * W.Om g⁻¹ = 1 := by rw [← map_mul, mul_inv_cancel, map_one]
  have h3 : W.Om g⁻¹ * W.Om g = 1 := by rw [← map_mul, inv_mul_cancel, map_one]
  generalize cw w (g⁻¹ 1 0) = α at h
  generalize cw w (g⁻¹ 1 1) = β at h
  have h2 : W.Om g * O.p D.δ w j = (α • O.d w j + β • O.p D.δ w j) * W.Om g := by
    calc W.Om g * O.p D.δ w j = W.Om g * O.p D.δ w j * (W.Om g⁻¹ * W.Om g) := by rw [h3, mul_one]
      _ = W.Om g * (O.p D.δ w j * W.Om g⁻¹) * W.Om g := by simp only [mul_assoc]
      _ = W.Om g * (W.Om g⁻¹ * (α • O.d w j + β • O.p D.δ w j)) * W.Om g := by rw [h]
      _ = (W.Om g * W.Om g⁻¹) * (α • O.d w j + β • O.p D.δ w j) * W.Om g := by simp only [mul_assoc]
      _ = (α • O.d w j + β • O.p D.δ w j) * W.Om g := by rw [h1, one_mul]
  have hx : O.x w i = c⁻¹ • O.p D.δ w j := by rw [hp, smul_smul, inv_mul_cancel₀ hc, one_smul]
  have h4 : W.Om g (O.p D.δ w j φ) = α • O.d w j (W.Om g φ) + (β * c) • O.x w i (W.Om g φ) := by
    have := LinearMap.congr_fun h2 φ
    simp only [Module.End.mul_apply, LinearMap.add_apply, LinearMap.smul_apply] at this
    rw [this, hp, LinearMap.smul_apply, smul_smul]
  have h5 : W.Om g (O.x w i φ) =
      (c⁻¹ * α) • O.d w j (W.Om g φ) + (c⁻¹ * (β * c)) • O.x w i (W.Om g φ) := by
    rw [hx, LinearMap.smul_apply, map_smul, h4, ← hx, smul_add, smul_smul, smul_smul]
  rw [h5]
  exact Submodule.add_mem _
    (Submodule.smul_mem _ _ (Submodule.subset_span ⟨w, j, Or.inr rfl⟩))
    (Submodule.smul_mem _ _ (Submodule.subset_span ⟨w, i, Or.inl rfl⟩))
end

