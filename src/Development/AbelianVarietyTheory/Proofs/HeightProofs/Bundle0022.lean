module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.IsTopologicalRingAE
public import Development.AbelianVarietyTheory.Counterexamples.HeightSurvey.Bundle0003
public import Development.AbelianVarietyTheory.Definitions.HeightFunctions.FiniteDimensionalOfSz
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.Bundle0018
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0084
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0006

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.HeightProofs.EqZeroOfCreationEqZero
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Matrix GlobalTheory.FockCompare GlobalTheory.IndefiniteRowSideFullHecke.FockOrthogonalDecomposition
open scoped TensorProduct ContDiff ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.FockCompare

theorem eq_zero_of_bounded_of_creation_eq {R : Type} [NormedAddCommGroup R] [NormedSpace ℝ R]
    (F : R → ℂ) (hF : Differentiable ℝ F) (C : ℝ) (hC : ∀ x, ‖F x‖ ≤ C) (u u' : R) (a b q : ℝ) (hq : 0 < q)
    (h : ∀ s t : ℝ, fderiv ℝ F (s • u - t • u') u - Complex.I * fderiv ℝ F (s • u - t • u') u' =
      Real.pi * Complex.I * ((a + t * q) - Complex.I * (b + s * q)) * F (s • u - t • u')) :
    F 0 = 0 := by
  let L : ℂ →L[ℝ] R := Complex.reCLM.smulRight u - Complex.imCLM.smulRight u'
  have hL : ∀ z : ℂ, L z = z.re • u - z.im • u' := fun z => rfl
  let re' : ℂ →L[ℝ] ℂ := Complex.ofRealCLM.comp Complex.reCLM
  let im' : ℂ →L[ℝ] ℂ := Complex.ofRealCLM.comp Complex.imCLM
  have hre : ∀ z : ℂ, re' z = (z.re : ℂ) := fun z => rfl
  have him : ∀ z : ℂ, im' z = (z.im : ℂ) := fun z => rfl
  let c1 : ℂ := -(Real.pi * Complex.I)
  let c2 : ℂ := -(Real.pi * q / 2)
  let φ : ℂ → ℂ := fun z => c1 * (a * re' z - b * im' z) + c2 * (re' z * re' z + im' z * im' z)
  let H : ℂ → ℂ := fun z => Complex.exp (φ z) * F (L z)
  have hHd : Differentiable ℂ H := by
    intro z
    have r := re'.hasFDerivAt (x := z)
    have i := im'.hasFDerivAt (x := z)
    have h1 := ((((r.const_mul (a : ℂ)).sub (i.const_mul (b : ℂ))).const_mul c1).add
      (((r.mul r).add (i.mul i)).const_mul c2)).cexp
    have h2 := (hF (L z)).hasFDerivAt.comp z (L.hasFDerivAt (x := z))
    have h3 : HasFDerivAt H _ z := h1.mul h2
    rw [differentiableAt_complex_iff_differentiableAt_real]
    refine ⟨h3.differentiableAt, ?_⟩
    rw [h3.fderiv]
    have e := h z.re z.im
    rw [← hL] at e
    have e1 : L 1 = u := by simp [hL]
    have eI : L Complex.I = -u' := by simp [hL]
    simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply, ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.sub_apply, e1, eI, hre, him, smul_eq_mul, map_neg, Function.comp_apply,
      Complex.I_re, Complex.I_im, Complex.one_re, Complex.one_im, Complex.ofReal_zero, Complex.ofReal_one]
    generalize Complex.exp _ = E
    rw [sub_eq_iff_eq_add] at e
    rw [e]
    simp only [c1, c2]
    linear_combination (-(E * fderiv ℝ F (L z) u') + E * F (L z) * Real.pi * (-(z.im * q) + Complex.I * (b + z.re * q))) * Complex.I_mul_I
  have hn : ∀ z, ‖H z‖ ≤ C * Real.exp (-(Real.pi * q / 2) * ‖z‖ ^ 2) := by
    intro z
    have : (φ z).re = -(Real.pi * q / 2) * ‖z‖ ^ 2 := by
      rw [Complex.sq_norm, Complex.normSq_apply]
      simp [φ, c1, c2, hre, him]
    simp only [H]
    rw [norm_mul, Complex.norm_exp, this, mul_comm]
    exact mul_le_mul_of_nonneg_right (hC _) (Real.exp_pos _).le
  have ht : Filter.Tendsto H (Filter.cocompact ℂ) (nhds 0) := by
    refine squeeze_zero_norm hn ?_
    have hp : -(Real.pi * q / 2) < 0 := by have := Real.pi_pos; have : 0 < Real.pi * q / 2 := by positivity
                                           linarith
    have t1 : Filter.Tendsto (fun z : ℂ => ‖z‖ ^ 2) (Filter.cocompact ℂ) Filter.atTop :=
      (Filter.tendsto_pow_atTop two_ne_zero).comp tendsto_norm_cocompact_atTop
    have t2 := (Real.tendsto_exp_atBot.comp (t1.const_mul_atTop_of_neg hp)).const_mul C
    simpa using t2
  have h0 := hHd.apply_eq_of_tendsto_cocompact 0 ht
  simp only [H, map_zero, mul_eq_zero, Complex.exp_ne_zero, false_or] at h0
  exact h0

theorem eq_zero_of_creation_eq_zero : ∀ (G R : Type) [AddCommGroup G] [NormedAddCommGroup R] [NormedSpace ℝ R] [FiniteDimensional ℝ R] (ι : R →+ G) (π : G →+ R) (om : R →ₗ[ℝ] R →ₗ[ℝ] ℝ), (∀ x, π (ι x) = x) → (∀ (f : G → ℂ), Sm ι f → ∀ (u : R) (w : G), hD ι π om u f w = -(Real.pi * Complex.I) * (om (π w) u : ℝ) * f w + fderiv ℝ (fun x : R => f (w + ι x)) 0 u) → (∀ u v, om v u = -om u v) → ∀ (f : G → ℂ), Sm ι f → (∀ w, ∃ C : ℝ, ∀ x, ‖f (w + ι x)‖ ≤ C) → ∀ u u' : R, 0 < om u u' → hD ι π om u f - Complex.I • hD ι π om u' f = 0 → f = 0 := by
  intro G R _ _ _ _ ι π om hπ hform hanti f hf hb u u' hq h0
  funext w
  obtain ⟨C, hC⟩ := hb w
  have hF : Differentiable ℝ fun x : R => f (w + ι x) := (hf w).differentiable (by simp)
  have huu : ∀ v, om v v = 0 := fun v => by have := hanti v v; linarith
  have key := eq_zero_of_bounded_of_creation_eq (fun x : R => f (w + ι x)) hF C hC u u'
    (om (π w) u) (om (π w) u') (om u u') hq (fun s t => by
      set x := s • u - t • u' with hx
      have e := congrFun h0 (w + ι x)
      have hfd : fderiv ℝ (fun y : R => f (w + ι x + ι y)) 0 = fderiv ℝ (fun y : R => f (w + ι y)) x := by
        have : (fun y : R => f (w + ι x + ι y)) = fun y => (fun y : R => f (w + ι y)) (x + y) := by
          funext y; simp only [map_add (f := _), add_assoc]
        rw [this, fderiv_comp_add_left (f := fun y : R => f (w + ι y)), add_zero]
      simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply, hform f hf, hfd] at e
      have e1 : om (π (w + ι x)) u = om (π w) u + t * om u u' := by
        rw [map_add (f := _), hπ, map_add (f := _), LinearMap.add_apply, hx]
        simp [huu, hanti u u']
      have e2 : om (π (w + ι x)) u' = om (π w) u' + s * om u u' := by
        rw [map_add (f := _), hπ, map_add (f := _), LinearMap.add_apply, hx]
        simp [huu]
      rw [e1, e2] at e
      push_cast at e
      linear_combination e)
  simpa using key

end GlobalTheory.FockCompare
end

-- bundled from Development.AbelianVarietyTheory.Proofs.HeightProofs.ExistsFieldIdealsPrincipal
section
open NumberField IsDedekindDomain GlobalTheory.FieldSize
open scoped IntermediateField nonZeroDivisors

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.FieldSize.Capit

theorem coeSubmodule_pow {R K : Type} [CommRing R] [CommRing K] [Algebra R K] (I : Ideal R) (k : ℕ) :
    IsLocalization.coeSubmodule K (I ^ k) = IsLocalization.coeSubmodule K I ^ k := by
  induction k with
  | zero => simp [IsLocalization.coeSubmodule_top]
  | succ k ih => rw [pow_succ, pow_succ, IsLocalization.coeSubmodule_mul, ih]

variable {E : Type} [Field E] [NumberField E] (φ : E →+* ℂ)

def intMap (F : IntermediateField ℚ ℂ) (h : ∀ x, φ x ∈ F) : 𝓞 E →+* 𝓞 F :=
  RingOfIntegers.mapRingHom (φ.codRestrict F h)

theorem coe_intMap (F : IntermediateField ℚ ℂ) (h : ∀ x, φ x ∈ F) (a : 𝓞 E) :
    ((intMap φ F h a : F) : ℂ) = φ (a : E) := rfl

theorem intMap_injective (F : IntermediateField ℚ ℂ) (h : ∀ x, φ x ∈ F) :
    Function.Injective (intMap φ F h) := by
  intro a b hab
  have h1 : φ (a : E) = φ (b : E) := by rw [← coe_intMap φ F h, ← coe_intMap φ F h, hab]
  exact RingOfIntegers.ext (φ.injective h1)

def intIncl {F K : IntermediateField ℚ ℂ} (hFK : F ≤ K) : 𝓞 F →+* 𝓞 K :=
  RingOfIntegers.mapRingHom (IntermediateField.inclusion hFK).toRingHom

theorem map_intMap {F K : IntermediateField ℚ ℂ} (hFK : F ≤ K) (h : ∀ x, φ x ∈ F) (I : Ideal (𝓞 E)) :
    I.map (intMap φ K fun x => hFK (h x)) = (I.map (intMap φ F h)).map (intIncl hFK) := by
  rw [Ideal.map_map]; rfl

theorem sz_mono' {F : IntermediateField ℚ ℂ} {a b a' b' : ℝ} (h : Sz F a b) (ha : a ≤ a') (hb : b ≤ b') :
    Sz F a' b' := by
  obtain ⟨i, h1, h2⟩ := h
  exact ⟨i, h1.trans ha, h2.trans hb⟩

theorem step (F : IntermediateField ℚ ℂ) (a b : ℝ) (hF : Sz F a b) (h : ∀ x, φ x ∈ F) (k : ℕ) (hk : 0 < k)
    (I : Ideal (𝓞 E)) (hI : I ≠ ⊥) (hp : ((I ^ k).map (intMap φ F h)).IsPrincipal) :
    ∃ (K : IntermediateField ℚ ℂ) (hFK : F ≤ K), Sz K (a + Real.log k) (b + Real.log k) ∧
      (I.map (intMap φ K fun x => hFK (h x))).IsPrincipal := by
  obtain ⟨y, hy⟩ := hp
  have hy' : (I ^ k).map (intMap φ F h) = Ideal.span {y} := hy
  have hy0 : y ≠ 0 := by
    rintro rfl
    rw [Ideal.span_singleton_zero, Ideal.map_eq_bot_iff_of_injective (intMap_injective φ F h)] at hy'
    exact pow_ne_zero k hI hy'
  have hyF : (y : F) ≠ 0 := fun h0 => hy0 (RingOfIntegers.ext h0)
  obtain ⟨z, hz⟩ := IsAlgClosed.exists_pow_nat_eq ((y : F) : ℂ) hk
  have hS := _root_.GlobalTheory.FieldSize.sz_sup_adjoin_root F a b k (y : F) (IsLocalization.coeSubmodule F (I.map (intMap φ F h))) z hF hk hyF
    (by rw [← coeSubmodule_pow, ← Ideal.map_pow, hy', IsLocalization.coeSubmodule_span_singleton]) hz
  have hzK : z ∈ F ⊔ ℚ⟮z⟯ := (le_sup_right : ℚ⟮z⟯ ≤ F ⊔ ℚ⟮z⟯) (IntermediateField.mem_adjoin_simple_self ℚ z)
  have hFK : F ≤ F ⊔ ℚ⟮z⟯ := le_sup_left
  generalize F ⊔ ℚ⟮z⟯ = K at hS hzK hFK
  refine ⟨K, hFK, hS, ?_⟩
  haveI := finiteDimensional_of_sz hS
  haveI : NumberField K := NumberField.mk
  rw [← IsFractionRing.coeSubmodule_isPrincipal (𝓞 K) K]
  have hz0 : z ≠ 0 := by
    rintro rfl
    rw [zero_pow hk.ne'] at hz
    exact hyF (by exact_mod_cast hz.symm)
  refine ⟨⟨z, hzK⟩, GlobalTheory.submodule_eq_span_of_pow_eq_span_pow K _ ⟨z, hzK⟩ k hk
    (fun h0 => hz0 (congrArg Subtype.val h0)) ?_ ?_⟩
  · exact (IsLocalization.coeSubmodule_fg K (RingOfIntegers.coe_injective) _).mpr (IsNoetherian.noetherian _)
  · rw [← coeSubmodule_pow, ← Ideal.map_pow, map_intMap φ hFK h, hy', Ideal.map_span, Set.image_singleton,
      IsLocalization.coeSubmodule_span_singleton]
    congr 2
    apply Subtype.ext
    exact hz.symm

end GlobalTheory.FieldSize.Capit

namespace GlobalTheory.FieldSize


end GlobalTheory.FieldSize
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.HeightProofs.ExistsIsArchimedeanAdeleChartOfRealChart
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Matrix GlobalTheory.FockCompare GlobalTheory.IndefiniteRowSideFullHecke.FockOrthogonalDecomposition
open scoped TensorProduct ContDiff ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.FockCompare.RealChart

theorem tensor_span {F E M : Type} [Field F] [Field E] [Algebra F E] [AddCommGroup M] [Module F M] (δ : E)
    (h : ∀ x : E, ∃ u v : F, x = u • (1 : E) + v • δ) (a : M ⊗[F] E) :
    ∃ a₀ a₁ : M, a = a₀ ⊗ₜ[F] (1 : E) + a₁ ⊗ₜ[F] δ := by
  induction a using TensorProduct.induction_on with
  | zero => exact ⟨0, 0, by simp⟩
  | tmul m x =>
    obtain ⟨u, v, rfl⟩ := h x
    exact ⟨u • m, v • m, by simp only [TensorProduct.tmul_add, TensorProduct.smul_tmul]⟩
  | add a b ha hb =>
    obtain ⟨a₀, a₁, rfl⟩ := ha
    obtain ⟨b₀, b₁, rfl⟩ := hb
    exact ⟨a₀ + b₀, a₁ + b₁, by simp only [TensorProduct.add_tmul]; abel⟩

theorem zero_tmul_add {F E M : Type} [Field F] [Field E] [Algebra F E] [CommRing M] [Algebra F M] (x y : E) :
    (0 : M) ⊗ₜ[F] x + (0 : M) ⊗ₜ[F] y = 0 := by simp

theorem tensor_prod_ext {F E R A B : Type} [Field F] [Field E] [Algebra F E] [CommRing R] [CommRing A] [CommRing B]
    [Algebra F R] [Algebra F A] [Algebra F B] (p : R →ₐ[F] A) (q : R →ₐ[F] B) (i : A →ₗ[F] R) (j : B →ₗ[F] R)
    (h : ∀ x, i (p x) + j (q x) = x) (a : R ⊗[F] E)
    (h1 : Algebra.TensorProduct.map p (AlgHom.id F E) a = 0)
    (h2 : Algebra.TensorProduct.map q (AlgHom.id F E) a = 0) : a = 0 := by
  have key : ∀ a : R ⊗[F] E,
      a = i.rTensor E (Algebra.TensorProduct.map p (AlgHom.id F E) a) +
        j.rTensor E (Algebra.TensorProduct.map q (AlgHom.id F E) a) := by
    intro a
    induction a using TensorProduct.induction_on with
    | zero => simp
    | tmul m x => simp [← TensorProduct.add_tmul, h]
    | add a b ha hb =>
      simp only [map_add (f := _)]
      rw [add_add_add_comm, ← ha, ← hb]
  rw [key a, h1, h2]; simp

theorem adele_tensor_ext {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E] (a : AF F ⊗[F] E)
    (h1 : Algebra.TensorProduct.map (fstA F) (AlgHom.id F E) a = 0)
    (h2 : Algebra.TensorProduct.map (sndA F) (AlgHom.id F E) a = 0) : a = 0 :=
  tensor_prod_ext (fstA F) (sndA F) (LinearMap.inl F (Ainf F) (Af F)) (LinearMap.inr F (Ainf F) (Af F))
    (fun x => Prod.ext (add_zero x.1) (zero_add x.2)) a h1 h2

theorem star_sqrtMinusD (D : D7) : star D.host.sqrtMinusD = -D.host.sqrtMinusD := by
  apply D.host.φ₀.injective
  have h1 : D.host.φ₀ D.host.sqrtMinusD = Complex.I * (Real.sqrt D.host.d : ℂ) := D.host.φ₀_mem
  have := D.host.isCMField_hostE
  have h2 : D.host.φ₀ (star D.host.sqrtMinusD) = starRingEnd ℂ (D.host.φ₀ D.host.sqrtMinusD) :=
    NumberField.IsCMField.complexEmbedding_complexConj D.host.E D.host.φ₀ D.host.sqrtMinusD
  rw [h2, map_neg, h1]
  simp

theorem sqrt_d_pos (D : D7) : 0 < Real.sqrt D.host.d :=
  Real.sqrt_pos.2 (Nat.cast_pos.2 (Nat.pos_of_ne_zero D.host.hyp.2.1.ne_zero))

theorem sqrtMinusD_ne (D : D7) : D.host.sqrtMinusD ≠ 0 := by
  intro h
  have h1 : D.host.φ₀ D.host.sqrtMinusD = Complex.I * (Real.sqrt D.host.d : ℂ) := D.host.φ₀_mem
  rw [h, map_zero] at h1
  have := congrArg Complex.im h1
  have h2 := sqrt_d_pos D
  simp only [Complex.zero_im, Complex.mul_im, Complex.I_re, Complex.ofReal_im, Complex.I_im, Complex.ofReal_re] at this
  linarith

theorem host_span (D : D7) (x : D.host.E) :
    ∃ u v : D.host.F, x = u • (1 : D.host.E) + v • D.host.sqrtMinusD := by
  have hδ := sqrtMinusD_ne D
  have h2 : star (2 : D.host.E) = 2 := by
    have := star_natCast (R := D.host.E) 2
    exact_mod_cast this
  obtain ⟨u, hu⟩ := (D.sp.cm.fixed ((x + star x) / 2)).1 (by
    show star ((x + star x) / 2) = _
    rw [star_div₀, star_add, star_star, h2, add_comm])
  obtain ⟨v, hv⟩ := (D.sp.cm.fixed ((x - star x) / (2 * D.host.sqrtMinusD))).1 (by
    show star ((x - star x) / (2 * D.host.sqrtMinusD)) = _
    rw [star_div₀, star_sub, star_star, star_mul', h2, star_sqrtMinusD]
    field_simp
    ring)
  refine ⟨u, v, ?_⟩
  rw [Algebra.smul_def, Algebra.smul_def]
  erw [hu, hv]
  field_simp
  ring

variable {D : D7} {θ : InfFam D}

theorem comp_tmul (hθ : IsInfFam θ) (τ : D.what₂.Tau) (a : Ainf D.host.F) (y : D.host.E) :
    θ τ (a ⊗ₜ[D.host.F] y) = θ τ (a ⊗ₜ[D.host.F] (1 : D.host.E)) * tauE D τ y := by
  rw [← (hθ τ).1, ← map_mul, Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]

def emb (D : D7) (e : D.host.E) : Ainf D.host.F →+ AE D where
  toFun a := pairA D.host.F a 0 ⊗ₜ[D.host.F] e
  map_zero' := TensorProduct.zero_tmul _ _
  map_add' a b := by
    rw [← TensorProduct.add_tmul]
    congr 1
    exact Prod.ext rfl (add_zero _).symm

theorem continuous_emb (e : D.host.E) : Continuous (emb D e) := by
  have h1 : Continuous fun a : Ainf D.host.F => pairA D.host.F a 0 :=
    Continuous.prodMk continuous_id continuous_const
  have h2 : Continuous fun a : AF D.host.F => a • ((1 : AF D.host.F) ⊗ₜ[D.host.F] e : AE D) :=
    continuous_smul.comp (continuous_id.prodMk continuous_const)
  refine (h2.comp h1).congr fun a => ?_
  show pairA D.host.F a 0 • ((1 : AF D.host.F) ⊗ₜ[D.host.F] e : AE D) = pairA D.host.F a 0 ⊗ₜ[D.host.F] e
  rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]

theorem finPart_emb (e : D.host.E) (a : Ainf D.host.F) : finPart D (emb D e a) = 0 :=
  TensorProduct.zero_tmul _ e

theorem infPart_emb (e : D.host.E) (a : Ainf D.host.F) : infPart D (emb D e a) = a ⊗ₜ[D.host.F] e := rfl

def reP (ι : Type) : (ι → ℂ) →+ (ι → ℝ) where
  toFun z i := (z i).re
  map_zero' := rfl
  map_add' _ _ := rfl

def imaginary (ι : Type) (c : ℝ) : (ι → ℂ) →+ (ι → ℝ) where
  toFun z i := (z i).im / c
  map_zero' := by funext i; simp
  map_add' x y := by funext i; simp [add_div]

theorem exists_chart : ∀ (D : D7) (θ : InfFam D), IsInfFam θ → ∀ ρ : (D.what₂.Tau → ℝ) →+ Ainf D.host.F, Continuous ρ → (∀ x τ, θ τ (ρ x ⊗ₜ[D.host.F] (1 : D.host.E)) = (x τ : ℂ)) → (∀ a : Ainf D.host.F, (∀ τ, θ τ (a ⊗ₜ[D.host.F] (1 : D.host.E)) = 0) → a = 0) → ∃ σ : (D.what₂.Tau → ℂ) →+ AE D, Chart θ σ := by
  intro D θ hθ ρ hρ h1 h0
  have hd := sqrt_d_pos D
  let σ : (D.what₂.Tau → ℂ) →+ AE D :=
    { toFun := fun z => emb D 1 (ρ (reP _ z)) + emb D D.host.sqrtMinusD (ρ (imaginary _ (Real.sqrt D.host.d) z))
      map_zero' := by rw [(reP _).map_zero, (imaginary _ _).map_zero, ρ.map_zero, (emb D _).map_zero, (emb D _).map_zero, add_zero]
      map_add' := fun x y => by
        rw [(reP _).map_add, (imaginary _ _).map_add, ρ.map_add, ρ.map_add, (emb D _).map_add, (emb D _).map_add,
          add_add_add_comm] }
  have hσ : ∀ z, σ z = emb D 1 (ρ (reP _ z)) + emb D D.host.sqrtMinusD (ρ (imaginary _ (Real.sqrt D.host.d) z)) :=
    fun _ => rfl
  refine ⟨σ, hθ, ?_, fun z => ?_, fun z τ => ?_, fun a hf hi => ?_⟩
  · have c1 : Continuous (reP D.what₂.Tau) :=
      continuous_pi fun τ => Complex.continuous_re.comp (continuous_apply τ)
    have c2 : Continuous (imaginary D.what₂.Tau (Real.sqrt D.host.d)) :=
      continuous_pi fun τ => (Complex.continuous_im.comp (continuous_apply τ)).div_const _
    exact ((continuous_emb _).comp (hρ.comp c1)).add ((continuous_emb _).comp (hρ.comp c2))
  · rw [hσ, RingHom.map_add (f := _), finPart_emb, finPart_emb, add_zero]
  · rw [hσ, RingHom.map_add (f := _), infPart_emb, infPart_emb, RingHom.map_add (f := _), comp_tmul hθ τ _ D.host.sqrtMinusD, h1, h1,
      tauE_sqrtMinusD]
    show ((z τ).re : ℂ) + (((z τ).im / Real.sqrt D.host.d : ℝ) : ℂ) * _ = _
    have h2 : ((Real.sqrt D.host.d : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hd.ne'
    rw [Complex.ofReal_div, mul_comm Complex.I, ← mul_assoc, div_mul_cancel₀ _ h2, Complex.re_add_im]
  · obtain ⟨b₀, b₁, hb⟩ := tensor_span D.host.sqrtMinusD (host_span D) (infPart D a)
    have key : ∀ τ, θ τ (b₀ ⊗ₜ[D.host.F] (1 : D.host.E)) = 0 ∧ θ τ (b₁ ⊗ₜ[D.host.F] (1 : D.host.E)) = 0 := by
      intro τ
      have e := hi τ
      rw [hb, RingHom.map_add (f := _), comp_tmul hθ τ _ D.host.sqrtMinusD, tauE_sqrtMinusD] at e
      have r0 := Complex.conj_eq_iff_im.1 (conj_tmul_one hθ τ b₀)
      have r1 := Complex.conj_eq_iff_im.1 (conj_tmul_one hθ τ b₁)
      generalize θ τ (b₀ ⊗ₜ[D.host.F] (1 : D.host.E)) = p at *
      generalize θ τ (b₁ ⊗ₜ[D.host.F] (1 : D.host.E)) = q at *
      generalize Real.sqrt D.host.d = s at *
      have e1 := congrArg Complex.re e
      have e2 := congrArg Complex.im e
      simp [r0, r1, hd.ne'] at e1 e2
      exact ⟨Complex.ext e1 r0, Complex.ext e2 r1⟩
    have z0 := h0 b₀ fun τ => (key τ).1
    have z1 := h0 b₁ fun τ => (key τ).2
    rw [z0, z1] at hb
    exact adele_tensor_ext a (hb.trans (zero_tmul_add _ _)) hf

end GlobalTheory.FockCompare.RealChart

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.HeightProofs.ExistsPosNatMemOpenAdeleSubgroup
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Matrix GlobalTheory.FockCompare GlobalTheory.IndefiniteRowSideFullHecke.FockOrthogonalDecomposition
open scoped TensorProduct ContDiff ComplexOrder
open NumberField IsDedekindDomain Filter Topology

namespace GlobalTheory.AdelicFactorial

theorem tendsto_factorial_adicCompletion (F : Type) [Field F] [NumberField F]
    (v : HeightOneSpectrum (𝓞 F)) :
    Tendsto (fun n : ℕ => ((n.factorial : ℕ) : v.adicCompletion F)) atTop (𝓝 0) := by
  have hle : ∀ m : ℕ, ‖(m : v.adicCompletion F)‖ ≤ 1 := fun m => by
    have := FinitePlace.norm_le_one F v (m : 𝓞 F)
    simpa using this
  set M := Ideal.absNorm v.asIdeal with hM
  have hlt : ‖(M : v.adicCompletion F)‖ < 1 := by
    have := (FinitePlace.norm_lt_one_iff_mem F v (M : 𝓞 F)).2 (Ideal.absNorm_mem _)
    simpa using this
  have hM0 : 0 < M := lt_trans one_pos (NumberField.HeightOneSpectrum.one_lt_absNorm v)
  rw [Metric.tendsto_atTop]
  intro ε hε
  obtain ⟨k, hk⟩ := exists_pow_lt_of_lt_one hε hlt
  refine ⟨M ^ k, fun n hn => ?_⟩
  obtain ⟨c, hc⟩ := Nat.dvd_factorial (pow_pos hM0 k) hn
  rw [dist_zero_right, hc, Nat.cast_mul, Nat.cast_pow, norm_mul, norm_pow]
  exact lt_of_le_of_lt (mul_le_of_le_one_right (by positivity) (hle c)) hk

theorem tendsto_factorial_finiteAdele (F : Type) [Field F] [NumberField F] :
    Tendsto (fun n : ℕ => ((n.factorial : ℕ) : FiniteAdeleRing (𝓞 F) F)) atTop (𝓝 0) := by
  have h1 : Tendsto (fun n : ℕ => fun v : HeightOneSpectrum (𝓞 F) =>
      ((n.factorial : ℕ) : v.adicCompletionIntegers F)) atTop (𝓝 0) := by
    refine tendsto_pi_nhds.2 fun v => ?_
    rw [tendsto_subtype_rng]
    simpa using tendsto_factorial_adicCompletion F v
  have h2 := ((RestrictedProduct.isEmbedding_structureMap
    (R := fun v : HeightOneSpectrum (𝓞 F) => v.adicCompletion F)
    (A := fun v : HeightOneSpectrum (𝓞 F) => (v.adicCompletionIntegers F : Set (v.adicCompletion F)))
    (𝓕 := cofinite)).continuous.tendsto _).comp h1
  exact h2

theorem exists_nat_mem_of_isOpen : ∀ (F : Type) [Field F] [NumberField F] (U : AddSubgroup (AF F)),
    IsOpen (U : Set (AF F)) → ∃ N : ℕ, 0 < N ∧ pairA F 0 (N : Af F) ∈ U := by
  intro F _ _ U hU
  have h : Tendsto (fun n : ℕ => pairA F 0 ((n.factorial : ℕ) : Af F)) atTop (𝓝 (0 : AF F)) :=
    (tendsto_const_nhds (x := (0 : Ainf F))).prodMk_nhds (tendsto_factorial_finiteAdele F)
  obtain ⟨n, hn⟩ := (h.eventually (hU.mem_nhds U.zero_mem)).exists
  exact ⟨n.factorial, n.factorial_pos, hn⟩

end GlobalTheory.AdelicFactorial
end

-- bundled from Development.AbelianVarietyTheory.Proofs.HeightProofs.ExistsRealChartInfiniteAdelesCmType
section
noncomputable section

namespace GlobalTheory.FockCompare

section General

open NumberField GlobalTheory.InfAdeleCM
open scoped TensorProduct

theorem exists_real_chart_general {F : Type} [Field F] [NumberField F] [IsTotallyReal F] {I : Type}
    (σ : I → (F →+* ℂ)) (hb : Function.Bijective fun i => InfinitePlace.mk (σ i)) :
    ∃ ρ : (I → ℝ) →+ InfiniteAdeleRing F, Continuous ρ ∧ (∀ x i, ext (σ i) (ρ x) = (x i : ℂ)) ∧
      ∀ a : InfiniteAdeleRing F, (∀ i, ext (σ i) a = 0) → a = 0 := by
  let e : I ≃ InfinitePlace F := Equiv.ofBijective _ hb
  let r : ∀ v : InfinitePlace F, v.Completion ≃+* ℝ := fun v =>
    InfinitePlace.Completion.ringEquivRealOfIsReal (IsTotallyReal.isReal v)
  have hr : ∀ v, Continuous (r v).symm := fun v =>
    (InfinitePlace.Completion.isometryEquivRealOfIsReal (IsTotallyReal.isReal v)).symm.continuous
  refine ⟨{ toFun := fun x v => (r v).symm (x (e.symm v))
            map_zero' := funext fun v => map_zero (r v).symm
            map_add' := fun x y => funext fun v => map_add (r v).symm _ _ }, ?_, ?_, ?_⟩
  · exact continuous_pi fun v => (hr v).comp (continuous_apply _)
  · intro x i
    rw [ext_eq_ofReal]
    congr 1
    have h := (r (e i)).apply_symm_apply (x (e.symm (e i)))
    refine Eq.trans h ?_
    rw [e.symm_apply_apply]
  · intro a ha
    funext v
    obtain ⟨i, rfl⟩ := hb.2 v
    exact (InfinitePlace.Completion.extensionEmbedding _).injective ((ha i).trans (map_zero _).symm)

end General

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Matrix GlobalTheory.FockCompare GlobalTheory.IndefiniteRowSideFullHecke.FockOrthogonalDecomposition
open scoped TensorProduct ContDiff ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem exists_real_chart : ∀ (D : D7) (θ : InfFam D), IsInfFam θ → (Function.Bijective fun τ : D.what₂.Tau => NumberField.InfinitePlace.mk ((tauE D τ).comp (algebraMap D.host.F D.host.E))) → ∃ ρ : (D.what₂.Tau → ℝ) →+ Ainf D.host.F, Continuous ρ ∧ (∀ x τ, θ τ (ρ x ⊗ₜ[D.host.F] (1 : D.host.E)) = (x τ : ℂ)) ∧ ∀ a : Ainf D.host.F, (∀ τ, θ τ (a ⊗ₜ[D.host.F] (1 : D.host.E)) = 0) → a = 0 := by
  intro D θ hθ hb
  haveI := D.sp.cm.totReal
  obtain ⟨ρ, h1, h2, h3⟩ := exists_real_chart_general (F := D.host.F)
    (fun τ : D.what₂.Tau => (tauE D τ).comp (algebraMap D.host.F D.host.E)) hb
  have key : ∀ τ (a : Ainf D.host.F), θ τ (a ⊗ₜ[D.host.F] (1 : D.host.E)) =
      GlobalTheory.InfAdeleCM.ext ((tauE D τ).comp (algebraMap D.host.F D.host.E)) a := fun τ a => by
    have := GlobalTheory.InfAdeleCM.hom_tmul (tauE D τ) (θ τ) (hθ τ).1 (hθ τ).2 a 1
    rw [RingHom.map_one, mul_one] at this
    exact this
  exact ⟨ρ, h1, fun x τ => (key τ _).trans (h2 x τ), fun a ha => h3 a fun τ => (key τ a).symm.trans (ha τ)⟩

end GlobalTheory.FockCompare

end
end

