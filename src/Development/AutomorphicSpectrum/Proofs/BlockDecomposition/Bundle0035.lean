module

public import Mathlib
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ThetaCellCovers.KernelL2RowsColumns
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.AcrisKummerUnits.Splits
public import Development.WeilBound.RepresentationTheoryGL.CasimirAlgebra.KugaCoordinates.KugaAbsoluteValues.KSumApply
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.WittExactSequences.Bundle0001
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0010
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0017
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.AesmIteratedDerivReal

@[expose] public section

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.InnerEqIntegralConjMul
section
noncomputable section

open MeasureTheory PositivityTheory.Rg.BcB.E1
open scoped ENNReal ComplexConjugate

namespace GlobalTheory.CompanionTheory.KerAdj

theorem pairing_swap {α : Type*} [MeasurableSpace α] {ν : Measure α} [SFinite ν]
    (k : α → α → ℂ) (g f : α → ℂ)
    (h : Integrable (fun p : α × α => conj (g p.1) * k p.1 p.2 * f p.2) (ν.prod ν)) :
    Integrable (fun x => conj (∫ y, conj (k y x) * g y ∂ν) * f x) ν ∧
    Integrable (fun y => conj (g y) * ∫ x, k y x * f x ∂ν) ν ∧
    ∫ x, conj (∫ y, conj (k y x) * g y ∂ν) * f x ∂ν
      = ∫ y, conj (g y) * ∫ x, k y x * f x ∂ν ∂ν := by
  have hL : ∀ x, conj (∫ y, conj (k y x) * g y ∂ν) * f x
      = ∫ y, conj (g y) * k y x * f x ∂ν := by
    intro x
    rw [← integral_conj, ← integral_mul_const]
    refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
    simp only [map_mul, Complex.conj_conj]
    ring
  have hR : ∀ y, conj (g y) * ∫ x, k y x * f x ∂ν
      = ∫ x, conj (g y) * k y x * f x ∂ν := by
    intro y
    rw [← integral_const_mul]
    refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    simp only [mul_assoc]
  refine ⟨?_, ?_, ?_⟩
  · simp_rw [hL]
    exact h.swap.integral_prod_left
  · simp_rw [hR]
    exact h.integral_prod_left
  · simp_rw [hL, hR]
    exact (integral_integral_swap (f := fun y x => conj (g y) * k y x * f x) h).symm

theorem inner_eq_integral_conj_mul {α : Type*} [MeasurableSpace α] {ν : Measure α} (u v : Lp ℂ 2 ν) :
    inner ℂ u v = ∫ x, conj ((u : α → ℂ) x) * (v : α → ℂ) x ∂ν := by
  rw [L2.inner_def]
  refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
  simp [mul_comm]

theorem entry_pairing (hK : KerBasic) (hR : RowInt) (hS : SchurInt) (X : Ctx) (φ : X.G → ℂ)
    (hφ : Tst φ) (g f : Lp ℂ 2 X.ν) :
    Integrable (fun x => conj (∫ y, ker X.Γ (adj φ) x y * (g : X.G → ℂ) y ∂X.ν) * (f : X.G → ℂ) x) X.ν ∧
    Integrable (fun y => conj ((g : X.G → ℂ) y) * ∫ x, ker X.Γ φ y x * (f : X.G → ℂ) x ∂X.ν) X.ν ∧
    ∫ x, conj (∫ y, ker X.Γ (adj φ) x y * (g : X.G → ℂ) y ∂X.ν) * (f : X.G → ℂ) x ∂X.ν
      = ∫ y, conj ((g : X.G → ℂ) y) * ∫ x, ker X.Γ φ y x * (f : X.G → ℂ) x ∂X.ν ∂X.ν := by
  haveI : SFinite X.ν := by unfold Ctx.ν; infer_instance
  obtain ⟨-, hc, -, -, hadj, -⟩ := hK X φ hφ
  obtain ⟨A, hA, h1, h2⟩ := hR X φ hφ
  have hg : MemLp (fun y => conj ((g : X.G → ℂ) y)) 2 X.ν := (Lp.memLp g).star
  have hI := hS X.G X.ν (ker X.Γ φ) A hc.measurable hA h1 h2 _ _ hg (Lp.memLp f)
  have := pairing_swap (ν := X.ν) (ker X.Γ φ) (g : X.G → ℂ) (f : X.G → ℂ) hI
  simpa only [hadj] using this

theorem opAdj_of : KerBasic → RowInt → SchurInt → OpExA → OpAdj := by
  intro hK hR hS hE X ι _ Φ T hΦ hT
  have hadj : ∀ i j, Tst (adj (Φ j i)) := fun i j => (hK X _ (hΦ j i)).2.2.2.1
  obtain ⟨T', hT', -⟩ := hE X ι (fun i j => adj (Φ j i)) hadj
  have hEq : T' = ContinuousLinearMap.adjoint T := by
    rw [ContinuousLinearMap.eq_adjoint_iff]
    intro g f
    have key := fun i j => entry_pairing hK hR hS X (Φ j i) (hΦ j i) (g j) (f i)
    have hl : ∀ i, inner ℂ (T' g i) (f i)
        = ∑ j, ∫ x, conj (∫ y, ker X.Γ (adj (Φ j i)) x y * (g j : X.G → ℂ) y ∂X.ν)
            * (f i : X.G → ℂ) x ∂X.ν := by
      intro i
      rw [inner_eq_integral_conj_mul, ← MeasureTheory.integral_finsetSum _ fun j _ => (key i j).1]
      refine integral_congr_ae ?_
      filter_upwards [hT' g i] with x hx
      set_option synthInstance.maxHeartbeats 100000 in
        rw [hx, map_sum, Finset.sum_mul]
    have hr : ∀ j, inner ℂ (g j) (T f j)
        = ∑ i, ∫ y, conj ((g j : X.G → ℂ) y)
            * ∫ x, ker X.Γ (Φ j i) y x * (f i : X.G → ℂ) x ∂X.ν ∂X.ν := by
      intro j
      rw [inner_eq_integral_conj_mul, ← MeasureTheory.integral_finsetSum _ fun i _ => (key i j).2.1]
      refine integral_congr_ae ?_
      filter_upwards [hT f j] with y hy
      rw [hy, Finset.mul_sum]
    rw [PiLp.inner_apply, PiLp.inner_apply]
    simp_rw [hl, hr]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun i _ => (key i j).2.2
  rw [← hEq]
  exact hT'

end GlobalTheory.CompanionTheory.KerAdj

end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IntegrableReflect
section
noncomputable section

open MeasureTheory
open scoped Pointwise
open PositivityTheory.Rg.BcB.E1

namespace GlobalTheory.CompanionTheory.ConvTest

variable (X : Ctx)

theorem support_cv_subset (φ ψ : X.G → ℂ) :
    Function.support (cv X.μ φ ψ) ⊆ tsupport φ * tsupport ψ := by
  intro y hy
  by_contra hmem
  apply hy
  have hz : ∀ z : X.G, φ z * ψ (z⁻¹ * y) = 0 := by
    intro z
    by_contra hne
    have h1 : φ z ≠ 0 := left_ne_zero_of_mul hne
    have h2 : ψ (z⁻¹ * y) ≠ 0 := right_ne_zero_of_mul hne
    apply hmem
    refine Set.mem_mul.2 ⟨z, subset_tsupport _ h1, z⁻¹ * y, subset_tsupport _ h2, ?_⟩
    group
  simp [cv, hz]

theorem continuous_cv {φ ψ : X.G → ℂ} (hφ : Tst φ) (hψ : Tst ψ) : Continuous (cv X.μ φ ψ) := by
  have hK : IsCompact (tsupport φ) := hφ.2
  have hEq : cv X.μ φ ψ = fun y => ∫ z in tsupport φ, φ z * ψ (z⁻¹ * y) ∂X.μ := by
    funext y
    refine (setIntegral_eq_integral_of_forall_compl_eq_zero ?_).symm
    intro z hz
    simp [image_eq_zero_of_notMem_tsupport hz]
  rw [hEq]
  refine continuous_parametric_integral_of_continuous
    (f := fun (y z : X.G) => φ z * ψ (z⁻¹ * y)) ?_ hK
  have h1 : Continuous fun p : X.G × X.G => φ p.2 := hφ.1.comp continuous_snd
  have h2 : Continuous fun p : X.G × X.G => ψ (p.2⁻¹ * p.1) :=
    hψ.1.comp (continuous_snd.inv.mul continuous_fst)
  exact h1.mul h2

theorem integrable_reflect {ψ : X.G → ℂ} (hψ : Tst ψ) (y : X.G) :
    Integrable (fun z => ‖ψ (z⁻¹ * y)‖) X.μ := by
  have hc : Continuous fun z : X.G => ψ (z⁻¹ * y) :=
    hψ.1.comp (continuous_inv.mul continuous_const)
  have hs : HasCompactSupport fun z : X.G => ψ (z⁻¹ * y) :=
    hψ.2.comp_homeomorph ((Homeomorph.inv X.G).trans (Homeomorph.mulRight y))
  exact (hc.integrable_of_hasCompactSupport hs).norm

theorem norm_cv_le {φ ψ : X.G → ℂ} (hψ : Tst ψ) (B : ℝ) (hB : ∀ z, ‖φ z‖ ≤ B) (y : X.G) :
    ‖cv X.μ φ ψ y‖ ≤ B * ∫ z, ‖ψ z⁻¹‖ ∂X.μ := by
  have hB0 : 0 ≤ B := (norm_nonneg _).trans (hB 1)
  have hshift : ∫ z, ‖ψ (z⁻¹ * y)‖ ∂X.μ = ∫ z, ‖ψ z⁻¹‖ ∂X.μ := by
    have h := integral_mul_left_eq_self (μ := X.μ) (fun z => ‖ψ z⁻¹‖) y⁻¹
    simpa [mul_inv_rev] using h
  have hle : ‖cv X.μ φ ψ y‖ ≤ ∫ z, B * ‖ψ (z⁻¹ * y)‖ ∂X.μ := by
    refine norm_integral_le_of_norm_le ((integrable_reflect X hψ y).const_mul B) ?_
    refine Filter.Eventually.of_forall fun z => ?_
    rw [norm_mul]
    exact mul_le_mul_of_nonneg_right (hB z) (norm_nonneg _)
  rw [integral_const_mul, hshift] at hle
  exact hle

theorem cvTest : CvTest := by
  intro X φ ψ hφ hψ
  have hsupp := support_cv_subset X φ ψ
  refine ⟨⟨continuous_cv X hφ hψ, ?_⟩, hsupp, fun B hB y => norm_cv_le X hψ B hB y⟩
  have hK : IsCompact (tsupport φ * tsupport ψ) := IsCompact.mul hφ.2 hψ.2
  refine HasCompactSupport.intro hK fun y hy => ?_
  by_contra hne
  exact hy (hsupp hne)

end GlobalTheory.CompanionTheory.ConvTest

end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IntegralLocalizationAwayInRing
section
open CategoryTheory AlgebraicGeometry CrystallineSemistableComparison CrystallineSemistableComparison.R

namespace GlobalTheory.CompanionTheory.ValIntClosed

theorem exists_eq_of_isIntegral : ∀ {S : Type} [CommRing S] (ϖ : S), ϖ ∈ nonZeroDivisors S → Val ϖ →
    ∀ x : Localization.Away ϖ, IsIntegral S x → ∃ y : S, algebraMap S (Localization.Away ϖ) y = x := by
  intro S _ ϖ hϖ hV x hx
  obtain ⟨P, hm, hP⟩ := hx
  obtain ⟨N, f, hf⟩ := IsLocalization.Away.surj ϖ x
  set a := algebraMap S (Localization.Away ϖ) with ha
  have hinj : Function.Injective a :=
    IsLocalization.injective (Localization.Away ϖ) (Submonoid.powers_le.2 hϖ)
  have hwnz : ϖ ^ N ∈ nonZeroDivisors S := pow_mem hϖ N
  have hwu : IsUnit (a (ϖ ^ N)) := by
    rw [map_pow]
    exact (IsLocalization.Away.algebraMap_isUnit ϖ).pow N
  obtain ⟨e, he, ⟨b, hb⟩, ⟨h, hh⟩⟩ := (by
    obtain ⟨e, he, h1, h2⟩ := hV f (ϖ ^ N) ⟨N, Ideal.subset_span (by simp)⟩
    exact ⟨e, he, Ideal.mem_span_singleton.1 h1, Ideal.mem_span_singleton.1 h2⟩ :
      ∃ e : S, IsIdempotentElem e ∧ ϖ ^ N ∣ e * f ∧ f ∣ (1 - e) * ϖ ^ N)
  set u := 1 - e with hu
  have hui : IsIdempotentElem u := he.one_sub
  set d := P.natDegree with hd

  have hhx : a h * x = a u := by
    apply hwu.mul_left_cancel
    calc a (ϖ ^ N) * (a h * x) = a h * (x * a (ϖ ^ N)) := by ring
      _ = a h * a f := by rw [map_pow, hf]
      _ = a u * a (ϖ ^ N) := by rw [← map_mul, ← map_mul, hh]; ring_nf
      _ = a (ϖ ^ N) * a u := by ring
  have hUi : a u * a u = a u := by rw [← map_mul, hui.eq]
  have hUp : ∀ i : ℕ, a u * a u ^ i = a u := by
    intro i
    induction i with
    | zero => simp
    | succ n ih => rw [pow_succ, ← mul_assoc, ih, hUi]
  set k : S := ∑ i ∈ Finset.range d, P.coeff i * h ^ (d - 1 - i) with hk
  have hrel : a (u * (1 + h * k)) = 0 := by
    have h0 : a u * a h ^ d * Polynomial.eval₂ a x P = 0 := by
      have : Polynomial.eval₂ a x P = 0 := hP
      rw [this, mul_zero]
    rw [Polynomial.eval₂_eq_sum_range, Finset.sum_range_succ, mul_add, Finset.mul_sum] at h0
    have hlead : P.coeff d = 1 := hm
    have t1 : a u * a h ^ d * (a (P.coeff d) * x ^ d) = a u := by
      rw [hlead, map_one, one_mul, mul_assoc, ← mul_pow, hhx, hUp]
    have t2 : ∀ i ∈ Finset.range d, a u * a h ^ d * (a (P.coeff i) * x ^ i)
        = a u * (a h * a (P.coeff i * h ^ (d - 1 - i))) := by
      intro i hi
      have hi' : i < d := Finset.mem_range.1 hi
      have hd' : d = i + (1 + (d - 1 - i)) := by omega
      have : a h ^ d = a h ^ i * (a h * a h ^ (d - 1 - i)) := by
        conv_lhs => rw [hd', pow_add, pow_add, pow_one]
      rw [this]
      calc a u * (a h ^ i * (a h * a h ^ (d - 1 - i))) * (a (P.coeff i) * x ^ i)
          = (a u * (a h * x) ^ i) * (a h * (a (P.coeff i) * a h ^ (d - 1 - i))) := by
            rw [mul_pow]; ring
        _ = a u * (a h * a (P.coeff i * h ^ (d - 1 - i))) := by
            rw [hhx, hUp, map_mul, map_pow]
    rw [t1, Finset.sum_congr rfl t2, ← Finset.mul_sum, ← Finset.mul_sum] at h0
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_mul, map_add (f := _), map_one, map_mul, hk, map_sum]
    rw [mul_add, mul_one, add_comm]
    exact h0
  have hrel' : u * (1 + h * k) = 0 := hinj (by rw [hrel, map_zero])
  have hu' : u = - (u * h * k) := by linear_combination hrel'
  have hdiv : ϖ ^ N ∣ f := by
    have hfe : f = e * f + u * f := by rw [hu]; ring
    have huf : u * f = ϖ ^ N * (-(k * u)) := by
      calc u * f = - (u * h * k) * f := by rw [← hu']
        _ = - (k * u * (f * h)) := by ring
        _ = - (k * u * (u * ϖ ^ N)) := by rw [hh]
        _ = - (k * (u * u) * ϖ ^ N) := by ring
        _ = ϖ ^ N * (-(k * u)) := by rw [hui.eq]; ring
    exact ⟨b + -(k * u), by rw [hfe, hb, huf]; ring⟩
  obtain ⟨y, hy⟩ := hdiv
  refine ⟨y, ?_⟩
  apply hwu.mul_left_cancel
  rw [← map_mul, ← hy, ← hf, map_pow, mul_comm]

end GlobalTheory.CompanionTheory.ValIntClosed
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.InvarianceContraction
section
open PositivityTheory.Rg.Cz Fin Function

namespace GlobalTheory.CompanionTheory.Invsum

theorem invariance_contraction {P : Type} [AddCommGroup P] [Module ℝ P] {M : Type} [AddCommGroup M]
    [Module ℂ M] [Module ℝ M] [IsScalarTower ℝ ℂ M] {β γ : Type} [Fintype β] (b : β → P)
    (D : γ → P →ₗ[ℝ] P) (c : β → β → γ → ℝ) (E : γ → Module.End ℂ M)
    (hanti : ∀ i j k, c j i k = -c i j k) (hD : ∀ k j, D k (b j) = ∑ i, c i j k • b i)
    {q : ℕ} (ω : P [⋀^Fin q]→ₗ[ℝ] M)
    (hinv : ∀ k (Y : Fin q → P), E k (ω Y) = ∑ s, ω (Function.update Y s (D k (Y s))))
    (k : γ) (J : Fin q → β) :
    ∑ s, ∑ i, (c (J s) i k : ℂ) • ω (Function.update (b ∘ J) s (b i)) = -E k (ω (b ∘ J)) := by
  have step : ∀ s, ω (Function.update (b ∘ J) s (D k ((b ∘ J) s))) =
      -∑ i, (c (J s) i k : ℂ) • ω (Function.update (b ∘ J) s (b i)) := by
    intro s
    have e : D k ((b ∘ J) s) = ∑ i, c i (J s) k • b i := hD k (J s)
    have h1 : ω (Function.update (b ∘ J) s (∑ i, c i (J s) k • b i)) =
        ∑ i, ω (Function.update (b ∘ J) s (c i (J s) k • b i)) :=
      ω.toMultilinearMap.map_update_sum Finset.univ s (fun i => c i (J s) k • b i) (b ∘ J)
    rw [e, h1, ← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    have h2 : ω (Function.update (b ∘ J) s (c i (J s) k • b i)) =
        c i (J s) k • ω (Function.update (b ∘ J) s (b i)) :=
      ω.map_update_smul (b ∘ J) s (c i (J s) k) (b i)
    have h3 : ((c (J s) i k : ℝ) : ℂ) • ω (Function.update (b ∘ J) s (b i)) =
        c (J s) i k • ω (Function.update (b ∘ J) s (b i)) :=
      algebraMap_smul ℂ (c (J s) i k) (ω (Function.update (b ∘ J) s (b i)))
    rw [h2, h3, hanti (J s) i k, neg_smul]
  rw [hinv k (b ∘ J), Finset.sum_congr rfl fun s _ => step s, Finset.sum_neg_distrib, neg_neg]

end GlobalTheory.CompanionTheory.Invsum
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsComplExistsUnique
section
open TensorProduct CrystallineSemistableComparison.D
open scoped LaurentPolynomial

namespace GlobalTheory.CompanionTheory.PfCompl

theorem isCompl_existsUnique :
    ∀ (B : Type) [CommRing B] (T : Type) [CommRing T] (π : B) (g : B →+* T), IsCompl π g →
      ∀ (T₁ : Type) [CommRing T₁] (x : B →+* T₁), IsAdicComplete (Ideal.span {x π}) T₁ →
        ∃! ψ : T →+* T₁, ψ.comp g = x := by
  intro B _ T _ π g h T₁ _ x hc
  exact existsUnique_comp_eq π g h.surj h.inj x hc

end GlobalTheory.CompanionTheory.PfCompl
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsComplNonZeroDivisor
section
open TensorProduct CrystallineSemistableComparison.D
open scoped LaurentPolynomial

namespace GlobalTheory.CompanionTheory.ComplReg

theorem isCompl_nonZeroDivisor : ∀ (B : Type) [CommRing B] (T : Type) [CommRing T] (π : B) (g : B →+* T),
    IsCompl π g → π ∈ nonZeroDivisors B → g π ∈ nonZeroDivisors T := by
  intro B _ T _ π g hC hπ
  exact nonZeroDivisor_of_dense_of_strict π g hC.compl.toIsHausdorff hC.surj hC.inj hπ

end GlobalTheory.CompanionTheory.ComplReg
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IteratedDerivIntegralGaussianExponential
section
open MeasureTheory Filter Topology

namespace GlobalTheory.CompanionTheory.HolMean.DilatedGaussian

lemma integrable_gauss_complex :
    Integrable (fun w : ℂ => Real.exp (-Real.pi * ‖w‖ ^ 2)) := by
  have hb : 0 < ((Real.pi : ℂ)).re := by simpa using Real.pi_pos
  have h := (GaussianFourier.integrable_cexp_neg_mul_sq_norm_add (V := ℂ) hb 0 0).norm
  refine h.congr (Filter.Eventually.of_forall fun w => ?_)
  simp only [inner_zero_left, Complex.ofReal_zero, mul_zero, zero_mul, add_zero, Complex.norm_exp]
  rw [← Complex.ofReal_pow, ← Complex.ofReal_neg, ← Complex.ofReal_mul, Complex.ofReal_re]

lemma integrable_gauss (m n : ℕ) :
    Integrable (fun v : Fin m → Fin n → ℂ =>
      Real.exp (-Real.pi * ∑ a, ∑ j, ‖v a j‖ ^ 2)) := by
  have h1 : Integrable (fun u : Fin n → ℂ => ∏ j, Real.exp (-Real.pi * ‖u j‖ ^ 2)) :=
    Integrable.fintype_prod (f := fun (_ : Fin n) (w : ℂ) => Real.exp (-Real.pi * ‖w‖ ^ 2))
      (μ := fun _ => volume) (fun _ => integrable_gauss_complex)
  have h2 : Integrable (fun v : Fin m → Fin n → ℂ => ∏ a, ∏ j, Real.exp (-Real.pi * ‖v a j‖ ^ 2)) :=
    Integrable.fintype_prod (f := fun (_ : Fin m) (u : Fin n → ℂ) => ∏ j, Real.exp (-Real.pi * ‖u j‖ ^ 2))
      (μ := fun _ => volume) (fun _ => h1)
  refine h2.congr (Filter.Eventually.of_forall fun v => ?_)
  simp only [← Real.exp_sum, Finset.mul_sum]

noncomputable def dilated (m n : ℕ) (X : Fin n → ℝ) (v : Fin m → Fin n → ℂ) (z : ℂ) : ℂ :=
  Complex.exp ((m : ℂ) * z * ∑ j, (X j : ℂ)) *
    Complex.exp (-(2 * Real.pi : ℂ) * ∑ a, ∑ j, Complex.exp (2 * z * X j) * ((‖v a j‖ ^ 2 : ℝ) : ℂ))

lemma differentiable_dilated (m n : ℕ) (X : Fin n → ℝ) (v : Fin m → Fin n → ℂ) :
    Differentiable ℂ (dilated m n X v) := by
  unfold dilated
  fun_prop

lemma continuous_dilated (m n : ℕ) (X : Fin n → ℝ) (z : ℂ) :
    Continuous (fun v : Fin m → Fin n → ℂ => dilated m n X v z) := by
  unfold dilated
  first
  | fun_prop
  | exact continuous_const.mul (Continuous.cexp (continuous_const.mul
      (continuous_finset_sum _ fun a _ => continuous_finset_sum _ fun j _ => continuous_const.mul
        (Complex.continuous_ofReal.comp ((continuous_norm.comp ((continuous_apply j).comp (continuous_apply a))).pow 2)))))

lemma eventually_small (m n : ℕ) (X : Fin n → ℝ) :
    ∀ᶠ z : ℂ in 𝓝 0, (∀ j, 1 / 2 ≤ (Complex.exp (2 * z * X j)).re) ∧
      ‖Complex.exp ((m : ℂ) * z * ∑ j, (X j : ℂ))‖ ≤ 2 := by
  have hre : ∀ j, ∀ᶠ z : ℂ in 𝓝 0, 1 / 2 ≤ (Complex.exp (2 * z * X j)).re := by
    intro j
    have hc : Continuous fun z : ℂ => (Complex.exp (2 * z * X j)).re := by fun_prop
    have h0 : (1 / 2 : ℝ) < (Complex.exp (2 * 0 * X j)).re := by norm_num
    exact ((hc.tendsto 0).eventually (lt_mem_nhds h0)).mono fun z hz => hz.le
  have hn : ∀ᶠ z : ℂ in 𝓝 0, ‖Complex.exp ((m : ℂ) * z * ∑ j, (X j : ℂ))‖ ≤ 2 := by
    have hc : Continuous fun z : ℂ => ‖Complex.exp ((m : ℂ) * z * ∑ j, (X j : ℂ))‖ := by fun_prop
    have h0 : ‖Complex.exp ((m : ℂ) * 0 * ∑ j, (X j : ℂ))‖ < 2 := by norm_num
    exact ((hc.tendsto 0).eventually (gt_mem_nhds h0)).mono fun z hz => hz.le
  exact (Filter.eventually_all.2 hre).and hn

lemma norm_dilated_le (m n : ℕ) (X : Fin n → ℝ) (z : ℂ)
    (h1 : ∀ j, 1 / 2 ≤ (Complex.exp (2 * z * X j)).re)
    (h2 : ‖Complex.exp ((m : ℂ) * z * ∑ j, (X j : ℂ))‖ ≤ 2) (v : Fin m → Fin n → ℂ) :
    ‖dilated m n X v z‖ ≤ 2 * Real.exp (-Real.pi * ∑ a, ∑ j, ‖v a j‖ ^ 2) := by
  unfold dilated
  rw [norm_mul]
  have hre : (-(2 * Real.pi : ℂ) * ∑ a, ∑ j, Complex.exp (2 * z * X j) * ((‖v a j‖ ^ 2 : ℝ) : ℂ)).re
      = -(2 * Real.pi) * ∑ a, ∑ j, (Complex.exp (2 * z * X j)).re * ‖v a j‖ ^ 2 := by
    have e : (-(2 * Real.pi : ℂ)) = ((-(2 * Real.pi) : ℝ) : ℂ) := by push_cast; ring
    rw [e, Complex.re_ofReal_mul, Complex.re_sum]
    simp only [Complex.re_sum, Complex.re_mul_ofReal]
  have hS : ∑ a, ∑ j, (1 / 2 : ℝ) * ‖v a j‖ ^ 2 ≤
      ∑ a, ∑ j, (Complex.exp (2 * z * X j)).re * ‖v a j‖ ^ 2 :=
    Finset.sum_le_sum fun a _ => Finset.sum_le_sum fun j _ =>
      mul_le_mul_of_nonneg_right (h1 j) (sq_nonneg _)
  have hT : ∑ a, ∑ j, (1 / 2 : ℝ) * ‖v a j‖ ^ 2 = (1 / 2) * ∑ a, ∑ j, ‖v a j‖ ^ 2 := by
    simp only [Finset.mul_sum]
  have key : -(2 * Real.pi) * ∑ a, ∑ j, (Complex.exp (2 * z * X j)).re * ‖v a j‖ ^ 2 ≤
      -Real.pi * ∑ a, ∑ j, ‖v a j‖ ^ 2 := by
    rw [hT] at hS
    nlinarith [Real.pi_pos]
  refine mul_le_mul h2 ?_ (norm_nonneg _) (by norm_num)
  rw [Complex.norm_exp, hre]
  exact Real.exp_le_exp.2 key

theorem holomorphic_integral (m n : ℕ) (X : Fin n → ℝ) (K : (Fin m → Fin n → ℂ) → ℂ)
    (hK : Continuous K) (hK1 : ∀ v, ‖K v‖ ≤ 1) :
    ∃ ρ : ℝ, 0 < ρ ∧ DifferentiableOn ℂ (fun z : ℂ => ∫ v, K v * (Complex.exp ((m : ℂ) * z * ∑ j, (X j : ℂ)) * Complex.exp (-(2 * Real.pi : ℂ) * ∑ a, ∑ j, Complex.exp (2 * z * X j) * ((‖v a j‖ ^ 2 : ℝ) : ℂ)))) (Metric.ball 0 ρ) ∧ ∀ r : ℕ, iteratedDeriv r (fun z : ℂ => ∫ v, K v * (Complex.exp ((m : ℂ) * z * ∑ j, (X j : ℂ)) * Complex.exp (-(2 * Real.pi : ℂ) * ∑ a, ∑ j, Complex.exp (2 * z * X j) * ((‖v a j‖ ^ 2 : ℝ) : ℂ)))) 0 = ∫ v, K v * iteratedDeriv r (fun z : ℂ => (Complex.exp ((m : ℂ) * z * ∑ j, (X j : ℂ)) * Complex.exp (-(2 * Real.pi : ℂ) * ∑ a, ∑ j, Complex.exp (2 * z * X j) * ((‖v a j‖ ^ 2 : ℝ) : ℂ)))) 0 := by
  have hcm : ∀ (c : ℂ) (f : ℂ → ℂ) (r : ℕ),
      iteratedDeriv r (fun w => c * f w) = fun w => c * iteratedDeriv r f w := by
    intro c f r
    induction r with
    | zero => simp only [iteratedDeriv_zero]
    | succ r ih => rw [iteratedDeriv_succ, ih, deriv_const_mul_field', iteratedDeriv_succ]
  obtain ⟨ρ, hρ, hsmall⟩ := Metric.eventually_nhds_iff_ball.1 (eventually_small m n X)
  have hU : IsOpen (Metric.ball (0 : ℂ) ρ) := Metric.isOpen_ball
  have hd : ∀ v : Fin m → Fin n → ℂ,
      DifferentiableOn ℂ (fun z => K v * dilated m n X v z) (Metric.ball (0 : ℂ) ρ) :=
    fun v => ((differentiable_dilated m n X v).const_mul (K v)).differentiableOn
  have hm : ∀ z ∈ Metric.ball (0 : ℂ) ρ,
      AEStronglyMeasurable (fun v : Fin m → Fin n → ℂ => K v * dilated m n X v z) volume :=
    fun z _ => (hK.mul (continuous_dilated m n X z)).aestronglyMeasurable
  have hb : ∀ z₀ ∈ Metric.ball (0 : ℂ) ρ, ∃ V ∈ 𝓝 z₀, ∃ g : (Fin m → Fin n → ℂ) → ℝ,
      Integrable g volume ∧ ∀ z ∈ V ∩ Metric.ball (0 : ℂ) ρ, ∀ v,
        ‖K v * dilated m n X v z‖ ≤ g v := by
    intro z₀ _
    refine ⟨Set.univ, Filter.univ_mem,
      fun v => 2 * Real.exp (-Real.pi * ∑ a, ∑ j, ‖v a j‖ ^ 2),
      (integrable_gauss m n).const_mul 2, ?_⟩
    intro z hz v
    obtain ⟨h1, h2⟩ := hsmall z hz.2
    rw [norm_mul]
    calc ‖K v‖ * ‖dilated m n X v z‖
        ≤ 1 * (2 * Real.exp (-Real.pi * ∑ a, ∑ j, ‖v a j‖ ^ 2)) :=
          mul_le_mul (hK1 v) (norm_dilated_le m n X z h1 h2 v) (norm_nonneg _) zero_le_one
      _ = 2 * Real.exp (-Real.pi * ∑ a, ∑ j, ‖v a j‖ ^ 2) := one_mul _
  have hstep := integral_step (μ := volume) hU (fun z v => K v * dilated m n X v z) hd hm hb
  refine ⟨ρ, hρ, ?_, ?_⟩
  · intro z hz
    exact (hstep.1 z hz).differentiableAt.differentiableWithinAt
  · intro r
    have h := iteratedDeriv_integral (μ := volume) hU r (fun z v => K v * dilated m n X v z)
      hd hm hb 0 (Metric.mem_ball_self hρ)
    refine h.trans ?_
    refine integral_congr_ae (Filter.Eventually.of_forall fun v => ?_)
    exact congrFun (hcm (K v) _ r) 0

end GlobalTheory.CompanionTheory.HolMean.DilatedGaussian
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MultisetAntitoneEnumerationStatement
section
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.multiset_antitone_enumeration : ∀ {α : Type*} (m : Multiset α) (f : α → ℝ) (P : α → α → Prop), (∀ a b, P a b → f a < f b) → ∃ (h : ℕ) (Δ : Fin h → α), Finset.univ.val.map Δ = m ∧ Antitone (f ∘ Δ) ∧ ∀ i j, i < j → ¬ P (Δ i) (Δ j) := by
  first | exact @GlobalTheory.CompanionTheory.Multiset.exists_antitone_listing | exact GlobalTheory.CompanionTheory.Multiset.exists_antitone_listing | (intros; apply GlobalTheory.CompanionTheory.Multiset.exists_antitone_listing <;> assumption)
end

