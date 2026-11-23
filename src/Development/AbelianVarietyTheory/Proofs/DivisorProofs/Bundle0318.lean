module

public import Mathlib
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.OmegaFactorization
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.PartialZetaFunctionalEquation
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0157
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0169
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0184
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0214
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CovolumeFractionalIdealRealLatticeImage
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0188
public import Formalism.LatticeTheta.ThetaShiftInversion
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeckePhiFourierTransformRapidDecay
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0207
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0275
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0097
public import Development.AbelianVarietyTheory.Definitions.Divisors.IndEtOfForallFinset
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0007
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0006

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeckeWeightTwoPoissonSummationFractionalIdeal
section
open NumberField Complex MeasureTheory
open scoped nonZeroDivisors ContDiff FourierTransform RealInnerProductSpace

noncomputable section

namespace GlobalTheory.HeckeTwoPoisson

open GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization GlobalTheory.HeckeTwo GlobalTheory.LipschitzTR

theorem hTrans_decay : ∀ (σ : ℂ), 0 < σ.re → ∀ (y : ℝ), y ≠ 0 → ∀ (N : ℕ), ∃ C : ℝ, ∀ ν : ℝ,
    ‖GlobalTheory.HeckeTwo.hTrans σ ν y‖ ≤ C * (1 + |ν|) ^ (-(N : ℝ)) := _root_.GlobalTheory.HeckeTwo.hTrans_rapid_decay

theorem phi_line : ∀ (σ : ℂ), 0 < σ.re → ∀ (y : ℝ), y ≠ 0 →
    Continuous (fun t : ℝ => GlobalTheory.HeckeTwo.phi σ ((t : ℂ) + (y : ℂ) * Complex.I)) ∧
    Integrable (fun t : ℝ => GlobalTheory.HeckeTwo.phi σ ((t : ℂ) + (y : ℂ) * Complex.I)) := _root_.GlobalTheory.HeckeTwo.phi_line_continuous_integrable

theorem summable_lat : ∀ (F : Type) [Field F] [NumberField F] [NumberField.IsTotallyReal F]
    (𝔞 : GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.Frac F) (σ : ℂ), 0 < σ.re → ∀ z ∈ GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.upperHalf F, ∀ b : F, b ≠ 0 →
    Summable (fun a : {a : F // a ∈ GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.latM 𝔞} =>
      ∏ τ : GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.Emb F, GlobalTheory.HeckeTwo.phi σ (((τ a.1 : ℝ) : ℂ) + ((τ b : ℝ) : ℂ) * z τ)) := GlobalTheory.T.summable_heckeWeightTwoLatticeSum

theorem prod_isBigO : ∀ (ι : Type) [Fintype ι] (g : ι → ℝ → ℂ) (b : ℝ), 0 ≤ b →
    (∀ i, ∃ C : ℝ, ∀ t : ℝ, ‖g i t‖ ≤ C * (1 + |t|) ^ (-b)) →
    (fun v : EuclideanSpace ℝ ι => ∏ i, g i (v i)) =O[Filter.cocompact (EuclideanSpace ℝ ι)]
      (fun v => ‖v‖ ^ (-b)) := _root_.GlobalTheory.prod_rpow_decay_isBigO_cocompact

theorem fourier_prod (ι : Type) [Fintype ι] (f : ι → ℝ → ℂ) (x : EuclideanSpace ℝ ι) :
    𝓕 (fun ξ : EuclideanSpace ℝ ι => ∏ i, f i (ξ i)) x = ∏ i, 𝓕 (f i) (x i) := by
  simp only [Real.fourier_eq', Real.fourier_real_eq]
  rw [← integral_fintype_prod_volume_eq_prod,
    ← (PiLp.volume_preserving_toLp ι).integral_comp (MeasurableEquiv.toLp 2 (ι → ℝ)).measurableEmbedding]
  refine integral_congr_ae (Filter.Eventually.of_forall fun ξ => ?_)
  simp only [smul_eq_mul]
  rw [Finset.prod_mul_distrib, ← Complex.exp_sum, PiLp.inner_apply, Finset.mul_sum, Complex.ofReal_sum,
    Finset.sum_mul]

theorem remb_inj {F : Type} [Field F] [NumberField F] [IsTotallyReal F] : Function.Injective (remb F) := by
  intro a b h
  have hne : Nonempty (F →+* ℝ) := by
    rw [← Fintype.card_pos_iff, GlobalTheory.IndefiniteRowSideFullHecke.TraceDualDifferent.card_realEmb]
    exact Module.finrank_pos
  have h1 := congrArg (fun v : RSp F => v (Classical.choice hne)) h
  simp only [remb_apply] at h1
  exact (Classical.choice hne).injective h1

theorem hTrans_eq_fourier (σ : ℂ) (y : ℝ) :
    (fun ν : ℝ => hTrans σ ν y) = 𝓕 (fun t : ℝ => phi σ ((t : ℂ) + (y : ℂ) * I)) := by
  funext ν
  rw [Real.fourier_real_eq]
  unfold hTrans
  refine integral_congr_ae (Filter.Eventually.of_forall fun t => ?_)
  simp only [smul_eq_mul, Real.fourierChar_apply]
  rw [mul_comm]
  congr 2
  push_cast
  ring

theorem continuous_hTrans (σ : ℂ) (hσ : 0 < σ.re) (y : ℝ) (hy : y ≠ 0) :
    Continuous (fun ν : ℝ => hTrans σ ν y) := by
  rw [hTrans_eq_fourier]
  exact VectorFourier.fourierIntegral_continuous Real.continuous_fourierChar (innerSL ℝ).continuous₂
    (phi_line σ hσ y hy).2

theorem fourier_mod (σ : ℂ) (hσ : 0 < σ.re) (y : ℝ) (hy : y ≠ 0) (c s : ℝ) :
    𝓕 (fun t : ℝ => Complex.exp (2 * (Real.pi : ℂ) * I * ((t * c : ℝ) : ℂ)) * hTrans σ t y) s =
      phi σ (((c - s : ℝ) : ℂ) + (y : ℂ) * I) := by
  set f : ℝ → ℂ := fun t => phi σ ((t : ℂ) + (y : ℂ) * I) with hf
  obtain ⟨hfc, hfi⟩ := phi_line σ hσ y hy
  have hH := hTrans_eq_fourier σ y
  have hFi : Integrable (𝓕 f) := by
    obtain ⟨C, hC⟩ := hTrans_decay σ hσ y hy 2
    have h2 : Integrable (fun t : ℝ => (1 + ‖t‖) ^ (-(2 : ℝ))) :=
      integrable_one_add_norm (by simp)
    refine (h2.const_mul C).mono' ?_ (Filter.Eventually.of_forall fun t => ?_)
    · rw [← hH]; exact (continuous_hTrans σ hσ y hy).aestronglyMeasurable
    · have := hC t
      rw [← hH]
      simpa [Real.norm_eq_abs] using this
  have hinv : 𝓕⁻ (𝓕 f) = f := Continuous.fourierInv_fourier_eq hfc hfi hFi
  have hmod : 𝓕 (fun t : ℝ => Complex.exp (2 * (Real.pi : ℂ) * I * ((t * c : ℝ) : ℂ)) * hTrans σ t y) s =
      𝓕 (𝓕 f) (s - c) := by
    rw [Real.fourier_real_eq, Real.fourier_real_eq, ← hH]
    refine integral_congr_ae (Filter.Eventually.of_forall fun t => ?_)
    simp only [Circle.smul_def, Real.fourierChar_apply, smul_eq_mul]
    rw [← mul_assoc, ← Complex.exp_add]
    congr 2
    push_cast
    ring
  rw [hmod]
  have h3 := congrFun hinv (-(s - c))
  rw [Real.fourierInv_eq_fourier_neg, neg_neg] at h3
  rw [h3, hf]
  congr 2
  push_cast
  ring

theorem poisson : ∀ (F : Type) [Field F] [NumberField F] [NumberField.IsTotallyReal F] (𝔞 : GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.Frac F) (σ : ℂ),
    0 < σ.re → ∀ z ∈ GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.upperHalf F, ∀ b : F, b ≠ 0 →
    Summable (fun ν : {ν : F // ν ∈ (𝔞 : FractionalIdeal (NumberField.RingOfIntegers F)⁰ F)} => GlobalTheory.HeckeTwo.fTerm σ z b ν.1) ∧
    HasSum (fun a : {a : F // a ∈ GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.latM 𝔞} => ∏ τ : GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.Emb F, GlobalTheory.HeckeTwo.phi σ (((τ a.1 : ℝ) : ℂ) + ((τ b : ℝ) : ℂ) * z τ))
      ((GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.omegaFactor 𝔞 : ℂ) * ∑' ν : {ν : F // ν ∈ (𝔞 : FractionalIdeal (NumberField.RingOfIntegers F)⁰ F)}, GlobalTheory.HeckeTwo.fTerm σ z b ν.1) := by
  intro F _ _ _ 𝔞 σ hσ z hz b hb
  classical
  set A : FractionalIdeal (𝓞 F)⁰ F := (𝔞 : FractionalIdeal (𝓞 F)⁰ F) with hA
  have hA0 : A ≠ 0 := 𝔞.ne_zero
  haveI : DiscreteTopology (latOf A) := discrete_latOf F A
  haveI : IsZLattice ℝ (latOf A) := isZLattice_latOf F A hA0
  set L := latOf A with hL
  have hdual : Formalism.H.dual L = latOf (latM 𝔞) := by
    rw [hL, dual_latOf_eq_latOf_traceDual F A hA0, latM_eq_dual]
  have hcov : ZLattice.covolume L = omegaFactor 𝔞 := by
    rw [hL, GlobalTheory.LipschitzCovol.covolume_latOf F A hA0, GlobalTheory.IndefiniteRowSideFullHecke.TraceDualDifferent.covol, omegaFactor, dF, nrm,
      Real.sqrt_eq_rpow]
  obtain ⟨h1, h2⟩ := Formalism.H.dualIsLattice (RSp F) L
  haveI : DiscreteTopology (Formalism.H.dual L) := h1

  have hyτ : ∀ τ : Emb F, τ b * (z τ).im ≠ 0 := fun τ => mul_ne_zero ((map_ne_zero τ).2 hb) (hz τ).ne'
  set g : Emb F → ℝ → ℂ := fun τ t =>
    Complex.exp (2 * (Real.pi : ℂ) * I * ((t * (τ b * (z τ).re) : ℝ) : ℂ)) * hTrans σ t (τ b * (z τ).im) with hg
  set Ψ : RSp F → ℂ := fun v => ∏ τ, g τ (v τ) with hΨ
  have hΨν : ∀ ν : F, Ψ (remb F ν) = fTerm σ z b ν := by
    intro ν
    simp only [hΨ, hg, remb_apply, fTerm]
    refine Finset.prod_congr rfl fun τ _ => ?_
    congr 3
    push_cast
    ring
  have hgn : ∀ τ t, ‖g τ t‖ = ‖hTrans σ t (τ b * (z τ).im)‖ := by
    intro τ t
    simp only [hg, norm_mul]
    rw [show (2 * (Real.pi : ℂ) * I * ((t * (τ b * (z τ).re) : ℝ) : ℂ)) =
      ((2 * Real.pi * (t * (τ b * (z τ).re)) : ℝ) : ℂ) * I by push_cast; ring, Complex.norm_exp_ofReal_mul_I, one_mul]
  have hΨc : Continuous Ψ := by
    refine continuous_finsetProd _ fun τ _ => ?_
    refine Continuous.comp (g := g τ) ?_ ((EuclideanSpace.proj τ : RSp F →L[ℝ] ℝ).continuous)
    exact (by fun_prop : Continuous fun t : ℝ => Complex.exp (2 * (Real.pi : ℂ) * I * ((t * (τ b * (z τ).re) : ℝ) : ℂ))).mul
      (continuous_hTrans σ hσ _ (hyτ τ))
  set N : ℕ := Module.finrank ℝ (RSp F) + 1 with hN
  have hbN : (Module.finrank ℝ (RSp F) : ℝ) < (N : ℝ) := by rw [hN]; push_cast; linarith
  have hΨO : Ψ =O[Filter.cocompact (RSp F)] fun v => ‖v‖ ^ (-(N : ℝ)) :=
    prod_isBigO (Emb F) g N (Nat.cast_nonneg _) fun τ => by
      obtain ⟨C, hC⟩ := hTrans_decay σ hσ _ (hyτ τ) N
      exact ⟨C, fun t => (hgn τ t).symm ▸ hC t⟩
  obtain ⟨hint, hsumx, hGc, hGper⟩ := Formalism.H.poisson_periodization (RSp F) L Ψ hΨc (N : ℝ) hbN hΨO
  haveI : Module.Free ℤ L := ZLattice.module_free ℝ L
  haveI : Module.Finite ℤ L := ZLattice.module_finite ℝ L
  have hD := ZLattice.isAddFundamentalDomain (Module.Free.chooseBasis ℤ L) (volume : Measure (RSp F))
  set D := ZSpan.fundamentalDomain ((Module.Free.chooseBasis ℤ L).ofZLatticeBasis ℝ L)
  have hcoef : ∀ μ : Formalism.H.dual L, (∫ y in D, (∑' l : L, Ψ ((l : RSp F) + y)) *
      Complex.exp (-(2 * Real.pi * Complex.I * (⟪(μ : RSp F), y⟫ : ℝ)))) = 𝓕 Ψ μ :=
    fun μ => Formalism.H.unfolding_fourier_coefficient (RSp F) L Ψ hint D hD μ μ.2

  have hFΨ : ∀ a : F, 𝓕 Ψ (remb F (-a)) = ∏ τ : Emb F, phi σ (((τ a : ℝ) : ℂ) + ((τ b : ℝ) : ℂ) * z τ) := by
    intro a
    rw [hΨ, fourier_prod]
    refine Finset.prod_congr rfl fun τ _ => ?_
    rw [remb_apply, hg]
    simp only
    rw [fourier_mod σ hσ _ (hyτ τ)]
    congr 1
    apply Complex.ext <;> simp <;> ring
  have hDmem : ∀ x, x ∈ Formalism.H.dual L ↔ ∃ a ∈ latM 𝔞, remb F a = x := by
    intro x; rw [hdual]; exact mem_latOf _ x
  have hLmem : ∀ x, x ∈ L ↔ ∃ ν ∈ A, remb F ν = x := by
    intro x; rw [hL]; exact mem_latOf _ x
  let eM : {a : F // a ∈ latM 𝔞} ≃ Formalism.H.dual L := Equiv.ofBijective
    (fun a => ⟨remb F (-a.1), (hDmem _).2 ⟨-a.1, (latM 𝔞 : Submodule (𝓞 F) F).neg_mem a.2, rfl⟩⟩)
    ⟨fun a a' h => Subtype.ext (neg_injective (remb_inj (congrArg Subtype.val h))), fun μ => by
      obtain ⟨a, ha, h⟩ := (hDmem μ).1 μ.2
      exact ⟨⟨-a, (latM 𝔞 : Submodule (𝓞 F) F).neg_mem ha⟩, Subtype.ext (by simp [h])⟩⟩
  let eD : {ν : F // ν ∈ A} ≃ L := Equiv.ofBijective
    (fun ν => ⟨remb F ν.1, (hLmem _).2 ⟨ν.1, ν.2, rfl⟩⟩)
    ⟨fun ν ν' h => Subtype.ext (remb_inj (congrArg Subtype.val h)), fun μ => by
      obtain ⟨ν, hν, h⟩ := (hLmem μ).1 μ.2
      exact ⟨⟨ν, hν⟩, Subtype.ext h⟩⟩
  have hsL := summable_lat F 𝔞 σ hσ z hz b hb
  have hsumc : Summable (fun μ : Formalism.H.dual L => ∫ y in D, (∑' l : L, Ψ ((l : RSp F) + y)) *
      Complex.exp (-(2 * Real.pi * Complex.I * (⟪(μ : RSp F), y⟫ : ℝ)))) := by
    simp only [hcoef]
    rw [← eM.summable_iff]
    exact hsL.congr fun a => (hFΨ a.1).symm
  have H4 := Formalism.H.lattice_fourier_series (RSp F) L (fun x => ∑' l : L, Ψ ((l : RSp F) + x))
    hGc hGper D hD hsumc 0
  simp only [hcoef, inner_zero_right, Complex.ofReal_zero, mul_zero, Complex.exp_zero, mul_one,
    add_zero] at H4
  rw [← eM.hasSum_iff] at H4
  have hs0 : Summable (fun l : L => Ψ (l : RSp F)) := by simpa using hsumx 0
  have hsF : Summable (fun ν : {ν : F // ν ∈ A} => fTerm σ z b ν.1) := by
    rw [← eD.summable_iff] at hs0
    exact hs0.congr fun ν => hΨν ν.1
  have hR : ∑' l : L, Ψ (l : RSp F) = ∑' ν : {ν : F // ν ∈ A}, fTerm σ z b ν.1 := by
    rw [← eD.tsum_eq]
    exact tsum_congr fun ν => hΨν ν.1
  refine ⟨hsF, ?_⟩
  have hc0 : (ZLattice.covolume L : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 (ZLattice.covolume_ne_zero L volume)
  have H5 := H4.mul_left (ZLattice.covolume L : ℂ)
  rw [hR] at H5
  rw [← hcov]
  refine H5.congr_fun fun a => ?_
  have key : ∀ a : {a : F // a ∈ latM 𝔞}, 𝓕 Ψ ((eM a : RSp F)) = ∏ τ : Emb F, phi σ (((τ a.1 : ℝ) : ℂ) + ((τ b : ℝ) : ℂ) * z τ) :=
    fun a => hFΨ a.1
  simp only [Function.comp_apply, key]
  rw [← mul_assoc, mul_inv_cancel₀ hc0, one_mul]

end GlobalTheory.HeckeTwoPoisson
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HomogeneousCochainsHomologyAddEquiv
section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex Simplicial TensorProduct GlobalTheory.EtC

namespace GlobalTheory.HomogCochains

open GroundTheory.ProfCoh groupCohomology

variable {k : Type} [CommRing k] {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  {M : Rep.{0} k G} [IsDiscreteRep M] {C : CosimplicialObject AddCommGrpCat.{1}}
  {e : ∀ m : ℕ, C.obj ⦋m⦌ →+ ((Fin (m + 1) → G) → M)}

theorem neg_one_pow_smul_eq (m : ℕ) (x : M) : ((-1 : k) ^ m) • x = ((-1 : ℤ) ^ m) • x := by
  rw [← Int.cast_smul_eq_zsmul k]
  simp

section
variable (he : ∀ m, Function.Injective (e m))
  (hr : ∀ m (φ : (Fin (m + 1) → G) → M), (∃ c, e m c = φ) ↔
    IsLocallyConstant φ ∧ ∀ (τ : G) (σ : Fin (m + 1) → G), φ (fun i => τ * σ i) = M.ρ τ (φ σ))
  (hd : ∀ m (i : Fin (m + 2)) (c : C.obj ⦋m⦌) (σ : Fin (m + 2) → G),
    e (m + 1) (C.δ i c) σ = e m c (σ ∘ i.succAbove))

include hr in
theorem isLocallyConstant_e (m : ℕ) (c : C.obj ⦋m⦌) : IsLocallyConstant (e m c) :=
  ((hr m (e m c)).1 ⟨c, rfl⟩).1

include hr in
theorem e_mul (m : ℕ) (c : C.obj ⦋m⦌) (τ : G) (σ : Fin (m + 1) → G) :
    e m c (fun i => τ * σ i) = M.ρ τ (e m c σ) :=
  ((hr m (e m c)).1 ⟨c, rfl⟩).2 τ σ

def toInh (m : ℕ) : C.obj ⦋m⦌ →+ locallyConstantCochains M m where
  toFun c := ⟨fun g => e m c (Fin.partialProd g),
    (isLocallyConstant_e hr m c).comp_continuous (continuous_partialProd m)⟩
  map_zero' := by ext g; simp
  map_add' a b := by ext g; simp

theorem toInh_apply (m : ℕ) (c : C.obj ⦋m⦌) (g : Fin m → G) :
    ((toInh hr m c : locallyConstantCochains M m) : (Fin m → G) → M) g = e m c (Fin.partialProd g) :=
  rfl

include he in
theorem toInh_bijective (m : ℕ) : Function.Bijective (toInh hr m) := by
  constructor
  · rw [injective_iff_map_eq_zero]
    intro c hc
    apply he m
    rw [map_zero]
    funext σ
    have h0 : ∀ g, e m c (Fin.partialProd g) = 0 := fun g => by
      have := congrArg (fun f : locallyConstantCochains M m => (f : (Fin m → G) → M) g) hc
      simpa [toInh_apply] using this
    have hσ : σ = fun i => σ 0 * Fin.partialProd (fun j => (σ (Fin.castSucc j))⁻¹ * σ j.succ) i := by
      have := Fin.partialProd_left_inv σ
      funext i
      conv_lhs => rw [← this]
      rfl
    rw [hσ, e_mul hr, h0, map_zero]
    rfl
  · intro φ
    let F : (Fin (m + 1) → G) → M := fun x => M.ρ (x 0) (φ.1 fun i => (x (Fin.castSucc i))⁻¹ * x i.succ)
    have hF : IsLocallyConstant F :=
      isLocallyConstant_ρ_apply M (continuous_apply 0)
        (φ.2.comp_continuous (continuous_pi fun _ =>
          ((continuous_apply _).inv).mul (continuous_apply _)))
    have hFm : ∀ (τ : G) (σ : Fin (m + 1) → G), F (fun i => τ * σ i) = M.ρ τ (F σ) := by
      intro τ σ
      simp only [F, mul_inv_rev, mul_assoc, inv_mul_cancel_left, map_mul]
      rfl
    obtain ⟨c, hc⟩ := (hr m F).2 ⟨hF, hFm⟩
    refine ⟨c, ?_⟩
    apply Subtype.ext
    funext g
    rw [toInh_apply, hc]
    simp only [F, Fin.partialProd_zero, Fin.partialProd_right_inv, map_one]
    rfl

theorem sum_hom_apply {X Y : AddCommGrpCat.{1}} {ι : Type} (s : Finset ι) (f : ι → (X ⟶ Y)) (x : X) :
    (∑ i ∈ s, f i) x = ∑ i ∈ s, f i x := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, AddCommGrpCat.hom_add_apply, ih]

theorem zsmul_hom_apply {X Y : AddCommGrpCat.{1}} (n : ℤ) (f : X ⟶ Y) (x : X) :
    (n • f) x = n • f x := by
  change (n • f).hom x = _
  rw [AddCommGrpCat.hom_zsmul]
  rfl

include hd hr in
theorem toInh_d (n : ℕ) (c : C.obj ⦋n⦌) :
    toInh hr (n + 1) ((AlgebraicTopology.AlternatingCofaceMapComplex.objD C n) c) =
      (dLocallyConstant M n).hom (toInh hr n c) := by
  apply Subtype.ext
  funext g
  rw [toInh_apply, dLocallyConstant_hom_apply, inhomogeneousCochains.d_hom_apply]
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [AlgebraicTopology.AlternatingCofaceMapComplex.objD, sum_hom_apply, zsmul_hom_apply,
    map_sum, map_zsmul, Finset.sum_apply, Pi.smul_apply, hd]
  rw [Fin.sum_univ_succ]
  congr 1
  · have : (Fin.partialProd g ∘ (0 : Fin (n + 2)).succAbove) =
        fun j => g 0 * Fin.partialProd (Fin.tail g) j := by
      funext j
      simp only [Function.comp_apply, Fin.succAbove_zero]
      exact Fin.partialProd_succ' g j
    rw [this, e_mul hr, Fin.val_zero, pow_zero, one_smul, toInh_apply]
    rfl
  · refine Finset.sum_congr rfl fun j _ => ?_
    rw [toInh_apply, Fin.partialProd_contractNth, Fin.val_succ, neg_one_pow_smul_eq]

abbrev upF (k : Type) [CommRing k] : ModuleCat.{0} k ⥤ AddCommGrpCat.{1} :=
  forget₂ (ModuleCat.{0} k) AddCommGrpCat.{0} ⋙ AddCommGrpCat.uliftFunctor.{1, 0}

theorem alt_d (n : ℕ) :
    ((AlgebraicTopology.alternatingCofaceMapComplex AddCommGrpCat.{1}).obj C).d n (n + 1) =
      AlgebraicTopology.AlternatingCofaceMapComplex.objD C n := by
  simp [AlgebraicTopology.alternatingCofaceMapComplex, AlgebraicTopology.AlternatingCofaceMapComplex.obj]


include he hr hd in
noncomputable def complexIso :
    (AlgebraicTopology.alternatingCofaceMapComplex AddCommGrpCat.{1}).obj C ≅
      ((upF k).mapHomologicalComplex _).obj (cochainsComplex M) :=
  HomologicalComplex.Hom.isoOfComponents
    (fun n => (((AddEquiv.ofBijective (toInh hr n) (toInh_bijective he hr n)).trans
      AddEquiv.ulift.symm).toAddCommGrpIso :
        (C.obj ⦋n⦌ : AddCommGrpCat.{1}) ≅ (upF k).obj (ModuleCat.of k (locallyConstantCochains M n))))
    (by
      rintro i j (rfl : i + 1 = j)
      rw [alt_d, Functor.mapHomologicalComplex_obj_d, cochainsComplex_d]
      ext c
      apply ULift.ext
      exact (toInh_d hr hd i c).symm)

end

end GlobalTheory.HomogCochains

open GlobalTheory.HomogCochains in
theorem GlobalTheory.homogeneousCochains_homology_addEquiv : ∀ (k : Type) [CommRing k] (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] (M : Rep.{0} k G) [GroundTheory.ProfCoh.IsDiscreteRep M] (C : CosimplicialObject AddCommGrpCat.{1}) (e : ∀ m : ℕ, C.obj ⦋m⦌ →+ ((Fin (m + 1) → G) → M)), (∀ m, Function.Injective (e m)) → (∀ m (φ : (Fin (m + 1) → G) → M), (∃ c, e m c = φ) ↔ IsLocallyConstant φ ∧ ∀ (τ : G) (σ : Fin (m + 1) → G), φ (fun i => τ * σ i) = M.ρ τ (φ σ)) → (∀ m (i : Fin (m + 2)) (c : C.obj ⦋m⦌) (σ : Fin (m + 2) → G), e (m + 1) (C.δ i c) σ = e m c (σ ∘ i.succAbove)) → ∀ n : ℕ, Nonempty (((AlgebraicTopology.alternatingCofaceMapComplex AddCommGrpCat.{1}).obj C).homology n ≃+ GroundTheory.ProfCoh.cohomology M n) := by
  intro k _ G _ _ _ M _ C e he hr hd n
  let i1 := (HomologicalComplex.homologyFunctor AddCommGrpCat.{1} _ n).mapIso (complexIso he hr hd)
  let i2 : (((upF k).mapHomologicalComplex _).obj (GroundTheory.ProfCoh.cochainsComplex M)).homology n ≅
      (upF k).obj ((GroundTheory.ProfCoh.cochainsComplex M).homology n) :=
    ((GroundTheory.ProfCoh.cochainsComplex M).sc n).mapHomologyIso (upF k)
  exact ⟨(i1 ≪≫ i2).addCommGroupIsoToAddEquiv.trans AddEquiv.ulift⟩
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HypercohomologyMappingConeSecondVariableExact
section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

noncomputable section
namespace GlobalTheory.EtC.ConeTgt

variable {R : Type} [CommRing R]

theorem cls_eq' {K I : Cx R} {n : ℤ} (x y : Cocycle K I n) (m : ℤ) (hm : m + 1 = n) (β : Cochain K I m)
    (h : (x : Cochain K I n) = (y : Cochain K I n) + δ m n β) :
    CohomologyClass.mk x = CohomologyClass.mk y := by
  rw [← sub_eq_zero, ← CohomologyClass.mk_sub, CohomologyClass.mk_eq_zero_iff,
    mem_coboundaries_iff _ m hm]
  exact ⟨β, by simp [h]⟩

end GlobalTheory.EtC.ConeTgt

private theorem coe_zcomp {R : Type} [CommRing R] {K L M : Cx R} {m n k : ℤ}
    (a : Cocycle K L m) (b : Cocycle L M n) (h : m + n = k) :
    ((zcomp a b h : Cocycle K M k) : Cochain K M k) = a.1.comp b.1 h := rfl

private theorem cohomologyClass_mk_eq_zero_of_eq_δ {R : Type} [CommRing R] {K L : Cx R} {n : ℤ} (x : Cocycle K L n)
    (m : ℤ) (hm : m + 1 = n) (β : Cochain K L m) (h : (x : Cochain K L n) = δ m n β) :
    CohomologyClass.mk x = 0 := by
  rw [CohomologyClass.mk_eq_zero_iff, mem_coboundaries_iff _ m hm]
  exact ⟨β, h.symm⟩

theorem GlobalTheory.EtC.coneSeqTgt_exact : ∀ (R : Type) [CommRing R] (K : Cx R) {I J : Cx R} (f : I ⟶ J) (n : ℤ), Function.Exact (cpush K f n) (cpush K (mappingCone.inr f) n) ∧ Function.Exact (cpush K (mappingCone.inr f) n) (cpost K (mappingCone.fst f) n (n + 1) rfl) ∧ Function.Exact (cpost K (mappingCone.fst f) n (n + 1) rfl) (cpush K f (n + 1)) := by
  intro R _ K I J f n
  refine ⟨fun c => ?_, fun c => ?_, fun c => ?_⟩
  · obtain ⟨y, rfl⟩ := c.mk_surjective
    constructor
    · intro hy
      simp only [cpush, cpost_mk] at hy
      rw [CohomologyClass.mk_eq_zero_iff, mem_coboundaries_iff _ (n - 1) (by omega)] at hy
      obtain ⟨γ, hγ⟩ := hy
      rw [coe_zcomp] at hγ
      have ha : δ n (n + 1) (γ.comp (mappingCone.fst f).1 (by omega : n - 1 + 1 = n)) = 0 := by
        rw [δ_comp γ (mappingCone.fst f).1 _ n 2 (n + 1) rfl (by omega) rfl,
          Cocycle.δ_eq_zero, hγ]
        simp [Cochain.comp_assoc_of_second_is_zero_cochain, mappingCone.inr_fst]
      refine ⟨CohomologyClass.mk (Cocycle.mk _ (n + 1) rfl ha), ?_⟩
      simp only [cpush, cpost_mk]
      refine GlobalTheory.EtC.ConeTgt.cls_eq' _ _ (n - 1) (by omega)
        (-(γ.comp (mappingCone.snd f) (add_zero _))) ?_
      rw [coe_zcomp, δ_neg, δ_comp_zero_cochain _ _ _ (by omega), mappingCone.δ_snd, hγ]
      simp [Cochain.comp_assoc_of_second_is_zero_cochain,
        Cochain.comp_assoc_of_third_is_zero_cochain, mappingCone.inr_snd]
    · rintro ⟨c', hc'⟩
      rw [← hc']
      obtain ⟨x, rfl⟩ := c'.mk_surjective
      simp only [cpush, cpost_mk]
      refine cohomologyClass_mk_eq_zero_of_eq_δ _ (n + -1) (by omega) (x.1.comp (mappingCone.inl f) rfl) ?_
      rw [δ_comp x.1 (mappingCone.inl f) rfl (n + 1) 0 n (by omega) rfl (neg_add_cancel 1),
        mappingCone.δ_inl, Cocycle.δ_eq_zero]
      simp [coe_zcomp, Cochain.comp_assoc_of_second_is_zero_cochain, Cochain.ofHom_comp]
  · obtain ⟨z, rfl⟩ := c.mk_surjective
    constructor
    · intro hz
      rw [cpost_mk, CohomologyClass.mk_eq_zero_iff, mem_coboundaries_iff _ n rfl] at hz
      obtain ⟨c₀, hc₀⟩ := hz
      rw [coe_zcomp] at hc₀
      have hy : δ n (n + 1) (z.1.comp (mappingCone.snd f) (add_zero n) +
          c₀.comp (Cochain.ofHom f) (add_zero n)) = 0 := by
        rw [δ_add, δ_comp_zero_cochain _ _ _ rfl, mappingCone.δ_snd, δ_comp_ofHom, hc₀,
          Cocycle.δ_eq_zero]
        simp [Cochain.comp_assoc_of_third_is_zero_cochain]
      refine ⟨CohomologyClass.mk (Cocycle.mk _ (n + 1) rfl hy), ?_⟩
      simp only [cpush, cpost_mk]
      refine GlobalTheory.EtC.ConeTgt.cls_eq' _ _ (n + -1) (by omega)
        (c₀.comp (mappingCone.inl f) rfl) ?_
      rw [coe_zcomp, δ_comp c₀ (mappingCone.inl f) rfl (n + 1) 0 n (by omega) rfl
        (neg_add_cancel 1), mappingCone.δ_inl, hc₀]
      rw [mappingCone.ext_cochain_to_iff _ n (n + 1) rfl]
      constructor
      · simp [Cochain.comp_assoc_of_second_is_zero_cochain, Cochain.add_comp]
      · simp [Cochain.comp_assoc_of_second_is_zero_cochain,
          Cochain.comp_assoc_of_third_is_zero_cochain, Cochain.add_comp]
    · rintro ⟨c', hc'⟩
      rw [← hc']
      obtain ⟨y, rfl⟩ := c'.mk_surjective
      simp only [cpush, cpost_mk]
      refine cohomologyClass_mk_eq_zero_of_eq_δ _ n rfl 0 ?_
      simp [coe_zcomp, Cochain.comp_assoc_of_second_is_zero_cochain, mappingCone.inr_fst]
  · obtain ⟨w, rfl⟩ := c.mk_surjective
    constructor
    · intro hw
      simp only [cpush, cpost_mk] at hw
      rw [CohomologyClass.mk_eq_zero_iff, mem_coboundaries_iff _ n rfl] at hw
      obtain ⟨b, hb⟩ := hw
      rw [coe_zcomp] at hb
      refine ⟨CohomologyClass.mk (mappingCone.liftCocycle f w (-b) rfl
        (by rw [δ_neg, hb]; simp)), ?_⟩
      rw [cpost_mk]
      congr 1
      apply Cocycle.ext
      rw [coe_zcomp]
      simp [mappingCone.liftCochain_fst]
    · rintro ⟨c', hc'⟩
      rw [← hc']
      obtain ⟨z, rfl⟩ := c'.mk_surjective
      simp only [cpush, cpost_mk]
      refine cohomologyClass_mk_eq_zero_of_eq_δ _ n rfl (-(z.1.comp (mappingCone.snd f) (add_zero n))) ?_
      rw [δ_neg, δ_comp_zero_cochain _ _ _ rfl, mappingCone.δ_snd, Cocycle.δ_eq_zero]
      simp [coe_zcomp, Cochain.comp_assoc_of_third_is_zero_cochain]
end
end

