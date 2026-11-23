module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0239
public import Development.AbelianVarietyTheory.Definitions.Divisors.GalMapMul
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0245
public import ReciprocityTheory.L2DbarEstimates.PlurisubharmonicCharts.Bundle0002
public import Development.AbelianVarietyTheory.Definitions.Divisors.IndEtOfForallFinset
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0256
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.StabilizerEqCentralizer
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0146
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0198
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0145

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorsorBaseChangeZmod
section
open CategoryTheory Limits
open scoped TensorProduct

noncomputable section
namespace GlobalTheory.LocAcyc

def zmodTensorAct (U B : Type) [CommRing U] [CommRing B] [Algebra U B] (q : ℕ) (D : Type)
    [CommRing D] [Algebra U D] (act : Multiplicative (ZMod q) →* (D ≃ₐ[U] D)) :
    Multiplicative (ZMod q) →* (B ⊗[U] D ≃ₐ[B] B ⊗[U] D) where
  toFun g := Algebra.TensorProduct.congr AlgEquiv.refl (act g)
  map_one' := by
    ext z
    induction z using TensorProduct.induction_on with
    | zero => simp
    | tmul b x => simp
    | add z w hz hw => simp_all [map_add (f := _)]
  map_mul' g h := by
    ext z
    induction z using TensorProduct.induction_on with
    | zero => simp
    | tmul b x => simp
    | add z w hz hw => simp_all [map_add (f := _)]

@[simp] theorem zmodTensorAct_tmul (U B : Type) [CommRing U] [CommRing B] [Algebra U B] (q : ℕ)
    (D : Type) [CommRing D] [Algebra U D] (act : Multiplicative (ZMod q) →* (D ≃ₐ[U] D))
    (b : B) (x : D) (g : Multiplicative (ZMod q)) :
    zmodTensorAct U B q D act g (b ⊗ₜ x) = b ⊗ₜ act g x := by simp [zmodTensorAct]

theorem isZModTorsor_tensorBase (U B : Type) [CommRing U] [CommRing B] [Algebra U B] (q : ℕ)
    (D : Type) [CommRing D] [Algebra U D] (act : Multiplicative (ZMod q) →* (D ≃ₐ[U] D))
    (hq : 0 < q) (hD : IsZModTorsor U D q act) :
    IsZModTorsor B (B ⊗[U] D) q (zmodTensorAct U B q D act) := by
  haveI : NeZero q := ⟨hq.ne'⟩
  obtain ⟨h1, h2, h3, h4⟩ := hD
  refine ⟨inferInstance, inferInstance, inferInstance, ?_⟩
  set Φ := Algebra.TensorProduct.productMap
      (Pi.algHom U (fun _ : Multiplicative (ZMod q) => D) (fun _ => AlgHom.id U D))
      (Pi.algHom U (fun _ : Multiplicative (ZMod q) => D) (fun g => (act g).toAlgHom)) with hΦ
  set ΦB := Algebra.TensorProduct.productMap
      (Pi.algHom B (fun _ : Multiplicative (ZMod q) => B ⊗[U] D) (fun _ => AlgHom.id B (B ⊗[U] D)))
      (Pi.algHom B (fun _ : Multiplicative (ZMod q) => B ⊗[U] D)
        (fun g => (zmodTensorAct U B q D act g).toAlgHom)) with hΦB
  let e1 := TensorProduct.AlgebraTensorModule.distribBaseChange U B D D
  let L := (LinearEquiv.ofBijective Φ.toLinearMap h4).lTensor B
  let e2 := TensorProduct.piRight U U B (fun _ : Multiplicative (ZMod q) => D)
  have key : ∀ z, ΦB (e1 z) = e2 (L z) := by
    intro z
    induction z using TensorProduct.induction_on with
    | zero => simp
    | tmul b w =>
      induction w using TensorProduct.induction_on with
      | zero => simp
      | tmul x y =>
        funext g
        simp [e1, L, e2, hΦ, hΦB, Algebra.TensorProduct.productMap_apply_tmul]
      | add w w' hw hw' =>
        simp only [TensorProduct.tmul_add, map_add (f := _), hw, hw']
    | add z w hz hw => simp only [map_add (f := _), hz, hw]
  have : (ΦB : _ → _) = e2 ∘ L ∘ e1.symm := by
    funext w
    simpa using key (e1.symm w)
  rw [this]
  exact e2.bijective.comp (L.bijective.comp e1.symm.bijective)

theorem exists_isZModTorsor_tensorBase : ∀ (U B : Type) [CommRing U] [CommRing B] [Algebra U B] (q : ℕ) (D : Type) [CommRing D]
    [Algebra U D] (act : Multiplicative (ZMod q) →* (D ≃ₐ[U] D)), 0 < q →
    GlobalTheory.LocAcyc.IsZModTorsor U D q act →
    ∃ actB : Multiplicative (ZMod q) →* (TensorProduct U B D ≃ₐ[B] TensorProduct U B D),
      GlobalTheory.LocAcyc.IsZModTorsor B (TensorProduct U B D) q actB :=
  fun U B _ _ _ q D _ _ act hq hD => ⟨_, isZModTorsor_tensorBase U B q D act hq hD⟩

end GlobalTheory.LocAcyc
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorusEmbeddingLieInjective
section
open GlobalTheory.EtC

namespace GlobalTheory

theorem genFibre_prime_meets_polynomial :
    ∀ (T : Type) [CommRing T] [IsDomain T] [IsLocalRing T], AIC T → ∀ (O : Type) [CommRing O] [Algebra T O] [Algebra (Polynomial T) O] [IsScalarTower T (Polynomial T) O] [HenselianLocalRing O] [IsSepClosed (IsLocalRing.ResidueField O)], (∃ (ι : Type) (_ : Preorder ι) (_ : IsDirected ι (· ≤ ·)) (_ : Nonempty ι) (Si : ι → Subalgebra (Polynomial T) O), Monotone Si ∧ (∀ s : O, ∃ i, s ∈ Si i) ∧ ∀ i, ∃ (E : Type) (_ : CommRing E) (_ : Algebra (Polynomial T) E) (_ : Algebra.Etale (Polynomial T) E) (P : Ideal E) (_ : P.IsPrime), Nonempty (Localization.AtPrime P ≃ₐ[(Polynomial T)] Si i)) → ∀ P : Ideal (Localization (Algebra.algebraMapSubmonoid O (nonZeroDivisors T))), P.IsPrime → P ≠ ⊥ → ∃ g : Polynomial T, g ≠ 0 ∧ algebraMap (Polynomial T) (Localization (Algebra.algebraMapSubmonoid O (nonZeroDivisors T))) g ∈ P := by
  intro T _ _ _ hA O _ _ _ _ _ _ hind P hP hne
  haveI : IsDomain (Localization (Algebra.algebraMapSubmonoid O (nonZeroDivisors T))) :=
    (locIndEtale_isDomain_isIntegrallyClosed T O 1 ⟨inferInstance, hA⟩ (by simp) one_pos hind).1
  by_contra hcon
  push_neg at hcon

  obtain ⟨y, hyP, hy0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hne
  obtain ⟨⟨o, s⟩, rfl⟩ := IsLocalization.mk'_surjective (Algebra.algebraMapSubmonoid O (nonZeroDivisors T)) y
  have ho : algebraMap O (Localization (Algebra.algebraMapSubmonoid O (nonZeroDivisors T))) o = IsLocalization.mk' (Localization (Algebra.algebraMapSubmonoid O (nonZeroDivisors T))) o s * algebraMap O (Localization (Algebra.algebraMapSubmonoid O (nonZeroDivisors T))) s :=
    (IsLocalization.mk'_spec (Localization (Algebra.algebraMapSubmonoid O (nonZeroDivisors T))) o s).symm
  have hoP : algebraMap O (Localization (Algebra.algebraMapSubmonoid O (nonZeroDivisors T))) o ∈ P := ho ▸ P.mul_mem_right _ hyP
  have ho0 : algebraMap O (Localization (Algebra.algebraMapSubmonoid O (nonZeroDivisors T))) o ≠ 0 := by
    rw [ho]
    exact mul_ne_zero hy0 (IsLocalization.map_units (Localization (Algebra.algebraMapSubmonoid O (nonZeroDivisors T))) s).ne_zero
  obtain ⟨ι, _, _, _, Si, -, hcov, hloc⟩ := hind
  obtain ⟨i, hoi⟩ := hcov o
  obtain ⟨E, _, _, _, p, _, ⟨e⟩⟩ := hloc i
  haveI : Algebra.QuasiFinite (Polynomial T) (Localization.AtPrime p) := inferInstance
  haveI : Algebra.QuasiFinite (Polynomial T) (Si i) := (Algebra.QuasiFinite.iff_of_algEquiv e).1 this
  let φ : Si i →+* (Localization (Algebra.algebraMapSubmonoid O (nonZeroDivisors T))) := (algebraMap O (Localization (Algebra.algebraMapSubmonoid O (nonZeroDivisors T)))).comp (Si i).val.toRingHom
  have hφ : ∀ g : Polynomial T, φ (algebraMap (Polynomial T) (Si i) g) =
      algebraMap (Polynomial T) (Localization (Algebra.algebraMapSubmonoid O (nonZeroDivisors T))) g := fun g => by
    simp [φ, IsScalarTower.algebraMap_apply (Polynomial T) O (Localization (Algebra.algebraMapSubmonoid O (nonZeroDivisors T)))]
  haveI h1 : (P.comap φ).IsPrime := Ideal.comap_isPrime φ P
  haveI h0 : ((⊥ : Ideal (Localization (Algebra.algebraMapSubmonoid O (nonZeroDivisors T)))).comap φ).IsPrime := Ideal.comap_isPrime φ ⊥
  have hunder : ((⊥ : Ideal (Localization (Algebra.algebraMapSubmonoid O (nonZeroDivisors T)))).comap φ).under (Polynomial T) = (P.comap φ).under (Polynomial T) := by
    ext g
    simp only [Ideal.under, Ideal.mem_comap, hφ, Ideal.mem_bot]
    constructor
    · intro h; rw [h]; exact P.zero_mem
    · intro h
      by_cases hg : g = 0
      · rw [hg, map_zero]
      · exact absurd h (hcon g hg)
  have heq := Algebra.QuasiFinite.eq_of_le_of_under_eq (R := Polynomial T) _ _
    (Ideal.comap_mono bot_le) hunder
  have hmem : (⟨o, hoi⟩ : Si i) ∈ P.comap φ := hoP
  rw [← heq, Ideal.mem_comap, Ideal.mem_bot] at hmem
  exact ho0 hmem

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.UniformTaylorBoundLeviPluriharmonicSplit
section
open Filter Topology MeasureTheory Metric ReciprocityTheory.L2DbarEstimates
open scoped ComplexOrder

namespace GlobalTheory.PluriTaylor

open Complex Set

variable {n : ℕ}

theorem smul_decomp (c : ℂ) (v : V n) : c • v = c.re • v + c.im • (I • v) := by
  ext j
  simp only [PiLp.add_apply, PiLp.smul_apply, smul_eq_mul, Complex.real_smul]
  conv_lhs => rw [← Complex.re_add_im c]
  ring

theorem vec_expand' (w : V n) : w = ∑ j, w j • bas n j := by
  have h := (EuclideanSpace.basisFun (Fin n) ℂ).sum_repr w
  simpa [bas] using h.symm

theorem sum_re_im_eq (w : V n) :
    (∑ k, ((w k).re • bas n k + (w k).im • (I • bas n k))) = w := by
  rw [Finset.sum_congr rfl fun k _ => (smul_decomp (w k) (bas n k)).symm]
  exact (vec_expand' w).symm

theorem sum_I_eq (w : V n) :
    (∑ k, ((w k).re • (I • bas n k) - (w k).im • bas n k)) = I • w := by
  have h : ∀ k, (w k).re • (I • bas n k) - (w k).im • bas n k = (I * w k) • bas n k := by
    intro k
    rw [smul_decomp (I * w k) (bas n k)]
    simp only [Complex.mul_re, Complex.mul_im, Complex.I_re, Complex.I_im, zero_mul, one_mul,
      zero_sub, zero_add, neg_smul]
    abel
  rw [Finset.sum_congr rfl fun k _ => h k]
  simp_rw [mul_smul]
  rw [← Finset.smul_sum, ← vec_expand']

noncomputable section

def lc (F : V n →L[ℝ] ℝ) (j : Fin n) : ℂ :=
  ((F (bas n j) : ℂ) - I * (F (I • bas n j) : ℂ)) / 2

def qc (B : V n →L[ℝ] V n →L[ℝ] ℝ) (j k : Fin n) : ℂ :=
  ((B (bas n j) (bas n k) : ℂ) - (B (I • bas n j) (I • bas n k) : ℂ) -
    I * ((B (bas n j) (I • bas n k) : ℂ) + (B (I • bas n j) (bas n k) : ℂ))) / 8

theorem re_holomorphicLinearTaylorCoeff_sum_eq (F : V n →L[ℝ] ℝ) (a c : Fin n → ℝ) :
    2 * (∑ j, ((a j : ℂ) + (c j : ℂ) * I) * lc F j).re =
      F (∑ k, (a k • bas n k + c k • (I • bas n k))) := by
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [map_sum, map_add (f := _), map_smul, smul_eq_mul, Complex.re_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  simp only [lc, Complex.mul_re, Complex.mul_im, Complex.add_re, Complex.add_im,
    Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im, Complex.div_ofNat_re,
    Complex.div_ofNat_im, Complex.sub_re, Complex.sub_im]
  ring

theorem re_holomorphicQuadraticTaylorCoeff_sum_eq (B : V n →L[ℝ] V n →L[ℝ] ℝ) (a c : Fin n → ℝ) :
    8 * (∑ j, ∑ k, ((a j : ℂ) + (c j : ℂ) * I) * ((a k : ℂ) + (c k : ℂ) * I) * qc B j k).re =
      B (∑ k, (a k • bas n k + c k • (I • bas n k))) (∑ k, (a k • bas n k + c k • (I • bas n k))) -
      B (∑ k, (a k • (I • bas n k) - c k • bas n k)) (∑ k, (a k • (I • bas n k) - c k • bas n k)) := by
  have e : ∀ x y : Fin n → V n, B (∑ j, x j) (∑ k, y k) = ∑ j, ∑ k, B (x j) (y k) := by
    intro x y
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum B, ContinuousLinearMap.sum_apply]
    set_option synthInstance.maxHeartbeats 100000 in
      simp_rw [map_sum]
  rw [e, e, Complex.re_sum, Finset.mul_sum, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Complex.re_sum, Finset.mul_sum, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun k _ => ?_
  simp only [map_add (f := _), map_sub, map_smul, ContinuousLinearMap.add_apply,
    ContinuousLinearMap.sub_apply, ContinuousLinearMap.smul_apply, smul_eq_mul, qc,
    Complex.mul_re, Complex.mul_im, Complex.add_re, Complex.add_im, Complex.ofReal_re,
    Complex.ofReal_im, Complex.I_re, Complex.I_im, Complex.div_ofNat_re, Complex.div_ofNat_im,
    Complex.sub_re, Complex.sub_im]
  ring

end

end GlobalTheory.PluriTaylor

namespace GlobalTheory.PluriTaylor

open Set

variable {n : ℕ}

theorem taylor_two_unif (U K : Set (V n)) (φ : V n → ℝ) (η : ℝ) (hU : IsOpen U)
    (hK : IsCompact K) (hKU : K ⊆ U) (hφ : ContDiffOn ℝ 2 φ U) (hη : 0 < η) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ z ∈ K, closedBall z δ ⊆ U ∧ ∀ w ∈ closedBall (0 : V n) δ,
      φ (z + w) ≤ φ z + fderiv ℝ φ z w + (1 / 2) * fderiv ℝ (fderiv ℝ φ) z w w + η * ‖w‖ ^ 2 := by
  obtain ⟨δ₀, hδ₀, hsub⟩ := hK.exists_cthickening_subset_open hU hKU
  have hK' : IsCompact (cthickening δ₀ K) := hK.cthickening
  have h1 : ContDiffOn ℝ 1 (fderiv ℝ φ) U := hφ.fderiv_of_isOpen hU (by norm_num)
  have h2 : ContinuousOn (fderiv ℝ (fderiv ℝ φ)) U :=
    (h1.fderiv_of_isOpen hU (m := 0) (by norm_num)).continuousOn
  obtain ⟨δ₁, hδ₁, hunif⟩ := Metric.uniformContinuousOn_iff.1
    (hK'.uniformContinuousOn_of_continuous (h2.mono hsub)) η hη
  refine ⟨min δ₀ (δ₁ / 2), lt_min hδ₀ (half_pos hδ₁), fun z hz => ?_⟩
  have hball : closedBall z (min δ₀ (δ₁ / 2)) ⊆ U :=
    (closedBall_subset_closedBall (min_le_left _ _)).trans
      ((closedBall_subset_cthickening hz δ₀).trans hsub)
  refine ⟨hball, fun w hw => ?_⟩
  rw [mem_closedBall, dist_zero_right] at hw
  set f1 := fderiv ℝ φ
  set f2 := fderiv ℝ f1
  have hpt : ∀ t ∈ Icc (0:ℝ) 1, z + t • w ∈ closedBall z (min δ₀ (δ₁ / 2)) := by
    intro t ht
    rw [mem_closedBall, dist_self_add_left, norm_smul, Real.norm_of_nonneg ht.1]
    exact (mul_le_of_le_one_left (norm_nonneg _) ht.2).trans hw
  have hnhds : ∀ t ∈ Icc (0:ℝ) 1, U ∈ 𝓝 (z + t • w) := fun t ht =>
    hU.mem_nhds (hball (hpt t ht))
  have hpath : ∀ t : ℝ, HasDerivAt (fun s : ℝ => z + s • w) w t := by
    intro t
    simpa using ((hasDerivAt_id t).smul_const w).const_add z
  have hg : ∀ t ∈ Icc (0:ℝ) 1, HasDerivAt (fun s : ℝ => φ (z + s • w)) (f1 (z + t • w) w) t := by
    intro t ht
    have hd : DifferentiableAt ℝ φ (z + t • w) :=
      (hφ.contDiffAt (hnhds t ht)).differentiableAt (by norm_num)
    exact hd.hasFDerivAt.comp_hasDerivAt t (hpath t)
  have hg1 : ∀ t ∈ Icc (0:ℝ) 1,
      HasDerivAt (fun s : ℝ => f1 (z + s • w) w) (f2 (z + t • w) w w) t := by
    intro t ht
    have hd : DifferentiableAt ℝ f1 (z + t • w) :=
      (h1.contDiffAt (hnhds t ht)).differentiableAt (by norm_num)
    have hc : HasDerivAt (fun s : ℝ => f1 (z + s • w)) (f2 (z + t • w) w) t :=
      hd.hasFDerivAt.comp_hasDerivAt t (hpath t)
    have hw0 : HasDerivAt (fun _ : ℝ => w) (0 : V n) t := hasDerivAt_const t w
    have := hc.clm_apply hw0
    simpa using this
  have hclose : ∀ t ∈ Icc (0:ℝ) 1, ‖f2 (z + t • w) - f2 z‖ ≤ η := by
    intro t ht
    have hz' : z ∈ cthickening δ₀ K := self_subset_cthickening K hz
    have hy : z + t • w ∈ cthickening δ₀ K :=
      closedBall_subset_cthickening hz δ₀
        (closedBall_subset_closedBall (min_le_left _ _) (hpt t ht))
    have hd : dist (z + t • w) z < δ₁ := by
      have := hpt t ht
      rw [mem_closedBall] at this
      linarith [min_le_right δ₀ (δ₁ / 2)]
    have := hunif _ hy _ hz' hd
    rw [dist_eq_norm] at this
    exact this.le
  have hud : ∀ t ∈ Icc (0:ℝ) 1, HasDerivWithinAt
      (fun s : ℝ => f1 (z + s • w) w - f1 z w - s * f2 z w w)
      (f2 (z + t • w) w w - f2 z w w) (Icc 0 1) t := by
    intro t ht
    have := ((hg1 t ht).sub_const (f1 z w)).sub ((hasDerivAt_id t).mul_const (f2 z w w))
    exact (this.congr_deriv (by simp)).hasDerivWithinAt
  have hbd : ∀ t ∈ Ico (0:ℝ) 1, ‖f2 (z + t • w) w w - f2 z w w‖ ≤ η * ‖w‖ ^ 2 := by
    intro t ht
    have hT := hclose t (Ico_subset_Icc_self ht)
    calc ‖f2 (z + t • w) w w - f2 z w w‖ = ‖(f2 (z + t • w) - f2 z) w w‖ := by
          simp only [ContinuousLinearMap.sub_apply]
      _ ≤ ‖f2 (z + t • w) - f2 z‖ * ‖w‖ * ‖w‖ := ContinuousLinearMap.le_opNorm₂ _ _ _
      _ ≤ η * ‖w‖ * ‖w‖ := by gcongr
      _ = η * ‖w‖ ^ 2 := by ring
  have hu : ∀ t ∈ Icc (0:ℝ) 1, ‖f1 (z + t • w) w - f1 z w - t * f2 z w w‖ ≤ η * ‖w‖ ^ 2 := by
    intro t ht
    have := norm_image_sub_le_of_norm_deriv_le_segment' hud hbd t ht
    simp only [zero_smul, add_zero, sub_self, zero_mul, sub_zero] at this
    exact this.trans (mul_le_of_le_one_right (mul_nonneg hη.le (sq_nonneg _)) ht.2)
  have hGd : ∀ t ∈ Icc (0:ℝ) 1, HasDerivWithinAt
      (fun s : ℝ => φ (z + s • w) - φ z - s * f1 z w - s ^ 2 / 2 * f2 z w w)
      (f1 (z + t • w) w - f1 z w - t * f2 z w w) (Icc 0 1) t := by
    intro t ht
    have := (((hg t ht).sub_const (φ z)).sub ((hasDerivAt_id t).mul_const (f1 z w))).sub
      (((hasDerivAt_pow 2 t).div_const 2).mul_const (f2 z w w))
    exact (this.congr_deriv (by norm_num)).hasDerivWithinAt
  have hG := norm_image_sub_le_of_norm_deriv_le_segment' hGd
    (fun t ht => hu t (Ico_subset_Icc_self ht)) 1 ⟨zero_le_one, le_rfl⟩
  simp only [one_smul, zero_smul, add_zero, one_mul, zero_mul, one_pow, sub_self, sub_zero,
    ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, zero_div, mul_one] at hG
  have hab := (Real.le_norm_self _).trans hG
  linarith

end GlobalTheory.PluriTaylor

namespace GlobalTheory.PluriTaylor

open Complex

theorem taylor_levi_unif : ∀ (n : ℕ) (U K : Set (V n)) (φ : V n → ℝ) (η : ℝ), IsOpen U →
    IsCompact K → K ⊆ U → ContDiffOn ℝ 2 φ U → 0 < η → ∃ δ : ℝ, 0 < δ ∧ ∀ z ∈ K,
      closedBall z δ ⊆ U ∧ ∃ h : V n → ℂ, Differentiable ℂ h ∧ h 0 = 0 ∧
        ∀ w ∈ closedBall (0 : V n) δ, φ (z + w) ≤ φ z + 2 * (h w).re +
          (leviV n (fun v => (φ v : ℂ)) z fun j => w j).re + η * ‖w‖ ^ 2 := by
  intro n U K φ η hU hK hKU hφ hη
  obtain ⟨δ, hδ, hT⟩ := taylor_two_unif U K φ η hU hK hKU hφ hη
  refine ⟨δ, hδ, fun z hz => ⟨(hT z hz).1, ?_⟩⟩
  have hp : ∀ j : Fin n, Differentiable ℂ (fun w : V n => w j) := fun j =>
    (EuclideanSpace.proj (𝕜 := ℂ) j).differentiable
  refine ⟨fun w => ∑ j, w j * lc (fderiv ℝ φ z) j +
      ∑ j, ∑ k, w j * w k * qc (fderiv ℝ (fderiv ℝ φ) z) j k, ?_, ?_, fun w hw => ?_⟩
  · fun_prop
  · simp
  · have hcd : ContDiffAt ℝ 2 φ z := hφ.contDiffAt (hU.mem_nhds (hKU hz))
    have h1 := re_holomorphicLinearTaylorCoeff_sum_eq (fderiv ℝ φ z) (fun j => (w j).re) (fun j => (w j).im)
    have h2 := re_holomorphicQuadraticTaylorCoeff_sum_eq (fderiv ℝ (fderiv ℝ φ) z) (fun j => (w j).re) (fun j => (w j).im)
    have h3 := ReciprocityTheory.L2DbarEstimates.Y.LocalMaximumSecondDerivative.leviV_re_eq hcd (fun j => w j)
    simp only [Complex.re_add_im, sum_re_im_eq, sum_I_eq] at h1 h2 h3
    have h4 := (hT z hz).2 w hw
    simp only [Complex.add_re]
    linarith

end GlobalTheory.PluriTaylor
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.WExactCongr
section
noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex TensorProduct GlobalTheory.EtC

namespace GlobalTheory.EtC.WExactCongr

variable {T : Type 1} [Category.{0} T]

theorem exactAt_iff {N M : T ⥤ AddCommGrpCat.{1}} (ε : N ⟶ M) {X : CosimplicialObject T}
    (hX : ∀ k, IsIso (ε.app (X.obj k))) (n : ℕ) :
    ((AlgebraicTopology.alternatingCofaceMapComplex AddCommGrpCat.{1}).obj (X ⋙ N)).ExactAt (n + 1) ↔
    ((AlgebraicTopology.alternatingCofaceMapComplex AddCommGrpCat.{1}).obj (X ⋙ M)).ExactAt (n + 1) := by
  haveI : ∀ k, IsIso ((Functor.whiskerLeft X ε).app k) := fun k => hX k
  have hw : IsIso (Functor.whiskerLeft X ε) := NatIso.isIso_of_isIso_app _
  let e := (AlgebraicTopology.alternatingCofaceMapComplex AddCommGrpCat.{1}).mapIso (@asIso _ _ _ _ (Functor.whiskerLeft X ε) hw)
  exact ⟨fun h => h.of_iso e, fun h => h.of_iso e.symm⟩

theorem wExact_iff (U : T) (X : CosimplicialObject T) (a : (CosimplicialObject.const T).obj U ⟶ X)
    (N M : T ⥤ AddCommGrpCat.{1}) (ε : N ⟶ M) (hU : IsIso (ε.app U)) (hX : ∀ k, IsIso (ε.app (X.obj k))) :
    WExact N a ↔ WExact M a := by
  have nat : ∀ {P Q : T} (f : P ⟶ Q) (x : N.obj P), M.map f (ε.app P x) = ε.app Q (N.map f x) := by
    intro P Q f x
    exact (ConcreteCategory.congr_hom (ε.naturality f) x).symm
  have surj : ∀ (P : T), IsIso (ε.app P) → ∀ (x : M.obj P), ∃ x', ε.app P x' = x := by
    intro P hP x
    refine ⟨inv (ε.app P) x, ?_⟩
    have := ConcreteCategory.congr_hom (IsIso.inv_hom_id (ε.app P)) x
    simpa using this
  have inj : ∀ (P : T), IsIso (ε.app P) → ∀ (x y : N.obj P), ε.app P x = ε.app P y → x = y := by
    intro P hP x y hxy
    have h := congrArg (inv (ε.app P)) hxy
    have hx := ConcreteCategory.congr_hom (IsIso.hom_inv_id (ε.app P)) x
    have hy := ConcreteCategory.congr_hom (IsIso.hom_inv_id (ε.app P)) y
    simp only [ConcreteCategory.comp_apply] at hx hy
    rw [hx, hy] at h
    simpa using h
  have h0 := hX (SimplexCategory.mk 0)
  have h1 := hX (SimplexCategory.mk 1)
  constructor
  · rintro ⟨i1, i2, i3⟩
    refine ⟨?_, ?_, fun n => (exactAt_iff ε hX n).1 (i3 n)⟩
    · intro x y hxy
      obtain ⟨x, rfl⟩ := surj _ hU x
      obtain ⟨y, rfl⟩ := surj _ hU y
      erw [nat, nat] at hxy
      rw [i1 (inj _ h0 _ _ hxy)]
    · intro y hy
      obtain ⟨y, rfl⟩ := surj _ h0 y
      erw [nat, nat] at hy
      obtain ⟨x, hx⟩ := i2 y (inj _ h1 _ _ hy)
      exact ⟨ε.app U x, (nat _ x).trans (congrArg _ hx)⟩
  · rintro ⟨i1, i2, i3⟩
    refine ⟨?_, ?_, fun n => (exactAt_iff ε hX n).2 (i3 n)⟩
    · intro x y hxy
      have h := congrArg (ε.app _) hxy
      erw [← nat, ← nat] at h
      exact inj _ hU _ _ (i1 h)
    · intro y hy
      have h := congrArg (ε.app _) hy
      erw [← nat, ← nat] at h
      obtain ⟨x, hx⟩ := i2 _ h
      obtain ⟨x, rfl⟩ := surj _ hU x
      erw [nat] at hx
      exact ⟨x, inj _ h0 _ _ hx⟩

end GlobalTheory.EtC.WExactCongr

theorem GlobalTheory.EtC.wExact_congr : ∀ (T : Type 1) [Category.{0} T] (U : T) (X : CosimplicialObject T)
    (a : (CosimplicialObject.const T).obj U ⟶ X) (N M : T ⥤ AddCommGrpCat.{1}) (ε : N ⟶ M),
    IsIso (ε.app U) → (∀ k, IsIso (ε.app (X.obj k))) → (WExact N a ↔ WExact M a) :=
  fun _ _ U X a N M ε hU hX => GlobalTheory.EtC.WExactCongr.wExact_iff U X a N M ε hU hX
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeightedOrbitSumEqPairOrbitSumStatement
section
open GlobalTheory.OrbitUnfold GlobalTheory.OrbitUnfold.ConjSelf
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.weightedOrbitSum_eq_pairOrbitSum : ∀ {Γ Y : Type} [Group Γ] [MulAction Γ Y] (F : Y → Γ → ℂ), (∀ (η : Γ) (y : Y) (γ : Γ), F (η • y) (η * γ * η⁻¹) = F y γ) → (∀ y : Y, (MulAction.stabilizer Γ y : Set Γ).Finite) → (∀ y : Y, (Function.support (F y)).Finite) → {o : MulAction.orbitRel.Quotient Γ Y | ∃ γ, F (Quotient.out o) γ ≠ 0}.Finite → ∑ᶠ o : MulAction.orbitRel.Quotient Γ Y, ((Nat.card (MulAction.stabilizer Γ (Quotient.out o)) : ℕ) : ℂ)⁻¹ * ∑ᶠ γ : Γ, F (Quotient.out o) γ = pairSum F := by
  first | exact @GlobalTheory.OrbitUnfold.orbitSum_eq_pairSum | exact GlobalTheory.OrbitUnfold.orbitSum_eq_pairSum | (intros; apply GlobalTheory.OrbitUnfold.orbitSum_eq_pairSum <;> assumption)
end

