module

public import Mathlib
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.Bundle0005
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovGeometry.Bundle0003
public import GroundTheory.HeightsAndTheta.Heights.Intersections.Bundle0005
public import ReciprocityTheory.AnalyticForms.MaIntEmpty
public import ReciprocityTheory.AnalyticForms.PotentialTheory.Bundle0005
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle0005
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.Bundle0010
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsSegre

@[expose] public section

-- bundled from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.ArithModel
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry

noncomputable section

set_option linter.unusedSectionVars false

namespace ProjLine

section Homog

variable {K : Type*} [Fintype K] {ι : K → Type*} [∀ k, Fintype (ι k)]

theorem isMultiHomog_one : IsMultiHomog (1 : MRing ι) 0 := by
  intro m hm k
  rw [support_one] at hm
  · rw [Finset.mem_singleton] at hm
    subst hm
    simp

theorem mhNeg {f : MRing ι} {a : K → ℕ} (hf : IsMultiHomog f a) : IsMultiHomog (-f) a := by
  intro m hm
  rw [support_neg] at hm
  exact hf m hm

theorem mhAdd {f g : MRing ι} {a : K → ℕ} (hf : IsMultiHomog f a) (hg : IsMultiHomog g a) :
    IsMultiHomog (f + g) a := by
  intro m hm
  classical
  rcases Finset.mem_union.mp (support_add hm) with h | h
  · exact hf m h
  · exact hg m h

theorem mhMul {f g : MRing ι} {a b : K → ℕ} (hf : IsMultiHomog f a) (hg : IsMultiHomog g b) :
    IsMultiHomog (f * g) (a + b) := by
  intro m hm k
  classical
  obtain ⟨m₁, hm₁, m₂, hm₂, rfl⟩ := Finset.mem_add.mp (support_mul f g hm)
  simp only [Finsupp.coe_add, Pi.add_apply, Finset.sum_add_distrib, hf m₁ hm₁ k, hg m₂ hm₂ k]

theorem isMultiHomog_X (p : Σ k, ι k) [DecidableEq K] :
    IsMultiHomog (X p : MRing ι) (fun k => if k = p.1 then 1 else 0) := by
  intro m hm k
  classical
  rw [support_X, Finset.mem_singleton] at hm
  subst hm
  obtain ⟨k₀, i₀⟩ := p
  by_cases hk : k = k₀
  · subst hk
    simp [Finsupp.single_apply]
  · simp only [hk, if_false]
    refine Finset.sum_eq_zero fun i _ => ?_
    rw [Finsupp.single_apply, if_neg]
    intro h
    exact hk (congrArg Sigma.fst h).symm

end Homog

abbrev Kfr : Type := FractionRing (MRing (GlobalTheory (Fin 2)))

abbrev Xk (i : Fin 2) : Kfr := algebraMap (MRing (GlobalTheory (Fin 2))) Kfr (X ⟨(), i⟩)

def u : Kfr := Xk 1 / Xk 0

abbrev FnField : Type := Subfield.closure ({u} : Set Kfr)

def uF : FnField := ⟨u, Subfield.subset_closure rfl⟩

def y : Ix (Fin 2) → FnField := fun p => ![1, uF] p.2

section FS

open scoped Topology

variable {J : Type} [Fintype J]

abbrev eL : (J → ℂ) →L[ℝ] EuclideanSpace ℂ J :=
  ((EuclideanSpace.equiv J ℂ).symm.toContinuousLinearMap).restrictScalars ℝ

theorem eL_apply (z : J → ℂ) : eL z = WithLp.toLp 2 z := rfl

def reInner : (J → ℂ) →L[ℝ] ((J → ℂ) →L[ℝ] ℝ) :=
  ((ContinuousLinearMap.compL ℝ (J → ℂ) (EuclideanSpace ℂ J) ℝ).flip eL).comp
    ((innerSL ℝ (E := EuclideanSpace ℂ J)).comp eL)

theorem reInner_apply (y v : J → ℂ) : reInner y v = inner ℝ (eL y) (eL v) := rfl

theorem realInner_eq (x y : EuclideanSpace ℂ J) : inner ℝ x y = RCLike.re (inner ℂ x y) := by
  set_option synthInstance.maxHeartbeats 100000 in
    rw [PiLp.inner_apply, PiLp.inner_apply, map_sum]
  exact Finset.sum_congr rfl fun i _ => real_inner_eq_re_inner ℂ _ _

def normSqE (z : J → ℂ) : ℝ := ‖eL z‖ ^ 2

theorem hasFDerivAt_normSqE (z : J → ℂ) : HasFDerivAt normSqE (2 • reInner z) z :=
  eL.hasFDerivAt.norm_sq

theorem normSqE_pos {z : J → ℂ} (hz : z ≠ 0) : 0 < normSqE z := by
  unfold normSqE
  have : eL z ≠ 0 := fun h => hz (by
    have := congrArg (fun v : EuclideanSpace ℂ J => v.ofLp) h
    simpa [eL_apply] using this)
  positivity

theorem log_fs_eq : (fun z => Real.log ((fsMetric (ι := J)).ρ z)) = fun z => (1 / 2) * Real.log (normSqE z) := by
  funext z
  change Real.log ‖WithLp.toLp 2 z‖ = _
  rw [normSqE, eL_apply, Real.log_pow]
  push_cast
  ring

theorem hasFDerivAt_log_fs {y : J → ℂ} (hy : y ≠ 0) :
    HasFDerivAt (fun z => Real.log ((fsMetric (ι := J)).ρ z)) ((normSqE y)⁻¹ • reInner y) y := by
  rw [log_fs_eq]
  have h := ((hasFDerivAt_normSqE y).log (normSqE_pos hy).ne').const_mul (1 / 2 : ℝ)
  refine h.congr_fderiv ?_
  ext v
  simp
  ring

theorem leviForm_log_fs_nonneg {z : J → ℂ} (hz : z ≠ 0) (w : J → ℂ) :
    0 ≤ leviForm (fun z => Real.log ((fsMetric (ι := J)).ρ z)) z w := by
  set G : (J → ℂ) → ((J → ℂ) →L[ℝ] ℝ) := fun y => (normSqE y)⁻¹ • reInner y with hG
  have hev : fderiv ℝ (fun z => Real.log ((fsMetric (ι := J)).ρ z)) =ᶠ[𝓝 z] G := by
    filter_upwards [isOpen_ne.mem_nhds hz] with y hy
    exact (hasFDerivAt_log_fs hy).fderiv
  have hq := normSqE_pos hz
  have hc : HasFDerivAt (fun y => (normSqE y)⁻¹) ((-(normSqE z ^ 2)⁻¹) • (2 • reInner z)) z :=
    (hasDerivAt_inv hq.ne').comp_hasFDerivAt z (hasFDerivAt_normSqE z)
  have hGd : HasFDerivAt G ((normSqE z)⁻¹ • reInner + ((-(normSqE z ^ 2)⁻¹) • (2 • reInner z)).smulRight (reInner z)) z :=
    hc.smul reInner.hasFDerivAt
  have hD : ∀ v, fderiv ℝ (fderiv ℝ (fun z => Real.log ((fsMetric (ι := J)).ρ z))) z v v =
      (normSqE z)⁻¹ * inner ℝ (eL v) (eL v) - 2 * (normSqE z ^ 2)⁻¹ * inner ℝ (eL z) (eL v) ^ 2 := by
    intro v
    rw [hev.fderiv_eq, hGd.fderiv]
    simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
      ContinuousLinearMap.smulRight_apply, smul_eq_mul, nsmul_eq_mul, reInner_apply]
    push_cast
    ring
  unfold leviForm
  rw [hD, hD]
  have hI : eL (Complex.I • w) = Complex.I • eL w := by
    rw [eL_apply, eL_apply, WithLp.toLp_smul]
  rw [hI]
  set q := normSqE z
  have hq' : q = ‖eL z‖ ^ 2 := rfl
  set c : ℂ := inner ℂ (eL z) (eL w) with hcdef
  have h1 : inner ℝ (eL w) (eL w) = ‖eL w‖ ^ 2 := real_inner_self_eq_norm_sq _
  have h2 : inner ℝ (Complex.I • eL w) (Complex.I • eL w) = ‖eL w‖ ^ 2 := by
    rw [real_inner_self_eq_norm_sq, norm_smul, Complex.norm_I, one_mul]
  have h3 : inner ℝ (eL z) (eL w) = RCLike.re c := realInner_eq _ _
  have h4 : inner ℝ (eL z) (Complex.I • eL w) = RCLike.re (Complex.I * c) := by
    rw [realInner_eq, inner_smul_right]
  simp only [h1, h2, h3, h4]
  have hcs : ‖c‖ ^ 2 ≤ q * ‖eL w‖ ^ 2 := by
    rw [hq', ← mul_pow]
    exact pow_le_pow_left₀ (norm_nonneg _) (norm_inner_le_norm _ _) 2
  have hre : RCLike.re c ^ 2 + RCLike.re (Complex.I * c) ^ 2 = ‖c‖ ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_apply]
    simp only [RCLike.re_to_complex, Complex.mul_re, Complex.I_re, Complex.I_im, zero_mul, one_mul,
      zero_sub]
    ring
  have key : 0 ≤ q⁻¹ * ‖eL w‖ ^ 2 - 2 * (q ^ 2)⁻¹ * RCLike.re c ^ 2 +
      (q⁻¹ * ‖eL w‖ ^ 2 - 2 * (q ^ 2)⁻¹ * RCLike.re (Complex.I * c) ^ 2) := by
    have h2 : q⁻¹ * ‖eL w‖ ^ 2 - 2 * (q ^ 2)⁻¹ * RCLike.re c ^ 2 +
        (q⁻¹ * ‖eL w‖ ^ 2 - 2 * (q ^ 2)⁻¹ * RCLike.re (Complex.I * c) ^ 2) =
        2 * (q ^ 2)⁻¹ * (q * ‖eL w‖ ^ 2 - ‖c‖ ^ 2) := by
      rw [← hre]
      field_simp
      ring
    rw [h2]
    have : 0 ≤ q * ‖eL w‖ ^ 2 - ‖c‖ ^ 2 := by linarith
    positivity
  linarith

theorem isSmoothMetric_fs : IsSmoothMetric (fsMetric (ι := J)) := by
  unfold IsSmoothMetric
  intro z hz
  have h : (fsMetric (ι := J)).ρ = fun z => ‖eL z‖ := rfl
  rw [h]
  have hne : eL z ≠ 0 := fun h0 => hz (by
    have := congrArg (fun v : EuclideanSpace ℂ J => v.ofLp) h0
    simpa [eL_apply] using this)
  exact ((contDiffAt_norm ℝ hne).comp z (ContinuousLinearMap.contDiff (eL (J := J))).contDiffAt).contDiffWithinAt

theorem isConjInvariant_fs : IsConjInvariant (fsMetric (ι := J)) := by
  intro z
  change ‖WithLp.toLp 2 _‖ = ‖WithLp.toLp 2 z‖
  rw [EuclideanSpace.norm_eq, EuclideanSpace.norm_eq]
  simp

end FS

end ProjLine

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PComplexTaylorTwo
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open Filter Topology Asymptotics ReciprocityTheory.AnForm Matrix Metric

noncomputable section

theorem taylor_two_isLittleO {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f : E → ℝ} {x : E} (hf : ContDiffAt ℝ 2 f x) :
    (fun z => f (x + z) - f x - fderiv ℝ f x z - fderiv ℝ (fderiv ℝ f) x z z / 2)
      =o[𝓝 0] fun z => ‖z‖ ^ 2 := by
  set L := fderiv ℝ f x
  set H := fderiv ℝ (fderiv ℝ f) x with hHdef
  have hsymm : IsSymmSndFDerivAt ℝ f x := hf.isSymmSndFDerivAt (by simp)
  have hH : HasFDerivAt (fderiv ℝ f) H x :=
    ((hf.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)).hasFDerivAt
  have ho := hasFDerivAt_iff_isLittleO_nhds_zero.1 hH
  have htend : Tendsto (fun z : E => x + z) (𝓝 0) (𝓝 x) := by
    have : Continuous fun z : E => x + z := continuous_const.add continuous_id
    simpa using this.tendsto (0 : E)
  have hdiff : ∀ᶠ z in 𝓝 (0 : E), DifferentiableAt ℝ f (x + z) :=
    htend.eventually ((hf.eventually (by simp)).mono fun y hy => hy.differentiableAt (by simp))
  refine isLittleO_iff.2 fun ε hε => ?_
  have hb := (isLittleO_iff.1 ho hε).and hdiff
  obtain ⟨δ, hδ, hball⟩ := Metric.eventually_nhds_iff_ball.1 hb
  filter_upwards [ball_mem_nhds (0 : E) hδ] with z hz
  set g : E → ℝ := fun w => f (x + w) - f x - L w - (2 : ℝ)⁻¹ • H w w with hg
  have hderiv : ∀ w ∈ ball (0 : E) δ, HasFDerivAt g (fderiv ℝ f (x + w) - L - H w) w := by
    intro w hw
    have h1 : HasFDerivAt (fun w => f (x + w)) ((fderiv ℝ f (x + w)).comp
        (ContinuousLinearMap.id ℝ E)) w :=
      (hball w hw).2.hasFDerivAt.comp w ((hasFDerivAt_id w).const_add x)
    have h2 : HasFDerivAt (fun w => H w w) ((H w).comp (ContinuousLinearMap.id ℝ E) + H.flip w) w :=
      H.hasFDerivAt.clm_apply (hasFDerivAt_id w)
    have h3 := ((h1.sub_const (f x)).sub L.hasFDerivAt).sub (h2.const_smul (2 : ℝ)⁻¹)
    refine h3.congr_fderiv ?_
    ext v
    simp only [_root_.sub_apply, ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.id_apply, _root_.smul_apply, _root_.add_apply,
      ContinuousLinearMap.flip_apply, smul_eq_mul]
    have := hsymm v w
    rw [← hHdef] at this
    rw [this]
    ring
  have hz' : ‖z‖ < δ := by simpa using hz
  have hsub : closedBall (0 : E) ‖z‖ ⊆ ball 0 δ := closedBall_subset_ball hz'
  have hbound : ∀ w ∈ closedBall (0 : E) ‖z‖, ‖fderiv ℝ f (x + w) - L - H w‖ ≤ ε * ‖z‖ := by
    intro w hw
    have hw' := (hball w (hsub hw)).1
    have hwz : ‖w‖ ≤ ‖z‖ := by simpa using hw
    calc ‖fderiv ℝ f (x + w) - L - H w‖ ≤ ε * ‖w‖ := hw'
      _ ≤ ε * ‖z‖ := by gcongr
  have hz0 : z ∈ closedBall (0 : E) ‖z‖ := by simp
  have hmvt := (convex_closedBall (0 : E) ‖z‖).norm_image_sub_le_of_norm_hasFDerivWithin_le
    (fun w hw => (hderiv w (hsub hw)).hasFDerivWithinAt) hbound
    (mem_closedBall_self (norm_nonneg z)) hz0
  have hg0 : g 0 = 0 := by simp [hg]
  rw [hg0, sub_zero, sub_zero] at hmvt
  have : g z = f (x + z) - f x - L z - H z z / 2 := by
    simp only [hg, smul_eq_mul]; ring
  rw [← this, norm_pow, norm_norm]
  calc ‖g z‖ ≤ ε * ‖z‖ * ‖z‖ := hmvt
    _ = ε * ‖z‖ ^ 2 := by ring

def complexLinearCoeffs {D : ℕ} (L : (Fin D → ℂ) →L[ℝ] ℝ) : Fin D → ℂ :=
  fun j => (L (Pi.single j 1) : ℂ) - Complex.I * (L (Complex.I • Pi.single j 1) : ℂ)

theorem re_complexLinearCoeffs_dot {D : ℕ} (L : (Fin D → ℂ) →L[ℝ] ℝ) (z : Fin D → ℂ) :
    (complexLinearCoeffs L ⬝ᵥ z).re = L z := by
  have hz : z = ∑ j, ((z j).re • (Pi.single j 1 : Fin D → ℂ) +
      (z j).im • (Complex.I • (Pi.single j 1 : Fin D → ℂ))) := by
    ext k
    apply Complex.ext <;> simp [Finset.sum_apply, Pi.single_apply, Finset.sum_add_distrib]
  conv_rhs => rw [hz]
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [map_sum, map_add (f := _), map_smul, dotProduct, Complex.re_sum, smul_eq_mul]
  refine Finset.sum_congr rfl fun j _ => ?_
  simp only [complexLinearCoeffs, Complex.mul_re, Complex.sub_re, Complex.sub_im, Complex.mul_im,
    Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im]
  ring

def complexQuadMatrix {D : ℕ} (H : (Fin D → ℂ) →L[ℝ] (Fin D → ℂ) →L[ℝ] ℝ) :
    Matrix (Fin D) (Fin D) ℂ :=
  fun j k =>
    let ej : Fin D → ℂ := Pi.single j 1
    let ek : Fin D → ℂ := Pi.single k 1
    ((H ej ek - H (Complex.I • ej) (Complex.I • ek) : ℝ) -
      Complex.I * ((H ej (Complex.I • ek) + H (Complex.I • ej) ek : ℝ))) / 4

theorem re_dot_complexQuadMatrix {D : ℕ} (H : (Fin D → ℂ) →L[ℝ] (Fin D → ℂ) →L[ℝ] ℝ)
    (z : Fin D → ℂ) :
    (z ⬝ᵥ (complexQuadMatrix H *ᵥ z)).re = (H z z - H (Complex.I • z) (Complex.I • z)) / 4 := by
  obtain ⟨c, hc⟩ : ∃ c : Fin D → (Fin D → ℂ), c = fun j => (z j).re • (Pi.single j 1 : Fin D → ℂ) +
      (z j).im • (Complex.I • (Pi.single j 1 : Fin D → ℂ)) := ⟨_, rfl⟩
  obtain ⟨d, hd⟩ : ∃ d : Fin D → (Fin D → ℂ), d = fun j =>
      (z j).re • (Complex.I • (Pi.single j 1 : Fin D → ℂ)) +
      (-(z j).im) • (Pi.single j 1 : Fin D → ℂ) := ⟨_, rfl⟩
  have hz : z = ∑ j, c j := by
    rw [hc]; ext k
    apply Complex.ext <;> simp [Finset.sum_apply, Pi.single_apply, Finset.sum_add_distrib]
  have hIz : Complex.I • z = ∑ j, d j := by
    rw [hd]; ext k
    apply Complex.ext <;> simp [Finset.sum_apply, Pi.single_apply, Finset.sum_add_distrib]
  have expand : ∀ c : Fin D → (Fin D → ℂ),
      H (Finset.sum Finset.univ c) (Finset.sum Finset.univ c) = ∑ i, ∑ k, H (c i) (c k) := by
    intro c
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [map_sum, _root_.sum_apply]
    rw [Finset.sum_comm]
  have e1 : H z z = ∑ i, ∑ k, H (c i) (c k) := by
    calc H z z = H (∑ j, c j) (∑ j, c j) := by rw [← hz]
      _ = _ := expand c
  have e2 : H (Complex.I • z) (Complex.I • z) = ∑ i, ∑ k, H (d i) (d k) := by
    rw [hIz]; exact expand d
  have hR : (z ⬝ᵥ (complexQuadMatrix H *ᵥ z)).re =
      ∑ i, ∑ k, (z i * (complexQuadMatrix H i k * z k)).re := by
    simp only [dotProduct, Matrix.mulVec, Finset.mul_sum, Complex.re_sum]
  rw [hR, e1, e2, ← Finset.sum_sub_distrib, Finset.sum_div]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← Finset.sum_sub_distrib, Finset.sum_div]
  refine Finset.sum_congr rfl fun k _ => ?_
  subst hc hd
  simp only [map_add (f := _), map_smul, _root_.add_apply, _root_.smul_apply, smul_eq_mul]
  simp only [complexQuadMatrix, Complex.mul_re, Complex.mul_im, Complex.div_ofNat_re,
    Complex.div_ofNat_im, Complex.sub_re, Complex.sub_im, Complex.ofReal_re, Complex.ofReal_im,
    Complex.I_re, Complex.I_im]
  ring

theorem ComplexTaylorTwo.proof : ComplexTaylorTwo.Statement := by
  intro D ψ y₀ hψ
  refine ⟨complexLinearCoeffs (fderiv ℝ ψ y₀), complexQuadMatrix (fderiv ℝ (fderiv ℝ ψ) y₀), ?_⟩
  refine (taylor_two_isLittleO hψ).congr_left fun z => ?_
  have h1 := re_complexLinearCoeffs_dot (fderiv ℝ ψ y₀) z
  have h2 := re_dot_complexQuadMatrix (fderiv ℝ (fderiv ℝ ψ) y₀) z
  have h3 := ReciprocityTheory.AnForm.M.re_star_dot_hessC ψ y₀ (star z)
  rw [star_star] at h3
  rw [Complex.add_re, h1, h2, h3]
  unfold levi
  ring

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsComponentsMeetNull
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial MeasureTheory ReciprocityTheory.ChartRestriction.G.Geo

noncomputable section

def ComponentsMeetNull.Statement : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (P : Ideal (MRing ι)) (e : ℕ)
    (Ψ : (((k : K) → ι k) → ℂ) →ₗ[ℂ] (Fin (e + 1) → ℂ)) (S : Finset (Ideal (MvPolynomial (Σ k, ι k) ℂ))),
    IsArithVar P (e + 1) → IsGoodProj P Ψ →
    (∀ W ∈ S, W ∈ (P.map (MvPolynomial.map (Int.castRingHom ℂ))).minimalPrimes) →
    volume {y : Fin e → ℂ | ∃ z ∈ mcPts P, Ψ (segre z) = Fin.cons 1 y ∧
      ∃ W ∈ S, ∃ W' ∈ S, W ≠ W' ∧ z ∈ zeroLocus ℂ W ∧ z ∈ zeroLocus ℂ W'} = 0

section Inhabitants

open GroundTheory.Heights₂.Heights.Inter

end Inhabitants

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsSegreDimGe
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial GroundTheory.Heights₂.Heights.NumbersDVR

noncomputable section

def SegreDimGe.Statement : Prop :=
  ∀ (F : Type) [Field F] (K : Type) [Fintype K] [DecidableEq K] [Nonempty K] (ι : K → Type)
    [∀ k, Fintype (ι k)] (q : Ideal (MRing ι F)) (e : ℕ), IsMultiProjPrime q →
    ringKrullDim (MRing ι F ⧸ q) = ((e + Fintype.card K : ℕ) : WithBot ℕ∞) →
    ((e + 1 : ℕ) : WithBot ℕ∞) ≤
      ringKrullDim (MRing (fun _ : Unit => ∀ k, ι k) F ⧸ segrePrime F q)

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsSegreHilb
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial GroundTheory.Heights₂.Heights.NumbersDVR

noncomputable section

def SegreHilb.Statement : Prop :=
  ∀ (F : Type) [Field F] (K : Type) [Fintype K] [DecidableEq K] [Nonempty K] (ι : K → Type)
    [∀ k, Fintype (ι k)] (q : Ideal (MRing ι F)) (n : ℤ),
    hilbFn (segrePrime F q) (fun _ : Unit => n) = hilbFn q (fun _ : K => n)

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsSegrePrime
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial GroundTheory.Heights₂.Heights.NumbersDVR

noncomputable section

def SegrePrime.Statement : Prop :=
  ∀ (F : Type) [Field F] (K : Type) [Fintype K] [DecidableEq K] [Nonempty K] (ι : K → Type)
    [∀ k, Fintype (ι k)] (q : Ideal (MRing ι F)), IsMultiProjPrime q →
    IsMultiProjPrime (segrePrime F q)

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

