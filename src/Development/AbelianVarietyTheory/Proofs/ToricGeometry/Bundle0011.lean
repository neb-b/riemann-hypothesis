module

public import Mathlib
public import ReciprocityTheory.ThetaQuasiPeriods.ThetaQuasiPeriodStatement
public import ReciprocityTheory.ThetaQuasiPeriods.Transl
public import ReciprocityTheory.ThetaQuasiPeriods.Change
public import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.DifferentiableOnOfTendstoLocallyUniformlyOn
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsFormDegreeLeHilbertDegreeEvalNeZero

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.ToricGeometry.MulVecOfRealVecAddMemSpanPeriodLattice
section
noncomputable section

open ReciprocityTheory.PTheta Complex Matrix Filter Topology
open scoped BigOperators Real

namespace GlobalTheory

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def periodCoordFst (τ : Matrix ι ι ℂ) (w : ι → ℂ) : ι → ℝ :=
  (τ.map Complex.im)⁻¹ *ᵥ fun i => (w i).im

def periodCoordSnd (τ : Matrix ι ι ℂ) (w : ι → ℂ) : ι → ℝ :=
  (fun i => (w i).re) - τ.map Complex.re *ᵥ periodCoordFst τ w

theorem continuous_periodCoordFst (τ : Matrix ι ι ℂ) : Continuous (periodCoordFst τ) := by
  unfold periodCoordFst
  exact continuous_const.matrix_mulVec (by fun_prop)

theorem continuous_periodCoordSnd (τ : Matrix ι ι ℂ) : Continuous (periodCoordSnd τ) := by
  unfold periodCoordSnd
  exact Continuous.sub (by fun_prop)
    (continuous_const.matrix_mulVec (continuous_periodCoordFst τ))

omit [DecidableEq ι] in
theorem im_mulVec_ofRealVec_add (τ : Matrix ι ι ℂ) (u v : ι → ℝ) :
    (fun i => ((τ *ᵥ ofRealVec u + ofRealVec v) i).im) = τ.map Complex.im *ᵥ u := by
  ext i
  simp [ofRealVec, Matrix.mulVec, dotProduct, Complex.im_sum]

omit [DecidableEq ι] in
theorem re_mulVec_ofRealVec_add (τ : Matrix ι ι ℂ) (u v : ι → ℝ) :
    (fun i => ((τ *ᵥ ofRealVec u + ofRealVec v) i).re) = τ.map Complex.re *ᵥ u + v := by
  ext i
  simp [ofRealVec, Matrix.mulVec, dotProduct, Complex.re_sum]

theorem periodCoordFst_apply {τ : Matrix ι ι ℂ} (hτ : IsUnit (τ.map Complex.im).det)
    (u v : ι → ℝ) : periodCoordFst τ (τ *ᵥ ofRealVec u + ofRealVec v) = u := by
  unfold periodCoordFst
  rw [im_mulVec_ofRealVec_add, Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ hτ,
    Matrix.one_mulVec]

theorem periodCoordSnd_apply {τ : Matrix ι ι ℂ} (hτ : IsUnit (τ.map Complex.im).det)
    (u v : ι → ℝ) : periodCoordSnd τ (τ *ᵥ ofRealVec u + ofRealVec v) = v := by
  unfold periodCoordSnd
  rw [periodCoordFst_apply hτ, re_mulVec_ofRealVec_add]
  abel

theorem mulVec_periodCoordFst_add_periodCoordSnd {τ : Matrix ι ι ℂ}
    (hτ : IsUnit (τ.map Complex.im).det) (w : ι → ℂ) :
    τ *ᵥ ofRealVec (periodCoordFst τ w) + ofRealVec (periodCoordSnd τ w) = w := by
  ext i
  apply Complex.ext
  · have h := congrFun
      (re_mulVec_ofRealVec_add τ (periodCoordFst τ w) (periodCoordSnd τ w)) i
    rw [h]
    simp [periodCoordSnd]
  · have h := congrFun
      (im_mulVec_ofRealVec_add τ (periodCoordFst τ w) (periodCoordSnd τ w)) i
    rw [h]
    unfold periodCoordFst
    rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ hτ, Matrix.one_mulVec]

omit [Fintype ι] [DecidableEq ι] in
theorem ofIntVec_eq_ofRealVec (n : ι → ℤ) : ofIntVec n = ofRealVec fun i => (n i : ℝ) := by
  ext i; simp [ofIntVec, ofRealVec]

theorem isUnit_det_im_of_mem_siegelH {τ : Matrix ι ι ℂ} (hτ : τ ∈ SiegelH ι) :
    IsUnit (τ.map Complex.im).det :=
  (Matrix.isUnit_iff_isUnit_det _).1 hτ.2.isUnit

theorem intVec_eq_zero_of_periodCoord_lt_one {τ : Matrix ι ι ℂ}
    (hτ : IsUnit (τ.map Complex.im).det) (n n' : ι → ℤ)
    (h₁ : ∀ i, |periodCoordFst τ (τ *ᵥ ofIntVec n + ofIntVec n') i| < 1)
    (h₂ : ∀ i, |periodCoordSnd τ (τ *ᵥ ofIntVec n + ofIntVec n') i| < 1) :
    n = 0 ∧ n' = 0 := by
  rw [ofIntVec_eq_ofRealVec n, ofIntVec_eq_ofRealVec n'] at h₁ h₂
  rw [periodCoordFst_apply hτ] at h₁
  rw [periodCoordSnd_apply hτ] at h₂
  constructor
  · ext i
    have := h₁ i
    exact Int.abs_lt_one_iff.1 (by exact_mod_cast this)
  · ext i
    have := h₂ i
    exact Int.abs_lt_one_iff.1 (by exact_mod_cast this)

theorem periodCoordFst_zero (τ : Matrix ι ι ℂ) : periodCoordFst τ 0 = 0 := by
  ext i; simp [periodCoordFst, Matrix.mulVec, dotProduct]

theorem periodCoordSnd_zero (τ : Matrix ι ι ℂ) : periodCoordSnd τ 0 = 0 := by
  ext i; simp [periodCoordSnd, periodCoordFst_zero]

theorem discreteTopology_periodLattice_of_isUnit {τ : Matrix ι ι ℂ}
    (hτ : IsUnit (τ.map Complex.im).det) : DiscreteTopology (periodLattice τ) := by
  apply discreteTopology_of_isOpen_singleton_zero
  have hO : IsOpen ((⋂ i, {w : ι → ℂ | |periodCoordFst τ w i| < 1}) ∩
      ⋂ i, {w : ι → ℂ | |periodCoordSnd τ w i| < 1}) := by
    refine IsOpen.inter (isOpen_iInter_of_finite fun i => ?_)
      (isOpen_iInter_of_finite fun i => ?_)
    · exact isOpen_lt (((continuous_apply i).comp (continuous_periodCoordFst τ)).abs)
        continuous_const
    · exact isOpen_lt (((continuous_apply i).comp (continuous_periodCoordSnd τ)).abs)
        continuous_const
  convert hO.preimage (continuous_subtype_val (p := fun w => w ∈ periodLattice τ)) using 1
  ext ⟨w, hw⟩
  simp only [Set.mem_singleton_iff, Set.mem_preimage, Set.mem_inter_iff, Set.mem_iInter,
    Set.mem_setOf_eq]
  constructor
  · intro h
    have h0 : w = 0 := congrArg Subtype.val h
    subst h0
    simp [periodCoordFst_zero, periodCoordSnd_zero]
  · rintro ⟨h₁, h₂⟩
    obtain ⟨n, n', rfl⟩ := hw
    obtain ⟨rfl, rfl⟩ := intVec_eq_zero_of_periodCoord_lt_one hτ n n' h₁ h₂
    apply Subtype.ext
    simp [ofIntVec_zero]

omit [DecidableEq ι] in
theorem mulVec_ofRealVec_add_mem_span_periodLattice (τ : Matrix ι ι ℂ) (u v : ι → ℝ) :
    τ *ᵥ ofRealVec u + ofRealVec v ∈
      Submodule.span ℝ (periodLattice τ : Set (ι → ℂ)) := by
  classical
  have e : ∀ u : ι → ℝ, ofRealVec u = ∑ j, u j • ofIntVec (Pi.single j (1 : ℤ)) := by
    intro u
    ext i
    simp [ofRealVec, ofIntVec, Finset.sum_apply, Pi.single_apply]
  refine Submodule.add_mem _ ?_ ?_
  · rw [e u, Matrix.mulVec_sum]
    refine Submodule.sum_mem _ fun j _ => ?_
    rw [Matrix.mulVec_smul]
    refine Submodule.smul_mem _ _ (Submodule.subset_span ⟨Pi.single j 1, 0, ?_⟩)
    rw [ofIntVec_zero, add_zero]
  · rw [e v]
    refine Submodule.sum_mem _ fun j _ => ?_
    refine Submodule.smul_mem _ _ (Submodule.subset_span ⟨0, Pi.single j 1, ?_⟩)
    rw [ofIntVec_zero, Matrix.mulVec_zero, zero_add]

theorem span_periodLattice_eq_top_of_isUnit {τ : Matrix ι ι ℂ}
    (hτ : IsUnit (τ.map Complex.im).det) :
    Submodule.span ℝ (periodLattice τ : Set (ι → ℂ)) = ⊤ := by
  rw [eq_top_iff]
  intro w _
  rw [← mulVec_periodCoordFst_add_periodCoordSnd hτ w]
  exact mulVec_ofRealVec_add_mem_span_periodLattice τ _ _

theorem intVec_eq_zero_of_period_eq_zero {τ : Matrix ι ι ℂ}
    (hτ : IsUnit (τ.map Complex.im).det) (n n' : ι → ℤ)
    (h : τ *ᵥ ofIntVec n + ofIntVec n' = 0) : n = 0 ∧ n' = 0 := by
  apply intVec_eq_zero_of_periodCoord_lt_one hτ n n'
  · intro i; simp [h, periodCoordFst_zero]
  · intro i; simp [h, periodCoordSnd_zero]

theorem periodLattice_isLattice_of_mem_siegelH :
    ∀ (g : ℕ) (τ : Matrix (Fin g) (Fin g) ℂ), τ ∈ SiegelH (Fin g) →
      DiscreteTopology (periodLattice τ) ∧
      Submodule.span ℝ (periodLattice τ : Set (Fin g → ℂ)) = ⊤ ∧
      ∀ n n' : Fin g → ℤ, τ *ᵥ ofIntVec n + ofIntVec n' = 0 → n = 0 ∧ n' = 0 := by
  intro g τ hτ
  have h := isUnit_det_im_of_mem_siegelH hτ
  exact ⟨discreteTopology_periodLattice_of_isUnit h, span_periodLattice_eq_top_of_isUnit h,
    intVec_eq_zero_of_period_eq_zero h⟩

end GlobalTheory
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ToricGeometry.ThetaConeIdealIsPrimeAndRingKrullDimLe
section
namespace GlobalTheory

namespace ThetaCone

open MvPolynomial Filter Topology Module ReciprocityTheory.ChartRestriction.G.AR.Up.IntPf

attribute [local instance] MvPolynomial.gradedAlgebra

section General

variable {ι E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

theorem eval_mul_of_isHomogeneous (q : ι → ℂ) (t : ℂ) {G : MvPolynomial ι ℂ} {m : ℕ}
    (hG : G.IsHomogeneous m) : eval (fun i => t * q i) G = t ^ m * eval q G := by
  rw [eval_eq, eval_eq, Finset.mul_sum]
  refine Finset.sum_congr rfl fun s hs => ?_
  have hw := hG (mem_support_iff.mp hs)
  simp only [Finsupp.weight_apply, Finsupp.sum, Pi.one_apply, smul_eq_mul, mul_one] at hw
  simp only [mul_pow, Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum, hw]
  ring

theorem differentiable_eval {φ : ι → E → ℂ} (hφ : ∀ c, Differentiable ℂ (φ c))
    (F : MvPolynomial ι ℂ) : Differentiable ℂ fun z => eval (fun c => φ c z) F := by
  apply MvPolynomial.induction_on F
  · intro a
    simp only [eval_C]
    exact differentiable_const a
  · intro p q hp hq
    simp only [map_add (f := _)]
    exact hp.add hq
  · intro p c hp
    simp only [map_mul, eval_X]
    exact hp.mul (hφ c)

theorem eq_zero_or_eq_zero_of_mul [FiniteDimensional ℂ E] {f g : E → ℂ}
    (hf : Differentiable ℂ f) (hg : Differentiable ℂ g) (h : ∀ z, f z * g z = 0) :
    (∀ z, f z = 0) ∨ ∀ z, g z = 0 := by
  by_cases hf0 : ∀ z, f z = 0
  · exact Or.inl hf0
  right
  simp only [not_forall] at hf0
  obtain ⟨a, ha⟩ := hf0

  have hev : g =ᶠ[𝓝 a] 0 := by
    filter_upwards [hf.continuous.continuousAt.eventually_ne ha] with z hz
    exact (mul_eq_zero.mp (h z)).resolve_left hz
  have hga : AnalyticOnNhd ℂ g Set.univ := GlobalTheory.SCV.analyticOnNhd_of_differentiable hg Set.univ
  have hzero := hga.eqOn_zero_of_preconnected_of_eventuallyEq_zero isPreconnected_univ
    (Set.mem_univ a) hev
  exact fun z => hzero (Set.mem_univ z)

theorem isPrime [FiniteDimensional ℂ E] {φ : ι → E → ℂ} (hφ : ∀ c, Differentiable ℂ (φ c))
    {I : Ideal (MvPolynomial ι ℂ)}
    (hI : ∀ F, F ∈ I ↔ ∀ (t : ℂ) (z : E), eval (fun c => t * φ c z) F = 0) : I.IsPrime := by
  refine Ideal.isPrime_iff.mpr ⟨fun htop => ?_, fun {F G} hFG => ?_⟩
  · have h1 := (hI 1).mp ((Ideal.eq_top_iff_one I).mp htop) 1 0
    simp at h1

  have hmul := (hI _).mp hFG
  have hψ : ∀ c, Differentiable ℂ (fun p : ℂ × E => p.1 * φ c p.2) := fun c =>
    differentiable_fst.mul ((hφ c).comp differentiable_snd)
  rcases eq_zero_or_eq_zero_of_mul (differentiable_eval hψ F) (differentiable_eval hψ G)
      (fun p => by simpa only [map_mul] using hmul p.1 p.2) with h | h
  · exact Or.inl ((hI F).mpr fun t z => h (t, z))
  · exact Or.inr ((hI G).mpr fun t z => h (t, z))

omit [NormedAddCommGroup E] [NormedSpace ℂ E] in
theorem isHomogeneous {φ : ι → E → ℂ} {I : Ideal (MvPolynomial ι ℂ)}
    (hI : ∀ F, F ∈ I ↔ ∀ (t : ℂ) (z : E), eval (fun c => t * φ c z) F = 0) :
    I.IsHomogeneous (homogeneousSubmodule ι ℂ) := by
  intro i F hF
  have hdec : ((DirectSum.decompose (homogeneousSubmodule ι ℂ) F) i : MvPolynomial ι ℂ) =
      homogeneousComponent i F := decomposition.decompose'_apply F i
  rw [hdec]
  refine (hI _).mpr fun t z => ?_
  rw [eval_mul_of_isHomogeneous (fun c => φ c z) t (homogeneousComponent_isHomogeneous i F)]
  suffices hz : eval (fun c => φ c z) (homogeneousComponent i F) = 0 by rw [hz, mul_zero]

  have hn : F.totalDegree + 1 ≤ F.totalDegree + i + 1 := by omega
  have hsum : ∑ m ∈ Finset.range (F.totalDegree + i + 1), homogeneousComponent m F = F := by
    rw [← Finset.sum_subset (Finset.range_mono hn) (fun m _ hm => by
      apply homogeneousComponent_eq_zero
      simp only [Finset.mem_range, not_lt] at hm
      omega)]
    exact sum_homogeneousComponent F
  have hP : ∀ s : ℂ, (∑ m ∈ Finset.range (F.totalDegree + i + 1),
      Polynomial.C (eval (fun c => φ c z) (homogeneousComponent m F)) * Polynomial.X ^ m).eval s
        = (0 : Polynomial ℂ).eval s := by
    intro s
    have h0 := (hI F).mp hF s z
    set_option synthInstance.maxHeartbeats 100000 in
      rw [← hsum, map_sum] at h0
    simp only [Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C,
      Polynomial.eval_pow, Polynomial.eval_X, Polynomial.eval_zero]
    rw [← h0]
    refine Finset.sum_congr rfl fun m _ => ?_
    rw [eval_mul_of_isHomogeneous (fun c => φ c z) s (homogeneousComponent_isHomogeneous m F)]
    ring
  have hc := congrArg (fun p => _root_.AddMonoidAlgebra.coeff (M := ℕ) p i) (Polynomial.funext hP)
  simp only [Polynomial.finsetSum_coeff, Polynomial.coeff_C_mul_X_pow, Polynomial.coeff_zero,
    Finset.sum_ite_eq, Finset.mem_range] at hc
  simpa [show i < F.totalDegree + i + 1 by omega] using hc

omit [NormedAddCommGroup E] [NormedSpace ℂ E] in
theorem finrank_quotPiece_le [Finite ι] {φ : ι → E → ℂ} {I : Ideal (MvPolynomial ι ℂ)}
    (hI : ∀ F, F ∈ I ↔ ∀ (t : ℂ) (z : E), eval (fun c => t * φ c z) F = 0) {d B : ℕ}
    (hB : ∀ (r : ℕ) (F : Fin r → MvPolynomial ι ℂ), (∀ k, (F k).IsHomogeneous d) →
      LinearIndependent ℂ (fun k z => eval (fun c => φ c z) (F k)) → r ≤ B) :
    finrank ℂ (quotPiece I d) ≤ B := by
  classical
  by_cases hfin : FiniteDimensional ℂ (quotPiece I d)
  swap
  · set_option synthInstance.maxHeartbeats 100000 in
    rw [Module.finrank_of_not_finite hfin]
    exact Nat.zero_le _
  let b := Module.finBasis ℂ (quotPiece I d)

  have hlift : ∀ x ∈ quotPiece I d, ∃ p ∈ homogeneousSubmodule ι ℂ d,
      (Ideal.Quotient.mkₐ ℂ I).toLinearMap p = x := by
    intro x hx
    rw [quotPiece_natCast] at hx
    exact Submodule.mem_map.mp hx
  have hmem : ∀ k, ∃ p ∈ homogeneousSubmodule ι ℂ d,
      (Ideal.Quotient.mkₐ ℂ I).toLinearMap p = (b k : MvPolynomial ι ℂ ⧸ I) :=
    fun k => hlift _ (b k).2
  choose F hFd hFb using hmem
  refine hB _ F (fun k => (mem_homogeneousSubmodule d (F k)).mp (hFd k)) ?_
  rw [Fintype.linearIndependent_iff]
  intro a ha
  have hhom : (∑ k, a k • F k).IsHomogeneous d := (mem_homogeneousSubmodule d _).mp
    (Submodule.sum_mem _ fun k _ => Submodule.smul_mem _ _ (hFd k))
  have hG : ∑ k, a k • F k ∈ I := by
    refine (hI _).mpr fun t z => ?_
    rw [eval_mul_of_isHomogeneous (fun c => φ c z) t hhom]
    have hz := congrFun ha z
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply] at hz
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum]
    simp only [smul_eval]
    rw [hz, mul_zero]
  have h0 : ∑ k, a k • b k = 0 := by
    apply Subtype.ext
    simp only [Submodule.coe_sum, Submodule.coe_smul, Submodule.coe_zero]
    set_option synthInstance.maxHeartbeats 100000 in
      simp_rw [← hFb, ← map_smul, ← map_sum]
    simp only [AlgHom.toLinearMap_apply, Ideal.Quotient.mkₐ_eq_mk]
    exact Ideal.Quotient.eq_zero_iff_mem.mpr hG
  exact (Fintype.linearIndependent_iff.mp b.linearIndependent) a h0

theorem isPrime_and_ringKrullDim_le [Finite ι] [FiniteDimensional ℂ E] {φ : ι → E → ℂ}
    (hφ : ∀ c, Differentiable ℂ (φ c)) (hne : ∃ c, φ c ≠ 0) {I : Ideal (MvPolynomial ι ℂ)}
    (hI : ∀ F, F ∈ I ↔ ∀ (t : ℂ) (z : E), eval (fun c => t * φ c z) F = 0) {g N : ℕ}
    (hB : ∀ d, 1 ≤ d → ∀ (r : ℕ) (F : Fin r → MvPolynomial ι ℂ), (∀ k, (F k).IsHomogeneous d) →
      LinearIndependent ℂ (fun k z => eval (fun c => φ c z) (F k)) → r ≤ (N * d) ^ g) :
    I.IsPrime ∧ ringKrullDim (MvPolynomial ι ℂ ⧸ I) ≤ (g + 1 : ℕ) := by
  classical
  have hprime := isPrime hφ hI
  have hhom := isHomogeneous hI
  obtain ⟨c, hc⟩ := hne
  have hX : ∃ i, X i ∉ I :=
    ⟨c, fun hmem => hc (funext fun z => by simpa using (hI _).mp hmem 1 z)⟩
  refine ⟨hprime, ?_⟩
  have := hprime
  rw [ProjCut.ringKrullDim_eq_natDegree_idealHilbertPoly hhom hX]

  have hle : (idealHilbertPoly I).degree ≤
      (Polynomial.C ((N : ℚ) ^ g) * Polynomial.X ^ g).degree := by
    apply degree_le_of_eventually_eval_nat (eventually_idealHilbertPoly_nonneg hhom)
    filter_upwards [eventually_finrank_quotPiece hhom, Filter.eventually_ge_atTop 1]
      with n hn hn1
    rw [← hn]
    have hb := finrank_quotPiece_le hI (hB n hn1)
    simp only [Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
    rw [← mul_pow]
    exact_mod_cast hb
  have hdeg : (idealHilbertPoly I).natDegree ≤ g :=
    Polynomial.natDegree_le_of_degree_le (hle.trans (Polynomial.degree_C_mul_X_pow_le _ _))
  exact_mod_cast (show (idealHilbertPoly I).natDegree + 1 ≤ g + 1 by omega)

end General

end ThetaCone

open ReciprocityTheory.PTheta Complex Matrix Filter Topology
open scoped BigOperators Real

theorem thetaConeIdeal_isPrime_and_ringKrullDim_le :
    (∀ (g : ℕ) (τ : Matrix (Fin g) (Fin g) ℂ), τ ∈ SiegelH (Fin g) → ∀ N : ℕ, 1 ≤ N → (∀ c : Fin g → Fin N, (Differentiable ℂ (fun z => theta (fun i => ((c i : ℕ) : ℝ) / N) 0 ((N : ℂ) • z) ((N : ℂ) • τ)) ∧ ∀ (n n' : Fin g → ℤ) z, (fun z => theta (fun i => ((c i : ℕ) : ℝ) / N) 0 ((N : ℂ) • z) ((N : ℂ) • τ)) (z + τ *ᵥ ofIntVec n + ofIntVec n') = eC (-(N : ℂ) * (ofIntVec n ⬝ᵥ (τ *ᵥ ofIntVec n) / 2 + ofIntVec n ⬝ᵥ z)) * (fun z => theta (fun i => ((c i : ℕ) : ℝ) / N) 0 ((N : ℂ) • z) ((N : ℂ) • τ)) z)) ∧ LinearIndependent ℂ (fun (c : Fin g → Fin N) (z : Fin g → ℂ) => theta (fun i => ((c i : ℕ) : ℝ) / N) 0 ((N : ℂ) • z) ((N : ℂ) • τ))) → (∀ (g n : ℕ) (τ : Matrix (Fin g) (Fin g) ℂ) (b : Fin g → ℂ), 1 ≤ n → (∀ j, b j ≠ 0) → ∀ (N : ℕ) (f : Fin N → (Fin g → ℂ) → ℂ), (∀ k, (Differentiable ℂ (f k) ∧ (∀ (i : Fin g) z, (f k) (z + Pi.single i 1) = (f k) z) ∧ ∀ (j : Fin g) z, (f k) (z + τ.mulVec (Pi.single j 1)) = b j ^ n * cexp (-(2 * Real.pi * I) * n * z j) * (f k) z)) → LinearIndependent ℂ f → N ≤ n ^ g) → (∀ (g : ℕ) (τ : Matrix (Fin g) (Fin g) ℂ), τ ∈ SiegelH (Fin g) → ∀ N : ℕ, 2 ≤ N → ∀ (I : Ideal (MvPolynomial (Fin g → Fin N) ℂ)), (∀ F, F ∈ I ↔ ∀ (t : ℂ) (z : Fin g → ℂ), MvPolynomial.eval (fun c => t * theta (fun i => ((c i : ℕ) : ℝ) / N) 0 ((N : ℂ) • z) ((N : ℂ) • τ)) F = 0) → I.IsPrime ∧ ringKrullDim (MvPolynomial (Fin g → Fin N) ℂ ⧸ I) ≤ (g + 1 : ℕ)) := by
  intro hA hBd g τ hτ N hN I hI
  let ψ : (Fin g → Fin N) → (Fin g → ℂ) → ℂ := fun c z =>
    theta (fun i => ((c i : ℕ) : ℝ) / N) 0 ((N : ℂ) • z) ((N : ℂ) • τ)
  have hAc := hA g τ hτ N (by omega)
  have hdiff : ∀ c, Differentiable ℂ (ψ c) := fun c => (hAc.1 c).1
  have hquasi : ∀ c (n n' : Fin g → ℤ) z, ψ c (z + τ *ᵥ ofIntVec n + ofIntVec n') =
      eC (-(N : ℂ) * (ofIntVec n ⬝ᵥ (τ *ᵥ ofIntVec n) / 2 + ofIntVec n ⬝ᵥ z)) * ψ c z :=
    fun c => (hAc.1 c).2
  have : Nonempty (Fin g → Fin N) := ⟨fun _ => ⟨0, by omega⟩⟩
  have hne : ∃ c, ψ c ≠ 0 := ⟨Classical.arbitrary _, hAc.2.ne_zero _⟩
  refine ThetaCone.isPrime_and_ringKrullDim_le (φ := ψ) (g := g) (N := N) hdiff hne hI ?_
  intro d hd r F hF hind

  have hscale : ∀ (k : Fin r) (w z : Fin g → ℂ) (l : ℂ), (∀ c, ψ c w = l * ψ c z) →
      MvPolynomial.eval (fun c => ψ c w) (F k) = l ^ d * MvPolynomial.eval (fun c => ψ c z) (F k) := by
    intro k w z l h
    rw [← ThetaCone.eval_mul_of_isHomogeneous (fun c => ψ c z) l (hF k)]
    have hfun : (fun c => ψ c w) = fun c => l * ψ c z := funext h
    rw [hfun]
  have hzero : ofIntVec (0 : Fin g → ℤ) = 0 := by
    funext i
    simp [ofIntVec]
  have hsingle : ∀ j : Fin g, ofIntVec (Pi.single j (1 : ℤ)) = (Pi.single j 1 : Fin g → ℂ) := by
    intro j
    funext i
    by_cases h : i = j
    · subst h
      simp [ofIntVec]
    · simp [ofIntVec, h]
  refine hBd g (N * d) τ (fun j => eC (-(τ j j) / 2)) (Nat.mul_pos (by omega) hd)
    (fun j => Complex.exp_ne_zero _) r (fun k z => MvPolynomial.eval (fun c => ψ c z) (F k))
    (fun k => ⟨ThetaCone.differentiable_eval hdiff (F k), fun i z => ?_, fun j z => ?_⟩) hind
  · have h := hscale k (z + Pi.single i 1) z 1 (fun c => by
      simpa [hzero, hsingle, eC] using hquasi c 0 (Pi.single i 1) z)
    simpa using h
  · have h := hscale k (z + τ.mulVec (Pi.single j 1)) z (eC (-(N : ℂ) * (τ j j / 2 + z j)))
      (fun c => by simpa [hzero, hsingle] using hquasi c (Pi.single j 1) 0 z)
    rw [h]
    congr 1
    simp only [eC, ← Complex.exp_nat_mul, ← Complex.exp_add]
    congr 1
    push_cast
    ring

end GlobalTheory
end

