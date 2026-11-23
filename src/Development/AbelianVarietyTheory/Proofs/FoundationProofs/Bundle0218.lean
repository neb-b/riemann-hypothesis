module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Foundations.NormSumPairRankZeroOfCurveCoordNorm
public import Formalism.PairingDivisors.StatementH
public import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.CsGlob
public import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.CsSpan
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0212
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0013
public import Formalism.LocalToGlobal.Columns.CoefficientsModP.PairingNondegenerateHolds
public import Formalism.LocalToGlobal.Columns.CoefficientsModP.FkPderivBlockEmbNe
public import Formalism.GradedWeylDivisibility.StatementE
public import Formalism.HarderNarasimhan.ShiftInvariance
public import Formalism.QuotientMetricDivisors.ReductionLemmaZero
public import Formalism.QuotientMetricDivisors.Bundle0001
public import Formalism.LocalToGlobal.IndefiniteForms.IndefiniteTree.RealCubicMeans.LeafBounds.MeanMaxLeaf.LeafMMFree
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0216

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.CmFiniteAdeleStrongApproxModAdelicIdeal
section
open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum
open scoped BigOperators Pointwise

namespace GlobalTheory.AdelicApprox

variable (D : D7)

theorem levelC_natCast (n : ℕ) : Formalism.UG.P.levelafC D.host.E (n : 𝓞 ℚ) = (n : AE D) := by
  rw [← Formalism.UG.P.adelstab_incl_C, map_natCast, map_natCast]

theorem exists_denom (x : AE D) : ∃ n : ℕ, 0 < n ∧ (n : AE D) * x ∈ OhE D := by
  obtain ⟨d, hd, hx⟩ := Formalism.UG.P.levelaf_denom x
  obtain ⟨c, hc⟩ := Ideal.mem_span_singleton'.1 (Ideal.absNorm_mem (Ideal.span {d}))
  refine ⟨Ideal.absNorm (Ideal.span {d}), Nat.pos_of_ne_zero ?_, ?_⟩
  · simpa [Ideal.absNorm_eq_zero_iff] using hd
  · rw [← levelC_natCast, ← hc, Formalism.UG.P.levelafC_mul, mul_assoc]
    exact mul_mem (Formalism.UG.P.levelafC_mem c) hx

theorem exists_approx (n : ℕ) (hn : 0 < n) (s : AE D) (hs : s ∈ OhE D) :
    ∃ r : D.host.E, ∃ w ∈ OhE D, s = inc D r + (n : AE D) * w := by
  rw [← levelC_natCast]
  obtain ⟨b, t, ht, h⟩ := Formalism.UG.P.csGlob_approx Formalism.UG.P.csGlob_intAdApprox (n : 𝓞 ℚ)
    (Nat.cast_ne_zero.2 hn.ne') s hs
  exact ⟨_, t, ht, h⟩

theorem one_mem_inverse_halfDifferent : (1 : D.host.E) ∈ (D.host.AA0 : Submodule (𝓞 D.host.E) D.host.E) := by
  have hne : differentIdeal (𝓞 D.host.K) (𝓞 D.host.E) ≠ ⊥ := differentIdeal_ne_bot
  have hspec : differentIdeal (𝓞 D.host.K) (𝓞 D.host.E) =
      D.host.𝔟 * (D.host.conj • D.host.𝔟) := D.host.𝔟_spec.1
  rw [hspec] at hne
  have hB : ((D.host.𝔟 : Ideal (𝓞 D.host.E)) :
      FractionalIdeal (nonZeroDivisors (𝓞 D.host.E)) D.host.E) ≠ 0 := by
    rw [Ne, FractionalIdeal.coeIdeal_eq_zero]; rintro h; exact hne (by rw [h]; simp)
  rw [FractionalIdeal.mem_coe]
  unfold Host.AA0
  rw [FractionalIdeal.mem_inv_iff hB]
  intro y hy
  rw [one_mul]
  exact FractionalIdeal.coeIdeal_le_one hy

theorem mul_mem_IhE (cc : Ideal (𝓞 D.host.K)) (s : AE D) (hs : s ∈ OhE D) (t : AE D)
    (ht : t ∈ IhE D cc) : s * t ∈ IhE D cc := by
  unfold IhE at ht
  induction ht using AddSubgroup.closure_induction with
  | mem x hx =>
    obtain ⟨c, hc, a, ha, u, hu, rfl⟩ := hx
    exact AddSubgroup.subset_closure ⟨c, hc, a, ha, s * u, mul_mem hs hu, by ring⟩
  | zero => rw [mul_zero]; exact zero_mem _
  | add x y _ _ hx hy => rw [mul_add]; exact add_mem hx hy
  | neg x _ hx => rw [mul_neg]; exact neg_mem hx

theorem absNorm_mul_mem_IhE (cc : Ideal (𝓞 D.host.K)) (s : AE D) (hs : s ∈ OhE D) :
    (Ideal.absNorm cc : AE D) * s ∈ IhE D cc := by
  refine AddSubgroup.subset_closure ⟨_, Ideal.absNorm_mem cc, 1, one_mem_inverse_halfDifferent D, s, hs, ?_⟩
  simp

theorem approx_mod_ideal : ∀ (D : D7) (cc : Ideal (𝓞 D.host.K)), cc ≠ ⊥ →
    (∀ (y : AE D) (m : ℕ), 0 < m → ∃ e : D.host.E, ∃ t ∈ IhE D cc,
      inc D e - y = (m : AE D) * t) ∧
    (∀ y : AE D, ∃ n : ℕ, 0 < n ∧ (n : AE D) * y ∈ OhE D) ∧
    (∀ s ∈ OhE D, ∀ t ∈ IhE D cc, s * t ∈ IhE D cc) := by
  intro D cc hcc
  refine ⟨fun y m hm => ?_, exists_denom D, mul_mem_IhE D cc⟩
  obtain ⟨k, hk, hy⟩ := exists_denom D y
  have hn : 0 < Ideal.absNorm cc :=
    Nat.pos_of_ne_zero (by rwa [Ne, Ideal.absNorm_eq_zero_iff])
  obtain ⟨r, w, hw, h⟩ := exists_approx D (k * m * Ideal.absNorm cc)
    (Nat.mul_pos (Nat.mul_pos hk hm) hn) _ hy
  refine ⟨(k : D.host.E)⁻¹ * r, _, absNorm_mul_mem_IhE D cc (-w) (neg_mem hw), ?_⟩
  have hu : inc D (k : D.host.E)⁻¹ * (k : AE D) = 1 := by
    rw [← map_natCast (inc D), ← map_mul, inv_mul_cancel₀ (Nat.cast_ne_zero.2 hk.ne'), map_one]
  rw [map_mul]
  push_cast at h
  linear_combination (-inc D (k : D.host.E)⁻¹) * h +
    (y - (m : AE D) * (Ideal.absNorm cc : AE D) * w) * hu

end GlobalTheory.AdelicApprox
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.CoordsAlongOrthonormalRealSubfieldBasis
section
open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum
open scoped BigOperators

namespace GlobalTheory.OnCoord
variable {D : D7}

theorem embT_conj (τ : D.what₂.Tau) (x : D.host.E) :
    embT D τ (D.host.conj x) = starRingEnd ℂ (embT D τ x) :=
  D.host.conjE_apply (embT D τ) x

theorem coord_emb (h : admG1 D) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) {N N' r : ℕ}
    (b : Fin r → Matrix (Fin N') (Fin N) D.host.E) (k : Fin r) (y : Matrix (Fin N') (Fin N) D.host.E) :
    coordB D (tor0 D cc δ) b k (embV D (tor0 D cc δ) y) =
      D.host.φ₀ ((hYY D y (b k) : D.host.K) : D.host.E) := by
  unfold hYY
  rw [← h.2]
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [coordB, embV, tor0, map_sum, map_mul, embT_conj]

theorem coord_add (T : Tor D) {N N' r : ℕ}
    (b : Fin r → Matrix (Fin N') (Fin N) D.host.E) (k : Fin r) (z w : VC D N N') :
    coordB D T b k (z + w) = coordB D T b k z + coordB D T b k w := by
  simp only [coordB, Pi.add_apply, add_mul, Finset.sum_add_distrib]

theorem coord_smul (T : Tor D) {N N' r : ℕ}
    (b : Fin r → Matrix (Fin N') (Fin N) D.host.E) (k : Fin r) (c : ℂ) (z : VC D N N') :
    coordB D T b k (c • z) = c * coordB D T b k z := by
  simp only [coordB, Pi.smul_apply, smul_eq_mul, Finset.mul_sum, mul_assoc]

noncomputable def coordL (T : Tor D) {N N' r : ℕ}
    (b : Fin r → Matrix (Fin N') (Fin N) D.host.E) (k : Fin r) : VC D N N' →ₗ[ℂ] ℂ where
  toFun := coordB D T b k
  map_add' := coord_add T b k
  map_smul' := coord_smul T b k

theorem coord_sum (T : Tor D) {N N' r : ℕ}
    (b : Fin r → Matrix (Fin N') (Fin N) D.host.E) (k : Fin r) {ι : Type} (s : Finset ι) (z : ι → VC D N N') :
    coordB D T b k (∑ i ∈ s, z i) = ∑ i ∈ s, coordB D T b k (z i) :=
  map_sum (coordL T b k) z s

theorem embT_injective : Function.Injective (embT D) := by
  intro τ τ' h
  apply D.eTau.injective
  apply Subtype.ext
  have h1 : D.host.sigmaOf (D.eTau τ : D.R.GG) = D.host.sigmaOf (D.eTau τ' : D.R.GG) := by
    ext x
    have := DFunLike.congr_fun h x
    exact D.host.φ₀.injective this
  exact (D.host.gal).symm.injective h1

theorem indep (c : D.what₂.Tau → ℂ) (h : ∀ x, ∑ τ, embT D τ x * c τ = 0) (τ : D.what₂.Tau) : c τ = 0 := by
  have h1 := (linearIndependent_monoidHom D.host.E ℂ).comp (fun τ => (embT D τ : D.host.E →* ℂ))
    (fun τ τ' h => embT_injective (RingHom.coe_monoidHom_injective h))
  refine Fintype.linearIndependent_iff.1 h1 c ?_ τ
  funext x
  simpa [Finset.sum_apply, mul_comm] using h x

theorem lin_eq_zero (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) {N N' : ℕ} (f : VC D N N' →ₗ[ℂ] ℂ)
    (h : ∀ y, f (embV D (tor0 D cc δ) y) = 0) (z : VC D N N') : f z = 0 := by
  have h1 : ∀ τ i j, f (coordV D (τ, i, j)) = 0 := by
    intro τ i j
    refine indep (fun τ => f (coordV D (τ, i, j))) (fun x => ?_) τ
    rw [← h (Matrix.single i j x)]
    have : embV D (tor0 D cc δ) (Matrix.single i j x) = ∑ τ, embT D τ x • coordV D (τ, i, j) := by
      funext τ' i' j'
      simp only [embV, tor0, coordV, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Matrix.single_apply]
      by_cases hi : i = i' ∧ j = j'
      · obtain ⟨rfl, rfl⟩ := hi
        simp
      · have : ¬ (i' = i ∧ j' = j) := fun h => hi ⟨h.1.symm, h.2.symm⟩
        simp [hi, this]
    set_option synthInstance.maxHeartbeats 100000 in
      rw [this, map_sum]
    simp
  have h2 : z = ∑ τ, ∑ i, ∑ j, z τ i j • coordV D (τ, i, j) := by
    funext τ' i' j'
    simp [coordV, Finset.sum_apply, ite_and]
  rw [h2]
  set_option synthInstance.maxHeartbeats 100000 in
    simp [map_sum, h1]

theorem embV_add (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) {N N' : ℕ} (x y : Matrix (Fin N') (Fin N) D.host.E) :
    embV D (tor0 D cc δ) (x + y) = embV D (tor0 D cc δ) x + embV D (tor0 D cc δ) y := by
  funext τ i j
  simp [embV, tor0]

theorem embV_smul (h : admG1 D) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) {N N' : ℕ} (a : D.host.K)
    (y : Matrix (Fin N') (Fin N) D.host.E) :
    embV D (tor0 D cc δ) (a • y) = D.host.φ₀ (a : D.host.E) • embV D (tor0 D cc δ) y := by
  funext τ i j
  have : (a • y) i j = (a : D.host.E) * y i j := rfl
  simp only [embV, tor0, this, map_mul, h.1 τ a, Pi.smul_apply, smul_eq_mul]

theorem coords_of_orthonormal_basis : ∀ (D : D7), admG1 D → ∀ (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (N N' r : ℕ) (b : Fin r → Matrix (Fin N') (Fin N) D.host.E), OnB D b → (∀ z : VC D N N', z = ∑ k, coordB D (tor0 D cc δ) b k z • embV D (tor0 D cc δ) (b k)) ∧ (∀ j k, coordB D (tor0 D cc δ) b j (embV D (tor0 D cc δ) (b k)) = if k = j then 1 else 0) ∧ (∀ z w : VC D N N', ∑ τ, ∑ i, ∑ j, z τ i j * (starRingEnd ℂ) (w τ i j) = ∑ k, coordB D (tor0 D cc δ) b k z * (starRingEnd ℂ) (coordB D (tor0 D cc δ) b k w)) ∧ (∀ x : VC D N N', x ∈ LaB D (tor0 D cc δ) b ↔ ∀ k, coordB D (tor0 D cc δ) b k x ∈ (lamOf D cc δ)) ∧ Function.Bijective (fun (z : VC D N N') (k : Fin r) => coordB D (tor0 D cc δ) b k z) := by
  intro D h cc δ N N' r b hb
  have h2 : ∀ j k, coordB D (tor0 D cc δ) b j (embV D (tor0 D cc δ) (b k)) = if k = j then 1 else 0 := by
    intro j k
    rw [coord_emb h, hb.1 k j]
    split_ifs <;> simp
  have hc : ∀ (c : Fin r → ℂ) j,
      coordB D (tor0 D cc δ) b j (∑ k, c k • embV D (tor0 D cc δ) (b k)) = c j := by
    intro c j
    simp [coord_sum, coord_smul, h2]
  let P : VC D N N' →ₗ[ℂ] VC D N N' :=
    ∑ k, (coordL (tor0 D cc δ) b k).smulRight (embV D (tor0 D cc δ) (b k))
  have hP : ∀ z, P z = ∑ k, coordB D (tor0 D cc δ) b k z • embV D (tor0 D cc δ) (b k) := by
    intro z
    simp only [P, LinearMap.sum_apply, LinearMap.smulRight_apply]
    rfl
  have hE : ∀ y, P (embV D (tor0 D cc δ) y) = embV D (tor0 D cc δ) y := by
    intro y
    have hy : y ∈ Submodule.span D.host.K (Set.range b) := hb.2 ▸ Submodule.mem_top
    induction hy using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨j, rfl⟩ := hx
      rw [hP]
      simp [h2]
    | zero =>
      have : embV D (tor0 D cc δ) (0 : Matrix (Fin N') (Fin N) D.host.E) = 0 := by
        funext τ i j
        simp [embV, tor0]
      rw [this, map_zero]
    | add x y _ _ hx hy => rw [embV_add, map_add (f := _), hx, hy]
    | smul a x _ hx => rw [embV_smul h, map_smul, hx]
  have h1 : ∀ z : VC D N N', z = ∑ k, coordB D (tor0 D cc δ) b k z • embV D (tor0 D cc δ) (b k) := by
    intro z
    rw [← hP]
    funext τ i j
    let e : VC D N N' →ₗ[ℂ] ℂ :=
      { toFun := fun z => z τ i j, map_add' := fun _ _ => rfl, map_smul' := fun _ _ => rfl }
    have := lin_eq_zero cc δ (e ∘ₗ (LinearMap.id - P)) (fun y => by
      simp only [LinearMap.comp_apply, LinearMap.sub_apply, hE, LinearMap.id_apply, sub_self, map_zero]) z
    simp only [LinearMap.comp_apply, LinearMap.sub_apply, LinearMap.id_apply, map_sub] at this
    exact sub_eq_zero.1 this
  refine ⟨h1, h2, fun z w => ?_, fun x => ⟨fun hx k => ?_, fun hx => ?_⟩, fun z w hzw => ?_, fun c => ?_⟩
  · have hw : ∀ τ i j, w τ i j = ∑ k, coordB D (tor0 D cc δ) b k w * (tor0 D cc δ).emb τ (b k i j) := by
      intro τ i j
      have := congrFun (congrFun (congrFun (h1 w) τ) i) j
      simpa [Finset.sum_apply, embV] using this
    obtain ⟨c, hcw⟩ : ∃ c : Fin r → ℂ, ∀ k, coordB D (tor0 D cc δ) b k w = c k := ⟨_, fun _ => rfl⟩
    simp only [hcw] at hw ⊢
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [hw, map_sum, map_mul, Finset.mul_sum, coordB, Finset.sum_mul]
    rw [Finset.sum_comm (s := (Finset.univ : Finset (Fin r)))]
    refine Finset.sum_congr rfl fun τ _ => ?_
    rw [Finset.sum_comm (s := (Finset.univ : Finset (Fin r)))]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.sum_comm (s := (Finset.univ : Finset (Fin r)))]
    refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun k _ => by ring
  · induction hx using AddSubgroup.closure_induction generalizing k with
    | mem x hx =>
      obtain ⟨w, hw, j, rfl⟩ := hx
      rw [coord_smul, h2]
      split_ifs
      · rw [mul_one]; exact hw
      · rw [mul_zero]; exact zero_mem _
    | zero =>
      have : coordB D (tor0 D cc δ) b k 0 = 0 := map_zero (coordL (tor0 D cc δ) b k)
      rw [this]; exact zero_mem _
    | add x y _ _ hx hy => rw [coord_add]; exact add_mem (hx k) (hy k)
    | neg x _ hx =>
      have : coordB D (tor0 D cc δ) b k (-x) = - coordB D (tor0 D cc δ) b k x :=
        map_neg (coordL (tor0 D cc δ) b k) x
      rw [this]; exact neg_mem (hx k)
  · rw [h1 x]
    exact sum_mem fun k _ => AddSubgroup.subset_closure ⟨_, hx k, k, rfl⟩
  · rw [h1 z, h1 w]
    exact Finset.sum_congr rfl fun k _ => by rw [show coordB D (tor0 D cc δ) b k z = coordB D (tor0 D cc δ) b k w from congrFun hzw k]
  · exact ⟨_, funext (hc c)⟩

end GlobalTheory.OnCoord
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.DifferentiableComb
section
open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum
open scoped BigOperators

noncomputable section

namespace GlobalTheory.GalTheta

variable (D : D7) (T : Tor D) {N N' : ℕ}

theorem Hf_add_left (x y z : VC D N N') : Hf D T (x + y) z = Hf D T x z + Hf D T y z := by
  simp only [Hf, Pi.add_apply, add_mul, Finset.sum_add_distrib, add_div]

theorem Hf_add_right (x y z : VC D N N') : Hf D T x (y + z) = Hf D T x y + Hf D T x z := by
  simp only [Hf, Pi.add_apply, map_add (f := _), mul_add, Finset.sum_add_distrib, add_div]

theorem Hf_smul_left (c : ℂ) (x y : VC D N N') : Hf D T (c • x) y = c * Hf D T x y := by
  simp only [Hf, Pi.smul_apply, smul_eq_mul, mul_assoc, ← Finset.mul_sum, mul_div_assoc]

theorem Hf_conj (x y : VC D N N') : (starRingEnd ℂ) (Hf D T x y) = Hf D T y x := by
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [Hf, map_div₀, map_sum, map_mul, Complex.conj_conj, Complex.conj_ofReal, mul_comm]

theorem Hf_smul_right (c : ℂ) (x y : VC D N N') : Hf D T x (c • y) = (starRingEnd ℂ) c * Hf D T x y := by
  rw [← Hf_conj D T (c • y) x, Hf_smul_left, map_mul, Hf_conj]

theorem Hf_zero_right (y : VC D N N') : Hf D T y 0 = 0 := by simp [Hf]

theorem Hf_nsmul_left (n : ℕ) (x y : VC D N N') : Hf D T (n • x) y = n * Hf D T x y := by
  rw [← Nat.cast_smul_eq_nsmul ℂ, Hf_smul_left]

theorem Hf_nsmul_right (n : ℕ) (x y : VC D N N') : Hf D T x (n • y) = n * Hf D T x y := by
  rw [← Nat.cast_smul_eq_nsmul ℂ, Hf_smul_right, Complex.conj_natCast]

theorem Hf_im_swap (x y : VC D N N') : (Hf D T y x).im = -(Hf D T x y).im := by
  rw [← Hf_conj D T x y, Complex.conj_im]

theorem Hf_re_swap (x y : VC D N N') : (Hf D T y x).re = (Hf D T x y).re := by
  rw [← Hf_conj D T x y, Complex.conj_re]

theorem U_zero (G : VC D N N' → ℂ) : U D T 0 G = G := by
  funext z; simp [U, Hf_zero_right]

theorem U_U (x y : VC D N N') (G : VC D N N' → ℂ) (z : VC D N N') :
    U D T x (U D T y G) z =
      Complex.exp (-(Real.pi : ℂ) * Complex.I * ((Hf D T x y).im : ℂ)) * U D T (x + y) G z := by
  have h : Hf D T y x = Hf D T x y - 2 * Complex.I * ((Hf D T x y).im : ℂ) := by
    rw [← Hf_conj D T x y]
    apply Complex.ext <;> simp
    ring
  simp only [U, Hf_add_left, Hf_add_right, add_assoc]
  rw [h, mul_assoc, ← Complex.exp_add, mul_left_comm, ← Complex.exp_add]
  congr 2
  ring

theorem U_mul (x : VC D N N') (a : ℂ) (G : VC D N N' → ℂ) (z : VC D N N') :
    U D T x (fun w => a * G w) z = a * U D T x G z := by
  simp only [U, mul_assoc]

theorem U_sum {ι : Type*} (s : Finset ι) (x : VC D N N') (G : ι → VC D N N' → ℂ) (z : VC D N N') :
    U D T x (fun w => ∑ i ∈ s, G i w) z = ∑ i ∈ s, U D T x (G i) z := by
  simp only [U, Finset.sum_mul]

theorem differentiable_Hf (x : VC D N N') : Differentiable ℂ (fun z : VC D N N' => Hf D T z x) := by
  unfold Hf
  fun_prop

theorem differentiable_U (x : VC D N N') {G : VC D N N' → ℂ} (hG : Differentiable ℂ G) :
    Differentiable ℂ (U D T x G) := by
  have h := differentiable_Hf D T x
  unfold U
  fun_prop

theorem differentiable_comb {k : ℕ} (c : Fin k → ℂ) (t : Fin k → VC D N N') {G : VC D N N' → ℂ}
    (hG : Differentiable ℂ G) : Differentiable ℂ (comb D T c t G) := by
  have h := fun i => differentiable_U D T (t i) hG
  unfold comb
  fun_prop

def pad (m : ℕ) (z : VC D N N') : VC D (N + m) N' := fun τ a => Fin.append (z τ a) (0 : Fin m → ℂ)

def padM (m : ℕ) (A : Matrix (Fin N') (Fin N) D.host.E) : Matrix (Fin N') (Fin (N + m)) D.host.E :=
  fun a => Fin.append (A a) (0 : Fin m → D.host.E)

@[simp] theorem pad_left (m : ℕ) (z : VC D N N') (τ a) (i : Fin N) : pad D m z τ a (Fin.castAdd m i) = z τ a i := by
  simp [pad]

@[simp] theorem pad_right (m : ℕ) (z : VC D N N') (τ a) (i : Fin m) : pad D m z τ a (Fin.natAdd N i) = 0 := by
  simp [pad]

def padL (m : ℕ) : VC D N N' →ₗ[ℂ] VC D (N + m) N' where
  toFun := pad D m
  map_add' x y := by
    funext τ a i
    refine Fin.addCases (fun i => ?_) (fun i => ?_) i <;> simp
  map_smul' c x := by
    funext τ a i
    refine Fin.addCases (fun i => ?_) (fun i => ?_) i <;> simp

theorem padL_apply (m : ℕ) (z : VC D N N') : padL D m z = pad D m z := rfl

theorem pad_add (m : ℕ) (x y : VC D N N') : pad D m (x + y) = pad D m x + pad D m y := (padL D m).map_add x y

theorem pad_smul (m : ℕ) (c : ℂ) (x : VC D N N') : pad D m (c • x) = c • pad D m x := (padL D m).map_smul c x

theorem pad_nsmul (m n : ℕ) (x : VC D N N') : pad D m (n • x) = n • pad D m x := map_nsmul (padL D m) n x

theorem pad_zero (m : ℕ) : pad D m (0 : VC D N N') = 0 := (padL D m).map_zero

theorem pad_sum {ι : Type*} (s : Finset ι) (m : ℕ) (x : ι → VC D N N') :
    pad D m (∑ i ∈ s, x i) = ∑ i ∈ s, pad D m (x i) := map_sum (padL D m) x s

theorem differentiable_pad (m : ℕ) : Differentiable ℂ (pad D m : VC D N N' → VC D (N + m) N') :=
  (LinearMap.toContinuousLinearMap (padL D m)).differentiable

theorem pad_embV (h0 : ∀ τ, T.emb τ 0 = 0) (m : ℕ) (A : Matrix (Fin N') (Fin N) D.host.E) :
    pad D m (embV D T A) = embV D T (padM D m A) := by
  funext τ a i
  refine Fin.addCases (fun i => ?_) (fun i => ?_) i <;> simp [embV, padM, h0]

theorem Hf_pad (m : ℕ) (x y : VC D N N') : Hf D T (pad D m x) (pad D m y) = Hf D T x y := by
  simp [Hf, Fin.sum_univ_add]

theorem U_pad (m : ℕ) (x : VC D N N') (G : VC D (N + m) N' → ℂ) :
    U D T x (fun z => G (pad D m z)) = fun z => U D T (pad D m x) G (pad D m z) := by
  funext z
  simp only [U, Hf_pad, pad_add]

theorem wdPh_pad (m : ℕ) (x : VC D N N') : wdPh D T (pad D m x) = wdPh D T x := by
  simp only [wdPh, qH, Hf_pad]

theorem comb_pad (m : ℕ) {k : ℕ} (c : Fin k → ℂ) (t : Fin k → VC D N N') (G : VC D (N + m) N' → ℂ) :
    comb D T c t (fun z => G (pad D m z)) = fun z => comb D T c (fun i => pad D m (t i)) G (pad D m z) := by
  funext z
  simp only [comb, U_pad]

def IsTr (A : AddSubgroup (VC D N N')) (F G : VC D N N' → ℂ) : Prop :=
  ∃ (k : ℕ) (c : Fin k → ℂ) (t : Fin k → VC D N N') (m : ℕ), 0 < m ∧ (∀ i, m • t i ∈ A) ∧ G = comb D T c t F

theorem IsTr.trans {A : AddSubgroup (VC D N N')} {F G H : VC D N N' → ℂ} (h₁ : IsTr D T A F G)
    (h₂ : IsTr D T A G H) : IsTr D T A F H := by
  obtain ⟨k, c, t, m, hm, ht, rfl⟩ := h₁
  obtain ⟨k', c', t', m', hm', ht', rfl⟩ := h₂
  refine ⟨k' * k, fun p => c' (finProdFinEquiv.symm p).1 * c (finProdFinEquiv.symm p).2 *
      Complex.exp (-(Real.pi : ℂ) * Complex.I *
        ((Hf D T (t' (finProdFinEquiv.symm p).1) (t (finProdFinEquiv.symm p).2)).im : ℂ)),
    fun p => t' (finProdFinEquiv.symm p).1 + t (finProdFinEquiv.symm p).2, m * m', Nat.mul_pos hm hm', ?_, ?_⟩
  · intro p
    rw [smul_add]
    refine A.add_mem ?_ ?_
    · rw [mul_smul]; exact A.nsmul_mem (ht' _) _
    · rw [mul_comm, mul_smul]; exact A.nsmul_mem (ht _) _
  · funext z
    have h : ∀ i, U D T (t' i) (comb D T c t F) z = ∑ j, c j * U D T (t' i) (U D T (t j) F) z := by
      intro i
      have := U_sum D T Finset.univ (t' i) (fun j w => c j * U D T (t j) F w) z
      simp only [U_mul] at this
      exact this
    have e : comb D T c' t' (comb D T c t F) z = ∑ i, c' i * U D T (t' i) (comb D T c t F) z := rfl
    rw [e]
    simp only [h, U_U]
    unfold comb
    rw [← finProdFinEquiv.sum_comp, Fintype.sum_prod_type]
    simp only [Equiv.symm_apply_apply, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    ring

theorem IsTr.single {A : AddSubgroup (VC D N N')} (F : VC D N N' → ℂ) (a : ℂ) (t : VC D N N') (m : ℕ)
    (hm : 0 < m) (ht : m • t ∈ A) : IsTr D T A F (fun z => a * U D T t F z) :=
  ⟨1, fun _ => a, fun _ => t, m, hm, fun _ => ht, by funext z; simp [comb]⟩

theorem IsTr.pad {A : AddSubgroup (VC D N N')} {m : ℕ} {B : AddSubgroup (VC D (N + m) N')} {R : ℕ} (hR : 0 < R)
    (hAB : ∀ y ∈ A, R • pad D m y ∈ B) {F : VC D (N + m) N' → ℂ} {G : VC D N N' → ℂ}
    (h : IsTr D T A (fun z => F (pad D m z)) G) :
    ∃ G₁, IsTr D T B F G₁ ∧ G = fun z => G₁ (pad D m z) := by
  obtain ⟨k, c, t, n, hn, ht, rfl⟩ := h
  refine ⟨_, ⟨k, c, fun i => GalTheta.pad D m (t i), R * n, Nat.mul_pos hR hn, fun i => ?_, rfl⟩, comb_pad D T m c t F⟩
  rw [mul_smul, ← pad_nsmul]
  exact hAB _ (ht i)

end GlobalTheory.GalTheta
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.DualLatticeIsLatticeAndHermitianDualStatement
section
open NumberField IsDedekindDomain MvPolynomial Formalism.BasicNotions Formalism.L2.DIV Formalism.DivisionValues GlobalTheory.TestLat Formalism.L2.Indef.Tree.ArchimedeanLeafBounds.Cuts
open scoped Matrix ComplexOrder
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.dualLattice_isLattice_and_hermitianDual : DualFrLattice ∧ DualFrHdual := by
  first | exact @GlobalTheory.DualLat.dualFr_lattice_and_hdual | exact GlobalTheory.DualLat.dualFr_lattice_and_hdual | (intros; apply GlobalTheory.DualLat.dualFr_lattice_and_hdual <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.OrthogonalSumCoefficientLatticeIsLatticeAndDualStatement
section
open NumberField IsDedekindDomain MvPolynomial Formalism.BasicNotions Formalism.L2.DIV Formalism.DivisionValues GlobalTheory.TestLat Formalism.L2.Indef.Tree.ArchimedeanLeafBounds.Cuts
open scoped Matrix ComplexOrder
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.orthogonalSumCoefficientLattice_isLattice_and_dual : ∀ (K : Type) [Field K] [NumberField K] [StarRing K] (ι : Type) [Fintype ι] (n : ℕ) (lam : ι → DomWeight n) (C : Type) [Nonempty C] (N : ℕ) (e : Fin N ≃ C × VVIdx lam) (T : C → Submodule (𝓞 K) (VV K lam)), (∀ c, Submodule.IsLattice K (T c)) → Submodule.IsLattice K (sumLat lam e T) ∧ 0 < N ∧ ∀ (G : ι → Matrix (Fin n) (Fin n) K), (∀ τ, (G τ)ᴴ = G τ) → hdualFr (sumGram lam e G) (sumLat lam e T) = sumLat lam e fun c => Formalism.HermitianLatticesTheory.dual (pairK lam G) (T c) := by
  first | exact @GlobalTheory.TestLat.SumLat.sumLat_lattice_dual | exact GlobalTheory.TestLat.SumLat.sumLat_lattice_dual | (intros; apply GlobalTheory.TestLat.SumLat.sumLat_lattice_dual <;> assumption)
end

