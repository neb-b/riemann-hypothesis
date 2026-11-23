module

public import Mathlib

@[expose] public section

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.DerivationCommutesWithTrace
section
set_option backward.isDefEq.respectTransparency false
open MvPolynomial

namespace GlobalTheory.CompanionTheory.TraceDerivation

theorem trace_map_derivation : ∀ (K F L : Type) [Field K] [CharZero K] [Field F] [Field L]
    [Algebra K F] [Algebra K L] [Algebra F L] [IsScalarTower K F L] [FiniteDimensional F L]
    (D : Derivation K L L) (D0 : Derivation K F F),
    (∀ x : F, D (algebraMap F L x) = algebraMap F L (D0 x)) →
    ∀ y : L, algebraMap F L (D0 (Algebra.trace F L y)) =
      algebraMap F L (Algebra.trace F L (D y)) := by
  intro K F L _ _ _ _ _ _ _ _ _ D D0 h y
  classical
  let b := Module.finBasis F L
  let M := Algebra.leftMulMatrix b y
  let N := Algebra.leftMulMatrix b (D y)
  let C : Matrix (Fin (Module.finrank F L)) (Fin (Module.finrank F L)) F :=
    Matrix.of fun i j => b.repr (D (b j)) i
  have hmul : ∀ (z : L) (j), z * b j = ∑ i, Algebra.leftMulMatrix b z i j • b i := by
    intro z j
    simp only [Algebra.leftMulMatrix_eq_repr_mul]
    exact (b.sum_repr _).symm
  have hD : ∀ j, D (b j) = ∑ k, C k j • b k := fun j => (b.sum_repr _).symm
  have hsmul : ∀ (a : F) (x : L), D (a • x) = D0 a • x + a • D x := by
    intro a x
    rw [Algebra.smul_def, D.leibniz, h, smul_eq_mul, smul_eq_mul, Algebra.smul_def,
      Algebra.smul_def]
    ring
  have h1 : ∀ j, ∑ i, (M * C) i j • b i = y * D (b j) := by
    intro j
    rw [hD j, Finset.mul_sum]
    simp only [Matrix.mul_apply, Finset.sum_smul]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [mul_smul_comm, hmul y k, Finset.smul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [mul_comm, mul_smul]
  have h2 : ∀ j, ∑ i, (C * M) i j • b i = ∑ k, M k j • D (b k) := by
    intro j
    simp only [Matrix.mul_apply, Finset.sum_smul]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [hD k, Finset.smul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [mul_comm, mul_smul]
  have key : ∀ j, ∑ i, (N + M * C) i j • b i = ∑ i, (M.map D0 + C * M) i j • b i := by
    intro j
    have e := congrArg D (hmul y j)
    set_option synthInstance.maxHeartbeats 100000 in
      rw [D.leibniz, map_sum] at e
    simp only [hsmul, Finset.sum_add_distrib, smul_eq_mul] at e
    simp only [Matrix.add_apply, add_smul, Finset.sum_add_distrib, h1, h2, Matrix.map_apply]
    rw [← hmul (D y) j]
    rw [add_comm (D y * b j), mul_comm (D y), e]
  have hmat : N + M * C = M.map D0 + C * M := by
    ext i j
    have : b.repr (∑ i, (N + M * C) i j • b i) i = b.repr (∑ i, (M.map D0 + C * M) i j • b i) i := by
      rw [key j]
    rw [b.repr_sum_self, b.repr_sum_self] at this
    exact this
  have htr : Matrix.trace N = D0 (Matrix.trace M) := by
    have := congrArg Matrix.trace hmat
    rw [Matrix.trace_add, Matrix.trace_add, Matrix.trace_mul_comm M C] at this
    have h3 := add_right_cancel this
    rw [h3]
    set_option synthInstance.maxHeartbeats 100000 in
      simp [Matrix.trace, map_sum]
  congr 1
  rw [Algebra.trace_eq_matrix_trace b y, Algebra.trace_eq_matrix_trace b (D y)]
  exact htr.symm

end GlobalTheory.CompanionTheory.TraceDerivation
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.DetSqNormEqHermitianBlockFormula
section
open Matrix

namespace GlobalTheory.CompanionTheory.KWhit

theorem norm_det_bottom_block_sq :
    ∀ {n : Type} [Fintype n] [DecidableEq n] (t u D K₁ K₂ β h g : Matrix n n ℂ) (e η : ℂ),
      ‖e‖ = 1 → η ≠ 0 → K₁ * K₁ᴴ + K₂ * K₂ᴴ = 1 → e • t = D * K₁ → e • (β * u) = D * K₂ →
      tᴴ * u = 1 → hᴴ = h → β = -(η • hᵀ) →
      g * uᴴ = ((‖η‖ ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) • 1 → IsUnit g.det →
      ‖D.det‖ ^ 2 = ‖t.det‖ ^ 2 *
        (1 + (g⁻¹ * h.map star * g⁻¹ᴴ) * (g⁻¹ * h.map star * g⁻¹ᴴ)).det.re := by
  intro n _ _ t u D K₁ K₂ β h g e η he hη hK h1 h2 htu hh hβ hg hgdet
  obtain ⟨s, hsdef⟩ : ∃ s : ℝ, s = ‖η‖ ^ (-(1 / 2 : ℝ)) := ⟨_, rfl⟩
  rw [← hsdef] at hg
  obtain ⟨M, hM⟩ : ∃ M : Matrix n n ℂ, M = g⁻¹ * h.map star * g⁻¹ᴴ := ⟨_, rfl⟩
  rw [← hM]
  have hn : 0 < ‖η‖ := norm_pos_iff.mpr hη
  have hss : s * s = ‖η‖ ^ (-1 : ℝ) := by
    rw [hsdef, ← Real.rpow_add hn]
    norm_num
  have hs : s * s * ‖η‖ = 1 := by
    rw [hss, Real.rpow_neg_one, inv_mul_cancel₀ hn.ne']
  have hs0 : s ≠ 0 := by
    intro h0
    rw [h0] at hs
    simp at hs
  have hinv : s⁻¹ = s * ‖η‖ := inv_eq_of_mul_eq_one_right (by linear_combination hs)
  have nsq : ∀ z : ℂ, ((‖z‖ ^ 2 : ℝ) : ℂ) = z * star z := by
    intro z
    rw [← Complex.normSq_eq_norm_sq]
    exact (Complex.mul_conj z).symm
  have hsstar : star (s : ℂ) = s := by
    exact Complex.conj_ofReal s
  have hsinvstar : star ((s : ℂ)⁻¹) = (s : ℂ)⁻¹ := by
    rw [star_inv₀, hsstar]
  have hee : e * star e = 1 := by
    rw [← nsq e, he]
    norm_num
  have hee' : star e * e = 1 := by rw [mul_comm]; exact hee
  have hsC : (s : ℂ) ≠ 0 := by exact_mod_cast hs0
  have hsa : star (-(η * (s : ℂ))) = -(star η * (s : ℂ)) := by
    rw [star_neg, star_mul', hsstar]
  have ha : -(η * (s : ℂ)) * star (-(η * (s : ℂ))) = (s : ℂ)⁻¹ * (s : ℂ)⁻¹ := by
    rw [hsa]
    have e1 : -(η * (s : ℂ)) * -(star η * (s : ℂ)) = (η * star η) * ((s : ℂ) * (s : ℂ)) := by
      ring
    rw [e1, ← nsq η]
    have e2 : ‖η‖ ^ 2 * (s * s) = s⁻¹ * s⁻¹ := by
      rw [hinv]
      ring
    have e3 : ((‖η‖ ^ 2 : ℝ) : ℂ) * ((s : ℂ) * (s : ℂ)) = ((‖η‖ ^ 2 * (s * s) : ℝ) : ℂ) := by
      first | (push_cast; ring) | push_cast | simp
    rw [e3, e2]
    first | (push_cast; ring) | push_cast | simp
  have ha' : star (-(η * (s : ℂ))) * -(η * (s : ℂ)) = (s : ℂ)⁻¹ * (s : ℂ)⁻¹ := by
    rw [mul_comm]; exact ha
  have hs_ij : ∀ i j, star (h i j) = h j i := by
    intro i j
    have hx := congrArg (fun X : Matrix n n ℂ => X j i) hh
    simp only [Matrix.conjTranspose_apply] at hx
    exact hx
  have hT : h.map star = hᵀ := by
    ext i j
    simp only [Matrix.map_apply, Matrix.transpose_apply]
    exact hs_ij i j
  have hTH : hᵀᴴ = hᵀ := by
    ext i j
    simp only [Matrix.conjTranspose_apply, Matrix.transpose_apply]
    exact hs_ij i j
  have hgg : g * g⁻¹ = 1 := Matrix.mul_nonsing_inv g hgdet
  have hgg' : g⁻¹ * g = 1 := Matrix.nonsing_inv_mul g hgdet
  have hMH : Mᴴ = M := by
    rw [hM, hT, Matrix.conjTranspose_mul, Matrix.conjTranspose_mul,
      Matrix.conjTranspose_conjTranspose, hTH, mul_assoc]
  have hgM : g * M = hᵀ * g⁻¹ᴴ := by
    rw [hM, hT, ← mul_assoc, ← mul_assoc, hgg, one_mul]
  have hut : uᴴ * t = 1 := by
    have hx := congrArg Matrix.conjTranspose htu
    rwa [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose,
      Matrix.conjTranspose_one] at hx
  have huH : uᴴ = (s : ℂ) • g⁻¹ := by
    calc uᴴ = g⁻¹ * (g * uᴴ) := by rw [← mul_assoc, hgg', one_mul]
      _ = (s : ℂ) • g⁻¹ := by rw [hg, mul_smul_comm, mul_one]
  have hu : u = (s : ℂ) • g⁻¹ᴴ := by
    calc u = uᴴᴴ := (Matrix.conjTranspose_conjTranspose u).symm
      _ = (s : ℂ) • g⁻¹ᴴ := by rw [huH, Matrix.conjTranspose_smul, hsstar]
  have ht : t = (s : ℂ)⁻¹ • g := by
    have h3 : (s : ℂ) • t = g := by
      calc (s : ℂ) • t = ((s : ℂ) • (1 : Matrix n n ℂ)) * t := by rw [smul_mul_assoc, one_mul]
        _ = g * uᴴ * t := by rw [hg]
        _ = g := by rw [mul_assoc, hut, mul_one]
    rw [← h3, smul_smul, inv_mul_cancel₀ hsC, one_smul]
  have hβu : β * u = (-(η * (s : ℂ))) • (g * M) := by
    rw [hβ, hu, hgM, neg_mul, smul_mul_assoc, mul_smul_comm, smul_smul, neg_smul]
  have hDD : D * Dᴴ = t * tᴴ + (β * u) * (β * u)ᴴ := by
    have step1 : D * Dᴴ = (D * K₁) * (D * K₁)ᴴ + (D * K₂) * (D * K₂)ᴴ := by
      calc D * Dᴴ = D * (K₁ * K₁ᴴ + K₂ * K₂ᴴ) * Dᴴ := by rw [hK, mul_one]
        _ = (D * K₁) * (D * K₁)ᴴ + (D * K₂) * (D * K₂)ᴴ := by
          simp only [Matrix.conjTranspose_mul, mul_add, add_mul, mul_assoc]
    rw [step1, ← h1, ← h2]
    simp only [Matrix.conjTranspose_smul, smul_mul_assoc, mul_smul_comm, smul_smul, hee', one_smul]
  have hmain : D * Dᴴ = ((s : ℂ)⁻¹ * (s : ℂ)⁻¹) • (g * (1 + M * M) * gᴴ) := by
    rw [hDD, ht, hβu]
    simp only [Matrix.conjTranspose_smul, smul_mul_assoc, mul_smul_comm, smul_smul, hsinvstar, ha']
    rw [← smul_add]
    congr 1
    simp only [Matrix.conjTranspose_mul, hMH, mul_add, add_mul, mul_one, mul_assoc]
  have hdet : D.det * star D.det = t.det * star t.det * (1 + M * M).det := by
    have lhs : D.det * star D.det = (D * Dᴴ).det := by
      rw [Matrix.det_mul, Matrix.det_conjTranspose]
    rw [lhs, hmain, Matrix.det_smul, Matrix.det_mul, Matrix.det_mul, Matrix.det_conjTranspose,
      ht, Matrix.det_smul, star_mul', star_pow, hsinvstar]
    ring
  rw [← nsq, ← nsq] at hdet
  have hre := congrArg Complex.re hdet
  first
    | (rw [Complex.ofReal_re, Complex.re_ofReal_mul] at hre; exact hre)
    | (simpa [Complex.mul_re] using hre)

end GlobalTheory.CompanionTheory.KWhit
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.EigenvectorLiftOfSurjection
section
namespace GlobalTheory.CompanionTheory.EigenLift

theorem exists_eigenvector_of_surjective_intertwiner
    (W W' : Type) [AddCommGroup W] [Module ℂ W] [AddCommGroup W'] [Module ℂ W']
    [FiniteDimensional ℂ W] (T : W →ₗ[ℂ] W) (S : W' →ₗ[ℂ] W') (f : W →ₗ[ℂ] W')
    (hf : Function.Surjective f) (hfT : f ∘ₗ T = S ∘ₗ f)
    (c : ℂ) (w' : W') (hw' : w' ≠ 0) (hS : S w' = c • w') :
    ∃ w : W, w ≠ 0 ∧ T w = c • w := by
  by_contra hne
  push_neg at hne
  haveI : FiniteDimensional ℂ W' := Module.Finite.of_surjective (R := ℂ) f hf
  set A : W →ₗ[ℂ] W := T - c • LinearMap.id with hA
  set B : W' →ₗ[ℂ] W' := S - c • LinearMap.id with hB
  have hinj : Function.Injective A := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro w hw
    by_contra h0
    apply hne w h0
    simpa [hA, sub_eq_zero] using hw
  have hsurjT : Function.Surjective A := LinearMap.injective_iff_surjective.1 hinj
  have hcomm : ∀ z, f (A z) = B (f z) := by
    intro z
    have h1 := LinearMap.congr_fun hfT z
    simp only [LinearMap.comp_apply] at h1
    simp [hA, hB, map_sub, map_smul, h1]
  have hsurjS : Function.Surjective B := by
    intro y
    obtain ⟨x, rfl⟩ := hf y
    obtain ⟨z, rfl⟩ := hsurjT x
    exact ⟨f z, (hcomm z).symm⟩
  have hinjS := LinearMap.injective_iff_surjective.2 hsurjS
  apply hw'
  apply hinjS
  simp [hB, hS]

theorem nonzero_eigenvalue_lifts :
    ∀ (W W' : Type) [AddCommGroup W] [Module ℂ W] [AddCommGroup W'] [Module ℂ W']
      [FiniteDimensional ℂ W] (T : W →ₗ[ℂ] W) (S : W' →ₗ[ℂ] W') (f : W →ₗ[ℂ] W'),
      Function.Surjective f → f ∘ₗ T = S ∘ₗ f →
      ∀ (c : ℂ) (w' : W'), w' ≠ 0 → S w' = c • w' → c ≠ 0 → ∃ w : W, w ≠ 0 ∧ T w = c • w := by
  intro W W' _ _ _ _ _ T S f hf hfT c w' hw' hS _
  exact exists_eigenvector_of_surjective_intertwiner W W' T S f hf hfT c w' hw' hS

end GlobalTheory.CompanionTheory.EigenLift
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.EqDiagonalOfUpperTriangularOfUnitary
section
open Matrix
open scoped ComplexOrder

namespace GlobalTheory.CompanionTheory.RealPlace

theorem eq_diagonal_of_upperTriangular_of_unitary {r : ℕ} (B : Matrix (Fin r) (Fin r) ℂ)
    (hB : B.BlockTriangular id) (hBB : Bᴴ * B = 1) : B = diagonal (fun i => B i i) := by
  have hinv : B⁻¹ = Bᴴ := Matrix.inv_eq_left_inv hBB
  haveI : Invertible B := Matrix.invertibleOfIsUnitDet B (Matrix.isUnit_det_of_left_inverse hBB)
  have hT : B⁻¹.BlockTriangular id := Matrix.blockTriangular_inv_of_blockTriangular hB
  rw [hinv] at hT
  ext i j
  rcases lt_trichotomy i j with h | rfl | h
  · have h1 : Bᴴ j i = 0 := hT h
    rw [Matrix.conjTranspose_apply, star_eq_zero] at h1
    rw [h1, Matrix.diagonal_apply_ne _ (ne_of_lt h)]
  · simp
  · rw [hB h, Matrix.diagonal_apply_ne _ (ne_of_gt h)]

theorem flag_isometry_diagonal_on_frame (n r : ℕ) (J P p : Matrix (Fin n) (Fin n) ℂ)
    (X Y : Matrix (Fin n) (Fin r) ℂ) (hJ : IsUnit J.det) (hXY : Xᴴ * J * Y = 1)
    (_hP : P.PosDef) (_hPJ : P * J⁻¹ * P = J) (hPX : P * X = J * Y)
    (hpJ : pᴴ * J * p = J) (hpP : pᴴ * P * p = P)
    (B : Matrix (Fin r) (Fin r) ℂ) (hB : B.BlockTriangular id) (hpX : p * X = X * B) :
    ∃ d : Fin r → ℂ, p * X = X * diagonal d ∧ p * Y = Y * diagonal d := by
  have hXPX : Xᴴ * P * X = 1 := by
    rw [Matrix.mul_assoc, hPX, ← Matrix.mul_assoc]
    exact hXY
  have hBB : Bᴴ * B = 1 := by
    calc Bᴴ * B = Bᴴ * (Xᴴ * P * X) * B := by rw [hXPX, Matrix.mul_one]
      _ = (X * B)ᴴ * P * (X * B) := by
          rw [Matrix.conjTranspose_mul]
          simp only [Matrix.mul_assoc]
      _ = (p * X)ᴴ * P * (p * X) := by rw [hpX]
      _ = Xᴴ * (pᴴ * P * p) * X := by
          rw [Matrix.conjTranspose_mul]
          simp only [Matrix.mul_assoc]
      _ = 1 := by
          rw [hpP]
          exact hXPX
  have hBd := eq_diagonal_of_upperTriangular_of_unitary B hB hBB
  obtain ⟨D, hD⟩ : ∃ D : Matrix (Fin r) (Fin r) ℂ, D = diagonal (fun i => B i i) := ⟨_, rfl⟩
  have hBD : B = D := hBd.trans hD.symm
  have hpXD : p * X = X * D := by
    rw [hpX, hBD]
  have hr : pᴴ * (J * p * J⁻¹) = 1 := by
    rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, hpJ, Matrix.mul_nonsing_inv J hJ]
  have hr' : (J * p * J⁻¹) * pᴴ = 1 := mul_eq_one_comm.mp hr
  have key : J * (p * Y) = J * (Y * D) := by
    calc J * (p * Y) = (J * p * J⁻¹) * pᴴ * (J * (p * Y)) := by rw [hr', Matrix.one_mul]
      _ = (J * p * J⁻¹) * (pᴴ * J * p) * Y := by simp only [Matrix.mul_assoc]
      _ = (J * p * J⁻¹) * (J * Y) := by
          rw [hpJ]
          simp only [Matrix.mul_assoc]
      _ = (J * p * J⁻¹) * (pᴴ * P * p * X) := by rw [hpP, hPX]
      _ = (J * p * J⁻¹) * pᴴ * (P * (p * X)) := by simp only [Matrix.mul_assoc]
      _ = (J * p * J⁻¹) * pᴴ * (P * X * D) := by
          rw [hpXD]
          simp only [Matrix.mul_assoc]
      _ = (J * p * J⁻¹) * pᴴ * (J * (Y * D)) := by
          rw [hPX]
          simp only [Matrix.mul_assoc]
      _ = J * (Y * D) := by rw [hr', Matrix.one_mul]
  have hpYD : p * Y = Y * D := by
    calc p * Y = J⁻¹ * (J * (p * Y)) := by
          simp only [← Matrix.mul_assoc, Matrix.nonsing_inv_mul J hJ, Matrix.one_mul]
      _ = J⁻¹ * (J * (Y * D)) := by rw [key]
      _ = Y * D := by
          simp only [← Matrix.mul_assoc, Matrix.nonsing_inv_mul J hJ, Matrix.one_mul]
  exact ⟨fun i => B i i, hD ▸ hpXD, hD ▸ hpYD⟩

end GlobalTheory.CompanionTheory.RealPlace
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.EqOfNearOfCharpolyEq
section
open MeasureTheory Set Filter Matrix
open scoped ENNReal NNReal Topology

namespace GlobalTheory.CompanionTheory.WeylNear

theorem exists_diag (n : ℕ) (s : Matrix (Fin n) (Fin n) ℂ) (hs : s.charpoly.Separable) :
    ∃ (P Q : Matrix (Fin n) (Fin n) ℂ) (l : Fin n → ℂ), Function.Injective l ∧
      P * Q = 1 ∧ Q * P = 1 ∧ Q * s * P = diagonal l := by
  have hnd : s.charpoly.roots.Nodup := Polynomial.nodup_roots hs
  have hcard : s.charpoly.roots.card = n := by
    have h1 := (IsAlgClosed.splits s.charpoly).natDegree_eq_card_roots
    rw [Matrix.charpoly_natDegree_eq_dim] at h1
    simpa using h1.symm
  have hc2 : s.charpoly.roots.toFinset.card = n := by
    rw [Multiset.toFinset_card_of_nodup hnd, hcard]
  let e := Finset.equivFinOfCardEq hc2
  let l : Fin n → ℂ := fun i => (e.symm i : ℂ)
  have hl : Function.Injective l := fun i j h =>
    e.symm.injective (Subtype.ext h)
  have hroot : ∀ i, s.charpoly.IsRoot (l i) := fun i => by
    have := (e.symm i).2
    rw [Multiset.mem_toFinset] at this
    exact Polynomial.isRoot_of_mem_roots this
  have hev : ∀ i, ∃ v : Fin n → ℂ, v ≠ 0 ∧ s *ᵥ v = l i • v := by
    intro i
    have h0 : Module.End.HasEigenvalue (Matrix.toLin' s : Module.End ℂ (Fin n → ℂ)) (l i) := by
      rw [Module.End.hasEigenvalue_iff_isRoot_charpoly, Matrix.charpoly_toLin']
      exact hroot i
    obtain ⟨v, hv⟩ := h0.exists_hasEigenvector
    refine ⟨v, hv.2, ?_⟩
    have := hv.apply_eq_smul
    simpa using this
  choose v hv0 hv using hev
  have hli : LinearIndependent ℂ v :=
    Module.End.eigenvectors_linearIndependent' (Matrix.toLin' s : Module.End ℂ (Fin n → ℂ)) l hl v
      (fun i => ⟨by
        rw [Module.End.mem_eigenspace_iff]; simpa using hv i, hv0 i⟩)
  let P : Matrix (Fin n) (Fin n) ℂ := Matrix.of fun i j => v j i
  have hcol : P.col = v := by
    ext j i; rfl
  have hP : IsUnit P := Matrix.linearIndependent_cols_iff_isUnit.mp (by rw [hcol]; exact hli)
  have hdet : IsUnit P.det := (Matrix.isUnit_iff_isUnit_det _).1 hP
  have hsP : s * P = P * diagonal l := by
    ext i j
    have := congrFun (hv j) i
    simp only [Matrix.mulVec, dotProduct, Pi.smul_apply, smul_eq_mul] at this
    rw [Matrix.mul_diagonal]
    simp only [Matrix.mul_apply, P, Matrix.of_apply]
    rw [this, mul_comm]
  refine ⟨P, P⁻¹, l, hl, Matrix.mul_nonsing_inv _ hdet, Matrix.nonsing_inv_mul _ hdet, ?_⟩
  rw [Matrix.mul_assoc, hsP, ← Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hdet, Matrix.one_mul]

end GlobalTheory.CompanionTheory.WeylNear
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsBumpWithNonzeroIntegral
section
open MeasureTheory
open scoped ENNReal NNReal Topology

namespace GlobalTheory.CompanionTheory.MeasureBump

theorem exists_integral_ne_zero_of_carried_by_isOpen
    (X : Type) [TopologicalSpace X] [T2Space X] [LocallyCompactSpace X]
    [SecondCountableTopology X] [MeasurableSpace X] [BorelSpace X] (m : Measure X) (U : Set X)
    (hU : IsOpen U) (hc : m Uᶜ = 0) (hm : m ≠ 0)
    (hint : ∀ χ : X → ℝ, Continuous χ → HasCompactSupport χ → tsupport χ ⊆ U → Integrable χ m) :
    ∃ χ : X → ℝ, Continuous χ ∧ HasCompactSupport χ ∧ tsupport χ ⊆ U ∧ ∫ x, χ x ∂m ≠ 0 := by
  have hmU : m U ≠ 0 := by
    intro h0
    apply hm
    rw [← Measure.measure_univ_eq_zero]
    have huniv : (Set.univ : Set X) = U ∪ Uᶜ := (Set.union_compl_self U).symm
    rw [huniv]
    exact measure_union_null h0 hc
  haveI : LocallyCompactSpace U := hU.locallyCompactSpace
  have hσ : IsSigmaCompact U := isSigmaCompact_iff_sigmaCompactSpace.2 inferInstance
  obtain ⟨K, hK, hKU⟩ := hσ
  have hex : ∃ n, m (K n) ≠ 0 := by
    by_contra hcon
    push_neg at hcon
    apply hmU
    rw [← hKU]
    exact measure_iUnion_null hcon
  obtain ⟨n, hn⟩ := hex
  have hsub : K n ⊆ U := hKU ▸ Set.subset_iUnion K n
  obtain ⟨f, hf1, hfc, hfU, hf01⟩ :=
    exists_continuousMap_one_of_isCompact_subset_isOpen (hK n) hU hsub
  refine ⟨f, f.continuous, hfc, hfU, ?_⟩
  have hI : Integrable (f : X → ℝ) m := hint f f.continuous hfc hfU
  have hnn : 0 ≤ᵐ[m] (f : X → ℝ) := Filter.Eventually.of_forall fun x => (hf01 x).1
  have hpos : 0 < ∫ x, f x ∂m := by
    rw [integral_pos_iff_support_of_nonneg_ae hnn hI]
    refine lt_of_lt_of_le (pos_iff_ne_zero.2 hn) (measure_mono ?_)
    intro x hx
    simp [Function.mem_support, hf1 hx]
  exact hpos.ne'

end GlobalTheory.CompanionTheory.MeasureBump
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsConjMulEq
section
namespace GlobalTheory.CompanionTheory.FFNorm

theorem exists_conj_mul_eq : ∀ (κ : Type) [Field κ] [Finite κ] (τ : κ →+* κ), (∀ x, τ (τ x) = x) →
    (∃ x, τ x ≠ x) → ∀ c : κ, τ c = c → ∃ s : κ, τ s * s = c := by
  intro κ _ _ τ hinv hne c hc
  classical
  let F : Subfield κ := RingHom.eqLocusField τ (RingHom.id κ)
  have hF : ∀ y : F, τ (y : κ) = y := fun y => y.2
  let σ : κ ≃ₐ[F] κ := AlgEquiv.ofRingEquiv (f := RingEquiv.ofRingHom τ τ
      (RingHom.ext hinv) (RingHom.ext hinv)) (fun y => hF y)
  have hσ : ∀ x, σ x = τ x := fun x => rfl
  have hσ1 : σ ≠ 1 := by
    obtain ⟨x, hx⟩ := hne
    intro h
    exact hx (by rw [← hσ, h]; rfl)
  have hall : ∀ ρ : κ ≃ₐ[F] κ, ρ = 1 ∨ ρ = σ := by
    have hfix : IntermediateField.fixedField (Subgroup.zpowers σ) = ⊥ := by
      rw [eq_bot_iff]
      intro x hx
      have : σ x = x := hx ⟨σ, Subgroup.mem_zpowers σ⟩
      exact IntermediateField.mem_bot.2 ⟨⟨x, this⟩, rfl⟩
    have htop : Subgroup.zpowers σ = ⊤ := by
      rw [← IntermediateField.fixingSubgroup_fixedField (Subgroup.zpowers σ), hfix]
      exact IntermediateField.fixingSubgroup_bot
    intro ρ
    have hρ : ρ ∈ Subgroup.zpowers σ := htop ▸ Subgroup.mem_top ρ
    have hsq : σ ^ 2 = 1 := by
      ext x
      simp [pow_two, hσ, hinv]
    obtain ⟨n, rfl⟩ := hρ
    rcases Int.even_or_odd' n with ⟨k, rfl | rfl⟩
    · left; simp [zpow_mul, hsq]
    · right; simp [zpow_add, zpow_mul, hsq]
  have huniv : (Finset.univ : Finset (κ ≃ₐ[F] κ)) = {1, σ} := by
    ext ρ
    simpa using hall ρ
  obtain ⟨a, ha⟩ := FiniteField.norm_surjective F κ (⟨c, hc⟩ : F)
  refine ⟨a, ?_⟩
  have h := Algebra.norm_eq_prod_automorphisms F a
  rw [huniv, Finset.prod_pair hσ1.symm, ha] at h
  have h2 : algebraMap F κ (⟨c, hc⟩ : F) = c := rfl
  rw [h2] at h
  simpa [hσ, mul_comm] using h.symm

end GlobalTheory.CompanionTheory.FFNorm
end

