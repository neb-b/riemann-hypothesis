module

public import Mathlib

@[expose] public section

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.ExtFrameOfQuotientKernel
section
namespace GlobalTheory.CompanionTheory.Ggeo

theorem ext_frame_of_quotient_kernel (Ω M V : Type) [Field Ω] [AddCommGroup M] [Module Ω M]
    [AddCommGroup V] [Module Ω V] (R : Subring Ω) (H : Submodule R M) (π : M →ₗ[Ω] V) (p q : ℕ)
    (u : Fin (p + q) → M) (v : Fin p → V) (P : Matrix (Fin p) (Fin p) Ω)
    (C : Matrix (Fin q) (Fin q) Ω)
    (hu : LinearIndependent Ω u) (hv : LinearIndependent Ω v)
    (hHu : ∀ y ∈ H, y ∈ Submodule.span Ω (Set.range u))
    (hπ1 : ∀ i, π (u (Fin.castAdd q i)) = v i) (hπ2 : ∀ j, π (u (Fin.natAdd p j)) = 0)
    (hP : P.det ≠ 0) (hC : C.det ≠ 0)
    (hmap : H.map (π.restrictScalars R) = Submodule.span R (Set.range fun i => ∑ j, P i j • v j))
    (hCH : ∀ j, ∑ k, C j k • u (Fin.natAdd p k) ∈ H)
    (hker : ∀ y ∈ H, π y = 0 →
      y ∈ Submodule.span R (Set.range fun j => ∑ k, C j k • u (Fin.natAdd p k))) :
    ∃ A : Matrix (Fin (p + q)) (Fin (p + q)) Ω, A.det = P.det * C.det ∧
      LinearIndependent Ω (fun i => ∑ j, A i j • u j) ∧
      H = Submodule.span R (Set.range fun i => ∑ j, A i j • u j) := by
  classical
  have hlift : ∀ i, ∃ y ∈ H, π y = ∑ j, P i j • v j := by
    intro i
    have hmem : (∑ j, P i j • v j) ∈ H.map (π.restrictScalars R) := by
      rw [hmap]; exact Submodule.subset_span ⟨i, rfl⟩
    obtain ⟨y, hy, e⟩ := hmem
    exact ⟨y, hy, e⟩
  choose h hH hπh using hlift
  have hT : ∀ i, ∃ t : Fin (p + q) → Ω, ∑ k, t k • u k = h i := fun i =>
    (Submodule.mem_span_range_iff_exists_fun Ω).1 (hHu _ (hH i))
  choose T hT using hT
  have hTP : ∀ i j, T i (Fin.castAdd q j) = P i j := by
    intro i
    have e : ∑ j, T i (Fin.castAdd q j) • v j = ∑ j, P i j • v j := by
      set_option synthInstance.maxHeartbeats 100000 in
        rw [← hπh i, ← hT i, map_sum, Fin.sum_univ_add]
      simp [hπ1, hπ2]
    have e2 : ∑ j, (T i (Fin.castAdd q j) - P i j) • v j = 0 := by
      simp [sub_smul, Finset.sum_sub_distrib, e]
    intro j
    exact sub_eq_zero.1 (Fintype.linearIndependent_iff.1 hv _ e2 j)
  let T2 : Matrix (Fin p) (Fin q) Ω := fun i k => T i (Fin.natAdd p k)
  let A : Matrix (Fin (p + q)) (Fin (p + q)) Ω :=
    Matrix.reindex finSumFinEquiv finSumFinEquiv (Matrix.fromBlocks P T2 0 C)
  have hA11 : ∀ i j, A (Fin.castAdd q i) (Fin.castAdd q j) = P i j := by
    intro i j; simp [A, Matrix.reindex_apply, Matrix.submatrix_apply]
  have hA12 : ∀ i j, A (Fin.castAdd q i) (Fin.natAdd p j) = T i (Fin.natAdd p j) := by
    intro i j
    change A (Fin.castAdd q i) (Fin.natAdd p j) = T2 i j
    simp [A, Matrix.reindex_apply, Matrix.submatrix_apply]
  have hA21 : ∀ i j, A (Fin.natAdd p i) (Fin.castAdd q j) = 0 := by
    intro i j; simp [A, Matrix.reindex_apply, Matrix.submatrix_apply]
  have hA22 : ∀ i j, A (Fin.natAdd p i) (Fin.natAdd p j) = C i j := by
    intro i j; simp [A, Matrix.reindex_apply, Matrix.submatrix_apply]
  have hdet : A.det = P.det * C.det := by
    simp only [A, Matrix.det_reindex_self, Matrix.det_fromBlocks_zero₂₁]
  have hw1 : ∀ i, ∑ j, A (Fin.castAdd q i) j • u j = h i := by
    intro i
    rw [← hT i, Fin.sum_univ_add, Fin.sum_univ_add]
    simp only [hA11, hA12, hTP]
  have hw2 : ∀ i, ∑ j, A (Fin.natAdd p i) j • u j = ∑ k, C i k • u (Fin.natAdd p k) := by
    intro i
    rw [Fin.sum_univ_add]
    simp only [hA21, hA22, zero_smul, Finset.sum_const_zero, zero_add]
  refine ⟨A, hdet, ?_, ?_⟩
  · rw [Fintype.linearIndependent_iff]
    intro c hc
    have hc' : ∑ j, (∑ i, c i * A i j) • u j = 0 := by
      rw [← hc]
      simp only [Finset.smul_sum, Finset.sum_smul, mul_smul]
      exact Finset.sum_comm
    have hz := Fintype.linearIndependent_iff.1 hu _ hc'
    have hvm : Matrix.vecMul c A = 0 := by
      funext j
      simpa [Matrix.vecMul, dotProduct] using hz j
    have hdet0 : A.det ≠ 0 := by rw [hdet]; exact mul_ne_zero hP hC
    have := Matrix.eq_zero_of_vecMul_eq_zero hdet0 hvm
    intro i
    exact congrFun this i
  · apply le_antisymm
    · intro y hy
      have hmem : π y ∈ Submodule.span R (Set.range fun i => ∑ j, P i j • v j) := by
        rw [← hmap]; exact ⟨y, hy, rfl⟩
      obtain ⟨r, hr⟩ := (Submodule.mem_span_range_iff_exists_fun R).1 hmem
      set S := Submodule.span R (Set.range fun i => ∑ j, A i j • u j) with hS
      have hhS : ∀ i, h i ∈ S := fun i => by
        rw [← hw1 i]; exact Submodule.subset_span ⟨_, rfl⟩
      have hCS : Submodule.span R (Set.range fun j => ∑ k, C j k • u (Fin.natAdd p k)) ≤ S := by
        rw [Submodule.span_le]
        rintro _ ⟨j, rfl⟩
        have := hw2 j
        simp only at this ⊢
        rw [← this]; exact Submodule.subset_span ⟨_, rfl⟩
      have hsumH : ∑ i, r i • h i ∈ H := Submodule.sum_mem _ fun i _ => H.smul_mem _ (hH i)
      have hsumS : ∑ i, r i • h i ∈ S := Submodule.sum_mem _ fun i _ => S.smul_mem _ (hhS i)
      have hdiff : y - ∑ i, r i • h i ∈ H := H.sub_mem hy hsumH
      have hπd : π (y - ∑ i, r i • h i) = 0 := by
        have e : π (∑ i, r i • h i) = ∑ i, r i • ∑ j, P i j • v j := by
          set_option synthInstance.maxHeartbeats 100000 in
            rw [map_sum]
          refine Finset.sum_congr rfl fun i _ => ?_
          rw [← hπh i, Subring.smul_def, Subring.smul_def, map_smul]
        rw [map_sub, e, hr, sub_self]
      have := hCS (hker _ hdiff hπd)
      simpa using S.add_mem this hsumS
    · rw [Submodule.span_le]
      rintro _ ⟨i, rfl⟩
      refine Fin.addCases (fun i => ?_) (fun i => ?_) i
      · simp only [SetLike.mem_coe]; rw [hw1]; exact hH i
      · simp only [SetLike.mem_coe]; rw [hw2]; exact hCH i

end GlobalTheory.CompanionTheory.Ggeo
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.FrobeniusStableSubspaceElement
section
open scoped TensorProduct

namespace GlobalTheory.CompanionTheory.HopfFrob

theorem exists_algHom_ne_zero_of_not_isNilpotent
    {k : Type} [Field k] [IsAlgClosed k] {A : Type} [CommRing A] [Algebra k A]
    [Module.Finite k A] {f : A} (hf : ¬ IsNilpotent f) :
    ∃ x : A →ₐ[k] k, x f ≠ 0 := by
  haveI : IsArtinianRing A := isArtinian_of_tower k inferInstance
  rw [← mem_nilradical, nilradical_eq_sInf, Ideal.mem_sInf] at hf
  push_neg at hf
  obtain ⟨P, hP, hfP⟩ := hf
  haveI : P.IsPrime := hP
  haveI : P.IsMaximal := IsArtinianRing.isMaximal_of_isPrime P
  letI : Field (A ⧸ P) := Ideal.Quotient.field P
  have hbij : Function.Bijective (algebraMap k (A ⧸ P)) :=
    IsAlgClosed.algebraMap_bijective_of_isIntegral
  let e : k ≃ₐ[k] (A ⧸ P) := AlgEquiv.ofBijective (Algebra.ofId k (A ⧸ P)) hbij
  refine ⟨(e.symm : (A ⧸ P) →ₐ[k] k).comp (Ideal.Quotient.mkₐ k P), ?_⟩
  intro h
  apply hfP
  have h' : e.symm (Ideal.Quotient.mk P f) = 0 := h
  have h2 : Ideal.Quotient.mk P f = 0 := by
    simpa using h'
  exact Ideal.Quotient.eq_zero_iff_mem.mp h2

theorem exists_pow_eq_zero_of_isNilpotent
    {A : Type} [CommRing A] {p : ℕ} (hp : 2 ≤ p) {S : Set A}
    (hS : ∀ f ∈ S, f ^ p ∈ S) {f : A} (hfS : f ∈ S) (hf0 : f ≠ 0) (hf : IsNilpotent f) :
    ∃ g ∈ S, g ≠ 0 ∧ g ^ p = 0 := by
  classical
  obtain ⟨n, hn⟩ := hf
  have hex : ∃ m : ℕ, f ^ (p ^ m) = 0 :=
    ⟨n, pow_eq_zero_of_le (Nat.lt_pow_self (by omega)).le hn⟩
  have hspec := Nat.find_spec hex
  have hpos : Nat.find hex ≠ 0 := by
    intro h0
    rw [h0] at hspec
    simp at hspec
    exact hf0 hspec
  obtain ⟨m, hm⟩ := Nat.exists_eq_succ_of_ne_zero hpos
  have hmem : ∀ j : ℕ, f ^ (p ^ j) ∈ S := by
    intro j
    induction j with
    | zero => simpa using hfS
    | succ j ih =>
      have := hS _ ih
      rwa [← pow_mul, ← pow_succ] at this
  refine ⟨f ^ (p ^ m), hmem m, Nat.find_min hex (m := m) (by omega), ?_⟩
  rw [← pow_mul, ← pow_succ]
  rw [hm] at hspec
  exact hspec

theorem exists_frobenius_fixed_or_killed :
    ∀ (k : Type) [Field k] [IsAlgClosed k] (p : ℕ) [Fact p.Prime] [CharP k p]
    (A : Type) [CommRing A] [Algebra k A] [Module.Finite k A] (V : Submodule k A),
    V ≠ ⊥ → (∀ f ∈ V, f ^ p ∈ V) → ∃ f ∈ V, f ≠ 0 ∧ (f ^ p = 0 ∨ f ^ p = f) := by
  intro k _ _ p _ _ A _ _ _ V hV hVp
  have hp : 2 ≤ p := (Fact.out : p.Prime).two_le
  obtain ⟨f₀, hf₀V, hf₀⟩ := (Submodule.ne_bot_iff V).mp hV
  have key : ∀ n : ℕ, ∀ f ∈ V, f ≠ 0 →
      Module.finrank k (LinearMap.range (LinearMap.mulLeft k f)) = n →
      ∃ f ∈ V, f ≠ 0 ∧ (f ^ p = 0 ∨ f ^ p = f) := by
    intro n
    induction n using Nat.strong_induction_on with
    | _ n ih =>
      intro f hfV hf0 hn
      by_cases hnil : IsNilpotent f
      · obtain ⟨g, hg, hg0, hgp⟩ := exists_pow_eq_zero_of_isNilpotent (S := (V : Set A)) hp
          (fun a ha => hVp a ha) hfV hf0 hnil
        exact ⟨g, hg, hg0, Or.inl hgp⟩
      obtain ⟨x, hx⟩ := exists_algHom_ne_zero_of_not_isNilpotent (k := k) hnil
      set c : k := (x f)⁻¹ with hc
      set f' : A := c • f with hf'
      have hf'V : f' ∈ V := V.smul_mem c hfV
      have hxf' : x f' = 1 := by
        simp [hf', hc, hx]
      have hf'0 : f' ≠ 0 := by
        intro h
        rw [h] at hxf'
        simp at hxf'
      set g : A := f' ^ p - f' with hg
      have hgV : g ∈ V := V.sub_mem (hVp _ hf'V) hf'V
      by_cases hg0 : g = 0
      · exact ⟨f', hf'V, hf'0, Or.inr (sub_eq_zero.mp hg0)⟩
      have hxg : x g = 0 := by
        simp [hg, hxf']
      obtain ⟨q, hq⟩ : ∃ q : A, g = f * q := by
        obtain ⟨r, hr⟩ : ∃ r, p = r + 1 := ⟨p - 1, by omega⟩
        refine ⟨c • (f' ^ r - 1), ?_⟩
        calc g = f' * (f' ^ r - 1) := by rw [hg, hr]; ring
          _ = f * (c • (f' ^ r - 1)) := by rw [mul_smul_comm, hf', smul_mul_assoc]
      have hlt : LinearMap.range (LinearMap.mulLeft k g) <
          LinearMap.range (LinearMap.mulLeft k f) := by
        refine lt_of_le_of_ne ?_ ?_
        · rintro _ ⟨a, rfl⟩
          exact ⟨q * a, by simp [hq, mul_assoc]⟩
        · intro heq
          have hmem : f ∈ LinearMap.range (LinearMap.mulLeft k g) := by
            rw [heq]
            exact ⟨1, by simp⟩
          obtain ⟨a, ha⟩ := hmem
          apply hx
          have : g * a = f := by simpa using ha
          rw [← this, map_mul, hxg, zero_mul]
      have hrank := Submodule.finrank_lt_finrank_of_lt hlt
      exact ih _ (hn ▸ hrank) g hgV hg0 rfl
  exact key _ f₀ hf₀V hf₀ rfl

end GlobalTheory.CompanionTheory.HopfFrob
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.FundamentalDomainRiemannForm
section
open MeasureTheory

namespace GlobalTheory.CompanionTheory.Ar.Sl.SelfDualCovol

noncomputable def stdBasis (g : ℕ) : Module.Basis (Σ _ : Fin g, Fin 2) ℝ (Fin g → ℂ) :=
  Pi.basis fun _ => Complex.basisOneI

theorem stdBasis_repr_zero {g : ℕ} (z : Fin g → ℂ) (j : Fin g) :
    (stdBasis g).repr z ⟨j, 0⟩ = (z j).re := by
  simp [stdBasis, Pi.basis_repr]

theorem stdBasis_repr_one {g : ℕ} (z : Fin g → ℂ) (j : Fin g) :
    (stdBasis g).repr z ⟨j, 1⟩ = (z j).im := by
  simp [stdBasis, Pi.basis_repr]

theorem re_dotProduct_star {g : ℕ} (z w : Fin g → ℂ) :
    (z ⬝ᵥ star w).re = ∑ a, (stdBasis g).repr z a * (stdBasis g).repr w a := by
  rw [Fintype.sum_sigma]
  simp only [Fin.sum_univ_two, stdBasis_repr_zero, stdBasis_repr_one, dotProduct, Complex.re_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  simp [Complex.mul_re]

theorem volume_fundamentalDomain_stdBasis (g : ℕ) :
    volume.real (ZSpan.fundamentalDomain (stdBasis g)) = 1 := by
  have hset : ZSpan.fundamentalDomain (stdBasis g) =
      Set.pi Set.univ fun _ : Fin g => Complex.reProdIm (Set.Ico 0 1) (Set.Ico 0 1) := by
    ext z
    simp only [ZSpan.mem_fundamentalDomain, Set.mem_pi, Set.mem_univ, true_implies,
      Complex.mem_reProdIm]
    constructor
    · intro h j
      exact ⟨by simpa [stdBasis_repr_zero] using h ⟨j, 0⟩,
        by simpa [stdBasis_repr_one] using h ⟨j, 1⟩⟩
    · rintro h ⟨j, a⟩
      fin_cases a
      · simpa [stdBasis_repr_zero] using (h j).1
      · simpa [stdBasis_repr_one] using (h j).2
  have hsq : volume (Complex.reProdIm (Set.Ico (0 : ℝ) 1) (Set.Ico (0 : ℝ) 1)) = 1 := by
    have h := Complex.volume_preserving_equiv_real_prod.measure_preimage_equiv
      ((Set.Ico (0 : ℝ) 1) ×ˢ (Set.Ico (0 : ℝ) 1))
    have h2 : Complex.measurableEquivRealProd ⁻¹' ((Set.Ico (0 : ℝ) 1) ×ˢ (Set.Ico (0 : ℝ) 1)) =
        Complex.reProdIm (Set.Ico (0 : ℝ) 1) (Set.Ico (0 : ℝ) 1) := by
      ext z
      simp [Complex.mem_reProdIm, Complex.measurableEquivRealProd]
    rw [h2] at h
    rw [h, Measure.volume_eq_prod, Measure.prod_prod]
    simp
  rw [hset, measureReal_def, volume_pi_pi]
  simp [hsq]

theorem det_ne_zero_of_pos {g : ℕ} {Hm : Matrix (Fin g) (Fin g) ℂ}
    (hpos : ∀ z : Fin g → ℂ, z ≠ 0 → 0 < (z ⬝ᵥ Hm.mulVec (star z)).re) : Hm.det ≠ 0 := by
  intro h
  obtain ⟨v, hv, hmv⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr h
  have hz : star v ≠ 0 := by simpa using hv
  have := hpos (star v) hz
  simp [hmv] at this

theorem det_gram {g : ℕ} {ι : Type*} [Fintype ι] [DecidableEq ι]
    (e : Module.Basis ι ℝ (Fin g → ℂ))
    (he : ∀ z w : Fin g → ℂ, (z ⬝ᵥ star w).re = ∑ a, e.repr z a * e.repr w a)
    (Hm : Matrix (Fin g) (Fin g) ℂ) (v : ι → Fin g → ℂ) :
    (Matrix.of fun i j => (v i ⬝ᵥ Hm.mulVec (star (v j))).im).det =
      (e.det v) ^ 2 * Complex.normSq Hm.det := by
  let S : (Fin g → ℂ) →ₗ[ℂ] (Fin g → ℂ) := (-Complex.I) • Matrix.toLin' Hm.transpose
  let SR : (Fin g → ℂ) →ₗ[ℝ] (Fin g → ℂ) := S.restrictScalars ℝ
  let M := LinearMap.toMatrix e e SR
  let P := e.toMatrix v
  have hS : ∀ z w : Fin g → ℂ, (z ⬝ᵥ Hm.mulVec (star w)).im = (S z ⬝ᵥ star w).re := by
    intro z w
    have h1 : z ⬝ᵥ Hm.mulVec (star w) = Hm.transpose.mulVec z ⬝ᵥ star w := by
      rw [Matrix.dotProduct_mulVec, Matrix.mulVec_transpose]
    have h2 : S z = (-Complex.I) • Hm.transpose.mulVec z := by
      simp [S]
    rw [h1, h2, smul_dotProduct]
    simp [Complex.mul_re]
  have hM : ∀ z a, e.repr (SR z) a = ∑ c, M a c * e.repr z c := by
    intro z a
    have := LinearMap.toMatrix_mulVec_repr e e SR z
    rw [← this]
    rfl
  have hG : (Matrix.of fun i j => (v i ⬝ᵥ Hm.mulVec (star (v j))).im) =
      P.transpose * M.transpose * P := by
    ext i j
    simp only [Matrix.of_apply, hS, Matrix.mul_apply, Matrix.transpose_apply]
    rw [he]
    have : ∀ a, e.repr (S (v i)) a = ∑ c, M a c * e.repr (v i) c := fun a => hM (v i) a
    simp only [this, Finset.sum_mul]
    refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun c _ => ?_
    simp only [P, Module.Basis.toMatrix_apply]
    ring
  have hdetM : M.det = Complex.normSq Hm.det := by
    have h1 : M.det = LinearMap.det SR := LinearMap.det_toMatrix e SR
    have h2 : LinearMap.det SR = Complex.normSq (LinearMap.det S) := by
      rw [show LinearMap.det SR = Algebra.norm ℝ (LinearMap.det S) from
        LinearMap.det_restrictScalars, Algebra.norm_complex_apply]
    rw [h1, h2]
    simp only [S, LinearMap.det_smul, LinearMap.det_toLin', Matrix.det_transpose, map_mul, map_pow]
    simp
  rw [hG, Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose, Matrix.det_transpose, hdetM,
    Module.Basis.det_apply]
  ring

theorem abs_det_gram_eq_one {V ι : Type*} [AddCommGroup V] [Module ℝ V] [Fintype ι] [DecidableEq ι]
    (E : V →ₗ[ℝ] V →ₗ[ℝ] ℝ) (bR : Module.Basis ι ℝ V)
    (hdet : (Matrix.of fun i j => E (bR i) (bR j)).det ≠ 0)
    (hint : ∀ i j, ∃ k : ℤ, E (bR i) (bR j) = k)
    (hself : ∀ w, (∀ j, ∃ k : ℤ, E w (bR j) = k) → ∀ i, ∃ k : ℤ, bR.repr w i = k) :
    |(Matrix.of fun i j => E (bR i) (bR j)).det| = 1 := by
  set G : Matrix ι ι ℝ := Matrix.of fun i j => E (bR i) (bR j) with hGdef
  have hunit : IsUnit G.det := isUnit_iff_ne_zero.mpr hdet
  let C : Matrix ι ι ℝ := G⁻¹
  have hCG : C * G = 1 := Matrix.nonsing_inv_mul G hunit
  let w : ι → V := fun i => ∑ k, C i k • bR k
  have hw : ∀ i j, E (w i) (bR j) = (1 : Matrix ι ι ℝ) i j := by
    intro i j
    rw [← hCG, Matrix.mul_apply]
    simp [w, hGdef]
  have hCint : ∀ i k, ∃ n : ℤ, C i k = n := by
    intro i k
    obtain ⟨n, hn⟩ := hself (w i) (fun j => by
      rw [hw, Matrix.one_apply]
      split_ifs
      · exact ⟨1, by simp⟩
      · exact ⟨0, by simp⟩) k
    refine ⟨n, ?_⟩
    rw [← hn]
    simp [w, Finsupp.single_apply]
  choose Cz hCz using hCint
  choose Gz hGz using hint
  have hmul : (Matrix.of Cz) * (Matrix.of Gz) = 1 := by
    have : ((Matrix.of Cz) * (Matrix.of Gz)).map (Int.castRingHom ℝ) = (1 : Matrix ι ι ℤ).map (Int.castRingHom ℝ) := by
      rw [Matrix.map_mul, Matrix.map_one _ (by simp) (by simp), ← hCG]
      congr 1
      · ext i j; simp [hCz]
      · ext i j; simp [hGdef, hGz]
    exact Matrix.map_injective (Int.cast_injective) this
  have hu : IsUnit (Matrix.of Gz).det :=
    IsUnit.of_mul_eq_one _ (by rw [mul_comm, ← Matrix.det_mul, hmul, Matrix.det_one])
  have hGm : G = (Matrix.of Gz).map (Int.castRingHom ℝ) := by
    ext i j; simp [hGdef, hGz]
  have hd : G.det = (((Matrix.of Gz).det : ℤ) : ℝ) := by
    rw [hGm]
    exact ((Int.castRingHom ℝ).map_det _).symm
  rw [hd]
  rcases Int.isUnit_iff.mp hu with h | h <;> simp [h]

noncomputable def imForm {g : ℕ} (Hm : Matrix (Fin g) (Fin g) ℂ) :
    (Fin g → ℂ) →ₗ[ℝ] (Fin g → ℂ) →ₗ[ℝ] ℝ :=
  LinearMap.mk₂ ℝ (fun z w => (z ⬝ᵥ Hm.mulVec (star w)).im)
    (fun z z' w => by simp [add_dotProduct])
    (fun c z w => by simp [smul_dotProduct])
    (fun z w w' => by simp [Matrix.mulVec_add, dotProduct_add])
    (fun c z w => by
      have : star (c • w) = c • star w := by ext j; simp
      rw [this, Matrix.mulVec_smul, dotProduct_smul]
      simp)

theorem imForm_apply {g : ℕ} (Hm : Matrix (Fin g) (Fin g) ℂ) (z w : Fin g → ℂ) :
    imForm Hm z w = (z ⬝ᵥ Hm.mulVec (star w)).im := rfl

theorem volume_mul_norm_det_eq_one :
    ∀ (g : ℕ) (Λ : Submodule ℤ (Fin g → ℂ)) (Hm : Matrix (Fin g) (Fin g) ℂ),
      DiscreteTopology Λ → Submodule.span ℝ (Λ : Set (Fin g → ℂ)) = ⊤ → Hm.IsHermitian →
      (∀ z : Fin g → ℂ, z ≠ 0 → 0 < (z ⬝ᵥ Hm.mulVec (star z)).re) →
      (∀ l ∈ Λ, ∀ l' ∈ Λ, ∃ k : ℤ, (l ⬝ᵥ Hm.mulVec (star l')).im = k) →
      (∀ w : Fin g → ℂ, (∀ l ∈ Λ, ∃ k : ℤ, (w ⬝ᵥ Hm.mulVec (star l)).im = k) → w ∈ Λ) →
      ∀ Fd : Set (Fin g → ℂ), IsAddFundamentalDomain Λ Fd volume →
        (volume Fd).toReal * ‖Hm.det‖ = 1 := by
  intro g Λ Hm hd hs _ hpos hint hself Fd hFd
  haveI := hd
  haveI : IsZLattice ℝ Λ := ⟨hs⟩
  haveI : Module.Free ℤ Λ := ZLattice.module_free ℝ Λ
  haveI : Module.Finite ℤ Λ := ZLattice.module_finite ℝ Λ
  let e := stdBasis g
  let b0 := Module.Free.chooseBasis ℤ Λ
  let b : Module.Basis (Σ _ : Fin g, Fin 2) ℤ Λ :=
    b0.reindex ((b0.ofZLatticeBasis ℝ Λ).indexEquiv e)
  let bR := b.ofZLatticeBasis ℝ Λ
  have hbR : ∀ i, bR i = (b i : Fin g → ℂ) := fun i => Module.Basis.ofZLatticeBasis_apply ℝ Λ b i
  have hval : (Subtype.val ∘ ⇑b) = ⇑bR := by
    funext i
    exact (hbR i).symm
  have hvol : (volume Fd).toReal = |e.det bR| := by
    have h1 := ZLattice.covolume_eq_measure_fundamentalDomain Λ volume hFd
    have h2 := ZLattice.covolume_eq_det_mul_measureReal Λ volume b e
    rw [volume_fundamentalDomain_stdBasis, mul_one, hval] at h2
    rw [← h2, h1]
    rfl
  have hGdet : (Matrix.of fun i j => imForm Hm (bR i) (bR j)).det =
      (e.det bR) ^ 2 * Complex.normSq Hm.det :=
    det_gram e re_dotProduct_star Hm bR
  have hD : e.det bR ≠ 0 := (e.isUnit_det bR).ne_zero
  have hN : Complex.normSq Hm.det ≠ 0 := by
    simpa using det_ne_zero_of_pos hpos
  have hcomb : ∀ (w : Fin g → ℂ), (∀ j, ∃ k : ℤ, imForm Hm w (bR j) = k) →
      ∀ l ∈ Λ, ∃ k : ℤ, (w ⬝ᵥ Hm.mulVec (star l)).im = k := by
    intro w hw l hl
    choose k hk using hw
    have hl' : l = ∑ j, ((b.repr ⟨l, hl⟩ j : ℤ) : ℝ) • bR j := by
      conv_lhs => rw [← bR.sum_repr l]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [show bR.repr l j = _ from Module.Basis.ofZLatticeBasis_repr_apply ℝ Λ b ⟨l, hl⟩ j]
    refine ⟨∑ j, b.repr ⟨l, hl⟩ j * k j, ?_⟩
    rw [← imForm_apply]
    conv_lhs => rw [hl']
    set_option synthInstance.maxHeartbeats 100000 in
      simp [map_sum, hk]
  have hone := abs_det_gram_eq_one (imForm Hm) bR
    (by rw [hGdet]; exact mul_ne_zero (pow_ne_zero 2 hD) hN)
    (fun i j => by
      rw [hbR, hbR]
      exact hint _ (b i).2 _ (b j).2)
    (fun w hw i => by
      have hwΛ : w ∈ Λ := hself w (hcomb w hw)
      exact ⟨b.repr ⟨w, hwΛ⟩ i, Module.Basis.ofZLatticeBasis_repr_apply ℝ Λ b ⟨w, hwΛ⟩ i⟩)
  have hnn : 0 ≤ (e.det bR) ^ 2 * Complex.normSq Hm.det :=
    mul_nonneg (sq_nonneg _) (Complex.normSq_nonneg _)
  rw [hGdet, abs_of_nonneg hnn, Complex.normSq_eq_norm_sq] at hone
  rw [hvol]
  have h0 : 0 ≤ |e.det bR| * ‖Hm.det‖ := by positivity
  refine (pow_eq_one_iff_of_nonneg h0 two_ne_zero).mp ?_
  rw [mul_pow, sq_abs]
  exact hone

end GlobalTheory.CompanionTheory.Ar.Sl.SelfDualCovol
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.LocalHomCharZeroUnits
section
open AlgebraicGeometry CategoryTheory

namespace GlobalTheory.CompanionTheory.Ggeo

private theorem map_aeval_int' {A B : Type*} [CommRing A] [CommRing B] (f : A →+* B) (a : A)
    (q : Polynomial ℤ) : f (Polynomial.aeval a q) = Polynomial.aeval (f a) q := by
  rw [Polynomial.aeval_def, Polynomial.aeval_def, Polynomial.hom_eval₂,
    RingHom.ext_int (f.comp (algebraMap ℤ A)) (algebraMap ℤ B)]

theorem unit_of_local_hom_charZero_nf : ∀ (O F L K : Type) [CommRing O] [Field F] [NumberField F] [CommRing L] [Field K] [CharZero K] (β : O →+* F) (θ : O →+* L) (ρ : L →+* K), IsLocalHom ρ → (∀ a, β a = 0 → θ a = 0) → ∀ b, β b ≠ 0 → IsUnit (θ b) := by
  intro O F L K _ _ _ _ _ _ β θ ρ hρ hker b hb
  have halg : IsAlgebraic ℤ (β b) :=
    (IsFractionRing.isAlgebraic_iff ℤ ℚ F).mpr (Algebra.IsAlgebraic.isAlgebraic (β b))
  obtain ⟨q, hq0, hq⟩ :=
    halg.exists_nonzero_coeff_and_aeval_eq_zero (mem_nonZeroDivisors_of_ne_zero hb)
  have h1 : β (Polynomial.aeval b q) = 0 := by rw [map_aeval_int', hq]
  have h2 : ρ (θ (Polynomial.aeval b q)) = 0 := by rw [hker _ h1, map_zero]
  rw [map_aeval_int', map_aeval_int'] at h2
  have h3 : ρ (θ b) ≠ 0 := by
    intro h0
    rw [h0, ← Polynomial.coeff_zero_eq_aeval_zero'] at h2
    exact hq0 (by simpa using h2)
  exact hρ.map_nonunit _ (isUnit_iff_ne_zero.mpr h3)

end GlobalTheory.CompanionTheory.Ggeo
end

