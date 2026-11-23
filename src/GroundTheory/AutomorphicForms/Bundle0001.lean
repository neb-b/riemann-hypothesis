module

public import Mathlib

@[expose] public section

-- bundled from GroundTheory.AutomorphicForms.AnisotropicRestrict
section
set_option maxSynthPendingDepth 1

open Matrix TensorProduct

set_option linter.unusedSectionVars false

namespace GroundTheory.Automorphic

noncomputable section

namespace Anisotropic

variable {K : Type*} [Field K] {κ : Type*} [Fintype κ] [DecidableEq κ]

section General

variable {A : Type*} [Ring A] [Algebra K A] (b : Module.Basis κ K A)
variable (R : Type*) [CommRing R] [Algebra K R]

abbrev baseBasis : Module.Basis κ R (R ⊗[K] A) := Algebra.TensorProduct.basis R b

def coords : (R ⊗[K] A) ≃ₗ[R] (κ → R) := (baseBasis b R).equivFun

theorem baseBasis_apply (k : κ) : baseBasis b R k = 1 ⊗ₜ b k :=
  Algebra.TensorProduct.basis_apply b k

theorem coords_baseBasis (k : κ) : coords b R (baseBasis b R k) = Pi.single k 1 := by
  funext l
  rw [coords, Module.Basis.equivFun_self, Pi.single_apply]
  exact if_congr eq_comm rfl rfl

theorem eq_sum_coords (z : R ⊗[K] A) : z = ∑ k, coords b R z k • baseBasis b R k :=
  ((baseBasis b R).sum_equivFun z).symm

def rmat (x : R ⊗[K] A) : Matrix κ κ R := fun k => coords b R (baseBasis b R k * x)

def lmat (a : R ⊗[K] A) : Matrix κ κ R := fun k => coords b R (a * baseBasis b R k)

theorem coords_mul (z x : R ⊗[K] A) : coords b R (z * x) = coords b R z ᵥ* rmat b R x := by
  conv_lhs => rw [eq_sum_coords b R z]
  set_option synthInstance.maxHeartbeats 100000 in
    rw [Finset.sum_mul, map_sum]
  funext l
  simp only [smul_mul_assoc, map_smul, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, vecMul,
    dotProduct, rmat]

theorem coords_mul_left (a z : R ⊗[K] A) : coords b R (a * z) = coords b R z ᵥ* lmat b R a := by
  conv_lhs => rw [eq_sum_coords b R z]
  set_option synthInstance.maxHeartbeats 100000 in
    rw [Finset.mul_sum, map_sum]
  funext l
  simp only [mul_smul_comm, map_smul, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, vecMul,
    dotProduct, lmat]

theorem rmat_mul (x y : R ⊗[K] A) : rmat b R (x * y) = rmat b R x * rmat b R y := by
  ext k l
  simp only [rmat]
  rw [← mul_assoc, coords_mul]
  simp only [vecMul, dotProduct, Matrix.mul_apply, rmat]

theorem rmat_one : rmat b R 1 = 1 := by
  ext k l
  simp only [rmat, mul_one, coords_baseBasis, Pi.single_apply, Matrix.one_apply, eq_comm]

def rmatHom : R ⊗[K] A →ₐ[R] Matrix κ κ R :=
  AlgHom.ofLinearMap
    { toFun := rmat b R
      map_add' := fun x y => by
        ext k l
        simp [rmat, mul_add]
      map_smul' := fun c x => by
        ext k l
        simp [rmat] }
    (rmat_one b R) (rmat_mul b R)

@[simp]
theorem rmatHom_apply (x : R ⊗[K] A) : rmatHom b R x = rmat b R x := rfl

theorem rmat_injective : Function.Injective (rmat b R) := by
  intro x y h
  have hx := coords_mul b R 1 x
  have hy := coords_mul b R 1 y
  rw [one_mul] at hx hy
  rw [h] at hx
  exact (coords b R).injective (hx.trans hy.symm)

theorem exists_rmat_eq (g : Matrix κ κ R)
    (hg : ∀ j, lmat b R (baseBasis b R j) * g = g * lmat b R (baseBasis b R j)) :
    ∃ x, rmat b R x = g := by
  let φ : R ⊗[K] A →ₗ[R] R ⊗[K] A :=
    (coords b R).symm.toLinearMap ∘ₗ g.vecMulLinear ∘ₗ (coords b R).toLinearMap
  have hφ : ∀ z, coords b R (φ z) = coords b R z ᵥ* g := by
    intro z
    simp [φ]
  have hj : ∀ j z, φ (baseBasis b R j * z) = baseBasis b R j * φ z := by
    intro j z
    apply (coords b R).injective
    rw [hφ, coords_mul_left, coords_mul_left, hφ, vecMul_vecMul, vecMul_vecMul, hg]
  have ha : ∀ a z, φ (a * z) = a * φ z := by
    intro a z
    set_option synthInstance.maxHeartbeats 100000 in
      rw [eq_sum_coords b R a, Finset.sum_mul, Finset.sum_mul, map_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [smul_mul_assoc, smul_mul_assoc, map_smul, hj]
  refine ⟨φ 1, ?_⟩
  ext k l
  have h1 : baseBasis b R k * φ 1 = φ (baseBasis b R k) := by rw [← ha, mul_one]
  simp only [rmat, h1, hφ, coords_baseBasis, single_one_vecMul, Matrix.row_apply]

variable {R} {R' : Type*} [CommRing R'] [Algebra K R']

def baseMap (f : R →ₐ[K] R') : R ⊗[K] A →ₐ[K] R' ⊗[K] A :=
  Algebra.TensorProduct.map f (AlgHom.id K A)

theorem baseMap_baseBasis (f : R →ₐ[K] R') (k : κ) :
    baseMap f (baseBasis b R k) = baseBasis b R' k := by
  rw [baseBasis_apply, baseBasis_apply, baseMap, Algebra.TensorProduct.map_tmul, map_one]
  rfl

theorem coords_baseMap (f : R →ₐ[K] R') (z : R ⊗[K] A) :
    coords b R' (baseMap f z) = f ∘ coords b R z := by
  have h : ∀ k, baseMap f (coords b R z k • baseBasis b R k) =
      f (coords b R z k) • baseBasis b R' k := by
    intro k
    simp only [baseBasis_apply, baseMap, TensorProduct.smul_tmul', smul_eq_mul, mul_one,
      Algebra.TensorProduct.map_tmul, AlgHom.coe_id, id_eq]
  conv_lhs => rw [eq_sum_coords b R z]
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sum, Finset.sum_congr rfl fun k _ => h k, map_sum]
  funext l
  rw [Finset.sum_apply]
  simp only [map_smul, Pi.smul_apply, coords_baseBasis, smul_eq_mul, Pi.single_apply, mul_ite,
    mul_one, mul_zero, Function.comp_apply]
  rw [Finset.sum_ite_eq]
  simp

theorem rmat_baseMap (f : R →ₐ[K] R') (x : R ⊗[K] A) :
    rmat b R' (baseMap f x) = (rmat b R x).map f := by
  ext k l
  simp only [rmat, Matrix.map_apply, ← baseMap_baseBasis b f k, ← map_mul, coords_baseMap,
    Function.comp_apply]

end General

section Block

variable {E : Type*} [CommRing E] [Algebra K E] (b : Module.Basis κ K E)
variable (R : Type*) [CommRing R] [Algebra K R] {R' : Type*} [CommRing R'] [Algebra K R']
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem lmat_eq_rmat (a : R ⊗[K] E) : lmat b R a = rmat b R a := by
  ext k l
  simp only [lmat, rmat, mul_comm]

def blockHom : Matrix ι ι (R ⊗[K] E) →ₐ[R] Matrix (ι × κ) (ι × κ) R :=
  (Matrix.compAlgEquiv ι κ R R).toAlgHom.comp (rmatHom b R).mapMatrix

theorem blockHom_apply (M : Matrix ι ι (R ⊗[K] E)) (i j : ι) (k l : κ) :
    blockHom b R M (i, k) (j, l) = rmat b R (M i j) k l := rfl

theorem blockHom_injective : Function.Injective (blockHom (ι := ι) b R) := by
  intro M M' h
  ext i j : 2
  apply rmat_injective b R
  ext k l
  exact congrFun (congrFun h (i, k)) (j, l)

def coordsVec (x : ι → R ⊗[K] E) : ι × κ → R := fun p => coords b R (x p.1) p.2

theorem coordsVec_vecMul (x : ι → R ⊗[K] E) (M : Matrix ι ι (R ⊗[K] E)) :
    coordsVec b R (x ᵥ* M) = coordsVec b R x ᵥ* blockHom b R M := by
  funext ⟨j, l⟩
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [coordsVec, vecMul, dotProduct, map_sum, Finset.sum_apply, coords_mul,
    Fintype.sum_prod_type, blockHom_apply]

theorem exists_blockHom_eq (g : Matrix (ι × κ) (ι × κ) R)
    (hg : ∀ j, blockHom b R (Matrix.scalar ι (baseBasis b R j)) * g =
      g * blockHom b R (Matrix.scalar ι (baseBasis b R j))) :
    ∃ M, blockHom b R M = g := by
  have hsc : ∀ j, blockHom b R (Matrix.scalar ι (baseBasis b R j)) =
      Matrix.compAlgEquiv ι κ R R (Matrix.scalar ι (rmat b R (baseBasis b R j))) := by
    intro j
    simp only [blockHom, AlgHom.comp_apply, AlgHom.mapMatrix_apply, Matrix.scalar_apply,
      Matrix.diagonal_map (map_zero _), rmatHom_apply]
    rfl
  have hcomm : ∀ j i i', rmat b R (baseBasis b R j) * (Matrix.comp ι ι κ κ R).symm g i i' =
      (Matrix.comp ι ι κ κ R).symm g i i' * rmat b R (baseBasis b R j) := by
    intro j i i'
    have h := hg j
    rw [hsc, ← (Matrix.compAlgEquiv ι κ R R).apply_symm_apply g, ← map_mul, ← map_mul] at h
    have h2 := (Matrix.compAlgEquiv ι κ R R).injective h
    have h3 := congrFun (congrFun h2 i) i'
    simpa [Matrix.scalar_apply, Matrix.diagonal_mul, Matrix.mul_diagonal] using h3
  have hx : ∀ i i', ∃ x, rmat b R x = (Matrix.comp ι ι κ κ R).symm g i i' := fun i i' =>
    exists_rmat_eq b R _ fun j => by rw [lmat_eq_rmat]; exact hcomm j i i'
  choose M hM using hx
  refine ⟨Matrix.of M, ?_⟩
  ext ⟨i, k⟩ ⟨i', l⟩
  rw [blockHom_apply, Matrix.of_apply, hM i i']
  rfl

variable {R}

theorem blockHom_baseMap (f : R →ₐ[K] R') (M : Matrix ι ι (R ⊗[K] E)) :
    blockHom b R' (M.map (baseMap f)) = (blockHom b R M).map f := by
  ext ⟨i, k⟩ ⟨j, l⟩
  simp only [blockHom_apply, Matrix.map_apply, rmat_baseMap]

theorem coordsVec_baseMap (f : R →ₐ[K] R') (x : ι → R ⊗[K] E) :
    coordsVec b R' (fun i => baseMap f (x i)) = f ∘ coordsVec b R x := by
  funext ⟨i, k⟩
  simp only [coordsVec, coords_baseMap, Function.comp_apply]

end Block

end Anisotropic

end

end GroundTheory.Automorphic
end

-- bundled from GroundTheory.AutomorphicForms.CompactSelfAdjoint
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Automorphic.CompactSelfAdjoint

open Module End Submodule Filter Topology
open scoped InnerProductSpace ComplexConjugate

variable {𝕜 : Type*} [RCLike 𝕜] {E : Type*} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]

theorem finite_setOf_mem_of_orthonormal {ι : Type*} {v : ι → E} (hv : Orthonormal 𝕜 v)
    (W : Submodule 𝕜 E) [FiniteDimensional 𝕜 W] : {i | v i ∈ W}.Finite := by
  let f : {i | v i ∈ W} → W := fun i => ⟨v i, i.2⟩
  have hf : LinearIndependent 𝕜 f := by
    apply LinearIndependent.of_comp W.subtype
    exact hv.linearIndependent.comp _ Subtype.val_injective
  exact Set.finite_coe_iff.1 hf.finite_of_isNoetherian

theorem isClosed_eigenspace (T : E →L[𝕜] E) (μ : 𝕜) :
    IsClosed (eigenspace (T : E →ₗ[𝕜] E) μ : Set E) := by
  have : (eigenspace (T : E →ₗ[𝕜] E) μ : Set E) =
      (T - μ • ContinuousLinearMap.id 𝕜 E) ⁻¹' {0} := by
    ext x
    simp [sub_eq_zero]
  rw [this]
  exact isClosed_singleton.preimage (map_continuous _)

section HilbertBasis

variable [CompleteSpace E]

theorem exists_hilbertBasis_subset_iUnion {α : Type*} (W : α → Submodule 𝕜 E)
    (hW : OrthogonalFamily 𝕜 (fun a => W a) fun a => (W a).subtypeₗᵢ)
    (hc : ∀ a, IsClosed (W a : Set E)) (hbot : (⨆ a, W a)ᗮ = ⊥) :
    ∃ (s : Set E) (b : HilbertBasis s 𝕜 E), ⇑b = ((↑) : s → E) ∧ s ⊆ ⋃ a, (W a : Set E) := by
  classical
  have : ∀ a, CompleteSpace (W a) := fun a =>
    completeSpace_coe_iff_isComplete.2 (hc a).isComplete
  choose w b hb using fun a => exists_hilbertBasis 𝕜 (W a)
  let v : (Σ a, w a) → E := fun p => ((p.2 : W p.1) : E)
  have hv : Orthonormal 𝕜 v :=
    hW.orthonormal_sigma_orthonormal (v_family := fun a => ((↑) : w a → W a))
      (fun a => by rw [← hb a]; exact (b a).orthonormal)
  have hkey : ∀ a, (W a : Set E) ⊆ closure (span 𝕜 (Set.range v) : Set E) := by
    intro a y hy
    let y' : W a := ⟨y, hy⟩
    have h := (W a).subtypeL.hasSum ((b a).hasSum_repr y')
    refine mem_closure_of_tendsto h (Eventually.of_forall fun t => ?_)
    refine Submodule.sum_mem _ fun i _ => ?_
    simp only [map_smul]
    refine Submodule.smul_mem _ _ (subset_span ⟨⟨a, i⟩, ?_⟩)
    simp [v, hb a]
  have hle : (⨆ a, W a) ≤ (span 𝕜 (Set.range v))ᗮᗮ := by
    rw [Submodule.orthogonal_orthogonal_eq_closure, iSup_le_iff]
    intro a y hy
    rw [← SetLike.mem_coe, Submodule.topologicalClosure_coe]
    exact hkey a hy
  have hspan : (span 𝕜 (Set.range v))ᗮ = ⊥ := by
    rw [eq_bot_iff, ← hbot, ← Submodule.triorthogonal_eq_orthogonal]
    exact Submodule.orthogonal_le hle
  have hinj : Function.Injective v := hv.linearIndependent.injective
  have hv' : Orthonormal 𝕜 ((↑) : Set.range v → E) := (orthonormal_subtype_range hinj).2 hv
  have hspan' : (span 𝕜 (Set.range ((↑) : Set.range v → E)))ᗮ = ⊥ := by
    rwa [Subtype.range_coe]
  refine ⟨Set.range v, HilbertBasis.mkOfOrthogonalEqBot hv' hspan',
    HilbertBasis.coe_mkOfOrthogonalEqBot hv' hspan', ?_⟩
  rintro _ ⟨p, rfl⟩
  exact Set.mem_iUnion.2 ⟨p.1, (p.2 : W p.1).2⟩

end HilbertBasis

section Spectrum

variable {T : E →L[𝕜] E}

variable [CompleteSpace E]

theorem exists_real_of_hasEigenvalue (hT' : IsSelfAdjoint T) {μ : 𝕜}
    (hμ : HasEigenvalue (T : E →ₗ[𝕜] E) μ) : ∃ r : ℝ, μ = r :=
  RCLike.conj_eq_iff_real.1
    ((ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.1 hT').conj_eigenvalue_eq_self hμ)

theorem finite_eigenvalues_norm_ge (hT : IsCompactOperator T) (hT' : IsSelfAdjoint T) {ε : ℝ}
    (hε : 0 < ε) : {μ : 𝕜 | HasEigenvalue (T : E →ₗ[𝕜] E) μ ∧ ε ≤ ‖μ‖}.Finite := by
  have hS := ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.1 hT'
  by_contra hinf
  set S := {μ : 𝕜 | HasEigenvalue (T : E →ₗ[𝕜] E) μ ∧ ε ≤ ‖μ‖}
  have : Infinite S := Set.infinite_coe_iff.2 hinf
  let f : ℕ ↪ S := Infinite.natEmbedding S
  have hv : ∀ n, ∃ v : E, T v = ((f n : 𝕜)) • v ∧ ‖v‖ = 1 := by
    intro n
    obtain ⟨v, hv1, hv2⟩ := (f n).2.1.exists_hasEigenvector
    refine ⟨((‖v‖⁻¹ : ℝ) : 𝕜) • v, ?_, ?_⟩
    · rw [map_smul, show T v = (f n : 𝕜) • v from mem_eigenspace_iff.1 hv1, smul_comm]
    · rw [norm_smul, RCLike.norm_ofReal, abs_inv, abs_norm,
        inv_mul_cancel₀ (norm_ne_zero_iff.2 hv2)]
  choose v hvT hvn using hv
  obtain ⟨K, hK, hK'⟩ := hT.image_closedBall_subset_compact 1
  obtain ⟨y, -, ψ, hψ, hψy⟩ :=
    hK.tendsto_subseq (fun n => hK' ⟨v n, by simp [hvn], rfl⟩)
  obtain ⟨N, hN⟩ := Metric.cauchySeq_iff'.1 hψy.cauchySeq ε hε
  have h1 : dist (T (v (ψ (N + 1)))) (T (v (ψ N))) < ε := hN (N + 1) (Nat.le_succ N)
  set a := ψ (N + 1)
  set b := ψ N
  have hne : (f a : 𝕜) ≠ f b := by
    intro h
    have := f.injective (Subtype.ext h)
    exact (hψ (Nat.lt_succ_self N)).ne this.symm
  have horth : ⟪v a, v b⟫_𝕜 = 0 := by
    have := hS.orthogonalFamily_eigenspaces hne ⟨v a, mem_eigenspace_iff.2 (hvT a)⟩
      ⟨v b, mem_eigenspace_iff.2 (hvT b)⟩
    simpa using this
  have hx : ⟪T (v a), T (v b)⟫_𝕜 = 0 := by
    rw [hvT, hvT, inner_smul_left, inner_smul_right, horth, mul_zero, mul_zero]
  have hnx : ε ≤ ‖T (v a)‖ := by
    rw [hvT, norm_smul, hvn, mul_one]
    exact (f a).2.2
  have hsq := norm_sub_sq (𝕜 := 𝕜) (T (v a)) (T (v b))
  rw [hx, map_zero, mul_zero, sub_zero] at hsq
  rw [dist_eq_norm] at h1
  have h2 : 0 ≤ ‖T (v a) - T (v b)‖ := norm_nonneg _
  nlinarith [sq_nonneg ‖T (v b)‖]

end Spectrum

section Eigenbasis

variable [CompleteSpace E]

theorem exists_hilbertBasis_eigenvectors {T : E →L[𝕜] E} (hT : IsCompactOperator T)
    (hT' : IsSelfAdjoint T) :
    ∃ (s : Set E) (b : HilbertBasis s 𝕜 E), ⇑b = ((↑) : s → E) ∧
      ∀ v ∈ s, ∃ μ : ℝ, T v = (μ : 𝕜) • v := by
  have hS := ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.1 hT'
  obtain ⟨s, b, hb, hs⟩ := exists_hilbertBasis_subset_iUnion
    (fun μ => eigenspace (T : E →ₗ[𝕜] E) μ) hS.orthogonalFamily_eigenspaces
    (isClosed_eigenspace T) (ContinuousLinearMap.orthogonalComplement_iSup_eigenspaces_eq_bot hT hS)
  refine ⟨s, b, hb, fun v hv => ?_⟩
  obtain ⟨μ, hμ⟩ := Set.mem_iUnion.1 (hs hv)
  have hv0 : v ≠ 0 := by
    have h := b.orthonormal.1 ⟨v, hv⟩
    rw [hb] at h
    intro h0
    simp [h0] at h
  have hE : HasEigenvalue (T : E →ₗ[𝕜] E) μ := hasEigenvalue_of_hasEigenvector ⟨hμ, hv0⟩
  obtain ⟨r, hr⟩ := exists_real_of_hasEigenvalue hT' hE
  exact ⟨r, by rw [← hr]; exact mem_eigenspace_iff.1 hμ⟩

theorem exists_hilbertBasis_eigenvectors_hasSum {T : E →L[𝕜] E} (hT : IsCompactOperator T)
    (hT' : IsSelfAdjoint T) :
    ∃ (s : Set E) (b : HilbertBasis s 𝕜 E) (l : s → ℝ), ⇑b = ((↑) : s → E) ∧
      (∀ i, T (b i) = (l i : 𝕜) • b i) ∧
      (∀ x, HasSum (fun i => ((l i : 𝕜) * ⟪b i, x⟫_𝕜) • b i) (T x)) ∧
      ∀ ε > 0, {i | ε ≤ |l i|}.Finite := by
  obtain ⟨s, b, hb, hs⟩ := exists_hilbertBasis_eigenvectors hT hT'
  choose l hl using fun i : s => hs i i.2
  have hTb : ∀ i, T (b i) = (l i : 𝕜) • b i := fun i => by rw [hb]; exact hl i
  refine ⟨s, b, l, hb, hTb, fun x => ?_, fun ε hε => ?_⟩
  · simpa only [map_smul, hTb, smul_smul, b.repr_apply_apply, mul_comm] using
      T.hasSum (b.hasSum_repr x)
  · have hF := finite_eigenvalues_norm_ge hT hT' hε
    have hsub : {i | ε ≤ |l i|} ⊆ ⋃ μ ∈ {μ : 𝕜 | HasEigenvalue (T : E →ₗ[𝕜] E) μ ∧ ε ≤ ‖μ‖},
        {i | b i ∈ eigenspace (T : E →ₗ[𝕜] E) μ} := by
      intro i hi
      have hmem : b i ∈ eigenspace (T : E →ₗ[𝕜] E) (l i : 𝕜) := mem_eigenspace_iff.2 (hTb i)
      have hne : b i ≠ 0 := fun h => by simpa [h] using b.orthonormal.1 i
      refine Set.mem_biUnion (x := (l i : 𝕜))
        ⟨hasEigenvalue_of_hasEigenvector ⟨hmem, hne⟩, ?_⟩ hmem
      simpa [RCLike.norm_ofReal] using hi
    refine (hF.biUnion fun μ hμ => ?_).subset hsub
    have hμ0 : μ ≠ 0 := norm_pos_iff.1 (hε.trans_le hμ.2)
    have := ContinuousLinearMap.finite_dimensional_eigenspace hT μ hμ0
    exact finite_setOf_mem_of_orthonormal b.orthonormal _

end Eigenbasis

end GroundTheory.Automorphic.CompactSelfAdjoint
end

