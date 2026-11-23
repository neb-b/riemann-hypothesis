module

public import Mathlib

@[expose] public section

-- bundled from GroundTheory.AutomorphicForms.LocallyProfinite
section
noncomputable section

namespace GroundTheory.Automorphic

open Set Filter Topology MeasureTheory
open scoped Pointwise

section Space

variable {X : Type*} [TopologicalSpace X] [LocallyCompactSpace X] [T2Space X]
  [TotallyDisconnectedSpace X]

theorem exists_isCompact_isOpen_subset {x : X} {U : Set X} (hU : U ∈ 𝓝 x) :
    ∃ V : Set X, IsCompact V ∧ IsOpen V ∧ x ∈ V ∧ V ⊆ U := by
  obtain ⟨K, hK, hKU, hKc⟩ := local_compact_nhds hU
  obtain ⟨V, hV, hxV, hVK⟩ := loc_compact_Haus_tot_disc_of_zero_dim.mem_nhds_iff.1 hK
  exact ⟨V, hKc.of_isClosed_subset hV.isClosed hVK, hV.isOpen, hxV, hVK.trans hKU⟩

end Space

section VanDantzig

variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [LocallyCompactSpace G] [T2Space G] [TotallyDisconnectedSpace G]

theorem exists_openSubgroup_isCompact_subset {U : Set G} (hU : U ∈ 𝓝 (1 : G)) :
    ∃ K : OpenSubgroup G, IsCompact (K : Set G) ∧ (K : Set G) ⊆ U := by
  obtain ⟨W, hWc, hWo, h1W, hWU⟩ := exists_isCompact_isOpen_subset hU
  obtain ⟨V, hV1, hWV⟩ := compact_open_separated_mul_right hWc hWo subset_rfl

  let H : Subgroup G :=
    { carrier := {x | ∀ w, w ∈ W ↔ w * x ∈ W}
      one_mem' := fun w => by simp
      mul_mem' := fun {a b} ha hb w => by rw [ha w, hb (w * a), mul_assoc]
      inv_mem' := fun {a} ha w => by
        have := ha (w * a⁻¹)
        rw [inv_mul_cancel_right] at this
        exact this.symm }
  have hVH : V ∩ V⁻¹ ⊆ (H : Set G) := by
    rintro v ⟨hv, hv'⟩ w
    refine ⟨fun hw => hWV (Set.mul_mem_mul hw hv), fun hw => ?_⟩
    have := hWV (Set.mul_mem_mul hw (Set.mem_inv.1 hv'))
    rwa [mul_inv_cancel_right] at this
  have hHn : (H : Set G) ∈ 𝓝 (1 : G) :=
    mem_of_superset (inter_mem hV1 (inv_mem_nhds_one G hV1)) hVH
  have hHW : (H : Set G) ⊆ W := fun x hx => by
    have := (hx 1).1 h1W
    rwa [one_mul] at this
  let K : OpenSubgroup G := ⟨H, H.isOpen_of_mem_nhds hHn⟩
  exact ⟨K, hWc.of_isClosed_subset K.isClosed hHW, hHW.trans hWU⟩

theorem hasBasis_nhds_one_compactOpenSubgroup :
    (𝓝 (1 : G)).HasBasis (fun K : OpenSubgroup G => IsCompact (K : Set G))
      (fun K => (K : Set G)) :=
  ⟨fun _ => ⟨fun hU => exists_openSubgroup_isCompact_subset hU,
    fun ⟨K, _, hKU⟩ => mem_of_superset K.mem_nhds_one hKU⟩⟩

theorem exists_compactOpenSubgroup : ∃ K : OpenSubgroup G, IsCompact (K : Set G) := by
  obtain ⟨K, hK, -⟩ := exists_openSubgroup_isCompact_subset (univ_mem : univ ∈ 𝓝 (1 : G))
  exact ⟨K, hK⟩


omit [LocallyCompactSpace G] [T2Space G] [TotallyDisconnectedSpace G] in
theorem isCompact_inf_left {K L : OpenSubgroup G} (hK : IsCompact (K : Set G)) :
    IsCompact ((K ⊓ L : OpenSubgroup G) : Set G) := by
  rw [OpenSubgroup.coe_inf]
  exact hK.inter_right L.isClosed

theorem exists_compactOpenSubgroup_normalized {K : Subgroup G} (hK : IsCompact (K : Set G))
    {U : Set G} (hU : U ∈ 𝓝 (1 : G)) :
    ∃ N : OpenSubgroup G, IsCompact (N : Set G) ∧ (N : Set G) ⊆ U ∧
      ∀ k ∈ K, ∀ n ∈ N, k * n * k⁻¹ ∈ N := by
  obtain ⟨L, hLc, hLU⟩ := exists_openSubgroup_isCompact_subset hU

  have hopen : IsOpen ((fun p : G × G => p.1 * p.2 * p.1⁻¹) ⁻¹' (L : Set G)) :=
    L.isOpen.preimage (by fun_prop)
  have hsub : (K : Set G) ×ˢ ({1} : Set G) ⊆
      (fun p : G × G => p.1 * p.2 * p.1⁻¹) ⁻¹' (L : Set G) := by
    rintro ⟨k, x⟩ ⟨-, hx⟩
    simp only [mem_singleton_iff] at hx
    simp [hx]
  obtain ⟨u, v, -, hv, hKu, h1v, huv⟩ := generalized_tube_lemma hK isCompact_singleton hopen hsub

  let N₀ : Subgroup G :=
    { carrier := {x | ∀ k ∈ K, k * x * k⁻¹ ∈ L}
      one_mem' := fun k _ => by simp
      mul_mem' := fun {a b} ha hb k hk => by
        have := mul_mem (ha k hk) (hb k hk)
        simpa [mul_assoc] using this
      inv_mem' := fun {a} ha k hk => by
        have := inv_mem (ha k hk)
        simpa [mul_assoc] using this }
  have hvN : v ⊆ (N₀ : Set G) := fun x hx k hk =>
    huv (show (k, x) ∈ u ×ˢ v from ⟨hKu hk, hx⟩)
  have hN₀n : (N₀ : Set G) ∈ 𝓝 (1 : G) := mem_of_superset (hv.mem_nhds (h1v rfl)) hvN
  have hN₀L : (N₀ : Set G) ⊆ L := fun x hx => by simpa using hx 1 K.one_mem
  let N : OpenSubgroup G := ⟨N₀, N₀.isOpen_of_mem_nhds hN₀n⟩
  refine ⟨N, hLc.of_isClosed_subset N.isClosed hN₀L, hN₀L.trans hLU, fun k hk n hn j hj => ?_⟩
  have := hn (j * k) (mul_mem hj hk)
  simpa [mul_assoc] using this

end VanDantzig

end GroundTheory.Automorphic
end
end

-- bundled from GroundTheory.AutomorphicForms.QuadraticConj
section
namespace GroundTheory.Automorphic

open Module

variable (F E : Type*) [Field F] [CommRing E] [Algebra F E]

noncomputable def conjLinear : E →ₗ[F] E :=
  (Algebra.linearMap F E).comp (Algebra.trace F E) - LinearMap.id

variable {F E}

theorem conjLinear_apply (x : E) :
    conjLinear F E x = algebraMap F E (Algebra.trace F E x) - x := rfl

variable [Algebra.IsQuadraticExtension F E]

theorem trace_algebraMap_quadratic (c : F) : Algebra.trace F E (algebraMap F E c) = 2 * c := by
  rw [Algebra.trace_algebraMap, Algebra.IsQuadraticExtension.finrank_eq_two, nsmul_eq_mul]
  norm_num

theorem conjLinear_algebraMap (c : F) : conjLinear F E (algebraMap F E c) = algebraMap F E c := by
  rw [conjLinear_apply, trace_algebraMap_quadratic, map_mul, map_ofNat]
  ring

theorem conjLinear_one : conjLinear F E 1 = 1 := by
  simpa using conjLinear_algebraMap (F := F) (E := E) 1


omit [Algebra.IsQuadraticExtension F E] in
theorem linearIndependent_one_of_not_mem [Nontrivial E] {x : E}
    (hx : x ∉ Set.range (algebraMap F E)) : LinearIndependent F ![1, x] := by
  rw [LinearIndependent.pair_iff]
  intro s t hst
  by_cases ht : t = 0
  · subst ht
    simp only [zero_smul, add_zero] at hst
    refine ⟨?_, rfl⟩
    by_contra hs
    exact one_ne_zero ((smul_eq_zero.mp hst).resolve_left hs)
  · exfalso
    apply hx
    refine ⟨-(s / t), ?_⟩
    have : t • x = -(s • (1 : E)) := eq_neg_of_add_eq_zero_right hst
    rw [Algebra.algebraMap_eq_smul_one]
    have h2 : x = t⁻¹ • (t • x) := by rw [smul_smul, inv_mul_cancel₀ ht, one_smul]
    rw [h2, this, smul_neg, smul_smul, neg_smul, div_eq_inv_mul]

theorem nontrivial_quadratic (K A : Type*) [Field K] [CommRing A] [Algebra K A]
    [Algebra.IsQuadraticExtension K A] : Nontrivial A :=
  Module.nontrivial_of_finrank_pos (R := K) (by
    rw [Algebra.IsQuadraticExtension.finrank_eq_two]; norm_num)

noncomputable def basisOneOf {x : E} (hx : x ∉ Set.range (algebraMap F E)) : Basis (Fin 2) F E :=
  haveI := nontrivial_quadratic F E
  basisOfLinearIndependentOfCardEqFinrank (linearIndependent_one_of_not_mem hx)
    (by rw [Algebra.IsQuadraticExtension.finrank_eq_two, Fintype.card_fin])

theorem basisOneOf_zero {x : E} (hx : x ∉ Set.range (algebraMap F E)) : basisOneOf hx 0 = 1 := by
  simp [basisOneOf]

theorem basisOneOf_one {x : E} (hx : x ∉ Set.range (algebraMap F E)) : basisOneOf hx 1 = x := by
  simp [basisOneOf]

theorem sq_eq_of_not_mem {x : E} (hx : x ∉ Set.range (algebraMap F E)) :
    x * x = algebraMap F E ((basisOneOf hx).repr (x * x) 0) +
      algebraMap F E ((basisOneOf hx).repr (x * x) 1) * x := by
  conv_lhs => rw [← (basisOneOf hx).sum_repr (x * x)]
  rw [Fin.sum_univ_two, basisOneOf_zero, basisOneOf_one, Algebra.smul_def, Algebra.smul_def,
    mul_one]

theorem repr_self_zero {x : E} (hx : x ∉ Set.range (algebraMap F E)) :
    (basisOneOf hx).repr x 0 = 0 := by
  have h := (basisOneOf hx).repr_self 1
  rw [basisOneOf_one] at h
  rw [h]; simp

theorem repr_self_one {x : E} (hx : x ∉ Set.range (algebraMap F E)) :
    (basisOneOf hx).repr x 1 = 1 := by
  have h := (basisOneOf hx).repr_self 1
  rw [basisOneOf_one] at h
  rw [h]; simp

theorem trace_eq_of_not_mem {x : E} (hx : x ∉ Set.range (algebraMap F E)) :
    Algebra.trace F E x = (basisOneOf hx).repr (x * x) 1 := by
  rw [Algebra.trace_eq_matrix_trace (basisOneOf hx), Matrix.trace_fin_two,
    Algebra.leftMulMatrix_eq_repr_mul, Algebra.leftMulMatrix_eq_repr_mul, basisOneOf_zero,
    basisOneOf_one, mul_one, repr_self_zero, zero_add]

theorem norm_eq_of_not_mem {x : E} (hx : x ∉ Set.range (algebraMap F E)) :
    Algebra.norm F x = -(basisOneOf hx).repr (x * x) 0 := by
  rw [Algebra.norm_eq_matrix_det (basisOneOf hx), Matrix.det_fin_two,
    Algebra.leftMulMatrix_eq_repr_mul, Algebra.leftMulMatrix_eq_repr_mul,
    Algebra.leftMulMatrix_eq_repr_mul, Algebra.leftMulMatrix_eq_repr_mul, basisOneOf_zero,
    basisOneOf_one, mul_one, repr_self_zero, repr_self_one]
  ring

theorem conjLinear_mul_self (x : E) :
    conjLinear F E (x * x) = conjLinear F E x * conjLinear F E x := by
  by_cases hx : x ∈ Set.range (algebraMap F E)
  · obtain ⟨c, rfl⟩ := hx
    rw [← map_mul, conjLinear_algebraMap, conjLinear_algebraMap, map_mul]
  · have hsq := sq_eq_of_not_mem hx
    have htr : Algebra.trace F E x = (basisOneOf hx).repr (x * x) 1 := trace_eq_of_not_mem hx
    have htr2 : Algebra.trace F E (x * x) = 2 * (basisOneOf hx).repr (x * x) 0 +
        (basisOneOf hx).repr (x * x) 1 * (basisOneOf hx).repr (x * x) 1 := by
      conv_lhs => rw [hsq]
      rw [map_add (f := _), trace_algebraMap_quadratic, ← Algebra.smul_def, map_smul, htr, smul_eq_mul]
    rw [conjLinear_apply, conjLinear_apply, htr2, htr]
    simp only [map_add (f := _), map_mul, map_ofNat]
    linear_combination (-2 : E) * hsq

theorem conjLinear_mul (x y : E) :
    conjLinear F E (x * y) = conjLinear F E x * conjLinear F E y := by
  by_cases hx : x ∈ Set.range (algebraMap F E)
  · obtain ⟨c, rfl⟩ := hx
    rw [conjLinear_algebraMap, ← Algebra.smul_def, ← Algebra.smul_def, map_smul]
  · have key : (conjLinear F E).comp (LinearMap.mulLeft F x) =
        (LinearMap.mulLeft F (conjLinear F E x)).comp (conjLinear F E) := by
      refine (basisOneOf hx).ext fun i => ?_
      fin_cases i
      · simp [basisOneOf_zero, conjLinear_one]
      · simp only [Fin.mk_one, basisOneOf_one, LinearMap.coe_comp, Function.comp_apply,
          LinearMap.mulLeft_apply]
        exact conjLinear_mul_self x
    exact LinearMap.congr_fun key y

theorem conjLinear_conjLinear (x : E) : conjLinear F E (conjLinear F E x) = x := by
  rw [conjLinear_apply, conjLinear_apply x, map_sub, trace_algebraMap_quadratic, map_sub,
    map_mul, map_ofNat]
  ring

variable (F E) in
noncomputable def conj : E ≃ₐ[F] E :=
  AlgEquiv.ofLinearEquiv
    (LinearEquiv.ofInvolutive (conjLinear F E) (fun x => conjLinear_conjLinear x))
    conjLinear_one conjLinear_mul

theorem conj_apply (x : E) : conj F E x = algebraMap F E (Algebra.trace F E x) - x := rfl

@[simp]
theorem conj_conj (x : E) : conj F E (conj F E x) = x := conjLinear_conjLinear x

theorem conj_algebraMap (c : F) : conj F E (algebraMap F E c) = algebraMap F E c :=
  conjLinear_algebraMap c

theorem add_conj (x : E) : x + conj F E x = algebraMap F E (Algebra.trace F E x) := by
  rw [conj_apply]; ring

theorem mul_conj (x : E) : x * conj F E x = algebraMap F E (Algebra.norm F x) := by
  by_cases hx : x ∈ Set.range (algebraMap F E)
  · obtain ⟨c, rfl⟩ := hx
    rw [conj_algebraMap, Algebra.norm_algebraMap, Algebra.IsQuadraticExtension.finrank_eq_two,
      map_pow, sq]
  · have hsq := sq_eq_of_not_mem hx
    rw [conj_apply, trace_eq_of_not_mem hx, norm_eq_of_not_mem hx, map_neg]
    linear_combination (-1 : E) * hsq

end GroundTheory.Automorphic
end

-- bundled from GroundTheory.AutomorphicForms.ReductionBlock
section
open Matrix

namespace GroundTheory.Automorphic

namespace Reduction

section Block

variable {R : Type*} [CommRing R] {m : ℕ}

def blockOne (M : Matrix (Fin m) (Fin m) R) : Matrix (Fin (m + 1)) (Fin (m + 1)) R :=
  Matrix.of fun i j => Fin.lastCases (Fin.lastCases 1 (fun _ => 0) j)
    (fun i' => Fin.lastCases 0 (fun j' => M i' j') j) i

@[simp] theorem blockOne_last_last (M : Matrix (Fin m) (Fin m) R) :
    blockOne M (Fin.last m) (Fin.last m) = 1 := by
  simp [blockOne]

@[simp] theorem blockOne_last_castSucc (M : Matrix (Fin m) (Fin m) R) (j : Fin m) :
    blockOne M (Fin.last m) (Fin.castSucc j) = 0 := by
  simp [blockOne]

@[simp] theorem blockOne_castSucc_last (M : Matrix (Fin m) (Fin m) R) (i : Fin m) :
    blockOne M (Fin.castSucc i) (Fin.last m) = 0 := by
  simp [blockOne]

@[simp] theorem blockOne_castSucc_castSucc (M : Matrix (Fin m) (Fin m) R) (i j : Fin m) :
    blockOne M (Fin.castSucc i) (Fin.castSucc j) = M i j := by
  simp [blockOne]

theorem blockOne_mul (M N : Matrix (Fin m) (Fin m) R) :
    blockOne (M * N) = blockOne M * blockOne N := by
  ext i j
  induction i using Fin.lastCases <;> induction j using Fin.lastCases <;>
    simp [Matrix.mul_apply, Fin.sum_univ_castSucc]

theorem blockOne_one : blockOne (1 : Matrix (Fin m) (Fin m) R) = 1 := by
  ext i j
  induction i using Fin.lastCases <;> induction j using Fin.lastCases <;>
    simp [Matrix.one_apply, Fin.castSucc_ne_last, (Fin.castSucc_ne_last _).symm]

theorem blockOne_map {S : Type*} [CommRing S] (f : R →+* S) (M : Matrix (Fin m) (Fin m) R) :
    (blockOne M).map f = blockOne (M.map f) := by
  ext i j
  induction i using Fin.lastCases <;> induction j using Fin.lastCases <;> simp

def blockOneMonoidHom : Matrix (Fin m) (Fin m) R →* Matrix (Fin (m + 1)) (Fin (m + 1)) R where
  toFun := blockOne
  map_one' := blockOne_one
  map_mul' := blockOne_mul

def blockOneHom : GL (Fin m) R →* GL (Fin (m + 1)) R :=
  Units.map blockOneMonoidHom

@[simp] theorem coe_blockOneHom (γ : GL (Fin m) R) :
    ((blockOneHom γ : GL (Fin (m + 1)) R) : Matrix (Fin (m + 1)) (Fin (m + 1)) R) =
      blockOne (γ : Matrix (Fin m) (Fin m) R) := rfl

theorem single_last_vecMul_blockOne (M : Matrix (Fin m) (Fin m) R) :
    Pi.single (Fin.last m) 1 ᵥ* blockOne M = Pi.single (Fin.last m) 1 := by
  ext j
  induction j using Fin.lastCases <;>
    simp [vecMul, dotProduct, Pi.single_apply, Fin.castSucc_ne_last]

theorem vecMul_blockOne_castSucc (y : Fin (m + 1) → R) (M : Matrix (Fin m) (Fin m) R) (j : Fin m) :
    (y ᵥ* blockOne M) (Fin.castSucc j) = (Fin.init y ᵥ* M) j := by
  simp [vecMul, dotProduct, Fin.sum_univ_castSucc, Fin.init]

theorem vecMul_blockOne_last (y : Fin (m + 1) → R) (M : Matrix (Fin m) (Fin m) R) :
    (y ᵥ* blockOne M) (Fin.last m) = y (Fin.last m) := by
  simp [vecMul, dotProduct, Fin.sum_univ_castSucc]

end Block

section Row

variable {F : Type*} [Field F] {m : ℕ}

def rowMatrix (x : Fin (m + 1) → F) : Matrix (Fin (m + 1)) (Fin (m + 1)) F :=
  Matrix.of fun i j => if i = Fin.last m then x j else if i = j then 1 else 0

theorem det_rowMatrix (x : Fin (m + 1) → F) : (rowMatrix x).det = x (Fin.last m) := by
  rw [det_of_isLowerTriangular]
  · rw [Fin.prod_univ_castSucc]
    simp [rowMatrix, Fin.castSucc_ne_last]
  · intro i j hij
    simp only [rowMatrix, of_apply]
    have hij' : i < j := hij
    have hi : i ≠ Fin.last m := fun h => by
      rw [h] at hij'
      exact absurd hij' (not_lt.2 (Fin.le_last j))
    rw [if_neg hi, if_neg hij'.ne]

theorem single_last_vecMul_rowMatrix (x : Fin (m + 1) → F) :
    Pi.single (Fin.last m) 1 ᵥ* rowMatrix x = x := by
  ext j
  rw [vecMul, dotProduct, Finset.sum_eq_single (Fin.last m)]
  · simp [rowMatrix]
  · intro b _ hb
    simp [hb]
  · simp

theorem exists_lastRow_eq {x : Fin (m + 1) → F} (hx : x ≠ 0) :
    ∃ γ : GL (Fin (m + 1)) F,
      Pi.single (Fin.last m) 1 ᵥ* (γ : Matrix (Fin (m + 1)) (Fin (m + 1)) F) = x := by
  classical

  obtain ⟨j, hj⟩ : ∃ j, x j ≠ 0 := by
    by_contra h
    exact hx (funext fun j => not_not.1 fun hj => h ⟨j, hj⟩)
  by_cases hl : x (Fin.last m) ≠ 0
  · refine ⟨GeneralLinearGroup.mkOfDetNeZero (rowMatrix x) (by rw [det_rowMatrix]; exact hl), ?_⟩
    exact single_last_vecMul_rowMatrix x
  · rw [not_not] at hl
    have hjl : j ≠ Fin.last m := fun h => hj (h ▸ hl)
    set τ := transvection j (Fin.last m) (1 : F) with hτ
    have hτdet : τ.det = 1 := det_transvection_of_ne j (Fin.last m) hjl 1
    set x' := x ᵥ* τ with hx'
    have hx'l : x' (Fin.last m) = x j := by
      simp [hx', hτ, transvection, vecMul_add, hl, Matrix.vecMul, dotProduct,
        Matrix.single_apply]
    have hx'l0 : x' (Fin.last m) ≠ 0 := by rw [hx'l]; exact hj
    set τu : GL (Fin (m + 1)) F :=
      GeneralLinearGroup.mkOfDetNeZero τ (by rw [hτdet]; exact one_ne_zero) with hτu
    refine ⟨GeneralLinearGroup.mkOfDetNeZero (rowMatrix x') (by rw [det_rowMatrix]; exact hx'l0) *
      τu⁻¹, ?_⟩
    rw [Units.val_mul, ← vecMul_vecMul]
    change (Pi.single (Fin.last m) 1 ᵥ* rowMatrix x') ᵥ* _ = x
    have hτu' : (τu : Matrix (Fin (m + 1)) (Fin (m + 1)) F) = τ := rfl
    rw [single_last_vecMul_rowMatrix, hx', ← hτu', vecMul_vecMul, ← Units.val_mul, mul_inv_cancel,
      Units.val_one, vecMul_one]

end Row

end Reduction

end GroundTheory.Automorphic
end

