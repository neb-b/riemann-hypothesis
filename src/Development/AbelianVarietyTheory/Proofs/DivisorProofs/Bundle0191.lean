module

public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0002
public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.HilbertNinetyQuotientHomEqIff
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.OmegaFactorization
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0169
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0138
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0035
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0133

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsBlockParabolicSubgroupLeviProjection
section
open Polynomial GlobalTheory.CuspGL GlobalTheory.BI GlobalTheory.Shin SemidirectProduct
open scoped Classical

noncomputable section

namespace GlobalTheory.Shin.BlockPar

variable {F : Type} [Field F] {a b : ℕ}

def sm (M : Matrix (Fin (a + b)) (Fin (a + b)) F) : Matrix (Fin a ⊕ Fin b) (Fin a ⊕ Fin b) F :=
  M.submatrix finSumFinEquiv finSumFinEquiv

theorem tl_eq (M : Matrix (Fin (a + b)) (Fin (a + b)) F) : tl a M = (sm M).toBlocks₁₁ := by
  ext i j
  have hi : (i : ℕ) < a + b := by omega
  have hj : (j : ℕ) < a + b := by omega
  simp only [tl, ent, hi, hj, and_self, dif_pos, sm, Matrix.toBlocks₁₁, Matrix.of_apply,
    Matrix.submatrix_apply, finSumFinEquiv_apply_left]
  rfl

theorem br_eq (M : Matrix (Fin (a + b)) (Fin (a + b)) F) : br a b M = (sm M).toBlocks₂₂ := by
  ext i j
  have hi : a + (i : ℕ) < a + b := by omega
  have hj : a + (j : ℕ) < a + b := by omega
  simp only [br, ent, hi, hj, and_self, dif_pos, sm, Matrix.toBlocks₂₂, Matrix.of_apply,
    Matrix.submatrix_apply, finSumFinEquiv_apply_right]
  rfl

theorem inPar_iff (x : GL (Fin (a + b)) F) :
    InPar a x ↔ (sm (x : Matrix (Fin (a + b)) (Fin (a + b)) F)).toBlocks₂₁ = 0 := by
  constructor
  · intro h
    ext i j
    simp only [sm, Matrix.toBlocks₂₁, Matrix.of_apply, Matrix.submatrix_apply, finSumFinEquiv_apply_left,
      finSumFinEquiv_apply_right, Matrix.zero_apply]
    apply h <;> simp
  · intro h i j hj hi
    obtain ⟨i', rfl⟩ : ∃ i' : Fin b, Fin.natAdd a i' = i :=
      ⟨⟨i - a, by omega⟩, Fin.ext (by simp; omega)⟩
    obtain ⟨j', rfl⟩ : ∃ j' : Fin a, Fin.castAdd b j' = j := ⟨⟨j, hj⟩, rfl⟩
    have := congrFun (congrFun h i') j'
    simpa [sm, Matrix.toBlocks₂₁] using this

theorem sm_eq {M : Matrix (Fin (a + b)) (Fin (a + b)) F} (h : (sm M).toBlocks₂₁ = 0) :
    sm M = Matrix.fromBlocks (tl a M) (sm M).toBlocks₁₂ 0 (br a b M) := by
  rw [tl_eq, br_eq, ← h, Matrix.fromBlocks_toBlocks]

theorem sm_mul (M N : Matrix (Fin (a + b)) (Fin (a + b)) F) : sm (M * N) = sm M * sm N :=
  (Matrix.submatrix_mul_equiv M N _ _ _).symm

theorem mul_blocks {M N : Matrix (Fin (a + b)) (Fin (a + b)) F} (hM : (sm M).toBlocks₂₁ = 0)
    (hN : (sm N).toBlocks₂₁ = 0) :
    (sm (M * N)).toBlocks₂₁ = 0 ∧ tl a (M * N) = tl a M * tl a N ∧ br a b (M * N) = br a b M * br a b N := by
  have e : sm (M * N) = Matrix.fromBlocks (tl a M * tl a N)
      (tl a M * (sm N).toBlocks₁₂ + (sm M).toBlocks₁₂ * br a b N) 0 (br a b M * br a b N) := by
    rw [sm_mul, sm_eq hM, sm_eq hN, Matrix.fromBlocks_multiply]
    simp
  refine ⟨by rw [e, Matrix.toBlocks_fromBlocks₂₁], ?_, ?_⟩
  · rw [tl_eq (M * N), e, Matrix.toBlocks_fromBlocks₁₁]
  · rw [br_eq (M * N), e, Matrix.toBlocks_fromBlocks₂₂]

theorem det_eq {M : Matrix (Fin (a + b)) (Fin (a + b)) F} (h : (sm M).toBlocks₂₁ = 0) :
    M.det = (tl a M).det * (br a b M).det := by
  rw [← Matrix.det_submatrix_equiv_self finSumFinEquiv M]
  change (sm M).det = _
  rw [sm_eq h, Matrix.det_fromBlocks_zero₂₁]

theorem charpoly_eq {M : Matrix (Fin (a + b)) (Fin (a + b)) F} (h : (sm M).toBlocks₂₁ = 0) :
    M.charpoly = (tl a M).charpoly * (br a b M).charpoly := by
  rw [← Matrix.charpoly_reindex finSumFinEquiv.symm M]
  have : Matrix.reindex finSumFinEquiv.symm finSumFinEquiv.symm M = sm M := by
    rw [Matrix.reindex_apply, Equiv.symm_symm]; rfl
  rw [this, sm_eq h, Matrix.charpoly_fromBlocks_zero₂₁]

theorem toG_val {m : ℕ} {M : Matrix (Fin m) (Fin m) F} (h : IsUnit M) : ((toG M : GL (Fin m) F) : Matrix (Fin m) (Fin m) F) = M := by
  unfold toG; rw [dif_pos h]; rfl

theorem units_of_par (x : GL (Fin (a + b)) F) (h : InPar a x) :
    IsUnit (tl a (x : Matrix (Fin (a + b)) (Fin (a + b)) F)) ∧ IsUnit (br a b (x : Matrix (Fin (a + b)) (Fin (a + b)) F)) := by
  have hu : IsUnit (x : Matrix (Fin (a + b)) (Fin (a + b)) F).det :=
    (Matrix.isUnit_iff_isUnit_det _).1 x.isUnit
  rw [det_eq ((inPar_iff x).1 h)] at hu
  exact ⟨(Matrix.isUnit_iff_isUnit_det _).2 (isUnit_of_mul_isUnit_left hu),
    (Matrix.isUnit_iff_isUnit_det _).2 (isUnit_of_mul_isUnit_right hu)⟩

theorem inPar_inv (x : GL (Fin (a + b)) F) (h : InPar a x) : InPar a x⁻¹ := by
  let β : Fin (a + b) → Bool := fun i => decide (a ≤ (i : ℕ))
  have hb : (x : Matrix (Fin (a + b)) (Fin (a + b)) F).BlockTriangular β := by
    intro i j hij
    rw [Bool.lt_iff] at hij
    simp only [β, decide_eq_false_iff_not, decide_eq_true_eq, not_le] at hij
    exact h i j hij.1 hij.2
  haveI := x.invertible
  have hb' := Matrix.blockTriangular_inv_of_blockTriangular hb
  intro i j hj hi
  rw [Matrix.coe_units_inv]
  exact hb' (by rw [Bool.lt_iff]; simp [β]; omega)

theorem block_par : ∀ (F : Type) [Field F] (a b n : ℕ), n = a + b → ∃ (H : Subgroup (GL (Fin n) F)) (π : H →* GL (Fin a) F × GL (Fin b) F), (∀ x, x ∈ H ↔ InPar a x) ∧ Function.Surjective π ∧ (∀ p : H, π p = (tlG a p.1, brG a b p.1)) ∧ (∀ p : H, ((π p).1 : Matrix (Fin a) (Fin a) F) = tl a (p.1 : Matrix (Fin n) (Fin n) F) ∧ ((π p).2 : Matrix (Fin b) (Fin b) F) = br a b (p.1 : Matrix (Fin n) (Fin n) F)) ∧ ∀ p : H, Matrix.charpoly (p.1 : Matrix (Fin n) (Fin n) F) = Matrix.charpoly ((π p).1 : Matrix (Fin a) (Fin a) F) * Matrix.charpoly ((π p).2 : Matrix (Fin b) (Fin b) F) := by
  intro F _ a b n hn
  subst hn
  let H : Subgroup (GL (Fin (a + b)) F) :=
    { carrier := {x | InPar a x}
      one_mem' := by
        intro i j hj hi
        rw [Units.val_one, Matrix.one_apply_ne]
        intro e; subst e; omega
      mul_mem' := by
        intro x y hx hy
        exact (inPar_iff _).2 (mul_blocks ((inPar_iff x).1 hx) ((inPar_iff y).1 hy)).1
      inv_mem' := fun {x} hx => inPar_inv x hx }
  have hH : ∀ x, x ∈ H ↔ InPar a x := fun _ => Iff.rfl
  have hpar : ∀ p : H, (sm ((p.1 : GL (Fin (a + b)) F) : Matrix (Fin (a + b)) (Fin (a + b)) F)).toBlocks₂₁ = 0 :=
    fun p => (inPar_iff _).1 p.2
  have hval : ∀ p : H, ((tlG a p.1 : GL (Fin a) F) : Matrix (Fin a) (Fin a) F) = tl a (p.1 : Matrix (Fin (a + b)) (Fin (a + b)) F) ∧
      ((brG a b p.1 : GL (Fin b) F) : Matrix (Fin b) (Fin b) F) = br a b (p.1 : Matrix (Fin (a + b)) (Fin (a + b)) F) :=
    fun p => ⟨toG_val (units_of_par _ p.2).1, toG_val (units_of_par _ p.2).2⟩
  let π : H →* GL (Fin a) F × GL (Fin b) F :=
    MonoidHom.mk' (fun p => (tlG a p.1, brG a b p.1)) (by
      intro p q
      have hm := mul_blocks (hpar p) (hpar q)
      refine Prod.ext (Units.ext ?_) (Units.ext ?_)
      · change ((tlG a (p * q).1 : GL (Fin a) F) : Matrix (Fin a) (Fin a) F) = ((tlG a p.1 : GL (Fin a) F) : Matrix (Fin a) (Fin a) F) * ((tlG a q.1 : GL (Fin a) F) : Matrix (Fin a) (Fin a) F)
        rw [(hval (p * q)).1, (hval p).1, (hval q).1]
        exact hm.2.1
      · change ((brG a b (p * q).1 : GL (Fin b) F) : Matrix (Fin b) (Fin b) F) = ((brG a b p.1 : GL (Fin b) F) : Matrix (Fin b) (Fin b) F) * ((brG a b q.1 : GL (Fin b) F) : Matrix (Fin b) (Fin b) F)
        rw [(hval (p * q)).2, (hval p).2, (hval q).2]
        exact hm.2.2)
  have hπ : ∀ p : H, π p = (tlG a p.1, brG a b p.1) := fun _ => rfl
  refine ⟨H, π, hH, ?_, hπ, fun p => hval p, fun p => ?_⟩
  · rintro ⟨u, v⟩
    let M : Matrix (Fin (a + b)) (Fin (a + b)) F :=
      (Matrix.fromBlocks (u : Matrix (Fin a) (Fin a) F) 0 0 (v : Matrix (Fin b) (Fin b) F)).submatrix
        finSumFinEquiv.symm finSumFinEquiv.symm
    have hsm : sm M = Matrix.fromBlocks (u : Matrix (Fin a) (Fin a) F) 0 0 (v : Matrix (Fin b) (Fin b) F) := by
      simp only [sm, M, Matrix.submatrix_submatrix, Equiv.symm_comp_self, Matrix.submatrix_id_id]
    have h21 : (sm M).toBlocks₂₁ = 0 := by rw [hsm, Matrix.toBlocks_fromBlocks₂₁]
    have htl : tl a M = u := by rw [tl_eq, hsm, Matrix.toBlocks_fromBlocks₁₁]
    have hbr : br a b M = v := by rw [br_eq, hsm, Matrix.toBlocks_fromBlocks₂₂]
    have hu : IsUnit M := by
      rw [Matrix.isUnit_iff_isUnit_det, det_eq h21, htl, hbr]
      exact ((Matrix.isUnit_iff_isUnit_det _).1 u.isUnit).mul ((Matrix.isUnit_iff_isUnit_det _).1 v.isUnit)
    have hmem : hu.unit ∈ H := by
      rw [hH, inPar_iff]
      exact h21
    refine ⟨⟨hu.unit, hmem⟩, ?_⟩
    have hv := hval ⟨hu.unit, hmem⟩
    simp only [IsUnit.unit_spec] at hv
    rw [hπ]
    refine Prod.ext (Units.ext ?_) (Units.ext ?_)
    · exact hv.1.trans htl
    · exact hv.2.trans hbr
  · rw [hπ, (hval p).1, (hval p).2]
    exact charpoly_eq (hpar p)

end GlobalTheory.Shin.BlockPar
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCompactOpenAddSubgroup
section
open MeasureTheory Filter Topology

namespace GlobalTheory.WeilM.HaarUniq

variable {V : Type} [AddCommGroup V] [TopologicalSpace V]


open MeasureTheory Filter Topology in
variable {V : Type} [AddCommGroup V] [TopologicalSpace V] in
theorem _root_.GlobalTheory.WeilM.HaarUniq.exists_compact_openAddSubgroup [NonarchimedeanAddGroup V]
    [LocallyCompactSpace V] :
    ∃ K : OpenAddSubgroup V, IsCompact (K : Set V) := by
  obtain ⟨C, hC, hC0⟩ := exists_compact_mem_nhds (0 : V)
  obtain ⟨K, hK⟩ := NonarchimedeanAddGroup.is_nonarchimedean C hC0
  exact ⟨K, hC.of_isClosed_subset K.isClosed hK⟩


open MeasureTheory Filter Topology in
variable {V : Type} [AddCommGroup V] [TopologicalSpace V] in
theorem _root_.GlobalTheory.WeilM.HaarUniq.indicator_mem [IsTopologicalAddGroup V] [T2Space V]
    (K : OpenAddSubgroup V) (hK : IsCompact (K : Set V)) :
    Set.indicator (K : Set V) (fun _ => (1 : ℂ)) ∈ _root_.GlobalTheory.WeilM.SB V := by
  simp only [_root_.GlobalTheory.WeilM.SB, Submodule.mem_mk,
    AddSubmonoid.mem_mk, AddSubsemigroup.mem_mk, Set.mem_setOf_eq]
  refine ⟨?_, HasCompactSupport.intro hK fun x hx => Set.indicator_of_notMem hx _⟩
  refine (IsLocallyConstant.iff_exists_open _).2 fun x => ?_
  by_cases hx : x ∈ (K : Set V)
  · exact ⟨K, K.isOpen, hx, fun y hy => by simp [Set.indicator_of_mem hy, Set.indicator_of_mem hx]⟩
  · exact ⟨(K : Set V)ᶜ, K.isClosed.isOpen_compl, hx, fun y hy => by
      simp [Set.indicator_of_notMem hy, Set.indicator_of_notMem hx]⟩


open MeasureTheory Filter Topology in
variable {V : Type} [AddCommGroup V] [TopologicalSpace V] in
theorem _root_.GlobalTheory.WeilM.HaarUniq.exists_invariant [NonarchimedeanAddGroup V] {φ : V → ℂ}
    (hφ : φ ∈ _root_.GlobalTheory.WeilM.SB V) :
    ∃ K : OpenAddSubgroup V, ∀ k ∈ K, ∀ x, φ (x + k) = φ x := by
  have hφ' : IsLocallyConstant φ ∧ HasCompactSupport φ := by
    simpa [_root_.GlobalTheory.WeilM.SB] using hφ
  obtain ⟨hlc, hcs⟩ := hφ'
  have hnhds : ∀ x : V, (fun w => x + w) ⁻¹' {y | φ y = φ x} ∈ 𝓝 (0 : V) := by
    intro x
    refine (continuous_const_add x).continuousAt.preimage_mem_nhds ?_
    rw [add_zero]
    exact (hlc.isOpen_fiber (φ x)).mem_nhds rfl
  choose W hW using fun x => NonarchimedeanAddGroup.is_nonarchimedean _ (hnhds x)
  have hval : ∀ i y, y - i ∈ W i → φ y = φ i := by
    intro i y hy
    have := hW i hy
    simpa using this
  obtain ⟨t, ht⟩ := hcs.isCompact.elim_finite_subcover (fun i => (fun y => y - i) ⁻¹' (W i))
    (fun i => (W i).isOpen.preimage (continuous_sub_right i))
    (fun y _ => Set.mem_iUnion.2 ⟨y, by simpa using (W y).zero_mem⟩)
  refine ⟨t.inf W, fun k hk x => ?_⟩
  have hkW : ∀ i ∈ t, k ∈ W i := fun i hi => (Finset.inf_le hi : t.inf W ≤ W i) hk
  by_cases hx : x ∈ tsupport φ
  · obtain ⟨i, hi, hxi⟩ := Set.mem_iUnion₂.1 (ht hx)
    have hxi' : x - i ∈ W i := hxi
    have hxk : x + k - i ∈ W i := by
      have := (W i).add_mem hxi' (hkW i hi)
      rwa [sub_add_eq_add_sub] at this
    rw [hval i _ hxk, hval i _ hxi']
  by_cases hxk : x + k ∈ tsupport φ
  · obtain ⟨i, hi, hxi⟩ := Set.mem_iUnion₂.1 (ht hxk)
    have hxi' : x + k - i ∈ W i := hxi
    have hx' : x - i ∈ W i := by
      have := (W i).sub_mem hxi' (hkW i hi)
      rwa [sub_right_comm, add_sub_cancel_right] at this
    rw [hval i _ hxi', hval i _ hx']
  rw [image_eq_zero_of_notMem_tsupport hx, image_eq_zero_of_notMem_tsupport hxk]


open MeasureTheory Filter Topology in
variable {V : Type} [AddCommGroup V] [TopologicalSpace V] in
theorem _root_.GlobalTheory.WeilM.HaarUniq.exists_decomp [IsTopologicalAddGroup V] (K : OpenAddSubgroup V)
    {φ : V → ℂ} (hc : HasCompactSupport φ) (hinv : ∀ k ∈ K, ∀ x, φ (x + k) = φ x) :
    ∃ S : Finset (V ⧸ K.toAddSubgroup),
      φ = ∑ q ∈ S, φ q.out • (fun x => Set.indicator (K : Set V) (fun _ => (1 : ℂ)) (x + -q.out)) := by
  classical
  obtain ⟨t, ht⟩ := hc.isCompact.elim_finite_subcover (fun p : V => (fun y => -p + y) ⁻¹' (K : Set V))
    (fun p => K.isOpen.preimage (continuous_const_add (-p)))
    (fun y _ => Set.mem_iUnion.2 ⟨y, by simpa using K.zero_mem⟩)
  refine ⟨t.image (QuotientAddGroup.mk : V → V ⧸ K.toAddSubgroup), ?_⟩
  funext x
  have hmem : ∀ q : V ⧸ K.toAddSubgroup,
      (x + -q.out ∈ (K : Set V)) ↔ q = (QuotientAddGroup.mk x : V ⧸ K.toAddSubgroup) := by
    intro q
    conv_rhs => rw [← QuotientAddGroup.out_eq' q]
    rw [QuotientAddGroup.eq, add_comm]
    simp
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Set.indicator_apply, hmem,
    mul_ite, mul_one, mul_zero]
  rw [Finset.sum_ite_eq']
  split_ifs with hS
  · have h := QuotientAddGroup.out_eq' (QuotientAddGroup.mk x : V ⧸ K.toAddSubgroup)
    rw [QuotientAddGroup.eq] at h
    have := hinv _ h ((QuotientAddGroup.mk x : V ⧸ K.toAddSubgroup).out)
    rw [add_neg_cancel_left] at this
    exact this
  · apply image_eq_zero_of_notMem_tsupport
    intro hx
    apply hS
    obtain ⟨p, hp, hxp⟩ := Set.mem_iUnion₂.1 (ht hx)
    refine Finset.mem_image.2 ⟨p, hp, ?_⟩
    rw [QuotientAddGroup.eq]
    simpa using hxp

open MeasureTheory Filter Topology in
variable {V : Type} [AddCommGroup V] [TopologicalSpace V] in
private theorem exists_coeff_form_and_integral [IsTopologicalAddGroup V] [T2Space V]
    [MeasurableSpace V] [BorelSpace V] (μ : Measure V) [μ.IsAddHaarMeasure]
    (m : (V → ℂ) →ₗ[ℂ] ℂ)
    (hm : ∀ φ ∈ _root_.GlobalTheory.WeilM.SB V, ∀ a : V,
      m (fun x => φ (x + a)) = m φ)
    (H : OpenAddSubgroup V) (hH : IsCompact (H : Set V)) {φ : V → ℂ} (hc : HasCompactSupport φ)
    (hinv : ∀ k ∈ H, ∀ x, φ (x + k) = φ x) :
    ∃ A : ℂ, m φ = A * m (Set.indicator (H : Set V) (fun _ => (1 : ℂ))) ∧
      ∫ x, φ x ∂μ = A * (μ.real (H : Set V) : ℂ) := by
  obtain ⟨S, hS⟩ := _root_.GlobalTheory.WeilM.HaarUniq.exists_decomp H hc hinv
  have hmemH := _root_.GlobalTheory.WeilM.HaarUniq.indicator_mem H hH
  have hint : Integrable (Set.indicator (H : Set V) (fun _ => (1 : ℂ))) μ :=
    (integrable_indicator_iff H.isOpen.measurableSet).2 (integrableOn_const hH.measure_lt_top.ne)
  refine ⟨∑ q ∈ S, φ q.out, ?_, ?_⟩
  · calc m φ = m (∑ q ∈ S, φ q.out •
          (fun x => Set.indicator (H : Set V) (fun _ => (1 : ℂ)) (x + -q.out))) := congrArg m hS
      _ = ∑ q ∈ S, φ q.out * m (Set.indicator (H : Set V) (fun _ => (1 : ℂ))) := by
          set_option synthInstance.maxHeartbeats 100000 in
            rw [map_sum]
          refine Finset.sum_congr rfl fun q _ => ?_
          rw [map_smul, smul_eq_mul, hm _ hmemH]
      _ = _ := by rw [Finset.sum_mul]
  · calc ∫ x, φ x ∂μ = ∫ x, (∑ q ∈ S, φ q.out •
          (fun x => Set.indicator (H : Set V) (fun _ => (1 : ℂ)) (x + -q.out))) x ∂μ := by
            rw [← hS]
      _ = ∑ q ∈ S, φ q.out * (μ.real (H : Set V) : ℂ) := by
          simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
          rw [MeasureTheory.integral_finsetSum]
          · refine Finset.sum_congr rfl fun q _ => ?_
            rw [integral_const_mul,
              integral_add_right_eq_self (fun x => Set.indicator (H : Set V) (fun _ => (1 : ℂ)) x),
              integral_indicator_const _ H.isOpen.measurableSet]
            simp
          · intro q _
            exact (hint.comp_add_right _).const_mul _
      _ = _ := by rw [Finset.sum_mul]


open MeasureTheory Filter Topology in
variable {V : Type} [AddCommGroup V] [TopologicalSpace V] in
theorem _root_.GlobalTheory.WeilM.HaarUniq.exists_eq_mul_integral : ∀ (V : Type) [AddCommGroup V]
    [TopologicalSpace V] [NonarchimedeanAddGroup V]
    [LocallyCompactSpace V] [T2Space V] [MeasurableSpace V] [BorelSpace V] (μ : Measure V)
    [μ.IsAddHaarMeasure]
    (m : (V → ℂ) →ₗ[ℂ] ℂ), (∀ φ ∈ _root_.GlobalTheory.WeilM.SB V, ∀ a : V,
      m (fun x => φ (x + a)) = m φ) →
    ∃ c : ℂ, ∀ φ ∈ _root_.GlobalTheory.WeilM.SB V, m φ = c * ∫ x, φ x ∂μ := by
  intro V _ _ _ _ _ _ _ μ _ m hm
  obtain ⟨K₀, hK₀⟩ := _root_.GlobalTheory.WeilM.HaarUniq.exists_compact_openAddSubgroup (V := V)
  have hpos : ∀ H : OpenAddSubgroup V, IsCompact (H : Set V) → μ.real (H : Set V) ≠ 0 := by
    intro H hH
    rw [measureReal_def, ENNReal.toReal_ne_zero]
    exact ⟨(H.isOpen.measure_pos μ ⟨0, H.zero_mem⟩).ne', hH.measure_lt_top.ne⟩
  refine ⟨m (Set.indicator (K₀ : Set V) (fun _ => (1 : ℂ))) / (μ.real (K₀ : Set V) : ℂ),
    fun φ hφ => ?_⟩
  have hφ' : IsLocallyConstant φ ∧ HasCompactSupport φ := by
    simpa [_root_.GlobalTheory.WeilM.SB] using hφ
  obtain ⟨K₁, hK₁⟩ := _root_.GlobalTheory.WeilM.HaarUniq.exists_invariant hφ
  set H : OpenAddSubgroup V := K₀ ⊓ K₁
  have hH : IsCompact (H : Set V) := by
    refine hK₀.of_isClosed_subset H.isClosed ?_
    rw [OpenAddSubgroup.coe_inf]
    exact Set.inter_subset_left
  have hHK₁ : ∀ k ∈ H, k ∈ K₁ := fun k hk => by
    have : k ∈ (H : Set V) := hk
    rw [OpenAddSubgroup.coe_inf] at this
    exact this.2
  have hHK₀ : ∀ k ∈ H, k ∈ K₀ := fun k hk => by
    have : k ∈ (H : Set V) := hk
    rw [OpenAddSubgroup.coe_inf] at this
    exact this.1
  obtain ⟨A, hA₁, hA₂⟩ := exists_coeff_form_and_integral μ m hm H hH hφ'.2
    (fun k hk x => hK₁ k (hHK₁ k hk) x)
  obtain ⟨B, hB₁, hB₂⟩ := exists_coeff_form_and_integral μ m hm H hH
    (φ := Set.indicator (K₀ : Set V) (fun _ => (1 : ℂ)))
    (HasCompactSupport.intro hK₀ fun x hx => Set.indicator_of_notMem hx _)
    (fun k hk x => by
      by_cases hx : x ∈ K₀ <;>
        simp [Set.indicator_apply, hx, add_mem_cancel_right (hHK₀ k hk)])
  rw [integral_indicator_const _ K₀.isOpen.measurableSet, Complex.real_smul, mul_one] at hB₂
  have hH0 : (μ.real (H : Set V) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 (hpos H hH)
  have hK0 : (μ.real (K₀ : Set V) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 (hpos K₀ hK₀)
  rw [hA₁, hA₂, hB₁, hB₂]
  have hB0 : B ≠ 0 := by
    rintro rfl
    apply hK0
    rw [hB₂, zero_mul]
  field_simp

end GlobalTheory.WeilM.HaarUniq
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsEquivFourierClassesPosConeSummand
section
open NumberField
open scoped nonZeroDivisors

noncomputable section

namespace GlobalTheory.Div.QFibre

open GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization GlobalTheory.SlopeTestRemainingChoices.EisFibre

variable {F : Type} [Field F] [NumberField F]

theorem unit_mul_mem (𝔞 : Frac F) (ε : (𝓞 F)ˣ) {x : F} (hx : x ∈ (𝔞 : FractionalIdeal (𝓞 F)⁰ F)) :
    ((ε : 𝓞 F) : F) * x ∈ (𝔞 : FractionalIdeal (𝓞 F)⁰ F) := by
  have := Submodule.smul_mem (𝔞 : FractionalIdeal (𝓞 F)⁰ F).coeToSubmodule (ε : 𝓞 F) hx
  rw [Algebra.smul_def] at this
  exact this

def toQ (𝔞 𝔟 : Frac F) (x : Σ β : NzCls 𝔟, posCone 𝔞 (rep β)) : Quotient (qRel 𝔞 𝔟) :=
  Quotient.mk _ ⟨(x.2.1, rep x.1), x.2.2.1, rep_mem x.1, x.2.2.2⟩

theorem toQ_injective (𝔞 𝔟 : Frac F) : Function.Injective (toQ 𝔞 𝔟) := by
  rintro ⟨β, ν, hν⟩ ⟨β', ν', hν'⟩ h
  obtain ⟨ε, h1, h2⟩ := Quotient.exact h
  simp only at h1 h2
  have hβ : β = β' := by
    rw [← Quotient.out_eq β, ← Quotient.out_eq β']
    exact Quotient.sound ⟨ε, h2⟩
  subst hβ
  have hε : ((ε : 𝓞 F) : F) = 1 := by
    have h0 := rep_ne_zero β
    have : (((ε : 𝓞 F) : F) - 1) * rep β = 0 := by unfold rep at h2 ⊢; rw [sub_mul, ← h2]; ring
    exact sub_eq_zero.1 ((mul_eq_zero.1 this).resolve_right h0)
  have hε' : (((ε⁻¹ : (𝓞 F)ˣ) : 𝓞 F) : F) = 1 := by
    have := unit_inv_mul ε; rw [hε, mul_one] at this; exact this
  rw [hε', one_mul] at h1
  have : (⟨ν, hν⟩ : posCone 𝔞 (rep β)) = ⟨ν', hν'⟩ := Subtype.ext h1.symm
  rw [this]

theorem exists_emb [IsTotallyReal F] : Nonempty (Emb F) := by
  obtain ⟨w⟩ := (inferInstance : Nonempty (InfinitePlace F))
  exact ⟨(IsTotallyReal.complexEmbedding_isReal w.embedding).embedding⟩

theorem toQ_surjective [IsTotallyReal F] (𝔞 𝔟 : Frac F) : Function.Surjective (toQ 𝔞 𝔟) := by
  intro c
  induction c using Quotient.ind with
  | _ p =>
  obtain ⟨⟨ν, b⟩, hν, hb, hpos⟩ := p
  have hb0 : b ≠ 0 := by
    rintro rfl
    obtain ⟨τ⟩ := exists_emb (F := F)
    have := hpos τ; simp at this
  let β : NzCls 𝔟 := Quotient.mk _ ⟨b, hb, hb0⟩
  obtain ⟨ε, hε⟩ : (unitRel 𝔟).r (Quotient.out β) ⟨b, hb, hb0⟩ := Quotient.exact (Quotient.out_eq β)
  have h4 := unit_inv_mul ε
  have hrep : rep β = (((ε⁻¹ : (𝓞 F)ˣ) : 𝓞 F) : F) * b := by
    unfold rep; simp only at hε; rw [hε, ← mul_assoc, h4, one_mul]
  have hprod : ((ε : 𝓞 F) : F) * ν * rep β = ν * b := by
    rw [hrep]; linear_combination (ν * b) * h4
  refine ⟨⟨β, ((ε : 𝓞 F) : F) * ν, unit_mul_mem 𝔞 ε hν, fun τ => by rw [hprod]; exact hpos τ⟩, ?_⟩
  apply Quotient.sound
  refine ⟨ε, ?_, ?_⟩
  · show ν = _ * (((ε : 𝓞 F) : F) * ν)
    rw [← mul_assoc, h4, one_mul]
  · show b = ((ε : 𝓞 F) : F) * rep β
    rw [hrep, ← mul_assoc, mul_comm ((ε : 𝓞 F) : F), h4, one_mul]

theorem qFibres : ∀ (F : Type) [Field F] [NumberField F] [NumberField.IsTotallyReal F] (𝔞 𝔟 : GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.Frac F),
    ∃ e : (Σ β : GlobalTheory.SlopeTestRemainingChoices.EisFibre.NzCls 𝔟, GlobalTheory.SlopeTestRemainingChoices.EisFibre.posCone 𝔞 (GlobalTheory.SlopeTestRemainingChoices.EisFibre.rep β)) ≃ Quotient (GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.qRel 𝔞 𝔟),
      ∀ (k : ℕ) (z : GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.Emb F → ℂ) (x : Σ β : GlobalTheory.SlopeTestRemainingChoices.EisFibre.NzCls 𝔟, GlobalTheory.SlopeTestRemainingChoices.EisFibre.posCone 𝔞 (GlobalTheory.SlopeTestRemainingChoices.EisFibre.rep β)),
        GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.qClass 𝔞 𝔟 k z (e x) = GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.qTerm 𝔞 k z (x.2.1, GlobalTheory.SlopeTestRemainingChoices.EisFibre.rep x.1) := by
  intro F _ _ _ 𝔞 𝔟
  refine ⟨Equiv.ofBijective (toQ 𝔞 𝔟) ⟨toQ_injective 𝔞 𝔟, toQ_surjective 𝔞 𝔟⟩, fun k z x => ?_⟩
  exact qClass_mk 𝔞 𝔟 k z _

end GlobalTheory.Div.QFibre
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFinsetMemTensorPowerFirstFactorAdjoinFinseStatement
section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_finset_mem_tensorPowerFirstFactorAdjoinFinset : ∀ (R A : Type) [CommRing R] [CommRing A] [Algebra R A] (k : ℕ) (x : PiTensorProduct R (fun _ : Fin (k + 1) => A)), ∃ F : Finset A, x ∈ firstAndFinite R A k F := by
  first | (exact @GlobalTheory.EtC.exists_finset_mem_firstAndFinite) | (exact GlobalTheory.EtC.exists_finset_mem_firstAndFinite) | (intros; apply GlobalTheory.EtC.exists_finset_mem_firstAndFinite  <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsHomAffineHilbertBaseSectionRingHom
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open scoped TensorProduct

namespace GlobalTheory.HilbAff

theorem secAlg_toSpecΓ_top (Z : Scheme.{0}) :
    secAlg Γ(Z, ⊤) Z.toSpecΓ ⊤ = RingHom.id _ := by
  ext a
  have e : Z.toSpecΓ.appLE ⊤ ⊤ (by simp) = Z.toSpecΓ.appTop := (Scheme.Hom.app_eq_appLE _).symm
  simp only [secAlg, RingHom.comp_apply, e, Scheme.toSpecΓ_appTop]
  simp

theorem exists_hom_secAlg_top (Z : Scheme.{0}) (C : Type) [CommRing C] (Φ : C →+* Γ(Z, ⊤)) :
    ∃ h : Z ⟶ Spec (CommRingCat.of C), GlobalTheory.HilbAff.secAlg C h ⊤ = Φ := by
  refine ⟨Z.toSpecΓ ≫ Spec.map (CommRingCat.ofHom Φ), ?_⟩
  rw [secAlg_comp, secAlg_toSpecΓ_top]
  rfl

end GlobalTheory.HilbAff
end

