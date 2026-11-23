module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.AdelicHermitianForms.Bundle0001

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.SpanRangeEqTopOfIsIrreducible
section
open Matrix GlobalTheory.ClassFin
open scoped Kronecker ComplexOrder TensorProduct

namespace GlobalTheory.ClassFin

open scoped MonoidAlgebra

open Matrix in
open scoped Kronecker ComplexOrder TensorProduct in
open scoped MonoidAlgebra in
private theorem subalgebra_end_eq_whole_of_isSimpleModule {V : Type} [AddCommGroup V] [Module ℂ V]
    [FiniteDimensional ℂ V] (A : Subalgebra ℂ (Module.End ℂ V)) [IsSimpleModule A V] :
    A = ⊤ := by
  classical
  have schur : ∀ f : V →ₗ[A] V, ∃ c : ℂ, ∀ y, f y = c • y := by
    intro f
    obtain ⟨c, hc⟩ := (IsSimpleModule.algebraMap_end_bijective_of_isAlgClosed (A := A) (V := V) ℂ).2 f
    exact ⟨c, fun y => by rw [← hc]; rfl⟩
  let b := Module.finBasis ℂ V
  let ι := Fin (Module.finrank ℂ V)
  let N : Submodule A (ι → V) := Submodule.span A {fun i => b i}
  obtain ⟨W, hW⟩ := exists_isCompl N
  let P : (ι → V) →ₗ[A] (ι → V) := N.subtype.comp (Submodule.linearProjOfIsCompl N W hW)
  have hPN : ∀ x, P x ∈ N := fun x => (Submodule.linearProjOfIsCompl N W hW x).2
  have hPfix : ∀ x ∈ N, P x = x := fun x hx => by
    simp only [P, LinearMap.comp_apply, Submodule.subtype_apply]
    exact congrArg Subtype.val (Submodule.linearProjOfIsCompl_apply_left hW ⟨x, hx⟩)
  have hcomm : ∀ (T : Module.End ℂ V) (x : ι → V), P (fun i => T (x i)) = fun i => T (P x i) := by
    intro T x
    have hsingle : ∀ (i j : ι) (y : V), P (Pi.single j (T y)) i = T (P (Pi.single j y) i) := by
      intro i j y
      obtain ⟨c, hc⟩ := schur ((LinearMap.proj i).comp (P.comp (LinearMap.single A (fun _ : ι => V) j)))
      have h1 := hc (T y)
      have h2 := hc y
      simp only [LinearMap.comp_apply, LinearMap.proj_apply, LinearMap.single_apply] at h1 h2
      rw [h1, h2, map_smul]
    funext i
    set_option synthInstance.maxHeartbeats 100000 in
      conv_lhs => rw [← Finset.univ_sum_single (fun i => T (x i)), map_sum]
    set_option synthInstance.maxHeartbeats 100000 in
      conv_rhs => rw [← Finset.univ_sum_single x, map_sum]
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [Finset.sum_apply, map_sum, hsingle]
  ext T
  simp only [Algebra.mem_top, iff_true]
  have hmem : (fun i => T (b i)) ∈ N := by
    have hfix : P (fun i => T (b i)) = fun i => T (b i) := by
      rw [hcomm T (fun i => b i), hPfix _ (Submodule.mem_span_singleton_self _)]
    rw [← hfix]
    exact hPN _
  obtain ⟨a, ha⟩ := Submodule.mem_span_singleton.1 hmem
  have hT : T = (a : Module.End ℂ V) := by
    refine b.ext fun i => ?_
    have := congrFun ha i
    exact this.symm
  rw [hT]
  exact a.2


open Matrix in
open scoped Kronecker ComplexOrder TensorProduct in
open scoped MonoidAlgebra in
theorem _root_.GlobalTheory.ClassFin.span_range_eq_top_of_isIrreducible :
    ∀ (G : Type) [Group G] (V : Type) [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ G V) [FiniteDimensional ℂ V], ρ.IsIrreducible → Submodule.span ℂ (Set.range ρ) = ⊤ := by
  intro G _ V _ _ ρ _ h
  let A : Subalgebra ℂ (Module.End ℂ V) := Algebra.adjoin ℂ (Set.range ρ)
  have hρA : ∀ g, ρ g ∈ A := fun g => Algebra.subset_adjoin ⟨g, rfl⟩
  have hspan : Subalgebra.toSubmodule A = Submodule.span ℂ (Set.range ρ) := by
    rw [Algebra.adjoin_eq_span]
    congr 1
    have : Set.range ρ = ((MonoidHom.mrange ρ : Submonoid (Module.End ℂ V)) : Set (Module.End ℂ V)) :=
      (MonoidHom.coe_mrange ρ).symm
    rw [this, Submonoid.closure_eq]
  let φ : Submodule A V → Subrepresentation ρ := fun M =>
    ⟨M.restrictScalars ℂ, fun g v hv => M.smul_mem (⟨ρ g, hρA g⟩ : A) hv⟩
  haveI : IsSimpleModule A V := by
    refine { exists_pair_ne := ⟨⊥, ⊤, fun hbt => ?_⟩, eq_bot_or_eq_top := fun M => ?_ }
    · obtain ⟨S, S', hS'⟩ := h.exists_pair_ne
      have hzero : ∀ x : V, x = 0 := fun x => by
        have : x ∈ (⊤ : Submodule A V) := Submodule.mem_top
        rw [← hbt] at this
        exact (Submodule.mem_bot A).1 this
      have hall : ∀ T U : Subrepresentation ρ, T = U := fun T U => by
        apply Subrepresentation.ext
        ext x
        rw [hzero x]
        exact ⟨fun _ => U.toSubmodule.zero_mem, fun _ => T.toSubmodule.zero_mem⟩
      exact hS' (hall S S')
    · rcases h.eq_bot_or_eq_top (φ M) with hM | hM
      · left
        have := congrArg Subrepresentation.toSubmodule hM
        exact (Submodule.restrictScalars_eq_bot_iff ℂ A V).1 this
      · right
        have := congrArg Subrepresentation.toSubmodule hM
        exact (Submodule.restrictScalars_eq_top_iff ℂ A V).1 this
  rw [← hspan, subalgebra_end_eq_whole_of_isSimpleModule A]
  ext x
  simp

end GlobalTheory.ClassFin
end

-- bundled from Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.SsTransfer
section
open Matrix GlobalTheory.ClassFin
open scoped Kronecker ComplexOrder TensorProduct

namespace GlobalTheory.ClassFin

theorem ss_transfer : ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (S Γ : Set (Matrix ι ι ℂ)), (S ⊆ Γ → Γ ⊆ (Submodule.span ℂ S : Set (Matrix ι ι ℂ)) → SS S → SS Γ) ∧ ∀ P : Matrix ι ι ℂ, IsUnit P.det → SS ((fun x => P * x * P⁻¹) '' S) → SS S := by
  intro ι _ _ S Γ
  refine ⟨fun h1 h2 hS W hW => ?_, fun P hP hS W hW => ?_⟩
  · obtain ⟨W', hW', hc⟩ := hS W (fun g hg => hW g (h1 hg))
    refine ⟨W', fun g hg v hv => ?_, hc⟩
    have hg' : g ∈ Submodule.span ℂ S := h2 hg
    clear hg
    induction hg' using Submodule.span_induction with
    | mem x hx => exact hW' x hx v hv
    | zero => simp
    | add x y _ _ hx hy => rw [Matrix.add_mulVec]; exact W'.add_mem hx hy
    | smul a x _ hx => rw [Matrix.smul_mulVec]; exact W'.smul_mem a hx
  · have h1 : P * P⁻¹ = 1 := Matrix.mul_nonsing_inv P hP
    have h2 : P⁻¹ * P = 1 := Matrix.nonsing_inv_mul P hP
    let e : (ι → ℂ) ≃ₗ[ℂ] (ι → ℂ) :=
      { P.mulVecLin with
        invFun := fun v => P⁻¹ *ᵥ v
        left_inv := fun v => by simp [Matrix.mulVec_mulVec, h2]
        right_inv := fun v => by simp [Matrix.mulVec_mulVec, h1] }
    have he : ∀ v, e v = P *ᵥ v := fun v => rfl
    have key : ∀ (x : Matrix ι ι ℂ) (v : ι → ℂ), (P * x * P⁻¹) *ᵥ (P *ᵥ v) = P *ᵥ (x *ᵥ v) := by
      intro x v
      rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, Matrix.mul_assoc, h2, Matrix.mul_one]
    obtain ⟨W', hW', hc⟩ := hS (Submodule.orderIsoMapComap e W) (by
      rintro _ ⟨x, hx, rfl⟩ _ ⟨v, hv, rfl⟩
      exact ⟨x *ᵥ v, hW x hx v hv, (key x v).symm⟩)
    refine ⟨(Submodule.orderIsoMapComap e).symm W', fun g hg v hv => ?_, ?_⟩
    · have hv' : P *ᵥ v ∈ W' := hv
      have := hW' _ ⟨g, hg, rfl⟩ _ hv'
      rw [key] at this
      exact this
    · have := (Submodule.orderIsoMapComap e).symm.isCompl hc
      rwa [OrderIso.symm_apply_apply] at this

end GlobalTheory.ClassFin
end

-- bundled from Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.TensorSLOrbitMapProperOfIsClosed
section
open Matrix GlobalTheory.ClassFin
open scoped Kronecker ComplexOrder TensorProduct

namespace GlobalTheory.ClassFin.OrbitProper

variable {ι : Type} [Fintype ι] [DecidableEq ι]

omit [DecidableEq ι] in
lemma tpow_mul' (n : ℕ) (y z : Matrix ι ι ℂ) : tpow n (y * z) = tpow n y * tpow n z := by
  classical
  ext a b
  simp only [tpow, Matrix.mul_apply, Matrix.of_apply]
  rw [Finset.prod_univ_sum]
  simp [Finset.prod_mul_distrib]

lemma tpow_one' (n : ℕ) : tpow n (1 : Matrix ι ι ℂ) = 1 := by
  ext a b
  simp only [tpow, Matrix.of_apply, Matrix.one_apply]
  rw [Finset.prod_ite_zero]
  simp [funext_iff]

variable {m : ℕ} (d : Fin m → ℕ)

omit [DecidableEq ι] in
lemma act_mul' (t : TIdx ι d → ℂ) (y z : Matrix ι ι ℂ) :
    act d t (y * z) = act d (act d t y) z := by
  funext k
  simp only [act, tpow_mul', ← Matrix.vecMul_vecMul]

lemma act_one' (t : TIdx ι d → ℂ) : act d t 1 = t := by
  funext k
  simp [act, tpow_one']

omit [DecidableEq ι] in
lemma continuous_act_right (t : TIdx ι d → ℂ) : Continuous (act d t) := by
  refine continuous_pi fun k => ?_
  simp only [act, Matrix.vecMul, dotProduct, tpow, Matrix.of_apply]
  fun_prop

omit [DecidableEq ι] in
lemma continuous_act_left (y : Matrix ι ι ℂ) : Continuous (fun t : TIdx ι d → ℂ => act d t y) := by
  refine continuous_pi fun k => ?_
  simp only [act, Matrix.vecMul, dotProduct, tpow, Matrix.of_apply]
  fun_prop

def box (ι : Type) [Fintype ι] [DecidableEq ι] (N : ℝ) : Set (Matrix ι ι ℂ) :=
  {y | y.det = 1 ∧ ∀ i j, ‖y i j‖ ≤ N}

lemma isCompact_box (N : ℝ) : IsCompact (box ι N) := by
  have h1 : IsCompact (Set.univ.pi fun _ : ι => Set.univ.pi fun _ : ι => Metric.closedBall (0 : ℂ) N) :=
    isCompact_univ_pi fun _ => isCompact_univ_pi fun _ => isCompact_closedBall _ _
  have h2 : IsClosed {y : Matrix ι ι ℂ | y.det = 1} :=
    isClosed_eq (continuous_id.matrix_det) continuous_const
  have h3 := IsCompact.inter_left (X := Matrix ι ι ℂ) h1 h2
  convert h3 using 1
  ext y
  exact ⟨fun h => ⟨h.1, fun i _ j _ => mem_closedBall_zero_iff.2 (h.2 i j)⟩,
    fun h => ⟨h.1, fun i j => mem_closedBall_zero_iff.1 (h.2 i trivial j trivial)⟩⟩

lemma box_mono {N M : ℝ} (h : N ≤ M) : box ι N ⊆ box ι M :=
  fun _ hy => ⟨hy.1, fun i j => (hy.2 i j).trans h⟩

lemma box_mul (N : ℝ) (g : Matrix ι ι ℂ) (hg : g.det = 1) : ∃ M : ℝ, ∀ a ∈ box ι N, a * g ∈ box ι M := by
  refine ⟨∑ j, ∑ k, |N| * ‖g k j‖, fun a ha => ⟨by rw [Matrix.det_mul, ha.1, hg, one_mul], fun i j => ?_⟩⟩
  calc ‖(a * g) i j‖ ≤ ∑ k, |N| * ‖g k j‖ := by
        rw [Matrix.mul_apply]
        refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun k _ => ?_)
        rw [norm_mul]
        exact mul_le_mul_of_nonneg_right ((ha.2 i k).trans (le_abs_self N)) (norm_nonneg _)
    _ ≤ _ := Finset.single_le_sum (f := fun j => ∑ k, |N| * ‖g k j‖)
        (fun j _ => Finset.sum_nonneg fun k _ => by positivity) (Finset.mem_univ j)

lemma det_adj {y : Matrix ι ι ℂ} (hy : y.det = 1) : y.adjugate.det = 1 := by
  rw [Matrix.det_adjugate, hy, one_pow]

lemma adj_mul {y : Matrix ι ι ℂ} (hy : y.det = 1) : y.adjugate * y = 1 := by
  rw [Matrix.adjugate_mul, hy, one_smul]

lemma mul_adj {y : Matrix ι ι ℂ} (hy : y.det = 1) : y * y.adjugate = 1 := by
  rw [Matrix.mul_adjugate, hy, one_smul]

lemma exists_interior (v : TIdx ι d → ℂ) (hX : IsClosed (orb d v)) :
    ∃ (n : ℝ) (O : Set (TIdx ι d → ℂ)) (y₀ : Matrix ι ι ℂ), IsOpen O ∧ y₀.det = 1 ∧ act d v y₀ ∈ O ∧
      ∀ w ∈ O, w ∈ orb d v → w ∈ act d v '' box ι n := by
  haveI : CompleteSpace (orb d v) := hX.completeSpace_coe
  haveI : Nonempty (orb d v) := ⟨⟨act d v 1, 1, Matrix.det_one, rfl⟩⟩
  obtain ⟨n, x, hx⟩ := nonempty_interior_of_iUnion_of_closed (X := orb d v)
    (f := fun n : ℕ => Subtype.val ⁻¹' (act d v '' box ι n))
    (fun n => ((isCompact_box (n : ℝ)).image (continuous_act_right d v)).isClosed.preimage
      continuous_subtype_val)
    (by
      refine Set.eq_univ_of_forall fun ⟨w, y, hy, hw⟩ => ?_
      obtain ⟨M, hM⟩ := box_mul (ι := ι) 1 y hy
      have h1 : (1 : Matrix ι ι ℂ) ∈ box ι 1 := ⟨Matrix.det_one, fun i j => by
        rw [Matrix.one_apply]; split_ifs <;> simp⟩
      have := hM 1 h1
      rw [one_mul] at this
      exact Set.mem_iUnion.2 ⟨⌈M⌉₊, y, box_mono (Nat.le_ceil M) this, hw.symm⟩)
  rw [mem_interior] at hx
  obtain ⟨t, hts, hto, hxt⟩ := hx
  obtain ⟨O, hO, rfl⟩ := isOpen_induced_iff.1 hto
  obtain ⟨x, y₀, hy₀, rfl⟩ := x
  exact ⟨n, O, y₀, hO, hy₀, hxt, fun w hw hwX => hts (a := ⟨w, hwX⟩) hw⟩

lemma locally_box (v : TIdx ι d → ℂ) (hX : IsClosed (orb d v)) (w : TIdx ι d → ℂ) (hw : w ∈ orb d v) :
    ∃ O : Set (TIdx ι d → ℂ), IsOpen O ∧ w ∈ O ∧ ∃ N : ℝ, O ∩ orb d v ⊆ act d v '' box ι N := by
  obtain ⟨n, O, y₀, hO, hy₀, hmem, hsub⟩ := exists_interior d v hX
  obtain ⟨y, hy, rfl⟩ := hw
  obtain ⟨M, hM⟩ := box_mul (ι := ι) n (y₀.adjugate * y)
    (by rw [Matrix.det_mul, det_adj hy₀, hy, one_mul])
  refine ⟨(fun t => act d t (y.adjugate * y₀)) ⁻¹' O, hO.preimage (continuous_act_left d _), ?_, M, ?_⟩
  · show act d (act d v y) (y.adjugate * y₀) ∈ O
    rwa [← act_mul', ← mul_assoc, mul_adj hy, one_mul]
  · rintro w ⟨hwO, z, hz, rfl⟩
    obtain ⟨a, ha, hav⟩ := hsub _ hwO ⟨z * (y.adjugate * y₀),
      by rw [Matrix.det_mul, Matrix.det_mul, det_adj hy, hy₀, hz]; simp, (act_mul' d v _ _).symm⟩
    refine ⟨_, hM a ha, ?_⟩
    simp only at hav
    rw [act_mul', hav, ← act_mul', mul_assoc, ← mul_assoc y₀, mul_adj hy₀, one_mul, adj_mul hy, act_one']

lemma isCompact_nsq {κ : Type} [Fintype κ] (C : ℝ) : IsCompact {w : κ → ℂ | nsq w ≤ C} := by
  refine Metric.isCompact_of_isClosed_isBounded ?_ ?_
  · refine isClosed_le ?_ continuous_const
    unfold nsq
    fun_prop
  · refine (Metric.isBounded_closedBall (x := (0 : κ → ℂ)) (r := Real.sqrt C)).subset fun w hw => ?_
    rw [mem_closedBall_zero_iff, pi_norm_le_iff_of_nonneg (Real.sqrt_nonneg _)]
    intro k
    refine Real.le_sqrt_of_sq_le (le_trans ?_ hw)
    exact Finset.single_le_sum (f := fun k => ‖w k‖ ^ 2) (fun _ _ => by positivity) (Finset.mem_univ k)

end GlobalTheory.ClassFin.OrbitProper


open GlobalTheory.ClassFin.OrbitProper in
theorem GlobalTheory.ClassFin.orbit_proper_of_isClosed : ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (m : ℕ) (d : Fin m → ℕ) (v : TIdx ι d → ℂ), IsClosed (orb d v) → ∀ C : ℝ, ∃ C' : ℝ, ∀ y : Matrix ι ι ℂ, y.det = 1 → nsq (act d v y) ≤ C → ∃ h : Matrix ι ι ℂ, h.det = 1 ∧ act d v h = v ∧ ∀ i j, ‖(h * y) i j‖ ≤ C' := by
  intro ι _ _ m d v hX C
  have hK : IsCompact (orb d v ∩ {w | nsq w ≤ C}) := (isCompact_nsq C).inter_left hX
  have key : ∃ N : ℝ, orb d v ∩ {w | nsq w ≤ C} ⊆ act d v '' box ι N := by
    refine hK.induction_on (p := fun s => ∃ N : ℝ, s ⊆ act d v '' box ι N) ⟨0, Set.empty_subset _⟩
      (fun s t hst ⟨N, hN⟩ => ⟨N, hst.trans hN⟩) ?_ ?_
    · rintro s t ⟨N, hN⟩ ⟨M, hM⟩
      exact ⟨max N M, Set.union_subset (hN.trans (Set.image_mono (box_mono (le_max_left _ _))))
        (hM.trans (Set.image_mono (box_mono (le_max_right _ _))))⟩
    · intro w hw
      obtain ⟨O, hO, hwO, N, hN⟩ := locally_box d v hX w hw.1
      refine ⟨O ∩ orb d v, ?_, N, hN⟩
      exact mem_nhdsWithin.2 ⟨O, hO, hwO, fun x hx => ⟨hx.1, hx.2.1⟩⟩
  obtain ⟨N, hN⟩ := key
  refine ⟨N, fun y hy hC => ?_⟩
  obtain ⟨a, ha, hav⟩ := hN (a := act d v y) ⟨⟨y, hy, rfl⟩, hC⟩
  refine ⟨a * y.adjugate, by rw [Matrix.det_mul, ha.1, det_adj hy, one_mul], ?_, ?_⟩
  · rw [act_mul', hav, ← act_mul', mul_adj hy, act_one']
  · rw [mul_assoc, adj_mul hy, mul_one]
    exact ha.2
end

-- bundled from Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.TraceLogLeLogDet
section
open Matrix GlobalTheory.ClassFin
open scoped Kronecker ComplexOrder TensorProduct

namespace GlobalTheory.LogCompress

theorem jensen_exp {ι : Type} [Fintype ι] (w d : ι → ℝ) (hw : ∀ j, 0 ≤ w j) (h1 : ∑ j, w j = 1) :
    0 < ∑ j, w j * Real.exp (d j) ∧ ∑ j, w j * d j ≤ Real.log (∑ j, w j * Real.exp (d j)) ∧
      (∑ j, w j * d j = Real.log (∑ j, w j * Real.exp (d j)) →
        ∀ j, w j ≠ 0 → Real.exp (d j) = ∑ j, w j * Real.exp (d j)) := by
  set m := ∑ j, w j * Real.exp (d j) with hm
  have hpos : 0 < m := by
    obtain ⟨j, -, hj⟩ : ∃ j ∈ (Finset.univ : Finset ι), w j ≠ 0 :=
      Finset.exists_ne_zero_of_sum_ne_zero (by rw [h1]; exact one_ne_zero)
    exact Finset.sum_pos' (fun i _ => mul_nonneg (hw i) (Real.exp_pos _).le)
      ⟨j, Finset.mem_univ _, mul_pos (lt_of_le_of_ne (hw j) hj.symm) (Real.exp_pos _)⟩
  have hexp : ∀ j, Real.exp (d j - Real.log m) = Real.exp (d j) / m := by
    intro j
    rw [Real.exp_sub, Real.exp_log hpos]
  have hnn : ∀ j ∈ (Finset.univ : Finset ι),
      0 ≤ w j * (Real.exp (d j - Real.log m) - (d j - Real.log m + 1)) :=
    fun j _ => mul_nonneg (hw j) (sub_nonneg.2 (Real.add_one_le_exp _))
  have hsum : ∑ j, w j * (Real.exp (d j - Real.log m) - (d j - Real.log m + 1))
      = Real.log m - ∑ j, w j * d j := by
    have : ∀ j, w j * (Real.exp (d j - Real.log m) - (d j - Real.log m + 1))
        = w j * Real.exp (d j) / m - w j * d j + w j * (Real.log m - 1) := by
      intro j
      rw [hexp]; ring
    simp only [this, Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.sum_div,
      ← Finset.sum_mul, h1, ← hm, div_self hpos.ne']
    ring
  refine ⟨hpos, ?_, ?_⟩
  · have := Finset.sum_nonneg hnn
    linarith
  · intro h j hj
    have h0 := (Finset.sum_eq_zero_iff_of_nonneg hnn).1 (by rw [hsum, h, sub_self]) j
      (Finset.mem_univ _)
    have h2 := (mul_eq_zero.1 h0).resolve_left hj
    have h3 : d j - Real.log m = 0 := by
      by_contra hne
      have := Real.add_one_lt_exp hne
      linarith
    have h4 : d j = Real.log m := by linarith
    rw [h4, Real.exp_log hpos]

theorem compress_diag {ι κ : Type} [Fintype ι] [DecidableEq ι] (C : Matrix ι κ ℂ) (f : ι → ℝ) (k : κ) :
    (Cᴴ * diagonal (fun i => (f i : ℂ)) * C) k k = ((∑ j, Complex.normSq (C j k) * f j : ℝ) : ℂ) := by
  rw [Matrix.mul_apply]
  push_cast
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Matrix.mul_diagonal, Matrix.conjTranspose_apply, Complex.normSq_eq_conj_mul_self]
  simp only [Complex.star_def]
  ring

theorem exists_diag {κ : Type} [Fintype κ] [DecidableEq κ] (B : Matrix κ κ ℂ) (hB : B.IsHermitian) :
    ∃ (V : Matrix κ κ ℂ) (m : κ → ℂ), V * Vᴴ = 1 ∧ Vᴴ * V = 1 ∧ Vᴴ * B * V = diagonal m := by
  refine ⟨hB.eigenvectorUnitary, RCLike.ofReal ∘ hB.eigenvalues, ?_, ?_, ?_⟩
  · exact (Matrix.mem_unitaryGroup_iff.1 hB.eigenvectorUnitary.2)
  · exact (Matrix.mem_unitaryGroup_iff'.1 hB.eigenvectorUnitary.2)
  · have := hB.conjStarAlgAut_star_eigenvectorUnitary
    simpa [Matrix.star_eq_conjTranspose] using this

theorem trace_log_le_log_det : ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (κ : Type) [Fintype κ] [DecidableEq κ] (H A : Matrix ι ι ℂ) (Q : Matrix ι κ ℂ), IsLog H A → Qᴴ * Q = 1 → (Matrix.trace (Qᴴ * H * Q)).re ≤ Real.log (Qᴴ * A * Q).det.re ∧ ((Matrix.trace (Qᴴ * H * Q)).re = Real.log (Qᴴ * A * Q).det.re → ∃ N : Matrix κ κ ℂ, A * Q = Q * N) := by
  intro ι _ _ κ _ _ H A Q ⟨U, d, hU, hH, hA⟩ hQ
  have hAh : A.IsHermitian := by
    rw [hA]
    refine Matrix.isHermitian_mul_mul_conjTranspose _ ?_
    rw [Matrix.isHermitian_diagonal_iff]
    intro i
    exact Complex.conj_ofReal _
  obtain ⟨V, m, hV, hV', hm⟩ := exists_diag _ (Matrix.isHermitian_conjTranspose_mul_mul Q hAh)
  set C : Matrix ι κ ℂ := Uᴴ * Q * V with hC
  have hCH : Cᴴ = Vᴴ * Qᴴ * U := by
    simp [hC, Matrix.conjTranspose_mul, Matrix.mul_assoc]
  have key : ∀ D : Matrix ι ι ℂ, Cᴴ * D * C = Vᴴ * (Qᴴ * (U * D * Uᴴ) * Q) * V := by
    intro D
    rw [hCH, hC]
    simp only [Matrix.mul_assoc]
  have hw : ∀ k, ∑ j, Complex.normSq (C j k) = 1 := by
    intro k
    have h := compress_diag C (fun _ => 1) k
    have h1 : diagonal (fun _ : ι => ((1 : ℝ) : ℂ)) = 1 := by simp
    rw [key, h1, Matrix.mul_one, hU, Matrix.mul_one, hQ, Matrix.mul_one, hV'] at h
    simp only [Matrix.one_apply_eq, mul_one] at h
    exact_mod_cast h.symm
  have hmk : ∀ k, m k = ((∑ j, Complex.normSq (C j k) * Real.exp (d j) : ℝ) : ℂ) := by
    intro k
    rw [← compress_diag C (fun j => Real.exp (d j)) k, key, ← hA, hm, Matrix.diagonal_apply_eq]
  have hJ := fun k => jensen_exp (fun j => Complex.normSq (C j k)) d
    (fun j => Complex.normSq_nonneg _) (hw k)
  have hdet : (Qᴴ * A * Q).det.re = ∏ k, ∑ j, Complex.normSq (C j k) * Real.exp (d j) := by
    have h := congrArg Matrix.det hm
    rw [Matrix.det_mul_comm, ← Matrix.mul_assoc, hV, Matrix.one_mul, Matrix.det_diagonal] at h
    rw [h]
    simp only [hmk]
    rw [← Complex.ofReal_prod, Complex.ofReal_re]
  have htr : (Matrix.trace (Qᴴ * H * Q)).re = ∑ k, ∑ j, Complex.normSq (C j k) * d j := by
    have h : Matrix.trace (Cᴴ * diagonal (fun i => (d i : ℂ)) * C) = Matrix.trace (Qᴴ * H * Q) := by
      rw [key, ← hH, Matrix.trace_mul_comm, ← Matrix.mul_assoc, hV, Matrix.one_mul]
    rw [← h, Matrix.trace]
    simp only [Matrix.diag_apply, compress_diag]
    rw [← Complex.ofReal_sum, Complex.ofReal_re]
  rw [hdet, htr, Real.log_prod (fun k _ => (hJ k).1.ne')]
  refine ⟨Finset.sum_le_sum fun k _ => (hJ k).2.1, fun h => ?_⟩
  have heq := (Finset.sum_eq_sum_iff_of_le fun k _ => (hJ k).2.1).1 h
  have hDC : diagonal (fun i => (Real.exp (d i) : ℂ)) * C = C * diagonal m := by
    ext j k
    rw [Matrix.diagonal_mul, Matrix.mul_diagonal]
    by_cases h0 : C j k = 0
    · simp [h0]
    · have := (hJ k).2.2 (heq k (Finset.mem_univ _)) j (by simpa using h0)
      rw [hmk, ← this, mul_comm]
  refine ⟨V * diagonal m * Vᴴ, ?_⟩
  have h1 : A * Q = U * (diagonal (fun i => (Real.exp (d i) : ℂ)) * C) * Vᴴ := by
    rw [hA, hC]
    simp only [Matrix.mul_assoc, hV, Matrix.mul_one]
  rw [h1, hDC, hC]
  simp only [← Matrix.mul_assoc, hU, Matrix.one_mul]

end GlobalTheory.LogCompress
end

-- bundled from Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.TwoPowCardLeIndexIInf
section
open NumberField IsDedekindDomain GlobalTheory.QNorm
open scoped WithZero

namespace GlobalTheory.QNorm

theorem two_pow_card_le_index_iInf :
    ∀ (G ι : Type) [CommGroup G] [Fintype ι] (K : ι → Subgroup G),
      (∀ i, ∃ x, x ∉ K i ∧ ∀ j, j ≠ i → x ∈ K j) → (⨅ i, K i).index ≠ 0 →
        2 ^ Fintype.card ι ≤ (⨅ i, K i).index := by
  intro G ι _ _ K h hidx
  classical
  choose x hx hx' using h
  have key : ∀ (A : Finset ι) (j : ι), (∏ i ∈ A, x i) ∈ K j ↔ j ∉ A := by
    intro A j
    constructor
    · intro hm hj
      rw [← Finset.mul_prod_erase A x hj] at hm
      have h2 : (∏ i ∈ A.erase j, x i) ∈ K j :=
        Subgroup.prod_mem _ fun i hi => hx' i j (Finset.ne_of_mem_erase hi).symm
      exact hx j ((Subgroup.mul_mem_cancel_right _ h2).1 hm)
    · intro hj
      exact Subgroup.prod_mem _ fun i hi => hx' i j (fun e => hj (e ▸ hi))
  haveI : Finite (G ⧸ ⨅ i, K i) := Nat.finite_of_card_ne_zero hidx
  have inj : Function.Injective
      (fun A : Finset ι => ((∏ i ∈ A, x i : G) : G ⧸ ⨅ i, K i)) := by
    intro A B hAB
    have hm : (∏ i ∈ A, x i)⁻¹ * (∏ i ∈ B, x i) ∈ ⨅ i, K i := QuotientGroup.eq.1 hAB
    ext j
    have hj : (∏ i ∈ A, x i)⁻¹ * (∏ i ∈ B, x i) ∈ K j := (Subgroup.mem_iInf.1 hm) j
    have hiff : (∏ i ∈ A, x i) ∈ K j ↔ (∏ i ∈ B, x i) ∈ K j := by
      constructor
      · intro ha
        exact (Subgroup.mul_mem_cancel_left _ (inv_mem ha)).1 hj
      · intro hb
        exact inv_mem_iff.1 ((Subgroup.mul_mem_cancel_right _ hb).1 hj)
    rw [key, key] at hiff
    exact not_iff_not.1 hiff
  have := Nat.card_le_card_of_injective _ inj
  rwa [Nat.card_eq_fintype_card, Fintype.card_finset] at this

end GlobalTheory.QNorm
end

