module

public import Mathlib
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.StabilizerIndexVolumes.Bundle0001
public import Lemmata.GeneralBFactThirdVersion.Imports

@[expose] public section

-- bundled from Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.StabilizerIndexVolumes.DiagMulOfBt
section
noncomputable section

open NumberField Matrix

namespace Formalism.L2.SG.Pf.StabilizerIndexVolumes

section Tri

variable {K : Type*} [Field K] {N : ℕ}

theorem diag_mul_of_bt {α : Type*} [LinearOrder α] {b : Fin N → α} (hb : Function.Injective b)
    {A B : Matrix (Fin N) (Fin N) K} (hA : A.BlockTriangular b) (hB : B.BlockTriangular b) (i : Fin N) :
    (A * B) i i = A i i * B i i := by
  rw [Matrix.mul_apply, Finset.sum_eq_single i]
  · intro k _ hk
    rcases lt_or_gt_of_ne (hb.ne hk) with h | h
    · rw [hA h, zero_mul]
    · rw [hB h, mul_zero]
  · intro h
    exact absurd (Finset.mem_univ i) h

theorem uni_inv {α : Type*} [LinearOrder α] {b : Fin N → α} (hb : Function.Injective b)
    {M : Matrix (Fin N) (Fin N) K} (hM : M.BlockTriangular b) (hd : ∀ i, M i i = 1)
    (hdet : IsUnit M.det) : M⁻¹.BlockTriangular b ∧ ∀ i, M⁻¹ i i = 1 := by
  haveI := M.invertibleOfIsUnitDet hdet
  have hI : M⁻¹.BlockTriangular b := Matrix.blockTriangular_inv_of_blockTriangular hM
  refine ⟨hI, fun i => ?_⟩
  have h1 := congrFun (congrFun (Matrix.mul_nonsing_inv M hdet) i) i
  rw [diag_mul_of_bt hb hM hI, hd, one_mul, Matrix.one_apply_eq] at h1
  exact h1

theorem lo_bt {L : Matrix (Fin N) (Fin N) K} (h : Formalism.MainNotions.S.IsLoUni L) :
    L.BlockTriangular OrderDual.toDual := by
  intro i j hij
  exact (h i j).1 (OrderDual.toDual_lt_toDual.mp hij)

theorem up_bt {U : Matrix (Fin N) (Fin N) K} (h : Formalism.MainNotions.S.IsUpUni U) : U.BlockTriangular id := by
  intro i j hij
  exact (h i j).1 hij

theorem lo_of {L : Matrix (Fin N) (Fin N) K} (h : L.BlockTriangular OrderDual.toDual)
    (hd : ∀ i, L i i = 1) : Formalism.MainNotions.S.IsLoUni L := by
  intro i j
  refine ⟨fun hij => h (OrderDual.toDual_lt_toDual.mpr hij), ?_⟩
  rintro rfl
  exact hd i

theorem up_of {U : Matrix (Fin N) (Fin N) K} (h : U.BlockTriangular id)
    (hd : ∀ i, U i i = 1) : Formalism.MainNotions.S.IsUpUni U := by
  intro i j
  refine ⟨fun hij => h hij, ?_⟩
  rintro rfl
  exact hd i

theorem lo_det {L : Matrix (Fin N) (Fin N) K} (h : Formalism.MainNotions.S.IsLoUni L) : L.det = 1 := by
  rw [Matrix.det_of_lowerTriangular (M := L) (lo_bt h)]
  exact Finset.prod_eq_one fun i _ => (h i i).2 rfl

theorem up_det {U : Matrix (Fin N) (Fin N) K} (h : Formalism.MainNotions.S.IsUpUni U) : U.det = 1 := by
  rw [Matrix.det_of_upperTriangular (M := U) (up_bt h)]
  exact Finset.prod_eq_one fun i _ => (h i i).2 rfl

theorem lo_mul {A B : Matrix (Fin N) (Fin N) K} (hA : Formalism.MainNotions.S.IsLoUni A) (hB : Formalism.MainNotions.S.IsLoUni B) :
    Formalism.MainNotions.S.IsLoUni (A * B) := by
  refine lo_of ((lo_bt hA).mul (lo_bt hB)) fun i => ?_
  rw [diag_mul_of_bt OrderDual.toDual.injective (lo_bt hA) (lo_bt hB), (hA i i).2 rfl, (hB i i).2 rfl, one_mul]

theorem up_mul {A B : Matrix (Fin N) (Fin N) K} (hA : Formalism.MainNotions.S.IsUpUni A) (hB : Formalism.MainNotions.S.IsUpUni B) :
    Formalism.MainNotions.S.IsUpUni (A * B) := by
  refine up_of ((up_bt hA).mul (up_bt hB)) fun i => ?_
  rw [diag_mul_of_bt Function.injective_id (up_bt hA) (up_bt hB), (hA i i).2 rfl, (hB i i).2 rfl, one_mul]

theorem lo_inv {A : Matrix (Fin N) (Fin N) K} (hA : Formalism.MainNotions.S.IsLoUni A) : Formalism.MainNotions.S.IsLoUni A⁻¹ := by
  obtain ⟨h1, h2⟩ := uni_inv OrderDual.toDual.injective (lo_bt hA) (fun i => (hA i i).2 rfl)
    (by rw [lo_det hA]; exact isUnit_one)
  exact lo_of h1 h2

theorem up_inv {A : Matrix (Fin N) (Fin N) K} (hA : Formalism.MainNotions.S.IsUpUni A) : Formalism.MainNotions.S.IsUpUni A⁻¹ := by
  obtain ⟨h1, h2⟩ := uni_inv Function.injective_id (up_bt hA) (fun i => (hA i i).2 rfl)
    (by rw [up_det hA]; exact isUnit_one)
  exact up_of h1 h2

theorem lo_one : Formalism.MainNotions.S.IsLoUni (1 : Matrix (Fin N) (Fin N) K) := by
  intro i j
  refine ⟨fun h => Matrix.one_apply_ne (ne_of_lt h), ?_⟩
  rintro rfl
  exact Matrix.one_apply_eq i

theorem up_one : Formalism.MainNotions.S.IsUpUni (1 : Matrix (Fin N) (Fin N) K) := by
  intro i j
  refine ⟨fun h => Matrix.one_apply_ne (ne_of_gt h), ?_⟩
  rintro rfl
  exact Matrix.one_apply_eq i

end Tri

theorem stClosed : StClosed := by
  unfold StClosed
  intro E _ _ n W
  simp only [StSet, Set.mem_setOf_eq]
  refine ⟨?_, ?_, ?_⟩
  · refine ⟨by rw [Units.val_one]; exact lo_one, 1, up_one, ?_⟩
    rw [Units.val_one, Matrix.one_mul, Matrix.mul_one]
  · rintro a ⟨ha, b, hb, hab⟩ a' ⟨ha', b', hb', hab'⟩
    refine ⟨?_, b' * b, up_mul hb' hb, ?_⟩
    · rw [Units.val_mul]
      exact lo_mul ha ha'
    · rw [Units.val_mul]
      calc _ = (a : Matrix (Fin n) (Fin n) E) * ((a' : Matrix (Fin n) (Fin n) E) * W * b') * b := by
            simp only [Matrix.mul_assoc]
        _ = W := by rw [hab', hab]
  · rintro a ⟨ha, b, hb, hab⟩
    have hbdet : IsUnit b.det := by rw [up_det hb]; exact isUnit_one
    refine ⟨?_, b⁻¹, up_inv hb, ?_⟩
    · rw [Matrix.coe_units_inv]
      exact lo_inv ha
    · calc _ = ((a⁻¹ : Matrix.GeneralLinearGroup (Fin n) E) : Matrix (Fin n) (Fin n) E) *
            ((a : Matrix (Fin n) (Fin n) E) * W * b) * b⁻¹ := by rw [hab]
        _ = (((a⁻¹ : Matrix.GeneralLinearGroup (Fin n) E) : Matrix (Fin n) (Fin n) E) *
            (a : Matrix (Fin n) (Fin n) E)) * W * (b * b⁻¹) := by simp only [Matrix.mul_assoc]
        _ = W := by rw [Units.inv_mul, Matrix.mul_nonsing_inv b hbdet, Matrix.one_mul, Matrix.mul_one]

end Formalism.L2.SG.Pf.StabilizerIndexVolumes
end
end

-- bundled from Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.StabilizerIndexVolumes.InvMulMemOfScaledEntriesCongr
section
noncomputable section

open NumberField Matrix

namespace Formalism.L2.SG.Pf.StabilizerIndexVolumes

variable {E : Type} [Field E] [NumberField E] {n : ℕ}

theorem inv_mul_mem_of_scaled_entries_congr (W : Matrix (Fin n) (Fin n) E) (H K : Subgroup (Matrix.GeneralLinearGroup (Fin n) E))
    (hHS : (H : Set (Matrix.GeneralLinearGroup (Fin n) E)) ⊆ StSet W) (N0 : ℕ) (hN0 : N0 ≠ 0)
    (hbd : ∀ h ∈ H, ∀ i j, IntE ((N0 : E) * (h : Matrix (Fin n) (Fin n) E) i j)) (N1 : ℕ) (hN1 : N1 ≠ 0)
    (hcg : ∀ a : Matrix.GeneralLinearGroup (Fin n) E, a ∈ StSet W →
      (∀ i j, IntE (((a : Matrix (Fin n) (Fin n) E) i j - (1 : Matrix (Fin n) (Fin n) E) i j) / (N1 : E))) → a ∈ K)
    (h1 h2 : Matrix.GeneralLinearGroup (Fin n) E) (hh1 : h1 ∈ H) (hh2 : h2 ∈ H)
    (c : Fin n → Fin n → 𝓞 E)
    (hc : ∀ k j, ((c k j : 𝓞 E) : E) * ((N0 * N0 * N1 : ℕ) : E) =
      (N0 : E) * (h2 : Matrix (Fin n) (Fin n) E) k j - (N0 : E) * (h1 : Matrix (Fin n) (Fin n) E) k j) :
    h1⁻¹ * h2 ∈ K := by
  have hN0E : (N0 : E) ≠ 0 := by exact_mod_cast hN0
  have hN1E : (N1 : E) ≠ 0 := by exact_mod_cast hN1
  apply hcg _ (hHS (H.mul_mem (H.inv_mem hh1) hh2))
  intro i j
  have hinv := hbd _ (H.inv_mem hh1)
  choose p hp using hinv
  refine ⟨∑ k, p i k * c k j, ?_⟩
  have hsub : ((h1⁻¹ * h2 : Matrix.GeneralLinearGroup (Fin n) E) : Matrix (Fin n) (Fin n) E) - 1 =
      ((h1⁻¹ : Matrix.GeneralLinearGroup (Fin n) E) : Matrix (Fin n) (Fin n) E) *
        ((h2 : Matrix (Fin n) (Fin n) E) - (h1 : Matrix (Fin n) (Fin n) E)) := by
    rw [Matrix.mul_sub, Units.val_mul, Units.inv_mul]
  have hent := congrFun (congrFun hsub i) j
  rw [Matrix.sub_apply] at hent
  have hcast : ((∑ k, p i k * c k j : 𝓞 E) : E) = ∑ k, (p i k : E) * (c k j : E) := by push_cast; rfl
  rw [hent, Matrix.mul_apply, Finset.sum_div, hcast]
  refine Finset.sum_congr rfl fun k _ => ?_
  have hpk := hp i k
  have hck := hc k j
  push_cast at hck
  have hX : ((h1⁻¹ : Matrix.GeneralLinearGroup (Fin n) E) : Matrix (Fin n) (Fin n) E) i k =
      (p i k : E) / N0 := by
    rw [hpk]; field_simp
  have hD : (h2 : Matrix (Fin n) (Fin n) E) k j - (h1 : Matrix (Fin n) (Fin n) E) k j =
      (c k j : E) * (N0 * N1) := by
    have : (N0 : E) * ((h2 : Matrix (Fin n) (Fin n) E) k j - (h1 : Matrix (Fin n) (Fin n) E) k j) =
        (N0 : E) * ((c k j : E) * (N0 * N1)) := by rw [mul_sub, ← hck]; ring
    exact mul_left_cancel₀ hN0E this
  rw [hX, Matrix.sub_apply, hD]
  field_simp

theorem commens : Commens := by
  intro E _ _ n W H K hHS ⟨N0, hN0, hbd⟩ ⟨N1, hN1, hcg⟩
  have hM0 : ((N0 * N0 * N1 : ℕ) : 𝓞 E) ≠ 0 := by
    exact_mod_cast (Nat.mul_ne_zero (Nat.mul_ne_zero hN0 hN0) hN1)
  have hI : Ideal.span {((N0 * N0 * N1 : ℕ) : 𝓞 E)} ≠ ⊥ := by
    simpa [Ideal.span_singleton_eq_bot] using hM0
  have : Finite (𝓞 E ⧸ Ideal.span {((N0 * N0 * N1 : ℕ) : 𝓞 E)}) :=
    Ideal.finiteQuotientOfFreeOfNeBot _ hI
  choose o ho using hbd
  let φ : H → Fin n → Fin n → 𝓞 E ⧸ Ideal.span {((N0 * N0 * N1 : ℕ) : 𝓞 E)} :=
    fun h i j => Ideal.Quotient.mk _ (o h h.2 i j)
  have key : ∀ h1 h2 : H, φ h1 = φ h2 → h1⁻¹ * h2 ∈ K.subgroupOf H := by
    intro h1 h2 hq
    have hc : ∀ k j, ∃ c : 𝓞 E, c * ((N0 * N0 * N1 : ℕ) : 𝓞 E) = o h2 h2.2 k j - o h1 h1.2 k j := by
      intro k j
      have := congrFun (congrFun hq k) j
      simp only [φ] at this
      exact Ideal.mem_span_singleton'.mp (Ideal.Quotient.eq.mp this.symm)
    choose c hc using hc
    rw [Subgroup.mem_subgroupOf]
    simp only [Subgroup.coe_mul, Subgroup.coe_inv]
    refine inv_mul_mem_of_scaled_entries_congr W H K hHS N0 hN0 (fun h hh i j => ⟨o h hh i j, ho h hh i j⟩) N1 hN1 hcg _ _ h1.2 h2.2 c
      fun k j => ?_
    have h3 := congrArg (fun x : 𝓞 E => (x : E)) (hc k j)
    have e1 : ((c k j * ((N0 * N0 * N1 : ℕ) : 𝓞 E) : 𝓞 E) : E) = (c k j : E) * ((N0 * N0 * N1 : ℕ) : E) := by
      push_cast; rfl
    have e2 : ((o h2 h2.2 k j - o h1 h1.2 k j : 𝓞 E) : E) = (o h2 h2.2 k j : E) - (o h1 h1.2 k j : E) := by
      push_cast; rfl
    rw [← e1, h3, e2, ho, ho]
  have : Finite (H ⧸ K.subgroupOf H) := by
    refine Finite.of_injective (fun q : H ⧸ K.subgroupOf H => φ (Quotient.out q)) ?_
    intro q1 q2 hq
    have := (QuotientGroup.eq (s := K.subgroupOf H)).mpr (key _ _ hq)
    simpa [QuotientGroup.out_eq'] using this
  exact Subgroup.index_ne_zero_of_finite

end Formalism.L2.SG.Pf.StabilizerIndexVolumes
end
end

-- bundled from Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.StabilizerIndexVolumes.NatSmulMem
section
noncomputable section

open NumberField

namespace Formalism.L2.SG.Pf.StabilizerIndexVolumes

section Den

variable {E : Type} [Field E] [NumberField E]

theorem intE_iff (x : E) : IntE x ↔ IsIntegral ℤ x := by
  rw [IsIntegralClosure.isIntegral_iff (A := 𝓞 E)]
  rfl

theorem intE_zero : IntE (0 : E) := ⟨0, by simp⟩

theorem intE_one : IntE (1 : E) := ⟨1, by simp⟩

theorem intE_nat (k : ℕ) : IntE (k : E) := ⟨k, by simp⟩

theorem intE_add {x y : E} (hx : IntE x) (hy : IntE y) : IntE (x + y) := by
  obtain ⟨a, rfl⟩ := hx; obtain ⟨b, rfl⟩ := hy; exact ⟨a + b, by simp⟩

theorem intE_neg {x : E} (hx : IntE x) : IntE (-x) := by
  obtain ⟨a, rfl⟩ := hx; exact ⟨-a, by simp⟩

theorem intE_mul {x y : E} (hx : IntE x) (hy : IntE y) : IntE (x * y) := by
  obtain ⟨a, rfl⟩ := hx; obtain ⟨b, rfl⟩ := hy; exact ⟨a * b, by simp⟩

theorem intE_nat_mul (k : ℕ) {x : E} (hx : IntE x) : IntE ((k : E) * x) := intE_mul (intE_nat k) hx

theorem intE_sum {ι : Type*} (s : Finset ι) (x : ι → E) (h : ∀ i ∈ s, IntE (x i)) : IntE (∑ i ∈ s, x i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using intE_zero
  | insert a s ha ih =>
    rw [Finset.sum_insert ha]
    exact intE_add (h a (Finset.mem_insert_self a s)) (ih fun i hi => h i (Finset.mem_insert_of_mem hi))

theorem intE_star [StarRing E] {x : E} (hx : IntE x) : IntE (star x) := by
  rw [intE_iff] at hx ⊢
  exact hx.map (starRingEnd E).toIntAlgHom

theorem den_exists (x : E) : ∃ m : ℕ, m ≠ 0 ∧ IntE ((m : E) * x) := by
  have hx : IsAlgebraic ℤ x := (IsFractionRing.isAlgebraic_iff ℤ ℚ E).mpr (.of_finite ℚ x)
  obtain ⟨m, s, hm, h⟩ := hx.exists_nsmul_eq (𝓞 E)
  refine ⟨m, hm, s, ?_⟩
  rw [← nsmul_eq_mul, h]

theorem den_fin {ι : Type*} [Fintype ι] (x : ι → E) : ∃ m : ℕ, m ≠ 0 ∧ ∀ i, IntE ((m : E) * x i) := by
  classical
  choose m hm hx using fun i => den_exists (x i)
  refine ⟨∏ i, m i, Finset.prod_ne_zero_iff.mpr (fun i _ => hm i), fun i => ?_⟩
  have : ((∏ j, m j : ℕ) : E) * x i = ((∏ j ∈ Finset.univ.erase i, m j : ℕ) : E) * ((m i : E) * x i) := by
    rw [← Finset.mul_prod_erase Finset.univ m (Finset.mem_univ i)]
    push_cast; ring
  rw [this]
  exact intE_nat_mul _ (hx i)

theorem den_mat {m n : Type*} [Fintype m] [Fintype n] (A : Matrix m n E) :
    ∃ k : ℕ, k ≠ 0 ∧ ∀ i j, IntE ((k : E) * A i j) := by
  obtain ⟨k, hk, h⟩ := den_fin (fun p : m × n => A p.1 p.2)
  exact ⟨k, hk, fun i j => h (i, j)⟩

theorem intE_matmul {l m n : Type*} [Fintype m] {A : Matrix l m E} {B : Matrix m n E} {a b : ℕ}
    (hA : ∀ i j, IntE ((a : E) * A i j)) (hB : ∀ i j, IntE ((b : E) * B i j)) :
    ∀ i j, IntE (((a * b : ℕ) : E) * (A * B) i j) := by
  intro i j
  rw [Matrix.mul_apply, Finset.mul_sum]
  refine intE_sum _ _ fun k _ => ?_
  have : ((a * b : ℕ) : E) * (A i k * B k j) = ((a : E) * A i k) * ((b : E) * B k j) := by push_cast; ring
  rw [this]; exact intE_mul (hA i k) (hB k j)

end Den

section Lat

variable {E : Type} [Field E] [NumberField E] {V : Type} [AddCommGroup V] [Module E V] [Module (𝓞 E) V]
  [IsScalarTower (𝓞 E) E V]

theorem coe_smul_eq (o : 𝓞 E) (v : V) : (o : E) • v = o • v := algebraMap_smul E o v

theorem nat_smul_mem (Λ : Submodule (𝓞 E) V) (k : ℕ) {v : V} (hv : v ∈ Λ) : (k : E) • v ∈ Λ := by
  rw [Nat.cast_smul_eq_nsmul]; exact Λ.toAddSubmonoid.nsmul_mem hv k

theorem int_smul_mem (Λ : Submodule (𝓞 E) V) {c : E} (hc : IntE c) {v : V} (hv : v ∈ Λ) : c • v ∈ Λ := by
  obtain ⟨o, rfl⟩ := hc
  rw [coe_smul_eq]; exact Λ.smul_mem o hv

theorem lat_smul_mem (Λ : Submodule (𝓞 E) V) (h : Submodule.IsFullLattice E Λ) (v : V) :
    ∃ m : ℕ, m ≠ 0 ∧ (m : E) • v ∈ Λ := by
  exact Bl.general_b_fact_third_version.goal1 Λ h v

theorem lat_fun_bdd (Λ : Submodule (𝓞 E) V) (h : Submodule.IsLattice E Λ) {ι : Type*} [Fintype ι]
    (φ : ι → V →ₗ[E] E) : ∃ m : ℕ, m ≠ 0 ∧ ∀ v ∈ Λ, ∀ i, IntE ((m : E) * φ i v) := by
  classical
  obtain ⟨S, hS⟩ := h.fg
  obtain ⟨m, hm, hmS⟩ := den_fin (fun p : ι × S => φ p.1 (p.2 : V))
  refine ⟨m, hm, fun v hv i => ?_⟩
  rw [← hS] at hv
  induction hv using Submodule.span_induction with
  | mem x hx => exact hmS (i, ⟨x, hx⟩)
  | zero => simpa using intE_zero
  | add x y _ _ hx hy => rw [map_add (f := _), mul_add]; exact intE_add hx hy
  | smul o x _ hx =>
    rw [← coe_smul_eq, LinearMap.map_smul, smul_eq_mul, mul_left_comm]
    exact intE_mul ⟨o, rfl⟩ hx

theorem coord_exists [FiniteDimensional E V] {n : ℕ} {f : Fin n → V} (hf : LinearIndependent E f) :
    ∃ φ : Fin n → V →ₗ[E] E, ∀ c d, φ c (f d) = if d = c then 1 else 0 := by
  classical
  have : ∀ c : Fin n, ∃ G : V →ₗ[E] E, ∀ d, G (f d) = if d = c then 1 else 0 := by
    intro c
    obtain ⟨G, hG⟩ := LinearMap.exists_extend ((Finsupp.lapply c).comp hf.repr)
    refine ⟨G, fun d => ?_⟩
    have h1 : G (f d) = (G.comp (Submodule.span E (Set.range f)).subtype) ⟨f d, Submodule.subset_span ⟨d, rfl⟩⟩ := rfl
    rw [h1, hG]
    rw [LinearMap.comp_apply, hf.repr_eq_single d _ rfl, Finsupp.lapply_apply, Finsupp.single_apply]
  choose φ hφ using this
  exact ⟨φ, hφ⟩

end Lat

end Formalism.L2.SG.Pf.StabilizerIndexVolumes
end
end

-- bundled from Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.StabilizerIndexVolumes.SESymmApply
section
noncomputable section

open NumberField Matrix

namespace Formalism.L2.SG.Pf.StabilizerIndexVolumes

variable {E : Type} [Field E] [NumberField E] [StarRing E] {S : Formalism.BasicNotions.HSpace E}
  {ι : Type} [Fintype ι] [DecidableEq ι]

def gramOf (g : ι → S.V) : Matrix ι ι E := fun k l => S.hT (g k) (g l)

def coordL (g : ι → S.V) (k : ι) : S.V →ₗ[E] E := ∑ l, ((gramOf g)⁻¹ k l) • S.hT (g l)

def cOf (g : ι → S.V) (v : S.V) : ι → E := fun k => coordL g k v

theorem cOf_eq (g : ι → S.V) (v : S.V) : cOf g v = (gramOf g)⁻¹ *ᵥ (fun l => S.hT (g l) v) := by
  ext k
  simp [cOf, coordL, Matrix.mulVec, dotProduct, LinearMap.sum_apply]

theorem cOf_add (g : ι → S.V) (v w : S.V) : cOf g (v + w) = cOf g v + cOf g w := by
  ext k; simp [cOf]

theorem cOf_smul (g : ι → S.V) (a : E) (v : S.V) : cOf g (a • v) = a • cOf g v := by
  ext k; simp [cOf]

theorem cOf_g (g : ι → S.V) (hG : IsUnit (gramOf g).det) (m : ι) : cOf g (g m) = Pi.single m 1 := by
  rw [cOf_eq]
  have : (fun l => S.hT (g l) (g m)) = (gramOf g) *ᵥ (Pi.single m 1) := by
    ext l; simp [gramOf, Matrix.mulVec_single]
  rw [this, Matrix.mulVec_mulVec, nonsing_inv_mul _ hG, Matrix.one_mulVec]

theorem cOf_comb (g : ι → S.V) (hG : IsUnit (gramOf g).det) (v : S.V) (y : ι → E) :
    cOf g (v + ∑ m, y m • g m) = cOf g v + y := by
  rw [cOf_add]
  congr 1
  have : cOf g (∑ m, y m • g m) = ∑ m, y m • cOf g (g m) := by
    ext k; simp [cOf, map_sum]
  rw [this]
  simp only [cOf_g g hG]
  ext k; simp [Pi.single_apply]

theorem gram_cOf (g : ι → S.V) (hG : IsUnit (gramOf g).det) (v : S.V) :
    (gramOf g) *ᵥ cOf g v = fun l => S.hT (g l) v := by
  rw [cOf_eq, Matrix.mulVec_mulVec, mul_nonsing_inv _ hG, Matrix.one_mulVec]

def sL (g : ι → S.V) (X : Matrix ι ι E) : S.V →ₗ[E] S.V :=
  LinearMap.id + ∑ m, ∑ k, ((X - 1) m k) • (coordL g k).smulRight (g m)

theorem sL_apply (g : ι → S.V) (X : Matrix ι ι E) (v : S.V) :
    sL g X v = v + ∑ m, ((X - 1) *ᵥ cOf g v) m • g m := by
  simp only [sL, LinearMap.add_apply, LinearMap.id_apply, LinearMap.sum_apply, LinearMap.smul_apply,
    LinearMap.smulRight_apply]
  congr 1
  refine Finset.sum_congr rfl fun m _ => ?_
  simp only [Matrix.mulVec, dotProduct, Finset.sum_smul, smul_smul, cOf]

theorem cOf_sL (g : ι → S.V) (hG : IsUnit (gramOf g).det) (X : Matrix ι ι E) (v : S.V) :
    cOf g (sL g X v) = X *ᵥ cOf g v := by
  rw [sL_apply, cOf_comb g hG, Matrix.sub_mulVec, Matrix.one_mulVec]; abel

theorem sL_comp (g : ι → S.V) (hG : IsUnit (gramOf g).det) (X Y : Matrix ι ι E) (v : S.V) :
    sL g X (sL g Y v) = sL g (X * Y) v := by
  rw [sL_apply g X, cOf_sL g hG, sL_apply g Y, sL_apply g (X * Y), add_assoc, ← Finset.sum_add_distrib]
  congr 1
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [← add_smul]
  congr 1
  simp only [Matrix.sub_mul, Matrix.one_mul, Matrix.sub_mulVec, Matrix.one_mulVec, Matrix.mulVec_mulVec, Pi.sub_apply]
  ring

theorem sL_one (g : ι → S.V) (v : S.V) : sL g 1 v = v := by
  rw [sL_apply]; simp

def sE (g : ι → S.V) (hG : IsUnit (gramOf g).det) (X Y : Matrix ι ι E) (hXY : X * Y = 1) (hYX : Y * X = 1) :
    S.V ≃ₗ[E] S.V :=
  LinearEquiv.ofLinearMap (sL g X) (sL g Y)
    (by ext v; simp only [LinearMap.comp_apply, LinearMap.id_apply]; rw [sL_comp g hG, hXY, sL_one])
    (by ext v; simp only [LinearMap.comp_apply, LinearMap.id_apply]; rw [sL_comp g hG, hYX, sL_one])

theorem gram_herm (g : ι → S.V) (k l : ι) : star (gramOf g k l) = gramOf g l k := by
  have := S.herm.eq (g k) (g l)
  simpa [gramOf, starRingEnd_apply] using this

theorem hT_comb (g : ι → S.V) (hG : IsUnit (gramOf g).det) (x y : S.V) (α β : ι → E) :
    S.hT (x + ∑ m, α m • g m) (y + ∑ n, β n • g n) =
      S.hT x y + star (cOf g x) ⬝ᵥ ((gramOf g) *ᵥ β) + star α ⬝ᵥ ((gramOf g) *ᵥ cOf g y) +
        star α ⬝ᵥ ((gramOf g) *ᵥ β) := by
  have h1 : ∀ n, S.hT (g n) y = ((gramOf g) *ᵥ cOf g y) n := fun n => by rw [gram_cOf g hG]
  have h2 : ∀ n, S.hT x (g n) = star (((gramOf g) *ᵥ cOf g x) n) := fun n => by
    rw [gram_cOf g hG]
    have := S.herm.eq (g n) x
    simpa [starRingEnd_apply] using this.symm
  rw [map_add (f := _), map_add (f := _), LinearMap.add_apply, LinearMap.add_apply]
  have hxB : S.hT x (∑ n, β n • g n) = star (cOf g x) ⬝ᵥ ((gramOf g) *ᵥ β) := by
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [map_sum, LinearMap.map_smul, smul_eq_mul, h2]
    simp only [Matrix.mulVec, dotProduct, star_sum, star_mul', Pi.star_apply, Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun n _ => ?_
    rw [← gram_herm g n k]; ring
  have hAy : S.hT (∑ m, α m • g m) y = star α ⬝ᵥ ((gramOf g) *ᵥ cOf g y) := by
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [map_sum, LinearMap.sum_apply, LinearMap.map_smulₛₗ, LinearMap.smul_apply, smul_eq_mul,
      starRingEnd_apply, h1]
    simp [dotProduct]
  have hAB : S.hT (∑ m, α m • g m) (∑ n, β n • g n) = star α ⬝ᵥ ((gramOf g) *ᵥ β) := by
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [map_sum, LinearMap.sum_apply, LinearMap.map_smulₛₗ, LinearMap.smul_apply, smul_eq_mul,
      starRingEnd_apply, dotProduct, Matrix.mulVec, Pi.star_apply, gramOf, Finset.mul_sum, RingHom.id_apply]
    refine Finset.sum_comm.trans (Finset.sum_congr rfl fun m _ => Finset.sum_congr rfl fun n _ => ?_)
    ring
  rw [hxB, hAy, hAB]
  ring

theorem sL_isom (g : ι → S.V) (hG : IsUnit (gramOf g).det) (X : Matrix ι ι E)
    (hX : X.conjTranspose * gramOf g * X = gramOf g) (x y : S.V) :
    S.hT (sL g X x) (sL g X y) = S.hT x y := by
  rw [sL_apply, sL_apply, hT_comb g hG]
  set p := cOf g x
  set q := cOf g y
  have key : star (X *ᵥ p) ⬝ᵥ ((gramOf g) *ᵥ (X *ᵥ q)) = star p ⬝ᵥ ((gramOf g) *ᵥ q) := by
    rw [Matrix.star_mulVec, ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, hX]
  simp only [Matrix.sub_mulVec, Matrix.one_mulVec, Matrix.mulVec_sub, dotProduct_sub,
    sub_dotProduct, star_sub]
  rw [key]
  ring

end Formalism.L2.SG.Pf.StabilizerIndexVolumes
end
end

