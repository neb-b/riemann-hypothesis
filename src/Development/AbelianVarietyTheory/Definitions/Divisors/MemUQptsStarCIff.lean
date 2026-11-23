module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0009

@[expose] public section

noncomputable section

open NumberField
open scoped TensorProduct

namespace GlobalTheory.UPel.HT

variable {p : ℕ} [Fact p.Prime] (D : Datum p)

abbrev Datum.VQ : Type := ℚ ⊗[ℤ] D.La

instance Datum.finVQ : FiniteDimensional ℚ D.VQ := by
  haveI := D.finLa; infer_instance

def Datum.actQ : D.O →+* Module.End ℚ D.VQ :=
  (Module.End.baseChangeHom ℤ ℚ D.La).toRingHom.comp (Module.toModuleEnd ℤ (S := D.O) D.La)

theorem Datum.actQ_tmul (b : D.O) (q : ℚ) (x : D.La) : D.actQ b (q ⊗ₜ x) = q ⊗ₜ (b • x) := rfl

def Datum.EFQ : LinearMap.BilinForm ℚ D.VQ := D.EF.baseChange ℚ

theorem Datum.EFQ_tmul (q q' : ℚ) (x y : D.La) : D.EFQ (q ⊗ₜ x) (q' ⊗ₜ y) = (D.EF x y : ℚ) * (q * q') := by
  simp [Datum.EFQ, LinearMap.BilinForm.baseChange_tmul, mul_comm]

theorem Datum.EFQ_swap (x y : D.VQ) : D.EFQ y x = - D.EFQ x y := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | add x x' h h' => simp only [map_add (f := _), LinearMap.add_apply, h, h']; ring
  | tmul q x =>
    induction y using TensorProduct.induction_on with
    | zero => simp
    | add y y' h h' => simp only [map_add (f := _), LinearMap.add_apply, h, h']; ring
    | tmul q' y => rw [D.EFQ_tmul, D.EFQ_tmul, D.EF_swap x y]; push_cast; ring

theorem Datum.EFQ_actQ (b : D.O) (x y : D.VQ) : D.EFQ (D.actQ b x) y = D.EFQ x (D.actQ (D.star b).unop y) := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | add x x' h h' => simp only [map_add (f := _), LinearMap.add_apply, h, h']
  | tmul q x =>
    induction y using TensorProduct.induction_on with
    | zero => simp
    | add y y' h h' => simp only [map_add (f := _), h, h']
    | tmul q' y => rw [D.actQ_tmul, D.actQ_tmul, D.EFQ_tmul, D.EFQ_tmul, D.adj]

theorem Datum.exists_tmul (v : D.VQ) : ∃ (q : ℚ) (x : D.La), q ≠ 0 ∧ v = q ⊗ₜ x := by
  induction v using TensorProduct.induction_on with
  | zero => exact ⟨1, 0, one_ne_zero, by simp⟩
  | tmul q x =>
    by_cases h : q = 0
    · exact ⟨1, 0, one_ne_zero, by simp [h]⟩
    · exact ⟨q, x, h, rfl⟩
  | add v v' h h' =>
    obtain ⟨q, x, -, rfl⟩ := h
    obtain ⟨q', x', -, rfl⟩ := h'
    have hd : (q.den : ℚ) ≠ 0 := by exact_mod_cast q.den_ne_zero
    have hd' : (q'.den : ℚ) ≠ 0 := by exact_mod_cast q'.den_ne_zero
    refine ⟨1 / (q.den * q'.den), (q.num * q'.den : ℤ) • x + (q'.num * q.den : ℤ) • x', by positivity, ?_⟩
    rw [TensorProduct.tmul_add, ← TensorProduct.smul_tmul, ← TensorProduct.smul_tmul]
    congr 2
    · rw [zsmul_eq_mul]; push_cast; conv_lhs => rw [← Rat.num_div_den q]
      field_simp
    · rw [zsmul_eq_mul]; push_cast; conv_lhs => rw [← Rat.num_div_den q']
      field_simp

theorem Datum.eq_zero_of_EFQ {v : D.VQ} (h : ∀ w, D.EFQ v w = 0) : v = 0 := by
  obtain ⟨q, x, hq, rfl⟩ := D.exists_tmul v
  have hx : D.EF x = D.EF 0 := by
    ext y
    have := h (1 ⊗ₜ y)
    rw [D.EFQ_tmul, mul_one] at this
    have h2 : (D.EF x y : ℚ) = 0 := (mul_eq_zero.1 this).resolve_right hq
    simpa using h2
  rw [D.nondeg hx, TensorProduct.tmul_zero]

theorem Datum.EFQ_nondeg : D.EFQ.Nondegenerate :=
  ⟨fun _ h => D.eq_zero_of_EFQ h, fun v h => D.eq_zero_of_EFQ fun w => by rw [D.EFQ_swap, h, neg_zero]⟩

def Datum.adjE (g : Module.End ℚ D.VQ) : Module.End ℚ D.VQ := D.EFQ.leftAdjointOfNondegenerate D.EFQ_nondeg g

theorem Datum.EFQ_adjE_left (g : Module.End ℚ D.VQ) (x y : D.VQ) : D.EFQ (D.adjE g x) y = D.EFQ x (g y) :=
  D.EFQ.isAdjointPairLeftAdjointOfNondegenerate D.EFQ_nondeg g x y

theorem Datum.EFQ_adjE_right (g : Module.End ℚ D.VQ) (x y : D.VQ) : D.EFQ (g x) y = D.EFQ x (D.adjE g y) := by
  rw [D.EFQ_swap y, D.EFQ_swap (D.adjE g y), D.EFQ_adjE_left]

theorem Datum.end_ext {g h : Module.End ℚ D.VQ} (H : ∀ x y, D.EFQ (g x) y = D.EFQ (h x) y) : g = h := by
  refine LinearMap.ext fun x => sub_eq_zero.1 (D.eq_zero_of_EFQ fun y => ?_)
  rw [map_sub, LinearMap.sub_apply, H, sub_self]

theorem Datum.adjE_adjE (g : Module.End ℚ D.VQ) : D.adjE (D.adjE g) = g :=
  D.end_ext fun x y => by rw [D.EFQ_adjE_left, D.EFQ_adjE_right]

theorem Datum.adjE_mul (g h : Module.End ℚ D.VQ) : D.adjE (g * h) = D.adjE h * D.adjE g :=
  D.end_ext fun x y => by simp only [D.EFQ_adjE_left, Module.End.mul_apply]

theorem Datum.adjE_smul (q : ℚ) (g : Module.End ℚ D.VQ) : D.adjE (q • g) = q • D.adjE g :=
  D.end_ext fun x y => by simp only [D.EFQ_adjE_left, LinearMap.smul_apply, map_smul]

theorem Datum.adjE_one : D.adjE 1 = 1 :=
  D.end_ext fun x y => by simp only [D.EFQ_adjE_left, Module.End.one_apply]

theorem Datum.adjE_actQ (b : D.O) : D.adjE (D.actQ b) = D.actQ (D.star b).unop :=
  D.end_ext fun x y => by rw [D.EFQ_adjE_left, D.EFQ_actQ, D.star_star]

def Datum.endO : Subalgebra ℚ (Module.End ℚ D.VQ) := Subalgebra.centralizer ℚ (Set.range D.actQ)

theorem Datum.mem_endO {g : Module.End ℚ D.VQ} : g ∈ D.endO ↔ ∀ b, D.actQ b * g = g * D.actQ b := by
  simp [Datum.endO, Subalgebra.mem_centralizer_iff]

def Datum.actInt : 𝓞 D.F →+* D.endO :=
  (D.actQ.comp (algebraMap (𝓞 D.F) D.O)).codRestrict D.endO fun c => D.mem_endO.2 fun b => by
    rw [RingHom.comp_apply, ← map_mul, ← map_mul, Algebra.commutes]

theorem Datum.coe_actInt (c : 𝓞 D.F) : (D.actInt c : Module.End ℚ D.VQ) = D.actQ (algebraMap (𝓞 D.F) D.O c) := rfl

def Datum.actFL : D.F →ₗ[ℚ] D.endO :=
  (integralBasis D.F).constr ℚ fun i => D.actInt (RingOfIntegers.basis D.F i)

theorem Datum.actFL_coe (c : 𝓞 D.F) : D.actFL (c : D.F) = D.actInt c := by
  have h : (D.actFL.restrictScalars ℤ).comp (algebraMap (𝓞 D.F) D.F).toIntAlgHom.toLinearMap =
      D.actInt.toIntAlgHom.toLinearMap := by
    refine (RingOfIntegers.basis D.F).ext fun i => ?_
    show D.actFL (algebraMap (𝓞 D.F) D.F (RingOfIntegers.basis D.F i)) = D.actInt _
    rw [← integralBasis_apply, Datum.actFL, Module.Basis.constr_basis]
  exact LinearMap.congr_fun h c

def Datum.actF : D.F →ₐ[ℚ] D.endO :=
  AlgHom.ofLinearMap D.actFL (by simpa using D.actFL_coe 1) (by
    refine (LinearMap.map_mul_iff D.actFL).2 ?_
    refine (integralBasis D.F).ext fun i => (integralBasis D.F).ext fun j => ?_
    show D.actFL (integralBasis D.F i * integralBasis D.F j) = D.actFL (integralBasis D.F i) * D.actFL (integralBasis D.F j)
    rw [integralBasis_apply, integralBasis_apply, ← map_mul]
    exact (D.actFL_coe _).trans ((map_mul _ _ _).trans (by rw [← D.actFL_coe, ← D.actFL_coe])))

theorem Datum.actF_coe (c : 𝓞 D.F) : D.actF (c : D.F) = D.actInt c := D.actFL_coe c

end GlobalTheory.UPel.HT
