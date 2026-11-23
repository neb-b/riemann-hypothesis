module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0098
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0011
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0005
public import Development.AbelianVarietyTheory.Definitions.Divisors.TCoefMInMMul
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0017
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0115
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorsionBySetPowFreeOfCardPowNumberField

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SqMulFinrankMatrixAlgebraHomEqFinrankMul
section
open scoped TensorProduct

noncomputable section

namespace GlobalTheory.MatCount

open Matrix Module

variable {k : Type} [Field k] {n : ℕ}

section
variable {X : Type} [AddCommGroup X] [Module k X]
  (ρ : Matrix (Fin (n+1)) (Fin (n+1)) k →ₐ[k] Module.End k X)

theorem unit_mul (i j l p : Fin (n+1)) (x : X) :
    ρ (single i j 1) (ρ (single l p 1) x) = if j = l then ρ (single i p 1) x else 0 := by
  rw [← Module.End.mul_apply, ← map_mul]
  split_ifs with h
  · subst h; rw [single_mul_single_same, mul_one]
  · rw [single_mul_single_of_ne (h := h), map_zero, LinearMap.zero_apply]

theorem recon (x : X) : ∑ i, ρ (single i 0 1) (ρ (single 0 i 1) x) = x := by
  simp only [unit_mul, if_true]
  set_option synthInstance.maxHeartbeats 100000 in
    rw [← LinearMap.sum_apply, ← map_sum, sum_single_one, map_one, Module.End.one_apply]

abbrev corner : Submodule k X := LinearMap.range (ρ (single 0 0 1))

theorem unit_mem_corner (i : Fin (n+1)) (x : X) : ρ (single 0 i 1) x ∈ corner ρ :=
  ⟨ρ (single 0 i 1) x, by rw [unit_mul]; simp⟩

theorem unit_corner (v : corner ρ) (i : Fin (n+1)) :
    ρ (single 0 i 1) (v : X) = if i = 0 then (v : X) else 0 := by
  obtain ⟨y, hy⟩ := v.2
  rw [← hy, unit_mul]

def cut (i : Fin (n+1)) : X →ₗ[k] corner ρ :=
  (ρ (single 0 i 1)).codRestrict (corner ρ) (unit_mem_corner ρ i)

@[simp] theorem cut_coe (i : Fin (n+1)) (x : X) : ((cut ρ i x : corner ρ) : X) = ρ (single 0 i 1) x := rfl

theorem cut_unit (i l p : Fin (n+1)) (x : X) :
    cut ρ i (ρ (single l p 1) x) = if i = l then cut ρ p x else 0 := by
  apply Subtype.ext
  rw [cut_coe, unit_mul]
  split_ifs <;> simp

theorem cut_corner (i : Fin (n+1)) (v : corner ρ) : cut ρ i v = if i = 0 then v else 0 := by
  apply Subtype.ext
  rw [cut_coe, unit_corner]
  split_ifs <;> simp

def piEquiv : X ≃ₗ[k] (Fin (n+1) → corner ρ) :=
  LinearEquiv.ofLinear (LinearMap.pi fun i => cut ρ i)
    (∑ i, ρ (single i 0 1) ∘ₗ (corner ρ).subtype ∘ₗ LinearMap.proj i)
    (by
      refine LinearMap.ext fun v => funext fun j => ?_
      set_option synthInstance.maxHeartbeats 100000 in
        simp only [LinearMap.comp_apply, LinearMap.pi_apply, LinearMap.sum_apply, map_sum,
        Submodule.subtype_apply, LinearMap.proj_apply, cut_unit, Finset.sum_ite_eq, Finset.mem_univ,
        if_true, cut_corner, LinearMap.id_apply])
    (by
      refine LinearMap.ext fun x => ?_
      simp only [LinearMap.comp_apply, LinearMap.pi_apply, LinearMap.sum_apply,
        cut_coe, Submodule.subtype_apply, LinearMap.proj_apply, LinearMap.id_apply]
      exact recon ρ x)

theorem finrank_eq [FiniteDimensional k X] : finrank k X = (n+1) * finrank k (corner ρ) := by
  rw [(piEquiv ρ).finrank_eq, Module.finrank_pi_fintype]
  simp
end

section
variable {X Y : Type} [AddCommGroup X] [Module k X] [AddCommGroup Y] [Module k Y]
  (ρX : Matrix (Fin (n+1)) (Fin (n+1)) k →ₐ[k] Module.End k X)
  (ρY : Matrix (Fin (n+1)) (Fin (n+1)) k →ₐ[k] Module.End k Y)

theorem comm {T : X →ₗ[k] Y} (hT : T ∈ GlobalTheory.HTRho.homO ρX.toRingHom ρY.toRingHom) (a : Matrix (Fin (n+1)) (Fin (n+1)) k)
    (x : X) : T (ρX a x) = ρY a (T x) :=
  (GlobalTheory.HTRho.mem_homO _ _ T).1 hT a x

theorem maps_corner (T : GlobalTheory.HTRho.homO ρX.toRingHom ρY.toRingHom) :
    ∀ x ∈ corner ρX, (T : X →ₗ[k] Y) x ∈ corner ρY := by
  rintro _ ⟨y, rfl⟩
  exact ⟨(T : X →ₗ[k] Y) y, (comm ρX ρY T.2 _ y).symm⟩

def restr : GlobalTheory.HTRho.homO ρX.toRingHom ρY.toRingHom →ₗ[k] (corner ρX →ₗ[k] corner ρY) where
  toFun T := (T : X →ₗ[k] Y).restrict (maps_corner ρX ρY T)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

@[simp] theorem restr_coe (T : GlobalTheory.HTRho.homO ρX.toRingHom ρY.toRingHom) (v : corner ρX) :
    ((restr ρX ρY T v : corner ρY) : Y) = (T : X →ₗ[k] Y) v := rfl

def ext (S : corner ρX →ₗ[k] corner ρY) : X →ₗ[k] Y :=
  ∑ i, ρY (single i 0 1) ∘ₗ (corner ρY).subtype ∘ₗ S ∘ₗ cut ρX i

theorem ext_apply (S : corner ρX →ₗ[k] corner ρY) (x : X) :
    ext ρX ρY S x = ∑ i, ρY (single i 0 1) (S (cut ρX i x)) := by
  simp [ext, LinearMap.sum_apply]

theorem ext_unit (S : corner ρX →ₗ[k] corner ρY) (l p : Fin (n+1)) (x : X) :
    ext ρX ρY S (ρX (single l p 1) x) = ρY (single l p 1) (ext ρX ρY S x) := by
  set_option synthInstance.maxHeartbeats 100000 in
    rw [ext_apply, ext_apply, map_sum]
  simp only [cut_unit, unit_mul]
  rw [Finset.sum_ite_eq]
  simp only [Finset.mem_univ, if_true]
  rw [Finset.sum_eq_single l (fun b _ hb => by rw [if_neg hb, map_zero, Submodule.coe_zero, map_zero])
    (by simp)]
  simp

theorem ext_mem (S : corner ρX →ₗ[k] corner ρY) :
    ext ρX ρY S ∈ GlobalTheory.HTRho.homO ρX.toRingHom ρY.toRingHom := by
  rw [GlobalTheory.HTRho.mem_homO]
  intro a x
  change ext ρX ρY S (ρX a x) = ρY a (ext ρX ρY S x)
  have ha : a = ∑ l, ∑ p, a l p • single l p (1 : k) := by
    conv_lhs => rw [matrix_eq_sum_single a]
    simp only [smul_single, smul_eq_mul, mul_one]
  rw [ha]
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [map_sum, map_smul, LinearMap.sum_apply, LinearMap.smul_apply, ext_unit]

theorem restr_bij : Function.Bijective (restr ρX ρY) := by
  constructor
  · refine (injective_iff_map_eq_zero _).2 fun T hT => ?_
    apply Subtype.ext
    refine LinearMap.ext fun x => ?_
    have h0 : ∀ i, (T : X →ₗ[k] Y) (ρX (single 0 i 1) x) = 0 := fun i => by
      exact (congrArg Subtype.val (LinearMap.congr_fun hT ⟨_, unit_mem_corner ρX i x⟩) :)
    change (T : X →ₗ[k] Y) x = 0
    set_option synthInstance.maxHeartbeats 100000 in
      rw [← recon ρX x, map_sum]
    refine Finset.sum_eq_zero fun i _ => ?_
    rw [comm ρX ρY T.2, h0, map_zero]
  · intro S
    refine ⟨⟨ext ρX ρY S, ext_mem ρX ρY S⟩, LinearMap.ext fun v => Subtype.ext ?_⟩
    rw [restr_coe]
    change ext ρX ρY S v = _
    rw [ext_apply]
    simp only [cut_corner]
    rw [Finset.sum_eq_single 0 (fun b _ hb => by rw [if_neg hb, map_zero, Submodule.coe_zero, map_zero])
      (by simp)]
    simp [unit_corner]

theorem finrank_homO [FiniteDimensional k X] [FiniteDimensional k Y] :
    finrank k (GlobalTheory.HTRho.homO ρX.toRingHom ρY.toRingHom) = finrank k (corner ρX) * finrank k (corner ρY) := by
  rw [(LinearEquiv.ofBijective _ (restr_bij ρX ρY)).finrank_eq, Module.finrank_linearMap]
end

theorem count : ∀ (k : Type) [Field k] (m : ℕ) (X Y : Type) [AddCommGroup X] [Module k X] [FiniteDimensional k X]
    [AddCommGroup Y] [Module k Y] [FiniteDimensional k Y]
    (ρX : Matrix (Fin m) (Fin m) k →ₐ[k] Module.End k X) (ρY : Matrix (Fin m) (Fin m) k →ₐ[k] Module.End k Y),
    m ^ 2 * Module.finrank k (GlobalTheory.HTRho.homO ρX.toRingHom ρY.toRingHom) = Module.finrank k X * Module.finrank k Y := by
  intro k _ m X Y _ _ _ _ _ _ ρX ρY
  cases m with
  | zero =>
    have hX : Subsingleton X := by
      refine ⟨fun a b => ?_⟩
      have h : (1 : Module.End k X) = 0 := by
        rw [← map_one ρX, ← map_zero ρX]
        congr 1
        ext i
        exact i.elim0
      have ha := congrArg (fun f : Module.End k X => f a) h
      have hb := congrArg (fun f : Module.End k X => f b) h
      simp only [Module.End.one_apply, LinearMap.zero_apply] at ha hb
      rw [ha, hb]
    simp [finrank_zero_of_subsingleton]
  | succ n =>
    rw [finrank_homO, finrank_eq ρX, finrank_eq ρY]
    ring

end GlobalTheory.MatCount
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SteinitzPiIdealsLinearEquivOfClassGroupProd
section
open scoped nonZeroDivisors

namespace GlobalTheory.SteinitzProd

variable {R : Type} [CommRing R] [IsDedekindDomain R]

def coprimeEquiv (I J : Ideal R) (u v : R) (hu : u ∈ I) (hv : v ∈ J) (h : u + v = 1) :
    (I × J) ≃ₗ[R] ((⊤ : Ideal R) × (I * J : Ideal R)) where
  toFun p := (⟨p.1 + p.2, Submodule.mem_top⟩,
    ⟨v * p.1 - u * p.2, Ideal.sub_mem _ (mul_comm (p.1 : R) v ▸ Ideal.mul_mem_mul p.1.2 hv)
      (Ideal.mul_mem_mul hu p.2.2)⟩)
  invFun q := (⟨u * q.1 + q.2, add_mem (Ideal.mul_mem_right _ I hu)
      ((Ideal.mul_le_left (I := I) (J := J)) q.2.2)⟩,
    ⟨v * q.1 - q.2, Ideal.sub_mem _ (Ideal.mul_mem_right _ J hv)
      ((Ideal.mul_le_right (I := I) (J := J)) q.2.2)⟩)
  map_add' p q := by
    ext <;> simp <;> ring
  map_smul' c p := by
    ext <;> simp <;> ring
  left_inv p := by
    ext
    · simp only; linear_combination (p.1 : R) * h
    · simp only; linear_combination (p.2 : R) * h
  right_inv q := by
    ext
    · simp only; linear_combination (q.1 : R) * h
    · simp only; linear_combination (q.2 : R) * h

theorem classGroup_exists_integral_ideal_coprime {m : Ideal R} (hm : m ≠ ⊥) (c : ClassGroup R) :
    ∃ I : (Ideal R)⁰, (I : Ideal R) ⊔ m = ⊤ ∧ ClassGroup.mk0 I = c := by
  by_cases ht : m = ⊤
  · obtain ⟨I, hI⟩ := ClassGroup.mk0_surjective c
    exact ⟨I, by rw [ht, sup_top_eq], hI⟩
  obtain ⟨J, hJ⟩ := ClassGroup.mk0_surjective c⁻¹
  have hJ0 : (J : Ideal R) ≠ 0 := nonZeroDivisors.coe_ne_zero J
  obtain ⟨a, ha⟩ := IsDedekindDomain.exists_sup_span_eq (I := (J : Ideal R) * m) (J := J)
    Ideal.mul_le_left (mul_ne_zero hJ0 hm)
  obtain ⟨M, hM⟩ : (J : Ideal R) ∣ Ideal.span {a} := Ideal.dvd_iff_le.2 (ha ▸ le_sup_right)
  have h1 : m ⊔ M = ⊤ := by
    apply mul_left_cancel₀ hJ0
    rw [Ideal.mul_sup, ← hM, ha, Ideal.mul_top]
  have hM0 : M ≠ 0 := by
    rintro rfl
    exact ht (by simpa using h1)
  refine ⟨⟨M, mem_nonZeroDivisors_of_ne_zero hM0⟩, by rw [sup_comm]; exact h1, ?_⟩
  have ha0 : a ≠ 0 := by
    rintro rfl
    exact mul_ne_zero hJ0 hM0 (by simpa using hM.symm)
  rw [← inv_inv c, ← hJ, ClassGroup.mk0_eq_mk0_inv_iff]
  exact ⟨a, ha0, by rw [hM, mul_comm]⟩

theorem exists_prod_equiv (I J : (Ideal R)⁰) :
    ∃ L : (Ideal R)⁰, ClassGroup.mk0 L = ClassGroup.mk0 I * ClassGroup.mk0 J ∧
      Nonempty ((↥(I : Ideal R) × ↥(J : Ideal R)) ≃ₗ[R] (R × ↥(L : Ideal R))) := by
  have hJ0 : (J : Ideal R) ≠ ⊥ := by simpa using nonZeroDivisors.coe_ne_zero J
  obtain ⟨I', hcop, hcl⟩ := classGroup_exists_integral_ideal_coprime hJ0 (ClassGroup.mk0 I)
  have h1 : (1 : R) ∈ (I' : Ideal R) ⊔ J := by rw [hcop]; exact Submodule.mem_top
  obtain ⟨u, hu, v, hv, huv⟩ := Submodule.mem_sup.1 h1
  refine ⟨I' * J, by rw [map_mul, hcl], ⟨?_⟩⟩
  have e1 := (GlobalTheory.ProjModFinIso.nonempty_equiv_of_mk0_eq hcl.symm).some
  exact (e1.prodCongr (LinearEquiv.refl R _)) ≪≫ₗ coprimeEquiv _ _ u v hu hv huv ≪≫ₗ
    (Submodule.topEquiv.prodCongr (LinearEquiv.ofEq _ _ (Submonoid.coe_mul _ _ _).symm))

theorem exists_prod_pi_equiv (n : ℕ) : ∀ (I : Fin n → (Ideal R)⁰) (K : (Ideal R)⁰),
    ∃ L : (Ideal R)⁰, ClassGroup.mk0 L = ClassGroup.mk0 K * ∏ i, ClassGroup.mk0 (I i) ∧
      Nonempty ((↥(K : Ideal R) × ((i : Fin n) → ↥(I i : Ideal R))) ≃ₗ[R]
        (↥(L : Ideal R) × (Fin n → R))) := by
  induction n with
  | zero =>
    intro I K
    exact ⟨K, by simp, ⟨(LinearEquiv.refl R _).prodCongr (LinearEquiv.ofSubsingleton _ _)⟩⟩
  | succ n ih =>
    intro I K
    obtain ⟨L₁, hL₁, ⟨e₁⟩⟩ := exists_prod_equiv K (I 0)
    obtain ⟨L, hL, ⟨e₂⟩⟩ := ih (fun i => I i.succ) L₁
    refine ⟨L, by rw [hL, hL₁, Fin.prod_univ_succ, mul_assoc], ⟨?_⟩⟩
    exact (LinearEquiv.refl R _).prodCongr (Fin.consLinearEquiv R (fun i => ↥(I i : Ideal R))).symm ≪≫ₗ
      (LinearEquiv.prodAssoc R _ _ _).symm ≪≫ₗ e₁.prodCongr (LinearEquiv.refl R _) ≪≫ₗ
      LinearEquiv.prodAssoc R _ _ _ ≪≫ₗ (LinearEquiv.refl R R).prodCongr e₂ ≪≫ₗ
      (LinearEquiv.prodAssoc R _ _ _).symm ≪≫ₗ
      (LinearEquiv.prodComm R _ _).prodCongr (LinearEquiv.refl R _) ≪≫ₗ
      LinearEquiv.prodAssoc R _ _ _ ≪≫ₗ
      (LinearEquiv.refl R _).prodCongr (Fin.consLinearEquiv R (fun _ => R))

theorem exists_pi_equiv {ι : Type} [Fintype ι] {n : ℕ} (e : ι ≃ Fin (n + 1))
    (I : ι → (Ideal R)⁰) :
    ∃ L : (Ideal R)⁰, ClassGroup.mk0 L = ∏ i, ClassGroup.mk0 (I i) ∧
      Nonempty (((i : ι) → ↥(I i : Ideal R)) ≃ₗ[R] (↥(L : Ideal R) × (Fin n → R))) := by
  let I' : Fin (n + 1) → (Ideal R)⁰ := fun j => I (e.symm j)
  obtain ⟨L, hL, ⟨f⟩⟩ := exists_prod_pi_equiv n (fun j => I' j.succ) (I' 0)
  refine ⟨L, ?_, ⟨?_⟩⟩
  · rw [hL, ← Fin.prod_univ_succ (f := fun j => ClassGroup.mk0 (I' j))]
    exact Equiv.prod_comp e.symm (fun i => ClassGroup.mk0 (I i))
  · exact LinearEquiv.piCongrLeft' R (fun i => ↥(I i : Ideal R)) e ≪≫ₗ
      (Fin.consLinearEquiv R (fun j => ↥(I' j : Ideal R))).symm ≪≫ₗ f

theorem steinitz : ∀ (R : Type) [CommRing R] [IsDedekindDomain R] (ι : Type) [Fintype ι]
    (I J : ι → (Ideal R)⁰), ∏ i, ClassGroup.mk0 (I i) = ∏ i, ClassGroup.mk0 (J i) →
    Nonempty (((i : ι) → (I i : Ideal R)) ≃ₗ[R] ((i : ι) → (J i : Ideal R))) := by
  intro R _ _ ι _ I J h
  rcases isEmpty_or_nonempty ι with hι | hι
  · exact ⟨LinearEquiv.ofSubsingleton _ _⟩
  obtain ⟨n, hn⟩ := Nat.exists_eq_succ_of_ne_zero (Fintype.card_ne_zero (α := ι))
  let e : ι ≃ Fin (n + 1) := (Fintype.equivFin ι).trans (finCongr hn)
  obtain ⟨L, hL, ⟨f⟩⟩ := exists_pi_equiv e I
  obtain ⟨L', hL', ⟨f'⟩⟩ := exists_pi_equiv e J
  obtain ⟨g⟩ := GlobalTheory.ProjModFinIso.nonempty_equiv_of_mk0_eq (R := R) (I := L) (J := L')
    (by rw [hL, hL', h])
  exact ⟨f ≪≫ₗ g.prodCongr (LinearEquiv.refl R _) ≪≫ₗ f'.symm⟩

end GlobalTheory.SteinitzProd
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SumLogDivPredLeReal
section
open scoped BigOperators Matrix
open Polynomial

namespace GlobalTheory.PrimeLogSum


open scoped BigOperators Matrix in
open Polynomial in
theorem _root_.GlobalTheory.PrimeLogSum.sum_log_div_pred_le_real : ∀ (B : ℝ), 1 ≤ B →
    ∑ p ∈ (Finset.range (⌊B⌋₊ + 1)).filter Nat.Prime, Real.log p / ((p : ℝ) - 1)
      ≤ Real.log B + 3 := by
  intro B hB
  have h := _root_.GlobalTheory.PrimeLogSum.sum_log_div_pred_le ⌊B⌋₊
  have hN : (1 : ℝ) ≤ (⌊B⌋₊ : ℝ) := by
    have : 1 ≤ ⌊B⌋₊ := Nat.le_floor (by exact_mod_cast hB)
    exact_mod_cast this
  have hle : ((⌊B⌋₊ : ℕ) : ℝ) ≤ B := Nat.floor_le (by linarith)
  have hlog : Real.log (⌊B⌋₊ : ℝ) ≤ Real.log B :=
    Real.log_le_log (by linarith) hle
  linarith

end GlobalTheory.PrimeLogSum
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SumPrimesInvPredLeLoglog
section
namespace GlobalTheory.PrimeRecipSum
open Finset

theorem sum_inv_pred_small (y : ℕ) (hy : y ≤ 8) :
    ∑ p ∈ (range (y + 1)).filter Nat.Prime, 1 / ((p : ℝ) - 1) ≤ 23 / 12 := by
  have hsub : (range (y + 1)).filter Nat.Prime ⊆ (range 9).filter Nat.Prime := by
    intro p hp
    simp only [mem_filter, mem_range] at hp ⊢
    exact ⟨by omega, hp.2⟩
  have hnn : ∀ p ∈ (range 9).filter Nat.Prime, p ∉ (range (y + 1)).filter Nat.Prime →
      (0:ℝ) ≤ 1 / ((p : ℝ) - 1) := by
    intro p hp _
    have h2 : (2:ℝ) ≤ p := by exact_mod_cast (mem_filter.1 hp).2.two_le
    exact div_nonneg (by norm_num) (by linarith)
  refine (sum_le_sum_of_subset_of_nonneg hsub hnn).trans ?_
  have e : (range 9).filter Nat.Prime = {2, 3, 5, 7} := by decide
  rw [e]
  norm_num

theorem inv_pred_le_of_sqrt_lt (y s p : ℕ) (hy : 2 ≤ y) (hs : y < (s + 1) * (s + 1))
    (hp : Nat.Prime p) (hps : s < p) :
    1 / ((p : ℝ) - 1) ≤ 2 / Real.log y * (Real.log p / ((p : ℝ) - 1)) := by
  have hp2 : (2:ℝ) ≤ p := by exact_mod_cast hp.two_le
  have ha : (0:ℝ) < (p:ℝ) - 1 := by linarith
  have hl : 0 < Real.log (y:ℝ) := Real.log_pos (by exact_mod_cast (by omega : 1 < y))
  have hyp : y ≤ p ^ 2 := by
    have := Nat.mul_le_mul (show s + 1 ≤ p from hps) (show s + 1 ≤ p from hps)
    rw [sq]; omega
  have hy' : (y:ℝ) ≤ (p:ℝ) ^ 2 := by exact_mod_cast hyp
  have hL : Real.log y ≤ 2 * Real.log p := by
    have := Real.log_le_log (by positivity) hy'
    rw [Real.log_pow] at this
    push_cast at this
    exact this
  rw [div_mul_div_comm, div_le_div_iff₀ ha (by positivity)]
  nlinarith [mul_le_mul_of_nonneg_right hL ha.le]

theorem sum_inv_pred_le : ∀ y : ℕ, 3 ≤ y →
    ∑ p ∈ (Finset.range (y + 1)).filter Nat.Prime, 1 / ((p : ℝ) - 1)
      ≤ 7 * Real.log (Real.log y) + 6 := by
  intro y
  induction y using Nat.strong_induction_on with
  | _ y ih =>
  intro hy3
  have hy3' : (3:ℝ) ≤ y := by exact_mod_cast hy3
  have hl1 : 1 ≤ Real.log (y:ℝ) := by
    have he := Real.exp_one_lt_d9
    have := Real.log_le_log (Real.exp_pos 1) (by linarith : Real.exp 1 ≤ y)
    rwa [Real.log_exp] at this
  have hll : 0 ≤ Real.log (Real.log y) := Real.log_nonneg hl1
  rcases le_or_gt y 8 with hy8 | hy8
  · have := sum_inv_pred_small y hy8
    linarith
  set s := Nat.sqrt y with hs_def
  have hs3 : 3 ≤ s := by rw [hs_def, Nat.le_sqrt]; omega
  have hsy : s < y := Nat.sqrt_lt_self (by omega)
  have hss : s * s ≤ y := Nat.sqrt_le y
  have hys : y < (s + 1) * (s + 1) := Nat.lt_succ_sqrt y
  have ih' := ih s hsy hs3
  have hsplit : ∑ p ∈ (range (y + 1)).filter Nat.Prime, 1 / ((p : ℝ) - 1)
      = ∑ p ∈ (range (s + 1)).filter Nat.Prime, 1 / ((p : ℝ) - 1)
        + ∑ p ∈ ((range (y + 1)).filter Nat.Prime).filter (fun p => ¬ p ≤ s),
            1 / ((p : ℝ) - 1) := by
    rw [← sum_filter_add_sum_filter_not ((range (y + 1)).filter Nat.Prime) (fun p => p ≤ s)]
    congr 1
    apply sum_congr _ (fun _ _ => rfl)
    ext p
    simp only [mem_filter, mem_range]
    exact ⟨fun ⟨⟨_, h2⟩, h3⟩ => ⟨by omega, h2⟩, fun ⟨h1, h2⟩ => ⟨⟨by omega, h2⟩, by omega⟩⟩
  have hl2 : 2 < Real.log (y:ℝ) := by
    have he : Real.exp 2 < 9 := by
      have := Real.exp_one_lt_d9
      have e2 : Real.exp 2 = Real.exp 1 * Real.exp 1 := by rw [← Real.exp_add]; norm_num
      rw [e2]; nlinarith [Real.exp_pos 1]
    have h9 : (9:ℝ) ≤ y := by exact_mod_cast (by omega : 9 ≤ y)
    have := Real.log_lt_log (Real.exp_pos 2) (by linarith : Real.exp 2 < y)
    rwa [Real.log_exp] at this
  have htail : ∑ p ∈ ((range (y + 1)).filter Nat.Prime).filter (fun p => ¬ p ≤ s),
      1 / ((p : ℝ) - 1) ≤ 2 / Real.log y * (Real.log y + 2.2) := by
    have hc : (0:ℝ) ≤ 2 / Real.log y := div_nonneg (by norm_num) (by linarith)
    calc _ ≤ ∑ p ∈ ((range (y + 1)).filter Nat.Prime).filter (fun p => ¬ p ≤ s),
            2 / Real.log y * (Real.log p / ((p : ℝ) - 1)) := by
          apply sum_le_sum
          intro p hp
          simp only [mem_filter, mem_range] at hp
          exact inv_pred_le_of_sqrt_lt y s p (by omega) hys hp.1.2 (by omega)
      _ = 2 / Real.log y * ∑ p ∈ ((range (y + 1)).filter Nat.Prime).filter (fun p => ¬ p ≤ s),
            Real.log p / ((p : ℝ) - 1) := by rw [mul_sum]
      _ ≤ 2 / Real.log y * ∑ p ∈ (range (y + 1)).filter Nat.Prime,
            Real.log p / ((p : ℝ) - 1) := by
          apply mul_le_mul_of_nonneg_left _ hc
          apply sum_le_sum_of_subset_of_nonneg (filter_subset _ _)
          intro p hp _
          have h2 : (2:ℝ) ≤ p := by exact_mod_cast (mem_filter.1 hp).2.two_le
          exact div_nonneg (Real.log_natCast_nonneg p) (by linarith)
      _ ≤ 2 / Real.log y * (Real.log y + 2.2) :=
          mul_le_mul_of_nonneg_left (GlobalTheory.PrimeLogSum.sum_log_div_pred_le y) hc
  have hfrac : 2 / Real.log y * (Real.log y + 2.2) ≤ 4.2 := by
    rw [div_mul_eq_mul_div, div_le_iff₀ (by linarith)]
    linarith
  have hslog : 0 < Real.log (s:ℝ) := Real.log_pos (by exact_mod_cast (by omega : 1 < s))
  have hslog2 : 2 * Real.log (s:ℝ) ≤ Real.log y := by
    have h : ((s:ℝ)) ^ 2 ≤ y := by
      have : s ^ 2 ≤ y := by rw [sq]; exact hss
      exact_mod_cast this
    have hs0 : (0:ℝ) < s := by exact_mod_cast (by omega : 0 < s)
    have := Real.log_le_log (by positivity) h
    rw [Real.log_pow] at this
    push_cast at this
    exact this
  have hlls : Real.log (Real.log s) ≤ Real.log (Real.log y) - Real.log 2 := by
    rw [← Real.log_div (by linarith) (by norm_num)]
    exact Real.log_le_log hslog (by linarith)
  have hlog2 := Real.log_two_gt_d9
  rw [hsplit]
  linarith

end GlobalTheory.PrimeRecipSum
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TDualProd
section
open MvPolynomial GlobalTheory.PsCo.Pc1 GlobalTheory.PsCo.Pc1.A

namespace GlobalTheory.PsCo.Cw2a

theorem t_dual_prod : T_dual_prod := by
  intro A _ _ D L la m J hD hsq
  exact GlobalTheory.dualProd_logDeriv_modSq (K := ℂ) D la m J hD hsq

end GlobalTheory.PsCo.Cw2a
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TendstoRankDivPowOfChooseBoundsStatement
section
open Filter Topology
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.tendsto_div_pow_of_choose_bounds : ∀ (D e δ : ℕ) (r : ℕ → ℕ), 0 < e → (∀ s : ℕ, s < e → ∃ c c' : ℕ, ∀ q : ℕ, δ * (q + D).choose D ≤ r (e * (q + c) + s) ∧ r (e * q + s) ≤ δ * (q + c' + D).choose D) → Tendsto (fun m : ℕ => (r m : ℝ) / (m : ℝ) ^ D) atTop (𝓝 (δ / ((e : ℝ) ^ D * D.factorial))) := by
  first | exact @GlobalTheory.tendsto_rank_div_pow_of_choose_bounds | exact GlobalTheory.tendsto_rank_div_pow_of_choose_bounds | (intros; apply GlobalTheory.tendsto_rank_div_pow_of_choose_bounds <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorsionBySetPowFreeOfCardPowNumberFieldStatement
section
open NumberField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.torsionBySet_pow_free_of_card_pow_numberField : ∀ (F : Type) [Field F] [NumberField F] (M : Type) [AddCommGroup M] [Module (𝓞 F) M] (w0 : Ideal (𝓞 F)) (h r : ℕ), w0.IsMaximal → w0 ≠ ⊥ → (∀ j : ℕ, Nat.card (Submodule.torsionBySet (𝓞 F) M ((w0 ^ j : Ideal (𝓞 F)) : Set (𝓞 F))) = Nat.card (𝓞 F ⧸ w0) ^ (j * h)) → ∃ f : (Fin h → 𝓞 F ⧸ w0 ^ r) →+ M, (∀ (c : 𝓞 F) (a : Fin h → 𝓞 F ⧸ w0 ^ r), f (Ideal.Quotient.mk (w0 ^ r) c • a) = c • f a) ∧ Function.Injective f ∧ ∀ g : M, (∀ c ∈ w0 ^ r, c • g = 0) → ∃ a, f a = g := by
  first | (exact @GlobalTheory.torsionBySet_pow_free_of_natCard) | (exact GlobalTheory.torsionBySet_pow_free_of_natCard) | (intros; apply GlobalTheory.torsionBySet_pow_free_of_natCard  <;> assumption)
end

