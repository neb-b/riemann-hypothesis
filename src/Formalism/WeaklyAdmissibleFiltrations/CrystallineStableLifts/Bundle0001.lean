module

public import Formalism.WeaklyAdmissibleFiltrations.Bundle0001
public import Formalism.CoboundaryTransfers.StatementAPI

@[expose] public section

-- bundled from Formalism.WeaklyAdmissibleFiltrations.CrystallineStableLifts.DPotCrisStableAndExistsPotentiallyCrystallineDat
section
noncomputable section

namespace Formalism.WeaklyAdmissibleFiltrations

open Module TensorProduct

section Top
variable {G : Type} [Group G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]

end Top

section Stable
variable {G : Type} [Group G] {Qp K₀ K K₀' K' : Type} [Field Qp] [Field K₀] [Field K]
    [Field K₀'] [Field K']
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    [Algebra Qp K₀'] [Algebra Qp K'] [Algebra K₀' K'] [IsScalarTower Qp K₀' K']
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra K₀' B] [IsScalarTower Qp K₀' B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    [Algebra K₀' BdR] [Algebra K' BdR] [IsScalarTower Qp K' BdR]
    [IsScalarTower K₀' K' BdR] [IsScalarTower Qp K₀' BdR]
    (PC : PotCrysData G Qp K₀ K K₀' K' B BdR)
    {LL : Type} [Field LL] [Algebra Qp LL]
    {V : Type} [AddCommGroup V] [Module LL V] [Module Qp V] [IsScalarTower Qp LL V]
    (ρ : Representation LL G V)

theorem pc_actVB_mul (PD : PeriodData G Qp K₀ K B BdR) (g h : G) (x : V ⊗[Qp] B) :
    actVB PD ρ (g * h) x = actVB PD ρ g (actVB PD ρ h x) := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul v b => simp [actVB, map_mul, AlgebraTensorModule.map_tmul]
  | add x y hx hy => simp only [map_add (f := _), hx, hy]

theorem pc_actVB_res (h : PC.H) (x : V ⊗[Qp] B) :
    actVB PC.PD' (PC.resH ρ) h x = actVB PC.PD ρ (h : G) x := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul v b => simp [actVB, AlgebraTensorModule.map_tmul, PotCrysData.resH, PC.actB_eq]
  | add x y hx hy => simp only [map_add (f := _), hx, hy]

theorem pc_mem_Dpcris {x : V ⊗[Qp] B} :
    x ∈ PC.Dpcris ρ ↔ ∀ h : PC.H, actVB PC.PD ρ (h : G) x = x := by
  simp only [PotCrysData.Dpcris, Dcris, Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.sub_apply,
    LinearMap.id_apply, sub_eq_zero, pc_actVB_res]

theorem pc_Dpcris_stable (g : G) {x : V ⊗[Qp] B} (hx : x ∈ PC.Dpcris ρ) :
    actVB PC.PD ρ g x ∈ PC.Dpcris ρ := by
  rw [pc_mem_Dpcris] at hx ⊢
  intro h
  have hmem : g⁻¹ * (h : G) * g ∈ PC.H := by
    have := PC.normal.conj_mem (h : G) h.2 g⁻¹
    rwa [inv_inv] at this
  have e : (h : G) * g = g * (g⁻¹ * (h : G) * g) := by group
  rw [← pc_actVB_mul, e, pc_actVB_mul, hx ⟨_, hmem⟩]

end Stable

end Formalism.WeaklyAdmissibleFiltrations
end
end

-- bundled from Formalism.WeaklyAdmissibleFiltrations.CrystallineStableLifts.ExLattice
section
noncomputable section

namespace Formalism.WeaklyAdmissibleFiltrations

theorem existsStableLattice_holds : ExLattice := by
  intro G _ LL _ O _ _ _ hinj
  have hli : LinearIndependent O (fun _ : Unit => (1 : LL)) := by
    rw [Fintype.linearIndependent_iff]
    intro g hg i
    cases i
    simp only [Finset.univ_unique, Finset.sum_singleton, Algebra.smul_def, mul_one] at hg
    exact (map_eq_zero_iff _ hinj).mp (by simpa using hg)
  refine ⟨⟨Submodule.span O (Set.range fun _ : Unit => (1 : LL)), ?_, ?_, ?_, ?_⟩⟩
  · intro g x hx
    simpa using hx
  · exact Submodule.fg_span (Set.finite_range _)
  · exact Module.Free.of_basis (Module.Basis.span hli)
  · rw [eq_top_iff]
    intro x _
    have h1 : (1 : LL) ∈ (Submodule.span O (Set.range fun _ : Unit => (1 : LL)) : Set LL) :=
      Submodule.subset_span ⟨(), rfl⟩
    have h2 := Submodule.smul_mem (Submodule.span LL (Submodule.span O (Set.range fun _ : Unit => (1 : LL)) : Set LL)) x
      (Submodule.subset_span h1)
    simpa using h2

end Formalism.WeaklyAdmissibleFiltrations
end
end

-- bundled from Formalism.WeaklyAdmissibleFiltrations.CrystallineStableLifts.ExistsPeriodRingDataHolds
section
noncomputable section

namespace Formalism.WeaklyAdmissibleFiltrations

open LaurentPolynomial

def lpScaleF (c : ℚˣ) : Multiplicative ℤ →* LaurentPolynomial ℚ where
  toFun m := ((c ^ m.toAdd : ℚˣ) : ℚ) • T m.toAdd
  map_one' := by simp
  map_mul' a b := by
    rw [toAdd_mul, zpow_add, Units.val_mul, T_add, smul_mul_smul_comm]

@[simp] lemma lpScaleF_apply (c : ℚˣ) (m : Multiplicative ℤ) :
    lpScaleF c m = ((c ^ m.toAdd : ℚˣ) : ℚ) • T m.toAdd := rfl

def lpScale (c : ℚˣ) : LaurentPolynomial ℚ →ₐ[ℚ] LaurentPolynomial ℚ :=
  AddMonoidAlgebra.lift ℚ (LaurentPolynomial ℚ) ℤ (lpScaleF c)

lemma lpScale_coeff (c : ℚˣ) (f : LaurentPolynomial ℚ) (m : ℤ) :
    (lpScale c f).coeff m = ((c ^ m : ℚˣ) : ℚ) * f.coeff m := by
  induction f using LaurentPolynomial.induction_on' with
  | add p q hp hq =>
    rw [map_add (f := _), AddMonoidAlgebra.coeff_add, AddMonoidAlgebra.coeff_add, Finsupp.add_apply,
      Finsupp.add_apply, hp, hq, mul_add]
  | C_mul_T n a =>
    have h1 : lpScale c (T n) = ((c ^ n : ℚˣ) : ℚ) • T n := by
      unfold lpScale T
      rw [AddMonoidAlgebra.lift_single, one_smul, lpScaleF_apply]
      rfl
    have h2 : (C a * T n : LaurentPolynomial ℚ) = a • T n := by
      rw [C_eq_algebraMap, Algebra.algebraMap_eq_smul_one, smul_mul_assoc, one_mul]
    rw [h2, map_smul, h1, smul_smul, AddMonoidAlgebra.coeff_smul_apply,
      AddMonoidAlgebra.coeff_smul_apply, T_apply, smul_eq_mul, smul_eq_mul]
    by_cases h : n = m
    · subst h
      simp only [if_true]
      ring
    · simp [h]

def lpScaleE (c : ℚˣ) : LaurentPolynomial ℚ ≃ₐ[ℚ] LaurentPolynomial ℚ :=
  AlgEquiv.ofAlgHom (lpScale c) (lpScale c⁻¹)
    (AlgHom.ext fun f => LaurentPolynomial.ext fun m => by
      simp [lpScale_coeff, ← mul_assoc]
      rw [mul_inv_cancel₀ (zpow_ne_zero _ c.ne_zero), one_mul])
    (AlgHom.ext fun f => LaurentPolynomial.ext fun m => by
      simp [lpScale_coeff, ← mul_assoc]
      rw [inv_mul_cancel₀ (zpow_ne_zero _ c.ne_zero), one_mul])

lemma lpScaleE_coeff (c : ℚˣ) (f : LaurentPolynomial ℚ) (m : ℤ) :
    (lpScaleE c f).coeff m = ((c ^ m : ℚˣ) : ℚ) * f.coeff m := by
  show (lpScale c f).coeff m = _
  rw [lpScale_coeff]

def lpScaleHom : ℚˣ →* (LaurentPolynomial ℚ ≃ₐ[ℚ] LaurentPolynomial ℚ) where
  toFun := lpScaleE
  map_one' := AlgEquiv.ext fun f => LaurentPolynomial.ext fun m => by simp [lpScaleE_coeff]
  map_mul' c d := AlgEquiv.ext fun f => LaurentPolynomial.ext fun m => by
    simp [lpScaleE_coeff, AlgEquiv.mul_apply, mul_zpow, mul_assoc]

def lpTwo : ℚˣ := Units.mk0 2 (by norm_num)

@[simp] lemma lpTwo_val : (lpTwo : ℚ) = 2 := rfl

@[simp] lemma lpTwo_zpow (m : ℤ) : ((lpTwo ^ m : ℚˣ) : ℚ) = (2 : ℚ) ^ m := by
  rw [Units.val_zpow_eq_zpow_val, lpTwo_val]

lemma lpTwo_fix (f : LaurentPolynomial ℚ) (h : lpScaleE lpTwo f = f) :
    algebraMap ℚ (LaurentPolynomial ℚ) (f.coeff 0) = f := by
  refine LaurentPolynomial.ext fun a => ?_
  rw [← C_eq_algebraMap, C_apply]
  by_cases ha : a = 0
  · rw [if_pos ha, ha]
  · rw [if_neg ha]
    have h' := congrArg (fun g : LaurentPolynomial ℚ => g.coeff a) h
    simp only [lpScaleE_coeff, lpTwo_zpow] at h'
    have h2 : (2 : ℚ) ^ a ≠ 1 := fun h1 => ha ((zpow_eq_one_iff_right₀ (by norm_num) (by norm_num)).mp h1)
    have h3 : ((2 : ℚ) ^ a - 1) * f.coeff a = 0 := by rw [sub_mul, h', one_mul, sub_self]
    rcases mul_eq_zero.mp h3 with h4 | h4
    · exact absurd (sub_eq_zero.mp h4) h2
    · exact h4.symm

def lpFil (a : ℤ) : Submodule ℚ (LaurentPolynomial ℚ) where
  carrier := {f | ∀ m < a, f.coeff m = 0}
  add_mem' {x y} hx hy m hm := by simp [AddMonoidAlgebra.coeff_add, hx m hm, hy m hm]
  zero_mem' m _ := by simp
  smul_mem' c x hx m hm := by simp [hx m hm]

lemma lpFil_mul (a b : ℤ) (x y : LaurentPolynomial ℚ) (hx : x ∈ lpFil a) (hy : y ∈ lpFil b) :
    x * y ∈ lpFil (a + b) := by
  classical
  intro m hm
  rw [AddMonoidAlgebra.coeff_mul]
  simp only [Finsupp.sum]
  refine Finset.sum_eq_zero fun i hi => Finset.sum_eq_zero fun j hj => ?_
  rw [if_neg]
  intro hij
  have hi' : ¬ i < a := fun h => (Finsupp.mem_support_iff.mp hi) (hx i h)
  have hj' : ¬ j < b := fun h => (Finsupp.mem_support_iff.mp hj) (hy j h)
  omega

theorem existsPeriodRingData_holds : ExPD := by
  let χ : Multiplicative ℤ →* ℚˣ := zpowersHom ℚˣ lpTwo
  let act : Multiplicative ℤ →* (LaurentPolynomial ℚ ≃ₐ[ℚ] LaurentPolynomial ℚ) := lpScaleHom.comp χ
  have hact : ∀ g (f : LaurentPolynomial ℚ) m, (act g f).coeff m = ((χ g ^ m : ℚˣ) : ℚ) * f.coeff m := by
    intro g f m
    exact lpScaleE_coeff (χ g) f m
  have hone : act (Multiplicative.ofAdd 1) = lpScaleE lpTwo := by
    show lpScaleE (χ (Multiplicative.ofAdd 1)) = lpScaleE lpTwo
    simp [χ]
  have hfix : ∀ f : LaurentPolynomial ℚ, (∀ g, act g f = f) → ∃ c : ℚ, algebraMap ℚ _ c = f := by
    intro f hf
    refine ⟨f.coeff 0, lpTwo_fix f ?_⟩
    have := hf (Multiplicative.ofAdd 1)
    rwa [hone] at this
  exact ⟨{
    p := 2
    hp := Nat.prime_two
    finK₀ := inferInstance
    finK := inferInstance
    σ := AlgHom.id ℚ ℚ
    σ_bij := ⟨fun _ _ h => h, fun b => ⟨b, rfl⟩⟩
    actB := act
    invB := hfix
    φ := (lpScaleE lpTwo).toAlgHom
    φ_inj := (lpScaleE lpTwo).injective
    φ_K₀ := fun c => (lpScaleE lpTwo).toAlgHom.commutes c
    φ_comm := fun g b => LaurentPolynomial.ext fun m => by
      change (lpScaleE lpTwo (act g b)).coeff m = (act g (lpScaleE lpTwo b)).coeff m
      rw [lpScaleE_coeff, hact, hact, lpScaleE_coeff]
      ring
    actdR := act
    invdR := hfix
    ι := AlgHom.id ℚ _
    ι_inj := fun _ _ h => h
    ι_comm := fun _ _ => rfl
    Fil := lpFil
    Fil_anti := fun a f hf m hm => hf m (by omega)
    one_mem := fun m hm => by rw [← T_zero, T_apply, if_neg (by omega)]
    Fil_mul := lpFil_mul
    Fil_exh := fun x => by
      refine ⟨-(∑ i ∈ x.coeff.support, |i|), fun m hm => ?_⟩
      by_contra hne
      have hm' : m ∈ x.coeff.support := Finsupp.mem_support_iff.mpr hne
      have h1 := Finset.single_le_sum (f := fun i : ℤ => |i|) (fun i _ => abs_nonneg i) hm'
      have h2 := neg_abs_le m
      linarith
    Fil_sep := fun x hx => LaurentPolynomial.ext fun m => by
      rw [hx (m + 1) m (by omega)]
      rfl
    Fil_G := fun g a x hx m hm => by rw [hact, hx m hm, mul_zero]
    χ := χ
    t := T 1
    t_unit := isUnit_T 1
    t_act := fun g => LaurentPolynomial.ext fun m => by
      rw [hact, AddMonoidAlgebra.coeff_smul_apply, T_apply, smul_eq_mul]
      by_cases h : (1 : ℤ) = m
      · subst h
        simp
      · simp [h]
    t_φ := LaurentPolynomial.ext fun m => by
      change (lpScaleE lpTwo (T 1)).coeff m = _
      rw [lpScaleE_coeff, AddMonoidAlgebra.coeff_smul_apply, T_apply, smul_eq_mul, lpTwo_zpow]
      by_cases h : (1 : ℤ) = m
      · subst h
        norm_num
      · simp [h]
    mem_filtration_one := fun m hm => by rw [AlgHom.id_apply, T_apply, if_neg (by omega)]
    not_mem_filtration_two := fun h => by
      have h1 := h 1 (by norm_num)
      rw [AlgHom.id_apply, T_apply, if_pos rfl] at h1
      exact one_ne_zero h1
    fund := fun b hb _ => ⟨b.coeff 0, lpTwo_fix b hb⟩ }⟩

end Formalism.WeaklyAdmissibleFiltrations
end
end

-- bundled from Formalism.WeaklyAdmissibleFiltrations.CrystallineStableLifts.Galois
section
noncomputable section

namespace Formalism.WeaklyAdmissibleFiltrations

open Module TensorProduct

section CobGalois

variable {G : Type} [Group G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : PeriodData G Qp K₀ K B BdR}
    {LL : Type} [Field LL] [Algebra Qp LL]
    {V : Type} [AddCommGroup V] [Module LL V] [Module Qp V] [IsScalarTower Qp LL V]
    {ρ : Representation LL G V}

theorem cob_apply_galois (x : V) (g : G) : cob ρ x g = ρ g x - x := rfl

variable [TopologicalSpace G] [TopologicalSpace V] [IsTopologicalAddGroup V]
    [ContinuousConstSMul LL V]

theorem coboundaryMap_mem_finiteCocycles (hcont : ∀ x, Continuous fun g => ρ g x) (x : V) :
    cob ρ x ∈ finiteCocycles PD ρ := by
  refine ⟨⟨?_, fun g h => ?_⟩, x ⊗ₜ[Qp] (1 : B), fun g => ?_⟩
  · exact (hcont x).sub continuous_const
  · simp only [cob_apply_galois, map_mul, Module.End.mul_apply, map_sub]
    abel
  · simp [cob_apply_galois, actVB, sub_tmul]

theorem coboundaries_le_finiteCocycles (hcont : ∀ x, Continuous fun g => ρ g x) : B1 ρ ≤ finiteCocycles PD ρ := by
  rintro c ⟨x, rfl⟩
  exact coboundaryMap_mem_finiteCocycles hcont x

end CobGalois

theorem cobF : CobF := by
  unfold CobF
  intros
  exact ⟨coboundaries_le_finiteCocycles ‹_›, fun c hc => hc.1⟩

theorem torsFreeT : TorsFreeT := by
  intro G _ Qp K₀ K _ _ _ _ _ _ _ B BdR _ _ _ _ _ _ _ _ _ _ _ PD LL _ _ O _ _ V _ _ _ _ _ _ ρ
    _ _ _ _ L c a hc ha h
  refine ⟨hc, ?_⟩
  have h2 : (algebraMap O LL a) • c ∈ finiteCocycles PD ρ := by
    rw [algebraMap_smul]
    exact h.2
  have h3 := (finiteCocycles PD ρ).smul_mem (algebraMap O LL a)⁻¹ h2
  rw [inv_smul_smul₀ ha] at h3
  exact h3

theorem cocyclesFunctorial_holds : CocyclesFunctorial := by
  intro G _ Qp K₀ K _ _ _ _ _ _ _ B BdR _ _ _ _ _ _ _ _ _ _ _ PD LL _ _ V V' _ _ _ _ _ _ _ _ ρ ρ'
    _ _ _ _ _ _ _ f hf hequiv c
  have hZ : c ∈ continuousCocycles ρ → ⇑f ∘ c ∈ continuousCocycles ρ' := by
    rintro ⟨hc1, hc2⟩
    refine ⟨hf.comp hc1, fun g h => ?_⟩
    change f (c (g * h)) = f (c g) + ρ' g (f (c h))
    rw [hc2, map_add (f := _), hequiv]
  refine ⟨hZ, ?_⟩
  rintro ⟨hc, x, hx⟩
  let m := AlgebraTensorModule.map f (LinearMap.id : B →ₗ[Qp] B)
  have hm : ∀ g y, m (actVB PD ρ g y) = actVB PD ρ' g (m y) := by
    intro g y
    induction y using TensorProduct.induction_on with
    | zero => simp
    | tmul v b => simp [m, actVB, hequiv]
    | add a b ha hb => simp only [map_add (f := _), ha, hb]
  refine ⟨hZ hc, m x, fun g => ?_⟩
  change f (c g) ⊗ₜ[Qp] (1 : B) = _
  have := congrArg m (hx g)
  simp only [m, AlgebraTensorModule.map_tmul, LinearMap.id_apply, map_sub] at this
  rw [this, ← hm]

section ImGalois

variable {G : Type} [Group G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : PeriodData G Qp K₀ K B BdR}
    {LL : Type} [Field LL] [Algebra Qp LL]
    {O : Type} [CommRing O] [Algebra O LL]
    {V : Type} [AddCommGroup V] [Module LL V] [Module Qp V] [IsScalarTower Qp LL V]
    [Module O V] [IsScalarTower O LL V] {ρ : Representation LL G V}
    {V' : Type} [AddCommGroup V'] [Module LL V'] [Module Qp V'] [IsScalarTower Qp LL V']
    [Module O V'] [IsScalarTower O LL V'] {ρ' : Representation LL G V'}
    [TopologicalSpace G]

theorem colZero_iff_galois [TopologicalSpace V] [ContinuousAdd V] [ContinuousConstSMul LL V]
    [TopologicalSpace V'] [ContinuousAdd V'] [ContinuousConstSMul LL V']
    {L : Lattice (O := O) ρ} {L' : Lattice (O := O) ρ'} (F : LatHom L L') :
    F.col PD = 0 ↔ F.LiftF PD 0 := by
  unfold LatHom.col LatHom.LiftF
  rw [Module.length_eq_zero_iff, Submodule.Quotient.subsingleton_iff,
    Submodule.comap_subtype_eq_top]
  simp only [pow_zero, one_smul]
  exact ⟨fun h c hc => h hc, fun h c hc => h c hc⟩

theorem imF_le_galois [TopologicalSpace V] [IsTopologicalAddGroup V] [ContinuousConstSMul LL V]
    [TopologicalSpace V'] [IsTopologicalAddGroup V'] [ContinuousConstSMul LL V']
    {L : Lattice (O := O) ρ} {L' : Lattice (O := O) ρ'} (F : LatHom L L')
    (hcont : ∀ x, Continuous fun g => ρ' g x) : F.ImF PD ≤ latticeFiniteCocycles PD L' := by
  refine sup_le (Submodule.map_le_iff_le_comap.mpr fun c hc => F.post_Z1fT PD c hc) ?_
  rintro c ⟨x, hx, rfl⟩
  have hf : cob ρ' x ∈ finiteCocycles PD ρ' := coboundaryMap_mem_finiteCocycles hcont x
  refine ⟨⟨hf.1, ?_⟩, hf⟩
  intro g _
  exact L'.T.sub_mem (L'.stable g x hx) hx

end ImGalois

theorem imFLe : ImFLe := by
  unfold ImFLe
  intros
  exact ⟨imF_le_galois _ ‹_›, colZero_iff_galois _⟩

theorem finiteCocycles_properties : CobF ∧ TorsFreeT ∧ CocyclesFunctorial ∧ ImFLe :=
  ⟨cobF, torsFreeT, cocyclesFunctorial_holds, imFLe⟩

end Formalism.WeaklyAdmissibleFiltrations
end
end

