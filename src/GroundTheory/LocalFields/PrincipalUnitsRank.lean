module

public import Mathlib
public import GroundTheory.LocalFields.Bundle0011
public import GroundTheory.LocalFields.Integers

@[expose] public section

namespace GroundTheory.LocalField

open ValuativeRel IsLocalRing Topology Filter
open scoped WithZero

variable {K : Type*} [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]

namespace PadicRank

variable (p : ℕ) [hp : Fact p.Prime]

theorem mem_integer_padic_iff (x : ℚ_[p]) : x ∈ 𝒪[ℚ_[p]] ↔ ‖x‖ ≤ 1 := by
  rw [Valuation.mem_integer_iff, ← map_one (valuation ℚ_[p]), ← Valuation.vle_iff_le,
    Valuation.Compatible.vle_iff_le (v := Padic.mulValuation),
    GroundTheory.LocalField.Padic.mulValuation_le_iff_norm_le, norm_one]

noncomputable def padicIntEquivInteger : ℤ_[p] ≃+* 𝒪[ℚ_[p]] where
  toFun x := ⟨x, (mem_integer_padic_iff p x).mpr x.2⟩
  invFun y := ⟨y, (mem_integer_padic_iff p y).mp y.2⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_mul' _ _ := rfl
  map_add' _ _ := rfl

variable [CharP 𝓀[K] p] [CharZero K]


variable (K) in
noncomputable def padicIntHom : ℤ_[p] →+* K :=
  (CharZero.padicHom K p).comp PadicInt.Coe.ringHom

theorem padicIntHom_mem (a : ℤ_[p]) : padicIntHom (K := K) p a ∈ 𝒪[K] :=
  CharZero.valuation_padicHom_padicInt_le_one K p a


variable (K) in
noncomputable def padicIntHomInteger : ℤ_[p] →+* 𝒪[K] :=
  (padicIntHom (K := K) p).codRestrict 𝒪[K] (padicIntHom_mem p)


variable (K) in
noncomputable abbrev algebraK : Algebra ℤ_[p] K := (padicIntHom (K := K) p).toAlgebra


variable (K) in
noncomputable abbrev algebraInteger : Algebra ℤ_[p] 𝒪[K] := (padicIntHomInteger (K := K) p).toAlgebra

attribute [local instance] algebraK algebraInteger

theorem finite_and_finrank_integer :
    Module.Finite ℤ_[p] 𝒪[K] ∧ Module.finrank ℤ_[p] 𝒪[K] =
      (letI := (CharZero.padicHom K p).toAlgebra; Module.finrank ℚ_[p] K) := by
  let := (CharZero.padicHom K p).toAlgebra
  have : ValuativeExtension ℚ_[p] K := ⟨fun {a b} ↦ CharZero.padicHom_vle_iff K p a b⟩
  have : FiniteDimensional ℚ_[p] K := CharZero.finiteDimensional_padicHom K p
  have hfin : Module.Finite 𝒪[ℚ_[p]] 𝒪[K] := finite_integer ℚ_[p] K
  have hrank := finrank_integer ℚ_[p] K
  have he : (algebraMap ℤ_[p] 𝒪[K]).comp ((padicIntEquivInteger p).symm : 𝒪[ℚ_[p]] →+* ℤ_[p]) =
      (RingEquiv.refl 𝒪[K] : 𝒪[K] →+* 𝒪[K]).comp (algebraMap 𝒪[ℚ_[p]] 𝒪[K]) := by
    ext x
    rfl
  refine ⟨Module.Finite.of_equiv_equiv (padicIntEquivInteger p).symm (RingEquiv.refl _) he, ?_⟩
  rw [← hrank]
  have := rank_eq_of_equiv_equiv (R := ℤ_[p]) (R' := 𝒪[ℚ_[p]]) (M := 𝒪[K]) (M₁ := 𝒪[K])
    (padicIntEquivInteger p) (AddEquiv.refl _) (padicIntEquivInteger p).bijective
    (fun r m ↦ rfl)
  exact congrArg Cardinal.toNat this

theorem padicIntHom_mem_valBall_zero (a : ℤ_[p]) :
    padicIntHom (K := K) p a ∈ valBall (K := K) 0 := by
  change normalizedValuation K (padicIntHom K p a) ≤ WithZero.exp (-(0 : ℤ))
  rw [neg_zero, WithZero.exp_zero, normalizedValuation_le_one_iff]
  exact padicIntHom_mem p a


variable (K) in
noncomputable def valBallSubmodule (m : ℤ) : Submodule ℤ_[p] K where
  carrier := valBall (K := K) m
  add_mem' := add_mem
  zero_mem' := zero_mem _
  smul_mem' a x hx := by
    rw [Algebra.smul_def]
    have ha : normalizedValuation K (padicIntHom K p a) ≤ 1 :=
      normalizedValuation_le_one_iff.mpr (padicIntHom_mem p a)
    change normalizedValuation K x ≤ WithZero.exp (-m) at hx
    change normalizedValuation K (padicIntHom K p a * x) ≤ WithZero.exp (-m)
    rw [map_mul]
    simpa only [one_mul] using mul_le_mul' ha hx

theorem mem_valBallSubmodule {m : ℤ} {x : K} :
    x ∈ valBallSubmodule (K := K) p m ↔ x ∈ valBall (K := K) m :=
  Iff.rfl


variable (K) in
noncomputable def valBallSubmoduleZeroEquiv : valBallSubmodule (K := K) p 0 ≃ₗ[ℤ_[p]] 𝒪[K] where
  toFun x := ⟨x, mem_integer_of_mem_valBall le_rfl x.2⟩
  invFun y := ⟨y, by
    change normalizedValuation K (y : K) ≤ WithZero.exp (-(0 : ℤ))
    rw [neg_zero, WithZero.exp_zero, normalizedValuation_le_one_iff]
    exact y.2⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl


variable (K) in
noncomputable def valBallSubmoduleEquiv (m : ℤ) :
    valBallSubmodule (K := K) p 0 ≃ₗ[ℤ_[p]] valBallSubmodule (K := K) p m :=
  have hy := exists_normalizedValuation_eq (K := K) (-m)
  let y := hy.choose
  have hyv : normalizedValuation K y = WithZero.exp (-m) := hy.choose_spec
  have hy0 : y ≠ 0 := by
    intro h
    rw [h, map_zero] at hyv
    exact WithZero.exp_ne_zero hyv.symm
  { toFun x := ⟨y * x, by
      have hx : normalizedValuation K (x : K) ≤ WithZero.exp (-(0 : ℤ)) := x.2
      change normalizedValuation K (y * x) ≤ WithZero.exp (-m)
      rw [map_mul, hyv]
      simpa only [neg_zero, WithZero.exp_zero, mul_one] using mul_le_mul_right hx (WithZero.exp (-m))⟩
    invFun x := ⟨y⁻¹ * x, by
      have hx : normalizedValuation K (x : K) ≤ WithZero.exp (-m) := x.2
      change normalizedValuation K (y⁻¹ * x) ≤ WithZero.exp (-(0 : ℤ))
      rw [map_mul, map_inv₀, hyv, ← WithZero.exp_neg]
      calc
        _ ≤ WithZero.exp (-(-m)) * WithZero.exp (-m) := mul_le_mul_right hx _
        _ = _ := by rw [← WithZero.exp_add, neg_add_cancel, neg_zero]⟩
    left_inv x := by ext; simp [hy0]
    right_inv x := by ext; simp [hy0]
    map_add' x x' := by ext; simp [mul_add]
    map_smul' a x := by
      ext
      simp only [SetLike.val_smul, Algebra.smul_def, RingHom.id_apply]
      ring }

theorem finite_and_finrank_valBallSubmodule (m : ℤ) :
    Module.Finite ℤ_[p] (valBallSubmodule (K := K) p m) ∧
      Module.finrank ℤ_[p] (valBallSubmodule (K := K) p m) =
        (letI := (CharZero.padicHom K p).toAlgebra; Module.finrank ℚ_[p] K) := by
  obtain ⟨h1, h2⟩ := finite_and_finrank_integer (K := K) p
  have e := (valBallSubmoduleEquiv (K := K) p m).symm.trans (valBallSubmoduleZeroEquiv (K := K) p)
  exact ⟨Module.Finite.equiv e.symm, e.finrank_eq.trans h2⟩

theorem rank_valBallSubmodule (m : ℤ) :
    Module.rank ℤ_[p] (valBallSubmodule (K := K) p m) =
      (letI := (CharZero.padicHom K p).toAlgebra; Module.finrank ℚ_[p] K) := by
  obtain ⟨h1, h2⟩ := finite_and_finrank_valBallSubmodule (K := K) p m
  rw [← h2]
  exact (Cardinal.cast_toNat_of_lt_aleph0 (Module.rank_lt_aleph0 _ _)).symm


variable (K) in
noncomputable def padicLogLinear : Additive (unitFiltrationUnits K 1) →ₗ[ℤ_[p]] K where
  toFun := padicLog K
  map_add' := map_add _
  map_smul' a u := by
    rw [padicLog_smul p a u, RingHom.id_apply, Algebra.smul_def]
    rfl

omit [CharZero K] in
theorem mem_principalFiltration_zero (u : Additive (unitFiltrationUnits K 1)) :
    u ∈ principalFiltration (K := K) 0 := by
  rw [principalFiltration_zero]; trivial

theorem padicLog_nsmul_mem (u : Additive (unitFiltrationUnits K 1)) :
    padicLog K (p ^ absRamificationIndex (K := K) • u) ∈
      valBall (K := K) (absRamificationIndex (K := K) + 1) := by
  have := nsmul_prime_pow_mem_principalFiltration p (mem_principalFiltration_zero u)
    (absRamificationIndex (K := K))
  rw [zero_add] at this
  exact_mod_cast padicLog_mem_valBall_of_mem p le_rfl this


include p in
theorem padicLog_mem_valBall_bound (u : Additive (unitFiltrationUnits K 1)) :
    padicLog K u ∈ valBall (K := K) (absRamificationIndex (K := K) + 1 -
      absRamificationIndex (K := K) * absRamificationIndex (K := K)) := by
  set e := absRamificationIndex (K := K)
  have h := padicLog_nsmul_mem p u
  rw [map_nsmul, nsmul_eq_mul] at h
  have hp0 : ((p ^ e : ℕ) : K) ≠ 0 := Nat.cast_ne_zero.mpr (pow_ne_zero _ hp.out.ne_zero)
  have hinv : (((p ^ e : ℕ) : K))⁻¹ ∈ valBall (K := K) (-(e * e : ℤ)) := by
    change normalizedValuation K (((p ^ e : ℕ) : K)⁻¹) ≤ WithZero.exp (-(-(e * e : ℤ)))
    rw [map_inv₀, Nat.cast_pow, map_pow, normalizedValuation_natCast_prime p,
      ← WithZero.exp_nsmul, ← WithZero.exp_neg]
    simp
    exact le_rfl
  have : (((p ^ e : ℕ) : K))⁻¹ * (((p ^ e : ℕ) : K) * padicLog K u) ∈
      valBall (K := K) (-(e * e : ℤ) + (e + 1)) := by
    change normalizedValuation K (_ * _) ≤ WithZero.exp (-(_ + _))
    rw [map_mul, neg_add, WithZero.exp_add]
    exact mul_le_mul' hinv h
  push_cast at this hp0
  rw [← mul_assoc, inv_mul_cancel₀ hp0, one_mul] at this
  convert this using 2
  ring

theorem range_padicLogLinear_le : LinearMap.range (padicLogLinear (K := K) p) ≤
    valBallSubmodule (K := K) p (absRamificationIndex (K := K) + 1 -
      absRamificationIndex (K := K) * absRamificationIndex (K := K)) := by
  rintro _ ⟨u, rfl⟩
  exact padicLog_mem_valBall_bound p u

omit [CharP 𝓀[K] p] [CharZero K] in
theorem lt_sub_one_mul_succ : (absRamificationIndex (K := K) : ℤ) <
    (p - 1 : ℤ) * ((absRamificationIndex (K := K) + 1 : ℕ) : ℤ) := by
  have hp2 : (2 : ℤ) ≤ p := by exact_mod_cast hp.out.two_le
  push_cast
  nlinarith

theorem valBallSubmodule_le_range :
    valBallSubmodule (K := K) p ((absRamificationIndex (K := K) + 1 : ℕ) : ℤ) ≤
      LinearMap.range (padicLogLinear (K := K) p) := by
  intro y hy
  set n := absRamificationIndex (K := K) + 1
  have hn := lt_sub_one_mul_succ (K := K) p
  have h1 : 1 ≤ n := by omega
  have hy' : y ∈ valBall (K := K) (n : ℤ) := hy
  have hone : (1 : K) ∈ valBall (K := K) 0 := by
    change normalizedValuation K (1 : K) ≤ WithZero.exp (-(0 : ℤ))
    simp
  have hsub : expSeries y - 1 - y ∈ valBall (K := K) ((n : ℤ) + 1) := by
    simpa only [one_mul, mul_zero, zero_add] using
      expSeries_mul_sub_one_sub_mem p hy' hn hone le_rfl
  have hsub' : expSeries y - 1 - y ∈ valBall (K := K) (n : ℤ) := by
    change normalizedValuation K (expSeries y - 1 - y) ≤ WithZero.exp (-(n : ℤ))
    exact le_trans hsub (WithZero.exp_le_exp.mpr (by omega))
  have hmem : expSeries y - 1 ∈ valBall (K := K) (n : ℤ) := by
    simpa only [sub_add_cancel] using add_mem hsub' hy'
  let w : Kˣ := Units.mk0 (expSeries y) (expSeries_ne_zero h1 hmem)
  have hw : w ∈ unitFiltrationUnits K n := (mem_unitFiltrationUnits_iff_valBall h1).mpr hmem
  refine ⟨Additive.ofMul ⟨w, unitFiltrationUnits_antitone h1 hw⟩, ?_⟩
  change logSeries (expSeries y - 1) = y
  exact logSeries_expSeries_sub_one p hy' hn

theorem nsmul_eq_zero_of_padicLog_eq_zero {u : Additive (unitFiltrationUnits K 1)}
    (hu : padicLog K u = 0) : p ^ absRamificationIndex (K := K) • u = 0 := by
  set e := absRamificationIndex (K := K)
  have hw := nsmul_prime_pow_mem_principalFiltration p (mem_principalFiltration_zero u) e
  rw [zero_add, mem_principalFiltration] at hw
  have hlog : logSeries ((((Additive.toMul (p ^ e • u) : unitFiltrationUnits K 1) : Kˣ) : K) - 1)
      = 0 := by
    rw [← padicLog_apply, map_nsmul, hu, smul_zero]
  have := eq_zero_of_logSeries_eq_zero p (by exact_mod_cast lt_sub_one_mul_succ (K := K) p) hw hlog
  apply Additive.toMul.injective
  ext
  simpa [sub_eq_zero] using this

theorem finite_ker_padicLog : Finite (LinearMap.ker (padicLogLinear (K := K) p)) := by
  set e := absRamificationIndex (K := K)
  let f : LinearMap.ker (padicLogLinear (K := K) p) → rootsOfUnity (p ^ e) K := fun u ↦
    ⟨((Additive.toMul (u : Additive (unitFiltrationUnits K 1)) : unitFiltrationUnits K 1) : Kˣ), by
      have h := nsmul_eq_zero_of_padicLog_eq_zero p (LinearMap.mem_ker.mp u.2)
      have := congrArg (fun v : Additive (unitFiltrationUnits K 1) ↦
        ((Additive.toMul v : unitFiltrationUnits K 1) : Kˣ)) h
      simpa [mem_rootsOfUnity] using this⟩
  refine Finite.of_injective f fun u v huv ↦ ?_
  have := congrArg (fun z : rootsOfUnity (p ^ e) K ↦ (z : Kˣ)) huv
  exact Subtype.ext (Additive.toMul.injective (Subtype.ext this))

theorem fg_ker_padicLogLinear : (LinearMap.ker (padicLogLinear (K := K) p)).FG := by
  have := finite_ker_padicLog (K := K) p
  have hfin : (LinearMap.ker (padicLogLinear (K := K) p) : Set (Additive (unitFiltrationUnits K 1))).Finite :=
    Set.toFinite _
  refine ⟨hfin.toFinset, ?_⟩
  rw [Set.Finite.coe_toFinset, Submodule.span_eq]

theorem fg_range_padicLogLinear : (LinearMap.range (padicLogLinear (K := K) p)).FG := by
  set e := absRamificationIndex (K := K)
  set c : ℤ := e + 1 - e * e
  have : Module.Finite ℤ_[p] (valBallSubmodule (K := K) p c) :=
    (finite_and_finrank_valBallSubmodule (K := K) p c).1
  have : IsNoetherian ℤ_[p] (valBallSubmodule (K := K) p c) := inferInstance
  have : IsNoetherian ℤ_[p] (LinearMap.range (padicLogLinear (K := K) p)) :=
    isNoetherian_of_le (range_padicLogLinear_le p)
  exact (Submodule.fg_top _).mp (IsNoetherian.noetherian ⊤)

end PadicRank

section Rank

open PadicRank

attribute [local instance] algebraK algebraInteger

theorem finite_principalUnits (p : ℕ) [Fact p.Prime] [CharP 𝓀[K] p] [CharZero K] :
    Module.Finite ℤ_[p] (Additive (unitFiltrationUnits K 1)) := by
  refine ⟨?_⟩
  have h := Submodule.fg_of_fg_map_of_fg_inf_ker (padicLogLinear (K := K) p)
    (s := ⊤) (by rw [Submodule.map_top]; exact fg_range_padicLogLinear p)
    (by rw [top_inf_eq]; exact fg_ker_padicLogLinear p)
  exact h

theorem finrank_principalUnits (p : ℕ) [Fact p.Prime] [CharP 𝓀[K] p] [CharZero K] :
    Module.finrank ℤ_[p] (Additive (unitFiltrationUnits K 1)) =
      (letI := (CharZero.padicHom K p).toAlgebra; Module.finrank ℚ_[p] K) := by
  set d := (letI := (CharZero.padicHom K p).toAlgebra; Module.finrank ℚ_[p] K)
  have hker : Module.rank ℤ_[p] (LinearMap.ker (padicLogLinear (K := K) p)) = 0 := by
    refine (rank_eq_zero_iff (R := ℤ_[p]) (M := LinearMap.ker (padicLogLinear (K := K) p))).mpr
      fun x ↦ ?_
    refine ⟨((p ^ absRamificationIndex (K := K) : ℕ) : ℤ_[p]), ?_, ?_⟩
    · exact_mod_cast pow_ne_zero _ (Fact.out : p.Prime).ne_zero
    · apply Subtype.ext
      rw [Submodule.coe_smul, natCast_smul, Submodule.coe_zero]
      exact nsmul_eq_zero_of_padicLog_eq_zero p (LinearMap.mem_ker.mp x.2)
  have hrange : Module.rank ℤ_[p] (LinearMap.range (padicLogLinear (K := K) p)) = d := by
    refine le_antisymm ?_ ?_
    · rw [← rank_valBallSubmodule (K := K) p (absRamificationIndex (K := K) + 1 -
        absRamificationIndex (K := K) * absRamificationIndex (K := K))]
      exact Submodule.rank_mono (range_padicLogLinear_le p)
    · rw [← rank_valBallSubmodule (K := K) p ((absRamificationIndex (K := K) + 1 : ℕ) : ℤ)]
      exact Submodule.rank_mono (valBallSubmodule_le_range p)
  have h := (padicLogLinear (K := K) p).rank_range_add_rank_ker
  rw [hker, hrange, add_zero] at h
  rw [Module.finrank, ← h]
  simp

end Rank

end GroundTheory.LocalField
