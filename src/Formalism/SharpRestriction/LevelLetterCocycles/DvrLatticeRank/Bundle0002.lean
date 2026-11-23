module

public import Formalism.SharpRestriction.LevelLetterCocycles.DvrLatticeRank.SatDVR
public import Mathlib
public import Formalism.PadicSubsetSums.CentralIdempotents.Bundle0001
public import Formalism.SharpRestriction.LevelLetterCocycles.DvrLatticeRank.Bundle0001

@[expose] public section

-- bundled from Formalism.SharpRestriction.LevelLetterCocycles.DvrLatticeRank.DecompCoord
section
noncomputable section

namespace Formalism.MainNotions.N.Ln34.UniversalLiftFrames

open Module

theorem decomp_coord {O LL : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field LL]
    [Algebra O LL] [IsFractionRing O LL] {L : Type*} [AddCommGroup L] [Module O L] {r m : ℕ}
    (bL : Basis (Fin r) O L) {ι₁ ι₂ : Type*} [Fintype ι₁] [Fintype ι₂]
    (C : ι₁ → Submodule LL (Fin r → LL)) (hC : ∀ τ, r ≤ finrank LL (C τ) + m)
    (Fs : ι₂ → Submodule LL (Fin r → LL)) (hF : ∀ τ, finrank LL (Fs τ) ≤ m) :
    ∃ (k : ℕ) (ell : Fin k → L) (Lr : Submodule O L) (P : Fin k → Fin r → O),
      finrank O Lr ≤ (Fintype.card ι₁ + Fintype.card ι₂) * m ∧
      (∀ j τ, (fun i => algebraMap O LL (bL.repr (ell j) i)) ∈ C τ) ∧
      (∀ i, bL i - ∑ j, P j i • ell j ∈ Lr) ∧
      (∀ τ, ∀ d ∈ Fs τ, ∀ j, ∑ i, algebraMap O LL (P j i) * d i = 0) := by
  obtain ⟨L₁, L₂, hc, hrk, hCL, hFL⟩ := DualFramesAlt.SatDVR.decomp (O := O) (K := LL) C hC Fs hF
  obtain ⟨k, bu⟩ := Submodule.basisOfPid (Pi.basisFun O (Fin r)) L₁
  set pr := L₁.projectionOnto L₂ hc with hpr
  set P : Fin k → Fin r → O := fun j i => bu.coord j (pr (fun i' => if i = i' then 1 else 0)) with hP
  have hrepr : ∀ (u : Fin r → O) (i : Fin r), bL.repr (bL.equivFun.symm u) i = u i := by
    intro u i
    rw [← Basis.equivFun_apply, LinearEquiv.apply_symm_apply]
  have hsum : ∀ (i : Fin r), ∑ j, P j i • ((bu j : L₁) : Fin r → O) =
      ((pr (fun i' => if i = i' then 1 else 0) : L₁) : Fin r → O) := by
    intro i
    have h := congrArg Subtype.val (bu.sum_repr (pr (fun i' => if i = i' then 1 else 0)))
    rw [Submodule.coe_sum] at h
    simpa [hP, Basis.coord_apply] using h
  have hrow : ∀ (j : Fin k) (y : Fin r → O), ∑ i, P j i * y i = bu.coord j (pr y) := by
    intro j y
    rw [← LinearMap.comp_apply, LinearMap.pi_apply_eq_sum_univ ((bu.coord j).comp pr) y]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp [hP, smul_eq_mul, mul_comm]
  refine ⟨k, fun j => bL.equivFun.symm (bu j), L₂.map (bL.equivFun.symm : (Fin r → O) →ₗ[O] L), P, ?_, ?_, ?_, ?_⟩
  · rw [LinearEquiv.finrank_map_eq]
    exact hrk
  · intro j τ
    convert hCL τ (bu j) (bu j).2 using 1
    funext i
    rw [DualFramesAlt.SatDVR.toK_apply, hrepr]
  · intro i
    set_option synthInstance.maxHeartbeats 100000 in
      rw [Submodule.mem_map_equiv, LinearEquiv.symm_symm, map_sub, map_sum]
    simp only [map_smul, LinearEquiv.apply_symm_apply]
    rw [hsum i, ← Submodule.ker_projectionOnto hc, LinearMap.mem_ker, map_sub, ← hpr,
      Submodule.projectionOnto_apply_left, sub_eq_zero]
    congr 1
    funext i'
    simp
  · intro τ d hd j
    let ψ : (Fin r → LL) →ₗ[LL] LL := ∑ i, algebraMap O LL (P j i) • LinearMap.proj i
    have hψ : ∀ x : Fin r → LL, ψ x = ∑ i, algebraMap O LL (P j i) * x i := by
      intro x
      simp [ψ, LinearMap.sum_apply, Algebra.smul_def]
    have hker : Submodule.span LL (DualFramesAlt.SatDVR.toK O LL r '' (L₂ : Set (Fin r → O))) ≤
        LinearMap.ker ψ := by
      rw [Submodule.span_le]
      rintro _ ⟨y, hy, rfl⟩
      rw [SetLike.mem_coe, LinearMap.mem_ker, hψ]
      set_option synthInstance.maxHeartbeats 100000 in
        simp only [DualFramesAlt.SatDVR.toK_apply, ← map_mul, ← map_sum]
      rw [hrow j y]
      have h0 : pr y = 0 := Submodule.projectionOnto_apply_right hc ⟨y, hy⟩
      rw [h0, map_zero, map_zero]
    have := hker (hFL τ hd)
    rwa [LinearMap.mem_ker, hψ] at this

end Formalism.MainNotions.N.Ln34.UniversalLiftFrames
end
end

-- bundled from Formalism.SharpRestriction.LevelLetterCocycles.DvrLatticeRank.EigenRingInvariants
section
namespace DualFramesAlt.eigenRingInvariants

open PowerSeries

noncomputable abbrev Ia {O : Type*} [CommRing O] (a : O) : Ideal (PowerSeries O) := Ideal.span {X - C a}

theorem mk_X {O : Type*} [CommRing O] (a : O) : Ideal.Quotient.mk (Ia a) X = Ideal.Quotient.mk (Ia a) (C a) :=
  Ideal.Quotient.eq.mpr (Ideal.mem_span_singleton.mpr dvd_rfl)

section Ev

variable {O : Type*} [CommRing O] [IsLocalRing O]

theorem map_residue_X_sub_C {a : O} (ha : a ∈ IsLocalRing.maximalIdeal O) :
    (X - C a : PowerSeries O).map (IsLocalRing.residue O) = X := by
  rw [map_sub, PowerSeries.map_X, PowerSeries.map_C, (IsLocalRing.residue_eq_zero_iff a).mpr ha, map_zero, sub_zero]

theorem order_map_X_sub_C {a : O} (ha : a ∈ IsLocalRing.maximalIdeal O) :
    ((X - C a : PowerSeries O).map (Ideal.Quotient.mk (IsLocalRing.maximalIdeal O))).order.toNat = 1 := by
  change ((X - C a : PowerSeries O).map (IsLocalRing.residue O)).order.toNat = 1
  rw [map_residue_X_sub_C ha, PowerSeries.order_X]
  rfl

variable [IsAdicComplete (IsLocalRing.maximalIdeal O) O]

theorem ev_exists {a : O} (ha : a ∈ IsLocalRing.maximalIdeal O) (f : PowerSeries O) :
    ∃ c : O, Ideal.Quotient.mk (Ia a) f = Ideal.Quotient.mk (Ia a) (C c) := by
  have hg : (X - C a : PowerSeries O).map (IsLocalRing.residue O) ≠ 0 := by
    rw [map_residue_X_sub_C ha]
    exact PowerSeries.X_ne_zero
  obtain ⟨q, r, hW⟩ := f.exists_isWeierstrassDivision hg
  obtain ⟨hdeg, heq⟩ := hW
  rw [order_map_X_sub_C ha] at hdeg
  have hr : r = Polynomial.C (r.coeff 0) :=
    Polynomial.eq_C_of_degree_le_zero (Nat.WithBot.lt_one_iff_le_zero.mp (by exact_mod_cast hdeg))
  refine ⟨r.coeff 0, ?_⟩
  rw [heq, map_add (f := _), Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_span_singleton.mpr (dvd_mul_right _ _)),
    zero_add]
  congr 1
  conv_lhs => rw [hr]
  exact Polynomial.coe_C _

theorem ev_inj {a : O} (ha : a ∈ IsLocalRing.maximalIdeal O) {c c' : O}
    (h : Ideal.Quotient.mk (Ia a) (C c) = Ideal.Quotient.mk (Ia a) (C c')) : c = c' := by
  rw [Ideal.Quotient.eq, ← map_sub] at h
  obtain ⟨H, hH⟩ := Ideal.mem_span_singleton.mp h
  have hrec : ∀ n, PowerSeries.coeff (R := O) n H = a * PowerSeries.coeff (R := O) (n + 1) H := by
    intro n
    have hn := congrArg (PowerSeries.coeff (R := O) (n + 1)) hH
    rw [PowerSeries.coeff_C, if_neg (by omega : n + 1 ≠ 0), sub_mul, map_sub, PowerSeries.coeff_succ_X_mul,
      PowerSeries.coeff_C_mul] at hn
    linear_combination -hn
  have hmem : ∀ n, PowerSeries.coeff (R := O) 0 H ∈ (IsLocalRing.maximalIdeal O) ^ n := by
    intro n
    have hpow : PowerSeries.coeff (R := O) 0 H = a ^ n * PowerSeries.coeff (R := O) n H := by
      induction n with
      | zero => simp
      | succ n ih => rw [ih, hrec n, pow_succ]; ring
    rw [hpow]
    exact Ideal.mul_mem_right _ _ (Ideal.pow_mem_pow ha n)
  have h0 : PowerSeries.coeff (R := O) 0 H = 0 := by
    apply IsHausdorff.haus' (I := IsLocalRing.maximalIdeal O)
    intro n
    rw [SModEq.sub_mem, sub_zero, smul_eq_mul, Ideal.mul_top]
    exact hmem n
  have hc := congrArg (PowerSeries.coeff (R := O) 0) hH
  rw [PowerSeries.coeff_zero_C, sub_mul, map_sub, PowerSeries.coeff_zero_X_mul, PowerSeries.coeff_C_mul, h0,
    mul_zero, sub_zero] at hc
  exact sub_eq_zero.mp hc

theorem ev_zero {a : O} (ha : a ∈ IsLocalRing.maximalIdeal O) {c : O}
    (h : Ideal.Quotient.mk (Ia a) (C c) = 0) : c = 0 := by
  exact ev_inj ha (by rw [h, map_zero, map_zero])

end Ev

theorem ev_subst {O : Type*} [CommRing O] {P : PowerSeries O} (hP : constantCoeff P = 0) {a b c : O}
    {F : PowerSeries O}
    (hPb : Ideal.Quotient.mk (Ideal.span {X - C a}) P = Ideal.Quotient.mk (Ideal.span {X - C a}) (C b))
    (hF : Ideal.Quotient.mk (Ideal.span {X - C b}) F = Ideal.Quotient.mk (Ideal.span {X - C b}) (C c)) :
    Ideal.Quotient.mk (Ideal.span {X - C a}) (PowerSeries.subst P F) =
      Ideal.Quotient.mk (Ideal.span {X - C a}) (C c) := by
  have hs : HasSubst P := HasSubst.of_constantCoeff_zero' hP
  rw [Ideal.Quotient.mk_eq_mk_iff_sub_mem, Ideal.mem_span_singleton'] at hF
  obtain ⟨k, hk⟩ := hF
  rw [Ideal.Quotient.mk_eq_mk_iff_sub_mem] at hPb ⊢
  have e : PowerSeries.subst P F - C c = PowerSeries.subst P k * (P - C b) := by
    have := congrArg (PowerSeries.subst P) hk
    rw [subst_mul hs, subst_sub hs, subst_sub hs, subst_X hs, subst_C, subst_C] at this
    exact this.symm
  rw [e]; exact Ideal.mul_mem_left _ _ hPb

section Dvd

variable {O : Type*} [CommRing O] [IsLocalRing O] [IsDomain O]
  [IsAdicComplete (IsLocalRing.maximalIdeal O) O]

theorem prod_dvd (T : Finset O) (hT : ∀ t ∈ T, t ∈ IsLocalRing.maximalIdeal O) (f : PowerSeries O)
    (hf : ∀ t ∈ T, Ideal.Quotient.mk (Ia t) f = 0) : (∏ t ∈ T, (X - C t)) ∣ f := by
  classical
  induction T using Finset.induction_on generalizing f with
  | empty => simp
  | @insert t0 T ht0 ih =>
    rw [Finset.prod_insert ht0]
    have h0 : (X - C t0) ∣ f :=
      Ideal.mem_span_singleton.mp (Ideal.Quotient.eq_zero_iff_mem.mp (hf t0 (Finset.mem_insert_self _ _)))
    obtain ⟨g, rfl⟩ := h0
    apply mul_dvd_mul_left
    apply ih (fun t ht => hT t (Finset.mem_insert_of_mem ht))
    intro t ht
    have htm := hT t (Finset.mem_insert_of_mem ht)
    obtain ⟨c, hc⟩ := ev_exists htm g
    have hft := hf t (Finset.mem_insert_of_mem ht)
    have key : Ideal.Quotient.mk (Ia t) (C ((t - t0) * c)) = 0 := by
      rw [← hft]
      simp only [map_mul, map_sub, mk_X, hc]
    have hz := ev_zero htm key
    have hne : t - t0 ≠ 0 := sub_ne_zero.mpr (fun h => ht0 (h ▸ ht))
    have hc0 : c = 0 := (mul_eq_zero.mp hz).resolve_left hne
    rw [hc, hc0, map_zero, map_zero]

end Dvd

section Order

variable {O : Type*} [CommRing O] [IsLocalRing O]

theorem card_le_of_dvd {f v k : PowerSeries O} {s : ℕ} (T : Finset O)
    (hT : ∀ t ∈ T, t ∈ IsLocalRing.maximalIdeal O) (hv : IsUnit v)
    (hf : f.map (IsLocalRing.residue O) = (X ^ s * v).map (IsLocalRing.residue O))
    (hk : f = (∏ t ∈ T, (X - C t)) * k) :
    T.card ≤ s ∧ (T.card = s → IsUnit k) := by
  set κ := IsLocalRing.ResidueField O
  have hprod : (∏ t ∈ T, (X - C t) : PowerSeries O).map (IsLocalRing.residue O) = X ^ T.card := by
    rw [map_prod]
    rw [Finset.prod_congr rfl fun t ht => (map_residue_X_sub_C (hT t ht))]
    rw [Finset.prod_const]
  have e : (X : PowerSeries κ) ^ s * v.map (IsLocalRing.residue O) =
      X ^ T.card * k.map (IsLocalRing.residue O) := by
    rw [← map_X (IsLocalRing.residue O), ← map_pow, ← map_mul, ← hf, hk, map_mul, hprod, map_X]
  have hv' : constantCoeff (v.map (IsLocalRing.residue O)) ≠ 0 := by
    have := (hv.map (PowerSeries.map (IsLocalRing.residue O)))
    rw [isUnit_iff_constantCoeff] at this
    exact this.ne_zero
  have hX : (X : PowerSeries κ) ≠ 0 := X_ne_zero
  by_cases hle : T.card ≤ s
  · refine ⟨hle, fun hcs => ?_⟩
    rw [hcs] at e
    have e2 := mul_left_cancel₀ (pow_ne_zero _ hX) e
    rw [isUnit_iff_constantCoeff]
    by_contra hnu
    apply hv'
    rw [e2, ← coeff_zero_eq_constantCoeff_apply, coeff_map, coeff_zero_eq_constantCoeff_apply,
      (IsLocalRing.residue_eq_zero_iff _).mpr ((IsLocalRing.mem_maximalIdeal _).mpr hnu)]
  · exfalso
    replace hle := not_le.mp hle
    have e2 : (X : PowerSeries κ) ^ s * v.map (IsLocalRing.residue O) =
        X ^ s * (X ^ (T.card - s) * k.map (IsLocalRing.residue O)) := by
      rw [e, ← mul_assoc, ← pow_add, Nat.add_sub_cancel' hle.le]
    have e3 := mul_left_cancel₀ (pow_ne_zero _ hX) e2
    apply hv'
    rw [e3, map_mul, map_pow, constantCoeff_X, zero_pow (by omega), zero_mul]

end Order

end DualFramesAlt.eigenRingInvariants

namespace DualFramesAlt.eigenRingInvariants

open PowerSeries Formalism.IrreducibleCountingLemmas.WindowSums

variable {l : ℕ} [hl : Fact l.Prime]

section O

variable {O : Type*} [CommRing O] [Algebra ℤ_[l] O] {a ζ : O}

end O

end DualFramesAlt.eigenRingInvariants

namespace DualFramesAlt.eigenRingInvariants

open PowerSeries Formalism.IrreducibleCountingLemmas.WindowSums Classical

variable {l : ℕ} [hl : Fact l.Prime]

section Act

variable {O : Type*} [CommRing O] [Algebra ℤ_[l] O]

variable [IsDomain O]

end Act

end DualFramesAlt.eigenRingInvariants

namespace DualFramesAlt.eigenRingInvariants

open PowerSeries Formalism.IrreducibleCountingLemmas.WindowSums Classical

variable {l : ℕ} [hl : Fact l.Prime]

section Fiber

variable {O : Type*} [CommRing O] [IsDomain O] [IsLocalRing O] [Algebra ℤ_[l] O]

variable [IsAdicComplete (IsLocalRing.maximalIdeal O) O]

end Fiber

end DualFramesAlt.eigenRingInvariants
end

