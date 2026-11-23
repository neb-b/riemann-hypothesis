module

public import Mathlib
public import Formalism.SharpRestriction.LevelLetterCocycles.DvrLatticeRank.Bundle0002
public import Formalism.WeaklyAdmissibleFiltrations.Statement
public import Formalism.SharpRestriction.LevelLetterCocycles.DvrLatticeRank.FrameAbs
public import Formalism.SharpRestriction.LevelLetterCocycles.DvrLatticeRank.Bundle0001

@[expose] public section

-- bundled from Formalism.SharpRestriction.LevelLetterCocycles.DvrLatticeRank.BlockProductRing
section
namespace DualFramesAlt.BlockProductRing

open PowerSeries

theorem prod_div_block {M : Type*} [CommMonoid M] (m : ℕ) (hm : 0 < m) (g : ℕ → M) (e : ℕ) :
    ∏ k ∈ Finset.range (m * e), g (k / m) = ∏ j ∈ Finset.range e, g j ^ m := by
  induction e with
  | zero => simp
  | succ e ih =>
    rw [mul_add_one, Finset.prod_range_add, ih, Finset.prod_range_succ]
    congr 1
    have hc : ∀ x ∈ Finset.range m, g ((m * e + x) / m) = g e := by
      intro x hx
      rw [Finset.mem_range] at hx
      congr 1
      rw [Nat.add_comm, Nat.add_mul_div_left _ _ hm, Nat.div_eq_of_lt hx, zero_add]
    rw [Finset.prod_congr rfl hc, Finset.prod_const, Finset.card_range]

theorem prod_ite_block {M : Type*} [CommMonoid M] (m : ℕ) (hm : 0 < m) (x : M) (k : ℕ) :
    ∏ i ∈ Finset.range k, (if i / m = k / m then x else 1) = x ^ (k % m) := by
  rw [Finset.prod_ite, Finset.prod_const_one, mul_one, Finset.prod_const]
  congr 1
  have hset : Finset.filter (fun i => i / m = k / m) (Finset.range k) = Finset.Ico (m * (k / m)) k := by
    ext i
    simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_Ico]
    constructor
    · rintro ⟨hik, hd⟩
      refine ⟨?_, hik⟩
      rw [← hd]
      exact Nat.mul_div_le i m
    · rintro ⟨hle, hik⟩
      refine ⟨hik, le_antisymm (Nat.div_le_div_right hik.le) ?_⟩
      rw [Nat.le_div_iff_mul_le hm, mul_comm]
      exact hle
  rw [hset, Nat.card_Ico]
  have h := Nat.mod_add_div k m
  generalize m * (k / m) = q at h ⊢
  generalize k % m = r at h ⊢
  omega

theorem dvd_of_mk_eq {O : Type*} [CommRing O] {y c : O} {F : PowerSeries O}
    (h : Ideal.Quotient.mk (DualFramesAlt.eigenRingInvariants.Ia y) F = Ideal.Quotient.mk (DualFramesAlt.eigenRingInvariants.Ia y) (C c)) :
    ∃ H, F - C c = (X - C y) * H := by
  obtain ⟨H, hH⟩ := Ideal.mem_span_singleton.mp (Ideal.Quotient.eq.mp h)
  exact ⟨H, hH⟩

theorem mk_eq_of_mem {O : Type*} [CommRing O] {y : O} {F G : PowerSeries O} (h : F - G ∈ DualFramesAlt.eigenRingInvariants.Ia y) :
    Ideal.Quotient.mk (DualFramesAlt.eigenRingInvariants.Ia y) F = Ideal.Quotient.mk (DualFramesAlt.eigenRingInvariants.Ia y) G :=
  Ideal.Quotient.eq.mpr h

theorem mem_of_factor {O : Type*} [CommRing O] (y : O) (F : PowerSeries O) :
    (X - C y) * F ∈ DualFramesAlt.eigenRingInvariants.Ia y :=
  Ideal.mem_span_singleton.mpr (dvd_mul_right _ _)

end DualFramesAlt.BlockProductRing
end

-- bundled from Formalism.SharpRestriction.LevelLetterCocycles.DvrLatticeRank.FrMultVOfNotJump
section
set_option linter.unusedVariables false

noncomputable section

namespace Formalism.MainNotions.N.Ln34.UniversalFiltration

open Formalism.WeaklyAdmissibleFiltrations Module TensorProduct

theorem tele (f : ℤ → ℤ) (m : ℤ) (d : ℕ) :
    ∑ a ∈ Finset.Ico m (m + d), (f a - f (a + 1)) = f m - f (m + d) := by
  induction d with
  | zero => simp
  | succ d ih =>
    have hI : Finset.Ico m (m + ((d + 1 : ℕ) : ℤ)) = insert (m + d) (Finset.Ico m (m + d)) := by
      ext x
      simp only [Finset.mem_Ico, Finset.mem_insert]
      push_cast
      omega
    rw [hI, Finset.sum_insert (by simp), ih]
    push_cast
    ring

section Fil

variable {G : Type} [Group G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    (PD : PeriodData G Qp K₀ K B BdR)
    {LL : Type} [Field LL] [Algebra Qp LL]
    {V : Type} [AddCommGroup V] [Module LL V] [Module Qp V] [IsScalarTower Qp LL V]

theorem fr_filV_succ (a : ℤ) : FilV PD (LL := LL) (V := V) (a + 1) ≤ FilV PD (LL := LL) (V := V) a := by
  rintro x ⟨t, rfl⟩
  induction t using TensorProduct.induction_on with
  | zero => rw [map_zero]; exact zero_mem _
  | tmul v b =>
    exact LinearMap.mem_range.2 ⟨v ⊗ₜ ⟨b.1, PD.Fil_anti a b.2⟩, by simp⟩
  | add s t hs ht =>
    rw [map_add (f := _)]
    exact add_mem hs ht

theorem fr_filV_anti : Antitone (fun a : ℤ => FilV PD (LL := LL) (V := V) a) := antitone_int_of_succ_le fun a => fr_filV_succ PD a

theorem fr_filV_exh (x : V ⊗[Qp] BdR) : ∃ a : ℤ, x ∈ FilV PD (LL := LL) (V := V) a := by
  induction x using TensorProduct.induction_on with
  | zero => exact ⟨0, zero_mem _⟩
  | tmul v b =>
    obtain ⟨a, ha⟩ := PD.Fil_exh b
    exact ⟨a, LinearMap.mem_range.2 ⟨v ⊗ₜ ⟨b, ha⟩, by simp⟩⟩
  | add x y hx hy =>
    obtain ⟨a, ha⟩ := hx
    obtain ⟨a', ha'⟩ := hy
    exact ⟨min a a', add_mem (fr_filV_anti PD (min_le_left a a') ha)
      (fr_filV_anti PD (min_le_right a a') ha')⟩

theorem fr_filV_fd (U : Submodule LL (V ⊗[Qp] BdR)) [FiniteDimensional LL ↥U] :
    ∃ a : ℤ, U ≤ FilV PD (LL := LL) (V := V) a := by
  classical
  have hfin : ∀ s : Finset (V ⊗[Qp] BdR), ∃ a : ℤ, ∀ x ∈ s, x ∈ FilV PD (LL := LL) (V := V) a := by
    intro s
    induction s using Finset.induction_on with
    | empty => exact ⟨0, by simp⟩
    | insert y s hy ih =>
      obtain ⟨a, ha⟩ := ih
      obtain ⟨b, hb⟩ := fr_filV_exh PD (LL := LL) y
      refine ⟨min a b, fun x hx => ?_⟩
      rcases Finset.mem_insert.1 hx with rfl | hx
      · exact fr_filV_anti PD (min_le_right a b) hb
      · exact fr_filV_anti PD (min_le_left a b) (ha x hx)
  obtain ⟨s, hs⟩ := (Submodule.fg_iff_finiteDimensional U).2 inferInstance
  obtain ⟨a, ha⟩ := hfin s
  exact ⟨a, hs ▸ Submodule.span_le.2 fun x hx => ha x hx⟩

theorem fr_filV_sep (x : V ⊗[Qp] BdR) (hx : ∀ a, x ∈ FilV PD (LL := LL) (V := V) a) : x = 0 := by
  classical
  let bV := Module.Basis.ofVectorSpace Qp V
  let e := TensorProduct.equivFinsuppOfBasisLeft (N := BdR) bV
  have hmem : ∀ a (y : V ⊗[Qp] BdR), y ∈ FilV PD (LL := LL) (V := V) a → ∀ i, e y i ∈ PD.Fil a := by
    intro a y hy i
    obtain ⟨t, rfl⟩ := LinearMap.mem_range.1 hy
    clear hy
    induction t using TensorProduct.induction_on with
    | zero => simp
    | tmul v b =>
      simp only [AlgebraTensorModule.map_tmul, LinearMap.id_apply, Submodule.coe_subtype, e,
        TensorProduct.equivFinsuppOfBasisLeft_apply_tmul, Finsupp.mapRange_apply]
      exact Submodule.smul_of_tower_mem _ _ b.2
    | add s t hs ht =>
      rw [map_add (f := _), map_add (f := _), Finsupp.add_apply]
      exact add_mem hs ht
  have hz : e x = 0 := by
    ext i
    exact PD.Fil_sep _ fun a => hmem a x (hx a) i
  exact e.injective (hz.trans (map_zero e).symm)

variable (ρ : Representation LL G V)

theorem fr_fildR_anti (τ : K →ₐ[Qp] LL) : Antitone (FildR PD ρ τ) := fun a b hab => inf_le_inf_left _ (fr_filV_anti PD hab)

theorem fr_fildR_lo (τ : K →ₐ[Qp] LL) [FiniteDimensional LL ↥(DdRE PD ρ τ)] :
    ∃ lo : ℤ, ∀ a ≤ lo, FildR PD ρ τ a = DdRE PD ρ τ := by
  obtain ⟨lo, hlo⟩ := fr_filV_fd PD (LL := LL) (V := V) (DdRE PD ρ τ)
  refine ⟨lo, fun a ha => ?_⟩
  unfold FildR
  exact inf_eq_left.2 (hlo.trans (fr_filV_anti PD ha))

theorem fr_fildR_hi (τ : K →ₐ[Qp] LL) [FiniteDimensional LL ↥(DdRE PD ρ τ)] :
    ∃ hi : ℤ, ∀ a, hi ≤ a → FildR PD ρ τ a = ⊥ := by
  classical
  have hfd : ∀ a, FiniteDimensional LL ↥(FildR PD ρ τ a) := fun a =>
    Submodule.finiteDimensional_of_le inf_le_left
  have hex : ∃ n : ℕ, ∃ a : ℤ, finrank LL ↥(FildR PD ρ τ a) = n := ⟨_, 0, rfl⟩
  obtain ⟨a0, ha0⟩ := Nat.find_spec hex
  have hmin : ∀ a, finrank LL ↥(FildR PD ρ τ a0) ≤ finrank LL ↥(FildR PD ρ τ a) := by
    intro a
    rw [ha0]
    exact Nat.find_min' hex ⟨a, rfl⟩
  haveI := hfd a0
  have hstab : ∀ a, a0 ≤ a → FildR PD ρ τ a = FildR PD ρ τ a0 := fun a ha =>
    Submodule.eq_of_le_of_finrank_le (fr_fildR_anti PD ρ τ ha) (hmin a)
  have hbot : FildR PD ρ τ a0 = ⊥ := by
    rw [eq_bot_iff]
    intro x hx
    rw [Submodule.mem_bot]
    apply fr_filV_sep PD (LL := LL) x
    intro b
    rcases le_total a0 b with h | h
    · rw [← hstab b h] at hx
      exact hx.2
    · exact fr_filV_anti PD h hx.2
  exact ⟨a0, fun a ha => by rw [hstab a ha, hbot]⟩

theorem fr_multV_of_not_jump (τ : K →ₐ[Qp] LL) (a : ℤ) (h : ¬ IsJumpV PD ρ τ a) :
    multV PD ρ τ a = 0 := by
  unfold IsJumpV at h
  unfold multV
  rw [not_not.1 h, sub_self]

theorem fr_sum_multV (τ : K →ₐ[Qp] LL) (m k : ℤ) (hmk : m ≤ k) :
    ∑ a ∈ Finset.Ico m k, multV PD ρ τ a =
      (finrank LL ↥(FildR PD ρ τ m) : ℤ) - finrank LL ↥(FildR PD ρ τ k) := by
  obtain ⟨d, rfl⟩ : ∃ d : ℕ, k = m + d := ⟨(k - m).toNat, by omega⟩
  exact tele (fun a => (finrank LL ↥(FildR PD ρ τ a) : ℤ)) m d

end Fil

end Formalism.MainNotions.N.Ln34.UniversalFiltration
end
end

-- bundled from Formalism.SharpRestriction.LevelLetterCocycles.DvrLatticeRank.FramePfMat
section
noncomputable section

namespace Formalism.MainNotions.N.Ln34

open PowerSeries DualFramesAlt.FrameAbs

variable {O : Type} [CommRing O] [IsDomain O] {d : ℕ}

theorem framepf_cc_subst (Fs g : PowerSeries O) :
    constantCoeff (subst ((X : PowerSeries O) * Fs) g) = constantCoeff g := by
  have h0 : PowerSeries.constantCoeff ((X : PowerSeries O) * Fs) = 0 := by simp
  have ha : PowerSeries.HasSubst ((X : PowerSeries O) * Fs) :=
    PowerSeries.HasSubst.of_constantCoeff_zero h0
  refine (PowerSeries.constantCoeff_subst (R := O) ha g).trans ?_
  rw [finsum_eq_single _ 0]
  · simp
  · intro n hn
    rw [map_pow]
    change coeff n g • (PowerSeries.constantCoeff ((X : PowerSeries O) * Fs)) ^ n = 0
    rw [h0, zero_pow hn, smul_zero]

theorem framepf_mem_span_X (a : PowerSeries O) :
    a ∈ Ideal.span {(X : PowerSeries O)} ↔ constantCoeff a = 0 := by
  rw [Ideal.mem_span_singleton, PowerSeries.X_dvd_iff]

theorem framepf_mats (c₀ : O) (hc : ∀ y : ℕ, 1 ≤ y → c₀ ^ y ≠ 1) (Fs : PowerSeries O)
    (hF : constantCoeff Fs = c₀) (R : Matrix (Fin d) (Fin d) (PowerSeries O)) (M : ℕ) (hM : 1 ≤ M)
    (aσ lσ : O) (hl : lσ = aσ * ∏ y ∈ Finset.Ico 1 M, (c₀ ^ y - 1)) :
    ∃ H H' : Matrix (Fin d) (Fin d) (PowerSeries O),
      (∃ K, H = C lσ • 1 + (X : PowerSeries O) • K) ∧
      (∃ K, (1 + (X : PowerSeries O) • R) * H.map (subst ((X : PowerSeries O) * Fs)) - H =
        (X : PowerSeries O) ^ M • K) ∧
      (∃ K, H' = C lσ • 1 + (X : PowerSeries O) • K) ∧
      (∃ K, H' * (1 + (X : PowerSeries O) • R) - H'.map (subst ((X : PowerSeries O) * Fs)) =
        (X : PowerSeries O) ^ M • K) ∧
      (∃ K, H' * H = C (lσ ^ 2) • 1 + (X : PowerSeries O) ^ M • K) ∧
      (∃ K, H * H' = C (lσ ^ 2) • 1 + (X : PowerSeries O) ^ M • K) := by
  classical
  have hG : HasSubst ((X : PowerSeries O) * Fs) := HasSubst.of_constantCoeff_zero' (by simp)
  set σr : PowerSeries O →+* PowerSeries O := (substAlgHom hG).toRingHom with hσr
  have hσ : ∀ g, σr g = subst ((X : PowerSeries O) * Fs) g := fun g => by
    simp [σr, coe_substAlgHom]
  set Γ : Matrix (Fin d) (Fin d) (PowerSeries O) := 1 + (X : PowerSeries O) • R with hΓ
  set ev : ℕ → PowerSeries O := fun y => C (c₀ ^ y - 1) with hev
  have hAC : ∀ o : O, algebraMap O (PowerSeries O) o = C o := fun o => by
    rw [PowerSeries.algebraMap_apply]; rfl
  have hyp : Hyp O σr Γ X ev := by
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · intro a
      rw [framepf_mem_span_X, map_sub, hσ, framepf_cc_subst, sub_self]
    · rw [hΓ, add_sub_cancel_left]
      exact MatIn.smul_self _ _
    · rw [PowerSeries.isUnit_iff_constantCoeff, RingHom.map_det]
      have : (constantCoeff : PowerSeries O →+* O).mapMatrix Γ = 1 := by
        ext p q
        simp [hΓ, Matrix.one_apply]
      rw [this, Matrix.det_one]
      exact isUnit_one
    · exact mem_nonZeroDivisors_of_ne_zero X_ne_zero
    · intro y
      rw [hσ, subst_pow hG, subst_X hG, hev]
      rw [Ideal.mem_span_singleton]
      obtain ⟨t, ht⟩ := sub_dvd_pow_sub_pow Fs (C c₀) y
      have hX : (X : PowerSeries O) ∣ Fs - C c₀ := by
        rw [X_dvd_iff, map_sub, constantCoeff_C, hF, sub_self]
      obtain ⟨u, hu⟩ := hX
      refine ⟨u * t, ?_⟩
      have e : C (c₀ ^ y - 1) + 1 = (C c₀) ^ y := by simp
      rw [e, mul_pow, mul_comm ((C c₀) ^ y), ← mul_sub, ht, hu, pow_succ]
      ring
    · intro y
      rw [hσ, hev, subst_C]
      rfl
    · intro y a hy h
      rw [framepf_mem_span_X] at h ⊢
      rw [map_mul, constantCoeff_C] at h
      exact (mul_eq_zero.1 h).resolve_left (sub_ne_zero.2 (hc y hy))
    · intro o
      rw [hσ, ← PowerSeries.coe_substAlgHom hG, AlgHom.commutes]
    · intro a
      refine ⟨constantCoeff a, ?_⟩
      rw [framepf_mem_span_X, map_sub, hAC, constantCoeff_C, sub_self]
    · intro o h
      rw [framepf_mem_span_X, hAC, constantCoeff_C] at h
      exact h
    · intro y
      exact ⟨c₀ ^ y - 1, by rw [hAC]⟩
  have hD : ∏ y ∈ Finset.Ico 1 M, ev y = C (∏ y ∈ Finset.Ico 1 M, (c₀ ^ y - 1)) := by
    rw [hev, map_prod]
  have hc' : ∀ a : PowerSeries O, (∏ y ∈ Finset.Ico 1 M, ev y) * a ∈ Ideal.span {(X : PowerSeries O) ^ M} →
      a ∈ Ideal.span {(X : PowerSeries O) ^ M} := by
    intro a h
    rw [Ideal.mem_span_singleton, X_pow_dvd_iff] at h ⊢
    intro j hj
    have := h j hj
    rw [hD, coeff_C_mul] at this
    exact (mul_eq_zero.1 this).resolve_left
      (Finset.prod_ne_zero_iff.2 fun y hy => sub_ne_zero.2 (hc y (Finset.mem_Ico.1 hy).1))
  obtain ⟨⟨H, hH⟩, -⟩ := exists_frame hyp M hM
  obtain ⟨F, hF'⟩ := exists_dualFrame hyp M hM
  obtain ⟨hFH, hHF⟩ := frame_products hyp M hM H F hH hF' hc'
  have hmap : ∀ Z : Matrix (Fin d) (Fin d) (PowerSeries O), Z.map σr = Z.map (subst ((X : PowerSeries O) * Fs)) := by
    intro Z; ext p q; simp [hσ]
  obtain ⟨K1, hK1⟩ := hH.1.exists_smul
  obtain ⟨K2, hK2⟩ := hH.2.exists_smul
  obtain ⟨K3, hK3⟩ := hF'.1.exists_smul
  obtain ⟨K4, hK4⟩ := hF'.2.exists_smul
  obtain ⟨K5, hK5⟩ := hFH.exists_smul
  obtain ⟨K6, hK6⟩ := hHF.exists_smul
  have hσa : σr (C aσ) = C aσ := by rw [hσ, subst_C]; rfl
  rw [hD] at hK1 hK3 hK5 hK6
  have e1 := (sub_eq_iff_eq_add.1 hK1).trans (add_comm _ _)
  have e3 := (sub_eq_iff_eq_add.1 hK3).trans (add_comm _ _)
  have e5 := (sub_eq_iff_eq_add.1 hK5).trans (add_comm _ _)
  have e6 := (sub_eq_iff_eq_add.1 hK6).trans (add_comm _ _)
  have hsc : ∀ Z : Matrix (Fin d) (Fin d) (PowerSeries O), (C aσ • Z).map σr = C aσ • Z.map σr := by
    intro Z; ext p q; simp [hσa]
  have hsq : C aσ * C aσ * C (∏ y ∈ Finset.Ico 1 M, (c₀ ^ y - 1)) ^ 2 = C (lσ ^ 2) := by
    rw [hl, ← map_mul, ← map_pow, ← map_mul]; ring_nf
  refine ⟨C aσ • H, C aσ • F, ⟨C aσ • K1, ?_⟩, ⟨C aσ • K2, ?_⟩, ⟨C aσ • K3, ?_⟩, ⟨C aσ • K4, ?_⟩,
    ⟨(C aσ * C aσ) • K5, ?_⟩, ⟨(C aσ * C aσ) • K6, ?_⟩⟩
  · rw [e1, smul_add, smul_smul, ← map_mul, ← hl, smul_comm (C aσ) (X : PowerSeries O) K1]
  · rw [← hmap, hsc, Matrix.mul_smul, ← smul_sub, hK2, smul_comm]
  · rw [e3, smul_add, smul_smul, ← map_mul, ← hl, smul_comm (C aσ) (X : PowerSeries O) K3]
  · rw [← hmap, hsc, Matrix.smul_mul, ← smul_sub, hK4, smul_comm]
  · rw [Matrix.smul_mul, Matrix.mul_smul, smul_smul, e5, smul_add, smul_smul, smul_comm _ _ K5, hsq]
  · rw [Matrix.smul_mul, Matrix.mul_smul, smul_smul, e6, smul_add, smul_smul, smul_comm _ _ K6, hsq]

end Formalism.MainNotions.N.Ln34

end
end

