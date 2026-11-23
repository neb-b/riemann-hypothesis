module

public import Formalism.SharpRestriction.LevelLetterCocycles.Bundle0027
public import Formalism.SharpRestriction.LevelLetterCocycles.DvrLatticeRank.Bundle0007
public import Formalism.SharpRestriction.LevelLetterCocycles.Bundle0025
public import Formalism.SharpRestriction.LevelLetterCocycles.DvrLatticeRank.Bundle0008
public import Formalism.SharpRestriction.LevelLetterCocycles.DvrLatticeRank.NinLamPf
public import Mathlib
public import Formalism.SharpRestriction.LevelLetterCocycles.Bundle0031
public import Formalism.SharpRestriction.LevelLetterCocycles.DvrLatticeRank.Bundle0003
public import Formalism.SharpRestriction.LevelLetterCocycles.DvrLatticeRank.Bundle0001

@[expose] public section

-- bundled from Formalism.SharpRestriction.LevelLetterCocycles.DvrLatticeRank.ExponentRecursionHolds
section
noncomputable section

namespace Formalism.MainNotions.N.Ln34

theorem exponent_recursion_holds : ExpansionFormHypothesis := fun D HW F Cm _ _ _ hA hd hr =>
  CrystallineExponents.exponent_recursion_of_dimension D HW F Cm hA.1 hA.2.2.2.2.2.2.2.2.2.2.1 fun l _ K LL hG T hT c τ =>
    ((hr l K LL hG T hT c).trans (hd l K LL ⟨1, hG⟩ T hT τ).symm).le

end Formalism.MainNotions.N.Ln34

end
end

-- bundled from Formalism.SharpRestriction.LevelLetterCocycles.DvrLatticeRank.GradNPf
section
noncomputable section

namespace Formalism.MainNotions.N.Ln34

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Module Formalism.MainNotions.ElementDenominator Formalism.MainNotions.ElementDenominator.CongruenceModules

theorem gradNCondition : Formalism.MainNotions.N.Ln34.GradNStep := by
  intro D HW F Cm CA CB CK hA l hlp hl K LL hG π' E hR T h' hh' hT
  have h1 : adm1 D HW F Cm := hA.1
  rcases Nat.eq_zero_or_pos (sK l K) with hs0 | hs
  ·
    apply gradNPf_small
    simp [MK, hs0]
  · obtain ⟨f, t, x, u, -, -, hf, ht, hE, hΔ, hγ, hK, hN⟩ :=
      gradNPf_hyps D HW F Cm h1 l hl K LL hG π' E hR T hT hs
    rcases le_or_gt (MK l K h') 1 with hM | hM
    · apply gradNPf_small
      exact hM
    · obtain ⟨a, ha⟩ := hN (MK l K h' - 1)
      rw [Nat.sub_add_cancel (by omega : 1 ≤ MK l K h')] at ha
      refine gradNPf_local (hf := hf) (ht := ht) (hu := hE) (hπΔ := hΔ) (hγN := hγ) (hK := hK)
        (hM := by omega) (a := a) (ha := ?_)
      convert ha using 2
      · rw [(D.loc l).PD_p K]
      · rfl

end Formalism.MainNotions.N.Ln34

end
end

-- bundled from Formalism.SharpRestriction.LevelLetterCocycles.DvrLatticeRank.InvLiftPf
section
noncomputable section

namespace Formalism.MainNotions.N.Ln34

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Module Formalism.MainNotions.ElementDenominator Formalism.MainNotions.ElementDenominator.CongruenceModules


set_option maxHeartbeats 1000000 in
theorem invLiftCondition : InvLiftStep := by
  set_option synthInstance.maxHeartbeats 400000 in
  intro D HW F Cm CA CB CK hA l _ hl K LL hG π' E hπ T h' hh' hT hJ c
  haveI := ((HW l).W K 1 LL hG).ddTowO T
  have hNL : NinLam ((HW l).W K 1 LL hG) T (Formalism.MainNotions.DeltaInvariantLattices.Eat E π') h' :=
    ninlam_pf D HW F Cm CA CB CK hA l hl K LL hG π' E hπ T h' hT hJ
  rcases le_or_gt (MK l K h') 1 with hM | hM
  · refine ⟨fun w hw => ⟨((((D.loc l).PD K).p : ℕ) : ↥(OL LL)) ^ sigA l (sK l K) h' • w, ?_, ?_⟩,
      fun wb _ hwb => gradNPf_PiNS_anti _ T π' hM hwb⟩
    · obtain ⟨hwL, hwγ⟩ := (mem_InvS _ T π' _ h' 1 c w).1 hw
      refine (mem_InvS _ T π' _ h' _ c _).2 ⟨Submodule.smul_mem _ _ hwL, ?_⟩
      rw [map_smul, ← smul_sub]
      exact Submodule.smul_mem _ _ (gradNPf_PiNS_anti _ T π' hM hwγ)
    · rw [sub_self]
      exact Submodule.zero_mem _
  have hs : 1 ≤ sK l K := by
    by_contra h0
    have h0' : sK l K = 0 := by omega
    have : MK l K h' = 0 := by simp [MK, h0']
    omega
  obtain ⟨f, t, x, u, hu, hxu, hf, ht, hEE, hπΔ, hγN, hK, hprod⟩ :=
    gradNPf_hyps D HW F Cm hA.1 l hl K LL hG π' E hπ T hT hs
  have hpl : ((D.loc l).PD K).p = l := (D.loc l).PD_p K
  obtain ⟨a, ha⟩ := hprod (MK l K h' - 1)
  have hM1 : MK l K h' - 1 + 1 = MK l K h' := by omega
  rw [hM1] at ha
  have hσ : sigA l (sK l K) h' = MK l K h' - 1 + padicValNat l (MK l K h' - 1).factorial := rfl

  have hl0 : ((l : ℕ) : ↥LL.1) ≠ 0 := by
    intro h0
    have hv := (D.loc l).v_l LL
    rw [h0, AddValuation.map_zero] at hv
    exact absurd hv (by simp)
  have hℓ : ∀ c : ↥(OL LL), (l : ↥(OL LL)) * c = 0 → c = 0 := by
    intro c hc
    have h1 := congrArg (algebraMap ↥(OL LL) ↥LL.1) hc
    rw [map_mul, map_natCast, map_zero] at h1
    have h2 := (mul_eq_zero.1 h1).resolve_left hl0
    exact (injective_iff_map_eq_zero (algebraMap ↥(OL LL) ↥LL.1)).1 Subtype.val_injective c h2

  have hs1 : ((HW l).W K 1 LL hG).s = 1 := (HW l).W_s K 1 LL hG
  have hp : ((D.loc l).PD K).p ≠ 2 := by rw [hpl]; exact hl
  obtain ⟨-, -, -, -, -, -, -, -, h9W, -⟩ := hA.1 l K 1 LL hG
  obtain ⟨-, ⟨π'₀, E₀, -, hm₀⟩, -⟩ := h9W T hT hs1 hp
  obtain ⟨⟨r, b, hbΔ, huniq, -⟩, -⟩ := hm₀
  obtain ⟨w, hw⟩ := hπ.2.2.1
  have hnz : ∀ y : ℕ, 1 ≤ y → y < MK l K h' → ∀ r₀ ∈ ((HW l).W K 1 LL hG).N T,
      ∀ d ∈ ((HW l).W K 1 LL hG).N T, ((x ^ sK l K) ^ y - 1) • r₀ = π' • d →
      ∃ e ∈ ((HW l).W K 1 LL hG).N T, r₀ = π' • e := by
    intro y hy1 hyM r₀ hr₀ d hd hrd
    obtain ⟨q, hq⟩ := Finset.dvd_prod_of_mem (fun y => (x ^ sK l K) ^ y - 1)
      (Finset.mem_Ico.2 ⟨hy1, hyM⟩)
    rw [hq] at ha
    refine invLiftPf_nzd _ T π' w (sK l K) w.isUnit hw (l : ↥(OL LL)) hℓ r b
      (fun j => (hbΔ j).1) huniq (MK l K h' - 1 + padicValNat l (MK l K h' - 1).factorial) r₀
      ((a * q) • d) hr₀ ?_ ?_
    · rw [← algebraMap_smul (LetA ↥(OL LL) (finrank ℚ_[l] ↥(K0 K)))]
      exact Submodule.smul_mem _ _ hd
    · rw [ha, mul_comm ((x ^ sK l K) ^ y - 1) q, ← mul_assoc, mul_smul, hrd,
        ← algebraMap_smul (LetA ↥(OL LL) (finrank ℚ_[l] ↥(K0 K))) (a * q) (π' • d),
        ← algebraMap_smul (LetA ↥(OL LL) (finrank ℚ_[l] ↥(K0 K))) (a * q) d, smul_smul, smul_smul,
        mul_comm]
  have hpσ : (((((D.loc l).PD K).p : ℕ) : ↥(OL LL)) ^ sigA l (sK l K) h') =
      a * ∏ y ∈ Finset.Ico 1 (MK l K h'), ((x ^ sK l K) ^ y - 1) := by
    rw [hpl, hσ]
    exact ha
  have hGr : GradN ((HW l).W K 1 LL hG) T π' (sigA l (sK l K) h') (MK l K h') :=
    gradNPf_local _ T π' f t (x ^ sK l K) hf ht hEE hπΔ hγN hK _ _ (by omega) a hpσ
  refine ⟨invLiftPf_lift _ T π' _ h' _ _ c hGr hNL, fun wb hwb hwb1 => ?_⟩
  exact invLiftPf_inj _ T π' f t (x ^ sK l K) hf ht hEE hπΔ hγN hK _ hnz wb hwb1
    ((mem_InvS _ T π' _ h' _ c wb).1 hwb).2

end Formalism.MainNotions.N.Ln34

end
end

-- bundled from Formalism.SharpRestriction.LevelLetterCocycles.DvrLatticeRank.LevConstOfEv
section
noncomputable section

namespace Formalism.MainNotions.N.Ln34.UniversalLiftFrames

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Module Formalism.MainNotions.N.Ln34 PowerSeries

section PS

variable {LL : Type*} [Field LL]

theorem eq_X_mul_shift (f : PowerSeries LL) (h0 : constantCoeff f = 0) :
    f = X * mk (fun k => coeff (k + 1) f) := by
  ext n
  rcases n with _ | n
  · rw [PowerSeries.coeff_zero_X_mul, PowerSeries.coeff_zero_eq_constantCoeff_apply, h0]
  · rw [PowerSeries.coeff_succ_X_mul, PowerSeries.coeff_mk]

end PS

section Ev

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : PeriodData G Qp K₀ K B BdR} {LL O : Type} [Field LL] [Algebra Qp LL] [TopologicalSpace LL]
    [CommRing O] [Algebra O LL] {v : AddValuation LL (WithTop ℚ)} {n : ℕ}
    (W : LocWach PD LL O v n) (c : ZMod n) (ζ : LL) (Eπ : LetA O n) (h' : ℕ)

def Vs : PowerSeries LL := mk fun k => coeff (k + 1) (W.lev c ζ Eπ)

def Ui : PowerSeries LL := (Vs W c ζ Eπ)⁻¹ ^ h'

def ev (a : LetA O n) (i : ℤ) : LL :=
  if 0 ≤ i + h' then coeff (i + h').toNat (W.lev c ζ a * Ui W c ζ Eπ h') else 0

variable {W c ζ Eπ h'}

theorem levE_eq (h0 : constantCoeff (W.lev c ζ Eπ) = 0) : W.lev c ζ Eπ = X * Vs W c ζ Eπ :=
  eq_X_mul_shift _ h0

theorem Vs_cc (h1 : coeff 1 (W.lev c ζ Eπ) ≠ 0) : constantCoeff (Vs W c ζ Eπ) ≠ 0 := by
  rw [Vs, ← PowerSeries.coeff_zero_eq_constantCoeff_apply, PowerSeries.coeff_mk]
  exact h1

theorem Vs_Ui (h1 : coeff 1 (W.lev c ζ Eπ) ≠ 0) : Vs W c ζ Eπ ^ h' * Ui W c ζ Eπ h' = 1 := by
  rw [Ui, ← mul_pow, PowerSeries.mul_inv_cancel _ (Vs_cc h1), one_pow]

theorem levΛ_eq (h0 : constantCoeff (W.lev c ζ Eπ) = 0) :
    W.lev c ζ (Eπ ^ h') = X ^ h' * Vs W c ζ Eπ ^ h' := by
  rw [map_pow, levE_eq h0, mul_pow]

theorem levΛ_Ui (h0 : constantCoeff (W.lev c ζ Eπ) = 0) (h1 : coeff 1 (W.lev c ζ Eπ) ≠ 0) :
    W.lev c ζ (Eπ ^ h') * Ui W c ζ Eπ h' = X ^ h' := by
  rw [levΛ_eq h0, mul_assoc, Vs_Ui h1, mul_one]

theorem ev_of_lt (a : LetA O n) {i : ℤ} (hi : i + h' < 0) : ev W c ζ Eπ h' a i = 0 := by
  unfold ev
  rw [if_neg (by omega)]

theorem ev_eq (a : LetA O n) {i : ℤ} (hi : 0 ≤ i + h') :
    ev W c ζ Eπ h' a i = coeff (i + h').toNat (W.lev c ζ a * Ui W c ζ Eπ h') := by
  unfold ev
  rw [if_pos hi]

theorem ev_add (a b : LetA O n) (i : ℤ) :
    ev W c ζ Eπ h' (a + b) i = ev W c ζ Eπ h' a i + ev W c ζ Eπ h' b i := by
  unfold ev
  split_ifs
  · rw [map_add (W.lev c ζ) a b, add_mul, map_add (f := _)]
  · rw [add_zero]

theorem ev_zero (i : ℤ) : ev W c ζ Eπ h' (0 : LetA O n) i = 0 := by
  unfold ev
  split_ifs <;> simp

theorem ev_sum {ι : Type*} (s : Finset ι) (a : ι → LetA O n) (i : ℤ) :
    ev W c ζ Eπ h' (∑ k ∈ s, a k) i = ∑ k ∈ s, ev W c ζ Eπ h' (a k) i := by
  classical
  refine Finset.induction_on s (by rw [Finset.sum_empty, Finset.sum_empty, ev_zero]) ?_
  intro x s hx ih
  rw [Finset.sum_insert hx, Finset.sum_insert hx, ev_add, ih]

theorem ev_alg (x : O) (a : LetA O n) (i : ℤ) :
    ev W c ζ Eπ h' (algebraMap O (LetA O n) x * a) i = algebraMap O LL x * ev W c ζ Eπ h' a i := by
  unfold ev
  split_ifs
  · rw [map_mul (W.lev c ζ), AlgHom.commutes, mul_assoc, ← Algebra.smul_def, PowerSeries.coeff_smul,
      Algebra.smul_def]
  · rw [mul_zero]

theorem ev_letE (a : LetA O n) (i : ℤ) :
    ev W c ζ Eπ h' ((letE c : LetA O n) * a) i = ev W c ζ Eπ h' a i := by
  unfold ev
  rw [map_mul (W.lev c ζ), Formalism.MainNotions.N.Ln34.ModelFPf.lev_letE (W := W) c ζ, one_mul]

private theorem coeff_lev_pow_eq_zero_of_lt (h0 : constantCoeff (W.lev c ζ Eπ) = 0) (j : ℕ) (hj : j < h') :
    coeff j (W.lev c ζ (Eπ ^ h')) = 0 := by
  rw [levΛ_eq h0, PowerSeries.coeff_X_pow_mul', if_neg (by omega)]

private theorem coeff_lev_eq_sum_coeff_lev_pow_mul_ev (h0 : constantCoeff (W.lev c ζ Eπ) = 0) (h1 : coeff 1 (W.lev c ζ Eπ) ≠ 0)
    (a : LetA O n) (i : ℕ) :
    coeff i (W.lev c ζ a) = ∑ j ∈ Finset.range (i + h' + 1),
      coeff j (W.lev c ζ (Eπ ^ h')) * ev W c ζ Eπ h' a ((i : ℤ) - j) := by
  have e1 : coeff i (W.lev c ζ a) =
      coeff (i + h') (W.lev c ζ (Eπ ^ h') * (W.lev c ζ a * Ui W c ζ Eπ h')) := by
    have e : W.lev c ζ (Eπ ^ h') * (W.lev c ζ a * Ui W c ζ Eπ h') = W.lev c ζ a * X ^ h' := by
      rw [← levΛ_Ui h0 h1]
      ring
    rw [e, PowerSeries.coeff_mul_X_pow]
  rw [e1, PowerSeries.coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  refine Finset.sum_congr rfl fun j hj => ?_
  rw [Finset.mem_range] at hj
  rw [ev_eq a (by omega), show ((i : ℤ) - j + h').toNat = i + h' - j by omega]

theorem serMul_ev (h0 : constantCoeff (W.lev c ζ Eπ) = 0) (h1 : coeff 1 (W.lev c ζ Eπ) ≠ 0)
    {V : Type} [AddCommGroup V] [Module LL V] (a : LetA O n) (d : V) (i : ℤ) :
    serMul (W.lev c ζ (Eπ ^ h')) (fun k => ev W c ζ Eπ h' a k • d) i = serC (W.lev c ζ a) d i := by
  unfold serMul serC
  split_ifs with hi
  · obtain ⟨i', rfl⟩ := Int.eq_ofNat_of_zero_le hi
    rw [finsum_eq_sum_of_support_subset _ (s := Finset.range (i' + h' + 1)) ?_]
    · simp only [smul_smul, ← Finset.sum_smul]
      rw [Int.toNat_natCast, coeff_lev_eq_sum_coeff_lev_pow_mul_ev h0 h1 a i']
    · intro j hj
      rw [Function.mem_support] at hj
      rw [Finset.coe_range, Set.mem_Iio]
      by_contra hc
      apply hj
      simp only
      rw [ev_of_lt a (by omega), zero_smul, smul_zero]
  · have hz : (fun j : ℕ => coeff j (W.lev c ζ (Eπ ^ h')) •
        (fun k => ev W c ζ Eπ h' a k • d) (i - j)) = fun _ => 0 := by
      funext j
      by_cases hj : j < h'
      · rw [coeff_lev_pow_eq_zero_of_lt h0 j hj, zero_smul]
      · simp only
        rw [ev_of_lt a (by omega), zero_smul, smul_zero]
    rw [hz, finsum_zero]

theorem lev_zero_of_ev (h1 : coeff 1 (W.lev c ζ Eπ) ≠ 0) (a : LetA O n) (t₀ : ℤ)
    (h : ∀ t < t₀, ev W c ζ Eπ h' a t = 0) (i : ℕ) (hi : (i : ℤ) < t₀ + h') :
    coeff i (W.lev c ζ a) = 0 := by
  have e : W.lev c ζ a = (W.lev c ζ a * Ui W c ζ Eπ h') * Vs W c ζ Eπ ^ h' := by
    rw [mul_assoc, mul_comm (Ui W c ζ Eπ h'), Vs_Ui h1, mul_one]
  rw [e, PowerSeries.coeff_mul]
  refine Finset.sum_eq_zero fun p hp => ?_
  have hp' := Finset.HasAntidiagonal.mem_antidiagonal.mp hp
  have hev := h ((p.1 : ℤ) - h') (by omega)
  rw [ev_eq a (by omega), show ((p.1 : ℤ) - h' + h').toNat = p.1 by omega] at hev
  rw [hev, zero_mul]

theorem lev_const_of_ev (h0 : constantCoeff (W.lev c ζ Eπ) = 0) (h1 : coeff 1 (W.lev c ζ Eπ) ≠ 0)
    (a : LetA O n) (t₁ : ℤ) (h : ∀ t < t₁, t ≠ 0 → ev W c ζ Eπ h' a t = 0) (i : ℕ)
    (hi : (i : ℤ) < t₁ + h') :
    coeff i (W.lev c ζ a) = ev W c ζ Eπ h' a 0 * coeff i (W.lev c ζ (Eπ ^ h')) := by
  rw [coeff_lev_eq_sum_coeff_lev_pow_mul_ev h0 h1 a i, Finset.sum_eq_single i]
  · rw [sub_self, mul_comm]
  · intro j _ hji
    by_cases hjh : j < h'
    · rw [coeff_lev_pow_eq_zero_of_lt h0 j hjh, zero_mul]
    · rw [h ((i : ℤ) - j) (by omega) (by omega), mul_zero]
  · intro hi'
    exact absurd (Finset.mem_range.mpr (by omega)) hi'

end Ev

end Formalism.MainNotions.N.Ln34.UniversalLiftFrames
end
end

-- bundled from Formalism.SharpRestriction.LevelLetterCocycles.DvrLatticeRank.ModelLPfK
section
noncomputable section

namespace Formalism.MainNotions.N.Ln34.MLK

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Module


set_option maxHeartbeats 800000 in
theorem lev_Eat_simple (D : D7) (HW : HWOf D.loc) (l : ℕ) [Fact l.Prime] (hl : l ≠ 2) (K LL : FinExt l)
    (hG : Good K 1 LL) (π' : LetA ↥(OL LL) (finrank ℚ_[l] ↥(K0 K)))
    (E : ZMod (finrank ℚ_[l] ↥(K0 K)) → Polynomial ↥(OL LL))
    (hr : Formalism.MainNotions.DeltaInvariantLattices.wachRingRelations ((HW l).W K 1 LL hG) (eK K) (sK l K) π' E) (c : ZMod (finrank ℚ_[l] ↥(K0 K)))
    (ζ : ↥LL.1) (τ : ↥K.1 →ₐ[ℚ_[l]] ↥LL.1) (hpt : Formalism.MainNotions.DeltaInvariantLattices.ptK D.loc HW hG c ζ τ) :
    ∃ U : PowerSeries ↥LL.1, ((HW l).W K 1 LL hG).lev c ζ (Formalism.MainNotions.DeltaInvariantLattices.Eat E π') = PowerSeries.X * U ∧
      PowerSeries.constantCoeff U ≠ 0 := by
  obtain ⟨τs, hIs, -⟩ := hpt
  obtain ⟨-, hIs2⟩ := hIs
  unfold Formalism.MainNotions.DeltaInvariantLattices.wachRingRelations at hr
  obtain ⟨-, -, -, -, ⟨w, hw⟩, -, -, -⟩ := hr
  generalize (HW l).W K 1 LL hG = W at hw ⊢

  have hz : (D.loc l).ζQ 1 ^ l = 1 := by
    have h := (D.loc l).ζQ_succ 0
    rw [(D.loc l).ζQ_zero] at h
    simpa using h
  have hmem : (D.loc l).ζQ 1 ∈ Ks K 1 := by
    show (D.loc l).ζQ 1 ∈ K0 K ⊔ IntermediateField.adjoin ℚ_[l] {x : Om l | x ^ (l ^ 1) = 1}
    exact SetLike.le_def.mp le_sup_right (IntermediateField.subset_adjoin ℚ_[l] _ (by simpa using hz))
  have hζ : τs ⟨_, hmem⟩ = ζ := hIs2 ⟨_, hmem⟩ rfl
  have hζl : ζ ^ l = 1 := by
    have h1 : (⟨_, hmem⟩ : ↥(Ks K 1)) ^ l = 1 := Subtype.ext (by simpa using hz)
    rw [← hζ, ← map_pow, h1, map_one]
  have hne : ζ ≠ 1 := by
    intro h1
    have h2 : (⟨_, hmem⟩ : ↥(Ks K 1)) = 1 :=
      RingHom.injective (τs : ↥(Ks K 1) →+* ↥LL.1) (by simp [hζ, h1])
    exact (D.loc l).ζQ_one (by simpa using congrArg Subtype.val h2)
  have hprim : IsPrimitiveRoot ζ l := by
    have h := IsPrimitiveRoot.orderOf ζ
    rwa [orderOf_eq_prime hζl hne] at h
  have hl0 : ((l : ℕ) : ↥LL.1) ≠ 0 := by
    intro h
    have h' := (D.loc l).v_l LL
    rw [h, AddValuation.map_zero] at h'
    simp at h'

  obtain ⟨F, hF0, hFd, hFπ⟩ :=
    W.lev_π c ζ ⟨1, by rw [(D.loc l).PD_p K, pow_one]; exact hprim⟩
  obtain ⟨F1, hF1⟩ : PowerSeries.X ∣ F - 1 := by
    rw [PowerSeries.X_dvd_iff, map_sub, hF0, map_one, sub_self]
  have hF1c : PowerSeries.constantCoeff F1 = 1 := by
    have hd := congrArg (fun f : PowerSeries ↥LL.1 => PowerSeries.constantCoeff (PowerSeries.derivative f)) hF1
    simp only [map_sub, Derivation.map_one_eq_zero, sub_zero, hFd, hF0, Derivation.leibniz,
      PowerSeries.derivative_X, smul_eq_mul, map_add, map_mul, map_one, PowerSeries.constantCoeff_X,
      zero_mul, zero_add, mul_one] at hd
    exact hd.symm

  have hq : (letπ : LetA ↥(OL LL) (finrank ℚ_[l] ↥(K0 K))) * W.q =
      (1 + letπ) ^ ((D.loc l).PD K).p - 1 := by
    funext i
    exact W.q₀_def
  have hl1 : W.lev c ζ 1 = 1 := map_one (W.lev c ζ)
  have hadd : W.lev c ζ (1 + letπ) = 1 + W.lev c ζ letπ := by
    rw [← hl1]
    exact (W.lev c ζ).map_add 1 letπ
  have hlq := congrArg (W.lev c ζ) hq
  rw [map_mul (W.lev c ζ), map_sub (W.lev c ζ), map_pow (W.lev c ζ), hadd, hl1, hFπ, (D.loc l).PD_p K, mul_pow, ← map_pow PowerSeries.C ζ l, hζl,
    map_one PowerSeries.C, one_mul, ← mul_geom_sum, hF1, hw, map_mul (W.lev c ζ)] at hlq
  have hy0 : PowerSeries.constantCoeff (W.lev c ζ letπ) ≠ 0 := by
    have h := congrArg PowerSeries.constantCoeff hFπ
    rw [map_add (f := _), map_one, map_mul, PowerSeries.constantCoeff_C, hF0, mul_one] at h
    have h' : PowerSeries.constantCoeff (W.lev c ζ letπ) = ζ - 1 := by linear_combination h
    rw [h']
    exact sub_ne_zero.mpr hne
  obtain ⟨u, hu⟩ : IsUnit (W.lev c ζ letπ * W.lev c ζ ↑w) :=
    (PowerSeries.isUnit_iff_constantCoeff.mpr (isUnit_iff_ne_zero.mpr hy0)).mul
      (w.isUnit.map (W.lev c ζ))
  rw [← mul_assoc, ← hu] at hlq
  refine ⟨↑u⁻¹ * (F1 * ∑ i ∈ Finset.range l, F ^ i), ?_, ?_⟩
  · calc _ = ↑u⁻¹ * (↑u * W.lev c ζ (Formalism.MainNotions.DeltaInvariantLattices.Eat E π')) := by
          rw [← mul_assoc, Units.inv_mul, one_mul]
      _ = _ := by rw [hlq]; ring
  · rw [map_mul]
    refine mul_ne_zero ((u⁻¹).isUnit.map PowerSeries.constantCoeff).ne_zero ?_
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_mul, hF1c, one_mul, map_sum]
    simpa [hF0] using hl0

end Formalism.MainNotions.N.Ln34.MLK
end
end

-- bundled from Formalism.SharpRestriction.LevelLetterCocycles.DvrLatticeRank.U2ringPfBSingleMem
section
noncomputable section

open Classical

namespace Formalism.MainNotions.N.Ln34

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Module Formalism.MainNotions.ElementDenominator Formalism.MainNotions.ElementDenominator.CongruenceModules

section unitaryAbsoluteValueBounds

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : PeriodData G Qp K₀ K B BdR} {LL O : Type} [Field LL] [Algebra Qp LL] [TopologicalSpace LL]
    [CommRing O] [Algebra O LL] {v : AddValuation LL (WithTop ℚ)} {n : ℕ}
    (W : LocWach PD LL O v n)

theorem u2ringPfB_γ₀_comm (g h : W.Gam) (x : PowerSeries O) :
    W.γ₀ g (W.γ₀ h x) = W.γ₀ h (W.γ₀ g x) := by
  rw [← AlgHom.mul_apply, ← map_mul, mul_comm, map_mul, AlgHom.mul_apply]

theorem u2ringPfB_single_mem (c : ZMod n) (x : PowerSeries O) (hx : ∀ δ ∈ W.DelF, W.γ₀ δ x = x) :
    (Pi.single c x : LetA O n) ∈ W.AΔ := by
  show ∀ δ ∈ W.DelF, W.γA δ (Pi.single c x : LetA O n) = Pi.single c x
  intro δ hδ
  funext j
  show W.γ₀ δ ((Pi.single c x : LetA O n) j) = (Pi.single c x : LetA O n) j
  by_cases hj : j = c
  · subst hj
    simp only [Pi.single_eq_same]
    exact hx δ hδ
  · simp only [Pi.single_eq_of_ne hj, map_zero]

theorem u2ringPfB_letter_mem {a : LetA O n} (ha : a ∈ W.AΔ) (i : ZMod n) :
    ∀ δ ∈ W.DelF, W.γ₀ δ (a i) = a i := by
  intro δ hδ
  have h : W.γA δ a = a := ha δ hδ
  exact congrFun h i

theorem u2ringPfB_q₀_ne_zero [IsDomain O] [CharZero O] (hp : PD.p ≠ 0) : W.q₀ ≠ 0 := by
  intro h0
  have h := W.q₀_def
  rw [h0, mul_zero] at h
  have h1 := congrArg (PowerSeries.coeff 1) h.symm
  have e : ((1 + PowerSeries.X : PowerSeries O) ^ PD.p - 1) =
      ((((Polynomial.X + 1) ^ PD.p - 1 : Polynomial O)) : PowerSeries O) := by
    push_cast
    ring
  rw [e, Polynomial.coeff_coe, map_zero] at h1
  simp [Polynomial.coeff_X_add_one_pow, Polynomial.coeff_one, hp] at h1

end unitaryAbsoluteValueBounds

end Formalism.MainNotions.N.Ln34
end
end

