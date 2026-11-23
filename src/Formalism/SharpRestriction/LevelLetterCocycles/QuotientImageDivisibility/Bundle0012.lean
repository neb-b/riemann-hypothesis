module

public import Mathlib
public import Formalism.SharpRestriction.LevelLetterCocycles.QuotientImageDivisibility.Bundle0011
public import Formalism.SharpRestriction.LevelLetterCocycles.QuotientImageDivisibility.Bundle0001
public import Formalism.SharpRestriction.LevelLetterCocycles.QuotientImageDivisibility.FrobeniusUniformizerPowDvd
public import Formalism.SharpRestriction.LevelLetterCocycles.QuotientImageDivisibility.SmulSZeroSplit
public import Formalism.SharpRestriction.LevelLetterCocycles.WachFrobeniusLatticeUnramifiedFunctor
public import Formalism.SharpRestriction.LevelLetterCocycles.Bundle0021

@[expose] public section

-- bundled from Formalism.SharpRestriction.LevelLetterCocycles.QuotientImageDivisibility.EvAtPsIff
section
noncomputable section
open Classical

namespace Formalism.MainNotions.N.Pv.LocalLengthBound.LB

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.ArcLiftingSetup Formalism.MainNotions.UnusedSlot80 Formalism.MainNotions.N.Ln03

section Bs

variable {O : Type} [CommRing O] [IsLocalRing O] [IsAdicComplete (IsLocalRing.maximalIdeal O) O]
  (p : ℕ) [Fact p.Prime] (hlm : ((p : ℕ) : O) ∈ IsLocalRing.maximalIdeal O)
  {F : Type} [Field F] [Algebra O F] [Algebra ℤ_[p] O] [IsDomain O] [CharZero O]

theorem evR_bs (s : ℕ) {x : F} (hx : Polynomial.aeval x (Zp (O := O) p (s + 1)) = 0) (ζ : F)
    (hxζ : x = ζ - 1) (z : ℤ_[p]) :
    evR p (s + 1) hlm hx (PowerSeries.binomialSeries O z) =
      ζ ^ (PadicInt.toZModPow (s + 1) z).val := by
  set A := (PadicInt.toZModPow (s + 1) z).val with hA
  have hker : z - (A : ℤ_[p]) ∈ Ideal.span {(p : ℤ_[p]) ^ (s + 1)} := by
    rw [← PadicInt.ker_toZModPow, RingHom.mem_ker, map_sub, map_natCast, hA,
      ZMod.natCast_zmod_val, sub_self]
  obtain ⟨w, hw⟩ := Ideal.mem_span_singleton'.1 hker
  have hz : z = (A : ℤ_[p]) + (((p ^ (s + 1) : ℕ)) : ℤ_[p]) * w := by
    push_cast; linear_combination -hw
  have hN : 1 ≤ p ^ (s + 1) := Nat.one_le_pow _ _ (Fact.out : p.Prime).pos
  rw [hz, PowerSeries.binomialSeries_add, PowerSeries.binomialSeries_nat,
    ← Formalism.MainNotions.UnusedSlot80.LG.subst_bs (p ^ (s + 1)) hN w, map_mul, evR_onePow,
    show 1 + x = ζ by rw [hxζ]; ring]
  have h0 : Polynomial.aeval (0 : F) (Zp (O := O) p (s + 1)) = 0 := root_Zp p (s + 1) (by simp)
  have hsub := evR_subst p (s + 1) hlm hx h0 ((1 + PowerSeries.X) ^ (p ^ (s + 1)) - 1)
    (by simp) (evR_Zs p (s + 1) hlm hx) (PowerSeries.binomialSeries O w)
  rw [hsub, evR_eq_cc p (s + 1) hlm h0 rfl, PowerSeries.binomialSeries_constantCoeff, map_one, mul_one]

end Bs

section Main

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {LL O : Type} [Field LL] [Algebra Qp LL] [TopologicalSpace LL] [CommRing O] [Algebra O LL]
    {v : AddValuation LL (WithTop ℚ)} {n : ℕ}
    {PD : PeriodData G Qp K₀ K B BdR} (W : LocWach PD LL O v n)
    [IsLocalRing O] [IsAdicComplete (IsLocalRing.maximalIdeal O) O] [hpF : Fact PD.p.Prime]
    [IsDomain O] [CharZero O]
    (hlm : ((PD.p : ℕ) : O) ∈ IsLocalRing.maximalIdeal O)
    (F : Type) [Field F] [Algebra O F]

theorem evAt_ps (a : ZMod n) (s t : ℕ) (ζ : Rs F PD.p s) :
    ∃ hy : Polynomial.aeval ((ζ : F) ^ (PD.p ^ t) - 1) (Zp (O := O) PD.p (s + 1)) = 0,
      evAt hlm F a s ζ (ps W t) =
        evR PD.p (s + 1) hlm hy (W.π₀₁ + ((PD.p : ℕ) : PowerSeries O)) := by
  have hl : 2 ≤ PD.p := hpF.out.two_le
  have hy : Polynomial.aeval ((ζ : F) ^ (PD.p ^ t) - 1) (Zp (O := O) PD.p (s + 1)) = 0 :=
    root_Zp PD.p (s + 1) (by rw [add_sub_cancel, ← pow_mul, mul_comm, pow_mul,
      rs_pow_N F PD.p s ζ, one_pow])
  refine ⟨hy, ?_⟩
  have hφ := Formalism.MainNotions.UnusedSlot80.LG.phi_pow_X W.φ₀ PD.p hl (Formalism.MainNotions.UnusedSlot80.LG.φ₀_X_eq W) t
  have h0 : PowerSeries.constantCoeff ((W.φ₀ ^ t) PowerSeries.X) = 0 := by rw [hφ]; simp
  rw [evAt_apply, Formalism.MainNotions.UnusedSlot80.LG.ps_apply W t a, Formalism.MainNotions.UnusedSlot80.LG.algHom_eq_subst _ h0, hφ]
  refine evR_subst PD.p (s + 1) hlm (rs_root F s ζ) hy _ (by simp) ?_ _
  rw [map_sub, evR_onePow, map_one, add_sub_cancel]

theorem evAt_ps_iff (hR : Formalism.MainNotions.UnusedSlot80.ToolsR.RingP W) [CharZero F] (a : ZMod n) (s t : ℕ)
    (ζ : Rs F PD.p s) : evAt hlm F a s ζ (ps W t) = 0 ↔ t = s := by
  obtain ⟨hy, he⟩ := evAt_ps W hlm F a s t ζ
  rw [he, ev_qp W hlm F hR s hy, add_sub_cancel]
  have hζ : IsPrimitiveRoot (ζ : F) (PD.p ^ (s + 1)) :=
    (mem_primitiveRoots (pos_pow PD.p s)).1 ζ.2
  have hp1 : 1 < PD.p := hpF.out.one_lt
  constructor
  · rintro ⟨hne, hpow⟩
    by_contra hts
    rcases Nat.lt_or_gt_of_ne hts with h | h
    ·
      have hprim := hζ.pow_of_dvd (pow_ne_zero t hpF.out.ne_zero)
        (pow_dvd_pow PD.p (by omega : t ≤ s + 1))
      rw [Nat.pow_div (by omega) hpF.out.pos] at hprim
      have hd := hprim.dvd_of_pow_eq_one PD.p hpow
      have h1 := Nat.le_of_dvd hpF.out.pos hd
      have h2 : PD.p ^ 2 ≤ PD.p ^ (s + 1 - t) := Nat.pow_le_pow_right hpF.out.pos (by omega)
      have h3 : PD.p < PD.p ^ 2 := by nlinarith
      omega
    ·
      apply hne
      rw [sub_eq_zero]
      obtain ⟨k, hk⟩ : PD.p ^ (s + 1) ∣ PD.p ^ t := pow_dvd_pow PD.p (by omega)
      rw [hk, pow_mul, hζ.pow_eq_one, one_pow]
  · rintro rfl
    have hprim := hζ.pow_of_dvd (pow_ne_zero t hpF.out.ne_zero)
      (pow_dvd_pow PD.p (by omega : t ≤ t + 1))
    rw [Nat.pow_div (by omega) hpF.out.pos, show t + 1 - t = 1 by omega, pow_one] at hprim
    exact ⟨sub_ne_zero.2 (hprim.ne_one hp1), hprim.pow_eq_one⟩

end Main

end Formalism.MainNotions.N.Pv.LocalLengthBound.LB
end
end

-- bundled from Formalism.SharpRestriction.LevelLetterCocycles.QuotientImageDivisibility.HasSubstPi0Series
section
noncomputable section
open Classical

namespace Formalism.MainNotions.N.Pv.LocalLengthBound

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc TensorProduct Formalism.MainNotions.N.Pv.LocalLengthBound.Ser

section CritB

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : PeriodData G Qp K₀ K B BdR} {LL O : Type} [Field LL] [Algebra Qp LL] [TopologicalSpace LL]
    [CommRing O] [Algebra O LL] {v : AddValuation LL (WithTop ℚ)} {n : ℕ} (W : LocWach PD LL O v n)

theorem hasSubst_pi0_series (hR : Formalism.MainNotions.UnusedSlot80.ToolsR.RingP W) : PowerSeries.HasSubst W.π₀₁ :=
  PowerSeries.HasSubst.of_constantCoeff_zero (Formalism.MainNotions.UnusedSlot80.ToolsR.π₀₁_cc hR)

def at0Hom (hR : Formalism.MainNotions.UnusedSlot80.ToolsR.RingP W) : PowerSeries O →+* LetA O n :=
  Pi.ringHom fun _ => (PowerSeries.substAlgHom (hasSubst_pi0_series W hR)).toRingHom

theorem at0Hom_apply (hR : Formalism.MainNotions.UnusedSlot80.ToolsR.RingP W) (f : PowerSeries O) :
    at0Hom W hR f = Formalism.MainNotions.RamifiedCoefficientChains.Sh.at0 W f := by
  funext i
  show (PowerSeries.substAlgHom (hasSubst_pi0_series W hR)) f = PowerSeries.subst W.π₀₁ f
  rw [PowerSeries.coe_substAlgHom]

theorem evalZero_X_eq_pi0 (hR : Formalism.MainNotions.UnusedSlot80.ToolsR.RingP W) :
    Formalism.MainNotions.RamifiedCoefficientChains.Sh.at0 W PowerSeries.X = W.π₀ := by
  funext i
  exact PowerSeries.subst_X (hasSubst_pi0_series W hR)

theorem evalZero_C (o : O) : Formalism.MainNotions.RamifiedCoefficientChains.Sh.at0 W (PowerSeries.C o) = algebraMap O (LetA O n) o := by
  funext i
  simp [Formalism.MainNotions.RamifiedCoefficientChains.Sh.at0, PowerSeries.subst_C, PowerSeries.algebraMap_eq]
  rfl

theorem evalZero_mul (hR : Formalism.MainNotions.UnusedSlot80.ToolsR.RingP W) (f g : PowerSeries O) :
    Formalism.MainNotions.RamifiedCoefficientChains.Sh.at0 W (f * g) = Formalism.MainNotions.RamifiedCoefficientChains.Sh.at0 W f * Formalism.MainNotions.RamifiedCoefficientChains.Sh.at0 W g := by
  rw [← at0Hom_apply W hR, ← at0Hom_apply W hR, ← at0Hom_apply W hR, map_mul]

theorem qp_unit_EE (hR : Formalism.MainNotions.UnusedSlot80.ToolsR.RingP W) :
    IsUnit (algebraMap (LetA O n) W.EE (Formalism.MainNotions.LiftingTheory.qp W)) := by
  obtain ⟨w, hw⟩ := hR.2.2.1
  have hπ₀ : IsUnit (algebraMap (LetA O n) W.EE W.π₀) := by
    rw [hw, map_mul, map_pow]
    exact (w.isUnit.map _).mul (W.EE_π.pow _)
  obtain ⟨U, hU⟩ := hπ₀
  haveI := W.EE_complete
  have hJ : ((PD.p : ℕ) : W.EE) ∈ (⊥ : Ideal W.EE).jacobson :=
    IsAdicComplete.le_jacobson_bot (Ideal.span {((PD.p : ℕ) : W.EE)})
      (Ideal.subset_span (Set.mem_singleton _))
  have h1 : IsUnit (((PD.p : ℕ) : W.EE) * ((U⁻¹ : W.EEˣ) : W.EE) + 1) :=
    Ideal.mem_jacobson_bot.1 hJ _
  have e : algebraMap (LetA O n) W.EE (Formalism.MainNotions.LiftingTheory.qp W) =
      (U : W.EE) * (((PD.p : ℕ) : W.EE) * ((U⁻¹ : W.EEˣ) : W.EE) + 1) := by
    rw [mul_add, mul_one, ← mul_assoc, mul_comm (U : W.EE), mul_assoc, Units.mul_inv, mul_one, hU]
    simp [Formalism.MainNotions.LiftingTheory.qp, map_add (f := _), map_natCast, add_comm]
  rw [e]
  exact U.isUnit.mul h1

theorem qp_pow_cancel (hR : Formalism.MainNotions.UnusedSlot80.ToolsR.RingP W) (T : LocLat G Qp LL O) (k : ℕ)
    {x y : W.DD T} (h : Formalism.MainNotions.LiftingTheory.qp W ^ k • x = Formalism.MainNotions.LiftingTheory.qp W ^ k • y) : x = y := by
  have hu : IsUnit (algebraMap (LetA O n) W.EE (Formalism.MainNotions.LiftingTheory.qp W ^ k)) := by
    rw [map_pow]; exact (qp_unit_EE W hR).pow _
  rw [← algebraMap_smul W.EE (Formalism.MainNotions.LiftingTheory.qp W ^ k) x,
    ← algebraMap_smul W.EE (Formalism.MainNotions.LiftingTheory.qp W ^ k) y] at h
  exact hu.smul_left_cancel.1 h

end CritB

end Formalism.MainNotions.N.Pv.LocalLengthBound
end
end

-- bundled from Formalism.SharpRestriction.LevelLetterCocycles.QuotientImageDivisibility.LemKD
section
noncomputable section
open Classical

namespace Formalism.MainNotions.N.Pv.LocalLengthBound

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc


set_option maxHeartbeats 800000 in
theorem lemK_D (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW)
    (Cm : CmpOf D.loc D.locA HW F) (CR CA CB CK : ℝ) (hA : Formalism.MainNotions.RamifiedCoefficientChains.admitted D HW F Cm CR CA CB CK)
    (hL : Formalism.MainNotions.UnusedSlot80.LevCoeff D HW F) :
    Formalism.MainNotions.WachCoordinates.AtCaseA fun l _ K LL h => Formalism.MainNotions.RamifiedCoefficientChains.Sh.LemK ((HW l).W K 1 LL h.2.2) := by
  intro l _ K LL hA' h5
  have : FiniteDimensional ℚ_[l] ↥LL.1 := LL.2
  haveI := Formalism.MainNotions.UnusedSlot80.neZero_finrank_max_unramified K
  have h1 := hA.1 l K 1 LL hA'.2.2
  have h11 := hA.2.2.2.2.2.2.2.2.2.2.1 l K LL
  have hs := (HW l).W_s K 1 LL hA'.2.2
  have hp : ((D.loc l).PD K).p ≠ 2 := by rw [(D.loc l).PD_p]; exact hA'.2.1
  have hP9 : Formalism.MainNotions.DeltaInvariantLattices.P9 D HW F := fun l _ K s LL h => (hA.1 l K s LL h).2.2.2.2.2.2.2.2.1
  have hring : Formalism.MainNotions.UnusedSlot80.ToolsR.RingP ((HW l).W K 1 LL hA'.2.2) :=
    (((h1.2.2.2.2.2.2.2.2.1 _ (Formalism.MainNotions.LiftingTheory.gen_one_crys ((HW l).W K 1 LL hA'.2.2))) hs hp).2.2
      (Formalism.MainNotions.UnusedSlot80.finrank_K0_eq_one_of_le_Kur hA'.1)).1
  have tie := ((Cm l).C K 1 LL hA'.2.2).tie
  set_option synthInstance.maxHeartbeats 800000 in
   obtain ⟨hN, hAg⟩ := gam_of_tie _ hs tie
   exact lemK_of _ inferInstance (Formalism.MainNotions.UnusedSlot80.BCF.isFrac_OL LL) h1.1 h1.2.2.1 (hL l K LL hA' h5)
    h1.2.2.2.2.1 h11.2.2 hring hN hAg (gamΔ_of_tie _ tie) (ptTrans_rec D HW F hP9 l K LL hA' h5)

end Formalism.MainNotions.N.Pv.LocalLengthBound
end
end

