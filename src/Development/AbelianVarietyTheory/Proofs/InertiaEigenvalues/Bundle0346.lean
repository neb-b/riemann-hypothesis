module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.ApplyLayers
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0006
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0227
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0150
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.OneAddXMulDerivativeBinomial
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsStratHom
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0005
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.UnramifiedIntegersTensorEqLetterwiseProductAinf
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0056

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LevLawsOfEvLaw
section
noncomputable section

namespace GlobalTheory.NL

open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct GlobalTheory.HWL PowerSeries

section Generic

variable {l : ℕ} [Fact l.Prime] {O L : Type} [CommRing O] [Field L] [CharZero L] [Algebra ℚ L] [Algebra ℤ_[l] O]
    [Algebra ℤ_[l] L] [Algebra O L] [IsScalarTower ℤ_[l] O L] {v : AddValuation L (WithTop ℚ)}
    {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR] {PD : PeriodData G Qp K₀ K B BdR}
    [Algebra Qp L] [TopologicalSpace L] {n : ℕ}

def levOne (W : LocWach PD L O v n) (i : ZMod n) (ζ : L) : O⟦X⟧ →ₐ[O] L⟦X⟧ :=
  (W.lev i ζ).comp (Pi.constAlgHom O (ZMod n) O⟦X⟧)


omit [CharZero L] [Algebra ℚ L] in
theorem lev_eq_levOne (W : LocWach PD L O v n) (i : ZMod n) (ζ : L) (f : LetA O n) :
    W.lev i ζ f = levOne W i ζ (f i) := by
  have h := W.lev_letter i ζ (f - Pi.constAlgHom O (ZMod n) O⟦X⟧ (f i)) (sub_self (f i))
  rw [map_sub, sub_eq_zero] at h
  exact h

theorem levOne_X (W : LocWach PD L O v n) (i : ZMod n) {ζ : L} (h : ∃ j : ℕ, IsPrimitiveRoot ζ (PD.p ^ j)) :
    levOne W i ζ X = C ζ * exp L - 1 := by
  obtain ⟨E, h0, h1, h2⟩ := W.lev_π i ζ h
  have hE : E = exp L := PowerSeries.exp_unique_of_derivative_eq_self h1 h0
  rw [← hE, ← h2, add_sub_cancel_left]
  rfl

theorem levLaws_of_evLaw [IsDomain O] (hl0 : (l : O) ≠ 0) (hlu : ¬ IsUnit (l : O)) (W : LocWach PD L O v n)
    (hp : PD.p = l) (c : W.Gam → ℤ_[l]) (hc : ∀ g, algebraMap ℤ_[l] O (c g) = (W.χΓ g : O))
    (hv : ∀ (c : ℤ_[l]) (j a : ℕ), (j : WithTop ℚ) ≤ v (algebraMap ℤ_[l] L c - (a : L)) →
      (l : ℤ_[l]) ^ j ∣ c - a) (H : Ser.EvLaw l (O := O) v inferInstance) : LevLaws W := by
  have hc' : ∀ g, algebraMap O L (W.χΓ g : O) = algebraMap ℤ_[l] L (c g) :=
    fun g => by rw [← hc, ← IsScalarTower.algebraMap_apply]
  have hpr : PD.p.Prime := hp ▸ (Fact.out : l.Prime)
  have hφX : W.φ₀ X = (1 + X) ^ l - 1 := by rw [W.φ₀_X, W.q₀_def, hp]
  have hφ : W.φ₀ = GlobalTheory.Fon.phi0 l O :=
    GlobalTheory.Cyc.algHom_ext_of_constantCoeff_zero _ _ (by rw [hφX, GlobalTheory.Fon.cyclotomicFrobeniusPowerSeries_X]) (by rw [hφX]; simp)
  have hγ : ∀ g, W.γ₀ g = GlobalTheory.Fon.gam O (c g) := fun g =>
    GlobalTheory.Cyc.algHom_ext_of_constantCoeff_zero _ _
      (GlobalTheory.Cyc.eq_of_commute_pow l hl0 hlu W.φ₀ _ _ hφX (W.γ₀_comm g _) (by rw [hφ]; exact GlobalTheory.Fon.cyclotomicFrobenius_comm_gammaAction _ _ _)
        (W.γ₀_X g).1 (GlobalTheory.Fon.constantCoeff_gam_X _ _)
        (by rw [(W.γ₀_X g).2, GlobalTheory.Fon.coeff_one_gam_X, hc])) (W.γ₀_X g).1
  constructor
  · rintro g i ζ _ j a h hj rfl f
    rw [hc'] at hj ⊢
    rw [lev_eq_levOne, lev_eq_levOne]
    change levOne W i ζ (W.γ₀ g (f i)) = _
    rw [hγ]
    exact Ser.ev_gam H (hp ▸ h.pow_eq_one) _ (hv _ j a hj) (levOne_X W i ⟨j, h⟩)
      (levOne_X W i (root_pow hpr ⟨j, h⟩ a)) (f i)
  · rintro i ζ ⟨j, h⟩ f
    rw [lev_eq_levOne, lev_eq_levOne]
    change levOne W i ζ (W.φ₀ (f (i - 1))) = _
    have := Ser.ev_gam H (hp ▸ h.pow_eq_one) (l : ℤ_[l]) (a := l) (by simp) (levOne_X W i ⟨j, h⟩)
      (levOne_X W (i - 1) (root_pow hpr ⟨j, h⟩ l)) (f (i - 1))
    rw [GlobalTheory.Fon.gam_l, map_natCast] at this
    rw [hφ, hp]
    exact this

end Generic

section Concrete

variable {l : ℕ} [Fact l.Prime] {P : LocPrime l} {AI : LocAinf l P} (H : LocHW l P) (F : LocFon l P AI H)
  {K : FinExt l} {s : ℕ} {LL : FinExt l} (h : Good K s LL)

theorem levLaws : LevLaws (H.W K s LL h) := by
  obtain ⟨_, -, h0, hu, -⟩ := GlobalTheory.Per.integers_completeDVR l LL
  obtain ⟨c, hc⟩ := Ser.exists_padic_char (GamL H h)
  refine levLaws_of_evLaw h0 hu _ (P.PD_p K) (fun g => (c g : ℤ_[l])) hc (Ser.dvd_of_le_v P) ?_
  convert Ser.evLaw_integers P LL using 1
  exact Algebra.algebra_ext _ _ fun r => PowerSeries.algebraMap_apply

theorem ioLaws_tie : IoLaws (F.E K s LL h).tie := by
  set_option synthInstance.maxHeartbeats 100000 in
    exact ⟨GlobalTheory.HWL.Back.ioE_φ (O := ↥(OL LL)) Subtype.val_injective _,
    GlobalTheory.HWL.Back.ioE_γ (O := ↥(OL LL)) Subtype.val_injective _⟩

theorem one_crys : IsCrys (P.PD K) (H.W K s LL h).one.ρ :=
  haveI : FiniteDimensional ℚ_[l] ↥LL.1 := LL.2
  GlobalTheory.TrivCrys.isCrys_lat_of_trivial _ (H.W K s LL h).one_triv

end Concrete

theorem laws : ∀ {l : ℕ} [Fact l.Prime] {P : LocPrime l} {AI : LocAinf l P} (H : LocHW l P) (F : LocFon l P AI H)
    {K : FinExt l} {s : ℕ} {LL : FinExt l} (h : Good K s LL), Laws H F h :=
  fun H F _ _ _ h => ⟨levLaws H h, ioLaws_tie H F h, one_crys H h⟩

end GlobalTheory.NL
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LocalPeriodRingsSectionEqAinfToBdRPlus
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP GlobalTheory.MemLoc
open scoped Formalism.Per NNReal

noncomputable section

namespace GlobalTheory.SeedSec

theorem eq_of_pow_eq_self {R K : Type} [CommRing R] [Field K] [CharZero K] (θ : R →+* K)
    (hθ : ∀ y, θ y ≠ 0 → IsUnit y) {n : ℕ} (hn : 2 ≤ n) {u v : R} (hu : u ^ n = u) (hv : v ^ n = v)
    (h : θ u = θ v) : u = v := by
  set S := ∑ i ∈ Finset.range n, u ^ i * v ^ (n - 1 - i) with hS
  have h1 : S * (u - v) = u - v := by rw [hS, geom_sum₂_mul, hu, hv]
  have hc : θ u ^ n = θ u := by rw [← map_pow, hu]
  have e : θ S = n * θ u ^ (n - 1) := by
    set_option synthInstance.maxHeartbeats 100000 in
      rw [hS, map_sum, Finset.sum_congr rfl (g := fun _ => θ u ^ (n - 1)) (fun i hi => by
      have := Finset.mem_range.1 hi
      rw [map_mul, map_pow, map_pow, ← h, ← pow_add]
      congr 1
      omega)]
    simp
  have h2 : θ (S - 1) ≠ 0 := by
    rw [map_sub, map_one, e]
    by_cases h0 : θ u = 0
    · rw [h0, zero_pow (by omega)]
      simp
    · have h3 : θ u ^ (n - 1) = 1 := by
        refine mul_right_cancel₀ h0 ?_
        rw [← pow_succ, Nat.sub_add_cancel (by omega), one_mul, hc]
      rw [h3, mul_one, sub_ne_zero]
      exact_mod_cast (show n ≠ 1 by omega)
  have h4 : (S - 1) * (u - v) = 0 := by rw [sub_mul, h1, one_mul, sub_self]
  exact sub_eq_zero.1 ((hθ _ h2).mul_right_eq_zero.1 h4)

theorem exists_om_of_pow_eq_self (l : ℕ) [Fact l.Prime] {n : ℕ} (hn : 2 ≤ n) (c : ℂ_[l]) (hc : c ^ n = c) :
    ∃ x : Om l, algebraMap (Om l) ℂ_[l] x = c := by
  have hs : (Polynomial.X ^ n - Polynomial.X : Polynomial (Om l)).Splits := IsAlgClosed.splits _
  have h0 : (Polynomial.X ^ n - Polynomial.X : Polynomial (Om l)) ≠ 0 := fun h => by
    have := congrArg (fun p : Polynomial (Om l) => p.coeff n) h
    simp [Polynomial.coeff_X_pow, Polynomial.coeff_X, show (1 : ℕ) ≠ n by omega] at this
  obtain ⟨x, hx⟩ := hs.mem_range_of_isRoot h0 (i := algebraMap (Om l) ℂ_[l]) (x := c) (by simp [hc])
  exact ⟨x, hx⟩

private theorem padicInt_hom_apply_eq {l : ℕ} [Fact l.Prime] {R : Type} [CommRing R]
    (hR : IsHausdorff (Ideal.span {(l : R)}) R) (f g : ℤ_[l] →+* R) (z : ℤ_[l]) : f z = g z := by
  rw [← sub_eq_zero]
  refine IsHausdorff.haus hR _ fun n => ?_
  obtain ⟨c, hc⟩ := Ideal.mem_span_singleton'.1 (PadicInt.appr_spec n z)
  rw [SModEq.zero, smul_eq_mul, Ideal.mul_top, Ideal.span_singleton_pow, Ideal.mem_span_singleton']
  refine ⟨f c - g c, ?_⟩
  have hf := congrArg f hc
  have hg := congrArg g hc
  simp only [map_mul, map_pow, map_natCast, map_sub] at hf hg
  linear_combination hf - hg

theorem exists_sec (l : ℕ) [Fact l.Prime] (a : ℕ) [NeZero a] (C : Core l) (w : Wq l a) :
    ∃ x : Om l, ((Per.θ l (wA l a w) : OC l) : ℂ_[l]) = algebraMap (Om l) ℂ_[l] x ∧
      C.o x = aDp l (wA l a w) := by
  have hspan : w ∈ Submodule.span ℤ_[l] (Set.range (WittVector.teichmuller l : Fq l a → Wq l a)) := by
    rw [span_teich]; trivial
  induction hspan using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨z, rfl⟩ := hy
    have hq : 2 ≤ l ^ a := one_lt_pow_l l a
    have hw : (WittVector.teichmuller l z) ^ (l ^ a) = WittVector.teichmuller l z := by
      rw [← map_pow, Fq.pow_card]
    set A := wA l a (WittVector.teichmuller l z) with hAdef
    have hA : A ^ (l ^ a) = A := by rw [hAdef, ← map_pow, hw]
    have hc : ((Per.θ l A : OC l) : ℂ_[l]) ^ (l ^ a) = ((Per.θ l A : OC l) : ℂ_[l]) := by
      rw [← SubmonoidClass.coe_pow, ← map_pow, hA]
    obtain ⟨x, hx⟩ := exists_om_of_pow_eq_self l hq _ hc
    have hxq : x ^ (l ^ a) = x := (algebraMap (Om l) ℂ_[l]).injective (by rw [map_pow, hx, hc])
    refine ⟨x, hx.symm, eq_of_pow_eq_self (Per.θD l) (thetaD_props l).2.2.1 hq
      (by rw [← map_pow, hxq]) (by rw [← map_pow, hA]) ?_⟩
    rw [C.o_sec.th, (thetaD_props l).2.2.2.1]
    exact hx
  | zero => exact ⟨0, by simp, by simp⟩
  | add y y' _ _ hy hy' =>
    obtain ⟨x, hx1, hx2⟩ := hy
    obtain ⟨x', hx1', hx2'⟩ := hy'
    refine ⟨x + x', ?_, ?_⟩
    · rw [map_add (f := _), map_add (f := _), map_add (f := _), Subring.coe_add, hx1, hx1']
    · rw [map_add (f := _), map_add (f := _), map_add (f := _), hx2, hx2']
  | smul r y _ hy =>
    obtain ⟨x, hx1, hx2⟩ := hy
    have e : wA l a (r • y) = algebraMap ℤ_[l] (Ainf l) r * wA l a y := by
      rw [map_smul, Algebra.smul_def]
    refine ⟨algebraMap ℚ_[l] (Om l) (r : ℚ_[l]) * x, ?_, ?_⟩
    · rw [e, map_mul, Subring.coe_mul, hx1, map_mul]
      congr 1
      exact GlobalTheory.UnramIdem.ringHom_eq ((Per.θ l).comp (algebraMap ℤ_[l] (Ainf l))) r
    · rw [e, map_mul, map_mul, hx2, C.o_sec.z r]
      have hA : IsAdicComplete (Ideal.span {(l : Ainf l)}) (Ainf l) := inferInstance
      rw [padicInt_hom_apply_eq hA.toIsHausdorff (Per.zA l) (algebraMap ℤ_[l] (Ainf l)) r]

theorem o_eq_aDp_wA : ∀ (l : ℕ) [Fact l.Prime] (a : ℕ) [NeZero a] (C : Core l) (w : Wq l a) (x : Om l),
    ((Per.θ l (wA l a w) : OC l) : ℂ_[l]) = (x : ℂ_[l]) → C.o x = aDp l (wA l a w) := by
  intro l _ a _ C w x hx
  obtain ⟨y, hy1, hy2⟩ := exists_sec l a C w
  have hxy : x = y := (algebraMap (Om l) ℂ_[l]).injective (hx.symm.trans hy1)
  rw [hxy, hy2]

end GlobalTheory.SeedSec
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MemBreuilKisinIdealPowOfNormLe
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal

namespace GlobalTheory.BSP

theorem exists_of_mem_ball_small {l : ℕ} (hl : 1 < l) {A : Type} [CommRing A] (u : A) {ρ : ℝ≥0} (h0 : 0 < ρ)
    (h1 : ρ < 1) (m n : ℕ) {y : PreDisc l u ρ} (hy : y ∈ ball l u ρ ((ρ : ℝ) ^ m / (l : ℝ) ^ n)) :
    ∃ (c : ℕ) (z₁ z₂ : A), algebraMap A (PreDisc l u ρ) ((l : A) ^ c) * y =
      algebraMap A (PreDisc l u ρ) (u ^ m * z₁ + (l : A) ^ (c + n) * z₂) := by
  have hl1 : (1 : ℝ) < l := by exact_mod_cast hl
  have hρ0 : (0 : ℝ) < ρ := h0
  have hρ1 : (ρ : ℝ) ≤ 1 := h1.le
  induction hy using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨a, b, c, hw, rfl⟩ := hx
    have e : algebraMap A (PreDisc l u ρ) ((l : A) ^ c) * (algebraMap A (PreDisc l u ρ) ((l : A) ^ a * u ^ b) *
        IsLocalization.Away.invSelf (l : A) ^ c) = algebraMap A (PreDisc l u ρ) ((l : A) ^ a * u ^ b) := by
      rw [map_pow, mul_left_comm, ← mul_pow, IsLocalization.Away.mul_invSelf, one_pow, mul_one]
    rcases le_or_gt m b with hb | hb
    · obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hb
      refine ⟨c, (l : A) ^ a * u ^ k, 0, ?_⟩
      rw [e]; congr 1; ring
    · have hp : (ρ : ℝ) ^ m ≤ (ρ : ℝ) ^ b := pow_le_pow_of_le_one hρ0.le hρ1 hb.le
      have h2 : (l : ℝ) ^ (c + n) ≤ (l : ℝ) ^ a := by
        rw [div_mul_eq_mul_div, le_div_iff₀ (by positivity)] at hw
        have h3 : (l : ℝ) ^ (c + n) * (ρ : ℝ) ^ b ≤ (l : ℝ) ^ a * (ρ : ℝ) ^ b :=
          calc (l : ℝ) ^ (c + n) * (ρ : ℝ) ^ b = (l : ℝ) ^ c * (ρ : ℝ) ^ b * (l : ℝ) ^ n := by ring
            _ ≤ _ := hw
            _ ≤ (ρ : ℝ) ^ b * (l : ℝ) ^ a := mul_le_mul_of_nonneg_right hp (by positivity)
            _ = _ := mul_comm _ _
        exact le_of_mul_le_mul_right h3 (by positivity)
      obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le ((pow_le_pow_iff_right₀ hl1).1 h2)
      refine ⟨c, 0, (l : A) ^ k * u ^ b, ?_⟩
      rw [e]; congr 1; ring
  | zero => exact ⟨0, 0, 0, by simp⟩
  | add x y _ _ hx hy =>
    obtain ⟨c, z₁, z₂, h⟩ := hx
    obtain ⟨c', z₁', z₂', h'⟩ := hy
    refine ⟨c + c', (l : A) ^ c' * z₁ + (l : A) ^ c * z₁', z₂ + z₂', ?_⟩
    simp only [map_add (f := _), map_mul, map_pow, pow_add] at h h' ⊢
    linear_combination (algebraMap A (PreDisc l u ρ) (l : A)) ^ c' * h +
      (algebraMap A (PreDisc l u ρ) (l : A)) ^ c * h'
  | smul a x _ hx =>
    obtain ⟨c, z₁, z₂, h⟩ := hx
    refine ⟨c, a * z₁, a * z₂, ?_⟩
    simp only [map_add (f := _), map_mul, map_pow, pow_add, Algebra.smul_def] at h ⊢
    linear_combination (algebraMap A (PreDisc l u ρ) a) * h

theorem exists_of_norm_toDisc_lt {l : ℕ} (hl : 1 < l) {A : Type} [CommRing A] (u : A)
    (ht : ∀ x : A, (l : A) * x = 0 → x = 0) (m : ℕ) (hd : ∀ x y : A, (l : A) * x = u ^ m * y → u ^ m ∣ x)
    {ρ : ℝ≥0} (h0 : 0 < ρ) (h1 : ρ < 1) (n : ℕ) (x : A) (hx : ‖toDisc l u ρ x‖ < (ρ : ℝ) ^ m / (l : ℝ) ^ n) :
    ∃ z₁ z₂ : A, x = u ^ m * z₁ + (l : A) ^ n * z₂ := by
  have hb : algebraMap A (PreDisc l u ρ) x ∈ ball l u ρ ((ρ : ℝ) ^ m / (l : ℝ) ^ n) :=
    mem_ball_of_gauge_lt l u ρ ((norm_ofPre l u ρ _).symm.trans_lt hx)
  obtain ⟨c, z₁, z₂, h⟩ := exists_of_mem_ball_small hl u h0 h1 m n hb
  have hn : (l : A) ∈ nonZeroDivisors A := mem_nonZeroDivisors_iff_left.2 ht
  have hi : Function.Injective (algebraMap A (PreDisc l u ρ)) :=
    IsLocalization.injective (M := Submonoid.powers (l : A)) _ (Submonoid.powers_le.2 hn)
  rw [← map_mul] at h
  have h2 := hi h
  have key : ∀ (c : ℕ) (w : A), u ^ m ∣ (l : A) ^ c * w → u ^ m ∣ w := fun c => by
    induction c with
    | zero => intro w hw; simpa using hw
    | succ c ih =>
      rintro w ⟨y, hy⟩
      exact ih w (hd _ y (by rw [← hy]; ring))
  obtain ⟨z, hz⟩ := key c (x - (l : A) ^ n * z₂) ⟨z₁, by rw [pow_add] at h2; linear_combination h2⟩
  exact ⟨z, z₂, by linear_combination hz⟩

theorem BK.X_pow_natDegree_mem_J {l : ℕ} [Fact l.Prime] {K : FinExt l} (bk : BK K) :
    (X : bk.S) ^ bk.Ep.natDegree ∈ bk.J := by
  have h := congrArg (Polynomial.coeToPowerSeries.ringHom (R := Wq l bk.a)) bk.monic.as_sum
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [map_add (f := _), map_pow, map_sum, map_mul, Polynomial.coeToPowerSeries.ringHom_apply, Polynomial.coe_X,
    Polynomial.coe_C] at h
  have e : (X : bk.S) ^ bk.Ep.natDegree =
      bk.E - ∑ i ∈ Finset.range bk.Ep.natDegree, C (bk.Ep.coeff i) * (X : bk.S) ^ i := by
    rw [eq_sub_iff_add_eq]; exact h.symm
  rw [e]
  refine sub_mem (Ideal.mem_sup_right (Ideal.mem_span_singleton_self _)) (Ideal.mem_sup_left (sum_mem fun i hi => ?_))
  obtain ⟨w, hw⟩ := bk.dvd_coeff i (Finset.mem_range.1 hi)
  rw [hw, map_mul, map_natCast, mul_assoc]
  exact Ideal.mul_mem_right _ _ (Ideal.mem_span_singleton_self _)

theorem mem_J_pow_of_norm_le : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (A : Type) [CommRing A] (s : bk.S →+* A), (∀ x : A, (l : A) * x = 0 → x = 0) → (∀ (m : ℕ) (x y : A), (l : A) * x = s X ^ m * y → s X ^ m ∣ x) → ∀ (ρ : ℝ≥0), 0 < ρ → ρ < 1 → ∀ n : ℕ, ∃ r : ℝ, 0 < r ∧ ∀ x : A, ‖toDisc l (s X) ρ x‖ ≤ r → x ∈ (bk.J ^ n).map s := by
  intro l hl K bk A _ s ht hd ρ h0 h1 n
  have hl0 : (0 : ℝ) < l := Nat.cast_pos.2 hl.out.pos
  have hρ0 : (0 : ℝ) < ρ := h0
  have hr : 0 < (ρ : ℝ) ^ (bk.Ep.natDegree * n) / (l : ℝ) ^ n := by positivity
  refine ⟨_, half_pos hr, fun x hx => ?_⟩
  obtain ⟨z₁, z₂, rfl⟩ := exists_of_norm_toDisc_lt hl.out.one_lt (s X) ht _ (hd _) h0 h1 n x
    (hx.trans_lt (half_lt_self hr))
  refine add_mem (Ideal.mul_mem_right _ _ ?_) (Ideal.mul_mem_right _ _ ?_)
  · rw [← map_pow, pow_mul]
    exact Ideal.mem_map_of_mem _ (Ideal.pow_mem_pow bk.X_pow_natDegree_mem_J n)
  · rw [← map_natCast s, ← map_pow]
    exact Ideal.mem_map_of_mem _ (Ideal.pow_mem_pow (Ideal.mem_sup_left (Ideal.mem_span_singleton_self _)) n)

end GlobalTheory.BSP
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NormBaseRingToClosedDiscJPowSmall
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal

noncomputable section

namespace GlobalTheory.BSP.DiscSmall

def ballIdeal (l : ℕ) {A : Type} [CommRing A] (u : A) (ρ : ℝ≥0) (r : ℝ) : Ideal A :=
  Submodule.comap (Algebra.linearMap A (PreDisc l u ρ)) (ball l u ρ r)

theorem mem_ballIdeal {l : ℕ} {A : Type} [CommRing A] {u : A} {ρ : ℝ≥0} {r : ℝ} {x : A} :
    x ∈ ballIdeal l u ρ r ↔ algebraMap A (PreDisc l u ρ) x ∈ ball l u ρ r := Iff.rfl

theorem ballIdeal_mul_le {l : ℕ} {A : Type} [CommRing A] {u : A} {ρ : ℝ≥0} {r s : ℝ} (hr : 0 ≤ r) :
    ballIdeal l u ρ r * ballIdeal l u ρ s ≤ ballIdeal l u ρ (r * s) :=
  Ideal.mul_le.2 fun x hx y hy => by
    rw [mem_ballIdeal, map_mul]
    exact mul_mem_ball l u ρ hr hx hy

theorem pow_le_ballIdeal {l : ℕ} {A : Type} [CommRing A] {u : A} {ρ : ℝ≥0} {r : ℝ} (hr : 0 ≤ r)
    {I : Ideal A} (hI : I ≤ ballIdeal l u ρ r) : ∀ n : ℕ, I ^ n ≤ ballIdeal l u ρ (r ^ n)
  | 0 => by
    rw [pow_zero, pow_zero, Ideal.one_eq_top]
    refine (Ideal.eq_top_of_isUnit_mem _ ?_ isUnit_one).ge
    rw [mem_ballIdeal, map_one]
    exact Submodule.subset_span ⟨0, 0, 0, by simp, by simp⟩
  | n + 1 => by
    rw [pow_succ, pow_succ]
    exact (Ideal.mul_mono (pow_le_ballIdeal hr hI n) hI).trans (ballIdeal_mul_le (pow_nonneg hr n))

theorem exists_E_eq {l : ℕ} [Fact l.Prime] {K : FinExt l} (bk : BK K) :
    ∃ q : bk.S, bk.E = (X : bk.S) ^ bk.Ep.natDegree + (l : bk.S) * q := by
  have hd : Polynomial.C (l : Wq l bk.a) ∣ bk.Ep - Polynomial.X ^ bk.Ep.natDegree := by
    refine (Polynomial.C_dvd_iff_dvd_coeff _ _).2 fun i => ?_
    rw [Polynomial.coeff_sub, Polynomial.coeff_X_pow]
    rcases lt_trichotomy i bk.Ep.natDegree with h | h | h
    · rw [if_neg h.ne, sub_zero]; exact bk.dvd_coeff i h
    · rw [h, if_pos rfl, bk.monic.coeff_natDegree, sub_self]; exact dvd_zero _
    · rw [if_neg h.ne', sub_zero, Polynomial.coeff_eq_zero_of_natDegree_lt h]; exact dvd_zero _
  obtain ⟨q, hq⟩ := hd
  have h2 : bk.Ep = Polynomial.X ^ bk.Ep.natDegree + Polynomial.C (l : Wq l bk.a) * q := by
    rw [← hq]; ring
  refine ⟨(q : bk.S), ?_⟩
  show ((bk.Ep : Polynomial (Wq l bk.a)) : (Wq l bk.a)⟦X⟧) = _
  nth_rewrite 1 [h2]
  simp [Polynomial.coe_add, Polynomial.coe_pow, Polynomial.coe_X, Polynomial.coe_mul, Polynomial.coe_C]
  left
  exact map_natCast (Polynomial.coeToPowerSeries.ringHom (R := Wq l bk.a)) l

end GlobalTheory.BSP.DiscSmall


open GlobalTheory.BSP.DiscSmall in
theorem GlobalTheory.BSP.norm_toDisc_J_pow_small : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (A : Type) [CommRing A]
    (s : bk.S →+* A) (ρ : ℝ≥0), 0 < ρ → ρ < 1 → ∀ r : ℝ, 0 < r → ∃ n : ℕ, ∀ x ∈ (bk.J ^ n).map s,
    ‖toDisc l (s X) ρ x‖ ≤ r := by
  intro l hl K bk A _ s ρ hρ0 hρ1 r hr
  have hl0 : (0 : ℝ) < l := Nat.cast_pos.2 hl.out.pos
  have hl1 : (1 : ℝ) < l := Nat.one_lt_cast.2 hl.out.one_lt
  set t : ℝ := max (1 / (l : ℝ)) ((ρ : ℝ) ^ bk.Ep.natDegree) with ht
  have ht0 : 0 < t := lt_max_of_lt_left (one_div_pos.2 hl0)
  have hρ1' : (ρ : ℝ) < 1 := by exact_mod_cast hρ1
  have ht1 : t < 1 := max_lt ((div_lt_one hl0).2 hl1) (pow_lt_one₀ ρ.2 hρ1' bk.deg_pos.ne')
  obtain ⟨n, hn⟩ := exists_pow_lt_of_lt_one hr ht1
  have hlmem : algebraMap A (PreDisc l (s X) ρ) (l : A) ∈ ball l (s X) ρ t := by
    refine Submodule.subset_span ⟨1, 0, 0, ?_, by simp⟩
    have : 1 / (l : ℝ) * l ≤ t * l := mul_le_mul_of_nonneg_right (le_max_left _ _) hl0.le
    rw [one_div_mul_cancel hl0.ne'] at this
    simpa using this
  have hJ : bk.J.map s ≤ ballIdeal l (s X) ρ t := by
    rw [Ideal.map_sup, Ideal.map_span, Ideal.map_span, Set.image_singleton, Set.image_singleton, sup_le_iff,
      Ideal.span_le, Ideal.span_le, Set.singleton_subset_iff, Set.singleton_subset_iff]
    constructor
    · show s (l : bk.S) ∈ ballIdeal l (s X) ρ t
      rw [map_natCast, mem_ballIdeal]
      exact hlmem
    · show s bk.E ∈ ballIdeal l (s X) ρ t
      obtain ⟨q, hq⟩ := exists_E_eq bk
      rw [hq, map_add (f := _), map_mul, map_pow, map_natCast, mem_ballIdeal, map_add (f := _), map_mul, mul_comm, ← Algebra.smul_def]
      refine add_mem (Submodule.subset_span ⟨0, bk.Ep.natDegree, 0, ?_, by simp⟩) (Submodule.smul_mem _ _ hlmem)
      show (l:ℝ)^0 * (ρ:ℝ)^bk.Ep.natDegree ≤ t * (l:ℝ)^0
      simp only [pow_zero, one_mul, mul_one]
      exact le_max_right _ _
  refine ⟨n, fun x hx => ?_⟩
  rw [Ideal.map_pow] at hx
  have hx' := pow_le_ballIdeal ht0.le hJ n hx
  rw [toDisc, RingHom.comp_apply, norm_ofPre]
  exact (gauge_le l (s X) ρ (pow_pos ht0 n) hx').trans hn.le
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PeriodRingCoreCrystallineDeRhamInvariants
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP GlobalTheory.MemLoc
open scoped Formalism.Per NNReal

namespace GlobalTheory.MemLoc

variable {l : ℕ} [Fact l.Prime]

theorem Fits.invB {P : LocPrime l} {AI : LocAinf l P} {T : LocTied l P AI} {C : Core l}
    (hF : Fits T C) : C.InvB := by
  intro K b hb
  set b' : P.R.B := T.eB.symm b with hb'
  have hfix : ∀ g : ↥(GK K), (P.PD K).actB g b' = b' := by
    intro g
    rw [P.PD_actB]
    apply T.eB.injective
    rw [T.actB, hb', RingEquiv.apply_symm_apply]
    exact hb g g.2
  obtain ⟨c, hc⟩ := (P.PD K).invB b' hfix
  refine ⟨IntermediateField.inclusion (inf_le_right : K0 K ≤ MaximalUnramifiedExtension l) c, (inf_le_left : K0 K ≤ K.1) c.2, ?_⟩
  rw [← hF.u]
  have : algebraMap ↥(MaximalUnramifiedExtension l) P.R.B (IntermediateField.inclusion (inf_le_right : K0 K ≤ MaximalUnramifiedExtension l) c) = b' := hc
  rw [this, hb', RingEquiv.apply_symm_apply]

theorem Fits.invdR {P : LocPrime l} {AI : LocAinf l P} {T : LocTied l P AI} {C : Core l}
    (hF : Fits T C) : C.InvdR := by
  intro K b hb
  set b' : P.R.BdR := T.eD.symm b with hb'
  have hfix : ∀ g : ↥(GK K), (P.PD K).actdR g b' = b' := by
    intro g
    rw [P.PD_actdR]
    apply T.eD.injective
    rw [T.actD, hb', RingEquiv.apply_symm_apply]
    exact hb g g.2
  obtain ⟨c, hc⟩ := (P.PD K).invdR b' hfix
  refine ⟨(c : Om l), c.2, ?_⟩
  rw [← hF.o]
  have : algebraMap (Om l) P.R.BdR (c : Om l) = b' := hc
  rw [this, hb', RingEquiv.apply_symm_apply]

theorem fits_inv : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P) (T : LocTied l P AI)
    (C : Core l), Fits T C → C.InvB ∧ C.InvdR :=
  fun _ _ _ _ _ _ hF => ⟨hF.invB, hF.invdR⟩

end GlobalTheory.MemLoc
end

