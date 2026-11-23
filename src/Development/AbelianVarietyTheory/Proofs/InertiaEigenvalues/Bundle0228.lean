module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.AcrisTorsionFreeComplete
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0054
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0062
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0056
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0065
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0069
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0052
public import Development.AbelianVarietyTheory.CrystallinePeriods.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0073
public import ReciprocityTheory.AdicCompleteness.IsAdicCompleteComapConstantCoeff
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.MemEurOfTeichmullerSeries
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0218
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0029
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CyclotomicTwistCocycleCoboundary
public import Formalism.SharpRestriction.LevelLetterCocycles.DataNLoc
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0010

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AssociatedPowOfUnits
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc GlobalTheory.MemLoc
open scoped Formalism.Per

namespace GlobalTheory.MemLoc.BdRDVR

section General

variable {R : Type*} [CommRing R]

theorem irreducible_of_units [IsDomain R] {x : R} (hx0 : x ≠ 0) (hxu : ¬ IsUnit x)
    (hu : ∀ y : R, ¬ x ∣ y → IsUnit y) : Irreducible x := by
  refine ⟨hxu, fun a b hab => ?_⟩
  by_cases ha : x ∣ a
  · right
    obtain ⟨c, rfl⟩ := ha
    have h1 : x * 1 = x * (c * b) := by rw [mul_one, ← mul_assoc]; exact hab
    have h2 := mul_left_cancel₀ hx0 h1
    exact IsUnit.of_mul_eq_one_right c h2.symm
  · exact Or.inl (hu a ha)

theorem associated_pow_of_units {x : R} (hu : ∀ y : R, ¬ x ∣ y → IsUnit y)
    [IsHausdorff (Ideal.span {x}) R] {y : R} (hy : y ≠ 0) : ∃ n : ℕ, Associated (x ^ n) y := by
  classical
  have hex : ∃ n : ℕ, ¬ x ^ n ∣ y := by
    by_contra h
    push_neg at h
    apply hy
    refine IsHausdorff.haus (I := Ideal.span {x}) inferInstance y fun n => ?_
    rw [SModEq.zero, smul_eq_mul, Ideal.mul_top, Ideal.span_singleton_pow, Ideal.mem_span_singleton]
    exact h n
  have hN := Nat.find_spec hex
  have hN0 : Nat.find hex ≠ 0 := by
    intro h0
    rw [h0, pow_zero] at hN
    exact hN (one_dvd _)
  obtain ⟨m, hm⟩ := Nat.exists_eq_succ_of_ne_zero hN0
  have hmin : x ^ m ∣ y := by
    have := Nat.find_min hex (m := m) (by omega)
    exact not_not.1 this
  obtain ⟨c, rfl⟩ := hmin
  have hc : IsUnit c := hu c fun hxc => hN (by
    rw [hm, pow_succ]
    exact mul_dvd_mul_left _ hxc)
  exact ⟨m, hc.unit, rfl⟩

end General

theorem core_dvr (l : ℕ) [Fact l.Prime] (C : Core l) : C.DVR := by
  have he := core_isEps l C
  obtain ⟨hdom, hinj, hfield, hden⟩ := BdRField.bdR_isField l
  obtain ⟨hfil, hreg, hcomp, -⟩ := filtration_eq_xi_pow l C.ε he
  obtain ⟨-, hker, hunit, -, -⟩ := thetaD_props l
  obtain ⟨-, ht1, ht2, -⟩ := core_t_unit_fil l C
  have hden' := hden C.ε he
  clear hden
  generalize aDp l (xi C.ε) = x at hfil hreg hcomp hden'
  have hθ : ∀ y : Per.BdRp l, Per.θD l y = 0 ↔ x ∣ y := fun y => by
    rw [hker, hfil, pow_one]
  have hu : ∀ y : Per.BdRp l, ¬ x ∣ y → IsUnit y := fun y hy => hunit y fun h => hy ((hθ y).1 h)
  have hx0 : x ≠ 0 := fun h => one_ne_zero (hreg 1 (by rw [h, zero_mul]))
  have hxu : ¬ IsUnit x := fun h => (h.map (Per.θD l)).ne_zero ((hθ x).2 dvd_rfl)
  have hirr : Irreducible x := irreducible_of_units hx0 hxu hu
  haveI : IsHausdorff (Ideal.span {x}) (Per.BdRp l) := hcomp.toIsHausdorff
  haveI hdvr : IsDiscreteValuationRing (Per.BdRp l) :=
    IsDiscreteValuationRing.ofHasUnitMulPowIrreducibleFactorization
      ⟨x, hirr, fun hy => associated_pow_of_units hu hy⟩
  have hmax : IsLocalRing.maximalIdeal (Per.BdRp l) = Ideal.span {x} := hirr.maximalIdeal_eq
  have hassoc : Associated x (C.j C.t) := by
    obtain ⟨c, hc⟩ := (hfil 1 _).1 ht1
    rw [pow_one] at hc
    have hcu : IsUnit c := hu c fun hxc => ht2 ((hfil 2 _).2 (by
      rw [hc, pow_two]
      exact mul_dvd_mul_left _ hxc))
    exact ⟨hcu.unit, hc.symm⟩
  refine ⟨hdom, hdvr, ?_, ?_, ?_, fun n => ?_, ?_⟩
  · rw [hmax]
    exact Ideal.span_singleton_eq_span_singleton.2 hassoc
  · rw [hmax]
    ext y
    rw [Ideal.mem_span_singleton, RingHom.mem_ker, hθ]
  · rw [hmax]
    exact hcomp
  · ext y
    rw [hfil, Ideal.mem_span_singleton]
    exact (hassoc.pow_pow (n := n)).dvd_iff_dvd_left
  · refine (isLocalization_iff _ _).2 ⟨fun y => ?_, fun z => ?_, fun {a b} h => ⟨1, by rw [hinj h]⟩⟩
    · have hy : algebraMap (Per.BdRp l) (Per.BdR l) y ≠ 0 := fun h =>
        nonZeroDivisors.ne_zero y.2 (hinj (h.trans (map_zero _).symm))
      obtain ⟨b, hb⟩ := hfield.mul_inv_cancel hy
      exact IsUnit.of_mul_eq_one b hb
    · obtain ⟨n, y, h⟩ := hden' z
      exact ⟨(y, ⟨x ^ n, mem_nonZeroDivisors_of_ne_zero (pow_ne_zero n hx0)⟩), by
        simpa only [map_pow] using h⟩

end GlobalTheory.MemLoc.BdRDVR
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AxLemmaPadicComplexFixedElementApproximation
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc GlobalTheory.MemLoc
open scoped Formalism.Per

namespace GlobalTheory.AxLemma

theorem ax_lemma_complete : ∀ (l : ℕ) [Fact l.Prime], ∃ c : ℝ, 0 < c ∧ ∀ (H : Subgroup (GQ l)) (y : ℂ_[l]) (r : ℝ), 0 < r → (∀ g ∈ H, ‖Per.σC g y - y‖ ≤ r) → ∃ z : Om l, (∀ g ∈ H, g z = z) ∧ ‖y - (z : ℂ_[l])‖ ≤ c * r := by
  intro l _
  obtain ⟨c, hc, hax⟩ := ax_lemma l
  refine ⟨c + 1, by linarith, fun H y r hr hy => ?_⟩
  obtain ⟨y₀, hy₀⟩ : ∃ y₀ : Om l, ‖y - (y₀ : ℂ_[l])‖ ≤ r := by
    have hd : DenseRange ((↑) : PadicAlgCl l → ℂ_[l]) := UniformSpace.Completion.denseRange_coe
    obtain ⟨b, hb⟩ := Metric.denseRange_iff.1 hd y r hr
    exact ⟨b, by rw [← dist_eq_norm]; exact hb.le⟩
  have hsub : ∀ a b : Om l, ((a - b : Om l) : ℂ_[l]) = (a : ℂ_[l]) - (b : ℂ_[l]) := by
    intro a b
    rw [PadicComplex.coe_eq, map_sub, ← PadicComplex.coe_eq, ← PadicComplex.coe_eq]
  obtain ⟨z, hz, hyz⟩ := hax H y₀ r (fun g hg => by
    rw [← PadicComplex.norm_extends l, hsub, ← GlobalTheory.RingBasics.σC_coe]
    have e : Per.σC g (y₀ : ℂ_[l]) - (y₀ : ℂ_[l])
        = Per.σC g ((y₀ : ℂ_[l]) - y) + ((Per.σC g y - y) + (y - (y₀ : ℂ_[l]))) := by
      rw [map_sub]; ring
    rw [e]
    refine (IsUltrametricDist.norm_add_le_max _ _).trans (max_le ?_ ?_)
    · rw [GlobalTheory.RingBasics.norm_σC, norm_sub_rev]; exact hy₀
    · exact (IsUltrametricDist.norm_add_le_max _ _).trans (max_le (hy g hg) hy₀))
  refine ⟨z, hz, ?_⟩
  rw [← PadicComplex.norm_extends l, hsub] at hyz
  have e : y - (z : ℂ_[l]) = (y - (y₀ : ℂ_[l])) + ((y₀ : ℂ_[l]) - (z : ℂ_[l])) := by ring
  rw [e]
  refine (norm_add_le _ _).trans ?_
  linarith

end GlobalTheory.AxLemma
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BcrisExistsTPowMulThetaNeZero
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc GlobalTheory.MemLoc
open scoped Formalism.Per

namespace GlobalTheory.MemLoc.RegDivide

theorem exists_pow_mul_not_dvd {R : Type*} [CommRing R] (ξ : R) [IsHausdorff (Ideal.span {ξ}) R]
    {y : R} (hy : y ≠ 0) : ∃ (n : ℕ) (z : R), y = ξ ^ n * z ∧ ¬ ξ ∣ z := by
  classical
  have hex : ∃ n : ℕ, ¬ ξ ^ (n + 1) ∣ y := by
    by_contra h
    push Not at h
    apply hy
    apply IsHausdorff.haus (inferInstance : IsHausdorff (Ideal.span {ξ}) R)
    intro n
    rw [SModEq.zero, smul_eq_mul, Ideal.mul_top, Ideal.span_singleton_pow, Ideal.mem_span_singleton]
    exact (pow_dvd_pow ξ (Nat.le_succ n)).trans (h n)
  have h1 : ξ ^ (Nat.find hex) ∣ y := by
    rcases h : Nat.find hex with _ | k
    · simp
    · by_contra hk
      exact Nat.find_min hex (by omega : k < Nat.find hex) hk
  obtain ⟨z, hz⟩ := h1
  refine ⟨Nat.find hex, z, hz, ?_⟩
  rintro ⟨w, rfl⟩
  apply Nat.find_spec hex
  exact ⟨w, by rw [pow_succ, mul_assoc]; exact hz⟩

theorem abstract {B R D : Type*} [CommRing B] [CommRing R] [CommRing D] (ι : B →+* D) (a : R →+* D)
    (hι : Function.Injective ι) (ξ v : R) [IsHausdorff (Ideal.span {ξ}) R] (hv : IsUnit v)
    (t : B) (ht : IsUnit t) (hιt : ι t = a (ξ * v))
    (hD : ∀ x : D, ∃ (n : ℕ) (y : R), x * a ξ ^ n = a y) (b : B) (hb : b ≠ 0) :
    ∃ (m n : ℕ) (b' : B) (y : R), b * t ^ m = t ^ n * b' ∧ ι b' = a y ∧ ¬ ξ ∣ y := by
  obtain ⟨m, y₀, h0⟩ := hD (ι b)
  obtain ⟨s, hs⟩ := ht.exists_right_inv
  obtain ⟨w, hw⟩ := hv.exists_right_inv
  have h1 : ι (b * t ^ m) = a (y₀ * v ^ m) := by
    rw [map_mul, map_pow, hιt, map_mul, map_mul, ← h0, map_pow]
    ring
  have hne : y₀ * v ^ m ≠ 0 := by
    intro h
    rw [h, map_zero, ← map_zero ι] at h1
    exact hb ((ht.pow m).mul_left_eq_zero.1 (hι h1))
  obtain ⟨n, z, hz, hnd⟩ := exists_pow_mul_not_dvd ξ hne
  refine ⟨m, n, b * t ^ m * s ^ n, z * w ^ n, ?_, ?_, ?_⟩
  · calc b * t ^ m = b * t ^ m * (t * s) ^ n := by rw [hs, one_pow, mul_one]
      _ = _ := by ring
  · have h2 : a ξ * a v * ι s = 1 := by rw [← map_mul a, ← hιt, ← map_mul, hs, map_one]
    have h3 : a v * a w = 1 := by rw [← map_mul, hw, map_one]
    rw [map_mul, h1, hz, map_mul, map_mul, map_pow, map_pow, map_pow]
    calc a ξ ^ n * a z * ι s ^ n = a ξ ^ n * a z * ι s ^ n * (a v * a w) ^ n := by
          rw [h3, one_pow, mul_one]
      _ = a z * a w ^ n * (a ξ * a v * ι s) ^ n := by ring
      _ = _ := by rw [h2, one_pow, mul_one]
  · intro h
    apply hnd
    have : z = z * w ^ n * v ^ n := by
      rw [mul_assoc, ← mul_pow, mul_comm w v, hw, one_pow, mul_one]
    rw [this]
    exact h.mul_right _

theorem exists_divide : ∀ (l : ℕ) [Fact l.Prime] (C : Core l) (b : Per.Bcris l), b ≠ 0 →
    ∃ (m n : ℕ) (b' : Per.Bcris l) (y : Per.BdRp l), b * C.tB ^ m = C.tB ^ n * b' ∧
      C.ι b' = algebraMap (Per.BdRp l) (Per.BdR l) y ∧ Per.θD l y ≠ 0 := by
  intro l _ C b hb
  have he := core_isEps l C
  obtain ⟨hF, -, hc, -⟩ := filtration_eq_xi_pow l C.ε he
  obtain ⟨ht, h1, h2, -⟩ := core_t_unit_fil l C
  obtain ⟨-, hk, hu, -⟩ := thetaD_props l
  have hinj := (ULaws.u_laws l C).2.2.2.1
  have hD := (BdRField.bdR_isField l).2.2.2 C.ε he
  have hθ : ∀ y : Per.BdRp l, ¬ aDp l (xi C.ε) ∣ y → Per.θD l y ≠ 0 := fun y hy h =>
    hy (by simpa only [pow_one] using (hF 1 y).1 ((hk y).1 h))
  obtain ⟨v, hv⟩ := (hF 1 _).1 h1
  rw [pow_one] at hv
  have hvu : IsUnit v := by
    apply hu
    apply hθ
    rintro ⟨w, hw⟩
    apply h2
    refine (hF 2 _).2 ⟨w, ?_⟩
    rw [hv, hw, pow_two, mul_assoc]
  haveI := hc.toIsHausdorff
  obtain ⟨m, n, b', y, e1, e2, e3⟩ := abstract C.ι (algebraMap (Per.BdRp l) (Per.BdR l)) hinj
    (aDp l (xi C.ε)) v hvu C.tB ht (by rw [← hv]; exact C.ι_j C.t) hD b hb
  exact ⟨m, n, b', y, e1, e2, hθ y e3⟩

end GlobalTheory.MemLoc.RegDivide
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BcrisRegularOfFullGaloisLineUnits
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc GlobalTheory.MemLoc
open scoped Formalism.Per

namespace GlobalTheory.MemLoc

theorem regular_of_full : ∀ (l : ℕ) [Fact l.Prime] (C : Core l), (∀ b : Per.Bcris l, b ≠ 0 → (∀ g : GQ l, ∃ x : ℚ_[l], Per.σB g b = C.qB x * b) → IsUnit b) → C.Regular := by
  intro l _ C H K b hb hx
  classical
  have hK := K.2
  have hidx : (GK K).index ≠ 0 := by
    rw [GK, ← IntermediateField.finrank_eq_fixingSubgroup_index]
    exact Module.finrank_pos.ne'
  have hfin : Fintype (GQ l ⧸ GK K) := Subgroup.fintypeOfIndexNeZero hidx
  have hmul : ∀ (g h : GQ l) (x : Per.Bcris l), Per.σB (g * h) x = Per.σB g (Per.σB h x) :=
    (ActLaws.act_laws l).1
  have hone : ∀ x : Per.Bcris l, Per.σB (1 : GQ l) x = x := (ActLaws.act_laws l).2.1
  have hinv : ∀ (g : GQ l) (x : Per.Bcris l), Per.σB g⁻¹ (Per.σB g x) = x := fun g x => by
    rw [← hmul, inv_mul_cancel, hone]
  have hfix : ∀ (g : GQ l) (x : ℚ_[l]), Per.σB g (C.qB x) = C.qB x := fun g x =>
    (ULaws.u_laws l C).2.1 g _ _ (g.commutes x)
  have hD : IsDomain (Per.BdR l) := (BdRField.bdR_isField l).2.2.1.isDomain
  have hB : IsDomain (Per.Bcris l) := (ULaws.u_laws l C).2.2.2.1.isDomain C.ι
  have fout : ∀ g : GQ l, ∃ x : ℚ_[l], Per.σB g b = C.qB x * Per.σB (g : GQ l ⧸ GK K).out b := fun g => by
    obtain ⟨h, hh⟩ := QuotientGroup.mk_out_eq_mul (GK K) g
    obtain ⟨x, hx'⟩ := hx (h : GQ l)⁻¹ (inv_mem h.2)
    refine ⟨x, ?_⟩
    rw [← hfix (g : GQ l ⧸ GK K).out x, ← map_mul, ← hx', ← hmul, hh, mul_inv_cancel_right]
  choose c hc using fout
  have hP : IsUnit (∏ q : GQ l ⧸ GK K, Per.σB q.out b) := by
    refine H _ (Finset.prod_ne_zero_iff.2 fun q _ h0 => hb ?_) fun g => ⟨∏ q : GQ l ⧸ GK K, c (g * q.out), ?_⟩
    · rw [← hinv q.out b, h0, map_zero]
    · rw [map_prod, map_prod,
        ← Equiv.prod_comp (MulAction.toPerm g) fun q : GQ l ⧸ GK K => Per.σB q.out b,
        ← Finset.prod_mul_distrib]
      refine Finset.prod_congr rfl fun q _ => ?_
      have e : MulAction.toPerm g q = ((g * q.out : GQ l) : GQ l ⧸ GK K) := by
        rw [MulAction.toPerm_apply, ← smul_eq_mul, MulAction.Quotient.mk_smul_out]
      rw [e, ← hmul, ← hc]
  have hu := isUnit_of_dvd_unit
    (Finset.dvd_prod_of_mem (fun q : GQ l ⧸ GK K => Per.σB q.out b) (Finset.mem_univ ((1 : GQ l) : GQ l ⧸ GK K))) hP
  have := hu.map (Per.σB (((1 : GQ l) : GQ l ⧸ GK K).out)⁻¹)
  rwa [hinv] at this

end GlobalTheory.MemLoc
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CDvdOfMapEqZero
section
noncomputable section

open PowerSeries GlobalTheory.Cyc

namespace GlobalTheory.PrismS

theorem series_hom_ext {A B : Type} [CommRing A] [CommRing B] {f g : A⟦X⟧ →+* B⟦X⟧}
    (hC : ∀ a, f (C a) = g (C a)) (hX : f X = g X) (hd : X ∣ f X) : f = g := by
  have hp : f.comp Polynomial.coeToPowerSeries.ringHom = g.comp Polynomial.coeToPowerSeries.ringHom :=
    Polynomial.ringHom_ext (fun a => by simpa using hC a) (by simpa using hX)
  ext x n
  have hx := eq_X_pow_mul_shift_add_trunc (n + 1) x
  have h1 : f (trunc (n + 1) x : A⟦X⟧) = g (trunc (n + 1) x : A⟦X⟧) := RingHom.congr_fun hp (trunc (n + 1) x)
  have h2 : X ^ (n + 1) ∣ f x - g x := by
    rw [hx, map_add (f := _), map_add (f := _), h1, add_sub_add_right_eq_sub, map_mul, map_mul, map_pow, map_pow, ← hX,
      ← mul_sub]
    exact (pow_dvd_pow_of_dvd hd _).mul_right _
  have h3 := X_pow_dvd_iff.1 h2 n (Nat.lt_succ_self n)
  rwa [map_sub, sub_eq_zero] at h3

theorem C_dvd_of_map_eq_zero {A : Type} [CommRing A] (p : A) (y : A⟦X⟧)
    (h : PowerSeries.map (Ideal.Quotient.mk (Ideal.span {p})) y = 0) : ∃ b, y = C p * b := by
  have h1 : ∀ n, ∃ c, coeff n y = p * c := fun n => by
    have := congrArg (coeff n) h
    rw [coeff_map, map_zero, Ideal.Quotient.eq_zero_iff_mem, Ideal.mem_span_singleton] at this
    exact this
  choose c hc using h1
  exact ⟨PowerSeries.mk c, PowerSeries.ext fun n => by rw [coeff_C_mul, coeff_mk, hc]⟩

section Act

variable {l : ℕ} [hl : Fact l.Prime] {A B : Type} [CommRing A] [CommRing B] [Algebra ℤ_[l] A]
  [Algebra ℤ_[l] B]

theorem act_C (c : ℤ_[l]) (a : A) : act l A c (C a) = C a := (act l A c).commutes a

theorem act_X (c : ℤ_[l]) : act l A c X = cyc l A c := (act_laws l A).1 c

theorem phi_X : phi l A X = (1 + X) ^ l - 1 := (act_X _).trans ((act_laws l A).2.2.2.1 l)

theorem map_cyc (e : A →ₐ[ℤ_[l]] B) (c : ℤ_[l]) : PowerSeries.map e.toRingHom (cyc l A c) = cyc l B c := by
  rw [cyc, cyc, map_sub, map_one, ← RingHom.comp_apply, ← PowerSeries.map_comp]
  congr 3
  exact RingHom.ext fun z => e.commutes z

theorem map_act (e : A →ₐ[ℤ_[l]] B) (c : ℤ_[l]) (x : A⟦X⟧) :
    PowerSeries.map e.toRingHom (act l A c x) = act l B c (PowerSeries.map e.toRingHom x) := by
  have hX : PowerSeries.map e.toRingHom (act l A c X) = cyc l B c := by rw [act_X, map_cyc]
  refine RingHom.congr_fun (series_hom_ext (f := (PowerSeries.map e.toRingHom).comp (act l A c).toRingHom)
    (g := (act l B c).toRingHom.comp (PowerSeries.map e.toRingHom)) (fun a => ?_) ?_ ?_) x
  · change PowerSeries.map e.toRingHom (act l A c (C a)) = act l B c (PowerSeries.map e.toRingHom (C a))
    rw [act_C, map_C, act_C]
  · change PowerSeries.map e.toRingHom (act l A c X) = act l B c (PowerSeries.map e.toRingHom X)
    rw [hX, map_X, act_X]
  · change X ∣ PowerSeries.map e.toRingHom (act l A c X)
    rw [hX, X_dvd_iff, cyc_const]

theorem constantCoeff_act (c : ℤ_[l]) (x : A⟦X⟧) : constantCoeff (act l A c x) = constantCoeff x := by
  obtain ⟨y, hy⟩ : X ∣ x - C (constantCoeff x) := by rw [X_dvd_iff]; simp
  have h : x = C (constantCoeff x) + X * y := by rw [← hy]; ring
  conv_lhs => rw [h, map_add (f := _), map_mul, act_C, act_X, map_add (f := _), map_mul, cyc_const]
  simp


omit hl [Algebra ℤ_[l] A] [Algebra ℤ_[l] B] in
theorem map_QQ (e : A →+* B) (s : ℕ) : PowerSeries.map e (QQ l A s) = QQ l B s := by
  simp [QQ, XX]

def phiS (σ : A →ₐ[ℤ_[l]] A) : A⟦X⟧ →+* A⟦X⟧ := (PowerSeries.map σ.toRingHom).comp (phi l A).toRingHom

theorem phiS_apply (σ : A →ₐ[ℤ_[l]] A) (x : A⟦X⟧) : phiS σ x = PowerSeries.map σ.toRingHom (phi l A x) := rfl

theorem phiS_lift (σ : A →ₐ[ℤ_[l]] A) (hu : ¬ IsUnit (l : A)) (h : ∀ a, ∃ b, σ a = a ^ l + (l : A) * b)
    (x : A⟦X⟧) : ∃ b, phiS σ x = x ^ l + (l : A⟦X⟧) * b := by
  set q := Ideal.Quotient.mk (Ideal.span {(l : A)}) with hq
  have : CharP (A ⧸ Ideal.span {(l : A)}) l := CharP.quotient A l hu
  have : CharP (A ⧸ Ideal.span {(l : A)})⟦X⟧ l := charP_of_injective_ringHom (f := C) C_injective l
  have hX : PowerSeries.map q (phiS σ X) = X ^ l := by
    rw [phiS_apply, phi_X]
    simp [add_pow_char]
  have key : (PowerSeries.map q).comp (phiS σ) = (frobenius _ l).comp (PowerSeries.map q) := by
    refine series_hom_ext (fun a => ?_) ?_ ?_
    · obtain ⟨b, hb⟩ := h a
      have h1 : phi l A (C a) = C a := act_C _ a
      rw [RingHom.comp_apply, RingHom.comp_apply, phiS_apply, h1, map_C, map_C, map_C, frobenius_def,
        ← map_pow]
      change C (q (σ a)) = _
      rw [hb, map_add (f := _), map_mul, map_natCast, CharP.cast_eq_zero (A ⧸ Ideal.span {(l : A)}) l, zero_mul, add_zero,
        map_pow]
    · rw [RingHom.comp_apply, RingHom.comp_apply, hX, map_X, frobenius_def]
    · rw [RingHom.comp_apply, hX]; exact dvd_pow_self _ hl.out.ne_zero
  obtain ⟨b, hb⟩ := C_dvd_of_map_eq_zero (l : A) (phiS σ x - x ^ l) (by
    have h2 := RingHom.congr_fun key x
    rw [RingHom.comp_apply, RingHom.comp_apply, frobenius_def] at h2
    rw [map_sub, map_pow, ← hq, h2, sub_self])
  exact ⟨b, by rw [map_natCast] at hb; rw [← hb]; ring⟩

end Act

theorem ker_eq_span {A B : Type} [CommRing A] [IsLocalRing A] [IsAdicComplete (IsLocalRing.maximalIdeal A) A]
    [CommRing B] (f : A⟦X⟧ →+* B) (Q b : A⟦X⟧) (d : ℕ) (p : A) (hp : ¬ IsUnit p) (hQ : Q = X ^ d + C p * b)
    (h0 : f Q = 0) (h : ∀ r : Polynomial A, r.natDegree < d → f r = 0 → r = 0) :
    RingHom.ker f = Ideal.span {Q} := by
  refine le_antisymm (fun x hx => ?_) ((Ideal.span_singleton_le_iff_mem _).2 h0)
  have h1 : Q.map (IsLocalRing.residue A) = X ^ d := by
    rw [hQ, map_add (f := _), map_mul, map_C, (IsLocalRing.residue_eq_zero_iff p).2 hp]
    simp
  obtain ⟨q, r, hr⟩ := exists_isWeierstrassDivision x (g := Q) (by rw [h1]; exact pow_ne_zero _ X_ne_zero)
  have h2 : r.degree < d := by
    have := hr.degree_lt
    change r.degree < ((Q.map (IsLocalRing.residue A)).order.toNat : ℕ) at this
    rwa [h1, order_X_pow, ENat.toNat_natCast] at this
  have h3 : r = 0 := by
    by_contra hne
    refine hne (h r ((Polynomial.natDegree_lt_iff_degree_lt hne).2 h2) ?_)
    have := congrArg f hr.eq_mul_add
    rw [map_add (f := _), map_mul, h0, zero_mul, zero_add] at this
    exact this.symm.trans hx
  rw [hr.eq_mul_add, h3]
  simpa using Ideal.mul_mem_right _ _ (Ideal.mem_span_singleton_self Q)

theorem isAdicComplete_span {A : Type} [CommRing A] (p : A) [IsAdicComplete (Ideal.span {p}) A] (Q b : A⟦X⟧)
    (d : ℕ) (hd : 0 < d) (hQ : Q = X ^ d + C p * b) :
    IsAdicComplete (Ideal.span {C p} ⊔ Ideal.span {Q}) A⟦X⟧ := by
  have hJ : (Ideal.span {p}).comap (constantCoeff (R := A)) = Ideal.span {C p} ⊔ Ideal.span {X} := by
    refine le_antisymm (fun x hx => ?_) (sup_le ?_ ?_)
    · rw [Ideal.mem_comap, Ideal.mem_span_singleton] at hx
      obtain ⟨c, hc⟩ := hx
      obtain ⟨y, hy⟩ : X ∣ x - C (constantCoeff x) := by rw [X_dvd_iff]; simp
      have h : x = C p * C c + X * y := by rw [← hy, ← map_mul, ← hc]; ring
      rw [h]
      exact Submodule.add_mem_sup (Ideal.mul_mem_right _ _ (Ideal.mem_span_singleton_self _))
        (Ideal.mul_mem_right _ _ (Ideal.mem_span_singleton_self _))
    · rw [Ideal.span_singleton_le_iff_mem, Ideal.mem_comap]; simp
    · rw [Ideal.span_singleton_le_iff_mem, Ideal.mem_comap]; simp
  have hc := ReciprocityTheory.P1.isAdicComplete_comap_constantCoeff (Ideal.span {p})
  rw [hJ] at hc
  refine GlobalTheory.isAdicComplete_of_pow_le_of_pow_le _ _ _ d 1 ?_ ?_ hc
  · have h1 : ∀ (I J : Ideal A⟦X⟧) (n : ℕ), (I ⊔ J) ^ n ≤ I ⊔ J ^ n := fun I J n => by
      induction n with
      | zero => simp
      | succ n ih =>
        rw [pow_succ, pow_succ]
        refine (Ideal.mul_mono_left ih).trans ?_
        rw [Ideal.sup_mul, Ideal.mul_sup (J ^ n)]
        exact sup_le (le_sup_of_le_left Ideal.mul_le_left)
          (sup_le (le_sup_of_le_left Ideal.mul_le_right) le_sup_right)
    refine (h1 _ _ _).trans (sup_le le_sup_left ?_)
    rw [Ideal.span_singleton_pow, Ideal.span_singleton_le_iff_mem,
      show (X : A⟦X⟧) ^ d = -(C p * b) + Q by rw [hQ]; ring]
    exact Submodule.add_mem_sup (neg_mem (Ideal.mul_mem_right _ _ (Ideal.mem_span_singleton_self _)))
      (Ideal.mem_span_singleton_self _)
  · rw [pow_one]
    refine sup_le le_sup_left ?_
    rw [Ideal.span_singleton_le_iff_mem, hQ, add_comm]
    exact Submodule.add_mem_sup (Ideal.mul_mem_right _ _ (Ideal.mem_span_singleton_self _))
      (Ideal.pow_mem_of_mem _ (Ideal.mem_span_singleton_self _) _ hd)

theorem existsUnique_series {A B κ : Type} [CommRing A] [CommRing B] {d : ℕ} (e : κ → (A →+* B)) (o : Fin d → B)
    (h : ∀ y : κ → B, ∃! c : Fin d → A, ∀ k, y k = ∑ i, o i * e k (c i)) (x : κ → B⟦X⟧) :
    ∃! c : Fin d → A⟦X⟧, ∀ k, x k = ∑ i, C (o i) * PowerSeries.map (e k) (c i) := by
  choose c hc hu using fun n => h fun k => coeff n (x k)
  refine ⟨fun i => PowerSeries.mk fun n => c n i, fun k => PowerSeries.ext fun n => ?_, fun c' hc' => ?_⟩
  · simpa [coeff_C_mul] using hc n k
  · funext i
    ext n
    rw [coeff_mk, ← hu n (fun i => coeff n (c' i)) fun k => by simp [hc' k, coeff_C_mul]]

end GlobalTheory.PrismS
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CyclotomicTwistCocycleCoboundaryStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.Loc GlobalTheory.Cyc
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cyclotomic_twist_cocycle_coboundary : ∀ (l : ℕ) [Fact l.Prime] (act : GQ l →* (PadicComplex l ≃+* PadicComplex l)) (χ : GQ l →* ℚ_[l]ˣ), IsActC act → IsCyc χ → ∀ (K : FinExt l), ∀ s : ℕ, Lev l s → ∀ j : ℤ, j ≠ 0 → ∀ c : GQ l → PadicComplex l, CocOn (Gj K s) (fun g y => chiC χ j g * act g y) {y | ‖y‖ ≤ 1} c → CobOn (Gj K s) (fun g y => chiC χ j g * act g y) {y | ‖y‖ ≤ 1} (fun g => (l : PadicComplex l) ^ (1 + s + padicValInt l j) * c g) := by
  first | exact @GlobalTheory.Cyc.TwistKill.pow_kills_cyclotomic_H1 | exact GlobalTheory.Cyc.TwistKill.pow_kills_cyclotomic_H1 | (intros; apply GlobalTheory.Cyc.TwistKill.pow_kills_cyclotomic_H1 <;> assumption)
end

