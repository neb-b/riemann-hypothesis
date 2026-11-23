module

public import Mathlib
public import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
public import Formalism.LocalRingCardinality.AdicCompletionLocal.LocTied
public import Formalism.SharpRestriction.LevelLetterCocycles.LocalSituation
public import Formalism.SharpRestriction.LevelLetterCocycles.LocCoh
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0236
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsDiscreteValuationRingIntegralClosurePadicInt
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.HeightTheory.Bundle0005
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IntegralOfBounded
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.MemEurOfTeichmullerSeries
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NilpotentOfNotIsUnit
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0010
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0008
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0128
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PowMulMemLatIff
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0009

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CoefficientRingIntegersCompactAdicProperties
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct Module

namespace GlobalTheory.GoodCoeff

section Open

variable {l : ℕ} [Fact l.Prime] {LL : Type} [Field LL] [Algebra ℚ_[l] LL] [TopologicalSpace LL]
  [IsModuleTopology ℚ_[l] LL]

theorem continuous_algebraMap_padic : Continuous (algebraMap ℚ_[l] LL) := by
  haveI := IsModuleTopology.toContinuousSMul ℚ_[l] LL
  have h : (algebraMap ℚ_[l] LL : ℚ_[l] → LL) = fun c => c • (1 : LL) :=
    funext Algebra.algebraMap_eq_smul_one
  rw [h]
  exact continuous_id.smul continuous_const

theorem padicInt_mem (A : Subring LL) (hA : IsOpen (A : Set LL)) (u : ℤ_[l]) :
    algebraMap ℚ_[l] LL (u : ℚ_[l]) ∈ A := by
  have hU : IsOpen ((algebraMap ℚ_[l] LL) ⁻¹' (A : Set LL)) :=
    hA.preimage continuous_algebraMap_padic
  have h0 : (0 : ℚ_[l]) ∈ (algebraMap ℚ_[l] LL) ⁻¹' (A : Set LL) := by
    simp [A.zero_mem]
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.1 hU 0 h0
  obtain ⟨n, hn⟩ := exists_pow_lt_of_lt_one hε (Padic.norm_p_lt_one (p := l))
  obtain ⟨w, hw⟩ := Ideal.mem_span_singleton'.1 (PadicInt.appr_spec n u)
  have hu : (u : ℚ_[l]) = ((u.appr n : ℕ) : ℚ_[l]) + (w : ℚ_[l]) * (l : ℚ_[l]) ^ n := by
    have := congrArg (fun z : ℤ_[l] => (z : ℚ_[l])) hw
    push_cast at this
    linear_combination -this
  have h1 : algebraMap ℚ_[l] LL ((w : ℚ_[l]) * (l : ℚ_[l]) ^ n) ∈ A := by
    apply hball
    rw [Metric.mem_ball, dist_zero_right, norm_mul, norm_pow]
    calc ‖(w : ℚ_[l])‖ * ‖(l : ℚ_[l])‖ ^ n ≤ 1 * ‖(l : ℚ_[l])‖ ^ n :=
          mul_le_mul_of_nonneg_right (PadicInt.norm_le_one w) (by positivity)
      _ < ε := by rwa [one_mul]
  rw [hu, map_add (f := _), map_natCast]
  exact A.add_mem (natCast_mem A _) h1

end Open

theorem good_coeff_integers : ∀ (l : ℕ) [Fact l.Prime] (LL : Type) [Field LL] [Algebra ℚ_[l] LL] [TopologicalSpace LL] (O : Type) [CommRing O] [Algebra O LL], GoodO (Qp := ℚ_[l]) LL O → (∀ x : LL, x ∈ Set.range (algebraMap O LL) ↔ RingHom.IsIntegralElem ((algebraMap ℚ_[l] LL).comp (algebraMap ℤ_[l] ℚ_[l])) x) ∧ IsCompact (Set.range (algebraMap O LL)) ∧ (∀ n : ℕ, Finite (O ⧸ Ideal.span {((l : ℕ) : O) ^ n})) ∧ IsAdicComplete (Ideal.span {((l : ℕ) : O)}) O := by
  first
  | exact @_root_.GlobalTheory.PowerImageOpen.main
  | exact _root_.GlobalTheory.PowerImageOpen.main
  | (apply _root_.GlobalTheory.PowerImageOpen.main <;> assumption)
  | (intros; apply _root_.GlobalTheory.PowerImageOpen.main <;> assumption)
  | (intros; apply @_root_.GlobalTheory.PowerImageOpen.main <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.PowerImageOpen.main ..)

end GlobalTheory.GoodCoeff
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ConstantCoeffTeichSub
section
open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations GlobalTheory.Cyc PowerSeries

namespace GlobalTheory.Cyc.IoMap

section General

variable {R A : Type*} [CommRing R] [CommRing A] [Algebra R A]

theorem X_pow_dvd_sub_trunc (a : R⟦X⟧) (n : ℕ) :
    (X : R⟦X⟧) ^ n ∣ a - (trunc n a : Polynomial R) := by
  rw [X_pow_dvd_iff]
  intro m hm
  simp [coeff_trunc, hm]

theorem algHom_coe (f : R⟦X⟧ →ₐ[R] A) (p : Polynomial R) :
    f (p : R⟦X⟧) = Polynomial.aeval (f X) p := by
  have : f.comp (Polynomial.coeToPowerSeries.algHom R) = Polynomial.aeval (f X) := by
    ext
    simp
  simpa using DFunLike.congr_fun this p

theorem algHom_unique (f g : R⟦X⟧ →ₐ[R] A) (h : f X = g X)
    (hs : ∀ x : A, (∀ n, f X ^ n ∣ x) → x = 0) : f = g := by
  ext a
  rw [← sub_eq_zero]
  refine hs _ fun n => ?_
  obtain ⟨b, hb⟩ := X_pow_dvd_sub_trunc a n
  have h1 := congrArg f hb
  have h2 := congrArg g hb
  rw [map_sub, map_mul, map_pow, algHom_coe] at h1 h2
  rw [← h] at h2
  exact ⟨f b - g b, by linear_combination h1 - h2⟩

theorem algHom_exists (y : A) (hc : GlobalTheory.Per.AinfComplete.Summ y)
    (hs : ∀ x : A, (∀ n, y ^ n ∣ x) → x = 0) : ∃ f : R⟦X⟧ →ₐ[R] A, f X = y := by
  have h1 : ∀ a : R⟦X⟧, ∃ L : A, ∀ n, y ^ n ∣ L - Polynomial.aeval y (trunc n a) := by
    intro a
    obtain ⟨L, hL⟩ := hc fun i => algebraMap R A (coeff i a)
    refine ⟨L, fun n => ?_⟩
    have e : Polynomial.aeval y (trunc n a) =
        ∑ i ∈ Finset.range n, y ^ i * algebraMap R A (coeff i a) := by
      induction n with
      | zero => simp
      | succ n ih =>
        rw [trunc_succ, map_add (f := _), ih, Finset.sum_range_succ, Polynomial.aeval_monomial, mul_comm]
    rw [e]
    exact Ideal.mem_span_singleton.1 (hL n)
  choose L hL using h1
  have h2 : ∀ (a : R⟦X⟧) (p : Polynomial R) (n : ℕ), (X : R⟦X⟧) ^ n ∣ a - p →
      y ^ n ∣ L a - Polynomial.aeval y p := by
    intro a p n h
    have h3 : (Polynomial.X : Polynomial R) ^ n ∣ trunc n a - p := by
      rw [Polynomial.X_pow_dvd_iff]
      intro d hd
      have := X_pow_dvd_iff.1 h d hd
      simpa [coeff_trunc, hd] using this
    have h4 := map_dvd (Polynomial.aeval y) h3
    rw [map_pow, Polynomial.aeval_X, map_sub] at h4
    convert dvd_add (hL a n) h4 using 1
    ring
  have h3 : ∀ p : Polynomial R, L p = Polynomial.aeval y p := fun p => by
    rw [← sub_eq_zero]
    exact hs _ fun n => h2 _ _ _ (by simp)
  have hadd : ∀ a b, L (a + b) = L a + L b := fun a b => by
    rw [← sub_eq_zero]
    refine hs _ fun n => ?_
    have := hL (a + b) n
    rw [map_add (f := _), map_add (f := _)] at this
    convert dvd_sub (dvd_sub this (hL a n)) (hL b n) using 1
    ring
  have hmul : ∀ a b, L (a * b) = L a * L b := fun a b => by
    rw [← sub_eq_zero]
    refine hs _ fun n => ?_
    have := h2 (a * b) (trunc n a * trunc n b) n (by
      rw [Polynomial.coe_mul]
      convert dvd_add ((X_pow_dvd_sub_trunc a n).mul_right b)
        ((X_pow_dvd_sub_trunc b n).mul_left (trunc n a : Polynomial R)) using 1
      ring)
    rw [map_mul] at this
    convert dvd_sub (dvd_sub this ((hL a n).mul_right (L b)))
      ((hL b n).mul_left (Polynomial.aeval y (trunc n a))) using 1
    ring
  refine ⟨{ toFun := L
            map_one' := by simpa using h3 1
            map_mul' := hmul
            map_zero' := by simpa using h3 0
            map_add' := hadd
            commutes' := fun r => by simpa using h3 (Polynomial.C r) }, ?_⟩
  simpa using h3 Polynomial.X

end General

variable (l : ℕ) [Fact l.Prime]

theorem ne_zero_of_coeff {B : Type*} [CommRing B] [IsDomain B] [CharP B l] (ψ : ℤ_[l]⟦X⟧ →+* B)
    (hX : ψ X ≠ 0) (m : ℕ) : ∀ a : ℤ_[l]⟦X⟧, ¬ ((l : ℕ) : ℤ_[l]) ∣ coeff m a → ψ a ≠ 0 := by
  have h0 : ∀ a : ℤ_[l]⟦X⟧, ¬ ((l : ℕ) : ℤ_[l]) ∣ constantCoeff a → ψ a ≠ 0 := by
    intro a ha
    have : IsUnit (constantCoeff a) := by
      by_contra hn
      exact ha ((PadicInt.norm_lt_one_iff_dvd _).1 (PadicInt.not_isUnit_iff.1 hn))
    exact ((isUnit_iff_constantCoeff.2 this).map ψ).ne_zero
  induction m with
  | zero => intro a ha; exact h0 a (by simpa using ha)
  | succ m ih =>
    intro a ha
    by_cases h : ((l : ℕ) : ℤ_[l]) ∣ constantCoeff a
    · obtain ⟨c, hc⟩ := h
      rw [eq_X_mul_shift_add_const a, hc, map_add (f := _), map_mul, map_mul, map_mul, map_natCast,
        map_natCast, CharP.cast_eq_zero, zero_mul, add_zero]
      exact mul_ne_zero hX (ih _ (by simpa using ha))
    · exact h0 a h

theorem ne_zero_of_not_dvd {B : Type*} [CommRing B] [IsDomain B] [CharP B l] (ψ : ℤ_[l]⟦X⟧ →+* B)
    (hX : ψ X ≠ 0) (a : ℤ_[l]⟦X⟧) (ha : ¬ ((l : ℕ) : ℤ_[l]⟦X⟧) ∣ a) : ψ a ≠ 0 := by
  by_contra h
  apply ha
  have : ∀ m, ((l : ℕ) : ℤ_[l]) ∣ coeff m a := fun m => by
    by_contra hm
    exact ne_zero_of_coeff l ψ hX m a hm h
  choose c hc using this
  refine ⟨PowerSeries.mk c, ?_⟩
  ext m
  rw [← map_natCast (C : ℤ_[l] →+* ℤ_[l]⟦X⟧), coeff_C_mul, coeff_mk, hc]

theorem phi_X : phi l ℤ_[l] X = (1 + X) ^ l - 1 := by
  rw [phi, act, substAlgHom_X, cyc, binomialSeries_nat]
  simp

theorem constantCoeff_teich_sub (e : OCb l) :
    WittVector.constantCoeff (WittVector.teichmuller l e - 1 : Ainf l) = e - 1 := by
  rw [map_sub, map_one, WittVector.constantCoeff_apply, WittVector.teichmuller_coeff_zero]

theorem complete_teich (e : OCb l) (he : ¬ IsUnit (e - 1)) :
    GlobalTheory.Per.AinfComplete.Summ (WittVector.teichmuller l e - 1 : Ainf l) ∧
      ∀ x : Ainf l, (∀ n, (WittVector.teichmuller l e - 1 : Ainf l) ^ n ∣ x) → x = 0 := by
  have hy : ¬ IsUnit (WittVector.teichmuller l e - 1 : Ainf l) := fun h =>
    he (constantCoeff_teich_sub l e ▸ h.map WittVector.constantCoeff)
  have := (GlobalTheory.Per.AinfComplete.main l _ hy).2
  exact ⟨GlobalTheory.Per.AinfComplete.summ_of_precomplete _, fun x hx =>
    GlobalTheory.Per.AinfComplete.eq_zero_of_haus _ x fun n => Ideal.mem_span_singleton.2 (hx n)⟩

noncomputable def frobA : Ainf l →ₐ[ℤ_[l]] Ainf l where
  toRingHom := WittVector.map (frobenius (OCb l) l)
  commutes' := fun x => map_zlW l _ x

theorem frobA_apply (x : Ainf l) : frobA l x = WittVector.frobenius x := by
  rw [WittVector.frobenius_eq_map_frobenius]
  rfl

theorem main : ∀ (l : ℕ) [Fact l.Prime], ∀ e : OCb l, ¬ IsUnit (e - 1) →
    (∃! io : PowerSeries ℤ_[l] →ₐ[ℤ_[l]] Ainf l, IsIo e io) ∧
    ∀ io : PowerSeries ℤ_[l] →ₐ[ℤ_[l]] Ainf l, IsIo e io →
      (∀ a, io (phi l ℤ_[l] a) = WittVector.frobenius (io a)) ∧
      (e ≠ 1 → ∀ a, ¬ ((l : ℕ) : PowerSeries ℤ_[l]) ∣ a → IsUnit (inclW l (io a))) := by
  intro l hl e he
  obtain ⟨hc, hs⟩ := complete_teich l e he
  refine ⟨?_, fun io hio => ⟨?_, fun he1 a ha => ?_⟩⟩
  · obtain ⟨f, hf⟩ := algHom_exists (R := ℤ_[l]) _ hc hs
    refine ⟨f, hf, fun g hg => algHom_unique g f (Eq.trans hg hf.symm) ?_⟩
    rw [show g X = _ from hg]
    exact hs
  · have he' : ¬ IsUnit (e ^ l - 1) := fun h => he (by
      rw [← geom_sum_mul] at h
      exact isUnit_of_mul_isUnit_right h)
    have hio' : io X = WittVector.teichmuller l e - 1 := hio
    have e1 : (io.comp (phi l ℤ_[l])) X = WittVector.teichmuller l (e ^ l) - 1 := by
      rw [AlgHom.comp_apply, phi_X, map_sub, map_pow, map_add (f := _), map_one, hio', map_pow]
      ring
    have e2 : ((frobA l).comp io) X = WittVector.teichmuller l (e ^ l) - 1 := by
      rw [AlgHom.comp_apply, hio', map_sub, map_one]
      congr 1
      exact WittVector.map_teichmuller l (frobenius (OCb l) l) e
    have := algHom_unique _ _ (e1.trans e2.symm) (by rw [e1]; exact (complete_teich l _ he').2)
    intro a
    rw [← frobA_apply]
    exact DFunLike.congr_fun this a
  · apply WittVector.isUnit_of_coeff_zero_ne_zero
    rw [inclW, WittVector.map_coeff]
    have hio' : io X = WittVector.teichmuller l e - 1 := hio
    have := ne_zero_of_not_dvd l
      ((WittVector.constantCoeff : Ainf l →+* OCb l).comp io.toRingHom) (by
        change WittVector.constantCoeff (io X) ≠ 0
        rw [hio', constantCoeff_teich_sub]
        exact sub_ne_zero.2 he1) a ha
    intro hz
    exact this ((IsFractionRing.injective (OCb l) (Cb l)) (hz.trans (map_zero _).symm))

end GlobalTheory.Cyc.IoMap
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ContractEquivariant
section
noncomputable section

namespace GlobalTheory.PushCob

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.MainNotions.LocalSituation GlobalTheory.Cyc GlobalTheory.ExpImage TensorProduct

theorem contract_equivariant {R Y Q : Type} [CommRing R] [AddCommGroup Y] [Module R Y]
    [AddCommGroup Q] [Module R Q] (ψ : Y →ₗ[R] R) (A : Y →ₗ[R] Y) (B : Q →ₗ[R] Q) (u t : R)
    (h : ∀ y, ∃ z, ψ (A y) - u * ψ y = t * z) (x : Y ⊗[R] Q) :
    ∃ q : Q, TensorProduct.lid R Q (ψ.rTensor Q (TensorProduct.map A B x)) =
      u • B (TensorProduct.lid R Q (ψ.rTensor Q x)) + t • q := by
  induction x using TensorProduct.induction_on with
  | zero => exact ⟨0, by simp⟩
  | tmul y q =>
    obtain ⟨z, hz⟩ := h y
    refine ⟨z • B q, ?_⟩
    simp only [TensorProduct.map_tmul, LinearMap.rTensor_tmul, TensorProduct.lid_tmul, map_smul,
      smul_smul, ← add_smul]
    rw [← hz]; congr 1; ring
  | add x x' hx hx' =>
    obtain ⟨q, hq⟩ := hx
    obtain ⟨q', hq'⟩ := hx'
    refine ⟨q + q', ?_⟩
    simp only [map_add (f := _), hq, hq', smul_add]
    abel

theorem actQab_mk {O G WC : Type} [CommRing O] [Group G] [CommRing WC] [Algebra O WC]
    {AA : Subalgebra O WC} {act : G →* (WC ≃ₐ[O] WC)} {ξ : WCˣ} (h : XiOK AA act ξ) (a b : ℤ)
    (g : G) (m : ↥(Mxi AA ξ a)) :
    actQab h a b g (Submodule.Quotient.mk m) = Submodule.Quotient.mk (actM h a g m) := rfl

variable {l : ℕ} [Fact l.Prime]

theorem inclW_injective : Function.Injective (inclW l) :=
  WittVector.map_injective _ (IsFractionRing.injective (OCb l) (Cb l))

theorem inclW_zl (z : ℤ_[l]) :
    inclW l (algebraMap ℤ_[l] (Ainf l) z) = algebraMap ℤ_[l] (WCb l) z := (inclWA l).commutes z

theorem mem_Mxi {P : LocPrime l} (AI : LocAinf l P) (k : ℕ) (w : WCb l)
    (hw : w ∈ Mxi (AinfSub l) (xiU AI) (k : ℤ)) : ∃ a : Ainf l, w = inclW l (AI.ξ ^ k * a) := by
  obtain ⟨y, ⟨a, rfl⟩, rfl⟩ := hw
  refine ⟨a, ?_⟩
  rw [LinearMap.mulLeft_apply, zpow_natCast, Units.val_pow_eq_pow_val, map_mul, map_pow]
  rfl

theorem mem_Mxi_zero {P : LocPrime l} (AI : LocAinf l P) (w : ↥(Mxi (AinfSub l) (xiU AI) 0)) :
    ∃ a : Ainf l, (w : WCb l) = inclW l a := by
  simpa using mem_Mxi AI 0 w w.2

def scaled {Y : Type} [AddCommGroup Y] [Module ℤ_[l] Y] (ψ : Y →ₗ[ℤ_[l]] ℚ_[l]) (r : ℕ)
    (h : ∀ y, ‖ψ y‖ ≤ (l : ℝ) ^ r) : Y →ₗ[ℤ_[l]] ℤ_[l] where
  toFun y := ⟨(l : ℚ_[l]) ^ r * ψ y, by
    have hl : (0 : ℝ) < l := by exact_mod_cast (Fact.out : l.Prime).pos
    rw [PadicInt.mem_subring_iff, norm_mul, norm_pow, Padic.norm_p, inv_pow,
      inv_mul_le_iff₀ (by positivity), mul_one]
    exact h y⟩
  map_add' y y' := by
    apply Subtype.ext
    change _ = (l : ℚ_[l]) ^ r * ψ y + (l : ℚ_[l]) ^ r * ψ y'
    rw [← mul_add, ← map_add (f := _)]
  map_smul' z y := by
    apply PadicInt.ext
    change (l : ℚ_[l]) ^ r * ψ (z • y) = (z : ℚ_[l]) * ((l : ℚ_[l]) ^ r * ψ y)
    rw [map_smul, Algebra.smul_def, PadicInt.algebraMap_apply]
    ring

theorem scaled_coe {Y : Type} [AddCommGroup Y] [Module ℤ_[l] Y] (ψ : Y →ₗ[ℤ_[l]] ℚ_[l]) (r : ℕ)
    (h : ∀ y, ‖ψ y‖ ≤ (l : ℝ) ^ r) (y : Y) :
    ((scaled ψ r h y : ℤ_[l]) : ℚ_[l]) = (l : ℚ_[l]) ^ r * ψ y := rfl

theorem push_coboundary : ∀ (D : Formalism.BasicNotions.D7) (l : ℕ) [Fact l.Prime] (K : FinExt l) (s e r N : ℕ) (Y : Type) [AddCommGroup Y] [Module ℤ_[l] Y] (ρ : ↥(Gj K s) →* (Y →ₗ[ℤ_[l]] Y)) (ψ : Y →ₗ[ℤ_[l]] ℚ_[l]), (∀ y, ‖ψ y‖ ≤ (l : ℝ) ^ r) → (∀ (σ : GQ l) (hσ : σ ∈ Gj K s) (y : Y), ‖ψ (ρ ⟨σ, hσ⟩ y) - (((D.loc l).χQ σ ^ (-(e : ℤ)) : ℚ_[l]ˣ) : ℚ_[l]) * ψ y‖ ≤ 1) → ∀ (f : ↥(Gj K s) → Y) (c : GQ l → ℚ_[l]), (∀ (σ : GQ l) (hσ : σ ∈ Gj K s), c σ = ψ (f ⟨σ, hσ⟩)) → ∀ one : ↥(Mxi (AinfSub l) (xiU (D.locA l)) 0), (one : WCb l) = 1 → IsCob (repQ (D.locA l) (Gj K s) ρ 0 ((e : ℤ) + 1)) (fun g => (l : ℤ_[l]) ^ N • (f g ⊗ₜ[ℤ_[l]] (Submodule.Quotient.mk one : Qab (AinfSub l) (xiU (D.locA l)) 0 ((e : ℤ) + 1)))) → ∃ b ∈ ((D.loc l).PD (botExt l)).Fil 0, ∀ σ ∈ Gj K s, ∃ a : Ainf l, algebraMap ℚ_[l] (D.loc l).R.BdR ((l : ℚ_[l]) ^ N * c σ) - (algebraMap ℚ_[l] (D.loc l).R.BdR (((D.loc l).χQ σ ^ (-(e : ℤ)) : ℚ_[l]ˣ) : ℚ_[l]) * (D.loc l).actQdR σ b - b) - (D.loc l).ιB ((D.locA l).ιA a) ∈ ((D.loc l).PD (botExt l)).Fil ((e : ℤ) + 1) := by
  intro D l _ K s e r N Y _ _ ρ ψ hψ hρ f c hc one hone hcob
  obtain ⟨x, hx⟩ := hcob
  have hl : (l : ℚ_[l]) ≠ 0 := by exact_mod_cast (Fact.out : l.Prime).ne_zero
  have hlr : (l : ℚ_[l]) ^ r ≠ 0 := pow_ne_zero _ hl
  obtain ⟨m0, hm0⟩ := Submodule.Quotient.mk_surjective _
    (TensorProduct.lid ℤ_[l] _ ((scaled ψ r hψ).rTensor _ x))
  obtain ⟨a0, ha0⟩ := mem_Mxi_zero _ m0
  refine ⟨qB (D.loc l) ((l : ℚ_[l]) ^ r)⁻¹ * io (D.locA l) a0, qB_mul_mem _ (io_mem _ _), ?_⟩
  intro σ hσ
  have hn : ‖(((D.loc l).χQ σ ^ (-(e : ℤ)) : ℚ_[l]ˣ) : ℚ_[l])‖ ≤ 1 := by
    rw [Units.val_zpow_eq_zpow_val, norm_zpow, (cyc_basic l _ (D.loc l).χQ_cyc).1, one_zpow]
  set u' : ℚ_[l] := (((D.loc l).χQ σ ^ (-(e : ℤ)) : ℚ_[l]ˣ) : ℚ_[l]) with hu'
  let u : ℤ_[l] := ⟨u', hn⟩
  have hu : (u : ℚ_[l]) = u' := rfl
  obtain ⟨q, hq⟩ := contract_equivariant (scaled ψ r hψ) (ρ ⟨σ, hσ⟩)
    (actQab (act := (D.locA l).actWCbHom.comp (Gj K s).subtype)
      ⟨fun g x hx => (xiOK (D.locA l)).1 (g : GQ l) x hx, (xiOK (D.locA l)).2.1,
        fun g => (xiOK (D.locA l)).2.2 (g : GQ l)⟩ 0 ((e : ℤ) + 1) ⟨σ, hσ⟩) u ((l : ℤ_[l]) ^ r)
    (fun y => ⟨⟨_, hρ σ hσ y⟩, by
      apply Subtype.ext
      change (l : ℚ_[l]) ^ r * ψ (ρ ⟨σ, hσ⟩ y) - u' * ((l : ℚ_[l]) ^ r * ψ y) =
        (((l : ℤ_[l]) ^ r : ℤ_[l]) : ℚ_[l]) * (ψ (ρ ⟨σ, hσ⟩ y) - u' * ψ y)
      push_cast
      ring⟩) x
  obtain ⟨m, rfl⟩ := Submodule.Quotient.mk_surjective _ q
  obtain ⟨a, ha⟩ := mem_Mxi_zero _ m
  have h1 := congrArg (fun w => TensorProduct.lid ℤ_[l] _ ((scaled ψ r hψ).rTensor _ w))
    (hx ⟨σ, hσ⟩)
  simp only [map_smul, map_sub, LinearMap.rTensor_tmul, TensorProduct.lid_tmul] at h1
  rw [← hm0] at hq
  have h2 := h1.trans (congrArg₂ (· - ·) hq hm0.symm)
  beta_reduce at h2
  erw [actQab_mk] at h2
  simp only [← Submodule.Quotient.mk_smul, ← Submodule.Quotient.mk_add,
    ← Submodule.Quotient.mk_sub] at h2
  rw [Submodule.Quotient.eq, Submodule.mem_comap] at h2
  obtain ⟨a', ha'⟩ := mem_Mxi (D.locA l) (e + 1) _ (by rw [Nat.cast_succ]; exact h2)
  have h3 : algebraMap ℤ_[l] (Ainf l) ((l : ℤ_[l]) ^ N * scaled ψ r hψ (f ⟨σ, hσ⟩)) -
      (algebraMap ℤ_[l] (Ainf l) u * (D.locA l).actW σ a0 +
        algebraMap ℤ_[l] (Ainf l) ((l : ℤ_[l]) ^ r) * a - a0) = (D.locA l).ξ ^ (e + 1) * a' := by
    apply inclW_injective
    rw [← ha']
    have h4 : inclW l ((D.locA l).actW σ a0) = (D.locA l).actWCbHom σ (m0 : WCb l) := by
      rw [ha0, inclW_act]; rfl
    rw [map_sub, map_sub, map_add (f := _), inclW_zl, map_mul (inclW l), map_mul (inclW l), inclW_zl,
      inclW_zl, h4, ← ha0, ← ha]
    change _ = (l : ℤ_[l]) ^ N • scaled ψ r hψ (f ⟨σ, hσ⟩) • (one : WCb l) -
      (u • (D.locA l).actWCbHom σ (m0 : WCb l) + (l : ℤ_[l]) ^ r • (m : WCb l) - (m0 : WCb l))
    rw [hone, smul_smul, ← Algebra.algebraMap_eq_smul_one, Algebra.smul_def, Algebra.smul_def]
  have h5 := congrArg (io (D.locA l)) h3
  rw [map_sub, map_sub, map_add (f := _), io_zl _ (D.locT l), map_mul (io _), map_mul (io _),
    map_mul (io _), map_pow (io _), io_zl _ (D.locT l), io_zl _ (D.locT l), io_act] at h5
  have h6 : io (D.locA l) (D.locA l).ξ ^ (e + 1) * io (D.locA l) a' ∈
      FilB (D.loc l) ((e : ℤ) + 1) := by
    have := FilB_mul (FilB_pow (io_ξ_mem (D.locA l)) (e + 1)) (io_mem (D.locA l) a')
    simpa using this
  refine ⟨a, ?_⟩
  have h7 := qB_mul_mem ((l : ℚ_[l]) ^ r)⁻¹ h6
  rw [← h5] at h7
  convert h7 using 1
  have h8 : qB (D.loc l) ((l : ℚ_[l]) ^ r)⁻¹ * qB (D.loc l) ((l : ℚ_[l]) ^ r) = 1 := by
    rw [← map_mul, inv_mul_cancel₀ hlr, map_one]
  rw [map_mul ((D.loc l).actQdR σ), AlgEquiv.commutes, hc σ hσ, ← io_apply, PadicInt.coe_mul,
    scaled_coe, PadicInt.coe_pow, PadicInt.coe_pow, PadicInt.coe_natCast, hu]
  simp only [map_mul]
  linear_combination (-(qB (D.loc l) ((l : ℚ_[l]) ^ N) * qB (D.loc l) (ψ (f ⟨σ, hσ⟩))) + io (D.locA l) a) * h8

end GlobalTheory.PushCob
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CutValueMemHeckeValueIdealOffSupport
section
namespace GlobalTheory.Cut

open Formalism Formalism.MainNotions Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Module GlobalTheory.Pass GlobalTheory.Cut

theorem cutVal_exists_single {O X : Type} [CommRing O] [IsDomain O] [Fintype X]
    (T : Subalgebra O (X → O)) (hsep : ∀ x y : X, x ≠ y → ∃ f ∈ T, f x ≠ f y) (x : X) :
    ∃ g ∈ T, g x ≠ 0 ∧ ∀ y, y ≠ x → g y = 0 := by
  classical
  have key : ∀ y : X, ∃ f ∈ T, f x ≠ 0 ∧ (y ≠ x → f y = 0) := by
    intro y
    by_cases hy : y = x
    · exact ⟨1, one_mem _, one_ne_zero, fun h => absurd hy h⟩
    · obtain ⟨f, hf, hne⟩ := hsep y x hy
      refine ⟨f - algebraMap _ _ (f y), sub_mem hf (Subalgebra.algebraMap_mem _ _), ?_, fun _ => ?_⟩
      · simpa [sub_eq_zero] using hne.symm
      · simp
  choose f hf h1 h2 using key
  refine ⟨∏ y, f y, prod_mem fun y _ => hf y, ?_, fun y hy => ?_⟩
  · rw [Finset.prod_apply]
    exact Finset.prod_ne_zero_iff.2 fun y _ => h1 y
  · rw [Finset.prod_apply]
    exact Finset.prod_eq_zero (Finset.mem_univ y) (h2 y hy)

theorem cutVal_coord_eq_zero {O X X' ι : Type} [CommRing O] [IsDomain O] [Fintype X] [Fintype ι]
    (T : Subalgebra O (X → O)) (hsep : ∀ x y : X, x ≠ y → ∃ f ∈ T, f x ≠ f y)
    (p : X' → X) (b : ι → X' → O)
    (huniq : ∀ cf : ι → T, (0 : X' → O) = ∑ k, ((fun x' => (cf k : X → O) (p x')) : X' → O) * b k →
      cf = 0)
    (cf : ι → T) (x : X)
    (h0 : ∀ x', p x' = x → (∑ k, ((fun x' => (cf k : X → O) (p x')) : X' → O) * b k) x' = 0)
    (k : ι) : (cf k : X → O) x = 0 := by
  obtain ⟨g, hg, hx, hy⟩ := cutVal_exists_single T hsep x
  have h := huniq (fun k => ⟨g, hg⟩ * cf k) (by
    funext x'
    have : (∑ k, ((fun x' => (((⟨g, hg⟩ : T) * cf k : T) : X → O) (p x')) : X' → O) * b k) x' =
        g (p x') * (∑ k, ((fun x' => (cf k : X → O) (p x')) : X' → O) * b k) x' := by
      simp [Finset.sum_apply, Finset.mul_sum, mul_assoc]
    rw [this]
    by_cases hp : p x' = x
    · rw [h0 x' hp]; simp
    · rw [hy _ hp]; simp)
  have h2 : g x * (cf k : X → O) x = 0 := by
    have := congrArg (fun c : ι → T => (c k : X → O) x) h
    simpa using this
  exact (mul_eq_zero.1 h2).resolve_left hx

theorem value_mem_ccOff :
    ∀ (D : D7) (i : D.nd.Loc) (r : D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i))) (ρ : D.nd.X i → (GE D.nd →* GL (Fin D.R.r) (D.nd.O i))) (π : D.nd.X i) (Xs : Set (D.nd.X i)) (S : IdempotentChoiceData D.nd i), GoodR D.nd i r → GoodCongruenceObjects D.nd r ρ π S → π ∈ Xs → ∀ f ∈ S.T', (∀ x', S.p x' ∈ Xs → S.p x' ∉ D.nd.Z i → f x' = 0) → f S.π' ∈ ccOff i Xs π := by
  intro D i r ρ π Xs S _ hS _ f hf h0
  obtain ⟨-, -, -, -, -, -, -, ⟨-, -, -, ⟨b, -, hb⟩, -⟩, -, ⟨hπ, -⟩, -⟩ := hS
  obtain ⟨cf, hcf, -⟩ := hb f hf
  have huniq : ∀ c : Fin D.R.t.factorial → D.nd.T i,
      (0 : S.X' → D.nd.O i) = ∑ k, ((fun x' => (c k : D.nd.X i → D.nd.O i) (S.p x')) :
        S.X' → D.nd.O i) * b k → c = 0 := by
    intro c hc
    obtain ⟨c0, -, hc0⟩ := hb 0 (zero_mem _)
    rw [hc0 c hc, hc0 0 (by funext x'; simp)]
  have hz : ∀ k, ∀ x ∈ Xs, x ∉ D.nd.Z i → (cf k : D.nd.X i → D.nd.O i) x = 0 := by
    intro k x hx hZ
    refine cutVal_coord_eq_zero (D.nd.T i) (D.nd.T_sep i) S.p b huniq cf x (fun x' hp => ?_) k
    rw [← hcf]
    exact h0 x' (hp ▸ hx) (hp ▸ hZ)
  rw [hcf, Finset.sum_apply]
  refine Ideal.sum_mem _ fun k _ => ?_
  rw [Pi.mul_apply]
  refine Ideal.mul_mem_right _ _ (Ideal.subset_span ⟨cf k, (cf k).2, hz k, ?_⟩)
  rw [hπ]

end GlobalTheory.Cut
end

