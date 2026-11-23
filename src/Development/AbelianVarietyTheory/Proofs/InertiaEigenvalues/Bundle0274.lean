module

public import Mathlib
public import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
public import Formalism.LocalRingCardinality.AdicCompletionLocal.LocTied
public import Formalism.SharpRestriction.LevelLetterCocycles.LocalSituation
public import Formalism.SharpRestriction.LevelLetterCocycles.LocCoh
public import Formalism.GaloisCohomology.LocalTateDualityK
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0247
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.AcrisTorsionFreeComplete
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0241
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0260
public import Development.AbelianVarietyTheory.CrystallinePeriods.RingIface
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CardLeOfSpan
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0039
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0011
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0030
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0010
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0008
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0257
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0252
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0250
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.FinrankMaxUnramifiedSubfieldPadicFinExtPos
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0159
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0254
public import Formalism.SharpRestriction.LevelLetterCocycles.Bundle0006
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0004

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsTraceFormIntegralIffGoodCoeff
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct Module

namespace GlobalTheory.GoodCoeff

theorem exists_trace_form_integral_iff : ∀ (l : ℕ) [Fact l.Prime] (LL : Type) [Field LL] [Algebra ℚ_[l] LL] [TopologicalSpace LL] (O : Type) [CommRing O] [Algebra O LL], GoodO (Qp := ℚ_[l]) LL O → ∃ lam : LL →ₗ[ℚ_[l]] ℚ_[l], ∀ a : LL, (∀ b : O, ∃ u : ℤ_[l], lam (a * algebraMap O LL b) = (u : ℚ_[l])) ↔ ∃ b : O, algebraMap O LL b = a := by
  intro l _ LL _ _ _ O _ _ hG
  have hint := (good_coeff_integers l LL O hG).1
  obtain ⟨⟨hD, hDVR, hFr⟩, hfin, hmod, htop, hopen⟩ := hG
  haveI := hD
  haveI := hDVR
  haveI := hFr
  haveI : FiniteDimensional ℚ_[l] LL := hfin
  letI : Algebra ℤ_[l] LL := ((algebraMap ℚ_[l] LL).comp (algebraMap ℤ_[l] ℚ_[l])).toAlgebra
  haveI : IsScalarTower ℤ_[l] ℚ_[l] LL := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  let A : Subring LL := (algebraMap O LL).range
  have hZ : ∀ u : ℤ_[l], algebraMap ℤ_[l] LL u ∈ A := fun u =>
    padicInt_mem A (by rw [RingHom.coe_range]; exact hopen) u
  have hinj : Function.Injective (algebraMap O LL) := IsFractionRing.injective O LL
  let ψ : O ≃+* A := RingEquiv.ofBijective (algebraMap O LL).rangeRestrict
    ⟨fun a b h => hinj (congrArg Subtype.val h), (algebraMap O LL).rangeRestrict_surjective⟩
  have hψ : ∀ a : A, algebraMap O LL (ψ.symm a) = a := fun a =>
    congrArg Subtype.val (ψ.apply_symm_apply a)
  let f : ℤ_[l] →+* O := ψ.symm.toRingHom.comp ((algebraMap ℤ_[l] LL).codRestrict A hZ)
  letI : Algebra ℤ_[l] O := f.toAlgebra
  haveI : IsScalarTower ℤ_[l] O LL := IsScalarTower.of_algebraMap_eq
    (fun u => (hψ ((algebraMap ℤ_[l] LL).codRestrict A hZ u)).symm)
  haveI : IsIntegralClosure O ℤ_[l] LL :=
    { algebraMap_injective := hinj
      isIntegral_iff := fun {x} => by
        rw [← Set.mem_range]
        exact (hint x).symm }
  let D : FractionalIdeal (nonZeroDivisors O) LL := FractionalIdeal.dual ℤ_[l] ℚ_[l] 1
  have hD0 : D ≠ 0 := FractionalIdeal.dual_ne_zero ℤ_[l] ℚ_[l] one_ne_zero
  haveI hP : (D : Submodule O LL).IsPrincipal := FractionalIdeal.isPrincipal D
  set c : LL := Submodule.IsPrincipal.generator (D : Submodule O LL) with hc
  have hDc : (D : Submodule O LL) = Submodule.span O {c} :=
    (Submodule.IsPrincipal.span_singleton_generator _).symm
  have hc0 : c ≠ 0 := by
    intro h
    apply hD0
    apply FractionalIdeal.coeToSubmodule_injective
    show (D : Submodule O LL) = ((0 : FractionalIdeal (nonZeroDivisors O) LL) : Submodule O LL)
    rw [hDc, h, FractionalIdeal.coe_zero]
    exact Submodule.span_singleton_eq_bot.2 rfl
  refine ⟨(Algebra.trace ℚ_[l] LL).comp (LinearMap.mulLeft ℚ_[l] c), fun a => ?_⟩
  have key : (∀ b : O, ∃ u : ℤ_[l], (Algebra.trace ℚ_[l] LL) (c * (a * algebraMap O LL b)) = (u : ℚ_[l]))
      ↔ c * a ∈ D := by
    rw [FractionalIdeal.mem_dual (one_ne_zero : (1 : FractionalIdeal (nonZeroDivisors O) LL) ≠ 0)]
    constructor
    · intro h y hy
      obtain ⟨b, rfl⟩ := (FractionalIdeal.mem_one_iff _).1 hy
      obtain ⟨u, hu⟩ := h b
      refine ⟨u, ?_⟩
      rw [Algebra.traceForm_apply, mul_assoc, hu]
      rfl
    · intro h b
      obtain ⟨u, hu⟩ := h _ ((FractionalIdeal.mem_one_iff _).2 ⟨b, rfl⟩)
      refine ⟨u, ?_⟩
      rw [Algebra.traceForm_apply, mul_assoc] at hu
      rw [← hu]
      rfl
  simp only [LinearMap.comp_apply, LinearMap.mulLeft_apply]
  rw [key, ← FractionalIdeal.mem_coe, hDc, Submodule.mem_span_singleton]
  constructor
  · rintro ⟨z, hz⟩
    refine ⟨z, ?_⟩
    rw [Algebra.smul_def, mul_comm] at hz
    exact mul_left_cancel₀ hc0 hz
  · rintro ⟨z, rfl⟩
    exact ⟨z, by rw [Algebra.smul_def, mul_comm]⟩

end GlobalTheory.GoodCoeff
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsUnramifiedPeriodAinfUnit
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc GlobalTheory.MemLoc
open scoped Formalism.Per

namespace GlobalTheory.MemLoc

theorem exists_pow_eq_one_algClosure_coprime (l : ℕ) [Fact l.Prime] (a : AlgebraicClosure (ZMod l))
    (ha : a ≠ 0) : ∃ m : ℕ, 0 < m ∧ ¬ l ∣ m ∧ a ^ m = 1 := by
  have hint : IsIntegral (ZMod l) a := Algebra.IsIntegral.isIntegral a
  let K := IntermediateField.adjoin (ZMod l) ({a} : Set (AlgebraicClosure (ZMod l)))
  haveI : FiniteDimensional (ZMod l) K := IntermediateField.adjoin.finiteDimensional hint
  haveI : Finite K := Module.finite_of_finite (ZMod l)
  letI : Fintype K := Fintype.ofFinite K
  let b : K := ⟨a, IntermediateField.mem_adjoin_simple_self _ a⟩
  have hb : b ≠ 0 := fun h => ha (congrArg Subtype.val h)
  have h1 : 1 < Fintype.card K := Fintype.one_lt_card
  refine ⟨Fintype.card K - 1, by omega, ?_, ?_⟩
  · intro hd
    have h0 : ((Fintype.card K - 1 : ℕ) : K) = 0 := by
      obtain ⟨c, hc⟩ := hd
      have hl : ((l : ℕ) : K) = 0 := by
        rw [← map_natCast (algebraMap (ZMod l) K), ZMod.natCast_self, map_zero]
      rw [hc, Nat.cast_mul, hl, zero_mul]
    rw [Nat.cast_sub h1.le, FiniteField.cast_card_eq_zero] at h0
    simp at h0
  · have := congrArg Subtype.val (FiniteField.pow_card_sub_one_eq_one b hb)
    simpa [b] using this

theorem exists_unit_frobenius_eq_mul (l : ℕ) [Fact l.Prime] (k : Type) [Field k] [CharP k l] [IsAlgClosed k]
    (u : WittVector l k) (hu : IsUnit u) :
    ∃ w : WittVector l k, IsUnit w ∧ WittVector.frobenius w = u * w := by
  have h1 : (1 : WittVector l k).coeff 0 ≠ 0 := by simp
  have h2 : u.coeff 0 ≠ 0 := (hu.map (WittVector.constantCoeff (p := l) (R := k))).ne_zero
  refine ⟨WittVector.frobeniusRotation l h1 h2, ?_, ?_⟩
  · apply WittVector.isUnit_of_coeff_zero_ne_zero
    simpa [WittVector.frobeniusRotation, WittVector.frobeniusRotationCoeff] using
      WittVector.RecursionBase.solution_nonzero l h1 h2
  · have := WittVector.frobenius_frobeniusRotation l h1 h2
    rwa [mul_one, mul_comm] at this

private theorem padicInt_ringHom_ext (l : ℕ) [Fact l.Prime] {R : Type*} [CommRing R]
    [IsHausdorff (Ideal.span {(l : R)}) R] (f g : ℤ_[l] →+* R) : f = g := by
  refine RingHom.ext fun x => ?_
  refine sub_eq_zero.1 (IsHausdorff.haus (inferInstance : IsHausdorff (Ideal.span {(l : R)}) R) _ fun n => ?_)
  obtain ⟨c, hc⟩ := Ideal.mem_span_singleton'.1 (PadicInt.appr_spec n x)
  have hx : x = c * (l : ℤ_[l]) ^ n + (x.appr n : ℤ_[l]) := by rw [hc]; ring
  have h : f x - g x = (f c - g c) * (l : R) ^ n := by
    rw [hx]
    simp only [map_add (f := _), map_mul, map_pow, map_natCast]
    ring
  rw [SModEq.zero, smul_eq_mul, Ideal.mul_top, Ideal.span_singleton_pow, h]
  exact Ideal.mul_mem_left _ _ (Ideal.mem_span_singleton_self _)

theorem exists_unramified_period : ∀ (l : ℕ) [Fact l.Prime] (F : GQ l), (∀ (x : Om l) (m : ℕ), 0 < m → ¬ l ∣ m → x ^ m = 1 → F x = x ^ l) → ∀ u : ℤ_[l]ˣ, ∃ w : Per.Ainf l, IsUnit w ∧ (∀ g ∈ (MaximalUnramifiedExtension l).fixingSubgroup, Per.σA g w = w) ∧ Per.σA F w = Per.zA l u * w ∧ Per.φA l w = Per.zA l u * w := by
  intro l _ F hF u
  obtain ⟨f⟩ := _root_.GlobalTheory.Per.nonempty_algClosure_zmod_to_tilt l
  let u' : WittVector l (AlgebraicClosure (ZMod l)) :=
    WittVector.map (ZMod.castHom (dvd_refl l) _) (WittVector.fromPadicInt l u)
  have hu' : IsUnit u' := (u.isUnit.map _).map _
  obtain ⟨w₀, hw₀, hφ⟩ := exists_unit_frobenius_eq_mul l _ u' hu'
  have hfu : WittVector.map f u' = Per.zA l u := by
    exact RingHom.congr_fun (padicInt_ringHom_ext l (R := Per.Ainf l)
      ((WittVector.map f).comp ((WittVector.map (ZMod.castHom (dvd_refl l) _)).comp
        (WittVector.fromPadicInt l))) (Per.zA l)) u
  have hact : ∀ (g : GQ l) (n : ℕ), n ≠ 0 →
      (∀ (x : Om l) (m : ℕ), 0 < m → ¬ l ∣ m → x ^ m = 1 → g x = x ^ n) →
      ∀ a, Per.σF g (f a) = f a ^ n := by
    intro g n hn hg a
    by_cases ha : a = 0
    · rw [ha, map_zero, map_zero, zero_pow hn]
    · obtain ⟨m, hm, hl, ham⟩ := exists_pow_eq_one_algClosure_coprime l a ha
      exact GlobalTheory.T.tilt_galois_action_root_of_unity_coprime l (f a) m n g hm hl (by rw [← map_pow, ham, map_one])
        fun x hx => hg x m hm hl hx
  have hφA : Per.φA l (WittVector.map f w₀) = Per.zA l u * WittVector.map f w₀ := by
    rw [← hfu, ← map_mul, ← hφ]
    refine WittVector.ext fun n => ?_
    rw [GlobalTheory.RingIface.phiA_coeff]
    simp only [WittVector.map_coeff, WittVector.coeff_frobenius_charP, map_pow]
  refine ⟨WittVector.map f w₀, hw₀.map _, fun g hg => ?_, ?_, hφA⟩
  · refine WittVector.ext fun n => ?_
    have := hact g 1 one_ne_zero (fun x m hm hl hx => by
      rw [pow_one]
      exact (IntermediateField.mem_fixingSubgroup_iff _ _).1 hg x
        (IntermediateField.subset_adjoin _ _ ⟨m, hm, hl, hx⟩)) (w₀.coeff n)
    rw [pow_one] at this
    rw [GlobalTheory.RingIface.sigA_coeff, WittVector.map_coeff]
    exact this
  · rw [← hφA]
    refine WittVector.ext fun n => ?_
    rw [GlobalTheory.RingIface.sigA_coeff, GlobalTheory.RingIface.phiA_coeff, WittVector.map_coeff]
    exact hact F l (Fact.out : l.Prime).ne_zero hF (w₀.coeff n)

end GlobalTheory.MemLoc
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsWachModuleGeneratorReduction
section
open GlobalTheory.PhiGam GlobalTheory.AdmLoc GlobalTheory.Models GlobalTheory.TopSteps GlobalTheory.Present GlobalTheory.RedFun Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc
open scoped LaurentSeries PowerSeries TensorProduct

namespace GlobalTheory.RedFun

theorem exists_extend_of_dense {A E F : Type} [CommRing A] [CommRing E] [CommRing F] (ι : A →+* E) (f : A →+* F)
    (π P : A) (hf : IsUnit (f π)) (hP : f P = 0)
    (hd : ∀ e : E, ∃ (a : A) (m : ℕ) (y : E), e * ι π ^ m = ι a + ι P * y)
    (hs : ∀ (a : A) (y : E), ι a = ι P * y → ∃ b, a = P * b) :
    ∃ g : E →+* F, (∀ a, g (ι a) = f a) := by
  first
  | exact @_root_.GlobalTheory.RelationExtension.exists_extension
  | exact _root_.GlobalTheory.RelationExtension.exists_extension
  | (apply _root_.GlobalTheory.RelationExtension.exists_extension <;> assumption)
  | (intros; apply _root_.GlobalTheory.RelationExtension.exists_extension <;> assumption)
  | (intros; apply @_root_.GlobalTheory.RelationExtension.exists_extension <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.RelationExtension.exists_extension ..)

theorem exists_letter_reduction : ∀ {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K] [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K] {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B] [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR] [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR] {PD : PeriodData G Qp K₀ K B BdR} {LL O : Type} [Field LL] [Algebra Qp LL] [CommRing O] [Algebra O LL] [TopologicalSpace LL] {v : AddValuation LL (WithTop ℚ)} {n : ℕ} (W : LocWach PD LL O v n) {k : Type} [Field k] [Algebra O k] (lam : O), Function.Surjective (algebraMap O k) → (∀ x, algebraMap O k x = 0 ↔ lam ∣ x) → ((PD.p : ℕ) : k) = 0 → ∃ p : ZMod n → (W.EE →+* k⸨X⸩), (∀ i (a : LetA O n), p i (algebraMap (LetA O n) W.EE a) = ((PowerSeries.map (algebraMap O k) (a i) : k⟦X⟧) : k⸨X⸩)) ∧ (∀ i, Function.Surjective (p i)) ∧ ∀ i e, p i e = 0 → ∃ e', algebraMap (LetA O n) W.EE (letE i) * e = algebraMap O W.EE lam * e' := by
  intro G _ _ Qp K₀ K _ _ _ _ _ _ _ B BdR _ _ _ _ _ _ _ _ _ _ _ PD LL O _ _ _ _ _ v n W k _ _ lam hsurj hker hp
  let f : ZMod n → (LetA O n →+* k⸨X⸩) := fun i =>
    (algebraMap k⟦X⟧ k⸨X⸩).comp ((PowerSeries.map (algebraMap O k)).comp (Pi.evalRingHom (fun _ => O⟦X⟧) i))
  have hf : ∀ i (a : LetA O n), f i a = algebraMap k⟦X⟧ k⸨X⸩ (PowerSeries.map (algebraMap O k) (a i)) :=
    fun _ _ => rfl
  have hX : ∀ i, f i letπ = algebraMap k⟦X⟧ k⸨X⸩ PowerSeries.X := fun i => by
    rw [hf, letπ, PowerSeries.map_X]
  have hu : IsUnit (algebraMap k⟦X⟧ k⸨X⸩ PowerSeries.X) :=
    IsLocalization.map_units k⸨X⸩ (⟨PowerSeries.X, Submonoid.mem_powers _⟩ : Submonoid.powers (PowerSeries.X : k⟦X⟧))
  have hP : ∀ i, f i (PD.p : LetA O n) = 0 := fun i => by
    rw [map_natCast, ← map_natCast (algebraMap k k⸨X⸩), hp, map_zero]
  have hd : ∀ e : W.EE, ∃ (a : LetA O n) (m : ℕ) (y : W.EE), e * algebraMap (LetA O n) W.EE letπ ^ m =
      algebraMap (LetA O n) W.EE a + algebraMap (LetA O n) W.EE (PD.p : LetA O n) * y := by
    intro e
    obtain ⟨a, m, h⟩ := W.EE_dense e 1
    obtain ⟨y, hy⟩ := Ideal.mem_span_singleton'.1 h
    refine ⟨a, m, y, ?_⟩
    rw [map_pow, pow_one] at hy
    rw [map_natCast]
    linear_combination -hy
  have hs : ∀ (a : LetA O n) (y : W.EE), algebraMap (LetA O n) W.EE a =
      algebraMap (LetA O n) W.EE (PD.p : LetA O n) * y → ∃ b, a = (PD.p : LetA O n) * b := by
    intro a y h
    have := W.EE_sat a 1 (Ideal.mem_span_singleton'.2 ⟨y, by rw [h, map_natCast, pow_one, mul_comm]⟩)
    simpa using this
  choose p hpa using fun i => exists_extend_of_dense (algebraMap (LetA O n) W.EE) (f i) letπ (PD.p : LetA O n)
    (by rw [hX]; exact hu) (hP i) hd hs
  obtain ⟨u, hπ⟩ := W.EE_π.exists_right_inv
  refine ⟨p, fun i a => hpa i a, fun i c => ?_, fun i e he => ?_⟩
  · obtain ⟨⟨s, ⟨_, m, rfl⟩⟩, h⟩ := IsLocalization.surj (Submonoid.powers (PowerSeries.X : k⟦X⟧)) c
    obtain ⟨t, rfl⟩ := PowerSeries.map_surjective _ hsurj s
    refine ⟨algebraMap (LetA O n) W.EE (fun _ => t) * u ^ m, ?_⟩
    have h1 := congrArg (p i) hπ
    rw [map_mul, hpa, hX, map_one] at h1
    simp only [map_pow] at h
    rw [map_mul, hpa, hf, map_pow, ← h, mul_assoc, ← mul_pow, h1, one_pow, mul_one]
  · obtain ⟨a, m, y, h⟩ := hd e
    have h1 := congrArg (p i) h
    rw [map_mul, he, zero_mul, map_add (f := _), map_mul, hpa, hpa, hP, zero_mul, add_zero, hf] at h1
    have h2 : PowerSeries.map (algebraMap O k) (a i) = 0 :=
      (IsFractionRing.injective k⟦X⟧ k⸨X⸩) (by rw [map_zero]; exact h1.symm)
    have h3 : ∀ j, ∃ d, PowerSeries.coeff j (a i) = lam * d := fun j => (hker _).1 (by
      have := congrArg (PowerSeries.coeff j) h2
      simpa using this)
    choose d hd' using h3
    obtain ⟨c, hc⟩ := (hker (PD.p : O)).1 (by rw [map_natCast, hp])
    have h4 : letE i * a = algebraMap O (LetA O n) lam * (letE i * fun _ => PowerSeries.mk d) := by
      funext j
      by_cases hj : j = i
      · subst hj
        ext l
        simp [letE, hd']
      · simp [letE, hj]
    have h5 : (PD.p : LetA O n) = algebraMap O (LetA O n) lam * algebraMap O (LetA O n) c := by
      rw [← map_mul, ← hc, map_natCast]
    have h6 := congrArg (algebraMap (LetA O n) W.EE) h4
    rw [h5] at h
    simp only [map_mul] at h h6
    rw [IsScalarTower.algebraMap_apply O (LetA O n) W.EE]
    have h7 : algebraMap (LetA O n) W.EE letπ ^ m * u ^ m = 1 := by rw [← mul_pow, hπ, one_pow]
    refine ⟨(algebraMap (LetA O n) W.EE (letE i) * algebraMap (LetA O n) W.EE (fun _ => PowerSeries.mk d) +
      algebraMap (LetA O n) W.EE (letE i) * algebraMap (LetA O n) W.EE (algebraMap O (LetA O n) c) * y) * u ^ m, ?_⟩
    linear_combination (algebraMap (LetA O n) W.EE (letE i) * u ^ m) * h + u ^ m * h6 -
      (algebraMap (LetA O n) W.EE (letE i) * e) * h7

end GlobalTheory.RedFun
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExtensionBlockPeriodMatrixSemistable
section
open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations GlobalTheory.Pst GlobalTheory.PMon TensorProduct
open scoped Formalism.Per

noncomputable section

namespace GlobalTheory.PMon

theorem extPeriodMatrix : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (a b : Type) [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b] (K : FinExt l) (ρ : ↥(GK K) →* GL (a ⊕ b) ↥(MaximalUnramifiedExtension l)) (ρ₁ : ↥(GK K) →* GL a ↥(MaximalUnramifiedExtension l)) (ρ₂ : ↥(GK K) →* GL b ↥(MaximalUnramifiedExtension l)) (c : ↥(GK K) → Matrix a b ↥(MaximalUnramifiedExtension l)), (∀ g, (ρ g : Matrix (a ⊕ b) (a ⊕ b) ↥(MaximalUnramifiedExtension l)) = Matrix.fromBlocks (ρ₁ g : Matrix a a ↥(MaximalUnramifiedExtension l)) (c g) 0 (ρ₂ g : Matrix b b ↥(MaximalUnramifiedExtension l))) → ∀ (Q₁ : GL a (Bst P)) (Q₂ : GL b (Bst P)), (∀ g : ↥(GK K), (ρ₁ g : Matrix a a ↥(MaximalUnramifiedExtension l)).map (ks P) * (Q₁ : Matrix a a (Bst P)).map (actSt P (g : GQ l)) = Q₁) → (∀ g : ↥(GK K), (ρ₂ g : Matrix b b ↥(MaximalUnramifiedExtension l)).map (ks P) * (Q₂ : Matrix b b (Bst P)).map (actSt P (g : GQ l)) = Q₂) → ∀ v : a × b → Bst P, (∀ g : ↥(GK K), (fun i => ks P (extCoc ρ₂ c g i)) = ((homRep ρ₁ ρ₂ g : Matrix (a × b) (a × b) ↥(MaximalUnramifiedExtension l)).map (ks P)).mulVec (fun i => actSt P (g : GQ l) (v i)) - v) → ∃ Q : GL (a ⊕ b) (Bst P), ∀ g : ↥(GK K), (ρ g : Matrix (a ⊕ b) (a ⊕ b) ↥(MaximalUnramifiedExtension l)).map (ks P) * (Q : Matrix (a ⊕ b) (a ⊕ b) (Bst P)).map (actSt P (g : GQ l)) = Q := by
  intro l _ P a b _ _ _ _ K ρ ρ₁ ρ₂ c hρ Q₁ Q₂ h₁ h₂ v hv
  let β : Matrix a b (Bst P) := Matrix.of fun i j => v (i, j)
  have hvβ : v = vecM β := rfl
  let Qm : Matrix (a ⊕ b) (a ⊕ b) (Bst P) :=
    Matrix.fromBlocks (Q₁ : Matrix a a (Bst P)) (-(β * (Q₂ : Matrix b b (Bst P)))) 0 (Q₂ : Matrix b b (Bst P))
  let Qi : Matrix (a ⊕ b) (a ⊕ b) (Bst P) :=
    Matrix.fromBlocks ((Q₁⁻¹ : GL a (Bst P)) : Matrix a a (Bst P)) (((Q₁⁻¹ : GL a (Bst P)) : Matrix a a (Bst P)) * β) 0
      ((Q₂⁻¹ : GL b (Bst P)) : Matrix b b (Bst P))
  have hQ : Qm * Qi = 1 := by
    simp only [Qm, Qi, Matrix.fromBlocks_multiply, Units.mul_inv, Matrix.mul_zero, Matrix.zero_mul, add_zero, zero_add,
      ← Matrix.mul_assoc, Matrix.neg_mul, Matrix.one_mul, Matrix.mul_assoc β, Units.mul_inv, Matrix.mul_one,
      add_neg_cancel, Matrix.fromBlocks_one]
  have hQ' : Qi * Qm = 1 := by
    simp only [Qm, Qi, Matrix.fromBlocks_multiply, Units.inv_mul, Matrix.mul_zero, Matrix.zero_mul, add_zero, zero_add,
      Matrix.mul_neg, ← Matrix.mul_assoc, neg_add_cancel, neg_zero, Matrix.fromBlocks_one]
  refine ⟨⟨Qm, Qi, hQ, hQ'⟩, fun g => ?_⟩
  set σ : Bst P →+* Bst P := (actSt P (g : GQ l)).toRingHom with hσ
  have hσc : ⇑(actSt P (g : GQ l)) = ⇑σ := rfl
  have hc : ((c g * (((ρ₂ g)⁻¹ : GL b ↥(MaximalUnramifiedExtension l)) : Matrix b b ↥(MaximalUnramifiedExtension l))).map (ks P)) =
      (ρ₁ g : Matrix a a ↥(MaximalUnramifiedExtension l)).map (ks P) * β.map σ * (((ρ₂ g)⁻¹ : GL b ↥(MaximalUnramifiedExtension l)) : Matrix b b ↥(MaximalUnramifiedExtension l)).map (ks P) - β := by
    apply vecM_injective
    have h := hv g
    rw [homRep_apply, hvβ] at h
    have e1 : (fun i => actSt P (g : GQ l) (vecM β i)) = vecM (β.map σ) := rfl
    rw [e1, homUnit_mulVec] at h
    exact h
  have hR : (((ρ₂ g)⁻¹ : GL b ↥(MaximalUnramifiedExtension l)) : Matrix b b ↥(MaximalUnramifiedExtension l)).map (ks P) * (ρ₂ g : Matrix b b ↥(MaximalUnramifiedExtension l)).map (ks P) = 1 := by
    rw [← Matrix.map_mul, Units.inv_mul, Matrix.map_one _ (map_zero _) (map_one _)]
  have hQ2 : (Q₂ : Matrix b b (Bst P)).map σ =
      (((ρ₂ g)⁻¹ : GL b ↥(MaximalUnramifiedExtension l)) : Matrix b b ↥(MaximalUnramifiedExtension l)).map (ks P) * (Q₂ : Matrix b b (Bst P)) := by
    calc (Q₂ : Matrix b b (Bst P)).map σ
        = ((((ρ₂ g)⁻¹ : GL b ↥(MaximalUnramifiedExtension l)) : Matrix b b ↥(MaximalUnramifiedExtension l)).map (ks P) * (ρ₂ g : Matrix b b ↥(MaximalUnramifiedExtension l)).map (ks P)) *
            (Q₂ : Matrix b b (Bst P)).map σ := by rw [hR, Matrix.one_mul]
      _ = _ := by rw [Matrix.mul_assoc]; exact congrArg _ (h₂ g)
  have hC : (c g).map (ks P) * (Q₂ : Matrix b b (Bst P)).map σ =
      ((ρ₁ g : Matrix a a ↥(MaximalUnramifiedExtension l)).map (ks P) * β.map σ * (((ρ₂ g)⁻¹ : GL b ↥(MaximalUnramifiedExtension l)) : Matrix b b ↥(MaximalUnramifiedExtension l)).map (ks P) - β) *
        (Q₂ : Matrix b b (Bst P)) := by
    rw [hQ2, ← hc, Matrix.map_mul, Matrix.mul_assoc]
  show (ρ g : Matrix (a ⊕ b) (a ⊕ b) ↥(MaximalUnramifiedExtension l)).map (ks P) * Qm.map σ = Qm
  rw [hρ g]
  simp only [Qm, Matrix.fromBlocks_map, Matrix.fromBlocks_multiply, Matrix.map_zero _ (map_zero _), Matrix.mul_zero,
    Matrix.zero_mul, add_zero, zero_add]
  have e1 := h₁ g
  have e2 := h₂ g
  rw [hσc] at e1 e2
  rw [e1, e2]
  congr 1
  rw [Matrix.map_neg _ (map_neg σ), Matrix.map_mul, hC, hQ2]
  simp only [Matrix.sub_mul, Matrix.mul_neg, Matrix.mul_assoc]
  abel

end GlobalTheory.PMon
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FiniteDimensionalDstOfIsSst
section
open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N GlobalTheory.Pst GlobalTheory.PMon TensorProduct Module
open scoped Formalism.Per

namespace GlobalTheory.Pst

theorem finiteDimensional_Dst_of_isSst : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (K : FinExt l) (V : Type)
    [AddCommGroup V] [Module ℚ_[l] V] [FiniteDimensional ℚ_[l] V] (ρ : Representation ℚ_[l] ↥(GK K) V),
    IsSst P ρ → FiniteDimensional ℚ_[l] ↥(Dst P ρ) := by
  intro l _ P K V _ _ _ ρ h
  haveI : FiniteDimensional ℚ_[l] ↥(K0 K) := (P.PD K).finK₀
  by_cases hV : 0 < finrank ℚ_[l] V
  · have hK : 0 < finrank ℚ_[l] ↥(K0 K) := Module.finrank_pos
    have hpos : 0 < finrank ℚ_[l] ↥(Dst P ρ) := by
      unfold IsSst at h
      rw [h]
      exact Nat.mul_pos hK hV
    exact Module.finite_of_finrank_pos hpos
  · have h0 : finrank ℚ_[l] V = 0 := Nat.eq_zero_of_not_pos hV
    haveI : Subsingleton V := Module.finrank_zero_iff.mp h0
    haveI : Subsingleton (V ⊗[ℚ_[l]] Bst P) := by
      refine ⟨fun x y => ?_⟩
      have hx : ∀ z : V ⊗[ℚ_[l]] Bst P, z = 0 := by
        intro z
        induction z using TensorProduct.induction_on with
        | zero => rfl
        | tmul v b => rw [Subsingleton.elim v 0, zero_tmul]
        | add x y hx hy => rw [hx, hy, add_zero]
      rw [hx x, hx y]
    infer_instance

end GlobalTheory.Pst
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FiniteDimensionalKsOfGood
section
open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.MainNotions.LocalSituation GlobalTheory.Cyc
open scoped TensorProduct

namespace GlobalTheory.Cyc.CrysDeRham

variable {l : ℕ} [Fact l.Prime]

theorem finiteDimensional_Ks_of_good {K LL : FinExt l} {s : ℕ} (h : Good K s LL) :
    FiniteDimensional ℚ_[l] ↥(Ks K s) := by
  have hle : Ks K s ≤ LL.1 := fun x hx => h.2.2.2 (Ks K s).val ⟨x, hx⟩
  have := LL.2
  exact FiniteDimensional.of_injective (IntermediateField.inclusion hle).toLinearMap
    (IntermediateField.inclusion_injective hle)

theorem apply_mem_Ks (K : FinExt l) (s : ℕ) :
    ∀ g ∈ GK K, ∀ x ∈ Ks K s, g x ∈ Ks K s := by
  intro g hg
  have key : Ks K s ≤ (Ks K s).comap (g : Om l →ₐ[ℚ_[l]] Om l) := by
    refine sup_le ?_ ?_
    · intro x hx
      have h1 : g x = x := hg ⟨x, hx.1⟩
      change g x ∈ Ks K s
      rw [h1]
      exact (le_sup_left : K0 K ≤ Ks K s) hx
    · rw [IntermediateField.adjoin_le_iff]
      intro x hx
      change g x ∈ Ks K s
      apply (le_sup_right : _ ≤ Ks K s)
      apply IntermediateField.subset_adjoin
      have hx' : x ^ (l ^ s) = 1 := hx
      change (g x) ^ (l ^ s) = 1
      rw [← map_pow, hx', map_one]
  intro x hx
  exact key hx

noncomputable def restrictRep {K E LL : FinExt l} (hle : K.1 ≤ E.1)
    (T : LocLat ↥(GK K) ℚ_[l] ↥LL.1 ↥(OL LL)) : GRep ↥(GK E) ℚ_[l] ↥LL.1 ↥(OL LL) where
  V := T.V
  modO := T.modO
  towO := T.towO
  ρ := T.ρ.comp (Subgroup.inclusion (GK_le hle))
  cont x := (T.cont x).comp (continuous_inclusion (GK_le hle))

theorem isDR_of_restrict (P : LocPrime l) {K E LL : FinExt l} (hle : K.1 ≤ E.1)
    (hs : ∀ g ∈ GK K, ∀ x ∈ E.1, g x ∈ E.1) (T : LocLat ↥(GK K) ℚ_[l] ↥LL.1 ↥(OL LL))
    (h : IsDR (P.PD E) (restrictRep hle T).ρ) : IsDR (P.PD K) T.ρ :=
  GlobalTheory.T.isDeRham_of_restrict_galois_descent l P K E LL (GK_le hle) hle hs T.V T.ρ h


set_option maxHeartbeats 1600000 in
theorem isDR_of_isCrysOn : ∀ (D : Formalism.BasicNotions.D7) (HW : HWOf D.loc), adm7 D → ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (s : ℕ) (LL : FinExt l) (h : Good K s LL), let S := sit D.loc HW l (D.locA l) K s LL h; ∀ (T : LocLat S.G S.Qp S.LL S.O), IsCrysOn S S.W.GKs T → IsDR S.PD T.ρ := by
  intro D HW hF l _ K s LL h S T hT
  let E : FinExt l := ⟨Ks K s, finiteDimensional_Ks_of_good h⟩
  have hle : K.1 ≤ E.1 := h.2.2.1
  have h1 := isCrys_Ks_of_finrank l (D.loc l) K s LL _ ((HW l).W K s LL h) ((HW l).W_s K s LL h)
    E rfl hle T hT
  have h2 := (hF l E ↥LL.1 ↥(OL LL) (GlobalTheory.LocalIntegers.goodO_integers l LL)
    (restrictRep hle T)).2.2 h1
  exact isDR_of_restrict (D.loc l) hle (apply_mem_Ks K s) T h2

end GlobalTheory.Cyc.CrysDeRham
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FinrankKsEq
section
open NumberField IsDedekindDomain Formalism Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations GlobalTheory.HubLoc Module

namespace GlobalTheory.HubLoc

theorem finrank_Ks_eq : ∀ (l : ℕ) [Fact l.Prime] (K : Loc.FinExt l) (s : ℕ), 0 < s → finrank ℚ_[l] ↥(Loc.Ks K s) = finrank ℚ_[l] ↥(Loc.K0 K) * (l ^ (s - 1) * (l - 1)) := by
  intro l _ K s hs
  rw [GlobalTheory.Cyc.finrank_Ks K s hs, mul_comm (l - 1)]

end GlobalTheory.HubLoc
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FlatOverProductPowerSeriesRingStatement
section
open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc TensorProduct GlobalTheory.NL Formalism.MainNotions.DeltaInvariantLattices
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.flat_over_product_power_series_ring : ∀ (O : Type) [CommRing O] [IsNoetherianRing O] (n : ℕ) [NeZero n] (E : Type) [CommRing E] [Algebra (LetA O n) E] (p : ℕ), IsUnit (algebraMap (LetA O n) E letπ) → IsAdicComplete (Ideal.span {(p : E)}) E → (∀ (x : E) (k : ℕ), ∃ (a : LetA O n) (m : ℕ), x * algebraMap (LetA O n) E (letπ ^ m) - algebraMap (LetA O n) E a ∈ Ideal.span {(p : E) ^ k}) → (∀ (a : LetA O n) (k : ℕ), algebraMap (LetA O n) E a ∈ Ideal.span {(p : E) ^ k} → ∃ b : LetA O n, a = (p : LetA O n) ^ k * b) → Module.Flat (LetA O n) E := by
  first | exact @GlobalTheory.FlatLocCompl.flat_letA | exact GlobalTheory.FlatLocCompl.flat_letA | (intros; apply GlobalTheory.FlatLocCompl.flat_letA <;> assumption)
end

