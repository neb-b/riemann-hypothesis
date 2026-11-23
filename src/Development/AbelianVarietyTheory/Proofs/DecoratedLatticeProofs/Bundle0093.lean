module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0008
public import Development.AbelianVarietyTheory.Counterexamples.JetSurvey.LatticeAndConstantUnique
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.Bundle0033
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0066
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0008
public import Formalism.LocalToGlobal.IndefiniteReal.OrthogonalComplementCharacterisation
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ExistsHeightLeTwoMulQuotHeight
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.WittDecompSymplInclIsotropicInclAnisotropic
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0019
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0007

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsNatEqMul
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.FinPl GlobalTheory.MixPer GlobalTheory.MixModel GlobalTheory.Unf GlobalTheory.LatPair ValuativeRel NumberField Filter
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open IsDedekindDomain
open scoped TensorProduct

noncomputable section
namespace GlobalTheory.FinPl.AlmostAll

theorem exists_nat_eq_mul {E : Type} [Field E] [NumberField E] {c : 𝓞 E} (hc : c ≠ 0) :
    ∃ n : ℕ, n ≠ 0 ∧ ∃ c' : 𝓞 E, (n : 𝓞 E) = c * c' := by
  refine ⟨Ideal.absNorm (Ideal.span {c}), ?_, ?_⟩
  · rw [Ne, Ideal.absNorm_eq_zero_iff, Ideal.span_singleton_eq_bot]
    exact hc
  · obtain ⟨c', hc'⟩ := Ideal.mem_span_singleton'.1 (Ideal.absNorm_mem (Ideal.span {c}))
    exact ⟨c', by rw [← hc', mul_comm]⟩

theorem exists_nat_bounds {E : Type} [Field E] [NumberField E]
    {I : FractionalIdeal (nonZeroDivisors (𝓞 E)) E} (hI : I ≠ 0) :
    ∃ N M : ℕ, N ≠ 0 ∧ M ≠ 0 ∧ (∀ a ∈ I, ∃ b : 𝓞 E, (N : E) * a = algebraMap (𝓞 E) E b) ∧ (M : E) ∈ I := by
  obtain ⟨d, hd, hint⟩ := I.isFractional
  obtain ⟨N, hN, d', hdd'⟩ := exists_nat_eq_mul (nonZeroDivisors.ne_zero hd)
  have hsub : (I : Submodule (𝓞 E) E) ≠ ⊥ := FractionalIdeal.coeToSubmodule_ne_bot.2 hI
  obtain ⟨x, hxI, hx0⟩ := (Submodule.ne_bot_iff _).1 hsub
  obtain ⟨⟨r, s⟩, hrs⟩ := IsLocalization.surj (nonZeroDivisors (𝓞 E)) x
  simp only at hrs
  have hs0 : algebraMap (𝓞 E) E (s : 𝓞 E) ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective (𝓞 E) E)).2 (nonZeroDivisors.ne_zero s.2)
  have hr0 : r ≠ 0 := by
    rintro rfl
    rw [map_zero, mul_eq_zero] at hrs
    exact hrs.elim hx0 hs0
  have hrI : algebraMap (𝓞 E) E r ∈ (I : Submodule (𝓞 E) E) := by
    rw [← hrs, mul_comm, ← Algebra.smul_def]
    exact Submodule.smul_mem _ _ hxI
  obtain ⟨M, hM, r', hrr'⟩ := exists_nat_eq_mul hr0
  refine ⟨N, M, hN, hM, fun a ha => ?_, ?_⟩
  · obtain ⟨b, hb⟩ := hint a (FractionalIdeal.mem_coe.2 ha)
    refine ⟨d' * b, ?_⟩
    rw [map_mul, hb, Algebra.smul_def, ← mul_assoc, ← map_mul, mul_comm d' d, ← hdd', map_natCast]
  · have : (M : E) = r' • algebraMap (𝓞 E) E r := by
      rw [Algebra.smul_def, ← map_mul, mul_comm r' r, ← hrr', map_natCast]
    rw [← FractionalIdeal.mem_coe, this]
    exact Submodule.smul_mem _ _ hrI

theorem eventually_notMem {F : Type} [Field F] [NumberField F] {N : ℕ} (hN : N ≠ 0) :
    ∀ᶠ v : HeightOneSpectrum (𝓞 F) in cofinite, (N : 𝓞 F) ∉ v.asIdeal := by
  have h0 : (N : 𝓞 F) ≠ 0 := Nat.cast_ne_zero.2 hN
  have hI : Ideal.span {(N : 𝓞 F)} ≠ 0 := by
    rwa [Ne, Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot]
  refine Filter.eventually_cofinite.2 ((Ideal.finite_factors hI).subset ?_)
  intro v hv
  simp only [Set.mem_setOf_eq, not_not] at hv ⊢
  rw [Ideal.dvd_iff_le, Ideal.span_singleton_le_iff_mem]
  exact hv

theorem inv_mem_integers {F : Type} [Field F] [NumberField F] {N : ℕ} {v : HeightOneSpectrum (𝓞 F)}
    (hv : (N : 𝓞 F) ∉ v.asIdeal) : algebraMap F (Fv F v) (N : F)⁻¹ ∈ v.adicCompletionIntegers F := by
  have h1 : v.valuation F (N : F) = 1 := by
    rw [← map_natCast (algebraMap (𝓞 F) F), HeightOneSpectrum.valuation_of_algebraMap]
    exact HeightOneSpectrum.intValuation_eq_one_iff.2 hv
  have h2 : Valued.v (algebraMap F (Fv F v) (N : F)) = 1 := by
    rw [← h1]
    exact HeightOneSpectrum.valuedAdicCompletion_eq_valuation' (v := v) (N : F)
  rw [HeightOneSpectrum.mem_adicCompletionIntegers, map_inv₀, map_inv₀, h2, inv_one]

theorem smul_inv_mem {F : Type} [Field F] [NumberField F] {N : ℕ} {v : HeightOneSpectrum (𝓞 F)}
    (hv : (N : 𝓞 F) ∉ v.asIdeal) {α : Af F} (hα : α ∈ intAf F) (h0 : ∀ w, ¬ w = v → evalV F w α = 0) :
    (N : F)⁻¹ • α ∈ intAf F ∧ ∀ w, ¬ w = v → evalV F w ((N : F)⁻¹ • α) = 0 := by
  have key : ∀ w, evalV F w ((N : F)⁻¹ • α) = algebraMap F (Fv F w) (N : F)⁻¹ * evalV F w α := by
    intro w
    rw [map_smul, Algebra.smul_def]
  have hα' : ∀ w, evalV F w α ∈ w.adicCompletionIntegers F := hα
  refine ⟨fun w => ?_, fun w hw => ?_⟩
  · rw [key]
    by_cases hw : w = v
    · subst hw
      exact mul_mem (inv_mem_integers hv) (hα' w)
    · rw [h0 w hw, mul_zero]
      exact zero_mem _
  · rw [key, h0 w hw, mul_zero]

theorem pairA_smul {F : Type} [Field F] [NumberField F] (c : F) (α : Af F) :
    pairA F 0 (c • α) = c • pairA F 0 α := by
  show ((0 : Ainf F), c • α) = c • ((0 : Ainf F), α)
  rw [Prod.smul_mk, smul_zero]

theorem tmul_eq {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E] {N : ℕ} (hN : N ≠ 0) (α : Af F) (z : E) :
    pairA F 0 α ⊗ₜ[F] z = pairA F 0 ((N : F)⁻¹ • α) ⊗ₜ[F] ((N : E) * z) := by
  have hN' : (N : F) ≠ 0 := Nat.cast_ne_zero.2 hN
  have hz : (N : E) * z = (N : F) • z := by
    rw [Algebra.smul_def, map_natCast]
  rw [hz, TensorProduct.tmul_smul, TensorProduct.smul_tmul', ← pairA_smul, smul_smul,
    mul_inv_cancel₀ hN', one_smul]

theorem latA_eq_latV (D : D7) :
    ∀ᶠ v : Pl D in cofinite, ∀ (S : HSp D) (L : Lat S), latA S L (· = v) = latV S L (· = v) := by
  obtain ⟨N, M, hN, hM, hNI, hMI⟩ := exists_nat_bounds (GlobalTheory.ModelLatticeCheck.AA_ne_zero D)
  filter_upwards [eventually_notMem (F := D.host.F) hN, eventually_notMem (F := D.host.F) hM]
    with v hvN hvM
  intro S L
  apply le_antisymm
  · rw [latA, latMul, AddSubgroup.closure_le]
    rintro y ⟨α, hα, h0, a, ha, x, hx, rfl⟩
    obtain ⟨b, hb⟩ := hNI a ha
    obtain ⟨hα', h0'⟩ := smul_inv_mem hvN hα h0
    rw [latV, latMul]
    refine AddSubgroup.subset_closure ⟨(N : D.host.F)⁻¹ • α, hα', h0', 1, rfl, b • x, L.smul_mem b hx, ?_⟩
    funext i
    have e : (N : D.host.E) * (a * x i) = 1 * (b • x) i := by
      rw [one_mul, Pi.smul_apply, Algebra.smul_def, ← hb, mul_assoc]
    rw [tmul_eq hN α (a * x i), e]
  · rw [latV, latMul, AddSubgroup.closure_le]
    rintro y ⟨α, hα, h0, a, ha, x, hx, rfl⟩
    rw [Set.mem_singleton_iff] at ha
    subst ha
    obtain ⟨hα', h0'⟩ := smul_inv_mem hvM hα h0
    rw [latA, latMul]
    refine AddSubgroup.subset_closure ⟨(M : D.host.F)⁻¹ • α, hα', h0', (M : D.host.E), hMI, x, hx, ?_⟩
    funext i
    rw [one_mul, tmul_eq hM α (x i)]

end GlobalTheory.FinPl.AlmostAll
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsTameRamified
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.FinPl GlobalTheory.MixPer GlobalTheory.MixModel GlobalTheory.Unf GlobalTheory.LatPair ValuativeRel NumberField Filter
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.RamLine

variable {D : D7}

def intRing (D : D7) : Subring (AE D) := (GlobalTheory.CharFin.hatRing D.host.F D.host.E).comap (finPart D)

theorem mem_intRing (z : AE D) : z ∈ intRing D ↔ finPart D z ∈ intAE D := by
  rw [GlobalTheory.IdeleParts.integralFiniteAdeles_eq_adelicCompletion_integers]
  exact Iff.rfl

theorem finPart_cA (z : AE D) : finPart D (cA D z) = sigR (Af D.host.F) D.sp.cm.sig (finPart D z) := by
  induction z using TensorProduct.induction_on with
  | zero => simp only [map_zero]
  | tmul a x => rfl
  | add a b ha hb => simp only [map_add (f := _), ha, hb]

theorem cA_cA' (z : AE D) : cA D (cA D z) = z := by
  induction z using TensorProduct.induction_on with
  | zero => simp only [map_zero]
  | tmul a x =>
    change a ⊗ₜ[D.host.F] star (star x) = _
    rw [star_star]
  | add a b ha hb => simp only [map_add (f := _), ha, hb]

theorem cA_mem {z : AE D} (hz : z ∈ intRing D) : cA D z ∈ intRing D := by
  rw [mem_intRing] at hz ⊢
  rw [finPart_cA]
  have : intAE D ≤ (intAE D).comap (sigR (Af D.host.F) D.sp.cm.sig).toAddMonoidHom := by
    refine (AddSubgroup.closure_le _).2 ?_
    rintro _ ⟨a, ha, x, rfl⟩
    exact AddSubgroup.subset_closure
      ⟨a, ha, RingOfIntegers.mapRingEquiv (starRingAut : D.host.E ≃+* D.host.E) x, rfl⟩
  exact this hz

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

variable (p : SplitPt D k)

variable {p} {N : ℕ}

section Line

variable {S : HSp D} [Subsingleton (Fin S.rank)] (i : Fin S.rank)


end Line

end GlobalTheory.RamLine
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsUnifUnit
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.FinPl GlobalTheory.MixPer GlobalTheory.MixModel GlobalTheory.Unf GlobalTheory.LatPair ValuativeRel NumberField Filter
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.FinPl.SplitApprox

variable {D : D7}

theorem cA_tmul (a : AF D.host.F) (x : D.host.E) : cA D (a ⊗ₜ[D.host.F] x) = a ⊗ₜ[D.host.F] star x := rfl

theorem cA_cA (z : AE D) : cA D (cA D z) = z := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul a x => rw [cA_tmul, cA_tmul, star_star]
  | add x y hx hy => rw [map_add (f := _), map_add (f := _), hx, hy]

theorem finPart_tmul (a : AF D.host.F) (x : D.host.E) :
    finPart D (a ⊗ₜ[D.host.F] x) = sndA D.host.F a ⊗ₜ[D.host.F] x := rfl

theorem approx_gen {F A B E : Type} [Field F] [CharZero F] [CommRing A] [CommRing B] [CommRing E] [Algebra F A]
    [Algebra F B] [Algebra F E] (φ : A → B) (σ : E →+* E) (fp : A ⊗[F] E →+* B ⊗[F] E) (c : A ⊗[F] E →+* A ⊗[F] E)
    (hfp : ∀ a x, fp (a ⊗ₜ[F] x) = φ a ⊗ₜ[F] x) (h1 : φ 1 = 1) (hc : ∀ a x, c (a ⊗ₜ[F] x) = a ⊗ₜ[F] σ x)
    (O : Set B) (I : AddSubgroup (B ⊗[F] E)) (hI : ∀ b ∈ O, ∀ x : E, IsIntegral ℤ x → b ⊗ₜ[F] x ∈ I)
    (hE : ∀ x : E, ∃ m : ℤ, m ≠ 0 ∧ IsIntegral ℤ (m • x)) (N : ℕ)
    (hB : ∀ y : B, ∃ (f : F) (β : B), β ∈ O ∧ y = algebraMap F B f + N • β) (z : A ⊗[F] E) :
    ∃ x : E, ∃ a ∈ I, ∃ a' ∈ I, fp (z - 1 ⊗ₜ[F] x) = N * a ∧ fp (c z - c (1 ⊗ₜ[F] x)) = N * a' := by
  induction z using TensorProduct.induction_on with
  | zero => exact ⟨0, 0, zero_mem _, 0, zero_mem _, by simp, by simp⟩
  | add x y hx hy =>
    obtain ⟨d, a, ha, a', ha', h, h'⟩ := hx
    obtain ⟨e, b, hb, b', hb', g, g'⟩ := hy
    refine ⟨d + e, a + b, add_mem ha hb, a' + b', add_mem ha' hb', ?_, ?_⟩
    · rw [mul_add, ← h, ← g, ← map_add (f := _), TensorProduct.tmul_add]; congr 1; ring
    · rw [mul_add, ← h', ← g', ← map_add fp, TensorProduct.tmul_add, map_add c, map_add c]; congr 1; ring
  | tmul a x =>
    obtain ⟨m, hm, hx⟩ := hE x
    have hm' : (m : F) ≠ 0 := Int.cast_ne_zero.2 hm
    obtain ⟨f, β, hβ, hy⟩ := hB ((m : F)⁻¹ • φ a)
    have key : ∀ x : E, fp (a ⊗ₜ[F] x - 1 ⊗ₜ[F] (f • (m • x))) = N * (β ⊗ₜ[F] (m • x)) := by
      intro x
      have e2 : φ a ⊗ₜ[F] x = ((m : F)⁻¹ • φ a) ⊗ₜ[F] (m • x) := by
        rw [TensorProduct.smul_tmul, ← Int.cast_smul_eq_zsmul F, smul_smul, inv_mul_cancel₀ hm', one_smul]
      rw [map_sub, hfp, hfp, h1, e2, hy, TensorProduct.add_tmul, Algebra.algebraMap_eq_smul_one,
        TensorProduct.smul_tmul f, add_sub_cancel_left, ← TensorProduct.smul_tmul', nsmul_eq_mul]
    have hx' : IsIntegral ℤ (m • σ x) := by
      rw [← map_zsmul]
      exact hx.map σ.toIntAlgHom
    refine ⟨f • (m • x), _, hI _ hβ _ hx, _, hI _ hβ _ hx', key x, ?_⟩
    rw [hc, ← TensorProduct.smul_tmul, hc, TensorProduct.smul_tmul, map_zsmul]
    exact key _

theorem cancel_gen {F R : Type} [Field F] [CharZero F] [CommRing R] [Algebra F R] {N : ℕ} (hN : 0 < N) {a b : R}
    (h : (N : R) * a = N * b) : a = b := by
  have : IsUnit (N : R) := by
    have := (IsUnit.mk0 (N : F) (Nat.cast_ne_zero.2 hN.ne')).map (algebraMap F R)
    rwa [map_natCast] at this
  exact this.mul_left_cancel h

theorem tmul_mem {a : Af D.host.F} (ha : a ∈ intAf D.host.F) {x : D.host.E} (hx : IsIntegral ℤ x) :
    a ⊗ₜ[D.host.F] x ∈ intAE D :=
  AddSubgroup.subset_closure ⟨a, ha, ⟨x, hx⟩, rfl⟩

theorem mul_mem_intAE {a b : Af D.host.F ⊗[D.host.F] D.host.E} (ha : a ∈ intAE D) (hb : b ∈ intAE D) :
    a * b ∈ intAE D := by
  induction ha using AddSubgroup.closure_induction with
  | zero => rw [zero_mul]; exact zero_mem _
  | add x y _ _ hx hy => rw [add_mul]; exact add_mem hx hy
  | neg x _ hx => rw [neg_mul]; exact neg_mem hx
  | mem x hx =>
    induction hb using AddSubgroup.closure_induction with
    | zero => rw [mul_zero]; exact zero_mem _
    | add x y _ _ hx hy => rw [mul_add]; exact add_mem hx hy
    | neg x _ hx => rw [mul_neg]; exact neg_mem hx
    | mem y hy =>
      obtain ⟨a, ha, x, rfl⟩ := hx
      obtain ⟨b, hb, y, rfl⟩ := hy
      rw [Algebra.TensorProduct.tmul_mul_tmul]
      refine tmul_mem (fun v => ?_) (x.2.mul y.2)
      rw [map_mul]; exact mul_mem (ha v) (hb v)

theorem approx (N : ℕ) (hN : 0 < N) (z : AE D) : ∃ c : D.host.E, ∃ A ∈ intAE D, ∃ A' ∈ intAE D,
    finPart D (z - incA D c) = N * A ∧ finPart D (cA D z - incA D (star c)) = N * A' :=
  approx_gen (F := D.host.F) (sndA D.host.F) (starRingEnd D.host.E) (finPart D) (cA D) finPart_tmul (map_one _) cA_tmul
    (intAf D.host.F) (intAE D) (fun _ hb _ hx => tmul_mem hb hx)
    (fun x => ((IsFractionRing.isAlgebraic_iff ℤ ℚ D.host.E).2
      (Algebra.IsAlgebraic.isAlgebraic (R := ℚ) x)).exists_integral_multiple) N
    (GlobalTheory.AdLat.strong_approximation_mod_nat D.host.F N hN).1 z

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem val_le (p : SplitPt D k) (N : ℕ) (hN : 0 < N) (z : AE D) (A : Af D.host.F ⊗[D.host.F] D.host.E)
    (hA : A ∈ intAE D) (h : finPart D z = N * A) : valuation k (p.pr z) ≤ valuation k (N : k) := by
  have hNE : (N : D.host.E) ≠ 0 := Nat.cast_ne_zero.2 hN.ne'
  have hNk : (N : k) ≠ 0 := by
    have := (map_ne_zero (p.pr.comp (incA D))).2 hNE
    rwa [map_natCast] at this
  have he : finPart D p.e ∈ intAE D := by
    have := (p.int_iff 1).1 (one_mem _)
    rwa [← map_one p.pr, p.sec_pr, mul_one] at this
  have h0 : (N : AE D) * p.sec (p.pr z / N) = p.e * z := by
    rw [← p.sec_pr, ← nsmul_eq_mul, ← AddMonoidHom.map_nsmul, nsmul_eq_mul, mul_div_cancel₀ _ hNk]
  have h1 := congrArg (finPart D) h0
  rw [RingHom.map_mul, RingHom.map_mul, h, mul_left_comm] at h1
  have h1' : finPart D (N : AE D) = N := map_natCast (finPart D) N
  rw [h1'] at h1
  have h2 := cancel_gen (F := D.host.F) hN h1
  have h3 : p.pr z / N ∈ 𝒪[k] := (p.int_iff _).2 (by rw [h2]; exact mul_mem_intAE he hA)
  have h4 : valuation k (p.pr z / N) ≤ 1 := h3
  have h5 : p.pr z = N * (p.pr z / N) := (mul_div_cancel₀ _ hNk).symm
  rw [h5, map_mul]
  exact mul_le_of_le_one_right' h4

theorem exists_nat (q : Unif k) : valuation k ((q.1 : 𝒪[k]) : k) < 1 ∧
    ∃ N : ℕ, 0 < N ∧ valuation k (N : k) < valuation k ((q.1 : 𝒪[k]) : k) := by
  have hlt : ∀ x : 𝒪[k], ¬ IsUnit x → valuation k (x : k) < 1 := fun x hx =>
    Valuation.Integer.not_isUnit_iff_valuation_lt_one.1 hx
  have hq := hlt _ q.2.not_isUnit
  refine ⟨hq, ?_⟩
  classical
  letI := Fintype.ofFinite (IsLocalRing.ResidueField 𝒪[k])
  set Q := Fintype.card (IsLocalRing.ResidueField 𝒪[k])
  have hQ : (Q : 𝒪[k]) ∈ IsLocalRing.maximalIdeal 𝒪[k] := by
    rw [← IsLocalRing.residue_eq_zero_iff, map_natCast]
    exact FiniteField.cast_card_eq_zero _
  rw [q.2.maximalIdeal_eq, Ideal.mem_span_singleton] at hQ
  obtain ⟨r, hr⟩ := hQ
  have hr' : (Q : k) = (q.1 : k) * r := by exact_mod_cast congrArg (fun x : 𝒪[k] => (x : k)) hr
  have hle : valuation k (Q : k) ≤ valuation k ((q.1 : 𝒪[k]) : k) := by
    rw [hr', map_mul]; exact mul_le_of_le_one_right' r.2
  have hq0 : 0 < valuation k ((q.1 : 𝒪[k]) : k) := by
    rw [Valuation.pos_iff]
    exact fun h => q.2.ne_zero (Subtype.ext h)
  refine ⟨Q * Q, Nat.mul_pos Fintype.card_pos Fintype.card_pos, ?_⟩
  rw [Nat.cast_mul, map_mul]
  exact (mul_le_mul' hle hle).trans_lt (mul_lt_of_lt_one_right hq0 hq)

theorem exists_unif_unit : ∀ (D : D7) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (p : SplitPt D k) (q : Unif k), ∃ c : D.host.E, valuation k (p.pr (incA D c)) = valuation k ((q.1 : 𝒪[k]) : k) ∧ valuation k (p.pr (incA D (star c))) = 1 := by
  intro D k _ _ _ _ p q
  obtain ⟨hq, N, hN, hNq⟩ := exists_nat q
  have hs : p.sec 1 = p.e := by rw [← map_one p.pr, p.sec_pr, mul_one]
  have he : p.pr p.e = 1 := by rw [← hs, p.pr_sec]
  have hce : p.pr (cA D p.e) = 0 := by
    have h : p.e * cA D p.e = 0 := p.split.2.1
    have := congrArg p.pr h
    rwa [map_mul, he, one_mul, map_zero] at this
  have hcq : ∀ a, p.pr (cA D (p.sec a)) = 0 := fun a => by
    have h : p.sec a = p.e * p.sec a := by rw [← p.sec_pr, p.pr_sec]
    rw [h, map_mul, map_mul, hce, zero_mul]
  obtain ⟨c, A, hA, A', hA', h, h'⟩ := approx N hN (p.sec (q.1 : k) + cA D p.e)
  have v1 := val_le p N hN _ A hA h
  have v2 := val_le p N hN _ A' hA' h'
  rw [map_sub, map_add (f := _), p.pr_sec, hce, add_zero] at v1
  rw [map_sub, map_add (f := _), map_add (f := _), hcq, cA_cA, he, zero_add] at v2
  refine ⟨c, ?_, ?_⟩
  · exact Valuation.map_eq_of_sub_lt _ (by rw [Valuation.map_sub_swap]; exact v1.trans_lt hNq)
  · rw [← map_one (valuation k)]
    exact Valuation.map_eq_of_sub_lt _ (by rw [Valuation.map_sub_swap, map_one]; exact v2.trans_lt (hNq.trans hq))

end GlobalTheory.FinPl.SplitApprox
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FlatThetaMapsPreserveThetaFunctions
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Unf.FlatTheta

variable {D : D7} {σ : ℕ}

def lastQ (B : BesLev D σ) : Matrix (Fin B.V.rank) (Fin (σ + 1)) D.host.E :=
  Matrix.of fun k => Fin.snoc (α := fun _ => D.host.E) (B.d.e k) ((B.d.i₀ *ᵥ vecB B.o B.ζ) k)

theorem rat_lastQ (B : BesLev D σ) : rat (lastQ B) = xLast B.d (vecB B.o B.ζ) := by
  funext k j
  refine Fin.lastCases ?_ (fun i => ?_) j
  · have := congrFun (ratV_mulVec B.d.i₀ (vecB B.o B.ζ)) k
    simp only [xLast, lastQ, rat, Matrix.map_apply, Matrix.of_apply, Fin.snoc_last]
    exact this
  · simp only [xLast, lastQ, rat, Matrix.map_apply, Matrix.of_apply, Fin.snoc_castSucc]
    rfl

theorem zeta_ne (B : BesLev D σ) : B.ζ ≠ 0 := fun h => B.line.2 (by rw [h]; simp)

theorem lastQ_indep (B : BesLev D σ) : LinearIndependent D.host.E (lastQ B).transpose := by
  have key : ∀ c : Fin (σ + 1) → D.host.E, lastQ B *ᵥ c =
      B.d.e *ᵥ (fun i => c i.castSucc) + c (Fin.last σ) • (B.d.i₀ *ᵥ (B.o.iB *ᵥ B.ζ)) := fun c => by
    funext k
    change ∑ j, lastQ B k j * c j = ∑ i, B.d.e k i * c i.castSucc + c (Fin.last σ) * (B.d.i₀ *ᵥ vecB B.o B.ζ) k
    rw [Fin.sum_univ_castSucc, mul_comm (c _)]
    simp only [lastQ, Matrix.of_apply, Fin.snoc_castSucc, Fin.snoc_last]
  refine Matrix.mulVec_injective_iff.1 ((injective_iff_map_eq_zero (lastQ B).mulVecLin).2 fun c hc => ?_)
  rw [Matrix.mulVecLin_apply, key] at hc
  have h1 := congrArg (B.d.qX *ᵥ ·) hc
  have h2 := congrArg ((B.o.qB * B.d.q0) *ᵥ ·) hc
  have a1 : B.d.qX * B.d.i₀ = 0 := rat_injective (by rw [rat_mul, rat_zero]; exact B.d.pX_j0)
  have a2 : B.d.q0 * B.d.e = 0 := rat_injective (by rw [rat_mul, rat_zero]; exact B.d.p0_jX)
  have a3 : B.d.q0 * B.d.i₀ = 1 := rat_injective (by rw [rat_mul, rat_one]; exact B.d.p0_j0)
  simp only [Matrix.mulVec_add, Matrix.mulVec_smul, Matrix.mulVec_mulVec, Matrix.mulVec_zero, qX_e, Matrix.one_mulVec,
    ← Matrix.mul_assoc, a1, Matrix.zero_mul, Matrix.zero_mulVec, smul_zero, add_zero] at h1
  have a4 : B.o.qB * B.d.q0 * B.d.e = 0 := by rw [Matrix.mul_assoc, a2, Matrix.mul_zero]
  have a5 : B.o.qB * B.d.q0 * B.d.i₀ * B.o.iB = 1 := by
    rw [Matrix.mul_assoc B.o.qB, a3, Matrix.mul_one, B.o.qB_iB]
  simp only [Matrix.mulVec_add, Matrix.mulVec_smul, Matrix.mulVec_mulVec, Matrix.mulVec_zero,
    ← Matrix.mul_assoc, a4, a5, Matrix.zero_mulVec, zero_add, Matrix.one_mulVec] at h2
  funext j
  refine Fin.lastCases ?_ (fun i => congrFun h1 i) j
  exact (smul_eq_zero.1 h2).resolve_right (zeta_ne B)

theorem flat_isThetaFun : ∀ D : D7, FlatLaw D → ∀ (ψ : AddChar (AF D.host.F) ℂ), (∀ (ρ : ℕ) (B : BesLev D ρ) (J : JacLev D ρ) (s : StepBF ψ B J) Ψ, IsThetaFunO ψ B.V J.W Ψ → IsThetaFunO ψ B.V₀ J.W₀ (flatBF s Ψ)) ∧ ∀ (σ : ℕ) (J : JacLev D (σ + 1)) (B : BesLev D σ) (s : StepFB ψ J B) Ψ, IsThetaFunO ψ J.W B.V Ψ → IsThetaFunO ψ J.W₀ B.V₀ (flatFB s Ψ) := by
  intro D hF ψ
  refine ⟨fun ρ B J s Ψ hΨ => ?_, fun σ J B s Ψ hΨ => ?_⟩
  · exact (hF ψ s.weil.std B.V B.V₀ J.W J.W₀ ρ ρ B.d J.d s.vS s.vT s.vU J.d.e (isIsoSub_e J.d).1
      (yZero B.V₀ ρ (vecB B.o B.ζ)) Ψ hΨ).2
  · have h := (hF ψ s.weil.std J.W J.W₀ B.V B.V₀ (σ + 1) σ J.d B.d s.vS s.vT s.vU (lastQ B) (lastQ_indep B) 0 Ψ hΨ).2
    rw [rat_lastQ] at h
    exact h

end GlobalTheory.Unf.FlatTheta

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.HeisenbergOperatorDisjointSupportSmulAdd
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.FinPl GlobalTheory.MixPer
open IsDedekindDomain NumberField Matrix
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.HeisDisj

variable {D : D7}

theorem cA_smul (c : AF D.host.F) (z : AE D) : cA D (c • z) = c • cA D z := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul a e => rw [TensorProduct.smul_tmul']; rfl
  | add a b ha hb => rw [smul_add, map_add (f := _), map_add (f := _), ha, hb, smul_add]

theorem hO_add_left (S T : HSp D) (x x' y : WO S T) : hO S T (x + x') y = hO S T x y + hO S T x' y := by
  simp only [hO, Matrix.add_apply, mul_add, Finset.sum_add_distrib]

theorem hO_add_right (S T : HSp D) (x y y' : WO S T) : hO S T x (y + y') = hO S T x y + hO S T x y' := by
  simp only [hO, Matrix.add_apply, map_add (f := _), mul_add, add_mul, Finset.sum_add_distrib]

theorem hO_smul_smul (S T : HSp D) (c c' : AF D.host.F) (x y : WO S T) :
    hO S T (c • x) (c' • y) = (c * c') • hO S T x y := by
  simp only [hO, Matrix.smul_apply, cA_smul, Finset.smul_sum, mul_smul_comm, smul_mul_assoc, smul_smul]

theorem symplOH_add_left (S T : HSp D) (x x' y : WO S T) :
    symplOH S T (x + x') y = symplOH S T x y + symplOH S T x' y := by
  simp only [symplOH, symplO, hO_add_left, mul_add, map_add (f := _)]

theorem symplOH_add_right (S T : HSp D) (x y y' : WO S T) :
    symplOH S T x (y + y') = symplOH S T x y + symplOH S T x y' := by
  simp only [symplOH, symplO, hO_add_right, mul_add, map_add (f := _)]

theorem symplOH_smul_smul_eq_zero (S T : HSp D) (c c' : AF D.host.F) (x y : WO S T) (h : c * c' = 0) :
    symplOH S T (c • x) (c' • y) = 0 := by
  rw [symplOH, symplO, hO_smul_smul, h, zero_smul, mul_zero, map_zero, mul_zero]

theorem heisO_smul_add_smul : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (c c' : AF D.host.F) (x y : WO S T) (f : WO S T → ℂ), c * c' = 0 → heisO ψ S T (c • x + c' • y) f = heisO ψ S T (c • x) (heisO ψ S T (c' • y) f) := by
  intro D ψ S T c c' x y f h
  funext w
  simp only [heisO]
  rw [symplOH_add_right, symplOH_add_left, symplOH_smul_smul_eq_zero S T c c' x y h, add_zero,
    AddChar.map_add_eq_mul, add_assoc, mul_assoc]

end GlobalTheory.HeisDisj
end

