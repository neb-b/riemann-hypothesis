module

public import Mathlib
public import ReciprocityTheory.AnalyticForms.PotentialTheory.IsPotentialOfFun
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.IsIntersectionFamily
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsHilbert
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle0005

@[expose] public section

-- bundled from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.BergmanObjects
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MeasureTheory Set ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M
open scoped ComplexConjugate ENNReal ContDiff

noncomputable section

variable {D : ℕ} {X : Type} [TopologicalSpace X]

structure HolLineBundle (A : FinHolAtlas D X) where

  g : Fin A.n → Fin A.n → X → ℂ
  holo : ∀ j k, A.HoloOn ((A.chart j).source ∩ (A.chart k).source) (g j k)
  ne_zero : ∀ j k, ∀ x ∈ (A.chart j).source ∩ (A.chart k).source, g j k x ≠ 0
  cocycle : ∀ j k l, ∀ x ∈ (A.chart j).source ∩ (A.chart k).source ∩ (A.chart l).source,
    g j l x = g j k x * g k l x

namespace HolLineBundle

variable {A : FinHolAtlas D X} (L : HolLineBundle A)

def sections (n : ℕ) : Submodule ℂ (Fin A.n → X → ℂ) where
  carrier := {f | (∀ j, A.HoloOn (A.chart j).source (f j)) ∧
    (∀ j k, ∀ x ∈ (A.chart j).source ∩ (A.chart k).source, f j x = L.g j k x ^ n * f k x) ∧
    ∀ j, ∀ x ∉ (A.chart j).source, f j x = 0}
  add_mem' := by
    rintro f f' ⟨hf, hc, hz⟩ ⟨hf', hc', hz'⟩
    refine ⟨fun j k => (hf j k).add (hf' j k), fun j k x hx => ?_, fun j x hx => ?_⟩
    · simp only [Pi.add_apply, hc j k x hx, hc' j k x hx]; ring
    · simp [hz j x hx, hz' j x hx]
  zero_mem' := by
    refine ⟨fun j k => ?_, fun j k x _ => by simp, fun j x _ => rfl⟩
    exact analyticOnNhd_const
  smul_mem' := by
    rintro c f ⟨hf, hc, hz⟩
    refine ⟨fun j k => analyticOnNhd_const.mul (hf j k), fun j k x hx => ?_, fun j x hx => ?_⟩
    · simp only [Pi.smul_apply, smul_eq_mul, hc j k x hx]; ring
    · simp [hz j x hx]

end HolLineBundle

structure Weight {A : FinHolAtlas D X} (L : HolLineBundle A) where

  φ : Fin A.n → X → ℝ
  smooth : ∀ j, A.SmoothOn (A.chart j).source (φ j)
  compat : ∀ j k, ∀ x ∈ (A.chart j).source ∩ (A.chart k).source,
    φ j x = φ k x + Real.log (‖L.g j k x‖ ^ 2)

namespace Weight

variable {A : FinHolAtlas D X} {L : HolLineBundle A}

def IsSemipositive (W : Weight L) : Prop :=
  ∀ j, ∀ y ∈ (A.chart j).target, ∀ w : Fin D → ℂ, 0 ≤ levi (W.φ j ∘ (A.chart j).symm) y w

def lerp (W₀ W₁ : Weight L) (t : ℝ) : Weight L where
  φ j x := W₀.φ j x + t * (W₁.φ j x - W₀.φ j x)
  smooth j k := (W₀.smooth j k).add (contDiffOn_const.mul ((W₁.smooth j k).sub (W₀.smooth j k)))
  compat j k x hx := by rw [W₀.compat j k x hx, W₁.compat j k x hx]; ring

def diff (W₁ W₀ : Weight L) (x : X) : ℝ :=
  W₁.φ (chartIdx A x) x - W₀.φ (chartIdx A x) x

theorem diff_eq (W₁ W₀ : Weight L) (j : Fin A.n) {x : X} (hx : x ∈ (A.chart j).source) :
    diff W₁ W₀ x = W₁.φ j x - W₀.φ j x := by
  have hi : x ∈ (A.chart (chartIdx A x)).source := Classical.choose_spec (A.cover x)
  rw [diff, W₁.compat (chartIdx A x) j x ⟨hi, hx⟩, W₀.compat (chartIdx A x) j x ⟨hi, hx⟩]
  ring

end Weight

structure SmoothVolume [MeasurableSpace X] (A : FinHolAtlas D X) where

  μ : Measure X
  isProb : IsProbabilityMeasure μ

  dens : Fin A.n → (Fin D → ℂ) → ℝ
  smooth : ∀ j, ContDiffOn ℝ ∞ (dens j) (A.chart j).target
  pos : ∀ j, ∀ y ∈ (A.chart j).target, 0 < dens j y
  chart_lintegral : ∀ j (g : X → ℝ≥0∞), Measurable g →
    ∫⁻ x in (A.chart j).source, g x ∂μ =
      ∫⁻ y in (A.chart j).target, g ((A.chart j).symm y) * ENNReal.ofReal (dens j y)

variable {A : FinHolAtlas D X} {L : HolLineBundle A}

def ptNormSq (W : Weight L) (n : ℕ) (s : Fin A.n → X → ℂ) (x : X) : ℝ :=
  ‖s (chartIdx A x) x‖ ^ 2 * Real.exp (-(n : ℝ) * W.φ (chartIdx A x) x)

variable [MeasurableSpace X]

def sectionL2NormSq (W : Weight L) (dV : SmoothVolume A) (n : ℕ) (s : Fin A.n → X → ℂ) : ℝ :=
  ∫ x, ptNormSq W n s x ∂dV.μ

def bergman (W : Weight L) (dV : SmoothVolume A) (V : Submodule ℂ (Fin A.n → X → ℂ)) (n : ℕ)
    (x : X) : ℝ :=
  ⨆ s : V, ptNormSq W n (s : Fin A.n → X → ℂ) x / sectionL2NormSq W dV n s

def chernTopDens (W : Weight L) (j : Fin A.n) (y : Fin D → ℂ) : ℝ :=
  (D.factorial : ℝ) * ((((1 / Real.pi : ℝ) : ℂ) • hessC (W.φ j ∘ (A.chart j).symm) y).det).re

def bergmanDens (W : Weight L) (dV : SmoothVolume A) (x : X) : ℝ :=
  chernTopDens W (chartIdx A x) (A.chart (chartIdx A x) x) /
    ((D.factorial : ℝ) * dV.dens (chartIdx A x) (A.chart (chartIdx A x) x))

def gram (W : Weight L) (dV : SmoothVolume A) (n : ℕ) {ι : Type*} (e : ι → Fin A.n → X → ℂ) :
    Matrix ι ι ℂ :=
  Matrix.of fun a b => ∫ x, e a (chartIdx A x) x * conj (e b (chartIdx A x) x) *
    ((Real.exp (-(n : ℝ) * W.φ (chartIdx A x) x) : ℝ) : ℂ) ∂dV.μ

def chiGram (W : Weight L) (dV : SmoothVolume A) (n : ℕ) {ι : Type*} [Fintype ι] [DecidableEq ι]
    (e : ι → Fin A.n → X → ℂ) : ℝ :=
  -(1 / 2) * Real.log (gram W dV n e).det.re

end

noncomputable def gaussDiscMass (lam R : ℝ) : ℝ :=
  if lam = 0 then Real.pi * R ^ 2 else Real.pi * (1 - Real.exp (-lam * R ^ 2)) / lam

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.GenericComplexPoint
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo Cardinal

noncomputable section

theorem exists_ringHom_complex_of_charZero (F : Type) [Field F] [CharZero F] (hF : #F ≤ 𝔠) :
    Nonempty (F →+* ℂ) := by
  let M := MvPolynomial ℂ F
  let E := FractionRing M
  let L := AlgebraicClosure E
  have : CharZero M := charZero_of_injective_algebraMap (R := F) (MvPolynomial.C_injective _ _)
  have : CharZero E := charZero_of_injective_algebraMap (R := M) (IsFractionRing.injective M E)
  have : CharZero L := charZero_of_injective_algebraMap (R := E) (algebraMap E L).injective
  have hM : #M ≤ 𝔠 := by
    refine MvPolynomial.cardinalMk_le_max.trans ?_
    rw [mk_complex]
    exact max_le (max_le hF le_rfl) aleph0_le_continuum
  have hE : #E = #M := Cardinal.mk_fractionRing M
  have hL : #L ≤ 𝔠 :=
    (Algebra.IsAlgebraic.cardinalMk_le_max E L).trans (max_le (hE ▸ hM) aleph0_le_continuum)
  have hinj : Function.Injective (fun c : ℂ => algebraMap E L (algebraMap M E (X c))) :=
    (algebraMap E L).injective.comp ((IsFractionRing.injective M E).comp MvPolynomial.X_injective)
  have hLc : #L = #ℂ :=
    le_antisymm (hL.trans_eq mk_complex.symm) (Cardinal.mk_le_of_injective hinj)
  obtain ⟨σ⟩ := IsAlgClosed.ringEquiv_of_equiv_of_charZero (K := L) (L := ℂ)
    (by rw [hLc, mk_complex]; exact aleph0_lt_continuum) (Cardinal.eq.1 hLc)
  exact ⟨σ.toRingHom.comp ((algebraMap E L).comp ((algebraMap M E).comp C))⟩

theorem exists_mcPts_not_mem_mcPts {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]
    {P J : Ideal (MRing ι)} {d : ℕ} (hP : IsArithVar P d) (hJ : ¬ J ≤ P) :
    ∃ z, z ∈ mcPts P ∧ z ∉ mcPts J := by
  obtain ⟨_, ⟨hprime, -, hrel⟩, hhor, -⟩ := hP
  obtain ⟨g, hgJ, hgP⟩ := SetLike.not_le_iff_exists.mp hJ
  have := hprime
  let Q := MRing ι ⧸ P
  let F := FractionRing Q
  have hQ : Function.Injective (algebraMap ℤ Q) := by
    have e : algebraMap ℤ Q = (Ideal.Quotient.mk P).comp C := RingHom.ext_int _ _
    rw [e, injective_iff_map_eq_zero]
    intro n hn
    have hn0 : (C n : MRing ι) ∈ P := Ideal.Quotient.eq_zero_iff_mem.mp hn
    have hn' : n ∈ P.comap (C : ℤ →+* MRing ι) := hn0
    rw [IsHorizontal] at hhor
    rw [hhor] at hn'
    exact (Ideal.mem_bot).mp hn'
  have : CharZero Q := charZero_of_injective_algebraMap hQ
  have : CharZero F := charZero_of_injective_algebraMap (R := Q) (IsFractionRing.injective Q F)
  have hcard : #F ≤ 𝔠 := by
    rw [Cardinal.mk_fractionRing]
    refine (Cardinal.mk_le_of_surjective (Ideal.Quotient.mk_surjective (I := P))).trans ?_
    refine MvPolynomial.cardinalMk_le_max.trans ?_
    exact max_le (max_le (mk_int.le.trans aleph0_le_continuum)
      (Cardinal.mk_le_aleph0.trans aleph0_le_continuum)) aleph0_le_continuum
  obtain ⟨ψ⟩ := exists_ringHom_complex_of_charZero F hcard
  let φ : MRing ι →+* ℂ := (ψ.comp (algebraMap Q F)).comp (Ideal.Quotient.mk P)
  have hker : ∀ f, φ f = 0 ↔ f ∈ P := by
    intro f
    have hi : Function.Injective (ψ.comp (algebraMap Q F)) :=
      ψ.injective.comp (IsFractionRing.injective Q F)
    rw [show φ f = (ψ.comp (algebraMap Q F)) (Ideal.Quotient.mk P f) from rfl,
      map_eq_zero_iff _ hi, Ideal.Quotient.eq_zero_iff_mem]
  let z : (Σ k, ι k) → ℂ := fun p => φ (X p)
  have hev : ∀ f : MRing ι, eval z (map (Int.castRingHom ℂ) f) = φ f := by
    intro f
    have h : (eval z).comp (map (Int.castRingHom ℂ)) = φ := by
      refine MvPolynomial.ringHom_ext (fun r => ?_) (fun i => ?_)
      · exact RingHom.congr_fun
          (RingHom.ext_int (((eval z).comp (map (Int.castRingHom ℂ))).comp C) (φ.comp C)) r
      · simp [z]
    exact RingHom.congr_fun h f
  refine ⟨z, ⟨fun k => ?_, fun f hf => ?_⟩, fun hz => ?_⟩
  · obtain ⟨i, hi⟩ := hrel k
    exact ⟨i, fun h => hi ((hker _).mp h)⟩
  · rw [hev]
    exact (hker f).mpr hf
  · exact hgP ((hker g).mp (by rw [← hev]; exact hz.2 g hgJ))

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.LengthLocalizedQuotientEqZero
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.HilbertSamuel

open MvPolynomial GroundTheory.Heights₂.Heights.NumbersDVR

noncomputable section

universe u

section Length

variable {R : Type*} [CommRing R]

theorem telescope_enat : ∀ (n : ℕ) (f : Fin (n + 1) → ℕ∞) (c : Fin n → ℕ∞),
    (∀ j : Fin n, f j.castSucc = c j + f j.succ) → f 0 = (∑ j, c j) + f (Fin.last n)
  | 0, f, c, _ => by simp
  | n + 1, f, c, h => by
    have ih : f (Fin.succ 0) = (∑ j : Fin n, c j.succ) + f (Fin.last n).succ :=
      telescope_enat n (fun k => f k.succ) (fun j => c j.succ) (fun j => h j.succ)
    have h0 : f 0 = c 0 + f (Fin.succ 0) := by
      simpa only [Fin.castSucc_zero] using h 0
    rw [h0, ih, Fin.succ_last, Fin.sum_univ_succ c, add_assoc]

theorem localizedModule_map_coe (P : Submonoid R) {M₀ M₁ : Type*} [AddCommGroup M₀] [Module R M₀]
    [AddCommGroup M₁] [Module R M₁] (f : M₀ →ₗ[R] M₁) :
    ⇑(LocalizedModule.map P f) = ⇑(IsLocalizedModule.map P (LocalizedModule.mkLinearMap P M₀)
      (LocalizedModule.mkLinearMap P M₁) f) := by
  funext y
  induction y using LocalizedModule.induction_on with
  | h m s => rw [LocalizedModule.map_mk, IsLocalizedModule.map_LocalizedModules]

theorem length_localized_eq_add (p : Ideal R) [p.IsPrime] {M₀ M₁ M₂ : Type*}
    [AddCommGroup M₀] [Module R M₀] [AddCommGroup M₁] [Module R M₁] [AddCommGroup M₂] [Module R M₂]
    (f : M₀ →ₗ[R] M₁) (g : M₁ →ₗ[R] M₂) (hf : Function.Injective f)
    (hg : Function.Surjective g) (h : Function.Exact f g) :
    Module.length (Localization.AtPrime p) (LocalizedModule p.primeCompl M₁) =
      Module.length (Localization.AtPrime p) (LocalizedModule p.primeCompl M₀) +
      Module.length (Localization.AtPrime p) (LocalizedModule p.primeCompl M₂) := by
  refine Module.length_eq_add_of_exact (LocalizedModule.map p.primeCompl f)
    (LocalizedModule.map p.primeCompl g) (LocalizedModule.map_injective _ f hf)
    (LocalizedModule.map_surjective _ g hg) ?_
  rw [localizedModule_map_coe, localizedModule_map_coe]
  exact LocalizedModule.map_exact p.primeCompl f g h

theorem length_localized_quotient_eq_zero (p q : Ideal R) [p.IsPrime] (h : ¬ q ≤ p) :
    Module.length (Localization.AtPrime p) (LocalizedModule p.primeCompl (R ⧸ q)) = 0 := by
  obtain ⟨t, htq, htp⟩ := Set.not_subset.mp h
  have key : ∀ y : LocalizedModule p.primeCompl (R ⧸ q), y = 0 := by
    intro y
    induction y using LocalizedModule.induction_on with
    | h m s =>
      obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective m
      rw [← LocalizedModule.zero_mk 1, LocalizedModule.mk_eq]
      refine ⟨⟨t, htp⟩, ?_⟩
      rw [one_smul, smul_zero, smul_zero, Submonoid.smul_def, Algebra.smul_def,
        Ideal.Quotient.algebraMap_eq, ← map_mul, Ideal.Quotient.eq_zero_iff_mem]
      exact q.mul_mem_right r htq
  have : Subsingleton (LocalizedModule p.primeCompl (R ⧸ q)) :=
    ⟨fun a b => by rw [key a, key b]⟩
  exact Module.length_eq_zero

theorem length_localized_quotient_self (p : Ideal R) [hp : p.IsPrime] :
    Module.length (Localization.AtPrime p) (LocalizedModule p.primeCompl (R ⧸ p)) = 1 := by
  rw [Module.length_eq_one_iff, isSimpleModule_iff_toSpanSingleton_surjective]
  have hne : ∀ (r : R) (s : p.primeCompl),
      LocalizedModule.mk (Ideal.Quotient.mk p r) s = 0 → r ∈ p := by
    intro r s h
    rw [← LocalizedModule.zero_mk 1, LocalizedModule.mk_eq] at h
    obtain ⟨u, hu⟩ := h
    rw [one_smul, smul_zero, smul_zero, Submonoid.smul_def, Algebra.smul_def,
      Ideal.Quotient.algebraMap_eq, ← map_mul, Ideal.Quotient.eq_zero_iff_mem] at hu
    exact (hp.mem_or_mem hu).resolve_left u.2
  refine ⟨⟨LocalizedModule.mk (Ideal.Quotient.mk p 1) 1, 0,
    fun h => hp.ne_top ((Ideal.eq_top_iff_one p).mpr (hne 1 1 h))⟩, ?_⟩
  intro x hx y
  induction x using LocalizedModule.induction_on with
  | h m s =>
  induction y using LocalizedModule.induction_on with
  | h m' t =>
  obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective m
  obtain ⟨r', rfl⟩ := Ideal.Quotient.mk_surjective m'
  have hr : r ∉ p := fun hr => hx (by
    rw [Ideal.Quotient.eq_zero_iff_mem.mpr hr, LocalizedModule.zero_mk])
  refine ⟨Localization.mk (r' * s) ⟨r * t, p.primeCompl.mul_mem hr t.2⟩, ?_⟩
  rw [LinearMap.toSpanSingleton_apply, LocalizedModule.mk_smul_mk, LocalizedModule.mk_eq]
  refine ⟨1, ?_⟩
  simp only [one_smul, Submonoid.smul_def, Submonoid.coe_mul, Algebra.smul_def,
    Ideal.Quotient.algebraMap_eq, ← map_mul]
  congr 1
  ring

theorem length_localized_step (p : Ideal R) [p.IsPrime] {M : Type*} [AddCommGroup M] [Module R M]
    (A B : Submodule R M) (x : M) (q : Ideal R) (hB : B = A ⊔ Submodule.span R {x})
    (hq : ∀ s : R, s • x ∈ A ↔ s ∈ q) :
    Module.length (Localization.AtPrime p) (LocalizedModule p.primeCompl (M ⧸ A)) =
      Module.length (Localization.AtPrime p) (LocalizedModule p.primeCompl (R ⧸ q)) +
      Module.length (Localization.AtPrime p) (LocalizedModule p.primeCompl (M ⧸ B)) := by
  have hAB : A ≤ B := hB ▸ le_sup_left
  let f : (R ⧸ q) →ₗ[R] M ⧸ A := Submodule.liftQ q (A.mkQ ∘ₗ LinearMap.toSpanSingleton R M x) (by
    intro s hs
    rw [LinearMap.mem_ker, LinearMap.comp_apply, LinearMap.toSpanSingleton_apply, Submodule.mkQ_apply,
      Submodule.Quotient.mk_eq_zero]
    exact (hq s).mpr hs)
  let g : M ⧸ A →ₗ[R] M ⧸ B := A.mapQ B LinearMap.id hAB
  have hf_mk : ∀ s : R, f (Submodule.Quotient.mk s) = Submodule.Quotient.mk (s • x) := fun s => rfl
  refine length_localized_eq_add p f g ?_ ?_ ?_
  · rw [← LinearMap.ker_eq_bot, Submodule.eq_bot_iff]
    intro y hy
    obtain ⟨s, rfl⟩ := Submodule.Quotient.mk_surjective q y
    rw [LinearMap.mem_ker, hf_mk, Submodule.Quotient.mk_eq_zero] at hy
    exact (Submodule.Quotient.mk_eq_zero q).mpr ((hq s).mp hy)
  · intro y
    obtain ⟨m, rfl⟩ := Submodule.Quotient.mk_surjective B y
    exact ⟨Submodule.Quotient.mk m, rfl⟩
  · intro y
    obtain ⟨m, rfl⟩ := Submodule.Quotient.mk_surjective A y
    simp only [g, Submodule.mapQ_apply, LinearMap.id_apply, Submodule.Quotient.mk_eq_zero, hB,
      Set.mem_range]
    rw [Submodule.mem_sup]
    constructor
    · rintro ⟨a, ha, z, hz, rfl⟩
      obtain ⟨s, rfl⟩ := Submodule.mem_span_singleton.mp hz
      refine ⟨Submodule.Quotient.mk s, ?_⟩
      rw [hf_mk, Submodule.Quotient.eq]
      simpa using A.neg_mem ha
    · rintro ⟨y, hy⟩
      obtain ⟨s, rfl⟩ := Submodule.Quotient.mk_surjective q y
      rw [hf_mk, Submodule.Quotient.eq] at hy
      refine ⟨m - s • x, ?_, s • x, Submodule.mem_span_singleton.mpr ⟨s, rfl⟩, sub_add_cancel _ _⟩
      simpa using A.neg_mem hy

theorem card_eq_length_of_filtration {M : Type*} [AddCommGroup M] [Module R M] {n : ℕ}
    (N : Fin (n + 1) → Submodule R M) (x : Fin n → M) (q : Fin n → Ideal R)
    (hN0 : N 0 = ⊥) (hNl : N (Fin.last n) = ⊤)
    (hsucc : ∀ j : Fin n, N j.succ = N j.castSucc ⊔ Submodule.span R {x j})
    (hprime : ∀ j, (q j).IsPrime) (hann : ∀ j (s : R), s • x j ∈ N j.castSucc ↔ s ∈ q j)
    (W : Ideal R) (hW : W ∈ (Module.annihilator R M).minimalPrimes) [W.IsPrime]
    [DecidablePred fun j => q j = W] :
    (((Finset.univ.filter fun j => q j = W).card : ℕ) : ℕ∞) =
      Module.length (Localization.AtPrime W) (LocalizedModule W.primeCompl M) := by
  let L : Fin (n + 1) → ℕ∞ := fun k =>
    Module.length (Localization.AtPrime W) (LocalizedModule W.primeCompl (M ⧸ N k))
  have hstep : ∀ j : Fin n, L j.castSucc = (if q j = W then 1 else 0) + L j.succ := by
    intro j
    simp only [L]
    rw [length_localized_step W (N j.castSucc) (N j.succ) (x j) (q j) (hsucc j) (hann j)]
    congr 1
    split_ifs with h
    · rw [h]
      exact length_localized_quotient_self W
    · apply length_localized_quotient_eq_zero
      intro hle
      apply h
      have hannq : Module.annihilator R M ≤ q j := by
        intro s hs
        rw [← hann j, Module.mem_annihilator.mp hs (x j)]
        exact zero_mem _
      exact le_antisymm hle (hW.2 ⟨hprime j, hannq⟩ hle)
  have h0 : L 0 = Module.length (Localization.AtPrime W) (LocalizedModule W.primeCompl M) := by
    simp only [L]
    rw [hN0]
    exact (IsLocalizedModule.mapEquiv W.primeCompl (LocalizedModule.mkLinearMap W.primeCompl _)
      (LocalizedModule.mkLinearMap W.primeCompl M) (Localization.AtPrime W)
      (Submodule.quotEquivOfEqBot ⊥ rfl)).length_eq
  have hl : L (Fin.last n) = 0 := by
    simp only [L]
    rw [hNl]
    have key : ∀ y : LocalizedModule W.primeCompl (M ⧸ (⊤ : Submodule R M)), y = 0 := by
      intro y
      induction y using LocalizedModule.induction_on with
      | h m s =>
        obtain ⟨m, rfl⟩ := Submodule.Quotient.mk_surjective _ m
        rw [(Submodule.Quotient.mk_eq_zero _).mpr Submodule.mem_top, LocalizedModule.zero_mk]
    have : Subsingleton (LocalizedModule W.primeCompl (M ⧸ (⊤ : Submodule R M))) :=
      ⟨fun a b => by rw [key a, key b]⟩
    exact Module.length_eq_zero
  rw [← h0, telescope_enat n L _ hstep, hl, add_zero, Finset.sum_boole]

end Length

section Spans

end Spans

end

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.HilbertSamuel
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PLeviCompHol
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open ReciprocityTheory.ChartRestriction.G.Geo Filter Topology

noncomputable section

theorem LeviCompHol.proof : LeviCompHol.Statement := by
  intro E F _ _ g φ x w hg hφ
  have hgev : ∀ᶠ y in 𝓝 x, AnalyticAt ℂ g y := hg.eventually_analyticAt
  have hfdg : ∀ᶠ y in 𝓝 x, fderiv ℝ g y = (fderiv ℂ g y).restrictScalars ℝ := by
    filter_upwards [hgev] with y hy
    exact hy.differentiableAt.fderiv_restrictScalars ℝ
  have hgC : ContDiffAt ℂ 2 g x := hg.contDiffAt
  have hgR : ContDiffAt ℝ 2 g x := hgC.restrict_scalars ℝ
  have hgd : DifferentiableAt ℝ g x := hgR.differentiableAt (by norm_num)
  have hd2 : DifferentiableAt ℝ (fderiv ℝ g) x :=
    (hgR.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)
  have hGw : ∀ v, fderiv ℝ g x v = fderiv ℂ g x v := fun v => by rw [hfdg.self_of_nhds]; rfl
  have hGI : ∀ v, fderiv ℝ g x (Complex.I • v) = Complex.I • fderiv ℝ g x v := fun v => by
    rw [hGw, hGw]; exact (fderiv ℂ g x).map_smul _ _

  have hG2I : ∀ u v, fderiv ℝ (fderiv ℝ g) x u (Complex.I • v) =
      Complex.I • fderiv ℝ (fderiv ℝ g) x u v := by
    intro u v
    have hA : HasFDerivAt (fun y => fderiv ℝ g y (Complex.I • v))
        ((ContinuousLinearMap.apply ℝ (F → ℂ) (Complex.I • v)).comp (fderiv ℝ (fderiv ℝ g) x)) x :=
      (ContinuousLinearMap.apply ℝ (F → ℂ) (Complex.I • v)).hasFDerivAt.comp x hd2.hasFDerivAt
    have hB : HasFDerivAt (fun y => Complex.I • fderiv ℝ g y v)
        (Complex.I • (ContinuousLinearMap.apply ℝ (F → ℂ) v).comp (fderiv ℝ (fderiv ℝ g) x)) x :=
      ((ContinuousLinearMap.apply ℝ (F → ℂ) v).hasFDerivAt.comp x hd2.hasFDerivAt).const_smul Complex.I
    have hAB : (fun y => Complex.I • fderiv ℝ g y v) =ᶠ[𝓝 x] fun y => fderiv ℝ g y (Complex.I • v) := by
      filter_upwards [hfdg] with y hy
      rw [hy]; exact ((fderiv ℂ g y).map_smul _ _).symm
    have h := congrArg (fun L => L u) ((hB.congr_of_eventuallyEq hAB.symm).unique hA)
    simpa using h.symm
  have hsymm : IsSymmSndFDerivAt ℝ g x := hgR.isSymmSndFDerivAt (by simp)
  have hG2II : fderiv ℝ (fderiv ℝ g) x (Complex.I • w) (Complex.I • w) =
      -fderiv ℝ (fderiv ℝ g) x w w := by
    rw [hG2I, hsymm (Complex.I • w) w, hG2I, smul_smul, Complex.I_mul_I, neg_one_smul]
  have hev : ∀ᶠ y in 𝓝 x, ContDiffAt ℝ 2 φ (g y) :=
    hgd.continuousAt.tendsto.eventually (hφ.eventually (by simp))
  have hfd : fderiv ℝ (fun y => φ (g y)) =ᶠ[𝓝 x]
      fun y => (fderiv ℝ φ (g y)).comp (fderiv ℝ g y) := by
    filter_upwards [hev, hgev] with y hy hy'
    exact fderiv_comp y (hy.differentiableAt (by norm_num)) (hy'.differentiableAt.restrictScalars ℝ)
  have hdφ : DifferentiableAt ℝ (fderiv ℝ φ) (g x) :=
    (hφ.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)
  have hc : HasFDerivAt (fun y => fderiv ℝ φ (g y))
      ((fderiv ℝ (fderiv ℝ φ) (g x)).comp (fderiv ℝ g x)) x :=
    hdφ.hasFDerivAt.comp x hgd.hasFDerivAt
  have hD := hc.clm_comp hd2.hasFDerivAt
  unfold leviForm
  rw [hfd.fderiv_eq, hD.fderiv]
  simp only [add_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.compL_apply, ContinuousLinearMap.flip_apply, hGI, hG2II, map_neg, hGw]
  ring

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

