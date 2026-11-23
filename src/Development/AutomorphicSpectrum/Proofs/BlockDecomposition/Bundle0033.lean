module

public import Mathlib
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.HodgeSurjectivity.FormLaws
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0011
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.WittExactSequences.Bundle0001
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.Bundle0001
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0012
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0013
public import Development.WeilBound.RepresentationTheoryGL.EisensteinSeries.SiegelEisensteinContinuation.StripEntire
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.DiscreteSeriesTopClasses.IsInvOne
public import Development.WeilBound.RepresentationTheoryGL.StandardBasisDerivatives.ArchimedeanBasisDerivatives.StBasDeriv

@[expose] public section

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FormConsEqSmul
section
open CrystallineSemistableComparison.Onto

set_option autoImplicit false

namespace GlobalTheory.CompanionTheory.OntoDLog

variable {K A : Type} [CommRing K] [CommRing A] [Algebra K A]

theorem form_mul_left {a : ℕ} (c g₀ : A) (g : Fin a → A) :
    form K (c * g₀) g = c • form K g₀ g := by
  simp only [form, mul_smul]

theorem form_cons_mem {a : ℕ} (f h : A) (g : Fin a → A) :
    form K h (Fin.cons f g : Fin (a + 1) → A) ∈ relOm K (Ideal.span {f}) (a + 1) := by
  apply Submodule.subset_span
  exact ⟨h, Fin.cons f g, Or.inr ⟨0, by rw [Fin.cons_zero]; exact Ideal.mem_span_singleton_self f⟩, rfl⟩

theorem form_cons_eq_smul {a : ℕ} (f h g₀ : A) (g : Fin a → A) (k : Fin a)
    (hk : g k = f * h) :
    form K g₀ (Fin.cons f g : Fin (a + 1) → A) =
      f • form K g₀ (Fin.cons f (Function.update g k h) : Fin (a + 1) → A) := by
  set v : Fin (a + 1) → Ω[A⁄K] := fun i =>
    KaehlerDifferential.D K A ((Fin.cons f (Function.update g k h) : Fin (a + 1) → A) i) with hv
  have hcons : (fun i => KaehlerDifferential.D K A ((Fin.cons f g : Fin (a + 1) → A) i)) =
      Function.update v k.succ (f • KaehlerDifferential.D K A h + h • KaehlerDifferential.D K A f) := by
    funext i
    induction i using Fin.cases with
    | zero => simp [v, Function.update_apply, (Fin.succ_ne_zero k).symm]
    | succ j =>
      by_cases hj : j = k
      · subst hj
        simp [hk, Derivation.leibniz]
      · simp [v, hj, Function.update_apply]
  have hv1 : Function.update v k.succ (KaehlerDifferential.D K A h) = v := by
    funext i
    by_cases hi : i = k.succ
    · subst hi
      simp [v]
    · simp [Function.update_apply, hi]
  have hv2 : exteriorPower.ιMulti A (a + 1) (Function.update v k.succ (KaehlerDifferential.D K A f)) = 0 := by
    apply AlternatingMap.map_eq_zero_of_eq _ _ (i := 0) (j := k.succ)
    · simp [v, Function.update_apply, (Fin.succ_ne_zero k).symm]
    · exact (Fin.succ_ne_zero k).symm
  simp only [form]
  rw [hcons, AlternatingMap.map_update_add, AlternatingMap.map_update_smul,
    AlternatingMap.map_update_smul, hv1, hv2, smul_zero, add_zero, smul_comm]

theorem dLog : DLog := by
  unfold DLog
  intro K A _ _ _ a f hf w hw ω hω
  have hex : ∀ ω ∈ relOm K (Ideal.span {f}) a,
      ∃ η ∈ relOm K (Ideal.span {f}) (a + 1), f • η = w ω := by
    intro ω hω
    induction hω using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨g₀, g, hg, rfl⟩ := hx
      rcases hg with hg₀ | ⟨k, hk⟩
      · obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton.mp hg₀
        refine ⟨form K c (Fin.cons f g), form_cons_mem f c g, ?_⟩
        rw [hw, ← form_mul_left]
      · obtain ⟨c, hc⟩ := Ideal.mem_span_singleton.mp hk
        refine ⟨form K g₀ (Fin.cons f (Function.update g k c)), form_cons_mem f g₀ _, ?_⟩
        rw [hw, form_cons_eq_smul f c g₀ g k hc]
    | zero => exact ⟨0, Submodule.zero_mem _, by simp⟩
    | add x y _ _ hx hy =>
      obtain ⟨η₁, h₁, e₁⟩ := hx
      obtain ⟨η₂, h₂, e₂⟩ := hy
      exact ⟨η₁ + η₂, Submodule.add_mem _ h₁ h₂, by rw [smul_add, e₁, e₂, map_add (f := _)]⟩
    | smul c x _ hx =>
      obtain ⟨η, h₁, e₁⟩ := hx
      exact ⟨c • η, Submodule.smul_mem _ c h₁, by rw [smul_comm, e₁, map_smul]⟩
  obtain ⟨η, hη, e⟩ := hex ω hω
  refine ⟨η, ⟨hη, e⟩, ?_⟩
  rintro η' ⟨_, e'⟩
  have hz : f • (η' - η) = 0 := by rw [smul_sub, e, e', sub_self]
  exact sub_eq_zero.mp (hf _ hz)

end GlobalTheory.CompanionTheory.OntoDLog
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FourierParameterDerivativeStatement
section
open MeasureTheory

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.fourier_parameter_derivative : ∀ (X : Type) [MeasurableSpace X] (μ : Measure X) (g : X → ℂ) (M : X → ℝ), Measurable M → Integrable g μ → Integrable (fun y => (M y : ℂ) * g y) μ → ∀ s : ℝ, HasDerivAt (fun t : ℝ => ∫ y, g y * Complex.exp (2 * Real.pi * Complex.I * ((t * M y : ℝ) : ℂ)) ∂μ) (2 * Real.pi * Complex.I * ∫ y, (M y : ℂ) * g y * Complex.exp (2 * Real.pi * Complex.I * ((s * M y : ℝ) : ℂ)) ∂μ) s := by
  first | exact @GlobalTheory.CompanionTheory.Analysis.OscPhase.hasDerivAt_integral_oscillating_phase | exact GlobalTheory.CompanionTheory.Analysis.OscPhase.hasDerivAt_integral_oscillating_phase | (intros; apply GlobalTheory.CompanionTheory.Analysis.OscPhase.hasDerivAt_integral_oscillating_phase <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FrobeniusPowerSolutionLift
section
open TensorProduct CrystallineSemistableComparison.D
open scoped LaurentPolynomial

namespace GlobalTheory.CompanionTheory.PerfectQuotient

theorem exists_frobenius_iterate (p : ℕ) [Fact p.Prime] (R : Type) [CommRing R]
    (h : (p : R) = 0) (k : ℕ) : ∃ f : R →+* R, ∀ x, f x = x ^ p ^ k := by
  rcases subsingleton_or_nontrivial R with hs | hn
  · exact ⟨RingHom.id R, fun x => Subsingleton.elim _ _⟩
  · haveI : CharP R p := (CharP.charP_iff_prime_eq_zero (Fact.out : p.Prime)).2 h
    exact ⟨iterateFrobenius R p k, fun x => iterateFrobenius_def p k x⟩

theorem solv_pow : ∀ (p : ℕ) [Fact p.Prime] (A : Type) [CommRing A](S : Type) [CommRing S] [Algebra A S] (B : Type) [CommRing B] [Algebra A B] (i : S →ₐ[A] B) (I : Ideal S) (m n : ℕ) (a : Fin m → Fin n → A) (c : Fin m → A), (p : A) = 0 → PQ p (i : S →+* B) I → Solv B a c → ∃ (k : ℕ) (s : Fin n → S), ∀ t, ∑ j, a t j ^ p ^ k • s j - algebraMap A S (c t ^ p ^ k) ∈ I := by
  intro p _ A _ S _ _ B _ _ i I m n a c hp hPQ hS
  obtain ⟨y, hy⟩ := hS
  have hpS : (p : S) = 0 := by
    have := congrArg (algebraMap A S) hp
    simpa using this
  choose k₀ x hx using fun j => hPQ.pow (y j)
  obtain ⟨K, hK⟩ : ∃ K, K = Finset.univ.sup k₀ := ⟨_, rfl⟩
  let s : Fin n → S := fun j => x j ^ p ^ (K - k₀ j)
  have hs : ∀ j, y j ^ p ^ K = i (s j) := by
    intro j
    have hle : k₀ j ≤ K := hK ▸ Finset.le_sup (Finset.mem_univ j)
    have hpow : p ^ K = p ^ k₀ j * p ^ (K - k₀ j) := by
      rw [← pow_add]; congr 1; omega
    have hxj : y j ^ p ^ k₀ j = i (x j) := hx j
    rw [hpow, pow_mul, hxj]
    simp [s, map_pow]
  obtain ⟨fB, hfB⟩ := exists_frobenius_iterate p B hPQ.pf.char K
  have he : ∀ t, i (∑ j, a t j ^ p ^ K • s j - algebraMap A S (c t ^ p ^ K)) = 0 := by
    intro t
    have h1 := congrArg fB (hy t)
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum] at h1
    have h2 : ∀ j, fB (a t j • y j) = a t j ^ p ^ K • i (s j) := by
      intro j
      rw [hfB, smul_pow, hs]
    simp only [h2] at h1
    rw [hfB, ← map_pow] at h1
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sub, map_sum, AlgHom.commutes, sub_eq_zero, ← h1]
    exact Finset.sum_congr rfl fun j _ => map_smul i _ _
  choose k₁ hk₁ using fun t => (hPQ.ker _).1 (he t)
  obtain ⟨L, hL⟩ : ∃ L, L = Finset.univ.sup k₁ := ⟨_, rfl⟩
  obtain ⟨fS, hfS⟩ := exists_frobenius_iterate p S hpS L
  refine ⟨K + L, fun j => s j ^ p ^ L, fun t => ?_⟩
  have hle : k₁ t ≤ L := hL ▸ Finset.le_sup (Finset.mem_univ t)
  have hpow : p ^ L = p ^ k₁ t * p ^ (L - k₁ t) := by
    rw [← pow_add]; congr 1; omega
  have hmem : (∑ j, a t j ^ p ^ K • s j - algebraMap A S (c t ^ p ^ K)) ^ p ^ L ∈ I := by
    rw [hpow, pow_mul]
    exact I.pow_mem_of_mem (hk₁ t) _ (pow_pos (Fact.out : p.Prime).pos _)
  set_option synthInstance.maxHeartbeats 100000 in
    rw [← hfS, map_sub, map_sum] at hmem
  have h3 : ∀ j, fS (a t j ^ p ^ K • s j) = a t j ^ p ^ (K + L) • s j ^ p ^ L := by
    intro j
    rw [hfS, smul_pow, ← pow_mul, ← pow_add]
  simp only [h3] at hmem
  rw [hfS, ← map_pow, ← pow_mul, ← pow_add] at hmem
  exact hmem

end GlobalTheory.CompanionTheory.PerfectQuotient
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FundamentalDomainFibrationVolume
section
open MeasureTheory Topology
open scoped ENNReal NNReal Matrix

namespace GlobalTheory.CompanionTheory.SW.PeriodisedMean

theorem setLIntegral_tsum_comp_inv_eq : ∀ (N : Type) [Group N] [TopologicalSpace N] [IsTopologicalGroup N] [LocallyCompactSpace N] [SecondCountableTopology N] [T2Space N] [MeasurableSpace N] [BorelSpace N] (ν : Measure N) [ν.IsHaarMeasure] (Γ : Subgroup N) [Countable Γ] (𝓕N : Set N), IsFundamentalDomain Γ 𝓕N ν → ν 𝓕N < ⊤ → ∀ (V : Type) [AddCommGroup V] [TopologicalSpace V] [IsTopologicalAddGroup V] [LocallyCompactSpace V] [SecondCountableTopology V] [T2Space V] [MeasurableSpace V] [BorelSpace V] (dA : Measure V) [dA.IsAddHaarMeasure] (Λ : AddSubgroup V) [Countable Λ] (D : Set V), IsAddFundamentalDomain Λ D dA → dA D = 1 → ∀ l : N → V, Continuous l → (∀ x y, l (x * y) = l x + l y) → Function.Surjective l → (∀ γ ∈ Γ, l γ ∈ Λ) → ∀ f : V → ℝ≥0∞, Measurable f → ∫⁻ m in 𝓕N, ∑' a : Λ, f ((a : V) + l m⁻¹) ∂ν = ν 𝓕N * ∫⁻ x, f x ∂dA := by
  intro N _ _ _ _ _ _ _ _ ν _ Γ _ 𝓕N h𝓕 hfin V _ _ _ _ _ _ _ _ dA _ Λ _ D hD hD1 l hlc hlmul hlsurj hlΓ f hf
  obtain ⟨-, hR, -⟩ :=
    GlobalTheory.CompanionTheory.SW.LatticeUnimod.unimodular_of_isFundamentalDomain N Γ ν 𝓕N h𝓕 hfin
  have hlm : Measurable l := hlc.measurable

  set Ft : V → ℝ≥0∞ := fun x => ∑' a : Λ, f ((a : V) + x) with hFt
  have hFtm : Measurable Ft :=
    Measurable.tsum fun a => hf.comp (measurable_const.add measurable_id)
  have hper : ∀ b ∈ Λ, ∀ x, Ft (x + b) = Ft x := by
    intro b hb x
    simp only [hFt]
    rw [← (Equiv.addRight (⟨b, hb⟩ : Λ)).tsum_eq (fun a : Λ => f ((a : V) + x))]
    refine tsum_congr fun a => ?_
    simp only [Equiv.coe_addRight, AddSubgroup.coe_add]
    congr 1
    abel
  set h : N → ℝ≥0∞ := fun m => Ft (l m⁻¹) with hh
  have hinv : ∀ γ ∈ Γ, ∀ m, h (γ * m) = h m := by
    intro γ hγ m
    simp only [hh]
    rw [mul_inv_rev, hlmul]
    exact hper _ (hlΓ _ (Γ.inv_mem hγ)) _

  have hshift : ∀ n₀ : N, ∫⁻ m in 𝓕N, h (m * n₀) ∂ν = ∫⁻ m in 𝓕N, h m ∂ν := by
    intro n₀
    have hF : IsFundamentalDomain Γ ((· * n₀⁻¹) ⁻¹' 𝓕N) ν :=
      h𝓕.preimage_of_equiv (quasiMeasurePreserving_mul_right ν n₀⁻¹) (e := id)
        Function.bijective_id (fun γ x => by simp [Subgroup.smul_def, smul_eq_mul, mul_assoc])
    have hmp : MeasurePreserving (· * n₀) ν ν := measurePreserving_mul_right ν n₀
    have hemb : MeasurableEmbedding (· * n₀ : N → N) :=
      (MeasurableEquiv.mulRight n₀).measurableEmbedding
    have e1 := hmp.setLIntegral_comp_preimage_emb hemb h ((· * n₀⁻¹) ⁻¹' 𝓕N)
    have e2 : (· * n₀ : N → N) ⁻¹' ((· * n₀⁻¹) ⁻¹' 𝓕N) = 𝓕N := by
      ext x; simp
    rw [e2] at e1
    rw [e1]
    exact hF.setLIntegral_eq h𝓕 h (fun γ x => hinv γ γ.2 x)

  have hT : ∀ x, ∫⁻ m in 𝓕N, Ft (x + l m⁻¹) ∂ν = ∫⁻ m in 𝓕N, h m ∂ν := by
    intro x
    obtain ⟨y, rfl⟩ := hlsurj x
    rw [← hshift y⁻¹]
    refine lintegral_congr fun m => ?_
    simp only [hh]
    rw [mul_inv_rev, inv_inv, hlmul]

  have hfold : ∀ c : V, ∫⁻ x in D, Ft (x + c) ∂dA = ∫⁻ x, f x ∂dA := by
    intro c
    have e0 : ∫⁻ x, f (x + c) ∂dA = ∫⁻ x, f x ∂dA := lintegral_add_right_eq_self f c
    have e3 : ∫⁻ x in D, ∑' a : Λ, f ((a +ᵥ x) + c) ∂dA
        = ∑' a : Λ, ∫⁻ x in D, f ((a +ᵥ x) + c) ∂dA :=
      lintegral_tsum fun a => (hf.comp ((measurable_const_vadd a).add_const c)).aemeasurable
    rw [← e0, hD.lintegral_eq_tsum'' (fun x => f (x + c)), ← e3]
    refine lintegral_congr fun x => ?_
    simp only [hFt]
    refine tsum_congr fun a => ?_
    simp [AddSubgroup.vadd_def, vadd_eq_add, add_assoc]
  have hswapm : Measurable (Function.uncurry fun (x : V) (m : N) => Ft (x + l m⁻¹)) :=
    hFtm.comp (measurable_fst.add (hlm.comp measurable_snd.inv))
  calc ∫⁻ m in 𝓕N, ∑' a : Λ, f ((a : V) + l m⁻¹) ∂ν
      = ∫⁻ m in 𝓕N, h m ∂ν := rfl
    _ = ∫⁻ _x in D, (∫⁻ m in 𝓕N, h m ∂ν) ∂dA := by
        rw [setLIntegral_const, hD1, mul_one]
    _ = ∫⁻ x in D, ∫⁻ m in 𝓕N, Ft (x + l m⁻¹) ∂ν ∂dA :=
        lintegral_congr fun x => (hT x).symm
    _ = ∫⁻ m in 𝓕N, ∫⁻ x in D, Ft (x + l m⁻¹) ∂dA ∂ν :=
        lintegral_lintegral_swap hswapm.aemeasurable
    _ = ∫⁻ _m in 𝓕N, (∫⁻ x, f x ∂dA) ∂ν := lintegral_congr fun m => hfold _
    _ = ν 𝓕N * ∫⁻ x, f x ∂dA := by
        rw [setLIntegral_const, mul_comm]

end GlobalTheory.CompanionTheory.SW.PeriodisedMean
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FundamentalDomainIntegralCountBoundStatement
section
open MeasureTheory Topology
open scoped ENNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.fundamental_domain_integral_count_bound : ∀ {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [SecondCountableTopology G]
    [MeasurableSpace G] [BorelSpace G] (Γ : Subgroup G) [Countable Γ] (μ : Measure G) [μ.IsMulLeftInvariant]
    (𝓕 : Set G), IsFundamentalDomain Γ 𝓕 μ → ∀ (M : Set G), MeasurableSet M → ∀ (f : G → ℝ≥0∞), Measurable f →
    (∀ γ ∈ Γ, ∀ x, f (γ * x) = f x) → ∀ n : ℕ, (∀ x, Set.encard {γ : Γ | (γ : G) * x ∈ M} ≤ n) →
    ∫⁻ x in M, f x ∂μ ≤ n * ∫⁻ x in 𝓕, f x ∂μ := by
  first | exact @GlobalTheory.CompanionTheory.Growth.lintegral_le_mul_of_encard_le | exact GlobalTheory.CompanionTheory.Growth.lintegral_le_mul_of_encard_le | (intros; apply GlobalTheory.CompanionTheory.Growth.lintegral_le_mul_of_encard_le <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.GUEqOneAdd
section
open MeasureTheory Topology Filter GlobalTheory.CompanionTheory.NullFr
open scoped NNReal ENNReal Matrix

namespace GlobalTheory.CompanionTheory.NullFr

theorem gU_eq_one_add {A : Type} [CommRing A] {t : ℕ} (i : Fin t) (c₀ : Fin t → A) :
    gU i c₀ = 1 + Matrix.replicateCol Unit c₀ * Matrix.replicateRow Unit (Pi.single i (1 : A) : Fin t → A) := by
  unfold gU
  congr 1
  ext k j
  simp [Matrix.mul_apply, Pi.single_apply]

theorem det_gU {A : Type} [CommRing A] {t : ℕ} (i : Fin t) (c₀ : Fin t → A) (h : c₀ i = 0) :
    (gU i c₀).det = 1 := by
  rw [gU_eq_one_add, Matrix.det_one_add_replicateCol_mul_replicateRow]
  simp [h]

theorem exists_GL_gU : ∀ {A : Type} [CommRing A] {t : ℕ} (i : Fin t) (c₀ : Fin t → A) (_ : c₀ i = 0),
    ∃ g : GL (Fin t) A, g.1 = gU i c₀ ∧ Matrix.GeneralLinearGroup.det g = 1 := by
  intro A _ t i c₀ h
  refine ⟨Matrix.GeneralLinearGroup.mk'' (GlobalTheory.CompanionTheory.NullFr.gU i c₀)
    (by rw [GlobalTheory.CompanionTheory.NullFr.det_gU i c₀ h]; exact isUnit_one), rfl, ?_⟩
  ext
  rw [Matrix.GeneralLinearGroup.val_det_apply, Units.val_one]
  exact GlobalTheory.CompanionTheory.NullFr.det_gU i c₀ h

end GlobalTheory.CompanionTheory.NullFr
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.GaussTubeOfTubeGood
section
noncomputable section

open MeasureTheory Filter Topology PositivityTheory.RgEis

namespace GlobalTheory.CompanionTheory.TubeFourier

variable {X : Type} [NormedAddCommGroup X] [NormedSpace ℂ X]

def pt (x y : ℝ × ℝ) : ℂ × ℂ := (⟨x.1, y.1⟩, ⟨x.2, y.2⟩)

def dot (l : ℂ × ℂ) (t : ℝ × ℝ) : ℂ := l.1 * t.1 + l.2 * t.2

def rdot (x t : ℝ × ℝ) : ℝ := x.1 * t.1 + x.2 * t.2

def phi (G : ℂ × ℂ → X) (x t : ℝ × ℝ) : X :=
  ∫ y : ℝ × ℝ, Complex.exp (-dot (pt x y) t) • G (pt x y)

def inv (φ : ℝ × ℝ → X) (l : ℂ × ℂ) : X :=
  (((2 * Real.pi) ^ 2 : ℂ)⁻¹) • ∫ t : ℝ × ℝ, Complex.exp (dot l t) • φ t

def gauss (F : ℂ × ℂ → X) (l : ℂ × ℂ) : X := Complex.exp (l.1 ^ 2 + l.2 ^ 2) • F l

structure GaussTube (G : ℂ × ℂ → X) (Ω : Set (ℝ × ℝ)) : Prop where
  hol : LineHol G (tube Ω)
  cont : ContinuousOn G (tube Ω)
  decay : ∀ C ⊆ Ω, IsCompact C → ∃ M : ℝ, ∀ l ∈ tube C,
    ‖G l‖ ≤ M * Real.exp (-(l.1.im ^ 2 + l.2.im ^ 2))

def ExpDecay {T : Type} [TopologicalSpace T] (φ : ℝ × ℝ → T → X) : Prop :=
  ∀ (x₀ : ℝ × ℝ) (g : T), ∃ ε : ℝ, 0 < ε ∧ ∃ U ∈ 𝓝 g, ∃ M : ℝ, ∀ x : ℝ × ℝ, |x.1 - x₀.1| ≤ ε → |x.2 - x₀.2| ≤ ε →
    ∀ g' ∈ U, ∀ t : ℝ × ℝ, ‖φ t g'‖ ≤ M * Real.exp (-rdot x t) * Real.exp (-ε * (|t.1| + |t.2|))

theorem norm_exp_sq (l : ℂ × ℂ) : ‖Complex.exp (l.1 ^ 2 + l.2 ^ 2)‖ =
    Real.exp (l.1.re ^ 2 + l.2.re ^ 2) * Real.exp (-(l.1.im ^ 2 + l.2.im ^ 2)) := by
  rw [Complex.norm_exp, ← Real.exp_add]
  congr 1
  simp [sq]
  ring

theorem gauss_bound {T : Type} [TopologicalSpace T] {F : ℂ × ℂ → T → X} {Ω C : Set (ℝ × ℝ)} (h : TubeGood F Ω)
    (hC : C ⊆ Ω) (hc : IsCompact C) (g : T) : ∃ U ∈ 𝓝 g, ∃ M : ℝ, ∀ g' ∈ U, ∀ l ∈ tube C,
      ‖gauss (F · g') l‖ ≤ M * Real.exp (-(l.1.im ^ 2 + l.2.im ^ 2)) := by
  obtain ⟨U, hU, M, hM⟩ := h.bdd C hC hc g
  obtain ⟨B, hB⟩ := (hc.image (f := fun x : ℝ × ℝ => x.1 ^ 2 + x.2 ^ 2) (by fun_prop)).bddAbove
  refine ⟨U, hU, Real.exp B * |M|, fun g' hg' l hl => ?_⟩
  have h1 : l.1.re ^ 2 + l.2.re ^ 2 ≤ B := hB ⟨(l.1.re, l.2.re), hl, rfl⟩
  have h2 : ‖F l g'‖ ≤ |M| := (hM l hl g' hg').trans (le_abs_self M)
  simp only [gauss]
  rw [norm_smul, norm_exp_sq]
  have h3 : Real.exp (l.1.re ^ 2 + l.2.re ^ 2) ≤ Real.exp B := Real.exp_le_exp.2 h1
  have h4 := Real.exp_pos (-(l.1.im ^ 2 + l.2.im ^ 2))
  calc _ = Real.exp (l.1.re ^ 2 + l.2.re ^ 2) * ‖F l g'‖ * Real.exp (-(l.1.im ^ 2 + l.2.im ^ 2)) := by ring
    _ ≤ Real.exp B * |M| * Real.exp (-(l.1.im ^ 2 + l.2.im ^ 2)) := by gcongr

theorem gaussTube_of_tubeGood {T : Type} [TopologicalSpace T] {F : ℂ × ℂ → T → X} {Ω : Set (ℝ × ℝ)}
    (h : TubeGood F Ω) (g : T) : GaussTube (gauss (F · g)) Ω := by
  refine ⟨?_, ?_, ?_⟩
  · intro p v
    have h1 : Differentiable ℂ fun τ : ℂ => Complex.exp ((p + τ • v).1 ^ 2 + (p + τ • v).2 ^ 2) := by
      simp only [Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd, smul_eq_mul]
      fun_prop
    exact h1.differentiableOn.smul (h.hol g p v)
  · have h1 : ContinuousOn (fun l : ℂ × ℂ => F l g) (tube Ω) :=
      h.cont.comp (f := fun l : ℂ × ℂ => (l, g)) (by fun_prop) fun l hl => ⟨hl, trivial⟩
    exact ContinuousOn.smul (by fun_prop) h1
  · intro C hC hc
    obtain ⟨U, hU, M, hM⟩ := gauss_bound h hC hc g
    exact ⟨M, fun l hl => hM g (mem_of_mem_nhds hU) l hl⟩

end GlobalTheory.CompanionTheory.TubeFourier
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.GelfandInfinitesimalCharacter
section
noncomputable section

open PositivityTheory.RgTw (Mat)

namespace GlobalTheory.CompanionTheory.GelfAct

variable {n : ℕ}

open scoped Matrix.Norms.Operator in
theorem hasDerivAt_exp_entry (X : Mat n) (a b : Fin n) :
    HasDerivAt (fun t : ℝ => NormedSpace.exp ((t : ℂ) • X) a b) (X a b) 0 := by
  have hsmul (t : ℝ) : (t : ℂ) • X = t • X := by ext; simp
  simp only [hsmul]
  have h := hasDerivAt_exp_smul_const (𝕂 := ℝ) X (0 : ℝ)
  rw [zero_smul, NormedSpace.exp_zero, one_mul] at h
  let entry : Mat n →L[ℝ] ℂ := (Matrix.entryLinearMap ℝ ℂ a b).toContinuousLinearMap
  exact entry.hasFDerivAt.comp_hasDerivAt 0 h

end GlobalTheory.CompanionTheory.GelfAct

end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.GoodBaseChange
section
open TensorProduct CrystallineSemistableComparison.D
open scoped LaurentPolynomial

namespace GlobalTheory.CompanionTheory.GoodBaseChange

theorem good_baseChange : ∀ (p : ℕ) [Fact p.Prime] (A : Type) [CommRing A](B : Type) [CommRing B] [Algebra A B] (r : ℕ → A) (K₁ K₀ : Type) [AddCommGroup K₁] [Module A K₁] [AddCommGroup K₀] [Module A K₀] (d : K₁ →ₗ[A] K₀), Good p r d → Good p (fun k => algebraMap A B (r k)) (d.baseChange B) := by
  intro p _ A _ B _ _ r K₁ K₀ _ _ _ _ d hd
  intro C _ _ hC w hw k
  letI : Algebra A C := Algebra.compHom C (algebraMap A B)
  haveI : IsScalarTower A B C := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  let e₁ := AlgebraTensorModule.cancelBaseChange A B C C K₁
  let e₀ := AlgebraTensorModule.cancelBaseChange A B C C K₀
  have hnat : ∀ v, e₀ ((d.baseChange B).lTensor C v) = d.lTensor C (e₁ v) := by
    intro v
    induction v using TensorProduct.induction_on with
    | zero => simp
    | tmul c y =>
      induction y using TensorProduct.induction_on with
      | zero => simp
      | tmul b x =>
        simp [e₀, e₁, LinearMap.baseChange_tmul, AlgebraTensorModule.cancelBaseChange_tmul]
      | add y y' h h' => simp only [tmul_add, map_add (f := _), h, h']
    | add v v' h h' => simp only [map_add (f := _), h, h']
  have hw' : d.lTensor C (e₁ w) = 0 := by rw [← hnat, hw, map_zero]
  have hmem := hd C hC (e₁ w) hw' k
  have hsmul : r k • e₁ w = e₁ (algebraMap A B (r k) • w) := by
    rw [← algebraMap_smul C (algebraMap A B (r k)) w, map_smul, algebraMap_smul]
    rfl
  have key : ∀ u : C ⊗[A] LinearMap.ker d,
      e₁.symm ((LinearMap.ker d).subtype.lTensor C u) ∈
        LinearMap.range ((LinearMap.ker (d.baseChange B)).subtype.lTensor C) := by
    intro u
    induction u using TensorProduct.induction_on with
    | zero => simp
    | tmul c x =>
      have hx : (1 : B) ⊗ₜ[A] (x : K₁) ∈ LinearMap.ker (d.baseChange B) := by
        simp [LinearMap.baseChange_tmul, x.2]
      refine ⟨c ⊗ₜ ⟨_, hx⟩, ?_⟩
      simp [e₁, AlgebraTensorModule.cancelBaseChange_symm_tmul]
    | add u u' h h' => rw [map_add (f := _), map_add (f := _)]; exact Submodule.add_mem _ h h'
  obtain ⟨u, hu⟩ := hmem
  have := key u
  rw [hu, hsmul, LinearEquiv.symm_apply_apply] at this
  exact this

end GlobalTheory.CompanionTheory.GoodBaseChange
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HasDerivAtTwistHomotopyKernel
section
noncomputable section

open MvPolynomial Matrix Finset
open scoped ContDiff
open PositivityTheory.RgTw

namespace GlobalTheory.CompanionTheory.TwistHomotopy

variable {n : ℕ}

theorem hb_conjTranspose (p : Fin n × Fin n) : (hb p)ᴴ = hb p := by
  unfold hb
  split_ifs with h1 h2
  · simp
  · simp [conjTranspose_smul, conjTranspose_add, add_comm]
  · have e : star (((Real.sqrt 2 : ℂ))⁻¹ * Complex.I) = -(((Real.sqrt 2 : ℂ))⁻¹ * Complex.I) := by
      simp
    rw [conjTranspose_smul, conjTranspose_sub, e]
    simp [neg_smul, smul_sub]
    abel

end GlobalTheory.CompanionTheory.TwistHomotopy
end
end

