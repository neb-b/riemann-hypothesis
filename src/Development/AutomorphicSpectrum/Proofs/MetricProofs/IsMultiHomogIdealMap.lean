module

public import Mathlib
public import Development.AutomorphicSpectrum.Definitions.MetricPeriods.Pull1
public import Development.AutomorphicSpectrum.Definitions.MetricPeriods.IsPeriodOn
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0035
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0040
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.FlagModelBaseProjectionPoints
public import GroundTheory.HeightsAndTheta.Heights.Intersections.IsMultiHomogOfPullWeight
public import GroundTheory.HeightsAndTheta.Heights.Intersections.Bundle0039
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0103
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0063
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0064
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0065
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.LogResolutionCompatiblePullback
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.FlagCoverArithmeticFourth
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.FlagCoverArithmeticFifth
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.FlagCoverArithmeticSeventh
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.FlagCoverArithmeticEighth
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0111

@[expose] public section

open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical

noncomputable section
namespace GlobalTheory.CompanionTheory.Ar.PB.CovMap

section Forms

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]
  {K' : Type} [Fintype K'] {ι' : K' → Type} [∀ k, Fintype (ι' k)]

theorem isMultiHomog_mul {f g : MRing ι} {a b : K → ℕ} (hf : IsMultiHomog f a) (hg : IsMultiHomog g b) :
    IsMultiHomog (f * g) (a + b) := by
  intro m hm k
  obtain ⟨m1, hm1, m2, hm2, rfl⟩ := Finset.mem_add.mp (MvPolynomial.support_mul _ _ hm)
  have h1 := hf m1 hm1 k
  have h2 := hg m2 hm2 k
  simp [Finset.sum_add_distrib, h1, h2]

theorem isMultiHomog_rename {κ : K → K'} {v : (Σ k, ι k) → (Σ k, ι' k)} (hv : IsBlockMap κ v) {f : MRing ι}
    {a : K → ℕ} (hf : IsMultiHomog f a) : IsMultiHomog (rename v f : MRing ι') (Function.extend κ a 0) := by
  intro m hm k'
  rw [support_rename_of_injective hv.2.1] at hm
  obtain ⟨m0, hm0, rfl⟩ := Finset.mem_image.mp hm
  by_cases hk : k' ∈ Set.range κ
  · obtain ⟨k, rfl⟩ := hk
    rw [hv.1.extend_apply, ← hf m0 hm0 k]
    have hex : ∀ i' : ι' (κ k), ∃ i : ι k, v ⟨k, i⟩ = ⟨κ k, i'⟩ := by
      intro i'
      obtain ⟨p, hp⟩ := hv.2.2.2 ⟨κ k, i'⟩ ⟨k, rfl⟩
      have h1 : κ p.1 = κ k := by rw [← hv.2.2.1 p, hp]
      obtain ⟨k₁, i⟩ := p
      obtain rfl : k₁ = k := hv.1 h1
      exact ⟨i, hp⟩
    choose g hg using hex
    have hb : Function.Bijective g := by
      constructor
      · intro a b hab
        have : (⟨κ k, a⟩ : Σ k, ι' k) = ⟨κ k, b⟩ := by rw [← hg a, ← hg b, hab]
        exact eq_of_heq (Sigma.mk.inj this).2
      · intro i
        obtain ⟨q1, q2⟩ : ∃ q : Σ k, ι' k, q = v ⟨k, i⟩ := ⟨_, rfl⟩
        have hq : ∃ i', v ⟨k, i⟩ = ⟨κ k, i'⟩ := by
          have h1 := hv.2.2.1 ⟨k, i⟩
          generalize v ⟨k, i⟩ = q at h1
          obtain ⟨q1, q2⟩ := q
          simp only at h1
          subst h1
          exact ⟨q2, rfl⟩
        obtain ⟨i', hi'⟩ := hq
        refine ⟨i', ?_⟩
        have h2 : v ⟨k, g i'⟩ = v ⟨k, i⟩ := by rw [hg i', hi']
        exact eq_of_heq (Sigma.mk.inj (hv.2.1 h2)).2
    calc ∑ i', (Finsupp.mapDomain v m0) ⟨κ k, i'⟩ = ∑ i', m0 ⟨k, g i'⟩ := by
          refine Finset.sum_congr rfl fun i' _ => ?_
          rw [← hg i', Finsupp.mapDomain_apply_of_injective hv.2.1]
      _ = ∑ i, m0 ⟨k, i⟩ := hb.sum_comp fun i => m0 ⟨k, i⟩
  · rw [Function.extend_apply' _ _ _ (by simpa using hk)]
    refine Finset.sum_eq_zero fun i' _ => ?_
    refine Finsupp.mapDomain_notin_range _ _ ?_
    rintro ⟨p, hp⟩
    exact hk ⟨p.1, by rw [← hv.2.2.1 p, hp]⟩

theorem eval_map_rename (zt : (Σ k, ι' k) → ℂ) (v : (Σ k, ι k) → (Σ k, ι' k)) (s : MRing ι) :
    eval zt (map (Int.castRingHom ℂ) (rename v s : MRing ι')) = eval (fun p => zt (v p)) (map (Int.castRingHom ℂ) s) := by
  rw [map_rename, eval_rename]
  rfl

theorem mem_mcPts_map {v : (Σ k, ι k) → (Σ k, ι' k)} {J : Ideal (MRing ι)} {zt : (Σ k, ι' k) → ℂ}
    (h0 : ∀ k, ∃ i, zt ⟨k, i⟩ ≠ 0) (hz : ∀ f ∈ J, eval (fun p => zt (v p)) (map (Int.castRingHom ℂ) f) = 0) :
    zt ∈ mcPts (J.map (rename v : MRing ι →ₐ[ℤ] MRing ι').toRingHom) := by
  refine ⟨h0, ?_⟩
  have hle : J.map (rename v : MRing ι →ₐ[ℤ] MRing ι').toRingHom ≤
      RingHom.ker ((eval zt).comp (map (Int.castRingHom ℂ)) : MRing ι' →+* ℂ) := by
    rw [Ideal.map_le_iff_le_comap]
    intro s hs
    rw [Ideal.mem_comap, RingHom.mem_ker]
    change eval zt (map (Int.castRingHom ℂ) (rename v s : MRing ι')) = 0
    rw [eval_map_rename]
    exact hz s hs
  intro f hf
  exact RingHom.mem_ker.mp (hle hf)

theorem isMultiHomogIdeal_map {κ : K → K'} {v : (Σ k, ι k) → (Σ k, ι' k)} (hv : IsBlockMap κ v)
    {J : Ideal (MRing ι)} (hJ : IsMultiHomogIdeal J) :
    IsMultiHomogIdeal (J.map (rename v : MRing ι →ₐ[ℤ] MRing ι').toRingHom) := by
  obtain ⟨S, hS, rfl⟩ := hJ
  refine ⟨_ '' S, ?_, Ideal.map_span _ _⟩
  rintro _ ⟨s, hs, rfl⟩
  obtain ⟨a, ha⟩ := hS s hs
  exact ⟨_, isMultiHomog_rename hv ha⟩

end Forms

theorem holoMap_comp {e₁ e₂ e₃ : ℕ} {X Y Z : Type} [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z]
    {C : FinHolAtlas e₁ Z} {B : FinHolAtlas e₂ Y} {A : FinHolAtlas e₃ X} {g : Z → Y} {f : Y → X}
    (hg : HoloMap C B g) (hf : HoloMap B A f) : HoloMap C A (f ∘ g) := by
  refine ⟨hf.1.comp hg.1, fun j k t ht => ?_⟩
  obtain ⟨ht1, ht2⟩ := ht
  obtain ⟨m, hm⟩ := B.cover (g ((C.chart j).symm t))
  have h1 : AnalyticAt ℂ (B.chart m ∘ g ∘ (C.chart j).symm) t := hg.2 j m t ⟨ht1, hm⟩
  have hu : (B.chart m).symm ((B.chart m ∘ g ∘ (C.chart j).symm) t) = g ((C.chart j).symm t) :=
    (B.chart m).left_inv hm
  have h2 : AnalyticAt ℂ (A.chart k ∘ f ∘ (B.chart m).symm) ((B.chart m ∘ g ∘ (C.chart j).symm) t) :=
    hf.2 m k _ ⟨(B.chart m).map_source hm, by
      rw [Set.mem_preimage, hu]; exact ht2⟩
  refine (h2.comp h1).congr ?_
  have hc : ContinuousAt (g ∘ (C.chart j).symm) t :=
    hg.1.continuousAt.comp ((C.chart j).continuousAt_symm ht1)
  filter_upwards [hc ((B.chart m).open_source.mem_nhds hm)] with t' ht'
  have ht'' : g ((C.chart j).symm t') ∈ (B.chart m).source := ht'
  simp only [Function.comp]
  rw [(B.chart m).left_inv ht'']

end GlobalTheory.CompanionTheory.Ar.PB.CovMap

noncomputable section
namespace GlobalTheory.CompanionTheory.Ar.PB.CovMap

section Corr

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {Φ : Type} [Field Φ] {y : (Σ k, ι k) → Φ}
  {Ψ : Type} [Fintype Ψ] [DecidableEq Ψ] {N j : ℕ} {M : FlagModel y Ψ N j} {K' : Type} [Fintype K']
  {ι' : K' → Type} [∀ k, Fintype (ι' k)] {Φ' : Type} [Field Φ'] {y' : (Σ k, ι' k) → Φ'}
  {M' : FlagModel y' Ψ N j}

end Corr

end GlobalTheory.CompanionTheory.Ar.PB.CovMap

noncomputable section
namespace GlobalTheory.CompanionTheory.Ar.PB.CovMap

end GlobalTheory.CompanionTheory.Ar.PB.CovMap
