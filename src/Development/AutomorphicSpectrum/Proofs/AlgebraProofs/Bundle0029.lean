module

public import Mathlib
public import ReciprocityTheory.DualLattices.Bundle0004
public import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.IsTight
public import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.Bundle0003
public import Development.WeilBound.CoreStatements.HodgeTatePoints.Bundle0023
public import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.Bundle0004
public import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.Bundle0001
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.StatementsBundles
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Bundle0025
public import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.Bundle0026
public import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.Bundle0009
public import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.Bundle0014
public import Development.WeilBound.CoreStatements.TorusUniformisation.ChowMahlerFamilies.XBundleOps
public import Development.AutomorphicSpectrum.Statements.GeometryStatements.IsPolLatticePlane
public import Development.WeilBound.CoreStatements.HodgeTatePoints.Bundle0021
public import Development.WeilBound.CoreStatements.HodgeTatePoints.ChSplit
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.LinearIndependentEigProj
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.QuotientEigenDifference
public import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.Bundle0005
public import Development.WeilBound.CoreStatements.HodgeTatePoints.Bundle0028

@[expose] public section

-- bundled from Development.AutomorphicSpectrum.Proofs.AlgebraProofs.AugmentationLengthColengthBound
section
open ReciprocityTheory.PGsh.L2 ReciprocityTheory.PGsh.Up GlobalTheory.CompanionTheory.Ar.GR
open scoped Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.CompanionTheory.Relay.augmentation_length_colength_bound : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (R : Type) [CommRing R] [Algebra R C], v.Integers R → v (p : C) < 1 → ∀ (N : Type) [AddCommGroup N] [Fintype N] [DecidableEq N], (∀ x : N, p • x = 0) → ∀ AA : HopfOrder (C := C) R N, ∀ cA cN, HasLen v R (AFQuot p AA.carrier) cA → HasColen R v AA.carrier cN → cA ^ (Fintype.card N * (p - 1)) ≤ cN ^ 2 ∧ (cA ^ (Fintype.card N * (p - 1)) = cN ^ 2 → GenAF p AA.carrier ⊥) := by
  first | exact @PositivityTheory.HtPt.Ra.cnt | exact PositivityTheory.HtPt.Ra.cnt
end

-- bundled from Development.AutomorphicSpectrum.Proofs.AlgebraProofs.ChartBundleBaseExtension
section
open MvPolynomial GlobalTheory.CompanionTheory.Ar.Num GroundTheory.Heights₂.Heights.NumbersDVR
open ReciprocityTheory.ChartRestriction.G.Geo (ChartBundle chartRing div_mem_chartRing exists_pow_mul_mem_chartRing)
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.NumbersDVR.Bundles (mseg mcIdeal chartMon joinCoord bcCoord pullDeg liftVar fnField ck rootNum SameGeneric LatLE IsPull IsPullBC IsSubQuot QuotIso IsFrobPres FlagModel modelDeg restrictChart)

namespace GlobalTheory.CompanionTheory.Ar.Num.PullExists

section Charts

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]
  {K' : Type} [Fintype K'] {ι' : K' → Type} [∀ k, Fintype (ι' k)]

def mixChart (c : ∀ k, ι k) (s : ∀ k : K ⊕ K', Sum.elim ι ι' k) : ∀ k : K ⊕ K', Sum.elim ι ι' k
  | .inl k => c k
  | .inr k => s (.inr k)

def secondChart (s : ∀ k : K ⊕ K', Sum.elim ι ι' k) : ∀ k, ι' k := fun k => s (.inr k)

theorem restrictChart_mixChart (c : ∀ k, ι k) (s : ∀ k : K ⊕ K', Sum.elim ι ι' k) :
    restrictChart (mixChart c s) = c := rfl

theorem secondChart_mixChart (c : ∀ k, ι k) (s : ∀ k : K ⊕ K', Sum.elim ι ι' k) :
    secondChart (mixChart c s) = secondChart s := rfl

theorem mseg_joinCoord {F : Type*} [CommMonoid F] (x : (Σ k, ι k) → F) (z : (Σ k, ι' k) → F)
    (s : ∀ k : K ⊕ K', Sum.elim ι ι' k) :
    mseg (joinCoord x z) s = mseg x (restrictChart s) * mseg z (secondChart s) := by
  simp only [mseg, Fintype.prod_sum_type]
  rfl

end Charts

section Pull

variable {O : Type} [CommRing O] {Ω Ω₁ : Type} [Field Ω] [Field Ω₁] [Algebra O Ω] [Algebra O Ω₁]
  [Algebra Ω Ω₁] [IsScalarTower O Ω Ω₁]
  {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]
  {K' : Type} [Fintype K'] {ι' : K' → Type} [∀ k, Fintype (ι' k)]
  {x : (Σ k, ι k) → Ω} {z : (Σ k, ι' k) → Ω₁}

theorem mseg_bcCoord (x : (Σ k, ι k) → Ω) (z : (Σ k, ι' k) → Ω₁)
    (s : ∀ k : K ⊕ K', Sum.elim ι ι' k) :
    mseg (bcCoord x z) s =
      algebraMap Ω Ω₁ (mseg x (restrictChart s)) * mseg z (secondChart s) := by
  rw [bcCoord, mseg_joinCoord]
  simp [mseg, map_prod]

theorem first_ne_zero {s : ∀ k : K ⊕ K', Sum.elim ι ι' k} (hs : mseg (bcCoord x z) s ≠ 0) :
    mseg x (restrictChart s) ≠ 0 := by
  intro h
  exact hs (by rw [mseg_bcCoord, h]; simp)

theorem second_ne_zero {s : ∀ k : K ⊕ K', Sum.elim ι ι' k} (hs : mseg (bcCoord x z) s ≠ 0) :
    mseg z (secondChart s) ≠ 0 := by
  intro h
  exact hs (by rw [mseg_bcCoord, h]; simp)

theorem ratio_first {s : ∀ k : K ⊕ K', Sum.elim ι ι' k} (hs : mseg (bcCoord x z) s ≠ 0)
    (c : ∀ k, ι k) :
    algebraMap Ω Ω₁ (mseg x c / mseg x (restrictChart s)) ∈
      chartRing O (mseg (bcCoord x z)) s := by
  have h := div_mem_chartRing (o := O) (mseg (bcCoord x z)) s (mixChart c s)
  rw [mseg_bcCoord x z (mixChart c s), mseg_bcCoord x z s, restrictChart_mixChart,
    secondChart_mixChart, mul_div_mul_right _ _ (second_ne_zero hs), ← map_div₀] at h
  exact h

theorem ratio_second {s t : ∀ k : K ⊕ K', Sum.elim ι ι' k} (ht : mseg (bcCoord x z) t ≠ 0) :
    mseg z (secondChart s) / mseg z (secondChart t) ∈ chartRing O (mseg (bcCoord x z)) t := by
  have h := div_mem_chartRing (o := O) (mseg (bcCoord x z)) t (mixChart (restrictChart t) s)
  rw [mseg_bcCoord x z (mixChart (restrictChart t) s), mseg_bcCoord x z t, restrictChart_mixChart,
    secondChart_mixChart, mul_div_mul_left _ _
      ((map_ne_zero (algebraMap Ω Ω₁)).2 (first_ne_zero ht))] at h
  exact h

theorem map_mem_chartRing {s : ∀ k : K ⊕ K', Sum.elim ι ι' k} (hs : mseg (bcCoord x z) s ≠ 0)
    {a : Ω} (ha : a ∈ chartRing O (mseg x) (restrictChart s)) :
    algebraMap Ω Ω₁ a ∈ chartRing O (mseg (bcCoord x z)) s := by
  have hle : chartRing O (mseg x) (restrictChart s) ≤
      (chartRing O (mseg (bcCoord x z)) s).comap (IsScalarTower.toAlgHom O Ω Ω₁) := by
    refine Algebra.adjoin_le ?_
    rintro _ ⟨c, rfl⟩
    exact ratio_first hs c
  exact hle ha

variable {N : ℕ} {V V₁ : Type} [AddCommGroup V] [Module Ω V] [AddCommGroup V₁] [Module Ω₁ V₁]
  [Module Ω V₁] [IsScalarTower Ω Ω₁ V₁]

def pullFam (x : (Σ k, ι k) → Ω) (z : (Σ k, ι' k) → Ω₁) (E : ChartBundle O (mseg x) N V)
    (bc : V →ₗ[Ω] V₁) : (∀ k : K ⊕ K', Sum.elim ι ι' k) → AddSubgroup V₁ := fun s =>
  spanOver (chartRing O (mseg (bcCoord x z)) s) (bc '' (E.lat (restrictChart s) : Set V))

theorem isLatFamily_pullFam (E : ChartBundle O (mseg x) N V) (bc : V →ₗ[Ω] V₁) :
    IsLatFamily O (bcCoord x z) (pullFam x z E bc) := by
  refine ⟨fun s _ a ha v hv => LocFreeBC.smul_mem_spanOver _ _ ha hv,
    fun s t hs ht v hv => ?_⟩
  have hf : mseg (bcCoord x z) s / mseg (bcCoord x z) t ∈ chartRing O (mseg (bcCoord x z)) t :=
    div_mem_chartRing _ t s
  have hst : ∀ a ∈ chartRing O (mseg (bcCoord x z)) t, ∀ e ∈ pullFam x z E bc t,
      a • e ∈ pullFam x z E bc t := fun a ha e he => LocFreeBC.smul_mem_spanOver _ _ ha he
  have hfac : mseg (bcCoord x z) s / mseg (bcCoord x z) t =
      algebraMap Ω Ω₁ (mseg x (restrictChart s) / mseg x (restrictChart t)) *
        (mseg z (secondChart s) / mseg z (secondChart t)) := by
    rw [mseg_bcCoord x z s, mseg_bcCoord x z t, map_div₀, mul_div_mul_comm]
  change v ∈ AddSubgroup.closure _ at hv
  induction hv using AddSubgroup.closure_induction with
  | mem v hv =>
    obtain ⟨a, ha, _, ⟨e, he, rfl⟩, rfl⟩ := hv
    obtain ⟨m₁, hm₁⟩ := exists_pow_mul_mem_chartRing (mseg (bcCoord x z)) s t hs ha
    obtain ⟨m₂, hm₂⟩ := E.overlap _ _ (first_ne_zero hs) (first_ne_zero ht) e he
    refine ⟨m₁ + m₂, AddSubgroup.subset_closure ⟨_, mul_mem hm₁ (pow_mem
      (ratio_second (s := s) ht) m₂), _, ⟨_, hm₂, rfl⟩, ?_⟩⟩
    rw [map_smul, ← algebraMap_smul Ω₁ (_ ^ m₂) (bc e), smul_smul, smul_smul]
    congr 1
    rw [pow_add, map_pow]
    nth_rw 2 [hfac]
    rw [mul_pow]
    ring
  | zero => exact ⟨0, by simp⟩
  | add v w _ _ hv hw => exact LocFreeBC.loc_add _ _ hst hf hv hw
  | neg v _ hv =>
    obtain ⟨n, hn⟩ := hv
    exact ⟨n, by simpa using neg_mem hn⟩

theorem locFree_pullFam (E : ChartBundle O (mseg x) N V) (bc : V →ₗ[Ω] V₁)
    (hbc : IsBaseChange Ω₁ bc) (s : ∀ k : K ⊕ K', Sum.elim ι ι' k)
    (hs : mseg (bcCoord x z) s ≠ 0) :
    LocFree (chartRing O (mseg (bcCoord x z)) s) N (pullFam x z E bc s) := by
  classical
  exact LocFreeBC.locFree_baseChange _ _ (fun _ ha => map_mem_chartRing hs ha) bc hbc N _
    (((BundleOfFamily.main O Ω K ι x N V).2 E).2 _ (first_ne_zero hs))

theorem exists_pullBC [IsDomain O] [IsDiscreteValuationRing O] (E : ChartBundle O (mseg x) N V)
    (bc : V →ₗ[Ω] V₁) (hbc : IsBaseChange Ω₁ bc) :
    ∃ EB : ChartBundle O (mseg (bcCoord x z)) N V₁, IsPullBC O x z bc E EB := by
  classical
  obtain ⟨EB, hEB⟩ := (BundleOfFamily.main O Ω₁ (K ⊕ K') (Sum.elim ι ι') (bcCoord x z) N V₁).1
    (pullFam x z E bc) (isLatFamily_pullFam E bc) (locFree_pullFam E bc hbc)
  refine ⟨EB, fun s hs => ?_⟩
  rw [hEB s hs]
  refine congrArg AddSubgroup.closure (Set.ext fun v => ?_)
  constructor
  · rintro ⟨a, ha, _, ⟨e, he, rfl⟩, rfl⟩
    exact ⟨a, ha, e, he, rfl⟩
  · rintro ⟨a, ha, e, he, rfl⟩
    exact ⟨a, ha, _, ⟨e, he, rfl⟩, rfl⟩

end Pull

theorem main : ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (Ω : Type) [Field Ω] [Algebra O Ω] (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)] (x : (Σ k, ι k) → Ω) (N : ℕ) (V : Type) [AddCommGroup V] [Module Ω V] (E : ChartBundle O (mseg x) N V), (∀ (K' : Type) [Fintype K'] [DecidableEq K'] (ι' : K' → Type) [∀ k, Fintype (ι' k)] (z : (Σ k, ι' k) → Ω), ∃ EB : ChartBundle O (mseg (joinCoord x z)) N V, IsPull O x z E EB) ∧ ∀ (Ω₁ : Type) [Field Ω₁] [Algebra O Ω₁] [Algebra Ω Ω₁] [IsScalarTower O Ω Ω₁] (K' : Type) [Fintype K'] [DecidableEq K'] (ι' : K' → Type) [∀ k, Fintype (ι' k)] (z : (Σ k, ι' k) → Ω₁) (V₁ : Type) [AddCommGroup V₁] [Module Ω₁ V₁] [Module Ω V₁] [IsScalarTower Ω Ω₁ V₁] (bc : V →ₗ[Ω] V₁), IsBaseChange Ω₁ bc → ∃ EB : ChartBundle O (mseg (bcCoord x z)) N V₁, IsPullBC O x z bc E EB := by
  intro O _ _ _ Ω _ _ K _ _ ι _ x N V _ _ E
  refine ⟨fun K' _ _ ι' _ z => ?_,
    fun Ω₁ _ _ _ _ K' _ _ ι' _ z V₁ _ _ _ _ bc hbc => exists_pullBC E bc hbc⟩
  exact exists_pullBC (Ω₁ := Ω) (V₁ := V) (z := z) E LinearMap.id
    (IsBaseChange.ofEquiv (LinearEquiv.refl Ω V))

end GlobalTheory.CompanionTheory.Ar.Num.PullExists
end

-- bundled from Development.AutomorphicSpectrum.Proofs.AlgebraProofs.ChartBundleExtensionComparison
section
open MvPolynomial GlobalTheory.CompanionTheory.Ar.Num GroundTheory.Heights₂.Heights.NumbersDVR
open ReciprocityTheory.ChartRestriction.G.Geo (ChartBundle chartRing)
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.NumbersDVR.Bundles (mseg mcIdeal chartMon joinCoord bcCoord pullDeg liftVar fnField ck rootNum SameGeneric LatLE IsPull IsPullBC IsSubQuot QuotIso IsFrobPres FlagModel modelDeg)

namespace GlobalTheory.CompanionTheory.Ar.Num.QuotExactMiddle

theorem main : ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (Ω : Type) [Field Ω] [Algebra O Ω] (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)] (x : (Σ k, ι k) → Ω) (N₀ N N₂ : ℕ) (V₀ : Type) [AddCommGroup V₀] [Module Ω V₀] (V : Type) [AddCommGroup V] [Module Ω V] (V₂ : Type) [AddCommGroup V₂] [Module Ω V₂] (A A' : (∀ k, ι k) → AddSubgroup V₀) (E E' : ChartBundle O (mseg x) N V) (C C' : ChartBundle O (mseg x) N₂ V₂), QuotExact O x A A' E.lat E'.lat C.lat C'.lat → ∃ E'' : ChartBundle O (mseg x) N V, LatLE O x E' E'' ∧ LatLE O x E'' E ∧ QuotEquiv O x A A' E''.lat E'.lat ∧ QuotEquiv O x E.lat E''.lat C.lat C'.lat := by
  intro O _ _ _ Ω _ _ K _ _ ι _ x N₀ N N₂ V₀ _ _ V _ _ V₂ _ _ A A' E E' C C' hQ
  obtain ⟨Γ, Δ, hΓ, hΔ, hX⟩ := hQ
  have bundleOfFamily : ∀ (N : ℕ) (W : Type) [AddCommGroup W] [Module Ω W],
      (∀ Γ : (∀ k, ι k) → AddSubgroup W, IsLatFamily O x Γ →
        (∀ s, mseg x s ≠ 0 → LocFree (chartRing O (mseg x) s) N (Γ s)) →
        ∃ E : ChartBundle O (mseg x) N W, ∀ s, mseg x s ≠ 0 → E.lat s = Γ s) ∧
      ∀ E : ChartBundle O (mseg x) N W, IsLatFamily O x E.lat ∧
        ∀ s, mseg x s ≠ 0 → LocFree (chartRing O (mseg x) s) N (E.lat s) := by
    classical
    intro N W _ _
    refine ⟨fun Γ hfam hloc => ?_, fun E => ⟨⟨fun s _ => E.stable s, fun s t hs ht => E.overlap s t hs ht⟩, fun s hs => ⟨E.stable s, E.frame s hs⟩⟩⟩
    refine ⟨{ lat := fun s => if mseg x s = 0 then ⊥ else Γ s
              stable := ?_
              frame := ?_
              overlap := ?_ }, ?_⟩
    · intro s a ha e he
      by_cases h : mseg x s = 0
      · simp only [h, if_true, AddSubgroup.mem_bot] at he ⊢
        rw [he, smul_zero]
      · simp only [h, if_false] at he ⊢
        exact hfam.1 s h a ha e he
    · intro s hs
      simp only [hs, if_false]
      exact (hloc s hs).2
    · intro s t hs ht e he
      simp only [hs, ht, if_false] at he ⊢
      exact hfam.2 s t hs ht e he
    · intro s hs
      simp only [hs, if_false]
  obtain ⟨F, hF⟩ : ∃ F : (∀ k, ι k) → AddSubgroup V,
      F = fun s => (Δ s).comap (AddMonoidHom.inl V V₂) := ⟨_, rfl⟩
  have memF : ∀ s b, b ∈ F s ↔ (b, (0 : V₂)) ∈ Δ s := by
    intro s b
    subst hF
    exact Iff.rfl
  have hFlat : IsLatFamily O x F := by
    refine ⟨fun s hs a ha v hv => ?_, fun s t hs ht v hv => ?_⟩
    · have h := hΔ.1.1 s hs a ha (v, 0) ((memF s v).1 hv)
      rw [memF]
      simpa using h
    · obtain ⟨m, hm⟩ := hΔ.1.2 s t hs ht (v, 0) ((memF s v).1 hv)
      refine ⟨m, ?_⟩
      rw [memF]
      simpa using hm
  have hFfree : ∀ s, mseg x s ≠ 0 → LocFree (chartRing O (mseg x) s) N (F s) := by
    intro s hs
    have hE := ((bundleOfFamily N V).2 E).2 s hs
    have hC := ((bundleOfFamily N₂ V₂).2 C).2 s hs
    have hC' := ((bundleOfFamily N₂ V₂).2 C').2 s hs
    have h := (GlobalTheory.CompanionTheory.Ar.Num.LocFreeSchanuel.main (chartRing O (mseg x) s) N N₂ (E.lat s) (C.lat s)
      (C'.lat s) (Δ s) hE hC hC' (fun a ha v hv => hΔ.1.1 s hs a ha v hv)
      (fun v w h => (hΔ.2 s hs).1 v w h) (fun v hv => (hΔ.2 s hs).2.1 v hv)
      (fun w => (hΔ.2 s hs).2.2.1 w) (fun w hw => (hX s hs).2.1 w hw)).2
    rw [hF]
    exact h
  obtain ⟨E'', hE''⟩ := (bundleOfFamily N V).1 F hFlat hFfree
  have memE'' : ∀ s, mseg x s ≠ 0 → ∀ b, b ∈ E''.lat s ↔ (b, (0 : V₂)) ∈ Δ s := by
    intro s hs b
    rw [hE'' s hs, memF]
  refine ⟨E'', fun s hs b hb => ?_, fun s hs b hb => ?_,
    ⟨Γ, ⟨hΓ.1, fun s hs => ⟨fun v w h => ⟨((hΓ.2 s hs).1 v w h).1,
        (memE'' s hs w).2 (((hX s hs).2.2 w).2 ⟨v, h⟩)⟩,
      (hΓ.2 s hs).2.1, (hΓ.2 s hs).2.2.1, (hΓ.2 s hs).2.2.2⟩⟩,
      fun s hs => ⟨(hX s hs).1, fun w hw => ((hX s hs).2.2 w).1 ((memE'' s hs w).1 hw)⟩⟩,
    ⟨Δ, ⟨hΔ.1, fun s hs => ⟨(hΔ.2 s hs).1, (hΔ.2 s hs).2.1, (hΔ.2 s hs).2.2.1,
        fun v hv => (memE'' s hs v).1 hv⟩⟩,
      fun s hs => ⟨fun v hv => (memE'' s hs v).2 hv, (hX s hs).2.1⟩⟩⟩
  · exact (memE'' s hs b).2 ((hΔ.2 s hs).2.2.2 b hb)
  · exact ((hΔ.2 s hs).1 b 0 ((memE'' s hs b).1 hb)).1

end GlobalTheory.CompanionTheory.Ar.Num.QuotExactMiddle
end

-- bundled from Development.AutomorphicSpectrum.Proofs.AlgebraProofs.ChartBundleProduct
section
open MvPolynomial GlobalTheory.CompanionTheory.Ar.Num GroundTheory.Heights₂.Heights.NumbersDVR
open ReciprocityTheory.ChartRestriction.G.Geo (ChartBundle chartRing)
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.NumbersDVR.Bundles (mseg mcIdeal chartMon joinCoord bcCoord pullDeg liftVar fnField ck rootNum SameGeneric LatLE IsPull IsPullBC IsSubQuot QuotIso IsFrobPres FlagModel modelDeg)

namespace GlobalTheory.CompanionTheory.Ar.BundleOps

theorem main : ∀ (O : Type) [CommRing O] (Ω : Type) [Field Ω] [Algebra O Ω] (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)] (x : (Σ k, ι k) → Ω), (∀ (N N₁ : ℕ) (V : Type) [AddCommGroup V] [Module Ω V] (V₁ : Type) [AddCommGroup V₁] [Module Ω V₁] (E : ChartBundle O (mseg x) N V) (F : ChartBundle O (mseg x) N₁ V₁), ∃ P : ChartBundle O (mseg x) (N + N₁) (V × V₁), ∀ s, mseg x s ≠ 0 → P.lat s = (E.lat s).prod (F.lat s)) ∧ (∀ (N : ℕ) (V : Type) [AddCommGroup V] [Module Ω V] (E : ChartBundle O (mseg x) N V) (c : Ω), c ≠ 0 → ∃ E' : ChartBundle O (mseg x) N V, IsScaled x c E.lat E'.lat) ∧ (∀ (u : Ω) (a : K → ℤ), u ≠ 0 → ∃ A : ChartBundle O (mseg x) 1 Ω, IsLine O x u a A.lat) ∧ (∀ (N : ℕ) (V : Type) [AddCommGroup V] [Module Ω V] (t : Module.Basis (Fin N) Ω V), ∃ T : ChartBundle O (mseg x) N V, ∀ s, mseg x s ≠ 0 → ∀ v, v ∈ T.lat s ↔ ∀ i, t.repr v i ∈ chartRing O (mseg x) s) ∧ (∀ (N : ℕ) (V : Type) [AddCommGroup V] [Module Ω V] (V₁ : Type) [AddCommGroup V₁] [Module Ω V₁] (E : ChartBundle O (mseg x) N V) (β : V →ₗ[Ω] V₁ →ₗ[Ω] Ω), Function.Bijective β.flip → ∃ F : ChartBundle O (mseg x) N V₁, IsDualLat O x β E.lat F.lat) :=
  @PositivityTheory.Xgn.t_bundle_ops

end GlobalTheory.CompanionTheory.Ar.BundleOps
end

-- bundled from Development.AutomorphicSpectrum.Proofs.AlgebraProofs.ChartBundleQuotientEquivalence
section
open MvPolynomial GlobalTheory.CompanionTheory.Ar.Num GroundTheory.Heights₂.Heights.NumbersDVR
open ReciprocityTheory.ChartRestriction.G.Geo (ChartBundle chartRing)
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.NumbersDVR.Bundles (mseg mcIdeal chartMon joinCoord bcCoord pullDeg liftVar fnField ck rootNum SameGeneric LatLE IsPull IsPullBC IsSubQuot QuotIso IsFrobPres FlagModel modelDeg)

namespace GlobalTheory.CompanionTheory.Ar.Num.QuotEquivIso

theorem main : ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (Ω : Type) [Field Ω] [Algebra O Ω] (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)] (x : (Σ k, ι k) → Ω) (N N₁ : ℕ) (V : Type) [AddCommGroup V] [Module Ω V] (V₁ : Type) [AddCommGroup V₁] [Module Ω V₁] (E E' : ChartBundle O (mseg x) N V) (F F' : ChartBundle O (mseg x) N₁ V₁), QuotEquiv O x E.lat E'.lat F.lat F'.lat ↔ QuotIso O x E E' F F' := by
  intro O _ _ _ Ω _ _ K _ _ ι _ x N N₁ V _ _ V₁ _ _ E E' F F'
  unfold GlobalTheory.CompanionTheory.Ar.Num.QuotEquiv GlobalTheory.CompanionTheory.Ar.Num.IsQuotHom
    GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.NumbersDVR.Bundles.QuotIso
  constructor
  · rintro ⟨Γ, ⟨hlat, hΓ⟩, hΓ'⟩
    have hloc : ∀ s, GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.NumbersDVR.Bundles.mseg x s ≠ 0 →
        GlobalTheory.CompanionTheory.Ar.Num.LocFree
          (ReciprocityTheory.ChartRestriction.G.Geo.chartRing O (GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.NumbersDVR.Bundles.mseg x) s)
          (N + N₁) (Γ s) := by
      intro s hs
      obtain ⟨h1, h2, h3, _⟩ := hΓ s hs
      obtain ⟨_, h6⟩ := hΓ' s hs
      exact (GlobalTheory.CompanionTheory.Ar.Num.LocFreeSchanuel.main _ N N₁ (E.lat s) (F.lat s) (F'.lat s) (Γ s)
        (((GlobalTheory.CompanionTheory.Ar.Num.BundleOfFamily.main O Ω K ι x N V).2 E).2 s hs)
        (((GlobalTheory.CompanionTheory.Ar.Num.BundleOfFamily.main O Ω K ι x N₁ V₁).2 F).2 s hs)
        (((GlobalTheory.CompanionTheory.Ar.Num.BundleOfFamily.main O Ω K ι x N₁ V₁).2 F').2 s hs)
        (hlat.1 s hs) h1 h2 h3 h6).1
    obtain ⟨Pb, hPb⟩ := (GlobalTheory.CompanionTheory.Ar.Num.BundleOfFamily.main O Ω K ι x (N + N₁) (V × V₁)).1 Γ hlat hloc
    refine ⟨Pb, fun s hs => ?_⟩
    rw [hPb s hs]
    obtain ⟨h1, h2, h3, h4⟩ := hΓ s hs
    obtain ⟨h5, h6⟩ := hΓ' s hs
    exact ⟨fun v => ⟨h5 v, h4 v⟩, fun v => ⟨fun h => Exists.elim h fun w hw => (h1 v w hw).1, h2 v⟩, h3,
      fun w => ⟨fun h => Exists.elim h fun v hv => (h1 v w hv).2, h6 w⟩⟩
  · rintro ⟨Pb, hPb⟩
    refine ⟨Pb.lat, ⟨((GlobalTheory.CompanionTheory.Ar.Num.BundleOfFamily.main O Ω K ι x _ _).2 Pb).1, fun s hs => ?_⟩,
      fun s hs => ?_⟩
    · obtain ⟨h1, h2, h3, h4⟩ := hPb s hs
      exact ⟨fun v w hvw => ⟨(h2 v).1 ⟨w, hvw⟩, (h4 w).1 ⟨v, hvw⟩⟩, fun v hv => (h2 v).2 hv, h3,
        fun v hv => (h1 v).2 hv⟩
    · obtain ⟨h1, -, -, h4⟩ := hPb s hs
      exact ⟨fun v hv => (h1 v).1 hv, fun w hw => (h4 w).2 hw⟩

end GlobalTheory.CompanionTheory.Ar.Num.QuotEquivIso
end

-- bundled from Development.AutomorphicSpectrum.Proofs.AlgebraProofs.CompleteIntegersProperties
section
open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct NumberField GlobalTheory GlobalTheory.PDivGroup GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.BT GlobalTheory.CompanionTheory.Ar.HT ReciprocityTheory.ChartRestriction.G.Semi

namespace GlobalTheory.CompanionTheory.Ar.HT

theorem padicComplete_integers_structure : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (O : Type) [CommRing O] [IsDomain O] [Algebra O C] (hv : v.Integers O) (hp : v (p : C) < 1) (hO : IsAdicComplete (Ideal.span {(p : O)}) O), Nonempty (Algebra ℤ_[p] O) ∧ HenselianLocalRing O ∧ IsIntegrallyClosed O ∧ ValuationRing O ∧ IsAlgClosed (FractionRing O) ∧ IsFractionRing O C :=
  @PositivityTheory.HtPt.Twhopf.padic_alg

end GlobalTheory.CompanionTheory.Ar.HT
end

-- bundled from Development.AutomorphicSpectrum.Proofs.AlgebraProofs.DegreeSumEigenSubDegrees
section
open GlobalTheory.CompanionTheory.Ar.Crv

namespace GlobalTheory.CompanionTheory.Ar.Crv

theorem degree_eq_sum_eigen : ∀ (K : Type) [Field K] (C : ACurve K) (V : Type) [AddCommGroup V] [Module K V] [FiniteDimensional K V] (L : C.I → AddSubgroup V) (O k S : Type) [CommRing O] [Field k] [Algebra k K] [Fintype S] [DecidableEq S] (χ : S → (O →+* k)), IsSplit χ → (∀ i (c : k), C.v i (algebraMap k K c) ≤ 1) → ∀ ρ : O →+* Module.End K V, IsBun C L → (∀ a, IsHom C L L (ρ a)) → deg C L = ∑ s, subDeg C L (eig (fun a => ρ a) (fun a => algebraMap k K (χ s a))) :=
  @PositivityTheory.HtPt.Ch.split_deg

end GlobalTheory.CompanionTheory.Ar.Crv
end

-- bundled from Development.AutomorphicSpectrum.Proofs.AlgebraProofs.EigCoordApply
section
open scoped NNReal
open NumberField GlobalTheory.IndefiniteRowSideFullHecke.QuotientEigenDifference GlobalTheory.CompanionTheory.Ar

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Flat.ExG

def kerFil {C : Type} [Field C] {w : Valuation C ℝ≥0} {S W : Type} [AddCommGroup W] [Module C W]
    (a : S → w.valuationSubring) (r : ℕ) (g : S → (Fin r → C) →ₗ[C] W) :
    Submodule w.valuationSubring (S → Fin r → C) where
  carrier := {f | f ∈ freeLattice a r ∧ ∀ s, g s (f s) = 0}
  zero_mem' := ⟨zero_mem _, fun s => by simp⟩
  add_mem' := fun hx hy => ⟨add_mem hx.1 hy.1, fun s => by simp [hx.2 s, hy.2 s]⟩
  smul_mem' := fun c f hf => ⟨Submodule.smul_mem _ c hf.1, fun s => by
    have e : (c • f) s = (c : C) • f s := rfl
    rw [e, map_smul, hf.2 s, smul_zero]⟩

def eigCoord {E : Type} [Field E] [NumberField E] {C M : Type} [Field C] [AddCommGroup M] [Module C M]
    (ρ : 𝓞 E →+* Module.End C M) {N : ℕ} (t : Fin N → M) (s : E →+* C) : (Fin N → C) →ₗ[C] M :=
  Fintype.linearCombination C (fun j => HT.eigProj ρ s (t j))

theorem eigCoord_apply {E : Type} [Field E] [NumberField E] {C M : Type} [Field C] [AddCommGroup M] [Module C M]
    (ρ : 𝓞 E →+* Module.End C M) {N : ℕ} (t : Fin N → M) (s : E →+* C) (y : Fin N → C) :
    eigCoord ρ t s y = ∑ j, y j • HT.eigProj ρ s (t j) := by
  simp [eigCoord, Fintype.linearCombination_apply]

def TargetO : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] (C : Type) [Field C] [CharZero C] (ν : Valuation C ℝ≥0)
    (bar : 𝓞 E ≃+* 𝓞 E) (σ σ' : E →+* C) (rk : (E →+* C) → ℕ) (p q : ℕ),
    (∃ ℓ : C, 0 < ν ℓ ∧ ν ℓ < 1) →
    (∀ (s : E →+* C) (a : 𝓞 E), s (a : E) ∈ ν.valuationSubring) →
    Nat.card (E →+* C) = Module.finrank ℚ E → (∀ a : 𝓞 E, σ' (a : E) = σ (bar a : 𝓞 E)) →
    (∀ a, bar (bar a) = a) →
    ∃ γ : C, γ ≠ 0 ∧ ∀ (W : Type) [AddCommGroup W] [Module C W] [Module ν.valuationSubring W]
      [IsScalarTower ν.valuationSubring C W] [FiniteDimensional C W]
      (ρ : 𝓞 E →+* Module.End C W) (ρH : 𝓞 E →+* Module.End C (W × Module.Dual C W))
      (HV : Submodule ν.valuationSubring (W × Module.Dual C W)) (Lie : Submodule ν.valuationSubring W)
      (x : Fin (p + q) → W × Module.Dual C W) (v : Fin p → W) (w : Fin q → W)
      (u : Fin (p + q) → W × Module.Dual C W) (A : Matrix (Fin (p + q)) (Fin (p + q)) C),
      (∀ a y, (ρH a y).1 = ρ a y.1) → (∀ a φ, ρH a (0, φ) = (0, φ ∘ₗ ρ (bar a))) →
      HV.map ((LinearMap.fst C W (Module.Dual C W)).restrictScalars ν.valuationSubring) = Lie →
      (∀ φ : Module.Dual C W, (0, φ) ∈ HV ↔ ∀ e ∈ Lie, φ e ∈ (algebraMap ν.valuationSubring C).range) →
      HT.IsFreeOn ρH HV x → (∀ s, Module.finrank C (HT.eigSp ρ s) = rk s) →
      LinearIndependent C v → Submodule.span ν.valuationSubring (Set.range v) = HT.eigSub ρ σ Lie →
      LinearIndependent C w → Submodule.span ν.valuationSubring (Set.range w) = HT.eigSub ρ σ' Lie →
      IsAdapted ρH σ v w u → LinearIndependent C (fun i => ∑ j, A i j • u j) →
      Submodule.span ν.valuationSubring (Set.range fun i => ∑ j, A i j • u j) = HT.eigQuot ρH σ HV →
      ∃ ε : (ν.valuationSubring)ˣ, A.det = algebraMap ν.valuationSubring C ε * γ

end GlobalTheory.CompanionTheory.Ar.Flat.ExG
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.AlgebraProofs.FormalBilinearTermProductStatement
section
open MvPowerSeries ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ GlobalTheory.CompanionTheory.Ar.Crv GlobalTheory.CompanionTheory.Ar.Conj
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.formal_bilinear_term_product : ∀ (R : Type) [CommRing R] (d : ℕ) (f g : PS R 2 d) (φ ψ : Pt R 1 d), AxOne f → AxOne g → (∀ i, constantCoeff (φ i) = 0) → (∀ i, constantCoeff (ψ i) = 0) → AxOne (f * g) ∧ (∀ m, bil (f * g) m 1 = bil f m 1 + bil g m 1) ∧ (∀ n, bil (f * g) 1 n = bil f 1 n + bil g 1 n) ∧ AxOne (ev (n := 2) ![comp1 φ (pt R d 0), comp1 ψ (pt R d 1)] f) ∧ bil (ev (n := 2) ![comp1 φ (pt R d 0), comp1 ψ (pt R d 1)] f) 1 1 = (lin φ 1).transpose * bil f 1 1 * lin ψ 1 ∧ (∀ m n, bil (ev (n := 2) ![pt R d 1, pt R d 0] f) m n = (bil f n m).transpose) ∧ ∀ m n : ℕ, 1 ≤ m → 1 ≤ n → bil (ev (n := 2) ![ptPow R d m 0, ptPow R d n 1] f) m n = bil f 1 1 := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Conj.BilCalc.bil_calc | exact GlobalTheory.CompanionTheory.Ar.Conj.BilCalc.bil_calc | (intros; apply GlobalTheory.CompanionTheory.Ar.Conj.BilCalc.bil_calc <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.AlgebraProofs.HodgeTateChartDifferentBound
section
open Module NumberField GlobalTheory.CompanionTheory.Ar.HT TensorProduct

namespace GlobalTheory.CompanionTheory.Ar.HT

theorem dualMap_exists_unique_split : ∀ (A K : Type) [CommRing A] [Field K] [Algebra A K] [CharZero K] (hAK : Function.Injective (algebraMap A K)) (E : Type) [Field E] [NumberField E] (c : E ≃+* E) (hc : ∀ x, c (c x) = x) (p R N : ℕ) [Fact p.Prime] (Ω : Type) [AddCommGroup Ω] [Module K Ω] [Module A Ω] [IsScalarTower A K Ω] (D : HTChart A K c p R N Ω) (κ : A) (σ : E →+* K) (d : A) (m : ℕ), (∀ (σ : E →+* K) (a : 𝓞 E), σ (a : E) ∈ (algebraMap A K).range) → GeneratesDiff σ d → κ * (p : A) ^ m ∣ (p : A) ^ R → (∀ x ∈ D.om, κ • x ∈ D.om') → Module.Projective A (D.omHT (σ.comp c.toRingHom)) → (∃ (i : Module.Dual A (D.omHT (σ.comp c.toRingHom)) →ₗ[A] (Fin N → A)), D.IsDualMap σ d m i) ∧ (∀ i i', D.IsDualMap σ d m i → D.IsDualMap σ d m i' → ∀ w, ∃ x : Fin N → A, i w = i' w + ((p : A) ^ m) • x) ∧ ∀ i, D.IsDualMap σ d m i → ∃ r : (Fin N → A) →ₗ[A] Module.Dual A (D.omHT (σ.comp c.toRingHom)), ∀ w, ∃ w', r (i w) = w + ((p : A) ^ m) • w' :=
  @PositivityTheory.HtPt.Ga.dual_map

end GlobalTheory.CompanionTheory.Ar.HT
end

-- bundled from Development.AutomorphicSpectrum.Proofs.AlgebraProofs.HodgeTateChartNonUnitP
section
open Module NumberField GlobalTheory.CompanionTheory.Ar.HT TensorProduct

namespace GlobalTheory.CompanionTheory.Ar.HT

theorem chart_rank_add_conj : ∀ (A K : Type) [CommRing A] [IsDomain A] [IsNoetherianRing A] [IsIntegrallyClosed A] [Field K] [Algebra A K] [IsFractionRing A K] [CharZero K] (E : Type) [Field E] [NumberField E] (c : E ≃+* E) (hc : ∀ x, c (c x) = x) (p R N : ℕ) [Fact p.Prime] (Ω : Type) [AddCommGroup Ω] [Module K Ω] [Module A Ω] [IsScalarTower A K Ω] (D : HTChart A K c p R N Ω) (κ : A) (σ : E →+* K) (d d' : A), ¬ IsUnit (p : A) → κ ∣ (p : A) ^ R → GeneratesDiff σ d → GeneratesDiff (σ.comp c.toRingHom) d' → Module.Projective A (D.omHT σ) → Module.Projective A (D.omHT (σ.comp c.toRingHom)) → D.HasTestPoints κ → Module.finrank A (D.omHT σ) + Module.finrank A (D.omHT (σ.comp c.toRingHom)) = N :=
  @PositivityTheory.HtPt.Gb.chart_rank

end GlobalTheory.CompanionTheory.Ar.HT
end

