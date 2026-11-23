module

public import Mathlib
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.EmbedsGeneric
public import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.GoodOrigin
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0097
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0104
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.LocalRingPointsExistsUnique
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle0004
public import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.FrameDefinitions.Metric
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsGrpPullback
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0022
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle0014
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsHolPeriods
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0052
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0105
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0043
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0094
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.HolomorphicFamilies.Bundle0004
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.HolomorphicHomDetermined
public import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.MemRangeCompIffOfIsClosedImmersion
public import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.PVertFactorSmooth
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0100
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.GlobalSectionsRankAlgClosed
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle0010
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle0005
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle0007

@[expose] public section

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.DominatingCoordsReindexed
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar
open ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P GlobalTheory.CompanionTheory.Ar.PB GlobalTheory.CompanionTheory.Ar.Chg
open ReciprocityTheory.ChartRestriction.G.AI.I1 (IsBlockMap pullDeg)
open ReciprocityTheory.ChartRestriction.G.AI.I4 (imageZ IsPullHerm)
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Inter (pullHerm)

namespace GlobalTheory.CompanionTheory.Ar.Chg

private lemma valAt_unique_lemma {X : Scheme.{0}} {Ω : Type} [Field Ω]
    (ξ : Spec (CommRingCat.of Ω) ⟶ X) (z : Spec (CommRingCat.of ℂ) ⟶ X) {b : Ω} {r r' : ℂ}
    (h1 : GlobalTheory.CompanionTheory.Ar.ValAt ξ z b r) (h2 : GlobalTheory.CompanionTheory.Ar.ValAt ξ z b r') : r = r' := by
  obtain ⟨hs, s, hs1, hs2⟩ := h1
  obtain ⟨hs', s', hs1', hs2'⟩ := h2
  have hs1'' : GlobalTheory.CompanionTheory.Ar.genMap ξ ⟨GlobalTheory.CompanionTheory.Ar.centre z, hs⟩ s' = b := hs1'
  have e0 : GlobalTheory.CompanionTheory.Ar.genMap ξ ⟨GlobalTheory.CompanionTheory.Ar.centre z, hs⟩ (s - s') = 0 :=
    (map_sub _ s s').trans (by rw [hs1, hs1'', sub_self])
  have hnu : ¬ IsUnit (s - s') := by
    intro hu
    have hu' := hu.map (GlobalTheory.CompanionTheory.Ar.genMap ξ ⟨GlobalTheory.CompanionTheory.Ar.centre z, hs⟩)
    exact not_isUnit_zero ((congrArg IsUnit e0).mp hu')
  have e1 : (Scheme.stalkClosedPointTo z).hom (s - s') = r - r' := by
    rw [← hs2, ← hs2']
    exact map_sub _ _ _
  by_contra hne
  apply hnu
  apply (Scheme.isLocalHom_stalkClosedPointTo z).map_nonunit
  exact (congrArg IsUnit e1).mpr (sub_ne_zero.mpr hne).isUnit

private lemma valAt_mul_lemma_2 {X : Scheme.{0}} {Ω : Type} [Field Ω]
    (ξ : Spec (CommRingCat.of Ω) ⟶ X) (z : Spec (CommRingCat.of ℂ) ⟶ X) {b b' : Ω} {r r' : ℂ}
    (h1 : GlobalTheory.CompanionTheory.Ar.ValAt ξ z b r) (h2 : GlobalTheory.CompanionTheory.Ar.ValAt ξ z b' r') :
    GlobalTheory.CompanionTheory.Ar.ValAt ξ z (b * b') (r * r') ∧ GlobalTheory.CompanionTheory.Ar.ValAt ξ z 1 1 := by
  obtain ⟨hs, s, hs1, hs2⟩ := h1
  obtain ⟨hs', s', hs1', hs2'⟩ := h2
  have hs1'' : GlobalTheory.CompanionTheory.Ar.genMap ξ ⟨GlobalTheory.CompanionTheory.Ar.centre z, hs⟩ s' = b' := hs1'
  exact ⟨⟨hs, s * s', (map_mul _ s s').trans (congrArg₂ (· * ·) hs1 hs1''),
      (map_mul _ s s').trans (congrArg₂ (· * ·) hs2 hs2')⟩,
    ⟨hs, 1, map_one _, map_one _⟩⟩

theorem coordsAt_blkV : ∀ (X X₀ : Scheme.{0}) (Ω Ω₀ : Type) [Field Ω] [Field Ω₀] (ξ : Spec (CommRingCat.of Ω) ⟶ X) (ξ₀ : Spec (CommRingCat.of Ω₀) ⟶ X₀) (h : X ⟶ X₀) (i : Ω₀ →+* Ω) (K₀ K : Type) [Fintype K₀] [Fintype K] (J₀ : K₀ → Type) (J : K → Type) [∀ k, Fintype (J₀ k)] [∀ k, Fintype (J k)] (y₀ : (Σ k, J₀ k) → Ω₀) (y : (Σ k, J k) → Ω) (bk : K₀ → K) (bx : ∀ k, J₀ k ≃ J (bk k)), GlobalTheory.CompanionTheory.Ar.Dominates ξ ξ₀ h i → CoordTie ℤ ξ₀ (fun c' : (k : K₀) → J₀ k => ∏ k, y₀ ⟨k, c' k⟩) → (∀ q : X, genPt ξ ⤳ q) → (∀ k a, y ⟨bk k, bx k a⟩ = i (y₀ ⟨k, a⟩)) → (∀ (z : Spec (CommRingCat.of ℂ) ⟶ X) (a : Ω₀) (r : ℂ), ValAt ξ₀ (z ≫ h) a r → ValAt ξ z (i a) r) → ∀ (z : Spec (CommRingCat.of ℂ) ⟶ X) (w : (Σ k, J k) → ℂ), CoordsAt ξ y z w → CoordsAt ξ₀ y₀ (z ≫ h) (fun p => w (blkV bk bx p)) := by
  classical
  intro X X₀ Ω Ω₀ _ _ ξ ξ₀ h i K₀ K _ _ J₀ J _ _ y₀ y bk bx hdom htie hgen hy hval z w hw
  unfold GlobalTheory.CompanionTheory.Ar.Dominates at hdom
  have hpt : ∀ (a b : PrimeSpectrum Ω₀), a = b := fun a b =>
    PrimeSpectrum.ext ((Ideal.eq_bot_of_prime a.asIdeal).trans (Ideal.eq_bot_of_prime b.asIdeal).symm)
  have hsp : GlobalTheory.CompanionTheory.Ar.genPt ξ₀ ⤳ GlobalTheory.CompanionTheory.Ar.centre (z ≫ h) := by
    have h2 := (hgen (GlobalTheory.CompanionTheory.Ar.centre z)).map h.continuous
    have e1 : h (GlobalTheory.CompanionTheory.Ar.genPt ξ) = GlobalTheory.CompanionTheory.Ar.genPt ξ₀ := by
      have hh := congrArg (fun f => f (IsLocalRing.closedPoint Ω)) hdom
      simp only [Scheme.Hom.comp_apply] at hh
      exact hh.trans (congrArg ξ₀ (hpt _ _))
    have e2 : h (GlobalTheory.CompanionTheory.Ar.centre z) = GlobalTheory.CompanionTheory.Ar.centre (z ≫ h) :=
      (Scheme.Hom.comp_apply z h _).symm
    rw [← e1, ← e2]
    exact h2
  unfold GlobalTheory.CompanionTheory.Ar.CoordsAt at hw ⊢
  obtain ⟨hw1, hw2⟩ := hw
  refine ⟨fun k => ?_, fun k c hc => ?_⟩
  · obtain ⟨c', hc'⟩ := hw1 (bk k)
    refine ⟨(bx k).symm c', ?_⟩
    simpa [GlobalTheory.CompanionTheory.Ar.Chg.blkV] using hc'
  · simp only [GlobalTheory.CompanionTheory.Ar.Chg.blkV] at hc ⊢
    obtain ⟨hyne, hrat⟩ := hw2 (bk k) (bx k c) hc
    have hy0c : y₀ ⟨k, c⟩ ≠ 0 := fun h0 => hyne (by rw [hy, h0, map_zero])
    refine ⟨hy0c, fun j => ?_⟩
    obtain ⟨c', hc'0, hc'reg⟩ := htie.cover ⟨GlobalTheory.CompanionTheory.Ar.centre (z ≫ h), hsp⟩
    dsimp only at hc'0 hc'reg
    have hprod : ∀ c'' : (k' : K₀) → J₀ k', (∏ k', y₀ ⟨k', c'' k'⟩) =
        y₀ ⟨k, c'' k⟩ * ∏ k' ∈ ({k}ᶜ : Finset K₀), y₀ ⟨k', c'' k'⟩ :=
      fun c'' => Fintype.prod_eq_mul_prod_compl k _
    have hQ : ∏ k' ∈ ({k}ᶜ : Finset K₀), y₀ ⟨k', c' k'⟩ ≠ 0 := by
      intro h0
      apply hc'0
      rw [hprod c', h0, mul_zero]
    have hd : y₀ ⟨k, c' k⟩ ≠ 0 := by
      intro h0
      apply hc'0
      rw [hprod c', h0, zero_mul]
    have hrat0 : ∀ j' : J₀ k, y₀ ⟨k, j'⟩ / y₀ ⟨k, c' k⟩ ∈
        GlobalTheory.CompanionTheory.Ar.regAt ξ₀ ⟨GlobalTheory.CompanionTheory.Ar.centre (z ≫ h), hsp⟩ := by
      intro j'
      have hm := hc'reg (Function.update c' k j')
      have hrest : ∏ k' ∈ ({k}ᶜ : Finset K₀), y₀ ⟨k', Function.update c' k j' k'⟩ =
          ∏ k' ∈ ({k}ᶜ : Finset K₀), y₀ ⟨k', c' k'⟩ := by
        apply Finset.prod_congr rfl
        intro k' hk'
        rw [Function.update_of_ne (by simpa using hk')]
      rw [hprod (Function.update c' k j'), hprod c', hrest, Function.update_self,
        mul_div_mul_right _ _ hQ] at hm
      exact hm
    obtain ⟨sj, hsj⟩ := RingHom.mem_range.mp (hrat0 j)
    obtain ⟨sc, hsc⟩ := RingHom.mem_range.mp (hrat0 c)
    have hvalc : GlobalTheory.CompanionTheory.Ar.ValAt ξ₀ (z ≫ h) (y₀ ⟨k, c⟩ / y₀ ⟨k, c' k⟩)
        ((Scheme.stalkClosedPointTo (z ≫ h)).hom sc) := ⟨hsp, sc, hsc, rfl⟩
    have hvalc' := hval z _ _ hvalc
    obtain ⟨rd, hrd, -⟩ := hrat (bx k (c' k))
    rw [hy, hy, ← map_div₀] at hrd
    obtain ⟨hprodv, hone⟩ := valAt_mul_lemma_2 ξ z hvalc' hrd
    rw [← map_mul, div_mul_div_comm, mul_comm (y₀ ⟨k, c⟩), div_self (mul_ne_zero hd hy0c),
      map_one] at hprodv
    have h1 := valAt_unique_lemma ξ z hprodv hone
    have hv : (Scheme.stalkClosedPointTo (z ≫ h)).hom sc ≠ 0 := left_ne_zero_of_mul_eq_one h1
    have hunit : IsUnit sc := (Scheme.isLocalHom_stalkClosedPointTo (z ≫ h)).map_nonunit _ (Ne.isUnit hv)
    let sci : X₀.presheaf.stalk (↑(⟨GlobalTheory.CompanionTheory.Ar.centre (z ≫ h), hsp⟩ : GlobalTheory.CompanionTheory.Ar.Cpt ξ₀)) :=
      ↑hunit.unit⁻¹
    have hsci : sci * sc = 1 := by
      have hinv := hunit.unit.inv_mul
      rw [IsUnit.unit_spec] at hinv
      exact hinv
    have hgsci : GlobalTheory.CompanionTheory.Ar.genMap ξ₀ ⟨GlobalTheory.CompanionTheory.Ar.centre (z ≫ h), hsp⟩ sci *
        (y₀ ⟨k, c⟩ / y₀ ⟨k, c' k⟩) = 1 := by
      rw [← hsc, ← map_mul, hsci, map_one]
    have hs₀ : GlobalTheory.CompanionTheory.Ar.genMap ξ₀ ⟨GlobalTheory.CompanionTheory.Ar.centre (z ≫ h), hsp⟩ (sj * sci) =
        y₀ ⟨k, j⟩ / y₀ ⟨k, c⟩ := by
      rw [map_mul, hsj, eq_inv_of_mul_eq_one_left hgsci]
      field_simp
    have hex : GlobalTheory.CompanionTheory.Ar.ValAt ξ₀ (z ≫ h) (y₀ ⟨k, j⟩ / y₀ ⟨k, c⟩)
        ((Scheme.stalkClosedPointTo (z ≫ h)).hom (sj * sci)) := ⟨hsp, _, hs₀, rfl⟩
    have hex' := hval z _ _ hex
    obtain ⟨r, hr, hwr⟩ := hrat (bx k j)
    rw [hy, hy, ← map_div₀] at hr
    have hrr := valAt_unique_lemma ξ z hr hex'
    refine ⟨r, ?_, hwr⟩
    rw [hrr]
    exact hex

end GlobalTheory.CompanionTheory.Ar.Chg
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.DominatingRegularPush
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar
open ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P GlobalTheory.CompanionTheory.Ar.PB GlobalTheory.CompanionTheory.Ar.Chg
open ReciprocityTheory.ChartRestriction.G.AI.I1 (IsBlockMap pullDeg)
open ReciprocityTheory.ChartRestriction.G.AI.I4 (imageZ IsPullHerm)
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Inter (pullHerm)

namespace GlobalTheory.CompanionTheory.Ar.Chg.Stalk

theorem regular_along_dominant : ∀ (X X₀ : Scheme.{0}) (Ω Ω₀ : Type) [Field Ω] [Field Ω₀] (ξ : Spec (CommRingCat.of Ω) ⟶ X) (ξ₀ : Spec (CommRingCat.of Ω₀) ⟶ X₀) (h : X ⟶ X₀) (i : Ω₀ →+* Ω) (hd : GlobalTheory.CompanionTheory.Ar.Dominates ξ ξ₀ h i), IsCptGen ξ → (∀ (p : Cpt ξ) (a : Ω₀), a ∈ regAt ξ₀ (pushCpt hd p) → i a ∈ regAt ξ p) ∧ (∀ (p : Cpt ξ) (a : Ω₀), a ∈ regAt ξ₀ (pushCpt hd p) → unitAt ξ p (i a) → unitAt ξ₀ (pushCpt hd p) a) ∧ (∀ (z : Spec (CommRingCat.of ℂ) ⟶ X) (a : Ω₀) (r : ℂ), genPt ξ ⤳ centre z → ValAt ξ₀ (z ≫ h) a r → ValAt ξ z (i a) r) := by
  intro X X₀ Ω Ω₀ _ _ ξ ξ₀ h i hd hc
  refine ⟨fun p a ha => ?_, fun p a ha hu => ?_, fun z a r hz hv => ?_⟩
  · obtain ⟨hh, h1, -⟩ := GlobalTheory.CompanionTheory.Ar.RegAtDom.regAt_dominates X₀ Ω₀ ξ₀ X Ω ξ h i hd p
    exact h1 a ha
  · obtain ⟨hh, -, h2⟩ := GlobalTheory.CompanionTheory.Ar.RegAtDom.regAt_dominates X₀ Ω₀ ξ₀ X Ω ξ h i hd p
    exact h2 hc a ha hu
  · obtain ⟨h0, s, hs1, hs2⟩ := hv
    refine ⟨hz, (Scheme.Hom.stalkMap h (centre z)).hom s, ?_, ?_⟩
    · rw [GlobalTheory.CompanionTheory.Ar.RegAtDom.genMap_stalkMap hd (centre z) hz h0 s]
      exact congrArg i hs1
    · rw [Scheme.stalkClosedPointTo_comp] at hs2
      rw [← hs2]
      rfl

end GlobalTheory.CompanionTheory.Ar.Chg.Stalk
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.ExistsChartFamilyOf
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField Matrix Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi
open GroundTheory.Heights₂.Heights.LowerBoundFree GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp GlobalTheory.CompanionTheory.Ar.Cusp.FamEx

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Cusp.FamEx.ChartHol

open Opposite ReciprocityTheory.ChartRestriction.G.TB.ValAt GlobalTheory.HolHom GlobalTheory.CompanionTheory.Ar.RootHt.ArchB

variable {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V] {X : Scheme.{0}}

theorem diffOn_div {f g : V → ℂ} {s : Set V} (hf : DifferentiableOn ℂ f s) (hg : DifferentiableOn ℂ g s)
    (h0 : ∀ b ∈ s, g b ≠ 0) : DifferentiableOn ℂ (fun b => f b / g b) s :=
  (hf.mul (hg.inv h0)).congr fun b _ => by simp [div_eq_mul_inv]

theorem holAt_of_isAffineOpen {N : Set V} {c : V → (Sp ℂ ⟶ X)} {A : X.Opens} (hA : IsAffineOpen A) (hN : IsOpen N)
    (hin : ∀ b ∈ N, ⊤ ≤ c b ⁻¹ᵁ A) (hz : ∀ r : Γ(X, A), DifferentiableOn ℂ (fun b => valAt' (c b) A r) N)
    {b₀ : V} (hb₀ : b₀ ∈ N) : HolAt c b₀ := by
  intro U hU
  have hmU : (c b₀) (default : PrimeSpectrum ℂ) ∈ U := (le_preimage_iff _ _).1 hU
  have hmA : (c b₀) (default : PrimeSpectrum ℂ) ∈ A := (le_preimage_iff _ _).1 (hin b₀ hb₀)
  obtain ⟨r, hrU, hr0⟩ := hA.exists_basicOpen_le (V := U) ⟨_, hmU⟩ hmA
  set M := {b ∈ N | valAt' (c b) A r ≠ 0} with hMdef
  have hMo : IsOpen M := (hz r).continuousOn.isOpen_inter_preimage hN isOpen_ne
  have hD : ∀ b ∈ M, ⊤ ≤ c b ⁻¹ᵁ X.basicOpen r := fun b hb =>
    (le_basicOpen_iff (c b) (hin b hb.1) r).2 hb.2
  have hb0M : b₀ ∈ M := ⟨hb₀, (le_basicOpen_iff (c b₀) (hin b₀ hb₀) r).1 ((le_preimage_iff _ _).2 hr0)⟩
  refine ⟨?_, fun f => ?_⟩
  · filter_upwards [hMo.mem_nhds hb0M] with b hb
    exact (hD b hb).trans (Scheme.Hom.preimage_mono _ hrU)
  · haveI := hA.isLocalization_basicOpen r
    obtain ⟨⟨hh, s⟩, hk⟩ := IsLocalization.surj (Submonoid.powers r) (X.presheaf.map (homOfLE hrU).op f)
    obtain ⟨k, hks⟩ := s.2
    dsimp only at hk
    have hval : ∀ b ∈ M, valAt' (c b) U f * valAt' (c b) A r ^ k = valAt' (c b) A hh := by
      intro b hb
      have e := congrArg (valAt' (c b) (X.basicOpen r)) hk
      rw [valAt'_mul, ReciprocityTheory.ChartRestriction.G.TB.ValAt.valAt'_res (c b) hrU (hD b hb)] at e
      have e2 : ∀ x : Γ(X, A), valAt' (c b) (X.basicOpen r) (algebraMap Γ(X, A) Γ(X, X.basicOpen r) x) =
          valAt' (c b) A x := fun x => ReciprocityTheory.ChartRestriction.G.TB.ValAt.valAt'_res (c b) (X.basicOpen_le r) (hD b hb) x
      rw [e2, e2, ← hks] at e
      have e3 : valAt' (c b) A (r ^ k) = valAt' (c b) A r ^ k := map_pow (valHom (c b) A (hin b hb.1)) r k
      rw [e3] at e
      exact e
    have h1 : DifferentiableOn ℂ (fun b => valAt' (c b) A hh) M := (hz hh).mono fun b (hb : b ∈ M) => hb.1
    have h2 : DifferentiableOn ℂ (fun b => valAt' (c b) A r) M := (hz r).mono fun b (hb : b ∈ M) => hb.1
    have h3 : DifferentiableOn ℂ (fun b => valAt' (c b) A hh / valAt' (c b) A r ^ k) M :=
      diffOn_div h1 (h2.fun_pow k) fun b hb => pow_ne_zero _ hb.2
    refine ((h3.congr fun b hb => ?_).differentiableAt (hMo.mem_nhds hb0M))
    rw [eq_div_iff (pow_ne_zero _ hb.2)]
    exact hval b hb

variable {Ω : Type} [Field Ω] {ξ : Spec (CommRingCat.of Ω) ⟶ X} {K : Type} [Fintype K] {J : K → Type}
  {y : (Σ k, J k) → Ω}

theorem genMap_germ {A : X.Opens} (hg : genPt ξ ∈ A) (q : Cpt ξ) (hq : q.1 ∈ A) (r : Γ(X, A)) :
    genMap ξ q (X.presheaf.germ A q.1 hq r) =
      (X.presheaf.germ A (genPt ξ) hg ≫ Scheme.stalkClosedPointTo ξ).hom r := by
  have h1 := X.presheaf.germ_stalkSpecializes (U := A) (y := q.1) hq q.2
  have h3 : X.presheaf.germ A q.1 hq ≫ (X.presheaf.stalkSpecializes q.2 ≫ Scheme.stalkClosedPointTo ξ) =
      X.presheaf.germ A (genPt ξ) hg ≫ Scheme.stalkClosedPointTo ξ :=
    (Category.assoc _ _ _).symm.trans (congrArg (· ≫ Scheme.stalkClosedPointTo ξ) h1)
  exact congrArg (fun f => f.hom r) h3

theorem valAt_section (hall : ∀ q : X, genPt ξ ⤳ q) {A : X.Opens} (hg : genPt ξ ∈ A) (r : Γ(X, A))
    {z : Sp ℂ ⟶ X} (hz : ⊤ ≤ z ⁻¹ᵁ A) :
    ValAt ξ z ((X.presheaf.germ A (genPt ξ) hg ≫ Scheme.stalkClosedPointTo ξ).hom r) (valAt' z A r) := by
  have hc : centre z ∈ A := (le_preimage_iff z A).1 hz
  refine ⟨hall _, X.presheaf.germ A (centre z) hc r, genMap_germ hg ⟨centre z, hall _⟩ hc r, ?_⟩
  rw [valAt'_of _ _ hz]
  exact congrArg (fun φ => φ.hom r) (GlobalTheory.Points.germ_stalkClosedPointTo_eq_valMap z A hz)

theorem exists_hol_value (hall : ∀ q : X, genPt ξ ⤳ q) {N : Set V} {β : V → (Σ k, J k) → ℂ} {ζ : V → (Sp ℂ ⟶ X)}
    (c : (k : K) → J k) (hβ : ∀ p, DifferentiableOn ℂ (fun b => β b p) N)
    (hco : ∀ b ∈ N, CoordsAt ξ y (ζ b) (β b)) (hne : ∀ b ∈ N, ∀ k, β b ⟨k, c k⟩ ≠ 0) {a : Ω}
    (ha : a ∈ Algebra.adjoin ℤ (Set.range fun j : (k : K) → J k => (∏ k, y ⟨k, j k⟩) / ∏ k, y ⟨k, c k⟩)) :
    ∃ F : V → ℂ, DifferentiableOn ℂ F N ∧ ∀ b ∈ N, ValAt ξ (ζ b) a (F b) := by
  induction ha using Algebra.adjoin_induction with
  | mem a ha =>
    obtain ⟨j, rfl⟩ := ha
    refine ⟨fun b => ∏ k, β b ⟨k, j k⟩ / β b ⟨k, c k⟩, ?_, fun b hb => ?_⟩
    · have hS : ∀ S : Finset K, DifferentiableOn ℂ (fun b => ∏ k ∈ S, β b ⟨k, j k⟩ / β b ⟨k, c k⟩) N := by
        classical
        intro S
        induction S using Finset.induction_on with
        | empty => simpa using differentiableOn_const (c := (1 : ℂ))
        | insert k S hk ih =>
          simp only [Finset.prod_insert hk]
          exact (diffOn_div (hβ _) (hβ _) fun b hb => hne b hb k).fun_mul ih
      exact hS _
    · simp only [← Finset.prod_div_distrib]
      have hS : ∀ S : Finset K, ValAt ξ (ζ b) (∏ k ∈ S, y ⟨k, j k⟩ / y ⟨k, c k⟩)
          (∏ k ∈ S, β b ⟨k, j k⟩ / β b ⟨k, c k⟩) := by
        classical
        intro S
        induction S using Finset.induction_on with
        | empty => simpa using val_one (ξ := ξ) (z := ζ b) (hall _)
        | insert k S hk ih =>
          rw [Finset.prod_insert hk, Finset.prod_insert hk]
          refine val_mul ?_ ih
          obtain ⟨r, hr, hr'⟩ := ((hco b hb).2 k (c k) (isUnit_iff_ne_zero.2 (hne b hb k))).2 (j k)
          rwa [hr', mul_div_cancel_right₀ _ (hne b hb k)]
      exact hS _
  | algebraMap n =>
    refine ⟨fun _ => (n : ℂ), differentiableOn_const _, fun b _ => ?_⟩
    exact ⟨hall _, (n : X.presheaf.stalk (centre (ζ b))), by simp, map_intCast _ n⟩
  | add a a' _ _ h h' =>
    obtain ⟨F, hF, hv⟩ := h
    obtain ⟨F', hF', hv'⟩ := h'
    exact ⟨fun b => F b + F' b, hF.fun_add hF', fun b hb => val_add (hv b hb) (hv' b hb)⟩
  | mul a a' _ _ h h' =>
    obtain ⟨F, hF, hv⟩ := h
    obtain ⟨F', hF', hv'⟩ := h'
    exact ⟨fun b => F b * F' b, hF.fun_mul hF', fun b hb => val_mul (hv b hb) (hv' b hb)⟩

theorem isHolTo_of_coordsAt (htie : CoordTie ℤ ξ (fun c' : (k : K) → J k => ∏ k, y ⟨k, c' k⟩))
    (hall : ∀ q : X, genPt ξ ⤳ q) {B : Set V} {β : V → (Σ k, J k) → ℂ} {ζ : V → (Sp ℂ ⟶ X)} (hB : IsOpen B)
    (hβ : ∀ p, DifferentiableOn ℂ (fun b => β b p) B) (hco : ∀ b ∈ B, CoordsAt ξ y (ζ b) (β b)) :
    IsHolTo B ζ := by
  refine isHolTo_of_holAt hB fun b₁ hb₁ => ?_
  choose c hc using (hco b₁ hb₁).1
  set N := {b ∈ B | ∀ k, β b ⟨k, c k⟩ ≠ 0} with hNdef
  have hNB : N ⊆ B := fun b hb => hb.1
  have hNo : IsOpen N := by
    refine isOpen_iff_mem_nhds.2 fun b hb => ?_
    have hk : ∀ᶠ t in 𝓝 b, ∀ k, β t ⟨k, c k⟩ ≠ 0 := eventually_all.2 fun k =>
      ((hβ _).continuousOn.continuousAt (hB.mem_nhds hb.1)).eventually_ne (hb.2 k)
    filter_upwards [hB.mem_nhds hb.1, hk] with t h1 h2 using ⟨h1, h2⟩
  have hb₁N : b₁ ∈ N := ⟨hb₁, fun k => (hc k).ne_zero⟩
  have hx0 : (∏ k, y ⟨k, c k⟩) ≠ 0 :=
    Finset.prod_ne_zero_iff.2 fun k _ => ((hco b₁ hb₁).2 k (c k) (hc k)).1
  obtain ⟨A, hA, hAq⟩ := htie.affine c hx0
  have hin : ∀ b ∈ N, ⊤ ≤ ζ b ⁻¹ᵁ A := fun b hb =>
    (le_preimage_iff _ _).2 ((hAq _).2 ⟨hall _, in_chart (hall _) (hco b hb.1) hb.2⟩)
  have hg : genPt ξ ∈ A := (hall _).mem_open A.2 ((le_preimage_iff _ _).1 (hin b₁ hb₁N))
  refine holAt_of_isAffineOpen hA hNo hin (fun r => ?_) hb₁N
  have ha := (htie.ring c hx0 ((X.presheaf.germ A (genPt ξ) hg ≫ Scheme.stalkClosedPointTo ξ).hom r)).2
    fun p hp => ⟨_, genMap_germ hg p ((hAq _).2 ⟨p.2, hp⟩) r⟩
  obtain ⟨F, hF, hFv⟩ := exists_hol_value hall c (fun p => (hβ p).mono hNB) (fun b hb => hco b hb.1)
    (fun b hb => hb.2) ha
  refine hF.congr fun b hb => ?_
  exact val_unique htie.gen (valAt_section hall hg r (hin b hb)) (hFv b hb)

end GlobalTheory.CompanionTheory.Ar.Cusp.FamEx.ChartHol
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.ExistsCocharacterLieModel
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.TorusLie

variable {S : Scheme.{0}} {X : Type} [AddCommGroup X] {R : Type} [CommRing R]

def pullPt {A A' : Type} [CommRing A] [CommRing A'] (g : A →+* A') {a : Sp A ⟶ S} {a' : Sp A' ⟶ S}
    (h : a' = spMap g ≫ a) (t : Over.mk a ⟶ splitTorus S X) : Over.mk a' ⟶ splitTorus S X :=
  Over.homMk (spMap g ≫ t.left) (by
    have h1 := Over.w t
    simp only [Over.mk_hom] at h1 ⊢
    rw [Category.assoc, h1, h])

theorem charVal_pullPt {A A' : Type} [CommRing A] [CommRing A'] (g : A →+* A') {a : Sp A ⟶ S}
    {a' : Sp A' ⟶ S} (h : a' = spMap g ≫ a) (t : Over.mk a ⟶ splitTorus S X) (χ : X) :
    charVal (pullPt g h t) χ = g (charVal t χ) := by
  subst h
  exact (_root_.GlobalTheory.CompanionTheory.Ar.TorusPoints.main S X A _).2.2.2.2.2 A' g t _ rfl χ

def wOf (δ : X →+ R) : Multiplicative X →* DualNumber R where
  toFun χ := TrivSqZeroExt.inl 1 + TrivSqZeroExt.inr (δ χ.toAdd)
  map_one' := by
    ext <;> simp
  map_mul' a b := by
    ext <;> simp [TrivSqZeroExt.fst_mul, TrivSqZeroExt.snd_mul, add_comm]

abbrev evZ (R : Type) [CommRing R] : DualNumber R →+* R := (TrivSqZeroExt.fstHom R R R).toRingHom

theorem base_ev (x : Sp R ⟶ S) :
    x = spMap (evZ R) ≫ Spec.map (CommRingCat.ofHom (algebraMap R (DualNumber R))) ≫ x := by
  have : spMap (evZ R) ≫ Spec.map (CommRingCat.ofHom (algebraMap R (DualNumber R))) = 𝟙 _ := by
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
    have : (evZ R).comp (algebraMap R (DualNumber R)) = RingHom.id R := by
      ext r; simp
    rw [this]; simp
  rw [← Category.assoc, this, Category.id_comp]

theorem isTanAt_iff (x : Sp R ⟶ S) (v : epsAt x ⟶ splitTorus S X) :
    IsTanAt (splitTorus S X) x v ↔ ∀ χ, (charVal v χ).fst = 1 := by
  have hT := _root_.GlobalTheory.CompanionTheory.Ar.TorusPoints.main S X
  constructor
  · intro hv χ
    have e : pullPt (evZ R) (base_ev x) v = 1 := Over.OverMorphism.ext hv
    have := charVal_pullPt (evZ R) (base_ev x) v χ
    rw [e, (hT R x).2.2.1 χ] at this
    exact this.symm
  · intro hv
    have e : pullPt (evZ R) (base_ev x) v = 1 := by
      refine (hT R x).1 _ _ fun χ => ?_
      rw [charVal_pullPt, (hT R x).2.2.1 χ]
      exact hv χ
    exact congrArg (fun t => t.left) e

def ptOf (x : Sp R ⟶ S) (δ : X →+ R) : epsAt x ⟶ splitTorus S X :=
  ((_root_.GlobalTheory.CompanionTheory.Ar.TorusPoints.main S X (DualNumber R) (Spec.map (CommRingCat.ofHom (algebraMap R (DualNumber R))) ≫ x)).2.2.2.2.1
    (wOf δ)).choose

theorem charVal_ptOf (x : Sp R ⟶ S) (δ : X →+ R) (χ : X) :
    charVal (ptOf x δ) χ = TrivSqZeroExt.inl 1 + TrivSqZeroExt.inr (δ χ) :=
  ((_root_.GlobalTheory.CompanionTheory.Ar.TorusPoints.main S X (DualNumber R) (Spec.map (CommRingCat.ofHom (algebraMap R (DualNumber R))) ≫ x)).2.2.2.2.1
    (wOf δ)).choose_spec χ

theorem ptOf_ext (x : Sp R ⟶ S) (v v' : epsAt x ⟶ splitTorus S X) (h : ∀ χ, charVal v χ = charVal v' χ) : v = v' :=
  (_root_.GlobalTheory.CompanionTheory.Ar.TorusPoints.main S X (DualNumber R) _).1 v v' h

theorem epsMul_comp_base (c : R) (x : Sp R ⟶ S) :
    Spec.map (CommRingCat.ofHom (algebraMap R (DualNumber R))) ≫ x =
      spMap (epsMul c) ≫ Spec.map (CommRingCat.ofHom (algebraMap R (DualNumber R))) ≫ x := by
  have : spMap (epsMul c) ≫ Spec.map (CommRingCat.ofHom (algebraMap R (DualNumber R))) =
      Spec.map (CommRingCat.ofHom (algebraMap R (DualNumber R))) := by
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
    have : (epsMul c).comp (algebraMap R (DualNumber R)) = algebraMap R (DualNumber R) := by
      ext r <;> simp [epsMul]
    rw [this]
  rw [← Category.assoc, this]

def deltaOf (x : Sp R ⟶ S) (v : epsAt x ⟶ splitTorus S X) (hv : ∀ χ, (charVal v χ).fst = 1) : X →+ R :=
  AddMonoidHom.mk' (fun χ => (charVal v χ).snd) (fun χ χ' => by
    have := ((_root_.GlobalTheory.CompanionTheory.Ar.TorusPoints.main S X (DualNumber R) _).2.2.2.1 v).2 χ χ'
    simp [this, TrivSqZeroExt.snd_mul, hv, add_comm])

theorem exists_lieModel_splitTorus : ∀ (S : Scheme.{0}) (X : Type) [AddCommGroup X] (R : Type) [CommRing R]
    (x : Sp R ⟶ S), ∃ M : LieModel (splitTorus S X) x (X →+ R), IsCocharLie M := by
  intro S X _ R _ x
  refine ⟨{ pt := ptOf x, tan := ?_, inj := ?_, onto := ?_, add := ?_, smul := ?_ },
    fun δ χ => charVal_ptOf x δ χ⟩
  · intro δ
    refine (isTanAt_iff x _).2 fun χ => ?_
    rw [charVal_ptOf]; simp
  · intro δ δ' h
    ext χ
    have := congrArg TrivSqZeroExt.snd
      ((charVal_ptOf x δ χ).symm.trans ((congrArg (fun t => charVal t χ) h).trans (charVal_ptOf x δ' χ)))
    simpa using this
  · intro v hv
    have hv' := (isTanAt_iff x v).1 hv
    refine ⟨deltaOf x v hv', ptOf_ext x _ _ fun χ => ?_⟩
    rw [charVal_ptOf]
    ext
    · simp [hv']
    · simp [deltaOf]
  · intro δ δ'
    refine ptOf_ext x _ _ fun χ => ?_
    rw [(_root_.GlobalTheory.CompanionTheory.Ar.TorusPoints.main S X (DualNumber R) _).2.1, charVal_ptOf, charVal_ptOf, charVal_ptOf]
    ext <;> simp [TrivSqZeroExt.fst_mul, TrivSqZeroExt.snd_mul, add_comm]
  · intro c δ
    have e : ptOf x (c • δ) = pullPt (epsMul c) (epsMul_comp_base c x) (ptOf x δ) := by
      refine ptOf_ext x _ _ fun χ => ?_
      rw [charVal_pullPt, charVal_ptOf, charVal_ptOf]
      ext <;> simp [epsMul, mul_comm]
    exact congrArg (fun t => t.left) e

end GlobalTheory.CompanionTheory.Ar.TorusLie
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.LabelEmbeddingInjectiveStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.label_embedding_injective : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (l : Geo.Tor.Level H) (c : Coeff l), Function.Injective (labelEmb (H := H) c) ∧ Nat.card (CMType H ⊕ CMType H) = Module.finrank ℚ E := by
  first | exact @GlobalTheory.CompanionTheory.Ar.labels_all_once | exact GlobalTheory.CompanionTheory.Ar.labels_all_once | (intros; apply GlobalTheory.CompanionTheory.Ar.labels_all_once <;> assumption)
end

