module

public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0677
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0374
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0047
public import Mathlib
public import Development.AutomorphicArithmetic.CharacterBoxes.Bundle0006
public import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.Bundle0007
public import Formalism.SharpRestriction.GlobalSchurBounds.LinkTied
public import Formalism.SharpRestriction.GlobalSchurBounds.MainSup
public import Formalism.LocalToGlobal.GroupLattices.AdmissibleAtGeneratorPlaces
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.WuDecayAll
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.Bundle0005
public import Formalism.LocalToGlobal.GlobalTheory.GL5.Bundle0001
public import Formalism.LocalToGlobal.GlobalTheory.GL5.DiscreteSeriesOfFormalDegree
public import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.Bundle0008
public import Formalism.LocalToGlobal.FiniteTOf
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0043
public import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.ColumnCompatibleSelection
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.STiesR
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0016
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.DivisionPairOfAdelicFormsFaceColumnsData
public import Formalism.LocalToGlobal.Bundle0002
public import Formalism.LocalToGlobal.Bundle0001
public import Formalism.LocalToGlobal.IndefiniteReal.DoubleCosetOperators.TwistedCharacterValue
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.TwArgs
public import Formalism.LocalToGlobal.Divisibility.Bundle0007
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0052
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0055
public import Formalism.LocalToGlobal.IndefiniteReal.Bundle0031
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ClassSumPin
public import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.SingleIndexPlacesAreTwisted
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0070
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.SerFixOne
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0041
public import Development.AbelianVarietyTheory.Statements.CuspidalUnitaryTwists.ExistsSmallSpherical
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0044
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0673
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0045
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.SettingsFormsExistList
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.PlaceModelImp
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0669
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.NonemptyPtsOfReading
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0528
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0889
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0033
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.StandardLatticesDiagonal
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0378
public import Formalism.LocalToGlobal.IndefiniteReal.Bundle0027
public import Formalism.LocalToGlobal.Columns.MtAdWt
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ContinuousCoeffBlockAct
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0786

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.GoodPlacesAllStates
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
open Formalism.AUTREP (GAf)
open Neutral.B1 (Ideles)
open GlobalTheory.HeckeGal (Gab IsGlobalArtin)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1000000
open GlobalTheory.LevCmp
open GlobalTheory.TwistChoice (Reading ReadsAt)

noncomputable section

namespace GlobalTheory.TypePlacesCover

variable {D : D7}

theorem isConjPl_conjPlE (P : PlE D.host) : Formalism.BasicNotions.IsConjPl D.host P (GlobalTheory.SplitConjPlace.conjPlE (D := D) P) := by
  intro x y hxy
  rw [GlobalTheory.SplitConjPlace.mem_conjPlE (D := D)]
  have : IsCMField.ringOfIntegersComplexConj D.host.E y = x := by
    apply RingOfIntegers.ext
    rw [IsCMField.coe_ringOfIntegersComplexConj, hxy]
    show IsCMField.complexConj D.host.E (D.host.conj (x : D.host.E)) = _
    have h : D.host.conj (x : D.host.E) = IsCMField.complexConj D.host.E (x : D.host.E) :=
      D.host.φ₀.injective (by
        rw [NumberField.IsCMField.complexEmbedding_complexConj, Formalism.HC.HostAx.conjE_apply])
    rw [h]; exact IsCMField.complexConj_apply_apply D.host.E _
  rw [this]

theorem conjPlE_conjPlE (P : PlE D.host) : GlobalTheory.SplitConjPlace.conjPlE (D := D) (GlobalTheory.SplitConjPlace.conjPlE (D := D) P) = P := by
  refine HeightOneSpectrum.ext (Ideal.ext fun x => ?_)
  rw [GlobalTheory.SplitConjPlace.mem_conjPlE (D := D), GlobalTheory.SplitConjPlace.mem_conjPlE (D := D), GlobalTheory.SplitConjPlace.cO_cO (D := D)]

theorem comap_conjPlE (P : PlE D.host) :
    (GlobalTheory.SplitConjPlace.conjPlE (D := D) P).asIdeal.comap (algebraMap (𝓞 (maximalRealSubfield D.host.E)) (𝓞 D.host.E)) =
      P.asIdeal.comap (algebraMap (𝓞 (maximalRealSubfield D.host.E)) (𝓞 D.host.E)) := by
  ext a
  rw [Ideal.mem_comap, Ideal.mem_comap, GlobalTheory.SplitConjPlace.mem_conjPlE (D := D), GlobalTheory.SplitConjPlace.cO_algebraMap (D := D)]

theorem finrank_E (D : D7) : Module.finrank ℚ D.host.E = 2 * D.R.f := by
  have h1 : Module.finrank ℚ D.host.E = 4 * D.R.ord := D.host.finrank_cmField
  have h5 : D.R.f = 2 * D.R.ord := rfl
  rw [h1, h5]; ring

theorem cover (k : Fin 2) (w : PlE D.host) (hw : ((D.host.g k : ℕ) : 𝓞 D.host.E) ∈ w.asIdeal) :
    ∃ v, w = D.naut.plGw k v ∨ w = GlobalTheory.SplitConjPlace.conjPlE (D := D) (D.naut.plGw k v) := by
  let T : Set (PlE D.host) := {u | ((D.host.g k : ℕ) : 𝓞 D.host.E) ∈ u.asIdeal}
  have hg : ∀ v, ((D.host.g k : ℕ) : 𝓞 D.host.E) ∈ (D.naut.plGw k v).asIdeal := fun v => D.naut.plGw_over k v
  let f : D.nd.PlG k ⊕ D.nd.PlG k → T :=
    Sum.elim (fun v => ⟨D.naut.plGw k v, hg v⟩) fun v => ⟨GlobalTheory.SplitConjPlace.conjPlE (D := D) (D.naut.plGw k v), by
      show _ ∈ (GlobalTheory.SplitConjPlace.conjPlE (D := D) _).asIdeal
      rw [GlobalTheory.SplitConjPlace.mem_conjPlE (D := D), map_natCast]; exact hg v⟩
  have hne : ∀ a b, D.naut.plGw k a ≠ GlobalTheory.SplitConjPlace.conjPlE (D := D) (D.naut.plGw k b) := fun a b e =>
    D.naut.plGw_nconj k b a (e ▸ isConjPl_conjPlE _)
  have hinj : Function.Injective f := by
    rintro (a | a) (b | b) e <;> have e' := congrArg Subtype.val e
    · exact congrArg Sum.inl (D.naut.plGw_inj k e')
    · exact absurd e' (hne a b)
    · exact absurd e'.symm (hne b a)
    · have := congrArg (GlobalTheory.SplitConjPlace.conjPlE (D := D)) e'
      simp only [f, Sum.elim_inr, conjPlE_conjPlE] at this
      exact congrArg Sum.inr (D.naut.plGw_inj k this)
  have hT : T.ncard = 2 * D.R.f := by
    rw [← finrank_E D]; exact D.nd.g_split k
  have hc : Nat.card T = Nat.card (D.nd.PlG k ⊕ D.nd.PlG k) := by
    rw [Nat.card_coe_set_eq, hT, Nat.card_sum, Nat.card_eq_fintype_card, D.nd.card_PlG k, two_mul]
  haveI : Finite T := by
    refine Nat.finite_of_card_ne_zero ?_
    rw [Nat.card_coe_set_eq, hT]
    have : 0 < D.R.f := by show 0 < 2 * D.R.ord; exact Nat.mul_pos two_pos D.R.ord_pos
    omega
  obtain ⟨x, hx⟩ := ((Nat.bijective_iff_injective_and_card f).2 ⟨hinj, hc.symm⟩).2 ⟨w, hw⟩
  rcases x with v | v
  · exact ⟨v, Or.inl (congrArg Subtype.val hx).symm⟩
  · exact ⟨v, Or.inr (congrArg Subtype.val hx).symm⟩


open GlobalTheory.LevCmp in
theorem gPlaces (D : D7) : GPlaces D := by
  refine ⟨fun k v => ⟨D.naut.plGw_over k v, GlobalTheory.SplitPlaceOfFixed.exists_splitPlace_plGw D ⟨k, v⟩⟩, ?_, ?_⟩
  · rintro u ⟨w, hwu, k, hwk⟩
    obtain ⟨v, hv⟩ := cover k w hwk
    obtain ⟨s, hs⟩ := GlobalTheory.SplitPlaceOfFixed.exists_splitPlace_plGw D ⟨k, v⟩
    refine ⟨k, v, s, HeightOneSpectrum.ext ?_, hs⟩
    have hu : u.asIdeal = (D.naut.plGw k v).asIdeal.comap (algebraMap (𝓞 (maximalRealSubfield D.host.E)) (𝓞 D.host.E)) := by
      rw [← hwu]
      rcases hv with rfl | rfl
      · rfl
      · exact comap_conjPlE _
    rw [hu, ← s.w_under, hs]
  · refine ⟨0, ?_⟩
    rw [← Fintype.card_pos_iff, D.nd.card_PlG 0]
    show 0 < 2 * D.R.ord; exact Nat.mul_pos two_pos D.R.ord_pos

end GlobalTheory.TypePlacesCover


end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.GridExistenceOfPieces
section
open Formalism.BasicNotions Formalism.MainNotions GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Fc GlobalTheory.RowEx GlobalTheory.Mem.LiteralAutomorphy
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim
open Formalism.L2.Host (HChar)
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

noncomputable section

namespace GlobalTheory.Mem.LiteralAutomorphy

theorem gridKey_heq_of_eq_preData_components (P P' : Pre) (h : P = P') (v : Pl P.host.F) (v' : Pl P'.host.F) (w : Pl P.host.F → Pl P.host.E)
    (w' : Pl P'.host.F → Pl P'.host.E) (c : ℕ → HChar P.host.E) (c' : ℕ → HChar P'.host.E) (hv : HEq v v') (hw : HEq w w')
    (hc : HEq c c') :
    HEq ((v, w v, fun a : Fin P.R.m => c (a.1 + 1)) : GKey P) ((v', w' v', fun a : Fin P'.R.m => c' (a.1 + 1)) : GKey P') := by
  subst h; subst hv; subst hw; subst hc; rfl

theorem gkeyOf_heq {X X' : Stages} {T T' : Type} {L : Formalism.IndefR.Links.LevCh X.toD7 T} {L' : Formalism.IndefR.Links.LevCh X'.toD7 T'} {sc : GlobalTheory.ChiGrid.Consts}
    {G : GridData L sc} {G' : GridData L' sc} (h : GAgree G G') (hp : X'.B.toPre = X.B.toPre) : HEq (gkeyOf G') (gkeyOf G) :=
  gridKey_heq_of_eq_preData_components _ _ hp _ _ _ _ _ _ h.v0 h.w h.chiH

end GlobalTheory.Mem.LiteralAutomorphy

namespace GlobalTheory.Mem.LiteralAutomorphy


set_option maxHeartbeats 3200000 in
theorem exGrid_of : WeilEx → IsEx → NFAll → NFSq → CarryG → CarryW → CarryS → TrEasy → TrPhase → TrJet → TrBot → TrSq → KeyFin →
    GKeyFin → ExGrid := by
  classical
  intro h1 h2 h3 h4 cG cW cS t1 t2 t3 t4 t5 kF gF
  obtain ⟨a1, h1⟩ := h1
  obtain ⟨a2, h2⟩ := h2
  obtain ⟨a3, h3⟩ := h3
  obtain ⟨a4, h4⟩ := h4
  refine ⟨max a1 (max a2 (max a3 a4)), fun ε CF hC => ?_⟩
  obtain ⟨x1, h1⟩ := h1 ε CF (le_of_max_le_left hC)
  obtain ⟨x2, h2⟩ := h2 ε CF (le_of_max_le_left (le_of_max_le_right hC))
  obtain ⟨x3, h3⟩ := h3 ε CF (le_of_max_le_left (le_of_max_le_right (le_of_max_le_right hC)))
  obtain ⟨x4, h4⟩ := h4 ε CF (le_of_max_le_right (le_of_max_le_right (le_of_max_le_right hC)))
  refine ⟨max x1 (max x2 (max x3 x4)), fun s he hx P f Ξ hΞ => ?_⟩
  have hx1 := le_of_max_le_left hx
  have hx2 := le_of_max_le_left (le_of_max_le_right hx)
  have hx3 := le_of_max_le_left (le_of_max_le_right (le_of_max_le_right hx))
  have hx4 := le_of_max_le_right (le_of_max_le_right (le_of_max_le_right hx))
  have per : ∀ (κ : Key P) (γ : GKey P), ∃ S : Finset ℂ, (∀ z ∈ S, IsAlgebraic ℚ z) ∧
      ∀ (X : Stages) (f' : Fr X.B.toPre), X.B.toPre = P → HEq f' f → ∀ large₂ : SizeData₂ X.toD7, large₂.sc = s → GlobalTheory.SqTop.Rec large₂ →
      ∀ (Γ : Type) [Group Γ] [Fintype Γ] (Pl0 T : Type) (A : FamIn X.toD7.what₂.LL Γ Pl0 T X.toD7.R.m) (Ks : Type) [Field Ks]
        [NumberField Ks] [Algebra Ks X.toD7.what₂.LL] (R : RealDat X.toD7 A Ks) (F : Face X.toD7 A), HidaSetting large₂ R F →
        R.C = Fr.at X f' → TwistPlacesOffPrimeQZero R.toLevCh → HEq (keyOf R.toLevCh) κ → ∀ G₀ : GridData R.toLevCh ⟨1, CF, s.b⟩,
        HEq (gkeyOf G₀) γ → (∀ z ∈ S, z ∈ Set.range X.toD7.what₂.embLL) →
        ∃ G : GridData R.toLevCh ⟨1, CF, s.b⟩, gkeyOf G = gkeyOf G₀ ∧ Full R G := by
    intro κ γ
    by_cases H : ∃ (X : Stages) (f' : Fr X.B.toPre) (_ : X.B.toPre = P) (_ : HEq f' f) (large₂ : SizeData₂ X.toD7) (_ : large₂.sc = s)
        (_ : GlobalTheory.SqTop.Rec large₂) (Γ : Type) (_ : Group Γ) (_ : Fintype Γ) (Pl0 T : Type)
        (A : FamIn X.toD7.what₂.LL Γ Pl0 T X.toD7.R.m) (Ks : Type) (_ : Field Ks) (_ : NumberField Ks)
        (_ : Algebra Ks X.toD7.what₂.LL) (R : RealDat X.toD7 A Ks) (F : Face X.toD7 A) (G₀ : GridData R.toLevCh ⟨1, CF, s.b⟩),
        HidaSetting large₂ R F ∧ R.C = Fr.at X f' ∧ TwistPlacesOffPrimeQZero R.toLevCh ∧ HEq (keyOf R.toLevCh) κ ∧ HEq (gkeyOf G₀) γ
    swap
    · exact ⟨∅, by simp, fun X f' a b large₂ c r Γ _ _ Pl0 T A Ks _ _ _ R F d e g i G₀ j _ =>
        absurd ⟨X, f', a, b, large₂, c, r, Γ, _, _, Pl0, T, A, Ks, _, _, _, R, F, G₀, d, e, g, i, j⟩ H⟩
    obtain ⟨X0, f0, a0, b0, Lg0, rfl, r0, Γ0, _, _, Pl00, T0, A0, Ks0, _, _, _, R0, F0, G00, d0, e0, g0, i0, j0⟩ := H
    obtain ⟨W0, hW0, ⟨S0⟩⟩ := h1 _ Lg0 he hx1 Γ0 Pl00 T0 A0 Ks0 R0 F0 d0 G00
    obtain ⟨M, ρ, ξ, cv, rm, S, rp, n, e, c, hS, hIs⟩ := h2 _ Lg0 he hx2 Γ0 Pl00 T0 A0 Ks0 R0 F0 d0 G00 W0 hW0 S0
    obtain ⟨N, hN, hAll⟩ := h3 _ Lg0 he hx3 Γ0 Pl00 T0 A0 Ks0 R0 F0 d0 _ hIs rfl
    obtain ⟨N2, hN2, hSq⟩ := h4 _ Lg0 he hx4 r0 T0 R0.toLevCh A0.μ0 d0.core.lev G00
    obtain ⟨b⟩ : Nonempty (Module.Basis (Fin (Module.finrank ℚ N)) ℚ N) := ⟨Module.finBasis ℚ N⟩
    obtain ⟨b2⟩ : Nonempty (Module.Basis (Fin (Module.finrank ℚ N2)) ℚ N2) := ⟨Module.finBasis ℚ N2⟩
    refine ⟨(Finset.univ.image fun i => ((b i : N) : ℂ)) ∪ Finset.univ.image fun i => ((b2 i : N2) : ℂ), ?_, ?_⟩
    · intro z hz
      rcases Finset.mem_union.1 hz with hz | hz
      · obtain ⟨i, -, rfl⟩ := Finset.mem_image.1 hz
        exact IntermediateField.isAlgebraic_iff.1 (Algebra.IsAlgebraic.isAlgebraic _)
      · obtain ⟨i, -, rfl⟩ := Finset.mem_image.1 hz
        exact IntermediateField.isAlgebraic_iff.1 (Algebra.IsAlgebraic.isAlgebraic _)
    intro X f' a b' large₂ hs hr Γ _ _ Pl0 T A Ks _ _ _ R F d e' g i G₀ j hz

    have rng : ∀ (K : IntermediateField ℚ ℂ) [FiniteDimensional ℚ K] (bK : Module.Basis (Fin (Module.finrank ℚ K)) ℚ K),
        (∀ i, ((bK i : K) : ℂ) ∈ Set.range X.toD7.what₂.embLL) → Set.range (algebraMap K ℂ) ⊆ Set.range X.toD7.what₂.embLL := by
      intro K _ bK hK
      rintro _ ⟨y, rfl⟩
      set_option synthInstance.maxHeartbeats 100000 in
        rw [← bK.sum_repr y, map_sum]
      refine X.toD7.what₂.embLL.fieldRange.sum_mem fun i _ => ?_
      rw [Rat.smul_def, map_mul, map_ratCast]
      exact X.toD7.what₂.embLL.fieldRange.mul_mem (SubfieldClass.ratCast_mem _ _) (hK i)
    have r1 := rng N b fun i => hz _ (Finset.mem_union_left _ (Finset.mem_image_of_mem _ (Finset.mem_univ i)))
    have r2 := rng N2 b2 fun i => hz _ (Finset.mem_union_right _ (Finset.mem_image_of_mem _ (Finset.mem_univ i)))
    have hk : HEq (keyOf R.toLevCh) (keyOf R0.toLevCh) := i.trans i0.symm
    have hpre : X.B.toPre = X0.B.toPre := a.trans a0.symm
    have key : ∀ (P P' : Pre) (_ : P = P') (k : Key P) (k' : Key P'), HEq k k' → ∀ x ∈ k, ∃ y ∈ k', HEq x.1 y.1 ∧ HEq x.2 y.2 := by
      rintro P _ rfl k k' h x hx
      obtain rfl := eq_of_heq h
      exact ⟨x, hx, HEq.rfl, HEq.rfl⟩
    have hι : ∀ t : T, ∃ t0 : T0, HEq (R.xiH t) (R0.xiH t0) ∧ HEq (R.Q t) (R0.Q t0) := fun t => by
      obtain ⟨_, ⟨t0, rfl⟩, h⟩ := key _ _ hpre _ _ hk _ ⟨t, rfl⟩
      exact ⟨t0, h⟩
    choose ι hι using hι
    have one : ∀ (P P' : Pre) (_ : P = P'), HEq (1 : HChar P.host.E) (1 : HChar P'.host.E) := by rintro P _ rfl; rfl
    have hb : ι A.μ0 = A0.μ0 := d0.core.lev.xi_inj (by
      rw [d0.core.lev.xi_base]
      have := (hι A.μ0).1
      rw [d.core.lev.xi_base] at this
      exact eq_of_heq (this.symm.trans (one _ _ hpre)))
    have hL : LAgree R0.toLevCh R.toLevCh A0.μ0 A.μ0 ι :=
      ⟨hpre, d0.core.lev, d.core.lev, ⟨f0, f', b'.trans b0.symm, e0, e'⟩, hb, fun t => (hι t).1, fun t => (hι t).2, d0.betaX,
        d.betaX⟩
    obtain ⟨G, hG⟩ := cG _ _ _ _ _ _ _ _ _ hL _ G00
    obtain ⟨W, hW, hWA⟩ := cW _ _ _ _ _ Γ Pl0 A Ks R _ ι hL d.core.chain d.core.models _ G00 G hG W0
    obtain ⟨S', hS'⟩ := cS _ _ _ _ _ _ _ _ _ hL _ G00 G hG W0 W hWA S.toGridChoice
    have hA : Agree S.toGridChoice S' A0.μ0 A.μ0 ι := ⟨hL, hG, hWA, hS'⟩
    have h2' := h2 _ large₂ (hs ▸ he) (hs ▸ hx2) Γ Pl0 T A Ks R F d
    rw [hs] at h2'
    obtain ⟨M', ρ', ξ', cv', rm', S2, rp', n', e2, c', hS2, hIs'⟩ := h2' G W hW S'
    have gk : gkeyOf G = gkeyOf G₀ := eq_of_heq ((gkeyOf_heq hG hpre).trans (j0.trans j.symm))
    refine ⟨G, gk, W, M', ρ', ξ', cv', rm', S2, rp', n', e2, c', hIs', ?_, ?_⟩
    · obtain ⟨u1, u2, u3⟩ := t1 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hA N (algebraMap N ℂ)
      have hAll' : AllIn (algebraMap N ℂ) S' A.μ0 := ⟨u1 hAll.chars, u2 hAll.root,
        t2 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hA N _ hAll.phase, t3 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hA N _ hAll.jet, u3 hAll.ratios,
        t4 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hA N _ hAll.bot⟩
      subst hS2
      exact hAll'.numbersIn.mono r1
    · exact (t5 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hA N2 _ hSq).mono r2
  obtain ⟨𝒦, hK, H⟩ := kF P Ξ hΞ
  obtain ⟨𝒢, hG, HG⟩ := gF P 1
  choose S hS HS using per
  refine ⟨hK.toFinset.biUnion fun κ => hG.toFinset.biUnion fun γ => S κ γ, ?_, ?_⟩
  · intro z hz
    obtain ⟨κ, -, hz⟩ := Finset.mem_biUnion.1 hz
    obtain ⟨γ, -, hz⟩ := Finset.mem_biUnion.1 hz
    exact hS κ γ z hz
  intro X f' Ξ' hP hf hΞ' hz large₂ hs hRec Γ _ _ Pl0 T A Ks _ _ _ R F st hCf ho htw G₀
  subst hP
  obtain rfl := eq_of_heq hΞ'
  obtain ⟨κ, hκ, hk⟩ := H X T R.toLevCh A.μ0 rfl st.core.lev htw
  obtain ⟨γ, hγ, hg⟩ := HG X T R.toLevCh _ G₀ rfl rfl
  exact HS κ γ X f' rfl hf large₂ hs hRec Γ Pl0 T A Ks R F st hCf ho hk G₀ hg fun z hz' =>
    hz z (Finset.mem_biUnion.2 ⟨κ, hK.mem_toFinset.2 hκ, Finset.mem_biUnion.2 ⟨γ, hG.mem_toFinset.2 hγ, hz'⟩⟩)

end GlobalTheory.Mem.LiteralAutomorphy

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HeckeCharacterSplitPlaceComponentUnique
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
open Formalism.AUTREP (GAf)
open Neutral.B1 (Ideles)
open GlobalTheory.HeckeGal (Gab IsGlobalArtin)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1000000
open GlobalTheory.LevCmp
open GlobalTheory.TwistChoice (Reading ReadsAt)

noncomputable section
namespace GlobalTheory.CompAtUniq

open Topology
open scoped WithZero

theorem ball_mem_nhds' {K : Type} [Field K] [Valued K ℤᵐ⁰] (x r : K) (hr : r ≠ 0) :
    {y | Valued.v (y - x) < Valued.v r} ∈ 𝓝 x := by
  rw [Valued.mem_nhds]
  have h' : (Valued.v : Valuation K ℤᵐ⁰).restrict r ≠ 0 := by simp [hr]
  exact ⟨Units.mk0 _ h', fun y hy => (Valuation.restrict_lt_iff _).1 hy⟩

theorem val_div_sub_one_lt {K : Type} [Field K] [Valued K ℤᵐ⁰] {u y : K} {c : ℤᵐ⁰} (hu : u ≠ 0)
    (hc : c ≤ 1) (h : Valued.v (y - u) < Valued.v u * c) : y ≠ 0 ∧ Valued.v (u * y⁻¹ - 1) < c := by
  have hvu : Valued.v u ≠ 0 := by simpa using hu
  have hlt : Valued.v (y - u) < Valued.v u := lt_of_lt_of_le h (mul_le_of_le_one_right' hc)
  have hvy : Valued.v y = Valued.v u := Valuation.map_eq_of_sub_lt _ hlt
  have hy : y ≠ 0 := by
    intro h0; rw [h0, map_zero] at hvy; exact hvu hvy.symm
  refine ⟨hy, ?_⟩
  have : u * y⁻¹ - 1 = -((y - u) * y⁻¹) := by field_simp; ring
  rw [this, Valuation.map_neg, map_mul, map_inv₀, hvy]
  have hpos : (0 : ℤᵐ⁰) < Valued.v u := pos_iff_ne_zero.2 hvu
  calc Valued.v (y - u) * (Valued.v u)⁻¹ < Valued.v u * c * (Valued.v u)⁻¹ :=
        mul_lt_mul_of_pos_right h (inv_pos.2 hpos)
    _ = c := by field_simp

theorem main : ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] (χ : HChar L) (s : SplitPlace L) (ξ ξ' : (s.v.adicCompletion (maximalRealSubfield L))ˣ →* ℂˣ), NG.IsCompAt χ s ξ → NG.IsCompAt χ s ξ' → ξ = ξ' := by
  intro L _ _ _ χ s ξ ξ' hξ hξ'
  obtain ⟨⟨N₁, hN₁⟩, hk⟩ := hξ
  obtain ⟨⟨N₂, hN₂⟩, hk'⟩ := hξ'
  ext1 u
  obtain ⟨π, hπ⟩ := s.v.valuation_exists_uniformizer (maximalRealSubfield L)
  have hπ' : Valued.v ((π : s.v.adicCompletion (maximalRealSubfield L))) = WithZero.exp (-1 : ℤ) := by
    rw [HeightOneSpectrum.valuedAdicCompletion_eq_valuation', hπ]
  set N := max N₁ N₂ with hN
  have hN1 : N₁ ≤ N := le_max_left _ _
  have hN2 : N₂ ≤ N := le_max_right _ _
  have hu0 : (u : s.v.adicCompletion (maximalRealSubfield L)) ≠ 0 := u.ne_zero
  have hπ0 : (π : s.v.adicCompletion (maximalRealSubfield L)) ≠ 0 := by
    intro h; rw [h, map_zero] at hπ'; exact (WithZero.exp_ne_zero) hπ'.symm
  have hvr : Valued.v ((u : s.v.adicCompletion (maximalRealSubfield L)) * (π : s.v.adicCompletion (maximalRealSubfield L)) ^ N)
      = Valued.v (u : s.v.adicCompletion (maximalRealSubfield L)) * WithZero.exp (-(N : ℤ)) := by
    rw [map_mul, map_pow, hπ', ← WithZero.exp_nsmul]; congr 2; simp
  have hnhds := ball_mem_nhds' (u : s.v.adicCompletion (maximalRealSubfield L)) _ (mul_ne_zero hu0 (pow_ne_zero N hπ0))
  obtain ⟨x, hx⟩ := (HeightOneSpectrum.denseRange_algebraMap (K := maximalRealSubfield L) s.v).mem_nhds hnhds
  rw [Set.mem_setOf_eq, hvr] at hx
  have hle : WithZero.exp (-(N : ℤ)) ≤ 1 := by
    rw [← WithZero.exp_zero, WithZero.exp_le_exp]; omega
  obtain ⟨hy0, hw⟩ := val_div_sub_one_lt hu0 hle hx
  have hx0 : x ≠ 0 := by rintro rfl; exact hy0 (map_zero _)
  set k : Lˣ := Units.mk0 (algebraMap (maximalRealSubfield L) L x) ((map_ne_zero _).2 hx0) with hkdef
  have hik : ((Units.map (s.i : L →* s.v.adicCompletion (maximalRealSubfield L)) k : _) : s.v.adicCompletion (maximalRealSubfield L))
      = algebraMap (maximalRealSubfield L) (s.v.adicCompletion (maximalRealSubfield L)) x := by
    simp [k]
  set w : (s.v.adicCompletion (maximalRealSubfield L))ˣ := u * (Units.map (s.i : L →* s.v.adicCompletion (maximalRealSubfield L)) k)⁻¹ with hwdef
  have hu : u = Units.map (s.i : L →* s.v.adicCompletion (maximalRealSubfield L)) k * w := by simp [w]
  have hw' : Valued.v ((w : s.v.adicCompletion (maximalRealSubfield L)) - 1) < WithZero.exp (-(N : ℤ)) := by
    have : (w : s.v.adicCompletion (maximalRealSubfield L)) = (u : s.v.adicCompletion (maximalRealSubfield L)) *
        (algebraMap (maximalRealSubfield L) (s.v.adicCompletion (maximalRealSubfield L)) x)⁻¹ := by
      rw [hwdef, Units.val_mul, Units.val_inv_eq_inv_val, hik]
    rw [this]; exact hw
  have e1 : ξ w = 1 := hN₁ w (hw'.le.trans (WithZero.exp_le_exp.2 (by omega)))
  have e2 : ξ' w = 1 := hN₂ w (hw'.le.trans (WithZero.exp_le_exp.2 (by omega)))
  clear_value w
  rw [hu, map_mul, map_mul, e1, e2, hk, hk']

end GlobalTheory.CompAtUniq

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HeckeGeometricAllStates
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1600000

namespace GlobalTheory.HeightCounting.HeckeLaw

theorem delAt_unr {D : D7} (C : CharFrame D) (i : D.ntw.Tw) {P : PlE D.host} (hP : P ∉ D.ntw.S0 i) :
    (C.delAt (D.ntw.l i)).UnrAt P := by
  have h : ¬ OverP D.host (if D.ntw.l i = D.host.pde then D.host.pde' else D.host.pde) P := fun hk =>
    hP (D.ntw.primes_subset_exceptional i (by rw [← Finset.mem_coe, D.ntw.pD_eq]; exact hk))
  unfold CharFrame.delAt
  split_ifs at h ⊢
  · exact C.isDel'.unr P h
  · exact C.isDel.unr P h

theorem del_values {B : Base} {δ : Fld.FieldDat B.toPre} {f : Fr B.toPre} (h : B.KsExact δ f) :
    f.del.ValuesIn 0 B.KstoC ∧ f.del'.ValuesIn 0 B.KstoC := by
  have h1 : Fld.charField f ≤ B.KsC := ((Fld.listField_le_iff δ f).1 (le_of_eq (Eq.symm h))).2.2.2.2.1
  rw [Fld.valuesIn_iff, Fld.valuesIn_iff, B.imField_KstoC]
  exact ⟨((le_sup_right.trans le_sup_left).trans le_sup_left).trans h1, (le_sup_right.trans le_sup_left).trans h1⟩

theorem delAt_mem {B : Base} {f : Fr B.toPre} {T : TwDat B} (w : ColW B f T) (Z : w.Lt) {hX : B.fields.Ok} {Wt : Set B.places.Pl}
    (z : Dat (w.st Z) w.I hX T Wt) (i : (w.st Z).toD7.ntw.Tw) (P : PlE (w.st Z).toD7.host) (hP : P ∉ (w.st Z).toD7.ntw.S0 i) :
    ∃ s : z.core.Q.c.F, (w.st Z).toD7.what₂.embLL (algebraMap z.core.Q.c.F (w.st Z).toD7.what₂.LL s) =
      (((z.R.C.delAt ((w.st Z).toD7.ntw.l i)).val P : ℂˣ) : ℂ) := by
  have hC : z.R.C = Fr.at (w.st Z) f := z.lev.C.trans (congrArg _ w.C_eq)
  have hu := delAt_unr z.R.C i hP
  have hv : (z.R.C.delAt ((w.st Z).toD7.ntw.l i)).ValuesIn 0 B.KstoC := by
    rw [hC]
    unfold CharFrame.delAt
    split_ifs
    · exact (del_values w.exact).2
    · exact (del_values w.exact).1
  obtain ⟨y, hy⟩ := hv P hu
  obtain ⟨s, hs⟩ := z.Ks_le y.1 y.2
  refine ⟨s, ?_⟩
  rw [hs]
  refine Eq.trans (show _ = B.KstoC y from rfl) (hy.trans ?_)
  simp [HChar.valTw]

end GlobalTheory.HeightCounting.HeckeLaw
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MatchingMatricesOfBaseChangeRepresentation
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
open Formalism.AUTREP (GAf)
open Neutral.B1 (Ideles)
open GlobalTheory.HeckeGal (Gab IsGlobalArtin)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1000000
open GlobalTheory.LevCmp
open GlobalTheory.TwistChoice (Reading ReadsAt)

open Formalism.L2.DIV GlobalTheory.CoefModel

namespace GlobalTheory.BcMatch

theorem bcmatch_main : ∀ {L : Type} [Field L] [NumberField L] [IsCMField L] {n : ℕ} {K K' : Type} [Field K] [Field K'] (f : K →+* K') (e : K' →+* ℂ) {W₀ W W' : Type} [AddCommGroup W₀] [Module K W₀] [AddCommGroup W] [Module K' W] [AddCommGroup W'] [Module ℂ W'] (ρ₀ : Representation K (GQ L n) W₀) (ρ : Representation K' (GQ L n) W) (ρ' : Representation ℂ (GQ L n) W'), (∃ (ι : Type) (_ : Fintype ι) (_ : DecidableEq ι) (b₀ : Module.Basis ι K W₀) (b₁ : Module.Basis ι K' W), ∀ γ, LinearMap.toMatrix b₁ b₁ (ρ γ) = (LinearMap.toMatrix b₀ b₀ (ρ₀ γ)).map f) → GlobalTheory.LevCmp.WtMatch (e.comp f) ρ₀ ρ' → GlobalTheory.LevCmp.WtMatch e ρ ρ' := by
  intro L _ _ _ n K K' _ _ f e W₀ W W' _ _ _ _ _ _ ρ₀ ρ ρ' hb hm
  obtain ⟨ι, _, _, b₀, b₁, hb⟩ := hb
  obtain ⟨κ, _, _, c₀, c', hc⟩ := hm
  set P : Matrix ι κ K := b₀.toMatrix c₀ with hP
  set Q : Matrix κ ι K := c₀.toMatrix b₀ with hQ
  have hPQ : P * Q = 1 := Module.Basis.toMatrix_mul_toMatrix_flip b₀ c₀
  have hQP : Q * P = 1 := Module.Basis.toMatrix_mul_toMatrix_flip c₀ b₀
  have hPQf : P.map f * Q.map f = 1 := by rw [← Matrix.map_mul, hPQ, Matrix.map_one _ f.map_zero f.map_one]
  have hQPf : Q.map f * P.map f = 1 := by rw [← Matrix.map_mul, hQP, Matrix.map_one _ f.map_zero f.map_one]
  let std := Pi.basisFun K' κ
  let E : (κ → K') ≃ₗ[K'] W := LinearEquiv.ofLinear (Matrix.toLin std b₁ (P.map f)) (Matrix.toLin b₁ std (Q.map f))
    (by rw [← Matrix.toLin_mul, hPQf, Matrix.toLin_one])
    (by rw [← Matrix.toLin_mul, hQPf, Matrix.toLin_one])
  let d : Module.Basis κ K' W := std.map E
  have hd1 : b₁.toMatrix d = P.map f := by
    ext i j
    rw [Module.Basis.toMatrix_apply]
    have : d j = ∑ k, (P.map f) k j • b₁ k := by
      show E (std j) = _
      exact Matrix.toLin_self _ _ _ _
    rw [this, Module.Basis.repr_sum_self]
  have hd2 : d.toMatrix b₁ = Q.map f := by
    ext j i
    rw [Module.Basis.toMatrix_apply]
    simp [d, E, std, Matrix.toLin_self, Pi.single_apply]
  refine ⟨κ, inferInstance, inferInstance, d, c', fun γ => ?_⟩
  rw [hc γ, ← basis_toMatrix_mul_linearMap_toMatrix_mul_basis_toMatrix d b₁ d b₁ (ρ γ), hd1, hd2, hb γ,
    ← basis_toMatrix_mul_linearMap_toMatrix_mul_basis_toMatrix c₀ b₀ c₀ b₀ (ρ₀ γ), ← hP, ← hQ]
  rw [Matrix.map_mul, Matrix.map_mul, Matrix.map_mul, Matrix.map_mul, Matrix.map_map, Matrix.map_map, Matrix.map_map]
  rfl

end GlobalTheory.BcMatch
end

