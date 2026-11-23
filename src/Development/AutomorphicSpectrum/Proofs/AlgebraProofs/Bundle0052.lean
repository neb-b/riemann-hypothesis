module

public import Mathlib
public import Development.AutomorphicSpectrum.PublishedTheorems.Algebra₂.RegularHypothesesAndConclusion
public import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.Bundle0051
public import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.Bundle0002
public import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.IsFinFlatSub
public import Development.AutomorphicSpectrum.Statements.AlgebraStatements.Bundle0002
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PlaceDivisors.StChartFH
public import ReciprocityTheory.DualLattices.Bundle0028
public import ReciprocityTheory.DualLattices.Bundle0014
public import ReciprocityTheory.DualLattices.Bundle0035
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Clauses
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.Biextensions.GenericFiberCubeInclusion
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.RosVal
public import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.Bundle0002
public import Development.AbelianVarietyTheory.Definitions.TeichmullerDepth.IsEigBasisIff
public import Development.WeilBound.CoreStatements.HodgeTatePoints.IsLocalHomOfFinite
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsTransition
public import Development.WeilBound.CoreStatements.SesquilinearFractions.DTrans
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.Bundle0012
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.Bundle0006
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.BlowupProjections.BlowupProjStatement
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.MultihomogeneousIdeals.Bundle0001
public import GroundTheory.HeightsAndTheta.Heights.SemipositiveHeights.Bundle0003
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Bundle0015
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Bundle0054
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Bundle0046
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Bundle0030
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PTwinFlagPairJoinLeft
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Bundle0064
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Bundle0023
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.StatementsBundles

@[expose] public section

-- bundled from Development.AutomorphicSpectrum.Proofs.AlgebraProofs.BasicOpenNormFibreIff
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory AlgebraicGeometry Opposite
open scoped CategoryTheory.MonObj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.CompanionTheory.FreeQuotProof GlobalTheory.CompanionTheory.Hypotheses₂ GlobalTheory.CompanionTheory.Hypotheses₂.FreeQuot

namespace GlobalTheory.CompanionTheory.PrimesToPts

private theorem to_spec_gamma_bijective (X : Scheme.{0}) [IsAffine X] : Function.Bijective X.toSpecΓ := by
  rw [← Scheme.isoSpec_hom]
  refine ⟨fun a b h => ?_, fun y => ⟨X.isoSpec.inv y, Scheme.inv_hom_apply _ _⟩⟩
  have h' := congrArg X.isoSpec.inv h
  rwa [Scheme.hom_inv_apply, Scheme.hom_inv_apply] at h'

theorem mem_basicOpen_iff_toSpecΓ {X : Scheme.{0}} (f : Γ(X, ⊤)) (x : X) :
    x ∈ X.basicOpen f ↔ f ∉ (X.toSpecΓ x : PrimeSpectrum Γ(X, ⊤)).asIdeal := by
  rw [← X.toSpecΓ_preimage_basicOpen f]
  exact Iff.rfl

theorem comap_toSpecΓ {P D : Scheme.{0}} (v : P ⟶ D) (z : P) :
    (P.toSpecΓ z : PrimeSpectrum Γ(P, ⊤)).asIdeal.comap v.appTop.hom =
      (D.toSpecΓ (v z) : PrimeSpectrum Γ(D, ⊤)).asIdeal := by
  have h : D.toSpecΓ (v z) = Spec.map v.appTop (P.toSpecΓ z) := by
    rw [← Scheme.Hom.comp_apply, Scheme.toSpecΓ_naturality, Scheme.Hom.comp_apply]
  rw [h]
  rfl

theorem primes_to_pts : ∀ {P D : Scheme.{0}} [IsAffine P] [IsAffine D] (v : P ⟶ D) (N : Γ(D, ⊤)) (e : Γ(P, ⊤)), (∀ p : PrimeSpectrum Γ(D, ⊤), N ∉ p.asIdeal ↔ ∀ q : PrimeSpectrum Γ(P, ⊤), q.asIdeal.comap v.appTop.hom = p.asIdeal → e ∉ q.asIdeal) → ∀ y : D, y ∈ D.basicOpen N ↔ ∀ z : P, v z = y → z ∈ P.basicOpen e := by
  intro P D _ _ v N e hN y
  refine (GlobalTheory.CompanionTheory.PrimesToPts.mem_basicOpen_iff_toSpecΓ N y).trans ((hN (D.toSpecΓ y)).trans ?_)
  constructor
  · intro H z hz
    refine (GlobalTheory.CompanionTheory.PrimesToPts.mem_basicOpen_iff_toSpecΓ e z).2 (H _ ?_)
    exact (GlobalTheory.CompanionTheory.PrimesToPts.comap_toSpecΓ v z).trans (by rw [hz])
  · intro H q hq
    obtain ⟨z, rfl⟩ := (to_spec_gamma_bijective P).2 q
    have hz : v z = y := by
      apply (to_spec_gamma_bijective D).1
      apply PrimeSpectrum.ext
      exact (GlobalTheory.CompanionTheory.PrimesToPts.comap_toSpecΓ v z).symm.trans hq
    exact (GlobalTheory.CompanionTheory.PrimesToPts.mem_basicOpen_iff_toSpecΓ e z).1 (H z hz)

end GlobalTheory.CompanionTheory.PrimesToPts
end

-- bundled from Development.AutomorphicSpectrum.Proofs.AlgebraProofs.DualTowerHodgeTateDatum
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry TensorProduct Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.Pdiv.ChartF ReciprocityTheory.ChartRestriction.G.Pdiv.AvDefs
open ReciprocityTheory.PGsh ReciprocityTheory.PGsh.Up ReciprocityTheory.PGsh.Be2 GlobalTheory.ChF
open ReciprocityTheory.ChartRestriction.G.Chart (sp spMap)
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.CompanionTheory.Ar.GR
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.CompanionTheory.Relay.dual_tower_hodge_tate_datum : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) {R₀ : Type} [CommRing R₀] (g : ℕ) (B : BX R₀) (Tw : ATowerL R₀ p) (Dt : DualTower Tw) [Algebra (Tw.O : Type) C], v.Integers (Tw.O : Type) → v (p : C) < 1 → ∀ [Algebra ℤ_[p] (Tw.O : Type)] (Oe : Type) [CommRing Oe] [Algebra ℤ_[p] Oe] (σ : Oe ≃ₐ[ℤ_[p]] Oe) (cp : (Tw.O : Type)) (D : Dat p g B Tw Dt Oe σ cp) (G : Over (Spec (CommRingCat.of R₀))) [GrpObj G] [IsCommMonObj G] (e : ∀ R : LAlg R₀, B.G R → (sp (R₀ := R₀) (R : Type) ⟶ G)), (∀ R, Function.Bijective (e R)) → (∀ R x y, e R (x + y) = e R x * e R y) → (∀ {R S : LAlg R₀} (f : LHom R S) (x : B.G R), e S (B.map f x) = spMap f.1 ≫ e R x) → ∀ (G' : Over (Spec (CommRingCat.of (Tw.O : Type)))) [GrpObj G'] [IsCommMonObj G'] (ψ : G'.left ⟶ G.left), Geo.Tor.IsGrpPullback G' G (Spec.map (CommRingCat.ofHom (algebraMap R₀ (Tw.O : Type)))) ψ → ∃ pt : Nb p g → (sp (R₀ := (Tw.O : Type)) (Tw.O : Type) ⟶ G'), (∀ t, (pt t).left ≫ ψ = (e Tw.O (ptOf B D.L.τ t)).left) ∧ IsTorsPts G' p pt ∧ ∀ T : TorsRep G' p, D.evImg C = torsFun C T pt := by
  first | exact @PositivityTheory.HtPt.Rf.htd_tie | exact PositivityTheory.HtPt.Rf.htd_tie
end

-- bundled from Development.AutomorphicSpectrum.Proofs.AlgebraProofs.ExistsTransitionMatrixGram
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Matrix GlobalTheory GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl
open scoped ComplexOrder

namespace GlobalTheory.CompanionTheory.Ar.Fl

theorem transition_matrix_exists : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (I : Type) [Fintype I] [DecidableEq I] (x e : I → D.La), Fintype.card I = D.p + D.q → LinearIndependent (𝓞 E) e → ∃ T : Matrix I I E, IsTransition D x e T ∧ gramE D x = T * gramE D e * (T.map (IsCMField.complexConj E)).transpose ∧ (LinearIndependent (𝓞 E) x → T.det ≠ 0) ∧ ∃ (n : ℕ) (S : Matrix I I (𝓞 E)), 0 < n ∧ (∀ a, n • x a = ∑ b, S a b • e b) ∧ ∀ a b, (S a b : E) = n * T a b :=
  @PositivityTheory.Xgf.exists_transition_matrix_gram

end GlobalTheory.CompanionTheory.Ar.Fl
end

-- bundled from Development.AutomorphicSpectrum.Proofs.AlgebraProofs.FibreDim
section
namespace GlobalTheory.CompanionTheory.Ar.Giv

theorem fibreDim : ReciprocityTheory.ChartRestriction.G.AI.I4.FibreDimStatement :=
  GroundTheory.Heights₂.Heights.ForSecondHalf.FibreDim.proof

end GlobalTheory.CompanionTheory.Ar.Giv
end

-- bundled from Development.AutomorphicSpectrum.Proofs.AlgebraProofs.FiniteFreePullbackAffine
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory AlgebraicGeometry Opposite
open scoped CategoryTheory.MonObj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.CompanionTheory.FreeQuotProof GlobalTheory.CompanionTheory.Hypotheses₂ GlobalTheory.CompanionTheory.Hypotheses₂.FreeQuot

noncomputable section
namespace GlobalTheory.CompanionTheory.FreeQuotProof.Nbhd

theorem finiteFreeHom_algebraMap_iff {A B : Type} [CommRing A] [CommRing B] [Algebra A B] :
    FiniteFreeHom (algebraMap A B) ↔ Module.Free A B ∧ Module.Finite A B := by
  have h : (algebraMap A B).toAlgebra = ‹Algebra A B› := Algebra.algebra_ext _ _ fun _ => rfl
  simp only [GlobalTheory.CompanionTheory.FreeQuotProof.Nbhd.FiniteFreeHom]
  rw [h]

theorem finiteFreeHom_comp {A B C : Type} [CommRing A] [CommRing B] [CommRing C]
    (f : A →+* B) (g : B →+* C) (hf : FiniteFreeHom f) (hg : FiniteFreeHom g) :
    FiniteFreeHom (g.comp f) := by
  letI := f.toAlgebra
  letI := g.toAlgebra
  letI := (g.comp f).toAlgebra
  haveI : IsScalarTower A B C := IsScalarTower.of_algebraMap_eq fun _ => rfl
  obtain ⟨hf₁, hf₂⟩ := hf
  obtain ⟨hg₁, hg₂⟩ := hg
  exact ⟨Module.Free.trans (S := B), Module.Finite.trans B C⟩

theorem finiteFreeHom_ringEquiv {A B : Type} [CommRing A] [CommRing B] (e : A ≃+* B) :
    FiniteFreeHom e.toRingHom := by
  letI := e.toRingHom.toAlgebra
  let l : A ≃ₗ[A] B := { e with map_smul' := fun a x => map_mul e a x }
  exact ⟨Module.Free.of_equiv l, Module.Finite.equiv l⟩

theorem finiteFreeHom_stableUnderComposition :
    RingHom.StableUnderComposition (fun {A B : Type} [CommRing A] [CommRing B] (f : A →+* B) =>
      FiniteFreeHom f) := by
  intro A B C _ _ _ f g hf hg
  exact GlobalTheory.CompanionTheory.FreeQuotProof.Nbhd.finiteFreeHom_comp f g hf hg

theorem finiteFreeHom_respectsIso :
    RingHom.RespectsIso (fun {A B : Type} [CommRing A] [CommRing B] (f : A →+* B) =>
      FiniteFreeHom f) :=
  RingHom.StableUnderComposition.respectsIso GlobalTheory.CompanionTheory.FreeQuotProof.Nbhd.finiteFreeHom_stableUnderComposition
    fun e => GlobalTheory.CompanionTheory.FreeQuotProof.Nbhd.finiteFreeHom_ringEquiv e

theorem finiteFreeHom_isStableUnderBaseChange :
    RingHom.IsStableUnderBaseChange (fun {A B : Type} [CommRing A] [CommRing B] (f : A →+* B) =>
      FiniteFreeHom f) := by
  refine RingHom.IsStableUnderBaseChange.mk GlobalTheory.CompanionTheory.FreeQuotProof.Nbhd.finiteFreeHom_respectsIso ?_
  intro R S T _ _ _ _ _ h
  obtain ⟨h₁, h₂⟩ := GlobalTheory.CompanionTheory.FreeQuotProof.Nbhd.finiteFreeHom_algebraMap_iff.1 h
  exact GlobalTheory.CompanionTheory.FreeQuotProof.Nbhd.finiteFreeHom_algebraMap_iff.2 ⟨inferInstance, inferInstance⟩

theorem finiteFreeHom_appTop_of_isPullback :
    ∀ {P Q D W : Scheme.{0}} {u : P ⟶ Q} {v : P ⟶ D} {g : Q ⟶ W} {h : D ⟶ W} [IsAffine P] [IsAffine Q] [IsAffine D] [IsAffine W], IsPullback u v g h → GlobalTheory.CompanionTheory.FreeQuotProof.Nbhd.FiniteFreeHom g.appTop.hom → GlobalTheory.CompanionTheory.FreeQuotProof.Nbhd.FiniteFreeHom v.appTop.hom := by
  intro P Q D W u v g h _ _ _ _ hpb hg
  have hbc := RingHom.IsStableUnderBaseChange.pullback_fst_appTop @GlobalTheory.CompanionTheory.FreeQuotProof.Nbhd.FiniteFreeHom
    GlobalTheory.CompanionTheory.FreeQuotProof.Nbhd.finiteFreeHom_isStableUnderBaseChange GlobalTheory.CompanionTheory.FreeQuotProof.Nbhd.finiteFreeHom_respectsIso h g hg
  haveI : IsIso hpb.flip.isoPullback.hom.appTop := by
    rw [← Scheme.Γ_map_op]
    exact (Scheme.Γ.mapIso hpb.flip.isoPullback.op).isIso_hom
  rw [← hpb.flip.isoPullback_hom_fst, Scheme.Hom.comp_appTop, CommRingCat.hom_comp]
  exact (RingHom.RespectsIso.cancel_right_isIso GlobalTheory.CompanionTheory.FreeQuotProof.Nbhd.finiteFreeHom_respectsIso _ _).2 hbc

end GlobalTheory.CompanionTheory.FreeQuotProof.Nbhd
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.AlgebraProofs.FiniteSetBasicOpenAffine
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory AlgebraicGeometry Opposite
open scoped CategoryTheory.MonObj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.CompanionTheory.FreeQuotProof GlobalTheory.CompanionTheory.Hypotheses₂ GlobalTheory.CompanionTheory.Hypotheses₂.FreeQuot

namespace GlobalTheory.CompanionTheory.PrimeAvoid

theorem exists_basicOpen_between {X : Scheme.{0}} (U V₀ : X.Opens) (hU : IsAffineOpen U)
    (hV : V₀ ≤ U) (K : Set X) (hK : K.Finite) (hKV : K ⊆ V₀) :
    ∃ f : Γ(X, U), K ⊆ X.basicOpen f ∧ X.basicOpen f ≤ V₀ := by
  classical
  let W : Set (PrimeSpectrum Γ(X, U)) := hU.fromSpec ⁻¹' (V₀ : Set X)
  have hWo : IsOpen W := (hU.fromSpec ⁻¹ᵁ V₀).isOpen
  let I : Ideal Γ(X, U) := PrimeSpectrum.vanishingIdeal Wᶜ
  let s : Set (Ideal Γ(X, U)) := PrimeSpectrum.asIdeal '' (hU.fromSpec ⁻¹' K)
  have hs : s.Finite := (hK.preimage hU.fromSpec.isOpenEmbedding.injective.injOn).image _
  have hnot : ¬ ((I : Set Γ(X, U)) ⊆ ⋃ P ∈ s, (P : Set Γ(X, U))) := by
    intro h
    obtain ⟨P, ⟨p, hpK, rfl⟩, hIp⟩ :=
      (Ideal.subset_union_prime_finite (f := fun P : Ideal Γ(X, U) => P) hs ⊥ ⊥
        (fun P hP _ _ => by obtain ⟨p, -, rfl⟩ := hP; exact p.isPrime)).1 h
    have hpW : p ∈ W := hKV hpK
    have hcl : p ∈ closure Wᶜ := by
      rw [← PrimeSpectrum.zeroLocus_vanishingIdeal_eq_closure]
      exact (PrimeSpectrum.mem_zeroLocus _ _).2 hIp
    rw [hWo.isClosed_compl.closure_eq] at hcl
    exact hcl hpW
  obtain ⟨g, hgI, hgs⟩ := Set.not_subset.1 hnot
  refine ⟨g, ?_, ?_⟩
  · intro x hx
    obtain ⟨p, rfl⟩ : x ∈ Set.range hU.fromSpec := by
      rw [hU.range_fromSpec]
      exact hV (hKV hx)
    have hp : p ∈ hU.fromSpec ⁻¹ᵁ X.basicOpen g := by
      rw [hU.fromSpec_preimage_basicOpen]
      exact (PrimeSpectrum.mem_basicOpen g p).2 fun hg => hgs (Set.mem_biUnion ⟨p, hx, rfl⟩ hg)
    exact hp
  · intro x hx
    obtain ⟨p, rfl⟩ : x ∈ Set.range hU.fromSpec := by
      rw [hU.range_fromSpec]
      exact X.basicOpen_le g hx
    have hp : p ∈ hU.fromSpec ⁻¹ᵁ X.basicOpen g := hx
    rw [hU.fromSpec_preimage_basicOpen] at hp
    have hp' := (PrimeSpectrum.mem_basicOpen g p).1 hp
    by_contra hpV
    exact hp' ((PrimeSpectrum.mem_vanishingIdeal _ _).1 hgI p hpV)

end GlobalTheory.CompanionTheory.PrimeAvoid
end

-- bundled from Development.AutomorphicSpectrum.Proofs.AlgebraProofs.FlagModelJoinLeft
section
namespace GlobalTheory.CompanionTheory.Ar.Num.FlagModelJoinLeft

theorem main : GroundTheory.Heights₂.Heights.NumbersDVR.FlagModelJoinLeftAlt.Statement :=
  GroundTheory.Heights₂.Heights.NumbersDVR.FlagModelJoinLeftAlt.proof
    GroundTheory.Heights₂.Heights.NumbersDVR.JoinVerticalDivisor.proof
    (GroundTheory.Heights₂.Heights.NumbersDVR.FlagPairJoinLeft.proof
      GroundTheory.Heights₂.Heights.NumbersDVR.JoinVerticalDivisorLeft.proof)
    (GroundTheory.Heights₂.Heights.NumbersDVR.PairNumberJoinLeft.proof _root_.GlobalTheory.CompanionTheory.Ar.Num.PairNumberPullback.main
      GroundTheory.Heights₂.Heights.NumbersDVR.JoinVerticalDivisorLeft.proof
      GroundTheory.Heights₂.Heights.NumbersDVR.BirationalJoin.proof)

end GlobalTheory.CompanionTheory.Ar.Num.FlagModelJoinLeft
end

-- bundled from Development.AutomorphicSpectrum.Proofs.AlgebraProofs.HasAffineChartIff
section
noncomputable section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory AlgebraicGeometry Opposite
open scoped CategoryTheory.MonObj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.CompanionTheory.FreeQuotProof GlobalTheory.CompanionTheory.Hypotheses₂ GlobalTheory.CompanionTheory.Hypotheses₂.FreeQuot

namespace GlobalTheory.CompanionTheory.FreeQuotGlue

def IsChart {P X Y : Scheme.{0}} (a b : P ⟶ X) (V : X.Opens) (q : V.toScheme ⟶ Y) : Prop :=
  a ⁻¹ᵁ V = b ⁻¹ᵁ V ∧ IsFinite q ∧ Flat q ∧ LocallyOfFinitePresentation q ∧ Surjective q ∧
    ∃ a' : (b ⁻¹ᵁ V).toScheme ⟶ V.toScheme,
      a' ≫ V.ι = (b ⁻¹ᵁ V).ι ≫ a ∧ IsPullback a' (b ∣_ V) q q

theorem hasAffineChart_iff {P X : Scheme.{0}} (a b : P ⟶ X) (V : X.Opens) :
    HasAffineChart a b V ↔ ∃ (Y : Scheme.{0}) (q : V.toScheme ⟶ Y), IsAffine Y ∧ IsChart a b V q := by
  constructor
  · rintro ⟨h, Y, q, a', hY, h1, h2, h3, h4, h5, h6⟩
    exact ⟨Y, q, hY, h, h1, h2, h3, h4, a', h5, h6⟩
  · rintro ⟨Y, q, hY, h, h1, h2, h3, h4, a', h5, h6⟩
    exact ⟨h, Y, q, a', hY, h1, h2, h3, h4, h5, h6⟩

variable {P X Y : Scheme.{0}} {a b : P ⟶ X} {V : X.Opens} {q : V.toScheme ⟶ Y}

theorem IsChart.stable (h : IsChart a b V q) : a ⁻¹ᵁ V = b ⁻¹ᵁ V := h.1
theorem IsChart.isFinite (h : IsChart a b V q) : IsFinite q := h.2.1
theorem IsChart.flat (h : IsChart a b V q) : Flat q := h.2.2.1
theorem IsChart.lfp (h : IsChart a b V q) : LocallyOfFinitePresentation q := h.2.2.2.1
theorem IsChart.surjective (h : IsChart a b V q) : Surjective q := h.2.2.2.2.1

theorem IsChart.effectiveEpi (h : IsChart a b V q) : EffectiveEpi q := by
  have := h.isFinite; have := h.flat; have := h.surjective
  infer_instance

theorem IsChart.comp_eq_iff (h : IsChart a b V q) {Z : Scheme.{0}} (g₁ g₂ : Z ⟶ V.toScheme) :
    g₁ ≫ q = g₂ ≫ q ↔ ∃ l : Z ⟶ P, l ≫ a = g₁ ≫ V.ι ∧ l ≫ b = g₂ ≫ V.ι := by
  obtain ⟨hs, -, -, -, -, a', ha, hp⟩ := h
  constructor
  · intro e
    refine ⟨hp.lift g₁ g₂ e ≫ (b ⁻¹ᵁ V).ι, ?_, ?_⟩
    · rw [Category.assoc, ← ha, hp.lift_fst_assoc]
    · rw [Category.assoc, ← morphismRestrict_ι, hp.lift_snd_assoc]
  · rintro ⟨l, h1, h2⟩
    have hr : Set.range l ⊆ Set.range (b ⁻¹ᵁ V).ι := by
      rintro _ ⟨z, rfl⟩
      have : b (l z) ∈ V := by
        have : b (l z) = V.ι (g₂ z) := congr($h2 z)
        rw [this]; exact (g₂ z).2
      simpa using this
    let l' : Z ⟶ (b ⁻¹ᵁ V).toScheme := IsOpenImmersion.lift _ l hr
    have hl : l' ≫ (b ⁻¹ᵁ V).ι = l := IsOpenImmersion.lift_fac _ _ _
    have e1 : l' ≫ a' = g₁ := by
      rw [← cancel_mono V.ι, Category.assoc, ha, reassoc_of% hl, h1]
    have e2 : l' ≫ (b ∣_ V) = g₂ := by
      rw [← cancel_mono V.ι, Category.assoc, morphismRestrict_ι, reassoc_of% hl, h2]
    rw [← e1, ← e2, Category.assoc, Category.assoc, hp.w]

theorem IsChart.apply_eq_iff (h : IsChart a b V q) (u v : V.toScheme) :
    q u = q v ↔ ∃ p : P, a p = V.ι u ∧ b p = V.ι v := by
  obtain ⟨hs, -, -, -, -, a', ha, hp⟩ := id h
  constructor
  · intro e
    obtain ⟨z, h1, h2⟩ := Scheme.Pullback.exists_preimage_pullback u v e
    let p : (b ⁻¹ᵁ V).toScheme := hp.isoPullback.inv z
    have e1 : a' p = u := by
      rw [← h1]
      exact congr($(hp.isoPullback_inv_fst) z)
    have e2 : (b ∣_ V) p = v := by
      rw [← h2]
      exact congr($(hp.isoPullback_inv_snd) z)
    refine ⟨(b ⁻¹ᵁ V).ι p, ?_, ?_⟩
    · rw [← e1]; exact (congr($ha p)).symm
    · rw [← e2]; exact (congr($(morphismRestrict_ι b V) p)).symm
  · rintro ⟨p, h1, h2⟩
    have hp' : p ∈ b ⁻¹ᵁ V := by
      change b p ∈ V
      rw [h2]; exact v.2
    let p' : (b ⁻¹ᵁ V).toScheme := ⟨p, hp'⟩
    have hi : (b ⁻¹ᵁ V).ι p' = p := rfl
    have e1 : a' p' = u := V.ι.isOpenEmbedding.injective (by
      rw [← h1, ← hi]; exact congr($ha p'))
    have e2 : (b ∣_ V) p' = v := V.ι.isOpenEmbedding.injective (by
      rw [← h2, ← hi]; exact congr($(morphismRestrict_ι b V) p'))
    rw [← e1, ← e2]
    exact congr($(hp.w) p')

end GlobalTheory.CompanionTheory.FreeQuotGlue
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.AlgebraProofs.MemOrbitSelf
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory AlgebraicGeometry Opposite
open scoped CategoryTheory.MonObj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.CompanionTheory.FreeQuotProof GlobalTheory.CompanionTheory.Hypotheses₂ GlobalTheory.CompanionTheory.Hypotheses₂.FreeQuot

namespace GlobalTheory.CompanionTheory.FreeQuotProof

theorem mem_orbit_self {S : Scheme.{0}} (G X : Over S) [GrpObj G] [ModObj G X] (x : X.left) :
    x ∈ orbit G X x := by
  have h1 : lift (1 : X ⟶ G) (𝟙 X) ≫ snd G X = 𝟙 X := lift_snd _ _
  have h2 : lift (1 : X ⟶ G) (𝟙 X) ≫ (γ[G, X] : G ⊗ X ⟶ X) = 𝟙 X := by
    have := one_smul (X ⟶ G) (𝟙 X)
    rwa [Hom.smul_def] at this
  have h1' : (lift (1 : X ⟶ G) (𝟙 X)).left ≫ (snd G X).left = 𝟙 X.left := by
    rw [← Over.comp_left, h1, Over.id_left]
  have h2' : (lift (1 : X ⟶ G) (𝟙 X)).left ≫ (γ[G, X] : G ⊗ X ⟶ X).left = 𝟙 X.left := by
    rw [← Over.comp_left, h2, Over.id_left]
  refine ⟨(lift (1 : X ⟶ G) (𝟙 X)).left x, ?_, ?_⟩
  · change (snd G X).left ((lift (1 : X ⟶ G) (𝟙 X)).left x) = x
    rw [← Scheme.Hom.comp_apply, h1']; rfl
  · rw [← Scheme.Hom.comp_apply, h2']; rfl

end GlobalTheory.CompanionTheory.FreeQuotProof
end

-- bundled from Development.AutomorphicSpectrum.Proofs.AlgebraProofs.NormNotMemPrimeIff
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory AlgebraicGeometry Opposite
open scoped CategoryTheory.MonObj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.CompanionTheory.FreeQuotProof GlobalTheory.CompanionTheory.Hypotheses₂ GlobalTheory.CompanionTheory.Hypotheses₂.FreeQuot

namespace GlobalTheory.CompanionTheory.NormPrime


open TensorProduct in
theorem norm_one_tmul {A B K : Type} [CommRing A] [CommRing B] [Algebra A B] [Module.Free A B]
    [Module.Finite A B] [Field K] [Algebra A K] (e : B) :
    Algebra.norm K ((1 : K) ⊗ₜ[A] e : K ⊗[A] B) = algebraMap A K (Algebra.norm A e) := by
  rw [Algebra.norm_apply, Algebra.norm_apply, ← LinearMap.det_baseChange]
  congr 1
  refine LinearMap.ext fun z => ?_
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul x y => simp [LinearMap.baseChange_tmul]
  | add x y hx hy => simp only [map_add (f := _), hx, hy]

theorem norm_mem_comap {A B : Type} [CommRing A] [CommRing B] [Algebra A B] [Module.Free A B]
    [Module.Finite A B] (e : B) (q : Ideal B) (he : e ∈ q) :
    Algebra.norm A e ∈ q.comap (algebraMap A B) := by
  set χ := (Algebra.lmul A B e).charpoly with hχ
  have h2 : Polynomial.aeval e χ = 0 := by
    apply Algebra.lmul_injective (R := A)
    rw [map_zero, ← Polynomial.aeval_algHom_apply]
    exact LinearMap.aeval_self_charpoly _
  have h3 := congrArg (Polynomial.aeval e) (Polynomial.divX_mul_X_add χ)
  rw [h2, map_add (f := _), map_mul, Polynomial.aeval_X, Polynomial.aeval_C] at h3
  have h4 : algebraMap A B (χ.coeff 0) ∈ q := by
    have h5 : algebraMap A B (χ.coeff 0) = -(Polynomial.aeval e χ.divX * e) :=
      eq_neg_of_add_eq_zero_right h3
    rw [h5]
    exact q.neg_mem (q.mul_mem_left _ he)
  rw [Algebra.norm_apply, LinearMap.det_eq_sign_charpoly_coeff]
  exact Ideal.mul_mem_left _ _ (Ideal.mem_comap.2 h4)


open TensorProduct in
theorem norm_notMem_iff {A B : Type} [CommRing A] [CommRing B] [Algebra A B] [Module.Free A B]
    [Module.Finite A B] (e : B) (p : Ideal A) (hp : p.IsPrime) :
    Algebra.norm A e ∉ p ↔ ∀ q : Ideal B, q.IsPrime → q.comap (algebraMap A B) = p → e ∉ q := by
  constructor
  · intro hN q _ hc he
    exact hN (hc ▸ norm_mem_comap e q he)
  · intro H hN
    have h0 : Algebra.norm p.ResidueField ((1 : p.ResidueField) ⊗ₜ[A] e : p.ResidueField ⊗[A] B) = 0 := by
      rw [norm_one_tmul]
      exact (Ideal.algebraMap_residueField_eq_zero).2 hN
    have hnu : ¬ IsUnit ((1 : p.ResidueField) ⊗ₜ[A] e : p.ResidueField ⊗[A] B) := fun hu => by
      have := hu.map (Algebra.norm p.ResidueField)
      rw [h0] at this
      exact not_isUnit_zero this
    obtain ⟨m, hm, hem⟩ := exists_max_ideal_of_mem_nonunits hnu
    let f : B →ₐ[A] p.ResidueField ⊗[A] B := Algebra.TensorProduct.includeRight
    have hmp : m.IsPrime := hm.isPrime
    refine H (m.comap f) (Ideal.comap_isPrime f m) ?_ (Ideal.mem_comap.2 hem)
    ext a
    have hfa : f (algebraMap A B a) =
        algebraMap p.ResidueField (p.ResidueField ⊗[A] B) (algebraMap A p.ResidueField a) := by
      rw [f.commutes, IsScalarTower.algebraMap_apply A p.ResidueField]
    rw [Ideal.mem_comap, Ideal.mem_comap, hfa]
    constructor
    · intro ha
      by_contra hap
      have hne : algebraMap A p.ResidueField a ≠ 0 :=
        fun h => hap ((Ideal.algebraMap_residueField_eq_zero).1 h)
      exact hm.ne_top (Ideal.eq_top_of_isUnit_mem _ ha ((isUnit_iff_ne_zero.2 hne).map _))
    · intro ha
      rw [(Ideal.algebraMap_residueField_eq_zero).2 ha, map_zero]
      exact m.zero_mem

end GlobalTheory.CompanionTheory.NormPrime
end

