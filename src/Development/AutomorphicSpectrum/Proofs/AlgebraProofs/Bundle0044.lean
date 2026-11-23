module

public import Mathlib
public import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.Bundle0043
public import ReciprocityTheory.DualLattices.Bundle0004
public import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.IsTight
public import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.Bundle0003
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.NonzeroLocus
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ChartPullbacks.UniversalCharts.LePreimageOfNil
public import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.IsFinFlatSub
public import Development.AutomorphicSpectrum.PublishedTheorems.Algebra₂.Bundle0001
public import Development.AutomorphicSpectrum.Statements.AlgebraStatements.Bundle0002
public import Development.AutomorphicSpectrum.Statements.AlgebraStatements.Bundle0001
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.ToFirst
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
public import Development.WeilBound.CoreStatements.HodgeTatePoints.Bundle0002
public import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.Bundle0005
public import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.BundleChernComparison
public import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.Bundle0008
public import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.Bundle0037
public import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.LatticeFamilyInjectiveModelFacts
public import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.Bundle0019
public import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.Bundle0002
public import Development.WeilBound.CoreStatements.HodgeTatePoints.CbFrob
public import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.Bundle0004
public import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.OrderPSquaredExtremalColength
public import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.Bundle0001
public import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.PluckerCoord
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.StatementsBundles
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Bundle0025
public import Development.WeilBound.CoreStatements.TorusUniformisation.ChowMahlerFamilies.Bundle0021

@[expose] public section

-- bundled from Development.AutomorphicSpectrum.Proofs.AlgebraProofs.AbelianSchemeTorsionAugmentationStatement
section
open ReciprocityTheory.PGsh.L2 ReciprocityTheory.PGsh.Up GlobalTheory.CompanionTheory.Ar.GR
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi
open ReciprocityTheory.ChartRestriction.G.Chart (sp spMap)
open scoped CategoryTheory.Obj CategoryTheory.MonObj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.abelian_scheme_torsion_augmentation : QuotientByFiniteFlatStatement → ZarhinStatement → HodgeTateDatumStatement → ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (R : Type) [CommRing R] [Algebra R C], v.Integers R → v (p : C) < 1 → IsAdicComplete (Ideal.span {(p : R)}) R → ∀ (A : Over (Spec (CommRingCat.of R))) [GrpObj A] (L : LB A.left), IsAbelianScheme A → L.IsLB → Out.RelAmple A L → ∀ (T : TorsRep A p) (N : Type) [AddCommGroup N] [Fintype N] [DecidableEq N] (pt : N → (sp (R₀ := R) R ⟶ A)), IsTorsPts A p pt → ∀ K : AddSubgroup N, GenAF p (torsFun C T pt) K := by
  first | exact @GlobalTheory.CompanionTheory.Ar.GR.sub_abelianScheme | exact GlobalTheory.CompanionTheory.Ar.GR.sub_abelianScheme | (intros; apply GlobalTheory.CompanionTheory.Ar.GR.sub_abelianScheme <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.AlgebraProofs.CompleteDvrDominatingValuation
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1 GlobalTheory.CompanionTheory.Ar.Crv GlobalTheory.CompanionTheory.Ar.Conj
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.CompanionTheory.Relay.complete_dvr_dominating_valuation : ∀ (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] (l : Type) [Field l] [Algebra (IsLocalRing.ResidueField V) l] [FiniteDimensional (IsLocalRing.ResidueField V) l], ∃ (R : Type) (_ : CommRing R) (_ : IsDomain R) (_ : IsDiscreteValuationRing R) (f : V →+* R) (_ : IsLocalHom f) (s : l →+* IsLocalRing.ResidueField R), IsAdicComplete (IsLocalRing.maximalIdeal R) R ∧ Function.Injective f ∧ s.comp (algebraMap _ l) = IsLocalRing.ResidueField.map f := by
  intro V _ _ _ l _ _ _
  obtain ⟨n, b⟩ : ∃ n, Nonempty (Module.Basis (Fin n) (IsLocalRing.ResidueField V) l) :=
    ⟨_, ⟨Module.finBasis (IsLocalRing.ResidueField V) l⟩⟩
  obtain ⟨b⟩ := b
  have hne : ∀ i, minpoly (IsLocalRing.ResidueField V) (b i) ≠ 0 := fun i =>
    minpoly.ne_zero (Algebra.IsIntegral.isIntegral (b i))
  obtain ⟨R1, _, _, _, f1, _, hinj1, hsplit⟩ := PositivityTheory.HtPt.Pdvr.exists_splits _ V
    (∏ i, minpoly (IsLocalRing.ResidueField V) (b i)) rfl
  letI : Algebra (IsLocalRing.ResidueField V) (IsLocalRing.ResidueField R1) :=
    (IsLocalRing.ResidueField.map f1).toAlgebra
  have hS : IntermediateField.adjoin (IsLocalRing.ResidueField V) (Set.range b) = ⊤ := by
    rw [eq_top_iff]
    intro x _
    have hspan : Submodule.span (IsLocalRing.ResidueField V) (Set.range b) ≤
        (IntermediateField.adjoin (IsLocalRing.ResidueField V) (Set.range b)).toSubalgebra.toSubmodule :=
      Submodule.span_le.mpr (IntermediateField.subset_adjoin _ _)
    exact hspan (b.span_eq ▸ Submodule.mem_top)
  have hK : ∀ s ∈ Set.range b, IsIntegral (IsLocalRing.ResidueField V) s ∧
      ((minpoly (IsLocalRing.ResidueField V) s).map
        (algebraMap (IsLocalRing.ResidueField V) (IsLocalRing.ResidueField R1))).Splits := by
    rintro s ⟨i, rfl⟩
    refine ⟨Algebra.IsIntegral.isIntegral (b i), ?_⟩
    refine Polynomial.Splits.of_dvd hsplit ?_ ?_
    · exact Polynomial.map_ne_zero (Finset.prod_ne_zero_iff.mpr fun j _ => hne j)
    · exact Polynomial.map_dvd _ (Finset.dvd_prod_of_mem _ (Finset.mem_univ i))
  obtain ⟨φ⟩ := IntermediateField.nonempty_algHom_of_adjoin_splits hK hS
  obtain ⟨R, _, _, _, f2, _, hcomp, hinj2⟩ := PositivityTheory.HtPt.Pdvr.exists_complete R1
  refine ⟨R, inferInstance, inferInstance, inferInstance, f2.comp f1, inferInstance,
    (IsLocalRing.ResidueField.map f2).comp φ.toRingHom, hcomp, hinj2.comp hinj1, ?_⟩
  ext x
  rw [IsLocalRing.ResidueField.map_comp]
  simp only [RingHom.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, AlgHom.commutes]
  rfl
end

-- bundled from Development.AutomorphicSpectrum.Proofs.AlgebraProofs.FundamentalIdealFrobeniusPowersStatement
section
open ReciprocityTheory.PGsh.L2 ReciprocityTheory.PGsh.Up GlobalTheory.CompanionTheory.Ar.GR
open scoped Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.fundamental_ideal_frobenius_powers : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (R : Type) [CommRing R] [Algebra R C], v.Integers R → v (p : C) < 1 → ∀ (F : Type) [Field F] [Fintype F] [DecidableEq F] [CharP F p] (f : ℕ), Fintype.card F = p ^ f → ∀ (AA : HopfOrder (C := C) R F), FStable F AA.carrier → ∀ σ : MulChar F R, IsFund p σ → ∀ c : ℕ → R, (∀ n, xIdeal AA.carrier (σ ^ p ^ n) = Ideal.span {c n}) → (∀ n, v (p : C) ≤ v (algebraMap R C (c n)) ^ (p - 1)) ∧ ∀ d : Fin f → Fin p, (∃ n, (d n : ℕ) ≠ 0) → xIdeal AA.carrier (σ ^ (∑ n : Fin f, (d n : ℕ) * p ^ (n : ℕ))) = Ideal.span {∏ n : Fin f, c n ^ (d n : ℕ)} := by
  first | exact @GlobalTheory.CompanionTheory.Relay.fundamental_ideal_frobenius_powers | exact GlobalTheory.CompanionTheory.Relay.fundamental_ideal_frobenius_powers | (intros; apply GlobalTheory.CompanionTheory.Relay.fundamental_ideal_frobenius_powers <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.AlgebraProofs.LatticeFamilyModelChern
section
open MvPolynomial GlobalTheory.CompanionTheory.Ar.Num GroundTheory.Heights₂.Heights.NumbersDVR
open ReciprocityTheory.ChartRestriction.G.Geo (ChartBundle chartRing)
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.NumbersDVR.Bundles (mseg mcIdeal chartMon joinCoord bcCoord pullDeg restrictChart fnField ck rootNum SameGeneric LatLE IsPull IsPullBC)

namespace GlobalTheory.CompanionTheory.Ar.FamLines

variable {o Ω : Type} [CommRing o] [Field Ω] [Algebra o Ω] {V : Type} [AddCommGroup V] [Module Ω V]

theorem exists_finset {R : Subalgebra o Ω} {r : ℕ} {L : AddSubgroup V} (h : LocFree R r L) :
    ∃ S : Finset V, L = spanOver R (S : Set V) := by
  classical
  let L' : Submodule R V := { L with smul_mem' := fun a e he => h.1 a a.2 e he }
  obtain ⟨k, φ, v, hφ, hv⟩ := LocFreeProj.exists_dualBasis (L := L') (r := r) h
  refine ⟨Finset.univ.image fun i => (v i : V), le_antisymm (fun e he => ?_) ?_⟩
  · rw [← hv e]
    · refine sum_mem fun i _ => AddSubgroup.subset_closure ⟨φ i e, hφ i e he, v i, ?_, rfl⟩
      simp
  · refine (AddSubgroup.closure_le _).2 ?_
    rintro _ ⟨a, ha, e, he, rfl⟩
    simp only [Finset.coe_image, Finset.coe_univ, Set.image_univ, Set.mem_range] at he
    obtain ⟨i, rfl⟩ := he
    exact h.1 a ha _ (v i).2

theorem ne_bot {R : Subalgebra o Ω} {L : AddSubgroup V} (h : LocFree R 1 L) : L ≠ ⊥ := by
  obtain ⟨-, k, f, c, -, -, hs, hb⟩ := h
  have hex : ∃ l, f l ≠ 0 := by
    by_contra hn
    push Not at hn
    simp [hn] at hs
  obtain ⟨l, hl⟩ := hex
  obtain ⟨b, hli, -, hb⟩ := hb l
  obtain ⟨m, hm⟩ := (hb (b 0)).2 ⟨fun _ => 1, fun _ => ⟨0, by simp⟩, by simp⟩
  rintro rfl
  exact smul_ne_zero (pow_ne_zero m hl) (hli.ne_zero 0) (AddSubgroup.mem_bot.1 hm)

theorem injective {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Algebra O Ω]
    {K : Type} [Fintype K] [DecidableEq K] {ι : K → Type} [∀ k, Fintype (ι k)] {x : (Σ k, ι k) → Ω} {d : ℕ}
    (h : GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.NumbersDVR.Bundles.IsModelOver O (mcIdeal O x) d) :
    Function.Injective (algebraMap O Ω) := by
  set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
  intro a ha
  have h1 : a ∈ (mcIdeal O x).comap (C : O →+* _) := by
    rw [Ideal.mem_comap, mcIdeal, RingHom.mem_ker]
    change GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.NumbersDVR.Bundles.mcMap O x (algebraMap O _ a) = 0
    rw [AlgHom.commutes, MvPolynomial.algebraMap_apply, ha, map_zero]
  rw [h.2.2.1] at h1
  exact h1

theorem main : ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (Ω : Type) [Field Ω] [Algebra O Ω] (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)] (x : (Σ k, ι k) → Ω) (d : ℕ), GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.NumbersDVR.Bundles.IsModelOver O (mcIdeal O x) d → fnField O x = ⊤ → ∀ {F : Type} [Zero F] [One F] [Fintype F] {n : ℕ} {Sg : Type} [Fintype Sg] {r s : Sg → ℕ} (p : ℕ), p.Prime → ∀ (w : O) (χ : Sg → F → O) (φ : Equiv.Perm Sg) (D : (∀ k, ι k) → LieLatticeData Ω F n Sg r s), IsLatticeFamily O x p w χ φ D → (∀ c, mseg x c ≠ 0 → (D c).Good₁ (chartRing O (mseg x) c) p (fun τ a => algebraMap O Ω (χ τ a))) → ∃ (K' : Type) (_ : Fintype K') (_ : DecidableEq K') (ι' : K' → Type) (_ : ∀ k, Fintype (ι' k)) (z : (Σ k, ι' k) → Ω), GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.NumbersDVR.Bundles.IsModelOver O (mcIdeal O (joinCoord x z)) d ∧ (∀ τ i, ∃ (u : Ω) (a : _ → ℤ), u ≠ 0 ∧ IsLine O (joinCoord x z) u a fun c => (pullFamily O x z D c).xId (fun a => algebraMap O Ω (χ τ a)) i) := by
  intro O _ _ _ Ω _ _ K _ _ ι _ x d hx hfn F _ _ _ n Sg _ r s p hp w χ φ D hD hG
  have hinj := injective hx
  have hchar : ∀ R : Subalgebra O Ω,
      CharData R p (algebraMap O Ω w) (fun τ a => algebraMap O Ω (χ τ a)) := by
    intro R
    obtain ⟨hp0, ⟨u, hu, huw⟩, -, h01, hχ⟩ := hD.char
    refine ⟨?_, R.algebraMap_mem _, ?_, h01, fun τ => ⟨?_, ?_, fun a => R.algebraMap_mem _⟩⟩
    · rw [← map_natCast (algebraMap O Ω)]
      exact fun h => hp0 (hinj (h.trans (map_zero _).symm))
    · obtain ⟨u, rfl⟩ := hu
      refine ⟨algebraMap O Ω (↑u⁻¹ * w ^ (p - 2)), R.algebraMap_mem _, ?_⟩
      rw [← map_mul, ← map_natCast (algebraMap O Ω), mul_assoc, ← pow_succ,
        show p - 2 + 1 = p - 1 by have := hp.two_le; omega, huw, Units.inv_mul_cancel_left]
    · simp [(hχ τ).1]
    · simp [(hχ τ).2]
  have hbc := fun c (hc : mseg x c ≠ 0) =>
    _root_.GlobalTheory.CompanionTheory.Ar.Num.LatticeGoodBaseChange.main (D c) (chartRing O (mseg x) c) p _ _ (hchar _) (hD.base c hc) (hG c hc)
  have hfam := (_root_.GlobalTheory.CompanionTheory.Ar.Num.FamConstr.main O Ω K ι x hinj p hp w χ φ D hD).2
  obtain ⟨K', i1, i2, ι', i3, z, hz, hl⟩ := _root_.GlobalTheory.CompanionTheory.Ar.FlattenLines.main O Ω K ι x d hx hfn (Sg × Fin n)
    (fun j c => (D c).xId (fun a => algebraMap O Ω (χ j.1 a)) j.2) fun j =>
      ⟨((hfam j.1).2.1 j.2).1, fun c hc =>
        ⟨ne_bot (((hbc c hc).1 j.1).2.2.2 j.2),
          exists_finset (((hbc c hc).1 j.1).2.2.2 j.2)⟩⟩
  refine ⟨K', i1, i2, ι', i3, z, hz, fun τ i => ?_⟩
  obtain ⟨a, ha⟩ := hl (τ, i)
  refine ⟨1, a, one_ne_zero, fun c hc v => ?_⟩
  obtain ⟨hc', hle⟩ := ((_root_.GlobalTheory.CompanionTheory.Ar.Num.ChartNoethFrac.main O Ω K ι x).2.2 K' ι' z).2 c hc
  have h := (((hbc _ hc').2 Ω (chartRing O (mseg (joinCoord x z)) c) fun a ha => hle ha).2 τ).2.2 i
  rw [← ha c hc v]
  simp only [Algebra.algebraMap_self, RingHom.id_apply, Set.image_id'] at h
  simp only [pullFamily, h]

end GlobalTheory.CompanionTheory.Ar.FamLines
end

-- bundled from Development.AutomorphicSpectrum.Proofs.AlgebraProofs.MultiplicationByPFactorsFrobenius
section
open MvPowerSeries ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ GlobalTheory.CompanionTheory.Ar.Crv GlobalTheory.CompanionTheory.Ar.Conj

namespace GlobalTheory.CompanionTheory.Ar.Conj

theorem mulp_factors_frobenius : ∀ (R : Type) [CommRing R] (p : ℕ) [Fact p.Prime] [CharP R p] (d : ℕ) (O : Type) [CommRing O] [StarRing O] (B : FB R d O), ∃ V : Pt R 1 d, (∀ i, constantCoeff (V i) = 0) ∧ B.A.act (p : O) = comp1 V (ptPow R d p 0) ∧ lin V 1 = hw B p :=
  @PositivityTheory.HtPt.Cb.mulp_V

end GlobalTheory.CompanionTheory.Ar.Conj
end

-- bundled from Development.AutomorphicSpectrum.Proofs.AlgebraProofs.OrderPSquaredExtremalColengthStatement
section
open ReciprocityTheory.PGsh.L2 ReciprocityTheory.PGsh.Up GlobalTheory.CompanionTheory.Ar.GR
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi
open ReciprocityTheory.ChartRestriction.G.Chart (sp spMap)
open scoped CategoryTheory.Obj CategoryTheory.MonObj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.order_p_squared_extremal_colength : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (R : Type) [CommRing R] [Algebra R C], v.Integers R → v (p : C) < 1 → ∀ (N : Type) [AddCommGroup N] [Fintype N] [DecidableEq N], (∀ x : N, p • x = 0) → Fintype.card N = p ^ 2 → ∀ AA : HopfOrder (C := C) R N, ∀ cN, HasColen R v AA.carrier cN → cN ^ 2 = v (p : C) ^ (p ^ 2) → (∃ t : N, ∃ g ∈ AA.carrier, v (g t - g 0) = 1) → ∃ e : ZMod p × ZMod p ≃+ N, AA.carrier.map (LinearMap.funLeft R C (e : ZMod p × ZMod p → N)) = tens (Submodule.span R (Set.range fun (ψ : AddChar (ZMod p) C) (x : (ZMod p)) => ψ x)) (intFun R (ZMod p)) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.GR.OrdSplit.ord_split | exact GlobalTheory.CompanionTheory.Ar.GR.OrdSplit.ord_split | (intros; apply GlobalTheory.CompanionTheory.Ar.GR.OrdSplit.ord_split <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.AlgebraProofs.PowOneSeriesPFormula
section
open MvPowerSeries ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ GlobalTheory.CompanionTheory.Ar.Crv GlobalTheory.CompanionTheory.Ar.Conj

namespace GlobalTheory.CompanionTheory.Ar.Conj

theorem pow_one_series_in_p : ∀ (R : Type) [CommRing R] (p : ℕ) [Fact p.Prime] [CharP R p] (d : ℕ) (O : Type) [CommRing O] [StarRing O] (B : FB R d O), ∃ g : PS R 2 d, AxOne g ∧ pow1 B p = ev (n := 2) ![ptPow R d p 0, pt R d 1] g ∧ bil g 1 1 = am B p :=
  PositivityTheory.HtPt.Cb.first_power_char_p

end GlobalTheory.CompanionTheory.Ar.Conj
end

-- bundled from Development.AutomorphicSpectrum.Proofs.AlgebraProofs.TrivialFlagAtPrime
section
open MvPolynomial GlobalTheory.CompanionTheory.Ar.Num GroundTheory.Heights₂.Heights.NumbersDVR
open ReciprocityTheory.ChartRestriction.G.Geo (ChartBundle chartRing)
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.NumbersDVR.Bundles (mseg mcIdeal chartMon joinCoord bcCoord pullDeg liftVar fnField ck rootNum SameGeneric LatLE IsPull IsPullBC IsSubQuot QuotIso IsFrobPres FlagModel modelDeg)

namespace GlobalTheory.CompanionTheory.Ar.Num.TrivFlagAtRelay

theorem main : ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (Ω : Type) [Field Ω] [Algebra O Ω] (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)] (x : (Σ k, ι k) → Ω) (ϖ : O), Irreducible ϖ → ∀ (N : ℕ) (b : Fin N → K → ℤ), TrivFlagMod O ϖ x N b → ∀ (W : Ideal (MRing ι O)), IsMultiProjPrime W → (pointIdeal O x) ≤ W → (C ϖ : MRing ι O) ∈ W → TrivFlagAt W b :=
  @PositivityTheory.Xgn.t_trivflagmod_at

end GlobalTheory.CompanionTheory.Ar.Num.TrivFlagAtRelay
end

