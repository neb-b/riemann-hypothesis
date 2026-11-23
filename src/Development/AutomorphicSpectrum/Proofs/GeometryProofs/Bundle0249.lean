module

public import Mathlib
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0070
public import Development.AutomorphicSpectrum.Statements.AlgebraStatements.Bundle0001
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0239
public import Development.AutomorphicSpectrum.Statements.GeometryStatements.NonemptyEquivOfCardHom
public import Development.WeilBound.CoreStatements.TorusUniformisation.ChowMahlerFamilies.TestOrderSections
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.BoundaryChartFrameGrowth
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.BdryChart
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsFlatAnIffIsConstMul
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle0005
public import Development.AutomorphicSpectrum.Definitions.MetricPeriods.ClopenCondOnto
public import Development.AbelianVarietyTheory.Definitions.Uniformization.PointEqOfSubsingleton
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.BlowupProjections.BlowupProjStatement
public import Development.AutomorphicSpectrum.PublishedTheorems.Geometry₂.GagaSections
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle0004
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.IsLatFamilyCongr
public import Development.WeilBound.CoreStatements.TorusUniformisation.ChowMahlerFamilies.Bundle0033
public import Development.AutomorphicSpectrum.Statements.GeometryStatements.Bundle0003
public import Development.AutomorphicSpectrum.Statements.GeometryStatements.CmpSt
public import Development.AutomorphicSpectrum.Statements.GeometryStatements.Bundle0002
public import Development.AutomorphicSpectrum.Statements.GeometryStatements.HodgeComparisonCompatibility
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0003
public import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.Proportional
public import Development.WeilBound.CoreStatements.HomogeneousNonvanishing.PairIso
public import Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.Bundle0015
public import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.Bundle0042
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0030
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0066
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0048
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.ConjugateHermitianLineIsometries
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterRes
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.RationalSections.ThmISt
public import Development.AutomorphicSpectrum.Proofs.GlobalProofs.HasSncCoordsOfLocal
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1874
public import Development.WeilBound.CoreStatements.ProjectiveValuations.Bundle0002
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsHodgeLine
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
public import Development.AutomorphicSpectrum.Statements.GeometryStatements.Bundle0005
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0246
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.ToFirst
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.RootLinesUnramifiedPrimes
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0196
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.GlobalSectionsRankAlgClosed
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle0010
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle0007
public import Development.AutomorphicSpectrum.Statements.GeometryStatements.IsPolLatticePlane
public import Development.AutomorphicSpectrum.Statements.AlgebraStatements.Bundle0003
public import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.Birational
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0247
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0136
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0240
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle0012
public import Development.AbelianVarietyTheory.PublishedTheorems.SemiabelianTori.GeometricallyConnectedSplitTorusAff
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.LieMetricHermitianBundle
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0153
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0089
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ExistsOrthogonalLieMetric
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0096
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.FlagLineDegreeFormula
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsGrpPullback
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.AbelianSchemeQuotients.IsAbelianScheme
public import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0010
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0248

@[expose] public section

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.ArithVarietyPrimeGlobalRelay
section
open AlgebraicGeometry CategoryTheory NumberField MvPolynomial ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Num GlobalTheory.CompanionTheory.Ar.Top
open GroundTheory.Heights₂.Heights.NumbersDVR (pointIdeal segreVec IsFlagFrame IsFlagPair SameGenericFibre IsModelOver divCycle)
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.NumbersDVR.Bundles (mseg fnField)
open Limits MonoidalCategory CartesianMonoidalCategory MonObj
open GlobalTheory.CompanionTheory.Ar.Num.FamEx GlobalTheory.CompanionTheory.Ar.BT

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.CompanionTheory.Relay.arith_variety_prime_global_relay : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (O₀ : Type) [CommRing O₀] (β : O₀ →+* c.F) (Y : Model Xo c β) (S : Finset ℕ) (Ω : Type) [Field Ω] (K : Type) [Fintype K] [DecidableEq K] (J : K → Type) [∀ k, Fintype (J k)] (y : (Σ k, J k) → Ω) (𝔐 : HodgeCpt Y S y) (d : ℕ), IsArithVar (mCoordIdeal y) (d + 1) → 0 < D.p + D.q → ∀ (p : ℕ) [Fact p.Prime], p ∈ S → HT.HTFree 𝔐 p → p ≠ 2 → ¬ (p : ℤ) ∣ NumberField.discr E → ∀ (b : ∀ t, Fin (labelRk D t) → 𝔐.Li), (∀ t, LinearIndependent Ω (b t) ∧ Submodule.span Ω (Set.range (b t)) = 𝔐.Vgen t) → ∀ φ : Equiv.Perm (CMType H ⊕ CMType H), IsFrobLabels c p φ → ∀ (A : Type) [CommRing A] [Algebra A Ω] [IsIntegralClosure A ℤ Ω] (m : Ideal A) [m.IsPrime], (p : A) ∈ m → ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Algebra A O] [IsLocalization.AtPrime O m] [Algebra O Ω] [IsScalarTower A O Ω], ∀ (t₀ : CMType H ⊕ CMType H) (Sg : Type) [Fintype Sg] (e : Sg → CMType H ⊕ CMType H) (φ' : Equiv.Perm Sg) (F : Type) [Field F] [Fintype F] [CharP F p] (pq : (𝓞 E ⧸ Ideal.span {(p : 𝓞 E)}) →+* F) (sc : F →+ (𝓞 E ⧸ Ideal.span {(p : 𝓞 E)})) (w : O) (σ : Sg → F →+* IsLocalRing.ResidueField O), IsOrbit O 𝔐 p φ t₀ e φ' pq w σ → IsSec pq sc → ∀ (G : GenTors 𝔐 p) (c' : ∀ k, J k), mseg y c' ≠ 0 → ∀ (P : ChartPack G O c') (i : ∀ τ, (Fin (labelRk D (e τ)) → Ω) →ₗ[Ω] (Fin (D.p + D.q) → Ω)), (∀ τ : Sg, SeqHyp (CR O y c') (algebraMap O Ω w) (coordLat O y (𝔐.HT p (e τ)) (b (e τ)) c') (dotDual (CR O y c') (coordLat O y (𝔐.HT p (e τ).swap) (b (e τ).swap) c')) (i τ) (qMap P (b (e τ).swap)) ∧ ∀ σE : E →+* Ω, (∀ a : 𝓞 E, σE (a : E) = 𝔐.emb (e τ) a) → DualSeq P σE (𝔐.R p - 2) (coordLat O y (𝔐.HT p (e τ)) (b (e τ)) c') (b (e τ)) (i τ)) → (chartD e b pq sc w P i).Base (CR O y c') p (algebraMap O Ω w) → ∀ (C : Type) [Field C] [Algebra O C] [Algebra Ω C] [IsScalarTower O Ω C] (RC : Subalgebra O C), IsTestPt p (CR O y c') RC → ∀ χ : Sg → F →*₀ C, (∀ τ a (o : O), IsLocalRing.residue O o = σ τ a → χ τ a - algebraMap O C o ∈ RC ∧ ∀ u ∈ RC, u * (χ τ a - algebraMap O C o) ≠ 1) → ∀ [DecidableEq F] [Fintype (GlobalTheory.CompanionTheory.Ar.Num.FamEx.TestPt.NAdd E (D.p + D.q) p)] [DecidableEq (GlobalTheory.CompanionTheory.Ar.Num.FamEx.TestPt.NAdd E (D.p + D.q) p)], ∃ (AA : ReciprocityTheory.PGsh.L2.HopfOrder (C := C) RC (GlobalTheory.CompanionTheory.Ar.Num.FamEx.TestPt.NAdd E (D.p + D.q) p)) (AW : ReciprocityTheory.PGsh.L2.HopfOrder (C := C) RC (Fin (D.p + D.q) → F)), AA.carrier = (GlobalTheory.CompanionTheory.Ar.Num.FamEx.TestPt.testOrd P RC) ∧ AW.carrier = (GlobalTheory.CompanionTheory.Ar.Num.FamEx.TestPt.testOrdW P sc RC) ∧ AW.carrier.toAddSubgroup = ((chartD e b pq sc w P i).bc RC).M ∧ (∀ h ∈ AA.carrier, (fun x => h ((GlobalTheory.CompanionTheory.Ar.Num.FamEx.TestPt.toNAdd sc) ((GlobalTheory.CompanionTheory.Ar.Num.FamEx.TestPt.fromNAdd pq) x))) ∈ AA.carrier) ∧ GlobalTheory.CompanionTheory.Ar.GR.FStable F AW.carrier := by
  first | exact @PositivityTheory.Xgn.test_order_sections | exact PositivityTheory.Xgn.test_order_sections
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.BoundaryChartFrameGrowthStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl GlobalTheory.CompanionTheory.Ar.Flat Filter Topology Metric
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.boundary_chart_frame_growth : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (τ : E →+* ℂ) (σ : c.F →+* ℂ) (Φ : CFn Xo c) (n a : ℕ) (C : BdryChart Xo (σ.comp (IntermediateField.inclusion c.le).toRingHom) n a) (k' : C.V ⟶ Xo.XF c) (u₁ : Fin D.p → Fin C.g → C.R) (u₂ : Fin D.q → Fin C.g → C.R) (φ : (Fin n → ℂ) → ℂ), 1 ≤ D.p + D.q → σ (tauIn c τ H.rt) = H.rt0 → τ (H.rt : E) = H.rt0 → IsUnitAn τ σ Φ → k' ≫ pullback.fst _ _ = C.k → LinearIndependent ℂ (fun i b => C.ψ 0 (u₁ i b)) → LinearIndependent ℂ (fun i b => C.ψ 0 (u₂ i b)) → (∀ z ∈ punct n a 1, ∃ (v : Vecs (C.pt z ≫ k') D.p) (w : Vecs (C.pt z ≫ k') D.q), IsFramed Set.univ τ σ (C.pt z ≫ k') v w ∧ (∀ i, ∃ uu : Sp (DualNumber ℂ) ⟶ C.tV.G.left, uu ≫ C.m₂.φ = (v i).left ∧ uu ≫ C.m₁.φ = spMap (dualMap (C.ψ z)) ≫ (C.M.pt (u₁ i)).left) ∧ (∀ j, ∃ uu : Sp (DualNumber ℂ) ⟶ C.tV.G.left, uu ≫ C.m₂.φ = (w j).left ∧ uu ≫ C.m₁.φ = spMap (dualMap (C.ψ z)) ≫ (C.M.pt (u₂ j)).left) ∧ φ z = Φ (C.pt z ≫ k') v w) → ∃ (ρ : ℝ) (h : (Fin n → ℂ) → ℂ), 0 < ρ ∧ ρ ≤ 1 ∧ DifferentiableOn ℂ h (ball 0 ρ) ∧ (∀ z ∈ ball (0 : Fin n → ℂ) ρ, h z ≠ 0) ∧ ∀ z ∈ punct n a ρ, h z = φ z := by
  intro E _ _ _ H D l Xo c τ σ Φ n a C k' u₁ u₂ φ hpq hσ hτ hU hk h1 h2 hz
  exact GlobalTheory.CompanionTheory.Ar.Flat.exists_unit_extension_of_bdryChart E H D l Xo c τ σ Φ n a C k' u₁ u₂ φ hpq hσ hτ hU hk h1 h2 hz
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.CmFlagUnramifiedPrime
section
open AlgebraicGeometry CategoryTheory NumberField MvPolynomial ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Num GlobalTheory.CompanionTheory.Ar.Top
open GroundTheory.Heights₂.Heights.NumbersDVR (pointIdeal segreVec IsFlagFrame IsFlagPair SameGenericFibre IsModelOver divCycle)
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.NumbersDVR.Bundles (mseg fnField)
open Limits MonoidalCategory CartesianMonoidalCategory MonObj
open GlobalTheory.CompanionTheory.Ar.Num.FamEx GlobalTheory.CompanionTheory.Ar.BT

namespace GlobalTheory.CompanionTheory.Ar.Num.FamEx

theorem hodgeLattices_isVBOn_overPrime : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (O₀ : Type) [CommRing O₀] (β : O₀ →+* c.F) (Y : Model Xo c β) (S : Finset ℕ) (Ω : Type) [Field Ω] (K : Type) [Fintype K] (J : K → Type) (y : (Σ k, J k) → Ω) (𝔐 : HodgeCpt Y S y) (p : ℕ) [Fact p.Prime], p ∈ S → ¬ (p : ℤ) ∣ NumberField.discr E → (∀ (t : CMType H ⊕ CMType H) (q : Cpt 𝔐.ξ), (∀ r : ℕ, r.Prime → ¬ InFibre 𝔐.ξ r q) → 𝔐.HT p t q = 𝔐.dR t q) → ∀ t : CMType H ⊕ CMType H, (𝔐.dR t).IsVBOn (overPrime 𝔐.ξ p) (labelRk D t) (𝔐.Vgen t) ∧ (𝔐.HT p t).IsVBOn (overPrime 𝔐.ξ p) (labelRk D t) (𝔐.Vgen t) :=
  PositivityTheory.Xgn.vector_bundle_lattice_labels

end GlobalTheory.CompanionTheory.Ar.Num.FamEx
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.CmpPairOfInputs
section
open MvPolynomial AlgebraicGeometry CategoryTheory NumberField Filter Topology ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cmp
open ReciprocityTheory.ChartRestriction.G.AI.I1 (IsBlockMap pullDeg)
open ReciprocityTheory.ChartRestriction.G.AI.I4 (IsPullHerm imageZ blockFnField)
open scoped ComplexOrder

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Cmp.PairTop

theorem hermLine_ext {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {A B : HermLine ι}
    (ha : A.a = B.a) (hh : A.h = B.h) : A = B := by
  cases A; cases B; cases ha; cases hh; rfl

theorem combLine_equiv {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {J : Type} [Fintype J]
    (ℓ : J → HermLine ι) (n : J → ℤ) (e : J ≃ J) :
    Top.combLine (ℓ ∘ e) (n ∘ e) = Top.combLine ℓ n := by
  apply hermLine_ext
  · simp only [Top.combLine, Function.comp]
    exact Equiv.sum_comp e (fun j => n j • (ℓ j).a)
  · funext z
    simp only [Top.combLine, Function.comp]
    exact Equiv.prod_comp e (fun j => (ℓ j).h z ^ n j)

def relab {Ψ : Type} (π : Ψ ≃ Ψ) (N : ℕ) : Ψ × Fin N ≃ Ψ × Fin N := Equiv.prodCongr π (Equiv.refl _)

end GlobalTheory.CompanionTheory.Ar.Cmp.PairTop

namespace GlobalTheory.CompanionTheory.Ar.Cmp.PairTop

theorem degComb {Ψ : Type} [Fintype Ψ] [DecidableEq Ψ] {N : ℕ} {K : Type} [Fintype K] {ι : K → Type}
    [∀ k, Fintype (ι k)] (sing ref line : Ψ × Fin N → HermLine ι) (hl : ∀ a, (line a).a = (ref a).a)
    (hr : ∀ a, (ref a).a = (Top.combLine sing (fundOnRoot a)).a) (r : Ψ × Fin N) :
    (Top.combLine line (rootOnFund r)).a = (sing r).a := by
  have hfi := _root_.GlobalTheory.CompanionTheory.Ar.Cmp.rootOnFund_mul_fundOnRoot_inverse Ψ N
  simp only [Top.combLine] at hr ⊢
  simp_rw [hl, hr, Finset.smul_sum, smul_smul]
  rw [Finset.sum_comm]
  simp_rw [← Finset.sum_smul, (hfi r _).1, ite_smul, one_smul, zero_smul]
  simp

theorem cmpSt_of_eq (hC : CmpSt) (II : IntersectionSystem) (hII : IsFullIntersectionSystem II)
    (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)]
    (K₁ : Type) [Fintype K₁] (ι₁ : K₁ → Type) [∀ k, Fintype (ι₁ k)]
    (K₂ : Type) [Fintype K₂] (ι₂ : K₂ → Type) [∀ k, Fintype (ι₂ k)]
    (κ₁ : K₁ → K) (v₁ : (Σ k, ι₁ k) → Σ k, ι k) (κ₂ : K₂ → K) (v₂ : (Σ k, ι₂ k) → Σ k, ι k)
    (Ω : Type) [Field Ω] [CharZero Ω] (y : (Σ k, ι k) → Ω) (D : ℕ) (σ : Type) [Fintype σ] (S₁ S₂ : PB.AnSys D σ)
    (P₁ : Ideal (MRing ι₁)) (P₂ : Ideal (MRing ι₂)) (Re₁ : PB.Realis S₁ P₁) (Re₂ : PB.Realis S₂ P₂)
    (h₁ : mCoordIdeal (y ∘ v₁) = P₁) (h₂ : mCoordIdeal (y ∘ v₂) = P₂) (β : MRing ι) (b : K → ℕ)
    (hv₁ : IsBlockMap κ₁ v₁) (hv₂ : IsBlockMap κ₂ v₂) (hy : IsArithVar (mCoordIdeal y) (D + 1))
    (hβ : IsMultiHomog β b) (hβy : β ∉ mCoordIdeal y) (hA₁ : AlgOver Re₁) (hA₂ : AlgOver Re₂)
    (hS : ∀ a, SameSing Re₁ Re₂ (mCoordIdeal y) κ₁ v₁ κ₂ v₂ β a a) (w : Fin (D + 1) → σ) :
    Tendsto (fun t =>
      (IntermediateField.relfinrank (blockFnField (y ∘ v₁)) (blockFnField y) : ℝ) *
          II K₁ ι₁ P₁ (D + 1) (fun j => Re₁.line (w j) t) -
        (IntermediateField.relfinrank (blockFnField (y ∘ v₂)) (blockFnField y) : ℝ) *
          II K₂ ι₂ P₂ (D + 1) (fun j => Re₂.line (w j) t)) (𝓝[>] 0) (𝓝 0) := by
  subst h₁ h₂
  exact hC II hII K ι K₁ ι₁ K₂ ι₂ κ₁ v₁ κ₂ v₂ Ω y D σ S₁ S₂ Re₁ Re₂ β b hv₁ hv₂ hy hβ hβy hA₁ hA₂ hS w

end GlobalTheory.CompanionTheory.Ar.Cmp.PairTop

namespace GlobalTheory.CompanionTheory.Ar.Cmp.PairTop

theorem cmpPair : PB.Inputs → CmpSt → HodgeComparisonCompatibility → ThetaUnifAV → CmpPair := by
  intro hIn hC hT hU II hII E _ _ _ H D l Xo c O _ β Y g Φ hΦ π S n M M' T T' hβ hs hπ hA hR w
  classical
  obtain ⟨K, hK, ι, hι, κ, v, κ', v', Ω, hΩ, hΩ0, y, b, d, hbv, hbv', hP, hP', harith, hmh, hb, hne, hdeg, hiso⟩ :=
    _root_.PositivityTheory.UnitarySelfGeneration.pair_iso hT hU E H D l Xo c O β Y g Φ hΦ π S n M M' T T' hβ hs hπ hA hR
  have hJ := _root_.GlobalTheory.CompanionTheory.Ar.Cmp.hermLine_pull_blockMap M.K M.ι K ι κ v hbv
  have hJ' := _root_.GlobalTheory.CompanionTheory.Ar.Cmp.hermLine_pull_blockMap M'.K M'.ι K ι κ' v' hbv'
  have hmpp : IsMultiProjPrime (mCoordIdeal y) := harith.2.1
  obtain ⟨hc1, -, -, hc4⟩ := _root_.GlobalTheory.CompanionTheory.Ar.Cmp.IsoLines.isoLineOn_comb_trans_symm_pull K ι (mCoordIdeal y)
    {z | z ∈ mcPts (mCoordIdeal y) ∧ evC z b ≠ 0} hmpp (fun z hz => hz.1)
  let f := relab π (D.p + D.q)
  let Lr : CMType H × Fin (D.p + D.q) → HermLine ι := fun r => (hJ.1 (T.sing r)).exists.choose
  let Lr' : CMType H × Fin (D.p + D.q) → HermLine ι := fun r => (hJ'.1 (T'.sing (f r))).exists.choose
  have hLr : ∀ r, IsPullHerm κ v (T.sing r) (Lr r) := fun r => (hJ.1 (T.sing r)).exists.choose_spec
  have hLr' : ∀ r, IsPullHerm κ' v' (T'.sing (f r)) (Lr' r) := fun r => (hJ'.1 (T'.sing (f r))).exists.choose_spec
  have hfi := _root_.GlobalTheory.CompanionTheory.Ar.Cmp.rootOnFund_mul_fundOnRoot_inverse (CMType H) (D.p + D.q)
  have hfun : ∀ a, fundOnRoot (f a) ∘ f = fundOnRoot a := fun a => funext fun r => ((hfi a r).2 π).2
  have hsame : ∀ a, SameSing T.Re (T'.Re.comap f) (mCoordIdeal y) κ v κ' v' b a a := by
    intro a
    have e2 : Top.combLine T'.sing (fundOnRoot (f a)) = Top.combLine (T'.sing ∘ f) (fundOnRoot a) := by
      rw [← hfun a, combLine_equiv]
    refine _root_.GlobalTheory.CompanionTheory.Ar.Cmp.sameSing_of_isoLine K ι M.K M.ι M'.K M'.ι κ v κ' v' (mCoordIdeal y) M.P M'.P _ _ _ T.Sy (T'.Sy.comap f)
      T.Re (T'.Re.comap f) b a a (Top.combLine T.sing (fundOnRoot a)) (Top.combLine T'.sing (fundOnRoot (f a)))
      (Top.combLine Lr (fundOnRoot a)) (Top.combLine Lr' (fundOnRoot a)) hbv hbv'
      (hc4 _ _ κ v _ _ _ (fundOnRoot a) hbv hLr) ?_ (T.ref_deg a) (T'.ref_deg (f a)) (T.sing_eq a)
      (T'.sing_eq (f a)) hmpp (hc1 _ Lr Lr' (fundOnRoot a) fun r => hiso r _ _ (hLr r) (hLr' r))
    rw [e2]
    exact hc4 _ _ κ' v' _ (T'.sing ∘ f) Lr' (fundOnRoot a) hbv' hLr'
  have hword := cmpSt_of_eq hC II hII K ι M.K M.ι M'.K M'.ι κ v κ' v' Ω y _ _ T.Sy (T'.Sy.comap f) M.P M'.P
    T.Re (T'.Re.comap f) hP hP' b d hbv hbv' harith hmh hb T.alg T'.alg hsame
  have hδ : IntermediateField.relfinrank (blockFnField (y ∘ v)) (blockFnField y) * M.δ =
      IntermediateField.relfinrank (blockFnField (y ∘ v')) (blockFnField y) * M'.δ := by
    rw [T.δ_eq, T'.δ_eq, mul_left_comm, hdeg, mul_left_comm]
  have hsm : ∀ᶠ t in 𝓝[>] (0 : ℝ), ∀ a, IsSmoothHerm (T.Re.line a t) ∧ IsSmoothHerm (T'.Re.line (f a) t) := by
    rw [Filter.eventually_all]
    intro a
    filter_upwards [Ioo_mem_nhdsGT (T.Sy.reg a).1, Ioo_mem_nhdsGT (T'.Sy.reg (f a)).1] with t ht1 ht2
    exact ⟨T.Re.line_smooth a t ht1.1 ht1.2.le, T'.Re.line_smooth _ t ht2.1 ht2.2.le⟩
  have hroot : ∀ r, rootOnFund (f.symm r) = rootOnFund r ∘ f := fun r => funext fun a => by
    have h := ((hfi (f.symm r) a).2 π).1
    rw [← h]
    exact congrArg (fun x => rootOnFund x (f a)) (f.apply_symm_apply r)
  have hev : ∀ᶠ t in 𝓝[>] (0 : ℝ), (∀ a, IsSmoothHerm (T.Re.line a t) ∧ IsSmoothHerm (T'.Re.line (f a) t)) ∧
      (∀ r, (M.x t (f.symm r)).a = (Top.combLine (fun a => T.Re.line a t) (rootOnFund (f.symm r))).a ∧
        ∀ z ∈ mcPts M.P, (M.x t (f.symm r)).h z = (Top.combLine (fun a => T.Re.line a t) (rootOnFund (f.symm r))).h z) ∧
      ∀ r, (M'.x t r).a = (Top.combLine (fun a => T'.Re.line (f a) t) (rootOnFund (f.symm r))).a ∧
        ∀ z ∈ mcPts M'.P, (M'.x t r).h z = (Top.combLine (fun a => T'.Re.line (f a) t) (rootOnFund (f.symm r))).h z := by
    filter_upwards [hsm, T.line_eq, T'.line_eq] with t hs1 hl1 hl2
    refine ⟨hs1, fun r => ⟨?_, fun z hz => hl1 _ z hz⟩, fun r => ?_⟩
    · rw [M.x_deg, ← T.sing_deg]
      exact (degComb T.sing T.Re.ref (fun a => T.Re.line a t) (fun a => T.Re.line_deg a t) T.ref_deg _).symm
    · have e : Top.combLine (fun a => T'.Re.line (f a) t) (rootOnFund (f.symm r)) =
          Top.combLine (fun a => T'.Re.line a t) (rootOnFund r) := by
        rw [hroot r]
        exact combLine_equiv (fun a => T'.Re.line a t) (rootOnFund r) f
      rw [e]
      refine ⟨?_, fun z hz => hl2 r z hz⟩
      rw [M'.x_deg, ← T'.sing_deg]
      exact (degComb T'.sing T'.Re.ref (fun a => T'.Re.line a t) (fun a => T'.Re.line_deg a t) T'.ref_deg _).symm
  have hmain := _root_.GlobalTheory.CompanionTheory.Ar.Cmp.Root.cmp_root hIn II hII (CMType H) (D.p + D.q) M M' (CMType H × Fin (D.p + D.q))
    (fun t a => T.Re.line a t) (fun t a => T'.Re.line (f a) t) (fun r => rootOnFund (f.symm r)) f.symm _ _
    hne hδ hev hword (f ∘ w)
  simp only [Function.comp_apply, Equiv.symm_apply_apply] at hmain
  exact hmain

end GlobalTheory.CompanionTheory.Ar.Cmp.PairTop
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.CoordsStatement
section
open AlgebraicGeometry CategoryTheory Limits ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R ReciprocityTheory.ChartRestriction.G.Geo.ResK

namespace GlobalTheory.CompanionTheory.Geo.SncCoordsSide

theorem coordsStatement_side : ReciprocityTheory.ChartRestriction.G.Geo.ResK.CoordsStatement :=
  GlobalTheory.CompanionTheory.Geo.SncCoords.coordsStatement

end GlobalTheory.CompanionTheory.Geo.SncCoordsSide
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.FlagModelProjectiveEmbedding
section
open CategoryTheory AlgebraicGeometry NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj

theorem GlobalTheory.CompanionTheory.FlagMod.flagModel_iso_cells : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (Y : Model Xo c (RingHom.id c.F)) (p : GlobalTheory.FlagMod.LowRank.Proj (RingHom.id c.F)) (A : GlobalTheory.FlagMod.FieldFlag.Atlas Y p) (M' : GlobalTheory.FlagMod.FlagModel Y) (g : ∀ en : GlobalTheory.FlagEmb.En Dw.mult, M'.YY ⟶ PSpace c.F (GlobalTheory.FlagEmb.plN A.N en.1)) (κ : ∀ b, GlobalTheory.FlagEmb.Pm Dw.mult → (Sp (GlobalTheory.FlagEmb.CR Dw.mult (A.V b)) ⟶ M'.YY)), (∀ b w, IsOpenImmersion (κ b w)) → GlobalTheory.FlagMod.FieldFlag.Cells A M'.π g κ → SmoothOfRelativeDimension Dw.dim Y.s → ∀ M : GlobalTheory.FlagMod.FlagModel Y, ∃ h : M.YY ⟶ M'.YY, IsIso h ∧ h ≫ M'.π = M.π := by
  exact @DifferentiableLines.flag_model_projective_embedding_alt
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.HodgeCptGlobalNefBound
section
open AlgebraicGeometry CategoryTheory NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Crv GlobalTheory.CompanionTheory.Ar.Conj

namespace GlobalTheory.CompanionTheory.Ar.Conj

theorem hodge_cpt_global_nefness : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (Xo : ∀ l : Level H, Moduli D l) (Yl : ∀ (p : ℕ) (W : ValuationSubring ℂ), p.Prime → (p : ℂ) ∈ W.nonunits → LocalSystem Xo p W), (∀ p W hp hW i, (Yl p W hp hW i).SplitFibres ∧ (Yl p W hp hW i).N3) → ∀ (l : Level H) (c : Coeff l) (hg : ∀ p : ℕ, p.Prime → l.GoodAt p) (Y : Model (Xo l) c (algebraMap (𝓞 c.F) c.F)), (∀ (p : ℕ) (W : ValuationSubring ℂ) (hp : p.Prime) (hW : (p : ℂ) ∈ W.nonunits) (b : 𝓞 c.F →+* c.V W), (∀ x, ((b x : c.V W) : c.F) = (x : c.F)) → ReciprocityTheory.ChartRestriction.G.Geo.Tor.Dominates Y (Yl p W hp hW ⟨l, c, hg p hp⟩) b) → 1 ≤ D.p → 1 ≤ D.q → ∀ (S : Finset ℕ) [Fintype (CMType H)] (M : GlobalTheory.CompanionTheory.Ar.Top.RootModel (CMType H) (D.p + D.q)) (𝔐 : HodgeCpt Y S M.y) (Fl : 𝔐.Flag) (e : CMType H × Fin (D.p + D.q) → M.Ω), Fl.RootLines M.xdeg e → ∀ p : ℕ, p.Prime → 2 < p → p ∉ S → ¬ (p : ℤ) ∣ NumberField.discr E → ∀ mu : GlobalTheory.CompanionTheory.Ar.Top.Wt (CMType H) (D.p + D.q), GlobalTheory.CompanionTheory.Ar.Top.Dominant mu → GlobalTheory.CompanionTheory.Ar.Top.NefThreshold D.p p mu → M.NefAt p mu 0 := by
  intro E _ _ _ H D Xo Yl hYl l c hg Y hdom hp1 hq1 S _ M 𝔐 Fl e hRL p hp hp2 hpS hdisc mu hmu hthr
  have hfib := (_root_.GlobalTheory.CompanionTheory.Ar.GlobalFib.global_fibPF E H D Xo Yl hYl l c hg Y hdom).2 p hp
  obtain ⟨t⟩ := _root_.GlobalTheory.CompanionTheory.Ar.Conj.HcptTie.drTie_of_hodgeCpt E H D l (Xo l) c Y S M 𝔐 Fl e hRL p hp hpS hdisc hfib
  exact _root_.GlobalTheory.CompanionTheory.Ar.Conj.m2Model_holds (CMType H) (D.p + D.q) M D.p p E H t hp hp2 hp1 (by omega) mu hmu hthr

end GlobalTheory.CompanionTheory.Ar.Conj
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.HodgeCptGoodReductionDegreeStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hodge_cpt_good_reduction_degree : Out.WeilSt → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Geo.Tor.Level H) (Xo : Moduli D l) (c : Coeff l) (Y : Model Xo c (algebraMap (𝓞 c.F) c.F)) (S : Finset ℕ) (Ω : Type) [Field Ω] [CharZero Ω] (K : Type) [Fintype K] (J : K → Type) [∀ k, Fintype (J k)] (y : (Σ k, J k) → Ω) (A : HodgeCpt Y S y) (y₀ : Sp Ω ⟶ Xo.XF c) (d : ℕ), A.ξ ≫ A.f = y₀ ≫ Y.j → (∀ p : ℕ, p.Prime → (p : ℤ) ∣ NumberField.discr E → p ∈ S) → (∀ p ∈ S, HT.HTFree A p) → (∀ p ∈ S, ∃ ζ : Ω, IsPrimitiveRoot ζ (p ^ A.R p)) → A.IsCover d → ∃ (Ω' : Type) (_ : Field Ω') (_ : CharZero Ω') (i : Ω →+* Ω') (K' : Type) (_ : Fintype K') (J' : K' → Type) (_ : ∀ k, Fintype (J' k)) (y' : (Σ k, J' k) → Ω') (𝔐 : HodgeCpt Y S y') (g : 𝔐.X ⟶ A.X) (b : ∀ s, Fin (labelRk D s) → 𝔐.Li) (Li₀ : Type) (_ : AddCommGroup Li₀) (_ : Module 𝔐.Ω₀ Li₀) (M₀ : LieModel Y.t.G 𝔐.ξ₀ Li₀) (j : Li₀ →+ 𝔐.Li) (V₀ : CMType H ⊕ CMType H → Submodule 𝔐.Ω₀ Li₀), GlobalTheory.CompanionTheory.Ar.Dominates 𝔐.ξ A.ξ g i ∧ 𝔐.f = g ≫ A.f ∧ 𝔐.R = A.R ∧ (∀ p ∈ S, HT.HTFree 𝔐 p) ∧ (∀ s, Submodule.span Ω' (Set.range (b s)) = 𝔐.Vgen s) ∧ (∀ e, (𝔐.M.pt (j e)).left ≫ 𝔐.m.φ = spMap (dualMap 𝔐.fn) ≫ (M₀.pt e).left) ∧ (∀ s e, e ∈ V₀ s ↔ j e ∈ 𝔐.Vgen s) ∧ (letI := 𝔐.fn.toAlgebra; IsGenericFlag (Ω' := Ω') j V₀ b d) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.GenFlag.exists_genericFlag | exact GlobalTheory.CompanionTheory.Ar.GenFlag.exists_genericFlag | (intros; apply GlobalTheory.CompanionTheory.Ar.GenFlag.exists_genericFlag <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.HodgeTateFreeFlagLatticeLower
section
open CategoryTheory AlgebraicGeometry NumberField MvPolynomial GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.HT ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.NumbersDVR.Bundles

namespace GlobalTheory.CompanionTheory.Ar.HT

theorem hodgeTate_family_exists : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (S : Finset ℕ) (Ω : Type) [Field Ω] (K : Type) [Fintype K] (J : K → Type) [∀ k, Fintype (J k)] (y : (Σ k, J k) → Ω) (𝔐 : HodgeCpt Y S y) (p : ℕ) [Fact p.Prime] (hpS : p ∈ S) (hpq : 0 < D.p + D.q) (o : Type) [CommRing o] [Algebra o Ω] (ho : ∀ x : Ω, x ∈ (algebraMap o Ω).range ↔ ∃ (a : ℤ) (b : ℕ), ¬ p ∣ b ∧ x = (a : Ω) / (b : Ω)), ∃ (Dc : ∀ s : {s : ∀ k, J k // mseg y s ≠ 0}, HTChart (chartRing o (mseg y) s.1) Ω (cmConj E) p (𝔐.R p) (D.p + D.q) (Module.Dual Ω 𝔐.Li)), IsHTFamily 𝔐 p o Dc ∧ ∀ (s : {s : ∀ k, J k // mseg y s ≠ 0}) (κ : chartRing o (mseg y) s.1), PointHT → IsCp p (κ : Ω) → (Dc s).HasTestPoints κ :=
  GlobalTheory.CompanionTheory.HtLink.htat_link_of GlobalTheory.CompanionTheory.Ar.BT.ChartEx.htChartExists GlobalTheory.CompanionTheory.Ar.HT.hasTestPoints_of_tate

end GlobalTheory.CompanionTheory.Ar.HT
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.RootModelFlagHeight
section
noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField TensorProduct Filter Topology Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar

namespace GlobalTheory.CompanionTheory.Ar.TopFibre

section Values

variable {X : Scheme.{0}} {Ω : Type} [Field Ω] {R R' : Type} [CommRing R] [IsLocalRing R] [CommRing R'] [IsLocalRing R']

theorem centre_comp_specializes (ψ : R →+* R') (z : Spec (CommRingCat.of R) ⟶ X) :
    centre (Spec.map (CommRingCat.ofHom ψ) ≫ z) ⤳ centre z := by
  have h := (IsLocalRing.specializes_closedPoint
    (Spec.map (CommRingCat.ofHom ψ) (IsLocalRing.closedPoint R'))).map z.continuous
  exact h


set_option backward.isDefEq.respectTransparency false in
theorem stalkSpecializes_comp_stalkClosedPointTo (ψ : R →+* R') (z : Spec (CommRingCat.of R) ⟶ X) :
    X.presheaf.stalkSpecializes (centre_comp_specializes ψ z) ≫
        Scheme.stalkClosedPointTo (Spec.map (CommRingCat.ofHom ψ) ≫ z) =
      Scheme.stalkClosedPointTo z ≫ CommRingCat.ofHom ψ := by
  apply Spec.map_injective
  rw [← cancel_mono (X.fromSpecStalk (centre z)), Spec.map_comp, Spec.map_comp, Category.assoc, Category.assoc,
    Scheme.SpecMap_stalkSpecializes_fromSpecStalk]
  exact (Scheme.Spec_stalkClosedPointTo_fromSpecStalk _).trans
    (congrArg (Spec.map (CommRingCat.ofHom ψ) ≫ ·) (Scheme.Spec_stalkClosedPointTo_fromSpecStalk z).symm)

theorem valAt_comp {ξ : Spec (CommRingCat.of Ω) ⟶ X} (ψ : R →+* R') {z : Spec (CommRingCat.of R) ⟶ X} {a : Ω} {r : R}
    (h : ValAt ξ z a r) (h' : genPt ξ ⤳ centre (Spec.map (CommRingCat.ofHom ψ) ≫ z)) :
    ValAt ξ (Spec.map (CommRingCat.ofHom ψ) ≫ z) a (ψ r) := by
  obtain ⟨h1, s, rfl, rfl⟩ := h
  refine ⟨h', (X.presheaf.stalkSpecializes (centre_comp_specializes ψ z)).hom s, ?_, ?_⟩
  · have e := TopCat.Presheaf.stalkSpecializes_comp X.presheaf h' (centre_comp_specializes ψ z)
    have e2 := congrArg (fun q => (q ≫ Scheme.stalkClosedPointTo ξ).hom s) e
    exact e2
  · exact congrArg (fun q => q.hom s) (stalkSpecializes_comp_stalkClosedPointTo ψ z)

theorem coordsAt_comp {ξ : Spec (CommRingCat.of Ω) ⟶ X} (hall : ∀ q : X, genPt ξ ⤳ q) {K : Type} {J : K → Type}
    {y : (Σ k, J k) → Ω} {L L' : Type} [Field L] [Field L'] (ψ : L →+* L') {z : Spec (CommRingCat.of L) ⟶ X}
    {w : (Σ k, J k) → L} (h : CoordsAt ξ y z w) :
    CoordsAt ξ y (Spec.map (CommRingCat.ofHom ψ) ≫ z) fun p => ψ (w p) := by
  refine ⟨fun k => (h.1 k).imp fun c hc => hc.map ψ, fun k c hc => ?_⟩
  have hc' : IsUnit (w ⟨k, c⟩) := by
    rw [isUnit_iff_ne_zero] at hc ⊢
    exact fun h0 => hc (by simp [h0])
  refine ⟨(h.2 k c hc').1, fun i => ?_⟩
  obtain ⟨r, hr, e⟩ := (h.2 k c hc').2 i
  exact ⟨ψ r, valAt_comp ψ hr (hall _), by simp only [e, map_mul]⟩

end Values

theorem logBound_mono {C C' t : ℝ} (h0 : 0 ≤ C) (h : C ≤ C') (ht : 0 ≤ t) :
    C * Real.log (2 + C + t) + C ≤ C' * Real.log (2 + C' + t) + C' := by
  have h1 : 0 ≤ Real.log (2 + C + t) := Real.log_nonneg (by linarith)
  have h2 : Real.log (2 + C + t) ≤ Real.log (2 + C' + t) := Real.log_le_log (by linarith) (by linarith)
  have h3 := mul_le_mul h h2 h1 (h0.trans h)
  linarith

theorem fibreInput : N1ab → PartI → Geo.ResK.ResKStatement → GlobalTheory.Published.SemiAbelianHomExtension → SlopeBoundSt → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (Y : Model Xo c (algebraMap (𝓞 c.F) c.F)) (S : Finset ℕ) [Fintype (CMType H)] (R : Top.RootModel (CMType H) (D.p + D.q)) (𝔐 : HodgeCpt Y S R.y) (Fl : 𝔐.Flag) (e : CMType H × Fin (D.p + D.q) → R.Ω), 1 ≤ D.p + D.q → Fl.RootLines R.xdeg e → Ht.FibreInput R := by
  intro h1 h2 h3 h4 h5 E _ _ _ H D l Xo c Y S _ R 𝔐 Fl e hpq hroot
  obtain ⟨h, horth⟩ := _root_.GlobalTheory.CompanionTheory.Ar.MetricOrth.main E H D l Xo c Y S R.Ω R.K R.ι R.y 𝔐
  obtain ⟨C₁, hC₁, hslope⟩ := _root_.GlobalTheory.CompanionTheory.Ar.SlopeUnif.slope_unif h1 h2 h3 h4 h5 E H D l Xo c Y S R.Ω R.K R.ι R.y 𝔐 h hpq
  have hdeg : (fun r => (R.x 1 r).a) = R.xdeg := funext fun r => R.x_deg 1 r
  obtain ⟨C₂, hht⟩ := _root_.GlobalTheory.CompanionTheory.Ar.RootHt.root_height E H D l Xo c Y S R.Ω R.K R.ι R.y 𝔐 Fl h (R.x 1) e (R.x_smooth 1)
    (hdeg.symm ▸ hroot)
  have hch : CharZero R.Ω := (RingHom.charZero_iff 𝔐.cst.injective).1 inferInstance
  refine ⟨max C₁ C₂, hC₁.trans (le_max_left _ _), fun L _ _ w hw => ?_⟩
  obtain ⟨z₀, hz₀⟩ := _root_.GlobalTheory.CompanionTheory.Ar.algebraicPoint_extends_to_integers 𝔐.X R.Ω R.K R.ι R.y 𝔐.ξ hch 𝔐.all 𝔐.tie L w hw
  obtain ⟨L', _, _, ε, hs⟩ := hslope L z₀
  have hsm : Smooth 𝔐.t.G.hom := 𝔐.t.semi.smooth
  obtain ⟨B, MB, hB⟩ := _root_.GlobalTheory.CompanionTheory.Ar.lie_fibre_exists 𝔐.X R.Ω R.K R.ι R.y 𝔐.ξ 𝔐.t.G 𝔐.Li 𝔐.M h L'
    (spMap (RingOfIntegers.mapRingHom ε) ≫ z₀)
  obtain ⟨A, hA, hW⟩ := _root_.GlobalTheory.CompanionTheory.Ar.FlagFib.flag_fibre E H D l Xo c Y S R.Ω R.K R.ι R.y 𝔐 Fl h horth L' _ B MB hB
  have hpt : spMap (algebraMap (𝓞 L') L') ≫ spMap (RingOfIntegers.mapRingHom ε) ≫ z₀ =
      spMap ε ≫ spMap (algebraMap (𝓞 L) L) ≫ z₀ := by
    rw [← Category.assoc, ← Category.assoc, ← Spec.map_comp, ← Spec.map_comp]
    rfl
  have hz : CoordsAt 𝔐.ξ R.y (spMap (algebraMap (𝓞 L') L') ≫ spMap (RingOfIntegers.mapRingHom ε) ≫ z₀)
      fun p => ε (w p) := by
    rw [hpt]
    exact coordsAt_comp 𝔐.all ε hz₀
  have hext : ∀ r, Ht.lineHt (R.x 1 r) L' (fun p => ε (w p)) = Ht.lineHt (R.x 1 r) L w := fun r => by
    simpa using _root_.GlobalTheory.CompanionTheory.Ar.Ht.lineHt_map_scale R.K R.ι (R.x 1 r) L L' ε w (fun _ => 1) hw.1 fun _ => one_ne_zero
  obtain ⟨ha, hb⟩ := hht L' _ _ hz B MB A hB hW
  refine ⟨L', inferInstance, inferInstance, ε, B, A, hA, fun τ i => ?_, fun τ i => ?_, ?_⟩
  · rw [← hext]
    exact (ha τ i).trans (le_max_right _ _)
  · rw [← hext]
    exact (hb τ i).trans (le_max_right _ _)
  · exact (hs B MB hB).trans
      (EReal.coe_le_coe_iff.2 (logBound_mono hC₁ (le_max_left _ _) (le_max_right _ _)))

end GlobalTheory.CompanionTheory.Ar.TopFibre
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.SeparatedPropernessFgSubalgebraStatement
section
open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open scoped CategoryTheory.Obj CategoryTheory.MonObj
theorem _root_.GlobalTheory.T.separated_properness_fg_subalgebra : ∀ (k V : Type) [CommRing k] [IsNoetherianRing k] [CommRing V] [Algebra k V] (X : Scheme.{0}) (p : X ⟶ Sp k), IsSeparated p → LocallyOfFiniteType p → QuasiCompact p → IsProper (pullback.snd p (spMap (algebraMap k V))) → ∃ R : Subalgebra k V, R.FG ∧ IsProper (pullback.snd p (spMap (algebraMap k R))) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Approx.isProper_descends | exact GlobalTheory.CompanionTheory.Ar.Approx.isProper_descends | (intros; apply GlobalTheory.CompanionTheory.Ar.Approx.isProper_descends <;> assumption)
end

