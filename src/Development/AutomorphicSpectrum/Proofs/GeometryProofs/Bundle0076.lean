module

public import Mathlib
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0070
public import Development.AutomorphicSpectrum.Statements.AlgebraStatements.Bundle0001
public import Development.WeilBound.CoreStatements.TorusUniformisation.ChowMahlerFamilies.TestLeafLattice
public import Development.WeilBound.CoreStatements.TorusUniformisation.ChowMahlerFamilies.TestLiftExists
public import Development.WeilBound.CoreStatements.TorusUniformisation.ChowMahlerFamilies.Bundle0022
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.IsLatFamilyCongr
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.GlobalSectionsRankAlgClosed
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle0007
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle0005
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0025
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0007
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.AdelicGroupAlgebraActionInjective
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0002
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsHodgeLine
public import Development.WeilBound.CoreStatements.HomogeneousNonvanishing.MorphismEqOfGenericPointEq
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle0013
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsFlatAnIffIsConstMul
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.DvrData
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.WchartLePreimage
public import Development.WeilBound.CoreStatements.HodgeTatePoints.Bundle0041
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0015

@[expose] public section

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.ArithVarietyModelPrimeTotal
section
open AlgebraicGeometry CategoryTheory NumberField MvPolynomial ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Num GlobalTheory.CompanionTheory.Ar.Top
open GroundTheory.Heights₂.Heights.NumbersDVR (pointIdeal segreVec IsFlagFrame IsFlagPair SameGenericFibre IsModelOver divCycle)
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.NumbersDVR.Bundles (mseg fnField)
open Limits MonoidalCategory CartesianMonoidalCategory MonObj
open GlobalTheory.CompanionTheory.Ar.Num.FamEx GlobalTheory.CompanionTheory.Ar.BT

namespace GlobalTheory.CompanionTheory.Ar.Num.FamEx.TestPt

theorem w_mul_forms_le_af : GlobalTheory.CompanionTheory.Ar.GR.ZarhinStatement → GlobalTheory.CompanionTheory.Ar.GR.HodgeTateDatumStatement → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (O₀ : Type) [CommRing O₀] (β : O₀ →+* c.F) (Y : Model Xo c β) (S : Finset ℕ) (Ω : Type) [Field Ω] (K : Type) [Fintype K] [DecidableEq K] (J : K → Type) [∀ k, Fintype (J k)] (y : (Σ k, J k) → Ω) (𝔐 : HodgeCpt Y S y) (d : ℕ), IsArithVar (mCoordIdeal y) (d + 1) → 0 < D.p + D.q → ∀ (p : ℕ) [Fact p.Prime], p ∈ S → HT.HTFree 𝔐 p → p ≠ 2 → ¬ (p : ℤ) ∣ NumberField.discr E → ∀ (b : ∀ t, Fin (labelRk D t) → 𝔐.Li), (∀ t, LinearIndependent Ω (b t) ∧ Submodule.span Ω (Set.range (b t)) = 𝔐.Vgen t) → ∀ φ : Equiv.Perm (CMType H ⊕ CMType H), IsFrobLabels c p φ → ∀ (A : Type) [CommRing A] [Algebra A Ω] [IsIntegralClosure A ℤ Ω] (m : Ideal A) [m.IsPrime], (p : A) ∈ m → ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Algebra A O] [IsLocalization.AtPrime O m] [Algebra O Ω] [IsScalarTower A O Ω], ∀ (t₀ : CMType H ⊕ CMType H) (Sg : Type) [Fintype Sg] (e : Sg → CMType H ⊕ CMType H) (φ' : Equiv.Perm Sg) (F : Type) [Field F] [Fintype F] [CharP F p] (pq : (𝓞 E ⧸ Ideal.span {(p : 𝓞 E)}) →+* F) (sc : F →+ (𝓞 E ⧸ Ideal.span {(p : 𝓞 E)})) (w : O) (σ : Sg → F →+* IsLocalRing.ResidueField O), IsOrbit O 𝔐 p φ t₀ e φ' pq w σ → IsSec pq sc → ∀ (G : GenTors 𝔐 p) (c' : ∀ k, J k), mseg y c' ≠ 0 → ∀ (P : ChartPack G O c') (i : ∀ τ, (Fin (labelRk D (e τ)) → Ω) →ₗ[Ω] (Fin (D.p + D.q) → Ω)), (∀ τ : Sg, SeqHyp (CR O y c') (algebraMap O Ω w) (coordLat O y (𝔐.HT p (e τ)) (b (e τ)) c') (dotDual (CR O y c') (coordLat O y (𝔐.HT p (e τ).swap) (b (e τ).swap) c')) (i τ) (qMap P (b (e τ).swap)) ∧ ∀ σE : E →+* Ω, (∀ a : 𝓞 E, σE (a : E) = 𝔐.emb (e τ) a) → DualSeq P σE (𝔐.R p - 2) (coordLat O y (𝔐.HT p (e τ)) (b (e τ)) c') (b (e τ)) (i τ)) → (chartD e b pq sc w P i).Base (CR O y c') p (algebraMap O Ω w) → ∀ (C : Type) [Field C] [Algebra O C] [Algebra Ω C] [IsScalarTower O Ω C] (RC : Subalgebra O C), IsTestPt p (CR O y c') RC → ∀ χ : Sg → F →*₀ C, (∀ τ a (o : O), IsLocalRing.residue O o = σ τ a → χ τ a - algebraMap O C o ∈ RC ∧ ∀ u ∈ RC, u * (χ τ a - algebraMap O C o) ≠ 1) → ∀ [DecidableEq F] [Fintype (GlobalTheory.CompanionTheory.Ar.Num.FamEx.TestPt.NAdd E (D.p + D.q) p)] [DecidableEq (GlobalTheory.CompanionTheory.Ar.Num.FamEx.TestPt.NAdd E (D.p + D.q) p)], ∀ (v : Valuation C NNReal), (∀ c, c ∈ RC ↔ v c ≤ 1) → v (p : C) < 1 → GlobalTheory.CompanionTheory.Ar.GR.IsAbFactor p (GlobalTheory.CompanionTheory.Ar.Num.FamEx.TestPt.testOrd P RC) → ∀ τ, mulLat (algebraMap O C w) (stdLat RC _) ≤ ((chartD e b pq sc w P i).bc RC).af RC p (fun a => χ τ a) := by
  exact @PositivityTheory.Xgn.test_leaf_lattice

end GlobalTheory.CompanionTheory.Ar.Num.FamEx.TestPt
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.ArithVarietyPrimeHodgeEstimate
section
open AlgebraicGeometry CategoryTheory NumberField MvPolynomial ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Num GlobalTheory.CompanionTheory.Ar.Top
open GroundTheory.Heights₂.Heights.NumbersDVR (pointIdeal segreVec IsFlagFrame IsFlagPair SameGenericFibre IsModelOver divCycle)
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.NumbersDVR.Bundles (mseg fnField)
open Limits MonoidalCategory CartesianMonoidalCategory MonObj
open GlobalTheory.CompanionTheory.Ar.Num.FamEx GlobalTheory.CompanionTheory.Ar.BT

theorem GlobalTheory.CompanionTheory.Ar.Num.FamEx.TestPt.htLift : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (O₀ : Type) [CommRing O₀] (β : O₀ →+* c.F) (Y : Model Xo c β) (S : Finset ℕ) (Ω : Type) [Field Ω] (K : Type) [Fintype K] [DecidableEq K] (J : K → Type) [∀ k, Fintype (J k)] (y : (Σ k, J k) → Ω) (𝔐 : HodgeCpt Y S y) (d : ℕ), IsArithVar (mCoordIdeal y) (d + 1) → 0 < D.p + D.q → ∀ (p : ℕ) [Fact p.Prime], p ∈ S → HT.HTFree 𝔐 p → p ≠ 2 → ¬ (p : ℤ) ∣ NumberField.discr E → ∀ (b : ∀ t, Fin (labelRk D t) → 𝔐.Li), (∀ t, LinearIndependent Ω (b t) ∧ Submodule.span Ω (Set.range (b t)) = 𝔐.Vgen t) → ∀ φ : Equiv.Perm (CMType H ⊕ CMType H), IsFrobLabels c p φ → ∀ (A : Type) [CommRing A] [Algebra A Ω] [IsIntegralClosure A ℤ Ω] (m : Ideal A) [m.IsPrime], (p : A) ∈ m → ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Algebra A O] [IsLocalization.AtPrime O m] [Algebra O Ω] [IsScalarTower A O Ω], ∀ (t₀ : CMType H ⊕ CMType H) (Sg : Type) [Fintype Sg] (e : Sg → CMType H ⊕ CMType H) (φ' : Equiv.Perm Sg) (F : Type) [Field F] [Fintype F] [CharP F p] (pq : (𝓞 E ⧸ Ideal.span {(p : 𝓞 E)}) →+* F) (sc : F →+ (𝓞 E ⧸ Ideal.span {(p : 𝓞 E)})) (w : O) (σ : Sg → F →+* IsLocalRing.ResidueField O), IsOrbit O 𝔐 p φ t₀ e φ' pq w σ → IsSec pq sc → ∀ (G : GenTors 𝔐 p) (c' : ∀ k, J k), mseg y c' ≠ 0 → ∀ (P : ChartPack G O c') (i : ∀ τ, (Fin (labelRk D (e τ)) → Ω) →ₗ[Ω] (Fin (D.p + D.q) → Ω)), (∀ τ : Sg, SeqHyp (CR O y c') (algebraMap O Ω w) (coordLat O y (𝔐.HT p (e τ)) (b (e τ)) c') (dotDual (CR O y c') (coordLat O y (𝔐.HT p (e τ).swap) (b (e τ).swap) c')) (i τ) (qMap P (b (e τ).swap)) ∧ ∀ σE : E →+* Ω, (∀ a : 𝓞 E, σE (a : E) = 𝔐.emb (e τ) a) → DualSeq P σE (𝔐.R p - 2) (coordLat O y (𝔐.HT p (e τ)) (b (e τ)) c') (b (e τ)) (i τ)) → (chartD e b pq sc w P i).Base (CR O y c') p (algebraMap O Ω w) → ∀ (C : Type) [Field C] [Algebra O C] [Algebra Ω C] [IsScalarTower O Ω C] (RC : Subalgebra O C), IsTestPt p (CR O y c') RC → ∀ χ : Sg → F →*₀ C, (∀ τ a (o : O), IsLocalRing.residue O o = σ τ a → χ τ a - algebraMap O C o ∈ RC ∧ ∀ u ∈ RC, u * (χ τ a - algebraMap O C o) ≠ 1) → ∀ τ, ∃ hb : ((Fin (labelRk D (e τ)) → C) →ₗ[C] (Fin (D.p + D.q) → C)), Function.Injective hb ∧ LinearMap.range hb = LinearMap.ker (GlobalTheory.CompanionTheory.Ar.Num.FamEx.TestPt.bcLin C (qMap P (b (e τ).swap))) ∧ (stdLat RC _).map (GlobalTheory.CompanionTheory.Ar.Num.FamEx.TestPt.bcLin C (qMap P (b (e τ).swap))).toAddMonoidHom = ((chartD e b pq sc w P i).bc RC).omHT τ ∧ (stdLat RC _).comap hb.toAddMonoidHom = ((chartD e b pq sc w P i).bc RC).W τ ∧ (∀ b' c'', (b', c'') ∈ ((chartD e b pq sc w P i).bc RC).Del τ ↔ (algebraMap O C w) • b' ∈ stdLat RC _ ∧ c'' - (GlobalTheory.CompanionTheory.Ar.Num.FamEx.TestPt.bcLin C (qMap P (b (e τ).swap))) b' ∈ ((chartD e b pq sc w P i).bc RC).omHT τ) ∧ (∀ a b', (a, b') ∈ ((chartD e b pq sc w P i).bc RC).Gam τ ↔ (algebraMap O C w) • a ∈ ((chartD e b pq sc w P i).bc RC).W τ ∧ b' - hb a ∈ stdLat RC _) ∧ ∀ a ∈ ((chartD e b pq sc w P i).bc RC).W τ, hb a - GlobalTheory.CompanionTheory.Ar.Num.FamEx.TestPt.bcLin C (i τ) a ∈ mulLat (algebraMap O C w) (stdLat RC _) :=
  @PositivityTheory.Xgn.test_lift_exists
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.ArithVarietyPrimeHodgeTotal
section
open AlgebraicGeometry CategoryTheory NumberField MvPolynomial ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Num GlobalTheory.CompanionTheory.Ar.Top
open GroundTheory.Heights₂.Heights.NumbersDVR (pointIdeal segreVec IsFlagFrame IsFlagPair SameGenericFibre IsModelOver divCycle)
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.NumbersDVR.Bundles (mseg fnField)
open Limits MonoidalCategory CartesianMonoidalCategory MonObj
open GlobalTheory.CompanionTheory.Ar.Num.FamEx GlobalTheory.CompanionTheory.Ar.BT

namespace GlobalTheory.CompanionTheory.Ar.Num.FamEx.TestPt

theorem lifts_eq_frobenius_powers : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (O₀ : Type) [CommRing O₀] (β : O₀ →+* c.F) (Y : Model Xo c β) (S : Finset ℕ) (Ω : Type) [Field Ω] (K : Type) [Fintype K] [DecidableEq K] (J : K → Type) [∀ k, Fintype (J k)] (y : (Σ k, J k) → Ω) (𝔐 : HodgeCpt Y S y) (d : ℕ), IsArithVar (mCoordIdeal y) (d + 1) → 0 < D.p + D.q → ∀ (p : ℕ) [Fact p.Prime], p ∈ S → HT.HTFree 𝔐 p → p ≠ 2 → ¬ (p : ℤ) ∣ NumberField.discr E → ∀ (b : ∀ t, Fin (labelRk D t) → 𝔐.Li), (∀ t, LinearIndependent Ω (b t) ∧ Submodule.span Ω (Set.range (b t)) = 𝔐.Vgen t) → ∀ φ : Equiv.Perm (CMType H ⊕ CMType H), IsFrobLabels c p φ → ∀ (A : Type) [CommRing A] [Algebra A Ω] [IsIntegralClosure A ℤ Ω] (m : Ideal A) [m.IsPrime], (p : A) ∈ m → ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Algebra A O] [IsLocalization.AtPrime O m] [Algebra O Ω] [IsScalarTower A O Ω], ∀ (t₀ : CMType H ⊕ CMType H) (Sg : Type) [Fintype Sg] (e : Sg → CMType H ⊕ CMType H) (φ' : Equiv.Perm Sg) (F : Type) [Field F] [Fintype F] [CharP F p] (pq : (𝓞 E ⧸ Ideal.span {(p : 𝓞 E)}) →+* F) (sc : F →+ (𝓞 E ⧸ Ideal.span {(p : 𝓞 E)})) (w : O) (σ : Sg → F →+* IsLocalRing.ResidueField O), IsOrbit O 𝔐 p φ t₀ e φ' pq w σ → IsSec pq sc → ∀ (G : GenTors 𝔐 p) (c' : ∀ k, J k), mseg y c' ≠ 0 → ∀ (P : ChartPack G O c') (i : ∀ τ, (Fin (labelRk D (e τ)) → Ω) →ₗ[Ω] (Fin (D.p + D.q) → Ω)), (∀ τ : Sg, SeqHyp (CR O y c') (algebraMap O Ω w) (coordLat O y (𝔐.HT p (e τ)) (b (e τ)) c') (dotDual (CR O y c') (coordLat O y (𝔐.HT p (e τ).swap) (b (e τ).swap) c')) (i τ) (qMap P (b (e τ).swap)) ∧ ∀ σE : E →+* Ω, (∀ a : 𝓞 E, σE (a : E) = 𝔐.emb (e τ) a) → DualSeq P σE (𝔐.R p - 2) (coordLat O y (𝔐.HT p (e τ)) (b (e τ)) c') (b (e τ)) (i τ)) → (chartD e b pq sc w P i).Base (CR O y c') p (algebraMap O Ω w) → ∀ (C : Type) [Field C] [Algebra O C] [Algebra Ω C] [IsScalarTower O Ω C] (RC : Subalgebra O C), IsTestPt p (CR O y c') RC → ∀ χ : Sg → F →*₀ C, (∀ τ a (o : O), IsLocalRing.residue O o = σ τ a → χ τ a - algebraMap O C o ∈ RC ∧ ∀ u ∈ RC, u * (χ τ a - algebraMap O C o) ≠ 1) → ∃ (σ' : MulChar F RC) (ee : Sg → ℕ), GlobalTheory.CompanionTheory.Ar.GR.IsFund p σ' ∧ (∀ τ a, χ τ a = ((σ' ^ p ^ ee τ) a : RC)) ∧ ∀ τ, σ' ^ p ^ ee (φ' τ) = σ' ^ p ^ (ee τ + 1) :=
  @PositivityTheory.Xgn.test_character_exists

end GlobalTheory.CompanionTheory.Ar.Num.FamEx.TestPt
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.ArithVarietyPrimeHodgeValue
section
open AlgebraicGeometry CategoryTheory NumberField MvPolynomial ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Num GlobalTheory.CompanionTheory.Ar.Top
open GroundTheory.Heights₂.Heights.NumbersDVR (pointIdeal segreVec IsFlagFrame IsFlagPair SameGenericFibre IsModelOver divCycle)
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.NumbersDVR.Bundles (mseg fnField)
open Limits MonoidalCategory CartesianMonoidalCategory MonObj
open GlobalTheory.CompanionTheory.Ar.Num.FamEx GlobalTheory.CompanionTheory.Ar.BT

namespace GlobalTheory.CompanionTheory.Ar.Num.FamEx

theorem chart_om_eigQuot_projective : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (O₀ : Type) [CommRing O₀] (β : O₀ →+* c.F) (Y : Model Xo c β) (S : Finset ℕ) (Ω : Type) [Field Ω] (K : Type) [Fintype K] [DecidableEq K] (J : K → Type) [∀ k, Fintype (J k)] (y : (Σ k, J k) → Ω) (𝔐 : HodgeCpt Y S y) (d : ℕ), IsArithVar (mCoordIdeal y) (d + 1) → 0 < D.p + D.q → ∀ (p : ℕ) [Fact p.Prime], p ∈ S → HT.HTFree 𝔐 p → ¬ (p : ℤ) ∣ NumberField.discr E → ∀ (A : Type) [CommRing A] [Algebra A Ω] [IsIntegralClosure A ℤ Ω] (m : Ideal A) [m.IsPrime], (p : A) ∈ m → ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Algebra A O] [IsLocalization.AtPrime O m] [Algebra O Ω] [IsScalarTower A O Ω], ∀ (G : GenTors 𝔐 p) (c' : ∀ k, J k), mseg y c' ≠ 0 → ∀ (P : ChartPack G O c'), IsNoetherianRing (CR O y c') → (∀ 𝔮 : Ideal (CR O y c'), 𝔮.IsPrime → ∃ q : Cpt 𝔐.ξ, InChart 𝔐.ξ (mseg y) c' q ∧ (∀ o : O, algebraMap O Ω o ∈ regAt 𝔐.ξ q) ∧ ∀ x : Ω, x ∈ regAt 𝔐.ξ q ↔ ∃ u v : CR O y c', v ∉ 𝔮 ∧ x * (v : Ω) = (u : Ω)) → (∀ q : Cpt 𝔐.ξ, InChart 𝔐.ξ (mseg y) c' q → (∀ o : O, algebraMap O Ω o ∈ regAt 𝔐.ξ q) → HT.omP 𝔐 p q = Submodule.span (regAt 𝔐.ξ q) (P.Dh.om' : Set (Module.Dual Ω 𝔐.Li))) → Module.Projective (CR O y c') P.Dh.om' ∧ ∀ t : CMType H ⊕ CMType H, ∀ σ : E →+* Ω, (∀ a : 𝓞 E, σ (a : E) = 𝔐.emb t a) → Module.Projective (CR O y c') (P.Dh.omHT σ) :=
  @PositivityTheory.Xgn.sequence_projection_exists

end GlobalTheory.CompanionTheory.Ar.Num.FamEx
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.DualMapSnd
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.HtPull

theorem seccomp : ∀ (B : Type) [CommRing B] (Z Z' : Scheme.{0}) (x : Spec (CommRingCat.of B) ⟶ Z') (φ : Z' ⟶ Z) (W : Z.Opens) (h : ⊤ ≤ x ⁻¹ᵁ (φ ⁻¹ᵁ W)) (h' : ⊤ ≤ (x ≫ φ) ⁻¹ᵁ W) (s : Γ(Z, W)), secVal x (φ ⁻¹ᵁ W) h (φ.app W s) = secVal (x ≫ φ) W h' s := by
  intro B _ Z Z' x φ W h h' s
  unfold secVal
  rw [Scheme.Hom.comp_appLE]
  rfl

theorem secring : ∀ (B B' : Type) [CommRing B] [CommRing B'] (ψ : B →+* B') (Z : Scheme.{0}) (x : Spec (CommRingCat.of B) ⟶ Z) (W : Z.Opens) (h : ⊤ ≤ x ⁻¹ᵁ W) (h' : ⊤ ≤ (spMap ψ ≫ x) ⁻¹ᵁ W) (s : Γ(Z, W)), secVal (spMap ψ ≫ x) W h' s = ψ (secVal x W h s) := by
  intro B B' _ _ ψ Z x W h h' s
  unfold secVal
  have e : (spMap ψ ≫ x).appLE W ⊤ h' = x.appLE W ⊤ h ≫ (spMap ψ).appTop := by
    have e₁ : (spMap ψ).appTop = (spMap ψ).appLE ⊤ ⊤ le_top := by
      rw [Scheme.Hom.appTop, Scheme.Hom.app_eq_appLE]
      rfl
    rw [e₁]
    exact (Scheme.Hom.appLE_comp_appLE (spMap ψ) x W ⊤ ⊤ h _).symm
  rw [e]
  have n := Scheme.ΓSpecIso_naturality (CommRingCat.ofHom ψ)
  have n' : (Scheme.ΓSpecIso (CommRingCat.of B')).hom.hom ((spMap ψ).appTop.hom ((x.appLE W ⊤ h).hom s)) =
      ψ ((Scheme.ΓSpecIso (CommRingCat.of B)).hom.hom ((x.appLE W ⊤ h).hom s)) :=
    (ConcreteCategory.congr_hom n.symm ((x.appLE W ⊤ h).hom s)).symm
  exact n'

theorem eta : ∀ (X X' : Scheme.{0}) (G : Over X) [GrpObj G] (G' : Over X') [GrpObj G'] (f : X' ⟶ X) (φ : G'.left ⟶ G.left), IsGrpPullback G' G f φ → (η[G']).left ≫ φ = f ≫ (η[G]).left := by
  intro X X' G _ G' _ f φ h
  have e := congrArg (fun z => z.left) (map_one (pushHom h (𝟙_ (Over X'))))
  have e₁ : (1 : 𝟙_ (Over X') ⟶ G') = η[G'] := by rw [Hom.one_def]; simp
  rw [e₁] at e
  refine e.trans ?_
  show (toUnit _ ≫ η[G]).left = _
  simp

theorem tanin : ∀ (X : Scheme.{0}) (G : Over X) [GrpObj G] (q : X) (v : epsAt (X.fromSpecStalk q) ⟶ G), IsTanAt G _ v → ∀ W : G.left.Opens, (η[G]).left q ∈ W → ⊤ ≤ v.left ⁻¹ᵁ W := by
  intro X G _ q v hv W hq z _
  obtain ⟨p, rfl⟩ := LieCarrier.surjective_fst z
  have h1 : (1 : Over.mk (X.fromSpecStalk q) ⟶ G).left = X.fromSpecStalk q ≫ (η[G]).left := by
    rw [Hom.one_def]
    simp
  have e : v.left (Spec.map _ p) = (η[G]).left (X.fromSpecStalk q p) := congrArg (fun g => g p) (hv.trans h1)
  show v.left _ ∈ W
  refine e.symm ▸ ?_
  have h3 : X.fromSpecStalk q p ⤳ q := by
    have : X.fromSpecStalk q p ∈ Set.range (X.fromSpecStalk q) := ⟨p, rfl⟩
    rwa [Scheme.range_fromSpecStalk] at this
  exact (h3.map (η[G]).left.continuous).mem_open W.isOpen hq

theorem comp_ring {B B' : Type} [CommRing B] [CommRing B'] (ψ : B →+* B') {Z Z' : Scheme.{0}}
    (x' : Spec (CommRingCat.of B') ⟶ Z') (x : Spec (CommRingCat.of B) ⟶ Z) (φ : Z' ⟶ Z) (hx : x' ≫ φ = spMap ψ ≫ x)
    (W : Z.Opens) (h : ⊤ ≤ x' ⁻¹ᵁ (φ ⁻¹ᵁ W)) (h0 : ⊤ ≤ x ⁻¹ᵁ W) (s : Γ(Z, W)) :
    secVal x' (φ ⁻¹ᵁ W) h (φ.app W s) = ψ (secVal x W h0 s) := by
  have key : ∀ (t : Spec (CommRingCat.of B') ⟶ Z) (_ : t = spMap ψ ≫ x) (h2 : ⊤ ≤ t ⁻¹ᵁ W),
      secVal t W h2 s = ψ (secVal x W h0 s) := by
    rintro _ rfl h2
    exact secring B B' ψ Z x W h0 h2 s
  rw [seccomp B' Z Z' x' φ W h h s]
  exact key _ hx h

theorem dualMap_snd {R R' : Type} [CommRing R] [CommRing R'] (φ : R →+* R') (a : DualNumber R) :
    (dualMap φ a).snd = φ a.snd := by
  simp [dualMap]

end GlobalTheory.CompanionTheory.Ar.HtPull
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.EqOfEqGenericProjective
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar

namespace GlobalTheory.CompanionTheory.Ar

theorem maps_eq_of_eq_at_generic : ∀ (R : Type) [CommRing R] (Z W : Scheme.{0}) [IsIntegral Z] (s : W ⟶ Sp R) (Ω : Type) [Field Ω] (ξ : Sp Ω ⟶ Z) (f g : Z ⟶ W), IsProjOver s → (∀ q : Z, genPt ξ ⤳ q) → ξ ≫ f = ξ ≫ g → f = g :=
  @PositivityTheory.UnitarySelfGeneration.morphism_eq_of_generic_point_eq

end GlobalTheory.CompanionTheory.Ar
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.ExistsSubMemEigW
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Crv GlobalTheory.CompanionTheory.Ar.Conj GlobalTheory.CompanionTheory.Ar.Flat GlobalTheory.CompanionTheory.Ar.Fl
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Flat.DegZ

open Module

section Map

variable {R S : Type} [CommRing R] [CommRing S] {d : ℕ}

def vmap (f : R →+* S) (y : (Fin d → R) × (Fin d → R)) : (Fin d → S) × (Fin d → S) :=
  (fun i => f (y.1 i), fun i => f (y.2 i))

theorem vmap_add (f : R →+* S) (y y' : (Fin d → R) × (Fin d → R)) :
    vmap f (y + y') = vmap f y + vmap f y' := by
  refine Prod.ext (funext fun i => ?_) (funext fun i => ?_) <;> simp [vmap]

theorem vmap_sub (f : R →+* S) (y y' : (Fin d → R) × (Fin d → R)) :
    vmap f (y - y') = vmap f y - vmap f y' := by
  refine Prod.ext (funext fun i => ?_) (funext fun i => ?_) <;> simp [vmap]

theorem vmap_zero (f : R →+* S) : vmap f (0 : (Fin d → R) × (Fin d → R)) = 0 := by
  refine Prod.ext (funext fun i => ?_) (funext fun i => ?_) <;> simp [vmap]

theorem vmap_smul (f : R →+* S) (c : R) (y : (Fin d → R) × (Fin d → R)) :
    vmap f (c • y) = f c • vmap f y := by
  refine Prod.ext (funext fun i => ?_) (funext fun i => ?_) <;> simp [vmap]

theorem vmap_sum {A : Type} (s : Finset A) (f : R →+* S) (y : A → (Fin d → R) × (Fin d → R)) :
    vmap f (∑ i ∈ s, y i) = ∑ i ∈ s, vmap f (y i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using vmap_zero f
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, vmap_add, ih]

theorem vmap_comp {T : Type} [CommRing T] (f : R →+* S) (g : S →+* T) (y : (Fin d → R) × (Fin d → R)) :
    vmap g (vmap f y) = vmap (g.comp f) y := rfl

theorem lin_map (f : R →+* S) (φ : Germ.Pt R 1 d) (m : ℕ) :
    lin (fun i => MvPowerSeries.map f (φ i)) m = (lin φ m).map f := by
  ext i j
  simp [lin, Matrix.map_apply, MvPowerSeries.coeff_map]

theorem bil_map (f : R →+* S) (g : Germ.PS R 2 d) (m n : ℕ) :
    bil (MvPowerSeries.map f g) m n = (bil g m n).map f := by
  ext i j
  simp [bil, Matrix.map_apply, MvPowerSeries.coeff_map]

theorem map_mulVec' (f : R →+* S) (M : Matrix (Fin d) (Fin d) R) (v : Fin d → R) :
    (fun i => f (M.mulVec v i)) = (M.map f).mulVec fun i => f (v i) :=
  funext fun i => RingHom.map_mulVec _ _ _ _

theorem vmap_transH (f : R →+* S) (φ ψ : Germ.Pt R 1 d) (lam : Germ.PS R 2 d)
    (y : (Fin d → R) × (Fin d → R)) :
    vmap f (transH φ ψ lam y) = transH (fun i => MvPowerSeries.map f (φ i)) (fun i => MvPowerSeries.map f (ψ i))
      (MvPowerSeries.map f lam) (vmap f y) := by
  rw [transH_apply, transH_apply, lin_map, lin_map, bil_map]
  refine Prod.ext ?_ ?_
  · exact map_mulVec' f _ _
  · have h1 := map_mulVec' f (lin ψ 1).transpose (y.2 + (bil lam 1 1).transpose.mulVec y.1)
    have h2 := map_mulVec' f (bil lam 1 1).transpose y.1
    change (fun i => f ((lin ψ 1).transpose.mulVec (y.2 + (bil lam 1 1).transpose.mulVec y.1) i)) = _
    rw [h1, Matrix.transpose_map]
    congr 1
    change _ = (fun i => f (y.2 i)) + ((bil lam 1 1).map f).transpose.mulVec fun i => f (y.1 i)
    rw [← Matrix.transpose_map, ← h2]
    funext i
    simp

variable {O : Type} [CommRing O] [StarRing O]

theorem rho_map {f : R →+* S} {B : Germ.FB R d O} {B₂ : Germ.FB S d O} (h : IsMapOf f B B₂) (a : O) :
    rho B₂ a = (rho B a).map f := by
  have : B₂.A.act a = fun i => MvPowerSeries.map f (B.A.act a i) := funext (h.act a)
  rw [rho, this, lin_map]
  rfl

theorem vmap_rhoH {f : R →+* S} {B : Germ.FB R d O} {B₂ : Germ.FB S d O} (h : IsMapOf f B B₂) (a : O)
    (y : (Fin d → R) × (Fin d → R)) : vmap f (rhoH B a y) = rhoH B₂ a (vmap f y) := by
  rw [rhoH_apply, rhoH_apply, rho_map h, rho_map h, h.ad, bil_map]
  refine Prod.ext ?_ ?_
  · exact map_mulVec' f _ _
  · have h1 := map_mulVec' f (rho B (star a)).transpose y.2
    have h2 := map_mulVec' f (bil (B.ad a) 1 1).transpose y.1
    rw [Matrix.transpose_map] at h1 h2
    change (fun i => f (((rho B (star a)).transpose.mulVec y.2 - (bil (B.ad a) 1 1).transpose.mulVec y.1) i)) = _
    change _ = ((rho B (star a)).map f).transpose.mulVec (fun i => f (y.2 i)) -
      ((bil (B.ad a) 1 1).map f).transpose.mulVec fun i => f (y.1 i)
    rw [← Matrix.transpose_map, ← Matrix.transpose_map] at *
    rw [← h1, ← h2]
    funext i
    simp

end Map

end GlobalTheory.CompanionTheory.Ar.Flat.DegZ

namespace GlobalTheory.CompanionTheory.Ar.Flat.DegZ

section H

variable {E : Type} [Field E] [NumberField E] [StarRing (𝓞 E)]

def IsHBasis {R : Type} [CommRing R] {d r : ℕ} (B : Germ.FB R d (𝓞 E))
    (x : Fin r → (Fin d → R) × (Fin d → R)) : Prop :=
  LinearIndependent R (fun q : Fin r × Module.Free.ChooseBasisIndex ℤ (𝓞 E) =>
      rhoH B (RingOfIntegers.basis E q.2) (x q.1)) ∧
    Submodule.span R (Set.range fun q : Fin r × Module.Free.ChooseBasisIndex ℤ (𝓞 E) =>
      rhoH B (RingOfIntegers.basis E q.2) (x q.1)) = ⊤

def eigW {R : Type} [CommRing R] {d : ℕ} (B : Germ.FB R d (𝓞 E)) (τ : 𝓞 E →+* R) :
    Submodule R ((Fin d → R) × (Fin d → R)) :=
  ⨆ a : 𝓞 E, LinearMap.range (rhoH B a - τ a • LinearMap.id)

theorem vmap_mem_eigW {R S : Type} [CommRing R] [CommRing S] {d : ℕ} {f : R →+* S} {B : Germ.FB R d (𝓞 E)}
    {B₂ : Germ.FB S d (𝓞 E)} (h : IsMapOf f B B₂) (τ : 𝓞 E →+* R) {y : (Fin d → R) × (Fin d → R)}
    (hy : y ∈ eigW B τ) : vmap f y ∈ eigW B₂ (f.comp τ) := by
  refine Submodule.iSup_induction (motive := fun y => vmap f y ∈ eigW B₂ (f.comp τ)) _ hy ?_ ?_ ?_
  · rintro a _ ⟨w, rfl⟩
    refine Submodule.mem_iSup_of_mem a ⟨vmap f w, ?_⟩
    simp [vmap_sub, vmap_smul, vmap_rhoH h]
  · simp [vmap_zero]
  · intro y y' h1 h2
    rw [vmap_add]
    exact add_mem h1 h2

theorem eigW_induction {R : Type} [CommRing R] {d : ℕ} {B : Germ.FB R d (𝓞 E)} {τ : 𝓞 E →+* R}
    {P : (Fin d → R) × (Fin d → R) → Prop} {w : (Fin d → R) × (Fin d → R)} (hw : w ∈ eigW B τ)
    (hg : ∀ a y, P (rhoH B a y - τ a • y)) (h0 : P 0) (hadd : ∀ y y', P y → P y' → P (y + y')) : P w := by
  refine Submodule.iSup_induction (motive := P) _ hw ?_ h0 hadd
  rintro a _ ⟨y, rfl⟩
  exact hg a y

theorem exists_sub_mem_eigW {R : Type} [CommRing R] {d r : ℕ} {B : Germ.FB R d (𝓞 E)}
    {x : Fin r → (Fin d → R) × (Fin d → R)} (h : IsHBasis B x) (τ : 𝓞 E →+* R)
    (y : (Fin d → R) × (Fin d → R)) : ∃ m : Fin r → R, y - ∑ l, m l • x l ∈ eigW B τ := by
  have hy : y ∈ Submodule.span R (Set.range fun q : Fin r × Module.Free.ChooseBasisIndex ℤ (𝓞 E) =>
      rhoH B (RingOfIntegers.basis E q.2) (x q.1)) := h.2 ▸ trivial
  induction hy using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨q, rfl⟩ := hy
    classical
    refine ⟨Pi.single q.1 (τ (RingOfIntegers.basis E q.2)), ?_⟩
    refine Submodule.mem_iSup_of_mem (RingOfIntegers.basis E q.2) ⟨x q.1, ?_⟩
    simp [Pi.single_apply, ite_smul]
  | zero => exact ⟨0, by simp⟩
  | add y y' _ _ h1 h2 =>
    obtain ⟨m, hm⟩ := h1
    obtain ⟨m', hm'⟩ := h2
    refine ⟨m + m', ?_⟩
    have := add_mem hm hm'
    convert this using 1
    simp only [Pi.add_apply, add_smul, Finset.sum_add_distrib]
    abel
  | smul c y _ h1 =>
    obtain ⟨m, hm⟩ := h1
    refine ⟨c • m, ?_⟩
    have := (eigW B τ).smul_mem c hm
    convert this using 1
    simp only [Pi.smul_apply, smul_sub, Finset.smul_sum, smul_eq_mul, mul_smul]

theorem vmap_rel {R R' K L : Type} [CommRing R] [CommRing R'] [CommRing K] [CommRing L] {d r : ℕ} (v₀ : R →+* K)
    (v : R' →+* L) (j : L →+* K) (c : R' →+* R) (h : j.comp v = v₀.comp c) (φ' ψ' : Germ.Pt R 1 d)
    (lam' : Germ.PS R 2 d) (x' : (Fin d → R') × (Fin d → R')) (m : Fin r → R)
    (x : Fin r → (Fin d → R) × (Fin d → R)) :
    vmap v₀ (transH φ' ψ' lam' (vmap c x') - ∑ l, m l • x l) =
      transH (fun i => MvPowerSeries.map v₀ (φ' i)) (fun i => MvPowerSeries.map v₀ (ψ' i))
        (MvPowerSeries.map v₀ lam') (vmap j (vmap v x')) - ∑ l, v₀ (m l) • vmap v₀ (x l) := by
  rw [vmap_sub, vmap_transH, vmap_comp, vmap_comp, h, vmap_sum]
  simp only [vmap_smul]

end H

section Gen

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {X : Scheme.{0}} [StarRing (𝓞 E)]
  {Ω : Type} [Field Ω] {t : SAB H X} {ξ : Spec (CommRingCat.of Ω) ⟶ X} {d : ℕ}
  {M : LieModel t.G ξ (Fin d → Ω)}

def toVec (Ω : Type) [Field Ω] (d : ℕ) :
    ((Fin d → Ω) × (Fin d → Ω)) →ₗ[Ω] (Fin d → Ω) × Module.Dual Ω (Fin d → Ω) :=
  LinearMap.prodMap LinearMap.id (dotProductBilin Ω Ω)

def toH (S : GermSys t ξ M) (p : Cpt ξ) (y : (Fin d → X.presheaf.stalk p.1) × (Fin d → X.presheaf.stalk p.1)) :
    (Fin d → Ω) × Module.Dual Ω (Fin d → Ω) :=
  toVec Ω d (transH (S.φ p) (S.ψ p) (S.lam p) (vmap (genMap ξ p) y))

theorem toH_add (S : GermSys t ξ M) (p : Cpt ξ)
    (y y' : (Fin d → X.presheaf.stalk p.1) × (Fin d → X.presheaf.stalk p.1)) :
    toH S p (y + y') = toH S p y + toH S p y' := by
  simp [toH, vmap_add]

theorem toH_sub (S : GermSys t ξ M) (p : Cpt ξ)
    (y y' : (Fin d → X.presheaf.stalk p.1) × (Fin d → X.presheaf.stalk p.1)) :
    toH S p (y - y') = toH S p y - toH S p y' := by
  simp [toH, vmap_sub]

theorem toH_zero (S : GermSys t ξ M) (p : Cpt ξ) :
    toH S p (0 : (Fin d → X.presheaf.stalk p.1) × (Fin d → X.presheaf.stalk p.1)) = 0 := by
  simp [toH, vmap_zero]

theorem toH_smul (S : GermSys t ξ M) (p : Cpt ξ) (c : X.presheaf.stalk p.1)
    (y : (Fin d → X.presheaf.stalk p.1) × (Fin d → X.presheaf.stalk p.1)) :
    toH S p (c • y) = genMap ξ p c • toH S p y := by
  simp [toH, vmap_smul]

theorem toH_sum {A : Type} (s : Finset A) (S : GermSys t ξ M) (p : Cpt ξ)
    (y : A → (Fin d → X.presheaf.stalk p.1) × (Fin d → X.presheaf.stalk p.1)) :
    toH S p (∑ i ∈ s, y i) = ∑ i ∈ s, toH S p (y i) := by
  simp [toH, vmap_sum]

theorem toH_spec (S : GermSys t ξ M) (p q : Cpt ξ) (h : q.1 ⤳ p.1) {φ' ψ' : Germ.Pt (X.presheaf.stalk q.1) 1 d}
    {lam' : Germ.PS (X.presheaf.stalk q.1) 2 d}
    (he : transH (S.φ p) (S.ψ p) (S.lam p) = transH (S.φ q) (S.ψ q) (S.lam q) ∘ₗ
      transH (fun i => MvPowerSeries.map (genMap ξ q) (φ' i)) (fun i => MvPowerSeries.map (genMap ξ q) (ψ' i))
        (MvPowerSeries.map (genMap ξ q) lam'))
    (y : (Fin d → X.presheaf.stalk p.1) × (Fin d → X.presheaf.stalk p.1)) :
    toH S p y = toH S q (transH φ' ψ' lam' (vmap (X.presheaf.stalkSpecializes h).hom y)) := by
  have h1 : (genMap ξ q).comp (X.presheaf.stalkSpecializes h).hom = genMap ξ p :=
    RingHom.ext fun s => ProjectiveLinePlaces.genMap_specializes h q.2 p.2 s
  rw [toH, toH, vmap_transH, vmap_comp, h1, he]
  rfl

end Gen

end GlobalTheory.CompanionTheory.Ar.Flat.DegZ
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.FieldPointLiftsGenericFibre
section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj

namespace GlobalTheory.CompanionTheory.Ar.M0

theorem fieldPoint_lifts : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Geo.Tor.Level H) (Xo : Moduli D l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β), (letI := β.toAlgebra; IsFractionRing O c.F) → ∀ (K : Type) [Field K] (x : Sp K ⟶ Y.X), Set.range x ⊆ Set.range Y.j → ∃ y : Sp K ⟶ Xo.XF c, y ≫ Y.j = x :=
  @PositivityTheory.HtPt.Ml.lift_generic_point

end GlobalTheory.CompanionTheory.Ar.M0
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.QuasiFiniteGroupFinite
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar

namespace GlobalTheory.CompanionTheory.Ar.BT

theorem QFGroup.finite_of_qfGroup : ∀ (R : Type) [CommRing R] [IsDomain R] (T : Type) [CommGroup T] (Γ : BT.QFGroup R T), Finite T := by
  intro R _ _ T _ Γ
  have hqf : LocallyQuasiFinite Γ.G.hom := Γ.quasiFinite
  have hqc : QuasiCompact Γ.G.hom := Γ.quasiCompact
  let F := pullback Γ.G.hom (genPt R).hom
  let g : F ⟶ Spec (CommRingCat.of (FractionRing R)) := pullback.snd Γ.G.hom (genPt R).hom
  have hK : ∀ u v : Spec (CommRingCat.of (FractionRing R)), u = v := fun u v =>
    Subsingleton.elim (α := PrimeSpectrum (FractionRing R)) u v
  let b : Spec (CommRingCat.of (FractionRing R)) := (⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum (FractionRing R))
  have hgqf : LocallyQuasiFinite g := inferInstance
  have hgqc : QuasiCompact g := inferInstance
  have huniv : g ⁻¹' {b} = Set.univ := by
    ext x; simp [hK (g x) b]
  have hfin : Finite F := by
    have h := g.finite_preimage_singleton b
    rw [huniv] at h
    exact Set.finite_univ_iff.mp h
  have hw : ∀ t, (Γ.pt t).left ≫ Γ.G.hom = 𝟙 _ ≫ (genPt R).hom := fun t => by
    rw [Category.id_comp]; exact Over.w (Γ.pt t)
  let f : T → F := fun t => (pullback.lift _ _ (hw t)) b
  refine Finite.of_injective f ?_
  intro s t hst
  have h := congrArg (pullback.fst Γ.G.hom (genPt R).hom) hst
  simp only [f] at h
  simp only [← Scheme.Hom.comp_apply, pullback.lift_fst] at h
  exact Γ.pt_inj s t b b h

end GlobalTheory.CompanionTheory.Ar.BT
end

