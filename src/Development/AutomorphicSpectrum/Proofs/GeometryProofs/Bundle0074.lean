module

public import Mathlib
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0073
public import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.Bundle0023
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.IsLatFamilyCongr
public import Development.WeilBound.CoreStatements.TorusUniformisation.ChowMahlerFamilies.Bundle0020
public import Development.WeilBound.CoreStatements.TorusUniformisation.ChowMahlerFamilies.Bundle0019
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0058
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle0011
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Bundle0017
public import Development.AutomorphicSpectrum.Statements.GeometryStatements.Bundle0002
public import Development.AutomorphicSpectrum.RootSurvey.GeometrySurvey.ExistsTopDegreeCoefficientFormAndEqOnTopForms
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0001
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0002
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle0001
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0031
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0070
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0066
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0008
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle0008
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle0061
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.Bundle0009
public import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.RingKrullDimQuotientEqOfMemMinimalPrimes
public import GroundTheory.ArithmeticGeometry.AbelianVarieties.JacobianSmoothness.RingKrullDimLeRingKrullDimQuotientAddOne
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle0004
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.RationalSections.ThmISt
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0069
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0037
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0041
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0065

@[expose] public section

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.AlgebraicPointOverNumberField
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi
open GroundTheory.Heights₂.Heights TensorProduct
open GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Sl
open GlobalTheory.CompanionTheory.Ar.Sl.Reg

namespace GlobalTheory.CompanionTheory.Ar.Sl.Reg.Descend

theorem exists_numberField_point (C : Type) [Field C] [CharZero C] [Algebra.IsAlgebraic ℚ C]
    (X : Scheme.{0}) (π : X ⟶ Sp ℤ) [LocallyOfFiniteType π] (x : Sp C ⟶ X) :
    ∃ (K : Type) (_ : Field K) (_ : NumberField K) (e : K →+* C) (x' : Sp K ⟶ X),
      spMap e ≫ x' = x :=
  _root_.UpperTheory.Reformulated.B.SpecPointFactorsThroughNumberField.main C X π x

end GlobalTheory.CompanionTheory.Ar.Sl.Reg.Descend
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.ArithVarietyPrimeHodgeCount
section
open AlgebraicGeometry CategoryTheory NumberField MvPolynomial ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Num GlobalTheory.CompanionTheory.Ar.Top
open GroundTheory.Heights₂.Heights.NumbersDVR (pointIdeal segreVec IsFlagFrame IsFlagPair SameGenericFibre IsModelOver divCycle)
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.NumbersDVR.Bundles (mseg fnField)
open Limits MonoidalCategory CartesianMonoidalCategory MonObj
open GlobalTheory.CompanionTheory.Ar.Num.FamEx GlobalTheory.CompanionTheory.Ar.BT

namespace GlobalTheory.CompanionTheory.Ar.Num.FamEx

theorem mem_coordLat_iff_forall_om_mem_chartRing : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (O₀ : Type) [CommRing O₀] (β : O₀ →+* c.F) (Y : Model Xo c β) (S : Finset ℕ) (Ω : Type) [Field Ω] (K : Type) [Fintype K] [DecidableEq K] (J : K → Type) [∀ k, Fintype (J k)] (y : (Σ k, J k) → Ω) (𝔐 : HodgeCpt Y S y) (d : ℕ), IsArithVar (mCoordIdeal y) (d + 1) → 0 < D.p + D.q → ∀ (p : ℕ) [Fact p.Prime], p ∈ S → ∀ (b : ∀ t, Fin (labelRk D t) → 𝔐.Li), (∀ t, LinearIndependent Ω (b t) ∧ Submodule.span Ω (Set.range (b t)) = 𝔐.Vgen t) → ∀ (A : Type) [CommRing A] [Algebra A Ω] [IsIntegralClosure A ℤ Ω] (m : Ideal A) [m.IsPrime], (p : A) ∈ m → ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Algebra A O] [IsLocalization.AtPrime O m] [Algebra O Ω] [IsScalarTower A O Ω], ∀ (G : GenTors 𝔐 p) (c' : ∀ k, J k), mseg y c' ≠ 0 → ∀ (P : ChartPack G O c'), ∀ (s : CMType H ⊕ CMType H), (∀ a : 𝓞 E, ∃ o : O, algebraMap O Ω o = 𝔐.emb s a) → (∃ x ∈ differentIdeal ℤ (𝓞 E), ∃ o : O, algebraMap O Ω o * 𝔐.emb s x = 1) → (∀ (q : Cpt 𝔐.ξ), InChart 𝔐.ξ (mseg y) c' q → (∀ o : O, algebraMap O Ω o ∈ regAt 𝔐.ξ q) → ∀ x ∈ CR O y c', x ∈ regAt 𝔐.ξ q) → (∀ 𝔮 : Ideal (CR O y c'), 𝔮.IsPrime → ∃ q : Cpt 𝔐.ξ, InChart 𝔐.ξ (mseg y) c' q ∧ (∀ o : O, algebraMap O Ω o ∈ regAt 𝔐.ξ q) ∧ ∀ x : Ω, x ∈ regAt 𝔐.ξ q ↔ ∃ u v : CR O y c', v ∉ 𝔮 ∧ x * (v : Ω) = (u : Ω)) → (∀ q : Cpt 𝔐.ξ, InChart 𝔐.ξ (mseg y) c' q → (∀ o : O, algebraMap O Ω o ∈ regAt 𝔐.ξ q) → HT.omP 𝔐 p q = Submodule.span (regAt 𝔐.ξ q) (P.Dh.om' : Set (Module.Dual Ω 𝔐.Li))) → ∀ a : Fin (labelRk D s) → Ω, a ∈ coordLat O y (𝔐.HT p s) (b s) c' ↔ ∀ u ∈ P.Dh.om', u (∑ k, a k • b s k) ∈ CR O y c' :=
  PositivityTheory.Xgn.sequence_coordinates_exist

end GlobalTheory.CompanionTheory.Ar.Num.FamEx
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.ArithVarietyPrimeHodgeDegree
section
open AlgebraicGeometry CategoryTheory NumberField MvPolynomial ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Num GlobalTheory.CompanionTheory.Ar.Top
open GroundTheory.Heights₂.Heights.NumbersDVR (pointIdeal segreVec IsFlagFrame IsFlagPair SameGenericFibre IsModelOver divCycle)
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.NumbersDVR.Bundles (mseg fnField)
open Limits MonoidalCategory CartesianMonoidalCategory MonObj
open GlobalTheory.CompanionTheory.Ar.Num.FamEx GlobalTheory.CompanionTheory.Ar.BT

namespace GlobalTheory.CompanionTheory.Ar.Num.FamEx.Diff

theorem embedding_integers_and_different_unit : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (O₀ : Type) [CommRing O₀] (β : O₀ →+* c.F) (Y : Model Xo c β) (S : Finset ℕ) (Ω : Type) [Field Ω] (K : Type) [Fintype K] [DecidableEq K] (J : K → Type) [∀ k, Fintype (J k)] (y : (Σ k, J k) → Ω) (𝔐 : HodgeCpt Y S y) (d : ℕ), IsArithVar (mCoordIdeal y) (d + 1) → 0 < D.p + D.q → ∀ (p : ℕ) [Fact p.Prime], p ∈ S → ¬ (p : ℤ) ∣ NumberField.discr E → ∀ (A : Type) [CommRing A] [Algebra A Ω] [IsIntegralClosure A ℤ Ω] (m : Ideal A) [m.IsPrime], (p : A) ∈ m → ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Algebra A O] [IsLocalization.AtPrime O m] [Algebra O Ω] [IsScalarTower A O Ω], ∀ σ : E →+* Ω, (∀ a : 𝓞 E, ∃ o : O, algebraMap O Ω o = σ (a : E)) ∧ ∃ x ∈ differentIdeal ℤ (𝓞 E), ∃ o : O, algebraMap O Ω o * σ (x : E) = 1 :=
  @PositivityTheory.Xgn.sequence_differentials_exist

end GlobalTheory.CompanionTheory.Ar.Num.FamEx.Diff
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.ChartPointInChartDominated
section
open AlgebraicGeometry CategoryTheory NumberField MvPolynomial ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Num GlobalTheory.CompanionTheory.Ar.Top
open GroundTheory.Heights₂.Heights.NumbersDVR (pointIdeal segreVec IsFlagFrame IsFlagPair SameGenericFibre IsModelOver divCycle)
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.NumbersDVR.Bundles (mseg fnField)
open Limits MonoidalCategory CartesianMonoidalCategory MonObj
open GlobalTheory.CompanionTheory.Ar.Num.FamEx GlobalTheory.CompanionTheory.Ar.BT

namespace GlobalTheory.CompanionTheory.Ar.Num.FamEx

theorem chartPoint_inChart_dominated : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (O₀ : Type) [CommRing O₀] (β : O₀ →+* c.F) (Y : Model Xo c β) (S : Finset ℕ) (Ω : Type) [Field Ω] (K : Type) [Fintype K] [DecidableEq K] (J : K → Type) [∀ k, Fintype (J k)] (y : (Σ k, J k) → Ω) (𝔐 : HodgeCpt Y S y) (d : ℕ), IsArithVar (mCoordIdeal y) (d + 1) → ∀ (p : ℕ) [Fact p.Prime], p ∈ S → ∀ (A : Type) [CommRing A] [Algebra A Ω] [IsIntegralClosure A ℤ Ω] (m : Ideal A) [m.IsPrime], (p : A) ∈ m → ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Algebra A O] [IsLocalization.AtPrime O m] [Algebra O Ω] [IsScalarTower A O Ω] (G : GenTors 𝔐 p) (c' : ∀ k, J k), mseg y c' ≠ 0 → ∀ (P : ChartPack G O c') (z : Spec (CommRingCat.of (CR O y c'))), InChart 𝔐.ξ (mseg y) c' ⟨P.x z, 𝔐.all _⟩ ∧ (∀ o : O, algebraMap O Ω o ∈ regAt 𝔐.ξ ⟨P.x z, 𝔐.all _⟩) ∧ ∀ a ∈ regAt 𝔐.ξ ⟨P.x z, 𝔐.all _⟩, ∃ r s : CR O y c', s ∉ z.asIdeal ∧ (s : Ω) * a = r :=
  @PositivityTheory.Xgn.exists_function_at_point

end GlobalTheory.CompanionTheory.Ar.Num.FamEx
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.DeltaTermLogDegreeBound
section
open MvPolynomial NumberField Filter Topology ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I2 GlobalTheory.CompanionTheory.Ar.Top GlobalTheory.CompanionTheory.Ar.Flat

namespace GlobalTheory.CompanionTheory.Ar.Flat

theorem deltaTerm_one : ∀ (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N : ℕ) (j p : ℕ) (τ : Ψ) (fr : ℕ → Ψ ⊕ Ψ), j ≤ N → 2 ≤ p → ∃ e : ℝ, |e| ≤ N / ((p : ℝ) - 1) ∧ ((∀ n, ∃ σ, fr n = Sum.inl σ) → e = 0) ∧ ((∀ n, (∃ σ, fr n = Sum.inl σ) ↔ Odd n) → e = ((N : ℝ) - 2 * j) * p / ((p : ℝ) ^ 2 - 1)) ∧ ∀ Q : RP Ψ N, deltaTerm j p τ fr 1 Q = e * Real.log p * degFl Q := by
  intro Ψ _ _ N j p τ fr hj hp
  refine ⟨Bound₂.ep N j p fr, Bound₂.abs_ep_le hj hp fr, fun h => ?_, fun h => ?_,
    fun Q => Bound₂.delta_one hj p τ fr Q⟩
  · have e : (fun n : ℕ => ((p : ℝ)⁻¹) ^ (n + 1) * Bound₂.rk N j (fr n)) =
        fun n : ℕ => (j : ℝ) / (p : ℝ) ^ (n + 1) := by
      funext n
      obtain ⟨σ, hσ⟩ := h n
      rw [hσ, inv_pow, div_eq_inv_mul]
      rfl
    unfold Bound₂.ep
    rw [e, (ep_split p j hp).tsum_eq, sub_self]
  · have e : (fun n : ℕ => ((p : ℝ)⁻¹) ^ (n + 1) * Bound₂.rk N j (fr n)) =
        fun n : ℕ => (if Even (n + 1) then (j : ℝ) else (N : ℝ) - j) / (p : ℝ) ^ (n + 1) := by
      funext n
      rw [inv_pow, div_eq_inv_mul]
      congr 1
      rcases hs : fr n with σ | σ
      · have : Odd n := (h n).1 ⟨σ, hs⟩
        rw [if_pos this.add_one]
        rfl
      · have : ¬ Odd n := fun ho => by
          obtain ⟨σ', h'⟩ := (h n).2 ho
          rw [hs] at h'
          cases h'
        rw [if_neg (by simpa [Nat.even_add_one] using this)]
        rfl
    unfold Bound₂.ep
    rw [e, (ep_inert p N j hp hj).1.tsum_eq]
    ring

end GlobalTheory.CompanionTheory.Ar.Flat
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.DotDualLatticeFamily
section
open AlgebraicGeometry CategoryTheory NumberField MvPolynomial ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Num GlobalTheory.CompanionTheory.Ar.Top
open GroundTheory.Heights₂.Heights.NumbersDVR (pointIdeal segreVec IsFlagFrame IsFlagPair SameGenericFibre IsModelOver divCycle)
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.NumbersDVR.Bundles (mseg fnField)
open Limits MonoidalCategory CartesianMonoidalCategory MonObj
open GlobalTheory.CompanionTheory.Ar.Num.FamEx GlobalTheory.CompanionTheory.Ar.BT

namespace GlobalTheory.CompanionTheory.Ar.Num.FamEx

theorem dotDual_latFamily : ∀ (O : Type) [CommRing O] (Ω : Type) [Field Ω] [Algebra O Ω] (K : Type) [Fintype K] (J : K → Type) [∀ k, Fintype (J k)] (y : (Σ k, J k) → Ω) (r : ℕ) (Γ : (∀ k, J k) → AddSubgroup (Fin r → Ω)), IsLatFamily O y Γ → (∀ c, mseg y c ≠ 0 → LocFree (chartRing O (mseg y) c) r (Γ c)) → IsLatFamily O y (fun c => dotDual (chartRing O (mseg y) c) (Γ c)) ∧ ∀ c, mseg y c ≠ 0 → LocFree (chartRing O (mseg y) c) r (dotDual (chartRing O (mseg y) c) (Γ c)) :=
  @PositivityTheory.Xgn.dual_lattice_family

end GlobalTheory.CompanionTheory.Ar.Num.FamEx
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.DvrLocalizationConstants
section
open AlgebraicGeometry CategoryTheory NumberField MvPolynomial ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Num GlobalTheory.CompanionTheory.Ar.Top
open GroundTheory.Heights₂.Heights.NumbersDVR (pointIdeal segreVec IsFlagFrame IsFlagPair SameGenericFibre IsModelOver divCycle)
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.NumbersDVR.Bundles (mseg fnField)
open Limits MonoidalCategory CartesianMonoidalCategory MonObj
open GlobalTheory.CompanionTheory.Ar.Num.FamEx GlobalTheory.CompanionTheory.Ar.BT

namespace GlobalTheory.CompanionTheory.Ar.Num.FamEx

theorem chart_points_over_place : ∀ (X : Scheme.{0}) (Ω : Type) [Field Ω] (ξ : Spec (CommRingCat.of Ω) ⟶ X) (K : Type) [Fintype K] [DecidableEq K] (J : K → Type) [∀ k, Fintype (J k)] (y : (Σ k, J k) → Ω), CoordTie ℤ ξ (mseg y) → ∀ (A : Type) [CommRing A] [Algebra A Ω], HasConstants ℤ A y → ∀ (m : Ideal A) [m.IsPrime] (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Algebra A O] [IsLocalization.AtPrime O m] [Algebra O Ω] [IsScalarTower A O Ω] (c : ∀ k, J k), mseg y c ≠ 0 → (∀ a ∈ chartRing O (mseg y) c, ∀ q : Cpt ξ, InChart ξ (mseg y) c q → (∀ o : O, algebraMap O Ω o ∈ regAt ξ q) → a ∈ regAt ξ q) ∧ (∀ P : Ideal (chartRing O (mseg y) c), P.IsPrime → ∃ q : Cpt ξ, InChart ξ (mseg y) c q ∧ (∀ o : O, algebraMap O Ω o ∈ regAt ξ q) ∧ ∀ s : chartRing O (mseg y) c, s ∉ P ↔ unitAt ξ q (s : Ω)) ∧ (∀ q : Cpt ξ, InChart ξ (mseg y) c q → (∀ o : O, algebraMap O Ω o ∈ regAt ξ q) → ∀ a ∈ regAt ξ q, ∃ s ∈ chartRing O (mseg y) c, unitAt ξ q s ∧ s * a ∈ chartRing O (mseg y) c) ∧ (∀ q : Cpt ξ, InChart ξ (mseg y) c q → (∀ o : O, algebraMap O Ω o ∈ regAt ξ q) → ∀ U : X.Opens, q.1 ∈ U → ∃ g ∈ chartRing O (mseg y) c, unitAt ξ q g ∧ ∀ q' : Cpt ξ, InChart ξ (mseg y) c q' → (∀ o : O, algebraMap O Ω o ∈ regAt ξ q') → unitAt ξ q' g → q'.1 ∈ U) :=
  @PositivityTheory.Xgn.lattice_chart_points

end GlobalTheory.CompanionTheory.Ar.Num.FamEx
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.EigenspaceDecompositionInternal
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj GlobalTheory.CompanionTheory.Ar

namespace GlobalTheory.CompanionTheory.Ar

open Polynomial NumberField

theorem iSupIndep_eigSp {Ω E F I : Type} [Field Ω] [CharZero Ω] [AddCommGroup E] [Module Ω E] [Field F] [NumberField F]
    (ρ : 𝓞 F →+* Module.End Ω E) (σ : I → (𝓞 F →+* Ω)) (hσ : Function.Injective σ) :
    iSupIndep fun s => eigSp ρ (σ s) := by
  obtain ⟨θ, -, -, -, -, hgen⟩ := Cusp.exists_integral_generator F
  have hagree : ∀ (τ : 𝓞 F →+* Ω) (P : ℤ[X]), τ (aeval θ P) = aeval (τ θ) P := fun τ P =>
    (aeval_algHom_apply τ.toIntAlgHom θ P).symm
  have hinj : Function.Injective fun s => σ s θ := by
    intro s t hst
    apply hσ
    ext a
    obtain ⟨n, P, hn, hP⟩ := hgen a
    have h1 := hagree (σ s) P
    have h2 := hagree (σ t) P
    have hst' : σ s θ = σ t θ := hst
    rw [hst', ← h2, ← hP, map_mul, map_mul, map_intCast, map_intCast] at h1
    exact mul_left_cancel₀ (by exact_mod_cast hn) h1
  refine ((Module.End.eigenspaces_iSupIndep (ρ θ)).comp hinj).mono fun s x hx => ?_
  have hx' := (Submodule.mem_iInf _).1 hx θ
  rw [LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.smul_apply, LinearMap.id_apply, sub_eq_zero] at hx'
  exact Module.End.mem_eigenspace_iff.2 hx'

theorem isInternal_eigSp : ∀ (Ω : Type) [Field Ω] [CharZero Ω] (E : Type) [AddCommGroup E] [Module Ω E] (F : Type) [Field F] [NumberField F] (ρ : NumberField.RingOfIntegers F →+* Module.End Ω E) (I : Type) [Fintype I] [DecidableEq I] (σ : I → (NumberField.RingOfIntegers F →+* Ω)), Function.Injective σ → Fintype.card I = Module.finrank ℚ F → DirectSum.IsInternal fun s => eigSp ρ (σ s) := by
  intro Ω _ _ E _ _ F _ _ ρ I _ _ σ hσ hcard
  exact DirectSum.isInternal_submodule_of_iSupIndep_of_iSup_eq_top (iSupIndep_eigSp ρ σ hσ)
    (Cusp.iSup_eigSp_eq_top ρ σ hσ hcard)

end GlobalTheory.CompanionTheory.Ar
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.ExistsPrimeDividingUniformizerStatement
section
open AlgebraicGeometry CategoryTheory Limits NumberField IsDedekindDomain MvPolynomial
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Flat GlobalTheory.CompanionTheory.Ar.Fl
open scoped ComplexOrder
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_prime_dividing_uniformizer : ∀ (F' : Type) [Field F'] [NumberField F'] (v : HeightOneSpectrum (𝓞 F')) (π : F'), v.valuation F' π = WithZero.exp (-1 : ℤ) → ∃ ℓ : ℕ, ℓ.Prime ∧ v.valuation F' ((ℓ : F') / π) ≤ 1 := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Rescar.exists_prime_div_uniformiser | exact GlobalTheory.CompanionTheory.Ar.Rescar.exists_prime_div_uniformiser | (intros; apply GlobalTheory.CompanionTheory.Ar.Rescar.exists_prime_div_uniformiser <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.ExistsStandardSmoothLocalization
section
noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.SegreChart

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I4 GroundTheory.Heights₂.Heights.HilbertSamuel

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {Ω : Type} [Field Ω] [CharZero Ω]


omit [CharZero Ω] in
theorem segre_update_ratio [DecidableEq K] (y : (Σ k, ι k) → Ω) (c : ∀ k, ι k) (hc : ∀ k, y ⟨k, c k⟩ ≠ 0)
    (k : K) (i : ι k) :
    (∏ k', y ⟨k', Function.update c k i k'⟩) / ∏ k', y ⟨k', c k'⟩ = y ⟨k, i⟩ / y ⟨k, c k⟩ := by
  rw [← Finset.prod_div_distrib, Finset.prod_eq_single k]
  · simp
  · intro b _ hb
    rw [Function.update_of_ne hb, div_self (hc b)]
  · intro h
    exact absurd (Finset.mem_univ k) h

theorem adjoin_segre_eq (y : (Σ k, ι k) → Ω) {N : ℕ} (E : Fin (N + 1) ≃ ((k : K) → ι k)) (c₀ : Fin (N + 1))
    (hc : ∀ k, y ⟨k, E c₀ k⟩ ≠ 0) :
    IntermediateField.adjoin ℚ (Set.range fun j => (∏ k, y ⟨k, E j k⟩) / ∏ k, y ⟨k, E c₀ k⟩) =
      blockFnField y := by
  classical
  rw [← CoordArithOfFnField.ratioField_eq y (E c₀) hc]
  apply le_antisymm
  · rw [IntermediateField.adjoin_le_iff]
    rintro _ ⟨j, rfl⟩
    simp only [← Finset.prod_div_distrib]
    exact prod_mem fun k _ => IntermediateField.subset_adjoin _ _ ⟨⟨k, E j k⟩, rfl⟩
  · rw [GroundTheory.Heights₂.Heights.CoordinateConeArithVar.ratioField, IntermediateField.adjoin_le_iff]
    rintro _ ⟨⟨k, i⟩, rfl⟩
    refine IntermediateField.subset_adjoin _ _ ⟨E.symm (Function.update (E c₀) k i), ?_⟩
    simpa using segre_update_ratio y (E c₀) hc k i

theorem trdeg_blockFnField {y : (Σ k, ι k) → Ω} {e : ℕ} (hA : IsArithVar (mCoordIdeal y) (e + 1))
    (c : ∀ k, ι k) (hc : ∀ k, y ⟨k, c k⟩ ≠ 0) : Algebra.trdeg ℚ (blockFnField y) = e := by
  obtain ⟨_, _, _, hdim⟩ := hA
  rw [CoordArithOfFnField.dim_eq y c hc] at hdim
  have h1 : (Algebra.trdeg ℤ (blockFnField y)).toENat = e := by
    generalize (Algebra.trdeg ℤ (blockFnField y)).toENat = n at hdim ⊢
    induction n using ENat.recTopCoe with
    | top =>
      exfalso
      simp only [top_add] at hdim
      norm_cast at hdim
    | coe n =>
      norm_cast at hdim ⊢
      omega
  rw [Cardinal.toENat_eq_natCast] at h1
  have : Algebra.IsAlgebraic ℤ ℚ := IsLocalization.isAlgebraic _ (nonZeroDivisors ℤ)
  rw [← h1, ← trdeg_add_eq ℤ ℚ (A := blockFnField y), trdeg_eq_zero (R := ℤ) (A := ℚ), zero_add]


open scoped IntermediateField.algebraAdjoinAdjoin in
theorem exists_away_of_trdeg (S : Set Ω) (hS : S.Finite) {e : ℕ}
    (h : Algebra.trdeg ℚ (IntermediateField.adjoin ℚ S) = e) :
    ∃ s : Algebra.adjoin ℚ S, s ≠ 0 ∧
      Algebra.IsStandardSmoothOfRelativeDimension e ℚ (Localization.Away s) := by
  have hfin : Algebra.FiniteType ℚ (Algebra.adjoin ℚ S) :=
    (Subalgebra.fg_iff_finiteType _).1 (Subalgebra.fg_def.2 ⟨S, hS, rfl⟩)
  have h2 : Algebra.trdeg ℚ (Algebra.adjoin ℚ S) = e := by
    rw [← h]
    exact (GroundTheory.Arith.Abelian.Jacobian.trdeg_eq_of_isFractionRing (k := ℚ) (A := Algebra.adjoin ℚ S)
      (IntermediateField.adjoin ℚ S)).symm
  exact GlobalTheory.AffinePoints.exists_ne_zero_isStandardSmoothOfRelativeDimension
    (GlobalTheory.ringKrullDim_eq_of_trdeg_eq ℚ _ h2)

theorem exists_away_standardSmooth (Ω : Type) [Field Ω] [CharZero Ω] (K : Type) [Fintype K] (ι : K → Type)
    [∀ k, Fintype (ι k)] (y : (Σ k, ι k) → Ω) (e : ℕ) (hA : IsArithVar (mCoordIdeal y) (e + 1)) (N : ℕ)
    (E : Fin (N + 1) ≃ ((k : K) → ι k)) (c₀ : Fin (N + 1)) (hc : ∀ k, y ⟨k, E c₀ k⟩ ≠ 0) :
    ∃ s : Algebra.adjoin ℚ (Set.range fun j => (∏ k, y ⟨k, E j k⟩) / ∏ k, y ⟨k, E c₀ k⟩), s ≠ 0 ∧
      Algebra.IsStandardSmoothOfRelativeDimension e ℚ (Localization.Away s) := by
  refine exists_away_of_trdeg _ (Set.finite_range _) ?_
  rw [adjoin_segre_eq y E c₀ hc]
  exact trdeg_blockFnField hA (E c₀) hc

end GlobalTheory.CompanionTheory.Ar.SegreChart
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.FlatHermUnitSectionAvoid
section
open MvPolynomial NumberField ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I2 GlobalTheory.CompanionTheory.Ar.Flat

namespace GlobalTheory.CompanionTheory.Ar.Flat

theorem isOpen_blockNonzero {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] :
    IsOpen {z : (Σ k, ι k) → ℂ | ∀ k, ∃ i, z ⟨k, i⟩ ≠ 0} := by
  simp only [Set.setOf_forall, Set.setOf_exists]
  exact isOpen_iInter_of_finite fun k => isOpen_iUnion fun i =>
    isOpen_ne_fun (continuous_apply _) continuous_const

theorem PtOver.eventually_ptOver {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {Ω : Type} [Field Ω]
    {F : Type} [Field F] [NumberField F] {y : (Σ k, ι k) → Ω} {φ : F →+* Ω} (hO : OverInt y φ)
    {σ : F →+* ℂ} {z : (Σ k, ι k) → ℂ} (hz : PtOver y φ σ z) :
    ∀ᶠ w in nhds z, w ∈ mcPts (mCoordIdeal y) → PtOver y φ σ w := by
  classical
  let e := Finite.equivFin (F →+* ℂ)
  let t : (F →+* ℂ) → ℝ := fun τ => ((e τ : ℕ) : ℝ)
  have ht : Function.Injective t := fun a b hab => by
    have h0 : ((e a : ℕ) : ℝ) = ((e b : ℕ) : ℝ) := hab
    have : ((e a : ℕ)) = (e b : ℕ) := by exact_mod_cast h0
    exact e.injective (Fin.ext this)
  obtain ⟨u, hu, -⟩ := GlobalTheory.T.exists_place_weight_conj_invariant K ι Ω F y φ t hO
  filter_upwards [hu.near σ z hz] with w hw hwP
  obtain ⟨τ, hτ, -⟩ := GlobalTheory.T.complex_point_existsUnique_embedding K ι Ω F y φ hO w hwP
  have h1 : u w = t τ := (hu.near τ w hτ).self_of_nhds
  have h2 : τ = σ := ht (h1.symm.trans hw)
  exact h2 ▸ hτ

theorem FlatHerm.exists_rep : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Ω : Type) [Field Ω] (F : Type) [Field F] [NumberField F] (y : (Σ k, ι k) → Ω) (φ : F →+* Ω) (A : HermLine ι) (S : FlatHerm y φ A) (d : ℕ) (W : Ideal (MRing ι)), OverInt y φ → IsArithVar (mCoordIdeal y) d → IsSmoothHerm A → IsMultiProjPrime W → mCoordIdeal y ≤ W → ∃ (f' g' : MRing ι) (df' dg' : K → ℕ), IsMultiHomog f' df' ∧ IsMultiHomog g' dg' ∧ (∀ k, (df' k : ℤ) - dg' k = S.M * A.a k) ∧ f' ∉ W ∧ g' ∉ W ∧ f' * S.g - g' * S.f ∈ mCoordIdeal y ∧ IsUnitSec (mCoordIdeal y) f' g' ∧ ∀ σ z, PtOver y φ σ z → ‖evC z f'‖ = (S.κ σ * A.h z) ^ S.M * ‖evC z g'‖ := by
  intro K _ ι _ Ω _ F _ _ y φ A S d W hO hV hA hW hPW
  obtain ⟨f', g', df', dg', hf', hg', hdeg, hfW, hgW, hrel, hunit⟩ :=
    _root_.GlobalTheory.CompanionTheory.Ar.Flat.exists_rep_avoiding K ι (mCoordIdeal y) W S.f S.g S.df S.dg hV.2.1 hW hPW S.hf S.hg S.g_ne S.unit
  refine ⟨f', g', df', dg', hf', hg', fun k => (hdeg k).trans (S.deg k), hfW, hgW, hrel, hunit, ?_⟩
  intro σ z hz
  have hcl := _root_.GlobalTheory.CompanionTheory.Ar.Flat.nonvanishing_dense K ι (mCoordIdeal y) d S.g hV S.g_ne hz.1
  have hfreq := mem_closure_iff_frequently.mp hcl
  have hnear := PtOver.eventually_ptOver hO hz
  have hcontA : ContinuousAt A.h z :=
    (hA.continuousOn).continuousAt (isOpen_blockNonzero.mem_nhds hz.1.1)
  have hcf : Continuous fun w : (Σ k, ι k) → ℂ => evC w f' := MvPolynomial.continuous_eval _
  have hcg : Continuous fun w : (Σ k, ι k) → ℂ => evC w g' := MvPolynomial.continuous_eval _
  have hL : Filter.Tendsto (fun w => ‖evC w f'‖) (nhds z) (nhds ‖evC z f'‖) :=
    hcf.norm.continuousAt
  have hR : Filter.Tendsto (fun w => (S.κ σ * A.h w) ^ S.M * ‖evC w g'‖) (nhds z)
      (nhds ((S.κ σ * A.h z) ^ S.M * ‖evC z g'‖)) :=
    (((continuousAt_const.mul hcontA).pow S.M).mul hcg.norm.continuousAt)
  refine tendsto_nhds_unique_of_frequently_eq hL hR ?_
  refine (hfreq.and_eventually hnear).mono ?_
  rintro w ⟨⟨hwP, hgw⟩, hwσ⟩
  have hover := hwσ hwP
  have hn := S.norm σ w hover
  have h0 : evC w f' * evC w S.g - evC w g' * evC w S.f = 0 := by
    have := hwP.2 _ hrel
    simpa [evC, map_sub, map_mul] using this
  have h1 : ‖evC w f'‖ * ‖evC w S.g‖ = ‖evC w g'‖ * ‖evC w S.f‖ := by
    rw [← norm_mul, ← norm_mul, sub_eq_zero.mp h0]
  have hg0 : ‖evC w S.g‖ ≠ 0 := norm_ne_zero_iff.mpr hgw
  apply mul_right_cancel₀ hg0
  rw [h1, hn]
  ring

end GlobalTheory.CompanionTheory.Ar.Flat
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.HermitianPairingTorsionFree
section
open AlgebraicGeometry CategoryTheory NumberField MvPolynomial ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Num GlobalTheory.CompanionTheory.Ar.Top
open GroundTheory.Heights₂.Heights.NumbersDVR (pointIdeal segreVec IsFlagFrame IsFlagPair SameGenericFibre IsModelOver divCycle)
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.NumbersDVR.Bundles (mseg fnField)
open Limits MonoidalCategory CartesianMonoidalCategory MonObj
open GlobalTheory.CompanionTheory.Ar.Num.FamEx GlobalTheory.CompanionTheory.Ar.BT

namespace GlobalTheory.CompanionTheory.Ar.Num.FamEx

theorem gram_invertible_of_unramified : ∀ (E : Type) [Field E] [NumberField E] (cc : E ≃+* E) (p R N : ℕ) [Fact p.Prime], 1 ≤ R → ¬ (p : ℤ) ∣ NumberField.discr E → ∀ (e : (Fin N → 𝓞 E) →+ (Fin N → 𝓞 E) →+ ZMod (p ^ R)), (∀ (a : 𝓞 E) (x y : Fin N → 𝓞 E), e (a • x) y = e x (RingOfIntegers.mapRingEquiv cc a • y)) → (∀ x, e x = 0 → ∃ x', x = (p ^ R) • x') → ∀ (O Ω : Type) [CommRing O] [IsDomain O] [IsLocalRing O] [Field Ω] [Algebra O Ω], Function.Injective (algebraMap O Ω) → ¬ IsUnit (p : O) → ∀ σ : E →+* Ω, (∀ a : 𝓞 E, ∃ o : O, algebraMap O Ω o = σ (a : E)) → ∃ C : Matrix (Fin N) (Fin N) Ω, (∀ i j, C i j ∈ (algebraMap O Ω).range) ∧ (Matrix.of fun i j => ∑ k, σ (HT.dualInt E k) * ((e (Pi.single i (RingOfIntegers.basis E k)) (Pi.single j 1)).val : Ω)) * C = 1 :=
  @PositivityTheory.Xgn.gram_determinant_unit_mod_p

end GlobalTheory.CompanionTheory.Ar.Num.FamEx
end

