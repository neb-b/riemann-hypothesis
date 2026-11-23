module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1128
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0015
public import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.IsGloballyGeneratedIffGeneratingSections
public import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.EventuallySubsingletonCohTwistZOfIsProjOver
public import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.IsFiniteLengthOfIsArtinianRingAnnihilator
public import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.EventuallyExistsFiniteSubsetNonzeroLocus
public import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.ExistsLinearMapMultilinearMapBaseChange
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0197
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0200
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0261
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPowLeGlobalSectionsDimLineBundlePow
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0004
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsIsLocModelIsPrimeOf
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0038
public import Development.AbelianVarietyTheory.Definitions.Divisors.PointsNonemptyUnitaryRankOne
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0974
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0884
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1149
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NontrivialIsomClassInt
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.UnderEqGenericPoint
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0016
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0035
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0036
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1131
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0013
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1148
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsConstAlongSingleton
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.GelfandKazhdanDual
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.StrongMultiplicityOne
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.CuspDiscreteDecompositionGL
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0005
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0008
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.CuspRapidDecaySiegelGL
public import Development.AbelianVarietyTheory.Definitions.Divisors.LineOppositeParabolicUnitaryLeviSectionEq
public import Development.AbelianVarietyTheory.Definitions.Foundations.IsSatVecUOfIsSphericalU

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbsFactorialMulEulerCharTwistPowSubLeStatement
section
open CategoryTheory Limits AlgebraicGeometry TopologicalSpace Filter Asymptotics
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.QCoh GlobalTheory.CechPic GlobalTheory.Twist
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.abs_factorial_mul_eulerChar_twist_pow_sub_le : ∀ (k : Type) [Field k] [Infinite k] (X : Scheme.{0}) [Algebra k Γ(X, ⊤)], IsProjOver (strHom k (X := X)) → ∀ (d : ℕ) (F : X.Modules) [IsFiniteQC F], suppDim F ≤ (d : ℕ) → ∀ L : LB X, L.IsLB → ∃ C : ℕ, ∀ m : ℕ, |(d.factorial : ℤ) * chi k (twist F (lbPow L m)) - interNum k F (fun _ : Fin d => L) * (m : ℤ) ^ d| ≤ C * ((d : ℤ) * ((m : ℤ) + 1) ^ (d - 1)) := by
  first | exact @GlobalTheory.abs_factorial_mul_chi_twist_lbPow_sub_le | exact GlobalTheory.abs_factorial_mul_chi_twist_lbPow_sub_le | (intros; apply GlobalTheory.abs_factorial_mul_chi_twist_lbPow_sub_le <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AlgebraicIndependentEtaleTowerCoordinatesStatement
section
open CategoryTheory AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.Discrepancy GlobalTheory.FieldPair
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.algebraicIndependent_etaleTower_coordinates : ∀ {K L : Type} [Field K] [Field L] (cK : ℂ →+* K) (cL : ℂ →+* L) (n r : ℕ) (R : Subring K) (T : Subring L)
    (ι : R →+* T) (ψ : T →+* R) (τ : Fin r → T) (x : Fin n → R),
  IsEtTower cK R cL T ι ψ τ → TrBasis cK (fun i => (x i : K)) →
  Function.Injective (MvPolynomial.eval₂Hom ι τ) →
  (letI := cL.toAlgebra; AlgebraicIndependent ℂ (Fin.append (fun i => (τ i : L)) (fun i => (ι (x i) : L)))) := by
  first | exact @GlobalTheory.FieldPair.etTower_coords_algebraicIndependent | exact GlobalTheory.FieldPair.etTower_coords_algebraicIndependent | (intros; apply GlobalTheory.FieldPair.etTower_coords_algebraicIndependent <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AnnihilatorOfAnnihilatorLe
section
open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKCount GlobalTheory.LKCx
open scoped TensorProduct Classical

namespace GlobalTheory

theorem LKMid.Pair.term_one_eq_pointSum : ∀ (p : ℕ) [Fact p.Prime] (G : HTGroup p) (P : Pair G) (Kf : Subgroup G.GAf) (f : G.GAf → ℂ) (K' : Subgroup (Gr G 1)) (f' : Gr G 1 → ℂ), (∀ k ∈ Kf, ∀ g, f (k⁻¹ * g * k) = f g) → (∀ k ∈ K', ∀ g, f' (k⁻¹ * g * sigG G 1 k) = f' g) → ∀ (x : (AfP p ⊗[ℚ] G.C)ˣ) (t : (AfP p)ˣ) (hx : Triv G (AfP p) P.β x t), P.term Kf f 1 K' f' = pointSum (P.toAf x t hx) (P.toQr 1 1) (MonoidHom.id (Gr G 1)) Kf K' (P.toAf x t hx P.self) (inclG G 1 P.atP) f f' := by
  intro p _ G P Kf f K' f' hf hf' x t hx
  have hN : IsNrm G 1 P.atP (inclG G 1 P.atP) 1 := (GlobalTheory.nrm_exact p G).2 P.atP
  have hsig : sigG G 1 = MonoidHom.id (Gr G 1) := by
    ext1 g
    exact (GlobalTheory.LKMid.SigIter.main p G 1 Nat.one_pos).1 g
  rw [GlobalTheory.T.kottwitzPair_term_eq_pointSum_any_trivialisation p G P Kf f 1 K' f' Nat.one_pos hf hf' x t hx (inclG G 1 P.atP) 1 hN]
  unfold Pair.termAt
  rw [hsig]

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ArithHeightsAndFormsOfIntersectionAndInductive
section
set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace MvPolynomial
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.ArInt GlobalTheory.Cartier GlobalTheory.CxPts

namespace GlobalTheory.Published

variable {k : Type} [CommRing k] {X : Scheme.{0}} [IsIntegral X] {p : X ⟶ Sp k} {D : ℕ}

theorem ArFormExists.exists_isArithHeight (H : ArFormExists) (hX : IsArithVar p D) (L : HermLB p) :
    ∃ h, L.IsArithHeight h := by
  obtain ⟨Φ, hΦ⟩ := H k X p D hX Unit fun _ => L
  obtain ⟨h, hh, -⟩ := hΦ.1 (Pi.single () 1)
  exact ⟨h, (isometric_comb_single (fun _ : Unit => L) ()).isArithHeight hX hh⟩

theorem ArMix.fnB_of_height (H : ArMix) (hX : IsArithVar p D) {ι : Type} [Fintype ι] {L : ι → HermLB p}
    {u : ∀ σ : k →+* ℂ, CxPts p σ → ℝ} {hu : ∀ σ y, CInfAt (u σ) y}
    {hc : ∀ σ σ', (Weight.ofFun (u σ)).IsConj (Weight.ofFun (u σ'))} {Φ : MvPolynomial (Option ι) ℝ →ₗ[ℝ] ℝ}
    (hΦ : IsArFun (fun o : Option ι => o.elim (ArInt.fnB u hu hc) L) D Φ) (n : ι → ℤ) {h : X → ℝ}
    (hh : (comb L n).IsArithHeight h) :
    Φ (MvPolynomial.X none * rename some (lin fun i => (n i : ℝ)) ^ D) = 1 / 2 * chInt (comb L n) D u := by
  have := hX.isLocallyNoetherian
  have hr : IsRatSec (ArInt.fnB u hu hc).B fun _ => 1 := fun a b h =>
    (map_one _).symm.trans (mul_one _).symm
  have he (z : X) : ((ArInt.fnB u hu hc).div hr).IsEqn z 1 :=
    (presents_divOfRatSec _ hr).isEqn PUnit.unit z trivial
  have h₁ (z : X) : ((ArInt.fnB u hu hc).div hr).mult z = 0 := (he z).mult_eq.trans (unitAt_one z).ord_eq_zero
  have h₂ (σ) : offSupp p σ ((ArInt.fnB u hu hc).div hr) = Set.univ :=
    Set.eq_univ_of_forall fun y => mem_offSupp.2 fun hy => (he _).mem_supp_iff.1 hy (unitAt_one _)
  have h₃ (σ) : logNorm ((ArInt.fnB u hu hc).φ σ) (fun _ => 1) = fun y => -(1 / 2) * u σ y := funext fun y => by
    have e := ratVal_fnOf (y := y) mem_ptsIn_top trivial 1
    rw [map_one, ev_one mem_ptsIn_top] at e
    rw [logNorm, Units.val_one, e, norm_one, Real.log_one]
    change 0 - u σ y / 2 = _
    ring
  rw [(H k X p D hX ι _ L Φ hΦ n h hh _ hr).2, HermLB.archInt, chInt]
  simp only [h₁, h₂, h₃, Weight.chernInt_const_mul, Int.cast_zero, zero_mul, finsum_zero, ← mul_finsum]
  ring

theorem arExists_of_form_of_mix : ArFormExists → ArMix → ArExists := by
  intro HF HM k _ X _ p D hX
  refine ⟨HF.exists_isArithHeight hX, fun ι _ L => ⟨HF k X p D hX ι L, ?_⟩⟩
  have hu (σ : k →+* ℂ) (y : CxPts p σ) : CInfAt (fun _ => (2 : ℝ)) y := cInfAt_const _ y
  have hc (σ σ' : k →+* ℂ) : (Weight.ofFun (p := p) (σ := σ) fun _ => (2 : ℝ)).IsConj
      (Weight.ofFun (σ := σ') fun _ => (2 : ℝ)) := fun _ _ _ _ _ => rfl
  obtain ⟨Φ, hΦ⟩ := HF k X p D hX _ fun o : Option ι => o.elim (ArInt.fnB (fun _ _ => 2) hu hc) L
  refine ⟨Φ ∘ₗ LinearMap.mulLeft ℝ (MvPolynomial.X none) ∘ₗ (rename (R := ℝ) (some : ι → Option ι)).toLinearMap,
    fun n => ?_, fun P d hd hP => ?_⟩
  · obtain ⟨h, hh⟩ := HF.exists_isArithHeight hX (comb L n)
    rw [LinearMap.comp_apply, LinearMap.comp_apply, AlgHom.toLinearMap_apply, map_pow, LinearMap.mulLeft_apply,
      HM.fnB_of_height hX hΦ n hh, gdeg, chInt, chInt, mul_finsum]
    refine finsum_congr fun σ => ?_
    rw [← Weight.chernInt_const_mul]
    norm_num
  · rw [LinearMap.comp_apply, LinearMap.comp_apply, AlgHom.toLinearMap_apply, LinearMap.mulLeft_apply]
    exact hΦ.2 _ (1 + d) (by omega) ((isHomogeneous_X ℝ none).mul hP.rename_isHomogeneous)

end GlobalTheory.Published
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ArithInterChangeOfMetricOfMixedInductive
section
set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry MvPolynomial
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.ArInt GlobalTheory.HermLB

namespace GlobalTheory.ArInt

variable {k : Type} [CommRing k] {X : Scheme.{0}} [IsIntegral X] {p : X ⟶ Sp k} {D : ℕ} {ι : Type} [Fintype ι]

theorem mixed_eq_of_icls (hX : IsArithVar p D) {T M N : HermLB p} {L : ι → HermLB p}
    {Ψ : MvPolynomial (Option (Option ι)) ℝ →ₗ[ℝ] ℝ}
    (hΨ : IsArFun (fun o : Option (Option ι) => o.elim T fun o => o.elim M L) D Ψ) (a b : ℤ)
    (hN : N.icls = b • T.icls + a • M.icls) {Φ : MvPolynomial (Option ι) ℝ →ₗ[ℝ] ℝ}
    (hΦ : IsArFun (fun o : Option ι => o.elim N L) D Φ) (n : ι → ℤ) :
    Φ (MvPolynomial.X none * rename some (lin fun i => (n i : ℝ)) ^ D) =
      b * Ψ (MvPolynomial.X none * rename (some ∘ some) (lin fun i => (n i : ℝ)) ^ D) +
      a * Ψ (MvPolynomial.X (some none) * rename (some ∘ some) (lin fun i => (n i : ℝ)) ^ D) := by
  classical
  let A : Option ι → Option (Option ι) → ℤ := fun j => j.elim (fun o => o.elim b fun o => o.elim a 0)
    fun i => Pi.single (some (some i)) 1
  have h := ((Published.arIso_holds k X p D hX).2 _ _ Ψ hΨ).2.2 (Option ι) (fun o : Option ι => o.elim N L) A (by
    rintro (_ | i)
    · exact icls_eq_iff.1 (by simp [A, icls_comb, Fintype.sum_option, hN])
    · exact isometric_comb_single _ (some (some i)))
  have e₀ : (lin fun i => (A none i : ℝ)) = (b : ℝ) • MvPolynomial.X none + (a : ℝ) • MvPolynomial.X (some none) := by
    simp [A, lin, Fintype.sum_option, smul_eq_C_mul]
  have e₁ (i : ι) : (lin fun j => (A (some i) j : ℝ)) = MvPolynomial.X (some (some i)) := lin_single _
  have e₂ : aeval (fun j => lin fun i => (A j i : ℝ)) (rename some (lin fun i => (n i : ℝ))) =
      rename (some ∘ some) (lin fun i => (n i : ℝ)) := by
    conv_lhs => rw [aeval_rename]
    simp only [Function.comp_def, e₁]
    rw [rename_eq_aeval]
    rfl
  rw [Model.isArFun_unique hX hΦ h, LinearMap.comp_apply, AlgHom.toLinearMap_apply, map_mul, map_pow, e₂, aeval_X, e₀,
    add_mul, smul_mul_assoc, smul_mul_assoc, map_add, map_smul, map_smul, smul_eq_mul, smul_eq_mul]

end GlobalTheory.ArInt

namespace GlobalTheory.Published

theorem arMetric_of_arMix : ArExists → ArMix → ArMetric := by
  intro HE H k _ X _ p D hX ι _ M L u hu hc Φ Φ' hΦ hΦ' n
  obtain ⟨Ψ, hΨ⟩ := ((HE k X p D hX).2 _
    fun o : Option (Option ι) => o.elim (ArInt.fnB u hu hc) fun o => o.elim M L).1
  obtain ⟨Θ, hΘ⟩ := ((HE k X p D hX).2 _ fun o : Option ι => o.elim (ArInt.fnB u hu hc) L).1
  obtain ⟨h₁, h₂⟩ := H.fnB HE hX hΘ n
  refine ⟨h₁, ?_⟩
  rw [← h₂, mixed_eq_of_icls hX hΨ 1 0 (by simp) hΦ, mixed_eq_of_icls hX hΨ 0 1 (by simp) hΘ,
    mixed_eq_of_icls hX hΨ 1 1 (by
      rw [← icls_eq_iff.2 (isometric_tens_fnB M u hu hc), icls_tens, one_smul, one_smul, add_comm]) hΦ']
  push_cast
  ring

end GlobalTheory.Published
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ArithInterProjectionFormulaOfHeightProjectionForStatement
section
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.arithInterProjectionFormula_of_heightProjectionFormula : GlobalTheory.Published.HeightProjection → GlobalTheory.Published.ArProj := by
  first | exact @GlobalTheory.Published.arProj_of_heightProjection | exact GlobalTheory.Published.arProj_of_heightProjection | (intros; apply GlobalTheory.Published.arProj_of_heightProjection <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ArithSelfInterConstantShiftOfTrivialWeightFormul
section
namespace GlobalTheory.Published

theorem arShift_of_arChange : GlobalTheory.Published.ArExists → GlobalTheory.Published.ArChange → GlobalTheory.Published.ArShift := by
  intro hE hC k _ X _ p D hX L a t ha
  have h := GlobalTheory.TwistTop.isSelfInter_shift hE hC k X p D hX L a (fun _ => t) (fun _ => rfl) ha
  rw [← mul_finsum, ← mul_assoc] at h
  exact h

end GlobalTheory.Published
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.BadPlacesPrimeToHostBaseTuple
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues Formalism.L2.Pj Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.FWT
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues GlobalTheory.AdelicScalar GlobalTheory.LiftRows GlobalTheory.LowRow

namespace GlobalTheory.LowRow

theorem primeToHost_base : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), GlobalTheory.Core5 R F → PrimeToHost R A.μ0 := by
  intro D G _ _ Pl0 T A Ks _ _ _ R F h PP hP
  rcases hP with hP | hP
  · exact GlobalTheory.LiftScalarCompare.primeToHost h.lev PP hP
  · rw [GlobalTheory.LiftLower.Q_base h.lev] at hP
    simp at hP

end GlobalTheory.LowRow
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.BoxMonomialFamilyProdMemNormBallOfExponentLt
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.VolBr GlobalTheory.HSNef

namespace GlobalTheory.HSNef.BoxProd

variable {k : Type} [CommRing k] {X : Scheme.{0}} [IsIntegral X] {p : X ⟶ Sp k}

theorem nu_nonneg (P : Pair p) (a b : ℤ) (σ : k →+* ℂ) (y : CxPts p σ) (f : X.functionField) :
    0 ≤ P.nu a b σ y f := by
  unfold Pair.nu; positivity

theorem mul_mem_Bl (P : Pair p) {a b a' b' : ℤ} {R R' : ℝ} (hR : 0 ≤ R) {f g : X.functionField}
    (hf : f ∈ P.Bl a b R) (hg : g ∈ P.Bl a' b' R') : f * g ∈ P.Bl (a + a') (b + b') (R * R') := by
  obtain ⟨h1, h2⟩ := GlobalTheory.VolBr.NuMul.mul_mem_H_and_nu_mul _ _ _ P a b a' b' f g hf.1 hg.1
  refine ⟨h1, fun σ y => ?_⟩
  rw [h2 σ y]
  exact mul_le_mul (hf.2 σ y) (hg.2 σ y) (nu_nonneg _ _ _ _ _ _) hR

theorem one_mem_Bl (P : Pair p) : (1 : X.functionField) ∈ P.Bl 0 0 1 := by
  refine ⟨fun x i j _ _ => ?_, fun σ y => ?_⟩
  · simp only [Pair.loc, zpow_zero, mul_one]
    exact ⟨1, map_one _⟩
  · have e := IntExample.ratVal_nat y 1
    simp only [Nat.cast_one] at e
    simp [Pair.nu, Pair.loc, e]

theorem prod_mem_of_le (P : Pair p) (D : ℕ) (J : Type) (e : J → X.functionField) (x : Fin D → X.functionField)
    (a b : ℤ) (R : ℝ) (hR : 0 ≤ R) (h : ∀ c, boxFam e x c ∈ P.Bl a b R) :
    ∀ (m : ℕ) (u : Fin m → J) (n : Fin D → ℕ), (∀ i, n i ≤ m) →
      (∏ l, e (u l)) * ∏ i, x i ^ n i ∈ P.Bl (m * a) (m * b) (R ^ m) := by
  intro m
  induction m with
  | zero =>
    intro u n hn
    have h0 : ∀ i, n i = 0 := fun i => Nat.le_zero.1 (hn i)
    simp only [h0, pow_zero, Finset.prod_const_one, Finset.univ_eq_empty, Finset.prod_empty, mul_one,
      Nat.cast_zero, zero_mul]
    exact one_mem_Bl P
  | succ m ih =>
    intro u n hn
    have hx : ∏ i, x i ^ n i =
        (∏ i ∈ Finset.univ.filter (fun i => 0 < n i), x i) * ∏ i, x i ^ (n i - 1) := by
      rw [Finset.prod_filter, ← Finset.prod_mul_distrib]
      refine Finset.prod_congr rfl fun i _ => ?_
      rcases Nat.eq_zero_or_pos (n i) with h0 | h0
      · simp [h0]
      · rw [if_pos h0, ← pow_succ', Nat.sub_add_cancel (by omega : 1 ≤ n i)]
    have key : (∏ l, e (u l)) * ∏ i, x i ^ n i =
        boxFam e x (u 0, Finset.univ.filter (fun i => 0 < n i)) *
          ((∏ l : Fin m, e (u l.succ)) * ∏ i, x i ^ (n i - 1)) := by
      rw [Fin.prod_univ_succ, hx]
      simp only [boxFam]
      ring
    rw [key]
    have hm := mul_mem_Bl P hR (h (u 0, Finset.univ.filter (fun i => 0 < n i)))
      (ih (fun l => u l.succ) (fun i => n i - 1) (fun i => by have := hn i; omega))
    have ea : ((m + 1 : ℕ) : ℤ) * a = a + m * a := by push_cast; ring
    have eb : ((m + 1 : ℕ) : ℤ) * b = b + m * b := by push_cast; ring
    rw [ea, eb, pow_succ']
    exact hm

theorem prod_mem_Bl : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k), ∀ (P : Pair p) (D : ℕ) (J : Type) (e : J → X.functionField) (x : Fin D → X.functionField) (a b : ℤ) (R : ℝ), 0 ≤ R → (∀ c, boxFam e x c ∈ P.Bl a b R) → ∀ (m : ℕ) (u : Fin m → J) (n : Fin D → ℕ), (∀ i, n i < m) → (∏ l, e (u l)) * ∏ i, x i ^ n i ∈ P.Bl (m * a) (m * b) (R ^ m) := by
  intro k _ X _ p P D J e x a b R hR h m u n hn
  exact prod_mem_of_le P D J e x a b R hR h m u n fun i => (hn i).le

end GlobalTheory.HSNef.BoxProd
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CTSubmatrixMul
section
open NumberField MeasureTheory Matrix Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet
open scoped TensorProduct

namespace GlobalTheory.TieStd

theorem depth_lt_iff {r : ℕ} (S : Finset (Fin r)) (s : ℕ) (hs : s ≤ r) (d : Fin s → ℕ)
    (hd : ∀ i, d i = (S.filter (· < Fin.castLE hs i)).card) (i j : Fin s) :
    d j < d i ↔ ∃ k ∈ S, Fin.castLE hs j ≤ k ∧ k < Fin.castLE hs i := by
  rw [hd, hd]
  constructor
  · intro h
    by_contra hne
    push Not at hne
    refine absurd h (not_lt.2 (Finset.card_le_card fun k hk => ?_))
    rw [Finset.mem_filter] at hk ⊢
    exact ⟨hk.1, lt_of_not_ge fun h' => absurd hk.2 (not_lt.2 (hne k hk.1 h'))⟩
  · rintro ⟨k, hk, h1, h2⟩
    refine Finset.card_lt_card ⟨fun x hx => ?_, fun h => ?_⟩
    · rw [Finset.mem_filter] at hx ⊢
      exact ⟨hx.1, lt_of_lt_of_le hx.2 (h1.trans h2.le)⟩
    · have := h (Finset.mem_filter.2 ⟨hk, h2⟩)
      exact absurd (Finset.mem_filter.1 this).2 (not_lt.2 h1)

theorem cT_submatrix_mul {E : Type} [Field E] (σ : E →+* E) {n r s : ℕ} (J : Matrix (Fin n) (Fin n) E)
    (A B : Matrix (Fin n) (Fin r) E) (f g : Fin s → Fin r) :
    Formalism.UG.cT σ (A.submatrix id f) * J * B.submatrix id g = (Formalism.UG.cT σ A * J * B).submatrix f g := by
  ext i j
  simp [Formalism.UG.cT, Matrix.mul_apply]

end GlobalTheory.TieStd
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CapelliOperatorAlgebraStableUnderComplexConj
section
open NumberField IsDedekindDomain Formalism.L2.Host GlobalTheory.CuspRep GlobalTheory.ContraPair

namespace GlobalTheory.CuspRep.ConjZalg

variable {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] {a : ℕ}

theorem map_qdet_semilinear {A B : Type} [Ring A] [Algebra ℂ A] [Ring B] [Algebra ℂ B] (f : A →+* B) (σ : ℂ →+* ℂ)
    (hf : ∀ c, f (algebraMap ℂ A c) = algebraMap ℂ B (σ c)) (X : Fin a → Fin a → A) (u : ℂ) :
    f (Formalism.REAL.qdet X u) = Formalism.REAL.qdet (fun i j => f (X i j)) (σ u) := by
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [Formalism.REAL.qdet, Formalism.REAL.qminor, map_sum, map_mul, map_intCast, map_list_prod, List.map_ofFn]
  refine Finset.sum_congr rfl fun s _ => ?_
  congr 3
  funext k
  by_cases h : s k = k <;> simp [Formalism.REAL.Tm, h, map_add, hf, map_sub, map_natCast]

def conjBy (C : Sm E a ≃ₗ⋆[ℂ] Sm E a) : Module.End ℂ (Sm E a) →+* Module.End ℂ (Sm E a) where
  toFun z :=
    { toFun := fun φ => C.symm (z (C φ))
      map_add' := fun φ ψ => by simp
      map_smul' := fun c φ => by
        rw [LinearEquiv.map_smulₛₗ, LinearMap.map_smul, LinearEquiv.map_smulₛₗ]; simp }
  map_one' := LinearMap.ext fun φ => by simp
  map_mul' z w := LinearMap.ext fun φ => by simp
  map_zero' := LinearMap.ext fun φ => by simp
  map_add' z w := LinearMap.ext fun φ => by simp

theorem conjBy_apply (C : Sm E a ≃ₗ⋆[ℂ] Sm E a) (z : Module.End ℂ (Sm E a)) (φ : Sm E a) :
    conjBy C z φ = C.symm (z (C φ)) := rfl

theorem conjBy_algebraMap (C : Sm E a ≃ₗ⋆[ℂ] Sm E a) (c : ℂ) :
    conjBy C (algebraMap ℂ (Module.End ℂ (Sm E a)) c) = algebraMap ℂ _ (starRingEnd ℂ c) :=
  LinearMap.ext fun φ => by
    rw [conjBy_apply, Module.algebraMap_end_apply, Module.algebraMap_end_apply, LinearEquiv.map_smulₛₗ]; simp

theorem C_Eop (C : Sm E a ≃ₗ⋆[ℂ] Sm E a) (hC : ∀ o φ, act o (C φ) = C (act o φ)) (τ : E →+* ℂ) (i j : Fin a)
    (φ : Sm E a) : C (Eop τ i j φ) = Eop (ComplexEmbedding.conjugate τ) i j (C φ) := by
  have hl : ∀ x φ, C (lieS E a i j x φ) = lieS E a i j x (C φ) := fun x φ => (hC (Op.lie _) φ).symm
  have e : atEmb τ (-Complex.I) = -atEmb τ Complex.I := by
    rw [atEmb_eq]; simp
  simp only [Eop, LinearMap.smul_apply, LinearMap.sub_apply, map_smulₛₗ, map_sub, hl, atEmb_conj, map_one,
    Complex.conj_I, e, map_neg, LinearMap.neg_apply]
  have h2 : starRingEnd ℂ (1 / 2 : ℂ) = 1 / 2 := by simp [map_div₀, map_ofNat]
  rw [h2]
  congr 1
  simp [sub_eq_add_neg, neg_smul, smul_neg]

theorem conjBy_Eop (C : Sm E a ≃ₗ⋆[ℂ] Sm E a) (hC : ∀ o φ, act o (C φ) = C (act o φ)) (τ : E →+* ℂ) (i j : Fin a) :
    conjBy C (Eop τ i j) = Eop (ComplexEmbedding.conjugate τ) i j :=
  LinearMap.ext fun φ => by
    apply C.injective
    have hcc : ComplexEmbedding.conjugate (ComplexEmbedding.conjugate τ) = τ :=
      RingHom.ext fun x => by simp [ComplexEmbedding.conjugate_coe_eq]
    rw [conjBy_apply, LinearEquiv.apply_symm_apply, C_Eop C hC, hcc]

theorem conjBy_cap (C : Sm E a ≃ₗ⋆[ℂ] Sm E a) (hC : ∀ o φ, act o (C φ) = C (act o φ)) (τ : E →+* ℂ) (u : ℂ) :
    conjBy C (cap τ u) = cap (ComplexEmbedding.conjugate τ) (starRingEnd ℂ u) := by
  rw [cap, map_qdet_semilinear (conjBy C) (starRingEnd ℂ) (conjBy_algebraMap C)]
  simp only [conjBy_Eop C hC, cap]
  congr 1
  simp [map_div₀, map_ofNat, map_sub, map_natCast]

theorem conjBy_mem_Zalg (C : Sm E a ≃ₗ⋆[ℂ] Sm E a) (hC : ∀ o φ, act o (C φ) = C (act o φ))
    {z : Module.End ℂ (Sm E a)} (hz : z ∈ Zalg E a) : conjBy C z ∈ Zalg E a := by
  let S : Subalgebra ℂ (Module.End ℂ (Sm E a)) :=
    { carrier := {z | conjBy C z ∈ Zalg E a}
      mul_mem' := fun {x y} hx hy => by
        simp only [Set.mem_setOf_eq, map_mul] at *; exact Subalgebra.mul_mem _ hx hy
      add_mem' := fun {x y} hx hy => by
        simp only [Set.mem_setOf_eq, map_add (f := _)] at *; exact Subalgebra.add_mem _ hx hy
      algebraMap_mem' := fun c => by
        simp only [Set.mem_setOf_eq, conjBy_algebraMap]; exact Subalgebra.algebraMap_mem _ _ }
  refine (Algebra.adjoin_le (S := S) ?_) hz
  rintro _ ⟨τ, u, rfl⟩
  change conjBy C (cap τ u) ∈ Zalg E a
  rw [conjBy_cap C hC]
  exact Algebra.subset_adjoin ⟨_, _, rfl⟩

theorem conj_Zalg : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a : ℕ) (C : Sm E a ≃ₗ⋆[ℂ] Sm E a),
    (∀ o φ, act o (C φ) = C (act o φ)) → ∀ z ∈ Zalg E a, ∃ z' ∈ Zalg E a, ∀ φ, z (C φ) = C (z' φ) := by
  intro E _ _ _ a C hC z hz
  exact ⟨conjBy C z, conjBy_mem_Zalg C hC hz, fun φ => by rw [conjBy_apply, LinearEquiv.apply_symm_apply]⟩

end GlobalTheory.CuspRep.ConjZalg
end

