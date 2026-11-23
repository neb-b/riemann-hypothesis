module

public import Mathlib
public import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.Bundle0067
public import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.Bundle0066
public import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.Bundle0065
public import Development.WeilBound.CoreStatements.TorusUniformisation.ChowMahlerFamilies.Bundle0030
public import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.Bundle0068
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.StatementsBundles
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Bundle0054
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Bundle0047
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Bundle0060
public import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.IsFinFlatSub
public import Development.AutomorphicSpectrum.Statements.AlgebraStatements.Bundle0002
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PlaceDivisors.StChartFH
public import ReciprocityTheory.DualLattices.Bundle0028
public import ReciprocityTheory.DualLattices.Bundle0014
public import ReciprocityTheory.DualLattices.Bundle0035
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Clauses
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.Biextensions.GenericFiberCubeInclusion
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.RosVal
public import ReciprocityTheory.DualLattices.Bundle0005
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.PrecompleteBases.PsbLb
public import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.Bundle0002
public import Development.AbelianVarietyTheory.Definitions.TeichmullerDepth.IsEigBasisIff
public import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.Bundle0031
public import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.ExistsTateMatricesLink
public import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.Bundle0056
public import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.Bundle0081
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ChartPullbacks.UniversalCharts.LePreimageOfNil
public import ReciprocityTheory.DualLattices.Bundle0031
public import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.ExistsCharacterPairSer
public import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.Bundle0059
public import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.Bundle0056
public import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.Bundle0057
public import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.Bundle0055
public import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.ExistsPeriodTowerDatumOfAbelianSchemeSymmetricBuStatement
public import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.Bundle0080
public import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.Bundle0079
public import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.Bundle0069
public import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.Bundle0077
public import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.Bundle0054
public import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.Bundle0054
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PPairCocycle
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Bundle0034
public import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.VerticalDivisorsCommute
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Bundle0003
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PScalarQuotient
public import Development.WeilBound.CoreStatements.CommonZeroEvaluation.GaussianSphereMeanIntegral
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PSubQuotient

@[expose] public section

-- bundled from Development.AutomorphicSpectrum.Proofs.AlgebraProofs.AeFibrePointsCardEqDegree
section
set_option maxSynthPendingDepth 1
open GroundTheory.Heights₂.Heights MeasureTheory MvPolynomial Matrix GlobalTheory.CompanionTheory.Ar.Short.Crofton
open scoped ENNReal

private theorem ae_fibre_encard_eq {n e : ℕ} (S : Set (EuclideanSpace ℂ (Fin n)))
    (hss : IsScaleStable S) (hsc : IsSigmaCompact S) (δ : ℕ)
    (hgen : ∀ᵐ (π : Fin (e + 1) → Fin n → ℂ), ∀ᵐ (w : EuclideanSpace ℂ (Fin (e + 1))),
      cntOver S π w = (δ : ℝ≥0∞)) :
    ∀ᵐ (π : Fin (e + 1) → Fin n → ℂ), (fibrePts S π).encard = δ := by
  let T : ℝ≥0∞ → ℝ≥0∞ := fun x => if x = (δ : ℝ≥0∞) then 0 else 1
  have hT : Measurable T := Measurable.ite (measurableSet_singleton _) measurable_const measurable_const
  have hcross := _root_.PositivityTheory.Xgn.t_xgz_chow_mahler_e0reduce n e S hss hsc T hT
  have hlhs : ∫⁻ (π : Fin (e + 1) → Fin n → ℂ), matGauss π *
      ∫⁻ (w : EuclideanSpace ℂ (Fin (e + 1))) in Metric.ball 0 1, T (cntOver S π w) = 0 := by
    have hae : (fun π : Fin (e + 1) → Fin n → ℂ => matGauss π *
        ∫⁻ (w : EuclideanSpace ℂ (Fin (e + 1))) in Metric.ball 0 1, T (cntOver S π w))
        =ᵐ[volume] fun _ => 0 := by
      filter_upwards [hgen] with π hπ
      have hz : (fun w => T (cntOver S π w))
          =ᵐ[volume.restrict (Metric.ball (0 : EuclideanSpace ℂ (Fin (e + 1))) 1)] fun _ => 0 := by
        filter_upwards [ae_restrict_of_ae hπ] with w hw
        simp only [T, hw, if_true]
      rw [lintegral_congr_ae hz, lintegral_zero, mul_zero]
    rw [lintegral_congr_ae hae, lintegral_zero]
  rw [hlhs] at hcross
  have hball : volume (Metric.ball (0 : EuclideanSpace ℂ (Fin (e + 1))) 1) ≠ 0 :=
    (Metric.measure_ball_pos volume _ one_pos).ne'
  have hrhs : ∫⁻ (π : Fin (e + 1) → Fin n → ℂ), matGauss π * T (cntOver S π (firstCoordVec (e + 1))) = 0 :=
    (mul_eq_zero.mp hcross.symm).resolve_left hball
  have hp : Measurable (fun π : Fin (e + 1) → Fin n → ℂ => (π, firstCoordVec (e + 1))) :=
    measurable_id.prodMk measurable_const
  have hmeasc := Measurable.comp
    (g := fun p : (Fin (e + 1) → Fin n → ℂ) × EuclideanSpace ℂ (Fin (e + 1)) => cntOver S p.1 p.2)
    (f := fun π : Fin (e + 1) → Fin n → ℂ => (π, firstCoordVec (e + 1))) (_root_.GlobalTheory.CompanionTheory.Ar.Short.Crofton.measurable_cntOver n (e + 1) S hsc) hp
  have hmg : Measurable (matGauss : (Fin (e + 1) → Fin n → ℂ) → ℝ≥0∞) := by
    unfold matGauss
    fun_prop
  have hz := (lintegral_eq_zero_iff (hmg.mul (hT.comp hmeasc))).mp hrhs
  filter_upwards [hz] with π hπ
  have hg : matGauss π ≠ 0 := by
    unfold matGauss
    exact (ENNReal.ofReal_pos.mpr (Real.exp_pos _)).ne'
  have hT0 : T (cntOver S π (firstCoordVec (e + 1))) = 0 :=
    (mul_eq_zero.mp hπ).resolve_left hg
  have hc : cntOver S π (firstCoordVec (e + 1)) = (δ : ℝ≥0∞) := by
    by_contra hne
    simp only [T, hne, if_false, one_ne_zero] at hT0
  have hc' : (((fibrePts S π).encard : ℕ∞) : ℝ≥0∞) = ((δ : ℕ∞) : ℝ≥0∞) := by
    rw [ENat.toENNReal_coe]
    exact hc
  exact ENat.toENNReal_inj.mp hc'

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.CompanionTheory.Relay.ae_fibre_points_card_eq_degree : ∀ (n e δ : ℕ) (h : HermNorm n) (W : Ideal (MvPolynomial (Fin n) ℂ))
  (f : MvPolynomial (Fin (e + 1) × Fin n) ℂ), IsProjPrime W → IsChowForm W (e + 1) f → IsMultiHomog δ f →
    ∀ᵐ π : Fin (e + 1) → Fin n → ℂ, (fibrePts (coneSet h W) π).encard = δ := by
  intro n e δ h W f hW hf hd
  apply ae_fibre_encard_eq (coneSet h W) (isScaleStable_coneSet h hW)
    (by simpa using isSigmaCompact_cone_inter h W (A := Set.univ) isOpen_univ) δ
  filter_upwards [GroundTheory.Heights₂.Heights.ConeFibreDegree.full n e δ h W f hW hf hd] with π hπ
  filter_upwards [hπ] with w hw
  show ((fibreCount h W π w : ℕ∞) : ℝ≥0∞) = _
  rw [hw]
  rfl
end

-- bundled from Development.AutomorphicSpectrum.Proofs.AlgebraProofs.FlagPlainValueIndependent
section
namespace GlobalTheory.CompanionTheory.CommAlg.FlagPlainValue


open GroundTheory.Heights₂.Heights.NumbersDVR in
theorem main : GroundTheory.Heights₂.Heights.NumbersDVR.FlagPlainValueIndependence.Statement :=
  FlagPlainValueIndependence.proof _root_.GlobalTheory.CompanionTheory.CommAlg.FlagIndependence.main FlagPairCharacterisation.proof VerticalDivisorSupportFibre.proof

end GlobalTheory.CompanionTheory.CommAlg.FlagPlainValue
end

-- bundled from Development.AutomorphicSpectrum.Proofs.AlgebraProofs.FormalGroupChartFamily
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry TensorProduct Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.Pdiv.ChartF ReciprocityTheory.ChartRestriction.G.Pdiv.AvDefs
open ReciprocityTheory.PGsh ReciprocityTheory.PGsh.Up ReciprocityTheory.PGsh.Be2 GlobalTheory.ChF
open ReciprocityTheory.ChartRestriction.G.Chart (sp spMap)
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.CompanionTheory.Ar.GR

set_option autoImplicit false

namespace GlobalTheory.CompanionTheory.Ar.GR

private theorem thetaBar_surj (p : ℕ) [Fact p.Prime] {C : Type} [Field C] [IsAlgClosed C] [CharZero C]
    {v : Valuation C NNReal} (O : Type) [CommRing O] [Algebra O C] [Fact ¬IsUnit (p : O)]
    [IsAdicComplete (Ideal.span {(p : O)}) O] (hv : v.Integers O) (ε : PreTilt O p)
    (hε : IsPrimitiveRoot (((frobeniusEquiv (PreTilt O p) p).symm ε).untilt) p) :
    Function.Surjective (Ainf.thetaBar p O hv ε hε) := by
  intro b
  obtain ⟨a, rfl⟩ := Ainf.theta_surj p O hv b
  exact ⟨Ideal.Quotient.mk _ a, rfl⟩

private theorem thetaBar_mul (p : ℕ) [Fact p.Prime] {C : Type} [Field C] [IsAlgClosed C] [CharZero C]
    {v : Valuation C NNReal} (O : Type) [CommRing O] [Algebra O C] [Fact ¬IsUnit (p : O)]
    [IsAdicComplete (Ideal.span {(p : O)}) O] (hv : v.Integers O) (ε : PreTilt O p)
    (hε : IsPrimitiveRoot (((frobeniusEquiv (PreTilt O p) p).symm ε).untilt) p)
    (x y : Ainf.R0 p O ε) (hx : x ∈ RingHom.ker (Ainf.thetaBar p O hv ε hε))
    (hy : y ∈ RingHom.ker (Ainf.thetaBar p O hv ε hε)) : x * y = 0 := by
  obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective x
  obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective y
  have ha : a ∈ RingHom.ker (WittVector.fontaineTheta O p) := hx
  have hb : b ∈ RingHom.ker (WittVector.fontaineTheta O p) := hy
  rw [Ainf.ker_theta p O hv ε hε, Ideal.mem_span_singleton'] at ha hb
  obtain ⟨a', rfl⟩ := ha
  obtain ⟨b', rfl⟩ := hb
  rw [← map_mul, Ideal.Quotient.eq_zero_iff_mem]
  exact Ideal.mem_span_singleton'.2 ⟨a' * b', by ring⟩

private theorem ptOf_act {R₀ : Type} [CommRing R₀] (p : ℕ) [Fact p.Prime] (g : ℕ) (B : BX R₀) (O : LAlg R₀)
    (τ : Ix g → ℕ → B.G O) (h0 : ∀ i, p • τ i 0 = 0) (f : B.G O →+ B.G O)
    (M : Matrix (Ix g) (Ix g) ℤ_[p])
    (hf : ∀ j, f (τ j 0) = ∑ k, (PadicInt.toZModPow (0 + 1) (M k j)).val • τ k 0) (t : TT p g) :
    f (ptOf B τ (red p g t)) = ptOf B τ (red p g (M *ᵥ t)) := by
  have hsum : ∀ (s : Finset (Ix g)) (c : Ix g → ZMod p) (x : B.G O), p • x = 0 →
      (∑ j ∈ s, c j).val • x = ∑ j ∈ s, (c j).val • x := by
    intro s c x hx
    classical
    induction s using Finset.induction_on with
    | empty => simp
    | insert b s hb ih =>
      rw [Finset.sum_insert hb, Finset.sum_insert hb, GlobalTheory.TateMatrices.val_add_smul _ _ x hx, ih]
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [ptOf, red, map_sum, map_nsmul, hf]
  have hred : ∀ k, PadicInt.toZMod ((M *ᵥ t) k) = ∑ j, PadicInt.toZMod (M k j) * PadicInt.toZMod (t j) := by
    intro k
    set_option synthInstance.maxHeartbeats 100000 in
      simp [Matrix.mulVec, dotProduct, map_sum, map_mul]
  simp only [hred]
  simp_rw [Finset.smul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [hsum _ _ _ (h0 k)]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [mul_comm, GlobalTheory.TateMatrices.val_mul_smul _ _ _ (h0 k), GlobalTheory.TateMatrices.toZMod_val_smul _ _ (h0 k)]

private theorem htd_of_dat {R₀ : Type} [CommRing R₀] (p : ℕ) [Fact p.Prime] (C : Type) [Field C]
    (v : Valuation C NNReal) (Tw : ATowerL R₀ p) [Algebra (Tw.O : Type) C] (hv : v.Integers (Tw.O : Type))
    (hp : ¬IsUnit (p : (Tw.O : Type))) (hc : IsAdicComplete (Ideal.span {(p : (Tw.O : Type))}) (Tw.O : Type))
    [Algebra ℤ_[p] (Tw.O : Type)] (g : ℕ) (OE : Type) [CommRing OE] [StarRing OE]
    (B : BX R₀) (F : FGLaw (Tw.O : Type) g)
    (Y : ∀ R : LAlg R₀, LHom Tw.O R → (Fin g → (R : Type)) → B.G R) (hY : BXChart B Tw.O F.F Y)
    (α : OE → Fin g → PS (Tw.O : Type) 1 g) (hα : ∀ a j, MvPowerSeries.constantCoeff (α a j) = 0)
    (A : OE → OEnd B Tw.O)
    (hA : ∀ b (R : LAlg R₀) (s : LHom Tw.O R) (a : Fin g → (R : Type)), (∀ i, IsNilpotent (a i)) →
      (A b).f s (Y R s a) = Y R s (fun j => nv s.1.toRingHom (α b j) ![a]))
    (Dt : DualTower Tw) (cp : (Tw.O : Type)) (D : Dat p g B Tw Dt (ℤ_[p] ⊗[ℤ] OE) (sigE p OE) cp)
    (h₁ : D.H.P = 0) (h₂ : D.H.PL = 0)
    (h₃ : ∀ a {R S : LAlg R₀} (s : LHom Tw.O R) (π : LHom R S) (hπ : π.SqZero) (l : Fin g) (i : π.ker)
      (m : Fin g → π.ker), (∀ k, (m k : (R : Type)) = s.1 (D.H.ρL (1 ⊗ₜ[ℤ] a) k l) * i) →
      (A a).f s (B.tg π hπ (D.ch.gb l ⊗ₜ[R₀] i)) = B.tg π hπ (∑ k, D.ch.gb k ⊗ₜ[R₀] m k)) :
    ∃ (H : HodgeTateDatum p g v (Tw.O : Type) (ℤ_[p] ⊗[ℤ] OE) (sigE p OE) cp) (S : Matrix (Fin g) (Fin g) (Tw.O : Type)),
      H.P = 0 ∧ H.PL = 0 ∧ IsUnit S ∧ (∀ a : OE, lin (α a) * S = S * H.ρL (1 ⊗ₜ[ℤ] a)) ∧
      (∀ i, ∃ u : PS (Tw.O : Type) 1 g, IsCh F.F u ∧ Sᵀ *ᵥ dl u = fun l => H.Ht l i) ∧
      H.AA.carrier = D.evImg C ∧ H.ρ = D.H.ρ := by
  obtain ⟨S, hS, hT⟩ := _root_.GlobalTheory.ChF.exists_tanMat R₀ B Tw.O g F Y hY D.ch.gb
  refine ⟨GlobalTheory.EvClose.htdOfDat D C v (Function.Injective.isDomain _ hv.hom_inj) hv.hom_inj, S, h₁, h₂, hS,
    fun a => ?_, fun i => ?_, rfl, rfl⟩
  · exact _root_.GlobalTheory.ChF.lin_mul_tanMat R₀ B Tw.O g F Y hY D.ch.gb S hT (A a) (α a) _ (hα a) (hA a) (h₃ a)
  · obtain ⟨u, hu, hP⟩ := _root_.GlobalTheory.ChF.exists_character_pairSer R₀ B Tw.O g F Y hY p hp hc (D.L.τ i) (D.L.τ_tors i) (D.L.τ_compat i)
    refine ⟨u, hu, ?_⟩
    rw [_root_.GlobalTheory.ChF.dl_pairSer_eq_height R₀ B p Tw Dt g Y D.ch.gb S hT (D.L.τ i) u hu.1 hP (D.L.ht i) (D.L.ht_spec i)]
    funext l
    exact (D.L.Ht_eq l i).symm

private theorem htd_of_tower (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C]
    (v : Valuation C NNReal) (O : Type) [CommRing O] [Algebra O C] [Fact ¬IsUnit (p : O)]
    [IsAdicComplete (Ideal.span {(p : O)}) O] (hv : v.Integers O) (ε : PreTilt O p)
    (hε : IsPrimitiveRoot (((frobeniusEquiv (PreTilt O p) p).symm ε).untilt) p)
    (Tw : ATowerL (Ainf.R0 p O ε) p) (hTw : Tw = Ainf.ainfTowerL p O hv ε hε)
    [Algebra (Tw.O : Type) C] (hv' : v.Integers (Tw.O : Type))
    [hp : Fact ¬IsUnit (p : (Tw.O : Type))]
    [hc : IsAdicComplete (Ideal.span {(p : (Tw.O : Type))}) (Tw.O : Type)]
    [Algebra ℤ_[p] (Tw.O : Type)] (hvp : v (p : C) < 1)
    (T : Type) [CommRing T] [IsNoetherianRing T] (P₀ : Out.PolAV (Geo.Tor.Sp T)) (io : T →+* (Tw.O : Type))
    (P : Out.PolAV (Geo.Tor.Sp (Tw.O : Type))) (φ : P.A.left ⟶ P₀.A.left)
    (h₁ : Geo.Tor.IsGrpPullback P.A P₀.A (Geo.Tor.spMap io) φ) (h₂ : Geo.Tor.LBIso P.L (P₀.L.pull φ))
    (h₃ : P.g = P₀.g) (h₄ : 1 ≤ P.g) (OE : Type) [CommRing OE] [StarRing OE] (o : P.OAct OE)
    (F : FGLaw (Tw.O : Type) P.g) (X : Fam P.A P.g) (hX : NilChart P.A F.F X)
    (α : OE → Fin P.g → PS (Tw.O : Type) 1 P.g) (hα : ∀ a, Reads X X (o.act a) (α a)) :
    ∃ (H : HodgeTateDatum p P.g v (Tw.O : Type) (ℤ_[p] ⊗[ℤ] OE) (sigE p OE) Tw.c)
      (S : Matrix (Fin P.g) (Fin P.g) (Tw.O : Type))
      (pt : Nb p P.g → (sp (R₀ := (Tw.O : Type)) (Tw.O : Type) ⟶ P.A)),
      H.P = 0 ∧ H.PL = 0 ∧ IsUnit S ∧ (∀ a : OE, lin (α a) * S = S * H.ρL (1 ⊗ₜ[ℤ] a)) ∧
      (∀ i, ∃ u : PS (Tw.O : Type) 1 P.g, IsCh F.F u ∧ Sᵀ *ᵥ dl u = fun l => H.Ht l i) ∧
      IsTorsPts P.A p pt ∧ (∀ T : TorsRep P.A p, H.AA.carrier = torsFun C T pt) ∧
      ∀ (a : OE) (t : TT p P.g), pt (red p P.g (H.ρ (1 ⊗ₜ[ℤ] a) *ᵥ t)) = pt (red p P.g t) ≫ o.act a := by
  have hsurj : Function.Surjective (algebraMap (Ainf.R0 p O ε) (Tw.O : Type)) := by
    subst hTw; exact thetaBar_surj p O hv ε hε
  have hmul : ∀ x y : Ainf.R0 p O ε, x ∈ RingHom.ker (algebraMap (Ainf.R0 p O ε) (Tw.O : Type)) →
      y ∈ RingHom.ker (algebraMap (Ainf.R0 p O ε) (Tw.O : Type)) → x * y = 0 := by
    subst hTw; exact thetaBar_mul p O hv ε hε
  have hker : RingHom.ker (algebraMap (Ainf.R0 p O ε) (Tw.O : Type)) ^ 2 = ⊥ := by
    refine (pow_two _).trans (eq_bot_iff.2 ?_)
    exact Ideal.mul_le.2 fun x hx y hy => (Submodule.mem_bot _).2 (hmul x y hx hy)
  haveI : IsLocalRing (Ainf.R0 p O ε) := Ainf.local_of_surj_sq _ hsurj (fun k hk => hmul k k hk hk)
  obtain ⟨G, iG, cG, Q, ψ, ψ₂, hab, hQ, t₁, t₂, hsym, hamp, hnd, hpb, hsq, hΛ⟩ :=
    _root_.GlobalTheory.AbelianLift.exists_lift p C v (Tw.O : Type) hv' T P₀ io P φ h₁ h₂ h₃ h₄ _ _ hsurj hker
  letI : Algebra (Ainf.R0 p O ε) C :=
    ((algebraMap (Tw.O : Type) C).comp (algebraMap (Ainf.R0 p O ε) (Tw.O : Type))).toAlgebra
  haveI : IsScalarTower (Ainf.R0 p O ε) (Tw.O : Type) C := IsScalarTower.of_algebraMap_eq fun _ => rfl
  have hp0 : 1 ≤ p := (Fact.out : p.Prime).one_lt.le
  have hsm := _root_.GlobalTheory.LiftDim.smoothOfRelativeDimension_of_isGrpPullback _ _ _ G P.A ψ P.g hab hpb P.smoothDim
  obtain ⟨hθ, hn⟩ := _root_.GlobalTheory.ChF.exists_gen_theta_tensor_and_finite_flat_surjective_pow _ G _ Q hab (LB.isLB_pull hQ _) hamp hQ
  obtain ⟨hf₁, hf₂, hf₃⟩ := hn p hp0
  have hcard := GlobalTheory.T.card_torsion_of_polarisedAbelianScheme_lift _ _ C G P ψ hpb p (Nat.cast_ne_zero.2 (Fact.out : p.Prime).ne_zero)
  have hros := fun a : OE =>
    GlobalTheory.T.exists_generator_of_rosatiAdjoint_lambdaBundle _ P _ Q ψ₂ hQ hΛ _ _ (o.hom a) (o.hom (star a)) (o.rosati a)
  have key : ∃ (B : BX (Ainf.R0 p O ε)) (e : ∀ R : LAlg (Ainf.R0 p O ε), B.G R → (sp (R₀ := (Ainf.R0 p O ε)) (R : Type) ⟶ G)) (Ad : OE → OAdj B Tw.O), (∀ R, Function.Bijective (e R)) ∧ (∀ R x y, e R (x + y) = e R x * e R y) ∧ (∀ {R S : LAlg (Ainf.R0 p O ε)} (f : LHom R S) (x : B.G R), e S (B.map f x) = spMap f.1 ≫ e R x) ∧ (∀ a, (∀ {R : LAlg (Ainf.R0 p O ε)} (s : LHom Tw.O R) (x : B.G R) (x' : Over.mk (Spec.map (CommRingCat.ofHom s.1.toRingHom)) ⟶ P.A), x'.left ≫ ψ = (e R x).left → (x' ≫ o.act a).left ≫ ψ = (e R ((Ad a).a.f s x)).left)) ∧ ∃ (Dt : DualTower Tw) (D : Dat p P.g B Tw Dt (ℤ_[p] ⊗[ℤ] OE) (sigE p OE) Tw.c), D.H.P = 0 ∧ D.H.PL = 0 ∧ (∀ a {R S : LAlg (Ainf.R0 p O ε)} (s : LHom Tw.O R) (π : LHom R S) (hπ : π.SqZero) (l : Fin P.g) (i : π.ker) (m : Fin P.g → π.ker), (∀ k, (m k : (R : Type)) = s.1 (D.H.ρL (1 ⊗ₜ[ℤ] a) k l) * i) → (Ad a).a.f s (B.tg π hπ (D.ch.gb l ⊗ₜ[(Ainf.R0 p O ε)] i)) = B.tg π hπ (∑ k, D.ch.gb k ⊗ₜ[(Ainf.R0 p O ε)] m k)) ∧ (∀ a j, (Ad a).a.f (LHom.id Tw.O) (D.L.τ j 0) = ∑ k, (PadicInt.toZModPow (0 + 1) (D.H.ρ (1 ⊗ₜ[ℤ] a) k j)).val • D.L.τ k 0) := by
    subst hTw
    obtain ⟨B, e, Ad, k₁, k₂, k₃, k₄, Dt, D, k₅, k₆, k₇, k₈⟩ :=
      GlobalTheory.T.exists_periodTowerDatum_of_abelianScheme_symmetricBundle p O hv ε hε P.g G Q hab hsm hQ hθ t₁ t₂ hsym hf₁ hf₂ hf₃ hv' (hnd _) hcard
        P.A ψ ψ₂ P.isAb hpb hsq OE (cjZ OE) o.toRingAct (fun a => star_star a) hros
    exact ⟨B, e, Ad, k₁, k₂, k₃, k₄, Dt, D, k₅, k₆, k₇, fun a j => k₈ a j 0⟩
  obtain ⟨B, e, Ad, k₁, k₂, k₃, k₄, Dt, D, k₅, k₆, k₇, k₈⟩ := key
  obtain ⟨Y, hY, hR⟩ := GlobalTheory.T.abelianFunctorNilChart_of_nilpotent_chart _ G B e k₁ k₂ k₃ Tw.O P.A ψ hpb P.g F.F X hX
  obtain ⟨H, S, e₁, e₂, e₃, e₄, e₅, e₆, e₇⟩ :=
    htd_of_dat p C v Tw hv' hp.out hc P.g OE B F Y hY α (fun a => (hα a).1) (fun a => (Ad a).a)
      (fun b => hR _ _ _ (hα b) (k₄ b)) Dt Tw.c D k₅ k₆ k₇
  obtain ⟨pt, hpt, hT, hE⟩ :=
    GlobalTheory.T.dual_tower_hodge_tate_datum p C v P.g B Tw Dt hv' hvp _ (sigE p OE) Tw.c D G e k₁ k₂ k₃ P.A ψ hpb
  refine ⟨H, S, pt, e₁, e₂, e₃, e₄, e₅, hT, fun T => e₆.trans (hE T), fun a t => ?_⟩
  have h0 : ∀ i, p • D.L.τ i 0 = 0 := fun i => by
    have h := D.L.τ_tors i 0
    rwa [zero_add, pow_one] at h
  have hAct := ptOf_act p P.g B Tw.O D.L.τ h0 ((Ad a).a.f (LHom.id Tw.O)) (D.H.ρ (1 ⊗ₜ[ℤ] a)) (k₈ a) t
  have hA := k₄ a (LHom.id Tw.O) (ptOf B D.L.τ (red p P.g t)) (pt (red p P.g t)) (hpt _)
  rw [hAct] at hA
  rw [e₇]
  apply Over.OverMorphism.ext
  apply hpb.1.hom_ext
  · rw [hpt]
    exact hA.symm
  · simp

theorem exists_htd_act : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (O : Type) [CommRing O] [Algebra O C], v.Integers O → ∀ [Fact ¬IsUnit (p : O)] [IsAdicComplete (Ideal.span {(p : O)}) O] [Algebra ℤ_[p] O] (P : Out.PolAV (Geo.Tor.Sp O)), 1 ≤ P.g → ∀ (g : ℕ), P.g = g → ∀ (OE : Type) [CommRing OE] [StarRing OE] (o : P.OAct OE) (F : FGLaw O g) (X : Fam P.A g), NilChart P.A F.F X → ∀ α : OE → Fin g → PS O 1 g, (∀ a, Reads X X (o.act a) (α a)) → ∃ (cp : O) (_ : HodgeTateSetting p v O (ℤ_[p] ⊗[ℤ] OE) (sigE p OE) cp) (H : HodgeTateDatum p g v O (ℤ_[p] ⊗[ℤ] OE) (sigE p OE) cp) (S : Matrix (Fin g) (Fin g) O) (pt : Nb p g → (sp (R₀ := O) O ⟶ P.A)), H.P = 0 ∧ H.PL = 0 ∧ IsUnit S ∧ (∀ a : OE, lin (α a) * S = S * H.ρL (1 ⊗ₜ[ℤ] a)) ∧ (∀ i, ∃ u : PS O 1 g, IsCh F.F u ∧ Sᵀ *ᵥ dl u = fun l => H.Ht l i) ∧ IsTorsPts P.A p pt ∧ (∀ T : TorsRep P.A p, H.AA.carrier = torsFun C T pt) ∧ ∀ (a : OE) (t : TT p g), pt (red p g (H.ρ (1 ⊗ₜ[ℤ] a) *ᵥ t)) = pt (red p g t) ≫ o.act a := by
  intro p _ C _ _ _ v O _ iA hv iF iC iZ P h₄ g hg OE _ _ o F X hX α hα
  subst hg
  haveI : IsDomain O := Function.Injective.isDomain _ hv.hom_inj
  haveI : IsLocalRing O := Ainf.O_local O hv
  obtain ⟨R, P₀, φ, hft, hg₀, h₁, h₂⟩ := GlobalTheory.KeyTf.exists_polAV_finiteType_subring O P
  haveI : IsNoetherianRing R := Algebra.FiniteType.isNoetherianRing ℤ R
  have hvp : v (p : C) < 1 := by
    have h := lt_of_le_of_ne (hv.map_le_one (p : O)) fun h => iF.out (hv.isUnit_iff_valuation_eq_one.2 h)
    simpa using h
  obtain ⟨ε, hε⟩ := exists_eps (p := p) C v O hv
  exact ⟨_, _root_.GlobalTheory.ChF.hodgeTateSetting_ainfTower_of_isPrimitiveRoot p O hv ε hε OE,
    @htd_of_tower p _ C _ _ _ v O _ _ _ _ hv ε hε _ rfl iA hv iF
      iC iZ hvp R _ _ P₀ R.subtype P φ h₁ h₂ hg₀.symm h₄ OE _ _ o F X hX α hα⟩

end GlobalTheory.CompanionTheory.Ar.GR
end

-- bundled from Development.AutomorphicSpectrum.Proofs.AlgebraProofs.PairCocycle
section
namespace GlobalTheory.CompanionTheory.CommAlg.PairCocycleClosed

open GroundTheory.Heights₂.Heights.NumbersDVR

theorem pairCocycle : PairCocycle.Statement :=
  PairCocycle.proof _root_.GlobalTheory.CompanionTheory.CommAlg.FlagIndependence.main _root_.GlobalTheory.CompanionTheory.CommAlg.VerticalDivisors.verticalDivisorsCommute IntNumAddFirst.full

end GlobalTheory.CompanionTheory.CommAlg.PairCocycleClosed
end

-- bundled from Development.AutomorphicSpectrum.Proofs.AlgebraProofs.ScalarQuotientStatement
section
namespace GlobalTheory.CompanionTheory.Ar.Num.ScalarFlags

theorem main : GroundTheory.Heights₂.Heights.NumbersDVR.ScalarQuotient.Statement :=
  GroundTheory.Heights₂.Heights.NumbersDVR.ScalarQuotient.proof _root_.GlobalTheory.CompanionTheory.CommAlg.FlagIndependence.main

end GlobalTheory.CompanionTheory.Ar.Num.ScalarFlags
end

-- bundled from Development.AutomorphicSpectrum.Proofs.AlgebraProofs.SphereMeanNormalizedGroups
section
set_option maxSynthPendingDepth 1
open GroundTheory.Heights₂.Heights MeasureTheory MvPolynomial Matrix GlobalTheory.CompanionTheory.Ar.Short.Crofton
open scoped ENNReal

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.CompanionTheory.Relay.sphere_mean_normalized_groups : ∀ (n e : ℕ) (h : HermNorm n) (G : (Fin e × Fin n → ℂ) → ℝ),
  IntegrableOn (fun u => G (nrmGroups h e u)) (ballProd h e) →
    Integrable (fun π : Fin (e + 1) → Fin n → ℂ => G (nrmGroups h e (coefRows h π))) (gaussM (e + 1) n) ∧
      ∫ π, G (nrmGroups h e (coefRows h π)) ∂(gaussM (e + 1) n) =
        (gaussM (e + 1) n Set.univ).toReal * sphereMean h e G := by
  intro n e h G hint
  have hfin := (gaussM_univ_pos_lt_top (e + 1) n).2
  haveI : IsFiniteMeasure (gaussM (e + 1) n) := ⟨hfin⟩
  haveI : IsFiniteMeasure (volume.restrict (ballProd h e)) := ⟨by rw [Measure.restrict_apply_univ]; exact volume_ballProd_lt_top h e⟩
  obtain ⟨a, ha⟩ := ModelDimension.GSph.map_coefRows (e := e) h
  have hmap : Measure.map (coefRows h) (gaussM (e + 1) n) = Measure.map ModelDimension.GSph.scT ((a • (ModelDimension.GSph.exP e).withDensity (ModelDimension.GSph.wt h)).prod (volume.restrict (ballProd h e))) := by
    rw [ha, ModelDimension.GSph.layer, Measure.prod_smul_left, Measure.map_smul]
    exact ModelDimension.GSph.measurable_scT.aemeasurable
  have h1 : ∀ᵐ x ∂ModelDimension.GSph.ex1, 0 < x :=
    (withDensity_absolutelyContinuous _ _).ae_le (ae_restrict_mem measurableSet_Ioi)
  have hp : ∀ᵐ s ∂(ModelDimension.GSph.exP e), ∀ i, 0 < s i := by
    rw [ae_all_iff]
    intro i
    exact (Measure.tendsto_eval_ae_ae (μ := fun _ : Fin e => ModelDimension.GSph.ex1) (i := i)).eventually h1
  have hpos0 : ∀ᵐ s ∂((ModelDimension.GSph.exP e).withDensity (ModelDimension.GSph.wt h)), ∀ i, 0 < s i :=
    (withDensity_absolutelyContinuous _ _).ae_le hp
  have hpos : ∀ᵐ s ∂(a • (ModelDimension.GSph.exP e).withDensity (ModelDimension.GSph.wt h)), ∀ i, 0 < s i :=
    Measure.ae_smul_measure hpos0 a
  have hne : (volume.restrict (ballProd h e)) Set.univ ≠ 0 := by
    rw [Measure.restrict_apply_univ]
    exact (volume_ballProd_pos h e).ne'
  have haesm : AEStronglyMeasurable (fun u => G (nrmGroups h e u)) (Measure.map (coefRows h) (gaussM (e + 1) n)) := by
    rw [ha]
    exact ((ModelDimension.GSph.aesm h G hint.1).mono_ac (withDensity_absolutelyContinuous _ _)).smul_measure a
  have hinv : ∀ᵐ s ∂(a • (ModelDimension.GSph.exP e).withDensity (ModelDimension.GSph.wt h)), ∀ u, (fun u => G (nrmGroups h e u)) (ModelDimension.GSph.scT (s, u)) = (fun u => G (nrmGroups h e u)) u := by
    filter_upwards [hpos] with s hs u
    exact congrArg G (ModelDimension.GSph.nrm_sc h (fun i => Real.sqrt_pos.mpr (hs i)) u)
  have key := ModelDimension.GSph.transfer (gaussM (e + 1) n) (a • (ModelDimension.GSph.exP e).withDensity (ModelDimension.GSph.wt h)) (volume.restrict (ballProd h e)) hne (ModelDimension.GSph.measurable_coefRows h) ModelDimension.GSph.measurable_scT hmap haesm hinv hint
  refine ⟨key.1, ?_⟩
  rw [key.2]
  rfl
end

-- bundled from Development.AutomorphicSpectrum.Proofs.AlgebraProofs.SubQuotientStatement
section
namespace GlobalTheory.CompanionTheory.Ar.Num.SubQuotFlags

theorem main : GroundTheory.Heights₂.Heights.NumbersDVR.SubQuotient.Statement :=
  GroundTheory.Heights₂.Heights.NumbersDVR.SubQuotient.proof _root_.GlobalTheory.CompanionTheory.CommAlg.FlagIndependence.main

end GlobalTheory.CompanionTheory.Ar.Num.SubQuotFlags
end

