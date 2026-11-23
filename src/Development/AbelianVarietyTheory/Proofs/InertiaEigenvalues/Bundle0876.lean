module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0030
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0026
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0010
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.WeilDeligneParamAboveLIndependentLocalEmbedding
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0029
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0007
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.FiniteDimensionalWdSpace
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DeRhamPotSemistable
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0070
public import Formalism.SharpRestriction.LevelLetterCocycles.DataN
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0077
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FiniteDimensionalFilDR
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0107
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FinrankLetterHomComp
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0045
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0104
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0050
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0075
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0061
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0049
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0858
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0862
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0850
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0808
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsAddHaarMeasureVolumeLie
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.StrongMultiplicityOne
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0025
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0866
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0869
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0864
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0867
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0717
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0826
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DifferentiableIntegralMulCpow
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0833
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0857
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0618
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0021
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0020
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0828
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.T2SpaceAdelicGeneralLinearGroupNumberField
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AdelicUnitriangularMulMemUnipotentTimesIntegral
public import GroundTheory.AutomorphicForms.MultiplicityOne.Injective
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0697
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0617
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0727
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.UnivChar

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.InertiaPolynomialKillsPotentiallyCrystallineModu
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin GlobalTheory.PendOf
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations
open TensorProduct

namespace GlobalTheory.KillLocal

theorem actPow {G : Type} [Group G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    (PD : PeriodData G Qp K₀ K B BdR)
    {LL : Type} [Field LL] [Algebra Qp LL]
    {V : Type} [AddCommGroup V] [Module LL V] [Module Qp V] [IsScalarTower Qp LL V]
    (ρ : Representation LL G V) (g : G) (n : ℕ) (x : V ⊗[Qp] B) :
    actVB PD ρ (g ^ n) x = (actVB PD ρ g ^ n) x := by
  induction n generalizing x with
  | zero =>
    induction x using TensorProduct.induction_on with
    | zero => simp
    | tmul v b => simp [actVB]
    | add a b ha hb => rw [map_add (f := _), ha, hb, map_add (f := _)]
  | succ n ih =>
    rw [pow_succ, pow_succ, Module.End.mul_apply, ← ih]
    induction x using TensorProduct.induction_on with
    | zero => simp
    | tmul v b => simp [actVB, map_mul, AlgEquiv.mul_apply]
    | add a b ha hb => rw [map_add (f := _), ha, hb, map_add (f := _), map_add (f := _)]

theorem sumAeval {O LL M : Type} [CommRing O] [Field LL] [AddCommGroup M] [Module LL M] (f : O →+* LL)
    (T : Module.End LL M) (p : O[X]) (x : M) :
    ∑ n ∈ Finset.range (p.natDegree + 1), f (p.coeff n) • (T ^ n) x = Polynomial.aeval T (p.map f) x := by
  rw [Polynomial.aeval_eq_sum_range' (n := p.natDegree + 1) (Nat.lt_succ_of_le Polynomial.natDegree_map_le)]
  rw [LinearMap.sum_apply]
  simp only [LinearMap.smul_apply, Polynomial.coeff_map]

set_option synthInstance.maxHeartbeats 400000 in
theorem main : ∀ (D : D7) (i : D.nd.Loc) (w : HeightOneSpectrum (𝓞 D.host.E)) (hw : w ∈ placesOver D.host.E (D.nd.l i)) (K' : FinExt (D.nd.l i)) (h : (D.nbr i w hw).Kw.1 ≤ K'.1) (hN : (GKin h).Normal) (hF : (GKin h).FiniteIndex) (hS : ∀ (g : ↥(GK (D.nbr i w hw).Kw)) (c : ↥(K0 K')), ∃ c' : ↥(K0 K'), ((D.loc (D.nd.l i)).PD (D.nbr i w hw).Kw).actB g (algebraMap ↥(K0 K') (D.loc (D.nd.l i)).R.B c) = algebraMap ↥(K0 K') (D.loc (D.nd.l i)).R.B c') (m : ℕ) (r : GE D.nd →* GL (Fin m) (D.nd.O i)), Continuous (fun g => ((r g : GL _ _) : Matrix (Fin m) (Fin m) (D.nd.O i))) → (pc (D.loc (D.nd.l i)) h hN hF hS).IsPotCrys ((D.nbr i w hw).rep (r.comp (decS D.nd w))) → ∀ σ : Gw D.nd w, (σ : GE D.nd) ∈ Ine (F := D.host.E) (D.nd.plOm.1 w) → ∀ p : (D.nd.O i)[X], p.map (iotaO D.nd D.naut i) = (GlobalTheory.Pst.wdAt (D.loc (D.nd.l i)) (D.naut.iotaQC i) (D.nbr i w hw) (D.nd.plOm.2 w) (D.nbr_ind i w hw) (GlobalTheory.Pst.resDec D.nd.plOm.1 (mapRep (iotaOQ D.nd D.naut i) r) w)).inePol (σ : GE D.nd) → ∀ d ∈ (pc (D.loc (D.nd.l i)) h hN hF hS).Dpcris ((D.nbr i w hw).rep (r.comp (decS D.nd w))), ∑ n ∈ Finset.range (p.natDegree + 1), (D.nbr i w hw).toLL (p.coeff n) • actVB ((D.loc (D.nd.l i)).PD (D.nbr i w hw).Kw) ((D.nbr i w hw).rep (r.comp (decS D.nd w))) ((D.nbr i w hw).e (σ ^ n)) d = 0 := by
  intro D i w hw K' h hN hF hS m r hr hpc σ hσ p hp d hd
  have hPst := _root_.GlobalTheory.PstOfCrys.pst_of_pc D i w hw K' h hN hF hS m r hr hpc
  obtain ⟨LL', hL, hV', hchar⟩ := GlobalTheory.T.charPoly_inertia_of_potSemistable_enlargement D i w hw m r hPst
  have hq := hchar σ hσ p hp
  have hkill := GlobalTheory.T.aeval_inertia_eq_zero_potSemistableDieudonne (D.loc (D.nd.l i)) (D.locA (D.nd.l i)) (D.locT (D.nd.l i)) (D.naut.iotaQC i) (D.nbr i w hw) (D.nd.plOm.2 w) (D.nbr_ind i w hw) _ hV' ⟨(σ : GE D.nd), hσ⟩ _ hq
  have hinj : Function.Injective (GlobalTheory.PstLine.incV hL m) := by
    intro x y hxy
    funext j
    exact (IntermediateField.inclusion hL).injective (congrFun hxy j)
  have hd' := _root_.GlobalTheory.PcrisPst.aeval_eq_zero_of_kills_Dpst (D.loc (D.nd.l i)) (D.nbr i w hw).Kw K' (D.nbr i w hw).LL LL' h hN hF hS hL _ _ (GlobalTheory.PstLine.incV hL m) hinj (GlobalTheory.PstLine.isMor_incV (D.nbr i w hw) hL m _) _ (p.map (D.nbr i w hw).toLL) hkill d hd
  have hg : GlobalTheory.Pst.weilToGK (D.nbr i w hw) (D.nd.plOm.2 w) (GlobalTheory.WeilDeligne.ineIncl (D.nd.plOm.2 w) ⟨(σ : GE D.nd), hσ⟩) = (D.nbr i w hw).e σ := rfl
  have key : ∑ n ∈ Finset.range (p.natDegree + 1), (D.nbr i w hw).toLL (p.coeff n) • ((actVB ((D.loc (D.nd.l i)).PD (D.nbr i w hw).Kw) ((D.nbr i w hw).rep (r.comp (decS D.nd w))) ((D.nbr i w hw).e σ)) ^ n) d = 0 := by
    rw [sumAeval]
    exact hd'
  refine (Finset.sum_congr rfl fun n _ => ?_).trans key
  have e1 : (D.nbr i w hw).e (σ ^ n) = (D.nbr i w hw).e σ ^ n := map_pow _ σ n
  exact congrArg _ ((congrArg (fun g => actVB ((D.loc (D.nd.l i)).PD (D.nbr i w hw).Kw) ((D.nbr i w hw).rep (r.comp (decS D.nd w))) g d) e1).trans (actPow _ _ _ _ _))

end GlobalTheory.KillLocal
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IntegralAbsDetCpowBoundedShellEntire
section
open NumberField Matrix MeasureTheory Filter Topology GlobalTheory.CuspRep GlobalTheory.UnitaryBC GroundTheory.Global.IdeleGroup Formalism.L2.Host
open scoped nonZeroDivisors ComplexConjugate

namespace GlobalTheory.DiffInt

theorem integral_absDet_cpow_entire : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a : ℕ) (μ : Measure (GA E a)) (S : Set (GA E a)), NullMeasurableSet S μ → μ S < ⊤ → ∀ c : ℝ, 0 < c → (∀ g ∈ S, c ≤ (ideleModule E (GeneralLinearGroup.det g) : ℝ) ∧ (ideleModule E (GeneralLinearGroup.det g) : ℝ) ≤ 1) → ∀ F : GA E a → ℂ, Continuous F → ∀ C : ℝ, (∀ g, ‖F g‖ ≤ C) → Differentiable ℂ fun s : ℂ => ∫ g in S, F g * ((ideleModule E (GeneralLinearGroup.det g) : ℝ) : ℂ) ^ (s - 1) ∂μ := by
  intro E _ _ _ a μ S hS hμS c hc hδ F hF C hC
  set δ : GA E a → ℝ := fun g => (ideleModule E (GeneralLinearGroup.det g) : ℝ) with hδdef
  have hδc : Continuous δ := GlobalTheory.RSThetaLow.continuous_absDet
  have hae : ∀ᵐ g ∂(μ.restrict S), g ∈ S := ae_restrict_mem₀ hS
  haveI : IsFiniteMeasure (μ.restrict S) := isFiniteMeasure_restrict.mpr hμS.ne
  have key := GlobalTheory.integral_mul_cpow_of_rapid_decay_entire (GA E a) (μ.restrict S) δ F hδc.measurable
    (hae.mono fun g hg => ⟨lt_of_lt_of_le hc (hδ g hg).1, (hδ g hg).2⟩)
    (by
      refine Integrable.mono' (integrable_const (1 : ℝ)) hδc.aestronglyMeasurable ?_
      refine hae.mono fun g hg => ?_
      rw [Real.norm_eq_abs, abs_of_nonneg (le_trans hc.le (hδ g hg).1)]
      exact (hδ g hg).2)
    hF.aestronglyMeasurable
    (by
      intro K
      refine ⟨max C 0 / c ^ K, hae.mono fun g hg => ?_⟩
      have hcK : 0 < c ^ K := pow_pos hc K
      have h1 : c ^ K ≤ δ g ^ K := pow_le_pow_left₀ hc.le (hδ g hg).1 K
      rw [div_mul_eq_mul_div, le_div_iff₀ hcK]
      calc ‖F g‖ * c ^ K ≤ max C 0 * c ^ K :=
            mul_le_mul_of_nonneg_right ((hC g).trans (le_max_left _ _)) hcK.le
        _ ≤ max C 0 * δ g ^ K := mul_le_mul_of_nonneg_left h1 (le_max_right _ _))
  have := key.2.comp (differentiable_id.sub_const (1 : ℂ))
  exact this

end GlobalTheory.DiffInt
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IntegralDetLeOneEqGeometricSeriesShells
section
open NumberField Matrix MeasureTheory Filter Topology GlobalTheory.CuspRep GlobalTheory.UnitaryBC GroundTheory.Global.IdeleGroup Formalism.L2.Host
open scoped nonZeroDivisors ComplexConjugate

noncomputable section

namespace GlobalTheory.RSThetaGeom

theorem integral_low_geometric : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a : ℕ), 0 < a → ∀ (μ : Measure (GA E a)) [μ.IsHaarMeasure] (𝓕 : Set (GA E a)), IsFundamentalDomain (ratGL E a).range 𝓕 μ → ∀ (F : GA E a → ℂ), Continuous F → ∀ C : ℝ, (∀ g, ‖F g‖ ≤ C) → (∀ (γ : GL (Fin a) E) (g : GA E a), F (ratGL E a γ * g) = F g) → ∀ χ : ℂ, ‖χ‖ = 1 → (∀ g, F (splitCentre E a 1 * g) = χ * F g) → ∀ s : ℂ, 1 < s.re → ∫ g in 𝓕 ∩ {g | (ideleModule E (GeneralLinearGroup.det g) : ℝ) ≤ 1}, F g * ((ideleModule E (GeneralLinearGroup.det g) : ℝ) : ℂ) ^ (s - 1) ∂μ = (∫ g in 𝓕 ∩ {g | Real.exp (-((a : ℝ) * (Module.finrank ℚ E : ℝ))) < (ideleModule E (GeneralLinearGroup.det g) : ℝ) ∧ (ideleModule E (GeneralLinearGroup.det g) : ℝ) ≤ 1}, F g * ((ideleModule E (GeneralLinearGroup.det g) : ℝ) : ℂ) ^ (s - 1) ∂μ) / (1 - starRingEnd ℂ χ * Complex.exp (-((((a : ℝ) * (Module.finrank ℚ E : ℝ) : ℝ) : ℂ) * (s - 1)))) := by
  intro E _ _ _ a ha μ _ 𝓕 h𝓕 F hF C hC hinv χ hχ hχF s hs
  set δ : GA E a → ℝ := fun g => (ideleModule E (GeneralLinearGroup.det g) : ℝ) with hδ
  set L : ℝ := (a : ℝ) * (Module.finrank ℚ E : ℝ) with hLdef
  set e : GA E a := splitCentre E a 1 with he
  have hδc : Continuous δ := GlobalTheory.RSTheta.continuous_absDet
  have hδ0 : ∀ g, 0 < δ g := fun g => (ideleModule E _).2
  have hδr : ∀ γ g, δ (ratGL E a γ * g) = δ g := fun γ g => by
    simp only [hδ, map_mul, GlobalTheory.ShortVecDecay.ideleModule_det_rat, one_mul]
  have hd0 : (0 : ℝ) < Module.finrank ℚ E := Nat.cast_pos.2 Module.finrank_pos
  have hL : 0 < L := mul_pos (Nat.cast_pos.2 ha) hd0
  have hTL : Real.exp 1 ^ (a * Module.finrank ℚ E) = Real.exp L := by
    rw [Real.exp_one_pow, hLdef]; push_cast; rfl
  have hδk : ∀ (k : ℕ) g, δ (e ^ k * g) = Real.exp (L * k) * δ g := fun k g => by
    have h := GlobalTheory.RSTheta.absDet_zpow_mul (E := E) (a := a) (k : ℤ) g
    rw [zpow_natCast, hTL, zpow_natCast, ← Real.exp_nat_mul, mul_comm (k : ℝ)] at h
    exact h
  have hFk : ∀ (k : ℕ) g, F (e ^ k * g) = χ ^ k * F g := by
    intro k
    induction k with
    | zero => intro g; simp
    | succ k ih => intro g; rw [pow_succ', mul_assoc, hχF, ih, pow_succ']; ring

  set f : GA E a → ℂ := fun g => F g * ((δ g : ℝ) : ℂ) ^ (s - 1) with hf
  have hfc : Continuous f := hF.mul ((Complex.continuous_ofReal.comp hδc).cpow continuous_const
    fun g => Complex.ofReal_mem_slitPlane.2 (hδ0 g))
  have hfr : ∀ γ g, f (ratGL E a γ * g) = f g := fun γ g => by
    simp only [hf, hinv, hδr]

  set S : ℕ → Set (GA E a) := fun k => {g | Real.exp (-(L * ((k : ℝ) + 1))) < δ g ∧ δ g ≤ Real.exp (-(L * k))} with hS
  have hSm : ∀ k, MeasurableSet (S k) := fun k =>
    (isOpen_lt continuous_const hδc).measurableSet.inter (isClosed_le hδc continuous_const).measurableSet

  have hSU : (⋃ k, S k) = {g | δ g ≤ 1} := by
    ext g
    simp only [hS, Set.mem_iUnion, Set.mem_setOf_eq]
    constructor
    · rintro ⟨k, -, h2⟩
      exact h2.trans (Real.exp_le_one_iff.2 (by have : (0:ℝ) ≤ k := k.cast_nonneg; nlinarith))
    · intro h
      have hl : 0 ≤ -Real.log (δ g) / L := div_nonneg (neg_nonneg.2 (Real.log_nonpos (hδ0 g).le h)) hL.le
      have h1 := Nat.lt_floor_add_one (-Real.log (δ g) / L)
      have h2 := Nat.floor_le hl
      set k := ⌊-Real.log (δ g) / L⌋₊
      refine ⟨k, ?_, ?_⟩
      ·
        rw [div_lt_iff₀ hL] at h1
        rw [← Real.exp_log (hδ0 g)]
        exact Real.exp_lt_exp.2 (by linarith)
      · rw [le_div_iff₀ hL] at h2
        rw [← Real.exp_log (hδ0 g)]
        exact Real.exp_le_exp.2 (by linarith)
  have hSd : Pairwise (Function.onFun Disjoint S) := by
    have key : ∀ j k : ℕ, j < k → Disjoint (S j) (S k) := by
      intro j k hjk
      refine Set.disjoint_left.2 fun g hj hk => ?_
      have h1 : Real.exp (-(L * k)) ≤ Real.exp (-(L * ((j : ℝ) + 1))) := by
        refine Real.exp_le_exp.2 ?_
        have : (j : ℝ) + 1 ≤ k := by exact_mod_cast hjk
        nlinarith
      exact absurd (hk.2.trans h1) (not_le.2 hj.1)
    intro j k hjk
    rcases lt_or_gt_of_ne hjk with h | h
    · exact key j k h
    · exact (key k j h).symm

  have hint : IntegrableOn f (𝓕 ∩ {g | δ g ≤ 1}) μ := by
    have h0 := (GlobalTheory.RSThetaLow.integrableOn_absDet_rpow_low E a ha μ 𝓕 h𝓕 (s.re - 1) (by linarith)).const_mul C
    refine h0.mono' hfc.aestronglyMeasurable.restrict (.of_forall fun g => ?_)
    rw [hf, norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos (hδ0 g)]
    simp only [Complex.sub_re, Complex.one_re]
    exact mul_le_mul_of_nonneg_right (hC g) (Real.rpow_nonneg (hδ0 g).le _)
  have hsum1 := hasSum_integral_iUnion (μ := μ.restrict 𝓕) (f := f) hSm hSd
    (by rw [hSU, IntegrableOn, Measure.restrict_restrict (isClosed_le hδc continuous_const).measurableSet,
      Set.inter_comm]; exact hint)
  rw [hSU, Measure.restrict_restrict (isClosed_le hδc continuous_const).measurableSet, Set.inter_comm] at hsum1

  set r : ℂ := starRingEnd ℂ χ * Complex.exp (-(((L : ℝ) : ℂ) * (s - 1))) with hr
  have hr1 : ‖r‖ < 1 := by
    have hre : (-(((L : ℝ) : ℂ) * (s - 1))).re = -(L * (s.re - 1)) := by simp
    have hpos : 0 < L * (s.re - 1) := mul_pos hL (by linarith)
    rw [hr, norm_mul, Complex.norm_conj, hχ, one_mul, Complex.norm_exp, hre]
    exact (Real.exp_lt_exp.2 (by linarith : -(L * (s.re - 1)) < 0)).trans_eq Real.exp_zero
  have hcancel : ∀ k : ℕ, r ^ k * (χ ^ k * Complex.exp (((L * k : ℝ) : ℂ) * (s - 1))) = 1 := by
    intro k
    have hc : starRingEnd ℂ χ * χ = 1 := by
      rw [mul_comm, Complex.mul_conj, Complex.normSq_eq_norm_sq, hχ]; simp
    have he1 : Complex.exp (((L * k : ℝ) : ℂ) * (s - 1)) = Complex.exp (((L : ℝ) : ℂ) * (s - 1)) ^ k := by
      rw [← Complex.exp_nat_mul]; congr 1; push_cast; ring
    rw [he1, ← mul_pow, ← mul_pow, hr]
    have : starRingEnd ℂ χ * Complex.exp (-(((L : ℝ) : ℂ) * (s - 1))) * (χ * Complex.exp (((L : ℝ) : ℂ) * (s - 1))) =
        (starRingEnd ℂ χ * χ) * (Complex.exp (-(((L : ℝ) : ℂ) * (s - 1))) * Complex.exp (((L : ℝ) : ℂ) * (s - 1))) := by ring
    rw [this, hc, ← Complex.exp_add, neg_add_cancel, Complex.exp_zero]; simp

  haveI : Countable (ratGL E a).range := by
    haveI : Countable E := (Module.finBasis ℚ E).equivFun.injective.countable
    haveI : Countable (Matrix (Fin a) (Fin a) E) := inferInstanceAs (Countable (Fin a → Fin a → E))
    haveI : Countable (GL (Fin a) E) := Units.val_injective.countable
    exact (ratGL E a).rangeRestrict_surjective.countable
  have hexp : ∀ t : ℝ, ((Real.exp t : ℝ) : ℂ) ^ (s - 1) = Complex.exp (((t : ℝ) : ℂ) * (s - 1)) := by
    intro t
    rw [Complex.cpow_def_of_ne_zero (by exact_mod_cast (Real.exp_pos t).ne'), ← Complex.ofReal_log (Real.exp_pos t).le,
      Real.log_exp]
  have hfd : ∀ k : ℕ, IsFundamentalDomain (ratGL E a).range ((fun y => (e ^ k)⁻¹ * y) ⁻¹' 𝓕) μ := by
    intro k
    refine h𝓕.preimage_of_equiv (measurePreserving_mul_left μ ((e ^ k)⁻¹)).quasiMeasurePreserving
      (e := id) Function.bijective_id fun γ x => ?_
    have hc0 : Commute e (γ : GA E a) := CuspidalL2GL.splitCentre_comm 1 _
    have hc : Commute ((e ^ k)⁻¹) (γ : GA E a) := (hc0.pow_left k).inv_left
    show (e ^ k)⁻¹ * ((γ : GA E a) * x) = (γ : GA E a) * ((e ^ k)⁻¹ * x)
    rw [← mul_assoc, hc.eq, mul_assoc]
  have hG0 : ∀ (γ : (ratGL E a).range) (x : GA E a), (S 0).indicator f (γ • x) = (S 0).indicator f x := by
    rintro ⟨_, γ, rfl⟩ x
    show (S 0).indicator f (ratGL E a γ * x) = (S 0).indicator f x
    simp only [Set.indicator_apply, hS, Set.mem_setOf_eq, hδr, hfr]
  have hshell : ∀ k : ℕ, ∫ g in S k, f g ∂(μ.restrict 𝓕) = r ^ k * ∫ g in S 0, f g ∂(μ.restrict 𝓕) := by
    intro k
    have hX : 0 < Real.exp (L * k) := Real.exp_pos _
    have hmem : ∀ g, g ∈ S k ↔ e ^ k * g ∈ S 0 := by
      intro g
      have e1 : Real.exp (L * k) * Real.exp (-(L * ((k : ℝ) + 1))) = Real.exp (-(L * (((0 : ℕ) : ℝ) + 1))) := by
        rw [← Real.exp_add]; congr 1; push_cast; ring
      have e2 : Real.exp (L * k) * Real.exp (-(L * k)) = Real.exp (-(L * ((0 : ℕ) : ℝ))) := by
        rw [← Real.exp_add]; congr 1; push_cast; ring
      show (Real.exp (-(L * ((k : ℝ) + 1))) < δ g ∧ δ g ≤ Real.exp (-(L * k))) ↔
        (Real.exp (-(L * (((0 : ℕ) : ℝ) + 1))) < δ (e ^ k * g) ∧ δ (e ^ k * g) ≤ Real.exp (-(L * ((0 : ℕ) : ℝ))))
      rw [hδk, ← e1, ← e2, mul_lt_mul_iff_of_pos_left hX, mul_le_mul_iff_of_pos_left hX]
    have hpt : ∀ g, (S k).indicator f g = r ^ k * (S 0).indicator f (e ^ k * g) := by
      intro g
      by_cases hg : g ∈ S k
      · rw [Set.indicator_of_mem hg, Set.indicator_of_mem ((hmem g).1 hg)]
        simp only [hf, hFk, hδk]
        rw [Complex.ofReal_mul, Complex.mul_cpow_ofReal_nonneg (Real.exp_pos _).le (hδ0 g).le, hexp]
        linear_combination (-(F g * ((δ g : ℝ) : ℂ) ^ (s - 1))) * hcancel k
      · rw [Set.indicator_of_notMem hg, Set.indicator_of_notMem (mt (hmem g).2 hg), mul_zero]
    have hpre : (fun x => e ^ k * x) ⁻¹' ((fun y => (e ^ k)⁻¹ * y) ⁻¹' 𝓕) = 𝓕 := by ext x; simp
    rw [← integral_indicator (hSm k), ← integral_indicator (hSm 0), integral_congr_ae (.of_forall hpt),
      integral_const_mul]
    congr 1
    calc ∫ g in 𝓕, (S 0).indicator f (e ^ k * g) ∂μ
        = ∫ g in (fun x => e ^ k * x) ⁻¹' ((fun y => (e ^ k)⁻¹ * y) ⁻¹' 𝓕), (S 0).indicator f (e ^ k * g) ∂μ := by
          rw [hpre]
      _ = ∫ y in (fun y => (e ^ k)⁻¹ * y) ⁻¹' 𝓕, (S 0).indicator f y ∂μ :=
          (measurePreserving_mul_left μ (e ^ k)).setIntegral_preimage_emb (measurableEmbedding_mulLeft _) _ _
      _ = ∫ y in 𝓕, (S 0).indicator f y ∂μ := by
          set_option synthInstance.maxHeartbeats 200000 in
            exact (hfd k).setIntegral_eq h𝓕 hG0
  have hgeo := (hasSum_geometric_of_norm_lt_one hr1).mul_right (∫ g in S 0, f g ∂(μ.restrict 𝓕))
  have hsum2 : HasSum (fun k : ℕ => ∫ g in S k, f g ∂(μ.restrict 𝓕))
      ((1 - r)⁻¹ * ∫ g in S 0, f g ∂(μ.restrict 𝓕)) := by
    rw [show (fun k : ℕ => ∫ g in S k, f g ∂(μ.restrict 𝓕)) = fun k => r ^ k * ∫ g in S 0, f g ∂(μ.restrict 𝓕) from
      funext hshell]
    exact hgeo
  have hS0 : S 0 = {g | Real.exp (-L) < δ g ∧ δ g ≤ 1} := by
    ext g; simp [hS]
  have hI0 : ∫ g in S 0, f g ∂(μ.restrict 𝓕) = ∫ g in 𝓕 ∩ {g | Real.exp (-L) < δ g ∧ δ g ≤ 1}, f g ∂μ := by
    rw [Measure.restrict_restrict (hSm 0), Set.inter_comm, hS0]
  show ∫ g in 𝓕 ∩ {g | δ g ≤ 1}, f g ∂μ = (∫ g in 𝓕 ∩ {g | Real.exp (-L) < δ g ∧ δ g ≤ 1}, f g ∂μ) / (1 - r)
  rw [← hI0, hsum1.unique hsum2, div_eq_inv_mul]

end GlobalTheory.RSThetaGeom

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsFundamentalDomainDetShellLatticeGL
section
open NumberField Matrix MeasureTheory Filter Topology GlobalTheory.CuspRep GlobalTheory.UnitaryBC GroundTheory.Global.IdeleGroup Formalism.L2.Host
open scoped nonZeroDivisors ComplexConjugate

noncomputable section

open scoped Pointwise

namespace GlobalTheory.ShellFD

theorem isFundamentalDomain_shell : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a : ℕ), 0 < a → ∀ (μ : Measure (GA E a)) [μ.IsHaarMeasure] (𝓕 : Set (GA E a)), IsFundamentalDomain (ratGL E a).range 𝓕 μ → IsFundamentalDomain (latticeGL E a) (𝓕 ∩ {g | Real.exp (-((a : ℝ) * (Module.finrank ℚ E : ℝ))) < (ideleModule E (GeneralLinearGroup.det g) : ℝ) ∧ (ideleModule E (GeneralLinearGroup.det g) : ℝ) ≤ 1}) μ := by
  intro E _ _ _ a ha μ _ 𝓕 h𝓕
  set δ : GA E a → ℝ := fun g => (ideleModule E (GeneralLinearGroup.det g) : ℝ) with hδ
  have hδc : Continuous δ := GlobalTheory.RSTheta.continuous_absDet
  have hδ0 : ∀ g, 0 < δ g := fun g => (ideleModule E _).2
  have hδr : ∀ γ g, δ (ratGL E a γ * g) = δ g := fun γ g => by
    simp only [hδ, map_mul, GlobalTheory.ShortVecDecay.ideleModule_det_rat, one_mul]
  set T : ℝ := Real.exp 1 ^ (a * Module.finrank ℚ E) with hT
  have hT1 : 1 < T := one_lt_pow₀ (Real.one_lt_exp_iff.2 one_pos) (Nat.mul_pos ha Module.finrank_pos).ne'
  have hT0 : 0 < T := one_pos.trans hT1
  have hδz : ∀ (n : ℤ) g, δ (splitCentre E a 1 ^ n * g) = T ^ n * δ g := GlobalTheory.RSTheta.absDet_zpow_mul
  have hTe : Real.exp (-((a : ℝ) * (Module.finrank ℚ E : ℝ))) = T ^ (-1 : ℤ) := by
    rw [hT, Real.exp_one_pow, _root_.zpow_neg_one, ← Real.exp_neg]
    push_cast
    rfl
  have hcomm : ∀ (n : ℤ) g, splitCentre E a 1 ^ n * g = g * splitCentre E a 1 ^ n := fun n g => by
    rw [← GlobalTheory.CuspRep.CuspidalL2GL.splitCentre_intCast]
    exact GlobalTheory.CuspRep.CuspidalL2GL.splitCentre_comm _ g
  have hTadd : ∀ m n : ℤ, T ^ m * T ^ n = T ^ (m + n) := fun m n => (zpow_add₀ hT0.ne' m n).symm
  rw [hTe]
  refine
    { nullMeasurableSet := h𝓕.nullMeasurableSet.inter
        ((measurableSet_lt measurable_const hδc.measurable).inter
          (measurableSet_le hδc.measurable measurable_const)).nullMeasurableSet
      ae_covers := ?_
      aedisjoint := ?_ }
  · have hN := ae_iff.1 h𝓕.ae_covers
    have hB : μ (⋃ n : ℤ, (fun x => splitCentre E a 1 ^ n * x) ⁻¹'
        {x | ¬∃ γ : (ratGL E a).range, γ • x ∈ 𝓕}) = 0 :=
      measure_iUnion_null fun n => (measurePreserving_mul_left μ _).quasiMeasurePreserving.preimage_null hN
    refine Filter.mem_of_superset (compl_mem_ae_iff.2 hB) fun x hx => ?_
    simp only [Set.mem_compl_iff, Set.mem_iUnion, Set.mem_preimage, Set.mem_setOf_eq, not_exists, not_not] at hx
    obtain ⟨m, hm1, hm2⟩ := exists_mem_Ioc_zpow (hδ0 x) hT1
    obtain ⟨γ, hγ⟩ := not_forall_not.1 (hx (-(m + 1)))
    obtain ⟨γ0, hγ0⟩ := γ.2
    refine ⟨⟨(γ : GA E a) * splitCentre E a 1 ^ (-(m + 1)),
      mul_mem (Subgroup.mem_sup_left γ.2) (GlobalTheory.CuspRep.CuspidalL2GL.zpow_mem_latticeGL _)⟩, ?_, ?_, ?_⟩
    · rw [Subgroup.smul_def]
      simpa only [Subgroup.smul_def, smul_eq_mul, mul_assoc] using hγ
    · rw [Subgroup.smul_def]
      change T ^ (-1 : ℤ) < δ ((γ : GA E a) * splitCentre E a 1 ^ (-(m + 1)) * x)
      rw [mul_assoc, ← hγ0, hδr, hδz]
      calc T ^ (-1 : ℤ) = T ^ (-(m + 1)) * T ^ m := by rw [hTadd]; ring_nf
        _ < T ^ (-(m + 1)) * δ x := mul_lt_mul_of_pos_left hm1 (zpow_pos hT0 _)
    · rw [Subgroup.smul_def]
      change δ ((γ : GA E a) * splitCentre E a 1 ^ (-(m + 1)) * x) ≤ 1
      rw [mul_assoc, ← hγ0, hδr, hδz]
      calc T ^ (-(m + 1)) * δ x ≤ T ^ (-(m + 1)) * T ^ (m + 1) := mul_le_mul_of_nonneg_left hm2 (zpow_pos hT0 _).le
        _ = 1 := by rw [hTadd]; simp
  · intro g1 g2 hne
    have key : ∀ (g : latticeGL E a) (γ : GL (Fin a) E) (n : ℤ),
        ratGL E a γ * splitCentre E a 1 ^ n = g → ∀ y ∈ g • (𝓕 ∩ {g | T ^ (-1 : ℤ) < δ g ∧ δ g ≤ 1}),
        T ^ (n - 1) < δ y ∧ δ y ≤ T ^ n ∧
          y ∈ splitCentre E a 1 ^ n • ((⟨ratGL E a γ, γ, rfl⟩ : (ratGL E a).range) • 𝓕) := by
      rintro g γ n hg y ⟨x, ⟨hx, hx1, hx2⟩, rfl⟩
      have hy : g • x = splitCentre E a 1 ^ n * (ratGL E a γ * x) := by
        rw [Subgroup.smul_def, smul_eq_mul, ← hg, hcomm n (ratGL E a γ * x)]
        simp only [mul_assoc, hcomm n x]
      beta_reduce
      rw [hy]
      refine ⟨?_, ?_, Set.smul_mem_smul_set (Set.smul_mem_smul_set hx)⟩
      · rw [hδz, hδr]
        calc T ^ (n - 1) = T ^ n * T ^ (-1 : ℤ) := by rw [hTadd]; ring_nf
          _ < T ^ n * δ x := mul_lt_mul_of_pos_left hx1 (zpow_pos hT0 _)
      · rw [hδz, hδr]
        calc T ^ n * δ x ≤ T ^ n * 1 := mul_le_mul_of_nonneg_left hx2 (zpow_pos hT0 _).le
          _ = T ^ n := mul_one _
    obtain ⟨γ1, n1, h1⟩ := GlobalTheory.CuspRep.CuspidalL2GL.mem_latticeGL_iff.1 g1.2
    obtain ⟨γ2, n2, h2⟩ := GlobalTheory.CuspRep.CuspidalL2GL.mem_latticeGL_iff.1 g2.2
    by_cases hn : n1 = n2
    · subst hn
      have hγ : (⟨ratGL E a γ1, γ1, rfl⟩ : (ratGL E a).range) ≠ ⟨ratGL E a γ2, γ2, rfl⟩ := fun h => hne <|
        Subtype.ext (by rw [← h1, ← h2, show ratGL E a γ1 = ratGL E a γ2 from congrArg Subtype.val h])
      have hd : AEDisjoint μ (splitCentre E a 1 ^ n1 • ((⟨ratGL E a γ1, γ1, rfl⟩ : (ratGL E a).range) • 𝓕))
          (splitCentre E a 1 ^ n1 • ((⟨ratGL E a γ2, γ2, rfl⟩ : (ratGL E a).range) • 𝓕)) := by
        set_option synthInstance.maxHeartbeats 200000 in
          rw [AEDisjoint, ← Set.smul_set_inter, measure_smul]
        exact h𝓕.aedisjoint hγ
      exact hd.mono (fun y hy => (key g1 γ1 n1 h1 y hy).2.2) (fun y hy => (key g2 γ2 n1 h2 y hy).2.2)
    · refine Disjoint.aedisjoint (Set.disjoint_left.2 fun y hy1 hy2 => ?_)
      obtain ⟨a1, b1, -⟩ := key g1 γ1 n1 h1 y hy1
      obtain ⟨a2, b2, -⟩ := key g2 γ2 n2 h2 y hy2
      rcases lt_or_gt_of_ne hn with h | h
      · exact absurd a2 (not_lt.2 (b1.trans (zpow_le_zpow_right₀ hT1.le (by omega : n1 ≤ n2 - 1))))
      · exact absurd a1 (not_lt.2 (b2.trans (zpow_le_zpow_right₀ hT1.le (by omega : n2 ≤ n1 - 1))))

end GlobalTheory.ShellFD
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsMirabolicWhittakerStageMulInvariantContinuousStatement
section
open NumberField IsDedekindDomain MeasureTheory GlobalTheory.CuspRep GlobalTheory.JSW Formalism.UG GlobalTheory.LFun Formalism.L2.Host
open scoped ENNReal ComplexConjugate ContDiff
open GlobalTheory.MirTower GlobalTheory.CuspGeneric
open GroundTheory.Automorphic.FourierWhittaker (partialCoeff blockGL uGL)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isMirabolicWhittakerStage_mul_invariant_continuous : ∀ (E : Type) [Field E] [NumberField E] (a m : ℕ) (ψ : AddChar (Ad E) ℂ) (f c : GA E a → ℂ),
    Good ψ m f → Continuous c → (∀ γ : GL (Fin a) E, IsMir m γ → ∀ g, c (ratGL E a γ * g) = c g) →
    (∀ (r l : ℕ) (y : UnipotentBlockColumnIndex a r l → Ad E) (g : GA E a), c (blkU y * g) = c g) → Good ψ m (fun g => c g * f g) := by
  first | (exact @GlobalTheory.GoodMul.good_mul_invariant) | (exact GlobalTheory.GoodMul.good_mul_invariant) | (intros; apply GlobalTheory.GoodMul.good_mul_invariant  <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ThetaSeriesTypeUnderSupportedLiftsStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links IsDedekindDomain NumberField Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.ExportSeries GlobalTheory.SeriesTie GlobalTheory.TwInputs GlobalTheory.TwSys GlobalTheory.TwAll GlobalTheory.SupLaw GlobalTheory.LiftLeaf
open Formalism.MainNotions.IntegralHeckeForms (TwOK ClsQ HkIdx V0 Fm0 FullRk SgJ BasisOf)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.thetaSeries_type_under_supported_lifts : ∀ (D : D7) (S T : HSp D) (B : Base S T), B.Good → S.SigOK → ∀ ω : PairRep S T, B.IsWeil 1 ω → ∀ (u : G0 B.G.Pg T.rank) (hu : u ∈ B.G.P.H), ∃ κ : GA D T, Lev.IsLevelLift T B.F.βT B.G.levT u κ ∧ SuppAt (idem B.G.Pg) T κ ∧ ∀ (Q : Finset (Pl D.host.E)), B.admitted Q → ∀ (φ : ∀ PP : ↥Q, Matrix (Fin T.rank) (Fin S.rank) (kP PP.1) → ℂ) (h : GA D S) (P : PolF D T.rank S.rank) (g : GA D T), series B.F ω (B.vecAt Q φ) h P (g * κ) = ((B.G.P.chi ⟨u, hu⟩ : ℂˣ) : ℂ) * series B.F ω (B.vecAt Q φ) h P g := by
  first | exact @GlobalTheory.TypeSupportLift.series_type_supp | exact GlobalTheory.TypeSupportLift.series_type_supp | (intros; apply GlobalTheory.TypeSupportLift.series_type_supp <;> assumption)
end

