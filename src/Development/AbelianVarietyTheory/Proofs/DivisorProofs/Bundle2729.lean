module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.TwistedPlaceChoiceLiesOverPair
public import Development.AbelianVarietyTheory.Counterexamples.RotationExamples.LeafIPOfTwoConstants
public import Formalism.LocalToGlobal.Divisibility.EigenvalueSumLeClosedOf
public import Development.AutomorphicArithmetic.CyclotomicBounds.RamifiedDiscriminants.Bundle0001
public import Development.AutomorphicArithmetic.CyclotomicBounds.RamifiedDiscriminants.Bundle0004
public import Development.AbelianVarietyTheory.Definitions.Divisors.OfFactorE
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
public import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissibleBaseOfCompleteDvr
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2710
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2700
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0066
public import Development.AbelianVarietyTheory.Definitions.Uniformization.Bundle0002
public import Development.AbelianVarietyTheory.Definitions.Divisors.DensConst
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0039
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsAmbOfIsArithVar
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0004
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2390
public import ReciprocityTheory.AnalyticForms.PotentialTheory.Bundle0003
public import ReciprocityTheory.AnalyticForms.PotentialTheory.Bundle0005
public import ReciprocityTheory.AnalyticForms.PotentialTheory.Bundle0006
public import ReciprocityTheory.AnalyticForms.PotentialTheory.Bundle0007
public import ReciprocityTheory.AnalyticForms.PotentialTheory.Bundle0008
public import ReciprocityTheory.AnalyticForms.PotentialTheory.Stokes
public import ReciprocityTheory.AnalyticForms.PotentialTheory.SNCAtlas
public import ReciprocityTheory.AnalyticForms.PotentialTheory.Bundle0002
public import ReciprocityTheory.AnalyticForms.PlurisubharmonicFunctions.Bundle0001
public import ReciprocityTheory.AnalyticForms.PotentialTheory.PLCurveA
public import ReciprocityTheory.AnalyticForms.PotentialTheory.PLLocalStatement
public import ReciprocityTheory.AnalyticForms.PotentialTheory.Pullback
public import ReciprocityTheory.AnalyticForms.PotentialTheory.AtlasIndep
public import ReciprocityTheory.AnalyticForms.PotentialTheory.DegreeInt
public import ReciprocityTheory.AnalyticForms.PotentialTheory.ContDiffFubiniStudyRatioCompChart0
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2557
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2550
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2521
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2497
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2699
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsDimEqOne
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2678
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2632
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.WeightExceedsCenterBound
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0617
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0403
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0433
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0015
public import Development.AbelianVarietyTheory.Definitions.Divisors.FormalCoboundarySmul
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2178
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinrankLeFrobeniusKernelMulSpanPrimePowers
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2691
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2653
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0537
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2305

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LambdaLowGivesFirstIdentity
section
open Formalism.BasicNotions Formalism.MainNotions NumberField Formalism.L2.Indef Formalism.L2.Indef.Tree GlobalTheory.BigTop GlobalTheory.BigTop.Fun

noncomputable section

namespace GlobalTheory.BigTop.Fun.IPbProof

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem one_le_b {D : D7} (L : SizeData₂ D) : 1 ≤ L.sc.b := by
  have hx := L.sc.one_lt_alt
  have h0 : 0 ≤ L.sc.L := Real.rpow_nonneg (by linarith) _
  unfold Scale.b
  exact Real.one_le_exp h0

theorem La_le_three {D : D7} (L : SizeData₂ D) (hS : SizesAt L) : L.La ≤ 3 * L.sc.L := by
  obtain ⟨hN, -, -, -, hT, hC, hQ, -⟩ := hS
  obtain ⟨-, -, -, -, -, -, hr1, hr2⟩ := hQ
  have hx := L.sc.one_lt_alt
  have hn : (1 : ℝ) ≤ (D.R.n : ℝ) := by
    have : 1 ≤ D.R.n := D.R.n_pos'
    exact_mod_cast this
  have hq : (1 : ℝ) ≤ (D.host.q : ℝ) := by exact_mod_cast D.host.hyp.1.one_le
  have hd : (1 : ℝ) ≤ (D.host.d : ℝ) := by exact_mod_cast D.host.hyp.2.1.one_le
  have hqd : (1 : ℝ) ≤ (D.host.q : ℝ) * D.host.d := by nlinarith
  have hb := one_le_b L
  have hnc : (D.R.n : ℝ) ≤ szCond L := by
    have h := D.host.four_ord_le_condN
    have h' : D.R.n ≤ D.host.QS * D.host.q * D.host.d := by rw [D.R.n_eq_ord]; omega
    unfold szCond; exact_mod_cast h'
  have hc1 : 1 ≤ szCond L := hn.trans hnc
  have hcb : szCond L ≤ L.sc.b := by
    have h1 : szCond L ≤ szCond L ^ 36 := le_self_pow₀ hc1 (by norm_num)
    have h2 : (1 : ℝ) ≤ (D.R.t : ℝ) ^ 150 := one_le_pow₀ hT.1
    have h3 : Real.sqrt L.sc.b ≤ L.sc.b := Real.sqrt_le_iff.2 ⟨by linarith, by nlinarith⟩
    have h4 : szCond L ^ 36 ≤ szCond L ^ 36 * (D.R.t : ℝ) ^ 150 := le_mul_of_one_le_right (by positivity) h2
    have h5 : szCond L ^ 36 * (D.R.t : ℝ) ^ 150 ≤ Real.sqrt L.sc.b := hC
    linarith
  have hxn : L.sc.x ≤ (D.R.n : ℝ) := by
    refine le_trans ?_ hN.1
    have he := L.sc.eps_pos
    calc L.sc.x = L.sc.x ^ (1 : ℝ) := (Real.rpow_one _).symm
      _ ≤ _ := Real.rpow_le_rpow_of_exponent_le hx.le (by unfold szTh; linarith)
  have hs : Real.sqrt ((D.host.q : ℝ) * D.host.d) ≤ (D.host.q : ℝ) * D.host.d :=
    Real.sqrt_le_iff.2 ⟨by linarith, by nlinarith⟩
  have hxb : L.sc.x ≤ L.sc.b := (hxn.trans hnc).trans hcb
  have hrb : D.host.rdE ≤ L.sc.b := (UpperTheory.Ram.Rd.rdE_le_cond D.host).trans hcb
  have hlb : Real.log L.sc.b = L.sc.L := Real.log_exp _
  have l1 := Real.log_le_log (by linarith) hxb
  have l2 := Real.log_le_log (by linarith) hrb
  have hx0 : 0 < L.sc.x := by linarith
  have hr0 : 0 < D.host.rdE := by linarith
  have e : L.La = Real.log L.sc.x + L.sc.L + Real.log D.host.rdE := by
    unfold SizeData₂.La Scale.a Scale.b
    rw [Real.log_mul (by positivity) hr0.ne', Real.log_mul hx0.ne' (Real.exp_pos _).ne', Real.log_exp]
  rw [e]
  linarith

end GlobalTheory.BigTop.Fun.IPbProof

namespace GlobalTheory.BigTop.Fun

open GlobalTheory.BigTop.Fun.IPbProof

end GlobalTheory.BigTop.Fun

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LinearUniformisationRosatiAdjointStar
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.TChart GlobalTheory.Mum

noncomputable section

namespace GlobalTheory.Mum.OLinRosati

variable {R : Type} [CommRing R] [IsDomain R] {I : Ideal R}


omit [IsDomain R] in
theorem thickMap_pullback_map {G : Over (Sp R)} (b : G ⟶ G) (e : ℕ) :
    thickMap R I e G ≫ ((Over.pullback (thick R I (e + 1))).map b).left =
      ((Over.pullback (thick R I e)).map b).left ≫ thickMap R I e G := by
  apply pullback.hom_ext <;>
    simp [thickMap, pullback.map, pullback.lift_fst, pullback.lift_snd, pullback.lift_fst_assoc,
      pullback.lift_snd_assoc]

theorem linEnd_act {D : DegData R I} {O : Type} [Ring O] [StarRing O] [Module O D.toPre.X] {o : D.toPre.OAct O}
    {A : PolAV (Sp (FractionRing R))} {G : Over (Sp R)} [GrpObj G] [IsCommMonObj G] {U : UnifPre I D A G}
    {oA : A.OAct O} {oG : RingAct G O} (h : U.OLinear O o oA oG) (a : O) :
    LinEnd U (o.onB.act a) (DistribSMul.toAddMonoidHom D.toPre.X (star a)) (oG.act a) := by
  haveI := oG.hom a
  refine ⟨oG.hom a, fun e => inferInstance, fun e => thickMap_pullback_map _ e, fun e => h.q_lin e a, fun e => ?_⟩
  exact h.i_lin e a

theorem endData_act {D : DegPre R} {O : Type} [Ring O] [StarRing O] [Module O D.X] (o : D.OAct O) (a : O) :
    EndData D (o.onB.act a) (o.onB.act (star a)) (DistribSMul.toAddMonoidHom D.X a)
      (DistribSMul.toAddMonoidHom D.X (star a)) :=
  ⟨o.onB.hom a, o.onB.hom (star a), o.onB.rosati a, o.c_lin a, o.c_lin (star a), o.tau_bal a⟩

theorem main : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], IsCN R → ∀ (D : DegData R (maximalIdeal R)) (O : Type) [Ring O] [StarRing O] [Module O D.toPre.X] (o : D.toPre.OAct O) (A : PolAV (Sp (FractionRing R))) (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G] (U : Unif (maximalIdeal R) D A G) (oA : A.OAct O) (oG : RingAct G O), IsSemiAbelian G → U.toUnifPre.OLinear O o oA oG → ∀ a : O, LBIso (cubeLB G ![fst G G ≫ oG.act a, snd G G] U.LG.L) (cubeLB G ![fst G G, snd G G ≫ oG.act (star a)] U.LG.L) := by
  intro R _ _ _ hR D O _ _ _ o A G _ _ U oA oG hG hlin a
  have hB : Base R := ⟨⟨hR.1, inferInstance, hR.2.1, hR.2.2.1⟩, hR.2.2.2⟩
  have h₁ := linEnd_act hlin a
  have h₂ := linEnd_act hlin (star a)
  rw [star_star] at h₂
  exact linEnd_adjoint_lbIso R hB D A G hG U _ _ _ _ (endData_act o a) _ _ h₁ h₂

end GlobalTheory.Mum.OLinRosati
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MatrixActsOnTorsionLabelsStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH
open scoped CategoryTheory.Obj
open GlobalTheory.Poinc GlobalTheory.Poinc.Eq8 Formalism.L2.Pj
open scoped TensorProduct
attribute [local instance] Over.cartesianMonoidalCategory
open Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.matrix_acts_on_torsion_labels_alt : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], GlobalTheory.Mum.Base R → IsDiscreteValuationRing R → ∀ (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ (D : DegData R (maximalIdeal R)) (A : PolAV (Sp (FractionRing R))) (U : Unif (maximalIdeal R) D A G) (G' : Over (Sp R)) [GrpObj G'] [IsCommMonObj G'], IsSemiAbelian G' → ∀ (D' : DegData R (maximalIdeal R)) (A' : PolAV (Sp (FractionRing R))) (U' : Unif (maximalIdeal R) D' A' G') (W : Matrix (Fin 8) (Fin 8) ℤ), IsE8 W → ∀ (pr : Fin 8 → (A'.A ⟶ A.A)), (∀ a, IsMonHom (pr a)) → (∀ (T' : Over (Sp (FractionRing R))) (y : Fin 8 → (T' ⟶ A.A)), ∃! z : T' ⟶ A'.A, ∀ a, z ≫ pr a = y a) → LBIso A'.L (LB.LinComb (abelian₂ A.A A.L) (K := Fin 8 × Fin 8) (fun ab => (lift (pr ab.1) (pr ab.2)).left) (fun ab => W ab.1 ab.2)) → ∀ (pG : Fin 8 → (G' ⟶ G)), (∀ v, IsMonHom (pG v)) → (∀ v, (Over.pullback (jK R)).map (pG v) ≫ U.gen.hom = U'.gen.hom ≫ pr v) → ∀ (c : Fin 8 → (D.toPre.X →+ D'.toPre.X)), (∀ v, TorMatch U U' (RingHom.id R) (pG v).left (c v)) → ∀ e : D'.toPre.X ≃+ (Fin 8 → D.toPre.X), (∀ y, ∑ v, c v (∑ u, (W + W.transpose) v u • e y u) = y) → ∀ (a : Matrix (Fin 8) (Fin 8) ℤ) (f : A'.A ⟶ A'.A), (∀ u, f ≫ pr u = (List.ofFn fun v => pr v ^ a u v).prod) → ∀ (K : Type) [Field K] [IsAlgClosed K] [Algebra (FractionRing R) K] (m : ℕ) (pk pk' : QkPt D'.toPre K m) (x : TFK (R := R) K ⟶ A'.A), 1 ≤ m → QkToAkU U'.toUnifPre K m pk x → QkToAkU U'.toUnifPre K m pk' (x ≫ f) → CongMod m (e pk'.y) (fun u => ∑ v, a u v • e pk.y v) := by
  first | exact @GlobalTheory.Poinc.Eq8.MatTors.matrix_acts_on_torsion_labels | exact GlobalTheory.Poinc.Eq8.MatTors.matrix_acts_on_torsion_labels | (intros; apply GlobalTheory.Poinc.Eq8.MatTors.matrix_acts_on_torsion_labels <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MixedChernFormFiniteIntegrablePointClosure
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Set Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.R
open GlobalTheory GlobalTheory.Cartier GlobalTheory.CxPts GlobalTheory.Points GlobalTheory.CechPic GlobalTheory.ChartGlue GlobalTheory.Mix

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.CycFin

theorem cycle_facts : GlobalTheory.Published.Principalisation → ∀ (F : Type) [Field F] (X : Scheme.{0}) (p : X ⟶ Sp F) (σ : F →+* ℂ), IsProjOver p → ∀ (e : ℕ) (L : Fin e → MLine p σ) (z : X), topologicalKrullDim (closure ({z} : Set X)) = e → (∀ ε : ℤˣ, IsFiniteMeasure (part (fun i => (L i).pull (closι z) rfl) ε)) ∧ (∀ f : CxPts p σ → ℝ, Continuous f → CycIntg L f z) ∧ (∀ (U : X.Opens), z ∈ U → ∀ ε : ℤˣ, part (fun i => (L i).pull (closι z) rfl) ε (ptMap (closι z) rfl σ ⁻¹' ptsIn p σ U)ᶜ = 0) ∧ ∀ (M : MLine p σ) (s : M.B.Sec), z ∈ nonzeroLocus s → CycIntg L (M.logSec s) z := by
  intro hP F _ X p σ hp e L z hdim
  obtain ⟨hint, hgen, hdimeq, -⟩ := _root_.GlobalTheory.ClosFacts.clos_facts X z
  haveI := hint
  have hp' : IsProjOver (closι z ≫ p) := by
    obtain ⟨N, φ, hφ, rfl⟩ := hp
    exact ⟨N, closι z ≫ φ, inferInstance, Category.assoc _ _ _⟩
  haveI : IsLocallyNoetherian (clos z) := by
    obtain ⟨N, ι, _, -⟩ := hp'
    exact LocallyOfFiniteType.isLocallyNoetherian (ι ≫ PSpace.str F N)
  have hd : topologicalKrullDim (clos z) = ((e : ℕ) : WithBot ℕ∞) := hdimeq.trans hdim
  have H1 := _root_.GlobalTheory.MixFin.finite_and_intg hP F (clos z) (closι z ≫ p) σ e hp' hd (fun i => (L i).pull (closι z) rfl)
  have hpre : ∀ U : X.Opens, ptMap (closι z) rfl σ ⁻¹' ptsIn p σ U = ptsIn (closι z ≫ p) σ (closι z ⁻¹ᵁ U) := by
    intro U
    ext y
    simp only [Set.mem_preimage, mem_ptsIn]
    rfl
  refine ⟨H1.1, fun f hf => H1.2 _ (hf.comp (PtsOver.continuous_map _ _ _)), ?_, ?_⟩
  · intro U hU ε
    have hgU : genericPoint (clos z) ∈ closι z ⁻¹ᵁ U := by
      show closι z (genericPoint (clos z)) ∈ U
      rw [hgen]; exact hU
    rw [hpre U]
    exact _root_.GlobalTheory.MixNull.part_compl_null F (clos z) (closι z ≫ p) σ σ.injective hp' e _ ε _ hgU
  · intro M s hs
    obtain ⟨s', hnz, hnsq, -⟩ := _root_.GlobalTheory.Mix.exists_secPull_props F X (clos z) p (closι z ≫ p) σ (closι z) rfl M s
    have hgs : genericPoint (clos z) ∈ nonzeroLocus s' := by
      rw [hnz]
      show closι z (genericPoint (clos z)) ∈ nonzeroLocus s
      rw [hgen]; exact hs
    have H := _root_.GlobalTheory.Mix.logSec_intg_proj hP F (clos z) (closι z ≫ p) σ e hp' hd (fun i => (L i).pull (closι z) rfl)
      (M.pull (closι z) rfl) s' hgs
    have he : (M.pull (closι z) rfl).logSec s' = fun y => M.logSec s (ptMap (closι z) rfl σ y) := by
      funext y
      simp only [MLine.logSec, hnsq]
    unfold CycIntg
    rw [← he]
    exact H

end GlobalTheory.CycFin
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MixedChernIntegralAddOfDensityAdd
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Set Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.R
open GlobalTheory GlobalTheory.Cartier GlobalTheory.CxPts GlobalTheory.Points GlobalTheory.CechPic GlobalTheory.ChartGlue GlobalTheory.Mix

theorem GlobalTheory.Mix.part_le_add_of_dens_add {k : Type} [CommRing k] {X : Scheme.{0}} {p : X ⟶ Sp k} {σ : k →+* ℂ} {D : ℕ}
    (L₁ L₂ L₃ : Fin D → MLine p σ)
    (h : ∀ c : AlgChart p σ D, ∀ y ∈ c.e.source, dens L₁ c y = dens L₂ c y + dens L₃ c y) (ε : ℤˣ) :
    part L₁ ε ≤ part L₂ ε + part L₃ ε := by
  unfold part glueMeas
  refine iSup_le fun c => ?_
  refine le_trans ?_ (add_le_add
    (le_iSup (fun c : AlgChart p σ D => chartMeas c.e fun y => ENNReal.ofReal ((ε : ℤ) * dens L₂ c y)) c)
    (le_iSup (fun c : AlgChart p σ D => chartMeas c.e fun y => ENNReal.ofReal ((ε : ℤ) * dens L₃ c y)) c))
  refine Measure.le_iff.2 fun A hA => ?_
  have hB : MeasurableSet (c.e.source ∩ A) := c.e.open_source.measurableSet.inter hA
  have hI := GlobalTheory.ChartGlue.measurableSet_image c.e hB inter_subset_left
  have hsub : c.e '' (c.e.source ∩ A) ⊆ c.e.target := fun _ ⟨y, hy, e⟩ => e ▸ c.e.map_source hy.1
  have hcont : ContinuousOn (fun v => dens L₂ c (c.e.symm v)) c.e.target :=
    (_root_.GlobalTheory.Mix.continuousOn_dens k X p σ D L₂ c).comp c.e.continuousOn_symm c.e.mapsTo_symm
  have hm : AEMeasurable (fun v => ENNReal.ofReal (((ε : ℤ) : ℝ) * dens L₂ c (c.e.symm v)))
      (volume.restrict (c.e '' (c.e.source ∩ A))) :=
    (((hcont.aemeasurable c.e.open_target.measurableSet).const_mul _).ennreal_ofReal).mono_measure
      (Measure.restrict_mono hsub le_rfl)
  rw [Measure.add_apply, chartMeas_apply _ _ hA, chartMeas_apply _ _ hA, chartMeas_apply _ _ hA,
    ← lintegral_add_left' hm]
  refine setLIntegral_mono' hI fun v hv => ?_
  beta_reduce
  rw [h c _ (c.e.map_target (hsub hv)), mul_add]
  exact ENNReal.ofReal_add_le

theorem GlobalTheory.Mix.int_add_of_dens_add : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) (p : X ⟶ Sp k) (σ : k →+* ℂ) [SecondCountableTopology (CxPts p σ)] (D : ℕ) (L₁ L₂ L₃ : Fin D → MLine p σ), (∀ c : AlgChart p σ D, ∀ y ∈ c.e.source, dens L₁ c y = dens L₂ c y + dens L₃ c y) → ∀ f : CxPts p σ → ℝ, (Intg L₂ f → Intg L₃ f → Intg L₁ f) ∧ (Intg L₁ f → Intg L₂ f → Intg L₃ f → Mix.int L₁ f = Mix.int L₂ f + Mix.int L₃ f) := by
  intro k _ X p σ _ D L₁ L₂ L₃ h f
  refine ⟨fun h₂ h₃ => ⟨(h₂.1.add_measure h₃.1).mono_measure (GlobalTheory.Mix.part_le_add_of_dens_add L₁ L₂ L₃ h 1),
    (h₂.2.add_measure h₃.2).mono_measure (GlobalTheory.Mix.part_le_add_of_dens_add L₁ L₂ L₃ h (-1))⟩, fun h₁ h₂ h₃ => ?_⟩
  have := _root_.GlobalTheory.Mix.sum_int_eq_zero_of_dens k X p σ D (Fin 3) ![1, -1, -1] ![L₁, L₂, L₃]
    (fun c y hy => by
      rw [Fin.sum_univ_three]
      show 1 * dens L₁ c y + -1 * dens L₂ c y + -1 * dens L₃ c y = 0
      rw [h c y hy]; ring) f
    (fun i => by
      fin_cases i
      · exact h₁
      · exact h₂
      · exact h₃)
  rw [Fin.sum_univ_three] at this
  change 1 * Mix.int L₁ f + -1 * Mix.int L₂ f + -1 * Mix.int L₃ f = 0 at this
  linarith
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MumfordClassSymmetricPullbackQuadratic
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.HTLat GlobalTheory.Published.AbVarRed GlobalTheory.CechPic GlobalTheory.AV GlobalTheory.AV.AbVar
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.AV.AbVar

theorem pull_zsmul_of_symm : ∀ (K : Type) [Field K] (B A : AbVar K) (c : Pic A.X.left), CechPic.pull (Hom.hom (-(𝟙 A))).left c = c → ∀ (f : B ⟶ A) (n : ℤ), AbVar.lam c f.hom f.hom = 2 • CechPic.pull f.hom.left c ∧ CechPic.pull (Hom.hom (n • f)).left c = (n ^ 2) • CechPic.pull f.hom.left c := by
  intro K _ B A c hc f n
  have bil := GlobalTheory.T.abelianVarietyMumfordClass_bilinear K A c B.X

  have h1 : CechPic.pull (1 : B.X ⟶ A.X).left c = 0 := by
    have e := (bil 1 1 1 0).2.1
    simp only [AbVar.lam, _root_.mul_one, sub_self, zero_sub, neg_eq_zero] at e
    exact e

  have hinv : ∀ y : B.X ⟶ A.X, CechPic.pull (y⁻¹).left c = CechPic.pull y.left c := by
    intro y
    have hc' : CechPic.pull ((𝟙 A.X)⁻¹).left c = c := hc
    rw [show y⁻¹ = y ≫ (𝟙 A.X)⁻¹ by rw [GrpObj.comp_inv, Category.comp_id], Over.comp_left, pull_comp, hc']

  have hmul : ∀ y z : B.X ⟶ A.X, CechPic.pull (y * z).left c =
      AbVar.lam c y z + CechPic.pull y.left c + CechPic.pull z.left c := by
    intro y z
    simp only [AbVar.lam]
    abel
  set x := f.hom with hx
  have key : AbVar.lam c x x = 2 • CechPic.pull x.left c := by
    have e := (bil x x 1 (-1)).2.2.2.2
    rw [zpow_neg_one] at e
    have e2 := hmul x x⁻¹
    rw [_root_.mul_inv_cancel, h1, hinv, e] at e2
    have e3 : AbVar.lam c x x - 2 • CechPic.pull x.left c =
        -((-1 : ℤ) • AbVar.lam c x x + CechPic.pull x.left c + CechPic.pull x.left c) := by module
    rw [← sub_eq_zero, e3, ← e2, neg_zero]
  refine ⟨key, ?_⟩
  have step : ∀ m : ℤ, CechPic.pull (x ^ (m + 1)).left c =
      CechPic.pull (x ^ m).left c + (2 * m + 1) • CechPic.pull x.left c := by
    intro m
    rw [zpow_add_one, hmul, (bil x x 1 m).2.2.2.1, key]
    module
  change CechPic.pull (x ^ n).left c = (n ^ 2) • CechPic.pull x.left c
  induction n using Int.induction_on with
  | zero => rw [zpow_zero, h1]; simp
  | succ m ih =>
    rw [step, ih]
    module
  | pred m ih =>
    have e := step (-(m : ℤ) - 1)
    rw [show -(m : ℤ) - 1 + 1 = -(m : ℤ) by ring, ih] at e
    rw [eq_sub_of_add_eq e.symm]
    module

end GlobalTheory.AV.AbVar
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.NFunAddOneLtEExpAddCen
section
noncomputable section

open Formalism.BasicNotions Formalism.MainNotions NumberField IsDedekindDomain Formalism.FrobeniusOrbits
open Formalism.L2 Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Indef.Tree Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Cx
open GlobalTheory.ChiGrid Formalism.L2.Host

namespace GlobalTheory.BigTop.Fun

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} {T : Type} {Lc : LevCh D T} {sc : Consts}

theorem natCast_mem_of_under {w : HeightOneSpectrum (𝓞 D.host.E)} {p : ℕ}
    (h : ((p : ℕ) : 𝓞 D.host.F) ∈ (w.under (𝓞 D.host.F)).asIdeal) : ((p : ℕ) : 𝓞 D.host.E) ∈ w.asIdeal := by
  have h1 : algebraMap (𝓞 D.host.F) (𝓞 D.host.E) (p : 𝓞 D.host.F) ∈ w.asIdeal := h
  rwa [map_natCast] at h1

theorem natCast_mem_under {w : HeightOneSpectrum (𝓞 D.host.E)} {p : ℕ}
    (h : ((p : ℕ) : 𝓞 D.host.E) ∈ w.asIdeal) : ((p : ℕ) : 𝓞 D.host.F) ∈ (w.under (𝓞 D.host.F)).asIdeal := by
  show algebraMap (𝓞 D.host.F) (𝓞 D.host.E) (p : 𝓞 D.host.F) ∈ w.asIdeal
  rwa [map_natCast]

theorem nFun_add_one_lt_eExp_add_cen (C : ℝ) (j a : Fin D.R.m) (g : D.R.Psi) :
    (BlochKatoReduction.Gen.NFun D.R : ℚ) + 1 < eExp D j g + (cen D C (D.eTau.symm g) (a.1 + 1) : ℚ) := by
  have h1 := GlobalTheory.LamTie.e_add_v_two_pos (D.hc (D.eTau.symm g)) (sLen D) (gap D C) 0 j
  have h2 := Int.lt_floor_add_one
    ((GlobalTheory.SignedHC.GridData.ofHCParam (D.hc (D.eTau.symm g)) (sLen D) (gap D C) 0).mid (a.1 + 1))
  have h3 := (GlobalTheory.SignedHC.GridData.ofHCParam (D.hc (D.eTau.symm g)) (sLen D) (gap D C) 0).mid_eq (i := a.1 + 1) (by omega)
  have h4 : (GlobalTheory.SignedHC.GridData.ofHCParam (D.hc (D.eTau.symm g)) (sLen D) (gap D C) 0).a (a.1 + 1) =
      ((GlobalTheory.SignedHC.GridData.ofHCParam (D.hc (D.eTau.symm g)) (sLen D) (gap D C) 0).v 2 : ℚ) + 1 / 2 +
        ((D.R.m : ℚ) + 1 - ((a.1 + 1 : ℕ) : ℚ)) * (gap D C : ℚ) := rfl
  have h5 : ((GlobalTheory.SignedHC.GridData.ofHCParam (D.hc (D.eTau.symm g)) (sLen D) (gap D C) 0).ga : ℚ) = gap D C := rfl
  have h6 := (isLeast_gap D C).1.2.1
  have h7 : bigN D ≤ bigN D ^ 3 := Nat.le_self_pow (by norm_num) _
  have h8 : ((bigN D + 2 : ℕ) : ℚ) ≤ gap D C := by exact_mod_cast (by omega)
  have h9 : ((a.1 + 1 : ℕ) : ℚ) ≤ D.R.m := by exact_mod_cast a.2
  have h10 : (0 : ℚ) ≤ gap D C := by positivity
  have h11 : (gap D C : ℚ) ≤ ((D.R.m : ℚ) + 1 - ((a.1 + 1 : ℕ) : ℚ)) * (gap D C : ℚ) := by nlinarith
  have h12 : BlochKatoReduction.Gen.NFun D.R = bigN D := GlobalTheory.LamTie.nFun_eq_bigN D
  rw [h12]
  unfold eExp cen
  push_cast at h8
  linarith

end GlobalTheory.BigTop.Fun

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PowFinrankOmegaLeFinrankFrobeniusKernel
section
open CategoryTheory TensorProduct MvPowerSeries GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup GlobalTheory.Katz

namespace GlobalTheory.PDivGroup

theorem pow_finrank_omega_le_finrank_frobKer : ∀ (p : ℕ) [Fact p.Prime] (K : Type) [Field K] (h : (p : K) = 0)
    (G : PDivGroup p K), ∀ r : ℕ,
    (p ^ r) ^ Module.finrank K G.omega ≤ Module.finrank K (G.A r ⧸ frobKerIdeal (p ^ r) K (G.A r)) := by
  intro p _ K _ h G r
  haveI : CharP K p := (CharP.charP_iff_prime_eq_zero (Fact.out : p.Prime)).2 h
  have hN : Module.finrank K (G.A r) = p ^ (r * G.height) := by
    have := G.rank_eq r (IsLocalRing.closedPoint K)
    rwa [Module.rankAtStalk_eq_finrank_of_free] at this
  have hdim := (_root_.GlobalTheory.PDivGroup.finrank_rigExt_omega p K h G).2.2.2
  have hord := _root_.GlobalTheory.PDiv.finrank_le_frobKer_mul_span_pow p K (G.A r) r
  have hspan := _root_.GlobalTheory.finrank_span_pow_le p K h G r
  have hpos : 0 < (p ^ r) ^ Module.finrank K G.dual.omega :=
    pow_pos (pow_pos (Fact.out : p.Prime).pos _) _
  have key : (p ^ r) ^ Module.finrank K G.omega * (p ^ r) ^ Module.finrank K G.dual.omega ≤
      Module.finrank K (G.A r ⧸ frobKerIdeal (p ^ r) K (G.A r)) * (p ^ r) ^ Module.finrank K G.dual.omega := by
    rw [← pow_add, hdim, ← pow_mul, ← hN]
    exact hord.trans (Nat.mul_le_mul_left _ hspan)
  exact Nat.le_of_mul_le_mul_right key hpos

end GlobalTheory.PDivGroup
end

