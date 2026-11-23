module

public import Mathlib
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
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2564
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2550
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2663
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2664
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2516
public import Development.AbelianVarietyTheory.Definitions.Divisors.HasDivPlace
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2108
public import Development.AbelianVarietyTheory.Definitions.Divisors.OfFactorE
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsProjOverWeierstrass
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
public import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissibleBaseOfCompleteDvr
public import Development.AbelianVarietyTheory.Proofs.CharacterTheory.Bundle0002
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AlgIdemBinv
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2393
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2670
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2613
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0069
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2662
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2668
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0106
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsProperSemiAbelianFamily
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0012
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0001
public import Development.AbelianVarietyTheory.Definitions.Divisors.JetAnalytic
public import Development.AbelianVarietyTheory.Definitions.Divisors.ZetaActRefl
public import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.Bundle0009
public import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.Bundle0007
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0605
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2658
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2605
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0469
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0217
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.InvTranspose

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MixedIntegralDdcPairingSymmProjective
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Set Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.R
open GlobalTheory GlobalTheory.Cartier GlobalTheory.CxPts GlobalTheory.Points GlobalTheory.CechPic GlobalTheory.ChartGlue GlobalTheory.Mix

namespace GlobalTheory.Mix

theorem mInt_half {e : ℕ} {X : Type} [TopologicalSpace X] [CompactSpace X] [T2Space X] (A : FinHolAtlas e X)
    (Φ : Fin e → LocPot X) (hΦ : ∀ i, IsPotential A (Φ i)) (g : X → ℝ) (hg : Continuous g) :
    mInt A Φ (fun x => g x / 2) = mInt A Φ g / 2 := by
  have h0 := mIntegrableCont A Φ hΦ (fun _ => 0) continuous_const
  have h1 := mIntLinear A Φ hΦ 1 (fun _ => 0) (fun _ => 0) h0 h0
  have h2 := mIntLinear A Φ hΦ (1 / 2) g (fun _ => 0) (mIntegrableCont A Φ hΦ g hg) h0
  have e1 : (fun x => 1 / 2 * g x + 0) = fun x => g x / 2 := funext fun x => by ring
  simp only [mul_zero, add_zero] at h1
  rw [e1] at h2
  linarith

theorem mInt_cons_ofFun_symm {k : Type} [CommRing k] {X : Scheme.{0}} {p : X ⟶ Sp k} {σ : k →+* ℂ} {e : ℕ}
    [CompactSpace (CxPts p σ)] [T2Space (CxPts p σ)] {A : FinHolAtlas (e + 1) (CxPts p σ)} (hA : IsAlgAtlas A)
    (L : Fin e → MLine p σ) (u v : CxPts p σ → ℝ) (hu : ∀ y, CInfAt u y) (hv : ∀ y, CInfAt v y) :
    mInt A (fun i => ((Fin.cons (MLine.ofFun u hu) L : Fin (e + 1) → MLine p σ) i).φ.locPot) v =
      mInt A (fun i => ((Fin.cons (MLine.ofFun v hv) L : Fin (e + 1) → MLine p σ) i).φ.locPot) u := by
  have hpot (N : MLine p σ) : IsPotential A N.φ.locPot :=
    ((Weight.isCInf_iff_isSmooth hA.anRead).1 N.cInf).isPotential hA
  have hsm (a : CxPts p σ → ℝ) (ha : ∀ y, CInfAt a y) : A.Smooth fun y => a y / 2 := fun j =>
    ((hA.smooth_iff hA.anRead).2 ((cInfAt_iff_smoothOn hA.anRead isOpen_univ).1 fun y _ => ha y) j).div_const 2
  have key (a b : CxPts p σ → ℝ) (ha : ∀ y, CInfAt a y) (hb : ∀ y, CInfAt b y) :
      mInt A (Fin.cons (LocPot.ofFun fun y => a y / 2) fun i => (L i).φ.locPot) (fun y => b y / 2) =
      mInt A (fun i => ((Fin.cons (MLine.ofFun a ha) L : Fin (e + 1) → MLine p σ) i).φ.locPot) b / 2 := by
    rw [← mInt_half A _ (fun i => hpot _) b (continuous_iff_continuousAt.2 fun y => (hb y).continuousAt)]
    refine SameForm.mInt_eq (fun i => ?_) _
    refine Fin.cases ?_ (fun j => ?_) i
    · exact fun _ _ _ => rfl
    · exact fun _ _ _ => rfl
  have h := byPartsSymm A _ _ (hsm v hv) (hsm u hu) (fun i => (L i).φ.locPot) fun i => hpot _
  rw [key u v hu hv, key v u hv hu] at h
  linarith

theorem int_cons_ofFun_symm : GlobalTheory.Published.Principalisation → ∀ (F : Type) [Field F] (X : Scheme.{0}) [IsIntegral X] [IsLocallyNoetherian X] (p : X ⟶ Sp F) (σ : F →+* ℂ) (e : ℕ), IsProjOver p → topologicalKrullDim X = (e + 1 : ℕ) → ∀ (L : Fin e → MLine p σ) (u v : CxPts p σ → ℝ) (hu : ∀ y, CInfAt u y) (hv : ∀ y, CInfAt v y), Mix.int (Fin.cons (MLine.ofFun u hu) L : Fin (e + 1) → MLine p σ) v = Mix.int (Fin.cons (MLine.ofFun v hv) L : Fin (e + 1) → MLine p σ) u := by
  intro hP F _ X _ _ p σ e hproj hdim L u v hu hv
  haveI : CharZero F := RingHom.charZero σ
  obtain ⟨Y, hY, π, hsm, hprojY, -, hgen, hdeg, -⟩ :=
    _root_.GlobalTheory.LogResProj.exists_logResolution hP F X p (e + 1) hproj hdim ⊥
      (by rw [← SetLike.mem_coe, TopologicalSpace.Closeds.coe_bot]; exact Set.notMem_empty _)
  haveI := hsm
  haveI : CompactSpace (CxPts (π ≫ p) σ) := CxPts.compactSpace σ hprojY
  haveI : T2Space (CxPts (π ≫ p) σ) := CxPts.t2Space_cxPts_of_isProjOver σ hprojY
  haveI : SecondCountableTopology (CxPts (π ≫ p) σ) := CxPts.secondCountableTopology_of_isProjOver σ hprojY
  have hA : IsAlgAtlas (AnRead.all (π ≫ p) σ (e + 1)).finAtlas := AnRead.isAlgAtlas_finAtlas _
  have hiso := _root_.GlobalTheory.Mix.isom_calculus F X Y p (π ≫ p) σ π rfl
  have hisoY := _root_.GlobalTheory.Mix.isom_calculus F Y Y (π ≫ p) (π ≫ p) σ (𝟙 Y) (Category.id_comp _)
  have key (a b : CxPts p σ → ℝ) (ha : ∀ y, CInfAt a y) (hb : ∀ y, CInfAt b y) :
      Mix.int (Fin.cons (MLine.ofFun a ha) L : Fin (e + 1) → MLine p σ) b =
      mInt (AnRead.all (π ≫ p) σ (e + 1)).finAtlas (fun i => ((Fin.cons (MLine.ofFun (fun z => a (ptMap π rfl σ z))
        fun z => (ha _).pull π rfl) fun i => (L i).pull π rfl : Fin (e + 1) → MLine (π ≫ p) σ) i).φ.locPot)
        (fun z => b (ptMap π rfl σ z)) := by
    have hbc : Continuous b := continuous_iff_continuousAt.2 fun y => (hb y).continuousAt
    have hbc' : Continuous fun z : CxPts (π ≫ p) σ => b (ptMap π rfl σ z) :=
      continuous_iff_continuousAt.2 fun z => ((hb _).pull π rfl).continuousAt
    have h1 := (_root_.GlobalTheory.PushInt.mixInt_pull F X Y p (π ≫ p) σ (e + 1) hproj hdim hprojY π rfl hgen
      (by rw [hdeg]; exact one_ne_zero) (Fin.cons (MLine.ofFun a ha) L) b hbc.measurable).2
    rw [hdeg, Nat.cast_one, one_mul] at h1
    have h2 := _root_.GlobalTheory.Mix.part_eq_of_isom F Y (π ≫ p) σ hprojY (e + 1)
      (fun i => ((Fin.cons (MLine.ofFun a ha) L : Fin (e + 1) → MLine p σ) i).pull π rfl)
      (Fin.cons (MLine.ofFun (fun z => a (ptMap π rfl σ z)) fun z => (ha _).pull π rfl) fun i => (L i).pull π rfl)
      (fun i => Fin.cases (hiso.2.2.2.1 a ha) (fun j => hisoY.1 _) i)
    have h3 := GlobalTheory.T.mixedChernIntegral_eq_mongeAmpereIntegral_compact F Y (π ≫ p) σ (e + 1) _ hA
      (Fin.cons (MLine.ofFun (fun z => a (ptMap π rfl σ z)) fun z => (ha _).pull π rfl) fun i => (L i).pull π rfl)
      _ hbc'.measurable
    rw [← h1, ← h3.2 (h3.1.2 (mIntegrableCont _ _
      (fun i => ((Weight.isCInf_iff_isSmooth hA.anRead).1 (MLine.cInf _)).isPotential hA) _ hbc'))]
    simp only [Mix.int, h2]
  rw [key u v hu hv, key v u hv hu]
  exact mInt_cons_ofFun_symm hA _ _ _ _ _

end GlobalTheory.Mix
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.NondegenerateIntegralForm
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.AV GlobalTheory.AV.AbVar GlobalTheory.PDivGroup GlobalTheory.Dieu GlobalTheory.UPel.HT GlobalTheory.LKTrip GlobalTheory.LKMid GlobalTheory.LKGeo GlobalTheory.LKRes
open ReciprocityTheory.DiscreteGroups.LocalClassField
open scoped TensorProduct

namespace GlobalTheory.LKGeo

theorem det_gram_ne_zero {L : Type} [AddCommGroup L] {κ : Type} [Fintype κ] [DecidableEq κ]
    (b : Module.Basis κ ℤ L) (B : LinearMap.BilinForm ℤ L) (hB : Function.Injective B) :
    (Matrix.of fun i j => B (b i) (b j)).det ≠ 0 := by
  intro h0
  obtain ⟨c, hc0, hc⟩ := Matrix.exists_vecMul_eq_zero_iff.mpr h0
  apply hc0
  have hx : B (∑ i, c i • b i) = 0 := by
    apply b.ext
    intro j
    have := congrFun hc j
    set_option synthInstance.maxHeartbeats 100000 in
      simpa [Matrix.vecMul, dotProduct, map_sum, map_smul, mul_comm] using this
  have h1 : ∑ i, c i • b i = 0 := hB (hx.trans (map_zero B).symm)
  funext i
  exact Fintype.linearIndependent_iff.mp b.linearIndependent c h1 i

theorem nondeg_afP : ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (z : AfP p ⊗[ℚ] VQ D),
    (∀ v, (D.EF.baseChange ℚ).baseChange (AfP p) v z = 0) → z = 0 := by
  intro p _ D z hz
  classical
  haveI := D.freeLa; haveI := D.finLa
  let b := Module.Free.chooseBasis ℤ D.La
  let bQ := Algebra.TensorProduct.basis ℚ b
  let bA := Algebra.TensorProduct.basis (AfP p) bQ
  have hg : ∀ i j, (D.EF.baseChange ℚ).baseChange (AfP p) (bA i) (bA j) = ((D.EF (b i) (b j) : ℤ) : AfP p) := by
    intro i j
    simp [bA, bQ, LinearMap.BilinForm.baseChange_tmul, Algebra.smul_def]
  set c := bA.repr z
  let M : Matrix _ _ (AfP p) := (Matrix.of fun i j => D.EF (b i) (b j)).map (Int.castRingHom (AfP p))
  have hzs : z = ∑ j, c j • bA j := (bA.sum_repr z).symm
  have hM : M.mulVec c = 0 := by
    funext i
    have := hz (bA i)
    set_option synthInstance.maxHeartbeats 100000 in
      rw [hzs, map_sum] at this
    simpa [Matrix.mulVec, dotProduct, M, hg, mul_comm] using this
  have hdet : IsUnit M.det := by
    rw [show M.det = Int.castRingHom (AfP p) (Matrix.of fun i j => D.EF (b i) (b j)).det from
      (RingHom.map_det _ _).symm]
    have h0 := det_gram_ne_zero b D.EF D.nondeg
    have hq : IsUnit (((Matrix.of fun i j => D.EF (b i) (b j)).det : ℤ) : ℚ) :=
      isUnit_iff_ne_zero.mpr (by exact_mod_cast h0)
    have := hq.map (algebraMap ℚ (AfP p))
    simpa using this
  have hc : (⇑c : _ → AfP p) = 0 := by
    have := congrArg (M⁻¹).mulVec hM
    rwa [Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ hdet, Matrix.one_mulVec, Matrix.mulVec_zero] at this
  have hc' : ∀ j, c j = 0 := fun j => congrFun hc j
  rw [hzs]
  simp [hc']

end GlobalTheory.LKGeo
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.NonemptyOfTensorDataPosDefUnimodular
section
noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.TChart GlobalTheory.Mum

namespace GlobalTheory.Mum.PowLim.Rosati

open GlobalTheory.CechPic GlobalTheory.Mum.RosatiTens

variable {R : Type} [CommRing R] [IsDomain R] {Q : Data R} {D' : DegPre R} {r : ℕ}
  {pr : Fin r → (D'.P.A ⟶ Q.B)}

def pairQ (Q : Data R) (pr : Fin r → (D'.P.A ⟶ Q.B)) (M : Matrix (Fin r) (Fin r) ℤ) {X : Over (Spec (CommRingCat.of R))}
    (u v : X ⟶ D'.P.A) : Pic X.left :=
  ∑ i, ∑ j, M i j • lam (cls Q.M.L Q.M.isLB) (u ≫ pr i) (v ≫ pr j)

theorem cls_pow {W : Matrix (Fin r) (Fin r) ℤ} (w : LB.Iso D'.P.L (LB.LinComb Q.M.L (tensφ pr) (tensε W)))
    (hw : w.IsGen) : cls D'.P.L D'.P.isLB = ∑ i, ∑ j, W i j • lam (cls Q.M.L Q.M.isLB) (pr i) (pr j) := by
  have hC := LB.isLB_linComb Q.M.isLB (tensφ pr) (tensε W)
  refine ((cls_eq_iff D'.P.isLB hC).2 ⟨w, hw⟩).trans ?_
  rw [cls_linComb Q.M.isLB, Fintype.sum_prod_type, Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  simp only [Fin.sum_univ_four, tensφ, tensε, GlobalTheory.PolDeg.lamPts, Oε, lam, mul_smul, ← smul_add]
  congr 1
  simp
  abel

theorem pull_pow {W : Matrix (Fin r) (Fin r) ℤ} (w : LB.Iso D'.P.L (LB.LinComb Q.M.L (tensφ pr) (tensε W)))
    (hw : w.IsGen) {X : Over (Spec (CommRingCat.of R))} (h : X ⟶ D'.P.A) :
    pull h.left (cls D'.P.L D'.P.isLB) = pairQ Q pr W h h := by
  set_option synthInstance.maxHeartbeats 100000 in
    rw [cls_pow w hw, pairQ, map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [map_zsmul, pull_lam]

theorem pairQ_mul (hpr : ∀ i, IsMonHom (pr i)) (W : Matrix (Fin r) (Fin r) ℤ) {X : Over (Spec (CommRingCat.of R))}
    (u v : X ⟶ D'.P.A) :
    pairQ Q pr W (u * v) (u * v) = pairQ Q pr W u u + pairQ Q pr W v v + pairQ Q pr (W + W.transpose) u v := by
  have hm : ∀ i, (u * v) ≫ pr i = u ≫ pr i * v ≫ pr i := fun i => by
    haveI := hpr i
    exact MonObj.mul_comp _ _ _
  have hΘ : ∃ t : LB.Gen (Theta Q.B Q.M.L), t.IsGen := ⟨Q.cub.t, Q.cub.isGen⟩
  have e : ∑ i, ∑ j, W i j • lam (cls Q.M.L Q.M.isLB) (v ≫ pr i) (u ≫ pr j) =
      ∑ i, ∑ j, W.transpose i j • lam (cls Q.M.L Q.M.isLB) (u ≫ pr i) (v ≫ pr j) := by
    rw [Finset.sum_comm]
    simp only [Matrix.transpose_apply, lam_comm _ (v ≫ _)]
  simp only [pairQ, hm, lam_mul_left Q.M.isLB hΘ, lam_mul_right Q.M.isLB hΘ, smul_add, Finset.sum_add_distrib,
    Matrix.add_apply, add_smul]
  rw [e]
  abel

theorem comp_act_pr' (hl : IsLimit (Fan.mk D'.P.A pr)) {X : Over (Spec (CommRingCat.of R))} (u : X ⟶ D'.P.A)
    (m : Matrix (Fin r) (Fin r) ℤ) (i : Fin r) :
    (u ≫ PowLim.act pr hl m) ≫ pr i = ∏ k, (u ≫ pr k) ^ m i k := by
  rw [Category.assoc, PowLim.act_pr]
  exact (map_prod (pre (Z := Q.B) u) _ _).trans (Finset.prod_congr rfl fun k _ => map_zpow (pre (Z := Q.B) u) _ _)

theorem pairQ_act_left (hl : IsLimit (Fan.mk D'.P.A pr)) (M m : Matrix (Fin r) (Fin r) ℤ)
    {X : Over (Spec (CommRingCat.of R))} (u v : X ⟶ D'.P.A) :
    pairQ Q pr M (u ≫ PowLim.act pr hl m) v = pairQ Q pr (m.transpose * M) u v := by
  have hΘ : ∃ t : LB.Gen (Theta Q.B Q.M.L), t.IsGen := ⟨Q.cub.t, Q.cub.isGen⟩
  simp only [pairQ, comp_act_pr', lam_prod_left Q.M.isLB hΘ, Finset.smul_sum, smul_smul, Matrix.mul_apply,
    Matrix.transpose_apply, Finset.sum_smul]
  rw [Finset.sum_comm]
  conv_rhs => rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Finset.sum_comm]
  simp only [mul_comm]

theorem pairQ_act_right (hl : IsLimit (Fan.mk D'.P.A pr)) (M m : Matrix (Fin r) (Fin r) ℤ)
    {X : Over (Spec (CommRingCat.of R))} (u v : X ⟶ D'.P.A) :
    pairQ Q pr M u (v ≫ PowLim.act pr hl m) = pairQ Q pr (M * m) u v := by
  have hΘ : ∃ t : LB.Gen (Theta Q.B Q.M.L), t.IsGen := ⟨Q.cub.t, Q.cub.isGen⟩
  simp only [pairQ, comp_act_pr', lam_prod_right Q.M.isLB hΘ, Finset.smul_sum, smul_smul, Matrix.mul_apply,
    Finset.sum_smul]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.sum_comm]

theorem rosatiAdj_pow : ∀ (R : Type) [CommRing R] [IsDomain R] (Q : Data R) (D' : DegPre R) {r : ℕ} (W : Matrix (Fin r) (Fin r) ℤ)
    (h : IsUnit (W + W.transpose).det) (pr : Fin r → (D'.P.A ⟶ Q.B)) (hl : IsLimit (Fan.mk D'.P.A pr))
    (w : LB.Iso D'.P.L (LB.LinComb Q.M.L (tensφ pr) (tensε W))), (∀ i, IsMonHom (pr i)) → w.IsGen →
    ∀ a : TensO (symUnitOf W h), RosatiAdj D'.P.A D'.P.L (PowLim.act pr hl (TensO.mat _ a)) (PowLim.act pr hl (TensO.mat _ (star a))) := by
  intro R _ _ Q D' r W h pr hl w hpr hw a
  intro s
  refine ⟨⊤, trivial, (cls_eq_zero_iff (LB.isLB_linComb D'.P.isLB _ _)).1 ?_⟩
  rw [cls_linComb D'.P.isLB]
  let f := PowLim.act pr hl (TensO.mat _ a)
  let g := PowLim.act pr hl (TensO.mat _ (star a))
  let H : Fin 6 → (D'.P.A ⊗ D'.P.A ⟶ D'.P.A) := ![fst _ _ ≫ f * snd _ _, fst _ _ ≫ f, snd _ _,
    fst _ _ * snd _ _ ≫ g, fst _ _, snd _ _ ≫ g]
  have hH : rosatiφ D'.P.A f g = fun k => (H k).left := by
    funext k
    fin_cases k <;> simp [rosatiφ, H, padd, Hom.mul_def]
  have key : ∑ k, rosatiε k • pull (rosatiφ D'.P.A f g k) (cls D'.P.L D'.P.isLB) = 0 := by
    simp only [hH, pull_pow w hw]
    simp only [Fin.sum_univ_six, H, rosatiε, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
      Matrix.cons_val_three, Matrix.cons_val_four, Matrix.head_cons, Matrix.tail_cons, Matrix.cons_val]
    rw [pairQ_mul hpr, pairQ_mul hpr]
    rw [pairQ_act_left hl (W + W.transpose) (TensO.mat _ a) (fst _ _) (snd _ _),
      pairQ_act_right hl (W + W.transpose) (TensO.mat _ (star a)) (fst _ _) (snd _ _), symUnit_mul_star]
    simp only [one_smul, neg_smul]
    abel
  calc ∑ k, rosatiε k • pull (((D'.P.A ⊗ D'.P.A).hom ⁻¹ᵁ ⊤).ι ≫ rosatiφ D'.P.A f g k) (cls D'.P.L D'.P.isLB)
      = pull (((D'.P.A ⊗ D'.P.A).hom ⁻¹ᵁ ⊤).ι)
          (∑ k, rosatiε k • pull (rosatiφ D'.P.A f g k) (cls D'.P.L D'.P.isLB)) := by
        set_option synthInstance.maxHeartbeats 100000 in
          simp only [pull_comp, map_sum, map_zsmul]
    _ = 0 := by rw [key, map_zero]

end GlobalTheory.Mum.PowLim.Rosati

theorem GlobalTheory.Mum.PFactor.nonempty_of_tens : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], IsCN R → ∀ (Q : Data R) (D' : DegData R (maximalIdeal R))
  {r : ℕ} (W : Matrix (Fin r) (Fin r) ℤ), ((W + W.transpose).map (Int.cast : ℤ → ℝ)).PosDef → IsUnit (W + W.transpose).det → 1 ≤ r →
  ∀ (pr : Fin r → (D'.toPre.P.A ⟶ Q.B)) (xe : D'.toPre.X ≃+ (Fin r → Q.X))
    (w : LB.Iso D'.toPre.P.L (LB.LinComb Q.M.L (tensφ pr) (tensε W))),
    (∀ i, IsMonHom (pr i)) → Nonempty (IsLimit (Fan.mk D'.toPre.P.A pr)) →
    (∀ z i, D'.toPre.c z ≫ pr i = Q.c (xe z i)) → w.IsGen →
    (∀ y z J J', Good Q.M.L z J → Good D'.toPre.P.L z J' →
      val (D'.toPre.psi y) (𝟙 _) z J' = gm (D'.toPre.xK y) z _ (w.s (fun k => J (D'.toPre.xK y ≫ tensφ pr k), J' (D'.toPre.xK y))) *
        ∏ i, ∏ j, val (Q.tau (xe y i) (xe y j)) (𝟙 _) z J ^ W i j) →
    Nonempty (PFactor Q D'.toPre) := by
  intro R _ _ _ hR Q D' r W hpos hdet hr pr xe w hpr hlim hc hw hpsi
  let hl := hlim.some
  let s := symUnitOf W hdet
  let i₀ : Fin r := ⟨0, hr⟩
  letI := PowLim.mod xe s
  obtain ⟨w', hw', htau⟩ := GlobalTheory.T.mumfordIso_periods_factor_tensor_polarised R hR Q D' W hdet hpos pr hl xe w hpr hc hw hpsi i₀
  obtain ⟨hxx, hxe, hinj, honto⟩ := PowLim.factor_latt xe s i₀
  have hp : 0 < (s.1 : Matrix (Fin r) (Fin r) ℤ) i₀ i₀ := by
    have h := hpos.diag_pos (i := i₀)
    have h' : (0 : ℝ) < (((W + W.transpose) i₀ i₀ : ℤ) : ℝ) := h
    exact_mod_cast h'
  exact ⟨{
    O := TensO s
    mod := PowLim.mod xe s
    o := { onB := { act := fun a => PowLim.act pr hl (TensO.mat s a)
                    hom := fun a => PowLim.act_isMonHom pr hl hpr _
                    map_one := PowLim.act_one pr hl
                    map_mul := fun a b => PowLim.act_mul pr hl _ _
                    map_add := fun a b => PowLim.act_add pr hl hpr _ _
                    rosati := GlobalTheory.Mum.PowLim.Rosati.rosatiAdj_pow R Q D'.toPre W hdet pr hl w hpr hw }
           c_lin := PowLim.c_smul Q D'.toPre pr hl xe hc s
           tau_bal := GlobalTheory.T.tensorData_periods_balanced_integralMatrices R hR Q D' W hdet hpos pr hl xe w hpr hc hw hpsi }
    e := TensO.idem s i₀
    f := TensO.binv s
    inc := PowLim.inc pr hl i₀
    pr := pr i₀
    xi := PowLim.xi xe i₀
    xp := PowLim.xp xe i₀
    w := w'
    idem := TensO.idem_mul_idem s i₀
    inc_hom := PowLim.inc_isMonHom pr hl hpr i₀
    pr_hom := hpr i₀
    inc_pr := PowLim.inc_pr_self pr hl i₀
    pr_inc := PowLim.pr_inc pr hl i₀
    xp_xi := hxx
    xi_xp := hxe
    c_xi := PowLim.c_xi Q D'.toPre pr hl xe hc i₀
    inj := hinj
    onto := honto
    w_gen := hw'
    tau := htau
    alg := PowLim.alg_idem_binv s i₀ hp }⟩
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.NonvanishingLocusAmpleSectionIsAffineModel
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.VolBr GlobalTheory.HSAmp
open ReciprocityTheory.ChartRestriction.G.DVR.FlatBC (algX)

set_option autoImplicit false
noncomputable section
namespace GlobalTheory.AffModel

theorem main : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k) (D : ℕ), IsArithVar p D → ∀ (P : Pair p), IsAmpleLB P.L.B → ∀ (e : ℕ) (g : X.functionField), 0 < e → g ∈ P.H e 0 → g ≠ 0 → ∃ (U : X.Opens) (h : genericPoint X ∈ U), (U : Set X) = NV P e 0 g ∧ IsAffineOpen U ∧ (∀ w : X.functionField, (∀ z ∈ U, RegAt z w) ↔ w ∈ (fnOf U h).range) ∧ Algebra.FiniteType ℤ (fnOf U h).range ∧ (∀ w : X.functionField, ∃ a ∈ (fnOf U h).range, ∃ b ∈ (fnOf U h).range, b ≠ 0 ∧ w = a / b) ∧ ∀ φ : (fnOf U h).range →+* ℂ, ∃ (σ : k →+* ℂ) (y : CxPts p σ), under y ∈ U ∧ ∀ w : (fnOf U h).range, ratVal (w : X.functionField) y = φ w := by
  intro k _ X _ p D hV P hA e g he hg hg0
  obtain ⟨u, hu⟩ := (_root_.GlobalTheory.HSAmp.pow_sec_dict k X p P e).2 g hg
  have hN := _root_.GlobalTheory.HSAmp.nv_rules k X p P (e : ℤ) 0 g hg
  have : IsProper p := GlobalTheory.ProperFamily.isProper_of_isProjOver hV.isProjOver
  have hU : IsAffineOpen (ReciprocityTheory.ChartRestriction.G.Out.nonzeroLocus u) := IsAmpleLB.isAffineOpen_nonzeroLocus p hA he u
  have hgen : genericPoint X ∈ ReciprocityTheory.ChartRestriction.G.Out.nonzeroLocus u := by
    have := hN.2.1.2 hg0
    rw [hu] at this
    exact this
  set U := ReciprocityTheory.ChartRestriction.G.Out.nonzeroLocus u with hUdef
  have : Nonempty U := ⟨⟨_, hgen⟩⟩
  have hfr := functionField_isFractionRing_of_isAffineOpen X U hU
  refine ⟨U, hgen, hu.symm, hU, ?_, ?_, ?_, ?_⟩
  · intro w
    refine ⟨fun h => ?_, ?_⟩
    · obtain ⟨a, ha⟩ := exists_fnOf_eq hgen h
      exact ⟨a, ha⟩
    · rintro ⟨a, rfl⟩ z hz
      exact regAt_fnOf hz hgen a
  · have h1 : (algebraMap ℤ k).FiniteType := by
      have := hV.finite
      exact RingHom.finiteType_algebraMap.2 inferInstance
    have h2 : (p.appLE ⊤ U le_top).hom.FiniteType :=
      p.finiteType_appLE (isAffineOpen_top _) hU _
    have h3 : (Scheme.ΓSpecIso (CommRingCat.of k)).inv.hom.FiniteType :=
      RingHom.FiniteType.of_surjective _ (fun x => ⟨(Scheme.ΓSpecIso (CommRingCat.of k)).hom.hom x, by
        rw [← CommRingCat.comp_apply, Iso.hom_inv_id, CommRingCat.id_apply]⟩)
    have h4 : (fnOf U hgen).rangeRestrict.FiniteType :=
      RingHom.FiniteType.of_surjective _ (fnOf U hgen).rangeRestrict_surjective
    have h5 := h4.comp (h2.comp (h3.comp h1))
    rw [← RingHom.finiteType_algebraMap]
    convert h5
    exact RingHom.ext_int _ _
  · intro w
    obtain ⟨a, b, hb, hab⟩ := IsFractionRing.div_surjective (A := Γ(X, U)) w
    refine ⟨_, ⟨a, rfl⟩, _, ⟨b, rfl⟩, ?_, ?_⟩
    · exact fun h0 => nonZeroDivisors.ne_zero hb (fnOf_injective U hgen (h0.trans (map_zero _).symm))
    · exact hab.symm
  · intro φ
    let ψ : Γ(X, U) →+* ℂ := φ.comp (fnOf U hgen).rangeRestrict
    refine ⟨ψ.comp (algX p U), CxPts.ofHom hU ψ (fun _ => rfl), mem_ptsIn.1 (CxPts.ofHom_mem hU ψ _), ?_⟩
    rintro ⟨_, a, rfl⟩
    rw [ratVal_fnOf (CxPts.ofHom_mem hU ψ _) hgen a, CxPts.ev_ofHom]
    rfl

end GlobalTheory.AffModel
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.NormHilbertEisensteinValueLeOfIntegralJ
section
open NumberField UpperHalfPlane GlobalTheory.HilbFam GlobalTheory.QFam
open GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization (Emb Frac latM qPow upperHalf cK omegaFactor IsPartialZeta HasExpansion)
open GlobalTheory.IndefiniteRowSideFullHecke.DefiningCoordinates (iterD partialD)
open scoped Classical MatrixGroups nonZeroDivisors
open GlobalTheory.LatVal (Sz)
open GlobalTheory.LatJet (EisExp IsEis FR)
open GlobalTheory.WpFam
open ReciprocityTheory.ChartRestriction.L1 (DD jT)
open ModularForm (E₄ E₆)

namespace GlobalTheory.HilbFam

theorem size_values_hfun : EisExp → ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F], 2 ≤ Module.finrank ℚ F → ∀ (s N : ℕ) [NeZero N] (L : Lat F), 1 ≤ s → HasLevel N L → ∀ [IsGalois ℚ F] (z : ClassGroup (𝓞 F) → ℚ), ZetaVals (2 * s) z → ∀ (l : ℕ) [Fact l.Prime] (lam : algebraicClosure ℚ ℂ →+* ℂ_[l]) (κ : Emb F → ℕ) (y : Fin 2 → ZMod N) (M M' b : ℕ) (e ρ₀ ρ : ℝ), 0 ≤ e → (∀ C, -(padicValRat l (z C / 2 ^ Module.finrank ℚ F) : ℝ) ≤ e) → ¬ l ∣ M → (∀ x ∈ stdLat F, ((M * l ^ b : ℕ) : 𝓞 F) • x ∈ L) → (∀ v ∈ L, ∀ (j : Fin 2) (i : Emb F), Sz l lam ρ₀ ((i (v j) : ℝ) : ℂ)) → Sz l lam ρ₀ (N : ℂ) → b + (padicValInt l (discr F) : ℝ) / Module.finrank ℚ F + ρ₀ ≤ ρ → 0 ≤ ρ → ¬ l ∣ M' → M' • y = 0 → y ≠ 0 →  ∀ (τ : ℍ) (ω : ℂ), Sz l lam 0 (jT τ) → ω ^ 12 = DD τ → Sz l lam (e + s * (padicValInt l (discr F) : ℝ) + 2 * s * b * Module.finrank ℚ F + (∑ i, κ i : ℕ) * ρ) (hfun (2 * s) L κ (wB N y) τ / ω ^ wt (2 * s) κ) := by
  intro hE F _ _ _ hf s N _ L hs hL _ z hz l _ lam κ y M M' b e ρ₀ ρ he hze hlM hML hLsz hNsz hρ hρ0 hlM' hMy hy τ ω hj hω
  have hA := GlobalTheory.WpFam.Act.rightActions N
  have hN : 0 < N := Nat.pos_of_ne_zero (NeZero.ne N)
  have hfam := _root_.GlobalTheory.HilbFam.isFam_hfun_GL hE F hf s N L hs hL y κ
  have hq := GlobalTheory.HilbFam.SizeGL.main hE F hf s N L hs hL z hz l lam κ y M M' b e ρ₀ ρ he hze hlM hML hLsz hNsz hρ hρ0 hlM' hMy hy
  have key := GlobalTheory.QFam.sz_value_of_family l lam (GL (Fin 2) (ZMod N)) (gact N 1) (wt (2 * s) κ) N _ _ τ ω hN
    ((hA.2.1 1).actBij) hfam hq hj hω 1
  simp only [Units.val_one, twist_one_of_hasLevel F N L hL, hA.2.2.2.1] at key
  exact key

end GlobalTheory.HilbFam
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TensorDegDataPeriodsBalancedMatrixActionStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.tensorDegData_periods_balanced_matrixAction : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], AdmBase R (maximalIdeal R) → ∀ (D D' : DegData R (maximalIdeal R)) {r : ℕ} (W : Matrix (Fin r) (Fin r) ℤ) (h : IsUnit (W + W.transpose).det), ((W + W.transpose).map (Int.cast : ℤ → ℝ)).PosDef → ∀ (T : Tens D.toPre D'.toPre W), letI := T.mod (symUnitOf W h); ∀ a : TensO (symUnitOf W h), D'.toPre.TauBal (T.act (TensO.mat _ a)) (T.act (TensO.mat _ (star a))) (fun y => a • y) (fun y => star a • y) := by
  first | exact @GlobalTheory.Mum.TensBal.tauBal_tens | exact GlobalTheory.Mum.TensBal.tauBal_tens | (intros; apply GlobalTheory.Mum.TensBal.tauBal_tens <;> assumption)
end

