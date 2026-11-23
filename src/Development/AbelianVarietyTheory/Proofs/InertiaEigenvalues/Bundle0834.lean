module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DecaysOfMemSmoothSpan
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0701
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MeasurePreservingToMixedPiSymm
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DifferentiableIntegralMulCpow
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0282
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0423
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.UnivChar
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0801
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0802
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0828
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0813
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AdelicUnitriangularMulMemUnipotentTimesIntegral
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0025
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0824
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0462
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.ToUnitsCompToCircle
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0775
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0025
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0034
public import Development.AbelianVarietyTheory.Definitions.ThetaValues.ExistsRootNotMem
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1656
public import Formalism.SharpRestriction.Divisibility.GeneratorPowers.Bundle0007
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0821

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IntegrableOnMinAbsDetInvFundamentalDomain
section
open NumberField Matrix MeasureTheory GlobalTheory.CuspRep GlobalTheory.CuspRep.CuspidalL2GL
open scoped ENNReal

noncomputable section

open GlobalTheory.UnitaryBC

namespace GlobalTheory.FinVolGL

theorem exists_tsum_min_le {T : ℝ} (hT : 1 < T) : ∃ B : ℝ≥0∞, B ≠ ⊤ ∧ ∀ u : ℝ, 0 < u →
    ∑' n : ℤ, ENNReal.ofReal (min (T ^ n * u) (T ^ n * u)⁻¹) ≤ B := by
  have hT0 : 0 < T := one_pos.trans hT
  have hq0 : 0 ≤ T⁻¹ := inv_nonneg.2 hT0.le
  have hq : T⁻¹ < 1 := inv_lt_one_of_one_lt₀ hT
  have hsum : Summable fun k : ℤ => T * T⁻¹ ^ k.natAbs :=
    (Summable.of_nat_of_neg (by simpa using summable_geometric_of_lt_one hq0 hq)
      (by simpa using summable_geometric_of_lt_one hq0 hq)).mul_left T
  refine ⟨∑' k : ℤ, ENNReal.ofReal (T * T⁻¹ ^ k.natAbs), hsum.tsum_ofReal_ne_top, fun u hu => ?_⟩
  obtain ⟨m, h1, h2⟩ := exists_mem_Ico_zpow hu hT
  rw [← (Equiv.subRight m).tsum_eq]
  refine ENNReal.tsum_le_tsum fun k => ENNReal.ofReal_le_ofReal ?_
  rw [Equiv.subRight_apply]
  have hp : 0 < T ^ (k - m) := zpow_pos hT0 _
  have e1 : T ^ (k - m) * T ^ m = T ^ k := by rw [← zpow_add₀ hT0.ne', sub_add_cancel]
  have e2 : T ^ (k - m) * T ^ (m + 1) = T ^ (k + 1) := by
    rw [← zpow_add₀ hT0.ne']; congr 1; ring
  have hv1 : T ^ k ≤ T ^ (k - m) * u := e1 ▸ mul_le_mul_of_nonneg_left h1 hp.le
  have hv2 : T ^ (k - m) * u < T ^ (k + 1) := e2 ▸ mul_lt_mul_of_pos_left h2 hp
  obtain ⟨j, rfl | rfl⟩ := Int.eq_nat_or_neg k
  · refine (min_le_right _ _).trans ?_
    have h3 := inv_anti₀ (zpow_pos hT0 _) hv1
    rw [zpow_natCast, ← inv_pow] at h3
    rw [Int.natAbs_natCast]
    exact h3.trans (le_mul_of_one_le_left (pow_nonneg hq0 _) hT.le)
  · refine (min_le_left _ _).trans (hv2.le.trans (le_of_eq ?_))
    rw [zpow_add_one₀ hT0.ne', _root_.zpow_neg, zpow_natCast, Int.natAbs_neg, Int.natAbs_natCast, inv_pow, mul_comm]

theorem integrableOn_min_absDet : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (m : ℕ), 0 < m →
    ∀ (μ : Measure (GA E m)) [μ.IsHaarMeasure] (𝓕 : Set (GA E m)),
      IsFundamentalDomain (ratGL E m).range 𝓕 μ →
      IntegrableOn (fun h : GA E m => min (GroundTheory.Global.IdeleGroup.ideleModule E (GeneralLinearGroup.det h) : ℝ)
        (GroundTheory.Global.IdeleGroup.ideleModule E (GeneralLinearGroup.det h) : ℝ)⁻¹) 𝓕 μ := by
  intro E _ _ _ a ha μ _ 𝓕 h𝓕
  set δ : GA E a → ℝ := fun g => (GroundTheory.Global.IdeleGroup.ideleModule E (GeneralLinearGroup.det g) : ℝ) with hδ
  have hδc : Continuous δ := GlobalTheory.RSTheta.continuous_absDet
  have hδ0 : ∀ g, 0 < δ g := fun g => (GroundTheory.Global.IdeleGroup.ideleModule E _).2
  have hδr : ∀ γ g, δ (ratGL E a γ * g) = δ g := fun γ g => by
    simp only [hδ, map_mul, GlobalTheory.ShortVecDecay.ideleModule_det_rat, one_mul]
  set T : ℝ := Real.exp 1 ^ (a * Module.finrank ℚ E) with hT
  have hT1 : 1 < T := one_lt_pow₀ (Real.one_lt_exp_iff.2 one_pos) (Nat.mul_pos ha Module.finrank_pos).ne'
  have hδz : ∀ (n : ℤ) g, δ (@GlobalTheory.UnitaryBC.splitCentre E _ _ _ a 1 ^ n * g) = T ^ n * δ g := GlobalTheory.RSTheta.absDet_zpow_mul
  have hc : Continuous fun g => min (δ g) (δ g)⁻¹ := hδc.min (hδc.inv₀ fun g => (hδ0 g).ne')
  refine ⟨hc.aestronglyMeasurable, (hasFiniteIntegral_iff_ofReal
    (.of_forall fun g => le_min (hδ0 g).le (inv_nonneg.2 (hδ0 g).le))).2 ?_⟩
  let φ : (ratGL E a).range × ℤ → latticeGL E a := fun p =>
    ⟨p.1 * @GlobalTheory.UnitaryBC.splitCentre E _ _ _ a 1 ^ p.2, mul_mem (Subgroup.mem_sup_left p.1.2) (zpow_mem_latticeGL _)⟩
  have hφ : Function.Bijective φ := by
    constructor
    · rintro ⟨⟨_, γ, rfl⟩, n⟩ ⟨⟨_, γ', rfl⟩, n'⟩ h
      have h1 : ratGL E a γ * @GlobalTheory.UnitaryBC.splitCentre E _ _ _ a 1 ^ n = ratGL E a γ' * @GlobalTheory.UnitaryBC.splitCentre E _ _ _ a 1 ^ n' := congrArg Subtype.val h
      have h2 := congrArg (fun x => δ (x * 1)) h1
      simp only [mul_assoc, hδr, hδz] at h2
      obtain rfl : n = n' := zpow_right_injective₀ (one_pos.trans hT1) hT1.ne' (mul_right_cancel₀ (hδ0 1).ne' h2)
      exact Prod.ext (Subtype.ext (mul_right_cancel h1)) rfl
    · rintro ⟨g, hg⟩
      obtain ⟨γ, n, rfl⟩ := mem_latticeGL_iff.1 hg
      exact ⟨⟨⟨_, γ, rfl⟩, n⟩, rfl⟩
  haveI : Countable (latticeGL E a) := TopologicalSpace.separableSpace_iff_countable.1 inferInstance
  have hd := GlobalTheory.AutomorphicL2Unitary.isFundamentalDomain_stdDom (latticeGL E a) μ
  haveI := GlobalTheory.CovolGL.isFiniteMeasure_quotMeasure E a μ
  have h1 : μ (GlobalTheory.AutomorphicL2Unitary.stdDom (latticeGL E a)) ≠ ⊤ := by
    rw [← GlobalTheory.AutomorphicL2Unitary.quotMeasure_univ hd]; exact measure_ne_top _ _
  rw [← GlobalTheory.ThetaUnfold.lintegral_unfold μ (latticeGL E a) (ratGL E a).range (fun n : ℤ => @GlobalTheory.UnitaryBC.splitCentre E _ _ _ a 1 ^ n)
    (Equiv.ofBijective φ hφ) (fun _ => rfl) hd h𝓕 (fun g => ENNReal.ofReal (min (δ g) (δ g)⁻¹))
    (by rintro _ ⟨γ, rfl⟩ g; simp only [hδr])
    hc.measurable.ennreal_ofReal.aemeasurable]
  obtain ⟨B, hB, h⟩ := exists_tsum_min_le hT1
  refine (lintegral_mono (g := fun _ => B) fun g => ?_).trans_lt ?_
  · refine le_of_eq_of_le (tsum_congr fun n => ?_) (h _ (hδ0 g))
    simp only [hδz]
  · rw [setLIntegral_const]
    exact ENNReal.mul_lt_top hB.lt_top h1.lt_top

end GlobalTheory.FinVolGL
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LawsOfSerSide
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links IsDedekindDomain NumberField Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.ExportSeries GlobalTheory.SeriesTie GlobalTheory.TwInputs GlobalTheory.TwSys GlobalTheory.TwAll GlobalTheory.SupLaw GlobalTheory.LiftLeaf
open Formalism.MainNotions.IntegralHeckeForms (TwOK ClsQ HkIdx V0 Fm0 FullRk SgJ BasisOf)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 800000

namespace GlobalTheory.TwInputs

theorem laws_of_serSide : ∀ (D : D7) (X : RealSide D) (E : IntegralHeckeForms.XD D) (Y : SerSide X E), (∀ i, D.ntw.NonzeroIndexPlace i → ∀ j b, RatRow Y.YS X.geo.v₀ Y.Z.good i j b) → Laws Y.Z.good Y.Z.rd := by
  intro D X E Y hR
  refine ⟨fun i j b => ?_, fun i j b => ?_, fun i j b => ?_, fun i hi j b => Y.Z.rat (hR i hi j b)⟩
  · exact GlobalTheory.SeriesTie.realRd_faithful D _ _ _ _ _ _ X.R X.cG Y.S Y.YS X.geo.v₀ Y.Z.ρ Y.Z.good i j b _
      (Y.Z.scalar i j b).ne X.unif X.char.models.HW (Y.Z.vec j)
      ((_root_.GlobalTheory.TwUnit.isKsForm_and_unit D X E Y).1 _ (Nat.le_add_left _ _) j.2)
  · exact GlobalTheory.SeriesTie.actRead_realRd D _ _ _ _ _ _ X.R X.cG Y.S Y.YS X.geo.v₀ Y.Z.ρ Y.Z.good i j b _
      Y.Z.pin X.unif X.char.models.HW
  · exact Y.Z.heckeRead (GlobalTheory.SeriesTie.HkRat.ratHecke_realRd D _ _ _ _ _ _ X.R X.cG Y.S Y.YS X.geo.v₀ Y.Z.ρ Y.Z.good i j b _
      Y.Z.pin (X.char.lev.mu0 j) (GlobalTheory.SplitOffS0.main Y.Z.good i _ (Y.Sb i)) Y.H.hL
      (Y.H.hs _ (Nat.le_add_left _ _) j.2) Y.reads)

end GlobalTheory.TwInputs
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LocFacOfNeg
section
open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.CuspRep GroundTheory.Global.IdeleGroup Formalism.L2.Host
open scoped ENNReal nonZeroDivisors Classical

noncomputable section

namespace GlobalTheory.RSCell

def sphZ (q : ℕ) {n : ℕ} (α : Fin n → ℂ) (ν : Fin n → ℤ) : ℂ :=
  if Antitone ν then GlobalTheory.JSW.sphW q α (fun i => (ν i).toNat) else 0

def locFac (q : ℕ) {n : ℕ} (α : Fin n → ℂ) (x : ℝ) (ν : Fin n → ℤ) : ℝ≥0∞ :=
  if Antitone ν ∧ ∀ i, 0 ≤ ν i then
    ENNReal.ofReal (‖GlobalTheory.JSW.schurAt (fun i => (ν i).toNat) α‖ ^ 2 *
      (q : ℝ) ^ (-(((∑ i, (ν i).toNat : ℕ) : ℝ) * x)))
  else 0

def cellProd {E : Type} [Field E] [NumberField E] {n : ℕ} (T : Finset (HeightOneSpectrum (𝓞 E)))
    (α : {w : HeightOneSpectrum (𝓞 E) // w ∉ T} → Fin n → ℂ) (x : ℝ)
    (ν : HeightOneSpectrum (𝓞 E) →₀ (Fin n → ℤ)) : ℝ≥0∞ :=
  ∏ w ∈ ν.support, if h : w ∈ T then 1 else locFac (Ideal.absNorm w.asIdeal) (α ⟨w, h⟩) x (ν w)

def bInt {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] {a : ℕ} (ℓ : Fin a) (F : GA E a → ℂ)
    (Φ : (Fin a → Cinf E) → ℂ) (J : (FractionalIdeal (𝓞 E)⁰ E)ˣ) (η : Fin a → Af E) (x : ℝ) (g : GA E a) : ℝ≥0∞ :=
  ‖GlobalTheory.RSTheta.rsPsi ℓ (GlobalTheory.JSW.whit F) (GlobalTheory.JSW.whit F) Φ J η g (g.val ℓ)‖ₑ *
    ENNReal.ofReal ((ideleModule E (GeneralLinearGroup.det g) : ℝ) ^ x)

theorem locFac_zero (q : ℕ) {n : ℕ} (α : Fin n → ℂ) (x : ℝ) : locFac q α x 0 = 1 := by
  have h : (fun i : Fin n => ((0 : Fin n → ℤ) i).toNat) = fun _ => 0 := funext fun _ => rfl
  rw [locFac, if_pos (show Antitone (0 : Fin n → ℤ) ∧ ∀ i, (0 : ℤ) ≤ (0 : Fin n → ℤ) i from ⟨fun _ _ _ => le_rfl, fun _ => le_rfl⟩), h]
  simp [GlobalTheory.JSW.schurAt, GlobalTheory.JSW.schur_zero]

theorem locFac_of_neg (q : ℕ) {n : ℕ} (α : Fin n → ℂ) (x : ℝ) {ν : Fin n → ℤ} {i : Fin n} (h : ν i < 0) :
    locFac q α x ν = 0 := by
  rw [locFac, if_neg fun h' => absurd (h'.2 i) (not_le.2 h)]

end GlobalTheory.RSCell
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LocalLatticeIndexCartanDecompositionEqNormPow
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef
open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.IndefR.Links
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RawLift
open Formalism.UG (IsUnifV qV IsUnramInv GU KU IsInertAt)
open Formalism.MainNotions.SchurIrreducible (IsSplit)
open GlobalTheory.LFun (IsSplitChart IsInertChart KGL)
open GlobalTheory.AdelicU

noncomputable section

namespace GlobalTheory.LocKerMod.FrameIdx

variable {K : Type} [Field K] {n : ℕ}

def colHom : (Fin n → K) →+ Matrix (Fin n) (Fin 1) K where
  toFun y := fun i _ => y i
  map_zero' := rfl
  map_add' _ _ := rfl

theorem colHom_injective : Function.Injective (colHom (K := K) (n := n)) :=
  fun x y h => funext fun i => congrFun (congrFun h i) 0

@[simp] theorem colHom_apply (y : Fin n → K) (i : Fin n) (j : Fin 1) : colHom y i j = y i := rfl

theorem colHom_mulVec (P : Matrix (Fin n) (Fin n) K) (y : Fin n → K) :
    colHom (P *ᵥ y) = GlobalTheory.SplitIdx.mulL (n := 1) P (colHom y) := by
  ext i j
  simp only [GlobalTheory.SplitIdx.mulL, AddMonoidHom.mk'_apply, colHom_apply, Matrix.mul_apply, Matrix.mulVec, dotProduct]

theorem mulL_one : GlobalTheory.SplitIdx.mulL (n := 1) (1 : Matrix (Fin n) (Fin n) K) = AddMonoidHom.id _ := by
  ext y : 1
  simp [GlobalTheory.SplitIdx.mulL]

end GlobalTheory.LocKerMod.FrameIdx


open GlobalTheory.LocKerMod.FrameIdx in
theorem GlobalTheory.LocKerMod.FrameIdx.idxAt_eq_pow : ∀ (D : D7) (T : HSp D) (v : HeightOneSpectrum (𝓞 D.host.F)) (w : HeightOneSpectrum (𝓞 D.host.E)) (h : w.under (𝓞 D.host.F) = v) (a : GL (Fin T.rank) (w.adicCompletion D.host.E)), GlobalTheory.LFun.IsFrameAt w (frameLat T) a → ∀ ϖ, IsUnifV D.host.E w ϖ → ∀ (d : Fin T.rank → ℤ) (t : GL (Fin T.rank) (w.adicCompletion D.host.E)), t.1 = Matrix.diagonal (fun i => ϖ ^ d i) → ∀ k₁ ∈ KGL w (n := T.rank), ∀ k₂ ∈ KGL w (n := T.rank), ∀ g : GlobalTheory.FinZeta.Gv T v, GlobalTheory.LFun.locMat D.sp.cm.sig T.gram h g = a * (k₁ * t * k₂) * a⁻¹ → GlobalTheory.LocKerMod.idxAt T w h g = qV D.host.E w ^ (∑ i, max (d i) 0).toNat := by
  intro D T v w h a ha ϖ hϖ d t ht k₁ hk₁ k₂ hk₂ g hg
  set k : GL (Fin T.rank) (w.adicCompletion D.host.E) := k₁ * t * k₂ with hk
  set Lw := (GlobalTheory.LFun.latAt w (frameLat T)).toAddSubgroup with hLw
  set M := GlobalTheory.SplitIdx.intMat D.host.E w T.rank 1 with hM
  let Φ : (Fin T.rank → w.adicCompletion D.host.E) →+ Matrix (Fin T.rank) (Fin 1) (w.adicCompletion D.host.E) :=
    colHom.comp (a⁻¹ : GL (Fin T.rank) (w.adicCompletion D.host.E)).1.mulVecLin.toAddMonoidHom
  have hΦ : Function.Injective Φ := by
    intro x y hxy
    have h1 : (a⁻¹ : GL (Fin T.rank) (w.adicCompletion D.host.E)).1 *ᵥ x =
        (a⁻¹ : GL (Fin T.rank) (w.adicCompletion D.host.E)).1 *ᵥ y := colHom_injective hxy
    have e := congrArg (fun z => a.1 *ᵥ z) h1
    simp only [Matrix.mulVec_mulVec] at e
    rwa [← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.one_mulVec, Matrix.one_mulVec] at e
  have hA : Lw.map Φ = M := by
    ext Y
    rw [AddSubgroup.mem_map]
    constructor
    · rintro ⟨x, hx, rfl⟩ i j
      have hx' : a.1 *ᵥ ((a⁻¹ : GL (Fin T.rank) (w.adicCompletion D.host.E)).1 *ᵥ x) ∈ GlobalTheory.LFun.latAt w (frameLat T) := by
        rw [Matrix.mulVec_mulVec, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.one_mulVec]; exact hx
      exact (ha _).2 hx' i
    · intro hY
      refine ⟨a.1 *ᵥ (fun i => Y i 0), (ha _).1 (fun i => hY i 0), ?_⟩
      refine Matrix.ext fun i j => ?_
      have hj : j = 0 := Subsingleton.elim _ _
      subst hj
      show colHom ((a⁻¹ : GL (Fin T.rank) (w.adicCompletion D.host.E)).1 *ᵥ (a.1 *ᵥ fun i => Y i 0)) i 0 = Y i 0
      rw [Matrix.mulVec_mulVec, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.one_mulVec]
      rfl
  have hB : (Lw.map (GlobalTheory.LFun.locMat D.sp.cm.sig T.gram h g).1.mulVecLin.toAddMonoidHom).map Φ =
      M.map (GlobalTheory.SplitIdx.mulL (n := 1) k.1) := by
    rw [← hA, AddSubgroup.map_map, AddSubgroup.map_map]
    congr 1
    refine AddMonoidHom.ext fun x => ?_
    show colHom ((a⁻¹ : GL (Fin T.rank) (w.adicCompletion D.host.E)).1 *ᵥ
        ((GlobalTheory.LFun.locMat D.sp.cm.sig T.gram h g).1 *ᵥ x)) =
      GlobalTheory.SplitIdx.mulL (n := 1) k.1 (colHom ((a⁻¹ : GL (Fin T.rank) (w.adicCompletion D.host.E)).1 *ᵥ x))
    rw [← colHom_mulVec, hg, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, ← Units.val_mul, ← Units.val_mul]
    congr 2
    group
  have step1 : GlobalTheory.LocKerMod.idxAt T w h g = (M.map (GlobalTheory.SplitIdx.mulL (n := 1) k.1)).relIndex M := by
    unfold GlobalTheory.LocKerMod.idxAt
    rw [← AddSubgroup.relIndex_map_map_of_injective _ _ hΦ, hB, hA]
  have hinv : (M.map (GlobalTheory.SplitIdx.mulL (n := 1) k.1)).map (GlobalTheory.SplitIdx.mulL (n := 1) (k⁻¹).1) = M := by
    rw [AddSubgroup.map_map, ← GlobalTheory.SplitIdx.LocIndex.mulL_mul, ← Units.val_mul, inv_mul_cancel, Units.val_one,
      mulL_one, AddSubgroup.map_id]
  have hinj : Function.Injective (GlobalTheory.SplitIdx.mulL (n := 1) (k⁻¹).1) := by
    intro x y hxy
    have e := congrArg (GlobalTheory.SplitIdx.mulL (n := 1) k.1) hxy
    simpa [GlobalTheory.SplitIdx.mulL, ← Matrix.mul_assoc, ← Units.val_mul] using e
  have hϖ0 : ϖ ≠ 0 := by
    rintro rfl
    have hv : Valued.v (0 : w.adicCompletion D.host.E) = _ := hϖ
    rw [map_zero] at hv
    exact WithZero.coe_ne_zero hv.symm
  have ht' : (t⁻¹).1 = Matrix.diagonal (fun i => ϖ ^ (-d i)) := by
    have e1 : t.1 * Matrix.diagonal (fun i => ϖ ^ (-d i)) = 1 := by
      rw [ht, Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
      congr 1; funext i
      rw [← zpow_add₀ hϖ0, add_neg_cancel, zpow_zero]
    calc (t⁻¹).1 = (t⁻¹).1 * (t.1 * Matrix.diagonal (fun i => ϖ ^ (-d i))) := by rw [e1, Matrix.mul_one]
      _ = _ := by rw [← Matrix.mul_assoc, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.one_mul]
  have hkinv : k⁻¹ = k₂⁻¹ * t⁻¹ * k₁⁻¹ := by rw [hk]; group
  rw [step1, ← AddSubgroup.relIndex_map_map_of_injective _ _ hinj, hinv, hkinv,
    GlobalTheory.SplitIdx.LocIndex.relIndex_intMat w T.rank 1 ϖ hϖ (fun i => -d i) t⁻¹ ht' k₂⁻¹ (inv_mem hk₂)
      k₁⁻¹ (inv_mem hk₁)]
  simp
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MapVVSymmMapVV
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.ExportSeries GlobalTheory.ConjTwist

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.CoefLatConj

open MvPolynomial GlobalTheory.SeriesTie.Scale

variable {D : D7} {n : ℕ}

def polLat {K : Type} [Field K] [NumberField K] (σ : K →+* ℂ) (emb : D.what₂.Tau → (D.host.E →+* K)) (O : Subring ℂ)
    (lam : D.what₂.Tau → DomWeight n) (M : Submodule (𝓞 D.host.E) (Fin n → D.host.E)) : Submodule O (VV ℂ lam) :=
  Submodule.span O {y | ∃ F ∈ nabAtr emb lam M, y = GlobalTheory.CoefModel.mapVV σ lam F}

theorem coefLatFn_eq {K : Type} [Field K] [NumberField K] (σ : K →+* ℂ) (emb : D.what₂.Tau → (D.host.E →+* K))
    (O : Subring ℂ) (lam : D.what₂.Tau → DomWeight n) (M : Submodule (𝓞 D.host.E) (Fin n → D.host.E)) :
    coefLatFn σ emb O lam M = (polLat σ emb O lam M).map ((coefLin lam).restrictScalars O) := by
  unfold coefLatFn polLat
  rw [Submodule.map_span]
  congr 1
  ext φ
  constructor
  · rintro ⟨F, hF, rfl⟩
    exact ⟨_, ⟨F, hF, rfl⟩, coefFn_map σ lam _⟩
  · rintro ⟨_, ⟨F, hF, rfl⟩, rfl⟩
    exact ⟨F, hF, coefFn_map σ lam _⟩

theorem polLat_conj {K : Type} [Field K] [NumberField K] {σ : K →+* ℂ} {emb : D.what₂.Tau → (D.host.E →+* K)}
    {O O' : Subring ℂ} {lam : D.what₂.Tau → DomWeight n} {M : Submodule (𝓞 D.host.E) (Fin n → D.host.E)} (τ : ℂ ≃+* ℂ)
    (hτ : ∀ a : K, τ (σ a) = σ a) (hO : ∀ a ∈ O, τ a ∈ O') {y : VV ℂ lam} (hy : y ∈ polLat σ emb O lam M) :
    GlobalTheory.CoefModel.mapVV (τ : ℂ →+* ℂ) lam y ∈ polLat σ emb O' lam M := by
  induction hy using Submodule.span_induction with
  | mem _ h =>
    obtain ⟨F, hF, rfl⟩ := h
    refine Submodule.subset_span ⟨F, hF, Subtype.ext ?_⟩
    change MvPolynomial.map (τ : ℂ →+* ℂ) (MvPolynomial.map σ F.1) = MvPolynomial.map σ F.1
    rw [MvPolynomial.map_map, show (τ : ℂ →+* ℂ).comp σ = σ from RingHom.ext hτ]
  | zero => rw [map_zero]; exact zero_mem _
  | add _ _ _ _ h1 h2 => rw [map_add]; exact add_mem h1 h2
  | smul a y _ h1 =>
    have e : GlobalTheory.CoefModel.mapVV (τ : ℂ →+* ℂ) lam (a • y) = (⟨τ a, hO a a.2⟩ : O') • GlobalTheory.CoefModel.mapVV (τ : ℂ →+* ℂ) lam y := by
      rw [Subring.smul_def, Subring.smul_def, map_smulₛₗ]
      rfl
    rw [e]
    exact Submodule.smul_mem _ _ h1

theorem mapVV_symm_mapVV (lam : D.what₂.Tau → DomWeight n) (τ : ℂ ≃+* ℂ) (y : VV ℂ lam) :
    GlobalTheory.CoefModel.mapVV (τ.symm : ℂ →+* ℂ) lam (GlobalTheory.CoefModel.mapVV (τ : ℂ →+* ℂ) lam y) = y := by
  refine Subtype.ext ?_
  change MvPolynomial.map (τ.symm : ℂ →+* ℂ) (MvPolynomial.map (τ : ℂ →+* ℂ) y.1) = y.1
  rw [MvPolynomial.map_map]
  have : (τ.symm : ℂ →+* ℂ).comp (τ : ℂ →+* ℂ) = RingHom.id ℂ := RingHom.ext fun a => τ.symm_apply_apply a
  rw [this, MvPolynomial.map_id]

section Base

variable {i : Fin D.R.m} {B : Base (Vc D i) (Wc D i)}

theorem pq_le (hB : B.Good) (τ : D.what₂.Tau) : B.w.p τ + B.w.q τ ≤ (Wc D i).rank := by
  obtain ⟨e, -⟩ := hB.sigOK (tauE D τ)
  rw [← hB.sig τ] at e
  have := Fintype.card_congr e
  simp only [Fintype.card_fin, Fintype.card_sum] at this
  omega

variable (Φ : VsV D i ℂ →ₗ[ℂ] PolF D (Wc D i).rank (Vc D i).rank) {κ : ℂ}

theorem mem_coefLat_iff (hlam : B.w.lam = lamV D i) (hval : ∀ x, Φ x ∈ B.valSpace)
    (hκ : ∀ x : VsV D i ℂ, harmFn (Wc D i).rank B.w B.F.BS (Φ x) =
      κ • coefFn (RingHom.id ℂ) (lamV D i) (x : Pol ℂ D.what₂.Tau (Vc D i).rank))
    {K : Type} [Field K] [NumberField K] (σ : K →+* ℂ) (emb : D.what₂.Tau → (D.host.E →+* K)) (O : Subring ℂ)
    (h : Bridge.Gf (Vc D i)) (x : VsV D i ℂ) :
    Φ x ∈ B.coefLat σ emb O h ↔ κ • x ∈ polLat σ emb O (lamV D i) (B.latAt h) := by
  show Φ x ∈ harmLat σ emb O _ B.w B.F.BS (B.latAt h) ↔ _
  rw [mem_harmLat, hlam, coefLatFn_eq, Submodule.mem_map]
  constructor
  · rintro ⟨-, y, hy, he⟩
    have e : coefLin (lamV D i) y = coefLin (lamV D i) (κ • x) := by
      rw [map_smul]
      exact he.trans (hκ x)
    exact coefLin_injective _ e ▸ hy
  · intro hx
    refine ⟨hval x, κ • x, hx, ?_⟩
    change coefLin (lamV D i) (κ • x) = _
    rw [map_smul, hκ]
    rfl

theorem existsUnique_eq (hB : B.Good) (hlam : B.w.lam = lamV D i) (hκ0 : κ ≠ 0) (hval : ∀ x, Φ x ∈ B.valSpace)
    (hκ : ∀ x : VsV D i ℂ, harmFn (Wc D i).rank B.w B.F.BS (Φ x) =
      κ • coefFn (RingHom.id ℂ) (lamV D i) (x : Pol ℂ D.what₂.Tau (Vc D i).rank)) :
    ∀ P ∈ B.valSpace, ∃! x : VsV D i ℂ, P = Φ x := by
  intro P hP
  have h1 : harmFn (Wc D i).rank B.w B.F.BS P ∈ (harm (Wc D i).rank B.w B.F.BS).map (harmFn (Wc D i).rank B.w B.F.BS) :=
    Submodule.mem_map_of_mem hP
  rw [GlobalTheory.T.fockHarmonicValueSpace_map_eq_dualWeylModuleFunctions D _ _ B.w B.F.BS hB.wt (pq_le hB), hlam] at h1
  have hs : Submodule.span ℂ {φ | ∃ F : VV ℂ (lamV D i), φ = coefFn (RingHom.id ℂ) (lamV D i) (F : Pol ℂ D.what₂.Tau (Vc D i).rank)}
      ≤ LinearMap.range (coefLin (lamV D i)) :=
    Submodule.span_le.2 (by rintro _ ⟨F, rfl⟩; exact ⟨F, rfl⟩)
  obtain ⟨y, hy⟩ := hs h1
  have hy' : coefLin (lamV D i) y = harmFn (Wc D i).rank B.w B.F.BS P := hy
  have hv : ∀ x, harmFn (Wc D i).rank B.w B.F.BS (Φ x) = κ • coefLin (lamV D i) x := hκ
  refine ⟨κ⁻¹ • y, ?_, fun x hx => ?_⟩
  · have e : harmFn (Wc D i).rank B.w B.F.BS (Φ (κ⁻¹ • y) - P) = 0 := by
      rw [map_sub, hv, map_smul, smul_smul, mul_inv_cancel₀ hκ0, one_smul, hy', sub_self]
    exact (sub_eq_zero.1 (_root_.GlobalTheory.ExportSeries.HarmInj.harm_inj D _ _ B.w B.F.BS hB.wt (pq_le hB) _ (sub_mem (hval _) hP) e)).symm
  · refine coefLin_injective (lamV D i) ?_
    have e := hv x
    rw [← hx, ← hy'] at e
    rw [map_smul, e, smul_smul, inv_mul_cancel₀ hκ0, one_smul]

theorem conj_mem_iff (hlam : B.w.lam = lamV D i) (hκ0 : κ ≠ 0) (hval : ∀ x, Φ x ∈ B.valSpace)
    (hκ : ∀ x : VsV D i ℂ, harmFn (Wc D i).rank B.w B.F.BS (Φ x) =
      κ • coefFn (RingHom.id ℂ) (lamV D i) (x : Pol ℂ D.what₂.Tau (Vc D i).rank))
    {K : Type} [Field K] [NumberField K] (σ : K →+* ℂ) (emb : D.what₂.Tau → (D.host.E →+* K)) (O : Subring ℂ)
    (τ : ℂ ≃+* ℂ) (hτ : ∀ a : K, τ (σ a) = σ a) (h : Bridge.Gf (Vc D i)) {x x' : VsV D i ℂ} (hx : ConjVec i τ x x') :
    Φ x ∈ B.coefLat σ emb O h ↔ Φ ((τ κ / κ) • x') ∈ B.coefLat σ emb (O.map (τ : ℂ →+* ℂ)) h := by
  rw [mem_coefLat_iff Φ hlam hval hκ, mem_coefLat_iff Φ hlam hval hκ]
  have hx' : x' = GlobalTheory.CoefModel.mapVV (τ : ℂ →+* ℂ) (lamV D i) x := Subtype.ext hx
  have e : κ • ((τ κ / κ) • x') = GlobalTheory.CoefModel.mapVV (τ : ℂ →+* ℂ) (lamV D i) (κ • x) := by
    rw [smul_smul, mul_div_cancel₀ _ hκ0, map_smulₛₗ, hx']
    rfl
  rw [e]
  constructor
  · exact polLat_conj τ hτ fun a ha => Subring.mem_map.2 ⟨a, ha, rfl⟩
  · intro h'
    have hτ' : ∀ a : K, τ.symm (σ a) = σ a := fun a => by rw [τ.symm_apply_eq, hτ]
    have := polLat_conj τ.symm hτ' (fun a ha => by
      obtain ⟨b, hb, rfl⟩ := Subring.mem_map.1 ha
      simpa using hb) h'
    rwa [mapVV_symm_mapVV] at this

theorem coefLat_eq_span (hB : B.Good) (hlam : B.w.lam = lamV D i) (hκ0 : κ ≠ 0) (hval : ∀ x, Φ x ∈ B.valSpace)
    (hκ : ∀ x : VsV D i ℂ, harmFn (Wc D i).rank B.w B.F.BS (Φ x) =
      κ • coefFn (RingHom.id ℂ) (lamV D i) (x : Pol ℂ D.what₂.Tau (Vc D i).rank))
    {K : Type} [Field K] [NumberField K] (σ : K →+* ℂ) (emb : D.what₂.Tau → (D.host.E →+* K)) (O : Subring ℂ)
    (h : Bridge.Gf (Vc D i)) :
    B.coefLat σ emb O h = Submodule.span O
      {P | ∃ F ∈ nabAtr emb (lamV D i) (B.latAt h), P = Φ (κ⁻¹ • GlobalTheory.CoefModel.mapVV σ (lamV D i) F)} := by
  let Ψ : VsV D i ℂ →ₗ[O] PolF D (Wc D i).rank (Vc D i).rank := (Φ ∘ₗ (κ⁻¹ • LinearMap.id)).restrictScalars O
  have hΨ : ∀ y, Ψ y = Φ (κ⁻¹ • y) := fun _ => rfl
  have e : B.coefLat σ emb O h = (polLat σ emb O (lamV D i) (B.latAt h)).map Ψ := by
    ext P
    constructor
    · intro hP
      obtain ⟨x, rfl, -⟩ := existsUnique_eq Φ hB hlam hκ0 hval hκ P (Submodule.mem_inf.1 hP).1
      refine ⟨κ • x, (mem_coefLat_iff Φ hlam hval hκ σ emb O h x).1 hP, ?_⟩
      rw [hΨ, smul_smul, inv_mul_cancel₀ hκ0, one_smul]
    · rintro ⟨y, hy, rfl⟩
      rw [hΨ, mem_coefLat_iff Φ hlam hval hκ, smul_smul, mul_inv_cancel₀ hκ0, one_smul]
      exact hy
  rw [e, polLat, Submodule.map_span]
  congr 1
  ext P
  constructor
  · rintro ⟨_, ⟨F, hF, rfl⟩, rfl⟩
    exact ⟨F, hF, rfl⟩
  · rintro ⟨F, hF, rfl⟩
    exact ⟨_, ⟨F, hF, rfl⟩, rfl⟩

end Base

end GlobalTheory.CoefLatConj
end
end

