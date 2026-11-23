module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0766
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IdempotentMulEqZeroOfOrthogonal
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0025
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.MemHomLatticeIffIntegralMatrixSplitChart
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ParahoricLevelLiftsExist
public import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.ThetaClassSumDominantWeightIsCuspForm
public import Development.AbelianVarietyTheory.Proofs.FormalGroupCharts.Bundle0038
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsSecOfMoveInv
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0765
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OscillatorModelValuesThird
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsRepsOfFiniteIndex
public import Formalism.LocalToGlobal.Divisibility.DefGroupLemmas
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0767
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1220
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0799
public import Formalism.LocalToGlobal.IndefiniteReal.LinksDefs
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0027
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.SupportedSubgroupSplitCommutePrimeIdempotents
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0288
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsFinitePlaceIdempotentBaseChangeAdeles
public import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0300
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0002
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.ThetaLetterEquivConjugate
public import Development.AbelianVarietyTheory.Definitions.ThetaValues.ExistsMemRowHighestTotalDegreeEqTwo
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0062

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MemCompletedLatticeOfFrameMatrixIntegral
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum IsDedekindDomain NumberField Matrix GlobalTheory.ExportSeries
open Formalism.IndefR.Links (PolF)
open Classical
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 800000

noncomputable section

namespace GlobalTheory.IntHalfLat

open GlobalTheory.AdelicLatMove

variable {D : D7}

theorem hatSelfDual {V : HSp D} {Λ : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E)} (hΛ : IsSelfDualC V Λ) :
    GlobalTheory.ParahoricLift.HatSelfDual D.sp.cm.sig V.gram Λ := by
  obtain ⟨-, -, -, -, hcc, -, -, hG, hdet, -⟩ := GlobalTheory.Member.latHat_eq_hat_and_gram D V
  have h1 : ∀ s ∈ Formalism.L2.Herm.intAf D.host.F D.host.E,
      Formalism.UG.sigR D.sp.cm.sig (Formalism.L2.Herm.Af D.host.F) s ∈ Formalism.L2.Herm.intAf D.host.F D.host.E :=
    fun _ h => Formalism.UG.P.csDual_sig_mem D.sp.cm.sig h
  have h2 : ∀ z, z ∈ GlobalTheory.AdLat.hat1 D.host.F
      ((1 : FractionalIdeal (nonZeroDivisors (𝓞 D.host.E)) D.host.E) : Set D.host.E) ↔
      GlobalTheory.LevSplit.swp D.host.F D.host.E z ∈ Formalism.L2.Herm.intAf D.host.F D.host.E := by
    intro z
    rw [← GlobalTheory.LatDual.integralTensorAdeles_eq_adelicCompletion_one]
    exact GlobalTheory.IdemSupport.mem_intAE_iff z
  have h3 : ∀ x, D.sp.cm.sig x = GlobalTheory.Member.cF D x := fun _ => rfl
  have hfull : ∀ (V : HSp D) (Λ : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E)),
      IsSelfDualC V Λ → Submodule.IsFullLattice D.host.E Λ := by
    intro V Λ hΛ
    haveI : Submodule.IsLattice D.host.E Λ := hΛ.1
    refine ⟨?_⟩
    obtain ⟨s, hs⟩ := hΛ.1.fg
    apply eq_top_iff.mpr
    intro y _
    let f : (Fin V.rank → D.host.E) → D.host.E := fun x =>
      ∑ i, ∑ j, star (x i) * V.gram i j * y j
    obtain ⟨a, ha⟩ := IsLocalization.exist_integer_multiples (nonZeroDivisors (𝓞 D.host.E)) s f
    have ha0 : (algebraMap (𝓞 D.host.E) D.host.E a) ≠ 0 := by
      exact (FaithfulSMul.algebraMap_injective _ _).ne (mem_nonZeroDivisors_iff_ne_zero.mp a.2)
    let P : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E) := {
      carrier := {x | ∃ b : 𝓞 D.host.E, (b : D.host.E) = (algebraMap (𝓞 D.host.E) D.host.E a) * f x}
      zero_mem' := by refine ⟨0, ?_⟩; simp [f]
      add_mem' := by
        rintro x z ⟨b, hb⟩ ⟨c, hc⟩
        refine ⟨b + c, ?_⟩
        change (b : D.host.E) + c = _
        rw [hb, hc]
        simp [f, map_add, add_mul, Finset.sum_add_distrib, mul_add]
      smul_mem' := by
        rintro c x ⟨b, hb⟩
        refine ⟨RingOfIntegers.mapRingHom (starRingEnd D.host.E) c * b, ?_⟩
        simp only [map_mul, hb, f, Pi.smul_apply, Algebra.smul_def, map_mul, RingOfIntegers.mapRingHom_apply, star_mul]
        simp only [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro i _
        apply Finset.sum_congr rfl
        intro j _
        change star (c : D.host.E) * _ = _
        ring }
    have hsP : (s : Set (Fin V.rank → D.host.E)) ⊆ P := by
      intro x hx
      obtain ⟨b, hb⟩ := ha x hx
      exact ⟨b, by simpa [Algebra.smul_def] using hb⟩
    have hy : (algebraMap (𝓞 D.host.E) D.host.E a) • y ∈ Λ := by
      apply (hΛ.2 _).2
      intro x hx
      have hxP : x ∈ P := (hs ▸ Submodule.span_le.mpr hsP) hx
      obtain ⟨b, hb⟩ := hxP
      refine ⟨b, ?_⟩
      rw [hb]
      dsimp only [f, Pi.smul_apply]
      simp only [smul_eq_mul, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro j _
      ring
    have hy' : (algebraMap (𝓞 D.host.E) D.host.E a) • y ∈ Submodule.span D.host.E (Λ : Set (Fin V.rank → D.host.E)) :=
      Submodule.subset_span hy
    have := (Submodule.span D.host.E (Λ : Set (Fin V.rank → D.host.E))).smul_mem
      (algebraMap (𝓞 D.host.E) D.host.E a)⁻¹ hy' 
    change (algebraMap (𝓞 D.host.E) D.host.E a)⁻¹ •
      ((algebraMap (𝓞 D.host.E) D.host.E a) • y) ∈ _ at this
    rw [← smul_assoc, smul_eq_mul, inv_mul_cancel₀ ha0, one_smul] at this
    exact this
  letI : Submodule.IsFullLattice D.host.E Λ := hfull V Λ hΛ
  refine GlobalTheory.ParahoricLift.hatL_selfDual_gen (GlobalTheory.Member.cF D) D.sp.cm.sig h3 V.gram Λ hΛ.1.fg Submodule.IsFullLattice.span_eq_top hcc hG hdet
    (fun v => ?_) h1 h2
  rw [hΛ.2 v]
  refine forall₂_congr fun y _ => ?_
  rw [FractionalIdeal.mem_one_iff]
  have e : (∑ a, ∑ b, v a * V.gramᵀ a b * GlobalTheory.Member.cF D (y b)) = ∑ i, ∑ j, star (y i) * V.gram i j * v j := by
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
    rw [Matrix.transpose_apply, show GlobalTheory.Member.cF D (y a) = star (y a) from rfl]
    ring
  rw [e]

theorem cF_cF (z : EAf D) : cF D (cF D z) = z := by
  induction z using TensorProduct.induction_on with
  | zero => simp only [map_zero]
  | tmul e α => rw [cF_tmul, cF_tmul, star_star]
  | add x y hx hy => simp only [map_add (f := _), hx, hy]

theorem cF_eToEAf (x : D.host.E) : cF D (eToEAf D x) = eToEAf D (star x) := rfl

theorem exists_dual {V : HSp D} {Λ : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E)} (hΛ : IsSelfDualC V Λ)
    {β : GL (Fin V.rank) (EAf D)} (hβ : IsFrame β Λ) (j : Fin V.rank) :
    ∃ s ∈ Formalism.L2.Herm.hatL (F := D.host.F) Λ, ∀ l, ∑ k, cF D (s k) * eToEAf D (V.gram k l) = (β⁻¹).val j l := by
  set Z : Matrix (Fin V.rank) (Fin V.rank) (EAf D) := (β⁻¹).val * (V.gram⁻¹).map (eToEAf D) with hZ
  have hZG : Z * V.gram.map (eToEAf D) = (β⁻¹).val := by
    rw [hZ, Matrix.mul_assoc, ← Matrix.map_mul, Matrix.nonsing_inv_mul _ (GlobalTheory.LatVac.gram_det_isUnit V),
      Matrix.map_one _ (map_zero _) (map_one _), Matrix.mul_one]
  have hrow : ∀ l, ∑ k, cF D (cF D (Z j k)) * eToEAf D (V.gram k l) = (β⁻¹).val j l := fun l => by
    rw [← hZG, Matrix.mul_apply]
    simp only [cF_cF, Matrix.map_apply]
  refine ⟨fun k => cF D (Z j k), (hatSelfDual hΛ _).2 fun z hz => ?_, hrow⟩
  have h1 : cF D (((β⁻¹).val *ᵥ z) j) ∈ Formalism.L2.Herm.intAf D.host.F D.host.E :=
    Formalism.UG.P.csDual_sig_mem D.sp.cm.sig ((hβ z).1 hz j)
  have e : cF D (((β⁻¹).val *ᵥ z) j) = ∑ a, ∑ b, cF D (z a) * eToEAf D (V.gram a b) * cF D (Z j b) := by
    set_option synthInstance.maxHeartbeats 100000 in
      rw [Matrix.mulVec, dotProduct, map_sum]
    refine Finset.sum_congr rfl fun a _ => ?_
    set_option synthInstance.maxHeartbeats 100000 in
      rw [← hrow a, map_mul, map_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl fun b _ => ?_
    rw [map_mul, cF_cF, cF_eToEAf, GlobalTheory.LatVac.gram_star]
    ring
  rw [e] at h1
  exact h1

theorem smul_mem_lat {S T : HSp D} {F : Frame S T} (hF : F.Good) {e : AE D} {P : Pl D.host.E}
    (he : Formalism.L2.NTheta.IsIdemAt e P) (hP : FractionalIdeal.count D.host.E P D.host.AA = 0) {x : WO S T}
    (hx : IsIntM (frMapO S T F.βS F.βT x)) : e • x ∈ F.lat := by
  obtain ⟨a, ha, haA⟩ := GlobalTheory.fractionalIdeal_exists_int_not_mem_of_count_eq_zero P D.host.AA
    (GlobalTheory.SplitHomLattice.ideal_ne_zero D) hP
  have ha0 : a ≠ 0 := fun h => ha (h ▸ zero_mem _)
  have ha' : (a : D.host.E) ≠ 0 := by exact_mod_cast ha0
  have hw : finPart D (e * incA D ((a : D.host.E))⁻¹) ∈ intAE D := by
    by_contra h
    exact ha ((he.2 a ha0).2 h)
  choose s hs hs' using exists_dual hF.sdS hF.frS
  set Y : Matrix (Fin T.rank) (Fin S.rank) (EAf D) := x.map (toEAf D) * F.βS.val with hY
  have ht : ∀ j, (fun i => Y i j) ∈ Formalism.L2.Herm.hatL (F := D.host.F) F.ΛT := fun j => by
    refine (hF.frT _).2 fun i => ?_
    have e1 : ((F.βT⁻¹).val *ᵥ fun i => Y i j) i = frMapO S T F.βS F.βT x i j := by
      rw [frMapO, Matrix.mul_assoc]
      rfl
    rw [e1]
    exact hx i j
  have hU := GlobalTheory.LatticeStable.smul_mem_latO D S T _ _ _ _ hw _
    (sum_mem fun j (_ : j ∈ Finset.univ) => rankOne_mem_latO S T F.ΛS F.ΛT (a : D.host.E) haA (s j) (hs j) _ (ht j))
  convert hU using 1
  ext i l
  have hYZ : ∑ j, Y i j * (F.βS⁻¹).val j l = toEAf D (x i l) := by
    rw [← Matrix.mul_apply, hY, Matrix.mul_assoc, Units.mul_inv, Matrix.mul_one, Matrix.map_apply]
  have hsum : (∑ j, rankOne S T (a : D.host.E) (s j) fun i => Y i j) i l =
      incA D (a : D.host.E) * x i l * finEmb D 1 := by
    set_option synthInstance.maxHeartbeats 100000 in
      rw [Matrix.sum_apply, ← finEmb_mul, mul_one, map_mul, toEAf_incA, ← hYZ, Finset.mul_sum, map_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [rankOne, Matrix.of_apply, hs' j l, mul_assoc]
  have h1 : e * finEmb D 1 = e := GlobalTheory.PlaceDatum.mul_pair_one (GlobalTheory.SplitScalar.infPart_splitIdem he.1)
  have h2 : incA D ((a : D.host.E))⁻¹ * incA D (a : D.host.E) = 1 := by
    rw [← map_mul, inv_mul_cancel₀ ha', map_one]
  rw [Matrix.smul_apply, Matrix.smul_apply, smul_eq_mul, smul_eq_mul, hsum]
  linear_combination (-(x i l)) * h1 - (e * x i l * finEmb D 1) * h2

theorem mem_lat_of_frMapO_int : ∀ {D : D7} {S T : HSp D} {F : Frame S T}, F.Good → ∀ {R : Finset (Pl D.host.E)},
    PlacesOK ∅ R → ∀ {x : WO S T}, IsHalf (idem R) x → IsIntM (frMapO S T F.βS F.βT x) → x ∈ F.lat := by
  intro D S T F hF R hR x hx hi
  have e : x = ∑ PP ∈ R, idemAt PP • x := by
    rw [← Finset.sum_smul]
    exact (Matrix.ext fun i j => hx i j).symm
  rw [e]
  refine sum_mem fun PP hPP => ?_
  obtain ⟨P, -, hRP, hP⟩ := hR.split
  exact smul_mem_lat hF (hP.isIdemAt (hRP hPP)) (hR.prime PP (Or.inr hPP) PP (Or.inl rfl)) hi

end GlobalTheory.IntHalfLat

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MemCuspOfThetaSum
section
open AlgebraicGeometry CategoryTheory NumberField Matrix Complex
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding Level
open GlobalTheory.SW hiding Level
open Formalism.L2.Pj GlobalTheory.Dict GlobalTheory.ClsVal
open scoped Classical

namespace GlobalTheory.ThetaSumDescent

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Geo.Tor.Level H}
  {Xo : Moduli Dw l} {c : Coeff l} {n : ℕ}

noncomputable def evHom {S : Type} [CommRing S] [_root_.IsReduced S] [Algebra c.F S] (y : FrPt Xo c S) : Rul Xo c →+* S where
  toFun f := evR Xo c f y
  map_one' := evalAt_one _ _ y
    (GlobalTheory.Frames.allTest_of_secBaseChange GlobalTheory.firstFiveLaws.1.secBaseChange E H Dw l Xo c S y)
  map_mul' f f' := evalAt_mul _ _ f f' y
  map_zero' := evalAt_zero _ _ y
  map_add' f f' := evalAt_add _ _ f f' y

noncomputable def secZero (Xo : Moduli Dw l) (c : Coeff l) : Subring (Rul Xo c) :=
  { (sec Xo c 0 0).toAddSubgroup with
    one_mem' := ⟨fun _ _ φ _ _ _ => (map_one φ).symm, fun p t _ _ _ => by
      have h0 : wchar (S := p.R) (ex Dw 0 0) t = 1 := Finset.prod_eq_one fun i _ => by cases i <;> exact pow_zero _
      rw [h0, one_mul]
      rfl⟩
    mul_mem' := fun ha hb => by simpa using sec_mul Xo c 0 0 0 0 ha hb }

theorem cases_of_pow_succ {z : ℂ} {e : ℕ} (he : 0 < e) (hz : z ^ (e + 1) = z) :
    ‖z + 1 - z ^ e‖ = 1 ∧ ‖1 - (z ^ e + z ^ e)‖ = 1 := by
  by_cases h0 : z = 0
  · simp [h0, he.ne']
  · have h1 : z ^ e = 1 := mul_right_cancel₀ h0 (by rw [← pow_succ, hz, one_mul])
    have h2 : ‖z‖ = 1 := (pow_eq_one_iff_of_nonneg (norm_nonneg z) he.ne').1 (by rw [← norm_pow, h1, norm_one])
    rw [h1]
    norm_num [h2]

theorem evR_eq_of_marked_pow [inst : Algebra c.F ℂ] (hσ : GoodEmb c (algebraMap c.F ℂ)) (hA : l.A = 1) {f : Rul Xo c}
    (hf : f ∈ sec Xo c 0 0) {m : ℕ} (hm0 : 0 < m) (hfm : f ^ (m + 1) = f) {r g : ℕ} {X : Data E r}
    {bas : (Fin g ⊕ Fin g → ℤ) ≃ₗ[ℤ] X.Λ} {idx : Fin g ≃ X.Ψ × Fin r} {e : Fin g ≃ Lt1 Dw} {L : Lt E r} (hr : 1 ≤ r)
    (hs : IsSympl X bas) {mk : Dw.La →ₗ[𝓞 E] (Fin r → E)} (hm : ∀ a, mk a ∈ L) {x x' : Frame X.Ψ r} (hx : x ∈ X.dom)
    (hx' : x' ∈ X.dom) {y y' : FrPt Xo c ℂ} (A : AnFib X bas idx e x L y) (A' : AnFib X bas idx e x' L y')
    (hk : A.Marked mk) (hk' : A'.Marked mk) : evR Xo c f y = evR Xo c f y' := by
  obtain ⟨σ, rfl⟩ : ∃ σ : c.F →+* ℂ, inst = σ.toAlgebra := ⟨algebraMap c.F ℂ, Algebra.algebra_ext _ _ fun _ => rfl⟩
  letI : Algebra c.F ℂ := σ.toAlgebra
  have hf' : f ∈ secZero Xo c := hf
  have hz : ∀ z : FrPt Xo c ℂ, evHom z f ^ (m + 1) = evHom z f := fun z => by rw [← map_pow, hfm]
  have e1 : ∀ z : FrPt Xo c ℂ, evR Xo c (f + 1 - f ^ m) z = evHom z f + 1 - evHom z f ^ m := fun z => by
    change evHom z _ = _
    simp only [(evHom z).map_sub, (evHom z).map_add, (evHom z).map_one, (evHom z).map_pow]
  have e2 : ∀ z : FrPt Xo c ℂ, evR Xo c (1 - (f ^ m + f ^ m)) z = 1 - (evHom z f ^ m + evHom z f ^ m) := fun z => by
    change evHom z _ = _
    simp only [(evHom z).map_sub, (evHom z).map_add, (evHom z).map_one, (evHom z).map_pow]
  have h1 := evR_eq_of_marked σ hσ hA (f := f + 1 - f ^ m) (show _ ∈ secZero Xo c from sub_mem (add_mem hf' (one_mem _)) (pow_mem hf' m))
    (fun z => (congrArg norm (e1 z)).trans (cases_of_pow_succ hm0 (hz z)).1) hr hs hm x hx x' hx' y y' A A' hk hk'
  have h2 := evR_eq_of_marked σ hσ hA (f := 1 - (f ^ m + f ^ m))
    (show _ ∈ secZero Xo c from sub_mem (one_mem _) (add_mem (pow_mem hf' m) (pow_mem hf' m)))
    (fun z => (congrArg norm (e2 z)).trans (cases_of_pow_succ hm0 (hz z)).2) hr hs hm x hx x' hx' y y' A A' hk hk'
  rw [e1, e1] at h1
  rw [e2, e2] at h2
  change evHom y f = evHom y' f
  linear_combination h1 - (1 / 2 : ℂ) * h2


set_option maxHeartbeats 1000000 in
theorem mem_cusp_of_thetaSum (d : DeltaDat Xo c n) {r : ℕ} (U : ∀ σ : c.F →+* ℂ, Formalism.L2.PjFree.Unf Xo c σ r) (hr1 : 1 ≤ r)
    (hU : ∀ σ, GoodEmb c σ → Formalism.L2.PjFree.IsUnf (U σ)) (hA : l.A = 1) (hlev : d.IsLev) (hA₂ : d.l₂.A = 1)
    [StarRing (𝓞 E)] (hnab : IsNab d.Xo₂ d.c₂ d.nab₂) (Λ : GenLat E n) (N : ℕ) (hun : Λ.Unimod) (hT : Λ.TrivAt d.l₂.M)
    (hO : Λ.LevOK N d.l₂.M) (a : (E →+* ℂ) × ℕ → ℕ) (hD : Dom a n) (hL : LastPos Dw a)
    {T : Type} [Fintype T] (cs : T → Rul d.Xo₂ d.c₂) (m : ℕ) (hm : 0 < m) (w : T → (Fin n → LevQ Dw d.l₂) → c.F)
    (P : T → MvPolynomial (LtN Dw n) c.F) (hcs : ∀ t, cs t ∈ sec d.Xo₂ d.c₂ 0 0 ∧ cs t ^ (m + 1) = cs t)
    (hP : ∀ t, P t ∈ HHa Dw.mult n c.F ComplexEmbedding.conjugate (InPsi H) (fun τ i => a (τ, i)))
    (f : Rul Xo c) (hsec : f ∈ sec Xo c a n)
    (hval : ∀ (k : Type) [Field k] [IsAlgClosed k] [Algebra c.F k] [Algebra d.c₂.F k],
      (∀ x : c.F, algebraMap d.c₂.F k (d.eF x) = algebraMap c.F k x) →
      ∀ (y : FrPt Xo c k) (y₂ : FrPt d.Xo₂ d.c₂ k), FrOver d y₂ y → ∃ v : T → k,
        (∀ t, thLaValAt d.Xo₂ d.c₂ d.nab₂ (fun q => d.eF (w t q)) Λ N
          (MvPolynomial.map (d.eF : c.F →+* d.c₂.F) (P t)) y₂ (v t)) ∧
        evR Xo c f y = ∑ t, evR d.Xo₂ d.c₂ (cs t) y₂ * v t) :
    f ∈ Formalism.L2.PjFree.cusp Xo c U a n := by
  have hci := GlobalTheory.chartIndependence_unconditional
  refine (Formalism.L2.PjFree.mem_cusp Xo c U a n f).2
    ⟨hsec, fun σ hσ => Formalism.L2.PjFree.holCusp_mem_holSub _ _ fun k => ?_⟩
  have hu := hU σ hσ
  obtain ⟨W⟩ := nonempty_uw hu
  letI : Algebra c.F ℂ := σ.toAlgebra
  letI A₂ : Algebra d.c₂.F ℂ := (σ.comp (d.eF.symm : d.c₂.F →+* c.F)).toAlgebra
  have halg : ∀ t : c.F, algebraMap d.c₂.F ℂ (d.eF t) = algebraMap c.F ℂ t := fun t => by
    change σ (d.eF.symm (d.eF t)) = σ t
    rw [AlgEquiv.symm_apply_apply]
  have hcomp : (algebraMap d.c₂.F ℂ).comp (d.eF : c.F →+* d.c₂.F) = σ := RingHom.ext fun t => halg t
  have hσ₂ : GoodEmb d.c₂ (algebraMap d.c₂.F ℂ) := by
    have h1 : d.eF (IntermediateField.inclusion c.le (baseKA l).ρ) =
        IntermediateField.inclusion d.c₂.le (baseKA d.l₂).ρ := Subtype.ext rfl
    change algebraMap d.c₂.F ℂ (IntermediateField.inclusion d.c₂.le (baseKA d.l₂).ρ) = _
    rw [← h1, halg]
    exact hσ
  have hn : Even n := hD.2
  obtain ⟨-, hsd, hmk, -⟩ := uw_lattice E H Dw l Xo c σ r (U σ) hσ hu hr1 W k
  obtain ⟨Dc, hDe, hk⟩ := exists_dic E H Dw l c σ r W.g n ((U σ).X k) a W.e hσ hu.1 (hu.2.1 k).1
    (hu.2.1 k).2 hsd hD
  have hw : IsIntegral ℤ (H.w0 : E) := H.w0.isIntegral_coe
  have hw' := ShortRead.halfIntegralGenerator_add_conj_eq_one H
  have hM : 0 < d.l₂.M := lt_of_lt_of_le (by norm_num) d.l₂.three_le
  have hΛ : Λ.La ∈ Vset E n d.l₂.M := (GenLatCmp.genLat_vset E n Λ.La).2.1 _ N hM hun hT hO
  obtain ⟨v, hv⟩ :=
    (TensVac.vacua E r _ _ Dc.bas Dc.idx n Dc.sympl hn _ hw hw' _ hsd 1 _ (Base.stdL_mem_Vset n 1)).1
  obtain ⟨x₁, hx₁⟩ := (GlobalTheory.frames_isConnected E r ((U σ).X k)).nonempty
  obtain ⟨b, -, hx₀, hux₀⟩ := exists_unitFr_rmul ((U σ).X k) hx₁
  obtain ⟨A₀, hAm, -⟩ := uw_anFib E H Dw l Xo c σ r (U σ) hσ hu hr1 W k Dc.bas Dc.idx Dc.sympl
    (hDe ▸ Dc.per_eq) (hDe ▸ Dc.ty_eq) ⟨_, hx₀⟩ hux₀
  obtain ⟨z₀, hz₀⟩ := hlev.2.2.2.2.2.2.1 ℂ halg (unC (U σ) k ⟨_, hx₀⟩)
  obtain ⟨B₀, -, mk₂, hmk₂, hB₀, hover⟩ := Lift.anFib_lift E H Dw l Xo c n d halg hlev r _ _ Dc.bas Dc.idx W.e _ _
    _ A₀ Dc.sympl hx₀ hsd z₀ hz₀ _ hAm
  obtain ⟨Y, hY⟩ := (DualMark.dual_marking E H Dw d.l₂ r _ _ mk₂ _ hsd hmk₂
    (Complex.isPrimitiveRoot_exp _ hM.ne')).2.2.2.2 n N hO.1.pos
  obtain ⟨ρ, hρ, hnorm⟩ := VacNorm.norm_factor_eq E r _ _ Dc.bas Dc.idx n Dc.sympl hn _ hw hw' _ hsd v hv
  have hpt : ∀ x (hx : x ∈ ((U σ).X k).dom), IsUnitFr ((U σ).X k) x → ∃ κ : ℂ, ‖κ‖ = ρ ∧
      ∃ (A : AnFib ((U σ).X k) Dc.bas Dc.idx W.e x ((U σ).X k).Λ (unC (U σ) k ⟨x, hx⟩)) (θ : (Fin W.g → ℂ) → ℂ),
        A.Marked (W.mark k) ∧ A.Reads 1 (unC (U σ) k ⟨x, hx⟩).s θ ∧
        ∀ z : Fin n → Fin W.g → ℂ, ∏ b, θ (z b) = κ * thA ((U σ).X k) Dc.bas Dc.idx v x z := by
    intro x hx hux
    obtain ⟨A, hA, θ, hθ, hmean⟩ := uw_anFib E H Dw l Xo c σ r (U σ) hσ hu hr1 W k Dc.bas Dc.idx Dc.sympl
      (hDe ▸ Dc.per_eq) (hDe ▸ Dc.ty_eq) ⟨x, hx⟩ hux
    have hT := isTheta1_of_reads_generator E H Dw l Xo c r _ _ Dc.bas Dc.idx W.e x _ _ A Dc.sympl hx hsd θ hθ
    obtain ⟨κ, hκ⟩ := VacProd.prod_eq_mul_thA E r _ _ Dc.bas Dc.idx n Dc.sympl hn _ hw hw' _ hsd v hv x hx θ hT
    exact ⟨κ, hnorm x hx hux θ κ hT hmean hκ, A, θ, hA, hθ, hκ⟩
  choose κ hκ hpt using hpt
  obtain ⟨C, -, hCe⟩ := Const.exists_const ((U σ).X k) (Formalism.L2.PjFree.laU (U σ) a n k) ρ hρ κ hκ
  have hG := fun j => ShortRead.sb_gphi Dc.idx Dc.sympl hn hw hw' hsd hΛ hv.1 (fun q => σ (w j q)) Y
  have hth := fun j => theta_holomorphic_weight E r _ _ _ Dc.hr Dc.bas Dc.idx n Dc.sympl hn _ _ _ (hG j) _ (Dc.mem _ (hP j))
  rw [Dc.wt_eq] at hth
  have hs := hu.2.2.2.2.1 a n hD f hsec k
  let co : T → ℂ := fun j => evR d.Xo₂ d.c₂ (cs j) z₀ * algebraMap d.c₂.F ℂ
    (1⁻¹ * ((Λ.mIdx N r : d.c₂.F))⁻¹ * ((Nat.card (Fin n → LevQ Dw d.l₂) : d.c₂.F))⁻¹ * (Λ.zCard N r : d.c₂.F))
  have hrd := hCe (Formalism.L2.PjFree.rdU (U σ) f k) (fun x => ∑ j, co j * thP ((U σ).X k) Dc.hr Dc.bas Dc.idx
      (gphi ((U σ).X k) Dc.bas (H.w0 : E) Λ.La ((U σ).X k).Λ v (fun q => σ (w j q)) Y)
      (MvPolynomial.rename Dc.eL (MvPolynomial.map σ (P j))) x) hs.1
    (DifferentiableOn.fun_sum fun j _ => (hth j).1.const_mul _) (fun x hx b hb => ⟨hs.2.1 x hx b hb, by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [(hth j).2.1 x hx b hb, mul_left_comm]
      rfl⟩) (by
      intro x hx hux
      obtain ⟨A, θ, hAk, hθ, hprod⟩ := hpt x hx hux
      obtain ⟨y₂, B, hy₂, hB, hrd⟩ := Reach.exists_lift_of_reached d halg hσ₂ hlev hA hA₂ hr1 A Dc.sympl hx hsd hmk hAk
        hmk₂ hover hx₀ B₀ hz₀ hB₀
      obtain ⟨vc, hvc, hev⟩ := hval ℂ halg _ y₂ hy₂
      have hrd' : Formalism.L2.PjFree.rdU (U σ) f k x = evR Xo c f (unC (U σ) k ⟨x, hx⟩) := dif_pos hx
      rw [hrd', hev, Finset.mul_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      have h := _root_.GlobalTheory.Dict.shortValAt_eq_thP hci E H Dw d.l₂ d.Xo₂ d.c₂ r _ _ Dc.bas Dc.idx W.e x _ y₂ B Dc.sympl hx hsd _ n Dc.hr Dc.eL
        hu.1 hn (hDe ▸ Dc.dir_eq) d.nab₂ hnab θ v _ (hrd θ hθ) hv hprod mk₂ hmk₂ hB Λ.La hΛ N hO Y hY a _
        ((GlobalTheory.admissible_columns_le_and_harmonic_map_cover E H Dw l Xo c n d).2 a _ (hP j)) _ 1 (vc j) (hvc j)
      rw [h, MvPolynomial.map_map, hcomp, evR_eq_of_marked_pow hσ₂ hA₂ (hcs j).1 hm (hcs j).2 hr1 Dc.sympl hmk₂.mem hx hx₀
        B B₀ hB hB₀]
      simp only [halg, co]
      change _ * (_ * _ * thP _ _ _ _ (gphi _ _ _ _ _ _ (fun q => σ (w j q)) _) _ _) = _
      ring)
  have hwt : Formalism.L2.PjFree.laU (U σ) a n k = wtOf ((U σ).X k) Dc.hr Dc.k Dc.k' n := Dc.wt_eq.symm
  rw [hwt] at hs ⊢
  refine CuspSum.mem_SS_of_eq_sum_thP E r ((U σ).X k) W.g Dw.p Dc.hr Dc.bas Dc.idx n Dc.sympl hn Dc.k Dc.k' ?_ T
    _ _ (fun j => ShortRead.sb_smul (C * co j) (hG j)) (fun j => Dc.mem _ (hP j)) _ (fun x hx => ?_) hs.2.2
  · rcases Nat.eq_zero_or_pos Dw.p with h0 | h0
    · exact Or.inr h0
    · exact Or.inl (hk hL h0)
  · rw [hrd x hx, Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [ShortRead.theta_smul₂ Dc.hr Dc.idx Dc.sympl hn (hG j) (Dc.mem _ (hP j)) hx, mul_assoc C]

end GlobalTheory.ThetaSumDescent
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SupportedAdelicPointEqOneWhereIdempotentVanishes
section
open NumberField Matrix Complex IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Dict GlobalTheory.AdTh GlobalTheory.ClsVal
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding Level Host
open GlobalTheory.SW hiding Level IsSB
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open GlobalTheory.ExportSeries (Base Twist Weight PairRep GLR detChar detFam fockGL harm harmLat IsCoefRing finPt series idem)
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SingleDatum
set_option synthInstance.maxHeartbeats 400000
open GlobalTheory.StdAtPrime

theorem GlobalTheory.SuppOneIdentity.finPt_entry_eq_one_of_idem_zero : ∀ (D : D7) (ι : (Af D.host.F ⊗[D.host.F] D.host.E) ≃+* FiniteAdeleRing (𝓞 D.host.E) D.host.E) (V : HSp D) (e : AE D) (g : GA D V), SuppAt e V g → ∀ Q : HeightOneSpectrum (𝓞 D.host.E), ι (finPart D (e + cA D e)) Q = 0 → ∀ i j, ((Matrix.GeneralLinearGroup.map ι.toRingHom (finPt V g).1).1 i j) Q = ((1 : Matrix (Fin V.rank) (Fin V.rank) (FiniteAdeleRing (𝓞 D.host.E) D.host.E)) i j) Q := by
  intro D ι V e g hS Q hQ i j
  have hent : ∀ i j, ((finPt V g).1 : Matrix (Fin V.rank) (Fin V.rank) _) i j
      = finPart D (Formalism.L2.Theta.mt V g i j) := fun i j => rfl
  have h1 := congrArg (fun x => ι (finPart D x) Q) (hS i j)
  simp only [map_mul] at h1
  have hm : (ι (finPart D (e + cA D e)) * ι (finPart D ((Formalism.L2.Theta.mt V g - 1) i j))) Q
      = ι (finPart D (e + cA D e)) Q * ι (finPart D ((Formalism.L2.Theta.mt V g - 1) i j)) Q := rfl
  rw [hm, hQ, zero_mul] at h1
  have h2 : ι (finPart D (Formalism.L2.Theta.mt V g i j)) Q
      = ι (finPart D ((1 : Matrix (Fin V.rank) (Fin V.rank) (AE D)) i j)) Q := by
    have hs : (Formalism.L2.Theta.mt V g - 1) i j = Formalism.L2.Theta.mt V g i j - (1 : Matrix (Fin V.rank) (Fin V.rank) (AE D)) i j := rfl
    rw [hs, map_sub, map_sub] at h1
    have hsub : (ι (finPart D (Formalism.L2.Theta.mt V g i j)) - ι (finPart D ((1 : Matrix (Fin V.rank) (Fin V.rank) (AE D)) i j))) Q
        = ι (finPart D (Formalism.L2.Theta.mt V g i j)) Q - ι (finPart D ((1 : Matrix (Fin V.rank) (Fin V.rank) (AE D)) i j)) Q := rfl
    rw [hsub] at h1
    exact (sub_eq_zero.mp h1.symm)
  show ι (((finPt V g).1 : Matrix (Fin V.rank) (Fin V.rank) _) i j) Q = _
  rw [hent, h2]
  by_cases hij : i = j
  · subst hij; simp [Matrix.one_apply_eq]
  · simp [Matrix.one_apply_ne hij]
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TauPsiApply
section
open NumberField Matrix Complex IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Dict GlobalTheory.AdTh GlobalTheory.ClsVal
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding Level Host
open GlobalTheory.SW hiding Level IsSB
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open GlobalTheory.ExportSeries (Base Twist Weight PairRep GLR detChar detFam fockGL harm harmLat IsCoefRing finPt series idem)
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SingleDatum
set_option synthInstance.maxHeartbeats 400000

noncomputable section
namespace GlobalTheory.FockLetters
variable {D : D7} {H : Geo.Tor.Host D.host.E}

def tauPsi (hΨ : ∀ τ : D.host.E →+* ℂ, InPsi H τ ↔ ∃ ρ, τ = tauE D ρ) : D.what₂.Tau ≃ {τ : D.host.E →+* ℂ // InPsi H τ} :=
  Equiv.ofBijective (fun ρ => ⟨tauE D ρ, (hΨ _).2 ⟨ρ, rfl⟩⟩)
    ⟨fun _ _ h => GlobalTheory.StdRat.tauE_injective D (congrArg Subtype.val h), fun τ => by
      obtain ⟨ρ, h⟩ := (hΨ τ.1).1 τ.2
      exact ⟨ρ, Subtype.ext h.symm⟩⟩

theorem tauPsi_apply (hΨ : ∀ τ : D.host.E →+* ℂ, InPsi H τ ↔ ∃ ρ, τ = tauE D ρ) (ρ : D.what₂.Tau) :
    ((tauPsi hΨ ρ : {τ : D.host.E →+* ℂ // InPsi H τ}) : D.host.E →+* ℂ) = tauE D ρ := rfl

def fockVarEquiv (Dw : Datum H) {m n : ℕ} (hΨ : ∀ τ : D.host.E →+* ℂ, InPsi H τ ↔ ∃ ρ, τ = tauE D ρ)
    (hm : m = Dw.p + Dw.q) : FVar D m n ≃ GlobalTheory.Harm.Var {τ : D.host.E →+* ℂ // InPsi H τ} Dw.p Dw.q (Fin n) :=
  (tauPsi hΨ).prodCongr (((finCongr hm).trans finSumFinEquiv.symm).prodCongr (Equiv.refl _))

def letterEquiv (Dw : Datum H) {m n : ℕ} (hΨ : ∀ τ : D.host.E →+* ℂ, InPsi H τ ↔ ∃ ρ, τ = tauE D ρ)
    (hm : m = Dw.p + Dw.q) : LtN Dw n ≃ FVar D m n :=
  (GlobalTheory.Harm.thetaLetterEquiv Dw n).trans (fockVarEquiv Dw hΨ hm).symm

end GlobalTheory.FockLetters
end
end

