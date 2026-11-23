module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0025
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0923
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0251
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0800
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IdempotentSumSelfDualFramesBound
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0919
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0770
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0479
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.SelfDualLatticePairingDual
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsInvariantForm
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0922
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IdempotentMulEqZeroOfOrthogonal
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FrameMatricesIntegralOfMemCompletedLattice
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0058
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0034
public import Development.AbelianVarietyTheory.Definitions.ThetaValues.ExistsRootNotMem
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1656
public import Formalism.SharpRestriction.Divisibility.GeneratorPowers.Bundle0007
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0046
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0033
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0029
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsRhoPtOfSplitting
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0010
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.DepthZeroSupport
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0646
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0925
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0620
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0141
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0204
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IndicesPairingLengthsVanishOffTwistedPlaces
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsGoodRationalEigenformHittingCarriedPart

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AdelicCharacterFactorPrimitiveOnIdempotentSum
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.ConjTwist GlobalTheory.GalTw ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Classical
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1600000
noncomputable section

namespace GlobalTheory.IdemCharLift

theorem exists_factor {M ι : Type} [AddCommGroup M] (k : ι → Type) [∀ i, AddCommGroup (k i)]
    (χ : AddChar M ℂ) (Q : Finset ι) (R : ∀ i, M →+ k i)
    (hker : ∀ m, (∀ i ∈ Q, R i m = 0) → χ m = 1)
    (hlift : ∀ Y : ∀ i, k i, ∃ m, ∀ i ∈ Q, R i m = Y i) :
    ∃ ψP : ∀ i, AddChar (k i) ℂ, ∀ m, χ m = ∏ i ∈ Q, ψP i (R i m) := by
  classical
  choose L hL using hlift
  have key : ∀ m m', (∀ i ∈ Q, R i m = R i m') → χ m = χ m' := by
    intro m m' h
    have h1 := hker (m - m') (fun i hi => by rw [map_sub, h i hi, sub_self])
    calc χ m = χ ((m - m') + m') := by rw [sub_add_cancel]
      _ = χ m' := by rw [AddChar.map_add_eq_mul, h1, one_mul]
  let ψP : ∀ i, AddChar (k i) ℂ := fun i =>
    { toFun := fun a => χ (L (Pi.single i a))
      map_zero_eq_one' := by
        rw [← AddChar.map_zero_eq_one χ]
        refine key _ _ fun j hj => ?_
        rw [hL _ j hj, map_zero, Pi.single_zero, Pi.zero_apply]
      map_add_eq_mul' := fun a b => by
        rw [← AddChar.map_add_eq_mul]
        refine key _ _ fun j hj => ?_
        rw [hL _ j hj, map_add (f := _), hL _ j hj, hL _ j hj, Pi.single_add, Pi.add_apply] }
  refine ⟨ψP, fun m => ?_⟩
  have hs : χ m = χ (∑ i ∈ Q, L (Pi.single i (R i m))) := by
    refine key _ _ fun j hj => ?_
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum, Finset.sum_congr rfl (fun i _ => hL (Pi.single i (R i m)) j hj),
      Finset.sum_eq_single j (fun i _ hij => Pi.single_eq_of_ne (Ne.symm hij) _) (fun h => absurd hj h),
      Pi.single_eq_same]
  have hprod : ∀ (s : Finset ι) (f : ι → M), χ (∑ i ∈ s, f i) = ∏ i ∈ s, χ (f i) := by
    intro s f
    refine Finset.induction_on s ?_ ?_
    · rw [Finset.sum_empty, Finset.prod_empty, AddChar.map_zero_eq_one]
    · intro a s ha ih
      rw [Finset.sum_insert ha, Finset.prod_insert ha, AddChar.map_add_eq_mul, ih]
  rw [hs, hprod]
  rfl

end GlobalTheory.IdemCharLift

namespace GlobalTheory.IdemCharLift

def supG (D : D7) (e : AE D) (ϖ : 𝓞 D.host.E) : AddSubgroup (AE D) where
  carrier := {Z | e * Z = Z ∧ toEAf D (incA D (ϖ : D.host.E) * Z) ∈ Formalism.L2.Herm.intAf D.host.F D.host.E}
  zero_mem' := ⟨mul_zero e, by rw [mul_zero, RingHom.map_zero]; exact zero_mem _⟩
  add_mem' := fun {a b} ha hb => ⟨by rw [mul_add, ha.1, hb.1], by rw [mul_add, RingHom.map_add (f := _)]; exact add_mem ha.2 hb.2⟩
  neg_mem' := fun {a} ha => ⟨by rw [mul_neg, ha.1], by rw [mul_neg, RingHom.map_neg]; exact neg_mem ha.2⟩

def resG (D : D7) (e : AE D) (ϖ : 𝓞 D.host.E) (PP : Pl D.host.E) : supG D e ϖ →+ kP PP where
  toFun m := resS D.host.F PP ⟨toEAf D (incA D (ϖ : D.host.E) * m), m.2.2⟩
  map_zero' := by
    rw [← map_zero (resS D.host.F PP)]
    exact congrArg _ (Subtype.ext (by simp))
  map_add' a b := by
    rw [← map_add (resS D.host.F PP)]
    exact congrArg _ (Subtype.ext (by simp [mul_add]))

def chiA (D : D7) (ψ : AddChar (AF D.host.F) ℂ) : AddChar (AE D) ℂ :=
  ψ.compAddMonoidHom ((Algebra.trace (AF D.host.F) (AE D)).toAddMonoidHom.comp (AddMonoidHom.mulLeft (incA D D.host.xi0)))

theorem toEAf_surj (D : D7) : Function.Surjective (toEAf D) := by
  intro z
  induction z using TensorProduct.induction_on with
  | zero => exact ⟨0, RingHom.map_zero _⟩
  | add x y hx hy =>
    obtain ⟨a, rfl⟩ := hx
    obtain ⟨b, rfl⟩ := hy
    exact ⟨a + b, RingHom.map_add _ _ _⟩
  | tmul x a => exact ⟨pairA D.host.F 0 a ⊗ₜ[D.host.F] x, rfl⟩

end GlobalTheory.IdemCharLift

namespace GlobalTheory.IdemCharLift

theorem factor_prim : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (Q : Finset (Pl D.host.E)) (e : AE D), IsIdemSum e Q → ∀ ϖ : 𝓞 D.host.E, ϖ ≠ 0 → (∀ PP ∈ Q, ϖ ∈ PP.asIdeal ∧ ϖ ∉ PP.asIdeal ^ 2) → (∀ Z : AE D, e * Z = Z → (toEAf D Z ∈ Formalism.L2.Herm.intAf D.host.F D.host.E ↔ ∀ Z' : AE D, e * Z' = Z' → toEAf D Z' ∈ Formalism.L2.Herm.intAf D.host.F D.host.E → ψ (Algebra.trace (AF D.host.F) (AE D) (incA D D.host.xi0 * (Z * Z'))) = 1)) → ∃ ψP : ∀ PP : Pl D.host.E, AddChar (kP PP) ℂ, (∀ PP ∈ Q, (ψP PP).IsPrimitive) ∧ ∀ Z : AE D, e * Z = Z → ∀ h : toEAf D (incA D (ϖ : D.host.E) * Z) ∈ Formalism.L2.Herm.intAf D.host.F D.host.E, ψ (Algebra.trace (AF D.host.F) (AE D) (incA D D.host.xi0 * Z)) = ∏ PP ∈ Q.attach, ψP PP.1 (resS D.host.F PP.1 ⟨toEAf D (incA D (ϖ : D.host.E) * Z), h⟩) := by
  intro D ψ Q e he ϖ hϖ0 hϖ H
  have hee : e * e = e := GlobalTheory.PlaceDatum.idemSum_mul_self he
  have heI : toEAf D e ∈ Formalism.L2.Herm.intAf D.host.F D.host.E :=
    GlobalTheory.LatHalfInt.toEAf_mem_of_finPart (GlobalTheory.AdIdem.idempotent_mem_intAE D _ (by rw [← RingHom.map_mul, hee]))
  obtain ⟨⟨es, hes, hsum⟩, hc⟩ := he
  have hc' : (∑ PP ∈ Q, es PP) * cA D (∑ PP ∈ Q, es PP) = 0 := hsum ▸ hc
  have hϖE : (ϖ : D.host.E) ≠ 0 := by exact_mod_cast hϖ0
  have hinv : incA D ((ϖ : D.host.E)⁻¹) * incA D (ϖ : D.host.E) = 1 := by
    rw [← map_mul, inv_mul_cancel₀ hϖE, map_one]
  have hdiv : ∀ m : supG D e ϖ, (toEAf D (m : AE D) ∈ Formalism.L2.Herm.intAf D.host.F D.host.E ↔
      ∀ PP ∈ Q, resG D e ϖ PP m = 0) := by
    intro m
    have h1 := _root_.GlobalTheory.IdemKerDiv.integral_div_iff D Q es (fun _ => ϖ) hes hc' (fun PP hP => hϖ PP hP)
      (toEAf D (incA D (ϖ : D.host.E) * m)) m.2.2
      (by rw [← hsum, ← map_mul, ← mul_assoc, mul_comm e, mul_assoc, m.2.1])
    have h2 : toEAf D (∑ PP ∈ Q, es PP * incA D ((ϖ : D.host.E)⁻¹)) * toEAf D (incA D (ϖ : D.host.E) * m) =
        toEAf D m := by
      rw [← Finset.sum_mul, ← hsum, ← map_mul]
      congr 1
      calc e * incA D ((ϖ : D.host.E)⁻¹) * (incA D (ϖ : D.host.E) * m)
          = (incA D ((ϖ : D.host.E)⁻¹) * incA D (ϖ : D.host.E)) * (e * m) := by ring
        _ = m := by rw [hinv, one_mul, m.2.1]
    rw [h2] at h1
    exact h1
  have hker : ∀ m : supG D e ϖ, (∀ PP ∈ Q, resG D e ϖ PP m = 0) →
      ((chiA D ψ).compAddMonoidHom (supG D e ϖ).subtype) m = 1 := by
    intro m hm
    have h1 := (H m m.2.1).1 ((hdiv m).2 hm) e hee heI
    rw [mul_comm (m : AE D) e, m.2.1] at h1
    exact h1
  have hlift : ∀ Y : ∀ PP : Pl D.host.E, kP PP, ∃ m : supG D e ϖ, ∀ PP ∈ Q, resG D e ϖ PP m = Y PP := by
    intro Y
    obtain ⟨N, hN, hNe, hNY⟩ := _root_.GlobalTheory.IdemResLift.exists_int_lift D Q es hes hc' Y
    obtain ⟨w, hw⟩ := toEAf_surj D N
    have hm1 : e * (e * incA D ((ϖ : D.host.E)⁻¹) * w) = e * incA D ((ϖ : D.host.E)⁻¹) * w := by
      rw [← mul_assoc, ← mul_assoc, hee]
    have hm0 : incA D (ϖ : D.host.E) * (e * incA D ((ϖ : D.host.E)⁻¹) * w) = e * w := by
      calc incA D (ϖ : D.host.E) * (e * incA D ((ϖ : D.host.E)⁻¹) * w)
          = (incA D ((ϖ : D.host.E)⁻¹) * incA D (ϖ : D.host.E)) * (e * w) := by ring
        _ = e * w := by rw [hinv, one_mul]
    have hm2 : toEAf D (incA D (ϖ : D.host.E) * (e * incA D ((ϖ : D.host.E)⁻¹) * w)) = N := by
      rw [hm0, map_mul, hw, hsum]
      exact hNe
    refine ⟨⟨_, hm1, hm2 ▸ hN⟩, fun PP hP => ?_⟩
    rw [← hNY PP hP]
    show resS D.host.F PP ⟨_, _⟩ = resS D.host.F PP ⟨N, hN⟩
    exact congrArg _ (Subtype.ext hm2)
  obtain ⟨ψP, hψP⟩ := exists_factor (fun PP : Pl D.host.E => kP PP)
    ((chiA D ψ).compAddMonoidHom (supG D e ϖ).subtype) Q (resG D e ϖ) hker hlift
  refine ⟨ψP, fun PP hP => ?_, fun Z hZ h => ?_⟩
  · haveI := PP.isMaximal
    letI := Ideal.Quotient.field PP.asIdeal
    refine AddChar.IsPrimitive.of_ne_one fun h1 => ?_
    obtain ⟨m1, hm1⟩ := hlift (Pi.single PP 1)
    have hnI : toEAf D (m1 : AE D) ∉ Formalism.L2.Herm.intAf D.host.F D.host.E := fun hI => by
      have h3 := (hdiv m1).1 hI PP hP
      rw [hm1 PP hP, Pi.single_eq_same] at h3
      exact one_ne_zero h3
    obtain ⟨Z', hZ'e, hZ'I, hne⟩ : ∃ Z' : AE D, e * Z' = Z' ∧ toEAf D Z' ∈ Formalism.L2.Herm.intAf D.host.F D.host.E ∧
        ψ (Algebra.trace (AF D.host.F) (AE D) (incA D D.host.xi0 * ((m1 : AE D) * Z'))) ≠ 1 := by
      by_contra hcon
      push_neg at hcon
      exact hnI ((H m1 m1.2.1).2 hcon)
    let m2 : supG D e ϖ := ⟨(m1 : AE D) * Z', by rw [← mul_assoc, m1.2.1],
      by rw [← mul_assoc, map_mul]; exact mul_mem m1.2.2 hZ'I⟩
    have hres : ∀ QQ : Pl D.host.E, resG D e ϖ QQ m2 =
        resG D e ϖ QQ m1 * resS D.host.F QQ ⟨toEAf D Z', hZ'I⟩ := by
      intro QQ
      show resS D.host.F QQ ⟨_, _⟩ = resS D.host.F QQ ⟨_, _⟩ * resS D.host.F QQ ⟨_, _⟩
      rw [← map_mul]
      exact congrArg _ (Subtype.ext (by
        show toEAf D (incA D (ϖ : D.host.E) * ((m1 : AE D) * Z')) = toEAf D (incA D (ϖ : D.host.E) * m1) * toEAf D Z'
        rw [← map_mul, mul_assoc]))
    have h2 := hψP m2
    rw [Finset.prod_eq_single PP (fun QQ hQ hQP => by
        rw [hres, hm1 QQ hQ, Pi.single_eq_of_ne hQP, zero_mul, AddChar.map_zero_eq_one])
      (fun h => absurd hP h), h1, AddChar.one_apply] at h2
    exact hne h2
  · exact (hψP ⟨Z, hZ, h⟩).trans (Finset.prod_attach Q (fun PP => ψP PP (resG D e ϖ PP ⟨Z, hZ, h⟩))).symm

end GlobalTheory.IdemCharLift
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AdjointConcreteThetaInjectiveReferenceTuple
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
open ReciprocityTheory.Aut Formalism.AUTREP
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.TypeRec.factG
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.IndefR.RecTie Formalism.IndefR.Lev
open scoped TensorProduct InnerProductSpace
open GlobalTheory.Mem.R3

namespace GlobalTheory.AdjInjLevel


set_option maxHeartbeats 2000000 in
theorem adjoint_eW_inj : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 I0 T : Type) (A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat3 D A3 Ks) (F : Face3 D A3) (cG : G0 R.Pg D.R.r ≃* G0g D.nd) (X0 : BaseLevelRowSide D) (Y : GlobalTheory.Mem.R3.Read (A3 := A3) R.toRealDat F.lv2 X0), GlobalTheory.Mem.R3.Pins R F cG → GlobalTheory.Mem.R3.Holds R F → ∀ (i : Fin D.R.m) (σ : D.what₂.FT), ∀ y ∈ D.what₂.isot ((i : ℕ) + 1) σ, LinearMap.adjoint (R.thG i A3.A.μ0) (Y.mj.eW i y) = 0 → y = 0 := by
  intro D G _ _ Pl0 I0 T A3 Ks _ _ _ R F cG X0 Y hP hH i σ y _ h0
  have hnP : 0 < RealDat.nP F.lv2 false := RealDat.nP_pos (F := F.lv2) false
  have hinj : Function.Injective (Y.mj.eW i) := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro d hd
    have h1 : RealDat.nP F.lv2 false * ‖d‖ ^ 2 = 0 := by rw [← Y.mj.eW_norm i d, hd]; simp
    have h2 : ‖d‖ ^ 2 = 0 := by
      rcases mul_eq_zero.1 h1 with h | h
      · exact absurd h hnP.ne'
      · exact h
    exact norm_eq_zero.1 (pow_eq_zero_iff (n := 2) (by norm_num) |>.1 h2)
  have hWS : Y.mj.eW i y ∈ R.toRealDat.WS F.lv2 false i (sg0 D A3.A) := by
    rw [hH.aux.levelW false i (sg0 D A3.A), ← Y.mj.eW_range i]
    exact LinearMap.mem_range_self _ _
  have hle : R.toRealDat.WS F.lv2 false i (sg0 D A3.A) ≤
      Submodule.comap (Tw.mkL (twAt D.what₂.embLL A3.A.v0) (R.HW i (sg0 D A3.A)).H)
        (LinearMap.range ((R.toCx3 F).w0C false i)) := by
    refine Submodule.span_le.2 ?_
    rintro _ ⟨k, rfl⟩
    exact GlobalTheory.TwParts.mk_bC_mem_range R F i k
  have h1 : Tw.mk (twAt D.what₂.embLL A3.A.v0) (Y.mj.eW i y) ∈ LinearMap.range ((R.toCx3 F).w0C false i) := hle hWS
  rw [← (hH.prim.sumW i).2] at h1
  have hsum : Y.mj.eW i y ∈ ⨆ p, R.Wp3 i p := by
    have key : ∀ w : (R.toCx3 F).W i, w ∈ (⨆ p, (R.toCx3 F).Wp i p ⊓ LinearMap.range ((R.toCx3 F).w0C false i)) →
        Tw.out (s := twAt D.what₂.embLL A3.A.v0) (E := (R.HW i (sg0 D A3.A)).H) w ∈ ⨆ p, R.Wp3 i p := by
      intro w hw
      refine Submodule.iSup_induction (motive := fun w => Tw.out (s := twAt D.what₂.embLL A3.A.v0) (E := (R.HW i (sg0 D A3.A)).H) w ∈ ⨆ p, R.Wp3 i p) _ hw
        (fun p w hw => Submodule.mem_iSup_of_mem p hw.1) (Submodule.zero_mem _) ?_
      intro a b ha hb
      rw [Tw.out_add (s := twAt D.what₂.embLL A3.A.v0) (E := (R.HW i (sg0 D A3.A)).H) a b]
      exact Submodule.add_mem _ ha hb
    exact key _ h1
  have hz := GlobalTheory.AdjointInjectiveOfParts.adjoint_inj_of_parts (R.thG i A3.A.μ0) (R.Wp3 i)
    (fun p => ((R.lam3 i A3.A.μ0 p A3.A.v0 : ℝ) : ℂ))
    (fun p => Complex.ofReal_ne_zero.2 (hH.prim.posScal.2 i A3.A.μ0 p A3.A.v0).ne')
    (fun p x hx => hH.prim.thmA i A3.A.μ0 p x hx) hsum h0
  exact hinj (hz.trans (map_zero _).symm)

end GlobalTheory.AdjInjLevel
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AdjointThetaKillsReferenceTuple
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
open ReciprocityTheory.Aut Formalism.AUTREP
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.TypeRec.factG
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.IndefR.RecTie Formalism.IndefR.Lev

noncomputable section
open scoped TensorProduct InnerProductSpace
open Formalism.L2.Rows GlobalTheory.Mem.R3

namespace GlobalTheory.Mem.ThetaRead3


set_option maxHeartbeats 4000000 in
theorem thetaP_read_plain : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 I0 T : Type) (A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat3 D A3 Ks) (F : Face3 D A3) (cG : G0 R.Pg D.R.r ≃* G0g D.nd) (X0 : BaseLevelRowSide D) (Y : Read (A3 := A3) R.toRealDat F.lv2 X0), Pins R F cG → Holds R F → ∀ (i : Fin D.R.m) (t : T) x, Y.mj.eW i (D.what₂.thetaP (Y.tup t) ((i : ℕ) + 1) (D.what₂.jMt (Y.tup t) ((i : ℕ) + 1) (Y.eMt i t x))) = R.thG i t (R.jV i t (liftForm A3.A F.P0 F.ψ0 i t x)) := by
  intro D G _ _ Pl0 I0 T A3 Ks _ _ _ R F cG X0 Y hP hH i t x
  have hE : R.toRealDat.IsThP := RealDat.thP_of_weak hP.char.base.thP hH.aux.ex
  have hM := hP.char.base.models
  have hμ : Used0 D (Y.tup t) := by
    rcases hP.char.tup.mu_used t with h | ⟨w, hw⟩
    · left
      rw [h, Y.tup0]
    · right
      refine ⟨D.plEq.symm w, ?_⟩
      rw [Y.muAt, Equiv.apply_symm_apply, hw]
  set xM := D.what₂.jMt (Y.tup t) ((i : ℕ) + 1) (Y.eMt i t x) with hxM
  set zt := R.jV i t (liftForm A3.A F.P0 F.ψ0 i t x) with hzt
  obtain ⟨w, hwM, hwK, hwW⟩ := _root_.GlobalTheory.ThetaFireLift.thetaFireL R.toRealDat F.lv2 Y.tupT Y.hm Y.hTop Y.hinj hP.char.base.lev
    hP.char.base.grp hM hE R.hv0 Y.IL (Y.tup t) hμ i xM
  have hth := Y.tied.lift.theta (Y.tup t) hμ i xM w
    (GlobalTheory.ThetaPRead.isThetaP_toLiftReal R.toRealDat F.lv2 Y.tupT Y.hm Y.hTop Y.hinj hE.thF (Y.tup t) i) hwM hwK hwW
  set u := Y.tupT (Y.tup t) with hu
  set a := Y.IL.jMt (Y.tup t) hμ i xM with ha
  set z' : (R.HV i u).H := (LinearEquiv.ofInjective (R.extV i u) (Y.hinj i u)).symm
    (Submodule.inclusion inf_le_left a) with hz'
  have hz'1 : R.extV i u z' = R.extV i t zt := by
    rw [hz', ofInjective_symm_eq]
    exact Y.mtRead i t hμ x
  have hzz : R.thF i u z' = R.thF i t zt := thF_congr R.toRealDat Y.hinj i t u (Y.tupT_tup t) zt z' hz'1
  let w' : (⨂[ℂ] τ, (R.MW i (sg0 D A3.A)).sm τ) →ₗ[ℂ] (GA D (Wc D i) → ℂ) := w
  let U : MMap (R.MW i (sg0 D A3.A)) := PiTensorProduct.lift.symm w'
  have hU : U ∈ R.Wall i (sg0 D A3.A) :=
    GlobalTheory.HeckeParts.mult_le_triv _ ((Mult.mem_multT _ _ _ _ w').1 hwM)
  have hlow : ∀ v : ∀ ρ, lowT (R.MW i (sg0 D A3.A)) ρ, U (fun ρ => v ρ) = R.thF i u z' (fun ρ => v ρ) := by
    intro v
    have e := LinearMap.congr_fun hwK (PiTensorProduct.tprod ℂ v)
    have e2 : w' (PiTensorProduct.map (fun τ => (lowT (R.MW i (sg0 D A3.A)) τ).subtype) (PiTensorProduct.tprod ℂ v)) =
        PiTensorProduct.lift (R.thF i u z')
          (PiTensorProduct.map (fun τ => (lowT (R.MW i (sg0 D A3.A)) τ).subtype) (PiTensorProduct.tprod ℂ v)) := e
    rw [PiTensorProduct.map_tprod, PiTensorProduct.lift.tprod] at e2
    exact e2
  have hw0 : U - R.thF i t zt = 0 :=
    GlobalTheory.LowTypeDetermined.eq_zero_of_lowT D _ _ (R.MW i (sg0 D A3.A)) R.θ hM.inf
      (GlobalTheory.LowTypeRestriction.lowT_ne_bot _) _ _ _ (Submodule.sub_mem _ hU (hE.thF_mem i t zt)) (fun v => by
        show U (fun ρ => v ρ) - R.thF i t zt (fun ρ => v ρ) = 0
        rw [hlow v, hzz, sub_self])
  have hUw : PiTensorProduct.lift U = w' := LinearEquiv.apply_symm_apply _ w'
  have h1 := (Y.mjRead i (D.what₂.thetaP (Y.tup t) ((i : ℕ) + 1) xM)).symm.trans hth
  change PiTensorProduct.lift _ = R.eWf i (sg0 D A3.A) ∘ₗ w' at h1
  rw [← hUw, sub_eq_zero.1 hw0, ← lift_postOn, ← hE.thG i t zt] at h1
  exact (hM.HW i (sg0 D A3.A)).1 (PiTensorProduct.lift.injective h1)

end GlobalTheory.Mem.ThetaRead3

namespace GlobalTheory.Mem.AdjLevel


set_option maxHeartbeats 4000000 in
theorem adjoint_eW_eq_zero : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 I0 T : Type) (A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat3 D A3 Ks) (F : Face3 D A3) (cG : G0 R.Pg D.R.r ≃* G0g D.nd) (X0 : BaseLevelRowSide D) (Y : GlobalTheory.Mem.R3.Read (A3 := A3) R.toRealDat F.lv2 X0), GlobalTheory.Mem.R3.Pins R F cG → GlobalTheory.Mem.R3.Holds R F → ∀ (i : Fin D.R.m) (σ : D.what₂.FT), ∀ y ∈ D.what₂.isot ((i : ℕ) + 1) σ, D.what₂.thetaT D.what₂.mu0 ((i : ℕ) + 1) y = 0 → LinearMap.adjoint (R.thG i A3.A.μ0) (Y.mj.eW i y) = 0 := by
  intro D G _ _ Pl0 I0 T A3 Ks _ _ _ R F cG X0 Y hP hH i σ y _hy hT
  have hread := GlobalTheory.Mem.ThetaRead3.thetaP_read_plain D G Pl0 I0 T A3 Ks R F cG X0 Y hP hH i A3.A.μ0
  have hT' : D.what₂.thetaT (Y.tup A3.A.μ0) ((i : ℕ) + 1) y = 0 := by rw [Y.tup0]; exact hT
  have hw : (R.HW i (sg0 D A3.A)).e (Y.mj.eW i y) ∈
      R.toRealDat.Wat i (sg0 D A3.A) (R.toRealDat.levL F.lv2 false (sg0 D A3.A)) := by
    have h0 : Y.mj.eW i y ∈ LinearMap.range (Y.mj.eW i) := ⟨y, rfl⟩
    rw [Y.mj.eW_range] at h0
    exact h0
  have ha := GlobalTheory.CarriedPart.adjoint_mem_span R F hH.ok hP.char hH.prim.unif hH.prim.gUnit hH.prim.gEquiv hH.prim.levW i _ hw
  have horth : ∀ f ∈ BlockGood.goodR (A3.A.fam.L i A3.A.μ0) (A3.A.fam.lvlA F.P0 F.ψ0),
      ⟪Y.mj.eW i y, R.thG i A3.A.μ0 (R.jV i A3.A.μ0 f)⟫_ℂ = 0 := by
    intro f hf
    rw [Formalism.IndefR.CxPass.LevelOperators.goodR_eq] at hf
    have hfl : f ∈ lvlForms (A3.A.fam.L i A3.A.μ0).S (A3.A.fam.L i A3.A.μ0).r (A3.A.fam.lvlA F.P0 F.ψ0).P
        (A3.A.fam.lvlA F.P0 F.ψ0).ψ := fun h =>
      Formalism.IndefR.CxPass.LevelOperators.opF_goodAt_type _ _ hH.ok.ok2.irr _ _ h f hf
    rw [← GlobalTheory.Mem.LiftForms.range_lvlForm] at hfl
    obtain ⟨x, rfl⟩ := hfl
    have hx : GlobalTheory.Mem.LiftForms.lvlForm (A3.A.fam.L i A3.A.μ0).S (A3.A.fam.L i A3.A.μ0).r (A3.A.fam.lvlA F.P0 F.ψ0).P
        (A3.A.fam.lvlA F.P0 F.ψ0).ψ x = liftForm A3.A F.P0 F.ψ0 i A3.A.μ0 x := rfl
    rw [hx, ← hread x, GlobalTheory.Mem.LiftForms.inner_of_norm_sq (Y.mj.eW i) (RealDat.nP_pos (F := F.lv2) false) (Y.mj.eW_norm i),
      ← LinearMap.adjoint_inner_left]
    show _ * ⟪D.what₂.thetaT (Y.tup A3.A.μ0) ((i : ℕ) + 1) y, _⟫_ℂ = 0
    rw [hT', inner_zero_left, mul_zero]
  have hall : ∀ v ∈ Submodule.span ℂ (R.jV i A3.A.μ0 '' (BlockGood.goodR (A3.A.fam.L i A3.A.μ0) (A3.A.fam.lvlA F.P0 F.ψ0) :
      Set (A3.A.fam.L i A3.A.μ0).S.Forms)), ⟪Y.mj.eW i y, R.thG i A3.A.μ0 v⟫_ℂ = 0 := by
    intro v hv
    induction hv using Submodule.span_induction with
    | mem z hz =>
      obtain ⟨f, hf, rfl⟩ := hz
      exact horth f hf
    | zero => rw [map_zero, inner_zero_right]
    | add a b _ _ ha hb => rw [map_add (f := _), inner_add_right, ha, hb, add_zero]
    | smul c a _ ha => rw [map_smul, inner_smul_right, ha, mul_zero]
  have h0 : ⟪LinearMap.adjoint (R.thG i A3.A.μ0) (Y.mj.eW i y), LinearMap.adjoint (R.thG i A3.A.μ0) (Y.mj.eW i y)⟫_ℂ = 0 := by
    rw [LinearMap.adjoint_inner_left]
    exact hall _ ha
  exact inner_self_eq_zero.1 h0

end GlobalTheory.Mem.AdjLevel

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ChosenFieldFormsProportionalOfReadings
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.FWT IsDedekindDomain NumberField Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.ExportSeries GlobalTheory.SeriesTie GlobalTheory.TwInputs GlobalTheory.ConjTwist GlobalTheory.ChoiceRead
open Formalism.MainNotions.IntegralHeckeForms (TwOK ClsQ)
open Formalism.L2.Host (embLL0)
open Formalism.IndefR.RecTie (Used0)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1600000
open GlobalTheory.PlaceRead
open GlobalTheory.HeightCounting.Up (PrN)

private theorem tensor_exists_basis_expansion {O K L M ι : Type*} [CommRing O] [IsDomain O] [Field K] [Algebra O K] [IsFractionRing O K]
    [Field L] [Algebra O L] [AddCommGroup M] [Module O M] [Module K M] [IsScalarTower O K M] [Fintype ι]
    (hinj : ∀ d : O, d ≠ 0 → algebraMap O L d ≠ 0) (v : Module.Basis ι K M) (x : L ⊗[O] M) :
    ∃ cf : ι → L, x = ∑ a, cf a ⊗ₜ v a := by
  induction x using TensorProduct.induction_on with
  | zero => exact ⟨0, by simp⟩
  | add x y hx hy =>
    obtain ⟨c, e⟩ := hx
    obtain ⟨c', e'⟩ := hy
    refine ⟨c + c', ?_⟩
    rw [e, e']
    simp [TensorProduct.add_tmul, Finset.sum_add_distrib]
  | tmul a f =>
    obtain ⟨d, hd⟩ := IsLocalization.exist_integer_multiples_of_finite (nonZeroDivisors O) fun c => v.repr f c
    choose y hy using hd
    have e : (d : O) • (a ⊗ₜ[O] f) = ∑ c, (y c • a) ⊗ₜ[O] v c := by
      rw [← TensorProduct.tmul_smul]
      conv_lhs => rw [← v.sum_repr f]
      rw [Finset.smul_sum, TensorProduct.tmul_sum]
      refine Finset.sum_congr rfl fun c _ => ?_
      rw [TensorProduct.smul_tmul, ← algebraMap_smul K (y c), hy, smul_assoc]
    have h0 := hinj d (nonZeroDivisors.coe_ne_zero d)
    refine ⟨fun c => (algebraMap O L d)⁻¹ • y c • a, ?_⟩
    rw [← algebraMap_smul L (d : O)] at e
    rw [← inv_smul_smul₀ h0 (a ⊗ₜ[O] f), e, Finset.smul_sum]
    simp only [TensorProduct.smul_tmul']

private theorem tensor_scalar_relation {O L M N ι : Type*} [CommRing O] [Field L] [Algebra O L] [AddCommGroup M] [Module O M]
    [AddCommGroup N] [Module ℂ N] [Fintype ι] (ε : L →+* ℂ) (v : ι → M) (r : M → N) (R : L ⊗[O] M →ₛₗ[ε] N)
    (hR : ∀ a f, R (a ⊗ₜ f) = ε a • r f) (hli : LinearIndependent ℂ fun c => r (v c))
    (hsp : ∀ x : L ⊗[O] M, ∃ cf : ι → L, x = ∑ a, cf a ⊗ₜ v a) (A B : L ⊗[O] M) (z : ℂ) (h : R A = z • R B) :
    (B = 0 → A = 0) ∧ (B ≠ 0 → ∃ t : L, ε t = z ∧ A = t • B) := by
  obtain ⟨α, rfl⟩ := hsp A
  have hind := Fintype.linearIndependent_iff.1 hli
  constructor
  · rintro rfl
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_zero, smul_zero, map_sum] at h
    simp only [hR] at h
    have h2 : ∀ a, α a = 0 := fun a => ε.injective ((hind _ h a).trans (map_zero _).symm)
    simp [h2]
  · obtain ⟨β, rfl⟩ := hsp B
    intro hB
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum, map_sum] at h
    simp only [hR] at h
    have h1 : ∀ a, ε (α a) - z * ε (β a) = 0 := hind (fun a => ε (α a) - z * ε (β a)) (by
      simp only [sub_smul, mul_smul, Finset.sum_sub_distrib, ← Finset.smul_sum, h, sub_self])
    have h2 : ∃ a, β a ≠ 0 := by
      by_contra hc
      push Not at hc
      exact hB (by simp [hc])
    obtain ⟨a0, ha0⟩ := h2
    have h3 : ε (β a0) ≠ 0 := (map_ne_zero ε).2 ha0
    have ht : ε (α a0 / β a0) = z := by
      rw [map_div₀, sub_eq_zero.1 (h1 a0), mul_div_cancel_right₀ _ h3]
    refine ⟨α a0 / β a0, ht, ?_⟩
    rw [Finset.smul_sum]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [TensorProduct.smul_tmul', smul_eq_mul]
    congr 1
    apply ε.injective
    rw [map_mul, ht, sub_eq_zero.1 (h1 a)]

theorem _root_.GlobalTheory.T.chosenField_forms_proportional_of_readings : ∀ (D : D7) (c : NChoice D) (w : D.what₂.places.Pl) (ρ : Setup D.ntw) (hρ : ρ.Good) (j : Fin D.R.m) (rd : Rd ρ D.nexp (c.twI w) j (c.sd w)), Faithful rd → ∀ (ε : KE c w →+* ℂ) (hε : Extends ρ ε) (A B : KE c w ⊗[D.ntw.O (c.twI w)] D.nexp.Fm (c.twI w) (j.1 + 1) (c.sd w)) (z : ℂ),
  rdF rd hρ hε A = z • rdF rd hρ hε B → (B = 0 → A = 0) ∧ (B ≠ 0 → ∃ t : KE c w, ε t = z ∧ A = t • B) := by
  intro D c w ρ hρ j rd hF ε hε A B z h
  let v := Module.finBasis (FractionRing (D.ntw.O (c.twI w))) (D.nexp.Fm (c.twI w) (j.1 + 1) (c.sd w))
  have hinj : ∀ d : D.ntw.O (c.twI w), d ≠ 0 → algebraMap _ (KE c w) d ≠ 0 := fun d hd h0 => by
    have h1 := congrArg ε h0
    rw [IsScalarTower.algebraMap_apply _ (D.ntw.Ok (c.twI w) (c.k' w)) (KE c w), hε.apply, hρ.ek_e, map_zero] at h1
    exact hd (ρ.eO_injective (c.twI w) (c.sd w) (h1.trans (map_zero _).symm))
  exact tensor_scalar_relation ε v rd (rdF rd hρ hε) (rdF_tmul hρ hε) (hF _ v v.linearIndependent) (tensor_exists_basis_expansion hinj v) A B z h
end

