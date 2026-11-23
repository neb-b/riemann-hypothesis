module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0093
public import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.ExistsSplitIdempotentsOfRelTraceOneModTwo
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsCoordLattice
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0099
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0010
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0011
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0013
public import Formalism.LocalRingCardinality.CoeNeZeroOfNotMem
public import Formalism.LocalToGlobal.TorsionIntegrality.UniformGaussModels.OrthogonalGaussModels.Bundle0002
public import Formalism.LocalToGlobal.TorsionIntegrality.GaussSumParity.Bundle0003
public import Formalism.GaussJetBounds.GaussJetProofs.LogarithmWeightComparison
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.OrbitPowerSeriesCoefficients.Bundle0002
public import Formalism.GaussJetBounds.GaussJetProofs.OrbMul
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.OrbitJetDegreeBound.JetTdegEqDegree
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsIntegralOrbitSeries
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0083
public import Formalism.LocalToGlobal.UnitaryNorms.Bundle0006
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0092
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0063
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.ExistsReadingLaws
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0001
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0027
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0004

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsPlaceChartOfSplitIdempotent
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.NTheta Formalism.IndefR.Datum IsDedekindDomain NumberField Matrix GlobalTheory.SplitHecke
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.SplitChart

open GlobalTheory.IdemModTwo GlobalTheory.SplitIdem

variable {D : D7} {v : HeightOneSpectrum (𝓞 D.host.F)} {e : AE D}

def sc (he : SplitAt D v e) (z : AE D) : Fv D.host.F v := (he.exists_scalar z).choose

theorem sc_spec (he : SplitAt D v e) (z : AE D) : e * z = fj D (singleV D.host.F v (sc he z)) * e :=
  (he.exists_scalar z).choose_spec

theorem sc_eq (he : SplitAt D v e) {z : AE D} {α : Af D.host.F} (h : e * z = fj D α * e) :
    sc he z = evalV D.host.F v α := by
  rw [sc_spec he] at h
  rw [← he.scalar_inj h, evalV_singleV_same]

def comp (he : SplitAt D v e) : AE D →+* Fv D.host.F v where
  toFun := sc he
  map_one' := by rw [sc_eq he (α := 1) (by rw [he.one_mul', mul_one]), map_one]
  map_zero' := by rw [sc_eq he (α := 0) (by rw [map_zero, mul_zero, zero_mul]), map_zero]
  map_mul' x y := by
    rw [sc_eq he (α := singleV D.host.F v (sc he x) * singleV D.host.F v (sc he y)), map_mul,
      evalV_singleV_same, evalV_singleV_same]
    rw [map_mul]
    linear_combination y * sc_spec he x + fj D (singleV D.host.F v (sc he x)) * sc_spec he y
  map_add' x y := by
    rw [sc_eq he (α := singleV D.host.F v (sc he x) + singleV D.host.F v (sc he y)), map_add (f := _),
      evalV_singleV_same, evalV_singleV_same]
    rw [map_add (f := _)]
    linear_combination sc_spec he x + sc_spec he y

theorem comp_apply (he : SplitAt D v e) (z : AE D) : comp he z = sc he z := rfl

theorem comp_fj (he : SplitAt D v e) (α : Af D.host.F) : comp he (fj D α) = evalV D.host.F v α :=
  sc_eq he (mul_comm _ _)

theorem comp_self (he : SplitAt D v e) : comp he e = 1 := by
  rw [comp_apply, sc_eq he (α := 1) (by rw [he.one_mul', he.1]), map_one]

theorem comp_algebraMap (he : SplitAt D v e) (y : AF D.host.F) :
    comp he (algebraMap (AF D.host.F) (AE D) y) = evalV D.host.F v y.2 := by
  rw [comp_apply, sc_eq he (α := y.2 * 1), mul_one]
  rw [← algebraMap_mul_fj, mul_assoc, he.one_mul', mul_comm]

theorem isIntegral_of_int (O : Type) {K L : Type} [CommRing O] [CommRing K] [CommRing L] [Algebra O K]
    (f : L →+* K) {x : L} (hx : IsIntegral ℤ x) : IsIntegral O (f x) :=
  (map_isIntegral_int f hx).tower_top

theorem comp_mem (he : SplitAt D v e) {z : AE D} (hz : z ∈ intL D) :
    comp he z ∈ v.adicCompletionIntegers D.host.F := by
  induction hz using AddSubgroup.closure_induction with
  | mem w hw =>
    obtain ⟨α, hα, o, rfl⟩ := hw
    have h1 : (pairA D.host.F 0 α ⊗ₜ[D.host.F] (o : D.host.E) : AE D) =
        fj D α * (1 : AF D.host.F) ⊗ₜ[D.host.F] (o : D.host.E) := by
      show _ = (_ ⊗ₜ _) * _
      rw [Algebra.TensorProduct.tmul_mul_tmul, one_mul, mul_one]
    rw [h1, map_mul, comp_fj]
    refine mul_mem (hα v) ?_
    have h3 : IsIntegral (v.adicCompletionIntegers D.host.F)
        (comp he ((1 : AF D.host.F) ⊗ₜ[D.host.F] (o : D.host.E))) :=
      isIntegral_of_int _ ((comp he).comp
        (Algebra.TensorProduct.includeRight (R := D.host.F) (A := AF D.host.F) (B := D.host.E)).toRingHom) o.2
    obtain ⟨y, hy⟩ := IsIntegrallyClosed.isIntegral_iff.1 h3
    rw [← hy]
    exact y.2
  | zero => rw [map_zero]; exact zero_mem _
  | add x y _ _ hx hy => rw [RingHom.map_add (comp he)]; exact add_mem hx hy
  | neg x _ hx => rw [map_neg]; exact neg_mem hx

theorem finPart_mem {z : AE D} (hz : z ∈ intL D) : finPart D z ∈ intAE D := by
  induction hz using AddSubgroup.closure_induction with
  | mem w hw =>
    obtain ⟨α, hα, o, rfl⟩ := hw
    exact AddSubgroup.subset_closure ⟨α, hα, o, rfl⟩
  | zero => rw [RingHom.map_zero]; exact zero_mem _
  | add x y _ _ hx hy => rw [RingHom.map_add (f := _)]; exact add_mem hx hy
  | neg x _ hx => rw [RingHom.map_neg]; exact neg_mem hx

theorem chart_comp (he : SplitAt D v e) : Chart e v (comp he) := by
  refine ⟨fun a => ⟨fj D (singleV D.host.F v a), by rw [comp_fj, evalV_singleV_same]⟩, fun a => ⟨fun h => ?_, fun h => ?_⟩,
    comp_algebraMap he, fun a => ⟨fun h => ?_, fun h => ?_⟩⟩
  · have h0 : singleV D.host.F v 0 = 0 := by
      rw [← sub_self (0 : Fv D.host.F v), singleV_sub, sub_self]
    rw [sc_spec he, ← comp_apply, h, h0, map_zero, zero_mul]
  · rw [← one_mul (comp he a), ← comp_self he, ← map_mul, h, map_zero]
  · have h1 := comp_mem he (inF_mem h)
    rw [inF_finPart, ← mul_assoc, he.one_mul', map_mul, comp_self, one_mul] at h1
    exact isInt_Ov.2 h1
  · rw [sc_spec he]
    exact finPart_mem (fj_mul_mem (singleV_mem_intAf D.host.F v ⟨_, isInt_Ov.1 h⟩) he.mem)

theorem exists_chart : ∀ {D : D7} (e : AE D), IsSplitIdem D e →
    ∃ (v : HeightOneSpectrum (𝓞 D.host.F)) (π : AE D →+* Fv D.host.F v), Chart e v π := by
  intro D e h
  obtain ⟨v, he⟩ := (isSplitIdem_iff e).1 h
  exact ⟨v, comp he, chart_comp he⟩

end GlobalTheory.SplitChart

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsSplitFrameSelfDualLatticeCompletion
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.NTheta Formalism.IndefR.Datum IsDedekindDomain NumberField Matrix GlobalTheory.SplitHecke
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.SplitFrame

open GlobalTheory.IdemModTwo (fj inF inF_finPart inF_tmul)
open GlobalTheory.SplitHeckeLabel (exists_local_lattice smul_mem_latHat mul_mem_intA intA)

theorem exists_gl_of_lattice (O : Type) [CommRing O] [IsDomain O] [IsPrincipalIdealRing O] {K : Type} [Field K]
    [Algebra O K] [IsFractionRing O K] {n : ℕ} (Λ : Submodule O (Fin n → K)) (hfg : Λ.FG)
    (hsp : Submodule.span K (Λ : Set (Fin n → K)) = ⊤) :
    ∃ β : GL (Fin n) K, ∀ w, w ∈ Λ ↔ ∀ i, IsInt O (((β⁻¹).1 *ᵥ w) i) := by
  classical
  have : Submodule.IsFullLattice K Λ := { toIsLattice := Submodule.IsLattice.of_fg K hfg, span_eq_top := hsp }
  have := Submodule.IsLattice.finite K Λ
  have := Submodule.IsLattice.free K Λ
  have hr : Module.finrank O Λ = n := by
    rw [((Submodule.IsFullLattice.finrank_eq K Λ).trans (Module.finrank_fintype_fun_eq_card K)), Fintype.card_fin]
  let b : Module.Basis (Fin n) O Λ := Module.finBasisOfFinrankEq O Λ hr
  let c : Module.Basis (Fin n) K (Fin n → K) := b.extendOfIsFullLattice K
  let s := Pi.basisFun K (Fin n)
  refine ⟨⟨s.toMatrix c, c.toMatrix s, Module.Basis.toMatrix_mul_toMatrix_flip _ _,
    Module.Basis.toMatrix_mul_toMatrix_flip _ _⟩, fun w => ?_⟩
  have hw : c.toMatrix s *ᵥ w = c.repr w := by
    exact Module.Basis.toMatrix_mulVec_repr s c w
  change _ ↔ ∀ i, IsInt O ((c.toMatrix s *ᵥ w) i)
  rw [hw]
  have hc : ∀ i, c i = (b i : Fin n → K) := fun i => Module.Basis.extendOfIsFullLattice_apply K b i
  constructor
  · intro h i
    refine ⟨b.repr ⟨w, h⟩ i, ?_⟩
    have h1 : w = ∑ j, algebraMap O K (b.repr ⟨w, h⟩ j) • c j := by
      have := congrArg Subtype.val (b.sum_repr ⟨w, h⟩)
      rw [Submodule.coe_sum] at this
      refine this.symm.trans (Finset.sum_congr rfl fun j _ => ?_)
      rw [hc, algebraMap_smul]
      rfl
    conv_rhs => rw [h1]
    rw [c.repr_sum_self]
  · intro h
    choose o ho using h
    rw [← c.sum_repr w]
    refine Λ.sum_mem fun j _ => ?_
    rw [← ho, algebraMap_smul, hc]
    exact Λ.smul_mem _ (b j).2

variable {D : D7}

theorem finPart_inF (z : Af D.host.F ⊗[D.host.F] D.host.E) : finPart D (inF D z) = z := by
  induction z using TensorProduct.induction_on with
  | zero => rw [AddMonoidHom.map_zero, RingHom.map_zero]
  | tmul a x => rfl
  | add x y hx hy => rw [AddMonoidHom.map_add (f := _), RingHom.map_add (f := _), hx, hy]

theorem exists_factor {e : AE D} {v : HeightOneSpectrum (𝓞 D.host.F)} {π : AE D →+* Fv D.host.F v}
    (h : Chart e v π) : ∃ φ : Af D.host.F ⊗[D.host.F] D.host.E →+* Fv D.host.F v, ∀ z, φ (finPart D z) = π z := by
  have h1 : π (fj D 1) = 1 := (h.2.2.1 _).trans (map_one (evalV D.host.F v))
  refine ⟨(finPart D).liftOfRightInverse (inF D) finPart_inF ⟨π, fun z hz => ?_⟩, fun z =>
    RingHom.liftOfRightInverse_comp_apply _ _ _ _ z⟩
  rw [RingHom.mem_ker] at hz ⊢
  have h2 := inF_finPart z
  rw [hz, AddMonoidHom.map_zero] at h2
  have h3 := congrArg π h2
  rwa [RingHom.map_zero, RingHom.map_mul, h1, one_mul, eq_comm] at h3

theorem finPart_mul_eq {e : AE D} {v : HeightOneSpectrum (𝓞 D.host.F)} {π : AE D →+* Fv D.host.F v}
    (h : Chart e v π) {φ : Af D.host.F ⊗[D.host.F] D.host.E →+* Fv D.host.F v} (hφ : ∀ z, φ (finPart D z) = π z)
    (y : AE D) (z : Af D.host.F ⊗[D.host.F] D.host.E) (hy : π y = φ z) : finPart D (e * y) = finPart D e * z := by
  have h1 : π y = π (inF D z) := by
    rw [← hφ (inF D z), finPart_inF]
    exact hy
  have h2 := (h.2.1 (y - inF D z)).1 (by rw [RingHom.map_sub, h1, sub_self])
  rw [mul_sub, sub_eq_zero] at h2
  rw [h2, RingHom.map_mul, finPart_inF]

theorem exists_frame : ∀ {D : D7} (e : AE D) (v : HeightOneSpectrum (𝓞 D.host.F)) (π : AE D →+* Fv D.host.F v), IsSplitIdem D e → Chart e v π → ∀ V : HSp D, ∃ β : GL (Fin V.rank) (Fv D.host.F v), Frame V e π β := by
  intro D e v π he h V
  obtain ⟨φ, hφ⟩ := exists_factor h
  have hei : finPart D e ∈ intA D.host.F D.host.E :=
    GlobalTheory.AdIdem.idempotent_mem_intAE D _ (by rw [← RingHom.map_mul, he.1])
  have hπe : π e = 1 := by
    have := (h.2.1 (e - 1)).2 (by rw [mul_sub, he.1, mul_one, sub_self])
    rwa [RingHom.map_sub, RingHom.map_one, sub_eq_zero] at this
  let L : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E) :=
    V.L0.map (V.frame.equivFun.toLinearMap.restrictScalars (𝓞 D.host.E))
  have hL : (L : Set (Fin V.rank → D.host.E)) = L0c D V := Set.ext fun y => by
    change _ ↔ ∑ i, y i • V.frame i ∈ V.L0
    rw [← V.frame.equivFun_symm_apply]
    constructor
    · rintro ⟨x, hx, rfl⟩
      change V.frame.equivFun.symm (V.frame.equivFun x) ∈ V.L0
      rwa [LinearEquiv.symm_apply_apply]
    · exact fun h => ⟨_, h, V.frame.equivFun.apply_symm_apply y⟩
  have hsp : Submodule.span D.host.E (L : Set (Fin V.rank → D.host.E)) = ⊤ := by
    classical
    have hs : Submodule.span D.host.E (V.L0 : Set V.V) = ⊤ := by
      obtain ⟨s, hs⟩ := V.standardTuple_isLattice.fg
      apply eq_top_iff.mpr
      intro y _
      obtain ⟨a, ha⟩ := IsLocalization.exist_integer_multiples (nonZeroDivisors (𝓞 D.host.E)) s (fun x => V.hT x y)
      have ha0 : (algebraMap (𝓞 D.host.E) D.host.E a) ≠ 0 :=
        (FaithfulSMul.algebraMap_injective _ _).ne (mem_nonZeroDivisors_iff_ne_zero.mp a.2)
      let P : Submodule (𝓞 D.host.E) V.V := {
        carrier := {x | ∃ b : 𝓞 D.host.E, (b : D.host.E) = (algebraMap (𝓞 D.host.E) D.host.E a) * V.hT x y}
        zero_mem' := by refine ⟨0, ?_⟩; simp
        add_mem' := by
          rintro x z ⟨b, hb⟩ ⟨c, hc⟩
          refine ⟨b + c, ?_⟩
          change (b : D.host.E) + c = _
          rw [hb, hc, map_add, LinearMap.add_apply, mul_add]
        smul_mem' := by
          rintro c x ⟨b, hb⟩
          refine ⟨RingOfIntegers.mapRingHom (starRingEnd D.host.E) c * b, ?_⟩
          simp only [map_mul, RingOfIntegers.mapRingHom_apply, hb]
          rw [show c • x = (c : D.host.E) • x from (IsScalarTower.algebraMap_smul D.host.E c x).symm, LinearMap.map_smulₛₗ, LinearMap.smul_apply, smul_eq_mul]
          change star (c : D.host.E) * ((algebraMap (𝓞 D.host.E) D.host.E a) * V.hT x y) = _
          simp only [starRingEnd_apply]
          ring }
      have hsP : (s : Set V.V) ⊆ P := by
        intro x hx
        obtain ⟨b, hb⟩ := ha x hx
        exact ⟨b, by simpa [Algebra.smul_def] using hb⟩
      have hy : (algebraMap (𝓞 D.host.E) D.host.E a) • y ∈ V.L0 := by
        rw [← V.baseLattice_isUnimodular]
        change (algebraMap (𝓞 D.host.E) D.host.E a) • y ∈ Formalism.E.hdual V.hT V.L0
        simp only [Formalism.E.hdual, Submodule.mem_iInf, Submodule.mem_comap]
        intro x hx
        obtain ⟨b, hb⟩ := (hs ▸ Submodule.span_le.mpr hsP) hx
        change V.hT x ((algebraMap (𝓞 D.host.E) D.host.E a) • y) ∈ (1 : Submodule (𝓞 D.host.E) D.host.E)
        rw [map_smul, smul_eq_mul, ← hb]
        exact Submodule.algebraMap_mem _
      have hy' := (Submodule.span D.host.E (V.L0 : Set V.V)).smul_mem (algebraMap (𝓞 D.host.E) D.host.E a)⁻¹ (Submodule.subset_span hy)
      rwa [← smul_assoc, smul_eq_mul, inv_mul_cancel₀ ha0, one_smul] at hy'
    change Submodule.span _ (V.frame.equivFun.toLinearMap '' (V.L0 : Set V.V)) = ⊤
    rw [← Submodule.map_span, hs, Submodule.map_top, LinearEquiv.range]
  obtain ⟨Λ, hfg, hΛ, hmem⟩ := exists_local_lattice (F := D.host.F) L (V.standardTuple_isLattice.fg.map _) hsp v φ
    (fun a => (hφ (algebraMap (AF D.host.F) (AE D) (pairA D.host.F 0 a))).trans (h.2.2.1 _))
    (fun x hx => by
      rw [← finPart_inF x, hφ, ← isInt_Ov, ← h.2.2.2, RingHom.map_mul, finPart_inF]
      exact mul_mem_intA hei hx)
  obtain ⟨β, hβ⟩ := exists_gl_of_lattice (Ov D v) Λ hfg hΛ
  refine ⟨β, fun y => ?_⟩
  rw [← hβ, hmem, LamHat, ← hL]
  constructor
  · intro hy
    refine ⟨_, hy, funext fun i => ?_⟩
    rw [Function.comp_apply, hφ, RingHom.map_mul, hπe, one_mul]
  · rintro ⟨z, hz, hy⟩
    have : (fun i => finPart D (e * y i)) = finPart D e • z := funext fun i =>
      finPart_mul_eq h hφ (y i) (z i) (congrFun hy i)
    rw [this]
    exact smul_mem_latHat L hei hz

end GlobalTheory.SplitFrame

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.HyperbolicPairAdditiveCoordsLinearFormsStatement
section
open NumberField Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.G Formalism.MainNotions.TaylorLogMetric GlobalTheory.KerStd Classical
open Formalism.L2.Th1.CM (MaximalUnramifiedExtension)
open Formalism.L2.Th1.D (F1 F2 OwOK TrDual phFF)
open Formalism.InvariantFactorPaths.G7 (UnrOK IsLawOfLog cob)
open MvPowerSeries
open Formalism.DworkPowerSeriesWeights (Integral mvExp entLog ZV)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.orbitPlaces_thetaSeries_subst_orbMap_eq : ∀ (D : D7) (p : ℕ) [Fact p.Prime] (hp : 5 ≤ p) (σ : MaximalUnramifiedExtension p →+* MaximalUnramifiedExtension p) (om oms : Fin (nP D p / 2) → MaximalUnramifiedExtension p)
    (R : Finset (OrbitPlaces.Pl D)) {M N N' r : ℕ} (eA : Fin M ≃ R × Fin N)
    (f f' : (R × Fin (nP D p / 2)) × Fin N × Fin N' → Fin r → MaximalUnramifiedExtension p) (Θ : MvPowerSeries (Fin r) ℂ_[p]), subst (fun y : ZV (nP D p) M N' =>
        (X (OrbitPlaces.orbMap D p (eA y.2.1).1 y.1, (eA y.2.1).2, y.2.2) : MvPowerSeries (OrbitPlaces.Pl D × Fin N × Fin N') ℂ_[p]))
      (Formalism.L2.Th1.D.thetaInZ (d := nP D p) p (MaximalUnramifiedExtension p).subtype σ om oms
        (subst (fun x : Bool × (R × Fin (nP D p / 2)) × Fin N × Fin N' =>
            (X (x.1, x.2.1.2, eA.symm (x.2.1.1, x.2.2.1), x.2.2.2) :
              MvPowerSeries (Bool × Fin (nP D p / 2) × Fin M × Fin N') ℂ_[p]))
          (Formalism.L2.Th1.Top.inHyp p f f'
            (subst (fun i : Fin r => (Formalism.InvariantFactorPaths.G7.at1 i (Formalism.InvariantFactorPaths.G7.lgF ℂ_[p] p) : MvPowerSeries (Fin r) ℂ_[p])) Θ)))) =
      subst (hypZ D p σ om oms R f f') Θ := by
  first | exact @GlobalTheory.KerStd.HypOrbit.hypZ_of_inHyp | exact GlobalTheory.KerStd.HypOrbit.hypZ_of_inHyp | (intros; apply GlobalTheory.KerStd.HypOrbit.hypZ_of_inHyp <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.InfDiagMulFinPartI
section
noncomputable section

namespace GlobalTheory.UnUnitCmp.Val

open NumberField IsDedekindDomain Neutral.B1 ReciprocityTheory.Neutral.Bridge.HCFR Formalism.L2.Host GlobalTheory.Mem.Chr

variable {L : Type} [Field L] [NumberField L]

def intFin (L : Type) [Field L] [NumberField L] : Subring (FiniteAdeleRing (𝓞 L) L) where
  carrier := {a | ∀ v, a v ∈ v.adicCompletionIntegers L}
  one_mem' := fun _ => one_mem _
  zero_mem' := fun _ => zero_mem _
  add_mem' := fun ha hb v => add_mem (ha v) (hb v)
  mul_mem' := fun ha hb v => mul_mem (ha v) (hb v)
  neg_mem' := fun ha v => neg_mem (ha v)

theorem finite_quot (N : ℕ) (hN : 0 < N) : Finite (intFin L ⧸ Ideal.span {(N : intFin L)}) := by
  let ι : 𝓞 L →+* intFin L :=
    ((algebraMap L (FiniteAdeleRing (𝓞 L) L)).comp (algebraMap (𝓞 L) L)).codRestrict _
      fun x v => HeightOneSpectrum.coe_mem_adicCompletionIntegers v x
  have : Finite (𝓞 L ⧸ Ideal.span {(N : 𝓞 L)}) :=
    Ideal.finiteQuotientOfFreeOfNeBot _ (by simpa using hN.ne')
  refine Finite.of_surjective (Ideal.quotientMap (I := Ideal.span {(N : 𝓞 L)})
    (Ideal.span {(N : intFin L)}) ι ?_) ?_
  · rw [Ideal.span_le, Set.singleton_subset_iff]
    change ι N ∈ Ideal.span {(N : intFin L)}
    rw [map_natCast]
    exact Ideal.mem_span_singleton_self _
  · intro z
    obtain ⟨z, rfl⟩ := Ideal.Quotient.mk_surjective z
    obtain ⟨x, w, hw, h⟩ := (GlobalTheory.AdLat.strong_approximation_mod_nat L N hN).2 z z.2
    refine ⟨Ideal.Quotient.mk _ x, ?_⟩
    rw [Ideal.quotientMap_mk, eq_comm, Ideal.Quotient.eq, Ideal.mem_span_singleton]
    refine ⟨⟨w, hw⟩, Subtype.ext ?_⟩
    change (z : FiniteAdeleRing (𝓞 L) L) - algebraMap L _ (x : L) = ((N : intFin L) : FiniteAdeleRing (𝓞 L) L) * w
    rw [h, add_sub_cancel_left, nsmul_eq_mul]
    simp

theorem finUnit_pow (χ : Formalism.L2.Host.HChar L) (hχ : χ.IsUnitary) :
    ∃ m : ℕ, 0 < m ∧ ∀ u : Neutral.B1.Ideles L, Formalism.L2.Host.IsFinIdele u → u ∈ unitIdl L → ((χ.1 u : ℂˣ) : ℂ) ^ m = 1 := by
  let ψ : Neutral.B1.Ideles L →* Circle :=
    { toFun := fun x => ⟨(χ.1 x : ℂˣ), by simpa [Submonoid.unitSphere] using hχ x⟩
      map_one' := by ext; simp
      map_mul' := fun x y => Subtype.ext (congrArg Units.val (map_mul χ.1 x y)) }
  have hψ : Continuous ψ := (Units.continuous_val.comp χ.2.1).subtype_mk _
  obtain ⟨-, -, -, m, hm, h⟩ := GlobalTheory.CharFin.finite_order_of_small (R := AdeleRing (𝓞 L) L)
    (RingHom.fst (InfiniteAdeleRing L) (FiniteAdeleRing (𝓞 L) L)) (RingHom.snd _ _) id continuous_id (fun _ => rfl) (intFin L)
    (fun W hW => GlobalTheory.AdLat.OpenLat.exists_nsmul_adele L W hW) finite_quot ψ hψ
  refine ⟨m, hm, fun u h1 h2 => ?_⟩
  have := h u ⟨funext h1, fun v => (h2 v).le, fun v => ((unitIdl L).inv_mem h2 v).le⟩
  exact congrArg (fun z : Circle => (z : ℂ)) this

theorem infDiag_mul_finPartI (k : Lˣ) : Formalism.L2.Host.infDiag k * finPartI L (Neutral.B1.diagUnits L k) = Neutral.B1.diagUnits L k := by
  classical
  have h : ((Formalism.L2.Host.infDiag k : Neutral.B1.Ideles L) : AdeleRing (𝓞 L) L) = (algebraMap L (InfiniteAdeleRing L) k, 1) := by
    unfold Formalism.L2.Host.infDiag
    rw [MonoidHom.finsetProd_apply, Units.coe_prod]
    let ι : (∀ w : InfinitePlace L, w.Completion) →* AdeleRing (𝓞 L) L :=
      MonoidHom.inl (InfiniteAdeleRing L) (FiniteAdeleRing (𝓞 L) L)
    change ∏ w : InfinitePlace L, ι (Pi.mulSingle w (algebraMap L w.Completion k)) = ι (fun w => algebraMap L w.Completion k)
    rw [← map_prod, Finset.univ_prod_mulSingle]
  apply Units.ext
  rw [Units.val_mul, h]
  exact Prod.ext (mul_one _) (one_mul _)

theorem exists_pow_eq (x : Neutral.B1.Ideles L) (hx : Formalism.L2.Host.IsFinIdele x) :
    ∃ h : ℕ, 0 < h ∧ ∃ (u : Neutral.B1.Ideles L) (k : Lˣ), Formalism.L2.Host.IsFinIdele u ∧ u ∈ unitIdl L ∧ x ^ h * Formalism.L2.Host.infDiag k = u * Neutral.B1.diagUnits L k := by
  have := GlobalTheory.Mem.UnitIndex.finiteIndex_unitIdl_sup L
  refine ⟨_, Nat.pos_of_ne_zero this.index_ne_zero, ?_⟩
  obtain ⟨u, hu, _, ⟨k, rfl⟩, e⟩ := Subgroup.mem_sup.1 ((unitIdl L ⊔ (Neutral.B1.diagUnits L).range).pow_index_mem x)
  have hf : finPartI L x = x := Units.ext (Prod.ext (funext hx).symm rfl)
  refine ⟨finPartI L u, k, fun _ => rfl, hu, ?_⟩
  rw [← hf, ← map_pow, ← e, map_mul, mul_assoc, mul_comm _ (Formalism.L2.Host.infDiag k), infDiag_mul_finPartI]

end GlobalTheory.UnUnitCmp.Val
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.IsIrreducibleTwist
section
noncomputable section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal Polynomial NumberField IsDedekindDomain GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.RowTie GlobalTheory.SplitRead
open GlobalTheory.WeilDeligne GlobalTheory.ThetaExh

namespace GlobalTheory.SplitPairLift

theorem isIrreducible_twist {G V : Type} [Group G] [AddCommGroup V] [Module ℂ V]
    {ρ : Representation ℂ G V} (h : ρ.IsIrreducible) (χ : G →* ℂˣ) : (twist ρ χ).IsIrreducible := by
  let e : Subrepresentation (twist ρ χ) ≃o Subrepresentation ρ :=
    { toFun := fun S => ⟨S.toSubmodule, fun g v hv => by
        have h1 := S.toSubmodule.smul_mem (((χ g)⁻¹ : ℂˣ) : ℂ) (S.apply_mem_toSubmodule g hv)
        rwa [twist_apply, smul_smul, Units.inv_mul, one_smul] at h1⟩
      invFun := fun S => ⟨S.toSubmodule, fun g v hv =>
        S.toSubmodule.smul_mem _ (S.apply_mem_toSubmodule g hv)⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl
      map_rel_iff' := Iff.rfl }
  exact e.isSimpleOrder_iff.2 h

section Local

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

def detIrr (n : ℕ) {χ : kˣ →* ℂˣ} (h : IsSmoothChar χ) : Irr k n where
  V := ℂ
  π := detRep (Fin n) χ
  smooth := (isSmooth_ofChar_iff _).2 h.detChar
  irr := isIrreducible_ofChar _

def twistIrr {n : ℕ} (π : Irr k n) {χ : kˣ →* ℂˣ} (h : IsSmoothChar χ) : Irr k n where
  V := π.V
  π := twist π.π (detChar (Fin n) χ)
  smooth := isSmooth_twist π.smooth h.detChar
  irr := isIrreducible_twist π.irr _

theorem twist_twist_inv {n : ℕ} (π : Irr k n) (χ : kˣ →* ℂˣ) :
    twist (twist π.π (detChar (Fin n) χ)) (detChar (Fin n) χ⁻¹) = π.π := by
  rw [twist_twist]
  have : detChar (Fin n) χ⁻¹ * detChar (Fin n) χ = 1 := by
    ext g; simp
  rw [this, twist_one]

end Local

variable {R : Ranks} {H : Host R} {what₂ : Rows.Data R} {N : NData R H what₂} {A : NAut N}

theorem e_spehLoc (T : WDTie N A) (p : Part A.CG) (w : PlE H) :
    T.e w (spehLoc N A p w) = speh (T.e w (A.locG p.π w)) p.d := by
  unfold spehLoc speh
  generalize ((p.d : ℝ) - 1) / 2 = s
  have key : ∀ L : List ℝ,
      T.e w (L.foldr (fun j acc => A.lpSum (A.lpTw (A.locG p.π w) (s - j)) acc) (A.lpZero w)) =
        L.foldr (fun j acc => ((T.e w (A.locG p.π w)).lpTw (s - j)).lpSum acc)
          (WD.lpZero (h := N.plOm.2 w)) := by
    intro L
    induction L with
    | nil => exact T.zero w
    | cons j l ih => rw [List.foldr_cons, List.foldr_cons, T.sum, T.tw, ih]
  exact key _

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

end GlobalTheory.SplitPairLift
end
end

