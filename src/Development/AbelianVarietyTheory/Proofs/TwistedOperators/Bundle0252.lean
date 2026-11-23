module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0221
public import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.ThetaKernelOrthonormalFrameInDomainPeriodLinear
public import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.IsWeakOfDatum
public import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0948
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0156
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.PairwiseDisjointCell
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0224
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0896
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SphericalHeckeValuesSameParameters
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0771
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0226
public import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.Bundle0001
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0005
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0160

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.RealPlaceDeterminantPowerMulCompactTorusElement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.FWT Formalism.L2.Pj
open MeasureTheory IsDedekindDomain NumberField Matrix Complex
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Ker GlobalTheory.AdSpan
open GlobalTheory.SW hiding Level
open scoped TensorProduct ComplexConjugate Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.AdSpan.DetTor

variable {D : D7} {S T : HSp D}

theorem det_conj_diag_exp {n : ℕ} {x : Matrix (Fin n) (Fin n) ℂ} (hx : IsUnit x.det) (t : Fin n → ℝ) (k : ℤ) :
    (x * diagonal (fun a => cexp ((t a : ℂ) * I)) * x⁻¹).det ^ k = cexp (((∑ a, (k : ℝ) * t a : ℝ) : ℂ) * I) := by
  rw [Matrix.det_conj ((Matrix.isUnit_iff_isUnit_det x).2 hx), det_diagonal, ← Complex.exp_sum,
    ← Complex.exp_int_mul]
  congr 1
  push_cast
  rw [Finset.mul_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun a _ => ?_
  ring

theorem detPow_mul_torAt (D : D7) (S T : HSp D) (C : Ctx S T) (B : C.Bas) (hB : C.IsB B) (m : D.what₂.Tau → ℤ)
    (ρ : D.what₂.Tau) (t : Fin T.rank → ℝ) (g : GA D T) :
    detPow C.θ T m (g * torAt C.θ T B ρ t) = cexp (((∑ a, ((m ρ : ℤ) : ℝ) * t a : ℝ) : ℂ) * I) * detPow C.θ T m g := by
  have R : GlobalTheory.SmoothForms.RealPoints C.θ T := (GlobalTheory.SmoothForms.RealPts.realPoints D).2 C.θ C.inf T
  have hu := GlobalTheory.HolRead.AdExt.conj_mem_unitary (GlobalTheory.AdSpan.ConjHol.isUnit_det_B C hB ρ) (hB ρ)
    (by unfold sgnM; exact GlobalTheory.HolRead.AdExt.diag_unitary _ t)
  have hk := GlobalTheory.HolRead.AdExt.atTau_spec R ρ hu
  have key : ∀ ρ', (compAt C.θ ρ' (Formalism.L2.Theta.mt T (g * torAt C.θ T B ρ t))).det ^ m ρ' =
      (if ρ' = ρ then cexp (((∑ a, ((m ρ : ℤ) : ℝ) * t a : ℝ) : ℂ) * I) else 1) *
        (compAt C.θ ρ' (Formalism.L2.Theta.mt T g)).det ^ m ρ' := by
    intro ρ'
    have hm : compAt C.θ ρ' (Formalism.L2.Theta.mt T (g * torAt C.θ T B ρ t)) =
        compAt C.θ ρ' (Formalism.L2.Theta.mt T g) * compAt C.θ ρ' (Formalism.L2.Theta.mt T (torAt C.θ T B ρ t)) :=
      R.2.2.2.1 g _ ρ'
    rw [hm, det_mul, mul_zpow, mul_comm]
    congr 1
    by_cases c : ρ' = ρ
    · subst c
      rw [if_pos rfl]
      have h1 : compAt C.θ ρ' (Formalism.L2.Theta.mt T (torAt C.θ T B ρ' t)) =
          B ρ' * diagonal (fun a => cexp ((t a : ℂ) * I)) * (B ρ')⁻¹ := hk.2.1
      rw [h1]
      exact det_conj_diag_exp (GlobalTheory.AdSpan.ConjHol.isUnit_det_B C hB ρ') t (m ρ')
    · rw [if_neg c]
      have h1 : compAt C.θ ρ' (Formalism.L2.Theta.mt T (torAt C.θ T B ρ t)) = 1 := hk.2.2 ρ' c
      rw [h1, det_one, _root_.one_zpow]
  unfold detPow
  rw [Finset.prod_congr rfl fun ρ' _ => key ρ', Finset.prod_mul_distrib, Finset.prod_ite_eq' Finset.univ ρ,
    if_pos (Finset.mem_univ _)]

end GlobalTheory.AdSpan.DetTor

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.SatakeVectorHeckeEigenvalue
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum GlobalTheory.LFun GlobalTheory.AdelicU GlobalTheory.PRep GlobalTheory.FinZeta GlobalTheory.AdelicScalar GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues GlobalTheory.LiftRows
open Formalism.IndefR.Lev (levG levChi IsBaseFrame)
open Formalism.UG (IsUnifV qV IsUnramInv GU KU IsInertAt Hecke dosetInd IsCommensurated)
open Formalism.MainNotions.SchurIrreducible (IsSplit)
open GlobalTheory.LGrp (IsUnitarisable IsIrrSmooth bcParam)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.FinZeta.GLTwist

open Formalism.UG (Tj Ov)

section Twist

variable {E : Type} [Field E] [NumberField E] {w : HeightOneSpectrum (𝓞 E)} {r : ℕ}
  {V : Type} [AddCommGroup V] [Module ℂ V]

theorem ordV_mul {x y : w.adicCompletion E} (hx : x ≠ 0) (hy : y ≠ 0) :
    Formalism.UG.ordV E w (x * y) = Formalism.UG.ordV E w x + Formalism.UG.ordV E w y := by
  have hx' : Valued.v x ≠ 0 := (Valuation.ne_zero_iff _).2 hx
  have hy' : Valued.v y ≠ 0 := (Valuation.ne_zero_iff _).2 hy
  rw [GlobalTheory.LGrp.BorelCompletion.ordV_eq, GlobalTheory.LGrp.BorelCompletion.ordV_eq, GlobalTheory.LGrp.BorelCompletion.ordV_eq, map_mul,
    WithZero.log_mul hx' hy']
  ring

theorem ordV_zpow {ϖ : w.adicCompletion E} (hϖ : IsUnifV E w ϖ) (k : ℤ) : Formalism.UG.ordV E w (ϖ ^ k) = k := by
  rw [GlobalTheory.LGrp.BorelCompletion.ordV_eq, map_zpow₀, show Valued.v ϖ = _ from hϖ, WithZero.log_zpow,
    show WithZero.log (((Multiplicative.ofAdd (-1 : ℤ) : Multiplicative ℤ)) : WithZero (Multiplicative ℤ)) = -1 from rfl]
  simp

def ordDet (g : GL (Fin r) (w.adicCompletion E)) : ℤ := Formalism.UG.ordV E w g.val.det

theorem det_ne_zero (g : GL (Fin r) (w.adicCompletion E)) : g.val.det ≠ 0 :=
  (Matrix.GeneralLinearGroup.det g).ne_zero

theorem ordDet_mul (g h : GL (Fin r) (w.adicCompletion E)) : ordDet (g * h) = ordDet g + ordDet h := by
  rw [ordDet, Units.val_mul, Matrix.det_mul, ordV_mul (det_ne_zero g) (det_ne_zero h)]
  rfl

theorem ordDet_of_mem {k : GL (Fin r) (w.adicCompletion E)} (hk : k ∈ KGL w (n := r)) : ordDet k = 0 := by
  have h : Valued.v k.val.det = 1 := GlobalTheory.SphGal.isUnitAt_det_of_mem hk
  rw [ordDet, GlobalTheory.LGrp.BorelCompletion.ordV_eq, h]
  simp

theorem ordDet_one : ordDet (1 : GL (Fin r) (w.adicCompletion E)) = 0 := ordDet_of_mem (one_mem _)

theorem prod_zpow_eq {ι : Type} {ϖ : w.adicCompletion E} (h0 : ϖ ≠ 0) (d : ι → ℤ) (s : Finset ι) :
    ∏ i ∈ s, ϖ ^ d i = ϖ ^ ∑ i ∈ s, d i := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih => rw [Finset.prod_insert ha, Finset.sum_insert ha, ih, zpow_add₀ h0]

theorem ordDet_of_diagonal {ϖ : w.adicCompletion E} (hϖ : IsUnifV E w ϖ) {t : GL (Fin r) (w.adicCompletion E)}
    {d : Fin r → ℤ} (ht : t.1 = Matrix.diagonal fun i => ϖ ^ d i) : ordDet t = ∑ i, d i := by
  have h0 : ϖ ≠ 0 := fun h0 => by simp [IsUnifV, h0] at hϖ
  rw [ordDet, ht, Matrix.det_diagonal, prod_zpow_eq h0, ordV_zpow hϖ]

def twistRep (ρ : Representation ℂ (GL (Fin r) (w.adicCompletion E)) V) (z : ℂˣ) :
    Representation ℂ (GL (Fin r) (w.adicCompletion E)) V where
  toFun g := ((z : ℂ) ^ ordDet g) • ρ g
  map_one' := by simp [ordDet_one]
  map_mul' g h := by
    rw [ordDet_mul, zpow_add₀ z.ne_zero, map_mul]
    refine LinearMap.ext fun y => ?_
    simp only [Module.End.mul_apply, LinearMap.smul_apply, map_smul, mul_smul]
    exact smul_comm _ _ _

theorem twistRep_apply (ρ : Representation ℂ (GL (Fin r) (w.adicCompletion E)) V) (z : ℂˣ)
    (g : GL (Fin r) (w.adicCompletion E)) (y : V) : twistRep ρ z g y = ((z : ℂ) ^ ordDet g) • ρ g y := rfl

theorem heckeVec_twistRep (ρ : Representation ℂ (GL (Fin r) (w.adicCompletion E)) V) (z : ℂˣ)
    (t : GL (Fin r) (w.adicCompletion E)) (x : V) :
    heckeVec (twistRep ρ z) (KGL w (n := r)) (dosetInd ℂ (KGL w (n := r)) t) x =
      ((z : ℂ) ^ ordDet t) • heckeVec ρ (KGL w (n := r)) (dosetInd ℂ (KGL w (n := r)) t) x := by
  rw [heckeVec, heckeVec, smul_finsum]
  refine finsum_congr fun c => ?_
  by_cases hc : ∃ a ∈ KGL w (n := r), ∃ b ∈ KGL w (n := r), c.out = a * t * b
  · obtain ⟨a, ha, b, hb, e⟩ := id hc
    have h : ordDet c.out = ordDet t := by
      rw [e, ordDet_mul, ordDet_mul, ordDet_of_mem ha, ordDet_of_mem hb]
      simp
    rw [twistRep_apply, h, smul_comm]
  · rw [GlobalTheory.WeylGL.dosetInd_of_not hc]
    simp

theorem isSatVecGL_twistRep {ρ : Representation ℂ (GL (Fin r) (w.adicCompletion E)) V} {x : V} {B : Multiset ℂˣ}
    (hx : IsSatVecGL w ρ x B) (z : ℂˣ) : IsSatVecGL w (twistRep ρ z) x (B.map (z * ·)) := by
  refine ⟨hx.1, GlobalTheory.LGrp.mem_fixed.2 fun k hk => ?_, by rw [Multiset.card_map, hx.2.2.1], fun ϖ hϖ j hj => ?_⟩
  · rw [twistRep_apply, ordDet_of_mem hk, zpow_zero, one_smul]
    exact GlobalTheory.LGrp.mem_fixed.1 hx.2.1 k hk
  · have h0 : ϖ ≠ 0 := fun h0 => by simp [IsUnifV, h0] at hϖ
    have em : B.map (z * ·) = B.map (· * z) := Multiset.map_congr rfl fun b _ => mul_comm _ _
    have ho : ordDet (GlobalTheory.WeylGL.tor h0 fun i : Fin r => if (i : ℕ) < j then 1 else 0) = j := by
      rw [ordDet_of_diagonal hϖ (GlobalTheory.WeylGL.tor_val h0 _)]
      simp [Finset.sum_boole, Fin.card_filter_val_lt, min_eq_right hj]
    rw [GlobalTheory.WeylGL.Tj_eq h0, heckeVec_twistRep, ← GlobalTheory.WeylGL.Tj_eq h0, hx.2.2.2 ϖ hϖ j hj, em,
      GlobalTheory.SphGal.satEig_map_mul, ho, zpow_natCast, smul_smul]

end Twist

theorem hasSum_twisted_hecke_eigenvalues : GlobalTheory.Published.UnramifiedDoublingGL → ∀ (E : Type) [Field E] [NumberField E] (w : HeightOneSpectrum (𝓞 E)) (r : ℕ) (V : Type) [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ (GL (Fin r) (w.adicCompletion E)) V) (x : V) (B : Multiset ℂˣ), IsSatVecGL w ρ x B → ∀ (z : ℂˣ) (ϖ : w.adicCompletion E), IsUnifV E w ϖ → ∀ T : (Fin r → ℤ) → GL (Fin r) (w.adicCompletion E), (∀ d, (T d).1 = Matrix.diagonal fun i => ϖ ^ d i) → ∀ c : (Fin r → ℤ) → ℂ, (∀ d, heckeVec ρ (KGL w (n := r)) (dosetInd ℂ (KGL w (n := r)) (T d)) x = c d • x) → ∃ δ : ℝ, 0 < δ ∧ ∀ X : ℝ, 0 < X → X < δ → HasSum (fun d : {d : Fin r → ℤ // Antitone d} => (z : ℂ) ^ (∑ i, d.1 i) * c d.1 * (X : ℂ) ^ (∑ i, |d.1 i|).toNat) (eulerFac (B.map (z * ·)) ((qV E w : ℂ) ^ (((r : ℂ) - 1) / 2) * X) * eulerFac (B.map fun β => (z * β)⁻¹) ((qV E w : ℂ) ^ (((r : ℂ) - 1) / 2) * X) * ∏ i ∈ Finset.range r, (1 - (qV E w : ℂ) ^ i * (X : ℂ) ^ 2)) := by
  intro hP E _ _ w r V _ _ ρ x B hx z ϖ hϖ T hT c hc
  have hc' : ∀ d, heckeVec (twistRep ρ z) (KGL w (n := r)) (dosetInd ℂ (KGL w (n := r)) (T d)) x =
      ((z : ℂ) ^ (∑ i, d i) * c d) • x := fun d => by
    rw [heckeVec_twistRep, hc d, ordDet_of_diagonal hϖ (hT d), smul_smul]
  obtain ⟨δ, h0, h⟩ := GlobalTheory.T.hasSum_heckeEigenvalue_generatingSeries_GL hP E w r V (twistRep ρ z) x _ (isSatVecGL_twistRep hx z) ϖ hϖ T hT _ hc'
  refine ⟨δ, h0, fun X h1 h2 => ?_⟩
  have := h X h1 h2
  rw [Multiset.map_map] at this
  exact this

end GlobalTheory.FinZeta.GLTwist

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ScalarOfComm
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open Matrix MeasureTheory GlobalTheory.Chain GlobalTheory.Chain.RealIt
open GlobalTheory.IndefiniteRowSideFullHecke.KTypeExtension (kFin KVec KMap maxCpt rep_mem_kFin)
open scoped TensorProduct InnerProductSpace Classical
open GlobalTheory.Chain.IoLift
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.Chain.IoLift.Scal

variable {ι : Type} [Fintype ι] {K : ι → Type} [∀ i, AddCommGroup (K i)] [∀ i, Module ℂ (K i)]

def tform (w : ∀ i, Module.Dual ℂ (K i)) : (⨂[ℂ] i, K i) →ₗ[ℂ] ℂ := GlobalTheory.MultilinearContraction.prodForm w

theorem tform_tprod (w : ∀ i, Module.Dual ℂ (K i)) (v : ∀ i, K i) :
    tform w (PiTensorProduct.tprod ℂ v) = ∏ i, w i (v i) := by
  exact GlobalTheory.MultilinearContraction.prodForm_tprod w v

theorem eq_of_tform {t t' : ⨂[ℂ] i, K i} (h : ∀ w, tform w t = tform w t') : t = t' := by
  let b := fun i => Module.Basis.ofVectorSpace ℂ (K i)
  let B := Basis.piTensorProduct b
  refine B.ext_elem fun p => ?_
  have : B.coord p = tform fun i => (b i).coord (p i) := by
    ext v
    simp [tform_tprod, B, Basis.piTensorProduct_repr_tprod_apply]
  have h2 := h fun i => (b i).coord (p i)
  rw [← this] at h2
  simpa using h2

def ctrM (i : ι) (w : ∀ i, Module.Dual ℂ (K i)) : (Π j, K j) →ₘₗ[ℂ] K i :=
  GlobalTheory.MultilinearContraction.contractMultilinear w i

def ctr (i : ι) (w : ∀ i, Module.Dual ℂ (K i)) : (⨂[ℂ] i, K i) →ₗ[ℂ] K i :=
  PiTensorProduct.lift (ctrM i w)

theorem ctr_tprod (i : ι) (w : ∀ i, Module.Dual ℂ (K i)) (v : ∀ i, K i) :
    ctr i w (PiTensorProduct.tprod ℂ v) = (∏ j ∈ Finset.univ.erase i, w j (v j)) • v i := by
  simp [ctr, ctrM]

theorem ctr_mapFactor (i : ι) (w : ∀ i, Module.Dual ℂ (K i)) (f : Module.End ℂ (K i)) (t : ⨂[ℂ] i, K i) :
    ctr i w (intersection_update_fsHerm_neg_one i f t) = f (ctr i w t) := by
  have : ctr i w ∘ₗ intersection_update_fsHerm_neg_one i f = f ∘ₗ ctr i w := by
    ext v
    simp only [LinearMap.compMultilinearMap_apply, LinearMap.comp_apply, position_tprod, ctr_tprod,
      Function.update_self, map_smul]
    congr 1
    exact Finset.prod_congr rfl fun j hj => by rw [Function.update_of_ne (Finset.ne_of_mem_erase hj)]
  exact LinearMap.congr_fun this t

theorem tform_eq (i : ι) (w : ∀ i, Module.Dual ℂ (K i)) (t : ⨂[ℂ] i, K i) :
    tform w t = w i (ctr i w t) := by
  have : tform w = w i ∘ₗ ctr i w := by
    ext v
    simp only [LinearMap.compMultilinearMap_apply, LinearMap.comp_apply, tform_tprod, ctr_tprod,
      map_smul, smul_eq_mul]
    rw [Finset.prod_erase_mul _ _ (Finset.mem_univ i)]
  exact LinearMap.congr_fun this t

theorem comm_mapFactor_of_absIrr {G : Type} (i : ι) (a : G → Module.End ℂ (K i)) (ha : AbsIrr a)
    (Φ : Module.End ℂ (⨂[ℂ] i, K i)) (h : ∀ g, Φ ∘ₗ intersection_update_fsHerm_neg_one i (a g) = intersection_update_fsHerm_neg_one i (a g) ∘ₗ Φ)
    (f : Module.End ℂ (K i)) (x : ∀ i, K i) :
    Φ (intersection_update_fsHerm_neg_one i f (PiTensorProduct.tprod ℂ x)) = intersection_update_fsHerm_neg_one i f (Φ (PiTensorProduct.tprod ℂ x)) := by
  refine eq_of_tform fun w => ?_
  rw [tform_eq i, tform_eq i, ctr_mapFactor]
  congr 1
  let T : Module.End ℂ (K i) :=
    ctr i w ∘ₗ Φ ∘ₗ (PiTensorProduct.tprod ℂ (s := K)).toLinearMap x i
  have hT : ∀ z, T z = ctr i w (Φ (PiTensorProduct.tprod ℂ (Function.update x i z))) := fun z => rfl
  obtain ⟨c, hc⟩ := ha.2 T (fun g => by
    ext z
    have := LinearMap.congr_fun (h g) (PiTensorProduct.tprod ℂ (Function.update x i z))
    simp only [LinearMap.comp_apply, position_tprod, Function.update_self, Function.update_idem] at this
    simp only [LinearMap.comp_apply, hT, this, ctr_mapFactor])
  have h1 := hT (x i)
  rw [Function.update_eq_self] at h1
  rw [position_tprod, ← hT, ← h1, hc]
  simp

theorem comm_map (Φ : Module.End ℂ (⨂[ℂ] i, K i))
    (h : ∀ i (f : Module.End ℂ (K i)), Φ ∘ₗ intersection_update_fsHerm_neg_one i f = intersection_update_fsHerm_neg_one i f ∘ₗ Φ) (f : ∀ i, Module.End ℂ (K i)) :
    Φ ∘ₗ PiTensorProduct.map f = PiTensorProduct.map f ∘ₗ Φ := by
  have key : ∀ s : Finset ι,
      Φ ∘ₗ PiTensorProduct.map (fun i => if i ∈ s then f i else LinearMap.id) =
        PiTensorProduct.map (fun i => if i ∈ s then f i else LinearMap.id) ∘ₗ Φ := by
    intro s
    induction s using Finset.induction_on with
    | empty => simp
    | insert i s hi ih =>
      have : PiTensorProduct.map (fun j => if j ∈ insert i s then f j else LinearMap.id) =
          intersection_update_fsHerm_neg_one i (f i) ∘ₗ PiTensorProduct.map (fun i => if i ∈ s then f i else LinearMap.id) := by
        ext v
        simp only [LinearMap.compMultilinearMap_apply, LinearMap.comp_apply, PiTensorProduct.map_tprod,
          position_tprod]
        congr 1
        funext j
        by_cases hj : j = i
        · subst hj; simp [hi]
        · simp [hj]
      rw [this, ← LinearMap.comp_assoc, h, LinearMap.comp_assoc, ih, LinearMap.comp_assoc]
  simpa using key Finset.univ

theorem scalar_of_comm (ι : Type) [Fintype ι] (K : ι → Type) [∀ i, AddCommGroup (K i)] [∀ i, Module ℂ (K i)]
    (G : ι → Type) (a : ∀ i, G i → Module.End ℂ (K i)) (ha : ∀ i, AbsIrr (a i))
    (Φ : Module.End ℂ (⨂[ℂ] i, K i)) (h : ∀ i g, Φ ∘ₗ intersection_update_fsHerm_neg_one i (a i g) = intersection_update_fsHerm_neg_one i (a i g) ∘ₗ Φ) :
    ∃ c : ℂ, Φ = c • LinearMap.id := by
  by_cases hn : ∀ i, ∃ e : K i, e ≠ 0
  · choose e he using hn
    have : ∀ i, ∃ w : Module.Dual ℂ (K i), w (e i) = 1 := fun i =>
      Module.Projective.exists_dual_eq_one ℂ (he i)
    choose w hw using this
    refine ⟨tform w (Φ (PiTensorProduct.tprod ℂ e)), ?_⟩
    ext x
    have hc := comm_map Φ (fun i f => by
      ext y
      exact comm_mapFactor_of_absIrr i (a i) (ha i) Φ (h i) f y) (fun i => (w i).smulRight (x i))
    have hm : PiTensorProduct.map (fun i => (w i).smulRight (x i)) =
        (tform w).smulRight (PiTensorProduct.tprod ℂ x) := by
      ext v
      simp [tform_tprod, MultilinearMap.map_smul_univ]
    have := LinearMap.congr_fun hc (PiTensorProduct.tprod ℂ e)
    rw [hm] at this
    simpa [tform_tprod, hw] using this
  · push Not at hn
    obtain ⟨i, hi⟩ := hn
    refine ⟨0, ?_⟩
    ext x
    have : PiTensorProduct.tprod ℂ x = 0 := MultilinearMap.map_coord_zero _ i (hi _)
    simp [this]

end GlobalTheory.Chain.IoLift.Scal

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.SignedUnitaryGroupCompat
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open MeasureTheory Matrix GlobalTheory.Chain GlobalTheory.ChainFr GlobalTheory.Grid
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.PairLift

namespace GlobalTheory.SgnIdent

variable {D : D7}

theorem uj_neg_eq {A : Type} [CommRing A] {n : ℕ} (σ : A →+* A) (J : Matrix (Fin n) (Fin n) A) :
    Formalism.UG.UJ σ (-J) = Formalism.UG.UJ σ J := by
  ext g
  show Formalism.UG.cT σ (g : Matrix (Fin n) (Fin n) A) * (-J) * (g : Matrix (Fin n) (Fin n) A) = -J ↔
    Formalism.UG.cT σ (g : Matrix (Fin n) (Fin n) A) * J * (g : Matrix (Fin n) (Fin n) A) = J
  rw [Matrix.mul_neg, Matrix.neg_mul, neg_inj]

theorem uh_neg_eq {n : ℕ} (H : Matrix (Fin n) (Fin n) ℂ) : Formalism.QuantumDeterminants.UH (-H) = Formalism.QuantumDeterminants.UH H := by
  ext g
  simp only [Formalism.QuantumDeterminants.UH, Set.mem_setOf_eq, Matrix.mul_neg, Matrix.neg_mul, neg_inj]

theorem gramAt_neg_eq (V : HSp D) (τ : D.what₂.Tau) : gramAt D (neg V) τ = -gramAt D V τ := by
  ext i j; simp [gramAt, neg_gram]

theorem mem_GQ_sgn (ε : Bool) (V : HSp D) (g : GA D (sgn ε V)) : g ∈ GQ (sgn ε V) ↔ ofSgn ε V g ∈ GQ V := by
  cases ε
  · exact Iff.rfl
  · constructor
    · rintro ⟨x, hx, e⟩
      exact ⟨x, by rw [← uj_neg_eq]; exact hx, e⟩
    · rintro ⟨x, hx, e⟩
      exact ⟨x, by rw [← uj_neg_eq] at hx; exact hx, e⟩

theorem mem_GfC_sgn (ε : Bool) (V : HSp D) (g : GA D (sgn ε V)) : g ∈ GfC (sgn ε V) ↔ ofSgn ε V g ∈ GfC V := Iff.rfl

theorem mem_GinfC_sgn (ε : Bool) (V : HSp D) (g : GA D (sgn ε V)) : g ∈ GinfC (sgn ε V) ↔ ofSgn ε V g ∈ GinfC V :=
  Iff.rfl

theorem uh_sgn (ε : Bool) (V : HSp D) (τ : D.what₂.Tau) :
    Formalism.QuantumDeterminants.UH (gramAt D (sgn ε V) τ) = Formalism.QuantumDeterminants.UH (gramAt D V τ) := by
  cases ε
  · rfl
  · rw [gramAt_neg_eq, uh_neg_eq]

theorem lieAt_sgn (ε : Bool) (V : HSp D) (τ : D.what₂.Tau) : lieAt (sgn ε V) τ = lieAt V τ := by
  cases ε
  · rfl
  · ext X
    show Xᴴ * gramAt D (neg V) τ + gramAt D (neg V) τ * X = 0 ↔ Xᴴ * gramAt D V τ + gramAt D V τ * X = 0
    rw [gramAt_neg_eq, Matrix.mul_neg, Matrix.neg_mul, ← neg_add, neg_eq_zero]

theorem isAtTau_sgn (θ : InfFam D) (ε : Bool) (V : HSp D) (τ : D.what₂.Tau) (g : Matrix (Fin V.rank) (Fin V.rank) ℂ)
    (x : GA D (sgn ε V)) : IsAtTau θ (sgn ε V) τ g x ↔ IsAtTau θ V τ g (ofSgn ε V x) := Iff.rfl

theorem atTau_sgn (θ : InfFam D) (hθ : IsInfFam θ) (ε : Bool) (V : HSp D) (τ : D.what₂.Tau)
    (g : Matrix (Fin V.rank) (Fin V.rank) ℂ) : ofSgn ε V (atTau θ (sgn ε V) τ g) = atTau θ V τ g := by
  by_cases h : ∃ x, IsAtTau θ V τ g x
  · have h₁ : ∃ x, IsAtTau θ (sgn ε V) τ g x := by
      obtain ⟨x, hx⟩ := h
      refine ⟨(ofSgn ε V).symm x, (isAtTau_sgn θ ε V τ g _).2 ?_⟩
      rw [MulEquiv.apply_symm_apply]; exact hx
    have a : IsAtTau θ (sgn ε V) τ g (atTau θ (sgn ε V) τ g) := by
      unfold atTau; rw [dite_eq_left h₁]; exact h₁.choose_spec
    have b : IsAtTau θ V τ g (atTau θ V τ g) := by
      unfold atTau; rw [dite_eq_left h]; exact h.choose_spec
    exact GlobalTheory.Published.AutFin.Model.isAtTau_unique θ V hθ ((isAtTau_sgn θ ε V τ g _).1 a) b
  · have h₁ : ¬ ∃ x, IsAtTau θ (sgn ε V) τ g x := fun ⟨x, hx⟩ => h ⟨_, (isAtTau_sgn θ ε V τ g x).1 hx⟩
    have a : atTau θ (sgn ε V) τ g = 1 := by unfold atTau; rw [dite_eq_right h₁]
    have b : atTau θ V τ g = 1 := by unfold atTau; rw [dite_eq_right h]
    rw [a, b, map_one]

theorem meas_sgn (ε : Bool) (V : HSp D) (ν : Measure (GA D V)) (𝓕 : Set (GA D V)) (hν : ν.IsHaarMeasure)
    (h𝓕 : IsFundamentalDomain (GQ V) 𝓕 ν) :
    ∃ ν₁ : Measure (GA D (sgn ε V)), ν₁.IsHaarMeasure ∧ IsFundamentalDomain (GQ (sgn ε V)) (ofSgn ε V ⁻¹' 𝓕) ν₁ ∧
      ∀ φ : GA D V → ℂ, (IntegrableOn (fun g => φ (ofSgn ε V g)) (ofSgn ε V ⁻¹' 𝓕) ν₁ ↔ IntegrableOn φ 𝓕 ν) ∧
        ∫ g in ofSgn ε V ⁻¹' 𝓕, φ (ofSgn ε V g) ∂ν₁ = ∫ g in 𝓕, φ g ∂ν := by
  obtain ⟨-, -, -, hb, hg, -, -⟩ := GlobalTheory.Mem.AdelicGroupTop.adelic_unitary_topology D V
  obtain ⟨-, -, -, hb₁, hg₁, -, -⟩ := GlobalTheory.Mem.AdelicGroupTop.adelic_unitary_topology D (sgn ε V)
  let h : GA D (sgn ε V) ≃ₜ GA D V :=
    { toEquiv := (ofSgn ε V).toEquiv, continuous_toFun := continuous_ofSgn ε V,
      continuous_invFun := continuous_ofSgn_symm ε V }
  have me : MeasurableEmbedding (ofSgn ε V) := h.toMeasurableEquiv.measurableEmbedding
  have hm : Measurable (ofSgn ε V) := (continuous_ofSgn ε V).measurable
  have hm' : Measurable (ofSgn ε V).symm := (continuous_ofSgn_symm ε V).measurable
  have mp : MeasurePreserving (ofSgn ε V) (ν.map (ofSgn ε V).symm) ν := by
    refine ⟨hm, ?_⟩
    rw [Measure.map_map hm hm']
    have : (⇑(ofSgn ε V) ∘ ⇑(ofSgn ε V).symm) = id := funext fun x => (ofSgn ε V).apply_symm_apply x
    rw [this, Measure.map_id]
  refine ⟨ν.map (ofSgn ε V).symm,
    (ofSgn ε V).symm.isHaarMeasure_map ν (continuous_ofSgn_symm ε V) (continuous_ofSgn ε V), ?_, fun φ => ?_⟩
  · refine h𝓕.preimage_of_equiv mp.quasiMeasurePreserving
      (e := fun γ : GQ V => (⟨(ofSgn ε V).symm γ, (mem_GQ_sgn ε V _).2 (by rw [MulEquiv.apply_symm_apply]; exact γ.2)⟩ :
        GQ (sgn ε V))) ⟨fun a b hab => ?_, fun δ => ?_⟩ fun γ x => ?_
    · exact Subtype.ext ((ofSgn ε V).symm.injective (congrArg Subtype.val hab))
    · exact ⟨⟨ofSgn ε V δ, (mem_GQ_sgn ε V δ).1 δ.2⟩, Subtype.ext ((ofSgn ε V).symm_apply_apply δ)⟩
    · show ofSgn ε V ((ofSgn ε V).symm (γ : GA D V) * x) = (γ : GA D V) * ofSgn ε V x
      rw [map_mul, MulEquiv.apply_symm_apply]
  · exact ⟨mp.integrableOn_comp_preimage me, mp.setIntegral_preimage_emb me φ 𝓕⟩

theorem sgnLaw_holds : ∀ (D : D7) (θ : InfFam D), IsInfFam θ → ∀ (ε : Bool) (V : HSp D), SgnLaw θ ε V :=
  fun _ θ hθ ε V => ⟨mem_GQ_sgn ε V, mem_GfC_sgn ε V, mem_GinfC_sgn ε V, uh_sgn ε V, lieAt_sgn ε V,
    fun τ g => atTau_sgn θ hθ ε V τ g, fun ν 𝓕 hν h𝓕 => meas_sgn ε V ν 𝓕 hν h𝓕⟩

end GlobalTheory.SgnIdent

end
end

