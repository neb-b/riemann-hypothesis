module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1228
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0712
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CentreEnvelopingAlgebraCommuteRealLieSmoothing
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1247
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1251
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1300
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1277
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1303
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1184
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1306
public import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.UnitaryHaarProducts.Bundle0005
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0045
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0013
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0019
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0043
public import Development.AbelianVarietyTheory.Definitions.Divisors.AevalEqZeroOfMemConeIdeal
public import ReciprocityTheory.SemistableReduction.Bundle0025
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1188
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1293
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1301
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1072

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFiniteDimensionalSpaceAutomorphicSmoothing
section
noncomputable section

open NumberField GlobalTheory.CuspRep GlobalTheory.CuspQuot GlobalTheory.AutGrowth MeasureTheory Filter Topology

namespace GlobalTheory.AutGrowth.SmoothFinite

section

variable {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] {a : ℕ}

def stabL (φ : Sm E a) : Subgroup (GL (Fin a) (Af E)) where
  carrier := {k | finRep E a k φ = φ}
  mul_mem' {x y} hx hy := by
    simp only [Set.mem_ofPred_eq, map_mul, Module.End.mul_apply] at *
    rw [hy, hx]
  one_mem' := by simp
  inv_mem' {x} hx := by
    simp only [Set.mem_ofPred_eq] at *
    conv_lhs => rw [← hx]
    rw [← Module.End.mul_apply, ← map_mul]
    simp

theorem height_mul_le (c : GL (Fin a) (Cinf E)) : ∃ B : ℝ, 1 ≤ B ∧ ∀ y, height (y * c) ≤ B * height y := by
  refine ⟨1 + ‖rmul (toL c.val)‖ + ‖lmul (toL (c⁻¹).val)‖,
    by linarith [norm_nonneg (rmul (toL c.val)), norm_nonneg (lmul (toL (c⁻¹).val))], fun y => ?_⟩
  have h1 : toL (y * c).val = rmul (toL c.val) (toL y.val) := rfl
  have h2 : toL ((y * c)⁻¹).val = lmul (toL (c⁻¹).val) (toL (y⁻¹).val) := by
    rw [_root_.mul_inv_rev]; rfl
  have e1 := (rmul (toL c.val)).le_opNorm (toL y.val)
  have e2 := (lmul (toL (c⁻¹).val)).le_opNorm (toL (y⁻¹).val)
  have n1 := norm_nonneg (toL y.val)
  have n2 := norm_nonneg (toL (y⁻¹).val)
  have n3 := norm_nonneg (rmul (toL c.val))
  have n4 := norm_nonneg (lmul (toL (c⁻¹).val))
  unfold height
  rw [h1, h2]
  nlinarith

theorem growth_cptRep {φ : Sm E a} (hφ : φ.1 ∈ growth E a) (k : Kinf E a) : (cptRep E a k φ).1 ∈ growth E a := by
  intro g
  obtain ⟨C, N, hC⟩ := hφ g
  obtain ⟨B, hB, hB'⟩ := height_mul_le (Unitary.toUnits k : GL (Fin a) (Cinf E))
  have C0 : 0 ≤ C := by
    have := (norm_nonneg _).trans (hC 1)
    have hp : 0 < height (1 : GL (Fin a) (Cinf E)) ^ N :=
      pow_pos (by linarith [one_le_height (1 : GL (Fin a) (Cinf E))]) N
    exact nonneg_of_mul_nonneg_left this hp
  refine ⟨C * B ^ N, N, fun y => ?_⟩
  change ‖φ.1 (g * infGL E a y * infGL E a (Unitary.toUnits k))‖ ≤ _
  rw [mul_assoc, ← map_mul]
  refine (hC _).trans ?_
  rw [mul_assoc, ← mul_pow]
  exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by linarith [one_le_height (y * Unitary.toUnits k)]) (hB' y) N) C0

theorem spanK_induction {φ : Sm E a} {p : Sm E a → Prop} (h0 : p 0) (hadd : ∀ x y, p x → p y → p (x + y))
    (hsmul : ∀ (c : ℂ) x, p x → p (c • x)) (hk : ∀ k, p (cptRep E a k φ)) {w : Sm E a}
    (hw : w ∈ spanK E a φ) : p w := by
  induction hw using Submodule.span_induction with
  | mem x hx => obtain ⟨k, rfl⟩ := hx; exact hk k
  | zero => exact h0
  | add x y _ _ hx hy => exact hadd x y hx hy
  | smul c x _ hx => exact hsmul c x hx

theorem fin_cpt_comm (k : GL (Fin a) (Af E)) (c : Kinf E a) :
    finRep E a k * cptRep E a c = cptRep E a c * finRep E a k := by
  change rt E a (finGL E a k) * rt E a (infGL E a (Unitary.toUnits c)) =
    rt E a (infGL E a (Unitary.toUnits c)) * rt E a (finGL E a k)
  rw [← map_mul, ← map_mul, infGL_comm]

variable {φ : Sm E a}

theorem growth_mem (hφ : IsAutForm φ) {w : Sm E a} (hw : w ∈ spanK E a φ) : w.1 ∈ growth E a :=
  spanK_induction (p := fun w : Sm E a => w.1 ∈ growth E a) (zero_mem _)
    (fun x y hx hy => by rw [Submodule.coe_add]; exact add_mem hx hy)
    (fun c x hx => by rw [Submodule.coe_smul]; exact Submodule.smul_mem _ c hx)
    (fun k => growth_cptRep (φ := φ) hφ.growth k) hw

theorem left_mem (hφ : IsAutForm φ) {w : Sm E a} (hw : w ∈ spanK E a φ) :
    ∀ γ g, w.1 (ratGL E a γ * g) = w.1 g :=
  spanK_induction (p := fun w : Sm E a => ∀ γ g, w.1 (ratGL E a γ * g) = w.1 g) (fun _ _ => rfl)
    (fun x y hx hy γ g => by simp [hx γ g, hy γ g])
    (fun c x hx γ g => by simp [hx γ g])
    (fun k γ g => by
      change φ.1 (ratGL E a γ * g * infGL E a (Unitary.toUnits k)) = φ.1 (g * infGL E a (Unitary.toUnits k))
      rw [mul_assoc, hφ.left]) hw

theorem fixed_mem {k : GL (Fin a) (Af E)} (hk : k ∈ stabL φ) {w : Sm E a} (hw : w ∈ spanK E a φ) :
    finRep E a k w = w :=
  spanK_induction (p := fun w : Sm E a => finRep E a k w = w) (map_zero _)
    (fun x y hx hy => by rw [map_add (f := _), hx, hy])
    (fun c x hx => by rw [map_smul, hx])
    (fun c => by
      have hk' : finRep E a k φ = φ := hk
      rw [← Module.End.mul_apply, fin_cpt_comm, Module.End.mul_apply, hk']) hw

theorem killed_mem {z : Module.End ℂ (Sm E a)} (hz : z ∈ Zalg E a) (h0 : z φ = 0) {w : Sm E a}
    (hw : w ∈ spanK E a φ) : z w = 0 :=
  spanK_induction (p := fun w : Sm E a => z w = 0) (map_zero _)
    (fun x y hx hy => by rw [map_add (f := _), hx, hy, add_zero])
    (fun c x hx => by rw [map_smul, hx, smul_zero])
    (fun c => by
      rw [← Module.End.mul_apply, GlobalTheory.ZalgCpt.zalg_comm_cptRep E a c z hz, Module.End.mul_apply, h0, map_zero]) hw

variable (ν : Measure (Lie E a)) [ν.IsAddHaarMeasure] {α : Lie E a → ℂ}

theorem smoothing_add (hα : IsTest (invSet E a) α) (φ ψ : Sm E a) :
    smoothing ν α (φ + ψ).1 = smoothing ν α φ.1 + smoothing ν α ψ.1 := by
  funext x
  simp only [Pi.add_apply, smoothing]
  refine (integral_congr_ae (.of_forall fun y => ?_)).trans
    (integral_add (hα.integrable_mul ν isOpen_invSet (φ.2 x).continuousOn)
      (hα.integrable_mul ν isOpen_invSet (ψ.2 x).continuousOn))
  by_cases h : IsUnit (Matrix.of y) <;> simp [chart, h, mul_add]

theorem smoothing_smul (c : ℂ) (φ : Sm E a) :
    smoothing ν α (c • φ).1 = c • smoothing ν α φ.1 := by
  funext x
  simp only [Pi.smul_apply, smul_eq_mul, smoothing]
  refine (integral_congr_ae (.of_forall fun y => ?_)).trans (integral_const_mul c _)
  by_cases h : IsUnit (Matrix.of y) <;> simp [chart, h, mul_left_comm]

def smoothMap (hα : IsTest (invSet E a) α) (W : Submodule ℂ (Sm E a)) : W →ₗ[ℂ] Sm E a where
  toFun w := ⟨smoothing ν α w.1.1, GlobalTheory.T.realLieSmoothing_mem_smoothAdelicFunctions E a ν α hα w.1.1 w.1.2⟩
  map_add' w w' := Subtype.ext (smoothing_add ν hα w.1 w'.1)
  map_smul' c w := Subtype.ext (smoothing_smul ν c w.1)

theorem smoothMap_mem (hα : IsTest (invSet E a) α) (hK : KInv α) (hφ : IsAutForm φ) :
    smoothMap ν hα (spanK E a φ) ∈ mapsJ φ (stabL φ) := by
  refine ⟨⟨fun k w => ?_, fun w => ⟨?_, fun γ g => ?_, fun k hk => ?_⟩⟩, fun z hz h0 w => ?_⟩
  · apply Subtype.ext; funext g
    exact GlobalTheory.T.smoothing_right_translate_maxCompact E a ν α hK w.1.1 k g
  · intro l
    obtain ⟨β, hβ, e⟩ : ∃ β, IsTest (invSet E a) β ∧
        ((l.map (lie E a)).prod (smoothMap ν hα (spanK E a φ) w)).1 = smoothing ν β w.1.1 := by
      induction l with
      | nil => exact ⟨α, hα, rfl⟩
      | cons X l ih =>
        obtain ⟨β, hβ, e⟩ := ih
        refine ⟨dens X β, isTest_dens X hβ, funext fun g => ?_⟩
        rw [List.map_cons, List.prod_cons, Module.End.mul_apply, lie_apply, e]
        exact _root_.GlobalTheory.AutGrowth.lieD_smoothing_eq_dens E a ν β hβ w.1.1 w.1.2 X g
    rw [e]
    exact _root_.GlobalTheory.AutGrowth.smoothing_mem_growth E a ν β hβ w.1.1 (growth_mem hφ w.2)
  · show smoothing ν α w.1.1 (ratGL E a γ * g) = smoothing ν α w.1.1 g
    have hl := left_mem hφ w.2
    simp only [smoothing, chart, mul_assoc, hl]
  · apply Subtype.ext; funext g
    show smoothing ν α w.1.1 (g * finGL E a k) = smoothing ν α w.1.1 g
    have hw : (fun x => w.1.1 (x * finGL E a k)) = w.1.1 := congrArg Subtype.val (fixed_mem hk w.2)
    simp only [smoothing]
    rw [← chart_rt_fin, hw]
  · show (z ⟨smoothing ν α w.1.1, GlobalTheory.T.realLieSmoothing_mem_smoothAdelicFunctions E a ν α hα w.1.1 w.1.2⟩) = 0
    apply Subtype.ext
    rw [_root_.GlobalTheory.CentreSmooth.zalg_smoothing E a ν α hα w.1 _ z hz, killed_mem hz h0 w.2]
    funext g
    simp [smoothing, chart]

end

theorem exists_finite_space : GlobalTheory.Published.AutomorphicFormsFiniteGL → ∀ (E : Type) [Field E] [NumberField E]
    [_root_.NumberField.IsTotallyComplex E] (a : ℕ) (ν : Measure (Lie E a)) [ν.IsAddHaarMeasure] (φ : Sm E a), IsAutForm φ →
    ∃ V : Submodule ℂ (Sm E a), FiniteDimensional ℂ V ∧ V ≤ tame E a ∧ ∀ α, IsTest (invSet E a) α → KInv α →
      ∃ h : smoothing ν α φ.1 ∈ Sm E a, (⟨smoothing ν α φ.1, h⟩ : Sm E a) ∈ V := by
  intro hP E _ _ _ a ν _ φ hφ
  let w0 : spanK E a φ := ⟨φ, self_mem_spanK φ⟩
  haveI := _root_.GlobalTheory.AutGrowth.KilledFin.finiteDimensional_mapsJ hP E a φ hφ (stabL φ) hφ.level
  refine ⟨(mapsJ φ (stabL φ)).map (LinearMap.applyₗ w0), inferInstance, ?_, fun α hα hK =>
    ⟨GlobalTheory.T.realLieSmoothing_mem_smoothAdelicFunctions E a ν α hα φ.1 φ.2, smoothMap ν hα _, smoothMap_mem ν hα hK hφ, rfl⟩⟩
  rintro _ ⟨T, hT, rfl⟩
  exact (hT.1.2 w0).1

end GlobalTheory.AutGrowth.SmoothFinite
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFinitePartZeroNeOfIsVacuumOrientedModel
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links
open IsDedekindDomain NumberField Matrix MvPolynomial
open GlobalTheory.SignedHC GlobalTheory.ChiGrid Formalism.L2.DIV Formalism.L2.Ker GlobalTheory.FunObj
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section
open scoped TensorProduct

namespace GlobalTheory.VacNonzeroReal

variable {D : D7}

theorem continuous_finTmul (e : D.host.E) :
    Continuous fun x : Af D.host.F => (pairA D.host.F 0 x ⊗ₜ[D.host.F] e : AE D) := by
  haveI : IsModuleTopology (AF D.host.F) (AE D) := ⟨rfl⟩
  haveI : ContinuousSMul (AF D.host.F) (AE D) := IsModuleTopology.toContinuousSMul _ _
  have h1 : Continuous fun x : Af D.host.F => pairA D.host.F 0 x :=
    continuous_const.prodMk continuous_id
  have h2 : Continuous fun x : Af D.host.F => pairA D.host.F 0 x • ((1 : AF D.host.F) ⊗ₜ[D.host.F] e : AE D) :=
    h1.smul (continuous_const : Continuous fun _ : Af D.host.F => ((1 : AF D.host.F) ⊗ₜ[D.host.F] e : AE D))
  refine h2.congr fun x => ?_
  rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]

theorem infPart_finTmul (x : Af D.host.F) (e : D.host.E) :
    infPart D (pairA D.host.F 0 x ⊗ₜ[D.host.F] e) = 0 := by
  show (Algebra.TensorProduct.map (fstA D.host.F) (AlgHom.id D.host.F D.host.E)) (pairA D.host.F 0 x ⊗ₜ[D.host.F] e) = 0
  rw [Algebra.TensorProduct.map_tmul]
  show (0 : Ainf D.host.F) ⊗ₜ[D.host.F] _ = 0
  rw [TensorProduct.zero_tmul]

theorem finPart_infTmul (x : Ainf D.host.F) (e : D.host.E) :
    finPart D (pairA D.host.F x 0 ⊗ₜ[D.host.F] e) = 0 := by
  show (Algebra.TensorProduct.map (sndA D.host.F) (AlgHom.id D.host.F D.host.E)) (pairA D.host.F x 0 ⊗ₜ[D.host.F] e) = 0
  rw [Algebra.TensorProduct.map_tmul]
  show (0 : Af D.host.F) ⊗ₜ[D.host.F] _ = 0
  rw [TensorProduct.zero_tmul]


set_option synthInstance.maxHeartbeats 160000 in
set_option maxHeartbeats 1600000 in
theorem decomp_AE (V : AddSubgroup (AE D)) (hV : IsOpen (V : Set (AE D))) (z : AE D) :
    ∃ e : D.host.E, ∃ u ∈ V, infPart D u = 0 ∧ ∃ r : AE D, finPart D r = 0 ∧ z = incA D e + u + r := by
  induction z using TensorProduct.induction_on with
  | zero => exact ⟨0, 0, V.zero_mem, map_zero _, 0, map_zero _, by rw [map_zero, add_zero, add_zero]⟩
  | tmul a e =>
    set W : Set (Af D.host.F) := (fun x => (pairA D.host.F 0 x ⊗ₜ[D.host.F] e : AE D)) ⁻¹' V with hW
    have hWo : IsOpen W := hV.preimage (continuous_finTmul e)
    have hO : IsOpen {x : Af D.host.F | a.2 - x ∈ W} := hWo.preimage (continuous_const.sub continuous_id)
    obtain ⟨c, hc⟩ := Formalism.L2.SG.Pf.CondStd.dense_F.exists_mem_open hO
      ⟨a.2, by
        show (pairA D.host.F 0 (a.2 - a.2) ⊗ₜ[D.host.F] e : AE D) ∈ V
        rw [sub_self]
        have : pairA D.host.F 0 (0 : Af D.host.F) = 0 := rfl
        rw [this, TensorProduct.zero_tmul]
        exact V.zero_mem⟩
    refine ⟨algebraMap D.host.F D.host.E c * e, _, hc, infPart_finTmul _ _, _, finPart_infTmul (a.1 - algebraMap D.host.F (Ainf D.host.F) c) e, ?_⟩
    have hinc : incA D (algebraMap D.host.F D.host.E c * e) =
        algebraMap D.host.F (AF D.host.F) c ⊗ₜ[D.host.F] e := by
      show (1 : AF D.host.F) ⊗ₜ[D.host.F] (algebraMap D.host.F D.host.E c * e) = _
      have h1 : (1 : AF D.host.F) ⊗ₜ[D.host.F] (algebraMap D.host.F D.host.E c * e) =
          ((1 : AF D.host.F) ⊗ₜ[D.host.F] algebraMap D.host.F D.host.E c) * ((1 : AF D.host.F) ⊗ₜ[D.host.F] e) := by
        rw [Algebra.TensorProduct.tmul_mul_tmul, one_mul]
      have h2 : algebraMap D.host.F (AF D.host.F) c ⊗ₜ[D.host.F] e =
          (algebraMap D.host.F (AF D.host.F) c ⊗ₜ[D.host.F] (1 : D.host.E)) * ((1 : AF D.host.F) ⊗ₜ[D.host.F] e) := by
        rw [Algebra.TensorProduct.tmul_mul_tmul, one_mul, mul_one]
      rw [h1, h2, ← Algebra.TensorProduct.algebraMap_apply, ← Algebra.TensorProduct.algebraMap_apply']
    rw [hinc, ← TensorProduct.add_tmul, ← TensorProduct.add_tmul]
    congr 1
    refine Prod.ext ?_ ?_
    · show a.1 = algebraMap D.host.F (Ainf D.host.F) c + 0 + (a.1 - algebraMap D.host.F (Ainf D.host.F) c)
      abel
    · show a.2 = algebraMap D.host.F (Af D.host.F) c + (a.2 - algebraMap D.host.F (Af D.host.F) c) + 0
      abel
  | add x y hx hy =>
    obtain ⟨e, u, hu, hu0, r, hr0, hx⟩ := hx
    obtain ⟨e', u', hu', hu0', r', hr0', hy⟩ := hy
    refine ⟨e + e', u + u', V.add_mem hu hu', by rw [map_add (f := _), hu0, hu0', add_zero], r + r',
      by rw [map_add (f := _), hr0, hr0', add_zero], ?_⟩
    rw [hx, hy, map_add (f := _), add_add_add_comm _ r, add_add_add_comm (incA D e) u]

theorem continuous_single {m n : ℕ} (i : Fin m) (j : Fin n) :
    Continuous fun v : AE D => (Matrix.single i j v : Matrix (Fin m) (Fin n) (AE D)) := by
  refine continuous_pi fun a => continuous_pi fun b => ?_
  by_cases h : i = a ∧ j = b
  · obtain ⟨rfl, rfl⟩ := h
    simp only [Matrix.single_apply, and_self, if_true]
    exact continuous_id
  · have : ∀ v : AE D, (Matrix.single i j v : Matrix (Fin m) (Fin n) (AE D)) a b = 0 := fun v => by
      rw [Matrix.single_apply, if_neg h]
    simpa only [this] using continuous_const

def singleHom {m n : ℕ} (i : Fin m) (j : Fin n) : AE D →+ Matrix (Fin m) (Fin n) (AE D) where
  toFun v := Matrix.single i j v
  map_zero' := Matrix.single_zero i j
  map_add' x y := Matrix.single_add i j x y

theorem decomp_WO {S T : HSp D} (U : AddSubgroup (WO S T)) (hU : IsOpen (U : Set (WO S T))) (w : WO S T) :
    ∃ γ : Matrix (Fin T.rank) (Fin S.rank) D.host.E, ∃ u ∈ U, u.map (infPart D) = 0 ∧
      ∃ r : WO S T, r.map (finPart D) = 0 ∧ w = ratW T S γ + u + r := by
  classical
  have hV : ∀ i j, IsOpen ((U.comap (singleHom i j) : AddSubgroup (AE D)) : Set (AE D)) := fun i j =>
    hU.preimage (continuous_single i j)
  choose e u hu hu0 r hr0 hw using fun i j => decomp_AE _ (hV i j) (w i j)
  refine ⟨Matrix.of e, Matrix.of u, ?_, ?_, Matrix.of r, ?_, ?_⟩
  · rw [Matrix.matrix_eq_sum_single (Matrix.of u)]
    exact U.sum_mem fun i _ => U.sum_mem fun j _ => hu i j
  · ext i j
    simp [hu0 i j]
  · ext i j
    simp [hr0 i j]
  · ext i j
    rw [hw i j]
    rfl

theorem exists_finPart_zero_ne : ∀ {D : D7} (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (S T : HSp D) (sS : D.what₂.Tau → Matrix (Fin S.rank) (Fin S.rank) ℂ) (sT : D.what₂.Tau → Matrix (Fin T.rank) (Fin T.rank) ℂ) (LS : Set (Fin S.rank → D.host.E)) (LT : Set (Fin T.rank → D.host.E)) (f : WO S T → ℂ), IsVacO ψ θ S T sS sT LS LT f → ∃ w : WO S T, w.map (finPart D) = 0 ∧ f w ≠ 0 := by
  intro D ψ θ S T sS sT LS LT f hv
  have hne := GlobalTheory.TwistFactorProof.vac_ne_zero hv
  have hth : IsThetaFunO ψ S T f := hv.2.theta
  obtain ⟨w0, hw0⟩ : ∃ w, f w ≠ 0 := by
    by_contra h
    push_neg at h
    exact hne (funext h)
  obtain ⟨U, hUo, hU⟩ := hth.level
  obtain ⟨γ, u, huU, hu0, r, hr0, rfl⟩ := decomp_WO U hUo w0
  refine ⟨r, hr0, fun hfr => ?_⟩
  have hψ : ∀ a, ψ a ≠ 0 := fun a => by
    have : ψ a * ψ (-a) = 1 := by rw [← AddChar.map_add_eq_mul, add_neg_cancel, AddChar.map_zero_eq_one]
    exact left_ne_zero_of_mul_eq_one this
  rw [add_assoc, hth.quasi γ (u + r)] at hw0
  have hfur : f (u + r) ≠ 0 := right_ne_zero_of_mul hw0
  have h2 := congrFun (hU u huU hu0) r
  unfold heisO at h2
  rw [hfr, add_comm r u] at h2
  exact (mul_ne_zero (hψ _) hfur) h2

end GlobalTheory.VacNonzeroReal
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFixedComplexPointOfFixedFieldPoint
section
open CategoryTheory NumberField IsDedekindDomain Module Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.L2.Pj GlobalTheory.DualWeyl GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.CompHt GlobalTheory.DefPt ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD
open scoped Matrix Classical
open AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj ReciprocityTheory.ChartRestriction.G.Semi
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.FixedCx

open Cardinal

theorem mk_le_of_essFiniteType {R S : Type} [CommRing R] [CommRing S] [Algebra R S] [Algebra.EssFiniteType R S] :
    #S ≤ max #R ℵ₀ := by
  have h1 : #S ≤ #(Algebra.EssFiniteType.subalgebra R S) :=
    IsLocalization.cardinalMk_le (Algebra.EssFiniteType.submonoid R S)
  have h2 := Algebra.cardinalMk_adjoin_le R ((Algebra.EssFiniteType.finset R S : Finset S) : Set S)
  have h3 : #(((Algebra.EssFiniteType.finset R S : Finset S) : Set S)) ≤ ℵ₀ :=
    (Cardinal.lt_aleph0_of_finite _).le
  refine h1.trans (h2.trans ?_)
  exact max_le (max_le (le_max_left _ _) (h3.trans (le_max_right _ _))) (le_max_right _ _)

theorem nonempty_ringHom_complex (K : Type) [Field K] [CharZero K] (h : #K ≤ 𝔠) : Nonempty (K →+* ℂ) := by
  have hP1 : #(MvPolynomial ℝ K) ≤ 𝔠 := MvPolynomial.cardinalMk_le_max.trans
    (max_le (max_le h (Cardinal.mk_real).le) Cardinal.aleph0_le_continuum)
  have hP2 : 𝔠 ≤ #(MvPolynomial ℝ K) := by
    rw [← Cardinal.mk_real]
    exact Cardinal.mk_le_of_injective (MvPolynomial.X_injective (σ := ℝ) (R := K))
  have hF : #(FractionRing (MvPolynomial ℝ K)) = 𝔠 := (FractionRing.cardinalMk (MvPolynomial ℝ K)).trans (le_antisymm hP1 hP2)
  haveI : CharZero (FractionRing (MvPolynomial ℝ K)) :=
    charZero_of_injective_ringHom (f := (algebraMap (MvPolynomial ℝ K) (FractionRing (MvPolynomial ℝ K))).comp MvPolynomial.C)
      ((IsFractionRing.injective (MvPolynomial ℝ K) (FractionRing (MvPolynomial ℝ K))).comp (MvPolynomial.C_injective ℝ K))
  haveI : CharZero (AlgebraicClosure (FractionRing (MvPolynomial ℝ K))) := charZero_of_injective_ringHom (algebraMap (FractionRing (MvPolynomial ℝ K)) (AlgebraicClosure (FractionRing (MvPolynomial ℝ K)))).injective
  have hΩ1 : #(AlgebraicClosure (FractionRing (MvPolynomial ℝ K))) ≤ 𝔠 := (Algebra.IsAlgebraic.cardinalMk_le_max (FractionRing (MvPolynomial ℝ K)) (AlgebraicClosure (FractionRing (MvPolynomial ℝ K)))).trans
    (max_le hF.le Cardinal.aleph0_le_continuum)
  have hΩ2 : 𝔠 ≤ #(AlgebraicClosure (FractionRing (MvPolynomial ℝ K))) := hF ▸ Cardinal.mk_le_of_injective (algebraMap (FractionRing (MvPolynomial ℝ K)) (AlgebraicClosure (FractionRing (MvPolynomial ℝ K)))).injective
  have hΩ : #(AlgebraicClosure (FractionRing (MvPolynomial ℝ K))) = #ℂ := (le_antisymm hΩ1 hΩ2).trans Cardinal.mk_complex.symm
  obtain ⟨e⟩ := IsAlgClosed.ringEquiv_of_equiv_of_charZero (K := AlgebraicClosure (FractionRing (MvPolynomial ℝ K))) (L := ℂ)
    (by rw [hΩ, Cardinal.mk_complex]; exact Cardinal.aleph0_lt_continuum) (Cardinal.eq.1 hΩ)
  exact ⟨e.toRingHom.comp ((algebraMap (FractionRing (MvPolynomial ℝ K)) (AlgebraicClosure (FractionRing (MvPolynomial ℝ K)))).comp ((algebraMap (MvPolynomial ℝ K) (FractionRing (MvPolynomial ℝ K))).comp MvPolynomial.C))⟩

theorem cancel_spec_field {K L : Type} [Field K] [Field L] (φ : L →+* K) {X : Scheme.{0}} (a b : Sp L ⟶ X)
    (h : spMap φ ≫ a = spMap φ ≫ b) : a = b := by
  obtain ⟨⟨p, α⟩, rfl⟩ := (Scheme.SpecToEquivOfField L X).symm.surjective a
  obtain ⟨⟨q, β⟩, rfl⟩ := (Scheme.SpecToEquivOfField L X).symm.surjective b
  simp only [Scheme.SpecToEquivOfField_symm_apply] at h ⊢
  rw [← Category.assoc, ← Category.assoc, ← Spec.map_comp, ← Spec.map_comp] at h
  obtain ⟨e, he⟩ := GlobalTheory.SS.residue_embedding_unique _ _ h
  subst e
  simp only [Scheme.residueFieldCongr_refl, Iso.refl_hom, Category.id_comp] at he
  have : α = β := by
    ext c
    exact φ.injective (congrArg (fun g => g.hom c) he)
  rw [this]

end GlobalTheory.FixedCx


open GlobalTheory.FixedCx Cardinal in
theorem GlobalTheory.FixedCx.exists_fixed_complex_point : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (k : Type) [Field k] (x : Sp k ⟶ Xo.X) (ρ : Xo.X ⟶ Xo.X), x ≫ ρ = x → ∃ x' : Sp ℂ ⟶ Xo.X, x' ≫ ρ = x' := by
  intro E _ _ _ H Dw l Xo k _ x ρ hx
  obtain ⟨⟨p, φ⟩, rfl⟩ := (Scheme.SpecToEquivOfField k Xo.X).symm.surjective x
  simp only [Scheme.SpecToEquivOfField_symm_apply] at hx
  have hι : Xo.X.fromSpecResidueField p ≫ ρ = Xo.X.fromSpecResidueField p :=
    cancel_spec_field φ.hom _ _ (by rw [Category.assoc] at hx; exact hx)
  haveI := Xo.smooth
  haveI := SmoothOfRelativeDimension.smooth Dw.dim Xo.s
  obtain ⟨ψ, hψ⟩ := Spec.map_surjective (Xo.X.fromSpecResidueField p ≫ Xo.s)
  have hess := GlobalTheory.SS.essFiniteType_residueField_of_locallyOfFiniteType Xo.s p ψ hψ
  letI : Algebra (KA l) (Xo.X.residueField p) := ψ.hom.toAlgebra
  haveI : Algebra.EssFiniteType (KA l) (Xo.X.residueField p) := hess
  haveI : CharZero (KA l) := charZero_of_injective_ringHom (algebraMap ℚ (KA l)).injective
  haveI : CharZero (Xo.X.residueField p) := charZero_of_injective_ringHom ψ.hom.injective
  have hK : #(KA l) ≤ 𝔠 := (Cardinal.mk_subtype_le _).trans Cardinal.mk_complex.le
  have hc : #(Xo.X.residueField p) ≤ 𝔠 :=
    mk_le_of_essFiniteType.trans (max_le hK Cardinal.aleph0_le_continuum)
  obtain ⟨j⟩ := nonempty_ringHom_complex (Xo.X.residueField p) hc
  exact ⟨Spec.map (CommRingCat.ofHom j) ≫ Xo.X.fromSpecResidueField p, by rw [Category.assoc, hι]⟩
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFormOutsideImageIdealVanishingOnBoundary
section
open NumberField MvPolynomial ReciprocityTheory.MultiplicativeHeights CategoryTheory AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.ChowHt GlobalTheory.Adelic GlobalTheory.HSCore GlobalTheory.HSChoice GlobalTheory.HSShort

set_option autoImplicit false

namespace GlobalTheory.BoundaryForm

theorem exists_local_fun {Y : Scheme.{0}} [IrreducibleSpace Y] (Z : TopologicalSpace.Closeds Y) (hZ : Z ≠ ⊤) (y : Y) :
    ∃ (W : Y.Opens) (a : Γ(Y, W)), y ∈ W ∧ a ≠ 0 ∧ ∀ z ∈ Y.basicOpen a, z ∉ Z := by
  obtain ⟨_, ⟨W, hW, rfl⟩, hy, -⟩ :=
    Y.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ y) isOpen_univ
  have hne : ((Z : Set Y)ᶜ).Nonempty := Set.nonempty_compl.2 fun h => hZ (SetLike.coe_injective h)
  obtain ⟨z, hzW, hzZ⟩ := nonempty_preirreducible_inter W.isOpen Z.isClosed.isOpen_compl ⟨y, hy⟩ hne
  obtain ⟨a, ha, hz⟩ := IsAffineOpen.exists_basicOpen_le hW (V := Z.compl) ⟨z, hzZ⟩ hzW
  refine ⟨W, a, hy, ?_, fun w hw => ha hw⟩
  rintro rfl
  rw [Scheme.basicOpen_zero] at hz
  exact hz

theorem exists_form_vanishing : ∀ (F : Type) [Field F] [NumberField F] (T : Tuple F), T.IsGeometric → T.Birational →
    ∃ (d : ℕ) (g : MvPolynomial (Fin T.N) F), g.IsHomogeneous d ∧ g ∉ T.imageIdeal ∧
      ∀ (K : Type) [Field K] [Algebra F K] (x : T.Pt K), ptOf x.1 ∈ T.bd → aeval (T.coords x.1) g = 0 := by
  intro F _ _ T hG hB
  have hV := hG.alg.variety
  have := HeightExists.isIntegral hV
  have := isNoetherian_of_isProjOver hV.proj
  have hp := HeightExists.isPrime_imageIdeal hV
  choose W a hy ha hz using exists_local_fun T.bd hG.bd_ne
  choose d P Q hP _ _ hPn hval using fun y => GlobalTheory.T.exists_homogeneous_forms_quotient_birational_system F T.toLinSys hV hG.alg.bpf hB (W y) (a y)
  obtain ⟨s, hs⟩ := isCompact_univ.elim_finite_subcover (fun y => (W y : Set T.Y)) (fun y => (W y).isOpen)
    fun y _ => Set.mem_iUnion.2 ⟨y, hy y⟩
  refine ⟨∑ y ∈ s, d y, ∏ y ∈ s, P y, IsHomogeneous.prod s P d fun y _ => hP y, fun h => ?_, fun K _ _ x hx => ?_⟩
  · obtain ⟨y, -, h⟩ := Ideal.IsPrime.prod_mem_iff.1 h
    exact hPn y (ha y) h
  · obtain ⟨y, hys, hxy⟩ := Set.mem_iUnion₂.1 (hs (Set.mem_univ (ptOf x.1)))
    rw [map_prod]
    refine Finset.prod_eq_zero hys ?_
    have h0 : valR x.1 (W y) (a y) = 0 := by
      by_contra h
      exact hz y _ ((valR_ne_zero_iff x.1 hxy _).1 h) hx
    rw [← hval y K x hxy, h0, zero_mul]

end GlobalTheory.BoundaryForm
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteRationalPointsSupportDefiniteUnitaryTestFuStatement
section
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finite_rationalPoints_support_definiteUnitary_testFunction : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E], Unr E → ∀ n : ℕ, 1 ≤ n → ∀ (S : Set (Pl E)), IsSection S → ∀ (K' : ∀ w : Pl E, Subgroup (UL n w)), IsLevelFam (fun w : Pl E => MonoidHom.id (UL n w)) (KL n) K' → ∀ f : ∀ w : Pl E, UL n w → ℂ, IsTest (KL n) K' f → ∀ x : finU (E := E) (n := n), {γ : UE E n | globFn S f (x⁻¹ * finPt γ * x) ≠ 0}.Finite := by
  first | exact @GlobalTheory.BCT.SuppFin.suppFin | exact GlobalTheory.BCT.SuppFin.suppFin | (intros; apply GlobalTheory.BCT.SuppFin.suppFin <;> assumption)
end

