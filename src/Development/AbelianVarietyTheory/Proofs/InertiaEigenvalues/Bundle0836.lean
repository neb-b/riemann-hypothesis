module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0292
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0495
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1516
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1678
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1176
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1252
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1247
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0040
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsAddHaarMeasureVolumeLie
public import GroundTheory.AutomorphicForms.ReductionFinite
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DecaysOfMemSmoothSpan
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0819
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0824
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0303
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsEigenSysOfHeckeLin
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0329
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0104
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.UnivChar
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0029
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0820

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.RapidKernelIntegralConjLieDerivativeMemSpan
section
open NumberField Matrix MeasureTheory GlobalTheory.CuspRep GlobalTheory.CuspRep.CuspidalL2GL GlobalTheory.UnitaryBC GroundTheory.Global GroundTheory.Global.IdeleGroup
open scoped Pointwise

noncomputable section

namespace GlobalTheory.MSpanDecay.RapidLie

variable {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] {a : ℕ}


omit [_root_.NumberField.IsTotallyComplex E] in
theorem norm_entry_le (A : Matrix (Fin a) (Fin a) (Cinf E)) (i j : Fin a) : ‖A i j‖ ≤ ‖toL A‖ :=
  (norm_le_pi_norm (toL A i) j).trans (norm_le_pi_norm (toL A) i)


omit [_root_.NumberField.IsTotallyComplex E] in
theorem norm_toL_mul_le (A B : Matrix (Fin a) (Fin a) (Cinf E)) : ‖toL (A * B)‖ ≤ a * (‖toL A‖ * ‖toL B‖) := by
  refine (pi_norm_le_iff_of_nonneg (by positivity)).2 fun i => (pi_norm_le_iff_of_nonneg (by positivity)).2 fun j => ?_
  change ‖(A * B) i j‖ ≤ _
  rw [Matrix.mul_apply]
  refine (norm_sum_le _ _).trans ((Finset.sum_le_card_nsmul _ _ (‖toL A‖ * ‖toL B‖) fun k _ => ?_).trans ?_)
  · exact (norm_mul_le _ _).trans (mul_le_mul (norm_entry_le A i k) (norm_entry_le B k j) (norm_nonneg _) (norm_nonneg _))
  · simp


omit [_root_.NumberField.IsTotallyComplex E] in
theorem measurable_comp_of_continuousOn {X : Type} [MeasurableSpace X] {f : Lie E a → ℂ}
    (hf : ContinuousOn f (invSet E a)) {φ : X → Lie E a} (hφ : Measurable φ) (hφ' : ∀ x, φ x ∈ invSet E a) :
    Measurable fun x => f (φ x) := by
  have e : (fun x => f (φ x)) = (invSet E a).restrict f ∘ fun x => (⟨φ x, hφ' x⟩ : invSet E a) := rfl
  rw [e]
  exact hf.restrict.measurable.comp (hφ.subtype_mk)


omit [_root_.NumberField.IsTotallyComplex E] in
theorem measurable_inv {X : Type} [MeasurableSpace X] {γ : X → GL (Fin a) (Cinf E)}
    (hγ : Measurable fun x => toL (γ x).val) : Measurable fun x => toL ((γ x)⁻¹).val := by
  have key : ∀ y : GL (Fin a) (Cinf E), ((y⁻¹ : GL (Fin a) (Cinf E)) : Matrix (Fin a) (Fin a) (Cinf E)) =
      (fun w => ((y : Matrix (Fin a) (Fin a) (Cinf E)).det w)⁻¹) • (y : Matrix (Fin a) (Fin a) (Cinf E)).adjugate := by
    intro y
    refine Units.inv_eq_of_mul_eq_one_left ?_
    have hu : IsUnit (y : Matrix (Fin a) (Fin a) (Cinf E)).det := (Matrix.isUnit_iff_isUnit_det _).1 y.isUnit
    have h1 : (fun w => ((y : Matrix (Fin a) (Fin a) (Cinf E)).det w)⁻¹) * (y : Matrix (Fin a) (Fin a) (Cinf E)).det = 1 := by
      funext w
      have hw : (y : Matrix (Fin a) (Fin a) (Cinf E)).det w ≠ 0 :=
        ((Pi.evalRingHom (fun _ : InfinitePlace E => ℂ) w).isUnit_map hu).ne_zero
      exact inv_mul_cancel₀ hw
    rw [Matrix.smul_mul, Matrix.adjugate_mul, smul_smul, h1, one_smul]
  have e : (fun x => toL ((γ x)⁻¹).val) = fun x => toL ((fun w => ((γ x : Matrix (Fin a) (Fin a) (Cinf E)).det w)⁻¹) •
      (γ x : Matrix (Fin a) (Fin a) (Cinf E)).adjugate) := funext fun x => congrArg toL (key (γ x))
  rw [e]
  have hdet : Measurable fun x => (γ x : Matrix (Fin a) (Fin a) (Cinf E)).det :=
    (contDiff_det (E := E) (a := a)).continuous.measurable.comp hγ
  have hadjc : Continuous fun m : Lie E a => (toL (Matrix.of m).adjugate : Lie E a) :=
    Continuous.matrix_adjugate continuous_id
  have hadj : Measurable fun x => toL (γ x : Matrix (Fin a) (Fin a) (Cinf E)).adjugate :=
    hadjc.measurable.comp hγ
  have hc : Measurable fun x => (fun w => ((γ x : Matrix (Fin a) (Fin a) (Cinf E)).det w)⁻¹ : Cinf E) :=
    Measurable.of_eval fun w => ((measurable_pi_apply w).comp hdet).inv
  exact (continuous_smul (M := Cinf E) (X := Lie E a)).measurable.comp (hc.prodMk hadj)

end GlobalTheory.MSpanDecay.RapidLie

namespace GlobalTheory.MSpanDecay.RapidLie

variable {E : Type} [Field E] [NumberField E] {a : ℕ}

theorem measurable_mul {X : Type} [MeasurableSpace X] {A B : X → Lie E a} (hA : Measurable A) (hB : Measurable B) :
    Measurable fun x => toL (Matrix.of (A x) * Matrix.of (B x)) := by
  refine Measurable.of_eval fun i => Measurable.of_eval fun j => Measurable.of_eval fun w => ?_
  have e : (fun x => toL (Matrix.of (A x) * Matrix.of (B x)) i j w) = fun x => ∑ k, A x i k w * B x k j w := by
    funext x; simp [Matrix.mul_apply, Finset.sum_apply]
  rw [e]
  exact Finset.measurable_sum _ fun k _ =>
    ((measurable_pi_apply w).comp ((measurable_pi_apply k).comp ((measurable_pi_apply i).comp hA))).mul
      ((measurable_pi_apply w).comp ((measurable_pi_apply j).comp ((measurable_pi_apply k).comp hB)))

theorem measurable_conj {X : Type} [MeasurableSpace X] {γ : X → GL (Fin a) (Cinf E)}
    (hγ : Measurable fun x => toL (γ x).val) (Y : Lie E a) :
    Measurable fun x => toL (((γ x)⁻¹).val * Matrix.of Y * (γ x).val) :=
  measurable_mul (measurable_mul (measurable_inv hγ) measurable_const) hγ

end GlobalTheory.MSpanDecay.RapidLie

namespace GlobalTheory.MSpanDecay.RapidLie

variable {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] {a : ℕ}


omit [_root_.NumberField.IsTotallyComplex E] in
theorem norm_conj_le (y : GL (Fin a) (Cinf E)) (Y : Lie E a) :
    ‖toL ((y⁻¹).val * Matrix.of Y * y.val)‖ ≤ a * a * ‖Y‖ * height y ^ 2 := by
  have h1 : ‖toL y.val‖ ≤ height y := by unfold height; linarith [norm_nonneg (toL (y⁻¹).val)]
  have h2 : ‖toL (y⁻¹).val‖ ≤ height y := by unfold height; linarith [norm_nonneg (toL y.val)]
  have h3 : ‖toL ((y⁻¹).val * Matrix.of Y)‖ ≤ a * (‖toL (y⁻¹).val‖ * ‖Y‖) := norm_toL_mul_le _ _
  calc ‖toL ((y⁻¹).val * Matrix.of Y * y.val)‖ ≤ a * (‖toL ((y⁻¹).val * Matrix.of Y)‖ * ‖toL y.val‖) :=
        norm_toL_mul_le _ _
    _ ≤ a * ((a * (height y * ‖Y‖)) * height y) := by
        have h4 : ‖toL ((y⁻¹).val * Matrix.of Y)‖ ≤ a * (height y * ‖Y‖) :=
          h3.trans (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right h2 (norm_nonneg _)) (Nat.cast_nonneg a))
        exact mul_le_mul_of_nonneg_left (mul_le_mul h4 h1 (norm_nonneg _) ((norm_nonneg _).trans h4)) (Nat.cast_nonneg a)
    _ = a * a * ‖Y‖ * height y ^ 2 := by ring

theorem lieD_eq_sum {ι : Type} [Fintype ι] (b : Module.Basis ι ℝ (Lie E a)) (W : Lie E a) (G : GA E a → ℂ)
    (g : GA E a) : lieD W G g = ∑ j, ((b.repr W j : ℝ) : ℂ) * lieD (b j) G g := by
  unfold lieD
  conv_lhs => rw [← b.sum_repr W]
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sum]
  simp only [map_smul, Complex.real_smul]

theorem measurable_height {X : Type} [MeasurableSpace X] {γ : X → GL (Fin a) (Cinf E)}
    (hγ : Measurable fun x => toL (γ x).val) : Measurable fun x => height (γ x) := by
  have e : (fun x => height (γ x)) = fun x => 1 + ‖toL (γ x).val‖ + ‖toL ((γ x)⁻¹).val‖ := rfl
  rw [e]
  exact (measurable_const.add hγ.norm).add (measurable_inv hγ).norm

end GlobalTheory.MSpanDecay.RapidLie

namespace GlobalTheory.MSpanDecay


open RapidLie in
theorem integral_lieD_conj_mem_kSpan : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a : ℕ) (G : GA E a → ℂ) (X : Type) [MeasurableSpace X] (ν : Measure X) [SFinite ν] (k : X → ℂ) (γ : X → GL (Fin a) (Cinf E)) (Y : Lie E a), GlobalTheory.JSW.IsRapidInf ν k γ → GlobalTheory.MSpanDecay.Good G → (fun g : GA E a => ∫ x, k x * lieD (toL (((γ x)⁻¹).val * Matrix.of Y * (γ x).val)) G (g * infGL E a (γ x)) ∂ν) ∈ GlobalTheory.MSpanDecay.kSpan E a := by
  intro E _ _ _ a G X _ ν _ k γ Y hk hG
  obtain ⟨hkm, hγm, hint⟩ := hk
  have hγ : Measurable fun x => toL (γ x).val := hγm
  let b := Module.finBasis ℝ (Lie E a)
  let L : Fin (Module.finrank ℝ (Lie E a)) → Lie E a →L[ℝ] ℝ := fun j => LinearMap.toContinuousLinearMap (b.coord j)
  let W : X → Lie E a := fun x => toL (((γ x)⁻¹).val * Matrix.of Y * (γ x).val)
  let c : Fin (Module.finrank ℝ (Lie E a)) → X → ℂ := fun j x => ((L j (W x) : ℝ) : ℂ)
  have hW : Measurable W := measurable_conj hγ Y
  have hc : ∀ j, Measurable (c j) := fun j => Complex.measurable_ofReal.comp ((L j).continuous.measurable.comp hW)
  set D : Fin (Module.finrank ℝ (Lie E a)) → ℝ := fun j => ‖L j‖ * (a * a * ‖Y‖) with hD
  have hD0 : ∀ j, 0 ≤ D j := fun j => by positivity
  have hcb : ∀ j x, ‖c j x‖ ≤ D j * height (γ x) ^ 2 := by
    intro j x
    have h := (L j).le_opNorm (W x)
    rw [Complex.norm_real]
    refine h.trans ?_
    rw [hD, mul_assoc]
    exact mul_le_mul_of_nonneg_left (norm_conj_le (γ x) Y) (norm_nonneg _)
  have hG' : ∀ j, Good (lieD (b j) G) := fun j => hG.derivative _
  have hrap : ∀ j, GlobalTheory.JSW.IsRapidInf ν (fun x => k x * c j x) γ := by
    intro j
    refine ⟨hkm.mul (hc j), hγm, fun N => ?_⟩
    refine Integrable.mono' ((hint (N + 2)).const_mul (D j))
      (((hkm.mul (hc j)).norm.mul ((measurable_height hγ).pow_const N)).aestronglyMeasurable)
      (ae_of_all _ fun x => ?_)
    have h1 := one_le_height (γ x)
    have hp : 0 ≤ height (γ x) ^ N := by positivity
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity), norm_mul]
    calc ‖k x‖ * ‖c j x‖ * height (γ x) ^ N ≤ ‖k x‖ * (D j * height (γ x) ^ 2) * height (γ x) ^ N := by
          gcongr; exact hcb j x
      _ = D j * (‖k x‖ * height (γ x) ^ (N + 2)) := by ring
  have hmeasG : ∀ j g, Measurable fun x => lieD (b j) G (g * infGL E a (γ x)) := by
    intro j g
    have e : (fun x => lieD (b j) G (g * infGL E a (γ x))) = fun x => chart (lieD (b j) G) g (toL (γ x).val) :=
      funext fun x => (chart_val _ g (γ x)).symm
    rw [e]
    exact measurable_comp_of_continuousOn (((hG' j).mem_Sm g).continuousOn) hγ fun x => val_mem_invSet (γ x)
  have hintj : ∀ j g, Integrable (fun x => k x * c j x * lieD (b j) G (g * infGL E a (γ x))) ν := by
    intro j g
    obtain ⟨C, N, hCN⟩ := (hG' j).growth g
    refine Integrable.mono' ((hint (N + 2)).const_mul (D j * |C|))
      (((hkm.mul (hc j)).mul (hmeasG j g)).aestronglyMeasurable) (ae_of_all _ fun x => ?_)
    have h1 := one_le_height (γ x)
    have hp : 0 ≤ height (γ x) ^ N := by positivity
    have hg : ‖lieD (b j) G (g * infGL E a (γ x))‖ ≤ |C| * height (γ x) ^ N :=
      (hCN (γ x)).trans (mul_le_mul_of_nonneg_right (le_abs_self C) hp)
    rw [norm_mul, norm_mul]
    calc ‖k x‖ * ‖c j x‖ * ‖lieD (b j) G (g * infGL E a (γ x))‖
        ≤ ‖k x‖ * (D j * height (γ x) ^ 2) * (|C| * height (γ x) ^ N) := by
          gcongr
          · exact hcb j x
      _ = D j * |C| * (‖k x‖ * height (γ x) ^ (N + 2)) := by ring
  have e : (fun g : GA E a => ∫ x, k x * lieD (toL (((γ x)⁻¹).val * Matrix.of Y * (γ x).val)) G
      (g * infGL E a (γ x)) ∂ν) =
      ∑ j, fun g : GA E a => ∫ x, k x * c j x * lieD (b j) G (g * infGL E a (γ x)) ∂ν := by
    funext g
    rw [Finset.sum_apply, ← integral_finsetSum _ fun j _ => hintj j g]
    congr 1
    funext x
    rw [lieD_eq_sum b, Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    exact (mul_assoc (k x) (c j x) _).symm
  rw [e]
  exact Submodule.sum_mem _ fun j _ => Submodule.subset_span ⟨X, inferInstance, ν, inferInstance, _, γ, _, hrap j, hG' j, rfl⟩

end GlobalTheory.MSpanDecay
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SelfDualLatticeIndexSplitPlaceEqMul
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
namespace GlobalTheory.SplitLatIdx

theorem relIndex_map_of_proj {X Y : Type} [AddCommGroup X] [AddCommGroup Y] (A : AddSubgroup X) (φ P : X →+ X)
    (pr : X →+ Y) (hK : ∀ x, pr x = 0 → P x = 0) (hPA : ∀ a ∈ A, P a ∈ A)
    (hφ : ∀ x, φ x - P (φ x) = x - P x) (hc : ∀ x, P (φ x) = φ (P x)) :
    (A.map φ).relIndex A = ((A.map φ).map pr).relIndex (A.map pr) := by
  rw [← AddSubgroup.relIndex_comap ((A.map φ).map pr) pr A, ← AddSubgroup.inf_relIndex_right (A.map φ) A,
    ← AddSubgroup.inf_relIndex_right (((A.map φ).map pr).comap pr) A]
  congr 1
  ext x
  simp only [AddSubgroup.mem_inf, AddSubgroup.mem_comap]
  refine ⟨fun h => ⟨⟨x, h.1, rfl⟩, h.2⟩, ?_⟩
  rintro ⟨⟨y, ⟨a, ha, rfl⟩, hy⟩, hx⟩
  refine ⟨⟨a + (x - φ a), ?_, ?_⟩, hx⟩
  · have hPz : P (x - φ a) = 0 := hK _ (by rw [map_sub, hy, sub_self])
    have hz : x - φ a = (x - P x) - (a - P a) := by
      calc x - φ a = (x - φ a) - P (x - φ a) := by rw [hPz, sub_zero]
        _ = (x - P x) - (φ a - P (φ a)) := by rw [map_sub]; abel
        _ = _ := by rw [hφ a]
    refine add_mem ha ?_
    rw [hz]
    exact sub_mem (sub_mem hx (hPA x hx)) (sub_mem ha (hPA a ha))
  · have hPz : P (x - φ a) = 0 := hK _ (by rw [map_sub, hy, sub_self])
    have h1 := hφ (x - φ a)
    simp only [hc, hPz, map_zero, sub_zero] at h1
    rw [map_add (f := _), h1]
    abel

end GlobalTheory.SplitLatIdx

namespace GlobalTheory.SplitLatIdx


set_option maxHeartbeats 1600000 in
theorem latIndex_split : ∀ (D : D7) (T : HSp D) (v : HeightOneSpectrum (𝓞 D.host.F)) (w w' : HeightOneSpectrum (𝓞 D.host.E)) (h : w.under (𝓞 D.host.F) = v) (h' : w'.under (𝓞 D.host.F) = v), IsSplit (E := D.host.E) v → w ≠ w' → ∀ g : GlobalTheory.FinZeta.Gv T v, latIndex T (GlobalTheory.FinZeta.embV T v g) = GlobalTheory.LocKerMod.idxAt T w h g * GlobalTheory.LocKerMod.idxAt T w' h' g := by
  intro D T v w w' h h' hv hne g
  classical
  obtain ⟨w'', -, hu, -⟩ := GlobalTheory.LFun.SplitChart.exists_conj_place (isCMExt_host D) h hv
  have hover : ∀ u : HeightOneSpectrum (𝓞 D.host.E), u.under (𝓞 D.host.F) = v → u = w ∨ u = w' := by
    intro u hu0
    rcases (hu u).1 hu0 with e | e
    · exact Or.inl e
    · rcases (hu w').1 h' with e' | e'
      · exact absurd e'.symm hne
      · exact Or.inr (e.trans e'.symm)
  set M := finMat D.sp.cm.sig T.gram (GlobalTheory.FinZeta.embV T v g) with hMdef
  have hcomp : ∀ (u : HeightOneSpectrum (𝓞 D.host.E)) (y : Fin T.rank → Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F ⊗[D.host.F] D.host.E) (i : Fin T.rank),
      GlobalTheory.LFun.compAt D.host.F u ((M *ᵥ y) i) = (M.map (GlobalTheory.LFun.compAt D.host.F u) *ᵥ fun j => GlobalTheory.LFun.compAt D.host.F u (y j)) i :=
    fun u y i => RingHom.map_mulVec _ M y i
  have hMw : ∀ (u : HeightOneSpectrum (𝓞 D.host.E)) (hh : u.under (𝓞 D.host.F) = v),
      M.map (GlobalTheory.LFun.compAt D.host.F u) = (GlobalTheory.LFun.locMat D.sp.cm.sig T.gram hh g).1 := by
    intro u hh
    have e := GlobalTheory.LFun.finMat_map_compAt D.sp.cm.sig T.gram hh (GlobalTheory.FinZeta.embV T v g)
    rw [proj_emb_self] at e
    exact e
  have hMu : ∀ u : HeightOneSpectrum (𝓞 D.host.E), u.under (𝓞 D.host.F) ≠ v → M.map (GlobalTheory.LFun.compAt D.host.F u) = 1 := by
    intro u hh
    have e := GlobalTheory.LFun.finMat_map_compAt D.sp.cm.sig T.gram (rfl : u.under (𝓞 D.host.F) = _) (GlobalTheory.FinZeta.embV T v g)
    rw [proj_emb_ne _ _ hh, map_one, Units.val_one] at e
    exact e
  set ε : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F ⊗[D.host.F] D.host.E := GlobalTheory.LFun.singleAt D.host.F w 1 + GlobalTheory.LFun.singleAt D.host.F w' 1 with hεdef
  have hεw : GlobalTheory.LFun.compAt D.host.F w ε = 1 := by
    rw [hεdef, map_add (f := _), GlobalTheory.LFun.compAt_singleAt, GlobalTheory.LFun.compAt_singleAt_ne hne, add_zero]
  have hεw' : GlobalTheory.LFun.compAt D.host.F w' ε = 1 := by
    rw [hεdef, map_add (f := _), GlobalTheory.LFun.compAt_singleAt, GlobalTheory.LFun.compAt_singleAt_ne (Ne.symm hne), zero_add]
  have hεu : ∀ u, u ≠ w → u ≠ w' → GlobalTheory.LFun.compAt D.host.F u ε = 0 := by
    intro u h1 h2
    rw [hεdef, map_add (f := _), GlobalTheory.LFun.compAt_singleAt_ne h1, GlobalTheory.LFun.compAt_singleAt_ne h2, add_zero]
  have hεint : ε ∈ intAE D :=
    add_mem (GlobalTheory.LFun.singleAt_mem_intAE (one_mem _)) (GlobalTheory.LFun.singleAt_mem_intAE (one_mem _))
  let pr : (Fin T.rank → Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F ⊗[D.host.F] D.host.E) →+
      (Fin T.rank → w.adicCompletion D.host.E) × (Fin T.rank → w'.adicCompletion D.host.E) :=
    AddMonoidHom.mk' (fun x => (fun i => GlobalTheory.LFun.compAt D.host.F w (x i), fun i => GlobalTheory.LFun.compAt D.host.F w' (x i)))
      (fun x y => by ext i <;> simp)
  let P : (Fin T.rank → Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F ⊗[D.host.F] D.host.E) →+ (Fin T.rank → Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F ⊗[D.host.F] D.host.E) :=
    AddMonoidHom.mk' (fun x i => ε * x i) (fun x y => by funext i; simp [mul_add])
  let φ := M.mulVecLin.toAddMonoidHom
  have hφa : ∀ x, φ x = M *ᵥ x := fun x => rfl
  have hK : ∀ x, pr x = 0 → P x = 0 := by
    intro x hx
    have h1 : ∀ i, GlobalTheory.LFun.compAt D.host.F w (x i) = 0 := fun i => congrFun (congrArg Prod.fst hx) i
    have h2 : ∀ i, GlobalTheory.LFun.compAt D.host.F w' (x i) = 0 := fun i => congrFun (congrArg Prod.snd hx) i
    funext i
    refine GlobalTheory.LFun.compAt_ext fun u => ?_
    show GlobalTheory.LFun.compAt D.host.F u (ε * x i) = GlobalTheory.LFun.compAt D.host.F u 0
    rw [map_mul, map_zero]
    by_cases e1 : u = w
    · subst e1; rw [h1 i, mul_zero]
    by_cases e2 : u = w'
    · subst e2; rw [h2 i, mul_zero]
    rw [hεu u e1 e2, zero_mul]
  have hPA : ∀ a ∈ Formalism.L2.NTheta.LamHat T, P a ∈ Formalism.L2.NTheta.LamHat T :=
    fun a ha => (GlobalTheory.LatDual.lamHat_selfDual_and_module T).2 ε hεint a ha
  have hφ : ∀ x, φ x - P (φ x) = x - P x := by
    intro x
    funext i
    refine GlobalTheory.LFun.compAt_ext fun u => ?_
    show GlobalTheory.LFun.compAt D.host.F u ((M *ᵥ x) i - ε * (M *ᵥ x) i) = GlobalTheory.LFun.compAt D.host.F u (x i - ε * x i)
    rw [map_sub, map_sub, map_mul, map_mul]
    by_cases e : u = w ∨ u = w'
    · have : GlobalTheory.LFun.compAt D.host.F u ε = 1 := by rcases e with rfl | rfl; exacts [hεw, hεw']
      rw [this, one_mul, one_mul, sub_self, sub_self]
    · push_neg at e
      have hv' : u.under (𝓞 D.host.F) ≠ v := fun hh => by rcases hover u hh with e' | e' <;> [exact e.1 e'; exact e.2 e']
      rw [hεu u e.1 e.2, zero_mul, zero_mul, hcomp, hMu u hv', Matrix.one_mulVec]
  have hc : ∀ x, P (φ x) = φ (P x) := by
    intro x
    show (fun i => ε * (M *ᵥ x) i) = M *ᵥ (fun j => ε * x j)
    have e : (fun j => ε * x j) = ε • x := rfl
    rw [e, Matrix.mulVec_smul]
    rfl
  have hprφ : ∀ y, pr (φ y) = ((GlobalTheory.LFun.locMat D.sp.cm.sig T.gram h g).1 *ᵥ fun i => GlobalTheory.LFun.compAt D.host.F w (y i),
      (GlobalTheory.LFun.locMat D.sp.cm.sig T.gram h' g).1 *ᵥ fun i => GlobalTheory.LFun.compAt D.host.F w' (y i)) := by
    intro y
    refine Prod.ext (funext fun i => ?_) (funext fun i => ?_)
    · show GlobalTheory.LFun.compAt D.host.F w ((M *ᵥ y) i) = _
      rw [hcomp, hMw w h]
    · show GlobalTheory.LFun.compAt D.host.F w' ((M *ᵥ y) i) = _
      rw [hcomp, hMw w' h']
  have hsg : ∀ (x : Fin T.rank → w.adicCompletion D.host.E) (x' : Fin T.rank → w'.adicCompletion D.host.E),
      pr (fun i => GlobalTheory.LFun.singleAt D.host.F w (x i) + GlobalTheory.LFun.singleAt D.host.F w' (x' i)) = (x, x') := by
    intro x x'
    refine Prod.ext (funext fun i => ?_) (funext fun i => ?_)
    · show GlobalTheory.LFun.compAt D.host.F w (GlobalTheory.LFun.singleAt D.host.F w (x i) + GlobalTheory.LFun.singleAt D.host.F w' (x' i)) = x i
      rw [map_add (f := _), GlobalTheory.LFun.compAt_singleAt, GlobalTheory.LFun.compAt_singleAt_ne hne, add_zero]
    · show GlobalTheory.LFun.compAt D.host.F w' (GlobalTheory.LFun.singleAt D.host.F w (x i) + GlobalTheory.LFun.singleAt D.host.F w' (x' i)) = x' i
      rw [map_add (f := _), GlobalTheory.LFun.compAt_singleAt, GlobalTheory.LFun.compAt_singleAt_ne (Ne.symm hne), zero_add]
  have hsgm : ∀ (x : Fin T.rank → w.adicCompletion D.host.E) (x' : Fin T.rank → w'.adicCompletion D.host.E),
      x ∈ GlobalTheory.LFun.latAt w (frameLat T) → x' ∈ GlobalTheory.LFun.latAt w' (frameLat T) →
      (fun i => GlobalTheory.LFun.singleAt D.host.F w (x i) + GlobalTheory.LFun.singleAt D.host.F w' (x' i)) ∈ Formalism.L2.NTheta.LamHat T :=
    fun x x' hx hx' => add_mem (GlobalTheory.LFun.singleAt_mem_lamHat hx) (GlobalTheory.LFun.singleAt_mem_lamHat hx')
  have hmem : ∀ (u : HeightOneSpectrum (𝓞 D.host.E)) y, y ∈ Formalism.L2.NTheta.LamHat T →
      (fun i => GlobalTheory.LFun.compAt D.host.F u (y i)) ∈ GlobalTheory.LFun.latAt u (frameLat T) :=
    fun u y hy => GlobalTheory.LFun.compAt_mem_latAt u (hermitianSpaceBaseLattice_eq_frameLattice T ▸ hy)
  have hA : (Formalism.L2.NTheta.LamHat T).map pr =
      (GlobalTheory.LFun.latAt w (frameLat T)).toAddSubgroup.prod (GlobalTheory.LFun.latAt w' (frameLat T)).toAddSubgroup := by
    ext ⟨x, x'⟩
    simp only [AddSubgroup.mem_map, AddSubgroup.mem_prod, Submodule.mem_toAddSubgroup]
    constructor
    · rintro ⟨y, hy, hxy⟩
      have e1 : (fun i => GlobalTheory.LFun.compAt D.host.F w (y i)) = x := congrArg Prod.fst hxy
      have e2 : (fun i => GlobalTheory.LFun.compAt D.host.F w' (y i)) = x' := congrArg Prod.snd hxy
      subst e1 e2
      exact ⟨hmem w y hy, hmem w' y hy⟩
    · rintro ⟨hx, hx'⟩
      exact ⟨_, hsgm x x' hx hx', hsg x x'⟩
  have hB : ((Formalism.L2.NTheta.LamHat T).map φ).map pr =
      ((GlobalTheory.LFun.latAt w (frameLat T)).toAddSubgroup.map
        (GlobalTheory.LFun.locMat D.sp.cm.sig T.gram h g).1.mulVecLin.toAddMonoidHom).prod
      ((GlobalTheory.LFun.latAt w' (frameLat T)).toAddSubgroup.map
        (GlobalTheory.LFun.locMat D.sp.cm.sig T.gram h' g).1.mulVecLin.toAddMonoidHom) := by
    ext ⟨x, x'⟩
    simp only [AddSubgroup.mem_map, AddSubgroup.mem_prod, Submodule.mem_toAddSubgroup]
    constructor
    · rintro ⟨y, ⟨a, ha, rfl⟩, hxy⟩
      rw [hprφ] at hxy
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj hxy
      exact ⟨⟨_, hmem w a ha, rfl⟩, ⟨_, hmem w' a ha, rfl⟩⟩
    · rintro ⟨⟨b, hb, rfl⟩, ⟨b', hb', rfl⟩⟩
      refine ⟨φ _, ⟨_, hsgm b b' hb hb', rfl⟩, ?_⟩
      rw [hprφ]
      have e := hsg b b'
      simp only [pr, AddMonoidHom.mk'_apply, Prod.mk.injEq] at e
      rw [e.1, e.2]
      rfl
  show ((Formalism.L2.NTheta.LamHat T).map φ).relIndex (Formalism.L2.NTheta.LamHat T) = _
  rw [relIndex_map_of_proj _ φ P pr hK hPA hφ hc, hA, hB, GlobalTheory.BorelUMod.relIndex_prod_prod]
  rfl

end GlobalTheory.SplitLatIdx
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TwistTripleEigenvectorInGoodPart
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.L2 Formalism.L2.Host Formalism.L2.DIV Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.NX GlobalTheory.HeightCounting GlobalTheory.TwInputs GlobalTheory.SeriesTie NumberField IsDedekindDomain Polynomial
open Formalism.MainNotions.IntegralHeckeForms (TwOK ClsQ HkIdx V0 Fm0)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.TwInputs

open Formalism.IndefR.NX

theorem goodE_of_eigOcc : ∀ (D : D7) (cf : CharFrame D) (Rw : RowSide D) (low : Finset ℕ) (Pq : HeightOneSpectrum (𝓞 (maximalRealSubfield D.host.E)) → PlE D.host) (S : RatDat D.ntw) (hL : ∀ j, ℕ → PlE D.host → Module.End D.what₂.LL (S.WL j)) (eig : ℕ → D.what₂.FT → ℕ → PlE D.host → ↥D.LL0) (θ : ∀ kk : Fin 2, Multiplicative (ZMod (D.host.g kk)) →* (↥D.LL0)ˣ) (Bs : SideB D cf Rw low Pq S hL eig θ), ∀ Sb : Finset (PlE D.host), (∀ i, Sb ⊆ D.ntw.S0 i) → (∀ j, 1 ≤ j → j ≤ D.R.m → (S.A j).IsKsForm) → EigOcc D S θ hL Sb eig → ∀ i (s : D.ntw.Sig i), Formalism.MainNotions.BlochKatoReduction.Gen.goodE D.nexp i s := by
  intro D cf Rw low Pq S hL eig θ Bs Sb hSb hKs hOcc i s
  classical
  obtain ⟨h1, h2⟩ := D.ntw.jS_range i s
  obtain ⟨hiso, hgood, -⟩ := Bs.rhoS i s
  obtain ⟨x, hxg, hx0, hxe⟩ := hOcc _ h1 h2 _ hiso hgood
  obtain ⟨Φ, hΦ0, hΦs, hΦT⟩ := GlobalTheory.T.exists_descent_map_nonzero_of_small_field_form D S _ (hKs _ h1 h2) i (D.ntw.side i s) x hx0
  set e := Bs.eF i (D.ntw.jS i s) (D.ntw.side i s) h1 h2 with he
  refine ⟨e.symm (Φ x), by simpa using hΦ0, ?_, ?_⟩
  · letI : Fintype (G0g D.nd) := Formalism.MainNotions.PrimeDegreeVariant.finiteLevelGroupFintype D
    have hx1 := Module.End.mem_eigenspace_iff.1 (Submodule.mem_inf.1 hxg).1
    rw [one_smul, finsum_eq_sum_of_fintype, LinearMap.sum_apply] at hx1
    apply e.injective
    set_option synthInstance.maxHeartbeats 100000 in
      rw [MonoidAlgebra.lift_apply, Finsupp.sum_fintype _ _ (by intros; simp), LinearMap.sum_apply,
      map_sum, e.apply_symm_apply]
    conv_rhs => rw [← hx1]
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum]
    refine Finset.sum_congr rfl fun g _ => ?_
    rw [LinearMap.smul_apply, map_smul, LinearMap.smul_apply, hΦs, D.nexp.eAlg_def]
    change readLL0 S i _ (D.nexp.eLL0 g) • e (D.nexp.actG i _ _ g (e.symm (Φ x))) = _
    rw [Bs.act i _ _ h1 h2 g, e.apply_symm_apply]
    congr 1
    have hc : ((((S.A (D.ntw.jS i s)).chi (S.eG.symm g) : D.what₂.LLˣ) : D.what₂.LL))⁻¹ =
        (((chiL S _ (Bs.chiL _ h1 h2) (S.eG.symm g))⁻¹ : ↥D.LL0) : D.what₂.LL) := by
      simp [chiL]
    change _ = Φ (((((S.A (D.ntw.jS i s)).chi (S.eG.symm g) : D.what₂.LLˣ) : D.what₂.LL))⁻¹ •
      (S.A (D.ntw.jS i s)).ρ (S.eG.symm g) x)
    rw [hc, hΦs, hΦT _ (Bs.rho _ h1 h2 (S.eG.symm g)), map_inv₀]
    rfl
  · intro k P hk1 hk2 hsp hP
    apply e.injective
    rw [Bs.hkEq i _ _ h1 h2 k P _ hP hsp hk2, e.apply_symm_apply, map_smul, e.apply_symm_apply,
      Bs.rowS_eig i s k P hk1 hk2 hsp hP]
    have h3 := hΦT (hL (D.ntw.jS i s) k P) (Bs.hs _ h1 h2 k P) x
    rw [hxe k P hk1 hk2 hsp (fun h => hP (hSb i h)), hΦs] at h3
    rw [mul_smul]
    congr 1
    exact h3.symm

end GlobalTheory.TwInputs

end
end

