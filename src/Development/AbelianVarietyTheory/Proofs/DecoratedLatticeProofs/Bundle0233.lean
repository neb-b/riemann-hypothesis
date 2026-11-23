module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.StabOrd
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0066
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.EvalAtOneExtremalMul
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0222
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0018
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0011
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0016
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0018
public import Development.AbelianVarietyTheory.PublishedTheorems.SiegelWeil₂.Bundle0001
public import Development.AbelianVarietyTheory.PublishedTheorems.SiegelWeil₂.SiegelEisensteinSimplePoleOfDoublingMethod
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.WeilThetaConvergence
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0161
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0217
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0199
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0120
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0160
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsMulRightInvariantHaarAdelicUnitaryGroupHermiti
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0152
public import Development.AbelianVarietyTheory.Definitions.Foundations.ForallEventuallyFinLocIff
public import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.Bundle0051
public import Formalism.LocalToGlobal.IndefiniteReal.LevelTypeEquivalence.InfFam
public import Formalism.LocalToGlobal.IndefiniteReal.LevelTypeEquivalence.Bundle0004
public import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.IntegralConjInnerMulInnerOfIsEmptyEquiv
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0017
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleDiscreteSeriesOfHasParam
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0204
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0225

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FrameValuesPolynomialDetStableHomogeneous
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.KJInf Formalism.L2.Forms GlobalTheory.SeeSaw
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.KJInf.ValPol

variable {ι : Type} [Fintype ι] {a : ℕ}

theorem evalAt_eq (y : ι → Matrix (Fin a) (Fin a) ℂ) (F : PY ι a) :
    evalAt y F = MvPolynomial.eval (fun x : ι × Fin a × Fin a => y x.1 x.2.1 x.2.2) F := rfl

theorem evalAt_frDet (y : ι → Matrix (Fin a) (Fin a) ℂ) (τ : ι) :
    evalAt y (Formalism.L2.Ker.frDet ℂ a τ) = (y τ).det := by
  rw [evalAt_eq, Formalism.L2.Ker.frDet, RingHom.map_det]
  congr 1
  ext i j
  simp [RingHom.mapMatrix_apply]

theorem evalAt_mul_prod (y : ι → Matrix (Fin a) (Fin a) ℂ) (P : PY ι a) (n : ι → ℕ) :
    evalAt y (P * ∏ τ, (Formalism.L2.Ker.frDet ℂ a τ : PY ι a) ^ n τ) = evalAt y P * ∏ τ, (y τ).det ^ n τ := by
  rw [evalAt_eq, map_mul, map_prod, ← evalAt_eq]
  congr 1
  refine Finset.prod_congr rfl fun τ _ => ?_
  rw [map_pow, ← evalAt_eq, evalAt_frDet]

theorem fnOf_one_apply {G : ι → Matrix (Fin a) (Fin a) ℂ} (s : ι → ℤ) (P : PY ι a) (y : Frames G) :
    fnOf G s 1 P y = (∏ τ, (y.1 τ).det ^ s τ) * evalAt y.1 P := by
  simp only [fnOf, LinearMap.coe_mk, AddHom.coe_mk, Pi.one_apply, one_mul, evalAt]

theorem evalAt_lft (g y : ι → Matrix (Fin a) (Fin a) ℂ) (F : PY ι a) :
    evalAt y (lft g F) = evalAt (fun τ => g τ * y τ) F := by
  induction F using MvPolynomial.induction_on with
  | C c => simp [evalAt, lft]
  | add p q hp hq => simp only [evalAt, map_add (f := _)] at *; rw [hp, hq]
  | mul_X p v hp =>
    simp only [evalAt, map_mul] at *
    rw [hp]
    simp [lft, Matrix.mul_apply]

theorem shift_eq {G : ι → Matrix (Fin a) (Fin a) ℂ} (lam : ι → DomWeight a) {n : ι → ℕ} {s : ι → ℤ}
    (hns : ∀ τ, (n τ : ℤ) = shiftOf lam τ + s τ) (P : PY ι a) (y : Frames G) :
    evalAt y.1 (P * ∏ τ, (Formalism.L2.Ker.frDet ℂ a τ : PY ι a) ^ n τ) * ∏ τ, (y.1 τ).det ^ (-s τ) =
      fnOf G (shiftOf lam) 1 P y := by
  rw [evalAt_mul_prod, fnOf_one_apply, mul_assoc, mul_comm, ← Finset.prod_mul_distrib]
  congr 1
  refine Finset.prod_congr rfl fun τ _ => ?_
  have hd : (y.1 τ).det ≠ 0 := (y.2 τ).ne_zero
  rw [← zpow_natCast, ← zpow_add₀ hd, hns τ]
  congr 1
  ring

theorem mem_valC_iff (G : ι → Matrix (Fin a) (Fin a) ℂ) (lam : ι → DomWeight a) (n : ι → ℕ) (s : ι → ℤ)
    (hns : ∀ τ, (n τ : ℤ) = shiftOf lam τ + s τ) (Φ : Frames G → ℂ) :
    Φ ∈ ValC G lam ↔ ∃ F ∈ Vn lam n, ∀ y, Φ y = evalAt y.1 F * ∏ τ, (y.1 τ).det ^ (-s τ) := by
  constructor
  · rintro ⟨P, hP, rfl⟩
    exact ⟨_, ⟨P, hP, rfl⟩, fun y => (shift_eq lam hns P y).symm⟩
  · rintro ⟨F, ⟨P, hP, rfl⟩, hΦ⟩
    refine ⟨P, hP, funext fun y => ?_⟩
    rw [hΦ y]
    exact (shift_eq lam hns P y).symm

def nOf (lam : ι → DomWeight a) : ι → ℕ := fun τ => (shiftOf lam τ).toNat

def sOf (lam : ι → DomWeight a) : ι → ℤ := fun τ => (nOf lam τ : ℤ) - shiftOf lam τ

theorem nOf_eq (lam : ι → DomWeight a) (τ : ι) : (nOf lam τ : ℤ) = shiftOf lam τ + sOf lam τ := by
  simp [sOf]

theorem valC_eq_map (G : ι → Matrix (Fin a) (Fin a) ℂ) (lam : ι → DomWeight a) :
    ValC G lam = (Vn lam (nOf lam)).map (fnOf G (fun τ => -sOf lam τ) 1) := by
  ext Φ
  rw [mem_valC_iff G lam _ _ (nOf_eq lam)]
  constructor
  · rintro ⟨F, hF, hΦ⟩
    refine ⟨F, hF, funext fun y => ?_⟩
    rw [hΦ y, fnOf_one_apply, mul_comm]
  · rintro ⟨F, hF, rfl⟩
    exact ⟨F, hF, fun y => by rw [fnOf_one_apply, mul_comm]⟩

theorem finiteDimensional_valC (G : ι → Matrix (Fin a) (Fin a) ℂ) (lam : ι → DomWeight a) :
    FiniteDimensional ℂ (ValC G lam) := by
  haveI := (_root_.GlobalTheory.KJInf.vn_finiteDimensional_and_lft_mem ι a lam (nOf lam)).1
  rw [valC_eq_map]
  infer_instance

theorem valC_stable (G : ι → Matrix (Fin a) (Fin a) ℂ) (lam : ι → DomWeight a) (Φ : Frames G → ℂ) (hΦ : Φ ∈ ValC G lam)
    (g : ι → Matrix (Fin a) (Fin a) ℂ) (Φ' : Frames G → ℂ) (hΦ' : ∀ y y', IsTr g y y' → Φ' y = Φ y') (hg : IsInv g) :
    Φ' ∈ ValC G lam := by
  obtain ⟨F, hF, hΦF⟩ := (mem_valC_iff G lam _ _ (nOf_eq lam) Φ).1 hΦ
  rw [mem_valC_iff G lam _ _ (nOf_eq lam)]
  refine ⟨(∏ τ, (g τ).det ^ (-sOf lam τ)) • lft g F,
    Submodule.smul_mem _ _ ((_root_.GlobalTheory.KJInf.vn_finiteDimensional_and_lft_mem ι a lam (nOf lam)).2 g F hF), fun y => ?_⟩
  let y' : Frames G := ⟨fun τ => g τ * y.1 τ, fun τ => by rw [Matrix.det_mul]; exact (hg τ).mul (y.2 τ)⟩
  rw [hΦ' y y' (fun τ => rfl), hΦF y']
  have e : evalAt y.1 ((∏ τ, (g τ).det ^ (-sOf lam τ)) • lft g F) =
      (∏ τ, (g τ).det ^ (-sOf lam τ)) * evalAt (fun τ => g τ * y.1 τ) F := by
    rw [evalAt_eq, MvPolynomial.smul_eval, ← evalAt_eq, evalAt_lft]
  rw [e]
  simp only [y', Matrix.det_mul, mul_zpow, Finset.prod_mul_distrib]
  ring

theorem natW_anti' (l : DomWeight a) : Antitone l.natW := fun i j h =>
  Int.toNat_le_toNat (by have := l.anti h; omega)

theorem isHomogeneous_of_mem_delSq (l : DomWeight a) {f : MvPolynomial (Fin a × Fin a) ℂ} (hf : f ∈ delSq ℂ a l) :
    f.IsHomogeneous (∑ r, l.natW r) := by
  have h : MvPolynomial.IsWeightedHomogeneous (Formalism.GradedWeylDivisibility.colW a a) f l.natW :=
    (Formalism.GradedWeylDivisibility.weylLeDual ℂ a a le_rfl l.natW (natW_anti' l) hf).1
  intro m hm
  rw [← h hm]
  simp only [Finsupp.weight_apply, Finsupp.sum, Finset.sum_apply, Formalism.GradedWeylDivisibility.colW]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun v _ => ?_
  simp [Pi.single_apply]

theorem eval_smul_of_isHomogeneous {σ : Type} {f : MvPolynomial σ ℂ} {d : ℕ} (hf : f.IsHomogeneous d)
    (c : ℂ) (v : σ → ℂ) : MvPolynomial.eval (c • v) f = c ^ d * MvPolynomial.eval v f := by
  rw [MvPolynomial.eval_eq, MvPolynomial.eval_eq, Finset.mul_sum]
  refine Finset.sum_congr rfl fun m hm => ?_
  have : m.degree = d := by
    rw [Finsupp.degree_eq_weight_one]
    exact hf (MvPolynomial.mem_support_iff.1 hm)
  rw [← this, Finsupp.degree_apply]
  simp only [Pi.smul_apply, smul_eq_mul, mul_pow, Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum]
  ring

theorem sum_w_eq (l : DomWeight a) : ∑ i, l.w i = ∑ i, ((l.natW i : ℕ) : ℤ) + (a : ℤ) * l.detShift := by
  have h : ∀ i, ((l.natW i : ℕ) : ℤ) = l.w i - l.detShift := by
    intro i
    have hpos : 0 < a := Fin.pos i
    have hle : l.w ⟨a - 1, by omega⟩ ≤ l.w i := l.anti (Fin.le_iff_val_le_val.2 (by simp; omega))
    simp only [DomWeight.natW, DomWeight.detShift, dif_pos hpos]
    exact Int.toNat_of_nonneg (by omega)
  simp only [h, Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  ring

theorem evalAt_scale_cSpan (lam : ι → DomWeight a) (z : ι → ℂ) (y y' : ι → Matrix (Fin a) (Fin a) ℂ)
    (hy : ∀ τ, y' τ = z τ • y τ) (P : PY ι a) (hP : P ∈ CSpan lam) :
    evalAt y' P = (∏ τ, z τ ^ (∑ i, (lam τ).natW i)) * evalAt y P := by
  induction hP using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨f, hf, rfl⟩ := hx
    simp only [evalAt_eq, ten, map_prod, MvPolynomial.eval_rename]
    rw [← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun τ _ => ?_
    have e : ((fun x : ι × Fin a × Fin a => y' x.1 x.2.1 x.2.2) ∘ Prod.mk τ) =
        z τ • ((fun x : ι × Fin a × Fin a => y x.1 x.2.1 x.2.2) ∘ Prod.mk τ) := by
      funext x
      simp [hy τ]
    rw [e, eval_smul_of_isHomogeneous (isHomogeneous_of_mem_delSq (lam τ) (hf τ))]
  | zero => simp [evalAt_eq]
  | add p q _ _ hp hq => simp only [evalAt_eq, map_add (f := _)] at *; rw [hp, hq]; ring
  | smul c p _ hp => simp only [evalAt_eq, MvPolynomial.smul_eval] at *; rw [hp]; ring

theorem valC_homog (G : ι → Matrix (Fin a) (Fin a) ℂ) (lam : ι → DomWeight a) (Φ : Frames G → ℂ) (hΦ : Φ ∈ ValC G lam)
    (z : ι → ℂ) (y y' : Frames G) (hy : ∀ τ, y'.1 τ = z τ • y.1 τ) :
    Φ y' = (∏ τ, z τ ^ (∑ i, (lam τ).w i)) * Φ y := by
  rcases Nat.eq_zero_or_pos a with rfl | ha
  · have : y' = y := Subtype.ext (funext fun τ => Subsingleton.elim _ _)
    simp [this]
  obtain ⟨P, hP, rfl⟩ := hΦ
  rw [fnOf_one_apply, fnOf_one_apply, evalAt_scale_cSpan lam z y.1 y'.1 hy P hP]
  have hz : ∀ τ, z τ ≠ 0 := by
    intro τ h0
    have hne := (y'.2 τ).ne_zero
    haveI : Nonempty (Fin a) := ⟨⟨0, ha⟩⟩
    rw [hy τ, h0, zero_smul, Matrix.det_zero] at hne
    exact hne rfl
  have per : ∀ (zz d : ℂ) (sh : ℤ) (deg : ℕ) (W : ℤ), zz ≠ 0 → W = deg + a * sh →
      (zz ^ a * d) ^ sh * zz ^ deg = zz ^ W * d ^ sh := by
    intro zz d sh deg W hz hW
    rw [mul_zpow, ← zpow_natCast zz a, ← _root_.zpow_mul, hW, zpow_add₀ hz, zpow_natCast]
    ring
  have key : (∏ τ, (y'.1 τ).det ^ shiftOf lam τ) * ∏ τ, z τ ^ (∑ i, (lam τ).natW i) =
      (∏ τ, z τ ^ (∑ i, (lam τ).w i)) * ∏ τ, (y.1 τ).det ^ shiftOf lam τ := by
    rw [← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun τ _ => ?_
    rw [hy τ, Matrix.det_smul, Fintype.card_fin]
    exact per _ _ _ _ _ (hz τ) (by rw [sum_w_eq, Nat.cast_sum]; rfl)
  linear_combination (evalAt y.1 P) * key

end GlobalTheory.KJInf.ValPol

theorem GlobalTheory.KJInf.valC_poly : ∀ (ι : Type) [Fintype ι] (a : ℕ) (G : ι → Matrix (Fin a) (Fin a) ℂ) (lam : ι → DomWeight a), (∀ (n : ι → ℕ) (s : ι → ℤ), (∀ τ, (n τ : ℤ) = shiftOf lam τ + s τ) → ∀ Φ : Frames G → ℂ, Φ ∈ ValC G lam ↔ ∃ F ∈ Vn lam n, ∀ y, Φ y = evalAt y.1 F * ∏ τ, (y.1 τ).det ^ (-s τ)) ∧ FiniteDimensional ℂ (ValC G lam) ∧ (∀ Φ ∈ ValC G lam, ∀ g : ι → Matrix (Fin a) (Fin a) ℂ, ∀ Φ' : Frames G → ℂ, (∀ y y', IsTr g y y' → Φ' y = Φ y') → IsInv g → Φ' ∈ ValC G lam) ∧ ∀ Φ ∈ ValC G lam, ∀ (z : ι → ℂ) (y y' : Frames G), (∀ τ, y'.1 τ = z τ • y.1 τ) → Φ y' = (∏ τ, z τ ^ (∑ i, (lam τ).w i)) * Φ y := by
  intro ι _ a G lam
  refine ⟨fun n s hns Φ => GlobalTheory.KJInf.ValPol.mem_valC_iff G lam n s hns Φ,
    GlobalTheory.KJInf.ValPol.finiteDimensional_valC G lam,
    fun Φ hΦ g Φ' hΦ' hg => GlobalTheory.KJInf.ValPol.valC_stable G lam Φ hΦ g Φ' hΦ' hg,
    fun Φ hΦ z y y' hy => GlobalTheory.KJInf.ValPol.valC_homog G lam Φ hΦ z y y' hy⟩

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.HeisenbergCombinationExtendByZeroTargetSlice
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.FinPl GlobalTheory.MixPer GlobalTheory.MixModel GlobalTheory.Unf GlobalTheory.LatPair GlobalTheory.SplitWeil GlobalTheory.SeeSaw ValuativeRel IsLocalRing Matrix
open GlobalTheory.IndefiniteRowSideFullHecke.AppendedVectorData (lastKer InDual)
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.FinPl.ExtZero

theorem comb_extT_resT_symm : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (S A L T : HSp D) (o : OrthDec S A L) (c : WO T A →₀ ℂ) (f : WO T S → ℂ) (y : WO T L) (w : WO T A), comb ψ T A c (fun w' => f ((o.resT T).symm (w', y))) w = comb ψ T S (extT o T c) f ((o.resT T).symm (w, y)) := by
  intro D ψ S A L T o c f y w
  have h1 : ∀ (X Y : HSp D) (d : WO X Y →₀ ℂ) (g : WO X Y → ℂ) (x : WO X Y),
      comb ψ X Y d g x = d.sum fun u a => a * heisO ψ X Y u g x := by
    intro X Y d g x
    simp only [comb, Finsupp.sum, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  rw [h1, h1, extT, Finsupp.sum_mapDomain_index (fun _ => zero_mul _) (fun _ _ _ => add_mul _ _ _)]
  exact Finsupp.sum_congr fun u _ => by rw [heisO_resT_symm]

end GlobalTheory.FinPl.ExtZero
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IsAtTauChart
section
open scoped Matrix NNReal TensorProduct Classical
open MeasureTheory NumberField IsDedekindDomain Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.Eis GlobalTheory.MixModel GlobalTheory.RegSW GlobalTheory.RegSch
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (swSec sZero IsKFinVec)
open GlobalTheory.Core.Rk.SW (sch)
open GlobalTheory.Mem.AutSpace (SmFun)
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section
namespace GlobalTheory.RegSch.ChartDer

open GlobalTheory.StdUnn

variable {D : D7}

theorem isAtTau_iff (θ : InfFam D) (V : HSp D) (τ : D.what₂.Tau) (x : Matrix (Fin V.rank) (Fin V.rank) ℂ) (h : GA D V) :
    IsAtTau θ V τ x h ↔ compAt θ τ (mt V h) = x ∧ (∀ τ', τ' ≠ τ → compAt θ τ' (mt V h) = 1) ∧
      (mt V h).map (finPart D) = 1 := by
  have : h ∈ GinfC V ↔ (mt V h).map (finPart D) = 1 := by
    rw [GinfC, MonoidHom.mem_ker, Units.ext_iff]
    rfl
  rw [IsAtTau, this]
  exact ⟨fun ⟨a, b, c⟩ => ⟨b, c, a⟩, fun ⟨b, c, a⟩ => ⟨a, b, c⟩⟩

end GlobalTheory.RegSch.ChartDer
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IsCompactGinfCOfOntoUni
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.KJInf Formalism.L2.Forms GlobalTheory.SeeSaw
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.SeeSaw

theorem isCompact_ginfC_of_ontoUni (D : D7) (θ : InfFam D) (V : HSp D) (B : D.what₂.Tau → Matrix (Fin V.rank) (Fin V.rank) ℂ)
    (hθ : IsInfFam θ) (hr : OntoUni (fun k : GinfC V => inB θ V B k.1)) : IsCompact (GinfC V : Set (GA D V)) := by
  obtain rfl := Formalism.IndefR.Eqv.eq_thetaC D hθ
  have hB : ∀ τ, IsUnit (B τ).det := by
    intro τ
    by_contra hn
    have h0 := hr.uni 1 τ
    have e : inB (Formalism.IndefR.Eqv.thetaC D) V B (1 : GinfC V).1 τ = 0 := by
      simp only [inB, Matrix.nonsing_inv_apply_not_isUnit _ hn, Matrix.zero_mul]
    rw [e] at h0
    have h1 : (1 : Matrix (Fin V.rank) (Fin V.rank) ℂ) = 0 := by
      have := Matrix.mem_unitaryGroup_iff.mp h0
      simpa using this.symm
    have hB1 : B τ = 1 := by
      calc B τ = B τ * 1 := (Matrix.mul_one _).symm
        _ = 0 := by rw [h1, Matrix.mul_zero]
        _ = 1 := h1.symm
    exact hn (by rw [hB1, Matrix.det_one]; exact isUnit_one)
  have hconj : ∀ τ (M : Matrix (Fin V.rank) (Fin V.rank) ℂ), B τ * ((B τ)⁻¹ * M * B τ) * (B τ)⁻¹ = M := by
    intro τ M
    calc B τ * ((B τ)⁻¹ * M * B τ) * (B τ)⁻¹ = (B τ * (B τ)⁻¹) * M * (B τ * (B τ)⁻¹) := by
          simp only [Matrix.mul_assoc]
      _ = M := by rw [Matrix.mul_nonsing_inv _ (hB τ), Matrix.one_mul, Matrix.mul_one]
  have hU : ∀ u : D.what₂.Tau → unitaryGroup (Fin V.rank) ℂ,
      Formalism.IndefR.Eqv.IsUnitFam D V (fun τ => B τ * (u τ : Matrix (Fin V.rank) (Fin V.rank) ℂ) * (B τ)⁻¹) := by
    intro u
    obtain ⟨k, hk⟩ := hr.onto (fun τ => (u τ : Matrix (Fin V.rank) (Fin V.rank) ℂ)) (fun τ => (u τ).2)
    have e : (fun τ => B τ * (u τ : Matrix (Fin V.rank) (Fin V.rank) ℂ) * (B τ)⁻¹) =
        fun τ => infMat D.sp.cm.sig V.gram (Formalism.IndefR.Eqv.thetaC D τ) (k : GA D V) := by
      funext τ
      have := congrFun hk τ
      rw [← this]
      exact hconj τ _
    rw [e]
    exact Formalism.IndefR.Eqv.infMat_unitary' D V _
  have : CompactSpace (unitaryGroup (Fin V.rank) ℂ) :=
    isCompact_iff_compactSpace.mp (GlobalTheory.isCompact_unitaryGroup _ _)
  let Ψ : (D.what₂.Tau → unitaryGroup (Fin V.rank) ℂ) → GA D V := fun u => Formalism.IndefR.Eqv.famH D V _ (hU u)
  have hg : Continuous fun u : (D.what₂.Tau → unitaryGroup (Fin V.rank) ℂ) =>
      fun τ => B τ * (u τ : Matrix (Fin V.rank) (Fin V.rank) ℂ) * (B τ)⁻¹ :=
    continuous_pi fun τ => (continuous_const.matrix_mul (continuous_subtype_val.comp (continuous_apply τ))).matrix_mul
      continuous_const
  have hΨ : Continuous Ψ := by
    refine continuous_induced_rng.2 (Units.continuous_iff.2 ⟨?_, ?_⟩)
    · exact GlobalTheory.HaarReal.continuous_famM.comp hg
    · have hi : Continuous fun u : (D.what₂.Tau → unitaryGroup (Fin V.rank) ℂ) =>
          fun τ => Formalism.IndefR.Eqv.ginv D V τ (B τ * (u τ : Matrix (Fin V.rank) (Fin V.rank) ℂ) * (B τ)⁻¹) :=
        continuous_pi fun τ => (continuous_const.matrix_mul ((continuous_apply τ).comp hg).matrix_conjTranspose).matrix_mul
          continuous_const
      exact GlobalTheory.HaarReal.continuous_famM.comp hi
  have hsub : (GinfC V : Set (GA D V)) ⊆ Set.range Ψ := by
    intro g hg
    refine ⟨fun τ => ⟨inB (Formalism.IndefR.Eqv.thetaC D) V B g τ, hr.uni ⟨g, hg⟩ τ⟩, ?_⟩
    refine (Formalism.IndefR.Eqv.famH_unique D V _ (hU _) g hg fun τ => ?_).symm
    exact (hconj τ _).symm
  exact (isCompact_range hΨ).of_isClosed_subset (GlobalTheory.Ker.CongTop.isClosed_GinfC V) hsub

end GlobalTheory.SeeSaw

namespace GlobalTheory.SeeSaw

theorem integral_eq_classSum : ∀ (D : D7) (θ : InfFam D) (V : HSp D) (B : D.what₂.Tau → Matrix (Fin V.rank) (Fin V.rank) ℂ), IsInfFam θ → OntoUni (fun k : GinfC V => inB θ V B k.1) → BorelSpace (GinfC V) ∧ CompactSpace (GinfC V) ∧ (∀ g ∈ GfC V, ∀ k ∈ GinfC V, g * k = k * g) ∧ ∃ ν : Measure (GinfC V), IsProbabilityMeasure ν ∧ ν.IsMulLeftInvariant ∧ ∀ (v : Vol V) (U : Subgroup (GA D V)) (cl : Type) [Fintype cl] (h : cl → GA D V), IsReps V U h → 0 < volLev v U ∧ (∀ a, 0 < stabOrd U (h a)) ∧ ∀ Φ : GA D V → ℂ, Continuous Φ → (∀ γ ∈ GQ V, ∀ g, Φ (γ * g) = Φ g) → (∀ κ ∈ U, ∀ g, Φ (g * κ) = Φ g) → ∫ g in v.𝓕, Φ g ∂v.μ = (volLev v U : ℂ) * ∑ a, ((stabOrd U (h a) : ℕ) : ℂ)⁻¹ * ∫ k, Φ (h a * k.1) ∂ν := by
  intro D θ V B hθ hr
  have hT := GlobalTheory.Mem.AdelicGroupTop.adelic_unitary_topology D V
  haveI := hT.1
  haveI := hT.2.1
  haveI := hT.2.2.1
  haveI := hT.2.2.2.1
  haveI := hT.2.2.2.2.1
  haveI := hT.2.2.2.2.2.1
  haveI := hT.2.2.2.2.2.2
  have hK : IsCompact (GinfC V : Set (GA D V)) := isCompact_ginfC_of_ontoUni D θ V B hθ hr
  haveI : CompactSpace (GinfC V) := isCompact_iff_compactSpace.mp hK
  haveI : BorelSpace (GinfC V) := Subtype.borelSpace _
  have hcf : ∀ {a b : GA D V}, a ∈ GinfC V → b ∈ GfC V → a * b = b * a := fun ha hb =>
    Formalism.IndefR.Eqv.Act.comm_inf_fin ha hb
  refine ⟨inferInstance, inferInstance, fun g hg k hk => (hcf hk hg).symm, ?_⟩
  let ν : Measure (GinfC V) := Measure.haarMeasure ⊤
  haveI : IsProbabilityMeasure ν :=
    ⟨by simpa using (Measure.haarMeasure_self (K₀ := (⊤ : TopologicalSpace.PositiveCompacts (GinfC V))))⟩
  refine ⟨ν, inferInstance, inferInstance, ?_⟩
  intro v U cl _ h hU
  haveI := v.haar
  haveI : v.μ.IsMulRightInvariant := GlobalTheory.AdelicPointsUnimod.isMulRightInvariant_of_isHaarMeasure D V v.μ v.haar
  haveI : (GinfC V).Normal := inferInstanceAs ((finHom V).ker.Normal)
  let K : Subgroup (GA D V) := GinfC V ⊔ U
  have hKset : (K : Set (GA D V)) = {g | ∃ k ∈ GinfC V, ∃ κ ∈ U, g = k * κ} := by
    show ((GinfC V ⊔ U : Subgroup (GA D V)) : Set (GA D V)) = _
    rw [Subgroup.normal_mul]
    ext g
    simp only [Set.mem_mul, SetLike.mem_coe, Set.mem_setOf_eq]
    constructor
    · rintro ⟨k, hk, κ, hκ, rfl⟩
      exact ⟨k, hk, κ, hκ, rfl⟩
    · rintro ⟨k, hk, κ, hκ, rfl⟩
      exact ⟨k, hk, κ, hκ, rfl⟩
  have hmemK : ∀ g, g ∈ K ↔ ∃ k ∈ GinfC V, ∃ κ ∈ U, g = k * κ := fun g => by
    rw [← SetLike.mem_coe, hKset]; rfl
  have hvol : volLev v U = (v.μ K).toReal := by
    simp only [volLev]
    rw [← hKset]
  have hKc : IsCompact (K : Set (GA D V)) := by
    show IsCompact ((GinfC V ⊔ U : Subgroup (GA D V)) : Set (GA D V))
    rw [Subgroup.normal_mul]
    exact hK.mul hU.cpt
  have hKo : IsOpen (K : Set (GA D V)) := by
    have ho : IsOpen (((U.subgroupOf (GfC V)).comap (GlobalTheory.AutMult.toFin V) : Subgroup (GA D V)) : Set (GA D V)) :=
      hU.opn.preimage (GlobalTheory.AutMult.continuous_toFin V)
    refine Subgroup.isOpen_mono (fun g hg => ?_) ho
    rw [hmemK]
    exact ⟨GlobalTheory.AutMult.toInf V g, (GlobalTheory.AutMult.toInf V g).2, GlobalTheory.AutMult.toFin V g,
      Subgroup.mem_subgroupOf.mp (Subgroup.mem_comap.mp hg), (GlobalTheory.AutMult.toInf_mul_toFin g).symm⟩
  have hKfin : v.μ K ≠ ⊤ := hKc.measure_lt_top.ne
  have hKpos : 0 < v.μ K := hKo.measure_pos v.μ ⟨1, K.one_mem⟩
  have huniq : ∀ x : GA D V, ∃! i, ∃ γ ∈ GQ V, ∃ k ∈ K, x = γ * h i * k := by
    intro x
    obtain ⟨γ, hγ, c, k, hk, κ, hκ, e⟩ := hU.dec x
    refine ⟨c, ⟨γ, hγ, k * κ, (hmemK _).2 ⟨k, hk, κ, hκ, rfl⟩, by rw [e]; group⟩, ?_⟩
    rintro c' ⟨γ', hγ', k', hk', e'⟩
    obtain ⟨k₁, hk₁, κ₁, hκ₁, rfl⟩ := (hmemK _).1 hk'
    refine (hU.uniq c c' (γ'⁻¹ * γ) (mul_mem (inv_mem hγ') hγ) (k * k₁⁻¹) (mul_mem hk (inv_mem hk₁)) (κ * κ₁⁻¹)
      (mul_mem hκ (inv_mem hκ₁)) ?_).symm
    have hc1 : k₁⁻¹ * (κ * κ₁⁻¹) = (κ * κ₁⁻¹) * k₁⁻¹ := hcf (inv_mem hk₁) (hU.le (mul_mem hκ (inv_mem hκ₁)))
    have e2 : h c' = γ'⁻¹ * x * (k₁ * κ₁)⁻¹ := by rw [e']; group
    rw [e2, e, _root_.mul_inv_rev]
    calc γ'⁻¹ * (γ * (h c * k) * κ) * (κ₁⁻¹ * k₁⁻¹) = γ'⁻¹ * γ * (h c * k) * ((κ * κ₁⁻¹) * k₁⁻¹) := by group
      _ = γ'⁻¹ * γ * (h c * k) * (k₁⁻¹ * (κ * κ₁⁻¹)) := by rw [hc1]
      _ = γ'⁻¹ * γ * (h c * (k * k₁⁻¹)) * (κ * κ₁⁻¹) := by group
  have hfin : ∀ i, {γ : GA D V | γ ∈ GQ V ∧ (h i)⁻¹ * γ * h i ∈ K}.Finite := by
    intro i
    have hC : IsCompact ((fun y => h i * y * (h i)⁻¹) '' (K : Set (GA D V))) :=
      hKc.image ((continuous_const.mul continuous_id).mul continuous_const)
    have hcl : IsClosed (GQ V : Set (GA D V)) := Subgroup.isClosed_of_discrete
    have hTc : IsCompact (((↑) : GQ V → GA D V) ⁻¹' ((fun y => h i * y * (h i)⁻¹) '' (K : Set (GA D V)))) :=
      hcl.isClosedEmbedding_subtypeVal.isCompact_preimage hC
    refine (hTc.finite_of_discrete.image Subtype.val).subset ?_
    rintro γ ⟨hγ, hk⟩
    exact ⟨⟨γ, hγ⟩, ⟨_, hk, by group⟩, rfl⟩
  have hst : ∀ i, {γ : GA D V | γ ∈ GQ V ∧ (h i)⁻¹ * γ * h i ∈ K}.ncard = stabOrd U (h i) := by
    intro i
    have hs : {γ : GA D V | γ ∈ GQ V ∧ (h i)⁻¹ * γ * h i ∈ K} =
        Subtype.val '' {γ : GQ V | ∃ k ∈ GinfC V, ∃ κ ∈ U, γ.1 * h i = h i * k * κ} := by
      ext γ
      constructor
      · rintro ⟨hγ, hk⟩
        obtain ⟨k, hk, κ, hκ, e⟩ := (hmemK _).1 hk
        refine ⟨⟨γ, hγ⟩, ⟨k, hk, κ, hκ, ?_⟩, rfl⟩
        calc γ * h i = h i * ((h i)⁻¹ * γ * h i) := by group
          _ = h i * k * κ := by rw [e, mul_assoc]
      · rintro ⟨γ, ⟨k, hk, κ, hκ, e⟩, rfl⟩
        refine ⟨γ.2, (hmemK _).2 ⟨k, hk, κ, hκ, ?_⟩⟩
        calc (h i)⁻¹ * γ.1 * h i = (h i)⁻¹ * (γ.1 * h i) := by group
          _ = k * κ := by rw [e]; group
    rw [hs, Set.ncard_image_of_injective _ Subtype.val_injective, ← Nat.card_coe_set_eq]
    rfl
  refine ⟨by rw [hvol]; exact ENNReal.toReal_pos hKpos.ne' hKfin, fun a => ?_, ?_⟩
  · rw [← hst]
    exact (Set.ncard_pos (hfin a)).mpr ⟨1, (GQ V).one_mem, by simpa using K.one_mem⟩
  intro Φ hΦc hΦl hΦr
  obtain ⟨-, he⟩ := GlobalTheory.integral_fundamentalDomain_eq_sum_doubleCoset_avg (GA D V) v.μ (GQ V) K U v.𝓕 v.fund hKo hKfin
    (GinfC V) ν (GinfC V).subtype continuous_subtype_val
    (fun k hk => by
      obtain ⟨a, ha, κ, hκ, rfl⟩ := (hmemK _).1 hk
      exact ⟨κ, hκ, ⟨a, ha⟩, hcf ha (hU.le hκ)⟩)
    (fun k hk w => (hcf w.2 (hU.le hk)).symm) cl h huniq hfin Φ hΦc hΦl hΦr
  rw [he, hvol]
  congr 1
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [hst i]
  rfl

end GlobalTheory.SeeSaw
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IsJointlySmoothBiThetaWeilRepFirstVariable
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.SeeSaw
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.BiTransfer

theorem isBiTheta_act_left : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (A S A' : HSp D) (χA χS : (AE D)ˣ →* Circle) (oma : Om A S), IsWeilDatumO ψ A S χA χS oma → ∀ C, IsBiTheta ψ A S A' C → ∀ p, IsBiTheta ψ A S A' fun u v => oma p (fun u' => C u' v) u := by
  intro D ψ A S A' χA χS oma H C hC p
  let d := sumDec A (GlobalTheory.ChiGrid.negSp A')
  have h := (GlobalTheory.T.weil_operator_commutes_superposition_slices_source D ψ _ A _ S d χA χS oma H _ (isThetaFunO_join d hC) Unit 0 (fun _ => 0) (fun _ => 0)
    measurable_const (integrable_zero _ _ _) p).1
  simp only [join_symm] at h
  exact isBiTheta_of_join d h

end GlobalTheory.BiTransfer
end

