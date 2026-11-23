module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0128
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0093
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.HasDerivAtZeroAndIsTheta
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0131
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0234
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0180
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.SelfDualLatticePairingDual
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0061
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0879
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0159
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0138
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0132
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0021
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.WittDecompSymplInclIsotropicInclAnisotropic
public import Development.AbelianVarietyTheory.Definitions.Foundations.T2SpaceTensorProductFiniteExtension
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0228
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0220
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0020

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.HeisenbergCompressionRealPlaceFockVacuaScalar
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting GlobalTheory.PlaceTensor
open scoped TensorProduct ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.VacCompress

open GlobalTheory.WeilVacMove

theorem gauss_ode (c : ℝ → ℂ) (a : ℂ) (h : ∀ s : ℝ, HasDerivAt c ((s : ℂ) * a * c s) s) :
    c 1 = Complex.exp (a / 2) * c 0 := by
  have key : ∀ s : ℝ, HasDerivAt (fun t : ℝ => Complex.exp (-(a * ((t : ℂ) * (t : ℂ)) / 2)) * c t) 0 s := by
    intro s
    have e1 : HasDerivAt (fun x : ℂ => -(a * (x * x) / 2)) (-(a * (1 * (s : ℂ) + (s : ℂ) * 1) / 2)) (s : ℂ) :=
      ((((hasDerivAt_id (s : ℂ)).mul (hasDerivAt_id (s : ℂ))).const_mul a).div_const 2).neg
    have e3 := (e1.cexp.comp_ofReal).mul (h s)
    exact e3.congr_deriv (by ring)
  have hc := is_const_of_deriv_eq_zero (fun s => (key s).differentiableAt) (fun s => (key s).deriv) 1 0
  simp only [Complex.ofReal_one, Complex.ofReal_zero, mul_one, mul_zero, zero_div, neg_zero,
    Complex.exp_zero, one_mul] at hc
  rw [← hc, ← mul_assoc, ← Complex.exp_add]
  simp

variable {D : D7} {ψ : AddChar (AF D.host.F) ℂ} {θ : InfFam D} {S T : HSp D}

theorem wAt_eq_lineAt (hθ : IsInfFam θ) {m n : ℕ} (τ : D.what₂.Tau) (w : Mx D m n) :
    wAt (.inr τ) w = lineAt θ τ (compAt θ τ w) 1 := by
  obtain ⟨σ, hσ⟩ := GlobalTheory.RealLineAt.exists_inverse_chart hθ
  obtain ⟨-, hfin, hcomp⟩ := GlobalTheory.WeilVacMove.isLineAt_lineAt hθ τ (compAt θ τ w)
  obtain ⟨-, -, -, -, hfi, -, hth⟩ := _root_.GlobalTheory.PlaceTensor.idem_spec D
  ext i j
  rw [← sub_eq_zero]
  apply hσ.ext
  · have h1 : finPart D (lineAt θ τ (compAt θ τ w) 1 i j) = 0 := by
      have := congrFun (congrFun (hfin 1) i) j
      simpa only [Matrix.map_apply, Matrix.zero_apply] using this
    simp [GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting.wAt, map_sub, map_mul, hfi τ, h1]
  · intro τ'
    have h2 := congrFun (congrFun (hcomp 1 τ') i) j
    by_cases hτ : τ' = τ
    · subst hτ
      rw [if_pos rfl, Complex.ofReal_one, one_smul] at h2
      have h2' : θ τ' (infPart D (lineAt θ τ' (compAt θ τ' w) 1 i j)) = θ τ' (infPart D (w i j)) := h2
      simp only [GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting.wAt, map_sub, map_mul, (hth θ hθ τ').1, one_mul, h2']
      exact sub_self _
    · have h3 := (hth θ hθ τ').2 τ (Ne.symm hτ)
      rw [if_neg hτ] at h2
      have h2' : θ τ' (infPart D (lineAt θ τ (compAt θ τ w) 1 i j)) = 0 := h2
      simp only [GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting.wAt, map_sub, map_mul, h3, zero_mul, zero_sub, neg_eq_zero, h2']

theorem dLine_heisO (hψ : IsStdChar D ψ (-1)) {lam : AF D.host.F →+ ℂ} (hl : Continuous lam)
    (hlam : ∀ a, sndA D.host.F a = 0 → ψ a = Complex.exp (lam a)) {L : ℝ →+ WO S T} (hL : Continuous L)
    (hL0 : ∀ t, (L t).map (finPart D) = 0) (v : WO S T) {f : WO S T → ℂ} (hf : IsThetaFunO ψ S T f) (x : WO S T) :
    dLine ψ S T L (heisO ψ S T v f) x =
      -2 * phase lam S T (L 1) v * heisO ψ S T v f x + ψ (symplOH S T x v) * dLine ψ S T L f (x + v) := by
  have hG : (fun t : ℝ => heisO ψ S T (L t) (heisO ψ S T v f) x) =
      fun t : ℝ => ψ (symplOH S T x v) * Complex.exp ((t : ℂ) * (-2 * phase lam S T (L 1) v)) *
        heisO ψ S T (L t) f (x + v) := by
    funext t
    have e1 := GlobalTheory.WeilVacMove.psi_sympl_line hl hlam hL hL0 v t
    have hX : Complex.exp ((t : ℂ) * (-2 * phase lam S T (L 1) v)) =
        (Complex.exp ((t : ℂ) * phase lam S T (L 1) v))⁻¹ * (Complex.exp ((t : ℂ) * phase lam S T (L 1) v))⁻¹ := by
      rw [← Complex.exp_neg, ← Complex.exp_add]
      congr 1
      ring
    have hE := Complex.exp_ne_zero ((t : ℂ) * phase lam S T (L 1) v)
    show ψ (symplOH S T x (L t)) * (ψ (symplOH S T (x + L t) v) * f (x + L t + v)) =
      ψ (symplOH S T x v) * Complex.exp ((t : ℂ) * (-2 * phase lam S T (L 1) v)) *
        (ψ (symplOH S T (x + v) (L t)) * f (x + v + L t))
    rw [GlobalTheory.WeilVacMove.symplOH_add_left, GlobalTheory.WeilVacMove.symplOH_add_left,
      GlobalTheory.WeilVacMove.symplOH_skew S T v (L t), AddChar.map_add_eq_mul, AddChar.map_add_eq_mul,
      AddChar.map_neg_eq_inv, e1, add_right_comm x (L t) v, hX]
    field_simp
  have hH := (GlobalTheory.WeilVacMove.hasDerivAt_zero_and_isTheta hψ hL hL0 hf).1 (x + v)
  have hexp : HasDerivAt (fun t : ℝ => Complex.exp ((t : ℂ) * (-2 * phase lam S T (L 1) v)))
      (Complex.exp (((0 : ℝ) : ℂ) * (-2 * phase lam S T (L 1) v)) * (1 * (-2 * phase lam S T (L 1) v))) 0 :=
    (((hasDerivAt_id ((0 : ℝ) : ℂ)).mul_const _).cexp).comp_ofReal
  have hD := (hexp.const_mul (ψ (symplOH S T x v))).mul hH
  show deriv (fun t : ℝ => heisO ψ S T (L t) (heisO ψ S T v f) x) 0 = _
  have hD' : HasDerivAt (fun t : ℝ => ψ (symplOH S T x v) * Complex.exp ((t : ℂ) * (-2 * phase lam S T (L 1) v)) *
      heisO ψ S T (L t) f (x + v)) _ 0 := hD
  rw [hG, hD'.deriv]
  have hv : heisO ψ S T v f x = ψ (symplOH S T x v) * f (x + v) := rfl
  rw [hv, map_zero, GlobalTheory.WeilVacMove.heisO_zero]
  simp only [Complex.ofReal_zero, zero_mul, Complex.exp_zero]
  ring

private theorem flow_lemma {μ : Measure (WO S T)} {𝓕 : Set (WO S T)} (hψ : IsStdChar D ψ (-1)) (hθ : IsInfFam θ)
    (hμ : IsCovolOne (ratL T S) μ 𝓕) {lam : AF D.host.F →+ ℂ} (hl : Continuous lam)
    (hlam : ∀ a, sndA D.host.F a = 0 → ψ a = Complex.exp (lam a)) (τ : D.what₂.Tau)
    (sS : Matrix (Fin S.rank) (Fin S.rank) ℂ) (sT : Matrix (Fin T.rank) (Fin T.rank) ℂ)
    (z : Matrix (Fin T.rank) (Fin S.rank) ℂ) {f g : WO S T → ℂ} (hf : IsThetaFunO ψ S T f)
    (hg : IsThetaFunO ψ S T g) (hvf : IsFockVacAt (heisO ψ S T) θ τ (cplxO sS sT) f)
    (hvg : IsFockVacAt (heisO ψ S T) θ τ (cplxO sS sT) g) :
    ipO μ 𝓕 (heisO ψ S T (lineAt θ τ z 1) f) g =
      Complex.exp (-(phase lam S T (lineAt θ τ z 1) (lineAt θ τ z 1) +
        Complex.I * phase lam S T (lineAt θ τ (Complex.I • (sT * z * sS)) 1) (lineAt θ τ z 1)) / 2) *
        ipO μ 𝓕 f g := by
  have U := _root_.GlobalTheory.ThetaPairingLaws.ipO_laws D ψ S T μ 𝓕 hψ hμ
  set J := Complex.I • (sT * z * sS) with hJ
  obtain ⟨hLc, hL0, -⟩ := GlobalTheory.WeilVacMove.isLineAt_lineAt hθ τ z
  obtain ⟨hLc', hL0', -⟩ := GlobalTheory.WeilVacMove.isLineAt_lineAt hθ τ J
  set L := lineAt θ τ z with hLeq
  set L' := lineAt θ τ J with hLJeq
  set Dz := Formalism.IndefR.Datum.dRho (heisO ψ S T) θ τ z with hDz
  set DJ := Formalism.IndefR.Datum.dRho (heisO ψ S T) θ τ J with hDJ
  have vf : Dz f + Complex.I • DJ f = 0 := hvf z
  have vg : Dz g + Complex.I • DJ g = 0 := hvg z
  have hp : ∀ (u : WO S T) (s : ℝ), phase lam S T u (L s) = (s : ℂ) * phase lam S T u (L 1) := by
    intro u s
    have hc : Continuous ((phase lam S T u).comp L) :=
      hl.comp (GlobalTheory.WeilVacMove.continuous_symplOH S T hLc continuous_const)
    exact GlobalTheory.WeilVacMove.additive_real _ hc s
  have key : ∀ s : ℝ, HasDerivAt (fun t : ℝ => ipO μ 𝓕 (heisO ψ S T (L t) f) g)
      ((s : ℂ) * -(phase lam S T (L 1) (L 1) + Complex.I * phase lam S T (L' 1) (L 1)) *
        ipO μ 𝓕 (heisO ψ S T (L s) f) g) s := by
    intro s
    set h := heisO ψ S T (L s) f with hheq
    have hh : IsThetaFunO ψ S T h := GlobalTheory.WeilVacMove.isTheta_heisO_real hψ (hL0 s) hf
    obtain ⟨hder, hXs⟩ := _root_.GlobalTheory.MatrixCoeffDeriv.hasDerivAt_ipO_and_skew D ψ θ S T μ 𝓕 hψ hθ hμ h g hh hg τ z
    have hYs := (_root_.GlobalTheory.MatrixCoeffDeriv.hasDerivAt_ipO_and_skew D ψ θ S T μ 𝓕 hψ hθ hμ h g hh hg τ J).2
    have h0 : HasDerivAt (fun t : ℝ => ipO μ 𝓕 (heisO ψ S T (L (t + s)) f) g) (ipO μ 𝓕 (Dz h) g) (s - s) := by
      rw [sub_self]
      refine hder.congr_of_eventuallyEq (Filter.Eventually.of_forall fun t => ?_)
      show ipO μ 𝓕 (heisO ψ S T (L (t + s)) f) g = ipO μ 𝓕 (heisO ψ S T (L t) h) g
      rw [hheq, GlobalTheory.WeilVacMove.heisO_line_add hψ hLc hL0 t s f]
    have hd := (h0.comp_sub_const s s)
    simp only [sub_add_cancel] at hd
    refine hd.congr_deriv ?_
    have hDzh := GlobalTheory.WeilVacMove.isTheta_dRho hψ hθ τ z hh
    have hDJh : IsThetaFunO ψ S T (DJ h) := GlobalTheory.WeilVacMove.isTheta_dRho hψ hθ τ J hh
    have hDJg := GlobalTheory.WeilVacMove.isTheta_dRho hψ hθ τ J hg
    have cA : Dz h + Complex.I • DJ h =
        (-2 * (phase lam S T (L 1) (L s) + Complex.I * phase lam S T (L' 1) (L s))) • h := by
      funext x
      have c1 : Dz h x = -2 * phase lam S T (L 1) (L s) * h x +
          ψ (symplOH S T x (L s)) * Dz f (x + L s) := dLine_heisO hψ hl hlam hLc hL0 (L s) hf x
      have c2 : DJ h x = -2 * phase lam S T (L' 1) (L s) * h x +
          ψ (symplOH S T x (L s)) * DJ f (x + L s) := dLine_heisO hψ hl hlam hLc' hL0' (L s) hf x
      have c3 := congrFun vf (x + L s)
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply] at c3 ⊢
      rw [c1, c2]
      linear_combination ψ (symplOH S T x (L s)) * c3
    have e3 : ipO μ 𝓕 h (Dz g) = Complex.I * ipO μ 𝓕 h (DJ g) := by
      have hz : Dz g = (-Complex.I) • DJ g := by rw [neg_smul]; exact eq_neg_of_add_eq_zero_left vg
      rw [hz, ((U h (DJ g) hh hDJg).2.2.1 (-Complex.I)).2]
      simp [Complex.conj_I]
    have e4 : ipO μ 𝓕 (Dz h + Complex.I • DJ h) g = ipO μ 𝓕 (Dz h) g + Complex.I * ipO μ 𝓕 (DJ h) g := by
      have hsmul : IsThetaFunO ψ S T (Complex.I • DJ h) := by
        refine { quasi := ?_, level := ?_, cont := ?_, smooth := ?_ }
        · intro γ w
          rw [Pi.smul_apply, Pi.smul_apply, hDJh.quasi, smul_eq_mul, smul_eq_mul, mul_left_comm]
        · obtain ⟨U, hU, h1⟩ := hDJh.level
          refine ⟨U, hU, fun u hu h0 => ?_⟩
          funext w
          have e1 := congrFun (h1 u hu h0) w
          change ψ (symplOH S T w u) * DJ h (w + u) = DJ h w at e1
          unfold heisO
          rw [Pi.smul_apply, Pi.smul_apply, smul_eq_mul, smul_eq_mul, mul_left_comm, e1]
        · exact hDJh.cont.const_smul Complex.I
        · intro k L h1 h2 w
          exact contDiff_const.mul (hDJh.smooth k L h1 h2 w)
      rw [((U (Dz h) g hDzh hg).2.2.2.1 _ hsmul).1,
        ((U (DJ h) g hDJh hg).2.2.1 Complex.I).1]
    rw [cA, ((U h g hh hg).2.2.1 _).1, hp (L 1) s, hp (L' 1) s] at e4
    linear_combination (-1 / 2 : ℂ) * e4 + (1 / 2 : ℂ) * hXs - (Complex.I / 2) * hYs - (1 / 2 : ℂ) * e3
  have hfin := gauss_ode _ _ key
  simp only [map_zero, GlobalTheory.WeilVacMove.heisO_zero] at hfin
  exact hfin

theorem compress : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (S T : HSp D) (μ : Measure (WO S T)) (𝓕 : Set (WO S T)), IsStdChar D ψ (-1) → IsInfFam θ → IsCovolOne (ratL T S) μ 𝓕 → ∀ (τ : D.what₂.Tau) (sS : Matrix (Fin S.rank) (Fin S.rank) ℂ) (sT : Matrix (Fin T.rank) (Fin T.rank) ℂ), IsCartanInv (gramAt D S τ) sS → IsCartanInv (gramAt D T τ) sT → ∀ w : WO S T, ∃ γ : ℂ, ∀ f g : WO S T → ℂ, IsThetaFunO ψ S T f → IsThetaFunO ψ S T g → IsFockVacAt (heisO ψ S T) θ τ (cplxO sS sT) f → IsFockVacAt (heisO ψ S T) θ τ (cplxO sS sT) g → ipO μ 𝓕 g (heisO ψ S T (wAt (.inr τ) w) f) = γ * ipO μ 𝓕 g f := by
  intro D ψ θ S T μ 𝓕 hψ hθ hμ τ sS sT _ _ w
  obtain ⟨lam, hl, hlam⟩ := GlobalTheory.WeilVacMove.exists_log hψ
  refine ⟨starRingEnd ℂ (Complex.exp (-(phase lam S T (lineAt θ τ (compAt θ τ w) 1) (lineAt θ τ (compAt θ τ w) 1) +
      Complex.I * phase lam S T (lineAt θ τ (Complex.I • (sT * compAt θ τ w * sS)) 1)
        (lineAt θ τ (compAt θ τ w) 1)) / 2)), ?_⟩
  intro f g hf hg hvf hvg
  have U := _root_.GlobalTheory.ThetaPairingLaws.ipO_laws D ψ S T μ 𝓕 hψ hμ
  obtain ⟨-, hL0, -⟩ := GlobalTheory.WeilVacMove.isLineAt_lineAt hθ τ (compAt θ τ w)
  have h1 := GlobalTheory.WeilVacMove.isTheta_heisO_real hψ (hL0 1) hf
  rw [wAt_eq_lineAt hθ τ w, (U _ g h1 hg).2.1, (U f g hf hg).2.1,
    flow_lemma hψ hθ hμ hl hlam τ sS sT (compAt θ τ w) hf hg hvf hvg, map_mul]

end GlobalTheory.VacCompress

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.HeisenbergOperatorPureTensorPlaceByPlace
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting GlobalTheory.PlaceTensor
open scoped TensorProduct ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.PlaceTensorHeis

open GlobalTheory.SplitScalar GlobalTheory.LatVac

variable {D : D7} {S T : HSp D}

theorem wAt_wAt (p : Place D) (w : WO S T) : wAt p (wAt p w) = wAt p w := by
  rw [wAt_eq_smul, wAt_eq_smul, smul_smul, (_root_.GlobalTheory.PlaceTensor.idem_spec D).1 p]

theorem wAt_off {P : Finset (Place D)} {w r : WO S T} (h : w = ∑ q ∈ P, wAt q w + r) {p : Place D} (hp : p ∉ P) :
    wAt p w = wAt p r := by
  have e : wAt p w = wAt p (∑ q ∈ P, wAt q w + r) := by rw [← h]
  simp only [wAt_eq_smul, smul_add, Finset.smul_sum, smul_smul] at e ⊢
  rw [e, Finset.sum_eq_zero, zero_add]
  intro q hq
  rw [(_root_.GlobalTheory.PlaceTensor.idem_spec D).2.1 p q (fun hpq => hp (hpq ▸ hq)), zero_smul]

theorem wAt_on {P : Finset (Place D)} {w r : WO S T} (h : w = ∑ q ∈ P, wAt q w + r) {p : Place D} (hp : p ∈ P) :
    wAt p r = 0 := by
  have e : wAt p w = wAt p (∑ q ∈ P, wAt q w + r) := by rw [← h]
  simp only [wAt_eq_smul, smul_add, Finset.smul_sum, smul_smul] at e ⊢
  rw [Finset.sum_eq_single p (fun q _ hqp => by rw [(_root_.GlobalTheory.PlaceTensor.idem_spec D).2.1 p q (Ne.symm hqp), zero_smul])
    (fun hn => absurd hp hn), (_root_.GlobalTheory.PlaceTensor.idem_spec D).1 p] at e
  exact add_left_cancel (e.symm.trans (add_zero _).symm)

theorem symplO_wAt (p : Place D) (x y : WO S T) : symplO S T (wAt p x) y = symplO S T x (wAt p y) := by
  rw [wAt_eq_smul, wAt_eq_smul, GlobalTheory.SplitScalar.symplO_smul, (_root_.GlobalTheory.PlaceTensor.idem_spec D).2.2.1 p]

private theorem symplO_sum_wAt_left (P : Finset (Place D)) (x y : WO S T) :
    symplO S T (∑ q ∈ P, wAt q x) y = ∑ q ∈ P, symplO S T (wAt q x) (wAt q y) := by
  induction P using Finset.cons_induction with
  | empty => rw [Finset.sum_empty, Finset.sum_empty, GlobalTheory.SplitScalar.symplO_zero_left]
  | cons a s ha ih =>
    rw [Finset.sum_cons, Finset.sum_cons, GlobalTheory.LatVac.symplO_add_left, ih, ← symplO_wAt, wAt_wAt]

private theorem wAt_add' (p : Place D) (x y : WO S T) : wAt p (x + y) = wAt p x + wAt p y := by
  rw [wAt_eq_smul, wAt_eq_smul, wAt_eq_smul, smul_add]

theorem symplO_split {P : Finset (Place D)} {w r w' r' : WO S T} (h : w = ∑ q ∈ P, wAt q w + r)
    (h' : w' = ∑ q ∈ P, wAt q w' + r') :
    symplO S T w w' = ∑ q ∈ P, symplO S T (wAt q w) (wAt q w') + symplO S T r r' := by
  have hr : ∀ q ∈ P, wAt q r = 0 := fun q hq => wAt_on h hq
  have hr' : ∀ q ∈ P, wAt q r' = 0 := fun q hq => wAt_on h' hq
  have hB : ∀ q ∈ P, wAt q (∑ q' ∈ P, wAt q' w') = wAt q w' := by
    intro q hq
    have e : wAt q w' = wAt q (∑ q' ∈ P, wAt q' w' + r') := by rw [← h']
    rw [wAt_add', hr' q hq, add_zero] at e
    exact e.symm
  have s1 : ∑ q ∈ P, symplO S T (wAt q w) (wAt q (∑ q' ∈ P, wAt q' w')) =
      ∑ q ∈ P, symplO S T (wAt q w) (wAt q w') :=
    Finset.sum_congr rfl fun q hq => by rw [hB q hq]
  have s2 : ∑ q ∈ P, symplO S T (wAt q w) (wAt q r') = 0 :=
    Finset.sum_eq_zero fun q hq => by rw [hr' q hq, GlobalTheory.SplitScalar.symplO_zero_right]
  have s3 : ∑ q ∈ P, symplO S T (wAt q w') (wAt q r) = 0 :=
    Finset.sum_eq_zero fun q hq => by rw [hr q hq, GlobalTheory.SplitScalar.symplO_zero_right]
  conv_lhs => rw [h, h']
  rw [GlobalTheory.LatVac.symplO_add_left, GlobalTheory.LatVac.symplO_add_right, GlobalTheory.LatVac.symplO_add_right,
    symplO_sum_wAt_left, symplO_sum_wAt_left, GlobalTheory.SplitScalar.symplO_skew S T (∑ q ∈ P, wAt q w') r,
    symplO_sum_wAt_left, s1, s2, s3, add_zero, neg_zero, zero_add]

variable {ψ : AddChar (AF D.host.F) ℂ}
  {ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)} {ΛT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)}

theorem cocycle_two (hψ : IsStdChar D ψ (-1)) (hS : IsSelfDualC S ΛS) (hT : IsSelfDualC T ΛT) {u u' : WO S T}
    (hu : u ∈ latO S T ΛS ΛT fun _ => True) (hu' : u' ∈ latO S T ΛS ΛT fun _ => True) :
    ψ (symplOH S T (2 • u) (2 • u')) = 1 := by
  have hd : ψ (symplO S T u u') = 1 :=
    ((_root_.GlobalTheory.LatVac.latO_selfDual_approx_sign D ψ S T ΛS ΛT hψ hS hT).1 u (GlobalTheory.SplitScalar.latO_fin hu)).mp hu u' hu'
  rw [two_nsmul, two_nsmul, GlobalTheory.SplitScalar.symplOH_add_left, GlobalTheory.SplitScalar.symplOH_add_right,
    GlobalTheory.SplitScalar.symplOH_add_self, AddChar.map_add_eq_mul, hd, one_mul]

theorem wAt_mem {u : WO S T} (hu : u ∈ latO S T ΛS ΛT fun _ => True) (p : Place D) :
    wAt p u ∈ latO S T ΛS ΛT fun _ => True :=
  latO_mono (fun _ _ => trivial) (_root_.GlobalTheory.LatticeLocal.wAt_mem_latO D S T ΛS ΛT _ u hu p).1

theorem wAt_two (p : Place D) (u : WO S T) : wAt p (2 • u) = 2 • wAt p u := by
  rw [two_nsmul, two_nsmul, wAt_eq_smul, wAt_eq_smul, smul_add]

private theorem eq_zero_of_add_self_eq_zero_AF {a : AF D.host.F} (h : a + a = 0) : a = 0 := by
  have h2 : IsUnit (2 : AF D.host.F) := by
    rw [← map_ofNat (algebraMap D.host.F (AF D.host.F)) 2]
    exact (IsUnit.mk0 (2 : D.host.F) two_ne_zero).map _
  rw [← two_mul] at h
  exact h2.mul_right_eq_zero.mp h

private theorem symplOH_eq_sum_wAt_add_of_decomp {P : Finset (Place D)} {w r w' r' : WO S T} (h : w = ∑ q ∈ P, wAt q w + r)
    (h' : w' = ∑ q ∈ P, wAt q w' + r') :
    symplOH S T w w' = ∑ q ∈ P, symplOH S T (wAt q w) (wAt q w') + symplOH S T r r' := by
  apply sub_eq_zero.mp
  apply eq_zero_of_add_self_eq_zero_AF
  rw [sub_add_sub_comm, GlobalTheory.SplitScalar.symplOH_add_self, add_add_add_comm, ← Finset.sum_add_distrib]
  simp only [GlobalTheory.SplitScalar.symplOH_add_self]
  rw [symplO_split h h', sub_self]

private theorem addChar_sum_eq_prod' (ψ : AddChar (AF D.host.F) ℂ) (s : Finset (Place D)) (g : Place D → AF D.host.F) :
    ψ (∑ p ∈ s, g p) = ∏ p ∈ s, ψ (g p) := by
  induction s using Finset.cons_induction with
  | empty => rw [Finset.sum_empty, Finset.prod_empty, AddChar.map_zero_eq_one]
  | cons a s ha ih => rw [Finset.sum_cons, Finset.prod_cons, AddChar.map_add_eq_mul, ih]

theorem cocycle_prod (hψ : IsStdChar D ψ (-1)) (hS : IsSelfDualC S ΛS) (hT : IsSelfDualC T ΛT) (w w' : WO S T) :
    ∃ P : Finset (Place D), (∀ p ∉ P, ψ (symplOH S T (wAt p w) (wAt p w')) = 1) ∧
      ψ (symplOH S T w w') = ∏ p ∈ P, ψ (symplOH S T (wAt p w) (wAt p w')) := by
  classical
  obtain ⟨P₀, hP₀⟩ := _root_.GlobalTheory.PlaceTensor.CompDecomp.exists_eq_sum_wAt_add_two_smul D S T ΛS ΛT hS hT w
  obtain ⟨P₁, hP₁⟩ := _root_.GlobalTheory.PlaceTensor.CompDecomp.exists_eq_sum_wAt_add_two_smul D S T ΛS ΛT hS hT w'
  obtain ⟨u, hu, hw⟩ := hP₀ (P₀ ∪ P₁) (fun _ hx => Finset.mem_union_left _ hx)
  obtain ⟨u', hu', hw'⟩ := hP₁ (P₀ ∪ P₁) (fun _ hx => Finset.mem_union_right _ hx)
  refine ⟨P₀ ∪ P₁, fun p hp => ?_, ?_⟩
  · rw [wAt_off hw hp, wAt_off hw' hp, wAt_two, wAt_two]
    exact cocycle_two hψ hS hT (wAt_mem hu p) (wAt_mem hu' p)
  · rw [symplOH_eq_sum_wAt_add_of_decomp hw hw', AddChar.map_add_eq_mul, cocycle_two hψ hS hT hu hu', mul_one,
      addChar_sum_eq_prod']

theorem isPure_heisO : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (S T : HSp D) (sS : D.what₂.Tau → Matrix (Fin S.rank) (Fin S.rank) ℂ) (sT : D.what₂.Tau → Matrix (Fin T.rank) (Fin T.rank) ℂ) (ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)) (ΛT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)) (f₀ : WO S T → ℂ) (μ : Measure (WO S T)) (𝓕 : Set (WO S T)), IsBase ψ θ S T sS sT ΛS ΛT f₀ → IsCovolOne (ratL T S) μ 𝓕 → ∀ (x : Place D → WO S T → ℂ) (f : WO S T → ℂ), IsPure ψ θ S T sS sT ΛS ΛT μ 𝓕 f₀ x f → ∀ w : WO S T, IsPure ψ θ S T sS sT ΛS ΛT μ 𝓕 f₀ (fun p => heisO ψ S T (wAt p w) (x p)) (heisO ψ S T w f) := by
  intro D ψ θ S T sS sT ΛS ΛT f₀ μ 𝓕 hB hμ x f hx w
  classical
  have hψ := base_std hB
  have hθ := base_inf hB
  have hf₀ := base_theta hB
  have hB' := hB
  unfold IsBase at hB'
  have hS : IsSelfDualC S ΛS := hB'.2.2.1
  have hT : IsSelfDualC T ΛT := hB'.2.2.2.1
  have laws := GlobalTheory.HeisThetaLaws.heis_theta_laws D ψ hψ S T
  unfold IsPure IsRestricted at hx ⊢
  obtain ⟨⟨hloc, hfin⟩, hf, hprod⟩ := hx
  have hxθ : ∀ p, IsThetaFunO ψ S T (x p) := fun p => by
    have hl := hloc p
    unfold IsLocal at hl
    exact hl.1
  have hneg : ∀ (p : Place D) (a : WO S T), wAt p (-a) = -wAt p a := fun p a => by
    rw [wAt_eq_smul, wAt_eq_smul, smul_neg]
  have hadd : ∀ (p : Place D) (a b : WO S T), wAt p (a + b) = wAt p a + wAt p b := fun p a b => by
    rw [wAt_eq_smul, wAt_eq_smul, wAt_eq_smul, smul_add]

  obtain ⟨P₀, hP₀⟩ := _root_.GlobalTheory.PlaceTensor.CompDecomp.exists_eq_sum_wAt_add_two_smul D S T ΛS ΛT hS hT w
  obtain ⟨u, hu, hwu⟩ := hP₀ P₀ (Finset.Subset.refl _)
  have hvac : ∀ p, p ∉ P₀ → (∀ τ, p ≠ .inr τ) → heisO ψ S T (wAt p w) f₀ = f₀ := by
    intro p hp hτ
    rcases p with v | τ
    · have hv : IsLatVac (heisO ψ S T) (latO S T ΛS ΛT fun u => u = v) f₀ := base_vacAt hB (.inl v)
      rw [wAt_off hwu hp, wAt_two]
      refine hv.1 _ (latO_mono ?_ (_root_.GlobalTheory.LatticeLocal.wAt_mem_latO D S T ΛS ΛT _ u hu (.inl v)).1)
      rintro v' ⟨-, hv'⟩
      exact Sum.inl_injective hv'
    · exact absurd rfl (hτ τ)
  have hfinV : {p : Place D | heisO ψ S T (wAt p w) f₀ ≠ f₀}.Finite := by
    refine ((P₀.finite_toSet).union (Set.finite_range (Sum.inr : D.what₂.Tau → Place D))).subset ?_
    intro p hp
    by_contra hc
    simp only [Set.mem_union, Finset.mem_coe, Set.mem_range, not_or, not_exists] at hc
    exact hp (hvac p hc.1 fun τ h => hc.2 τ h.symm)
  refine ⟨⟨fun p => ((_root_.GlobalTheory.PlaceStable.heis_stable D ψ θ S T sS sT ΛS ΛT hψ hθ (x p) (hxθ p)).2 p (hloc p)).1 w, ?_⟩,
    laws.1 w f hf, fun w' => ?_⟩
  · refine (hfin.union hfinV).subset ?_
    intro p hp
    by_contra hc
    simp only [Set.mem_union, Set.mem_setOf_eq, not_or, not_not] at hc
    apply hp
    show heisO ψ S T (wAt p w) (x p) = f₀
    rw [hc.1, hc.2]

  have hfac : ∀ p, ipO μ 𝓕 (heisO ψ S T (wAt p w) (x p)) (heisO ψ S T (wAt p w') f₀) =
      (starRingEnd ℂ) (ψ (symplOH S T (wAt p (-w)) (wAt p w'))) *
        ipO μ 𝓕 (x p) (heisO ψ S T (wAt p (-w + w')) f₀) := by
    intro p
    have I := _root_.GlobalTheory.ThetaPairingLaws.ipO_laws D ψ S T μ 𝓕 hψ hμ (x p) (heisO ψ S T (wAt p (-w + w')) f₀) (hxθ p) (laws.1 _ f₀ hf₀)
    have J := _root_.GlobalTheory.ThetaPairingLaws.ipO_laws D ψ S T μ 𝓕 hψ hμ (x p) (heisO ψ S T (wAt p w') f₀) (hxθ p) (laws.1 _ f₀ hf₀)
    rw [(J.2.2.2.2.2.2.1 (wAt p w)).2, laws.2.1, ← hneg, ← hadd, (I.2.2.1 _).2]
  obtain ⟨P, hP1, hP2⟩ := cocycle_prod hψ hS hT (-w) w'
  have hcfin : (Function.mulSupport fun p => (starRingEnd ℂ) (ψ (symplOH S T (wAt p (-w)) (wAt p w')))) ⊆ ↑P := by
    intro p hp
    by_contra hc
    simp only [Function.mem_mulSupport] at hp
    exact hp (by rw [hP1 p (fun h => hc (Finset.mem_coe.mpr h)), map_one])
  have hgfin := (hprod (-w + w')).1
  beta_reduce
  simp only [hfac]
  refine ⟨((P.finite_toSet.subset hcfin).union hgfin).subset (Function.mulSupport_mul _ _), ?_⟩
  have K0 := _root_.GlobalTheory.ThetaPairingLaws.ipO_laws D ψ S T μ 𝓕 hψ hμ f (heisO ψ S T w' f₀) hf (laws.1 _ _ hf₀)
  have K1 := _root_.GlobalTheory.ThetaPairingLaws.ipO_laws D ψ S T μ 𝓕 hψ hμ f (heisO ψ S T (-w + w') f₀) hf (laws.1 _ _ hf₀)
  rw [(K0.2.2.2.2.2.2.1 w).2, laws.2.1, (K1.2.2.1 _).2, (hprod (-w + w')).2, hP2, map_prod,
    finprod_mul_distrib (P.finite_toSet.subset hcfin) hgfin, finprod_eq_prod_of_mulSupport_subset _ hcfin]

end GlobalTheory.PlaceTensorHeis
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.IntegralLeviPhaseChangeOfVariables
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum MeasureTheory NumberField Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.LeviNorm

variable {D : D7}

def sandwichHomeo {m n : ℕ} (P : GL (Fin m) (AE D)) (Q : GL (Fin n) (AE D)) : Mx D m n ≃ₜ Mx D m n where
  toFun u := HMul.hMul (HMul.hMul P.val u) Q.val
  invFun v := HMul.hMul (HMul.hMul (P⁻¹).val v) (Q⁻¹).val
  left_inv u := by
    simp only [Matrix.mul_assoc, Units.mul_inv, Matrix.mul_one]
    rw [← Matrix.mul_assoc, Units.inv_mul, Matrix.one_mul]
  right_inv v := by
    simp only [Matrix.mul_assoc, Units.inv_mul, Matrix.mul_one]
    rw [← Matrix.mul_assoc, Units.mul_inv, Matrix.one_mul]
  continuous_toFun := (continuous_const.matrix_mul continuous_id).matrix_mul continuous_const
  continuous_invFun := (continuous_const.matrix_mul continuous_id).matrix_mul continuous_const

theorem phase_sandwich (ψ : AddChar (AF D.host.F) ℂ) (W : HSp D) {r : ℕ} (h : GA D W) (a : GL (Fin r) (AE D))
    (y u : Mx D W.rank r) :
    phase ψ W (HMul.hMul (HMul.hMul (Formalism.L2.Theta.mt W h⁻¹) y) (GlobalTheory.MixModel.adj (a⁻¹).val))
      (HMul.hMul (HMul.hMul (Formalism.L2.Theta.mt W h⁻¹) u) a.val) = phase ψ W y u := by
  rw [phase_apply, phase_apply]
  congr 3
  have hu := GlobalTheory.MixModel.mt_unitary W h⁻¹
  have adj_mul_local {l m n : ℕ} (x : Mx D l m) (y : Mx D m n) :
      GlobalTheory.MixModel.adj (x * y) = GlobalTheory.MixModel.adj y * GlobalTheory.MixModel.adj x := by
    unfold GlobalTheory.MixModel.adj
    rw [Matrix.map_mul, Matrix.transpose_mul]
  change (GlobalTheory.MixModel.adj ((Formalism.L2.Theta.mt W h⁻¹) * y * (GlobalTheory.MixModel.adj (a⁻¹).val)) *
    (GlobalTheory.MixModel.gA W * ((Formalism.L2.Theta.mt W h⁻¹) * u * a.val))).trace = _
  simp only [adj_mul_local, GlobalTheory.MixModel.adj_adj]
  simp only [Matrix.mul_assoc]
  rw [← Matrix.mul_assoc (GlobalTheory.MixModel.gA W) (Formalism.L2.Theta.mt W h⁻¹),
    ← Matrix.mul_assoc (GlobalTheory.MixModel.adj (Formalism.L2.Theta.mt W h⁻¹)), hu, Matrix.trace_mul_comm]
  simp only [Matrix.mul_assoc, Units.mul_inv, Matrix.mul_one]

theorem absE_det_matHom_inv {W : HSp D} (h : GA D W)
    (hh : GlobalTheory.Doubling.absE D.host.F D.host.E (Matrix.GeneralLinearGroup.det (Formalism.L2.Theta.matHom W h)) = 1) :
    GlobalTheory.Doubling.absE D.host.F D.host.E (Matrix.GeneralLinearGroup.det (Formalism.L2.Theta.matHom W h⁻¹)) = 1 := by
  rw [map_inv, map_inv, map_inv, hh, inv_one]

theorem absE_det_pow_ne {r : ℕ} (a : GL (Fin r) (AE D)) (k : ℕ) :
    ((GlobalTheory.Doubling.absE D.host.F D.host.E (Matrix.GeneralLinearGroup.det a) : ENNReal) ^ k) ≠ 0 ∧
      ((GlobalTheory.Doubling.absE D.host.F D.host.E (Matrix.GeneralLinearGroup.det a) : ENNReal) ^ k) ≠ ⊤ :=
  ⟨pow_ne_zero _ (ENNReal.coe_ne_zero.2 ((Group.isUnit (Matrix.GeneralLinearGroup.det a)).map
    (GlobalTheory.Doubling.absE D.host.F D.host.E)).ne_zero), ENNReal.pow_ne_top ENNReal.coe_ne_top⟩


set_option maxHeartbeats 800000 in
theorem integral_phase_sandwich : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ (W : HSp D) (r : ℕ) (μ : Measure (Mx D W.rank r)), μ.IsAddHaarMeasure → ∀ (h : GA D W), GlobalTheory.Doubling.absE D.host.F D.host.E (Matrix.GeneralLinearGroup.det (matHom W h)) = 1 → ∀ (a : GL (Fin r) (AE D)) (N : Mx D W.rank r → ℂ), Continuous N → Integrable N μ → Integrable (fun u : Mx D W.rank r => N (HMul.hMul (HMul.hMul (Formalism.L2.Theta.mt W h⁻¹) u) a.val)) μ ∧ ∀ y : Mx D W.rank r, ∫ u, GlobalTheory.LeviNorm.phase ψ W (HMul.hMul (HMul.hMul (Formalism.L2.Theta.mt W h⁻¹) y) (GlobalTheory.MixModel.adj (a⁻¹).val)) u * N u ∂μ = ((GlobalTheory.Doubling.absE D.host.F D.host.E (Matrix.GeneralLinearGroup.det a) : ℝ) : ℂ) ^ W.rank * ∫ u, GlobalTheory.LeviNorm.phase ψ W y u * N (HMul.hMul (HMul.hMul (Formalism.L2.Theta.mt W h⁻¹) u) a.val) ∂μ := by
  intro D ψ _ W r μ hμ h hh a N _ hNi
  haveI : BorelSpace (Mx D W.rank r) := ⟨rfl⟩
  have hmod := _root_.GlobalTheory.ModuLR.modu_lrMul D W.rank r μ hμ (Formalism.L2.Theta.matHom W h⁻¹) a
  have h1 := absE_det_matHom_inv h hh
  rw [h1, ENNReal.coe_one, one_pow, one_mul] at hmod
  obtain ⟨hc0, hcT⟩ := absE_det_pow_ne a W.rank
  let e := (sandwichHomeo (Formalism.L2.Theta.matHom W h⁻¹) a).toMeasurableEquiv
  have he : ∀ u, e u = HMul.hMul (HMul.hMul (Formalism.L2.Theta.mt W h⁻¹) u) a.val := fun _ => rfl
  have hmap : (Measure.map (fun u : Mx D W.rank r =>
      (HMul.hMul (HMul.hMul (Formalism.L2.Theta.matHom W h⁻¹).val (u : Matrix (Fin W.rank) (Fin r) (AE D))) a.val :
        Mx D W.rank r)) μ) = Measure.map e μ := rfl
  rw [hmap] at hmod
  refine ⟨?_, fun y => ?_⟩
  · rw [hmod, integrable_smul_measure hc0 hcT, integrable_map_equiv] at hNi
    exact hNi
  · conv_lhs => rw [hmod]
    rw [integral_smul_measure, integral_map_equiv]
    simp only [he, phase_sandwich]
    rw [ENNReal.toReal_pow, ENNReal.coe_toReal, Complex.real_smul]
    push_cast
    rfl

end GlobalTheory.LeviNorm
end
end

