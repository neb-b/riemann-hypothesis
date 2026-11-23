module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0221
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0013
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleDiscreteSeriesOfHasParam
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HasDRepIffHasDerivAt
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0275
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ThetaInnerFockProductEqProdRealPlaces
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0152
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0162
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0292
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0299
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0300
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsCombAt
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0018
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ExistsUnitarySupportedAtPlaceOfMulEqIdem
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0009
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0297

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ThetaChainRealZetaNonvanishing
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.S Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory NumberField Matrix
open GlobalTheory.Chain GlobalTheory.ChainFr GlobalTheory.PairLift GlobalTheory.Chain.RealIt
open scoped TensorProduct InnerProductSpace ComplexConjugate
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.RealZetaProof


open GlobalTheory.IndefiniteRowSideFullHecke.ThetaSourceAction in
theorem realZeta : GlobalTheory.Published.HarishChandraModules → ∀ D : D7, GlobalTheory.IndefiniteRowSideFullHecke.ThetaSourceAction.ArchOnRecord D → GlobalTheory.ChainOnto.RealZeta D := by
  intro hHC D hA hgap c hc k hk s s' hs hs' p hp m X hmX
  obtain ⟨hWexp, hvac⟩ := _root_.GlobalTheory.ChainOnto.StepExp.stepExpVac D hgap c hc k hk s s' hs hs' p hp hk
  obtain ⟨χS, χT, hW, hexp⟩ := hWexp
  have hCT := (hA.2 hgap).1
  have hfock : ∀ τ, IsFockAt c.ψ c.θ s.V s'.V τ (cart s.M τ) (cart s'.M τ) (onb s.M τ) (onb s'.M τ) p.f :=
    fun τ => ⟨hc.inf, isAdapted_model s.M τ, isAdapted_model s'.M τ, hvac.theta, hvac.ne, hvac.vac τ⟩
  have hSe : ∀ τ, alS D ⟨k, hk⟩ τ = expS D ⟨k, hk⟩ τ := by
    intro τ
    simp only [alS, expS]
    rcases Nat.even_or_odd k with h | h
    · simp [h, h.add_one]
    · have h1 : ¬ Odd (k + 1) := by rw [Nat.odd_add_one]; simpa using h
      have h2 : ¬ Even k := by simpa using h
      simp [h1, h2]
  have hTe : ∀ τ, alT D ⟨k, hk⟩ τ = expT D ⟨k, hk⟩ τ := by
    intro τ
    simp only [alT, expT]
    rcases Nat.even_or_odd k with h | h
    · simp [h, h.add_one]
    · have h1 : ¬ Odd (k + 1) := by rw [Nat.odd_add_one]; simpa using h
      have h2 : ¬ Even k := by simpa using h
      simp [h1, h2]
  have hpar : ∀ τ, s.par τ = parB (Ptw D) ((⟨k, hk⟩ : Fin D.R.m) : ℕ) τ := fun τ => by rw [hs.par]
  have hpar' : ∀ τ, s'.par τ = parB (Ptw D) (((⟨k, hk⟩ : Fin D.R.m) : ℕ) + 1) τ := fun τ => by rw [hs'.par]
  have hLL := fun τ => (hCT ⟨k, hk⟩ τ s.V s'.V).2.1 c.ψ c.θ χS χT p.ω hW (by rw [hSe]; exact (hexp τ).1)
    (by rw [hTe]; exact (hexp τ).2) s.par s'.par s.M s'.M (hpar τ) (hpar' τ) _ _ p.f (hfock τ)
  have hZL := fun τ => (hCT ⟨k, hk⟩ τ s.V s'.V).2.2 c.ψ c.θ χS χT p.ω hW (by rw [hSe]; exact (hexp τ).1)
    (by rw [hTe]; exact (hexp τ).2) s.par s'.par s.M s'.M (hpar τ) (hpar' τ) _ _ p.f (hfock τ) m X hmX.1 hmX.2.1
  choose Φ hΦ using fun τ => (hLL τ).joint_ex
  choose w hwsm hwk hwhi using fun τ => _root_.GlobalTheory.RealZetaSmoothHi.exists_smooth_highestUnit hHC D s.V s.par s.M τ
  refine ⟨glue Φ, fun τ => ⟨w τ, hwsm τ⟩, fun τ => hwk τ, ?_⟩
  intro mR hmR z
  have hfac := _root_.GlobalTheory.FockProdCoef.ipTh_ptOf_glue D s.V s'.V s.par s'.par s.M s'.M c.θ c.ψ χS χT p.ω hc.inf hW m X hmX p.f hvac
  obtain ⟨cst, hcst, hhaar⟩ := _root_.GlobalTheory.HaarReal.integral_prod_eq D s.V s.par s.M c.θ hc.inf mR (fun τ => Formalism.REAL.muG (s.M.ε τ)) hmR
    (fun τ => inferInstance)
  have hZ := fun τ => hZL τ (Φ τ) (hΦ τ) ⟨w τ, hwk τ⟩ (hwhi τ) (Formalism.REAL.muG (s.M.ε τ)) inferInstance
  set i0 := ipTh m X p.f p.f with hi0
  set F : D.what₂.Tau → Matrix (Fin s.V.rank) (Fin s.V.rank) ℂ → ℂ := fun τ h =>
    ipTh m X (p.ω (atTau c.θ s.V τ h, 1) (ptAt c.ψ c.θ s.V s'.V τ (cart s.M τ) (cart s'.M τ) (onb s.M τ) (onb s'.M τ) p.f (Φ τ)))
      (ptAt c.ψ c.θ s.V s'.V τ (cart s.M τ) (cart s'.M τ) (onb s.M τ) (onb s'.M τ) p.f (Φ τ)) / i0 *
      conj ⟪(w τ : s.M.H τ), s.M.rep τ h (w τ)⟫_ℂ with hF
  have hrep : ∀ τ (Y : Matrix (Fin s.V.rank) (Fin s.V.rank) ℂ), s.M.rep τ (ofFr s.M τ Y) = s.M.σ τ Y := by
    intro τ Y
    have h1 : s.M.fr τ * (s.M.fr τ)⁻¹ = 1 := Matrix.mul_nonsing_inv _ ((Matrix.isUnit_iff_isUnit_det _).1 (s.M.fr_unit τ))
    have : s.M.fr τ * ((s.M.fr τ)⁻¹ * Y * s.M.fr τ) * (s.M.fr τ)⁻¹ = Y := by
      calc s.M.fr τ * ((s.M.fr τ)⁻¹ * Y * s.M.fr τ) * (s.M.fr τ)⁻¹
          = (s.M.fr τ * (s.M.fr τ)⁻¹) * Y * (s.M.fr τ * (s.M.fr τ)⁻¹) := by simp only [Matrix.mul_assoc]
        _ = Y := by rw [h1]; simp
    simp only [DSModel.rep, ofFr, this]
  have hFu : ∀ τ (u : Formalism.REAL.UJ (s.M.ε τ)), F τ (ofFr s.M τ (umat u)) =
      ipTh m X (actSrc c.θ p.ω τ (ofFr s.M τ (umat u))
        (ptAt c.ψ c.θ s.V s'.V τ (cart s.M τ) (cart s'.M τ) (onb s.M τ) (onb s'.M τ) p.f (Φ τ)))
        (ptAt c.ψ c.θ s.V s'.V τ (cart s.M τ) (cart s'.M τ) (onb s.M τ) (onb s'.M τ) p.f (Φ τ)) *
        star (coefOn (s.M.σ τ) (w τ) (w τ) u) / i0 := by
    intro τ u
    simp only [hF, hrep, actSrc, coefOn, starRingEnd_apply]
    ring
  have hFint : ∀ τ, Integrable (fun u : Formalism.REAL.UJ (s.M.ε τ) => F τ (ofFr s.M τ (umat u))) (Formalism.REAL.muG (s.M.ε τ)) := by
    intro τ; simp_rw [hFu]; exact (hZ τ).2.1.div_const _
  have hFval : ∀ τ, ∃ r : ℝ, 0 < r ∧ ∫ u, F τ (ofFr s.M τ (umat u)) ∂(Formalism.REAL.muG (s.M.ε τ)) = (r : ℂ) / i0 := by
    intro τ
    obtain ⟨r, hr, hrI⟩ := (hZ τ).2.2.1
    refine ⟨r, hr, ?_⟩
    simp_rw [hFu]; rw [integral_div, hrI]
  choose r hr hrI using hFval
  have hi0 : i0 ≠ 0 := hfac.1
  have hz : ∀ g : GinfC s.V, z g = i0 * ∏ τ, F τ (Formalism.MainNotions.StandardLattice.infMat D.sp.cm.sig s.V.gram (c.θ τ) (g : GA D s.V)) := by
    intro g
    have h := hfac.2 Φ g g.2
    change ipTh m X (p.ω ((g : GA D s.V), 1) (ptOf c.ψ c.θ s.M s'.M p.f (glue Φ))) (ptOf c.ψ c.θ s.M s'.M p.f (glue Φ)) *
      conj (∏ τ, ⟪(w τ : s.M.H τ), s.M.rep τ (Formalism.MainNotions.StandardLattice.infMat D.sp.cm.sig s.V.gram (c.θ τ) (g : GA D s.V)) (w τ)⟫_ℂ) = _
    rw [h, map_prod, mul_assoc, ← Finset.prod_mul_distrib]
  obtain ⟨hIint, hIval⟩ := hhaar F hFint
  have hintz : ∫ g, z g ∂mR = i0 * ((cst : ℂ) * ∏ τ, ((r τ : ℂ) / i0)) := by
    simp_rw [hz]; rw [integral_const_mul, hIval]; simp_rw [hrI]
  refine ⟨?_, ?_⟩
  · rw [hintz]
    exact mul_ne_zero hi0 (mul_ne_zero (by exact_mod_cast hcst.ne')
      (Finset.prod_ne_zero_iff.2 fun τ _ => div_ne_zero (by exact_mod_cast (hr τ).ne') hi0))
  · intro a ha hfr
    refine ⟨0, div_pos (by exact_mod_cast D.R.t_odd.pos) two_pos, ?_⟩
    obtain ⟨C, hC⟩ := _root_.GlobalTheory.TwBound.tw_bound D s.V s'.V s.par s'.par s.M s'.M c.θ c.ψ χS χT p.ω hc.inf hW m X hmX p.f hvac a ha hfr
      (glue Φ) (glue Φ)
    set mf : GinfC s.V → ℂ := fun g => conj (∏ τ, ⟪(w τ : s.M.H τ),
      s.M.rep τ (Formalism.MainNotions.StandardLattice.infMat D.sp.cm.sig s.V.gram (c.θ τ) (g : GA D s.V)) (w τ)⟫_ℂ) with hmf
    have hmint : Integrable mf mR := by
      obtain ⟨hI2, -⟩ := hhaar (fun τ h => conj ⟪(w τ : s.M.H τ), s.M.rep τ h (w τ)⟫_ℂ) (fun τ => by
        simp only [hrep]
        exact (hZ τ).1.norm.mono' (hZ τ).1.1.star (Filter.Eventually.of_forall fun x => (RCLike.norm_conj _).le))
      simpa [hmf, map_prod] using hI2
    set Hf : GinfC s.V → ℝ := fun g => ∏ w, GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift.hgtW s.V a w
      (GlobalTheory.AdelicU.projArch D.sp.cm.sig s.V.gram w (g : GA D s.V)) with hHf
    have hHc : Continuous Hf := continuous_finsetProd _ fun w _ =>
      (_root_.GlobalTheory.Corev.RealHeight.hgtW_cont_pos_le_one D s.V a ha w).1.comp ((GlobalTheory.AdelicU.continuous_projArch _ _ w).comp continuous_subtype_val)
    have hHpos : ∀ g, 0 < Hf g ∧ Hf g ≤ 1 := fun g =>
      ⟨Finset.prod_pos fun w _ => ((_root_.GlobalTheory.Corev.RealHeight.hgtW_cont_pos_le_one D s.V a ha w).2 _).1,
        Finset.prod_le_one₀ (fun w _ => ((_root_.GlobalTheory.Corev.RealHeight.hgtW_cont_pos_le_one D s.V a ha w).2 _).1.le)
          fun w _ => ((_root_.GlobalTheory.Corev.RealHeight.hgtW_cont_pos_le_one D s.V a ha w).2 _).2⟩
    have hzint : Integrable z mR :=
      (hIint.const_mul i0).congr (Filter.Eventually.of_forall fun g => (hz g).symm)
    have htb : D.R.t ≤ s'.V.rank := by
      rw [hs'.rank, Formalism.BasicNotions.Ranks.rankY]; nlinarith
    have hbd : ∀ g, ‖z g‖ ≤ C * Hf g ^ ((s'.V.rank : ℝ) / 2) * ‖mf g‖ := by
      intro g
      change ‖ipTh m X (p.ω ((g : GA D s.V), 1) (ptOf c.ψ c.θ s.M s'.M p.f (glue Φ))) (ptOf c.ψ c.θ s.M s'.M p.f (glue Φ)) *
        mf g‖ ≤ _
      rw [norm_mul]
      exact mul_le_mul_of_nonneg_right (hC g g.2) (norm_nonneg _)
    exact _root_.GlobalTheory.realZeta_integrable_mul_heightPow mR z mf Hf C s'.V.rank D.R.t hzint hmint hHc hHpos htb hbd

end GlobalTheory.RealZetaProof
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ThetaConstMul
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory Matrix ValuativeRel GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.FinPl GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.SymChain

noncomputable section

namespace GlobalTheory.SeeSawFold

variable {D : D7}

theorem theta_add' {ψ : AddChar (AF D.host.F) ℂ} {S T : HSp D} {f g : WO S T → ℂ}
    (hf : IsThetaFunO ψ S T f) (hg : IsThetaFunO ψ S T g) : IsThetaFunO ψ S T (fun w => f w + g w) := {
  quasi γ w := by rw [hf.quasi, hg.quasi]; ring
  level := by
    obtain ⟨U, hU, hUf⟩ := hf.level
    obtain ⟨V, hV, hVg⟩ := hg.level
    refine ⟨U ⊓ V, hU.inter hV, fun u hu h0 => ?_⟩
    have e1 := hUf u hu.1 h0
    have e2 := hVg u hu.2 h0
    funext w
    have a1 := congrFun e1 w
    have a2 := congrFun e2 w
    simp only [heisO] at a1 a2 ⊢
    rw [mul_add, a1, a2]
  cont := hf.cont.add hg.cont
  smooth k L hL hL' w := (hf.smooth k L hL hL' w).add (hg.smooth k L hL hL' w) }

theorem theta_const_mul' {ψ : AddChar (AF D.host.F) ℂ} {S T : HSp D} {f : WO S T → ℂ}
    (a : ℂ) (hf : IsThetaFunO ψ S T f) : IsThetaFunO ψ S T (fun w => a * f w) := {
  quasi γ w := by rw [hf.quasi]; ring
  level := by
    obtain ⟨U, hU, hUf⟩ := hf.level
    refine ⟨U, hU, fun u hu h0 => ?_⟩
    funext w
    have a1 := congrFun (hUf u hu h0) w
    simp only [heisO] at a1 ⊢
    rw [mul_left_comm, a1]
  cont := continuous_const.mul hf.cont
  smooth k L hL hL' w := contDiff_const.mul (hf.smooth k L hL hL' w) }

theorem theta_zero' (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) : IsThetaFunO ψ S T (fun _ => 0) :=
  ⟨fun _ _ => by simp, ⟨⊤, isOpen_univ, fun a _ _ => by funext w; simp [heisO]⟩, continuous_const,
    fun _ _ _ _ _ => contDiff_const⟩

theorem theta_sum' {ψ : AddChar (AF D.host.F) ℂ} {S T : HSp D} {ι : Type*} (s : Finset ι) (F : ι → WO S T → ℂ)
    (hF : ∀ i ∈ s, IsThetaFunO ψ S T (F i)) : IsThetaFunO ψ S T (fun w => ∑ i ∈ s, F i w) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using theta_zero' ψ S T
  | insert i s hi ih =>
    simp only [Finset.sum_insert hi]
    exact theta_add' (hF i (Finset.mem_insert_self i s)) (ih fun j hj => hF j (Finset.mem_insert_of_mem hj))

section Ops

variable (ψ : AddChar (AF D.host.F) ℂ) (A S A' : HSp D)

def opL (a : WO A S →₀ ℂ) (C : WO A S → WO S A' → ℂ) : WO A S → WO S A' → ℂ :=
  fun u v => comb ψ A S a (fun u' => C u' v) u

def opR (b : WO S A' →₀ ℂ) (C : WO A S → WO S A' → ℂ) : WO A S → WO S A' → ℂ :=
  fun u v => comb ψ S A' b (C u) v

theorem biComb_eq (a : WO A S →₀ ℂ) (b : WO S A' →₀ ℂ) (C : WO A S → WO S A' → ℂ) :
    biComb ψ A S A' a b C = opL ψ A S A' a (opR ψ A S A' b C) := rfl

theorem opL_opR (a : WO A S →₀ ℂ) (b : WO S A' →₀ ℂ) (C : WO A S → WO S A' → ℂ) :
    opL ψ A S A' a (opR ψ A S A' b C) = opR ψ A S A' b (opL ψ A S A' a C) := by
  funext u v
  simp only [opL, opR, comb, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, heisO, Finset.mul_sum]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring

theorem foldL_opR (l : List ((WO A S →₀ ℂ) × (WO S A' →₀ ℂ))) (b : WO S A' →₀ ℂ) (C : WO A S → WO S A' → ℂ) :
    l.foldr (fun p C => opL ψ A S A' p.1 C) (opR ψ A S A' b C) =
      opR ψ A S A' b (l.foldr (fun p C => opL ψ A S A' p.1 C) C) := by
  induction l with
  | nil => rfl
  | cons p l ih => simp only [List.foldr_cons, ih, opL_opR]

theorem foldL_foldR (l : List ((WO A S →₀ ℂ) × (WO S A' →₀ ℂ))) (Y : WO A S → WO S A' → ℂ) :
    l.foldr (fun p C => opL ψ A S A' p.1 C) (l.foldr (fun p C => opR ψ A S A' p.2 C) Y) =
      l.foldr (fun p C => biComb ψ A S A' p.1 p.2 C) Y := by
  induction l with
  | nil => rfl
  | cons p l ih => simp only [List.foldr_cons, foldL_opR, ih, biComb_eq]

theorem foldR_apply (l : List ((WO A S →₀ ℂ) × (WO S A' →₀ ℂ))) (Y : WO A S → WO S A' → ℂ) (u : WO A S) :
    l.foldr (fun p C => opR ψ A S A' p.2 C) Y u = l.foldr (fun p f => comb ψ S A' p.2 f) (Y u) := by
  induction l with
  | nil => rfl
  | cons p l ih => simp only [List.foldr_cons, ← ih]; rfl

theorem foldL_apply (l : List ((WO A S →₀ ℂ) × (WO S A' →₀ ℂ))) (C : WO A S → WO S A' → ℂ) (u : WO A S)
    (v : WO S A') :
    l.foldr (fun p C => opL ψ A S A' p.1 C) C u v = l.foldr (fun p f => comb ψ A S p.1 f) (fun u' => C u' v) u := by
  induction l generalizing u with
  | nil => rfl
  | cons p l ih =>
    simp only [List.foldr_cons]
    show comb ψ A S p.1 (fun u' => l.foldr (fun p C => opL ψ A S A' p.1 C) C u' v) u = _
    congr 1
    funext u'
    rw [ih]

theorem theta_opR (b : WO S A' →₀ ℂ) (C : WO A S → WO S A' → ℂ) (hC : ∀ v, IsThetaFunO ψ A S (fun u => C u v))
    (v : WO S A') : IsThetaFunO ψ A S (fun u => opR ψ A S A' b C u v) := by
  simp only [opR, comb, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, heisO]
  refine theta_sum' _ _ fun y _ => ?_
  have h := theta_const_mul' (b y * ψ (symplOH S A' v y)) (hC (v + y))
  simpa only [mul_assoc] using h

theorem theta_foldR (l : List ((WO A S →₀ ℂ) × (WO S A' →₀ ℂ))) (Y : WO A S → WO S A' → ℂ)
    (hY : ∀ v, IsThetaFunO ψ A S (fun u => Y u v)) (v : WO S A') :
    IsThetaFunO ψ A S (fun u => l.foldr (fun p C => opR ψ A S A' p.2 C) Y u v) := by
  induction l generalizing v with
  | nil => exact hY v
  | cons p l ih => exact theta_opR ψ A S A' p.2 _ ih v

end Ops

end GlobalTheory.SeeSawFold


open GlobalTheory.SeeSawFold in
theorem GlobalTheory.SeeSaw.biComb_eq_foldr : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (A S A' : HSp D) (c : WO A S →₀ ℂ)
    (c' : WO S A' →₀ ℂ) (l : List ((WO A S →₀ ℂ) × (WO S A' →₀ ℂ))),
    (∀ f, IsThetaFunO ψ A S f → comb ψ A S c f = l.foldr (fun p f' => comb ψ A S p.1 f') f) →
    (∀ f, IsThetaFunO ψ S A' f → comb ψ S A' c' f = l.foldr (fun p f' => comb ψ S A' p.2 f') f) →
    ∀ Y : WO A S → WO S A' → ℂ, (∀ v, IsThetaFunO ψ A S (fun u => Y u v)) → (∀ u, IsThetaFunO ψ S A' (Y u)) →
      biComb ψ A S A' c c' Y = l.foldr (fun p C => biComb ψ A S A' p.1 p.2 C) Y := by
  intro D ψ A S A' c c' l hc hc' Y hYv hYu
  have hR : opR ψ A S A' c' Y = l.foldr (fun p C => opR ψ A S A' p.2 C) Y := by
    funext u v
    show comb ψ S A' c' (Y u) v = _
    rw [hc' _ (hYu u), foldR_apply]
  rw [← foldL_foldR, biComb_eq, hR]
  funext u v
  rw [foldL_apply]
  exact congrFun (hc _ (theta_foldR ψ A S A' l Y hYv v)) u

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ThetaContractionIsLocalModelSecondVariable
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory Matrix ValuativeRel GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.LocMod
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section
open scoped Topology GlobalTheory.MixModel

namespace GlobalTheory.ContrModR

section SlopeTestRemainingChoices
variable {D : D7} {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  (p : Place D k)

theorem incA_mul_ι (b : D.host.E) (x : k) : incA D b * p.ι x = p.ι (p.pr b * x) := by
  have hm : ∀ x y, p.ι (x * y) = p.ι x * p.ι y := fun x y => by
    conv_lhs => rw [← p.π_ι x, ← p.π_ι y, ← RingHom.map_mul, p.ι_π, ← mul_assoc, Witness.e_ι]
  rw [hm]
  change _ = p.ι (p.π (incA D b)) * p.ι x
  rw [p.ι_π, mul_assoc, mul_left_comm, Witness.e_ι]

theorem map_rat_mul_ι {a b c : Type} [Fintype b] (N : Matrix a b D.host.E) (M : Matrix b c k) :
    N.map (incA D) * M.map p.ι = (N.map p.pr * M).map p.ι := by
  ext i j
  set_option synthInstance.maxHeartbeats 100000 in
    simp [Matrix.mul_apply, incA_mul_ι, map_sum]

theorem map_pr_eq {a b : Type} (M : Matrix a b D.host.E) : M.map p.pr = M.map (Witness.prH p) := rfl

variable {n n' : Type} [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n']

theorem core_β {ρ : ℕ} (B : BesLev D ρ) {s : k} (FA : Frame k B.A.rank n') (F₀ : Frame k B.V₀.rank (n' ⊕ Unit))
    (h : p.IsCoreFrame B s FA F₀) : F₀.β * fromRows (1 : Matrix n' n' k) (0 : Matrix Unit n' k) = B.o.iA.map p.pr * FA.β := by
  ext r a
  rw [← h.1 r a]
  simp [Matrix.mul_apply, Fintype.sum_sum_type, Matrix.one_apply]

theorem core_qA {ρ : ℕ} (B : BesLev D ρ) {s : k} (FA : Frame k B.A.rank n') (F₀ : Frame k B.V₀.rank (n' ⊕ Unit))
    (h : p.IsCoreFrame B s FA F₀) :
    FA.γ * B.o.qA.map p.pr * F₀.β = fromCols (1 : Matrix n' n' k) (0 : Matrix n' Unit k) := by
  have hA : FA.γ * B.o.qA.map p.pr * (B.o.iA.map p.pr * FA.β) = 1 := by
    rw [map_pr_eq, map_pr_eq, Matrix.mul_assoc, ← Matrix.mul_assoc (B.o.qA.map _), ← Matrix.map_mul, B.o.qA_iA,
      Matrix.map_one _ (map_zero _) (map_one _), Matrix.one_mul, FA.γβ]
  have hB : FA.γ * B.o.qA.map p.pr * B.o.iB.map p.pr = 0 := by
    rw [map_pr_eq, map_pr_eq, Matrix.mul_assoc, ← Matrix.map_mul, B.o.qA_iB, Matrix.map_zero _ (map_zero _),
      Matrix.mul_zero]
  have hc : ∀ r, F₀.β r (Sum.inr ()) = s * ((B.o.iB.map p.pr) *ᵥ (fun c => p.pr (B.ζ c))) r := by
    intro r
    rw [h.2 r, vecB, map_pr_eq]
    congr 1
    exact (RingHom.map_mulVec (Witness.prH p) B.o.iB B.ζ r)
  have hv : (FA.γ * B.o.qA.map p.pr) *ᵥ ((B.o.iB.map p.pr) *ᵥ (fun c => p.pr (B.ζ c))) = 0 := by
    rw [Matrix.mulVec_mulVec, hB, Matrix.zero_mulVec]
  generalize (B.o.iB.map p.pr) *ᵥ (fun c => p.pr (B.ζ c)) = v at hc hv
  generalize FA.γ * B.o.qA.map p.pr = X at hA hv ⊢
  ext i (a | u)
  · have := congrFun (congrFun hA i) a
    rw [Matrix.mul_apply] at this
    rw [Matrix.mul_apply, fromCols_apply_inl, ← this]
    simp only [h.1]
  · rw [Matrix.mul_apply, fromCols_apply_inr, Matrix.zero_apply]
    simp only [hc, mul_left_comm _ s, ← Finset.mul_sum]
    have h2 := congrFun hv i
    simp only [Matrix.mulVec, dotProduct, Pi.zero_apply] at h2
    rw [h2, mul_zero]

end SlopeTestRemainingChoices

section Up
variable {D : D7} {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  (p : Place D k)
variable {n n'' : Type} [Fintype n] [DecidableEq n] [Fintype n''] [DecidableEq n'']

theorem up_fromRows {σ : ℕ} (B' : BesLev D σ) {s : k} (S : HSp D) (FA' : Frame k B'.A.rank n'')
    (F₀' : Frame k B'.V₀.rank (n'' ⊕ Unit)) (FS : Frame k S.rank n) (h : p.IsCoreFrame B' s FA' F₀')
    (x : Matrix n'' n k) :
    p.up FS F₀' (fromRows x (0 : Matrix Unit n k)) = (B'.o.resT S).symm (p.up FS FA' x, 0) := by
  have hx : fromRows x (0 : Matrix Unit n k) = fromRows (1 : Matrix n'' n'' k) (0 : Matrix Unit n'' k) * x := by
    rw [Matrix.fromRows_mul, Matrix.one_mul, Matrix.zero_mul]
  rw [OrthDec.resT_symm_apply, Matrix.mul_zero, add_zero, Place.up, Place.up, OrthDec.jA, rat, map_rat_mul_ι, hx,
    ← Matrix.mul_assoc, core_β p B' FA' F₀' h]
  simp only [Matrix.mul_assoc]

theorem pA_up {σ : ℕ} (B' : BesLev D σ) {s : k} (S : HSp D) (FA' : Frame k B'.A.rank n'')
    (F₀' : Frame k B'.V₀.rank (n'' ⊕ Unit)) (FS : Frame k S.rank n) (h : p.IsCoreFrame B' s FA' F₀')
    (t : Matrix (n'' ⊕ Unit) n k) : B'.o.pA ⬝ p.up FS F₀' t = p.up FS FA' t.toRows₁ := by
  have hq : B'.o.qA.map p.pr * F₀'.β = fromCols FA'.β (0 : Matrix (Fin B'.A.rank) Unit k) := by
    have := congrArg (FA'.β * ·) (core_qA p B' FA' F₀' h)
    simp only [← Matrix.mul_assoc, FA'.βγ, Matrix.one_mul] at this
    rw [this, Matrix.mul_fromCols, Matrix.mul_one, Matrix.mul_zero]
  rw [Place.up, Place.up, OrthDec.pA, rat, map_rat_mul_ι, ← Matrix.mul_assoc, ← Matrix.mul_assoc, hq]
  conv_lhs => rw [← fromRows_toRows t]
  rw [fromCols_mul_fromRows, Matrix.zero_mul, add_zero]

end Up

section Pass
variable {D : D7} (ψ : AddChar (AF D.host.F) ℂ)

theorem symplOH_zero_r {S T : HSp D} (x : WO S T) : symplOH S T x 0 = 0 := by
  have : hO S T x 0 = 0 := by simp [hO]
  simp [symplOH, symplO, this]

theorem heis_pass {V A L : HSp D} (o : OrthDec V A L) (S : HSp D) (f : WO S V → ℂ) (b v : WO S A) (z : WO S L) :
    heisO ψ S V ((o.resT S).symm (b, 0)) f ((o.resT S).symm (v, z)) =
      ψ (symplOH S A v b) * f ((o.resT S).symm (v + b, z)) := by
  simp only [heisO]
  rw [o.symplOH_resT, AddEquiv.apply_symm_apply, AddEquiv.apply_symm_apply, symplOH_zero_r, add_zero,
    ← map_add, Prod.mk_add_mk, add_zero]

end Pass

end GlobalTheory.ContrModR

namespace GlobalTheory.ContrModR

theorem contr_isModel : ∀ (D : D7) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (p : Place D k) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ (ρ σ : ℕ) (B : BesLev D ρ) (B' : BesLev D σ) (l : Link B B'.L B'.ζ) (S : HSp D) (vL : VolM D B'.L.rank S.rank) (s : k), s ≠ 0 → ∀ (n n'' : Type) [Fintype n] [DecidableEq n] [Fintype n''] [DecidableEq n''] (FS : Frame k S.rank n) (FA' : Frame k B'.A.rank n'') (F₀' : Frame k B'.V₀.rank (n'' ⊕ Unit)), p.IsCoreFrame B' s FA' F₀' → ∀ (T₂ : SB (Matrix (n'' ⊕ Unit) n k) →ₗ[ℂ] (WO S B'.V₀ → ℂ)), p.IsModel ψ FS F₀' T₂ → ∀ (φ₀ : SB (n → k)) (Ξ₁ : WO B.V₀ S → ℂ), IsThetaFunO ψ B.V₀ S Ξ₁ → ∀ (u : WO B.A S) (T : SB (Matrix n'' n k) →ₗ[ℂ] (WO S B'.A → ℂ)), (∀ Ξ₂ v, T Ξ₂ v = GlobalTheory.Unf.contr l S vL Ξ₁ (T₂ (GlobalTheory.ContractionLocal.rowTens φ₀ Ξ₂)) u v) → p.IsModel ψ FS FA' T := by
  intro D k _ _ _ _ p ψ hψ ρ σ B B' l S vL s hs n n'' _ _ _ _ FS FA' F₀' hcore T₂ hT₂ φ₀ Ξ₁ hΞ₁ u T hT

  have pass : ∀ (b : WO S B'.A) (Φ Φ' : SB (Matrix n'' n k)),
      T₂ (GlobalTheory.ContractionLocal.rowTens φ₀ Φ') =
        heisO ψ S B'.V₀ ((B'.o.resT S).symm (b, 0)) (T₂ (GlobalTheory.ContractionLocal.rowTens φ₀ Φ)) →
      T Φ' = heisO ψ S B'.A b (T Φ) := by
    intro b Φ Φ' e
    funext v
    rw [hT Φ' v, e]
    change _ = ψ (symplOH S B'.A v b) * T Φ (v + b)
    rw [hT Φ (v + b)]
    unfold GlobalTheory.Unf.contr
    rw [← integral_const_mul]
    refine congrArg (fun f : WO S B'.L → ℂ => ∫ w in vL.𝓕, f w ∂vL.μ) (funext fun w => ?_)
    rw [heis_pass]
    ring
  refine ⟨fun Φ => ?_, fun x Φ Φ' e => ?_, fun y hy Φ Φ' e => ?_⟩
  ·
    haveI : ∀ m n, BorelSpace (Mx D m n) := fun _ _ => ⟨rfl⟩
    haveI : IsFiniteMeasure (vL.μ.restrict vL.𝓕) :=
      ⟨by rw [Measure.restrict_apply_univ, vL.covol.2.2]; exact ENNReal.one_lt_top⟩
    obtain ⟨C₁, hC₁⟩ := GlobalTheory.IsoMean.isThetaFunO_bounded _ _ ψ hψ Ξ₁ hΞ₁
    have hc : Continuous fun w => Ξ₁ ((B.o.resS S).symm (u, l.κ S w)) :=
      hΞ₁.cont.comp ((OrthDec.continuous_resS_symm _ _).comp
        (Continuous.prodMk continuous_const (GlobalTheory.ContractionLocal.continuous_kappa l S)))
    have hint : Integrable (fun w => Ξ₁ ((B.o.resS S).symm (u, l.κ S w))) (vL.μ.restrict vL.𝓕) :=
      (integrable_const C₁).mono' hc.aestronglyMeasurable (ae_of_all _ fun w => hC₁ _)
    have h := GlobalTheory.SuperposT.superpos_target D ψ hψ B'.V₀ B'.A B'.L S B'.o (T₂ (GlobalTheory.ContractionLocal.rowTens φ₀ Φ))
      (hT₂.theta _) (WO S B'.L) (vL.μ.restrict vL.𝓕) id (fun w => Ξ₁ ((B.o.resS S).symm (u, l.κ S w)))
      measurable_id hint
    convert h using 1
    funext v
    rw [hT]
    unfold GlobalTheory.Unf.contr
    refine congrArg (fun f : WO S B'.L → ℂ => ∫ w in vL.𝓕, f w ∂vL.μ) (funext fun w => ?_)
    simp only [id]
    ring
  ·
    refine pass (p.up FS FA' x) Φ Φ' ?_
    rw [← up_fromRows p B' S FA' F₀' FS hcore x]
    refine hT₂.trans _ _ _ fun t => ?_
    have h1 : (t + fromRows x (0 : Matrix Unit n k)).toRows₁ = t.toRows₁ + x := by
      ext i j; simp [Matrix.toRows₁]
    have h2 : (t + fromRows x (0 : Matrix Unit n k)) (Sum.inr ()) = t (Sum.inr ()) := by
      funext j; simp
    simp only [GlobalTheory.ContractionLocal.rowTens_apply, e, h1, h2]
  ·
    refine pass y Φ Φ' (hT₂.modul _ ?_ _ _ fun t => ?_)
    · intro i j
      rw [OrthDec.resT_symm_apply, Matrix.mul_zero, add_zero, Matrix.mul_apply, Finset.mul_sum]
      exact Finset.sum_congr rfl fun c _ => by rw [mul_left_comm, hy c j]
    · simp only [GlobalTheory.ContractionLocal.rowTens_apply, e]
      rw [B'.o.symplO_resT S (p.up FS F₀' t), AddEquiv.apply_symm_apply]
      rw [OrthDec.resT_apply B'.o S (p.up FS F₀' t)]
      simp only
      rw [pA_up p B' S FA' F₀' FS hcore t]
      have : symplO S B'.L (B'.o.pB ⬝ p.up FS F₀' t) 0 = 0 := by
        have h0 : hO S B'.L (B'.o.pB ⬝ p.up FS F₀' t) 0 = 0 := by simp [hO]
        simp [symplO, h0]
      simp only [this, add_zero]
      ring

end GlobalTheory.ContrModR

end
end

