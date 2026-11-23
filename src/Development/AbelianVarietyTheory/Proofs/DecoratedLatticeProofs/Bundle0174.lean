module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0013
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0009
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0151
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0004
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0015
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0140
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsUniqueIsConjAt
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0303
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0061
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.GaussianBinomialClosedForm
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0287
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0085
public import Development.AbelianVarietyTheory.Definitions.Foundations.T2SpaceAdeleRing
public import Development.AbelianVarietyTheory.Definitions.Foundations.NotIsSplitOfIsInertAt
public import Development.AbelianVarietyTheory.Definitions.Foundations.GLintEqKOAndPrincEqKOne
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0014
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.PairwiseDisjointCell
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0131
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0014
public import Development.AbelianVarietyTheory.PublishedTheorems.DiscreteSeriesUnitary₂.Bundle0001
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.Bundle0004
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0150
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsThetaFam
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0018
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0005

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SeesawFubiniTwoLiftsModerateGrowthKernels
section
open scoped ComplexConjugate Matrix NNReal
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.Cusp GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (FinPl RealMat Lat IsFockVec IsSphOff HidaSetting volQ)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (ip delta swSec sZero IsKFinVec ThetaClause SectionClause CoefClause)
open GlobalTheory.Mem.Th (CptF)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Core.Rk.IP

noncomputable section

namespace GlobalTheory.Core.Rk.Seesaw

variable {D : D7}

theorem out_eq_sec {V : HSp D} {X : Type*} {φ : GA D V → X} (h : ∀ γ ∈ GQ V, ∀ g, φ (γ * g) = φ g) (q : AutQ V) :
    φ q.out = φ (sec (GQ V) q) :=
  LeftInv.eq_of_mk_eq (Γ := GQ V) h ((Quotient.out_eq q).trans (mk_sec q).symm)

theorem measurable_out {V : HSp D} {φ : GA D V → ℂ} (h : ∀ γ ∈ GQ V, ∀ g, φ (γ * g) = φ g) (hc : Continuous φ) :
    Measurable fun q : AutQ V => φ q.out := by
  have e : (fun q : AutQ V => φ q.out) = φ ∘ sec (GQ V) := funext (out_eq_sec h)
  rw [e]
  exact hc.measurable.comp measurableEmbedding_sec.measurable

theorem measurable_kernel_out {A B : HSp D} {K : GA D A → GA D B → ℂ} (hc : Continuous (Function.uncurry K))
    (hl : ∀ γ ∈ GQ A, ∀ g h, K (γ * g) h = K g h) (hr : ∀ g, ∀ γ ∈ GQ B, ∀ h, K g (γ * h) = K g h) :
    Measurable (Function.uncurry fun (q : AutQ A) (y : AutQ B) => K q.out y.out) := by
  have e : (Function.uncurry fun (q : AutQ A) (y : AutQ B) => K q.out y.out) =
      Function.uncurry K ∘ fun p => (sec (GQ A) p.1, sec (GQ B) p.2) := by
    funext p
    show K p.1.out p.2.out = K (sec (GQ A) p.1) (sec (GQ B) p.2)
    rw [out_eq_sec (φ := fun g => K g p.2.out) (fun γ hγ g => hl γ hγ g _) p.1, out_eq_sec (hr _) p.2]
  rw [e]
  exact hc.measurable.comp ((measurableEmbedding_sec.measurable.comp measurable_fst).prodMk
    (measurableEmbedding_sec.measurable.comp measurable_snd))

theorem integrable_lift_integrand {A B : HSp D} (m : Measure (GA D A)) (hm : m.IsHaarMeasure)
    {K : GA D A → GA D B → ℂ} (hc : Continuous (Function.uncurry K)) (hl : ∀ γ ∈ GQ A, ∀ g h, K (γ * g) h = K g h)
    (hg : ∀ h, GlobalTheory.Grow.ModGrowth A fun g => K g h) {u : GA D A → ℂ} (hu : GlobalTheory.Grow.RapidDec A u) (h : GA D B) :
    Integrable (descend (GQ A) fun g => K g h * u g) (autMeasure A m) := by
  obtain ⟨C, a, hC⟩ := hg h
  have hb := GlobalTheory.Grow.norm_le_quotHeight_pow (f := fun g => K g h) (fun γ hγ g => hl γ hγ g h) hC
  have hKc : Continuous fun g => K g h := hc.comp (continuous_id.prodMk continuous_const)
  have hmeas : Measurable (descend (GQ A) fun g => K g h * u g) :=
    measurable_out (φ := fun g => K g h * u g) (fun γ hγ g => by simp only [hl γ hγ, hu.1 γ hγ]) (hKc.mul hu.2.1)
  refine ((_root_.GlobalTheory.Core.Rk.IP.integrable_quotHeight_pow_mul_norm_of_rapidDec D A m hm u hu a).const_mul (C * 2 ^ a)).mono' hmeas.aestronglyMeasurable
    (ae_of_all _ fun q => ?_)
  show ‖K q.out h * u q.out‖ ≤ C * 2 ^ a * (GlobalTheory.Grow.quotHeight A q.out ^ a * ‖u q.out‖)
  rw [norm_mul, ← mul_assoc]
  exact mul_le_mul_of_nonneg_right (hb _) (norm_nonneg _)

theorem lintegral_slice_le {A B : HSp D} (mH : Measure (GA D B)) {K : GA D A → GA D B → ℂ}
    (hl : ∀ γ ∈ GQ A, ∀ g h, K (γ * g) h = K g h) (hL2 : ∀ g, MemL2Quotient (GQ B) mH (K g))
    (hP : GlobalTheory.Grow.ModGrowth A fun g => petersson B mH (K g) (K g)) :
    ∃ (c : ℝ) (a : ℕ), 0 ≤ c ∧ ∀ g, ∫⁻ y, ‖K g y.out‖ₑ ^ 2 ∂autMeasure B mH ≤
      ENNReal.ofReal (c * GlobalTheory.Grow.quotHeight A g ^ a) := by
  obtain ⟨C, a, hC⟩ := hP
  have hinv : ∀ γ ∈ GQ A, ∀ g, petersson B mH (K (γ * g)) (K (γ * g)) = petersson B mH (K g) (K g) :=
    fun γ hγ g => by rw [show K (γ * g) = K g from funext (hl γ hγ g)]
  refine ⟨C * 2 ^ a, a, mul_nonneg (GlobalTheory.Grow.nonneg_of_growth hC) (by positivity), fun g => ?_⟩
  have hb := GlobalTheory.Grow.norm_le_quotHeight_pow hinv hC g
  have hf := (hL2 g).2
  have hf2 : Integrable (fun y : AutQ B => ‖K g y.out‖ ^ 2) (autMeasure B mH) :=
    (memLp_two_iff_integrable_sq_norm hf.aestronglyMeasurable).1 hf
  have e1 : ∫⁻ y, ‖K g y.out‖ₑ ^ 2 ∂autMeasure B mH = ENNReal.ofReal (∫ y, ‖K g y.out‖ ^ 2 ∂autMeasure B mH) := by
    rw [ofReal_integral_eq_lintegral_ofReal hf2 (ae_of_all _ fun _ => by positivity)]
    refine lintegral_congr fun y => ?_
    rw [ENNReal.ofReal_pow (norm_nonneg _), ofReal_norm]
  have e2 : petersson B mH (K g) (K g) = ((∫ y, ‖K g y.out‖ ^ 2 ∂autMeasure B mH : ℝ) : ℂ) := by
    rw [← integral_complex_ofReal]
    show ∫ y, descend (GQ B) (K g) y * conj (descend (GQ B) (K g) y) ∂autMeasure B mH = _
    refine integral_congr_ae (ae_of_all _ fun y => ?_)
    show K g y.out * conj (K g y.out) = _
    rw [Complex.mul_conj, Complex.normSq_eq_norm_sq]
  have e3 : ‖petersson B mH (K g) (K g)‖ = ∫ y, ‖K g y.out‖ ^ 2 ∂autMeasure B mH := by
    rw [e2, Complex.norm_real, Real.norm_of_nonneg (integral_nonneg fun _ => by positivity)]
  rw [e1]
  exact ENNReal.ofReal_le_ofReal (e3 ▸ hb)

theorem weight_data {A : HSp D} (m : Measure (GA D A)) (hm : m.IsHaarMeasure) {u : GA D A → ℂ}
    (hu : GlobalTheory.Grow.RapidDec A u) {c : ℝ} (hc : 0 ≤ c) (a : ℕ) :
    (∀ q : AutQ A, ENNReal.ofReal (c * GlobalTheory.Grow.quotHeight A q.out ^ a) ≤
      ENNReal.ofReal (1 + c * GlobalTheory.Grow.quotHeight A q.out ^ a) ^ 2) ∧
    ∫⁻ q, ENNReal.ofReal (1 + c * GlobalTheory.Grow.quotHeight A q.out ^ a) * ‖u q.out‖ₑ ∂autMeasure A m ≠ ⊤ := by
  have ht : ∀ q : AutQ A, 0 ≤ c * GlobalTheory.Grow.quotHeight A q.out ^ a :=
    fun q => mul_nonneg hc (pow_nonneg (GlobalTheory.Grow.quotHeight_pos A _).le _)
  refine ⟨fun q => ?_, ?_⟩
  · rw [← ENNReal.ofReal_pow (by linarith [ht q])]
    exact ENNReal.ofReal_le_ofReal (by nlinarith [ht q])
  · have hint : Integrable (fun q : AutQ A => (1 + c * GlobalTheory.Grow.quotHeight A q.out ^ a) * ‖u q.out‖)
        (autMeasure A m) := by
      refine ((_root_.GlobalTheory.Core.Rk.IP.integrable_quotHeight_pow_mul_norm_of_rapidDec D A m hm u hu 0).add ((_root_.GlobalTheory.Core.Rk.IP.integrable_quotHeight_pow_mul_norm_of_rapidDec D A m hm u hu a).const_mul c)).congr
        (ae_of_all _ fun q => ?_)
      simp only [Pi.add_apply, pow_zero, one_mul]
      ring
    refine ne_of_lt (lt_of_le_of_lt (le_of_eq ?_) hint.lintegral_lt_top)
    refine lintegral_congr fun q => ?_
    rw [← ofReal_norm, ← ENNReal.ofReal_mul (by linarith [ht q])]

theorem seesaw_fubini : ∀ (D : D7) (A B : HSp D) (m : Measure (GA D A)) (mH : Measure (GA D B)), m.IsHaarMeasure → mH.IsHaarMeasure → ∀ K₁ K₂ : GA D A → GA D B → ℂ, (∀ K ∈ ({K₁, K₂} : Set (GA D A → GA D B → ℂ)), Continuous (Function.uncurry K) ∧ (∀ γ ∈ GQ A, ∀ g h, K (γ * g) h = K g h) ∧ (∀ g, MemL2Quotient (GQ B) mH (K g)) ∧ (GlobalTheory.Grow.ModGrowth A fun g => petersson B mH (K g) (K g)) ∧ ∀ h, GlobalTheory.Grow.ModGrowth A fun g => K g h) → ∀ u₁ u₂ : GA D A → ℂ, GlobalTheory.Grow.RapidDec A u₁ → GlobalTheory.Grow.RapidDec A u₂ → let θ₁ : GA D B → ℂ := fun h => ∫ q, GlobalTheory.AutomorphicL2Unitary.descend (GQ A) (fun g => K₁ g h * u₁ g) q ∂autMeasure A m; let θ₂ : GA D B → ℂ := fun h => ∫ q, GlobalTheory.AutomorphicL2Unitary.descend (GQ A) (fun g => K₂ g h * u₂ g) q ∂autMeasure A m; (∀ h, Integrable (GlobalTheory.AutomorphicL2Unitary.descend (GQ A) fun g => K₁ g h * u₁ g) (autMeasure A m)) ∧ (∀ h, Integrable (GlobalTheory.AutomorphicL2Unitary.descend (GQ A) fun g => K₂ g h * u₂ g) (autMeasure A m)) ∧ MemL2Quotient (GQ B) mH θ₁ ∧ MemL2Quotient (GQ B) mH θ₂ ∧ petersson B mH θ₁ θ₂ = ∫ q : AutQ A × AutQ A, petersson B mH (K₁ q.1.out) (K₂ q.2.out) * u₁ q.1.out * conj (u₂ q.2.out) ∂(autMeasure A m).prod (autMeasure A m) := by
  intro D A B m mH hm hmH K₁ K₂ hK u₁ u₂ hu₁ hu₂ θ₁ θ₂
  obtain ⟨hc₁, hl₁, hL₁, hP₁, hg₁⟩ := hK K₁ (Set.mem_insert _ _)
  obtain ⟨hc₂, hl₂, hL₂, hP₂, hg₂⟩ := hK K₂ (Set.mem_insert_of_mem _ rfl)
  have hi₁ := integrable_lift_integrand m hm hc₁ hl₁ hg₁ hu₁
  have hi₂ := integrable_lift_integrand m hm hc₂ hl₂ hg₂ hu₂
  have hr₁ : ∀ g, ∀ γ ∈ GQ B, ∀ h, K₁ g (γ * h) = K₁ g h := fun g => (hL₁ g).1
  have hr₂ : ∀ g, ∀ γ ∈ GQ B, ∀ h, K₂ g (γ * h) = K₂ g h := fun g => (hL₂ g).1
  obtain ⟨c₁, a₁, hc₁0, hs₁⟩ := lintegral_slice_le mH hl₁ hL₁ hP₁
  obtain ⟨c₂, a₂, hc₂0, hs₂⟩ := lintegral_slice_le mH hl₂ hL₂ hP₂
  obtain ⟨hw₁, hf₁⟩ := weight_data m hm hu₁ hc₁0 a₁
  obtain ⟨hw₂, hf₂⟩ := weight_data m hm hu₂ hc₂0 a₂
  have := hm
  have := hmH
  have key := _root_.GlobalTheory.AbsFubini.abstract_fubini_two_lifts (autMeasure A m) (autMeasure A m) (autMeasure B mH)
    (fun q y => K₁ q.out y.out) (fun q y => K₂ q.out y.out) (fun q => u₁ q.out) (fun q => u₂ q.out)
    (measurable_kernel_out hc₁ hl₁ hr₁) (measurable_kernel_out hc₂ hl₂ hr₂)
    (measurable_out hu₁.1 hu₁.2.1) (measurable_out hu₂.1 hu₂.2.1) _ _
    (fun q => (hs₁ q.out).trans (hw₁ q)) (fun q => (hs₂ q.out).trans (hw₂ q)) hf₁ hf₂
    (fun y => hi₁ y.out) (fun y => hi₂ y.out)
  have inv₁ : ∀ γ ∈ GQ B, ∀ h, θ₁ (γ * h) = θ₁ h := fun γ hγ h => by
    have e : (fun g => K₁ g (γ * h) * u₁ g) = fun g => K₁ g h * u₁ g := funext fun g => by rw [hr₁ g γ hγ h]
    show ∫ q, descend (GQ A) (fun g => K₁ g (γ * h) * u₁ g) q ∂autMeasure A m = _
    rw [e]
  have inv₂ : ∀ γ ∈ GQ B, ∀ h, θ₂ (γ * h) = θ₂ h := fun γ hγ h => by
    have e : (fun g => K₂ g (γ * h) * u₂ g) = fun g => K₂ g h * u₂ g := funext fun g => by rw [hr₂ g γ hγ h]
    show ∫ q, descend (GQ A) (fun g => K₂ g (γ * h) * u₂ g) q ∂autMeasure A m = _
    rw [e]
  exact ⟨hi₁, hi₂, ⟨inv₁, key.1⟩, ⟨inv₂, key.2.1⟩, key.2.2⟩

end GlobalTheory.Core.Rk.Seesaw

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SpanRhoTEqTop
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.IndefR.Datum
open scoped TensorProduct

attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option synthInstance.maxHeartbeats 400000

namespace GlobalTheory.InertFrameLoc

open Formalism.UG (IsInertAt)

variable {D : D7} {v : HeightOneSpectrum (𝓞 D.host.F)} {w : HeightOneSpectrum (𝓞 D.host.E)}

def secW (hw : IsInertAt D.host.F D.host.E v w) (h : w.under (𝓞 D.host.F) = v) :
    w.adicCompletion D.host.E →+ AE D :=
  (GlobalTheory.EmbChart.tensAt D.host.E v).toAddMonoidHom.comp
    (GlobalTheory.LFun.InertChart.complEquiv hw h).symm.toRingHom.toAddMonoidHom

def uPt (hw : IsInertAt D.host.F D.host.E v w) (h : w.under (𝓞 D.host.F) = v) {S T : HSp D}
    (k : w.adicCompletion D.host.E) (aS : GL (Fin S.rank) (w.adicCompletion D.host.E))
    (aT : GL (Fin T.rank) (w.adicCompletion D.host.E))
    (x : Matrix (Fin T.rank) (Fin S.rank) (w.adicCompletion D.host.E)) : WO S T :=
  (k • (aT.1 * x * (aS⁻¹).1)).map (secW hw h)

def thW (ψ : AddChar (AF D.host.F) ℂ) (hw : IsInertAt D.host.F D.host.E v w) (h : w.under (𝓞 D.host.F) = v)
    (k : w.adicCompletion D.host.E) : AddChar (w.adicCompletion D.host.E) ℂ :=
  ψ.compAddMonoidHom ((Algebra.trace (AF D.host.F) (AE D)).toAddMonoidHom.comp
    ((AddMonoidHom.mulLeft (incA D D.host.xi0)).comp ((secW hw h).comp (AddMonoidHom.mulLeft k))))

variable {hw : IsInertAt D.host.F D.host.E v w} {h : w.under (𝓞 D.host.F) = v} {S T : HSp D}
  {k : w.adicCompletion D.host.E} {aS : GL (Fin S.rank) (w.adicCompletion D.host.E)}
  {aT : GL (Fin T.rank) (w.adicCompletion D.host.E)}

theorem thW_apply (ψ : AddChar (AF D.host.F) ℂ) (z : w.adicCompletion D.host.E) :
    thW ψ hw h k z = ψ (Algebra.trace (AF D.host.F) (AE D) (incA D D.host.xi0 * secW hw h (k * z))) := rfl

theorem uPt_add (x y : Matrix (Fin T.rank) (Fin S.rank) (w.adicCompletion D.host.E)) :
    uPt hw h k aS aT (x + y) = uPt hw h k aS aT x + uPt hw h k aS aT y := by
  ext i j
  simp [uPt, Matrix.mul_add, Matrix.add_mul, smul_add]

theorem uPt_zero : uPt hw h k aS aT (0 : Matrix (Fin T.rank) (Fin S.rank) _) = 0 := by
  ext i j
  simp [uPt]

theorem infPart_tensAt (y : Fv D.host.F v ⊗[D.host.F] D.host.E) :
    infPart D (GlobalTheory.EmbChart.tensAt D.host.E v y) = 0 := by
  induction y using TensorProduct.induction_on with
  | zero => rw [map_zero, map_zero]
  | tmul a x =>
    rw [GlobalTheory.EmbChart.tensAt_tmul, GlobalTheory.EmbChart.atPlace_apply]
    show (fstA D.host.F) (pairA D.host.F 0 (GlobalTheory.AdelicU.singleFin v a)) ⊗ₜ[D.host.F] x = 0
    rw [show (fstA D.host.F) (pairA D.host.F 0 (GlobalTheory.AdelicU.singleFin v a)) = 0 from rfl, TensorProduct.zero_tmul]
  | add x y hx hy => rw [LinearMap.map_add (f := _), RingHom.map_add (f := _), hx, hy, add_zero]

theorem infPart_secW (z : w.adicCompletion D.host.E) : infPart D (secW hw h z) = 0 :=
  infPart_tensAt _

theorem map_infPart_uPt (x : Matrix (Fin T.rank) (Fin S.rank) (w.adicCompletion D.host.E)) :
    (uPt hw h k aS aT x).map (infPart D) = 0 := by
  ext i j
  exact infPart_secW _

section Anti

open Formalism.UG GlobalTheory.Hk3 GlobalTheory.FinWeil

variable {L : Type} [Field L]

theorem antiJ_herm (σ : L →+* L) (n : ℕ) (i j : Fin n) : σ (antiJ L n i j) = antiJ L n j i := by
  simp only [antiJ]
  rw [show j.val + i.val = i.val + j.val from add_comm _ _]
  split_ifs <;> simp

variable [Valued L (WithZero (Multiplicative ℤ))]

theorem antiG_mem (n : ℕ) : GlobalTheory.SphTheta.antiG L n ∈ GLint (Fin n) (intL L) := by
  let A : Matrix (Fin n) (Fin n) (intL L) := fun i j => if i.val + j.val + 1 = n then 1 else 0
  have hA : A.map (intL L).subtype = antiJ L n := by
    ext i j
    show ((if i.val + j.val + 1 = n then 1 else 0 : intL L) : L) = antiJ L n i j
    simp only [antiJ]
    split_ifs <;> simp
  have hinj : Function.Injective fun M : Matrix (Fin n) (Fin n) (intL L) => M.map (intL L).subtype :=
    fun M N e => Matrix.ext fun i j => Subtype.ext (congrFun (congrFun e i) j)
  have hAA : A * A = 1 := hinj (by
    show (A * A).map (intL L).subtype = (1 : Matrix (Fin n) (Fin n) (intL L)).map (intL L).subtype
    rw [Matrix.map_mul, Matrix.map_one _ (map_zero _) (map_one _), hA]
    exact P.fIwasawa_antiJ_mul_antiJ)
  exact ⟨⟨A, A, hAA, hAA⟩, Units.ext hA⟩

end Anti

section Build

variable {D : D7} (ψ : AddChar (AF D.host.F) ℂ) {S T : HSp D} {X : Type} (u : X → WO S T) (f : WO S T → ℂ)

def spanT : Submodule ℂ (WO S T → ℂ) := Submodule.span ℂ (Set.range fun x => heisO ψ S T (u x) f)

variable {ψ u f}

theorem mem_spanT_of {g : Module.End ℂ (WO S T → ℂ)} (hg : ∀ x, g (heisO ψ S T (u x) f) ∈ spanT ψ u f) {m : WO S T → ℂ}
    (hm : m ∈ spanT ψ u f) : g m ∈ spanT ψ u f := by
  have key : spanT ψ u f ≤ (spanT ψ u f).comap g := Submodule.span_le.2 (by
    rintro _ ⟨x, rfl⟩
    exact hg x)
  exact key hm

theorem heis_mem_spanT [Add X] (hu : ∀ x y, u (x + y) = u x + u y) (x : X) {m : WO S T → ℂ} (hm : m ∈ spanT ψ u f) :
    heisO ψ S T (u x) m ∈ spanT ψ u f :=
  mem_spanT_of (g := GlobalTheory.SplitScalar.heisL ψ S T (u x)) (fun y => by
    show heisO ψ S T (u x) (heisO ψ S T (u y) f) ∈ spanT ψ u f
    rw [GlobalTheory.SplitScalar.heisO_heisO, ← hu]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨x + y, rfl⟩)) hm

theorem self_mem_spanT [Zero X] (hu : u 0 = 0) : f ∈ spanT ψ u f :=
  Submodule.subset_span ⟨0, by
    show heisO ψ S T (u 0) f = f
    rw [hu, GlobalTheory.SplitScalar.heisO_zero]⟩


variable (ψ u f) in
def rhoT [Add X] (hu : ∀ x y, u (x + y) = u x + u y) (x : X) : Module.End ℂ (spanT ψ u f) :=
  (GlobalTheory.SplitScalar.heisL ψ S T (u x)).restrict fun _ hm => heis_mem_spanT hu x hm

theorem coe_rhoT [Add X] (hu : ∀ x y, u (x + y) = u x + u y) (x : X) (m : spanT ψ u f) :
    (rhoT ψ u f hu x m : WO S T → ℂ) = heisO ψ S T (u x) m := rfl


variable (ψ u f) in
def omT {G : Type} [Monoid G] (π : G →* Module.End ℂ (WO S T → ℂ))
    (hπ : ∀ g, ∀ m ∈ spanT ψ u f, π g m ∈ spanT ψ u f) : G →* Module.End ℂ (spanT ψ u f) where
  toFun g := (π g).restrict (hπ g)
  map_one' := LinearMap.ext fun m => Subtype.ext (by
    show π 1 m = m
    rw [map_one, Module.End.one_apply])
  map_mul' g g' := LinearMap.ext fun m => Subtype.ext (by
    show π (g * g') m = π g (π g' m)
    rw [map_mul, Module.End.mul_apply])

theorem span_rhoT_eq_top [Add X] (hu : ∀ x y, u (x + y) = u x + u y) (hf : f ∈ spanT ψ u f) :
    Submodule.span ℂ (Set.range fun x => rhoT ψ u f hu x ⟨f, hf⟩) = ⊤ := by
  have e : (Set.range fun x => rhoT ψ u f hu x ⟨f, hf⟩) =
      ((↑) : spanT ψ u f → WO S T → ℂ) ⁻¹' Set.range fun x => heisO ψ S T (u x) f := by
    ext m
    refine ⟨?_, ?_⟩
    · rintro ⟨x, rfl⟩
      exact ⟨x, rfl⟩
    · rintro ⟨x, hx⟩
      exact ⟨x, Subtype.ext hx⟩
  rw [e]
  exact Submodule.span_span_coe_preimage

end Build

end GlobalTheory.InertFrameLoc

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SphericalParameterBoundNonsplitPlaces
section
open scoped ComplexConjugate Matrix NNReal
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.Cusp GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (FinPl RealMat Lat IsFockVec IsSphOff HidaSetting volQ)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (ip delta swSec sZero IsKFinVec ThetaClause SectionClause CoefClause)
open GlobalTheory.Mem.Th (CptF)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Core.Rk.IP

namespace GlobalTheory.Core.Rk.ParamInert

open Formalism.UG (IsUnramInv GU KU qV IsInertAt)

theorem paramBoundOn_nonsplit (hUDI : GlobalTheory.IndefiniteRowSideFullHecke.SphericalSectionVariables.UnramDoublingInert) :
    ∀ D : D7, ParamBoundOn D fun v => ¬ Formalism.MainNotions.SchurIrreducible.IsSplit (E := D.host.E) v := by
  intro D A L hL v hv par c hc hc1 w hw
  obtain ⟨⟨C, hC⟩, V, iV, iM, ρ, x, ℓ, hpar, hℓ, hcv⟩ := hc
  have hp := hpar w hw
  refine ⟨hp.card, ?_⟩
  rcases hp with ⟨hs, -⟩ | ⟨hin, τ, ϖ, e, α, hU, he, hsat, hB⟩
  · exact absurd hs hv
  have hϖ0 : ϖ ≠ 0 := by
    intro h0
    have h4 := hU.2.2.2.1
    rw [h0, map_zero] at h4
    exact WithZero.zero_ne_coe h4
  set ϖu : (w.adicCompletion D.host.E)ˣ := Units.mk0 ϖ hϖ0 with hϖu
  have hU' : IsUnramInv ((ϖu : w.adicCompletion D.host.E)) τ (qV D.host.F v) := hU
  set ρ' : Representation ℂ (GU τ A.rank) V := ρ.comp e.symm.toMonoidHom with hρ'
  have hKinv : ∀ k ∈ KU τ A.rank, ∀ g, ℓ (ρ' (k * g) x) = ℓ (ρ' g x) := by
    intro k hk g
    have hk' : e.symm k ∈ stabLoc D.sp.cm.sig A.gram L v := by
      rw [he.2.2, MulEquiv.apply_symm_apply]; exact hk
    simp only [hρ', MonoidHom.coe_comp, Function.comp_apply, MulEquiv.coe_toMonoidHom, map_mul]
    rw [← map_mul]
    exact hℓ _ hk' _
  have h1 : ℓ x ≠ 0 := by
    intro h0; apply hc1; rw [hcv, map_one]; exact h0
  have hz := (_root_.GlobalTheory.ZonalCoeff.coeff_zero_or_zonal _ ϖu τ (qV D.host.F v) A.rank hU' V ρ' x α hsat ℓ hKinv).2 h1
  have hbd : ∃ C' : ℝ, ∀ g, ‖ℓ (ρ' g x) / ℓ x‖ ≤ C' := by
    refine ⟨C / ‖ℓ x‖, fun g => ?_⟩
    rw [norm_div]
    have : ‖ℓ (ρ' g x)‖ ≤ C := by
      have := hC (e.symm g); rw [hcv] at this; exact this
    exact div_le_div_of_nonneg_right this (norm_nonneg _)
  have htb := _root_.GlobalTheory.ZonalBound.trivialBound_of_bounded hUDI _ ϖu τ (qV D.host.F v) A.rank hU' α _ hz hbd
  intro β hβ
  rw [hB] at hβ
  have hq2 : 2 ≤ qV D.host.F v := hU.2.2.2.2.2.1
  have hle := GlobalTheory.FinZeta.ParamBound.norm_le_of_mem_bcParam hq2 htb β hβ
  have hnorm : Ideal.absNorm w.asIdeal = Ideal.absNorm v.asIdeal ^ 2 :=
    ((GlobalTheory.LFun.exists_isInertChart _ (isCMExt_host D) v).2 w hw hin).2.2.2.1
  have hqv : (qV D.host.F v : ℝ) = (Ideal.absNorm v.asIdeal : ℝ) := rfl
  rw [hnorm, Nat.cast_pow, ← hqv]
  refine hle.trans (Real.rpow_le_rpow_of_exponent_le ?_ ?_)
  · have : (1 : ℝ) ≤ qV D.host.F v := by exact_mod_cast (by omega : 1 ≤ qV D.host.F v)
    nlinarith
  · linarith

end GlobalTheory.Core.Rk.ParamInert
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.StarEqHostConj
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.AutomorphicEvaluation Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.Core.Rk GlobalTheory.Core.Mi
open scoped TensorProduct InnerProductSpace Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.RankOneLine

theorem star_eq_hostConj (D : D7) (x : D.host.E) : star x = D.host.conj x := by
  apply D.host.φ₀.injective
  letI := D.host.isCMField_hostE
  show D.host.φ₀ (IsCMField.complexConj D.host.E x) = _
  rw [NumberField.IsCMField.complexEmbedding_complexConj, Formalism.HC.HostAx.conjE_apply]

def negLine (D : D7) : HSp D :=
  Formalism.BasicNotions.Examples₂.stdSpace Formalism.BasicNotions.Examples₂.star_isIntegral 1 (fun _ => true) 0 1

theorem negLine_gram (D : D7) : ∀ i j, (negLine D).gram i j = -1 := by
  show ∀ i j : Fin 1, (Formalism.BasicNotions.Examples₂.stdSpace (E := D.host.E) Formalism.BasicNotions.Examples₂.star_isIntegral 1
    (fun _ => true) 0 1).gram i j = -1
  intro i j
  rw [Formalism.BasicNotions.Examples₂.stdSpace_gram_apply, Subsingleton.elim i j]
  simp [Formalism.BasicNotions.Examples₂.sgn]

theorem exists_line (D : D7) (X : HidaSetting D) (u : D.what₂.Word) :
    ∃ (L : HSp D) (s : D.host.E), s ≠ 0 ∧ L.rank = 1 ∧ (VS D).hT (X.zu u) (X.zu u) ≠ 0 ∧
      ∀ i j, L.gram i j = star s * s * (VS D).hT (X.zu u) (X.zu u) := by
  obtain ⟨π, -, hπ, -⟩ := D.T_norm u
  have hT0 : (((D.mem u).A.T : ℕ) : D.host.E) ≠ 0 := Nat.cast_ne_zero.2 (D.mem u).A.T_prime.ne_zero
  have hπ0 : ((π : 𝓞 D.host.E) : D.host.E) ≠ 0 := by
    intro h; apply hT0; rw [← hπ, h, zero_mul]
  have hc0 : D.host.conj (π : D.host.E) ≠ 0 := by
    intro h; apply hT0; rw [← hπ, h, mul_zero]
  refine ⟨negLine D, ((π : 𝓞 D.host.E) : D.host.E)⁻¹, inv_ne_zero hπ0, ?_, ?_, fun i j => ?_⟩
  · simp [negLine, Formalism.BasicNotions.Examples₂.stdSpace]
  · rw [X.zu_norm]; exact neg_ne_zero.2 hT0
  · rw [negLine_gram, X.zu_norm, star_inv₀, star_eq_hostConj, ← hπ]
    field_simp <;> ring

end GlobalTheory.RankOneLine
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SumMatApply
section
open scoped ComplexConjugate Matrix NNReal
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.Cusp GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (FinPl RealMat Lat IsFockVec IsSphOff HidaSetting volQ)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (ip delta swSec sZero IsKFinVec)
open GlobalTheory.Mem.Th (CptF)
open GlobalTheory.Core.Rk.IP
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Core.Rk.Exh GlobalTheory.RegSW

noncomputable section

namespace GlobalTheory.Core.Rk.SumBox

variable {D : D7}

def sumMat {B W H : HSp D} (o : OrthDec B W H) (sW : RealMat W) (sH : RealMat H) : RealMat B :=
  fun τ => o.iA.map (tauE D τ) * sW τ * o.qA.map (tauE D τ) + o.iB.map (tauE D τ) * sH τ * o.qB.map (tauE D τ)

def sumLatO {B W H : HSp D} (o : OrthDec B W H) (LW : Lat W) (LH : Lat H) : Lat B :=
  LW.map ((Matrix.mulVecLin o.iA).restrictScalars (𝓞 D.host.E)) ⊔
    LH.map ((Matrix.mulVecLin o.iB).restrictScalars (𝓞 D.host.E))

theorem sumMat_apply {B W H : HSp D} (o : OrthDec B W H) (sW : RealMat W) (sH : RealMat H) (τ : D.what₂.Tau) :
    sumMat o sW sH τ =
      o.iA.map (tauE D τ) * sW τ * o.qA.map (tauE D τ) + o.iB.map (tauE D τ) * sH τ * o.qB.map (tauE D τ) := rfl

theorem mem_sumLatO {B W H : HSp D} (o : OrthDec B W H) (LW : Lat W) (LH : Lat H) (y : Fin B.rank → D.host.E) :
    y ∈ sumLatO o LW LH ↔ ∃ x ∈ LW, ∃ x' ∈ LH, o.iA *ᵥ x + o.iB *ᵥ x' = y := by
  simp only [sumLatO, Submodule.mem_sup, Submodule.mem_map, LinearMap.restrictScalars_apply, Matrix.mulVecLin_apply]
  constructor
  · rintro ⟨_, ⟨x, hx, rfl⟩, _, ⟨x', hx', rfl⟩, rfl⟩
    exact ⟨x, hx, x', hx', rfl⟩
  · rintro ⟨x, hx, x', hx', rfl⟩
    exact ⟨_, ⟨x, hx, rfl⟩, _, ⟨x', hx', rfl⟩, rfl⟩

end GlobalTheory.Core.Rk.SumBox
end
end

