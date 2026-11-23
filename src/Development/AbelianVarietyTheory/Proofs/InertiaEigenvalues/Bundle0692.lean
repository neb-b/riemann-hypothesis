module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.LengthPosOfPosDef
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0021
public import Formalism.LocalToGlobal.IndefiniteReal.LinksStage
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0683
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1083
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0879
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.HasDerivAtZeroAndIsTheta
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0646
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0268
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0142
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.LevelHyperspecialTrivialCharacterSplitsOffPlaces

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ThetaFunctionHeisenbergIrreducibleOrthogonal
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef
open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.IndefR.Links
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RawLift

noncomputable section

namespace GlobalTheory.ThetaIrred

variable {D : D7} {ψ : AddChar (AF D.host.F) ℂ} {S T : HSp D}

theorem integrable_star_mul (hψ : IsStdChar D ψ (-1)) {μ : Measure (WO S T)} {𝓕 : Set (WO S T)} (h1 : μ 𝓕 = 1)
    {f g q : WO S T → ℂ} (hf : IsThetaFunO ψ S T f) (hg : IsThetaFunO ψ S T g) (hq : Continuous q)
    {Cq : ℝ} (hCq : ∀ x, ‖q x‖ ≤ Cq) :
    Integrable (fun x => star (f x) * (q x * g x)) (μ.restrict 𝓕) := by
  haveI : BorelSpace (WO S T) := ⟨rfl⟩
  haveI : IsFiniteMeasure (μ.restrict 𝓕) := ⟨by rw [Measure.restrict_apply_univ, h1]; exact ENNReal.one_lt_top⟩
  obtain ⟨Cf, hCf⟩ := GlobalTheory.ThetaSchurBdd.exists_bound hψ hf
  obtain ⟨Cg, hCg⟩ := GlobalTheory.ThetaSchurBdd.exists_bound hψ hg
  refine Integrable.of_bound (hf.cont.star.mul (hq.mul hg.cont)).aestronglyMeasurable (Cf * (Cq * Cg))
    (Filter.Eventually.of_forall fun x => ?_)
  rw [norm_mul, norm_mul, norm_star]
  have a0 : 0 ≤ Cq := (norm_nonneg _).trans (hCq x)
  have b0 : 0 ≤ Cf := (norm_nonneg _).trans (hCf x)
  exact mul_le_mul (hCf x) (mul_le_mul (hCq x) (hCg x) (norm_nonneg _) a0) (by positivity) b0

theorem orth_periodic (hψ : IsStdChar D ψ (-1)) {μ : Measure (WO S T)} {𝓕 : Set (WO S T)} (h1 : μ 𝓕 = 1)
    {h k : WO S T → ℂ} (hh : IsThetaFunO ψ S T h) (hk : IsThetaFunO ψ S T k)
    (horth : ∀ γ ∈ ratL T S, thetaIP μ 𝓕 h (heisO ψ S T γ k) = 0)
    {q : WO S T → ℂ} (hq : Continuous q) (hqp : ∀ γ ∈ ratL T S, ∀ x, q (γ + x) = q x)
    {Cq : ℝ} (hCq : ∀ x, ‖q x‖ ≤ Cq) :
    ∫ x in 𝓕, star (h x) * (q x * k x) ∂μ = 0 := by
  haveI : BorelSpace (WO S T) := ⟨rfl⟩
  haveI : IsFiniteMeasure (μ.restrict 𝓕) := ⟨by rw [Measure.restrict_apply_univ, h1]; exact ENNReal.one_lt_top⟩
  have hth := (GlobalTheory.HeisThetaLaws.heis_theta_laws D ψ hψ S T).1
  obtain ⟨Ch, hCh⟩ := GlobalTheory.ThetaSchurBdd.exists_bound hψ hh
  obtain ⟨Ck, hCk⟩ := GlobalTheory.ThetaSchurBdd.exists_bound hψ hk
  have ch0 : 0 ≤ Ch := (norm_nonneg _).trans (hCh 0)
  have ck0 : 0 ≤ Ck := (norm_nonneg _).trans (hCk 0)
  set I := ∫ x in 𝓕, star (h x) * (q x * k x) ∂μ with hIdef
  have hint := integrable_star_mul hψ h1 hh hk hq hCq
  have key : ∀ δ : ℝ, 0 < δ → ‖I‖ ≤ δ * (Ch * Ck) := by
    intro δ hδ
    obtain ⟨s, c, hsc⟩ := GlobalTheory.ThetaSchurBdd.trig_approx hψ hq hqp hδ
    have hpk := GlobalTheory.ThetaSchurBdd.trig_mul_eq s c hk
    have hsum : ∀ x, star (h x) * ((∑ a ∈ s, c a * ψ (symplO S T x a)) * k x) =
        ∑ a ∈ s, c a * (star (h x) * heisO ψ S T a k x) := by
      intro x
      have := congrFun hpk x
      rw [this, Finset.sum_apply, Finset.mul_sum]
      refine Finset.sum_congr rfl fun a _ => ?_
      rw [Pi.smul_apply, smul_eq_mul]
      ring
    have hint_a : ∀ a ∈ s, Integrable (fun x => c a * (star (h x) * heisO ψ S T a k x)) (μ.restrict 𝓕) := by
      intro a _
      have := integrable_star_mul hψ h1 hh (hth a k hk) (q := fun _ => (1 : ℂ)) continuous_const (Cq := 1)
        (fun _ => by simp)
      simp only [one_mul] at this
      exact this.const_mul (c a)
    have hP : ∫ x in 𝓕, star (h x) * ((∑ a ∈ s, c a * ψ (symplO S T x a)) * k x) ∂μ = 0 := by
      simp_rw [hsum]
      rw [integral_finsetSum s hint_a]
      refine Finset.sum_eq_zero fun a _ => ?_
      rw [integral_const_mul]
      have := horth a a.2
      unfold thetaIP at this
      rw [this, mul_zero]
    have hPint : Integrable (fun x => star (h x) * ((∑ a ∈ s, c a * ψ (symplO S T x a)) * k x)) (μ.restrict 𝓕) := by
      simp_rw [hsum]
      exact integrable_finsetSum s hint_a
    have hdiff : I = ∫ x in 𝓕, (star (h x) * (q x * k x) -
        star (h x) * ((∑ a ∈ s, c a * ψ (symplO S T x a)) * k x)) ∂μ := by
      rw [integral_sub hint hPint, hP, sub_zero]
    rw [hdiff]
    have hb : ∀ᵐ x ∂(μ.restrict 𝓕), ‖star (h x) * (q x * k x) -
        star (h x) * ((∑ a ∈ s, c a * ψ (symplO S T x a)) * k x)‖ ≤ δ * (Ch * Ck) := by
      refine Filter.Eventually.of_forall fun x => ?_
      rw [show star (h x) * (q x * k x) - star (h x) * ((∑ a ∈ s, c a * ψ (symplO S T x a)) * k x) =
        star (h x) * ((q x - ∑ a ∈ s, c a * ψ (symplO S T x a)) * k x) by ring]
      rw [norm_mul, norm_mul, norm_star]
      have e1 := hsc x
      calc ‖h x‖ * (‖q x - ∑ a ∈ s, c a * ψ (symplO S T x a)‖ * ‖k x‖) ≤ Ch * (δ * Ck) :=
            mul_le_mul (hCh x) (mul_le_mul e1 (hCk x) (norm_nonneg _) hδ.le) (by positivity) ch0
        _ = δ * (Ch * Ck) := by ring
    refine (norm_integral_le_of_norm_le_const hb).trans ?_
    rw [measureReal_def, Measure.restrict_apply_univ, h1, ENNReal.toReal_one, mul_one]
  by_contra hne
  have hpos : 0 < ‖I‖ := norm_pos_iff.2 hne
  have hM : 0 < Ch * Ck + 1 := by positivity
  have := key (‖I‖ / (Ch * Ck + 1)) (div_pos hpos hM)
  rw [div_mul_eq_mul_div, le_div_iff₀ hM] at this
  nlinarith

theorem pointwise (hψ : IsStdChar D ψ (-1)) {μ : Measure (WO S T)} {𝓕 : Set (WO S T)}
    (hcv : IsCovolOne (ratL T S) μ 𝓕)
    {h k : WO S T → ℂ} (hh : IsThetaFunO ψ S T h) (hk : IsThetaFunO ψ S T k)
    (horth : ∀ γ ∈ ratL T S, thetaIP μ 𝓕 h (heisO ψ S T γ k) = 0) (x : WO S T) :
    h x = 0 ∨ k x = 0 := by
  have h1 : μ 𝓕 = 1 := hcv.2.2
  haveI : BorelSpace (WO S T) := ⟨rfl⟩
  obtain ⟨Ch, hCh⟩ := GlobalTheory.ThetaSchurBdd.exists_bound hψ hh
  obtain ⟨Ck, hCk⟩ := GlobalTheory.ThetaSchurBdd.exists_bound hψ hk
  have ch0 : 0 ≤ Ch := (norm_nonneg _).trans (hCh 0)
  set q : WO S T → ℂ := fun x => h x * star (k x) with hq
  have hqc : Continuous q := hh.cont.mul hk.cont.star
  have hqb : ∀ x, ‖q x‖ ≤ Ch * Ck := fun x => by
    rw [hq, norm_mul, norm_star]
    exact mul_le_mul (hCh x) (hCk x) (norm_nonneg _) ch0
  have hqp : ∀ γ ∈ ratL T S, ∀ x, q (γ + x) = q x := fun γ hγ x =>
    GlobalTheory.ThetaSchur.prod_periodic hψ hh hk hγ x
  have hz := orth_periodic hψ h1 hh hk horth hqc hqp hqb
  set F : WO S T → ℝ := fun x => ‖h x‖ ^ 2 * ‖k x‖ ^ 2 with hF
  have hpt : ∀ x, star (h x) * (q x * k x) = ((F x : ℝ) : ℂ) := by
    intro x
    rw [hq, hF, show star (h x) * (h x * star (k x) * k x) = (star (h x) * h x) * (star (k x) * k x) by ring]
    simp only [Complex.star_def, Complex.conj_mul']
    push_cast
    ring
  have hint := integrable_star_mul hψ h1 hh hk hqc hqb
  simp_rw [hpt] at hz hint
  rw [integral_complex_ofReal, Complex.ofReal_eq_zero] at hz
  have hFi : Integrable F (μ.restrict 𝓕) := by
    have := hint.re
    simpa using this
  have hae : ∀ᵐ x ∂(μ.restrict 𝓕), F x = 0 :=
    (integral_eq_zero_iff_of_nonneg (fun x => by positivity) hFi).1 hz
  have hf : IsThetaFunO ψ S T (fun x => star (k x) * k x * h x) := {
    quasi γ w := by
      rw [hk.quasi, hh.quasi, star_mul']
      linear_combination (star (k w) * k w * h w * ψ (-(symplOH S T (ratW T S γ) w))) *
        GlobalTheory.ThetaSchur.mul_star_psi hψ (-(symplOH S T (ratW T S γ) w))
    level := by
      obtain ⟨U1, o1, h1⟩ := hk.level
      obtain ⟨U2, o2, h2⟩ := hh.level
      refine ⟨U1 ⊓ U2, o1.inter o2, fun u hu hfin => ?_⟩
      funext x
      have e1 := congrFun (h1 u hu.1 hfin) x
      have e2 := congrFun (h2 u hu.2 hfin) x
      simp only [heisO] at e1 e2 ⊢
      have hs := GlobalTheory.ThetaSchur.mul_star_psi hψ (symplOH S T x u)
      rw [← e1, ← e2, star_mul']
      linear_combination (-(ψ (symplOH S T x u) * (star (k (x + u)) * k (x + u) * h (x + u)))) * hs
    cont := (hk.cont.star.mul hk.cont).mul hh.cont
    smooth n L hL hL0 w := by
      have hs : ContDiff ℝ (⊤ : ℕ∞) (fun t => star (k (w + L t))) :=
        Complex.conjCLE.contDiff.comp (hk.smooth n L hL hL0 w)
      exact ContDiff.mul (ContDiff.mul hs (hk.smooth n L hL hL0 w)) (hh.smooth n L hL hL0 w) }
  have h0 : nrm2 μ 𝓕 (fun x => star (k x) * k x * h x) = 0 := by
    unfold nrm2
    refine integral_eq_zero_of_ae ?_
    filter_upwards [hae] with y hy
    have e : ‖star (k y) * k y * h y‖ ^ 2 = ‖k y‖ ^ 2 * F y := by
      rw [hF, norm_mul, norm_mul, norm_star]; ring
    rw [Pi.zero_apply, e, hy, mul_zero]
  have := congrFun (GlobalTheory.ThetaSchurBdd.thetaFunction_eq_zero_of_meanSquare_zero hψ hcv hf h0) x
  simp only [Pi.zero_apply, mul_eq_zero, star_eq_zero, or_self] at this
  exact this.symm

end GlobalTheory.ThetaIrred

theorem GlobalTheory.ThetaIrred.orth_heis_translates : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D), IsStdChar D ψ (-1) →
    ∀ (μ : Measure (WO S T)) (𝓕 : Set (WO S T)), IsCovolOne (ratL T S) μ 𝓕 →
    ∀ h e : WO S T → ℂ, IsThetaFunO ψ S T h → IsThetaFunO ψ S T e →
    (∀ w : WO S T, thetaIP μ 𝓕 h (heisO ψ S T w e) = 0) → h = 0 ∨ e = 0 := by
  intro D ψ S T hψ μ 𝓕 hcv h e hh he horth
  have hth := (GlobalTheory.HeisThetaLaws.heis_theta_laws D ψ hψ S T).1
  have hhh := (GlobalTheory.HeisThetaLaws.heis_theta_laws D ψ hψ S T).2.1
  have key : ∀ w x, h x = 0 ∨ heisO ψ S T w e x = 0 := by
    intro w x
    refine GlobalTheory.ThetaIrred.pointwise hψ hcv hh (hth w e he) (fun γ _ => ?_) x
    rw [hhh γ w e]
    unfold thetaIP
    simp only [Pi.smul_apply, smul_eq_mul, mul_left_comm (star (h _))]
    rw [integral_const_mul]
    have := horth (γ + w)
    unfold thetaIP at this
    rw [this, mul_zero]
  by_cases he0 : e = 0
  · exact Or.inr he0
  left
  obtain ⟨y, hy⟩ : ∃ y, e y ≠ 0 := by
    by_contra hn
    push_neg at hn
    exact he0 (funext hn)
  funext x
  rcases key (y - x) x with h0 | h0
  · exact h0
  · exfalso
    simp only [heisO, add_sub_cancel] at h0
    rcases mul_eq_zero.1 h0 with h1 | h1
    · exact GlobalTheory.ThetaSchurBdd.psi_ne_zero hψ _ h1
    · exact hy h1
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ThetaFunctionMemSpanLevelTypeDifferences
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef
open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.IndefR.Links
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.DownLift
open GlobalTheory.DownLift.GenFinite

noncomputable section

namespace GlobalTheory.DownLift.GenFinite.TypeSpan

variable {D : D7} {V W : HSp D}

theorem levChi_mul' {β : GL (Fin V.rank) (Formalism.IndefR.Lev.EAf D)} {L : Formalism.L2.DIV.LevDat D.host.E ℂ V.rank} {k k' : GA D V}
    (hk : k ∈ levG V β L) (hk' : k' ∈ levG V β L) :
    levChi V β L (k * k') = levChi V β L k * levChi V β L k' := by
  have e := (Formalism.L2.DIV.levChar D.sp.cm V.gram β L).map_mul ⟨_, hk.2⟩ ⟨_, hk'.2⟩
  have e' : Formalism.L2.DIV.levFn β L (finE V k * finE V k') =
      Formalism.L2.DIV.levFn β L (finE V k) * Formalism.L2.DIV.levFn β L (finE V k') := e
  unfold levChi
  rw [map_mul, e', Units.val_mul]

theorem levChi_ne_zero (β : GL (Fin V.rank) (Formalism.IndefR.Lev.EAf D)) (L : Formalism.L2.DIV.LevDat D.host.E ℂ V.rank) (k : GA D V) :
    levChi V β L k ≠ 0 := by
  unfold levChi
  exact Units.ne_zero _

theorem eventually_levChi_one (β : GL (Fin V.rank) (Formalism.IndefR.Lev.EAf D)) (L : Formalism.L2.DIV.LevDat D.host.E ℂ V.rank) :
    ∀ᶠ κ in nhds (1 : GA D V), levChi V β L κ = 1 := by
  classical
  filter_upwards [GlobalTheory.ThetaIntegrand.eventually_princ V β (L.Pg ∪ L.Q)] with κ hh
  obtain ⟨-, -, h3⟩ := hh
  unfold levChi
  rw [GlobalTheory.LevSplit.levFn_eq_one β L _ fun PP hP => h3 PP (by rcases hP with h | h <;> simp [h]), Units.val_one]

end GlobalTheory.DownLift.GenFinite.TypeSpan

namespace GlobalTheory.DownLift.GenFinite

open GlobalTheory.DownLift.GenFinite.TypeSpan

theorem typeSpan : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T : Type) (A : FamIn D.what₂.LL G Pl0 T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), GlobalTheory.LiftRows.Given R F → R.FullP → ∀ (i : Fin D.R.m) (t : T) (f : WO (Vc D i) (Wc D i) → ℂ), IsThetaFunO R.ψ (Vc D i) (Wc D i) f → f ∈ Submodule.span ℂ ({φ | GlobalTheory.DownLift.GenFinite.TypeVec R i t φ} ∪ GlobalTheory.DownLift.GenFinite.TypeDiff R i t) := by
  intro D G _ _ Pl0 T A Ks _ _ _ R F _ hP i t f hf
  classical
  have hW := (hP i t).datum
  haveI := Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.Unfold.topGroupHA D.sp.cm.sig (Vc D i).gram
  obtain ⟨U, U', hUo, -, hfix⟩ := GlobalTheory.Mem.ThetaLevel.exists_level D R.ψ hW.std (Vc D i) (Wc D i) (R.ωP i t)
    (GlobalTheory.Ker.isWeak_of_datum hW) hW.om_cont f hf
  set J := levG (Vc D i) (R.βV i) (R.datVt i t) with hJ
  set lam := levChi (Vc D i) (R.βV i) (R.datVt i t) with hlam
  set om := R.ωP i t with hom
  have hmul : ∀ a b : GA D (Vc D i), om (a * b, 1) = om (a, 1) * om (b, 1) := fun a b => by
    rw [← map_mul, Prod.mk_mul_mk, mul_one]
  have hone : om (1, 1) = 1 := by rw [← Prod.one_eq_mk, map_one]
  have hlm : ∀ {a b : GA D (Vc D i)}, a ∈ J → b ∈ J → lam (a * b) = lam a * lam b := fun ha hb => levChi_mul' ha hb
  have hlne : ∀ a : GA D (Vc D i), lam a ≠ 0 := fun a => levChi_ne_zero _ _ a
  have hlam1 : lam 1 = 1 := by
    have e := hlm (one_mem J) (one_mem J)
    rw [mul_one] at e
    have h0 := hlne 1
    have e' : lam 1 * 1 = lam 1 * lam 1 := by rw [mul_one]; exact e
    exact (mul_left_cancel₀ h0 e').symm

  let N : Subgroup J :=
    { carrier := {κ | om ((κ : GA D (Vc D i)), 1) f = f ∧ lam κ = 1}
      mul_mem' := by
        rintro a b ⟨ha1, ha2⟩ ⟨hb1, hb2⟩
        refine ⟨?_, ?_⟩
        · show om ((a : GA D (Vc D i)) * b, 1) f = f
          rw [hmul, Module.End.mul_apply, hb1, ha1]
        · show lam ((a : GA D (Vc D i)) * b) = 1
          rw [hlm a.2 b.2, ha2, hb2, one_mul]
      one_mem' := by
        refine ⟨?_, ?_⟩
        · show om (1, 1) f = f
          rw [hone]; rfl
        · exact hlam1
      inv_mem' := by
        rintro a ⟨ha1, ha2⟩
        refine ⟨?_, ?_⟩
        · show om ((a : GA D (Vc D i))⁻¹, 1) f = f
          conv_lhs => rw [← ha1]
          rw [← Module.End.mul_apply, ← hmul, inv_mul_cancel, hone]; rfl
        · show lam ((a : GA D (Vc D i))⁻¹) = 1
          have e := hlm (inv_mem a.2) a.2
          rw [inv_mul_cancel, hlam1, ha2, mul_one] at e
          exact e.symm }
  have hNo : IsOpen (N : Set J) := by
    refine Subgroup.isOpen_of_mem_nhds N (g := 1) ?_
    have h1 : {x : GA D (Vc D i) | x ∈ U ∧ lam x = 1} ∈ nhds (1 : GA D (Vc D i)) :=
      Filter.inter_mem (hUo.mem_nhds U.one_mem) (eventually_levChi_one _ _)
    have h2 := (continuous_subtype_val (p := fun x => x ∈ J)).continuousAt (x := (1 : J)).preimage_mem_nhds h1
    exact Filter.mem_of_superset h2 fun κ hκ => ⟨hfix _ hκ.1 κ.2.1 1 U'.one_mem (one_mem _), hκ.2⟩
  haveI : CompactSpace J := isCompact_iff_compactSpace.mp (GlobalTheory.ParahoricCompact.isCompact_levG _ _ _)
  haveI : Finite (J ⧸ N) := Subgroup.quotient_finite_of_isOpen N hNo
  letI : Fintype (J ⧸ N) := Fintype.ofFinite _

  let Fv : J → (WO (Vc D i) (Wc D i) → ℂ) := fun κ => lam κ • om ((κ : GA D (Vc D i)), 1) f
  have hFvN : ∀ (a n : J), n ∈ N → Fv (a * n) = Fv a := by
    rintro a n ⟨hn1, hn2⟩
    show lam ((a : GA D (Vc D i)) * n) • om ((a : GA D (Vc D i)) * n, 1) f = lam a • om ((a : GA D (Vc D i)), 1) f
    rw [hlm a.2 n.2, hn2, mul_one, hmul, Module.End.mul_apply, hn1]
  let Fb : J ⧸ N → (WO (Vc D i) (Wc D i) → ℂ) := fun q => Fv q.out
  have hFb : ∀ κ : J, Fb (κ : J ⧸ N) = Fv κ := by
    intro κ
    obtain ⟨n, hn⟩ := QuotientGroup.mk_out_eq_mul N κ
    show Fv (κ : J ⧸ N).out = Fv κ
    rw [hn]
    exact hFvN κ n n.2
  have hFbTh : ∀ q, IsThetaFunO R.ψ (Vc D i) (Wc D i) (Fb q) := fun q =>
    theta_smul _ (hW.om_pres _ _ hf)

  have hact : ∀ (κ' : J) (q : J ⧸ N), om ((κ' : GA D (Vc D i)), 1) (Fb q) = (lam κ')⁻¹ • Fb (κ' • q) := by
    intro κ' q
    induction q using QuotientGroup.induction_on with
    | H κ =>
      rw [MulAction.Quotient.smul_mk, hFb, hFb]
      show om ((κ' : GA D (Vc D i)), 1) (lam κ • om ((κ : GA D (Vc D i)), 1) f) =
        (lam κ')⁻¹ • (lam ((κ' : GA D (Vc D i)) * κ) • om ((κ' : GA D (Vc D i)) * κ, 1) f)
      rw [map_smul, hmul, Module.End.mul_apply, hlm κ'.2 κ.2, smul_smul, ← mul_assoc,
        inv_mul_cancel₀ (hlne _), one_mul]
  set c : ℂ := ((Fintype.card (J ⧸ N) : ℕ) : ℂ)⁻¹ with hc
  set fJ := c • ∑ q, Fb q with hfJ
  have hfJv : TypeVec R i t fJ := by
    refine ⟨theta_smul _ (theta_sum Finset.univ Fb f hf fun q _ => hFbTh q), fun κ hκ => ?_⟩
    show om (κ, 1) fJ = (lam κ)⁻¹ • fJ
    have e : om (κ, 1) (∑ q, Fb q) = (lam κ)⁻¹ • ∑ q, Fb q := by
      set_option synthInstance.maxHeartbeats 100000 in
        rw [map_sum]
      have := fun q => hact ⟨κ, hκ⟩ q
      simp only [] at this
      rw [Finset.sum_congr rfl fun q _ => this q, ← Finset.smul_sum]
      congr 1
      exact Equiv.sum_comp (MulAction.toPerm (⟨κ, hκ⟩ : J)) Fb
    rw [hfJ, map_smul, e, smul_comm]
  have hdiff : ∀ q, f - Fb q ∈ Submodule.span ℂ ({φ | TypeVec R i t φ} ∪ TypeDiff R i t) := by
    intro q
    induction q using QuotientGroup.induction_on with
    | H κ =>
      rw [hFb]
      have e : f - Fv κ = (-lam κ) • (om ((κ : GA D (Vc D i)), 1) f - (lam κ)⁻¹ • f) := by
        show f - lam κ • om ((κ : GA D (Vc D i)), 1) f = _
        rw [smul_sub, smul_smul, neg_mul, mul_inv_cancel₀ (hlne _)]
        simp only [neg_smul, one_smul]
        abel
      rw [e]
      exact Submodule.smul_mem _ _ (Submodule.subset_span (Or.inr ⟨κ, κ.2, f, hf, rfl⟩))
  have hcard : ((Fintype.card (J ⧸ N) : ℕ) : ℂ) ≠ 0 := by
    have : 0 < Fintype.card (J ⧸ N) := Fintype.card_pos
    exact_mod_cast this.ne'
  have hsplit : f = fJ + c • ∑ q, (f - Fb q) := by
    rw [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, smul_sub, ← Nat.cast_smul_eq_nsmul ℂ, smul_smul,
      hc, inv_mul_cancel₀ hcard, one_smul, hfJ]
    abel
  rw [hsplit]
  exact Submodule.add_mem _ (Submodule.subset_span (Or.inl hfJv))
    (Submodule.smul_mem _ _ (Submodule.sum_mem _ fun q _ => hdiff q))

end GlobalTheory.DownLift.GenFinite

end
end

