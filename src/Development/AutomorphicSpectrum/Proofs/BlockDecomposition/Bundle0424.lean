module

public import Mathlib
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.RealDescent.RealLeviDescent.Bundle0001
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0396
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0372
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0341
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.WeilThetaConvergence
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsSmoothModerateOfIsAutFunSm
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0212
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LintegralNormSqEqToL2
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0075
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ThetaNormCommutation.LocalComparisonSplitting.GlobalCharacterOfInputs
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0061
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0400
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.InfinitesimalCharacterLimits.AllLeaves
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0282

@[expose] public section

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.RealFirstNilpotent
section
noncomputable section

open Finset
open PositivityTheory.RgBcC PositivityTheory.RgBcC.Real PositivityTheory.RgBcC.RealD

namespace GlobalTheory.CompanionTheory.HarmCone

variable {n : ℕ}

def sg (lev : Fin n → ℕ) (a b : Fin n) : ℝ :=
  (if lev a < lev b then 1 else 0) - (if lev b < lev a then 1 else 0)

theorem two_rhoU (lev : Fin n → ℕ) (a : Fin n) : 2 * rhoU lev a = ∑ b, sg lev a b := by
  simp only [rhoU, sg, Finset.sum_sub_distrib, Finset.sum_boole]
  ring

theorem sg_anti (lev : Fin n → ℕ) (a b : Fin n) : sg lev a b = - sg lev b a := by
  unfold sg
  ring

theorem sg_cases (lev : Fin n → ℕ) (a b : Fin n) :
    sg lev a b = 1 ∨ sg lev a b = 0 ∨ sg lev a b = -1 := by
  unfold sg
  split_ifs <;> norm_num

theorem mul_sg_self (lev : Fin n → ℕ) (a b : Fin n) :
    ((lev a : ℝ) - lev b) * sg lev a b = -|(lev a : ℝ) - lev b| := by
  rcases lt_trichotomy (lev a) (lev b) with h | h | h
  · have h' : (lev a : ℝ) < lev b := by exact_mod_cast h
    have hs : sg lev a b = 1 := by
      unfold sg
      rw [if_pos h, if_neg (by omega)]
      norm_num
    rw [hs, abs_of_neg (by linarith)]
    ring
  · have hs : sg lev a b = 0 := by
      unfold sg
      rw [if_neg (by omega), if_neg (by omega)]
      norm_num
    rw [hs, h]
    simp
  · have h' : (lev b : ℝ) < lev a := by exact_mod_cast h
    have hs : sg lev a b = -1 := by
      unfold sg
      rw [if_neg (by omega), if_pos h]
      norm_num
    rw [hs, abs_of_pos (by linarith)]
    ring

theorem neg_abs_le_mul_sg (lev : Fin n → ℕ) (x : ℝ) (a b : Fin n) : -|x| ≤ x * sg lev a b := by
  have h1 := neg_abs_le x
  have h2 := le_abs_self x
  have h3 := abs_nonneg x
  rcases sg_cases lev a b with h | h | h <;> rw [h] <;> linarith

theorem pair_root (f : Fin n → ℝ) (a b : Fin n) :
    ∑ x, f x * ((if x = a then 1 else 0) - (if x = b then 1 else 0)) = f a - f b := by
  simp [mul_sub, Finset.sum_sub_distrib]

def dsg (lev lev' : Fin n → ℕ) (x b : Fin n) : ℝ := sg lev' x b - sg lev x b

theorem dsg_anti (lev lev' : Fin n → ℕ) (x b : Fin n) : dsg lev lev' x b = - dsg lev lev' b x := by
  unfold dsg
  rw [sg_anti lev' x b, sg_anti lev x b]
  ring

theorem dsg_nonneg (lev lev' : Fin n → ℕ) (x b : Fin n) :
    0 ≤ ((lev x : ℝ) - lev b) * dsg lev lev' x b := by
  unfold dsg
  rw [mul_sub, mul_sg_self]
  have := neg_abs_le_mul_sg lev' ((lev x : ℝ) - lev b) x b
  linarith

theorem pairing_nonneg (lev lev' : Fin n → ℕ) :
    0 ≤ ∑ x, (lev x : ℝ) * ∑ b, dsg lev lev' x b := by
  have e1 : ∑ x, ∑ b, (lev x : ℝ) * dsg lev lev' x b = ∑ x, (lev x : ℝ) * ∑ b, dsg lev lev' x b := by
    simp only [Finset.mul_sum]
  have e2 : ∑ x, ∑ b, (lev b : ℝ) * dsg lev lev' x b = -∑ x, (lev x : ℝ) * ∑ b, dsg lev lev' x b := by
    rw [Finset.sum_comm, ← e1, ← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun b _ => ?_
    rw [dsg_anti lev lev' b x]
    ring
  have e3 : ∑ x, ∑ b, ((lev x : ℝ) - lev b) * dsg lev lev' x b
      = 2 * ∑ x, (lev x : ℝ) * ∑ b, dsg lev lev' x b := by
    simp only [sub_mul, Finset.sum_sub_distrib]
    rw [e1, e2]
    ring
  have e4 : 0 ≤ ∑ x, ∑ b, ((lev x : ℝ) - lev b) * dsg lev lev' x b :=
    Finset.sum_nonneg fun x _ => Finset.sum_nonneg fun b _ => dsg_nonneg lev lev' x b
  linarith

theorem harm_cone : N1 := by
  intro n lam _ lev lev' _ _ hc
  obtain ⟨c, hc0, hQ⟩ := hc
  have hQx : ∀ x, (muQ lam lev' - muQ lam lev) x = ∑ b, dsg lev lev' x b := by
    intro x
    simp only [Pi.sub_apply, muQ, dsg, Finset.sum_sub_distrib, ← two_rhoU]
    ring
  have hD : ∑ x, (lev x : ℝ) * ∑ b, dsg lev lev' x b
      = ∑ a, ∑ b, (c a b : ℝ) * ((lev a : ℝ) - lev b) := by
    have e : ∀ x, (lev x : ℝ) * ∑ b, dsg lev lev' x b = ∑ a, ∑ b, (c a b : ℝ) *
        ((lev x : ℝ) * ((if x = a then 1 else 0) - (if x = b then 1 else 0))) := by
      intro x
      rw [← hQx, hQ x, Finset.mul_sum]
      refine Finset.sum_congr rfl fun a _ => ?_
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun b _ => ?_
      ring
    simp only [e]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun b _ => ?_
    rw [← Finset.mul_sum, pair_root (fun x => (lev x : ℝ)) a b]
  have hterm : ∀ a b, (c a b : ℝ) * ((lev a : ℝ) - lev b) ≤ 0 := by
    intro a b
    by_cases h0 : c a b = 0
    · simp [h0]
    · have h1 : (lev a : ℝ) < lev b := by exact_mod_cast hc0 a b h0
      have h2 : (0 : ℝ) ≤ c a b := Nat.cast_nonneg _
      nlinarith
  have hsum : ∑ a, ∑ b, (c a b : ℝ) * ((lev a : ℝ) - lev b) = 0 :=
    le_antisymm (Finset.sum_nonpos fun a _ => Finset.sum_nonpos fun b _ => hterm a b)
      (hD ▸ pairing_nonneg lev lev')
  have h1 := (Finset.sum_eq_zero_iff_of_nonpos
    (fun a _ => Finset.sum_nonpos fun b _ => hterm a b)).1 hsum
  have hz : ∀ a b, c a b = 0 := by
    intro a b
    by_contra h0
    have h2 := (Finset.sum_eq_zero_iff_of_nonpos (fun b _ => hterm a b)).1
      (h1 a (Finset.mem_univ _)) b (Finset.mem_univ _)
    have h3 : (lev a : ℝ) < lev b := by exact_mod_cast hc0 a b h0
    have h4 : (c a b : ℝ) ≠ 0 := by exact_mod_cast h0
    rcases mul_eq_zero.1 h2 with h | h
    · exact h4 h
    · linarith
  funext x
  have h5 := hQ x
  simp only [hz, Nat.cast_zero, zero_mul, Finset.sum_const_zero] at h5
  exact sub_eq_zero.1 h5

end GlobalTheory.CompanionTheory.HarmCone
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.RestrictionBallIndicatorSpan
section
noncomputable section

open Matrix GlobalTheory.PRep GlobalTheory.BZMir GlobalTheory.SplitWeil GlobalTheory.CompanionTheory.MirFourier GlobalTheory.CompanionTheory.MirLevi
open MeasureTheory GlobalTheory.CompanionTheory.Rodier GlobalTheory.CompanionTheory.Rodier.SmIntEl
open scoped Topology

namespace GlobalTheory.CompanionTheory.ThetaInt

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem isOpen_ball (n : ℕ) (s : kˣ) :
    IsOpen {a : Fin n → k | Multiplicative.ofAdd a ∈ polyBall (k := k) n s} :=
  (isOpen_polyBall n s).preimage continuous_ofAdd

theorem isCompact_ball (n : ℕ) (s : kˣ) :
    IsCompact {a : Fin n → k | Multiplicative.ofAdd a ∈ polyBall (k := k) n s} := by
  have e : {a : Fin n → k | Multiplicative.ofAdd a ∈ polyBall (k := k) n s} =
      Multiplicative.toAdd '' (polyBall (k := k) n s : Set (Multiplicative (Fin n → k))) := by
    ext a
    constructor
    · intro h
      exact ⟨Multiplicative.ofAdd a, h, rfl⟩
    · rintro ⟨x, hx, rfl⟩
      exact hx
  rw [e]
  exact (isCompact_polyBall n s).image continuous_toAdd

theorem isLocallyConstant_of_periodic {n : ℕ} {Y : Type} (g : (Fin n → k) → Y) (s : kˣ)
    (h : ∀ v a : Fin n → k, Multiplicative.ofAdd a ∈ polyBall (k := k) n s → g (v + a) = g v) :
    IsLocallyConstant g := by
  refine (IsLocallyConstant.iff_eventually_eq _).mpr fun x => ?_
  have h0 : (fun z : Fin n → k => -x + z) ⁻¹'
      {a : Fin n → k | Multiplicative.ofAdd a ∈ polyBall (k := k) n s} ∈ 𝓝 x :=
    ((isOpen_ball n s).preimage (by fun_prop)).mem_nhds (by
      show Multiplicative.ofAdd (-x + x) ∈ polyBall (k := k) n s
      rw [neg_add_cancel]
      exact one_mem _)
  filter_upwards [h0] with z hz
  have e : z = x + (-x + z) := by abel
  rw [e]
  exact h x _ hz

theorem hasCompactSupport_of_ball {n : ℕ} {E : Type} [AddCommGroup E] (g : (Fin n → k) → E) (S : kˣ)
    (h : ∀ v, g v ≠ 0 → Multiplicative.ofAdd v ∈ polyBall (k := k) n S) : HasCompactSupport g := by
  haveI := GlobalTheory.SplitWeil.t2Space k
  refine HasCompactSupport.intro (isCompact_ball n S) fun x hx => ?_
  by_contra h1
  exact hx (h x h1)

def tw (ψ : AddChar k Circle) {N : ℕ} {E : Type} [AddCommGroup E] [Module ℂ E]
    (g : (Fin (N + 1) → k) → E) : (Fin (N + 1) → k) → E :=
  fun v => ((ψ (-(v (Fin.last N))) : Circle) : ℂ) • g v

variable {N : ℕ} {E : Type} [AddCommGroup E] [Module ℂ E]

theorem isLocallyConstant_tw (ψ : AddChar k Circle) (hψ : Continuous ψ)
    {g : (Fin (N + 1) → k) → E} (hg : IsLocallyConstant g) : IsLocallyConstant (tw ψ g) := by
  obtain ⟨s, hs⟩ := exists_cball_addChar_eq_one ψ hψ
  have h1 : IsLocallyConstant fun v : Fin (N + 1) → k => ((ψ (-(v (Fin.last N))) : Circle) : ℂ) := by
    refine isLocallyConstant_of_periodic _ s fun v a ha => ?_
    have h2 : ψ (a (Fin.last N)) = 1 := hs _ (ha (Fin.last N))
    rw [Pi.add_apply, neg_add, AddChar.map_add_eq_mul, AddChar.map_neg_eq_inv (a := a (Fin.last N)), h2,
      inv_one, mul_one]
  exact h1.comp₂ hg fun c x => c • x

theorem hasCompactSupport_tw (ψ : AddChar k Circle) {g : (Fin (N + 1) → k) → E} (S : kˣ)
    (h : ∀ v, g v ≠ 0 → Multiplicative.ofAdd v ∈ polyBall (k := k) (N + 1) S) :
    HasCompactSupport (tw ψ g) := by
  refine hasCompactSupport_of_ball _ S fun v hv => h v fun h0 => hv ?_
  simp [tw, h0]

section Int

variable [MeasurableSpace k] [BorelSpace k] [SecondCountableTopology k] (ν : Measure k)
  [ν.IsAddHaarMeasure]

theorem smInt_comp_inv_mulVec (g : GL (Fin (N + 1)) k) {φ : (Fin (N + 1) → k) → E}
    (l : IsLocallyConstant φ) :
    smInt (Measure.pi fun _ : Fin (N + 1) => ν) (φ ∘ ((g⁻¹ : GL (Fin (N + 1)) k) :
        Matrix (Fin (N + 1)) (Fin (N + 1)) k).mulVec) =
      ((nabs k (Matrix.GeneralLinearGroup.det g) : ℝ) : ℂ) •
        smInt (Measure.pi fun _ : Fin (N + 1) => ν) φ := by
  have hm : ∀ B : Matrix (Fin (N + 1)) (Fin (N + 1)) k, Measurable B.mulVec := fun B =>
    (continuous_const.matrix_mulVec continuous_id).measurable
  have key : ∀ B : Set (Fin (N + 1) → k), MeasurableSet B →
      (Measure.pi fun _ : Fin (N + 1) => ν)
          (((g⁻¹ : GL (Fin (N + 1)) k) : Matrix (Fin (N + 1)) (Fin (N + 1)) k).mulVec ⁻¹' B) =
        (distribHaarChar k (Matrix.GeneralLinearGroup.det g) : ENNReal) *
          (Measure.pi fun _ : Fin (N + 1) => ν) B := by
    intro B hB
    have h1 := GlobalTheory.WeilM.smul_map_mulVec_pi ν g.val (Matrix.GeneralLinearGroup.det g) rfl
    conv_lhs => rw [← h1]
    rw [Measure.smul_apply, Measure.map_apply (hm _) ((hm _) hB), smul_eq_mul]
    congr 2
    ext x
    simp only [Set.mem_preimage, mulVec_mulVec]
    rw [← Units.val_mul, inv_mul_cancel, Units.val_one, one_mulVec]
  unfold smInt
  rw [smul_finsum]
  refine finsum_congr fun v => ?_
  rw [Set.preimage_comp, key (φ ⁻¹' {v}) (l.isOpen_fiber v).measurableSet, ENNReal.toReal_mul, smul_smul]
  congr 1
  simp [nabs]

end Int

theorem exists_twisted_integral : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (ψ : AddChar k Circle), Continuous ψ → ∀ (N : ℕ) (X E : Type) [AddCommGroup X] [Module ℂ X] [AddCommGroup E] [Module ℂ E] (r : X →ₗ[ℂ] (Fin (N + 1) → k) → E), (∀ f, ∃ s : kˣ, ∀ (v a : Fin (N + 1) → k), Multiplicative.ofAdd a ∈ polyBall (k := k) (N + 1) s → r f (v + a) = r f v) → (∀ f, ∃ S : kˣ, ∀ v : Fin (N + 1) → k, r f v ≠ 0 → Multiplicative.ofAdd v ∈ polyBall (k := k) (N + 1) S) → ∀ (tr : (Fin (N + 1) → k) → X → X), (∀ a f v, r (tr a f) v = r f (v + a)) → ∀ (lev : GL (Fin (N + 1)) k → X → X) (A : GL (Fin (N + 1)) k → E →ₗ[ℂ] E), (∀ m f v, r (lev m f) v = A m (r f (((m⁻¹ : GL (Fin (N + 1)) k) : Matrix (Fin (N + 1)) (Fin (N + 1)) k).mulVec v))) → ∃ T : X →ₗ[ℂ] E, (∀ a f, T (tr a f) = ((ψ (a (Fin.last N)) : Circle) : ℂ) • T f) ∧ (∀ m : GL (Fin (N + 1)) k, m ∈ Mir k N → ∀ f, T (lev m f) = ((nabs k (Matrix.GeneralLinearGroup.det m) : ℝ) : ℂ) • A m (T f)) ∧ (∀ s : kˣ, (∀ a : Fin (N + 1) → k, Multiplicative.ofAdd a ∈ polyBall (k := k) (N + 1) s → ψ (a (Fin.last N)) = 1) → ∃ c : ℂ, c ≠ 0 ∧ ∀ (b : X) (e : E), (∀ v, r b v = @ite _ (Multiplicative.ofAdd v ∈ polyBall (k := k) (N + 1) s) (Classical.propDecidable _) e 0) → T b = c • e) := by
  intro k _ _ _ _ ψ hψ N X E _ _ _ _ r hper hsup tr htr lev A hlev
  borelize k
  haveI := GlobalTheory.SplitWeil.secondCountable k
  haveI := GlobalTheory.SplitWeil.t2Space k
  obtain ⟨ν, hν⟩ : ∃ ν : Measure k, ν.IsAddHaarMeasure := ⟨Measure.addHaar, inferInstance⟩
  let μ : Measure (Fin (N + 1) → k) := Measure.pi fun _ => ν
  haveI hμ : μ.IsAddHaarMeasure := Measure.pi.isAddHaarMeasure _
  have hl : ∀ f, IsLocallyConstant (tw ψ (r f)) := fun f => by
    obtain ⟨s, hs⟩ := hper f
    exact isLocallyConstant_tw ψ hψ (isLocallyConstant_of_periodic _ s fun v a ha => hs v a ha)
  have hc : ∀ f, HasCompactSupport (tw ψ (r f)) := fun f => by
    obtain ⟨S, hS⟩ := hsup f
    exact hasCompactSupport_tw ψ S hS
  let T : X →ₗ[ℂ] E :=
    { toFun := fun f => smInt μ (tw ψ (r f))
      map_add' := fun f g => by
        have e : tw ψ (r (f + g)) = tw ψ (r f) + tw ψ (r g) := by
          funext v
          simp [tw, map_add (f := _), smul_add]
        show smInt μ (tw ψ (r (f + g))) = smInt μ (tw ψ (r f)) + smInt μ (tw ψ (r g))
        rw [e, smInt_add μ (hl f) (hc f) (hl g) (hc g)]
      map_smul' := fun c f => by
        have e : tw ψ (r (c • f)) = (c • LinearMap.id : E →ₗ[ℂ] E) ∘ tw ψ (r f) := by
          funext v
          simp only [tw, Function.comp, map_smul, Pi.smul_apply, LinearMap.smul_apply, LinearMap.id_apply]
        show smInt μ (tw ψ (r (c • f))) = c • smInt μ (tw ψ (r f))
        rw [e, smInt_linear μ _ (hl f) (hc f)]
        rfl }
  have hT : ∀ f, T f = smInt μ (tw ψ (r f)) := fun _ => rfl
  refine ⟨T, ?_, ?_, ?_⟩
  · intro a f
    let L : E →ₗ[ℂ] E := ((ψ (a (Fin.last N)) : Circle) : ℂ) • LinearMap.id
    have e : tw ψ (r (tr a f)) = (L ∘ tw ψ (r f)) ∘ fun v => v + a := by
      funext v
      simp only [tw, Function.comp, htr, L, LinearMap.smul_apply, LinearMap.id_apply, smul_smul]
      congr 1
      rw [← Circle.coe_mul, ← AddChar.map_add_eq_mul]
      congr 2
      simp only [Pi.add_apply]
      abel
    rw [hT, hT, e, smInt_comp_measurePreserving μ (measurePreserving_add_right μ a) ((hl f).comp _),
      smInt_linear μ L (hl f) (hc f)]
    rfl
  · intro m hm f
    have e : tw ψ (r (lev m f)) = (A m ∘ tw ψ (r f)) ∘
        ((m⁻¹ : GL (Fin (N + 1)) k) : Matrix (Fin (N + 1)) (Fin (N + 1)) k).mulVec := by
      funext v
      simp only [tw, Function.comp, hlev, map_smul]
      rw [mulVec_last_of_mem k _ (inv_mem hm) v]
    rw [hT, hT, e]
    refine (smInt_comp_inv_mulVec ν m ((hl f).comp _)).trans ?_
    congr 1
    exact smInt_linear μ (A m) (hl f) (hc f)
  · intro s hs
    have hLo := isOpen_ball (k := k) (N + 1) s
    have hLc := isCompact_ball (k := k) (N + 1) s
    refine ⟨(((μ {a | Multiplicative.ofAdd a ∈ polyBall (k := k) (N + 1) s}).toReal : ℝ) : ℂ), ?_, fun b e hb => ?_⟩
    · have h0 := (hLo.measure_pos μ ⟨0, one_mem (polyBall (k := k) (N + 1) s)⟩).ne'
      exact Complex.ofReal_ne_zero.2 (ENNReal.toReal_ne_zero.2 ⟨h0, hLc.measure_lt_top.ne⟩)
    · have e' : tw ψ (r b) = Set.indicator {a | Multiplicative.ofAdd a ∈ polyBall (k := k) (N + 1) s} fun _ => e := by
        funext v
        by_cases hv : Multiplicative.ofAdd v ∈ polyBall (k := k) (N + 1) s
        · have h1 : ψ (v (Fin.last N)) = 1 := hs v hv
          simp only [tw]
          rw [hb v, if_pos hv, Set.indicator_of_mem (show v ∈ {a | Multiplicative.ofAdd a ∈ polyBall (k := k) (N + 1) s} from hv),
            AddChar.map_neg_eq_inv, h1]
          simp
        · simp only [tw]
          rw [hb v, if_neg hv, Set.indicator_of_notMem (show v ∉ {a | Multiplicative.ofAdd a ∈ polyBall (k := k) (N + 1) s} from hv),
            smul_zero]
      rw [hT, e', smInt_indicator]

end GlobalTheory.CompanionTheory.ThetaInt
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SchwartzBoundFiniteInfinite
section
open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.SiegelFormula
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.CompanionTheory.WeilTheta

theorem schwartzA_continuous_and_dominated : ∀ (D : D7) (θ : InfFam D), IsInfFam θ → ∀ (m n : ℕ) (Φ : Mx D m n → ℂ),
    Φ ∈ schwartzA θ m n → Continuous Φ ∧ ∃ (k : ℕ) (f : Fin k → SchwartzMap (D.what₂.Tau → Fin m → Fin n → ℂ) ℂ)
      (g : Fin k → (Fin m → Fin n → Af D.host.F ⊗[D.host.F] D.host.E) → ℂ),
      (∀ i, g i ∈ GlobalTheory.WeilM.SB (Fin m → Fin n → Af D.host.F ⊗[D.host.F] D.host.E)) ∧
      ∀ x, ‖Φ x‖ₑ ≤ ∑ i, ‖f i (fun τ i' j => compAt θ τ x i' j) * g i (fun i' j => finPart D (x i' j))‖ₑ := by
  intro D θ hθ m n Φ hΦ
  have hy : Continuous fun x : Mx D m n => (fun τ i j => compAt θ τ x i j : D.what₂.Tau → Fin m → Fin n → ℂ) :=
    continuous_pi fun τ => continuous_pi fun i => continuous_pi fun j =>
      (GlobalTheory.RealWeil.continuous_compAt hθ τ m n).matrix_elem i j
  have hz : Continuous fun x : Mx D m n =>
      (fun i j => finPart D (x i j) : Fin m → Fin n → Af D.host.F ⊗[D.host.F] D.host.E) :=
    continuous_pi fun i => continuous_pi fun j =>
      (GlobalTheory.Member.continuous_finPart D).comp (continuous_id.matrix_elem i j)
  induction hΦ using Submodule.span_induction with
  | mem Φ h =>
    obtain ⟨f, g, hg, rfl⟩ := h
    refine ⟨(f.continuous.comp hy).mul (hg.1.continuous.comp hz), 1, fun _ => f, fun _ => g, fun _ => hg, fun x => ?_⟩
    simp
  | zero =>
    exact ⟨continuous_const, 0, Fin.elim0, Fin.elim0, fun i => i.elim0, fun x => by simp⟩
  | add Φ₁ Φ₂ _ _ h₁ h₂ =>
    obtain ⟨c₁, k₁, f₁, g₁, hg₁, hb₁⟩ := h₁
    obtain ⟨c₂, k₂, f₂, g₂, hg₂, hb₂⟩ := h₂
    refine ⟨c₁.add c₂, k₁ + k₂, Fin.append f₁ f₂, Fin.append g₁ g₂, fun i => ?_, fun x => ?_⟩
    · refine Fin.addCases (fun i => ?_) (fun i => ?_) i
      · rw [Fin.append_left]; exact hg₁ i
      · rw [Fin.append_right]; exact hg₂ i
    · rw [Fin.sum_univ_add]
      simp only [Fin.append_left, Fin.append_right]
      exact (enorm_add_le _ _).trans (add_le_add (hb₁ x) (hb₂ x))
  | smul c Φ _ h =>
    obtain ⟨hc, k, f, g, hg, hb⟩ := h
    refine ⟨hc.const_smul c, k, fun i => c • f i, g, hg, fun x => ?_⟩
    have e : ∀ i, ‖(c • f i) (fun τ i' j => compAt θ τ x i' j) * g i (fun i' j => finPart D (x i' j))‖ₑ =
        ‖c‖ₑ * ‖f i (fun τ i' j => compAt θ τ x i' j) * g i (fun i' j => finPart D (x i' j))‖ₑ := fun i => by
      rw [smul_apply, smul_eq_mul, mul_assoc, enorm_mul]
    simp only [e, Pi.smul_apply, smul_eq_mul]
    rw [← Finset.mul_sum, enorm_mul]
    gcongr
    exact hb x

end GlobalTheory.CompanionTheory.WeilTheta

end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SecondCountableUnits
section
open NumberField IsDedekindDomain Matrix
open GlobalTheory.CuspRep GlobalTheory.BCT PositivityTheory.Rg.BcB PositivityTheory.Rg.BcB.G8

noncomputable section

namespace GlobalTheory.CompanionTheory.LocalThetaTopology

theorem locallyCompact_units {M : Type} [Ring M] [TopologicalSpace M] [IsTopologicalRing M] [T2Space M]
    [LocallyCompactSpace M] : LocallyCompactSpace Mˣ :=
  Units.isClosedEmbedding_embedProduct.locallyCompactSpace

theorem secondCountable_units {M : Type} [Monoid M] [TopologicalSpace M] [SecondCountableTopology M] :
    SecondCountableTopology Mˣ := by
  haveI : SecondCountableTopology Mᵐᵒᵖ := (MulOpposite.opHomeomorph (M := M)).symm.secondCountableTopology
  exact Units.isEmbedding_embedProduct.secondCountableTopology

theorem t2Space_units {M : Type} [Monoid M] [TopologicalSpace M] [T2Space M] : T2Space Mˣ :=
  Units.isEmbedding_embedProduct.t2Space

theorem top_GL {R : Type} [CommRing R] [TopologicalSpace R] [IsTopologicalRing R] [T2Space R] [LocallyCompactSpace R]
    [SecondCountableTopology R] (n : ℕ) :
    LocallyCompactSpace (GL (Fin n) R) ∧ SecondCountableTopology (GL (Fin n) R) ∧ T2Space (GL (Fin n) R) := by
  haveI : LocallyCompactSpace (Matrix (Fin n) (Fin n) R) := inferInstanceAs (LocallyCompactSpace (Fin n → Fin n → R))
  haveI : SecondCountableTopology (Matrix (Fin n) (Fin n) R) :=
    inferInstanceAs (SecondCountableTopology (Fin n → Fin n → R))
  haveI : T2Space (Matrix (Fin n) (Fin n) R) := inferInstanceAs (T2Space (Fin n → Fin n → R))
  exact ⟨locallyCompact_units, secondCountable_units, t2Space_units⟩

theorem continuous_thetaR {A : Type} [CommRing A] [TopologicalSpace A] [IsTopologicalRing A] (σ : A →+* A)
    (hσ : Continuous σ) (n : ℕ) : Continuous (thetaR σ n) :=
  Units.continuous_iff.2 ⟨(Units.continuous_coe_inv.matrix_map hσ).matrix_transpose,
    (Units.continuous_val.matrix_map hσ).matrix_transpose⟩

theorem countable_numberField (E : Type) [Field E] [NumberField E] : Countable E := by
  let b := Module.finBasis ℚ E
  exact Function.Injective.countable b.equivFun.injective

theorem countable_GL (E : Type) [Field E] [NumberField E] (n : ℕ) : Countable (GL (Fin n) E) := by
  haveI := countable_numberField E
  haveI : Countable (Matrix (Fin n) (Fin n) E) := inferInstanceAs (Countable (Fin n → Fin n → E))
  exact Function.Injective.countable (f := fun g : GL (Fin n) E => (g : Matrix (Fin n) (Fin n) E)) fun _ _ h => Units.ext h

theorem continuous_thF (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ) : Continuous (thF E n) := by
  have h : (thF E n : GL (Fin n) (Af E) → GL (Fin n) (Af E)) = fun g =>
      PhiU n (Af E) * thetaR (conjFin (IsCMField.complexConj E).toRingEquiv) n g * (PhiU n (Af E))⁻¹ :=
    funext fun g => thetaGL_eq n (Af E) _ g
  rw [h]
  exact (continuous_const.mul (continuous_thetaR _ (continuous_conjFin _) n)).mul continuous_const

theorem topo : Topo := by
  intro E _ _ _ n
  haveI := GlobalTheory.AdelicUnitaryTop.locallyCompact_adele E
  haveI := GlobalTheory.AdelicUnitaryTop.secondCountable_adele E
  haveI := GlobalTheory.AdelicUnitaryTop.t2Space_adeleRing_numberField E
  haveI := GlobalTheory.AdelicUnitaryTop.locallyCompact_finiteAdele E
  haveI := GlobalTheory.AdelicUnitaryTop.secondCountable_finiteAdele E
  haveI := GlobalTheory.AdelicUnitaryTop.t2Space_finiteAdeleRing_of_numberField E
  obtain ⟨c1, c2, -⟩ := top_GL (R := ℂ) n
  exact ⟨top_GL n, top_GL n, ⟨c1, c2⟩, countable_GL E n, continuous_thF E n,
    continuous_thetaR _ Complex.continuous_conj n⟩

end GlobalTheory.CompanionTheory.LocalThetaTopology
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.UniformBoundSiegelSetStatement
section
open scoped ENNReal
open NumberField IsDedekindDomain Matrix MeasureTheory Filter Topology Polynomial
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC PositivityTheory.Rg.Rs GlobalTheory.CompanionTheory.Conc
open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.AutomorphicForm
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.uniform_bound_siegel_set : ∀ (K : Type) [Field K] [NumberField K] (n : ℕ) [MeasurableSpace (AdelicGLn.AdelicGL K n)] [BorelSpace (AdelicGLn.AdelicGL K n)] (μ : Measure (AdelicGLn.AdelicGL K n)) [μ.IsHaarMeasure] (ι : Type)
  (f : ι → AdelicGLn.AdelicGL K n → ℂ) (κ : ℕ → ℝ), (∀ i, Continuous (f i)) → UBnd f κ → (∀ r, 0 < r → r < n → κ r < An.rho K n r) →
  ∀ ω : Set (AdelicGLn.AdelicGL K n), IsCompact ω → ω ⊆ (adelicBorel (K := K) (n := n) : Set _) → ∀ (t₀ : ℝ) (η : ℝ≥0∞), 0 < η →
  ∃ Ω : Set (AdelicGLn.AdelicGL K n), IsCompact Ω ∧ ∀ i, ∫⁻ g in An.slab ω t₀ \ Ω, ‖f i g‖ₑ ^ 2 ∂μ ≤ η := by
  first | exact @GlobalTheory.CompanionTheory.Conc.TailU.tail_unif | exact GlobalTheory.CompanionTheory.Conc.TailU.tail_unif | (intros; apply GlobalTheory.CompanionTheory.Conc.TailU.tail_unif <;> assumption)
end

