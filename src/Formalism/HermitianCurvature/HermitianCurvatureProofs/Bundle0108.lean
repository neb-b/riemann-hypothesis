module

public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0074
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0047
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0102
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.NFRadRedS
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.NFRadRedLocSec
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0080
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0101
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0103
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.ActualAdjointnessFromHermitian
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0104

@[expose] public section

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.CutGCoreGTCLRadTAsmA
section
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt
open scoped ContDiff

namespace Formalism.FourierDecayAlt.P.CutMP.Gauge.GC.RadTA

noncomputable section

open Classical

def Ann {k r : ℕ} (z z' : Fin (2 * r + k + 1) → ℂ) : Set ℂ := {ζ | Tz k r z * Tz k r z' < Complex.normSq ζ}

theorem ann_open {k r : ℕ} (z z' : Fin (2 * r + k + 1) → ℂ) : IsOpen (Ann z z') :=
  isOpen_lt continuous_const Complex.continuous_normSq

theorem exists_pr {V : Type} [AddCommGroup V] [Module ℂ V] (S : Submodule ℂ V) :
    ∃ Pr : V →ₗ[ℂ] V, (∀ x, Pr x ∈ S) ∧ ∀ x ∈ S, Pr x = x := by
  obtain ⟨q, hq⟩ := S.exists_isCompl
  refine ⟨S.subtype ∘ₗ S.linearProjOfIsCompl q hq, fun x => (S.linearProjOfIsCompl q hq x).2, fun x hx => ?_⟩
  exact congrArg Subtype.val (Submodule.linearProjOfIsCompl_apply_left hq ⟨x, hx⟩)

def e2 : Fin 2 → ℂ := ![1, Complex.I]

def crd : Fin 2 → (ℂ →L[ℝ] ℝ) := ![Complex.reCLM, Complex.imCLM]

theorem sum_crd (v : ℂ) : ∑ t : Fin 2, crd t v • e2 t = v := by
  simp only [Fin.sum_univ_two, crd, e2, Matrix.cons_val_zero, Matrix.cons_val_one,
    Complex.reCLM_apply, Complex.imCLM_apply, Complex.real_smul, mul_one]
  exact Complex.re_add_im v

section

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem ml_expand {j : ℕ} (m : ContinuousMultilinearMap ℝ (fun _ : Fin j => ℂ) E) (v : ℂ) :
    m (fun _ => v) = ∑ s : Fin j → Fin 2, (∏ i, crd (s i) v) • m (fun i => e2 (s i)) := by
  have h : (fun _ : Fin j => v) = fun _ => ∑ t : Fin 2, crd t v • e2 t := funext fun _ => (sum_crd v).symm
  set_option synthInstance.maxHeartbeats 100000 in
    rw [h, m.map_sum]
  refine Finset.sum_congr rfl fun s _ => ?_
  exact m.map_smul_univ (fun i => crd (s i) v) (fun i => e2 (s i))

end

section

variable {k r : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq]

def fibS (z z' : Fin (2 * r + k + 1) → ℂ) (μs : ℂ → Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ)
    (π : Q.Mx k r → (Wp →L[ℂ] Wp)) (π' : Q.Mx k r → (Wq →L[ℂ] Wq)) (ζ : ℂ) : Submodule ℂ (Wq →L[ℂ] Wp) where
  carrier := NF.Fib k r z z' μs π π' ζ
  add_mem' := by
    intro X X' hX hX' p hp
    rw [ContinuousLinearMap.add_comp, ContinuousLinearMap.comp_add, hX p hp, hX' p hp]
  zero_mem' := by
    intro p _
    simp
  smul_mem' := by
    intro s X hX p hp
    rw [ContinuousLinearMap.smul_comp, ContinuousLinearMap.comp_smul, hX p hp]

theorem radR_apply {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] {z z' : Fin (2 * r + k + 1) → ℂ}
    {μs : ℂ → Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ} (Φ : Q.Fn k r E) {q : (Fin r → ℂ) × ℂ}
    (hq : q ∈ NF.QR k r z z') : NF.radR k r z z' μs Φ q = Φ q.1 (NF.muZ k r μs q.2) := by
  unfold NF.radR
  rw [Set.indicator_of_mem hq]

theorem radR_add {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] {z z' : Fin (2 * r + k + 1) → ℂ}
    {μs : ℂ → Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ} (Φ Ψ : Q.Fn k r E) :
    NF.radR k r z z' μs (Φ + Ψ) = NF.radR k r z z' μs Φ + NF.radR k r z z' μs Ψ := by
  funext q
  unfold NF.radR
  by_cases hq : q ∈ NF.QR k r z z' <;> simp [hq]

theorem radR_sub {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] {z z' : Fin (2 * r + k + 1) → ℂ}
    {μs : ℂ → Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ} (Φ Ψ : Q.Fn k r E) :
    NF.radR k r z z' μs (Φ - Ψ) = NF.radR k r z z' μs Φ - NF.radR k r z z' μs Ψ := by
  funext q
  unfold NF.radR
  by_cases hq : q ∈ NF.QR k r z z' <;> simp [hq]

theorem radR_smul {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] {z z' : Fin (2 * r + k + 1) → ℂ}
    {μs : ℂ → Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ} (s : ℂ) (Φ : Q.Fn k r E) :
    NF.radR k r z z' μs (s • Φ) = s • NF.radR k r z z' μs Φ := by
  funext q
  unfold NF.radR
  by_cases hq : q ∈ NF.QR k r z z' <;> simp [hq]

theorem radR_zero {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] {z z' : Fin (2 * r + k + 1) → ℂ}
    {μs : ℂ → Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ} :
    NF.radR k r z z' μs (0 : Q.Fn k r E) = 0 := by
  funext q
  unfold NF.radR
  by_cases hq : q ∈ NF.QR k r z z' <;> simp [hq]

end

end

noncomputable section

open Classical

variable {k r : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq]
  {z z' : Fin (2 * r + k + 1) → ℂ} {μs : ℂ → Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ}
  {π : Q.Mx k r → (Wp →L[ℂ] Wp)} {π' : Q.Mx k r → (Wq →L[ℂ] Wq)}
  {Pr : (Wq →L[ℂ] Wp) →ₗ[ℂ] (Wq →L[ℂ] Wp)}

def phiP (z z' : Fin (2 * r + k + 1) → ℂ) (Pr : (Wq →L[ℂ] Wp) →ₗ[ℂ] (Wq →L[ℂ] Wp)) (p : ℂ → (Wq →L[ℂ] Wp)) :
    (Fin r → ℂ) × ℂ → (Wq →L[ℂ] Wp) :=
  (NF.QR k r z z').indicator fun q => Pr (p q.2)

def Gd (z z' : Fin (2 * r + k + 1) → ℂ) (μs : ℂ → Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ)
    (π : Q.Mx k r → (Wp →L[ℂ] Wp)) (π' : Q.Mx k r → (Wq →L[ℂ] Wq)) (Pr : (Wq →L[ℂ] Wp) →ₗ[ℂ] (Wq →L[ℂ] Wp)) : Prop :=
  NF.RadBase k r z z' μs π π' ∧ ∀ x, ∀ ζ ∈ Ann z z', Pr x ∈ NF.Fib k r z z' μs π π' ζ

theorem pr_contDiff (Pr : (Wq →L[ℂ] Wp) →ₗ[ℂ] (Wq →L[ℂ] Wp)) : ContDiff ℝ ∞ (fun x => Pr x) :=
  (LinearMap.toContinuousLinearMap (Pr.restrictScalars ℝ)).contDiff

theorem phiP_mem (hG : Gd z z' μs π π' Pr) {p : ℂ → (Wq →L[ℂ] Wp)} (hp : ContDiff ℝ ∞ p) :
    phiP z z' Pr p ∈ NF.RadSec k r z z' μs π π' := by
  refine ⟨?_, fun q hq => ?_, fun q hq => ?_⟩
  · refine ((pr_contDiff Pr).comp (hp.comp contDiff_snd)).contDiffOn.congr fun q hq => ?_
    simp only [phiP, Set.indicator_of_mem hq, Function.comp]
  · simp only [phiP, Set.indicator_of_mem hq]
    exact hG.2 _ _ hq.2
  · simp only [phiP, Set.indicator_of_notMem hq]

def PhiP (z z' : Fin (2 * r + k + 1) → ℂ) (μs : ℂ → Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ)
    (π : Q.Mx k r → (Wp →L[ℂ] Wp)) (π' : Q.Mx k r → (Wq →L[ℂ] Wq)) (Pr : (Wq →L[ℂ] Wp) →ₗ[ℂ] (Wq →L[ℂ] Wp))
    (p : ℂ → (Wq →L[ℂ] Wp)) : Q.RadSp k r z z' π π' :=
  if h : Gd z z' μs π π' Pr ∧ ContDiff ℝ ∞ p then
    ⟨Classical.choose (Formalism.FourierDecayAlt.P.radical_reduction_surjective Wp Wq k r z z' μs π π' h.1.1 (phiP z z' Pr p)
      (phiP_mem h.1 h.2)),
     (Classical.choose_spec (Formalism.FourierDecayAlt.P.radical_reduction_surjective Wp Wq k r z z' μs π π' h.1.1 (phiP z z' Pr p)
      (phiP_mem h.1 h.2))).1⟩
  else 0

theorem radR_PhiP (hG : Gd z z' μs π π' Pr) {p : ℂ → (Wq →L[ℂ] Wp)} (hp : ContDiff ℝ ∞ p) :
    NF.radR k r z z' μs ((PhiP z z' μs π π' Pr p : Q.RadSp k r z z' π π') : Q.Fn k r (Wq →L[ℂ] Wp)) =
      phiP z z' Pr p := by
  unfold PhiP
  rw [dite_eq_left ⟨hG, hp⟩]
  exact (Classical.choose_spec (Formalism.FourierDecayAlt.P.radical_reduction_surjective Wp Wq k r z z' μs π π' hG.1 (phiP z z' Pr p)
      (phiP_mem hG hp))).2

theorem eq_of_radR (hG : Gd z z' μs π π' Pr) {Φ Ψ : Q.RadSp k r z z' π π'}
    (h : NF.radR k r z z' μs (Φ : Q.Fn k r (Wq →L[ℂ] Wp)) = NF.radR k r z z' μs (Ψ : Q.Fn k r (Wq →L[ℂ] Wp))) :
    Φ = Ψ :=
  Subtype.ext (Formalism.FourierDecayAlt.P.radical_reduction_injective Wp Wq k r z z' μs π π' hG.1 Φ Φ.2 Ψ Ψ.2 h)

theorem PhiP_add (hG : Gd z z' μs π π' Pr) {p p' : ℂ → (Wq →L[ℂ] Wp)} (hp : ContDiff ℝ ∞ p)
    (hp' : ContDiff ℝ ∞ p') :
    PhiP z z' μs π π' Pr (fun ζ => p ζ + p' ζ) = PhiP z z' μs π π' Pr p + PhiP z z' μs π π' Pr p' := by
  refine eq_of_radR hG ?_
  rw [radR_PhiP hG (hp.add hp'), Submodule.coe_add, radR_add, radR_PhiP hG hp, radR_PhiP hG hp']
  funext q
  by_cases hq : q ∈ NF.QR k r z z' <;> simp [phiP, hq]

theorem PhiP_smul (hG : Gd z z' μs π π' Pr) {p : ℂ → (Wq →L[ℂ] Wp)} (hp : ContDiff ℝ ∞ p) (s : ℂ) :
    PhiP z z' μs π π' Pr (fun ζ => s • p ζ) = s • PhiP z z' μs π π' Pr p := by
  refine eq_of_radR hG ?_
  rw [radR_PhiP hG (hp.const_smul s), Submodule.coe_smul, radR_smul, radR_PhiP hG hp]
  funext q
  by_cases hq : q ∈ NF.QR k r z z' <;> simp [phiP, hq]

theorem PhiP_zero (hG : Gd z z' μs π π' Pr) : PhiP z z' μs π π' Pr (fun _ => 0) = 0 := by
  refine eq_of_radR hG ?_
  rw [radR_PhiP hG contDiff_const, Submodule.coe_zero, radR_zero]
  funext q
  by_cases hq : q ∈ NF.QR k r z z' <;> simp [phiP, hq]

def VV (z z' : Fin (2 * r + k + 1) → ℂ) (μs : ℂ → Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ)
    (π : Q.Mx k r → (Wp →L[ℂ] Wp)) (π' : Q.Mx k r → (Wq →L[ℂ] Wq)) (Pr : (Wq →L[ℂ] Wp) →ₗ[ℂ] (Wq →L[ℂ] Wp))
    (T : Module.End ℂ (Q.RadSp k r z z' π π')) (c0 : Fin r → ℂ) (p : ℂ → (Wq →L[ℂ] Wp)) (ζ : ℂ) : Wq →L[ℂ] Wp :=
  NF.radR k r z z' μs ((T (PhiP z z' μs π π' Pr p) : Q.RadSp k r z z' π π') : Q.Fn k r (Wq →L[ℂ] Wp)) (c0, ζ)

variable {T : Module.End ℂ (Q.RadSp k r z z' π π')} {c0 : Fin r → ℂ}

theorem VV_add (hG : Gd z z' μs π π' Pr) {p p' : ℂ → (Wq →L[ℂ] Wp)} (hp : ContDiff ℝ ∞ p)
    (hp' : ContDiff ℝ ∞ p') (ζ : ℂ) :
    VV z z' μs π π' Pr T c0 (fun ζ => p ζ + p' ζ) ζ = VV z z' μs π π' Pr T c0 p ζ + VV z z' μs π π' Pr T c0 p' ζ := by
  unfold VV
  rw [PhiP_add hG hp hp', map_add (f := _), Submodule.coe_add, radR_add]
  rfl

theorem VV_smul (hG : Gd z z' μs π π' Pr) {p : ℂ → (Wq →L[ℂ] Wp)} (hp : ContDiff ℝ ∞ p) (s : ℂ) (ζ : ℂ) :
    VV z z' μs π π' Pr T c0 (fun ζ => s • p ζ) ζ = s • VV z z' μs π π' Pr T c0 p ζ := by
  unfold VV
  rw [PhiP_smul hG hp, map_smul, Submodule.coe_smul, radR_smul]
  rfl

theorem VV_smulR (hG : Gd z z' μs π π' Pr) {p : ℂ → (Wq →L[ℂ] Wp)} (hp : ContDiff ℝ ∞ p) (s : ℝ) (ζ : ℂ) :
    VV z z' μs π π' Pr T c0 (fun ζ => s • p ζ) ζ = s • VV z z' μs π π' Pr T c0 p ζ := by
  have h := VV_smul (T := T) (c0 := c0) hG hp (s : ℂ) ζ
  simp only [Complex.coe_smul] at h
  exact h

theorem VV_zero (hG : Gd z z' μs π π' Pr) (ζ : ℂ) : VV z z' μs π π' Pr T c0 (fun _ => 0) ζ = 0 := by
  unfold VV
  rw [PhiP_zero hG, map_zero, Submodule.coe_zero, radR_zero]
  rfl

theorem VV_sum (hG : Gd z z' μs π π' Pr) {ι : Type} (s : Finset ι) (p : ι → ℂ → (Wq →L[ℂ] Wp))
    (hp : ∀ i, ContDiff ℝ ∞ (p i)) (ζ : ℂ) :
    VV z z' μs π π' Pr T c0 (fun ζ => ∑ i ∈ s, p i ζ) ζ = ∑ i ∈ s, VV z z' μs π π' Pr T c0 (p i) ζ := by
  induction s using Finset.induction_on with
  | empty => simpa using VV_zero (T := T) (c0 := c0) hG ζ
  | insert i s hi ih =>
    simp only [Finset.sum_insert hi]
    rw [VV_add hG (hp i) (ContDiff.sum fun j _ => hp j), ih]

theorem VV_smooth (hG : Gd z z' μs π π' Pr) {p : ℂ → (Wq →L[ℂ] Wp)} (hc0 : c0 ∈ OmX r) :
    ContDiffOn ℝ ∞ (VV z z' μs π π' Pr T c0 p) (Ann z z') := by
  have hm := Formalism.FourierDecayAlt.P.radical_reduction_mem Wp Wq k r z z' μs π π' hG.1
    ((T (PhiP z z' μs π π' Pr p) : Q.RadSp k r z z' π π') : Q.Fn k r (Wq →L[ℂ] Wp))
    (T (PhiP z z' μs π π' Pr p)).2
  exact hm.1.comp (contDiff_const.prodMk contDiff_id).contDiffOn fun ζ hζ => ⟨hc0, hζ⟩

end

end Formalism.FourierDecayAlt.P.CutMP.Gauge.GC.RadTA
end

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.CutGCoreGTCLRadTJetRad
section
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt
open scoped ContDiff

namespace Formalism.FourierDecayAlt.P.CutMP.Gauge.GC

noncomputable section

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

namespace RJR

theorem le_inf (n : ℕ) : (n : WithTop ℕ∞) ≤ ∞ := by
  exact_mod_cast (le_top : ((n : ℕ∞)) ≤ ⊤)

theorem zero_bilin {D E F G : Type*} [NormedAddCommGroup D] [NormedSpace ℝ D] [NormedAddCommGroup E]
    [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedAddCommGroup G] [NormedSpace ℝ G]
    (B : E →L[ℝ] F →L[ℝ] G) {u : D → E} {v : D → F} {s : Set D} {x : D} (hs : IsOpen s) (hx : x ∈ s)
    (hu : ContDiffOn ℝ ∞ u s) (hv : ContDiffOn ℝ ∞ v s) (n : ℕ) (hvz : ∀ j ≤ n, iteratedFDeriv ℝ j v x = 0) :
    ∀ j ≤ n, iteratedFDeriv ℝ j (fun y => B (u y) (v y)) x = 0 := by
  intro j hj
  have hus : UniqueDiffOn ℝ s := hs.uniqueDiffOn
  have key := B.norm_iteratedFDerivWithin_le_of_bilinear hu hv hus hx (n := j) (RJR.le_inf j)
  rw [← norm_le_zero_iff, ← iteratedFDerivWithin_of_isOpen j hs hx]
  refine key.trans (le_of_eq ?_)
  rw [Finset.sum_eq_zero, mul_zero]
  intro i _
  rw [iteratedFDerivWithin_of_isOpen (j - i) hs hx, hvz (j - i) (le_trans (Nat.sub_le _ _) hj),
    norm_zero, mul_zero]

theorem zero_comp {D G : Type*} [NormedAddCommGroup D] [NormedSpace ℝ D] [NormedAddCommGroup G] [NormedSpace ℝ G]
    {ψ : ℂ → G} {ζ : D → ℂ} {s : Set D} {t : Set ℂ} {x : D} (hs : IsOpen s) (ht : IsOpen t) (hx : x ∈ s)
    (hmap : Set.MapsTo ζ s t) (hψ : ContDiffOn ℝ ∞ ψ t) (hζ : ContDiffOn ℝ ∞ ζ s) (n : ℕ)
    (hz : ∀ j ≤ n, iteratedFDeriv ℝ j ψ (ζ x) = 0) :
    ∀ j ≤ n, iteratedFDeriv ℝ j (ψ ∘ ζ) x = 0 := by
  intro j hj
  have hus : UniqueDiffOn ℝ s := hs.uniqueDiffOn
  have hut : UniqueDiffOn ℝ t := ht.uniqueDiffOn
  set Dd : ℝ := ∑ i ∈ Finset.range (j + 1), ‖iteratedFDerivWithin ℝ i ζ s x‖ + 1 with hDd
  have hD1 : 1 ≤ Dd := by
    have : 0 ≤ ∑ i ∈ Finset.range (j + 1), ‖iteratedFDerivWithin ℝ i ζ s x‖ :=
      Finset.sum_nonneg (fun _ _ => norm_nonneg _)
    linarith
  have key := norm_iteratedFDerivWithin_comp_le (n := j) hψ hζ (RJR.le_inf j) hut hus hmap hx
    (C := 0) (D := Dd)
    (fun i hi => by
      rw [iteratedFDerivWithin_of_isOpen i ht (hmap hx), hz i (le_trans hi hj), norm_zero])
    (fun i hi1 hij => by
      have h1 : ‖iteratedFDerivWithin ℝ i ζ s x‖ ≤ Dd := by
        have : ‖iteratedFDerivWithin ℝ i ζ s x‖ ≤ ∑ i ∈ Finset.range (j + 1), ‖iteratedFDerivWithin ℝ i ζ s x‖ :=
          Finset.single_le_sum (f := fun i => ‖iteratedFDerivWithin ℝ i ζ s x‖)
            (fun _ _ => norm_nonneg _) (Finset.mem_range.2 (Nat.lt_succ_of_le hij))
        linarith
      refine h1.trans ?_
      first
        | exact le_self_pow₀ hD1 (by omega)
        | exact le_self_pow hD1 (by omega))
  rw [← norm_le_zero_iff, ← iteratedFDerivWithin_of_isOpen j hs hx]
  simpa using key

def Bc (Wp Wq : Type) [NormedAddCommGroup Wp] [NormedSpace ℂ Wp] [NormedAddCommGroup Wq] [NormedSpace ℂ Wq] :
    (Wp →L[ℂ] Wp) →L[ℝ] (Wq →L[ℂ] Wp) →L[ℝ] (Wq →L[ℂ] Wp) :=
  ((ContinuousLinearMap.restrictScalarsL ℂ (Wq →L[ℂ] Wp) (Wq →L[ℂ] Wp) ℝ ℂ).comp
    (ContinuousLinearMap.compL ℂ Wq Wp Wp)).restrictScalars ℝ

def Bd (Wp Wq : Type) [NormedAddCommGroup Wp] [NormedSpace ℂ Wp] [NormedAddCommGroup Wq] [NormedSpace ℂ Wq] :
    (Wq →L[ℂ] Wq) →L[ℝ] (Wq →L[ℂ] Wp) →L[ℝ] (Wq →L[ℂ] Wp) :=
  ((ContinuousLinearMap.restrictScalarsL ℂ (Wq →L[ℂ] Wp) (Wq →L[ℂ] Wp) ℝ ℂ).comp
    (ContinuousLinearMap.compL ℂ Wq Wq Wp).flip).restrictScalars ℝ

end RJR

open RJR in
theorem jet_radial_holds : GTCLRJetRad := by
  intro Wp Wq _ _ _ _ _ _ P Bs _ _ Φ q hq N hN
  have hq1 : q.1 ∈ OmX P.r := hq.1
  have hB : NF.RadBase P.k P.r Bs.z Bs.z' Bs.μsec Bs.π Bs.π' :=
    ⟨Bs.k_pos, Bs.z_mem, Bs.z'_mem, Bs.T_pos, Bs.T'_pos, Bs.sec, Bs.π_rep, Bs.π'_rep, Bs.π_cont,
      Bs.π'_cont⟩
  have hmem := Formalism.FourierDecayAlt.P.radical_reduction_mem Wp Wq P.k P.r Bs.z Bs.z' Bs.μsec Bs.π Bs.π' hB Φ Φ.2
  have hΦe := (Φ.2).2.2
  let tt : Set ℂ := {ζ | Tz P.k P.r Bs.z * Tz P.k P.r Bs.z' < Complex.normSq ζ}
  have ht : IsOpen tt := isOpen_lt continuous_const Complex.continuous_normSq
  let ψ : ℂ → (Wq →L[ℂ] Wp) := fun ζ =>
    NF.radR P.k P.r Bs.z Bs.z' Bs.μsec (Φ : Q.Fn P.k P.r (Wq →L[ℂ] Wp)) (q.1, ζ)
  have hmapQ : Set.MapsTo (fun ζ : ℂ => (q.1, ζ)) tt (NF.QR P.k P.r Bs.z Bs.z') :=
    fun ζ hζ => ⟨hq1, hζ⟩
  have hpair : ContDiff ℝ ∞ (fun ζ : ℂ => (q.1, ζ)) := by
    first
      | exact contDiff_const.prodMk contDiff_id
      | exact contDiff_const.prod contDiff_id
  have hψs : ContDiffOn ℝ ∞ ψ tt := hmem.1.comp hpair.contDiffOn hmapQ
  have hψval : ∀ ζ ∈ tt, ψ ζ = (Φ : Q.Fn P.k P.r (Wq →L[ℂ] Wp)) q.1 (NF.muZ P.k P.r Bs.μsec ζ) := by
    intro ζ hζ
    simp only [ψ, NF.radR]
    rw [Set.indicator_of_mem (hmapQ hζ)]
  have hdom := Formalism.FourierDecayAlt.P.NFRadRedA.mem_domR Bs.z_mem Bs.z'_mem Bs.sec hq
  obtain ⟨V, hV, hg₀V, a, b, ha, hb, hfac⟩ :=
    Formalism.FourierDecayAlt.P.local_smooth_section P.k P.r Bs.z Bs.z' Bs.μsec Bs.k_pos Bs.z_mem Bs.z'_mem Bs.T_pos
      Bs.T'_pos Bs.sec _ hdom.2.1 hdom.2.2
  have hf0 := hfac _ hg₀V hdom.2.1 hdom.2.2
  obtain ⟨Vp, hVp, haVp, Pp, hPp, hPpe⟩ :=
    Formalism.FourierDecayAlt.P.representation_smooth Wp P.k P.r Bs.z Bs.π Bs.z_mem Bs.T_pos Bs.π_rep Bs.π_cont _ hf0.1
  obtain ⟨Vq, hVq, hbVq, Pq, hPq, hPqe⟩ :=
    Formalism.FourierDecayAlt.P.representation_smooth Wq P.k P.r Bs.z' Bs.π' Bs.z'_mem Bs.T'_pos Bs.π'_rep Bs.π'_cont _
      hf0.2.1
  let zL := Q.zetaL P.k P.r Bs.z Bs.z' (Fin.last P.r)
  have hzL : ContDiff ℝ ∞ zL := Formalism.FourierDecayAlt.P.Qx5.zetaL_contDiff P.k P.r Bs.z Bs.z' (Fin.last P.r)
  have hz0 : zL (NF.muZ P.k P.r Bs.μsec q.2) = q.2 :=
    Formalism.FourierDecayAlt.P.NFRadRedA.zeta_muZ Bs.z_mem Bs.z'_mem Bs.sec hq.2
  let W : Set (Q.Mx P.k P.r) := (V ∩ a ⁻¹' Vp) ∩ (V ∩ b ⁻¹' Vq) ∩ zL ⁻¹' tt
  have hW : IsOpen W :=
    ((ha.continuousOn.isOpen_inter_preimage hV hVp).inter
      (hb.continuousOn.isOpen_inter_preimage hV hVq)).inter (ht.preimage hzL.continuous)
  have hg₀W : NF.muZ P.k P.r Bs.μsec q.2 ∈ W := by
    refine ⟨⟨⟨hg₀V, haVp⟩, ⟨hg₀V, hbVq⟩⟩, ?_⟩
    show zL (NF.muZ P.k P.r Bs.μsec q.2) ∈ tt
    rw [hz0]
    exact hq.2
  have hu : ContDiffOn ℝ ∞ (fun g => Pp (a g)) W :=
    hPp.comp (ha.mono fun g hg => hg.1.1.1) fun g hg => hg.1.1.2
  have hu' : ContDiffOn ℝ ∞ (fun g => Pq (b g)) W :=
    hPq.comp (hb.mono fun g hg => hg.1.2.1) fun g hg => hg.1.2.2
  have hv' : ContDiffOn ℝ ∞ (ψ ∘ zL) W := hψs.comp hzL.contDiffOn fun g hg => hg.2
  have hv : ContDiffOn ℝ ∞ (fun g => Bd Wp Wq (Pq (b g)) ((ψ ∘ zL) g)) W :=
    ((Bd Wp Wq).contDiff.comp_contDiffOn hu').clm_apply hv'
  have hF : ContDiffOn ℝ ∞ (fun g => Bc Wp Wq (Pp (a g)) (Bd Wp Wq (Pq (b g)) ((ψ ∘ zL) g))) W :=
    ((Bc Wp Wq).contDiff.comp_contDiffOn hu).clm_apply hv
  have hz1 : ∀ j ≤ N, iteratedFDeriv ℝ j ψ (zL (NF.muZ P.k P.r Bs.μsec q.2)) = 0 := by
    rw [hz0]
    exact hN
  have hv'0 := zero_comp hW ht hg₀W (fun g hg => hg.2) hψs hzL.contDiffOn N hz1
  have hv0 := zero_bilin (Bd Wp Wq) hW hg₀W hu' hv' N hv'0
  have hF0 := zero_bilin (Bc Wp Wq) hW hg₀W hu hv N hv0
  refine ⟨W, _, hW, hg₀W, hF, ?_, hF0⟩
  intro g hg hGl
  have hgt : Tz P.k P.r Bs.z * Tz P.k P.r Bs.z' < Complex.normSq (zL g) := hg.2
  have hGG : 0 < Q.GGl P.k P.r Bs.z Bs.z' g := by
    show 0 < Complex.normSq (zL g) - Tz P.k P.r Bs.z * Tz P.k P.r Bs.z'
    exact sub_pos.2 hgt
  obtain ⟨haU, hbU, hfg⟩ := hfac g hg.1.1.1 hGl hGG
  have hdom' := Formalism.FourierDecayAlt.P.NFRadRedA.mem_domR Bs.z_mem Bs.z'_mem Bs.sec (q := (q.1, zL g)) ⟨hq1, hgt⟩
  have he := hΦe (q.1, NF.muZ P.k P.r Bs.μsec (zL g)) hdom' (a g) haU (b g) hbU
  have hl : (Φ : Q.Fn P.k P.r (Wq →L[ℂ] Wp)) q.1 g =
      (Φ : Q.Fn P.k P.r (Wq →L[ℂ] Wp)) q.1 (a g * NF.muZ P.k P.r Bs.μsec (zL g) * b g) := by
    conv_lhs => rw [hfg]
  rw [hl, he]
  simp only
  rw [hPpe (a g) hg.1.1.2 haU, hPqe (b g) hg.1.2.2 hbU, ← hψval (zL g) hgt]
  rfl

end

end Formalism.FourierDecayAlt.P.CutMP.Gauge.GC
end

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.CutJAGQQSSFCut
section
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt NumberField

namespace Formalism.FourierDecayAlt.P.CutMP.JA.SSn.Rep.Core.GQ

noncomputable section

def GQBridge : Prop :=
  ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq]
    [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (P : M.Par) (Bs : B.RealPlaceData P.k P.r Wp Wq),
    2 ≤ P.k → ∀ (X : Q.ActualOps P.k P.r Bs.z Bs.z' Bs.π Bs.π') (d : Q.NFData P (Q.Pr (Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π'))),
    ActHyp P Bs X d → ∀ e : M.Ty P → ℂ → (Wq →L[ℂ] Wp), Gauge.IsFrameB P Bs e → GQQ P Bs e →
    ∀ (Y : ℝ) (a b : Fin 2), Gauge.GC.Intw P Bs e (X.QQ (Y : ℂ) a b) (MA.QQr P (MA.DQ P) (Y : ℂ) a b)

def GQKap : Prop :=
  ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq]
    [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (P : M.Par) (Bs : B.RealPlaceData P.k P.r Wp Wq),
    2 ≤ P.k → ∀ (X : Q.ActualOps P.k P.r Bs.z Bs.z' Bs.π Bs.π') (d : Q.NFData P (Q.Pr (Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π'))),
    ActHyp P Bs X d → ∀ e : M.Ty P → ℂ → (Wq →L[ℂ] Wp), Gauge.IsFrameB P Bs e →
    (∀ (Y : ℝ) (a b : Fin 2), Gauge.GC.Intw P Bs e (d.QQ (Y : ℂ) a b) (MA.QQr P (MA.DQ P) (Y : ℂ) a b)) →
    ∀ f : M.Ty P → ℂ, Gauge.GC.Intw P Bs e (d.κ f) (MA.kap P (MA.DQ P) f)

def GQSS : Prop :=
  ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq]
    [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (P : M.Par) (Bs : B.RealPlaceData P.k P.r Wp Wq),
    2 ≤ P.k → ∀ (X : Q.ActualOps P.k P.r Bs.z Bs.z' Bs.π Bs.π') (d : Q.NFData P (Q.Pr (Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π'))),
    ActHyp P Bs X d → ∀ e : M.Ty P → ℂ → (Wq →L[ℂ] Wp), Gauge.IsFrameB P Bs e →
    (∀ (Y : ℝ) (a b : Fin 2), Gauge.GC.Intw P Bs e (d.QQ (Y : ℂ) a b) (MA.QQr P (MA.DQ P) (Y : ℂ) a b)) →
    (∀ f : M.Ty P → ℂ, Gauge.GC.Intw P Bs e (d.κ f) (MA.kap P (MA.DQ P) f)) →
    ∀ l ∈ Finset.Icc 1 (P.k - 1),
      Gauge.GC.Intw P Bs e (d.SS l) (MA.SS P (MA.DQ P) l) ∧
      Gauge.GC.Intw P Bs e (star (d.SS l)) (star (MA.SS P (MA.DQ P) l))

def GQQSSFOfCut : Prop := GQBridge → GQKap → GQSS → GQQSSF

theorem gQQSSF_of_cut : GQQSSFOfCut := by
  intro hB hK hS Wp Wq _ _ _ _ _ _ P Bs hk X d hA e he hg
  have hQ : ∀ (Y : ℝ) (a b : Fin 2), Gauge.GC.Intw P Bs e (d.QQ (Y : ℂ) a b) (MA.QQr P (MA.DQ P) (Y : ℂ) a b) := by
    intro Y a b
    rw [← hA.2.2.2.2 (Y : ℂ)]
    exact hB Wp Wq P Bs hk X d hA e he hg Y a b
  have hκ := hK Wp Wq P Bs hk X d hA e he hQ
  intro l hl Φ
  exact ⟨(hS Wp Wq P Bs hk X d hA e he hQ hκ l hl).1 Φ, (hS Wp Wq P Bs hk X d hA e he hQ hκ l hl).2 Φ⟩

end

end Formalism.FourierDecayAlt.P.CutMP.JA.SSn.Rep.Core.GQ
end

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.CutJAPRCPRcComm
section
open Matrix
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.Q
open scoped ContDiff

namespace Formalism.FourierDecayAlt.P.CutMP.JA.SSn.Rep.Core.TC.PR.CP

noncomputable section

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

theorem radial_coefficient_commutation : RcComm := by
  intro k r E _ _ D f _ hf Z₁ Z₂ h₁ h₂ g hg
  exact Qx5.RZ_comm hf hg h₁ h₂

end

end Formalism.FourierDecayAlt.P.CutMP.JA.SSn.Rep.Core.TC.PR.CP
end

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.PsiMajNonneg
section
noncomputable section

open MeasureTheory Matrix
open scoped InnerProductSpace ENNReal

namespace Formalism.FourierDecayAlt.P.S3dx6

open Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.ThreeDimData

variable {k r : ℕ}

theorem gN_nonneg (g : Mx k r) : 0 ≤ B.gN g := Real.sqrt_nonneg _

end Formalism.FourierDecayAlt.P.S3dx6
end
end

