module

public import Mathlib
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.QuotientEigenDifference
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0078
public import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.Bundle0004
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0032
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0030
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0024
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0117
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0071
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0044
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0057
public import Development.AbelianVarietyTheory.Definitions.Divisors.TCoefMInMMul
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsCyclotomicExtensionQI

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SingleMemOfMem
section
open scoped NNReal

namespace GlobalTheory.Div.KerFil
open GlobalTheory.IndefiniteRowSideFullHecke.QuotientEigenDifference

variable {C : Type} [Field C] {w : Valuation C ℝ≥0}

theorem smul_vec_apply {r : ℕ} (b : w.valuationSubring) (v : Fin r → C) (i : Fin r) :
    (b • v) i = (b : C) * v i := rfl

theorem smul_C (b : w.valuationSubring) (z : C) : b • z = (b : C) * z := rfl

theorem smul_pi_apply {S : Type} {r : ℕ} (b : w.valuationSubring) (x : S → Fin r → C) (s : S)
    (i : Fin r) : (b • x) s i = (b : C) * x s i := rfl

theorem exists_prod_apply {S : Type} [DecidableEq S] {r : ℕ} (a : S → w.valuationSubring)
    (Fil : Submodule w.valuationSubring (S → Fin r → C))
    (hst : ∀ x ∈ Fil, unif a x ∈ Fil) (x : S → Fin r → C) (hx : x ∈ Fil) (T : Finset S) :
    ∃ y ∈ Fil, ∀ s' i, y s' i = (∏ s ∈ T, ((a s' : C) - a s)) * x s' i := by
  induction T using Finset.induction_on with
  | empty => exact ⟨x, hx, fun _ _ => by simp⟩
  | insert s0 T hs0 ih =>
    obtain ⟨y, hy, hyv⟩ := ih
    refine ⟨unif a y - a s0 • y, sub_mem (hst y hy) (Fil.smul_mem _ hy), fun s' i => ?_⟩
    rw [Finset.prod_insert hs0]
    simp only [Pi.sub_apply, unif, Pi.smul_apply, smul_eq_mul]
    rw [smul_C, hyv]
    ring

theorem single_mem_of_mem {S : Type} [Fintype S] [DecidableEq S] {r : ℕ}
    (a : S → w.valuationSubring) (Fil : Submodule w.valuationSubring (S → Fin r → C))
    (hst : ∀ x ∈ Fil, unif a x ∈ Fil) (τ : S) (x : S → Fin r → C) (hx : x ∈ Fil) :
    (Pi.single τ (diffGen a τ • x τ) : S → Fin r → C) ∈ Fil := by
  obtain ⟨y, hy, hyv⟩ := exists_prod_apply a Fil hst x hx (Finset.univ.erase τ)
  convert hy using 1
  funext s' i
  rw [hyv]
  by_cases e : s' = τ
  · subst e
    simp only [Pi.single_eq_same, smul_vec_apply, diffGen]
    push_cast
    rfl
  · rw [Finset.prod_eq_zero (i := s') (Finset.mem_erase.2 ⟨e, Finset.mem_univ _⟩) (sub_self _)]
    simp [e]

theorem diffGen_ne_zero {S : Type} [Fintype S] [DecidableEq S] (a : S → w.valuationSubring)
    (ha : Function.Injective a) (τ : S) : diffGen a τ ≠ 0 := by
  rw [diffGen, Finset.prod_ne_zero_iff]
  intro s hs e
  exact (Finset.mem_erase.1 hs).1 (ha (sub_eq_zero.1 e)).symm

end GlobalTheory.Div.KerFil

namespace GlobalTheory.Div.KerFil
open GlobalTheory.IndefiniteRowSideFullHecke.QuotientEigenDifference

variable {C : Type} [Field C] {w : Valuation C ℝ≥0}

def clearDen {S : Type} [DecidableEq S] {r : ℕ}
    (Fil : Submodule w.valuationSubring (S → Fin r → C)) (τ : S) : Submodule C (Fin r → C) where
  carrier := {v | ∃ b : w.valuationSubring, b ≠ 0 ∧ (Pi.single τ (b • v) : S → Fin r → C) ∈ Fil}
  zero_mem' := ⟨1, one_ne_zero, by simp⟩
  add_mem' := by
    rintro v v' ⟨b, hb, h⟩ ⟨b', hb', h'⟩
    refine ⟨b * b', mul_ne_zero hb hb', ?_⟩
    have : (Pi.single τ ((b * b') • (v + v')) : S → Fin r → C) =
        b' • (Pi.single τ (b • v) : S → Fin r → C) + b • (Pi.single τ (b' • v') : S → Fin r → C) := by
      funext s i
      by_cases e : s = τ
      · subst e; simp only [Pi.single_eq_same, Pi.add_apply, smul_pi_apply, smul_vec_apply]
        push_cast; ring
      · simp [e]
    rw [this]
    exact add_mem (Fil.smul_mem _ h) (Fil.smul_mem _ h')
  smul_mem' := by
    rintro c v ⟨b, hb, h⟩
    by_cases hc0 : c = 0
    · exact ⟨1, one_ne_zero, by simp [hc0]⟩
    rcases w.valuationSubring.mem_or_inv_mem c with hc | hc
    · refine ⟨b, hb, ?_⟩
      have : (Pi.single τ (b • c • v) : S → Fin r → C) =
          (⟨c, hc⟩ : w.valuationSubring) • (Pi.single τ (b • v) : S → Fin r → C) := by
        funext s i
        by_cases e : s = τ
        · subst e; simp only [Pi.single_eq_same, smul_pi_apply, smul_vec_apply, Pi.smul_apply,
            smul_eq_mul, smul_C]
          ring
        · simp [e]
      rw [this]
      exact Fil.smul_mem _ h
    · have hne : (⟨c⁻¹, hc⟩ : w.valuationSubring) ≠ 0 := by
        intro e
        exact hc0 (inv_eq_zero.1 (congrArg Subtype.val e))
      refine ⟨b * ⟨c⁻¹, hc⟩, mul_ne_zero hb hne, ?_⟩
      have : (b * ⟨c⁻¹, hc⟩ : w.valuationSubring) • c • v = b • v := by
        funext i
        simp only [smul_vec_apply, Pi.smul_apply, smul_eq_mul, smul_C]
        push_cast
        field_simp
      rw [this]
      exact h

end GlobalTheory.Div.KerFil
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SmoothAlongCurveProductsStable
section
open MeasureTheory
open scoped ContDiff

namespace GlobalTheory
namespace CurveProductSmooth

variable {G : Type} [Group G] {K : Type} [NormedAddCommGroup K] [InnerProductSpace ℂ K]
  (ρ : G →* (K →L[ℂ] K)) {P : Type} (A : Set P) (e : P → ℝ → G)

def JointlySmooth {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] (Φ : E → K) : Prop :=
  ∀ (F : Type) [NormedAddCommGroup F] [NormedSpace ℝ F] (g : F → E), ContDiff ℝ ∞ g →
    ∀ l : List (P × (F → ℝ)), (∀ a ∈ l, a.1 ∈ A ∧ ContDiff ℝ ∞ a.2) →
      ContDiff ℝ ∞ fun x : F => ρ (l.map fun a => e a.1 (a.2 x)).prod (Φ (g x))

variable {ρ A e}

end CurveProductSmooth

open MeasureTheory in
open scoped ContDiff in
variable {G : Type} [Group G] {K : Type} [NormedAddCommGroup K] [InnerProductSpace ℂ K]
  (ρ : G →* (K →L[ℂ] K)) {P : Type} (A : Set P) (e : P → ℝ → G) in
variable {ρ A e} in
private theorem contDiff_prod_ofFn_apply_of_jointlySmooth {k : ℕ} {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {Φ : E → K} (h : _root_.GlobalTheory.CurveProductSmooth.JointlySmooth ρ A e Φ) {g : (Fin k → ℝ) → E}
    (hg : ContDiff ℝ ∞ g) (ps : Fin k → P) (hps : ∀ i, ps i ∈ A) :
    ContDiff ℝ ∞ fun t : Fin k → ℝ => ρ (List.ofFn fun i => e (ps i) (t i)).prod (Φ (g t)) := by
  have h1 := h (Fin k → ℝ) g hg (List.ofFn fun i => (ps i, fun t : Fin k → ℝ => t i)) (by
    intro a ha
    rw [List.mem_ofFn] at ha
    obtain ⟨i, rfl⟩ := ha
    exact ⟨hps i, contDiff_apply ℝ (fun _ => ℝ) i⟩)
  simpa [List.map_ofFn, Function.comp_def] using h1

open MeasureTheory in
open scoped ContDiff in
variable {G : Type} [Group G] {K : Type} [NormedAddCommGroup K] [InnerProductSpace ℂ K]
  (ρ : G →* (K →L[ℂ] K)) {P : Type} (A : Set P) (e : P → ℝ → G) in
variable {ρ A e} in
private theorem deriv_continuousLinearMap_comp_eq (T : K →L[ℂ] K) (f : ℝ → K) (hf : DifferentiableAt ℝ f 0) :
    deriv (fun r => T (f r)) 0 = T (deriv f 0) :=
  ((T.restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt (0 : ℝ) hf.hasDerivAt).deriv

open MeasureTheory in
open scoped ContDiff in
variable {G : Type} [Group G] {K : Type} [NormedAddCommGroup K] [InnerProductSpace ℂ K]
  (ρ : G →* (K →L[ℂ] K)) {P : Type} (A : Set P) (e : P → ℝ → G) in
variable {ρ A e} in
private theorem jointlySmooth_deriv_action {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] {Φ : E → K}
    (h : _root_.GlobalTheory.CurveProductSmooth.JointlySmooth ρ A e Φ) {p : P} (hp : p ∈ A) :
    _root_.GlobalTheory.CurveProductSmooth.JointlySmooth ρ A e fun t => deriv (fun r : ℝ => ρ (e p r) (Φ t)) 0 := by
  intro F _ _ g hg l hl
  have hf : ∀ y : E, ContDiff ℝ ∞ fun r : ℝ => ρ (e p r) (Φ y) := fun y => by
    simpa using h ℝ (fun _ => y) contDiff_const [(p, id)] (by simp [hp, contDiff_id])
  let H : F × ℝ → K := fun z =>
    ρ (((l.map fun a : P × (F → ℝ) => (a.1, a.2 ∘ Prod.fst)) ++ [(p, Prod.snd)]).map
      fun a : P × (F × ℝ → ℝ) => e a.1 (a.2 z)).prod
      (Φ (g z.1))
  have hH : ContDiff ℝ ∞ H := h (F × ℝ) (g ∘ Prod.fst) (hg.comp contDiff_fst) _ (by
    intro a ha
    rcases List.mem_append.1 ha with ha | ha
    · obtain ⟨b, hb, rfl⟩ := List.mem_map.1 ha
      exact ⟨(hl b hb).1, (hl b hb).2.comp contDiff_fst⟩
    · rw [List.mem_singleton] at ha
      subst ha
      exact ⟨hp, contDiff_snd⟩)
  have hHx : ∀ x r, H (x, r) = ρ (l.map fun a => e a.1 (a.2 x)).prod (ρ (e p r) (Φ (g x))) := by
    intro x r
    simp [H, List.map_append, List.map_map, Function.comp_def, map_mul]
  have hder : ∀ x, ρ (l.map fun a => e a.1 (a.2 x)).prod (deriv (fun r : ℝ => ρ (e p r) (Φ (g x))) 0)
      = fderiv ℝ H (x, 0) (0, 1) := by
    intro x
    rw [← deriv_continuousLinearMap_comp_eq _ _ ((hf (g x)).differentiable (by simp)).differentiableAt]
    have h2 : HasDerivAt (fun r : ℝ => H (x, r)) (fderiv ℝ H (x, 0) (0, 1)) 0 :=
      (hH.differentiable (by simp)).differentiableAt.hasFDerivAt.comp_hasDerivAt (0 : ℝ)
        ((hasDerivAt_const (0 : ℝ) x).prodMk (hasDerivAt_id (0 : ℝ)))
    rw [← h2.deriv]
    simp only [hHx]
  have hfin : ContDiff ℝ ∞ fun x : F => fderiv ℝ H (x, 0) (0, 1) :=
    ((contDiff_infty_iff_fderiv.1 hH).2.comp (contDiff_id.prodMk contDiff_const)).clm_apply
      contDiff_const
  convert hfin using 1
  funext x
  exact hder x

open MeasureTheory in
open scoped ContDiff in
variable {G : Type} [Group G] {K : Type} [NormedAddCommGroup K] [InnerProductSpace ℂ K]
  (ρ : G →* (K →L[ℂ] K)) {P : Type} (A : Set P) (e : P → ℝ → G) in
variable {ρ A e} in
private theorem jointlySmooth_const' {v : K}
    (hv : ∀ (k : ℕ) (ps : Fin k → P), (∀ i, ps i ∈ A) →
      ContDiff ℝ ∞ fun t : Fin k → ℝ => ρ (List.ofFn fun i => e (ps i) (t i)).prod v)
    {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] :
    _root_.GlobalTheory.CurveProductSmooth.JointlySmooth ρ A e (fun _ : E => v) := by
  intro F _ _ g _ l hl
  have h1 := hv l.length (fun i => l[i].1) (fun i => (hl _ (List.getElem_mem _)).1)
  have h2 : ContDiff ℝ ∞ fun x : F => fun i : Fin l.length => l[i].2 x :=
    contDiff_pi.2 fun i => (hl _ (List.getElem_mem _)).2
  have h3 := h1.comp h2
  convert h3 using 1
  funext x
  have hlist : (l.map fun a : P × (F → ℝ) => e a.1 (a.2 x)) =
      List.ofFn fun i : Fin l.length => e l[i].1 (l[i].2 x) :=
    List.ext_getElem (by simp) (by simp)
  simp only [hlist, Function.comp_apply]

open MeasureTheory in
open scoped ContDiff in
variable {G : Type} [Group G] {K : Type} [NormedAddCommGroup K] [InnerProductSpace ℂ K]
  (ρ : G →* (K →L[ℂ] K)) {P : Type} (A : Set P) (e : P → ℝ → G) in
variable {ρ A e} in
private theorem jointlySmooth_prod_map_action {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {Φ : E → K} (h : _root_.GlobalTheory.CurveProductSmooth.JointlySmooth ρ A e Φ) (m : List (P × (E → ℝ)))
    (hm : ∀ a ∈ m, a.1 ∈ A ∧ ContDiff ℝ ∞ a.2) :
    _root_.GlobalTheory.CurveProductSmooth.JointlySmooth ρ A e fun y => ρ (m.map fun a => e a.1 (a.2 y)).prod (Φ y) := by
  intro F _ _ g hg l hl
  have h1 := h F g hg (l ++ m.map fun a => (a.1, a.2 ∘ g)) (by
    intro a ha
    rcases List.mem_append.1 ha with ha | ha
    · exact hl a ha
    · obtain ⟨b, hb, rfl⟩ := List.mem_map.1 ha
      exact ⟨(hm b hb).1, (hm b hb).2.comp hg⟩)
  convert h1 using 1
  funext x
  simp [List.map_append, List.prod_append, map_mul, List.map_map, Function.comp_def]

open MeasureTheory in
open scoped ContDiff in
variable {G : Type} [Group G] {K : Type} [NormedAddCommGroup K] [InnerProductSpace ℂ K]
  (ρ : G →* (K →L[ℂ] K)) {P : Type} (A : Set P) (e : P → ℝ → G) in
variable {ρ A e} in
private theorem jointlySmooth_foldr_deriv_action {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {Φ : E → K} (h : _root_.GlobalTheory.CurveProductSmooth.JointlySmooth ρ A e Φ) (l : List P) (hl : ∀ p ∈ l, p ∈ A) :
    _root_.GlobalTheory.CurveProductSmooth.JointlySmooth ρ A e fun t =>
      l.foldr (fun p w => deriv (fun r : ℝ => ρ (e p r) w) 0) (Φ t) := by
  induction l with
  | nil => exact h
  | cons q l ih =>
    exact jointlySmooth_deriv_action (ih fun p hp => hl p (List.mem_cons_of_mem _ hp)) (hl q (by simp))


open scoped ContDiff in
theorem _root_.GlobalTheory.smooth_along_curve_products_stable : ∀ (G : Type) [Group G] (K : Type) [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K] (ρ : G →* (K →L[ℂ] K)) (P : Type) (A : Set P) (e : P → ℝ → G) (v : K), (∀ (k : ℕ) (ps : Fin k → P), (∀ i, ps i ∈ A) → ContDiff ℝ ∞ fun t : Fin k → ℝ => ρ (List.ofFn fun i => e (ps i) (t i)).prod v) → (∀ p ∈ A, ∀ (k : ℕ) (ps : Fin k → P), (∀ i, ps i ∈ A) → ContDiff ℝ ∞ fun t : Fin k → ℝ => ρ (List.ofFn fun i => e (ps i) (t i)).prod (deriv (fun r : ℝ => ρ (e p r) v) 0)) ∧ (∀ (m : ℕ) (qs : Fin m → P) (r : Fin m → ℝ), (∀ i, qs i ∈ A) → ∀ (k : ℕ) (ps : Fin k → P), (∀ i, ps i ∈ A) → ContDiff ℝ ∞ fun t : Fin k → ℝ => ρ (List.ofFn fun i => e (ps i) (t i)).prod (ρ (List.ofFn fun i => e (qs i) (r i)).prod v)) ∧ ∀ l : List P, (∀ p ∈ l, p ∈ A) → ∀ (k : ℕ) (ps : Fin k → P), (∀ i, ps i ∈ A) → ContDiff ℝ ∞ fun t : Fin k → ℝ => l.foldr (fun p w => deriv (fun r : ℝ => ρ (e p r) w) 0) (ρ (List.ofFn fun i => e (ps i) (t i)).prod v) := by
  intro G _ K _ _ _ ρ P A e v hv
  refine ⟨fun p hp k ps hps => ?_, fun m qs r hqs k ps hps => ?_, fun l hl k ps hps => ?_⟩
  · exact contDiff_prod_ofFn_apply_of_jointlySmooth
      (jointlySmooth_deriv_action (jointlySmooth_const' hv (E := ℝ)) hp) (g := fun _ => 0) contDiff_const ps hps
  · have h1 := jointlySmooth_prod_map_action (jointlySmooth_const' hv (E := ℝ))
      (List.ofFn fun i => (qs i, fun _ : ℝ => r i)) (by
        intro a ha
        rw [List.mem_ofFn] at ha
        obtain ⟨i, rfl⟩ := ha
        exact ⟨hqs i, contDiff_const⟩)
    simpa [List.map_ofFn, Function.comp_def] using
      contDiff_prod_ofFn_apply_of_jointlySmooth h1 (g := fun _ => 0) contDiff_const ps hps
  · have h1 := jointlySmooth_prod_map_action (jointlySmooth_const' hv (E := Fin k → ℝ))
      (List.ofFn fun i => (ps i, fun t : Fin k → ℝ => t i)) (by
        intro a ha
        rw [List.mem_ofFn] at ha
        obtain ⟨i, rfl⟩ := ha
        exact ⟨hps i, contDiff_apply ℝ (fun _ => ℝ) i⟩)
    have h2 := jointlySmooth_foldr_deriv_action h1 l hl (Fin k → ℝ) id contDiff_id [] (by simp)
    simpa [List.map_ofFn, Function.comp_def] using h2

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SpanImageInfOfLinearIndependent
section
open scoped TensorProduct

namespace GlobalTheory

theorem span_image_inf_of_linearIndependent {K V W ι : Type} [Field K] [AddCommGroup V]
    [Module K V] [AddCommGroup W] [Module ℂ W] [Finite ι] (σ : K →+* ℂ) (j : V →ₛₗ[σ] W)
    (b : Module.Basis ι K V) (hb : LinearIndependent ℂ (fun k => j (b k)))
    (U U' : Submodule K V) :
    Submodule.span ℂ (j '' (U : Set V)) ⊓ Submodule.span ℂ (j '' (U' : Set V)) =
      Submodule.span ℂ (j '' ((U ⊓ U' : Submodule K V) : Set V)) := by
  classical
  letI : Algebra K ℂ := σ.toAlgebra
  haveI := Fintype.ofFinite ι
  let B := Algebra.TensorProduct.basis ℂ b
  let J : ℂ ⊗[K] V →ₗ[ℂ] W := B.constr ℂ (fun k => j (b k))
  have hJb : ∀ k, J (1 ⊗ₜ b k) = j (b k) := fun k => by
    have := B.constr_basis ℂ (fun k => j (b k)) k
    rwa [Algebra.TensorProduct.basis_apply] at this
  have hJ : ∀ v, J (1 ⊗ₜ v) = j v := fun v => by
    set_option synthInstance.maxHeartbeats 100000 in
      rw [← b.sum_repr v, TensorProduct.tmul_sum, map_sum, map_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [TensorProduct.tmul_smul, map_smulₛₗ j, ← hJb, ← map_smul,
      ← algebraMap_smul ℂ (b.repr v k)]
    rfl
  have hinj : Function.Injective J := by
    apply Module.Basis.injective_constr_of_linearIndependent
    exact hb
  have key : ∀ A : Submodule K V,
      Submodule.span ℂ (j '' (A : Set V)) = (A.baseChange ℂ).map J := fun A => by
    rw [Submodule.baseChange_eq_span, Submodule.map_span, Submodule.map_coe, Set.image_image]
    congr 1
    exact Set.image_congr fun v _ => (hJ v).symm
  rw [key, key, key, baseChange_inf, Submodule.map_inf _ hinj]

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SquarePresentationOfCounitalComul
section
open scoped TensorProduct

namespace GlobalTheory

theorem square_presentation_counital_comul_of_finrank (p : ℕ) [Fact p.Prime] (k : Type) [Field k]
    [CharP k p] [PerfectRing k p] (n : ℕ) :
    ∀ (A : Type) [CommRing A] [Algebra k A] [Module.Finite k A] (ε : A →ₐ[k] k)
      (Δ : A →ₐ[k] A ⊗[k] A), Module.finrank k A = n →
      ((∀ a : A, TensorProduct.lid k A (LinearMap.rTensor A ε.toLinearMap (Δ a)) = a) ∧
        (∀ a : A, TensorProduct.rid k A (LinearMap.lTensor A ε.toLinearMap (Δ a)) = a)) →
      IsNilpotent (RingHom.ker ε) →
      (∃ (s : ℕ) (φ : MvPolynomial (Fin s) k →ₐ[k] A) (g : Fin s → MvPolynomial (Fin s) k),
        Function.Surjective φ ∧ RingHom.ker φ = Ideal.span (Set.range g)) := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro A _ _ _ ε Δ hn hΔ hε
  obtain ⟨d, x, l, hl, hlx, hadj⟩ := _root_.GlobalTheory.exists_generators_dual_point_derivations k A ε hε
  choose D hD using fun i => _root_.GlobalTheory.invariant_derivation_exists k A ε Δ hΔ (l i) (hl i)
  obtain ⟨E, hE⟩ := _root_.GlobalTheory.derivation_normalise_family k A ε hε d x D (fun i j => by rw [hD, hlx])
  have hnt : Nontrivial A := ε.toRingHom.domain_nontrivial
  rcases Nat.eq_zero_or_pos d with hd | hd
  · subst hd
    refine ⟨0, MvPolynomial.aeval x, fun _ => 0, ?_, ?_⟩
    · rw [← AlgHom.range_eq_top, ← Algebra.adjoin_range_eq_range_aeval, hadj]
    · rw [Set.range_eq_empty, Ideal.span_empty, ← RingHom.injective_iff_ker_eq_bot]
      intro f g h
      rw [MvPolynomial.eq_C_of_isEmpty f, MvPolynomial.eq_C_of_isEmpty g] at h ⊢
      simp only [MvPolynomial.aeval_C] at h
      rw [(algebraMap k A).injective h]
  · obtain ⟨B, hB, Δ', hΔ'⟩ := _root_.GlobalTheory.frobSubalgebra_counit p k A ε Δ hΔ
    have hp : (p : A) = 0 := by
      rw [← map_natCast (algebraMap k A), CharP.cast_eq_zero, map_zero]
    have hEB : ∀ i, ∀ b ∈ B, E i b = 0 := by
      intro i b hb
      obtain ⟨c, rfl⟩ := (hB b).1 hb
      rw [Derivation.leibniz_pow, nsmul_eq_mul, hp, zero_mul]
    have hBtop : B ≠ ⊤ := by
      intro h
      have h1 := hE ⟨0, hd⟩ ⟨0, hd⟩
      rw [hEB _ _ (h ▸ Algebra.mem_top), if_pos rfl] at h1
      exact zero_ne_one h1
    have hlt : Module.finrank k B < n := by
      rw [← hn]
      have : (Subalgebra.toSubmodule B) ≠ ⊤ := by
        intro h
        apply hBtop
        rw [← Algebra.toSubmodule_eq_top]
        exact h
      exact Submodule.finrank_lt this
    have hfin : Module.Finite k B :=
      Module.Finite.of_injective B.val.toLinearMap Subtype.val_injective
    have hε' : IsNilpotent (RingHom.ker (ε.comp B.val)) := by
      obtain ⟨m, hm⟩ := hε
      refine ⟨m, ?_⟩
      have h1 : (RingHom.ker (ε.comp B.val)) = Ideal.comap B.val (RingHom.ker ε) := by
        ext b; simp [RingHom.mem_ker, Ideal.mem_comap]
      rw [h1, Ideal.zero_eq_bot, eq_bot_iff]
      refine (Ideal.le_comap_pow _ m).trans ?_
      rw [hm, Ideal.zero_eq_bot]
      intro b hb
      rw [Ideal.mem_comap, Ideal.mem_bot] at hb
      rw [Ideal.mem_bot]
      exact Subtype.ext hb
    refine _root_.GlobalTheory.SquareTower.tower k B A (ih _ hlt B (ε.comp B.val) Δ' rfl hΔ' hε') ?_
    refine ⟨d, MvPolynomial.aeval x, _, ?_,
      _root_.GlobalTheory.ker_aeval_truncated p (Fact.out : p.Prime).pos B A d x
        (fun i => ⟨x i ^ p, (hB _).2 ⟨x i, rfl⟩⟩) (fun i => rfl)
        (_root_.GlobalTheory.truncMono_linearIndependent p k A d x E hE B hEB)⟩
    rw [← AlgHom.range_eq_top, ← Algebra.adjoin_range_eq_range_aeval, eq_top_iff]
    intro a _
    have ha : a ∈ Algebra.adjoin k (Set.range x) := hadj ▸ Algebra.mem_top
    have hle : Algebra.adjoin k (Set.range x) ≤
        (Algebra.adjoin B (Set.range x)).restrictScalars k :=
      Algebra.adjoin_le Algebra.subset_adjoin
    exact hle ha

theorem square_presentation_of_counital_comul : ∀ (p : ℕ) [Fact p.Prime] (k A : Type) [Field k] [CommRing A] [Algebra k A] [CharP k p] [PerfectRing k p] [Module.Finite k A] (ε : A →ₐ[k] k) (Δ : A →ₐ[k] A ⊗[k] A), ((∀ a : A, TensorProduct.lid k A (LinearMap.rTensor A ε.toLinearMap (Δ a)) = a) ∧ (∀ a : A, TensorProduct.rid k A (LinearMap.lTensor A ε.toLinearMap (Δ a)) = a)) → IsNilpotent (RingHom.ker ε) → (∃ (s : ℕ) (φ : MvPolynomial (Fin s) k →ₐ[k] A) (g : Fin s → MvPolynomial (Fin s) k), Function.Surjective φ ∧ RingHom.ker φ = Ideal.span (Set.range g)) := by
  intro p _ k A _ _ _ _ _ _ ε Δ h hε
  exact square_presentation_counital_comul_of_finrank p k _ A ε Δ rfl h hε

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.StProfileHolds
section
noncomputable section

open MvPolynomial
open scoped ContDiff

namespace GlobalTheory.PsCo.Pc1

theorem stProfile_holds : StProfile := by
  intro N
  induction N with
  | zero =>
    refine ⟨fun x => expNegInvGlue (1 - x), ?_, ?_, ?_, ?_⟩
    · exact expNegInvGlue.contDiff.comp (contDiff_const.sub contDiff_id)
    · intro x hx
      exact expNegInvGlue.zero_of_nonpos (by linarith)
    · intro x
      simpa using expNegInvGlue.nonneg _
    · simpa using expNegInvGlue.pos_of_pos (x := 1) one_pos
  | succ N ih =>
    obtain ⟨G, h1, h2, h3, h4⟩ := ih
    have hc : Continuous G := h1.continuous
    have hd : deriv (fun x => ∫ s in (1:ℝ)..x, G s) = G := by
      funext x
      exact (hc.deriv_integral G 1 x)
    refine ⟨fun x => ∫ s in (1:ℝ)..x, G s, ?_, ?_, ?_, ?_⟩
    · rw [contDiff_infty_iff_deriv, hd]
      exact ⟨fun x => (intervalIntegral.integral_hasDerivAt_right (hc.intervalIntegrable _ _)
        (hc.stronglyMeasurableAtFilter _ _) hc.continuousAt).differentiableAt, h1⟩
    · intro x hx
      have : ∫ s in (1:ℝ)..x, G s = ∫ s in (1:ℝ)..x, (0:ℝ) := by
        apply intervalIntegral.integral_congr
        intro s hs
        rw [Set.uIcc_of_le hx] at hs
        exact h2 s hs.1
      simpa using this
    · intro x
      rw [iteratedDeriv_succ', hd]
      exact h3 x
    · rw [iteratedDeriv_succ', hd]
      exact h4

end GlobalTheory.PsCo.Pc1
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TC
section
noncomputable section

open GlobalTheory.LKTrip
open scoped TensorProduct

namespace GlobalTheory.TorCls

def TC (D : Type) [Ring D] [Algebra ℚ D] (σ : D →+* Dᵐᵒᵖ) (β y : D) (R : Type) [CommRing R] [Algebra ℚ R]
    (z : (R ⊗[ℚ] D)ˣ × Rˣ) : Prop :=
  (z.1 : R ⊗[ℚ] D) * ((1 : R) ⊗ₜ β) * (starT σ R (z.1 : R ⊗[ℚ] D)).unop =
      algebraMap R (R ⊗[ℚ] D) (z.2 : R) * ((1 : R) ⊗ₜ β) ∧
    Commute (z.1 : R ⊗[ℚ] D) ((1 : R) ⊗ₜ y)

end GlobalTheory.TorCls
end
end

