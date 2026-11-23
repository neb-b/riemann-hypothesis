module

public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.TensorRepresentations.TraceFormula
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.TensorRepresentations.UnitarizeC
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.TensorRepresentations.Bundle0001

@[expose] public section

-- bundled from ReciprocityTheory.ReductiveGroups.DiscreteSeries.TensorRepresentations.FmFormBAddLeft
section
set_option autoImplicit false

noncomputable section

open Finset Matrix

namespace ReciprocityTheory.ChartRestriction.DS

variable {n : ℕ}

section
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] {D : Submodule ℂ H} {ε : Fin n → Bool}

theorem fm_sgn_star (c : Fin n) : starRingEnd ℂ (if ε c then (1 : ℂ) else -1) = if ε c then 1 else -1 := by
  split_ifs <;> simp

theorem fm_formB_add_left (f f' g : Fin n → D) : formB ε (f + f') g = formB ε f g + formB ε f' g := by
  delta formB
  simp only [Pi.add_apply, Submodule.coe_add, inner_add_left, mul_add, sum_add_distrib]

theorem fm_sum_ite_left (w : Fin n → ℂ) (a : Fin n) (x : D) (G : Fin n → D) :
    ∑ c, w c * inner ℂ (((if c = a then x else 0 : D)) : H) ((G c : D) : H) = w a * inner ℂ (x : H) ((G a : D) : H) := by
  rw [Finset.sum_eq_single a (fun c _ hc => by rw [ite_eq_right hc]; simp)
    (fun h => absurd (Finset.mem_univ a) h), ite_eq_left rfl]

theorem fm_formB_tensF (dual : Bool) {E : Fin n → Fin n → Module.End ℂ D} (hU : IsInfUnitary ε E) (a b : Fin n)
    (f g : Fin n → D) :
    formB ε (tensF dual E a b f) g = adjSign ε a b * formB ε f (tensF dual E b a g) := by
  have hU' : ∀ (x y : D), inner ℂ ((E a b x : D) : H) (y : H) = adjSign ε a b * inner ℂ (x : H) ((E b a y : D) : H) := by
    intro x y; simpa only [Submodule.coe_inner] using hU a b x y
  delta formB tensF
  cases dual
  · simp only [Bool.cond_false, tensV_coord, Submodule.coe_add, inner_add_left, inner_add_right, hU',
      mul_add, sum_add_distrib, mul_sum]
    have h2 : ∑ i, adjSign ε a b * ((if ε i then (1 : ℂ) else -1) * inner ℂ ((f i : D) : H)
        (((if i = b then g a else 0 : D)) : H)) = adjSign ε a b * ((if ε b then (1 : ℂ) else -1) *
          inner ℂ ((f b : D) : H) ((g a : D) : H)) := by
      rw [Finset.sum_eq_single b (fun c _ hc => by rw [ite_eq_right hc]; simp)
        (fun h => absurd (Finset.mem_univ b) h), ite_eq_left rfl]
    rw [h2, fm_sum_ite_left, ← tfa_sign ε a b]
    congr 1
    · exact sum_congr rfl fun c _ => by ring
    · ring
  · simp only [Bool.cond_true, tensVd_coord, Submodule.coe_sub, inner_sub_left, inner_sub_right, hU',
      mul_sub, sum_sub_distrib, mul_sum]
    have h2 : ∑ i, adjSign ε a b * ((if ε i then (1 : ℂ) else -1) * inner ℂ ((f i : D) : H)
        (((if i = a then g b else 0 : D)) : H)) = adjSign ε a b * ((if ε a then (1 : ℂ) else -1) *
          inner ℂ ((f a : D) : H) ((g b : D) : H)) := by
      rw [Finset.sum_eq_single a (fun c _ hc => by rw [ite_eq_right hc]; simp)
        (fun h => absurd (Finset.mem_univ a) h), ite_eq_left rfl]
    rw [h2, fm_sum_ite_left, ← tfa_sign' ε b a]
    congr 1
    · exact sum_congr rfl fun c _ => by ring
    · ring

end

section
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] {ε : Fin n → Bool}

theorem fm_kset_uj {k : Matrix (Fin n) (Fin n) ℂ} (hk : k ∈ Kset ε) : k ∈ UJset ε := by
  obtain ⟨h1, -⟩ := rq_K_unit hk
  show kᴴ * Jm ε * k = Jm ε
  rw [Matrix.mul_assoc, ← hk.2, ← Matrix.mul_assoc, h1, Matrix.one_mul]

theorem fm_JJ {k : Matrix (Fin n) (Fin n) ℂ} (hk : k ∈ Kset ε) (d e : Fin n) :
    ∑ c, (if ε c then (1 : ℂ) else -1) * (star (k c d) * k c e) = if d = e then (if ε d then (1 : ℂ) else -1) else 0 := by
  have h := congrFun (congrFun (fm_kset_uj hk : kᴴ * Jm ε * k = Jm ε) d) e
  rw [Matrix.mul_apply] at h
  delta Jm at h
  simp only [Matrix.mul_diagonal, Matrix.conjTranspose_apply, Matrix.diagonal_apply] at h
  rw [← h]
  refine sum_congr rfl fun c _ => ?_
  simp only [RCLike.star_def]
  ring

theorem fm_formBH_kDiag (dual : Bool) {σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)} (hσ : IsURepOn (UJset ε) σ)
    {k : Matrix (Fin n) (Fin n) ℂ} (hk : k ∈ Kset ε) (F G : Fin n → H) :
    ∑ c, (if ε c then (1 : ℂ) else -1) * inner ℂ (kDiag dual σ k F c) (kDiag dual σ k G c) =
      ∑ c, (if ε c then (1 : ℂ) else -1) * inner ℂ (F c) (G c) := by
  have hin : ∀ u v : H, inner ℂ (σ k u) (σ k v) = inner ℂ u v := fun u v =>
    UnitB.sig_inner hσ (UnitB.toG k (fm_kset_uj hk)) u v
  set m : Fin n → Fin n → ℂ := fun c d => cond dual (star (k c d)) (k c d) with hm
  have hJ : ∀ d e, ∑ c, (if ε c then (1 : ℂ) else -1) * (star (m c d) * m c e) =
      if d = e then (if ε d then (1 : ℂ) else -1) else 0 := by
    intro d e
    cases dual
    · exact fm_JJ hk d e
    · have h := congrArg star (fm_JJ hk d e)
      rw [star_sum] at h
      have h2 : star (if d = e then (if ε d then (1 : ℂ) else -1) else 0) = if d = e then (if ε d then (1 : ℂ) else -1) else 0 := by
        split_ifs <;> simp
      rw [h2] at h
      rw [← h]
      refine sum_congr rfl fun c _ => ?_
      simp only [hm, Bool.cond_true, star_mul, star_star]
      split_ifs <;> simp [mul_comm]
  have hk1 : ∀ (F : Fin n → H) c, kDiag dual σ k F c = ∑ d, m c d • σ k (F d) := fun F c => rfl
  simp only [hk1, sum_inner, inner_sum, inner_smul_left, inner_smul_right, hin, mul_sum]
  have key : ∀ X : Fin n → Fin n → Fin n → ℂ, ∑ c, ∑ e, ∑ d, X c e d = ∑ d, ∑ e, ∑ c, X c e d := by
    intro X
    rw [show (∑ c, ∑ e, ∑ d, X c e d) = ∑ c, ∑ d, ∑ e, X c e d from sum_congr rfl fun c _ => sum_comm, sum_comm]
    exact sum_congr rfl fun d _ => sum_comm
  refine (key _).trans ?_
  calc _ = ∑ d, ∑ e, (if d = e then (if ε d then (1 : ℂ) else -1) else 0) * inner ℂ (F d) (G e) := by
        refine sum_congr rfl fun d _ => sum_congr rfl fun e _ => ?_
        rw [← hJ d e, sum_mul]
        refine sum_congr rfl fun c _ => ?_
        simp only [RCLike.star_def]; ring
    _ = _ := by simp only [ite_mul, zero_mul, sum_ite_eq, mem_univ, ite_true]

end

end ReciprocityTheory.ChartRestriction.DS
end
end

-- bundled from ReciprocityTheory.ReductiveGroups.DiscreteSeries.TensorRepresentations.PoleMatchA
section
noncomputable section

open Finset

namespace ReciprocityTheory.ChartRestriction.DS

variable {n : ℕ}

open MeasureTheory

section Generic

variable {W : Type*} [AddCommGroup W] [Module ℂ W]

theorem pm_pow_eig (A : Module.End ℂ W) {z : ℂ} {f : W} (h : A f = z • f) (k : ℕ) :
    (A ^ k) f = z ^ k • f := by
  induction k with
  | zero => simp
  | succ k ih => rw [pow_succ', mul_apply_eq_comp, ih, map_smul, h, smul_smul, pow_succ]

theorem pm_proj_decomp (A Q : Module.End ℂ W) (T : Submodule ℂ W) (B : Finset ℝ) (z : ℂ)
    (hQ1 : ∀ f ∈ T, A f = z • f → Q f = f) (hQ0 : ∀ f ∈ T, ∀ z' : ℂ, z' ≠ z → A f = z' • f → Q f = 0)
    (fb : ℝ → W) (hfb : ∀ b, fb b ∈ T ∧ A (fb b) = ((b : ℝ) : ℂ) • fb b) :
    Q (∑ b ∈ B, fb b) = ∑ b ∈ B, if ((b : ℝ) : ℂ) = z then fb b else 0 := by
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sum]
  refine Finset.sum_congr rfl fun b _ => ?_
  split_ifs with h
  · exact hQ1 _ (hfb b).1 (by rw [← h]; exact (hfb b).2)
  · exact hQ0 _ (hfb b).1 _ h (hfb b).2

theorem pm_agree (A : Module.End ℂ W) (T : Submodule ℂ W) (B : Finset ℝ)
    (hdec : ∀ f ∈ T, ∃ fb : ℝ → W, (∀ b, fb b ∈ T ∧ A (fb b) = ((b : ℝ) : ℂ) • fb b) ∧ f = ∑ b ∈ B, fb b)
    (P : ℝ → Module.End ℂ W)
    (hP1 : ∀ b, ∀ f ∈ T, A f = ((b : ℝ) : ℂ) • f → P b f = f)
    (hP0 : ∀ b, ∀ f ∈ T, ∀ z' : ℂ, z' ≠ ((b : ℝ) : ℂ) → A f = z' • f → P b f = 0) :
    (∀ f ∈ T, ∀ k : ℕ, (A ^ k) f = ∑ b ∈ B, ((b : ℝ) : ℂ) ^ k • P b f) ∧
      ∀ (Q : Module.End ℂ W) (z : ℂ), (∀ f ∈ T, A f = z • f → Q f = f) →
        (∀ f ∈ T, ∀ z' : ℂ, z' ≠ z → A f = z' • f → Q f = 0) →
        ∀ f ∈ T, Q f = ∑ b ∈ B, if ((b : ℝ) : ℂ) = z then P b f else 0 := by
  have hPb : ∀ fb : ℝ → W, (∀ b, fb b ∈ T ∧ A (fb b) = ((b : ℝ) : ℂ) • fb b) →
      ∀ b ∈ B, P b (∑ b' ∈ B, fb b') = fb b := by
    intro fb hfb b hb
    rw [pm_proj_decomp A (P b) T B _ (hP1 b) (hP0 b) fb hfb]
    simp [Complex.ofReal_inj, hb]
  refine ⟨fun f hf k => ?_, fun Q z hQ1 hQ0 f hf => ?_⟩
  · obtain ⟨fb, hfb, rfl⟩ := hdec f hf
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum]
    refine Finset.sum_congr rfl fun b hb => ?_
    rw [hPb fb hfb b hb, pm_pow_eig A (hfb b).2]
  · obtain ⟨fb, hfb, rfl⟩ := hdec f hf
    rw [pm_proj_decomp A Q T B z hQ1 hQ0 fb hfb]
    refine Finset.sum_congr rfl fun b hb => ?_
    rw [hPb fb hfb b hb]

end Generic

theorem pm_single_mem {M : Type*} [AddCommGroup M] [Module ℂ M] (S : Submodule ℂ M) {x : M} (hx : x ∈ S)
    (c : Fin n) : Pi.single c x ∈ tensSub (n := n) S := by
  refine tset_mem.2 fun i => ?_
  by_cases h : i = c <;> simp [h, hx]

theorem pm_ptr {M : Type*} [AddCommGroup M] [Module ℂ M] (S : Submodule ℂ M)
    (Q : Module.End ℂ (Fin n → M)) (R : ℝ → Module.End ℂ (Fin n → M)) (B : Finset ℝ) (g : ℝ → ℂ)
    (hQ : ∀ f ∈ tensSub S, Q f = ∑ b ∈ B, g b • R b f) {x : M} (hx : x ∈ S) :
    ptr Q x = ∑ b ∈ B, g b • ptr (R b) x := by
  simp only [ptr_apply, hQ _ (pm_single_mem S hx _), Finset.sum_apply, Pi.smul_apply, Finset.smul_sum]
  exact Finset.sum_comm

theorem pm_resid (dual : Bool) (lam : Fin n → ℝ) (s : Fin n) :
    resid (poleF dual lam) s = ((ratioF dual lam s : ℝ) : ℂ) := by
  cases dual
  · exact resid_poleV lam s
  · exact resid_poleVd lam s

theorem pm_pole_inj (dual : Bool) {lam : Fin n → ℝ} (hl : StrictAnti lam) : Function.Injective (poleF dual lam) := by
  cases dual
  · exact poleV_injective hl.injective
  · exact poleVd_injective hl.injective

theorem pm_char (dual : Bool) {M : Type*} [AddCommGroup M] [Module ℂ M] {E : Fin n → Fin n → Module.End ℂ M}
    {lam : Fin n → ℝ} {S : Submodule ℂ M} (hS : HasGelfandChar E lam S) (k : ℕ) (x : M) (hx : x ∈ S) :
    ptr (eeF dual E ^ k) x = PowerSeries.coeff (k + 1) (resSeries (poleF dual lam)) • x := by
  cases dual
  · exact ptr_eeV_pow_char hS k x hx
  · exact ptr_eeVd_pow_char hS k x hx

theorem pm_core (dual : Bool) {lam : Fin n → ℝ} {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] {ε : Fin n → Bool}
    {σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)} {D : Submodule ℂ H} {E : Fin n → Fin n → Module.End ℂ D}
    (hσ : IsURepOn (UJset ε) σ) (hD : IsDerivedOn ε σ D E) (hsm : ∀ v : D, IsSmoothVecU ε σ v)
    {V : Submodule ℂ D} (hgap : StdGap ε lam) (hV : IsKIrrHW ε E (lowK ε lam) V)
    (hc : ∀ v ∈ V, casimir E v = (casVal lam : ℂ) • v)
    (hVK : ∀ k ∈ Kset ε, ∀ v ∈ V, ∃ w ∈ V, (w : H) = σ k v) (hW : ∀ v ∈ genSub E V, ∀ w ∈ genSub E V, MemLp (fun g : Formalism.REAL.UJ ε =>
      ((Real.sqrt (S7.hs (Formalism.MainNotions.S.umat g)) : ℝ) : ℂ) * inner ℂ ((w : D) : H) (σ (Formalism.MainNotions.S.umat g) ((v : D) : H)))
      2 (Formalism.REAL.muG ε)) (hG : HasGelfandChar E lam (genSub E V)) :
    ∃ B : Finset ℝ, ∃ c : ℝ → ℂ, ∃ P : ℝ → Module.End ℂ (Fin n → D),
      (∀ z : ℂ, ∀ f ∈ tensSub (genSub E V), f ≠ 0 → eeF dual E f = z • f → ∃ b ∈ B, z = ((b : ℝ) : ℂ)) ∧
      (∀ b, ∀ f ∈ tensSub (genSub E V), P b f ∈ tensSub (genSub E V)) ∧
      (∀ b, ∀ f ∈ tensSub (genSub E V), eeF dual E (P b f) = ((b : ℝ) : ℂ) • P b f) ∧
      (∀ b, ∀ f ∈ tensSub (genSub E V), eeF dual E f = ((b : ℝ) : ℂ) • f → P b f = f) ∧
      (∀ b, ∀ x ∈ genSub E V, ptr (P b) x = c b • x) ∧
      (∀ b, c b = 0 → ∀ f ∈ tensSub (genSub E V), P b f = 0) ∧
      (∀ (Q : Module.End ℂ (Fin n → D)) (z : ℂ), (∀ f ∈ tensSub (genSub E V), eeF dual E f = z • f → Q f = f) →
        (∀ f ∈ tensSub (genSub E V), ∀ z' : ℂ, z' ≠ z → eeF dual E f = z' • f → Q f = 0) →
        ∀ x ∈ genSub E V, ptr Q x = (∑ b ∈ B, if ((b : ℝ) : ℂ) = z then c b else 0) • x) ∧
      (∀ p : ℂ, (∑ b ∈ B, if ((b : ℝ) : ℂ) = p then c b else 0) =
        ∑ s ∈ univ.filter (fun s => poleF dual lam s = p), ((ratioF dual lam s : ℝ) : ℂ)) ∧
      ∃ x₀ ∈ genSub E V, x₀ ≠ 0 := by
  obtain ⟨B, hdec, hev⟩ := ee_decomp dual hσ hD hgap hV hc hVK hW
  have hPex := fun b : ℝ => eigenProj_exists dual hσ hD hgap hV hc hVK hW ((b : ℝ) : ℂ)
  choose P hPG hPP hPz hP1 hP0 using hPex
  have hsc := fun b => ptr_scalar dual hσ hD hgap hV hc hVK (hPG b)
  choose c hcb using hsc
  have hPB := fun b => eigenProj_formB dual hσ hD hgap hV hc hVK hW _ (hPG b).1 (hPz b) (hP1 b) (hP0 b)
  have htr := fun b => trace_nonneg dual hσ hD hsm hgap hV hc hVK hW (hPG b) (hPP b) (hPB b) (hPz b) (hcb b)
  obtain ⟨hpow, hagr⟩ := pm_agree (eeF dual E) (tensSub (genSub E V)) B hdec P hP1 hP0
  have hQ : ∀ (Q : Module.End ℂ (Fin n → D)) (z : ℂ),
      (∀ f ∈ tensSub (genSub E V), eeF dual E f = z • f → Q f = f) →
      (∀ f ∈ tensSub (genSub E V), ∀ z' : ℂ, z' ≠ z → eeF dual E f = z' • f → Q f = 0) →
      ∀ x ∈ genSub E V, ptr Q x = (∑ b ∈ B, if ((b : ℝ) : ℂ) = z then c b else 0) • x := by
    intro Q z hQ1 hQ0 x hx
    rw [pm_ptr (genSub E V) Q P B (fun b => if ((b : ℝ) : ℂ) = z then 1 else 0)
      (fun f hf => by
        rw [hagr Q z hQ1 hQ0 f hf]
        exact sum_congr rfl fun b _ => by split_ifs <;> simp) hx, Finset.sum_smul]
    refine sum_congr rfl fun b _ => ?_
    rw [hcb b x hx]
    split_ifs <;> simp
  have hVle : V ≤ genSub E V := by
    unfold genSub
    exact le_sInf fun T hT => hT.1
  obtain ⟨x₀, hx₀V, hx₀0, -⟩ := hV.2.2.2
  have hx₀ : x₀ ∈ genSub E V := hVle hx₀V
  have hmom : ∀ k : ℕ, ∑ i : B, c i * ((i : ℝ) : ℂ) ^ k =
      ∑ s, resid (poleF dual lam) s * poleF dual lam s ^ k := by
    intro k
    rw [Finset.sum_coe_sort B (fun b => c b * ((b : ℝ) : ℂ) ^ k), ← resSeries_coeff_succ (pm_pole_inj dual hgap.1) k]
    apply smul_left_injective ℂ hx₀0
    beta_reduce
    rw [← pm_char dual hG k x₀ hx₀, pm_ptr (genSub E V) _ P B (fun b => ((b : ℝ) : ℂ) ^ k)
      (fun f hf => hpow f hf k) hx₀, Finset.sum_smul]
    refine sum_congr rfl fun b _ => ?_
    rw [hcb b x₀ hx₀, smul_smul, mul_comm (c b)]
  refine ⟨B, c, P, hev, fun b => (hPG b).1, hPz, hP1, hcb, fun b h0 => (htr b).2.2 h0, hQ, fun p => ?_,
    x₀, hx₀, hx₀0⟩
  have hf := moment_fibre (fun i : B => ((i : ℝ) : ℂ)) (fun i => c i) (poleF dual lam) (resid (poleF dual lam)) hmom p
  rw [Finset.sum_filter, Finset.sum_coe_sort B (fun b => if ((b : ℝ) : ℂ) = p then c b else 0)] at hf
  rw [hf]
  exact sum_congr rfl fun s _ => pm_resid dual lam s

theorem pm_filter_pole (dual : Bool) {lam : Fin n → ℝ} (hl : StrictAnti lam) (s : Fin n) :
    univ.filter (fun s' => poleF dual lam s' = poleF dual lam s) = {s} := by
  ext t
  simp [(pm_pole_inj dual hl).eq_iff]

theorem pm_sum_single {B : Finset ℝ} {b : ℝ} (hb : b ∈ B) (c : ℝ → ℂ) :
    (∑ b' ∈ B, if ((b' : ℝ) : ℂ) = ((b : ℝ) : ℂ) then c b' else 0) = c b := by
  simp [Complex.ofReal_inj, hb]

end ReciprocityTheory.ChartRestriction.DS
end
end

