module

public import Mathlib
public import Formalism.SharpRestriction.Divisibility.SchurIrreducible
public import Formalism.LocalToGlobal.BesselHermitianTheta.Bundle0001
public import Formalism.SharpRestriction.GlobalSchurBounds.StandardLatticesGL3
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0003

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.InnerCoeffEqOfIsometricAnalyticModules
section
open Formalism.BasicNotions.TH Formalism.MainNotions.SchurIrreducible

namespace GlobalTheory.AnalyticVec

theorem map_flow_eq_zero {V E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
    (ι : V → E) (a : V → V) (U : ℝ → E →L[ℝ] E) (h0 : U 0 = 1) (hadd : ∀ s t, U (s + t) = U s * U t)
    (hder : ∀ v, HasDerivAt (fun t : ℝ => U t (ι v)) (ι (a v)) 0)
    (han : ∀ v, AnalyticOnNhd ℝ (fun t : ℝ => U t (ι v)) Set.univ)
    (L : E →L[ℝ] F) (hL : ∀ v, L (ι v) = 0) (v : V) (t : ℝ) : L (U t (ι v)) = 0 := by
  have hd : ∀ w s, HasDerivAt (fun r : ℝ => U r (ι w)) (U s (ι (a w))) s := by
    intro w s
    have e : (fun r : ℝ => U r (ι w)) = fun r => U s (U (r - s) (ι w)) := by
      funext r
      have hr : r = s + (r - s) := by ring
      conv_lhs => rw [hr]
      rw [hadd, ContinuousLinearMap.mul_apply]
    rw [e]
    have hs : HasDerivAt (fun r : ℝ => r - s) 1 s := (hasDerivAt_id s).sub_const s
    have hz : HasDerivAt (fun r : ℝ => U r (ι w)) (ι (a w)) ((fun r : ℝ => r - s) s) := by
      simpa using hder w
    have h2 : HasDerivAt ((fun r : ℝ => U r (ι w)) ∘ (fun r : ℝ => r - s)) ((1 : ℝ) • ι (a w)) s :=
      HasDerivAt.scomp s hz hs
    rw [one_smul] at h2
    exact (U s).hasFDerivAt.comp_hasDerivAt s h2
  have hit : ∀ n w, deriv^[n] (fun r : ℝ => L (U r (ι w))) = fun r => L (U r (ι (a^[n] w))) := by
    intro n
    induction n with
    | zero => intro w; rfl
    | succ n ih =>
      intro w
      rw [Function.iterate_succ_apply]
      have hD : deriv (fun r : ℝ => L (U r (ι w))) = fun r => L (U r (ι (a w))) := by
        funext r
        exact (L.hasFDerivAt.comp_hasDerivAt r (hd w r)).deriv
      rw [hD, ih (a w), Function.iterate_succ_apply]
  have hf : AnalyticOnNhd ℝ (fun r : ℝ => L (U r (ι v))) Set.univ :=
    fun r _ => (L.analyticAt _).comp (han v r (Set.mem_univ r))
  obtain ⟨p, hp⟩ := hf 0 (Set.mem_univ 0)
  have hc : ∀ n, p.coeff n = 0 := by
    intro n
    obtain ⟨ρ, hpr⟩ := hp
    have h1 := hpr.factorial_smul 1 n
    rw [← iteratedDeriv_eq_iteratedFDeriv, iteratedDeriv_eq_iterate, hit n v] at h1
    dsimp only at h1
    rw [h0, ContinuousLinearMap.one_apply, hL] at h1
    have h2 : ((n.factorial : ℝ)) • p.coeff n = 0 := by
      rw [Nat.cast_smul_eq_nsmul ℝ]
      exact h1
    exact (smul_eq_zero.mp h2).resolve_left (by exact_mod_cast n.factorial_ne_zero)
  have hp0 : p = 0 := by
    ext n y
    rw [p.apply_eq_prod_smul_coeff, hc n, smul_zero]
    rfl
  rw [hp0] at hp
  have hev : (fun r : ℝ => L (U r (ι v))) =ᶠ[nhds 0] 0 := HasFPowerSeriesAt.eventually_eq_zero hp
  have := hf.eqOn_zero_of_preconnected_of_eventuallyEq_zero isPreconnected_univ (Set.mem_univ 0) hev
    (Set.mem_univ t)
  simpa using this

private theorem eventually_abs_le_half_add_of_doubling_bounds {p q : ℕ} (T : GrpData p q) (π₁ π₂ : URep T) (M : GKMod p q)
    (j₁ : M.V →ₗ[ℂ] π₁.H) (j₂ : M.V →ₗ[ℂ] π₂.H) (Y : Mat p q) (hY : Y ∈ upq p q)
    (hd1 : ∀ x, HasDerivAt (fun t : ℝ => π₁.π (T.expt (t • Y)) (j₁ x)) (j₁ (M.act Y x)) 0)
    (hd2 : ∀ x, HasDerivAt (fun t : ℝ => π₂.π (T.expt (t • Y)) (j₂ x)) (j₂ (M.act Y x)) 0)
    (ha1 : ∀ x, AnalyticOnNhd ℝ (fun t : ℝ => π₁.π (T.expt (t • Y)) (j₁ x)) Set.univ)
    (ha2 : ∀ x, AnalyticOnNhd ℝ (fun t : ℝ => π₂.π (T.expt (t • Y)) (j₂ x)) Set.univ)
    (h : T.G) (hh : ∀ x y, inner ℂ (j₁ x) (π₁.π h (j₁ y)) = inner ℂ (j₂ x) (π₂.π h (j₂ y)))
    (t : ℝ) : ∀ x y, inner ℂ (j₁ x) (π₁.π (h * T.expt (t • Y)) (j₁ y)) =
      inner ℂ (j₂ x) (π₂.π (h * T.expt (t • Y)) (j₂ y)) := by
  intro x y
  let U : ℝ → (π₁.H × π₂.H) →L[ℝ] (π₁.H × π₂.H) := fun s =>
    ((π₁.π (T.expt (s • Y))).restrictScalars ℝ).prodMap ((π₂.π (T.expt (s • Y))).restrictScalars ℝ)
  let L : (π₁.H × π₂.H) →L[ℝ] ℂ :=
    (((innerSL ℂ (j₁ x)).comp (π₁.π h)).restrictScalars ℝ).comp (ContinuousLinearMap.fst ℝ _ _) -
    (((innerSL ℂ (j₂ x)).comp (π₂.π h)).restrictScalars ℝ).comp (ContinuousLinearMap.snd ℝ _ _)
  have key := map_flow_eq_zero (fun v => (j₁ v, j₂ v)) (M.act Y) U ?_ ?_ ?_ ?_ L ?_ y t
  · have e : L (U t (j₁ y, j₂ y)) = inner ℂ (j₁ x) (π₁.π (h * T.expt (t • Y)) (j₁ y)) -
        inner ℂ (j₂ x) (π₂.π (h * T.expt (t • Y)) (j₂ y)) := by
      simp [L, U, map_mul]
    rw [e, sub_eq_zero] at key
    exact key
  · refine ContinuousLinearMap.ext fun z => ?_
    simp [U, T.expt_zero]
  · intro s r
    refine ContinuousLinearMap.ext fun z => ?_
    simp [U, T.expt_add Y hY, map_mul]
    rfl
  · intro v
    exact (hd1 v).prodMk (hd2 v)
  · intro v
    exact (ha1 v).prod (ha2 v)
  · intro v
    simp [L, hh]

theorem inner_apply_eq_of_analytic : ∀ (p q : ℕ) (T : GrpData p q), Subgroup.closure (T.expt '' upq p q) = ⊤ → ∀ (π₁ π₂ : URep T) (M : GKMod p q) (j₁ : M.V →ₗ[ℂ] π₁.H) (j₂ : M.V →ₗ[ℂ] π₂.H), (∀ Y ∈ upq p q, ∀ x, HasDerivAt (fun t : ℝ => π₁.π (T.expt (t • Y)) (j₁ x)) (j₁ (M.act Y x)) 0) → (∀ Y ∈ upq p q, ∀ x, HasDerivAt (fun t : ℝ => π₂.π (T.expt (t • Y)) (j₂ x)) (j₂ (M.act Y x)) 0) → (∀ Y ∈ upq p q, ∀ x, AnalyticOnNhd ℝ (fun t : ℝ => π₁.π (T.expt (t • Y)) (j₁ x)) Set.univ) → (∀ Y ∈ upq p q, ∀ x, AnalyticOnNhd ℝ (fun t : ℝ => π₂.π (T.expt (t • Y)) (j₂ x)) Set.univ) → (∀ x y, inner ℂ (j₁ x) (j₁ y) = inner ℂ (j₂ x) (j₂ y)) → ∀ g x y, inner ℂ (j₁ x) (π₁.π g (j₁ y)) = inner ℂ (j₂ x) (π₂.π g (j₂ y)) := by
  intro p q T hT π₁ π₂ M j₁ j₂ hd1 hd2 ha1 ha2 hiso
  let Q : T.G → Prop := fun h => ∀ x y, inner ℂ (j₁ x) (π₁.π h (j₁ y)) = inner ℂ (j₂ x) (π₂.π h (j₂ y))
  let S : Subgroup T.G :=
    { carrier := {g | ∀ h, Q h ↔ Q (h * g)}
      mul_mem' := fun {a b} ha hb h => (ha h).trans (by rw [hb (h * a), mul_assoc])
      one_mem' := fun h => by rw [mul_one]
      inv_mem' := fun {g} hg h => by
        have e := hg (h * g⁻¹)
        rw [inv_mul_cancel_right] at e
        exact e.symm }
  have hle : Subgroup.closure (T.expt '' upq p q) ≤ S := by
    rw [Subgroup.closure_le]
    rintro _ ⟨Y, hY, rfl⟩ h
    have e : T.expt Y * T.expt ((-1 : ℝ) • Y) = 1 := by
      have e1 := T.expt_add Y hY 1 (-1)
      rw [one_smul, show (1 : ℝ) + -1 = 0 by norm_num, zero_smul, T.expt_zero] at e1
      exact e1.symm
    constructor
    · intro hh
      have h2 := eventually_abs_le_half_add_of_doubling_bounds T π₁ π₂ M j₁ j₂ Y hY (hd1 Y hY) (hd2 Y hY) (ha1 Y hY) (ha2 Y hY) h hh 1
      rw [one_smul] at h2
      exact h2
    · intro hh
      have h2 := eventually_abs_le_half_add_of_doubling_bounds T π₁ π₂ M j₁ j₂ Y hY (hd1 Y hY) (hd2 Y hY) (ha1 Y hY) (ha2 Y hY)
        (h * T.expt Y) hh (-1)
      rw [mul_assoc, e, mul_one] at h2
      exact h2
  have q1 : Q 1 := by
    intro x y
    rw [map_one, map_one, ContinuousLinearMap.one_apply, ContinuousLinearMap.one_apply]
    exact hiso x y
  intro g
  have hg : g ∈ S := hle (by rw [hT]; exact Subgroup.mem_top g)
  have q2 := (hg 1).mp q1
  rw [one_mul] at q2
  exact q2

end GlobalTheory.AnalyticVec
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.InnerEqOfIrreducible
section
open Formalism.BasicNotions.TH Formalism.MainNotions.SchurIrreducible

namespace GlobalTheory.InvFormUnique

theorem inner_eq_of_common_kernel_line {V H₁ H₂ ι : Type*} [AddCommGroup V] [Module ℂ V]
    [NormedAddCommGroup H₁] [InnerProductSpace ℂ H₁] [NormedAddCommGroup H₂] [InnerProductSpace ℂ H₂]
    (j₁ : V →ₗ[ℂ] H₁) (j₂ : V →ₗ[ℂ] H₂) (A A' : ι → Module.End ℂ V) (W : Submodule ℂ V)
    [FiniteDimensional ℂ W] (hA : ∀ i, ∀ w ∈ W, A i w ∈ W) (hA' : ∀ i, ∀ w ∈ W, A' i w ∈ W)
    (h₁ : ∀ i x y, inner ℂ (j₁ (A i x)) (j₁ y) = inner ℂ (j₁ x) (j₁ (A' i y)))
    (h₂ : ∀ i x y, inner ℂ (j₂ (A i x)) (j₂ y) = inner ℂ (j₂ x) (j₂ (A' i y)))
    (hinj : Function.Injective j₂) (v : V) (hv : ∀ i, A i v = 0)
    (hline : ∀ h, (∀ i, A i h = 0) → ∃ c : ℂ, c • v = h)
    (hn : inner ℂ (j₁ v) (j₁ v) = inner ℂ (j₂ v) (j₂ v)) (y : V) (hy : y ∈ W) :
    inner ℂ (j₁ v) (j₁ y) = inner ℂ (j₂ v) (j₂ y) := by
  classical

  let f : W →ₗ[ℂ] H₂ := j₂ ∘ₗ W.subtype
  have hfi : Function.Injective f := hinj.comp Subtype.val_injective
  let e : W ≃ₗ[ℂ] LinearMap.range f := LinearEquiv.ofInjective f hfi
  let ψ : V →ₗ[ℂ] ℂ := (innerₛₗ ℂ (j₁ v)) ∘ₗ j₁ - (innerₛₗ ℂ (j₂ v)) ∘ₗ j₂
  have hψ : ∀ x, ψ x = inner ℂ (j₁ v) (j₁ x) - inner ℂ (j₂ v) (j₂ x) := fun x => by
    simp [ψ]
  let g : LinearMap.range f →ₗ[ℂ] ℂ := ψ ∘ₗ W.subtype ∘ₗ e.symm.toLinearMap

  obtain ⟨u, huW, hrep⟩ : ∃ u ∈ W, ∀ z ∈ W, inner ℂ (j₂ u) (j₂ z) = ψ z := by
    let u' := (InnerProductSpace.toDual ℂ (LinearMap.range f)).symm (LinearMap.toContinuousLinearMap g)
    have key : ∀ s : LinearMap.range f, inner ℂ (u' : H₂) (s : H₂) = g s := by
      intro s
      rw [← Submodule.coe_inner]
      exact InnerProductSpace.toDual_symm_apply
    refine ⟨(e.symm u' : V), (e.symm u').2, fun z hz => ?_⟩
    have h1 := key (e ⟨z, hz⟩)
    have h2 : ((e ⟨z, hz⟩ : LinearMap.range f) : H₂) = j₂ z := LinearEquiv.ofInjective_apply _ _
    have h3 : ((u' : LinearMap.range f) : H₂) = j₂ (e.symm u' : V) := by
      conv_lhs => rw [← e.apply_symm_apply u']
      exact LinearEquiv.ofInjective_apply _ _
    rw [h2, h3] at h1
    rw [h1]
    simp [g]

  have hker : ∀ i, A i u = 0 := by
    intro i
    have horth : ∀ z ∈ W, inner ℂ (j₂ (A i u)) (j₂ z) = 0 := by
      intro z hz
      rw [h₂, hrep _ (hA' i z hz), hψ, ← h₁, ← h₂, hv]
      simp
    have h0 := horth _ (hA i u huW)
    rw [inner_self_eq_zero] at h0
    exact hinj (by rw [h0, map_zero])

  obtain ⟨c, hc⟩ := hline u hker
  have hψv : ψ v = 0 := by rw [hψ, hn, sub_self]
  have hψu : ψ u = 0 := by rw [← hc, map_smul, hψv, smul_zero]
  have hj : j₂ u = 0 := by
    rw [← inner_self_eq_zero (𝕜 := ℂ), hrep u huW, hψu]
  have hy' := hrep y hy
  rw [hj, inner_zero_left, hψ] at hy'
  exact sub_eq_zero.mp hy'.symm

theorem adjZ_Eab {p q : ℕ} {a b : Ix p q} (h : sameBlock a b) : adjZ (Eab a b) = Eab b a := by
  unfold adjZ Eab Jm Formalism.UG.Jpq

  have hJ : (Matrix.fromBlocks (1 : Matrix (Fin p) (Fin p) ℂ) 0 0 (-1) : Mat p q) =
      Matrix.diagonal (Sum.elim (fun _ => (1 : ℂ)) (fun _ => -1)) := by
    ext i j
    rcases i with i | i <;> rcases j with j | j <;>
      simp [Matrix.diagonal_apply, Matrix.one_apply, apply_ite]
  rw [hJ]
  rcases a with a | a <;> rcases b with b | b
  all_goals try exact (h : False).elim
  all_goals
    ext i j
    simp only [Matrix.mul_diagonal, Matrix.diagonal_mul, Matrix.conjTranspose_apply, Matrix.single_apply]
    split_ifs with h1 h2 <;> (try obtain ⟨rfl, rfl⟩ := h1) <;> simp_all

theorem isKC_Eab {p q : ℕ} {a b : Ix p q} (h : sameBlock a b) : IsKC (Eab a b) := by
  unfold IsKC Eab
  intro c d hcd
  rw [Matrix.single_apply, if_neg]
  rintro ⟨rfl, rfl⟩
  exact hcd h

theorem sameBlock_of_posC {p q : ℕ} {a b : Ix p q} (h : posC a b) : sameBlock a b ∧ sameBlock b a := by
  rcases a with i | i <;> rcases b with j | j
  all_goals first
    | exact ⟨True.intro, True.intro⟩
    | exact (h : False).elim

theorem sameBlock_refl {p q : ℕ} (a : Ix p q) : sameBlock a a := by
  cases a <;> exact True.intro

private theorem mem_hwSub_iff' {p q : ℕ} {V0 : Type} [AddCommGroup V0] [Module ℂ V0]
    (f : Mat p q →ₗ[ℂ] Module.End ℂ V0) (μ : Ix p q → ℚ) (z : V0) :
    z ∈ hwSub f μ ↔ (∀ a, f (Eab a a) z = (μ a : ℂ) • z) ∧ ∀ a b, posC a b → f (Eab a b) z = 0 := by
  simp only [hwSub, wtSub, Submodule.mem_inf, Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.sub_apply,
    LinearMap.smul_apply, LinearMap.id_apply, sub_eq_zero]

theorem inner_eq_of_irreducible (p q : ℕ) (M : GKMod p q) (H₁ : Type) [NormedAddCommGroup H₁]
    [InnerProductSpace ℂ H₁] (H₂ : Type) [NormedAddCommGroup H₂] [InnerProductSpace ℂ H₂]
    (j₁ : M.V →ₗ[ℂ] H₁) (j₂ : M.V →ₗ[ℂ] H₂)
    (h₁ : ∀ Z x y, inner ℂ (j₁ (M.act Z x)) (j₁ y) = inner ℂ (j₁ x) (j₁ (M.act (adjZ Z) y)))
    (h₂ : ∀ Z x y, inner ℂ (j₂ (M.act Z x)) (j₂ y) = inner ℂ (j₂ x) (j₂ (M.act (adjZ Z) y)))
    (hinj : Function.Injective j₂) (hirr : IrrGK M) (μ : Ix p q → ℚ) (v : M.V) (hv : IsHW M.act μ v)
    (hdim : Module.finrank ℂ ↥(hwSub M.act μ) = 1)
    (hn : inner ℂ (j₁ v) (j₁ v) = inner ℂ (j₂ v) (j₂ v)) (x y : M.V) :
    inner ℂ (j₁ x) (j₁ y) = inner ℂ (j₂ x) (j₂ y) := by
  classical

  let N : Submodule ℂ M.V :=
    { carrier := {z | ∀ w, inner ℂ (j₁ z) (j₁ w) = inner ℂ (j₂ z) (j₂ w)}
      add_mem' := by
        intro a b ha hb
        simp only [Set.mem_ofPred_eq] at ha hb ⊢
        intro w
        rw [map_add (f := _), map_add (f := _), inner_add_left, inner_add_left, ha, hb]
      zero_mem' := by
        simp only [Set.mem_ofPred_eq, map_zero, inner_zero_left, implies_true]
      smul_mem' := by
        intro c a ha
        simp only [Set.mem_ofPred_eq] at ha ⊢
        intro w
        rw [map_smul, map_smul, inner_smul_left, inner_smul_left, ha] }
  have hmemN : ∀ z, z ∈ N ↔ ∀ w, inner ℂ (j₁ z) (j₁ w) = inner ℂ (j₂ z) (j₂ w) := fun z => Iff.rfl

  have hNinv : ∀ Z, ∀ z ∈ N, M.act Z z ∈ N := by
    intro Z z hz
    rw [hmemN] at hz ⊢
    intro w
    rw [h₁, h₂, hz]
  obtain ⟨hv0, hvmem⟩ : v ≠ 0 ∧ v ∈ hwSub M.act μ := hv
  have hmem := (mem_hwSub_iff' M.act μ v).mp hvmem

  let A : ({ab : Ix p q × Ix p q // posC ab.1 ab.2} ⊕ Ix p q) → Module.End ℂ M.V :=
    Sum.elim (fun ab => M.act (Eab ab.1.1 ab.1.2)) (fun c => M.act (Eab c c) - (μ c : ℂ) • LinearMap.id)
  let A' : ({ab : Ix p q × Ix p q // posC ab.1 ab.2} ⊕ Ix p q) → Module.End ℂ M.V :=
    Sum.elim (fun ab => M.act (Eab ab.1.2 ab.1.1)) (fun c => M.act (Eab c c) - (μ c : ℂ) • LinearMap.id)
  have hh : ∀ (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] (j : M.V →ₗ[ℂ] H),
      (∀ Z z w, inner ℂ (j (M.act Z z)) (j w) = inner ℂ (j z) (j (M.act (adjZ Z) w))) →
      ∀ i z w, inner ℂ (j (A i z)) (j w) = inner ℂ (j z) (j (A' i w)) := by
    intro H _ _ j hj
    rintro (⟨⟨a, b⟩, hab⟩ | c) z w
    · simp only [A, A', Sum.elim_inl]
      rw [hj, adjZ_Eab (sameBlock_of_posC hab).1]
    · simp only [A, A', Sum.elim_inr, LinearMap.sub_apply, LinearMap.smul_apply, LinearMap.id_apply,
        map_sub, map_smul, inner_sub_left, inner_sub_right, inner_smul_left, inner_smul_right]
      rw [hj, adjZ_Eab (sameBlock_refl c)]
      all_goals simp
  have hAv : ∀ i, A i v = 0 := by
    rintro (⟨⟨a, b⟩, hab⟩ | c)
    · exact hmem.2 a b hab
    · simp only [A, Sum.elim_inr, LinearMap.sub_apply, LinearMap.smul_apply, LinearMap.id_apply]
      rw [hmem.1 c, sub_self]
  have hline : ∀ z, (∀ i, A i z = 0) → ∃ c : ℂ, c • v = z := by
    intro z hz0
    have hzmem : z ∈ hwSub M.act μ := by
      rw [mem_hwSub_iff']
      refine ⟨fun c => ?_, fun a b hab => hz0 (Sum.inl ⟨(a, b), hab⟩)⟩
      have hc0 := hz0 (Sum.inr c)
      simp only [A, Sum.elim_inr, LinearMap.sub_apply, LinearMap.smul_apply, LinearMap.id_apply,
        sub_eq_zero] at hc0
      exact hc0
    have hne : (⟨v, hvmem⟩ : hwSub M.act μ) ≠ 0 := by
      rwa [Ne, Submodule.mk_eq_zero]
    obtain ⟨c, hc⟩ := (finrank_eq_one_iff_of_nonzero' _ hne).mp hdim ⟨z, hzmem⟩
    exact ⟨c, by simpa using congrArg Subtype.val hc⟩

  have hvN : v ∈ N := by
    rw [hmemN]
    intro w
    obtain ⟨W, hWfin, hwW, hWst⟩ := M.kfin w
    have := hWfin
    have hWst' : ∀ Z, IsKC Z → ∀ u ∈ W, M.act Z u ∈ W := hWst
    have hAW : ∀ i, ∀ u ∈ W, A i u ∈ W := by
      rintro (⟨⟨a, b⟩, hab⟩ | c) u hu
      · exact hWst' _ (isKC_Eab (sameBlock_of_posC hab).1) u hu
      · simp only [A, Sum.elim_inr, LinearMap.sub_apply, LinearMap.smul_apply, LinearMap.id_apply]
        exact W.sub_mem (hWst' _ (isKC_Eab (sameBlock_refl c)) u hu) (W.smul_mem _ hu)
    have hA'W : ∀ i, ∀ u ∈ W, A' i u ∈ W := by
      rintro (⟨⟨a, b⟩, hab⟩ | c) u hu
      · exact hWst' _ (isKC_Eab (sameBlock_of_posC hab).2) u hu
      · simp only [A', Sum.elim_inr, LinearMap.sub_apply, LinearMap.smul_apply, LinearMap.id_apply]
        exact W.sub_mem (hWst' _ (isKC_Eab (sameBlock_refl c)) u hu) (W.smul_mem _ hu)
    exact inner_eq_of_common_kernel_line j₁ j₂ A A' W hAW hA'W (hh H₁ j₁ h₁) (hh H₂ j₂ h₂) hinj v hAv
      hline hn w hwW

  obtain ⟨-, hirr2⟩ := hirr
  rcases hirr2 N hNinv with hN | hN
  · exact absurd ((Submodule.mem_bot ℂ).mp (hN ▸ hvN)) hv0
  · have hx : x ∈ N := by rw [hN]; exact Submodule.mem_top
    exact (hmemN x).mp hx y

end GlobalTheory.InvFormUnique
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.SelfDualLatticeResolutionOfIdentity
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes NumberField Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.SelfDualIdDecomp

variable {E : Type} [Field E] [NumberField E] [StarRing E]

theorem star_mem_range (a : 𝓞 E) : star (a : E) ∈ (algebraMap (𝓞 E) E).range := by
  have h : IsIntegral ℤ (star (a : E)) := by
    exact (RingOfIntegers.isIntegral_coe a).map (starRingEnd E).toIntAlgHom
  exact ⟨⟨star (a : E), h⟩, rfl⟩

theorem exists_den {N : ℕ} (L : Submodule (𝓞 E) (Fin N → E)) (hfg : L.FG) :
    ∃ b : 𝓞 E, b ≠ 0 ∧ ∀ x ∈ L, ∀ i, ∃ u : 𝓞 E, (u : E) = (b : E) * x i := by
  first
  | exact @_root_.GlobalTheory.CommonDenominatorLemma.exists_common_denominator
  | exact _root_.GlobalTheory.CommonDenominatorLemma.exists_common_denominator
  | (apply _root_.GlobalTheory.CommonDenominatorLemma.exists_common_denominator <;> assumption)
  | (intros; apply _root_.GlobalTheory.CommonDenominatorLemma.exists_common_denominator <;> assumption)
  | (intros; apply @_root_.GlobalTheory.CommonDenominatorLemma.exists_common_denominator <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.CommonDenominatorLemma.exists_common_denominator ..)

theorem exists_extension {N : ℕ} (L : Submodule (𝓞 E) (Fin N → E)) (hL : IsSDLat E N L)
    (φ : L →ₗ[𝓞 E] 𝓞 E) : ∃ u ∈ L, ∀ x (hx : x ∈ L), stdH E N u x = (φ ⟨x, hx⟩ : E) := by
  classical
  obtain ⟨hfg, -, hdual⟩ := hL
  obtain ⟨b, hb0, hb⟩ := exists_den L hfg
  obtain ⟨c', hc'⟩ := star_mem_range b
  have hbE : (b : E) ≠ 0 := by
    intro h; apply hb0; exact RingOfIntegers.coe_injective (by simpa using h)
  have hc0 : star (b : E) ≠ 0 := star_ne_zero.2 hbE
  have hce : ∀ i, (Pi.single i (star (b : E)) : Fin N → E) ∈ L := by
    intro i
    rw [hdual]
    intro x hx
    obtain ⟨u, hu⟩ := hb x hx i
    have h1 : stdH E N x (Pi.single i (star (b : E))) = star (u : E) := by
      rw [hu, star_mul]
      simp [stdH, Pi.single_apply]
    rw [h1]; exact star_mem_range u
  let w : Fin N → E := fun i => (φ ⟨Pi.single i (star (b : E)), hce i⟩ : E) / star (b : E)
  have hw : ∀ x (hx : x ∈ L), (φ ⟨x, hx⟩ : E) = ∑ i, w i * x i := by
    intro x hx
    choose ub hub using hb x hx
    have h1 : (b * c') • (⟨x, hx⟩ : L) = ∑ i, ub i • (⟨Pi.single i (star (b : E)), hce i⟩ : L) := by
      apply Subtype.ext; funext j
      simp only [Submodule.coe_smul, Submodule.coe_sum, Finset.sum_apply, Pi.smul_apply,
        Algebra.smul_def, Pi.single_apply, mul_ite, mul_zero, Finset.sum_ite_eq, Finset.mem_univ, if_true]
      have := hub j
      simp only [map_mul, hc']
      rw [show (algebraMap (𝓞 E) E) (ub j) = (b : E) * x j from this]
      ring
    have h2 := congrArg (fun z => ((φ z : 𝓞 E) : E)) h1
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [map_smul, map_sum, smul_eq_mul] at h2
    push_cast at h2
    apply mul_left_cancel₀ (mul_ne_zero hbE hc0)
    have h3 : (b : E) * star (b : E) * (φ ⟨x, hx⟩ : E) =
        ∑ i, ((ub i : 𝓞 E) : E) * (φ ⟨Pi.single i (star (b : E)), hce i⟩ : E) := by
      rw [← h2, ← hc']
    rw [h3, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [hub i]
    simp only [w]
    first | (field_simp; ring) | field_simp
  refine ⟨fun i => star (w i), ?_, ?_⟩
  · rw [hdual]
    intro y hy
    have : stdH E N y (fun i => star (w i)) = star (φ ⟨y, hy⟩ : E) := by
      rw [hw y hy, star_sum]
      simp [stdH, star_mul, mul_comm]
    rw [this]; exact star_mem_range _
  · intro x hx
    rw [hw x hx]
    simp [stdH]

theorem exists_decomp {N : ℕ} (L : Submodule (𝓞 E) (Fin N → E)) (hL : IsSDLat E N L) :
    ∃ (r : ℕ) (s u : Fin r → Fin N → E), (∀ k, s k ∈ L) ∧ (∀ k, u k ∈ L) ∧
      ∑ k, Matrix.vecMulVec (s k) (star (u k)) = 1 := by
  classical
  have hspan := hL.2.1
  have : Module.Finite (𝓞 E) L := Module.Finite.iff_fg.2 hL.1
  have : Module.FinitePresentation (𝓞 E) L := Module.finitePresentation_of_finite _ _
  have : Module.Projective (𝓞 E) L := Module.Flat.projective_of_finitePresentation
  obtain ⟨m, f, g, -, -, hfg⟩ := Module.Finite.exists_comp_eq_id_of_projective (𝓞 E) L
  choose u hu hux using fun k : Fin m => exists_extension L hL ((LinearMap.proj k) ∘ₗ g)
  refine ⟨m, fun k => (f (Pi.single k 1) : Fin N → E), u, fun k => (f _).2, hu, ?_⟩
  have hrec : ∀ y : L, (y : Fin N → E) = ∑ k, ((g y k : 𝓞 E) : E) • (f (Pi.single k 1) : Fin N → E) := by
    intro y
    have h1 : f (g y) = y := LinearMap.congr_fun hfg y
    set_option synthInstance.maxHeartbeats 100000 in
      conv_lhs => rw [← h1, pi_eq_sum_univ' (g y), map_sum]
    simp only [map_smul, Submodule.coe_sum, Submodule.coe_smul, algebraMap_smul]
  apply Matrix.toLin'.injective
  apply LinearMap.ext_on hspan
  rintro x hx
  rw [Matrix.toLin'_one, LinearMap.id_apply, Matrix.toLin'_apply]
  funext i
  have e1 : x i = ∑ k, ((g ⟨x, hx⟩ k : 𝓞 E) : E) * (f (Pi.single k 1) : Fin N → E) i := by
    conv_lhs => rw [show x = ((⟨x, hx⟩ : L) : Fin N → E) from rfl, hrec ⟨x, hx⟩]
    simp only [Finset.sum_apply, Pi.smul_apply]
    exact Finset.sum_congr rfl fun k _ => Algebra.smul_def _ _
  rw [e1]
  simp only [Matrix.mulVec, dotProduct, Matrix.sum_apply, vecMulVec_apply, Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun k _ => ?_
  have := hux k x hx
  simp only [stdH, LinearMap.comp_apply, LinearMap.proj_apply] at this
  rw [← this, Finset.sum_mul]
  refine Finset.sum_congr rfl fun j _ => ?_
  simp only [Pi.star_apply]
  ring

theorem iddecomp : ∀ {D : D7} {N : ℕ} (L : Submodule (𝓞 D.host.E) (Fin N → D.host.E)),
    Formalism.MainNotions.StandardLatticesGL3.SD D L → ∃ (r : ℕ) (s u : Fin r → Fin N → D.host.E), (∀ k, s k ∈ L) ∧ (∀ k, u k ∈ L) ∧
      ∑ k, Matrix.vecMulVec (s k) (star (u k)) = 1 := by
  intro D N L hL
  exact exists_decomp L hL

end GlobalTheory.SelfDualIdDecomp
end

