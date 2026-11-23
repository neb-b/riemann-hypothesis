module

public import Mathlib
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.ModeHalfStatementPfB
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.PairUnfoldPfA
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.HolomorphicFamilies.Bundle0005
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0001

@[expose] public section

-- bundled from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.HolomorphicFamilies.ModelGamS
section
set_option autoImplicit false

noncomputable section

namespace ReciprocityTheory.ChartRestriction.G.PullbackSections

open NumberField ReciprocityTheory.ChartRestriction.G.FD Matrix

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}

theorem map_gl_mul (τ : E →+* ℂ) (γ₁ γ₂ : GL (Fin r) E) :
    ((γ₁ * γ₂ : GL (Fin r) E) : Matrix (Fin r) (Fin r) E).map τ =
      (γ₁ : Matrix (Fin r) (Fin r) E).map τ * (γ₂ : Matrix (Fin r) (Fin r) E).map τ := by
  rw [Units.val_mul, Matrix.map_mul]

theorem map_gl_inv_mul (τ : E →+* ℂ) (γ : GL (Fin r) E) :
    ((γ⁻¹ : GL (Fin r) E) : Matrix (Fin r) (Fin r) E).map τ * (γ : Matrix (Fin r) (Fin r) E).map τ = 1 := by
  rw [← map_gl_mul, inv_mul_cancel, Units.val_one, Matrix.map_one]
  all_goals first | exact τ.map_zero | exact τ.map_one

def TSet (Ψ : Finset (E →+* ℂ)) (g : Matrix (Fin r) (Fin r) E) : Set (Frame Ψ r) :=
  {x | ∀ τ : Ψ, ∀ a c : Fin r, c < a → (adjugate (mat x τ) * g.map τ.1 * mat x τ) a c = 0}

theorem isClosed_TSet (Ψ : Finset (E →+* ℂ)) (g : Matrix (Fin r) (Fin r) E) : IsClosed (TSet Ψ g) := by
  simp only [TSet, Set.setOf_forall]
  refine isClosed_iInter fun τ => isClosed_iInter fun a => isClosed_iInter fun c =>
    isClosed_iInter fun _ => ?_
  have hm : Continuous fun x : Frame Ψ r => mat x τ :=
    continuous_pi fun i => continuous_pi fun j => by
      simp only [mat, Matrix.of_apply]
      fun_prop
  exact isClosed_eq
    (((hm.matrix_adjugate.matrix_mul continuous_const).matrix_mul hm).matrix_elem a c)
    continuous_const

theorem mem_TSet (Ψ : Finset (E →+* ℂ)) (γ γ' : GL (Fin r) E) {x b : Frame Ψ r} (hb : b ∈ Bor Ψ r)
    (h : lact γ x = rmul (lact γ' x) b) : x ∈ TSet Ψ ((γ'⁻¹ * γ : GL (Fin r) E) : Matrix (Fin r) (Fin r) E) := by
  change ∀ τ : Ψ, ∀ a c : Fin r, c < a →
    (adjugate (mat x τ) * ((γ'⁻¹ * γ : GL (Fin r) E) : Matrix (Fin r) (Fin r) E).map τ.1 * mat x τ) a c = 0
  intro τ a c hca
  have h1 : (γ : Matrix (Fin r) (Fin r) E).map τ.1 * mat x τ =
      (γ' : Matrix (Fin r) (Fin r) E).map τ.1 * (mat x τ * mat b τ) := by
    have h0 := congrArg (fun y => mat y τ) h
    rw [← Matrix.mul_assoc]
    exact h0
  have h2 : adjugate (mat x τ) * ((γ'⁻¹ * γ : GL (Fin r) E) : Matrix (Fin r) (Fin r) E).map τ.1 *
      mat x τ = (mat x τ).det • mat b τ := by
    rw [map_gl_mul]
    simp only [Matrix.mul_assoc]
    rw [h1, ← Matrix.mul_assoc _ ((γ' : Matrix (Fin r) (Fin r) E).map τ.1), map_gl_inv_mul,
      Matrix.one_mul, ← Matrix.mul_assoc, Matrix.adjugate_mul, Matrix.smul_mul, Matrix.one_mul]
  rw [h2, Matrix.smul_apply, smul_eq_mul]
  have hB : b τ a c = 0 := (hb τ).2 a c hca
  simp [mat, hB]

theorem scalar_step {Ψ : Finset (E →+* ℂ)} (τ₀ : Ψ) (g : Matrix (Fin r) (Fin r) E) {W : Set (Frame Ψ r)}
    (hWo : IsOpen W) (hWT : W ⊆ TSet Ψ g) {y : Frame Ψ r} (hyW : y ∈ W) (hy : (mat y τ₀).det ≠ 0) :
    ∃ κ : ℂ, g.map τ₀.1 = κ • 1 := by
  classical
  rcases Nat.eq_zero_or_pos r with rfl | hr
  · exact ⟨0, by ext a; exact Fin.elim0 a⟩
  set M : Matrix (Fin r) (Fin r) ℂ := g.map τ₀.1 with hM
  let i0 : Fin r := ⟨0, hr⟩
  let fr : (Fin r → ℂ) → Frame Ψ r := fun v τ a c => if τ = τ₀ ∧ c = i0 then v a else y τ a c
  let v₀ : Fin r → ℂ := fun a => y τ₀ a i0
  have hfr : Continuous fr := by
    refine continuous_pi fun τ => continuous_pi fun a => continuous_pi fun c => ?_
    by_cases h : τ = τ₀ ∧ c = i0
    · simp only [fr, if_pos h]
      exact continuous_apply a
    · simp only [fr, if_neg h]
      exact continuous_const
  have hfr0 : fr v₀ = y := by
    funext τ a c
    by_cases h : τ = τ₀ ∧ c = i0
    · obtain ⟨rfl, rfl⟩ := h
      simp [fr, v₀]
    · simp [fr, h]
  have hdet : Continuous fun v => (mat (fr v) τ₀).det := by
    refine Continuous.matrix_det ?_
    exact continuous_pi fun a => continuous_pi fun c => by
      simp only [mat, Matrix.of_apply]
      exact (continuous_apply c).comp ((continuous_apply a).comp ((continuous_apply τ₀).comp hfr))
  have hW1 : ∀ᶠ v in nhds v₀, fr v ∈ W := (hfr.tendsto' v₀ y hfr0) (hWo.mem_nhds hyW)
  have hP : ∀ᶠ v in nhds v₀, fr v ∈ W ∧ (mat (fr v) τ₀).det ≠ 0 :=
    hW1.and (hdet.continuousAt.eventually_ne (by
      show (mat (fr v₀) τ₀).det ≠ 0
      rw [hfr0]
      exact hy))
  have hB : ∀ v, fr v ∈ W → (mat (fr v) τ₀).det ≠ 0 → ∃ l : ℂ, M *ᵥ v = l • v := by
    intro v hvW hd
    have hT : ∀ τ : Ψ, ∀ a c : Fin r, c < a →
        (adjugate (mat (fr v) τ) * g.map τ.1 * mat (fr v) τ) a c = 0 := hWT hvW
    set X := mat (fr v) τ₀ with hX
    have hcol : ∀ a, X a i0 = v a := fun a => by simp [hX, mat, fr]
    set z := X.adjugate *ᵥ (M *ᵥ v) with hz
    have hz0 : ∀ a, a ≠ i0 → z a = 0 := by
      intro a ha
      have h1 := hT τ₀ a i0 (by
        rw [Fin.lt_iff_val_lt_val]
        exact Nat.pos_of_ne_zero fun h => ha (Fin.ext h))
      have h2 : z a = (X.adjugate * M * X) a i0 := by
        rw [hz, Matrix.mulVec_mulVec]
        simp only [Matrix.mulVec, dotProduct, Matrix.mul_apply, hcol]
      rw [h2]
      exact h1
    have hXz : X *ᵥ z = X.det • (M *ᵥ v) := by
      calc X *ᵥ z = (X * X.adjugate) *ᵥ (M *ᵥ v) := by
            rw [hz]
            simp only [Matrix.mulVec_mulVec, Matrix.mul_assoc]
        _ = X.det • (M *ᵥ v) := by
            rw [Matrix.mul_adjugate]
            first
              | rw [Matrix.smul_mulVec, Matrix.one_mulVec]
              | (ext i; simp [Matrix.mulVec, dotProduct, Matrix.one_apply])
    have hXz' : X *ᵥ z = z i0 • v := by
      funext a
      simp only [Matrix.mulVec, dotProduct, Pi.smul_apply, smul_eq_mul]
      rw [Finset.sum_eq_single i0 (fun b _ hb => by rw [hz0 b hb, mul_zero])
        (fun h => absurd (Finset.mem_univ i0) h), hcol, mul_comm]
    refine ⟨z i0 / X.det, ?_⟩
    funext a
    have ha := congrFun (hXz.symm.trans hXz') a
    simp only [Pi.smul_apply, smul_eq_mul] at ha ⊢
    rw [div_mul_eq_mul_div, eq_div_iff hd]
    linear_combination ha
  have hQ : ∀ v, fr v ∈ W → (mat (fr v) τ₀).det ≠ 0 →
      ∀ a b, (M *ᵥ v) a * v b = (M *ᵥ v) b * v a := by
    intro v h1 h2 a b
    obtain ⟨l, hl⟩ := hB v h1 h2
    rw [hl]
    simp only [Pi.smul_apply, smul_eq_mul]
    ring
  have hall : ∀ u : Fin r → ℂ, ∀ a b, (M *ᵥ u) a * u b = (M *ᵥ u) b * u a := by
    intro u a b
    have t1 : Filter.Tendsto (fun s : ℂ => v₀ + s • u) (nhds 0) (nhds v₀) :=
      Continuous.tendsto' (by fun_prop) 0 v₀ (by simp)
    have t2 : Filter.Tendsto (fun s : ℂ => v₀ + (2 * s) • u) (nhds 0) (nhds v₀) :=
      Continuous.tendsto' (by fun_prop) 0 v₀ (by simp)
    have e1 : ∀ᶠ s in nhdsWithin (0 : ℂ) {0}ᶜ, fr (v₀ + s • u) ∈ W ∧ (mat (fr (v₀ + s • u)) τ₀).det ≠ 0 :=
      nhdsWithin_le_nhds (t1.eventually hP)
    have e2 : ∀ᶠ s in nhdsWithin (0 : ℂ) {0}ᶜ,
        fr (v₀ + (2 * s) • u) ∈ W ∧ (mat (fr (v₀ + (2 * s) • u)) τ₀).det ≠ 0 :=
      nhdsWithin_le_nhds (t2.eventually hP)
    have e3 : ∀ᶠ s in nhdsWithin (0 : ℂ) {0}ᶜ, s ≠ 0 := self_mem_nhdsWithin
    obtain ⟨s, hs1, hs2, hs0⟩ := (e1.and (e2.and e3)).exists
    have q0 := hQ v₀ (by rw [hfr0]; exact hyW) (by rw [hfr0]; exact hy) a b
    have q1 := hQ _ hs1.1 hs1.2 a b
    have q2 := hQ _ hs2.1 hs2.2 a b
    simp only [Matrix.mulVec_add, Matrix.mulVec_smul, Pi.add_apply, Pi.smul_apply, smul_eq_mul] at q1 q2
    have key : (2 * s ^ 2) * ((M *ᵥ u) a * u b - (M *ᵥ u) b * u a) = 0 := by
      linear_combination q2 - 2 * q1 + q0
    have hs2' : (2 * s ^ 2 : ℂ) ≠ 0 := mul_ne_zero two_ne_zero (pow_ne_zero 2 hs0)
    exact sub_eq_zero.mp ((mul_eq_zero.mp key).resolve_left hs2')
  have hcolv : ∀ j i, (M *ᵥ Pi.single j 1) i = M i j := by
    intro j i
    simp [Matrix.mulVec, dotProduct, Pi.single_apply]
  have hoff : ∀ a b, a ≠ b → M a b = 0 := by
    intro a b hab
    have h := hall (Pi.single b 1) a b
    rw [hcolv, hcolv] at h
    simpa [Pi.single_apply, hab] using h
  have hdiag : ∀ a b, M a a = M b b := by
    intro a b
    by_cases hab : a = b
    · rw [hab]
    have h := hall (Pi.single a 1 + Pi.single b 1) a b
    rw [Matrix.mulVec_add] at h
    simp only [Pi.add_apply, hcolv] at h
    simp [Pi.single_apply, hab, Ne.symm hab, hoff a b hab, hoff b a (Ne.symm hab)] at h
    linear_combination h
  refine ⟨M i0 i0, ?_⟩
  ext a b
  by_cases hab : a = b
  · subst hab
    simp [hdiag a i0]
  · simp [hoff a b hab, hab]

end ReciprocityTheory.ChartRestriction.G.PullbackSections
end
end

-- bundled from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.HolomorphicFamilies.UnLocal
section
noncomputable section

namespace ReciprocityTheory.ChartRestriction.G.PullbackSections

open AlgebraicGeometry CategoryTheory NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.TB.ValAt

theorem valAt'_spMap {A : Type} [CommRing A] (ψ : A →+* ℂ) (a : A) :
    valAt' (spMap ψ) ⊤ ((Scheme.ΓSpecIso (CommRingCat.of A)).inv a) = ψ a := by
  unfold valAt'
  rw [dite_eq_left (by simp)]
  unfold valAt
  have h1 : (spMap ψ).appLE ⊤ ⊤ (by simp) = (spMap ψ).appTop := by
    rw [Scheme.Hom.appTop, Scheme.Hom.app_eq_appLE]
    first
      | rfl
      | simp
  rw [h1]
  have h2 := congrArg (fun f => (CommRingCat.Hom.hom f) ((Scheme.ΓSpecIso (CommRingCat.of A)).inv a))
    (Scheme.ΓSpecIso_naturality (CommRingCat.ofHom ψ))
  simp only [CommRingCat.hom_comp, RingHom.comp_apply, CommRingCat.hom_ofHom] at h2
  refine h2.trans ?_
  simp

private lemma app_lemma_0 {A : Type} [CommRing A] (ψ : A →+* ℂ) (a : A) :
    (Scheme.ΓSpecIso (CommRingCat.of ℂ)).hom ((spMap ψ).appTop ((Scheme.ΓSpecIso (CommRingCat.of A)).inv a)) = ψ a := by
  have h0 := valAt'_spMap ψ a
  unfold valAt' at h0
  rw [dite_eq_left (by simp)] at h0
  unfold valAt at h0
  have h1 : (spMap ψ).appLE ⊤ ⊤ (by simp) = (spMap ψ).appTop := by
    rw [Scheme.Hom.appTop, Scheme.Hom.app_eq_appLE]
    first
      | rfl
      | simp
  rw [h1] at h0
  exact h0

private lemma vEq_lemma {A : Type} [CommRing A] (ψ : A →+* ℂ) {V : (Sp A).Opens}
    (e : ⊤ ≤ spMap ψ ⁻¹ᵁ V) (s : Γ(Sp A, V)) :
    valAt' (spMap ψ) V s = (Scheme.ΓSpecIso (CommRingCat.of ℂ)).hom ((spMap ψ).appLE V ⊤ e s) := by
  unfold valAt'
  rw [dite_eq_left e]
  rfl

private lemma preMono_lemma_8 {A : Type} [CommRing A] (ψ : A →+* ℂ) {V W : (Sp A).Opens} (hVW : V ≤ W) :
    spMap ψ ⁻¹ᵁ V ≤ spMap ψ ⁻¹ᵁ W := by
  first
    | exact fun x hx => hVW hx
    | exact (Opens.map (spMap ψ).base).monotone hVW
    | exact Scheme.Hom.preimage_mono _ hVW
    | (intro x hx; exact hVW hx)

private lemma vRes_lemma_2 {A : Type} [CommRing A] (ψ : A →+* ℂ) {V W : (Sp A).Opens} (hVW : V ≤ W)
    (e : ⊤ ≤ spMap ψ ⁻¹ᵁ V) (s : Γ(Sp A, W)) :
    valAt' (spMap ψ) V ((Sp A).presheaf.map (homOfLE hVW).op s) = valAt' (spMap ψ) W s := by
  rw [vEq_lemma ψ e, vEq_lemma ψ (e.trans (preMono_lemma_8 ψ hVW))]
  have key := congrArg (fun g => (CommRingCat.Hom.hom g) s) ((spMap ψ).map_appLE e (homOfLE hVW).op)
  simp only [CommRingCat.hom_comp, RingHom.comp_apply] at key
  exact congrArg (fun t => (Scheme.ΓSpecIso (CommRingCat.of ℂ)).hom t) key

private lemma vMul_lemma_6 {A : Type} [CommRing A] (ψ : A →+* ℂ) {V : (Sp A).Opens}
    (e : ⊤ ≤ spMap ψ ⁻¹ᵁ V) (s t : Γ(Sp A, V)) :
    valAt' (spMap ψ) V (s * t) = valAt' (spMap ψ) V s * valAt' (spMap ψ) V t := by
  simp only [vEq_lemma ψ e, map_mul]

private lemma vPow_lemma_7 {A : Type} [CommRing A] (ψ : A →+* ℂ) {V : (Sp A).Opens}
    (e : ⊤ ≤ spMap ψ ⁻¹ᵁ V) (s : Γ(Sp A, V)) (n : ℕ) :
    valAt' (spMap ψ) V (s ^ n) = valAt' (spMap ψ) V s ^ n := by
  simp only [vEq_lemma ψ e, map_pow]

private lemma topLe_lemma_3 {A : Type} [CommRing A] (ψ : A →+* ℂ) (g : A) (hg : ψ g ≠ 0) :
    ⊤ ≤ spMap ψ ⁻¹ᵁ (Sp A).basicOpen ((Scheme.ΓSpecIso (CommRingCat.of A)).inv g) := by
  have hc := app_lemma_0 ψ g
  have hu : IsUnit ((spMap ψ).appTop ((Scheme.ΓSpecIso (CommRingCat.of A)).inv g)) := by
    have h0 : IsUnit ((Scheme.ΓSpecIso (CommRingCat.of ℂ)).hom
        ((spMap ψ).appTop ((Scheme.ΓSpecIso (CommRingCat.of A)).inv g))) := by
      rw [hc]
      exact hg.isUnit
    have h1 := h0.map (Scheme.ΓSpecIso (CommRingCat.of ℂ)).inv.hom
    simpa using h1
  have hb := (Sp ℂ).basicOpen_of_isUnit hu
  rw [Scheme.preimage_basicOpen]
  first
    | exact hb.symm.le
    | exact le_of_eq hb.symm
    | (rw [← Scheme.Hom.appTop, hb])
    | simp [Scheme.Hom.appTop, hb]

private lemma local_lemma_4 {A : Type} [CommRing A] (ψ : A →+* ℂ) {U : (Sp A).Opens}
    (e : ⊤ ≤ spMap ψ ⁻¹ᵁ U) : ∃ g : A, ψ g ≠ 0 ∧
      (Sp A).basicOpen ((Scheme.ΓSpecIso (CommRingCat.of A)).inv g) ≤ U := by
  obtain ⟨pt⟩ : Nonempty (Sp ℂ) := by
    first
      | infer_instance
      | exact ⟨(⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum ℂ)⟩
  have hpt : pt ∈ spMap ψ ⁻¹ᵁ U := e (show pt ∈ (⊤ : (Sp ℂ).Opens) by first | trivial | simp)
  obtain ⟨g', hD, hxD⟩ := (isAffineOpen_top (Sp A)).exists_basicOpen_le ⟨(spMap ψ).base pt, hpt⟩
    (by first | trivial | simp)
  obtain ⟨g, rfl⟩ : ∃ g : A, (Scheme.ΓSpecIso (CommRingCat.of A)).inv g = g' :=
    ⟨(Scheme.ΓSpecIso (CommRingCat.of A)).hom g', by simp⟩
  refine ⟨g, ?_, hD⟩
  intro hg
  have hc := app_lemma_0 ψ g
  rw [hg] at hc
  have hc0 : (spMap ψ).appTop ((Scheme.ΓSpecIso (CommRingCat.of A)).inv g) = 0 := by
    have h3 := congrArg (Scheme.ΓSpecIso (CommRingCat.of ℂ)).inv.hom hc
    simpa using h3
  have hpt' : pt ∈ spMap ψ ⁻¹ᵁ (Sp A).basicOpen ((Scheme.ΓSpecIso (CommRingCat.of A)).inv g) := hxD
  rw [Scheme.preimage_basicOpen] at hpt'
  first
    | rw [hc0] at hpt'
    | erw [hc0] at hpt'
    | rw [← Scheme.Hom.appTop, hc0] at hpt'
  first
    | (rw [Scheme.basicOpen_zero] at hpt'; simp at hpt')
    | (erw [Scheme.basicOpen_zero] at hpt'; simp at hpt')
    | (simp at hpt'; done)
    | exact absurd hpt' (by simp [Scheme.basicOpen_zero])
    | (rw [Scheme.mem_basicOpen] at hpt'; simp at hpt')
    | (erw [Scheme.mem_basicOpen] at hpt'; simp at hpt')

private lemma alg_lemma_5 {A : Type} [CommRing A] (ψ : A →+* ℂ) (g' : Γ(Sp A, ⊤))
    (e : ⊤ ≤ spMap ψ ⁻¹ᵁ (Sp A).basicOpen g') (x : Γ(Sp A, ⊤)) :
    valAt' (spMap ψ) ((Sp A).basicOpen g') (algebraMap Γ(Sp A, ⊤) Γ(Sp A, (Sp A).basicOpen g') x) =
      ψ ((Scheme.ΓSpecIso (CommRingCat.of A)).hom x) := by
  have h0 := vRes_lemma_2 ψ (le_top : (Sp A).basicOpen g' ≤ ⊤) e x
  have h2 := valAt'_spMap ψ ((Scheme.ΓSpecIso (CommRingCat.of A)).hom x)
  have hx : (Scheme.ΓSpecIso (CommRingCat.of A)).inv ((Scheme.ΓSpecIso (CommRingCat.of A)).hom x) = x := by
    simp
  rw [hx] at h2
  exact h0.trans h2

theorem isHolTo_spMap {A : Type} [CommRing A] {m : ℕ} {B : Set (Fin m → ℂ)} (hB : IsOpen B) {Ψ : (Fin m → ℂ) → (A →+* ℂ)}
    (h : ∀ a, DifferentiableOn ℂ (fun b => Ψ b a) B) : IsHolTo B fun b => spMap (Ψ b) := by
  unfold IsHolTo
  intro U f
  have nbhd : ∀ b0 ∈ {b | b ∈ B ∧ ⊤ ≤ spMap (Ψ b) ⁻¹ᵁ U}, ∃ g : A, Ψ b0 g ≠ 0 ∧
      (Sp A).basicOpen ((Scheme.ΓSpecIso (CommRingCat.of A)).inv g) ≤ U :=
    fun b0 hb0 => local_lemma_4 (Ψ b0) hb0.2
  have hopen : ∀ g : A, IsOpen (B ∩ (fun b => Ψ b g) ⁻¹' {0}ᶜ) :=
    fun g => ((h g).continuousOn).isOpen_inter_preimage hB isOpen_compl_singleton
  have hsub : ∀ g : A, (Sp A).basicOpen ((Scheme.ΓSpecIso (CommRingCat.of A)).inv g) ≤ U →
      B ∩ (fun b => Ψ b g) ⁻¹' {0}ᶜ ⊆ {b | b ∈ B ∧ ⊤ ≤ spMap (Ψ b) ⁻¹ᵁ U} := by
    intro g hD b hb
    exact ⟨hb.1, (topLe_lemma_3 (Ψ b) g hb.2).trans (preMono_lemma_8 (Ψ b) hD)⟩
  refine ⟨?_, ?_⟩
  · rw [isOpen_iff_forall_mem_open]
    intro b0 hb0
    obtain ⟨g, hg, hD⟩ := nbhd b0 hb0
    exact ⟨_, hsub g hD, hopen g, hb0.1, hg⟩
  · apply differentiableOn_of_locally_differentiableOn
    intro b0 hb0
    obtain ⟨g, hg, hD⟩ := nbhd b0 hb0
    refine ⟨_, hopen g, ⟨hb0.1, hg⟩, ?_⟩
    haveI := (isAffineOpen_top (Sp A)).isLocalization_basicOpen ((Scheme.ΓSpecIso (CommRingCat.of A)).inv g)
    obtain ⟨⟨h', m⟩, hm⟩ := IsLocalization.surj (Submonoid.powers ((Scheme.ΓSpecIso (CommRingCat.of A)).inv g))
      ((Sp A).presheaf.map (homOfLE hD).op f)
    dsimp only at hm
    obtain ⟨n, hn⟩ : ∃ n : ℕ, (Scheme.ΓSpecIso (CommRingCat.of A)).inv g ^ n = (m : Γ(Sp A, ⊤)) := by
      first
        | exact (Submonoid.mem_powers_iff _ _).mp m.2
        | exact m.2
        | simpa using m.2
        | (obtain ⟨k, hk⟩ := m.2; exact ⟨k, hk⟩)
    have key : ∀ b ∈ {b | b ∈ B ∧ ⊤ ≤ spMap (Ψ b) ⁻¹ᵁ U} ∩ (B ∩ (fun b => Ψ b g) ⁻¹' {0}ᶜ),
        valAt' (spMap (Ψ b)) U f = Ψ b ((Scheme.ΓSpecIso (CommRingCat.of A)).hom h') * (Ψ b g ^ n)⁻¹ := by
      intro b hb
      have hgb : Ψ b g ≠ 0 := hb.2.2
      have eD := topLe_lemma_3 (Ψ b) g hgb
      rw [← div_eq_mul_inv, eq_div_iff (pow_ne_zero _ hgb), ← vRes_lemma_2 (Ψ b) hD eD f]
      have hm' := congrArg (valAt' (spMap (Ψ b)) _) hm
      rw [vMul_lemma_6 (Ψ b) eD, ← hn, map_pow, vPow_lemma_7 (Ψ b) eD, alg_lemma_5 (Ψ b) _ eD, alg_lemma_5 (Ψ b) _ eD] at hm'
      have hg' : (Scheme.ΓSpecIso (CommRingCat.of A)).hom ((Scheme.ΓSpecIso (CommRingCat.of A)).inv g) = g := by
        simp
      rw [hg'] at hm'
      exact hm'
    refine DifferentiableOn.congr ?_ key
    exact ((((h _).mono Set.inter_subset_left).mul ((((h g).mono Set.inter_subset_left).pow n).inv
      (fun b (hb : b ∈ B ∩ (fun b => Ψ b g) ⁻¹' {0}ᶜ) => pow_ne_zero n hb.2))).mono Set.inter_subset_right)

end ReciprocityTheory.ChartRestriction.G.PullbackSections
end
end

-- bundled from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.HolomorphicFamilies.VtfValPullGen
section
set_option autoImplicit false

noncomputable section

namespace ReciprocityTheory.ChartRestriction.G.PullbackSections

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj Opposite
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.TB.ValAt Formalism.L2.Pj

attribute [local instance] Over.cartesianMonoidalCategory

section LC

variable {X Y Z : Scheme.{0}} (L : LB X) {K K' : Type} [Fintype K] [Fintype K']

private lemma valprod_lemma {R : Type} [CommRing R] (φ : R →+* ℂ) (u : K → Rˣ) (ε : K → ℤ) :
    φ ↑(∏ k, u k ^ ε k) = ∏ k, φ ↑(u k) ^ ε k := by
  have key : ∀ x : Rˣ, φ ↑x = ((Units.map φ.toMonoidHom x : ℂˣ) : ℂ) := fun _ => rfl
  rw [key, map_prod, Units.coe_prod]
  simp only [map_zpow, Units.val_zpow_eq_zpow_val, key]

theorem vtf_val_prodU (p : Sp ℂ ⟶ Y) {V : Y.Opens} (h : ⊤ ≤ p ⁻¹ᵁ V) (u : K → Γ(Y, V)ˣ) (ε : K → ℤ) :
    valAt' p V (∏ k, u k ^ ε k).val = ∏ k, valAt' p V (u k).val ^ ε k := by
  simp only [valAt', dif_pos h]
  unfold valAt
  simp only [← RingHom.comp_apply]
  exact valprod_lemma _ u ε

theorem vtf_val_lcg (φ : K → (Y ⟶ X)) (ε : K → ℤ) (p : Sp ℂ ⟶ Y) (j j' : K → L.ι)
    (h : ⊤ ≤ p ⁻¹ᵁ (LB.wchart L φ j ⊓ LB.wchart L φ j')) :
    valAt' p _ ((LB.LinComb L φ ε).g j j').val =
      ∏ k, valAt' (p ≫ φ k) (L.U (j k) ⊓ L.U (j' k)) (L.g (j k) (j' k)).val ^ ε k := by
  calc valAt' p _ ((LB.LinComb L φ ε).g j j').val
      = valAt' p (LB.wchart L φ j ⊓ LB.wchart L φ j')
          (∏ k, (res (le_inf (inf_le_left.trans (LB.wchart_le L φ j k))
            (inf_le_right.trans (LB.wchart_le L φ j' k)) :
              LB.wchart L φ j ⊓ LB.wchart L φ j' ≤ φ k ⁻¹ᵁ (L.U (j k) ⊓ L.U (j' k)))
            (pullU (φ k) _ (L.g (j k) (j' k)))) ^ ε k).val := rfl
    _ = ∏ k, valAt' p (LB.wchart L φ j ⊓ LB.wchart L φ j')
          (res (le_inf (inf_le_left.trans (LB.wchart_le L φ j k))
            (inf_le_right.trans (LB.wchart_le L φ j' k)) :
              LB.wchart L φ j ⊓ LB.wchart L φ j' ≤ φ k ⁻¹ᵁ (L.U (j k) ⊓ L.U (j' k)))
            (pullU (φ k) _ (L.g (j k) (j' k)))).val ^ ε k := vtf_val_prodU p h _ ε
    _ = _ := Finset.prod_congr rfl fun k _ => by
        exact congrArg (· ^ ε k) ((vtf_val_res (U := φ k ⁻¹ᵁ (L.U (j k) ⊓ L.U (j' k))) p _ h _).trans
          (vtf_val_pullU p (φ k) (L.U (j k) ⊓ L.U (j' k)) (L.g (j k) (j' k))))

theorem vtf_isGen_val (φ : K → (Y ⟶ X)) (ε : K → ℤ) (t : LB.Gen (LB.LinComb L φ ε)) (ht : t.IsGen)
    (p : Sp ℂ ⟶ Y) (j j' : K → L.ι) (h : ⊤ ≤ p ⁻¹ᵁ (LB.wchart L φ j ⊓ LB.wchart L φ j')) :
    valAt' p _ (t.s j).val =
      (∏ k, valAt' (p ≫ φ k) (L.U (j k) ⊓ L.U (j' k)) (L.g (j k) (j' k)).val ^ ε k) *
        valAt' p _ (t.s j').val := by
  have h' : ⊤ ≤ p ⁻¹ᵁ ((LB.LinComb L φ ε).U j ⊓ (LB.LinComb L φ ε).U j') := h
  calc valAt' p _ (t.s j).val
      = valAt' p ((LB.LinComb L φ ε).U j ⊓ (LB.LinComb L φ ε).U j')
          (res (inf_le_left : (LB.LinComb L φ ε).U j ⊓ (LB.LinComb L φ ε).U j' ≤ _) (t.s j)).val :=
        (vtf_val_res p _ h' _).symm
    _ = valAt' p ((LB.LinComb L φ ε).U j ⊓ (LB.LinComb L φ ε).U j')
          ((LB.LinComb L φ ε).g j j' *
            res (inf_le_right : (LB.LinComb L φ ε).U j ⊓ (LB.LinComb L φ ε).U j' ≤ _) (t.s j')).val := by
        rw [ht j j']
    _ = valAt' p ((LB.LinComb L φ ε).U j ⊓ (LB.LinComb L φ ε).U j') ((LB.LinComb L φ ε).g j j').val *
          valAt' p ((LB.LinComb L φ ε).U j ⊓ (LB.LinComb L φ ε).U j')
            (res (inf_le_right : (LB.LinComb L φ ε).U j ⊓ (LB.LinComb L φ ε).U j' ≤ _) (t.s j')).val := by
        rw [Units.val_mul, valAt'_mul]
    _ = _ := by rw [vtf_val_lcg L φ ε p j j' h, vtf_val_res p _ h']

end LC

section Liou

variable {g : ℕ}

end Liou

end ReciprocityTheory.ChartRestriction.G.PullbackSections
end
end

