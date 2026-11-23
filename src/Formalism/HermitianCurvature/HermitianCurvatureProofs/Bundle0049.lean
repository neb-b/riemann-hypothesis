module

public import Formalism.HermitianCurvature.HermitianCurvatureProofs.NormalFormOrderZeroOfParts
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0040
public import Mathlib.Geometry.Manifold.PartitionOfUnity

@[expose] public section

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.SmulRApply
section
noncomputable section

open Finset Filter
open scoped ContDiff Topology

namespace Formalism.FourierDecayAlt.P.NFRO

open Formalism.FourierDecayAlt.NF Formalism.FourierDecayAlt.P.NFx4

def JetR {M : Type*} [AddCommGroup M] [Module ℝ M] (U : Set ℂ) (ζ0 : ℂ) (Λ : (ℂ → ℂ) → M) : Prop :=
  ∃ (ι : Type) (_ : Fintype ι) (w : ι → List Bool) (L : ι → ℂ →ₗ[ℝ] M),
    ∀ f, ContDiffOn ℝ ∞ f U → Λ f = ∑ i, L i (wd (w i) f ζ0)

theorem wn_cmono (ζ0 c : ℂ) (j l a b : ℕ) :
    wn a b (fun x => c * mono ζ0 j l x) ζ0 = c * wn a b (mono ζ0 j l) ζ0 := by
  have e : mono ζ0 j l = fun x => 1 * mono ζ0 j l x := by funext x; ring
  have h1 : wn a b (fun x => c * mono ζ0 j l x) ζ0 =
      (c * (l.descFactorial b : ℂ) * (j.descFactorial a : ℂ)) * mono ζ0 (j - a) (l - b) ζ0 := by
    rw [wn, iter_dZb_cmono, iter_dZ_cmono]
  have h2 : wn a b (mono ζ0 j l) ζ0 =
      (1 * (l.descFactorial b : ℂ) * (j.descFactorial a : ℂ)) * mono ζ0 (j - a) (l - b) ζ0 := by
    rw [wn, e, iter_dZb_cmono, iter_dZ_cmono]
  rw [h1, h2]
  ring

section Zero

variable {M : Type*} [AddCommGroup M] [Module ℝ M] {U : Set ℂ} {ζ0 : ℂ}

theorem jetR_zero (hU : IsOpen U) (h0 : ζ0 ∈ U) {Λ : (ℂ → ℂ) → M} (hΛ : JetR U ζ0 Λ)
    (hP : ∀ (c : ℂ) (j l : ℕ), Λ (fun x => c * mono ζ0 j l x) = 0) : ∀ f, ContDiffOn ℝ ∞ f U → Λ f = 0 := by
  classical
  obtain ⟨ι, _, w, L, h⟩ := hΛ
  let cnt : ι → ℕ × ℕ := fun i => ((w i).count false, (w i).count true)
  have hS : ∀ (c : ℕ × ℕ) (x : ℂ), ∑ i ∈ univ.filter (fun i => cnt i = c), L i x = 0 := by
    intro c x
    have hne : ((c.1.factorial * c.2.factorial : ℕ) : ℂ) ≠ 0 := by
      exact_mod_cast (Nat.mul_pos (Nat.factorial_pos _) (Nat.factorial_pos _)).ne'
    obtain ⟨y, hy⟩ : ∃ y : ℂ, y * ((c.1.factorial * c.2.factorial : ℕ) : ℂ) = x :=
      ⟨x / _, div_mul_cancel₀ x hne⟩
    have hsm : ContDiffOn ℝ ∞ (fun t => y * mono ζ0 c.1 c.2 t) U :=
      contDiffOn_const.mul (contDiff_mono ζ0 c.1 c.2).contDiffOn
    have hc := h _ hsm
    rw [hP] at hc
    have e1 : ∀ i, L i (wd (w i) (fun t => y * mono ζ0 c.1 c.2 t) ζ0) =
        if cnt i = c then L i x else 0 := by
      intro i
      rw [wd_eq hU hsm (w i) h0, wn_cmono, wn_mono]
      by_cases hi : cnt i = c
      · rw [if_pos hi, if_pos (by rw [← hi]), hy]
      · rw [if_neg hi, if_neg (by intro h'; exact hi (by rw [h'])), mul_zero, map_zero]
    rw [Finset.sum_congr rfl (fun i _ => e1 i), ← Finset.sum_filter] at hc
    exact hc.symm
  intro f hf
  rw [h f hf, Finset.sum_congr rfl (fun i _ => by rw [wd_eq hU hf (w i) h0]),
    ← Finset.sum_fiberwise_of_maps_to (g := cnt) (t := univ.image cnt)
      (fun i _ => Finset.mem_image_of_mem cnt (Finset.mem_univ i))]
  refine Finset.sum_eq_zero fun c _ => ?_
  have e2 : ∀ i ∈ univ.filter (fun i => cnt i = c),
      L i (wn ((w i).count false) ((w i).count true) f ζ0) = L i (wn c.1 c.2 f ζ0) := by
    intro i hi
    have hi' : cnt i = c := (Finset.mem_filter.1 hi).2
    rw [← hi']
  rw [Finset.sum_congr rfl e2, hS c]

end Zero

section Deriv

variable {X : Type} [NormedAddCommGroup X] [NormedSpace ℝ X]

def smulR {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedSpace ℂ E] [IsScalarTower ℝ ℂ E]
    (c : X →L[ℝ] ℂ) : E →L[ℝ] (X →L[ℝ] E) :=
  ((ContinuousLinearMap.compL ℝ X ℂ E).flip c).comp (ContinuousLinearMap.lsmul ℝ ℂ : ℂ →L[ℝ] E →L[ℝ] E).flip

theorem smulR_apply {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedSpace ℂ E] [IsScalarTower ℝ ℂ E]
    (c : X →L[ℝ] ℂ) (e : E) (v : X) : smulR c e v = c v • e := by
  first
  | rfl
  | simp [smulR]

theorem jetR_iter (p : X →L[ℝ] ℂ) {U : Set ℂ} {V : Set X} (hU : IsOpen U) (hV : IsOpen V)
    (hVU : ∀ x ∈ V, p x ∈ U) {q : X} (hq : q ∈ V) (j : ℕ) :
    ∀ (E : Type) [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedSpace ℂ E] [IsScalarTower ℝ ℂ E] (φ : X → E),
      ContDiffOn ℝ ∞ φ V → JetR U (p q) (fun f => iteratedFDeriv ℝ j (fun x => f (p x) • φ x) q) := by
  induction j with
  | zero =>
    intro E _ _ _ _ φ _
    let L0 : ℂ →ₗ[ℝ] ContinuousMultilinearMap ℝ (fun _ : Fin 0 => X) E :=
      { toFun := fun c => (continuousMultilinearCurryFin0 ℝ X E).symm (c • φ q)
        map_add' := fun a b => by rw [add_smul, map_add (f := _)]
        map_smul' := fun s a => by
          rw [RingHom.id_apply, smul_assoc, LinearIsometryEquiv.map_smul] }
    refine ⟨Unit, inferInstance, fun _ => [], fun _ => L0, fun f _ => ?_⟩
    simp only [Finset.univ_unique, Finset.sum_singleton]
    rfl
  | succ j ih =>
    intro E _ _ _ _ φ hφ
    let c2 : X →L[ℝ] ℂ := (Complex.conjCLE : ℂ →L[ℝ] ℂ).comp p
    have hφ' : ContDiffOn ℝ ∞ (fun y => fderiv ℝ φ y) V := hφ.fderiv_of_isOpen hV (by simp)
    have hM1 : ContDiffOn ℝ ∞ (fun y => smulR (E := E) p (φ y)) V :=
      (smulR (E := E) p).contDiff.comp_contDiffOn hφ
    have hM2 : ContDiffOn ℝ ∞ (fun y => smulR (E := E) c2 (φ y)) V :=
      (smulR (E := E) c2).contDiff.comp_contDiffOn hφ
    obtain ⟨ι1, _, w1, L1, e1⟩ := ih (X →L[ℝ] E) _ hφ'
    obtain ⟨ι2, _, w2, L2, e2⟩ := ih (X →L[ℝ] E) _ hM1
    obtain ⟨ι3, _, w3, L3, e3⟩ := ih (X →L[ℝ] E) _ hM2
    let K : ContinuousMultilinearMap ℝ (fun _ : Fin j => X) (X →L[ℝ] E) →ₗ[ℝ]
        ContinuousMultilinearMap ℝ (fun _ : Fin (j + 1) => X) E :=
      (continuousMultilinearCurryRightEquiv' ℝ j X E).symm.toLinearEquiv.toLinearMap
    refine ⟨ι1 ⊕ ι2 ⊕ ι3, inferInstance,
      Sum.elim w1 (Sum.elim (fun i => w2 i ++ [false]) (fun i => w3 i ++ [true])),
      Sum.elim (fun i => K ∘ₗ L1 i) (Sum.elim (fun i => K ∘ₗ L2 i) (fun i => K ∘ₗ L3 i)), fun f hf => ?_⟩
    have hsm : ∀ {g : ℂ → ℂ} {F : Type} [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedSpace ℂ F]
        [IsScalarTower ℝ ℂ F] {ψ : X → F}, ContDiffOn ℝ ∞ g U → ContDiffOn ℝ ∞ ψ V →
        ContDiffAt ℝ j (fun y => g (p y) • ψ y) q := by
      intro g F _ _ _ _ ψ hg hψ
      exact (((hg.comp p.contDiff.contDiffOn hVU).smul hψ).contDiffAt (hV.mem_nhds hq)).of_le (inf_ge j)
    have hD : ∀ y ∈ V, fderiv ℝ (fun x => f (p x) • φ x) y =
        (f (p y) • fderiv ℝ φ y + dZ f (p y) • smulR p (φ y)) + dZb f (p y) • smulR c2 (φ y) := by
      intro y hy
      have hfd : HasFDerivAt f (fderiv ℝ f (p y)) (p y) :=
        ((hf.differentiableOn (by simp)).differentiableAt (hU.mem_nhds (hVU y hy))).hasFDerivAt
      have hφd : HasFDerivAt φ (fderiv ℝ φ y) y :=
        ((hφ.differentiableOn (by simp)).differentiableAt (hV.mem_nhds hy)).hasFDerivAt
      have hc : HasFDerivAt (fun x => f (p x)) ((fderiv ℝ f (p y)).comp p) y := hfd.comp y p.hasFDerivAt
      rw [(hc.fun_smul hφd).fderiv]
      ext v
      simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
        ContinuousLinearMap.smulRight_apply, ContinuousLinearMap.comp_apply, smulR_apply, fderiv_wirt, add_smul,
        mul_smul, c2]
      simp [add_assoc]
    have hev : (fun y => fderiv ℝ (fun x => f (p x) • φ x) y) =ᶠ[𝓝 q]
        (fun y => (f (p y) • fderiv ℝ φ y + dZ f (p y) • smulR p (φ y)) + dZb f (p y) • smulR c2 (φ y)) :=
      Filter.eventually_of_mem (hV.mem_nhds hq) hD
    beta_reduce at e1 e2 e3 ⊢
    rw [iteratedFDeriv_succ_eq_comp_right, Function.comp_apply, (hev.iteratedFDeriv ℝ j).eq_of_nhds,
      fun_iteratedFDeriv_add_apply ((hsm hf hφ').add (hsm (contDiffOn_dZ hU hf) hM1))
        (hsm (contDiffOn_dZb hU hf) hM2),
      fun_iteratedFDeriv_add_apply (hsm hf hφ') (hsm (contDiffOn_dZ hU hf) hM1),
      e1 f hf, e2 _ (contDiffOn_dZ hU hf), e3 _ (contDiffOn_dZb hU hf)]
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [map_add (f := _), map_sum, Fintype.sum_sum_type, Sum.elim_inl, Sum.elim_inr, LinearMap.comp_apply, wd_append]
    simp only [wd, Bool.false_eq_true, ↓reduceIte, add_assoc]
    rfl

end Deriv

section Closure

variable {M N : Type*} [AddCommGroup M] [Module ℝ M] [AddCommGroup N] [Module ℝ N] {U : Set ℂ} {ζ0 : ℂ}

theorem jetR_congr {Λ Λ' : (ℂ → ℂ) → M} (h : JetR U ζ0 Λ) (e : ∀ f, ContDiffOn ℝ ∞ f U → Λ f = Λ' f) :
    JetR U ζ0 Λ' := by
  obtain ⟨ι, hι, w, L, hL⟩ := h
  exact ⟨ι, hι, w, L, fun f hf => (e f hf).symm.trans (hL f hf)⟩

theorem jetR_map (Lm : M →ₗ[ℝ] N) {Λ : (ℂ → ℂ) → M} (h : JetR U ζ0 Λ) : JetR U ζ0 (fun f => Lm (Λ f)) := by
  obtain ⟨ι, hι, w, L, hL⟩ := h
  exact ⟨ι, hι, w, fun i => Lm ∘ₗ L i, fun f hf => by simp only [hL f hf, map_sum, LinearMap.comp_apply]⟩

theorem jetR_add {Λ Λ' : (ℂ → ℂ) → M} (h : JetR U ζ0 Λ) (h' : JetR U ζ0 Λ') :
    JetR U ζ0 (fun f => Λ f + Λ' f) := by
  obtain ⟨ι, hι, w, L, hL⟩ := h
  obtain ⟨ι', hι', w', L', hL'⟩ := h'
  exact ⟨ι ⊕ ι', inferInstance, Sum.elim w w', Sum.elim L L', fun f hf => by
    simp only [hL f hf, hL' f hf, Fintype.sum_sum_type, Sum.elim_inl, Sum.elim_inr]⟩

theorem jetR_sub {Λ Λ' : (ℂ → ℂ) → M} (h : JetR U ζ0 Λ) (h' : JetR U ζ0 Λ') :
    JetR U ζ0 (fun f => Λ f - Λ' f) := by
  refine jetR_congr (jetR_add h (jetR_map (-LinearMap.id) h')) fun f _ => ?_
  simp [sub_eq_add_neg]

theorem jetR_sum {κ : Type*} (s : Finset κ) {Λ : κ → (ℂ → ℂ) → M} (h : ∀ j ∈ s, JetR U ζ0 (Λ j)) :
    JetR U ζ0 (fun f => ∑ j ∈ s, Λ j f) := by
  have h0 : JetR U ζ0 (fun _ : ℂ → ℂ => (0 : M)) :=
    ⟨Empty, inferInstance, Empty.elim, Empty.elim, fun f _ => by simp⟩
  have hs := Finset.sum_induction Λ (JetR U ζ0) (fun a b ha hb => jetR_add ha hb) h0 h
  refine jetR_congr hs fun f _ => ?_
  simp [Finset.sum_apply]

theorem jetR_word (w : List Bool) (L : ℂ →ₗ[ℝ] M) : JetR U ζ0 (fun f => L (wd w f ζ0)) := by
  exact ⟨Unit, inferInstance, fun _ => w, fun _ => L, fun f _ => by simp⟩

def cl {E : Type*} [AddCommGroup E] [Module ℂ E] [Module ℝ E] [IsScalarTower ℝ ℂ E] (α : ℂ) (e : E) :
    ℂ →ₗ[ℝ] E where
  toFun c := (α * c) • e
  map_add' x y := by rw [mul_add, add_smul]
  map_smul' s c := by rw [RingHom.id_apply, mul_smul_comm, smul_assoc]

theorem cl_apply {E : Type*} [AddCommGroup E] [Module ℂ E] [Module ℝ E] [IsScalarTower ℝ ℂ E] (α : ℂ) (e : E)
    (c : ℂ) : cl α e c = (α * c) • e := rfl

end Closure

end Formalism.FourierDecayAlt.P.NFRO
end
end

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.Sq2UnitOfEqOneOfSq2EqDiv
section
open Matrix Set
open scoped ComplexConjugate ContDiff Manifold Topology

noncomputable section

namespace Formalism.FourierDecayAlt.P.AdmissibleLieWords

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.P.BetaSesquilinearity PI.UnitaryCorollaryDerivatives.CRH

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

def utv {k r m : ℕ} (ε T : ℝ) (Gp : Mat k r → ℝ) (om : Mat k r → Fin m → ℂ) (g : Mat k r) : Fin m → ℂ :=
  fun a => (Real.sqrt T : ℂ) * (Phh ε ((Gp g : ℝ) : ℂ) * om g a)

lemma utv_eq {k r m : ℕ} {ε T : ℝ} (hε : 0 < ε) (hT : 0 < T) (Gp : Mat k r → ℝ) (om : Mat k r → Fin m → ℂ)
    {g : Mat k r} (hg : ε / 2 < Gp g) : C6.unitOf T (Gp g) (om g) = utv ε T Gp om g := by
  have hx : 0 < Gp g := by linarith
  funext a
  simp only [C6.unitOf, utv, Phh, hh, Complex.ofReal_re, sc_one hε hg.le, one_mul, Pi.smul_apply,
    smul_eq_mul, sqrt_div_eq hT hx, Complex.ofReal_mul]
  ring

lemma utv_cd {k r m : ℕ} {ε T : ℝ} (hε : 0 < ε) {Gp : Mat k r → ℝ} {om : Mat k r → Fin m → ℂ}
    (hG : ContDiff ℝ ∞ (fun g => ((Gp g : ℝ) : ℂ))) (ho : ∀ a, ContDiff ℝ ∞ (fun g => om g a)) :
    ContDiff ℝ ∞ (utv ε T Gp om) := by
  refine contDiff_pi.2 fun a => ?_
  simp only [utv]
  exact contDiff_const.mul (((Phh_cd hε).comp hG).mul (ho a))

lemma sq2_unitOf_eq_one_of_sq2_eq_div {m : ℕ} {T Gv : ℝ} (hT : 0 < T) (hG : 0 < Gv) {v : Fin m → ℂ} (hv : C6.sq2 v = Gv / T) :
    C6.sq2 (C6.unitOf T Gv v) = 1 := by
  unfold C6.sq2 C6.unitOf at *
  simp only [Pi.smul_apply, smul_eq_mul, Complex.normSq_mul, Complex.normSq_ofReal]
  rw [← Finset.mul_sum, hv, Real.mul_self_sqrt (div_nonneg hT.le hG.le), div_mul_div_comm, mul_comm T Gv,
    div_self (mul_pos hG hT).ne']

lemma continuous_sum_squares (m : ℕ) : Continuous (C6.sq2 (m := m)) := by
  unfold C6.sq2
  exact continuous_finsetSum _ fun a _ => Complex.continuous_normSq.comp (continuous_apply a)

lemma norm_le_one_of_sq2_eq_one {m : ℕ} {v : Fin m → ℂ} (h : C6.sq2 v = 1) : ‖v‖ ≤ 1 := by
  refine (pi_norm_le_iff_of_nonneg zero_le_one).2 fun a => ?_
  have h1 : Complex.normSq (v a) ≤ 1 := by
    rw [← h]
    unfold C6.sq2
    exact Finset.single_le_sum (f := fun a => Complex.normSq (v a)) (fun i _ => Complex.normSq_nonneg _)
      (Finset.mem_univ a)
  have h2 : ‖v a‖ ^ 2 ≤ 1 := by rw [← Complex.normSq_eq_norm_sq]; exact h1
  nlinarith [norm_nonneg (v a)]

lemma spheres_compact (m m' : ℕ) :
    IsCompact {w : (Fin m → ℂ) × (Fin m' → ℂ) | C6.sq2 w.1 = 1 ∧ C6.sq2 w.2 = 1} := by
  apply Metric.isCompact_of_isClosed_isBounded
  · exact (isClosed_eq ((continuous_sum_squares m).comp continuous_fst) continuous_const).inter
      (isClosed_eq ((continuous_sum_squares m').comp continuous_snd) continuous_const)
  · refine (Metric.isBounded_closedBall (x := (0 : (Fin m → ℂ) × (Fin m' → ℂ))) (r := 1)).subset ?_
    intro w hw
    rw [Metric.mem_closedBall, dist_zero_right]
    exact norm_prod_le_iff.2 ⟨norm_le_one_of_sq2_eq_one hw.1, norm_le_one_of_sq2_eq_one hw.2⟩

lemma bump_ext {F E : Type} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
    [NormedAddCommGroup E] [NormedSpace ℝ E] (K O : Set F) (hK : IsCompact K) (hO : IsOpen O) (hKO : K ⊆ O)
    (Pi : F → E) (hPi : ContDiffOn ℝ ∞ Pi O) :
    ∃ Φ : F → E, ContDiff ℝ ∞ Φ ∧ (∀ y ∈ K, Φ y = Pi y) ∧
      ∀ j : ℕ, ∃ B : ℝ, ∀ y ∈ K, ‖iteratedFDeriv ℝ j Φ y‖ ≤ B := by
  obtain ⟨V, hVo, hKV, hVO, -⟩ := exists_open_between_and_isCompact_closure hK hO hKO
  obtain ⟨χ, hχ0, hχ1, -⟩ := exists_contMDiffMap_zero_one_of_isClosed (I := 𝓘(ℝ, F)) hVo.isClosed_compl
    hK.isClosed (disjoint_compl_left_iff_subset.2 hKV)
  have hχ : ContDiff ℝ ∞ (χ : F → ℝ) := contMDiff_iff_contDiff.1 χ.contMDiff
  have hΦ : ContDiff ℝ ∞ (fun y => χ y • Pi y) := by
    rw [contDiff_iff_contDiffAt]
    intro x
    by_cases hx : x ∈ O
    · exact hχ.contDiffAt.smul (hPi.contDiffAt (hO.mem_nhds hx))
    · have hx' : x ∈ (closure V)ᶜ := fun h => hx (hVO h)
      have h0 : (fun y => χ y • Pi y) =ᶠ[𝓝 x] fun _ => (0 : E) := by
        filter_upwards [isClosed_closure.isOpen_compl.mem_nhds hx'] with y hy
        have hyV : y ∈ Vᶜ := fun h => hy (subset_closure h)
        simp [hχ0 hyV]
      exact contDiffAt_const.congr_of_eventuallyEq h0
  refine ⟨fun y => χ y • Pi y, hΦ, fun y hy => by simp [hχ1 hy], fun j => ?_⟩
  exact hK.exists_bound_of_continuousOn
    ((hΦ.continuous_iteratedFDeriv (m := j) (by exact_mod_cast le_top)).continuousOn)

end Formalism.FourierDecayAlt.P.AdmissibleLieWords

namespace Formalism.FourierDecayAlt.P

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.P.BetaSesquilinearity PI.UnitaryCorollaryDerivatives.CRH Formalism.FourierDecayAlt.P.AdmissibleLieWords

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

theorem c6_fib_cost_of_pieces : C6.FibCostOfParts := by
  intro hU k r m m' om om' Gp T T' E _ _ Pi O hom hom' hGp hT hT' hsq hsq' hO hKO hPi ε hε i
  have hGcd : ContDiff ℝ ∞ (fun g => ((Gp g : ℝ) : ℂ)) := (poly_adm (n := 0) hGp).1
  have hGc : Continuous Gp := by
    have h := Complex.continuous_re.comp hGcd.continuous
    simp only [Function.comp_def, Complex.ofReal_re] at h
    exact h
  have ho : ∀ a, ContDiff ℝ ∞ (fun g => om g a) := fun a => (poly_adm (n := 0) (hom a)).1
  have ho' : ∀ a, ContDiff ℝ ∞ (fun g => om' g a) := fun a => (poly_adm (n := 0) (hom' a)).1
  have hu1 : ContDiff ℝ ∞ (utv ε T Gp om) := utv_cd hε hGcd ho
  have hu2 : ContDiff ℝ ∞ (utv ε T' Gp om') := utv_cd hε hGcd ho'
  have hψ : ContDiff ℝ ∞ (fun g => (utv ε T Gp om g, utv ε T' Gp om' g)) := hu1.prodMk hu2
  have hOε : IsOpen {g : Mat k r | ε / 2 < Gp g} := isOpen_lt continuous_const hGc

  have hsph : ∀ g ∈ GV k r, ε / 2 < Gp g →
      C6.unitOf T (Gp g) (om g) = utv ε T Gp om g ∧ C6.unitOf T' (Gp g) (om' g) = utv ε T' Gp om' g ∧
      (C6.unitOf T (Gp g) (om g), C6.unitOf T' (Gp g) (om' g)) ∈
        {w : (Fin m → ℂ) × (Fin m' → ℂ) | C6.sq2 w.1 = 1 ∧ C6.sq2 w.2 = 1} := by
    intro g hg hgt
    have hpos : 0 < Gp g := by linarith
    exact ⟨utv_eq hε hT Gp om hgt, utv_eq hε hT' Gp om' hgt, sq2_unitOf_eq_one_of_sq2_eq_div hT hpos (hsq g hg),
      sq2_unitOf_eq_one_of_sq2_eq_div hT' hpos (hsq' g hg)⟩
  obtain ⟨Φ, hΦ, hΦK, hΦb⟩ := bump_ext _ O (spheres_compact m m') hO hKO Pi hPi

  have hwl : ∀ u v : List (Mat k r), (∀ X ∈ u, unitLie k r X) → (∀ X ∈ v, unitLie k r X) →
      ∀ x ∈ wL u ++ wR v, inLie k r x.2 := by
    intro u v hu hv x hx
    rcases List.mem_append.mp hx with hx | hx
    · simp only [wL, List.mem_map] at hx
      obtain ⟨X, hX, rfl⟩ := hx
      exact (hu X hX).1
    · simp only [wR, List.mem_map, List.mem_reverse] at hx
      obtain ⟨X, hX, rfl⟩ := hx
      exact (hv X hX).1
  have hlen : ∀ u v : List (Mat k r), (wL u ++ wR v).length = u.length + v.length := by
    intro u v
    simp [wL, wR]
  choose C1 hC1 using hU k r m om Gp T hom hGp hT hsq ε hε
  choose C2 hC2 using hU k r m' om' Gp T' hom' hGp hT' hsq' ε hε
  obtain ⟨M, hM⟩ : ∃ M : ℝ, M = ∑ j ∈ Finset.range (i + 1), (|C1 j| + |C2 j|) := ⟨_, rfl⟩
  have hCM : ∀ j ≤ i, C1 j ≤ M ∧ C2 j ≤ M := by
    intro j hj
    have hmem : j ∈ Finset.range (i + 1) := Finset.mem_range.mpr (by omega)
    have hle := Finset.single_le_sum (f := fun j => |C1 j| + |C2 j|)
      (fun j _ => add_nonneg (abs_nonneg _) (abs_nonneg _)) hmem
    rw [← hM] at hle
    exact ⟨by linarith [le_abs_self (C1 j), abs_nonneg (C2 j)], by linarith [le_abs_self (C2 j), abs_nonneg (C1 j)]⟩
  have H : ∀ w, admitted i w → w ≠ [] → ∀ g ∈ {g : Mat k r | g ∈ GV k r ∧ ε ≤ Gp g},
      ‖Dw w (fun g => (utv ε T Gp om g, utv ε T' Gp om' g)) g‖ ≤
        M * gN g ^ (2 * (r + 1) * w.length + (r + 1)) := by
    rintro w ⟨u, v, hu, hv, hl, rfl⟩ - g ⟨hg, hge⟩
    have hgt : ε / 2 < Gp g := by linarith
    have hw := hwl u v hu hv
    have huv : C6.UnitWords k r u v (u.length + v.length) := ⟨hu, hv, rfl⟩
    have e1 : Dw (wL u ++ wR v) (utv ε T Gp om) g =
        Dw (wL u ++ wR v) (fun g' => C6.unitOf T (Gp g') (om g')) g :=
      Dw_congr_loc hw hOε (fun g' hg' hg'O => ((hsph g' hg' hg'O).1).symm) g hg hgt
    have e2 : Dw (wL u ++ wR v) (utv ε T' Gp om') g =
        Dw (wL u ++ wR v) (fun g' => C6.unitOf T' (Gp g') (om' g')) g :=
      Dw_congr_loc hw hOε (fun g' hg' hg'O => ((hsph g' hg' hg'O).2.1).symm) g hg hgt
    have f1 : Dw (wL u ++ wR v) (utv ε T Gp om) g =
        (Dw (wL u ++ wR v) (fun g => (utv ε T Gp om g, utv ε T' Gp om' g)) g).1 := by
      have h := congrFun (dw_clm (ContinuousLinearMap.fst ℝ (Fin m → ℂ) (Fin m' → ℂ)) (wL u ++ wR v) hψ) g
      simpa using h
    have f2 : Dw (wL u ++ wR v) (utv ε T' Gp om') g =
        (Dw (wL u ++ wR v) (fun g => (utv ε T Gp om g, utv ε T' Gp om' g)) g).2 := by
      have h := congrFun (dw_clm (ContinuousLinearMap.snd ℝ (Fin m → ℂ) (Fin m' → ℂ)) (wL u ++ wR v) hψ) g
      simpa using h
    have b1 := hC1 _ u v huv g hg hge
    have b2 := hC2 _ u v huv g hg hge
    rw [dLR_eq, ← e1, f1] at b1
    rw [dLR_eq, ← e2, f2] at b2
    have hexp : (r + 1) * (2 * (u.length + v.length) + 1) =
        2 * (r + 1) * (wL u ++ wR v).length + (r + 1) := by
      rw [hlen]; ring
    rw [hexp] at b1 b2
    have hY : 0 ≤ gN g ^ (2 * (r + 1) * (wL u ++ wR v).length + (r + 1)) :=
      pow_nonneg (le_trans zero_le_one (gN_ge_one hg)) _
    obtain ⟨m1, m2⟩ := hCM _ hl
    rw [Prod.norm_def]
    exact max_le (b1.trans (mul_le_mul_of_nonneg_right m1 hY)) (b2.trans (mul_le_mul_of_nonneg_right m2 hY))
  obtain ⟨C, -, hC⟩ := fdb (fun g => (utv ε T Gp om g, utv ε T' Gp om' g)) hψ
    {g : Mat k r | g ∈ GV k r ∧ ε ≤ Gp g} _
    (fun g hg => by rw [← (hsph g hg.1 (by linarith [hg.2])).1, ← (hsph g hg.1 (by linarith [hg.2])).2.1]
                    exact (hsph g hg.1 (by linarith [hg.2])).2.2)
    gN (fun g hg => gN_ge_one hg.1) (2 * (r + 1)) (r + 1) M i H i E Φ hΦ hΦb
  refine ⟨C, fun u v huv g hg hge => ?_⟩
  have hw := hwl u v huv.1 huv.2.1
  rw [dLR_eq]
  have e : Dw (wL u ++ wR v) (fun g' => Pi (C6.unitOf T (Gp g') (om g'), C6.unitOf T' (Gp g') (om' g'))) g =
      Dw (wL u ++ wR v) (fun g' => Φ (utv ε T Gp om g', utv ε T' Gp om' g')) g := by
    refine Dw_congr_loc hw hOε (fun g' hg' hg'O => ?_) g hg (show ε / 2 < Gp g by linarith)
    obtain ⟨h1, h2, h3⟩ := hsph g' hg' hg'O
    rw [← hΦK _ h3, h1, h2]
  rw [e]
  have hl : (wL u ++ wR v).length = i := by rw [hlen]; exact huv.2.2
  have hb := hC (wL u ++ wR v) (admissible_of_unit_words huv) hl.le g ⟨hg, hge⟩
  rw [hl] at hb
  have hexp : (2 * (r + 1) + (r + 1)) * i = 3 * (r + 1) * i := by ring
  rwa [hexp] at hb

theorem fibre_cost_estimate : C6.FibCost := c6_fib_cost_of_pieces fibre_unit_normalization

end Formalism.FourierDecayAlt.P
end
end

