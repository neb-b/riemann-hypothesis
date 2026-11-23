module

public import Formalism.HermitianCurvature.CompositeFormulaLevelZero
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0027

@[expose] public section

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.FsvMulFsvNeg
section
open scoped ComplexConjugate ContDiff
open Filter Topology

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

noncomputable section

namespace Formalism.FourierDecayAlt.P5

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.Wd

theorem fsv_mul_fsv_neg (s t : ℂ) : fsv s t * fsv (-s) t = 1 := by
  rw [fsv, fsv, ← Complex.exp_add]
  convert Complex.exp_zero using 2
  simp only [map_neg]
  ring

theorem fsv_neg_mul_fsv (s t : ℂ) : fsv (-s) t * fsv s t = 1 := by
  rw [mul_comm]
  exact fsv_mul_fsv_neg s t

theorem hasFDerivAt_fsv {m : ℕ} (t : ℂ) (l : Fin m) (c : Fin m → ℂ) :
    ∃ D : (Fin m → ℂ) →L[ℝ] ℂ, HasFDerivAt (fun c' : Fin m → ℂ => fsv t (c' l)) D c ∧
      D (Pi.single l 1) = (t - conj t) * fsv t (c l) ∧
      D (Pi.single l Complex.I) = Complex.I * (t + conj t) * fsv t (c l) := by
  classical
  let L : (Fin m → ℂ) →L[ℝ] ℂ := t • (ContinuousLinearMap.proj l : (Fin m → ℂ) →L[ℝ] ℂ) -
    (conj t) • (Complex.conjCLE.toContinuousLinearMap.comp (ContinuousLinearMap.proj l : (Fin m → ℂ) →L[ℝ] ℂ))
  have hL : ∀ c' : Fin m → ℂ, L c' = t * c' l - conj t * conj (c' l) := by
    intro c'
    simp [L]
  refine ⟨fsv t (c l) • L, ?_, ?_, ?_⟩
  · have h2 := (L.hasFDerivAt (x := c)).cexp
    have he : (fun c' : Fin m → ℂ => fsv t (c' l)) = fun c' => Complex.exp (L c') := by
      funext c'
      rw [hL]
      rfl
    have hc : Complex.exp (L c) = fsv t (c l) := by
      rw [hL]
      rfl
    rw [he, ← hc]
    exact h2
  · simp only [ContinuousLinearMap.smul_apply, hL, Pi.single_eq_same, map_one, smul_eq_mul]
    ring
  · simp only [ContinuousLinearMap.smul_apply, hL, Pi.single_eq_same, Complex.conj_I, smul_eq_mul]
    ring

section Leibniz

variable {m : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

theorem wirt_fsv_smul (t : ℂ) (l : Fin m) (φ : (Fin m → ℂ) → E) (c : Fin m → ℂ)
    (hφ : DifferentiableAt ℝ φ c) :
    wirt l (fun c' => fsv t (c' l) • φ c') c = fsv t (c l) • wirt l φ c + (t * fsv t (c l)) • φ c ∧
    wirtBar l (fun c' => fsv t (c' l) • φ c') c =
      fsv t (c l) • wirtBar l φ c + (-(conj t) * fsv t (c l)) • φ c := by
  obtain ⟨D, hD, h1, hI⟩ := hasFDerivAt_fsv t l c
  have hP : HasFDerivAt (fun c' => fsv t (c' l) • φ c') (fsv t (c l) • fderiv ℝ φ c + D.smulRight (φ c)) c :=
    hD.smul hφ.hasFDerivAt
  unfold wirt wirtBar
  rw [hP.fderiv]
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
    ContinuousLinearMap.smulRight_apply, h1, hI, smul_add, smul_sub, smul_smul, ← mul_assoc, Complex.I_mul_I]
  constructor <;> module

theorem pOp_fsv_smul (t : ℂ) (l : Fin m) (φ : (Fin m → ℂ) → E) (c : Fin m → ℂ)
    (hd : c ∈ OmX m → DifferentiableAt ℝ φ c) (h0 : c ∉ OmX m → φ c = 0) :
    pOp l (fun c' => fsv t (c' l) • φ c') c =
      fsv t (c l) • pOp l φ c + t • fsv t (c l) • (c l • φ c) := by
  unfold pOp
  by_cases h : c ∈ OmX m
  · rw [if_pos h, if_pos h, (wirt_fsv_smul t l φ c (hd h)).1]
    module
  · rw [if_neg h, if_neg h, h0 h]
    simp

theorem pbOp_fsv_smul (t : ℂ) (l : Fin m) (φ : (Fin m → ℂ) → E) (c : Fin m → ℂ)
    (hd : c ∈ OmX m → DifferentiableAt ℝ φ c) (h0 : c ∉ OmX m → φ c = 0) :
    pbOp l (fun c' => fsv (-t) (c' l) • φ c') c =
      fsv (-t) (c l) • pbOp l φ c + conj t • fsv (-t) (c l) • (star (c l) • φ c) := by
  unfold pbOp
  by_cases h : c ∈ OmX m
  · rw [if_pos h, if_pos h, (wirt_fsv_smul (-t) l φ c (hd h)).2]
    simp only [map_neg, neg_neg, Complex.star_def]
    module
  · rw [if_neg h, if_neg h, h0 h]
    simp

end Leibniz

section Reg

variable {k r : ℕ} {z z' : Fin (2 * r + k + 1) → ℂ} {Wp Wq : Type} [NormedAddCommGroup Wp] [NormedSpace ℂ Wp]
  [NormedAddCommGroup Wq] [NormedSpace ℂ Wq] {π : Mx k r → (Wp →L[ℂ] Wp)} {π' : Mx k r → (Wq →L[ℂ] Wq)}

theorem radSp_regular (Φ : RadSp k r z z' π π') (g : Mx k r) (c : Fin r → ℂ) :
    (c ∈ OmX r → DifferentiableAt ℝ (fun c' => (Φ : Fn k r (Wq →L[ℂ] Wp)) c' g) c) ∧
      (c ∉ OmX r → (Φ : Fn k r (Wq →L[ℂ] Wp)) c g = 0) := by
  have hΦm : (Φ : Fn k r (Wq →L[ℂ] Wp)) ∈ RadSp k r z z' π π' := Φ.2
  obtain ⟨h0, hs, -⟩ := hΦm
  refine ⟨fun hc => ?_, fun hc => h0 (c, g) (fun hx => hc (by
    simp only [DomR, Set.mem_setOf_eq] at hx
    exact hx.1))⟩
  by_cases hg : g ∈ Glev k r (Fin.last r) ∧ 0 < GGl k r z z' g
  · obtain ⟨U, F, hU, hxU, hF, hΦ⟩ := hs (c, g) (by
      simp only [DomR, Set.mem_setOf_eq]
      exact ⟨hc, hg.1, hg.2⟩)
    have hcont : Continuous (fun c' : Fin r → ℂ => (c', g)) := by fun_prop
    have hev : ∀ᶠ c' in nhds c, (Φ : Fn k r (Wq →L[ℂ] Wp)) c' g = F (c', g) := by
      have hU' : ∀ᶠ c' in nhds c, (c', g) ∈ U := hcont.continuousAt.preimage_mem_nhds (hU.mem_nhds hxU)
      filter_upwards [hU'] with c' hc'
      exact hΦ (c', g) hc' hg.1
    have hFd : DifferentiableAt ℝ F (c, g) := (hF.contDiffAt (hU.mem_nhds hxU)).differentiableAt (by simp)
    have hpair : DifferentiableAt ℝ (fun c' : Fin r → ℂ => (c', g)) c := by fun_prop
    have hcomp : DifferentiableAt ℝ (fun c' => F (c', g)) c := hFd.comp c hpair
    exact hcomp.congr_of_eventuallyEq hev
  · have hz : (fun c' => (Φ : Fn k r (Wq →L[ℂ] Wp)) c' g) = fun _ => 0 := by
      funext c'
      refine h0 (c', g) (fun hx => hg ?_)
      simp only [DomR, Set.mem_setOf_eq] at hx
      exact ⟨hx.2.1, hx.2.2⟩
    rw [hz]
    exact differentiableAt_const 0

end Reg

section PairLemmas

variable {V : Type*} [AddCommGroup V] [Module ℂ V]

theorem pr_ext {a b : Pr V} (h1 : a.1 = b.1) (h2 : a.2.unop = b.2.unop) : a = b :=
  Prod.ext h1 (MulOpposite.unop_injective h2)

@[simp] theorem pr_alg_fst (w : ℂ) : (algebraMap ℂ (Pr V) w).1 = algebraMap ℂ (Module.End ℂ V) w := rfl
@[simp] theorem pr_alg_snd (w : ℂ) :
    (algebraMap ℂ (Pr V) w).2.unop = algebraMap ℂ (Module.End ℂ V) (conj w) := rfl

end PairLemmas

theorem waveSiteAll : WaveSiteAll := by
  intro Wp Wq _ _ _ _ P z z' π π' X L hL l s Wv Wv' hW hW'
  obtain ⟨hp, -, hc, hci, -⟩ := hL
  have hW1 : ∀ (Φ : RadSp P.k P.r z z' π π') c g, (Wv Φ : Fn P.k P.r (Wq →L[ℂ] Wp)) c g =
      fsv s (c l) • (Φ : Fn P.k P.r (Wq →L[ℂ] Wp)) c g := hW
  have hW2 : ∀ (Φ : RadSp P.k P.r z z' π π') c g, (Wv' Φ : Fn P.k P.r (Wq →L[ℂ] Wp)) c g =
      fsv (-s) (c l) • (Φ : Fn P.k P.r (Wq →L[ℂ] Wp)) c g := hW'
  have hop : ∀ i (Φ : RadSp P.k P.r z z' π π'),
      (X.op l i Φ : Fn P.k P.r (Wq →L[ℂ] Wp)) = crd (opL l i) (Φ : Fn P.k P.r (Wq →L[ℂ] Wp)) :=
    fun i Φ => X.op_apply l i Φ
  have hWW' : Wv * Wv' = 1 := by
    apply LinearMap.ext; intro Φ; apply Subtype.ext; funext c g
    simp only [Module.End.mul_apply, Module.End.one_apply, hW1, hW2, smul_smul, fsv_mul_fsv_neg, one_smul]
  have hW'W : Wv' * Wv = 1 := by
    apply LinearMap.ext; intro Φ; apply Subtype.ext; funext c g
    simp only [Module.End.mul_apply, Module.End.one_apply, hW1, hW2, smul_smul, fsv_neg_mul_fsv, one_smul]

  have hcomm : ∀ (W : Module.End ℂ (RadSp P.k P.r z z' π π')) (u : ℂ → ℂ),
      (∀ (Φ : RadSp P.k P.r z z' π π') c g, (W Φ : Fn P.k P.r (Wq →L[ℂ] Wp)) c g =
        u (c l) • (Φ : Fn P.k P.r (Wq →L[ℂ] Wp)) c g) →
      ∀ i : Fin 6, (i = 1 ∨ i = 2 ∨ i = 4 ∨ i = 5) → W * X.op l i = X.op l i * W := by
    intro W u hWu i hi
    apply LinearMap.ext; intro Φ; apply Subtype.ext; funext c g
    simp only [Module.End.mul_apply, hWu, hop, crd]
    rcases hi with rfl | rfl | rfl | rfl <;>
      simp only [opL, cOp, ciOp, cbOp, cbiOp] <;> exact smul_comm _ _ _
  have hsite : ∀ f : Pr (RadSp P.k P.r z z' π π'), (site L l).p = L.p l ∧ (site L l).c = L.c l ∧
      (site L l).ci = L.ci l := fun _ => ⟨rfl, rfl, rfl⟩
  obtain ⟨hsp, hsc, hsci⟩ := hsite 0
  rw [hsp, hsc, hsci, hp l, hc l, hci l]
  refine ⟨⟨pr_ext ?_ ?_, pr_ext ?_ ?_, rfl⟩, pr_ext ?_ ?_, pr_ext ?_ ?_, pr_ext ?_ ?_⟩
  · exact hWW'
  · exact hWW'
  · exact hW'W
  · exact hW'W
  · exact hcomm Wv _ hW1 1 (by decide)
  · exact (hcomm Wv' _ hW2 4 (by decide)).symm
  · exact hcomm Wv _ hW1 2 (by decide)
  · exact (hcomm Wv' _ hW2 5 (by decide)).symm
  · change X.op l 0 * Wv = Wv * X.op l 0 + algebraMap ℂ _ s * Wv * X.op l 1
    apply LinearMap.ext; intro Φ; apply Subtype.ext; funext c g
    obtain ⟨hd, h0⟩ := radSp_regular Φ g c
    simp only [Module.End.mul_apply, LinearMap.add_apply, Module.algebraMap_end_apply, Submodule.coe_add,
      Submodule.coe_smul, Pi.add_apply, Pi.smul_apply, hop, crd, hW1, opL]
    rw [pOp_fsv_smul s l _ c hd h0]
    simp only [cOp]
  · change Wv' * (-X.op l 3) = (-X.op l 3) * Wv' + X.op l 4 * (Wv' * algebraMap ℂ _ (conj s))
    apply LinearMap.ext; intro Φ; apply Subtype.ext; funext c g
    obtain ⟨hd, h0⟩ := radSp_regular Φ g c
    simp only [Module.End.mul_apply, LinearMap.add_apply, LinearMap.neg_apply, Module.algebraMap_end_apply,
      Submodule.coe_add, Submodule.coe_neg, Submodule.coe_smul, Pi.add_apply, Pi.neg_apply, Pi.smul_apply, hop,
      crd, hW2, opL]
    rw [pbOp_fsv_smul s l _ c hd h0]
    simp only [cbOp]
    module

end Formalism.FourierDecayAlt.P5
end
end

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.HermMulVecMulVec
section
open Matrix MeasureTheory Filter Topology
open scoped InnerProductSpace ComplexConjugate ComplexOrder ContDiff

noncomputable section

namespace Formalism.FourierDecayAlt.P5

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.Wd Formalism.YangianSpanCharacter.T

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

section Wave

variable {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq] {k r : ℕ} {z z' : Fin (2 * r + k + 1) → ℂ} {π : Mx k r → (Wp →L[ℂ] Wp)}
  {π' : Mx k r → (Wq →L[ℂ] Wq)}

lemma mul_mem (m : (Fin r → ℂ) × Mx k r → ℂ) (hm : ContDiff ℝ ∞ m)
    (hinv : ∀ x ∈ DomR k r z z', ∀ h ∈ UWset k r z, ∀ h' ∈ UWset k r z', m (x.1, h * x.2 * h') = m x)
    (Φ : RadSp k r z z' π π') :
    (fun c g => m (c, g) • (Φ : Fn k r (Wq →L[ℂ] Wp)) c g) ∈ RadSp k r z z' π π' := by
  have hΦm : (Φ : Fn k r (Wq →L[ℂ] Wp)) ∈ RadSp k r z z' π π' := Φ.2
  obtain ⟨h0, hs, he⟩ := hΦm
  refine (show _ ∧ _ ∧ _ from ⟨fun x hx => ?_, fun x₀ hx₀ => ?_, fun x hx h hh h' hh' => ?_⟩)
  · show m (x.1, x.2) • (Φ : Fn k r (Wq →L[ℂ] Wp)) x.1 x.2 = 0
    rw [h0 x hx, smul_zero]
  · obtain ⟨U, F, hU, hxU, hF, hΦ⟩ := hs x₀ hx₀
    refine ⟨U, fun x => m x • F x, hU, hxU, hm.contDiffOn.smul hF, fun x hx hg => ?_⟩
    show m (x.1, x.2) • (Φ : Fn k r (Wq →L[ℂ] Wp)) x.1 x.2 = m x • F x
    rw [hΦ x hx hg]
  · show m (x.1, h * x.2 * h') • (Φ : Fn k r (Wq →L[ℂ] Wp)) x.1 (h * x.2 * h') =
      (π h).comp ((m (x.1, x.2) • (Φ : Fn k r (Wq →L[ℂ] Wp)) x.1 x.2).comp (π' h'))
    rw [hinv x hx h hh h' hh', he x hx h hh h' hh']
    ext v
    simp

def mulOp (m : (Fin r → ℂ) × Mx k r → ℂ) (hm : ContDiff ℝ ∞ m)
    (hinv : ∀ x ∈ DomR k r z z', ∀ h ∈ UWset k r z, ∀ h' ∈ UWset k r z', m (x.1, h * x.2 * h') = m x) :
    Module.End ℂ (RadSp k r z z' π π') where
  toFun Φ := ⟨_, mul_mem m hm hinv Φ⟩
  map_add' Φ Ψ := by
    ext c g v
    simp [smul_add]
  map_smul' a Φ := by
    ext c g v
    simp [smul_smul, mul_comm]

lemma mulOp_isMulOp (m : (Fin r → ℂ) × Mx k r → ℂ) (hm : ContDiff ℝ ∞ m)
    (hinv : ∀ x ∈ DomR k r z z', ∀ h ∈ UWset k r z, ∀ h' ∈ UWset k r z', m (x.1, h * x.2 * h') = m x) :
    multiplicationOperator (mulOp (π := π) (π' := π') m hm hinv) (fun c g => m (c, g)) := by
  intro _ _ _
  rfl

lemma contDiff_fsv (s : ℂ) : ContDiff ℝ ∞ (fsv s) := by
  have hL : ContDiff ℝ ∞ (fun t : ℂ => s * t - conj s * conj t) :=
    (contDiff_const.mul contDiff_id).sub (contDiff_const.mul Complex.conjCLE.contDiff)
  exact Complex.contDiff_exp.comp hL

lemma contDiff_fsv_coord (l : Fin r) (s : ℂ) :
    ContDiff ℝ ∞ (fun x : (Fin r → ℂ) × Mx k r => fsv s (x.1 l)) :=
  (contDiff_fsv s).comp (by fun_prop : ContDiff ℝ ∞ (fun x : (Fin r → ℂ) × Mx k r => x.1 l))

def hermLin (H : Mx k r) (v w : Fin (2 * r + k + 1) → ℂ) : Mx k r →ₗ[ℂ] ℂ where
  toFun g := herm H (g *ᵥ v) w
  map_add' g g' := by simp [herm, Matrix.add_mulVec, Matrix.mulVec_add, dotProduct_add]
  map_smul' a g := by simp [herm, Matrix.smul_mulVec, Matrix.mulVec_smul, dotProduct_smul]

lemma contDiff_zeta : ContDiff ℝ ∞ (fun x : (Fin r → ℂ) × Mx k r => zeta k r z z' x.2) := by
  unfold zeta zetaL
  let Lc : Mx k r →L[ℂ] ℂ := LinearMap.toContinuousLinearMap
    (hermLin (Hpk k r) (fvec k r z' (Fin.last r)) (fvec k r z (Fin.last r)))
  have h1 : ContDiff ℝ ∞ (fun g : Mx k r => Lc g) := (Lc.restrictScalars ℝ).contDiff
  exact h1.comp contDiff_snd

lemma herm_mulVec_mulVec (H h : Mx k r) (hh : hᴴ * H * h = H) (v w : Fin (2 * r + k + 1) → ℂ) :
    herm H (h *ᵥ v) (h *ᵥ w) = herm H v w := by
  unfold herm
  rw [Matrix.star_mulVec, ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, hh]

lemma zeta_inv (g : Mx k r) (h h' : Mx k r) (hh : h ∈ UWset k r z) (hh' : h' ∈ UWset k r z') :
    zeta k r z z' (h * g * h') = zeta k r z z' g := by
  simp only [UWset, Set.mem_setOf_eq] at hh hh'
  obtain ⟨hU, hb, hz⟩ := hh
  obtain ⟨hU', hb', hz'⟩ := hh'
  simp only [UH, Set.mem_setOf_eq] at hU
  have hf' : h' *ᵥ fvec k r z' (Fin.last r) = fvec k r z' (Fin.last r) := by
    unfold fvec
    rw [dite_eq_right (by simp)]
    exact hz'
  have hf : h *ᵥ fvec k r z (Fin.last r) = fvec k r z (Fin.last r) := by
    unfold fvec
    rw [dite_eq_right (by simp)]
    exact hz
  unfold zeta zetaL
  rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, hf']
  conv_lhs => rw [← hf]
  exact herm_mulVec_mulVec _ _ hU _ _

end Wave

theorem waveCExists : WaveCExists := by
  intro Wp Wq _ _ _ _ k r z z' π π' l s
  exact ⟨mulOp (π := π) (π' := π') (fun x => fsv s (x.1 l)) (contDiff_fsv_coord l s)
    (fun _ _ _ _ _ _ => rfl), mulOp_isMulOp _ _ _⟩

theorem waveZExists : WaveZExists := by
  intro Wp Wq _ _ _ _ k r z z' π π' s
  exact ⟨mulOp (π := π) (π' := π') (fun x => fsv s (zeta k r z z' x.2))
    ((contDiff_fsv s).comp (contDiff_zeta (k := k) (r := r) (z := z) (z' := z')))
    (fun x _ h hh h' hh' => by
      show fsv s (zeta k r z z' (h * x.2 * h')) = fsv s (zeta k r z z' x.2)
      rw [zeta_inv _ _ _ hh hh']), mulOp_isMulOp _ _ _⟩

section Zero

variable {k r : ℕ} {z z' : Fin (2 * r + k + 1) → ℂ} {Wp Wq : Type} [NormedAddCommGroup Wp]
  [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq]
  {π : Mx k r → (Wp →L[ℂ] Wp)} {π' : Mx k r → (Wq →L[ℂ] Wq)} {S : Type} [Fintype S] [DecidableEq S]

end Zero

end Formalism.FourierDecayAlt.P5
end
end

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.HermitianFormFlagVector
section
open Matrix Formalism.FourierDecayAlt Formalism.QuantumDeterminants
open scoped ComplexConjugate

namespace Formalism.FourierDecayAlt.P

namespace C2x5

variable {k r : ℕ}

lemma herm_sum_smul {n : ℕ} {ι : Type*} [Fintype ι] (H : Matrix (Fin n) (Fin n) ℂ) (x : ι → ℂ)
    (v : ι → Fin n → ℂ) (w : Fin n → ℂ) :
    herm H (∑ c, x c • v c) w = ∑ c, x c * herm H (v c) w := by
  simp only [herm, Matrix.mulVec_sum, Matrix.mulVec_smul, dotProduct_sum, dotProduct_smul, smul_eq_mul]

lemma hzz_real (z : Fin (2 * r + k + 1) → ℂ) : herm (Hpk k r) z z = ((-(Tz k r z) : ℝ) : ℂ) := by
  have h := ggHerm_swap (Hpk k r) (GBasic.Hpk_herm k r) z z
  apply Complex.ext
  · simp [Tz]
  · have h2 := congrArg Complex.im h
    simp only [Complex.star_def, Complex.conj_im] at h2
    simp only [Complex.ofReal_im]; linarith

lemma hzz_ne {z : Fin (2 * r + k + 1) → ℂ} (hz : 0 < Tz k r z) : herm (Hpk k r) z z ≠ 0 := by
  rw [hzz_real]; exact_mod_cast (neg_ne_zero.mpr hz.ne')

lemma herm_f_es {z : Fin (2 * r + k + 1) → ℂ} (hz : inWb k r z) (c : Fin (r + 1)) (a : Fin r) :
    herm (Hpk k r) (fvec k r z c) (bvec (esI k r a)) = if c.val = a.val then 1 else 0 := by
  rw [bvec, ggHerm_bvec_right]
  have hlt : r + k < (esI k r a).val := by simp [esI]; omega
  rw [gn_Hpk_mulVec, dite_eq_left (Or.inr hlt)]
  have e : (⟨2 * r + k - (esI k r a).val, by omega⟩ : Fin (2 * r + k + 1)) = ⟨a.val, by omega⟩ := by
    apply Fin.ext; simp [esI]; omega
  rw [e, fvec_apply_lt z hz c _ (by simp)]

lemma herm_e_alt {z : Fin (2 * r + k + 1) → ℂ} (hz : inWb k r z) (x : Fin (2 * r + k + 1))
    (hx : x.val < r ∨ r + k < x.val) : herm (Hpk k r) (bvec x) z = 0 := by
  rw [ggHerm_swap (Hpk k r) (GBasic.Hpk_herm k r), bvec, ggHerm_bvec_right, ggHpk_mulVec_Wb k r z hz,
    hz x hx, mul_zero, star_zero]

lemma hermitian_form_flag_vector {z : Fin (2 * r + k + 1) → ℂ} (hz : inWb k r z) (c : Fin (r + 1)) :
    herm (Hpk k r) (fvec k r z c) z = if c.val = r then herm (Hpk k r) z z else 0 := by
  unfold fvec
  split_ifs with h1 h2 h2
  · omega
  · exact herm_e_alt hz _ (Or.inl (by simp [eI, h1]))
  · rfl
  · omega

lemma uMap_eq {z : Fin (2 * r + k + 1) → ℂ} (hz : C2.StdZ k r z) (s : B.Mat k r)
    (U : Matrix (Fin (r + 1)) (Fin (r + 1)) ℂ) (h : ∀ b, s *ᵥ fvec k r z b = ∑ c, U c b • fvec k r z c) :
    C2.uMap k r z s = U := by
  ext a b
  unfold C2.uMap
  rw [h b]
  split_ifs with ha
  · rw [herm_sum_smul]
    simp only [herm_f_es hz.1]
    rw [Finset.sum_eq_single a]
    · simp
    · intro c _ hc; rw [if_neg (fun e => hc (Fin.ext e)), mul_zero]
    · simp
  · rw [herm_sum_smul]
    simp only [hermitian_form_flag_vector hz.1]
    rw [Finset.sum_eq_single a]
    · rw [if_pos (by have := a.isLt; omega)]
      field_simp [hzz_ne hz.2]
    · intro c _ hc
      rw [if_neg, mul_zero]
      intro e; apply hc; apply Fin.ext; have := a.isLt; omega
    · simp

lemma colEq {z : Fin (2 * r + k + 1) → ℂ} {s : B.Mat k r} {U : Matrix (Fin (r + 1)) (Fin (r + 1)) ℂ}
    (h : s * Fm k r z = Fm k r z * U) (b : Fin (r + 1)) :
    s *ᵥ fvec k r z b = ∑ c, U c b • fvec k r z c := by
  funext i
  have := congrFun (congrFun h i) b
  simp only [Matrix.mul_apply, Fm, Matrix.of_apply] at this
  simp only [Matrix.mulVec, dotProduct, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  rw [this]
  exact Finset.sum_congr rfl (fun c _ => mul_comm _ _)

end C2x5

open C2x5

theorem unipotent_map_frame : C2.UMapFrame := by
  intro k r z hz
  refine ⟨fun s hs => ?_, fun h hh => ?_⟩
  · obtain ⟨U, hU1, hU2, hsF⟩ := S_F hz.1 hs
    have hu := uMap_eq hz s U (colEq hsF)
    refine ⟨by rw [hu]; exact colEq hsF, by rw [hu]; exact ⟨fun i j h => hU1 i j h, hU2⟩, fun t ht => ?_⟩
    obtain ⟨Ut, _, _, htF⟩ := S_F hz.1 ht
    have hut := uMap_eq hz t Ut (colEq htF)
    have hst : s * t * Fm k r z = Fm k r z * (U * Ut) := by
      rw [Matrix.mul_assoc, htF, ← Matrix.mul_assoc, hsF, Matrix.mul_assoc]
    rw [uMap_eq hz (s * t) (U * Ut) (colEq hst), hu, hut]
  · have h1 : h * Fm k r z = Fm k r z * (1 : Matrix (Fin (r + 1)) (Fin (r + 1)) ℂ) := by
      rw [UW_F hh, Matrix.mul_one]
    exact uMap_eq hz h 1 (colEq h1)

theorem zhat_equivalence : C2.ZhatEquiv := by
  intro k r z z' hz hz' s hs s' hs' g
  obtain ⟨U, _, _, hsF⟩ := S_F hz.1 hs
  obtain ⟨U', _, _, hs'F⟩ := S_F hz'.1 hs'
  rw [uMap_eq hz s U (colEq hsF), uMap_eq hz' s' U' (colEq hs'F), Zhat_eq, Zhat_eq]
  have hsU : sᴴ * Hpk k r * s = Hpk k r := Sset_UH hs
  have hu : IsUnit s.det := WeylGroupFacts.isUnit_of_uh hsU
  have hHs : Hpk k r * s⁻¹ = sᴴ * Hpk k r := by
    calc Hpk k r * s⁻¹ = sᴴ * Hpk k r * s * s⁻¹ := by rw [hsU]
      _ = sᴴ * Hpk k r := by rw [Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hu, Matrix.mul_one]
  calc (Fm k r z)ᴴ * Hpk k r * (s⁻¹ * g * s') * Fm k r z'
      = (Fm k r z)ᴴ * (Hpk k r * s⁻¹) * g * (s' * Fm k r z') := by simp only [Matrix.mul_assoc]
    _ = (Fm k r z)ᴴ * (sᴴ * Hpk k r) * g * (Fm k r z' * U') := by rw [hHs, hs'F]
    _ = (s * Fm k r z)ᴴ * Hpk k r * g * Fm k r z' * U' := by
        rw [Matrix.conjTranspose_mul]; simp only [Matrix.mul_assoc]
    _ = (Fm k r z * U)ᴴ * Hpk k r * g * Fm k r z' * U' := by rw [hsF]
    _ = Uᴴ * ((Fm k r z)ᴴ * Hpk k r * g * Fm k r z') * U' := by
        rw [Matrix.conjTranspose_mul]; simp only [Matrix.mul_assoc]

end Formalism.FourierDecayAlt.P
end

