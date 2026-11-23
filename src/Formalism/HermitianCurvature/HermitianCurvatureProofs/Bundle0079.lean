module

public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0074
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.SumDualVectorEqZeta
public import Formalism.HermitianCurvature.Bundle0005
public import Formalism.HermitianCurvature.FiniteOrderIntersectionInSmooth
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0021
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0073
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.LduDecompositionExists
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.UnipotentCoordinatesMeasurePreserving
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.CompactGroupHaarExists
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0028
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0038
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0065

@[expose] public section

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.CutGCoreGTCLRadTJet
section
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt
open scoped ContDiff

namespace Formalism.FourierDecayAlt.P.CutMP.Gauge.GC

noncomputable section

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

section Jet

variable {k r : ℕ} {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]

theorem jetT_le (j : ℕ) : ((j : ℕ) : WithTop ℕ∞) ≤ ((⊤ : ℕ∞) : WithTop ℕ∞) := by
  exact_mod_cast (le_top : (j : ℕ∞) ≤ ⊤)

theorem jetT_mono {N M : ℕ} (hMN : M ≤ N) {f : Q.Mx k r → E} {g₀ : Q.Mx k r} (h : ZJ k r N f g₀) :
    ZJ k r M f g₀ := by
  obtain ⟨U, F, hU, hgU, hF, hfF, hv⟩ := h
  exact ⟨U, F, hU, hgU, hF, hfF, fun j hj => hv j (hj.trans hMN)⟩

theorem jetT_val {N : ℕ} {f : Q.Mx k r → E} {g₀ : Q.Mx k r} (hg₀ : g₀ ∈ Q.Glev k r (Fin.last r))
    (h : ZJ k r N f g₀) : f g₀ = 0 := by
  obtain ⟨U, F, hU, hgU, hF, hfF, hv⟩ := h
  rw [hfF g₀ hgU hg₀]
  have h0 := hv 0 (Nat.zero_le _)
  calc F g₀ = iteratedFDeriv ℝ 0 F g₀ (fun i => Fin.elim0 i) := (iteratedFDeriv_zero_apply _).symm
    _ = 0 := by rw [h0]; rfl

theorem jetT_zero {N : ℕ} {g₀ : Q.Mx k r} : ZJ k r N (fun _ => (0 : E)) g₀ :=
  ⟨Set.univ, fun _ => (0 : E), isOpen_univ, Set.mem_univ _, contDiffOn_const, fun _ _ _ => rfl,
    fun j _ => by rw [iteratedFDeriv_fun_zero]; rfl⟩

theorem jetT_add {N : ℕ} {f f₂ : Q.Mx k r → E} {g₀ : Q.Mx k r} (h : ZJ k r N f g₀) (h₂ : ZJ k r N f₂ g₀) :
    ZJ k r N (fun x => f x + f₂ x) g₀ := by
  obtain ⟨U, F, hU, hgU, hF, hfF, hv⟩ := h
  obtain ⟨U₂, F₂, hU₂, hgU₂, hF₂, hfF₂, hv₂⟩ := h₂
  have hO : IsOpen (U ∩ U₂) := hU.inter hU₂
  have hx : g₀ ∈ U ∩ U₂ := ⟨hgU, hgU₂⟩
  have hF1 : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) F (U ∩ U₂) := hF.mono Set.inter_subset_left
  have hF2 : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) F₂ (U ∩ U₂) := hF₂.mono Set.inter_subset_right
  refine ⟨U ∩ U₂, fun x => F x + F₂ x, hO, hx, hF1.add hF2, ?_, ?_⟩
  · intro g hg hgl
    simp only [hfF g hg.1 hgl, hfF₂ g hg.2 hgl]
  · intro j hj
    show iteratedFDeriv ℝ j (F + F₂) g₀ = 0
    rw [← iteratedFDerivWithin_of_isOpen j hO hx,
      iteratedFDerivWithin_add_apply ((hF1 g₀ hx).of_le (jetT_le j)) ((hF2 g₀ hx).of_le (jetT_le j))
        hO.uniqueDiffOn hx,
      iteratedFDerivWithin_of_isOpen j hO hx, iteratedFDerivWithin_of_isOpen j hO hx, hv j hj, hv₂ j hj,
      add_zero]

theorem jetT_smul {N : ℕ} (c : ℂ) {f : Q.Mx k r → E} {g₀ : Q.Mx k r} (h : ZJ k r N f g₀) :
    ZJ k r N (fun x => c • f x) g₀ := by
  obtain ⟨U, F, hU, hgU, hF, hfF, hv⟩ := h
  refine ⟨U, fun x => c • F x, hU, hgU, hF.const_smul c, ?_, ?_⟩
  · intro g hg hgl
    simp only [hfF g hg hgl]
  · intro j hj
    show iteratedFDeriv ℝ j (c • F) g₀ = 0
    rw [← iteratedFDerivWithin_of_isOpen j hU hgU,
      iteratedFDerivWithin_const_smul_apply ((hF g₀ hgU).of_le (jetT_le j)) hU.uniqueDiffOn hgU,
      iteratedFDerivWithin_of_isOpen j hU hgU, hv j hj, smul_zero]

theorem jetT_fderiv {D G : Type*} [NormedAddCommGroup D] [NormedSpace ℝ D] [NormedAddCommGroup G] [NormedSpace ℝ G]
    {F : D → G} {g₀ : D} {i : ℕ} (h : iteratedFDeriv ℝ (i + 1) F g₀ = 0) :
    iteratedFDeriv ℝ i (fderiv ℝ F) g₀ = 0 := by
  rw [iteratedFDeriv_succ_eq_comp_right, Function.comp_apply] at h
  exact (LinearIsometryEquiv.map_eq_zero_iff _).1 h

theorem jetT_gen {D G : Type*} [NormedAddCommGroup D] [NormedSpace ℝ D] [NormedAddCommGroup G] [NormedSpace ℝ G]
    {F : D → G} {U : Set D} (hU : IsOpen U) {g₀ : D} (hgU : g₀ ∈ U)
    (hF : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) F U) (L : D →L[ℝ] D) (N : ℕ)
    (hv : ∀ j ≤ N + 1, iteratedFDeriv ℝ j F g₀ = 0) :
    ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun x => fderiv ℝ F x (L x)) U ∧
      ∀ j ≤ N, iteratedFDeriv ℝ j (fun x => fderiv ℝ F x (L x)) g₀ = 0 := by
  have hmn : ((⊤ : ℕ∞) : WithTop ℕ∞) + 1 ≤ ((⊤ : ℕ∞) : WithTop ℕ∞) := by
    rw [← WithTop.coe_one, ← WithTop.coe_add, top_add]
  have hF' : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun y => fderiv ℝ F y) U := hF.fderiv_of_isOpen hU hmn
  refine ⟨hF'.clm_apply L.contDiff.contDiffOn, ?_⟩
  intro j hj
  let Bl : (D →L[ℝ] G) →L[ℝ] D →L[ℝ] G := (ContinuousLinearMap.apply ℝ G : D →L[ℝ] (D →L[ℝ] G) →L[ℝ] G).flip
  have hfun : (fun x => fderiv ℝ F x (L x)) = fun x => Bl (fderiv ℝ F x) (L x) := rfl
  have hbd := Bl.norm_iteratedFDerivWithin_le_of_bilinear hF' L.contDiff.contDiffOn hU.uniqueDiffOn hgU
    (n := j) (jetT_le j)
  have hzero : ∀ i ∈ Finset.range (j + 1), iteratedFDerivWithin ℝ i (fun y => fderiv ℝ F y) U g₀ = 0 := by
    intro i hi
    rw [iteratedFDerivWithin_of_isOpen i hU hgU]
    exact jetT_fderiv (hv (i + 1) (by simp at hi; omega))
  rw [Finset.sum_eq_zero (fun i hi => by rw [hzero i hi, norm_zero, mul_zero, zero_mul]), mul_zero] at hbd
  have h0 := norm_le_zero_iff.1 hbd
  rw [iteratedFDerivWithin_of_isOpen j hU hgU] at h0
  rw [hfun]
  exact h0

theorem jetT_rd {N : ℕ} {f : Q.Mx k r → E} {g₀ X : Q.Mx k r}
    (hX : Q.inLieLev k r (Fin.last r) X) (h : ZJ k r (N + 1) f g₀) : ZJ k r N (RdV X f) g₀ := by
  obtain ⟨U, F, hU, hgU, hF, hfF, hv⟩ := h
  let L : Q.Mx k r →L[ℝ] Q.Mx k r := (LinearMap.mulRight ℝ X).toContinuousLinearMap
  have hL : ∀ x, L x = x * X := fun x => rfl
  have hG := jetT_gen hU hgU hF L N hv
  refine ⟨U, fun x => fderiv ℝ F x (L x), hU, hgU, hG.1, ?_, hG.2⟩
  intro g hg hgl
  have hd : DifferentiableAt ℝ F g :=
    (hF.contDiffAt (hU.mem_nhds hg)).differentiableAt (by simpa using jetT_le 1)
  show RdV X f g = fderiv ℝ F g (L g)
  rw [hL]
  exact (Formalism.FourierDecayAlt.P.Qx2.hasDeriv_ext hU hg hgl hX hd hfF).deriv

theorem jetT_EH {N : ℕ} {f : Q.Mx k r → E} {g₀ : Q.Mx k r} (a b : Fin (Q.mdim k r (Fin.last r)))
    (h : ZJ k r (N + 1) f g₀) :
    ZJ k r N (Q.EH k r (Q.posL k r (Fin.last r) a) (Q.posL k r (Fin.last r) b) f) g₀ := by
  have hl := Formalism.FourierDecayAlt.P.Qx2.hpart_lev (k := k) (r := r) (Fin.last r) a b
  exact jetT_add (jetT_rd hl.1 h) (jetT_smul Complex.I (jetT_rd hl.2 h))

theorem jetT_Top {N : ℕ} {f : Q.Mx k r → E} {g₀ : Q.Mx k r} (u : ℂ) (a b : Fin (Q.mdim k r (Fin.last r)))
    (h : ZJ k r (N + 1) f g₀) :
    ZJ k r N (Top (Q.EH k r) u (Q.posL k r (Fin.last r) a) (Q.posL k r (Fin.last r) b) f) g₀ := by
  by_cases hab : Q.posL k r (Fin.last r) a = Q.posL k r (Fin.last r) b
  · have he : Top (Q.EH k r) u (Q.posL k r (Fin.last r) a) (Q.posL k r (Fin.last r) b) f =
        fun g => u • f g + Q.EH k r (Q.posL k r (Fin.last r) a) (Q.posL k r (Fin.last r) b) f g := by
      funext g
      simp only [Formalism.QuantumDeterminants.Top, hab, if_true]
    rw [he]
    exact jetT_add (jetT_smul u (jetT_mono (Nat.le_succ N) h)) (jetT_EH a b h)
  · have he : Top (Q.EH k r) u (Q.posL k r (Fin.last r) a) (Q.posL k r (Fin.last r) b) f =
        Q.EH k r (Q.posL k r (Fin.last r) a) (Q.posL k r (Fin.last r) b) f := by
      funext g
      simp only [Formalism.QuantumDeterminants.Top, hab, if_false, zero_add]
    rw [he]
    exact jetT_EH a b h

theorem jetT_foldr {g₀ : Q.Mx k r} (L : List ((Q.Mx k r → E) → (Q.Mx k r → E)))
    (hL : ∀ T ∈ L, ∀ (N : ℕ) (h : Q.Mx k r → E), ZJ k r (N + 1) h g₀ → ZJ k r N (T h) g₀) :
    ∀ (N : ℕ) (f : Q.Mx k r → E), ZJ k r (N + L.length) f g₀ →
      ZJ k r N (L.foldr (fun T h => T h) f) g₀ := by
  induction L with
  | nil =>
    intro N f h
    simpa using h
  | cons T L ih =>
    intro N f h
    simp only [List.foldr_cons]
    apply hL T List.mem_cons_self N
    apply ih (fun T' hT' => hL T' (List.mem_cons_of_mem _ hT')) (N + 1) f
    simp only [List.length_cons] at h
    rwa [show N + 1 + L.length = N + (L.length + 1) by omega]

theorem jetT_qminor {N t : ℕ} {f : Q.Mx k r → E} {g₀ : Q.Mx k r} (c d : Fin t → Fin (Q.mdim k r (Fin.last r)))
    (u : ℂ) (h : ZJ k r (N + t) f g₀) :
    ZJ k r N (qminorOp (Q.EH k r) (Q.posL k r (Fin.last r) ∘ c) (Q.posL k r (Fin.last r) ∘ d) u f) g₀ := by
  have hG : ∀ σ : Equiv.Perm (Fin t), ZJ k r N
      ((((Equiv.Perm.sign σ : ℤ) : ℂ) •
        (List.ofFn fun i : Fin t => Top (Q.EH k r) (u - ((i : ℕ) : ℂ))
          ((Q.posL k r (Fin.last r) ∘ c) (σ i)) ((Q.posL k r (Fin.last r) ∘ d) i)).foldr
          (fun T h => T h) f)) g₀ := by
    intro σ
    apply jetT_smul
    apply jetT_foldr
    · intro T hT N' h'' h'
      rw [List.mem_ofFn] at hT
      obtain ⟨i, rfl⟩ := hT
      exact jetT_Top _ (c (σ i)) (d i) h'
    · rwa [List.length_ofFn]
  have hsum : ∀ s : Finset (Equiv.Perm (Fin t)), ZJ k r N (∑ σ ∈ s, ((((Equiv.Perm.sign σ : ℤ) : ℂ) •
        (List.ofFn fun i : Fin t => Top (Q.EH k r) (u - ((i : ℕ) : ℂ))
          ((Q.posL k r (Fin.last r) ∘ c) (σ i)) ((Q.posL k r (Fin.last r) ∘ d) i)).foldr
          (fun T h => T h) f))) g₀ := by
    intro s
    refine Finset.induction_on s ?_ ?_
    · rw [Finset.sum_empty]
      exact jetT_zero
    · intro σ s hσ ih
      rw [Finset.sum_insert hσ]
      exact jetT_add (hG σ) ih
  exact hsum Finset.univ

theorem jetT_qminor_val {t : ℕ} {f : Q.Mx k r → E} {g₀ : Q.Mx k r} (hg₀ : g₀ ∈ Q.Glev k r (Fin.last r))
    (hZ : ZJ k r (Q.mdim k r (Fin.last r)) f g₀) (c d : Fin t → Fin (Q.mdim k r (Fin.last r))) (u : ℂ)
    (ht : t ≤ Q.mdim k r (Fin.last r)) :
    qminorOp (Q.EH k r) (Q.posL k r (Fin.last r) ∘ c) (Q.posL k r (Fin.last r) ∘ d) u f g₀ = 0 :=
  jetT_val hg₀ (jetT_qminor c d u (jetT_mono (by omega) hZ : ZJ k r (0 + t) f g₀))

end Jet

theorem jet_finite_order_along_level : GTCLRJetT := by
  intro E _ _ k r z z' Y a b
  refine ⟨Q.mdim k r (Fin.last r), ?_⟩
  intro f g₀ hg₀ hZ
  have hq : ∀ {t : ℕ} (c d : Fin t → Fin (Q.mdim k r (Fin.last r))) (u : ℂ), t ≤ Q.mdim k r (Fin.last r) →
      qminorOp (Q.EH k r) (Q.posL k r (Fin.last r) ∘ c) (Q.posL k r (Fin.last r) ∘ d) u f g₀ = 0 :=
    fun c d u ht => jetT_qminor_val hg₀ hZ c d u ht
  match a, b with
  | 0, 0 => exact hq id id _ le_rfl
  | 0, 1 =>
    simp only [Q.tL, Pi.neg_apply, Q.chatL, neg_eq_zero]
    refine Finset.sum_eq_zero fun i _ => Finset.sum_eq_zero fun j _ => ?_
    rw [hq _ _ _ (Nat.sub_le _ _), smul_zero]
  | 1, 0 =>
    simp only [Q.tL, Pi.neg_apply, Q.chatL, neg_eq_zero]
    refine Finset.sum_eq_zero fun i _ => Finset.sum_eq_zero fun j _ => ?_
    rw [hq _ _ _ (Nat.sub_le _ _), smul_zero]
  | 1, 1 =>
    simp only [Q.tL, Pi.neg_apply, Q.chat2L, neg_eq_zero]
    refine Finset.sum_eq_zero fun i _ => Finset.sum_eq_zero fun i' _ =>
      Finset.sum_eq_zero fun j _ => Finset.sum_eq_zero fun j' _ => ?_
    split_ifs
    · rw [hq _ _ _ (Nat.sub_le _ _), smul_zero]
    · rfl

end

end Formalism.FourierDecayAlt.P.CutMP.Gauge.GC
end

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.CutGCoreGTCLRadTTaylor
section
open scoped ContDiff

namespace Formalism.FourierDecayAlt.P.CutMP.Gauge.GC.RadTTaylor

noncomputable section

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem perm_of_swaps {W : Type} [NormedAddCommGroup W] [NormedSpace ℝ W] {n : ℕ}
    (T : ContinuousMultilinearMap ℝ (fun _ : Fin n => E) W)
    (h : ∀ (a b : Fin n), a ≠ b → ∀ v : Fin n → E, T (v ∘ Equiv.swap a b) = T v) :
    ∀ (σ : Equiv.Perm (Fin n)) (v : Fin n → E), T (v ∘ σ) = T v := by
  classical
  intro σ
  induction σ using Equiv.Perm.swap_induction_on with
  | one => intro v; rfl
  | swap_mul f x y hxy ih =>
    intro v
    rw [Equiv.Perm.coe_mul]
    calc T (v ∘ (⇑(Equiv.swap x y) ∘ ⇑f)) = T ((v ∘ Equiv.swap x y) ∘ f) := rfl
      _ = T (v ∘ Equiv.swap x y) := ih _
      _ = T v := h x y hxy v

theorem symm_iter : ∀ (n : ℕ) (W : Type) [NormedAddCommGroup W] [NormedSpace ℝ W] (f : E → W) (U : Set E),
    IsOpen U → ContDiffOn ℝ ∞ f U → ∀ x ∈ U, ∀ (σ : Equiv.Perm (Fin n)) (v : Fin n → E),
      iteratedFDeriv ℝ n f x (v ∘ σ) = iteratedFDeriv ℝ n f x v := by
  have hle : ∀ k : ℕ, ((k : ℕ) : WithTop ℕ∞) ≤ ∞ := fun k => by
    first
    | exact WithTop.coe_le_coe.2 le_top
    | exact_mod_cast (le_top : ((k : ℕ∞)) ≤ ⊤)
  intro n
  induction n with
  | zero =>
    intro W _ _ f U hU hf x hx σ v
    rw [Subsingleton.elim (v ∘ σ) v]
  | succ n ih =>
    intro W _ _ f U hU hf x hx
    refine perm_of_swaps (iteratedFDeriv ℝ (n + 1) f x) ?_
    intro a b hab
    rcases n with _ | m
    · exact absurd (Fin.ext (by have := a.isLt; have := b.isLt; omega)) hab
    have hfx : ContDiffAt ℝ ∞ f x := hf.contDiffAt (hU.mem_nhds hx)
    have hmul : ∀ σ τ : Equiv.Perm (Fin (m + 1 + 1)),
        (∀ v, iteratedFDeriv ℝ (m + 1 + 1) f x (v ∘ σ) = iteratedFDeriv ℝ (m + 1 + 1) f x v) →
        (∀ v, iteratedFDeriv ℝ (m + 1 + 1) f x (v ∘ τ) = iteratedFDeriv ℝ (m + 1 + 1) f x v) →
        ∀ v, iteratedFDeriv ℝ (m + 1 + 1) f x (v ∘ ⇑(σ * τ)) = iteratedFDeriv ℝ (m + 1 + 1) f x v := by
      intro σ τ hσ hτ v
      rw [Equiv.Perm.coe_mul]
      exact (hτ (v ∘ σ)).trans (hσ v)
    have T1 : ∀ a' b' : Fin (m + 1), a' ≠ b' → ∀ v : Fin (m + 1 + 1) → E,
        iteratedFDeriv ℝ (m + 1 + 1) f x (v ∘ Equiv.swap a'.succ b'.succ) =
          iteratedFDeriv ℝ (m + 1 + 1) f x v := by
      intro a' b' _ v
      rw [iteratedFDeriv_succ_apply_left, iteratedFDeriv_succ_apply_left]
      have h0 : (v ∘ Equiv.swap a'.succ b'.succ) 0 = v 0 := by
        simp only [Function.comp_apply]
        rw [Equiv.swap_apply_of_ne_of_ne (Fin.succ_ne_zero a').symm (Fin.succ_ne_zero b').symm]
      have ht : Fin.tail (v ∘ Equiv.swap a'.succ b'.succ) = Fin.tail v ∘ Equiv.swap a' b' := by
        funext i
        simp only [Fin.tail, Function.comp_apply]
        rw [(Fin.succ_injective _).swap_apply]
      rw [h0, ht]
      have hgd : DifferentiableAt ℝ (iteratedFDeriv ℝ (m + 1) f) x :=
        (hfx.iteratedFDeriv_right (m := 1) (i := m + 1) (by
          have := hle (1 + (m + 1)); push_cast at this ⊢; exact this)).differentiableAt one_ne_zero
      rw [← fderiv_continuousMultilinear_apply_const_apply hgd,
        ← fderiv_continuousMultilinear_apply_const_apply hgd]
      rw [Filter.EventuallyEq.fderiv_eq (Filter.eventually_of_mem (hU.mem_nhds hx)
        (fun y hy => ih W f U hU hf y hy (Equiv.swap a' b') (Fin.tail v)))]
    have T2 : ∀ v : Fin (m + 1 + 1) → E,
        iteratedFDeriv ℝ (m + 1 + 1) f x (v ∘ Equiv.swap 0 (Fin.succ 0)) =
          iteratedFDeriv ℝ (m + 1 + 1) f x v := by
      intro v
      have hrepr : ∀ w : Fin (m + 1 + 1) → E, iteratedFDeriv ℝ (m + 1 + 1) f x w =
          fderiv ℝ (fderiv ℝ (iteratedFDeriv ℝ m f)) x (w 0) (Fin.tail w 0) (Fin.tail (Fin.tail w)) := by
        intro w
        rw [iteratedFDeriv_succ_apply_left, iteratedFDeriv_succ_eq_comp_left, LinearIsometryEquiv.comp_fderiv]
        first
        | rfl
        | simp [continuousMultilinearCurryLeftEquiv_symm_apply]
      rw [hrepr, hrepr]
      have hg : ContDiffAt ℝ 2 (iteratedFDeriv ℝ m f) x :=
        hfx.iteratedFDeriv_right (by have := hle (2 + m); push_cast at this ⊢; exact this)
      have hs := hg.isSymmSndFDerivAt (by rw [minSmoothness_of_isRCLikeNormedField])
      have e0 : (v ∘ Equiv.swap 0 (Fin.succ 0)) 0 = Fin.tail v 0 := by
        simp only [Function.comp_apply, Equiv.swap_apply_left, Fin.tail]
      have e1 : Fin.tail (v ∘ Equiv.swap 0 (Fin.succ 0)) 0 = v 0 := by
        simp only [Fin.tail, Function.comp_apply, Equiv.swap_apply_right]
      have e2 : Fin.tail (Fin.tail (v ∘ Equiv.swap 0 (Fin.succ 0))) = Fin.tail (Fin.tail v) := by
        funext i
        simp only [Fin.tail, Function.comp_apply]
        rw [Equiv.swap_apply_of_ne_of_ne (Fin.succ_ne_zero _)
          (fun h => Fin.succ_ne_zero i (Fin.succ_injective _ h))]
      rw [e0, e1, e2, hs (Fin.tail v 0) (v 0)]
    have T0 : ∀ b' : Fin (m + 1), ∀ v : Fin (m + 1 + 1) → E,
        iteratedFDeriv ℝ (m + 1 + 1) f x (v ∘ Equiv.swap 0 b'.succ) =
          iteratedFDeriv ℝ (m + 1 + 1) f x v := by
      intro b'
      by_cases hb : b' = 0
      · subst hb; exact T2
      · have e := Equiv.swap_mul_swap_mul_swap (x := (0 : Fin (m + 1 + 1))) (y := Fin.succ 0)
          (z := b'.succ) (Fin.succ_ne_zero 0).symm (Fin.succ_ne_zero b').symm
        rw [Equiv.swap_comm, ← e]
        have h1 := T1 0 b' (Ne.symm hb)
        exact hmul _ _ (hmul _ _ h1 T2) h1
    cases a using Fin.cases with
    | zero =>
      cases b using Fin.cases with
      | zero => exact absurd rfl hab
      | succ b' => exact T0 b'
    | succ a' =>
      cases b using Fin.cases with
      | zero => intro v; rw [Equiv.swap_comm]; exact T0 a' v
      | succ b' => exact T1 a' b' (fun h => hab (h ▸ rfl))

variable {W : Type} [NormedAddCommGroup W] [NormedSpace ℝ W]

theorem poly_contDiff {j : ℕ} (m : ContinuousMultilinearMap ℝ (fun _ : Fin j => E) W) (a : E) {n : WithTop ℕ∞} :
    ContDiff ℝ n (fun ζ => m (fun _ => ζ - a)) := m.contDiff.comp (contDiff_pi.2 fun _ => contDiff_id.sub contDiff_const)

theorem poly_hom {j i : ℕ} (hij : i ≠ j) (m : ContinuousMultilinearMap ℝ (fun _ : Fin j => E) W) :
    iteratedFDeriv ℝ i (fun ζ => m (fun _ => ζ)) 0 = 0 := by
  have hg : ContDiff ℝ i (fun ζ : E => m (fun _ => ζ)) :=
    m.contDiff.comp (contDiff_pi.2 fun _ => contDiff_id)
  set L : E →L[ℝ] E := (2 : ℝ) • ContinuousLinearMap.id ℝ E with hL
  have hcomp : (fun ζ : E => m (fun _ => ζ)) ∘ L = ((2 : ℝ) ^ j) • (fun ζ : E => m (fun _ => ζ)) := by
    funext ζ
    simp only [Function.comp_apply, Pi.smul_apply, hL, ContinuousLinearMap.smul_apply,
      ContinuousLinearMap.id_apply]
    rw [m.map_smul_univ (fun _ => (2 : ℝ)) (fun _ => ζ)]
    simp [Finset.prod_const]
  have h1 := ContinuousLinearMap.iteratedFDeriv_comp_right L hg 0 (i := i) le_rfl
  rw [hcomp, iteratedFDeriv_const_smul_apply hg.contDiffAt, map_zero] at h1
  have hne : (2 : ℝ) ^ j ≠ (2 : ℝ) ^ i := by
    intro h
    apply hij
    have : (2 : ℕ) ^ j = 2 ^ i := by exact_mod_cast h
    exact (Nat.pow_right_injective le_rfl this).symm
  ext v
  have key : ((2 : ℝ) ^ j) • iteratedFDeriv ℝ i (fun ζ : E => m (fun _ => ζ)) 0 v =
      ((2 : ℝ) ^ i) • iteratedFDeriv ℝ i (fun ζ : E => m (fun _ => ζ)) 0 v := by
    have hv := congrArg (fun T => T v) h1
    simp only [ContinuousMultilinearMap.smul_apply,
      ContinuousMultilinearMap.compContinuousLinearMap_apply] at hv
    rw [hv, hL]
    simp only [ContinuousLinearMap.smul_apply, ContinuousLinearMap.id_apply]
    rw [ContinuousMultilinearMap.map_smul_univ (iteratedFDeriv ℝ i (fun ζ : E => m (fun _ => ζ)) 0)
      (fun _ => (2 : ℝ)) v]
    simp [Finset.prod_const]
  have h0 : ((2 : ℝ) ^ j - (2 : ℝ) ^ i) • iteratedFDeriv ℝ i (fun ζ : E => m (fun _ => ζ)) 0 v = 0 := by
    rw [sub_smul, key, sub_self]
  rw [ContinuousMultilinearMap.zero_apply]
  exact (smul_eq_zero.1 h0).resolve_left (sub_ne_zero.2 hne)

theorem poly_at {j i : ℕ} (m : ContinuousMultilinearMap ℝ (fun _ : Fin j => E) W) (a : E) (v : Fin i → E) :
    iteratedFDeriv ℝ i (fun ζ => m (fun _ => ζ - a)) a v =
      if h : i = j then ∑ σ : Equiv.Perm (Fin j), m (fun k => (v ∘ Fin.cast h.symm) (σ k)) else 0 := by
  by_cases h : i = j
  · subst h
    rw [dite_eq_left rfl, iteratedFDeriv_comp_sub (f := fun ζ => m fun _ => ζ), sub_self,
      ContinuousMultilinearMap.iteratedFDeriv_comp_diagonal]
    rfl
  · rw [dite_eq_right h, iteratedFDeriv_comp_sub (f := fun ζ => m fun _ => ζ), sub_self, poly_hom h m]
    rfl

end

end Formalism.FourierDecayAlt.P.CutMP.Gauge.GC.RadTTaylor

namespace Formalism.FourierDecayAlt.P.CutMP.Gauge.GC

open Formalism.FourierDecayAlt.P.CutMP.Gauge.GC.RadTTaylor

theorem taylor_expansion_holds : GTCLRTaylor := by
  intro V _ _ ψ U ζ₀ N hU hζ hψ i hi
  have hle : ∀ k : ℕ, ((k : ℕ) : WithTop ℕ∞) ≤ ((⊤ : ℕ∞) : WithTop ℕ∞) := fun k => by
    first
    | exact WithTop.coe_le_coe.2 le_top
    | exact_mod_cast (le_top : ((k : ℕ∞)) ≤ ⊤)
  have hψat : ContDiffAt ℝ i ψ ζ₀ := (hψ.contDiffAt (hU.mem_nhds hζ)).of_le (hle i)
  have hS : ContDiff ℝ i (fun ζ : ℂ => ∑ j ∈ Finset.range (N + 1),
      ((j.factorial : ℝ)⁻¹) • iteratedFDeriv ℝ j ψ ζ₀ (fun _ => ζ - ζ₀)) :=
    ContDiff.sum fun j _ => (poly_contDiff _ _).const_smul _
  refine (iteratedFDeriv_sub_apply hψat hS.contDiffAt).trans ?_
  rw [sub_eq_zero, iteratedFDeriv_sum (fun j _ => (poly_contDiff _ _).const_smul _)]
  ext v
  rw [Finset.sum_apply, ContinuousMultilinearMap.sum_apply]
  have hterm : ∀ j ∈ Finset.range (N + 1),
      iteratedFDeriv ℝ i (fun ζ : ℂ => ((j.factorial : ℝ)⁻¹) • iteratedFDeriv ℝ j ψ ζ₀ (fun _ => ζ - ζ₀)) ζ₀ v =
        if j = i then ((i.factorial : ℝ)⁻¹) • ∑ σ : Equiv.Perm (Fin i), iteratedFDeriv ℝ i ψ ζ₀ (v ∘ σ)
        else 0 := by
    intro j _
    rw [show (fun ζ : ℂ => ((j.factorial : ℝ)⁻¹) • iteratedFDeriv ℝ j ψ ζ₀ (fun _ => ζ - ζ₀)) =
        ((j.factorial : ℝ)⁻¹) • (fun ζ : ℂ => iteratedFDeriv ℝ j ψ ζ₀ (fun _ => ζ - ζ₀)) from rfl,
      iteratedFDeriv_const_smul_apply ((poly_contDiff _ _).contDiffAt),
      ContinuousMultilinearMap.smul_apply, poly_at]
    split_ifs with h1 h2 h2
    · subst h1; rfl
    · exact absurd h1.symm h2
    · exact absurd h2.symm h1
    · rw [smul_zero]
  rw [Finset.sum_congr rfl hterm, Finset.sum_ite_eq' (Finset.range (N + 1)) i,
    if_pos (Finset.mem_range.2 (Nat.lt_succ_of_le hi))]
  have hs : ∀ σ : Equiv.Perm (Fin i), iteratedFDeriv ℝ i ψ ζ₀ (v ∘ σ) = iteratedFDeriv ℝ i ψ ζ₀ v :=
    fun σ => symm_iter i V ψ U hU hψ ζ₀ hζ σ v
  rw [Finset.sum_congr rfl (fun σ _ => hs σ), Finset.sum_const, Finset.card_univ, Fintype.card_perm,
    Fintype.card_fin, ← Nat.cast_smul_eq_nsmul ℝ, smul_smul,
    inv_mul_cancel₀ (Nat.cast_ne_zero.2 (Nat.factorial_ne_zero i)), one_smul]

end Formalism.FourierDecayAlt.P.CutMP.Gauge.GC
end

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.InnerAveragingInputOfSliceData
section
open Matrix

noncomputable section

namespace Formalism.FourierDecayAlt.P

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.C6

theorem norm_eq_of_pow_eq_same {s : ℕ} (hs : 0 < s) {a z z₀ : ℂ} (hz : z ^ s = a) (hz₀ : z₀ ^ s = a) : ‖z‖ = ‖z₀‖ := by
  have h : ‖z‖ ^ s = ‖z₀‖ ^ s := by rw [← norm_pow, ← norm_pow, hz, hz₀]
  exact (pow_left_inj₀ (norm_nonneg _) (norm_nonneg _) hs.ne').mp h

theorem mem_rootSet_iff_pow_eq {s : ℕ} (hs : 0 < s) {a z : ℂ} : z ∈ G.rootSet s a ↔ z ^ s = a := by
  rw [G.rootSet, Multiset.mem_toFinset, Polynomial.mem_nthRoots hs]

theorem germ_leading_term_root_sum {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V] (β : ℂ) (m : ℕ)
    (Ψ : G.Mat (m + 1 + 1) → V) (t Dd z₀ : ℂ) (hz₀ : z₀ ^ (m + 2) = (-1) ^ (m + 3) * Dd) :
    G.mainTerm β m (fun _ => 1) Ψ t Dd =
      (((m : ℂ) + 2)⁻¹ * ((‖z₀‖ ^ ((m + 1) ^ 2) : ℝ) : ℂ)) •
        ∑ z ∈ G.rootSet (m + 2) ((-1) ^ (m + 3) * Dd), G.psi β (((m : ℂ) + 2) * z / t) • G.OmLong β (m + 1) Ψ z := by
  unfold G.mainTerm
  rw [mul_smul]
  congr 1
  rw [Finset.smul_sum]
  refine Finset.sum_congr rfl fun z hz => ?_
  rw [mem_rootSet_iff_pow_eq (by omega)] at hz
  rw [norm_eq_of_pow_eq_same (by omega) hz hz₀, mul_one, mul_smul]

end Formalism.FourierDecayAlt.P
end
end

