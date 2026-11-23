module

public import Formalism.SharpRestriction.GrowthBounds.DualFockLinear.CloudBAtOfRho
public import Formalism.SharpRestriction.GrowthBounds.DualFockLinear.Bundle0005

@[expose] public section

-- bundled from Formalism.SharpRestriction.GrowthBounds.DualFockLinear.CloudBStepOfRho
section
noncomputable section

namespace Formalism.MainNotions.TestSideCounting

open Formalism.MainNotions.G Formalism.GradedWeylDivisibility Formalism.MainNotions.SourceCleaning Formalism.MainNotions.Pf14 MvPolynomial

def RhoStep (C CK : ℝ) : Prop :=
  ∀ (p : ℕ) (W Qq O Kf : Type) [CommRing W] [IsDomain W] [IsDiscreteValuationRing W] [Field Qq] [Algebra W Qq]
    [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field Kf] [Algebra O Kf]
    (ι : Qq →+* Kf) (σ : Qq ≃+* Qq) (j : W →+* O) (w : O)
    (n' m r : ℕ) [Fact p.Prime] [NeZero n'] (TT : Finset (Fin n')) (L₁ L₂ : ℕ) (de h x : ℝ)
    (lam0 : Fin n' → Fin (m + 1) → ℤ) (aT bT : Fin n' → ℤ) (a Y : ℝ) (cpp c0 Dp cStar : ℕ),
    ∀ hSet : UnramifiedQuadraticSetting p n' W Qq O Kf ι σ j w,
    Hyps C p n' m r TT L₁ L₂ de h x lam0 aT bT a Y cpp c0 Dp cStar →
    ∀ φ : WF p n' ≃+* W, IsWittIdent σ φ →
    ∀ e : Edge W Qq (m + 1), IsEdge p n' r e → e.tgt = colSpan W (1 : Matrix (Fin (m + 1)) (Fin (m + 1)) Qq) →
    ∀ (hm : Matrix (Fin (m + 1)) (Fin (m + 1)) Qq) (g : Matrix (Fin (m + 1)) (Fin (m + 1)) (WF p n')),
      IsUnit hm.det → IsGLW g → IsEdgeBasis p r e (hm * ((matQ φ g)⁻¹).transpose) →
      ∀ Θ : ↥((Pol (KK O) (ι := Fin n') (m + 1) (dT TT lam0)).restrictScalars O) ≃ₗ[O]
      ↥(Vsp Kf (flW (m := m) (dT TT lam0))),
        IsTrueTheta hSet.1 (dT TT lam0) (flW (dT TT lam0)) (vecE n') hm Θ →
        RhoAt p n' ι σ w r TT lam0 c0 (r * TT.card * c0 + 2 * r * n' * cpp)
          (CK * (TT.card : ℝ) * ((m + 1 : ℕ) : ℝ) ^ 2 * Real.logb p a) e Θ

def RestRho (D : Formalism.BasicNotions.D7) (CLa Ck Crk Cdeg : ℝ) : Prop :=
  tableLineDegreeFive.admitted D CLa Ck Crk Cdeg → ∃ CK C₁ : ℝ, 0 < CK ∧ 0 < C₁ ∧ ∀ C : ℝ, C₁ ≤ C → RhoStep C CK

theorem cloudBStep_of_rho (D : Formalism.BasicNotions.D7) (C CK CLa : ℝ) (hR : RhoStep C CK) : CloudBStep C CK CLa := by
  intro p W Qq O Kf _ _ _ _ _ _ _ _ _ _ ι σ j w n' m r _ _ TT L₁ L₂ de h x lam0 aT bT a Y cpp c0 Dp cStar hSet H φ hφ K
    _ _ hk hrk F hF E' hE' nb B hB hli hc e he htgt hm g hhm hg hbasis
  let _ : Algebra (WF p n') O := algOfIdent j φ
  intro FsB hFsB Θ hΘ
  have hkr : orbitWindowCount r de h x + 2 * r ≤ (m + 1) - r := H.2.2.2.2.2.2.2.1
  have hr2 : 2 ≤ r := H.2.1
  have hdom : IsDominant lam0 := H.2.2.2.2.1.2.1
  have hw : algebraMap O Kf w ≠ 0 := w_ne_zero hSet.1
  obtain ⟨Θ', hΘ1, hΘ2⟩ := theta_exists p n' W Qq O Kf ι σ j w hSet.1 φ hφ m r (vecE n') (dT TT lam0) (flW (dT TT lam0))
    (by omega) (by omega) (isFlat_flW _) hm hhm
  have hΘeq : Θ = Θ' := LinearEquiv.ext fun G => Subtype.ext (by rw [hΘ G, hΘ2 G])
  have hFs : ∀ b, Θ (FsB b) ∈ Re p ι σ w r (flW (dT TT lam0)) e := by
    intro b
    have h1 : InWjRg p n' O w r (flatLetters (vecE n')) g (FsB b : MvPolynomial (Fin n' × Fin (m + 1)) (KK O)) 0 := by
      show InWj w (subst p n' O w n' r g (FsB b : MvPolynomial (TV n' (m + 1)) (KK O))) 0
      rw [hFsB b]
      unfold symB toK
      rw [subst_SPtrue w F hF.2.1 hSet.1.even (by omega) hrk hg, ← map_mul]
      intro mm
      exact ⟨AddMonoidAlgebra.coeff _ mm, by rw [coeff_map, pow_zero, one_mul]⟩
    have h2 := (hΘ1.2 g hg e hbasis (FsB b) 0).1 h1
    rw [hΘeq]
    obtain ⟨z, hz, hze⟩ := mem_scale.1 h2
    rw [← hze]
    simpa using hz
  refine cloudBAt_of_rho hSet.1 Formalism.L2.G.Model.bePerfect r TT lam0 hdom c0 _ _ e he FsB Θ ?_
    (hR p W Qq O Kf ι σ j w n' m r TT L₁ L₂ de h x lam0 aT bT a Y cpp c0 Dp cStar hSet H φ hφ e he htgt hm g hhm hg hbasis
      Θ hΘ)
  intro b s u hs hu
  exact edge_lattice_mul_of_weight_sum D (Formalism.L2.G.Model.products_sections_integral D) p ι σ w hw r (lambda_zero_eq_product TT lam0) (flW_dom _)
    (restW_dom (by omega) TT lam0 hdom) e hu (hFs b) hs

theorem restCloudB_of_rho (D : Formalism.BasicNotions.D7) (CLa Ck Crk Cdeg : ℝ) (h : RestRho D CLa Ck Crk Cdeg) :
    RestCloudB D CLa Ck Crk Cdeg := by
  intro hA
  obtain ⟨CK, C₁, h1, h2, h3⟩ := h hA
  exact ⟨CK, C₁, h1, h2, fun C hC => cloudBStep_of_rho D C CK CLa (h3 C hC)⟩

end Formalism.MainNotions.TestSideCounting
end
end

-- bundled from Formalism.SharpRestriction.GrowthBounds.DualFockLinear.FockSumRight
section
noncomputable section

open MvPolynomial Finset Classical

namespace Formalism.MainNotions.TestSideCounting

open Formalism.MainNotions.G Formalism.GradedWeylDivisibility Formalism.MainNotions.SourceCleaning Formalism.MainNotions.Pf14
open Formalism.L2.G.Model (kapR kapR_alg)

theorem fock_sum_right {R : Type} [CommRing R] {τ : Type} {ι : Type} (s : Finset ι) (F : MvPolynomial τ R)
    (G : ι → MvPolynomial τ R) : fock F (∑ q ∈ s, G q) = ∑ q ∈ s, fock F (G q) := by
  simp only [fock, MvPolynomial.coeff_sum, Finset.mul_sum, Finset.sum_mul]
  exact Finset.sum_comm

theorem inWj_map {O : Type} [CommRing O] [IsDomain O] {τ : Type} (w : O) (P : MvPolynomial τ O) :
    InWj w (MvPolynomial.map (algebraMap O (KK O)) P) 0 := by
  intro m
  exact ⟨P.coeff m, by simp [MvPolynomial.coeff_map]⟩

theorem valLe_perturb {O Kf : Type} [CommRing O] [IsDomain O] [IsLocalRing O] [Field Kf] [Algebra O Kf] (p : ℕ) (w : O)
    (hw : ¬ IsUnit w) (hsq : w ^ 2 = (p : O)) (D c : ℕ) (hc : 2 * D < c) (a b z : O) (hab : a * b = (p : O) ^ D) :
    ValLe (Kf := Kf) (p : O) D (algebraMap O Kf (a + w ^ c * z)) := by
  obtain ⟨k, hk⟩ : ∃ k, c = 2 * D + (k + 1) := ⟨c - 2 * D - 1, by omega⟩
  have hwc : w ^ c = (p : O) ^ D * w ^ (k + 1) := by rw [hk, pow_add, pow_mul, hsq]
  have hwk : w ^ (k + 1) ∈ IsLocalRing.maximalIdeal O := by
    rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
    exact fun h => hw ((isUnit_pow_iff (Nat.succ_ne_zero k)).1 h)
  have hm : b * w ^ (k + 1) * z ∈ IsLocalRing.maximalIdeal O :=
    Ideal.mul_mem_right _ _ (Ideal.mul_mem_left _ _ hwk)

  have hu : IsUnit (1 + b * w ^ (k + 1) * z) := by
    by_contra hne
    have h1 : (1 + b * w ^ (k + 1) * z) ∈ IsLocalRing.maximalIdeal O :=
      (IsLocalRing.mem_maximalIdeal _).2 hne
    have h2 : (1 : O) ∈ IsLocalRing.maximalIdeal O := by
      have := Ideal.sub_mem _ h1 hm
      simpa using this
    exact (IsLocalRing.maximalIdeal.isMaximal O).ne_top ((Ideal.eq_top_iff_one _).2 h2)
  have ha' : a + w ^ c * z = a * (1 + b * w ^ (k + 1) * z) := by rw [hwc, ← hab]; ring
  refine ⟨a + w ^ c * z, b * ↑hu.unit⁻¹, rfl, ?_⟩
  rw [ha', mul_mul_mul_comm, IsUnit.mul_val_inv, mul_one, hab]


set_option maxHeartbeats 1600000 in
theorem restFlat_of (D : Formalism.BasicNotions.D7) (CLa Ck Crk Cdeg CLa' CD Csz CH CE C6 C18 : ℝ)
    (hXi : RestXi D CLa Ck Crk Cdeg CH CE C6 C18) (hRe : RestReal D CLa Ck Crk Cdeg) :
    RestFlat D CLa Ck Crk Cdeg CLa' CD Csz CH CE C6 C18 := by
  intro hA _ h14b
  obtain ⟨Ct0, CDf, C₂, h0, h1, hC2, hX⟩ := hXi hA h14b
  obtain ⟨C₃, hC3, hR⟩ := hRe hA
  obtain ⟨C6U, hC6U, h6⟩ := one_sided_lemma4_of_admitted_theorem_II
  have h6' := h6 D CLa Ck Crk Cdeg hA
  obtain ⟨C₄, hC4, hII⟩ := hypII_at C6U (C6U + 1) C6U
  refine ⟨Ct0, CDf, max (max C₂ C₃) (max C₄ CDf), h0, h1,
    lt_of_lt_of_le hC2 (le_trans (le_max_left _ _) (le_max_left _ _)), ?_⟩
  intro C hCC p W Qq O Kf _ _ _ _ _ _ _ _ _ _ ι σ j w n' m r _ _ TT L₁ L₂ de h x lam0 aT bT a Y cpp c0 Dp cStar hSet H φ hφ K
    _ _ hk hrk F hFr E' hE' nb B hB hli hc e he htgt hm g hhm hg hbasis
  let _ : Algebra (WF p n') O := algOfIdent j φ
  intro FsB hFsB Θ hΘ
  have c2 : C₂ ≤ C := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hCC
  have c3 : C₃ ≤ C := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hCC
  have c4 : C₄ ≤ C := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hCC
  have c5 : CDf ≤ C := le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hCC
  obtain ⟨tF, DX, htF, hDX, hxi⟩ := hX C c2 p W Qq O Kf ι σ j w n' m r TT L₁ L₂ de h x lam0 aT bT a Y
    cpp c0 Dp cStar hSet H φ hφ K hk hrk F hFr E' hE' nb B hB hli hc e he htgt hm g hhm hg hbasis FsB hFsB Θ hΘ
  obtain ⟨gv, hgv, hreal⟩ := hR C c3 p W Qq O Kf ι σ j w n' m r TT L₁ L₂ de h x lam0 aT bT a Y
    cpp c0 Dp cStar hSet H φ hφ K hk hrk F hFr E' hE' nb B hB hli hc e he htgt hm g hhm hg hbasis FsB hFsB Θ hΘ
  obtain ⟨hII1, hcP⟩ := hII C c4 p n' m r TT L₁ L₂ de h x lam0 aT bT a Y cpp c0 Dp cStar H F hFr
  have hBas := hyps_basic (C := C) (le_trans hC4 c4) H
  have hGn : goodG' r de h x ≤ n' := by have := H.2.2.1.2.2.2; omega
  have hH : CommonHypotheses p n' r (m + 1) := ⟨H.1, H.2.1, hrk, hSet.1.two_le, hSet.1.even⟩
  have hw0 : algebraMap O Kf w ≠ 0 := Formalism.L2.G.Model.w_ne hSet.1

  have hlog : 0 ≤ (TT.card : ℝ) * ((m + 1 : ℕ) : ℝ) ^ 2 * Real.logb p a := by
    have h2a := hBas.two_le_a
    have hp1 : (1 : ℝ) < (p : ℝ) := by
      have := H.1
      have : 1 < p := by omega
      exact_mod_cast this
    have : 0 ≤ Real.logb p a := Real.logb_nonneg hp1 (by linarith)
    positivity
  have hDp : (DX : ℝ) ≤ Dp := by
    have h10 : C * (TT.card : ℝ) * ((m + 1 : ℕ) : ℝ) ^ 2 * Real.logb p a ≤ Dp := H.2.2.2.2.2.2.2.2.2.1
    have : CDf * (TT.card : ℝ) * ((m + 1 : ℕ) : ℝ) ^ 2 * Real.logb p a ≤
        C * (TT.card : ℝ) * ((m + 1 : ℕ) : ℝ) ^ 2 * Real.logb p a := by
      have e1 : ∀ t : ℝ, t * (TT.card : ℝ) * ((m + 1 : ℕ) : ℝ) ^ 2 * Real.logb p a =
          t * ((TT.card : ℝ) * ((m + 1 : ℕ) : ℝ) ^ 2 * Real.logb p a) := fun t => by ring
      rw [e1, e1]
      exact mul_le_mul_of_nonneg_right c5 hlog
    linarith
  have hDp' : DX ≤ Dp := by exact_mod_cast hDp
  have h2D : 2 * DX < cPrime n' r TT.card c0 cpp cStar := by
    have h11 : 8 * (Dp + 1) ≤ cStar := H.2.2.2.2.2.2.2.2.2.2.1
    unfold cPrime
    omega
  refine ⟨tF, DX, htF, hDX, ?_⟩
  intro F1 f1 f2 f3
  obtain ⟨nq, o, sig, hsig, hval⟩ := hxi F1 f1 f2 f3
  have hT : ∀ q, ∃ T : Module.Dual Kf (Vsp Kf (flW (m := m) (dT TT lam0))),
      T ∈ scale (algebraMap O Kf w ^ (-(tF : ℤ))) (dualLat O Kf (HL (O := O) ι σ (flW (dT TT lam0)) e.tgt)) ∧
      T ∈ Re' p ι σ w r (flW (dT TT lam0)) e ∧
      (∀ e' : Edge W Qq (m + 1), IsEdge p n' r e' → e'.tgt = e.tgt → e' ≠ e →
        T ∈ scale (algebraMap O Kf w ^ ((cPrime n' r TT.card c0 cpp cStar : ℕ) : ℤ))
          (Re' p ι σ w r (flW (dT TT lam0)) e')) ∧
      ∃ z : O, be p r (flW (dT TT lam0)) (Θ F1) T =
        kapR hSet.1 ((p : KK O) ^ (kapFl p (m + 1) (dT TT lam0)) *
          fock (subst p n' O w n' r g (F1 : MvPolynomial (TV n' (m + 1)) (KK O))) (sig q) /
            (((∏ s, (dT TT lam0 s).factorial : ℕ) : ℕ) : KK O)) +
          algebraMap O Kf (w ^ (cPrime n' r TT.card c0 cpp cStar) * z) := by
    intro q
    obtain ⟨ho, hmd, hL4⟩ := hsig q
    have hint : InWj w (sig q) 0 := by
      obtain ⟨_, _, _, _, _, _, _, _, _, _, hs⟩ := hL4
      rw [hs]
      exact inWj_map w _
    have hrl : Realisable p n' w n' r gv (cPrime n' r TT.card c0 cpp cStar) (o q) (sig q) := by
      rw [← hcP] at hL4 ⊢
      exact one_sided_lemma4_realisable D C6U (C6U + 1) C6U h6' O (dvrOfStd hSet) (oHyp_of hSet φ) hk hH F L₁ (orbitWindowCount r de h x)
        (goodG' r de h x) hFr.2.1 (twist_of hFr (by have := H.2.1; omega) hGn p (by have := H.1; omega))
        (flatDeg lam0) ⌈a⌉₊ Y c0 0 (cStar + 2 * r * n' * cpp) (Dp : ℝ) hII1 gv hgv (o q) (sig q) hL4
    obtain ⟨T, t1, t2, t3, t4⟩ := hreal (o q) (sig q) hmd hint hrl
    exact ⟨T, scale_neg_mono w hw0 ho _ t1, t2, t3, t4 F1 f2⟩
  choose T t1 t2 t3 z t4 using hT
  refine ⟨∑ q, T q, Submodule.sum_mem _ fun q _ => t1 q, Submodule.sum_mem _ fun q _ => t2 q,
    fun e' he' htg hne => Submodule.sum_mem _ fun q _ => t3 q e' he' htg hne, ?_⟩
  obtain ⟨aa, bb, hx1, hab⟩ := hval
  have hbe : be p r (flW (dT TT lam0)) (Θ F1) (∑ q, T q) =
      algebraMap O Kf (aa + w ^ (cPrime n' r TT.card c0 cpp cStar) * ∑ q, z q) := by
    have e1 : be p r (flW (dT TT lam0)) (Θ F1) (∑ q, T q) = ∑ q, be p r (flW (dT TT lam0)) (Θ F1) (T q) := by
      unfold be
      rw [LinearMap.sum_apply]
    rw [e1]
    simp only [t4, Finset.sum_add_distrib]
    set_option synthInstance.maxHeartbeats 100000 in
      rw [← map_sum, ← Finset.sum_div, ← Finset.mul_sum, ← fock_sum_right, hx1, kapR_alg, map_add (f := _), ← map_sum,
      ← Finset.mul_sum]
  rw [hbe]
  exact valLe_perturb p w hSet.2.1.not_isUnit hSet.1.w_sq DX _ h2D aa bb _ hab

end Formalism.MainNotions.TestSideCounting
end
end

-- bundled from Formalism.SharpRestriction.GrowthBounds.DualFockLinear.Lemma4ElementZero
section
noncomputable section

open MvPolynomial Finset Classical

namespace Formalism.MainNotions.TestSideCounting

open Formalism.MainNotions.G Formalism.GradedWeylDivisibility Formalism.MainNotions.SourceCleaning Formalism.MainNotions.Pf14

theorem lemma4_element_normal_degree {p n' r : ℕ} [NeZero n'] {K : ℕ} [NeZero r] [NeZero K] {O : Type} [CommRing O] [IsDomain O]
    {Fr : Frames n' r} {N₁ G' cP : ℕ} {deg : Fin n' → ℕ} {Y : ℝ} {k : ℕ} (hk : k = r + K) {o : ℕ}
    {sig : MvPolynomial (TV n' k) (KK O)} (hs : OneSidedLemma4Element p K O Fr N₁ G' cP deg Y hk o sig) :
    ∀ mm ∈ sig.support, normDeg r mm = o := by
  subst hk
  obtain ⟨n, obd, xi, dd, mon, -, -, -, -, h5, rfl⟩ := hs
  have hren : rename (castVK (n' := n') (rfl : r + K = r + K)) (monPh O K p Fr mon xi) = monPh O K p Fr mon xi := by
    have : (castVK (n' := n') (rfl : r + K = r + K)) = id := by
      funext v
      rfl
    rw [this, rename_id_apply]
  rw [hren]
  intro mm hmm
  exact h5 mm (support_map_subset _ _ hmm)

theorem lemma4_element_zero {p n' r : ℕ} (hp : 0 < p) [NeZero n'] {K : ℕ} [NeZero r] [NeZero K] {O : Type} [CommRing O] [IsDomain O]
    (Fr : Frames n' r) (N₁ G' cP : ℕ) (deg : Fin n' → ℕ) (Y : ℝ) {k : ℕ} (hk : k = r + K) (o : ℕ) :
    OneSidedLemma4Element p K O Fr N₁ G' cP deg Y hk o (0 : MvPolynomial (TV n' k) (KK O)) := by
  refine ⟨0, fun _ _ => 0, fun i => i.elim0, fun _ _ => 0, 0, fun i => i.elim0, ?_, ?_, ?_, ?_, ?_⟩
  · intro j _ x _ _
    have : 0 ≤ levDeg p Fr deg j x := by
      unfold levDeg
      positivity
    push_cast
    linarith
  · intro j x _ _ c
    simpa using Nat.pow_pos hp
  · intro v hv
    simp at hv
  · intro mm hmm
    simp [monPh] at hmm
  · simp [monPh]

section At

variable (p n' : ℕ) [Fact p.Prime] [NeZero n'] {W Qq O Kf : Type} [CommRing W] [IsDomain W] [IsDiscreteValuationRing W]
  [Field Qq] [Algebra W Qq] [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field Kf]
  [Algebra O Kf] [Algebra (WF p n') O] (ι : Qq →+* Kf) (σ : Qq ≃+* Qq) {j : W →+* O} (w : O) {m : ℕ} (r : ℕ)
  (TT : Finset (Fin n')) (lam0 : Fin n' → Fin (m + 1) → ℤ)

def XiAtN (K : ℕ) [NeZero r] [NeZero K] (hk : m + 1 = r + K) (Fr : Frames n' r) (N₁ G' : ℕ) (Y : ℝ)
    (c0 cP κ : ℕ) (bD : ℝ) (e : Edge W Qq (m + 1)) (g : Matrix (Fin (m + 1)) (Fin (m + 1)) (WF p n')) {nb : ℕ}
    (FsB : Fin nb → ↥((Pol (KK O) (ι := Fin n') (m + 1) (dT TT lam0)).restrictScalars O))
    (Θ : ↥((Pol (KK O) (ι := Fin n') (m + 1) (dT TT lam0)).restrictScalars O) ≃ₗ[O]
      ↥(Vsp Kf (flW (m := m) (dT TT lam0)))) : Prop :=
  ∃ DX : ℕ, (DX : ℝ) ≤ bD ∧
    ∀ F1 : ↥((Pol (KK O) (ι := Fin n') (m + 1) (dT TT lam0)).restrictScalars O),
      (F1 : MvPolynomial (Fin n' × Fin (m + 1)) (KK O)) ∈ SgOp n' TT lam0 c0 FsB →
      Θ F1 ∈ Re p ι σ w r (flW (dT TT lam0)) e →
      Θ F1 ∉ scale (algebraMap O Kf w ^ (1 : ℤ)) (Re p ι σ w r (flW (dT TT lam0)) e) →
      ∃ (nq : ℕ) (o : Fin nq → ℕ) (sig : Fin nq → MvPolynomial (TV n' (m + 1)) (KK O)),
        (∀ q, HasMultideg (sig q) (dT TT lam0) ∧
          OneSidedLemma4Element p K O Fr N₁ G' cP (flatDeg lam0) Y hk (o q) (sig q)) ∧
        ValLe (Kf := KK O) (p : O) DX
          ((p : KK O) ^ κ * fock (subst p n' O w n' r g (F1 : MvPolynomial (TV n' (m + 1)) (KK O))) (∑ q, sig q) /
            (((∏ s, (dT TT lam0 s).factorial : ℕ) : ℕ) : KK O))

def NDAt (c0 : ℕ) (bT : ℝ) (g : Matrix (Fin (m + 1)) (Fin (m + 1)) (WF p n')) {nb : ℕ}
    (FsB : Fin nb → ↥((Pol (KK O) (ι := Fin n') (m + 1) (dT TT lam0)).restrictScalars O)) : Prop :=
  ∃ tF : ℕ, (tF : ℝ) ≤ bT ∧ ∀ f ∈ SgOp n' TT lam0 c0 FsB,
    ∀ mm ∈ (subst p n' O w n' r g f).support, normDeg r mm ≤ tF

variable {p n' ι σ w r TT lam0}

theorem xiAt_of {K : ℕ} [NeZero r] [NeZero K] {hk : m + 1 = r + K} {Fr : Frames n' r} {N₁ G' : ℕ} {Y : ℝ}
    {c0 cP κ : ℕ} {bT bD : ℝ} {e : Edge W Qq (m + 1)} {g : Matrix (Fin (m + 1)) (Fin (m + 1)) (WF p n')} {nb : ℕ}
    {FsB : Fin nb → ↥((Pol (KK O) (ι := Fin n') (m + 1) (dT TT lam0)).restrictScalars O)}
    {Θ : ↥((Pol (KK O) (ι := Fin n') (m + 1) (dT TT lam0)).restrictScalars O) ≃ₗ[O]
      ↥(Vsp Kf (flW (m := m) (dT TT lam0)))}
    (hN : XiAtN p n' ι σ w r TT lam0 K hk Fr N₁ G' Y c0 cP κ bD e g FsB Θ)
    (hD : NDAt p n' w r TT lam0 c0 bT g FsB) :
    XiAt p n' ι σ w r TT lam0 K hk Fr N₁ G' Y c0 cP κ bT bD e g FsB Θ := by
  obtain ⟨DX, hDX, hN⟩ := hN
  obtain ⟨tF, htF, hD⟩ := hD
  refine ⟨tF, DX, htF, hDX, fun F1 h1 h2 h3 => ?_⟩
  obtain ⟨nq, o, sig, hs, hv⟩ := hN F1 h1 h2 h3
  refine ⟨nq, fun q => if o q ≤ tF then o q else 0, fun q => if o q ≤ tF then sig q else 0, fun q => ?_, ?_⟩
  · by_cases hq : o q ≤ tF
    · simp only [ite_eq_left hq]
      exact ⟨hq, (hs q).1, (hs q).2⟩
    · simp only [ite_eq_right hq]
      exact ⟨Nat.zero_le _, Submodule.zero_mem _, lemma4_element_zero (Fact.out : p.Prime).pos Fr N₁ G' cP _ Y hk 0⟩
  · have e1 : fock (subst p n' O w n' r g (F1 : MvPolynomial (TV n' (m + 1)) (KK O)))
        (∑ q, if o q ≤ tF then sig q else 0) =
        fock (subst p n' O w n' r g (F1 : MvPolynomial (TV n' (m + 1)) (KK O))) (∑ q, sig q) := by
      unfold fock
      refine Finset.sum_congr rfl fun mm hmm => ?_
      congr 2
      rw [coeff_sum, coeff_sum]
      refine Finset.sum_congr rfl fun q _ => ?_
      by_cases hq : o q ≤ tF
      · rw [ite_eq_left hq]
      · rw [ite_eq_right hq]
        change 0 = _
        by_contra hne
        have h4 : mm ∈ (sig q).support := mem_support_iff.2 (Ne.symm hne)
        have h5 := lemma4_element_normal_degree hk (hs q).2 mm h4
        have h6 := hD _ h1 mm hmm
        omega
    rw [e1]
    exact hv

end At

def XiStepN (C CD CLa : ℝ) : Prop :=
  ∀ (p : ℕ) (W Qq O Kf : Type) [CommRing W] [IsDomain W] [IsDiscreteValuationRing W] [Field Qq] [Algebra W Qq]
    [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field Kf] [Algebra O Kf]
    (ι : Qq →+* Kf) (σ : Qq ≃+* Qq) (j : W →+* O) (w : O)
    (n' m r : ℕ) [Fact p.Prime] [NeZero n'] (TT : Finset (Fin n')) (L₁ L₂ : ℕ) (de h x : ℝ)
    (lam0 : Fin n' → Fin (m + 1) → ℤ) (aT bT : Fin n' → ℤ) (a Y : ℝ) (cpp c0 Dp cStar : ℕ),
    ∀ hSet : UnramifiedQuadraticSetting p n' W Qq O Kf ι σ j w,
    Hyps C p n' m r TT L₁ L₂ de h x lam0 aT bT a Y cpp c0 Dp cStar →
    ∀ φ : WF p n' ≃+* W, IsWittIdent σ φ →
    ∀ (K : ℕ) [NeZero r] [NeZero K] (hk : m + 1 = r + K) (hrk : r ≤ m + 1),
    ∀ F : Frames n' r, FramesOK TT L₁ L₂ (orbitWindowCount r de h x) (goodG' r de h x) F →
    ∀ E' : Fin n' → ℕ,
      (∀ t ∈ F.TT, E' t ≤ E0 p r (r + K) (orbitWindowCount r de h x) (goodG' r de h x) (cPrime n' r TT.card c0 cpp cStar) ∧
        E' t ≤ flatDeg lam0 t) →
    ∀ (nb : ℕ) (B : Fin nb → RRing O n' (r + K)),
      (∀ i, B i ∈ Gen O p K F
        (symbolSpaces CLa p n' O r K F (flatDeg lam0) L₁ (min (orbitWindowCount r de h x) (2 * TT.card))
          (mStar p F (r + K) (orbitWindowCount r de h x) (p ^ goodG' r de h x) (cPrime n' r TT.card c0 cpp cStar)) a Y)
        (G2d F (flatDeg lam0) E')) →
      LinearIndependent O B → (∃ T : Submodule O (RRing O n' (r + K)), IsCompl (Submodule.span O (Set.range B)) T) →
    ∀ e : Edge W Qq (m + 1), IsEdge p n' r e → e.tgt = colSpan W (1 : Matrix (Fin (m + 1)) (Fin (m + 1)) Qq) →
    ∀ (hm : Matrix (Fin (m + 1)) (Fin (m + 1)) Qq) (g : Matrix (Fin (m + 1)) (Fin (m + 1)) (WF p n')),
      IsUnit hm.det → IsGLW g → IsEdgeBasis p r e (hm * ((matQ φ g)⁻¹).transpose) →
    letI : Algebra (WF p n') O := algOfIdent j φ
    ∀ FsB : Fin nb → ↥((Pol (KK O) (ι := Fin n') (m + 1) (dT TT lam0)).restrictScalars O),
      (∀ b, subst p n' O w n' r g (FsB b : MvPolynomial (TV n' (m + 1)) (KK O)) =
        symB p n' O w hk hrk F g (cPrime n' r TT.card c0 cpp cStar) (p ^ goodG' r de h x) (B b)) →
      ∀ Θ : ↥((Pol (KK O) (ι := Fin n') (m + 1) (dT TT lam0)).restrictScalars O) ≃ₗ[O]
      ↥(Vsp Kf (flW (m := m) (dT TT lam0))),
        IsTrueTheta hSet.1 (dT TT lam0) (flW (dT TT lam0)) (vecE n') hm Θ →
        XiAtN p n' ι σ w r TT lam0 K hk F (orbitWindowCount r de h x) (goodG' r de h x) Y c0 (cPrime n' r TT.card c0 cpp cStar)
          (kapFl p (m + 1) (dT TT lam0))
          (CD * (TT.card : ℝ) * ((m + 1 : ℕ) : ℝ) ^ 2 * Real.logb p a) e g FsB Θ

def NDStep (C Ct0 CLa : ℝ) : Prop :=
  ∀ (p : ℕ) (W Qq O Kf : Type) [CommRing W] [IsDomain W] [IsDiscreteValuationRing W] [Field Qq] [Algebra W Qq]
    [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field Kf] [Algebra O Kf]
    (ι : Qq →+* Kf) (σ : Qq ≃+* Qq) (j : W →+* O) (w : O)
    (n' m r : ℕ) [Fact p.Prime] [NeZero n'] (TT : Finset (Fin n')) (L₁ L₂ : ℕ) (de h x : ℝ)
    (lam0 : Fin n' → Fin (m + 1) → ℤ) (aT bT : Fin n' → ℤ) (a Y : ℝ) (cpp c0 Dp cStar : ℕ),
    ∀ hSet : UnramifiedQuadraticSetting p n' W Qq O Kf ι σ j w,
    Hyps C p n' m r TT L₁ L₂ de h x lam0 aT bT a Y cpp c0 Dp cStar →
    ∀ φ : WF p n' ≃+* W, IsWittIdent σ φ →
    ∀ (K : ℕ) [NeZero r] [NeZero K] (hk : m + 1 = r + K) (hrk : r ≤ m + 1),
    ∀ F : Frames n' r, FramesOK TT L₁ L₂ (orbitWindowCount r de h x) (goodG' r de h x) F →
    ∀ E' : Fin n' → ℕ,
      (∀ t ∈ F.TT, E' t ≤ E0 p r (r + K) (orbitWindowCount r de h x) (goodG' r de h x) (cPrime n' r TT.card c0 cpp cStar) ∧
        E' t ≤ flatDeg lam0 t) →
    ∀ (nb : ℕ) (B : Fin nb → RRing O n' (r + K)),
      (∀ i, B i ∈ Gen O p K F
        (symbolSpaces CLa p n' O r K F (flatDeg lam0) L₁ (min (orbitWindowCount r de h x) (2 * TT.card))
          (mStar p F (r + K) (orbitWindowCount r de h x) (p ^ goodG' r de h x) (cPrime n' r TT.card c0 cpp cStar)) a Y)
        (G2d F (flatDeg lam0) E')) →
      LinearIndependent O B → (∃ T : Submodule O (RRing O n' (r + K)), IsCompl (Submodule.span O (Set.range B)) T) →
    ∀ e : Edge W Qq (m + 1), IsEdge p n' r e → e.tgt = colSpan W (1 : Matrix (Fin (m + 1)) (Fin (m + 1)) Qq) →
    ∀ (hm : Matrix (Fin (m + 1)) (Fin (m + 1)) Qq) (g : Matrix (Fin (m + 1)) (Fin (m + 1)) (WF p n')),
      IsUnit hm.det → IsGLW g → IsEdgeBasis p r e (hm * ((matQ φ g)⁻¹).transpose) →
    letI : Algebra (WF p n') O := algOfIdent j φ
    ∀ FsB : Fin nb → ↥((Pol (KK O) (ι := Fin n') (m + 1) (dT TT lam0)).restrictScalars O),
      (∀ b, subst p n' O w n' r g (FsB b : MvPolynomial (TV n' (m + 1)) (KK O)) =
        symB p n' O w hk hrk F g (cPrime n' r TT.card c0 cpp cStar) (p ^ goodG' r de h x) (B b)) →
      ∀ Θ : ↥((Pol (KK O) (ι := Fin n') (m + 1) (dT TT lam0)).restrictScalars O) ≃ₗ[O]
      ↥(Vsp Kf (flW (m := m) (dT TT lam0))),
        IsTrueTheta hSet.1 (dT TT lam0) (flW (dT TT lam0)) (vecE n') hm Θ →
        NDAt p n' w r TT lam0 c0
          (t0 C Ct0 p TT.card (orbitWindowCount r de h x) L₁ (goodG' r de h x) (m + 1) a + (TT.card : ℝ) * c0) g FsB

def RestXiN (D : Formalism.BasicNotions.D7) (CLa Ck Crk Cdeg CH CE C6 C18 : ℝ) : Prop :=
  tableLineDegreeFive.admitted D CLa Ck Crk Cdeg → PlaneGramData.aux₃ D CH CE C6 C18 →
    ∃ CDf C₁ : ℝ, 0 < CDf ∧ 0 < C₁ ∧ ∀ C : ℝ, C₁ ≤ C → XiStepN C CDf CLa

def RestND (CLa : ℝ) : Prop :=
  ∃ Ct0 C₁ : ℝ, 0 < Ct0 ∧ 0 < C₁ ∧ ∀ C : ℝ, C₁ ≤ C → NDStep C Ct0 CLa

theorem restXi_of (D : Formalism.BasicNotions.D7) (CLa Ck Crk Cdeg CH CE C6 C18 : ℝ)
    (hN : RestXiN D CLa Ck Crk Cdeg CH CE C6 C18) (hD : RestND CLa) : RestXi D CLa Ck Crk Cdeg CH CE C6 C18 := by
  intro hA h14b
  obtain ⟨CDf, C₂, h1, hC2, hN⟩ := hN hA h14b
  obtain ⟨Ct0, C₃, h0, hC3, hD⟩ := hD
  refine ⟨Ct0, CDf, max C₂ C₃, h0, h1, lt_of_lt_of_le hC2 (le_max_left _ _), ?_⟩
  intro C hCC p W Qq O Kf _ _ _ _ _ _ _ _ _ _ ι σ j w n' m r _ _ TT L₁ L₂ de h x lam0 aT bT a Y cpp c0 Dp cStar hSet H φ hφ K
    _ _ hk hrk F hFr E' hE' nb B hB hli hc e he htgt hm g hhm hg hbasis
  let : Algebra (WF p n') O := algOfIdent j φ
  intro FsB hFsB Θ hΘ
  exact xiAt_of
    (hN C (le_trans (le_max_left _ _) hCC) p W Qq O Kf ι σ j w n' m r TT L₁ L₂ de h x lam0 aT bT a Y
      cpp c0 Dp cStar hSet H φ hφ K hk hrk F hFr E' hE' nb B hB hli hc e he htgt hm g hhm hg hbasis FsB hFsB Θ hΘ)
    (hD C (le_trans (le_max_right _ _) hCC) p W Qq O Kf ι σ j w n' m r TT L₁ L₂ de h x lam0 aT bT a Y
      cpp c0 Dp cStar hSet H φ hφ K hk hrk F hFr E' hE' nb B hB hli hc e he htgt hm g hhm hg hbasis FsB hFsB Θ hΘ)

end Formalism.MainNotions.TestSideCounting
end
end

