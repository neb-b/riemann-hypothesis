module

public import Formalism.SharpRestriction.GrowthBounds.DualFockLinear.Bundle0012
public import Formalism.SharpRestriction.GrowthBounds.ProjectionOfIsotypicDecomposition

@[expose] public section

-- bundled from Formalism.SharpRestriction.GrowthBounds.DualFockLinear.RhoTopStepOfPair
section
noncomputable section

namespace Formalism.MainNotions.TestSideCounting

open Formalism.MainNotions.G Formalism.GradedWeylDivisibility Formalism.MainNotions.SourceCleaning Formalism.MainNotions.Pf14 MvPolynomial

theorem topW_lam {n' m : ℕ} (TT : Finset (Fin n')) (lam0 : Fin n' → Fin (m + 1) → ℤ) :
    topW TT lam0 = flW (dT TT lam0) + topW TT (restW TT lam0) := by
  funext s
  by_cases hs : s ∈ TT
  · have := congrFun (lambda_zero_eq_product TT lam0) s
    simp only [topW, if_pos hs, Pi.add_apply] at this ⊢
    exact this
  · funext i
    simp [topW, hs, flW, dT]

theorem ordMax_top {n' m : ℕ} (hm : 2 ≤ m) {TT : Finset (Fin n')} {aT bT : Fin n' → ℤ} {cpp c0 : ℕ} {a : ℝ}
    {lam0 : Fin n' → Fin (m + 1) → ℤ} (hW : tableLineDegreeFive.WeightHyp TT aT bT cpp c0 a lam0) (r : ℕ) :
    ordMax r (topW TT (restW TT lam0)) ≤ ((r * TT.card * c0 : ℕ) : ℤ) := by
  obtain ⟨hb, hdom, hw⟩ := hW
  have hdr := topW_dom TT (restW_dom (by omega) TT lam0 hdom)
  have hl0 : Fin.last m ≠ 0 := by
    intro h
    have := congrArg Fin.val h
    simp at this
    omega
  have hv1 : ((1 : Fin (m + 1)) : ℕ) = 1 := by
    rw [Fin.val_one']
    exact Nat.mod_eq_of_lt (by omega)
  have key : ∀ s, topW TT (restW TT lam0) s 0 - topW TT (restW TT lam0) s (Fin.last m) ≤
      (if s ∈ TT then (c0 : ℤ) else 0) := by
    intro s
    by_cases hs : s ∈ TT
    · have e1 : restW TT lam0 s (Fin.last m) = lam0 s (Fin.last m) := by
        unfold restW flW
        simp [Pi.single_apply, hl0]
      have e0 : restW TT lam0 s 0 = lam0 s 0 - (dT TT lam0 s : ℤ) := by
        unfold restW flW
        simp
      simp only [topW, if_pos hs]
      rw [e0, e1]
      obtain ⟨_, elast, hc⟩ := (hb s).1 hs
      obtain ⟨_, _, hb0, hbc⟩ := hw s hs
      have h01 : lam0 s 1 ≤ lam0 s 0 := hdom s (Fin.zero_le _)
      have hc1 := abs_le.1 (hc 1 (by omega) (by omega))
      unfold dT flatDeg
      rw [if_pos hs, Int.toNat_of_nonneg (by omega), elast]
      omega
    · simp [topW, hs]
  unfold ordMax
  have hr0 : (0 : ℤ) ≤ r := Int.natCast_nonneg _
  calc ∑ s : Fin n', ∑ a : Fin (m + 1) with a.val < r,
        (lamAt (topW TT (restW TT lam0)) s a - lamAt (topW TT (restW TT lam0)) s (Fin.last m))
      ≤ ∑ s : Fin n', (r : ℤ) * (if s ∈ TT then (c0 : ℤ) else 0) :=
        Finset.sum_le_sum fun s _ => le_trans (ord_pos r _ hdr s) (mul_le_mul_of_nonneg_left (key s) hr0)
    _ = ((r * TT.card * c0 : ℕ) : ℤ) := by
        rw [← Finset.mul_sum, Finset.sum_ite_mem, Finset.univ_inter, Finset.sum_const]
        push_cast
        simp only [nsmul_eq_mul]
        ring

def PairTopStep (C CK : ℝ) : Prop :=
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
        PairAt p n' ι σ w r TT (dT TT lam0) (topW TT (restW TT lam0)) (topW TT lam0) c0
          (CK * (TT.card : ℝ) * ((m + 1 : ℕ) : ℝ) ^ 2 * Real.logb p a) e Θ

def RestPairTop (D : Formalism.BasicNotions.D7) (CLa Ck Crk Cdeg : ℝ) : Prop :=
  tableLineDegreeFive.admitted D CLa Ck Crk Cdeg → ∃ CK C₁ : ℝ, 0 < CK ∧ 0 < C₁ ∧ ∀ C : ℝ, C₁ ≤ C → PairTopStep C CK

theorem rhoTopStep_of_pair (D : Formalism.BasicNotions.D7) (C CK : ℝ) (hR : PairTopStep C CK) : RhoTopStep C CK := by
  intro p W Qq O Kf _ _ _ _ _ _ _ _ _ _ ι σ j w n' m r _ _ TT L₁ L₂ de h x lam0 aT bT a Y cpp c0 Dp cStar hSet H φ hφ
    e he htgt hm g hhm hg hbasis Θ hΘ
  have hkr : orbitWindowCount r de h x + 2 * r ≤ (m + 1) - r := H.2.2.2.2.2.2.2.1
  have hr2 : 2 ≤ r := H.2.1
  have hdom : IsDominant lam0 := H.2.2.2.2.1.2.1
  exact rhoAtG_of_pair D hSet.1 r TT (dT TT lam0) (topW TT (restW TT lam0)) (topW TT lam0) (topW_lam TT lam0)
    (topW_dom TT (restW_dom (by omega) TT lam0 hdom)) c0 (r * TT.card * c0)
    (ordMax_top (by omega) H.2.2.2.2.1 r) _ e he Θ
    (hR p W Qq O Kf ι σ j w n' m r TT L₁ L₂ de h x lam0 aT bT a Y cpp c0 Dp cStar hSet H φ hφ
      e he htgt hm g hhm hg hbasis Θ hΘ)

theorem restRhoTop_of_pair (D : Formalism.BasicNotions.D7) (CLa Ck Crk Cdeg : ℝ) (h : RestPairTop D CLa Ck Crk Cdeg) :
    RestRhoTop D CLa Ck Crk Cdeg := by
  intro hA
  obtain ⟨CK, C₁, h1, h2, h3⟩ := h hA
  exact ⟨CK, C₁, h1, h2, fun C hC => rhoTopStep_of_pair D C CK (h3 C hC)⟩

theorem restCloudB_of_pair (D : Formalism.BasicNotions.D7) (CLa Ck Crk Cdeg : ℝ) (h : RestPairTop D CLa Ck Crk Cdeg) :
    RestCloudB D CLa Ck Crk Cdeg :=
  restCloudB_of_top D CLa Ck Crk Cdeg (restRhoTop_of_pair D CLa Ck Crk Cdeg h)

end Formalism.MainNotions.TestSideCounting
end
end

-- bundled from Formalism.SharpRestriction.GrowthBounds.DualFockLinear.ValLeOfVK
section
noncomputable section

open MvPolynomial

namespace Formalism.MainNotions.TestSideCounting

open Formalism.MainNotions.G Formalism.MainNotions.Pf14 Formalism.MainNotions.G.Joints

variable {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]

theorem valLe_of_vK {p : ℕ} (S : UniformizedDVR p O) (D : ℕ) (a : O)
    (h : Formalism.MainNotions.PlaneGramData.leQ (vK p (algebraMap O (KK O) a)) (D : ℝ)) :
    ValLe (Kf := KK O) (p : O) D (algebraMap O (KK O) a) := by
  obtain ⟨q, hq, hqD⟩ := h
  have ha : a ≠ 0 := by
    rintro rfl
    have h0 : vK p (algebraMap O (KK O) 0) = ⊤ := by simp [vK, ordW]
    rw [h0] at hq
    exact WithTop.top_ne_coe hq
  rw [vK_alg p a ha] at hq
  have hq' : (nv a : ℚ) / (ramE p O : ℚ) = q := WithTop.coe_injective hq
  have hr : (0 : ℝ) < (ramE p O : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero (ramE_ne_zero S)
  have hle : nv a ≤ D * ramE p O := by
    rw [← hq'] at hqD
    push_cast at hqD
    rw [div_le_iff₀ hr] at hqD
    exact_mod_cast hqD
  have hne : IsDiscreteValuationRing.addVal O a ≠ ⊤ := fun h0 =>
    ha (IsDiscreteValuationRing.addVal_eq_top_iff.mp h0)
  have hne' : IsDiscreteValuationRing.addVal O (p : O) ≠ ⊤ := fun h0 =>
    S.p_ne (IsDiscreteValuationRing.addVal_eq_top_iff.mp h0)
  have e1 : IsDiscreteValuationRing.addVal O a = (nv a : ℕ∞) := (ENat.coe_toNat hne).symm
  have e2 : IsDiscreteValuationRing.addVal O (p : O) = (ramE p O : ℕ∞) := (ENat.coe_toNat hne').symm
  have hdvd : a ∣ (p : O) ^ D := by
    rw [← IsDiscreteValuationRing.addVal_le_iff_dvd, IsDiscreteValuationRing.addVal_pow, e1, e2,
      nsmul_eq_mul]
    exact_mod_cast hle
  obtain ⟨b, hb⟩ := hdvd
  exact ⟨a, b, rfl, hb.symm⟩

end Formalism.MainNotions.TestSideCounting
end
end

