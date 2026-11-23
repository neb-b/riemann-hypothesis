module

public import Formalism.SharpRestriction.GrowthBounds.DualFockLinear.Bundle0010

@[expose] public section

-- bundled from Formalism.SharpRestriction.GrowthBounds.DualFockLinear.RestCloudBOfTop
section
noncomputable section

namespace Formalism.MainNotions.TestSideCounting

open Formalism.MainNotions.G Formalism.GradedWeylDivisibility Formalism.MainNotions.SourceCleaning Formalism.MainNotions.Pf14 MvPolynomial

def topW {n' m : ℕ} (TT : Finset (Fin n')) (X : Fin n' → Fin (m + 1) → ℤ) : Fin n' → Fin (m + 1) → ℤ :=
  fun s => if s ∈ TT then X s else 0

def specW {n' m : ℕ} (TT : Finset (Fin n')) (X : Fin n' → Fin (m + 1) → ℤ) : Fin n' → Fin (m + 1) → ℤ :=
  fun s => if s ∈ TT then 0 else X s

theorem topW_dom {n' m : ℕ} (TT : Finset (Fin n')) {X : Fin n' → Fin (m + 1) → ℤ} (h : IsDominant X) :
    IsDominant (topW TT X) := by
  intro s
  unfold topW
  split_ifs
  · exact h s
  · exact anti_zero m

theorem specW_dom {n' m : ℕ} (TT : Finset (Fin n')) {X : Fin n' → Fin (m + 1) → ℤ} (h : IsDominant X) :
    IsDominant (specW TT X) := by
  intro s
  unfold specW
  split_ifs
  · exact anti_zero m
  · exact h s

theorem top_add_spec {n' m : ℕ} (TT : Finset (Fin n')) (X : Fin n' → Fin (m + 1) → ℤ) : X = topW TT X + specW TT X := by
  funext s
  by_cases h : s ∈ TT <;> simp [topW, specW, h]

theorem peel_self {n' m : ℕ} (TT : Finset (Fin n')) (X : Fin n' → Fin (m + 1) → ℤ) :
    Peel TT X (topW TT X) (specW TT X) :=
  ⟨fun s hs => by simp [topW, specW, hs], fun s hs => by simp [topW, specW, hs]⟩

theorem restW_off {n' m : ℕ} (TT : Finset (Fin n')) (lam0 : Fin n' → Fin (m + 1) → ℤ) (s : Fin n') (hs : s ∉ TT) :
    restW TT lam0 s = lam0 s := by
  funext i
  simp [restW, flW, dT, hs]

theorem specW_rest {n' m : ℕ} (TT : Finset (Fin n')) (lam0 : Fin n' → Fin (m + 1) → ℤ) :
    specW TT (restW TT lam0) = specW TT lam0 := by
  funext s
  by_cases h : s ∈ TT
  · simp [specW, h]
  · simp only [specW, if_neg h, restW_off TT lam0 s h]

theorem card_lt_le (m r : ℕ) : (Finset.univ.filter fun a : Fin (m + 1) => a.val < r).card ≤ r := by
  calc (Finset.univ.filter fun a : Fin (m + 1) => a.val < r).card ≤ (Finset.range r).card := by
        refine Finset.card_le_card_of_injOn (fun a => a.val) ?_ (Fin.val_injective.injOn)
        intro a ha
        simpa using ha
    _ = r := Finset.card_range r

theorem ordMax_spec {n' m : ℕ} (r : ℕ) (TT : Finset (Fin n')) (lam0 : Fin n' → Fin (m + 1) → ℤ) (cpp : ℕ)
    (hb : ∀ s, s ∉ TT → ∀ i, |lam0 s i| ≤ cpp) : ordMax r (specW TT lam0) ≤ ((2 * r * n' * cpp : ℕ) : ℤ) := by
  unfold ordMax
  have h1 : ∀ s : Fin n', ∀ a : Fin (m + 1),
      lamAt (specW TT lam0) s a - lamAt (specW TT lam0) s (Fin.last m) ≤ 2 * (cpp : ℤ) := by
    intro s a
    by_cases hs : s ∈ TT
    · rw [lamAt_zero (by simp [specW, hs])]
      simp
    · have hz : specW TT lam0 s = lam0 s := by simp [specW, hs]
      have hb' := hb s hs
      unfold lamAt
      rw [hz]
      split_ifs
      · have := abs_le.1 (hb' a)
        have := abs_le.1 (hb' (Fin.last m))
        omega
      · have := abs_le.1 (hb' a.rev)
        have := abs_le.1 (hb' (Fin.last m).rev)
        show -lam0 s a.rev - -lam0 s (Fin.last m).rev ≤ 2 * (cpp : ℤ)
        omega
  calc ∑ s : Fin n', ∑ a : Fin (m + 1) with a.val < r,
        (lamAt (specW TT lam0) s a - lamAt (specW TT lam0) s (Fin.last m))
      ≤ ∑ _s : Fin n', ∑ a : Fin (m + 1) with a.val < r, 2 * (cpp : ℤ) :=
        Finset.sum_le_sum fun s _ => Finset.sum_le_sum fun a _ => h1 s a
    _ = ∑ _s : Fin n', ((Finset.univ.filter fun a : Fin (m + 1) => a.val < r).card : ℤ) * (2 * (cpp : ℤ)) := by
        simp [Finset.sum_const]
    _ ≤ ∑ _s : Fin n', (r : ℤ) * (2 * (cpp : ℤ)) := by
        refine Finset.sum_le_sum fun s _ => ?_
        have := card_lt_le m r
        have h2 : ((Finset.univ.filter fun a : Fin (m + 1) => a.val < r).card : ℤ) ≤ r := by exact_mod_cast this
        nlinarith [Int.natCast_nonneg cpp]
    _ = ((2 * r * n' * cpp : ℕ) : ℤ) := by
        simp [Finset.sum_const]
        ring

def RhoTopStep (C CK : ℝ) : Prop :=
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
        ∃ κ : ℕ, (κ : ℝ) ≤ CK * (TT.card : ℝ) * ((m + 1 : ℕ) : ℝ) ^ 2 * Real.logb p a ∧
          RhoAtG p n' ι σ w r TT (dT TT lam0) (topW TT (restW TT lam0)) (topW TT lam0) c0 (r * TT.card * c0) κ e Θ

def RestRhoTop (D : Formalism.BasicNotions.D7) (CLa Ck Crk Cdeg : ℝ) : Prop :=
  tableLineDegreeFive.admitted D CLa Ck Crk Cdeg → ∃ CK C₁ : ℝ, 0 < CK ∧ 0 < C₁ ∧ ∀ C : ℝ, C₁ ≤ C → RhoTopStep C CK

theorem rhoStep_of_top (D : Formalism.BasicNotions.D7) (C CK : ℝ) (hR : RhoTopStep C CK) : RhoStep C CK := by
  intro p W Qq O Kf _ _ _ _ _ _ _ _ _ _ ι σ j w n' m r _ _ TT L₁ L₂ de h x lam0 aT bT a Y cpp c0 Dp cStar hSet H φ hφ
    e he htgt hm g hhm hg hbasis Θ hΘ
  obtain ⟨κ, hκ, hT⟩ := hR p W Qq O Kf ι σ j w n' m r TT L₁ L₂ de h x lam0 aT bT a Y cpp c0 Dp cStar hSet H φ hφ
    e he htgt hm g hhm hg hbasis Θ hΘ
  have hdom : IsDominant lam0 := H.2.2.2.2.1.2.1
  have hb : ∀ s, s ∉ TT → ∀ i, |lam0 s i| ≤ cpp := fun s hs => (H.2.2.2.2.1.1 s).2 hs
  refine rhoAt_of_G p n' ι σ w r TT lam0 c0 _ _ e Θ κ hκ ?_
  have hPr : Peel TT (restW TT lam0) (topW TT (restW TT lam0)) (specW TT lam0) := by
    have := peel_self TT (restW TT lam0)
    rwa [specW_rest] at this
  have hrest : restW TT lam0 = topW TT (restW TT lam0) + specW TT lam0 := by
    have := top_add_spec TT (restW TT lam0)
    rwa [specW_rest] at this
  exact rho_peel D hSet.1 r TT (dT TT lam0) (fun s hs => by simp [dT, hs]) (restW TT lam0) lam0
    (topW TT (restW TT lam0)) (topW TT lam0) (specW TT lam0) (peel_self TT lam0) hPr (topW_dom TT hdom)
    (specW_dom TT hdom) (top_add_spec TT lam0) hrest c0 (r * TT.card * c0) κ (2 * r * n' * cpp)
    (ordMax_spec r TT lam0 cpp hb) e he Θ hT

theorem restRho_of_top (D : Formalism.BasicNotions.D7) (CLa Ck Crk Cdeg : ℝ) (h : RestRhoTop D CLa Ck Crk Cdeg) :
    RestRho D CLa Ck Crk Cdeg := by
  intro hA
  obtain ⟨CK, C₁, h1, h2, h3⟩ := h hA
  exact ⟨CK, C₁, h1, h2, fun C hC => rhoStep_of_top D C CK (h3 C hC)⟩

theorem restCloudB_of_top (D : Formalism.BasicNotions.D7) (CLa Ck Crk Cdeg : ℝ) (h : RestRhoTop D CLa Ck Crk Cdeg) :
    RestCloudB D CLa Ck Crk Cdeg :=
  restCloudB_of_rho D CLa Ck Crk Cdeg (restRho_of_top D CLa Ck Crk Cdeg h)

end Formalism.MainNotions.TestSideCounting
end
end

-- bundled from Formalism.SharpRestriction.GrowthBounds.DualFockLinear.ScaleZeroIff
section
noncomputable section

open MvPolynomial

namespace Formalism.MainNotions.TestSideCounting

open Formalism.MainNotions.G Formalism.GradedWeylDivisibility Formalism.MainNotions.Pf14 Formalism.MainNotions.SourceCleaning
open Formalism.MainNotions.G.LatticeSystems (la_tw lb_D la_tw_det lb_D_det)
open Formalism.L2.G.Model (Lin Th0 Aa Lin_Pol dE invT_mul_D dual_edgeBasis dual_edge edgeBasis latDual_colSpan w_ne p_eq pQ_ne
  kapR kapR_alg pol_iff inWj_iff pol_of_map)
open Formalism.L2.G.Model.TS

theorem scale_zero_iff {O Kf X : Type} [CommRing O] [Field Kf] [Algebra O Kf] [AddCommGroup X] [Module Kf X] [Module O X]
    [IsScalarTower O Kf X] (c : Kf) (M : Submodule O X) (x : X) : x ∈ scale (c ^ (0 : ℤ)) M ↔ x ∈ M := by
  rw [mem_scale]
  constructor
  · rintro ⟨y, hy, rfl⟩
    simpa using hy
  · intro h
    exact ⟨x, h, by simp⟩

section

variable {p n' : ℕ} [Fact p.Prime] [NeZero n'] {W Qq O Kf : Type} [CommRing W] [IsDomain W] [IsDiscreteValuationRing W]
  [Field Qq] [Algebra W Qq] [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field Kf] [Algebra O Kf]
  {ι : Qq →+* Kf} {σ : Qq ≃+* Qq} {j : W →+* O} {w : O} {m : ℕ}


set_option maxHeartbeats 1600000 in
theorem realAt_gen (hS : HidaSetting p n' W Qq O Kf ι σ j w) (φ : WF p n' ≃+* W) (hφ : IsWittIdent σ φ)
    (hm1 : 1 ≤ m) (r : ℕ) (hr1 : 1 ≤ r) (hr2 : r < m + 1) (d : Fin n' → ℕ) (cP κ : ℕ)
    (hMD : MultDiv O p κ (k := m + 1) d)
    (e : Edge W Qq (m + 1)) (he : IsEdge p n' r e)
    (htgt : e.tgt = colSpan W (1 : Matrix (Fin (m + 1)) (Fin (m + 1)) Qq))
    (hm : Matrix (Fin (m + 1)) (Fin (m + 1)) Qq) (g : Matrix (Fin (m + 1)) (Fin (m + 1)) (WF p n'))
    (hhm : IsUnit hm.det) (hg : IsGLW g) (hbasis : IsEdgeBasis p r e (hm * ((matQ φ g)⁻¹).transpose))
    (Θ : ↥((Pol (KK O) (ι := Fin n') (m + 1) d).restrictScalars O) ≃ₗ[O] ↥(Vsp Kf (flW (m := m) d)))
    (hΘ : IsTrueTheta hS d (flW d) (vecE n') hm Θ) :
    letI : Algebra (WF p n') O := algOfIdent j φ
    ∃ gv : Matrix (Fin (m + 1)) (Fin (m + 1)) (WF p n'), IsGLW gv ∧
    ∀ (o : ℕ) (sig : MvPolynomial (TV n' (m + 1)) (KK O)), HasMultideg sig d → InWj w sig 0 →
      Realisable p n' w n' r gv cP o sig →
      ∃ T : Module.Dual Kf (Vsp Kf (flW (m := m) d)),
        T ∈ scale (algebraMap O Kf w ^ (-(o : ℤ))) (dualLat O Kf (HL (O := O) ι σ (flW d) e.tgt)) ∧
        T ∈ Re' p ι σ w r (flW d) e ∧
        (∀ e' : Edge W Qq (m + 1), IsEdge p n' r e' → e'.tgt = e.tgt → e' ≠ e →
          T ∈ scale (algebraMap O Kf w ^ (cP : ℤ)) (Re' p ι σ w r (flW d) e')) ∧
        ∀ F : ↥((Pol (KK O) (ι := Fin n') (m + 1) d).restrictScalars O),
          Θ F ∈ Re p ι σ w r (flW d) e →
          ∃ z : O, be p r (flW d) (Θ F) T =
            kapR hS ((p : KK O) ^ κ * fock (subst p n' O w n' r g (F : MvPolynomial (TV n' (m + 1)) (KK O))) sig /
              (((∏ s, (d s).factorial : ℕ) : ℕ) : KK O)) + algebraMap O Kf (w ^ cP * z) := by
  letI : Algebra (WF p n') O := algOfIdent j φ
  have hw := w_ne hS
  have h1d : IsUnit (1 : Matrix (Fin (m + 1)) (Fin (m + 1)) Qq).det := by simp
  have h1T : ((1 : Matrix (Fin (m + 1)) (Fin (m + 1)) Qq)⁻¹).transpose = 1 := by simp
  set b := hm * ((matQ φ g)⁻¹).transpose with hbdef
  have htg : e.tgt = colSpan W (b * lb_D (m + 1) r ((p : ℕ) : Qq)) := hbasis.2.2
  obtain ⟨gv, hgv, hgvX⟩ := exists_gv hS φ (b * lb_D (m + 1) r ((p : ℕ) : Qq)) (by rw [← htg, htgt])
  have hrel : ((matQ φ gv)⁻¹).transpose = (b⁻¹).transpose * dE (m + 1) r ((p : ℕ) : Qq) := by
    rw [hgvX]
    exact invT_mul_D b hbasis.1 r _ (pQ_ne hS)
  have hbv : IsEdgeBasis p r e.dual (1 * ((matQ φ gv)⁻¹).transpose) := by
    rw [Matrix.one_mul, hrel]
    exact dual_edgeBasis p r (pQ_ne hS) e b hbasis
  obtain ⟨Θv, ⟨hv1, hv2⟩, hv3⟩ := theta_exists p n' W Qq O Kf ι σ j w hS φ hφ m r (vecE n') d (flW d) hr1 hr2
    (isFlat_flW d) 1 h1d
  obtain ⟨Θ', ⟨_, h2'⟩, h3'⟩ := theta_exists p n' W Qq O Kf ι σ j w hS φ hφ m r (vecE n') d (flW d) hr1 hr2
    (isFlat_flW d) hm hhm
  have hΘeq : Θ = Θ' := LinearEquiv.ext fun F => Subtype.ext ((hΘ F).trans (h3' F).symm)
  subst hΘeq
  obtain ⟨thK, hthK⟩ := exists_thK Kf hm1 d
  obtain ⟨hE1, _, hE3⟩ := edgePlane p n' W Qq O Kf ι σ j w hS φ hφ m r 1 h1d
  refine ⟨gv, hgv, ?_⟩
  intro o sig hmd hint hreal
  obtain ⟨Ff, hA, hmdF, hsym, hoth⟩ := hreal
  let F' : ↥((Pol (KK O) (ι := Fin n') (m + 1) d).restrictScalars O) := ⟨Ff, hmdF d hmd⟩
  set cc : Kf := (p : Kf) ^ κ / (((∏ s, (d s).factorial : ℕ) : ℕ) : Kf) with hcc
  refine ⟨TY thK cc ((algebraMap O Kf w ^ (-(o : ℤ))) • Θv F'), ?_, ?_, ?_, ?_⟩
  · rw [htgt]
    apply FD_HL thK hS hm1 hthK κ hMD 1 h1d
    rw [h1T]
    exact mem_scale.2 ⟨Θv F', (hv1 F').1 hA, rfl⟩
  · rw [← scale_zero_iff (algebraMap O Kf w)]
    apply FD_edge thK hS hm1 hthK κ hMD r e b hbasis
    have h1 : InWjRg p n' O w r (flatLetters (vecE n')) gv
        (F' : MvPolynomial (Fin n' × Fin (m + 1)) (KK O)) (o + 0) := by
      intro mm
      obtain ⟨c1, hc1⟩ := hsym mm
      obtain ⟨c2, hc2⟩ := hint mm
      refine ⟨c2 + w ^ cP * c1, ?_⟩
      have e1 : AddMonoidAlgebra.coeff (subst p n' O w n' r gv Ff) mm =
          AddMonoidAlgebra.coeff (subst p n' O w n' r gv Ff - C (algebraMap O (KK O) (w ^ o)) * sig) mm +
            algebraMap O (KK O) (w ^ o) * AddMonoidAlgebra.coeff sig mm := by
        rw [coeff_sub, coeff_C_mul]
        ring
      show AddMonoidAlgebra.coeff (subst p n' O w n' r gv Ff) mm = _
      rw [e1, hc1, hc2, ← map_mul, ← map_add (f := _)]
      congr 1
      ring
    have h2 := (hv2 gv hgv e.dual hbv F' (o + 0)).1 h1
    exact scale_shift (algebraMap O Kf w) hw o 0 _ h2
  · intro e' he' htg' hne
    obtain ⟨b', hb'⟩ := edgeBasis hS m r e' he'
    apply FD_edge thK hS hm1 hthK κ hMD r e' b' hb'
    have hd' := dual_edge hS m r e' he'
    have hd := dual_edge hS m r e he
    have hsrc : e'.dual.src = colSpan W (1 : Matrix (Fin (m + 1)) (Fin (m + 1)) Qq) := by
      show latDual e'.tgt = _
      rw [htg', htgt, latDual_colSpan _ h1d, h1T]
    obtain ⟨g', hg', hbg'⟩ := hE1 e'.dual hd'.1 hsrc
    have hpl : ratPlane p n' r g' ≠ ratPlane p n' r gv := by
      intro hEq
      have h5 : e'.dual = e.dual := (hE3 g' gv e'.dual e.dual hg' hgv hbg' hbv).2 hEq
      apply hne
      rw [← hd'.2, h5, hd.2]
    have h1 : InWjRg p n' O w r (flatLetters (vecE n')) g'
        (F' : MvPolynomial (Fin n' × Fin (m + 1)) (KK O)) (o + cP) := hoth g' hg' hpl
    have h2 := (hv2 g' hg' e'.dual hbg' F' (o + cP)).1 h1
    exact scale_shift (algebraMap O Kf w) hw o cP _ h2
  · intro F hF
    have hpf := pair_formula thK hS φ hφ r hr1 hr2 hthK κ hm hhm g gv hg hgv hbasis.1 hrel Θ Θv hΘ hv3 F F'

    have hF0 : InWjRg p n' O w r (flatLetters (vecE n')) g (F : MvPolynomial (Fin n' × Fin (m + 1)) (KK O)) 0 :=
      (h2' g hg e hbasis F 0).2 (by
        have : ((0 : ℕ) : ℤ) = 0 := rfl
        rw [this, scale_zero_iff]
        exact hF)
    obtain ⟨G0, hG0⟩ := (inWj_iff hS _ 0).1 hF0
    rw [pow_zero, one_smul] at hG0
    have hG0' : map (kapR hS) (subst p n' O w n' r g (F : MvPolynomial (TV n' (m + 1)) (KK O))) =
        map (algebraMap O Kf) G0 := hG0
    have hG0P : G0 ∈ Pol O (m + 1) d := by
      apply pol_of_map hS
      rw [← hG0', subst_Lin hS φ hφ r hm hhm g hg F.1 F.2]
      exact Submodule.smul_mem _ _ (Lin_Pol _ _ (Lin_Pol _ _ ((pol_iff hS _ _ _).1 F.2)))
    obtain ⟨E, hE⟩ := (inWj_iff hS _ (o + cP)).1 hsym
    obtain ⟨z, hz⟩ := int_pair (Kf := Kf) p κ hMD G0 hG0P E
    refine ⟨z, ?_⟩
    set SF := subst p n' O w n' r g (F : MvPolynomial (TV n' (m + 1)) (KK O)) with hSF
    set Rr := subst p n' O w n' r gv Ff - C (algebraMap O (KK O) (w ^ o)) * sig with hRr
    have e1 : subst p n' O w n' r gv (F' : MvPolynomial (TV n' (m + 1)) (KK O)) =
        algebraMap O (KK O) (w ^ o) • sig + Rr := by
      rw [hRr, smul_eq_C_mul]
      show subst p n' O w n' r gv Ff = _
      ring
    have e2 : be p r (flW d) (Θ F) (TY thK cc ((algebraMap O Kf w ^ (-(o : ℤ))) • Θv F')) =
        algebraMap O Kf w ^ (-(o : ℤ)) * be p r (flW d) (Θ F) (TY thK cc (Θv F')) := by
      simp only [be, map_smul, LinearMap.smul_apply, smul_eq_mul]
      ring
    have e3 : kapR hS (fock SF Rr) = algebraMap O Kf w ^ (o + cP) *
        fockR (map (algebraMap O Kf) G0) (map (algebraMap O Kf) E) := by
      rw [fock_eq_fockR, ← fockR_map, hG0', hE, tsact_smul_right]
    rw [e2, hpf, e1, fock_eq_fockR, fockR_add_right, tsact_smul_right, ← fock_eq_fockR, ← fock_eq_fockR]
    have e4 : kapR hS ((p : KK O) ^ κ * (algebraMap O (KK O) (w ^ o) * fock SF sig + fock SF Rr) /
        (((∏ s, (d s).factorial : ℕ) : ℕ) : KK O)) =
        algebraMap O Kf w ^ o * kapR hS ((p : KK O) ^ κ * fock SF sig / (((∏ s, (d s).factorial : ℕ) : ℕ) : KK O)) +
          algebraMap O Kf w ^ (o + cP) * algebraMap O Kf z := by
      rw [← hz]
      simp only [map_div₀, map_mul, map_add (f := _), map_pow, map_natCast, kapR_alg, e3]
      ring
    rw [e4, zpow_neg, zpow_natCast, map_mul, map_pow, pow_add]
    field_simp

end

theorem realStep (C CLa : ℝ) : RealStep C CLa := by
  intro p W Qq O Kf _ _ _ _ _ _ _ _ _ _ ι σ j w n' m r _ _ TT L₁ L₂ de h x lam0 aT bT a Y cpp c0 Dp cStar hSet H φ hφ K
    _ _ hk hrk F hFr E' hE' nb B hB hli hc e he htgt hm g hhm hg hbasis FsB hFsB Θ hΘ
  have hkr : orbitWindowCount r de h x + 2 * r ≤ (m + 1) - r := H.2.2.2.2.2.2.2.1
  have hr2 : 2 ≤ r := H.2.1
  exact realAt_gen hSet.1 φ hφ (by omega) r (by omega) (by omega) (dT TT lam0) _ _
    (multDiv_kapFl O p (dvrOfStd hSet).p_mem (dT TT lam0)) e he htgt hm g hhm hg hbasis Θ hΘ

theorem restReal (D : Formalism.BasicNotions.D7) (CLa Ck Crk Cdeg : ℝ) : RestReal D CLa Ck Crk Cdeg :=
  fun _ => ⟨1, one_pos, fun C _ => realStep C CLa⟩

theorem restFlat_of_Xi (D : Formalism.BasicNotions.D7) (CLa Ck Crk Cdeg CLa' CD Csz CH CE C6 C18 : ℝ)
    (hXi : RestXi D CLa Ck Crk Cdeg CH CE C6 C18) : RestFlat D CLa Ck Crk Cdeg CLa' CD Csz CH CE C6 C18 :=
  restFlat_of D CLa Ck Crk Cdeg CLa' CD Csz CH CE C6 C18 hXi (restReal D CLa Ck Crk Cdeg)

end Formalism.MainNotions.TestSideCounting
end
end

-- bundled from Formalism.SharpRestriction.GrowthBounds.DualFockLinear.WspanLeOpCl
section
noncomputable section

open MvPolynomial Finset Classical

namespace Formalism.MainNotions.TestSideCounting

open Formalism.MainNotions.G Formalism.GradedWeylDivisibility Formalism.MainNotions.SourceCleaning Formalism.MainNotions.Pf14
open Formalism.L2.G.Model (Lin)

section Words

variable {R : Type} [CommRing R] {n' k : ℕ}

def WSpan (l : List (Fin n' × (Fin k × Fin k))) (h : MvPolynomial (Fin n' × Fin k) R) :
    Submodule R (MvPolynomial (Fin n' × Fin k) R) :=
  Submodule.span R {y | ∃ l' : List (Fin n' × (Fin k × Fin k)), l'.map Prod.fst = l.map Prod.fst ∧ y = opWord l' h}

theorem wspan_op (l : List (Fin n' × (Fin k × Fin k))) (h : MvPolynomial (Fin n' × Fin k) R) (s : Fin n')
    (x : Fin k × Fin k) (c c' : Fin k) {z : MvPolynomial (Fin n' × Fin k) R} (hz : z ∈ WSpan l h) :
    X (s, c) * pderiv (s, c') z ∈ WSpan ((s, x) :: l) h := by
  unfold WSpan at hz ⊢
  induction hz using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨l', hl', rfl⟩ := hy
    exact Submodule.subset_span ⟨(s, (c, c')) :: l', by simp [hl'], rfl⟩
  | zero => simp
  | add a b _ _ ha hb =>
    rw [map_add (f := _), mul_add]
    exact Submodule.add_mem _ ha hb
  | smul a y _ hy =>
    rw [Derivation.map_smul, mul_smul_comm]
    exact Submodule.smul_mem _ a hy

theorem Lin_word (N N' : Fin n' → Matrix (Fin k) (Fin k) R) (h : ∀ s, N s * N' s = 1)
    (f : MvPolynomial (Fin n' × Fin k) R) :
    ∀ l : List (Fin n' × (Fin k × Fin k)), Lin N (opWord l f) ∈ WSpan l (Lin N f) := by
  intro l
  induction l with
  | nil => exact Submodule.subset_span ⟨[], rfl, rfl⟩
  | cons y l ih =>
    obtain ⟨s, a, b⟩ := y
    show Lin N (X (s, a) * pderiv (s, b) (opWord l f)) ∈ _
    rw [map_mul, Lin_X, Lin_pderiv N N' h, Finset.sum_mul]
    refine Submodule.sum_mem _ fun b' _ => ?_
    rw [Finset.mul_sum]
    refine Submodule.sum_mem _ fun c _ => ?_
    rw [mul_smul_comm, MvPolynomial.C_mul', smul_mul_assoc]
    exact Submodule.smul_mem _ _ (Submodule.smul_mem _ _ (wspan_op l _ s (a, b) b' c ih))

theorem wspan_le_OpCl (TT : Finset (Fin n')) (c : ℕ) (M : Submodule R (MvPolynomial (Fin n' × Fin k) R))
    (l : List (Fin n' × (Fin k × Fin k))) (h1 : ∀ z ∈ l, z.1 ∈ TT) (h2 : ∀ s, (l.filter fun z => z.1 = s).length ≤ c)
    {h : MvPolynomial (Fin n' × Fin k) R} (hh : h ∈ M) : WSpan l h ≤ OpCl TT c M := by
  rw [WSpan, Submodule.span_le]
  rintro y ⟨l', hl', rfl⟩
  refine Submodule.subset_span ⟨h, hh, l', ?_, ?_, rfl⟩
  · intro z hz
    have hz' : z.1 ∈ l.map Prod.fst := hl' ▸ List.mem_map_of_mem hz
    obtain ⟨z', hz'', e⟩ := List.mem_map.1 hz'
    exact e ▸ h1 z' hz''
  · intro s
    have e : ∀ L : List (Fin n' × (Fin k × Fin k)), (L.filter fun z => decide (z.1 = s)).length =
        ((L.map Prod.fst).filter fun t => decide (t = s)).length := by
      intro L
      rw [List.filter_map, List.length_map]
      rfl
    rw [e, hl', ← e]
    exact h2 s

theorem Lin_OpCl (N N' : Fin n' → Matrix (Fin k) (Fin k) R) (h : ∀ s, N s * N' s = 1) (TT : Finset (Fin n')) (c : ℕ)
    (M M' : Submodule R (MvPolynomial (Fin n' × Fin k) R)) (hM : ∀ f ∈ M, Lin N f ∈ M') :
    ∀ f ∈ OpCl TT c M, Lin N f ∈ OpCl TT c M' := by
  intro f hf
  unfold OpCl at hf
  induction hf using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨f0, hf0, l, h1, h2, rfl⟩ := hy
    exact wspan_le_OpCl TT c M' l h1 h2 (hM f0 hf0) (Lin_word N N' h f0 l)
  | zero => rw [map_zero]; exact Submodule.zero_mem _
  | add x y _ _ hx hy => rw [map_add (f := _)]; exact Submodule.add_mem _ hx hy
  | smul a x _ hx => rw [map_smul]; exact Submodule.smul_mem _ _ hx

end Words

end Formalism.MainNotions.TestSideCounting
end
end

