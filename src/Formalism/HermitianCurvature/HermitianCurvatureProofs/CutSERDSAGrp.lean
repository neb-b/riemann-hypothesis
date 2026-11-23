module

public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0266
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0265
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0173

@[expose] public section

open Matrix

noncomputable section

namespace Formalism.FourierDecayAlt.P.CutMP

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.P.BetaSesquilinearity Formalism.FourierDecayAlt.P.JFxB CapInv

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

theorem rdsag_capInv {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (P : M.Par)
    (Bs : B.RealPlaceData P.k P.r Wp Wq) (y : ℂ) (Θ : B.DiffOp P.k P.r Wp Wq) (hm : P.r ≤ B.opOrder Θ) :
    ((∀ (F : B.Mat P.k P.r → (Wq →L[ℂ] Wp)) (g : B.Mat P.k P.r), g ∈ B.GV P.k P.r →
          B.CkOn (B.opOrder Θ : ℕ∞) {g} F → B.opApply Θ F g = capA P.k P.r y F g) →
        B.Commutes Bs (B.GPos Bs) Θ) ∧
      ((∀ (F : B.Mat P.k P.r → (Wq →L[ℂ] Wp)) (g : B.Mat P.k P.r), g ∈ B.GV P.k P.r →
          B.CkOn (B.opOrder Θ : ℕ∞) {g} F → B.opApply Θ F g = capAv P.k P.r y F g) →
        B.Commutes Bs (B.GPos Bs) Θ) := by
  have key : ∀ (G : (B.Mat P.k P.r → (Wq →L[ℂ] Wp)) → B.Mat P.k P.r → (Wq →L[ℂ] Wp)),
      (∀ (F : B.Mat P.k P.r → (Wq →L[ℂ] Wp)), CkOn ((P.r : ℕ) : ℕ∞) (GV P.k P.r) F → ∀ p, Bs.inSS p →
        ∀ g ∈ GV P.k P.r, G (rho Bs p F) g = rho Bs p (G F) g) →
      (∀ (F : B.Mat P.k P.r → (Wq →L[ℂ] Wp)) (g : B.Mat P.k P.r), g ∈ B.GV P.k P.r →
          B.CkOn (B.opOrder Θ : ℕ∞) {g} F → B.opApply Θ F g = G F g) →
        B.Commutes Bs (B.GPos Bs) Θ := by
    intro G hG hA p hp f hf g hg
    have hgG : g ∈ GV P.k P.r := hg.1
    obtain ⟨h1, h2, h3, h4⟩ := hp
    have ha : (Matrix.of p.1.1)⁻¹ * (Matrix.of p.1.2)⁻¹ ∈ GV P.k P.r := gv_mul (gv_inv h1.1) (gv_inv h2.1)
    have hb : Matrix.of p.2.2 * Matrix.of p.2.1 ∈ GV P.k P.r := gv_mul h4.1 h3.1
    have hck : ∀ (F : B.Mat P.k P.r → (Wq →L[ℂ] Wp)) (x : B.Mat P.k P.r), x ∈ GV P.k P.r →
        CkOn (B.opOrder Θ : ℕ∞) (GV P.k P.r) F → CkOn (B.opOrder Θ : ℕ∞) {x} F := by
      intro F x hx hF g₀ hg₀
      rw [Set.mem_singleton_iff] at hg₀
      subst hg₀
      exact hF _ hx
    have hfr : CkOn ((P.r : ℕ) : ℕ∞) (GV P.k P.r) f := sCkOn_mono (by exact_mod_cast hm) hf
    have hrho : CkOn (B.opOrder Θ : ℕ∞) (GV P.k P.r) (rho Bs p f) := by
      rw [rho_eq_trn']; exact CkOn_trn _ ha hb hf
    have hx : sgs p g ∈ GV P.k P.r := by
      rw [show sgs p g = (Matrix.of p.1.1)⁻¹ * (Matrix.of p.1.2)⁻¹ * g * (Matrix.of p.2.2 * Matrix.of p.2.1) by
        simp [sgs, Matrix.mul_assoc]]
      exact gv_mul (gv_mul ha hgG) hb
    rw [hA _ g hgG (hck _ g hgG hrho), hG f hfr p ⟨h1, h2, h3, h4⟩ g hgG]
    simp only [rho]
    rw [hA f (sgs p g) hx (hck f _ hx hf)]
  constructor
  · exact key _ fun F hF p hp g hg =>
      (rho_AA_ck Bs hF (Q.uC P.k P.r 0 y) 0 hp hg).1
  · exact key _ fun F hF p hp g hg =>
      (rho_AA_ck Bs hF 0 (y - ((2 * P.r + P.k : ℕ) : ℂ) / 2) hp hg).2

end Formalism.FourierDecayAlt.P.CutMP

namespace Formalism.FourierDecayAlt.P.CutMP

open Formalism.FourierDecayAlt Formalism.REAL Formalism.QuantumDeterminants

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

theorem rdsag_toda {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (P : M.Par)
    (Bs : B.RealPlaceData P.k P.r Wp Wq) (y : ℂ) (J : B.Mat P.k P.r → (Wq →L[ℂ] Wp))
    (hJ : J ∈ Q.FFl P.k P.r Bs.z Bs.z' Bs.π Bs.π' 0 (Gauge.OmB Bs)) (c : Fin P.r → ℂ) (hc : c ∈ OmX P.r)
    (g : Q.Mx P.k P.r) (hg : g ∈ Q.Glev P.k P.r (Fin.last P.r))
    (hcg : Q.wCell P.k P.r (Fin.last P.r) c * g ∈ Gauge.OmB Bs) :
    Q.resG P.k P.r (Fin.last P.r) (capA P.k P.r y J) c g =
      dMul (drF P.r) (Q.crd (Q.cmp (Q.vAB P.r y P.r) 0) (Q.resG P.k P.r (Fin.last P.r) J)) c g := by
  have hGG := JDAToda.gg_pos Bs hc hg hcg
  have hx : (c, g) ∈ Q.DomR P.k P.r Bs.z Bs.z' := ⟨hc, hg, hGG⟩
  obtain ⟨hf, hLf, hRf, -⟩ := hJ
  rw [JDAToda.omB_eq] at hf hLf hRf
  have hm := JDAToda.minorCell_of Bs hf hLf hRf y (c, g) hx
  have hcell := Formalism.FourierDecayAlt.P.raising_cell P.k P.r (Wq →L[ℂ] Wp) J (Q.uC P.k P.r 0 y) c g hg
  simp only [dMul, drF, Q.crd, Q.cmp, ↓reduceIte] at hm ⊢
  rw [← hm]
  simp only [Q.resG, capA]
  rw [hcell, JDAToda.uC_zero, smul_comm]

end Formalism.FourierDecayAlt.P.CutMP

namespace Formalism.FourierDecayAlt.P.CutMP.TVG

open Formalism.FourierDecayAlt Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.P.Qx5 Formalism.FourierDecayAlt.P.Qx2 Formalism.FourierDecayAlt.P.PBN Formalism.FourierDecayAlt.P.PBN.MC

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

theorem rdsag_tvGrp {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (P : M.Par)
    (Bs : B.RealPlaceData P.k P.r Wp Wq) (y : ℂ) (J : B.Mat P.k P.r → (Wq →L[ℂ] Wp))
    (hJ : J ∈ Q.FFl P.k P.r Bs.z Bs.z' Bs.π Bs.π' 0 (Gauge.OmB Bs)) (c : Fin P.r → ℂ) (hc : c ∈ OmX P.r)
    (g : Q.Mx P.k P.r) (hg : g ∈ Q.Glev P.k P.r (Fin.last P.r))
    (hcg : Q.wCell P.k P.r (Fin.last P.r) c * g ∈ Gauge.OmB Bs) :
    kvM P.k P.r P.r (kvTop P.k P.r y) J (Q.wCell P.k P.r (Fin.last P.r) c * g) =
      kvC P.r (kvTop P.k P.r y) P.r (fun c' => J (Q.wCell P.k P.r (Fin.last P.r) c' * g)) c := by
  have hGG := JDAToda.gg_pos Bs hc hg hcg
  have hx : (c, g) ∈ Q.DomR P.k P.r Bs.z Bs.z' := ⟨hc, hg, hGG⟩
  obtain ⟨hf, hLf, hRf, -⟩ := hJ
  rw [JDAToda.omB_eq] at hf hLf hRf
  set D := OmPlus P.k P.r Bs.z Bs.z' with hDdef
  have hD : IsOpen D := Formalism.FourierDecayAlt.P.SmoothnessOnGoodSet.isOpen_OmPlus Bs.z Bs.z'
  let k := P.k
  let r := P.r
  let E := Wq →L[ℂ] Wp
  let TorV (hD : IsOpen D) (j : ℕ) : Subalgebra ℂ (SA E hD) :=
    Algebra.adjoin ℂ {x | ∃ l : Fin r, l.val < j ∧ x = EA hD (esI k r l) (esI k r l)}

  have comm_TorV (hD : IsOpen D) (j : ℕ) (p q : Fin (2 * r + k + 1))
      (hp : ∀ l : Fin r, l.val < j → p ≠ esI k r l) (hq : ∀ l : Fin r, l.val < j → q ≠ esI k r l) (P : SA E hD)
      (hP : P ∈ TorV hD j) : Commute (EA hD p q) P := by
    induction hP using Algebra.adjoin_induction with
    | mem y hy =>
      obtain ⟨l, hl, rfl⟩ := hy
      have h := EA_gl (E := E) hD p q (esI k r l) (esI k r l)
      rw [if_neg (hq l hl), if_neg (fun e => hp l hl e.symm), sub_zero] at h
      exact sub_eq_zero.1 h
    | algebraMap c => exact Algebra.commute_algebraMap_right c _
    | add y₁ y₂ _ _ h₁ h₂ => exact h₁.add_right h₂
    | mul y₁ y₂ _ _ h₁ h₂ => exact h₁.mul_right h₂

  have TorV_mono (hD : IsOpen D) {j j' : ℕ} (h : j ≤ j') : TorV hD j ≤ TorV hD j' := Algebra.adjoin_mono fun x ⟨l, hl, hx⟩ => ⟨l, lt_of_lt_of_le hl h, hx⟩

  have EAs_mem_TorV (hD : IsOpen D) (l : Fin r) {j : ℕ} (h : l.val < j) :
      EA (E := E) hD (esI k r l) (esI k r l) ∈ TorV hD j := Algebra.subset_adjoin ⟨l, h, rfl⟩

  have root_action_on_truncated_vector (hD : IsOpen D) (z' : Fin (2 * r + k + 1) → ℂ) (hz' : inWb k r z') (hRR : RightRuleEv)
      {f : Mx k r → E} (hf : SmoothLev k r 0 D f) (hRf : RightEq k r z' 0 D f) (a b : Fin r) (hab : b.val < a.val) :
      ((EA hD (esI k r a) (esI k r b) : SA E hD) : Module.End ℂ (VS k r 0 D E)) ⟨cut k r 0 D f, cut_mem hD hf⟩ =
        (if a.val = b.val + 1 then (1 : ℂ) else 0) • ⟨cut k r 0 D f, cut_mem hD hf⟩ := by
    apply Subtype.ext
    funext g
    by_cases hg : g ∈ Glev k r 0 ∩ D
    · rw [EA_val, ev_E hD _ _ _ hg]
      have hloc := (good_eh (E := E) hD (cI (esI k r a)) (cI (esI k r b))).loc (cut k r 0 D f) f
        (fun x hx => cut_of_mem f hx) g hg
      simp only [posL_cI] at hloc
      rw [posL_cI, posL_cI]
      show EH k r (esI k r a) (esI k r b) (cut k r 0 D f) g = (if a.val = b.val + 1 then (1 : ℂ) else 0) • cut k r 0 D f g
      rw [hloc, hRR E k r z' D f hz' hD hf hRf g hg a b hab, cut_of_mem f hg]
    · show ((Eh hD (cI (esI k r a)) (cI (esI k r b)) ⟨cut k r 0 D f, cut_mem hD hf⟩ : VS k r 0 D E) : Mx k r → E) g =
        (if a.val = b.val + 1 then (1 : ℂ) else 0) • cut k r 0 D f g
      rw [(Eh hD (cI (esI k r a)) (cI (esI k r b)) ⟨cut k r 0 D f, cut_mem hD hf⟩).2.2 g hg,
        show cut k r 0 D f g = 0 from Set.indicator_of_notMem hg f, smul_zero]

  have la_torus (hD : IsOpen D) (hTC : TorusCellv) (v₀ : VS k r 0 D E) (g₀ : Mx k r)
      (hg₀ : g₀ ∈ Glev k r (Fin.last r)) (hcell : ∀ c ∈ OmX r, wCell k r (Fin.last r) c * g₀ ∈ Glev k r 0 ∩ D)
      (l : Fin r) (w' : ℂ) (x : SA E hD) (c : Fin r → ℂ) (hc : c ∈ OmX r) :
      La hD v₀ (wCell k r (Fin.last r) c * g₀) (Tm (EA hD) w' (esI k r l) (esI k r l) * x) =
        w' • La hD v₀ (wCell k r (Fin.last r) c * g₀) x -
          pbOp l (fun c' => La hD v₀ (wCell k r (Fin.last r) c' * g₀) x) c := by
    have hγ := hcell c hc
    rw [La_apply, La_apply]
    simp only [Tm, Subalgebra.coe_mul, Subalgebra.coe_add, Module.End.mul_apply, LinearMap.add_apply, EA_val,
      Submodule.coe_add, Pi.add_apply, ite_true, Subalgebra.coe_algebraMap, Module.algebraMap_end_apply,
      Submodule.coe_smul, Pi.smul_apply]
    rw [ev_E hD _ _ _ hγ, posL_cI, hTC E k r D _ hD ((x : Module.End ℂ (VS k r 0 D E)) v₀).2.1 c hc g₀ hg₀ hγ.2 l,
      sub_eq_add_neg]
    rfl

  have claimV (hRR : RightRuleEv) (hLR : LeftRuleCellv) (hTC : TorusCellv) (hCh : MirrorChainExpansion)
      (hD : IsOpen D) (v₀ : VS k r 0 D E) (g₀ : Mx k r) (w : ℂ)
      (z z' : Fin (2 * r + k + 1) → ℂ) (hz : inWb k r z) (hz' : inWb k r z')
      (hN : ∀ g ∈ Glev k r 0 ∩ D, ∀ n ∈ Nlev k r 0, n * g ∈ D)
      {f : Mx k r → E} (hf : SmoothLev k r 0 D f) (hLf : LeftEq k r z 0 D f) (hRf : RightEq k r z' 0 D f)
      (hv : v₀ = ⟨cut k r 0 D f, cut_mem hD hf⟩) (hg₀ : g₀ ∈ Glev k r (Fin.last r))
      (hcell : ∀ c ∈ OmX r, wCell k r (Fin.last r) c * g₀ ∈ Glev k r 0 ∩ D) :
      ∀ (m : ℕ), m ≤ r → ∀ P ∈ TorV hD (r - m), ∀ c ∈ OmX r,
        La hD v₀ (wCell k r (Fin.last r) c * g₀) (qminor (EA hD) (colsVm k r m) (colsVm k r m) w * P) =
          kvC r w m (fun c' => La hD v₀ (wCell k r (Fin.last r) c' * g₀) P) c := by
    have hLv : LeftEq k r z 0 D (v₀ : Mx k r → E) := by rw [hv]; exact leftEq_cut z hN hLf
    intro m
    induction m using Nat.strong_induction_on with
    | _ m ih =>
    intro hm P hP c hc
    rcases m with _ | _ | m
    · rw [MC.qminor_zero, one_mul]
      rfl
    · rw [MC.qminor_one]
      have hx0 : colsVm k r 1 0 = esI k r ⟨r - 1, by omega⟩ := by
        ext
        simp only [colsVm, esI, Fin.val_zero]
        omega
      rw [hx0, la_torus hD hTC v₀ g₀ hg₀ hcell ⟨r - 1, by omega⟩ w P c hc, kvC_one w _ hm c]
    · have hm2 : m + 2 ≤ r := hm
      have hP1 : P ∈ TorV hD (r - (m + 1)) := TorV_mono hD (by omega) hP
      have hP0 : P ∈ TorV hD (r - m) := TorV_mono hD (by omega) hP
      set ρ : ℂ := star (c ⟨r - m - 1, by omega⟩) / star (c ⟨r - m - 2, by omega⟩) with hρ
      set_option synthInstance.maxHeartbeats 200000 in
      set LaP : SA E hD →ₗ[ℂ] E := (La hD v₀ (wCell k r (Fin.last r) c * g₀)).comp (LinearMap.mulRight ℂ P) with hLaP
      have hLaP_apply : ∀ x, LaP x = La hD v₀ (wCell k r (Fin.last r) c * g₀) (x * P) := fun x => rfl
      have hnot : ∀ a : Fin r, r - m - 2 ≤ a.val → ∀ l' : Fin r, l'.val < r - (m + 2) → esI k r a ≠ esI k r l' :=
        fun a ha l' hl' => esI_ne (by omega)
      have hR0 : ∀ (x : SA E hD) (a : Fin r), r - m - 1 < a.val →
          LaP (x * EA hD (esI k r a) (esI k r ⟨r - m - 2, by omega⟩)) = 0 := by
        intro x a ha
        rw [hLaP_apply, mul_assoc, (comm_TorV hD (r - (m + 2)) _ _ (hnot a (by omega))
          (hnot ⟨r - m - 2, by omega⟩ le_rfl) P hP).eq, ← mul_assoc, La_apply, Subalgebra.coe_mul, Module.End.mul_apply]
        conv_lhs => rw [hv]
        rw [root_action_on_truncated_vector hD z' hz' hRR hf hRf a ⟨r - m - 2, by omega⟩ (by simp only; omega), if_neg (by simp only; omega),
          zero_smul, map_zero]
        rfl
      have hR1 : ∀ x : SA E hD,
          LaP (x * EA hD (esI k r ⟨r - m - 1, by omega⟩) (esI k r ⟨r - m - 2, by omega⟩)) = LaP x := by
        intro x
        rw [hLaP_apply, hLaP_apply, mul_assoc, (comm_TorV hD (r - (m + 2)) _ _ (hnot ⟨r - m - 1, by omega⟩ (by simp only; omega))
          (hnot ⟨r - m - 2, by omega⟩ le_rfl) P hP).eq, ← mul_assoc, La_apply, La_apply, Subalgebra.coe_mul,
          Module.End.mul_apply]
        conv_lhs => rw [hv]
        rw [root_action_on_truncated_vector hD z' hz' hRR hf hRf ⟨r - m - 1, by omega⟩ ⟨r - m - 2, by omega⟩ (by simp only; omega),
          if_pos (by simp only; omega), one_smul, ← hv]
      have hL : ∀ (x : SA E hD) (b : Fin r), r - m - 2 < b.val →
          LaP (EA hD (esI k r ⟨r - m - 2, by omega⟩) (esI k r b) * x) =
            (if b.val = r - m - 1 then ρ else 0) • LaP x := by
        intro x b hb
        rw [hLaP_apply, hLaP_apply, mul_assoc, La_apply, La_apply, Subalgebra.coe_mul, Module.End.mul_apply, EA_val,
          ev_E hD _ _ _ (hcell c hc), posL_cI, posL_cI]
        have hsm := (((x * P : SA E hD) : Module.End ℂ (VS k r 0 D E)) v₀).2.1
        have hle := leftEq_SA hD z hN (x * P) v₀ hLv
        rw [hLR E k r z D _ hz hD hN hsm hle c hc g₀ hg₀ (hcell c hc).2 b ⟨r - m - 2, by omega⟩ (by simp only; omega)]
        congr 1
        by_cases hbm : b.val = r - m - 1
        · have hb' : b = ⟨r - m - 1, by omega⟩ := Fin.ext hbm
          rw [if_pos (by simp only; omega), if_pos hbm, hρ, congrArg c hb']
        · rw [if_neg (by simp only; omega), if_neg hbm]
      have hX := hCh (SA E hD) E k r (EA (E := E) hD) LaP ρ (EA_gl (E := E) hD) m hm2 w hR0 hR1 hL
      set T := Tm (EA (E := E) hD) (w - ((m + 1 : ℕ) : ℂ)) (esI k r ⟨r - m - 2, by omega⟩)
        (esI k r ⟨r - m - 2, by omega⟩) with hT
      have hTmem : T ∈ TorV hD (r - (m + 1)) := by
        rw [hT]
        unfold Tm
        rw [if_pos rfl]
        exact Subalgebra.add_mem _ (Subalgebra.algebraMap_mem _ _) (EAs_mem_TorV hD ⟨r - m - 2, by omega⟩ (by simp only; omega))
      have hTP : T * P ∈ TorV hD (r - (m + 1)) := Subalgebra.mul_mem _ hTmem hP1
      have ih1 := ih (m + 1) (by omega) (by omega) (T * P) hTP c hc
      have ih0 := ih m (by omega) (by omega) P hP0 c hc
      rw [hLaP_apply, hLaP_apply, hLaP_apply, mul_assoc] at hX
      rw [hX, ih1, ih0, kvC_two]
      have hloc := kvC_loc w (m + 1) (fun c' => La hD v₀ (wCell k r (Fin.last r) c' * g₀) (T * P))
        (fun c' => (w - ((m + 1 : ℕ) : ℂ)) • La hD v₀ (wCell k r (Fin.last r) c' * g₀) P -
          pbN r (r - (m + 1) - 1) (fun c'' => La hD v₀ (wCell k r (Fin.last r) c'' * g₀) P) c')
        (fun c' hc' => by
          rw [hT, la_torus hD hTC v₀ g₀ hg₀ hcell ⟨r - m - 2, by omega⟩ _ P c' hc']
          unfold pbN
          rw [dite_eq_left (by omega)]
          have e : (⟨r - (m + 1) - 1, by omega⟩ : Fin r) = ⟨r - m - 2, by omega⟩ := Fin.ext (by simp only; omega)
          rw [e]) hc
      rw [hloc]
      congr 1
      unfold cbN cbiN
      rw [dite_eq_left (by omega), dite_eq_left (by omega)]
      have e1 : (⟨r - (m + 1), by omega⟩ : Fin r) = ⟨r - m - 1, by omega⟩ := Fin.ext (by simp only; omega)
      have e2 : (⟨r - (m + 1) - 1, by omega⟩ : Fin r) = ⟨r - m - 2, by omega⟩ := Fin.ext (by simp only; omega)
      rw [e1, e2]
      simp only [cbOp, cbiOp, hρ, div_eq_mul_inv, mul_smul]
  have h1N : (1 : Mx P.k P.r) ∈ Nlev P.k P.r 0 :=
    ⟨(Formalism.QuantumDeterminants.unipotent_subgroup_holds P.k P.r).1, by simp [Glev, UH]⟩
  have hN : ∀ g ∈ Glev P.k P.r 0 ∩ D, ∀ n ∈ Nlev P.k P.r 0, n * g ∈ D := by
    intro g hg n hn
    have hDom := Formalism.FourierDecayAlt.P.JCx2.rma_isDom_omPlus (k := P.k) (r := P.r) Bs.z_mem Bs.z'_mem
    have := hDom.2 g hg n ⟨1, Formalism.FourierDecayAlt.P.Qx8.uw_one Bs.z, n, hn, (one_mul n).symm⟩ 1
      ⟨1, Formalism.FourierDecayAlt.P.Qx8.uw_one Bs.z', 1, h1N, (one_mul 1).symm⟩
    rwa [Matrix.mul_one] at this
  set v₀ : VS P.k P.r 0 D (Wq →L[ℂ] Wp) := ⟨cut P.k P.r 0 D J, cut_mem hD hf⟩ with hv₀
  have hcellB : ∀ c ∈ OmX P.r, wCell P.k P.r (Fin.last P.r) c * g ∈ C6.bigPos Bs := fun c hc =>
    (Formalism.FourierDecayAlt.P.big_cell_values P.k P.r Wp Wq Bs (c, g) ⟨hc, hx.2.1, hx.2.2⟩).1
  have hcell : ∀ c ∈ OmX P.r, wCell P.k P.r (Fin.last P.r) c * g ∈ Glev P.k P.r 0 ∩ D := by
    intro c hc
    have h := hcellB c hc
    exact ⟨Formalism.FourierDecayAlt.P.OrbitalIntegralIdentities.glev0 h.1, fun l _ => h.2.2 l (by simp), h.2.1⟩
  have hcl := claimV mirror_right_rule_holds mirror_left_rule_cell_holds mirror_torus_cell_holds mirror_chain_expansion_holds hD v₀ g
    (kvTop P.k P.r y) Bs.z Bs.z' Bs.z_mem Bs.z'_mem hN hf hLf hRf rfl hg hcell P.r le_rfl 1 (Subalgebra.one_mem _) c hc
  rw [mul_one] at hcl
  have eR : kvC P.r (kvTop P.k P.r y) P.r (fun c' => J (wCell P.k P.r (Fin.last P.r) c' * g)) c =
      kvC P.r (kvTop P.k P.r y) P.r (fun c' => La hD v₀ (wCell P.k P.r (Fin.last P.r) c' * g) 1) c :=
    kvC_loc _ _ _ _ (fun c' hc' => (cut_of_mem _ (hcell c' hc')).symm) hc
  rw [eR, ← hcl, La_apply]
  have hγ := hcell c hc
  have e1 : ((qminor (EA (E := Wq →L[ℂ] Wp) hD) (colsVm P.k P.r P.r) (colsVm P.k P.r P.r) (kvTop P.k P.r y) :
      SA (Wq →L[ℂ] Wp) hD) : Module.End ℂ (VS P.k P.r 0 D (Wq →L[ℂ] Wp))) =
      qminor (Eh (E := Wq →L[ℂ] Wp) (i := 0) hD) (cI ∘ colsVm P.k P.r P.r) (cI ∘ colsVm P.k P.r P.r)
        (kvTop P.k P.r y) := by
    have := map_qminor (SA (Wq →L[ℂ] Wp) hD).val (EA hD) (colsVm P.k P.r P.r) (colsVm P.k P.r P.r) (kvTop P.k P.r y)
    rw [Subalgebra.coe_val] at this
    rw [this]
    exact qminor_reindex (Eh hD) cI cI_inj _ _ _
  rw [e1, rep_qminor hD _ _ _ v₀ _ hγ]
  have hpos : posL P.k P.r 0 ∘ (cI ∘ colsVm P.k P.r P.r) = colsVm P.k P.r P.r := funext fun l => posL_cI _
  have hloc := (good_qminor (E := Wq →L[ℂ] Wp) hD (cI ∘ colsVm P.k P.r P.r) (cI ∘ colsVm P.k P.r P.r)
    (kvTop P.k P.r y)).loc (cut P.k P.r 0 D J) J (fun x' hx' => cut_of_mem _ hx') _ hγ
  rw [hpos] at hloc
  rw [hpos]
  exact hloc.symm

end Formalism.FourierDecayAlt.P.CutMP.TVG

namespace Formalism.FourierDecayAlt.P.CutMP

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace


open scoped ContDiff in
theorem rdsag_todaV {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (P : M.Par)
    (Bs : B.RealPlaceData P.k P.r Wp Wq) (y : ℂ) (J : B.Mat P.k P.r → (Wq →L[ℂ] Wp))
    (hJ : J ∈ Q.FFl P.k P.r Bs.z Bs.z' Bs.π Bs.π' 0 (Gauge.OmB Bs)) (c : Fin P.r → ℂ) (hc : c ∈ OmX P.r)
    (g : Q.Mx P.k P.r) (hg : g ∈ Q.Glev P.k P.r (Fin.last P.r))
    (hcg : Q.wCell P.k P.r (Fin.last P.r) c * g ∈ Gauge.OmB Bs) :
    Q.resG P.k P.r (Fin.last P.r) (capAv P.k P.r y J) c g =
      dMul (drbF P.r) (Q.crd (Q.cmp (vABm P.r y P.r) 0) (Q.resG P.k P.r (Fin.last P.r) J)) c g := by
  have e1 : capAv P.k P.r y J (Q.wCell P.k P.r (Fin.last P.r) c * g) =
      drbF P.r c • kvM P.k P.r P.r (kvTop P.k P.r y) J (Q.wCell P.k P.r (Fin.last P.r) c * g) := by
    obtain ⟨hGV, hCk⟩ := capa_J_ck P Bs hJ hc hg hcg ((P.r : ℕ) : ℕ∞)
    exact TVCoefPf.coef_gen hc hg hGV (hCk _ (Set.mem_singleton _)) y
  have e2 := TVG.rdsag_tvGrp P Bs y J hJ c hc g hg hcg
  have hD : Q.IsDom P.k P.r Bs.z Bs.z' 0 (Gauge.OmB Bs) := isDom_omP Bs.z_mem Bs.z'_mem
  have hfam := (Formalism.FourierDecayAlt.P.restriction_good_family Wp Wq P.k P.r Bs.z Bs.z' Bs.π Bs.π' (Gauge.OmB Bs) Bs.z_mem Bs.z'_mem hD J hJ
    (Fin.last P.r)).1
  obtain ⟨U, F, hUo, hx0, hF, hFeq⟩ := hfam (c, g) ⟨hc, hcg⟩ hg
  have hemb : ContDiff ℝ ∞ (fun c' : Fin P.r → ℂ => (c', g)) := contDiff_id.prodMk contDiff_const
  set U' : Set (Fin P.r → ℂ) := {c' | (c', g) ∈ U} ∩ OmX P.r with hU'
  have hU'o : IsOpen U' := (hUo.preimage hemb.continuous).inter (Formalism.FourierDecayAlt.P.Qx5.isOpen_OmX P.r)
  have hgauge : ∀ c' : Fin P.r → ℂ, gaugeF P.k P.r c' • J (Q.wCell P.k P.r (Fin.last P.r) c' * g) =
      Q.resG P.k P.r (Fin.last P.r) J c' g := by
    intro c'
    simp only [gaugeF, Q.resG, smul_eq_mul, mul_one]
  have hsm : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun c' => gaugeF P.k P.r c' • J (Q.wCell P.k P.r (Fin.last P.r) c' * g)) U' := by
    refine ((hF.comp hemb.contDiffOn (fun c' (hc' : c' ∈ U') => hc'.1))).congr (fun c' hc' => ?_)
    rw [hgauge c']
    exact hFeq (c', g) hc'.1 hg
  have e3 := toda_coordinate_holds P.k P.r (Wq →L[ℂ] Wp) y (fun c' => J (Q.wCell P.k P.r (Fin.last P.r) c' * g)) U' c hU'o
    (fun _ h => h.2) ⟨hx0, hc⟩ hsm
  have hfun : (fun c' => gaugeF P.k P.r c' • J (Q.wCell P.k P.r (Fin.last P.r) c' * g)) =
      fun c' => Q.resG P.k P.r (Fin.last P.r) J c' g := funext hgauge
  rw [hfun] at e3
  simp only [dMul, Q.crd, Q.cmp, if_true]
  rw [← e3]
  have hres : Q.resG P.k P.r (Fin.last P.r) (capAv P.k P.r y J) c g =
      gaugeF P.k P.r c • capAv P.k P.r y J (Q.wCell P.k P.r (Fin.last P.r) c * g) := by
    simp only [gaugeF, Q.resG, smul_eq_mul, mul_one]
  rw [hres, e1, e2, smul_comm]

end Formalism.FourierDecayAlt.P.CutMP

namespace Formalism.FourierDecayAlt.P.CutSE

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.Wd Formalism.FourierDecayAlt.P5

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

theorem spectral_group_action : RDSAGrp := by
  intro Wp Wq _ _ _ _ _ _ P D hPl y
  obtain ⟨Θ, Θv, hP, hPv, hO, hOv, hA, hAv⟩ := CutMP.capelli_representation_holds P.k P.r Wp Wq y
  refine ⟨Θ, Θv, ⟨_, _, hP⟩, ⟨_, _, hPv⟩, (CutMP.rdsag_capInv P D y Θ hO.ge).1 hA,
    (CutMP.rdsag_capInv P D y Θv hOv.ge).2 hAv, fun J hJ x hx => ?_⟩
  have hJB : J ∈ Q.FFl P.k P.r D.z D.z' D.π D.π' 0 (CutMP.Gauge.OmB D) := by
    rw [CutMP.JDAToda.omB_eq, ← ffl_om_eq]; exact hJ
  have hcell : Q.wCell P.k P.r (Fin.last P.r) x.1 * x.2 ∈ CutMP.Gauge.OmB D := by
    rw [CutMP.JDAToda.omB_eq]
    have h := (Formalism.FourierDecayAlt.P.big_cell_values P.k P.r Wp Wq D x hx).1
    exact ⟨fun l _ => h.2.2 l (by simp), h.2.1⟩
  obtain ⟨hc, hg, -⟩ := hx
  constructor
  · obtain ⟨hGV, hCk⟩ := CutMP.capa_J_ck P D hJB hc hg hcell (B.opOrder Θ)
    rw [← CutMP.rdsag_toda P D y J hJB x.1 hc x.2 hg hcell]
    simp only [Q.resG]
    rw [hA J _ hGV hCk]
  · obtain ⟨hGV, hCk⟩ := CutMP.capa_J_ck P D hJB hc hg hcell (B.opOrder Θv)
    rw [← CutMP.rdsag_todaV P D y J hJB x.1 hc x.2 hg hcell]
    simp only [Q.resG]
    rw [hAv J _ hGV hCk]

end Formalism.FourierDecayAlt.P.CutSE
