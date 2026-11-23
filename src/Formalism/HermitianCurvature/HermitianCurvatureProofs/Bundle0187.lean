module

public import Formalism.HermitianCurvature.StatementHeads
public import Formalism.HermitianCurvature.RealInputsClosedAdmissibleSettings
public import Formalism.HermitianCurvature.StatementTL
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0092
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.OpApplyContinuousOn
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.LiftClosedUnderOperations
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0173
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0112
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0091
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0179
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0113
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0101

@[expose] public section

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.TopFirstOfParts
section
open MeasureTheory Matrix Filter Topology
open scoped ComplexConjugate

noncomputable section

namespace Formalism.FourierDecayAlt.P.PBN

open Formalism.FourierDecayAlt Formalism.REAL Formalism.QuantumDeterminants

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

def DegTopOfParts : Prop := TL.WordStep → RadAATop → PolyTop → KB.DensC → KB.DegTop

section lin

variable {k r : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq]

theorem jf_congr_pos (Bs : B.RealPlaceData k r Wp Wq) {F F₂ : B.Mat k r → (Wq →L[ℂ] Wp)}
    (h : ∀ g ∈ C6.domL Bs ∅, F g = F₂ g) {g : B.Mat k r} (hg : g ∈ C6.domL Bs ∅) : B.JF Bs F g = B.JF Bs F₂ g := by
  show ∫ p, JF.xiP Bs p • B.rho Bs p F g ∂Bs.μSS = ∫ p, JF.xiP Bs p • B.rho Bs p F₂ g ∂Bs.μSS
  refine integral_congr_ae ?_
  filter_upwards [Formalism.FourierDecayAlt.P.B5.ae_inSS Bs] with p hp
  have hs : B.sgs p g ∈ C6.domL Bs ∅ :=
    ⟨Formalism.FourierDecayAlt.P.B7.sgs_mem Bs hp hg.1, by rw [Formalism.FourierDecayAlt.P.JCx1.needs.gf_sgs Bs hp]; exact hg.2.1, by simp⟩
  simp only [B.rho]
  rw [h _ hs]

theorem cpt_zero' (Bs : B.RealPlaceData k r Wp Wq) : KB.CptCoef Bs (fun _ => (0 : Wq →L[ℂ] Wp)) :=
  ⟨Formalism.FourierDecayAlt.P.BetaSesquilinearity.CkOn_zero, ⟨0, fun _ _ h => (h rfl).elim⟩, ⟨1, one_pos, fun _ _ h => (h rfl).elim⟩⟩

theorem cpt_add_smul' (Bs : B.RealPlaceData k r Wp Wq) {F₁ F₂ : B.Mat k r → (Wq →L[ℂ] Wp)} (c : ℂ)
    (h₁ : KB.CptCoef Bs F₁) (h₂ : KB.CptCoef Bs F₂) : KB.CptCoef Bs (fun g => F₁ g + c • F₂ g) := by
  obtain ⟨s₁, ⟨R₁, hR₁⟩, ⟨ε₁, hε₁, hG₁⟩⟩ := h₁
  obtain ⟨s₂, ⟨R₂, hR₂⟩, ⟨ε₂, hε₂, hG₂⟩⟩ := h₂
  refine ⟨Formalism.FourierDecayAlt.P.BetaSesquilinearity.CkOn_add s₁ (Formalism.FourierDecayAlt.P.BetaSesquilinearity.CkOn_smul c s₂), ⟨max R₁ R₂, fun g hg hne => ?_⟩,
    ⟨min ε₁ ε₂, lt_min hε₁ hε₂, fun g hg hne => ?_⟩⟩
  · by_cases h0 : F₁ g = 0
    · have : F₂ g ≠ 0 := fun h2 => hne (by simp [h0, h2])
      exact (hR₂ g hg this).trans (le_max_right _ _)
    · exact (hR₁ g hg h0).trans (le_max_left _ _)
  · by_cases h0 : F₁ g = 0
    · have : F₂ g ≠ 0 := fun h2 => hne (by simp [h0, h2])
      exact (min_le_right _ _).trans (hG₂ g hg this)
    · exact (min_le_left _ _).trans (hG₁ g hg h0)

theorem cpt_add (Bs : B.RealPlaceData k r Wp Wq) {F₁ F₂ : B.Mat k r → (Wq →L[ℂ] Wp)}
    (h₁ : KB.CptCoef Bs F₁) (h₂ : KB.CptCoef Bs F₂) : KB.CptCoef Bs (fun g => F₁ g + F₂ g) := by
  have := cpt_add_smul' Bs (1 : ℂ) h₁ h₂
  simpa [one_smul] using this

theorem cpt_sub (Bs : B.RealPlaceData k r Wp Wq) {F₁ F₂ : B.Mat k r → (Wq →L[ℂ] Wp)}
    (h₁ : KB.CptCoef Bs F₁) (h₂ : KB.CptCoef Bs F₂) : KB.CptCoef Bs (fun g => F₁ g - F₂ g) := by
  have := cpt_add_smul' Bs (-1 : ℂ) h₁ h₂
  simpa [neg_one_smul, ← sub_eq_add_neg] using this

theorem cpt_smul (Bs : B.RealPlaceData k r Wp Wq) {F : B.Mat k r → (Wq →L[ℂ] Wp)} (c : ℂ)
    (h : KB.CptCoef Bs F) : KB.CptCoef Bs (fun g => c • F g) := by
  have := cpt_add_smul' Bs c (cpt_zero' Bs) h
  simpa using this

theorem gN_bound (Bs : B.RealPlaceData k r Wp Wq) {F : B.Mat k r → (Wq →L[ℂ] Wp)} (hF : KB.CptCoef Bs F) (A : ℝ)
    (hA : 0 ≤ A) : ∃ c : ℝ, 0 ≤ c ∧ ∀ g ∈ B.GV k r, ‖F g‖ ≤ c * B.gN g ^ (-A) := by
  obtain ⟨c, hc⟩ := Formalism.FourierDecayAlt.P.StabilizerDisintegration.CV.cpt_bound Bs F hF A hA
  refine ⟨max c 0, le_max_right _ _, fun g hg => ?_⟩
  have hg1 : 1 ≤ B.gN g := Formalism.FourierDecayAlt.P.BetaSesquilinearity.gN_ge_one hg
  have hpos : 0 < B.gN g ^ A := Real.rpow_pos_of_pos (by linarith) A
  rw [Real.rpow_neg (by linarith), ← div_eq_mul_inv, le_div_iff₀ hpos]
  calc ‖F g‖ * B.gN g ^ A = B.gN g ^ A * ‖F g‖ := mul_comm _ _
    _ ≤ c := hc g hg
    _ ≤ max c 0 := le_max_left _ _

theorem vecV_sub (Bs : B.RealPlaceData k r Wp Wq) (ν' : Fin (2 * r + k + 1) → ℂ) (m₀ : B.Mat k r) (q : C.LPt)
    {H₁ H₂ : B.Mat k r → (Wq →L[ℂ] Wp)} (h₁ : KB.CptCoef Bs H₁) (h₂ : KB.CptCoef Bs H₂) :
    D.vecV Bs ν' m₀ (fun g => H₁ g - H₂ g) q = D.vecV Bs ν' m₀ H₁ q - D.vecV Bs ν' m₀ H₂ q := by
  obtain ⟨c₃, hc₃⟩ := Formalism.FourierDecayAlt.P.PBE.orbJ_dom
  set A : ℝ := max 0 (c₃ * ((r : ℝ) + 1) ^ 2 * ((r : ℝ) * ((2 * r + k + 1 : ℕ) : ℝ) + 1)) with hAdef
  obtain ⟨c₁, hc₁0, hb₁⟩ := gN_bound Bs h₁ A (le_max_left _ _)
  obtain ⟨c₂, hc₂0, hb₂⟩ := gN_bound Bs h₂ A (le_max_left _ _)
  have h₁₂ := cpt_sub Bs h₁ h₂
  unfold D.vecV
  by_cases h : D.IsLocPt q (r + 1) ∧ 0 < D.ptG (Tz k r Bs.z * Tz k r Bs.z') r q
  · simp only [dif_pos h]
    by_cases h' : ∃ γ ∈ B.GV k r, Zhat k r Bs.z Bs.z' γ = D.ptMatN q (r + 1) ∧ D.IsDFrame Bs ν' m₀ γ
    · simp only [dif_pos h']
      have hγ := h'.choose_spec.1
      have hZ := h'.choose_spec.2.1
      have hGq := Formalism.FourierDecayAlt.P.ptG_spec k r Bs.z Bs.z' q h'.choose h.1 hZ
      have hpos : 0 < Gf k r Bs.z Bs.z' h'.choose := hGq ▸ h.2
      obtain ⟨hmono, hd⟩ := Formalism.FourierDecayAlt.P.Dx2.VV.ptMatN_monoP' q (r + 1) h.1.2 h.1.1
      have hrel := Formalism.FourierDecayAlt.P.relevant_points_holds k r Wp Wq Bs q h'.choose h.1 hγ hZ
      have horb : ∀ p, Bs.inSS p → B.sgs p h'.choose ∈ B.GPos Bs := fun p hp =>
        ⟨Formalism.FourierDecayAlt.P.B7.sgs_mem Bs hp hγ, by rw [Formalism.FourierDecayAlt.P.JCx1.needs.gf_sgs Bs hp]; exact hpos⟩
      have hZm := hZ.trans hmono
      obtain ⟨θ, maj, hθ, hmaj, hdom⟩ := hc₃ k r Wp Wq Bs h'.choose _ _ A hγ hd hZm hpos (le_max_right _ _)
      have hG : Formalism.FourierDecayAlt.P.Dx2.Rad.Good Bs h'.choose _ _ :=
        ⟨Formalism.FourierDecayAlt.P.Dx2.Rad.exists_rho Bs hγ hpos hd hZm, Formalism.FourierDecayAlt.P.Dx2.Rad.u_inj Bs hγ hpos hd hZm,
          fun ρ hρ => Formalism.FourierDecayAlt.P.Dx2.Rad.u_lstg Bs hγ hpos hd hZm hρ⟩
      have hR := Formalism.FourierDecayAlt.P.Dx2.Rad.haar_good Bs hγ hd hG
      have hEq : ∀ (G : B.Mat k r → (Wq →L[ℂ] Wp)) (cF : ℝ), 0 ≤ cF → KB.CptCoef Bs G →
          (∀ g ∈ B.GV k r, ‖G g‖ ≤ cF * B.gN g ^ (-A)) →
          D.orbJ Bs h'.choose (D.muR Bs h'.choose (h.1.2 ▸ D.ptPerm q)) G =
              ∫ p, θ p • D.orbIntegrand Bs h'.choose G p ∂Bs.μSS ∧
            Integrable (fun p => θ p • D.orbIntegrand Bs h'.choose G p) Bs.μSS := by
        intro G cF hcF hGc hGb
        have hm : AEStronglyMeasurable (D.orbIntegrand Bs h'.choose G) Bs.μSS :=
          Formalism.FourierDecayAlt.P.PBE.integrand_aesm' Bs horb ((Formalism.FourierDecayAlt.P.B5.ckOn_continuousOn hGc.1).mono fun g hg => hg.1)
        have hi : Integrable (fun p => θ p • D.orbIntegrand Bs h'.choose G p) Bs.μSS :=
          Integrable.mono' (hmaj.const_mul cF) (hθ.1.aestronglyMeasurable.smul hm)
            (hdom G cF hcF fun p hp => hGb _ (Formalism.FourierDecayAlt.P.B7.sgs_mem Bs hp hγ))
        refine ⟨?_, hi⟩
        have hex : ∃ θ', D.IsNormCut Bs h'.choose (D.muR Bs h'.choose (h.1.2 ▸ D.ptPerm q)) θ' ∧
            Integrable (fun p => θ' p • D.orbIntegrand Bs h'.choose G p) Bs.μSS := ⟨θ, hθ, hi⟩
        unfold D.orbJ
        rw [dif_pos hex]
        exact Formalism.FourierDecayAlt.P.orbital_integral_indep_choice k r Wp Wq Bs h'.choose _ hrel hR G _ θ hex.choose_spec.1 hθ
          hex.choose_spec.2 hi
      obtain ⟨e1, i1⟩ := hEq H₁ c₁ hc₁0 h₁ hb₁
      obtain ⟨e2, i2⟩ := hEq H₂ c₂ hc₂0 h₂ hb₂
      obtain ⟨e12, -⟩ := hEq (fun g => H₁ g - H₂ g) (c₁ + c₂) (add_nonneg hc₁0 hc₂0) h₁₂ (fun g hg =>
        (norm_sub_le _ _).trans (by rw [add_mul]; exact add_le_add (hb₁ g hg) (hb₂ g hg)))
      rw [e12, e1, e2, ← integral_sub i1 i2]
      congr 1
      funext p
      simp only [D.orbIntegrand, B.rho, ContinuousLinearMap.sub_comp,
        ContinuousLinearMap.comp_sub, smul_sub]
    · simp only [dif_neg h', sub_zero]
  · simp only [dif_neg h, sub_zero]

end lin

section rad

variable {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq]

theorem cell_dom {P : M.Par} (Bs : B.RealPlaceData P.k P.r Wp Wq) {x : (Fin P.r → ℂ) × Q.Mx P.k P.r}
    (hx : x ∈ Q.DomR P.k P.r Bs.z Bs.z') : Q.wCell P.k P.r (Fin.last P.r) x.1 * x.2 ∈ C6.domL Bs ∅ := by
  have h := (Formalism.FourierDecayAlt.P.big_cell_values P.k P.r Wp Wq Bs x hx).1
  exact ⟨h.1, h.2.1, by simp⟩

theorem isRadOf_congr {P : M.Par} (Bs : B.RealPlaceData P.k P.r Wp Wq) {Φ : Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π'}
    {F F₂ : B.Mat P.k P.r → (Wq →L[ℂ] Wp)} (hΦ : Top.IsRadOf P Bs Φ F) (h : ∀ g ∈ C6.domL Bs ∅, F g = F₂ g) :
    Top.IsRadOf P Bs Φ F₂ := by
  intro x hx
  rw [hΦ x hx]
  simp only [Q.resG]
  rw [jf_congr_pos Bs h (cell_dom Bs hx)]

theorem isRadOf_sub {P : M.Par} (Bs : B.RealPlaceData P.k P.r Wp Wq) {Φ₁ Φ₂ : Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π'}
    {F₁ F₂ : B.Mat P.k P.r → (Wq →L[ℂ] Wp)} (h₁ : KB.CptCoef Bs F₁) (h₂ : KB.CptCoef Bs F₂)
    (hΦ₁ : Top.IsRadOf P Bs Φ₁ F₁) (hΦ₂ : Top.IsRadOf P Bs Φ₂ F₂) :
    Top.IsRadOf P Bs (Φ₁ - Φ₂) (fun g => F₁ g - F₂ g) := by
  intro x hx
  have h₂' := cpt_smul Bs (-1 : ℂ) h₂
  obtain ⟨ε₁, hε₁, hn₁⟩ := Formalism.FourierDecayAlt.P.TLB.nice_of_cpt h₁
  obtain ⟨ε₂, hε₂, hn₂⟩ := Formalism.FourierDecayAlt.P.TLB.nice_of_cpt h₂'
  have e : (fun g => F₁ g - F₂ g) = fun g => F₁ g + (-1 : ℂ) • F₂ g := by
    funext g; rw [neg_one_smul, sub_eq_add_neg]
  rw [e]
  simp only [Submodule.coe_sub, Pi.sub_apply]
  rw [hΦ₁ x hx, hΦ₂ x hx]
  simp only [Q.resG]
  rw [Formalism.FourierDecayAlt.P.JCx2.bc_JF_add (Formalism.FourierDecayAlt.P.TLB.nice_mono hn₁ (min_le_left ε₁ ε₂))
    (Formalism.FourierDecayAlt.P.TLB.nice_mono hn₂ (min_le_right ε₁ ε₂)) (Formalism.FourierDecayAlt.P.TLB.wCell_om Bs hx),
    Formalism.FourierDecayAlt.P.JCx2.bc_JF_smul, smul_add, neg_one_smul, smul_neg, sub_eq_add_neg]

theorem radExists {P : M.Par} (p : KB.Pl P Wp Wq) {F : B.Mat P.k P.r → (Wq →L[ℂ] Wp)}
    (hF : KB.CptCoef p.T.base F) : ∃ Φ, Top.IsRadOf P p.T.base Φ F := by
  obtain ⟨ε, hε, hn⟩ := Formalism.FourierDecayAlt.P.TLB.nice_of_cpt hF
  obtain ⟨Φ, hΦ⟩ := Formalism.FourierDecayAlt.P5.radJFExists Wp Wq P p.T.base.z p.T.base.z' p.T.base.π p.T.base.π' p.T.base F
    p.hP rfl rfl rfl rfl ⟨hn.2.1, ε, hε, hn.2.2⟩
  exact ⟨Φ, hΦ⟩

theorem vecV_eq_of_rad (hDC : KB.DensC) {P : M.Par} (p : KB.Pl P Wp Wq) {F₁ F₂ : B.Mat P.k P.r → (Wq →L[ℂ] Wp)}
    (h₁ : KB.CptCoef p.T.base F₁) (h₂ : KB.CptCoef p.T.base F₂) {Φ : Q.RadSp P.k P.r p.T.base.z p.T.base.z' p.T.base.π p.T.base.π'}
    (hΦ₁ : Top.IsRadOf P p.T.base Φ F₁) (hΦ₂ : Top.IsRadOf P p.T.base Φ F₂) (a : C.LPt) : p.V F₁ a = p.V F₂ a := by
  have h0 := isRadOf_sub p.T.base h₁ h₂ hΦ₁ hΦ₂
  rw [sub_self] at h0
  have hv := hDC Wp Wq P p _ (cpt_sub p.T.base h₁ h₂) h0 a
  have e := vecV_sub p.T.base p.ν' p.m₀ a h₁ h₂
  unfold KB.Pl.V at hv ⊢
  rw [e] at hv
  exact sub_eq_zero.1 hv

end rad

end Formalism.FourierDecayAlt.P.PBN
end
end

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.VecVAppendSingletonEqVecVSliceAt
section
open Matrix MeasureTheory Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.U

noncomputable section

namespace Formalism.FourierDecayAlt.P.PBM

section helpers

variable {k : ℕ}

theorem cast_cancel (a : ℕ) (h1 : a = 0) (h2 : 0 = a) (γ : B.Mat k 0) : h1 ▸ D.castM h2 γ = γ := by
  subst h1; exact Dx2.MN.castM_rfl γ

theorem phiFun_tr {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] (R j ρ' : ℕ) (hj : j = R) (hρ : ρ' = 0)
    (σ : Equiv.Perm (Fin j)) (d : Fin j → ℂ) (z z' : Fin (2 * R + k + 1) → ℂ) (F : B.Mat k R → E)
    (e1 : R = j + 0 + ρ') (e2 : j + 0 + ρ' = R) (γ : B.Mat k ρ') :
    U.PhiFun (s := 0) k ρ' σ d (D.castV e1 z) (D.castV e1 z') (D.castF e2 F) (fun a => a.elim0) γ =
      U.PhiFun (s := 0) k 0 (hj ▸ σ) (hj ▸ d) z z' F (fun a => a.elim0) (hρ ▸ γ) := by
  subst hj; subst hρ
  have h1 : D.castV e1 z = z := Dx2.Tower.castV_rfl z
  have h2 : D.castV e1 z' = z' := Dx2.Tower.castV_rfl z'
  have h3 : D.castF e2 F = F := by funext g; exact congrArg F (Dx2.MN.castM_rfl g)
  rw [h1, h2, h3]

theorem ptMatN_one (ζ : ℂ) : D.ptMatN [(1, ζ)] (0 + 1) = Matrix.of fun _ _ => ζ := by
  ext a b
  have ha : a.val = 0 := by have := a.isLt; omega
  have hb : b.val = 0 := by have := b.isLt; omega
  simp [D.ptMatN, D.ptEntry, ha, hb]

theorem ptMatN_append_head (h : C.LPt) (ζ : ℂ) (R : ℕ) (hR : D.ptSize h = R) :
    D.ptMatN (h ++ [(1, ζ)]) R = D.ptMatN h R := by
  ext a b
  simp only [D.ptMatN, ptEntry_append, hR, a.isLt, b.isLt, and_self, if_true]

theorem isLocPt_app (h : C.LPt) (R : ℕ) (hh : D.IsLocPt h R) (ζ : ℂ) (hζ : ζ ≠ 0) :
    D.IsLocPt (h ++ [(1, ζ)]) (R + 1) := by
  refine ⟨fun b hb => ?_, CompactCoefficientAppend.ptSize_app h R hh ζ⟩
  rcases List.mem_append.1 hb with hb | hb
  · exact hh.1 b hb
  · simp at hb; subst hb; exact ⟨le_refl _, hζ⟩

theorem Tz_lift (R : ℕ) (v : Fin (2 * 0 + k + 1) → ℂ) : Tz k (R + 0) (liftVec k R 0 v) = Tz k 0 v := by
  unfold Tz; rw [herm_lift]

end helpers

section master

variable {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq]

theorem lev_inv {k R : ℕ} (y : B.Mat k 0) (hy : IsUnit y.det) : ιLev k R 0 y⁻¹ = (ιLev k R 0 y)⁻¹ := by
  refine (Matrix.inv_eq_left_inv ?_).symm
  rw [← Dx2.Tower.lev_mul, Matrix.nonsing_inv_mul _ hy, Dx2.Tower.lev_one]


set_option maxHeartbeats 1000000 in
theorem vecV_append_singleton_eq_vecV_sliceAt (k R ρ : ℕ) (hρ : ρ = 0) (e : R + ρ = R) (S : B.RealPlaceData k R Wp Wq) (S0 : B.RealPlaceData k ρ Wp Wq)
    (hzL : D.castV e (liftVec k R ρ S0.z) = S.z) (hzL' : D.castV e (liftVec k R ρ S0.z') = S.z')
    (hπ : ∀ y, S0.π y = S.π (D.castM e (ιLev k R ρ y))) (hπ' : ∀ y, S0.π' y = S.π' (D.castM e (ιLev k R ρ y)))
    (hN : S.μN = D.muN k R) (hW1 : S.μW Set.univ = 1) (hW1' : S.μW' Set.univ = 1)
    (hW01 : S0.μW Set.univ = 1) (hW01' : S0.μW' Set.univ = 1) (hN0 : S0.μN = D.muN k ρ)
    (ν' : Fin (2 * R + k + 1) → ℂ) (m₀ : B.Mat k R) (ν'r : Fin (2 * ρ + k + 1) → ℂ) (m₀r : B.Mat k ρ)
    (hν : D.castV e (liftVec k R ρ ν'r) = ν') (hm : D.castM e (ιLev k R ρ m₀r) = m₀)
    (hFb : D.IsBaseFrame S ν' m₀) (hF0 : D.IsBaseFrame S0 ν'r m₀r)
    (h : C.LPt) (hh : D.IsLocPt h R) (ζ : ℂ) (hζ : ζ ≠ 0)
    (F : B.Mat k R → (Wq →L[ℂ] Wp)) (hF : KB.CptCoef S F) (hR : 1 ≤ R) (e' : ρ = R - D.ptSize h) :
    D.vecV S ν' m₀ F (h ++ [(1, ζ)]) = D.vecV S0 ν'r m₀r (D.castF e' (D.sliceAt k R S.z S.z' F h)) [(1, ζ)] := by
  subst hρ
  have hzS : S.z = liftVec k R 0 S0.z := by rw [← hzL]; exact (Dx2.Tower.castV_rfl _).symm
  have hzS' : S.z' = liftVec k R 0 S0.z' := by rw [← hzL']; exact (Dx2.Tower.castV_rfl _).symm
  have hνS : ν' = liftVec k R 0 ν'r := by rw [← hν]; exact Dx2.Tower.castV_rfl _
  have hmS : m₀ = ιLev k R 0 m₀r := by rw [← hm]; exact Dx2.MN.castM_rfl _
  have hT : Tz k R S.z = Tz k 0 S0.z := by rw [hzS]; exact Tz_lift R S0.z
  have hT' : Tz k R S.z' = Tz k 0 S0.z' := by rw [hzS']; exact Tz_lift R S0.z'
  obtain ⟨hZh, hdR, hQmono, hdd, hw⟩ := CompactCoefficientAppend.perm_app h R hh ζ hζ
  set σR := hh.2 ▸ D.ptPerm h with hσR
  set dR := hh.2 ▸ D.ptDiag h with hdRdef
  set Z := U.hMat σR dR with hZdef
  have hZu : IsUnit Z.det := by rw [hZdef, hMat_monoP]; exact C2x2.isUnit_det_monomialMatrix _ _ hdR
  have hq := isLocPt_app h R hh ζ hζ
  have hG : D.ptG (Tz k R S.z * Tz k R S.z') R (h ++ [(1, ζ)]) =
      Complex.normSq (D.ptMatN h R).det * (Complex.normSq ζ - Tz k R S.z * Tz k R S.z') := by
    unfold D.ptG
    rw [ptMatN_append_one h ζ R hh.2, det_extendOne, ptMatN_append_head h ζ R hh.2, Complex.normSq_mul]
    ring
  have hdetpos : 0 < Complex.normSq (D.ptMatN h R).det := by
    rw [← hZh]; exact Complex.normSq_pos.2 hZu.ne_zero
  by_cases hζT : Complex.normSq ζ ≤ Tz k R S.z * Tz k R S.z'
  · have hL : D.vecV S ν' m₀ F (h ++ [(1, ζ)]) = 0 := by
      unfold D.vecV
      rw [dite_eq_right]
      rintro ⟨_, hpos⟩
      rw [hG] at hpos
      nlinarith
    rw [hL, vector_level_zero_degenerate rfl S0 ν'r m₀r _ ζ (by rw [← hT, ← hT']; exact hζT)]
  push_neg at hζT
  have hζT0 : Tz k 0 S0.z * Tz k 0 S0.z' < Complex.normSq ζ := by rw [← hT, ← hT']; exact hζT
  obtain ⟨γ0, hγ0G, hZ0, hD0⟩ := exists_frame_level_zero rfl S0 ν'r m₀r hF0 ζ hζT0
  rw [vector_level_zero_eq_jacquet rfl S0 ν'r m₀r hF0 _ ζ hζT0 γ0 hγ0G hZ0 hD0, jacquet_integral_level_zero rfl S0 hN0 _ γ0]
  have hZ0' : Zhat k 0 S0.z S0.z' γ0 = Matrix.of fun _ _ => ζ := by rw [hZ0, ptMatN_one]
  have hγG : U.mMap k R 0 Z γ0 ∈ B.GV k R := (Formalism.FourierDecayAlt.P.slice_membership k R 0).1 Z γ0 hZu.ne_zero hγ0G
  have hZhat : Zhat k R S.z S.z' (U.mMap k R 0 Z γ0) = D.ptMatN (h ++ [(1, ζ)]) (R + 1) := by
    have h1 := zhat_mMap (j := R) S.z S.z' S.z_mem S.z'_mem Z γ0
    refine h1.trans ?_
    rw [hzS, hzS', lowV_liftVec, lowV_liftVec, hZ0', ptMatN_append_one h ζ R hh.2, hZh]
  have hDγ : D.IsDFrame S ν' m₀ (U.mMap k R 0 Z γ0) := by
    rw [hνS, hmS]
    exact dFrame_mMap S S0 hzS hzS' ν'r m₀r Z hZu γ0 (gv_unit hγ0G) ζ hζ hZ0' hD0
  have hpos : 0 < D.ptG (Tz k R S.z * Tz k R S.z') R (h ++ [(1, ζ)]) := by
    rw [hG]; exact mul_pos hdetpos (by linarith)
  rw [Formalism.FourierDecayAlt.P.isotropic_vectors_linear_indep k R Wp Wq S ν' m₀ F _ hq _ hFb hpos hγG hZhat hDγ]
  have hrel := Formalism.FourierDecayAlt.P.relevant_points_holds k R Wp Wq S _ _ hq hγG hZhat
  obtain ⟨hFc, Rb, hFs⟩ := CompactCoefficientAppend.cptCoef_cont_supp S F hF
  have hZw : Zhat k R S.z S.z' (U.mMap k R 0 Z γ0) =
      C2.monoP (hq.2 ▸ D.ptPerm (h ++ [(1, ζ)])) (hq.2 ▸ D.ptDiag (h ++ [(1, ζ)])) := by
    rw [hZhat]; exact hQmono
  rw [orbJ_mMap S hN hW1 hW1' S0.z S0.z' hzS hzS' σR dR hdR γ0 hγ0G hrel _ _ hdd hZw hw F hFc hR Rb hFs]

  have hsW0 : SigmaFinite S0.μW := Dx2.OrbJ.sigmaF S0.haarW
  have hsW0' : SigmaFinite S0.μW' := Dx2.OrbJ.sigmaF S0.haarW'
  have hH := haar_lev R 0 e S0.z S.z hzL S.μW S0.μW S.haarW S0.haarW hW1 hW01
  have hH' := haar_lev R 0 e S0.z' S.z' hzL' S.μW' S0.μW' S.haarW' S0.haarW' hW1' hW01'
  rw [hH, hH', Measure.map_prod_map _ _ (levMt_cont R 0 e).measurable (levMt_cont R 0 e).measurable,
    ((levMt_emb R 0 e).prodMap (levMt_emb R 0 e)).integral_map]
  have hae : ∀ᵐ y ∂(S0.μW.prod S0.μW'), Matrix.of y.1 ∈ UWset k 0 S0.z ∧ Matrix.of y.2 ∈ UWset k 0 S0.z' := by
    have b1 := (Measure.quasiMeasurePreserving_fst (μ := S0.μW) (ν := S0.μW')).ae (Dx2.OrbJ.ae_mem S0.haarW)
    have b2 := (Measure.quasiMeasurePreserving_snd (μ := S0.μW) (ν := S0.μW')).ae (Dx2.OrbJ.ae_mem S0.haarW')
    filter_upwards [b1, b2] with x h1 h2 using ⟨h1, h2⟩
  refine integral_congr_ae ?_
  filter_upwards [hae] with y hy
  obtain ⟨y1, y2⟩ := y
  have hlev : ∀ x : Mt k 0, Matrix.of (levMt R 0 e x) = ιLev k R 0 (Matrix.of x) := by
    intro x; simp only [levMt, Equiv.apply_symm_apply]; exact Dx2.MN.castM_rfl _
  simp only [Prod.map_apply, conjL_apply, hlev, midB_lev]
  have hy2u : IsUnit (Matrix.of y2).det := gv_unit hy.2.1
  rw [← lev_inv _ hy2u, hπ (Matrix.of y1), hπ' (Matrix.of y2)⁻¹, Dx2.MN.castM_rfl, Dx2.MN.castM_rfl]
  congr 2

  show _ = D.sliceAt k R S.z S.z' F h (D.castM e' ((Matrix.of y1)⁻¹ * γ0 * Matrix.of y2))
  unfold D.sliceAt
  rw [dite_eq_left (by rw [hh.2]), phiFun_tr R (D.ptSize h) (R - D.ptSize h) hh.2 (by rw [hh.2]; simp),
    cast_cancel]

end master

end Formalism.FourierDecayAlt.P.PBM
end
end

