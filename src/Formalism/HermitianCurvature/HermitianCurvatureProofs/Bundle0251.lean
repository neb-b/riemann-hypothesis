module

public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0246
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.PBGLet
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutHB2
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.ExistsCompactCutoffCoefficient
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0189
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0226
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.ComponentFamilySettingOfSettingBis
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0033
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0241

@[expose] public section

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.CutEX_UwTop
section
noncomputable section

open Matrix MeasureTheory Filter Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt
open scoped ContDiff

namespace Formalism.FourierDecayAlt.P.CutEXUw

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

section gloc

variable {k r : ℕ} {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]

def LocOpG (T : (B.Mat k r → E) → (B.Mat k r → E)) : Prop :=
  ∀ O : Set (B.Mat k r), IsOpen O → ∀ f₁ f₂ : B.Mat k r → E, (∀ x ∈ O, x ∈ B.GV k r → f₁ x = f₂ x) →
    ∀ x ∈ O, x ∈ B.GV k r → T f₁ x = T f₂ x

theorem locOpG_top (u : ℂ) (a b : Fin (2 * r + k + 1)) :
    LocOpG (k := k) (r := r) (E := E) (Formalism.QuantumDeterminants.Top (EabH (Hpk k r)) u a b) := by
  intro O hO f₁ f₂ h x hx hxG
  exact PBG.top_congr' O hO u a b h x hx hxG

theorem locOpG_foldr : ∀ (L : List ((B.Mat k r → E) → (B.Mat k r → E))), (∀ T ∈ L, LocOpG T) →
    LocOpG (fun f => L.foldr (fun T h => T h) f)
  | [], _ => fun _ _ _ _ h => h
  | T :: L, hL => by
    intro O hO f₁ f₂ h x hx hxG
    simp only [List.foldr_cons]
    exact hL T List.mem_cons_self O hO _ _
      (locOpG_foldr L (fun T' hT' => hL T' (List.mem_cons_of_mem _ hT')) O hO f₁ f₂ h) x hx hxG

theorem locOpG_qminorOp {t : ℕ} (a b : Fin t → Fin (2 * r + k + 1)) (u : ℂ) :
    LocOpG (k := k) (r := r) (E := E) (qminorOp (EabH (Hpk k r)) a b u) := by
  intro O hO f₁ f₂ h x hx hxG
  simp only [qminorOp, Finset.sum_apply, Pi.smul_apply]
  refine Finset.sum_congr rfl fun σ _ => ?_
  congr 1
  refine locOpG_foldr _ (fun T hT => ?_) O hO f₁ f₂ h x hx hxG
  obtain ⟨i, rfl⟩ := List.mem_ofFn.1 hT
  exact locOpG_top _ _ _

theorem locOpG_AAop (m : ℕ) (hm : m ≤ r) (u : ℂ) : LocOpG (k := k) (r := r) (E := E) (C3.AAop k r m hm u) := by
  intro O hO f₁ f₂ h x hx hxG
  simp only [C3.AAop]
  refine Finset.sum_congr rfl fun c _ => ?_
  split_ifs
  · rw [locOpG_qminorOp _ _ _ O hO f₁ f₂ h x hx hxG]
  · rfl

theorem locOpG_AAvop (m : ℕ) (hm : m ≤ r) (ell : ℂ) :
    LocOpG (k := k) (r := r) (E := E) (C3.AAvop k r m hm ell) := by
  intro O hO f₁ f₂ h x hx hxG
  simp only [C3.AAvop]
  refine Finset.sum_congr rfl fun c _ => ?_
  split_ifs
  · rw [locOpG_qminorOp _ _ _ O hO f₁ f₂ h x hx hxG]
  · rfl

theorem locOpG_vLet (z z' : Fin (2 * r + k + 1) → ℂ) (j : ℕ) (hj : j ≤ r) (l : C.Letter) (e : Fin 2) :
    LocOpG (k := k) (r := r) (E := E) (D.vLet k r z z' j hj l e) := by
  intro O hO f₁ f₂ h x hx hxG
  simp only [D.vLet]
  split_ifs
  · rfl
  · rw [locOpG_AAop _ _ _ O hO f₁ f₂ h x hx hxG]
  · rw [locOpG_AAvop _ _ _ O hO f₁ f₂ h x hx hxG]

theorem uwG_congrG (z z' : Fin (2 * r + k + 1) → ℂ) (j : ℕ) (hj : j ≤ r) {O : Set (B.Mat k r)} (hO : IsOpen O)
    {f₁ f₂ : B.Mat k r → E} (h : ∀ x ∈ O, x ∈ B.GV k r → f₁ x = f₂ x) :
    ∀ (w : List C.Letter) (e : Wd.Ix (Fin w.length)), ∀ x ∈ O, x ∈ B.GV k r →
      D.uwG k r z z' f₁ j hj w e x = D.uwG k r z z' f₂ j hj w e x
  | [], _ => h
  | l :: w, e => by
    intro x hx hxG
    simp only [D.uwG]
    exact locOpG_vLet z z' j hj l _ O hO _ _ (uwG_congrG z z' j hj hO h w _) x hx hxG

theorem top_zero (u : ℂ) (a b : Fin (2 * r + k + 1)) :
    Formalism.QuantumDeterminants.Top (EabH (Hpk k r)) u a b (fun _ : B.Mat k r => (0 : E)) = fun _ => 0 := by
  funext g
  simp only [Formalism.QuantumDeterminants.Top, smul_zero, ite_self, zero_add]
  exact PBG.eabH_zero a b g

theorem foldr_zero : ∀ (L : List ((B.Mat k r → E) → (B.Mat k r → E))),
    (∀ T ∈ L, T (fun _ => 0) = fun _ => 0) → L.foldr (fun T h => T h) (fun _ => (0 : E)) = fun _ => 0
  | [], _ => rfl
  | T :: L, hL => by
    simp only [List.foldr_cons]
    rw [foldr_zero L (fun T' hT' => hL T' (List.mem_cons_of_mem _ hT'))]
    exact hL T List.mem_cons_self

theorem qminorOp_zero {t : ℕ} (a b : Fin t → Fin (2 * r + k + 1)) (u : ℂ) :
    qminorOp (EabH (Hpk k r)) a b u (fun _ : B.Mat k r => (0 : E)) = fun _ => 0 := by
  unfold qminorOp
  apply Finset.sum_eq_zero
  intro σ _
  rw [foldr_zero _ (fun T hT => by obtain ⟨i, rfl⟩ := List.mem_ofFn.1 hT; exact top_zero _ _ _)]
  funext g
  simp

theorem AAop_zero (m : ℕ) (hm : m ≤ r) (u : ℂ) : C3.AAop k r m hm u (fun _ : B.Mat k r => (0 : E)) = fun _ => 0 := by
  funext g
  simp only [C3.AAop]
  apply Finset.sum_eq_zero
  intro c _
  split_ifs
  · rw [qminorOp_zero]; simp
  · rfl

theorem AAvop_zero (m : ℕ) (hm : m ≤ r) (ell : ℂ) :
    C3.AAvop k r m hm ell (fun _ : B.Mat k r => (0 : E)) = fun _ => 0 := by
  funext g
  simp only [C3.AAvop]
  apply Finset.sum_eq_zero
  intro c _
  split_ifs
  · rw [qminorOp_zero]; simp
  · rfl

theorem vLet_zero (z z' : Fin (2 * r + k + 1) → ℂ) (j : ℕ) (hj : j ≤ r) (l : C.Letter) (e : Fin 2) :
    D.vLet k r z z' j hj l e (fun _ : B.Mat k r => (0 : E)) = fun _ => 0 := by
  funext g
  simp only [D.vLet]
  split_ifs
  · rfl
  · rw [AAop_zero]; simp
  · rw [AAvop_zero]; simp

theorem uwG_zero (z z' : Fin (2 * r + k + 1) → ℂ) (j : ℕ) (hj : j ≤ r) :
    ∀ (w : List C.Letter) (e : Wd.Ix (Fin w.length)),
      D.uwG k r z z' (fun _ : B.Mat k r => (0 : E)) j hj w e = fun _ => 0
  | [], _ => rfl
  | l :: w, e => by
    simp only [D.uwG]
    rw [uwG_zero z z' j hj w _]
    exact vLet_zero z z' j hj l _

end gloc

theorem continuous_gN {k r : ℕ} : Continuous (fun g : B.Mat k r => B.gN g) := by
  unfold B.gN
  fun_prop

theorem topCls_uwG {k r : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] (Bs : B.RealPlaceData k r Wp Wq) (F : B.Mat k r → (Wq →L[ℂ] Wp))
    (hF : CutEX.TopCls Bs F) (w : List C.Letter) (e : Wd.Ix (Fin w.length)) :
    CutEX.TopCls Bs (D.uwG k r Bs.z Bs.z' F r le_rfl w e) := by
  obtain ⟨⟨hsm, ⟨R, hR⟩, ⟨ε, hε, hεG⟩⟩, ⟨K, hK, h0K, hDK⟩⟩ := hF
  let S : Set (B.Mat k r) := {x | x ∈ B.GV k r ∧ F x ≠ 0}
  have hDc : Continuous (fun x : B.Mat k r => Dmin k r Bs.z Bs.z' x ⟨r, by omega⟩) :=
    (Formalism.FourierDecayAlt.P.JCx1.contDiff_Dmin Bs.z Bs.z' _).continuous
  have hvan : ∀ x ∈ (closure S)ᶜ, x ∈ B.GV k r → D.uwG k r Bs.z Bs.z' F r le_rfl w e x = 0 := by
    intro x hx hxG
    have hz : ∀ y ∈ (closure S)ᶜ, y ∈ B.GV k r → F y = (fun _ => (0 : Wq →L[ℂ] Wp)) y := by
      intro y hy hyG
      by_contra hne
      exact hy (subset_closure ⟨hyG, hne⟩)
    rw [uwG_congrG Bs.z Bs.z' r le_rfl isClosed_closure.isOpen_compl hz w e x hx hxG, uwG_zero]
  have hcl : ∀ x, x ∈ B.GV k r → D.uwG k r Bs.z Bs.z' F r le_rfl w e x ≠ 0 → x ∈ closure S := by
    intro x hxG hne
    by_contra hx
    exact hne (hvan x hx hxG)
  have hDcl : ∀ x ∈ closure S, Dmin k r Bs.z Bs.z' x ⟨r, by omega⟩ ∈ K := by
    have hsub : S ⊆ (fun x => Dmin k r Bs.z Bs.z' x ⟨r, by omega⟩) ⁻¹' K := fun x hx => hDK x hx.1 hx.2
    exact fun x hx => closure_minimal hsub (hK.isClosed.preimage hDc) hx
  refine ⟨⟨?_, ⟨R, ?_⟩, ⟨ε, hε, ?_⟩⟩, ⟨K, hK, h0K, ?_⟩⟩
  · intro g₀ hg₀
    by_cases hD : Dmin k r Bs.z Bs.z' g₀ ⟨r, by omega⟩ = 0
    · have hg₀S : g₀ ∈ (closure S)ᶜ := fun h => h0K (hD ▸ hDcl g₀ h)
      exact ⟨(closure S)ᶜ, fun _ => 0, isClosed_closure.isOpen_compl, hg₀S, contDiffOn_const,
        fun x hx hxG => hvan x hx hxG⟩
    · exact PBG.uwG_mem Bs.z Bs.z' r le_rfl hsm w e g₀ hD hg₀
  · intro g hg hne
    have hsub : S ⊆ {x | B.gN x ≤ R} := fun x hx => hR x hx.1 hx.2
    exact closure_minimal hsub (isClosed_le continuous_gN continuous_const) (hcl g hg hne)
  · intro g hg hne
    have hsub : S ⊆ {x | ε ≤ Gf k r Bs.z Bs.z' x} := fun x hx => hεG x hx.1 hx.2
    exact closure_minimal hsub (isClosed_le continuous_const (Formalism.FourierDecayAlt.P.Ux8.cont_Gf _ _ _ _)) (hcl g hg hne)
  · intro g hg hne
    exact hDcl g (hcl g hg hne)

end Formalism.FourierDecayAlt.P.CutEXUw

namespace Formalism.FourierDecayAlt.P

theorem unipotent_weight_top : CutEX.UwTop := by
  intro Wp Wq _ _ _ _ _ _ P p F hF w e
  exact CutEXUw.topCls_uwG p.T.base F hF w e

end Formalism.FourierDecayAlt.P
end
end

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.CutHBCutOff
section
open Matrix MeasureTheory

noncomputable section

namespace Formalism.FourierDecayAlt.P.CutHB

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.P.LevelPointCoordinates Formalism.FourierDecayAlt.P.PBQ

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

def CutOffStep : Prop :=
  ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (P : M.Par) (p : KB.Pl P Wp Wq) (F)
    (j : ℕ) (hj : j + 1 ≤ P.r) (w : List C.Letter) (h : C.LPt) (hh : D.IsLocPt h j)
    (γ : B.Mat P.k (P.r - (j + 1))),
    γ ∈ B.GV P.k (P.r - (j + 1)) →
    γ ∈ Q.OmPlus P.k (P.r - (j + 1)) (p.T.bs (j + 1)).z (p.T.bs (j + 1)).z' →
    ∀ (t : ℂ) (ht : D.IsLocPt (h ++ [(1, t)]) (j + 1)) (e : Wd.Ix (Fin w.length))
      (Fc : B.Mat P.k P.r → (Wq →L[ℂ] Wp)), KB.CptCoef p.T.base Fc →
      (∀ g, Dmin P.k P.r p.T.base.z p.T.base.z' g ⟨j + 1, by omega⟩ = (U.hMat (D.ptPerm h) (D.ptDiag h)).det * t →
        Fc g = D.uwG P.k P.r p.T.base.z p.T.base.z' F (j + 1) hj w e g) →
      B.JF (p.T.bs (j + 1)) (KB.slv p.T F (j + 1) hj w (h ++ [(1, t)]) ht.2 e) γ =
        B.JF (p.T.bs j) (KB.slv p.T Fc j (by omega) [] h hh.2 (fun a => a.elim0)) (mLev P j hj t γ)

def CutOffExists : Prop :=
  ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (P : M.Par) (p : KB.Pl P Wp Wq) (F)
    (j : ℕ) (hj : j + 1 ≤ P.r) (w : List C.Letter) (h : C.LPt) (hh : D.IsLocPt h j),
    KB.CptCoef p.T.base F →
    ∀ (t : ℂ) (ht : D.IsLocPt (h ++ [(1, t)]) (j + 1)) (e : Wd.Ix (Fin w.length)),
      ∃ Fc : B.Mat P.k P.r → (Wq →L[ℂ] Wp), KB.CptCoef p.T.base Fc ∧
        ∀ g, Dmin P.k P.r p.T.base.z p.T.base.z' g ⟨j + 1, by omega⟩ = (U.hMat (D.ptPerm h) (D.ptDiag h)).det * t →
          Fc g = D.uwG P.k P.r p.T.base.z p.T.base.z' F (j + 1) hj w e g

section proofs

variable {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq]

theorem det_hMat_app (h : C.LPt) (t : ℂ) :
    (U.hMat (D.ptPerm (h ++ [(1, t)])) (D.ptDiag (h ++ [(1, t)]))).det =
      (U.hMat (D.ptPerm h) (D.ptDiag h)).det * t := by
  rw [Formalism.FourierDecayAlt.P.PBI.det_hMat_pt, Formalism.FourierDecayAlt.P.PBI.det_hMat_pt h]
  have hsz : D.ptSize (h ++ [(1, t)]) = D.ptSize h + 1 := by
    simp [D.ptSize]
  rw [hsz, (Formalism.FourierDecayAlt.P.PBD.det_ptMatN_app t h (D.ptSize h) rfl).1, mul_comm]

theorem uwG_zero_of_G {k r : ℕ} (z z' : Fin (2 * r + k + 1) → ℂ) (F : B.Mat k r → (Wq →L[ℂ] Wp)) (ε : ℝ)
    (hε : ∀ g ∈ B.GV k r, F g ≠ 0 → ε ≤ Gf k r z z' g) (i : ℕ) (hi : i ≤ r) :
    ∀ (w : List C.Letter) (e : Wd.Ix (Fin w.length)), ∀ g ∈ B.GV k r,
      D.uwG k r z z' F i hi w e g ≠ 0 → ε ≤ Gf k r z z' g
  | [], _, g, hg, hne => hε g hg hne
  | l :: w, e, g, hg, hne => by
    by_contra hlt
    push Not at hlt
    apply hne
    show D.vLet k r z z' i hi l (e 0) (D.uwG k r z z' F i hi w fun a => e a.succ) g = 0
    refine Formalism.FourierDecayAlt.P.PBG.vLet_zero_near z z' i hi l (e 0) _ (V := {x | Gf k r z z' x < ε})
      (isOpen_lt (Formalism.FourierDecayAlt.P.DifferentialOperatorClasses.gf_cont k r z z') continuous_const) (fun x hx hxG => ?_) g hlt hg
    by_contra h0
    exact absurd (uwG_zero_of_G z z' F ε hε i hi w _ x hxG h0) (not_le.2 hx)

def cutW {P : M.Par} (Bs : B.RealPlaceData P.k P.r Wp Wq) (χ : ℂ → ℝ) (F : B.Mat P.k P.r → (Wq →L[ℂ] Wp)) (i : ℕ)
    (hi : i ≤ P.r) (w : List C.Letter) (e : Wd.Ix (Fin w.length)) : B.Mat P.k P.r → (Wq →L[ℂ] Wp) :=
  fun g => χ (Dmin P.k P.r Bs.z Bs.z' g ⟨i, by omega⟩) • D.uwG P.k P.r Bs.z Bs.z' F i hi w e g

theorem cutW_exists {P : M.Par} (Bs : B.RealPlaceData P.k P.r Wp Wq) (F : B.Mat P.k P.r → (Wq →L[ℂ] Wp))
    (hF : KB.CptCoef Bs F) (i : ℕ) (hi : i ≤ P.r) (w : List C.Letter) (e : Wd.Ix (Fin w.length)) (a : ℂ)
    (ha : a ≠ 0) :
    ∃ Fc : B.Mat P.k P.r → (Wq →L[ℂ] Wp), KB.CptCoef Bs Fc ∧
      ∀ g, Dmin P.k P.r Bs.z Bs.z' g ⟨i, by omega⟩ = a → Fc g = D.uwG P.k P.r Bs.z Bs.z' F i hi w e g := by
  obtain ⟨hck, ⟨R, hR⟩, ε, hε, hεG⟩ := hF
  have hn : 0 < ‖a‖ := norm_pos_iff.mpr ha
  let b : ContDiffBump a := ⟨‖a‖ / 4, ‖a‖ / 2, by positivity, by linarith⟩
  have hD : ContDiff ℝ (⊤ : ℕ∞) (fun g : B.Mat P.k P.r => Dmin P.k P.r Bs.z Bs.z' g ⟨i, by omega⟩) :=
    Formalism.FourierDecayAlt.P.JCx1.contDiff_Dmin Bs.z Bs.z' _
  have hbD : ContDiff ℝ (⊤ : ℕ∞) (fun g : B.Mat P.k P.r => b (Dmin P.k P.r Bs.z Bs.z' g ⟨i, by omega⟩)) :=
    b.contDiff.comp hD
  have hne : ∀ g, cutW Bs b F i hi w e g ≠ 0 → D.uwG P.k P.r Bs.z Bs.z' F i hi w e g ≠ 0 := by
    intro g hg h0
    apply hg
    simp [cutW, h0]
  refine ⟨cutW Bs b F i hi w e, ⟨?_, ⟨R, fun g hg h1 => Formalism.FourierDecayAlt.P.PBG.uwG_supp Bs.z Bs.z' F R hR i hi w e g hg
      (hne g h1)⟩, ε, hε, fun g hg h1 => uwG_zero_of_G Bs.z Bs.z' F ε hεG i hi w e g hg (hne g h1)⟩, ?_⟩
  · intro g₀ hg₀
    by_cases h0 : Dmin P.k P.r Bs.z Bs.z' g₀ ⟨i, by omega⟩ = 0
    · refine ⟨{g | ‖Dmin P.k P.r Bs.z Bs.z' g ⟨i, by omega⟩‖ < ‖a‖ / 2}, fun _ => 0,
        isOpen_lt (continuous_norm.comp hD.continuous) continuous_const, by simp [h0]; positivity,
        contDiffOn_const, fun g hg _ => ?_⟩
      have hb0 : b (Dmin P.k P.r Bs.z Bs.z' g ⟨i, by omega⟩) = 0 := by
        apply Function.notMem_support.1
        rw [b.support_eq, Metric.mem_ball, dist_eq_norm]
        intro hlt
        have h1 : ‖a‖ ≤ ‖Dmin P.k P.r Bs.z Bs.z' g ⟨i, by omega⟩ - a‖ + ‖Dmin P.k P.r Bs.z Bs.z' g ⟨i, by omega⟩‖ := by
          have := norm_sub_le (Dmin P.k P.r Bs.z Bs.z' g ⟨i, by omega⟩) (Dmin P.k P.r Bs.z Bs.z' g ⟨i, by omega⟩ - a)
          simp at this
          linarith
        have h2 : b.rOut = ‖a‖ / 2 := rfl
        have h3 : ‖Dmin P.k P.r Bs.z Bs.z' g ⟨i, by omega⟩‖ < ‖a‖ / 2 := hg
        linarith
      simp [cutW, hb0]
    · obtain ⟨U, f', hU, hgU, hf', hE⟩ :=
        Formalism.FourierDecayAlt.P.PBG.uwG_mem Bs.z Bs.z' i hi hck w e g₀ h0 hg₀
      refine ⟨U, fun g => b (Dmin P.k P.r Bs.z Bs.z' g ⟨i, by omega⟩) • f' g, hU, hgU,
        (hbD.contDiffOn.of_le le_rfl).smul hf', fun g hg hgG => ?_⟩
      simp only [cutW]
      rw [hE g hg hgG]
  · intro g hg
    simp only [cutW]
    rw [hg, b.one_of_mem_closedBall (Metric.mem_closedBall_self b.rIn_pos.le), one_smul]

end proofs

theorem truncation_off_exists_formula : CutOffExists := by
  intro Wp Wq _ _ _ _ _ _ P p F j hj w h hh hF t ht e
  have ht0 : t ≠ 0 := (ht.1 (1, t) (List.mem_append_right _ (List.mem_singleton_self _))).2
  have hH : (U.hMat (D.ptPerm h) (D.ptDiag h)).det ≠ 0 := by
    rw [Formalism.FourierDecayAlt.P.PBI.det_hMat_pt, hh.2]
    exact Formalism.FourierDecayAlt.P.PBI.det_ptMatN_ne h j hh
  exact cutW_exists p.T.base F hF (j + 1) hj w e _ (mul_ne_zero hH ht0)

theorem truncation_off_induction : CutOffStep := by
  intro Wp Wq _ _ _ _ _ _ P p F j hj w h hh γ hγ hΩ t ht e Fc hFc hag
  have hs : KB.slv p.T F (j + 1) hj w (h ++ [(1, t)]) ht.2 e =
      KB.slv p.T Fc (j + 1) hj [] (h ++ [(1, t)]) ht.2 (fun a => a.elim0) := by
    unfold KB.slv
    congr 1
    apply Formalism.FourierDecayAlt.P.PBI.sliceAt_congr_Dr _ _ _ (by rw [ht.2]; exact hj)
    intro x hx
    symm
    show Fc x = _
    apply hag
    have e1 : (⟨j + 1, by omega⟩ : Fin (P.r + 2)) = ⟨D.ptSize (h ++ [(1, t)]), by rw [ht.2]; omega⟩ :=
      Fin.ext ht.2.symm
    rw [e1, hx, det_hMat_app]
  rw [hs, Formalism.FourierDecayAlt.P.slice_induction_level Wp Wq P p Fc j hj h t hh ht hFc γ hγ hΩ]
  rfl

end Formalism.FourierDecayAlt.P.CutHB
end
end

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.CutHLMinusZeroOfParts
section
open Matrix
open scoped ComplexConjugate

noncomputable section

namespace Formalism.FourierDecayAlt.P.CutHLMZ

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.P.LevelPointCoordinates Formalism.FourierDecayAlt.P.CutHL

variable {k r : ℕ} {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]

theorem dmin_zero (z z' : Fin (2 * r + k + 1) → ℂ) (g : Q.Mx k r) (h : 0 < r + 2) :
    Dmin k r z z' g ⟨0, h⟩ = 1 := by
  unfold Dmin
  exact Matrix.det_isEmpty

theorem qminorOp_zero (a b : Fin 0 → Fin (2 * r + k + 1)) (u : ℂ) (f : Q.Mx k r → E) (g : Q.Mx k r) :
    qminorOp (EabH (Hpk k r)) a b u f g = f g := by
  unfold qminorOp
  rw [Finset.sum_apply, Fintype.sum_unique]
  simp

theorem AAvop_zero (h : 0 ≤ r) (ell : ℂ) (f : Q.Mx k r → E) (g : Q.Mx k r) : C3.AAvop k r 0 h ell f g = f g := by
  unfold C3.AAvop
  rw [Fintype.sum_unique, if_pos (Subsingleton.strictMono _), Matrix.det_isEmpty, one_smul, qminorOp_zero]

theorem qminorOp_one (a b : Fin 1 → Fin (2 * r + k + 1)) (u : ℂ) (f : Q.Mx k r → E) (g : Q.Mx k r) :
    qminorOp (EabH (Hpk k r)) a b u f g =
      (if a 0 = b 0 then u • f g else 0) + EabH (Hpk k r) (a 0) (b 0) f g := by
  unfold qminorOp
  rw [Finset.sum_apply, Fintype.sum_unique]
  simp [QuantumDeterminants.Top]

theorem AAvop_one (h : 1 ≤ r) (x : Q.Mx k r) (w : ℂ)
    (hnf : ∀ p : Fin (2 * r + k + 1), PBG.y0 x ⟨0, by omega⟩ p = if p.val = 2 * r + k then w else 0)
    (ell : ℂ) (f : Q.Mx k r → E) :
    C3.AAvop k r 1 h ell f x =
      w • (ell • f x + Q.EH k r (esI k r ⟨0, by omega⟩) (esI k r ⟨0, by omega⟩) f x) := by
  classical
  unfold C3.AAvop
  have hent : ∀ c : Fin 1 → Fin (2 * r + k + 1),
      (Matrix.of fun a l : Fin 1 => (x⁻¹ *ᵥ bvec (eI k r (Fin.castLE h a))) (c l)).det =
        if (c 0).val = 2 * r + k then w else 0 := by
    intro c
    rw [Matrix.det_unique]
    exact hnf (c 0)
  rw [Finset.sum_eq_single (fun _ => esI k r ⟨0, by omega⟩)]
  · rw [if_pos (Subsingleton.strictMono _), hent, if_pos (by simp [esI]),
      qminorOp_one, if_pos (by simp [C3.sR, esI])]
    simp only [C3.sR, Q.EH] at *
    rw [show ell + ((1 : ℕ) : ℂ) - 1 = ell by push_cast; ring]
    rfl
  · intro c _ hc
    split_ifs with hm
    · rw [hent, if_neg, zero_smul]
      intro h0
      apply hc
      funext l
      rw [Subsingleton.elim l 0]
      ext
      simpa [esI] using h0
    · rfl
  · intro hc; exact absurd (Finset.mem_univ _) hc

end Formalism.FourierDecayAlt.P.CutHLMZ

namespace Formalism.FourierDecayAlt.P

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.P.LevelPointCoordinates Formalism.FourierDecayAlt.P.CutHL Formalism.FourierDecayAlt.P.CutHLMZ

theorem minus_zero_of_parts : CutHL.MinusZeroOfParts := by
  intro hNf hDm hT k r j hj z z' E _ _ Dm Φ Z γ τ hj0 hH Y
  subst hj0
  obtain ⟨_, _, hDo, _, hR, hZ, hτ, hγ, hx⟩ := hH
  have hnfy := (hNf k r 0 hj Z τ γ hZ hτ hγ).2
  have hT' := hT E k r 0 hj Dm Φ Z τ γ hDo hR.1 hZ hτ hγ hx
  have hD1 := (hDm k r 0 hj z z' Z τ γ hZ hτ hγ).2
  rw [Matrix.det_isEmpty, one_mul] at hD1
  have hτc : conj τ ≠ 0 := (map_ne_zero _).2 hτ
  have hv0 : ∀ g, D.vLet k r z z' 0 (by omega) (false, Y) 0 Φ g = Φ g := by
    intro g
    rw [PBG.letter_minus_component_zero, dmin_zero, map_one, inv_one, one_smul, AAvop_zero]
  have hv1 : ∀ g, D.vLet k r z z' 0 (by omega) (false, Y) 1 Φ g = 0 := by
    intro g
    unfold D.vLet
    simp
  have hA := AAvop_one (k := k) (r := r) (E := E) hj (x0 k r 0 hj Z τ γ) (conj τ) (fun p => by
      rw [hnfy ⟨0, by omega⟩ p (by simp)]
      have hp := p.isLt
      by_cases hq : p.val = 2 * r + k
      · rw [if_pos (by omega), if_pos hq, hq, Nat.sub_self]; simp [C3.Zb]
      · rw [if_neg (by omega), if_neg hq])
    ((Y : ℂ) - ((2 * r + k : ℕ) : ℂ) / 2) Φ
  have hu : ((Y : ℂ) - ((2 * r + k : ℕ) : ℂ) / 2) = (Y : ℂ) - levelZeroKernel k r 0 := by
    unfold levelZeroKernel; rw [Nat.sub_zero]; push_cast; ring
  rw [hu] at hA
  unfold Eq3
  simp only [hv0, hv1]
  rw [PBG.letter_minus_component_zero, hD1, hu, hA, smul_smul, inv_mul_cancel₀ hτc, one_smul, smul_zero, sub_zero, sub_eq_add_neg _ (conj τ • _),
    ← hT']

end Formalism.FourierDecayAlt.P
end
end

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.OneVariableLettersUnderIntegral
section
open MeasureTheory

noncomputable section

namespace Formalism.FourierDecayAlt.P.SliceIntegralLemmas

open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P.LevelPointCoordinates

theorem good_of_goodFam {E X S : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] [NormedAddCommGroup X]
    [NormedSpace ℝ X] {Φ : X → S → V1 E} (h : CutHB.GoodFam Φ) (e : S) : Good (fun v => Φ v e) := by
  refine ⟨h.1 e, fun K hK hK0 => ?_⟩
  obtain ⟨C, hC, hz⟩ := h.2 K hK hK0
  exact ⟨C, hC, fun v hv τ hτ => hz v hv τ hτ e⟩

end Formalism.FourierDecayAlt.P.SliceIntegralLemmas

namespace Formalism.FourierDecayAlt.P

open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P.LevelPointCoordinates Formalism.FourierDecayAlt.P.SliceIntegralLemmas

theorem one_variable_letters_under_integral : CutHB.OneBTInt := by
  intro E _ _ _ X _ _ _ _ _ μ _ ℓ hℓ S _ _ κ w Φ hΦ f hf t ht e
  exact (oneBT_int (μ := μ) hℓ κ w Φ f (good_of_goodFam hΦ) (fun b τ hτ => hf b τ hτ) e).2 t ht

end Formalism.FourierDecayAlt.P
end
end

