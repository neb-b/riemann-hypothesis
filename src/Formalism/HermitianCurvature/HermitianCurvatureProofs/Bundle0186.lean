module

public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0176
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0151
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.OpApplySub
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0174
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0061
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.LiftClosedUnderOperations

@[expose] public section

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.SelfAdjointDescentHolds
section
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.Q
open scoped ContDiff ComplexConjugate

noncomputable section

namespace Formalism.FourierDecayAlt.P.CutMP.JA.SA.Desc

open Formalism.FourierDecayAlt.P.Qx4

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

section iter

variable {Wp Wq : Type} [NormedAddCommGroup Wp] [NormedSpace ℂ Wp] [NormedAddCommGroup Wq] [NormedSpace ℂ Wq]
  {k r : ℕ}

def lev (r i : ℕ) : Fin (r + 1) := ⟨min i r, by omega⟩

theorem lev_castSucc (i : ℕ) (h : i < r) : (⟨i, h⟩ : Fin r).castSucc = lev r i := Fin.ext (by simp [lev]; omega)
theorem lev_succ (i : ℕ) (h : i < r) : (⟨i, h⟩ : Fin r).succ = lev r (i + 1) := Fin.ext (by simp [lev]; omega)
theorem lev_r : lev r r = Fin.last r := Fin.ext (by simp [lev])
theorem lev_zero : lev r 0 = 0 := Fin.ext (by simp [lev])

def Dn (z z' : Fin (2 * r + k + 1) → ℂ) (i : ℕ) : Set (Mx k r) :=
  if h : i < r then D0 k r ⟨i, h⟩ (Dn z z' (i + 1)) else Qx8.Dp k r z z'
termination_by r - i

def Kn (z z' : Fin (2 * r + k + 1) → ℂ) (Φ : Fn k r (Wq →L[ℂ] Wp)) (i : ℕ) : Fn k r (Wq →L[ℂ] Wp) :=
  if h : i < r then JxF ⟨i, h⟩ z z' (Kn z z' Φ (i + 1)) else Φ
termination_by r - i

theorem Dn_lt (z z' : Fin (2 * r + k + 1) → ℂ) {i : ℕ} (h : i < r) :
    Dn z z' i = D0 k r ⟨i, h⟩ (Dn z z' (i + 1)) := by
  rw [Dn, dite_eq_left h]

theorem Dn_ge (z z' : Fin (2 * r + k + 1) → ℂ) {i : ℕ} (h : ¬ i < r) : Dn z z' i = Qx8.Dp k r z z' := by
  rw [Dn, dite_eq_right h]

theorem Kn_lt (z z' : Fin (2 * r + k + 1) → ℂ) (Φ : Fn k r (Wq →L[ℂ] Wp)) {i : ℕ} (h : i < r) :
    Kn z z' Φ i = JxF ⟨i, h⟩ z z' (Kn z z' Φ (i + 1)) := by
  rw [Kn, dite_eq_left h]

theorem Kn_ge (z z' : Fin (2 * r + k + 1) → ℂ) (Φ : Fn k r (Wq →L[ℂ] Wp)) {i : ℕ} (h : ¬ i < r) :
    Kn z z' Φ i = Φ := by
  rw [Kn, dite_eq_right h]

theorem famR {z z' : Fin (2 * r + k + 1) → ℂ} {π : Mx k r → (Wp →L[ℂ] Wp)} {π' : Mx k r → (Wq →L[ℂ] Wq)}
    (hz : inWb k r z) (hz' : inWb k r z') {Φ : Fn k r (Wq →L[ℂ] Wp)} (hΦ : Φ ∈ RadSp k r z z' π π') :
    FamD z z' π π' (Fin.last r) (Qx8.Dp k r z z') Φ := by
  refine ⟨fun c hc => ?_, fun c₀ hc₀ g₀ hg₀ => ?_⟩
  · have h := Qx8.slice_FF hz hz' hΦ hc
    exact ⟨h.2.1, h.2.2.1, h.2.2.2⟩
  · obtain ⟨U, F, hU, hx, hF, hΦF⟩ := hΦ.2.1 (c₀, g₀) ⟨hc₀, hg₀.1, hg₀.2⟩
    exact ⟨U, F, hU, hx, hF, fun x hx _ hg _ => hΦF x hx hg⟩

theorem allLev {z z' : Fin (2 * r + k + 1) → ℂ} {π : Mx k r → (Wp →L[ℂ] Wp)} {π' : Mx k r → (Wq →L[ℂ] Wq)}
    (hz : inWb k r z) (hz' : inWb k r z') {Φ : Fn k r (Wq →L[ℂ] Wp)} (hΦ : Φ ∈ RadSp k r z z' π π') :
    ∀ j, j ≤ r → IsDom k r z z' (lev r (r - j)) (Dn z z' (r - j)) ∧
      FamD z z' π π' (lev r (r - j)) (Dn z z' (r - j)) (Kn z z' Φ (r - j)) := by
  intro j
  induction j with
  | zero =>
    intro _
    simp only [Nat.sub_zero]
    rw [lev_r, Dn_ge z z' (lt_irrefl r), Kn_ge z z' Φ (lt_irrefl r)]
    exact ⟨Qx8.Dp_dom k r z z', famR hz hz' hΦ⟩
  | succ j ih =>
    intro hj
    obtain ⟨hD, hF⟩ := ih (by omega)
    have hi : r - (j + 1) < r := by omega
    have e : r - j = r - (j + 1) + 1 := by omega
    rw [e, ← lev_succ _ hi] at hD hF
    rw [← lev_castSucc _ hi, Dn_lt z z' hi, Kn_lt z z' Φ hi]
    exact ⟨descended_set_is_domain _ hD, famStep hz hz' _ hF⟩

def mix (i : ℕ) (c d : Fin r → ℂ) : Fin r → ℂ := fun a => if a.val < i then c a else d a

theorem vals {z z' : Fin (2 * r + k + 1) → ℂ} (hz : inWb k r z) (hz' : inWb k r z') (Φ : Fn k r (Wq →L[ℂ] Wp))
    (d : Fin r → ℂ) {c : Fin r → ℂ} (hc : c ∈ OmX r) :
    ∀ i, i ≤ r → ∀ X ∈ Glev k r (lev r i) ∩ Dn z z' i,
      wCell k r (lev r i) c * X ∈ Glev k r 0 ∩ Dn z z' 0 ∧
        Kn z z' Φ 0 d (wCell k r (lev r i) c * X) = Kn z z' Φ i (mix i c d) X := by
  intro i
  induction i with
  | zero =>
    intro _ X hX
    have hm : mix 0 c d = d := funext fun a => by simp [mix]
    rw [lev_zero] at hX ⊢
    rw [Qx6.wCell_zero, Matrix.one_mul, hm]
    exact ⟨hX, rfl⟩
  | succ i ih =>
    intro hi X hX
    have hlt : i < r := by omega
    obtain ⟨l, hl⟩ : ∃ l : Fin r, l = ⟨i, hlt⟩ := ⟨_, rfl⟩
    have hli : l.val = i := by rw [hl]
    have hcs : l.castSucc = lev r i := by rw [hl]; exact lev_castSucc i hlt
    have hsc : l.succ = lev r (i + 1) := by rw [hl]; exact lev_succ i hlt
    have hDi : Dn z z' i = D0 k r l (Dn z z' (i + 1)) := by rw [hl]; exact Dn_lt z z' hlt
    have hKi : Kn z z' Φ i = JxF l z z' (Kn z z' Φ (i + 1)) := by rw [hl]; exact Kn_lt z z' Φ hlt
    rw [← hsc] at hX ⊢
    have hcl : c l ≠ 0 := hc l
    have hX' : w1 k r l (c l) * X ∈ Glev k r (lev r i) ∩ Dn z z' i := by
      rw [← hcs, hDi]
      exact ⟨glev_mul (weyl_cell_mem_level_group (l := l) hcl) (glev_succ_le hX.1), (w1_mul_mem_descended_set_iff l _ hcl hX.1).2 hX.2⟩
    obtain ⟨hmem, hval⟩ := ih (by omega) _ hX'
    have hmix : Function.update (mix i c d) l (c l) = mix (i + 1) c d := by
      funext a
      by_cases ha : a = l
      · subst ha; simp [mix, hli]
      · have hne : a.val ≠ i := fun h => ha (Fin.ext (by rw [h, hli]))
        simp only [mix, Function.update_apply, ha, if_false]
        by_cases h1 : a.val < i
        · rw [if_pos h1, if_pos (by omega)]
        · rw [if_neg h1, if_neg (by omega)]
    rw [Qx6.wCell_succ, Matrix.mul_assoc, hcs]
    refine ⟨hmem, ?_⟩
    rw [hval, hKi, descended_function_apply_w1_mul hz hz' l _ _ hcl hX.1, hmix]

end iter

end Formalism.FourierDecayAlt.P.CutMP.JA.SA.Desc

namespace Formalism.FourierDecayAlt.P.CutMP.JA.SA

open Formalism.FourierDecayAlt.P.CutMP.JA.SA.Desc

theorem self_adjoint_descent_holds : SADescend := by
  intro Wp Wq _ _ _ _ k r z z' π π' hz hz' Φ hΦ
  have hall := allLev (π := π) (π' := π') hz hz' hΦ r le_rfl
  rw [Nat.sub_self, lev_zero] at hall
  obtain ⟨hD, hF⟩ := hall
  refine ⟨Dn z z' 0, hD, Kn z z' Φ 0 (fun _ => 1), famD_FFl hD.1 hF (fun _ => one_ne_zero), ?_⟩
  intro c hc g hg hGG
  have hv := vals hz hz' Φ (fun _ => 1) hc r le_rfl g
    ⟨by rw [lev_r]; exact hg, by rw [Dn_ge z z' (lt_irrefl r)]; exact hGG⟩
  rw [lev_r] at hv
  have hm : mix r c (fun _ => 1) = c := funext fun a => by simp [mix, a.isLt]
  rw [hm, Kn_ge z z' Φ (lt_irrefl r)] at hv
  exact ⟨hv.1.2, hv.2⟩

end Formalism.FourierDecayAlt.P.CutMP.JA.SA
end
end

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.SliceIntegralCutoff
section
open Matrix MeasureTheory Filter Topology
open scoped ContDiff

noncomputable section

namespace Formalism.FourierDecayAlt.P.FormNormSumIdentities

open Formalism.FourierDecayAlt Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.P.PBE

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

theorem levQInt : ∃ Cp : ℝ, 0 ≤ Cp ∧ ∀ Cc : ℝ, 16 * Cp ≤ Cc →
    ∀ (k r : ℕ) (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
    [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq]
    (T : D.LevTower k r Wp Wq) (χ : ℝ → ℝ) (A₀ : ℝ) (N : ℕ) (P0 : M.Par),
    P0.k = k → P0.r = r → 2 ≤ k → C6.IsCut0 χ →
    Cc * ((r : ℝ) + 1) ^ 4 * ((N : ℝ) * (2 * (r : ℝ) + k + 1) ^ 2 + (2 * (r : ℝ) + k + 1) ^ 3) ≤ A₀ →
    ∀ ε : ℝ, 0 < ε → ∀ (i : ℕ) (hi : i ≤ r), 1 ≤ i → ∀ (w : List C.Letter), w.length ≤ N →
      ∀ (p : C.LPt) (hc : r - i = r - D.ptSize p), D.IsLocPt p i → ∀ (hle : D.ptSize p ≤ r) (a : Wd.Ix (Fin w.length)),
      ∀ (hh : B.Mat k r → (Wq →L[ℂ] Wp)) (c : ℝ), B.CkOn ⊤ (B.GV k r) hh →
        B.CCle A₀ (3 * (11 * (N * (2 * r + k + 1) ^ 2 + (2 * r + k + 1) ^ 3) + 5)) hh c →
      ∀ γ ∈ B.GV k (r - D.ptSize p),
        Integrable (fun ξ : U.Xi k (D.ptSize p) 0 (r - D.ptSize p) (D.ptPerm p) =>
          U.psiStar k (r - D.ptSize p) (D.ptPerm p) (D.castV (by omega) T.base.z) (D.castV (by omega) T.base.z') ξ •
            D.castF (by omega) (D.uwG k r T.base.z T.base.z' (D.cutF T.base χ hh ε) i hi w a)
              (U.gaXi k (r - D.ptSize p) (D.ptPerm p) (D.ptDiag p) ξ (fun a => a.elim0) γ))
          (U.muXi k (D.ptSize p) 0 (r - D.ptSize p) (D.ptPerm p)) := by
  obtain ⟨Cp, hCp0, hCp⟩ := posCoreQ
  refine ⟨Cp, hCp0, ?_⟩
  intro Cc hCc k r Wp Wq _ _ _ _ _ _ T χ A₀ N P0 hPk hPr hk2 hχ hA₀ ε hε i hi hi1 w hw p hc hp hle a

  obtain ⟨h, n, t, rfl⟩ : ∃ (h : C.LPt) (n : ℕ) (t : ℂ), p = h ++ [(n + 1, t)] := by
    have hne : p ≠ [] := by
      rintro rfl
      have := hp.2
      simp [D.ptSize] at this
      omega
    refine ⟨p.dropLast, (p.getLast hne).1 - 1, (p.getLast hne).2, ?_⟩
    have h1 : 1 ≤ (p.getLast hne).1 := (hp.1 _ (List.getLast_mem hne)).1
    rw [Nat.sub_add_cancel h1]
    exact (List.dropLast_append_getLast hne).symm
  obtain ⟨hpb, hps⟩ := hp
  subst hps
  set ph := D.ptSize h with hph
  have hP : D.ptSize (h ++ [(n + 1, t)]) = ph + (n + 1) := Formalism.FourierDecayAlt.P.Dx2.SL.ptSize_append h (n + 1) t
  have ht : t ≠ 0 := (hpb (n + 1, t) (by simp)).2
  have hloc : D.IsLocPt (h ++ [(n + 1, t)]) (D.ptSize (h ++ [(n + 1, t)])) := ⟨hpb, rfl⟩
  have hlocH := Formalism.FourierDecayAlt.P.Dx2.SL.isLocPt_head hloc
  have hd0 : ∀ q, D.ptDiag h q ≠ 0 := fun q => Formalism.FourierDecayAlt.P.JCTx6.Link2.ptScal_ne h hlocH.1 q q.2
  set ρ := r - D.ptSize (h ++ [(n + 1, t)]) with hρ
  have hsum : ph + (n + 1) + ρ = r := by omega
  have hspec := (Formalism.FourierDecayAlt.P.ptPerm_spec _ _ hloc).1
  have hspec' := (Formalism.FourierDecayAlt.P.ptPerm_spec _ _ hlocH).1
  have hσ : ∀ q : Fin (D.ptSize (h ++ [(n + 1, t)])),
      ((Formalism.FourierDecayAlt.P.Dx2.SL.sigP (n := n) (D.ptPerm h)) (Fin.cast hP q)).val = (D.ptPerm (h ++ [(n + 1, t)]) q).val := by
    intro q
    rw [hspec q, Formalism.FourierDecayAlt.P.Dx2.SL.partner_append (n + 1) t h q.val (by have := q.isLt; omega)]
    by_cases h1 : q.val < D.ptSize h
    · rw [if_pos h1]
      have e : Fin.cast hP q = Fin.castAdd (n + 1) ⟨q.val, h1⟩ := Fin.ext rfl
      rw [e, Formalism.FourierDecayAlt.P.Dx2.SL.blockPerm_castAdd]
      exact hspec' ⟨q.val, h1⟩
    · rw [if_neg h1]
      have e : Fin.cast hP q = Fin.natAdd (D.ptSize h) ⟨q.val - D.ptSize h, by have := q.isLt; omega⟩ :=
        Fin.ext (by simp; omega)
      rw [e, Formalism.FourierDecayAlt.P.Dx2.SL.blockPerm_natAdd]
      simp only [Fin.val_natAdd, Fin.val_rev]
      omega
  have hd : ∀ q : Fin (D.ptSize (h ++ [(n + 1, t)])),
      Formalism.FourierDecayAlt.P.Dx2.SL.dP (n := n) (D.ptDiag h) t (Fin.cast hP q) = D.ptDiag (h ++ [(n + 1, t)]) q := by
    intro q
    simp only [D.ptDiag]
    rw [Formalism.FourierDecayAlt.P.Dx2.SL.scal_append (n + 1) t h q.val (by have := q.isLt; omega)]
    by_cases h1 : q.val < D.ptSize h
    · rw [if_pos h1]
      have e : Fin.cast hP q = Fin.castAdd (n + 1) ⟨q.val, h1⟩ := Fin.ext rfl
      rw [e, Formalism.FourierDecayAlt.P.Dx2.SL.dP, Fin.addCases_left]; rfl
    · rw [if_neg h1]
      have e : Fin.cast hP q = Fin.natAdd (D.ptSize h) ⟨q.val - D.ptSize h, by have := q.isLt; omega⟩ :=
        Fin.ext (by simp; omega)
      rw [e, Formalism.FourierDecayAlt.P.Dx2.SL.dP, Fin.addCases_right]
  have hdP : ∀ q, Formalism.FourierDecayAlt.P.Dx2.SL.dP (n := n) (D.ptDiag h) t q ≠ 0 := by
    intro q
    refine Fin.addCases (fun i => ?_) (fun i => ?_) q
    · simp only [Formalism.FourierDecayAlt.P.Dx2.SL.dP, Fin.addCases_left]; exact hd0 i
    · simp only [Formalism.FourierDecayAlt.P.Dx2.SL.dP, Fin.addCases_right]; exact ht
  have hS : ∀ (Gx : B.Mat k r → (Wq →L[ℂ] Wp)) (γ : B.Mat k ρ), D.sliceAt k r T.base.z T.base.z' Gx (h ++ [(n + 1, t)]) γ =
      U.PhiFun (p := ph + (n + 1)) (s := 0) k ρ (Formalism.FourierDecayAlt.P.Dx2.SL.sigP (D.ptPerm h))
        (Formalism.FourierDecayAlt.P.Dx2.SL.dP (D.ptDiag h) t) (D.castV (by omega) T.base.z) (D.castV (by omega) T.base.z')
        (D.castF (by omega) Gx) (fun a => a.elim0) γ := by
    intro Gx γ
    obtain ⟨-, hT2⟩ := Formalism.FourierDecayAlt.P.Dx2.SL.phi_transport (k := k) (ρ := ρ) hP _ _ hσ _ _ hd
      (D.castV (by omega) T.base.z) (D.castV (by omega) T.base.z') (D.castF (by omega) Gx) γ
    unfold D.sliceAt
    rw [dite_eq_left (by omega), hT2]
    simp only [Formalism.FourierDecayAlt.P.Dx2.SL.castV_castV, Formalism.FourierDecayAlt.P.Dx2.SL.castF_castF]
  have e1 : r = ph + (n + 1) + ρ := hsum.symm
  have e2 : ph + (n + 1) + ρ = r := hsum
  have hj1 : 1 ≤ ph + (n + 1) := by omega
  obtain ⟨Θ, hΘ, hΘF⟩ := Formalism.FourierDecayAlt.P.JCTx6.Let.lettersDD k (ph + (n + 1)) ρ Wp Wq (D.castV e1 T.base.z)
    (D.castV e1 T.base.z') (by omega) w a hj1
  have hU : ∀ hh : B.Mat k r → (Wq →L[ℂ] Wp), B.CkOn ⊤ (B.GV k r) hh →
      ∀ g ∈ B.GV k (ph + (n + 1) + ρ), U.DjU k (ph + (n + 1)) ρ g ≠ 0 →
      D.castF e2 (D.uwG k r T.base.z T.base.z' (D.cutF T.base χ hh ε) (D.ptSize (h ++ [(n + 1, t)])) hi w a) g =
        B.opApply Θ (D.castF e2 (D.cutF T.base χ hh ε)) g := by
    intro hh hsm g hg hD
    have hFc : B.CkOn ⊤ (B.GV k r) (D.cutF T.base χ hh ε) := Formalism.FourierDecayAlt.P.JCTx6.Link2.ckOn_cutF T.base hχ hsm ε
    have h1 : D.castF e2 (D.uwG k r T.base.z T.base.z' (D.cutF T.base χ hh ε) (D.ptSize (h ++ [(n + 1, t)])) hi w a) =
        D.uwG k (ph + (n + 1) + ρ) (D.castV e1 T.base.z) (D.castV e1 T.base.z')
          (D.castF e2 (D.cutF T.base χ hh ε)) (ph + (n + 1)) (by omega) w a := by
      rw [Formalism.FourierDecayAlt.P.JCTx6.Link2.castF_uwG e2 _ _ _ _ hi (by omega)]
      exact Formalism.FourierDecayAlt.P.JCTx6.Link2.uwG_level _ _ _ hP _ _ w a
    rw [h1, hΘF _ (Formalism.FourierDecayAlt.P.JCTx6.Link2.ckOn_castF e2 hFc) g hg hD]
  have hFrel : ∀ hh : B.Mat k r → (Wq →L[ℂ] Wp), B.CkOn ⊤ (B.GV k r) hh →
      ∀ g ∈ B.GV k (ph + (n + 1) + ρ), U.DjU k (ph + (n + 1)) ρ g ≠ 0 →
      D.castF e2 (D.uwG k r T.base.z T.base.z' (D.cutF T.base χ hh ε) (D.ptSize (h ++ [(n + 1, t)])) hi w a) g =
        B.opApply Θ (fun x => ((χ (Gf k (ph + (n + 1) + ρ) (D.castV e1 T.base.z)
          (D.castV e1 T.base.z') x / ε) : ℝ) : ℂ) • D.castF e2 hh x) g := by
    intro hh hsm g hg hD
    rw [hU hh hsm g hg hD, Formalism.FourierDecayAlt.P.JCTx6.Link2.castF_cutF e2]
  set nd := 2 * r + k + 1 with hnd
  set As := 11 * (N * nd ^ 2 + nd ^ 3) + 5 with hAs
  obtain ⟨b1, b2, b3, b4, b5⟩ := Formalism.FourierDecayAlt.P.JCTx6.Link2.budgetAs r k N w.length (ph + (n + 1)) hk2 hw (by omega)
  have hmmU : P5.mmUser P0 N = 5 + 3 * (r + 1) * (N + 2) * nd + N * r := by
    simp only [P5.mmUser, P5.nV, hPk, hPr, hnd]
  have hAU : P5.Auser P0 N = 127 * ((r : ℝ) + 1) ^ 3 * ((N : ℝ) * (nd : ℝ) ^ 2 + (nd : ℝ) ^ 3) := by
    simp only [P5.Auser, P5.nV, hPk, hPr, hnd]
    try (push_cast; try ring)
  have hX1 : (1 : ℝ) ≤ (N : ℝ) * (nd : ℝ) ^ 2 + (nd : ℝ) ^ 3 := by exact_mod_cast b5
  have hAsR : (As : ℝ) = 11 * ((N : ℝ) * (nd : ℝ) ^ 2 + (nd : ℝ) ^ 3) + 5 := by
    rw [hAs]; push_cast; ring
  have hR1 : (1 : ℝ) ≤ (r : ℝ) + 1 := by have : (0 : ℝ) ≤ r := Nat.cast_nonneg r; linarith
  have hsumR : (((ph + (n + 1) + ρ : ℕ) : ℝ)) = (r : ℝ) := by exact_mod_cast hsum
  obtain ⟨ε', K, hε', hK0, hQ⟩ := hCp k ph n ρ Wp Wq (D.castV e1 T.base.z) (D.castV e1 T.base.z')
    (Formalism.FourierDecayAlt.P.Dx1.SN.castV_inWb e1 _ T.base.z_mem) (Formalism.FourierDecayAlt.P.Dx1.SN.castV_inWb e1 _ T.base.z'_mem)
    Θ _ _ hΘ χ A₀ ε hχ hε (D.ptPerm h) (D.ptDiag h) t hd0 ht As (P5.mmUser P0 N) (P5.Auser P0 N + 1)
    b1 b2 (by rw [hmmU]; exact b3) (by rw [hsum]; exact b4)
    (by
      rw [hsumR, hAU, hAsR]
      have hR3 : (1 : ℝ) ≤ ((r : ℝ) + 1) ^ 3 := one_le_pow₀ hR1
      have : 0 ≤ ((r : ℝ) + 1) ^ 3 * ((N : ℝ) * (nd : ℝ) ^ 2 + (nd : ℝ) ^ 3) := by positivity
      nlinarith)
    (by
      rw [hsumR, hAsR]
      have hR4 : 0 ≤ ((r : ℝ) + 1) ^ 4 := by positivity
      have hX0 : 0 ≤ (N : ℝ) * (nd : ℝ) ^ 2 + (nd : ℝ) ^ 3 := by linarith
      have s1 : Cp * ((r : ℝ) + 1) ^ 4 * (11 * ((N : ℝ) * (nd : ℝ) ^ 2 + (nd : ℝ) ^ 3) + 5) ≤
          Cp * ((r : ℝ) + 1) ^ 4 * (16 * ((N : ℝ) * (nd : ℝ) ^ 2 + (nd : ℝ) ^ 3)) := by
        apply mul_le_mul_of_nonneg_left _ (by positivity); linarith
      have s2 : 16 * Cp * (((r : ℝ) + 1) ^ 4 * ((N : ℝ) * (nd : ℝ) ^ 2 + (nd : ℝ) ^ 3)) ≤
          Cc * (((r : ℝ) + 1) ^ 4 * ((N : ℝ) * (nd : ℝ) ^ 2 + (nd : ℝ) ^ 3)) :=
        mul_le_mul_of_nonneg_right hCc (by positivity)
      have s3 : Cc * ((r : ℝ) + 1) ^ 4 * ((N : ℝ) * (nd : ℝ) ^ 2 + (nd : ℝ) ^ 3) ≤ A₀ := by
        have hndR : (nd : ℝ) = 2 * (r : ℝ) + k + 1 := by rw [hnd]; push_cast; ring
        rw [hndR]; exact hA₀
      nlinarith)
  have hfun : ∀ hh : B.Mat k r → (Wq →L[ℂ] Wp),
      D.castF hc (D.sliceAt k r T.base.z T.base.z'
        (D.uwG k r T.base.z T.base.z' (D.cutF T.base χ hh ε) (D.ptSize (h ++ [(n + 1, t)])) hi w a) (h ++ [(n + 1, t)])) =
      fun γ => U.PhiFun (p := ph + (n + 1)) (s := 0) k ρ (Formalism.FourierDecayAlt.P.Dx2.SL.sigP (D.ptPerm h))
        (Formalism.FourierDecayAlt.P.Dx2.SL.dP (D.ptDiag h) t) (D.castV e1 T.base.z) (D.castV e1 T.base.z')
        (D.castF e2 (D.uwG k r T.base.z T.base.z' (D.cutF T.base χ hh ε) (D.ptSize (h ++ [(n + 1, t)])) hi w a))
        (fun a => a.elim0) γ := by
    intro hh
    rw [Formalism.FourierDecayAlt.P.JCTx6.Link2.castF_self]
    funext γ
    exact hS _ γ
  have hz1 : U.lowV k (ph + (n + 1)) ρ (D.castV e1 T.base.z) = (T.bs (D.ptSize (h ++ [(n + 1, t)]))).z := by
    have hzl : T.base.z = D.castV (by omega)
        (liftVec k (D.ptSize (h ++ [(n + 1, t)])) ρ (T.bs (D.ptSize (h ++ [(n + 1, t)]))).z) :=
      (T.z_lev _ hi).symm
    rw [hzl, Formalism.FourierDecayAlt.P.Dx2.SL.castV_castV]
    exact Formalism.FourierDecayAlt.P.JCTx6.Link2.lowV_liftVec hP.symm _ _
  have hz1' : U.lowV k (ph + (n + 1)) ρ (D.castV e1 T.base.z') = (T.bs (D.ptSize (h ++ [(n + 1, t)]))).z' := by
    have hzl' : T.base.z' = D.castV (by omega)
        (liftVec k (D.ptSize (h ++ [(n + 1, t)])) ρ (T.bs (D.ptSize (h ++ [(n + 1, t)]))).z') :=
      (T.z'_lev _ hi).symm
    rw [hzl', Formalism.FourierDecayAlt.P.Dx2.SL.castV_castV]
    exact Formalism.FourierDecayAlt.P.JCTx6.Link2.lowV_liftVec hP.symm _ _
  have hZ0 : G.detM (fun a => a.elim0 : G.Mat 0) ≠ 0 := by
    unfold G.detM; rw [Matrix.det_isEmpty]; exact one_ne_zero
  intro hh c hsm hcl γ hγ
  have I := (hQ (D.castF e2 hh) c (ccle_castF e2 hcl) _ (hFrel hh hsm)).2.2 γ hγ
  have hσ' : ∀ q : Fin (ph + (n + 1)), (D.ptPerm (h ++ [(n + 1, t)]) (Fin.cast hP.symm q)).val =
      (Formalism.FourierDecayAlt.P.Dx2.SL.sigP (n := n) (D.ptPerm h) q).val := by
    intro q; have := hσ (Fin.cast hP.symm q); simpa using this.symm
  have hd' : ∀ q : Fin (ph + (n + 1)), D.ptDiag (h ++ [(n + 1, t)]) (Fin.cast hP.symm q) =
      Formalism.FourierDecayAlt.P.Dx2.SL.dP (n := n) (D.ptDiag h) t q := by
    intro q; have := hd (Fin.cast hP.symm q); simpa using this.symm
  have I2 := (Formalism.FourierDecayAlt.P.Dx2.SL.phi_transport (k := k) (ρ := ρ) hP.symm _ _ hσ' _ _ hd' (D.castV e1 T.base.z)
    (D.castV e1 T.base.z') (D.castF e2 (D.uwG k r T.base.z T.base.z' (D.cutF T.base χ hh ε)
      (D.ptSize (h ++ [(n + 1, t)])) hi w a)) γ).1 I
  simp only [Formalism.FourierDecayAlt.P.Dx2.SL.castV_castV, Formalism.FourierDecayAlt.P.Dx2.SL.castF_castF] at I2
  exact I2

end Formalism.FourierDecayAlt.P.FormNormSumIdentities

namespace Formalism.FourierDecayAlt.P

open Formalism.FourierDecayAlt

theorem slice_integral_cutoff : Formalism.FourierDecayAlt.P.FormNormSumIdentities.SliceIntCut := by
  obtain ⟨Cp, hCp0, hL⟩ := Formalism.FourierDecayAlt.P.FormNormSumIdentities.levQInt
  intro Wp Wq _ _ _ _ _ _ P0 T w f χ ε i hi hi1 hk2 hfs hR hχ hε p hp e γ hγ
  obtain ⟨R, hR⟩ := hR
  obtain ⟨c, hcl⟩ := Formalism.FourierDecayAlt.P.JFxG.cptInCC_G hfs (Formalism.FourierDecayAlt.P.PBE.isCompact_gN_le P0.k P0.r R)
    (fun g hg hgC => by
      by_contra hne
      exact hgC (hR g hg hne))
    ((16 * Cp) * ((P0.r : ℝ) + 1) ^ 4 * ((w.length : ℝ) * (2 * (P0.r : ℝ) + P0.k + 1) ^ 2 +
      (2 * (P0.r : ℝ) + P0.k + 1) ^ 3))
    (3 * (11 * (w.length * (2 * P0.r + P0.k + 1) ^ 2 + (2 * P0.r + P0.k + 1) ^ 3) + 5))
  have hle : D.ptSize p ≤ P0.r := hp.2 ▸ hi
  have hc : P0.r - i = P0.r - D.ptSize p := by rw [hp.2]
  exact hL (16 * Cp) le_rfl P0.k P0.r Wp Wq T χ _ w.length P0 rfl rfl hk2 hχ le_rfl ε hε i hi hi1 w le_rfl p hc hp
    hle e f c hfs hcl γ hγ

end Formalism.FourierDecayAlt.P
end
end

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.UInvZeroAt
section
noncomputable section

namespace Formalism.FourierDecayAlt.P.PBFV

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt

section Supp

variable {k r : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq]

theorem uInv_zero_at (s : ℂ) (g : B.Mat k r) :
    ∀ (w : List C.Letter) (x : Wd.Ix (Fin w.length) → B.Mat k r → (Wq →L[ℂ] Wp)),
      (∀ e', x e' g = 0) → ∀ e, KB.uInv s w x e g = 0 := by
  intro w
  induction w with
  | nil =>
    intro x hx e
    exact hx e
  | cons l w ih =>
    intro x hx e
    have h0 := ih (fun e' => x (Fin.cons (0 : Fin 2) e')) (fun e' => hx (Fin.cons (0 : Fin 2) e'))
    have h1 := ih (fun e' => x (Fin.cons (1 : Fin 2) e')) (fun e' => hx (Fin.cons (1 : Fin 2) e'))
    show (if e (0 : Fin (w.length + 1)) = 0 then KB.uInv s w (fun e' => x (Fin.cons (0 : Fin 2) e')) (fun a => e a.succ)
      else KB.uInv s w (fun e' => x (Fin.cons (1 : Fin 2) e')) (fun a => e a.succ) +
        (if l.1 then s else (starRingEnd ℂ) s) • KB.uInv s w (fun e' => x (Fin.cons (0 : Fin 2) e')) fun a => e a.succ) g = 0
    split_ifs <;> simp only [Pi.add_apply, Pi.smul_apply, h0, h1, smul_zero, add_zero]

theorem waveG_bs (Bs : B.RealPlaceData k r Wp Wq) (s : ℂ) (w : List C.Letter)
    (x : Wd.Ix (Fin w.length) → B.Mat k r → (Wq →L[ℂ] Wp)) (R : ℝ)
    (hx : ∀ e, ∀ g ∈ B.GV k r, x e g ≠ 0 → B.gN g ≤ R) :
    ∀ e, ∀ g ∈ B.GV k r, KB.waveG Bs s w x e g ≠ 0 → B.gN g ≤ R := by
  intro e g hg hne
  by_contra hR
  apply hne
  have hz : ∀ e', x e' g = 0 := fun e' => by
    by_contra h
    exact hR (hx e' g hg h)
  show P5.fsv s _ • KB.uInv s w x e g = 0
  rw [uInv_zero_at s g w x hz e, smul_zero]

theorem nice_mono {Bs : B.RealPlaceData k r Wp Wq} {F : B.Mat k r → (Wq →L[ℂ] Wp)} {ε ε' : ℝ} (h : ε' ≤ ε)
    (hF : JC.NiceCoef Bs ε F) : JC.NiceCoef Bs ε' F :=
  ⟨hF.1, hF.2.1, fun g hg hne => h.trans (hF.2.2 g hg hne)⟩

theorem common_R {ι : Type*} [Fintype ι] (F : ι → B.Mat k r → (Wq →L[ℂ] Wp))
    (h : ∀ i, ∃ R : ℝ, ∀ g ∈ B.GV k r, F i g ≠ 0 → B.gN g ≤ R) :
    ∃ R : ℝ, ∀ i, ∀ g ∈ B.GV k r, F i g ≠ 0 → B.gN g ≤ R := by
  classical
  choose R hR using h
  refine ⟨∑ i, |R i|, fun i g hg hne => (hR i g hg hne).trans ?_⟩
  exact (le_abs_self _).trans (Finset.single_le_sum (f := fun i => |R i|) (fun i _ => abs_nonneg _) (Finset.mem_univ i))

end Supp

end Formalism.FourierDecayAlt.P.PBFV
end
end

