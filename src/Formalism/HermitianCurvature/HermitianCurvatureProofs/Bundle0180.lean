module

public import Formalism.HermitianCurvature.HermitianCurvatureProofs.PosCoreQ
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0172

@[expose] public section

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.PBGInt
section
open Matrix MeasureTheory Filter Topology
open scoped ContDiff

noncomputable section

namespace Formalism.FourierDecayAlt.P.PBG

open Formalism.FourierDecayAlt Formalism.REAL Formalism.QuantumDeterminants

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

theorem Dmin_castM {k a b : ℕ} (e : a = b) (z z' : Fin (2 * b + k + 1) → ℂ) (g : B.Mat k a) (l : ℕ)
    (hl : l < b + 2) (hl' : l < a + 2) :
    Dmin k b z z' (D.castM e g) ⟨l, hl⟩ = Dmin k a (D.castV e.symm z) (D.castV e.symm z') g ⟨l, hl'⟩ := by
  subst e
  rw [Formalism.FourierDecayAlt.P.Dx2.MN.castM_rfl, Formalism.FourierDecayAlt.P.JCTx6.Link2.castV_self, Formalism.FourierDecayAlt.P.JCTx6.Link2.castV_self]

theorem sliceAt_lincomb (k r : ℕ) (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
    [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq]
    (T : D.LevTower k r Wp Wq) (F : B.Mat k r → (Wq →L[ℂ] Wp)) (hF : KB.CptCoef T.base F)
    (i : ℕ) (hi : i ≤ r) (hi1 : 1 ≤ i) (p : C.LPt) (hp : D.IsLocPt p i)
    {ι : Type} (S : Finset ι) (c : ι → ℂ) (ws : ι → List C.Letter) (as : ∀ q, Wd.Ix (Fin (ws q).length))
    (Hf : B.Mat k r → (Wq →L[ℂ] Wp))
    (hG : ∀ g ∈ B.GV k r, Dmin k r T.base.z T.base.z' g ⟨i, by omega⟩ ≠ 0 →
      Hf g = ∑ q ∈ S, c q • D.uwG k r T.base.z T.base.z' F i hi (ws q) (as q) g)
    (γ : B.Mat k (r - D.ptSize p)) (hγ : γ ∈ B.GV k (r - D.ptSize p)) :
    D.sliceAt k r T.base.z T.base.z' Hf p γ =
      ∑ q ∈ S, c q • D.sliceAt k r T.base.z T.base.z' (D.uwG k r T.base.z T.base.z' F i hi (ws q) (as q)) p γ := by
  revert γ

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
  intro γ hγ
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

  have hS : ∀ Gw : B.Mat k r → (Wq →L[ℂ] Wp), D.sliceAt k r T.base.z T.base.z' Gw (h ++ [(n + 1, t)]) γ =
      U.PhiFun (p := ph + (n + 1)) (s := 0) k ρ (Formalism.FourierDecayAlt.P.Dx2.SL.sigP (D.ptPerm h))
        (Formalism.FourierDecayAlt.P.Dx2.SL.dP (D.ptDiag h) t) (D.castV (by omega) T.base.z) (D.castV (by omega) T.base.z')
        (D.castF (by omega) Gw) (fun a => a.elim0) γ := by
    intro Gw
    obtain ⟨-, hT2⟩ := Formalism.FourierDecayAlt.P.Dx2.SL.phi_transport (k := k) (ρ := ρ) hP _ _ hσ _ _ hd
      (D.castV (by omega) T.base.z) (D.castV (by omega) T.base.z') (D.castF (by omega) Gw) γ
    unfold D.sliceAt
    rw [dite_eq_left (by omega), hT2]
    simp only [Formalism.FourierDecayAlt.P.Dx2.SL.castV_castV, Formalism.FourierDecayAlt.P.Dx2.SL.castF_castF]
  have e1 : r = ph + (n + 1) + ρ := hsum.symm
  have e2 : ph + (n + 1) + ρ = r := hsum
  have hj1 : 1 ≤ ph + (n + 1) := by omega
  obtain ⟨hFs, ⟨R, hR⟩, ⟨ε, hε, hGε⟩⟩ := hF

  have hcut : ∀ x ∈ B.GV k (ph + (n + 1) + ρ), D.castF e2 F x =
      ((Formalism.FourierDecayAlt.P.Topx2.chi0 (Gf k (ph + (n + 1) + ρ) (D.castV e1 T.base.z) (D.castV e1 T.base.z') x / ε) : ℝ) : ℂ) •
        D.castF e2 F x := by
    intro x hx
    by_cases h0 : D.castF e2 F x = 0
    · rw [h0, smul_zero]
    · have hxG := Formalism.FourierDecayAlt.P.PBE.castM_GV e2 hx
      have h1 : ε ≤ Gf k r T.base.z T.base.z' (D.castM e2 x) := hGε _ hxG h0
      rw [show Gf k (ph + (n + 1) + ρ) (D.castV e1 T.base.z) (D.castV e1 T.base.z') x =
        Gf k r T.base.z T.base.z' (D.castM e2 x) from Formalism.FourierDecayAlt.P.PBE.Gf_castM e2 _ _ x]
      rw [Formalism.FourierDecayAlt.P.Topx2.base_cutoff_is_truncation.2.2 _ ((one_le_div hε).2 h1)]
      simp
  have hfA : ∀ (A₀ : ℝ) (m : ℕ), B.InCC A₀ m (D.castF e2 F) := fun A₀ m =>
    Formalism.FourierDecayAlt.P.JCTx6.Link2.inCC_castF e2 (Formalism.FourierDecayAlt.P.JFxG.cptInCC_G hFs (Formalism.FourierDecayAlt.P.PBE.isCompact_gN_le k r R)
      (fun g hg hgC => by
        by_contra h0
        exact hgC (hR g hg h0)) A₀ m)

  obtain ⟨Cq, hCq0, hCq⟩ := Formalism.FourierDecayAlt.P.PBE.posCoreQ
  have hInt : ∀ (w : List C.Letter) (a : Wd.Ix (Fin w.length)), Integrable
      (fun ξ : U.Xi k (ph + (n + 1)) 0 ρ (Formalism.FourierDecayAlt.P.Dx2.SL.sigP (D.ptPerm h)) =>
        U.psiStar (p := ph + (n + 1)) (s := 0) k ρ (Formalism.FourierDecayAlt.P.Dx2.SL.sigP (D.ptPerm h))
          (D.castV e1 T.base.z) (D.castV e1 T.base.z') ξ •
          D.castF e2 (D.uwG k r T.base.z T.base.z' F (D.ptSize (h ++ [(n + 1, t)])) hi w a)
            (U.gaXi (p := ph + (n + 1)) (s := 0) k ρ (Formalism.FourierDecayAlt.P.Dx2.SL.sigP (D.ptPerm h))
              (Formalism.FourierDecayAlt.P.Dx2.SL.dP (D.ptDiag h) t) ξ (fun a => a.elim0) γ))
      (U.muXi k (ph + (n + 1)) 0 ρ (Formalism.FourierDecayAlt.P.Dx2.SL.sigP (D.ptPerm h))) := by
    intro w a
    set Gw := D.uwG k r T.base.z T.base.z' F (D.ptSize (h ++ [(n + 1, t)])) hi w a with hGw
    obtain ⟨Θ, hΘ, hΘF⟩ := Formalism.FourierDecayAlt.P.JCTx6.Let.lettersDD k (ph + (n + 1)) ρ Wp Wq (D.castV e1 T.base.z)
      (D.castV e1 T.base.z') (by omega) w a hj1
    have hG1 : D.castF e2 Gw = D.uwG k (ph + (n + 1) + ρ) (D.castV e1 T.base.z) (D.castV e1 T.base.z')
        (D.castF e2 F) (ph + (n + 1)) (by omega) w a := by
      rw [hGw, Formalism.FourierDecayAlt.P.JCTx6.Link2.castF_uwG e2 _ _ _ _ hi (by omega)]
      exact Formalism.FourierDecayAlt.P.JCTx6.Link2.uwG_level _ _ _ hP _ _ w a
    have hFrel : ∀ g ∈ B.GV k (ph + (n + 1) + ρ), U.DjU k (ph + (n + 1)) ρ g ≠ 0 →
        D.castF e2 Gw g = B.opApply Θ (fun x => ((Formalism.FourierDecayAlt.P.Topx2.chi0 (Gf k (ph + (n + 1) + ρ)
          (D.castV e1 T.base.z) (D.castV e1 T.base.z') x / ε) : ℝ) : ℂ) • D.castF e2 F x) g := by
      intro g hg hD
      rw [hG1, hΘF _ (Formalism.FourierDecayAlt.P.JCTx6.Link2.ckOn_castF e2 hFs) g hg hD]
      exact Formalism.FourierDecayAlt.P.PBE.opApply_congrGV Θ hcut g hg
    set o := w.length * (ph + (n + 1))
    set κ := w.length * (ph + (n + 1)) + w.length * (ph + (n + 1)) ^ 2
    set As : ℕ := o + (κ + (ph + (n + 1)) * o) + (2 * (ph + (n + 1) + ρ) + k + 1) ^ 3 with hAs
    obtain ⟨cc, hcc⟩ := hfA (Cq * (((ph + (n + 1) + ρ : ℕ) : ℝ) + 1) ^ 4 * (As : ℝ)) (3 * As)
    obtain ⟨ε', K, -, -, hmain⟩ := hCq k ph n ρ Wp Wq (D.castV e1 T.base.z) (D.castV e1 T.base.z')
      (Formalism.FourierDecayAlt.P.Dx1.SN.castV_inWb e1 _ T.base.z_mem) (Formalism.FourierDecayAlt.P.Dx1.SN.castV_inWb e1 _ T.base.z'_mem)
      Θ o κ hΘ Formalism.FourierDecayAlt.P.Topx2.chi0 (Cq * (((ph + (n + 1) + ρ : ℕ) : ℝ) + 1) ^ 4 * (As : ℝ)) ε
      Formalism.FourierDecayAlt.P.Topx2.base_cutoff_is_truncation hε (D.ptPerm h) (D.ptDiag h) t hd0 ht As 0 0
      (by omega) (by omega) (by omega) (by omega) (by positivity) le_rfl
    exact (hmain (D.castF e2 F) cc hcc (D.castF e2 Gw) hFrel).2.2 γ hγ

  have hZ0 : G.detM (fun a => a.elim0 : G.Mat 0) ≠ 0 := by
    unfold G.detM; rw [Matrix.det_isEmpty]; exact one_ne_zero
  have hdh0 : (U.hMat (Formalism.FourierDecayAlt.P.Dx2.SL.sigP (n := n) (D.ptPerm h)) (Formalism.FourierDecayAlt.P.Dx2.SL.dP (D.ptDiag h) t)).det ≠ 0 :=
    Formalism.FourierDecayAlt.P.Ux10.det_hMat_ne _ _ hdP
  have hpt : ∀ ξ : U.Xi k (ph + (n + 1)) 0 ρ (Formalism.FourierDecayAlt.P.Dx2.SL.sigP (D.ptPerm h)),
      D.castF e2 Hf (U.gaXi (p := ph + (n + 1)) (s := 0) k ρ (Formalism.FourierDecayAlt.P.Dx2.SL.sigP (D.ptPerm h))
          (Formalism.FourierDecayAlt.P.Dx2.SL.dP (D.ptDiag h) t) ξ (fun a => a.elim0) γ) =
        ∑ q ∈ S, c q • D.castF e2 (D.uwG k r T.base.z T.base.z' F (D.ptSize (h ++ [(n + 1, t)])) hi (ws q) (as q))
          (U.gaXi (p := ph + (n + 1)) (s := 0) k ρ (Formalism.FourierDecayAlt.P.Dx2.SL.sigP (D.ptPerm h))
            (Formalism.FourierDecayAlt.P.Dx2.SL.dP (D.ptDiag h) t) ξ (fun a => a.elim0) γ) := by
    intro ξ
    set g := U.gaXi (p := ph + (n + 1)) (s := 0) k ρ (Formalism.FourierDecayAlt.P.Dx2.SL.sigP (D.ptPerm h))
      (Formalism.FourierDecayAlt.P.Dx2.SL.dP (D.ptDiag h) t) ξ (fun a => a.elim0) γ with hg
    have hgG : g ∈ B.GV k (ph + (n + 1) + 0 + ρ) :=
      Formalism.FourierDecayAlt.P.Ux10.gaXi_mem Formalism.FourierDecayAlt.P.slice_membership Formalism.FourierDecayAlt.P.radical_parametrisation _ _ hdP ξ _ hZ0 hγ
    have hDj : U.DjU k (ph + (n + 1) + 0) ρ g = _ :=
      Formalism.FourierDecayAlt.P.Ux10.DjU_gaXi Formalism.FourierDecayAlt.P.hat_z_on_slice _ _ ξ _ γ
    have hD : Dmin k r T.base.z T.base.z' (D.castM e2 g) ⟨D.ptSize (h ++ [(n + 1, t)]), by omega⟩ ≠ 0 := by
      rw [Dmin_castM e2 _ _ g _ _ (by omega)]
      have e3 : (⟨D.ptSize (h ++ [(n + 1, t)]), by omega⟩ : Fin (ph + (n + 1) + ρ + 2)) = ⟨ph + (n + 1), by omega⟩ :=
        Fin.ext hP
      rw [e3, Formalism.FourierDecayAlt.P.hat_z_minimum_degree k (ph + (n + 1)) ρ]
      show U.DjU k (ph + (n + 1) + 0) ρ g ≠ 0
      rw [hDj]
      exact mul_ne_zero hdh0 hZ0
    show Hf (D.castM e2 g) = ∑ q ∈ S, c q • D.uwG k r T.base.z T.base.z' F _ hi (ws q) (as q) (D.castM e2 g)
    exact hG _ (Formalism.FourierDecayAlt.P.PBE.castM_GV e2 hgG) hD
  rw [hS Hf]
  simp_rw [hS]
  unfold U.PhiFun
  have key : ∀ q ∈ S, Integrable (fun ξ : U.Xi k (ph + (n + 1)) 0 ρ (Formalism.FourierDecayAlt.P.Dx2.SL.sigP (D.ptPerm h)) =>
      c q • (U.psiStar (p := ph + (n + 1)) (s := 0) k ρ (Formalism.FourierDecayAlt.P.Dx2.SL.sigP (D.ptPerm h))
          (D.castV e1 T.base.z) (D.castV e1 T.base.z') ξ •
          D.castF e2 (D.uwG k r T.base.z T.base.z' F (D.ptSize (h ++ [(n + 1, t)])) hi (ws q) (as q))
            (U.gaXi (p := ph + (n + 1)) (s := 0) k ρ (Formalism.FourierDecayAlt.P.Dx2.SL.sigP (D.ptPerm h))
              (Formalism.FourierDecayAlt.P.Dx2.SL.dP (D.ptDiag h) t) ξ (fun a => a.elim0) γ)))
      (U.muXi k (ph + (n + 1)) 0 ρ (Formalism.FourierDecayAlt.P.Dx2.SL.sigP (D.ptPerm h))) :=
    fun q _ => MeasureTheory.Integrable.smul (c q) (hInt (ws q) (as q))
  rw [Finset.sum_congr rfl (fun q _ => (integral_smul (c q) _).symm), ← integral_finsetSum S key]
  refine integral_congr_ae (Filter.Eventually.of_forall fun ξ => ?_)
  dsimp only
  rw [hpt ξ, Finset.smul_sum]
  refine Finset.sum_congr rfl fun q _ => ?_
  rw [smul_comm]

end Formalism.FourierDecayAlt.P.PBG
end
end

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.RadialTransformSquareIntegrable
section
open MeasureTheory

noncomputable section

namespace Formalism.FourierDecayAlt.P5.HerC

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.Wd Formalism.FourierDecayAlt.P5 Formalism.FourierDecayAlt.P5.HerA Formalism.FourierDecayAlt.P5.HerB
attribute [-instance] Formalism.BasicNotions.Examples₂.instIsEmptyClsEmptyColumnChain

section L2

variable {k r : ℕ} {z z' : Fin (2 * r + k + 1) → ℂ} {Wp Wq : Type} [NormedAddCommGroup Wp]
  [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp]
  [FiniteDimensional ℂ Wq] {π : Mx k r → (Wp →L[ℂ] Wp)} {π' : Mx k r → (Wq →L[ℂ] Wq)}

def wt0 (c' : Cf r 0) : ℂ := ((∏ l, ‖c' l‖ ^ (-2 : ℤ) : ℝ) : ℂ)

theorem level_zero_weight_measurable : Measurable (wt0 (r := r)) := by
  unfold wt0
  have e : ∀ x : ℝ, x ^ (-2 : ℤ) = (x ^ 2)⁻¹ := fun x => by rw [zpow_neg]; norm_cast
  simp_rw [e]
  exact Complex.measurable_ofReal.comp
    (Finset.measurable_prod _ fun l _ => ((measurable_norm.comp (measurable_pi_apply l)).pow_const 2).inv)

def LevelZeroSquareIntegrable (μ : Measure (Mt k r)) (u : RadSp k r z z' π π') (c : Fin r → ℂ) : Prop :=
  Integrable (fun c' : Cf r 0 => wt0 c' * pairAt μ u u (glue 0 c c'))

theorem pairAt_meas0 (μ : Measure (Mt k r)) [SFinite μ] (u v : RadSp k r z z' π π') (c : Fin r → ℂ) :
    StronglyMeasurable (fun c' : Cf r 0 => pairAt μ u v (glue 0 c c')) :=
  (pair_measurable c u v).stronglyMeasurable.integral_prod_right'

theorem hsInner_self_ofReal (A : Wq →L[ℂ] Wp) : B.hsInner A A = ((‖B.hsVec A‖ ^ 2 : ℝ) : ℂ) := by
  unfold B.hsInner
  rw [inner_self_eq_norm_sq_to_K (𝕜 := ℂ) (B.hsVec A)]
  push_cast
  rfl

theorem norm_pairAt_self (μ : Measure (Mt k r)) (u : RadSp k r z z' π π') (c : Fin r → ℂ) :
    ‖pairAt μ u u c‖ = ∫ g : Mt k r, ‖B.hsInner ((u : Fn k r (Wq →L[ℂ] Wp)) c (Matrix.of g))
      ((u : Fn k r (Wq →L[ℂ] Wp)) c (Matrix.of g))‖ ∂μ := by
  unfold pairAt
  simp_rw [hsInner_self_ofReal]
  rw [integral_complex_ofReal, Complex.norm_real, Real.norm_of_nonneg (integral_nonneg fun g => by positivity)]
  refine integral_congr_ae (Filter.Eventually.of_forall fun g => ?_)
  simp only [Complex.norm_real, Real.norm_of_nonneg (sq_nonneg _)]

theorem norm_pairAt_le (μ : Measure (Mt k r)) (hμ : B.IsHaarOn (Glev k r (Fin.last r)) μ) {u v : RadSp k r z z' π π'}
    (hu : u ∈ lcSub k r z z' π π') (hv : v ∈ lcSub k r z z' π π') (c : Fin r → ℂ) :
    ‖pairAt μ u v c‖ ≤ ‖pairAt μ u u c‖ + ‖pairAt μ v v c‖ := by
  rw [norm_pairAt_self, norm_pairAt_self]
  unfold pairAt
  refine (norm_integral_le_integral_norm _).trans ?_
  rw [← integral_add (int_lc μ hμ hu hu c).norm (int_lc μ hμ hv hv c).norm]
  exact integral_mono (int_lc μ hμ hu hv c).norm ((int_lc μ hμ hu hu c).norm.add (int_lc μ hμ hv hv c).norm)
    fun g => norm_hs_le _ _

theorem int_cross (μ : Measure (Mt k r)) [SFinite μ] (hμ : B.IsHaarOn (Glev k r (Fin.last r)) μ)
    {u v : RadSp k r z z' π π'} (hu : u ∈ lcSub k r z z' π π') (hv : v ∈ lcSub k r z z' π π') (c : Fin r → ℂ)
    (Iu : LevelZeroSquareIntegrable μ u c) (Iv : LevelZeroSquareIntegrable μ v c) :
    Integrable (fun c' : Cf r 0 => wt0 c' * pairAt μ u v (glue 0 c c')) := by
  refine (Iu.norm.add Iv.norm).mono'
    (level_zero_weight_measurable.aestronglyMeasurable.mul (pairAt_meas0 μ u v c).aestronglyMeasurable)
    (Filter.Eventually.of_forall fun c' => ?_)
  show ‖wt0 c' * pairAt μ u v (glue 0 c c')‖ ≤
    ‖wt0 c' * pairAt μ u u (glue 0 c c')‖ + ‖wt0 c' * pairAt μ v v (glue 0 c c')‖
  rw [norm_mul, norm_mul, norm_mul, ← mul_add]
  exact mul_le_mul_of_nonneg_left (norm_pairAt_le μ hμ hu hv _) (norm_nonneg _)

theorem pairAt_zero_zero (μ : Measure (Mt k r)) (c : Fin r → ℂ) :
    pairAt μ (0 : RadSp k r z z' π π') 0 c = 0 := by
  unfold pairAt
  simp [hsInner_zero_left]

theorem pairAt_add_add (μ : Measure (Mt k r)) (hμ : B.IsHaarOn (Glev k r (Fin.last r)) μ) {u v : RadSp k r z z' π π'}
    (hu : u ∈ lcSub k r z z' π π') (hv : v ∈ lcSub k r z z' π π') (c : Fin r → ℂ) :
    pairAt μ (u + v) (u + v) c = pairAt μ u u c + pairAt μ u v c + pairAt μ v u c + pairAt μ v v c := by
  unfold pairAt
  have e : ∀ g : Mt k r, B.hsInner (((u + v : RadSp k r z z' π π') : Fn k r (Wq →L[ℂ] Wp)) c (Matrix.of g))
      (((u + v : RadSp k r z z' π π') : Fn k r (Wq →L[ℂ] Wp)) c (Matrix.of g)) =
      B.hsInner ((u : Fn k r (Wq →L[ℂ] Wp)) c (Matrix.of g)) ((u : Fn k r (Wq →L[ℂ] Wp)) c (Matrix.of g)) +
      B.hsInner ((u : Fn k r (Wq →L[ℂ] Wp)) c (Matrix.of g)) ((v : Fn k r (Wq →L[ℂ] Wp)) c (Matrix.of g)) +
      B.hsInner ((v : Fn k r (Wq →L[ℂ] Wp)) c (Matrix.of g)) ((u : Fn k r (Wq →L[ℂ] Wp)) c (Matrix.of g)) +
      B.hsInner ((v : Fn k r (Wq →L[ℂ] Wp)) c (Matrix.of g)) ((v : Fn k r (Wq →L[ℂ] Wp)) c (Matrix.of g)) := by
    intro g
    show B.hsInner ((u : Fn k r (Wq →L[ℂ] Wp)) c (Matrix.of g) + (v : Fn k r (Wq →L[ℂ] Wp)) c (Matrix.of g))
      ((u : Fn k r (Wq →L[ℂ] Wp)) c (Matrix.of g) + (v : Fn k r (Wq →L[ℂ] Wp)) c (Matrix.of g)) = _
    rw [Formalism.FourierDecayAlt.P.B6.hsInner_add_left, Formalism.FourierDecayAlt.P.B6.hsInner_add_right, Formalism.FourierDecayAlt.P.B6.hsInner_add_right]
    ring
  have e2 : (∫ g : Mt k r, B.hsInner (((u + v : RadSp k r z z' π π') : Fn k r (Wq →L[ℂ] Wp)) c (Matrix.of g))
      (((u + v : RadSp k r z z' π π') : Fn k r (Wq →L[ℂ] Wp)) c (Matrix.of g)) ∂μ) =
      ∫ g, ((fun g : Mt k r => B.hsInner ((u : Fn k r (Wq →L[ℂ] Wp)) c (Matrix.of g)) ((u : Fn k r (Wq →L[ℂ] Wp)) c (Matrix.of g))) +
        (fun g : Mt k r => B.hsInner ((u : Fn k r (Wq →L[ℂ] Wp)) c (Matrix.of g)) ((v : Fn k r (Wq →L[ℂ] Wp)) c (Matrix.of g))) +
        (fun g : Mt k r => B.hsInner ((v : Fn k r (Wq →L[ℂ] Wp)) c (Matrix.of g)) ((u : Fn k r (Wq →L[ℂ] Wp)) c (Matrix.of g))) +
        (fun g : Mt k r => B.hsInner ((v : Fn k r (Wq →L[ℂ] Wp)) c (Matrix.of g)) ((v : Fn k r (Wq →L[ℂ] Wp)) c (Matrix.of g)))) g ∂μ := by
    congr 1; funext g; rw [e g]; rfl
  rw [e2, integral_add' (((int_lc μ hμ hu hu c).add (int_lc μ hμ hu hv c)).add (int_lc μ hμ hv hu c))
      (int_lc μ hμ hv hv c),
    integral_add' ((int_lc μ hμ hu hu c).add (int_lc μ hμ hu hv c)) (int_lc μ hμ hv hu c),
    integral_add' (int_lc μ hμ hu hu c) (int_lc μ hμ hu hv c)]


variable (k r z z' π π') in
def squareIntegrableSmoothSubmoduleGL (μ : Measure (Mt k r)) [SFinite μ] (hμ : B.IsHaarOn (Glev k r (Fin.last r)) μ) :
    Submodule ℂ (RadSp k r z z' π π') where
  carrier := {u | u ∈ lcSub k r z z' π π' ∧ ∀ c, LevelZeroSquareIntegrable μ u c}
  zero_mem' := ⟨(lcSub k r z z' π π').zero_mem, fun c => by
    unfold LevelZeroSquareIntegrable
    simp only [pairAt_zero_zero, mul_zero]
    exact integrable_zero _ _ _⟩
  add_mem' := by
    rintro u v ⟨hu, Iu⟩ ⟨hv, Iv⟩
    refine ⟨(lcSub k r z z' π π').add_mem hu hv, fun c => ?_⟩
    unfold LevelZeroSquareIntegrable
    simp_rw [pairAt_add_add μ hμ hu hv, mul_add]
    exact (((Iu c).add (int_cross μ hμ hu hv c (Iu c) (Iv c))).add
      (int_cross μ hμ hv hu c (Iv c) (Iu c))).add (Iv c)
  smul_mem' := by
    rintro a u ⟨hu, Iu⟩
    refine ⟨(lcSub k r z z' π π').smul_mem a hu, fun c => ?_⟩
    unfold LevelZeroSquareIntegrable
    simp_rw [pairAt_smul_left, pairAt_smul_right]
    have e : (fun c' : Cf r 0 => wt0 c' * (a * ((starRingEnd ℂ) a * pairAt μ u u (glue 0 c c')))) =
        fun c' => (a * (starRingEnd ℂ) a) * (wt0 c' * pairAt μ u u (glue 0 c c')) := by
      funext c'; ring
    rw [e]
    exact (Iu c).const_mul _

theorem unimodular_multiplier_preserves_L2 (μ : Measure (Mt k r)) [SFinite μ] (hμ : B.IsHaarOn (Glev k r (Fin.last r)) μ)
    {W : Module.End ℂ (RadSp k r z z' π π')} {m : (Fin r → ℂ) → Mx k r → ℂ} (hW : multiplicationOperator W m)
    (hm : ∀ c g, ‖m c g‖ = 1) : ∀ u ∈ squareIntegrableSmoothSubmoduleGL k r z z' π π' μ hμ, W u ∈ squareIntegrableSmoothSubmoduleGL k r z z' π π' μ hμ := by
  rintro u ⟨hu, Iu⟩
  refine ⟨mul_lc hW u hu, fun c => ?_⟩
  have e : ∀ c0, pairAt μ (W u) (W u) c0 = pairAt μ u u c0 := by
    intro c0
    unfold pairAt
    refine integral_congr_ae (Filter.Eventually.of_forall fun g => ?_)
    show B.hsInner ((W u : Fn k r (Wq →L[ℂ] Wp)) c0 (Matrix.of g)) ((W u : Fn k r (Wq →L[ℂ] Wp)) c0 (Matrix.of g)) = _
    rw [hW u c0 (Matrix.of g), hsInner_smul_left', hsInner_smul_right', ← mul_assoc, Complex.mul_conj,
      Complex.normSq_eq_norm_sq, hm]
    simp
  unfold LevelZeroSquareIntegrable
  simp_rw [e]
  exact Iu c

theorem norm_fsv (s t : ℂ) : ‖fsv s t‖ = 1 := by
  unfold fsv
  rw [Complex.norm_exp]
  have : (s * t - (starRingEnd ℂ) s * (starRingEnd ℂ) t).re = 0 := by
    rw [← map_mul, Complex.sub_re, Complex.conj_re, sub_self]
  rw [this, Real.exp_zero]

end L2

section Classes

variable {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] {S : Type} [Fintype S] [DecidableEq S]

theorem radial_transform_square_integrable (P : M.Par) (z z' : Fin (2 * P.r + P.k + 1) → ℂ) (π : Mx P.k P.r → (Wp →L[ℂ] Wp))
    (π' : Mx P.k P.r → (Wq →L[ℂ] Wq)) (μ : Measure (Mt P.k P.r)) [SFinite μ]
    (hμ : B.IsHaarOn (Glev P.k P.r (Fin.last P.r)) μ) (D : B.RealPlaceData P.k P.r Wp Wq) (hP : IsPlace P z z' π π')
    (hz : D.z = z) (hz' : D.z' = z') (hπ : D.π = π) (hπ' : D.π' = π') (F : Mx P.k P.r → (Wq →L[ℂ] Wp))
    (hF : JFOKCpt P z z' F) (Φ : RadSp P.k P.r z z' π π') (hΦ : IsRadJF P z z' π π' D F Φ) :
    Φ ∈ squareIntegrableSmoothSubmoduleGL P.k P.r z z' π π' μ hμ := by
  refine ⟨jfCptLocAll Wp Wq P z z' π π' D F Φ hP hz hz' hπ hπ' hF hΦ, fun c => ?_⟩
  subst hz hz' hπ hπ'
  have h := level_zero_form_integrable_compact (S := Empty) D μ hμ (fun _ => F) (fun _ => F) (fun _ => Φ) (fun _ => Φ)
    (fun _ => hF.1.1) (fun _ => hF.1.1) (fun _ => hΦ) (fun _ => hΦ) c
  unfold LevelZeroSquareIntegrable
  simpa [wt0] using h

theorem compact_kernel_le_L2 (P : M.Par) (z z' : Fin (2 * P.r + P.k + 1) → ℂ) (π : Mx P.k P.r → (Wp →L[ℂ] Wp))
    (π' : Mx P.k P.r → (Wq →L[ℂ] Wq)) (μ : Measure (Mt P.k P.r)) [SFinite μ]
    (hμ : B.IsHaarOn (Glev P.k P.r (Fin.last P.r)) μ) (L : R.LevelData (Pr (RadSp P.k P.r z z' π π')) P.r)
    (st : Fr.Start (Pr (RadSp P.k P.r z z' π π'))) (l0 : ℕ) (D : B.RealPlaceData P.k P.r Wp Wq) (hP : IsPlace P z z' π π')
    (hz : D.z = z) (hz' : D.z' = z') (hπ : D.π = π) (hπ' : D.π' = π') :
    herKc S P z z' π π' L st l0 D 0 ≤ squareIntegrableSmoothSubmoduleGL P.k P.r z z' π π' μ hμ := by
  refine Submodule.span_le.mpr fun Φ hΦ => ?_
  have key : ∀ (i : Fin (P.r + 1)) (Ψ : RadSp P.k P.r z z' π π'), HerGenC S P z z' π π' L st l0 D i Ψ →
      i = 0 → Ψ ∈ squareIntegrableSmoothSubmoduleGL P.k P.r z z' π π' μ hμ := by
    intro i Ψ h
    induction h with
    | jf F Φ hF hΦ => exact fun _ => radial_transform_square_integrable P z z' π π' μ hμ D hP hz hz' hπ hπ' F hF Φ hΦ
    | slice l w a b Φ _ _ _ => exact fun h => absurd h (Fin.succ_ne_zero l)
    | waveC l w s Wv Wv' a b Φ _ h1 h2 _ ih =>
      intro h
      have hm : (Vw (mkP Wv Wv') s w : SlopeTestRemainingChoices S (Pr (RadSp P.k P.r z z' π π'))) ∈
          entSub (presAlg (squareIntegrableSmoothSubmoduleGL P.k P.r z z' π π' μ hμ)) :=
        (entSub _).mul_mem (Formalism.FourierDecayAlt.P5.HerA.io_mem (show mkP Wv Wv' ∈ presAlg _ from
          ⟨unimodular_multiplier_preserves_L2 μ hμ h1 (fun c _ => norm_fsv _ _), unimodular_multiplier_preserves_L2 μ hμ h2 (fun c _ => norm_fsv _ _)⟩)) (UUiw_mem s w)
      exact (hm a b).1 Φ (ih h)
    | waveZ w s Wv Wv' a b Φ _ h1 h2 _ ih =>
      intro h
      have hm : (Vw (mkP Wv Wv') s w : SlopeTestRemainingChoices S (Pr (RadSp P.k P.r z z' π π'))) ∈
          entSub (presAlg (squareIntegrableSmoothSubmoduleGL P.k P.r z z' π π' μ hμ)) :=
        (entSub _).mul_mem (Formalism.FourierDecayAlt.P5.HerA.io_mem (show mkP Wv Wv' ∈ presAlg _ from
          ⟨unimodular_multiplier_preserves_L2 μ hμ h1 (fun _ _ => norm_fsv _ _), unimodular_multiplier_preserves_L2 μ hμ h2 (fun _ _ => norm_fsv _ _)⟩)) (UUiw_mem s w)
      exact (hm a b).1 Φ (ih h)
  exact key 0 Φ hΦ rfl

end Classes

end Formalism.FourierDecayAlt.P5.HerC
end
end

