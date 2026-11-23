module

public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0219
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.LiftClosedUnderOperations
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.LevelFormSesquilinearFiniteClass
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0142
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0218
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0220
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0200
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0215

@[expose] public section

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.MinorCellOfPartsAlt
section
open Matrix

noncomputable section

namespace Formalism.FourierDecayAlt.P

open Formalism.FourierDecayAlt Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.P.Qx5 Formalism.FourierDecayAlt.P.Qx2 Formalism.FourierDecayAlt.P.PBN Formalism.FourierDecayAlt.P.PBN.MC

theorem minor_cell_of_parts : PBN.MinorCellOfParts := by
  intro hRR hLR hTC hGP k r Wp Wq _ _ _ _ _ _ Bs F y hF x hx
  set D := OmPlus k r Bs.z Bs.z' with hDdef
  have hD : IsOpen D := Formalism.FourierDecayAlt.P.SmoothnessOnGoodSet.isOpen_OmPlus Bs.z Bs.z'
  obtain ⟨ε, hε, hn⟩ := Formalism.FourierDecayAlt.P.TLB.nice_of_cpt hF
  obtain ⟨hf, hLf, hRf, -⟩ := Formalism.FourierDecayAlt.P.bessel_function_finite_class k r Wp Wq Bs F ε hε hn
  have h1N : (1 : Mx k r) ∈ Nlev k r 0 :=
    ⟨(Formalism.QuantumDeterminants.unipotent_subgroup_holds k r).1, by simp [Glev, UH]⟩
  have hN : ∀ g ∈ Glev k r 0 ∩ D, ∀ n ∈ Nlev k r 0, n * g ∈ D := by
    intro g hg n hn
    have hDom := Formalism.FourierDecayAlt.P.JCx2.rma_isDom_omPlus (k := k) (r := r) Bs.z_mem Bs.z'_mem
    have := hDom.2 g hg n ⟨1, Formalism.FourierDecayAlt.P.Qx8.uw_one Bs.z, n, hn, (one_mul n).symm⟩ 1
      ⟨1, Formalism.FourierDecayAlt.P.Qx8.uw_one Bs.z', 1, h1N, (one_mul 1).symm⟩
    rwa [Matrix.mul_one] at this
  set v₀ : VS k r 0 D (Wq →L[ℂ] Wp) := ⟨cut k r 0 D (B.JF Bs F), cut_mem hD hf⟩ with hv₀
  have hcellB : ∀ c ∈ OmX r, wCell k r (Fin.last r) c * x.2 ∈ C6.bigPos Bs := fun c hc =>
    (Formalism.FourierDecayAlt.P.big_cell_values k r Wp Wq Bs (c, x.2) ⟨hc, hx.2.1, hx.2.2⟩).1
  have hcell : ∀ c ∈ OmX r, wCell k r (Fin.last r) c * x.2 ∈ Glev k r 0 ∩ D := by
    intro c hc
    have h := hcellB c hc
    exact ⟨Formalism.FourierDecayAlt.P.OrbitalIntegralIdentities.glev0 h.1, fun l _ => h.2.2 l (by simp), h.2.1⟩
  have hdiff : ∀ x' : SA (E := Wq →L[ℂ] Wp) hD, ∀ c ∈ OmX r, DifferentiableAt ℝ
      (fun c' => ((x' : Module.End ℂ (VS k r 0 D (Wq →L[ℂ] Wp))) v₀ : Mx k r → (Wq →L[ℂ] Wp))
        (wCell k r (Fin.last r) c' * x.2)) c :=
    fun x' c hc => cell_diff Bs ((x' : Module.End ℂ (VS k r 0 D (Wq →L[ℂ] Wp))) v₀).2.1 hx.2.1 hx.2.2 hc
  have hWS : ∀ x' : SA (E := Wq →L[ℂ] Wp) hD,
      resW ((x' : Module.End ℂ (VS k r 0 D (Wq →L[ℂ] Wp))) v₀ : Mx k r → (Wq →L[ℂ] Wp)) x.2 ∈ WSm r (Wq →L[ℂ] Wp) :=
    fun x' => resG_wsm Bs ((x' : Module.End ℂ (VS k r 0 D (Wq →L[ℂ] Wp))) v₀).2.1 hx.2.1 hx.2.2
  have hcl := claim hD v₀ x.2 y hRR hLR hTC hGP Bs.z Bs.z' Bs.z_mem Bs.z'_mem hN hf hLf hRf rfl hx.2.1 hcell hdiff hWS
    r le_rfl 1 (Subalgebra.one_mem _) x.1 hx.1
  rw [mul_one] at hcl

  have eR : Q.crd (Q.vAB r y r).1 (Q.resG k r (Fin.last r) (B.JF Bs F)) x.1 x.2 =
      (Q.vAB r y r).1 (fun c' => Q.resG k r (Fin.last r)
        (((1 : SA (E := Wq →L[ℂ] Wp) hD) : Module.End ℂ (VS k r 0 D (Wq →L[ℂ] Wp))) v₀ : Mx k r → (Wq →L[ℂ] Wp)) c' x.2) x.1 := by
    have hloc : ∀ (i : ℕ) (f₁ f₂ : (Fin r → ℂ) → (Wq →L[ℂ] Wp)),
        (∀ c ∈ OmX r, f₁ c = f₂ c) → ∀ c ∈ OmX r,
        (Q.vAB r y i).1 f₁ c = (Q.vAB r y i).1 f₂ c ∧
        (Q.vAB r y i).2 f₁ c = (Q.vAB r y i).2 f₂ c := by
      intro i
      induction i with
      | zero => intro f₁ f₂ h c hc; exact ⟨h c hc, rfl⟩
      | succ i ih =>
        intro f₁ f₂ h c hc
        have hih := ih f₁ f₂ h
        by_cases hi : i < r
        · simp only [Q.vAB, dif_pos hi]
          refine ⟨?_, ?_⟩
          · simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, cOp]
            have hev : (Q.vAB r y i).1 f₁ =ᶠ[nhds c] (Q.vAB r y i).1 f₂ := by
              filter_upwards [(Formalism.FourierDecayAlt.P.Qx3.isOpen_OmX r).mem_nhds hc] with c' hc' using (hih c' hc').1
            simp only [pOp, wirt, if_pos hc, hev.fderiv_eq, (hih c hc).1, (hih c hc).2]
          · simp only [ciOp, (hih c hc).1]
        · simp only [Q.vAB, dif_neg hi]
          exact hih c hc
    refine (hloc r _ _ (fun c' hc' => ?_) x.1 hx.1).1
    rw [resG_last, resG_last]
    congr 1
    exact (cut_of_mem _ (hcell c' hc')).symm
  rw [eR, ← hcl, resG_last, resG_last]
  congr 1

  have hγ := hcell x.1 hx.1
  have e1 : ((qminor (EA (E := Wq →L[ℂ] Wp) hD) (C3.xR k r r le_rfl) (C3.xR k r r le_rfl)
      (y + ((2 * r + k : ℕ) : ℂ) / 2) : SA (E := Wq →L[ℂ] Wp) hD) : Module.End ℂ (VS k r 0 D (Wq →L[ℂ] Wp))) =
      qminor (Eh (E := Wq →L[ℂ] Wp) (i := 0) hD) (cI ∘ C3.xR k r r le_rfl) (cI ∘ C3.xR k r r le_rfl)
        (y + ((2 * r + k : ℕ) : ℂ) / 2) := by
    have := map_qminor (SA (E := Wq →L[ℂ] Wp) hD).val (EA hD) (C3.xR k r r le_rfl) (C3.xR k r r le_rfl)
      (y + ((2 * r + k : ℕ) : ℂ) / 2)
    rw [Subalgebra.coe_val] at this
    rw [this]
    exact qminor_reindex (Eh hD) cI cI_inj _ _ _
  rw [e1, rep_qminor hD _ _ _ v₀ _ hγ]
  have hpos : posL k r 0 ∘ (cI ∘ C3.xR k r r le_rfl) = C3.xR k r r le_rfl := funext fun l => posL_cI _
  have hloc := (good_qminor (E := Wq →L[ℂ] Wp) hD (cI ∘ C3.xR k r r le_rfl) (cI ∘ C3.xR k r r le_rfl)
    (y + ((2 * r + k : ℕ) : ℂ) / 2)).loc (cut k r 0 D (B.JF Bs F)) (B.JF Bs F) (fun x' hx' => cut_of_mem _ hx')
    _ hγ
  rw [hpos] at hloc
  rw [hpos]
  exact hloc.symm

end Formalism.FourierDecayAlt.P
end
end

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.PTieUL
section
open Matrix MeasureTheory
open scoped ENNReal NNReal

noncomputable section

namespace Formalism.FourierDecayAlt.P.PTieUL

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.P.PBH Formalism.FourierDecayAlt.P.PTieB Formalism.FourierDecayAlt.P.PTieL

theorem lev_indU {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (P : M.Par)
    (T : D.LevTower P.k P.r Wp Wq) (hP : IsPlace P T.base.z T.base.z' T.base.π T.base.π')
    (X : ActualOps P.k P.r T.base.z T.base.z' T.base.π T.base.π') (μ : Measure (Mt P.k P.r))
    (L : R.LevelData (Pr (RadSp P.k P.r T.base.z T.base.z' T.base.π T.base.π')) P.r)
    (st : Fr.Start (Pr (RadSp P.k P.r T.base.z T.base.z' T.base.π T.base.π'))) (l0 : ℕ)
    (hD : P5.IsData P T.base.z T.base.z' T.base.π T.base.π' X μ L st l0) :
    ∀ (j : ℕ) (hj : j ≤ P.r),
    ∃ (Xj : ActualOps (JC.parLev P j).k (JC.parLev P j).r (T.bs j).z (T.bs j).z' (T.bs j).π (T.bs j).π')
      (μj : Measure (Mt P.k (P.r - j)))
      (Lj : R.LevelData (Pr (RadSp P.k (P.r - j) (T.bs j).z (T.bs j).z' (T.bs j).π (T.bs j).π')) (P.r - j))
      (stj : Fr.Start (Pr (RadSp P.k (P.r - j) (T.bs j).z (T.bs j).z' (T.bs j).π (T.bs j).π'))) (κ : ℝ),
      0 < κ ∧ P5.IsData (JC.parLev P j) (T.bs j).z (T.bs j).z' (T.bs j).π (T.bs j).π' Xj μj Lj stj l0 ∧
      KB.ZetaNorm (T.bs j) μj ∧
      ∀ c : Fin P.r → ℂ, (∀ l : Fin P.r, l.val < j → c l ≠ 0) →
      ∃ Tj : RadSp P.k P.r T.base.z T.base.z' T.base.π T.base.π' →ₗ[ℂ]
        RadSp P.k (P.r - j) (T.bs j).z (T.bs j).z' (T.bs j).π (T.bs j).π',
      (∀ Φ c'' g, (Tj Φ : Fn P.k (P.r - j) (Wq →L[ℂ] Wp)) c'' g =
        (Φ : Fn P.k P.r (Wq →L[ℂ] Wp)) (P5.glue ⟨j, by omega⟩ c (PTie.shiftCf ⟨j, by omega⟩ c''))
          (D.castM (by omega) (ιLev P.k j (P.r - j) g))) ∧
      (∀ Φ Ψ c'', P5.pairAt μj (Tj Φ) (Tj Ψ) c'' =
        (κ : ℂ) * P5.pairAt μ Φ Ψ (P5.glue ⟨j, by omega⟩ c (PTie.shiftCf ⟨j, by omega⟩ c''))) ∧
      (∀ l : Fin (P.r - j), Rel Tj (L.p ⟨l.val + j, by omega⟩) (Lj.p l) ∧
        Rel Tj (L.c ⟨l.val + j, by omega⟩) (Lj.c l) ∧ Rel Tj (L.ci ⟨l.val + j, by omega⟩) (Lj.ci l)) ∧
      ∀ (n : ℕ) (hn : n + j ≤ P.r) (Y : ℂ),
        MRel Tj (P5.QQi L st ⟨n + j, by omega⟩ Y) (P5.QQi Lj stj ⟨n, by omega⟩ Y) := by
  intro j
  induction j with
  | zero =>
    intro _
    obtain ⟨μ0, hμ0⟩ := Formalism.FourierDecayAlt.P.exists_zeta_normalized_haar P.k (P.r - 0) Wp Wq (T.bs 0)
    have h1 : B.IsHaarOn (Glev P.k P.r (Fin.last P.r)) μ := hD.2.1
    obtain ⟨a, ha⟩ : ∃ a : ℝ≥0, μ = a • μ0 := by
      have hU := Formalism.FourierDecayAlt.P.opposite_weyl_subgroup_closed P.k P.r
      have h1' := h1
      have h0 : B.IsHaarOn (Glev P.k P.r (Fin.last P.r)) μ0 := hμ0.1
      rw [glev_last_eq] at h1' h0
      exact Formalism.FourierDecayAlt.P.haar_measure_unique_up_to_scalar P.k P.r _ μ0 μ hU h0 h1'.conc h1'.left h1'.finite_compact
    have ha0 : (a : ℝ) ≠ 0 := by
      intro h
      apply h1.ne_zero
      rw [ha, show a = 0 from by exact_mod_cast h, zero_smul]
    refine ⟨X, μ0, L, st, (a : ℝ)⁻¹, inv_pos.2 (lt_of_le_of_ne a.2 (Ne.symm ha0)),
      ⟨JCTx5.isPlace_lev P T ⟨0, by omega⟩ hP, hμ0.1, hD.2.2⟩, hμ0, fun c _ => ⟨LinearMap.id,
      fun Φ c'' g => ?_, fun Φ Ψ c'' => ?_, fun l => ⟨rel_id _, rel_id _, rel_id _⟩, fun n hn Y => mrel_id _⟩⟩
    · rw [glue_zero', castM_iota0]; rfl
    · rw [glue_zero', ha, pairAt_smul, ← mul_assoc, ← Complex.ofReal_mul, inv_mul_cancel₀ ha0, Complex.ofReal_one,
        one_mul]
      rfl
  | succ j ih =>
    intro hj'
    obtain ⟨Xj, μj, Lj, stj, κ, hκ, hDj, hZj, hall⟩ := ih (by omega)
    have hPl := JCTx5.isPlace_lev P T ⟨j + 1, by omega⟩ hP
    obtain ⟨Xs⟩ := Formalism.FourierDecayAlt.P.actual_operators_exist _ _ _ _ _ _ _ hPl
    obtain ⟨Ls, sts, h1, h2, h3, h4, h5, h6⟩ := Formalism.FourierDecayAlt.P.level_start_actual _ _ _ _ _ _ _ hPl Xs l0
    obtain ⟨μs, hμs⟩ := Formalism.FourierDecayAlt.P.exists_zeta_normalized_haar P.k (P.r - (j + 1)) Wp Wq (T.bs (j + 1))
    have hDs : P5.IsData (JC.parLev P (j + 1)) (T.bs (j + 1)).z (T.bs (j + 1)).z' (T.bs (j + 1)).π
        (T.bs (j + 1)).π' Xs μs Ls sts l0 := ⟨hPl, hμs.1, h1, h2, h3, h4, h5, h6⟩
    refine ⟨Xs, μs, Ls, sts, κ, hκ, hDs, hμs, fun c hc => ?_⟩
    obtain ⟨Tj, hform, hpair, hsite, hqq⟩ := hall c (fun l hl => hc l (by omega))
    have hn : P.r - j = 1 + (P.r - (j + 1)) := by omega
    have hcj : c ⟨j, by omega⟩ ≠ 0 := hc ⟨j, by omega⟩ (by simp)
    obtain ⟨T', hf', hs', hq', hp'⟩ := step_cast (k := P.k) (n := P.r - j) (ρ := P.r - (j + 1)) hn
      (levTower_bs_z_eq_castV_liftVec T j hj') (levTower_bs_z'_eq_castV_liftVec T j hj') (T.bs (j + 1)).z_mem (T.bs (j + 1)).z'_mem (tower_π T j hj')
      (tower_π' T j hj') Xj Xs Lj stj Ls sts (M.sgn (JC.parLev P j) l0) μj μs hDj.2.2.1 hDs.2.2.1
      hDj.2.2.2.1 hDs.2.2.2.1 hZj.1 hμs.1 hZj.2 hμs.2 (c ⟨j, by omega⟩) hcj
    refine ⟨T' ∘ₗ Tj, fun Φ c'' g => ?_, fun Φ Ψ c'' => ?_, fun l => ?_, fun n hn' Y => ?_⟩
    · rw [LinearMap.comp_apply, hf', hform, glue_step j hj' c c'' hn,
        lift_lift_M j (P.r - (j + 1)) (P.r - j) P.r hn.symm (by omega) (by omega)]
    · rw [LinearMap.comp_apply, LinearMap.comp_apply, hp', hpair, glue_step j hj' c c'' hn]
    · have e : (⟨l.val + 1 + j, by omega⟩ : Fin P.r) = ⟨l.val + (j + 1), by omega⟩ :=
        Fin.ext (show l.val + 1 + j = l.val + (j + 1) by omega)
      obtain ⟨a1, a2, a3⟩ := hsite ⟨l.val + 1, by omega⟩
      obtain ⟨b1, b2, b3⟩ := hs' l
      rw [← e]
      exact ⟨rel_comp a1 b1, rel_comp a2 b2, rel_comp a3 b3⟩
    · have e : (⟨n + 1 + j, by omega⟩ : Fin (P.r + 1)) = ⟨n + (j + 1), by omega⟩ :=
        Fin.ext (show n + 1 + j = n + (j + 1) by omega)
      have a := hqq (n + 1) (by omega) Y
      have b := hq' n (by omega) Y
      rw [← e]
      exact mrel_comp a b

theorem levTransportU : Formalism.FourierDecayAlt.P.PTie.LevTransportU := by
  intro Wp Wq _ _ _ _ _ _ P z z' π π' X μ L st l0 Bs hD hz hz' hπ hπ' i
  obtain ⟨T, h1, h2, h3, h4, hN⟩ := Formalism.FourierDecayAlt.P.exists_normalized_tower P.k P.r Wp Wq Bs
  have e1 : T.base.z = z := h1.trans hz
  have e2 : T.base.z' = z' := h2.trans hz'
  have e3 : T.base.π = π := h3.trans hπ
  have e4 : T.base.π' = π' := h4.trans hπ'
  subst e1 e2 e3 e4
  obtain ⟨Xi, μi, Li, sti, κ, hκ, hDi, -, hall⟩ := lev_indU P T hD.1 X μ L st l0 hD i.val (by omega)
  refine ⟨T, hN, rfl, rfl, rfl, rfl, T.bs i, Xi, μi, Li, sti, κ, rfl, hκ, hDi, fun c hc => ?_⟩
  obtain ⟨Ti, hform, hpair, hsite, hqq⟩ := hall c hc
  refine ⟨Ti, ⟨hform, ⟨κ, hκ, hpair⟩, fun n hn Y => hqq n hn Y,
    fun S _ _ w => ⟨fun l => ?_, fun n hn => ?_, fun hw => ?_⟩⟩, hpair⟩
  · obtain ⟨a1, a2, a3⟩ := hsite l
    exact arel_bT (σ := P5.site L ⟨l.val + i, by omega⟩) (σ' := P5.site Li l) a1 a2 a3 w
  · exact arel_RRw (fun Y => hqq n hn Y) w
  · obtain ⟨⟨hA1, hA2, hA3, hA4⟩, hw2, hw3⟩ := hw
    have hq : sti.q = st.q := hDi.2.2.2.2.1.trans hD.2.2.2.2.1.symm
    have hinv : sti.inv = st.inv := hDi.2.2.2.2.2.1.trans hD.2.2.2.2.2.1.symm
    refine ⟨⟨hA1, hA2, fun l hl => ?_, hA4⟩, hw2, hw3⟩
    rw [hq, hinv]
    exact hA3 l hl

end Formalism.FourierDecayAlt.P.PTieUL

namespace Formalism.FourierDecayAlt.P

theorem level_transport_unitary : Formalism.FourierDecayAlt.P.PTie.LevTransportU := PTieUL.levTransportU

end Formalism.FourierDecayAlt.P
end
end

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.SecondDefectPlusWordLe
section
namespace Formalism.FourierDecayAlt.P.PBL

open Formalism.FourierDecayAlt Formalism.QuantumDeterminants NumberField
open scoped ComplexConjugate ComplexOrder

noncomputable section

open Classical

section wts

variable {P : M.Par} (l0 : ℕ) (a : List C.Letter) (e : Wd.Ix (Fin a.length)) (ρ : M.Ty P) (Pv : ℝ → ℝ) (C : ℝ)

def RHyp : List ℝ → Prop
  | [] => True
  | y :: ys => (0 < (topR l0 (KB.plusW ys a) (KB.firstSt ys e) ρ y).re ∧
      (topR l0 (KB.plusW ys a) (KB.firstSt ys e) ρ y).im = 0 ∧
      |Pv y| ≤ C * (topR l0 (KB.plusW ys a) (KB.firstSt ys e) ρ y).re) ∧ RHyp ys

theorem prodR_props (hC : 0 ≤ C) : ∀ ys : List ℝ, RHyp l0 a e ρ Pv C ys →
    (topRprod l0 a e ρ ys).im = 0 ∧ 0 < (topRprod l0 a e ρ ys).re ∧
      (ys.map fun y => |Pv y|).prod ≤ C ^ ys.length * (topRprod l0 a e ρ ys).re := by
  intro ys
  induction ys with
  | nil => simp [topRprod]
  | cons y ys ih =>
    intro h
    rw [RHyp] at h
    obtain ⟨⟨h1, h2, h3⟩, hr⟩ := h
    obtain ⟨i1, i2, i3⟩ := ih hr
    simp only [topRprod, Complex.mul_im, Complex.mul_re, List.map_cons, List.prod_cons, List.length_cons]
    refine ⟨by rw [i1, h2]; ring, by rw [i1, h2]; simp only [mul_zero, sub_zero]; positivity, ?_⟩
    rw [i1, h2]
    simp only [mul_zero, sub_zero]
    have hp : 0 ≤ (ys.map fun y => |Pv y|).prod := List.prod_nonneg fun x hx => by
      obtain ⟨z, -, rfl⟩ := List.mem_map.1 hx; exact abs_nonneg _
    calc |Pv y| * (ys.map fun y => |Pv y|).prod ≤ (C * (topR l0 (KB.plusW ys a) (KB.firstSt ys e) ρ y).re) *
          (C ^ ys.length * (topRprod l0 a e ρ ys).re) := mul_le_mul h3 i3 hp (by positivity)
      _ = C ^ (ys.length + 1) * ((topRprod l0 a e ρ ys).re * (topR l0 (KB.plusW ys a) (KB.firstSt ys e) ρ y).re) := by
          ring

end wts

section wts2

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {Wp Wq : InfinitePlace E → Type}
  [∀ x, NormedAddCommGroup (Wp x)] [∀ x, InnerProductSpace ℂ (Wp x)] [∀ x, NormedAddCommGroup (Wq x)]
  [∀ x, InnerProductSpace ℂ (Wq x)] [∀ x, FiniteDimensional ℂ (Wp x)] [∀ x, FiniteDimensional ℂ (Wq x)]

theorem second_defect_plus_word_le (S : C.HidaSetting E Wp Wq) (p : ∀ v, KB.Pl (D.parOf S v) (Wp (S.pl v)) (Wq (S.pl v))) (v : Fin S.f)
    (a : List C.Letter) (e : Wd.Ix (Fin a.length)) (ρ : M.Ty (D.parOf S v)) (C : ℝ) (hC : 0 ≤ C) (ys : List ℝ)
    (hR : RHyp (p v).l0 a e ρ (S.P v) C ys) :
    del2 S p v a e ρ * (ys.map fun y => |S.P v y|).prod ≤
      C ^ ys.length * del2 S p v (KB.plusW ys a) (KB.firstSt ys e) ρ := by
  obtain ⟨i1, i2, i3⟩ := prodR_props (p v).l0 a e ρ (S.P v) C hC ys hR
  have hd : del2 S p v (KB.plusW ys a) (KB.firstSt ys e) ρ = del2 S p v a e ρ * (topRprod (p v).l0 a e ρ ys).re := by
    unfold del2
    rw [cW_plusW, Complex.mul_re, i1, mul_zero, sub_zero, Real.sqrt_mul' _ i2.le]
    rw [show √(Top.cW (D.parOf S v) (p v).l0 a e ρ).re * √(topRprod (p v).l0 a e ρ ys).re *
        (√(Top.cW (D.parOf S v) (p v).l0 a e ρ).re * √(topRprod (p v).l0 a e ρ ys).re) =
        √(Top.cW (D.parOf S v) (p v).l0 a e ρ).re * √(Top.cW (D.parOf S v) (p v).l0 a e ρ).re *
          (√(topRprod (p v).l0 a e ρ ys).re * √(topRprod (p v).l0 a e ρ ys).re) by ring,
      Real.mul_self_sqrt i2.le]
  rw [hd]
  have h0 := second_defect_nonneg S p v a e ρ
  calc del2 S p v a e ρ * (ys.map fun y => |S.P v y|).prod ≤
        del2 S p v a e ρ * (C ^ ys.length * (topRprod (p v).l0 a e ρ ys).re) := mul_le_mul_of_nonneg_left i3 h0
    _ = _ := by ring

end wts2

end

end Formalism.FourierDecayAlt.P.PBL
end

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.SmoothOnHOfLoc
section
open Matrix MeasureTheory

noncomputable section

namespace Formalism.FourierDecayAlt.P.VandermondePolynomialIntegral

open Formalism.FourierDecayAlt Formalism.REAL Formalism.QuantumDeterminants

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

def KrAA : Prop :=
  ∀ (k r : ℕ) (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (Bs : B.RealPlaceData k r Wp Wq)
    (F : B.Mat k r → (Wq →L[ℂ] Wp)), KB.CptCoef Bs F → ∀ (u : ℂ), ∀ x ∈ B.GV k r,
      PBG.Kr Bs (C3.AAop k r r le_rfl u F) x = C3.AAop k r r le_rfl u (PBG.Kr Bs F) x

section point

variable {k r : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq]

theorem ptSize_app (h : C.LPt) (s : ℕ) (t : ℂ) : D.ptSize (h ++ [(s, t)]) = D.ptSize h + s := by
  simp [D.ptSize]

theorem smoothOnH_of_loc {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] {f : B.Mat k r → E}
    (hf : ∀ x ∈ B.GV k r, Formalism.FourierDecayAlt.P.CapelliWordSumExpansion.Loc ⊤ f x) : SmoothOnH (Hpk k r) f := by
  intro g₀ hg₀
  obtain ⟨U, f', hU, hgU, hf', hfe⟩ := hf g₀ hg₀
  exact ⟨U, f', hU, hgU, hf', fun g hg hgG => hfe g hg hgG⟩

theorem pt_poly (hKA : KrAA) (Bs : B.RealPlaceData k r Wp Wq) {G : B.Mat k r → (Wq →L[ℂ] Wp)} (hG : KB.CptCoef Bs G)
    (h : C.LPt) (s : ℕ) (t : ℂ) (hs : 2 ≤ s) (hq : D.IsLocPt (h ++ [(s, t)]) (r + 1)) {γ : B.Mat k r}
    (hγ : γ ∈ B.GV k r) (hZγ : Zhat k r Bs.z Bs.z' γ = D.ptMatN (h ++ [(s, t)]) (r + 1))
    (hpos : 0 < Gf k r Bs.z Bs.z' γ) {x : Mt k r × Mt k r}
    (hx : (Matrix.of x.1 : B.Mat k r) ∈ UWset k r Bs.z ∧ (Matrix.of x.2 : B.Mat k r) ∈ Formalism.QuantumDeterminants.Nset k r) :
    ∃ c : Fin (D.ptSize h + 1) → (Wq →L[ℂ] Wp),
      c (Fin.last _) = ((-1) ^ (s - 1) / t) • PBG.Kr Bs G ((Matrix.of x.1)⁻¹ * (Matrix.of x.2)⁻¹ * γ) ∧
      ∀ y : ℝ, PBG.Kr Bs (PBN.aaTop Bs y G) ((Matrix.of x.1)⁻¹ * (Matrix.of x.2)⁻¹ * γ) =
        ∑ n : Fin (D.ptSize h + 1), ((y : ℂ) ^ (n : ℕ)) • c n := by
  set σ : B.Mat k r := (Matrix.of x.1 : B.Mat k r)⁻¹ * (Matrix.of x.2 : B.Mat k r)⁻¹ with hσ
  set Gσ : B.Mat k r → (Wq →L[ℂ] Wp) := fun g => G (σ * g) with hGσdef
  have hGσ : KB.CptCoef Bs Gσ := cpt_left Bs hG hx
  have hp := inSS_pL Bs hx
  have hσS : σ ∈ Sset k r Bs.z :=
    ⟨(Matrix.of x.1 : B.Mat k r)⁻¹, Formalism.QuantumDeterminants.WeylGroupFacts.uw_inv hx.1, (Matrix.of x.2 : B.Mat k r)⁻¹,
      Formalism.QuantumDeterminants.WeylGroupFacts.mem_n_inv hx.2, rfl⟩
  have h1S : (1 : B.Mat k r) ∈ Sset k r Bs.z := ⟨1, Formalism.FourierDecayAlt.P.BigCellZetaMinors.one_uw _, 1, Formalism.QuantumDeterminants.WeylGroupFacts.mem_n_one,
    (Matrix.mul_one 1).symm⟩
  have h1S' : (1 : B.Mat k r) ∈ Sset k r Bs.z' := ⟨1, Formalism.FourierDecayAlt.P.BigCellZetaMinors.one_uw _, 1, Formalism.QuantumDeterminants.WeylGroupFacts.mem_n_one,
    (Matrix.mul_one 1).symm⟩
  have hdσ : ∀ (g : B.Mat k r) (l : Fin (r + 2)), Dmin k r Bs.z Bs.z' (σ * g) l = Dmin k r Bs.z Bs.z' g l := by
    intro g l
    have := Formalism.FourierDecayAlt.P.BigCellZetaMinors.dmin_sgs Bs hp g l
    rwa [sgs_pL] at this

  have hsz : D.ptSize h + s = r + 1 := by rw [← ptSize_app h s t]; exact hq.2
  have ht : t ≠ 0 := (hq.1 (s, t) (by simp)).2
  set i0 := D.ptSize h with hi0
  set hh := D.ptMatN h i0 with hhh
  have hZ : ∀ a b : Fin (r + 1), Zhat k r Bs.z Bs.z' γ a b = C3.Zb i0 s hh t a.val b.val := by
    intro a b
    rw [hZγ]
    exact ptMatN_zb h s t (r + 1) hsz.symm a b
  have hDlast : Dmin k r Bs.z Bs.z' γ (Fin.last (r + 1)) ≠ 0 := by
    intro h0
    have hTT : 0 ≤ Tz k r Bs.z * Tz k r Bs.z' := mul_nonneg Bs.T_pos.le Bs.T'_pos.le
    have : Gf k r Bs.z Bs.z' γ ≤ 0 := by
      unfold Gf
      rw [h0, map_zero]
      nlinarith [Complex.normSq_nonneg (Dmin k r Bs.z Bs.z' γ ⟨r, by omega⟩)]
    linarith
  have hdet : hh.det ≠ 0 := by
    intro h0
    apply hDlast
    rw [dmin_zb Bs.z Bs.z' γ i0 s hh t hZ]
    have := (Formalism.FourierDecayAlt.P.SignAntidiagonal.derivative_leading_zb i0 s hh t).2
    rw [show ((Fin.last (r + 1) : Fin (r + 2)) : ℕ) = i0 + s by simp; omega, this, h0]
    ring
  have hT' : herm (Hpk k r) Bs.z' Bs.z' ≠ 0 := by
    intro h0
    have := Bs.T'_pos
    unfold Tz at this
    rw [h0] at this
    simp at this
  obtain ⟨n0, hn0, yb, hyb, hzy, hnf1, hnf2⟩ :=
    nf_top Bs.z Bs.z' Bs.z'_mem hT' γ hγ i0 s hs hsz hh hdet t ht hZ
  have hn0N : n0 ∈ Formalism.QuantumDeterminants.Nset k r := stabilizer_mem_unipotent hn0
  have hn0S : n0 ∈ Sset k r Bs.z' := ⟨1, Formalism.FourierDecayAlt.P.BigCellZetaMinors.one_uw _, n0, hn0N, (Matrix.one_mul n0).symm⟩
  have hx₁G : γ * n0 ∈ B.GV k r := Formalism.QuantumDeterminants.WeylGroupFacts.uh_mul hγ hn0N.1
  have hZ₁ : ∀ a b : Fin (r + 1), Zhat k r Bs.z Bs.z' (γ * n0) a b = C3.Zb i0 s hh t a.val b.val := by
    intro a b; rw [corner_matrix_right_translate Bs.z Bs.z' γ n0 hn0]; exact hZ a b
  have hD₁ : ∀ l : Fin (r + 2), Dmin k r Bs.z Bs.z' (γ * n0) l = Dmin k r Bs.z Bs.z' γ l := by
    intro l; unfold Dmin; rw [corner_matrix_right_translate Bs.z Bs.z' γ n0 hn0]

  set K : B.Mat k r → (Wq →L[ℂ] Wp) := PBG.Kr Bs Gσ with hKdef
  have hKloc := loc_kr Bs hGσ
  have hKn0 : ∀ g, K (g * n0) = K g := by
    intro g
    rw [hKdef, PBG.kr_rightEq Bs Gσ g n0 hn0N, character_stabilizer_eq_one Bs.z'_mem cStd hn0, one_smul]
  have hKσ : ∀ g, K g = PBG.Kr Bs G (σ * g) := fun g => kr_left Bs G σ g
  have hR : ∀ g ∈ Q.Glev k r 0 ∩ Set.univ, ∀ p q, C3.InNp k r p q →
      Q.EH k r p q K g = C3.dpsiP k r Bs.z' p q • K g :=
    fun g _ p q hpq => PBG.kr_rule Bs Gσ g p q hpq
  obtain ⟨c, hc, hcy⟩ := top_poly isOpen_univ Bs.z Bs.z' yb i0 s hs hsz hh t hdet ht (γ * n0)
    ⟨(Formalism.FourierDecayAlt.P.CapelliUnderIntegral.glev0 _).2 hx₁G, Set.mem_univ _⟩ Bs.z'_mem hyb hzy hnf1 hnf2 hZ₁ K
    (smoothLev_of_loc hKloc) hR
  refine ⟨c, ?_, fun y => ?_⟩
  · rw [hc, hKn0, hKσ]
  · rw [← hcy y, hD₁]
    set u : ℂ := (y : ℂ) + ((2 * r + k : ℕ) : ℂ) / 2 with hu

    have hX1 := (Formalism.FourierDecayAlt.P.operators_commute_translations' (Wq →L[ℂ] Wp) k r Bs.z Bs.z' r le_rfl u 0 K Bs.z_mem Bs.z'_mem
      (smoothOnH_of_loc hKloc) 1 h1S n0 hn0S γ hγ).1
    have e1 : (fun g => K (1 * g * n0)) = K := by
      funext g; rw [Matrix.one_mul, hKn0]
    rw [e1, Matrix.one_mul] at hX1
    rw [← hX1]

    have hleft : ∀ g ∈ B.GV k r, PBN.aaTop Bs y G (σ * g) = PBN.aaTop Bs y Gσ g := by
      intro g hg
      unfold PBN.aaTop
      rw [hdσ]
      have hX0 := (Formalism.FourierDecayAlt.P.operators_commute_translations' (Wq →L[ℂ] Wp) k r Bs.z Bs.z' r le_rfl u 0 G Bs.z_mem Bs.z'_mem
        (smoothOnH_of_ckOn hG.1) σ hσS 1 h1S' g hg).1
      have e2 : (fun x => G (σ * x * 1)) = Gσ := by funext x; rw [Matrix.mul_one]
      rw [e2, Matrix.mul_one] at hX0
      rw [hX0]
    have hKA' := hKA k r Wp Wq Bs Gσ hGσ u γ hγ
    calc PBG.Kr Bs (PBN.aaTop Bs y G) (σ * γ)
        = PBG.Kr Bs (fun g => PBN.aaTop Bs y G (σ * g)) γ := (kr_left Bs _ σ γ).symm
      _ = PBG.Kr Bs (PBN.aaTop Bs y Gσ) γ := kr_congr Bs hleft hγ
      _ = (Dmin k r Bs.z Bs.z' γ (Fin.last _))⁻¹ • PBG.Kr Bs (C3.AAop k r r le_rfl u Gσ) γ :=
          kr_dmin Bs (C3.AAop k r r le_rfl u Gσ) (Fin.last _) γ
      _ = (Dmin k r Bs.z Bs.z' γ (Fin.last _))⁻¹ • C3.AAop k r r le_rfl u K γ := by rw [hKA']

end point

end Formalism.FourierDecayAlt.P.VandermondePolynomialIntegral
end
end

