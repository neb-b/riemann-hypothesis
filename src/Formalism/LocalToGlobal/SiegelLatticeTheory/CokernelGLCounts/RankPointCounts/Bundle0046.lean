module

public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.FiberCount
public import Mathlib
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.Bundle0044
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.CountingFormula.Bundle0005
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.FStarOmRepPf
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.Bundle0023
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.Bundle0027
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.Bundle0038
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.Bundle0024
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.Bundle0016
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.AtPtRel
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.Bundle0037
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.RowFrameCoherence.Bundle0001
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.Bundle0021
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.TermDefPf

@[expose] public section

-- bundled from Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.CoefDens
section
noncomputable section

namespace Formalism.L2.SG.Pf.Coef

open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.TermDef Formalism.L2.SG.DataCut
  Formalism.L2.SG.LsDatumB Formalism.L2.SG.Pf.PCount
open Classical ValuativeRel

attribute [local instance] Formalism.BasicNotions.Host.cmStar

def DensCong : Prop :=
  ∀ (F E : Type) {_ : Field F} {_ : ValuativeRel F} {_ : TopologicalSpace F} {_ : CommRing E} {_ : Algebra F E}
    {_ : TopologicalSpace E} {_ : MeasurableSpace E} (M : Loc.Model F E) (V : Type) {_ : AddCommGroup V}
    {_ : Module E V} (H : Loc.HermSp M V) (ϖ : 𝒪[F]) (abelian₂ : Submodule M.L.O V) (ι : Type) {_ : Fintype ι}
    {_ : DecidableEq ι} (G A : Matrix ι ι E),
    (∀ i j, A i j ∈ M.L.O) → (∃ y ∈ M.L.O, A.det * y = 1) →
      H.dens ϖ abelian₂ ((A.map M.L.cj).transpose * G * A) = H.dens ϖ abelian₂ G

section Steps

variable {D : Formalism.BasicNotions.D7} (M : ∀ p : PlF D, Loc.Model (D.s.atP p).Fp (D.s.atP p).Ep)
  (δ : ∀ p : PlF D, (D.s.atP p).Fp) (u u' : D.what₂.Word)

def GaPlusTh : Prop :=
  (∀ p, Agree δ M p) → (D.mem u).A.T ≡ (D.mem u').A.T [MOD (Lat.gS D) ^ 2] → PrimeHyp D u (Tu D u') →
  ∀ (w w' : Point D.host.E (D.R.rS + 1)) (Z Z' : PairVal.MatR D), kind w = kind w' → AtMat w Z → AtMat w' Z' →
  ∀ p, FCount.thZ M δ u u' w Z p ≠ none → FCount.thZ M δ u u' w Z p = FCount.thZ M δ u u' w' Z' p →
    ∃ A : Matrix (Fin (D.R.rS + 1) ⊕ Fin (D.R.rS + 1)) (Fin (D.R.rS + 1) ⊕ Fin (D.R.rS + 1)) (D.s.atP p).Ep,
      (∀ i j, A i j ∈ (M p).L.O) ∧ (∃ y ∈ (M p).L.O, A.det * y = 1) ∧
      CntLocal.GaPlus M δ p (CntLocal.Tn u) (CntLocal.Tn u') Z' =
        (A.map (M p).L.cj).transpose * CntLocal.GaPlus M δ p (CntLocal.Tn u) (CntLocal.Tn u') Z * A

end Steps

theorem densTh_of {D : Formalism.BasicNotions.D7} {M : ∀ p : PlF D, Loc.Model (D.s.atP p).Fp (D.s.atP p).Ep}
    {δ : ∀ p : PlF D, (D.s.atP p).Fp} {L : CntLocal.LocSp D M} {u u' : D.what₂.Word}
    (hC : DensCong) (hG : GaPlusTh M δ u u') : FCount.DensTh M δ L u u' := by
  intro hA hT hPH ϖ _ w w' Z Z' hk hZ hZ' p hne heq
  obtain ⟨A, hAO, hAd, hGa⟩ := hG hA hT hPH w w' Z Z' hk hZ hZ' p hne heq
  unfold CntLocal.densP
  rw [hGa]
  exact (hC (D.s.atP p).Fp (D.s.atP p).Ep (M p) (L.V p) (L.H p) (ϖ p) (CntLocal.lattice₂ L p (VS D).L0)
    (Fin (D.R.rS + 1) ⊕ Fin (D.R.rS + 1)) (CntLocal.GaPlus M δ p (CntLocal.Tn u) (CntLocal.Tn u') Z) A hAO hAd).symm

end Formalism.L2.SG.Pf.Coef
end
end

-- bundled from Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.FStarCohPfC
section
noncomputable section

open scoped Classical
open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.TermDef Formalism.L2.SG.DataCut Formalism.L2.SG.LsDatumB
  Formalism.L2.SG.TermLoc Formalism.L2.SG.Pf.PCount Formalism.L2.SG.Pf.FrameGlobalPatching

namespace Formalism.L2.SG.Pf.FrameGlobalPatching.FStar

attribute [local instance] Formalism.BasicNotions.Host.cmStar

open CohCut

variable {D : Formalism.BasicNotions.D7} (Zd : LocDat D) {u u' : D.what₂.Word} {F0 : FlagG (VS D) D.R.rS (CntLocal.Tn u)}
  {what₂ : Finset (Submodule (𝓞 D.host.E) (VS D).V)}

theorem split_finite : {p : PlF D | (Zd.M p).split.isSome}.Finite := by
  have hfinite (ℓ : ℕ) : {p : PlF D | Loc.resChar p = ℓ}.Finite := by
    have hsub : {p : PlF D | Loc.resChar p = ℓ} ⊆
        {v | v.asIdeal ∣ Ideal.span {(ℓ : 𝓞 D.host.F)}} := by
      intro p hp
      simp only [Set.mem_ofPred_eq] at hp ⊢
      rw [Ideal.dvd_span_singleton, ← hp, ← Ideal.Quotient.eq_zero_iff_mem, map_natCast]
      exact ringChar.Nat.cast_ringChar
    by_cases hℓ : ℓ = 0
    · subst hℓ
      convert Set.finite_empty
      rename_i p
      change Loc.resChar p = 0 ↔ False
      simp only [iff_false]
      intro hp
      have h1 : ((Ideal.absNorm p.asIdeal : ℕ) : 𝓞 D.host.F ⧸ p.asIdeal) = 0 := by
        rw [← map_natCast (Ideal.Quotient.mk p.asIdeal), Ideal.Quotient.eq_zero_iff_mem]
        exact Ideal.absNorm_mem p.asIdeal
      have hc : CharP (𝓞 D.host.F ⧸ p.asIdeal) 0 := by
        have h2 := ringChar.charP (𝓞 D.host.F ⧸ p.asIdeal)
        unfold Loc.resChar at hp
        rwa [hp] at h2
      rw [CharP.cast_eq_zero_iff _ 0, zero_dvd_iff, Ideal.absNorm_eq_zero_iff] at h1
      exact p.ne_bot h1
    · refine (Ideal.finite_factors ?_).subset hsub
      rw [Ne, Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot]
      exact_mod_cast hℓ
  refine ((hfinite (D.host.g 0)).union (hfinite (D.host.g 1))).subset ?_
  intro p hp
  simp only [Set.mem_ofPred_eq] at hp
  have hs : (D.s.atP p).split.isSome := by
    obtain ⟨g, hg⟩ := Option.isSome_iff_exists.1 hp
    have hA := (Zd.agree p).2.2.2.2.2
    rw [hg] at hA
    cases h2 : (D.s.atP p).split with
    | none =>
      rw [h2] at hA
      exact (hA : False).elim
    | some sg => rfl
  have hin : Loc.resChar p ∈ ({D.host.g 0, D.host.g 1} : Finset ℕ) := (D.s_split p).1 hs
  simp only [Finset.mem_insert, Finset.mem_singleton] at hin
  simp only [Set.mem_union, Set.mem_ofPred_eq]
  exact hin

theorem cohIota_holds : CohIota Zd u u' F0 what₂ := by
  intro _ γ Z F'₂ φ' _
  refine (split_finite Zd).subset ?_
  intro p hp
  simp only [Set.mem_ofPred_eq]
  by_contra hn
  apply hp
  intro g hg
  rw [hg] at hn
  exact (hn rfl).elim

end Formalism.L2.SG.Pf.FrameGlobalPatching.FStar
end
end

-- bundled from Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.FStarMinors
section
noncomputable section

open scoped Classical
open Matrix NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.TermDef Formalism.L2.SG.DataCut
  Formalism.L2.SG.LsDatumB Formalism.L2.SG.TermLoc Formalism.L2.SG.Pf.PCount Formalism.L2.SG.Pf.FrameGlobalPatching

namespace Formalism.L2.SG.Pf.FrameGlobalPatching.FStar.FsLA

variable {E : Type} [Field E] [NumberField E] [StarRing E]

theorem lm_one {N l : ℕ} (hl : l ≤ N) : leadMinorE (1 : Matrix (Fin N) (Fin N) E) l = 1 := by
  unfold leadMinorE
  rw [dite_eq_left hl, Matrix.submatrix_one _ (Fin.castLE_injective hl), Matrix.det_one]

theorem lm_diag_right {N : ℕ} (X Dg : Matrix (Fin N) (Fin N) E) (hD : ∀ c b, c ≠ b → Dg c b = 0) (l : ℕ) :
    leadMinorE (X * Dg) l = leadMinorE X l * leadMinorE Dg l := by
  unfold leadMinorE
  split_ifs with h
  · have hsub : (X * Dg).submatrix (Fin.castLE h) (Fin.castLE h) =
        X.submatrix (Fin.castLE h) (Fin.castLE h) * Dg.submatrix (Fin.castLE h) (Fin.castLE h) := by
      ext i j
      simp only [Matrix.submatrix_apply, Matrix.mul_apply]
      rw [Formalism.L2.SG.Pf.sum_castLE_td h]
      intro d hd
      have hj := j.isLt
      rw [hD d _ (fun e => by have h1 := congrArg Fin.val e; simp at h1; omega), mul_zero]
    rw [hsub, Matrix.det_mul]
  · simp

theorem zhatOM_one_eq {r : ℕ} :
    ZhatOM (1 : Matrix (Fin (r + 1)) (Fin (r + 1)) E) = Matrix.diagonal fun b => (-1 : E) ^ (r - b.val) := by
  ext a b
  simp only [ZhatOM, Matrix.one_apply, Matrix.diagonal_apply]
  split_ifs with h
  · subst h; rw [mul_one]
  · rw [mul_zero]

theorem zhatOM_eq_mul {r : ℕ} (X : Matrix (Fin (r + 1)) (Fin (r + 1)) E) : ZhatOM X = X * ZhatOM 1 := by
  rw [zhatOM_one_eq]
  ext a b
  rw [Matrix.mul_diagonal]
  simp only [ZhatOM]
  rw [mul_comm]

theorem zhatOM_zhatOM {r : ℕ} (X : Matrix (Fin (r + 1)) (Fin (r + 1)) E) : ZhatOM (ZhatOM X) = X := by
  ext a b
  simp only [ZhatOM]
  rw [← mul_assoc, ← pow_add, ← two_mul, pow_mul, neg_one_sq, one_pow, one_mul]

theorem lm_zhatOM {r : ℕ} (X : Matrix (Fin (r + 1)) (Fin (r + 1)) E) (l : ℕ) :
    leadMinorE (ZhatOM X) l = leadMinorE X l * leadMinorE (ZhatOM (1 : Matrix (Fin (r + 1)) (Fin (r + 1)) E)) l := by
  rw [zhatOM_eq_mul X]
  refine lm_diag_right X _ (fun c b hcb => ?_) l
  rw [zhatOM_one_eq, Matrix.diagonal_apply_ne _ hcb]

theorem lm_sign_ne {r l : ℕ} (hl : l ≤ r + 1) :
    leadMinorE (ZhatOM (1 : Matrix (Fin (r + 1)) (Fin (r + 1)) E)) l ≠ 0 := by
  intro h0
  have := lm_zhatOM (ZhatOM (1 : Matrix (Fin (r + 1)) (Fin (r + 1)) E)) l
  rw [zhatOM_zhatOM, lm_one hl, h0, mul_zero] at this
  exact one_ne_zero this

theorem lm_cell {r : ℕ} (X : Matrix (Fin (r + 1)) (Fin (r + 1)) E) (w : Point E (r + 1))
    (h : IsInCell (ZhatOM X) w) (l : ℕ) :
    leadMinorE X l * leadMinorE (ZhatOM (1 : Matrix (Fin (r + 1)) (Fin (r + 1)) E)) l = leadMinorE (ptMat w) l := by
  obtain ⟨L, U, hL, hU, hX⟩ := h
  rw [← lm_zhatOM, hX]
  exact Formalism.L2.SG.Pf.leadMinor_uni L (ptMat w) U (fun a c h => (hL a c).1 h) (fun a => (hL a a).2 rfl)
    (fun d b h => (hU d b).1 h) (fun b => (hU b b).2 rfl) l

end Formalism.L2.SG.Pf.FrameGlobalPatching.FStar.FsLA

namespace Formalism.L2.SG.Pf.FrameGlobalPatching.FStar

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : Formalism.BasicNotions.D7} {u u' : D.what₂.Word} {F0 : FlagG (VS D) D.R.rS (CntLocal.Tn u)}
  {what₂ : Finset (Submodule (𝓞 D.host.E) (VS D).V)}

theorem starDmin_eq (w : Point D.host.E (D.R.rS + 1)) (l : ℕ) : Dmin w l = leadMinorE (ptMat w) l := by
  unfold Dmin leadMinorE
  split_ifs <;> rfl

theorem starRepF_rep (γ : TermDef.Term D u u' F0 what₂) :
    Rep γ.lam (lf D F0) (PD D γ.lam (lf D F0) u') γ.cls (repF γ) := by
  unfold repF
  rcases hn : nrep γ with _ | x
  · exact ⟨(Quot.out γ.cls).2, Quot.out_eq _⟩
  · unfold nrep at hn
    split_ifs at hn with h
    cases hn
    exact h.choose_spec.1

theorem star_frame_cell_minor (γ : TermDef.Term D u u' F0 what₂) (w : Point D.host.E (D.R.rS + 1)) (hγ : EligAt γ w)
    (l : ℕ) : leadMinorE (starZh (frame (lf D F0)) (starFrame γ)) l *
      leadMinorE (ZhatOM (1 : Matrix (Fin (D.R.rS + 1)) (Fin (D.R.rS + 1)) D.host.E)) l = leadMinorE (ptMat w) l := by
  obtain ⟨F', ⟨h1, h1e⟩, -, hcell⟩ := hγ.2
  obtain ⟨h2, h2e⟩ := starRepF_rep γ
  have hrel := (Formalism.L2.SG.Pf.double_coset_equivalence γ.lam (lf D F0) (PD D γ.lam (lf D F0) u') ⟨F', h1⟩ ⟨repF γ, h2⟩).1
    (h1e.trans h2e.symm)
  have hc := Formalism.L2.SG.Pf.cell_rel (lf D F0) hrel w hcell
  obtain ⟨hξ1, hξ2⟩ := inv_unitri _ (admissibility_witness_unitriangular γ.lam (lf D F0) (repF γ)).1 (admissibility_witness_unitriangular γ.lam (lf D F0) (repF γ)).2
  have hZ : starZh (frame (lf D F0)) (starFrame γ) =
      1 * ZhatL (lf D F0) (repF γ) * (Matrix.of fun a b => (((admXi D γ.lam (lf D F0) (repF γ))⁻¹ a b : 𝓞 D.host.E) : D.host.E)) := by
    rw [Matrix.one_mul]
    exact FsLA.gram_comb_left (S := VS D) (frame (repF γ)) _ (frame (lf D F0))
  rw [hZ, Formalism.L2.SG.Pf.leadMinor_uni 1 _ _ (fun a c h => Matrix.one_apply_ne (ne_of_lt h)) (fun a => Matrix.one_apply_eq a)
    (fun d b h => by simp [Matrix.of_apply, hξ1 d b h]) (fun b => by simp [Matrix.of_apply, hξ2 b]) l]
  exact FsLA.lm_cell _ w hc l

variable (u u' F0 what₂)

theorem starMinors_holds : StarMinors u u' F0 what₂ := by
  intro γ Z hC
  obtain ⟨w, hγ, w', -, hk, hZ⟩ := hC
  have hs : ∀ l, l ≤ D.R.rS + 1 →
      leadMinorE (ZhatOM (1 : Matrix (Fin (D.R.rS + 1)) (Fin (D.R.rS + 1)) D.host.E)) l ≠ 0 :=
    fun l hl => FsLA.lm_sign_ne hl
  have c1 := star_frame_cell_minor γ w hγ
  have c2 := FsLA.lm_cell Z w' hZ
  have hdet : ∀ v : Point D.host.E (D.R.rS + 1), leadMinorE (ptMat v) (D.R.rS + 1) ≠ 0 := fun v => by
    rw [FsLA.leadMinorE_full]; exact Formalism.L2.SG.Pf.det_ptMat_ne v
  have hcross : Dmin w D.R.rS * Dmin w' (D.R.rS + 1) = Dmin w' D.R.rS * Dmin w (D.R.rS + 1) := by
    unfold kind at hk
    by_cases h0 : Dmin w D.R.rS = 0
    · rw [if_pos h0] at hk
      have h0' : Dmin w' D.R.rS = 0 := by
        by_contra h; rw [if_neg h] at hk; cases hk
      rw [h0, h0', zero_mul, zero_mul]
    · rw [if_neg h0] at hk
      have h0' : Dmin w' D.R.rS ≠ 0 := by
        intro h; rw [if_pos h] at hk; cases hk
      rw [if_neg h0'] at hk
      have hz := Option.some.inj hk
      unfold zetaOf at hz
      field_simp at hz
      linear_combination hz
  rw [starDmin_eq, starDmin_eq, starDmin_eq, starDmin_eq, ← c1, ← c1, ← c2, ← c2] at hcross
  refine ⟨?_, ?_, ?_⟩
  · rw [← FsLA.leadMinorE_full]
    intro h; apply hdet w'; rw [← c2, h, zero_mul]
  · rw [← FsLA.leadMinorE_full]
    intro h; apply hdet w; rw [← c1, h, zero_mul]
  · rw [← FsLA.leadMinorE_full, ← FsLA.leadMinorE_full]
    have hr := hs D.R.rS (Nat.le_succ _)
    have hr1 := hs (D.R.rS + 1) le_rfl
    apply mul_right_cancel₀ (mul_ne_zero hr hr1)
    linear_combination hcross

end Formalism.L2.SG.Pf.FrameGlobalPatching.FStar
end
end

-- bundled from Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.FStarOmPartPf
section
noncomputable section

open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.L2.SG.TermLoc Formalism.L2.SG.Pf.FrameGlobalPatching

namespace Formalism.L2.SG.Pf.FrameGlobalPatching.FStar

variable {D : Formalism.BasicNotions.D7} (Zd : LocDat D) (u u' : D.what₂.Word) (F0 : FlagG (VS D) D.R.rS (CntLocal.Tn u))
  (what₂ : Finset (Submodule (𝓞 D.host.E) (VS D).V))

theorem omega_part_holds : OmPart Zd u u' F0 what₂ :=
  omPart_of Zd (modeMatrixDet_eq_adjointDet Zd u u' F0 what₂) (omega_local_holds Zd u u' F0 what₂) (omega_representative_holds u u' F0 what₂)

end Formalism.L2.SG.Pf.FrameGlobalPatching.FStar
end
end

-- bundled from Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.FiberCountSteps
section
noncomputable section

namespace Formalism.L2.SG.Pf.FCount

open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.TermDef Formalism.L2.SG.DataCut

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem eligible_totally_positive {D : Formalism.BasicNotions.D7} (u u' : D.what₂.Word) (F0 : FlagG (VS D) D.R.rS (CntLocal.Tn u))
    (what₂ : Finset (Submodule (𝓞 D.host.E) (VS D).V)) : EligPos u u' F0 what₂ :=
  fun γ w h => Formalism.L2.SG.WConst.atPt_totPos γ w h.2

end Formalism.L2.SG.Pf.FCount
end
end

-- bundled from Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.FinitePhase
section
noncomputable section

open scoped Classical ComplexConjugate

namespace Formalism.L2.SG.Pf.FinitePhase

open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.L2.SG.TermDef Formalism.L2.SG.HidaSetting

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} (X : HidaSetting D) (Y : Formalism.L2.SG.Full.Full X) (u u' : D.what₂.Word)
  (κ : Term D u u' (X.Fu u) (Y.what₂ u) → ℕ)

def LiftCellC : Prop :=
  ∀ (R : Formalism.L2.SG.TermOp.Rw (Y.what₂ u) (Y.what₂ u') Y.TR) (ρ : ℕ) (s : Formalism.L2.SG.Pf.RowForm.LiftT X Y u u' κ R ρ),
    s.1.relevant →
    ∃ L U : Formalism.L2.SG.PairVal.MatR D, IsLoUni L ∧ IsUpUni U ∧
      ZhatOM (ZhatL (lf D (X.Fu u)) s.1.frame) = L * ptMat (Formalism.L2.SG.PairVal.ptOf s.1.toTerm) * U ∧
      ∀ v, Formalism.L2.SG.RealObj.ZhatO (Formalism.L2.SG.RealObj.ZX X u u' 1 s.1.pt.1 v) =
        (L * ptMat (Formalism.L2.SG.PairVal.ptOf s.1.toTerm) * U).map (fun x => X.B.I.φ v (X.ιE.symm x))

def FinPhaseC : Prop :=
  ∀ (R : Formalism.L2.SG.TermOp.Rw (Y.what₂ u) (Y.what₂ u') Y.TR) (ρ : ℕ) (s : Formalism.L2.SG.Pf.RowForm.LiftT X Y u u' κ R ρ),
    s.1.relevant → ∀ L U : Formalism.L2.SG.PairVal.MatR D, IsLoUni L → IsUpUni U →
      ZhatOM (ZhatL (lf D (X.Fu u)) s.1.frame) = L * ptMat (Formalism.L2.SG.PairVal.ptOf s.1.toTerm) * U →
      Formalism.L2.SG.TermOp.chiN X (Formalism.L2.SG.TermOp.kOf X u u' ((Y.cs u).h ((Y.cs u).base s.1.lam) : X.B.I.Gf)
                ((Y.cs u').h ((Y.cs u').base s.1.lam') : X.B.I.Gf) s.1.pt) * Formalism.L2.SG.PairVal.phasePair (gS D) L U =
        Formalism.L2.SG.PairVal.phaseAt s.1.toTerm (Formalism.L2.SG.PairVal.ptOf s.1.toTerm)

theorem phaseTieC_of (hC : LiftCellC X Y u u' κ) (hF : FinPhaseC X Y u u' κ) :
    Formalism.L2.SG.Pf.RowForm.PhaseTieC X Y u u' κ := by
  intro R ρ s hrel g hg g' hg' hdec
  obtain ⟨L, U, hL, hU, hrat, hreal⟩ := hC R ρ s hrel
  have hex := Formalism.L2.SG.RealObj.RealPointRepresentatives.exists_ptRep X u u' s.1.pt.1 _ L U hL hU hreal
  have hPt : Formalism.L2.SG.RealObj.IsPtRep X u u' (Formalism.L2.SG.PairVal.ptOf s.1.toTerm)
      (Formalism.L2.SG.RealObj.gamW X u u' (Formalism.L2.SG.PairVal.ptOf s.1.toTerm)) := by
    unfold Formalism.L2.SG.RealObj.gamW
    rw [dite_eq_left hex]
    exact hex.choose_spec
  rw [Formalism.L2.SG.RealObj.RealPhaseFrames.realPhase X u u' hg hg' hdec _ hPt L U hL hU hreal]
  exact hF R ρ s hrel L U hL hU hrat

end Formalism.L2.SG.Pf.FinitePhase
end
end

-- bundled from Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.LiftAtSome
section
noncomputable section

namespace Formalism.L2.SG.Pf

open Formalism.BasicNotions Formalism.L2.SG.HidaSetting Formalism.L2.SG.Pf.RowForm

theorem liftAtSomeC_holds {D : D7} (X : HidaSetting D) (Y : Formalism.L2.SG.Full.Full X) (u u' : D.what₂.Word)
    (κ : Formalism.L2.SG.TermDef.Term D u u' (X.Fu u) (Y.what₂ u) → ℕ) : LiftAtSomeC X Y u u' κ := by
  intro R ρ s hrel
  have hG : s.1.toTerm.G ≠ 0 := by
    intro h0
    apply s.2.1
    show Formalism.L2.SG.TermOp.Gt s.1 = 0
    unfold Formalism.L2.SG.TermOp.Gt
    exact if_pos h0
  exact Formalism.L2.SG.LeadingMinorsNonvanishing.atSomeAll_holds D X Y u u' s.1.toTerm hG hrel

theorem atPtRelevantC_holds {D : D7} (X : HidaSetting D) (Y : Formalism.L2.SG.Full.Full X) (u u' : D.what₂.Word) :
    AtPtRelevantC X Y u u' := fun t w h =>
  Formalism.L2.SG.Pf.FinXP.atPtRelevant_holds D u u' (X.Fu u) (Y.what₂ u) t w h

theorem liftIotaC_of (hD : Formalism.L2.SG.Pf.IotaDictC) {D : D7} (X : HidaSetting D) (Y : Formalism.L2.SG.Full.Full X)
    (u u' : D.what₂.Word) : Formalism.L2.SG.Pf.RowForm.ScalT.LiftIotaC X Y u u' := by
  intro s₁ s₂ hG₁ hG₂ hg₁ hg₂ hrow
  have hlam : s₁.lam = s₂.lam := congrArg (fun r => r.1.1) hrow
  have hlam' : s₁.lam' = s₂.lam' := congrArg (fun r => r.2.1.1) hrow
  have hio : Formalism.L2.SG.TermOp.iotaOf Y.TR (Y.cs u) (Y.cs u') s₁ = Formalism.L2.SG.TermOp.iotaOf Y.TR (Y.cs u) (Y.cs u') s₂ :=
    congrArg (fun r => r.2.2) hrow
  exact (hD D X Y u u' s₁ s₂ hG₁ hG₂ hg₁ hg₂ hlam hlam').mp hio

end Formalism.L2.SG.Pf
end
end

-- bundled from Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.RepAtTup
section
noncomputable section

namespace Formalism.L2.SG.Pf.FibPart

open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.TermDef Formalism.L2.SG.DataCut
  Formalism.L2.SG.LsDatumB Formalism.L2.SG.Pf.PCount
open Classical ValuativeRel
open Formalism.L2.SG.Pf.AtPt Formalism.L2.SG.TermLoc

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section Steps

variable {D : Formalism.BasicNotions.D7} (M : ∀ p : PlF D, Loc.Model (D.s.atP p).Fp (D.s.atP p).Ep)
  (δ : ∀ p : PlF D, (D.s.atP p).Fp) (u u' : D.what₂.Word)
  (F0 : FlagG (VS D) D.R.rS (CntLocal.Tn u)) (what₂ : Finset (Submodule (𝓞 D.host.E) (VS D).V))

def RepIn (γ : TermDef.Term D u u' F0 what₂) (Z : PairVal.MatR D) : Prop :=
  ∃ F' ∈ CntLocal.EZ (D := D) ((Tu D u' : ℕ) : D.host.E) F0 γ.lam Z,
    Rep γ.lam (lf D F0) (PD D γ.lam (lf D F0) u') γ.cls F'

def Pre : Prop :=
  (∀ p, Agree δ M p) ∧ (D.mem u).A.T ≡ (D.mem u').A.T [MOD (Lat.gS D) ^ 2] ∧ PrimeHyp D u (Tu D u') ∧
    PairVal.NormRepExists D u u' F0 what₂ ∧ IsRowReps D F0 what₂ ∧ EligRel u u' F0 what₂

def TupFun : Prop :=
  Pre M δ u u' F0 what₂ → ∀ (γ : TermDef.Term D u u' F0 what₂) (w : Point D.host.E (D.R.rS + 1)) (Z : PairVal.MatR D),
    EligAt γ w → AtMat w Z → RepIn u u' F0 what₂ γ Z → locT M δ γ = tupZ M δ u u' Z

def RepAtTup : Prop :=
  Pre M δ u u' F0 what₂ → ∀ (γ : TermDef.Term D u u' F0 what₂) (w : Point D.host.E (D.R.rS + 1)),
    Gpt (D.mem u).A.T (D.mem u').A.T w ≠ 0 → ∀ Z : PairVal.MatR D, AtMat w Z → EligAt γ w →
      locT M δ γ = tupZ M δ u u' Z → RepIn u u' F0 what₂ γ Z

def OrbZT : Prop :=
  Pre M δ u u' F0 what₂ → ∀ (γ : TermDef.Term D u u' F0 what₂) (w : Point D.host.E (D.R.rS + 1)) (Z : PairVal.MatR D),
    EligAt γ w → AtMat w Z → RepIn u u' F0 what₂ γ Z →
      (PairVal.orbT D u u' F0 what₂ γ (zT γ)).encard = (PairVal.orbT D u u' F0 what₂ γ Z).encard

end Steps

end Formalism.L2.SG.Pf.FibPart
end
end

