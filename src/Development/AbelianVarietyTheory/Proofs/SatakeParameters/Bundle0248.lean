module

public import Mathlib
public import Formalism.LocalToGlobal.Columns.KOneCharacterTrivialNearOne
public import Formalism.LocalToGlobal.Columns.ChainInstY
public import Formalism.LocalToGlobal.Columns.Bundle0036
public import Formalism.LocalToGlobal.Columns.Bundle0037
public import Formalism.LocalToGlobal.Columns.ChainTopLawB
public import Formalism.LocalToGlobal.Columns.Bundle0039
public import Formalism.LocalToGlobal.Columns.ChainTopLawTw
public import Formalism.LocalToGlobal.KernelLattices.KernelLocalFactors.TopLawQ
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.MemZmuOfPowPred
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.SmulCompSmul
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0241
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.XiAtPenultimateEqXiCpl1
public import Formalism.LocalToGlobal.KernelLattices.TopPin
public import Formalism.LocalToGlobal.Columns.Bundle0047
public import Formalism.LocalToGlobal.Columns.Bundle0048
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0175
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0240
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0242
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0243
public import Development.AbelianVarietyTheory.Statements.EllipticCurveLevels.HasLevel
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.RegPolOfRepOf
public import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.Imports
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0005
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.ArthurClozelStrongTC
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0009
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0236
public import GroundTheory.AutomorphicForms.SmoothRep
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.SameOffRefl
public import Formalism.LocalToGlobal.GroupLattices.TiedFamilies.Bundle0001
public import Formalism.SharpRestriction.GrowthBounds.ChartedClasses.ToLEInvApply
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.ExistsMidLevIff
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.CyclicStrongAtCusp

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.LastStepDatumLawTopLevelStabilizer
section
open Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV Formalism.L2.Col Formalism.L2.Ker NumberField IsDedekindDomain Classical

noncomputable section

namespace GlobalTheory.StabTopLaw


set_option maxHeartbeats 4000000 in
theorem xiTop_stab_law : ∀ {X : Fields} {Pr : Primes X} {R : Ranks} (Ch : Chars X Pr R.m) (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) {S : Set ℕ} (mu : Tup X.F X.E X.K S) (cst : LocCst X (rowSG Pr sel mu)) (L : ChIdx X Pr R (QE sel (mu : Chr X.F X.E X.K))) (G : ChGlob X R.m) (m2 : ℕ), X.Ok → Pr.Ok → IsSel X sel → (∀ i, Pr.g i ∈ S) → (∀ v, Pr.T v ∈ S) → L.Ok Ch sel mu cst G m2 → Ch.Ok → cst.sharp = true → R.m ≤ cst.A → (∀ j, j ≤ m2 + 1 → ∀ (b : L.β j) (P : rowSG Pr sel mu), P.1 ∈ Pr.vGs → L.h j b P = 1) → 2 * cst.M ≤ twTopDepth R → ∀ (u : Pr.Word) (p : ChPt (R := R) sel mu u (m2 + 1)) (Y : Set (Sp X.E (R.N (m2 + 1)))) (p' : ChPt (R := R) sel mu u (m2 + 1 + 1)) (a : FrmG (twLt Ch (m2 + 1 + 1)) (twTt (R := R) sel mu (m2 + 1 + 1))), Y ∈ ybSet sel mu cst p.deco.1.N → a • p' = p' → ∀ x, XiTop Ch sel mu cst (m2 + 1) p Y p' (a.1.1.toLinearMap ∘ₗ x) * ∏ P : rowSG Pr sel mu, muAt Ch sel mu cst (m2 + 1) P ((LinearEquiv.det a.1.1 : X.Eˣ) : X.E) = (((twLt Ch (m2 + 1 + 1)).chr a.2.1 * (twTt (R := R) sel mu (m2 + 1 + 1)).chr a.2.2 : X.Kˣ) : X.K) * XiTop Ch sel mu cst (m2 + 1) p Y p' x := by
  intro X Pr R Ch sel S mu cst L G m2 hX hPr hsel hgS hTS hL hCh hsh hA hb hMd u p Y p' a hY hfix x
  have hm : R.m = m2 + 2 := hL.hm
  have hc : cst.Ok := hL.cst_ok
  have hn : TopNum R (m2 + 1) := topNum_of hm
  have hS : QSep Pr sel mu := qSep_of sel mu hPr hsel hgS
  have hU : QUnif sel mu := qUnif_of sel mu hX hPr hsel
  have hLaw := topLawG_sym Ch sel mu cst control_phi_law hX hPr hm hsh
  have hRow := lastRow_colLevSym Ch hm
  choose κ' hκ' hκr' hκQ' using fun w : rowSG Pr sel mu =>
    frsF_smulQ sel mu u p' (twLt Ch (m2 + 1 + 1)) (twTt (R := R) sel mu (m2 + 1 + 1)) a w
  rw [hfix] at hκ'
  have e0 : phiT X.K p.deco.1 p'.deco.1 (a.1.1.toLinearMap ∘ₗ x) = phiT X.K p.deco.1 p'.deco.1 x := by
    have h := phiT_smul X.K p.deco p'.deco 1 1 a.1 (a.2.1 : GLG (E := X.E) (n := R.N (m2 + 1 + 1)) (SG := Pr.vGs)) x
    have hd : (a • p').deco = (a.1, (a.2.1 : GLG (E := X.E) (n := R.N (m2 + 1 + 1)) (SG := Pr.vGs))) • p'.deco := rfl
    rw [← hd, hfix, ← Prod.one_eq_mk, one_smul] at h
    exact h

  rw [XiTop_eq, XiTop_eq, e0]

  have hsym : ∀ w z, (frsF sel mu p' w).symm (a.1.1 z) = (κ' w).1.symm ((frsF sel mu p' w).symm z) := by
    intro w z
    have h := hκ' w
    generalize frsF sel mu p' w = F' at h ⊢
    rw [LinearEquiv.symm_apply_eq]
    calc a.1.1 z = (a.1.1 * F' * (κ' w).1) ((κ' w).1.symm (F'.symm z)) := by
          simp only [LinearEquiv.mul_apply, LinearEquiv.apply_symm_apply]
      _ = F' ((κ' w).1.symm (F'.symm z)) := by rw [← h]
  have hF : ∀ w, inFr (frsF sel mu p w) (frsF sel mu p' w) (a.1.1.toLinearMap ∘ₗ x) =
      (κ' w).1.symm.toLinearMap ∘ₗ inFr (frsF sel mu p w) (frsF sel mu p' w) x := by
    intro w
    apply LinearMap.ext
    intro v
    simp only [inFr, LinearMap.comp_apply, LinearEquiv.coe_coe]
    exact hsym w _

  have hdet : ∀ w, ((LinearEquiv.det a.1.1 : X.Eˣ) : X.E) = ((LinearEquiv.det ((κ' w)⁻¹).1 : X.Eˣ) : X.E) := by
    intro w
    have hd := congrArg (fun f => ((LinearEquiv.det f : X.Eˣ) : X.E)) (hκ' w)
    simp only [map_mul, Units.val_mul] at hd
    have hdF : ((LinearEquiv.det (frsF sel mu p' w) : X.Eˣ) : X.E) ≠ 0 := Units.ne_zero _
    have hdK : ((LinearEquiv.det (κ' w).1 : X.Eˣ) : X.E) ≠ 0 := Units.ne_zero _
    have hAK : ((LinearEquiv.det a.1.1 : X.Eˣ) : X.E) * ((LinearEquiv.det (κ' w).1 : X.Eˣ) : X.E) = 1 := by
      have h2 : ((LinearEquiv.det (frsF sel mu p' w) : X.Eˣ) : X.E) *
          (((LinearEquiv.det a.1.1 : X.Eˣ) : X.E) * ((LinearEquiv.det (κ' w).1 : X.Eˣ) : X.E)) =
          ((LinearEquiv.det (frsF sel mu p' w) : X.Eˣ) : X.E) * 1 := by
        rw [mul_one]
        conv_rhs => rw [hd]
        ring
      exact mul_left_cancel₀ hdF h2
    have e1 : ((LinearEquiv.det ((κ' w)⁻¹).1 : X.Eˣ) : X.E) = ((LinearEquiv.det (κ' w).1 : X.Eˣ) : X.E)⁻¹ := by
      show ((LinearEquiv.det ((κ' w).1)⁻¹ : X.Eˣ) : X.E) = _
      rw [map_inv, Units.val_inv_eq_inv_val]
    rw [e1]
    exact eq_inv_of_mul_eq_one_left hAK

  have hmu : ∀ w, muAt Ch sel mu cst (m2 + 1) w ((LinearEquiv.det a.1.1 : X.Eˣ) : X.E) =
      rhoT Ch sel mu (m2 + 1) w ((LinearEquiv.det (κ' w).1 : X.Eˣ) : X.E) := by
    intro w
    rw [hdet w]
    have hun : IsUnit (redP w.1 ((LinearEquiv.det ((κ' w)⁻¹).1 : X.Eˣ) : X.E)) :=
      isUnit_reduction_of_integralAt_inv (intAt_det _ ((κ' w)⁻¹).2) (intAt_det_inv _ ((κ' w)⁻¹).2) (Units.ne_zero _)
    have e2 := GlobalTheory.TopLaw.rhoT_inv (Ch := Ch) (sel := sel) (mu := mu) (m2 + 1) w (κ' w)⁻¹
    rw [inv_inv] at e2
    rw [e2]
    unfold muAt rhoS
    rw [GlobalTheory.LastSteps.locChar_unit _ _ hun]

  have hchr : (((twLt Ch (m2 + 1 + 1)).chr a.2.1 * (twTt (R := R) sel mu (m2 + 1 + 1)).chr a.2.2 : X.Kˣ) : X.K) =
      ∏ w : rowSG Pr sel mu,
        (if hw : w.1 ∈ Pr.vGs then
          (((twLt Ch (m2 + 1 + 1) ⟨w.1, hw⟩).lam ⟨(a.2.1 : GLG (E := X.E) (n := R.N (m2 + 1 + 1)) (SG := Pr.vGs)) ⟨w.1, hw⟩, a.2.1.2 _ (Set.mem_univ _)⟩ : X.Kˣ) : X.K)
        else
          (((twTt (R := R) sel mu (m2 + 1 + 1) ⟨w.1, (Finset.mem_union.mp w.2).resolve_left hw⟩).lam
              ⟨(a.2.2 : GLQ X.E (R.N (m2 + 1 + 1)) (QE sel (mu : Chr X.F X.E X.K))) ⟨w.1, (Finset.mem_union.mp w.2).resolve_left hw⟩,
                a.2.2.2 _ (Set.mem_univ _)⟩ : X.Kˣ) : X.K)) := by
    rw [prod_uSG_dite hS
      (fun w => (((twLt Ch (m2 + 1 + 1) w).lam ⟨(a.2.1 : GLG (E := X.E) (n := R.N (m2 + 1 + 1)) (SG := Pr.vGs)) w, a.2.1.2 _ (Set.mem_univ _)⟩ : X.Kˣ) : X.K))
      (fun Q => (((twTt (R := R) sel mu (m2 + 1 + 1) Q).lam ⟨(a.2.2 : GLQ X.E (R.N (m2 + 1 + 1)) (QE sel (mu : Chr X.F X.E X.K))) Q,
        a.2.2.2 _ (Set.mem_univ _)⟩ : X.Kˣ) : X.K))]
    rw [Units.val_mul, levFam_chr_apply_coe]
    congr 1
    exact piChar_apply_coe' _ _ a.2.2

  have hper : ∀ w : rowSG Pr sel mu,
      muAt Ch sel mu cst (m2 + 1) w ((LinearEquiv.det a.1.1 : X.Eˣ) : X.E) *
        topDat Ch sel mu cst (m2 + 1) w (inFr (frsF sel mu p w) (frsF sel mu p' w) (a.1.1.toLinearMap ∘ₗ x)) ((frsF sel mu p w).symm (repY Y)) =
      (if hw : w.1 ∈ Pr.vGs then
          (((twLt Ch (m2 + 1 + 1) ⟨w.1, hw⟩).lam ⟨(a.2.1 : GLG (E := X.E) (n := R.N (m2 + 1 + 1)) (SG := Pr.vGs)) ⟨w.1, hw⟩, a.2.1.2 _ (Set.mem_univ _)⟩ : X.Kˣ) : X.K)
        else
          (((twTt (R := R) sel mu (m2 + 1 + 1) ⟨w.1, (Finset.mem_union.mp w.2).resolve_left hw⟩).lam
              ⟨(a.2.2 : GLQ X.E (R.N (m2 + 1 + 1)) (QE sel (mu : Chr X.F X.E X.K))) ⟨w.1, (Finset.mem_union.mp w.2).resolve_left hw⟩,
                a.2.2.2 _ (Set.mem_univ _)⟩ : X.Kˣ) : X.K)) *
        topDat Ch sel mu cst (m2 + 1) w (inFr (frsF sel mu p w) (frsF sel mu p' w) x) ((frsF sel mu p w).symm (repY Y)) := by
    intro w
    rw [hmu w, hF w]
    have hFst : ∀ z, z ∈ localization₂ w.1.asIdeal p.deco.1.N → (frsF sel mu p w).symm z ∈ stdAt X.E (R.N (m2 + 1)) w.1 := by
      intro z hz
      apply (frsF_isFr sel mu p w _).1
      rw [LinearEquiv.apply_symm_apply]
      exact hz
    by_cases hw : w.1 ∈ Pr.vGs
    · rw [dite_eq_left hw]
      obtain ⟨hne, -, hqm⟩ := ybSet_props2 sel mu cst hY w hw
      have hr0 := representative_mem hne
      have hq : ((qOf w.1 : ℕ) : X.E) • (frsF sel mu p w).symm (repY Y) ∈ stdAt X.E (R.N (m2 + 1)) w.1 := by
        rw [← LinearEquiv.map_smul]
        exact hFst _ (hqm _ hr0)
      have key := topDat_law hc hn hLaw hRow w hw 1 ⟨(a.2.1 : GLG (E := X.E) (n := R.N (m2 + 1 + 1)) (SG := Pr.vGs)) ⟨w.1, hw⟩, a.2.1.2 _ (Set.mem_univ _)⟩
        1 (κ' w) (fun z _ => by simp) (hκr' w hw) (ciQ_notMem_sq hX hPr hw)
        (inFr (frsF sel mu p w) (frsF sel mu p' w) x) ((frsF sel mu p w).symm (repY Y)) ((frsF sel mu p w).symm (repY Y)) (by simp) hq
      have h1 : rhoS Ch sel mu (m2 + 1) w ((LinearEquiv.det ((1 : ↥(GLint X.E (R.N (m2 + 1)) w.1)) : Sp X.E (R.N (m2 + 1)) ≃ₗ[X.E] Sp X.E (R.N (m2 + 1))) : X.Eˣ) : X.E) = 1 := by
        simp [rhoS, LocE.unitV, redP_one]
      rw [h1, one_mul, map_one, inv_one, Units.val_one, mul_one] at key
      exact key
    · rw [dite_eq_right hw]
      obtain ⟨hne, hqm⟩ := coupling_index_scaled_mem_local sel mu cst hY w hw
      have hr0 := representative_mem hne
      have hq : ((qOf w.1 : X.E) ^ cst.M) • (frsF sel mu p w).symm (repY Y) ∈ stdAt X.E (R.N (m2 + 1)) w.1 := by
        rw [← LinearEquiv.map_smul]
        exact hFst _ (hqm _ hr0)
      have hQw := (Finset.mem_union.mp w.2).resolve_left hw
      have hc' : (κ' w)⁻¹ ∈ (twTt (R := R) sel mu (m2 + 1 + 1) ⟨w.1, hQw⟩).H := by
        rw [hκQ' w hw, inv_inv]
        exact a.2.2.2 _ (Set.mem_univ _)
      have key := GlobalTheory.T.twTt_k1Depth_twice_m Ch sel mu cst w hw (κ' w) hc' (inFr (frsF sel mu p w) (frsF sel mu p' w) x) ((frsF sel mu p w).symm (repY Y))
        hm hc (hU w.1 hQw) (hL.depthQ w hw) hMd hq
      have e4 : (⟨(κ' w)⁻¹, hc'⟩ : ↥(twTt (R := R) sel mu (m2 + 1 + 1) ⟨w.1, hQw⟩).H) =
          ⟨(a.2.2 : GLQ X.E (R.N (m2 + 1 + 1)) (QE sel (mu : Chr X.F X.E X.K))) ⟨w.1, hQw⟩, a.2.2.2 _ (Set.mem_univ _)⟩ :=
        Subtype.ext (by show (κ' w)⁻¹ = _; rw [hκQ' w hw, inv_inv])
      rw [e4] at key
      exact key
  rw [hchr]
  have := prod_mul_eq_of_forall_cross_mul_eq _ _ _ _ (phiT X.K p.deco.1 p'.deco.1 x) hper
  linear_combination this

end GlobalTheory.StabTopLaw
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.LevelQuotientEqTwistedTop
section
noncomputable section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker GlobalTheory.Mem.Col2 GlobalTheory.TopStep

namespace GlobalTheory.TopLevQ

section Gen

variable {E K : Type} [Field E] [NumberField E] [StarRing E] [Field K]

theorem lamQB_prinCong (P : HeightOneSpectrum (𝓞 E)) (ξ : (𝓞 E ⧸ P.asIdeal)ˣ →* Kˣ) {N : ℕ} (r c : ℕ) (hc : 0 < c)
    (k : GLint E N P) (hk : k ∈ prinCong N P c) : LocE.lamQB ξ r N k.1.toLinearMap = 1 := by
  have h1 := redGL_of_prinCong hc hk
  refine twLamQB_red_one P ξ le_rfl k.1 fun s t _ _ _ _ => ⟨glint_entry k s t, ?_⟩
  have h2 := congrArg (fun M : GL (Fin N) (𝓞 E ⧸ P.asIdeal) => (M : Matrix (Fin N) (Fin N) (𝓞 E ⧸ P.asIdeal)) s t) h1
  simp only [redGL_val, Units.val_one, Matrix.one_apply] at h2
  exact h2

theorem levI_ext {N : ℕ} {P : HeightOneSpectrum (𝓞 E)} {A B : LevI E K N P} (e : A.H = B.H)
    (e' : ∀ k (h1 : k ∈ A.H) (h2 : k ∈ B.H), A.lam ⟨k, h1⟩ = B.lam ⟨k, h2⟩) : A = B := by
  obtain ⟨H, lam⟩ := A
  obtain ⟨H', lam'⟩ := B
  obtain rfl : H = H' := e
  obtain rfl : lam = lam' := MonoidHom.ext fun a => e' a.1 a.2 a.2
  rfl

theorem level_congruence_eq_twisted_k1 (P : HeightOneSpectrum (𝓞 E)) (hu : ((qOf P : ℕ) : 𝓞 E) ∉ P.asIdeal ^ 2) (ξ : (𝓞 E ⧸ P.asIdeal)ˣ →* Kˣ)
    {N n : ℕ} (hN : N = n + 1) (r b c : ℕ) (hn : n = r + b) :
    levCong hN P c ⟨HQ (𝓞 E ⧸ P.asIdeal) n r b, (lamQ ξ n r b)⁻¹⟩ = kOneLevel P N r (c + 1) ξ := by
  set l : Lev (𝓞 E ⧸ P.asIdeal) K n := ⟨HQ (𝓞 E ⧸ P.asIdeal) n r b, (lamQ ξ n r b)⁻¹⟩
  have hH : (levCong hN P c l).H = twK1H P N r (c + 1) := by
    refine le_antisymm (sup_le ?_ (_root_.GlobalTheory.PrincipalCongruenceLevelK1.principal_congruence_le_level_k1 P r (c + 1) c.succ_pos)) fun g hg => ?_
    · rintro _ ⟨j, hj, rfl⟩
      exact _root_.GlobalTheory.TopStep.ext_mem_twisted_k1_level P hu hN r b (c + 1) hn j hj
    · obtain ⟨j, hj, hb⟩ := _root_.GlobalTheory.BlockDecompositionK1.exists_block_of_twisted_k1 P hN r b c hn g hg
      exact (mem_levCong hN c l g).2 ⟨j, hj, hb⟩
  refine levI_ext hH fun k h1 h2 => ?_
  obtain ⟨j, hj, hb⟩ := (mem_levCong hN c l k).1 h1
  rw [levCong_lam hN c l h1 hj hb]
  apply Units.ext
  have hjK : extI hN P j ∈ twK1H P N r (c + 1) := _root_.GlobalTheory.TopStep.ext_mem_twisted_k1_level P hu hN r b (c + 1) hn j hj
  have hbK : (extI hN P j)⁻¹ * k ∈ twK1H P N r (c + 1) := _root_.GlobalTheory.PrincipalCongruenceLevelK1.principal_congruence_le_level_k1 P r (c + 1) c.succ_pos hb
  have hk : (⟨k, h2⟩ : twK1H P N r (c + 1)) = ⟨_, hjK⟩ * ⟨_, hbK⟩ := Subtype.ext (mul_inv_cancel_left _ _).symm
  show _ = ((kOneCharacter P N r (c + 1) ξ).toHomUnits ⟨k, h2⟩ : K)
  rw [MonoidHom.coe_toHomUnits, hk, map_mul]
  show _ = LocE.lamQB ξ r N (extI hN P j).1.toLinearMap * LocE.lamQB ξ r N ((extI hN P j)⁻¹ * k).1.toLinearMap
  rw [lamQB_prinCong P ξ r (c + 1) c.succ_pos _ hb, mul_one, extI_val, _root_.GlobalTheory.SumRowType.lamQB_sumE P ξ hN r (by omega) j.1,
    GlobalTheory.TopLaw.lamQB_eq_red ξ hn j hj]
  rfl

end Gen

section Top

theorem levQTop_eq_twTt : ∀ (X : Fields) (Pr : Primes X) (R : Ranks) (Ch : Chars X Pr R.m) (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) (S : Set ℕ) (mu : Tup X.F X.E X.K S), X.Ok → Pr.Ok → IsSel X sel → (∀ i, Pr.g i ∈ S) → (∀ v, Pr.T v ∈ S) → levQTop R sel mu (4 * R.m) = twTt (R := R) sel mu R.m := by
  intro X Pr R _ sel S mu hX hPr hsel _ _
  funext Q
  have hu : ((qOf Q.1 : ℕ) : 𝓞 X.E) ∉ Q.1.asIdeal ^ 2 :=
    (GlobalTheory.ColPeriod.levelPrimes X Pr sel S mu hX hPr hsel ⟨Q.1, by classical exact Finset.mem_union_right _ Q.2⟩).1.2
  exact level_congruence_eq_twisted_k1 Q.1 hu _ (N_m_succ R) R.r (R.m * R.t) (4 * R.m) (rank_X'_eq R)

end Top
end GlobalTheory.TopLevQ
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.LocalOperatorActsByLocalComponentScalar
section
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.GalCut GlobalTheory.UnitaryBC GlobalTheory.Cong GlobalTheory.Published GlobalTheory.AboveL

noncomputable section

namespace GlobalTheory.LocOpAct

variable {G : Type} [Group G] {V : Type} [AddCommGroup V] [Module ℂ V]

theorem cosetSum_mem_fixed (ρ : Representation ℂ G V) {K N : Subgroup G} [Fintype (K ⧸ N.subgroupOf K)] {v : V}
    (hv : v ∈ GroundTheory.Automorphic.fixedVectors ρ N) :
    GroundTheory.Automorphic.cosetSum ρ K N v ∈ GroundTheory.Automorphic.fixedVectors ρ K := by
  intro k hk
  set_option synthInstance.maxHeartbeats 100000 in
    rw [GroundTheory.Automorphic.cosetSum_apply, map_sum]
  refine Fintype.sum_equiv (MulAction.toPerm (⟨k, hk⟩ : K)) _ _ fun q => ?_
  rw [← Module.End.mul_apply, ← map_mul]
  have := GroundTheory.Automorphic.act_eq_of_mk_eq ρ hv (a := ⟨k, hk⟩ * Quotient.out q)
    (b := Quotient.out ((⟨k, hk⟩ : K) • q)) (by
      rw [QuotientGroup.out_eq']; conv_rhs => rw [← QuotientGroup.out_eq' q]
      rfl)
  simpa using this

theorem opOf_eq (ρ : Representation ℂ G V) (f : G →₀ ℂ) (v : V) :
    GlobalTheory.Cong.opOf ρ f v = (f.sum fun g c => c • ρ g) v := by
  simp [GlobalTheory.Cong.opOf, Finsupp.sum, LinearMap.sum_apply]

theorem opOf_map {W : Type} [AddCommGroup W] [Module ℂ W] (ρ : Representation ℂ G V)
    (τ : Representation ℂ G W) (F : V →ₗ[ℂ] W) (hF : ∀ g v, F (ρ g v) = τ g (F v)) (f : G →₀ ℂ) (v : V) :
    F (GlobalTheory.Cong.opOf ρ f v) = GlobalTheory.Cong.opOf τ f (F v) := by
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [GlobalTheory.Cong.opOf, Finsupp.sum, map_sum, map_smul, hF]

end GlobalTheory.LocOpAct

theorem GlobalTheory.Cong.opOf_locU_eq_smul : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (a : ℕ) (w : HeightOneSpectrum (𝓞 E)), IsSplitAt w → ∀ (Kw : Subgroup (GL (Fin a) (w.adicCompletion E))), IsCompact (Kw : Set (GL (Fin a) (w.adicCompletion E))) → IsOpen (Kw : Set (GL (Fin a) (w.adicCompletion E))) → ∀ (f : GL (Fin a) (w.adicCompletion E) →₀ ℂ) (z : SmIrr (GL (Fin a) (w.adicCompletion E)) → ℂ), (∀ σ : SmIrr (GL (Fin a) (w.adicCompletion E)), ∀ v ∈ GlobalTheory.PRep.fixed σ.ρ Kw, opOf σ.ρ f v = z σ • v) → ∃ f' : UA E a →₀ ℂ, (∀ g ∈ f'.support, g ∈ locU a w ∧ f' g = f (cLoc w g)) ∧ ∀ U : Submodule ℂ (UA E a → ℂ), IsAutRepU U → ∀ σ : SmIrr (GL (Fin a) (w.adicCompletion E)), IsCompAlong U (locU a w) ((cLoc w).comp (locU a w).subtype) σ.ρ → ∀ φ ∈ U, (∀ x ∈ locU a w, cLoc w x ∈ Kw → RU E a x φ = φ) → opOf (RU E a) f' φ = z σ • φ := by
  classical
  intro E _ _ _ a w hw Kw hKc hKo f z hf
  obtain ⟨hbij, -, -⟩ := GlobalTheory.T.definiteUnitaryLocalComponent_splitPlace_homeomorph E a w hw
  let e : locU a w ≃* GL (Fin a) (w.adicCompletion E) :=
    MulEquiv.ofBijective ((cLoc w).comp (locU a w).subtype) hbij
  let j : GL (Fin a) (w.adicCompletion E) →* UA E a := (locU a w).subtype.comp e.symm.toMonoidHom
  let ρ' : Representation ℂ (GL (Fin a) (w.adicCompletion E)) (UA E a → ℂ) := (RU E a).comp j
  have hcj : ∀ g, cLoc w (j g) = g := fun g => e.apply_symm_apply g
  have hinj : Function.Injective j := Subtype.val_injective.comp e.symm.injective
  haveI : CompactSpace Kw := isCompact_iff_compactSpace.1 hKc
  have hfin : ∀ N : Subgroup (GL (Fin a) (w.adicCompletion E)), IsOpen (N : Set (GL (Fin a) (w.adicCompletion E))) →
      Finite (Kw ⧸ N.subgroupOf Kw) := fun N hN =>
    Subgroup.quotient_finite_of_isOpen _ (by rw [Subgroup.coe_subgroupOf]; exact hN.preimage continuous_subtype_val)
  refine ⟨f.mapDomain j, ?_, ?_⟩
  · intro g hg
    obtain ⟨h, -, rfl⟩ := Finset.mem_image.1 (Finsupp.mapDomain_support hg)
    exact ⟨(e.symm h).2, by rw [Finsupp.mapDomain_apply_of_injective hinj, hcj]⟩
  · intro U hU σ hσ φ hφU hφK
    have hop : ∀ ψ, opOf (RU E a) (f.mapDomain j) ψ = opOf ρ' f ψ := by
      intro ψ
      simp only [GlobalTheory.Cong.opOf]
      rw [Finsupp.sum_mapDomain_index (by intro b; simp) (by intro b c₁ c₂; simp [add_smul])]
      rfl
    rw [hop]
    have hFint : ∀ (F : {F : σ.V →ₗ[ℂ] (UA E a → ℂ) // (∀ v, F v ∈ U) ∧
        ∀ (x : locU a w) v, F (σ.ρ (cLoc w x) v) = RU E a x (F v)}) g v, F.1 (σ.ρ g v) = ρ' g (F.1 v) := by
      intro F g v
      have h := F.2.2 (e.symm g) v
      have h2 : cLoc w ((e.symm g : locU a w) : UA E a) = g := hcj g
      rw [h2] at h
      exact h
    let T : Module.End ℂ (UA E a → ℂ) := (f.sum fun g c => c • ρ' g) - z σ • 1
    have hT : ∀ ψ, T ψ = opOf ρ' f ψ - z σ • ψ := fun ψ => by
      rw [GlobalTheory.LocOpAct.opOf_eq]; rfl
    have key := GlobalTheory.T.autRepDefiniteUnitary_spanned_by_split_component E a U hU w hw σ hσ φ hφU
    have hC : ∃ N : Subgroup (GL (Fin a) (w.adicCompletion E)), IsOpen (N : Set (GL (Fin a) (w.adicCompletion E))) ∧
        ∀ N' : Subgroup (GL (Fin a) (w.adicCompletion E)), IsOpen (N' : Set (GL (Fin a) (w.adicCompletion E))) → N' ≤ N →
          T (GroundTheory.Automorphic.cosetSum ρ' Kw N' φ) = 0 := by
      refine Submodule.iSup_induction _ (motive := fun ψ => ∃ N : Subgroup (GL (Fin a) (w.adicCompletion E)),
        IsOpen (N : Set (GL (Fin a) (w.adicCompletion E))) ∧
        ∀ N' : Subgroup (GL (Fin a) (w.adicCompletion E)), IsOpen (N' : Set (GL (Fin a) (w.adicCompletion E))) → N' ≤ N →
          T (GroundTheory.Automorphic.cosetSum ρ' Kw N' ψ) = 0) key ?_ ?_ ?_
      · rintro F _ ⟨v, rfl⟩
        refine ⟨GroundTheory.Automorphic.stabilizerOf σ.ρ v, σ.smooth v, fun N' hN' hle => ?_⟩
        haveI := hfin N' hN'
        haveI := Fintype.ofFinite (Kw ⧸ N'.subgroupOf Kw)
        have hv : v ∈ GroundTheory.Automorphic.fixedVectors σ.ρ N' := fun n hn => hle hn
        have hu := GlobalTheory.LocOpAct.cosetSum_mem_fixed σ.ρ (K := Kw) hv
        have hcs : GroundTheory.Automorphic.cosetSum ρ' Kw N' (F.1 v) = F.1 (GroundTheory.Automorphic.cosetSum σ.ρ Kw N' v) := by
          set_option synthInstance.maxHeartbeats 100000 in
            rw [GroundTheory.Automorphic.cosetSum_apply, GroundTheory.Automorphic.cosetSum_apply, map_sum]
          simp only [hFint]
        have hfix : GroundTheory.Automorphic.cosetSum σ.ρ Kw N' v ∈ GlobalTheory.PRep.fixed σ.ρ Kw := fun k => by
          show σ.ρ k _ = ((1 : Kw →* ℂˣ) k : ℂ) • _
          simp [hu k k.2]
        rw [hcs, hT, ← GlobalTheory.LocOpAct.opOf_map σ.ρ ρ' F.1 (hFint F) f, hf σ _ hfix, map_smul, sub_self]
      · exact ⟨⊤, by simp, fun N' _ _ => by simp⟩
      · rintro x y ⟨N₁, h₁, hx⟩ ⟨N₂, h₂, hy⟩
        refine ⟨N₁ ⊓ N₂, by rw [Subgroup.coe_inf]; exact h₁.inter h₂, fun N' hN' hle => ?_⟩
        rw [map_add (f := _), map_add (f := _), hx N' hN' (hle.trans inf_le_left), hy N' hN' (hle.trans inf_le_right), add_zero]
    obtain ⟨N, hN, hNφ⟩ := hC
    haveI := hfin N hN
    haveI := Fintype.ofFinite (Kw ⧸ N.subgroupOf Kw)
    have hφ : φ ∈ GroundTheory.Automorphic.fixedVectors ρ' Kw := fun k hk => by
      have := hφK (j k) (e.symm k).2 (by rw [hcj]; exact hk)
      exact this
    have h0 := hNφ N hN le_rfl
    rw [GroundTheory.Automorphic.cosetSum_of_mem ρ' hφ, map_smul] at h0
    have hne : (Fintype.card (Kw ⧸ N.subgroupOf Kw) : ℂ) ≠ 0 := Nat.cast_ne_zero.2 Fintype.card_ne_zero
    rw [smul_eq_zero] at h0
    have h1 := h0.resolve_left hne
    rw [hT, sub_eq_zero] at h1
    exact h1
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.LocalisationInverseHalfDifferentEqOneUnramified
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.G Formalism.L2.G Formalism.L2.G.Cmp Formalism.L2.Forms Formalism.UG Formalism.L2.DIV Formalism.L2.G.Pend Formalism.L2.PairingIndexBounds.F Formalism.MainNotions.G.KAat GlobalTheory.TwV GlobalTheory.TwV.Xc TensorProduct

namespace GlobalTheory.TwV.Xc

theorem not_dvd_absDifferent_of_not_mem_sq {E : Type} [Field E] [NumberField E] (p : ℕ) (hp : p.Prime)
    (P : HeightOneSpectrum (𝓞 E)) (h1 : ((p : ℕ) : 𝓞 E) ∈ P.asIdeal)
    (h2 : ((p : ℕ) : 𝓞 E) ∉ P.asIdeal ^ 2) : ¬ P.asIdeal ∣ differentIdeal ℤ (𝓞 E) := by
  have hP : P.asIdeal.IsMaximal := P.isMaximal
  have : Fact p.Prime := ⟨hp⟩
  have : NeZero p := ⟨hp.ne_zero⟩
  have : (Ideal.span {((p : ℕ) : ℤ)}).IsMaximal := Int.ideal_span_isMaximal_of_prime _
  have : Finite (ℤ ⧸ Ideal.span {((p : ℕ) : ℤ)}) :=
    Finite.of_equiv _ (Int.quotientSpanNatEquivZMod p).toEquiv.symm
  have hmap : Ideal.map (algebraMap ℤ (𝓞 E)) (Ideal.span {((p : ℕ) : ℤ)}) =
      Ideal.span {((p : ℕ) : 𝓞 E)} := by
    rw [Ideal.map_span, Set.image_singleton, map_natCast]
  have hle : Ideal.map (algebraMap ℤ (𝓞 E)) (Ideal.span {((p : ℕ) : ℤ)}) ≤ P.asIdeal := by
    rw [hmap, Ideal.span_singleton_le_iff_mem]
    exact h1
  obtain ⟨Q, hQ⟩ := Ideal.dvd_iff_le.2 hle
  have hcop : IsCoprime P.asIdeal Q := by
    rw [Ideal.isCoprime_iff_sup_eq]
    by_contra hne
    have heq := hP.eq_of_le hne le_sup_left
    have hQP : Q ≤ P.asIdeal := heq ▸ le_sup_right
    apply h2
    have hmem : ((p : ℕ) : 𝓞 E) ∈
        Ideal.map (algebraMap ℤ (𝓞 E)) (Ideal.span {((p : ℕ) : ℤ)}) := by
      rw [hmap]; exact Ideal.subset_span rfl
    rw [hQ] at hmem
    rw [pow_two]
    exact Ideal.mul_mono_right hQP hmem
  exact not_dvd_differentIdeal_of_isCoprime ℤ P.asIdeal Q hcop hQ.symm

theorem inverseHalfDifferent_local_trivial_at_prime_norm : ∀ (D : D7) (p : ℕ), p.Prime → ∀ P : HeightOneSpectrum (𝓞 D.host.E), ((p : ℕ) : 𝓞 D.host.E) ∈ P.asIdeal → ((p : ℕ) : 𝓞 D.host.E) ∉ P.asIdeal ^ 2 → Formalism.HermitianLatticesTheory.localization₂ P.asIdeal (D.host.AA0 : Submodule (𝓞 D.host.E) D.host.E) = Formalism.HermitianLatticesTheory.localization₂ P.asIdeal (1 : Submodule (𝓞 D.host.E) D.host.E) := by
  intro D p hp P h1 h2
  have hnd := not_dvd_absDifferent_of_not_mem_sq p hp P h1 h2
  have ht : differentIdeal ℤ (𝓞 D.host.E) = differentIdeal (𝓞 D.host.K) (𝓞 D.host.E) *
      (differentIdeal ℤ (𝓞 D.host.K)).map (algebraMap (𝓞 D.host.K) (𝓞 D.host.E)) :=
    differentIdeal_eq_differentIdeal_mul_differentIdeal ℤ (𝓞 D.host.K) (𝓞 D.host.E)
  have hspec : D.host.𝔟 ∣ differentIdeal (𝓞 D.host.K) (𝓞 D.host.E) := ⟨_, D.host.𝔟_spec.1⟩
  have hn : ¬ D.host.𝔟 ≤ P.asIdeal := fun h => hnd (by
    rw [ht]
    exact ((Ideal.dvd_iff_le.2 h).trans hspec).mul_right _)
  obtain ⟨t, htb, htP⟩ := SetLike.not_le_iff_exists.1 hn
  have hb : ((D.host.𝔟 : Ideal (𝓞 D.host.E)) :
      FractionalIdeal (nonZeroDivisors (𝓞 D.host.E)) D.host.E) ≠ 0 :=
    FractionalIdeal.coeIdeal_ne_zero.2 fun h => hn (h ▸ bot_le)
  ext x
  constructor
  · rintro ⟨s, hs, hx⟩
    refine ⟨t * s, fun h => (P.isPrime.mem_or_mem h).elim htP hs, ?_⟩
    obtain ⟨u, hu⟩ := (FractionalIdeal.mem_one_iff _).1
      ((FractionalIdeal.mem_inv_iff hb).1 hx _ (FractionalIdeal.mem_coeIdeal_of_mem _ htb))
    rw [Submodule.mem_one]
    refine ⟨u, ?_⟩
    rw [hu, mul_smul, Algebra.smul_def t, mul_comm]
  · rintro ⟨s, hs, hx⟩
    refine ⟨s, hs, ?_⟩
    obtain ⟨u, hu⟩ := Submodule.mem_one.1 hx
    refine (FractionalIdeal.mem_inv_iff hb).2 fun y hy => ?_
    obtain ⟨z, -, rfl⟩ := (FractionalIdeal.mem_coeIdeal _).1 hy
    exact (FractionalIdeal.mem_one_iff _).2 ⟨u * z, by rw [map_mul, hu]⟩

end GlobalTheory.TwV.Xc
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.SupercuspidalSupportCharacters
section
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Polynomial
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp GlobalTheory.GLq
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.GalCut GlobalTheory.RoadU GlobalTheory.AboveL
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.supercuspidal_support_characters : ∀ (E : Type) [Field E] [NumberField E] (n : ℕ), 1 ≤ n → ∀ (w : HeightOneSpectrum (𝓞 E)) (σ : SmIrr (GL (Fin n) (w.adicCompletion E))) (B : Multiset ℂˣ), GlobalTheory.LFun.HasSatGL w σ.ρ B → ∃ (ξ : Fin n → ((w.adicCompletion E)ˣ →* ℂˣ)) (hξ : ∀ j, IsSmoothChar (ξ j)) (ϖ : (w.adicCompletion E)ˣ), HasSupport (IrrGL.of σ.ρ σ.smooth σ.irred).rep (chars ξ hξ) ∧ (∀ j (x : (w.adicCompletion E)ˣ), Valued.v (x : w.adicCompletion E) = 1 → ξ j x = 1) ∧ Valued.v (ϖ : w.adicCompletion E) = WithZero.exp (-1 : ℤ) ∧ B = Finset.univ.val.map fun j => ξ j ϖ := by
  first | (exact @GlobalTheory.SatSupp.hasSupport_of_hasSatGL) | (exact GlobalTheory.SatSupp.hasSupport_of_hasSatGL) | (intros; apply GlobalTheory.SatSupp.hasSupport_of_hasSatGL  <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.SupercuspidalSupportTwistNuCharactersStatement
section
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Polynomial
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp GlobalTheory.GLq
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.GalCut GlobalTheory.RoadU GlobalTheory.AboveL
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.supercuspidalSupport_twist_nu_characters : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [CharZero k] (x : IrrGL (k := k)) (n : ℕ) (ξ ξ' : Fin n → (kˣ →* ℂˣ)) (hξ : ∀ j, IsSmoothChar (ξ j)) (hξ' : ∀ j, IsSmoothChar (ξ' j)) (s : ℂ), (∀ j, ξ' j = ξ j * absPow k s) → (HasSupport x.rep (chars ξ hξ) ↔ HasSupport (x.nu s).rep (chars ξ' hξ')) ∧ (Unlinked (chars ξ hξ) ↔ Unlinked (chars ξ' hξ')) := by
  first | (exact @GlobalTheory.RoadU.TwistSupp.supp_nu_chars) | (exact GlobalTheory.RoadU.TwistSupp.supp_nu_chars) | (intros; apply GlobalTheory.RoadU.TwistSupp.supp_nu_chars  <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.WeilDeligneParamEqUnramifiedSatakeOfFrobeniusStatement
section
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Polynomial
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp GlobalTheory.GLq
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.GalCut GlobalTheory.RoadU GlobalTheory.AboveL
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.weilDeligneParam_eq_unramifiedSatake_of_frobenius : ∀ (Ω : Type) [Field Ω] (E : Type) [Field E] [NumberField E] [Algebra E Ω] [IsAlgClosure E Ω] (l : ℕ) [Fact l.Prime] (ι : Qbar l ≃+* ℂ) (n : ℕ) (r : G E Ω →* GL (Fin n) (Qbar l)), Continuous r → ∀ (w : HeightOneSpectrum (𝓞 E)) (hl : ((l : ℕ) : 𝓞 E) ∉ w.asIdeal) (A : ValuationSubring Ω) (h : IsPlaceOver A w), ∀ B : Multiset ℂˣ, UpperTheory.V.Af.FrobEig ι r w (UpperTheory.V.Af.algSat n (normV w) B) → wdOf h hl ι r = satWD h n B := by
  first | (exact @GlobalTheory.RoadU.wdOf_eq_satWD_of_frobEig) | (exact GlobalTheory.RoadU.wdOf_eq_satWD_of_frobEig) | (intros; apply GlobalTheory.RoadU.wdOf_eq_satWD_of_frobEig  <;> assumption)
end

