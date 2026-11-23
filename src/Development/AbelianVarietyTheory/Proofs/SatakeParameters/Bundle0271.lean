module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0260
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.SmulCompSmul
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ChartPointRightTranslateByLevelCoupledStep
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0023
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0025
public import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.RedPEqZeroOfDiv
public import Formalism.LocalToGlobal.KernelLattices.KernelLocalFactors.LocalProductMeasures.MqRowSGUnif
public import Formalism.SharpRestriction.GlobalSchurBounds.Joints
public import Formalism.LocalToGlobal.Columns.Bundle0035
public import Formalism.LocalToGlobal.GlobalTheory.GL6.PBwLocBases
public import Formalism.LocalToGlobal.LatticeGeometry.GeometryDefinitions.PNeatB
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0159
public import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.CsSpan
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.TrueColumnChoicesHeckeCharReferenceEqOne
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsFiniteAdeleBaseChangeEquiv
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0442
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.PointDecorationAgreeBelow
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.ExistsMidLevIff
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0269

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.LastStepLocalFactorSourceLawCoupledLevel
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.L2.DIV Formalism.L2.Col Formalism.MainNotions Formalism.L2.Ker GlobalTheory.TwU GlobalTheory.TwV GlobalTheory.TwTop GlobalTheory.TopStep
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.TopLawG

theorem locTopG_source : ∀ {X : Fields} {Pr : Primes X} {R : Ranks} {Ch : Chars X Pr R.m} {sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)}
  {S : Set ℕ} {mu : Tup X.F X.E X.K S} {cst : LocCst X (rowSG Pr sel mu)} {L : ChIdx X Pr R (QE sel (mu : Chr X.F X.E X.K))}
  {G : ChGlob X R.m} {m2 : ℕ}, X.Ok → Pr.Ok → IsSel X sel → L.Ok Ch sel mu cst G m2 → ∀ (b : L.β (m2 + 1)) (P : rowSG Pr sel mu), P.1 ∈ Pr.vGs →
  ∀ (g : Sp X.E (R.N (m2 + 1)) ≃ₗ[X.E] Sp X.E (R.N (m2 + 1))) (z : X.K), MidLev Ch sel mu cst (m2 + 1) P (L.h (m2 + 1) b P) g z →
  ∃ Gg : GLint X.E (R.N (m2 + 1)) P.1, Gg.1 = g ∧ ∀ (k : GLint X.E (R.N (m2 + 1)) P.1), redGL _ P.1 k = redGL _ P.1 Gg →
  ∀ (y : HomE X.E (R.N (m2 + 1)) (R.N (m2 + 1 + 1))) (y' y'' : Sp X.E (R.N (m2 + 1))),
    (∀ i, IntAt P.1 ((qOf P.1 : X.E) * y' i)) → k.1 y'' - y' ∈ stdAt X.E _ P.1 →
    (PhiTopG Ch mu cst.sharp (m2 + 1) (m2 + 1 + 1) (R.N (m2 + 1 + 1)) P.1
        (prXpG X.E (R.N (m2 + 1 + 1)) ∘ₗ (y ∘ₗ k.1.toLinearMap) ∘ₗ LinearMap.funLeft X.E X.E (Fin.castAdd (cOf R (m2 + 1)))) *
      ftY sel mu cst P (atNL X.E (R.N (m2 + 1 + 1)) (R.N (m2 + 1 + 1) - 1) ∘ₗ (y ∘ₗ k.1.toLinearMap)) y'') * rhoS Ch sel mu (m2 + 1) P ((LinearEquiv.det g : X.Eˣ) : X.E) =
      z * (PhiTopG Ch mu cst.sharp (m2 + 1) (m2 + 1 + 1) (R.N (m2 + 1 + 1)) P.1
        (prXpG X.E (R.N (m2 + 1 + 1)) ∘ₗ y ∘ₗ LinearMap.funLeft X.E X.E (Fin.castAdd (cOf R (m2 + 1)))) *
      ftY sel mu cst P (atNL X.E (R.N (m2 + 1 + 1)) (R.N (m2 + 1 + 1) - 1) ∘ₗ y) y') := by
  intro X Pr R Ch sel S mu cst L G m2 hX hPr _hsel hL b P hP g z hmid
  have hgC : g ∈ prCat (Pr := Pr) cst.sharp (m2 + 1) P.1 (L.h (m2 + 1) b P) :=
    (exists_midLev_iff Ch sel mu cst (m2 + 1) P (L.h (m2 + 1) b P) g).1 ⟨z, hmid⟩
  have hgI : g ∈ GLint X.E (R.N (m2 + 1)) P.1 := hL.int (m2 + 1) b P hgC
  refine ⟨⟨g, hgI⟩, rfl, ?_⟩
  intro k hk y y' y'' hy' hky
  obtain ⟨r, hr, hrg, hz⟩ := hmid
  have hred : ∀ x ∈ stdAt X.E (R.N (m2 + 1)) P.1, redV P.1 (g x) = (redGL _ P.1 k).1.mulVec (redV P.1 x) := by
    intro x hx
    rw [hk]
    exact redV_redGL (⟨g, hgI⟩ : GLint X.E (R.N (m2 + 1)) P.1) hx
  have hmem : redGL _ P.1 k ∈ (L.levG (m2 + 1) b ⟨P.1, hP⟩).H :=
    (hL.grpG (m2 + 1) b ⟨P.1, hP⟩ (redGL _ P.1 k)).2 ⟨g, hgC, hred⟩
  set c : X.Kˣ := (L.levG (m2 + 1) b ⟨P.1, hP⟩).lam ⟨redGL _ P.1 k, hmem⟩ with hcdef
  have hcz : (c : X.K) = z := by
    rw [hz]
    exact hL.chrG (m2 + 1) b ⟨P.1, hP⟩ ⟨redGL _ P.1 k, hmem⟩ g r hr hrg hred
  have hlev : GlobalTheory.TopLaw.LevAt (L.levG (m2 + 1) b) (L.levQ (m2 + 1) b) P k c :=
    ⟨fun _ => ⟨hmem, rfl⟩, fun _ h => absurd hP h⟩
  have hrho : rhoS Ch sel mu (m2 + 1) P ((LinearEquiv.det g : X.Eˣ) : X.E) =
      rhoS Ch sel mu (m2 + 1) P ((LinearEquiv.det k.1 : X.Eˣ) : X.E) := by
    unfold rhoS
    refine unitV_congr _ ?_
    rw [(det_glint k).2, ← redGL_val, hk, redGL_val]
    exact (det_glint (⟨g, hgI⟩ : GLint X.E (R.N (m2 + 1)) P.1)).2
  rw [hrho, ← hcz]
  have hm := hL.hm
  have key := GlobalTheory.TopLaw.locTop_source hX hPr hL hlev
  clear_value c
  clear hcdef hcz hrho hred hz hrg hr hmem
  revert key y
  cases R with
  | mk e k0 m t h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 =>
    change m = m2 + 2 at hm
    subst hm
    intro y key
    have := key y (fun _ => hy') (fun h => absurd hP h) (fun _ => hky) (fun h => absurd hP h)
    unfold locTop at this
    rw [PhiTopG_eq]
    exact this

end GlobalTheory.TopLawG
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.LastStepLocalFactorTargetLawTopLevel
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.L2.DIV Formalism.L2.Col Formalism.MainNotions Formalism.L2.Ker GlobalTheory.TwU GlobalTheory.TwV GlobalTheory.TwTop GlobalTheory.TopStep
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.TwTop

open GlobalTheory.DatumLaw GlobalTheory.TopLaw

variable {X : Fields} {Pr : Primes X} {R : Ranks} {Ch : Chars X Pr R.m}
  {sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)} {S : Set ℕ} {mu : Tup X.F X.E X.K S}
  {cst : LocCst X (rowSG Pr sel mu)} {m2 : ℕ}

theorem rowLevTop_glint {sharp : Bool} {n : ℕ} {P : HeightOneSpectrum (𝓞 X.E)} (hP : P ∈ Pr.vGs)
    {g : Sp X.E ((n - 1) + 0) ≃ₗ[X.E] Sp X.E ((n - 1) + 0)} (hg : g ∈ rowLevTop Pr R sharp n P) : g ∈ GLint X.E (n - 1) P := by
  unfold rowLevTop at hg
  rw [if_pos hP] at hg
  have h : g ∈ stabL X.E ((n - 1) + 0) (LocE.lamY P (qOf P) (n - 1) 0 fun i => i + 1) := by
    split_ifs at hg
    · exact hg.1
    · exact hg.1
  rw [GlobalTheory.TopLawSym.lamY_eq] at h
  exact h

theorem phiTop_rowLevTop (hm : R.m = m2 + 2) (sharp : Bool) {P : HeightOneSpectrum (𝓞 X.E)} (hP : P ∈ Pr.vGs)
    {g : Sp X.E ((R.N R.m - 1) + 0) ≃ₗ[X.E] Sp X.E ((R.N R.m - 1) + 0)} (hg : g ∈ rowLevTop Pr R sharp (R.N R.m) P)
    (x : HomE X.E (R.N (m2 + 1) + cOf R (m2 + 1)) ((R.N R.m - 1) + 0)) :
    PhiTop Ch mu sharp m2 P (g.toLinearMap ∘ₗ x) * LocE.unitV (chiP Ch P (m2 + 1)) ((LinearEquiv.det g : X.Eˣ) : X.E) =
      rowChrTop Ch mu sharp R.m (R.N R.m) P g.toLinearMap * PhiTop Ch mu sharp m2 P x := by
  obtain ⟨-, -, -, a4⟩ := ranks R (j := 0) (by omega)
  have a5 := r_le_X' R
  have b1 : R.N R.m - 1 + 0 = R.r + (m2 + 1) * R.t + R.t := by
    rw [add_zero, rank_X'_eq R, hm]; ring
  unfold rowLevTop at hg
  unfold PhiTop rowChrTop
  rw [if_pos hP] at hg
  rw [if_pos hP, if_pos hP]
  generalize R.N R.m - 1 = n at *
  generalize psi0P Ch P = ψ
  generalize chiP Ch P = χ
  rw [hm]
  split_ifs at hg ⊢
  · rw [DatumLaw.phiGS_eq]
    exact phiM_target _ _ (by omega) (by omega) b1 _ inf_le_left
      (fun g hg => levG_of_JGsym (by omega) a4 (by omega) hg) hg x
  · rw [phiG_eq, LocE.lamGB, lamGv_eq]
    exact phiM_target _ _ (by omega) (by omega) b1 _ inf_le_left
      (fun g hg => levG_of_JG (by omega) (by omega) hg) hg x

theorem locTop_topLev (hm : R.m = m2 + 2) (hc : cst.Ok) {P : rowSG Pr sel mu} (hq : ((qOf P.1 : ℕ) : 𝓞 X.E) ∉ P.1.asIdeal ^ 2)
    (hP : P.1 ∈ Pr.vGs) (g : Sp X.E (R.N R.m) ≃ₗ[X.E] Sp X.E (R.N R.m)) (z : X.K) (hg : TopLev Ch sel mu cst R.m P g z) :
    ∃ Gg : GLint X.E (R.N R.m) P.1, Gg.1 = g ∧ ∀ (k : GLint X.E (R.N R.m) P.1), redGL _ P.1 k = redGL _ P.1 Gg →
      ∀ (y : HomE X.E (R.N (m2 + 1)) (R.N R.m)) (y' : Sp X.E (R.N (m2 + 1))), (∀ i, IntAt P.1 ((qOf P.1 : X.E) * y' i)) →
        z * locTop Ch sel mu cst m2 P ((k⁻¹).1.toLinearMap ∘ₗ y) y' * rhoT Ch sel mu (m2 + 1) P ((LinearEquiv.det g : X.Eˣ) : X.E) =
          locTop Ch sel mu cst m2 P y y' := by
  classical
  obtain ⟨g', hg', h1, h2, rfl⟩ := hg
  let j : GLint X.E (R.N R.m - 1) P.1 := ⟨g', rowLevTop_glint hP hg'⟩
  have eg : (extI (N_m_succ R) P.1 j).1 = g := by
    refine LinearEquiv.ext fun v => ext_prH (N_m_succ R) ?_ ?_
    · exact (prH_sumE (N_m_succ R) _ _ _).trans (LinearMap.congr_fun h1 v).symm
    · refine (sumE_last (N_m_succ R) _ _ _).trans ?_
      rw [Units.val_one, one_mul]
      exact (atNL_last v).symm.trans ((LinearMap.congr_fun h2 v).symm.trans (atNL_last _))
  refine ⟨extI (N_m_succ R) P.1 j, eg, fun k hk y y' hy' => ?_⟩
  have e3 : (k⁻¹).1.toLinearMap ∘ₗ y = (k⁻¹ * extI (N_m_succ R) P.1 j).1.toLinearMap ∘ₗ
      ((extI (N_m_succ R) P.1 j⁻¹).1.toLinearMap ∘ₗ y) := by
    rw [map_inv]
    exact LinearMap.ext fun v => congrArg (k⁻¹).1 (LinearEquiv.apply_symm_apply (extI (N_m_succ R) P.1 j).1 (y v)).symm
  rw [e3, locTop_inv hm hc hP hq _ (by rw [map_mul, map_inv, hk, inv_mul_cancel]) _ hy', locTop_extI, ← eg]
  unfold rhoT
  rw [if_pos hP, unitV_det_ext _ (N_m_succ R) j _ rfl]
  have h3 := phiTop_rowLevTop (Ch := Ch) (mu := mu) hm cst.sharp hP hg' ((j⁻¹).1.toLinearMap ∘ₗ
    (prXp X.E R ∘ₗ y ∘ₗ LinearMap.funLeft X.E X.E (Fin.castAdd (cOf R (m2 + 1)))))
  have e4 : g'.toLinearMap ∘ₗ ((j⁻¹).1.toLinearMap ∘ₗ
      (prXp X.E R ∘ₗ y ∘ₗ LinearMap.funLeft X.E X.E (Fin.castAdd (cOf R (m2 + 1))))) =
      prXp X.E R ∘ₗ y ∘ₗ LinearMap.funLeft X.E X.E (Fin.castAdd (cOf R (m2 + 1))) :=
    LinearMap.ext fun v => g'.apply_symm_apply _
  rw [e4] at h3
  have hu : IsUnit (redP P.1 ((LinearEquiv.det j.1 : X.Eˣ) : X.E)) := by
    rw [(det_glint j).2, ← redGL_val, ← Matrix.isUnit_iff_isUnit_det]
    exact Units.isUnit _
  have h4 : LocE.unitV (chiP Ch P.1 (m2 + 1)) ((LinearEquiv.det g' : X.Eˣ) : X.E) *
      LocE.unitV (chiP Ch P.1 (m2 + 1))⁻¹ ((LinearEquiv.det j.1 : X.Eˣ) : X.E) = 1 := by
    rw [DatumLaw.unitV_eq, DatumLaw.unitV_eq, extendByZeroOffSubset_mul_left_of_mem_lattice]
    exact mul_inv_cancel₀ (unitCharacterExtendByZero_ne_zero_of_isUnit _ hu)
  unfold locTop
  rw [← mul_assoc, mul_right_comm]
  congr 1
  refine (congrArg (· * _) h3.symm).trans ?_
  rw [mul_assoc, h4, mul_one]

theorem topF_target_vG : ∀ {X : Fields} {Pr : Primes X} {R : Ranks} {Ch : Chars X Pr R.m} {sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)}
  {S : Set ℕ} {mu : Tup X.F X.E X.K S} {cst : LocCst X (rowSG Pr sel mu)} {L : ChIdx X Pr R (QE sel (mu : Chr X.F X.E X.K))}
  {G : ChGlob X R.m} {m2 : ℕ}, X.Ok → Pr.Ok → IsSel X sel → L.Ok Ch sel mu cst G m2 → ∀ (P : rowSG Pr sel mu), P.1 ∈ Pr.vGs →
  ∀ (g : Sp X.E (R.N (m2 + 1 + 1)) ≃ₗ[X.E] Sp X.E (R.N (m2 + 1 + 1))) (z : X.K), TopLev Ch sel mu cst (m2 + 1 + 1) P g z →
  ∃ Gg : GLint X.E (R.N (m2 + 1 + 1)) P.1, Gg.1 = g ∧ ∀ (k : GLint X.E (R.N (m2 + 1 + 1)) P.1), redGL _ P.1 k = redGL _ P.1 Gg →
  ∀ (y : HomE X.E (R.N (m2 + 1)) (R.N (m2 + 1 + 1))) (y' : Sp X.E (R.N (m2 + 1))),
    (∀ i, IntAt P.1 ((qOf P.1 : X.E) * y' i)) →
    z * (PhiTopG Ch mu cst.sharp (m2 + 1) (m2 + 1 + 1) (R.N (m2 + 1 + 1)) P.1
        (prXpG X.E (R.N (m2 + 1 + 1)) ∘ₗ ((k⁻¹).1.toLinearMap ∘ₗ y) ∘ₗ LinearMap.funLeft X.E X.E (Fin.castAdd (cOf R (m2 + 1)))) *
      ftY sel mu cst P (atNL X.E (R.N (m2 + 1 + 1)) (R.N (m2 + 1 + 1) - 1) ∘ₗ ((k⁻¹).1.toLinearMap ∘ₗ y)) y') * rhoT Ch sel mu (m2 + 1) P ((LinearEquiv.det g : X.Eˣ) : X.E) =
      (PhiTopG Ch mu cst.sharp (m2 + 1) (m2 + 1 + 1) (R.N (m2 + 1 + 1)) P.1
        (prXpG X.E (R.N (m2 + 1 + 1)) ∘ₗ y ∘ₗ LinearMap.funLeft X.E X.E (Fin.castAdd (cOf R (m2 + 1)))) *
      ftY sel mu cst P (atNL X.E (R.N (m2 + 1 + 1)) (R.N (m2 + 1 + 1) - 1) ∘ₗ y) y') := by
  intro X Pr R Ch sel S mu cst L G m2 hX hPr hsel hL P hP
  have hm : R.m = m2 + 1 + 1 := hL.hm
  generalize m2 + 1 + 1 = j at hm ⊢
  subst hm
  intro g z hg
  exact locTop_topLev hL.hm hL.cst_ok (GlobalTheory.ColPeriod.levelPrimes X Pr sel S mu hX hPr hsel P).1.2 hP g z hg

end GlobalTheory.TwTop

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.LevelFrameLiftUnitaryAutNearAdelicMatrixDepthOne
section
open NumberField IsDedekindDomain Matrix Formalism.BasicNotions Formalism.MainNotions Formalism.UG Formalism.L2.Col Formalism.L2.Ker Formalism.L2.DIV GlobalTheory.TwU GlobalTheory.TwV
open scoped TensorProduct

noncomputable section
namespace GlobalTheory.FrameRat

theorem nearAt_liftFr_smul : ∀ {D : D7} {X : Fields} (s : Seam D X) {n : ℕ} {ST SG : Finset (HeightOneSpectrum (𝓞 X.E))} (d : DecoSet (E := X.E) (n := n) (ST := ST) (SG := SG)) (w : SG) (g : UF X.E n), ((qOf w.1 : ℕ) : 𝓞 X.E) ∉ w.1.asIdeal ^ 2 → ∀ (y : GL (Fin n) (D.host.E ⊗[D.host.F] FiniteAdeleRing (𝓞 D.host.F) D.host.F)), NearAt (seamP s w.1) 1 y (seamGL s (d.1.liftFr w)) → NearAt (seamP s w.1) 1 (ratA D.host.F (seamGL s g.1) * y) (seamGL s (((g, (1 : GLG (E := X.E) (n := n) (SG := SG))) • d).1.liftFr w)) := by
  intro D X s n ST SG d w g hq y hy
  have hf := GlobalTheory.TopStep.liftFr_spec d.2 w
  have hf' : GlobalTheory.TopStep.IsLiftFr (d.1.act g.1 1) w (((g, (1 : GLG (E := X.E) (n := n) (SG := SG))) • d).1.liftFr w) := by
    have := GlobalTheory.TopStep.liftFr_spec ((g, (1 : GLG (E := X.E) (n := n) (SG := SG))) • d).2 w
    rwa [DecoSet.smul_val] at this
  set κ := GlobalTheory.TopStep.passFr g.1 1 hf hf' with hκ
  have hred : GlobalTheory.TopStep.redGL n w.1 κ = 1 := GlobalTheory.TopStep.redGL_passFr g.1 1 hf hf'
  have hred' : GlobalTheory.TopStep.redGL n w.1 κ⁻¹ = 1 := by rw [map_inv, hred, inv_one]
  have he : ((g, (1 : GLG (E := X.E) (n := n) (SG := SG))) • d).1.liftFr w = g.1 * d.1.liftFr w * (κ⁻¹).1 := by
    rw [InvMemClass.coe_inv, hκ]
    show _ = g.1 * d.1.liftFr w * ((((g, (1 : GLG (E := X.E) (n := n) (SG := SG))) • d).1.liftFr w)⁻¹ * g.1 * d.1.liftFr w)⁻¹
    group
  rw [he, map_mul, map_mul, mul_assoc, nearAt_rat_mul]
  exact GlobalTheory.CplPt.nearAt_mul 1 hy (GlobalTheory.CplPt.congAt_one_of_redGL s hq κ⁻¹ hred')

end GlobalTheory.FrameRat
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.LevelPrimeFunctionalsMoveRationalLatticeAut
section
open NumberField IsDedekindDomain Matrix Formalism.BasicNotions Formalism.MainNotions Formalism.UG Formalism.L2.Col Formalism.L2.Ker Formalism.L2.DIV GlobalTheory.TwU GlobalTheory.TwV
open scoped TensorProduct

namespace GlobalTheory.TwU


set_option maxHeartbeats 1000000 in
theorem funMoved_ratA_act : ∀ {D : D7} {X : Fields} (s : Seam D X) {i : ℕ} {hi : i ≤ D.R.m} {T : ℕ} {bad : Set (HeightOneSpectrum (𝓞 D.host.F))} (lev : Formalism.L2.Forms.StepLevel D.host.F D.host.E (Formalism.L2.Forms.sigD D) (Formalism.L2.Forms.gramN D i hi) T D.R.f bad) {ST SG : Finset (HeightOneSpectrum (𝓞 X.E))} (P : ST) (v : HeightOneSpectrum (𝓞 D.host.F)) (h : (T : 𝓞 D.host.F) ∈ v.asIdeal) (ι : lev.fM v h →+ 𝓞 X.E ⧸ P.1.asIdeal) (x : GL (Fin (D.R.N i)) (D.host.E ⊗[D.host.F] FiniteAdeleRing (𝓞 D.host.F) D.host.F)) (d : Deco X.E (D.R.N i) ST SG) (g : Sp X.E (D.R.N i) ≃ₗ[X.E] Sp X.E (D.R.N i)) (hh : GLG (E := X.E) (n := D.R.N i) (SG := SG)), FunMoved s lev P v h ι x d → FunMoved s lev P v h ι (ratA D.host.F (seamGL s g) * x) (d.act g hh) := by
  intro D X s i hi T bad lev ST SG P v h ι x d g hh H w hw z hz
  have hw' : g.symm w ∈ d.N := (Formalism.L2.Col.mem_gmap g d.N w).1 hw
  have key : pullV (F := D.host.F) (ratA D.host.F (seamGL s g) * x) (fun a => s.iE (w a)) =
      pullV (F := D.host.F) x (fun a => s.iE (g.symm w a)) := by
    unfold pullV
    rw [_root_.mul_inv_rev, Units.val_mul, ← Matrix.mulVec_mulVec]
    congr 1
    have e1 : (seamGL s g)⁻¹ = seamGL s g.symm := (map_inv (seamGL s) g).symm
    rw [← map_inv, e1]
    have := Formalism.MainNotions.G.KAat.bc_mulVec (F := D.host.F) (seamGL s g.symm) (fun a => s.iE (w a))
    rw [seamGL_mulVec] at this
    exact this
  show d.f P (g.symm w) = _
  exact H (g.symm w) hw' z (by rw [hz, key])

end GlobalTheory.TwU
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.MemLatSLatAdIff
section
open NumberField IsDedekindDomain Matrix Formalism.BasicNotions Formalism.UG Formalism.L2.Col Formalism.L2.PairingIndexBounds.F Formalism.MainNotions.G.KAat Formalism.L2.Forms Formalism.L2.Ker Formalism.MainNotions Formalism.L2.DIV Formalism.MainNotions.G GlobalTheory.TwU GlobalTheory.TwV
attribute [local instance] Formalism.BasicNotions.Host.cmStar

open scoped TensorProduct

namespace GlobalTheory.LocCarry

theorem prV_mulVec {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {N : ℕ}
    (v : HeightOneSpectrum (𝓞 F)) (M : Matrix (Fin N) (Fin N) (E ⊗[F] FiniteAdeleRing (𝓞 F) F))
    (w : Fin N → E ⊗[F] FiniteAdeleRing (𝓞 F) F) :
    (fun i => prV (E := E) v ((M *ᵥ w) i)) = M.map (prV (E := E) v) *ᵥ (fun i => prV (E := E) v (w i)) := by
  ext i
  set_option synthInstance.maxHeartbeats 100000 in
    simp [Matrix.mulVec, dotProduct, map_sum, map_mul]

theorem coe_bc_inv {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {N : ℕ}
    (v : HeightOneSpectrum (𝓞 F)) (x : GL (Fin N) (E ⊗[F] FiniteAdeleRing (𝓞 F) F)) :
    (((bc (prV (E := E) v) x)⁻¹ : GL (Fin N) (E ⊗[F] v.adicCompletion F)) :
      Matrix (Fin N) (Fin N) (E ⊗[F] v.adicCompletion F)) =
      ((x⁻¹ : GL (Fin N) (E ⊗[F] FiniteAdeleRing (𝓞 F) F)) : Matrix (Fin N) (Fin N) _).map (prV (E := E) v) := by
  rw [← map_inv]
  rfl

theorem coe_bc {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {N : ℕ}
    (v : HeightOneSpectrum (𝓞 F)) (x : GL (Fin N) (E ⊗[F] FiniteAdeleRing (𝓞 F) F)) :
    ((bc (prV (E := E) v) x : GL (Fin N) (E ⊗[F] v.adicCompletion F)) :
      Matrix (Fin N) (Fin N) (E ⊗[F] v.adicCompletion F)) =
      (x : Matrix (Fin N) (Fin N) _).map (prV (E := E) v) := rfl

theorem mem_latS_latAd_iff : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E] {N : ℕ}
    (x : GL (Fin N) (E ⊗[F] FiniteAdeleRing (𝓞 F) F)) (Lb : Submodule (𝓞 E) (Fin N → E)),
    Module.Finite (𝓞 E) Lb → Submodule.span E (Lb : Set (Fin N → E)) = ⊤ →
    ∀ (v : HeightOneSpectrum (𝓞 F)) (z : Fin N → E ⊗[F] v.adicCompletion F),
      z ∈ latS (F := F) (v.adicCompletion F) (intV E v) (latAd x Lb) ↔
        (((bc (prV (E := E) v) x)⁻¹ : GL (Fin N) (E ⊗[F] v.adicCompletion F)) : Matrix (Fin N) (Fin N) (E ⊗[F] v.adicCompletion F)) *ᵥ z ∈
          latS (F := F) (v.adicCompletion F) (intV E v) Lb := by
  intro F E _ _ _ _ _ _ N x Lb hfin hspan v z
  have hrec := Formalism.UG.P.span_recovery_of_integral_adelic_approx Formalism.UG.P.integral_adele_approximation_holds F E (Fin N) Lb hfin hspan x
  have hpr : ∀ y : Fin N → E ⊗[F] v.adicCompletion F,
      (fun i => prV (E := E) v (Formalism.UG.P.afsplitIE v (y i))) = y := fun y => by
    ext i; exact Formalism.UG.P.afsplit_prV_IE v (y i)
  have hlat : Formalism.L2.PairingIndexBounds.F.latAd x Lb = Formalism.UG.CS.globLat x Lb := Submodule.span_eq (Formalism.UG.CS.globLat x Lb)
  rw [hlat]
  constructor
  · intro hz
    have h1 := Formalism.L2.Geo.Def.PN.IE_latS (Formalism.UG.CS.globLat x Lb) v hz
    have h2 := (hrec _).1 h1
    have h3 := Formalism.L2.Geo.Def.PN.prV_latS Lb v h2
    rw [prV_mulVec, hpr, ← coe_bc_inv] at h3
    exact h3
  · intro hz
    have h1 := Formalism.L2.Geo.Def.PN.IE_latS Lb v hz
    set u : Fin N → E ⊗[F] FiniteAdeleRing (𝓞 F) F :=
      ((x : GL (Fin N) (E ⊗[F] FiniteAdeleRing (𝓞 F) F)) : Matrix (Fin N) (Fin N) _) *ᵥ
        (fun i => Formalism.UG.P.afsplitIE v (((((bc (prV (E := E) v) x)⁻¹ : GL (Fin N) (E ⊗[F] v.adicCompletion F)) :
          Matrix (Fin N) (Fin N) (E ⊗[F] v.adicCompletion F)) *ᵥ z) i)) with hu
    have h2 : u ∈ latS (F := F) (FiniteAdeleRing (𝓞 F) F)
        (tensInt (F := F) (FiniteAdeleRing (𝓞 F) F) (intOE E) (intAd F)) (Formalism.UG.CS.globLat x Lb) := by
      refine (hrec u).2 ?_
      rw [hu, Matrix.mulVec_mulVec, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.one_mulVec]
      exact h1
    have h3 := Formalism.L2.Geo.Def.PN.prV_latS (Formalism.UG.CS.globLat x Lb) v h2
    rw [hu, prV_mulVec, hpr, ← coe_bc, Matrix.mulVec_mulVec, ← Units.val_mul, mul_inv_cancel, Units.val_one,
      Matrix.one_mulVec] at h3
    exact h3

end GlobalTheory.LocCarry
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.OrthonormalCoordsConjUnitaryStandardForm
section
open NumberField IsDedekindDomain Matrix Formalism.BasicNotions Formalism.MainNotions Formalism.UG Formalism.L2.Col Formalism.L2.Ker Formalism.L2.DIV GlobalTheory.TwU GlobalTheory.TwV
open scoped TensorProduct

namespace GlobalTheory

theorem unitary_conj_orthonormal : ∀ (D : D7) {n : ℕ} (J : Matrix (Fin n) (Fin n) D.host.E) (crd γ : GL (Fin n) D.host.E), cT (Formalism.L2.Forms.sigD D : D.host.E →+* D.host.E) (crd : Matrix (Fin n) (Fin n) D.host.E) * (crd : Matrix (Fin n) (Fin n) D.host.E) = J → γ ∈ UJ (Formalism.L2.Forms.sigD D : D.host.E →+* D.host.E) J → cT (Formalism.L2.Forms.sigD D : D.host.E →+* D.host.E) ((crd * γ * crd⁻¹ : GL (Fin n) D.host.E) : Matrix (Fin n) (Fin n) D.host.E) * ((crd * γ * crd⁻¹ : GL (Fin n) D.host.E) : Matrix (Fin n) (Fin n) D.host.E) = 1 := by
  intro D n J crd γ hc hγ
  set σ : D.host.E →+* D.host.E := (Formalism.L2.Forms.sigD D : D.host.E →+* D.host.E) with hσ
  have hg : cT σ (γ : Matrix (Fin n) (Fin n) D.host.E) * J * (γ : Matrix (Fin n) (Fin n) D.host.E) = J := hγ
  have h1 : (crd : Matrix (Fin n) (Fin n) D.host.E) * ((crd⁻¹ : GL (Fin n) D.host.E) : Matrix (Fin n) (Fin n) D.host.E) = 1 := by
    rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
  simp only [Units.val_mul]
  rw [cT_mul, cT_mul]
  calc cT σ ((crd⁻¹ : GL (Fin n) D.host.E) : Matrix (Fin n) (Fin n) D.host.E) * (cT σ (γ : Matrix (Fin n) (Fin n) D.host.E) * cT σ (crd : Matrix (Fin n) (Fin n) D.host.E)) *
        ((crd : Matrix (Fin n) (Fin n) D.host.E) * (γ : Matrix (Fin n) (Fin n) D.host.E) * ((crd⁻¹ : GL (Fin n) D.host.E) : Matrix (Fin n) (Fin n) D.host.E))
      = cT σ ((crd⁻¹ : GL (Fin n) D.host.E) : Matrix (Fin n) (Fin n) D.host.E) * (cT σ (γ : Matrix (Fin n) (Fin n) D.host.E) * (cT σ (crd : Matrix (Fin n) (Fin n) D.host.E) * (crd : Matrix (Fin n) (Fin n) D.host.E)) * (γ : Matrix (Fin n) (Fin n) D.host.E)) * ((crd⁻¹ : GL (Fin n) D.host.E) : Matrix (Fin n) (Fin n) D.host.E) := by
        simp only [Matrix.mul_assoc]
    _ = cT σ ((crd⁻¹ : GL (Fin n) D.host.E) : Matrix (Fin n) (Fin n) D.host.E) * (cT σ (crd : Matrix (Fin n) (Fin n) D.host.E) * (crd : Matrix (Fin n) (Fin n) D.host.E)) * ((crd⁻¹ : GL (Fin n) D.host.E) : Matrix (Fin n) (Fin n) D.host.E) := by
        rw [hc, hg, ← hc]
    _ = cT σ ((crd : Matrix (Fin n) (Fin n) D.host.E) * ((crd⁻¹ : GL (Fin n) D.host.E) : Matrix (Fin n) (Fin n) D.host.E)) * ((crd : Matrix (Fin n) (Fin n) D.host.E) * ((crd⁻¹ : GL (Fin n) D.host.E) : Matrix (Fin n) (Fin n) D.host.E)) := by
        rw [cT_mul]; simp only [Matrix.mul_assoc]
    _ = 1 := by rw [h1, cT_one, Matrix.one_mul]

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.PlaceComponentEqOneIffComponentsOverEqOne
section
open NumberField IsDedekindDomain Formalism.L2.DIV
open scoped TensorProduct

namespace GlobalTheory.AfIsoPrV

theorem prV_eq_one_iff_afIso : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (v : HeightOneSpectrum (𝓞 F)) (z : AfE F E), Formalism.UG.prV (E := E) v z = 1 ↔ ∀ P : HeightOneSpectrum (𝓞 E), P.under (𝓞 F) = v → GlobalTheory.Mem.Col2.afIso F E z P = 1 := by
  intro F E _ _ _ _ _ v z
  obtain ⟨ι, hι⟩ := GlobalTheory.AdeleBaseChange.exists_toAd F E
  let ι' : AfE F E ≃+* FiniteAdeleRing (𝓞 E) E :=
    RingEquiv.ofBijective ι ⟨GlobalTheory.AdeleBaseChange.map_injective hι, GlobalTheory.AdeleBaseChange.map_surjective hι⟩
  have hiso : GlobalTheory.TwU.IsAdIso ι' :=
    ⟨GlobalTheory.AdeleBaseChange.map_tmul_one hι,
      fun y => ⟨fun hy => GlobalTheory.AdeleBaseChange.map_mem_int hι hy,
        fun hy => GlobalTheory.AdeleBaseChange.mem_int_of_map hι hy⟩⟩
  have he : ι z = GlobalTheory.Mem.Col2.afIso F E z := GlobalTheory.isAdIso_eq_afIso F E ι' hiso z
  rw [GlobalTheory.AdeleBaseChange.prV_eq_one_iff hι, he]

end GlobalTheory.AfIsoPrV
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.PointDecorationAgreeBelowStatement
section
open NumberField IsDedekindDomain Matrix Formalism.BasicNotions Formalism.UG Formalism.L2.Col Formalism.L2.PairingIndexBounds.F Formalism.MainNotions.G.KAat Formalism.L2.Forms Formalism.L2.Ker Formalism.MainNotions Formalism.L2.DIV Formalism.MainNotions.G GlobalTheory.TwU GlobalTheory.TwV
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.point_decoration_agree_below : UnderTie (fun {D L hT Gi Gl Kc Y cX ex t u μ St} A dtU a => ∀ (j : ℕ) (hj : j ≤ D.R.m) (β : (St j hj).Ch) (x x₁ : UA D j hj)
  (p p₁ : ChPt (R := D.R) t.sel (t.tup μ) (t.word u) j), IsPtAd A a j hj β x p → IsPtAd A a j hj β x₁ p₁ →
  (∀ v ∈ plUnder D.host.F (ssRec t u μ), bc (prV (E := D.host.E) v) x₁.1 = bc (prV (E := D.host.E) v) x.1) →
  ∀ P : t.Pr.vT (t.word u), p₁.deco.1.at P.1 = p.deco.1.at P.1) := by
  first | exact @GlobalTheory.TwV.AwayLat.lat_eq | exact GlobalTheory.TwV.AwayLat.lat_eq | (intros; apply GlobalTheory.TwV.AwayLat.lat_eq <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.RationalMatrixEntriesCongruentOneOfAdelicCongrue
section
open NumberField IsDedekindDomain

namespace GlobalTheory.TwU

theorem ratA_congAt_entry : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (Q : HeightOneSpectrum (𝓞 E)) (n N : ℕ) (g : GL (Fin N) E), GlobalTheory.TwU.CongAt (F := F) Q n (GlobalTheory.TwU.ratA F g) → ∀ a b : Fin N, Formalism.L2.Col.IntAt Q ((((Formalism.L2.Col.qOf Q : ℕ) : E) ^ n)⁻¹ * ((g : Matrix (Fin N) (Fin N) E) a b - (1 : Matrix (Fin N) (Fin N) E) a b)) := by
  intro F E _ _ _ _ _ Q n N g h a b
  set e : E := (((Formalism.L2.Col.qOf Q : ℕ) : E) ^ n)⁻¹ * ((g : Matrix (Fin N) (Fin N) E) a b - (1 : Matrix (Fin N) (Fin N) E) a b) with he
  have hm : ((GlobalTheory.TwU.ratA F g : GL (Fin N) _) : Matrix (Fin N) (Fin N) _) - 1 =
      ((g : Matrix (Fin N) (Fin N) E) - 1).map (Formalism.L2.Col.iA F E) := by
    rw [Matrix.map_sub _ (map_sub _), Matrix.map_one _ (map_zero _) (map_one _)]
    rfl
  have h1 := h a b
  rw [hm, Matrix.map_apply, ← map_mul] at h1
  obtain ⟨s, hs, hmem⟩ := h1
  rw [← map_mul] at hmem
  have h2 := ((GlobalTheory.St.G.IntAd.integral_adeles_properties F E).2.2.2.2 (algebraMap (𝓞 E) E s * e)).1 hmem
  obtain ⟨r, hr⟩ := h2
  exact ⟨r, s, hs, hr.symm⟩

end GlobalTheory.TwU
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ResidueCardColumnFieldPrimeToHostPrimeEq
section
open NumberField IsDedekindDomain

namespace GlobalTheory

theorem qOf_seamP : ∀ (D : Formalism.BasicNotions.D7) (X : Formalism.L2.Col.Fields) (s : Formalism.L2.Ker.Seam D X) (P : HeightOneSpectrum (𝓞 X.E)), Formalism.L2.Col.qOf (GlobalTheory.TwU.seamP s P) = Formalism.L2.Col.qOf P := by
  intro D X s P
  have hJ : (GlobalTheory.TwU.seamP s P).asIdeal = P.asIdeal.map (RingOfIntegers.mapRingEquiv s.iE) := by
    ext y
    obtain ⟨x, rfl⟩ := (RingOfIntegers.mapRingEquiv s.iE).surjective y
    rw [GlobalTheory.TwU.mem_seamP, Ideal.mem_map_of_equiv]
    constructor
    · intro h; exact ⟨x, h, rfl⟩
    · rintro ⟨z, hz, hzx⟩
      have := (RingOfIntegers.mapRingEquiv s.iE).injective hzx
      subst this; exact hz
  unfold Formalism.L2.Col.qOf
  rw [Ideal.absNorm_apply, Ideal.absNorm_apply, Submodule.cardQuot_apply, Submodule.cardQuot_apply]
  exact (Nat.card_congr (Ideal.quotientEquiv _ _ (RingOfIntegers.mapRingEquiv s.iE) hJ).toEquiv).symm

end GlobalTheory
end

