module

public import Mathlib
public import Development.AutomorphicArithmetic.Foundations.UnitarySphericalFixing.SatakeParameters.SplitLevelConjugates.IsPrincipalCongruenceAt
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0220
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ConjEqOfNormalises
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0750
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0923
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0647
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0655
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0199

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.Foundations.UnitarySphericalFixing.SatakeParameters.SplitLevelConjugates.FixOne
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host NumberField IsDedekindDomain
open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.HeightCounting
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

theorem UpperTheory.One.M.B.fixOne :
    UpperTheory.One.M.B.FixOne := by
  intro L _ _ _ n a S hS s f hf hf0 hfix σ hσ
  obtain ⟨c, T, hc, hci, -⟩ := id hσ
  have hiso : f ∈ NG.isoTyp a.ρ S :=
    (le_sSup (s := {S' | NG.IsIrrRep a.ρ S' ∧ NG.IsoRep S S'})
      ⟨hS, LinearEquiv.refl ℂ S, fun _ _ _ e => e⟩ : S ≤ NG.isoTyp a.ρ S) hf
  have hint : ∀ g ∈ KOne (s.v.adicCompletion (maximalRealSubfield L)) (Fin n),
      g ∈ Formalism.UG.GLint (Fin n) (s.v.adicCompletionIntegers (maximalRealSubfield L)).toSubring := fun g hg => by
    rw [(GlobalTheory.AdelicU.GLint_eq_KO_and_princ_eq_KOne s.v n).1]
    exact GlobalTheory.StepData.KOne_le_KO hg
  obtain ⟨u, hu0, hu⟩ := GlobalTheory.LocVec.main L n a S hS s σ hσ c hc hci
    (KOne (s.v.adicCompletion (maximalRealSubfield L)) (Fin n)) 1 hint
    (by rw [MonoidHom.ker_one, Subgroup.coe_top]; exact isOpen_univ)
    f hiso hf0 (fun κ hκ h => by
      rw [hfix κ ((GlobalTheory.HeckeScalarSph.loc_mem_GLint_iff s hκ).1 (hint _ h)) hκ
        ((GlobalTheory.FixedAtSplit.mem_KOne_iff' _).1 h)]
      simp)
  rw [Submodule.ne_bot_iff]
  refine ⟨u, GlobalTheory.Parabolic.mem_fixed.2 fun h hh => ?_, hu0⟩
  have e : Matrix.GeneralLinearGroup.map c.toRingHom (Matrix.GeneralLinearGroup.map c.symm.toRingHom h) = h := by
    ext i j
    simp
  have hg := GlobalTheory.FixedAtSplit.mem_KOne_of_map c hc _ (e.symm ▸ hh)
  have h3 := hu _ hg
  rw [e] at h3
  simpa using h3
end

-- bundled from Development.AutomorphicArithmetic.Foundations.UnitarySphericalFixing.SatakeParameters.SplitLevelConjugates.FixSph
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host NumberField IsDedekindDomain ReciprocityTheory.Aut Formalism.AUTREP
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.RecT GlobalTheory.HeightCounting
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

theorem UpperTheory.One.M.B.fixSph :
    UpperTheory.One.M.B.FixSph := by
  intro L _ _ _ n a S hS s f hf hf0 hfix σ hσ
  let J : Subgroup (GAf L n) :=
    { carrier := {κ | κ ∈ Umax L n ∧ ∀ g, f (g * κ) = f g}
      one_mem' := ⟨one_mem _, fun g => by rw [mul_one]⟩
      mul_mem' := fun {x y} hx hy => ⟨mul_mem hx.1 hy.1, fun g => by rw [← mul_assoc, hy.2, hx.2]⟩
      inv_mem' := fun {x} hx => ⟨inv_mem hx.1, fun g => by
        rw [← hx.2 (g * x⁻¹), inv_mul_cancel_right]⟩ }
  have hAF := hS.1.le hf
  have hlev : ∃ N : ℕ, 0 < N ∧ ∀ κ, NG.Cong L n N κ → ∃ h : κ ∈ J, (1 : J →* ℂˣ) ⟨κ, h⟩ = 1 := by
    obtain ⟨-, N, hN, h⟩ := hAF
    exact ⟨N, hN, fun κ hκ => ⟨⟨hκ.1, h κ hκ⟩, rfl⟩⟩
  have hB : NG.HypOutside J (1 : J →* ℂˣ) {s.v}ᶜ := by
    intro κ hκ
    rw [compl_compl] at hκ
    exact ⟨⟨fun h => h.1, fun h => ⟨h, fun g => congrFun (hfix κ h hκ) g⟩⟩, fun _ => rfl⟩
  have hiso : f ∈ NG.isoTyp a.ρ S :=
    (le_sSup (s := {S' | NG.IsIrrRep a.ρ S' ∧ NG.IsoRep S S'})
      ⟨hS, LinearEquiv.refl ℂ S, fun _ _ _ h => h⟩ : S ≤ _) hf
  have hT : f ∈ NG.TypeSp a.ρ J (1 : J →* ℂˣ) := ⟨hAF, fun κ => by
    rw [MonoidHom.one_apply, Units.val_one, one_smul]
    exact funext κ.2.2⟩
  have h := GlobalTheory.SphHyp.isSpherical_of_hypOutside L n a S hS J 1 hlev _ hB f hiso hT hf0 s (by simp) σ hσ
  exact GlobalTheory.BCOffT.isSpherical_of_equiv (equivRep σ).symm h
end

-- bundled from Development.AutomorphicArithmetic.Foundations.UnitarySphericalFixing.SatakeParameters.SplitLevelConjugates.LevSplit
section
noncomputable section
set_option maxHeartbeats 1000000

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
open ReciprocityTheory.Aut Formalism.AUTREP GlobalTheory.CenFrame
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.TypeRec.factG

namespace UpperTheory.One.M.B

private theorem map_eq_one {L : Type} [Field L] [NumberField L] [IsCMField L] {n : ℕ} (s : SplitPlace L) {κ : GAf L n}
    (hK : IsPrincipalCongruenceAt s κ) {y : GL (Fin n) (Os s)} (hy : IsCompOf s κ y) {k : Type} [CommRing k] (φ : Os s →+* k)
    (hφ : IsResidue s φ) : Matrix.GeneralLinearGroup.map φ y = 1 := by
  refine Units.ext (Matrix.ext fun a c => ?_)
  have h0 : φ (y.val a c - (1 : Matrix (Fin n) (Fin n) (Os s)) a c) = 0 := by
    rw [hφ.ker]
    have e : ((y.val a c - (1 : Matrix (Fin n) (Fin n) (Os s)) a c : Os s) : s.v.adicCompletion (maximalRealSubfield L)) =
        ((s.loc n κ).val - 1) a c := by
      rw [Matrix.sub_apply, ← hy a c]
      by_cases h : a = c <;> simp [Matrix.one_apply, h]
    rw [e]
    exact hK a c
  rw [map_sub, sub_eq_zero] at h0
  refine h0.trans ?_
  rw [Units.val_one, Matrix.one_apply, Matrix.one_apply]
  split_ifs
  · exact map_one _
  · exact map_zero _

private theorem map_eq_one_conj {L : Type} [Field L] [NumberField L] [IsCMField L] {n : ℕ} (s : SplitPlace L) {κ : GAf L n}
    (hU : κ ∈ Umax L n) (hK : IsPrincipalCongruenceAt s κ) {y' : GL (Fin n) (Os (GlobalTheory.TypeTame.conjSP s))}
    (hy' : IsCompOf (GlobalTheory.TypeTame.conjSP s) κ y') {k : Type} [CommRing k] (φ : Os (GlobalTheory.TypeTame.conjSP s) →+* k)
    (hφ : IsResidue (GlobalTheory.TypeTame.conjSP s) φ) : Matrix.GeneralLinearGroup.map φ y' = 1 := by
  obtain ⟨y, hy⟩ := GlobalTheory.BlockLiftFrame.exists_isCompOf s hU
  have h1 : Matrix.GeneralLinearGroup.map (φ : Os s →+* k) y = 1 := map_eq_one s hK hy φ ⟨hφ.surj, hφ.ker⟩
  have h2 : Matrix.GeneralLinearGroup.map (φ : Os s →+* k) y⁻¹ = 1 := by rw [map_inv, h1, inv_one]
  have h3 : Matrix.GeneralLinearGroup.map (s.v.adicCompletionIntegers (maximalRealSubfield L)).subtype y = s.loc n κ :=
    Units.ext (Matrix.ext fun a c => hy a c)
  refine Units.ext (Matrix.ext fun a c => ?_)
  have e : y'.val a c = (y⁻¹).val c a := by
    apply Subtype.ext
    have h4 : (s.loc n κ)⁻¹ =
        Matrix.GeneralLinearGroup.map (s.v.adicCompletionIntegers (maximalRealSubfield L)).subtype y⁻¹ :=
      (congrArg _ h3.symm).trans (MonoidHom.map_inv _ y).symm
    rw [hy' a c, GlobalTheory.ConjLoc.loc_conjSP, h4]
    rfl
  have e2 : (Matrix.GeneralLinearGroup.map (φ : Os s →+* k) y⁻¹).val c a = (1 : GL (Fin n) k).val c a := by rw [h2]
  refine ((congrArg φ e).trans e2).trans ?_
  rw [Units.val_one, Matrix.one_apply, Matrix.one_apply]
  exact if_congr eq_comm rfl rfl

variable {D : D7}

private theorem red_of_comp {V : TH.HSp D} {n : ℕ} (hn : V.rank = n) {hF : D.host.F = maximalRealSubfield D.host.E}
    {P : Formalism.IndefR.principalLevelFrame.RowPsi V n} (hP : StdFrame hF P) {β : GL (Fin V.rank) (Formalism.IndefR.Lev.EAf D)}
    {Λ : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E)} (hB : Formalism.IndefR.Lev.IsBaseFrame V β Λ 1)
    (s : SplitPlace D.host.E) {κ : GAf D.host.E n} (hU : κ ∈ Umax D.host.E n)
    (h : ∀ y, IsCompOf s κ y → ∀ φ : Os s →+* Formalism.L2.DIV.kP s.w, IsResidue s φ → Matrix.GeneralLinearGroup.map φ y = 1) :
    Formalism.L2.DIV.redFn β s.w (Formalism.IndefR.Lev.finE V (P.ψ κ)) = 1 := by
  obtain ⟨φ, b, hφ, hfr⟩ := GlobalTheory.FrameRedSplit.frameRed_exists D V n hn hF P β Λ hP hB s
  obtain ⟨y, hy⟩ := GlobalTheory.BlockLiftFrame.exists_isCompOf s hU
  refine Units.ext (Matrix.ext fun i j => ?_)
  have e := hfr κ hU y hy (Fin.cast hn i) (Fin.cast hn j)
  rw [h y hy φ hφ, mul_one, mul_inv_cancel] at e
  refine e.trans ?_
  rw [Units.val_one, Units.val_one, Matrix.one_apply, Matrix.one_apply]
  exact if_congr (Fin.cast_injective hn).eq_iff rfl rfl

private theorem red_one {V : TH.HSp D} {n : ℕ} (hn : V.rank = n) {hF : D.host.F = maximalRealSubfield D.host.E}
    {P : Formalism.IndefR.principalLevelFrame.RowPsi V n} (hP : StdFrame hF P) {β : GL (Fin V.rank) (Formalism.IndefR.Lev.EAf D)}
    {Λ : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E)} (hB : Formalism.IndefR.Lev.IsBaseFrame V β Λ 1)
    (s : SplitPlace D.host.E) {κ : GAf D.host.E n} (hU : κ ∈ Umax D.host.E n) (hT : TrivOutside {s.v} κ)
    (PP : PlE D.host) (hK : NG.OverPl PP s.v → IsPrincipalCongruenceAt s κ) :
    Formalism.L2.DIV.redFn β PP (Formalism.IndefR.Lev.finE V (P.ψ κ)) = 1 := by
  by_cases ho : NG.OverPl PP s.v
  · have hk := hK ho
    have hconj (x : 𝓞 D.host.E) : x ∈ (GlobalTheory.TypeTame.conjSP s).w.asIdeal ↔
        IsCMField.ringOfIntegersComplexConj D.host.E x ∈ s.w.asIdeal := by
      show Valued.v ((GlobalTheory.TypeTame.conjSP s).i (x : D.host.E)) < 1 ↔
        Valued.v (s.i ((IsCMField.ringOfIntegersComplexConj D.host.E x : 𝓞 D.host.E) : D.host.E)) < 1
      rw [IsCMField.coe_ringOfIntegersComplexConj]
      rfl
    have hor : PP = s.w ∨ PP = (GlobalTheory.TypeTame.conjSP s).w := by
      by_contra hne
      push Not at hne
      have nle : ∀ Q : PlE D.host, PP ≠ Q → ¬ PP.asIdeal ≤ Q.asIdeal := fun Q h hle =>
        h (HeightOneSpectrum.ext (PP.isMaximal.eq_of_le Q.isPrime.ne_top hle))
      obtain ⟨a, ha, haP⟩ := Set.not_subset.mp (nle _ hne.1)
      obtain ⟨b, hb, hbQ⟩ := Set.not_subset.mp (nle _ hne.2)
      have key : ∃ x ∈ PP.asIdeal, x ∉ s.w.asIdeal ∧ x ∉ (GlobalTheory.TypeTame.conjSP s).w.asIdeal := by
        by_cases haQ : a ∈ (GlobalTheory.TypeTame.conjSP s).w.asIdeal
        · by_cases hbP : b ∈ s.w.asIdeal
          · refine ⟨a + b, PP.asIdeal.add_mem ha hb, fun h => haP ?_, fun h => hbQ ?_⟩
            · simpa using s.w.asIdeal.sub_mem h hbP
            · simpa using (GlobalTheory.TypeTame.conjSP s).w.asIdeal.sub_mem h haQ
          · exact ⟨b, hb, hbP, hbQ⟩
        · exact ⟨a, ha, haP, haQ⟩
      obtain ⟨x, hx, hxP, hxQ⟩ := key
      rw [hconj] at hxQ
      let cO := IsCMField.ringOfIntegersComplexConj D.host.E
      have hc (x : 𝓞 D.host.E) : cO (cO x) = x := by
        apply RingOfIntegers.ext
        rw [IsCMField.coe_ringOfIntegersComplexConj, IsCMField.coe_ringOfIntegersComplexConj]
        exact IsCMField.complexConj_apply_apply D.host.E (x : D.host.E)
      have hfix : cO (x * cO x) = x * cO x := by rw [map_mul, hc, mul_comm]
      obtain ⟨y, hy⟩ := (IsCMField.ringOfIntegersComplexConj_eq_self_iff D.host.E _).1 hfix
      have hyw : y ∈ PP.asIdeal.comap (algebraMap (𝓞 (maximalRealSubfield D.host.E)) (𝓞 D.host.E)) := by
        rw [Ideal.mem_comap, hy]; exact PP.asIdeal.mul_mem_right _ hx
      rw [Eq.trans ho s.w_under.symm, Ideal.mem_comap, hy] at hyw
      rcases s.w.isPrime.mem_or_mem hyw with h | h
      · exact hxP h
      · exact hxQ h
    rcases hor with e | e
    · rw [e]
      exact red_of_comp hn hP hB s hU fun y hy φ hφ => map_eq_one s hk hy φ hφ
    · rw [e]
      exact red_of_comp hn hP hB _ hU fun y hy φ hφ => map_eq_one_conj s hU hk hy φ hφ
  · have hS := (GlobalTheory.FinZeta.LevelOff.finE_mem_St_iff hB (P.into κ)).2 ((hP.2 κ).1 hU)
    refine GlobalTheory.FinZeta.LevelOff.redFn_eq_one_of_proj β {(_root_.IsDedekindDomain.HeightOneSpectrum.under (𝓞 D.host.F) PP)} hS (fun u hu => ?_) (Finset.mem_singleton_self _)
    rw [Finset.mem_singleton.1 hu]
    exact GlobalTheory.NonSplitLevel.projV_eq_one hP κ PP (hT _ fun e => ho (congrArg HeightOneSpectrum.asIdeal e))

end UpperTheory.One.M.B

theorem UpperTheory.One.M.B.levSplit :
    UpperTheory.One.M.B.LevSplit := by
  refine GlobalTheory.HeightCounting.JumpsAt.evLgG_of_forall fun K B f T _ w _ Z Wt hX z p0 Y _ _ _ _ _ i P hP s κ hU hT hK => ?_
  have hlev := z.pins.char.base.lev
  obtain ⟨c, hc⟩ := hlev.βV i
  rw [one_pow] at hc
  have hS := (GlobalTheory.FinZeta.LevelOff.finE_mem_St_iff hc (P.into κ)).2 ((hP.2 κ).1 hU)
  have hred : ∀ PP, PP ∈ (Formalism.IndefR.RecTie.datVP z.R.toRealDat i (Y.tupT (w.st Z).toD7.what₂.mu0)
        (z.R.toRealDat.levR z.F.lv2 false)).Pg ∨
      PP ∈ (Formalism.IndefR.RecTie.datVP z.R.toRealDat i (Y.tupT (w.st Z).toD7.what₂.mu0) (z.R.toRealDat.levR z.F.lv2 false)).Q →
      Formalism.L2.DIV.redFn (z.R.toRealDat.βV i) PP (Formalism.IndefR.Lev.finE (Formalism.IndefR.Links.Vc (w.st Z).toD7 i) (P.ψ κ)) = 1 := by
    intro PP hPP
    rcases hPP with h | h
    · obtain ⟨k, hk⟩ := (hlev.Pg PP).1 h
      exact UpperTheory.One.M.B.red_one (GlobalTheory.FrameBlockDiagonal.rankV _ i) hP hc s hU hT PP fun ho =>
        hK ⟨PP, ho, k, GlobalTheory.Mem.TypePl.div_over _ hk⟩
    · refine absurd ?_ ((hlev.Q_ram _ PP).2 (Or.inl h))
      have e := (congrArg z.R.toRealDat.toLevCh.xiH ((congrArg Y.tupT Y.tup0).symm.trans (Y.tupT_tup _))).trans hlev.xi_base
      exact e ▸ fun _ _ => rfl
  refine ⟨⟨P.into κ, GlobalTheory.LevSplit.mem_lev_of_red _ _ _ _ _ (GlobalTheory.LevSplit.finE_mem_UA _ _) hS hred⟩, ?_⟩
  unfold Formalism.IndefR.Lev.levChi
  rw [GlobalTheory.LevSplit.levFn_eq_one _ _ _ hred, Units.val_one]

end
end

