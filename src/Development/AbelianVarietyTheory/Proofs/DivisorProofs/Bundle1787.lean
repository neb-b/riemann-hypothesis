module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0033
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0041
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1487
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0007
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1502
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsNatMulIntegralOfIsCompact
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTranslatesEqPrimFrameLat
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1531
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1544
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1592
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1645
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EventuallySelfDualLatticeIndicatorIsVacuum
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContinuousAtPlace
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1561
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1558
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0091
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.StoneVonNeumannSchwartzBruhatTransverseLagrangia
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0902
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1768
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1694
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1345
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0211
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1760
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0035
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1776
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0015
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1656
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0034
public import Formalism.LocalToGlobal.IndefiniteReal.Bundle0027
public import Formalism.LocalToGlobal.IndefiniteReal.FWExist
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0054
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1000
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0912
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1063
public import Development.WeilBound.ThetaLifts.Reductions.WeilPairs.SplitPlaceThetaFunctionVacuumConjugatePlace
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0057

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLinearBarGoodPlace
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links
open IsDedekindDomain NumberField MeasureTheory Matrix
open scoped TensorProduct
open GlobalTheory.FunObj GlobalTheory.ChiGrid GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames Formalism.L2.DIV
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun
open ValuativeRel
open scoped GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped GlobalTheory.VacAny

noncomputable section

namespace GlobalTheory.LinBarAt

theorem locCo_form' {F : Type} [Field F] [NumberField F] {W : Type} [AddCommGroup W] [Module (AF F) W]
    {B : W → W → AF F} {κ : Type} [Fintype κ] (co : Darboux B κ) (v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl (F := F)) (x u : W) :
    (GlobalTheory.LatVac.locCo co v x).1 ⬝ᵥ (GlobalTheory.LatVac.locCo co v u).2 -
      (GlobalTheory.LatVac.locCo co v u).1 ⬝ᵥ (GlobalTheory.LatVac.locCo co v x).2 = evFin F v (B x u) := by
  rw [co.form]
  set_option synthInstance.maxHeartbeats 100000 in
    simp [GlobalTheory.LatVac.locCo, dotProduct, map_sum, map_mul, map_sub]

theorem locCo_surj' {F : Type} [Field F] [NumberField F] {W : Type} [AddCommGroup W] [Module (AF F) W]
    {B : W → W → AF F} {κ : Type} [Fintype κ] (co : Darboux B κ) (v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl (F := F))
    (w : (κ → Fv F v) × (κ → Fv F v)) : ∃ u : W, At (evFin F v) u ∧ GlobalTheory.LatVac.locCo co v u = w := by
  refine ⟨co.e.symm (fun k => GlobalTheory.LatVac.liftV v (w.1 k), fun k => GlobalTheory.LatVac.liftV v (w.2 k)), ?_, ?_⟩
  · intro a ha
    rw [← LinearEquiv.map_smul, ← co.e.symm.map_zero]
    congr 1
    refine Prod.ext (funext fun k => ?_) (funext fun k => ?_)
    · exact GlobalTheory.LatVac.at_liftV v _ a ha
    · exact GlobalTheory.LatVac.at_liftV v _ a ha
  · refine Prod.ext (funext fun k => ?_) (funext fun k => ?_) <;>
      simp [GlobalTheory.LatVac.locCo, GlobalTheory.LatVac.evFin_liftV]

theorem at_symp' {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    {n d : ℕ} (JA : Matrix (Fin n) (Fin n) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))) (JB : Matrix (Fin d) (Fin d) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))) {v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl (F := F)}
    (x u : Matrix (Fin n) (Fin d) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))) (hx : At (evFin F v) x) :
    At (evFin F v) (symp (R := AF F) (cA σ) (-1) JA JB x u) := by
  intro a ha
  have h := GlobalTheory.LatVac.symp_smul_smul σ JA JB (-1) a 1 x u
  rw [hx a ha, one_smul, mul_one, GlobalTheory.VacIndic.symp_zero_left] at h
  rw [smul_eq_mul]
  exact h.symm

end GlobalTheory.LinBarAt

namespace GlobalTheory.LinBarAt

theorem exists_isLinBar_at : GlobalTheory.FunPr.Hypotheses₂ → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    (a a' : ℕ) (G : Geo σ a a') (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W), IsTriple B G X om om' → ∀ v, X.Good v →
    ∀ t : E →ₐ[F] Fv F v, ∃ ι, G.M'.IsLinBar B.ψ t 1 1 ι := by
  intro _ F E _ _ _ _ _ σ B a a' G X om om' hTr v hv t
  obtain ⟨uT, uM, hT, hM, hspan, hsymp⟩ := (GlobalTheory.T.exists_local_unipotent_additive) F E σ B a a' G X om om' hTr v t
  have hψc : Continuous (GlobalTheory.LatVac.psiAt B.ψ v) := GlobalTheory.VacAny.continuous_psiV hTr.base.std.1 v
  have hunr : PsiUnr B.ψ v := (GlobalTheory.T.psi_unramified_away_different) F B.ψ hTr.base.std v (GlobalTheory.SplitFullyUnr.not_le_differentIdeal v hv.2)
  have hunr' : ∀ x : Fv F v, (∀ y ∈ 𝒪[Fv F v], GlobalTheory.LatVac.psiAt B.ψ v (x * y) = 1) ↔
      x ∈ 𝒪[Fv F v] := by
    intro x
    simp only [GlobalTheory.FinPl.SplitPoint.mem_integer_iff]
    exact hunr x
  have hcoM : ∀ z, coAt G t (uM z) = 0 := fun z => coAt_eq_zero G t _ (hM z).2.1
  haveI : CharZero (Fv F v) := charZero_of_injective_algebraMap (algebraMap F _).injective
  obtain ⟨ι, hbij, htr, hmu⟩ := _root_.GlobalTheory.StoneVN.intertwiner_matrix (GlobalTheory.LatVac.psiAt B.ψ v) hψc hunr'
    ((GlobalTheory.LatVac.locCo G.M'.co v).comp uT) ((GlobalTheory.LatVac.locCo G.M'.co v).comp uM)
    (fun Y Y' => by
      simp only [AddMonoidHom.comp_apply]
      rw [locCo_form']
      unfold GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA incM
      rw [hsymp _ _ (hT Y).1 (hT Y').1, (hT Y).2.1, (hT Y').2.1]
      simp)
    (fun z z' => by
      simp only [AddMonoidHom.comp_apply]
      rw [locCo_form']
      unfold GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA incM
      rw [hsymp _ _ (hM z).1 (hM z').1, hcoM, hcoM]
      simp)
    (fun Y z => by
      simp only [AddMonoidHom.comp_apply]
      rw [locCo_form']
      unfold GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA incM
      rw [hsymp _ _ (hT Y).1 (hM z).1, (hT Y).2.1, (hT Y).2.2, (hM z).2.2, hcoM]
      simp)
    (fun w => by
      obtain ⟨u, hu, rfl⟩ := locCo_surj' G.M'.co v w
      obtain ⟨Y, z, rfl⟩ := hspan u hu
      exact ⟨Y, z, by simp only [AddMonoidHom.comp_apply, map_add (f := _)]⟩)
  have hφ₁ : ∀ (u : Matrix (Fin a') (Fin (a + a')) (AE F E)), At (evFin F v) u →
      ∀ φ ∈ GlobalTheory.WeilM.SB _, ∀ φ₁, Acts (evFin F v) (G.M'.co.rho B.ψ u) φ φ₁ →
        φ₁ = GlobalTheory.WeilM.schr (GlobalTheory.LatVac.psiAt B.ψ v) (GlobalTheory.LatVac.locCo G.M'.co v u) φ :=
    fun u hu φ hφ φ₁ hact => GlobalTheory.TensUniq.eq_of_tens_eq v φ φ₁ _ hφ fun r hr =>
      (hact r hr).symm.trans (GlobalTheory.VacBridge.rho_acts_locCo G.M'.co B.ψ v u hu φ r hr)
  refine ⟨ι, hbij, ?_, ?_⟩
  · intro u hu hu0 φ hφ φ₁ _ hact Y
    have e1 := hφ₁ u hu φ hφ φ₁ hact
    obtain ⟨Y₀, z, rfl⟩ := hspan u hu
    have hz : z = 0 := by
      have h := hu0
      rw [Matrix.map_add _ (map_add _), (hT Y₀).2.1, (hM z).2.2, zero_add, neg_eq_zero] at h
      exact h
    subst hz
    rw [map_zero, add_zero] at e1 ⊢
    show ι φ₁ Y = ι φ (Y + coAt G t (uT Y₀))
    rw [(hT Y₀).2.2, e1]
    exact congrFun (htr Y₀ φ hφ) Y
  · intro u hu hu1 φ hφ φ₁ _ hact x hx hx0
    have e1 := hφ₁ u hu φ hφ φ₁ hact
    obtain ⟨Y₀, z, rfl⟩ := hspan u hu
    have hY : Y₀ = 0 := by
      have h := hu1
      rw [Matrix.map_add _ (map_add _), (hM z).2.1, add_zero] at h
      rw [← (hT Y₀).2.2]
      exact coAt_eq_zero G t _ h
    subst hY
    rw [map_zero, zero_add] at e1 ⊢
    show ι φ₁ (coAt G t x) = _ * ι φ (coAt G t x)
    rw [e1, GlobalTheory.VacIndic.psi_of_at B.ψ (at_symp' _ _ _ x (uM z) hx)]
    conv_rhs => unfold GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA incM
    rw [hsymp x (uM z) hx (hM z).1, hx0, hcoM,
      (hM z).2.2]
    have h2 := congrFun (hmu z φ hφ) (coAt G t x)
    simp only [AddMonoidHom.comp_apply] at h2
    rw [h2, ← GlobalTheory.LatVac.psiAt_apply]
    congr 2
    simp [Finset.sum_neg_distrib]

end GlobalTheory.LinBarAt
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsOpenSubgroupsSchroedingerFixContinuousCharStatement
section
open scoped TensorProduct Matrix
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_openSubgroups_schroedinger_fix_continuousChar : ∀ (F : Type) [Field F] [NumberField F] (ψ : AddChar (AF F) ℂ), Continuous ψ →
    ∀ (κ : Type) [Fintype κ], ∀ Φ ∈ schA F κ,
      ∃ L₁ L₂ : AddSubgroup (κ → FiniteAdeleRing (𝓞 F) F),
        IsOpen (L₁ : Set (κ → FiniteAdeleRing (𝓞 F) F)) ∧ IsOpen (L₂ : Set (κ → FiniteAdeleRing (𝓞 F) F)) ∧
        ∀ x ∈ L₁, ∀ y ∈ L₂, schr ψ (GlobalTheory.WeilCont.adeleJoin F 0 x, GlobalTheory.WeilCont.adeleJoin F 0 y) Φ = Φ := by
  first | exact @GlobalTheory.SchrFixFin.exists_fix | exact GlobalTheory.SchrFixFin.exists_fix | (intros; apply GlobalTheory.SchrFixFin.exists_fix <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsOrbitFamilyAdaptedLatticeSplitSupport
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.DIV.Cons Formalism.L2.Pj Formalism.L2.Indef Formalism.L2.Indef.Tree
open Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.FWT Formalism.IndefR.Datum Formalism.IndefR.Lev
open GlobalTheory.FormTies GlobalTheory.OnTies GlobalTheory.TraceClassRank
open scoped TensorProduct Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.OnCmp GlobalTheory.BigOn GlobalTheory.RealIndexBound
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Datum Level Moduli Coeff)

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 200000

namespace GlobalTheory.OrbitAdapt

section
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out Formalism.MainNotions.WeightAlgebra GlobalTheory.IndefiniteRowSideFullHecke.UnitaryAdjointCongruence GlobalTheory.ShortMove

theorem exists_step_int (D : D7) (T : Full D) (hF : LawsFull T) (j : ℕ) (hj : InR D j) (n : ℕ) (hev : Even n)
    (hb : 0 < badN D) (Λ : GenLat D.host.E n) (N : ℕ) (a : (D.host.E →+* ℂ) × ℕ → ℕ)
    (P : MvPolynomial (LtN (T.Q.Dw j) n) T.Q.c.F) (hU : Λ.Unimod) (hT : Λ.TrivAt (badN D))
    (hM : Λ.TrivAt (T.dδ j n).l₂.M) (hN : Λ.LevOK N (T.dδ j n).l₂.M) (hP : P ∈ harmL T.Q.c Λ a) (p : ℕ)
    (hp : 0 < p) :
    ∃ (Λ₁ : GenLat D.host.E n) (N₁ : ℕ) (P₁ : MvPolynomial (LtN (T.Q.Dw j) n) T.Q.c.F) (ζ : T.Q.c.F),
      Λ₁.Unimod ∧ Λ₁.TrivAt (badN D * (T.dδ j n).l₂.M * p) ∧ Λ₁.LevOK N₁ (T.dδ j n).l₂.M ∧ P₁ ∈ harmL T.Q.c Λ₁ a ∧
      ζ ≠ 0 ∧ (∃ m : ℕ, 0 < m ∧ ζ ^ m = 1) ∧
      (∀ (x0 : Fin n → (T.Q.Dw j).La) (f : Rul (T.Q.Xo j) T.Q.c),
        IsShortRule (T.Q.Xo j) T.Q.c (T.dδ j n) Λ N x0 P f →
        IsShortRule (T.Q.Xo j) T.Q.c (T.dδ j n) Λ₁ N₁ x0 P₁ (ζ • f)) := by
  have hBM := GlobalTheory.ShortChange.trivAt_mul hT hM
  have hMpos : 0 < (T.dδ j n).l₂.M := by have := (T.dδ j n).l₂.three_le; omega
  obtain ⟨γ, Λ', hγ, hc, hmove, hU', s, -, -, -, -, k, hk, hk1, hk2⟩ :=
    GlobalTheory.AdaptCongr.exists_move_split D.host.E T.Q.H n _ p Λ (Nat.mul_pos hb hMpos) hp hU hBM
  have h2b : 2 ∣ badN D := by
    unfold badN
    exact ((D.host.two_dvd_QS.mul_right _).mul_right _).mul_right _
  have hg : IsUnitaryM γ.1 := by
    refine Matrix.ext fun i l => ?_
    have := hγ (Pi.single l 1) (Pi.single i 1)
    rw [GlobalTheory.UnRep.Move.hermE_one, GlobalTheory.UnRep.Move.hermE_one] at this
    simp only [Matrix.mulVec_single_one, Matrix.col_apply] at this
    simp only [adjM, Matrix.mul_apply, Matrix.of_apply, this, Matrix.one_apply, Pi.single_apply]
    by_cases h : i = l
    · subst h; simp [apply_ite (IsCMField.complexConj D.host.E)]
    · simp [h, apply_ite (IsCMField.complexConj D.host.E), Ne.symm h]
  have hinv' : ∀ v : Fin n → D.host.E, γ.1 *ᵥ ((γ⁻¹).1 *ᵥ v) = v := fun v => by
    rw [Matrix.mulVec_mulVec, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.one_mulVec]
  obtain rfl : Λ' = actLat γ.1 Λ := by
    cases Λ' with
    | mk L =>
      simp only [actLat, GenLat.mk.injEq]
      ext v
      constructor
      · intro hv
        exact ⟨_, (hmove _).2 (by rw [hinv']; exact hv), hinv' v⟩
      · rintro ⟨u, hu, rfl⟩
        exact (hmove u).1 hu
  have hkT : ∀ m, m ∣ p * (badN D * (T.dδ j n).l₂.M) → (actLat γ.1 Λ).TrivAt m := fun m hm =>
    ⟨k, hk.coprime_dvd_right hm, hk1, hk2⟩
  have hN₁ : (actLat γ.1 Λ).LevOK ((T.dδ j n).l₂.M * k) (T.dδ j n).l₂.M := by
    refine ⟨?_, dvd_mul_right _ _, ?_⟩
    · exact (T.dδ j n).l₂.odd.mul
        (Nat.coprime_two_right.1 (hk.coprime_dvd_right ((h2b.mul_right _).mul_left _)))
    · show _ ≤ (actLat γ.1 Λ).La ⊓ Formalism.L2.Pj.stdLat D.host.E n
      refine le_inf ((Submodule.smul_mono_left ?_).trans hk2) Submodule.smul_le_right
      refine Ideal.span_singleton_le_span_singleton.2 ?_
      rw [Nat.cast_mul]
      exact dvd_mul_left _ _
  obtain ⟨P₁, ζ, hP₁, hζ, hroot, hR⟩ := shortRule_change_mat D T hF j hj n Λ γ.1 _ a P hg
    (dvd_mul_left _ _) hc hev hU hU' hT (hkT _ ((dvd_mul_right _ _).mul_left _)) hM
    (hkT _ ((dvd_mul_left _ _).mul_left _)) hP
  exact ⟨actLat γ.1 Λ, _, P₁, ζ, hU', hkT _ (by rw [mul_comm]), hN₁, hP₁, hζ, hroot,
    fun x0 f h => hR x0 N _ f hN hN₁ h⟩

theorem exists_step_split_off (D : D7) (T : Full D) (hF : LawsFull T) (j : ℕ) (hj : InR D j) (V : Formalism.BasicNotions.TH.HSp D)
    (hg : V.gram = 1) (hL : Formalism.IndefR.Bridge.hLat V 1 = Formalism.L2.Pj.stdLat D.host.E V.rank) (hev : Even V.rank) (hb : 0 < badN D)
    (p : ℕ) (hp : 0 < p) (Λ : GenLat D.host.E V.rank) (N : ℕ) (a : (D.host.E →+* ℂ) × ℕ → ℕ)
    (P : MvPolynomial (LtN (T.Q.Dw j) V.rank) T.Q.c.F) (hU : Λ.Unimod)
    (hT : Λ.TrivAt (badN D * (T.dδ j V.rank).l₂.M * p)) (hN : Λ.LevOK N (T.dδ j V.rank).l₂.M)
    (hP : P ∈ harmL T.Q.c Λ a) :
    ∃ (h : Formalism.L2.Theta.GA D V) (Λ' : GenLat D.host.E V.rank) (N' : ℕ)
      (P' : MvPolynomial (LtN (T.Q.Dw j) V.rank) T.Q.c.F) (ζ : T.Q.c.F),
      Formalism.IndefR.FWT.SplitOffBad V (badN D * (T.dδ j V.rank).l₂.M * p) h ∧
      (∀ w, w ∈ Λ'.La ↔ (fun b => star (w b)) ∈ Formalism.IndefR.Bridge.hLat V (Formalism.IndefR.FWT.fin V h)) ∧
      Λ'.Unimod ∧ Λ'.TrivAt (badN D) ∧ Λ'.TrivAt (T.dδ j V.rank).l₂.M ∧ Λ'.TrivAt p ∧
      Λ'.LevOK N' (T.dδ j V.rank).l₂.M ∧ P' ∈ harmL T.Q.c Λ' a ∧ ζ ≠ 0 ∧ (∃ m : ℕ, 0 < m ∧ ζ ^ m = 1) ∧
      ∀ (x0 : Fin V.rank → (T.Q.Dw j).La) (f : Rul (T.Q.Xo j) T.Q.c),
        IsShortRule (T.Q.Xo j) T.Q.c (T.dδ j V.rank) Λ N x0 P f →
        IsShortRule (T.Q.Xo j) T.Q.c (T.dδ j V.rank) Λ' N' x0 P' (ζ • f) := by
  have hM0 : 0 < (T.dδ j V.rank).l₂.M := by have := (T.dδ j V.rank).l₂.three_le; omega
  have hpos : 0 < badN D * p * (T.dδ j V.rank).l₂.M := Nat.mul_pos (Nat.mul_pos hb hp) hM0
  have hT' : Λ.TrivAt (badN D * p * (T.dδ j V.rank).l₂.M) := by
    rwa [show badN D * p * (T.dδ j V.rank).l₂.M = badN D * (T.dδ j V.rank).l₂.M * p by ring]
  obtain ⟨gm, h, hgm, hc, hh, hs, e⟩ := _root_.GlobalTheory.SplitMove.exists_move_to_split D V hg hL T.Q.H _ hpos Λ hU hT'
  have h2 : 2 ∣ badN D * p := by
    unfold badN
    exact dvd_mul_of_dvd_left (((D.host.two_dvd_QS.mul_right _).mul_right _).mul_right _) p
  obtain ⟨N', c1, c2, c3, c4, -⟩ := GlobalTheory.SplitReps.exists_conjLat V hg hL T.Q.H (T.dδ j V.rank).l₂ (badN D * p) h2 h hs
  rw [← e] at c1 c2 c3 c4
  have hcg := congAt_of_cols gm _ hc
  have hTb : Λ.TrivAt (badN D) := trivAt_of_dvd ⟨(T.dδ j V.rank).l₂.M * p, by ring⟩ hT
  have hTM : Λ.TrivAt (T.dδ j V.rank).l₂.M := trivAt_of_dvd ⟨badN D * p, by ring⟩ hT
  obtain ⟨P', ζ, hP', hζ, hroot, hR⟩ := shortRule_change_mat D T hF j hj V.rank Λ gm _ a P hgm
    (dvd_mul_left _ _) hcg hev hU c1 hTb (trivAt_of_dvd (dvd_mul_right _ _) c2) hTM c3 hP
  have hsp : Formalism.IndefR.FWT.SplitOffBad V (badN D * p * (T.dδ j V.rank).l₂.M) h :=
    GlobalTheory.SplitReps.splitOffBad_of_suppSplit V _ h hh hs
  refine ⟨h, actLat gm Λ, N', P', ζ, ?_, fun w => by rw [e]; rfl, c1, trivAt_of_dvd (dvd_mul_right _ _) c2, c3,
    trivAt_of_dvd (dvd_mul_left _ _) c2, c4, hP', hζ, hroot, fun x0 f hf => hR x0 N N' f hN c4 hf⟩
  rwa [show badN D * (T.dδ j V.rank).l₂.M * p = badN D * p * (T.dδ j V.rank).l₂.M by ring]

theorem splitOffBad_of_dvd (D : D7) (V : Formalism.BasicNotions.TH.HSp D) {a b : ℕ} (hab : a ∣ b) {h : Formalism.L2.Theta.GA D V}
    (hs : Formalism.IndefR.FWT.SplitOffBad V b h) : Formalism.IndefR.FWT.SplitOffBad V a h := by
  obtain ⟨h1, e', Q, h3, h4, h5⟩ := hs
  obtain ⟨c, rfl⟩ := hab
  refine ⟨h1, e', Q, h3, fun PP hP hbd => h4 PP hP ?_, h5⟩
  rw [Nat.cast_mul]
  exact Ideal.mul_mem_right _ _ hbd

end


open GlobalTheory.IndefiniteRowSideFullHecke.UnitaryAdjointCongruence GlobalTheory.ShortMove in
set_option maxHeartbeats 1000000 in
theorem exists_adapted : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T0 : Type) (A : FamIn D.what₂.LL G Pl0 T0 D.R.m) (T : Full D) [Algebra T.J.Q.c.F D.what₂.LL] (R : RealDat D A T.J.Q.c.F) (F : Face D A) (κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)) (v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec) (fw : FWTie T.J R κ v₀) (O : ∀ i, OMDat T.J.toCore R i Unit (fun _ => A.μ0)) (hT : LawsFull T), GlobalTheory.Hk3.Core R F → ∀ (i : Fin D.R.m), OMPins T.J R κ v₀ O i → ∀ (ℓ : G → (LaMod (T.Q.Dw ((i : ℕ) + 1)) T.Q.l ≃ₗ[𝓞 D.host.E] LaMod (T.Q.Dw ((i : ℕ) + 1)) T.Q.l)) (U : Subgroup G) (lam : HeightOneSpectrum (𝓞 D.what₂.LL)) (f : U → (recB hT.p.toLawsCore).Cusp ((i : ℕ) + 1) (κ i)), IsOrbitFamily (T.Q.Xo ((i : ℕ) + 1)) T.Q.c (badN D) (wtA (κ i)) (T.dδ ((i : ℕ) + 1) (κ i).n) (fun u : U => ℓ u) (fun u => ((f u).1 : T.R ((i : ℕ) + 1))) → ∃ (a : 𝓞 T.Q.c.F) (s : ℕ) (f' : U → (recB hT.p.toLawsCore).Cusp ((i : ℕ) + 1) (κ i)) (Λ : GenLat D.host.E (Vc D i).rank) (h : GA D (Vc D i)) (N : ℕ) (x₀ : Fin (Vc D i).rank → (T.Q.Dw ((i : ℕ) + 1)).La) (P : MvPolynomial (LtN (T.Q.Dw ((i : ℕ) + 1)) (Vc D i).rank) T.Q.c.F) (x : U → Fin (Vc D i).rank → (T.Q.Dw ((i : ℕ) + 1)).La), (s : 𝓞 D.what₂.LL) ∉ lam.asIdeal ∧ (∀ u, (s : T.Q.c.F) • ((f u).1 : T.R ((i : ℕ) + 1)) = (a : T.Q.c.F) • ((f' u).1 : T.R ((i : ℕ) + 1))) ∧ SplitOffBad (Vc D i) (badN D * (T.dδ ((i : ℕ) + 1) (Vc D i).rank).l₂.M * (O i).bad ()) h ∧ (∀ w, w ∈ Λ.La ↔ (fun b => star (w b)) ∈ Bridge.hLat (Vc D i) (fin (Vc D i) h)) ∧ Λ.TrivAt (Formalism.EigenvalueLevelCeiling.plc lam) ∧ Λ.Unimod ∧ Λ.TrivAt (badN D) ∧ Λ.TrivAt (T.dδ ((i : ℕ) + 1) (Vc D i).rank).l₂.M ∧ Λ.LevOK N (T.dδ ((i : ℕ) + 1) (Vc D i).rank).l₂.M ∧ AdmX (l := T.Q.l) true x₀ ∧ P ∈ harmL (Dw := T.Q.Dw ((i : ℕ) + 1)) T.Q.c Λ (wtA (κ i)) ∧ ∀ u : U, IsRightMul (ℓ u) x₀ (x u) ∧ AdmX (l := T.Q.l) true (x u) ∧ IsShortRule (T.Q.Xo ((i : ℕ) + 1)) T.Q.c (T.dδ ((i : ℕ) + 1) (Vc D i).rank) Λ N (x u) P ((f' u).1 : T.R ((i : ℕ) + 1)) := by
  intro D G _ _ Pl0 T0 A T _ R F κ v₀ fw O hT hk i hO ℓ U lam f hf
  have hj : InR D ((i : ℕ) + 1) := ⟨Nat.le_add_left _ _, i.2⟩
  have hrk : (Vc D i).rank = D.R.nV := D.sp.V_rank _ (Nat.le_add_left _ _) i.2
  have hn : (κ i).n = (Vc D i).rank := (fw.kap i (D.eTau.symm 1)).2.2.trans hrk.symm
  have hr : Odd D.R.r := by
    obtain ⟨a, ha⟩ := D.R.k_even
    obtain ⟨b, hb⟩ := D.R.m_even
    have h2 := D.R.two_le_m
    exact ⟨a + b - 1, by simp only [Ranks.r]; omega⟩
  have hev : Even (Vc D i).rank := hrk ▸ hr.add_odd D.R.t_odd
  have hV := hO.2.lift.std
  have hg : (Vc D i).gram = 1 := hV.1
  have hL : Bridge.hLat (Vc D i) 1 = Formalism.L2.Pj.stdLat D.host.E (Vc D i).rank := hV.2
  rw [hn] at hf
  obtain ⟨Λ, N, x₀, P, x, hU, hTb, hTM, hN, hA, hP, hx⟩ := hf
  have hp := plc_prime lam
  have hq : 0 < Formalism.EigenvalueLevelCeiling.plc lam * (O i).bad () := Nat.mul_pos hp.pos (hO.2.bad ()).1
  obtain ⟨h, Λ', N', P', ζ, hs, hmem, hU', hTb', hTM', hTp, hN', hP', hζ, ⟨m, hm, hζm⟩, hR⟩ :
      ∃ (h : GA D (Vc D i)) (Λ' : GenLat D.host.E (Vc D i).rank) (N' : ℕ)
        (P' : MvPolynomial (LtN (T.Q.Dw ((i : ℕ) + 1)) (Vc D i).rank) T.Q.c.F) (ζ : T.Q.c.F),
        SplitOffBad (Vc D i) (badN D * (T.dδ ((i : ℕ) + 1) (Vc D i).rank).l₂.M * (O i).bad ()) h ∧
        (∀ w, w ∈ Λ'.La ↔ (fun b => star (w b)) ∈ Bridge.hLat (Vc D i) (fin (Vc D i) h)) ∧
        Λ'.Unimod ∧ Λ'.TrivAt (badN D) ∧ Λ'.TrivAt (T.dδ ((i : ℕ) + 1) (Vc D i).rank).l₂.M ∧
        Λ'.TrivAt (Formalism.EigenvalueLevelCeiling.plc lam) ∧ Λ'.LevOK N' (T.dδ ((i : ℕ) + 1) (Vc D i).rank).l₂.M ∧
        P' ∈ harmL T.Q.c Λ' (wtA (κ i)) ∧ ζ ≠ 0 ∧ (∃ m : ℕ, 0 < m ∧ ζ ^ m = 1) ∧
        ∀ (x0 : Fin (Vc D i).rank → (T.Q.Dw ((i : ℕ) + 1)).La) (g : Rul (T.Q.Xo ((i : ℕ) + 1)) T.Q.c),
          IsShortRule (T.Q.Xo ((i : ℕ) + 1)) T.Q.c (T.dδ ((i : ℕ) + 1) (Vc D i).rank) Λ N x0 P g →
          IsShortRule (T.Q.Xo ((i : ℕ) + 1)) T.Q.c (T.dδ ((i : ℕ) + 1) (Vc D i).rank) Λ' N' x0 P' (ζ • g) := by
    rcases Nat.eq_zero_or_pos (badN D) with hb | hb
    · rw [hb] at hTb
      obtain ⟨h1, h2, h3⟩ := zero_case D (Vc D i) hL Λ hTb
      exact ⟨1, Λ, N, P, 1, h2 _, h1, hU, h3 _, h3 _, h3 _, hN, hP, one_ne_zero, ⟨1, one_pos, one_pow _⟩,
        fun x0 g hg => by rwa [one_smul]⟩
    · obtain ⟨Λ₁, N₁, P₁, ζ₁, hU₁, hT₁, hN₁, hP₁, hζ₁, ⟨m₁, hm₁, e₁⟩, hR₁⟩ :=
        exists_step_int D T hT ((i : ℕ) + 1) hj _ hev hb Λ N (wtA (κ i)) P hU hTb hTM hN hP _ hq
      obtain ⟨h, Λ', N', P', ζ₂, d1, d2, d3, d4, d5, d6, d7, d8, hζ₂, ⟨m₂, hm₂, e₂⟩, hR₂⟩ :=
        exists_step_split_off D T hT _ hj (Vc D i) hg hL hev hb _ hq Λ₁ N₁ _ P₁ hU₁ hT₁ hN₁ hP₁
      refine ⟨h, Λ', N', P', ζ₂ * ζ₁, splitOffBad_of_dvd D _ ⟨Formalism.EigenvalueLevelCeiling.plc lam, by ring⟩ d1, d2, d3, d4, d5,
        trivAt_of_dvd (dvd_mul_right _ _) d6, d7, d8, mul_ne_zero hζ₂ hζ₁,
        ⟨m₁ * m₂, Nat.mul_pos hm₁ hm₂, by rw [mul_pow, pow_mul' ζ₂, e₂, pow_mul ζ₁, e₁, one_pow, one_pow, one_mul]⟩,
        fun x0 g hg => ?_⟩
      rw [mul_smul]
      exact hR₂ x0 _ (hR₁ x0 g hg)
  have hint : IsIntegral ℤ (ζ ^ (m - 1)) :=
    IsIntegral.pow (IsIntegral.of_pow hm (by rw [hζm]; exact isIntegral_one)) _
  have hinv : ζ ^ (m - 1) * ζ = 1 := by rw [← pow_succ, Nat.sub_add_cancel hm, hζm]
  refine ⟨⟨ζ ^ (m - 1), hint⟩, 1, fun u => ⟨ζ • (f u).1, Submodule.smul_mem _ ζ (f u).2⟩, Λ', h, N', x₀, P', x,
    ?_, fun u => ?_, hs, hmem, hTp, hU', hTb', hTM', hN', hA, hP', fun u => ⟨(hx u).1, (hx u).2.1, hR _ _ (hx u).2.2⟩⟩
  · rw [Nat.cast_one]
    exact (Ideal.ne_top_iff_one _).1 lam.isPrime.ne_top
  · show ((1 : ℕ) : T.Q.c.F) • ((f u).1 : T.R ((i : ℕ) + 1)) = (ζ ^ (m - 1)) • (ζ • ((f u).1 : T.R ((i : ℕ) + 1)))
    rw [Nat.cast_one, one_smul, smul_smul, hinv, one_smul]

end GlobalTheory.OrbitAdapt
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSplitPlaceConjHeisenbergInvariantForm
section
open scoped TensorProduct Matrix
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open Formalism.IndefR.DatumF
open MeasureTheory

noncomputable section

namespace GlobalTheory.SplitInvFormF

theorem exists_invForm_split : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E),
    B.IsGood σ → ∀ (nS nT : ℕ) (JS : Matrix (Fin nS) (Fin nS) E) (JT : Matrix (Fin nT) (Fin nT) E),
      IsHermND σ JS → IsHermND σ JT → ∀ ξ₀ : E, ξ₀ ≠ 0 → σ ξ₀ = -ξ₀ →
      ∀ e, IsSplitIdemF σ e → ∀ f₀ : WOF F E nS nT → ℂ, IsThetaFunOF σ JS JT ξ₀ B.ψ f₀ → f₀ ≠ 0 →
        ∃ ℓ : (WOF F E nS nT → ℂ) →ₗ[ℂ] ℂ,
          (∀ u : WOF F E nS nT, (∀ i j, cAF σ e * u i j = u i j) → ∀ f, IsThetaFunOF σ JS JT ξ₀ B.ψ f →
            ℓ (heisOF σ JS JT ξ₀ B.ψ u f) = ℓ f) ∧
          ∃ f, IsThetaFunOF σ JS JT ξ₀ B.ψ f ∧ ℓ f ≠ 0 := by
  intro F E _ _ _ _ _ σ B hB nS nT JS JT hS hT ξ₀ hξ hσξ e he f₀ hf₀ hf₀0
  obtain ⟨φ, hφ, hφ0, hd⟩ := _root_.PositivityTheory.ThKW.SplitVacuumEigenvectors.exists_vac_split F E σ B hB nS nT JS JT hS hT ξ₀ hξ hσξ e he f₀ hf₀ hf₀0
  obtain ⟨ℓ, h1, h2⟩ := GlobalTheory.HalfCoinv.exists_form (Y := conjHalf σ e nS nT) (ρ := heisL σ JS JT ξ₀ B.ψ)
    (B := commF σ JS JT ξ₀ B.ψ) (Θ := {g | IsThetaFunOF σ JS JT ξ₀ B.ψ g})
    (fun x hx x' hx' f => by
      show heisOF σ JS JT ξ₀ B.ψ x (heisOF σ JS JT ξ₀ B.ψ x' f) = heisOF σ JS JT ξ₀ B.ψ (x + x') f
      rw [heisOF_heisOF, symplOHF_half he hx hx', AddChar.map_zero_eq_one, one_smul])
    (fun f => heisOF_zero f) (fun u y f => heisOF_comm u y f)
    (fun u hu g hg => exists_nsmul_fix he hu hg) hφ0 hd
  exact ⟨ℓ, fun u hu f hf => h1 u hu f hf, φ, hφ, h2⟩

end GlobalTheory.SplitInvFormF

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUnifDvd
section
set_option autoImplicit false

noncomputable section

open Formalism.CohomologicalDescent.DepthNonnegative Formalism.CohomologicalDescent.ShortWeightBounds GlobalTheory.ExpFrame

namespace GlobalTheory.ExpModel

open GlobalTheory.ExpTie

theorem exists_unif_dvd (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [CharZero O] (l : ℕ)
    (hl : l ≠ 0) (hu : ¬ IsUnit ((l : ℕ) : O)) :
    ∃ (ϖ : O) (n : ℕ), Irreducible ϖ ∧ ϖ ∣ (l : O) ∧ (l : O) ∣ ϖ ^ n := by
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible O
  have h0 : ((l : ℕ) : O) ≠ 0 := Nat.cast_ne_zero.2 hl
  obtain ⟨n, hn⟩ := IsDiscreteValuationRing.associated_pow_irreducible h0 hϖ
  refine ⟨ϖ, n, hϖ, ?_, hn.dvd⟩
  rcases n with _ | n
  · exact absurd (hn.isUnit_iff.2 (by simp)) hu
  · exact (dvd_pow_self ϖ n.succ_ne_zero).trans hn.symm.dvd

end GlobalTheory.ExpModel

namespace GlobalTheory.ExpModel

open GlobalTheory.ExpTie

section Sub

variable {ι : Type} {N : ℕ} {lam : ι → ℕ → ℕ} (X : HidaSetting ι N lam) (ϖ : X.O)

abbrev Red : Type := NablaT X.O N lam ⧸ scaleSub X.A (NablaT X.O N lam) ϖ

abbrev SimpIx : Type :=
  Σ E : Submodule X.A (Red X ϖ), {N' : Submodule X.A E // IsSimpleModule X.A (E ⧸ N')}

abbrev SimpMod (μ : SimpIx X ϖ) : Type := μ.1 ⧸ μ.2.1

variable {X ϖ}

theorem exists_simpMod (Gm : Type) [AddCommGroup Gm] [Module X.A Gm] [IsSimpleModule X.A Gm]
    (h : IsSubquot X.A (Red X ϖ) Gm) :
    ∃ μ : SimpIx X ϖ, Nonempty (Gm ≃ₗ[X.A] SimpMod X ϖ μ) := by
  obtain ⟨E, ψ, hψ⟩ := h
  let e := ψ.quotKerEquivOfSurjective hψ
  haveI : IsSimpleModule X.A (E ⧸ LinearMap.ker ψ) := IsSimpleModule.congr e
  exact ⟨⟨E, LinearMap.ker ψ, inferInstance⟩, ⟨e.symm⟩⟩

end Sub

end GlobalTheory.ExpModel

namespace GlobalTheory.ExpModel

section SubF

variable {l : ℕ} [Fact l.Prime] {ι : Type} [DecidableEq ι] {N : ℕ} (F : Frame l ι N) (lam : ι → ℕ → ℕ)
  (jK : F.K →* alg F.O N lam) [mT : Module F.T (Forms F.O (A := alg F.O N lam) F.Γ jK (NablaT F.O N lam))]
  [@IsScalarTower F.O F.T (Forms F.O (A := alg F.O N lam) F.Γ jK (NablaT F.O N lam)) _ mT.toSMul _]
  (m : Ideal F.T) [m.IsPrime] (ϖ : F.O)

end SubF

end GlobalTheory.ExpModel

end
end

