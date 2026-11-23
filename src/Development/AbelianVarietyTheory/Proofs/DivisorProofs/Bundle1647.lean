module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0047
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.Bundle0019
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1487
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1507
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1531
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContinuousAtPlace
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0118
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1556
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1565
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1579
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1582
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1572
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1617
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1634
public import Formalism.LocalToGlobal.IndefiniteReal.FinitePlaces.Bundle0002
public import Formalism.SharpRestriction.GlobalSchurBounds.GlobalRankLatticeProofs.UnitTraceSumBounds.Bundle0008
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.UnitaryHeckeCharacterValues
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0222
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0066
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.DefiniteThetaPairTestVectorExpansion
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0247
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1624
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1227
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1234
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1625
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.HoweUnram
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsCoversOfHalves
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0902
public import Formalism.LocalToGlobal.IndefiniteReal.OneMapT
public import Formalism.LocalToGlobal.IndefiniteReal.Bundle0023
public import Formalism.LocalToGlobal.IndefiniteReal.FWExist
public import Formalism.LocalRingCardinality.Bundle0007
public import Formalism.LocalRingCardinality.Bundle0003

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFinitePlaceVacuumOfHeisenbergLattice
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links
open IsDedekindDomain NumberField MeasureTheory Matrix
open Classical
open scoped TensorProduct ComplexConjugate GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open GlobalTheory.FunObj GlobalTheory.ChiGrid GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames Formalism.L2.DIV
open GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation (spV spW spW₁ spV₁ alpha beta Num skewGram blk conjU)
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model HasExp SplitsFully Chars)

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

open scoped GlobalTheory.VacAny

noncomputable section

open Matrix

namespace GlobalTheory.HeisLatVac

open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (At Acts)

theorem exists_local_vac {F : Type} [Field F] [NumberField F] (v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl (F := F)) {κ : Type} [Fintype κ]
    (ψ₀ : AddChar (Fv F v) ℂ) (hc : Continuous ψ₀) (hne : ψ₀ ≠ 1)
    (Λ : AddSubgroup ((κ → Fv F v) × (κ → Fv F v))) (ho : IsOpen (Λ : Set ((κ → Fv F v) × (κ → Fv F v))))
    (hk : IsCompact (Λ : Set ((κ → Fv F v) × (κ → Fv F v))))
    (χ : (κ → Fv F v) × (κ → Fv F v) → ℂ) (h0 : χ 0 = 1)
    (hco : ∀ u ∈ Λ, ∀ u' ∈ Λ, χ (u + u') = χ u * χ u' * ψ₀ (⅟(2 : Fv F v) * (u.1 ⬝ᵥ u'.2 - u'.1 ⬝ᵥ u.2)))
    (h2 : ∀ u ∈ Λ, χ (u + u) = 1) :
    ∃ φ ∈ GlobalTheory.WeilM.SB (κ → Fv F v), φ ≠ 0 ∧ ∀ u ∈ Λ, GlobalTheory.WeilM.schr ψ₀ u φ = χ u • φ := by
  have hsq : ∀ u ∈ Λ, χ u * χ u = 1 := fun u hu => by
    have e := hco u hu u hu
    rw [h2 u hu, sub_self, mul_zero, AddChar.map_zero_eq_one, mul_one] at e
    exact e.symm
  have hiso : ∀ u ∈ Λ, ∀ w ∈ Λ, ψ₀ (u.1 ⬝ᵥ w.2 - w.1 ⬝ᵥ u.2) = 1 := by
    intro u hu w hw
    have e1 := hco u hu w hw
    have e2 := hco w hw u hu
    rw [add_comm w u, e1, mul_comm (χ w) (χ u)] at e2
    have hne0 : χ u * χ w ≠ 0 :=
      mul_ne_zero (left_ne_zero_of_mul_eq_one (hsq u hu)) (left_ne_zero_of_mul_eq_one (hsq w hw))
    set a := ⅟(2 : Fv F v) * (u.1 ⬝ᵥ w.2 - w.1 ⬝ᵥ u.2) with ha_def
    have ha : ⅟(2 : Fv F v) * (w.1 ⬝ᵥ u.2 - u.1 ⬝ᵥ w.2) = -a := by rw [ha_def]; ring
    rw [ha] at e2
    have e3 : ψ₀ a = ψ₀ (-a) := mul_left_cancel₀ hne0 e2
    have e4 : u.1 ⬝ᵥ w.2 - w.1 ⬝ᵥ u.2 = a + a := by
      rw [ha_def, ← two_mul, ← mul_assoc, mul_invOf_self, one_mul]
    rw [e4, AddChar.map_add_eq_mul]
    calc ψ₀ a * ψ₀ a = ψ₀ (-a) * ψ₀ a := congrArg (· * ψ₀ a) e3
      _ = 1 := by rw [← AddChar.map_add_eq_mul, neg_add_cancel, AddChar.map_zero_eq_one]
  let L : AddSubgroup (κ → Fv F v) := Λ.comap (AddMonoidHom.inr (κ → Fv F v) (κ → Fv F v))
  let L' : AddSubgroup (κ → Fv F v) := Λ.comap ((AddMonoidHom.inr (κ → Fv F v) (κ → Fv F v)).comp
    (DistribSMul.toAddMonoidHom (κ → Fv F v) (⅟(2 : Fv F v))))
  have hL : IsCompact (L : Set (κ → Fv F v)) := by
    have e : (L : Set (κ → Fv F v)) = Prod.snd '' ((Λ : Set ((κ → Fv F v) × (κ → Fv F v))) ∩ {u | u.1 = 0}) := by
      ext y
      constructor
      · intro hy
        exact ⟨(0, y), ⟨hy, rfl⟩, rfl⟩
      · rintro ⟨u, ⟨hu, hu1⟩, rfl⟩
        have : u = (0, u.2) := Prod.ext hu1 rfl
        show (0, u.2) ∈ Λ
        rw [← this]; exact hu
    rw [e]
    exact (hk.inter_right (isClosed_eq continuous_fst continuous_const)).image continuous_snd
  have hL' : IsOpen (L' : Set (κ → Fv F v)) := by
    rw [AddSubgroup.coe_comap]
    exact ho.preimage (continuous_const.prodMk (continuous_const.smul continuous_id))
  obtain ⟨x₀, hx₀⟩ := GlobalTheory.T.exists_dotProduct_representation_compact_character_local v ψ₀ hc hne L hL L' hL' (fun y => χ (0, y))
    (fun y hy y' hy' => by
      have e := hco _ hy _ hy'
      simp only [AddMonoidHom.inr_apply, Prod.mk_add_mk, add_zero, zero_dotProduct, sub_self, mul_zero,
        AddChar.map_zero_eq_one, mul_one] at e
      exact e)
    (fun y hy hy' => by
      have e := h2 _ hy'
      simp only [AddMonoidHom.coe_comp, Function.comp_apply, AddMonoidHom.inr_apply,
        DistribSMul.toAddMonoidHom_apply, Prod.mk_add_mk, add_zero] at e
      rwa [← add_smul, invOf_two_add_invOf_two, one_smul] at e)
  have hx : ∀ y : κ → Fv F v, ((0 : κ → Fv F v), y) ∈ Λ → χ (0, y) = ψ₀ (x₀ ⬝ᵥ y) := fun y hy => hx₀ y hy
  refine ⟨vacFn ψ₀ Λ χ x₀, ⟨GlobalTheory.T.isLocallyConstant_heisenberg_lattice_vacuum_function v ψ₀ hc Λ ho χ x₀ hco hx h2, GlobalTheory.T.heisenbergLatticeVacuumFn_hasCompactSupport v ψ₀ Λ χ x₀ hk⟩, ?_,
    _root_.GlobalTheory.HeisLatVac.schr_vacFn ψ₀ Λ χ x₀ hco hx hiso⟩
  intro h
  have e := _root_.GlobalTheory.HeisLatVac.vacFn_apply_add ψ₀ Λ χ x₀ hco hx 0 (zero_mem _)
  simp only [Prod.fst_zero, Prod.snd_zero, add_zero, dotProduct_zero, neg_zero, mul_zero, sub_zero,
    AddChar.map_zero_eq_one, h0, mul_one, h, Pi.zero_apply] at e
  exact zero_ne_one e

end GlobalTheory.HeisLatVac

namespace GlobalTheory.HeisLatVac

theorem exists_vac_of_lattice : ∀ {F : Type} [Field F] [NumberField F] {W : Type} [AddCommGroup W] [Module (AF F) W]
    {B : W → W → AF F} {κ : Type} [Fintype κ] (co : GlobalTheory.WeilM.Darboux B κ) (ψ : AddChar (AF F) ℂ)
    (v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl (F := F)), Continuous ψ → GlobalTheory.LatVac.psiAt ψ v ≠ 1 →
    ∀ Γ : AddSubgroup W, (∀ γ ∈ Γ, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.At (GlobalTheory.AdelicU.evFin F v) γ) →
    (∀ a ∈ v.adicCompletionIntegers F, ∀ γ ∈ Γ, GlobalTheory.LatVac.liftV v a • γ ∈ Γ) →
    IsOpen ((Γ.map (GlobalTheory.LatVac.locCo co v) : AddSubgroup ((κ → Fv F v) × (κ → Fv F v))) : Set ((κ → Fv F v) × (κ → Fv F v))) →
    IsCompact ((Γ.map (GlobalTheory.LatVac.locCo co v) : AddSubgroup ((κ → Fv F v) × (κ → Fv F v))) : Set ((κ → Fv F v) × (κ → Fv F v))) →
    ∀ c : W → ℂ, c 0 = 1 → (∀ γ ∈ Γ, ∀ γ' ∈ Γ, c (γ + γ') = c γ * c γ' * ψ (⅟(2 : AF F) * B γ γ')) →
    (∀ γ ∈ Γ, c (GlobalTheory.LatVac.liftV v 2 • γ) = 1) →
    ∃ φ : (κ → Fv F v) → ℂ, φ ∈ GlobalTheory.WeilM.SB _ ∧ φ ≠ 0 ∧
      ∀ γ ∈ Γ, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Acts (GlobalTheory.AdelicU.evFin F v) (co.rho ψ γ) φ (c γ • φ) := by
  intro F _ _ W _ _ B κ _ co ψ v hψc hψ1 Γ hAt _hO hopen hcomp c hc0 hcoc hc2
  have hsupp : ∀ a : AF F, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.At (GlobalTheory.AdelicU.evFin F v) a →
      a = GlobalTheory.LatVac.liftV v (GlobalTheory.AdelicU.evFin F v a) := by
    intro a ha
    have h1 := ha (1 - GlobalTheory.LatVac.liftV v 1) (by rw [map_sub, map_one, GlobalTheory.LatVac.evFin_liftV, sub_self])
    rw [smul_eq_mul, sub_mul, one_mul, sub_eq_zero] at h1
    conv_lhs => rw [h1]
    exact GlobalTheory.EmbChart.atPlace_mul_right v 1 a |>.trans (by rw [one_mul]; rfl)
  have hψloc : ∀ a : AF F, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.At (GlobalTheory.AdelicU.evFin F v) a →
      ψ a = GlobalTheory.LatVac.psiAt ψ v (GlobalTheory.AdelicU.evFin F v a) := by
    intro a ha
    conv_lhs => rw [hsupp a ha]
    rfl
  have hAtE : ∀ γ, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.At (GlobalTheory.AdelicU.evFin F v) γ → ∀ k,
      GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.At (GlobalTheory.AdelicU.evFin F v) ((co.e γ).1 k) ∧
      GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.At (GlobalTheory.AdelicU.evFin F v) ((co.e γ).2 k) := by
    intro γ hγ k
    have e : ∀ u : AF F, GlobalTheory.AdelicU.evFin F v u = 0 → u • co.e γ = 0 := fun u hu => by
      rw [← LinearEquiv.map_smul, hγ u hu, map_zero]
    exact ⟨fun u hu => by simpa using congrArg (fun p => p.1 k) (e u hu),
      fun u hu => by simpa using congrArg (fun p => p.2 k) (e u hu)⟩
  have hinj : ∀ γ ∈ Γ, ∀ γ' ∈ Γ, GlobalTheory.LatVac.locCo co v γ = GlobalTheory.LatVac.locCo co v γ' → γ = γ' := by
    intro γ hγ γ' hγ' h
    have hδ := hAt _ (sub_mem hγ hγ')
    have h0 : GlobalTheory.LatVac.locCo co v (γ - γ') = 0 := by rw [map_sub, h, sub_self]
    have he : co.e (γ - γ') = 0 := by
      refine Prod.ext (funext fun k => ?_) (funext fun k => ?_)
      · rw [hsupp _ (hAtE _ hδ k).1]
        have := congrFun (congrArg Prod.fst h0) k
        change GlobalTheory.AdelicU.evFin F v ((co.e (γ - γ')).1 k) = 0 at this
        rw [this, map_zero]; rfl
      · rw [hsupp _ (hAtE _ hδ k).2]
        have := congrFun (congrArg Prod.snd h0) k
        change GlobalTheory.AdelicU.evFin F v ((co.e (γ - γ')).2 k) = 0 at this
        rw [this, map_zero]; rfl
    rw [LinearEquiv.map_eq_zero_iff, sub_eq_zero] at he
    exact he
  classical
  let χ : (κ → Fv F v) × (κ → Fv F v) → ℂ := fun u =>
    if h : ∃ γ ∈ Γ, GlobalTheory.LatVac.locCo co v γ = u then c h.choose else 0
  have hχ : ∀ γ ∈ Γ, χ (GlobalTheory.LatVac.locCo co v γ) = c γ := by
    intro γ hγ
    have h : ∃ γ' ∈ Γ, GlobalTheory.LatVac.locCo co v γ' = GlobalTheory.LatVac.locCo co v γ := ⟨γ, hγ, rfl⟩
    simp only [χ, dif_pos h]
    rw [hinj _ h.choose_spec.1 _ hγ h.choose_spec.2]
  have hcont : Continuous (GlobalTheory.LatVac.psiAt ψ v) := GlobalTheory.VacAny.continuous_psiV hψc v
  obtain ⟨φ, hSB, hne, heig⟩ := exists_local_vac v (GlobalTheory.LatVac.psiAt ψ v) hcont hψ1
    (Γ.map (GlobalTheory.LatVac.locCo co v)) hopen hcomp χ
    (by rw [← map_zero (GlobalTheory.LatVac.locCo co v), hχ 0 (zero_mem _), hc0])
    (by
      rintro _ ⟨γ, hγ, rfl⟩ _ ⟨γ', hγ', rfl⟩
      rw [← map_add (f := _), hχ _ (add_mem hγ hγ'), hχ _ hγ, hχ _ hγ', hcoc γ hγ γ' hγ']
      congr 1
      have at_mul_left (x : AF F) {y : AF F}
          (hy : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.At (GlobalTheory.AdelicU.evFin F v) y) :
          GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.At (GlobalTheory.AdelicU.evFin F v) (x * y) := fun u hu => by
        rw [smul_eq_mul, mul_left_comm, show u * y = 0 from hy u hu, mul_zero]
      have at_sub {x y : AF F}
          (hx : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.At (GlobalTheory.AdelicU.evFin F v) x)
          (hy : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.At (GlobalTheory.AdelicU.evFin F v) y) :
          GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.At (GlobalTheory.AdelicU.evFin F v) (x - y) := fun u hu => by
        rw [smul_sub, hx u hu, hy u hu, sub_self]
      have at_sum : ∀ (s : Finset κ) {f : κ → AF F},
          (∀ i ∈ s, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.At (GlobalTheory.AdelicU.evFin F v) (f i)) →
          GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.At (GlobalTheory.AdelicU.evFin F v) (∑ i ∈ s, f i) := by
        intro s f h
        induction s using Finset.induction_on with
        | empty => simp only [Finset.sum_empty]; exact fun u _ => smul_zero u
        | insert a s ha ih =>
          rw [Finset.sum_insert ha]
          exact fun u hu => by rw [smul_add, h a (Finset.mem_insert_self a s) u hu,
            ih (fun i hi => h i (Finset.mem_insert_of_mem hi)) u hu, add_zero]
      have evFin_invOf_two : GlobalTheory.AdelicU.evFin F v (⅟(2 : AF F)) = ⅟(2 : Fv F v) := by
        refine (invOf_eq_right_inv ?_).symm
        have h : GlobalTheory.AdelicU.evFin F v (2 * ⅟(2 : AF F)) = 1 := by rw [mul_invOf_self, map_one]
        rwa [map_mul, map_ofNat] at h
      have hA : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.At (GlobalTheory.AdelicU.evFin F v) (⅟(2 : AF F) * B γ γ') := by
        rw [co.form]
        refine at_mul_left _ (at_sub ?_ ?_)
        · exact at_sum _ fun i _ => at_mul_left _ (hAtE _ (hAt _ hγ') i).2
        · exact at_sum _ fun i _ => at_mul_left _ (hAtE _ (hAt _ hγ) i).2
      rw [hψloc _ hA, co.form, map_mul, evFin_invOf_two, map_sub]
      set_option synthInstance.maxHeartbeats 100000 in
        simp only [dotProduct, map_sum, map_mul]
      rfl)
    (by
      rintro _ ⟨γ, hγ, rfl⟩
      rw [← map_add (f := _), hχ _ (add_mem hγ hγ)]
      have e : γ + γ = GlobalTheory.LatVac.liftV v 2 • γ := by
        have h := hAt γ hγ (GlobalTheory.LatVac.liftV v 2 - 2)
          (by rw [map_sub, GlobalTheory.LatVac.evFin_liftV, map_ofNat, sub_self])
        rw [sub_smul, sub_eq_zero, two_smul] at h
        exact h.symm
      rw [e]
      exact hc2 γ hγ)
  refine ⟨φ, hSB, hne, fun γ hγ => ?_⟩
  have hb := GlobalTheory.T.adelicHeisenberg_acts_by_local_schrodinger co ψ v γ (hAt γ hγ) φ
  rwa [heig _ (AddSubgroup.mem_map_of_mem _ hγ), hχ γ hγ] at hb

end GlobalTheory.HeisLatVac
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLevelCurvePhaseEqOfClose
section
open NumberField MeasureTheory
open scoped Classical
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum
open Formalism.MainNotions.TaylorLogMetric (VC embT tor0 Hf lamOf area Th U)
open Formalism.MainNotions.StandardLatticesGL3 (WeilO HeckeU TT stdL pt oddE0)
open GlobalTheory.NormSum (Pair Tup minorPol ratG intG Cls gam)
open GlobalTheory.NormDict GlobalTheory.NormExact
open GlobalTheory.BotFormula (IsFinPt)
open GlobalTheory.IndefiniteRowSideFullHecke.ClassFunctionSumIntegral (IsDefiniteSpace IsOpenCompactLevel)

attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section
namespace GlobalTheory.PhaseMove

theorem trace_sum_int : ∀ (D : D7) (w : D.host.E), IsIntegral ℤ w → ∃ m : ℤ, 2 * (∑ τ, Formalism.MainNotions.TaylorLogMetric.embT D τ w).re = m := by
  intro D w hw
  have htr := Formalism.MainNotions.Ext.trace_sum_over_letters_holds D w
  have ht : IsIntegral ℤ (Algebra.trace D.host.K D.host.E w) := Algebra.isIntegral_trace hw
  obtain ⟨u, v, huv⟩ := ((GlobalTheory.MomDict.main D).2.2.1 _).2 ⟨⟨_, ht⟩, rfl⟩
  refine ⟨2 * u + v, ?_⟩
  rw [htr]
  erw [huv]
  simp [GlobalTheory.MomOne.wK]
  ring

def cTA (D : D7) {m p : ℕ} (B : Matrix (Fin m) (Fin p) (Formalism.MainNotions.StandardLatticesGL3.AE D)) : Matrix (Fin p) (Fin m) (Formalism.MainNotions.StandardLatticesGL3.AE D) :=
  (B.map (Formalism.MainNotions.StandardLatticesGL3.sgA D)).transpose

theorem sq_unitary : ∀ {D : D7} {a d : ℕ} (x : Formalism.MainNotions.StandardLatticesGL3.GA D a) (y : Formalism.MainNotions.StandardLatticesGL3.GA D d) (A : Matrix (Fin d) (Fin a) (Formalism.MainNotions.StandardLatticesGL3.AE D)), (∑ i, ∑ j, (((y : GL (Fin d) (Formalism.MainNotions.StandardLatticesGL3.AE D)) : Matrix (Fin d) (Fin d) (Formalism.MainNotions.StandardLatticesGL3.AE D)) * A * ((((x : GL (Fin a) (Formalism.MainNotions.StandardLatticesGL3.AE D))⁻¹ : GL (Fin a) (Formalism.MainNotions.StandardLatticesGL3.AE D))) : Matrix (Fin a) (Fin a) (Formalism.MainNotions.StandardLatticesGL3.AE D))) i j * Formalism.MainNotions.StandardLatticesGL3.sgA D ((((y : GL (Fin d) (Formalism.MainNotions.StandardLatticesGL3.AE D)) : Matrix (Fin d) (Fin d) (Formalism.MainNotions.StandardLatticesGL3.AE D)) * A * ((((x : GL (Fin a) (Formalism.MainNotions.StandardLatticesGL3.AE D))⁻¹ : GL (Fin a) (Formalism.MainNotions.StandardLatticesGL3.AE D))) : Matrix (Fin a) (Fin a) (Formalism.MainNotions.StandardLatticesGL3.AE D))) i j)) = ∑ i, ∑ j, A i j * Formalism.MainNotions.StandardLatticesGL3.sgA D (A i j) := by
  intro D a d x y A
  have hinv : ∀ e : D.host.E, D.host.conj (D.host.conj e) = e := fun e => by
    apply D.host.φ₀.injective
    have h1 := D.host.conjE_apply D.host.φ₀
    change D.host.φ₀ (D.host.conj (D.host.conj e)) = _
    rw [h1, h1, Complex.conj_conj]
  have hsg : ∀ u : Formalism.MainNotions.StandardLatticesGL3.AE D, Formalism.MainNotions.StandardLatticesGL3.sgA D (Formalism.MainNotions.StandardLatticesGL3.sgA D u) = u := fun u => by
    induction u using TensorProduct.induction_on with
    | zero => simp
    | tmul e r =>
      change (Algebra.TensorProduct.map _ _) ((Algebra.TensorProduct.map _ _) (e ⊗ₜ r)) = e ⊗ₜ r
      simp only [Algebra.TensorProduct.map_tmul, AlgHom.id_apply]
      congr 1
      exact hinv e
    | add u v hu hv => rw [map_add (f := _), map_add (f := _), hu, hv]
  have hΦ : ∀ B : Matrix (Fin d) (Fin a) (Formalism.MainNotions.StandardLatticesGL3.AE D), (∑ i, ∑ j, B i j * Formalism.MainNotions.StandardLatticesGL3.sgA D (B i j)) = (B * cTA D B).trace := fun B => by
    simp [cTA, Matrix.trace, Matrix.mul_apply]
  have hmul : ∀ {m p q : ℕ} (B : Matrix (Fin m) (Fin p) (Formalism.MainNotions.StandardLatticesGL3.AE D)) (C : Matrix (Fin p) (Fin q) (Formalism.MainNotions.StandardLatticesGL3.AE D)), cTA D (B * C) = cTA D C * cTA D B := fun B C => by
    simp only [cTA, Matrix.map_mul, Matrix.transpose_mul]
  have hcc : ∀ {m p : ℕ} (B : Matrix (Fin m) (Fin p) (Formalism.MainNotions.StandardLatticesGL3.AE D)), cTA D (cTA D B) = B := fun B => by
    ext i j; simp [cTA, hsg]
  have hU : ∀ {m : ℕ} (g : Formalism.MainNotions.StandardLatticesGL3.GA D m), cTA D ((g : GL (Fin m) (Formalism.MainNotions.StandardLatticesGL3.AE D)) : Matrix (Fin m) (Fin m) (Formalism.MainNotions.StandardLatticesGL3.AE D)) * ((g : GL (Fin m) (Formalism.MainNotions.StandardLatticesGL3.AE D)) : Matrix (Fin m) (Fin m) (Formalism.MainNotions.StandardLatticesGL3.AE D)) = 1 := fun g => by
    have h := g.2
    change Formalism.UG.cT _ _ * ((1 : Matrix _ _ D.host.E).map _) * _ = (1 : Matrix _ _ D.host.E).map _ at h
    rw [Matrix.map_one _ (map_zero _) (map_one _), Matrix.mul_one] at h
    exact h
  set X : Matrix (Fin a) (Fin a) (Formalism.MainNotions.StandardLatticesGL3.AE D) := ((x : GL (Fin a) (Formalism.MainNotions.StandardLatticesGL3.AE D)) : Matrix (Fin a) (Fin a) (Formalism.MainNotions.StandardLatticesGL3.AE D)) with hX
  set V : Matrix (Fin a) (Fin a) (Formalism.MainNotions.StandardLatticesGL3.AE D) := ((((x : GL (Fin a) (Formalism.MainNotions.StandardLatticesGL3.AE D))⁻¹ : GL (Fin a) (Formalism.MainNotions.StandardLatticesGL3.AE D))) : Matrix (Fin a) (Fin a) (Formalism.MainNotions.StandardLatticesGL3.AE D)) with hV
  set Y : Matrix (Fin d) (Fin d) (Formalism.MainNotions.StandardLatticesGL3.AE D) := ((y : GL (Fin d) (Formalism.MainNotions.StandardLatticesGL3.AE D)) : Matrix (Fin d) (Fin d) (Formalism.MainNotions.StandardLatticesGL3.AE D)) with hY
  have hVX : V * X = 1 := by rw [hV, hX, ← Units.val_mul, inv_mul_cancel, Units.val_one]
  have hXc : X * cTA D X = 1 := mul_eq_one_comm.1 (hU x)
  have hVe : V = cTA D X := by
    calc V = V * (X * cTA D X) := by rw [hXc, Matrix.mul_one]
      _ = cTA D X := by rw [← Matrix.mul_assoc, hVX, Matrix.one_mul]
  have hVV : V * cTA D V = 1 := by rw [hVe, hcc, hU x]
  rw [hΦ, hΦ, hmul, hmul, Matrix.mul_assoc, Matrix.mul_assoc, ← Matrix.mul_assoc V, hVV, Matrix.one_mul,
    ← Matrix.mul_assoc, Matrix.trace_mul_comm, ← Matrix.mul_assoc]
  have hY1 : cTA D Y * Y = 1 := hU y
  rw [Matrix.mul_assoc (cTA D A), hY1, Matrix.mul_one, Matrix.trace_mul_comm]

theorem sq_move_int : ∀ {D : D7} (cc : Ideal (𝓞 D.host.K)) {a d : ℕ} (A : Matrix (Fin d) (Fin a) (Formalism.MainNotions.StandardLatticesGL3.AE D)) (M : ℕ), 0 < M → ∃ n : ℕ, 0 < n ∧ ∀ A' : Matrix (Fin d) (Fin a) (Formalism.MainNotions.StandardLatticesGL3.AE D), (∀ i j, ∃ t ∈ Formalism.MainNotions.StandardLatticesGL3.IhE D cc, A' i j - A i j = (n : Formalism.MainNotions.StandardLatticesGL3.AE D) * t) → ∃ s ∈ Formalism.MainNotions.StandardLatticesGL3.OhE D, (∑ i, ∑ j, A' i j * Formalism.MainNotions.StandardLatticesGL3.sgA D (A' i j)) - (∑ i, ∑ j, A i j * Formalism.MainNotions.StandardLatticesGL3.sgA D (A i j)) = (M : Formalism.MainNotions.StandardLatticesGL3.AE D) * s := by
  intro D cc a d A M hM
  obtain ⟨B, hB, hBA⟩ := GlobalTheory.NormSum.Expand.denom_fin (fun k : Fin d × Fin a => A k.1 k.2)
  obtain ⟨m, hm, hmI⟩ := GlobalTheory.CompletedLattice.exists_mul_IhE_mem D cc
  refine ⟨M * B * m, by positivity, fun A' hA' => ?_⟩
  choose t ht et using hA'
  have hsg : ∀ u ∈ Formalism.MainNotions.StandardLatticesGL3.OhE D, Formalism.MainNotions.StandardLatticesGL3.sgA D u ∈ Formalism.MainNotions.StandardLatticesGL3.OhE D := fun u hu =>
    GlobalTheory.NormSum.UnramHecke.sgA_mem D hu
  have hA1 : ∀ i j, (B : Formalism.MainNotions.StandardLatticesGL3.AE D) * A i j ∈ Formalism.MainNotions.StandardLatticesGL3.OhE D := fun i j => hBA (i, j)
  have ht1 : ∀ i j, (m : Formalism.MainNotions.StandardLatticesGL3.AE D) * t i j ∈ Formalism.MainNotions.StandardLatticesGL3.OhE D := fun i j => hmI _ (ht i j)
  refine ⟨∑ i, ∑ j, (((B : Formalism.MainNotions.StandardLatticesGL3.AE D) * A i j) * Formalism.MainNotions.StandardLatticesGL3.sgA D ((m : Formalism.MainNotions.StandardLatticesGL3.AE D) * t i j) +
      ((m : Formalism.MainNotions.StandardLatticesGL3.AE D) * t i j) * Formalism.MainNotions.StandardLatticesGL3.sgA D ((B : Formalism.MainNotions.StandardLatticesGL3.AE D) * A i j) +
      ((M * B * B : ℕ) : Formalism.MainNotions.StandardLatticesGL3.AE D) * (((m : Formalism.MainNotions.StandardLatticesGL3.AE D) * t i j) * Formalism.MainNotions.StandardLatticesGL3.sgA D ((m : Formalism.MainNotions.StandardLatticesGL3.AE D) * t i j))),
    sum_mem fun i _ => sum_mem fun j _ => add_mem (add_mem (mul_mem (hA1 i j) (hsg _ (ht1 i j)))
      (mul_mem (ht1 i j) (hsg _ (hA1 i j)))) (mul_mem (natCast_mem _ _) (mul_mem (ht1 i j) (hsg _ (ht1 i j)))), ?_⟩
  have hA' : ∀ i j, A' i j = A i j + ((M * B * m : ℕ) : Formalism.MainNotions.StandardLatticesGL3.AE D) * t i j := fun i j => by
    rw [← et i j]; ring
  simp only [hA', Finset.mul_sum, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  simp only [map_add (f := _), map_mul, map_natCast]
  push_cast
  ring

theorem sq_diff_int : ∀ {D : D7} (cc : Ideal (𝓞 D.host.K)) {a d : ℕ} (x : Formalism.MainNotions.StandardLatticesGL3.GA D a) (y : Formalism.MainNotions.StandardLatticesGL3.GA D d) (z : Matrix (Fin d) (Fin a) D.host.E) (M : ℕ), 0 < M → ∃ n : ℕ, 0 < n ∧ ∀ z' : Matrix (Fin d) (Fin a) D.host.E, Formalism.MainNotions.StandardLatticesGL3.CloseTo D cc n (x : GL (Fin a) (Formalism.MainNotions.StandardLatticesGL3.AE D)) (y : GL (Fin d) (Formalism.MainNotions.StandardLatticesGL3.AE D)) z z' → IsIntegral ℤ (((∑ i, ∑ j, z' i j * D.host.conj (z' i j)) - ∑ i, ∑ j, z i j * D.host.conj (z i j)) / (M : D.host.E)) := by
  intro D cc a d x y z M hM
  obtain ⟨n, hn, h⟩ := sq_move_int cc ((((y : GL (Fin d) (Formalism.MainNotions.StandardLatticesGL3.AE D)) : Matrix (Fin d) (Fin d) (Formalism.MainNotions.StandardLatticesGL3.AE D)) * z.map (Formalism.MainNotions.StandardLatticesGL3.inc D) * ((((x : GL (Fin a) (Formalism.MainNotions.StandardLatticesGL3.AE D))⁻¹ : GL (Fin a) (Formalism.MainNotions.StandardLatticesGL3.AE D))) : Matrix (Fin a) (Fin a) (Formalism.MainNotions.StandardLatticesGL3.AE D)))) M hM
  refine ⟨n, hn, fun z' hz' => ?_⟩
  obtain ⟨s, hs, e⟩ := h (z'.map (Formalism.MainNotions.StandardLatticesGL3.inc D)) fun i j => by
    obtain ⟨t, ht, et⟩ := hz' i j
    exact ⟨t, ht, by rw [← et, Matrix.sub_apply]⟩
  rw [sq_unitary] at e
  have hinc : ∀ w : Matrix (Fin d) (Fin a) D.host.E, (∑ i, ∑ j, w.map (Formalism.MainNotions.StandardLatticesGL3.inc D) i j * Formalism.MainNotions.StandardLatticesGL3.sgA D (w.map (Formalism.MainNotions.StandardLatticesGL3.inc D) i j)) = Formalism.MainNotions.StandardLatticesGL3.inc D (∑ i, ∑ j, w i j * D.host.conj (w i j)) := fun w => by
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [Matrix.map_apply, map_sum, map_mul]
    rfl
  rw [hinc, hinc, ← map_sub] at e
  have hM0 : (M : D.host.E) ≠ 0 := Nat.cast_ne_zero.2 hM.ne'
  rw [← GlobalTheory.HeckeVal.inc_mem_iff]
  have e2 : Formalism.MainNotions.StandardLatticesGL3.inc D (((∑ i, ∑ j, z' i j * D.host.conj (z' i j)) - ∑ i, ∑ j, z i j * D.host.conj (z i j)) / (M : D.host.E)) = Formalism.MainNotions.StandardLatticesGL3.inc D (M : D.host.E)⁻¹ * (M : Formalism.MainNotions.StandardLatticesGL3.AE D) * s := by
    rw [div_eq_inv_mul, map_mul, e, mul_assoc]
  have e3 : Formalism.MainNotions.StandardLatticesGL3.inc D (M : D.host.E)⁻¹ * (M : Formalism.MainNotions.StandardLatticesGL3.AE D) = 1 := by
    rw [← map_natCast (Formalism.MainNotions.StandardLatticesGL3.inc D), ← map_mul, inv_mul_cancel₀ hM0, map_one]
  rw [e2, e3, one_mul]
  exact hs

theorem qH_pt {D : D7} {cc : Ideal (𝓞 D.host.K)} {δ : ℂ} (hC : Formalism.MainNotions.StandardLatticesGL3.Crv D cc δ) {a d : ℕ}
    (z : Matrix (Fin d) (Fin a) D.host.E) :
    Formalism.MainNotions.TaylorLogMetric.qH D (tor0 D cc δ) (pt D (tor0 D cc δ) δ z) =
      (∑ τ, embT D τ (∑ i, ∑ j, z i j * D.host.conj (z i j))).re / (Ideal.absNorm cc : ℝ) := by
  have hδ : δ ≠ 0 := GlobalTheory.NormExact.delta_ne_zero hC
  have hN : (0 : ℝ) < Ideal.absNorm cc := by
    exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.2 hC.1.1)
  have hd : (0 : ℝ) < √(D.host.d : ℝ) := Real.sqrt_pos.2 (by exact_mod_cast D.host.hyp.2.1.pos)
  have hc : ∀ τ x, embT D τ (D.host.conj x) = starRingEnd ℂ (embT D τ x) := fun τ x =>
    D.host.conjE_apply (embT D τ) x
  have hpt : ∀ τ i j, pt D (tor0 D cc δ) δ z τ i j = δ * embT D τ (z i j) := fun τ i j => rfl
  have hS : ∑ τ, embT D τ (∑ i, ∑ j, z i j * D.host.conj (z i j)) =
      ∑ τ, ∑ i, ∑ j, embT D τ (z i j) * starRingEnd ℂ (embT D τ (z i j)) := by
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [map_sum, map_mul, hc]
  have hH : Hf D (tor0 D cc δ) (pt D (tor0 D cc δ) δ z) (pt D (tor0 D cc δ) δ z) =
      ((Complex.normSq δ : ℝ) : ℂ) * (∑ τ, embT D τ (∑ i, ∑ j, z i j * D.host.conj (z i j))) /
        ((area (lamOf D cc δ) : ℝ) : ℂ) := by
    rw [hS, Hf]
    simp only [hpt, map_mul, Finset.mul_sum]
    congr 1
    refine Finset.sum_congr rfl fun τ _ => Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    rw [Complex.normSq_eq_conj_mul_self]
    ring
  rw [Formalism.MainNotions.TaylorLogMetric.qH, hH, GlobalTheory.MomDict.area_lamOf D cc δ hC.1.1]
  have hδ2 : 0 < Complex.normSq δ := Complex.normSq_pos.2 hδ
  rw [show ((Complex.normSq δ * (Ideal.absNorm cc : ℝ) * √(D.host.d : ℝ) / 2 : ℝ) : ℂ) =
    ((Complex.normSq δ * (Ideal.absNorm cc : ℝ) * √(D.host.d : ℝ) / 2 : ℝ) : ℂ) from rfl,
    mul_div_assoc, Complex.re_ofReal_mul, Complex.div_ofReal_re]
  field_simp

theorem phase_eq : ∀ {D : D7} (cc : Ideal (𝓞 D.host.K)) (δ : ℂ), Formalism.MainNotions.StandardLatticesGL3.Crv D cc δ →
  ∀ {a d : ℕ} (x : Formalism.MainNotions.StandardLatticesGL3.GA D a) (y : Formalism.MainNotions.StandardLatticesGL3.GA D d) (z : Matrix (Fin d) (Fin a) D.host.E),
  ∃ n : ℕ, 0 < n ∧ ∀ z', Formalism.MainNotions.StandardLatticesGL3.CloseTo D cc n (x : GL (Fin a) (Formalism.MainNotions.StandardLatticesGL3.AE D)) (y : GL (Fin d) (Formalism.MainNotions.StandardLatticesGL3.AE D)) z z' →
    Formalism.MainNotions.StandardLatticesGL3.wdPh D (tor0 D cc δ) (pt D (tor0 D cc δ) δ z') = Formalism.MainNotions.StandardLatticesGL3.wdPh D (tor0 D cc δ) (pt D (tor0 D cc δ) δ z) := by
  intro D cc δ hC a d x y z
  have hN : 0 < Ideal.absNorm cc := Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.2 hC.1.1)
  obtain ⟨n, hn, h⟩ := sq_diff_int cc x y z (8 * Ideal.absNorm cc) (by positivity)
  refine ⟨n, hn, fun z' hz' => ?_⟩
  obtain ⟨m, hm⟩ := trace_sum_int D _ (h z' hz')
  set S' := ∑ i, ∑ j, z' i j * D.host.conj (z' i j)
  set S := ∑ i, ∑ j, z i j * D.host.conj (z i j)
  have h8 : ((8 * Ideal.absNorm cc : ℕ) : D.host.E) ≠ 0 := Nat.cast_ne_zero.2 (by positivity)
  have hsplit : S' = S + ((8 * Ideal.absNorm cc : ℕ) : D.host.E) * ((S' - S) / ((8 * Ideal.absNorm cc : ℕ) : D.host.E)) := by
    field_simp; ring
  have key : (∑ τ, embT D τ S').re = (∑ τ, embT D τ S).re + 4 * (Ideal.absNorm cc : ℝ) * m := by
    rw [hsplit]
    simp only [map_add (f := _), map_mul, map_natCast, Finset.sum_add_distrib, ← Finset.mul_sum, Complex.add_re]
    have e : ((8 * Ideal.absNorm cc : ℕ) : ℂ) = (((8 * Ideal.absNorm cc : ℕ) : ℝ) : ℂ) := rfl
    rw [e, Complex.re_ofReal_mul]
    push_cast at hm ⊢
    rw [← hm]; ring
  have hN' : (0 : ℝ) < Ideal.absNorm cc := by exact_mod_cast hN
  have harg : (∑ τ, embT D τ S').re / (Ideal.absNorm cc : ℝ) / 2 =
      (∑ τ, embT D τ S).re / (Ideal.absNorm cc : ℝ) / 2 + 2 * m := by
    rw [key]; field_simp; ring
  rw [Formalism.MainNotions.StandardLatticesGL3.wdPh, Formalism.MainNotions.StandardLatticesGL3.wdPh, qH_pt hC z', qH_pt hC z, harg]
  unfold Formalism.MainNotions.StandardLatticesGL3.ee
  rw [Complex.exp_eq_exp_iff_exists_int]
  refine ⟨2 * m, ?_⟩
  push_cast
  ring

end GlobalTheory.PhaseMove
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLocalDictionaryInertPlaceStatement
section
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped TensorProduct Matrix

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_local_dictionary_inertPlace : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    (n r s : ℕ) (X : Spc F E n), B.IsGood σ → X.IsHerm σ B r s →
    ∀ (v : Pl (F := F)) (w : HeightOneSpectrum (𝓞 E)), Formalism.UG.IsInertAt F E v w →
    ∃ (O : Type) (_ : CommRing O) (c : O →+* O) (ι : O →ₙ+* _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)) (P Q : Matrix (Fin n) (Fin n) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)))
      (JL : Matrix (Fin n) (Fin n) O),
      IsLocalRing O ∧ (∀ x, c (c x) = x) ∧ IsUnit (2 : O) ∧ (∃ x : O, IsUnit (c x - x)) ∧
      Function.Injective ι ∧ At (evFin F v) (ι 1) ∧ (∀ y : _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E), At (evFin F v) y → ι 1 * y = y) ∧
      (∀ x, cA σ (ι x) = ι (c x)) ∧
      P * Q = ι 1 • (1 : Matrix (Fin n) (Fin n) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))) ∧ Q * P = ι 1 • (1 : Matrix (Fin n) (Fin n) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))) ∧
      ι 1 • P = P ∧ ι 1 • Q = Q ∧
      (∀ i j, c (JL j i) = JL i j) ∧ IsUnit JL.det ∧ Pᵀ * incM F X.J * P.map (cA σ) = JL.map ι ∧
      ∀ z : Fin n → _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E), z ∈ GlobalTheory.InertSph.latAt X v ↔ ∃ a : Fin n → O, z = P *ᵥ fun i => ι (a i) := by
  first | exact @GlobalTheory.InertLocDict.exists_local_dictionary | exact GlobalTheory.InertLocDict.exists_local_dictionary | (intros; apply GlobalTheory.InertLocDict.exists_local_dictionary <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLocalSchroedingerFamilyAtPlaceStatement
section
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped TensorProduct Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_local_schroedinger_family_at_place : ∀ (F : Type) [Field F] [NumberField F] (v : Pl (F := F)) (ψ : AddChar (AF F) ℂ), IsStd ψ → PsiUnr ψ v →
    ∀ {Wm : Type} [AddCommGroup Wm] [Module (AF F) Wm] {Bf : Wm → Wm → AF F} {κ : Type} [Fintype κ] (co : Darboux Bf κ)
      (Y : Type) [AddCommGroup Y] (Xm : Y →+ Wm) (χ : Y → Y → ℂ),
      (∀ z : Wm, At (evFin F v) z ↔ ∃ y, Xm y = z) → (∀ x y, ψ (⅟(2 : AF F) * Bf (Xm x) (Xm y)) = χ x y) →
      ∃ ρ : Y → Module.End ℂ (SB (κ → Fv F v)), ρ 0 = 1 ∧ (∀ x y, ρ x * ρ y = χ x y • ρ (x + y)) ∧
        (∀ x (φ : SB (κ → Fv F v)), Acts (evFin F v) (co.rho ψ (Xm x)) (φ : (κ → Fv F v) → ℂ)
          ((ρ x φ : SB (κ → Fv F v)) : (κ → Fv F v) → ℂ)) ∧
        ∀ s : SB (κ → Fv F v), s ≠ 0 → Submodule.span ℂ (Set.range fun x => ρ x s) = ⊤ := by
  first | exact @GlobalTheory.SchrLocModel.exists_locRho | exact GlobalTheory.SchrLocModel.exists_locRho | (intros; apply GlobalTheory.SchrLocModel.exists_locRho <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsNormalisedDataAllTuplesOfBaseTuple
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.PinnedTuples

theorem exists_pins_of_base : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T0 : Type) (A : FamIn D.what₂.LL G Pl0 T0 D.R.m) (T : CoreJ D) [Algebra T.Q.c.F D.what₂.LL] (R : RealDat D A T.Q.c.F) (κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)) (v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec) (O : ∀ i, OMDat T.toCore R i Unit (fun _ => A.μ0)) , R.toLevCh.Is A.μ0 → R.grp_chiW → R.IsFam → R.IsModels → R.thP_vP → R.tup_mu_off → R.tup_mu_used → Nonempty (FWTie T R κ v₀) → ∀ i : Fin D.R.m, OMPins T R κ v₀ O i → QGuard R → ∃ O' : OMDat T.toCore R i T0 id, D.what₂.embLL.toRatAlgHom.fieldRange ≤ O'.c'.F ∧ O'.Pins (κ i) (v₀ i (sg0 D A)) (iotaW T i) (T.x₀ ((i : ℕ) + 1) O'.s0) ∧ O'.lev = (O i).lev := by
  intro D G _ _ Pl0 T0 A T _ R κ v₀ O hL hχ hF hM hθ h1 h2 hfw i hO hG
  obtain ⟨fw⟩ := hfw
  obtain ⟨hpb, hV, hlev⟩ := _root_.GlobalTheory.BasePins.orient_std_lev D G Pl0 T0 A T R κ v₀ O hL fw.laws i hO
  obtain ⟨gramR, c0R, c0L, htie⟩ := hF.tie
  obtain ⟨O', a, b, c, -⟩ := _root_.GlobalTheory.PinnedDataGiven.exists_pins_given D G Pl0 T0 A T R κ v₀ hL hχ hF hM hθ ⟨fw⟩ hpb
    (GlobalTheory.TupleCover.finite_tuples R h1 h2) hG i hV (O i).lev hlev gramR c0R c0L htie
  exact ⟨O', a, b, c⟩

end GlobalTheory.PinnedTuples
end

