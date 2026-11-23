module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0745
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0026
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.RingSpecNormalisedCharacterEq
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0616
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HasSupportOfIsSubquotientProdIrr
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0670
public import Formalism.LocalToGlobal.GaloisLevelStructure.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ThetaFunctionLocalGenerationInertPlaceOffLevel
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0654
public import Formalism.SharpRestriction.LevelLetterCocycles.Bundle0006
public import Formalism.SharpRestriction.LevelLetterCocycles.Bundle0015
public import Formalism.SharpRestriction.LevelLetterCocycles.CrystallineLiftingInputs
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0747
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0638
public import Formalism.SharpRestriction.LevelLetterCocycles.QuotientImageDivisibility.IsAdicCompleteOfLe
public import Formalism.SharpRestriction.LevelLetterCocycles.QuotientImageDivisibility.Bundle0009
public import Formalism.SharpRestriction.LevelLetterCocycles.QuotientImageDivisibility.Bundle0007
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0424

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SplitPlaceUnderFixedSplitPlace
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host NumberField IsDedekindDomain
open ValuativeRel Matrix GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.RecT GlobalTheory.HeightCounting
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.PlaceUnderFixed

theorem exists_splitPlace_under_plGw : ∀ (D : D7) (s : SplitPlace D.host.E), s.v ∈ gPl D → ∃ (k : Fin 2) (v : D.nd.PlG k) (s₀ : SplitPlace D.host.E), s₀.w = D.naut.plGw k v ∧ s₀.v = s.v := by
  intro D s hs
  obtain ⟨k, u, s₀, hv, hw⟩ := GlobalTheory.FormInner.exists_split_of_gPl D s.v hs
  exact ⟨k, u, s₀, hw, hv⟩

end GlobalTheory.PlaceUnderFixed
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ThetaFunctionLocalGenerationInertPlaceOffLevelStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef
open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.IndefR.Links
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.DownLift
open GlobalTheory.DownLift.GenFinite
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.thetaFunction_local_generation_inertPlace_offLevel : GlobalTheory.Hk3.HoweUnram → ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T : Type) (A : FamIn D.what₂.LL G Pl0 T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), GlobalTheory.LiftRows.Given R F → R.FullP → ∀ (i : Fin D.R.m) (t : T) (Sb : Finset (HeightOneSpectrum (𝓞 D.host.F))) (v : HeightOneSpectrum (𝓞 D.host.F)), v ∈ Sb → (∀ ε, IsPlaceIdem D v ε → ∀ e, IsSplitIdem D e → e * algebraMap (AF D.host.F) (AE D) ε = 0) → (∀ PP, PP ∈ R.Pg ∨ PP ∈ R.Q t → ¬ GlobalTheory.DownLift.GenFinite.Over PP v) → ∀ (f : WO (Vc D i) (Wc D i) → ℂ), GlobalTheory.DownLift.GenFinite.TypeIn R i t Sb f → GlobalTheory.DownLift.GenFinite.CleanIn R i t Sb f → GlobalTheory.DownLift.GenFinite.LikeOff R i t Sb f → f ∈ Submodule.span ℂ (GlobalTheory.DownLift.GenFinite.StepGen R i t (GlobalTheory.DownLift.GenFinite.dropPl Sb v)) := by
  first | exact @GlobalTheory.DownLift.GenFinite.Inert.step_inert | exact GlobalTheory.DownLift.GenFinite.Inert.step_inert | (intros; apply GlobalTheory.DownLift.GenFinite.Inert.step_inert <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.WachOperatorProductShiftMemLattice
section
open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc

namespace GlobalTheory

set_option synthInstance.maxHeartbeats 100000 in
theorem wachShift_mem_of_N1used : ∀ (D : Formalism.BasicNotions.D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (Cm : CmpOf D.loc D.locA HW F), Formalism.MainNotions.DeltaInvariantLattices.DeltaInvariantNormBound D HW F Cm → ∀ (l : ℕ) [Fact l.Prime] (K LL : FinExt l) (hA : Loc.CaseA K LL), ∀ (T : LocLat ↥(GK K) ℚ_[l] ↥LL.1 ↥(OL LL)), IsCrys ((D.loc l).PD K) T.ρ → ∀ (i : ZMod (Module.finrank ℚ_[l] ↥(K0 K))) (y' Y : ℕ) (cO : ℤ → ↥(OL LL)), (∀ x : ℤ, ((l : ℕ) : ↥(OL LL)) * cO x = 1 - (((((HW l).W K 1 LL hA.2.2).χΓ ((HW l).W K 1 LL hA.2.2).gam) ^ (-x) : (↥(OL LL))ˣ) : ↥(OL LL))) → ∀ xs : List ℤ, (∀ (τ : ↥K.1 →ₐ[ℚ_[l]] ↥LL.1) (a : ℤ) (j : ℕ), Formalism.MainNotions.LiftingTheory.Over ((HW l).W K 1 LL hA.2.2) τ i → IsJumpV ((D.loc l).PD K) T.ρ τ a → y' < j → j ≤ Y → a + (j : ℤ) ∈ xs) → ∀ seq : ℕ → ((HW l).W K 1 LL hA.2.2).DD T, Formalism.MainNotions.CrystallineLiftingInputs.DL ((HW l).W K 1 LL hA.2.2) T i (seq 0) → Formalism.MainNotions.LiftingTheory.qp ((HW l).W K 1 LL hA.2.2) ^ Y • seq 0 ∈ ((HW l).W K 1 LL hA.2.2).N T → (∀ k < xs.length, ((HW l).W K 1 LL hA.2.2).π₀ • (seq (k + 1) + cO (xs.getD k 0) • seq k) = ((HW l).W K 1 LL hA.2.2).γD T ((HW l).W K 1 LL hA.2.2).gam (seq k) - seq k) → Formalism.MainNotions.CrystallineLiftingInputs.DL ((HW l).W K 1 LL hA.2.2) T i (seq xs.length) ∧ Formalism.MainNotions.LiftingTheory.qp ((HW l).W K 1 LL hA.2.2) ^ y' • seq xs.length ∈ ((HW l).W K 1 LL hA.2.2).N T := by
  intro D HW F Cm hN l _ K LL hA
  have h9 : Formalism.MainNotions.DeltaInvariantLattices.P9W ((HW l).W K 1 LL hA.2.2) := hN.2.2.2.2.2.2.2.2.1 l K 1 LL hA.2.2
  obtain ⟨hRg, hRu, hCr⟩ := _root_.GlobalTheory.ExpansionsOdd.main D HW F Cm hN l K LL hA
  have hD : Formalism.MainNotions.RamifiedCoefficientChains.DdREqDcris ((D.loc l).PD K) ↥LL.1 := fun hb V _ _ _ _ _ ρ hc =>
    GlobalTheory.Per.DdREqDcris.map_Dcris_eq_DdR l (D.loc l) (D.locA l) (D.locT l) K LL hb V ρ hc
  intro T hT i y' Y cO hc xs hxs seq h0 h0N hrec
  have hp : ((D.loc l).PD K).p = l := (D.loc l).PD_p K
  have : FiniteDimensional ℚ_[l] ↥(K0 K) := ((D.loc l).PD K).finK₀
  have : NeZero (Module.finrank ℚ_[l] ↥(K0 K)) := ⟨Module.finrank_pos.ne'⟩
  obtain ⟨ζ, hζ⟩ := Formalism.MainNotions.UnusedSlot80.exists_prim_of_good D hA.2.2
  have hCase := Formalism.MainNotions.UnusedSlot80.caseA_of_le_Kur_of_ne_two
    (D.loc l) (HW l) hA.2.2 hA.1 hA.2.1
  have hpne : (((D.loc l).PD K).p : ↥LL.1) ≠ 0 := by
    rw [hp]
    exact Nat.cast_ne_zero.2 (Fact.out : l.Prime).ne_zero
  exact wachShift_mem_of_exp _ h9 hRg hRu hCr hD hCase hpne ζ (by rw [hp]; exact hζ)
    T hT i y' Y cO (fun x => by rw [hp]; exact hc x) xs hxs seq h0 h0N hrec

end GlobalTheory
end

