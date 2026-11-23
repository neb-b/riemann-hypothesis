module

public import Mathlib
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeilRepresentationPreservesSchwartz
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1674
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0484
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0432
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0041
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0015
public import Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.ThetaIntegralsAgree
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.Bundle0069
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0003
public import Development.AbelianVarietyTheory.BlockTheory.HeightDefect.Bundle0005
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.Bundle0067
public import Formalism.LocalToGlobal.IndefiniteReal.Bundle0020
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0440
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0459
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsSmoothAutomorphicFunctionTranslateAtRealPlace
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0316
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0184
public import Development.AbelianVarietyTheory.Counterexamples.HeightSurvey.Bundle0003
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0161
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0215
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0224
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0470
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0476
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0482
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0295
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0129
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0123

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.HeisenbergCommutingOperatorIndependentOfArchimedeanFiber
section
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

noncomputable section

namespace GlobalTheory.FinFibre

variable {F : Type} [Field F] [NumberField F] {κ : Type} [Fintype κ]

def fin (x : κ → AF F) : κ → Af F := fun i => (x i).2

def mkv (a : κ → Ainf F) (w : κ → Af F) : κ → AF F := fun i => (a i, w i)

def chi (ψ : AddChar (AF F) ℂ) (q : κ → Af F) (w : κ → Af F) : ℂ := GlobalTheory.HeisSchA.finChar ψ (w ⬝ᵥ q)


variable (κ) in
def alg (ψ : AddChar (AF F) ℂ) : Submodule ℂ ((κ → Af F) → ℂ) := Submodule.span ℂ (Set.range (chi (κ := κ) ψ))

theorem chi_zero (ψ : AddChar (AF F) ℂ) : chi (κ := κ) ψ 0 = 1 := by
  funext w; simp [chi]

theorem chi_add (ψ : AddChar (AF F) ℂ) (q q' : κ → Af F) : chi (κ := κ) ψ (q + q') = chi ψ q * chi ψ q' := by
  funext w; simp [chi, dotProduct_add, AddChar.map_add_eq_mul]

theorem one_mem (ψ : AddChar (AF F) ℂ) : (1 : (κ → Af F) → ℂ) ∈ alg κ ψ :=
  chi_zero (κ := κ) ψ ▸ Submodule.subset_span ⟨0, rfl⟩

theorem mul_mem (ψ : AddChar (AF F) ℂ) {C D : (κ → Af F) → ℂ} (hC : C ∈ alg κ ψ) (hD : D ∈ alg κ ψ) :
    C * D ∈ alg κ ψ := by
  have h := Submodule.mul_mem_mul hC hD
  rw [alg, Submodule.span_mul_span] at h
  refine Submodule.span_mono ?_ h
  rintro _ ⟨_, ⟨q, rfl⟩, _, ⟨q', rfl⟩, rfl⟩
  exact ⟨q + q', chi_add ψ q q'⟩

end GlobalTheory.FinFibre

namespace GlobalTheory.FinFibre
variable {F : Type} [Field F] [NumberField F] {κ : Type} [Fintype κ]

theorem exists_ne_one (ψ : AddChar (AF F) ℂ) (hψ : ∀ w : Pl (F := F), ∃ t, GlobalTheory.LatVac.psiAt ψ w t ≠ 1) {a : Af F}
    (ha : a ≠ 0) : ∃ b : Af F, GlobalTheory.HeisSchA.finChar ψ (a * b) ≠ 1 := by
  classical
  obtain ⟨v, hv⟩ : ∃ v, evalV F v a ≠ 0 := by
    by_contra h
    push_neg at h
    exact ha (af_ext fun u => by rw [h u, map_zero])
  obtain ⟨t, ht⟩ := hψ v
  refine ⟨singleFin v (t / evalV F v a), ?_⟩
  have e : a * singleFin v (t / evalV F v a) = singleFin v t := by
    apply af_ext
    intro u
    rw [map_mul]
    by_cases hu : u = v
    · subst hu
      rw [evalV_singleFin_self, evalV_singleFin_self]
      field_simp
    · rw [evalV_singleFin_ne hu, evalV_singleFin_ne hu, mul_zero]
  rw [e]
  exact ht

theorem exists_chi_ne_one (ψ : AddChar (AF F) ℂ) (hψ : ∀ w : Pl (F := F), ∃ t, GlobalTheory.LatVac.psiAt ψ w t ≠ 1) {d : κ → Af F}
    (hd : d ≠ 0) : ∃ q : κ → Af F, chi ψ q d ≠ 1 := by
  classical
  obtain ⟨i, hi⟩ := Function.ne_iff.mp hd
  obtain ⟨b, hb⟩ := exists_ne_one ψ hψ hi
  exact ⟨Pi.single i b, by rw [chi, dotProduct_single]; exact hb⟩

theorem chi_mul_eq_schr (ψ : AddChar (AF F) ℂ) (q : κ → Af F) (Φ : (κ → AF F) → ℂ) :
    (fun x => chi ψ q (fin x) * Φ x) =
      schr ψ ((GlobalTheory.HeisSchA.mk 0 1 : AF F) • (0 : κ → AF F),
        (GlobalTheory.HeisSchA.mk 0 1 : AF F) • fun i => GlobalTheory.HeisSchA.mk 0 (q i)) Φ := by
  funext x
  simp only [schr, smul_zero, zero_dotProduct, mul_zero, add_zero]
  congr 1
  rw [chi, GlobalTheory.HeisSchA.finChar_apply]
  congr 1
  symm
  refine Prod.ext ?_ ?_
  · change GlobalTheory.HeisSchA.p1 (x ⬝ᵥ _) = 0
    rw [RingHom.map_dotProduct]
    refine Finset.sum_eq_zero fun i _ => ?_
    change GlobalTheory.HeisSchA.p1 (x i) * (0 * 0) = 0
    simp
  · change GlobalTheory.HeisSchA.p2 (x ⬝ᵥ _) = _
    rw [RingHom.map_dotProduct]
    refine Finset.sum_congr rfl fun i _ => ?_
    change (x i).2 * (1 * q i) = (x i).2 * q i
    rw [one_mul]

end GlobalTheory.FinFibre

namespace GlobalTheory.FinFibre
variable {F : Type} [Field F] [NumberField F] {κ : Type} [Fintype κ]

theorem comm_alg (ψ : AddChar (AF F) ℂ) (T : Module.End ℂ ((κ → AF F) → ℂ))
    (hT : ∀ u : AF F, evI F u = 0 → ∀ p q : κ → AF F, ∀ Φ ∈ schA F κ,
      T (schr ψ (u • p, u • q) Φ) = schr ψ (u • p, u • q) (T Φ))
    {C : (κ → Af F) → ℂ} (hC : C ∈ alg κ ψ) {Φ : (κ → AF F) → ℂ} (hΦ : Φ ∈ schA F κ) :
    T (fun x => C (fin x) * Φ x) = fun x => C (fin x) * T Φ x := by
  induction hC using Submodule.span_induction with
  | mem C h =>
    obtain ⟨q, rfl⟩ := h
    have h0 : evI F (GlobalTheory.HeisSchA.mk 0 1 : AF F) = 0 := by
      change InfiniteAdeleRing.ringEquiv_mixedSpace F 0 = 0
      exact map_zero _
    rw [chi_mul_eq_schr, chi_mul_eq_schr]
    exact hT _ h0 _ _ Φ hΦ
  | zero =>
    have e : (fun x : κ → AF F => (0 : (κ → Af F) → ℂ) (fin x) * T Φ x) = 0 := by funext x; simp
    have e' : (fun x : κ → AF F => (0 : (κ → Af F) → ℂ) (fin x) * Φ x) = 0 := by funext x; simp
    rw [e, e', map_zero]
  | add C D _ _ hC hD =>
    have e : (fun x : κ → AF F => (C + D) (fin x) * Φ x) =
        (fun x => C (fin x) * Φ x) + fun x => D (fin x) * Φ x := by funext x; simp [add_mul]
    rw [e, map_add (f := _), hC, hD]
    funext x; simp [add_mul]
  | smul a C _ hC =>
    have e : (fun x : κ → AF F => (a • C) (fin x) * Φ x) = a • fun x => C (fin x) * Φ x := by
      funext x; simp [mul_assoc]
    rw [e, map_smul, hC]
    funext x; simp [mul_assoc]

theorem exists_sep (ψ : AddChar (AF F) ℂ) (hc : Continuous ψ)
    (hψ : ∀ w : Pl (F := F), ∃ t, GlobalTheory.LatVac.psiAt ψ w t ≠ 1) (y₀ : κ → Af F) {S : Set (κ → Af F)} (hS : IsCompact S)
    (hy : y₀ ∉ S) : ∃ C ∈ alg κ ψ, C y₀ = 1 ∧ ∀ w ∈ S, C w = 0 := by
  have hlc := GlobalTheory.HeisSchA.finChar_isLocallyConstant ψ hc
  refine hS.induction_on (p := fun t => ∃ C ∈ alg κ ψ, C y₀ = 1 ∧ ∀ w ∈ t, C w = 0) ?_ ?_ ?_ ?_
  · exact ⟨1, one_mem ψ, rfl, fun _ h => h.elim⟩
  · rintro s t hst ⟨C, hC, h1, h0⟩
    exact ⟨C, hC, h1, fun w hw => h0 w (hst hw)⟩
  · rintro s t ⟨C, hC, h1, h0⟩ ⟨D, hD, h1', h0'⟩
    refine ⟨C * D, mul_mem ψ hC hD, by simp [h1, h1'], ?_⟩
    rintro w (hw | hw)
    · simp [h0 w hw]
    · simp [h0' w hw]
  · intro w hw
    have hne : w - y₀ ≠ 0 := sub_ne_zero.mpr fun h => hy (h ▸ hw)
    obtain ⟨q, hq⟩ := exists_chi_ne_one ψ hψ hne
    set ζ := chi ψ q (w - y₀)
    have hζ : 1 - ζ ≠ 0 := sub_ne_zero.mpr (Ne.symm hq)
    let C : (κ → Af F) → ℂ := (1 - ζ)⁻¹ • (GlobalTheory.HeisSchA.finChar ψ (-(y₀ ⬝ᵥ q)) • chi ψ q - ζ • chi ψ 0)
    have hCv : ∀ w', C w' = (1 - ζ)⁻¹ * (chi ψ q (w' - y₀) - ζ) := by
      intro w'
      simp only [C, chi_zero, Pi.smul_apply, Pi.sub_apply, Pi.one_apply, smul_eq_mul, mul_one]
      congr 2
      rw [chi, chi, sub_dotProduct, sub_eq_neg_add, AddChar.map_add_eq_mul]
    have hCm : C ∈ alg κ ψ := Submodule.smul_mem _ _ (Submodule.sub_mem _
      (Submodule.smul_mem _ _ (Submodule.subset_span ⟨q, rfl⟩)) (Submodule.smul_mem _ _ (Submodule.subset_span ⟨0, rfl⟩)))
    have hcont : Continuous fun w' : κ → Af F => (w' - y₀) ⬝ᵥ q :=
      (continuous_id.sub continuous_const).dotProduct continuous_const
    have hev := (IsLocallyConstant.iff_eventually_eq _).mp (hlc.comp_continuous hcont) w
    refine ⟨{w' | chi ψ q (w' - y₀) = ζ}, mem_nhdsWithin_of_mem_nhds hev, C, hCm, ?_, ?_⟩
    · rw [hCv, sub_self]
      have h1 : chi ψ q 0 = 1 := by simp [chi]
      rw [h1]
      exact inv_mul_cancel₀ hζ
    · intro w' hw'
      rw [hCv, show chi ψ q (w' - y₀) = ζ from hw', sub_self, mul_zero]

end GlobalTheory.FinFibre

namespace GlobalTheory.FinFibre
variable {F : Type} [Field F] [NumberField F] {κ : Type} [Fintype κ]

theorem schA_struct {Φ : (κ → AF F) → ℂ} (hΦ : Φ ∈ schA F κ) :
    (∃ K : Set (κ → Af F), IsCompact K ∧ ∀ x, fin x ∉ K → Φ x = 0) ∧
      ∀ w₀ : κ → Af F, ∀ᶠ w in nhds w₀, ∀ a : κ → Ainf F, Φ (mkv a w) = Φ (mkv a w₀) := by
  induction hΦ using Submodule.span_induction with
  | mem Φ h =>
    obtain ⟨f, g, hg, rfl⟩ := h
    refine ⟨⟨tsupport g, hg.2, fun x hx => ?_⟩, fun w₀ => ?_⟩
    · change _ * g (fin x) = 0
      rw [image_eq_zero_of_notMem_tsupport hx, mul_zero]
    · filter_upwards [(IsLocallyConstant.iff_eventually_eq _).mp hg.1 w₀] with w hw a
      change _ * g w = _ * g w₀
      rw [hw]
      rfl
  | zero => exact ⟨⟨∅, isCompact_empty, fun _ _ => rfl⟩, fun _ => Filter.Eventually.of_forall fun _ _ => rfl⟩
  | add Φ Ψ _ _ hΦ hΨ =>
    obtain ⟨⟨K, hK, h0⟩, h1⟩ := hΦ
    obtain ⟨⟨K', hK', h0'⟩, h1'⟩ := hΨ
    refine ⟨⟨K ∪ K', hK.union hK', fun x hx => ?_⟩, fun w₀ => ?_⟩
    · simp only [Set.mem_union, not_or] at hx
      simp [h0 x hx.1, h0' x hx.2]
    · filter_upwards [h1 w₀, h1' w₀] with w hw hw' a
      simp [hw a, hw' a]
  | smul c Φ _ hΦ =>
    obtain ⟨⟨K, hK, h0⟩, h1⟩ := hΦ
    refine ⟨⟨K, hK, fun x hx => by simp [h0 x hx]⟩, fun w₀ => ?_⟩
    filter_upwards [h1 w₀] with w hw a
    simp [hw a]

theorem main (ψ : AddChar (AF F) ℂ) (T : Module.End ℂ ((κ → AF F) → ℂ)) (hψ : IsStd ψ)
    (hnd : ∀ w : Pl (F := F), ∃ t, GlobalTheory.LatVac.psiAt ψ w t ≠ 1)
    (hT : ∀ u : AF F, evI F u = 0 → ∀ p q : κ → AF F, ∀ Φ ∈ schA F κ,
      T (schr ψ (u • p, u • q) Φ) = schr ψ (u • p, u • q) (T Φ))
    (Φ : (κ → AF F) → ℂ) (hΦ : Φ ∈ schA F κ) (y : κ → AF F) (hy : ∀ z, At (evI F) z → Φ (y + z) = 0) :
    T Φ y = 0 := by
  obtain ⟨⟨K, hK, h0⟩, h1⟩ := schA_struct hΦ
  set U := {w : κ → Af F | ∀ a : κ → Ainf F, Φ (mkv a w) = Φ (mkv a (fin y))}
  have hU : U ∈ nhds (fin y) := h1 (fin y)
  obtain ⟨C, hC, hC1, hC0⟩ := exists_sep ψ hψ.1 hnd (fin y) (hK.diff isOpen_interior)
    (fun h => h.2 (mem_interior_iff_mem_nhds.mpr hU))
  have hzero : (fun x => C (fin x) * Φ x) = 0 := by
    funext x
    by_cases hxK : fin x ∈ K
    · by_cases hxU : fin x ∈ interior U
      · have hx := interior_subset hxU (fun i => (x i).1)
        have e1 : mkv (fun i => (x i).1) (fin x) = x := rfl
        rw [e1] at hx
        have e2 : mkv (fun i => (x i).1) (fin y) = y + fun i => GlobalTheory.HeisSchA.mk ((x i).1 - (y i).1) 0 := by
          funext i
          refine Prod.ext ?_ ?_
          · change (x i).1 = (y i).1 + ((x i).1 - (y i).1)
            abel
          · change (y i).2 = (y i).2 + 0
            rw [add_zero]
        rw [hx, e2, hy _ (fun u hu => funext fun i => GlobalTheory.HeisSchA.at_mk _ u hu)]
        simp
      · simp [hC0 _ ⟨hxK, hxU⟩]
    · simp [h0 x hxK]
  have h := congrFun (comm_alg ψ T hT hC hΦ) y
  rw [hzero, map_zero, hC1, one_mul] at h
  exact h.symm

end GlobalTheory.FinFibre


open GlobalTheory.FinFibre in
theorem GlobalTheory.FinFibre.fibre_zero : ∀ {F : Type} [Field F] [NumberField F] {κ : Type} [Fintype κ] (ψ : AddChar (AF F) ℂ) (T : Module.End ℂ ((κ → AF F) → ℂ)),
    IsStd ψ → (∀ Φ ∈ schA F κ, T Φ ∈ schA F κ) →
    (∀ u : AF F, evI F u = 0 → ∀ p q : κ → AF F, ∀ Φ ∈ schA F κ, T (schr ψ (u • p, u • q) Φ) = schr ψ (u • p, u • q) (T Φ)) →
    ∀ Φ ∈ schA F κ, ∀ y : κ → AF F, (∀ z, At (evI F) z → Φ (y + z) = 0) → T Φ y = 0 :=
  fun ψ T hψ _ hT Φ hΦ y hy => main ψ T hψ (GlobalTheory.T.standardAdelicAddChar_nontrivial_finitePlace ψ hψ) hT Φ hΦ y hy
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsGKSubmoduleISupGelfandJointEigenspacesStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim GlobalTheory.FlipRun
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
open scoped TensorProduct
open Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isGKSubmodule_iSup_gelfandJointEigenspaces : ∀ {D : D7} (θ : D.what₂.Tau → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)) (V : HSp D) (S : D.what₂.Tau → SPar)
    (M : Formalism.IndefR.Mult.DSModel V S), IsInfFam (D := D) θ → ∀ ψ : GA D V → ℂ, IsAutFunSm θ V ψ →
    ∀ C : Finset (D.what₂.Tau × ℕ → ℂ), GlobalTheory.CuspGK.IsGKSub θ M (⨆ c ∈ C, Submodule.span ℂ
      {h | h ∈ GlobalTheory.CuspGK.gkGen θ M ψ ∧ ∀ i : D.what₂.Tau × ℕ, gelf θ V i.1 i.2 h = c i • h}) := by
  first | exact @GlobalTheory.GKEigen.isGKSub_iSup_eigen | exact GlobalTheory.GKEigen.isGKSub_iSup_eigen | (intros; apply GlobalTheory.GKEigen.isGKSub_iSup_eigen <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsNonzeroFockVacuumConjUnitVacuumNegSpace
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.ChiGrid GlobalTheory.GridJoin
open scoped Pointwise TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Chain GlobalTheory.ChainFr GlobalTheory.Chain.RealIt GlobalTheory.PairLift

noncomputable section

namespace GlobalTheory.VacCjNeg

variable {D : D7}


open GlobalTheory.IndefiniteRowSideFullHecke.ConjugateAdjointDagger in
theorem dRho_cj {ψ : AddChar (AF D.host.F) ℂ} (hψ : IsStdChar D ψ (-1)) (S T : HSp D) (θ : InfFam D)
    (τ : D.what₂.Tau) (z : Matrix (Fin T.rank) (Fin S.rank) ℂ) (f : WO S T → ℂ) :
    dRho (heisO ψ S T) θ τ z (cj id f) = cj id (dRho (heisO ψ (GlobalTheory.Grid.neg S) T) θ τ z f) := by
  funext x
  show deriv (fun t : ℝ => heisO ψ S T (lineAt θ τ z t) (cj id f) x) 0 =
    starRingEnd ℂ (deriv (fun t : ℝ => heisO ψ (GlobalTheory.Grid.neg S) T (lineAt θ τ z t) f x) 0)
  have e : (fun t : ℝ => heisO ψ S T (lineAt θ τ z t) (cj id f) x) =
      fun t => star (heisO ψ (GlobalTheory.Grid.neg S) T (lineAt θ τ z t) f x) := by
    funext t
    rw [GlobalTheory.CjNeg.heis_negS' hψ]
    rfl
  rw [e, deriv.star]
  rfl

theorem isVacVec_cj_of_isVac_neg : ∀ {D : D7} (S T : GlobalTheory.Grid.Node D) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D)
    (f : WO S.V T.V → ℂ), GlobalTheory.Grid.IsVac ψ θ true S T f →
      GlobalTheory.Chain.IsVacVec ψ θ S.M T.M (GlobalTheory.IndefiniteRowSideFullHecke.ConjugateAdjointDagger.cj id f) := by
  intro D S T ψ θ f h
  obtain ⟨hψ, hv⟩ := h
  have hth : IsThetaFunO ψ (GlobalTheory.Grid.neg S.V) T.V f := hv.theta
  refine ⟨GlobalTheory.CjNeg.theta_negS' hψ (show IsThetaFunO ψ (GlobalTheory.ChiGrid.negSp S.V) T.V f from hth), ?_, fun τ => ?_⟩
  · intro h0
    have hf0 : f = 0 := by
      rw [← GlobalTheory.CjNeg.cj_id_cj_id f, h0]
      funext x
      simp [GlobalTheory.IndefiniteRowSideFullHecke.ConjugateAdjointDagger.cj]
    obtain ⟨⟨p, hp⟩, hall⟩ := hv.norm
    have h1 := hall p hp
    rw [hf0] at h1
    simp [nrm2] at h1
  · intro z
    have h0 : annih (heisO ψ (GlobalTheory.Grid.neg S.V) T.V) θ τ (cplxO (-(cart S.M τ)) (cart T.M τ)) z f = 0 :=
      hv.fock τ z
    have hJ : cplxO (-(cart S.M τ)) (cart T.M τ) z = -cplxO (cart S.M τ) (cart T.M τ) z := by
      simp [cplxO]
    unfold annih at h0 ⊢
    rw [hJ, GlobalTheory.FockAdjoint.dRho_neg' hψ hv.inf hth] at h0
    rw [dRho_cj hψ, dRho_cj hψ]
    funext x
    have h2 := congrFun h0 x
    simp only [Pi.add_apply, Pi.smul_apply, Pi.neg_apply, smul_eq_mul, Pi.zero_apply] at h2 ⊢
    simp only [GlobalTheory.IndefiniteRowSideFullHecke.ConjugateAdjointDagger.cj, id_eq]
    have e := congrArg (starRingEnd ℂ) h2
    simp only [map_add (f := _), map_mul, map_neg, Complex.conj_I, map_zero] at e
    linear_combination e

end GlobalTheory.VacCjNeg

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsSchrodingerThetaDatumAddAdelicSchwartzStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.Doubling GlobalTheory.ChainFr GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SquareComm GlobalTheory.SquareAgree
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isSchrodingerThetaDatum_add_adelicSchwartz : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {n d : ℕ}
    {Y : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc F E n} {Wd : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc F E d} (M : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Model σ Y Wd)
    (ψ : AddChar (AF F) ℂ), GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsStd ψ → ∀ {Z : Type} [AddCommGroup Z]
    (crd : Matrix (Fin n) (Fin d) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)) → Z) (Φ Φ' : (Fin n × Fin d → AF F) → ℂ) (f f' : Z → ℂ),
    IsDatum M ψ crd Φ f → IsDatum M ψ crd Φ' f' → IsDatum M ψ crd (Φ + Φ') (f + f') := by
  first | exact @GlobalTheory.SquareAgree.isDatum_add | exact GlobalTheory.SquareAgree.isDatum_add | (intros; apply GlobalTheory.SquareAgree.isDatum_add <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsWeilDatumComplexConjugateOfNegHermitianSpace
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.ChiGrid GlobalTheory.GridJoin
open scoped Pointwise TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Chain GlobalTheory.ChainFr GlobalTheory.Chain.RealIt GlobalTheory.PairLift
noncomputable section

namespace GlobalTheory.ConjWeilBack

open GlobalTheory.IndefiniteRowSideFullHecke.ConjugateAdjointDagger GlobalTheory.ChiGrid

variable {D : D7}

theorem key {S T : HSp D} (ω : GlobalTheory.Grid.WRep S T) (p : GA D S × GA D T) (F : WO S T → ℂ) :
    GlobalTheory.AdjTr.conjRep ω p F = cj id ((ω.toSgn true) ((ofSgn true S).symm p.1, p.2) (cj id F)) := rfl

theorem actO_negS' (S T : HSp D) (g : GA D (negSp S)) (h : GA D T) (w : WO S T) :
    actO (negSp S) T g h w = actO S T (ofSgn true S g) h w := by
  unfold actO; rfl

theorem ofSgn_symm_mem_GQ (S : HSp D) (γ : GA D S) (h : γ ∈ GQ S) : (ofSgn true S).symm γ ∈ GQ (negSp S) := by
  unfold GQ HFinIn HFin at *
  erw [Subgroup.mem_subgroupOf] at h ⊢
  convert h using 2 <;> first | rfl | exact (GlobalTheory.ConjWeil.UJ_neg _ _)


open GlobalTheory.ConjWeil in
theorem weil_conjRep_of_neg : ∀ {D : D7} (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (χS χT : (AE D)ˣ →* Circle)
    (ω : GlobalTheory.Grid.WRep S T), GlobalTheory.Grid.IsWeil ψ true S T χS χT ω → IsWeilDatumO ψ S T χS⁻¹ χT⁻¹ (GlobalTheory.AdjTr.conjRep ω) := by
  intro D ψ S T χS χT ω hw
  change IsWeilDatumO ψ (negSp S) T χS χT (ω.toSgn true) at hw
  have I := GlobalTheory.CjNeg.theta_heis_neg D ψ hw.std S T
  have thS : ∀ f : WO S T → ℂ, IsThetaFunO ψ S T f ↔ IsThetaFunO ψ (negSp S) T (cj id f) := fun f => (I.1 f).2.symm
  have hz2 : ∀ (w : WO S T) (X : WO S T → ℂ), heisO ψ S T w (cj id X) = cj id (heisO ψ (negSp S) T w X) := fun w X => by
    have := congrArg (cj id) (I.2 w (cj id X)).2
    rw [cj_id_cj_id, cj_id_cj_id] at this
    exact this.symm
  have hz1 : ∀ (w : WO S T) (f : WO S T → ℂ), heisO ψ (negSp S) T w (cj id f) = cj id (heisO ψ S T w f) :=
    fun w f => (I.2 w f).2
  refine
    { std := hw.std
      hecS := hecke_inv hw.hecS
      hecT := hecke_inv hw.hecT
      resS := resEta_inv hw.resS
      resT := resEta_inv hw.resT
      om_pres := ?_
      om_heis := ?_
      om_aut := ?_
      om_cont := ?_
      om_unit := ?_
      om_split := ?_ }
  · intro p f hf
    rw [key, thS, cj_id_cj_id]
    exact hw.om_pres _ _ ((thS f).1 hf)
  · intro g h w₀ f hf
    rw [key, key, ← hz1, hw.om_heis _ _ _ _ ((thS f).1 hf), hz2, actO_negS']
    rfl
  · intro γ hγ γ' hγ' f hf
    rw [key]
    show starRingEnd ℂ ((ω.toSgn true) ((ofSgn true S).symm γ, γ') (cj id f) 0) = f 0
    rw [hw.om_aut _ (ofSgn_symm_mem_GQ S γ hγ) γ' hγ' _ ((thS f).1 hf)]
    show starRingEnd ℂ (starRingEnd ℂ (f 0)) = f 0
    simp
  · intro f hf w
    have hc := hw.om_cont _ ((thS f).1 hf) w
    simp only [key]
    exact Complex.continuous_conj.comp
      (hc.comp (((continuous_ofSgn_symm true S).comp continuous_fst).prodMk continuous_snd))
  · intro μ 𝓕 hμ hF p f hf
    have hu := hw.om_unit μ 𝓕 hμ hF ((ofSgn true S).symm p.1, p.2) (cj id f) ((thS f).1 hf)
    simp only [key, cj_id_apply, enorm_conj] at hu ⊢
    exact hu
  · intro e he g h hg hh x y hx hy
    obtain ⟨r, hr, H⟩ := hw.om_split e he ((ofSgn true S).symm g) h
      (by unfold SuppAt; exact hg) hh x y (by unfold IsDetAt; exact hx) hy
    refine ⟨r, hr, fun ℓ hℓ f hf => ?_⟩
    let ℓ' : (WO S T → ℂ) →ₗ[ℂ] ℂ :=
      { toFun := fun f => starRingEnd ℂ (ℓ (cj id f))
        map_add' := fun a b => by
          have : cj id (a + b) = cj id a + cj id b := by funext z; simp [cj_id_apply]
          rw [this, map_add (f := _), map_add (f := _)]
        map_smul' := fun c a => by
          have : cj id (c • a) = starRingEnd ℂ c • cj id a := by funext z; simp [cj_id_apply]
          rw [this, map_smul, smul_eq_mul, map_mul, Complex.conj_conj]; rfl }
    have h1 : starRingEnd ℂ (ℓ (cj id ((ω.toSgn true) ((ofSgn true S).symm g, h) (cj id f)))) =
        (r : ℂ) * (splitFacO χS χT x y : ℂ) * starRingEnd ℂ (ℓ (cj id (cj id f))) :=
      H ℓ' (fun u hu f' hf' => by
        show starRingEnd ℂ (ℓ (cj id (heisO ψ (negSp S) T u f'))) = starRingEnd ℂ (ℓ (cj id f'))
        rw [← hz2, hℓ u hu (cj id f') ((thS (cj id f')).2 (by rwa [cj_id_cj_id]))]) (cj id f) ((thS f).1 hf)
    rw [cj_id_cj_id, ← key ω (g, h) f] at h1
    rw [splitFacO_inv]
    have h2 := congrArg (starRingEnd ℂ) h1
    simp only [map_mul, Complex.conj_conj, Complex.conj_ofReal] at h2
    exact h2

end GlobalTheory.ConjWeilBack
end
end

