module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0306
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0390
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0304
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0255
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0027
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0026
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleDiscreteSeriesOfHasParam
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HasDRepIffHasDerivAt
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.WeilRepresentationUnitaryPair
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0395
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0314
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SplitPlaceLocalGroupElementsJacobiBessel
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.MemIdAtOfSupp
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0092
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0391
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SelfDualSplitComponentIsLatticeStabilizerEq
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsCombAt
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0018
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0191
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0400

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.MovedVacuumInvariantUnderStdLatticeStabilizers
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Forms Formalism.UG
open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.MixPer GlobalTheory.Core.Rk GlobalTheory.AdForm
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.KJInf Formalism.L2.Ker
open GlobalTheory.SeeSaw GlobalTheory.Unf

namespace GlobalTheory.AdForm.StabMoveTup

theorem unramAt_of_chrEq_mul {D : D7} {c : (AE D)ˣ →* Circle} {χ ξ : Formalism.L2.Host.HChar D.host.E} (hc : ChrEq c (χ * ξ))
    (hu : ∀ P : HeightOneSpectrum (𝓞 D.host.E), (∀ k : Fin 2, ¬ Formalism.L2.Host.OverP D.host (D.host.g k) P) → χ.UnrAt P)
    (hξ : ∀ P : HeightOneSpectrum (𝓞 D.host.E), ¬ ξ.UnrAt P → IsSplitPl D.host P)
    {v ε} (hv : GlobalTheory.WeilParts.NonSplitAt D v ε) : GlobalTheory.WeilParts.UnramAt ε c := by
  refine GlobalTheory.UnramOver.unramAt_of_unrAt D c _ hc v ε hv.1 fun P hP => Formalism.L2.Host.HChar.UnrAt.mul (hu P fun k hk => ?_) ?_
  · obtain ⟨e, he⟩ := GlobalTheory.ChoiceAdm.exists_idem
      (GlobalTheory.Mem.Chr.splitsC_main D.R D.host _ (D.host.g_prime k) (D.nd.g_split k) P hk).2.2.1
    exact GlobalTheory.AdTh.RecPair.under_ne he hv hP
  · by_contra hn
    obtain ⟨e, he⟩ := GlobalTheory.ChoiceAdm.exists_idem (hξ P hn)
    exact GlobalTheory.AdTh.RecPair.under_ne he hv hP

theorem moveT_mul_stab : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)) ψ θ, IsStdChar (I.rec7 l Z) ψ (-1) → IsInfFam θ → ∀ (i : ℕ) (hi : i + 1 ≤ B.R.m) vac, IsVacO ψ θ ((I.rec7 l Z).sp.X i) ((I.rec7 l Z).sp.X (i + 1)) (fun _ => 1) (fun _ => 1) (intVec _ _) (intVec _ _) vac → ∀ (a : I.ι) μ om, ChrEq μ (I.C.mu0 ⟨i, hi⟩ * I.xi a) → IsWeilDatumO ψ _ _ μ μ om → ∀ c₀ g h, g ∈ GfC _ → h ∈ GfC _ → GlobalTheory.AdForm.VacAll.MoveT I l Z θ i hi c₀ μ om vac (g) (h) → ∀ k ∈ GfC _, ∀ k' ∈ GfC _, Moves _ (rankN (I.rec7 l Z) i (Nat.le_of_succ_le hi)) k (Formalism.L2.Col.stdLat (I.rec7 l Z).host.E _) → Moves _ (rankN (I.rec7 l Z) (i + 1) hi) k' (Formalism.L2.Col.stdLat (I.rec7 l Z).host.E _) → GlobalTheory.AdForm.VacAll.MoveT I l Z θ i hi c₀ μ om vac (g * k) (h * k') := by
  intro B X I hI hPins l Z ψ θ hψ hθ i hi vac hvac a μ om hchr hW c₀ g h hg hh hM k hk k' hk' mk mk' N N' hN hN' x y hx hy
  have hP := (GlobalTheory.AdForm.StdStepsT.stdPair_steps_all I hI hPins l Z ψ θ hψ hθ).1 i hi
  have b := StabMove.intG_of_moves _ mk
  have b' := StabMove.intG_of_moves _ mk'
  have a₁ := b.inv hP.gS
  have a₁' := b'.inv hP.gT
  rw [inv_inv] at a₁ a₁'
  have hξ : ∀ P, ¬ (I.xi a).UnrAt P → IsSplitPl B.host P := fun P hn =>
    ((GlobalTheory.Mem.ReadTwist.isTwist_of_reads B.R B.host B.fields.K B.embLL I.S (I.tup a) (I.xi a) (hI.xi_reads a)).1.2.2.2 P hn).1
  obtain ⟨x₁, y₁, rx, ry, e⟩ := StabMove.om_vac hP hW
    (fun v ε hv => unramAt_of_chrEq_mul hchr (I.C.isMu0 ⟨i, hi⟩).unr hξ hv) hvac hk hk' a₁ a₁'
  obtain ⟨x₀, sx⟩ := (GlobalTheory.Member.isDetRoot_laws _ _).1 g
  obtain ⟨y₀, sy⟩ := (GlobalTheory.Member.isDetRoot_laws _ _).1 h
  have e0 := hM N N' (StabMove.moves_of_mul _ a₁ b hN) (StabMove.moves_of_mul _ a₁' b' hN') x₀ y₀ sx sy
  have ex := StabMove.root_eq hW.resS hP.rk.2.2.1 ((GlobalTheory.Member.isDetRoot_laws _ _).2.2.2 _ _ _ _ sx rx) hx
  have ey := StabMove.root_eq hW.resS hP.rk.2.2.1 ((GlobalTheory.Member.isDetRoot_laws _ _).2.2.2 _ _ _ _ sy ry) hy
  rw [← Prod.mk_mul_mk, map_mul, Module.End.mul_apply, e, map_smul, ex, ey]
  refine (GlobalTheory.AdForm.VacAll.xiS_smul _ _ _ _ _).trans ?_
  funext z
  have e1 := congrFun e0 z
  rw [e1]
  simp only [map_mul, Circle.coe_mul, Circle.coe_inv, mul_inv]
  ring

end GlobalTheory.AdForm.StabMoveTup
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.MovesOfMatrixMemLevelZero
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SplitWeil GlobalTheory.LatPair GlobalTheory.SeeSaw GlobalTheory.FinPl ValuativeRel
open scoped TensorProduct nonZeroDivisors
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open scoped Pointwise

open GlobalTheory.StepData GlobalTheory.RootEx GlobalTheory.SymChain

namespace GlobalTheory.LevX

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  {ι n : Type} [Fintype n] [DecidableEq n] {c : ℕ}


open MeasureTheory IsDedekindDomain NumberField Matrix ValuativeRel in
open scoped TensorProduct nonZeroDivisors in
open scoped Pointwise in
attribute [local instance] _root_.Formalism.BasicNotions.Host.cmStar in
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  {ι n : Type} [Fintype n] [DecidableEq n] {c : ℕ} in
theorem _root_.GlobalTheory.LevX.conj_embX_val (ϖ : kˣ) (ord : ι ≃ n ⊕ Fin c) (g : GL n k) :
    ((_root_.GlobalTheory.StepData.typeFrame ϖ ord).bas⁻¹ *
        _root_.GlobalTheory.RootEx.embX c g *
        (_root_.GlobalTheory.StepData.typeFrame ϖ ord).bas).val.toBlocks₁₁ = g.val := by
  simp [_root_.GlobalTheory.StepData.typeFrame, _root_.GlobalTheory.StepData.LatFrame.bas,
    _root_.GlobalTheory.RootEx.embA, _root_.GlobalTheory.RootEx.embX, Matrix.fromBlocks_multiply]


open MeasureTheory IsDedekindDomain NumberField Matrix ValuativeRel in
open scoped TensorProduct nonZeroDivisors in
open scoped Pointwise in
attribute [local instance] _root_.Formalism.BasicNotions.Host.cmStar in
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  {ι n : Type} [Fintype n] [DecidableEq n] {c : ℕ} in
theorem _root_.GlobalTheory.LevX.mem_KO_of_embX_mem_stabLat (ϖ : kˣ) (ord : ι ≃ n ⊕ Fin c) {g : GL n k}
    (h : _root_.GlobalTheory.RootEx.embX c g ∈
      _root_.GlobalTheory.StepData.stabLat (_root_.GlobalTheory.StepData.typeFrame ϖ ord).bas) :
    g ∈ _root_.GlobalTheory.SplitWeil.KO k n := by
  set b := (_root_.GlobalTheory.StepData.typeFrame ϖ ord).bas with hb
  have hconj : b⁻¹ * _root_.GlobalTheory.RootEx.embX c g * b ∈
      _root_.GlobalTheory.SplitWeil.KO k (n ⊕ Fin c) := by
    unfold _root_.GlobalTheory.StepData.stabLat at h
    simpa [MulAut.conj_apply] using Subgroup.mem_comap.1 h
  obtain ⟨h₁, h₂⟩ := (_root_.GlobalTheory.SplitFlip.mem_KO_iff _).1 hconj
  have hinv : (b⁻¹ * _root_.GlobalTheory.RootEx.embX c g * b)⁻¹ =
      b⁻¹ * _root_.GlobalTheory.RootEx.embX c g⁻¹ * b := by
    simp [_root_.mul_inv_rev, mul_assoc]
  rw [_root_.GlobalTheory.SplitFlip.mem_KO_iff]
  refine ⟨fun i j => ?_, fun i j => ?_⟩
  · have e := congrFun (congrFun (_root_.GlobalTheory.LevX.conj_embX_val ϖ ord g) i) j
    rw [← e]
    exact h₁ (Sum.inl i) (Sum.inl j)
  · have e := congrFun (congrFun (_root_.GlobalTheory.LevX.conj_embX_val ϖ ord g⁻¹) i) j
    rw [← e]
    have := h₂ (Sum.inl i) (Sum.inl j)
    rw [hinv] at this
    exact this

open MeasureTheory IsDedekindDomain NumberField Matrix ValuativeRel in
open scoped TensorProduct nonZeroDivisors in
open scoped Pointwise in
attribute [local instance] _root_.Formalism.BasicNotions.Host.cmStar in
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  {ι n : Type} [Fintype n] [DecidableEq n] {c : ℕ} in
omit [TopologicalSpace k] [IsNonarchimedeanLocalField k] in
private lemma mulVec_apply_mem_integer_of_entries_mem_integer {M : Matrix n n k}
    (hM : ∀ i j, M i j ∈ (ValuativeRel.valuation k).integer) {y : n → k}
    (hy : ∀ j, y j ∈ (ValuativeRel.valuation k).integer) (i : n) :
    (M *ᵥ y) i ∈ (ValuativeRel.valuation k).integer := by
  simp only [Matrix.mulVec, dotProduct]
  exact Subring.sum_mem _ fun j _ => Subring.mul_mem _ (hM i j) (hy j)


open MeasureTheory IsDedekindDomain NumberField Matrix ValuativeRel in
open scoped TensorProduct nonZeroDivisors in
open scoped Pointwise in
attribute [local instance] _root_.Formalism.BasicNotions.Host.cmStar in
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  {ι n : Type} [Fintype n] [DecidableEq n] {c : ℕ} in
theorem _root_.GlobalTheory.LevX.smul_stdLat_of_mem_KO {g : GL n k} (h : g ∈ _root_.GlobalTheory.SplitWeil.KO k n) :
    g • _root_.GlobalTheory.SplitLat.stdLat k n = _root_.GlobalTheory.SplitLat.stdLat k n := by
  obtain ⟨h₁, h₂⟩ := (_root_.GlobalTheory.SplitFlip.mem_KO_iff _).1 h
  ext x
  change x ∈ (g : Matrix n n k) • _root_.GlobalTheory.SplitLat.stdLat k n ↔ _
  rw [Submodule.mem_smul_pointwise_iff_exists]
  constructor
  · rintro ⟨y, hy, rfl⟩
    rw [_root_.GlobalTheory.SplitLat.mem_std] at hy ⊢
    intro i
    rw [Matrix.smul_eq_mulVec]
    exact mulVec_apply_mem_integer_of_entries_mem_integer h₁ hy i
  · intro hx
    refine ⟨((g⁻¹ : GL n k) : Matrix n n k) • x, ?_, ?_⟩
    · rw [_root_.GlobalTheory.SplitLat.mem_std] at hx ⊢
      intro i
      rw [Matrix.smul_eq_mulVec]
      exact mulVec_apply_mem_integer_of_entries_mem_integer h₂ hx i
    · rw [smul_smul, ← Units.val_mul, mul_inv_cancel, Units.val_one, one_smul]

end GlobalTheory.LevX
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.MovesOfMemLev
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SplitWeil GlobalTheory.LatPair GlobalTheory.SeeSaw GlobalTheory.FinPl ValuativeRel
open scoped TensorProduct nonZeroDivisors
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open scoped Pointwise

noncomputable section
namespace GlobalTheory.SeeSaw.LevMoves

section
variable {D : D7} {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem mulVec_sec (q : SplitPt D k) {m n : ℕ} (M : Matrix (Fin m) (Fin n) (AE D)) (y : Fin n → k) :
    M *ᵥ (fun i => q.sec (y i)) = fun i => q.sec ((M.map q.pr *ᵥ y) i) := by
  funext i
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [Matrix.mulVec, dotProduct, map_sum, Matrix.map_apply]
  refine Finset.sum_congr rfl fun j _ => ?_
  have h := q.sec_pr (M i j * q.sec (y j))
  rw [RingHom.map_mul, q.pr_sec, mul_left_comm, ← GlobalTheory.FrameGlob.sec_eq_mul] at h
  exact h.symm

theorem isLat_moved (q : SplitPt D k) {PP : Formalism.L2.DIV.Pl D.host.E} (hq : Formalism.L2.NTheta.IsIdemAt q.e PP) (S : HSp D)
    (Λ L : Lat S) (β : GL (Fin S.rank) (Lev.EAf D)) (hβ : Formalism.L2.DIV.IsFrame β Λ) (t : GA D S)
    (ht : Moves S t Λ L (· = q.v)) {Y : Type} [Fintype Y] [DecidableEq Y] (F : GlobalTheory.LocMod.Frame k S.rank Y) (bas : GL Y k)
    (σ : Fin S.rank ≃ Y) (hM : GlobalTheory.LocMod.MovedTo (GlobalTheory.LocMod.ofSplit q) S t β ((F.β * bas.val).submatrix id σ))
    (x : Y → k) : x ∈ GlobalTheory.StepData.latOf bas ↔ (fun i => q.sec ((F.β *ᵥ x) i)) ∈ latV S L (· = q.v) := by
  obtain ⟨B, hB, hl⟩ := GlobalTheory.LocMod.PinEx.exists_topFrame q hq S Λ β hβ
  have hs : Function.Surjective (toEAf D) := by
    refine (Algebra.TensorProduct.comm D.host.F (Af D.host.F) D.host.E).surjective.comp ?_
    exact Algebra.TensorProduct.map_surjective _ _ (fun α => ⟨pairA _ 0 α, rfl⟩) Function.surjective_id
  choose f hf using hs
  have e : (β.val.map f).map (toEAf D) = β.val := by ext i j; exact hf _
  have h1 := hB _ e
  have h2 := hM _ e
  rw [GlobalTheory.MixModel.mt_one, Matrix.one_mul] at h1
  rw [Matrix.map_mul, h1] at h2
  have h3 : (mt S t).map q.pr *ᵥ (B.val *ᵥ fun i => ((bas⁻¹).val *ᵥ x) (σ i)) = F.β *ᵥ x := by
    rw [Matrix.mulVec_mulVec]
    refine (congrArg (· *ᵥ _) h2).trans ?_
    have : (fun i => ((bas⁻¹).val *ᵥ x) (σ i)) = ((bas⁻¹).val *ᵥ x) ∘ σ := rfl
    rw [this, Matrix.submatrix_mulVec_equiv, Function.comp_id, Function.comp_assoc, Equiv.self_comp_symm, Function.comp_id,
      Matrix.mulVec_mulVec, Matrix.mul_assoc, Units.mul_inv, Matrix.mul_one]
  rw [← h3, ← mulVec_sec, ← ht _ fun i => GlobalTheory.FrameGlob.sec_mem_idAt q _, hl, Matrix.mulVec_mulVec, Units.inv_mul,
    Matrix.one_mulVec, GlobalTheory.StepData.mem_latOf]
  exact ⟨fun h i => h _, fun h i => by simpa using h (σ.symm i)⟩

theorem smul_latOf {Y : Type} [Fintype Y] [DecidableEq Y] {bas g : GL Y k} (h : g ∈ GlobalTheory.StepData.stabLat bas) :
    g • GlobalTheory.StepData.latOf bas = GlobalTheory.StepData.latOf bas := by
  have h1 := GlobalTheory.StepData.mem_stabLat_iff.1 h
  ext y
  conv_rhs => rw [← h1]
  change (∃ x, x ∈ GlobalTheory.StepData.latOf bas ∧ g • x = y) ↔ _
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact (GlobalTheory.StepData.mulVec_mem_latOf g).2 hx
  · intro hy
    refine ⟨g⁻¹ • y, (GlobalTheory.StepData.mulVec_mem_latOf g).1 ?_, smul_inv_smul _ _⟩
    have : g.val *ᵥ (g⁻¹ • y) = y := smul_inv_smul g y
    rwa [this]

end

end GlobalTheory.SeeSaw.LevMoves
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.NoTransvectionInvariantPairOnScaledKernel
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.AutomorphicEvaluation Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.Core.Rk GlobalTheory.Core.Mi
open scoped TensorProduct InnerProductSpace Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (latV Moves MonoAt OrthAt PrimAt idAt intAt grpAt colMul Lat SplitPt GoodBF GluedCore IsSumFrame)
open GlobalTheory.SeeSaw (idV dI FI)
open ValuativeRel
open GlobalTheory.Core.Mi.LatMatch
open IsLocalRing

noncomputable section
namespace GlobalTheory.LatPair

theorem no_pair_on_scaled_kernel : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (n : Type) [Fintype n] [DecidableEq n] (i : n) (P : GlobalTheory.LatPair.Pair k n) (c : k), 3 ≤ Fintype.card n → c ≠ 0 → (∀ x : n → k, x ∈ P.lat ↔ (∀ j, c⁻¹ * x j ∈ 𝒪[k]) ∧ ∃ s : 𝒪[k], s ∈ IsLocalRing.maximalIdeal 𝒪[k] ∧ (s : k) = c⁻¹ * x i) → (∀ (x : n → k) (a : 𝓀[k]), P.HasVal x a → ∀ (b d : n) (t : 𝒪[k]), b ≠ d → (b ≠ i ∨ t ∈ IsLocalRing.maximalIdeal 𝒪[k]) → P.HasVal (x + Pi.single b ((t : k) * x d)) a) → False := by
  intro k _ _ _ _ n _ _ i P c hn hc hlat hcl
  have hmem : ∀ b, b ≠ i → Pi.single b c ∈ P.lat := by
    intro b hb
    rw [hlat]
    refine ⟨fun j => ?_, ⟨0, zero_mem _, ?_⟩⟩
    · by_cases h : j = b
      · subst h; simp [hc]
      · rw [Pi.single_eq_of_ne h]; simp
    · rw [Pi.single_eq_of_ne (Ne.symm hb)]; simp
  have hzero : ∀ a, a ≠ i → P.HasVal (Pi.single a c) 0 := by
    intro a ha
    obtain ⟨d, hda, hdi⟩ : ∃ d, d ≠ a ∧ d ≠ i := by
      by_contra h
      push_neg at h
      have hsub : (Finset.univ : Finset n) ⊆ {a, i} := fun d _ => by
        by_cases hd : d = a
        · simp [hd]
        · simp [h d hd]
      have h1 := Finset.card_le_card hsub
      have h2 : ({a, i} : Finset n).card ≤ 2 := Finset.card_le_two
      rw [Finset.card_univ] at h1
      omega
    obtain ⟨v, hv⟩ := (Pair.mem_lat_iff (P := P)).1 (hmem d hdi)
    obtain ⟨w, hw⟩ := (Pair.mem_lat_iff (P := P)).1 (hmem a ha)
    have h1 := hcl _ _ hv a d 1 (Ne.symm hda) (Or.inl ha)
    have hx : (Pi.single d c + Pi.single a (((1 : 𝒪[k]) : k) * (Pi.single d c : n → k) d) : n → k) = Pi.single d c + Pi.single a c := by
      simp
    rw [hx] at h1
    have h3 := h1.unique (hv.add hw)
    have hw0 : w = 0 := by linear_combination -h3
    exact hw0 ▸ hw
  obtain ⟨a, ha⟩ : ∃ a, a ≠ i := by
    by_contra h
    push_neg at h
    have : Fintype.card n ≤ 1 := Fintype.card_le_one_iff.2 (fun x y => (h x).trans (h y).symm)
    omega
  have hzi : ∀ t : 𝒪[k], t ∈ IsLocalRing.maximalIdeal 𝒪[k] → P.HasVal (Pi.single i ((t : k) * c)) 0 := by
    intro t ht
    have h1 := hcl _ _ (hzero a ha) i a t (Ne.symm ha) (Or.inr ht)
    rw [Pi.single_eq_same] at h1
    simpa using h1.sub (hzero a ha)
  apply P.fn_ne
  ext ⟨x, hx⟩
  obtain ⟨hxj, s, hs, hsx⟩ := (hlat x).1 hx
  have hsing : ∀ b, P.HasVal (Pi.single b (x b)) 0 := by
    intro b
    by_cases hb : b = i
    · subst hb
      have he : (s : k) * c = x b := by rw [hsx]; field_simp
      simpa [he] using hzi s hs
    · have h := (hzero b hb).smul ⟨c⁻¹ * x b, hxj b⟩
      have he : (⟨c⁻¹ * x b, hxj b⟩ : 𝒪[k]) • (Pi.single b c : n → k) = Pi.single b (x b) := by
        rw [← Pi.single_smul']; congr 1; change (c⁻¹ * x b) * c = x b; field_simp
      simpa [he] using h
  have hsum : P.HasVal (∑ b, Pi.single b (x b)) 0 :=
    Finset.sum_induction _ (fun y => P.HasVal y 0) (fun _ _ h h' => by simpa using h.add h')
      ⟨P.lat.zero_mem, map_zero P.fn⟩ (fun b _ => hsing b)
  rw [Finset.univ_sum_single] at hsum
  rw [LinearMap.zero_apply]
  exact hsum.2

end GlobalTheory.LatPair
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.NormOneHomothetyCarriesSelfDualOfSplitComponent
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.AutomorphicEvaluation Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.Core.Rk GlobalTheory.Core.Mi
open scoped TensorProduct InnerProductSpace Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (latV Moves MonoAt OrthAt PrimAt idAt intAt grpAt colMul Lat SplitPt GoodBF GluedCore IsSumFrame)
open GlobalTheory.SeeSaw (idV dI FI)
open ValuativeRel
open GlobalTheory.Core.Mi.LatMatch

noncomputable section

namespace GlobalTheory.Core.Mi.LatMatch

open GlobalTheory.FinPl.FrameLat


set_option maxHeartbeats 1000000 in
theorem sMoves_of_wComp : ∀ (D : D7) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (p : SplitPt D k) (S : HSp D) (L L' : Lat S) (c : AE D) (g : GA D S), IsSelfDualC S L → IsSelfDualC S L' → NormOneAt p.v c → (∀ x : Fin S.rank → k, (fun i => p.sec (x i)) ∈ latV S L (· = p.v) ↔ (fun i => p.sec ((p.pr c • ((Formalism.L2.Theta.mt S g).map p.pr *ᵥ x)) i)) ∈ latV S L' (· = p.v)) → SMoves S c g L L' p.v := by
  intro D k _ _ _ _ p S L L' c g hL hL' hc hw
  have hpc : p.pr c * p.pr (cA D c) = 1 := by rw [← map_mul, hc.1, map_one]
  have hGinv : ∀ x : Fin S.rank → k,
      (Formalism.L2.Theta.mt S g).map p.pr *ᵥ ((Formalism.L2.Theta.mt S g⁻¹).map p.pr *ᵥ x) = x := by
    intro x
    rw [Matrix.mulVec_mulVec, ← Matrix.map_mul,
      show Formalism.L2.Theta.mt S g * Formalism.L2.Theta.mt S g⁻¹ = Formalism.L2.Theta.mt S (g * g⁻¹) from rfl, mul_inv_cancel,
      show Formalism.L2.Theta.mt S 1 = 1 from rfl, Matrix.map_one p.pr (map_zero _) (map_one _), Matrix.one_mulVec]
  have hsec : ∀ u : Fin S.rank → k, Formalism.L2.Theta.mt S g *ᵥ (fun i => p.sec (u i)) =
      fun i => p.sec (((Formalism.L2.Theta.mt S g).map p.pr *ᵥ u) i) := by
    intro u
    funext i
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [Matrix.mulVec, dotProduct, map_sum, Matrix.map_apply]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [sec_mul, p.sec_pr, mul_comm p.e, mul_assoc, e_mul_sec]
  have hc1 : ∀ a : k, c * p.sec a = p.sec (p.pr c * a) := by
    intro a; rw [mul_comm, sec_mul_right, mul_comm]
  have hc2 : ∀ b : k, c * cA D (p.sec b) = cA D (p.sec (p.pr (cA D c) * b)) := by
    intro b
    have h : c * cA D (p.sec b) = cA D (cA D c * p.sec b) := by rw [map_mul, cA_cA]
    rw [h, mul_comm, sec_mul_right, mul_comm]
  have hB : ∀ x z : Fin S.rank → k,
      ∑ i, ∑ j, (p.pr c • ((Formalism.L2.Theta.mt S g).map p.pr *ᵥ x)) i * p.pr (cA D (incA D (S.gram i j))) *
          (p.pr (cA D c) • ((Formalism.L2.Theta.mt S g).map (fun a => p.pr (cA D a)) *ᵥ z)) j =
        ∑ i, ∑ j, x i * p.pr (cA D (incA D (S.gram i j))) * z j := by
    intro x z
    rw [← pairing_inv (p := p) g x z]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    simp only [Pi.smul_apply, smul_eq_mul]
    linear_combination (((Formalism.L2.Theta.mt S g).map p.pr *ᵥ x) i * p.pr (cA D (incA D (S.gram i j))) *
      (((Formalism.L2.Theta.mt S g).map (fun a => p.pr (cA D a)) *ᵥ z) j)) * hpc
  intro y hy
  have hyd : y = (fun i => p.sec (p.pr (y i))) + (fun i => cA D (p.sec (p.pr (cA D (y i))))) := by
    funext i
    simp only [Pi.add_apply, p.sec_pr]
    rw [map_mul, cA_cA, ← add_mul]
    exact ((idem_iff p _).1 (hy i)).symm
  obtain ⟨u, z, rfl⟩ : ∃ u z : Fin S.rank → k, y = (fun i => p.sec (u i)) + (fun i => cA D (p.sec (z i))) :=
    ⟨_, _, hyd⟩
  have himg : c • (Formalism.L2.Theta.mt S g *ᵥ ((fun i => p.sec (u i)) + (fun i => cA D (p.sec (z i))))) =
      (fun i => p.sec ((p.pr c • ((Formalism.L2.Theta.mt S g).map p.pr *ᵥ u)) i)) +
        (fun i => cA D (p.sec ((p.pr (cA D c) • ((Formalism.L2.Theta.mt S g).map (fun a => p.pr (cA D a)) *ᵥ z)) i))) := by
    funext i
    have h1 := congrFun (hsec u) i
    have h2 := congrFun (mt_csec (p := p) g z) i
    have h3 : (Formalism.L2.Theta.mt S g *ᵥ ((fun i => p.sec (u i)) + (fun i => cA D (p.sec (z i))))) i =
        p.sec (((Formalism.L2.Theta.mt S g).map p.pr *ᵥ u) i) +
          cA D (p.sec ((((Formalism.L2.Theta.mt S g).map (fun a => p.pr (cA D a))) *ᵥ z) i)) := by
      rw [Matrix.mulVec_add, Pi.add_apply, h1, h2]
    have h4 : c * (p.sec (((Formalism.L2.Theta.mt S g).map p.pr *ᵥ u) i) +
          cA D (p.sec ((((Formalism.L2.Theta.mt S g).map (fun a => p.pr (cA D a))) *ᵥ z) i))) =
        p.sec (p.pr c * ((Formalism.L2.Theta.mt S g).map p.pr *ᵥ u) i) +
          cA D (p.sec (p.pr (cA D c) * (((Formalism.L2.Theta.mt S g).map (fun a => p.pr (cA D a))) *ᵥ z) i)) := by
      rw [mul_add, hc1, hc2]
    show c * (Formalism.L2.Theta.mt S g *ᵥ ((fun i => p.sec (u i)) + (fun i => cA D (p.sec (z i))))) i = _
    refine (congrArg (c * ·) h3).trans (h4.trans ?_)
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  rw [himg, decomp hL, decomp hL']
  refine and_congr (hw u) ?_
  rw [csec_mem_iff hL, csec_mem_iff hL']
  constructor
  · intro h x' hx'
    have hx : p.pr c • ((Formalism.L2.Theta.mt S g).map p.pr *ᵥ
        (p.pr (cA D c) • ((Formalism.L2.Theta.mt S g⁻¹).map p.pr *ᵥ x'))) = x' := by
      rw [Matrix.mulVec_smul, smul_smul, hpc, one_smul, hGinv]
    have hmem := (hw (p.pr (cA D c) • ((Formalism.L2.Theta.mt S g⁻¹).map p.pr *ᵥ x'))).2 (by rw [hx]; exact hx')
    rw [← hx, hB]
    exact h _ hmem
  · intro h x hx
    have h5 := h _ ((hw x).1 hx)
    rwa [hB] at h5

end GlobalTheory.Core.Mi.LatMatch

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.OrthAtSumLatO
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory Matrix ValuativeRel GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.FinPl
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section
namespace GlobalTheory.Core.Rk.SumSplit

theorem orthAt_sumLatO : ∀ (D : D7) (S A B : HSp D) (o : OrthDec S A B) (LA : Lat A) (LB : Lat B) (v : Pl D),
    OrthAt o (GlobalTheory.Core.Rk.SumBox.sumLatO o LA LB) LA LB v := by
  intro D S A B o LA LB v y
  constructor
  · intro hy
    refine ⟨GlobalTheory.SeeSaw.SplitLat.rat_mulVec_mem_latV o.qA (fun x hx => ?_) _ hy,
      GlobalTheory.SeeSaw.SplitLat.rat_mulVec_mem_latV o.qB (fun x hx => ?_) _ hy⟩
    · obtain ⟨x₁, hx₁, x₂, -, rfl⟩ := (GlobalTheory.Core.Rk.SumBox.mem_sumLatO o LA LB x).1 hx
      rw [GlobalTheory.Core.Rk.SumBox.qA_split]; exact hx₁
    · obtain ⟨x₁, -, x₂, hx₂, rfl⟩ := (GlobalTheory.Core.Rk.SumBox.mem_sumLatO o LA LB x).1 hx
      rw [GlobalTheory.Core.Rk.SumBox.qB_split]; exact hx₂
  · rintro ⟨hA, hB⟩
    have e : y = o.jA *ᵥ (o.pA *ᵥ y) + o.jB *ᵥ (o.pB *ᵥ y) := by
      have hs : o.jA * o.pA + o.jB * o.pB = 1 := by
        change (o.iA.map (incA D)) * (o.qA.map (incA D)) + (o.iB.map (incA D)) * (o.qB.map (incA D)) = 1
        rw [← Matrix.map_mul, ← Matrix.map_mul, ← Matrix.map_add _ (map_add (incA D)),
          o.iA_qA_add, Matrix.map_one _ (map_zero (incA D)) (map_one (incA D))]
      rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, ← Matrix.add_mulVec, hs, Matrix.one_mulVec]
    rw [e]
    exact add_mem
      (GlobalTheory.SeeSaw.SplitLat.rat_mulVec_mem_latV o.iA
        (fun x hx => GlobalTheory.Core.Rk.SumBox.iA_mem_sumLatO o LB hx) _ hA)
      (GlobalTheory.SeeSaw.SplitLat.rat_mulVec_mem_latV o.iB
        (fun x hx => GlobalTheory.Core.Rk.SumBox.iB_mem_sumLatO o LA hx) _ hB)

end GlobalTheory.Core.Rk.SumSplit
end
end

