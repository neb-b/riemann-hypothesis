module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0013
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0139
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.EntryAgree
public import Formalism.LocalToGlobal.Columns.ChainTw
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0086
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0085
public import Development.AbelianVarietyTheory.Definitions.Foundations.T2SpaceAdeleRing
public import Development.AbelianVarietyTheory.Definitions.Foundations.NotIsSplitOfIsInertAt
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0014
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.PairwiseDisjointCell
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0087
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.RamificationIdxEqOneOfIsSquare
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.GaussianBinomialClosedForm
public import Development.AbelianVarietyTheory.Definitions.Foundations.GLintEqKOAndPrincEqKOne
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.FiniteDimensionalModel
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0006
public import Formalism.LocalToGlobal.BesselHermitianTheta.Bundle0002
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.WeilRepresentationUnitaryPair
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0140

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.DoublingSphericalVacuaToDoubledLatticeVacuum
section
noncomputable section

open scoped ComplexConjugate Matrix NNReal
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.Cusp GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (FinPl RealMat Lat IsFockVec IsSphOff HidaSetting volQ)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (ip delta swSec sZero IsKFinVec ThetaClause SectionClause CoefClause resL resR)
open GlobalTheory.Mem.Th (CptF)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Core.Rk.IP

namespace GlobalTheory.Core.Rk.VacBox

variable {D : D7}

theorem gram_dbl_inv (A : HSp D) : (dblSp A).gram⁻¹ = blkMat finSumFinEquiv A.gram⁻¹ (-A.gram⁻¹) :=
  Matrix.inv_eq_left_inv (by
    rw [gram_hdbl, dblGram, blkMat_mul, neg_mul_neg, Matrix.nonsing_inv_mul _ (isHermND_gram A).2.isUnit, blkMat_one])

theorem hO_dbl (A B : HSp D) (x y : WO (dblSp A) B) :
    hO (dblSp A) B x y = hO A B (resL A B x) (resL A B y) - hO A B (resR A B x) (resR A B y) := by
  simp only [hO]
  rw [gram_dbl_inv]
  simp only [← finSumFinEquiv.sum_comp, Fintype.sum_sum_type, resL, resR, Matrix.of_apply,
    blkMat, Matrix.submatrix_apply, Equiv.symm_apply_apply, Matrix.fromBlocks_apply₁₁, Matrix.fromBlocks_apply₁₂,
    Matrix.fromBlocks_apply₂₁, Matrix.fromBlocks_apply₂₂, Matrix.zero_apply, Matrix.neg_apply, map_zero,
    map_neg, zero_mul, Finset.sum_const_zero, add_zero, zero_add, neg_mul, Finset.sum_neg_distrib, sub_eq_add_neg]

theorem hO_neg_neg (A B : HSp D) (x y : WO A B) : hO A B (-x) (-y) = hO A B x y := by
  simp only [hO, Matrix.neg_apply, map_neg, mul_neg, neg_mul, neg_neg]

theorem symplOH_dbl (A B : HSp D) (x y : WO (dblSp A) B) :
    symplOH (dblSp A) B x y = symplOH A B (resL A B x) (resL A B y) - symplOH A B (resR A B x) (resR A B y) := by
  simp only [symplOH, symplO, hO_dbl, mul_sub, map_sub]

theorem symplOH_neg_neg (A B : HSp D) (x y : WO A B) : symplOH A B (-x) (-y) = symplOH A B x y := by
  simp only [symplOH, symplO, hO_neg_neg]

theorem resL_add (A B : HSp D) (x y : WO (dblSp A) B) : resL A B (x + y) = resL A B x + resL A B y :=
  Matrix.ext fun _ _ => rfl

theorem resR_add (A B : HSp D) (x y : WO (dblSp A) B) : resR A B (x + y) = resR A B x + resR A B y :=
  Matrix.ext fun _ _ => rfl

def resLHom (A B : HSp D) : WO (dblSp A) B →+ WO A B where
  toFun := resL A B
  map_zero' := Matrix.ext fun _ _ => rfl
  map_add' := resL_add A B

def resRHom (A B : HSp D) : WO (dblSp A) B →+ WO A B where
  toFun := resR A B
  map_zero' := Matrix.ext fun _ _ => rfl
  map_add' := resR_add A B

theorem conj_psi_eq {ψ : AddChar (AF D.host.F) ℂ} (hψ : ∀ x, ‖ψ x‖ = 1) (z : AF D.host.F) :
    conj (ψ z) = ψ (-z) := by
  rw [AddChar.map_neg_eq_inv, Complex.inv_def, Complex.normSq_eq_norm_sq, hψ, one_pow, inv_one, Complex.ofReal_one,
    mul_one]

theorem heisO_delta {ψ : AddChar (AF D.host.F) ℂ} (hψ : ∀ x, ‖ψ x‖ = 1) (A B : HSp D) (w₀ : WO (dblSp A) B)
    (f₁ f₂ : WO A B → ℂ) :
    heisO ψ (dblSp A) B w₀ (delta A B f₁ f₂) =
      delta A B (heisO ψ A B (resL A B w₀) f₁) (heisO ψ A B (-resR A B w₀) f₂) := by
  funext x
  simp only [heisO, GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero.delta, resL_add, resR_add, map_mul, conj_psi_eq hψ, symplOH_dbl, symplOH_neg_neg, neg_add]
  rw [sub_eq_add_neg, AddChar.map_add_eq_mul]
  ring

theorem sum_dbl_gram_inl (A : HSp D) (s : Fin (dblSp A).rank → D.host.E) (j : Fin A.rank) :
    ∑ k, star (s k) * (dblSp A).gram k (finSumFinEquiv (Sum.inl j)) =
      ∑ k, star ((fun k => s (finSumFinEquiv (Sum.inl k))) k) * A.gram k j := by
  rw [gram_hdbl]
  simp only [← finSumFinEquiv.sum_comp, Fintype.sum_sum_type, dblGram, blkMat, Matrix.submatrix_apply,
    Equiv.symm_apply_apply, Matrix.fromBlocks_apply₁₁, Matrix.fromBlocks_apply₂₁, Matrix.zero_apply, mul_zero,
    Finset.sum_const_zero, add_zero]

theorem sum_dbl_gram_inr (A : HSp D) (s : Fin (dblSp A).rank → D.host.E) (j : Fin A.rank) :
    ∑ k, star (s k) * (dblSp A).gram k (finSumFinEquiv (Sum.inr j)) =
      ∑ k, star ((-fun k => s (finSumFinEquiv (Sum.inr k))) k) * A.gram k j := by
  rw [gram_hdbl]
  simp only [← finSumFinEquiv.sum_comp, Fintype.sum_sum_type, dblGram, blkMat, Matrix.submatrix_apply,
    Equiv.symm_apply_apply, Matrix.fromBlocks_apply₁₂, Matrix.fromBlocks_apply₂₂, Matrix.zero_apply, mul_zero,
    Finset.sum_const_zero, zero_add, Matrix.neg_apply, Pi.neg_apply, star_neg, mul_neg, neg_mul]

theorem res_mem_latO {A B : HSp D} {LA : Lat A} {LB : Lat B} {P : FinPl D → Prop} {u : WO (dblSp A) B}
    (hu : u ∈ latO (dblSp A) B (sumLat finSumFinEquiv LA LA : Lat (dblSp A)) LB P) :
    resL A B u ∈ latO A B LA LB P ∧ resR A B u ∈ latO A B LA LB P := by
  have key : latO (dblSp A) B (sumLat finSumFinEquiv LA LA : Lat (dblSp A)) LB P ≤
      (latO A B LA LB P).comap (resLHom A B) ⊓ (latO A B LA LB P).comap (resRHom A B) := by
    refine (AddSubgroup.closure_le _).2 ?_
    rintro w ⟨α, hα, hP, a, ha, s, hs, t, ht, rfl⟩
    refine ⟨AddSubgroup.subset_closure
      ⟨α, hα, hP, a, ha, fun k => s (finSumFinEquiv (Sum.inl k)), hs.1, t, ht, ?_⟩,
      AddSubgroup.subset_closure
      ⟨α, hα, hP, a, ha, -fun k => s (finSumFinEquiv (Sum.inr k)), neg_mem hs.2, t, ht, ?_⟩⟩
    · ext i j
      simp only [resLHom, AddMonoidHom.coe_mk, ZeroHom.coe_mk, resL, Matrix.of_apply]
      exact congrArg (fun z => pairA D.host.F 0 α ⊗ₜ[D.host.F] (a * t i * z)) (sum_dbl_gram_inl A s j)
    · ext i j
      simp only [resRHom, AddMonoidHom.coe_mk, ZeroHom.coe_mk, resR, Matrix.of_apply]
      exact congrArg (fun z => pairA D.host.F 0 α ⊗ₜ[D.host.F] (a * t i * z)) (sum_dbl_gram_inr A s j)
  exact key hu

theorem latO_mono_at {A B : HSp D} (LA : Lat A) (LB : Lat B) {Sf : Finset (FinPl D)} {v : FinPl D} (hv : v ∉ Sf) :
    latO A B LA LB (fun u => u = v) ≤ latO A B LA LB (fun u => u ∉ Sf) := by
  refine AddSubgroup.closure_mono ?_
  rintro w ⟨α, hα, hP, rest⟩
  refine ⟨α, hα, fun v' hv' => hP v' fun h => hv' (h ▸ hv), rest⟩

theorem pair_dbl (A : HSp D) (x y : Fin (dblSp A).rank → D.host.E) :
    ∑ i, ∑ j, star (x i) * (dblSp A).gram i j * y j =
      (∑ i, ∑ j, star (x (finSumFinEquiv (Sum.inl i))) * A.gram i j * y (finSumFinEquiv (Sum.inl j))) -
      ∑ i, ∑ j, star (x (finSumFinEquiv (Sum.inr i))) * A.gram i j * y (finSumFinEquiv (Sum.inr j)) := by
  rw [gram_hdbl]
  simp only [← finSumFinEquiv.sum_comp, Fintype.sum_sum_type, dblGram, blkMat, Matrix.submatrix_apply,
    Equiv.symm_apply_apply, Matrix.fromBlocks_apply₁₁, Matrix.fromBlocks_apply₁₂, Matrix.fromBlocks_apply₂₁,
    Matrix.fromBlocks_apply₂₂, Matrix.zero_apply, Matrix.neg_apply, mul_zero, zero_mul, Finset.sum_const_zero,
    add_zero, zero_add, mul_neg, neg_mul, Finset.sum_neg_distrib, sub_eq_add_neg]

theorem selfDual_sumLat {A : HSp D} {L : Lat A} (hL : IsSelfDualC A L) :
    IsSelfDualC (dblSp A) (sumLat finSumFinEquiv L L) := by
  have hsum : Submodule.IsLattice D.host.E (sumLat finSumFinEquiv L L) := by
    let φ : ((Fin A.rank → D.host.E) × (Fin A.rank → D.host.E)) ≃ₗ[D.host.E]
        (Fin (A.rank + A.rank) → D.host.E) :=
      (LinearEquiv.sumArrowLequivProdArrow _ _ _ _).symm.trans
        (LinearEquiv.funCongrLeft _ _ finSumFinEquiv.symm)
    have e : sumLat finSumFinEquiv L L = (L.prod L).map (φ.toLinearMap.restrictScalars (𝓞 D.host.E)) := by
      ext w
      refine ⟨fun hw => ⟨(_, _), hw, pairVec_eta _ w⟩, ?_⟩
      rintro ⟨x, hx, rfl⟩
      exact (pairVec_mem_sumLat _).2 hx
    exact Submodule.IsLattice.of_fg D.host.E (e ▸ (hL.1.fg.prod hL.1.fg).map _)
  refine ⟨hsum, fun y => ⟨fun hy x hx => ?_, fun H => ?_⟩⟩
  · obtain ⟨b₁, hb₁⟩ := (hL.2 (fun i => y (finSumFinEquiv (Sum.inl i)))).1 hy.1
      (fun i => x (finSumFinEquiv (Sum.inl i))) hx.1
    obtain ⟨b₂, hb₂⟩ := (hL.2 (fun i => y (finSumFinEquiv (Sum.inr i)))).1 hy.2
      (fun i => x (finSumFinEquiv (Sum.inr i))) hx.2
    refine ⟨b₁ - b₂, ?_⟩
    rw [pair_dbl]
    push_cast
    linear_combination hb₁ - hb₂
  · refine ⟨(hL.2 _).2 fun x hx => ?_, (hL.2 _).2 fun x hx => ?_⟩
    · obtain ⟨b, hb⟩ := H (pairVec finSumFinEquiv x 0) ((pairVec_mem_sumLat _).2 ⟨hx, zero_mem _⟩)
      rw [pair_dbl] at hb
      simp only [pairVec_inl, pairVec_inr, Pi.zero_apply, star_zero, zero_mul, Finset.sum_const_zero, sub_zero] at hb
      refine ⟨b, ?_⟩
      show (b : D.host.E) = ∑ i, ∑ j, star (x i) * A.gram i j * y (finSumFinEquiv (Sum.inl j))
      exact hb
    · obtain ⟨b, hb⟩ := H (pairVec finSumFinEquiv 0 x) ((pairVec_mem_sumLat _).2 ⟨zero_mem _, hx⟩)
      rw [pair_dbl] at hb
      simp only [pairVec_inl, pairVec_inr, Pi.zero_apply, star_zero, zero_mul, Finset.sum_const_zero, zero_sub] at hb
      refine ⟨-b, ?_⟩
      show ((-b : 𝓞 D.host.E) : D.host.E) = ∑ i, ∑ j, star (x i) * A.gram i j * y (finSumFinEquiv (Sum.inr j))
      push_cast
      linear_combination -hb

theorem doubling_isLatVac : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (A B : HSp D) (LA : Lat A) (LB : Lat B), IsStdChar D ψ (-1) → IsSelfDualC A LA → IsSelfDualC (dblSp A) (sumLat finSumFinEquiv LA LA) ∧ ∀ (Sf : Finset (FinPl D)) (Φ₁ Φ₂ : WO A B → ℂ), IsSphOff ψ A B LA LB Sf Φ₁ → IsSphOff ψ A B LA LB Sf Φ₂ → ∀ v ∉ Sf, IsLatVac (heisO ψ (dblSp A) B) (latO (dblSp A) B (sumLat finSumFinEquiv LA LA : Lat (dblSp A)) LB fun u => u = v) (delta A B Φ₁ Φ₂) := by
  intro D ψ A B LA LB hψ hLA
  have hn : ∀ x, ‖ψ x‖ = 1 := hψ.1.2.1
  refine ⟨selfDual_sumLat hLA, ?_⟩
  intro Sf Φ₁ Φ₂ h₁ h₂ v hv
  have mono := latO_mono_at LA LB hv
  refine ⟨fun u hu => ?_, fun e he u hu hh => ?_⟩
  · obtain ⟨hL, hR⟩ := res_mem_latO hu
    have eL : resL A B (2 • u) = 2 • resL A B u := by rw [two_nsmul, two_nsmul, resL_add]
    have eR : -resR A B (2 • u) = 2 • (-resR A B u) := by
      rw [two_nsmul, two_nsmul, resR_add, neg_add]
    rw [heisO_delta hn, eL, eR, h₁.1 _ (mono hL), h₂.1 _ (neg_mem (mono hR))]
  · obtain ⟨hL, hR⟩ := res_mem_latO hu
    have hhL : IsHalf e (resL A B u) := fun i j => hh i (finSumFinEquiv (Sum.inl j))
    have hhR : IsHalf e (-resR A B u) := fun i j => by
      show e * -(u i (finSumFinEquiv (Sum.inr j))) = -(u i (finSumFinEquiv (Sum.inr j)))
      rw [mul_neg, hh]
    rw [heisO_delta hn, h₁.2 e he _ (mono hL) hhL, h₂.2 e he _ (neg_mem (mono hR)) hhR]

end GlobalTheory.Core.Rk.VacBox
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsCompletionTwistDataChainColumnsStatement
section
open NumberField IsDedekindDomain MeasureTheory ValuativeRel Matrix Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV Formalism.L2.Col GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.TwBridge
open GlobalTheory.TwBridgeInhab in
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_completionTwistData_chainColumns : ∀ (X : Fields) (Pr : Primes X) (R : Ranks) (Ch : Chars X Pr R.m) (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) (S₀ : Set ℕ) (mu : Tup X.F X.E X.K S₀) (cst : LocCst X (rowSG Pr sel mu)) (L : ChIdx X Pr R (QE sel (mu : Chr X.F X.E X.K))) (G : ChGlob X R.m) (s : ℕ), L.Ok Ch sel mu cst G s → ∀ (P : rowSG Pr sel mu), P.1 ∉ Pr.vGs → ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (ι : X.E →+* k) (ϖ : kˣ), GlobalTheory.SymBridge.IsCompl P.1 (qOf P.1) ι ϖ → GlobalTheory.IndefiniteRowSideFullHecke.FramePositiveSum.IsUnif ϖ → ∀ ψ : AddChar k Circle, Continuous ψ → HasConductor ψ 1 → (∀ (a : X.E) (b : ℤ) (n : ℕ), IntAt P.1 (G.xi0 * a - (b : X.E) / (qOf P.1 : X.E) ^ n) → (ψ (ι a) : ℂ) = Complex.exp (2 * Real.pi * Complex.I * b / (qOf P.1 : ℂ) ^ n)) → ∀ μ : ℕ → kˣ →* ℂˣ, (∀ i, i < R.m → (∀ (a : X.E) (u : kˣ), (u : k) = ι a → (μ (i + 1) u : ℂ) = G.σ₀ (muAt Ch sel mu cst i P a)) ∧ IsTame (μ (i + 1))) → ∃ W : TwData k, AtTwist (R := R) sel mu cst G.σ₀ P ι s W ∧ W.ϖ = ϖ ∧ W.ψ = ψ ∧ (∀ i, i < R.m → W.η (i + 1) * W.δ = μ (i + 1)) ∧ (W.sg = 1 ∨ W.sg = -1) := by
  intro X Pr R Ch sel S₀ mu cst L G s hL P hP k _ _ _ _ ι ϖ hc hϖ ψ hψc hψ1 hψt μ hμ
  have hm : R.m = s + 2 := hL.hm
  have hm0 : 0 < R.m := by omega
  have hq0 : (qOf P.1 : X.E) ≠ 0 := GlobalTheory.SymBridge.ComplRes.q_ne_zero hc
  have hqpos : 0 < qOf P.1 := Nat.pos_of_ne_zero fun h => hq0 (by rw [h, Nat.cast_zero])
  have hqmem : ((qOf P.1 : ℕ) : 𝓞 X.E) ∈ P.1.asIdeal := GlobalTheory.SymBridge.ComplRes.q_mem hc
  let δ : kˣ →* ℂˣ := μ 1 * (GlobalTheory.SmGL.unrChar k (μ 1 ϖ))⁻¹
  have hδ_unit (x : kˣ) (hx : valuation k (x : k) = 1) : δ x = μ 1 x := by
    simp [δ, GlobalTheory.SmGL.isUnram_unrChar k _ x hx]
  have hμ_unit (i : ℕ) {a : X.E} (ha : IsUnit (redP P.1 a)) :
      muAt Ch sel mu cst i P a = LocE.unitV (resChar (mu : Chr X.F X.E X.K) P.1)⁻¹ a := by
    unfold muAt
    rw [ite_eq_right hP]
    unfold LocE.locChar
    rw [GlobalTheory.LastSteps.vP_unit ha]
    simp
  have hμ_uniformizer (i : ℕ) :
      muAt Ch sel mu cst i P (qOf P.1 : X.E) = cst.muq (i + 1) P := by
    unfold muAt
    rw [ite_eq_right hP]
    unfold LocE.locChar
    rw [valuation_self P.1 _ hqmem hqpos, zpow_one, zpow_one, div_self hq0]
    have hred : redP P.1 (1 : X.E) = 1 := by
      rw [← (map_one (algebraMap (𝓞 X.E) X.E)), reduction_coe, map_one]
    have hu : IsUnit (redP P.1 (1 : X.E)) := hred ▸ isUnit_one
    unfold LocE.unitV
    rw [dite_eq_left hu]
    have hu_one : hu.unit = 1 := Units.ext (by rw [IsUnit.unit_spec, hred, Units.val_one])
    rw [hu_one, map_one, Units.val_one, mul_one]
  have hμ1 : ∀ (a : X.E) (u : kˣ), (u : k) = ι a → (μ 1 u : ℂ) = G.σ₀ (muAt Ch sel mu cst 0 P a) :=
    fun a u h => (hμ 0 hm0).1 a u h
  have ht1 : IsTame (μ 1) := (hμ 0 hm0).2
  have hδ_tame : IsTame δ := by
    intro x hx
    rw [hδ_unit x (val_eq_one_of_sub_one hx)]
    exact ht1 x hx

  have hδ : ∀ i, i < R.m → ∀ x : kˣ, valuation k (x : k) = 1 → μ (i + 1) x = δ x := by
    intro i hi x hx
    rw [hδ_unit x hx]
    obtain ⟨a, ha⟩ := exists_near hc.dense (x : k)
    have hva : valuation k (ι a) = 1 := by
      have e : ι a = (ι a - x) + x := by ring
      rw [e, Valuation.map_add_eq_of_lt_right _ (by rw [hx]; exact ha), hx]
    have ha0 : ι a ≠ 0 := by
      intro h0; rw [h0, map_zero] at hva; exact zero_ne_one hva
    have hint : IntAt P.1 a := GlobalTheory.SymBridge.ComplRes.intAt_of_v hc (le_of_eq hva)
    have hred : IsUnit (redP P.1 a) := (GlobalTheory.SymBridge.ComplRes.v_eq_one_iff_red hc hϖ hint).mp hva
    have hn : valuation k (((Units.mk0 (ι a) ha0 : kˣ) : k) - x) < 1 := ha
    rw [← tame_near (hμ i hi).2 hx hn, ← tame_near ht1 hx hn]
    apply Units.ext
    rw [(hμ i hi).1 a _ rfl, hμ1 a _ rfl, hμ_unit i hred, hμ_unit 0 hred]

  have hsq : G.σ₀ (cst.sq P) ^ 2 = ((Real.sqrt (qOf P.1) : ℝ) : ℂ) ^ 2 := by
    rw [← map_pow, hL.cst_ok.sq_sq P, map_natCast, ← Complex.ofReal_pow, Real.sq_sqrt (Nat.cast_nonneg _),
      Complex.ofReal_natCast]
  obtain ⟨sg, hsg1, hsg2⟩ : ∃ sg : ℂ, (sg = 1 ∨ sg = -1) ∧ G.σ₀ (cst.sq P) = sg * (Real.sqrt (qOf P.1) : ℂ) := by
    rcases sq_eq_sq_iff_eq_or_eq_neg.mp hsq with h | h
    · exact ⟨1, Or.inl rfl, by rw [h, one_mul]⟩
    · exact ⟨-1, Or.inr rfl, by rw [h, neg_one_mul]⟩
  refine ⟨⟨ϖ, hϖ, ψ, hψc, hψ1, δ, hδ_tame, eta μ R.m (δ),
    eta_unram μ R.m _ hδ, sg⟩, ⟨hP, hm, hc, ?_, ?_, ?_, hsg2⟩, rfl, rfl, fun i hi => eta_mul μ R.m _ hi, hsg1⟩
  · intro a ha
    show (ψ (ι a) : ℂ) = G.σ₀ (cst.psi P a)
    have hxi : IntAt P.1 G.xi0 := (hL.xiUnitAtPrime P).1
    have hx : valuation k (ι (G.xi0 * ((qOf P.1 : X.E) ^ cst.D P * a))) ≤ 1 :=
      GlobalTheory.SymBridge.ComplRes.v_le_one hc (hxi.mul ha)
    obtain ⟨i, -, hi⟩ := GlobalTheory.SymBridge.ComplRes.exists_rep hc hϖ (cst.D P) _ hx
    have hqk : ((qOf P.1 : ℕ) : k) ≠ 0 := by
      rw [← GlobalTheory.SymBridge.ComplRes.unif_eq_cast hc]; exact ϖ.ne_zero
    have hint : IntAt P.1 (G.xi0 * a - ((i : ℤ) : X.E) / (qOf P.1 : X.E) ^ cst.D P) := by
      apply GlobalTheory.SymBridge.ComplRes.intAt_of_v hc
      have e : ι (G.xi0 * ((qOf P.1 : X.E) ^ cst.D P * a)) - (i : k) =
          ι (G.xi0 * a - ((i : ℤ) : X.E) / (qOf P.1 : X.E) ^ cst.D P) * (ϖ : k) ^ cst.D P := by
        rw [GlobalTheory.SymBridge.ComplRes.unif_eq_cast hc]
        simp only [map_mul, map_sub, map_div₀, map_pow, map_intCast, map_natCast]
        push_cast
        field_simp
      rw [e, map_mul, map_pow] at hi
      have h0 : (0 : ValueGroupWithZero k) < valuation k (ϖ : k) ^ cst.D P :=
        pow_pos (zero_lt_iff.mpr (by simp)) _
      exact le_of_mul_le_mul_right (by rwa [one_mul]) h0
    rw [hψt a (i : ℤ) (cst.D P) hint, hL.weil P a (i : ℤ) ha hint]
  · intro a u ha hr hu
    show ((δ u : ℂˣ) : ℂ) = _
    have hva : valuation k (u : k) = 1 := by
      rw [hu]; exact (GlobalTheory.SymBridge.ComplRes.v_eq_one_iff_red hc hϖ ha).mpr hr
    rw [hδ_unit u hva, hμ1 a u hu, hμ_unit 0 hr]
    unfold LocE.unitV
    rw [dite_eq_left hr, dite_eq_left hr, MonoidHom.inv_apply, Units.val_inv_eq_inv_val, map_inv₀]
  · intro i hi
    show ((eta μ R.m (δ) (i + 1) * δ) ϖ : ℂ) = _
    rw [eta_mul μ R.m _ hi, (hμ i hi).1 ((qOf P.1 : ℕ) : X.E) ϖ hc.unif, hμ_uniformizer i]
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsIsSphSec
section
open scoped ComplexConjugate Matrix NNReal
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.Cusp GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (FinPl RealMat Lat IsFockVec IsSphOff HidaSetting volQ)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (ip delta swSec sZero IsKFinVec ThetaClause SectionClause CoefClause)
open GlobalTheory.Mem.Th (CptF)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Core.Rk.IP
open Formalism.UG (IsUnifV qV IsUnramInv GU KU IsInertAt)
open GlobalTheory.LFun (locChar IsSplitChart IsInertChart KGL UnrAt)

namespace GlobalTheory.KerInert

open scoped TensorProduct

theorem npow_zpow {q : ℕ} (hq : q ≠ 0) (r : ℝ≥0) (m : ℤ) (hr : (r : ℝ) = (q : ℝ) ^ (-(2 * m))) (t : ℂ) :
    GlobalTheory.Doubling.npow r t = (q : ℂ) ^ (-(2 * (m : ℂ) * t)) := by
  have h0 : (0 : ℝ) < q := by exact_mod_cast Nat.pos_of_ne_zero hq
  have h1 : ((r : ℝ) : ℂ) ≠ 0 := by rw [hr]; exact_mod_cast (zpow_pos h0 _).ne'
  rw [GlobalTheory.Doubling.npow, Complex.cpow_def_of_ne_zero h1, Complex.cpow_def_of_ne_zero (Nat.cast_ne_zero.2 hq),
    ← Complex.ofReal_log r.coe_nonneg, hr, Real.log_zpow, ← Complex.natCast_log]
  congr 1
  push_cast
  ring

theorem exists_isSphSec {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
    (hc : IsCMExt F E σ) {n : ℕ} {J : Matrix (Fin n) (Fin n) E} (hJ : IsHermND σ J)
    {Q : Matrix (Fin (n + n)) (Fin (n + n)) E} (hQ : Q = dblGram finSumFinEquiv J)
    (L : Submodule (𝓞 E) (Fin n → E)) (hL : Submodule.IsLattice E L) (μ : (AF F ⊗[F] E)ˣ →* Circle)
    {v : HeightOneSpectrum (𝓞 F)} {w : HeightOneSpectrum (𝓞 E)} (h : w.under (𝓞 F) = v) (hw : IsInertAt F E v w)
    (hq : qV F v ≠ 0) {s : ℂ} {φ : GLoc σ Q v → ℂ} (h1 : φ ∈ degPSFin σ Q L v (charAt μ v) s)
    (h2 : ∀ k ∈ KFin σ Q L v, ∀ g, φ (g * k) = φ g) (h3 : φ 1 = 1)
    {c : w.adicCompletion E →+* w.adicCompletion E} {e : GLoc σ J v ≃* GU c n} (he : IsInertChart σ J L h c e) :
    ∃ Φ, GlobalTheory.IndefiniteRowSideFullHecke.SphericalSectionVariables.IsSphSec c (qV F v) n (locChar μ w) s Φ ∧
      ∀ y, φ (ioH _ σ hQ (y, 1)) = Φ (GlobalTheory.IndefiniteRowSideFullHecke.SphericalSectionVariables.io1 c n (e y)) := by
  obtain ⟨f, hK, hio, hP, ha⟩ := _root_.GlobalTheory.DblInert.exists_dblChart F E σ hc n J hJ Q hQ L v w h hw c e he
  refine ⟨fun g => φ (f.symm g), fun p k hk => ?_, fun y => ?_⟩
  · have hp : f.symm p ∈ siegelH (Fv F v) σ Q := (hP _).2 (by rw [f.apply_symm_apply]; exact p.2)
    have hk' : f.symm k ∈ KFin σ Q L v := (hK _).2 (by rwa [f.apply_symm_apply])
    have e1 := (mem_degPSH.1 h1).1 ⟨_, hp⟩ 1
    have e3 : GlobalTheory.IndefiniteRowSideFullHecke.SphericalSectionVariables.aD c n p = Units.map (GlobalTheory.LFun.toCompl h).toMonoidHom (aH _ σ Q ⟨_, hp⟩) :=
      (congrArg _ (Subtype.ext (f.apply_symm_apply _).symm)).trans (ha ⟨_, hp⟩ ((hP _).1 hp))
    rw [mul_one, h3, mul_one, _root_.GlobalTheory.LFun.charAt_eq_locChar_of_isInertAt F E μ v w h hw, npow_zpow hq _ _ (GlobalTheory.AbsInert.absEv_inert F E σ hc v w h hw _)] at e1
    show φ (f.symm (p * k)) = _
    rw [map_mul, h2 _ hk', e3]
    exact e1
  · show _ = φ (f.symm _)
    rw [← hio y, f.symm_apply_apply]

theorem sphSec_inert : ∀ (D : D7) (A : HSp D) (L : Lat A), IsSelfDualC A L → ∀ (χ : (AE D)ˣ →* Circle) (b : ℕ), ResEta D χ b → ∀ (v : FinPl D) (w : HeightOneSpectrum (𝓞 D.host.E)) (h : w.under (𝓞 D.host.F) = v), IsInertAt D.host.F D.host.E v w → UnrAt χ w → ∀ (s : ℂ) (φ : Gv (dblSp A) v → ℂ), IsSphSecAt A L v χ⁻¹ s φ → ∀ (c : w.adicCompletion D.host.E →+* w.adicCompletion D.host.E) (ϖ : (w.adicCompletion D.host.E)ˣ) (e : Gv A v ≃* GU c A.rank), IsUnramInv (ϖ : w.adicCompletion D.host.E) c (qV D.host.F v) → IsInertChart D.sp.cm.sig A.gram L h c e → GlobalTheory.IndefiniteRowSideFullHecke.SphericalSectionVariables.IsUnr (locChar χ⁻¹ w) ∧ locChar χ⁻¹ w ϖ = (GlobalTheory.LFun.val χ w)⁻¹ ∧ ((locChar χ⁻¹ w ϖ : ℂˣ) : ℂ) = (-1) ^ b ∧ ∃ Φ, GlobalTheory.IndefiniteRowSideFullHecke.SphericalSectionVariables.IsSphSec c (qV D.host.F v) A.rank (locChar χ⁻¹ w) s Φ ∧ ∀ y, φ (ioAt A v y) = Φ (GlobalTheory.IndefiniteRowSideFullHecke.SphericalSectionVariables.io1 c A.rank (e y)) := by
  intro D A L hL χ b hχ v w h hw hu s φ hφ c ϖ e hU he
  have h2 : locChar χ⁻¹ w ϖ = (GlobalTheory.LFun.val χ w)⁻¹ :=
    (hu.inv.locChar_eq_val hU.2.2.2.1).trans (GlobalTheory.LFun.val_inv χ w)
  have hq : qV D.host.F v ≠ 0 := by have := hU.2.2.2.2.2.1; omega
  refine ⟨hu.inv, h2, ?_, exists_isSphSec (isCMExt_host D) (isHermND_gram A) (gram_hdbl A) L hL.1 χ⁻¹ h hw hq
    hφ.1 hφ.2.1 hφ.2.2 he⟩
  rw [h2, ((GlobalTheory.LFun.resEta_iff χ b).1 hχ).val_of_isInertAt (isCMExt_host D).2.2.1 hw hu, ← inv_pow, inv_neg_one]
  simp

end GlobalTheory.KerInert
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsOpenPrincipalCongruenceFinitelyManyPrimes
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace ComplexConjugate
open GlobalTheory.ChainOnto
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.ChainOnto.LevelOpen

theorem exists_open_princ : ∀ (D : D7) (V : HSp D) (β : GL (Fin V.rank) (Lev.EAf D)) (Z : Finset (Pl D.host.E)), ∃ U : Subgroup (GA D V), IsOpen (U : Set (GA D V)) ∧ ∀ k ∈ U, Lev.finE V k ∈ Formalism.L2.DIV.St β ∧ ∀ PP ∈ Z, Formalism.L2.DIV.redFn β PP (Lev.finE V k) = 1 := by
  intro D V β Z
  have hOpen : IsOpen (((Kg D.sp.cm V.gram β Z).comap (Lev.finE V) : Subgroup (GA D V)) : Set (GA D V)) := by
    have := Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.Unfold.topGroupHA D.sp.cm.sig V.gram
    set N : ℕ := ∏ PP ∈ Z, Ideal.absNorm PP.asIdeal with hN
    have hN0 : 0 < N := Finset.prod_pos fun PP _ => Nat.pos_of_ne_zero (by
      rw [Ne, Ideal.absNorm_eq_zero_iff]; exact PP.ne_bot)
    have hNm : ∀ PP ∈ Z, ((N : ℕ) : 𝓞 D.host.E) ∈ PP.asIdeal := fun PP hP => by
      obtain ⟨c, hc⟩ := Finset.dvd_prod_of_mem (fun PP : Pl D.host.E => Ideal.absNorm PP.asIdeal) hP
      rw [hN, hc, Nat.cast_mul]
      exact Ideal.mul_mem_right _ _ (Ideal.absNorm_mem _)
    let P : GA D V → Prop := fun k => ∀ i j, ∃ s ∈ Formalism.L2.Herm.intAf D.host.F D.host.E,
      (β⁻¹ * Lev.finE V k * β).1 i j - (1 : Matrix (Fin V.rank) (Fin V.rank) (Formalism.IndefR.Lev.EAf D)) i j = N • s
    have hP : ∀ᶠ k in nhds (1 : GA D V), P k := by
      have hc := (GlobalTheory.Member.continuous_finHom_val D V).tendsto 1
      rw [map_one, Units.val_one] at hc
      exact hc.eventually (GlobalTheory.DefiniteEnd.eventually_cong β N hN0)
    have hP' : ∀ᶠ k in nhds (1 : GA D V), P k⁻¹ := by
      have : Filter.Tendsto (fun k : GA D V => k⁻¹) (nhds 1) (nhds 1) := by
        simpa using (continuous_inv (G := GA D V)).tendsto 1
      exact this.eventually hP
    refine Subgroup.isOpen_of_mem_nhds _ (g := 1) (Filter.mem_of_superset (hP.and hP') ?_)
    rintro k ⟨h1, h2⟩
    obtain ⟨y, hy, hred⟩ := GlobalTheory.DefiniteEnd.exists_int_of_entries _ (β⁻¹ * Lev.finE V k * β) N h1 (by
      rw [show (β⁻¹ * Lev.finE V k * β)⁻¹ = β⁻¹ * Lev.finE V k⁻¹ * β by rw [map_inv]; group]; exact h2)
    have hy' : frGL β y = Lev.finE V k := by
      show β * Formalism.UG.bc _ y * β⁻¹ = _
      rw [hy]; group
    have hSt : Lev.finE V k ∈ St β := ⟨y, hy'⟩
    refine ⟨⟨GlobalTheory.PrincInLevel.swap_mem_UPts _ _ _ (GlobalTheory.UnitarySplit.finHom_mem V k), hSt⟩, ?_⟩
    refine Subgroup.mem_iInf.2 fun PP => Subgroup.mem_iInf.2 fun hP => mem_princAt.2 ⟨hSt, ?_⟩
    rw [← hy', redFn_frGL]
    refine hred _ _ ?_
    rw [← map_natCast (Ideal.Quotient.mk PP.asIdeal)]
    exact Ideal.Quotient.eq_zero_iff_mem.2 (hNm PP hP)
  
  refine ⟨_, hOpen, fun k hk => ?_⟩
  have hk' : Lev.finE V k ∈ Kg D.sp.cm V.gram β Z := hk
  have h1 : Lev.finE V k ∈ ⨅ PP ∈ Z, princAt β PP := hk'.2
  refine ⟨hk'.1.2, fun PP hP => ?_⟩
  exact (mem_princAt.1 (Subgroup.mem_iInf.1 (Subgroup.mem_iInf.1 h1 PP) hP)).2

end GlobalTheory.ChainOnto.LevelOpen
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsTwistIndexRepresentativeOfBoundsStatement
section
open NumberField IsDedekindDomain MeasureTheory ValuativeRel Matrix Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV Formalism.L2.Col GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.TwBridge
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_twistIndex_representative_of_bounds : ∀ (X : Fields) (Pr : Primes X) (R : Ranks) (Ch : Chars X Pr R.m) (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) (S₀ : Set ℕ) (mu : Tup X.F X.E X.K S₀) (cst : LocCst X (rowSG Pr sel mu)) (σ₀ : X.K →+* ℂ) (P : rowSG Pr sel mu) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (ι : X.E →+* k) (s : ℕ) (W : TwData k) [MeasurableSpace k] [BorelSpace k] (ν : Measure k), IsUnitVol ν → cst.Ok → AtTwist (R := R) sel mu cst σ₀ P ι s W → ∀ (L : ChIdx X Pr R (QE sel (mu : Chr X.F X.E X.K))) (G : ChGlob X R.m), L.Ok Ch sel mu cst G s → IdxProd sel mu cst L → ∀ j c (h : j + 1 + c = s) (γ : AutY X R (j + 1)), (∀ x ∈ lamYat (Pr := Pr) (R := R) (j + 1) P.1, γ⁻¹ x ∈ lamYat (Pr := Pr) (R := R) (j + 1) P.1 ∧ ((qOf P.1 : X.E) ^ (j + 1)) • γ x ∈ lamYat (Pr := Pr) (R := R) (j + 1) P.1) → (∃ al : L.β j, FiniteSumNonzeroLargeDepth Ch sel mu cst j P (L.h j al P) γ) → Nonempty (L.β (j + 1)) → ∃ b : L.β (j + 1), SameDC (Pr := Pr) cst.sharp (j + 1) P.1 (L.h (j + 1) b P) γ := by
  first | exact @GlobalTheory.MRepsPick.exists_rep_of_bounds | exact GlobalTheory.MRepsPick.exists_rep_of_bounds | (intros; apply GlobalTheory.MRepsPick.exists_rep_of_bounds <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsWeilDatumHermitianSpaceDoubled
section
open scoped ComplexConjugate Matrix NNReal
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.Cusp GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (FinPl RealMat Lat IsFockVec IsSphOff HidaSetting volQ)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (ip delta swSec sZero IsKFinVec ThetaClause SectionClause CoefClause)
open GlobalTheory.Mem.Th (CptF)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Core.Rk.IP

namespace GlobalTheory.Core.Rk

theorem exists_doubled_weilDatum : GlobalTheory.Published.WeilRepresentationUnitaryPair → ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (A B : HSp D) (χA χB : (AE D)ˣ →* Circle) (om : WRep A B), IsWeilDatumO ψ A B χA χB om → ∃ omh : WRep (dblSp A) B, IsWeilDatumO ψ (dblSp A) B 1 χB omh := by
  intro H D ψ A B χA χB om h
  have h0 : ResEta D 1 0 := by
    have h1 := resEta_parity (m := 0) (resEta_mul h.resS (resEta_inv h.resS)) (by omega)
    rwa [show χA * χA⁻¹ = 1 from mul_inv_cancel χA] at h1
  have h2 : IsHeckeChar D 1 := ⟨continuous_const, fun _ => rfl⟩
  exact H D ψ (dblSp A) B 1 χB h.1 h2 h.3 (resEta_parity h0 (by change 0 % 2 = (A.rank + A.rank) % 2; omega)) h.resT

end GlobalTheory.Core.Rk
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FirstStepCompletionRepresentativesEqOneStatement
section
open NumberField IsDedekindDomain MeasureTheory ValuativeRel Matrix Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV Formalism.L2.Col GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.TwBridge
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.firstStep_completionRepresentatives_eq_one : ∀ (X : Fields) (Pr : Primes X) (R : Ranks) (Ch : Chars X Pr R.m) (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) (S₀ : Set ℕ) (mu : Tup X.F X.E X.K S₀) (cst : LocCst X (rowSG Pr sel mu)) (σ₀ : X.K →+* ℂ) (P : rowSG Pr sel mu) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (ι : X.E →+* k) (s : ℕ) (W : TwData k) [MeasurableSpace k] [BorelSpace k] (ν : Measure k), IsUnitVol ν → cst.Ok → AtTwist (R := R) sel mu cst σ₀ P ι s W → ∀ (L : ChIdx X Pr R (QE sel (mu : Chr X.F X.E X.K))) (G : ChGlob X R.m), L.Ok Ch sel mu cst G s → IdxProd sel mu cst L → ∀ c (h : 0 + c = s), {g : GL (XIx (Fin R.k) (Fin R.t) (0) ⊕ Fin (c + 1)) k | ∃ b : L.β 0, IsGL ι (L.h 0 b P) g} = {1} := by
  first | exact @GlobalTheory.TwBridge.ZeroReps.reps_zero | exact GlobalTheory.TwBridge.ZeroReps.reps_zero | (intros; apply GlobalTheory.TwBridge.ZeroReps.reps_zero <;> assumption)
end

