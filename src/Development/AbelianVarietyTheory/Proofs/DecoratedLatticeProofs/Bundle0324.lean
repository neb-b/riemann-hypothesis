module

public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0020
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.StepLocGenPinnedGP
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerVolume.InVolumesAtOfSWS
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.Bundle0075
public import Development.AbelianVarietyTheory.Statements.CuspFrameWeights.StepAnalyticConstantsP
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.Bundle0098
public import Mathlib
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.BDataOf
public import Formalism.LocalRingCardinality.Bundle0003
public import Development.AbelianVarietyTheory.Definitions.Jets.SideFam
public import Formalism.SharpRestriction.CuspSpanNormBounds.WeightedUniformRotatedOfExpansion
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.GammaRangeOfSizeHypotheses
public import Formalism.SharpRestriction.CuspSpanNormBounds.ThresholdCubicInequalitySignPattern
public import Formalism.LocalToGlobal.Columns.FiniteSumNonzeroLargeDepth
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0062
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.MemParahoricOfTrivialReduction
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.PhiMapsAndOmegaLaw
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0251
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.XiAtCongInvariant
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0134
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsCombAt
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0018
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.MemHomLatticeCompletionIffSupportedMaps
public import Development.AbelianVarietyTheory.BlockTheory.SiegelEisenstein.DoubledUnramifiedFrames
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SplitPlaceLocalGroupElementsJacobiBessel
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ThetaInnerFockProductEqProdRealPlaces
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DiagonalBlockDetBlockTriangular
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0299
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SplitPlaceBaseVacuumDatumExistsUnique
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0009
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0291
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0305

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.OneOnSingletonOfRows
section
open scoped Classical
open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.TermOp Formalism.L2.SG.Full Formalism.FourierDecayAlt Formalism.L2.SG.RowsConc Formalism.L2.SG.NGData Formalism.L2.SG.NGCut Formalism.L2.SG.NGAnalytic Formalism.L2.SG.TermLoc Formalism.L2.SG.NGLocModel Formalism.L2.SG.Pf.MainEqCut Formalism.L2.SG.Pf.MainEqSteps Formalism.L2.SG.Pf.MainEqAna Formalism.L2.SG.Pf.MainEqLoc Formalism.L2.SG.Pf.MainEqFam GlobalTheory.SnFam GlobalTheory.Core.One
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.Core.Diag

theorem mR_eq_m (D : D7) : Formalism.L2.SG.RowsConc.mR D = (D.R.m : ℝ) := by
  have h : 2 * D.R.rS + 2 = D.R.m := by
    obtain ⟨j, hj⟩ := D.R.m_even
    have := D.R.two_le_m
    unfold Formalism.BasicNotions.Ranks.rS
    omega
  unfold Formalism.L2.SG.RowsConc.mR
  rw [h]

theorem log_b_eq (D : D7) (large₂ : SizeData₂ D) : Real.log large₂.sc.b = large₂.sc.L := by
  unfold Formalism.BasicNotions.Scale.b
  exact Real.log_exp _

theorem gamB_eq_gamL (D : D7) (large₂ : SizeData₂ D) (C : ℝ) : gamB D large₂ C = gamL D large₂.sc.L C := by
  unfold gamB gamL
  rw [mR_eq_m, log_b_eq]

theorem epsNG_le_gamL (D : D7) (large₂ : SizeData₂ D) (C : ℝ) : epsNG D large₂ C ≤ gamL D large₂.sc.L C := by
  unfold epsNG
  have h1 : ((2 : ℝ) ^ (D.R.k - 2 * D.R.rS - 5))⁻¹ ≤ 1 :=
    inv_le_one_of_one_le₀ (one_le_pow₀ (by norm_num))
  have h2 : Real.exp (C * Formalism.L2.SG.RowsConc.mR D ^ 5 * D.R.f * Real.log large₂.sc.b) = gamL D large₂.sc.L C := by
    unfold gamL
    rw [mR_eq_m, log_b_eq]
  rw [h2]
  exact mul_le_of_le_one_left (Real.exp_pos _).le h1

theorem oneOn_singleton_of_rows :
    (RowGen1P → ∀ c : ℝ, GlobalTheory.Core.Diag.OneOn {c} true) ∧ (GlobalTheory.NGRow.RowNGP → ∀ c : ℝ, GlobalTheory.Core.Diag.OneOn {c} false) := by
  constructor
  · intro hG c Cg cb Cu cT CT hcb hcT
    obtain ⟨CB, hCB, C'₀, Cl₀, H⟩ := hG Cg cb Cu cT CT c hcb hcT
    refine ⟨CB, hCB, max (max C'₀ Cl₀) 3, ?_⟩
    intro C0 hC0 C' Cl h1 h2 D large₂ X Y u hT hH hC ha
    rw [Set.mem_singleton_iff] at hC0
    subst hC0
    have a1 : C'₀ ≤ C' := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) h1
    have b1 : Cl₀ ≤ Cl := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) h2
    have b3 : (2 : ℝ) < Cl := lt_of_lt_of_le (by norm_num) (le_trans (le_max_right _ _) h2)
    have hs : Formalism.MainNotions.S.Cnt.Stand D u u := Formalism.MainNotions.Stand_of D large₂ C' Cl Cg cb Cu cT CT C0 hH.2.1 hH.1 b3 u u
    have r := H C' Cl a1 b1 D large₂ X Y u hT hH hs hC ha
    unfold GeneratorBoundAt at r
    rw [gamB_eq_gamL] at r
    rw [if_pos rfl]
    exact r
  · intro hN c Cg cb Cu cT CT hcb hcT
    obtain ⟨C4, hC4, C'₀, Cl₀, H⟩ := hN Cg cb Cu cT CT c hcb hcT
    refine ⟨C4, hC4, max (max C'₀ Cl₀) 3, ?_⟩
    intro C0 hC0 C' Cl h1 h2 D large₂ X Y u hT hH hC ha
    rw [Set.mem_singleton_iff] at hC0
    subst hC0
    have a1 : C'₀ ≤ C' := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) h1
    have b1 : Cl₀ ≤ Cl := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) h2
    have b3 : (2 : ℝ) < Cl := lt_of_lt_of_le (by norm_num) (le_trans (le_max_right _ _) h2)
    have hs : Formalism.MainNotions.S.Cnt.Stand D u u := Formalism.MainNotions.Stand_of D large₂ C' Cl Cg cb Cu cT CT C0 hH.2.1 hH.1 b3 u u
    have r : (Y.tO u u).pairSum ((Y.tO u u).one (Y.tO u u).ngSet) ≤ epsNG D large₂ C4 * ddC X Y u u :=
      H C' Cl a1 b1 D large₂ X Y u u hT hH hs hC ha
    rw [if_neg Bool.false_ne_true]
    exact r.trans (mul_le_mul_of_nonneg_right (epsNG_le_gamL D large₂ C4) (Formalism.L2.SG.RowsConc.dd_nonneg hC u u))

end GlobalTheory.Core.Diag
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.PenultimateDatumUnchangedFramesCongruentOne
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV Formalism.L2.Col

noncomputable section

namespace GlobalTheory.PenPsiInv

open GlobalTheory.CongLevel

section Ext

variable {E : Type} [Field E]

theorem resX_extE {n : ℕ} (c : ℕ) (κ : (Fin n → E) ≃ₗ[E] (Fin n → E)) (v : Fin (n + c) → E) :
    resX c (extE c κ v) = κ (resX c v) := by
  rw [extE_apply, map_add (f := _), resX_inX]
  abel

theorem atNL_inX {n : ℕ} (c : ℕ) (w : Fin n → E) : atNL E (n + c) n (Loc.inX E n c w) = 0 := by
  unfold atNL
  split_ifs with h
  · rw [LinearMap.proj_apply, inX_apply, dite_eq_right (lt_irrefl n)]
  · rfl

theorem atNL_extE {n : ℕ} (c : ℕ) (κ : (Fin n → E) ≃ₗ[E] (Fin n → E)) (v : Fin (n + c) → E) :
    atNL E (n + c) n (extE c κ v) = atNL E (n + c) n v := by
  rw [extE_apply, map_add (f := _), atNL_inX, add_zero]

theorem joinCol_inFr {n' c' n c : ℕ} (f : Sp E n' ≃ₗ[E] Sp E n') (f' : Sp E n ≃ₗ[E] Sp E n) (x : HomE E n' n)
    (y : Sp E n) :
    joinCol (c' := c') (c := c) (inFr f f' x) (f'.symm y) =
      (extE c f'.symm).toLinearMap ∘ₗ joinCol (c' := c') (c := c) x y ∘ₗ (extE c' f).toLinearMap := by
  apply LinearMap.ext
  intro v
  simp only [joinCol, LinearMap.comp_apply, LinearEquiv.coe_coe, LinearMap.add_apply, LinearMap.smulRight_apply]
  rw [extE_inX]
  congr 1
  have h1 : LinearMap.funLeft E E (Fin.castAdd c') (extE c' f v) = f (LinearMap.funLeft E E (Fin.castAdd c') v) :=
    resX_extE c' f v
  rw [h1, atNL_extE, map_add (f := _), map_smul]
  rfl

end Ext

section Main

variable {X : Fields} {Pr : Primes X} {R : Ranks} (Ch : Chars X Pr R.m)
  (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) {S₀ : Set ℕ}
  (mu : Tup X.F X.E X.K S₀) (cst : LocCst X (rowSG Pr sel mu)) (P : rowSG Pr sel mu)

theorem extE_mem_Jat (sharp : Bool) (j : ℕ) (w : HeightOneSpectrum (𝓞 X.E)) (hw : w ∈ Pr.vGs)
    (hd : ∀ a : X.E, IntAt w a → redP w a = 0 → IntAt w (a / (qOf w : X.E)))
    (κ : Sp X.E (R.N j) ≃ₗ[X.E] Sp X.E (R.N j)) (hκ : κ ∈ GLint X.E (R.N j) w)
    (hr : ∀ x ∈ stdAt X.E (R.N j) w, redV w (κ x) = redV w x) :
    extE (cOf R j) κ ∈ Jat (Pr := Pr) sharp j w := by
  have h := (Subgroup.mem_inf.1
    (GlobalTheory.Mem.Col2.LevMod.extE_mem_Cbe (Pr := Pr) sharp j w hw hd 1 (one_mem _) κ hκ hr)).2
  rw [Subgroup.mem_comap, inv_one, map_one] at h
  exact h

theorem lamRow_extE (sharp : Bool) (j : ℕ) (w : HeightOneSpectrum (𝓞 X.E)) (hw : w ∈ Pr.vGs)
    (hd : ∀ a : X.E, IntAt w a → redP w a = 0 → IntAt w (a / (qOf w : X.E)))
    (κ : Sp X.E (R.N j) ≃ₗ[X.E] Sp X.E (R.N j)) (hκ : κ ∈ GLint X.E (R.N j) w)
    (hr : ∀ x ∈ stdAt X.E (R.N j) w, redV w (κ x) = redV w x) :
    lamRow Ch mu sharp j w (extE (cOf R j) κ).toLinearMap = 1 := by
  have hq : ((qOf w : ℕ) : X.E) ≠ 0 := by
    rw [Nat.cast_ne_zero]
    exact fun h0 => w.ne_bot (Ideal.absNorm_eq_zero_iff.1 h0)
  have e : (extE (cOf R j) κ).toLinearMap = LinearMap.id + ((qOf w : ℕ) : X.E) •
      (((qOf w : ℕ) : X.E)⁻¹ • ((extE (cOf R j) κ).toLinearMap - LinearMap.id)) := by
    rw [smul_inv_smul₀ hq, add_sub_cancel]
  rw [e]
  refine GlobalTheory.LamRowCong.lamRow_one_add_q Ch mu sharp j w hw _ fun v hv => ?_
  unfold lamYat at hv ⊢
  rw [if_pos hw] at hv ⊢
  exact extE_cong w (qOf w) (cOf R j) (fun i => i + 1) hd κ hκ hr v hv

theorem muAt_det_extE (i : ℕ) {n : ℕ} (c : ℕ)
    (hd : ∀ a : X.E, IntAt P.1 a → redP P.1 a = 0 → IntAt P.1 (a / (qOf P.1 : X.E)))
    (κ : Sp X.E n ≃ₗ[X.E] Sp X.E n) (hκ : κ ∈ GLint X.E n P.1)
    (hr : ∀ x ∈ stdAt X.E n P.1, redV P.1 (κ x) = redV P.1 x) :
    muAt Ch sel mu cst i P ((LinearEquiv.det (extE c κ) : X.Eˣ) : X.E) = 1 := by
  refine GlobalTheory.TwU.MidIndep.muAt_det_cong Ch sel mu cst i P (n + c) 1 le_rfl _ fun v hv => ?_
  rw [pow_one]
  rw [GlobalTheory.DatumLaw.stdAt_eq] at hv ⊢
  exact extE_cong P.1 (qOf P.1) c 0 hd κ hκ hr v hv

end Main

theorem psiAt_one_inFr : ∀ {X : Formalism.L2.Col.Fields} {Pr : Formalism.L2.Col.Primes X} {R : Formalism.BasicNotions.Ranks} (Ch : Formalism.L2.Col.Chars X Pr R.m) (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) {S₀ : Set ℕ} (mu : Formalism.L2.DIV.Tup X.F X.E X.K S₀) (cst : Formalism.L2.Col.LocCst X (Formalism.L2.Col.rowSG Pr sel mu)) (s : ℕ) (P : Formalism.L2.Col.rowSG Pr sel mu), P.1 ∈ Pr.vGs → R.m = s + 2 → (∀ a : X.E, Formalism.L2.Col.IntAt P.1 a → Formalism.L2.Col.redP P.1 a = 0 → Formalism.L2.Col.IntAt P.1 (a / (Formalism.L2.Col.qOf P.1 : X.E))) → ∀ (f : Formalism.L2.Col.Sp X.E (R.N s) ≃ₗ[X.E] Formalism.L2.Col.Sp X.E (R.N s)) (f' : Formalism.L2.Col.Sp X.E (R.N (s + 1)) ≃ₗ[X.E] Formalism.L2.Col.Sp X.E (R.N (s + 1))), f ∈ Formalism.L2.Col.GLint X.E (R.N s) P.1 → (∀ x ∈ Formalism.L2.Col.stdAt X.E (R.N s) P.1, Formalism.L2.Col.redV P.1 (f x) = Formalism.L2.Col.redV P.1 x) → f' ∈ Formalism.L2.Col.GLint X.E (R.N (s + 1)) P.1 → (∀ x ∈ Formalism.L2.Col.stdAt X.E (R.N (s + 1)) P.1, Formalism.L2.Col.redV P.1 (f' x) = Formalism.L2.Col.redV P.1 x) → ∀ (x : Formalism.L2.Col.HomE X.E (R.N s) (R.N (s + 1))) (y : Formalism.L2.Col.Sp X.E (R.N (s + 1))), Formalism.L2.Col.PsiAt Ch sel mu cst s P 1 (Formalism.L2.Col.inFr f f' x) (f'.symm y) = Formalism.L2.Col.PsiAt Ch sel mu cst s P 1 x y := by
  intro X Pr R Ch sel S₀ mu cst s P hP hm hd f f' hf hr hf' hr' x y
  have hi : s + 2 ≤ R.m := hm.ge
  have hg : f'.symm ∈ GLint X.E (R.N (s + 1)) P.1 := inv_mem hf'
  have hgr : ∀ v ∈ stdAt X.E (R.N (s + 1)) P.1, redV P.1 (f'.symm v) = redV P.1 v := fun v hv => by
    have h := hr' _ ((hg v).2 hv)
    rw [LinearEquiv.apply_symm_apply] at h
    exact h.symm
  have h1 := GlobalTheory.DatumLaw.phiAt_target Ch sel mu cst cst.sharp hi P (extE_mem_Jat cst.sharp (s + 1) P.1 hP hd _ hg hgr)
    (joinCol x y ∘ₗ (extE (cOf R s) f).toLinearMap)
  have h2 := GlobalTheory.DatumLaw.phiAt_source Ch sel mu cst cst.sharp hi P (extE_mem_Jat cst.sharp s P.1 hP hd _ hf hr) (joinCol x y)
  rw [muAt_det_extE Ch sel mu cst P s _ hd _ hg hgr, lamRow_extE Ch mu cst.sharp (s + 1) P.1 hP hd _ hg hgr, mul_one, one_mul] at h1
  rw [muAt_det_extE Ch sel mu cst P s _ hd _ hf hr, lamRow_extE Ch mu cst.sharp s P.1 hP hd _ hf hr, mul_one, one_mul] at h2
  unfold PsiAt
  rw [GlobalTheory.SymBridge.PsiStep.omPhi_one_one, GlobalTheory.SymBridge.PsiStep.omPhi_one_one, joinCol_inFr, h1, h2]

end GlobalTheory.PenPsiInv
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.PlaceIdemMemIdAt
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory Matrix ValuativeRel
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.FinPl
open IsDedekindDomain NumberField
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.PlaceIdemFacts

variable {D : D7}

theorem cA_cA (z : AE D) : cA D (cA D z) = z := by
  induction z using TensorProduct.induction_on with
  | zero => rw [RingHom.map_zero, RingHom.map_zero]
  | add x y hx hy => rw [RingHom.map_add (f := _), RingHom.map_add (f := _), hx, hy]
  | tmul a x =>
    change a ⊗ₜ[D.host.F] star (star x) = _
    rw [star_star]

theorem algebraMap_pairA (α : Af D.host.F) :
    algebraMap (AF D.host.F) (AE D) (pairA D.host.F 0 α) = pairA D.host.F 0 α ⊗ₜ[D.host.F] (1 : D.host.E) := rfl

theorem placeIdem_mem_idAt {v : Pl D} {ε : AF D.host.F} (hε : IsPlaceIdem D v ε) {P : Pl D → Prop} (hP : P v) :
    algebraMap (AF D.host.F) (AE D) ε ∈ idAt D P := by
  obtain ⟨α, rfl, -, h0⟩ := hε
  rw [algebraMap_pairA]
  exact GlobalTheory.FinPl.LatMem.tmul_mem_idAt (fun w hw => h0 w fun h => hw (h ▸ hP)) 1

theorem infPart_placeIdem {v : Pl D} {ε : AF D.host.F} (hε : IsPlaceIdem D v ε) :
    infPart D (algebraMap (AF D.host.F) (AE D) ε) = 0 := by
  obtain ⟨α, rfl, -, -⟩ := hε
  exact TensorProduct.zero_tmul _ _

theorem placeIdem_mul {v v' : Pl D} {ε ε' : AF D.host.F} (hε : IsPlaceIdem D v ε) (hε' : IsPlaceIdem D v' ε')
    (h : v ≠ v') : ε * ε' = 0 := by
  obtain ⟨α, rfl, -, h0⟩ := hε
  obtain ⟨α', rfl, -, h0'⟩ := hε'
  have hαα : α * α' = 0 := by
    apply RestrictedProduct.ext
    intro w
    change evalV D.host.F w (α * α') = evalV D.host.F w 0
    rw [map_mul, map_zero]
    by_cases hw : w = v
    · subst hw
      rw [h0' w h, mul_zero]
    · rw [h0 w hw, zero_mul]
  show ((0 : Ainf D.host.F), α) * ((0 : Ainf D.host.F), α') = 0
  rw [Prod.mk_mul_mk, mul_zero, hαα]
  rfl

theorem idem_facts : ∀ (D : D7) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (q : SplitPt D k), cA D (q.e + cA D q.e) = q.e + cA D q.e ∧
      (∀ (P : Pl D → Prop), P q.v → ∀ (m n : ℕ) (w : Mx D m n), IsHalf (q.e + cA D q.e) w →
        MxAt P w ∧ w.map (infPart D) = 0) ∧
      ∀ (k' : Type) [Field k'] [ValuativeRel k'] [TopologicalSpace k'] [IsNonarchimedeanLocalField k'] (q' : SplitPt D k'),
        q.v ≠ q'.v → (q.e + cA D q.e) * (q'.e + cA D q'.e) = 0 := by
  intro D k _ _ _ _ q
  obtain ⟨ε, hε, heq⟩ := q.above
  refine ⟨by rw [map_add (f := _), cA_cA, add_comm], fun P hP m n w hw => ⟨fun i j => ?_, ?_⟩,
    fun k' _ _ _ _ q' hv => ?_⟩
  · rw [← hw i j, heq]
    exact Ideal.mul_mem_right _ _ (placeIdem_mem_idAt hε hP)
  · ext i j
    rw [Matrix.map_apply, Matrix.zero_apply, ← hw i j, map_mul, heq, infPart_placeIdem hε, zero_mul]
  · obtain ⟨ε', hε', heq'⟩ := q'.above
    rw [heq, heq', ← map_mul, placeIdem_mul hε hε' hv, map_zero]

end GlobalTheory.PlaceIdemFacts

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.PureTensorOPerm
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.FinPl ValuativeRel IsLocalRing
open GlobalTheory.LatPair GlobalTheory.SplitWeil
open GlobalTheory.StepData (XIx Ix latOf box LatFrame)
open GlobalTheory.LocMod (GAt PinGBy ofSplit MovedTo)
open GlobalTheory.IndefiniteRowSideFullHecke.UnramifiedCharacter (CharUnramAt)
open GlobalTheory.IndefiniteRowSideFullHecke.AppendedVectorData (lastPair lastKer)
open GlobalTheory.IndefiniteRowSideFullHecke.UnramifiedLocalFrameSequences (IsFockOver StepsAll vec atW IsMoved InAt InvOnUnits IsBesFrame IsJacFrame FrameMapsPrefix jacLat ptBF ptFB)
open scoped TensorProduct Pointwise
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.FockOrder

variable {D : D7}

theorem exists_sortPerm {n : ℕ} (ε : Fin n → Bool) :
    ∃ π : Equiv.Perm (Fin n), ∀ a, ε (π a) = decide (a.val < (Finset.univ.filter fun a => ε a = true).card) := by
  classical
  set p := (Finset.univ.filter fun a => ε a = true).card with hp
  set q := (Finset.univ.filter fun a => ¬ ε a = true).card with hq
  have hpq : p + q = n := by
    rw [hp, hq, Finset.card_filter_add_card_filter_not]; simp
  have e1 : {a // ε a = true} ≃ Fin p := Fintype.equivFinOfCardEq (by rw [Fintype.card_subtype])
  have e2 : {a // ¬ ε a = true} ≃ Fin q := Fintype.equivFinOfCardEq (by rw [Fintype.card_subtype])
  refine ⟨(finCongr hpq.symm).trans (finSumFinEquiv.symm.trans ((Equiv.sumCongr e1.symm e2.symm).trans
    (Equiv.sumCompl _))), fun a => ?_⟩
  by_cases ha : a.val < p
  · have h : finCongr hpq.symm a = Fin.castAdd q ⟨a.val, ha⟩ := Fin.ext rfl
    simp only [Equiv.trans_apply, h, finSumFinEquiv_symm_apply_castAdd, Equiv.sumCongr_apply, Sum.map_inl,
      Equiv.sumCompl_apply_inl]
    rw [(e1.symm _).2]; simp [ha]
  · have h : finCongr hpq.symm a = Fin.natAdd p ⟨a.val - p, by omega⟩ := Fin.ext (by simp; omega)
    simp only [Equiv.trans_apply, h, finSumFinEquiv_symm_apply_natAdd, Equiv.sumCongr_apply, Sum.map_inr,
      Equiv.sumCompl_apply_inr]
    have h2 := (e2.symm ⟨a.val - p, by omega⟩).2
    simp only [Bool.not_eq_true] at h2
    rw [h2]; simp [ha]

variable {V : HSp D} {S : D.what₂.Tau → SPar}

section Main

variable {ψ : AddChar (AF D.host.F) ℂ} {θ : InfFam D} {V W : HSp D} {S S' : D.what₂.Tau → SPar}

end Main

end GlobalTheory.FockOrder

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ReducedChainLocalIdentity
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory Matrix ValuativeRel GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.SeeSaw GlobalTheory.LocMod GlobalTheory.StepData NumberField
open scoped Classical

noncomputable section

namespace GlobalTheory.ChainOnto

theorem one_add_idem_mul {R : Type} [CommRing R] {e A B : R} (he : e * e = e) (hAB : A * B = 1) :
    (1 + e * (A - 1)) * (1 + e * (B - 1)) = 1 := by
  linear_combination (A - 1) * (B - 1) * he + e * hAB

theorem one_add_idem_mul_eq {R : Type} [CommRing R] (e A : R) : 1 + e * (A - 1) = e * A + (1 - e) := by ring

theorem locE_mul_inv (D : D7) {e : AE D} (he : e * e = e) {z : D.host.E} (hz : z ≠ 0) :
    Formalism.L2.JoinChr.locE D e z * Formalism.L2.JoinChr.locE D e z⁻¹ = 1 := by
  have h3 : incA D z * incA D z⁻¹ = 1 := by rw [← map_mul, mul_inv_cancel₀ hz, map_one]
  exact one_add_idem_mul he h3

theorem locE_eq (D : D7) (e : AE D) (z : D.host.E) : Formalism.L2.JoinChr.locE D e z = e * incA D z + (1 - e) :=
  one_add_idem_mul_eq _ _


open GlobalTheory.ChiGrid GlobalTheory.SplitFlip GlobalTheory.StdFrames Formalism.L2.Host Formalism.L2.DIV in
set_option maxHeartbeats 2000000 in
theorem chi_compat_of_isComp : ∀ (D : D7) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (q : GlobalTheory.FinPl.SplitPt D k) (PP : Formalism.L2.DIV.Pl D.host.E), Formalism.L2.NTheta.IsIdemAt q.e PP → ∀ π' : EAf D →+* k, (∀ a, π' (toEAf D a) = q.pr a) → GlobalTheory.FunObj.Comparison₂.IsRed (Formalism.L2.DIV.resS D.host.F PP) (π'.comp (Formalism.L2.Herm.intAf D.host.F D.host.E).subtype) → ∀ c : GlobalTheory.ChainOnto.Com D, c.Is → PP ∈ c.Pg → ∀ j : ℕ, 1 ≤ j → j ≤ D.R.m → ∀ μ : kˣ →* ℂˣ, IsTame μ → (ofSplit q).IsComp (c.chS j)⁻¹ μ → GlobalTheory.FunObj.Comparison₂.Compat (Formalism.L2.DIV.resS D.host.F PP) (π'.comp (Formalism.L2.Herm.intAf D.host.F D.host.E).subtype) (c.chi j PP) μ := by
  intro D k _ _ _ _ q PP hI π' hπ hR c hc hP j hj1 hj2 μ hμ hC
  intro s u x hu hx
  obtain ⟨a, ha⟩ := Ideal.Quotient.mk_surjective (u : Formalism.L2.DIV.kP PP)
  have hoa : ((Formalism.L2.DIV.oToS D.host.F D.host.E a : Formalism.L2.Herm.intAf D.host.F D.host.E) : EAf D) =
      toEAf D (incA D (a : D.host.E)) := rfl
  have hψa : (π'.comp (Formalism.L2.Herm.intAf D.host.F D.host.E).subtype) (Formalism.L2.DIV.oToS D.host.F D.host.E a) =
      q.pr (incA D (a : D.host.E)) := by
    rw [RingHom.comp_apply, Subring.coe_subtype, hoa, hπ]
  have hres : Formalism.L2.DIV.resS D.host.F PP (Formalism.L2.DIV.oToS D.host.F D.host.E a) = u := by
    rw [Formalism.L2.DIV.resS_oToS, ha]
  have h1 : valuation k (q.pr (incA D (a : D.host.E))) = 1 := by
    rw [← hψa, ← hR.isUnit_iff, hres]; exact u.isUnit
  have h2 : valuation k ((x : k) - q.pr (incA D (a : D.host.E))) < 1 := by
    rw [← hψa, hx, ← map_sub]
    refine (hR.ker _).1 ?_
    rw [map_sub, hres, ← hu, sub_self]
  have hp0 : q.pr (incA D (a : D.host.E)) ≠ 0 := fun h => by rw [h, map_zero] at h1; exact zero_ne_one h1
  have hμx : μ x = μ (Units.mk0 _ hp0) := by
    have : μ (x * (Units.mk0 _ hp0)⁻¹) = 1 := hμ _ (by
      rw [Units.val_mul, Units.val_inv_eq_inv_val, Units.val_mk0, ← mul_inv_cancel₀ hp0, ← sub_mul, map_mul, map_inv₀, h1,
        inv_one, mul_one]
      exact h2)
    rw [map_mul, map_inv, mul_inv_eq_one] at this; exact this
  have ha0 : (a : D.host.E) ≠ 0 := fun h => by rw [h, map_zero, map_zero] at h1; exact zero_ne_one h1
  have hee : q.e * q.e = q.e := hI.1.1
  let y : (AE D)ˣ := ⟨Formalism.L2.JoinChr.locE D q.e (a : D.host.E), Formalism.L2.JoinChr.locE D q.e (a : D.host.E)⁻¹,
    GlobalTheory.ChainOnto.locE_mul_inv D hee ha0, by rw [mul_comm]; exact GlobalTheory.ChainOnto.locE_mul_inv D hee ha0⟩
  have hyι : (y : AE D) = (ofSplit q).ι ((Units.mk0 _ hp0 : kˣ) : k) + (1 - (ofSplit q).e) := by
    show Formalism.L2.JoinChr.locE D q.e (a : D.host.E) = q.sec (q.pr (incA D (a : D.host.E))) + (1 - q.e)
    rw [q.sec_pr, GlobalTheory.ChainOnto.locE_eq]
  have hcomp := hC _ y hyι
  have hinf : infPart D q.e = 0 := (GlobalTheory.IdemSupport.delta_of_isIdemAt (comp_toAd D) hI).1
  have hint : ∀ z : D.host.E, valuation k (q.pr (incA D z)) = 1 →
      finPart D (Formalism.L2.JoinChr.locE D q.e z) ∈ intAE D := by
    intro z hz
    rw [GlobalTheory.ChainOnto.locE_eq, ← q.sec_pr, map_add, (finPart D).map_sub, (finPart D).map_one]
    refine add_mem ((q.int_iff _).1 ?_) (sub_mem (GlobalTheory.AdIdem.idempotent_mem_intAE D 1 (mul_one 1))
      (GlobalTheory.AdIdem.idempotent_mem_intAE D _ (by rw [← (finPart D).map_mul, hee])))
    exact (Valuation.mem_integer_iff _ _).2 hz.le
  have hinv : q.pr (incA D (a : D.host.E)⁻¹) = (q.pr (incA D (a : D.host.E)))⁻¹ := map_inv₀ (q.pr.comp (incA D)) _
  have hη : c.η y = 1 := hc.chars.2.1 y (by
      show infPart D (Formalism.L2.JoinChr.locE D q.e (a : D.host.E)) = 1
      rw [GlobalTheory.ChainOnto.locE_eq, map_add, (infPart D).map_mul, (infPart D).map_sub, (infPart D).map_one, hinf,
        zero_mul, zero_add, sub_zero])
    (hint _ h1) (hint _ (by rw [hinv, map_inv₀, h1, inv_one]))
  have hS : c.chS j y = c.μ j y := by
    unfold GlobalTheory.ChainOnto.Com.chS Formalism.IndefR.Lift.chrStep
    split_ifs <;> simp [hη]
  obtain ⟨H, hH1, hH2⟩ := hc.res ⟨j - 1, by omega⟩
  have hj : j - 1 + 1 = j := Nat.sub_add_cancel hj1
  dsimp only at hH1 hH2
  rw [hj] at hH1 hH2
  have hIP : Formalism.L2.JoinChr.IsPlIdem D q.e PP := by
    obtain ⟨h1', h2', v, ε, h3', h4'⟩ := hI.1
    exact ⟨h1', ⟨v, ε, h3', Or.inl ⟨h2', h4'⟩⟩, hI.2⟩
  have e1 := hH1.2 PP q.e hIP (Units.mk0 _ ha0) y rfl
  have e2 := hH2 PP hP a (Units.mk0 _ ha0) u rfl ha.symm
  apply Units.ext
  rw [hμx, hcomp, MonoidHom.inv_apply, Circle.coe_inv, hS, e1, ← e2, MonoidHom.inv_apply, Units.val_inv_eq_inv_val, inv_inv]

end GlobalTheory.ChainOnto

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SplitPlaceChangeBaseVacuumHeisenbergCombination
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.FinPl GlobalTheory.MixPer GlobalTheory.MixModel GlobalTheory.Unf GlobalTheory.LatPair GlobalTheory.SplitWeil GlobalTheory.SeeSaw ValuativeRel IsLocalRing

noncomputable section

namespace GlobalTheory.FinPl.Rebase

theorem rebase : ∀ (D : D7) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (p : SplitPt D k) (n n' : Type) [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n'] (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → p.UnitAA → ∀ (S T : HSp D) (α : Frame p S n') (β : Frame p T n) (LS MS : Lat S) (LT MT : Lat T), IsSelfDualC S LS → IsSelfDualC T LT → IsSelfDualC S MS → IsSelfDualC T MT → (∀ (ΛS : Submodule 𝒪[k] (n' → k)) (ΛT : Submodule 𝒪[k] (n → k)), α.IsLat MS ΛS → β.IsLat MT ΛT → ∀ f₀ g, Over ψ α β LS LT f₀ (latInd ΛS ΛT) g → Vac ψ S T MS MT (· = p.v) g ∧ ∀ Ψ f, Over ψ α β LS LT f₀ Ψ f → Over ψ α β MS MT g Ψ f) ∧ ∀ Ψ ∈ SB (Matrix n n' k), ∃ c : WO S T →₀ ℂ, CombAt (· = p.v) c ∧ ∀ f₀, Vac ψ S T LS LT (· = p.v) f₀ → Over ψ α β LS LT f₀ Ψ (comb ψ S T c f₀) := by
  intro D k _ _ _ _ p n n' _ _ _ _ ψ hψ hU S T α β LS MS LT MT hLS hLT hMS hMT
  have hOB := _root_.GlobalTheory.FinPl.overBasic D k p n n' ψ hψ S T α β
  refine ⟨fun ΛS ΛT hΛS hΛT f₀ g hg => ?_, fun Ψ hΨ => ?_⟩
  · obtain ⟨-, -, hvac0, -, ⟨Tm, hTm⟩, hall⟩ := id hg
    have hE := _root_.GlobalTheory.FinPl.LatIndHalf.extFun_latInd_eq_halfInd D k p n n' S T α β MS MT hMS hMT hU ΛS ΛT hΛS hΛT
    have hgT : g = Tm (halfInd p.e (latO S T (MS : Set (Fin S.rank → D.host.E)) (MT : Set (Fin T.rank → D.host.E)) (· = p.v))) := by
      rw [← hE]; exact hall Tm hTm
    have hmono := sbHalf_mono D k p S T LS MS LT MT hLS hLT hMS hMT
    have hTm' : IsPlaceModel ψ (symplO S T) (heisO ψ S T) p.e
        (latO S T (MS : Set (Fin S.rank → D.host.E)) (MT : Set (Fin T.rank → D.host.E)) (· = p.v)) 1 g Tm := by
      refine ⟨fun Φ hΦ x hx => hTm.trans Φ (hmono Φ hΦ) x hx, fun Φ hΦ y hy => hTm.modul Φ (hmono Φ hΦ) y hy, ?_⟩
      rw [one_smul, hgT]
    have hth : IsThetaFunO ψ S T g := ((hOB LS LT hLS hLT f₀ hvac0).2.1 _ g hg).1
    have hvacg : Vac ψ S T MS MT (· = p.v) g := by
      refine ⟨hth, ?_⟩
      rw [hgT]
      exact latVac_image D k p ψ hψ S T LS MS LT MT hLS hLT hMS hMT f₀ Tm hTm
    refine ⟨hvacg, fun Ψ f hf => ?_⟩
    obtain ⟨f', hf', -⟩ := (hOB MS MT hMS hMT g hvacg).1 Ψ hf.2.2.2.1
    have e1 : f' = Tm (extFun α β Ψ) := hf'.2.2.2.2.2 Tm hTm'
    have e2 : f = Tm (extFun α β Ψ) := hf.2.2.2.2.2 Tm hTm
    refine ⟨hMS, hMT, hvacg, hf.2.2.2.1, ⟨Tm, hTm'⟩, fun T' hT' => ?_⟩
    rw [e2, ← e1]
    exact hf'.2.2.2.2.2 T' hT'
  · obtain ⟨c, hc, hcomb⟩ := _root_.GlobalTheory.FinPl.CombProof.extFun_comb D k p n n' ψ hψ S T α β LS LT hLS hLT Ψ hΨ
    refine ⟨c, hc, fun f₀ hvac => ?_⟩
    obtain ⟨f, hf, -⟩ := (hOB LS LT hLS hLT f₀ hvac).1 Ψ hΨ
    exact ⟨hLS, hLT, hvac, hΨ, hf.2.2.2.2.1, fun T' hT' => (hcomb f₀ T' hT').symm⟩

end GlobalTheory.FinPl.Rebase

end
end

