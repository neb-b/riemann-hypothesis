module

public import Mathlib
public import Formalism.LocalToGlobal.IndefiniteReal.LinksW
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsStepWeil
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleDiscreteSeriesOfHasParam
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0442
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0125
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0409
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0395
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.AdmissibleEmptyOfGood
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0670
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1282
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0448
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0135
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0156
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0146
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.LevelHyperspecialTrivialCharacterSplitsOffPlaces
public import Formalism.LocalToGlobal.IndefiniteReal.FinitePlaces.Bundle0011

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PItYOfOne
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.Chain.ItAllTuples

variable {D : D7}

theorem isItW_smul {V W : HSp D} {S S' : D.what₂.Tau → SPar} {θ : InfFam D} {M : DSModel V S} {M' : DSModel W S'}
    {ω : GA D V × GA D W →* Module.End ℂ (WO V W → ℂ)} {pt : PolF D W.rank V.rank → (WO V W → ℂ)}
    {It : PolF D W.rank V.rank →ₗ[ℂ] SmT M' →ₗ[ℂ] SmT M} (h : IsItW θ M M' ω pt It) {c : ℂ} (hc : c ≠ 0) :
    IsItW θ M M' ω pt (c • It) := by
  refine { ne := smul_ne_zero hc h.ne, bdd := ?_, eqK := ?_, eqg := ?_, invK := ?_, invg := ?_ }
  · intro φ w
    obtain ⟨b, hb⟩ := h.bdd φ w
    refine ⟨‖c‖ * b, fun v => ?_⟩
    have e : ellT M w (inclT M ((c • It) φ (PiTensorProduct.tprod ℂ v))) =
        c * ellT M w (inclT M (It φ (PiTensorProduct.tprod ℂ v))) := by
      rw [LinearMap.smul_apply, LinearMap.smul_apply, map_smul, map_smul, smul_eq_mul]
    rw [e, norm_mul, mul_assoc]
    exact mul_le_mul_of_nonneg_left (hb v) (norm_nonneg _)
  · intro τ g hg φ φ' hφ v
    rw [LinearMap.smul_apply, LinearMap.smul_apply, LinearMap.smul_apply, LinearMap.smul_apply, map_smul, map_smul,
      map_smul, h.eqK τ g hg φ φ' hφ v]
  · intro τ X hX φ φ' hφ v w
    have := (h.eqg τ X hX φ φ' hφ v w).const_mul c
    simp only [LinearMap.smul_apply, map_smul, smul_eq_mul]
    exact this
  · intro τ g hg φ φ' v v' hφ hv
    rw [LinearMap.smul_apply, LinearMap.smul_apply, LinearMap.smul_apply, LinearMap.smul_apply,
      h.invK τ g hg φ φ' v v' hφ hv]
  · intro τ X hX φ φ' v v' hφ hv
    rw [LinearMap.smul_apply, LinearMap.smul_apply, LinearMap.smul_apply, LinearMap.smul_apply, ← smul_add,
      h.invg τ X hX φ φ' v v' hφ hv, smul_zero]

theorem pItY_of_one : GlobalTheory.Published.DiscreteSeriesCover → GlobalTheory.Published.HarishChandraModules → ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T : Type) (A : FamIn D.what₂.LL G Pl0 T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks), (∀ k, GlobalTheory.Chain.ChainPar D k) → R.toLevCh.Is A.μ0 → R.IsModels → R.chain_ωY → R.chain_ωX → R.chain_vY → R.chain_vX → ∀ (k : ℕ), k + 1 < D.R.m → ∀ (t₀ : T) (y : PolF D (Yc D (k + 1)).rank (Yc D k).rank →ₗ[ℂ] SmT (R.MY (k + 1)) →ₗ[ℂ] SmT (R.MY k)), IsItW R.θ (R.MY k) (R.MY (k + 1)) (R.ωY t₀ k) (R.ptY t₀ k) y → R.PItY k y := by
  intro h1 h2 D G _ _ Pl0 T A Ks _ _ _ R hC hL hM hωY hωX hvY hvX k hk t₀ y hy
  have hk0 : k < D.R.m := by omega
  have hSt := GlobalTheory.Chain.StepVac.stepsOK D G Pl0 T A Ks R hL hM.inf hωY hωX hvY hvX
  obtain ⟨y₀, hy₀⟩ := GlobalTheory.Chain.innerIntertwiners_of_pair D G Pl0 T A Ks R (GlobalTheory.T.exists_uniformRealThetaIntertwiner_chainStep h1 h2 D) hC hM.inf hSt k hk
  have hS := hSt.1 t₀ ⟨k, hk0⟩ hk
  have key : ∀ (V W : HSp D) (a b : ℕ) (_ : a = k) (_ : b = k + 1) (M : DSModel V (parB (Ptw D) a))
      (M' : DSModel W (parB (Ptw D) b)) ω f, GlobalTheory.Chain.IsStepWeil ⟨k, hk0⟩ R.ψ V W ω → GlobalTheory.Chain.IsVacVec R.ψ R.θ M M' f →
      ∀ It It' : PolF D W.rank V.rank →ₗ[ℂ] SmT M' →ₗ[ℂ] SmT M, IsItW R.θ M M' ω (GlobalTheory.Chain.ptOf R.ψ R.θ M M' f) It →
        IsItW R.θ M M' ω (GlobalTheory.Chain.ptOf R.ψ R.θ M M' f) It' → ∃ c : ℂ, It' = c • It := by
    intro V W a b ha hb M M' ω f
    subst ha hb
    exact _root_.GlobalTheory.Chain.RealLine.itLine_of_discreteSeries h1 h2 D ⟨a, hk0⟩ V W M M' R.θ R.ψ hM.inf (hC _) ω f
  obtain ⟨c, hc⟩ := key _ _ _ _ (min_eq_left hk0.le) (min_eq_left hk.le) (R.MY k) (R.MY (k + 1)) _ _ hS.1 hS.2 y₀ y
    (hy₀ t₀) hy
  have hc0 : c ≠ 0 := by
    rintro rfl
    exact hy.ne (by rw [hc, zero_smul])
  intro t
  rw [hc]
  exact isItW_smul (hy₀ t) hc0

end GlobalTheory.Chain.ItAllTuples

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.RestrictHalfApply
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum IsDedekindDomain NumberField Matrix GlobalTheory.ExportSeries
open Formalism.IndefR.Links (PolF)
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 800000

namespace GlobalTheory.ExportSeries

variable {D : D7}


open Classical in
def restrictHalf {m n : ℕ} (a' b : AE D) (Λ : AddSubgroup (Mx D m n)) : (Mx D m n → ℂ) →ₗ[ℂ] (Mx D m n → ℂ) where
  toFun Φ x := Φ (a' • x) * halfInd b Λ (b • x) * (if IsHalf (a' + b) x then 1 else 0)
  map_add' Φ Φ' := by funext x; simp only [Pi.add_apply]; ring
  map_smul' c Φ := by funext x; simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply]; ring

open Classical in
theorem restrictHalf_apply {m n : ℕ} (a' b : AE D) (Λ : AddSubgroup (Mx D m n)) (Φ : Mx D m n → ℂ) (x : Mx D m n) :
    restrictHalf a' b Λ Φ x = Φ (a' • x) * halfInd b Λ (b • x) * (if IsHalf (a' + b) x then 1 else 0) := rfl

end GlobalTheory.ExportSeries

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SchrodingerFunctionInvariantTypePrime
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef
open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.IndefR.Links
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.DownLift
open GlobalTheory.DownLift.GenFinite
open GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting (FinPl idem SplitProj IsIdemOf IsProjAt adjCo grpCo frCo)
open GlobalTheory.DownLift.GenSplit

namespace GlobalTheory.DownLift.GenSplit

theorem actO_sigma_of_grpCo : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T : Type) (A : FamIn D.what₂.LL G Pl0 T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks), R.toLevCh.Is A.μ0 → ∀ (i : Fin D.R.m) (v : FinPl D) (φ : SplitProj D v) (e : Formalism.L2.Theta.AE D), IsIdemOf φ e → ∀ (σ : Matrix (Fin D.R.r ⊕ Fin D.R.t) (Fin D.R.r) (Fv D.host.F v) → WO (Vc D i) (Wc D i)), (∀ X, IsHalf (cA D e) (σ X) ∧ coR R i φ (σ X) = X) → ∀ (κ : GA D (Vc D i)) (h : GL (Fin D.R.r ⊕ Fin D.R.t) (OI v)) (h' : GL (Fin (Vc D i).rank) (OI v)), (∀ a b, (h' : Matrix (Fin (Vc D i).rank) (Fin (Vc D i).rank) (OI v)) (rowIx (rank_V i) a) (rowIx (rank_V i) b) = (h : Matrix (Fin D.R.r ⊕ Fin D.R.t) (Fin D.R.r ⊕ Fin D.R.t) (OI v)) a b) → grpCo φ (Vc D i) (frCo φ (R.βV i)) κ = Matrix.GeneralLinearGroup.map (algebraMap (OI v) (Fv D.host.F v)) h' → ∀ X : Matrix (Fin D.R.r ⊕ Fin D.R.t) (Fin D.R.r) (Fv D.host.F v), actO (Vc D i) (Wc D i) κ 1 (σ X) = σ ((h : Matrix (Fin D.R.r ⊕ Fin D.R.t) (Fin D.R.r ⊕ Fin D.R.t) (OI v)).map (algebraMap (OI v) (Fv D.host.F v)) * X) := by
  intro D G _ _ Pl0 T A Ks _ _ _ R hL i v φ e he σ hσ κ h h' hh' hgrp X
  have sdV := _root_.GlobalTheory.SDFrameLattice.isSelfDualC_of_isSDFrame D _ _ _ _ (hL.βV i)
  have sdW := _root_.GlobalTheory.SDFrameLattice.isSelfDualC_of_isSDFrame D _ _ _ _ (hL.βW i)
  have hco := (GlobalTheory.PlaceTensor.adjCo_isCoord D (Vc D i) (Wc D i) _ _ sdV sdW v φ e he
    (frCo φ (R.βV i)) (frCo φ (R.βW i))).1
  have hinj := hco.2.1.injOn
  have h1 : IsHalf (cA D e) (actO (Vc D i) (Wc D i) κ 1 (σ X)) := GlobalTheory.SplitHecke.isHalf_actO κ 1 (hσ X).1
  have h2 : IsHalf (cA D e) (σ ((h : Matrix (Fin D.R.r ⊕ Fin D.R.t) (Fin D.R.r ⊕ Fin D.R.t) (OI v)).map (algebraMap (OI v) (Fv D.host.F v)) * X)) := (hσ _).1
  refine hinj h1 h2 ?_
  have ha : adjCo φ (Vc D i) (Wc D i) (frCo φ (R.βV i)) (frCo φ (R.βW i)) (actO (Vc D i) (Wc D i) κ 1 (σ X)) =
      (grpCo φ (Vc D i) (frCo φ (R.βV i)) κ).val * adjCo φ (Vc D i) (Wc D i) (frCo φ (R.βV i)) (frCo φ (R.βW i)) (σ X) := by
    have := GlobalTheory.PlaceTensor.AdjCoord.adjCo_actO φ (Vc D i) (Wc D i) (frCo φ (R.βV i)) (frCo φ (R.βW i)) κ⁻¹ 1 (σ X)
    rw [inv_inv, inv_one, GlobalTheory.PlaceTensor.AdjCoord.grpCo_inv, inv_inv] at this
    rw [this]
    have g1 : grpCo φ (Wc D i) (frCo φ (R.βW i)) 1 = 1 := by
      unfold grpCo; rw [map_one, map_one, mul_one, inv_mul_cancel]
    rw [g1, Units.val_one, Matrix.mul_one]
  have hc : ∀ x, coR R i φ x = (adjCo φ (Vc D i) (Wc D i) (frCo φ (R.βV i)) (frCo φ (R.βW i)) x).submatrix (rowIx (rank_V i)) (finCongr (rank_weight_component_eq i)) := fun x => rfl
  have hX : coR R i φ (actO (Vc D i) (Wc D i) κ 1 (σ X)) = coR R i φ (σ ((h : Matrix (Fin D.R.r ⊕ Fin D.R.t) (Fin D.R.r ⊕ Fin D.R.t) (OI v)).map (algebraMap (OI v) (Fv D.host.F v)) * X)) := by
    rw [(hσ _).2, hc, ha, hgrp, ← Matrix.submatrix_mul_equiv _ _ _ (rowIx (rank_V i)), ← hc, (hσ X).2]
    congr 1
    ext a b
    simp [Matrix.GeneralLinearGroup.map, hh']
  refine Matrix.ext fun a b => ?_
  have e1 := congrFun (congrFun hX ((rowIx (rank_V i)).symm a)) ((finCongr (rank_weight_component_eq i)).symm b)
  simpa [hc] using e1

theorem levG_levChi_of_red : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T : Type) (A : FamIn D.what₂.LL G Pl0 T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks), R.toLevCh.Is A.μ0 → ∀ (i : Fin D.R.m) (t : T) (PP : Pl D.host.E), PP ∈ R.Pg → ∀ (κ : GA D (Vc D i)), κ ∈ GfC (Vc D i) → finE (Vc D i) κ ∈ St (R.βV i) → ∀ (g : GL (Fin (Vc D i).rank) (kP PP)), redFn (R.βV i) PP (finE (Vc D i) κ) = g → (∀ PP', PP' ∈ R.Pg ∨ PP' ∈ R.Q t → PP' ≠ PP → redFn (R.βV i) PP' (finE (Vc D i) κ) = 1) → (∀ a b : Fin D.R.r, (g : Matrix (Fin (Vc D i).rank) (Fin (Vc D i).rank) (kP PP)) (rowIx (rank_V i) (Sum.inl a)) (rowIx (rank_V i) (Sum.inl b)) = (1 : Matrix (Fin D.R.r) (Fin D.R.r) (kP PP)) a b) → (∀ (a : Fin D.R.t) (b : Fin D.R.r), (g : Matrix (Fin (Vc D i).rank) (Fin (Vc D i).rank) (kP PP)) (rowIx (rank_V i) (Sum.inr a)) (rowIx (rank_V i) (Sum.inl b)) = 0) → κ ∈ levG (Vc D i) (R.βV i) (R.datVt i t) ∧ levChi (Vc D i) (R.βV i) (R.datVt i t) κ = ((R.chi ((i : ℕ) + 1) PP (Matrix.GeneralLinearGroup.det g) : ℂˣ) : ℂ)⁻¹ := by
  intro D G _ _ Pl0 T A Ks _ _ _ R hL i t PP hPP κ hGf hSt g hg hoth hg1 hg2
  have rV : (Vc D i).rank = D.R.r + D.R.t := (rank_V i).symm
  have hdisj : PP ∉ R.Q t := Finset.disjoint_left.1 (Formalism.IndefR.Fin.disjoint_Pg_Q R.toLevCh hL t) hPP
  have hlo : ∀ a : Fin (Vc D i).rank, (ha : a.val < D.R.r) → a = rowIx (rank_V i) (Sum.inl ⟨a.val, ha⟩) := by
    intro a ha; ext; simp [rowIx]
  have hhi : ∀ a : Fin (Vc D i).rank, (ha : D.R.r ≤ a.val) →
      a = rowIx (rank_V i) (Sum.inr ⟨a.val - D.R.r, by have := a.2; omega⟩) := by
    intro a ha; ext; simp [rowIx]; omega
  have htri : g ∈ blockTri (blkOf D.R.r D.R.t) := by
    intro a b hab
    have ha : D.R.r ≤ a.val := by
      by_contra h; push_neg at h
      simp [blkOf, h] at hab
    have hb : b.val < D.R.r := by
      by_contra h; push_neg at h
      have h1 := a.2; have h2 := b.2
      have e1 : (a.val - D.R.r) / D.R.t = 0 := Nat.div_eq_of_lt (by omega)
      have e2 : (b.val - D.R.r) / D.R.t = 0 := Nat.div_eq_of_lt (by omega)
      simp [blkOf, not_lt.2 ha, not_lt.2 h, e1, e2] at hab
    rw [hhi a ha, hlo b hb]
    exact hg2 _ _
  have hr1 : upperLeftBlock (r_le_V i) g = 1 := by
    apply Units.ext
    rw [upper_block_val_submatrix _ (blockTri_blkOf_le _ _ htri), Units.val_one]
    refine Matrix.ext fun a b => ?_
    simp only [Matrix.submatrix_apply]
    have ea : Fin.castLE (r_le_V i) a = rowIx (rank_V i) (Sum.inl a) := by ext; simp [rowIx]
    have eb : Fin.castLE (r_le_V i) b = rowIx (rank_V i) (Sum.inl b) := by ext; simp [rowIx]
    rw [ea, eb, hg1]
  have hred : ∀ PP', PP' ∈ R.Pg ∨ PP' ∈ R.Q t → redFn (R.βV i) PP' (finE (Vc D i) κ) = 1 ∨ PP' = PP := by
    intro PP' h
    by_cases e : PP' = PP
    · exact Or.inr e
    · exact Or.inl (hoth PP' h e)
  have hrT : rTup (R.βV i) (R.datVt i t) (finE (Vc D i) κ) = 1 := by
    funext PP'
    show upperLeftBlock (r_le_V i) (redFn (R.βV i) PP'.1 (finE (Vc D i) κ)) = 1
    rcases hred PP'.1 (Or.inl PP'.2) with h | h
    · rw [h]; exact blockDiagonalExtendByOnePrimeField_one _ _
    · rw [h, hg, hr1]
  have hpar : finE (Vc D i) κ ∈ parLev D.sp.cm (Vc D i).gram (R.βV i) (R.datVt i t) := by
    refine mem_parLev.2 ⟨GlobalTheory.LevSplit.finE_mem_UA _ _, hSt, fun PP' hP' => ?_, fun PP' hP' => ?_⟩
    · rcases hred PP' (Or.inl hP') with h | h
      · rw [h]; exact Subgroup.one_mem _
      · rw [h, hg]; exact htri
    · rcases hred PP' (Or.inr hP') with h | h
      · rw [h]; exact Subgroup.one_mem _
      · exact absurd (h ▸ hP') hdisj
  refine ⟨⟨hGf, hpar, ?_⟩, ?_⟩
  · show rTup (R.βV i) (R.datVt i t) (finE (Vc D i) κ) ∈ (R.datVt i t).P.H
    rw [hrT]; exact Subgroup.one_mem _
  · have hQ : ∏ PP' ∈ (R.datVt i t).Q, (R.datVt i t).xq PP' (dBlk (blk2 (R.datVt i t).r) 1 (redFn (R.βV i) PP' (finE (Vc D i) κ))) = 1 := by
      refine Finset.prod_eq_one fun PP' hP' => ?_
      rcases hred PP' (Or.inr hP') with h | h
      · rw [h, dBlk, blockDiagonalExtendByOnePrimeField_one, map_one]
      · exact absurd (h ▸ hP') hdisj
    have hdet : Matrix.GeneralLinearGroup.det g = dBlk (blkOf D.R.r D.R.t) 1 g := by
      rw [(_root_.GlobalTheory.VecInv.TwoBlockDet.det_blocks _ _ _ D.R.t (r_le_V i) g).1 (blockTri_blkOf_le _ _ htri), hr1, map_one, one_mul,
        (_root_.GlobalTheory.VecInv.TwoBlockDet.det_blocks _ _ _ D.R.t (r_le_V i) g).2.1 rV htri]
    have hG : ∏ PP' ∈ (R.datVt i t).Pg, ∏ c ∈ Finset.range (R.datVt i t).s, (R.datVt i t).cg (c + 1) PP'
        (dBlk (blkOf (R.datVt i t).r (R.datVt i t).t) (c + 1) (redFn (R.βV i) PP' (finE (Vc D i) κ))) =
        (R.chi ((i : ℕ) + 1) PP (Matrix.GeneralLinearGroup.det g))⁻¹ := by
      rw [Finset.prod_eq_single PP]
      · show ∏ c ∈ Finset.range 1, _ = _
        rw [Finset.prod_range_one, hg, hdet]
        rfl
      · intro PP' hP' hne
        rcases hred PP' (Or.inl hP') with h | h
        · refine Finset.prod_eq_one fun c _ => ?_
          rw [h, dBlk, blockDiagonalExtendByOnePrimeField_one, map_one]
        · exact absurd h hne
      · intro h; exact absurd hPP h
    unfold levChi levFn
    rw [hrT, blockDiagonalExtendByOnePrimeField_one, hQ, hG, one_mul, mul_one, Units.val_inv_eq_inv_val]

theorem heisO_smul_fun {D : D7} {ψ : AddChar (AF D.host.F) ℂ} {S T : HSp D} (w : WO S T) (c : ℂ) (f : WO S T → ℂ) :
    heisO ψ S T w (c • f) = c • heisO ψ S T w f := by
  funext x; simp only [heisO, Pi.smul_apply, smul_eq_mul]; ring

theorem schrodinger_type_inv : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T : Type) (A : FamIn D.what₂.LL G Pl0 T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks), R.toLevCh.Is A.μ0 → R.thP_ωP → ∀ (i : Fin D.R.m) (t : T) (PP : Pl D.host.E), PP ∈ R.Pg → ∀ (v : FinPl D) (φ : SplitProj D v) (e : Formalism.L2.Theta.AE D), IsProjAt φ PP → IsIdemOf φ e → ∀ (red : OI v →+* kP PP), Function.Surjective red → (∀ a : OI v, red a = 0 ↔ Valued.v (a : Fv D.host.F v) < 1) → ActAt R i t PP φ e red → ∀ (Sb : Finset (FinPl D)), v ∈ Sb → ∀ (σ : Matrix (Fin D.R.r ⊕ Fin D.R.t) (Fin D.R.r) (Fv D.host.F v) → WO (Vc D i) (Wc D i)), (∀ X, IsHalf (cA D e) (σ X) ∧ coR R i φ (σ X) = X) → ∀ (ℓ : (WO (Vc D i) (Wc D i) → ℂ) →ₗ[ℂ] ℂ), InvForm R.ψ (Vc D i) (Wc D i) e ℓ → ∀ (f : WO (Vc D i) (Wc D i) → ℂ), TypeIn R i t Sb f → ∀ (ϖ : OI v), Irreducible ϖ → ∀ h : GL (Fin D.R.r ⊕ Fin D.R.t) (OI v), (∀ a b, (h : Matrix (Fin D.R.r ⊕ Fin D.R.t) (Fin D.R.r ⊕ Fin D.R.t) (OI v)) (Sum.inl a) (Sum.inl b) - (1 : Matrix (Fin D.R.r) (Fin D.R.r) (OI v)) a b ∈ Ideal.span {ϖ}) → (∀ a b, (h : Matrix (Fin D.R.r ⊕ Fin D.R.t) (Fin D.R.r ⊕ Fin D.R.t) (OI v)) (Sum.inr a) (Sum.inl b) ∈ Ideal.span {ϖ}) → ∀ X : Matrix (Fin D.R.r ⊕ Fin D.R.t) (Fin D.R.r) (Fv D.host.F v), ℓ (heisO R.ψ (Vc D i) (Wc D i) (σ ((h : Matrix (Fin D.R.r ⊕ Fin D.R.t) (Fin D.R.r ⊕ Fin D.R.t) (OI v)).map (algebraMap (OI v) (Fv D.host.F v)) * X)) f) = ℓ (heisO R.ψ (Vc D i) (Wc D i) (σ X) f) := by
  intro D G _ _ Pl0 T A Ks _ _ _ R hL hω i t PP hPP v φ e hφ he red hsur hker hAct Sb hv σ hσ ℓ hℓ f hf ϖ hϖ h hh1 hh2 X
  let e' := rowIx (rank_V i)
  let h' : GL (Fin (Vc D i).rank) (OI v) := Units.map (Matrix.reindexAlgEquiv (OI v) (OI v) e').toMonoidHom h
  have hh' : ∀ a b, (h' : Matrix (Fin (Vc D i).rank) (Fin (Vc D i).rank) (OI v)) (e' a) (e' b) =
      (h : Matrix (Fin D.R.r ⊕ Fin D.R.t) (Fin D.R.r ⊕ Fin D.R.t) (OI v)) a b := by
    intro a b
    simp [h', Matrix.reindexAlgEquiv_apply]
  obtain ⟨κ, hsupp, hGf, hSt, hgrp, hred', hoth, hact⟩ := hAct h'
  have hϖ0 : red ϖ = 0 := by
    haveI : PP.asIdeal.IsMaximal := PP.isMaximal
    letI : Field (kP PP) := Ideal.Quotient.field _
    have hmax : RingHom.ker red = IsLocalRing.maximalIdeal (OI v) :=
      IsLocalRing.eq_maximalIdeal (RingHom.ker_isMaximal_of_surjective red hsur)
    have : ϖ ∈ RingHom.ker red := by
      rw [hmax]; exact (IsLocalRing.mem_maximalIdeal _).2 hϖ.not_isUnit
    exact this
  have hspan : ∀ x ∈ Ideal.span {ϖ}, red x = 0 := by
    intro x hx
    obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton'.1 hx
    rw [map_mul, hϖ0, mul_zero]
  have hg1 : ∀ a b : Fin D.R.r, ((Matrix.GeneralLinearGroup.map red h' : GL (Fin (Vc D i).rank) (kP PP)) :
      Matrix (Fin (Vc D i).rank) (Fin (Vc D i).rank) (kP PP)) (e' (Sum.inl a)) (e' (Sum.inl b)) =
      (1 : Matrix (Fin D.R.r) (Fin D.R.r) (kP PP)) a b := by
    intro a b
    have h0 := hspan _ (hh1 a b)
    rw [map_sub, sub_eq_zero] at h0
    rw [Matrix.GeneralLinearGroup.map_apply, hh', h0]
    by_cases hab : a = b
    · subst hab; simp
    · simp [Matrix.one_apply_ne hab]
  have hg2 : ∀ (a : Fin D.R.t) (b : Fin D.R.r), ((Matrix.GeneralLinearGroup.map red h' : GL (Fin (Vc D i).rank) (kP PP)) :
      Matrix (Fin (Vc D i).rank) (Fin (Vc D i).rank) (kP PP)) (e' (Sum.inr a)) (e' (Sum.inl b)) = 0 := by
    intro a b
    rw [Matrix.GeneralLinearGroup.map_apply, hh']
    exact hspan _ (hh2 a b)
  obtain ⟨hmem, hchi⟩ := levG_levChi_of_red D G Pl0 T A Ks R hL i t PP hPP κ hGf hSt _ hred' hoth hg1 hg2
  have hSIn : SuppIn Sb (Vc D i) κ := suppIn_of_suppAt he hv hsupp
  have hW := hω i t
  have hTy := hf.2 κ hmem hSIn
  rw [hchi, inv_inv] at hTy
  have hx := actO_sigma_of_grpCo D G Pl0 T A Ks R hL i v φ e he σ hσ κ h h' hh' hgrp X
  have e1 := hW.om_heis κ 1 (σ X) f hf.1
  rw [hx, hTy, heisO_smul_fun] at e1
  have e2 := hact ℓ hℓ (heisO R.ψ (Vc D i) (Wc D i) (σ X) f)
    (GlobalTheory.TwistFactorCompare.isTheta_heisO hW.std hf.1 _)
  rw [e1, map_smul, smul_eq_mul] at e2
  exact mul_left_cancel₀ (Units.ne_zero _) e2

end GlobalTheory.DownLift.GenSplit
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SupportTermSubset
section
noncomputable section

open Formalism.IndefR

namespace GlobalTheory.LawTrace

variable {G Γ W : Type} [Group G] [Group Γ] [AddCommGroup W] [Module ℂ W]
  (ι : Γ →* G) (ρ : Γ →* Module.End ℂ W) (J : Subgroup G) (χ : J →* ℂˣ)


open Classical in
def term (y x : G) (P : W) (γ : Γ) : W :=
  if h : (ι γ * y)⁻¹ * x ∈ J then ((χ ⟨_, h⟩ : ℂˣ) : ℂ) • ρ γ P else 0

def tr (y : G) (P : W) : G → W := fun x => ∑ᶠ γ, term ι ρ J χ y x P γ

variable {ι ρ J χ}

theorem support_term_subset (y x : G) (P : W) :
    Function.support (term ι ρ J χ y x P) ⊆ {γ | (ι γ * y)⁻¹ * x ∈ J} := by
  intro γ hγ
  by_contra h
  exact hγ (by unfold term; exact dif_neg (show ¬ ((ι γ * y)⁻¹ * x ∈ J) from h))

theorem finite_cond {y : G} (hf : Finite (Bridge.stab ι J y)) (x : G) : {γ | (ι γ * y)⁻¹ * x ∈ J}.Finite := by
  rcases Set.eq_empty_or_nonempty {γ | (ι γ * y)⁻¹ * x ∈ J} with h | ⟨γ₀, h₀⟩
  · rw [h]; exact Set.finite_empty
  · have hs : ((Bridge.stab ι J y : Subgroup Γ) : Set Γ).Finite := Set.finite_coe_iff.1 hf
    refine (hs.image fun s => γ₀ * s).subset fun γ hγ => ⟨γ₀⁻¹ * γ, ?_, by simp⟩
    change γ₀⁻¹ * γ ∈ Bridge.stab ι J y
    rw [Bridge.mem_stab]
    have h1 := J.mul_mem h₀ (J.inv_mem (show (ι γ * y)⁻¹ * x ∈ J from hγ))
    convert h1 using 1
    simp [mul_assoc]

theorem support_term_finite {y : G} (hf : Finite (Bridge.stab ι J y)) (x : G) (P : W) :
    (Function.support (term ι ρ J χ y x P)).Finite :=
  (finite_cond hf x).subset (support_term_subset y x P)

theorem term_mul (y x : G) (P : W) (γ₀ γ : Γ) (k : J) :
    term ι ρ J χ y (ι γ₀ * x * k) P (γ₀ * γ) = ((χ k : ℂˣ) : ℂ) • ρ γ₀ (term ι ρ J χ y x P γ) := by
  have e : (ι (γ₀ * γ) * y)⁻¹ * (ι γ₀ * x * k) = (ι γ * y)⁻¹ * x * k := by
    simp [mul_assoc]
  unfold term
  by_cases h : (ι γ * y)⁻¹ * x ∈ J
  · have h' : (ι (γ₀ * γ) * y)⁻¹ * (ι γ₀ * x * k) ∈ J := by rw [e]; exact J.mul_mem h k.2
    rw [dite_eq_left h', dite_eq_left h]
    have ek : (⟨_, h'⟩ : J) = ⟨_, h⟩ * k := Subtype.ext e
    rw [ek, map_mul, map_mul, Units.val_mul, map_smul, smul_smul, mul_comm, Module.End.mul_apply]
  · have h' : ¬ (ι (γ₀ * γ) * y)⁻¹ * (ι γ₀ * x * k) ∈ J := by
      rw [e]; intro h2; exact h (by simpa using J.mul_mem h2 (J.inv_mem k.2))
    rw [dif_neg h', dif_neg h, map_zero, smul_zero]

theorem tr_law {y : G} (hf : Finite (Bridge.stab ι J y)) (P : W) (γ₀ : Γ) (x : G) (k : J) :
    tr ι ρ J χ y P (ι γ₀ * x * k) = ((χ k : ℂˣ) : ℂ) • ρ γ₀ (tr ι ρ J χ y P x) := by
  unfold tr
  rw [← finsum_comp_equiv (Equiv.mulLeft γ₀)]
  simp only [Equiv.coe_mulLeft, term_mul]
  let L : W →ₗ[ℂ] W := ((χ k : ℂˣ) : ℂ) • ρ γ₀
  change ∑ᶠ γ, L (term ι ρ J χ y x P γ) = L (∑ᶠ γ, term ι ρ J χ y x P γ)
  exact (map_finsum L (support_term_finite hf x P)).symm

theorem mem_lawForms_tr {y : G} (hf : Finite (Bridge.stab ι J y)) (P : W) :
    tr ι ρ J χ y P ∈ GlobalTheory.ExportSeries.lawForms ι ρ J χ :=
  GlobalTheory.ExportSeries.mem_lawForms.2 fun γ x k => tr_law hf P γ x k

theorem tr_add {y : G} (hf : Finite (Bridge.stab ι J y)) (P Q : W) :
    tr ι ρ J χ y (P + Q) = tr ι ρ J χ y P + tr ι ρ J χ y Q := by
  funext x
  have e : ∀ γ, term ι ρ J χ y x (P + Q) γ = term ι ρ J χ y x P γ + term ι ρ J χ y x Q γ := fun γ => by
    unfold term; split_ifs <;> simp [smul_add]
  simp only [tr, Pi.add_apply, e]
  exact finsum_add_distrib (support_term_finite hf x P) (support_term_finite hf x Q)

theorem tr_smul (y : G) (a : ℂ) (P : W) : tr ι ρ J χ y (a • P) = a • tr ι ρ J χ y P := by
  funext x
  have e : ∀ γ, term ι ρ J χ y x (a • P) γ = a • term ι ρ J χ y x P γ := fun γ => by
    unfold term; split_ifs <;> simp [smul_comm a]
  simp only [tr, Pi.smul_apply, e]
  exact (smul_finsum a _).symm

theorem tr_zero (y : G) : tr ι ρ J χ y (0 : W) = 0 := by
  simpa using tr_smul (ι := ι) (ρ := ρ) (χ := χ) y (0 : ℂ) (0 : W)

theorem tr_mem {R : Type} [Semiring R] [Module R W] {y : G} (hf : Finite (Bridge.stab ι J y)) (P : W) (x : G)
    (M : Submodule R W) (hM : ∀ γ, (ι γ * y)⁻¹ * x ∈ J → term ι ρ J χ y x P γ ∈ M) : tr ι ρ J χ y P x ∈ M := by
  unfold tr
  rw [finsum_eq_sum _ (support_term_finite hf x P)]
  refine Submodule.sum_mem _ fun γ hγ => ?_
  have h := support_term_subset y x P ((Set.Finite.mem_toFinset _).1 hγ)
  exact hM γ h

theorem tr_self {y : G} (hf : Finite (Bridge.stab ι J y)) {F : G → W} (hF : F ∈ GlobalTheory.ExportSeries.lawForms ι ρ J χ) :
    tr ι ρ J χ y (F y) y = (Nat.card (Bridge.stab ι J y) : ℂ) • F y := by
  classical
  have e : ∀ γ, term ι ρ J χ y y (F y) γ = if γ ∈ Bridge.stab ι J y then F y else 0 := fun γ => by
    unfold term
    have hc : (ι γ * y)⁻¹ * y ∈ J ↔ γ ∈ Bridge.stab ι J y := by
      rw [Bridge.mem_stab, ← J.inv_mem_iff]
      simp [mul_assoc]
    by_cases h : (ι γ * y)⁻¹ * y ∈ J
    · rw [dite_eq_left h, if_pos (hc.1 h)]
      have := GlobalTheory.ExportSeries.mem_lawForms.1 hF γ y ⟨_, h⟩
      rw [show ι γ * y * ((ι γ * y)⁻¹ * y) = y by group] at this
      exact this.symm
    · rw [dif_neg h, if_neg fun h' => h (hc.2 h')]
  unfold tr
  simp only [e]
  have hs : ((Bridge.stab ι J y : Subgroup Γ) : Set Γ).Finite := Set.finite_coe_iff.1 hf
  have ei : (fun γ => if γ ∈ Bridge.stab ι J y then F y else 0) =
      Set.indicator ((Bridge.stab ι J y : Subgroup Γ) : Set Γ) (fun _ => F y) := by
    funext γ; simp [Set.indicator]
  rw [ei, ← finsum_mem_def]
  rw [finsum_mem_eq_finite_toFinset_sum _ hs, Finset.sum_const, ← Nat.cast_smul_eq_nsmul ℂ]
  congr 1
  rw [← Nat.card_eq_card_finite_toFinset hs]
  rfl

theorem eq_sum_tr {I : Type} [Fintype I] {y : I → G} (hr : Bridge.IsReps ι J y)
    (hf : ∀ i, Finite (Bridge.stab ι J (y i))) {F : G → W} (hF : F ∈ GlobalTheory.ExportSeries.lawForms ι ρ J χ) :
    F = ∑ i, ((Nat.card (Bridge.stab ι J (y i)) : ℂ))⁻¹ • tr ι ρ J χ (y i) (F (y i)) := by
  funext x
  obtain ⟨i₀, ⟨γ₀, k₀, hx⟩, huniq⟩ := hr x
  rw [Finset.sum_apply, Finset.sum_eq_single i₀]
  · have hne : ((Nat.card (Bridge.stab ι J (y i₀)) : ℂ)) ≠ 0 := by
      haveI := hf i₀
      exact Nat.cast_ne_zero.2 Nat.card_pos.ne'
    rw [Pi.smul_apply, hx, tr_law (hf i₀), tr_self (hf i₀) hF, GlobalTheory.ExportSeries.mem_lawForms.1 hF γ₀ (y i₀) k₀, map_smul,
      smul_comm ((χ k₀ : ℂˣ) : ℂ) ((Nat.card (Bridge.stab ι J (y i₀)) : ℂ)), smul_smul, inv_mul_cancel₀ hne, one_smul]
  · intro i _ hi
    rw [Pi.smul_apply]
    have : tr ι ρ J χ (y i) (F (y i)) x = 0 := by
      unfold tr
      refine finsum_eq_zero_of_forall_eq_zero fun γ => ?_
      unfold term
      rw [dif_neg]
      intro h
      exact hi (huniq i ⟨γ, ⟨_, h⟩, by simp [mul_assoc]⟩)
    rw [this, smul_zero]
  · intro h; exact absurd (Finset.mem_univ _) h

end GlobalTheory.LawTrace

end
end

