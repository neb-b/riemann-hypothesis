module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0222
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0359
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0307
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0300
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SchwartzBruhatMatrixTranslationModulationIrreduc
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0365
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.HzUnit
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleDiscreteSeriesOfHasParam
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0025
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0338
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsCombAt
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0009
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0002
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0371
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ExistsUnitarySupportedAtPlaceOfMulEqIdem
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0350
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.CosInj
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.UnitRatio
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0357
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.VacOfShape
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.FrameTopAlt
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ProdDat
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0322
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0337
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0355
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0800
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0433
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.IsSelfDualCLatFrame
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0187
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0367
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0347
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SplitPlaceLocalGroupClosedEmbeddingIntegral

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SchwartzBruhatMulConjugateHalfCharacterSplitPlac
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.FinPl GlobalTheory.MixPer GlobalTheory.MixModel GlobalTheory.Unf GlobalTheory.LatPair GlobalTheory.SplitWeil GlobalTheory.SeeSaw ValuativeRel IsLocalRing
open GlobalTheory.IndefiniteRowSideFullHecke.AppendedVectorData (lastKer lastPair cosetInd withRow)
open GlobalTheory.FinPl.ExtZero (colFun rowFun)

noncomputable section
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.ModSB

theorem continuous_pi_hO_up {D : D7} {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (p : GlobalTheory.LocMod.Place D k) {S T : HSp D} {Y Y' : Type} [Fintype Y] [DecidableEq Y] [Fintype Y'] [DecidableEq Y']
    (FS : GlobalTheory.LocMod.Frame k S.rank Y') (FT : GlobalTheory.LocMod.Frame k T.rank Y) (y : WO S T) :
    Continuous fun t : Matrix Y Y' k => p.π (hO S T (p.up FS FT t) y) := by
  have h : (fun t : Matrix Y Y' k => p.π (hO S T (p.up FS FT t) y)) = fun t =>
      ∑ a, ∑ b, ∑ c, ∑ d, p.π (incA D (S.gram⁻¹ a b)) * p.π (cA D (y c b)) * p.π (incA D (T.gram c d)) *
        (FT.β * t * FS.γ) d a := by
    funext t
    unfold hO
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [map_sum, map_mul]
    refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun c _ =>
      Finset.sum_congr rfl fun d _ => ?_
    simp only [GlobalTheory.LocMod.Place.up, Matrix.map_apply, p.π_ι]
  rw [h]
  have hm : Continuous fun t : Matrix Y Y' k => FT.β * t * FS.γ :=
    (continuous_const.matrix_mul continuous_id).matrix_mul continuous_const
  refine continuous_finsetSum _ fun a _ => continuous_finsetSum _ fun b _ => continuous_finsetSum _ fun c _ =>
    continuous_finsetSum _ fun d _ => continuous_const.mul (hm.matrix_elem d a)

theorem mul_char_mem_SB : ∀ (D : D7) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (p : GlobalTheory.LocMod.Place D k) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ (S T : HSp D) (Y Y' : Type) [Fintype Y] [DecidableEq Y] [Fintype Y'] [DecidableEq Y'] (FS : GlobalTheory.LocMod.Frame k S.rank Y') (FT : GlobalTheory.LocMod.Frame k T.rank Y) (y : WO S T), IsHalf (cA D p.e) y → ∀ Φ ∈ SB (Matrix Y Y' k), (fun t => ψ (symplO S T (p.up FS FT t) y) * Φ t) ∈ SB (Matrix Y Y' k) := by
  intro D k _ _ _ _ p ψ hψ S T Y Y' _ _ _ _ FS FT y hy Φ hΦ
  obtain ⟨⟨ψk, hk⟩, hc, -⟩ := GlobalTheory.LocChar.weil_char_split D k p ψ hψ
  have hcont := (hc ψk hk).1
  have heq : (fun t => ψ (symplO S T (p.up FS FT t) y) * Φ t) =
      fun t => ((ψk (p.π (hO S T (p.up FS FT t) y)) : Circle) : ℂ) * Φ t := by
    funext t
    rw [GlobalTheory.LocSympl.psi_sympl_up p FS FT ψ ψk hk t y]
  rw [heq]
  have hl : IsLocallyConstant (fun t : Matrix Y Y' k => ((ψk (p.π (hO S T (p.up FS FT t) y)) : Circle) : ℂ)) :=
    ((GlobalTheory.IrredSB.char_isLocallyConstant ψk hcont).comp_continuous (continuous_pi_hO_up p FS FT y)).comp
      (fun z : Circle => (z : ℂ))
  exact ⟨hl.mul hΦ.1, HasCompactSupport.mul_left hΦ.2⟩

end GlobalTheory.ModSB

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SeeSawFlatMapContractionSupportAtLevelPlaceStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.FinPl
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.seeSaw_flatMap_contraction_support_at_level_place : ∀ {D : D7} {c : Comm D} {v : VCom c}, c.Is → v.Is → GlobalTheory.LocMod.GSupp2 D → ∀ (t : Tup c), t.Is → ∀ (Gi : GLoc v), Gi.Chars t → ∀ (j σ : ℕ) (h : j + 2 * (σ + 1) + 2 = D.R.m) (F₁ : WO (c.V j) (c.V (j + 1)) → ℂ), Vac c.ψ _ _ (v.N j) (v.N (j + 1)) (· = Gi.q.v) F₁ → ∀ (F₂ : WO (c.V (j + 1)) (c.V (j + 1 + 1)) → ℂ), Vac c.ψ _ _ (v.N (j + 1)) (v.N (j + 1 + 1)) (· = Gi.q.v) F₂ → ∀ (x : GA D (c.V (j + 1 + 1))), SuppAt Gi.q.e (c.V (j + 1 + 1)) x → c.ctr j σ h (t.sBF j (σ + 1) h) (t.sFB j σ h) (comb c.ψ _ _ (Gi.eg j) F₁) (t.om (j + 1) (1, x) (comb c.ψ _ _ (Gi.eg (j + 1)) F₂)) ≠ 0 → ∃ r ∈ besGrp (c.bes (j + 1 + 1) σ (idx_step h)).d (c.bes (j + 1 + 1) σ (idx_step h)).o, SuppAt Gi.q.e (c.V (j + 1 + 1)) r ∧ ∃ u uk, (GlobalTheory.LocMod.ofSplit Gi.q).IsLoc (Gi.FY (j + 1 + 1) (2 * σ + 1) (by have := Gi.hs; omega)) u uk ∧ uk ∈ ((Gi.S.T (Fin D.R.t)).lev (j + 1 + 1) (2 * σ + 1) (by have := Gi.hs; omega)).J ∧ x = r * u := by
  first | exact @GlobalTheory.SeeSaw.PlaceSupp.supp_ctr | exact GlobalTheory.SeeSaw.PlaceSupp.supp_ctr | (intros; apply GlobalTheory.SeeSaw.PlaceSupp.supp_ctr <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SeeSawLocalSourceLevelCharacter
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.FinPl
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.LocMod GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.SymChain ValuativeRel

noncomputable section
namespace GlobalTheory.SeeSaw.LocSrc

section Local
variable {D : D7} {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem isLoc_one (p : Place D k) {S : HSp D} {Y : Type} [Fintype Y] [DecidableEq Y] (F : GlobalTheory.LocMod.Frame k S.rank Y) :
    p.IsLoc F 1 1 := by
  refine ⟨fun i j => by simp [Formalism.L2.Theta.mt], ?_⟩
  have : Formalism.L2.Theta.mt S 1 = 1 := by simp [Formalism.L2.Theta.mt]
  rw [this, Matrix.map_one p.π (map_zero _) (map_one _)]
  simp [F.βγ]

theorem isComp_inv (p : Place D k) {χ : (AE D)ˣ →* Circle} {μ : kˣ →* ℂˣ} (h : p.IsComp χ⁻¹ μ) : p.IsComp χ μ⁻¹ := by
  intro x a ha
  have h1 := h x a ha
  simp only [MonoidHom.inv_apply, Units.val_inv_eq_inv_val, Circle.coe_inv] at h1 ⊢
  rw [h1, inv_inv]

theorem valuation_det_of_mem_stabLat {Y : Type} [Fintype Y] [DecidableEq Y] {g h : GL Y k} (hh : h ∈ GlobalTheory.StepData.stabLat g) :
    valuation k ((Matrix.GeneralLinearGroup.det h : kˣ) : k) = 1 := by
  have h1 := valuation_det_of_mem_KO (GlobalTheory.StepData.mem_stabLat.1 hh)
  have e : Matrix.GeneralLinearGroup.det (g⁻¹ * h * g) = Matrix.GeneralLinearGroup.det h := by
    rw [map_mul, map_mul, map_inv, mul_comm, ← mul_assoc, mul_inv_cancel, one_mul]
  rwa [e] at h1

theorem om_Phi {s κ : ℕ} (S : SymData k s κ) (t : Type) [Fintype t] [DecidableEq t] (μ : ℕ → kˣ →* ℂˣ) (hμ : ∀ j, IsTame (μ j))
    (hu : ∀ j (x : kˣ), valuation k (x : k) = 1 → μ j x = S.μ j x) (j a : ℕ) (H : j + a = s) (hb : j + (a + 1) = s + 1)
    (x : ((S.T t).lev j (a + 1) hb).J) :
    GlobalTheory.SplitWeil.om (μ (j + 1)) x.1 1 ((S.T t).Phi j a H) = (((S.T t).lev j (a + 1) hb).lam x : ℂ) • (S.T t).Phi j a H := by
  obtain ⟨e1, e2⟩ := GlobalTheory.SeeSaw.MuUnits.withMu_eq k s κ S t μ hμ hu
  have hx : x.1 ∈ (((withMu S μ hμ).T t).lev j (a + 1) hb).J := by rw [(e2 j (a + 1) hb).1]; exact x.2
  have L : ((withMu S μ hμ).T t).Laws := Chain.ofType_laws _ _ _ _ _
  have h1 := (L.1 j a H).1 ⟨x.1, hx⟩
  rw [e1, (e2 j (a + 1) hb).2 x.1 hx x.2] at h1
  exact h1

end Local

theorem seeSaw_local_sourceLevel_character : ∀ (D : D7) (c : Comm D) (v : VCom c) (G : GLoc v), c.Is → v.Is → ∀ (j : ℕ) (χS χT : (AE D)ˣ →* Circle) (om : Om (c.V j) (c.V (j + 1))), IsWeilDatumO c.ψ _ _ χS χT om → ∀ (μ : ℕ → G.kˣ →* ℂˣ), (∀ i, IsTame (μ i)) → (∀ i (x : G.kˣ), valuation G.k (x : G.k) = 1 → μ i x = G.S.μ i x) → (ofSplit G.q).IsComp χS⁻¹ (μ (j + 1)) → (∃ μ', (ofSplit G.q).IsComp χT μ' ∧ ∀ x : G.kˣ, valuation G.k (x : G.k) = 1 → μ' x * μ (j + 1) x = 1) → j ≤ G.s → ∀ (b : ℕ) (hb : j + b = G.s + 1) (x : ((G.S.T (Fin D.R.t)).lev j b hb).J) (h : GA D (c.V j)), (ofSplit G.q).IsLoc (G.FY j b hb) h x.1 → ∀ f : WO (c.V j) (c.V (j + 1)) → ℂ, Vac c.ψ _ _ (v.N j) (v.N (j + 1)) (· = G.q.v) f → om (h, 1) (comb c.ψ _ _ (G.eg j) f) = (((G.S.T (Fin D.R.t)).lev j b hb).lam x : ℂ) • comb c.ψ _ _ (G.eg j) f := by
  intro D c v G hc hv j χS χT ω hω μ hμ hu hS hT hj b hb x h hl f hf
  obtain ⟨μ', hT, hT'⟩ := hT
  obtain ⟨a, rfl⟩ : ∃ a, b = a + 1 := ⟨b - 1, by omega⟩
  have H : j + a = G.s := by omega
  have H' : j + 1 + a = G.s + 1 := by omega
  have hm := G.hs
  obtain ⟨Tm, hTm, hO⟩ := (_root_.GlobalTheory.LocMod.indicator_vac D G.k G.q G.unit _ _ (c.V j) (c.V (j + 1)) (G.FY j (a + 1) hb) (G.FY (j + 1) a H')
    c.ψ G.S.ψ hc.std G.char G.S.cond (v.N j) (v.N (j + 1)) (hv.sd j (by omega)) (hv.sd (j + 1) (by omega))
    (G.latY j (a + 1) hb) (G.latY (j + 1) a H')).2 f hf
  obtain ⟨O, hO1, -⟩ := GlobalTheory.LocMod.PinModel.exists_isOne (k := G.k) (Y := XIx (Fin D.R.k) (Fin D.R.t) (j + 1) ⊕ Fin a)
    (Y' := XIx (Fin D.R.k) (Fin D.R.t) j ⊕ Fin (a + 1))
  have R : (G.S.T (Fin D.R.t)).Regular := Chain.ofType_regular _ _ _ _ _
  let Φ : SB (Matrix (XIx (Fin D.R.k) (Fin D.R.t) (j + 1) ⊕ Fin a) (XIx (Fin D.R.k) (Fin D.R.t) j ⊕ Fin (a + 1)) G.k) :=
    ⟨(G.S.T (Fin D.R.t)).Phi j a H, R.1 j a H⟩
  have e1 : Tm Φ = comb c.ψ _ _ (G.eg j) f := by
    rw [← hO O hO1]
    exact (G.eg_is j a H).2 Tm hTm O Φ hO1 rfl
  have hd := valuation_det_of_mem_stabLat ((R.2.2 j (a + 1) hb).2.2 x.2)
  have e2 : ((μ (j + 1))⁻¹ * μ'⁻¹) (Matrix.GeneralLinearGroup.det x.1) = 1 := by
    rw [MonoidHom.mul_apply, MonoidHom.inv_apply, MonoidHom.inv_apply, ← mul_inv, mul_comm, hT' _ hd, inv_one]
  have key := _root_.GlobalTheory.LocOm.omLoc D G.k (ofSplit G.q) c.ψ _ _ χS χT ω hω (μ (j + 1))⁻¹ μ' (isComp_inv _ hS) hT _ _
    (G.FY j (a + 1) hb) (G.FY (j + 1) a H') Tm hTm h x.1 1 1 hl (isLoc_one _ _) Φ
    ((((G.S.T (Fin D.R.t)).lev j (a + 1) hb).lam x : ℂ) • Φ) (by
      rw [e2, inv_inv, Units.val_one, one_smul]
      exact (om_Phi G.S (Fin D.R.t) μ hμ hu j a H hb x).symm)
  rw [← e1, key, map_smul]

end GlobalTheory.SeeSaw.LocSrc
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SeeSawTotalConstantRatioOfFactorRatios
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.FinPl GlobalTheory.Fam ValuativeRel IsLocalRing
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.SeeSaw

theorem ratio_total_unitRatio_of_parts : ∀ (D : D7) (c : Comm D) (v : VCom c) (𝒯 : Type) (t : 𝒯 → Tup c) (w : ∀ s, VTup (t s)) (S : 𝒯 → ℕ → Prop) (s₀ : 𝒯), (∀ s, (t s).Is) → (∀ s, CVEq v (w s)) → (∀ j σ h, v.kap j σ h ≠ 0) → (∀ j, v.cG j ≠ 0) → (∀ s j, j < D.R.m → UnitRatio (S s) ((w s).sc j) ((w s₀).sc j) ∧ UnitRatio (S s) ((t s).cK j) ((t s₀).cK j)) → (∀ s j ρ, j + 2 * ρ + 2 = D.R.m → UnitRatio (S s) ((w s).cT j) ((w s₀).cT j) ∧ UnitRatio (S s) ((w s).cQ j / ((t s).cI j * (t s).cI (j + 1))) ((w s₀).cQ j / ((t s₀).cI j * (t s₀).cI (j + 1)))) → (∀ s, UnitRatio (S s) (t s).cP (t s₀).cP) → ∀ n, 2 * n = D.R.m → ∀ s, (t s).cTop n ≠ 0 ∧ (t s).cBot ≠ 0 ∧ UnitRatio (S s) ((t s).cTop n / (t s).cBot) ((t s₀).cTop n / (t s₀).cBot) := by
  intro D c v 𝒯 t w S s₀ hIs hCV hkap hcG hscK hTQ hcP n hn s
  obtain ⟨hrefl, hmul, -, hprod⟩ := GlobalTheory.Fam.unitRatio_laws (S s)
  have split : ∀ (f : ℕ → ℂ) (k : ℕ), ∏ j ∈ Finset.range (2 * k), f j =
      ∏ i ∈ Finset.range k, (f (2 * i) * f (2 * i + 1)) := by
    intro f k
    induction k with
    | zero => simp
    | succ k ih =>
      rw [show 2 * (k + 1) = 2 * k + 1 + 1 by ring, Finset.prod_range_succ, Finset.prod_range_succ, ih,
        Finset.prod_range_succ, mul_assoc]
  have hIs' : ∀ s j, j < D.R.m → (t s).cI j ≠ 0 := fun s j hj => (hIs s).cI j hj
  have hκ : ∀ i, i < n → ∃ κ : ℂ, κ ≠ 0 ∧ ∀ s, (t s).cV (2 * i) =
      κ * ((w s).sc (2 * i) * (w s).sc (2 * i + 1)) * (w s).cQ (2 * i) * v.cG (2 * i) * (w s).cT (2 * i) := by
    intro i hi
    by_cases hlast : i + 1 = n
    · refine ⟨1, one_ne_zero, fun s => ?_⟩
      rw [one_mul]
      exact (hCV s).2 (2 * i) (by omega)
    · exact ⟨v.kap (2 * i) (n - i - 2) (by omega), hkap _ _ _, fun s => (hCV s).1 (2 * i) (n - i - 2) (by omega)⟩
  have hB : ∀ i, i < n → UnitRatio (S s)
      ((t s).cV (2 * i) * (t s).cK (2 * i) * (t s).cK (2 * i + 1) / ((t s).cI (2 * i) * (t s).cI (2 * i + 1)))
      ((t s₀).cV (2 * i) * (t s₀).cK (2 * i) * (t s₀).cK (2 * i + 1) / ((t s₀).cI (2 * i) * (t s₀).cI (2 * i + 1))) := by
    intro i hi
    obtain ⟨κ, hκ0, hκs⟩ := hκ i hi
    have hK0 : κ * v.cG (2 * i) ≠ 0 := mul_ne_zero hκ0 (hcG _)
    have hform : ∀ s', (t s').cV (2 * i) * (t s').cK (2 * i) * (t s').cK (2 * i + 1) /
        ((t s').cI (2 * i) * (t s').cI (2 * i + 1)) =
        κ * v.cG (2 * i) *
          ((w s').sc (2 * i) * (w s').sc (2 * i + 1) * (w s').cT (2 * i) *
            ((w s').cQ (2 * i) / ((t s').cI (2 * i) * (t s').cI (2 * i + 1))) *
            ((t s').cK (2 * i) * (t s').cK (2 * i + 1))) := by
      intro s'
      rw [hκs s']
      ring
    rw [hform s, hform s₀]
    have hsc1 := (hscK s (2 * i) (by omega)).1
    have hsc2 := (hscK s (2 * i + 1) (by omega)).1
    have homogComponent_comm_first_action := (hscK s (2 * i) (by omega)).2
    have homogComponent_comm_second_action := (hscK s (2 * i + 1) (by omega)).2
    have hcT := (hTQ s (2 * i) (n - i - 1) (by omega)).1
    have hcQ := (hTQ s (2 * i) (n - i - 1) (by omega)).2
    exact (hmul _ _ _ _ (hrefl _ hK0)
      (hmul _ _ _ _ (hmul _ _ _ _ (hmul _ _ _ _ (hmul _ _ _ _ hsc1 hsc2).1 hcT).1 hcQ).1
        (hmul _ _ _ _ homogComponent_comm_first_action homogComponent_comm_second_action).1).1).1
  have hq : ∀ s', (t s').cTop n / (t s').cBot = (∏ i ∈ Finset.range n,
      ((t s').cV (2 * i) * (t s').cK (2 * i) * (t s').cK (2 * i + 1) / ((t s').cI (2 * i) * (t s').cI (2 * i + 1)))) *
      (t s').cP := by
    intro s'
    unfold Tup.cTop Tup.cBot
    rw [← hn, split (fun j => (t s').cI j) n, Finset.prod_div_distrib]
    ring
  have hall : UnitRatio (S s) ((t s).cTop n / (t s).cBot) ((t s₀).cTop n / (t s₀).cBot) := by
    rw [hq s, hq s₀]
    exact (hmul _ _ _ _ (hprod ℕ (Finset.range n) _ _ fun i hi => hB i (Finset.mem_range.mp hi)) (hcP s)).1
  have hbot : (t s).cBot ≠ 0 := by
    unfold Tup.cBot
    exact Finset.prod_ne_zero_iff.mpr fun j hj => hIs' s j (Finset.mem_range.mp hj)
  have hne := (hmul _ _ _ _ hall hall).2.2
  refine ⟨fun h0 => hne ?_, hbot, hall⟩
  rw [h0, zero_div]

end GlobalTheory.SeeSaw
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SeeSawUnfoldedDataEqKernelDataAtLevelStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.FinPl
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.seeSaw_unfoldedData_eq_kernelData_at_level : ∀ (D : D7) (c : Comm D) (v : VCom c) (t : Tup c) (w : VTup t), c.Is → v.Is → t.Is → VForm v w → GValue (t := t) v → TLaw v w → FlatLaw D → BiAct D → ∀ j σ h Ψ₁ Ψ₂, Vac c.ψ _ _ (v.N j) (v.N (j + 1)) (fun _ => True) Ψ₁ → Vac c.ψ _ _ (v.N (j + 1)) (v.N (j + 1 + 1)) (fun _ => True) Ψ₂ → ∀ φ : t.Ch j → GA D (c.X j) → ℂ, (∀ α, φ α ∈ v.RamAd j) → ∀ β, (∑ α, ∑ γ, c.bl j (t.kom j) (t.kom (j + 1)) (φ α) (biComb c.ψ _ _ _ (w.dQ j α γ) (w.dQ (j + 1) γ β) (c.ctr j σ h (t.sBF j (σ + 1) h) (t.sFB j σ h) (comb c.ψ _ _ (v.eG j) Ψ₁) (comb c.ψ _ _ (v.eG (j + 1)) Ψ₂)))) = (v.cG j * w.cT j) • t.two j (fun α => v.Sad j (φ α)) ((v.op j).app c.ψ (c.ctr j σ h (t.sBF j (σ + 1) h) (t.sFB j σ h) Ψ₁ Ψ₂)) β := by
  first | exact @GlobalTheory.SeeSawRhs.unfolded_eq_kernel_data | exact GlobalTheory.SeeSawRhs.unfolded_eq_kernel_data | (intros; apply GlobalTheory.SeeSawRhs.unfolded_eq_kernel_data <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SeesawCombinationsCompositeNeZeroOfVacuum
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.LocMod GlobalTheory.MiS ValuativeRel
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Fam

noncomputable section

namespace GlobalTheory.CombNonzero

variable {D : D7} {ψ : AddChar (AF D.host.F) ℂ} {S T : HSp D} {M : GlobalTheory.FinPl.Lat S} {M' : GlobalTheory.FinPl.Lat T}

theorem comb_o_ne_zero (hψ : IsStdChar D ψ (-1)) (hM : IsSelfDualC S M) (hM' : IsSelfDualC T M') (L : LocPl ψ S T M M')
    {h : WO S T → ℂ} (hv : GlobalTheory.FinPl.Vac ψ S T M M' (· = L.q.v) h) (h0 : h ≠ 0) : comb ψ S T L.o h ≠ 0 := by
  classical
  set p : Place D L.k := ofSplit L.q with hp
  obtain ⟨ε, hε, hs⟩ := L.q.above
  obtain ⟨s1, s2, -⟩ := L.q.split
  have hsc := GlobalTheory.PlaceModelSum.isSplitIdem_cA L.q.split
  have c1 : cA D L.q.e * cA D L.q.e = cA D L.q.e := by rw [← map_mul, s1]
  have he1 : algebraMap (AF D.host.F) (AE D) ε * L.q.e = L.q.e := by
    rw [← hs]; linear_combination s1 + s2
  have he2 : algebraMap (AF D.host.F) (AE D) ε * cA D L.q.e = cA D L.q.e := by
    rw [← hs]; linear_combination c1 + s2

  have fix : ∀ a : AE D, IsSplitIdem D a → algebraMap (AF D.host.F) (AE D) ε * a = a →
      ∀ u ∈ (latO S T (M : Set _) (M' : Set _) fun _ => True) ⊓ GlobalTheory.PlaceModel.half S T a, heisO ψ S T u h = h := by
    intro a ha hea u hu
    have hm := GlobalTheory.PlaceModel.idem_smul_mem hε ha.1 hea (AddSubgroup.mem_inf.1 hu).1
    have hua : a • u = u := (GlobalTheory.PlaceModel.mem_half S T).1 (AddSubgroup.mem_inf.1 hu).2
    rw [hua] at hm
    exact hv.2.2 a ha u (AddSubgroup.mem_inf.1 hm).1 ((GlobalTheory.PlaceModel.isHalf_iff S T).2 (AddSubgroup.mem_inf.1 hm).2)
  have hO : GlobalTheory.PlaceModelSum.IsOrthSum L.q.e :=
    ⟨Unit, {()}, fun _ => L.q.e, fun _ _ => L.q.split, fun _ _ _ _ hne => absurd rfl hne, by simp⟩
  obtain ⟨T', hT'⟩ := GlobalTheory.FlatVecExist.exists_model_of_fix hψ hM hM' hO s2 (fix _ L.q.split he1) (fix _ hsc he2)
  let Tm := T'.comp (GlobalTheory.LocMod.Witness.ext p L.FS L.FT)
  have hTm : p.IsModel ψ L.FS L.FT Tm := by
    refine ⟨fun Φ => ?_, fun x Φ Φ' e => ?_, fun y hy Φ Φ' e => ?_⟩
    · exact GlobalTheory.SchrTheta.isTheta_placeModel D ψ hψ S T M M' hM hM' L.q.e s1 (GlobalTheory.PlaceModelSum.infPart_split L.q.split)
        h hv.1 T' hT' _ (GlobalTheory.LocMod.Witness.ext_sb p L.FS L.FT hM hM' Φ)
    · refine Eq.trans (congrArg T' ?_) (hT'.trans _ (GlobalTheory.LocMod.Witness.ext_sb p L.FS L.FT hM hM' Φ) _
        (GlobalTheory.LocMod.Witness.up_half p L.FS L.FT x))
      funext t
      rw [GlobalTheory.LocMod.Witness.ext_apply, GlobalTheory.LocMod.Witness.ext_apply, GlobalTheory.LocMod.Witness.down_add,
        GlobalTheory.LocMod.Witness.down_up, e]
      exact if_congr (GlobalTheory.LocMod.Witness.half_add (GlobalTheory.LocMod.Witness.up_half p L.FS L.FT x)).symm rfl rfl
    · refine Eq.trans (congrArg T' ?_) (hT'.modul _ (GlobalTheory.LocMod.Witness.ext_sb p L.FS L.FT hM hM' Φ) _ hy)
      funext t
      rw [GlobalTheory.LocMod.Witness.ext_apply, GlobalTheory.LocMod.Witness.ext_apply, e]
      split_ifs with ht
      · rw [GlobalTheory.LocMod.Witness.up_down p L.FS L.FT ht]
      · rw [mul_zero]
  let Φ₀ : SB (Matrix L.Y L.Y' L.k) := ⟨_, GlobalTheory.LatIndSB.indicator_latO_mem_SB D ψ S T M M' hM hM' L⟩
  have hΦ₀ : Tm Φ₀ = h := by
    have e1 : GlobalTheory.LocMod.Witness.ext p L.FS L.FT Φ₀ = (1 : ℂ) • halfInd L.q.e (latO S T (M : Set _) (M' : Set _) fun _ => True) := by
      funext t
      rw [one_smul, GlobalTheory.LocMod.Witness.ext_apply, halfInd]
      by_cases ht : IsHalf p.e t
      · rw [if_pos ht]
        show Set.indicator {x | p.up L.FS L.FT x ∈ latO S T (M : Set _) (M' : Set _) (· = L.q.v)} (fun _ => (1 : ℂ)) (p.down L.FS L.FT t) = _
        rw [Set.indicator_apply]
        refine if_congr ?_ rfl rfl
        change p.up L.FS L.FT (p.down L.FS L.FT t) ∈ latO S T (M : Set _) (M' : Set _) (· = L.q.v) ↔ _
        rw [GlobalTheory.LocMod.Witness.up_down p L.FS L.FT ht, and_iff_left (show IsHalf L.q.e t from ht)]
        refine ⟨fun hm => GlobalTheory.PlaceModel.latO_le_top _ hm, fun hm => ?_⟩
        have h2 := (GlobalTheory.PlaceModel.idem_smul_mem hε s1 he1 hm).1
        have h3 : L.q.e • t = t := (GlobalTheory.PlaceModel.mem_half S T).1 ((GlobalTheory.PlaceModel.isHalf_iff S T).1 ht)
        rw [h3] at h2
        exact h2
      · rw [if_neg ht, if_neg fun hh => ht hh.2]
    change T' (GlobalTheory.LocMod.Witness.ext p L.FS L.FT Φ₀) = h
    rw [e1]
    exact hT'.vac
  obtain ⟨O, hO, hO1⟩ := GlobalTheory.LocMod.PinModel.exists_isOne (k := L.k) (Y := L.Y) (Y' := L.Y')
  have hOne : Tm O = comb ψ S T L.o (Tm Φ₀) := L.o_is Tm hTm Φ₀ O hO rfl
  intro hc
  rw [hΦ₀, hc] at hOne
  have hO0 : O ≠ 0 := by rintro rfl; simp at hO1
  have hz := (GlobalTheory.LocModU.localModel_uniq_transport_exist D L.k p L.Y L.Y' S T L.FS L.FT ψ hψ).1 Tm ((0 : ℂ) • Tm) hTm
    (GlobalTheory.LocMod.Witness.isModel_smul p hTm 0) O hO0 (by rw [hOne]; simp)
  apply h0
  rw [← hΦ₀, hz]
  simp

theorem vac_mono (hψ : IsStdChar D ψ (-1)) (hM : IsSelfDualC S M) (hM' : IsSelfDualC T M')
    {P Q : GlobalTheory.FinPl.Pl D → Prop} (hQP : ∀ v, Q v → P v) {f : WO S T → ℂ}
    (hf : GlobalTheory.FinPl.Vac ψ S T M M' P f) : GlobalTheory.FinPl.Vac ψ S T M M' Q f := by
  have hiff := (GlobalTheory.DisjComb.main D ψ hψ S T Q (fun v => P v ∧ ¬ Q v) (fun v hq hp => hp.2 hq)).2.2.2.2 M M' f hM hM'
  have e : (fun v => Q v ∨ (P v ∧ ¬ Q v)) = P := by
    funext v
    apply propext
    constructor
    · rintro (hq | hq)
      · exact hQP v hq
      · exact hq.1
    · intro hp
      by_cases hq : Q v
      · exact Or.inl hq
      · exact Or.inr ⟨hp, hq⟩
  rw [e] at hiff
  exact (hiff.1 hf).1

theorem fold_vac (hψ : IsStdChar D ψ (-1)) {n : ℕ} (Lp : Fin n → LocPl ψ S T M M') (P : GlobalTheory.FinPl.Pl D → Prop)
    (l : List (Fin n)) (hl : ∀ i ∈ l, ¬ P (Lp i).q.v) (g : WO S T → ℂ) (hg : GlobalTheory.FinPl.Vac ψ S T M M' P g) :
    GlobalTheory.FinPl.Vac ψ S T M M' P (l.foldr (fun i g' => comb ψ S T (Lp i).o g') g) := by
  induction l with
  | nil => exact hg
  | cons i l ih =>
    rw [List.foldr_cons]
    have hc : GlobalTheory.FinPl.CombAt (· = (Lp i).q.v) (Lp i).o := fun u hu =>
      GlobalTheory.FinPl.SplitHalfSuppImp.mxAt_of_isHalf D _ (Lp i).q u ((Lp i).o_at u hu)
    refine ((GlobalTheory.DisjComb.main D ψ hψ S T (· = (Lp i).q.v) P
      (fun v hv hp => hl i List.mem_cons_self (hv ▸ hp))).2.1 _ hc).2 M M' _ ?_
    exact ih fun j hj => hl j (List.mem_cons_of_mem _ hj)

theorem fold_ne_zero (hψ : IsStdChar D ψ (-1)) (hM : IsSelfDualC S M) (hM' : IsSelfDualC T M') {n : ℕ}
    (Lp : Fin n → LocPl ψ S T M M') (hinj : Function.Injective fun i => (Lp i).q.v) (l : List (Fin n)) (hnd : l.Nodup)
    (g : WO S T → ℂ) (hg : GlobalTheory.FinPl.Vac ψ S T M M' (fun v => ∃ i ∈ l, (Lp i).q.v = v) g) (g0 : g ≠ 0) :
    l.foldr (fun i g' => comb ψ S T (Lp i).o g') g ≠ 0 := by
  induction l with
  | nil => exact g0
  | cons i l ih =>
    rw [List.foldr_cons]
    obtain ⟨hi, hnd'⟩ := List.nodup_cons.1 hnd
    refine comb_o_ne_zero hψ hM hM' (Lp i) ?_ (ih hnd' (vac_mono hψ hM hM'
      (fun v ⟨j, hj, e⟩ => ⟨j, List.mem_cons_of_mem _ hj, e⟩) hg))
    refine fold_vac hψ Lp _ l (fun j hj e => hi ?_) g (vac_mono hψ hM hM' (fun v hv => ⟨i, List.mem_cons_self, hv.symm⟩) hg)
    have : j = i := hinj e
    exact this ▸ hj

theorem main : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ (S T : HSp D) (M : GlobalTheory.FinPl.Lat S) (M' : GlobalTheory.FinPl.Lat T), IsSelfDualC S M → IsSelfDualC T M' → ∀ (n : ℕ) (Lp : Fin n → LocPl ψ S T M M'), (Function.Injective fun i => (Lp i).q.v) → ∀ g, GlobalTheory.FinPl.Vac ψ S T M M' (fun _ => True) g → g ≠ 0 → (List.finRange n).foldr (fun i g' => comb ψ S T (Lp i).o g') g ≠ 0 := by
  intro D ψ hψ S T M M' hM hM' n Lp hinj g hg g0
  exact fold_ne_zero hψ hM hM' Lp hinj _ (List.nodup_finRange n) g (vac_mono hψ hM hM' (fun _ _ => trivial) hg) g0

end GlobalTheory.CombNonzero
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SeesawFirstFlatMapSupportAtLevelPlaceStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.FinPl
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.seesaw_first_flatMap_support_at_level_place : ∀ {D : D7} {c : Comm D} {v : VCom c}, c.Is → v.Is → GlobalTheory.LocMod.GSupp1 D → ∀ (t : Tup c), t.Is → ∀ (Gi : GLoc v), Gi.Chars t → ∀ (j σ : ℕ) (h : j + 2 * (σ + 1) + 2 = D.R.m) (F : WO (c.V j) (c.V (j + 1)) → ℂ), Vac c.ψ _ _ (v.N j) (v.N (j + 1)) (· = Gi.q.v) F → ∀ (x : GA D (c.V (j + 1))), SuppAt Gi.q.e (c.V (j + 1)) x → flatBF (t.sBF j (σ + 1) h) (t.om j (1, x) (comb c.ψ _ _ (Gi.eg j) F)) ≠ 0 → ∃ r ∈ jacGrp (c.jac j (σ + 1) h).d, SuppAt Gi.q.e (c.V (j + 1)) r ∧ ∃ u uk, (GlobalTheory.LocMod.ofSplit Gi.q).IsLoc (Gi.FY (j + 1) (2 * σ + 1 + 1) (by have := Gi.hs; omega)) u uk ∧ uk ∈ ((Gi.S.T (Fin D.R.t)).lev (j + 1) (2 * σ + 1 + 1) (by have := Gi.hs; omega)).J ∧ x = r * u := by
  first | exact @GlobalTheory.SeeSaw.GSuppFirst.gsupp1_at | exact GlobalTheory.SeeSaw.GSuppFirst.gsupp1_at | (intros; apply GlobalTheory.SeeSaw.GSuppFirst.gsupp1_at <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SplitFrameGLFiniteMatrixOffPlaceEqOneStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Forms Formalism.L2.Ker
open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.SeeSaw GlobalTheory.LatPair GlobalTheory.SplitWeil
open GlobalTheory.Unf GlobalTheory.Grow GlobalTheory.FinPl ValuativeRel IsLocalRing
open scoped TensorProduct Pointwise
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.AdForm

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.splitFrameGL_finiteMatrix_offPlace_eq_one : ∀ (D : D7) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (p : SplitPt D k) (S : HSp D) (n : Type) [Fintype n] [DecidableEq n] (β : Frame p S n) (g : GL n k) (m : ℕ) (hm : S.rank = m) (x : GL (Fin m) (EF D)), x.1 = finM S hm (β.gl g) → ∀ v : Pl D, v ≠ p.v → Formalism.UG.bc (Formalism.UG.prV (E := D.host.E) v) x = 1 := by
  first | exact @GlobalTheory.StabOff.bc_prV_finM_eq_one | exact GlobalTheory.StabOff.bc_prV_finM_eq_one | (intros; apply GlobalTheory.StabOff.bc_prV_finM_eq_one <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SplitPlaceLocalGroupClosedEmbeddingIntegralStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.SeeSaw GlobalTheory.LocMod GlobalTheory.QPl ValuativeRel
open GlobalTheory.PosOne (toOne Covers TriPos)
open GlobalTheory.IndefiniteRowSideFullHecke.FourierJacobiAverage (app HasTensorVal fl opEFJ IsQuotIntFJ RFJ)
open GlobalTheory.IndefiniteRowSideFullHecke.FramePositiveSum (IsCO)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.splitPlace_local_group_closedEmbedding_integral : ∀ (D : D7) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (q : GlobalTheory.FinPl.SplitPt D k) (V : HSp D) (Y : Type) [Fintype Y] [DecidableEq Y] (F : Frame k V.rank Y) (gl : GL Y k →* GA D V), (∀ g, (ofSplit q).IsLoc F (gl g) g) → Topology.IsClosedEmbedding gl ∧ gl.range = GlobalTheory.FinPl.grpAt V (· = q.v) ∧ (∀ x : GA D V, ∃! g, x * (gl g)⁻¹ ∈ GlobalTheory.FinPl.grpOff V (· = q.v)) ∧ (∀ g, ∀ y ∈ GlobalTheory.FinPl.grpOff V (· = q.v), gl g * y = y * gl g) ∧ ∀ L : GlobalTheory.FinPl.Lat V, IsSelfDualC V L → (∀ y : Y → k, (∀ i, y i ∈ 𝒪[k]) ↔ (fun i => q.sec ((F.β *ᵥ y) i)) ∈ GlobalTheory.FinPl.latV V L (· = q.v)) → ∀ g, g ∈ KO k Y ↔ GlobalTheory.FinPl.InK V L (· = q.v) (gl g) := by
  first | exact @GlobalTheory.LocGl.local_group | exact GlobalTheory.LocGl.local_group | (intros; apply GlobalTheory.LocGl.local_group <;> assumption)
end

