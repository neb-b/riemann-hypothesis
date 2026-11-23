module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.Bundle0007
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0447
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.AdelicPointComponentsAtPlacesLatticesVacua
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.MemHomLatticeCompletionIffSupportedMaps
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0632
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0595
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0533
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0187
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0565
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0027
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0026
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleDiscreteSeriesOfHasParam
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HasDRepIffHasDerivAt
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.WeilRepresentationUnitaryPair
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0546
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0120
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0029
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0341
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0116
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0100
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0624
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0630
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0465

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.BesselJacobiSuperdiagonalEntriesAtPlace
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows GlobalTheory.Asc
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (Lat idAt idOff intAt grpAt grpOff MxAt latV latA InK MonoAt OrthAt PrimAt ColsAt)
open scoped nonZeroDivisors ContDiff
open GlobalTheory.AscFin


open GlobalTheory.SeeSaw (idV FI dI) in
theorem GlobalTheory.AscFin.coef_superdiag : OnStd fun {D} _ _ {sc} {G} W F => ∀ ρ (h : 2 * ρ + 2 ≤ D.R.m)
    (M : WO (G.V (.grid (2 * ρ + 2) 0)) (G.V (.grid (2 * ρ + 1) 0))) (𝔠 : GlobalTheory.SeeSaw.FI D), 𝔠 ≠ 0 →
    ∀ v : GlobalTheory.FinPl.Pl D, (∀ y ∈ latV _ (G.Λ (.grid (2 * ρ + 2) 0)) (· = v), ∀ s ∈ GlobalTheory.SeeSaw.idV 𝔠 v,
      s • (M *ᵥ y) ∈ latV _ (G.Λ (.grid (2 * ρ + 1) 0)) (· = v)) → ∀ i j : Fin ρ, j.1 = i.1 + 1 →
    GlobalTheory.FinPlLoc.idem D (· = v) * ((F.dJ ρ h).pX ⬝ (M ⬝ (F.dB ρ h).jX)) i j ∈
      GlobalTheory.SeeSaw.idV (FractionalIdeal.spanSingleton _ D.host.xi0 * G.pl.stAbar sc * 𝔠⁻¹) v := by
  intro D hD T L μ0 hL sc G W M0 hM0 F hF ρ h M 𝔠 h𝔠 v hM i j hij
  obtain ⟨-, f2, -, -, -, -, -⟩ := _root_.GlobalTheory.SeeSaw.idV_props D W.ψ W.ψ_std v
  have hmono : MonoAt (F.dJ ρ h) (G.Λ (.grid (2 * ρ + 1) 0)) (G.Λ (.core (2 * ρ + 1))) v :=
    ((_root_.GlobalTheory.AscFin.GridLat.lattices_grid D hD T L μ0 hL sc G W M0 hM0 F hF).2.1 ρ h).2.1 v |>.2
  obtain ⟨hcB, heB, -⟩ := hF.hB ρ h
  obtain ⟨hcJ, heJ, -⟩ := hF.hJ ρ h
  have hlatB := G.sp.colLat (2 * ρ + 2) (by omega) h
  have hlatJ := G.sp.colLat (2 * ρ + 1) (by omega) (by omega)
  have hx : ∀ n : ℕ, (-D.host.xi0) ^ n ≠ 0 := fun n => pow_ne_zero _ (neg_ne_zero.2 cmHost_imaginaryGenerator_ne_zero)
  let 𝔟B : Fin ρ → FI D := fun p => FractionalIdeal.spanSingleton _ (((-D.host.xi0) ^ (p.1 + 1))⁻¹) *
    stairId (G.pl.stA sc) (G.pl.stAbar sc) (2 * ρ + 2 - 1) (Fin.castLE (by omega) p)
  let 𝔟J : Fin ρ → FI D := fun p => FractionalIdeal.spanSingleton _ (((-D.host.xi0) ^ (p.1 + 1))⁻¹) *
    stairId (G.pl.stA sc) (G.pl.stAbar sc) (2 * ρ + 1 - 1) (Fin.castLE (by omega) p)
  have lineB : ∀ (p : Fin ρ) (a : AE D), GlobalTheory.FinPl.colMul (F.dB ρ h).jX p a ∈ latV _ (G.Λ (.grid (2 * ρ + 2) 0)) (· = v) ↔
      a ∈ idV (𝔟B p) v := by
    intro p a
    have e1 : GlobalTheory.FinPl.colMul (F.dB ρ h).jX p a = fun k => a * incA D ((-D.host.xi0) ^ (p.1 + 1) *
        (G.colDec (2 * ρ + 2) (by omega) h).a k (Fin.castLE (by omega) p)) := by
      funext k
      simp only [GlobalTheory.FinPl.colMul, HypDec.jX, rat, Matrix.map_apply, heB, colsOf]
    rw [e1]
    have e2 : G.Λ (.grid (2 * ρ + 2) 0) = _ := hlatB
    rw [e2]
    exact GlobalTheory.StairLine.line_mem_iff _ _ _ _ (by simp only [Fin.coe_castLE]; omega) (hx _) v a
  have lineJ : ∀ (p : Fin ρ) (a : AE D), GlobalTheory.FinPl.colMul (F.dJ ρ h).jX p a ∈ latV _ (G.Λ (.grid (2 * ρ + 1) 0)) (· = v) ↔
      a ∈ idV (𝔟J p) v := by
    intro p a
    have e1 : GlobalTheory.FinPl.colMul (F.dJ ρ h).jX p a = fun k => a * incA D ((-D.host.xi0) ^ (p.1 + 1) *
        (G.colDec (2 * ρ + 1) (by omega) (by omega)).a k (Fin.castLE (by omega) p)) := by
      funext k
      simp only [GlobalTheory.FinPl.colMul, HypDec.jX, rat, Matrix.map_apply, heJ, colsOf]
    rw [e1]
    have e2 : G.Λ (.grid (2 * ρ + 1) 0) = _ := hlatJ
    rw [e2]
    exact GlobalTheory.StairLine.line_mem_iff _ _ _ _ (by simp only [Fin.coe_castLE]; omega) (hx _) v a
  have hN : ((G.pl.modul sc : Ideal (𝓞 D.host.E)) : FI D) ≠ 0 :=
    FractionalIdeal.coeIdeal_ne_zero.2 (G.pl.modul_ne_bot sc)
  have hN' : ((G.pl.modulBar sc : Ideal (𝓞 D.host.E)) : FI D) ≠ 0 :=
    FractionalIdeal.coeIdeal_ne_zero.2 (GlobalTheory.AscFin.PrimStd.modulBar_ne_bot G.pl sc)
  have hA : G.pl.stA sc ≠ 0 := mul_ne_zero (GlobalTheory.CuspCharLattice.host_AA_ne_zero _) (inv_ne_zero hN')
  have hAb : G.pl.stAbar sc ≠ 0 := mul_ne_zero (GlobalTheory.Member.LatSelfDual.AAbar_ne_zero D) (inv_ne_zero hN)
  have hsp : ∀ n : ℕ, FractionalIdeal.spanSingleton (𝓞 D.host.E)⁰ (((-D.host.xi0) ^ n)⁻¹) ≠ 0 := fun n => by
    rw [Ne, FractionalIdeal.spanSingleton_eq_zero_iff]; exact inv_ne_zero (hx _)
  have hb0B : ∀ p, 𝔟B p ≠ 0 := fun p => mul_ne_zero (hsp _) (by
    unfold stairId; exact mul_ne_zero (pow_ne_zero _ hA) (inv_ne_zero (pow_ne_zero _ hAb)))
  have hb0J : ∀ p, 𝔟J p ≠ 0 := fun p => mul_ne_zero (hsp _) (by
    unfold stairId; exact mul_ne_zero (pow_ne_zero _ hA) (inv_ne_zero (pow_ne_zero _ hAb)))
  have hrat : 𝔟J i * (𝔟B j)⁻¹ = FractionalIdeal.spanSingleton _ D.host.xi0 * G.pl.stAbar sc := by
    rw [mul_inv_eq_iff_eq_mul₀ (hb0B j)]
    have hneg : FractionalIdeal.spanSingleton (𝓞 D.host.E)⁰ (-D.host.xi0) = FractionalIdeal.spanSingleton _ D.host.xi0 :=
      FractionalIdeal.spanSingleton_eq_spanSingleton.2 ⟨-1, by simp⟩
    have e2 : ((-D.host.xi0) ^ (i.1 + 1))⁻¹ = -D.host.xi0 * ((-D.host.xi0) ^ (j.1 + 1))⁻¹ := by
      have hξ : -D.host.xi0 ≠ 0 := neg_ne_zero.2 cmHost_imaginaryGenerator_ne_zero
      rw [hij]
      field_simp
      ring
    show FractionalIdeal.spanSingleton _ _ * stairId _ _ _ _ = _ * (FractionalIdeal.spanSingleton _ _ * stairId _ _ _ _)
    rw [e2, ← FractionalIdeal.spanSingleton_mul_spanSingleton, hneg]
    unfold stairId
    simp only [Fin.coe_castLE]
    have e3 : 2 * ρ + 1 - 1 - i.1 = 2 * ρ + 2 - 1 - j.1 := by omega
    rw [e3, hij, pow_succ (G.pl.stAbar sc) (i.1 + 1), mul_inv]
    conv_lhs => rw [show (G.pl.stAbar sc ^ (i.1 + 1))⁻¹ = G.pl.stAbar sc * ((G.pl.stAbar sc ^ (i.1 + 1))⁻¹ * (G.pl.stAbar sc)⁻¹) by
      rw [mul_comm ((G.pl.stAbar sc ^ (i.1 + 1))⁻¹), ← mul_assoc, mul_inv_cancel₀ hAb, one_mul]]
    ring
  have hxA : GlobalTheory.FinPlLoc.idem D (· = v) * ((F.dJ ρ h).pX ⬝ (M ⬝ (F.dB ρ h).jX)) i j ∈ idAt D (· = v) :=
    Ideal.mul_mem_right _ _ (GlobalTheory.FinPlLoc.idem_mem_idAt _)
  rw [← hrat]
  refine (f2 𝔠 _ h𝔠 (mul_ne_zero (hb0J i) (inv_ne_zero (hb0B j))) _ hxA).1 ?_
  intro s hs
  have hsA : s ∈ idAt D (· = v) := GlobalTheory.SeeSaw.LiftModel.idV_le_idAt _ _ s hs
  refine (f2 (𝔟B j) (𝔟J i) (hb0B j) (hb0J i) _ (Ideal.mul_mem_right _ _ hxA)).1 ?_
  intro c hc
  have hcA : c ∈ idAt D (· = v) := GlobalTheory.SeeSaw.LiftModel.idV_le_idAt _ _ c hc
  have h1 := hM _ ((lineB j c).2 hc) s hs
  have h3 := ((hmono _).1 h1).1 i
  rw [Matrix.mulVec_smul, GlobalTheory.FinPl.PsiUnit.mulVec_colMul, GlobalTheory.FinPl.PsiUnit.mulVec_colMul] at h3
  have h4 := (lineJ i _).1 h3
  have e4 : ((s • GlobalTheory.FinPl.colMul ((F.dJ ρ h).pX ⬝ (M ⬝ (F.dB ρ h).jX)) j c) i) =
      GlobalTheory.FinPlLoc.idem D (· = v) * ((F.dJ ρ h).pX ⬝ (M ⬝ (F.dB ρ h).jX)) i j * s * c := by
    rw [Pi.smul_apply, smul_eq_mul, GlobalTheory.FinPl.colMul]
    have hc' := (GlobalTheory.FinPlLoc.mem_idAt_iff _ c).1 hcA
    calc s * (c * _) = s * ((GlobalTheory.FinPlLoc.idem D (· = v) * c) * ((F.dJ ρ h).pX ⬝ (M ⬝ (F.dB ρ h).jX)) i j) := by rw [hc']
      _ = _ := by ring
  rwa [e4] at h4
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.BesselStepCorePieceFiniteNonzeroVacuum
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows GlobalTheory.Asc
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (Lat idAt idOff intAt grpAt grpOff MxAt latV latA InK MonoAt OrthAt PrimAt ColsAt)
open scoped nonZeroDivisors ContDiff
open GlobalTheory.AscFin

noncomputable section

namespace GlobalTheory.AscFin.CorePiece

variable {D : D7}

theorem proj_mem_adelic_lattice_of_mono {S S₀ : HSp D} {ρ : ℕ} (d : HypDec S S₀ ρ) {L : Lat S} {L₀ : Lat S₀} {P : GlobalTheory.FinPl.Pl D → Prop}
    (hL₀ : Submodule.IsLattice D.host.E L₀) (hm : ∀ v, P v → MonoAt d L L₀ v) {z : Fin S.rank → AE D}
    (hz : z ∈ latA S L P) : d.p0 *ᵥ z ∈ latA S₀ L₀ P := by
  induction hz using AddSubgroup.closure_induction with
  | mem z hz =>
    obtain ⟨β, hβi, hβ, a, ha, x, hx, rfl⟩ := hz
    set u : Fin S.rank → AE D := fun i => pairA D.host.F 0 β ⊗ₜ[D.host.F] (1 * x i) with hu
    have hu' : u ∈ latV S L P := AddSubgroup.subset_closure ⟨β, hβi, hβ, 1, rfl, x, hx, rfl⟩
    have heq : d.p0 *ᵥ (fun i => pairA D.host.F 0 β ⊗ₜ[D.host.F] (a * x i)) =
        fun k => ((1 : AF D.host.F) ⊗ₜ[D.host.F] a) * (d.p0 *ᵥ u) k := by
      funext k
      simp only [Matrix.mulVec, dotProduct, Finset.mul_sum, hu]
      refine Finset.sum_congr rfl fun i _ => ?_
      have h1 : pairA D.host.F 0 β ⊗ₜ[D.host.F] (a * x i) =
          ((1 : AF D.host.F) ⊗ₜ[D.host.F] a) * (pairA D.host.F 0 β ⊗ₜ[D.host.F] (1 * x i)) := by
        rw [Algebra.TensorProduct.tmul_mul_tmul, one_mul, one_mul]
      rw [h1]; ring
    rw [heq]
    exact GlobalTheory.FinPl.VacFlat.smul_mem_latA ha (GlobalTheory.FinPl.ExtZeroAt.wittProjectionZero_mem_latticeCompletion_of_splits d hL₀ hm hu')
  | zero => rw [Matrix.mulVec_zero]; exact zero_mem _
  | add z z' _ _ hz hz' => rw [Matrix.mulVec_add]; exact add_mem hz hz'
  | neg z _ hz => rw [Matrix.mulVec_neg]; exact neg_mem hz

theorem mem_lattice_of_extend_inclusion {V V₀ W W₀ : HSp D} {ρ σ : ℕ} (dV : HypDec V V₀ ρ) (dW : HypDec W W₀ σ)
    {LV : Lat V} {LV₀ : Lat V₀} {LW : Lat W} {LW₀ : Lat W₀}
    (hV : IsSelfDualC V LV) (hV₀ : IsSelfDualC V₀ LV₀) (hW₀ : IsSelfDualC W₀ LW₀)
    (hmV : ∀ v, MonoAt dV LV LV₀ v) (hmW : ∀ v, MonoAt dW LW LW₀ v) {u : WO V₀ W₀}
    (hu : dV.ext0 W (dW.inc0 V₀ u) ∈ latO V W (LV : Set _) (LW : Set _) fun _ => True) :
    u ∈ latO V₀ W₀ (LV₀ : Set _) (LW₀ : Set _) fun _ => True := by
  have hE : dV.ext0 W (dW.inc0 V₀ u) = dW.j0 * u * dV.p0 := by
    rw [HypDec.matrixExtendByZero_apply, HypDec.wittDecomp_inclAnisotropicHom_apply]
  rw [hE] at hu
  have hx := GlobalTheory.FinPl.LatMem.latO_mxAt hu
  have hu0 : dW.p0 * (dW.j0 * u * dV.p0) * dV.j0 = u := by
    simp only [← Matrix.mul_assoc, HypDec.p0_j0, Matrix.one_mul]
    simp only [Matrix.mul_assoc, HypDec.p0_j0, Matrix.mul_one]
  refine (GlobalTheory.FinPl.LatMem.mem_latO_iff D V₀ W₀ LV₀ LW₀ hV₀ hW₀ _ u).2 ⟨?_, fun y hy => ?_⟩
  · rw [← hu0]
    intro i j
    rw [Matrix.mul_apply]
    refine sum_mem fun l _ => ?_
    rw [Matrix.mul_apply, Finset.sum_mul]
    refine sum_mem fun k _ => ?_
    rw [mul_assoc]
    exact Ideal.mul_mem_left _ _ (Ideal.mul_mem_right _ _ (hx k l))
  · have key : (show Matrix (Fin W₀.rank) (Fin V₀.rank) (AE D) from u) *ᵥ y =
        dW.p0 *ᵥ ((dW.j0 * u * dV.p0) *ᵥ (dV.j0 *ᵥ y)) := by
      rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, hu0]
    rw [key]
    exact proj_mem_adelic_lattice_of_mono dW hW₀.1 (fun v _ => hmW v)
      (GlobalTheory.FinPl.LatMem.latO_maps hV hu (GlobalTheory.FinPl.ExtZeroAt.wittCoreInclusion_mem_latticeCompletionAtPlace dV hV.1 (fun v _ => hmV v) hy))

theorem core_fin_vac : OnStd fun {D} _ _ {sc} {G} W F => ∀ ρ (h : 2 * ρ + 2 ≤ D.R.m),
    (∀ u ∈ (pcBF W F ρ h).Γ₀, MxAt (fun _ => True) (show Mx D (G.V (.core (2 * ρ + 1))).rank (F.V₀ ρ).rank from u)) ∧
      ∃ f, VacG W.ψ (F.V₀ ρ) (G.V (.core (2 * ρ + 1))) (pcBF W F ρ h).Γ₀ f ∧ f ≠ 0 := by
  intro D hOff T L μ0 hL sc G W M hM F hF ρ h
  obtain ⟨-, hB, -⟩ := _root_.GlobalTheory.AscFin.GridLat.lattices_grid D hOff T L μ0 hL sc G W M hM F hF
  obtain ⟨hsd0, hmono, -, -⟩ := hB ρ h
  have hV : IsSelfDualC (G.V (.grid (2 * ρ + 2) 0)) (G.Λ (.grid (2 * ρ + 2) 0)) :=
    (G.isV (X := .grid (2 * ρ + 2) 0) ⟨h, Nat.zero_le _⟩ (fun j hj => by injection hj with h1 h2; omega)).sd
  have hW₀ : IsSelfDualC (G.V (.core (2 * ρ + 1))) (G.Λ (.core (2 * ρ + 1))) :=
    (G.isV (X := .core (2 * ρ + 1)) (show 2 * ρ + 1 ≤ D.R.m by omega) (fun j hj => Node.noConfusion hj)).sd
  have hle : (pcBF W F ρ h).Γ₀ ≤ latO (F.V₀ ρ) (G.V (.core (2 * ρ + 1))) (lat0 F ρ h : Set _)
      (G.Λ (.core (2 * ρ + 1)) : Set _) fun _ => True := by
    intro u hu
    refine mem_lattice_of_extend_inclusion (F.dB ρ h) (F.dJ ρ h) hV hsd0 hW₀ (fun v => (hmono v).1) (fun v => (hmono v).2) ?_
    exact GlobalTheory.RowLoc.mem_latO_negSp.1 (AddSubgroup.mem_comap.1 hu).1
  exact ⟨fun u hu => GlobalTheory.FinPl.LatMem.latO_mxAt (hle hu), _root_.GlobalTheory.AscFin.VacSub.exists_vacG_ne_zero D W.ψ W.ψ_std _ _ _ _ hsd0 hW₀ _ hle⟩

end GlobalTheory.AscFin.CorePiece

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.BesselStepDepthLatticeMulVecMemCompletion
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows GlobalTheory.Asc
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (Lat idAt idOff intAt grpAt grpOff MxAt latV latA InK MonoAt OrthAt PrimAt ColsAt)
open scoped nonZeroDivisors ContDiff
open GlobalTheory.AscFin

noncomputable section

namespace GlobalTheory.ShiftRowMul

variable {D : D7}

theorem latV_at_le_all {S : HSp D} {Λ : Lat S} {v : GlobalTheory.FinPl.Pl D} {y : Fin S.rank → AE D}
    (hy : y ∈ latV S Λ (· = v)) : y ∈ latV S Λ (fun _ => True) := by
  unfold GlobalTheory.FinPl.latV GlobalTheory.FinPl.latMul at *
  refine AddSubgroup.closure_mono ?_ hy
  rintro _ ⟨α, hα, -, a, ha, x, hx, rfl⟩
  exact ⟨α, hα, fun _ h => (h trivial).elim, a, ha, x, hx, rfl⟩

theorem smul_mem_of_idLat {n : ℕ} {I : FractionalIdeal (𝓞 D.host.E)⁰ D.host.E} (hI : I ≠ 0)
    {Λ : Submodule (𝓞 D.host.E) (Fin n → D.host.E)} {c : D.host.E} (hc : c ∈ I⁻¹) {x : Fin n → D.host.E}
    (hx : x ∈ idLat I Λ) : c • x ∈ Λ := by
  induction hx using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨t, ht, y, hy, rfl⟩ := hx
    have h1 : c * t ∈ (1 : FractionalIdeal (𝓞 D.host.E)⁰ D.host.E) := by
      rw [← inv_mul_cancel₀ hI]; exact FractionalIdeal.mul_mem_mul hc ht
    obtain ⟨r, hr⟩ := (FractionalIdeal.mem_one_iff _).1 h1
    rw [smul_smul, ← hr, algebraMap_smul]
    exact Λ.smul_mem r hy
  | zero => rw [smul_zero]; exact zero_mem _
  | add x x' _ _ h h' => rw [smul_add]; exact add_mem h h'
  | smul r x _ h =>
    rw [← algebraMap_smul D.host.E r x, smul_smul, mul_comm, ← smul_smul, algebraMap_smul]
    exact Λ.smul_mem r h

theorem smul_mem_latV {S : HSp D} {Λ : Lat S} {I : FractionalIdeal (𝓞 D.host.E)⁰ D.host.E} {v : GlobalTheory.FinPl.Pl D}
    {s : AE D} (hs : s ∈ GlobalTheory.SeeSaw.idV (D.host.AA⁻¹ * I⁻¹) v) {z : Fin S.rank → AE D}
    (hz : z ∈ latA S (idLat I Λ) (fun _ => True)) : s • z ∈ latV S Λ (· = v) := by
  have hAA : D.host.AA ≠ 0 := GlobalTheory.HostAAPartition.host_AA_ne_zero D
  induction hs using AddSubgroup.closure_induction with
  | mem s hs =>
    obtain ⟨β, hβ, hβv, b, hb, rfl⟩ := hs
    by_cases hI : I = 0
    · subst hI
      rw [_root_.inv_zero, mul_zero, FractionalIdeal.mem_zero_iff] at hb
      subst hb
      rw [TensorProduct.tmul_zero, zero_smul]; exact zero_mem _
    induction hz using AddSubgroup.closure_induction with
    | mem z hz =>
      obtain ⟨α, hα, -, a, ha, x, hx, rfl⟩ := hz
      have hba : b * a ∈ I⁻¹ := by
        have := FractionalIdeal.mul_mem_mul hb ha
        rwa [mul_comm D.host.AA⁻¹, mul_assoc, inv_mul_cancel₀ hAA, mul_one] at this
      refine AddSubgroup.subset_closure ⟨β * α, GlobalTheory.FinPl.LatMem.intAf_mul' hβ hα,
        fun w hw => by rw [map_mul, hβv w hw, zero_mul], 1, rfl, (b * a) • x, smul_mem_of_idLat hI hba hx, ?_⟩
      funext i
      simp only [Pi.smul_apply, smul_eq_mul, Algebra.TensorProduct.tmul_mul_tmul, GlobalTheory.FinPlLoc.pairA_mul, one_mul, mul_assoc]
    | zero => rw [smul_zero]; exact zero_mem _
    | add z z' _ _ h h' => rw [smul_add]; exact add_mem h h'
    | neg z _ h => rw [smul_neg]; exact neg_mem h
  | zero => rw [zero_smul]; exact zero_mem _
  | add s s' _ _ h h' => rw [add_smul]; exact add_mem h h'
  | neg s _ h => rw [neg_smul]; exact neg_mem h

end GlobalTheory.ShiftRowMul

theorem GlobalTheory.AscFin.shiftRow_smul_mulVec_mem : OnStd fun {D} _ _ {sc} {G} W F => ∀ ρ (h : 2 * ρ + 2 ≤ D.R.m) (M : WO (G.V (.grid (2 * ρ + 2) 0)) (G.V (.grid (2 * ρ + 1) 0))), M ∈ latRow G (2 * ρ + 1) → ∀ v : GlobalTheory.FinPl.Pl D, ∀ y ∈ latV _ (G.Λ (.grid (2 * ρ + 2) 0)) (· = v), ∀ s ∈ GlobalTheory.SeeSaw.idV (D.host.AA⁻¹ * (shiftId G)⁻¹) v, s • (M *ᵥ y) ∈ latV _ (G.Λ (.grid (2 * ρ + 1) 0)) (· = v) := by
  intro D hq T L μ0 hL sc G W Mv hMv F hF ρ h M hM v y hy s hs
  have hBig : M ∈ latBig G (2 * ρ + 1) :=
    _root_.GlobalTheory.RowBig.latRow_le_latBig D hq T L μ0 hL sc G W Mv hMv (2 * ρ + 1) (by omega) (by omega) hM
  have hS : IsSelfDualC (G.V (.grid (2 * ρ + 1 + 1) 0)) (G.Λ (.grid (2 * ρ + 1 + 1) 0)) :=
    (G.isV (X := .grid (2 * ρ + 1 + 1) 0) ⟨by omega, by omega⟩ (fun j h => by injection h with h1 h2; omega)).sd
  have hT := ((_root_.GlobalTheory.AscFin.GridLat.lattices_grid D hq T L μ0 hL sc G W Mv hMv F hF).1 (2 * ρ + 1) (by omega)).2.2.2
  have hmap := ((GlobalTheory.FinPl.LatMem.mem_latO_iff D _ _ _ _ hS hT (fun _ => True) M).1 hBig).2 y
    (GlobalTheory.ShiftRowMul.latV_at_le_all hy)
  exact GlobalTheory.ShiftRowMul.smul_mem_latV hs hmap
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.BesselStepLineComponentMemHomLattice
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows GlobalTheory.Asc
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (Lat idAt idOff intAt grpAt grpOff MxAt latV latA InK MonoAt OrthAt PrimAt ColsAt)
open scoped nonZeroDivisors ContDiff
open GlobalTheory.AscFin

noncomputable section

namespace GlobalTheory.LineCompLat

variable {D : D7}

theorem rat_mulVec_tmul {m n : ℕ} (M : Matrix (Fin m) (Fin n) D.host.E) (t : AF D.host.F) (x : Fin n → D.host.E) :
    rat M *ᵥ (fun l => t ⊗ₜ[D.host.F] (1 * x l)) = fun k => t ⊗ₜ[D.host.F] (1 * (M *ᵥ x) k) := by
  funext k
  simp only [Matrix.mulVec, dotProduct, rat, Matrix.map_apply, one_mul, TensorProduct.tmul_sum]
  refine Finset.sum_congr rfl fun l _ => ?_
  change ((1 : AF D.host.F) ⊗ₜ[D.host.F] M k l) * (t ⊗ₜ[D.host.F] x l) = _
  rw [Algebra.TensorProduct.tmul_mul_tmul, one_mul]

theorem rat_mulVec_latV {S S' : HSp D} {L : Lat S} {L' : Lat S'} {P : GlobalTheory.FinPl.Pl D → Prop}
    (M : Matrix (Fin S'.rank) (Fin S.rank) D.host.E) (hM : ∀ x ∈ L, M *ᵥ x ∈ L')
    {y : Fin S.rank → AE D} (hy : y ∈ latV S L P) : rat M *ᵥ y ∈ latV S' L' P := by
  induction hy using AddSubgroup.closure_induction with
  | mem z hz =>
    obtain ⟨α, hαi, hα, a, ha, x, hx, rfl⟩ := hz
    rw [Set.mem_singleton_iff] at ha
    subst ha
    rw [rat_mulVec_tmul]
    exact AddSubgroup.subset_closure ⟨α, hαi, hα, 1, rfl, M *ᵥ x, hM x hx, rfl⟩
  | zero => rw [Matrix.mulVec_zero]; exact zero_mem _
  | add z z' _ _ hz hz' => rw [Matrix.mulVec_add]; exact add_mem hz hz'
  | neg z _ hz => rw [Matrix.mulVec_neg]; exact neg_mem hz

theorem mxAt_mul_left {P : GlobalTheory.FinPl.Pl D → Prop} {k m n : ℕ} (B : Mx D k m) {A : Mx D m n} (hA : MxAt P A) :
    MxAt P (B * A) := fun i j => by
  rw [Matrix.mul_apply]
  exact Ideal.sum_mem _ fun l _ => Ideal.mul_mem_left _ _ (hA l j)

theorem mxAt_mul_right {P : GlobalTheory.FinPl.Pl D → Prop} {k m n : ℕ} {A : Mx D k m} (hA : MxAt P A) (C : Mx D m n) :
    MxAt P (A * C) := fun i j => by
  rw [Matrix.mul_apply]
  exact Ideal.sum_mem _ fun l _ => Ideal.mul_mem_right _ _ (hA i l)

end GlobalTheory.LineCompLat

open GlobalTheory.LineCompLat

theorem GlobalTheory.AscFin.BoxBF.lineComp_mem_latO : OnStd fun {D} _ _ {sc} {G} W F => ∀ ρ (h : 2 * ρ + 2 ≤ D.R.m), ∀ u ∈ (pcBF W F ρ h).Γ₀, ((F.oB ρ h).resS (G.V (.core (2 * ρ + 1))) u).2 ∈ latO (negSp F.Lz) (G.V (.core (2 * ρ + 1))) (idLat (G.pl.stA sc ^ (ρ + 1) * (G.pl.stAbar sc ^ (ρ + 1))⁻¹) (Submodule.span (𝓞 D.host.E) {F.ζ 0}) : Set _) (G.Λ (.core (2 * ρ + 1)) : Set _) fun _ => True := by
  intro D hD T L μ0 hL sc G W Mv hM F hF ρ h u hu
  obtain ⟨hsd0, hloc, hsdM, horth⟩ := (_root_.GlobalTheory.AscFin.GridLat.lattices_grid D hD T L μ0 hL sc G W Mv hM F hF).2.1 ρ h
  have sdV : IsSelfDualC (negSp (G.V (.grid (2 * ρ + 1 + 1) 0))) (G.Λ (.grid (2 * ρ + 1 + 1) 0)) :=
    isSelfDualC_neg (G.sp.V_is (2 * ρ + 1 + 1) 0 (by omega) h (by omega)).sd
  have sdW : IsSelfDualC (G.V (.grid (2 * ρ + 1) 0)) (G.Λ (.grid (2 * ρ + 1) 0)) :=
    (G.sp.V_is (2 * ρ + 1) 0 (by omega) (by omega) (by omega)).sd
  have sdC : IsSelfDualC (G.V (.core (2 * ρ + 1))) (G.Λ (.core (2 * ρ + 1))) :=
    (G.sp.P_is (2 * ρ + 1) (by omega)).sd
  have hU1 : (F.dJ ρ h).j0 * u * (F.dB ρ h).p0 ∈ latRow G (2 * ρ + 1) := hu
  have hU := hU1.1
  dsimp only [GridData.pS, GridData.pT, GridData.latS, GridData.latT] at hU
  clear hU1 hu
  have hu' : u = (F.dJ ρ h).p0 * ((F.dJ ρ h).j0 * u * (F.dB ρ h).p0) * (F.dB ρ h).j0 := by
    simp only [← Matrix.mul_assoc, HypDec.p0_j0, Matrix.one_mul]
    rw [Matrix.mul_assoc u, HypDec.p0_j0, Matrix.mul_one]
  rw [OrthDec.resS_apply]
  refine (GlobalTheory.FinPl.LatMem.mem_latO_iff D _ _ _ _ hsdM sdC _ _).2 ⟨?_, fun z hz => ?_⟩
  · rw [hu']
    exact mxAt_mul_right (mxAt_mul_right (mxAt_mul_left _ (GlobalTheory.FinPl.LatMem.latO_mxAt hU)) _) _
  have h1 : (F.oB ρ h).jB *ᵥ z ∈ latV (F.V₀ ρ) (lat0 F ρ h) fun _ => True := by
    refine GlobalTheory.FinPl.FlatVacuum.mulVec_latV_of_local hsdM.1 hsd0.1 (F.oB ρ h).jB (fun v _ y hy => ?_) hz
    refine ((horth v) _).2 ⟨?_, ?_⟩
    · rw [Matrix.mulVec_mulVec, OrthDec.pA_jB, Matrix.zero_mulVec]; exact zero_mem _
    · rw [Matrix.mulVec_mulVec, OrthDec.pB_jB, Matrix.one_mulVec]; exact hy
  have h2 : (F.dB ρ h).j0 *ᵥ ((F.oB ρ h).jB *ᵥ z) ∈
      latV (negSp (G.V (.grid (2 * ρ + 1 + 1) 0))) (G.Λ (.grid (2 * ρ + 1 + 1) 0)) fun _ => True :=
    rat_mulVec_latV (F.dB ρ h).i₀ (fun x hx => hx) h1
  have h3 := GlobalTheory.FinPl.LatMem.latO_maps sdV hU h2
  have h4 : (F.dJ ρ h).p0 *ᵥ (((F.dJ ρ h).j0 * u * (F.dB ρ h).p0) *ᵥ ((F.dB ρ h).j0 *ᵥ ((F.oB ρ h).jB *ᵥ z))) ∈
      latA _ (G.Λ (.core (2 * ρ + 1))) fun _ => True := by
    refine GlobalTheory.FinPl.FlatVacuum.mulVec_latA (F.dJ ρ h).p0 (fun y hy => ?_) h3
    refine GlobalTheory.FinPl.FlatVacuum.mulVec_latV_of_local sdW.1 sdC.1 (F.dJ ρ h).p0 (fun v _ y' hy' => ?_) hy
    exact (((hloc v).2 y').1 hy').2.2
  have e : (F.dJ ρ h).p0 *ᵥ (((F.dJ ρ h).j0 * u * (F.dB ρ h).p0) *ᵥ ((F.dB ρ h).j0 *ᵥ ((F.oB ρ h).jB *ᵥ z))) =
      (u * (F.oB ρ h).jB) *ᵥ z := by
    simp only [Matrix.mulVec_mulVec, ← Matrix.mul_assoc, HypDec.p0_j0, Matrix.one_mul]
    rw [Matrix.mul_assoc u, HypDec.p0_j0, Matrix.mul_one]
  rw [← e]
  exact h4
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.BesselStepPiecesBFiniteAdelicLattices
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows GlobalTheory.Asc
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (Lat idAt idOff intAt grpAt grpOff MxAt latV latA InK MonoAt OrthAt PrimAt ColsAt)
open scoped nonZeroDivisors ContDiff
open GlobalTheory.AscFin

namespace GlobalTheory.BesselPieceB

variable {D : D7}

theorem mxAt_mul_left {P : GlobalTheory.FinPl.Pl D → Prop} {k m n : ℕ} (M : Mx D k m) {x : Mx D m n} (hx : MxAt P x) :
    MxAt P (M ⬝ x) := fun i j => by
  simp only [Matrix.mul_apply]
  exact Ideal.sum_mem _ fun l _ => Ideal.mul_mem_left _ _ (hx l j)

theorem mxAt_mul_right {P : GlobalTheory.FinPl.Pl D → Prop} {k m n : ℕ} {x : Mx D k m} (hx : MxAt P x) (M : Mx D m n) :
    MxAt P (x ⬝ M) := fun i j => by
  simp only [Matrix.mul_apply]
  exact Ideal.sum_mem _ fun l _ => Ideal.mul_mem_right _ _ (hx i l)

theorem finLat_comap_mul {k n k' m' : ℕ} {A : AddSubgroup (Mx D k' m')} (hA : FinLat A) (f : Mx D k n →+ Mx D k' m')
    (M : Mx D k' k) (N : Mx D n m') (M' : Mx D k k') (N' : Mx D m' n) (hf : ∀ x : Mx D k n, f x = M ⬝ x ⬝ N)
    (hM : M' ⬝ M = 1) (hN : N ⬝ N' = 1) : FinLat (A.comap f) := by
  haveI : T2Space (Mx D k' m') := (lattice_Mx D k' m').2.2.2.1
  have hfc : Continuous f := by
    have : (f : Mx D k n → Mx D k' m') = fun x : Mx D k n => M ⬝ x ⬝ N := funext hf
    rw [this]; exact (continuous_const.matrix_mul continuous_id).matrix_mul continuous_const
  have hgc : Continuous fun y : Mx D k' m' => M' ⬝ y ⬝ N' :=
    (continuous_const.matrix_mul continuous_id).matrix_mul continuous_const
  have hgf : ∀ x, M' ⬝ f x ⬝ N' = x := fun x => by
    have e : M' ⬝ f x ⬝ N' = (M' ⬝ M) ⬝ x ⬝ (N ⬝ N') := by rw [hf]; simp only [Matrix.mul_assoc]
    rw [e, hM, hN, Matrix.one_mul, Matrix.mul_one]
  refine ⟨fun a ha => ?_, ?_, ?_⟩
  · rw [← hgf a]; exact mxAt_mul_right (mxAt_mul_left _ (hA.fin _ ha)) _
  · refine (hA.cpt.image hgc).of_isClosed_subset (hA.cpt.isClosed.preimage hfc) fun a ha => ⟨f a, ha, hgf a⟩
  · obtain ⟨U, hU, h0, hUA⟩ := hA.opn
    refine ⟨f ⁻¹' U, hU.preimage hfc, by simpa using h0, fun a ha hfin => hUA _ ha ?_⟩
    rw [hf]; exact mxAt_mul_right (mxAt_mul_left _ hfin) _

end GlobalTheory.BesselPieceB


open GlobalTheory.BesselPieceB in
theorem GlobalTheory.BesselPieceB.finLat_pcBF_B : OnStd fun {D} _ _ {sc} {G} W F => ∀ ρ (h : 2 * ρ + 2 ≤ D.R.m),
    FinLat (pcBF W F ρ h).B₁ ∧ FinLat (pcBF W F ρ h).B₂ := by
  intro D hD T L μ0 hL sc G W M hM F hF ρ h
  have hB : FinLat (latBig G (2 * ρ + 1)) :=
    ((_root_.GlobalTheory.AscFin.GridLat.lattices_grid D hD T L μ0 hL sc G W M hM F hF).1 (2 * ρ + 1) (by omega)).2.2.1
  exact ⟨finLat_comap_mul hB _ (F.dJ ρ h).jX (F.dB ρ h).p0 (F.dJ ρ h).pX (F.dB ρ h).j0 (fun _ => rfl)
      (F.dJ ρ h).pX_jX (F.dB ρ h).p0_j0,
    finLat_comap_mul hB _ (F.dJ ρ h).jY (F.dB ρ h).p0 (F.dJ ρ h).pY (F.dB ρ h).j0 (fun _ => rfl)
      (F.dJ ρ h).pY_jY (F.dB ρ h).p0_j0⟩
end

