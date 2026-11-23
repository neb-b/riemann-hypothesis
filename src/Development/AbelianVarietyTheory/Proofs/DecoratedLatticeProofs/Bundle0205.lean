module

public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0017
public import Development.AbelianVarietyTheory.PublishedTheorems.SiegelWeil₂.SiegelWeilUnitaryConvergent
public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0064
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0068
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0018
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0009
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0016
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0180
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0075
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0156
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0014
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0013
public import Development.AbelianVarietyTheory.PublishedTheorems.DiscreteSeriesUnitary₂.Bundle0001
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.Bundle0004
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleDiscreteSeriesOfHasParam
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0008
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0007
public import Formalism.LocalToGlobal.IndefiniteReal.OrthogonalComplementCharacterisation
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ExistsHeightLeTwoMulQuotHeight
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.WittDecompSymplInclIsotropicInclAnisotropic
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0019
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0007
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.CuspRapidDecayOfSobolev
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0160

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IsHeckeCharRestrictionEtaInv
section
open scoped Matrix NNReal ComplexConjugate TensorProduct ContDiff
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel GlobalTheory.Core.Rk.SWLaw GlobalTheory.Core.Rk.SW GlobalTheory.StdUnn
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (RealMat IsFockVec)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (swSec sZero)
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.StdUnn

theorem isHeckeChar_resEta_inv : ∀ (D : D7) (χ : (AE D)ˣ →* Circle) (m : ℕ), IsHeckeChar D χ → ResEta D χ m → IsHeckeChar D χ⁻¹ ∧ ResEta D χ⁻¹ m := by
  intro D χ m h1 h2
  refine ⟨⟨h1.1.inv, fun x => ?_⟩, resEta_inv h2⟩
  rw [MonoidHom.inv_apply, h1.2, inv_one]

end GlobalTheory.StdUnn
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IsPolynomialFockThetaVectorWeilOperatorCartan
section
open scoped Matrix NNReal ComplexConjugate TensorProduct ContDiff
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel GlobalTheory.Core.Rk.SWLaw GlobalTheory.Core.Rk.SW GlobalTheory.StdUnn
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (RealMat IsFockVec)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (swSec sZero)
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.FockMove

variable {D : D7} {ψ : AddChar (AF D.host.F) ℂ} {θ : InfFam D} {S T : HSp D} {χS χT : (AE D)ˣ →* Circle}
  {om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)}

theorem theta_annih (hθ : IsInfFam θ) (hψ : IsStdChar D ψ (-1)) (τ : D.what₂.Tau)
    (J : Matrix (Fin T.rank) (Fin S.rank) ℂ → Matrix (Fin T.rank) (Fin S.rank) ℂ)
    (z : Matrix (Fin T.rank) (Fin S.rank) ℂ) {f : WO S T → ℂ} (hf : IsThetaFunO ψ S T f) :
    IsThetaFunO ψ S T (annih (heisO ψ S T) θ τ J z f) :=
  GlobalTheory.OrientedHeis.theta_add (GlobalTheory.OrientedHeis.theta_dRho hθ hψ τ z hf)
    (GlobalTheory.OrientedHeis.theta_smul _ (GlobalTheory.OrientedHeis.theta_dRho hθ hψ τ _ hf))

theorem om_annih (hW : IsWeilDatumO ψ S T χS χT om) (hθ : IsInfFam θ) (g : GA D S) (h : GA D T) (τ : D.what₂.Tau)
    {sS sS' : Matrix (Fin S.rank) (Fin S.rank) ℂ} {sT sT' : Matrix (Fin T.rank) (Fin T.rank) ℂ}
    (hS : sS' * compAt θ τ (mt S g) = compAt θ τ (mt S g) * sS)
    (hT : sT' * compAt θ τ (mt T h) = compAt θ τ (mt T h) * sT) (z : Matrix (Fin T.rank) (Fin S.rank) ℂ)
    {f : WO S T → ℂ} (hf : IsThetaFunO ψ S T f) :
    om (g, h) (annih (heisO ψ S T) θ τ (cplxO sS sT) z f) =
      annih (heisO ψ S T) θ τ (cplxO sS' sT') (compAt θ τ (mt T h) * z * compAt θ τ (mt S g⁻¹)) (om (g, h) f) := by
  unfold annih
  rw [map_add (f := _), map_smul, GlobalTheory.WeilVacMove.om_dRho hW hθ g h τ _ hf, GlobalTheory.WeilVacMove.om_dRho hW hθ g h τ _ hf,
    GlobalTheory.WeilVacMove.cplxO_move θ τ g h hS hT]

theorem om_foldr (hW : IsWeilDatumO ψ S T χS χT om) (hθ : IsInfFam θ) (g : GA D S) (h : GA D T)
    {sS sS' : RealMat S} {sT sT' : RealMat T}
    (hS : ∀ τ, sS' τ * compAt θ τ (mt S g) = compAt θ τ (mt S g) * sS τ)
    (hT : ∀ τ, sT' τ * compAt θ τ (mt T h) = compAt θ τ (mt T h) * sT τ) {f : WO S T → ℂ}
    (hf : IsThetaFunO ψ S T f) (l : List (D.what₂.Tau × Matrix (Fin T.rank) (Fin S.rank) ℂ)) :
    IsThetaFunO ψ S T (l.foldr (fun p F => annih (heisO ψ S T) θ p.1 (cplxO (sS p.1) (sT p.1)) p.2 F) f) ∧
      om (g, h) (l.foldr (fun p F => annih (heisO ψ S T) θ p.1 (cplxO (sS p.1) (sT p.1)) p.2 F) f) =
        (l.map fun p => (p.1, compAt θ p.1 (mt T h) * p.2 * compAt θ p.1 (mt S g⁻¹))).foldr
          (fun p F => annih (heisO ψ S T) θ p.1 (cplxO (sS' p.1) (sT' p.1)) p.2 F) (om (g, h) f) := by
  induction l with
  | nil => exact ⟨hf, rfl⟩
  | cons p l ih =>
    rw [List.map_cons, List.foldr_cons, List.foldr_cons, ← ih.2]
    exact ⟨theta_annih hθ hW.std p.1 _ p.2 ih.1, om_annih hW hθ g h p.1 (hS p.1) (hT p.1) p.2 ih.1⟩

end GlobalTheory.FockMove

namespace GlobalTheory.FockMove

theorem isFockVec_om : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (χS χT : (AE D)ˣ →* Circle) (om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)), IsWeilDatumO ψ S T χS χT om → ∀ θ : InfFam D, IsInfFam θ → ∀ (sS sS' : RealMat S) (sT : RealMat T) (g : GA D S), (∀ τ, sS' τ * compAt θ τ (mt S g) = compAt θ τ (mt S g) * sS τ) → ∀ f, IsFockVec ψ θ S T sS sT f → IsFockVec ψ θ S T sS' sT (om (g, 1) f) := by
  intro D ψ S T χS χT om hW θ hθ sS sS' sT g hS f hf
  obtain ⟨hth, N, hN⟩ := hf
  have hT : ∀ τ, sT τ * compAt θ τ (mt T 1) = compAt θ τ (mt T 1) * sT τ := by
    intro τ
    rw [GlobalTheory.WeilVacMove.mt_one, GlobalTheory.WeilVacMove.compAt_one, Matrix.mul_one, Matrix.one_mul]
  refine ⟨hW.om_pres _ _ hth, N, fun l hl => ?_⟩
  let l₀ : List (D.what₂.Tau × Matrix (Fin T.rank) (Fin S.rank) ℂ) :=
    l.map fun p => (p.1, compAt θ p.1 (mt T (1 : GA D T)⁻¹) * p.2 * compAt θ p.1 (mt S g))
  have e : (l₀.map fun p => (p.1, compAt θ p.1 (mt T (1 : GA D T)) * p.2 * compAt θ p.1 (mt S g⁻¹))) = l := by
    simp only [l₀, List.map_map]
    conv_rhs => rw [← List.map_id l]
    refine List.map_congr_left fun p _ => ?_
    simp only [Function.comp_apply, id]
    rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, GlobalTheory.WeilVacMove.compAt_mt_mul_inv, Matrix.one_mul, Matrix.mul_assoc,
      GlobalTheory.WeilVacMove.compAt_mt_mul_inv, Matrix.mul_one]
  have key := (om_foldr hW hθ g 1 hS hT hth l₀).2
  rw [e] at key
  rw [← key, hN l₀ (by simp [l₀, hl]), map_zero]

end GlobalTheory.FockMove

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IsSchwartzBruhatAdelicMatrixOfMemAdelicSchwartz
section
open scoped ComplexConjugate Matrix NNReal ENNReal
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.Cusp GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (FinPl RealMat Lat IsFockVec IsSphOff HidaSetting volQ)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (ip delta swSec sZero IsKFinVec ThetaClause SectionClause CoefClause)
open GlobalTheory.Mem.Th (CptF)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Core.Rk.IP GlobalTheory.Core.Rk.SWLaw
open GlobalTheory.Core.Rk.SW
open scoped ContDiff
open scoped TensorProduct Topology

noncomputable section

namespace GlobalTheory.SchwartzPure

open GlobalTheory.IndefiniteRowSideFullHecke.SchwartzBruhatMixedFamilies

variable {D : D7} {m n : ℕ}

theorem eventually_invariant {M : Type} [AddCommGroup M] [TopologicalSpace M] [IsTopologicalAddGroup M] {Φ : M → ℂ}
    (h1 : IsLocallyConstant Φ) (h2 : HasCompactSupport Φ) : ∀ᶠ u in 𝓝 (0 : M), ∀ x, Φ (x + u) = Φ x := by
  have h : ∀ᶠ u in 𝓝 (0 : M), ∀ x ∈ tsupport Φ, Φ (x + u) = Φ x ∧ Φ (x - u) = Φ x := by
    apply h2.isCompact.eventually_forall_of_forall_eventually
    intro x _
    have a1 := (h1.comp_continuous (show Continuous fun z : M × M => z.2 + z.1 by fun_prop)).eventually_eq (0, x)
    have a2 := (h1.comp_continuous (show Continuous fun z : M × M => z.2 - z.1 by fun_prop)).eventually_eq (0, x)
    have a3 := (h1.comp_continuous (show Continuous fun z : M × M => z.2 by fun_prop)).eventually_eq (0, x)
    filter_upwards [a1, a2, a3] with z b1 b2 b3
    simp only [Function.comp, add_zero, sub_zero] at b1 b2 b3
    exact ⟨b1.trans b3.symm, b2.trans b3.symm⟩
  filter_upwards [h] with u hu x
  by_cases hx : x ∈ tsupport Φ
  · exact (hu x hx).1
  · by_cases hx' : x + u ∈ tsupport Φ
    · have := (hu _ hx').2
      rw [add_sub_cancel_right] at this
      exact this.symm
    · rw [image_eq_zero_of_notMem_tsupport hx, image_eq_zero_of_notMem_tsupport hx']

def periods {M : Type} [AddCommGroup M] (Φ : M → ℂ) : AddSubgroup M where
  carrier := {u | ∀ x, Φ (x + u) = Φ x}
  zero_mem' := fun x => by rw [add_zero]
  add_mem' := fun {a b} ha hb x => by rw [← add_assoc, hb, ha]
  neg_mem' := fun {a} ha x => by
    have := ha (x + -a)
    rw [neg_add_cancel_right] at this
    exact this.symm

theorem isOpen_periods {M : Type} [AddCommGroup M] [TopologicalSpace M] [IsTopologicalAddGroup M] {Φ : M → ℂ}
    (h1 : IsLocallyConstant Φ) (h2 : HasCompactSupport Φ) : IsOpen (periods Φ : Set M) :=
  AddSubgroup.isOpen_of_mem_nhds _ (eventually_invariant h1 h2)

theorem zero : IsSchwartzBruhat (0 : Mx D m n → ℂ) := by
  exact
    { level := ⟨⊤, isOpen_univ, fun _ _ _ _ => rfl⟩
      supp := ⟨∅, isCompact_empty, fun _ h => absurd rfl h⟩
      schwartz := fun _ _ _ _ _ => ⟨0, fun _ => rfl⟩ }

theorem add {φ ψ : Mx D m n → ℂ} (hφ : IsSchwartzBruhat φ) (hψ : IsSchwartzBruhat ψ) : IsSchwartzBruhat (φ + ψ) := by
  refine { level := ?_, supp := ?_, schwartz := ?_ }
  · obtain ⟨U, hU, h⟩ := hφ.level
    obtain ⟨U', hU', h'⟩ := hψ.level
    refine ⟨U ⊓ U', hU.inter hU', fun u hu h0 x => ?_⟩
    simp only [Pi.add_apply, h u hu.1 h0, h' u hu.2 h0]
  · obtain ⟨K, hK, h⟩ := hφ.supp
    obtain ⟨K', hK', h'⟩ := hψ.supp
    refine ⟨K ∪ K', hK.union hK', fun x hx => ?_⟩
    by_cases h1 : φ x = 0
    · exact Or.inr (h' x fun h2 => hx (by simp [h1, h2]))
    · exact Or.inl (h x h1)
  · intro k L hL hi x
    obtain ⟨g, hg⟩ := hφ.schwartz k L hL hi x
    obtain ⟨g', hg'⟩ := hψ.schwartz k L hL hi x
    exact ⟨g + g', fun t => by simp [hg, hg']⟩

theorem smul (c : ℂ) {φ : Mx D m n → ℂ} (hφ : IsSchwartzBruhat φ) : IsSchwartzBruhat (c • φ) := by
  refine { level := ?_, supp := ?_, schwartz := ?_ }
  · obtain ⟨U, hU, h⟩ := hφ.level
    exact ⟨U, hU, fun u hu h0 x => by simp only [Pi.smul_apply, h u hu h0]⟩
  · obtain ⟨K, hK, h⟩ := hφ.supp
    exact ⟨K, hK, fun x hx => h x fun h1 => hx (by simp [h1])⟩
  · intro k L hL hi x
    obtain ⟨g, hg⟩ := hφ.schwartz k L hL hi x
    exact ⟨c • g, fun t => by simp [hg]⟩

theorem compAt_add (θ : InfFam D) (τ : D.what₂.Tau) (x y : Mx D m n) :
    compAt θ τ (x + y) = compAt θ τ x + compAt θ τ y := by
  ext i j
  simp only [compAt, Matrix.map_apply, Matrix.add_apply]
  rw [map_add (infPart D), map_add (θ τ)]

def realVec {k : ℕ} (θ : InfFam D) (L : (Fin k → ℝ) →+ Mx D m n) : (Fin k → ℝ) →+ (D.what₂.Tau → Fin m → Fin n → ℂ) where
  toFun t := fun τ i j => compAt θ τ (L t) i j
  map_zero' := by ext τ i j; simp [compAt]
  map_add' a b := by ext τ i j; simp [compAt_add]

theorem norm_compAt_le (θ : InfFam D) (x : Mx D m n) (τ : D.what₂.Tau) (i : Fin m) (j : Fin n) :
    ‖compAt θ τ x i j‖ ≤ GlobalTheory.Unf.realSize θ x := by
  unfold GlobalTheory.Unf.realSize
  calc ‖compAt θ τ x i j‖ ≤ ∑ j', ‖compAt θ τ x i j'‖ :=
        Finset.single_le_sum (f := fun j' => ‖compAt θ τ x i j'‖) (fun _ _ => norm_nonneg _) (Finset.mem_univ j)
    _ ≤ ∑ i', ∑ j', ‖compAt θ τ x i' j'‖ :=
        Finset.single_le_sum (f := fun i' => ∑ j', ‖compAt θ τ x i' j'‖)
          (fun _ _ => Finset.sum_nonneg fun _ _ => norm_nonneg _) (Finset.mem_univ i)
    _ ≤ _ := Finset.single_le_sum (f := fun τ' => ∑ i', ∑ j', ‖compAt θ τ' x i' j'‖)
          (fun _ _ => Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => norm_nonneg _) (Finset.mem_univ τ)

theorem realSize_nonneg (θ : InfFam D) (x : Mx D m n) : 0 ≤ GlobalTheory.Unf.realSize θ x :=
  Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => norm_nonneg _

theorem norm_vec_le (θ : InfFam D) (x : Mx D m n) :
    ‖(fun τ i j => compAt θ τ x i j : D.what₂.Tau → Fin m → Fin n → ℂ)‖ ≤ GlobalTheory.Unf.realSize θ x :=
  (pi_norm_le_iff_of_nonneg (realSize_nonneg θ x)).2 fun τ =>
    (pi_norm_le_iff_of_nonneg (realSize_nonneg θ x)).2 fun i =>
      (pi_norm_le_iff_of_nonneg (realSize_nonneg θ x)).2 fun j => norm_compAt_le θ x τ i j

theorem realSize_le (θ : InfFam D) (x : Mx D m n) :
    GlobalTheory.Unf.realSize θ x ≤ (Fintype.card D.what₂.Tau * (m * n) : ℝ) *
      ‖(fun τ i j => compAt θ τ x i j : D.what₂.Tau → Fin m → Fin n → ℂ)‖ := by
  set v : D.what₂.Tau → Fin m → Fin n → ℂ := fun τ i j => compAt θ τ x i j with hv
  unfold GlobalTheory.Unf.realSize
  calc ∑ τ, ∑ i, ∑ j, ‖compAt θ τ x i j‖ ≤ ∑ τ : D.what₂.Tau, ∑ i : Fin m, ∑ j : Fin n, ‖v‖ :=
        Finset.sum_le_sum fun τ _ => Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ =>
          (norm_le_pi_norm (v τ i) j).trans ((norm_le_pi_norm (v τ) i).trans (norm_le_pi_norm v τ))
    _ = _ := by simp [Finset.sum_const]; ring

theorem realSize_zero (θ : InfFam D) : GlobalTheory.Unf.realSize θ (0 : Mx D m n) = 0 := by
  simp [GlobalTheory.Unf.realSize, compAt]

def finVec : Mx D m n →+ (Fin m → Fin n → Af D.host.F ⊗[D.host.F] D.host.E) where
  toFun x := fun i j => finPart D (x i j)
  map_zero' := by ext i j; exact (finPart D).map_zero
  map_add' a b := by ext i j; exact (finPart D).map_add _ _

theorem continuous_finVec : Continuous (finVec (D := D) (m := m) (n := n)) :=
  continuous_pi fun i => continuous_pi fun j =>
    (GlobalTheory.Member.continuous_finPart D).comp ((continuous_apply j).comp (continuous_apply i))

theorem pure (θ : InfFam D) (hθ : IsInfFam θ) (f : SchwartzMap (D.what₂.Tau → Fin m → Fin n → ℂ) ℂ)
    (g : (Fin m → Fin n → Af D.host.F ⊗[D.host.F] D.host.E) → ℂ)
    (hg : g ∈ GlobalTheory.WeilM.SB (Fin m → Fin n → Af D.host.F ⊗[D.host.F] D.host.E)) :
    IsSchwartzBruhat fun x : Mx D m n => f (fun τ i j => compAt θ τ x i j) * g (fun i j => finPart D (x i j)) := by
  refine { level := ?_, supp := ?_, schwartz := ?_ }
  · have : IsModuleTopology (Af D.host.F) (Af D.host.F ⊗[D.host.F] D.host.E) := ⟨rfl⟩
    have : IsTopologicalAddGroup (Af D.host.F ⊗[D.host.F] D.host.E) :=
      IsModuleTopology.isTopologicalAddGroup (Af D.host.F) _
    set P := (finVec : Mx D m n →+ (Fin m → Fin n → Af D.host.F ⊗[D.host.F] D.host.E)) with hP
    refine ⟨(periods g).comap P, (isOpen_periods hg.1 hg.2).preimage continuous_finVec, fun u hu h0 x => ?_⟩
    have e1 : ∀ τ, compAt θ τ (x + u) = compAt θ τ x := fun τ => by
      rw [compAt_add]
      ext i j
      have h := congrFun (congrFun h0 i) j
      simp only [Matrix.map_apply, Matrix.zero_apply] at h
      simp only [Matrix.add_apply, compAt, Matrix.map_apply, h, (θ τ).map_zero, add_zero]
    have e2 : (fun i j => finPart D ((x + u) i j)) = (fun i j => finPart D (x i j)) + P u :=
      P.map_add x u
    simp only [e1, e2]
    rw [show g ((fun i j => finPart D (x i j)) + P u) = g (fun i j => finPart D (x i j)) from hu _]
  · exact ⟨tsupport g, hg.2.isCompact, fun x hx => subset_tsupport g (right_ne_zero_of_mul hx)⟩
  · intro k L hL hi x
    obtain ⟨⟨C₁, hC₁⟩, hlow⟩ := _root_.GlobalTheory.Unf.realParam_size_bounds D θ hθ m n k L hL
    obtain ⟨C₂, hC₂⟩ := hlow hi
    have hAb : ∀ t, ‖realVec θ L t‖ ≤ C₁ * ‖t‖ := fun t => (norm_vec_le θ (L t)).trans (hC₁ t)
    have hAc : Continuous (realVec θ L) := AddMonoidHomClass.continuous_of_bound (realVec θ L) C₁ hAb
    set Al := (realVec θ L).toRealLinearMap hAc with hAl
    have hAlt : ∀ t, Al t = realVec θ L t := fun t => rfl
    have hker : (Al : (Fin k → ℝ) →ₗ[ℝ] (D.what₂.Tau → Fin m → Fin n → ℂ)).ker = ⊥ := by
      rw [LinearMap.ker_eq_bot']
      intro t ht
      have h0 : realVec θ L t = 0 := by rw [← hAlt]; exact ht
      have h1 := hC₂ 0 t
      rw [zero_add, realSize_zero, add_zero] at h1
      have h2 := realSize_le θ (L t)
      have h3 : (fun τ i j => compAt θ τ (L t) i j : D.what₂.Tau → Fin m → Fin n → ℂ) = 0 := h0
      rw [h3, norm_zero, mul_zero] at h2
      have h4 : GlobalTheory.Unf.realSize θ (L t) = 0 := le_antisymm h2 (realSize_nonneg θ _)
      rw [h4, mul_zero] at h1
      exact norm_le_zero_iff.mp h1
    obtain ⟨K, -, hK⟩ := (Al : (Fin k → ℝ) →ₗ[ℝ] (D.what₂.Tau → Fin m → Fin n → ℂ)).exists_antilipschitzWith hker
    set a : D.what₂.Tau → Fin m → Fin n → ℂ := fun τ i j => compAt θ τ x i j with ha
    have hgr : Function.HasTemperateGrowth (fun t => a + Al t) :=
      (Function.HasTemperateGrowth.const a).add Al.hasTemperateGrowth
    have hanti : AntilipschitzWith K (fun t => a + Al t) :=
      AntilipschitzWith.of_le_mul_dist fun s t => by rw [dist_add_left]; exact hK.le_mul_dist s t
    refine ⟨g (fun i j => finPart D (x i j)) • SchwartzMap.compCLMOfAntilipschitz ℂ hgr hanti f, fun t => ?_⟩
    have e1 : (fun τ i j => compAt θ τ (x + L t) i j : D.what₂.Tau → Fin m → Fin n → ℂ) = a + Al t := by
      ext τ i j
      rw [hAlt, compAt_add]
      rfl
    have e2 : (fun i j => finPart D ((x + L t) i j)) = (fun i j => finPart D (x i j)) := by
      ext i j
      have h := congrFun (congrFun (hL.2 t) i) j
      simp only [Matrix.map_apply, Matrix.zero_apply] at h
      rw [Matrix.add_apply, map_add (finPart D), h, add_zero]
    simp only [e1, e2, smul_apply, SchwartzMap.compCLMOfAntilipschitz_apply, Function.comp_apply, smul_eq_mul]
    ring

theorem isSchwartzBruhat_of_mem_schwartzA : ∀ (D : D7) (θ : InfFam D), IsInfFam θ → ∀ (m n : ℕ),
    ∀ φ ∈ GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz.schwartzA θ m n, GlobalTheory.IndefiniteRowSideFullHecke.SchwartzBruhatMixedFamilies.IsSchwartzBruhat φ := by
  intro D θ hθ m n φ hφ
  induction hφ using Submodule.span_induction with
  | mem φ h =>
    obtain ⟨f, g, hg, rfl⟩ := h
    exact pure θ hθ f g hg
  | zero => exact zero
  | add _ _ _ _ h1 h2 => exact add h1 h2
  | smul c _ _ h => exact smul c h

end GlobalTheory.SchwartzPure
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LevOfMem
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.SeeSaw
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.ValMoveProof

theorem lev_of_mem {D : D7} (θ : InfFam D) {V : HSp D} {S : D.what₂.Tau → SPar} (M : DSModel V S)
    (J : Set (GA D V)) (χ : GA D V → ℂ) (T : MMap M) (hT : T ∈ Mult θ M J χ) :
    ∀ v, ∀ k ∈ J, ∀ g, T v (g * k) = χ k * T v g := by
  induction hT using Submodule.span_induction with
  | mem x hx => exact hx.lev
  | zero => intros; simp
  | add x y _ _ hx hy =>
    intro v k hk g
    simp only [MultilinearMap.add_apply, Pi.add_apply, hx v k hk g, hy v k hk g, mul_add]
  | smul a x _ hx =>
    intro v k hk g
    simp only [MultilinearMap.smul_apply, Pi.smul_apply, smul_eq_mul, hx v k hk g]
    ring

theorem valMove : ∀ D : D7, ValMove D := by
  intro D θ hθ V S M J χ
  refine ⟨?_, ?_⟩
  · intro G hG x k hk
    rw [mem_multT] at hG
    have h := lev_of_mem θ M J χ _ hG
    have e : ∀ f, G (PiTensorProduct.tprod ℂ f) = (PiTensorProduct.lift.symm G) f := fun f => by
      simp [PiTensorProduct.lift_symm]
    induction x using PiTensorProduct.induction_on with
    | smul_tprod r f =>
      funext g
      simp only [rTrans, map_smul, Pi.smul_apply, smul_eq_mul, e, h f k hk g]
      ring
    | add x y hx hy =>
      funext g
      have hx' := congrFun hx g
      have hy' := congrFun hy g
      simp only [rTrans, map_add (f := _), Pi.add_apply, Pi.smul_apply, smul_eq_mul] at hx' hy' ⊢
      rw [hx', hy', mul_add]
  · intro a ha v
    obtain ⟨σ, hσ⟩ := _root_.GlobalTheory.RealTransSm.rTrans_eq_map D θ V S M hθ a ha
    exact ⟨σ v, fun G hG => (hσ J χ G hG v).symm⟩

end GlobalTheory.ValMoveProof

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LiftConvContGrowth
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Unf
open scoped ComplexOrder ENNReal NNReal ContDiff Topology

namespace GlobalTheory.Unf.LiftRapid

theorem lift_conv_cont_growth : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (χS χT : (AE D)ˣ →* Circle) (om : Om S T), IsWeilDatumO ψ S T χS χT om → ∀ (v : Vol T) (G : GA D T → ℂ) (f : WO S T → ℂ), RapidDec T G → IsThetaFunO ψ S T f → (∀ g, IntegrableOn (fun h => om (g, h) f 0 * G h) v.𝓕 v.μ) ∧ IsAutFun S (liftS om v.μ v.𝓕 G f) ∧ IsContAut S (liftS om v.μ v.𝓕 G f) ∧ ModGrowth S (liftS om v.μ v.𝓕 G f) ∧ ∀ g₀ h₀, liftS om v.μ v.𝓕 (rTrans h₀ G) (om (g₀, h₀) f) = rTrans g₀ (liftS om v.μ v.𝓕 G f) := by
  intro D ψ S T χS χT om hω v G f hG hf
  have hν := v.haar
  have h𝓕 := v.fund
  have : BorelSpace (GA D T) := ⟨rfl⟩
  have : SecondCountableTopology (GA D S) := (GlobalTheory.Mem.AdelicGroupTop.adelic_unitary_topology D S).2.1
  have : IsFiniteMeasure (v.μ.restrict v.𝓕) :=
    isFiniteMeasure_restrict.2 (GlobalTheory.Chain.LiftReg.vol_ne_top hν h𝓕)
  obtain ⟨C, A, hC⟩ := _root_.GlobalTheory.SupThetaGrowth.om_sup_growth D ψ S T χS χT om hω f hf
  obtain ⟨B, hB⟩ := hG.decay A
  have hk : ∀ g h, ‖om (g, h) f 0‖ ≤ C * height S g ^ A * height T h ^ A := fun g h => by
    rw [mul_assoc, ← mul_pow]; exact hC g h 0
  have hleft := fun g => GlobalTheory.Chain.LiftConv.thetaKO_left hω hf g
  have hcont := fun g => GlobalTheory.Chain.LiftConv.thetaKO_continuous hω hf g
  have hint : ∀ g, IntegrableOn (fun h => om (g, h) f 0 * G h) v.𝓕 v.μ := fun g =>
    hG.integrableOn_modGrowth_mul hν h𝓕 ⟨C * height S g ^ A, A, hk g⟩ (hleft g)
      (hcont g).measurable.aestronglyMeasurable
  have hbd : ∀ g h, ‖om (g, h) f 0 * G h‖ ≤ C * 2 ^ A * B * height S g ^ A := fun g h => by
    have h1 := norm_le_quotHeight_pow (f := fun h => thetaKO om g h f) (hleft g) (hk g) h
    have hC0 : 0 ≤ C * height S g ^ A * 2 ^ A :=
      (mul_nonneg (nonneg_of_growth (hk g)) (by positivity))
    rw [norm_mul]
    calc ‖om (g, h) f 0‖ * ‖G h‖ ≤ C * height S g ^ A * 2 ^ A * quotHeight T h ^ A * ‖G h‖ :=
          mul_le_mul_of_nonneg_right h1 (norm_nonneg _)
      _ = C * height S g ^ A * 2 ^ A * (‖G h‖ * quotHeight T h ^ A) := by ring
      _ ≤ C * height S g ^ A * 2 ^ A * B := mul_le_mul_of_nonneg_left (hB h) hC0
      _ = C * 2 ^ A * B * height S g ^ A := by ring
  have hm : ∀ g, AEStronglyMeasurable (fun h => om (g, h) f 0 * G h) (v.μ.restrict v.𝓕) := fun g =>
    ((hcont g).mul hG.continuous).measurable.aestronglyMeasurable
  have hc : Continuous (liftS om v.μ v.𝓕 G f) := by
    refine continuous_iff_continuousAt.2 fun g₀ => ?_
    have hcb : Continuous fun g => C * 2 ^ A * B * height S g ^ A := continuous_const.mul ((continuous_height S).pow A)
    have hev := hcb.continuousAt.eventually_lt (continuousAt_const (y := C * 2 ^ A * B * height S g₀ ^ A + 1))
      (lt_add_one _)
    exact continuousAt_of_dominated (bound := fun _ => C * 2 ^ A * B * height S g₀ ^ A + 1)
      (.of_forall hm) (hev.mono fun g hg => .of_forall fun h => (hbd g h).trans hg.le) (integrable_const _)
      (.of_forall fun h => (((hω.om_cont f hf 0).comp (Continuous.prodMk_left h)).mul continuous_const).continuousAt)
  have hl : ∀ γ ∈ GQ S, ∀ g, liftS om v.μ v.𝓕 G f (γ * g) = liftS om v.μ v.𝓕 G f g := fun γ hγ g => by
    have e : ∀ h, om (γ * g, h) f 0 = om (g, h) f 0 := fun h => by
      have e' : ((γ * g, h) : GA D S × GA D T) = (γ, 1) * (g, h) := by simp
      rw [e', map_mul, Module.End.mul_apply]
      exact hω.om_aut γ hγ 1 (one_mem _) _ (hω.om_pres _ _ hf)
    simp only [liftS_apply, e]
  have heq : ∀ g₀ h₀, liftS om v.μ v.𝓕 (rTrans h₀ G) (om (g₀, h₀) f) = rTrans g₀ (liftS om v.μ v.𝓕 G f) :=
    fun g₀ h₀ => GlobalTheory.Chain.LiftReg.lift_om hω hν h𝓕 hf hG.1 g₀ h₀
  refine ⟨hint, ⟨hl, ?_, hc⟩, ⟨hl, hc⟩, ⟨C * 2 ^ A * B * (v.μ.restrict v.𝓕).real Set.univ, A, fun g => ?_⟩, heq⟩
  · obtain ⟨U, U', hU, -, e⟩ := GlobalTheory.Mem.ThetaLevel.exists_level D ψ hω.std S T om (GlobalTheory.Ker.isWeak_of_datum hω)
      hω.om_cont f hf
    refine ⟨U, hU, fun k h1 h2 g => ?_⟩
    have := congrFun (heq k 1) g
    rw [e k h1 h2 1 (one_mem _) (one_mem _), show rTrans 1 G = G from funext fun h => congrArg G (mul_one h)] at this
    exact this.symm
  · rw [liftS_apply]
    refine (norm_integral_le_of_norm_le_const (.of_forall fun h => hbd g h)).trans_eq ?_
    ring

end GlobalTheory.Unf.LiftRapid

end
end

