module

public import Mathlib
public import Development.AbelianVarietyTheory.PublishedTheorems.SiegelWeil₂.SiegelWeilUnitarySchrodinger
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0017
public import Development.AbelianVarietyTheory.PublishedTheorems.SiegelWeil₂.SiegelWeilUnitaryConvergent
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0015
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsThetaFam
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0018
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.PairwiseDisjointCell
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0005
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1256
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0792
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1283
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleDiscreteSeriesOfHasParam
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0090
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0008
public import Formalism.LocalToGlobal.IndefiniteReal.OrthogonalComplementCharacterisation
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ExistsHeightLeTwoMulQuotHeight
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.WittDecompSymplInclIsotropicInclAnisotropic
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0019
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0007
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0150
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0013

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ContinuousLeviBlock
section
open scoped Matrix NNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel GlobalTheory.Core.Rk.SWLaw GlobalTheory.Core.Rk.SW GlobalTheory.StdUnn
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.StdUnn.HeightExists

variable {D : D7} {n : ℕ}

theorem lower_eq_zero {p : G D n} (hp : p ∈ P D n) (i j : Fin n) :
    mat p (finSumFinEquiv (.inr i)) (finSumFinEquiv (.inl j)) = 0 := by
  have h := (hp (Pi.single (finSumFinEquiv (.inl j)) 1)).1 (by
    ext k
    have : (finSumFinEquiv (Sum.inr k : Fin n ⊕ Fin n)) ≠ finSumFinEquiv (.inl j) := by
      rw [Ne, finSumFinEquiv.apply_eq_iff_eq]; simp
    simp only [LinearMap.funLeft_apply, Pi.single_eq_of_ne this, Pi.zero_apply])
  have h2 := congrFun h i
  simp only [LinearMap.funLeft_apply, Matrix.mulVec_single_one, Pi.zero_apply] at h2
  exact h2

theorem blkA_mul {p q : G D n} (hq : q ∈ P D n) : blkA (mat (p * q)) = blkA (mat p) * blkA (mat q) := by
  ext i j
  have e : mat (p * q) = mat p * mat q := rfl
  simp only [e, blkA, Matrix.toBlocks₁₁, Matrix.of_apply, Matrix.submatrix_apply, Matrix.mul_apply]
  rw [← finSumFinEquiv.sum_comp, Fintype.sum_sum_type]
  simp only [lower_eq_zero hq, mul_zero, Finset.sum_const_zero, add_zero]

theorem blkA_one : blkA (mat (1 : G D n)) = 1 := by
  have e : mat (1 : G D n) = 1 := rfl
  rw [e, blkA, Matrix.submatrix_one_equiv, ← Matrix.fromBlocks_one, Matrix.toBlocks_fromBlocks₁₁]

def leviBlock : P D n →* GL (Fin n) (AE D) :=
  MonoidHom.toHomUnits ⟨⟨fun p => blkA (mat p.1), blkA_one⟩, fun p q => blkA_mul q.2⟩

theorem continuous_mat : Continuous (mat : G D n → Mx D (n + n) (n + n)) :=
  Units.continuous_val.comp (isEmbedding_matHom (AF D.host.F) D.sp.cm.sig (Jst D n)).continuous

theorem continuous_leviBlock : Continuous (leviBlock (D := D) (n := n)) := by
  have hA : Continuous fun g : G D n => blkA (mat g) :=
    continuous_matrix fun i j => continuous_mat.matrix_elem _ _
  rw [Units.continuous_iff]
  refine ⟨hA.comp continuous_subtype_val, ?_⟩
  refine (hA.comp (continuous_subtype_val.comp continuous_inv)).congr fun p => ?_
  rw [← map_inv]; rfl

theorem continuous_detGL : Continuous (Matrix.GeneralLinearGroup.det : GL (Fin n) (AE D) → (AE D)ˣ) := by
  haveI := isTopologicalRing_tens (F := D.host.F) (E := D.host.E) (R := AF D.host.F)
  rw [Units.continuous_iff]
  refine ⟨Units.continuous_val.matrix_det, (Units.continuous_coe_inv.matrix_det).congr fun g => ?_⟩
  rw [← map_inv]; rfl

theorem isCompact_K : IsCompact (K D n : Set (G D n)) :=
  haveI := isLattice_stdLattice (E := D.host.E) (n := n + n)
  isCompact_levelAll (isCMExt_host D) _ _ _

theorem isClosed_P : IsClosed (P D n : Set (G D n)) := by
  haveI := t2Space_adeleRing' (F := D.host.F)
  haveI := isTopologicalRing_tens (F := D.host.F) (E := D.host.E) (R := AF D.host.F)
  haveI := t2Space_tensorProduct_finiteExtension (F := D.host.F) (E := D.host.E) (R := AF D.host.F)
  have : (P D n : Set (G D n)) = ⋂ x ∈ upperHalf D n, ({g | (mat g).mulVec x ∈ upperHalf D n} ∩
      {g | (mat g⁻¹).mulVec x ∈ upperHalf D n}) := by
    ext g
    simp only [Set.mem_iInter, Set.mem_inter_iff, Set.mem_setOf_eq, SetLike.mem_coe]
    refine ⟨fun h x hx => ⟨(h x).1 hx, ((P D n).inv_mem h x).1 hx⟩, fun h x => ⟨fun hx => (h x hx).1, fun hx => ?_⟩⟩
    have := (h _ hx).2
    change (mat g⁻¹).mulVec ((mat g).mulVec x) ∈ _ at this
    rwa [Matrix.mulVec_mulVec, show mat g⁻¹ * mat g = mat (g⁻¹ * g) from rfl, inv_mul_cancel,
      show mat (1 : G D n) = 1 from rfl, Matrix.one_mulVec] at this
  have hU : IsClosed (upperHalf D n : Set (Fin (n + n) → AE D)) :=
    isClosed_eq (f := fun (x : Fin (n + n) → AE D) (i : Fin n) => x (finSumFinEquiv (Sum.inr i : Fin n ⊕ Fin n)))
      (g := fun _ => 0) (continuous_pi fun i => continuous_apply _) continuous_const
  rw [this]
  exact isClosed_biInter fun x _ => (hU.preimage (continuous_mat.matrix_mulVec continuous_const)).inter
    (hU.preimage ((continuous_mat.comp continuous_inv).matrix_mulVec continuous_const))

end GlobalTheory.StdUnn.HeightExists

namespace GlobalTheory.StdUnn


open HeightExists in
theorem exists_height : ∀ (D : D7) (n : ℕ), ∃ H : G D n → ℝ≥0, IsHeight H := by
  intro D n
  let δ : P D n →* ℝ≥0 := (absA D).comp (Matrix.GeneralLinearGroup.det.comp leviBlock)
  have hc : Continuous δ := continuous_absE.comp (continuous_detGL.comp continuous_leviBlock)
  haveI := t2Space_adeleRing' (F := D.host.F)
  have ht := triv_of_isCompact (δ := δ) isClosed_P hc isCompact_K
  refine ⟨iwAbs δ (K D n), fun p hp a ha k hk => ?_⟩
  rw [show a = leviBlock (D := D) (n := n) ⟨p, hp⟩ from Units.ext ha.symm]
  exact iwAbs_mul_of_triv ht ⟨p, hp⟩ hk

end GlobalTheory.StdUnn

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.CosetSumAlongMulEquivSubgroups
section
open scoped Matrix NNReal ComplexConjugate TensorProduct ContDiff
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel GlobalTheory.Core.Rk.SWLaw GlobalTheory.Core.Rk.SW GlobalTheory.StdUnn
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (RealMat IsFockVec)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (swSec sZero)
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.StdUnn

open scoped Matrix NNReal ComplexConjugate TensorProduct ContDiff in
open MeasureTheory IsDedekindDomain NumberField in
attribute [local instance] _root_.Formalism.BasicNotions.Host.cmStar in
private theorem bijective_quot_mk_map_out {G₁ G₂ : Type} [Group G₁] [Group G₂] (κ : G₁ ≃* G₂)
    (P₁ Γ₁ : Subgroup G₁) (P₂ Γ₂ : Subgroup G₂) (hP : ∀ g, g ∈ P₁ ↔ κ g ∈ P₂)
    (hΓ : ∀ g, g ∈ Γ₁ ↔ κ g ∈ Γ₂) :
    Function.Bijective fun q : _root_.GlobalTheory.AutomorphicL2Unitary.Quot (P₁.subgroupOf Γ₁) =>
      _root_.GlobalTheory.AutomorphicL2Unitary.mk (P₂.subgroupOf Γ₂)
        (⟨κ (Quotient.out q : Γ₁), (hΓ _).1 (Quotient.out q : Γ₁).2⟩ : Γ₂) := by
  have hout : ∀ q : _root_.GlobalTheory.AutomorphicL2Unitary.Quot (P₁.subgroupOf Γ₁),
      _root_.GlobalTheory.AutomorphicL2Unitary.mk (P₁.subgroupOf Γ₁) (Quotient.out q) = q := by
    intro q
    unfold _root_.GlobalTheory.AutomorphicL2Unitary.mk
    exact Quotient.out_eq q
  constructor
  · intro q q' h
    simp only at h
    obtain ⟨p, hp⟩ := _root_.GlobalTheory.AutomorphicL2Unitary.mk_eq_iff.1 h
    have hp' : κ.symm ((p : Γ₂) : G₂) * (Quotient.out q : Γ₁) = (Quotient.out q' : Γ₁) := by
      apply κ.injective
      have := congrArg Subtype.val hp
      simpa using this
    have hmemΓ : κ.symm ((p : Γ₂) : G₂) ∈ Γ₁ := by
      rw [hΓ]; simpa using ((p : Γ₂)).2
    have hmemP : (⟨κ.symm ((p : Γ₂) : G₂), hmemΓ⟩ : Γ₁) ∈ P₁.subgroupOf Γ₁ := by
      rw [Subgroup.mem_subgroupOf, hP]
      simpa using Subgroup.mem_subgroupOf.1 p.2
    rw [← hout q, ← hout q']
    refine _root_.GlobalTheory.AutomorphicL2Unitary.mk_eq_iff.2 ⟨⟨_, hmemP⟩, ?_⟩
    ext
    simpa using hp'
  · intro q₂
    obtain ⟨y, rfl⟩ : ∃ y : Γ₂, _root_.GlobalTheory.AutomorphicL2Unitary.mk (P₂.subgroupOf Γ₂) y = q₂ := by
      refine ⟨Quotient.out q₂, ?_⟩
      unfold _root_.GlobalTheory.AutomorphicL2Unitary.mk
      exact Quotient.out_eq q₂
    have hx : κ.symm (y : G₂) ∈ Γ₁ := by
      rw [hΓ]; simpa using y.2
    refine ⟨_root_.GlobalTheory.AutomorphicL2Unitary.mk (P₁.subgroupOf Γ₁) ⟨_, hx⟩, ?_⟩
    obtain ⟨p, hp⟩ := _root_.GlobalTheory.AutomorphicL2Unitary.mk_eq_iff.1
      (hout (_root_.GlobalTheory.AutomorphicL2Unitary.mk (P₁.subgroupOf Γ₁) ⟨_, hx⟩)).symm
    simp only
    rw [← hp]
    have hmemΓ : κ ((p : Γ₁) : G₁) ∈ Γ₂ := (hΓ _).1 (p : Γ₁).2
    have hmemP : (⟨κ ((p : Γ₁) : G₁), hmemΓ⟩ : Γ₂) ∈ P₂.subgroupOf Γ₂ := by
      rw [Subgroup.mem_subgroupOf]
      exact (hP _).1 (Subgroup.mem_subgroupOf.1 p.2)
    refine (_root_.GlobalTheory.AutomorphicL2Unitary.mk_eq_iff.2 ⟨⟨_, hmemP⟩, ?_⟩).symm
    ext
    simp


open scoped Matrix NNReal ComplexConjugate TensorProduct ContDiff in
open MeasureTheory IsDedekindDomain NumberField in
attribute [local instance] _root_.Formalism.BasicNotions.Host.cmStar in
theorem _root_.GlobalTheory.StdUnn.cosetSum_along_mulEquiv : ∀ (G₁ G₂ : Type) [Group G₁] [Group G₂] (κ : G₁ ≃* G₂) (P₁ Γ₁ : Subgroup G₁) (P₂ Γ₂ : Subgroup G₂), (∀ g, g ∈ P₁ ↔ κ g ∈ P₂) → (∀ g, g ∈ Γ₁ ↔ κ g ∈ Γ₂) → ∀ (Φ₂ : G₂ → ℂ) (x : G₁) (c : ℂ) (Φ₁ : G₁ → ℂ), (∀ g, Φ₁ g = c * Φ₂ (κ (g * x))) → _root_.GlobalTheory.AutomorphicL2Unitary.LeftInv (P₂ ⊓ Γ₂) Φ₂ → _root_.GlobalTheory.AutomorphicL2Unitary.LeftInv (P₁ ⊓ Γ₁) Φ₁ ∧ ∀ g, (_root_.GlobalTheory.Eis.CosetConv P₂ Γ₂ Φ₂ (κ (g * x)) → _root_.GlobalTheory.Eis.CosetConv P₁ Γ₁ Φ₁ g) ∧ _root_.GlobalTheory.Eis.cosetSum P₁ Γ₁ Φ₁ g = c * _root_.GlobalTheory.Eis.cosetSum P₂ Γ₂ Φ₂ (κ (g * x)) := by
  intro G₁ G₂ _ _ κ P₁ Γ₁ P₂ Γ₂ hP hΓ Φ₂ x c Φ₁ hΦ hinv₂
  have hinv₁ : _root_.GlobalTheory.AutomorphicL2Unitary.LeftInv (P₁ ⊓ Γ₁) Φ₁ := by
    unfold _root_.GlobalTheory.AutomorphicL2Unitary.LeftInv at hinv₂ ⊢
    intro γ hγ g
    have hγ₂ : κ γ ∈ P₂ ⊓ Γ₂ :=
      Subgroup.mem_inf.2 ⟨(hP γ).1 (Subgroup.mem_inf.1 hγ).1, (hΓ γ).1 (Subgroup.mem_inf.1 hγ).2⟩
    rw [hΦ, hΦ, mul_assoc, map_mul, hinv₂ _ hγ₂]
  have hbij := bijective_quot_mk_map_out κ P₁ Γ₁ P₂ Γ₂ hP hΓ
  have hbij₁ : Function.Bijective fun q : _root_.GlobalTheory.AutomorphicL2Unitary.Quot (P₁.subgroupOf Γ₁) =>
      _root_.GlobalTheory.AutomorphicL2Unitary.mk (P₁.subgroupOf Γ₁) (Quotient.out q) := by
    have : (fun q : _root_.GlobalTheory.AutomorphicL2Unitary.Quot (P₁.subgroupOf Γ₁) =>
        _root_.GlobalTheory.AutomorphicL2Unitary.mk (P₁.subgroupOf Γ₁) (Quotient.out q)) = id := by
      funext q
      unfold _root_.GlobalTheory.AutomorphicL2Unitary.mk
      exact Quotient.out_eq q
    rw [this]
    exact Function.bijective_id
  have hterm : ∀ (g : G₁) (q : _root_.GlobalTheory.AutomorphicL2Unitary.Quot (P₁.subgroupOf Γ₁)),
      Φ₁ (((Quotient.out q : Γ₁) : G₁) * g) =
        c * Φ₂ (((⟨κ (Quotient.out q : Γ₁), (hΓ _).1 (Quotient.out q : Γ₁).2⟩ : Γ₂) : G₂) *
          κ (g * x)) := by
    intro g q
    rw [hΦ, mul_assoc, map_mul]
  refine ⟨hinv₁, fun g => ⟨fun hconv => ?_, ?_⟩⟩
  · rw [_root_.GlobalTheory.Eis.cosetConv_iff hinv₁ hbij₁]
    rw [_root_.GlobalTheory.Eis.cosetConv_iff hinv₂ hbij] at hconv
    simp_rw [hterm g, norm_mul]
    exact hconv.mul_left _
  · rw [_root_.GlobalTheory.Eis.cosetSum_eq_tsum hinv₁ hbij₁,
      _root_.GlobalTheory.Eis.cosetSum_eq_tsum hinv₂ hbij]
    simp_rw [hterm g]
    exact tsum_mul_left

end GlobalTheory.StdUnn
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.DefiniteRealGroupFixesSplitSpaceWeilVacuum
section
noncomputable section
open scoped Matrix ComplexOrder
open Formalism.IndefR.Datum

namespace GlobalTheory.VacuumSplitReal

theorem trace_cartan_of_sig {k t : ℕ} (G s : Matrix (Fin k) (Fin k) ℂ) (hs : IsCartanInv G s)
    (hG : Formalism.UG.HasSignature G t t) (hk : k = 2 * t) : s.trace = 0 := by
  obtain ⟨e, P, hP⟩ := hG
  obtain ⟨Q, hQ⟩ : ∃ Q : Matrix (Fin t ⊕ Fin t) (Fin t ⊕ Fin t) ℂ, Q = (P : Matrix (Fin t ⊕ Fin t) (Fin t ⊕ Fin t) ℂ) := ⟨_, rfl⟩
  obtain ⟨Q', hQ'⟩ : ∃ Q' : Matrix (Fin t ⊕ Fin t) (Fin t ⊕ Fin t) ℂ,
      Q' = ((P⁻¹ : GL (Fin t ⊕ Fin t) ℂ) : Matrix (Fin t ⊕ Fin t) (Fin t ⊕ Fin t) ℂ) := ⟨_, rfl⟩
  have hQQ : Q' * Q = 1 := by rw [hQ, hQ', ← Units.val_mul, inv_mul_cancel, Units.val_one]
  let B0 : Matrix (Fin t ⊕ Fin t) (Fin t) ℂ := Matrix.fromRows 1 1
  let C0 : Matrix (Fin t) (Fin t ⊕ Fin t) ℂ := Matrix.fromCols 1 0
  have hC0 : C0 * B0 = 1 := by
    simp [C0, B0, Matrix.fromCols_mul_fromRows]
  have hPP : Qᴴ * G.reindex e e * Q = Formalism.UG.Jpq t t := by
    rw [← hP, hQ]; rfl
  have hB0 : B0ᴴ * Formalism.UG.Jpq t t * B0 = 0 := by
    simp [B0, Formalism.UG.Jpq, Matrix.conjTranspose_fromRows_eq_fromCols_conjTranspose, Matrix.fromCols_mul_fromBlocks,
      Matrix.fromCols_mul_fromRows]
  obtain ⟨B, hB⟩ : ∃ B : Matrix (Fin k) (Fin t) ℂ, B = (Q * B0).submatrix e id := ⟨_, rfl⟩
  obtain ⟨C, hC⟩ : ∃ C : Matrix (Fin t) (Fin k) ℂ, C = (C0 * Q').submatrix id e := ⟨_, rfl⟩
  have h1 : C * B = 1 := by
    rw [hB, hC, Matrix.submatrix_mul_equiv, Matrix.submatrix_id_id, Matrix.mul_assoc, ← Matrix.mul_assoc Q', hQQ,
      Matrix.one_mul, hC0]
  have h2 : Bᴴ * G * B = 0 := by
    have hG' : G = (G.reindex e e).submatrix e e := by
      ext i j; simp [Matrix.reindex_apply]
    rw [hB, Matrix.conjTranspose_submatrix, hG', Matrix.submatrix_mul_equiv, Matrix.submatrix_mul_equiv,
      Matrix.submatrix_id_id]
    have h3 : (Q * B0)ᴴ * G.reindex e e * (Q * B0) = B0ᴴ * (Qᴴ * G.reindex e e * Q) * B0 := by
      rw [Matrix.conjTranspose_mul]; simp only [Matrix.mul_assoc]
    rw [h3, hPP, hB0]
  exact GlobalTheory.SplitVacSum.trace_eq_zero hs.1 hs.2.2 (m := t) (by rw [Fintype.card_fin, hk]) B C h1 h2

end GlobalTheory.VacuumSplitReal

open scoped ComplexConjugate Matrix NNReal
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.Cusp GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (FinPl RealMat Lat IsFockVec IsSphOff HidaSetting volQ)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (ip delta swSec sZero IsKFinVec)
open GlobalTheory.Mem.Th (CptF)
open GlobalTheory.Core.Rk.IP
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Core.Rk.Exh GlobalTheory.RegSW

namespace GlobalTheory.VacuumSplitReal

theorem vacuum_fixed : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (A H : HSp D) (t : ℕ) (χA : (AE D)ˣ →* Circle) (om : WRep A H) (sH : RealMat H), IsInfFam θ → (∃ η, GlobalTheory.WeilParts.IsEtaTilde D η) → IsWeilDatumO ψ A H χA 1 om → (∀ τ, IsCartanInv (gramAt D A τ) 1) → (∀ τ, IsCartanInv (gramAt D H τ) (sH τ)) → HSpace.SigOK H → H.rank = 2 * t → (∀ τ, H.sig τ = (t, t)) → ∀ f, IsThetaFunO ψ A H f → (∀ τ, IsFockVacAt (heisO ψ A H) θ τ (cplxO 1 (sH τ)) f) → ∀ b ∈ GinfC A, om (b, 1) f = f := by
  intro D ψ θ A H t χA om sH hθ ⟨η, hη⟩ hW hA hH hsig hrank hsigt f hf hv b hb
  have hdet : ∀ {k : ℕ} {G s : Matrix (Fin k) (Fin k) ℂ}, IsCartanInv G s → G.det ≠ 0 := fun {k G s} hG => by
    have := hG.2.2.det_pos.ne'
    rw [Matrix.det_mul] at this
    exact left_ne_zero_of_mul this
  obtain ⟨x, hx, hxv⟩ := GlobalTheory.VacuumCharacter.exists_root hθ A (fun τ => hdet (hA τ)) b hb
  have mt1 : ∀ τ, compAt θ τ (Formalism.L2.Theta.mt H 1) = 1 := fun τ => by
    unfold Formalism.L2.Theta.mt compAt
    rw [map_one, Units.val_one]
    exact Matrix.map_one _ (by simp) (by simp)
  have h1 : ∀ τ, HasInfExp D 1 τ 0 := fun τ => ⟨0, by norm_num, ⟨θ, hθ⟩, fun _ _ _ _ _ => by simp⟩
  have hexp : ∀ τ, HasInfExp D (1 * (η ^ H.rank)⁻¹) τ ((-(t : ℤ) : ℤ) : ℚ) := fun τ => by
    have h := GlobalTheory.VacuumCharacter.hasInfExp_twist (h1 τ) (hη.2.2.2 τ) H.rank
    convert h using 1
    rw [hrank]; push_cast; ring
  have hν := hxv _ (fun _ => -(t : ℤ)) hexp
  rw [GlobalTheory.WeilVacChar.vacuum_character D ψ hW.std A H θ hθ χA 1 om η hη hW (fun _ => 1) sH hA hH b hb 1 (one_mem _)
    (fun τ => by rw [one_mul, mul_one]) (fun τ => by rw [mt1, one_mul, mul_one]) x 1 hx ?_ f hf hv]
  · conv_rhs => rw [← one_smul ℂ f]
    congr 1
    rw [Circle.coe_mul, Circle.coe_inv, hν, MonoidHom.map_one, Circle.coe_one, mul_one, ← Finset.prod_inv_distrib,
      ← Finset.prod_mul_distrib]
    refine Finset.prod_eq_one fun τ _ => ?_
    obtain ⟨p, hp, hd⟩ := GlobalTheory.VacuumCharacter.detPlus_one (n := A.rank) (sH τ) (hH τ).1
    have htr : (sH τ).trace = 0 := by
      have hs := hsig (tauE D τ)
      rw [hsigt] at hs
      exact trace_cartan_of_sig (gramAt D H τ) (sH τ) (hH τ) hs hrank
    have hpt : p = t := by
      have : (p : ℂ) = t := by
        rw [htr, hrank] at hp; push_cast at hp; linear_combination -hp / 2
      exact_mod_cast this
    have inv : (compAt θ τ (Formalism.L2.Theta.mt A b)).det * (compAt θ τ (Formalism.L2.Theta.mt A b⁻¹)).det = 1 := by
      rw [GlobalTheory.VacuumCharacter.det_compAt, GlobalTheory.VacuumCharacter.det_compAt, ← map_mul, ← map_mul, ← Matrix.det_mul]
      unfold Formalism.L2.Theta.mt
      rw [← Units.val_mul, ← map_mul, mul_inv_cancel, map_one, Units.val_one, Matrix.det_one, map_one, map_one]
    have d0 := left_ne_zero_of_mul_eq_one inv
    rw [mt1, (hd _ 1 (by rw [one_mul, mul_one])).1, eq_inv_of_mul_eq_one_right inv, hpt, mul_one,
      show (1 / 2 : ℂ) • (1 + sH τ) + (1 / 2 : ℂ) • (1 - sH τ) = 1 by module, Matrix.det_one, one_pow, one_mul,
      zpow_neg, inv_inv, zpow_natCast, inv_pow, mul_inv_cancel₀ (pow_ne_zero _ d0)]
  · unfold Formalism.L2.Theta.IsDetRoot
    simp

end GlobalTheory.VacuumSplitReal

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.DoubleLiftFockSumEqSumIteratedLifts
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.SeeSaw
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.SeeSaw

variable {D : D7}

theorem comb_sum_mul (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (c : WO S T →₀ ℂ) {n : ℕ} (a : Fin n → ℂ)
    (F : Fin n → WO S T → ℂ) :
    comb ψ S T c (fun w => ∑ i, a i * F i w) = fun w => ∑ i, a i * comb ψ S T c (F i) w := by
  funext w
  simp only [comb, heisO, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun u _ => by ring

theorem comb_pureTensorO (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (S T : HSp D) (hψ : IsStdChar D ψ (-1))
    (hθ : IsInfFam θ) (sS sT BS BT) (f : WO S T → ℂ) (hf : IsThetaFunO ψ S T f) (c : WO S T →₀ ℂ)
    (hc : IsFinComb c) (P : PolF D T.rank S.rank) :
    comb ψ S T c (pureTensorO ψ θ S T sS sT BS BT f P) = pureTensorO ψ θ S T sS sT BS BT (comb ψ S T c f) P := by
  let e := c.support.equivFin
  have key := (_root_.GlobalTheory.FockFiniteHeis.heis_comb_pureTensorO D ψ θ S T hψ hθ sS sT BS BT f hf c.support.card (fun i => c (e.symm i).1)
    (fun i => (e.symm i).1) (fun i => hc _ (e.symm i).2) P).1
  have h1 : ∀ g : WO S T → (WO S T → ℂ), ∑ u ∈ c.support, c u • g u = ∑ i, c (e.symm i).1 • g (e.symm i).1 := by
    intro g
    rw [← Finset.sum_coe_sort c.support]
    exact (Equiv.sum_comp e.symm (fun u : c.support => c u.1 • g u.1)).symm
  simp only [comb]
  rw [h1, h1]
  exact key

theorem integrableOn_kernel {S T : HSp D} (hS : CoCpt S) (v : Vol S) {ψ : AddChar (AF D.host.F) ℂ}
    {χS χT : (AE D)ˣ →* Circle} {om : Om S T} (hw : IsWeilDatumO ψ S T χS χT om) {f : WO S T → ℂ}
    (hf : IsThetaFunO ψ S T f) {φ : GA D S → ℂ} (hφ : IsContAut S φ) (h : GA D T) :
    IntegrableOn (fun g => om (g, h) f 0 * φ g) v.𝓕 v.μ := by
  have hc : Continuous fun g : GA D S => om (g, h) f 0 :=
    (hw.om_cont f hf 0).comp (by fun_prop : Continuous fun g : GA D S => (g, h))
  refine (_root_.GlobalTheory.CocompactParam.continuous_integral_param D S hS v Unit (fun g _ => om (g, h) f 0 * φ g) ((hc.mul hφ.2).comp continuous_fst) ?_).1 ()
  intro γ hγ g _
  have e : ((γ * g, h) : GA D S × GA D T) = (γ, 1) * (g, h) := by simp
  rw [e, map_mul, Module.End.mul_apply, hw.om_aut γ hγ 1 (one_mem _) _ (hw.om_pres _ _ hf), hφ.1 γ hγ g]

theorem biLift_biComb_fockSum : ∀ (D : D7), BiAct D → CenFock D → LiftSum D → ∀ (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D), IsInfFam θ → ∀ (A S A' : HSp D) (x : DefSp A) (y : DefSp S) (z : DefSp A'), x.Is → y.Is → z.Is → ∀ (k : KerDat A S) (k' : KerDat S A'), k.Is ψ θ x y → k'.Is ψ θ y z → ∀ (n : ℕ) (P : Fin n → PolF D S.rank A.rank) (P' : Fin n → PolF D A'.rank S.rank) (C : WO A S → WO S A' → ℂ), (∀ u v, C u v = ∑ i, pureTensorO ψ θ A S x.s y.s x.B y.B k.vac (P i) u * pureTensorO ψ θ S A' y.s z.s y.B z.B k'.vac (P' i) v) → ∀ φ, IsContAut A φ → biLift k.om k'.om x.vol y.vol φ (biComb ψ A S A' k.c k'.c C) = ∑ i, k'.lift ψ θ y z (P' i) (k.lift ψ θ x y (P i) φ) := by
  intro D _ _ hL ψ θ hθ A S A' x y z hx hy hz k k' hk hk' n P P' C hC φ hφ
  obtain ⟨χA, χS, hwA⟩ := hk.weil
  obtain ⟨χS', χA', hwB⟩ := hk'.weil
  have hX : ∀ i, IsThetaFunO ψ A S (k.pt ψ θ x y (P i)) := fun i => (hL ψ θ hθ A S x y hx hy k hk (P i)).1
  have hY : ∀ i, IsThetaFunO ψ S A' (k'.pt ψ θ y z (P' i)) := fun i => (hL ψ θ hθ S A' y z hy hz k' hk' (P' i)).1
  have hLc : ∀ i, IsContAut S (k.lift ψ θ x y (P i) φ) := fun i => (hL ψ θ hθ A S x y hx hy k hk (P i)).2.1 φ hφ
  have hcX : ∀ i, comb ψ A S k.c (pureTensorO ψ θ A S x.s y.s x.B y.B k.vac (P i)) = k.pt ψ θ x y (P i) := fun i =>
    comb_pureTensorO ψ θ A S hwA.std hθ _ _ _ _ k.vac hk.vac.2.theta k.c hk.fin (P i)
  have hcY : ∀ i, comb ψ S A' k'.c (pureTensorO ψ θ S A' y.s z.s y.B z.B k'.vac (P' i)) = k'.pt ψ θ y z (P' i) :=
    fun i => comb_pureTensorO ψ θ S A' hwB.std hθ _ _ _ _ k'.vac hk'.vac.2.theta k'.c hk'.fin (P' i)
  have hbi : biComb ψ A S A' k.c k'.c C = fun u v => ∑ i, k.pt ψ θ x y (P i) u * k'.pt ψ θ y z (P' i) v := by
    funext u v
    simp only [biComb]
    have e1 : (fun u' => comb ψ S A' k'.c (C u') v) = fun u' => ∑ i,
        comb ψ S A' k'.c (pureTensorO ψ θ S A' y.s z.s y.B z.B k'.vac (P' i)) v *
          pureTensorO ψ θ A S x.s y.s x.B y.B k.vac (P i) u' := by
      funext u'
      have : C u' = fun v => ∑ i, pureTensorO ψ θ A S x.s y.s x.B y.B k.vac (P i) u' *
          pureTensorO ψ θ S A' y.s z.s y.B z.B k'.vac (P' i) v := funext (hC u')
      rw [this, comb_sum_mul]
      exact Finset.sum_congr rfl fun i _ => mul_comm _ _
    rw [e1, comb_sum_mul]
    simp only [hcX, hcY]
    exact Finset.sum_congr rfl fun i _ => mul_comm _ _
  have hint : ∀ h₀ h₁ h₂, k'.om (h₁, h₂) (fun v => k.om (h₀, h₁)
      (fun u => ∑ i, k.pt ψ θ x y (P i) u * k'.pt ψ θ y z (P' i) v) 0) 0 =
      ∑ i, k.om (h₀, h₁) (k.pt ψ θ x y (P i)) 0 * k'.om (h₁, h₂) (k'.pt ψ θ y z (P' i)) 0 := by
    intro h₀ h₁ h₂
    have e1 : ∀ v, (fun u => ∑ i, k.pt ψ θ x y (P i) u * k'.pt ψ θ y z (P' i) v) =
        ∑ i, k'.pt ψ θ y z (P' i) v • k.pt ψ θ x y (P i) := by
      intro v; funext u; simp [Finset.sum_apply, mul_comm]
    have e2 : (fun v => k.om (h₀, h₁) (fun u => ∑ i, k.pt ψ θ x y (P i) u * k'.pt ψ θ y z (P' i) v) 0) =
        ∑ i, k.om (h₀, h₁) (k.pt ψ θ x y (P i)) 0 • k'.pt ψ θ y z (P' i) := by
      funext v; rw [e1 v, map_sum]; simp [Finset.sum_apply, mul_comm]
    set_option synthInstance.maxHeartbeats 100000 in
      rw [e2, map_sum]; simp [Finset.sum_apply]
  funext h₂
  have hin : ∀ h₁, ∫ h₀ in x.vol.𝓕, φ h₀ * ∑ i, k.om (h₀, h₁) (k.pt ψ θ x y (P i)) 0 *
      k'.om (h₁, h₂) (k'.pt ψ θ y z (P' i)) 0 ∂x.vol.μ =
      ∑ i, k.lift ψ θ x y (P i) φ h₁ * k'.om (h₁, h₂) (k'.pt ψ θ y z (P' i)) 0 := by
    intro h₁
    have e : (fun h₀ => φ h₀ * ∑ i, k.om (h₀, h₁) (k.pt ψ θ x y (P i)) 0 *
        k'.om (h₁, h₂) (k'.pt ψ θ y z (P' i)) 0) = fun h₀ => ∑ i,
          k.om (h₀, h₁) (k.pt ψ θ x y (P i)) 0 * φ h₀ * k'.om (h₁, h₂) (k'.pt ψ θ y z (P' i)) 0 := by
      funext h₀; rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun i _ => by ring
    rw [e, integral_finsetSum]
    · refine Finset.sum_congr rfl fun i _ => ?_
      rw [integral_mul_const]
      rfl
    · intro i _
      exact (integrableOn_kernel hx.cpt x.vol hwA (hX i) hφ h₁).mul_const _
  simp only [biLift, hbi, hint, hin, Finset.sum_apply]
  rw [integral_finsetSum]
  · refine Finset.sum_congr rfl fun i _ => ?_
    simp only [KerDat.lift, liftT_apply]
    congr 1
    funext h₁
    exact mul_comm _ _
  · intro i _
    have := (integrableOn_kernel hy.cpt y.vol hwB (hY i) (hLc i) h₂)
    exact Integrable.congr this (Filter.Eventually.of_forall fun h₁ => mul_comm _ _)

end GlobalTheory.SeeSaw
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.DoubledFlatSectionEqTranslateStandardSection
section
open scoped Matrix NNReal ComplexConjugate TensorProduct ContDiff
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel GlobalTheory.Core.Rk.SWLaw GlobalTheory.Core.Rk.SW GlobalTheory.StdUnn
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (RealMat IsFockVec)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (swSec sZero)
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.StdUnn

theorem flat_swSec_eq_sect : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (A B : HSp D) (χB : (AE D)ˣ →* Circle) (omh : GA D (dblSp A) × GA D B →* Module.End ℂ (WO (dblSp A) B → ℂ)), IsWeilDatumO ψ (dblSp A) B 1 χB omh → ∀ (ν : Measure (WO A B)) (𝓨 : Set (WO A B)), IsCovolOne (ratL B A) ν 𝓨 → ∀ θ : InfFam D, IsInfFam θ → ∀ μ : D.host.E, IsSkew μ → ∀ κ : GA D (dblSp A) ≃* G D A.rank, IsChart A μ κ → ∀ omS : G D A.rank →* Module.End ℂ (schwartzA θ B.rank A.rank), IsTransport ψ θ A B ν 𝓨 omh κ omS → ∀ lam : D.host.F, algebraMap D.host.F D.host.E lam = -D.host.xi0 / μ → ∀ (a : GL (Fin A.rank) (AE D)) (p : siegel A) (f : WO (dblSp A) B → ℂ), IsThetaFunO ψ (dblSp A) B f → ∀ Φ : schwartzA θ B.rank A.rank, Φ.1 = sch ψ A B ν 𝓨 (omh ((p : GA D (dblSp A))⁻¹, 1) f) → s0 B A.rank = sZero A B ∧ (∀ (z : ℂ) (g : GA D (dblSp A)), flat A a (swSec A B omh ν 𝓨 f) (sZero A B) z g = npow (absA D (aP A p)) (sZero A B - z) * sect omS (hgtStd A a κ p) Φ z (κ (g * p))) ∧ ∀ g : GA D (dblSp A), (omS (κ (g * p)) Φ).1 = sch ψ A B ν 𝓨 (omh (g, 1) f) := by
  intro D ψ A B χB omh hW ν 𝓨 _ θ _ μ _ κ _ omS hT lam _ a p f hf Φ hΦ
  have h0 : s0 B A.rank = sZero A B := by unfold s0 sZero; ring
  have h3 : ∀ g : GA D (dblSp A), (omS (κ (g * p)) Φ).1 = sch ψ A B ν 𝓨 (omh (g, 1) f) := fun g => by
    rw [hT (g * p) _ (hW.om_pres _ f hf) Φ hΦ, ← Module.End.mul_apply, ← map_mul, Prod.mk_mul_mk, mul_one,
      mul_inv_cancel_right]
  refine ⟨h0, fun z g => ?_, h3⟩
  have hp : 0 < absA D (aP A p) := hom_pos _ _
  have h1 : npow (absA D (aP A p)) (sZero A B - z) * npow (absA D (aP A p)) (z - sZero A B) = 1 := by
    rw [← npow_add hp, show sZero A B - z + (z - sZero A B) = 0 by ring, npow_zero]
  have h2 : hgtStd A a κ p (κ (g * p)) = hgt A a g * absA D (aP A p) := by
    rw [hgtStd, MulEquiv.symm_apply_apply, mul_inv_cancel_right]
  have h4 : sch ψ A B ν 𝓨 (omh (g, 1) f) 0 = swSec A B omh ν 𝓨 f g := mixS_dblDec_zero A B ψ ν 𝓨 _ 0
  have h5 : flat A a (swSec A B omh ν 𝓨 f) (sZero A B) z g =
      swSec A B omh ν 𝓨 f g * npow (hgt A a g) (z - sZero A B) := rfl
  rw [h5, sect, h3, h4, h2, h0, npow_mul]
  linear_combination (-(swSec A B omh ν 𝓨 f g * npow (hgt A a g) (z - sZero A B))) * h1

end GlobalTheory.StdUnn
end

