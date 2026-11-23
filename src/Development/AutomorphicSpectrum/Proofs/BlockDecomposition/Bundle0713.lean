module

public import Mathlib
public import Development.WeilBound.CoreStatements.AutomorphicKernels.UnitarySchrodingerModel.CoefDataExists
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0633
public import Development.AbelianVarietyTheory.PublishedTheorems.SiegelWeil₂.Bundle0002
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0262
public import Development.AutomorphicSpectrum.Proofs.GlobalProofs.SummableCell
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0495
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0464
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0625
public import Development.WeilBound.RepresentationTheoryGL.RegularisedSiegelWeil.HermitianCellMeasures.Bundle0001
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0710
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.FrameReading.ExpToSat
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.IwahoriFactorisation.StrictDominance.SatakeSocle.SatBridge
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0341
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0708
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0589
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0356
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0565
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SatakeParameterSphericalProductSpehQuotients
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0623
public import Development.AutomorphicSpectrum.Proofs.GlobalProofs.Bundle0030
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0704
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1743
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1766

@[expose] public section

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.BigCellCosetsHermitianParam
section
noncomputable section
open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC PositivityTheory.PfSWUS GlobalTheory.Eis GlobalTheory.CompanionTheory.SwUnf
open PositivityTheory.GramSchwartzFunctions.EC GlobalTheory.StdUnn.Model GlobalTheory.StdUnn.LeftInvSect GlobalTheory.CompanionTheory.Hypotheses₂.WeilU

namespace GlobalTheory.CompanionTheory.SwUnf.BigCell

section Field

variable {K : Type} [Field K] {n : ℕ}

theorem cT_mul_sq (σ : K →+* K) (x y : Matrix (Fin n) (Fin n) K) : cT σ (x * y) = cT σ y * cT σ x := by
  unfold cT
  rw [Matrix.map_mul, Matrix.transpose_mul]

theorem cT_one_sq (σ : K →+* K) : cT σ (1 : Matrix (Fin n) (Fin n) K) = 1 := by
  unfold cT
  rw [Matrix.map_one _ (map_zero σ) (map_one σ), Matrix.transpose_one]

theorem cT_blk4 (σ : K →+* K) (a b c d : Matrix (Fin n) (Fin n) K) :
    cT σ (blk4 a b c d) = blk4 (cT σ a) (cT σ c) (cT σ b) (cT σ d) := by
  ext i j
  simp only [cT, blk4, Matrix.transpose_apply, Matrix.map_apply, Matrix.submatrix_apply]
  rcases finSumFinEquiv.symm i with i | i <;> rcases finSumFinEquiv.symm j with j | j <;> rfl

theorem block_identity_eq_one {R : Type} [CommRing R] : blk4 (1 : Matrix (Fin n) (Fin n) R) 0 0 1 = 1 := by
  unfold blk4
  rw [Matrix.fromBlocks_one, Matrix.submatrix_one_equiv]

theorem lowerLeft_block {R : Type} (a b c d : Matrix (Fin n) (Fin n) R) : lowerC (blk4 a b c d) = c := by
  ext i j
  simp [lowerC, blk4]

theorem exists_blockMatrixTwoByTwoFin_eq {R : Type} (M : Matrix (Fin (n + n)) (Fin (n + n)) R) :
    ∃ a b, M = blk4 a b (lowerC M) (GlobalTheory.CompanionTheory.RatPtsUnn.blkD M) := by
  refine ⟨(M.submatrix finSumFinEquiv finSumFinEquiv).toBlocks₁₁,
    (M.submatrix finSumFinEquiv finSumFinEquiv).toBlocks₁₂, ?_⟩
  have h : Matrix.fromBlocks (M.submatrix finSumFinEquiv finSumFinEquiv).toBlocks₁₁
      (M.submatrix finSumFinEquiv finSumFinEquiv).toBlocks₁₂ (lowerC M) (GlobalTheory.CompanionTheory.RatPtsUnn.blkD M) =
      M.submatrix finSumFinEquiv finSumFinEquiv :=
    Matrix.fromBlocks_toBlocks _
  unfold blk4
  rw [h]
  ext i j
  simp

theorem isSiegelParabolic_iff (M : Matrix (Fin (n + n)) (Fin (n + n)) K) : IsSiegelP M ↔ lowerC M = 0 := by
  constructor
  · intro h
    ext i j
    exact h i j
  · intro h i j
    exact congrFun (congrFun h i) j

theorem cellKer_eq_bot_iff' {E : Type} [Field E] (C : Matrix (Fin n) (Fin n) E) :
    LinearMap.ker C.mulVecLin = ⊥ ↔ IsUnit C.det := by
  rw [LinearMap.ker_eq_bot, ← Matrix.isUnit_iff_isUnit_det, ← Matrix.mulVec_injective_iff_isUnit]
  rfl

abbrev cellM (b : Matrix (Fin n) (Fin n) K) : Matrix (Fin (n + n)) (Fin (n + n)) K := blk4 0 1 (-1) (-b)

theorem cellM_mul (b : Matrix (Fin n) (Fin n) K) : cellM b * blk4 (-b) (-1) 1 0 = 1 := by
  rw [cellM, submatrix_fromBlocks_mul]
  simp [block_identity_eq_one]

theorem mul_cellM (b : Matrix (Fin n) (Fin n) K) : blk4 (-b) (-1) 1 0 * cellM b = 1 := by
  rw [cellM, submatrix_fromBlocks_mul]
  simp [block_identity_eq_one]

theorem cellM_det (b : Matrix (Fin n) (Fin n) K) : IsUnit (cellM b).det :=
  Matrix.isUnit_det_of_left_inverse (mul_cellM b)

theorem cellM_inv (b : Matrix (Fin n) (Fin n) K) : (cellM b)⁻¹ = blk4 (-b) (-1) 1 0 :=
  Matrix.inv_eq_right_inv (cellM_mul b)

theorem lower_rel (σ : K →+* K) {A B C Dd : Matrix (Fin n) (Fin n) K}
    (h : IsUnitary σ (blk4 0 1 (-1) 0) (blk4 A B C Dd)) : Dd * cT σ C = C * cT σ Dd := by
  have hJJ : (blk4 0 1 (-1) 0 : Matrix (Fin (n + n)) (Fin (n + n)) K) * blk4 0 (-1) 1 0 = 1 := by
    rw [submatrix_fromBlocks_mul]
    simp [block_identity_eq_one]
  have hJJ' : (blk4 0 (-1) 1 0 : Matrix (Fin (n + n)) (Fin (n + n)) K) * blk4 0 1 (-1) 0 = 1 := by
    rw [submatrix_fromBlocks_mul]
    simp [block_identity_eq_one]
  have h0 : cT σ (blk4 A B C Dd) * blk4 0 1 (-1) 0 * blk4 A B C Dd = blk4 0 1 (-1) 0 := h
  have h1 : (blk4 0 (-1) 1 0 * cT σ (blk4 A B C Dd) * blk4 0 1 (-1) 0) * blk4 A B C Dd = 1 := by
    rw [mul_assoc (blk4 0 (-1) 1 0), mul_assoc (blk4 0 (-1) 1 0), h0, hJJ']
  have h2 := mul_eq_one_comm.1 h1
  have h3 : blk4 A B C Dd * blk4 0 (-1) 1 0 * cT σ (blk4 A B C Dd) = blk4 0 (-1) 1 0 := by
    calc _ = blk4 A B C Dd * (blk4 0 (-1) 1 0 * cT σ (blk4 A B C Dd) * blk4 0 1 (-1) 0) * blk4 0 (-1) 1 0 := by
          simp only [mul_assoc, hJJ, mul_one]
      _ = _ := by rw [h2, one_mul]
  rw [cT_blk4, submatrix_fromBlocks_mul, submatrix_fromBlocks_mul] at h3
  obtain ⟨-, -, -, h4⟩ := blockMatrixTwoByTwoFin_injective h3
  simp only [mul_zero, mul_neg, mul_one, zero_add, add_zero] at h4
  exact sub_eq_zero.1 (by simpa [sub_eq_add_neg, add_comm] using h4)

theorem herm_of_rel (σ : K →+* K) {C Dd : Matrix (Fin n) (Fin n) K} (hC : IsUnit C.det)
    (h : Dd * cT σ C = C * cT σ Dd) : cT σ (C⁻¹ * Dd) = C⁻¹ * Dd := by
  have a1 : C⁻¹ * C = 1 := Matrix.nonsing_inv_mul _ hC
  have b1 : cT σ C * cT σ C⁻¹ = 1 := by rw [← cT_mul_sq, a1, cT_one_sq]
  have b2 : C⁻¹ * Dd * cT σ C = cT σ Dd := by rw [mul_assoc, h, ← mul_assoc, a1, one_mul]
  rw [cT_mul_sq, ← b2, mul_assoc, b1, mul_one]

theorem lower_unit {x : Matrix (Fin (n + n)) (Fin (n + n)) K} (hx : IsUnit x.det) (b : Matrix (Fin n) (Fin n) K)
    (hS : IsSiegelP (x * (cellM b)⁻¹)) : IsUnit (lowerC x).det := by
  rw [cellM_inv] at hS
  set S := x * blk4 (-b) (-1) 1 0 with hSd
  have hSx : S * cellM b = x := by rw [hSd, mul_assoc, mul_cellM, mul_one]
  have hdet : IsUnit S.det := by
    rw [hSd, Matrix.det_mul]
    exact hx.mul (Matrix.isUnit_det_of_left_inverse (cellM_mul b))
  have hd : IsUnit (GlobalTheory.CompanionTheory.RatPtsUnn.blkD S).det := by
    rw [GlobalTheory.CompanionTheory.RatPtsUnn.det_eq_of_lowerLeft_zero S hS] at hdet
    exact isUnit_of_mul_isUnit_right hdet
  obtain ⟨a, c, hb⟩ := exists_blockMatrixTwoByTwoFin_eq S
  have h0 : lowerC S = 0 := (isSiegelParabolic_iff S).1 hS
  rw [h0] at hb
  have e : lowerC x = -GlobalTheory.CompanionTheory.RatPtsUnn.blkD S := by
    rw [← hSx, hb, cellM, submatrix_fromBlocks_mul, lowerLeft_block, ← hb]
    simp
  rw [e, ← Matrix.isUnit_iff_isUnit_det]
  exact ((Matrix.isUnit_iff_isUnit_det _).2 hd).neg

theorem of_lower_unit (σ : K →+* K) {x : Matrix (Fin (n + n)) (Fin (n + n)) K}
    (hu : IsUnitary σ (blk4 0 1 (-1) 0) x) (hC : IsUnit (lowerC x).det) :
    cT σ ((lowerC x)⁻¹ * GlobalTheory.CompanionTheory.RatPtsUnn.blkD x) = (lowerC x)⁻¹ * GlobalTheory.CompanionTheory.RatPtsUnn.blkD x ∧
      IsSiegelP (x * (cellM ((lowerC x)⁻¹ * GlobalTheory.CompanionTheory.RatPtsUnn.blkD x))⁻¹) := by
  obtain ⟨a, b, hb⟩ := exists_blockMatrixTwoByTwoFin_eq x
  have hu' : IsUnitary σ (blk4 0 1 (-1) 0) (blk4 a b (lowerC x) (GlobalTheory.CompanionTheory.RatPtsUnn.blkD x)) := by
    rw [← hb]
    exact hu
  refine ⟨herm_of_rel σ hC (lower_rel σ hu'), ?_⟩
  rw [cellM_inv, isSiegelParabolic_iff]
  have a2 : lowerC x * (lowerC x)⁻¹ = 1 := Matrix.mul_nonsing_inv _ hC
  generalize hl : (lowerC x)⁻¹ * GlobalTheory.CompanionTheory.RatPtsUnn.blkD x = l
  have e : lowerC x * l = GlobalTheory.CompanionTheory.RatPtsUnn.blkD x := by
    rw [← hl, ← mul_assoc, a2, one_mul]
  conv_lhs => rw [hb]
  rw [submatrix_fromBlocks_mul, lowerLeft_block, mul_neg, e]
  simp

end Field

variable {D : D7} {n : ℕ}

theorem ratOf_spec (γ : GF D n) : IsUnit (ratOf γ).det ∧
    IsUnitary (D.sp.cm.sig : D.host.E →+* D.host.E) (blk4 0 1 (-1) 0) (ratOf γ) := by
  obtain ⟨g, hd, hu, hm⟩ := GlobalTheory.CompanionTheory.RatPtsUnn.clause1 γ.1 γ.2
  have e : ratOf γ = g := Matrix.map_injective incA_injective ((mat_ratOf γ).symm.trans hm)
  rw [e]
  exact ⟨hd, hu⟩

theorem mat_cell_rat {w u : G D n} (hw : mat w = blk4 0 1 (-1) 0) (b : Matrix (Fin n) (Fin n) D.host.E)
    (hu : mat u = blk4 1 (b.map (incA D)) 0 1) : mat (w * u) = (cellM b).map (incA D) := by
  rw [mat_cell hw hu, cellM, blk4_map_alt]
  have e0 : (0 : Matrix (Fin n) (Fin n) D.host.E).map (incA D) = 0 := map_zero (incA D).mapMatrix
  have e1 : (1 : Matrix (Fin n) (Fin n) D.host.E).map (incA D) = 1 := map_one (incA D).mapMatrix
  have e2 : (-1 : Matrix (Fin n) (Fin n) D.host.E).map (incA D) = -1 := by
    have := map_neg (incA D).mapMatrix (1 : Matrix (Fin n) (Fin n) D.host.E)
    rwa [map_one] at this
  have e3 : (-b).map (incA D) = -(b.map (incA D)) := map_neg (incA D).mapMatrix b
  rw [e0, e1, e2, e3]

theorem exists_hermQ (l : ratHerm D n) : ∃ b : HermQ D n, b.1.map (incA D) = l.1.1 := by
  have hm : l.1.1 ∈ ratMx D n n := l.2
  obtain ⟨b, hb⟩ := hm
  have hb' : b.map (incA D) = l.1.1 := hb
  have hadj : adj (b.map (incA D) : Mx D n n) = b.map (incA D) := by
    rw [hb']
    exact l.1.2
  refine ⟨⟨b, fun i j => incA_injective ?_⟩, hb'⟩
  exact congrFun (congrFun hadj i) j

theorem bigCell : ∀ {D : D7} {n : ℕ} {w : G D n}, mat w = blk4 0 1 (-1) 0 → ∀ {nb : hermA D n → G D n}, IsNMap nb → ∃ e : ratHerm D n → Cosets (P D n) (GF D n), Function.Injective e ∧ (∀ q, cosetCell q = ⊥ ↔ q ∈ Set.range e) ∧ ∀ f : G D n → ℂ, LeftInv (P D n ⊓ GF D n) f → ∀ (l : ratHerm D n) (y : G D n), term (P D n) (GF D n) f y (e l) = f (w * nb l.1 * y) := by
  intro D n w hw nb hnb
  choose β hβ using exists_hermQ (D := D) (n := n)
  have hu : ∀ l, mat (nb l.1) = blk4 1 ((β l).1.map (incA D)) 0 1 := fun l => by
    rw [hβ]
    exact hnb l.1
  let c : ratHerm D n → GF D n := fun l => ⟨w * nb l.1, cell_mem_GF hw (β l) (hu l)⟩
  have hc : ∀ l, mat (c l).1 = (cellM (β l).1).map (incA D) := fun l => mat_cell_rat hw _ (hu l)
  refine ⟨fun l => mk ((P D n).subgroupOf (GF D n)) (c l), ?_, ?_, ?_⟩
  · intro l l' h
    obtain ⟨δ, hδ⟩ := mk_eq_iff.1 h
    have hP : (w * nb l'.1) * (w * nb l.1)⁻¹ ∈ P D n := by
      have e : (w * nb l'.1) * (w * nb l.1)⁻¹ = δ.1.1 := by
        have := congrArg Subtype.val hδ
        change δ.1.1 * (w * nb l.1) = w * nb l'.1 at this
        rw [← this]
        exact mul_inv_cancel_right _ _
      rw [e]
      exact Subgroup.mem_subgroupOf.1 δ.2
    have hbb := cell_inj hw (hu l) (hu l') hP
    apply Subtype.ext
    apply Subtype.ext
    rw [← hβ l, ← hβ l', hbb]
  · intro q
    have hspec := ratOf_spec (Quotient.out q)
    have hker : cosetCell q = ⊥ ↔ IsUnit (lowerC (ratOf (Quotient.out q))).det :=
      cellKer_eq_bot_iff' _
    rw [hker]
    constructor
    · intro hC
      obtain ⟨hh, hS⟩ := of_lower_unit _ hspec.2 hC
      set lam := (lowerC (ratOf (Quotient.out q)))⁻¹ * GlobalTheory.CompanionTheory.RatPtsUnn.blkD (ratOf (Quotient.out q)) with hlam
      let b : HermQ D n := ⟨lam, fun i j => congrFun (congrFun hh i) j⟩
      let l : ratHerm D n := ⟨⟨lam.map (incA D), adj_map_herm b⟩, ⟨lam, rfl⟩⟩
      have hbl : (β l).1 = lam := Matrix.map_injective incA_injective (hβ l)
      refine ⟨l, ?_⟩
      have hmk := (GlobalTheory.CompanionTheory.EisCellsAsm.mk_eq_iff_siegel GlobalTheory.CompanionTheory.RatPtsUnn.ratPtsUnn (c l) (Quotient.out q)
        (cellM_det _) (hc l) (mat_ratOf _)).2 (by rw [hbl]; exact hS)
      exact hmk.trans (Quotient.out_eq q)
    · rintro ⟨l, rfl⟩
      have hmk : mk ((P D n).subgroupOf (GF D n)) (c l) =
          mk ((P D n).subgroupOf (GF D n)) (Quotient.out (mk ((P D n).subgroupOf (GF D n)) (c l))) :=
        (Quotient.out_eq _).symm
      exact lower_unit hspec.1 _ ((GlobalTheory.CompanionTheory.EisCellsAsm.mk_eq_iff_siegel GlobalTheory.CompanionTheory.RatPtsUnn.ratPtsUnn (c l) _
        (cellM_det _) (hc l) (mat_ratOf _)).1 hmk)
  · intro f hf l y
    exact term_mk hf y (c l)

end GlobalTheory.CompanionTheory.SwUnf.BigCell
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ContinuousSmulH
section
noncomputable section
open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC

namespace GlobalTheory.CompanionTheory.HermSc

section Abstract

variable {M : Type} [AddCommGroup M] [TopologicalSpace M]

theorem sub_mem_ker (S : AddSubgroup M) (P : M →+ M) (hPm : ∀ x, P x ∈ S) (hPs : ∀ s ∈ S, P s = s) (x : M) :
    x - P x ∈ P.ker := by
  rw [AddMonoidHom.mem_ker, map_sub, hPs _ (hPm x), sub_self]

def imKer [IsTopologicalAddGroup M] (S : AddSubgroup M) (P : M →+ M) (hPc : Continuous P) (hPm : ∀ x, P x ∈ S)
    (hPs : ∀ s ∈ S, P s = s) : (S × P.ker) ≃ₜ+ M where
  toFun p := p.1.1 + p.2.1
  invFun x := (⟨P x, hPm x⟩, ⟨x - P x, sub_mem_ker S P hPm hPs x⟩)
  left_inv p := by
    have h2 : P p.2.1 = 0 := p.2.2
    refine Prod.ext (Subtype.ext ?_) (Subtype.ext ?_)
    · change P (p.1.1 + p.2.1) = p.1.1
      rw [map_add (f := _), hPs _ p.1.2, h2, add_zero]
    · change (p.1.1 + p.2.1) - P (p.1.1 + p.2.1) = p.2.1
      rw [map_add (f := _), hPs _ p.1.2, h2, add_zero, add_sub_cancel_left]
  right_inv x := by
    change P x + (x - P x) = x
    abel
  map_add' p q := by
    change (p.1.1 + q.1.1) + (p.2.1 + q.2.1) = (p.1.1 + p.2.1) + (q.1.1 + q.2.1)
    abel
  continuous_toFun :=
    (continuous_subtype_val.comp continuous_fst).add (continuous_subtype_val.comp continuous_snd)
  continuous_invFun := (hPc.subtype_mk _).prodMk ((continuous_id.sub hPc).subtype_mk _)

theorem char_restr [IsTopologicalAddGroup M] [LocallyCompactSpace M] [SecondCountableTopology M] [T2Space M]
    [MeasurableSpace M] [BorelSpace M] (S : AddSubgroup M) [LocallyCompactSpace S] (P : M →+ M)
    (hPc : Continuous P) (hPm : ∀ x, P x ∈ S) (hPs : ∀ s ∈ S, P s = s)
    (U : M ≃ₜ+ M) (hU : ∀ s ∈ S, U s ∈ S) (hU' : ∀ s ∈ S, U.symm s ∈ S) (hfix : ∀ x, P x = 0 → U x = x) :
    addEquivAddHaarChar (GlobalTheory.CompanionTheory.CgMod.restr S U hU hU') = addEquivAddHaarChar U := by
  haveI : SecondCountableTopology S := Topology.IsInducing.subtypeVal.secondCountableTopology
  haveI : T2Space S := Topology.IsEmbedding.subtypeVal.t2Space
  haveI : SecondCountableTopology P.ker := Topology.IsInducing.subtypeVal.secondCountableTopology
  haveI : T2Space P.ker := Topology.IsEmbedding.subtypeVal.t2Space
  have hcl : IsClosed (P.ker : Set M) := by
    have : (P.ker : Set M) = P ⁻¹' {0} := by
      ext x; simp [AddMonoidHom.mem_ker]
    rw [this]
    exact isClosed_singleton.preimage hPc
  haveI : LocallyCompactSpace P.ker := hcl.isClosedEmbedding_subtypeVal.locallyCompactSpace
  set Ψ := imKer S P hPc hPm hPs with hΨ
  set T := GlobalTheory.CompanionTheory.CgMod.restr S U hU hU' with hT
  have e : ((Ψ.symm.trans (GlobalTheory.ModuLR.prodCE T (ContinuousAddEquiv.refl P.ker))).trans Ψ) = U := by
    ext x
    obtain ⟨p, rfl⟩ := Ψ.surjective x
    change Ψ (GlobalTheory.ModuLR.prodCE T (ContinuousAddEquiv.refl P.ker) (Ψ.symm (Ψ p))) = U (Ψ p)
    have hl : Ψ.symm (Ψ p) = p := Ψ.left_inv p
    rw [hl]
    change U p.1.1 + p.2.1 = U (p.1.1 + p.2.1)
    rw [map_add (f := _), hfix _ p.2.2]
  rw [← e, GlobalTheory.ModuLR.addEquivAddHaarChar_transport Ψ, _root_.GlobalTheory.ModuLR.addEquivAddHaarChar_prodCE, addEquivAddHaarChar_refl, mul_one]

end Abstract

section Main

open GlobalTheory.CompanionTheory.IwaAd GlobalTheory.CompanionTheory.HermVol GlobalTheory.CompanionTheory.CgMod PositivityTheory.Rg.Rsw.L PositivityTheory.Rg.Rsw.Em

variable {D : D7} {n : ℕ}


set_option synthInstance.maxHeartbeats 400000 in
set_option maxHeartbeats 1000000 in
theorem char_herm [BorelSpace (Mx D n n)] [LocallyCompactSpace (hermA D n)] (a : GL (Fin n) (AE D)) :
    addEquivAddHaarChar (restr (hermA D n) (GlobalTheory.ModuLR.lrCE a (ad a)⁻¹) (lr_herm a) (lr_herm_symm a)) =
      absA D (Matrix.GeneralLinearGroup.det a : (AE D)ˣ) ^ n := by
  obtain ⟨i1, i2, i3, i4, -, -⟩ := lattice_Mx D n n
  haveI : IsTopologicalAddGroup (Mx D n n) := i1
  haveI : LocallyCompactSpace (Mx D n n) := i2
  haveI : SecondCountableTopology (Mx D n n) := i3
  haveI : T2Space (Mx D n n) := i4
  haveI : SecondCountableTopology (hermA D n) := Topology.IsInducing.subtypeVal.secondCountableTopology
  haveI : T2Space (hermA D n) := Topology.IsEmbedding.subtypeVal.t2Space
  obtain ⟨d, e, hde, hd, he⟩ := exists_anti_units D
  have hsq := char_sq (hermA D n) (hermPartHom D n) continuous_hermPart hermPart_mem
    (fun s hs => hermPart_of_mem hs) (mulCE d e hde)
    (fun s hs => hermPart_anti hd hs) (fun s hs => hermPart_anti he hs)
    (fun x => hermPart_split he hde x) (GlobalTheory.ModuLR.lrCE a (ad a)⁻¹)
    (lr_smul a d e hde) (lr_herm a) (lr_herm_symm a)
  have hlr : addEquivAddHaarChar (GlobalTheory.ModuLR.lrCE a (ad a)⁻¹) =
      absA D (Matrix.GeneralLinearGroup.det a : (AE D)ˣ) ^ n * absA D (Matrix.GeneralLinearGroup.det a : (AE D)ˣ) ^ n := by
    have h := GlobalTheory.ResidueEisenstein.ModMat.addEquivAddHaarChar_lrCE _ _ D.sp.cm.sig (isCMExt_host D) n n a (ad a)⁻¹
    rw [h]
    exact congrArg (fun t => absA D (Matrix.GeneralLinearGroup.det a : (AE D)ˣ) ^ n * t ^ n) (absA_det_ad_inv a)
  exact (pow_left_inj₀ zero_le zero_le two_ne_zero).1 ((hsq.trans hlr).trans (sq _).symm)

theorem smul_herm {e : AE D} (hc : cA D e = e) (x : hermA D n) : e • x.1 ∈ hermA D n := by
  change adj (e • x.1) = e • x.1
  have h : adj x.1 = x.1 := x.2
  rw [adj_smul, h, hc]

def smulH (e : AE D) (hc : cA D e = e) : hermA D n →+ hermA D n where
  toFun x := ⟨e • x.1, smul_herm hc x⟩
  map_zero' := Subtype.ext (smul_zero e)
  map_add' x y := Subtype.ext (smul_add e x.1 y.1)

set_option synthInstance.maxHeartbeats 400000 in
theorem continuous_smulH (e : AE D) (hc : cA D e = e) : Continuous (smulH (n := n) e hc) :=
  ((continuous_const_smul e).comp continuous_subtype_val).subtype_mk _

theorem smul_sandwich (e : AE D) (A B x : Mx D n n) (h : e • x = x) : e • (A * x * B) = A * x * B := by
  rw [← Matrix.smul_mul, ← Matrix.mul_smul, h]

theorem mul_fix {e : AE D} (g : GL (Fin n) (AE D)) (hg : e • (g.1 - 1) = g.1 - 1) (x : Mx D n n) (hx : e • x = 0) :
    g.1 * x = x := by
  have h : (g.1 - 1) * x = 0 := by
    rw [← hg, Matrix.smul_mul, ← Matrix.mul_smul, hx, Matrix.mul_zero]
  rw [Matrix.sub_mul, Matrix.one_mul, sub_eq_zero] at h
  exact h

theorem sandwich_fix {e : AE D} (g : GL (Fin n) (AE D)) (hg : e • (g.1 - 1) = g.1 - 1) (x : hermA D n)
    (hx : e • x.1 = 0) : g.1 * x.1 * adj g.1 = x.1 := by
  have h1 := mul_fix g hg x.1 hx
  have h2 : adj x.1 = x.1 := x.2
  have h3 : x.1 * adj g.1 = x.1 := by
    have := congrArg adj h1
    rwa [adj_mul, h2] at this
  rw [h1, h3]

end Main

end GlobalTheory.CompanionTheory.HermSc
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExponentToSaturation
section
noncomputable section

open NumberField IsDedekindDomain Matrix
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil ValuativeRel GlobalTheory.CuspRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC GlobalTheory.IndefiniteRowSideFullHecke.IwahoriDoubleCosets

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.CompanionTheory.ExpProd

theorem val_unifU (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] :
    valuation k ((Zls.unifU k : kˣ) : k) = uniformizer k := by
  apply le_antisymm
  · rw [le_uniformizer_iff]
    exact GlobalTheory.CompanionTheory.UnifPow.valuation_unifU_lt_one k
  · obtain ⟨y, hy⟩ := valuation_surjective (uniformizer k)
    have hy1 : valuation k y < 1 := hy ▸ uniformizer_lt_one
    have hyO : y ∈ 𝒪[k] := hy1.le
    have hm : (⟨y, hyO⟩ : 𝒪[k]) ∈ IsLocalRing.maximalIdeal 𝒪[k] := by
      rw [IsLocalRing.mem_maximalIdeal]
      intro hu
      exact hy1.ne (((Valuation.integer.integers (valuation k)).isUnit_iff_valuation_eq_one).1 hu)
    rw [(Zls.irreducible_unif (k := k)).maximalIdeal_eq, Ideal.mem_span_singleton] at hm
    rw [← hy]
    exact (Valuation.Integers.le_iff_dvd (Valuation.integer.integers (valuation k))).2 hm

theorem atUnif_unrChar (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    {n : ℕ} (ξ : Fin n → ℂˣ) : PositivityTheory.SphericalProduct.atUnif k (fun i => unrChar k (ξ i)) = ξ :=
  funext fun i => unrChar_uniformizer k (ξ i) (val_unifU k)

theorem expToSat : PositivityTheory.Rg.BcB.F.Tail.PExp.ExpToSat := by
  intro E _ _ w c n N h σ P ξ hsub hmono ⟨y, hy0, hy⟩
  haveI : CharZero (w.adicCompletion E) := charZero_of_injective_algebraMap (algebraMap E _).injective
  have hd : ∑ _a : Fin n, 1 = n := by simp
  obtain ⟨v, hv0, hv⟩ := GlobalTheory.CompanionTheory.StandardBlocks.stdBridge (w.adicCompletion E) n hd P.V P.ρ _ y hy0 hy
  have hadm : IsAdmissible P.ρ :=
    (GlobalTheory.CompanionTheory.Published.bernsteinZelevinskyFiniteness (w.adicCompletion E)).1 _ P.V P.ρ P.smooth P.irred
  have hanti : PositivityTheory.SphericalProduct.AbsAnti (PositivityTheory.SphericalProduct.atUnif (w.adicCompletion E)
      (fun i => unrChar (w.adicCompletion E) (ξ i))) := by
    rw [atUnif_unrChar]
    exact fun i j hij => hmono i j hij
  have hsat := GlobalTheory.CompanionTheory.LocGL.expSat (w.adicCompletion E) n hd P.V P.ρ P.smooth hadm P.irred
    (fun i => unrChar (w.adicCompletion E) (ξ i)) (fun i => isUnram_unrChar _ _) hanti ⟨v, hv0, hv⟩
  rw [atUnif_unrChar] at hsat
  have hG := (GlobalTheory.CompanionTheory.SatakeBridge.satBridge E w n P.V P.ρ P.smooth P.irred ξ).1 hsat
  obtain ⟨x, hx⟩ := hG.exists_vec
  obtain ⟨S, f, hf⟩ := hsub
  have hsm : IsSmooth (locProd h w σ) := GlobalTheory.SmGL.isSmooth_parInd _ _
  have hSs : IsSmooth S.toRepresentation := GlobalTheory.CompanionTheory.JacExp.isSmooth_sub hsm S
  have hc := GlobalTheory.SatInd.isCompact_KGL (w := w) (n := n)
  obtain ⟨s, rfl⟩ := hf x
  obtain ⟨u, hu, hfu⟩ := GlobalTheory.LocGL.exists_mem_fixed_map_eq hSs hc f hx.2.1
  have hu0 : u ≠ 0 := by
    rintro rfl
    exact hx.1 (by rw [← hfu, map_zero])
  have hfix : u.1 ∈ fixed (locProd h w σ) (GlobalTheory.LFun.KGL w (n := n)) :=
    GlobalTheory.LGrp.mem_fixed.2 fun g hg => congrArg Subtype.val (GlobalTheory.LGrp.mem_fixed.1 hu g hg)
  have hne : u.1 ≠ 0 := fun e => hu0 (Subtype.ext e)
  obtain ⟨B, hB, hBv⟩ := GlobalTheory.SatInd.exists_sat_multiProd h (π := fun i => (σ i).ρ)
    (fun i => (σ i).smooth) (fun i => (σ i).irred) hfix hne
  have h1 : GlobalTheory.LFun.IsSatVecGL w S.toRepresentation u (∑ a, B a) :=
    GlobalTheory.LFun.IsSatVecGL.of_map S.toSubmodule.subtype (fun g y => rfl) Subtype.val_injective hBv
  have h2 := h1.map (ρ' := P.ρ) f.toLinearMap (fun g y => f.isIntertwining _ _ g y) (by
    change f u ≠ 0
    rw [hfu]
    exact hx.1)
  change GlobalTheory.LFun.IsSatVecGL w P.ρ (f u) _ at h2
  rw [hfu] at h2
  exact ⟨fun i => (hB i).1, B, hB, h2.unique hx⟩

end GlobalTheory.CompanionTheory.ExpProd

end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HermitianMeasureConjugationStatement
section
noncomputable section
open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hermitian_measure_conjugation : ∀ (D : D7) (n : ℕ) (lam : Measure (hermA D n)), lam.IsAddHaarMeasure → ∀ (a : GL (Fin n) (AE D)) (f : hermA D n → ℂ), ∫ c, f (GlobalTheory.CompanionTheory.IwaAd.cg a c) ∂lam = npow (absA D (Matrix.GeneralLinearGroup.det a)) (-(n : ℂ)) * ∫ c, f c ∂lam := by
  first | exact @GlobalTheory.CompanionTheory.CgMod.integral_cg | exact GlobalTheory.CompanionTheory.CgMod.integral_cg | (intros; apply GlobalTheory.CompanionTheory.CgMod.integral_cg <;> assumption)
end
end

