module

public import Mathlib
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0703
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.InfinitesimalCharacterLimits.AllLeaves
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0282
public import Development.WeilBound.RepresentationTheoryGL.ResidualSpectrum.ExponentialNegativity.CommonEigenvectors.KillPoly
public import Development.WeilBound.RepresentationTheoryGL.ResidualSpectrum.ExponentialNegativity.DiagonalInfinityValues.InfGLValDiag
public import Development.WeilBound.RepresentationTheoryGL.ResidualSpectrum.ExponentialNegativity.NormalisedExistence.ExistsNormed
public import Development.WeilBound.RepresentationTheoryGL.ResidualSpectrum.SliceTensors.Bundle0007
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0445
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsStableBdSub
public import Development.WeilBound.RepresentationTheoryGL.RegularisedSiegelWeil.ThetaIdempotents.HeckeEta
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0706
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.PartialConstantTermBound
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0658
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.PolarPartIdentity
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0704
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1743
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1766
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0461
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0133
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0130
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0687
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0696
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0692
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0691
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0693
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0697
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.RankPosOfLeaves
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0705

@[expose] public section

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HasDerivAtTorusTranslateStatement
section
open scoped ENNReal
open NumberField IsDedekindDomain Matrix MeasureTheory Filter Topology Polynomial
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC PositivityTheory.Rg.Rs GlobalTheory.CompanionTheory.Conc
open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.AutomorphicForm

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hasDerivAt_torus_translate : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (r s : ℕ) (F : Sm E (r + s)) (g : GA E (r + s)) (t : ℝ),
  HasDerivAt (fun t : ℝ => F.1 (g * aT E (r + s) r t))
    (((∑ τ : E →+* ℂ, ∑ i : Fin r, Eop (a := r + s) τ (Fin.castAdd s i) (Fin.castAdd s i)) F).1 (g * aT E (r + s) r t)) t := by
  first | exact @GlobalTheory.CompanionTheory.Conc.TorusDeriv.hasDerivAt_aT_right | exact GlobalTheory.CompanionTheory.Conc.TorusDeriv.hasDerivAt_aT_right | (intros; apply GlobalTheory.CompanionTheory.Conc.TorusDeriv.hasDerivAt_aT_right <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HeightPowerSummableRationalHermitian
section
open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct Topology
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory Filter
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC PositivityTheory.PfSWUS PositivityTheory.Rg.Rsw
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.CompanionTheory.HermSum

open GlobalTheory.StdUnn.Model (submatrix_fromBlocks_mul block_matrix_one)

theorem mat_mul_block_decomposition {D : D7} {n : ℕ} (g h : G D n) : mat (g * h) = mat g * mat h := rfl

theorem weyl_mul_inv {R : Type} [CommRing R] {k : ℕ} :
    blk4 (0 : Matrix (Fin k) (Fin k) R) 1 (-1) 0 * blk4 0 (-1) 1 0 = 1 := by
  rw [submatrix_fromBlocks_mul]
  simp [block_matrix_one]

theorem weyl_conj {R : Type} [CommRing R] {k : ℕ} (d : Matrix (Fin k) (Fin k) R) :
    blk4 (0 : Matrix (Fin k) (Fin k) R) 1 (-1) 0 * blk4 1 d 0 1 * blk4 0 (-1) 1 0 = blk4 1 0 (-d) 1 := by
  rw [submatrix_fromBlocks_mul, submatrix_fromBlocks_mul]
  simp

private theorem mat_one_eq_one {D : D7} {n : ℕ} : mat (1 : G D n) = 1 := by
  simp only [GlobalTheory.StdUnn.mat, map_one, Units.val_one]

private theorem mat_inv_eq_of_mat_mul_eq_one {D : D7} {n : ℕ} (g : G D n) (M : Mx D (n + n) (n + n))
    (h : mat g * M = 1) : mat g⁻¹ = M := by
  have h1 : mat g⁻¹ * mat g = 1 := by rw [← mat_mul_block_decomposition, inv_mul_cancel, mat_one_eq_one]
  calc mat g⁻¹ = mat g⁻¹ * (mat g * M) := by rw [h, mul_one]
    _ = M := by rw [← mul_assoc, h1, one_mul]

private theorem blk4_apply_inr_inl {R : Type} {k : ℕ} (a b c d : Matrix (Fin k) (Fin k) R) (i j : Fin k) :
    blk4 a b c d (finSumFinEquiv (Sum.inr i)) (finSumFinEquiv (Sum.inl j)) = c i j := by
  show (Matrix.fromBlocks a b c d).submatrix finSumFinEquiv.symm finSumFinEquiv.symm
    (finSumFinEquiv (Sum.inr i)) (finSumFinEquiv (Sum.inl j)) = c i j
  rw [Matrix.submatrix_apply, Equiv.symm_apply_apply, Equiv.symm_apply_apply, Matrix.fromBlocks_apply₂₁]

private theorem mulVec_single_one_apply' {R : Type} [CommRing R] {m : ℕ} (M : Matrix (Fin m) (Fin m) R)
    (i j : Fin m) : (M *ᵥ Pi.single j 1) i = M i j := by
  simp [Matrix.mulVec]

private theorem eq_zero_of_mem_P_of_mat_eq_blk4 {D : D7} {n : ℕ} (x : G D n) (hx : x ∈ P D n)
    (d : Mx D n n) (hd : mat x = blk4 1 0 (-d) 1) : d = 0 := by
  have key : ∀ v : Fin (n + n) → AE D,
      v ∈ GlobalTheory.StdUnn.upperHalf D n ↔ (mat x).mulVec v ∈ GlobalTheory.StdUnn.upperHalf D n := hx
  refine Matrix.ext fun i j => ?_
  have hv : (Pi.single (finSumFinEquiv (Sum.inl j)) 1 : Fin (n + n) → AE D) ∈
      GlobalTheory.StdUnn.upperHalf D n := by
    rw [GlobalTheory.StdUnn.upperHalf, LinearMap.mem_ker]
    ext l
    rw [LinearMap.funLeft_apply, Pi.zero_apply, Pi.single_eq_of_ne]
    exact fun h => Sum.inr_ne_inl (finSumFinEquiv.injective h)
  have h2 := (key _).1 hv
  rw [hd, GlobalTheory.StdUnn.upperHalf, LinearMap.mem_ker] at h2
  have h3 := congrFun h2 i
  rw [LinearMap.funLeft_apply, Pi.zero_apply, mulVec_single_one_apply', blk4_apply_inr_inl, Matrix.neg_apply,
    neg_eq_zero] at h3
  rw [h3, Matrix.zero_apply]

theorem summable_height_rpow : ∀ (D : D7) (ρ : ℕ) (H : G D ρ → ℝ≥0), IsHt H → ∀ (w : G D ρ) (nb : hermA D ρ → G D ρ),
  mat w = blk4 0 1 (-1) 0 → (∀ z : hermA D ρ, mat (nb z) = blk4 1 z.1 0 1) → ∀ τ : ℝ, (ρ : ℝ) < τ →
    Summable (fun ζ : ratHerm D ρ => (H (w * nb ζ.1) : ℝ) ^ τ) := by
  intro D ρ H hH w nb hw hnb τ hτ
  have hτ0 : 0 ≤ τ := le_trans (Nat.cast_nonneg ρ) hτ.le
  set Φ : G D ρ → ℂ := fun g => (((H g : ℝ) ^ τ : ℝ) : ℂ) with hΦ
  set s₁ : ℂ := ((τ - (ρ : ℝ) / 2 : ℝ) : ℂ) with hs₁
  have hlaw : PositivityTheory.Rg.Rsw.IsLaw 1 s₁ Φ := by
    intro q hq a ha g
    have e1 := hH.2.2 q hq a ha g
    have e2 : s₁ + (ρ : ℂ) / 2 = (τ : ℂ) := by
      rw [hs₁]
      push_cast
      ring
    rw [e2]
    simp only [hΦ, e1, MonoidHom.one_apply, OneMemClass.coe_one, NNReal.coe_mul, GlobalTheory.Doubling.npow]
    rw [Real.mul_rpow (NNReal.coe_nonneg _) (NNReal.coe_nonneg _), Complex.ofReal_mul,
      ← Complex.ofReal_cpow (NNReal.coe_nonneg _)]
    simp
  have hcont : Continuous Φ := by
    have hH' : Continuous fun g => (H g : ℝ) := NNReal.continuous_coe.comp hH.1
    exact Complex.continuous_ofReal.comp (hH'.rpow_const fun _ => Or.inr hτ0)
  have hre : (ρ : ℝ) / 2 < s₁.re := by
    rw [hs₁, Complex.ofReal_re]
    linarith
  have hconv := GlobalTheory.CompanionTheory.Godement.cosetConv_of_continuous_law D ρ 1 s₁ Φ hcont hlaw hre 1
  have hHecke : Formalism.L2.Theta.IsHeckeChar D 1 :=
    ⟨by
      have h1 : (⇑(1 : (AE D)ˣ →* Circle)) = fun _ => 1 := funext fun _ => MonoidHom.one_apply _
      rw [h1]
      exact continuous_const, fun _ => MonoidHom.one_apply _⟩
  have hinv := GlobalTheory.CompanionTheory.FJE.leftInv_of_isLaw (1 : (AE D)ˣ →* Circle) s₁ Φ hHecke hlaw
  have hWr : mat w = GlobalTheory.MixModel.rat (blk4 (0 : Matrix (Fin ρ) (Fin ρ) D.host.E) 1 (-1) 0) := by
    rw [hw, GlobalTheory.CompanionTheory.PcB.rational_map_block_matrix, GlobalTheory.CompanionTheory.PcB.rat_zero', GlobalTheory.CompanionTheory.PcB.rat_one', GlobalTheory.CompanionTheory.PcB.rat_neg',
      GlobalTheory.CompanionTheory.PcB.rat_one']
  have hwinv : mat w⁻¹ = blk4 0 (-1) 1 0 := by
    apply mat_inv_eq_of_mat_mul_eq_one
    rw [hw]
    exact weyl_mul_inv
  have hWr' : mat w⁻¹ = GlobalTheory.MixModel.rat (blk4 (0 : Matrix (Fin ρ) (Fin ρ) D.host.E) (-1) 1 0) := by
    rw [hwinv, GlobalTheory.CompanionTheory.PcB.rational_map_block_matrix, GlobalTheory.CompanionTheory.PcB.rat_zero', GlobalTheory.CompanionTheory.PcB.rat_neg', GlobalTheory.CompanionTheory.PcB.rat_one']
  have hwmem : w ∈ GF D ρ := GlobalTheory.CompanionTheory.PcB.mem_GF w _ _ hWr hWr'
  have hrat : ∀ ζ : ratHerm D ρ, ∃ Z : Matrix (Fin ρ) (Fin ρ) D.host.E,
      GlobalTheory.MixModel.rat Z = ((ζ.1 : hermA D ρ) : Mx D ρ ρ) := by
    intro ζ
    obtain ⟨Z, hZ⟩ := AddMonoidHom.mem_range.mp (AddSubgroup.mem_comap.mp ζ.2)
    exact ⟨Z, hZ⟩
  have hnbinv : ∀ ζ : ratHerm D ρ, mat (nb ζ.1)⁻¹ = blk4 1 (-((ζ.1 : hermA D ρ) : Mx D ρ ρ)) 0 1 := by
    intro ζ
    apply mat_inv_eq_of_mat_mul_eq_one
    rw [hnb, GlobalTheory.CompanionTheory.PcB.block_unipotent_mul, add_neg_cancel, block_matrix_one]
  have hnbmem : ∀ ζ : ratHerm D ρ, nb ζ.1 ∈ GF D ρ := by
    intro ζ
    obtain ⟨Z, hZ⟩ := hrat ζ
    refine GlobalTheory.CompanionTheory.PcB.mem_GF _ (blk4 1 Z 0 1) (blk4 1 (-Z) 0 1) ?_ ?_
    · rw [hnb, ← hZ, GlobalTheory.CompanionTheory.PcB.rational_map_block_matrix, GlobalTheory.CompanionTheory.PcB.rat_one', GlobalTheory.CompanionTheory.PcB.rat_zero']
    · rw [hnbinv, ← hZ, GlobalTheory.CompanionTheory.PcB.rational_map_block_matrix, GlobalTheory.CompanionTheory.PcB.rat_one', GlobalTheory.CompanionTheory.PcB.rat_zero',
        GlobalTheory.CompanionTheory.PcB.rat_neg']
  set x : ratHerm D ρ → GF D ρ := fun ζ => ⟨w * nb ζ.1, mul_mem hwmem (hnbmem ζ)⟩ with hx
  set ι : ratHerm D ρ → GlobalTheory.Eis.Cosets (P D ρ) (GF D ρ) :=
    fun ζ => Quotient.mk (QuotientGroup.rightRel ((P D ρ).subgroupOf (GF D ρ))) (x ζ) with hι
  have hinj : Function.Injective ι := by
    intro ζ ζ' h
    have h0 : Quotient.mk (QuotientGroup.rightRel ((P D ρ).subgroupOf (GF D ρ))) (x ζ) =
        Quotient.mk (QuotientGroup.rightRel ((P D ρ).subgroupOf (GF D ρ))) (x ζ') := h
    have h1 : x ζ' * (x ζ)⁻¹ ∈ (P D ρ).subgroupOf (GF D ρ) :=
      QuotientGroup.rightRel_apply.mp (Quotient.exact h0)
    have h2 : (w * nb ζ'.1) * (w * nb ζ.1)⁻¹ ∈ P D ρ := Subgroup.mem_subgroupOf.mp h1
    have hm : mat ((w * nb ζ'.1) * (w * nb ζ.1)⁻¹) =
        blk4 1 0 (-(((ζ'.1 : hermA D ρ) : Mx D ρ ρ) + -((ζ.1 : hermA D ρ) : Mx D ρ ρ))) 1 := by
      rw [mul_inv_rev, mat_mul_block_decomposition, mat_mul_block_decomposition, mat_mul_block_decomposition, hw, hnb, hwinv, hnbinv ζ, ← mul_assoc,
        mul_assoc (blk4 0 1 (-1) 0), GlobalTheory.CompanionTheory.PcB.block_unipotent_mul]
      exact weyl_conj _
    have h3 := eq_zero_of_mem_P_of_mat_eq_blk4 _ h2 _ hm
    exact Subtype.ext (Subtype.ext (add_neg_eq_zero.mp h3).symm)
  have hterm : ∀ ζ : ratHerm D ρ,
      ‖GlobalTheory.Eis.term (P D ρ) (GF D ρ) Φ 1 (ι ζ)‖ = (H (w * nb ζ.1) : ℝ) ^ τ := by
    intro ζ
    have ho : Quotient.mk (QuotientGroup.rightRel ((P D ρ).subgroupOf (GF D ρ))) (Quotient.out (ι ζ)) =
        Quotient.mk (QuotientGroup.rightRel ((P D ρ).subgroupOf (GF D ρ))) (x ζ) := Quotient.out_eq (ι ζ)
    have hrel : x ζ * (Quotient.out (ι ζ))⁻¹ ∈ (P D ρ).subgroupOf (GF D ρ) :=
      QuotientGroup.rightRel_apply.mp (Quotient.exact ho)
    have hγ : Quotient.out (ι ζ) * (x ζ)⁻¹ ∈ (P D ρ).subgroupOf (GF D ρ) := by
      have h4 := inv_mem hrel
      rwa [mul_inv_rev, inv_inv] at h4
    have hγP : ((Quotient.out (ι ζ) * (x ζ)⁻¹ : GF D ρ) : G D ρ) ∈ P D ρ ⊓ GF D ρ :=
      Subgroup.mem_inf.mpr ⟨Subgroup.mem_subgroupOf.mp hγ, (Quotient.out (ι ζ) * (x ζ)⁻¹).2⟩
    have hsplit : ((Quotient.out (ι ζ) : GF D ρ) : G D ρ) * 1 =
        ((Quotient.out (ι ζ) * (x ζ)⁻¹ : GF D ρ) : G D ρ) * ((x ζ : GF D ρ) : G D ρ) := by
      rw [mul_one, ← Subgroup.coe_mul, inv_mul_cancel_right]
    show ‖Φ (((Quotient.out (ι ζ) : GF D ρ) : G D ρ) * 1)‖ = _
    rw [hsplit, hinv _ hγP]
    show ‖(((H (w * nb ζ.1) : ℝ) ^ τ : ℝ) : ℂ)‖ = (H (w * nb ζ.1) : ℝ) ^ τ
    rw [Complex.norm_real, Real.norm_of_nonneg (Real.rpow_nonneg (NNReal.coe_nonneg _) _)]
  have hsum : Summable (fun q => ‖GlobalTheory.Eis.term (P D ρ) (GF D ρ) Φ 1 q‖) := hconv
  exact (hsum.comp_injective hinj).congr hterm

end GlobalTheory.CompanionTheory.HermSum

end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HermitianMeasureConjugation
section
noncomputable section
open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC

namespace GlobalTheory.CompanionTheory.CgMod

section Abstract

variable {M : Type} [AddCommGroup M] [TopologicalSpace M]

def restr (S : AddSubgroup M) (U : M ≃ₜ+ M) (hU : ∀ s ∈ S, U s ∈ S) (hU' : ∀ s ∈ S, U.symm s ∈ S) : S ≃ₜ+ S where
  toFun s := ⟨U s.1, hU _ s.2⟩
  invFun s := ⟨U.symm s.1, hU' _ s.2⟩
  left_inv s := Subtype.ext (U.left_inv s.1)
  right_inv s := Subtype.ext (U.right_inv s.1)
  map_add' x y := Subtype.ext (map_add U x.1 y.1)
  continuous_toFun := (U.continuous.comp continuous_subtype_val).subtype_mk _
  continuous_invFun := (U.symm.continuous.comp continuous_subtype_val).subtype_mk _

def dbl [IsTopologicalAddGroup M] (S : AddSubgroup M) (P : M →+ M) (hPc : Continuous P) (hPm : ∀ x, P x ∈ S)
    (hPs : ∀ s ∈ S, P s = s) (L : M ≃ₜ+ M) (h1 : ∀ s ∈ S, P (L s) = 0) (h2 : ∀ s ∈ S, P (L.symm s) = 0)
    (h3 : ∀ x, P x + L (P (L.symm x)) = x) : (S × S) ≃ₜ+ M where
  toFun p := p.1.1 + L p.2.1
  invFun x := (⟨P x, hPm x⟩, ⟨P (L.symm x), hPm _⟩)
  left_inv p := by
    refine Prod.ext (Subtype.ext ?_) (Subtype.ext ?_)
    · change P (p.1.1 + L p.2.1) = p.1.1
      rw [map_add (f := _), hPs _ p.1.2, h1 _ p.2.2, add_zero]
    · change P (L.symm (p.1.1 + L p.2.1)) = p.2.1
      have hl : L.symm (L p.2.1) = p.2.1 := L.left_inv _
      rw [map_add (f := _), map_add (f := _), h2 _ p.1.2, zero_add, hl, hPs _ p.2.2]
  right_inv x := h3 x
  map_add' p q := by
    change (p.1.1 + q.1.1) + L (p.2.1 + q.2.1) = (p.1.1 + L p.2.1) + (q.1.1 + L q.2.1)
    rw [map_add (f := _)]; abel
  continuous_toFun :=
    (continuous_subtype_val.comp continuous_fst).add (L.continuous.comp (continuous_subtype_val.comp continuous_snd))
  continuous_invFun := (hPc.subtype_mk _).prodMk ((hPc.comp L.symm.continuous).subtype_mk _)

theorem char_sq [IsTopologicalAddGroup M] [LocallyCompactSpace M] [SecondCountableTopology M] [T2Space M]
    [MeasurableSpace M] [BorelSpace M] (S : AddSubgroup M) [LocallyCompactSpace S] (P : M →+ M)
    (hPc : Continuous P) (hPm : ∀ x, P x ∈ S) (hPs : ∀ s ∈ S, P s = s) (L : M ≃ₜ+ M)
    (h1 : ∀ s ∈ S, P (L s) = 0) (h2 : ∀ s ∈ S, P (L.symm s) = 0) (h3 : ∀ x, P x + L (P (L.symm x)) = x)
    (U : M ≃ₜ+ M) (hUL : ∀ x, U (L x) = L (U x)) (hU : ∀ s ∈ S, U s ∈ S) (hU' : ∀ s ∈ S, U.symm s ∈ S) :
    addEquivAddHaarChar (restr S U hU hU') ^ 2 = addEquivAddHaarChar U := by
  haveI : SecondCountableTopology S := Topology.IsInducing.subtypeVal.secondCountableTopology
  haveI : T2Space S := Topology.IsEmbedding.subtypeVal.t2Space
  set Ψ := dbl S P hPc hPm hPs L h1 h2 h3 with hΨ
  set T := restr S U hU hU' with hT
  have e : ((Ψ.symm.trans (GlobalTheory.ModuLR.prodCE T T)).trans Ψ) = U := by
    ext x
    obtain ⟨p, rfl⟩ := Ψ.surjective x
    change Ψ (GlobalTheory.ModuLR.prodCE T T (Ψ.symm (Ψ p))) = U (Ψ p)
    have hl : Ψ.symm (Ψ p) = p := Ψ.left_inv p
    rw [hl]
    change U p.1.1 + L (U p.2.1) = U (p.1.1 + L p.2.1)
    rw [map_add (f := _), hUL]
  rw [sq, ← _root_.GlobalTheory.ModuLR.addEquivAddHaarChar_prodCE, ← GlobalTheory.ModuLR.addEquivAddHaarChar_transport Ψ (GlobalTheory.ModuLR.prodCE T T), e]

end Abstract

theorem exists_anti {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (h : IsCMExt F E σ) : ∃ δ : E, δ ≠ 0 ∧ σ δ = -δ := by
  obtain ⟨-, hc, -, hs⟩ := h
  obtain ⟨v⟩ : Nonempty (NumberField.InfinitePlace E) := inferInstance
  have hv : v.IsComplex := hc.isComplex v
  have hsq : ∀ x, σ (σ x) = x := fun x => v.embedding.injective (by rw [hs, hs]; simp)
  have hx : ∃ x, σ x ≠ x := by
    by_contra hn
    push_neg at hn
    apply NumberField.InfinitePlace.not_isReal_iff_isComplex.2 hv
    rw [NumberField.InfinitePlace.isReal_iff, NumberField.ComplexEmbedding.isReal_iff]
    ext x
    have := hs v.embedding x
    rw [hn] at this
    simpa [NumberField.ComplexEmbedding.conjugate_coe_eq] using this.symm
  obtain ⟨x, hx⟩ := hx
  exact ⟨x - σ x, sub_ne_zero.2 (Ne.symm hx), by rw [map_sub, hsq]; abel⟩

open GlobalTheory.CompanionTheory.IwaAd GlobalTheory.CompanionTheory.HermVol

variable {D : D7} {n : ℕ}

theorem cA_incA (D : D7) (x : D.host.E) : cA D (incA D x) = incA D (D.sp.cm.sig x) := by
  simp [cA, sigR, incA, inclR]

theorem hermPart_anti {c : AE D} (hc : cA D c = -c) {s : Mx D n n} (hs : s ∈ hermA D n) :
    hermPart D n (c • s) = 0 := by
  have h : adj s = s := hs
  rw [hermPart, adj_smul, h, hc, neg_smul, add_neg_cancel, smul_zero]

theorem hermPart_split {d e : AE D} (he : cA D e = -e) (hde : d * e = 1) (x : Mx D n n) :
    hermPart D n x + d • hermPart D n (e • x) = x := by
  have h : d * half D * e = half D := by rw [mul_comm d, mul_assoc, hde, mul_one]
  rw [hermPart, hermPart, adj_smul, he, neg_smul, ← sub_eq_add_neg, ← smul_sub, smul_smul, smul_smul, h, smul_add,
    smul_sub]
  exact (add_add_sub_cancel _ _ _).trans (half_smul_add x)


set_option synthInstance.maxHeartbeats 400000 in
def mulCE (d e : AE D) (hde : d * e = 1) : Mx D n n ≃ₜ+ Mx D n n where
  toFun x := d • x
  invFun x := e • x
  left_inv x := by
    change e • d • x = x
    rw [smul_smul, mul_comm, hde, one_smul]
  right_inv x := by
    change d • e • x = x
    rw [smul_smul, hde, one_smul]
  map_add' := smul_add d
  continuous_toFun := continuous_const_smul d
  continuous_invFun := continuous_const_smul e

def hermPartHom (D : D7) (n : ℕ) : Mx D n n →+ Mx D n n := AddMonoidHom.mk' (hermPart D n) hermPart_add

set_option maxHeartbeats 400000 in
theorem val_det_ad_inv (a : GL (Fin n) (AE D)) :
    ((Matrix.GeneralLinearGroup.det ((ad a)⁻¹ : GL (Fin n) (AE D)) : (AE D)ˣ) : AE D) = cA D (Matrix.GeneralLinearGroup.det a : (AE D)ˣ) := by
  change (adj a.1 : Mx D n n).det = cA D a.1.det
  rw [adj, Matrix.det_transpose, RingHom.map_det]
  rfl

theorem absA_det_ad_inv (a : GL (Fin n) (AE D)) :
    absA D (Matrix.GeneralLinearGroup.det ((ad a)⁻¹ : GL (Fin n) (AE D)) : (AE D)ˣ) =
      absA D (Matrix.GeneralLinearGroup.det a : (AE D)ˣ) := by
  have h : (Matrix.GeneralLinearGroup.det ((ad a)⁻¹ : GL (Fin n) (AE D)) : (AE D)ˣ) =
      conjUnit D.sp.cm.sig (Matrix.GeneralLinearGroup.det a : (AE D)ˣ) := Units.ext (val_det_ad_inv a)
  rw [h]
  exact GlobalTheory.DiagThetaRule.absA_conj D _

theorem exists_anti_units (D : D7) : ∃ d e : AE D, d * e = 1 ∧ cA D d = -d ∧ cA D e = -e := by
  obtain ⟨δ, hδ, hσ⟩ := exists_anti _ (isCMExt_host D)
  refine ⟨incA D δ, incA D δ⁻¹, ?_, ?_, ?_⟩
  · rw [← map_mul, mul_inv_cancel₀ hδ, map_one]
  · rw [cA_incA, hσ, map_neg]
  · rw [cA_incA, map_inv₀, hσ, inv_neg, map_neg]

theorem lr_herm (a : GL (Fin n) (AE D)) : ∀ s ∈ hermA D n, GlobalTheory.ModuLR.lrCE a (ad a)⁻¹ s ∈ hermA D n :=
  fun s hs => (cg a ⟨s, hs⟩).2

theorem lr_herm_symm (a : GL (Fin n) (AE D)) :
    ∀ s ∈ hermA D n, (GlobalTheory.ModuLR.lrCE a (ad a)⁻¹).symm s ∈ hermA D n :=
  fun s hs => (cg a⁻¹ ⟨s, hs⟩).2

theorem lr_smul (a : GL (Fin n) (AE D)) (d e : AE D) (hde : d * e = 1) (x : Mx D n n) :
    GlobalTheory.ModuLR.lrCE a (ad a)⁻¹ (mulCE d e hde x) = mulCE d e hde (GlobalTheory.ModuLR.lrCE a (ad a)⁻¹ x) := by
  change a.1 * (d • x) * ((ad a)⁻¹ : GL (Fin n) (AE D)).1 = d • (a.1 * x * ((ad a)⁻¹ : GL (Fin n) (AE D)).1)
  rw [Matrix.mul_smul, Matrix.smul_mul]

set_option synthInstance.maxHeartbeats 400000 in
set_option maxHeartbeats 1000000 in
theorem integral_cg : ∀ (D : D7) (n : ℕ) (lam : Measure (hermA D n)), lam.IsAddHaarMeasure → ∀ (a : GL (Fin n) (AE D)) (f : hermA D n → ℂ), ∫ c, f (GlobalTheory.CompanionTheory.IwaAd.cg a c) ∂lam = npow (absA D (Matrix.GeneralLinearGroup.det a)) (-(n : ℂ)) * ∫ c, f c ∂lam := by
  intro D n lam hlam a f
  obtain ⟨i1, i2, i3, i4, -, -⟩ := lattice_Mx D n n
  haveI : IsTopologicalAddGroup (Mx D n n) := i1
  haveI : LocallyCompactSpace (Mx D n n) := i2
  haveI : SecondCountableTopology (Mx D n n) := i3
  haveI : T2Space (Mx D n n) := i4
  haveI : BorelSpace (Mx D n n) := ⟨rfl⟩
  haveI : SecondCountableTopology (hermA D n) := Topology.IsInducing.subtypeVal.secondCountableTopology
  haveI : T2Space (hermA D n) := Topology.IsEmbedding.subtypeVal.t2Space
  haveI : LocallyCompactSpace (hermA D n) := (isClosed_hermA (D := D) (r := n)).isClosedEmbedding_subtypeVal.locallyCompactSpace
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
  have hT : addEquivAddHaarChar (restr (hermA D n) _ (lr_herm a) (lr_herm_symm a)) =
      absA D (Matrix.GeneralLinearGroup.det a : (AE D)ˣ) ^ n :=
    (pow_left_inj₀ zero_le zero_le two_ne_zero).1 ((hsq.trans hlr).trans (sq _).symm)
  have h : ∫ c, f (cg a c) ∂lam = _ := integral_comp_char lam (restr (hermA D n) _ (lr_herm a) (lr_herm_symm a)) f
  rw [h, hT, npow_neg_nat (absA_pos _) n]

end GlobalTheory.CompanionTheory.CgMod
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IdeleClassCompactRayDecompositionStatement
section
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology Filter PositivityTheory.Rg.Base1 GroundTheory.Global GlobalTheory.CompanionTheory.SW.RankOneSiegelWeil
open scoped TensorProduct ENNReal NNReal Matrix Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.idele_class_compact_ray_decomposition : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ θ : ℝ →+* Ainf F, Continuous θ → ∀ r, IsRay θ r → ∃ K : Set (AF F ⊗[F] E)ˣ, IsCompact K ∧ ∀ (y : (AF F ⊗[F] E)ˣ) (n : (AF F)ˣ), IsNm σ y n → ∃ (q : Eˣ) (k : (AF F ⊗[F] E)ˣ) (ε : ℝ), k ∈ K ∧ 0 < ε ∧ y = ofE q * (k * ofF (r ε)) ∧ md n = ε ^ (2 * Module.finrank ℚ F) := by
  first | exact @GlobalTheory.CompanionTheory.SW.RankOneSiegelWeil.exists_unit_decomp | exact GlobalTheory.CompanionTheory.SW.RankOneSiegelWeil.exists_unit_decomp | (intros; apply GlobalTheory.CompanionTheory.SW.RankOneSiegelWeil.exists_unit_decomp <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LeviFactorOfUnipotentDecompStatement
section
open NumberField IsDedekindDomain Matrix MeasureTheory Filter Topology
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.SmGL GlobalTheory.DiscSpec GlobalTheory.CompanionTheory.CTFin PositivityTheory.Rg.Rs PositivityTheory.Rg.Rs.InducedTensorMap
open PositivityTheory.Rg.BcB.E PositivityTheory.Rg.BcB.SpectralAccumulation GlobalTheory.CompanionTheory.LimV
open scoped ContDiff
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.levi_factor_of_unipotent_decomp : ∀ {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] {r s : ℕ} (u : BlockIx (r + s) r → Ad E) (m : GA E r × GA E s) (k : Kinf E (r + s)) (c : GL (Fin (r + s)) (Af E)), c ∈ KO E (r + s) → unip u * lev (Ad E) r s m = cf (r + s) k c → ∃ (k₁ : Kinf E r) (c₁ : GL (Fin r) (Af E)) (k₂ : Kinf E s) (c₂ : GL (Fin s) (Af E)), c₁ ∈ KO E r ∧ c₂ ∈ KO E s ∧ m = (cf r k₁ c₁, cf s k₂ c₂) := by
  first | exact @GlobalTheory.CompanionTheory.LimV.LeviCf.levi_cf_integral | exact GlobalTheory.CompanionTheory.LimV.LeviCf.levi_cf_integral | (intros; apply GlobalTheory.CompanionTheory.LimV.LeviCf.levi_cf_integral <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.PairRestriction
section
noncomputable section

open NumberField IsDedekindDomain Matrix MeasureTheory Filter Topology
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.SmGL GlobalTheory.DiscSpec GlobalTheory.CompanionTheory.CTFin PositivityTheory.Rg.Rs
open PositivityTheory.Rg.BcB.E PositivityTheory.Rg.BcB.SpectralAccumulation GlobalTheory.CompanionTheory.LimV

namespace GlobalTheory.CompanionTheory.EGlue.Restrict

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {a b : ℕ}

theorem pairSpace_le_prodSpan (U₁ : Submodule ℂ (Sm E a)) (U₂ : Submodule ℂ (Sm E b)) :
    pairSpace U₁ U₂ ≤ prodSpan (U₁.map (Sm E a).subtype) (U₂.map (Sm E b).subtype) := by
  refine Submodule.span_le.2 ?_
  rintro _ ⟨φ₁, h₁, φ₂, h₂, rfl⟩
  exact Submodule.subset_span ⟨φ₁.1, ⟨φ₁, h₁, rfl⟩, φ₂.1, ⟨φ₂, h₂, rfl⟩, rfl⟩

theorem prodSpan_le_pairSpace (U₁ : Submodule ℂ (Sm E a)) (U₂ : Submodule ℂ (Sm E b)) :
    prodSpan (U₁.map (Sm E a).subtype) (U₂.map (Sm E b).subtype) ≤ pairSpace U₁ U₂ := by
  refine Submodule.span_le.2 ?_
  rintro _ ⟨_, ⟨φ₁, h₁, rfl⟩, _, ⟨φ₂, h₂, rfl⟩, rfl⟩
  exact Submodule.subset_span ⟨φ₁, h₁, φ₂, h₂, rfl⟩

theorem slice_mem (U₁ : Submodule ℂ (Sm E a)) (U₂ : Submodule ℂ (Sm E b)) (F : H E a b → ℂ)
    (hF : F ∈ pairSpace U₁ U₂) (m₁ : GA E a) :
    (fun y => F (m₁, y)) ∈ U₂.map (Sm E b).subtype := by
  induction hF using Submodule.span_induction with
  | mem F h =>
    obtain ⟨φ₁, -, φ₂, h₂, rfl⟩ := h
    exact ⟨φ₁.1 m₁ • φ₂, U₂.smul_mem _ h₂, by funext y; simp⟩
  | zero => exact Submodule.zero_mem _
  | add F F' _ _ h₁ h₂ => exact Submodule.add_mem _ h₁ h₂
  | smul r F _ h => exact Submodule.smul_mem _ r h

end GlobalTheory.CompanionTheory.EGlue.Restrict

namespace GlobalTheory.CompanionTheory.EGlue

theorem pairRestrict_holds : PairRestrict := by
  intro E _ _ _ a b U₁ U₂ U₂' F hF hs
  have hS₂ : ∀ m₁, (fun y => F (m₁, y)) ∈ U₂'.map (Sm E b).subtype := by
    intro m₁
    obtain ⟨φ, -, hφ⟩ := Restrict.slice_mem U₁ U₂ F hF m₁
    exact ⟨φ, hs m₁ φ hφ, hφ⟩
  have h := GlobalTheory.CompanionTheory.LimV.Slices.mem_prodSpan_inf_of_slices (U₁.map (Sm E a).subtype) ⊤
    (U₂.map (Sm E b).subtype) (U₂'.map (Sm E b).subtype) F
    (Restrict.pairSpace_le_prodSpan U₁ U₂ hF) (fun _ => Submodule.mem_top) hS₂
  refine Restrict.prodSpan_le_pairSpace U₁ U₂' ?_
  refine Submodule.span_mono ?_ h
  rintro _ ⟨p, hp, q, hq, rfl⟩
  exact ⟨p, hp.1, q, hq.2, rfl⟩

end GlobalTheory.CompanionTheory.EGlue

end
end

