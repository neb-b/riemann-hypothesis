module

public import Mathlib
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0701
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0697
public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.BaseOneSide.PsiSide
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0689
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0703
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0693
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0698
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0696
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0700
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0706
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0690
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0705
public import Development.WeilBound.RepresentationTheoryGL.RegularisedSiegelWeil.ThetaIdempotents.HeckeEta
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.PartialConstantTermBound
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0704
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.InfinitesimalCharacterLimits.AllLeaves
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0282
public import Development.WeilBound.RepresentationTheoryGL.ResidualSpectrum.ExponentialNegativity.CommonEigenvectors.KillPoly
public import Development.WeilBound.RepresentationTheoryGL.ResidualSpectrum.ExponentialNegativity.DiagonalInfinityValues.InfGLValDiag
public import Development.WeilBound.RepresentationTheoryGL.ResidualSpectrum.ExponentialNegativity.NormalisedExistence.ExistsNormed
public import Development.WeilBound.RepresentationTheoryGL.ResidualSpectrum.SliceTensors.Bundle0007
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0445
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsStableBdSub
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.IwahoriFactorisation.StrictDominance.SatakeSocle.SocleOne
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0496
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0702

@[expose] public section

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CarriesTwistStatement
section
open NumberField IsDedekindDomain Matrix MeasureTheory Filter Topology
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.SmGL GlobalTheory.DiscSpec GlobalTheory.CompanionTheory.CTFin PositivityTheory.Rg.Rs PositivityTheory.Rg.Rs.InducedTensorMap
open PositivityTheory.Rg.BcB.E PositivityTheory.Rg.BcB.SpectralAccumulation GlobalTheory.CompanionTheory.LimV
open scoped ContDiff
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.carries_twist : ∀ {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] {N : ℕ} (e : GA E N → ℂ) (U U' : Submodule ℂ (Sm E N)) (z : ℂ), Carries e U U' → Carries e (tw U z) (tw U' z) := by
  first | exact @GlobalTheory.CompanionTheory.LimV.carries_tw | exact GlobalTheory.CompanionTheory.LimV.carries_tw | (intros; apply GlobalTheory.CompanionTheory.LimV.carries_tw <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CharacterSideEquidistribution
section
noncomputable section

open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology Filter
open GroundTheory.Global PositivityTheory.Rg.Base1
open scoped ENNReal NNReal Classical

namespace GlobalTheory.CompanionTheory.BasePsi

variable {F : Type} [Field F] [NumberField F]

theorem exists_strictHenselian_absolutely_closed_local_ring (a : (AF F)ˣ) (S : Finset (HeightOneSpectrum (𝓞 F))) :
    ∃ T : Finset (HeightOneSpectrum (𝓞 F)), S ⊆ T ∧ ∀ v, v ∉ T → (a : AF F).2 v ∈ v.adicCompletionIntegers F ∧
      ((a⁻¹ : (AF F)ˣ) : AF F).2 v ∈ v.adicCompletionIntegers F := by
  have h1 : ∀ᶠ v in cofinite, (a : AF F).2 v ∈ v.adicCompletionIntegers F := (a : AF F).2.2
  have h2 : ∀ᶠ v in cofinite, ((a⁻¹ : (AF F)ˣ) : AF F).2 v ∈ v.adicCompletionIntegers F :=
    ((a⁻¹ : (AF F)ˣ) : AF F).2.2
  have h3 := h1.and h2
  rw [eventually_cofinite] at h3
  refine ⟨S ∪ h3.toFinset, Finset.subset_union_left, fun v hv => ?_⟩
  by_contra hc
  exact hv (Finset.mem_union_right _ (h3.mem_toFinset.2 hc))

theorem limit (hE : PositivityTheory.Rg.Mass.Equi) (hF : IsTotallyReal F) (θ : ℝ →+* Ainf F) (hθ : Continuous θ) (r : ℝ → (AF F)ˣ)
    (hr : IsRay θ r) (li : Measure (Ainf F)) (lam : ∀ v : HeightOneSpectrum (𝓞 F), Measure (Fv F v)) (hli : IsStdInf li)
    (hlam : ∀ v, IsStdV v (lam v)) (S : Finset (HeightOneSpectrum (𝓞 F))) (G : Ainf F → ℝ)
    (g : ∀ v : HeightOneSpectrum (𝓞 F), Fv F v → ℝ) (hG : Continuous G) (hGc : HasCompactSupport G)
    (hG0 : ∀ y, 0 ≤ G y) (hg0 : ∀ v y, 0 ≤ g v y) (hgS : ∀ v ∈ S, Continuous (g v) ∧ HasCompactSupport (g v))
    (a : (AF F)ˣ) :
    Tendsto (fun δ : ℝ => ENNReal.ofReal (δ ^ Module.finrank ℚ F) * th (PositivityTheory.Rg.Base1.pure S G g fun v => rv v 0) (a * r δ))
      (𝓝[>] 0) (𝓝 (ENNReal.ofReal ((md a)⁻¹ * ((∫ y, G y ∂li) * ∏ v ∈ S, ∫ s, g v s ∂(lam v))))) := by
  obtain ⟨T, hST, hT⟩ := exists_strictHenselian_absolutely_closed_local_ring a S
  have hφ := _root_.GlobalTheory.CompanionTheory.BasePsi.phiA_test F G a hG hGc
  have hψ := _root_.GlobalTheory.CompanionTheory.BasePsi.Test.psiA_isTest F S g a hgS
  have h := hE F hF θ hθ li lam hli hlam Unit T (phiA G a) (fun v => psiA S g a v) hφ.1 hφ.2 (fun v _ => hψ v)
  rw [_root_.GlobalTheory.CompanionTheory.BasePsi.Integrals.integrals_translates F li lam hli hlam S T G g a hST hT] at h
  simp only [Fintype.card_unit, mul_one] at h
  set d := Module.finrank ℚ F with hd
  have hdpos : d ≠ 0 := (Module.finrank_pos (R := ℚ) (M := F)).ne'

  let P : F → Prop := fun x => ∀ v, v ∉ T → algebraMap F (Fv F v) x ∈ v.adicCompletionIntegers F
  let q : ℝ → F → ℝ := fun δ x => phiA G a (fun _ => θ δ * algebraMap F (Ainf F) x) *
    ∏ v ∈ T, psiA S g a v (fun _ => algebraMap F (Fv F v) x)
  have hq0 : ∀ δ x, 0 ≤ q δ x := fun δ x => mul_nonneg (hG0 _) (Finset.prod_nonneg fun v _ => by
    unfold psiA
    split_ifs
    exacts [hg0 _ _, zero_le_one, le_rfl])
  let H : ℝ → F → ℝ := fun δ x => if P x then q δ x else 0
  have hH0 : ∀ δ x, 0 ≤ H δ x := fun δ x => by
    simp only [H]
    split_ifs
    exacts [hq0 δ x, le_rfl]
  have hsum : ∀ δ : ℝ, (∑' x : {x : Unit → F // ∀ v, v ∉ T → ∀ i, algebraMap F (Fv F v) (x i) ∈ v.adicCompletionIntegers F},
      phiA G a (fun i => θ δ * algebraMap F (Ainf F) (x.1 i)) * ∏ v ∈ T, psiA S g a v fun i => algebraMap F (Fv F v) (x.1 i)) =
      ∑' x : F, H δ x := by
    intro δ
    let e : {x : Unit → F // ∀ v, v ∉ T → ∀ i, algebraMap F (Fv F v) (x i) ∈ v.adicCompletionIntegers F} ≃ {x : F // P x} :=
      (Equiv.funUnique Unit F).subtypeEquiv (fun x => by
        simp only [P, Equiv.funUnique_apply]
        exact ⟨fun hx v hv => hx v hv _, fun hx v hv i => by
          have : i = default := Subsingleton.elim _ _
          rw [this]
          exact hx v hv⟩)
    have e1 := e.tsum_eq (fun x : {x : F // P x} => q δ x.1)
    have e2 : (∑' x : F, H δ x) = ∑' x : {x : F // P x}, q δ x.1 := by
      have := tsum_subtype {x : F | P x} (q δ)
      rw [show (∑' x : {x : F // P x}, q δ x.1) = ∑' x : ({x : F | P x} : Set F), q δ x.1 from rfl, this]
      refine tsum_congr fun x => ?_
      simp only [H, Set.indicator, Set.mem_ofPred_eq]
    rw [e2, ← e1]
    refine tsum_congr fun x => ?_
    simp only [q]
    have c1 : (fun i => θ δ * algebraMap F (Ainf F) (x.1 i)) = fun _ => θ δ * algebraMap F (Ainf F) ((e x).1) := by
      funext i
      have : i = default := Subsingleton.elim _ _
      rw [this]
      rfl
    have c2 : ∀ v, (fun i => algebraMap F (Fv F v) (x.1 i)) = fun _ => algebraMap F (Fv F v) ((e x).1) := by
      intro v
      funext i
      have : i = default := Subsingleton.elim _ _
      rw [this]
      rfl
    rw [c1]
    exact congrArg _ (Finset.prod_congr rfl fun v _ => by rw [c2 v])
  have hz : ∀ δ : ℝ, H δ 0 = H 1 0 := fun δ => by
    simp [H, q]
  have hth : ∀ δ : ℝ, 0 < δ → ENNReal.ofReal (∑' x : F, H δ x) =
      ENNReal.ofReal (H 1 0) + th (PositivityTheory.Rg.Base1.pure S G g fun v => rv v 0) (a * r δ) := by
    intro δ hδ
    have hfin : (Function.support (H δ)).Finite := by
      refine (_root_.GlobalTheory.CompanionTheory.BasePsi.finite_contributing F hF θ hθ S T G g a hG hGc hgS hST hT δ hδ).subset fun x hx => ?_
      simp only [Function.mem_support, H] at hx
      by_cases hP : P x
      · rw [ite_eq_left hP] at hx
        exact ⟨hP, hx⟩
      · rw [ite_eq_right hP] at hx
        exact absurd rfl hx
    rw [ENNReal.ofReal_tsum_of_nonneg (hH0 δ) (summable_of_hasFiniteSupport hfin),
      ENNReal.tsum_eq_add_tsum_ite (0 : F), hz δ]
    congr 1
    unfold th
    have e1 := (unitsEquivNeZero (G₀ := F)).tsum_eq (fun x : {x : F // x ≠ 0} => ENNReal.ofReal (H δ x.1))
    have e2 := tsum_subtype {x : F | x ≠ 0} (fun x => ENNReal.ofReal (H δ x))
    have e3 : (∑' x : F, if x = 0 then (0 : ℝ≥0∞) else ENNReal.ofReal (H δ x)) =
        ∑' x : {x : F // x ≠ 0}, ENNReal.ofReal (H δ x.1) := by
      rw [show (∑' x : {x : F // x ≠ 0}, ENNReal.ofReal (H δ x.1)) =
        ∑' x : ({x : F | x ≠ 0} : Set F), ENNReal.ofReal (H δ x.1) from rfl, e2]
      refine tsum_congr fun x => ?_
      by_cases hx : x = 0 <;> simp [hx, Set.indicator]
    rw [e3, ← e1]
    refine tsum_congr fun t => ?_
    rw [_root_.GlobalTheory.CompanionTheory.BasePsi.pure_term F θ r hr S T G g a hST hT δ hδ t]
    simp only [H, P, q, unitsEquivNeZero_apply_coe]
    split_ifs <;> simp
  set z := ENNReal.ofReal (H 1 0) with hzdef
  have hzt : z ≠ ⊤ := ENNReal.ofReal_ne_top
  have hpow : Tendsto (fun δ : ℝ => ENNReal.ofReal (δ ^ d)) (𝓝[>] 0) (𝓝 0) := by
    have c : Continuous fun δ : ℝ => ENNReal.ofReal (δ ^ d) := ENNReal.continuous_ofReal.comp (continuous_pow d)
    have := (c.tendsto 0).mono_left (nhdsWithin_le_nhds (s := Set.Ioi 0))
    simpa [hdpos] using this
  have h1 := (ENNReal.tendsto_ofReal h)
  have h2 : Tendsto (fun δ : ℝ => ENNReal.ofReal (δ ^ d) * z) (𝓝[>] 0) (𝓝 0) := by
    simpa using ENNReal.Tendsto.mul_const hpow (Or.inr hzt)
  have h3 := ENNReal.Tendsto.sub h1 h2 (Or.inr ENNReal.zero_ne_top)
  rw [tsub_zero] at h3
  refine h3.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with δ hδ
  have hδ' : (0 : ℝ) < δ := hδ
  have hne : ENNReal.ofReal (δ ^ d) * z ≠ ⊤ := ENNReal.mul_ne_top ENNReal.ofReal_ne_top hzt
  rw [hsum δ, ENNReal.ofReal_mul (by positivity), hth δ hδ', mul_add]
  exact ENNReal.add_sub_cancel_left hne

theorem psiSide_of_equi : PositivityTheory.Rg.Mass.Equi → PsiSide := by
  intro hE F _ _ hF θ hθ r hr li lam hli hlam S G g hG hGc hG0 hg0 hgS
  refine ⟨GlobalTheory.T.measurable_pure_adelic_function F S G g hG fun v hv => (hgS v hv).1, ?_⟩
  obtain ⟨D, hD, hD1, hDk⟩ := IdeleGroup.exists_isCompact_normOneSubgroup F
  obtain ⟨C, hC⟩ := _root_.GlobalTheory.CompanionTheory.BasePsi.th_pure_rv_zero_bound F hF θ hθ r hr S G g hG hGc hgS D hD
  set d := Module.finrank ℚ F with hd
  have hdpos : d ≠ 0 := (Module.finrank_pos (R := ℚ) (M := F)).ne'
  have hmd : ∀ (a : (AF F)ˣ) (δ : ℝ), 0 < δ → ENNReal.ofReal (md (a * r δ)) = ENNReal.ofReal (md a) * ENNReal.ofReal (δ ^ d) := by
    intro a δ hδ
    rw [md_mul, _root_.GlobalTheory.CompanionTheory.BasePsi.md_ray F hF θ r hr δ hδ, ENNReal.ofReal_mul (md_pos a).le]
  refine ⟨⟨C, fun a => ?_⟩, _root_.GlobalTheory.CompanionTheory.BasePsi.th_pure_vanish F S G g hGc fun v hv => (hgS v hv).2, fun a ha => absurd (Subgroup.mem_top a) ha, fun a _ => ?_⟩
  · set δ : ℝ := md a ^ ((d : ℝ)⁻¹) with hδdef
    have hδ : 0 < δ := Real.rpow_pos_of_pos (md_pos a) _
    have hδd : δ ^ d = md a := Real.rpow_inv_natCast_pow (md_pos a).le hdpos
    set x : (AF F)ˣ := a * (r δ)⁻¹ with hx
    have hxr : x * r δ = a := by simp [hx]
    have hx1 : md x = 1 := by
      have h1 := md_mul x (r δ)
      rw [hxr, _root_.GlobalTheory.CompanionTheory.BasePsi.md_ray F hF θ r hr δ hδ, hδd] at h1
      have := md_pos a
      field_simp at h1
      nlinarith [h1]
    have hxn : x ∈ IdeleGroup.normOneSubgroup F := by
      rw [IdeleGroup.normOneSubgroup, MonoidHom.mem_ker]
      exact Subtype.ext hx1
    obtain ⟨k, hk⟩ := hDk x hxn
    have hk' : pr k * x ∈ D := hk
    have e : th (PositivityTheory.Rg.Base1.pure S G g fun v => rv v 0) a =
        th (PositivityTheory.Rg.Base1.pure S G g fun v => rv v 0) ((pr k * x) * r δ) := by
      rw [mul_assoc, hxr, th_pr]
    rw [e, ← hδd]
    exact hC _ hk' δ hδ
  · have hl := limit hE hF θ hθ r hr li lam hli hlam S G g hG hGc hG0 hg0 hgS a
    have hm := ENNReal.Tendsto.const_mul (a := ENNReal.ofReal (md a)) hl (Or.inr ENNReal.ofReal_ne_top)
    rw [← ENNReal.ofReal_mul (md_pos a).le, ← mul_assoc, mul_inv_cancel₀ (md_pos a).ne', one_mul] at hm
    refine hm.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with δ hδ
    rw [hmd a δ hδ, mul_assoc]

end GlobalTheory.CompanionTheory.BasePsi

end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CoefficientLeviEquivariance
section
noncomputable section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct Topology
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory Filter
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC PositivityTheory.PfSWUS PositivityTheory.Rg.Rsw

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.CompanionTheory.WzLevi

open GlobalTheory.StdUnn.Model (submatrix_fromBlocks_mul block_matrix_one)
open GlobalTheory.CompanionTheory.PcB (blockMatrix_multiply blockMatrix_add' blockMatrix_one mat_mul')
open GlobalTheory.CompanionTheory.IwaAd (levi_mem_P adj_mul_adj_inv adj_inv_mul_adj)

variable {D : D7} {n ρ p : ℕ} {hn : ρ + p = n}

theorem adj_zero' {k l : ℕ} : adj (0 : Mx D k l) = 0 := by
  have h := adj_add (0 : Mx D k l) 0
  rw [add_zero] at h
  exact left_eq_add.1 h

theorem blkA_blk4 {R : Type} {k : ℕ} (a b c d : Matrix (Fin k) (Fin k) R) : blkA (blk4 a b c d) = a := by
  simp only [blkA, blk4, Matrix.submatrix_submatrix, Equiv.symm_comp_self, Matrix.submatrix_id_id,
    Matrix.toBlocks_fromBlocks₁₁]

theorem blockMatrix_zero' {R : Type} [CommRing R] (hn : ρ + p = n) :
    bl hn (0 : Matrix (Fin ρ) (Fin ρ) R) 0 0 (0 : Matrix (Fin p) (Fin p) R) = 0 := by
  simp only [bl, Matrix.fromBlocks_zero]
  rfl

theorem emb_comm (M : Maps D hn) (ζ : hermA D ρ) (g₀ : G D p) (a : GL (Fin p) (AE D))
    (hg : mat g₀ = blk4 a.1 0 0 (adj (a⁻¹).1)) :
    M.w * M.nzx ζ 0 * M.emb g₀ = M.emb g₀ * (M.w * M.nzx ζ 0) := by
  have hE := M.emb_mat g₀ _ _ _ _ hg
  apply GlobalTheory.CompanionTheory.FourierN.mat_injective
  simp only [mat_mul']
  rw [hE, M.w_mat, M.nzx_mat, adj_zero']
  simp only [submatrix_fromBlocks_mul]
  simp only [blockMatrix_zero' hn, blockMatrix_add', blockMatrix_multiply, Matrix.mul_zero, Matrix.zero_mul, Matrix.one_mul, Matrix.mul_one, add_zero,
    zero_add, Matrix.mul_neg, Matrix.neg_mul, neg_zero]

theorem mat_inv_levi (g₀ : G D p) (a : GL (Fin p) (AE D)) (hg : mat g₀ = blk4 a.1 0 0 (adj (a⁻¹).1)) :
    mat g₀⁻¹ = blk4 (a⁻¹).1 0 0 (adj a.1) := by
  have h1 : HMul.hMul (mat g₀) (blk4 (a⁻¹).1 0 0 (adj a.1)) = (1 : Mx D (p + p) (p + p)) := by
    rw [hg, submatrix_fromBlocks_mul]
    have e1 : a.1 * (a⁻¹).1 = 1 := by rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
    have e2 : HMul.hMul (adj (a⁻¹).1) (adj a.1) = (1 : Mx D p p) := adj_inv_mul_adj a
    simp only [Matrix.mul_zero, Matrix.zero_mul, add_zero, zero_add, e1, e2]
    exact block_matrix_one
  calc mat g₀⁻¹ = HMul.hMul (mat g₀⁻¹) (HMul.hMul (mat g₀) (blk4 (a⁻¹).1 0 0 (adj a.1))) := by
        rw [h1]; exact (Matrix.mul_one _).symm
    _ = HMul.hMul (mat (g₀⁻¹ * g₀)) (blk4 (a⁻¹).1 0 0 (adj a.1)) := by
        rw [mat_mul']; exact (Matrix.mul_assoc _ _ _).symm
    _ = blk4 (a⁻¹).1 0 0 (adj a.1) := by
        rw [inv_mul_cancel]; exact Matrix.one_mul _

theorem exists_lv (hn : ρ + p = n) (a : GL (Fin p) (AE D)) :
    ∃ b : GL (Fin n) (AE D), b.1 = bl hn 1 0 0 a.1 := by
  have e : a.1 * (a⁻¹).1 = 1 := by rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
  have e' : (a⁻¹).1 * a.1 = 1 := by rw [← Units.val_mul, inv_mul_cancel, Units.val_one]
  refine ⟨⟨bl hn 1 0 0 a.1, bl hn 1 0 0 (a⁻¹).1, ?_, ?_⟩, rfl⟩
  · rw [blockMatrix_multiply]
    simp only [Matrix.mul_zero, Matrix.zero_mul, Matrix.one_mul, Matrix.mul_one, add_zero, zero_add, e]
    exact blockMatrix_one hn
  · rw [blockMatrix_multiply]
    simp only [Matrix.mul_zero, Matrix.zero_mul, Matrix.one_mul, Matrix.mul_one, add_zero, zero_add, e']
    exact blockMatrix_one hn

theorem det_lv (hn : ρ + p = n) (a : GL (Fin p) (AE D)) (b : GL (Fin n) (AE D)) (hb : b.1 = bl hn 1 0 0 a.1) :
    Matrix.GeneralLinearGroup.det b = Matrix.GeneralLinearGroup.det a := by
  apply Units.ext
  rw [Matrix.GeneralLinearGroup.val_det_apply, Matrix.GeneralLinearGroup.val_det_apply, hb]
  simp only [bl]
  rw [Matrix.det_submatrix_equiv_self, Matrix.det_fromBlocks_zero₂₁, Matrix.det_one, one_mul]

theorem wz_emb : ∀ (D : D7) (n ρ p : ℕ) (hn : ρ + p = n) (M : Maps D hn) (m : Meas D ρ p) (ψ : AddChar (AF D.host.F) ℂ) (b₀ : HermE D ρ)
  (χ : (AE D)ˣ →* Circle) (z : ℂ) (f : G D n → ℂ), IsLaw χ z f → ∀ (g₀ : G D p) (a : GL (Fin p) (AE D)),
  mat g₀ = blk4 a.1 0 0 (adj (a⁻¹).1) → ∀ x : G D n, Wz M m ψ b₀ f (M.emb g₀ * x) =
    (χ (Matrix.GeneralLinearGroup.det a) : ℂ) * npow (absA D (Matrix.GeneralLinearGroup.det a)) (z + (n : ℂ) / 2) * Wz M m ψ b₀ f x := by
  intro D n ρ p hn M m ψ b₀ χ z f hf g₀ a hg x
  have hE := M.emb_mat g₀ _ _ _ _ hg
  have hE' := M.emb_mat g₀⁻¹ _ _ _ _ (mat_inv_levi g₀ a hg)
  rw [blockMatrix_zero' hn] at hE hE'
  have hP : M.emb g₀ ∈ P D n :=
    levi_mem_P hE hE' (by rw [← map_mul, inv_mul_cancel, map_one])
  obtain ⟨b, hb⟩ := exists_lv hn a
  have hA : blkA (mat (M.emb g₀)) = b.1 := by
    rw [hE, blkA_blk4, hb]
  have e : ∀ ζ : hermA D ρ, f (M.w * M.nzx ζ 0 * (M.emb g₀ * x)) =
      (χ (Matrix.GeneralLinearGroup.det a) : ℂ) * npow (absA D (Matrix.GeneralLinearGroup.det a)) (z + (n : ℂ) / 2) *
        f (M.w * M.nzx ζ 0 * x) := by
    intro ζ
    rw [← mul_assoc, emb_comm M ζ g₀ a hg, mul_assoc, hf _ hP b hA, det_lv hn a b hb]
  simp only [Wz]
  simp only [e]
  simp only [mul_assoc]
  rw [integral_const_mul, integral_const_mul]

end GlobalTheory.CompanionTheory.WzLevi

end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CommutingHeckeCapelliOperatorsStatement
section
open scoped ENNReal
open NumberField IsDedekindDomain Matrix MeasureTheory Filter Topology Polynomial
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC PositivityTheory.Rg.Rs GlobalTheory.CompanionTheory.Conc
open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.AutomorphicForm

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.commuting_hecke_capelli_operators : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (r s : ℕ), 0 < r → 0 < s →
  ∃ (S : Subalgebra ℂ (Module.End ℂ (Sm E (r + s)))) (a b : (E →+* ℂ) → ℕ → Module.End ℂ (Sm E (r + s))) (t : (E →+* ℂ) → ℂ),
    (∀ x ∈ S, ∀ y ∈ S, x * y = y * x) ∧
    (∀ x ∈ S, ∀ (τ : E →+* ℂ) (u : ℂ), Commute (cap (a := r + s) τ u) x) ∧
    (∀ x ∈ S, ∀ F : Sm E (r + s), (∀ (v : BlockIx (r + s) r → Ad E) (g : GA E (r + s)), F.1 (unip v * g) = F.1 g) →
      ∀ (v : BlockIx (r + s) r → Ad E) (g : GA E (r + s)), (x F).1 (unip v * g) = (x F).1 g) ∧
    (∀ τ k, a τ k ∈ S) ∧ (∀ τ k, b τ k ∈ S) ∧ (∀ τ, a τ r = 1) ∧ (∀ τ, b τ s = 1) ∧
    (∀ τ, a τ (r - 1) = ∑ i : Fin r, Eop (a := r + s) τ (Fin.castAdd s i) (Fin.castAdd s i) + t τ • 1) ∧
    (∀ τ u, GlobalTheory.CompanionTheory.CTFin.capR r s τ (u - (s : ℂ) / 2) = ∑ k ∈ Finset.range (r + 1), u ^ k • a τ k) ∧
    (∀ τ u, GlobalTheory.CompanionTheory.CTFin.capS r s τ (u + (r : ℂ) / 2) = ∑ k ∈ Finset.range (s + 1), u ^ k • b τ k) := by
  first | exact @GlobalTheory.CompanionTheory.CapCoeff.exists_coeffs | exact GlobalTheory.CompanionTheory.CapCoeff.exists_coeffs | (intros; apply GlobalTheory.CompanionTheory.CapCoeff.exists_coeffs <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.EisensteinHolomorphyOfHeights
section
open scoped TensorProduct ENNReal Matrix NNReal
open MeasureTheory NumberField IsDedekindDomain Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.Doubling GlobalTheory.Eis GlobalTheory GlobalTheory.SiegelFormula
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.AdelicU GlobalTheory.Cont GlobalTheory.MixModel GlobalTheory.StdUnn
open PositivityTheory.Rg.Rsw

noncomputable section

namespace GlobalTheory.CompanionTheory.EisHolFam

open GlobalTheory.StdUnn.HeightExists GlobalTheory.StdUnn.PolesModel

theorem eisHol_of_htExist : HtExist → EisHol := by
  intro _ D p χ _ c f hc hd hl h
  haveI := t2Space_adeleRing' (F := D.host.F)
  have hsub : rightOf (max c ((p : ℝ) / 2)) ⊆ {z : ℂ | c < z.re} := fun z hz =>
    lt_of_le_of_lt (le_max_left _ _) (mem_rightOf.1 hz)
  have key := analyticOnNhd_cosetSum (P := P D p) (Γ := GF D p) (K := K D p) (δ := modP (D := D) (n := p))
    (χ := χ.comp detP) (ρ := (p : ℝ) / 2) (σ := max c ((p : ℝ) / 2)) (Φ := f) isIwasawa isCompact_K
    (hc.mono (Set.prod_mono hsub (Set.subset_univ _)))
    (fun z hz q g => by
      have := hl z (hsub hz) q q.2 (leviBlock (D := D) (n := p) q) rfl g
      push_cast
      exact this)
    (fun τ hτ => summable_spherical τ (lt_of_le_of_lt (le_max_right _ _) hτ))
    (fun g => (hd g).mono hsub) h
  refine key.differentiableOn.mono fun z hz => ?_
  exact mem_rightOf.2 (max_lt hz.1 hz.2)

end GlobalTheory.CompanionTheory.EisHolFam

end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExpSat
section
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.SplitWeil ValuativeRel

namespace GlobalTheory.CompanionTheory.LocGL

theorem expSat : PositivityTheory.SphericalProduct.ExpSat := by
  intro k _ _ _ _ _ n hd V _ _ π hs ha hirr ξ hξ hanti hv
  have hsm : ∀ a, IsSmoothChar (ξ a) := fun a => isSmoothChar_of_isUnram (hξ a)
  have hdeg : ∑ a, (IrrGL.ofChar (ξ a) (hsm a)).1 = n :=
    (Finset.sum_congr rfl fun _ _ => rfl).trans hd
  obtain ⟨f, hf⟩ := GlobalTheory.CompanionTheory.GlFrob.embedding_of_exponent k n hd V π hs ha hirr ξ hsm hdeg hv
  obtain ⟨⟨x, hx1, hxL⟩, hsoc⟩ := GlobalTheory.CompanionTheory.LocGL.socleOne k n ξ hξ hanti hdeg
  subst hx1
  have hS := hsoc _ x.rep hxL
  obtain ⟨e⟩ := hS.equiv_of_embeds hirr ⟨f, hf⟩
  have hL : IsL (PositivityTheory.SphericalProduct.msOne ξ hξ) π := IsL.of_equiv hxL e.symm
  exact (_root_.GlobalTheory.CompanionTheory.OneSat.lOneSat k _ ξ hξ V π hs).1 hL

end GlobalTheory.CompanionTheory.LocGL
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FinStableInducedSpanStatement
section
open NumberField IsDedekindDomain Matrix MeasureTheory Filter Topology
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.SmGL GlobalTheory.DiscSpec GlobalTheory.CompanionTheory.CTFin PositivityTheory.Rg.Rs PositivityTheory.Rg.Rs.InducedTensorMap
open PositivityTheory.Rg.BcB.E PositivityTheory.Rg.BcB.SpectralAccumulation GlobalTheory.CompanionTheory.LimV
open scoped ContDiff
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finStable_induced_span : ∀ {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] {r s : ℕ} (U₁ : Submodule ℂ (Sm E r)) (U₂ : Submodule ℂ (Sm E s)), FinStable (indSpan U₁ U₂) := by
  first | exact @GlobalTheory.CompanionTheory.LimV.indSpan_finStable | exact GlobalTheory.CompanionTheory.LimV.indSpan_finStable | (intros; apply GlobalTheory.CompanionTheory.LimV.indSpan_finStable <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FinStableTwistStatement
section
open NumberField IsDedekindDomain Matrix MeasureTheory Filter Topology
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.SmGL GlobalTheory.DiscSpec GlobalTheory.CompanionTheory.CTFin PositivityTheory.Rg.Rs PositivityTheory.Rg.Rs.InducedTensorMap
open PositivityTheory.Rg.BcB.E PositivityTheory.Rg.BcB.SpectralAccumulation GlobalTheory.CompanionTheory.LimV
open scoped ContDiff
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finStable_twist : ∀ {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] {N : ℕ} (U : Submodule ℂ (Sm E N)) (z : ℂ), FinStable U → FinStable (tw U z) := by
  first | exact @GlobalTheory.CompanionTheory.LimV.finStable_tw | exact GlobalTheory.CompanionTheory.LimV.finStable_tw | (intros; apply GlobalTheory.CompanionTheory.LimV.finStable_tw <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FiniteDimensionalTypedDiscreteStatement
section
open NumberField IsDedekindDomain Matrix MeasureTheory Filter Topology
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.SmGL GlobalTheory.DiscSpec GlobalTheory.CompanionTheory.CTFin PositivityTheory.Rg.Rs PositivityTheory.Rg.Rs.InducedTensorMap
open PositivityTheory.Rg.BcB.E PositivityTheory.Rg.BcB.SpectralAccumulation GlobalTheory.CompanionTheory.LimV
open scoped ContDiff
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finiteDimensional_typed_discrete : ∀ {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] {N : ℕ} (V : Submodule ℂ (Sm E N)) (K : Subgroup (GL (Fin N) (Af E))) (W : Submodule ℂ (Kinf E N → ℂ)), IsDiscrete V → IsOpen (K : Set (GL (Fin N) (Af E))) → FiniteDimensional ℂ W → FiniteDimensional ℂ (typed V K W) := by
  first | exact @GlobalTheory.CompanionTheory.LimV.FdV.fd_typed | exact GlobalTheory.CompanionTheory.LimV.FdV.fd_typed | (intros; apply GlobalTheory.CompanionTheory.LimV.FdV.fd_typed <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FlatAbsoluteCharacterStatement
section
open NumberField IsDedekindDomain Matrix MeasureTheory Filter Topology
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.SmGL GlobalTheory.DiscSpec GlobalTheory.CompanionTheory.CTFin PositivityTheory.Rg.Rs PositivityTheory.Rg.Rs.InducedTensorMap
open PositivityTheory.Rg.BcB.E PositivityTheory.Rg.BcB.SpectralAccumulation GlobalTheory.CompanionTheory.LimV
open scoped ContDiff
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.flat_absolute_character : ∀ {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (N : ℕ) (w : ℂ), FlatFn (absFn (E := E) N w) := by
  first | exact @GlobalTheory.CompanionTheory.LimV.absFn_flat | exact GlobalTheory.CompanionTheory.LimV.absFn_flat | (intros; apply GlobalTheory.CompanionTheory.LimV.absFn_flat <;> assumption)
end

