module

public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.HodgeBundleWeights.TamagawaNumberSpecialUnitary
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SumAbsExOfLe
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.HodgeBundleWeights.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2144
public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.NormNegCmConstantEqAtAllEmbeddings
public import Formalism.LocalRingCardinality.Bundle0003
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0059
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0053
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0041
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0042
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0043
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0891
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsHeightIffOfDegreeEq
public import Development.AbelianVarietyTheory.Definitions.Divisors.WedgeNrmLeOfWedgeNormLe
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0048
public import Development.AbelianVarietyTheory.Definitions.Divisors.MemLevEigenIffTransl
public import Formalism.LocalToGlobal.IndefiniteForms.IndefiniteTree.RealCubicMeans.LogMeanShares.LogMeanStatements.HSClaim
public import Development.AbelianVarietyTheory.Definitions.Divisors.GenRatios
public import Development.AbelianVarietyTheory.Definitions.Divisors.BadElt
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2194
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.HodgeBundleWeights.Hypotheses2
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.HodgeBundleWeights.Bundle0007
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsUniqueIsTanFrameOfIsEmpty
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0058
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0008
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2185
public import Development.AutomorphicArithmetic.CyclotomicBounds.RamifiedDiscriminants.Bundle0004
public import Development.AbelianVarietyTheory.Definitions.Divisors.MulSmulIdemMem
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.Bundle0014
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0056
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0045
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0077
public import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.PermutesRefl
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0130
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1868
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1907
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1871
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0049
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1842
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0331
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0134
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.HolomorphicFamilies.WeightFloorInequalities
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1866
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0127
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0063
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2190
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsImageHeightUnique
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0047
public import Development.WeilBound.CoreStatements.HomogeneousNonvanishing.Bundle0014
public import Development.WeilBound.CoreStatements.HomogeneousNonvanishing.VuSelfA
public import Development.WeilBound.CoreStatements.HomogeneousNonvanishing.VuSelfB
public import CompanionTheory.AutomorphicTheory.KrullDimension.TopologicalKrullDimModel
public import Development.WeilBound.CoreStatements.TorusUniformisation.ChowMahlerFamilies.Bundle0034

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.HodgeBundleWeights.CoverHeightComparison
section
section
set_option autoImplicit false
noncomputable section
open CategoryTheory AlgebraicGeometry NumberField IsDedekindDomain
open scoped TensorProduct NNReal
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Pdiv ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Formalism.L2.Pj GlobalTheory.HTLat GlobalTheory.EigenSplit GlobalTheory.Frames GlobalTheory.AllWt GlobalTheory.CompHt GlobalTheory.CovHt
attribute [local instance] Over.cartesianMonoidalCategory
namespace GlobalTheory.CovHt.FrameCmp
section Different
variable {C : Type} [Field C] [IsAlgClosed C] [CharZero C] {v : Valuation C ℝ≥0} {O : Type} [CommRing O] [Algebra O C]
  {E : Type} [Field E] [NumberField E]
end Different
section Point
variable {p : ℕ} [Fact p.Prime] {C : Type} [Field C] [IsAlgClosed C] [CharZero C] {v : Valuation C ℝ≥0}
  {O : Type} [CommRing O] [Algebra O C] [Algebra ℤ_[p] O] [Algebra ℤ_[p] C] [IsScalarTower ℤ_[p] O C]
  {Λ : Type} [CommRing Λ] [StarRing Λ] (P : Point p v O Λ)
variable [Fact ¬IsUnit (p : O)] [IsAdicComplete (Ideal.span {(p : O)}) O]
end Point
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {l : Level H} {Xo : Moduli Dw l} {c : Coeff l}
section Frame
variable {p : ℕ} [Fact p.Prime] {C : Type} [Field C] [IsAlgClosed C] [CharZero C] {v : Valuation C ℝ≥0}
  {O : Type} [CommRing O] [Algebra O C] [Algebra ℤ_[p] O] [Algebra ℤ_[p] C] [IsScalarTower ℤ_[p] O C]
  [Algebra c.F C] [StarRing (𝓞 E)] [Fact ¬IsUnit (p : O)] [IsAdicComplete (Ideal.span {(p : O)}) O]
end Frame
attribute [local instance] algPadicInt algPadicField towerPadic factPadic PadicComplexHost.isAdicComplete
end GlobalTheory.CovHt.FrameCmp
theorem GlobalTheory.CovHt.cover_height_comparison : _root_.GlobalTheory.CovTop.PublishedHodgeBundleTheorems → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E]
    [IsGalois ℚ E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l),
    HTCmp Xo c := fun _ _ _ _ _ _ _ _ _ _ _ => GlobalTheory.CovHt.FrameCmp.htCmp
end
end
end

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.HodgeBundleWeights.ExistsGoodCoverAtMinimalLevel
section
section
open CategoryTheory AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Theta
open GlobalTheory GlobalTheory.CompHS GlobalTheory.CovTop GlobalTheory.HSApp GlobalTheory.DegVal GlobalTheory.DegCmp
open GlobalTheory.AllWt (Psi wtOf cuspOn cuspW latOn latW normOn petOn GoodOn GoodW rankOn degOn rankW)
open GlobalTheory.CompHt (hodgeWt)
open GlobalTheory.LevDesc (TypeFrame grpHR grpGHR latN levDet secRing transl pull KeepsCusp)
open GlobalTheory.IndefiniteRowSideFullHecke.LevelStructureAutomorphisms (LevelAut)
open GlobalTheory.BadCount
open scoped TensorProduct
noncomputable section
namespace GlobalTheory.CovGmin
set_option maxHeartbeats 1000000 in
set_option synthInstance.maxHeartbeats 400000 in
theorem minimal_level_cover_is_good : _root_.GlobalTheory.CovTop.PublishedHodgeBundleTheorems → ∃ C : ℝ, 0 ≤ C ∧ ∀ (D : D7) (T : CoreJ D), LawsJ T → ∀ j : ℕ, 1 ≤ (T.Q.Dw j).p → 1 ≤ (T.Q.Dw j).q → 2 < Module.finrank ℚ D.host.E / 2 → InR D j → ∀ (Y : Deep T.toCore j) (e : ℕ) (o : ℝ), Y.Good e o → ∀ Lb : ℝ, 1 ≤ Lb → Real.log Y.d.l₂.M ≤ 30 * Lb → fieldSz D.host.E ≤ 3 * Lb → Real.log (D.R.f * D.R.r) ≤ Lb → o ≤ 391 * (D.R.f * D.R.r * Lb) ^ 2 → ∀ (a : (D.host.E →+* ℂ) × ℕ → ℕ) (n : ℕ), Dom a n → Even n → 8 * D.R.f * D.R.r + 4 ≤ n → (∀ (τ : Psi T.Q.H) (k : Fin ((T.Q.Dw j).p + (T.Q.Dw j).q)), (k : ℕ) < (T.Q.Dw j).p → ((n / 2 : ℕ) : ℤ) < laOf (T.Q.Dw j) a n τ k) → Real.log (sizeK (T.Q.Dw j) a n) ≤ 20 * Lb → ∃ s : Set (Y.V (wtZ a n)), s ⊆ (AllWt.latW Y.U (wtZ a n) : Set (Y.V (wtZ a n))) ∧ Submodule.span Y.d.c₂.F s = ⊤ ∧ ∀ y ∈ s, ∀ σ, Y.nrm (wtZ a n) σ y ≤ Real.exp (C * ((D.R.f : ℝ) * D.R.r * Lb) ^ 2 * sizeK (T.Q.Dw j) a n) ∧ ∀ Z, petOn Y.U (xiR D) (fun _ => D.sp.W j) Y.dict Z (wtZ a n) σ y ≤ Real.exp (C * ((D.R.f : ℝ) * D.R.r * Lb) ^ 2 * sizeK (T.Q.Dw j) a n) := by
  intro _
  obtain ⟨CA, hCA0, hA⟩ := GlobalTheory.CovGmin.span_thFam
  obtain ⟨CB, hCB0, hB⟩ := GlobalTheory.RawThetaSup.homN_smul_raw_le
  obtain ⟨CC, hCC0, hC⟩ := _root_.GlobalTheory.CovInt.integral_smul_thLa
  refine ⟨CA + CB + CC + 391, by linarith only [hCA0, hCB0, hCC0], ?_⟩
  intro D T hJ j hp hq hf hj Y e o hG Lb hL hM hE hfr ho a n hDom hev hn hpos hsz
  have hH : GlobalTheory.CovGmin.Hyp D T j Y e o Lb a n :=
    ⟨hJ, hp, hq, hf, hj, hG, hL, hM, hE, hfr, ho, hDom, hev, hn, hpos, hsz⟩
  obtain ⟨_, nab, hnab⟩ := GlobalTheory.CanonConn.exists_isNab_uncond D.host.E T.Q.H (T.Q.Dw j) Y.d.l₂ Y.d.Xo₂ Y.d.c₂
  obtain ⟨Na, hNa, hlog, hint⟩ := hC D T j Y e o Lb a n hH nab hnab
  have hspan := hA D T j Y e o Lb a n hH nab hnab
  have hB' := hB D T j Y e o Lb a n hH nab hnab
  clear hA hB hC
  have hκ : 1 ≤ sizeK (T.Q.Dw j) a n := by
    have h1 := GlobalTheory.RawThetaSup.two_mul_card_psi T.Q.H
    have h2 : 1 ≤ n / 2 * (Fintype.card (Psi T.Q.H) * ((T.Q.Dw j).p + (T.Q.Dw j).q)) :=
      Nat.mul_pos (by omega) (Nat.mul_pos (by omega) (by omega))
    have h3 : (1 : ℝ) ≤ ((n / 2 : ℕ) : ℝ) * (Fintype.card (Psi T.Q.H) * ((T.Q.Dw j).p + (T.Q.Dw j).q) : ℕ) := by
      exact_mod_cast h2
    rw [GlobalTheory.RawThetaSup.sizeK_eq]
    exact h3.trans (le_add_of_nonneg_left (Nat.cast_nonneg _))
  have hNaE : (Na : ℝ) ≤ Real.exp (CC * ((D.R.f : ℝ) * D.R.r * Lb) ^ 2 * sizeK (T.Q.Dw j) a n) :=
    (Real.log_le_iff_le_exp (Nat.cast_pos.2 hNa)).1 hlog
  have hFE : Real.exp (fieldSz Y.d.c₂.F) ≤ Real.exp (391 * ((D.R.f : ℝ) * D.R.r * Lb) ^ 2 * sizeK (T.Q.Dw j) a n) :=
    Real.exp_le_exp.2 ((hG.size.trans ho).trans
      (le_mul_of_one_le_right (mul_nonneg (by norm_num) (sq_nonneg _)) hκ))
  refine ⟨{w | w ∈ (AllWt.latW Y.U (wtZ a n) : Set (Y.V (wtZ a n))) ∧ ∀ σ, Y.nrm (wtZ a n) σ w ≤ Real.exp ((CA + CB + CC + 391) * ((D.R.f : ℝ) * D.R.r * Lb) ^ 2 * sizeK (T.Q.Dw j) a n) ∧ ∀ Z, petOn Y.U (xiR D) (fun _ => D.sp.W j) Y.dict Z (wtZ a n) σ w ≤ Real.exp ((CA + CB + CC + 391) * ((D.R.f : ℝ) * D.R.r * Lb) ^ 2 * sizeK (T.Q.Dw j) a n)}, fun _ h => h.1, ?_, fun _ h => h.2⟩
  refine span_eq_top_of_multiples (Y.V (wtZ a n)) _ _ hspan Na hNa ?_
  rintro y ⟨x0, La, N, P, -, hU, hTb, hTM, hO, hP, hρ, hy⟩
  obtain ⟨s, hs0, hs1, hs2⟩ := _root_.GlobalTheory.SmallScal.exists_small_scalar D.host.E T.Q.H (T.Q.Dw j) Y.d.l₂ Y.d.c₂ n La hU
  refine ⟨s, hs0, fun y₁ hy₁ hc => ⟨hint x0 La N P hU hTb hTM hO hP y hy s hs1 y₁ hy₁, fun σ => ?_⟩⟩
  have hsup := hB' _ x0 La N P hU hTM hO hP hρ y hy s _ (Real.exp_pos _).le
    (fun σ => (hs2 σ).trans (pow_le_pow_left₀ (Real.exp_pos _).le hFE 2)) σ
  have hfin := nrm_le_of_eq_smul D T.toCore j Y (wtZ a n) σ _ _ Na _ _
    (mul_nonneg (mul_nonneg (Real.exp_pos _).le (Real.exp_pos _).le) (Real.exp_pos _).le) hNaE hc hsup
  rw [exp_consts] at hfin
  exact hfin
end GlobalTheory.CovGmin
end
end

section
open CategoryTheory AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Theta
open GlobalTheory GlobalTheory.CompHS GlobalTheory.CovTop GlobalTheory.HSApp GlobalTheory.DegVal GlobalTheory.DegCmp
open GlobalTheory.AllWt (Psi wtOf cuspOn cuspW latOn latW normOn petOn GoodOn GoodW rankOn degOn rankW)
open GlobalTheory.CompHt (hodgeWt)
open GlobalTheory.LevDesc (TypeFrame grpHR grpGHR latN levDet secRing transl pull KeepsCusp)
open GlobalTheory.IndefiniteRowSideFullHecke.LevelStructureAutomorphisms (LevelAut)
open GlobalTheory.BadCount
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
set_option synthInstance.maxHeartbeats 400000 in
theorem _root_.GlobalTheory.T.exists_good_cover_at_minimal_level : _root_.GlobalTheory.CovTop.PublishedHodgeBundleTheorems → ∃ C : ℝ, 0 ≤ C ∧ ∀ (D : D7) (T : CoreJ D), LawsJ T → ∀ j : ℕ, 1 ≤ (T.Q.Dw j).p → 1 ≤ (T.Q.Dw j).q → 2 < Module.finrank ℚ D.host.E / 2 → InR D j → ∀ (Y : Deep T.toCore j) (e : ℕ) (o : ℝ), Y.Good e o → ∀ Lb : ℝ, 1 ≤ Lb → Real.log Y.d.l₂.M ≤ 30 * Lb → fieldSz D.host.E ≤ 3 * Lb → Real.log (D.R.f * D.R.r) ≤ Lb → o ≤ 391 * (D.R.f * D.R.r * Lb) ^ 2 → ∀ (a : (D.host.E →+* ℂ) × ℕ → ℕ) (n : ℕ), Dom a n → Even n → 8 * D.R.f * D.R.r + 4 ≤ n → (∀ (τ : Psi T.Q.H) (k : Fin ((T.Q.Dw j).p + (T.Q.Dw j).q)), (k : ℕ) < (T.Q.Dw j).p → ((n / 2 : ℕ) : ℤ) < laOf (T.Q.Dw j) a n τ k) → Real.log (sizeK (T.Q.Dw j) a n) ≤ 20 * Lb → ∃ s : Set (Y.V (wtZ a n)), s ⊆ (AllWt.latW Y.U (wtZ a n) : Set (Y.V (wtZ a n))) ∧ Submodule.span Y.d.c₂.F s = ⊤ ∧ ∀ y ∈ s, ∀ σ, Y.nrm (wtZ a n) σ y ≤ Real.exp (C * ((D.R.f : ℝ) * D.R.r * Lb) ^ 2 * sizeK (T.Q.Dw j) a n) ∧ ∀ Z, petOn Y.U (xiR D) (fun _ => D.sp.W j) Y.dict Z (wtZ a n) σ y ≤ Real.exp (C * ((D.R.f : ℝ) * D.R.r * Lb) ^ 2 * sizeK (T.Q.Dw j) a n) := by
  first | exact @_root_.GlobalTheory.CovGmin.minimal_level_cover_is_good | exact _root_.GlobalTheory.CovGmin.minimal_level_cover_is_good | (intros; apply _root_.GlobalTheory.CovGmin.minimal_level_cover_is_good <;> assumption)
end
end

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.HodgeBundleWeights.FlagDeformationsEqOfKodairaSpencerEq
section
section
set_option autoImplicit false
noncomputable section
open NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open AlgebraicGeometry CategoryTheory
namespace GlobalTheory.FlagTan
theorem eq_of_kodaira_spencer_eq : _root_.GlobalTheory.CovTop.Hypotheses'' → GlobalTheory.Published.GrothendieckDeformation → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (K : Type) [Field K] [Algebra c.F K] (y : FrPt Xo c K) (x' x'' : Sp (DualNumber K) ⟶ Xo.X) (M : GlobalTheory.FlagTan.HIx Dw (GlobalTheory.FlagTan.psiSet H) → K), 1 ≤ Dw.p + Dw.q → GlobalTheory.FlagTan.IsTanX y x' → GlobalTheory.FlagTan.IsTanX y x'' → GlobalTheory.FlagTan.IsKS (GlobalTheory.FlagTan.psiSet H) y x' M → GlobalTheory.FlagTan.IsKS (GlobalTheory.FlagTan.psiSet H) y x'' M → x' = x'' := by
  intro hP hG E _ _ _ H Dw l Xo c K _ _ y x' x'' M hpq h' h'' k' k''
  obtain ⟨X, hX, hXy, hXM⟩ : ∃ X : Sp (TrivSqZeroExt K (GlobalTheory.FlagTan.HIx Dw (GlobalTheory.FlagTan.psiSet H) → K)) ⟶ Xo.X, X ≫ Xo.s = sOf c _ ∧
      spMap (TrivSqZeroExt.fstHom c.F K (GlobalTheory.FlagTan.HIx Dw (GlobalTheory.FlagTan.psiSet H) → K)).toRingHom ≫ X = y.x ∧
      ∀ M : GlobalTheory.FlagTan.HIx Dw (GlobalTheory.FlagTan.psiSet H) → K,
        GlobalTheory.FlagTan.IsKS (GlobalTheory.FlagTan.psiSet H) y (spMap (GlobalTheory.FlagTan.dir c M).toRingHom ≫ X) M := by
    first
    | exact _root_.GlobalTheory.T.kodaira_spencer_universal_family hP hG E H Dw l Xo c K y hpq
    | exact _root_.GlobalTheory.T.kodaira_spencer_universal_family hP E H Dw l Xo c K y hpq
    | exact (_root_.GlobalTheory.T.kodaira_spencer_universal_family hP hG E H Dw l Xo c K y hpq)
  have htan : ∀ N, GlobalTheory.FlagTan.IsTanX y (spMap (GlobalTheory.FlagTan.dir c N).toRingHom ≫ X) := fun N => by
    refine ⟨?_, ?_⟩
    · rw [Category.assoc, hX, sOf, sOf, ← Spec.map_comp]
      congr 1
      apply CommRingCat.hom_ext
      apply RingHom.ext
      intro a
      exact (GlobalTheory.FlagTan.dir c N).commutes _
    · rw [← Category.assoc, ← Spec.map_comp, ← hXy]
      congr 2
      ext z
      simp
  have uniq := fun x hx => _root_.GlobalTheory.T.flag_tangent_kodaira_spencer_unique hP E H Dw l Xo c K y x hpq hx
  have key := exists_dir_eq_of_smooth (KA l) Xo.X Xo.s Dw.dim Xo.smooth K ((algebraMap c.F K).comp (IntermediateField.inclusion c.le).toRingHom)
    (GlobalTheory.FlagTan.HIx Dw (GlobalTheory.FlagTan.psiSet H)) (GlobalTheory.FlagTan.card_HIx (GlobalTheory.FlagTan.isHalf_psiSet H)) X
    (by rw [hX, sOf])
    (fun N N' e => uniq _ (htan N) N N' (hXM N) (e ▸ hXM N'))
  have hk : ∀ x, GlobalTheory.FlagTan.IsTanX y x → ∃ N, x = spMap (GlobalTheory.FlagTan.dir c N).toRingHom ≫ X := fun x hx =>
    key x (by rw [hx.1, sOf]) (hx.2.trans hXy.symm)
  obtain ⟨N', rfl⟩ := hk x' h'
  obtain ⟨N'', rfl⟩ := hk x'' h''
  rw [uniq _ (htan N') N' M (hXM N') k', uniq _ (htan N'') N'' M (hXM N'') k'']
end GlobalTheory.FlagTan
end
end

section
open NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open AlgebraicGeometry CategoryTheory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.flag_deformations_eq_of_kodaira_spencer_eq : _root_.GlobalTheory.CovTop.Hypotheses'' → GlobalTheory.Published.GrothendieckDeformation → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (K : Type) [Field K] [Algebra c.F K] (y : FrPt Xo c K) (x' x'' : Sp (DualNumber K) ⟶ Xo.X) (M : GlobalTheory.FlagTan.HIx Dw (GlobalTheory.FlagTan.psiSet H) → K), 1 ≤ Dw.p + Dw.q → GlobalTheory.FlagTan.IsTanX y x' → GlobalTheory.FlagTan.IsTanX y x'' → GlobalTheory.FlagTan.IsKS (GlobalTheory.FlagTan.psiSet H) y x' M → GlobalTheory.FlagTan.IsKS (GlobalTheory.FlagTan.psiSet H) y x'' M → x' = x'' := by
  first | exact @_root_.GlobalTheory.FlagTan.eq_of_kodaira_spencer_eq | exact _root_.GlobalTheory.FlagTan.eq_of_kodaira_spencer_eq | (intros; apply _root_.GlobalTheory.FlagTan.eq_of_kodaira_spencer_eq <;> assumption)
end
end

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.HodgeBundleWeights.ImageHeightNonnegOfDivisor
section
section
set_option autoImplicit false
noncomputable section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.BasicNotions.TH Formalism.L2.Theta ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.CompHt GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.Mean4 GlobalTheory.Mean4O
open scoped ENNReal Classical
namespace GlobalTheory.ImageHeightNonneg
theorem imageHeight_nonneg_of_divisor : _root_.GlobalTheory.CovTop.PublishedHodgeBundleTheorems → ∀ (K V Ω : Type) [Field K] [NumberField K] [_root_.NumberField.IsTotallyComplex K] [AddCommGroup V] [Module K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] [Field Ω] [Algebra K Ω] (Nm : (K →+* ℂ) → V → ℝ) (L : Submodule (𝓞 K) V) (ev : V →ₗ[K] Ω) (d n : ℕ) (w : Fin n → V) (abelian₂ : ℝ), HasGram Nm → (∀ σ x, Nm ((starRingEnd ℂ).comp σ) x = Nm σ x) → Submodule.span K (L : Set V) = ⊤ → IsShortGen Nm L w abelian₂ → 0 < imageDeg ev d → 0 ≤ imageHeight Nm L ev d + Real.log abelian₂ :=
  fun _ => imageHeight_add_log_nonneg
end GlobalTheory.ImageHeightNonneg
end
end
end

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.HodgeBundleWeights.LogSumBadPrimesBoundOfCovering
section
section
open CategoryTheory AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Theta
open GlobalTheory GlobalTheory.CompHS GlobalTheory.CovTop GlobalTheory.HSApp GlobalTheory.DegVal GlobalTheory.DegCmp
open GlobalTheory.AllWt (Psi wtOf cuspOn cuspW latOn latW normOn petOn GoodOn GoodW rankOn degOn rankW)
open GlobalTheory.CompHt (hodgeWt)
open GlobalTheory.LevDesc (TypeFrame grpHR grpGHR latN levDet secRing transl pull KeepsCusp)
open GlobalTheory.IndefiniteRowSideFullHecke.LevelStructureAutomorphisms (LevelAut)
open GlobalTheory.BadCount
open scoped TensorProduct
open GlobalTheory.FlatLine GlobalTheory.FlatTw GlobalTheory.IndefiniteRowSideFullHecke.ComponentMassSum GlobalTheory.ShFam GlobalTheory.IndefiniteRowSideFullHecke.DifferentConjugateDefects ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions.TH
set_option maxHeartbeats 400000
noncomputable section
namespace GlobalTheory.BadLogCov
theorem log_sum_bad_primes_le_sq : _root_.GlobalTheory.CovTop.PublishedHodgeBundleTheorems → ∃ C : ℝ, 0 ≤ C ∧ ∀ (D : D7) (T : CoreJ D), LawsJ T → ∀ j : ℕ, InR D j → ∀ (Y : Deep T.toCore j) (e : ℕ) (o : ℝ), Y.Good e o → ∀ Lb : ℝ, 1 ≤ Lb → Real.log Y.d.l₂.M ≤ 30 * Lb → fieldSz D.host.E ≤ 3 * Lb → Real.log (D.R.f * D.R.r) ≤ Lb → GlobalTheory.FlatTw.logSum (GlobalTheory.FlatTw.badPrimes T.Q.H Y.d.l₂) ≤ C * ((D.R.f : ℝ) * D.R.r * Lb) ^ 2 := by
  intro _
  refine ⟨37, by norm_num, fun D T hT j hj Y e o hY Lb hL hM hE hfr => ?_⟩
  have hQ := hT.pins
  have hM0 : Y.d.l₂.M ≠ 0 := by have := Y.d.l₂.three_le; omega
  have h1 := UpperTheory.KR.sum_log_bad_le D.host.toHostAx Y.d.l₂.M (badPrimes T.Q.H Y.d.l₂) hM0 fun p hp => by
    obtain ⟨hp, h'⟩ := mem_badPrimes.1 hp
    refine ⟨hp, ?_⟩
    rcases h' with h' | h' | h' | h' | h'
    · exact Or.inl h'
    · exact Or.inr (Or.inl (h'.trans hQ.1.1))
    · exact Or.inr (Or.inr (Or.inl h'))
    · exact Or.inr (Or.inr (Or.inr h'))
    · rw [hY.lev.2] at h'
      exact absurd (Nat.dvd_one.1 h') hp.ne_one
  have hrd : Real.log D.host.rd ≤ fieldSz D.host.E := by
    refine le_trans (le_of_eq ?_) (log_rd_le_fieldSz D.host.E)
    unfold Formalism.HC.HostRaw.rd
    rw [Real.log_rpow (abs_pos.2 (by exact_mod_cast NumberField.discr_ne_zero D.host.E))]; ring
  have hsum : GlobalTheory.FlatTw.logSum (GlobalTheory.FlatTw.badPrimes T.Q.H Y.d.l₂) ≤ 37 * Lb := by
    refine le_trans h1 ?_; linarith
  have hn : 0 < D.R.n := D.R.ord_pos
  have h1' := D.R.two_le_m
  have h2' := D.R.m_add_three_le_k
  have hf : (1 : ℝ) ≤ D.R.f := by exact_mod_cast (by unfold Ranks.f; omega : 1 ≤ D.R.f)
  have hr : (1 : ℝ) ≤ D.R.r := by exact_mod_cast (by unfold Ranks.r; omega : 1 ≤ D.R.r)
  have hfr1 : (1 : ℝ) ≤ (D.R.f : ℝ) * D.R.r := one_le_mul_of_one_le_of_one_le hf hr
  have hX : Lb ≤ ((D.R.f : ℝ) * D.R.r * Lb) ^ 2 := by
    have a : Lb ≤ (D.R.f : ℝ) * D.R.r * Lb := le_mul_of_one_le_left (by linarith) hfr1
    have b : (1 : ℝ) ≤ (D.R.f : ℝ) * D.R.r * Lb := hL.trans a
    nlinarith
  linarith
end GlobalTheory.BadLogCov
end
end

section
open CategoryTheory AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Theta
open GlobalTheory GlobalTheory.CompHS GlobalTheory.CovTop GlobalTheory.HSApp GlobalTheory.DegVal GlobalTheory.DegCmp
open GlobalTheory.AllWt (Psi wtOf cuspOn cuspW latOn latW normOn petOn GoodOn GoodW rankOn degOn rankW)
open GlobalTheory.CompHt (hodgeWt)
open GlobalTheory.LevDesc (TypeFrame grpHR grpGHR latN levDet secRing transl pull KeepsCusp)
open GlobalTheory.IndefiniteRowSideFullHecke.LevelStructureAutomorphisms (LevelAut)
open GlobalTheory.BadCount
open scoped TensorProduct
open GlobalTheory.FlatLine GlobalTheory.FlatTw GlobalTheory.IndefiniteRowSideFullHecke.ComponentMassSum GlobalTheory.ShFam GlobalTheory.IndefiniteRowSideFullHecke.DifferentConjugateDefects ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions.TH
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.log_sum_bad_primes_bound_of_covering : _root_.GlobalTheory.CovTop.PublishedHodgeBundleTheorems → ∃ C : ℝ, 0 ≤ C ∧ ∀ (D : D7) (T : CoreJ D), LawsJ T → ∀ j : ℕ, InR D j → ∀ (Y : Deep T.toCore j) (e : ℕ) (o : ℝ), Y.Good e o → ∀ Lb : ℝ, 1 ≤ Lb → Real.log Y.d.l₂.M ≤ 30 * Lb → fieldSz D.host.E ≤ 3 * Lb → Real.log (D.R.f * D.R.r) ≤ Lb → GlobalTheory.FlatTw.logSum (GlobalTheory.FlatTw.badPrimes T.Q.H Y.d.l₂) ≤ C * ((D.R.f : ℝ) * D.R.r * Lb) ^ 2 := by
  first | exact @_root_.GlobalTheory.BadLogCov.log_sum_bad_primes_le_sq | exact _root_.GlobalTheory.BadLogCov.log_sum_bad_primes_le_sq | (intros; apply _root_.GlobalTheory.BadLogCov.log_sum_bad_primes_le_sq <;> assumption)
end
end

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.HodgeBundleWeights.VolumeEstimateHypotheses
section
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.BasicNotions.TH Formalism.L2.Theta ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.CompHt GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.Mean4 GlobalTheory.Mean4O
open scoped ENNReal Classical
namespace SelfIntersectionVolumeEstimates
def SelfIntersectionBound : Prop := _root_.GlobalTheory.CovTop.PublishedHodgeBundleTheorems → ∀ (K V Ω : Type) [Field K] [NumberField K] [AddCommGroup V] [Module K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] [Field Ω] [Algebra K Ω] (Nm : (K →+* ℂ) → V → ℝ) (W : Submodule (𝓞 K) V) (ev : V →ₗ[K] Ω) (D : ℕ) (X : AlgebraicGeometry.Scheme.{0}) [AlgebraicGeometry.IsIntegral X] (p : X ⟶ Sp (𝓞 K)) (L : GlobalTheory.HermLB p) (ψ : Ω →+* X.functionField) (s : W → L.B.Sec) (t a : ℝ), (∀ σ : K →+* ℂ, (starRingEnd ℂ).comp σ ≠ σ) → HasGram Nm → (∀ σ x, Nm ((starRingEnd ℂ).comp σ) x = Nm σ x) → W.FG → Submodule.span K (W : Set V) = ⊤ → GlobalTheory.DegVal.GenRatios ev → 0 < imageDeg ev D → GlobalTheory.ImageModel.IsModelOf Nm W ev D p L ψ s → (L.shift (fun _ => t) (fun _ => rfl)).IsSelfInter a → a ≤ (Module.finrank ℚ K : ℝ) * ((D : ℝ) + 1) * ((imageDeg ev D : ℝ) * (imageHeight Nm W ev D + t))
set_option synthInstance.maxHeartbeats 400000 in
def SmallSectionsInject : Prop := _root_.GlobalTheory.CovTop.PublishedHodgeBundleTheorems → ∀ (D : D7) (T : Core D) (j : ℕ) (Y : Deep T j) (e : ℕ) (o : ℝ), Y.Good e o → 2 < Module.finrank ℚ D.host.E / 2 → ∀ (Z : Comp Y.d.Xo₂ Y.d.c₂) (u : GlobalTheory.AllWt.Weight (T.Q.Dw j)) (X : AlgebraicGeometry.Scheme.{0}) [AlgebraicGeometry.IsIntegral X] (p : X ⟶ Sp (𝓞 Y.d.c₂.F)) (L : GlobalTheory.HermLB p) (ψ : Om Z →+* X.functionField) (s : latOn Y.U Z (wtOf (T.Q.Dw j) u 0) → L.B.Sec) (t : ℝ), GoodOn Y.U (xiR D) (fun _ => D.sp.W j) Y.dict Z (wtOf (T.Q.Dw j) u 0) → GlobalTheory.DegVal.BirOn Y.U Z (wtOf (T.Q.Dw j) u 0) → NoBase Y.U Z (wtOf (T.Q.Dw j) u 0) → 0 < Y.dg u Z → GlobalTheory.ImageModel.IsModelOf (normOn Y.U (xiR D) (fun _ => D.sp.W j) Y.dict Z (wtOf (T.Q.Dw j) u 0)) (latOn Y.U Z (wtOf (T.Q.Dw j) u 0)) (genPoint Z (cuspOn Y.U Z (wtOf (T.Q.Dw j) u 0))) (dimFlag (T.Q.Dw j)) p L ψ s → ∀ i : ℕ, 1 ≤ i → (smallL Y.U (xiR D) (fun _ => D.sp.W j) Y.dict Z (wtOf (T.Q.Dw j) u 0) (8 * i) t).encard ≤ ((L.shift (fun _ => t) (fun _ => rfl)).pow (8 * i)).smallSec.encard
def VolumeEstimateHypotheses : Prop := _root_.SelfIntersectionVolumeEstimates.SelfIntersectionBound ∧ _root_.SelfIntersectionVolumeEstimates.SmallSectionsInject
end SelfIntersectionVolumeEstimates
end
end

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.HodgeBundleWeights.VolumeLeSelfIntersection
section
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.BasicNotions.TH Formalism.L2.Theta ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.CompHt GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.Mean4 GlobalTheory.Mean4O
open scoped ENNReal Classical
open PositivityTheory.UnitarySelfGeneration.FrameHeightScaling
theorem PositivityTheory.UnitarySelfGeneration.volume_le_self_intersection : PositivityTheory.UnitarySelfGeneration.ChowFormHeight → _root_.GlobalTheory.CovTop.PublishedHodgeBundleTheorems → ∀ (K V Ω : Type) [Field K] [NumberField K] [AddCommGroup V] [Module K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] [Field Ω] [Algebra K Ω] (Nm : (K →+* ℂ) → V → ℝ) (L : Submodule (𝓞 K) V) (ev : V →ₗ[K] Ω) (d N m : ℕ) (b : Module.Basis (Fin N) K V) (g : Matrix (Fin N) (Fin m) K) (A : (K →+* ℂ) → Matrix (Fin N) (Fin N) ℂ) (t : ℝ), IsFrame Nm L b g A → GlobalTheory.DegVal.GenRatios ev → 0 < imageDeg ev d → ∀ (M : GlobalTheory.ZH.RatModel (𝓞 K) Ω), M.HasDiv (fun k => ev (∑ j, g j k • b j)) → GlobalTheory.IsArithVar M.s d → ∀ (H : ReciprocityTheory.ChartRestriction.G.Semi.LB M.Z) (hH : H.IsLB) (e : H.ι → Ω), M.GenTriv H e → ∀ (s : Fin m → H.Sec), (∀ k, M.HasVal e (s k) (ev (∑ j, g j k • b j))) → ∀ (hs : ⨆ k, ReciprocityTheory.ChartRestriction.G.Out.nonzeroLocus (s k) = ⊤) (Mt : (𝓞 K →+* ℂ) → Matrix (Fin m) (Fin m) ℂ) (hdet : ∀ σ, (Mt σ).det ≠ 0) (hc : ∀ σ, ∃ U ∈ Matrix.unitaryGroup (Fin m) ℂ, Mt ((starRingEnd ℂ).comp σ) = (Mt σ).map (starRingEnd ℂ) * U), (∀ (σ : K →+* ℂ) (x : Fin N → ℂ), ∑ a, ‖∑ k, Mt (σ.comp (algebraMap (𝓞 K) K)) k a * ∑ j, σ (g j k) * x j‖ ^ 2 = GlobalTheory.Adelic.archSize (A σ) x ^ 2) → ((GlobalTheory.HermLB.fs M.s hH s hs Mt hdet hc).shift (fun _ => t) (fun _ => rfl)).IsSelfInter (((d : ℝ) + 1) * (Module.finrank ℚ K : ℝ) * (imageDeg ev d : ℝ) * (imageHeight Nm L ev d + t)) := by
  intro HP hP K V Ω _ _ _ _ _ _ _ _ Nm L ev d N m b g A t hF hG hd M hNm hX H hH e he s hv hs Mt hdet hc hMt
  have : CharZero Ω := charZero_of_injective_algebraMap (algebraMap K Ω).injective
  have hcomb := PositivityTheory.Xgn.A_xgz_height_r_vol_up_model_model.exists_comb ev b g hF.full
  obtain ⟨i, hi, -⟩ := hNm (genericPoint M.Z)
  have htop := PositivityTheory.Xgn.A_xgz_height_r_vol_up_model_model.closure_eq_top ev (fun k => ev (∑ j, g j k • b j))
    hcomb i hi hG.2
  obtain ⟨n, rfl⟩ : ∃ n, m = n + 1 := ⟨m - 1, by have := i.pos; omega⟩
  obtain ⟨Z, hZ, hZp⟩ := GlobalTheory.ZH.exists_isCl_isProjOver (𝓞 K) Ω n _ ⟨i, hi⟩ htop
  have hZX : GlobalTheory.IsArithVar Z.s d := by
    have : Algebra.IsAlgebraic ℤ ℚ := IsLocalization.isAlgebraic ℚ (nonZeroDivisors ℤ)
    have : Algebra.IsAlgebraic ℤ K := Algebra.IsAlgebraic.trans ℤ ℚ K
    have h1 : Algebra.trdeg ℤ Ω = d :=
      (GlobalTheory.trdeg_eq_of_isAlgebraic_bot ℤ K Ω).trans (ModelDimension.ModelDim.trdeg_eq ev hG hd)
    refine ⟨inferInstance, inferInstance, inferInstance, hZp, (GlobalTheory.flat_int_iff_charZero _).2 ?_,
      ModelDimension.ModelDim.topologicalKrullDim_model inferInstance Z h1⟩
    exact (Z.res ⊤ ⟨genericPoint Z.Z, trivial⟩).charZero
  obtain ⟨π, hπ⟩ := hZ.exists_isHom (M' := M) (φ := AlgHom.id _ _) hNm
  obtain ⟨H', hH', e', s', he', hv', hs'⟩ := exists_bundle Z _ hZ.1
  obtain ⟨N', b', f', hf'⟩ := (imageDeg_pos_iff ev d).1 hd
  have hf := isChowFormInt_basis ev b' b hf'
  set f := GlobalTheory.ChowHt.linSubst (b'.toMatrix b) f'
  set δ := imageDeg ev d with hδ
  have hN : 0 < N := by
    obtain ⟨y, hy, -⟩ := hf.exists_point
    obtain ⟨j, -⟩ := Function.ne_iff.1 hy
    exact j.pos
  have hδ0 : ((d : ℝ) + 1) * δ ≠ 0 := mul_ne_zero (by positivity) (Nat.cast_ne_zero.2 hd.ne')
  have hh : imageHeight Nm L ev d = GlobalTheory.ChowHt.formHeight δ g A f / (((d : ℝ) + 1) * δ) :=
    GlobalTheory.ImageHeightUnique.imageHeight_eq K V Ω Nm L ev d _
      ⟨N, _, b, g, A, δ, f, hF, hf, mul_div_cancel₀ _ hδ0⟩
  have hc0 : ((Real.exp t : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 (Real.exp_pos t).ne'
  have ht : (fun k => ev (∑ j, g j k • b j)) = fun k => ∑ j, algebraMap K Ω (g j k) * ev (b j) := funext fun k => by
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [map_sum, map_smul, Algebra.smul_def]
  have hdet' : ∀ σ, (((Real.exp t : ℝ) : ℂ) • Mt σ).det ≠ 0 := fun σ => by
    rw [Matrix.det_smul]; exact mul_ne_zero (pow_ne_zero _ hc0) (hdet σ)
  have hc' : ∀ σ, ∃ U ∈ Matrix.unitaryGroup (Fin (n + 1)) ℂ, ((Real.exp t : ℝ) : ℂ) • Mt ((starRingEnd ℂ).comp σ) =
      (((Real.exp t : ℝ) : ℂ) • Mt σ).map (starRingEnd ℂ) * U := fun σ => by
    obtain ⟨U, hU, h⟩ := hc σ
    refine ⟨U, hU, ?_⟩
    rw [h, ← smul_mul_assoc]
    congr 1
    ext i j
    simp only [Matrix.smul_apply, Matrix.map_apply, smul_eq_mul, map_mul, Complex.conj_ofReal]
  have h1 := HP K Ω d N (n + 1) δ g (fun σ => ((Real.exp t : ℝ) : ℂ) • A σ) hF.full
    (fun σ => by rw [Matrix.det_smul]; exact mul_ne_zero (pow_ne_zero _ hc0) (hF.herm σ))
    (conjCompat_smul hF.herm hF.conj hc0) (fun j => ev (b j)) Z (ht ▸ hZ) hZX f hf H' hH' e' he' s'
    (fun k => congrFun ht k ▸ hv' k) hs' (fun σ => ((Real.exp t : ℝ) : ℂ) • Mt σ) hdet' hc'
    (fun σ x => by rw [sum_smul, archSize_smul_sq, hMt])
  have h2 := (hP.p4.arProj _ _ _ Z.s M.s d hZX hX π hπ.inducedModelMorphism_comp_structureMap (map_generic hπ)
    (by rw [residueDegree_eq_one hπ]; exact one_ne_zero)).1 _ _ h1
  have h3 := (isometric_pull_fs hπ hH' he' hv' hs' hH he hv hs Mt _ hdet hc hdet' hc' t
    (fun _ => rfl)).isSelfInter hX h2
  convert h3 using 1
  rw [residueDegree_eq_one hπ, formHeight_smul hN g hF.herm hf.ne_zero hf.homog, hh]
  push_cast
  field_simp
end
end

