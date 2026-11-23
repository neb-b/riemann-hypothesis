module

public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.HodgeBundleWeights.TamagawaNumberSpecialUnitary
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2866
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.HodgeBundleWeights.Bundle0001
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.HodgeBundleWeights.Hypotheses2
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.HodgeBundleWeights.Bundle0023
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.HodgeBundleWeights.Bundle0011
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.HodgeBundleWeights.Bundle0015
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.HodgeBundleWeights.Bundle0024
public import Mathlib
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0012
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ToroidalCompactificationBis
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0019
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0008
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
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0058
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsLogCanonicalMultipleCanonical
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0004
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.DenseInterior
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0006
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1856
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1664
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1842
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2440
public import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.IsProjOverIffIsProperAndExistsIsAmpleLB
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2452
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2457
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorusFlagUnitWeightBundlesNef
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2834
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1843
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2365
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1159
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemNonzeroLocusFormMap
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1246
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.GeometricallyIntegralIffGeometricallyConnectedOf
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0920
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1876
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1884
public import Development.AbelianVarietyTheory.Definitions.Foundations.ExistsIsDeepOfField
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1483
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.HodgeBundleWeights.Bundle0002
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2850
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.HodgeBundleWeights.Bundle0009
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.HodgeBundleWeights.Bundle0006
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2877

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.HodgeBundleWeights.ExistsCuspRegularLevelDeterminant
section
section
set_option autoImplicit false
set_option synthInstance.maxHeartbeats 400000
noncomputable section
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.BasicNotions
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.CompHS GlobalTheory.CovTop GlobalTheory.HSApp GlobalTheory.Cartier
open GlobalTheory.AllWt (Psi wtOf cuspOn cuspW secZ ptF LiesOn)
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.CompHt (hodgeWt)
open GlobalTheory.LevDesc (TypeFrame grpHR grpGHR levDet secRing move)
open GlobalTheory.IndefiniteRowSideFullHecke.LevelStructureAutomorphisms (LevelAut)
open GlobalTheory.OrbitSep
namespace GlobalTheory.OrbitSep
set_option maxHeartbeats 2000000 in
theorem separate_orbits_by_cusp (hP2 : _root_.GlobalTheory.CovTop.PublishedHodgeBundleTheorems) (hG : GlobalTheory.Published.GrothendieckDeformation) (hQ : GlobalTheory.HSCore.Quoted)
    (hSg : GlobalTheory.Published.SiegelToroidalIntegral) (hKS : GlobalTheory.Published.ToroidalForFanKS)
    (hLie : GlobalTheory.Published.SemiAbelianLieSeminegative) {D : D7}
    {T : Core D} {j : ℕ} (Y : Deep T j) {e : ℕ} {o : ℝ} (hY : Y.Good e o) (hf : 2 < Module.finrank ℚ D.host.E / 2)
    (hp : 1 ≤ (T.Q.Dw j).p) (hq : 1 ≤ (T.Q.Dw j).q) (S : Subgroup (LevelAut (T.Q.Dw j) Y.d.l₂))
    {I : Ideal (𝓞 D.host.E)} {g : ℕ} (hI : NeatPrime I g ((T.Q.Dw j).p + (T.Q.Dw j).q)) (hM : Y.d.l₂.Mb ≤ I)
    (hS : ∀ γ ∈ S, UnipAt I γ) (s : ℕ)
    (hs : (T.Q.Dw j).p + (T.Q.Dw j).q + ((T.Q.Dw j).dim + 1).choose 2 + 1 ≤ s) (Z : Comp Y.d.Xo₂ Y.d.c₂) :
    ∃ y : FrPt Y.d.Xo₂ Y.d.c₂ ℂ, LiesOn Z y ∧
      ∀ [Fintype {h : S // LiesOn Z (move Y.d.Xo₂ Y.d.c₂ (h : LevelAut (T.Q.Dw j) Y.d.l₂)⁻¹ y)}]
        (a : {h : S // LiesOn Z (move Y.d.Xo₂ Y.d.c₂ (h : LevelAut (T.Q.Dw j) Y.d.l₂)⁻¹ y)} → ℂ),
        (∀ u ∈ cuspOn Y.U Z (wtOf (T.Q.Dw j) ((s : ℤ) • hodgeWt (T.Q.Dw j)) 0),
          ∑ h, a h * evR Y.d.Xo₂ Y.d.c₂ u (move Y.d.Xo₂ Y.d.c₂ (h.1 : LevelAut (T.Q.Dw j) Y.d.l₂)⁻¹ y) = 0) → a = 0 := by
  have hP : _root_.GlobalTheory.CovTop.Hypotheses'' := _root_.GlobalTheory.T.covering_topology_refinement hP2
  have hA : Y.d.l₂.A = 1 := hY.lev.2
  have hA' : Y.d.l₂.A.Coprime Y.d.l₂.M := hA ▸ Nat.coprime_one_left _
  have hpq : 1 ≤ (T.Q.Dw j).p + (T.Q.Dw j).q := by omega
  have hdim : 1 ≤ (T.Q.Dw j).dim := Nat.mul_pos (Nat.mul_pos (by omega) hp) hq
  have hfl : 1 ≤ FlagTan.dimFlag (T.Q.Dw j) := by
    refine Nat.mul_pos (by omega) ?_
    exact Nat.choose_pos (by omega)
  obtain ⟨TF⟩ : Nonempty (TorFlag Y.d.Xo₂ Y.d.c₂) :=
    _root_.GlobalTheory.T.torFlag_nonempty_of_one_le_dimFlag hP _ _ _ _ Y.d.Xo₂ Y.d.c₂ hfl
  have hF := hY.geo
  have hV := GlobalTheory.T.flagSpace_component_smooth_projective_connected _ _ _ _ _ _ TF Z hF
  obtain ⟨hint, hsm, hpr, hgc, hsurj, hnorm, hgen⟩ := GlobalTheory.T.compactificationComponent_integral_smooth_projective _ _ _ _ _ _ TF Z hF
  obtain ⟨y, hy⟩ := _root_.GlobalTheory.GenCxPt.exists_frPt_ptF_eq_genPt _ _ _ _ Y.d.Xo₂ Y.d.c₂ Z
  have hyZ : LiesOn Z y := fun s => hy s ▸ (Z.2.1.isGenericPoint_genericPoint (isClosed_of_mem_irreducibleComponents _ Z.2)).mem
  refine ⟨y, hyZ, fun a ha => ?_⟩
  have lift : ∀ w : FrPt Y.d.Xo₂ Y.d.c₂ ℂ, LiesOn Z w → ∃ v : Sp ℂ ⟶ V₀ TF.Y Z, v ≫ i₀ TF.Y Z = ptF w := fun w hw =>
    ⟨IsOpenImmersion.lift (i₀ TF.Y Z) (ptF w) (by
      rintro _ ⟨s, rfl⟩
      exact ⟨⟨_, (j_mem_barComp Z _).2 (hw s)⟩, rfl⟩), IsOpenImmersion.lift_fac _ _ _⟩
  obtain ⟨v₁, hv₁⟩ := lift y hyZ
  choose v hv using fun h : {h : S // LiesOn Z (move Y.d.Xo₂ Y.d.c₂ (h : LevelAut (T.Q.Dw j) Y.d.l₂)⁻¹ y)} => lift _ h.2
  obtain ⟨Γ, ρ, hΓ, hρ, hmem⟩ := _root_.GlobalTheory.CompLevelStab.stab_acts _ _ _ _ _ _ TF.Y Z hpq hA S
  obtain ⟨X', W, φ, ℓ, ρ', q, sW, hint', n1, n2, n3, n4, n5, n6, n7, n8, n9, n10, n11⟩ :=
    GlobalTheory.T.equivariant_normal_projective_compactification Y.d.c₂.F _ _ (s₀ TF.Y Z) (j₀ TF.Y Z) Γ ρ hpr ⟨v₁ (IsLocalRing.closedPoint ℂ)⟩ hnorm hρ.1
  obtain ⟨δ, hδ, eδ, hlin⟩ := _root_.GlobalTheory.T.hodgeLineBundle_rational_linear_equiv_class hP2 _ _ _ _ _ _ TF Z hpq hA hF
  obtain ⟨N, hN, eN⟩ := _root_.GlobalTheory.QuotDescent.descent Y.d.c₂.F X' W q sW Γ ρ' _ _ (n7 ▸ n2) n6
    (hlin I g hI hM Γ Γ.subtype ρ (fun γ => hS _ (hΓ γ.2)) hρ X' φ ℓ ρ' n1 n2 n3 n4 n5)
  let K := CanonLB.all (s₀ TF.Y Z) (T.Q.Dw j).dim
  obtain ⟨κ, hκ, eκ, θ, hθ⟩ := GlobalTheory.T.exists_toroidalCanonicalBundle_weight_line _ _ _ _ _ _ TF Z hpq hF K
  set m := ((T.Q.Dw j).dim + 1).choose 2 + 1 with hm
  obtain ⟨t, rfl⟩ : ∃ t, s = m + t := Nat.exists_eq_add_of_le (by omega)
  obtain ⟨N', hN', eN'⟩ := cls_surj (t • cls δ hδ - cls κ hκ)
  obtain ⟨B, hB, eB⟩ := cls_surj (m • cls δ hδ + cls N' hN')
  have C := common₀ TF.X Z
  have nef : ∀ (L : LB (X₀ TF.Y Z)) (hL : L.IsLB) (w : AllWt.Weight (T.Q.Dw j)), GapGe 0 w →
      CechPic.pull (π₀ TF.X Z) (cls L hL) = cls (L₀ TF.X Z w) (isLB_L₀ TF.X Z w) →
      (letI := algebraΓOfHom (s₀ TF.Y Z); IsNef Y.d.c₂.F L) := fun L hL w hw e =>
    GlobalTheory.T.isNefLineBundle_of_pullback_surjective_projective _ _ _ _ _ _ L hL _ _ (π₀_s₀ TF.X Z) hpr hV.2.1 hsurj e
      (_root_.GlobalTheory.T.base_weight_line_bundle_is_nef hP hQ.nef hLie _ _ _ _ _ _ TF Z hF w hw)
  have ens : ∀ n : ℕ, cls (L₀ TF.X Z ((n : ℤ) • hodgeWt (T.Q.Dw j))) (isLB_L₀ TF.X Z _) =
      n • cls (L₀ TF.X Z (hodgeWt (T.Q.Dw j))) (isLB_L₀ TF.X Z _) := fun n => by
    rw [natCast_zsmul]; exact cls_nsmul (common₀ TF.X Z) n _
  have nefN' := nef N' hN' ((t : ℤ) • hodgeWt (T.Q.Dw j) - kapBase _) (gapGe_sub_kapBase _ (by omega)) (by
    have h := GlobalTheory.HSApp.cls_common_add (common₀ TF.X Z) ((t : ℤ) • hodgeWt (T.Q.Dw j) - kapBase _) (kapBase _)
    rw [sub_add_cancel] at h
    rw [eN', map_sub, map_nsmul, eδ, eκ, ← ens, sub_eq_iff_eq_add]
    exact h)
  have hKB := isLB_tens K.isLB hB
  have hθB := LB.isLB_div hκ K.isLB
  obtain ⟨Φ, hΦ, hval⟩ := _root_.GlobalTheory.OrbitSep.exists_rule_of_cls_pull D T j Y e o hY hf Z TF (((m + t : ℕ) : ℤ) • hodgeWt (T.Q.Dw j)) _
    (isLB_tens hθB hKB) (by
      rw [cls_tens hθB hKB, cls_div hκ K.isLB, cls_tens K.isLB hB, eB, eN', ens, ← eδ, ← map_nsmul]
      refine congrArg _ ?_
      have key : ∀ (A : Type 1) [AddCommGroup A] (a b k : A) (m t : ℕ),
          b - k + (k + (m • a + (t • a - b))) = (m + t) • a := fun A _ a b k m t => by
        rw [add_nsmul, ← add_assoc, sub_add_cancel, add_left_comm, add_sub_cancel]
      exact key _ _ _ _ _ _)
  choose k hk using fun h => exists_chart_pt hKB (v h ≫ j₀ TF.Y Z)
  choose k' hk' using fun h => exists_chart_pt hθB (v h ≫ j₀ TF.Y Z)
  choose lam hlam using fun h => hval _ (v h) (hv h) (k' h, k h) (fun s hs => ⟨hk' h hs, hk h hs⟩)
  have hc : ∀ h, H0.val (v h ≫ j₀ TF.Y Z) (k' h) le_top (hk' h) (H0.ofSec (s₀ TF.Y Z) ⊤ θ) ≠ 0 := fun h =>
    val_ofSec_ne_zero _ θ _ _ _ fun s => hθ ▸ ⟨v h s, rfl⟩
  have hvρ : ∀ h, v h = v₁ ≫ (ρ ⟨h.1, hmem _ h.1.2 y hyZ h.2⟩).asIso.hom := fun h => by
    rw [← cancel_mono (i₀ TF.Y Z), hv, Category.assoc, hρ.2 _ ℂ y v₁ hv₁]; rfl
  have h1 : LiesOn Z (move Y.d.Xo₂ Y.d.c₂ ((1 : S) : LevelAut (T.Q.Dw j) Y.d.l₂)⁻¹ y) := by
    rw [OneMemClass.coe_one, inv_one, LevDesc.move_one hpq hA']; exact hyZ
  have key := GlobalTheory.T.sections_separate_quotient_generic_fibre_descends hP2.q15 hQ.nef hP2.q16 Y.d.c₂.F (algebraMap _ ℂ) (X₀ TF.Y Z) X' W (V₀ TF.Y Z) (s₀ TF.Y Z) _ φ q sW
    (j₀ TF.Y Z) ℓ hpr hgc hdim n2 n8 n10 n11 n7 inferInstance n3 n4 K δ N' B hδ hN' hB N hN m eN
    (nef δ hδ _ gapGe_hodgeWt eδ) (_root_.GlobalTheory.T.hodgeLineBundle_bigness_on_shimuraVariety hP2 hG hQ hSg hKS _ _ _ _ _ _ TF Z hp hq hF δ hδ eδ) nefN' (by omega) eB _ v
    (fun h h' e => ?_) (fun h => ?_) (fun h h' => ?_) ⟨⟨1, h1⟩, fun s => hgen _ ?_⟩ k hk
    (fun h => a h * (lam h * H0.val (v h ≫ j₀ TF.Y Z) (k' h) le_top (hk' h) (H0.ofSec (s₀ TF.Y Z) ⊤ θ))) fun u => ?_
  · funext h
    exact (mul_eq_zero.1 (congrFun key h)).resolve_right (mul_ne_zero (lam h).ne_zero (hc h))
  · have e' := (hv h').symm.trans (e ▸ hv h)
    have e₂ : move Y.d.Xo₂ Y.d.c₂ (h'.1 : LevelAut (T.Q.Dw j) Y.d.l₂)⁻¹ y =
        move Y.d.Xo₂ Y.d.c₂ ((h.1 * h'.1⁻¹ : S) : LevelAut (T.Q.Dw j) Y.d.l₂)
          (move Y.d.Xo₂ Y.d.c₂ (h.1 : LevelAut (T.Q.Dw j) Y.d.l₂)⁻¹ y) := by
      rw [← LevDesc.move_mul hpq hA']; simp
    rw [e₂] at e'
    have := GlobalTheory.T.levelAutomorphism_unipotent_fixes_complexPoint_eq_one _ _ _ _ _ _ hpq hA I g hI hM _ (hS _ (h.1 * h'.1⁻¹).2) _ e'
    exact Subtype.ext (mul_inv_eq_one.1 (Subtype.ext this))
  · have e₁ : TF.Y.j ≫ TF.Y.s = pullback.snd _ _ := by
      rw [Model.j, Category.assoc, pullback.condition, ← Category.assoc, TF.Y.jQ_over]
      exact (congrArg (_ ≫ ·) (Spec.map_id _)).trans (Category.comp_id _)
    rw [← Category.assoc (j₀ _ _), j₀_ι, Category.assoc, e₁, ← Category.assoc, hv]
    exact pullback.lift_snd _ _ _
  · rw [hvρ h, hvρ h', Category.assoc, Category.assoc, reassoc_of% n5, reassoc_of% n5, n6.comp_eq, n6.comp_eq]
  · change (v ⟨1, h1⟩ ≫ i₀ TF.Y Z) s = _
    rw [hv]
    simp only [OneMemClass.coe_one, inv_one, LevDesc.move_one hpq hA']
    exact hy s
  · let P := tensChart hθB hKB
    have hu := ha _ (hΦ (P.mul (H0.ofSec (s₀ TF.Y Z) ⊤ θ) u) fun x hx => ?_)
    · rw [← hu]
      refine Finset.sum_congr rfl fun h _ => ?_
      rw [hlam, mul_assoc, mul_assoc]
      exact congrArg (fun x => a h * (lam h * x)) (P.val_mul _ _ (k' h, k h) _ le_top (hk' h) (hk h) _).symm
    · obtain ⟨τ, ha', hb', hc'⟩ := P.cover x
      have hu := (isUnit_ger_iff _ hc').2 hx
      rw [ger_toSec, P.germ_mul _ _ τ x _ ha' hb' hc', H0.germ_ofSec] at hu
      exact hθ ▸ (isUnit_ger_iff θ ha').1 (isUnit_of_mul_isUnit_left hu)
end GlobalTheory.OrbitSep
namespace GlobalTheory.OrbitSep
open Formalism.MainNotions Formalism.L2.Theta GlobalTheory.DegVal GlobalTheory.DegCmp GlobalTheory.BadCount
theorem exists_cusp_regular_level_determinant : _root_.GlobalTheory.CovTop.PublishedHodgeBundleTheorems → GlobalTheory.Published.GrothendieckDeformation → GlobalTheory.HSCore.Quoted → GlobalTheory.Published.SiegelToroidalIntegral → GlobalTheory.Published.ToroidalForFanKS → GlobalTheory.Published.SemiAbelianLieSeminegative → ∀ (D : D7) (T : CoreJ D), LawsJ T → ∀ j : ℕ, 1 ≤ (T.Q.Dw j).p → 1 ≤ (T.Q.Dw j).q → 2 < Module.finrank ℚ D.host.E / 2 → InR D j → ∀ (Y : Deep T.toCore j) (e : ℕ) (o : ℝ), Y.Good e o → 4 ≤ e → (∀ k, D.R.r + 1 < D.host.g k) → ∀ (fr : TypeFrame (T.Q.Dw j) Y.d.l₂) (S : Subgroup (LevelAut (T.Q.Dw j) Y.d.l₂)), (S = grpHR fr ∨ ∃ k, S = grpGHR fr k) → ∃ u ∈ Y.V (wtOf (T.Q.Dw j) (cZero D j • hodgeWt (T.Q.Dw j)) 0), ∀ f ∈ secRing Y.d.Xo₂ Y.d.c₂, levDet Y.d.Xo₂ Y.d.c₂ S u * f = 0 → f = 0 := by
  classical
  intro hP2 hG hQ hSg hKS hLie D T hT j hp hq hf hj Y e o hY _ hg fr S hS
  have hA : Y.d.l₂.A = 1 := hY.lev.2
  have hA' : Y.d.l₂.A.Coprime Y.d.l₂.M := hA ▸ Nat.coprime_one_left _
  have hpq : 1 ≤ (T.Q.Dw j).p + (T.Q.Dw j).q := by omega
  have hdat := hT.pins.2.2.2 j hj
  have hr : (T.Q.Dw j).p + (T.Q.Dw j).q = D.R.r := by
    rw [hdat.1, hdat.2.1]; exact Formalism.L2.Geo.sigW_sum D hj.1 hj.2
  have hM : Y.d.l₂.M = D.host.g 0 * D.host.g 1 * Y.d.pd := by rw [hY.lev.1.2.1, hT.pins.2.1.1]
  obtain ⟨I, g, hI, hMb, hU⟩ := _root_.GlobalTheory.OrbitSep.exists_neatPrime_unipAt D _ (T.Q.Dw j) Y.d.l₂ ⟨_, hM⟩ (hr ▸ hg) fr S hS
  have hs : (T.Q.Dw j).p + (T.Q.Dw j).q + ((T.Q.Dw j).dim + 1).choose 2 + 1 ≤ cZeroN D j := by
    have := (cZeroN_isLeast D j).1.2.1
    rw [hr, Datum.dim, GlobalTheory.FlagDim.finrank_host_div_two, hdat.1, hdat.2.1]
    omega
  choose y hyZ hy using _root_.GlobalTheory.OrbitSep.separate_orbits_by_cusp hP2 hG hQ hSg hKS hLie Y hY hf hp hq S hI hMb hU _ hs
  have : Finite (Comp Y.d.Xo₂ Y.d.c₂) := CompFin.finite_comp _ _
  let G := wtOf (T.Q.Dw j) (cZero D j • hodgeWt (T.Q.Dw j)) 0
  let ev : Comp Y.d.Xo₂ Y.d.c₂ → Y.V G →ₗ[Y.d.c₂.F] (S → ℂ) := fun Z => LinearMap.pi fun h =>
    evalL (K := Y.d.c₂.F) (fun R _ _ => FrPt Y.d.Xo₂ Y.d.c₂ R) (fun φ y z => FrMap φ y z)
      (move Y.d.Xo₂ Y.d.c₂ (h : LevelAut (T.Q.Dw j) Y.d.l₂)⁻¹ (y Z)) ∘ₗ (Y.V G).subtype
  obtain ⟨u, hu⟩ := GlobalTheory.T.exists_vector_groupDeterminants_ne_zero Y.d.c₂.F (Y.V G) S _ ev
    (fun Z => {h : S // LiesOn Z (move Y.d.Xo₂ Y.d.c₂ (h : LevelAut (T.Q.Dw j) Y.d.l₂)⁻¹ (y Z))}) (fun _ h => h.1)
    (fun Z => (AllWt.suppOn Z).comap (Y.V G).subtype)
    (fun Z => ⟨⟨1, by rw [OneMemClass.coe_one, inv_one, LevDesc.move_one hpq hA']; exact hyZ Z⟩, rfl⟩)
    (fun Z v hv h hh => hv ℂ _ ((AllWt.liesOff_iff Z _).2 fun h' => hh ⟨⟨h, h'⟩, rfl⟩))
    (fun Z a ha => hy Z a fun u hu => ha ⟨u, hu.1⟩ hu.2)
  have hu' := AllWt.cuspW_le_secZ _ u.2
  refine ⟨u, u.2, _root_.GlobalTheory.SecRingNonZeroDiv.eq_zero_of_mul_eq_zero _ _ _ _ _ _ _ _ (LevDesc.levDet_mem_secZ hpq hA' hu') fun Z => ⟨y Z, hyZ Z, ?_⟩⟩
  have ht := GlobalTheory.FlagTan.fromTest_of_isLocalRing (y Z)
  let χ : Rul Y.d.Xo₂ Y.d.c₂ →+* ℂ :=
    { toFun := fun f => evR Y.d.Xo₂ Y.d.c₂ f (y Z)
      map_one' := evalAt_one _ _ _ ht
      map_mul' := fun f g => evalAt_mul _ _ f g _
      map_zero' := evalAt_zero _ _ _
      map_add' := fun f g => evalAt_add _ _ f g _ }
  have e₁ := χ.map_det (LevDesc.levMat Y.d.Xo₂ Y.d.c₂ S u)
  refine fun h0 => hu Z ?_
  rw [← h0]
  refine Eq.trans ?_ (e₁.symm.trans ?_)
  · congr 1
    ext h g
    exact (GlobalTheory.LevelKeeps.evR_transl hpq hA' _ hu' (y Z)).symm
  · change χ _ = χ _
    unfold levDet
    congr!
end GlobalTheory.OrbitSep
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
theorem _root_.GlobalTheory.T.orbits_separated_by_regular_cusp : _root_.GlobalTheory.CovTop.PublishedHodgeBundleTheorems → GlobalTheory.Published.GrothendieckDeformation → GlobalTheory.HSCore.Quoted → GlobalTheory.Published.SiegelToroidalIntegral → GlobalTheory.Published.ToroidalForFanKS → GlobalTheory.Published.SemiAbelianLieSeminegative → ∀ (D : D7) (T : CoreJ D), LawsJ T → ∀ j : ℕ, 1 ≤ (T.Q.Dw j).p → 1 ≤ (T.Q.Dw j).q → 2 < Module.finrank ℚ D.host.E / 2 → InR D j → ∀ (Y : Deep T.toCore j) (e : ℕ) (o : ℝ), Y.Good e o → 4 ≤ e → (∀ k, D.R.r + 1 < D.host.g k) → ∀ (fr : TypeFrame (T.Q.Dw j) Y.d.l₂) (S : Subgroup (LevelAut (T.Q.Dw j) Y.d.l₂)), (S = grpHR fr ∨ ∃ k, S = grpGHR fr k) → ∃ u ∈ Y.V (wtOf (T.Q.Dw j) (cZero D j • hodgeWt (T.Q.Dw j)) 0), ∀ f ∈ secRing Y.d.Xo₂ Y.d.c₂, levDet Y.d.Xo₂ Y.d.c₂ S u * f = 0 → f = 0 := by
  first | exact @_root_.GlobalTheory.OrbitSep.exists_cusp_regular_level_determinant | exact _root_.GlobalTheory.OrbitSep.exists_cusp_regular_level_determinant | (intros; apply _root_.GlobalTheory.OrbitSep.exists_cusp_regular_level_determinant <;> assumption)
end
end

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.HodgeBundleWeights.HermitianGeometricHypothesisHolds
section
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory Formalism.L2.Pj Formalism.BasicNotions
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.HermTools GlobalTheory.Adelic GlobalTheory.CompHS GlobalTheory.CovTop
open GlobalTheory.AllWt (Psi wtOf cuspOn latOn normOn petOn GoodOn GoodW bergOn framesOn)
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.FlagTan (dimFlag)
open GlobalTheory.HSApp
open GlobalTheory.Vanishing.H0
set_option maxHeartbeats 1000000 in
theorem GlobalTheory.HSApp.geometric_hypothesis_of_components : _root_.GlobalTheory.CovTop.Hypotheses'' → GlobalTheory.Published.GrothendieckDeformation → GlobalTheory.HSCore.Quoted → GlobalTheory.Published.NadelVanishingAndNonKltDivisor → GlobalTheory.Published.Principalisation → GlobalTheory.Published.SiegelToroidalIntegral → GlobalTheory.Published.ToroidalChartsForFan → GlobalTheory.Published.SemiAbelianLieSeminegative → ∀ (D : D7) (T : Core D) (j : ℕ) (Y : Deep T j) (e : ℕ) (o : ℝ), Y.Good e o → 2 < Module.finrank ℚ D.host.E / 2 → ∀ (Z : Comp Y.d.Xo₂ Y.d.c₂) (TF : TorFlag Y.d.Xo₂ Y.d.c₂) (P : WtPar (T.Q.Dw j)) (R : Choice TF.X Z Y.U P) (ω : CanId R.toModif) (h : Ready R ω (xiR D) (fun _ => D.sp.W j) Y.dict) (f₁ : CuspFrame Z Y.U (xiR D) (fun _ => D.sp.W j) Y.dict P.u₁) (f₂ : CuspFrame Z Y.U (xiR D) (fun _ => D.sp.W j) Y.dict P.u₂) (th : R.L.Sec) (k : Consts), ∀ Λ₀ : ℝ, WtBig P → RatGen TF.X Z Y.U P.u₁ → RatGen TF.X Z Y.U P.u₂ → BergLe Z Y.U (fun _ => D.sp.W j) Y.dict P.u₁ k.beta → 1 ≤ k.abelian₂ → (∀ q σ, ChowHt.frameNorm (f₁.A σ) (fun a => σ (f₁.w.col q a)) ≤ k.abelian₂) → 1 ≤ Λ₀ → (h.data f₁ f₂ th k).ShortFamily 0 Λ₀ → (h.data f₁ f₂ th k).ShortFamily (dimFlag (T.Q.Dw j)) k.LamD → (h.data f₁ f₂ th k).ShortFamily P.T k.LamT → GlobalTheory.HSShort.GeoHyp (h.data f₁ f₂ th k) Λ₀ := by
  intro hPr hGD hQ hNad hPrin hSi hFa hLie D T j Y e o hG hE Z TF P R ω h f₁ f₂ th k Λ₀ hW hR₁ hR₂ hB hL hLe h1 hS0 hSD hST
  have hNN := hQ.nef
  have hF := hG.geo
  have hA : IsNef Y.d.c₂.F (h.geo f₁ f₂ th k).LA ∧ IsBig Y.d.c₂.F (h.geo f₁ f₂ th k).LA := by
    apply _root_.GlobalTheory.T.hodge_bundle_isNef_isBig_of_weight <;> assumption
  obtain ⟨hnef, hbig⟩ := hA
  have hbir := GlobalTheory.HSApp.birational_of_ratGen TF.X Z Y.U P R ω _ _ _ h f₁ f₂ th k hR₁
  have hbir₂ := GlobalTheory.HSApp.geo_second_birational TF.X Z Y.U P R ω _ _ _ h f₁ f₂ th k hR₂
  obtain ⟨hms, hmb⟩ := _root_.GlobalTheory.HSApp.generated_weights_mul_stable_and_bounded hPr D T j Y e o hG hE Z TF P R ω h f₁ f₂ th k hB
  have hnb₂ : IsNef Y.d.c₂.F (h.data f₁ f₂ th k).L₂ ∧ IsBig Y.d.c₂.F (h.data f₁ f₂ th k).L₂ :=
    GlobalTheory.BirationalBig.isNef_and_isBig hQ _ (h.geo f₁ f₂ th k).second.toLinSys
    (h.geo f₁ f₂ th k).alg₂.variety (h.geo f₁ f₂ th k).alg₂.bpf hbir₂
  have hTC : IsTotallyComplex Y.d.c₂.F := ⟨fun v => by
    rw [← InfinitePlace.not_isReal_iff_isComplex, InfinitePlace.isReal_iff, ComplexEmbedding.isReal_iff]
    exact fun e => GlobalTheory.CompHt.conj_comp_ne (c := Y.d.c₂) v.embedding (RingHom.ext fun a => RingHom.congr_fun e a)⟩
  obtain ⟨hD, hT, -, -, hLam, -, hLD, hLT, -⟩ := Ready.data_numbers h f₁ f₂ th k
  refine ⟨hTC, ?_, ?_, ?_, ?_, ?_, hms, hmb, ?_, ?_, h1, hS0, ?_, ?_⟩
  · exact hbir
  · exact hnef
  · exact hbig
  · exact hnb₂.1
  · exact hnb₂.2
  · intro q σ
    rw [hLam]
    exact hLe q σ
  · rw [hLam]; exact hL
  · rw [hD, hLD]; exact hSD
  · rw [hT, hLT]; exact hST
end

section
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory Formalism.L2.Pj Formalism.BasicNotions
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.HermTools GlobalTheory.Adelic GlobalTheory.CompHS GlobalTheory.CovTop
open GlobalTheory.AllWt (Psi wtOf cuspOn latOn normOn petOn GoodOn GoodW bergOn framesOn)
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.FlagTan (dimFlag)
open GlobalTheory.HSApp
open GlobalTheory.Vanishing.H0
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hermitian_geometric_hypothesis_holds : _root_.GlobalTheory.CovTop.Hypotheses'' → GlobalTheory.Published.GrothendieckDeformation → GlobalTheory.HSCore.Quoted → GlobalTheory.Published.NadelVanishingAndNonKltDivisor → GlobalTheory.Published.Principalisation → GlobalTheory.Published.SiegelToroidalIntegral → GlobalTheory.Published.ToroidalChartsForFan → GlobalTheory.Published.SemiAbelianLieSeminegative → ∀ (D : D7) (T : Core D) (j : ℕ) (Y : Deep T j) (e : ℕ) (o : ℝ), Y.Good e o → 2 < Module.finrank ℚ D.host.E / 2 → ∀ (Z : Comp Y.d.Xo₂ Y.d.c₂) (TF : TorFlag Y.d.Xo₂ Y.d.c₂) (P : WtPar (T.Q.Dw j)) (R : Choice TF.X Z Y.U P) (ω : CanId R.toModif) (h : Ready R ω (xiR D) (fun _ => D.sp.W j) Y.dict) (f₁ : CuspFrame Z Y.U (xiR D) (fun _ => D.sp.W j) Y.dict P.u₁) (f₂ : CuspFrame Z Y.U (xiR D) (fun _ => D.sp.W j) Y.dict P.u₂) (th : R.L.Sec) (k : Consts), ∀ Λ₀ : ℝ, WtBig P → RatGen TF.X Z Y.U P.u₁ → RatGen TF.X Z Y.U P.u₂ → BergLe Z Y.U (fun _ => D.sp.W j) Y.dict P.u₁ k.beta → 1 ≤ k.abelian₂ → (∀ q σ, ChowHt.frameNorm (f₁.A σ) (fun a => σ (f₁.w.col q a)) ≤ k.abelian₂) → 1 ≤ Λ₀ → (h.data f₁ f₂ th k).ShortFamily 0 Λ₀ → (h.data f₁ f₂ th k).ShortFamily (dimFlag (T.Q.Dw j)) k.LamD → (h.data f₁ f₂ th k).ShortFamily P.T k.LamT → GlobalTheory.HSShort.GeoHyp (h.data f₁ f₂ th k) Λ₀ := by
  first | exact @_root_.GlobalTheory.HSApp.geometric_hypothesis_of_components | exact _root_.GlobalTheory.HSApp.geometric_hypothesis_of_components | (intros; apply _root_.GlobalTheory.HSApp.geometric_hypothesis_of_components <;> assumption)
end
end

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.HodgeBundleWeights.LogCanonicalCriterionBoundary
section
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory Formalism.L2.Pj Formalism.BasicNotions
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.HermTools GlobalTheory.Adelic GlobalTheory.CompHS GlobalTheory.CovTop
open GlobalTheory.AllWt (Psi wtOf cuspOn latOn normOn petOn GoodOn GoodW bergOn framesOn)
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.FlagTan (dimFlag)
open GlobalTheory.HSApp
set_option autoImplicit false
noncomputable section
namespace GlobalTheory.LogCanon
theorem log_canonical_pair_iff : _root_.GlobalTheory.CovTop.Hypotheses'' → GlobalTheory.Published.GrothendieckDeformation → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (TF : TorFlag Xo c) (Z : Comp Xo c), FnAlgClosed (Xo := Xo) (c := c) → ∀ (M : Modif (str₀ TF.X Z) (U₀ TF.X Z) (dimFlag Dw)) (ω : CanId M) (b s : AllWt.Weight Dw) (hs : FlagTan.kap Dw + b = s) (m : H0 (str₀ TF.X Z) (L₀ TF.X Z s) (U₀ TF.X Z)), (∃ g ∈ vanBd TF.X Z s, H0.restr le_top g = m) ↔ ∃ g : H0 M.str (tens M.K.bundle ((L₀ TF.X Z b).pull M.σ)) ⊤, H0.restr le_top g = (((common₀ TF.X Z).pull M.σ).canChart M.K.isLB hs).mul ω.ω (M.pullOff m) := by
  intro hP hG E _ _ _ H Dw l Xo c TF Z hF M ω b s hs m
  have hV : IsVariety₀ TF.X Z := GlobalTheory.T.flagSpace_component_smooth_projective_connected E H Dw l Xo c TF Z hF
  by_cases hpq : 1 ≤ Dw.p + Dw.q
  · have hKS : (∀ (K : Type) [Field K] [Algebra c.F K] (y : FrPt Xo c K), GlobalTheory.FlagTan.KSIso (GlobalTheory.FlagTan.psiSet H) y) := fun K _ _ y => _root_.GlobalTheory.T.flag_tangent_kodaira_spencer_iso hP hG E H Dw l Xo c K y hpq
    obtain ⟨ω₀⟩ := _root_.GlobalTheory.CompHS.canId_nonempty hP.p5 E H Dw l Xo c TF.Y TF.X Z (Modif.refl hV.1 hV.2.1 (dense_U₀ TF.X Z)) hKS
    exact (_root_.GlobalTheory.T.logCanonical_divisor_refl hP hG E H Dw l Xo c TF Z hF hKS hV ω₀ b s hs m).trans (_root_.GlobalTheory.T.canonicalExtension_birational_invariance hP hG E H Dw l Xo c TF Z hF hKS hV ω₀ M ω b s hs m)
  · have h0 := dimFlag_eq_zero Dw hpq
    have hU : U₀ TF.X Z = ⊤ := _root_.GlobalTheory.dense_open_eq_top_of_smoothOfRelativeDimension_zero c.F _ (str₀ TF.X Z) (h0 ▸ hV.1) _ (dense_U₀ TF.X Z)
    have hall : ∀ y, y ∈ U₀ TF.X Z := fun y => hU.symm ▸ (Set.mem_univ y : y ∈ ((⊤ : (Y₀ TF.X Z).Opens) : Set _))
    have hoff : M.off = ⊤ := eq_top_iff.2 fun x _ => M.off_eq.ge (hall _)
    refine iff_of_true ?_ (restr_top_surj hoff _)
    obtain ⟨g, hg⟩ := restr_top_surj hU m
    refine ⟨g, fun y hy => (hy (hall y)).elim, hg⟩
end GlobalTheory.LogCanon
end
end

section
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory Formalism.L2.Pj Formalism.BasicNotions
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.HermTools GlobalTheory.Adelic GlobalTheory.CompHS GlobalTheory.CovTop
open GlobalTheory.AllWt (Psi wtOf cuspOn latOn normOn petOn GoodOn GoodW bergOn framesOn)
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.FlagTan (dimFlag)
open GlobalTheory.HSApp
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.log_canonical_criterion_boundary : _root_.GlobalTheory.CovTop.Hypotheses'' → GlobalTheory.Published.GrothendieckDeformation → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (TF : TorFlag Xo c) (Z : Comp Xo c), FnAlgClosed (Xo := Xo) (c := c) → ∀ (M : Modif (str₀ TF.X Z) (U₀ TF.X Z) (dimFlag Dw)) (ω : CanId M) (b s : AllWt.Weight Dw) (hs : FlagTan.kap Dw + b = s) (m : H0 (str₀ TF.X Z) (L₀ TF.X Z s) (U₀ TF.X Z)), (∃ g ∈ vanBd TF.X Z s, H0.restr le_top g = m) ↔ ∃ g : H0 M.str (tens M.K.bundle ((L₀ TF.X Z b).pull M.σ)) ⊤, H0.restr le_top g = (((common₀ TF.X Z).pull M.σ).canChart M.K.isLB hs).mul ω.ω (M.pullOff m) := by
  first | exact @_root_.GlobalTheory.LogCanon.log_canonical_pair_iff | exact _root_.GlobalTheory.LogCanon.log_canonical_pair_iff | (intros; apply _root_.GlobalTheory.LogCanon.log_canonical_pair_iff <;> assumption)
end
end

