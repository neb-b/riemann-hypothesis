module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsDatNeZero
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0064
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0362
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0006
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.AbelianHodgeDeRham
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2411
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2531
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2685
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1504
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1511
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0460
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2634
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2612
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2679
public import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.FinrankCechLBHomologyExtProd
public import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.Bundle0027
public import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.Bundle0028
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFinFreeAwayOfFinitePresentation
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.IsProjectiveOverRingByChartsAbelianVariety
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0108
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0097
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0004
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1139
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1170
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1101
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.FinrankRiemannRochNsmulHyperplane
public import Development.AbelianVarietyTheory.Definitions.QuasicoherentCohomology.FiniteCohPushforwardIffOfIsClosedImmersion
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsIsClosedImmersionGenericPoint
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0014
public import Development.AbelianVarietyTheory.Definitions.Divisors.AnalyticOnNhdFinChartIff
public import ReciprocityTheory.AnalyticForms.PotentialTheory.Bundle0003
public import ReciprocityTheory.AnalyticForms.PotentialTheory.Bundle0005
public import ReciprocityTheory.AnalyticForms.PotentialTheory.Bundle0006
public import ReciprocityTheory.AnalyticForms.PotentialTheory.Bundle0007
public import ReciprocityTheory.AnalyticForms.PotentialTheory.Bundle0008
public import ReciprocityTheory.AnalyticForms.PotentialTheory.Stokes
public import ReciprocityTheory.AnalyticForms.PotentialTheory.SNCAtlas
public import ReciprocityTheory.AnalyticForms.PotentialTheory.Bundle0002
public import ReciprocityTheory.AnalyticForms.PlurisubharmonicFunctions.Bundle0001
public import ReciprocityTheory.AnalyticForms.PotentialTheory.PLCurveA
public import ReciprocityTheory.AnalyticForms.PotentialTheory.PLLocalStatement
public import ReciprocityTheory.AnalyticForms.PotentialTheory.Pullback
public import ReciprocityTheory.AnalyticForms.PotentialTheory.AtlasIndep
public import ReciprocityTheory.AnalyticForms.PotentialTheory.DegreeInt
public import ReciprocityTheory.AnalyticForms.PotentialTheory.ContDiffFubiniStudyRatioCompChart0
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2680
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0015
public import Development.AbelianVarietyTheory.Definitions.Divisors.FormalCoboundarySmul
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2178
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0069
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0004
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2668
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2699
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0068
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2499
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2636
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2656
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2681
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2682

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CanonicalIsoHodgeFiltrationEqRangeInvariantForms
section
open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct WithConv
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Sp spMap epsR IsTangent IsGrpPullback)
open ReciprocityTheory.ChartRestriction.G.Semi (IsAbelianScheme LB RigLB CubicalStr Theta thφ thε thK x3)
open GlobalTheory GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.PDiv GlobalTheory.PtExt
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.PtExt

theorem map_F1prim_eq_range_rigOfOmega (p : ℕ) [Fact p.Prime] (R : Type) [CommRing R] (N : ℕ)
    (hN : (p : R) ^ N = 0) (A : Over (Sp R)) [GrpObj A] (hA : IsAbelianScheme A)
    (G : PDivGroup p R) (t : G.TorsionTower A) (L : primDR A →ₗ[R] ((G.cocycles × G.omega) ⧸ _root_.LinearMap.range (G.cob.prod (_root_.LinearMap.codRestrict G.omegaSub ((_root_.LinearMap.piMap fun i => _root_.GlobalTheory.AugCot.d (_root_.Bialgebra.counitAlgHom _ (G.A i))).domRestrict G.funs) (fun b n => (_root_.GlobalTheory.PDiv.cotMap_d _ _).trans (_root_.congrArg _ (b.2 n)))))))
    (hL : Function.Surjective L) (hc : ∀ c, IsCan t c (L c)) :
    (PrimitiveSubmodule A).map L = LinearMap.range G.rigOfOmega := by
  obtain ⟨ψ, hψ⟩ := GlobalTheory.T.exists_hodgeFiltration_to_pDivOmega_linearMap p R N hN A hA G t
  apply le_antisymm
  · rintro _ ⟨c, hcF, rfl⟩
    refine ⟨ψ ⟨c, hcF⟩, ?_⟩
    exact GlobalTheory.PtExt.isCan_unique R A p G t c hA _ _ (hψ ⟨c, hcF⟩) (hc c)
  · rintro _ ⟨w, rfl⟩
    obtain ⟨c, hcw⟩ := hL (G.rigOfOmega w)
    refine ⟨c, GlobalTheory.T.mem_primitiveSubmodule_of_isCan_of_rigToExt_eq_zero p R N hN A hA G t c (L c) (hc c) ?_, hcw⟩
    rw [hcw]
    exact G.exact_rigOfOmega_rigToExt.apply_apply_eq_zero w

end GlobalTheory.PtExt
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CechNonvanishingInvMixPairKunnethIsogeny
section
set_option autoImplicit false

noncomputable section

section Lemmas
open CategoryTheory MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AmpleGen
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.AmpleGen


open GlobalTheory.CechPic in
theorem cls_tw_one {X : Scheme.{0}} {M H : LB X} (hM : M.IsLB) (hH : H.IsLB) :
    cls (GlobalTheory.AbLaw.tw M H 1) (GlobalTheory.AbLaw.isLB_tw hM hH 1) = cls M hM + cls H hH := by
  refine (cls_div (A := M) (B := GlobalTheory.AbLaw.pw H (-1)) hM (GlobalTheory.AbLaw.isLB_pw hH _) (GlobalTheory.AbLaw.isLB_tw hM hH 1)).trans ?_
  rw [GlobalTheory.AmpleStabFinite.cls_pw hH]
  simp


open GlobalTheory.CechPic in
theorem cls_mix_pull {K : Type} [Field K] (A : Over (Sp K)) [GrpObj A] {L : LB A.left} (hL : L.IsLB)
    {T : Over (Sp K)} (z : T ⟶ A) (a b : ℤ) :
    cls ((mix A L a b).pull z.left) (LB.isLB_pull (LB.isLB_linComb hL _ _) _) =
      a • pull z.left (cls L hL) + b • pull (z⁻¹).left (cls L hL) := by
  refine (cls_pull (L := LB.LinComb L ![𝟙 A.left, (GrpObj.inv : A ⟶ A).left] ![a, b])
    (LB.isLB_linComb hL _ _) _ _).trans ?_
  rw [cls_linComb hL, Fin.sum_univ_two]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, map_add (f := _), map_zsmul, pull_id, ← pull_comp,
    ← Over.comp_left, Hom.inv_def]

end GlobalTheory.AmpleGen
end Lemmas

section RowLatticeBoundForBasis
open CategoryTheory MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AmpleGen
attribute [local instance] Over.cartesianMonoidalCategory
namespace GlobalTheory.AmpleGen

open GlobalTheory.CechPic in
theorem lbIso_pull_psiMap {K : Type} [Field K] (A : Over (Sp K)) [GrpObj A] (hA : IsAbelianScheme A)
    (a₁ b₁ a₂ b₂ : ℤ) (hs : a₁ * b₁ + a₂ * b₂ = 0) {L : LB A.left} (hL : L.IsLB) (a b : ℤ) :
    LBIso ((GlobalTheory.AbLaw.tw ((mix A L a b).pull (fst A A).left) ((mix A L a b).pull (snd A A).left) 1).pull
        (psiMap A a₁ b₁ a₂ b₂).left)
      (GlobalTheory.AbLaw.tw ((mix A L (a * tri a₁ + b * tri (-a₁) + a * tri a₂ + b * tri (-a₂))
                   (a * tri (-a₁) + b * tri a₁ + a * tri (-a₂) + b * tri a₂)).pull (fst A A).left)
        ((mix A L (a * tri b₁ + b * tri (-b₁) + a * tri b₂ + b * tri (-b₂))
          (a * tri (-b₁) + b * tri b₁ + a * tri (-b₂) + b * tri b₂)).pull (snd A A).left) 1) := by
  haveI := hA.comm
  have hP' : ∀ a b : ℤ, (mix A L a b).IsLB := fun _ _ => LB.isLB_linComb hL _ _
  have h₁ := GlobalTheory.AbLaw.isLB_tw (LB.isLB_pull (hP' a b) (fst A A).left) (LB.isLB_pull (hP' a b) (snd A A).left) 1
  refine (cls_eq_iff (LB.isLB_pull h₁ _) (GlobalTheory.AbLaw.isLB_tw (LB.isLB_pull (hP' _ _) _)
    (LB.isLB_pull (hP' _ _) _) 1)).1 ?_
  rw [cls_pull h₁, cls_tw_one, cls_tw_one, cls_mix_pull A hL, cls_mix_pull A hL, cls_mix_pull A hL,
    cls_mix_pull A hL]
  simp only [map_add (f := _), map_zsmul, ← pull_comp, ← Over.comp_left, GrpObj.comp_inv, psiMap, lift_fst, lift_snd]
  set c := cls L hL
  set x := fst A A
  set y := snd A A
  have e₁ := GlobalTheory.T.cechPicardPullback_zpow_mul_mixed_split K A hA L hL _ x y a₁ b₁ a b
  have e₂ := GlobalTheory.T.cechPicardPullback_zpow_mul_mixed_split K A hA L hL _ x y a₂ b₂ a b
  have f (z : A ⊗ A ⟶ A) (n : ℤ) := _root_.GlobalTheory.PowPull.pull_zpow K A hA L hL _ z n
  have g (z : A ⊗ A ⟶ A) (n : ℤ) : pull ((z ^ n)⁻¹).left c = tri (-n) • pull z.left c + tri n • pull (z⁻¹).left c := by
    rw [← zpow_neg, f, neg_neg]
  rw [e₁, e₂, f x a₁, g x a₁, f x a₂, g x a₂, f y b₁, g y b₁, f y b₂, g y b₂]
  have hl : ((a + b) * (a₁ * b₁)) • lam c x y + ((a + b) * (a₂ * b₂)) • lam c x y = 0 := by
    rw [← add_smul, ← mul_add, hs, mul_zero, zero_smul]
  linear_combination (norm := module) hl
  all_goals exact LB.isLB_pull (hP' _ _) _
end GlobalTheory.AmpleGen
end RowLatticeBoundForBasis

section MainAux
open CategoryTheory MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AmpleGen GlobalTheory.AbLaw
attribute [local instance] Over.cartesianMonoidalCategory
namespace GlobalTheory.AmpleGen

theorem finrank_pos_of_not_exactAt {K : Type} [Field K] {X : Scheme.{0}} {f : X ⟶ Spec (CommRingCat.of K)}
    {M : LB X} {κ : Type} [LinearOrder κ] {D : κ → X.Opens} {n : ℕ}
    [Module.Finite K ((cechLB f M D).homology n)] (h : ¬ (cechLB f M D).ExactAt n) :
    0 < Module.finrank K ((cechLB f M D).homology n) := by
  have : Nontrivial ((cechLB f M D).homology n) := by
    by_contra hn
    rw [not_nontrivial_iff_subsingleton] at hn
    exact h ((HomologicalComplex.exactAt_iff_isZero_homology _ _).2 (ModuleCat.isZero_of_subsingleton _))
  exact Module.finrank_pos

theorem exists_nonvanishing_invMix_pair_isogeny (K : Type) [Field K] [IsAlgClosed K] (A : Over (Sp K)) [GrpObj A] (hA : IsAbelianScheme A)
    (a₁ b₁ a₂ b₂ : ℤ) (hs : a₁ * b₁ + a₂ * b₂ = 0) (hd : ((a₁ * b₂ - b₁ * a₂ : ℤ) : K) ≠ 0)
    (L : LB A.left) (hL : L.IsLB) (a b j : ℕ) (hN : NV A (mix A L a b) j) :
    ∃ j₁ j₂ : ℕ, j₁ + j₂ = 2 * j ∧
      NV A (mix A L (a * tri a₁ + b * tri (-a₁) + a * tri a₂ + b * tri (-a₂))
        (a * tri (-a₁) + b * tri a₁ + a * tri (-a₂) + b * tri a₂)) j₁ ∧
      NV A (mix A L (a * tri b₁ + b * tri (-b₁) + a * tri b₂ + b * tri (-b₂))
        (a * tri (-b₁) + b * tri b₁ + a * tri (-b₂) + b * tri b₂)) j₂ := by
  haveI := hA.comm
  haveI := hA.proper
  obtain ⟨κ, _, _, W, hW, hWc, hne⟩ := hN
  have hP' : ∀ a b : ℤ, (mix A L a b).IsLB := fun _ _ => LB.isLB_linComb hL _ _
  have hsep : IsSeparated A.hom := inferInstance
  have hproj := GlobalTheory.AbelianProjective.isProjBy_of_isAbelianScheme K A hA
  have fin : ∀ M : LB A.left, M.IsLB → ∀ n, Module.Finite K ((cechLB A.hom M W).homology n) :=
    fun M hM => cechLB_homology_finite_of_affine_cover K _ A.hom M κ W hM hsep hproj hW hWc
  have h₀ : IsPullback (fst A A).left (snd A A).left A.hom A.hom := IsPullback.of_hasPullback A.hom A.hom
  have hAA := ReciprocityTheory.ChartRestriction.G.Geo.Tor.AbelianSchemeGerms.isAbelianScheme_tensor A A hA hA
  haveI := hAA.comm
  haveI := hAA.proper
  have hsepAA : IsSeparated (A ⊗ A).hom := inferInstance
  have hprojAA := GlobalTheory.AbelianProjective.isProjBy_of_isAbelianScheme K (A ⊗ A) hAA
  haveI : CompactSpace (A ⊗ A).left := QuasiCompact.compactSpace_of_compactSpace (A ⊗ A).hom
  obtain ⟨k, E, hE, hEc⟩ := GlobalTheory.PicZeroVan.exists_fin_affine_cover (A ⊗ A).left
  obtain ⟨hfin, hflat, hlfp, r, hr, hr0⟩ := _root_.GlobalTheory.AmpleGen.psiMap_finite_locallyFree K A hA a₁ b₁ a₂ b₂ hd
  set ψ := psiMap A a₁ b₁ a₂ b₂ with hψ
  set P := mix A L a b with hPdef
  have hP := hP' a b
  have hf₁ : (fst A A).left ≫ A.hom = (A ⊗ A).hom := Over.w (fst A A)
  have hfψ : ψ.left ≫ (A ⊗ A).hom = (A ⊗ A).hom := Over.w ψ

  have k₀ := finrank_cechLB_homology_extProd K _ _ _ A.hom A.hom (fst A A).left (snd A A).left P P h₀ hP hP
    hsep hsep κ W κ W (Fin k) E hW hWc hW hWc hE hEc (fin P hP) (fin P hP) (2 * j)
  have hpos : 0 < Module.finrank K ((cechLB A.hom P W).homology j) := by
    haveI := fin P hP j
    exact finrank_pos_of_not_exactAt hne
  have hM : ¬ (cechLB ((fst A A).left ≫ A.hom) (tw (P.pull (fst A A).left) (P.pull (snd A A).left) 1) E).ExactAt
      (2 * j) := by
    intro hex
    have hz : Module.finrank K ((cechLB ((fst A A).left ≫ A.hom)
        (tw (P.pull (fst A A).left) (P.pull (snd A A).left) 1) E).homology (2 * j)) = 0 := by
      have : Subsingleton ((cechLB ((fst A A).left ≫ A.hom)
          (tw (P.pull (fst A A).left) (P.pull (snd A A).left) 1) E).homology (2 * j)) :=
        ModuleCat.subsingleton_of_isZero ((HomologicalComplex.exactAt_iff_isZero_homology _ _).1 hex)
      exact Module.finrank_zero_of_subsingleton
    rw [k₀] at hz
    have := (Finset.sum_eq_zero_iff.1 hz) (j, j) (by simp [two_mul])
    exact (Nat.mul_pos hpos hpos).ne' this

  have hu : IsUnit ((r : ℕ) : Γ((A ⊗ A).left, ⊤)) := by
    have := (GlobalTheory.AbelianMulFin.isUnit_natCast_Sp (K := K) hr0).map (A ⊗ A).hom.appTop.hom
    rwa [map_natCast] at this
  rw [hf₁] at hM
  have hM' : ¬ (cechLB (ψ.left ≫ (A ⊗ A).hom)
      ((tw (P.pull (fst A A).left) (P.pull (snd A A).left) 1).pull ψ.left) (fun i => ψ.left ⁻¹ᵁ E i)).ExactAt
      (2 * j) := fun h => hM ((GlobalTheory.FinTrace.cechLB_retract_and_exactAt ψ.left (A ⊗ A).hom r hr hu _ E).2 _ h)
  rw [hfψ] at hM'
  set P₁ := mix A L (a * tri a₁ + b * tri (-a₁) + a * tri a₂ + b * tri (-a₂))
        (a * tri (-a₁) + b * tri a₁ + a * tri (-a₂) + b * tri a₂) with hP₁def
  set P₂ := mix A L (a * tri b₁ + b * tri (-b₁) + a * tri b₂ + b * tri (-b₂))
        (a * tri (-b₁) + b * tri b₁ + a * tri (-b₂) + b * tri b₂) with hP₂def
  have hP₁ : P₁.IsLB := hP' _ _
  obtain ⟨w, hw⟩ := lbIso_pull_psiMap A hA a₁ b₁ a₂ b₂ hs hL a b
  have hP₂ : P₂.IsLB := hP' _ _
  have hTw : (tw (P₁.pull (fst A A).left) (P₂.pull (snd A A).left) 1).IsLB :=
    isLB_tw (LB.isLB_pull hP₁ _) (LB.isLB_pull hP₂ _) 1
  have hN₂ : ¬ (cechLB (A ⊗ A).hom (tw (P₁.pull (fst A A).left) (P₂.pull (snd A A).left) 1)
      (fun i => ψ.left ⁻¹ᵁ E i)).ExactAt (2 * j) := fun h =>
    hM' (h.of_iso (cechLBCongr _ _ (LB.isLB_pull (isLB_tw (LB.isLB_pull hP _) (LB.isLB_pull hP _) 1) _)
      hTw w hw).symm)

  have hD : ∀ i, IsAffineOpen (ψ.left ⁻¹ᵁ E i) := fun i => (hE i).preimage ψ.left
  have hDc : ⨆ i, ψ.left ⁻¹ᵁ E i = ⊤ := by
    rw [← Scheme.Hom.preimage_iSup, hEc]; rfl
  have k₁ := finrank_cechLB_homology_extProd K _ _ _ A.hom A.hom (fst A A).left (snd A A).left P₁ P₂ h₀ hP₁ hP₂
    hsep hsep κ W κ W (Fin k) (fun i => ψ.left ⁻¹ᵁ E i) hW hWc hW hWc hD hDc (fin P₁ hP₁) (fin P₂ hP₂) (2 * j)
  rw [hf₁] at k₁
  haveI := cechLB_homology_finite_of_affine_cover K _ (A ⊗ A).hom _ (Fin k) (fun i => ψ.left ⁻¹ᵁ E i) hTw hsepAA
    hprojAA hD hDc (2 * j)
  have hpos₂ := finrank_pos_of_not_exactAt hN₂
  rw [k₁] at hpos₂
  obtain ⟨x, hx, hx0⟩ := Finset.exists_ne_zero_of_sum_ne_zero hpos₂.ne'
  have hx' : x.1 + x.2 = 2 * j := by simpa using hx
  refine ⟨x.1, x.2, hx', ⟨κ, inferInstance, inferInstance, W, hW, hWc, fun h => hx0 ?_⟩,
    ⟨κ, inferInstance, inferInstance, W, hW, hWc, fun h => hx0 ?_⟩⟩
  · haveI := fin P₁ hP₁ x.1
    have : Subsingleton ((cechLB A.hom P₁ W).homology x.1) :=
      ModuleCat.subsingleton_of_isZero ((HomologicalComplex.exactAt_iff_isZero_homology _ _).1 h)
    rw [Module.finrank_zero_of_subsingleton, zero_mul]
  · haveI := fin P₂ hP₂ x.2
    have : Subsingleton ((cechLB A.hom P₂ W).homology x.2) :=
      ModuleCat.subsingleton_of_isZero ((HomologicalComplex.exactAt_iff_isZero_homology _ _).1 h)
    rw [Module.finrank_zero_of_subsingleton (R := K) (M := (cechLB A.hom P₂ W).homology x.2), mul_zero]

end GlobalTheory.AmpleGen
end MainAux

section Target
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AmpleGen
open scoped CategoryTheory.Obj

theorem GlobalTheory.AmpleGen.nv_mix_pair_of_nv : ∀ (K : Type) [Field K] [IsAlgClosed K] (A : Over (Sp K)) [GrpObj A], IsAbelianScheme A → ∀ α β γ δ : ℤ, α * β + γ * δ = 0 → ((α * δ - β * γ : ℤ) : K) ≠ 0 → ∀ L : LB A.left, L.IsLB → ∀ a b j : ℕ, NV A (mix A L a b) j → ∃ j₁ j₂ : ℕ, j₁ + j₂ = 2 * j ∧ NV A (mix A L (a * tri α + b * tri (-α) + a * tri γ + b * tri (-γ)) (a * tri (-α) + b * tri α + a * tri (-γ) + b * tri γ)) j₁ ∧ NV A (mix A L (a * tri β + b * tri (-β) + a * tri δ + b * tri (-δ)) (a * tri (-β) + b * tri β + a * tri (-δ) + b * tri δ)) j₂ := by
  intro K _ _ A _ hA α β γ δ hs hd L hL a b j h
  exact exists_nonvanishing_invMix_pair_isogeny K A hA α β γ δ hs hd L hL a b j h

end Target
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ChernMassEqSelfIntersectionLineBundle
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Set Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open ReciprocityTheory.AnForm.M
open GlobalTheory GlobalTheory.Cartier GlobalTheory.CxPts GlobalTheory.Points GlobalTheory.CechPic GlobalTheory.ProjVar
set_option autoImplicit false

namespace GlobalTheory.MassDegree

theorem chernInt_eq_topSelf : ∀ (Y : Var ℂ) (L : LB Y.X) (φ : Weight Y.str (RingHom.id ℂ) L), φ.IsCInf → Weight.chernInt φ Y.dim Set.univ (fun _ => 1) = (topSelfIntersection ℂ L Y.dim : ℝ) := by
  intro Y L φ hφ
  let ψ : Weight Y.str (RingHom.id ℂ) ((ProjSpace.O1 ℂ Y.N).pull Y.ι) :=
    ((ProjSpace.hermitianTwistingSheaf ℂ Y.N).φ (RingHom.id ℂ)).pull Y.ι Y.ι_str
  have hψ : ψ.IsCInf := ((ProjSpace.hermitianTwistingSheaf ℂ Y.N).cInf (RingHom.id ℂ)).pull Y.ι Y.ι_str
  obtain ⟨P, hP0, hP⟩ := _root_.GlobalTheory.ChernPoly.chernInt_tens_pow_poly Y L _ φ ψ hφ hψ
  obtain ⟨Q, hQ0, hQ⟩ := GlobalTheory.SelfInterPoly.exists_polynomial_topSelf Y L _ φ.isLB ψ.isLB
  obtain ⟨m₀, hm₀⟩ := _root_.GlobalTheory.ProjVar.exists_generating_secs_tens_lbPow_O1 Y L φ.isLB
  have key : ∀ m : ℕ, m₀ ≤ m → P.eval (m : ℝ) = Q.eval (m : ℝ) := by
    intro m hm
    obtain ⟨n, u, hu⟩ := hm₀ m hm
    rw [← hP m, ← hQ m]
    exact _root_.GlobalTheory.chernInt_eq_topSelf_of_generated Y _ (φ.tens (ψ.pow m)) (hφ.tens (hψ.zpow m)) n u hu
  have hPQ : P = Q := by
    refine Polynomial.eq_of_infinite_eval_eq P Q ?_
    refine Set.Infinite.mono ?_ ((Set.Ici_infinite m₀).image Nat.cast_injective.injOn)
    rintro _ ⟨m, hm, rfl⟩
    exact key m hm
  rw [← hP0, ← hQ0, hPQ]

end GlobalTheory.MassDegree
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConnectedPDivGroupFormalLawCoordinatesStatement
section
open CategoryTheory TensorProduct MvPowerSeries GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup GlobalTheory.Katz
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.connectedPDivGroup_formalLaw_coordinates : ∀ (p : ℕ) (k : Type) [CommRing k] (d : ℕ) (G : PDivGroup p k) (c : Chart G d), (∃ μ, c.IsLawOf μ) ∧ ∀ (μ : Fin d → MvPowerSeries (Fin d ⊕ Fin d) k), c.IsLawOf μ → (∀ i, constantCoeff (μ i) = 0) ∧ ∀ n f, c.ev₂ n (subst μ f) = Coalgebra.comul (R := k) (c.ev n f) ∧ c.ev₂ n (cob1 μ f) = cobOne k (G.A n) (c.ev n f) := by
  first | exact @GlobalTheory.LawCoord.main | exact GlobalTheory.LawCoord.main | (intros; apply GlobalTheory.LawCoord.main <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContinuousHermSectionValueMulConjAndNormBounded
section
set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.VolBr GlobalTheory.HSAmp

namespace GlobalTheory.HSAmp

theorem continuous_val_mul_conj (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k) (P : Pair p)
    (a b : ℤ) (σ : k →+* ℂ) (f : X.functionField) (hf : f ∈ P.H a b) (g : X.functionField) (hg : g ∈ P.H a b) :
    Continuous fun y : CxPts p σ => val P a b σ y f * (starRingEnd ℂ) (val P a b σ y g) := by
  refine continuous_iff_continuousAt.2 fun y₀ => ?_
  set i := pick (P.L.φ σ).isLB y₀
  set j := pick (P.A.φ σ).isLB y₀
  have hi : y₀ ∈ ptsIn p σ (P.L.B.U i) := mem_pick _ y₀
  have hj : y₀ ∈ ptsIn p σ (P.A.B.U j) := mem_pick _ y₀
  have hW : IsOpen (ptsIn p σ (P.L.B.U i) ∩ ptsIn p σ (P.A.B.U j)) := (isOpen_ptsIn _).inter (isOpen_ptsIn _)
  have hWn := hW.mem_nhds ⟨hi, hj⟩
  have hrf : ContinuousAt (fun y : CxPts p σ => ratVal (P.loc a b f i j) y) y₀ :=
    (GlobalTheory.T.sectionLocalFunction_continuousOn_holomorphicChart k X p P a b σ f hf i j).1.continuousAt hWn
  have hrg : ContinuousAt (fun y : CxPts p σ => ratVal (P.loc a b g i j) y) y₀ :=
    (GlobalTheory.T.sectionLocalFunction_continuousOn_holomorphicChart k X p P a b σ g hg i j).1.continuousAt hWn
  have hφ : ContinuousAt ((P.L.φ σ).φ i) y₀ := CInfAt.continuousAt (P.L.cInf σ i y₀ hi)
  have hψ : ContinuousAt ((P.A.φ σ).φ j) y₀ := CInfAt.continuousAt (P.A.cInf σ j y₀ hj)
  have he : ContinuousAt (fun y : CxPts p σ =>
      ((Real.exp (-(a * (P.L.φ σ).φ i y + b * (P.A.φ σ).φ j y) / 2) : ℝ) : ℂ)) y₀ :=
    Complex.continuous_ofReal.continuousAt.comp (Real.continuous_exp.continuousAt.comp
      (((continuousAt_const.mul hφ).add (continuousAt_const.mul hψ)).neg.div_const 2))
  have hF : ContinuousAt (fun y : CxPts p σ =>
      ratVal (P.loc a b f i j) y * ((Real.exp (-(a * (P.L.φ σ).φ i y + b * (P.A.φ σ).φ j y) / 2) : ℝ) : ℂ) *
        (starRingEnd ℂ) (ratVal (P.loc a b g i j) y *
          ((Real.exp (-(a * (P.L.φ σ).φ i y + b * (P.A.φ σ).φ j y) / 2) : ℝ) : ℂ))) y₀ :=
    (hrf.mul he).mul (Complex.continuous_conj.continuousAt.comp (hrg.mul he))
  refine hF.congr ?_
  filter_upwards [hWn] with y hy
  obtain ⟨θ, hθ, hv⟩ := _root_.GlobalTheory.HSAmp.val_frame k X p P a b σ y i j hy.1 hy.2
  have h1 : θ * (starRingEnd ℂ) θ = 1 := by
    rw [Complex.mul_conj, Complex.normSq_eq_norm_sq, hθ]; simp
  rw [hv f hf, hv g hg]
  generalize ratVal (P.loc a b f i j) y * ((Real.exp (-(a * (P.L.φ σ).φ i y + b * (P.A.φ σ).φ j y) / 2) : ℝ) : ℂ) = A
  generalize ratVal (P.loc a b g i j) y * ((Real.exp (-(a * (P.L.φ σ).φ i y + b * (P.A.φ σ).φ j y) / 2) : ℝ) : ℂ) = B
  rw [map_mul]
  linear_combination (-(A * (starRingEnd ℂ) B)) * h1

theorem nu_eq_sqrt {k : Type} [CommRing k] {X : Scheme.{0}} [IsIntegral X] {p : X ⟶ Sp k} (P : Pair p)
    (a b : ℤ) (σ : k →+* ℂ) (y : CxPts p σ) (f : X.functionField) :
    P.nu a b σ y f = Real.sqrt ((val P a b σ y f * (starRingEnd ℂ) (val P a b σ y f)).re) := by
  rw [← norm_val, Complex.mul_conj, Complex.ofReal_re, Complex.normSq_eq_norm_sq, Real.sqrt_sq (norm_nonneg _)]

theorem continuous_val_and_bounded : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k) (D : ℕ),
    IsArithVar p D → ∀ (P : Pair p), ∀ (a b : ℤ),
      (∀ (σ : k →+* ℂ), ∀ f ∈ P.H a b, ∀ g ∈ P.H a b,
        Continuous fun y : CxPts p σ => val P a b σ y f * (starRingEnd ℂ) (val P a b σ y g)) ∧
      ∀ f ∈ P.H a b, (∀ σ, Continuous fun y : CxPts p σ => P.nu a b σ y f) ∧
        ∃ C : ℝ, ∀ (σ : k →+* ℂ) (y : CxPts p σ), P.nu a b σ y f ≤ C := by
  intro k _ X _ p D hX P a b
  refine ⟨fun σ f hf g hg => continuous_val_mul_conj k X p P a b σ f hf g hg, fun f hf => ?_⟩
  have hc : ∀ σ, Continuous fun y : CxPts p σ => P.nu a b σ y f := fun σ => by
    simp_rw [nu_eq_sqrt]
    exact Real.continuous_sqrt.comp (Complex.continuous_re.comp (continuous_val_mul_conj k X p P a b σ f hf f hf))
  refine ⟨hc, ?_⟩
  have hb : ∀ σ : k →+* ℂ, ∃ C : ℝ, ∀ y : CxPts p σ, P.nu a b σ y f ≤ C := fun σ => by
    haveI := hX.compactSpace σ
    obtain ⟨C, hC⟩ := (isCompact_range (hc σ)).bddAbove
    exact ⟨C, fun y => hC ⟨y, rfl⟩⟩
  choose C hC using hb
  haveI := hX.finite_emb
  obtain ⟨M, hM⟩ := (Set.finite_range C).bddAbove
  exact ⟨M, fun σ y => (hC σ y).trans (hM ⟨σ, rfl⟩)⟩

end GlobalTheory.HSAmp
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CurvaturePowerSumsDbarCohomologous
section
open CategoryTheory AlgebraicGeometry MvPolynomial MeasureTheory Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.L2DbarEstimates (V)
open GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.FlagBundle GlobalTheory.HermFrame GlobalTheory.GoodMetric GlobalTheory.CxForm GlobalTheory.LineForm GlobalTheory.ChernCalc
open scoped Matrix ContDiff ComplexOrder

namespace GlobalTheory.ChernCalc.PowCoh

variable {M : Type} [TopologicalSpace M] {n : ℕ} {A : HolAtlas M n} {r : Type} [Fintype r] [DecidableEq r]
  {G G' : M → M → Matrix r r ℂ}

theorem pair_symm (h : IsGramPair A G G') : IsGramPair A G' G :=
  ⟨fun y => (h.smooth y).symm, fun y => (h.trans y).mono fun _ ⟨T, K, K', hT, hK, hK', e⟩ =>
    ⟨T, K', K, hT, hK', hK, e.mono fun _ hw => hw.symm⟩⟩

theorem smooth_crd (h : IsGramPair A G G') (x : A.Pt) :
    MContDiffAt ∞ (fun u => G x.pt (x.ch.symm u)) x.crd ∧ IsUnit (G x.pt (x.ch.symm x.crd)).det := by
  refine ⟨((h.smooth x.pt).1.2 x.1.1 x.2).self_of_nhds, ?_⟩
  rw [x.ch.left_inv x.2]
  exact (h.smooth x.pt).1.1

theorem dbar_powFld (h : IsGramPair A G G') (k : ℕ) : A.dbar (fld A (powFld A G k)) = 0 := by
  funext x
  have h₁ := smooth_crd h x
  refine ((_root_.GlobalTheory.CxForm.dbarAt_local_calculus n x.crd).1 _ _ ((_root_.GlobalTheory.ChernCalc.loc_fields_near M n A r G G' h x k).mono fun _ hv => hv.1)).trans ?_
  exact (_root_.GlobalTheory.ChernCalc.powAt_transAt_smooth n r _ _ x.crd h₁.1 h₁.2 h₁.1 h₁.2 k).2.1

theorem dbar_transFld (h : IsGramPair A G G') (k : ℕ) :
    fld A (powFld A G k) - fld A (powFld A G' k) = A.dbar (transFld A G G' k) := by
  funext x
  have h₁ := smooth_crd h x
  have h₂ := smooth_crd (pair_symm h) x
  symm
  refine ((_root_.GlobalTheory.CxForm.dbarAt_local_calculus n x.crd).1 _ _ ((_root_.GlobalTheory.ChernCalc.loc_fields_near M n A r G G' h x k).mono fun _ hv => hv.2.2)).trans ?_
  exact GlobalTheory.T.dbar_chernTransgressionForm_eq_power_sum_diff n r _ _ x.crd h₁.1 h₁.2 h₂.1 h₂.2 k

theorem dbarCoh_powFld : ∀ (M : Type) [TopologicalSpace M] (n : ℕ) (A : HolAtlas M n) (r : Type) [Fintype r]
    [DecidableEq r] (G G' : M → M → Matrix r r ℂ), IsGramPair A G G' → ∀ k,
    DbarCoh A (powFld A G k) (powFld A G' k) := fun M _ n A r _ _ G G' h k =>
  ⟨(_root_.GlobalTheory.ChernCalc.PairForm.isForm_pow_trans M n A r G G' h k).1, (_root_.GlobalTheory.ChernCalc.PairForm.isForm_pow_trans M n A r G' G (pair_symm h) k).1, dbar_powFld h k,
    dbar_powFld (pair_symm h) k, _, (_root_.GlobalTheory.ChernCalc.PairForm.isForm_pow_trans M n A r G G' h k).2, dbar_transFld h k⟩

end GlobalTheory.ChernCalc.PowCoh
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DetReLePowMulDetReStatement
section
open Filter Topology MeasureTheory GlobalTheory.HSAmp
open scoped ComplexOrder Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.det_re_le_pow_mul_det_re_of_posDef : ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (A B : Matrix ι ι ℂ) (κ : ℝ), A.PosDef → B.PosDef → (∀ c : ι → ℂ, (star c ⬝ᵥ A *ᵥ c).re ≤ κ * (star c ⬝ᵥ B *ᵥ c).re) → A.det.re ≤ κ ^ Fintype.card ι * B.det.re := by
  first | exact @GlobalTheory.HSAmp.det_re_le_pow_mul_det_re | exact GlobalTheory.HSAmp.det_re_le_pow_mul_det_re | (intros; apply GlobalTheory.HSAmp.det_re_le_pow_mul_det_re <;> assumption)
end

