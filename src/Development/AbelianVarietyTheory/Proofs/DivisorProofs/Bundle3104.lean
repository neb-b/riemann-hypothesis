module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.NotCompactOfMEqOne
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0003
public import Development.AbelianVarietyTheory.Definitions.Divisors.Rosati
public import Development.AbelianVarietyTheory.Definitions.Divisors.ToRingActOpOfRingAct
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0389
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0019
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0791
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0012
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsAdditiveLiftIff
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2489
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3079
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3096
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3095
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0007
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1945
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3097
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2283
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2092
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0111
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ClsLinCombSingle
public import Development.AbelianVarietyTheory.Definitions.Divisors.TorsionTowersOfDivisibleGroup
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.Bundle0001
public import Development.AbelianVarietyTheory.Statements.EllipticCurveLevels.BaseChangeMapRingAct
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3090
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2770
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2215
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LiftLeftFst
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0023
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.IsAbelianSchemeAndExtendOfGenericHoms
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1421
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0688
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0478
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0169
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0006
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0063
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0044
public import Development.AbelianVarietyTheory.Definitions.Divisors.ToIThCapDegOfAddNsmulDivP
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsFrobGBaseChange
public import Formalism.SharpRestriction.Divisibility.Bundle0002
public import Development.AbelianVarietyTheory.Definitions.Divisors.PrismaticDieudonnePerfdIff
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsUniqueIsWeilChar
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0186
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.PrismaticDieudonnePerfd
public import ReciprocityTheory.DualLattices.Bundle0005
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0242
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0059
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0010
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0022
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0099
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0072
public import Development.AbelianVarietyTheory.Definitions.Divisors.HasTraitsOnOfHasTraitsP
public import ReciprocityTheory.AnalyticForms.RegularLocalRings.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3048
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2441
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0135
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3056
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3098
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3086
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3069
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0066
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsMonoFamNontrivial
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2070
public import Development.AbelianVarietyTheory.Definitions.Divisors.ThetaSetupStructureMapComp
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2184

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LineBundleProdIsoOfPowIsoBirigidified
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT
open GlobalTheory.ZM GlobalTheory.SiegelTor
open GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual
open scoped CategoryTheory.Obj CategoryTheory.MonObj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.BirigidRoot

variable {S : Scheme.{0}} {A : Over S} [GrpObj A]

theorem pow_comp_hom {Z H : Over S} [GrpObj H] (f : A ⟶ H) [IsMonHom f] (x : Z ⟶ A) (n : ℕ) :
    (x ^ n) ≫ f = (x ≫ f) ^ n := by
  induction n with
  | zero => rw [pow_zero, pow_zero, MonObj.one_comp]
  | succ n ih => rw [pow_succ, pow_succ, MonObj.mul_comp, ih]

theorem pull_eq_evc {P : LB (A ⊗ A).left} (hP : P.IsLB) {Y : Over S} (w : Y ⟶ A ⊗ A) :
    CechPic.pull w.left (cls P hP) = evc hP (w ≫ fst A A) (w ≫ snd A A) := by
  rw [evc, lift_comp_fst_snd]

theorem cube_rel (hA : IsAbelianScheme A) {P : LB (A ⊗ A).left} (hP : P.IsLB) {Y : Over S}
    (x y z : Y ⟶ A ⊗ A) :
    CechPic.pull (x * y * z).left (cls P hP) - CechPic.pull (x * y).left (cls P hP)
      - CechPic.pull (x * z).left (cls P hP) - CechPic.pull (y * z).left (cls P hP)
      + CechPic.pull x.left (cls P hP) + CechPic.pull y.left (cls P hP) + CechPic.pull z.left (cls P hP)
      - CechPic.pull (1 : Y ⟶ A ⊗ A).left (cls P hP) = 0 := by
  have hX := AbelianSchemeGerms.isAbelianScheme_tensor A A hA hA
  have t := GlobalTheory.CubeTop.cubeTheorem S (A ⊗ A) hX P hP Y x y z
  have z0 := (cls_linComb hP _ _ (LB.isLB_linComb hP _ _)).symm.trans
    ((cls_eq_zero_iff (LB.isLB_linComb hP _ _)).2 t)
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Matrix.cons_val_zero, Matrix.cons_val_succ,
    one_zsmul, neg_one_zsmul, add_zero] at z0
  rw [← z0]
  abel

theorem additive_of_birigid (hA : IsAbelianScheme A) {P : LB (A ⊗ A).left} (hP : P.IsLB)
    (h₁ : Triv (ev P (1 : A ⟶ A) (𝟙 A))) (h₂ : Triv (ev P (𝟙 A) (1 : A ⟶ A))) :
    IsAdditive P ∧ IsAdditive (swap P) := by
  refine ⟨(isAdditive_iff hP).2 fun Y a a' t ↦ ?_, (BirigidLift.isAdditive_swap_iff hP).2 fun Y a t t' ↦ ?_⟩
  · have e := cube_rel hA hP (lift a 1) (lift a' 1) (lift 1 t)
    simp only [pull_eq_evc hP, MonObj.mul_comp, lift_fst, lift_snd, MonObj.one_comp, _root_.mul_one,
      _root_.one_mul, evc_one_right hP h₂, evc_one_left hP h₁] at e
    rw [← sub_eq_zero, ← e]
    abel
  · have e := cube_rel hA hP (lift a 1) (lift 1 t) (lift 1 t')
    simp only [pull_eq_evc hP, MonObj.mul_comp, lift_fst, lift_snd, MonObj.one_comp, _root_.mul_one,
      _root_.one_mul, evc_one_right hP h₂, evc_one_left hP h₁] at e
    rw [← sub_eq_zero, ← e]
    abel

end GlobalTheory.BirigidRoot

theorem GlobalTheory.BirigidRoot.iso_of_lbPow_iso : ∀ (S : Scheme.{0}) (A : Over S) [GrpObj A] [IsCommMonObj A] (k : ℕ)
    (P₁ P₂ : LB (G2 A).left), IsAbelianScheme A → 0 < k → IsUnit (k : Γ(S, ⊤)) → P₁.IsLB →
    (∃ t : (P₁.pull (lift (1 : A ⟶ A) (𝟙 A)).left).Gen, t.IsGen) →
    (∃ t : (P₁.pull (lift (𝟙 A) (1 : A ⟶ A)).left).Gen, t.IsGen) → P₂.IsLB →
    (∃ t : (P₂.pull (lift (1 : A ⟶ A) (𝟙 A)).left).Gen, t.IsGen) →
    (∃ t : (P₂.pull (lift (𝟙 A) (1 : A ⟶ A)).left).Gen, t.IsGen) → LBIso (lbPow P₁ k) (lbPow P₂ k) →
    LBIso P₁ P₂ := by
  intro S A _ _ k P₁ P₂ hA hk _ hP₁ h₁ h₂ hP₂ h₁' h₂' e
  obtain ⟨a₁, b₁⟩ := GlobalTheory.BirigidRoot.additive_of_birigid hA hP₁ h₁ h₂
  obtain ⟨a₂, b₂⟩ := GlobalTheory.BirigidRoot.additive_of_birigid hA hP₂ h₁' h₂'
  obtain ⟨D, _, Q, -, -, q, q'⟩ := GlobalTheory.dualAbelianScheme S A hA
  obtain ⟨x₁, hx₁, ex₁⟩ := GlobalTheory.BirigidLift.exists_hom q q'.additive hP₁ a₁ b₁
  obtain ⟨x₂, hx₂, ex₂⟩ := GlobalTheory.BirigidLift.exists_hom q q'.additive hP₂ a₂ b₂
  have hk' : k • cls P₁ hP₁ = k • cls P₂ hP₂ := by
    rw [← cls_lbPow hP₁ k (LB.isLB_linComb hP₁ _ _), ← cls_lbPow hP₂ k (LB.isLB_linComb hP₂ _ _)]
    exact (cls_eq_iff _ _).2 e
  have pw : ∀ (y : A ⟶ D) (n : ℕ), evc q.isLB (fst A A) (snd A A ≫ y ^ n) =
      n • evc q.isLB (fst A A) (snd A A ≫ y) := by
    intro y n
    induction n with
    | zero => rw [pow_zero, MonObj.comp_one, zero_smul]; exact evc_one_right q.isLB q.zero _
    | succ n ih =>
      rw [pow_succ, MonObj.comp_mul, (GlobalTheory.BirigidLift.isAdditive_swap_iff q.isLB).1 q'.additive, ih, succ_nsmul]
  have hpow : x₁ ^ k = x₂ ^ k := GlobalTheory.BirigidLift.dual_ext q (by rw [pw, pw, ← ex₁, ← ex₂, hk'])
  have hx : x₁ = x₂ := by
    obtain ⟨hfl, hsu, -⟩ := GlobalTheory.UPel.HT.SiegUniqBase.flat_surjective_qc_pow S A hA k hk
    haveI := hfl
    haveI := hsu
    haveI : Epi ((𝟙 A) ^ k).left := Flat.epi_of_flat_of_surjective _
    have c : (((𝟙 A) ^ k) ≫ x₁).left = (((𝟙 A) ^ k) ≫ x₂).left := by
      rw [GlobalTheory.BirigidRoot.pow_comp_hom, GlobalTheory.BirigidRoot.pow_comp_hom, Category.id_comp, Category.id_comp, hpow]
    rw [Over.comp_left, Over.comp_left] at c
    exact Over.OverMorphism.ext ((cancel_epi ((𝟙 A) ^ k).left).1 c)
  subst hx
  exact (cls_eq_iff hP₁ hP₂).1 (ex₁.trans ex₂.symm)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemHodgeFiltrationIffDualNumberGraphReduction
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.UPel.Sm GlobalTheory.Cris GlobalTheory.DeRham

noncomputable section

namespace GlobalTheory.HTRealise

variable {k : Type} [Field k]

theorem crysRed_pull_constMor_pull (A₀ : Over (Sp k)) [GrpObj A₀] (c : primDR A₀) :
    (GlobalTheory.Published.GrothendieckMessing.crysRedMor (epsDP k) rfl A₀).pull ((constMor A₀).pull c) = c := by
  rw [GrpMor.pull_pull (constMor A₀) (GlobalTheory.Published.GrothendieckMessing.crysRedMor (epsDP k) rfl A₀)
    (homMor (dp0 k) (𝟙 _) (𝟙 A₀)) (fun _ ↦ rfl) (by simp) c]
  exact Subtype.ext (IsMor.pullCohomologyOne_id _ c.1)


set_option maxHeartbeats 1000000 in
theorem mem_Fil_iff_exists_graphFil_corr (A₀ : Over (Sp k)) [GrpObj A₀] (hA : IsAbelianScheme A₀)
    (f : HdR A₀ →ₗ[k] HdR A₀) (y : HdR A₀) :
    y ∈ Fil A₀ ↔ ∃ d ∈ graphFil A₀ f,
      (GlobalTheory.Published.GrothendieckMessing.crysRedMor (epsDP k) rfl A₀).Corr d y := by
  constructor
  · intro hy
    obtain ⟨d, hd⟩ := exists_crys hA y (f y)
    refine ⟨d, ⟨y, hy, 0, zero_mem _, fun c ↦ by rw [hd c]; simp⟩, fun c ↦ ?_⟩
    obtain ⟨z, rfl⟩ := (isBC_constMor hA).2 c
    induction z using TensorProduct.induction_on with
    | zero => simp only [map_zero, TrivSqZeroExt.fst_zero]
    | add a b ha hb => simp only [map_add (f := _), ha, hb, TrivSqZeroExt.fst_add]
    | tmul a c =>
      rw [liftSemi_tmul, map_smulₛₗ, map_smul, crysRed_pull_constMor_pull, map_smul, hd c]
      simp
  · rintro ⟨d, ⟨x, hx, y', -, e⟩, hc⟩
    have : y = x := LinearMap.ext fun c ↦ by
      have h1 := hc ((constMor A₀).pull c)
      rw [crysRed_pull_constMor_pull, e c] at h1
      simpa using h1
    exact this ▸ hx

end GlobalTheory.HTRealise
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemHodgeFiltrationIffReductionGluedFilHtObject
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.UPel.Sm GlobalTheory.Cris GlobalTheory.DeRham

noncomputable section

namespace GlobalTheory.HTGlue

theorem red_pull_constMorV_pull {k : Type} [Field k] {d : ℕ} (A₀ : Over (Sp k)) [GrpObj A₀]
    (c : prim (dp0 k) (𝟙 _) A₀) :
    (GlobalTheory.Published.GrothendieckMessing.crysRedMor (divided₂ (GlobalTheory.FODef.sqZero k (Fin d → k))) rfl A₀).pull
      ((GlobalTheory.FODef.constMorV k (Fin d → k) A₀).pull c) = c := by
  rw [GrpMor.pull_pull _ _ (homMor (dp0 k) (𝟙 _) (𝟙 A₀)) (fun r => rfl) (by simp)]
  exact Subtype.ext (IsMor.pullCohomologyOne_id _ c.1)

theorem eq_of_liftSemi_surj {K C : Type} [Field K] [CommRing C] [Algebra K C] {M M' : Type*} [AddCommGroup M]
    [Module K M] [AddCommGroup M'] [Module C M'] (P : M →ₛₗ[algebraMap K C] M')
    (hP : Function.Surjective (liftSemi P)) (π : C →+* K)
    (Q : M' →ₛₗ[π] M) (e : M' →ₗ[C] C) (y : M →ₗ[K] K) (hQ : ∀ c, Q (P c) = c)
    (he : ∀ c, π (e (P c)) = y c) (c' : M') : y (Q c') = π (e c') := by
  obtain ⟨u, rfl⟩ := hP c'
  induction u using TensorProduct.induction_on with
  | zero => simp
  | add u v hu hv => rw [map_add (f := _), map_add (f := _), map_add (f := _), map_add (f := _), map_add (f := _), hu, hv]
  | tmul r c =>
    rw [liftSemi_tmul, LinearMap.map_smulₛₗ, hQ, map_smul, map_smul, smul_eq_mul, smul_eq_mul, map_mul, he]

theorem corr_of_fst {k : Type} [Field k] {d : ℕ} (A₀ : Over (Sp k)) [GrpObj A₀] (hA : IsAbelianScheme A₀)
    (e : Crys (divided₂ (GlobalTheory.FODef.sqZero k (Fin d → k))) (spMap (TrivSqZeroExt.fstHom k k (Fin d → k)).toRingHom) A₀)
    (y : HdR A₀) (hc : ∀ c, (TrivSqZeroExt.fstHom k k (Fin d → k)).toRingHom
      (e ((GlobalTheory.FODef.constMorV k (Fin d → k) A₀).pull c)) = y c) :
    (GlobalTheory.Published.GrothendieckMessing.crysRedMor (divided₂ (GlobalTheory.FODef.sqZero k (Fin d → k))) rfl A₀).Corr e y :=
  eq_of_liftSemi_surj _ (GlobalTheory.SqZeroCrys.isBC_trivSqZeroExt k (Fin d → k) A₀ hA (GlobalTheory.FODef.sqZero k (Fin d → k))
    (GlobalTheory.FODef.constMorV k (Fin d → k) A₀)).2 _ _ e y (red_pull_constMorV_pull A₀) hc

theorem fil_iff_red_glueFil : ∀ (p : ℕ) [Fact p.Prime] (D : GlobalTheory.UPel.HT.Datum p) (R : Type) [CommRing R] (b : GlobalTheory.UPel.HT.Base D R) (N : ℕ), 3 ≤ N → N.Coprime p → ∀ (k : Type) [Field k] [IsAlgClosed k] (t : Sp k ⟶ Sp R) (o₀ : GlobalTheory.UPel.HT.Obj b N t) (β : R →+* k), t = spMap β → ∀ φ : LinearMap.BilinForm k (HdR o₀.A), GlobalTheory.AbDual.IsCorrForm (dp0 k) (𝟙 _) o₀.A o₀.A o₀.P φ → ∀ (d : ℕ) (f : Fin d → (HdR o₀.A →ₗ[k] HdR o₀.A)), (∀ j, IsKS (GlobalTheory.HTCount.crysAct o₀) φ (Fil o₀.A) (GlobalTheory.HTCount.lieZ o₀ β) (f j)) → (∀ y : HdR o₀.A, y ∈ Fil o₀.A ↔ ∃ e ∈ (GlobalTheory.HTGlue.glueFil o₀.A f), (GlobalTheory.Published.GrothendieckMessing.crysRedMor (divided₂ (GlobalTheory.FODef.sqZero k (Fin d → k))) rfl o₀.A).Corr e y) := by
  intro p _ D R _ b N _ _ k _ _ t o₀ β _ φ _ d f _ y
  constructor
  · intro hy
    obtain ⟨e, he, hc⟩ := exists_mem_glueFil o₀.A o₀.ab f hy
    refine ⟨e, he, corr_of_fst o₀.A o₀.ab e y fun c => ?_⟩
    rw [hc c]
    simp
  · rintro ⟨e, ⟨x, hx, z, hz, he⟩, hcorr⟩
    have hxy : y = x := LinearMap.ext fun c => by
      have h1 := hcorr ((GlobalTheory.FODef.constMorV k (Fin d → k) o₀.A).pull c)
      rw [red_pull_constMorV_pull, he c] at h1
      simpa using h1
    exact hxy ▸ hx

end GlobalTheory.HTGlue
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemHodgeFiltrationIffReductionGluedFiltration
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.UPel.Sm GlobalTheory.Cris GlobalTheory.DeRham

noncomputable section

namespace GlobalTheory.HTGlue

variable {k : Type} [Field k] (V : Type) [AddCommGroup V] [Module k V] [Module kᵐᵒᵖ V] [IsCentralScalar k V]

theorem red_constPull (A₀ : Over (Sp k)) [GrpObj A₀] (c : primDR A₀) :
    (GlobalTheory.Published.GrothendieckMessing.crysRedMor (divided₂ (GlobalTheory.FODef.sqZero k V)) rfl A₀).pull
      ((GlobalTheory.FODef.constMorV k V A₀).pull c) = c :=
  (GrpMor.pull_pull _ _ (homMor (dp0 k) (𝟙 _) (𝟙 A₀))
    (fun r ↦ by simp [TrivSqZeroExt.algebraMap_eq_inl]) (by simp) c).trans
    (Subtype.ext (IsMor.pullCohomologyOne_id _ _))

theorem corr_crysRedMor_iff (A₀ : Over (Sp k)) [GrpObj A₀] (hA : IsAbelianScheme A₀)
    (e : Crys (divided₂ (GlobalTheory.FODef.sqZero k V)) (spMap (TrivSqZeroExt.fstHom k k V).toRingHom) A₀) (y : HdR A₀) :
    (GlobalTheory.Published.GrothendieckMessing.crysRedMor (divided₂ (GlobalTheory.FODef.sqZero k V)) rfl A₀).Corr e y ↔
      ∀ c, y c = TrivSqZeroExt.fst (e ((GlobalTheory.FODef.constMorV k V A₀).pull c)) := by
  constructor
  · intro H c
    have := H ((GlobalTheory.FODef.constMorV k V A₀).pull c)
    rw [red_constPull] at this
    exact this
  · intro H c'
    have hm := GlobalTheory.SqZeroCrys.isBC_trivSqZeroExt k V A₀ hA (GlobalTheory.FODef.sqZero k V) (GlobalTheory.FODef.constMorV k V A₀)
    obtain ⟨z, rfl⟩ := hm.2 c'
    induction z with
    | add x x' hx hx' => simp only [map_add (f := _), hx, hx']
    | tmul r c =>
      rw [liftSemi_tmul]
      have h1 := (GlobalTheory.Published.GrothendieckMessing.crysRedMor (divided₂ (GlobalTheory.FODef.sqZero k V)) rfl A₀).pull.map_smulₛₗ r
        ((GlobalTheory.FODef.constMorV k V A₀).pull c)
      refine (congrArg y h1).trans ?_
      rw [red_constPull, map_smul, H c]
      have h2 := e.map_smul r ((GlobalTheory.FODef.constMorV k V A₀).pull c)
      rw [h2]
      exact (TrivSqZeroExt.fst_mul r _).symm

theorem mem_fil_iff_exists_glueFil : ∀ (p : ℕ) [Fact p.Prime] (D : GlobalTheory.UPel.HT.Datum p) (R : Type) [CommRing R] (b : GlobalTheory.UPel.HT.Base D R) (N : ℕ) (k : Type) [Field k] [IsAlgClosed k] (tk : R →+* k) (s : Sp k ⟶ Sp R) (o₀ : GlobalTheory.UPel.HT.Obj b N s), s = spMap tk → ∀ (d : ℕ) (f : Fin d → (HdR o₀.A →ₗ[k] HdR o₀.A)), ∀ y : HdR o₀.A, y ∈ Fil o₀.A ↔ ∃ e ∈ GlobalTheory.HTGlue.glueFil o₀.A f, (GlobalTheory.Published.GrothendieckMessing.crysRedMor (divided₂ (GlobalTheory.FODef.sqZero k (Fin d → k))) rfl o₀.A).Corr e y := by
  intro p _ D R _ b N k _ _ tk s o₀ _ d f y
  constructor
  · intro hy
    obtain ⟨e, he, hc⟩ := exists_mem_glueFil o₀.A o₀.ab f hy
    refine ⟨e, he, (corr_crysRedMor_iff (Fin d → k) o₀.A o₀.ab e y).2 fun c ↦ ?_⟩
    rw [hc c]
    simp
  · rintro ⟨e, ⟨x, hx, z, -, he⟩, hc⟩
    have hxy : y = x := LinearMap.ext fun c ↦ by
      rw [(corr_crysRedMor_iff (Fin d → k) o₀.A o₀.ab e y).1 hc c, he c]
      simp
    exact hxy ▸ hx

end GlobalTheory.HTGlue
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PicEqZeroOfFpqc
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT
open GlobalTheory.ZM GlobalTheory.SiegelTor

set_option autoImplicit false
noncomputable section

namespace GlobalTheory.BirigUniq

theorem one_comp_monHom {S : Scheme.{0}} {T A A' : Over S} [GrpObj A] [GrpObj A'] (f : A ⟶ A') [IsMonHom f] :
    (1 : T ⟶ A) ≫ f = 1 := by
  rw [Hom.one_def, Hom.one_def, Category.assoc, IsMonHom.one_hom]

theorem pull_comp_left {S : Scheme.{0}} {U V W : Over S} (g : U ⟶ V) (f : V ⟶ W) (c : GlobalTheory.CechPic.Pic W.left) :
    GlobalTheory.CechPic.pull (g ≫ f).left c = GlobalTheory.CechPic.pull g.left (GlobalTheory.CechPic.pull f.left c) := by
  rw [Over.comp_left, GlobalTheory.CechPic.pull_comp]

theorem pic_eq_zero_of_fpqc {S : Scheme.{0}} (X Y Y' : Over S) [GrpObj X] (hX : IsAbelianScheme X)
    (c : Y' ⟶ Y) (hfl : Flat c.left) (hsu : Surjective c.left) (hqc : QuasiCompact c.left)
    (d : GlobalTheory.CechPic.Pic (X ⊗ Y).left)
    (h0 : GlobalTheory.CechPic.pull (lift (1 : Y ⟶ X) (𝟙 Y)).left d = 0)
    (h1 : GlobalTheory.CechPic.pull (lift (fst X Y') (snd X Y' ≫ c)).left d = 0) : d = 0 := by
  obtain ⟨D, hD, rfl⟩ := GlobalTheory.CechPic.cls_surj d
  have t := GlobalTheory.RigDesc.triv_of_triv_zero_of_fpqc S X Y Y' hX c hfl hsu hqc D hD
    ((GlobalTheory.CechPic.cls_eq_zero_iff (pull_isLB hD _)).1 h0) ((GlobalTheory.CechPic.cls_eq_zero_iff (pull_isLB hD _)).1 h1)
  exact (GlobalTheory.CechPic.cls_eq_zero_iff hD).2 t

end GlobalTheory.BirigUniq

namespace GlobalTheory.BirigUniq

end GlobalTheory.BirigUniq
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SmoothOfRelativeDimensionDual
section
set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.PDiv GlobalTheory.PDivGroup GlobalTheory.AbDual GlobalTheory.CechPic
open GlobalTheory.SerreTateDef (IsPairRed polBundle)
open GlobalTheory.CompanionTheory.Hypotheses₂.Zarhin (IsPolarisation)
open GlobalTheory.BadPt (IsWeilHom)
open GlobalTheory.PerfdLat (dualBaseChange)

attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory

namespace GlobalTheory.DualTower

theorem dim_eq_of_isDual {K : Type} [Field K] (A D : AV.AbVar K) (P : LB (A.X ⊗ D.X).left)
    (h : IsDual A.X D.X P) : D.dim = A.dim := by
  obtain ⟨B, _, P₀, _, hdim, hdual, _⟩ := GlobalTheory.dualAbelianScheme _ A.X A.ab
  obtain ⟨e⟩ := GlobalTheory.Published.AbelianDualCrystal.Test.dual_unique hdual h
  have hB := hdim A.dim A.smooth
  have hne : Nonempty (Sp K) := ⟨IsLocalRing.closedPoint K⟩
  exact (GlobalTheory.relDim_unique_of_iso_grp _ hne B D.X e.hom inferInstance A.dim D.dim hB D.smooth).symm

end GlobalTheory.DualTower
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaMemberTorusTranslationExponentAffine
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT ReciprocityTheory.ChartRestriction.G.DVR
open GlobalTheory.Poinc.Sep
open GlobalTheory.UT.CoefBasic

namespace GlobalTheory.GSep.TransTerms

theorem trans_exp_affine : ∀ (I : Type) (X₁ : GlobalTheory.GSep.GSet) (z₁ : X₁.M.Z) (act : I → (X₁.ρ.P.A ⟶ X₁.ρ.P.A)) (x₀ : X₁.S.Gam), X₁.M.Div X₁.S.th x₀ z₁ → ∀ (V1 : Type) [CommRing V1] [IsDomain V1] [IsLocalRing V1] (ev1 : X₁.M.Z.presheaf.stalk z₁ →+* V1) (Y1 : Type) [AddCommGroup Y1] (t1 : Y1 → V1) (δ1 : I → Y1 → Y1) (𝔪1 : GlobalTheory.GSep.GMem X₁ z₁ act V1 ev1 Y1 t1 δ1) (V2 : Type) [CommRing V2] [IsDomain V2] [IsLocalRing V2] (ev2 : X₁.M.Z.presheaf.stalk z₁ →+* V2) (Y2 : Type) [AddCommGroup Y2] (t2 : Y2 → V2) (δ2 : I → Y2 → Y2) (𝔪2 : GlobalTheory.GSep.GMem X₁ z₁ act V2 ev2 Y2 t2 δ2), ∀ τ ∈ X₁.S.TT X₁.M z₁, ∃ F1 F2 : X₁.S.Gam → ℕ, (∀ a ∈ X₁.S.HH X₁.M z₁, GlobalTheory.GSep.TransTerms.TransExp 𝔪1 x₀ a τ (F1 a)) ∧ (∀ a ∈ X₁.S.HH X₁.M z₁, GlobalTheory.GSep.TransTerms.TransExp 𝔪2 x₀ a τ (F2 a)) ∧ ∃ (κ : ZMod ((X₁.S.r * X₁.S.N) ^ 2)) (h : X₁.S.HH X₁.M z₁ →+ ZMod ((X₁.S.r * X₁.S.N) ^ 2)), ∀ (a : X₁.S.Gam) (ha : a ∈ X₁.S.HH X₁.M z₁), ((F1 a : ℕ) : ZMod ((X₁.S.r * X₁.S.N) ^ 2)) - ((F2 a : ℕ) : ZMod ((X₁.S.r * X₁.S.N) ^ 2)) = κ + h ⟨a, ha⟩ := by
  classical
  intro I X₁ z₁ act x₀ hd V1 _ _ _ ev1 Y1 _ t1 δ1 𝔪1 V2 _ _ _ ev2 Y2 _ t2 δ2 𝔪2 τ hτ
  let E1 : X₁.S.Gam → ℕ := fun a => if ha : a ∈ X₁.S.HH X₁.M z₁ then
    Classical.choose (_root_.GlobalTheory.GSep.FrameExpEx.exists_frExp I X₁ z₁ act x₀ hd V1 ev1 Y1 t1 δ1 𝔪1 a ha τ hτ) else 0
  let E2 : X₁.S.Gam → ℕ := fun a => if ha : a ∈ X₁.S.HH X₁.M z₁ then
    Classical.choose (_root_.GlobalTheory.GSep.FrameExpEx.exists_frExp I X₁ z₁ act x₀ hd V2 ev2 Y2 t2 δ2 𝔪2 a ha τ hτ) else 0
  have h1 : ∀ a ∈ X₁.S.HH X₁.M z₁, FrExp 𝔪1 a τ (E1 a) := fun a ha => by
    simp only [E1, dif_pos ha]
    exact Classical.choose_spec (_root_.GlobalTheory.GSep.FrameExpEx.exists_frExp I X₁ z₁ act x₀ hd V1 ev1 Y1 t1 δ1 𝔪1 a ha τ hτ)
  have h2 : ∀ a ∈ X₁.S.HH X₁.M z₁, FrExp 𝔪2 a τ (E2 a) := fun a ha => by
    simp only [E2, dif_pos ha]
    exact Classical.choose_spec (_root_.GlobalTheory.GSep.FrameExpEx.exists_frExp I X₁ z₁ act x₀ hd V2 ev2 Y2 t2 δ2 𝔪2 a ha τ hτ)
  exact ⟨E1, E2, fun a ha => _root_.GlobalTheory.GSep.TransTerms.transExp_of_frExp I X₁ z₁ act x₀ hd V1 ev1 Y1 t1 δ1 𝔪1 a ha τ hτ _ (h1 a ha),
    fun a ha => _root_.GlobalTheory.GSep.TransTerms.transExp_of_frExp I X₁ z₁ act x₀ hd V2 ev2 Y2 t2 δ2 𝔪2 a ha τ hτ _ (h2 a ha),
    _root_.GlobalTheory.GSep.TransTerms.frExp_affine_two_members I X₁ z₁ act x₀ hd V1 ev1 Y1 t1 δ1 𝔪1 V2 ev2 Y2 t2 δ2 𝔪2 τ hτ E1 E2 h1 h2⟩

end GlobalTheory.GSep.TransTerms
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitaryFourierClassSumsDeeperLevel
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.Models GlobalTheory.LN GlobalTheory.ShFam GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZH GlobalTheory.Poinc
open scoped CategoryTheory.Obj
open GlobalTheory.UPoinc
open GlobalTheory
open Classical

namespace GlobalTheory.UPoinc

theorem ustalk_isNoetherian_normal_fractionRing : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l) (C : UCompact Xo c) (X₁ : USetup C) (z₁ : X₁.M.Z), letI : Algebra (X₁.M.Z.presheaf.stalk z₁) X₁.Ω₁ := (X₁.M.stalkHom z₁).toAlgebra; IsDomain (X₁.M.Z.presheaf.stalk z₁) ∧ IsFractionRing (X₁.M.Z.presheaf.stalk z₁) X₁.Ω₁ ∧ IsIntegrallyClosed (X₁.M.Z.presheaf.stalk z₁) ∧ IsNoetherianRing (X₁.M.Z.presheaf.stalk z₁) := by
  intro E _ _ _ H Dw l Xo c C X₁ z₁
  letI : Algebra (X₁.M.Z.presheaf.stalk z₁) X₁.Ω₁ := (X₁.M.stalkHom z₁).toAlgebra
  have hN := X₁.normal
  refine ⟨GlobalTheory.IsNormalScheme.isDomain_stalk z₁, ?_, GlobalTheory.IsNormalScheme.isIntegrallyClosed_stalk z₁, ?_⟩
  · have : FaithfulSMul (X₁.M.Z.presheaf.stalk z₁) X₁.Ω₁ :=
      (faithfulSMul_iff_algebraMap_injective _ _).2 (X₁.M.stalkHom_injective z₁)
    refine IsFractionRing.of_field _ _ fun x => ?_
    obtain ⟨a, b, -, hx⟩ := IsFractionRing.div_surjective (A := X₁.M.O z₁) x
    refine ⟨(X₁.M.stalkEquiv z₁).symm a, (X₁.M.stalkEquiv z₁).symm b, ?_⟩
    have h : ∀ c : X₁.M.O z₁, algebraMap (X₁.M.Z.presheaf.stalk z₁) X₁.Ω₁ ((X₁.M.stalkEquiv z₁).symm c) = c := fun c => by
      change X₁.M.stalkHom z₁ _ = _
      rw [← RatModel.coe_stalkEquiv, RingEquiv.apply_symm_apply]
    rw [h, h, ← hx]
    rfl
  · have : IsDedekindDomain X₁.o₁ := X₁.ar.ded
    have := X₁.M.lft
    have : IsLocallyNoetherian (Sp X₁.o₁) :=
      inferInstanceAs (IsLocallyNoetherian (Spec (CommRingCat.of X₁.o₁)))
    have : IsLocallyNoetherian X₁.M.Z := LocallyOfFiniteType.isLocallyNoetherian X₁.M.s
    infer_instance

theorem uclassSums_deeper : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H), 1 ≤ Dw.p + Dw.q → ∀ (l : Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l) (C : UCompact Xo c) (X₁ : USetup C) (p : ℕ) [Fact p.Prime] (z₁ : X₁.M.Z) (Φ : FPre (H.bar : 𝓞 E → 𝓞 E) (min Dw.p Dw.q) p (X₁.M.Z.presheaf.stalk z₁)), (∀ y, ∃ t : UCTrait X₁ p z₁, (∀ a, Φ.ev y a = t.val a) ∧ ∃ e : Φ.X y ≃ₗ[𝓞 E] t.T.P.D.toPre.X, ∀ a b, Φ.sc y * Φ.β y a b = t.sc * t.T.be (e a) (e b)) → ∀ (y₀ : Φ.Y) (N₀ : ℕ), ∃ N, N₀ ≤ N ∧ (X₁.S.r * X₁.S.N) ∣ N ∧ ∃ (k : ∀ y, Φ.X y₀ →ₗ[ℤ] Φ.X y) (Q : Type) (t : ∀ y, (Fin 1 → Φ.X y) → Q → PadicAlgCl p) (B : Type) (_ : CommRing B) (_ : IsDomain B) (_ : Algebra (X₁.M.Z.presheaf.stalk z₁) B) (_ : Module.Finite (X₁.M.Z.presheaf.stalk z₁) B) (_ : Finite (B ≃ₐ[X₁.M.Z.presheaf.stalk z₁] B)) (𝔷 : Ideal B), Function.Injective (algebraMap (X₁.M.Z.presheaf.stalk z₁) B) ∧ (∀ b : B, (∀ σ : B ≃ₐ[X₁.M.Z.presheaf.stalk z₁] B, σ b = b) → b ∈ Set.range (algebraMap (X₁.M.Z.presheaf.stalk z₁) B)) ∧ 𝔷.IsMaximal ∧ k y₀ = LinearMap.id ∧ (∀ y, IsUnimodMod (𝓞 E) N (k y)) ∧ Φ.IsTerms !![(1 : ℤ)] t ∧ Φ.ClassSums (X₁.S.r * X₁.S.N) N y₀ k t B 𝔷 := by
  intro E _ _ _ H Dw hpq l Xo c C X₁ p _ z₁ Φ hΦ y₀ N₀
  obtain ⟨N, hN₀, hdvd, Ω₂, _, _, _, _, hcore⟩ := GlobalTheory.T.unitary_classSums_deeper_level_integralClosure E H Dw hpq l Xo c C X₁ p z₁ Φ hΦ y₀ N₀
  letI : Algebra (X₁.M.Z.presheaf.stalk z₁) X₁.Ω₁ := (X₁.M.stalkHom z₁).toAlgebra
  obtain ⟨hdom, hfr, hic, hno⟩ := ustalk_isNoetherian_normal_fractionRing E H Dw l Xo c C X₁ z₁
  obtain ⟨hfin, hfinA, hinj, hfix⟩ := GlobalTheory.T.integralClosure_galois_finite_autGroup_invariants (X₁.M.Z.presheaf.stalk z₁) X₁.Ω₁ Ω₂
  letI : Algebra (X₁.M.Z.presheaf.stalk z₁) Ω₂ := ((algebraMap X₁.Ω₁ Ω₂).comp (X₁.M.stalkHom z₁)).toAlgebra
  obtain ⟨𝔷, hmax⟩ := Ideal.exists_maximal (integralClosure (X₁.M.Z.presheaf.stalk z₁) Ω₂)
  have hext := fun y => _root_.GlobalTheory.ValExt.exists_ext_centred p (X₁.M.Z.presheaf.stalk z₁) (integralClosure (X₁.M.Z.presheaf.stalk z₁) Ω₂) 𝔷 hinj hfix hmax (Φ.ev y) (Φ.ev_le y) (Φ.ev_lt y)
  choose ev' h1 h2 h3 using hext
  obtain ⟨k, Q, t, f, hk₀, hk, ht, hf, hcs, hgal⟩ := hcore 𝔷 hmax ev' h1 h2 h3
  exact ⟨N, hN₀, hdvd, k, Q, t, (integralClosure (X₁.M.Z.presheaf.stalk z₁) Ω₂), inferInstance, inferInstance, inferInstance, hfin, hfinA, 𝔷, hinj, hfix, hmax, hk₀, hk, ht,
    ev', f, h1, h2, h3, hf, hcs, hgal⟩

end GlobalTheory.UPoinc
end

