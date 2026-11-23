module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3103
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0322
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0358
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3099
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1945
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3097
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2283
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3104
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3090
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsThetaOfTranslDiff
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3100
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3095
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0007
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DualNumberGraphFiltrationLieOfMapIntoHodge
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0061
public import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.ChainOfKernelsUnique
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0017
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3101

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CechDegreeZeroBijective
section
open CategoryTheory Limits AlgebraicGeometry Opposite Simplicial GlobalTheory.EtC GlobalTheory.EtC.GmStep
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cech_degree_zero_bijective : ∀ (q : ℕ) [NeZero q] (A : Type) [CommRing A], SH A → IsUnit (q : A) → ∀ (A' : Type) [CommRing A'] [Algebra A A'],
  Module.Finite A A' → ∀ (k : ℕ) (i : ℤ), Function.Bijective (rowOne A A' q i k) := by
  first | (exact @GlobalTheory.EtC.GmStep.LevelOne.rowOne_bijective) | (exact GlobalTheory.EtC.GmStep.LevelOne.rowOne_bijective) | (intros; apply GlobalTheory.EtC.GmStep.LevelOne.rowOne_bijective  <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CrystalGluedHodgeGraphFiltrationHasComplementStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.UPel.Sm GlobalTheory.Cris GlobalTheory.DeRham
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.crystalGluedHodgeGraphFiltration_hasComplement : ∀ (p : ℕ) [Fact p.Prime] (D : GlobalTheory.UPel.HT.Datum p) (R : Type) [CommRing R] (b : GlobalTheory.UPel.HT.Base D R) (N : ℕ), 3 ≤ N → N.Coprime p → ∀ (k : Type) [Field k] [IsAlgClosed k] (t : Sp k ⟶ Sp R) (o₀ : GlobalTheory.UPel.HT.Obj b N t) (β : R →+* k), t = spMap β → ∀ φ : LinearMap.BilinForm k (HdR o₀.A), GlobalTheory.AbDual.IsCorrForm (dp0 k) (𝟙 _) o₀.A o₀.A o₀.P φ → ∀ (d : ℕ) (f : Fin d → (HdR o₀.A →ₗ[k] HdR o₀.A)), (∀ j, IsKS (GlobalTheory.HTCount.crysAct o₀) φ (Fil o₀.A) (GlobalTheory.HTCount.lieZ o₀ β) (f j)) → (∃ M : Submodule (TrivSqZeroExt k (Fin d → k)) (Crys (divided₂ (GlobalTheory.FODef.sqZero k (Fin d → k))) (spMap (TrivSqZeroExt.fstHom k k (Fin d → k)).toRingHom) o₀.A), IsCompl (GlobalTheory.HTGlue.glueFil o₀.A f) M) := by
  first | (exact @GlobalTheory.HTGlue.glueFil_hasCompl) | (exact GlobalTheory.HTGlue.glueFil_hasCompl) | (intros; apply GlobalTheory.HTGlue.glueFil_hasCompl  <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CrystalGluedHodgeGraphFiltrationIsotropicPolarisStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.UPel.Sm GlobalTheory.Cris GlobalTheory.DeRham
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.crystalGluedHodgeGraphFiltration_isotropic_polarisation : ∀ (p : ℕ) [Fact p.Prime] (D : GlobalTheory.UPel.HT.Datum p) (R : Type) [CommRing R] (b : GlobalTheory.UPel.HT.Base D R) (N : ℕ), 3 ≤ N → N.Coprime p → ∀ (k : Type) [Field k] [IsAlgClosed k] (t : Sp k ⟶ Sp R) (o₀ : GlobalTheory.UPel.HT.Obj b N t) (β : R →+* k), t = spMap β → ∀ φ : LinearMap.BilinForm k (HdR o₀.A), GlobalTheory.AbDual.IsCorrForm (dp0 k) (𝟙 _) o₀.A o₀.A o₀.P φ → ∀ (d : ℕ) (f : Fin d → (HdR o₀.A →ₗ[k] HdR o₀.A)), (∀ j, IsKS (GlobalTheory.HTCount.crysAct o₀) φ (Fil o₀.A) (GlobalTheory.HTCount.lieZ o₀ β) (f j)) → (∀ Φ : Crys (divided₂ (GlobalTheory.FODef.sqZero k (Fin d → k))) (spMap (TrivSqZeroExt.fstHom k k (Fin d → k)).toRingHom) o₀.A →ₗ[(TrivSqZeroExt k (Fin d → k))] Crys (divided₂ (GlobalTheory.FODef.sqZero k (Fin d → k))) (spMap (TrivSqZeroExt.fstHom k k (Fin d → k)).toRingHom) o₀.A →ₗ[(TrivSqZeroExt k (Fin d → k))] (TrivSqZeroExt k (Fin d → k)), GlobalTheory.AbDual.IsCorrForm (divided₂ (GlobalTheory.FODef.sqZero k (Fin d → k))) (spMap (TrivSqZeroExt.fstHom k k (Fin d → k)).toRingHom) o₀.A o₀.A o₀.P Φ → ∀ x ∈ (GlobalTheory.HTGlue.glueFil o₀.A f), ∀ y ∈ (GlobalTheory.HTGlue.glueFil o₀.A f), Φ x y = 0) := by
  first | (exact @GlobalTheory.HTGlueIsoPol.glueFil_isotropic) | (exact GlobalTheory.HTGlueIsoPol.glueFil_isotropic) | (intros; apply GlobalTheory.HTGlueIsoPol.glueFil_isotropic  <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CrystalGluedHodgeGraphFiltrationOrderStableStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.UPel.Sm GlobalTheory.Cris GlobalTheory.DeRham
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.crystalGluedHodgeGraphFiltration_order_stable : ∀ (p : ℕ) [Fact p.Prime] (D : GlobalTheory.UPel.HT.Datum p) (R : Type) [CommRing R] (b : GlobalTheory.UPel.HT.Base D R) (N : ℕ), 3 ≤ N → N.Coprime p → ∀ (k : Type) [Field k] [IsAlgClosed k] (t : Sp k ⟶ Sp R) (o₀ : GlobalTheory.UPel.HT.Obj b N t) (β : R →+* k), t = spMap β → ∀ φ : LinearMap.BilinForm k (HdR o₀.A), GlobalTheory.AbDual.IsCorrForm (dp0 k) (𝟙 _) o₀.A o₀.A o₀.P φ → ∀ (d : ℕ) (f : Fin d → (HdR o₀.A →ₗ[k] HdR o₀.A)), (∀ j, IsKS (GlobalTheory.HTCount.crysAct o₀) φ (Fil o₀.A) (GlobalTheory.HTCount.lieZ o₀ β) (f j)) → (∀ (c : D.O), ∀ e ∈ (GlobalTheory.HTGlue.glueFil o₀.A f), (haveI := o₀.act.hom (c); push (divided₂ (GlobalTheory.FODef.sqZero k (Fin d → k))) (spMap (TrivSqZeroExt.fstHom k k (Fin d → k)).toRingHom) (o₀.act.act (c)) (e)) ∈ (GlobalTheory.HTGlue.glueFil o₀.A f)) := by
  first | exact @GlobalTheory.HTGlue.push_mem_glueFil | exact GlobalTheory.HTGlue.push_mem_glueFil | (intros; apply GlobalTheory.HTGlue.push_mem_glueFil <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CrystalGluedHodgeGraphIsotropicOfDirections
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.UPel.Sm GlobalTheory.Cris GlobalTheory.DeRham

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.HTGlueIso

open GlobalTheory.AbDual

variable {k : Type} [Field k]

theorem fil_isotropic_of_isCorrForm (A : Over (Sp k)) [GrpObj A] (hA : IsAbelianScheme A) (P : LB (A ⊗ A).left)
    (hP : P.IsLB) (φ : HdR A →ₗ[k] HdR A →ₗ[k] k) (hφ : IsCorrForm (dp0 k) (𝟙 _) A A P φ) :
    ∀ x ∈ Fil A, ∀ y ∈ Fil A, φ x y = 0 := by
  have H := GlobalTheory.abelianDeRham
  obtain ⟨g, hg⟩ := GlobalTheory.AbVarRelDim.exists_relDim k A hA
  have hAB := AbelianSchemeGerms.isAbelianScheme_tensor A A hA hA
  have gAB := smooth_prod hg hg
  obtain ⟨ψ, hψ, e⟩ := hφ.isPolForm
  obtain ⟨iso, -⟩ := H.2.2.2.2 k _ _ hAB gAB P hP ψ hψ
  intro x hx y hy
  have a₁ : push (dp0 k) (𝟙 _) (fst A A) (push (dp0 k) (𝟙 _) (inl A A) x) = x := by
    rw [push_push _ _ _ (lift_fst _ _), push_id]; rfl
  have a₂ : push (dp0 k) (𝟙 _) (snd A A) (push (dp0 k) (𝟙 _) (inl A A) x) = 0 := by
    rw [push_push _ _ _ (lift_snd _ _), push_one]; rfl
  have b₁ : push (dp0 k) (𝟙 _) (fst A A) (push (dp0 k) (𝟙 _) (inr A A) y) = 0 := by
    rw [push_push _ _ _ (lift_fst _ _), push_one]; rfl
  have b₂ : push (dp0 k) (𝟙 _) (snd A A) (push (dp0 k) (𝟙 _) (inr A A) y) = y := by
    rw [push_push _ _ _ (lift_snd _ _), push_id]; rfl
  have key : φ x y = ψ (push (dp0 k) (𝟙 _) (inl A A) x) (push (dp0 k) (𝟙 _) (inr A A) y) := by
    rw [e, a₁, a₂, b₁, b₂]; simp
  rw [key]
  exact iso _ (push_mem_Fil _ hx) _ (push_mem_Fil _ hy)

variable {d : ℕ}

def proj (j : Fin d) : TrivSqZeroExt k (Fin d → k) →+* TrivSqZeroExt k k :=
  (TrivSqZeroExt.map (LinearMap.proj (R := k) (φ := fun _ : Fin d => k) j)).toRingHom

@[simp] theorem fst_proj (j : Fin d) (a : TrivSqZeroExt k (Fin d → k)) : (proj j a).fst = a.fst := by
  simp [proj]

@[simp] theorem snd_proj (j : Fin d) (a : TrivSqZeroExt k (Fin d → k)) : (proj j a).snd = a.snd j := by
  simp [proj]

theorem projMor (A₀ : Over (Sp k)) [GrpObj A₀] (j : Fin d) :
    GrpMor (divided₂ (GlobalTheory.FODef.sqZero k (Fin d → k))) (spMap (TrivSqZeroExt.fstHom k k (Fin d → k)).toRingHom) A₀
      (divided₂ (GlobalTheory.FODef.sqZero k k)) (spMap (TrivSqZeroExt.fstHom k k k).toRingHom) A₀ (proj j) (𝟙 _)
      (Over.Hom.left (𝟙 A₀)) :=
  GrpMor.of_hom (isDPMorphism_sqDP _ _ _ fun a ha => by
      rw [RingHom.mem_ker] at ha ⊢
      change (proj j a).fst = 0
      rw [fst_proj]; exact ha)
    (by
      rw [← GlobalTheory.Cris.spMap_comp]
      congr 1
      ext a <;> simp) (𝟙 A₀)

theorem eq_of_liftSemi_surj' {K C C' : Type} [Field K] [CommRing C] [CommRing C'] [Algebra K C] {M M' M'' : Type*}
    [AddCommGroup M] [Module K M] [AddCommGroup M'] [Module C M'] [AddCommGroup M''] [Module C' M'']
    (P : M →ₛₗ[algebraMap K C] M') (hP : Function.Surjective (liftSemi P)) (σ : C →+* C')
    (Q : M' →ₛₗ[σ] M'') (P' : M → M'') (hQ : ∀ c, Q (P c) = P' c) (x : M' →ₗ[C] C) (x' : M'' →ₗ[C'] C')
    (h : ∀ c, x' (P' c) = σ (x (P c))) (c : M') : x' (Q c) = σ (x c) := by
  obtain ⟨u, rfl⟩ := hP c
  induction u using TensorProduct.induction_on with
  | zero => simp
  | add u v hu hv => rw [map_add (f := _), map_add (f := _), map_add (f := _), map_add (f := _), map_add (f := _), hu, hv]
  | tmul r c =>
    rw [liftSemi_tmul, LinearMap.map_smulₛₗ, map_smul, map_smul, hQ, h, smul_eq_mul, smul_eq_mul, map_mul]

theorem projMor_corr (A₀ : Over (Sp k)) [GrpObj A₀] (hA : IsAbelianScheme A₀) (j : Fin d)
    (x : Crys (divided₂ (GlobalTheory.FODef.sqZero k (Fin d → k))) (spMap (TrivSqZeroExt.fstHom k k (Fin d → k)).toRingHom) A₀)
    (x' : Crys (divided₂ (GlobalTheory.FODef.sqZero k k)) (spMap (TrivSqZeroExt.fstHom k k k).toRingHom) A₀)
    (h : ∀ c, x' ((GlobalTheory.FODef.constMorV k k A₀).pull c) = proj j (x ((GlobalTheory.FODef.constMorV k (Fin d → k) A₀).pull c))) :
    (projMor A₀ j).Corr x x' :=
  eq_of_liftSemi_surj' _ (GlobalTheory.SqZeroCrys.isBC_trivSqZeroExt k (Fin d → k) A₀ hA (GlobalTheory.FODef.sqZero k (Fin d → k))
    (GlobalTheory.FODef.constMorV k (Fin d → k) A₀)).2 (proj j) (projMor A₀ j).pull _
    (fun c => GrpMor.pull_pull (GlobalTheory.FODef.constMorV k (Fin d → k) A₀) (projMor A₀ j) (GlobalTheory.FODef.constMorV k k A₀)
      (fun r => by ext <;> simp [TrivSqZeroExt.algebraMap_eq_inl]) (by simp) c) x x' h

theorem exists_red_form (A₀ : Over (Sp k)) [GrpObj A₀] (P : LB (A₀ ⊗ A₀).left) (hP : P.IsLB)
    (φ : Crys (divided₂ (GlobalTheory.FODef.sqZero k (Fin d → k))) (spMap (TrivSqZeroExt.fstHom k k (Fin d → k)).toRingHom) A₀ →ₗ[TrivSqZeroExt k (Fin d → k)]
      Crys (divided₂ (GlobalTheory.FODef.sqZero k (Fin d → k))) (spMap (TrivSqZeroExt.fstHom k k (Fin d → k)).toRingHom) A₀ →ₗ[TrivSqZeroExt k (Fin d → k)]
        TrivSqZeroExt k (Fin d → k))
    (hφ : IsCorrForm (divided₂ (GlobalTheory.FODef.sqZero k (Fin d → k))) (spMap (TrivSqZeroExt.fstHom k k (Fin d → k)).toRingHom)
      A₀ A₀ P φ) :
    ∃ φ₀ : HdR A₀ →ₗ[k] HdR A₀ →ₗ[k] k, IsCorrForm (dp0 k) (𝟙 _) A₀ A₀ P φ₀ ∧
      ∀ x x' y y', (GlobalTheory.Published.GrothendieckMessing.crysRedMor (divided₂ (GlobalTheory.FODef.sqZero k (Fin d → k))) rfl A₀).Corr x x' →
        (GlobalTheory.Published.GrothendieckMessing.crysRedMor (divided₂ (GlobalTheory.FODef.sqZero k (Fin d → k))) rfl A₀).Corr y y' →
        φ₀ x' y' = (φ x y).fst :=
  hφ.pull hP (GlobalTheory.Published.GrothendieckMessing.crysRedMor (divided₂ (GlobalTheory.FODef.sqZero k (Fin d → k))) rfl A₀)
    (GlobalTheory.Published.GrothendieckMessing.crysRedMor (divided₂ (GlobalTheory.FODef.sqZero k (Fin d → k))) rfl A₀)
    (h := 𝟙 _) ((Category.id_comp _).trans (Category.comp_id _).symm)
    ((Category.id_comp _).trans (Category.comp_id _).symm) hP (GlobalTheory.lbIso_pull_id hP)

theorem exists_proj_form (A₀ : Over (Sp k)) [GrpObj A₀] (P : LB (A₀ ⊗ A₀).left) (hP : P.IsLB) (j : Fin d)
    (φ : Crys (divided₂ (GlobalTheory.FODef.sqZero k (Fin d → k))) (spMap (TrivSqZeroExt.fstHom k k (Fin d → k)).toRingHom) A₀ →ₗ[TrivSqZeroExt k (Fin d → k)]
      Crys (divided₂ (GlobalTheory.FODef.sqZero k (Fin d → k))) (spMap (TrivSqZeroExt.fstHom k k (Fin d → k)).toRingHom) A₀ →ₗ[TrivSqZeroExt k (Fin d → k)]
        TrivSqZeroExt k (Fin d → k))
    (hφ : IsCorrForm (divided₂ (GlobalTheory.FODef.sqZero k (Fin d → k))) (spMap (TrivSqZeroExt.fstHom k k (Fin d → k)).toRingHom)
      A₀ A₀ P φ) :
    ∃ φ' : Crys (divided₂ (GlobalTheory.FODef.sqZero k k)) (spMap (TrivSqZeroExt.fstHom k k k).toRingHom) A₀ →ₗ[TrivSqZeroExt k k]
        Crys (divided₂ (GlobalTheory.FODef.sqZero k k)) (spMap (TrivSqZeroExt.fstHom k k k).toRingHom) A₀ →ₗ[TrivSqZeroExt k k]
          TrivSqZeroExt k k,
      IsCorrForm (divided₂ (GlobalTheory.FODef.sqZero k k)) (spMap (TrivSqZeroExt.fstHom k k k).toRingHom) A₀ A₀ P φ' ∧
      ∀ x x' y y', (projMor A₀ j).Corr x x' → (projMor A₀ j).Corr y y' → φ' x' y' = proj j (φ x y) :=
  hφ.pull hP (projMor A₀ j) (projMor A₀ j) (h := 𝟙 _) ((Category.id_comp _).trans (Category.comp_id _).symm)
    ((Category.id_comp _).trans (Category.comp_id _).symm) hP (GlobalTheory.lbIso_pull_id hP)

theorem exists_mem_of_fil (A₀ : Over (Sp k)) [GrpObj A₀] (g : HdR A₀ →ₗ[k] HdR A₀)
    (E : Submodule (TrivSqZeroExt k k)
      (Crys (divided₂ (GlobalTheory.FODef.sqZero k k)) (spMap (TrivSqZeroExt.fstHom k k k).toRingHom) A₀))
    (hE : ∀ x ∈ Fil A₀, ∃ e ∈ E, ∀ c, e ((GlobalTheory.FODef.constMorV k k A₀).pull c) =
      TrivSqZeroExt.inl (x c) + TrivSqZeroExt.inr (g x c))
    {x z : HdR A₀} (hx : x ∈ Fil A₀) (hz : z ∈ Fil A₀) :
    ∃ e ∈ E, ∀ c, e ((GlobalTheory.FODef.constMorV k k A₀).pull c) =
      TrivSqZeroExt.inl (x c) + TrivSqZeroExt.inr ((g x + z) c) := by
  obtain ⟨e₁, h₁, he₁⟩ := hE x hx
  obtain ⟨e₂, h₂, he₂⟩ := hE z hz
  refine ⟨e₁ + (TrivSqZeroExt.inr (1 : k) : TrivSqZeroExt k k) • e₂, add_mem h₁ (E.smul_mem _ h₂), fun c => ?_⟩
  rw [LinearMap.add_apply, LinearMap.smul_apply, he₁, he₂, smul_eq_mul]
  ext <;> simp

theorem glueFil_isotropic : ∀ (p : ℕ) [Fact p.Prime] (D : GlobalTheory.UPel.HT.Datum p) (R : Type) [CommRing R] (b : GlobalTheory.UPel.HT.Base D R) (N : ℕ) (k : Type) [Field k] [IsAlgClosed k] (tk : R →+* k) (s : Sp k ⟶ Sp R) (o₀ : GlobalTheory.UPel.HT.Obj b N s), s = spMap tk → ∀ (d : ℕ) (f : Fin d → (HdR o₀.A →ₗ[k] HdR o₀.A)), ∀ (E' : Fin d → Submodule (TrivSqZeroExt k k) (Crys (divided₂ (GlobalTheory.FODef.sqZero k k)) (spMap (TrivSqZeroExt.fstHom k k k).toRingHom) o₀.A)), (∀ j, ∃ M : Submodule (TrivSqZeroExt k k) (Crys (divided₂ (GlobalTheory.FODef.sqZero k k)) (spMap (TrivSqZeroExt.fstHom k k k).toRingHom) o₀.A), IsCompl (E' j) M) → (∀ j, ∀ y : HdR o₀.A, y ∈ Fil o₀.A ↔ ∃ e ∈ E' j, (GlobalTheory.Published.GrothendieckMessing.crysRedMor (divided₂ (GlobalTheory.FODef.sqZero k k)) rfl o₀.A).Corr e y) → (∀ j, ∀ x ∈ Fil o₀.A, ∃ e ∈ E' j, ∀ c, e ((GlobalTheory.FODef.constMorV k k o₀.A).pull c) = TrivSqZeroExt.inl (x c) + TrivSqZeroExt.inr (f j x c)) → (∀ j (c : D.O), ∀ e ∈ E' j, (haveI := o₀.act.hom (c); push (divided₂ (GlobalTheory.FODef.sqZero k k)) (spMap (TrivSqZeroExt.fstHom k k k).toRingHom) (o₀.act.act (c)) (e)) ∈ E' j) → (∀ j, ∀ φ : Crys (divided₂ (GlobalTheory.FODef.sqZero k k)) (spMap (TrivSqZeroExt.fstHom k k k).toRingHom) o₀.A →ₗ[TrivSqZeroExt k k] Crys (divided₂ (GlobalTheory.FODef.sqZero k k)) (spMap (TrivSqZeroExt.fstHom k k k).toRingHom) o₀.A →ₗ[TrivSqZeroExt k k] TrivSqZeroExt k k, GlobalTheory.AbDual.IsCorrForm (divided₂ (GlobalTheory.FODef.sqZero k k)) (spMap (TrivSqZeroExt.fstHom k k k).toRingHom) o₀.A o₀.A o₀.P φ → ∀ x ∈ E' j, ∀ y ∈ E' j, φ x y = 0) → ∀ φ : Crys (divided₂ (GlobalTheory.FODef.sqZero k (Fin d → k))) (spMap (TrivSqZeroExt.fstHom k k (Fin d → k)).toRingHom) o₀.A →ₗ[TrivSqZeroExt k (Fin d → k)] Crys (divided₂ (GlobalTheory.FODef.sqZero k (Fin d → k))) (spMap (TrivSqZeroExt.fstHom k k (Fin d → k)).toRingHom) o₀.A →ₗ[TrivSqZeroExt k (Fin d → k)] TrivSqZeroExt k (Fin d → k), GlobalTheory.AbDual.IsCorrForm (divided₂ (GlobalTheory.FODef.sqZero k (Fin d → k))) (spMap (TrivSqZeroExt.fstHom k k (Fin d → k)).toRingHom) o₀.A o₀.A o₀.P φ → ∀ x ∈ GlobalTheory.HTGlue.glueFil o₀.A f, ∀ y ∈ GlobalTheory.HTGlue.glueFil o₀.A f, φ x y = 0 := by
  intro p _ D R _ b N k _ _ tk s o₀ _ d f E' _ _ h3 _ h5 φ hφ x hx y hy
  obtain ⟨x₀, hx₀, zx, hzx, hxc⟩ := hx
  obtain ⟨y₀, hy₀, zy, hzy, hyc⟩ := hy
  have t₀ := exists_red_form (k := k) (d := d) o₀.A o₀.P o₀.isLB φ hφ
  obtain ⟨φ₀, hφ₀, e₀⟩ := t₀
  have hfst : (φ x y).fst = 0 := by
    have cx := GlobalTheory.HTGlue.corr_of_fst o₀.A o₀.ab x x₀ fun c => by rw [hxc c]; simp
    have cy := GlobalTheory.HTGlue.corr_of_fst o₀.A o₀.ab y y₀ fun c => by rw [hyc c]; simp
    rw [← e₀ x x₀ y y₀ cx cy]
    exact fil_isotropic_of_isCorrForm o₀.A o₀.ab o₀.P o₀.isLB φ₀ hφ₀ x₀ hx₀ y₀ hy₀
  have hsnd : ∀ j, (φ x y).snd j = 0 := by
    intro j
    have t₁ := exists_proj_form (k := k) (d := d) o₀.A o₀.P o₀.isLB j φ hφ
    obtain ⟨φ', hφ', e'⟩ := t₁
    have t₂ := exists_mem_of_fil o₀.A (f j) (E' j) (h3 j) hx₀ (hzx j)
    obtain ⟨x', hx', hx'c⟩ := t₂
    have t₃ := exists_mem_of_fil o₀.A (f j) (E' j) (h3 j) hy₀ (hzy j)
    obtain ⟨y', hy', hy'c⟩ := t₃
    have cx := projMor_corr o₀.A o₀.ab j x x' fun c => by
      rw [hx'c c, hxc c]; ext <;> simp
    have cy := projMor_corr o₀.A o₀.ab j y y' fun c => by
      rw [hy'c c, hyc c]; ext <;> simp
    have e := e' x x' y y' cx cy
    have h0 : φ' x' y' = 0 := h5 j φ' hφ' x' hx' y' hy'
    have e2 : proj j (φ x y) = 0 := e.symm.trans h0
    have e3 : (proj j (φ x y)).snd = (0 : TrivSqZeroExt k k).snd := congrArg TrivSqZeroExt.snd e2
    rw [snd_proj] at e3
    exact e3
  exact TrivSqZeroExt.ext hfst (funext hsnd)

end GlobalTheory.HTGlueIso
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CrystalGluedHodgeGraphOrderStableOfDirectionsStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.UPel.Sm GlobalTheory.Cris GlobalTheory.DeRham
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.crystalGluedHodgeGraph_order_stable_of_directions : ∀ (p : ℕ) [Fact p.Prime] (D : GlobalTheory.UPel.HT.Datum p) (R : Type) [CommRing R] (b : GlobalTheory.UPel.HT.Base D R) (N : ℕ) (k : Type) [Field k] [IsAlgClosed k] (tk : R →+* k) (s : Sp k ⟶ Sp R) (o₀ : GlobalTheory.UPel.HT.Obj b N s), s = spMap tk → ∀ (d : ℕ) (f : Fin d → (HdR o₀.A →ₗ[k] HdR o₀.A)), ∀ (E' : Fin d → Submodule (TrivSqZeroExt k k) (Crys (divided₂ (GlobalTheory.FODef.sqZero k k)) (spMap (TrivSqZeroExt.fstHom k k k).toRingHom) o₀.A)), (∀ j, ∃ M : Submodule (TrivSqZeroExt k k) (Crys (divided₂ (GlobalTheory.FODef.sqZero k k)) (spMap (TrivSqZeroExt.fstHom k k k).toRingHom) o₀.A), IsCompl (E' j) M) → (∀ j, ∀ y : HdR o₀.A, y ∈ Fil o₀.A ↔ ∃ e ∈ E' j, (GlobalTheory.Published.GrothendieckMessing.crysRedMor (divided₂ (GlobalTheory.FODef.sqZero k k)) rfl o₀.A).Corr e y) → (∀ j, ∀ x ∈ Fil o₀.A, ∃ e ∈ E' j, ∀ c, e ((GlobalTheory.FODef.constMorV k k o₀.A).pull c) = TrivSqZeroExt.inl (x c) + TrivSqZeroExt.inr (f j x c)) → (∀ j (c : D.O), ∀ e ∈ E' j, (haveI := o₀.act.hom (c); push (divided₂ (GlobalTheory.FODef.sqZero k k)) (spMap (TrivSqZeroExt.fstHom k k k).toRingHom) (o₀.act.act (c)) (e)) ∈ E' j) → ∀ (c : D.O), ∀ e ∈ GlobalTheory.HTGlue.glueFil o₀.A f, (haveI := o₀.act.hom (c); push (divided₂ (GlobalTheory.FODef.sqZero k (Fin d → k))) (spMap (TrivSqZeroExt.fstHom k k (Fin d → k)).toRingHom) (o₀.act.act (c)) (e)) ∈ GlobalTheory.HTGlue.glueFil o₀.A f := by
  first | (exact @GlobalTheory.HTGlueOStab.glueFil_stable) | (exact GlobalTheory.HTGlueOStab.glueFil_stable) | (intros; apply GlobalTheory.HTGlueOStab.glueFil_stable <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DualNumberGraphFiltrationIsotropicOfSkewStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.UPel.Sm GlobalTheory.Cris GlobalTheory.DeRham
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.dualNumberGraphFiltration_isotropic_of_skew : ∀ (k : Type) [Field k] (A₀ : Over (Sp k)) [GrpObj A₀], IsAbelianScheme A₀ → ∀ (P : LB (A₀ ⊗ A₀).left), P.IsLB → ∀ (φ : LinearMap.BilinForm k (HdR A₀)), GlobalTheory.AbDual.IsCorrForm (dp0 k) (𝟙 _) A₀ A₀ P φ → ∀ f : HdR A₀ →ₗ[k] HdR A₀, (∀ x ∈ Fil A₀, ∀ y ∈ Fil A₀, φ (f x) y + φ x (f y) = 0) → ∀ φ' : Crys (epsDP k) (GlobalTheory.DeRham.epsRed k) A₀ →ₗ[DualNumber k] Crys (epsDP k) (GlobalTheory.DeRham.epsRed k) A₀ →ₗ[DualNumber k] DualNumber k, GlobalTheory.AbDual.IsCorrForm (epsDP k) (GlobalTheory.DeRham.epsRed k) A₀ A₀ P φ' → ∀ d ∈ GlobalTheory.HTRealise.graphFil A₀ f, ∀ d' ∈ GlobalTheory.HTRealise.graphFil A₀ f, φ' d d' = 0 := by
  first | (exact @GlobalTheory.HTRealise.graphFil_isotropic) | (exact GlobalTheory.HTRealise.graphFil_isotropic) | (intros; apply GlobalTheory.HTRealise.graphFil_isotropic <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DualNumberGraphFiltrationLieOfMapIntoHodgeStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.UPel.Sm GlobalTheory.Cris GlobalTheory.DeRham
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.dualNumberGraphFiltration_lie_of_map_into_hodge : ∀ (p : ℕ) [Fact p.Prime] (D : GlobalTheory.UPel.HT.Datum p) (R : Type) [CommRing R] (b : GlobalTheory.UPel.HT.Base D R) (N : ℕ) (k : Type) [Field k] (β : R →+* k) (s : Sp k ⟶ Sp R) (o₀ : GlobalTheory.UPel.HT.Obj b N s) (f : HdR o₀.A →ₗ[k] HdR o₀.A), GlobalTheory.HTCount.lieZ o₀ β ≤ Fil o₀.A → (∀ x ∈ GlobalTheory.HTCount.lieZ o₀ β, f x ∈ Fil o₀.A) → ∀ d : Crys (epsDP k) (GlobalTheory.DeRham.epsRed k) o₀.A, (haveI := o₀.act.hom (algebraMap (𝓞 D.F) D.O D.ω); push (epsDP k) (GlobalTheory.DeRham.epsRed k) (o₀.act.act (algebraMap (𝓞 D.F) D.O D.ω)) d) - algebraMap k (DualNumber k) (β b.ρ) • d ∈ GlobalTheory.HTRealise.graphFil o₀.A f → ∃ w : Fin D.a → Crys (epsDP k) (GlobalTheory.DeRham.epsRed k) o₀.A, (∀ i (c : 𝓞 D.F), (haveI := o₀.act.hom (algebraMap (𝓞 D.F) D.O c); push (epsDP k) (GlobalTheory.DeRham.epsRed k) (o₀.act.act (algebraMap (𝓞 D.F) D.O c)) (w i)) - algebraMap k (DualNumber k) (β (b.t i c)) • w i ∈ GlobalTheory.HTRealise.graphFil o₀.A f) ∧ d - ∑ i, w i ∈ GlobalTheory.HTRealise.graphFil o₀.A f := by
  first | (exact @GlobalTheory.HTRealise.eigen_decomp_graphFil) | (exact GlobalTheory.HTRealise.eigen_decomp_graphFil) | (intros; apply GlobalTheory.HTRealise.eigen_decomp_graphFil <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EvcPowRight
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Hecke GlobalTheory.UPel.HT.ES
open GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual

set_option autoImplicit false
noncomputable section

namespace GlobalTheory.UPel.HT.ES.KerFin

variable {p : ℕ} [Fact p.Prime] {D : Datum p} {R : Type} [CommRing R] {b : Base D R} {N : ℕ}

theorem evc_pow_right {S : Scheme.{0}} {s : S ⟶ Sp R} (o : Obj b N s) {T : Over S} (x y : T ⟶ o.A) (n : ℕ) :
    evc o.isLB x (y ^ n) = n • evc o.isLB x y := by
  obtain ⟨-, ad⟩ := GlobalTheory.BirigidRoot.additive_of_birigid o.ab o.isLB o.rig₁ o.rig₂
  induction n with
  | zero => rw [pow_zero, zero_smul]; exact evc_one_right o.isLB o.rig₂ x
  | succ n ih => rw [pow_succ, (GlobalTheory.BirigidLift.isAdditive_swap_iff o.isLB).1 ad, ih, succ_nsmul]

theorem evc_isog {S : Scheme.{0}} {s : S ⟶ Sp R} {c : ℕ} {o o' : Obj b N s} {ψ : o.A ⟶ o'.A}
    (h : IsPIsog c o o' ψ) {T : Over S} (x y : T ⟶ o.A) :
    evc o'.isLB (x ≫ ψ) (y ≫ ψ) = c • evc o.isLB x y := by
  obtain ⟨e⟩ := h.2.2.2.2.1
  have hQ : (Hecke.lbPow o.P c).IsLB := LB.isLB_linComb o.isLB _ _
  have hP : (ev o'.P (fst o.A o.A ≫ ψ) (snd o.A o.A ≫ ψ)).IsLB := pull_isLB o'.isLB _
  have e₁ : cls _ hQ = cls _ hP := (cls_eq_iff hQ hP).2 e
  have e₂ : cls _ hQ = c • cls o.P o.isLB := by
    refine (cls_linComb o.isLB _ _ hQ).trans ?_
    simp [pull_id]
  have z := evc_ev o'.isLB (fst o.A o.A ≫ ψ) (snd o.A o.A ≫ ψ) hP x y
  rw [lift_fst_assoc, lift_snd_assoc] at z
  rw [← z, evc, ← e₁, e₂, map_nsmul]
  rfl

theorem evc_adj {S : Scheme.{0}} {s : S ⟶ Sp R} {c : ℕ} {o o' : Obj b N s} {ψ : o.A ⟶ o'.A}
    (h : IsPIsog c o o' ψ) (ψ' : o'.A ⟶ o.A) [IsMonHom ψ'] (h' : ψ' ≫ ψ = (𝟙 o'.A) ^ c) {T : Over S}
    (x : T ⟶ o.A) (y : T ⟶ o'.A) : evc o'.isLB (x ≫ ψ) y = evc o.isLB x (y ≫ ψ') := by
  haveI := h.2.1
  obtain ⟨hfl, hsu, hqc⟩ := SiegUniqBase.flat_surjective_qc_pow S o'.A o'.ab c h.pos
  have key := GlobalTheory.BirigUniq.pic_eq_zero_of_fpqc o.A o'.A o'.A o.ab ((𝟙 o'.A) ^ c) hfl hsu hqc
    (evc o'.isLB (fst o.A o'.A ≫ ψ) (snd o.A o'.A) - evc o.isLB (fst o.A o'.A) (snd o.A o'.A ≫ ψ')) (by
      rw [map_sub, pull_evc, pull_evc, lift_fst_assoc, lift_fst, MonObj.one_comp,
        evc_one_left o'.isLB o'.rig₁, evc_one_left o.isLB o.rig₁, sub_self]) (by
      rw [map_sub, pull_evc, pull_evc, lift_fst_assoc, lift_fst, lift_snd, lift_snd_assoc, sub_eq_zero]
      have e₁ : (snd o.A o'.A ≫ (𝟙 o'.A) ^ c) ≫ ψ' = (snd o.A o'.A ≫ ψ') ^ c := by
        rw [MonObj.comp_pow, Category.comp_id, GlobalTheory.BirigidRoot.pow_comp_hom]
      rw [e₁, evc_pow_right, ← h', ← Category.assoc, evc_isog h])
  have z := congrArg (CechPic.pull (lift x y).left) (sub_eq_zero.1 key)
  rwa [pull_evc, pull_evc, lift_fst_assoc, lift_fst, lift_snd, lift_snd_assoc] at z

theorem evc_rosati {S : Scheme.{0}} {s : S ⟶ Sp R} (o : Obj b N s) (a : D.O) {T : Over S} (x y : T ⟶ o.A) :
    evc o.isLB (x ≫ o.act.act a) y = evc o.isLB x (y ≫ o.act.act (D.star a).unop) := by
  have h₁ : (ev o.P (fst o.A o.A ≫ o.act.act a) (snd o.A o.A)).IsLB := pull_isLB o.isLB _
  have h₂ : (ev o.P (fst o.A o.A) (snd o.A o.A ≫ o.act.act (D.star a).unop)).IsLB := pull_isLB o.isLB _
  have e := (cls_eq_iff h₁ h₂).2 (o.rosati a)
  have z₁ := evc_ev o.isLB _ _ h₁ x y
  have z₂ := evc_ev o.isLB _ _ h₂ x y
  rw [lift_fst_assoc, lift_snd] at z₁
  rw [lift_fst, lift_snd_assoc] at z₂
  rw [← z₁, ← z₂, evc, evc, e]

theorem mulN_eq_pow {S : Scheme.{0}} (A : Over S) [GrpObj A] (n : ℕ) : mulN A n = (𝟙 A) ^ n := by
  induction n with
  | zero => rw [pow_zero]; rfl
  | succ n ih => rw [pow_succ, ← ih]; rfl

theorem star_ker_le {k : Type} [CommRing k] {s : Sp k ⟶ Sp R} {c : ℕ} {o o₁ o₂ : Obj b N s} {ψ₁ : o.A ⟶ o₁.A}
    {ψ₂ : o.A ⟶ o₂.A} (h₁ : IsPIsog c o o₁ ψ₁) (h₂ : IsPIsog c o o₂ ψ₂) (a : D.O)
    (H : ∀ (T : Over (Sp k)) (x : T ⟶ o.A), x ≫ ψ₂ = 1 → (x ≫ o.act.act a) ≫ ψ₁ = 1)
    (T : Over (Sp k)) (x : T ⟶ o.A) (hx : x ≫ ψ₁ = 1) : (x ≫ o.act.act (D.star a).unop) ≫ ψ₂ = 1 := by
  haveI := h₁.2.1
  haveI := h₂.2.1
  haveI := o.act.hom a
  haveI := o.act.hom (D.star a).unop
  obtain ⟨φ₁, hφ₁, e₁, e₁'⟩ := h₁.2.2.2.2.2
  obtain ⟨φ₂, hφ₂, e₂, e₂'⟩ := h₂.2.2.2.2.2
  have hom_ext_spAlg {T B : Over (Sp k)} (a b : T ⟶ B)
      (h : ∀ (S : Type) [CommRing S] [Algebra k S] (g : GlobalTheory.PDiv.SpAlg k S ⟶ T), g ≫ a = g ≫ b) : a = b := by
    ext1
    apply T.left.affineOpenCover.openCover.hom_ext
    intro j
    let C : CommRingCat := T.left.affineOpenCover.X j
    let φ : CommRingCat.of k ⟶ C := Spec.preimage (T.left.affineOpenCover.f j ≫ T.hom)
    letI : Algebra k C := φ.hom.toAlgebra
    let g : GlobalTheory.PDiv.SpAlg k C ⟶ T := Over.homMk (T.left.affineOpenCover.f j) (by
      show _ = Spec.map (CommRingCat.ofHom (algebraMap k C))
      rw [← Spec.map_preimage (T.left.affineOpenCover.f j ≫ T.hom)]
      rfl)
    have := congrArg CommaMorphism.left (h C g)
    simp only [g, Over.comp_left, Over.homMk_left] at this
    exact this
  have factor (A B : Over (Sp k)) [GrpObj A] [GrpObj B] (hA : IsAbelianScheme A)
      (n : ℕ) (hn : 0 < n) (F : A ⟶ B) (hF : IsMonHom F)
      (hker : ∀ (S : Type) [CommRing S] [Algebra k S] (z : GlobalTheory.PDiv.SpAlg k S ⟶ A),
        z ^ n = 1 → z ≫ F = 1) : ∃ f : A ⟶ B, IsMonHom f ∧ F = mulN A n ≫ f := by
    haveI := hA.comm
    obtain ⟨hfin, hflat, hsurj⟩ := _root_.GlobalTheory.MulFlatSurj.finite_flat_surjective_mulN k A hA n hn
    haveI : IsMonHom (mulN A n) := GlobalTheory.MulEtaleDvr.isMonHom_mulN A n
    have hqc : QuasiCompact (mulN A n).left := inferInstance
    have h : ∀ (T : Over (Sp k)) (x : T ⟶ A), x ≫ mulN A n = 1 → x ≫ F = 1 := by
      intro T x hx
      apply hom_ext_spAlg
      intro S _ _ g
      have hxn : x ^ n = 1 := by
        rw [← hx, GlobalTheory.MulEtaleDvr.mulN_eq_pow, MonObj.comp_pow, Category.comp_id]
      have hz : (g ≫ x) ^ n = 1 := by
        rw [← MonObj.comp_pow, hxn, MonObj.comp_one]
      rw [← Category.assoc, hker S (g ≫ x) hz, MonObj.comp_one]
    obtain ⟨⟨ψ, hψ, hc⟩, -⟩ := exists_monHom_factor_of_flat_surjective _ A A B (mulN A n) F inferInstance hF
      hflat hsurj hqc h
    exact ⟨ψ, hψ, hc.symm⟩
  obtain ⟨β, hβ, eβ⟩ := factor o₂.A o₁.A o₂.ab c h₁.pos
    (φ₂ ≫ o.act.act a ≫ ψ₁) inferInstance (fun S _ _ z hz => by
      have := H _ (z ≫ φ₂) (by rw [Category.assoc, e₂', MonObj.comp_pow, Category.comp_id, hz])
      simpa only [Category.assoc] using this)
  rw [mulN_eq_pow] at eβ
  have hfac : φ₂ ≫ o.act.act a = β ≫ φ₁ := by
    obtain ⟨hfl, hsu, -⟩ := SiegUniqBase.flat_surjective_qc_pow _ o₂.A o₂.ab c h₁.pos
    haveI := hfl
    haveI := hsu
    haveI : Epi ((𝟙 o₂.A) ^ c).left := Flat.epi_of_flat_of_surjective _
    have e : (((𝟙 o₂.A) ^ c) ≫ φ₂ ≫ o.act.act a).left = (((𝟙 o₂.A) ^ c) ≫ β ≫ φ₁).left := by
      rw [← Category.assoc _ β, ← eβ, Category.assoc, Category.assoc, e₁, GlobalTheory.BirigidRoot.pow_comp_hom,
        Category.id_comp, ← Category.assoc, MonObj.comp_pow, Category.comp_id]
    rw [Over.comp_left, Over.comp_left] at e
    exact Over.OverMorphism.ext ((cancel_epi ((𝟙 o₂.A) ^ c).left).1 e)
  obtain ⟨e, he, hker⟩ := o₂.kerP
  set y := (x ≫ o.act.act (D.star a).unop) ≫ ψ₂ with hy
  have hye : y ^ e = 1 := by
    refine hker T y ((triv_ev_iff o₂.isLB _ _).2 ?_)
    rw [hy, ← Category.assoc, evc_adj h₂ φ₂ e₂', ← Category.assoc, evc_rosati, D.star_star, Category.assoc, hfac,
      ← Category.assoc, ← evc_adj h₁ φ₁ e₁', Category.assoc, hx, MonObj.comp_one]
    exact evc_one_left o₁.isLB o₁.rig₁ _
  have hyc : y ^ c = 1 := by
    have hxc : x ^ c = 1 := by
      rw [← Category.comp_id x, ← MonObj.comp_pow, ← e₁, ← Category.assoc, hx, MonObj.one_comp]
    rw [hy, ← GlobalTheory.BirigidRoot.pow_comp_hom, ← GlobalTheory.BirigidRoot.pow_comp_hom, hxc, MonObj.one_comp, MonObj.one_comp]
  obtain ⟨m, rfl⟩ := h₁.1
  have := pow_gcd_eq_one.2 ⟨hye, hyc⟩
  rwa [(Nat.Coprime.pow_right m he).gcd_eq_one, pow_one] at this

end GlobalTheory.UPel.HT.ES.KerFin
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsHeckeMapHarrisTaylorIntegralModels
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Hecke

namespace GlobalTheory.UPel.HT.Hecke

theorem exists_isHeckeMap : ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (R : Type) [CommRing R] [IsNoetherianRing R]
    (b : Base D R) (g : D.La →ₗ[D.O] D.La) (c k N : ℕ), c.Coprime p → k.Coprime p → 3 ≤ N → N.Coprime p →
    (∀ x y, D.EF (g x) (g y) = c * D.EF x y) → (∀ x, ∃ y, g y = k • x) → c ∣ k ^ 2 →
    ∀ (M : Model b N) (M' : Model b (N * k)), ∃ π : M'.X ⟶ M.X, IsHeckeMap g c k N M.toRepFam M'.toRepFam π := by
  intro p _ D R _ _ b g c k N hc hk hN hNp hEF hg hck M M'
  obtain ⟨o', ψ, hψ⟩ := GlobalTheory.T.exists_primeToP_hecke_translate_harrisTaylor p D R b g c k N hc hk hN hNp hEF hg hck M'.X M'.s M'.univ
  obtain ⟨π, ⟨hπ, hm⟩, -⟩ := M.toRepFam.rep M'.X M'.s o'
  exact ⟨π, hπ, o', ψ, hψ, hm⟩

end GlobalTheory.UPel.HT.Hecke
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIsComplCrystalGluedHodgeGraphFiltration
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.UPel.Sm GlobalTheory.Cris GlobalTheory.DeRham

noncomputable section

namespace GlobalTheory.HTGlue

theorem exists_isCompl_glueFil : ∀ (p : ℕ) [Fact p.Prime] (D : GlobalTheory.UPel.HT.Datum p) (R : Type) [CommRing R]
    (b : GlobalTheory.UPel.HT.Base D R) (N : ℕ) (k : Type) [Field k] [IsAlgClosed k] (tk : R →+* k) (s : Sp k ⟶ Sp R)
    (o₀ : GlobalTheory.UPel.HT.Obj b N s), s = spMap tk → ∀ (d : ℕ) (f : Fin d → (HdR o₀.A →ₗ[k] HdR o₀.A)),
    ∃ M : Submodule (TrivSqZeroExt k (Fin d → k))
      (Crys (divided₂ (GlobalTheory.FODef.sqZero k (Fin d → k))) (spMap (TrivSqZeroExt.fstHom k k (Fin d → k)).toRingHom) o₀.A),
      IsCompl (GlobalTheory.HTGlue.glueFil o₀.A f) M := by
  intro p _ D R _ b N k _ _ tk s o₀ _ d f
  obtain ⟨M₀, hM₀⟩ := Submodule.exists_isCompl (Fil o₀.A)
  exact ⟨_, isCompl_glueFil o₀.A o₀.ab f M₀ hM₀⟩

end GlobalTheory.HTGlue
end
end

