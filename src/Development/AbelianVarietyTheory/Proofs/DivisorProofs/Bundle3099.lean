module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3094
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsKSValueOneOfRetraction
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.SplitTori.SplitTorusAff
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1945
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3097
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2283
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3014
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2126
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0022
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3084
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2811
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3079
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0078
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0044
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.SABBaseChangeSt
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0007
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0060
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0071
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ToroidalCompactificationBis
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3095
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0007
public import Development.AbelianVarietyTheory.Definitions.Divisors.NotCompactOfMEqOne
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0003
public import Development.AbelianVarietyTheory.Definitions.Divisors.Rosati
public import Development.AbelianVarietyTheory.Definitions.Divisors.ToRingActOpOfRingAct
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0389
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0019
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0791
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0012
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3096

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CharpolyDeRhamHomologyEndomorphismEqMapLadicStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Cris GlobalTheory.DeRham
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.charpoly_deRhamHomology_endomorphism_eq_map_ladic : ∀ (k : Type) [Field k] [IsAlgClosed k] (A : Over (Sp k)) [GrpObj A] [IsCommMonObj A], IsAbelianScheme A →
    ∀ (f : A ⟶ A) [IsMonHom f] (L : Type) [AddCommGroup L] [Module.Free ℤ L] [Module.Finite ℤ L]
      (φ : L →ₗ[ℤ] L) (l : ℕ), l.Prime → (l : k) ≠ 0 →
      ∀ ev : ℕ → L → (Over.mk (𝟙 (Sp k)) ⟶ A),
      (∀ j x y, ev j (x + y) = ev j x * ev j y) →
      (∀ j x, ev j (φ x) = ev j x ≫ f) →
      (∀ j x, ev j x = 1 ↔ ∃ y, x = l ^ j • y) →
      (∀ j (q : Over.mk (𝟙 (Sp k)) ⟶ A), q ^ (l ^ j) = 1 ↔ ∃ x, ev j x = q) →
      ∀ [Module.Finite k (HdR A)],
        LinearMap.charpoly (push (dp0 k) (𝟙 _) f) = (LinearMap.charpoly φ).map (Int.castRingHom k) := by
  first | (exact @GlobalTheory.DeRham.charpoly_push_eq) | (exact GlobalTheory.DeRham.charpoly_push_eq) | (intros; apply GlobalTheory.DeRham.charpoly_push_eq  <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CrystalGluedHodgeGraphFiltrationHasComplement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.UPel.Sm GlobalTheory.Cris GlobalTheory.DeRham

noncomputable section

open scoped TensorProduct

namespace GlobalTheory.HTGlue

variable {k : Type} [Field k] {d : ℕ}

theorem crys_ext (A₀ : Over (Sp k)) [GrpObj A₀] (hA : IsAbelianScheme A₀)
    {e e' : Crys (divided₂ (GlobalTheory.FODef.sqZero k (Fin d → k))) (spMap (TrivSqZeroExt.fstHom k k (Fin d → k)).toRingHom) A₀}
    (h : ∀ c, e ((GlobalTheory.FODef.constMorV k (Fin d → k) A₀).pull c) =
      e' ((GlobalTheory.FODef.constMorV k (Fin d → k) A₀).pull c)) : e = e' := by
  have hm := GlobalTheory.SqZeroCrys.isBC_trivSqZeroExt k (Fin d → k) A₀ hA (GlobalTheory.FODef.sqZero k (Fin d → k))
    (GlobalTheory.FODef.constMorV k (Fin d → k) A₀)
  let eqv := LinearEquiv.ofBijective _ hm
  have h1 : ∀ c, (GlobalTheory.FODef.constMorV k (Fin d → k) A₀).pull c = eqv (1 ⊗ₜ c) := fun c =>
    (one_smul (TrivSqZeroExt k (Fin d → k)) ((GlobalTheory.FODef.constMorV k (Fin d → k) A₀).pull c)).symm
  have key : e ∘ₗ eqv.toLinearMap = e' ∘ₗ eqv.toLinearMap := by
    refine TensorProduct.AlgebraTensorModule.ext fun r c => ?_
    have hr : (r ⊗ₜ c : TrivSqZeroExt k (Fin d → k) ⊗[k] primDR A₀) = r • (1 ⊗ₜ c) := by
      rw [TensorProduct.smul_tmul', smul_eq_mul, _root_.mul_one]
    simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, hr, map_smul, ← h1, h c]
  refine LinearMap.ext fun y => ?_
  obtain ⟨t, rfl⟩ := eqv.surjective y
  exact LinearMap.congr_fun key t

theorem crys_pull_smul (A₀ : Over (Sp k)) [GrpObj A₀]
    (e : Crys (divided₂ (GlobalTheory.FODef.sqZero k (Fin d → k))) (spMap (TrivSqZeroExt.fstHom k k (Fin d → k)).toRingHom) A₀)
    (a : k) (c : primDR A₀) :
    e ((GlobalTheory.FODef.constMorV k (Fin d → k) A₀).pull (a • c)) =
      TrivSqZeroExt.inl a * e ((GlobalTheory.FODef.constMorV k (Fin d → k) A₀).pull c) := by
  rw [LinearMap.map_smulₛₗ]
  exact e.map_smul (algebraMap k (TrivSqZeroExt k (Fin d → k)) a) ((GlobalTheory.FODef.constMorV k (Fin d → k) A₀).pull c)

theorem crys_pull_add (A₀ : Over (Sp k)) [GrpObj A₀]
    (e : Crys (divided₂ (GlobalTheory.FODef.sqZero k (Fin d → k))) (spMap (TrivSqZeroExt.fstHom k k (Fin d → k)).toRingHom) A₀)
    (a b : primDR A₀) :
    e ((GlobalTheory.FODef.constMorV k (Fin d → k) A₀).pull (a + b)) =
      e ((GlobalTheory.FODef.constMorV k (Fin d → k) A₀).pull a) + e ((GlobalTheory.FODef.constMorV k (Fin d → k) A₀).pull b) := by
  rw [LinearMap.map_add (f := _)]
  exact e.map_add _ _

def fstVal (A₀ : Over (Sp k)) [GrpObj A₀]
    (e : Crys (divided₂ (GlobalTheory.FODef.sqZero k (Fin d → k))) (spMap (TrivSqZeroExt.fstHom k k (Fin d → k)).toRingHom) A₀) :
    HdR A₀ where
  toFun c := (e ((GlobalTheory.FODef.constMorV k (Fin d → k) A₀).pull c)).fst
  map_add' a b := by
    rw [crys_pull_add]
    rfl
  map_smul' a c := by
    rw [crys_pull_smul]
    simp

def sndVal (A₀ : Over (Sp k)) [GrpObj A₀]
    (e : Crys (divided₂ (GlobalTheory.FODef.sqZero k (Fin d → k))) (spMap (TrivSqZeroExt.fstHom k k (Fin d → k)).toRingHom) A₀)
    (j : Fin d) : HdR A₀ where
  toFun c := (e ((GlobalTheory.FODef.constMorV k (Fin d → k) A₀).pull c)).snd j
  map_add' a b := by
    rw [crys_pull_add]
    rfl
  map_smul' a c := by
    rw [crys_pull_smul]
    simp

def constSub (A₀ : Over (Sp k)) [GrpObj A₀] (S : Submodule k (HdR A₀)) :
    Submodule (TrivSqZeroExt k (Fin d → k))
      (Crys (divided₂ (GlobalTheory.FODef.sqZero k (Fin d → k))) (spMap (TrivSqZeroExt.fstHom k k (Fin d → k)).toRingHom) A₀) where
  carrier := {e | ∃ x ∈ S, ∃ z : Fin d → HdR A₀, (∀ j, z j ∈ S) ∧
      ∀ c : primDR A₀, e ((GlobalTheory.FODef.constMorV k (Fin d → k) A₀).pull c) =
        TrivSqZeroExt.inl (x c) + TrivSqZeroExt.inr (fun j => z j c)}
  add_mem' := by
    rintro e e' ⟨x, hx, z, hz, he⟩ ⟨x', hx', z', hz', he'⟩
    refine ⟨x + x', add_mem hx hx', z + z', fun j => add_mem (hz j) (hz' j), fun c => ?_⟩
    rw [LinearMap.add_apply, he c, he' c]
    ext
    · simp
    · simp only [TrivSqZeroExt.snd_add, TrivSqZeroExt.snd_inl, TrivSqZeroExt.snd_inr, Pi.add_apply,
        LinearMap.add_apply, zero_add, add_zero, Pi.zero_apply]
  zero_mem' := ⟨0, zero_mem _, 0, fun _ => zero_mem _, fun c => by rw [LinearMap.zero_apply]; ext <;> simp⟩
  smul_mem' := by
    rintro r e ⟨x, hx, z, hz, he⟩
    refine ⟨r.fst • x, Submodule.smul_mem _ _ hx, fun j => r.fst • z j + r.snd j • x,
      fun j => add_mem (Submodule.smul_mem _ _ (hz j)) (Submodule.smul_mem _ _ hx), fun c => ?_⟩
    rw [LinearMap.smul_apply, he c, smul_eq_mul]
    ext
    · simp
    · simp only [TrivSqZeroExt.snd_mul, TrivSqZeroExt.fst_add, TrivSqZeroExt.fst_inl, TrivSqZeroExt.fst_inr,
        TrivSqZeroExt.snd_add, TrivSqZeroExt.snd_inl, TrivSqZeroExt.snd_inr, Pi.add_apply, Pi.smul_apply,
        LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul, add_zero, zero_add,
        MulOpposite.smul_eq_mul_unop, MulOpposite.unop_op, Pi.zero_apply]


set_option maxHeartbeats 1000000 in
theorem mem_sup_of_coords (A₀ : Over (Sp k)) [GrpObj A₀] (hA : IsAbelianScheme A₀)
    (f : Fin d → (HdR A₀ →ₗ[k] HdR A₀)) (M₀ : Submodule k (HdR A₀))
    (e : Crys (divided₂ (GlobalTheory.FODef.sqZero k (Fin d → k))) (spMap (TrivSqZeroExt.fstHom k k (Fin d → k)).toRingHom) A₀)
    (x₁ m : HdR A₀) (hx₁ : x₁ ∈ Fil A₀) (hm : m ∈ M₀) (hxm : ∀ c, x₁ c + m c = (e ((GlobalTheory.FODef.constMorV k (Fin d → k) A₀).pull c)).fst)
    (z w : Fin d → HdR A₀) (hz : ∀ j, z j ∈ Fil A₀) (hw : ∀ j, w j ∈ M₀)
    (hzw : ∀ j c, z j c + w j c = (e ((GlobalTheory.FODef.constMorV k (Fin d → k) A₀).pull c)).snd j - f j x₁ c) :
    e ∈ glueFil A₀ f ⊔ constSub A₀ M₀ := by
  obtain ⟨g, hg⟩ := exists_coords (Fin d → k) A₀ hA
    ((Algebra.linearMap k (TrivSqZeroExt k (Fin d → k))) ∘ₗ x₁ + (TrivSqZeroExt.inrHom k (Fin d → k)) ∘ₗ
      LinearMap.pi fun j => f j x₁ + z j)
  have hgv : ∀ c, g ((GlobalTheory.FODef.constMorV k (Fin d → k) A₀).pull c) =
      TrivSqZeroExt.inl (x₁ c) + TrivSqZeroExt.inr (fun j => (f j x₁ + z j) c) := fun c => by
    rw [hg c]; ext <;> simp [TrivSqZeroExt.algebraMap_eq_inl]
  have hgm : g ∈ glueFil A₀ f := ⟨x₁, hx₁, z, hz, hgv⟩
  obtain ⟨h, hh⟩ := exists_coords (Fin d → k) A₀ hA
    ((Algebra.linearMap k (TrivSqZeroExt k (Fin d → k))) ∘ₗ m + (TrivSqZeroExt.inrHom k (Fin d → k)) ∘ₗ
      LinearMap.pi fun j => w j)
  have hhv : ∀ c, h ((GlobalTheory.FODef.constMorV k (Fin d → k) A₀).pull c) =
      TrivSqZeroExt.inl (m c) + TrivSqZeroExt.inr (fun j => w j c) := fun c => by
    rw [hh c]; ext <;> simp [TrivSqZeroExt.algebraMap_eq_inl]
  have hhm : h ∈ constSub A₀ M₀ := ⟨m, hm, w, hw, hhv⟩
  refine Submodule.mem_sup.2 ⟨g, hgm, h, hhm, crys_ext A₀ hA fun c => ?_⟩
  rw [LinearMap.add_apply, hgv c, hhv c]
  ext
  · simp only [TrivSqZeroExt.fst_add, TrivSqZeroExt.fst_inl, TrivSqZeroExt.fst_inr, add_zero, hxm c]
  · rename_i j
    simp only [TrivSqZeroExt.snd_add, TrivSqZeroExt.snd_inl, TrivSqZeroExt.snd_inr,
      Pi.add_apply, zero_add, LinearMap.add_apply]
    linear_combination (hzw j c)

theorem isCompl_glueFil (A₀ : Over (Sp k)) [GrpObj A₀] (hA : IsAbelianScheme A₀)
    (f : Fin d → (HdR A₀ →ₗ[k] HdR A₀)) (M₀ : Submodule k (HdR A₀)) (hM : IsCompl (Fil A₀) M₀) :
    IsCompl (glueFil A₀ f) (constSub (d := d) A₀ M₀) := by
  constructor
  · rw [Submodule.disjoint_def]
    rintro e ⟨x, hx, z, hz, he⟩ ⟨m, hm, w, hw, he'⟩
    have hxm : x = m := LinearMap.ext fun c => by
      have := congrArg TrivSqZeroExt.fst ((he c).symm.trans (he' c))
      simpa using this
    have hx0 : x = 0 := by
      rw [← Submodule.mem_bot k, ← hM.inf_eq_bot]
      exact ⟨hx, hxm ▸ hm⟩
    have hzw : ∀ j, z j = w j := fun j => LinearMap.ext fun c => by
      have := congrFun (congrArg TrivSqZeroExt.snd ((he c).symm.trans (he' c))) j
      simpa [hx0] using this
    have hz0 : ∀ j, z j = 0 := fun j => by
      rw [← Submodule.mem_bot k, ← hM.inf_eq_bot]
      exact ⟨hz j, (hzw j) ▸ hw j⟩
    refine crys_ext A₀ hA fun c => ?_
    rw [he c, LinearMap.zero_apply]
    ext <;> simp [hx0, hz0]
  · rw [codisjoint_iff, eq_top_iff]
    rintro e -
    have hdec : ∀ u : HdR A₀, ∃ a ∈ Fil A₀, ∃ b ∈ M₀, a + b = u := fun u => by
      have hu : u ∈ Fil A₀ ⊔ M₀ := by rw [hM.sup_eq_top]; trivial
      rw [Submodule.mem_sup] at hu
      exact hu
    choose pa hpa pb hpb hpab using hdec
    exact mem_sup_of_coords A₀ hA f M₀ e _ _ (hpa _) (hpb _) (fun c => LinearMap.congr_fun (hpab (fstVal A₀ e)) c)
      (fun j => pa (sndVal A₀ e j - f j (pa (fstVal A₀ e))))
      (fun j => pb (sndVal A₀ e j - f j (pa (fstVal A₀ e)))) (fun _ => hpa _) (fun _ => hpb _)
      (fun j c => LinearMap.congr_fun (hpab (sndVal A₀ e j - f j (pa (fstVal A₀ e)))) c)

end GlobalTheory.HTGlue


open GlobalTheory.HTGlue in
theorem GlobalTheory.HTGlue.glueFil_hasCompl : ∀ (p : ℕ) [Fact p.Prime] (D : GlobalTheory.UPel.HT.Datum p) (R : Type) [CommRing R] (b : GlobalTheory.UPel.HT.Base D R) (N : ℕ), 3 ≤ N → N.Coprime p → ∀ (k : Type) [Field k] [IsAlgClosed k] (t : Sp k ⟶ Sp R) (o₀ : GlobalTheory.UPel.HT.Obj b N t) (β : R →+* k), t = spMap β → ∀ φ : LinearMap.BilinForm k (HdR o₀.A), GlobalTheory.AbDual.IsCorrForm (dp0 k) (𝟙 _) o₀.A o₀.A o₀.P φ → ∀ (d : ℕ) (f : Fin d → (HdR o₀.A →ₗ[k] HdR o₀.A)), (∀ j, IsKS (GlobalTheory.HTCount.crysAct o₀) φ (Fil o₀.A) (GlobalTheory.HTCount.lieZ o₀ β) (f j)) → (∃ M : Submodule (TrivSqZeroExt k (Fin d → k)) (Crys (divided₂ (GlobalTheory.FODef.sqZero k (Fin d → k))) (spMap (TrivSqZeroExt.fstHom k k (Fin d → k)).toRingHom) o₀.A), IsCompl (GlobalTheory.HTGlue.glueFil o₀.A f) M) := by
  intro p _ D R _ b N _ _ k _ _ t o₀ β _ φ _ d f _
  obtain ⟨M₀, hM⟩ := Submodule.exists_isCompl (Fil o₀.A)
  exact ⟨_, isCompl_glueFil o₀.A o₀.ab f M₀ hM⟩
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CrystalGluedHodgeGraphFiltrationIsotropicPolaris
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.UPel.Sm GlobalTheory.Cris GlobalTheory.DeRham

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.HTGlueIsoPol

open GlobalTheory.AbDual

section
variable {R R' : Type} [CommRing R] [CommRing R'] [Algebra R R'] {I : Ideal R} {I' : Ideal R'}
  {S S' : Scheme.{0}} {κ : DividedPowers I} {t : S ⟶ Sp R} {A : Over S} [GrpObj A]
  {κ' : DividedPowers I'} {t' : S' ⟶ Sp R'} {A' : Over S'} [GrpObj A']
  {b : S' ⟶ S} {φ : A'.left ⟶ A.left} {m : GrpMor κ t A κ' t' A' (algebraMap R R') b φ}

theorem ext_of_isBC (hm : m.IsBC) {h₁ h₂ : Crys κ' t' A'} (e : ∀ c, h₁ (m.pull c) = h₂ (m.pull c)) :
    h₁ = h₂ := by
  refine LinearMap.ext fun c ↦ ?_
  obtain ⟨z, rfl⟩ := hm.2 c
  induction z with
  | add x y hx hy => simp only [map_add (f := _), hx, hy]
  | tmul x c => rw [liftSemi_tmul, map_smul, map_smul, e c]


omit [Algebra R R'] in
theorem crys_sum_apply {J : Type} (s : Finset J) (g : J → Crys κ' t' A') (q : prim κ' t' A') :
    (∑ i ∈ s, g i) q = ∑ i ∈ s, g i q := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, LinearMap.add_apply, ih]

theorem bcMap_pull (hm : m.IsBC) (h : Crys κ t A) (c : prim κ t A) :
    hm.bcMap h (m.pull c) = algebraMap R R' (h c) :=
  (hm.corr_iff (h := h)).2 rfl c


omit [Algebra R R'] in
theorem crys_add_apply (g g' : Crys κ' t' A') (q : prim κ' t' A') : (g + g') q = g q + g' q :=
  LinearMap.add_apply g g' q


omit [Algebra R R'] in
theorem crys_smul_apply (r : R') (g : Crys κ' t' A') (q : prim κ' t' A') : (r • g) q = r * g q :=
  LinearMap.smul_apply r g q
end

theorem tsze_coords {k : Type} [Field k] {d : ℕ} (a : k) (v : Fin d → k) :
    (TrivSqZeroExt.inl a + TrivSqZeroExt.inr v : TrivSqZeroExt k (Fin d → k)) =
      algebraMap k _ a + ∑ j, TrivSqZeroExt.inr (Pi.single j 1) * algebraMap k _ (v j) := by
  ext
  · simp [TrivSqZeroExt.algebraMap_eq_inl, TrivSqZeroExt.fst_sum]
  · simp [TrivSqZeroExt.algebraMap_eq_inl, TrivSqZeroExt.snd_sum, Finset.sum_apply, Pi.single_apply]

theorem glue_pairing_eq_zero {k : Type} [Field k] {d : ℕ} {H M : Type*} [AddCommGroup H] [Module k H]
    [AddCommGroup M] [Module (TrivSqZeroExt k (Fin d → k)) M]
    (bc : H →ₛₗ[algebraMap k (TrivSqZeroExt k (Fin d → k))] M)
    (Φ : M →ₗ[TrivSqZeroExt k (Fin d → k)] M →ₗ[TrivSqZeroExt k (Fin d → k)] TrivSqZeroExt k (Fin d → k))
    (φ : LinearMap.BilinForm k H) (key : ∀ u v, Φ (bc u) (bc v) = algebraMap k _ (φ u v))
    {x y : H} {u v : Fin d → H} (hxy : φ x y = 0) (huv : ∀ j, φ (u j) y + φ x (v j) = 0) :
    Φ (bc x + ∑ j, (TrivSqZeroExt.inr (Pi.single j 1) : TrivSqZeroExt k (Fin d → k)) • bc (u j))
      (bc y + ∑ j, (TrivSqZeroExt.inr (Pi.single j 1) : TrivSqZeroExt k (Fin d → k)) • bc (v j)) = 0 := by
  have hee : ∀ (j l : Fin d) (r : TrivSqZeroExt k (Fin d → k)),
      (TrivSqZeroExt.inr (Pi.single j 1) : TrivSqZeroExt k (Fin d → k)) * (TrivSqZeroExt.inr (Pi.single l 1) * r) = 0 :=
    fun j l r ↦ by rw [← _root_.mul_assoc, TrivSqZeroExt.inr_mul_inr, MulZeroClass.zero_mul]
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [map_add (f := _), map_sum, map_smul, LinearMap.add_apply, LinearMap.sum_apply, LinearMap.smul_apply, key,
    smul_eq_mul, Finset.mul_sum, mul_add, hee, Finset.sum_const_zero, add_zero, hxy, map_zero, zero_add]
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_eq_zero fun j _ ↦ ?_
  rw [← mul_add, ← map_add (f := _), huv j, map_zero, mul_zero]


set_option maxHeartbeats 4000000 in
theorem glueFil_isotropic : ∀ (p : ℕ) [Fact p.Prime] (D : GlobalTheory.UPel.HT.Datum p) (R : Type) [CommRing R] (b : GlobalTheory.UPel.HT.Base D R) (N : ℕ), 3 ≤ N → N.Coprime p → ∀ (k : Type) [Field k] [IsAlgClosed k] (t : Sp k ⟶ Sp R) (o₀ : GlobalTheory.UPel.HT.Obj b N t) (β : R →+* k), t = spMap β → ∀ φ : LinearMap.BilinForm k (HdR o₀.A), GlobalTheory.AbDual.IsCorrForm (dp0 k) (𝟙 _) o₀.A o₀.A o₀.P φ → ∀ (d : ℕ) (f : Fin d → (HdR o₀.A →ₗ[k] HdR o₀.A)), (∀ j, IsKS (GlobalTheory.HTCount.crysAct o₀) φ (Fil o₀.A) (GlobalTheory.HTCount.lieZ o₀ β) (f j)) → (∀ Φ : Crys (divided₂ (GlobalTheory.FODef.sqZero k (Fin d → k))) (spMap (TrivSqZeroExt.fstHom k k (Fin d → k)).toRingHom) o₀.A →ₗ[(TrivSqZeroExt k (Fin d → k))] Crys (divided₂ (GlobalTheory.FODef.sqZero k (Fin d → k))) (spMap (TrivSqZeroExt.fstHom k k (Fin d → k)).toRingHom) o₀.A →ₗ[(TrivSqZeroExt k (Fin d → k))] (TrivSqZeroExt k (Fin d → k)), GlobalTheory.AbDual.IsCorrForm (divided₂ (GlobalTheory.FODef.sqZero k (Fin d → k))) (spMap (TrivSqZeroExt.fstHom k k (Fin d → k)).toRingHom) o₀.A o₀.A o₀.P Φ → ∀ x ∈ (GlobalTheory.HTGlue.glueFil o₀.A f), ∀ y ∈ (GlobalTheory.HTGlue.glueFil o₀.A f), Φ x y = 0) := by
  intro p _ D R _ b N hN hNp k _ _ t o₀ β hβ φ hφ d f hf Φ hΦ X hX Y hY
  have h2 := GlobalTheory.FODef.sqZero k (Fin d → k)
  have hA := o₀.ab
  obtain ⟨g, hg⟩ := GlobalTheory.AbelianDim.exists_relDim k o₀.A hA
  obtain ⟨A, _, i, hi, hAC, hgC⟩ := GlobalTheory.abelianScheme_constLift (TrivSqZeroExt k (Fin d → k)) k
    (TrivSqZeroExt.fstHom k k (Fin d → k)).toRingHom (algebraMap k (TrivSqZeroExt k (Fin d → k)))
    (by ext; simp [TrivSqZeroExt.algebraMap_eq_inl]) o₀.A g hA hg
  have ADR := GlobalTheory.abelianDeRham
  have ADC := GlobalTheory.abelianDualCrystal_of_dualAbelianScheme GlobalTheory.dualAbelianScheme
  have CS := GlobalTheory.Published.AbelianDualCrystal.cupSquare_crys_prod ADR.1 ADC.2 (isDPNilpotent_squareZero h2)
    (fun r ↦ ⟨TrivSqZeroExt.inl r, rfl⟩) rfl hAC hgC hAC hgC hi hi
  have m := GlobalTheory.FODef.constMorV k (Fin d → k) o₀.A
  have hBC : m.IsBC := GlobalTheory.SqZeroCrys.isBC_trivSqZeroExt k (Fin d → k) o₀.A hA _ m
  have hP := o₀.isLB
  have e0 : LBIso (o₀.P.pull (𝟙 _)) o₀.P := by
    first
      | exact LBIso.chartPull (chartPullPull o₀.P (𝟙 _)) (chartPullId o₀.P) (PolBaseChange.lbIso_refl hP)
      | exact LBIso.chartPull (chartPullPull o₀.P (𝟙 _)) (chartPullId o₀.P) (ChernExists.lbIso_refl hP)
  obtain ⟨Ψ, hΨ, hΨc⟩ := hφ.pull hP m m (h := 𝟙 _) (by simp) (by simp) hP e0
  obtain rfl := hΦ.unique CS hP hΨ

  have key : ∀ u v : HdR o₀.A, Φ (hBC.bcMap u) (hBC.bcMap v) = algebraMap k _ (φ u v) := fun u v ↦
    hΨc u _ v _ ((hBC.corr_iff (h := u)).2 rfl) ((hBC.corr_iff (h := v)).2 rfl)

  have dec : ∀ Z ∈ GlobalTheory.HTGlue.glueFil o₀.A f, ∃ x ∈ Fil o₀.A, ∃ z : Fin d → HdR o₀.A, (∀ j, z j ∈ Fil o₀.A) ∧
      Z = hBC.bcMap x + ∑ j, (TrivSqZeroExt.inr (Pi.single j 1) : TrivSqZeroExt k (Fin d → k)) •
        hBC.bcMap (f j x + z j) := by
    rintro Z ⟨x, hx, z, hz, hZ⟩
    refine ⟨x, hx, z, hz, ext_of_isBC hBC fun c ↦ ?_⟩
    rw [hZ c, tsze_coords, crys_add_apply]
    refine (congrArg₂ (· + ·) (bcMap_pull hBC x c) ?_).symm
    exact (crys_sum_apply _ _ _).trans (Finset.sum_congr rfl fun j _ ↦
      (crys_smul_apply _ _ _).trans (congrArg _ (bcMap_pull hBC _ c)))
  have iso := (GlobalTheory.HTLagr.fil_lagrangian p D R b N k t o₀ φ ⟨g, hg⟩ hφ).1
  refine (dec X hX).elim fun x hx' ↦ (dec Y hY).elim fun y hy' ↦ ?_
  refine hx'.2.elim fun z hz' ↦ hy'.2.elim fun w hw' ↦ ?_
  refine (congrArg₂ (fun a b ↦ Φ a b) hz'.2 hw'.2).trans ?_
  refine glue_pairing_eq_zero hBC.bcMap Φ φ key (iso x hx'.1 y hy'.1) fun j ↦ ?_
  simp only [map_add (f := _), LinearMap.add_apply, iso _ (hz'.1 j) _ hy'.1, iso _ hx'.1 _ (hw'.1 j), add_zero]
  exact (hf j).2.2 x hx'.1 y hy'.1

end GlobalTheory.HTGlueIsoPol
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CrystalGluedHodgeGraphFiltrationOrderStable
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.UPel.Sm GlobalTheory.Cris GlobalTheory.DeRham

noncomputable section

namespace GlobalTheory.HTGlue

theorem primPull_constMorV_pull {k : Type} [Field k] (V : Type) [AddCommGroup V] [Module k V] [Module kᵐᵒᵖ V]
    [IsCentralScalar k V] (A₀ : Over (Sp k)) [GrpObj A₀] (g : A₀ ⟶ A₀) [IsMonHom g] (q : primDR A₀) :
    primPull (divided₂ (GlobalTheory.FODef.sqZero k V)) (spMap (TrivSqZeroExt.fstHom k k V).toRingHom) g
        ((GlobalTheory.FODef.constMorV k V A₀).pull q) =
      (GlobalTheory.FODef.constMorV k V A₀).pull (primPull (dp0 k) (𝟙 _) g q) := by
  apply Subtype.ext
  have K := (homMor (dp0 k) (𝟙 _) g).isMor.comp (GlobalTheory.FODef.constMorV k V A₀).isMor
  have e1 := IsMor.pullback1_comp (GlobalTheory.FODef.constMorV k V A₀).isMor
    (homMor (divided₂ (GlobalTheory.FODef.sqZero k V)) (spMap (TrivSqZeroExt.fstHom k k V).toRingHom) g).isMor K
    (fun _ ↦ rfl) (by simp) q.1
  have e2 := IsMor.pullback1_comp (homMor (dp0 k) (𝟙 _) g).isMor (GlobalTheory.FODef.constMorV k V A₀).isMor K
    (fun _ ↦ rfl) rfl q.1
  exact e1.trans e2.symm

theorem push_mem_glueFil : ∀ (p : ℕ) [Fact p.Prime] (D : GlobalTheory.UPel.HT.Datum p) (R : Type) [CommRing R] (b : GlobalTheory.UPel.HT.Base D R) (N : ℕ), 3 ≤ N → N.Coprime p → ∀ (k : Type) [Field k] [IsAlgClosed k] (t : Sp k ⟶ Sp R) (o₀ : GlobalTheory.UPel.HT.Obj b N t) (β : R →+* k), t = spMap β → ∀ φ : LinearMap.BilinForm k (HdR o₀.A), GlobalTheory.AbDual.IsCorrForm (dp0 k) (𝟙 _) o₀.A o₀.A o₀.P φ → ∀ (d : ℕ) (f : Fin d → (HdR o₀.A →ₗ[k] HdR o₀.A)), (∀ j, IsKS (GlobalTheory.HTCount.crysAct o₀) φ (Fil o₀.A) (GlobalTheory.HTCount.lieZ o₀ β) (f j)) → (∀ (c : D.O), ∀ e ∈ (GlobalTheory.HTGlue.glueFil o₀.A f), (haveI := o₀.act.hom (c); push (divided₂ (GlobalTheory.FODef.sqZero k (Fin d → k))) (spMap (TrivSqZeroExt.fstHom k k (Fin d → k)).toRingHom) (o₀.act.act (c)) (e)) ∈ (GlobalTheory.HTGlue.glueFil o₀.A f)) := by
  intro p _ D R _ b N _ _ k _ _ t o₀ β _ φ _ d f hf c e he
  haveI := o₀.act.hom c
  obtain ⟨x, hx, z, hz, hxz⟩ := he
  let g : HdR o₀.A →ₗ[k] HdR o₀.A := GlobalTheory.HTCount.crysAct o₀ c
  have hg : ∀ h, g h = push (dp0 k) (𝟙 _) (o₀.act.act c) h := fun _ ↦ rfl
  refine ⟨g x, push_mem_Fil _ hx, fun j ↦ g (z j) - (f j (g x) - g (f j x)),
    fun j ↦ sub_mem (push_mem_Fil _ (hz j)) ((hf j).1 c x hx), fun q ↦ ?_⟩
  rw [push_apply, primPull_constMorV_pull, hxz]
  congr 2
  funext j
  rw [← push_apply, ← hg]
  simp only [map_add (f := _), LinearMap.add_apply, LinearMap.sub_apply, map_sub]
  abel

end GlobalTheory.HTGlue
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DeRhamHomologyClosedFibreSurjectiveKernelStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.UPel GlobalTheory.UPel.Sm GlobalTheory.Cris GlobalTheory.DeRham
open scoped TensorProduct
attribute [local instance] Functor.grpObjObj
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.deRhamHomology_closedFibre_surjective_kernel : ∀ (C₀ : Type) [CommRing C₀] [IsLocalRing C₀] (A₀ : Over (Sp C₀)) [GrpObj A₀] [IsCommMonObj A₀], IsAbelianScheme A₀ → ∀ (O : Type) [CommRing O] (a : OAct O A₀), ∃ f : HdR A₀ →ₛₗ[algebraMap C₀ (IsLocalRing.ResidueField C₀)] HdR ((Over.pullback (spMap (algebraMap C₀ (IsLocalRing.ResidueField C₀)))).obj A₀), Function.Surjective f ∧ (∀ h, f h = 0 → h ∈ IsLocalRing.maximalIdeal C₀ • (⊤ : Submodule C₀ (HdR A₀))) ∧ ∀ (x : O) (h : HdR A₀), f (act (dp0 C₀) (𝟙 _) a x h) = act (dp0 (IsLocalRing.ResidueField C₀)) (𝟙 _) (OAct.pullback (spMap (algebraMap C₀ (IsLocalRing.ResidueField C₀))) A₀ a) x (f h) := by
  first | (exact @GlobalTheory.HdRFibre.fibre_baseChange) | (exact GlobalTheory.HdRFibre.fibre_baseChange) | (intros; apply GlobalTheory.HdRFibre.fibre_baseChange  <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DegenerationDataConstantOfFlatHeatOperatorsStatement
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj Matrix TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.KS (rsT pbT C1 IsCoc IsCob)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.RayEv (Ray)
open GlobalTheory.Toroidal GlobalTheory.LogKS GlobalTheory.RigChart GlobalTheory.Heat
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.degenerationData_constant_of_flat_heatOperators : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (k : Type) [Field k] [CharZero k] (m d : ℕ) (t : SAB H (Sp (ChartRing k m d))) (P : PELUnif (maximalIdeal (ChartRing k m d)) t) (gam : Fin m → LinearMap.BilinForm ℤ P.D.toPre.X), IsMonomial P.D.toPre (bdParam k m d) gam → LinearIndependent ℤ gam → (∀ p : Sp (ChartRing k m d), p ∈ abLocus t.G ↔ ∏ i, bdParam k m d i ∉ p.asIdeal) → letI := H.starRing; ∀ (Y : Ray P.oD) (n' : ℕ) (v' : Module.Basis (Fin n') (ChartRing k m d) (TanM (𝟙 (Sp (ChartRing k m d))) Y.H)) (dd : Fin n' → Fld Y.H.left), (∀ a, IsInv Y.H (v' a) (dd a)) → ∀ (D : Derivation ℤ (ChartRing k m d) (ChartRing k m d)) (q : Fin m → ChartRing k m d), (∀ i, D (bdParam k m d i) = q i * bdParam k m d i) → ∀ h : Heat Y.H Y.q.left P.D.toPre.P.L dd ⇑D, IsBasic Y h → HasDefect Y h (fun _ _ _ => 0) → (∀ a b, h.Θ a b ∈ maximalIdeal (ChartRing k m d)) → ∀ ρ : ChartRing k m d →+* DualNumber k, (∀ r, ρ r = TrivSqZeroExt.inl (MvPowerSeries.constantCoeff r) + TrivSqZeroExt.inr (MvPowerSeries.constantCoeff (D r))) → ∃ c : ℚ, c ≠ 0 ∧ IsConstAlong P.D.toPre (bdParam k m d) gam ρ (fun i => (c : k) * MvPowerSeries.constantCoeff (q i)) := by
  first | exact @GlobalTheory.KSFlatPer.isConstAlong_of_heat_flat | exact GlobalTheory.KSFlatPer.isConstAlong_of_heat_flat | (intros; apply GlobalTheory.KSFlatPer.isConstAlong_of_heat_flat <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DualNumberGraphFiltrationPushforwardMem
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.UPel.Sm GlobalTheory.Cris GlobalTheory.DeRham

noncomputable section

namespace GlobalTheory.HTRealise

theorem push_constMor_pull {k : Type} [Field k] (A₀ : Over (Sp k)) [GrpObj A₀] (g : A₀ ⟶ A₀)
    [IsMonHom g] (c : primDR A₀) :
    primPull (epsDP k) (GlobalTheory.DeRham.epsRed k) g ((constMor A₀).pull c) =
      (constMor A₀).pull (primPull (dp0 k) (𝟙 _) g c) := by
  have K := (constMor A₀).isMor.comp (homMor (epsDP k) (GlobalTheory.DeRham.epsRed k) g).isMor
  apply Subtype.ext
  exact (IsMor.pullback1_comp (constMor A₀).isMor
    (homMor (epsDP k) (GlobalTheory.DeRham.epsRed k) g).isMor K (fun _ ↦ rfl) rfl c.1).trans
    (IsMor.pullback1_comp (homMor (dp0 k) (𝟙 _) g).isMor (constMor A₀).isMor K
      (fun _ ↦ rfl) (by simp) c.1).symm

theorem push_mem_graphFil : ∀ (k : Type) [Field k] (A₀ : Over (Sp k)) [GrpObj A₀] (g : A₀ ⟶ A₀) [IsMonHom g] (f : HdR A₀ →ₗ[k] HdR A₀), (∀ x ∈ Fil A₀, f (push (dp0 k) (𝟙 _) g x) - push (dp0 k) (𝟙 _) g (f x) ∈ Fil A₀) → ∀ d ∈ GlobalTheory.HTRealise.graphFil A₀ f, push (epsDP k) (GlobalTheory.DeRham.epsRed k) g d ∈ GlobalTheory.HTRealise.graphFil A₀ f := by
  intro k _ A₀ _ g _ f hf d hd
  obtain ⟨x, hx, y, hy, e⟩ := hd
  refine ⟨push (dp0 k) (𝟙 _) g x, push_mem_Fil g hx,
    push (dp0 k) (𝟙 _) g (f x) - f (push (dp0 k) (𝟙 _) g x) + push (dp0 k) (𝟙 _) g y,
    add_mem (by rw [← neg_sub]; exact neg_mem (hf x hx)) (push_mem_Fil g hy), fun c ↦ ?_⟩
  rw [push_apply, push_constMor_pull, e]
  simp only [push_apply, LinearMap.add_apply, LinearMap.sub_apply]
  congr 2
  ring

end GlobalTheory.HTRealise
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EpiPowOfIsAbelianScheme
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT
open GlobalTheory.ZM GlobalTheory.SiegelTor

namespace GlobalTheory.UPel.HT.MulEpi

attribute [local instance] Over.cartesianMonoidalCategory

theorem epi_pow_of_isAbelianScheme (S : Scheme.{0}) (A : Over S) [GrpObj A] (hA : IsAbelianScheme A)
    (k : ℕ) (hk : 0 < k) : Epi ((𝟙 A) ^ k) := by
  obtain ⟨h1, h2, h3⟩ := GlobalTheory.UPel.HT.SiegUniqBase.flat_surjective_qc_pow S A hA k hk
  haveI : Epi ((𝟙 A) ^ k).left := Flat.epi_of_flat_of_surjective _
  exact (Over.forget S).epi_of_epi_map this

end GlobalTheory.UPel.HT.MulEpi
end

