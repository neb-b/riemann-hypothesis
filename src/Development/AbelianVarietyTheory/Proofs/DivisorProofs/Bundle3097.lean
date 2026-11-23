module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3090
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1945
public import Development.AbelianVarietyTheory.Definitions.Divisors.NotCompactOfMEqOne
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0044
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1317
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3092
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0008
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0691
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3084
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0022
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0010
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.AbelianHodgeDeRham
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0007
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0006
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0078
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0809
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsAdditiveLiftIff
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3079
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0026
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2069
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0009
public import Development.AbelianVarietyTheory.Definitions.Divisors.TorsionTowersOfDivisibleGroup
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.Bundle0001
public import Development.AbelianVarietyTheory.Statements.EllipticCurveLevels.BaseChangeMapRingAct
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3087
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle0029
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.IsUnitNatCastSections
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0322
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0358
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0037
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0004
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0015
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0014
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GroupLiftTangentCompatibility
public import Development.AbelianVarietyTheory.Definitions.Divisors.GalRigidOfSurjective
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0064
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0061
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsProperToroidalModelStructureMap
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.QuasiFiniteTautologicalChartOfSeparation
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RingKrullDimStalkLeTautologicalChartRing
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2372
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2014
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0006

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HarrisTaylorPairingSkewHodgeLagrangianStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.UPel.Sm GlobalTheory.Cris GlobalTheory.DeRham
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.harrisTaylor_pairing_skew_hodge_lagrangian : ∀ (p : ℕ) [Fact p.Prime] (D : GlobalTheory.UPel.HT.Datum p) (R : Type) [CommRing R] (b : GlobalTheory.UPel.HT.Base D R) (N : ℕ), 3 ≤ N → N.Coprime p → ∀ (k : Type) [Field k] [IsAlgClosed k] (t : Sp k ⟶ Sp R) (o₀ : GlobalTheory.UPel.HT.Obj b N t) (β : R →+* k), t = spMap β → ∀ φ : LinearMap.BilinForm k (HdR o₀.A), GlobalTheory.AbDual.IsCorrForm (dp0 k) (𝟙 _) o₀.A o₀.A o₀.P φ → FiniteDimensional k (HdR o₀.A) ∧ 2 * Module.finrank k (Fil o₀.A) = Module.finrank k (HdR o₀.A) ∧ (∀ x y, φ x y = -φ y x) ∧ ∀ x ∈ Fil o₀.A, ∀ y ∈ Fil o₀.A, φ x y = 0 := by
  first | (exact @GlobalTheory.UPel.HT.FormFacts.formFacts) | (exact GlobalTheory.UPel.HT.FormFacts.formFacts) | (intros; apply GlobalTheory.UPel.HT.FormFacts.formFacts  <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HarrisTaylorPolarisationBundlesCorrespondDeforma
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.UPel.Sm GlobalTheory.Cris GlobalTheory.DeRham
open GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.Published

attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.UPel.HT.PolIsoLift

theorem pol_iso : ∀ (p : ℕ) [Fact p.Prime] (D : GlobalTheory.UPel.HT.Datum p) (R : Type) [CommRing R] (b : GlobalTheory.UPel.HT.Base D R) (N : ℕ) (k : Type) [Field k] (t : Sp k ⟶ Sp R) (o₀ : GlobalTheory.UPel.HT.Obj b N t) (s₁ s₂ : Sp (DualNumber k) ⟶ Sp R) (o₁ : GlobalTheory.UPel.HT.Obj b N s₁) (o₂ : GlobalTheory.UPel.HT.Obj b N s₂) (m₁ : GlobalTheory.UPel.HT.ObjMap o₀ o₁ (spMap (TrivSqZeroExt.fstHom k k k).toRingHom)) (m₂ : GlobalTheory.UPel.HT.ObjMap o₀ o₂ (spMap (TrivSqZeroExt.fstHom k k k).toRingHom)) (e : o₁.A ≅ o₂.A), IsMonHom e.hom → m₁.φ ≫ e.hom.left = m₂.φ → ∀ φ₂ : (G2 o₁.A).left ⟶ (G2 o₂.A).left, IsSquare e.hom.left φ₂ → LBIso o₁.P (o₂.P.pull φ₂) := by
  intro p _ D R _ b N k _ t o₀ s₁ s₂ o₁ o₂ m₁ m₂ e he hφ φ₂ hsq
  haveI := he
  have hκ : IsNilDP (GlobalTheory.DeRham.epsDP k) := isDPNilpotent_squareZero _
  have hπ : Function.Surjective (TrivSqZeroExt.fstHom k k k).toRingHom := fun x ↦ ⟨TrivSqZeroExt.inl x, rfl⟩
  obtain ⟨g, hg⟩ := GlobalTheory.AbelianDim.exists_relDim (DualNumber k) o₁.A o₁.ab
  have hred : m₁.φ₂ ≫ φ₂ = m₂.φ₂ := by
    apply GlobalTheory.AbDual.left_ext (P := o₂.A) (Q := o₂.A)
    · rw [Category.assoc, hsq.1, ← Category.assoc, m₁.sq.1, Category.assoc, hφ, m₂.sq.1]
    · rw [Category.assoc, hsq.2, ← Category.assoc, m₁.sq.2, Category.assoc, hφ, m₂.sq.2]
  have hP' : (o₂.P.pull φ₂).IsLB := pull_isLB o₂.isLB φ₂
  have axis : ∀ (u v : o₁.A ⟶ o₁.A) (u' v' : o₂.A ⟶ o₂.A),
      (lift u v).left ≫ φ₂ = e.hom.left ≫ (lift u' v').left → Triv (ev o₂.P u' v') →
        Triv (ev (o₂.P.pull φ₂) u v) := by
    intro u v u' v' hc h
    rw [triv_ev_iff hP', evc, cls_pull o₂.isLB φ₂ hP', ← GlobalTheory.CechPic.pull_comp, hc, GlobalTheory.CechPic.pull_comp]
    rw [triv_ev_iff o₂.isLB, evc] at h
    rw [h, map_zero]
  have t₁ : Triv (ev (o₂.P.pull φ₂) (1 : o₁.A ⟶ o₁.A) (𝟙 o₁.A)) := by
    refine axis _ _ (1 : o₂.A ⟶ o₂.A) (𝟙 o₂.A) ?_ o₂.rig₁
    apply GlobalTheory.AbDual.left_ext (P := o₂.A) (Q := o₂.A)
    · rw [Category.assoc, hsq.1, lift_left_fst_assoc, Category.assoc, lift_left_fst, ← Over.comp_left,
        ← Over.comp_left, MonObj.one_comp, MonObj.comp_one]
    · rw [Category.assoc, hsq.2, lift_left_snd_assoc, Category.assoc, lift_left_snd]
      simp
  have t₂ : Triv (ev (o₂.P.pull φ₂) (𝟙 o₁.A) (1 : o₁.A ⟶ o₁.A)) := by
    refine axis _ _ (𝟙 o₂.A) (1 : o₂.A ⟶ o₂.A) ?_ o₂.rig₂
    apply GlobalTheory.AbDual.left_ext (P := o₂.A) (Q := o₂.A)
    · rw [Category.assoc, hsq.1, lift_left_fst_assoc, Category.assoc, lift_left_fst]
      simp
    · rw [Category.assoc, hsq.2, lift_left_snd_assoc, Category.assoc, lift_left_snd, ← Over.comp_left,
        ← Over.comp_left, MonObj.one_comp, MonObj.comp_one]
  have e' : LBIso ((o₂.P.pull φ₂).pull m₁.φ₂) o₀.P := by
    refine (cls_eq_iff (pull_isLB hP' _) o₀.isLB).1 ?_
    rw [cls_pull hP', cls_pull o₂.isLB φ₂ hP', ← GlobalTheory.CechPic.pull_comp, hred,
      ← cls_pull o₂.isLB m₂.φ₂ (pull_isLB o₂.isLB _)]
    exact (cls_eq_iff _ _).2 (LBIso.symm m₂.pol)
  have hL : (o₁.P.pull (lift (𝟙 o₁.A) (𝟙 o₁.A)).left).IsLB := pull_isLB o₁.isLB _
  exact GlobalTheory.BirigidLift.lift_unique (κ := epsDP k)
    (grothendieckDeformation_of_lifting _root_.GlobalTheory.abelianDeRham _root_.GlobalTheory.abelianScheme_hom_lifting_nilpotent_dividedPowers) _root_.GlobalTheory.dualAbelianScheme hκ hπ rfl
    o₁.ab hg o₁.ab hg m₁.cart m₁.cart m₁.sq.1 m₁.sq.2 hL o₁.ample hL o₁.ample o₀.isLB o₁.isLB o₁.rig₁ o₁.rig₂
    (LBIso.symm m₁.pol) hP' t₁ t₂ e'

end GlobalTheory.UPel.HT.PolIsoLift
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HarrisTaylorPullbackBundleDualHomStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Hecke GlobalTheory.UPel.HT.ES

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.harrisTaylor_pullback_bundle_dual_hom : ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (R : Type) [CommRing R] (b : Base D R) (N : ℕ) (Y : Scheme.{0}) (s : Y ⟶ Sp R) (o : Obj b N s) (B : Over Y) [GrpObj B] [IsCommMonObj B] (ψ' : B ⟶ o.A), IsAbelianScheme B → IsMonHom ψ' → ∃ (C : Over Y) (_ : GrpObj C) (Q : LB (B ⊗ C).left) (h : B ⟶ C), IsAbelianScheme C ∧ GlobalTheory.AbDual.IsDual B C Q ∧ GlobalTheory.AbDual.IsAdditive (GlobalTheory.AbDual.swap Q) ∧ IsMonHom h ∧ LBIso (o.P.pull (ψ' ⊗ₘ ψ').left) (Q.pull (lift (fst B B) (snd B B ≫ h)).left) ∧ ∀ (T : Over Y) (x : T ⟶ B), PullPolTriv o ψ' x ↔ x ≫ h = 1 := by
  first | (exact @GlobalTheory.UPel.HT.ES.pullPol_dual_hom) | (exact GlobalTheory.UPel.HT.ES.pullPol_dual_hom) | (intros; apply GlobalTheory.UPel.HT.ES.pullPol_dual_hom  <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HomFactorsThroughMulN
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Sp spMap IsGrpPullback)
open ReciprocityTheory.ChartRestriction.G.Semi (IsAbelianScheme LB mulN)
open GlobalTheory.PDiv (SpAlg)
open GlobalTheory.DeRham (spOver)
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.MulNDiv

theorem hom_ext_of_spAlg {R : Type} [CommRing R] {T B : Over (Sp R)} (a b : T ⟶ B)
    (h : ∀ (S : Type) [CommRing S] [Algebra R S] (g : SpAlg R S ⟶ T), g ≫ a = g ≫ b) : a = b := by
  ext1
  apply T.left.affineOpenCover.openCover.hom_ext
  intro j
  let C : CommRingCat := T.left.affineOpenCover.X j
  let φ : CommRingCat.of R ⟶ C := Spec.preimage (T.left.affineOpenCover.f j ≫ T.hom)
  letI : Algebra R C := φ.hom.toAlgebra
  let g : SpAlg R C ⟶ T := Over.homMk (T.left.affineOpenCover.f j) (by
    show _ = Spec.map (CommRingCat.ofHom (algebraMap R C))
    rw [← Spec.map_preimage (T.left.affineOpenCover.f j ≫ T.hom)]
    rfl)
  have := congrArg CommaMorphism.left (h C g)
  simp only [g, Over.comp_left, Over.homMk_left] at this
  exact this

theorem exists_factor_mulN : ∀ (R : Type) [CommRing R] (A B : Over (Sp R)) [GrpObj A] [GrpObj B], IsAbelianScheme A → IsAbelianScheme B → ∀ (n : ℕ), 0 < n → ∀ (F : A ⟶ B), IsMonHom F → (∀ (S : Type) [CommRing S] [Algebra R S] (z : SpAlg R S ⟶ A), z ^ n = 1 → z ≫ F = 1) → ∃ f : A ⟶ B, IsMonHom f ∧ F = mulN A n ≫ f := by
  intro R _ A B _ _ hA _ n hn F hF hker
  haveI := hA.comm
  obtain ⟨hfin, hflat, hsurj⟩ := _root_.GlobalTheory.MulFlatSurj.finite_flat_surjective_mulN R A hA n hn
  haveI : IsMonHom (mulN A n) := GlobalTheory.MulEtaleDvr.isMonHom_mulN A n
  have hqc : QuasiCompact (mulN A n).left := inferInstance
  have h : ∀ (T : Over (Sp R)) (x : T ⟶ A), x ≫ mulN A n = 1 → x ≫ F = 1 := by
    intro T x hx
    apply hom_ext_of_spAlg
    intro S _ _ g
    have hxn : x ^ n = 1 := by
      rw [← hx, GlobalTheory.MulEtaleDvr.mulN_eq_pow, MonObj.comp_pow, Category.comp_id]
    have hz : (g ≫ x) ^ n = 1 := by
      rw [← MonObj.comp_pow, hxn, MonObj.comp_one]
    rw [← Category.assoc, hker S (g ≫ x) hz, MonObj.comp_one]
  obtain ⟨⟨ψ, hψ, hc⟩, -⟩ := exists_monHom_factor_of_flat_surjective _ A A B (mulN A n) F inferInstance hF
    hflat hsurj hqc h
  exact ⟨ψ, hψ, hc.symm⟩

end GlobalTheory.MulNDiv
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsArtinianRingTsze
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.UPel.Sm GlobalTheory.Cris GlobalTheory.DeRham

noncomputable section

namespace GlobalTheory.HTGlue

variable {k : Type} [Field k] {d : ℕ}

theorem finite_tsze (k : Type) [Field k] (d : ℕ) : Module.Finite k (TrivSqZeroExt k (Fin d → k)) :=
  Module.Finite.of_surjective
    ((Algebra.linearMap k (TrivSqZeroExt k (Fin d → k))).coprod (TrivSqZeroExt.inrHom k (Fin d → k)))
    (fun x => ⟨(x.fst, x.snd), by ext <;> simp [TrivSqZeroExt.algebraMap_eq_inl]⟩)

theorem isArtinianRing_tsze (k : Type) [Field k] (d : ℕ) : IsArtinianRing (TrivSqZeroExt k (Fin d → k)) :=
  haveI := finite_tsze k d; IsArtinianRing.of_finite k _

theorem exists_coords (V : Type) [AddCommGroup V] [Module k V] [Module kᵐᵒᵖ V] [IsCentralScalar k V]
    (A₀ : Over (Sp k)) [GrpObj A₀] (hA : IsAbelianScheme A₀) (l : primDR A₀ →ₗ[k] TrivSqZeroExt k V) :
    ∃ e : Crys (divided₂ (GlobalTheory.FODef.sqZero k V)) (spMap (TrivSqZeroExt.fstHom k k V).toRingHom) A₀,
      ∀ c, e ((GlobalTheory.FODef.constMorV k V A₀).pull c) = l c := by
  have hm := GlobalTheory.SqZeroCrys.isBC_trivSqZeroExt k V A₀ hA (GlobalTheory.FODef.sqZero k V) (GlobalTheory.FODef.constMorV k V A₀)
  let eqv := LinearEquiv.ofBijective _ hm
  refine ⟨(LinearMap.liftBaseChange (TrivSqZeroExt k V) l) ∘ₗ eqv.symm.toLinearMap, fun c => ?_⟩
  have : (GlobalTheory.FODef.constMorV k V A₀).pull c = eqv (1 ⊗ₜ c) :=
    (one_smul (TrivSqZeroExt k V) ((GlobalTheory.FODef.constMorV k V A₀).pull c)).symm
  rw [this, LinearMap.comp_apply, LinearEquiv.coe_coe, eqv.symm_apply_apply,
    LinearMap.liftBaseChange_tmul, one_smul]

def glueFil (A₀ : Over (Sp k)) [GrpObj A₀] (f : Fin d → (HdR A₀ →ₗ[k] HdR A₀)) :
    Submodule (TrivSqZeroExt k (Fin d → k))
      (Crys (divided₂ (GlobalTheory.FODef.sqZero k (Fin d → k))) (spMap (TrivSqZeroExt.fstHom k k (Fin d → k)).toRingHom) A₀) where
  carrier := {e | ∃ x ∈ Fil A₀, ∃ z : Fin d → HdR A₀, (∀ j, z j ∈ Fil A₀) ∧
      ∀ c : primDR A₀, e ((GlobalTheory.FODef.constMorV k (Fin d → k) A₀).pull c) =
        TrivSqZeroExt.inl (x c) + TrivSqZeroExt.inr (fun j => (f j x + z j) c)}
  add_mem' := by
    rintro e e' ⟨x, hx, z, hz, he⟩ ⟨x', hx', z', hz', he'⟩
    refine ⟨x + x', add_mem hx hx', z + z', fun j => add_mem (hz j) (hz' j), fun c => ?_⟩
    rw [LinearMap.add_apply, he c, he' c]
    ext
    · simp
    · simp only [TrivSqZeroExt.snd_add, TrivSqZeroExt.snd_inl, TrivSqZeroExt.snd_inr, Pi.add_apply, map_add (f := _),
        LinearMap.add_apply, zero_add, Pi.zero_apply, add_zero]
      ring
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
        map_smul, map_add, LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul, add_zero, zero_add,
        MulOpposite.smul_eq_mul_unop, MulOpposite.unop_op, Pi.zero_apply]
      ring

theorem exists_mem_glueFil (A₀ : Over (Sp k)) [GrpObj A₀] (hA : IsAbelianScheme A₀)
    (f : Fin d → (HdR A₀ →ₗ[k] HdR A₀)) {x : HdR A₀} (hx : x ∈ Fil A₀) :
    ∃ e ∈ glueFil A₀ f, ∀ c, e ((GlobalTheory.FODef.constMorV k (Fin d → k) A₀).pull c) =
      TrivSqZeroExt.inl (x c) + TrivSqZeroExt.inr ((LinearMap.pi fun j => f j x) c) := by
  obtain ⟨e, he⟩ := exists_coords (Fin d → k) A₀ hA
    ((Algebra.linearMap k (TrivSqZeroExt k (Fin d → k))) ∘ₗ x + (TrivSqZeroExt.inrHom k (Fin d → k)) ∘ₗ
      LinearMap.pi fun j => f j x)
  refine ⟨e, ⟨x, hx, 0, fun _ => zero_mem _, fun c => ?_⟩, fun c => ?_⟩
  · rw [he c]; ext <;> simp [TrivSqZeroExt.algebraMap_eq_inl]
  · rw [he c]; simp [TrivSqZeroExt.algebraMap_eq_inl]

end GlobalTheory.HTGlue
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LaurentKummerCupProductMapBijectiveFiniteStrictHStatement
section
open CategoryTheory Limits AlgebraicGeometry Opposite Simplicial GlobalTheory.EtC GlobalTheory.EtC.GmStep
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.laurentKummerCupProductMap_bijective_finite_strictHenselian : ∀ (q : ℕ) [NeZero q] (A : Type) [CommRing A], SH A → IsUnit (q : A) → ∀ (T : Type) [CommRing T] [Algebra A T],
  Module.Finite A T → ∀ i : ℤ, Function.Bijective (gmPhi q T i) := by
  first | (exact @GlobalTheory.EtC.GmStep.gmPhi_bijective_finite) | (exact GlobalTheory.EtC.GmStep.gmPhi_bijective_finite) | (intros; apply GlobalTheory.EtC.GmStep.gmPhi_bijective_finite  <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LcCutTwoClosedPointsOneCentreStatement
section
open CategoryTheory AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.QCoh GlobalTheory.Discrepancy GlobalTheory.PairStep
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lc_cut_two_closed_points_one_centre : GlobalTheory.Published.Principalisation → GlobalTheory.Published.NadelVanishingPair → GlobalTheory.Published.NefNumerics → ∀ (X : Scheme.{0}) [IsIntegral X] [IsLocallyNoetherian X] [GlobalTheory.IsNormalScheme X] (p : X ⟶ Sp ℂ) (n : ℕ), IsProjOver p → topologicalKrullDim X = n → letI := algebraΓOfHom p; ∀ (Δ : X → ℚ) (m : ℕ) (G : CartierDiv X) (N : LB X) (D : X → ℚ) (d h : ℚ) (x x' z : X) (j : ℕ), IsEffQDiv Δ → (∀ y, KltAt p n Δ y) → 0 < m → IsLogCanonicalMultiple p n Δ m G → IsAmpleLB N → QNum p N d D → 0 ≤ d → IsClosed ({x} : Set X) → IsClosed ({x'} : Set X) → LcAt p n (Δ + D) x → LcAt p n (Δ + D) x' → z ⤳ x → z ⤳ x' → (z = genericPoint X ∨ IsNkltCentre p n (Δ + D) z) → topologicalKrullDim (closure ({z} : Set X)) = (j + 1 : ℕ) → 0 < h → 2 * ((j + 1 : ℕ) : ℚ) ^ (j + 1) < h ^ (j + 1) * (interNumRed ℂ (Closeds.closure ({z} : Set X)) fun _ : Fin (j + 1) => N : ℤ) → ∃ (D' : X → ℚ) (d' : ℚ), 0 ≤ d' ∧ d' ≤ d + h ∧ QNum p N d' D' ∧ ((LcCut p n (Δ + D') x j ∧ ¬ KltAt p n (Δ + D') x') ∨ (LcCut p n (Δ + D') x' j ∧ ¬ KltAt p n (Δ + D') x)) := by
  first | exact @GlobalTheory.PairStep.logCanonicalCut_two_points | exact GlobalTheory.PairStep.logCanonicalCut_two_points | (intros; apply GlobalTheory.PairStep.logCanonicalCut_two_points <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LiftedHodgeFiltrationEqOfSameLifts
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.UPel.Sm GlobalTheory.Cris GlobalTheory.DeRham

set_option autoImplicit false

noncomputable section

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.LiftFilEq

open GlobalTheory.Published GlobalTheory.Published.GrothendieckMessing


set_option maxHeartbeats 1000000 in
theorem liftFil_le (k : Type) [Field k] (A₀ : Over (Sp k)) [GrpObj A₀] (A₁ A₂ : Over (Sp (DualNumber k)))
    [GrpObj A₁] [GrpObj A₂] (i₁ : A₀.left ⟶ A₁.left) (i₂ : A₀.left ⟶ A₂.left)
    (h₁ : IsGrpPullback A₀ A₁ (spMap (TrivSqZeroExt.fstHom k k k).toRingHom) i₁)
    (h₂ : IsGrpPullback A₀ A₂ (spMap (TrivSqZeroExt.fstHom k k k).toRingHom) i₂)
    (hA₁ : IsAbelianScheme A₁) (g : HdR A₀ → HdR A₀)
    (H₁ : ∀ x ∈ Fil A₀, IsFilLift h₁ x (g x)) (H₂ : ∀ x ∈ Fil A₀, IsFilLift h₂ x (g x)) :
    liftFil (epsDP k) h₁ ≤ liftFil (epsDP k) h₂ := by
  have P : AbelianDeRham := _root_.GlobalTheory.abelianDeRham
  obtain ⟨g₁, hg₁⟩ := GlobalTheory.AbelianDim.exists_relDim (DualNumber k) A₁ hA₁
  have hA₀ : IsAbelianScheme A₀ := by
    have := hA₁.comm
    have hc : IsCommMonObj A₀ := by
      rw [isCommMonObj_iff_isMulCommutative]
      intro T
      refine ⟨⟨fun x y => Over.OverMorphism.ext (h₁.1.hom_ext ?_ (by rw [Over.w, Over.w]))⟩⟩
      rw [← h₁.2 T x y (pushPt h₁.1.w x) (pushPt h₁.1.w y) rfl rfl,
        ← h₁.2 T y x (pushPt h₁.1.w y) (pushPt h₁.1.w x) rfl rfl, _root_.mul_comm]
    exact { comm := hc
            smooth := MorphismProperty.of_isPullback (P := @Smooth) h₁.1 hA₁.smooth
            proper := MorphismProperty.of_isPullback (P := @IsProper) h₁.1 hA₁.proper
            geomConnected := MorphismProperty.of_isPullback (P := @GeometricallyConnected) h₁.1 hA₁.geomConnected }
  have gA₀ := (smoothOfRelativeDimension_isStableUnderBaseChange g₁).of_isPullback h₁.1 hg₁
  obtain ⟨C, _, φ, j, hφ, hic, e1⟩ := exists_const A₀
  have hBC := constMor_isBC P hA₀ gA₀ hφ hic e1
  have HC : Canonical (epsDP k) (TrivSqZeroExt.fstHom k k k).toRingHom :=
    canonical_of_abelianDeRham P (isDPNilpotent_squareZero _) (fun r ↦ ⟨TrivSqZeroExt.inl r, rfl⟩) rfl
  have step : ∀ x ∈ liftFil (epsDP k) h₁, ∃ y ∈ liftFil (epsDP k) h₁ ⊓ liftFil (epsDP k) h₂,
      ∃ z : Crys (epsDP k) (GlobalTheory.DeRham.epsRed k) A₀, x = y + (DualNumber.eps : DualNumber k) • z := by
    intro x hx
    have ha := crysLo_mem_Fil P hA₁ hg₁ h₁ hx
    obtain ⟨d₁, hd₁, e₁⟩ := H₁ _ ha
    obtain ⟨d₂, hd₂, e₂⟩ := H₂ _ ha
    have e : d₁ = d₂ := crys_ext P hA₀ gA₀ fun c ↦ (e₁ c).trans (e₂ c).symm
    obtain ⟨z, hz⟩ := hBC.exists (crysHi x - g (crysLo x))
    have hd₁₂ : d₁ ∈ liftFil (epsDP k) h₂ := by rw [e]; exact hd₂
    refine ⟨d₁, ⟨hd₁, hd₁₂⟩, z, crys_ext P hA₀ gA₀ fun c ↦ ?_⟩
    rw [LinearMap.add_apply, LinearMap.smul_apply, e₁, hz c, crys_constMor x c]
    ext <;> simp [TrivSqZeroExt.algebraMap_eq_inl]
  have hEq : liftFil (epsDP k) h₁ = liftFil (epsDP k) h₁ ⊓ liftFil (epsDP k) h₂ := by
    refine eq_of_le_of_le_add_eps ?_ inf_le_left step
    obtain ⟨N, hN⟩ := (HC g₁ A₀ A₁ i₁ h₁ hA₁ hg₁).2.1
    have c := HC.crysToDR_bijective h₁ hA₁ hg₁
    exact ⟨_, (Submodule.orderIsoMapComap (LinearEquiv.ofBijective _ c)).symm.isCompl hN⟩
  exact fun x hx ↦ (hEq.le hx).2

theorem liftFil_eq : ∀ (k : Type) [Field k] (A₀ : Over (Sp k)) [GrpObj A₀] (A₁ A₂ : Over (Sp (DualNumber k))) [GrpObj A₁] [GrpObj A₂] (i₁ : A₀.left ⟶ A₁.left) (i₂ : A₀.left ⟶ A₂.left) (h₁ : IsGrpPullback A₀ A₁ (spMap (TrivSqZeroExt.fstHom k k k).toRingHom) i₁) (h₂ : IsGrpPullback A₀ A₂ (spMap (TrivSqZeroExt.fstHom k k k).toRingHom) i₂), IsAbelianScheme A₁ → IsAbelianScheme A₂ → ∀ g : HdR A₀ → HdR A₀, (∀ x ∈ Fil A₀, IsFilLift h₁ x (g x)) → (∀ x ∈ Fil A₀, IsFilLift h₂ x (g x)) → liftFil (epsDP k) h₁ = liftFil (epsDP k) h₂ := by
  intro k _ A₀ _ A₁ A₂ _ _ i₁ i₂ h₁ h₂ hA₁ hA₂ g H₁ H₂
  exact le_antisymm (liftFil_le k A₀ A₁ A₂ i₁ i₂ h₁ h₂ hA₁ g H₁ H₂)
    (liftFil_le k A₀ A₂ A₁ i₂ i₁ h₂ h₁ hA₂ g H₂ H₁)

end GlobalTheory.LiftFilEq
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TautologicalChartCentreIsCompletedEtaleLocalMap
section
noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.SiegJoin GlobalTheory.Poinc GlobalTheory.TChart
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.TChartEt

theorem injective_of_flat_isLocalHom {A B : Type} [CommRing A] [CommRing B] [IsLocalRing A] [IsLocalRing B]
    (f : A →+* B) (hf : f.Flat) [hl : IsLocalHom f] : Function.Injective f := by
  algebraize [f]
  have : IsLocalHom (algebraMap A B) := hl
  have := Module.FaithfullyFlat.of_flat_of_isLocalHom (A := A) (B := B)
  exact FaithfulSMul.algebraMap_injective A B

theorem charZero_stalk_of_flat {o : Type} [CommRing o] [IsDomain o] [CharZero o] (X : Scheme.{0}) (s : X ⟶ Sp o)
    [Flat s] (x : X) : CharZero (X.presheaf.stalk x) := by
  have hf : (s.stalkMap x).hom.Flat := Flat.stalkMap s x
  have h0 : CharZero ((Sp o).presheaf.stalk (s x)) := by
    have : CharZero Γ(Sp o, ⊤) := (Scheme.ΓSpecIso (.of o)).hom.hom.charZero
    exact charZero_of_injective_ringHom (f := ((Sp o).presheaf.germ ⊤ (s x) trivial).hom)
      (germ_injective_of_isIntegral (Sp o) (U := ⊤) (s x) trivial)
  exact charZero_of_injective_ringHom (injective_of_flat_isLocalHom _ hf)

theorem essFiniteType_int_stalk (n : ℕ) (X : Scheme.{0}) (s : X ⟶ Sp (cycAway n)) [LocallyOfFiniteType s] (x : X) :
    Algebra.EssFiniteType ℤ (X.presheaf.stalk x) := by
  have h1 : (s.stalkMap x).hom.EssFiniteType := LocallyOfFiniteType.stalkMap s x
  let p : PrimeSpectrum (cycAway n) := s x
  have h2 : (algebraMap (cycAway n) ((Spec.structureSheaf (cycAway n)).presheaf.stalk p)).EssFiniteType :=
    RingHom.essFiniteType_algebraMap.2 (Algebra.EssFiniteType.of_isLocalization _ p.asIdeal.primeCompl)
  haveI := finiteType_cycAway n
  have h3 : (algebraMap ℤ (cycAway n)).EssFiniteType := RingHom.essFiniteType_algebraMap.2 inferInstance
  have h4 := (h3.comp h2).comp h1
  rw [← RingHom.essFiniteType_algebraMap]
  convert h4
  exact RingHom.ext_int _ _

theorem charZero_stalk_centre {g n : ℕ} (F : SFam g n (zetaAway n)) {S : Scheme.{0}} (j : F.X ⟶ S)
    {R : Type} [CommRing R] [IsDomain R] [IsLocalRing R] (y : Sp (FractionRing R) ⟶ F.X) (ξ : Sp R ⟶ S)
    (hy : y ≫ j = jK R ≫ ξ) : CharZero (S.presheaf.stalk (ξ (closedPoint R))) := by
  haveI := F.smooth
  haveI : Smooth F.s := SmoothOfRelativeDimension.smooth (g * (g + 1) / 2) F.s
  haveI : Flat F.s := inferInstance
  let w : Sp (FractionRing R) := closedPoint (FractionRing R)
  have hsp : ξ (jK R w) ⤳ ξ (closedPoint R) := (specializes_closedPoint _).map ξ.continuous
  have hjw : j (y w) = ξ (jK R w) := by
    rw [← Scheme.Hom.comp_apply, hy, Scheme.Hom.comp_apply]
  haveI : CharZero (F.X.presheaf.stalk (y w)) := charZero_stalk_of_flat F.X F.s (y w)
  haveI h₁ : CharZero (S.presheaf.stalk (j (y w))) := (j.stalkMap (y w)).hom.charZero
  rw [hjw] at h₁
  exact (S.presheaf.stalkSpecializes hsp).hom.charZero

end GlobalTheory.TChartEt

namespace GlobalTheory.TChartEt

theorem isEtaleCompletion_tautChart : GlobalTheory.Poinc.Sep.SepSt → ∀ g : ℕ, 1 ≤ g → ∀ φ : InvFun ℤ, IsPolFan id g φ → NoSelfInt id g φ → ∀ n : ℕ, 3 ≤ n → Odd n → ∀ (F : SFam g n (zetaAway n)) (Z : Scheme.{0}) (z : Z ⟶ Sp (cycAway n)) (i : F.X ⟶ Z) (OZ : LB Z) (d : ℕ) (S : Scheme.{0}) (π : S ⟶ Z) (j : F.X ⟶ S) [IsOpenImmersion j] (BD : GlobalTheory.EffCartierData S), MinAt5 F z i OZ → BlowAt F z i φ d π j BD → ∀ (C : Taut (zetaAway n) g n φ) (G₁ : Over (Sp C.R)) [GrpObj G₁] [IsCommMonObj G₁] (y : Sp (FractionRing C.R) ⟶ F.X) (α₁ : pullback G₁.hom (jK C.R) ⟶ F.univ.A.left) (ξ : Sp C.R ⟶ S), C.IsFam F G₁ y α₁ → y ≫ j = jK C.R ≫ ξ → IsEtaleCompletion (Scheme.stalkClosedPointTo ξ).hom ∧ ((residue C.R).comp (Scheme.stalkClosedPointTo ξ).hom).FormallyUnramified := by
  intro hSep g hg φ hφ hns n hn ho F Z z i OZ d S π j _ BD hM hB C G₁ _ _ y α₁ ξ hF hy
  obtain ⟨J, h₁, h₂, h₃, hNB, hP, h₄⟩ := hB
  haveI : GlobalTheory.IsNormalScheme S := hNB.1
  haveI : CharZero (S.presheaf.stalk (ξ (closedPoint C.R))) := charZero_stalk_centre F j y ξ hy
  haveI : LocallyOfFiniteType (π ≫ z) := by
    obtain ⟨N, ιP, hιP, e⟩ := hP
    rw [← e]
    haveI := ReciprocityTheory.ChartRestriction.G.Geo.Tor.isProper_str (cycAway n) N
    infer_instance
  haveI : Algebra.EssFiniteType ℤ (S.presheaf.stalk (ξ (closedPoint C.R))) :=
    essFiniteType_int_stalk n S (π ≫ z) _
  haveI : IsNoetherianRing C.R := C.compl.1
  obtain ⟨hqf, hfin⟩ := _root_.GlobalTheory.QFChart.quasiFinite_tautChart hSep g hg φ hφ hns n hn ho F Z z i OZ d S π j BD hM
    ⟨J, h₁, h₂, h₃, hNB, hP, h₄⟩ C G₁ y α₁ ξ hF hy
  have hdim := _root_.GlobalTheory.TChart.ChartDim.ringKrullDim_stalk_le_chart g hg φ hφ hns n hn ho F Z z i OZ d S π j BD hM
    ⟨J, h₁, h₂, h₃, hNB, hP, h₄⟩ C G₁ y α₁ ξ hF hy hfin
  have hgal := _root_.GlobalTheory.TChart.galRigid_stalk_of_isFam hn F S j C G₁ y α₁ ξ hF hy
  exact _root_.GlobalTheory.QFEtale.isEtaleCompletion_of_galRigid _ _ (Scheme.stalkClosedPointTo ξ).hom C.compl.2.1 hqf hfin hdim hgal

end GlobalTheory.TChartEt
end
end

