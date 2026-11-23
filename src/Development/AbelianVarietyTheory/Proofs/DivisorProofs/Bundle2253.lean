module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0064
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2141
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.AbelianHodgeDeRham
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0022
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0006
public import Development.AbelianVarietyTheory.Definitions.Divisors.ThetaSetupStructureMapComp
public import Development.AbelianVarietyTheory.Definitions.Divisors.NonUnitAt
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0063
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0065
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0007
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0006
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.BCTools
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.DegProd
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1917
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0074
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.IsAbelianSchemeAndExtendOfGenericHoms
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0012
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0001
public import Development.AbelianVarietyTheory.Definitions.Divisors.JetAnalytic
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2169
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0747
public import Development.AbelianVarietyTheory.Definitions.Divisors.AxesVanishingStructureSheafDegOne
public import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.IsScalarTowerOfAlgebraMapEq
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsKSValueOneOfRetraction
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0006
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0657
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0634
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2195
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
public import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissibleBaseOfCompleteDvr

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsDualNumberGeneratorOfTorsorCoboundary
section
set_option autoImplicit false
noncomputable section

open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Sp spMap epsR IsTangent IsGrpPullback)
open ReciprocityTheory.ChartRestriction.G.Semi (IsAbelianScheme LB)
open GlobalTheory GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.PDiv GlobalTheory.PtExt
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.PtExt.EpsGenCob

theorem evU_mul' {Y : Scheme.{0}} {D : Type} [CommRing D] (y : Sp D ⟶ Y) (U : Y.Opens) (h : ⊤ ≤ y ⁻¹ᵁ U)
    (a b : Γ(Y, U)) : evU y U (a * b) = evU y U a * evU y U b := by
  simpa only [evU, dite_eq_left h] using map_mul (evalAt y U h) a b

theorem evU_isUnit' {Y : Scheme.{0}} {D : Type} [CommRing D] (y : Sp D ⟶ Y) (U : Y.Opens) (h : ⊤ ≤ y ⁻¹ᵁ U)
    (a : Γ(Y, U)ˣ) : IsUnit (evU y U a.val) := by
  simpa only [evU, dite_eq_left h] using a.isUnit.map (evalAt y U h)

theorem evU_cocycle {X : Scheme.{0}} (P : LB X) (hP : P.IsLB) {D : Type} [CommRing D] (y : Sp D ⟶ X)
    (a b c : P.ι) (ha : ⊤ ≤ y ⁻¹ᵁ P.U a) (hb : ⊤ ≤ y ⁻¹ᵁ P.U b) (hc : ⊤ ≤ y ⁻¹ᵁ P.U c) :
    evU y (P.U a ⊓ P.U c) (P.g a c).val =
      evU y (P.U a ⊓ P.U b) (P.g a b).val * evU y (P.U b ⊓ P.U c) (P.g b c).val := by
  have h3 : ⊤ ≤ y ⁻¹ᵁ (P.U a ⊓ P.U b ⊓ P.U c) := fun p hp ↦ ⟨⟨ha hp, hb hp⟩, hc hp⟩
  have e := congrArg (fun u ↦ evU y _ (Units.val u)) (hP.cocycle a b c)
  simp only [ReciprocityTheory.ChartRestriction.G.Semi.res, Units.val_mul, Units.coe_map, MonoidHom.coe_ofClass] at e
  rw [evU_mul' y _ h3, evalSectionAtPointOrZero_restriction, evalSectionAtPointOrZero_restriction, evalSectionAtPointOrZero_restriction] at e
  · exact e.symm
  all_goals exact h3

theorem snd_eq_fst_mul_dl {D : Type} [CommRing D] (u : DualNumber D) (hu : IsUnit u) : u.snd = u.fst * dl u := by
  have hfst : IsUnit u.fst := hu.map (TrivSqZeroExt.fstHom D D D)
  rw [dl, mul_left_comm, Ring.mul_inverse_cancel _ hfst, _root_.mul_one]

theorem dualNumber_inl_mul_one_add_inr_fst_snd {D : Type} [CommRing D] (a c : D) :
    (TrivSqZeroExt.inl a * (1 + TrivSqZeroExt.inr c) : DualNumber D).fst = a ∧
    (TrivSqZeroExt.inl a * (1 + TrivSqZeroExt.inr c) : DualNumber D).snd = a * c := by
  constructor <;> simp

end GlobalTheory.PtExt.EpsGenCob

namespace GlobalTheory.PtExt.EpsGenCob

variable {R : Type} [CommRing R] {A B : Over (Sp R)} [GrpObj A] [GrpObj B]

theorem red_ptV {v : epsR R ⟶ B} (hv : IsTangent v) {E : Type} [CommRing E] [Algebra R E] (x : Pt A E) :
    spOver (TrivSqZeroExt.fstHom R E E) ≫ ptV v x = x ≫ AbDual.inl A B := by
  have hv' : spOver (TrivSqZeroExt.fstHom R R R) ≫ v = toUnit _ ≫ η[B] := by
    refine Over.OverMorphism.ext ?_
    refine hv.trans ?_
    simp [spMap]
  apply CartesianMonoidalCategory.hom_ext
  · simp only [ptV, Category.assoc, lift_fst, Category.comp_id]
    rw [← Category.assoc, spOver_comp]
    have : (TrivSqZeroExt.fstHom R E E).comp (TrivSqZeroExt.inlAlgHom R E E) = AlgHom.id R E := by ext; simp
    rw [this]
    refine Over.OverMorphism.ext ?_
    simp [spOver, spMap]
  · simp only [ptV, Category.assoc, lift_snd]
    rw [← Category.assoc, spOver_comp]
    have : (TrivSqZeroExt.fstHom R E E).comp (EpsWeil.epsMap R E) =
        (Algebra.ofId R E).comp (TrivSqZeroExt.fstHom R R R) := by
      apply DualNumber.algHom_ext
      simp [EpsWeil.epsMap]
    rw [this, ← spOver_comp, Category.assoc, hv', Hom.one_def, ← Category.assoc, ← Category.assoc]
    congr 1
    exact toUnit_unique _ _

theorem ptV_mem (P : LB (A ⊗ B).left) {v : epsR R ⟶ B} (hv : IsTangent v) {E : Type} [CommRing E] [Algebra R E]
    (x : Pt A E) (i : P.ι) (h : ⊤ ≤ x.left ⁻¹ᵁ chartsA P i) : ⊤ ≤ (ptV v x).left ⁻¹ᵁ P.U i := by
  apply dualNumberPoint_preimage_top_of_reduction
  change ⊤ ≤ (spOver (TrivSqZeroExt.fstHom R E E) ≫ ptV v x).left ⁻¹ᵁ P.U i
  rw [red_ptV hv x]
  exact h

theorem ptV_nat (v : epsR R ⟶ B) {E E' : Type} [CommRing E] [Algebra R E] [CommRing E'] [Algebra R E']
    (ψ : E →ₐ[R] E') (x : Pt A E) : ptV v (spOver ψ ≫ x) = spOver (epsHom ψ) ≫ ptV v x := by
  apply CartesianMonoidalCategory.hom_ext
  · simp only [ptV, Category.assoc, lift_fst]
    rw [← Category.assoc, ← Category.assoc, spOver_comp, spOver_comp]
    congr 2
    ext a <;> simp [epsHom, DualNumber.lift_apply_inl]
  · simp only [ptV, Category.assoc, lift_snd]
    rw [← Category.assoc, spOver_comp]
    congr 2
    apply DualNumber.algHom_ext
    simp [epsHom, EpsWeil.epsMap]

theorem memV (P : LB (A ⊗ B).left) {v : epsR R ⟶ B} (hv : IsTangent v) {E : Type} [CommRing E] [Algebra R E]
    (x : Pt A E) (a b : P.ι) (ha : ⊤ ≤ x.left ⁻¹ᵁ chartsA P a) (hb : ⊤ ≤ x.left ⁻¹ᵁ chartsA P b) :
    ⊤ ≤ (ptV v x).left ⁻¹ᵁ (P.U a ⊓ P.U b) := fun p hp ↦
  ⟨ptV_mem P hv x a ha hp, ptV_mem P hv x b hb hp⟩

theorem fst_gV (P : LB (A ⊗ B).left) {v : epsR R ⟶ B} (hv : IsTangent v) {E : Type} [CommRing E] [Algebra R E]
    (x : Pt A E) (a b : P.ι) (ha : ⊤ ≤ x.left ⁻¹ᵁ chartsA P a) (hb : ⊤ ≤ x.left ⁻¹ᵁ chartsA P b) :
    (evU (ptV v x).left (P.U a ⊓ P.U b) (P.g a b).val).fst =
      evU (x ≫ AbDual.inl A B).left (P.U a ⊓ P.U b) (P.g a b).val := by
  have h := evalSectionAtPointOrZero_specMap_comp _ _ _ (TrivSqZeroExt.fstHom R E E : DualNumber E →+* E) (ptV v x).left _
    (P.g a b).val (memV P hv x a b ha hb)
  have e : spMap (TrivSqZeroExt.fstHom R E E : DualNumber E →+* E) ≫ (ptV v x).left =
      (x ≫ AbDual.inl A B).left := by
    rw [← red_ptV hv x, Over.comp_left]; rfl
  rw [e] at h
  rw [h]; rfl

end GlobalTheory.PtExt.EpsGenCob


open GlobalTheory.PtExt.EpsGenCob in
theorem GlobalTheory.PtExt.exists_isEpsGen_of_isCob : ∀ (R : Type) [CommRing R] (A B : Over (Sp R)) [GrpObj A] [GrpObj B]
    (P : LB (A ⊗ B).left), P.IsLB → ∀ v : epsR R ⟶ B, IsTangent v →
    ∀ (j : ∀ (D : Type) [CommRing D] [Algebra R D], Pt A D → P.ι), IsChoice P j →
    ∀ s, IsPtGen P (AbDual.inl A B) s → ∀ k : Fn0 A, IsCob (chartsA P) (tanCoc P j v) k → ∃ T, IsEpsGen P v T := by
  intro R _ A B _ _ P hP v hv j hj s hs k hk
  obtain ⟨hs1, hs2, hs3⟩ := hs
  refine ⟨fun E _ _ x i ↦ TrivSqZeroExt.inl (s E x i) * (1 + TrivSqZeroExt.inr
    (dl (evU (ptV v x).left (P.U i ⊓ P.U (j E x)) (P.g i (j E x)).val) + k E x)), ?_, ?_, ?_⟩
  · intro E _ _ x i h
    exact ((hs1 E x i h).map (TrivSqZeroExt.inlHom E E)).mul (EpsWeil.epsUnit _).isUnit
  · intro E _ _ E' _ _ ψ x i h
    have h' : ⊤ ≤ (spOver ψ ≫ x).left ⁻¹ᵁ chartsA P i := fun p _ ↦ h (Set.mem_univ _)
    have hjx : ⊤ ≤ x.left ⁻¹ᵁ chartsA P (j E x) := hj E x ⟨i, h⟩
    have hjx2 : ⊤ ≤ (spOver ψ ≫ x).left ⁻¹ᵁ chartsA P (j E x) := fun p _ ↦ hjx (Set.mem_univ _)
    have hjx' : ⊤ ≤ (spOver ψ ≫ x).left ⁻¹ᵁ chartsA P (j E' (spOver ψ ≫ x)) := hj E' _ ⟨i, h'⟩
    have hc := evU_cocycle P hP (ptV v (spOver ψ ≫ x)).left i (j E' (spOver ψ ≫ x)) (j E x)
      (ptV_mem P hv _ i h') (ptV_mem P hv _ _ hjx') (ptV_mem P hv _ _ hjx2)
    have u1 := evU_isUnit' _ _ (memV P hv _ i _ h' hjx') (P.g i (j E' (spOver ψ ≫ x)))
    have u2 := evU_isUnit' _ _ (memV P hv _ _ _ hjx' hjx2) (P.g (j E' (spOver ψ ≫ x)) (j E x))
    have hd := dualNumberSndMulInverseFst_mul_units E' _ _ u1 u2
    rw [← hc] at hd
    have uG := evU_isUnit' _ _ (memV P hv x i _ h hjx) (P.g i (j E x))
    have hnat : evU (ptV v (spOver ψ ≫ x)).left (P.U i ⊓ P.U (j E x)) (P.g i (j E x)).val =
        epsHom ψ (evU (ptV v x).left (P.U i ⊓ P.U (j E x)) (P.g i (j E x)).val) := by
      have e : (ptV v (spOver ψ ≫ x)).left = spMap (epsHom ψ : DualNumber E →+* DualNumber E') ≫ (ptV v x).left := by
        rw [ptV_nat, Over.comp_left]; rfl
      rw [e, evalSectionAtPointOrZero_specMap_comp _ _ _ _ _ _ _ (memV P hv x i _ h hjx)]
      rfl
    have e1 : dl (evU (ptV v (spOver ψ ≫ x)).left (P.U i ⊓ P.U (j E x)) (P.g i (j E x)).val) =
        ψ (dl (evU (ptV v x).left (P.U i ⊓ P.U (j E x)) (P.g i (j E x)).val)) := by
      rw [hnat, (dualNumberAlgHomMap_fst_snd_logDerivative R E E' ψ _).2.2 uG]
    have hcob : dl (evU (ptV v (spOver ψ ≫ x)).left (P.U (j E' (spOver ψ ≫ x)) ⊓ P.U (j E x))
        (P.g (j E' (spOver ψ ≫ x)) (j E x)).val) = k E' (spOver ψ ≫ x) - ψ (k E x) := hk E E' ψ x ⟨i, h⟩
    have hs := hs2 E E' ψ x i h
    obtain ⟨a1, a2⟩ := dualNumber_inl_mul_one_add_inr_fst_snd (s E x i) (dl (evU (ptV v x).left (P.U i ⊓ P.U (j E x)) (P.g i (j E x)).val) + k E x)
    obtain ⟨b1, b2⟩ := dualNumber_inl_mul_one_add_inr_fst_snd (s E' (spOver ψ ≫ x) i) (dl (evU (ptV v (spOver ψ ≫ x)).left
      (P.U i ⊓ P.U (j E' (spOver ψ ≫ x))) (P.g i (j E' (spOver ψ ≫ x))).val) + k E' (spOver ψ ≫ x))
    beta_reduce
    refine TrivSqZeroExt.ext ?_ ?_
    · rw [b1, (dualNumberAlgHomMap_fst_snd_logDerivative R E E' ψ _).1, a1, hs]
    · rw [b2, (dualNumberAlgHomMap_fst_snd_logDerivative R E E' ψ _).2.1, a2, hs, map_mul, map_add (f := _)]
      linear_combination (ψ (s E x i)) * (-hd + e1 - hcob)
  · intro E _ _ x i i' hi hi'
    have hjx : ⊤ ≤ x.left ⁻¹ᵁ chartsA P (j E x) := hj E x ⟨i, hi⟩
    have hc := evU_cocycle P hP (ptV v x).left i i' (j E x) (ptV_mem P hv x i hi)
      (ptV_mem P hv x i' hi') (ptV_mem P hv x _ hjx)
    have u1 := evU_isUnit' _ _ (memV P hv x i i' hi hi') (P.g i i')
    have u2 := evU_isUnit' _ _ (memV P hv x i' (j E x) hi' hjx) (P.g i' (j E x))
    have hd := dualNumberSndMulInverseFst_mul_units E _ _ u1 u2
    rw [← hc] at hd
    have hsnd := snd_eq_fst_mul_dl _ u1
    have hfst := fst_gV P hv x i i' hi hi'
    have ht := hs3 E x i i' hi hi'
    obtain ⟨a1, a2⟩ := dualNumber_inl_mul_one_add_inr_fst_snd (s E x i) (dl (evU (ptV v x).left (P.U i ⊓ P.U (j E x)) (P.g i (j E x)).val) + k E x)
    obtain ⟨b1, b2⟩ := dualNumber_inl_mul_one_add_inr_fst_snd (s E x i') (dl (evU (ptV v x).left (P.U i' ⊓ P.U (j E x)) (P.g i' (j E x)).val) + k E x)
    beta_reduce
    refine TrivSqZeroExt.ext ?_ ?_
    · rw [a1, TrivSqZeroExt.fst_mul, b1, hfst, ht]
    · rw [a2, TrivSqZeroExt.snd_mul, b1, b2, hsnd, hfst, hd, ht, smul_eq_mul, MulOpposite.smul_eq_mul_unop,
        MulOpposite.unop_op]
      ring
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsEighthPowerProjectionsExtendFromGeneric
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH
open scoped CategoryTheory.Obj
open GlobalTheory.Poinc GlobalTheory.Poinc.Eq8 Formalism.L2.Pj
attribute [local instance] Over.cartesianMonoidalCategory
open Classical

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.PowExtend

theorem isMonHom_of_components {𝒞 : Type*} [Category 𝒞] [CartesianMonoidalCategory 𝒞] {ι : Type}
    {A B C : 𝒞} [MonObj A] [MonObj B] [MonObj C] (p : ι → (B ⟶ C)) (hp : ∀ a, IsMonHom (p a))
    (hl : IsLimit (Fan.mk B p)) (e : A ⟶ B) (he : ∀ a, IsMonHom (e ≫ p a)) : IsMonHom e := by
  refine ⟨?_, ?_⟩
  · refine Fan.IsLimit.hom_ext hl _ _ fun a => ?_
    have := hp a
    have := he a
    change (_ ≫ e) ≫ p a = _ ≫ p a
    rw [Category.assoc, IsMonHom.one_hom, IsMonHom.one_hom]
  · refine Fan.IsLimit.hom_ext hl _ _ fun a => ?_
    have := hp a
    have := he a
    change (_ ≫ e) ≫ p a = (_ ≫ _) ≫ p a
    rw [Category.assoc, IsMonHom.mul_hom, Category.assoc, IsMonHom.mul_hom, ← Category.assoc,
      tensorHom_comp_tensorHom]

theorem exists_iso_of_universal {𝒞 : Type*} [Category 𝒞] {ι : Type} {A B C : 𝒞} (p : ι → (B ⟶ C))
    (hl : IsLimit (Fan.mk B p)) (q : ι → (A ⟶ C))
    (hq : ∀ (T : 𝒞) (y : ι → (T ⟶ C)), ∃! x : T ⟶ A, ∀ a, x ≫ q a = y a) :
    ∃ e : A ≅ B, ∀ a, e.hom ≫ p a = q a := by
  have hA : IsLimit (Fan.mk A q) :=
    mkFanLimit _ (fun s => (hq s.pt s.proj).exists.choose)
      (fun s a => (hq s.pt s.proj).exists.choose_spec a)
      (fun s m hm => (hq s.pt s.proj).unique hm (hq s.pt s.proj).exists.choose_spec)
  exact ⟨hA.conePointUniqueUpToIso hl, fun a => hA.conePointUniqueUpToIso_hom_comp hl ⟨a⟩⟩

theorem universal_of_iso {𝒞 : Type*} [Category 𝒞] {ι : Type} {A B C : 𝒞} (p : ι → (B ⟶ C))
    (hl : IsLimit (Fan.mk B p)) (E : A ≅ B) (T : 𝒞) (y : ι → (T ⟶ C)) :
    ∃! x : T ⟶ A, ∀ a, x ≫ (E.hom ≫ p a) = y a := by
  refine ⟨hl.lift (Fan.mk T y) ≫ E.inv, fun a => ?_, fun x hx => ?_⟩
  · rw [Category.assoc, E.inv_hom_id_assoc]
    exact hl.fac (Fan.mk T y) ⟨a⟩
  · rw [Iso.eq_comp_inv]
    refine Fan.IsLimit.hom_ext hl _ _ fun a => ?_
    exact ((Category.assoc _ _ _).trans (hx a)).trans (hl.fac (Fan.mk T y) ⟨a⟩).symm

theorem exists_pow_projections : ∀ (R : Type) [CommRing R] [IsDomain R] [IsNoetherianRing R] [IsIntegrallyClosed R] (G C : Over (Sp R)) [GrpObj G] [IsCommMonObj G] [GrpObj C] [IsCommMonObj C], IsSemiAbelian G → IsAbelianScheme C → ∀ pr' : Fin 8 → ((Over.pullback (jK R)).obj G ⟶ (Over.pullback (jK R)).obj C), (∀ a, IsMonHom (pr' a)) → (∀ (T' : Over (Sp (FractionRing R))) (y : Fin 8 → (T' ⟶ (Over.pullback (jK R)).obj C)), ∃! x : T' ⟶ (Over.pullback (jK R)).obj G, ∀ a, x ≫ pr' a = y a) → ∃ prO : Fin 8 → (G ⟶ C), (∀ a, IsMonHom (prO a)) ∧ (∀ a, (Over.pullback (jK R)).map (prO a) = pr' a) ∧ ∀ (T' : Over (Sp R)) (y : Fin 8 → (T' ⟶ C)), ∃! x : T' ⟶ G, ∀ a, x ≫ prO a = y a := by
  intro R _ _ _ _ G C _ _ _ _ hG hC pr' hm hu
  have hH : IsSemiAbelian (powObj C 8) :=
    GlobalTheory.SemiPow.isSemiAbelian_of_isPowGrp _ C (powObj C 8) 8 (powIsPowGrp C 8)
      (GlobalTheory.isSemiAbelian_of_isAbelianScheme C hC)
  let prK : Fin 8 → ((Over.pullback (jK R)).obj (powObj C 8) ⟶ (Over.pullback (jK R)).obj C) :=
    fun i => (Over.pullback (jK R)).map (powPr C i)
  have hlim : IsLimit (Fan.mk ((Over.pullback (jK R)).obj (powObj C 8)) prK) :=
    isLimitFanMkObjOfIsLimit (Over.pullback (jK R)) (fun _ : Fin 8 => C) (powPr C) (powIsLimit C 8)
  have hprKm : ∀ i, IsMonHom (prK i) := fun i =>
    inferInstanceAs (IsMonHom ((Over.pullback (jK R)).map (powPr C i)))
  obtain ⟨e, he⟩ := exists_iso_of_universal prK hlim pr' hu
  have hem : IsMonHom e.hom := isMonHom_of_components prK hprKm hlim e.hom fun a => by
    rw [he a]; exact hm a
  obtain ⟨E, ⟨hE, hEe⟩, -⟩ := @GlobalTheory.SemiAbExtDomain.existsUnique_iso_extension_generic R _ _ _ _
    (FractionRing R) _ _ _ G (powObj C 8) _ _ hG hH e hem
  refine ⟨fun a => E.hom ≫ powPr C a, fun a => inferInstance, fun a => ?_,
    universal_of_iso (powPr C) (powIsLimit C 8) E⟩
  rw [Functor.map_comp, ← he a]
  exact congrArg (· ≫ prK a) hEe

end GlobalTheory.PowExtend
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsEquivCmTypeRealEmbeddings
section
open NumberField UpperHalfPlane GlobalTheory.HilbFam GlobalTheory.QFam
open GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization (Emb Frac latM qPow upperHalf cK omegaFactor IsPartialZeta HasExpansion)
open GlobalTheory.IndefiniteRowSideFullHecke.DefiningCoordinates (iterD partialD)
open scoped Classical MatrixGroups nonZeroDivisors
open GlobalTheory.LatVal (Sz)
open GlobalTheory.LatJet (EisExp IsEis FR)
open GlobalTheory.CMVal (OF Af lattice IsCMType)
open GlobalTheory.IndefiniteRowSideFullHecke.DefiningCoordinates (IsDefSum IsEisValue polydisc)

namespace GlobalTheory.CMTypeEmb

theorem card_eq_finrank {E : Type} [Field E] [NumberField E] [IsCMField E] {I : Type} [Fintype I] {φ : I → E →+* ℂ}
    (hφ : IsCMType φ) : Fintype.card I = Module.finrank ℚ (FR E) := by
  have hc : Fintype.card I = Fintype.card (InfinitePlace E) :=
    Fintype.card_of_bijective (GlobalTheory.CMTypeCard.bijective_mk_of_isCMType hφ)
  have hE : Fintype.card (InfinitePlace E) = Fintype.card (InfinitePlace (FR E)) :=
    Fintype.card_congr (IsCMField.equivInfinitePlace E)
  have h1 := InfinitePlace.card_add_two_mul_card_eq_rank (FR E)
  have hr : InfinitePlace.nrComplexPlaces (FR E) = 0 := IsTotallyReal.nrComplexPlaces_eq_zero (FR E)
  have h3 := InfinitePlace.card_eq_nrRealPlaces_add_nrComplexPlaces (K := FR E)
  omega

theorem exists_equiv : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (I : Type) [Fintype I] (φ : I → E →+* ℂ),
    IsCMType φ → ∃ e : I ≃ Emb (FR E), ∀ i (x : FR E), φ i (x : E) = ((e i x : ℝ) : ℂ) := by
  intro E _ _ _ I _ φ hφ
  have hcard : Fintype.card I = Module.finrank ℚ (FR E) := card_eq_finrank hφ
  let e₀ : Fin (Module.finrank ℚ (FR E)) ≃ I := (Fintype.equivFinOfCardEq hcard).symm
  obtain ⟨e, he⟩ := GlobalTheory.CMTypeRestrict.exists_equiv_realEmbeddings E I φ hφ e₀
  refine ⟨e₀.symm.trans e, fun i x ↦ ?_⟩
  have := he (e₀.symm i) x
  simp only [Equiv.apply_symm_apply] at this
  simp only [Equiv.trans_apply]
  exact this.symm

end GlobalTheory.CMTypeEmb
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsEquivGlobalOneFormsBaseChange
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.AbCoh
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.DeRham

namespace GlobalTheory.AbCoh

theorem isAffineOpen_preimage_of_isPullback (R R' : Type) [CommRing R] [CommRing R'] [Algebra R R']
    (X X' : Scheme.{0}) (s : X ⟶ Sp R) (s' : X' ⟶ Sp R') (φ : X' ⟶ X)
    (h : IsPullback φ s' s (spMap (algebraMap R R'))) (U : X.affineOpens) : IsAffineOpen (φ ⁻¹ᵁ U.1) := by
  haveI : IsAffineHom φ := MorphismProperty.of_isPullback (P := @IsAffineHom) h.flip inferInstance
  exact U.2.preimage φ

theorem exists_equiv_globForm_baseChange : ∀ (R R' : Type) [CommRing R] [CommRing R'] [Algebra R R'] (X X' : Scheme.{0}) (s : X ⟶ Sp R) (s' : X' ⟶ Sp R') (φ : X' ⟶ X) (h : IsPullback φ s' s (spMap (algebraMap R R'))), HasFrame (OAff s) → CohomZeroIsConstants (OAff s) → HasFrame (OAff s') → CohomZeroIsConstants (OAff s') → Flat s' → Surjective s' → ∃ e : R' ⊗[R] GlobForm s ≃ₗ[R'] GlobForm s', ∀ c, e (1 ⊗ₜ c) = GlobalTheory.CechDR.pullForm h.w c := by
  intro R R' _ _ _ X X' s s' φ h hF hC hF' hC' hfl hsu
  have hb : Function.Bijective (liftSemi (pullForm h.w)) :=
    _root_.GlobalTheory.bijective_of_lTensor_flat_family R' _ _ (liftSemi (pullForm h.w)) X.affineOpens (fun U ↦ Sec s' (φ ⁻¹ᵁ U.1))
      (fun U ↦ GlobalTheory.T.flat_sections_affineOpen_of_flat_scheme R' X' s' hfl ⟨_, isAffineOpen_preimage_of_isPullback R R' X X' s s' φ h U⟩)
      (_root_.GlobalTheory.PointSec.exists_affine_map_ne_top R' X X' s' φ hsu)
      (fun U ↦ _root_.GlobalTheory.AbCoh.lTensor_liftSemi_pullForm_bijective R R' X X' s s' φ h hF hC hF' hC' U
        (isAffineOpen_preimage_of_isPullback R R' X X' s s' φ h U))
  refine ⟨LinearEquiv.ofBijective _ hb, fun c ↦ ?_⟩
  rw [LinearEquiv.ofBijective_apply, liftSemi_tmul, one_smul]

end GlobalTheory.AbCoh
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsEtaleAwayOfBijectiveMapBaseChange
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

noncomputable section
namespace GlobalTheory.Mum
open KaehlerDifferential TensorProduct

theorem bijective_of_bijective_lTensor_residueField {R M N : Type*} [CommRing R] [IsLocalRing R]
    [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    [Module.Finite R M] [Module.Finite R N] [Module.Projective R N] (l : M →ₗ[R] N)
    (h : Function.Bijective (l.lTensor (ResidueField R))) : Function.Bijective l := by
  have : Module.Free R N := Module.free_of_flat_of_isLocalRing
  refine ⟨?_, ?_⟩
  · obtain ⟨l', hl'⟩ := (IsLocalRing.split_injective_iff_lTensor_residueField_injective l).mpr h.1
    exact Function.HasLeftInverse.injective ⟨l', LinearMap.congr_fun hl'⟩
  · have hex := lTensor_exact (ResidueField R) (LinearMap.exact_map_mkQ_range l)
      (Submodule.mkQ_surjective _)
    have hsub : Subsingleton (ResidueField R ⊗[R] (N ⧸ LinearMap.range l)) := by
      refine subsingleton_of_forall_eq 0 fun y => ?_
      obtain ⟨x, rfl⟩ := LinearMap.lTensor_surjective (ResidueField R) (Submodule.mkQ_surjective _) y
      obtain ⟨z, rfl⟩ := h.2 x
      exact hex.apply_apply_eq_zero z
    rw [IsLocalRing.subsingleton_tensorProduct] at hsub
    rw [← LinearMap.range_eq_top]
    exact Submodule.Quotient.subsingleton_iff.mp hsub

theorem formallyEtale_of_bijective_mapBaseChange (R P B : Type*) [CommRing R] [CommRing P]
    [CommRing B] [Algebra R P] [Algebra R B] [Algebra P B] [IsScalarTower R P B]
    [Algebra.FormallySmooth R B] (h : Function.Bijective (mapBaseChange R P B)) :
    Algebra.FormallyEtale P B := by
  have h1 : Subsingleton Ω[B⁄P] := by
    refine subsingleton_of_forall_eq 0 fun x => ?_
    obtain ⟨y, rfl⟩ := map_surjective R P B x
    exact (exact_mapBaseChange_map R P B y).mpr (h.2 y)
  have h2 : Subsingleton (Algebra.H1Cotangent P B) := by
    refine subsingleton_of_forall_eq 0 fun x => ?_
    have h3 : Algebra.H1Cotangent.δ R P B x = 0 := by
      apply h.1
      rw [map_zero]
      exact (Algebra.H1Cotangent.exact_δ_mapBaseChange R P B _).mpr ⟨x, rfl⟩
    obtain ⟨y, rfl⟩ := (Algebra.H1Cotangent.exact_map_δ R P B x).mp h3
    rw [Subsingleton.elim y 0, map_zero]
  exact ⟨h1, h2⟩

theorem bijective_lTensor_baseChange_of_bijective {B M N : Type*} [CommRing B]
    [AddCommGroup M] [Module B M] [AddCommGroup N] [Module B N] (Q : Ideal B) [Q.IsPrime]
    (φ : M →ₗ[B] N) (h : Function.Bijective (φ.lTensor Q.ResidueField)) :
    Function.Bijective ((φ.baseChange (Localization.AtPrime Q)).lTensor
      (ResidueField (Localization.AtPrime Q))) := by
  let BQ := Localization.AtPrime Q
  let k := ResidueField BQ
  let eM := AlgebraTensorModule.cancelBaseChange B BQ k k M
  let eN := AlgebraTensorModule.cancelBaseChange B BQ k k N
  have key : ∀ x, eN ((φ.baseChange BQ).lTensor k x) = φ.lTensor Q.ResidueField (eM x) := by
    intro x
    induction x using TensorProduct.induction_on with
    | zero => simp
    | add x y hx hy => simp only [map_add (f := _), hx, hy]
    | tmul c y =>
      induction y using TensorProduct.induction_on with
      | zero => simp
      | add y z hy hz => simp only [tmul_add, map_add (f := _)] at hy hz ⊢; rw [hy, hz]
      | tmul q m => simp [eM, eN]
  have : ⇑((φ.baseChange BQ).lTensor k) = eN.symm ∘ (φ.lTensor Q.ResidueField) ∘ eM := by
    funext x; simp [← key]
  rw [this]
  exact eN.symm.bijective.comp (h.comp eM.bijective)

theorem kaehler_map_map_apply (A C B BQ : Type) [CommRing A] [CommRing C] [CommRing B] [CommRing BQ] [Algebra A C] [Algebra A B] [Algebra C B] [IsScalarTower A C B]
   [Algebra B BQ] [Algebra A BQ] [Algebra C BQ] [IsScalarTower A B BQ] [IsScalarTower C B BQ] [IsScalarTower A C BQ] (ω : Ω[C⁄A]) :
    map A A B BQ (map A A C B ω) = map A A C BQ ω := by
  have : ((map A A B BQ).restrictScalars C).comp (map A A C B) = map A A C BQ := by
    apply Derivation.liftKaehlerDifferential_unique
    ext x
    simp [map_D, ← IsScalarTower.algebraMap_apply]
  exact LinearMap.congr_fun this ω

theorem exists_etale_away_of_bijective_mapBaseChange : ∀ (A C B : Type) [CommRing A] [CommRing C]
    [CommRing B] [Algebra A C] [Algebra A B] [Algebra C B] [IsScalarTower A C B] [Algebra.Smooth A C]
    [Algebra.Smooth A B] (Q : Ideal B) [Q.IsPrime],
    Function.Bijective ((KaehlerDifferential.mapBaseChange A C B).lTensor Q.ResidueField) →
      ∃ f : B, f ∉ Q ∧ Algebra.Etale C (Localization.Away f) := by
  intro A C B _ _ _ _ _ _ _ _ _ Q _ h
  let BQ := Localization.AtPrime Q
  let φ := mapBaseChange A C B
  have hψ₀ : Function.Bijective (φ.baseChange BQ) :=
    bijective_of_bijective_lTensor_residueField _ (bijective_lTensor_baseChange_of_bijective Q φ h)
  let eM := AlgebraTensorModule.cancelBaseChange C B BQ BQ Ω[C⁄A]
  have hbc : IsBaseChange BQ (map A A B BQ) :=
    (isLocalizedModule_iff_isBaseChange Q.primeCompl BQ _).mp
      (isLocalizedModule_map A B BQ Q.primeCompl)
  let eN := hbc.equiv
  have key : ∀ x, mapBaseChange A C BQ (eM x) = eN (φ.baseChange BQ x) := by
    intro x
    induction x using TensorProduct.induction_on with
    | zero => simp
    | add x y hx hy => simp only [map_add (f := _), hx, hy]
    | tmul q y =>
      induction y using TensorProduct.induction_on with
      | zero => simp
      | add y z hy hz => simp only [tmul_add, map_add (f := _)] at hy hz ⊢; rw [hy, hz]
      | tmul b ω =>
        simp only [eM, eN, φ, AlgebraTensorModule.cancelBaseChange_tmul, mapBaseChange_tmul,
          LinearMap.baseChange_tmul]
        rw [IsBaseChange.equiv_tmul, map_smul, kaehler_map_map_apply, smul_assoc, smul_comm q b]
  have hψ : Function.Bijective (mapBaseChange A C BQ) := by
    have : ⇑(mapBaseChange A C BQ) = eN ∘ (φ.baseChange BQ) ∘ eM.symm := by
      funext x; simp [← key]
    rw [this]
    exact eN.bijective.comp (hψ₀.comp eM.symm.bijective)
  haveI : Algebra.FormallySmooth B BQ := Algebra.FormallySmooth.of_isLocalization Q.primeCompl
  haveI : Algebra.FormallySmooth A BQ := Algebra.FormallySmooth.comp A B BQ
  haveI : Algebra.IsEtaleAt C Q := formallyEtale_of_bijective_mapBaseChange A C BQ hψ
  haveI : Algebra.FinitePresentation C B :=
    Algebra.FinitePresentation.of_restrict_scalars_finitePresentation A C B
  exact Algebra.exists_etale_of_isEtaleAt Q

end GlobalTheory.Mum
end
end

