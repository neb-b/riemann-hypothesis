module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.TateProductRigidificationTrivial
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0056
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0059
public import Development.AbelianVarietyTheory.Definitions.Divisors.MulSmulIdemMem
public import Development.AbelianVarietyTheory.Definitions.Divisors.WedgeNrmLeOfWedgeNormLe
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0045
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0044
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1645
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2076
public import Development.AbelianVarietyTheory.Definitions.Divisors.NormNegCmConstantEqAtAllEmbeddings
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1981
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1870
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1877
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1871
public import Development.AbelianVarietyTheory.Definitions.Divisors.OrdGeOfForall
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0012
public import ReciprocityTheory.AnalyticForms.RegularLocalRings.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0028
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0086
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2052
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2064
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0013

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemRangeAppOfFlatBaseChangeEqualised
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

noncomputable section

namespace GlobalTheory.Mum.AffDesc

open TensorProduct

theorem appLE_eq_of_eq {X Y : Scheme.{0}} {f g : X ⟶ Y} (h : f = g) (U : Y.Opens) (V : X.Opens)
    (e : V ≤ f ⁻¹ᵁ U) (e' : V ≤ g ⁻¹ᵁ U) : f.appLE U V e = g.appLE U V e' := by
  subst h; rfl

theorem isoPushout_desc_tmul {R0 A B : Type} [CommRing R0] [CommRing A] [CommRing B] [Algebra R0 A]
    [Algebra R0 B] {D : CommRingCat.{0}} (u : CommRingCat.of A ⟶ D) (v : CommRingCat.of B ⟶ D)
    (w : CommRingCat.ofHom (algebraMap R0 A) ≫ u = CommRingCat.ofHom (algebraMap R0 B) ≫ v) (a : A) (b : B) :
    ((CommRingCat.isPushout_tensorProduct R0 A B).isoPushout.hom ≫ pushout.desc u v w).hom (a ⊗ₜ b) =
      u.hom a * v.hom b := by
  have e : a ⊗ₜ[R0] b = Algebra.TensorProduct.includeLeftRingHom a *
      Algebra.TensorProduct.includeRight.toRingHom b := by
    simp [Algebra.TensorProduct.tmul_mul_tmul]
  rw [e, map_mul]
  have h1 := congrArg (fun φ => φ.hom a)
    ((CommRingCat.isPushout_tensorProduct R0 A B).inl_isoPushout_hom =≫ pushout.desc u v w)
  have h2 := congrArg (fun φ => φ.hom b)
    ((CommRingCat.isPushout_tensorProduct R0 A B).inr_isoPushout_hom =≫ pushout.desc u v w)
  simp only [Category.assoc, pushout.inl_desc, pushout.inr_desc, CommRingCat.hom_comp, RingHom.comp_apply,
    CommRingCat.hom_ofHom] at h1 h2
  rw [← h1, ← h2]
  rfl

theorem appLE_apply_appLE {X Y Y' Z : Scheme.{0}} (f : X ⟶ Y) (g : Y ⟶ Z) (f' : X ⟶ Y') (g' : Y' ⟶ Z)
    (h : f ≫ g = f' ≫ g') (U : Z.Opens) (V : Y.Opens) (V' : Y'.Opens) (W : X.Opens) (e₁ : V ≤ g ⁻¹ᵁ U)
    (e₂ : W ≤ f ⁻¹ᵁ V) (e₁' : V' ≤ g' ⁻¹ᵁ U) (e₂' : W ≤ f' ⁻¹ᵁ V') (x : Γ(Z, U)) :
    (f.appLE V W e₂).hom ((g.appLE U V e₁).hom x) = (f'.appLE V' W e₂').hom ((g'.appLE U V' e₁').hom x) := by
  have a := Scheme.Hom.appLE_comp_appLE f g U V W e₁ e₂
  have b := Scheme.Hom.appLE_comp_appLE f' g' U V' W e₁' e₂'
  have c := appLE_eq_of_eq h U W (by rw [Scheme.Hom.comp_preimage]; exact le_trans e₂ (Scheme.Hom.preimage_mono f e₁))
    (by rw [Scheme.Hom.comp_preimage]; exact le_trans e₂' (Scheme.Hom.preimage_mono f' e₁'))
  exact congrArg (fun φ => CommRingCat.Hom.hom φ x) (a.trans (c.trans b.symm))

theorem appTop_eq_appLE {X Y : Scheme.{0}} (f : X ⟶ Y) : f.appTop = f.appLE ⊤ ⊤ le_top :=
  Scheme.Hom.app_eq_appLE f

end GlobalTheory.Mum.AffDesc

namespace GlobalTheory.Mum.AffDesc
open TensorProduct

theorem mem_range_app_of_flat : ∀ (R : Type) [CommRing R] (S Y Z : Scheme.{0}) (π : S ⟶ Sp R) (y : Y ⟶ Sp R) (p : Z ⟶ Y) (q : Z ⟶ S), IsProper π → Flat y → IsPullback p q y π → ∀ r : pullback p p ⟶ pullback π π, r ≫ pullback.fst π π = pullback.fst p p ≫ q → r ≫ pullback.snd π π = pullback.snd p p ≫ q → IsPullback r (pullback.fst p p ≫ p) (pullback.fst π π ≫ π) y → (∀ x : Γ(S, ⊤), (pullback.fst π π).appTop.hom x = (pullback.snd π π).appTop.hom x → x ∈ Set.range π.appTop.hom) → ∀ V : Y.Opens, IsAffineOpen V → ∀ f : Γ(Z, p ⁻¹ᵁ V), (∀ h : pullback.snd p p ⁻¹ᵁ (p ⁻¹ᵁ V) = pullback.fst p p ⁻¹ᵁ (p ⁻¹ᵁ V), ((pullback.fst p p).app _).hom f = ((pullback.snd p p).appLE _ _ h.ge).hom f) → f ∈ Set.range (p.app V).hom := by
  intro R _ S Y Z π y p q hπ hy H r h1 h2 hP hx V hV f hf
  classical
  haveI : CompactSpace S := QuasiCompact.compactSpace_of_compactSpace π
  haveI : QuasiSeparatedSpace S := (quasiSeparated_iff_quasiSeparatedSpace π).1 inferInstance
  haveI : CompactSpace (pullback π π : Scheme) :=
    QuasiCompact.compactSpace_of_compactSpace (pullback.fst π π ≫ π)
  have hUY1 : p ⁻¹ᵁ V = q ⁻¹ᵁ ⊤ ⊓ p ⁻¹ᵁ V := by simp
  have hUY2 : pullback.fst p p ⁻¹ᵁ (p ⁻¹ᵁ V) = r ⁻¹ᵁ ⊤ ⊓ (pullback.fst p p ≫ p) ⁻¹ᵁ V := by
    simp [Scheme.Hom.comp_preimage]
  have i1 := isIso_pushoutSection_of_isQuasiSeparated_of_flat_right H.flip (US := ⊤) (UX := ⊤) (UT := V)
    le_top le_top hUY1 (isAffineOpen_top _) hV isCompact_univ isQuasiSeparated_univ
  have m2 := mono_pushoutSection_of_isCompact_of_flat_right hP (US := ⊤) (UX := ⊤) (UT := V)
    le_top le_top hUY2 (isAffineOpen_top _) hV isCompact_univ
  letI aB : Algebra Γ(Sp R, ⊤) Γ(S, ⊤) := (π.appLE ⊤ ⊤ le_top).hom.toAlgebra
  letI aA : Algebra Γ(Sp R, ⊤) Γ(Y, V) := (y.appLE ⊤ V le_top).hom.toAlgebra
  letI aC : Algebra Γ(Sp R, ⊤) Γ(pullback π π, ⊤) := ((pullback.fst π π ≫ π).appLE ⊤ ⊤ le_top).hom.toAlgebra
  haveI : Module.Flat Γ(Sp R, ⊤) Γ(Y, V) := y.flat_appLE (isAffineOpen_top _) hV le_top
  let ΦB := (CommRingCat.isPushout_tensorProduct Γ(Sp R, ⊤) Γ(S, ⊤) Γ(Y, V)).isoPushout.hom ≫
    pushoutSection H.flip (US := ⊤) (UX := ⊤) (UT := V) le_top le_top hUY1
  let ΦC := (CommRingCat.isPushout_tensorProduct Γ(Sp R, ⊤) Γ(pullback π π, ⊤) Γ(Y, V)).isoPushout.hom ≫
    pushoutSection hP (US := ⊤) (UX := ⊤) (UT := V) le_top le_top hUY2
  have hB : Function.Surjective ΦB.hom := by
    have : IsIso ΦB := by dsimp only [ΦB]; infer_instance
    exact (ConcreteCategory.bijective_of_isIso ΦB).2
  have hC : Function.Injective ΦC.hom := by
    have : Mono ΦC := by dsimp only [ΦC]; infer_instance
    exact (ConcreteCategory.mono_iff_injective_of_preservesPullback ΦC).1 this
  have fB : ∀ (b : Γ(S, ⊤)) (a : Γ(Y, V)), ΦB.hom (b ⊗ₜ a) =
      (q.appLE ⊤ (p ⁻¹ᵁ V) (by simp)).hom b * (p.appLE V (p ⁻¹ᵁ V) le_rfl).hom a :=
    fun b a => isoPushout_desc_tmul _ _ _ b a
  have fC : ∀ (c : Γ(pullback π π, ⊤)) (a : Γ(Y, V)), ΦC.hom (c ⊗ₜ a) =
      (r.appLE ⊤ (pullback.fst p p ⁻¹ᵁ (p ⁻¹ᵁ V)) (by simp)).hom c *
        ((pullback.fst p p ≫ p).appLE V (pullback.fst p p ⁻¹ᵁ (p ⁻¹ᵁ V)) (by simp [Scheme.Hom.comp_preimage])).hom a :=
    fun c a => isoPushout_desc_tmul _ _ _ c a
  have k1 : ∀ x, (pullback.fst π π).appLE ⊤ ⊤ le_top ((π.appLE ⊤ ⊤ le_top) x) =
      ((pullback.fst π π ≫ π).appLE ⊤ ⊤ le_top) x := fun x =>
    congrArg (fun φ => CommRingCat.Hom.hom φ x) (Scheme.Hom.appLE_comp_appLE (pullback.fst π π) π ⊤ ⊤ ⊤ le_top le_top)
  have k2 : ∀ x, (pullback.snd π π).appLE ⊤ ⊤ le_top ((π.appLE ⊤ ⊤ le_top) x) =
      ((pullback.fst π π ≫ π).appLE ⊤ ⊤ le_top) x := fun x =>
    (congrArg (fun φ => CommRingCat.Hom.hom φ x) (Scheme.Hom.appLE_comp_appLE (pullback.snd π π) π ⊤ ⊤ ⊤ le_top le_top)).trans
      (congrArg (fun φ => CommRingCat.Hom.hom φ x) (appLE_eq_of_eq (pullback.condition (f := π) (g := π)).symm _ _ _ _))
  let d : Γ(S, ⊤) →ₗ[Γ(Sp R, ⊤)] Γ(pullback π π, ⊤) :=
    { toFun := fun x => (pullback.fst π π).appLE ⊤ ⊤ le_top x - (pullback.snd π π).appLE ⊤ ⊤ le_top x
      map_add' := fun x x' => by simp only [map_add (f := _)]; abel
      map_smul' := fun c x => by
        simp only [Algebra.smul_def, RingHom.algebraMap_toAlgebra, map_mul, k1, k2, RingHom.id_apply]
        ring }
  have hex : Function.Exact (Algebra.linearMap Γ(Sp R, ⊤) Γ(S, ⊤)) d := by
    intro x
    constructor
    · intro h0
      have e0 : (pullback.fst π π).appTop.hom x = (pullback.snd π π).appTop.hom x := by
        rw [appTop_eq_appLE, appTop_eq_appLE]; exact sub_eq_zero.1 h0
      obtain ⟨c, hc⟩ := hx x e0
      refine ⟨c, ?_⟩
      rw [appTop_eq_appLE] at hc
      exact hc
    · rintro ⟨c, rfl⟩
      show (pullback.fst π π).appLE ⊤ ⊤ le_top ((π.appLE ⊤ ⊤ le_top) c) -
        (pullback.snd π π).appLE ⊤ ⊤ le_top ((π.appLE ⊤ ⊤ le_top) c) = 0
      rw [k1, k2, sub_self]
  have hex' := Module.Flat.rTensor_exact Γ(Y, V) hex
  have hEq : pullback.snd p p ⁻¹ᵁ (p ⁻¹ᵁ V) = pullback.fst p p ⁻¹ᵁ (p ⁻¹ᵁ V) := by
    rw [← Scheme.Hom.comp_preimage, ← Scheme.Hom.comp_preimage, pullback.condition]
  have c1 : ∀ b, ((pullback.fst p p).app (p ⁻¹ᵁ V)).hom ((q.appLE ⊤ (p ⁻¹ᵁ V) (by simp)).hom b) =
      (r.appLE ⊤ (pullback.fst p p ⁻¹ᵁ (p ⁻¹ᵁ V)) (by simp)).hom ((pullback.fst π π).appLE ⊤ ⊤ le_top b) :=
    fun b => by
      rw [Scheme.Hom.app_eq_appLE]
      exact appLE_apply_appLE (pullback.fst p p) q r (pullback.fst π π) h1.symm ⊤ (p ⁻¹ᵁ V) ⊤
        (pullback.fst p p ⁻¹ᵁ (p ⁻¹ᵁ V)) (by simp) le_rfl le_top (by simp) b
  have c2 : ∀ b, ((pullback.snd p p).appLE _ _ hEq.ge).hom ((q.appLE ⊤ (p ⁻¹ᵁ V) (by simp)).hom b) =
      (r.appLE ⊤ (pullback.fst p p ⁻¹ᵁ (p ⁻¹ᵁ V)) (by simp)).hom ((pullback.snd π π).appLE ⊤ ⊤ le_top b) :=
    fun b => appLE_apply_appLE (pullback.snd p p) q r (pullback.snd π π) h2.symm ⊤ (p ⁻¹ᵁ V) ⊤
      (pullback.fst p p ⁻¹ᵁ (p ⁻¹ᵁ V)) (by simp) hEq.ge le_top (by simp) b
  have c3 : ∀ a, ((pullback.fst p p).app (p ⁻¹ᵁ V)).hom ((p.appLE V (p ⁻¹ᵁ V) le_rfl).hom a) =
      ((pullback.fst p p ≫ p).appLE V (pullback.fst p p ⁻¹ᵁ (p ⁻¹ᵁ V)) (by simp [Scheme.Hom.comp_preimage])).hom a :=
    fun a => by
      rw [Scheme.Hom.app_eq_appLE]
      exact congrArg (fun φ => CommRingCat.Hom.hom φ a)
        (Scheme.Hom.appLE_comp_appLE (pullback.fst p p) p V (p ⁻¹ᵁ V) (pullback.fst p p ⁻¹ᵁ (p ⁻¹ᵁ V)) le_rfl le_rfl)
  have c4 : ∀ a, ((pullback.snd p p).appLE _ _ hEq.ge).hom ((p.appLE V (p ⁻¹ᵁ V) le_rfl).hom a) =
      ((pullback.fst p p ≫ p).appLE V (pullback.fst p p ⁻¹ᵁ (p ⁻¹ᵁ V)) (by simp [Scheme.Hom.comp_preimage])).hom a :=
    fun a => (congrArg (fun φ => CommRingCat.Hom.hom φ a)
      (Scheme.Hom.appLE_comp_appLE (pullback.snd p p) p V (p ⁻¹ᵁ V) (pullback.fst p p ⁻¹ᵁ (p ⁻¹ᵁ V)) le_rfl hEq.ge)).trans
      (congrArg (fun φ => CommRingCat.Hom.hom φ a) (appLE_eq_of_eq (pullback.condition (f := p) (g := p)).symm V
        (pullback.fst p p ⁻¹ᵁ (p ⁻¹ᵁ V)) _ _))
  have key : ∀ t, ΦC.hom (d.rTensor Γ(Y, V) t) = ((pullback.fst p p).app (p ⁻¹ᵁ V)).hom (ΦB.hom t) -
      ((pullback.snd p p).appLE _ _ hEq.ge).hom (ΦB.hom t) := by
    intro t
    induction t using TensorProduct.induction_on with
    | zero => simp
    | tmul b a =>
      rw [LinearMap.rTensor_tmul, fC, fB, map_mul, map_mul, c1, c2, c3, c4]
      change (r.appLE _ _ _).hom ((pullback.fst π π).appLE ⊤ ⊤ le_top b - (pullback.snd π π).appLE ⊤ ⊤ le_top b) * _ = _
      rw [map_sub, sub_mul]
    | add t t' ht ht' =>
      rw [map_add (f := _), map_add (f := _), ht, ht', map_add (f := _), map_add (f := _), map_add (f := _)]
      abel
  obtain ⟨t, rfl⟩ := hB f
  have hz : d.rTensor Γ(Y, V) t = 0 := hC (by rw [key, map_zero, hf hEq, sub_self])
  obtain ⟨s, rfl⟩ := (hex' t).1 hz
  clear hf hz key
  induction s using TensorProduct.induction_on with
  | zero => exact ⟨0, by simp⟩
  | tmul c a =>
    rw [LinearMap.rTensor_tmul, fB]
    refine ⟨(y.appLE ⊤ V le_top).hom c * a, ?_⟩
    rw [map_mul, Scheme.Hom.app_eq_appLE]
    congr 1
    exact appLE_apply_appLE p y q π H.w ⊤ V ⊤ (p ⁻¹ᵁ V) le_top le_rfl le_top (by simp) c
  | add s s' hs hs' =>
    obtain ⟨u, hu⟩ := hs
    obtain ⟨u', hu'⟩ := hs'
    exact ⟨u + u', by rw [map_add (f := _), hu, hu', map_add (f := _), map_add (f := _)]⟩

end GlobalTheory.Mum.AffDesc
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemRangeAppTopOfFibreSquareProjectionsEq
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum
open scoped TensorProduct

namespace GlobalTheory.Mum

theorem mem_range_of_tmul_eq_tmul {R A : Type} [CommRing R] [IsDomain R] [IsIntegrallyClosed R] [CommRing A]
    [IsDomain A] [Algebra R A] (hinj : Function.Injective (algebraMap R A)) (a : A) (ha : IsIntegral R a)
    (h : algebraMap A (FractionRing A) a ⊗ₜ[R] (1 : FractionRing A) =
      (1 : FractionRing A) ⊗ₜ[R] algebraMap A (FractionRing A) a) :
    a ∈ Set.range (algebraMap R A) := by
  have hRL : Function.Injective (algebraMap R (FractionRing A)) := by
    rw [IsScalarTower.algebraMap_eq R A (FractionRing A)]
    exact (IsFractionRing.injective A (FractionRing A)).comp hinj
  haveI : FaithfulSMul R (FractionRing A) := (faithfulSMul_iff_algebraMap_injective R _).mpr hRL
  letI : Algebra (FractionRing R) (FractionRing A) := FractionRing.liftAlgebra R (FractionRing A)
  haveI := FractionRing.isScalarTower_liftAlgebra R (FractionRing A)
  obtain ⟨φ, hφ⟩ := LinearMap.exists_leftInverse_of_injective (Algebra.linearMap (FractionRing R) (FractionRing A))
    (LinearMap.ker_eq_bot.mpr (algebraMap (FractionRing R) (FractionRing A)).injective)
  have hφ1 : φ 1 = 1 := by simpa using congr($hφ 1)
  let Φ : FractionRing A ⊗[R] FractionRing A →ₗ[R] FractionRing A :=
    LinearMap.mul' R (FractionRing A) ∘ₗ
      TensorProduct.map ((Algebra.linearMap (FractionRing R) (FractionRing A) ∘ₗ φ).restrictScalars R) LinearMap.id
  have key := congr(Φ $h)
  simp only [Φ, LinearMap.comp_apply, TensorProduct.map_tmul, LinearMap.restrictScalars_apply,
    Algebra.linearMap_apply, LinearMap.id_apply, LinearMap.mul'_apply, hφ1, map_one] at key
  replace key : algebraMap (FractionRing R) (FractionRing A) (φ (algebraMap A (FractionRing A) a)) =
      algebraMap A (FractionRing A) a := by
    convert key using 1
    · exact (_root_.mul_one _).symm
    · exact (_root_.one_mul _).symm
  have hint : IsIntegral R (φ (algebraMap A (FractionRing A) a)) := by
    rw [← isIntegral_algHom_iff (IsScalarTower.toAlgHom R (FractionRing R) (FractionRing A))
      (algebraMap (FractionRing R) (FractionRing A)).injective]
    change IsIntegral R (algebraMap (FractionRing R) (FractionRing A) _)
    rw [key]
    exact ha.map (IsScalarTower.toAlgHom R A (FractionRing A))
  obtain ⟨r, hr⟩ := IsIntegrallyClosed.isIntegral_iff.mp hint
  refine ⟨r, IsFractionRing.injective A (FractionRing A) ?_⟩
  rw [← IsScalarTower.algebraMap_apply, IsScalarTower.algebraMap_apply R (FractionRing R) (FractionRing A), hr, key]

end GlobalTheory.Mum

namespace GlobalTheory.Mum

theorem mem_range_appTop_of_fst_eq_snd : ∀ (R : Type) [CommRing R] [IsDomain R] [IsIntegrallyClosed R] (S : Scheme.{0})
    (π : S ⟶ Sp R), IsProper π → IsIntegral S → Function.Injective π.appTop.hom → ∀ x : Γ(S, ⊤),
    (pullback.fst π π).appTop.hom x = (pullback.snd π π).appTop.hom x → x ∈ Set.range π.appTop.hom := by
  intro R _ _ _ S π hP hI hinj x hx
  obtain ⟨s⟩ : Nonempty S := hI.nonempty
  obtain ⟨U, hU, hsU, -⟩ := exists_isAffineOpen_mem_and_subset (show s ∈ (⊤ : S.Opens) from trivial)
  haveI : Nonempty U := ⟨⟨s, hsU⟩⟩
  let res := S.presheaf.map (homOfLE (le_top : U ≤ ⊤)).op
  have hres : Function.Injective res.hom := map_injective_of_isIntegral S _
  have happ : ∀ t, (π.appLE ⊤ U le_top).hom t = res.hom (π.appTop.hom t) := fun t => rfl
  let ρ : R →+* Γ(S, U) := ((Scheme.ΓSpecIso (CommRingCat.of R)).inv ≫ π.appLE ⊤ U le_top).hom
  letI : Algebra R Γ(S, U) := ρ.toAlgebra
  have hρ : ∀ t, (π.appLE ⊤ U le_top).hom t = algebraMap R Γ(S, U) ((Scheme.ΓSpecIso (CommRingCat.of R)).hom.hom t) := by
    intro t
    change _ = ρ _
    simp only [ρ, CommRingCat.hom_comp, RingHom.comp_apply]
    congr 1
    exact (Iso.hom_inv_id_apply (Scheme.ΓSpecIso (CommRingCat.of R)) t).symm
  have hρinj : Function.Injective (algebraMap R Γ(S, U)) := by
    intro a b hab
    have h1 : ∀ c, algebraMap R Γ(S, U) c = res.hom (π.appTop.hom ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom c)) :=
      fun c => rfl
    rw [h1, h1] at hab
    exact (Scheme.ΓSpecIso (CommRingCat.of R)).commRingCatIsoToRingEquiv.symm.injective (hinj (hres hab))
  haveI : UniversallyClosed π := inferInstance
  have hxint : IsIntegral R (res.hom x) := by
    obtain ⟨p, hpm, hp⟩ := isIntegral_appTop_of_universallyClosed π x
    refine ⟨p.map (Scheme.ΓSpecIso (CommRingCat.of R)).hom.hom, hpm.map _, ?_⟩
    rw [Polynomial.eval₂_map]
    have hc : (algebraMap R Γ(S, U)).comp (Scheme.ΓSpecIso (CommRingCat.of R)).hom.hom = res.hom.comp π.appTop.hom := by
      ext t
      exact (hρ t).symm.trans (happ t)
    rw [hc, ← Polynomial.hom_eval₂, hp, map_zero]
  have H : IsPullback (pullback.fst π π) (pullback.snd π π) π π := IsPullback.of_hasPullback π π
  have po := (isIso_pushoutSection_iff H (US := ⊤) (UT := U) (UX := U) le_top le_top rfl).mp
    (isIso_pushoutSection_of_isAffineOpen H le_top le_top rfl (isAffineOpen_top _) hU hU)
  let j₁ : Γ(S, U) →+* FractionRing Γ(S, U) ⊗[R] FractionRing Γ(S, U) :=
    Algebra.TensorProduct.includeLeftRingHom.comp (algebraMap Γ(S, U) (FractionRing Γ(S, U)))
  let j₂ : Γ(S, U) →+* FractionRing Γ(S, U) ⊗[R] FractionRing Γ(S, U) :=
    (Algebra.TensorProduct.includeRight : FractionRing Γ(S, U) →ₐ[R] _).toRingHom.comp
      (algebraMap Γ(S, U) (FractionRing Γ(S, U)))
  have hw : π.appLE ⊤ U le_top ≫ (CommRingCat.ofHom j₁ : Γ(S, U) ⟶ CommRingCat.of _) =
      π.appLE ⊤ U le_top ≫ (CommRingCat.ofHom j₂ : Γ(S, U) ⟶ CommRingCat.of _) := by
    ext t
    change j₁ ((π.appLE ⊤ U le_top).hom t) = j₂ ((π.appLE ⊤ U le_top).hom t)
    rw [hρ]
    show algebraMap Γ(S, U) (FractionRing Γ(S, U)) (algebraMap R Γ(S, U) _) ⊗ₜ[R] (1 : FractionRing Γ(S, U)) =
      (1 : FractionRing Γ(S, U)) ⊗ₜ[R] algebraMap Γ(S, U) (FractionRing Γ(S, U)) (algebraMap R Γ(S, U) _)
    rw [← IsScalarTower.algebraMap_apply, Algebra.algebraMap_eq_smul_one, TensorProduct.smul_tmul]
  have hd1 := congr(($(po.inl_desc _ _ hw)).hom (res.hom x))
  have hd2 := congr(($(po.inr_desc _ _ hw)).hom (res.hom x))
  have e1 : ∀ (f : pullback π π ⟶ S) (h : pullback.fst π π ⁻¹ᵁ U ⊓ pullback.snd π π ⁻¹ᵁ U ≤ f ⁻¹ᵁ U),
      (f.appLE U _ h).hom (res.hom x) =
        ((pullback π π).presheaf.map (homOfLE (le_top : pullback.fst π π ⁻¹ᵁ U ⊓ pullback.snd π π ⁻¹ᵁ U ≤ ⊤)).op).hom
          (f.appTop.hom x) := by
    intro f h
    rw [← CommRingCat.comp_apply, ← CommRingCat.comp_apply, Scheme.Hom.map_appLE]
    rfl
  have hj : j₁ (res.hom x) = j₂ (res.hom x) := by
    refine hd1.symm.trans (Eq.trans ?_ hd2)
    rw [CommRingCat.comp_apply, CommRingCat.comp_apply, e1, e1, hx]
  obtain ⟨r, hr⟩ := mem_range_of_tmul_eq_tmul hρinj _ hxint hj
  refine ⟨(Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom r, hres ?_⟩
  rw [← happ]
  exact hr

end GlobalTheory.Mum
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemSecOfMemCuspWWtZ
section
set_option autoImplicit false
set_option synthInstance.maxHeartbeats 400000

noncomputable section

open GlobalTheory.IndefiniteRowSideFullHecke.DifferentConjugateDefects NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.FlatTw GlobalTheory.SlopeRec GlobalTheory.CovTop GlobalTheory.BigTop GlobalTheory.RefSum

namespace GlobalTheory.RefSum

theorem mem_sec_of_mem_cuspW_wtZ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E}
    {Dw : Datum H} {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {r : ℕ} {U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r}
    {a : (E →+* ℂ) × ℕ → ℕ} {n : ℕ} {f : Rul Xo c} (hf : f ∈ cuspW Xo c U (wtZ a n)) : f ∈ sec Xo c a n := by
  rw [cuspW_wtZ] at hf
  exact cusp_le_sec Xo c U a n hf

theorem refExp_vp_cover_le : ∀ (D : D7) (T : CoreJ D) (j : ℕ) (Y : Deep T.toCore j) (e : ℕ) (o : ℝ), LawsJ T → InR D j → Y.Good e o → ∀ (a : (D.host.E →+* ℂ) × ℕ → ℕ) (n : ℕ), Dom a n → ∀ (cst : ℝ) (q : ℕ), q.Prime → refExp_vp Y.U cst (wtZ a n) q ≤ refExp_vp (T.U j) cst (wtZ a n) q := by
  intro D T j Y e o hJ hj hG a n hD cst q hq
  have hpq : 1 ≤ (T.Q.Dw j).p + (T.Q.Dw j).q := by
    obtain ⟨hp, hq', -⟩ := hJ.pins.2.2.2 j hj
    obtain ⟨h1, h2⟩ := hj
    have h3 := D.R.m_add_three_le_k
    rw [hp, hq']
    simp only [Ranks.sigW]
    omega
  have hne : (T.Q.Dw j).p ≠ (T.Q.Dw j).q := by
    obtain ⟨hp, hq', -⟩ := hJ.pins.2.2.2 j hj
    obtain ⟨h1, h2⟩ := hj
    have hk := D.R.m_add_three_le_k
    rw [hp, hq']
    simp only [Ranks.sigW]
    omega
  rw [refExp_vp_le_iff]
  intro la₂ S io₂ e₂ ho₂ y₂ ha₂ φ hφ
  obtain ⟨y', ha', hφ', hv'⟩ := GlobalTheory.CoverDown.exists_intFr_below _ _ _ _ (T.Q.Xo j) Y.c' Y.d hpq hG.lev.1
    (Or.inl ⟨hne, hJ.pins.2.1.2⟩) S io₂ y₂ ha₂
  obtain ⟨y, ha, hφy, hv⟩ := _root_.GlobalTheory.RefSum.intFr_res_down _ _ _ _ (T.Q.Xo j) T.Q.c Y.c' Y.hle S _ y' ha'
  obtain ⟨la', e', hq', ho'⟩ := GlobalTheory.PlaceBelow.exists_overLa_under Y.c'.F Y.d.c₂.F (Y.d.eF : Y.c'.F →+* Y.d.c₂.F) q la₂.1 hq la₂.2 S io₂ e₂ ho₂
  obtain ⟨la, e₀, hq₀, ho⟩ := GlobalTheory.PlaceBelow.exists_overLa_under T.Q.c.F Y.c'.F (IntermediateField.inclusion Y.hle).toRingHom q la' hq hq' S _ e' ho'
  refine le_trans ?_ (refExp_vp_le_iff (T.U j) |>.1 le_rfl ⟨la, hq₀⟩ S _ e₀ ho y ha φ (hφy φ (hφ' φ hφ)))
  refine le_iInf₂ fun f hf => ?_
  obtain ⟨g, ⟨hg, hP⟩, -⟩ := _root_.GlobalTheory.CoverPull.cusp_pullback_existsUnique D T j Y e o hJ hj hG hG.unit hG.modelW a n hD f.1 f.2
  have hgl := (_root_.GlobalTheory.CovTop.PullLat.pull_mem_latW D T j Y e o hJ hj hG a n f ⟨g, hg⟩ hP).2 hf
  have hfs : f.1 ∈ sec (T.Q.Xo j) T.Q.c a n := mem_sec_of_mem_cuspW_wtZ f.2
  have hP' := ((GlobalTheory.DeepLaws.laws_galois_pull D T j Y e o hJ hj hG hG.unit hG.modelW).2.2 a n f.1 hfs g).1 hP
  have hbc := ((GlobalTheory.FieldBC.rulBC_sec_val_linear _ _ _ _ (T.Q.Xo j) T.Q.c Y.c' Y.hle).1 a n f.1 hfs).1
  have hval : evI y₂ g = evI y f.1 :=
    (hv' a n _ hbc g (mem_sec_of_mem_cuspW_wtZ hg) hP').trans (hv a n f.1 hfs)
  refine (iInf₂_le (⟨g, hg⟩ : Y.V (wtZ a n)) hgl).trans (le_of_eq ?_)
  exact congrArg _ hval

end GlobalTheory.RefSum

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemSpanSupPowOfForallCompleteDvrLocalTest
section
open AlgebraicGeometry CategoryTheory IsLocalRing ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.TorRef GlobalTheory.Poinc

namespace GlobalTheory.Poinc

theorem dvd_of_forall_mem_span_sup_pow {V : Type} [CommRing V] [IsDomain V] [IsDiscreteValuationRing V]
    {x y : V} (hx : x ≠ 0) (h : ∀ e, y ∈ Ideal.span {x} ⊔ maximalIdeal V ^ e) : x ∣ y := by
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible V
  obtain ⟨k, hk⟩ := IsDiscreteValuationRing.associated_pow_irreducible hx hϖ
  have hs : Ideal.span {x} = maximalIdeal V ^ k := by
    rw [hϖ.maximalIdeal_eq, Ideal.span_singleton_pow]
    exact Ideal.span_singleton_eq_span_singleton.mpr hk
  have := h k
  rw [← hs, sup_idem] at this
  exact Ideal.mem_span_singleton.mp this

theorem mem_span_sup_pow_of_forall_complete_dvr : ∀ (O : Type) [CommRing O] [IsDomain O] [IsLocalRing O] [IsIntegrallyClosed O] [CharZero O] [Algebra.EssFiniteType ℤ O] (g : O) (b : ℕ → O), g ≠ 0 → (∀ m n, m ≤ n → b m - b n ∈ maximalIdeal O ^ m) → (∀ (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [CharZero V], IsAdicComplete (maximalIdeal V) V → ∀ ρ : O →+* V, Function.Injective ρ → IsLocalHom ρ → ∀ e, ρ (b e) ∈ Ideal.span {ρ g} ⊔ maximalIdeal V ^ e) → ∀ n, b n ∈ Ideal.span {g} ⊔ maximalIdeal O ^ n := by
  intro O _ _ _ _ _ _ g b hg hb hV n
  haveI : IsNoetherianRing O := Algebra.EssFiniteType.isNoetherianRing ℤ O
  set m := maximalIdeal O with hm
  let R := AdicCompletion m O
  let ι : O →+* R := algebraMap O R
  haveI : IsNoetherianRing R := GlobalTheory.AdicNoeth.isNoetherianRing_adicCompletion O m
  obtain ⟨hdom, hic⟩ := GlobalTheory.AnalyticNormality.completion_isDomain_and_isIntegrallyClosed O
  have fg : m.FG := m.fg_of_isNoetherianRing
  haveI : Module.Flat O R := AdicCompletion.flat_of_isNoetherian m
  haveI : IsLocalHom (algebraMap O R) := AdicCompletion.algebraMap_isLocalHom_of_fg fg
  haveI : Module.FaithfullyFlat O R := Module.FaithfullyFlat.of_flat_of_isLocalHom
  have hinj : Function.Injective ι := FaithfulSMul.algebraMap_injective O R
  haveI : CharZero R := charZero_of_injective_ringHom hinj
  have hmR : maximalIdeal R = m.map ι := AdicCompletion.maximalIdeal_eq_map

  have hc : IsAdicComplete (m.map ι) R := AdicCompletion.isAdicComplete_self m fg
  obtain ⟨F, hF⟩ := IsPrecomplete.prec hc.toIsPrecomplete (f := fun k => ι (b k)) (by
    intro k l hkl
    rw [SModEq.sub_mem, smul_eq_mul, Ideal.mul_top, ← map_sub, ← Ideal.map_pow]
    exact Ideal.mem_map_of_mem _ (hb k l hkl))
  have hF' : ∀ k, ι (b k) - F ∈ maximalIdeal R ^ k := by
    intro k
    have := hF k
    rwa [SModEq.sub_mem, smul_eq_mul, Ideal.mul_top, ← hmR] at this

  have hgR : ι g ≠ 0 := fun h => hg (hinj (by rw [h, map_zero]))
  have hdvd : ι g ∣ F := by
    refine _root_.GlobalTheory.Poinc.dvd_of_forall_complete_dvr R F (ι g) hgR ?_
    intro V _ _ _ hVc ρ' hρ' _
    let ρ : O →+* V := ρ'.comp ι
    have hρ : Function.Injective ρ := hρ'.comp hinj
    haveI : IsLocalHom ρ := inferInstance
    haveI : CharZero V := charZero_of_injective_ringHom hρ
    have hgV : ρ' (ι g) ≠ 0 := fun h => hgR (hρ' (by rw [h, map_zero]))
    refine dvd_of_forall_mem_span_sup_pow hgV fun e => ?_
    have h1 : ρ (b e) ∈ Ideal.span {ρ g} ⊔ maximalIdeal V ^ e := hV V hVc ρ hρ inferInstance e
    have hmap : ∀ x ∈ maximalIdeal R, ρ' x ∈ maximalIdeal V := by
      intro x hx
      rw [mem_maximalIdeal, mem_nonunits_iff] at hx ⊢
      exact fun h => hx (isUnit_of_map_unit ρ' x h)
    have h2 : ρ' (ι (b e) - F) ∈ maximalIdeal V ^ e := by
      have hle : (maximalIdeal R ^ e).map ρ' ≤ maximalIdeal V ^ e := by
        rw [Ideal.map_pow]
        exact Ideal.pow_right_mono (Ideal.map_le_iff_le_comap.mpr hmap) e
      exact hle (Ideal.mem_map_of_mem _ (hF' e))
    have : ρ' F = ρ (b e) - ρ' (ι (b e) - F) := by
      simp [ρ, map_sub]
    rw [this]
    exact Ideal.sub_mem _ h1 (Ideal.mem_sup_right h2)

  have hmem : ι (b n) ∈ (Ideal.span {g} ⊔ m ^ n).map ι := by
    rw [Ideal.map_sup, Ideal.map_span, Set.image_singleton, Ideal.map_pow, ← hmR]
    have h3 : F ∈ Ideal.span {ι g} := Ideal.mem_span_singleton.mpr hdvd
    have : ι (b n) = F + (ι (b n) - F) := by ring
    rw [this]
    exact Ideal.add_mem _ (Ideal.mem_sup_left h3) (Ideal.mem_sup_right (hF' n))
  rwa [← Ideal.mem_comap, Ideal.comap_map_eq_self_of_faithfullyFlat] at hmem

end GlobalTheory.Poinc
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ModelLocalRingResidueFieldFiniteOfClosedPoint
section
open AlgebraicGeometry CategoryTheory Limits IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.ZH GlobalTheory.Poinc

namespace GlobalTheory.ResFin

theorem finite_residueField_O : ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] [ArithBase o Ω] (M : RatModel o Ω)
    (x : M.Z), IsClosed ({x} : Set M.Z) → Finite (ResidueField (M.O x)) := by
  intro o Ω _ _ _ hA M x hx
  haveI : Algebra.FiniteType ℤ o := hA.ft
  haveI : LocallyOfFiniteType (spMap (algebraMap ℤ o)) :=
    (HasRingHomProperty.Spec_iff (P := @LocallyOfFiniteType)).2 (RingHom.finiteType_algebraMap.2 inferInstance)
  haveI : LocallyOfFiniteType M.s := M.lft
  have h := finite_residueField_of_isClosed_of_locallyOfFiniteType_int (M.s ≫ spMap (algebraMap ℤ o)) x hx
  haveI : Finite (ResidueField (M.Z.presheaf.stalk x)) := h
  exact Finite.of_equiv _ (ResidueField.mapEquiv (M.stalkEquiv x)).toEquiv

end GlobalTheory.ResFin
end

