module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2950
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2962
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.MemPadicAlgClValuationSubringIffNormLeOne
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0192
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0044
public import Mathlib
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.DenseInterior
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2412
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TranslateUnique
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0100
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2948
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0543
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2496
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2956
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2963
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ValCalc
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2946
public import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2877
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2911
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0018
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsMonHomOfMul
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.BCTools
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.KernelKilledOverOpenOfLocal
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2938

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUnitaryTraitOfClassicalPoint
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.Models GlobalTheory.LN GlobalTheory.ShFam GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZH GlobalTheory.Poinc
open scoped CategoryTheory.Obj
open GlobalTheory.UPoinc
open GlobalTheory
open Classical

namespace GlobalTheory.UTraitPt

theorem spMap_comp_eq {A B D : Type} [CommRing A] [CommRing B] [CommRing D] (f : A →+* B) (g : B →+* D) :
    spMap (g.comp f) = spMap g ≫ spMap f := by
  simp only [spMap, ← Spec.map_comp]; rfl

theorem exists_embed_padicAlgCl (p : ℕ) [Fact p.Prime] (K : IntermediateField ℚ_[p] (PadicAlgCl p))
    [FiniteDimensional ℚ_[p] K] (W : Type) [CommRing W] [IsDomain W] [IsDiscreteValuationRing W]
    (f : integralClosure ℤ_[p] K →+* W) (fK : FractionRing (integralClosure ℤ_[p] K) →+* FractionRing W)
    (hfin : f.Finite) (hfK : ∀ a, fK (algebraMap _ _ a) = algebraMap W (FractionRing W) (f a)) :
    ∃ (ι : FractionRing W →+* PadicAlgCl p) (j : W →+* OO p),
      (∀ x, ‖ι x‖ ≤ 1 ↔ x ∈ Set.range (algebraMap W (FractionRing W))) ∧
      (∀ v, (j v : PadicAlgCl p) = ι (algebraMap W (FractionRing W) v)) ∧ IsLocalHom j ∧
      ∀ a, (j (f a) : PadicAlgCl p) = ((a : K) : PadicAlgCl p) := by
  let V₀ := integralClosure ℤ_[p] K
  letI : Algebra V₀ W := f.toAlgebra
  haveI : Module.Finite V₀ W := hfin
  haveI : IsFractionRing V₀ K := integralClosure.isFractionRing_of_finite_extension ℚ_[p] K
  let eK : K ≃ₐ[V₀] FractionRing V₀ := IsLocalization.algEquiv (nonZeroDivisors V₀) K (FractionRing V₀)
  letI : Algebra K (FractionRing W) := (fK.comp eK.toRingHom).toAlgebra
  have e : (algebraMap W (FractionRing W)).comp (algebraMap V₀ W) =
      (algebraMap K (FractionRing W)).comp (algebraMap V₀ K) := by
    refine RingHom.ext fun a => ?_
    show algebraMap W (FractionRing W) (f a) = fK (eK (algebraMap V₀ K a))
    rw [AlgEquiv.commutes, hfK]
  obtain ⟨K', hKK', hK', τ, f', hτK, hτW⟩ :=
    GlobalTheory.SS.exists_ringHom_integralClosure p K W (FractionRing W) e
  let ι : FractionRing W →+* PadicAlgCl p := K'.val.toRingHom.comp τ
  let j : W →+* OO p := (integralClosureToPadicAlgClIntegers K').comp f'
  have hj : ∀ v, (j v : PadicAlgCl p) = ι (algebraMap W (FractionRing W) v) := fun v => by
    dsimp [j, ι, integralClosureToPadicAlgClIntegers, RingHom.comp_apply]
    rw [← RingHom.comp_apply τ, hτW]; rfl
  have hball : ∀ x, ‖ι x‖ ≤ 1 ↔ x ∈ Set.range (algebraMap W (FractionRing W)) := by
    intro x
    constructor
    · intro hx
      have hint : IsIntegral ℤ_[p] (τ x) := (mem_integralClosure_padicInt_iff K' (τ x)).2 hx
      let ρ : ℤ_[p] →+* W := f.comp (algebraMap ℤ_[p] V₀)
      letI : Algebra ℤ_[p] W := ρ.toAlgebra
      have hτc : ∀ r : ℤ_[p], τ (algebraMap ℤ_[p] (FractionRing W) r) = algebraMap ℤ_[p] K' r := by
        intro r
        have h1 : algebraMap ℤ_[p] (FractionRing W) r =
            (algebraMap K (FractionRing W)) (algebraMap V₀ K (algebraMap ℤ_[p] V₀ r)) := by
          rw [IsScalarTower.algebraMap_apply ℤ_[p] W (FractionRing W)]
          exact congrArg (fun φ : V₀ →+* FractionRing W => φ (algebraMap ℤ_[p] V₀ r)) e
        rw [h1, ← RingHom.comp_apply τ, hτK]
        rfl
      let τa : FractionRing W →ₐ[ℤ_[p]] K' := { τ with commutes' := hτc }
      have hx' : IsIntegral ℤ_[p] x := (isIntegral_algHom_iff τa τ.injective).1 hint
      have hxW : IsIntegral W x := hx'.tower_top
      obtain ⟨w, hw⟩ := IsIntegrallyClosed.isIntegral_iff.1 hxW
      exact ⟨w, hw⟩
    · rintro ⟨w, rfl⟩
      rw [← hj]
      exact (mem_padicAlgCl_valuationSubring_iff_norm_le_one _).1 (j w).2
  refine ⟨ι, j, hball, hj, ⟨fun v hv => ?_⟩, fun a => ?_⟩
  · obtain ⟨u, hu⟩ := hv.exists_right_inv
    have hu' : ι (algebraMap W (FractionRing W) v) * (u : PadicAlgCl p) = 1 := by
      rw [← hj]; exact congrArg (fun z : OO p => (z : PadicAlgCl p)) hu
    have h0 : algebraMap W (FractionRing W) v ≠ 0 := by
      intro h0; rw [h0, map_zero, zero_mul] at hu'; exact zero_ne_one hu'
    have hinv : (algebraMap W (FractionRing W) v)⁻¹ ∈ Set.range (algebraMap W (FractionRing W)) := by
      rw [← hball, map_inv₀, ← eq_inv_of_mul_eq_one_right hu']
      exact (mem_padicAlgCl_valuationSubring_iff_norm_le_one _).1 u.2
    obtain ⟨w, hw⟩ := hinv
    refine IsUnit.of_mul_eq_one (b := w) (IsFractionRing.injective W (FractionRing W) ?_)
    rw [map_mul, hw, map_one, mul_inv_cancel₀ h0]
  · rw [hj]
    have h1 : algebraMap W (FractionRing W) (f a) = algebraMap K (FractionRing W) (algebraMap V₀ K a) :=
      congrArg (fun φ : V₀ →+* FractionRing W => φ a) e
    show ((τ (algebraMap W (FractionRing W) (f a)) : K') : PadicAlgCl p) = _
    rw [h1, ← RingHom.comp_apply τ, hτK]
    rfl

end GlobalTheory.UTraitPt

namespace GlobalTheory.UTraitPt

theorem exists_lift_i {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H}
    {l : Geo.Tor.Level H} {Xo : Moduli Dw l} {c : Coeff l} (C : UCompact Xo c) (F : Type) [Field F]
    (g : Sp F ⟶ C.Z) (hg : Set.range g ⊆ Set.range C.i) : ∃ g' : Sp F ⟶ Xo.XF c, g' ≫ C.i = g := by
  letI := C.b.toAlgebra
  haveI := C.isFractionRing
  haveI := C.ded
  haveI := C.iF_open
  haveI : IsPreimmersion (spMap C.b) := IsPreimmersion.of_isLocalization (nonZeroDivisors C.o)
  haveI : IsPreimmersion (pullback.fst C.z (spMap C.b)) := inferInstance
  have hinj : Function.Injective (pullback.fst C.z (spMap C.b)) :=
    (pullback.fst C.z (spMap C.b)).isEmbedding.injective
  let pt : Sp F := ⟨⊥, Ideal.isPrime_bot⟩
  obtain ⟨x, hx⟩ := hg ⟨pt, rfl⟩
  let φ : C.o →+* F := (Spec.preimage (g ≫ C.z)).hom
  have hφ : spMap φ = g ≫ C.z := Spec.map_preimage _
  have hφi : Function.Injective φ := by
    have e : (spMap φ) pt = (spMap C.b) ((C.iF ≫ pullback.snd C.z (spMap C.b)) x) := by
      rw [hφ, Scheme.Hom.comp_apply, ← hx]
      show C.z ((C.iF ≫ pullback.fst C.z (spMap C.b)) x) = _
      rw [← Scheme.Hom.comp_apply, Category.assoc, pullback.condition, ← Category.assoc]
      rfl
    have e2 : RingHom.ker φ = ⊥ := by
      have := congrArg PrimeSpectrum.asIdeal e
      have h1 : ((spMap φ) pt).asIdeal = RingHom.ker φ := by
        show Ideal.comap φ ⊥ = _
        rfl
      rw [h1] at this
      rw [this]
      haveI := ((C.iF ≫ pullback.snd C.z (spMap C.b)) x).isPrime
      show Ideal.comap C.b _ = ⊥
      rw [Ideal.eq_bot_of_prime (((C.iF ≫ pullback.snd C.z (spMap C.b)) x).asIdeal), Ideal.comap_bot_of_injective _ C.inj]
    exact (RingHom.injective_iff_ker_eq_bot φ).2 e2
  let ψ : c.F →+* F := IsFractionRing.lift hφi
  have hψ : ψ.comp C.b = φ := RingHom.ext fun a => IsFractionRing.lift_algebraMap hφi a
  have hsq : g ≫ C.z = spMap ψ ≫ spMap C.b := by
    rw [← hφ, ← hψ]; exact spMap_comp_eq _ _
  let g₁ : Sp F ⟶ pullback C.z (spMap C.b) := pullback.lift g (spMap ψ) hsq
  have hr : Set.range g₁ ⊆ Set.range C.iF := by
    rintro _ ⟨w, rfl⟩
    have hw : w = pt := Subsingleton.elim _ _
    subst hw
    refine ⟨x, hinj ?_⟩
    rw [← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply, pullback.lift_fst]
    exact hx
  refine ⟨IsOpenImmersion.lift C.iF g₁ hr, ?_⟩
  show _ ≫ C.iF ≫ pullback.fst C.z (spMap C.b) = g
  rw [← Category.assoc, IsOpenImmersion.lift_fac, pullback.lift_fst]

end GlobalTheory.UTraitPt

namespace GlobalTheory.UTraitPt

theorem exists_uTrait_of_classicalPoint : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l) (C : UCompact Xo c) (X₁ : USetup C) (Y : RatModel X₁.o₁ X₁.Ω₁) (πY : Y.Z ⟶ X₁.M.Z) (p : ℕ) [Fact p.Prime] (y : Sp (OO p) ⟶ Y.Z), Set.range (gPt p ≫ y ≫ πY ≫ X₁.π) ⊆ Set.range C.i → ∃ (T : UTrait Xo c) (ι : FractionRing T.V →+* PadicAlgCl p) (j : T.V →+* OO p) (ξ : Sp T.V ⟶ Y.Z), (∀ x, ‖ι x‖ ≤ 1 ↔ x ∈ Set.range (algebraMap T.V (FractionRing T.V))) ∧ (∀ v, (j v : PadicAlgCl p) = ι (algebraMap T.V (FractionRing T.V) v)) ∧ IsLocalHom j ∧ spMap j ≫ ξ = y ∧ jK T.V ≫ ξ ≫ πY ≫ X₁.π = T.y ≫ C.i := by
  intro E _ _ _ H Dw l Xo c C X₁ Y πY p _ y hy
  haveI : Algebra.FiniteType ℤ X₁.o₁ := X₁.ar.ft
  haveI := Y.lft
  haveI hSpecZ : LocallyOfFiniteType (spMap (algebraMap ℤ X₁.o₁)) := by
    show LocallyOfFiniteType (Spec.map (CommRingCat.ofHom (algebraMap ℤ X₁.o₁)))
    rw [HasRingHomProperty.Spec_iff (P := @LocallyOfFiniteType)]
    exact RingHom.finiteType_algebraMap.mpr inferInstance
  obtain ⟨K, hK, hKall⟩ := padicAlgCl_integral_points.2 Y.Z (Y.s ≫ spMap (algebraMap ℤ X₁.o₁)) p y
  haveI : FiniteDimensional ℚ_[p] K := hK
  obtain ⟨j₀, y₀, hj₀, -, hy₀⟩ := hKall K le_rfl
  let V₀ := integralClosure ℤ_[p] K
  haveI hdvr : IsDiscreteValuationRing V₀ := ReciprocityTheory.ChartRestriction.G.T0.FiniteAlgebraLocalCompletion.cl_dvr ℤ_[p] ℚ_[p] K
  haveI : Module.Finite ℤ_[p] V₀ := IsIntegralClosure.finite ℤ_[p] ℚ_[p] K _
  haveI : IsAdicComplete (maximalIdeal V₀) V₀ := CompleteFiniteExtension.isAdicComplete_of_finite_local ℤ_[p] _
  haveI : CharZero V₀ := inferInstance
  have hB : GlobalTheory.Mum.Base V₀ := ⟨⟨inferInstance, inferInstance, inferInstance, inferInstance⟩, inferInstance⟩

  have hj₀i : Function.Injective ((OO p).subtype.comp j₀) := by
    intro a b h
    have h' : ((a : K) : PadicAlgCl p) = ((b : K) : PadicAlgCl p) := by
      rw [← hj₀, ← hj₀]; exact h
    exact Subtype.ext (Subtype.ext h')
  obtain ⟨e₀, he₀'⟩ : ∃ e₀ : FractionRing V₀ →+* PadicAlgCl p,
      ∀ a, e₀ (algebraMap V₀ (FractionRing V₀) a) = ((OO p).subtype.comp j₀) a :=
    ⟨IsFractionRing.lift hj₀i, fun a => IsFractionRing.lift_algebraMap hj₀i a⟩
  have he₀ : e₀.comp (algebraMap V₀ (FractionRing V₀)) = (OO p).subtype.comp j₀ := RingHom.ext he₀'
  have hgy : gPt p ≫ y = spMap e₀ ≫ jK V₀ ≫ y₀ := by
    rw [← hy₀, ← Category.assoc, ← Category.assoc]
    congr 1
    show spMap (OO p).subtype ≫ spMap j₀ = spMap e₀ ≫ spMap (algebraMap V₀ (FractionRing V₀))
    rw [← spMap_comp_eq, ← spMap_comp_eq, he₀]
  let gen₀ : Sp (FractionRing V₀) ⟶ C.Z := jK V₀ ≫ y₀ ≫ πY ≫ X₁.π
  have hgen : Set.range gen₀ ⊆ Set.range C.i := by
    rintro _ ⟨w, rfl⟩
    let q : Sp (PadicAlgCl p) := ⟨⊥, Ideal.isPrime_bot⟩
    have hw : w = (spMap e₀) q := Subsingleton.elim _ _
    apply hy
    refine ⟨q, ?_⟩
    rw [hw, ← Scheme.Hom.comp_apply]
    congr 1
    rw [← Category.assoc, hgy]
    simp only [gen₀, Category.assoc]
  obtain ⟨yK, hyK⟩ := exists_lift_i C (FractionRing V₀) gen₀ hgen
  obtain ⟨T, f, fK, -, -, hfin, hfK, hTy⟩ := GlobalTheory.UTraitExt.uTraitExtSt E H Dw l Xo c V₀ hB hdvr yK
  haveI : IsDiscreteValuationRing T.V := T.cdvr.1
  obtain ⟨ι, j, hball, hj, hloc, hjf⟩ := exists_embed_padicAlgCl p K T.V f fK hfin hfK
  refine ⟨T, ι, j, spMap f ≫ y₀, hball, hj, hloc, ?_, ?_⟩
  · have hjf' : j.comp f = j₀ := RingHom.ext fun a => Subtype.ext ((hjf a).trans (hj₀ a).symm)
    rw [← Category.assoc, ← spMap_comp_eq, hjf', hy₀]
  · have hc : jK T.V ≫ spMap f = spMap fK ≫ jK V₀ := by
      show spMap (algebraMap T.V (FractionRing T.V)) ≫ spMap f = spMap fK ≫ spMap (algebraMap V₀ (FractionRing V₀))
      rw [← spMap_comp_eq, ← spMap_comp_eq]
      congr 1
      exact RingHom.ext fun a => (hfK a).symm
    rw [hTy, Category.assoc (spMap fK), hyK]
    simp only [gen₀, ← Category.assoc]
    rw [hc]

end GlobalTheory.UTraitPt
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FibreIndependenceLogDerivativesClosedFibre
section
open AlgebraicGeometry CategoryTheory Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.LogKS Formalism.L2.Pj
open MonoidalCategory CartesianMonoidalCategory
attribute [local instance] Over.cartesianMonoidalCategory
set_option autoImplicit false
noncomputable section

namespace GlobalTheory.FibreIndep
open MonObj


set_option maxHeartbeats 2000000 in
theorem fibre_indep' : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (X : Scheme.{0}) (t : SAB H X), IsProper t.G.hom → Out.RelAmple t.G t.PP.L → Out.KTriv t.G t.PP.L → ∀ (U : X.affineOpens) (n : ℕ) (v : Fin n → (Sp (DualNumber Γ(X, U.1)) ⟶ t.G.left)), (∀ a, IsTanAtG t (chart U) (v a)) → (∀ w, IsTanAtG t (chart U) w → ∃! cf : Fin n → Γ(X, U.1), IsCombAtG t (chart U) v cf w) → ∀ (δ : Fin n → ∀ O : t.G.left.Opens, Γ(t.G.left, O) → Γ(t.G.left, O)), (∀ a, IsField (t.G.hom ⁻¹ᵁ U.1) (δ a)) → (∀ a (O : t.G.left.Opens) (h : O ≤ t.G.hom ⁻¹ᵁ U.1) (r : Γ(X, U.1)), δ a O ((t.G.hom.appLE U.1 O h).hom r) = 0) → (∀ a (O : t.G.left.Opens), O ≤ t.G.hom ⁻¹ᵁ U.1 → ∀ (f : Γ(t.G.left, O)) (S : Type) [CommRing S] (φ : Γ(X, U.1) →+* S) (g₀ : Sp S ⟶ t.G.left) (w : Sp (DualNumber S) ⟶ t.G.left), g₀ ≫ t.G.hom = spMap φ ≫ chart U → ⊤ ≤ g₀ ⁻¹ᵁ O → IsTranslate t φ g₀ (v a) w → valR g₀ O (δ a O f) = (valR w O f).snd) → ∀ (J : Type) (W : J → t.G.left.Opens) (j : J → t.PP.L.ι), (∀ i, IsAffineOpen (W i)) → ⨆ i, W i = t.G.hom ⁻¹ᵁ U.1 → ∀ (hWU : ∀ i, W i ≤ t.G.hom ⁻¹ᵁ U.1) (hj : ∀ i, W i ≤ t.PP.L.U (j i)) (m : Ideal Γ(X, U.1)), m.IsMaximal → ∀ (A : Over (Sp (Γ(X, U.1) ⧸ m))) [GrpObj A] (ιA : A.left ⟶ t.G.left), IsGrpPullback A t.G (spMap (Ideal.Quotient.mk m) ≫ chart U) ιA → ∀ (r : Fin n → Γ(X, U.1)) (h' : ∀ i, Γ(A.left, ιA ⁻¹ᵁ W i)), (∀ i i', (ιA.appLE (W i ⊓ W i') (ιA ⁻¹ᵁ W i ⊓ ιA ⁻¹ᵁ W i') (fun _ hx => hx)).hom (∑ b, (t.G.hom.appLE U.1 (W i ⊓ W i') (inf_le_left.trans (hWU i))).hom (r b) * (δ b (W i ⊓ W i') (resG t.G.left (inf_le_inf (hj i) (hj i')) (t.PP.L.g (j i) (j i')).val) * resG t.G.left (inf_le_inf (hj i) (hj i')) (t.PP.L.g (j i) (j i'))⁻¹.val)) = resG A.left inf_le_left (h' i) - resG A.left inf_le_right (h' i')) → ∀ b, r b ∈ m := by
  intro E _ _ _ H X t _hprop _hamp hK U n v hv hb δ hδ hδ0 hδt J W j hWa hWcov hWU hj m hm A _ ιA hι r h' hcob
  haveI := hm
  letI : Field (Γ(X, U.1) ⧸ m) := Ideal.Quotient.field m
  set q := Ideal.Quotient.mk m with hq
  set x0 : Sp (Γ(X, U.1) ⧸ m) ⟶ X := spMap q ≫ chart U with hx0
  have hB := GlobalTheory.LineNorm.isTanBasis_of_basis E H X t Γ(X, U.1) (chart U) n v hv hb
  have hT : ∀ b, IsTanAtG t x0 (spMap (dualMap q) ≫ v b) := fun b => GlobalTheory.VertSpanZero.isTanAtG_bc t q (hv b)
  let uR : Fin n → (tEpsG (chart U) ⟶ t.G) := fun b => Over.homMk (spMap (epsMul (r b)) ≫ v b) (by
    change (spMap (epsMul (r b)) ≫ v b) ≫ t.G.hom = spMap (algebraMap _ (DualNumber _)) ≫ chart U
    rw [Category.assoc, (hv b).1, ← Category.assoc, ← Spec.map_comp, ← CommRingCat.ofHom_comp,
      GlobalTheory.VertSpanZero.epsMul_comp_algebraMap])
  obtain ⟨xR, hxRdef⟩ : ∃ xR : tEpsG (chart U) ⟶ t.G, xR = (List.ofFn uR).prod := ⟨_, rfl⟩
  have hxR : IsCombAtG t (chart U) v r xR.left := ⟨uR, fun b => rfl, by rw [hxRdef]⟩
  have eq0 : (dualMap q).comp (algebraMap Γ(X, U.1) (DualNumber Γ(X, U.1))) =
      (algebraMap (Γ(X, U.1) ⧸ m) (DualNumber (Γ(X, U.1) ⧸ m))).comp q := by
    ext a <;> simp [dualMap, TrivSqZeroExt.algebraMap_eq_inl]
  let jq : tEpsG x0 ⟶ tEpsG (chart U) := Over.homMk (spMap (dualMap q)) (by
    change spMap (dualMap q) ≫ spMap (algebraMap _ (DualNumber _)) ≫ chart U = spMap (algebraMap _ (DualNumber _)) ≫ spMap q ≫ chart U
    rw [← Category.assoc, ← Category.assoc, ← Spec.map_comp, ← Spec.map_comp, ← CommRingCat.ofHom_comp,
      ← CommRingCat.ofHom_comp, eq0])
  obtain ⟨P, hPdef⟩ : ∃ P : tEpsG x0 ⟶ t.G, P = jq ≫ xR := ⟨_, rfl⟩
  have hPl : P.left = spMap (dualMap q) ≫ xR.left := by rw [hPdef]; rfl
  have hP : IsCombAtG t x0 (fun b => spMap (dualMap q) ≫ v b) (fun b => q (r b)) P.left := by
    refine ⟨fun b => jq ≫ uR b, fun b => ?_, ?_⟩
    · change spMap (dualMap q) ≫ spMap (epsMul (r b)) ≫ v b = spMap (epsMul (q (r b))) ≫ spMap (dualMap q) ≫ v b
      have e1 : (dualMap q).comp (epsMul (r b)) = (epsMul (q (r b))).comp (dualMap q) := by
        apply RingHom.ext; intro z; ext
        · simp [epsMul, dualMap]
        · simp [epsMul, dualMap, mul_comm]
      rw [← Category.assoc, ← Category.assoc, ← Spec.map_comp, ← Spec.map_comp, ← CommRingCat.ofHom_comp,
        ← CommRingCat.ofHom_comp]
      exact congrArg (fun g => Spec.map (CommRingCat.ofHom g) ≫ v b) e1
    · rw [← GlobalTheory.FirstOrderValue.comp_prod_ofFn, ← hxRdef, hPdef]
  have hPt : spMap (TrivSqZeroExt.fstHom (Γ(X, U.1) ⧸ m) (Γ(X, U.1) ⧸ m) (Γ(X, U.1) ⧸ m)).toRingHom ≫ P.left = (1 : Over.mk x0 ⟶ t.G).left := by
    obtain ⟨u', hu', hu'P⟩ := hP
    let s : Over.mk x0 ⟶ tEpsG x0 := Over.homMk (spMap (TrivSqZeroExt.fstHom (Γ(X, U.1) ⧸ m) (Γ(X, U.1) ⧸ m) (Γ(X, U.1) ⧸ m)).toRingHom) (by
      change _ ≫ spMap (algebraMap _ _) ≫ x0 = x0
      rw [← Category.assoc, GlobalTheory.VertSpanZero.spMap_fst_algebraMap, Category.id_comp])
    have hs : ∀ b, s ≫ u' b = 1 := fun b => Over.OverMorphism.ext (by
      change spMap _ ≫ (u' b).left = _
      rw [hu' b, ← Category.assoc, ← Spec.map_comp, ← CommRingCat.ofHom_comp, GlobalTheory.VertSpanZero.fst_comp_epsMul]
      exact (hT b).2)
    have h1 : s ≫ (List.ofFn u').prod = 1 := by
      rw [GlobalTheory.FirstOrderValue.comp_prod_ofFn]; simp [hs]
    have h2 : (s ≫ (List.ofFn u').prod).left = (1 : Over.mk x0 ⟶ t.G).left := by rw [h1]
    rw [Over.comp_left, hu'P] at h2
    exact h2

  have hgen : ∃ c : LB.Gen (Out.translDiff t.G t.PP.L P), c.IsGen := by
    let T := tEpsG x0
    let π : (T ⊗ t.G).left ⟶ Sp (DualNumber (Γ(X, U.1) ⧸ m)) := (fst T t.G).left
    let τ : (T ⊗ t.G).left ⟶ t.G.left := (lift (fst T t.G ≫ P) (snd T t.G) ≫ μ[t.G]).left
    let ρ : (T ⊗ t.G).left ⟶ t.G.left := (snd T t.G).left
    have wπ : π ≫ spMap (algebraMap _ (DualNumber (Γ(X, U.1) ⧸ m))) ≫ x0 = (T ⊗ t.G).hom := Over.w (fst T t.G)
    have wρ : ρ ≫ t.G.hom = (π ≫ spMap (algebraMap _ (DualNumber (Γ(X, U.1) ⧸ m)))) ≫ (spMap q ≫ chart U) := by
      rw [Category.assoc, wπ]; exact Over.w (snd T t.G)
    have wτ : τ ≫ t.G.hom = (π ≫ spMap (algebraMap _ (DualNumber (Γ(X, U.1) ⧸ m)))) ≫ (spMap q ≫ chart U) := by
      rw [Category.assoc, wπ]; exact Over.w (lift (fst T t.G ≫ P) (snd T t.G) ≫ μ[t.G])
    obtain ⟨ρ', hρ', hρs⟩ : ∃ ρ' : (T ⊗ t.G).left ⟶ A.left, ρ' ≫ ιA = ρ ∧
        ρ' ≫ A.hom = π ≫ spMap (algebraMap _ (DualNumber (Γ(X, U.1) ⧸ m))) :=
      ⟨hι.1.lift ρ _ wρ, hι.1.lift_fst _ _ _, hι.1.lift_snd _ _ _⟩
    obtain ⟨τ', hτ', hτs⟩ : ∃ τ' : (T ⊗ t.G).left ⟶ A.left, τ' ≫ ιA = τ ∧
        τ' ≫ A.hom = π ≫ spMap (algebraMap _ (DualNumber (Γ(X, U.1) ⧸ m))) :=
      ⟨hι.1.lift τ _ wτ, hι.1.lift_fst _ _ _, hι.1.lift_snd _ _ _⟩
    have hpts : ∀ y, τ'.base y = ρ'.base y := by
      intro y
      obtain ⟨K, _, z, ⟨p, rfl⟩, hz⟩ := _root_.GlobalTheory.InfTranslPts.transl_points E H X t _ x0 P hPt y
      have hzz : z ≫ τ' = z ≫ ρ' := hι.1.hom_ext (by rw [Category.assoc, Category.assoc, hτ', hρ']; exact hz)
        (by rw [Category.assoc, Category.assoc, hτs, hρs])
      rw [← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply, hzz]
    have hιU : ∀ z, ιA.base z ∈ t.G.hom ⁻¹ᵁ U.1 := fun z => by
      show (ιA ≫ t.G.hom).base z ∈ U.1
      rw [hι.1.w, hx0, ← Category.assoc, Scheme.Hom.comp_apply]
      have h : (chart U).base ((A.hom ≫ spMap q).base z) ∈ Set.range (chart U).base := ⟨_, rfl⟩
      rwa [chart, U.2.range_fromSpec] at h
    have e : (fun n : Fin 2 => ![τ', ρ'] n ≫ ιA) = ![τ, ρ] := by
      funext n; fin_cases n
      · exact hτ'
      · exact hρ'
    have key := GlobalTheory.KS.DlogPol.exists_gen (K := Γ(X, U.1) ⧸ m) π τ' ρ' (fun y W hy => by rwa [← hpts y]) ιA t.PP.L
      t.PP.isLB (fun a b => GlobalTheory.KS.pbT ιA (∑ c, (t.G.hom.appLE U.1 ((t.PP.L.U a ⊓ t.G.hom ⁻¹ᵁ U.1) ⊓ (t.PP.L.U b ⊓ t.G.hom ⁻¹ᵁ U.1)) (inf_le_left.trans inf_le_right)).hom (r c) * (δ c ((t.PP.L.U a ⊓ t.G.hom ⁻¹ᵁ U.1) ⊓ (t.PP.L.U b ⊓ t.G.hom ⁻¹ᵁ U.1)) (resG t.G.left (inf_le_inf inf_le_left inf_le_left) (t.PP.L.g a b).val) * resG t.G.left (inf_le_inf inf_le_left inf_le_left) (t.PP.L.g a b)⁻¹.val)) (ιA ⁻¹ᵁ t.PP.L.U a ⊓ ιA ⁻¹ᵁ t.PP.L.U b)) ?_ (_root_.GlobalTheory.ChartCob.chart_isCob E H X t U n δ hδ J W j hWa hWcov hWU hj m A ιA hι r h' hcob)
    · rw [e] at key
      exact key
    intro a b y ha hb
    beta_reduce
    have hτy : τ.base y = ρ.base y := by
      rw [← hτ', ← hρ', Scheme.Hom.comp_apply, Scheme.Hom.comp_apply, hpts]
    have hρU : ρ.base y ∈ t.G.hom ⁻¹ᵁ U.1 := by rw [← hρ', Scheme.Hom.comp_apply]; exact hιU _
    have ha' : ρ.base y ∈ t.PP.L.U a := by rw [← hτy, ← hτ', Scheme.Hom.comp_apply]; exact ha
    have hb' : ρ.base y ∈ t.PP.L.U b := by rw [← hτy, ← hτ', Scheme.Hom.comp_apply]; exact hb
    have hyO : ρ.base y ∈ (t.PP.L.U a ⊓ t.G.hom ⁻¹ᵁ U.1) ⊓ (t.PP.L.U b ⊓ t.G.hom ⁻¹ᵁ U.1) := ⟨⟨ha', hρU⟩, ⟨hb', hρU⟩⟩
    have hOab : (t.PP.L.U a ⊓ t.G.hom ⁻¹ᵁ U.1) ⊓ (t.PP.L.U b ⊓ t.G.hom ⁻¹ᵁ U.1) ≤ t.PP.L.U a ⊓ t.PP.L.U b :=
      inf_le_inf inf_le_left inf_le_left
    have hOU : (t.PP.L.U a ⊓ t.G.hom ⁻¹ᵁ U.1) ⊓ (t.PP.L.U b ⊓ t.G.hom ⁻¹ᵁ U.1) ≤ t.G.hom ⁻¹ᵁ U.1 :=
      inf_le_left.trans inf_le_right
    have hρ'y : ρ'.base y ∈ ιA ⁻¹ᵁ t.PP.L.U a ⊓ ιA ⁻¹ᵁ t.PP.L.U b := by
      rw [← hpts y]; exact ⟨ha, hb⟩
    have e2a := _root_.GlobalTheory.TranslGerm.transl_germ E H X t U n v hv δ hδ hδ0 hδt r xR hxR (Γ(X, U.1) ⧸ m) q P hPl
    have e2 := e2a _ hOU (resG t.G.left hOab (t.PP.L.g a b).val) y hyO
    rw [GlobalTheory.KS.DlogPol.gs_pbT ρ' ιA y (O₀ := (t.PP.L.U a ⊓ t.G.hom ⁻¹ᵁ U.1) ⊓ (t.PP.L.U b ⊓ t.G.hom ⁻¹ᵁ U.1)) (O := ιA ⁻¹ᵁ t.PP.L.U a ⊓ ιA ⁻¹ᵁ t.PP.L.U b) (fun z hz => ⟨⟨hz.1, hιU z⟩, ⟨hz.2, hιU z⟩⟩) hρ'y, hτ', hρ',
      ← gs_res τ y hOab (hτy ▸ hyO), ← gs_res ρ y hOab hyO]
    rw [e2]
    have hκ : (∑ c, (t.G.hom.appLE U.1 _ hOU).hom (r c) * (δ c _ (resG t.G.left hOab (t.PP.L.g a b).val) *
        resG t.G.left hOab (t.PP.L.g a b)⁻¹.val)) = (∑ c, (t.G.hom.appLE U.1 _ hOU).hom (r c) *
        δ c _ (resG t.G.left hOab (t.PP.L.g a b).val)) * resG t.G.left hOab (t.PP.L.g a b)⁻¹.val := by
      rw [Finset.sum_mul]; exact Finset.sum_congr rfl fun c _ => by ring
    have hFF : resG t.G.left hOab (t.PP.L.g a b).val * resG t.G.left hOab (t.PP.L.g a b)⁻¹.val = 1 := by
      rw [← map_mul, Units.mul_inv, map_one]
    have hFF' := congrArg (gs ρ y _) hFF
    rw [gs_mul ρ y _ hyO, GlobalTheory.KS.DlogPol.gs_one ρ y _ hyO] at hFF'
    rw [hκ, gs_mul ρ y _ hyO]
    linear_combination (-(gs π y ⊤ ((Scheme.ΓSpecIso (CommRingCat.of (DualNumber (Γ(X, U.1) ⧸ m)))).inv.hom DualNumber.eps) *
      gs ρ y _ (∑ c, (t.G.hom.appLE U.1 _ hOU).hom (r c) * δ c _ (resG t.G.left hOab (t.PP.L.g a b).val)))) * hFF'
  have hP1 : P = toUnit _ ≫ η[t.G] := hK (DualNumber (Γ(X, U.1) ⧸ m)) _ P fun p => by
    obtain ⟨c, hc⟩ := hgen
    exact ⟨⊤, trivial, gen_chartPull (GlobalTheory.chartPullPull (Out.translDiff t.G t.PP.L P) _) c hc⟩
  have hP1' : P.left = (1 : tEpsG x0 ⟶ t.G).left := by rw [hP1, Hom.one_def]
  have h0 := GlobalTheory.VertSpanZero.isCombAtG_zero t x0 _ hT
  have huniq := (hB.2 (Γ(X, U.1) ⧸ m) q _ (GlobalTheory.VertSpanZero.isTanAtG_one t x0)).unique (hP1' ▸ hP) h0
  intro b
  have := congrFun huniq b
  exact Ideal.Quotient.eq_zero_iff_mem.1 this

end GlobalTheory.FibreIndep

theorem GlobalTheory.FibreIndep.fibre_indep : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (X : Scheme.{0}) (t : SAB H X), IsProper t.G.hom → Out.RelAmple t.G t.PP.L → Out.KTriv t.G t.PP.L → ∀ (U : X.affineOpens) (n : ℕ) (v : Fin n → (Sp (DualNumber Γ(X, U.1)) ⟶ t.G.left)), (∀ a, IsTanAtG t (chart U) (v a)) → (∀ w, IsTanAtG t (chart U) w → ∃! cf : Fin n → Γ(X, U.1), IsCombAtG t (chart U) v cf w) → ∀ (δ : Fin n → ∀ O : t.G.left.Opens, Γ(t.G.left, O) → Γ(t.G.left, O)), (∀ a, IsField (t.G.hom ⁻¹ᵁ U.1) (δ a)) → (∀ a (O : t.G.left.Opens) (h : O ≤ t.G.hom ⁻¹ᵁ U.1) (r : Γ(X, U.1)), δ a O ((t.G.hom.appLE U.1 O h).hom r) = 0) → (∀ a (O : t.G.left.Opens), O ≤ t.G.hom ⁻¹ᵁ U.1 → ∀ (f : Γ(t.G.left, O)) (S : Type) [CommRing S] (φ : Γ(X, U.1) →+* S) (g₀ : Sp S ⟶ t.G.left) (w : Sp (DualNumber S) ⟶ t.G.left), g₀ ≫ t.G.hom = spMap φ ≫ chart U → ⊤ ≤ g₀ ⁻¹ᵁ O → IsTranslate t φ g₀ (v a) w → valR g₀ O (δ a O f) = (valR w O f).snd) → ∀ (J : Type) (W : J → t.G.left.Opens) (j : J → t.PP.L.ι), (∀ i, IsAffineOpen (W i)) → ⨆ i, W i = t.G.hom ⁻¹ᵁ U.1 → ∀ (hWU : ∀ i, W i ≤ t.G.hom ⁻¹ᵁ U.1) (hj : ∀ i, W i ≤ t.PP.L.U (j i)) (m : Ideal Γ(X, U.1)), m.IsMaximal → ∀ (A : Over (Sp (Γ(X, U.1) ⧸ m))) [GrpObj A] (ι : A.left ⟶ t.G.left), IsGrpPullback A t.G (spMap (Ideal.Quotient.mk m) ≫ chart U) ι → ∀ (r : Fin n → Γ(X, U.1)) (h' : ∀ i, Γ(A.left, ι ⁻¹ᵁ W i)), (∀ i i', (ι.appLE (W i ⊓ W i') (ι ⁻¹ᵁ W i ⊓ ι ⁻¹ᵁ W i') (fun _ hx => hx)).hom (∑ b, (t.G.hom.appLE U.1 (W i ⊓ W i') (inf_le_left.trans (hWU i))).hom (r b) * (δ b (W i ⊓ W i') (resG t.G.left (inf_le_inf (hj i) (hj i')) (t.PP.L.g (j i) (j i')).val) * resG t.G.left (inf_le_inf (hj i) (hj i')) (t.PP.L.g (j i) (j i'))⁻¹.val)) = resG A.left inf_le_left (h' i) - resG A.left inf_le_right (h' i')) → ∀ b, r b ∈ m := GlobalTheory.FibreIndep.fibre_indep'
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FibreKernelKilledOfBaseFaithfullyFlat
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.SiegelTor GlobalTheory.EndLoc
open scoped CategoryTheory.Obj

namespace GlobalTheory.KerKilledFibre

theorem one_left_push {S S' : Scheme.{0}} {G' : Over S'} [GrpObj G'] {G : Over S} [GrpObj G] {f : S' ⟶ S}
    {φ : G'.left ⟶ G.left} (h : IsGrpPullback G' G f φ) (T : Over S') :
    (1 : Over.mk (T.hom ≫ f) ⟶ G).left = (1 : T ⟶ G').left ≫ φ := by
  let u : Over.mk (T.hom ≫ f) ⟶ G := Over.homMk ((1 : T ⟶ G').left ≫ φ) (by
    simp only [Over.mk_hom, Category.assoc]
    rw [h.1.w, ← Category.assoc, Over.w])
  have hu : u * u = u := Over.OverMorphism.ext (by
    rw [h.2 T 1 1 u u rfl rfl, _root_.mul_one]; rfl)
  have : u = 1 := mul_eq_left.1 hu
  rw [← this]
  rfl

theorem pow_left_push {S S' : Scheme.{0}} {G' : Over S'} [GrpObj G'] {G : Over S} [GrpObj G] {f : S' ⟶ S}
    {φ : G'.left ⟶ G.left} (h : IsGrpPullback G' G f φ) {T : Over S'} (x : T ⟶ G') (x₀ : Over.mk (T.hom ≫ f) ⟶ G)
    (hx : x₀.left = x.left ≫ φ) (n : ℕ) : (x₀ ^ n).left = (x ^ n).left ≫ φ := by
  induction n with
  | zero => rw [pow_zero, pow_zero]; exact one_left_push h T
  | succ n ih =>
    rw [pow_succ, pow_succ]
    exact h.2 T _ _ _ _ ih hx

theorem comp_pow_pt {S : Scheme.{0}} {G A B : Over S} [GrpObj G] (f : A ⟶ B) (g : B ⟶ G) (n : ℕ) :
    f ≫ g ^ n = (f ≫ g) ^ n := by
  induction n with
  | zero => rw [pow_zero, pow_zero, MonObj.comp_one]
  | succ n ih => rw [pow_succ, pow_succ, MonObj.comp_mul, ih]

end GlobalTheory.KerKilledFibre

namespace GlobalTheory.KerKilledFibre

theorem fibreKilled_of_base : ∀ (d : ℕ) (S' : Scheme.{0}) [IsLocallyNoetherian S'] (G : Over S') [GrpObj G] [IsCommMonObj G] (P : LB (G2 G).left), IsAbelianScheme G → P.IsLB → (∃ s : (P.pull (lift (1 : G ⟶ G) (𝟙 G)).left).Gen, s.IsGen) → (∃ s : (P.pull (lift (𝟙 G) (1 : G ⟶ G)).left).Gen, s.IsGen) → LBIso P (P.pull (lift (snd G G) (fst G G)).left) → ∀ (T : Scheme.{0}) (g : T ⟶ S') (A' : Over T) [GrpObj A'] [IsCommMonObj A'] (φ : A'.left ⟶ G.left) (φ₂ : (G2 A').left ⟶ (G2 G).left) (P' : LB (G2 A').left), IsGrpPullback A' G g φ → IsSquare φ φ₂ → P'.IsLB → LBIso P' (P.pull φ₂) → IsUnit ((d : ℕ) : Γ(T, ⊤)) → (∀ (T' : Over T) (x : T' ⟶ A'), (∃ s : (P'.pull (lift (snd A' T' ≫ x) (fst A' T')).left).Gen, s.IsGen) → x ^ d = 1) → ∀ t : T, GlobalTheory.KerKilledNear.FibreKilled d G P (g.base t) := by
  intro d S' _ G _ _ P _ hP _ _ _ T g A' _ _ φ φ₂ P' hpb hsq hP' hiso _ H t T' x hT' hgen
  obtain ⟨f, hf⟩ := hT'
  obtain ⟨c, hc⟩ := hgen
  let r : Spec (T.residueField t) ⟶ Spec (S'.residueField (g.base t)) := Spec.map (g.residueFieldMap t)
  have hr : r ≫ S'.fromSpecResidueField (g.base t) = T.fromSpecResidueField t ≫ g :=
    Scheme.Hom.SpecMap_residueFieldMap_fromSpecResidueField g t
  let p1 : pullback f r ⟶ T'.left := pullback.fst f r
  let p2 : pullback f r ⟶ Spec (T.residueField t) := pullback.snd f r
  let T'' : Over T := Over.mk (p2 ≫ T.fromSpecResidueField t)
  have hw : p1 ≫ T'.hom = T''.hom ≫ g := by
    show p1 ≫ T'.hom = (p2 ≫ T.fromSpecResidueField t) ≫ g
    rw [hf, ← Category.assoc, pullback.condition, Category.assoc, hr, Category.assoc]
  have hxw : (p1 ≫ x.left) ≫ G.hom = T''.hom ≫ g := by rw [Category.assoc, Over.w x]; exact hw
  let x'' : T'' ⟶ A' := Over.homMk (hpb.1.lift (p1 ≫ x.left) T''.hom hxw) (hpb.1.lift_snd _ _ _)
  have hx''φ : x''.left ≫ φ = p1 ≫ x.left := hpb.1.lift_fst _ _ _

  let Y : Over S' := Over.mk ((A' ⊗ T'').hom ≫ g)
  let a : Y ⟶ G := Over.homMk ((fst A' T'').left ≫ φ) (by
    show ((fst A' T'').left ≫ φ) ≫ G.hom = (A' ⊗ T'').hom ≫ g
    rw [Category.assoc, hpb.1.w, ← Category.assoc]
    exact congrArg (· ≫ g) (Over.w (fst A' T'')))
  let b : Y ⟶ T' := Over.homMk ((snd A' T'').left ≫ p1) (by
    show ((snd A' T'').left ≫ p1) ≫ T'.hom = (A' ⊗ T'').hom ≫ g
    rw [Category.assoc, hw, ← Category.assoc]
    exact congrArg (· ≫ g) (Over.w (snd A' T'')))
  let m := (lift a b).left
  let ψ := (lift (snd G T' ≫ x) (fst G T')).left
  let ψ'' := (lift (snd A' T'' ≫ x'') (fst A' T'')).left
  have heq : ψ'' ≫ φ₂ = m ≫ ψ := by
    have k1 : ψ ≫ (fst G G).left = (snd G T' ≫ x).left := by rw [← Over.comp_left, lift_fst]
    have k2 : ψ'' ≫ (fst A' A').left = (snd A' T'' ≫ x'').left := by rw [← Over.comp_left, lift_fst]
    have k3 : m ≫ (snd G T').left = b.left := by rw [← Over.comp_left, lift_snd]
    have k4 : ψ ≫ (snd G G).left = (fst G T').left := by rw [← Over.comp_left, lift_snd]
    have k5 : ψ'' ≫ (snd A' A').left = (fst A' T'').left := by rw [← Over.comp_left, lift_snd]
    have k6 : m ≫ (fst G T').left = a.left := by rw [← Over.comp_left, lift_fst]
    apply Over.tensorObj_ext
    · show ψ'' ≫ φ₂ ≫ (fst G G).left = m ≫ ψ ≫ (fst G G).left
      rw [hsq.1, reassoc_of% k2, k1]
      simp only [Over.comp_left, Category.assoc]
      rw [reassoc_of% k3, hx''φ]
      show _ = ((snd A' T'').left ≫ p1) ≫ x.left
      rw [Category.assoc]
    · show ψ'' ≫ φ₂ ≫ (snd G G).left = m ≫ ψ ≫ (snd G G).left
      rw [hsq.2, reassoc_of% k5, k4, k6]
      rfl
  obtain ⟨w, hwg⟩ := hiso
  obtain ⟨c1, hc1⟩ := gen_chartPull
    (chartPullSame P (fun _ : PUnit => ψ'' ≫ φ₂) (fun _ => ψ) (fun _ => 1) m (fun _ => heq)) c hc
  obtain ⟨c2, hc2⟩ := exists_down ((isGen_iff w).1 hwg) hP hP' (φ' := fun _ : PUnit => ψ'')
    (ε := fun _ => 1) c1 hc1
  have hx'' : x'' ^ d = 1 := H T'' x'' ⟨c2, hc2⟩

  let ρ : Over.mk (T''.hom ≫ g) ⟶ T' := Over.homMk p1 hw
  have hρ : (ρ ≫ x).left = x''.left ≫ φ := hx''φ.symm
  have e1 : ((ρ ≫ x) ^ d).left = (1 : Over.mk (T''.hom ≫ g) ⟶ G).left := by
    rw [pow_left_push hpb x'' (ρ ≫ x) hρ d, hx'', one_left_push hpb T'']
  have e2 : p1 ≫ (x ^ d).left = p1 ≫ (1 : T' ⟶ G).left := by
    have := congrArg CommaMorphism.left ((comp_pow_pt ρ x d).trans
      ((Over.OverMorphism.ext e1).trans (MonObj.comp_one ρ).symm))
    exact this
  have : Flat r := inferInstance
  have : Surjective r := ⟨Function.surjective_to_subsingleton _⟩
  have : Epi p1 := Flat.epi_of_flat_of_surjective _
  exact Over.OverMorphism.ext ((cancel_epi p1).1 e2)

end GlobalTheory.KerKilledFibre
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.KernelKilledOverOpenOfLocalStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.SiegelTor GlobalTheory.EndLoc
open scoped CategoryTheory.Obj
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.kernelKilledOverOpen_of_local : ∀ (d : ℕ) (S' : Scheme.{0}) (G : Over S') [GrpObj G] [IsCommMonObj G] (P : LB (G2 G).left) (W : S'.Opens), (∀ p ∈ W, ∃ V : S'.Opens, p ∈ V ∧ GlobalTheory.KerKilledLocus.KerKilledOn d G P V) → GlobalTheory.KerKilledLocus.KerKilledOn d G P W := by
  first | (exact @GlobalTheory.KerKilledLocal.kerKilledOn_of_local) | (exact GlobalTheory.KerKilledLocal.kerKilledOn_of_local) | (intros; apply GlobalTheory.KerKilledLocal.kerKilledOn_of_local <;> assumption)
end

