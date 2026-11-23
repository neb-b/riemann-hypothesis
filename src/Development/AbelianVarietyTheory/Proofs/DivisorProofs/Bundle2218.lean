module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0026
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0028
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0022
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1991
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1999
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2008
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2066
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsDatNeZero
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0063
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0044
public import Development.AbelianVarietyTheory.Definitions.Divisors.ToIThCapDegOfAddNsmulDivP
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsFrobGBaseChange
public import Formalism.SharpRestriction.Divisibility.Bundle0002
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0059
public import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.MemNonzeroLocusIffPowFn
public import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.RestrictPullbackIsoHomAppPullbackSections
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2046
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0011

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SubsingletonSpectrumDualNumber
section
set_option autoImplicit false
noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon GlobalTheory.DualOpen
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.DualOpen

theorem subsingleton_spectrum_dualNumber (K : Type) [Field K] : Subsingleton (PrimeSpectrum (DualNumber K)) := by
  have key : ∀ (p : PrimeSpectrum (DualNumber K)) (x : DualNumber K), x ∈ p.asIdeal ↔ x.fst = 0 := by
    intro p x
    constructor
    · intro hx
      by_contra h
      have hu : IsUnit x := TrivSqZeroExt.isUnit_iff_isUnit_fst.2 (isUnit_iff_ne_zero.2 h)
      exact p.isPrime.ne_top (Ideal.eq_top_of_isUnit_mem _ hx hu)
    · intro h
      have hsq : x * x = 0 := by
        refine TrivSqZeroExt.ext ?_ ?_ <;> simp [h]
      exact p.isPrime.mem_of_pow_mem 2 (by rw [pow_two, hsq]; exact p.asIdeal.zero_mem)
  exact ⟨fun p q => PrimeSpectrum.ext (Ideal.ext fun x => by rw [key p x, key q x])⟩

private theorem spMap_comp_of_eq {R₁ R₂ R₂' R₃ : Type} [CommRing R₁] [CommRing R₂] [CommRing R₂'] [CommRing R₃]
    {f : R₁ →+* R₂} {g : R₂ →+* R₃} {f' : R₁ →+* R₂'} {g' : R₂' →+* R₃} (h : g.comp f = g'.comp f') :
    spMap g ≫ spMap f = spMap g' ≫ spMap f' := by
  simp only [spMap, ← Spec.map_comp, ← CommRingCat.ofHom_comp, h]

theorem tanLift_of_fieldChart : ∀ (S : Scheme.{0}) (A : Over S) [GrpObj A], IsAbelianScheme A →
    ∀ (U : Over S) [LocallyOfFiniteType U.hom] (M : LB (A ⊗ U).left), Fam A M → Inj A M → FieldChart A M →
      TanLift A M := by
  intro S A _ hA U _ M hM hInj hFC k _ s N hN u₀ h₀
  obtain ⟨hpull, -, -, hcomp, hev⟩ := _root_.GlobalTheory.FamCalc.famCalc S A
  obtain ⟨ψ, hψ₁, hψ₂, hflat, hsurj⟩ :=
    _root_.GlobalTheory.DualOpen.dualNumber_map_flat_surjective k (AlgebraicClosure k) (algebraMap k (AlgebraicClosure k))

  let T : Over S := Over.mk (spMap (dnInl k) ≫ s)
  haveI : IsNoetherianRing (DualNumber k) := inferInstance
  haveI : IsLocallyNoetherian T.left := (inferInstance : IsLocallyNoetherian (Sp (DualNumber k)))
  obtain ⟨G, π, hmono, -, hG⟩ := _root_.GlobalTheory.DualGraph.exists_mono_same S A hA T U N M hN hM hInj
  haveI : Mono π.left := hmono

  let Y : Over S := Over.mk (spMap ψ ≫ spMap (dnInl k) ≫ s)
  let y : Y ⟶ T := Over.homMk (spMap ψ)
  have hq : spMap ψ ≫ spMap (dnInl k) =
      spMap (dnInl (AlgebraicClosure k)) ≫ spMap (algebraMap k (AlgebraicClosure k)) :=
    spMap_comp_of_eq hψ₁
  let q : Y ⟶ Over.mk (spMap (algebraMap k (AlgebraicClosure k)) ≫ s) :=
    Over.homMk (spMap (dnInl (AlgebraicClosure k))) ((reassoc_of% hq) s).symm
  have hN' : Fam A (ev N (fst A Y) (snd A Y ≫ y)) := hpull T Y N y hN
  obtain ⟨W, hW⟩ := hFC (AlgebraicClosure k) (spMap (algebraMap k (AlgebraicClosure k)) ≫ s) Y q _ hN'

  let Z : Over S := Over.mk (spMap (dnFst (AlgebraicClosure k)) ≫ Y.hom)
  let z : Z ⟶ Y := Over.homMk (spMap (dnFst (AlgebraicClosure k)))
  have hr : spMap (dnFst (AlgebraicClosure k)) ≫ spMap ψ =
      spMap (algebraMap k (AlgebraicClosure k)) ≫ spMap (dnFst k) :=
    spMap_comp_of_eq hψ₂
  let e : Z ⟶ Over.mk (spMap (dnFst k) ≫ spMap (dnInl k) ≫ s) :=
    Over.homMk (spMap (algebraMap k (AlgebraicClosure k))) ((reassoc_of% hr) (spMap (dnInl k) ≫ s)).symm
  have hez : e ≫ ptMap _ (dnFst k) = z ≫ y := by
    ext
    exact hr.symm
  have h₁ : Same A N M (z ≫ y) (e ≫ u₀) := by
    rw [← hez]
    exact hcomp T U _ Z N M (ptMap _ (dnFst k)) u₀ e hN.isLB hM.isLB h₀
  have h₂ : Same A (ev N (fst A Y) (snd A Y ≫ y)) M z (e ≫ u₀) :=
    (hev T U Y Z N M y z _ hN.isLB hM.isLB).2 h₁
  have hx : ∀ x, z.left x ∈ W := (hW Z z).1 ⟨_, h₂⟩

  haveI : Subsingleton Y.left := subsingleton_spectrum_dualNumber (AlgebraicClosure k)
  have x₀ : Z.left := IsLocalRing.closedPoint (AlgebraicClosure k)
  have hall : ∀ x : Y.left, x ∈ W := fun x => by
    rw [Subsingleton.elim x (z.left x₀)]
    exact hx x₀
  obtain ⟨u', hu'⟩ := (hW Y (𝟙 Y)).2 (fun x => hall _)
  have h₃ : Same A N M y u' := by
    have := (hev T U Y Y N M y (𝟙 Y) u' hN.isLB hM.isLB).1 hu'
    rwa [Category.id_comp] at this

  obtain ⟨z', hz'⟩ := (hG Y y).1 ⟨u', h₃⟩
  haveI : Flat (spMap ψ) := hflat
  haveI : Surjective (spMap ψ) := hsurj
  obtain ⟨w, hw⟩ := _root_.GlobalTheory.DualOpen.exists_lift_of_fpqc_cover G.left T.left Y.left T.left π.left (𝟙 _) (spMap ψ) z'
    (by rw [Category.comp_id]; exact hz')
  exact (hG T (𝟙 T)).2 ⟨w, hw⟩

end GlobalTheory.DualOpen
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SumTwoPointFunctionMultiplesNaturalCharP
section
open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct WithConv
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Sp spMap epsR IsTangent IsGrpPullback)
open ReciprocityTheory.ChartRestriction.G.Semi (IsAbelianScheme LB RigLB CubicalStr Theta thφ thε thK x3)
open GlobalTheory GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.PDiv GlobalTheory.PtExt
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.PtExt

theorem chi_natural (p : ℕ) (R : Type) [CommRing R] (hp : (p : R) = 0)
    (A : Over (Sp R)) [GrpObj A] (f : Fn1 A) (g : Fn2 A) (hg : IsAdd f g)
    (D : Type) [CommRing D] [Algebra R D] (D' : Type) [CommRing D'] [Algebra R D']
    (φ : D →ₐ[R] D') (x : Pt A D) :
    chi p g D' (spOver φ ≫ x) - φ (chi p g D x) = f D D' φ (x ^ p) - f D D' φ 1 := by
  have hp' : (p : D') = 0 := by
    rw [← map_natCast (algebraMap R D') p, hp, map_zero]
  unfold chi
  rw [map_sum φ, ← Finset.sum_sub_distrib]
  have h : ∀ i ∈ Finset.range p, g D' ((spOver φ ≫ x) ^ i) (spOver φ ≫ x) - φ (g D (x ^ i) x) =
      (f D D' φ (x ^ (i + 1)) - f D D' φ (x ^ i)) - f D D' φ x := by
    intro i _
    rw [← MonObj.comp_pow, hg D D' φ (x ^ i) x, pow_succ]
  rw [Finset.sum_congr rfl h, Finset.sum_sub_distrib, Finset.sum_range_sub (fun i ↦ f D D' φ (x ^ i)) p,
    Finset.sum_const, Finset.card_range, nsmul_eq_mul, hp', zero_mul, sub_zero, pow_zero]

end GlobalTheory.PtExt
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SupportPullbackEqPreimage
section
open CategoryTheory Limits AlgebraicGeometry IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Out
open GlobalTheory GlobalTheory.QCoh GlobalTheory.CechPic GlobalTheory.Vert GlobalTheory.Twist

namespace GlobalTheory.QCoh


open TensorProduct in
theorem nontrivial_fibre_of_isBaseChange {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]
    {M N : Type*} [AddCommGroup M] [Module R M]
    [AddCommGroup N] [Module R N] [Module S N] [IsScalarTower R S N]
    {l : M →ₗ[R] N} (hl : IsBaseChange S l) (p : Ideal R) [p.IsPrime] (q : Ideal S) [q.IsPrime]
    (hpq : p = q.comap (algebraMap R S)) :
    Nontrivial (q.ResidueField ⊗[S] N) ↔ Nontrivial (p.ResidueField ⊗[R] M) := by
  letI : Algebra p.ResidueField q.ResidueField :=
    (Ideal.ResidueField.map p q (algebraMap R S) hpq).toAlgebra
  haveI : IsScalarTower R p.ResidueField q.ResidueField :=
    .of_algebraMap_eq fun r =>
      (IsScalarTower.algebraMap_apply R S q.ResidueField r).trans
        (Ideal.ResidueField.map_algebraMap _ _ _ hpq r).symm
  have e₁ : q.ResidueField ⊗[S] N ≃ₗ[S] q.ResidueField ⊗[S] (S ⊗[R] M) :=
    LinearEquiv.lTensor q.ResidueField hl.equiv.symm
  have e₂ : q.ResidueField ⊗[S] (S ⊗[R] M) ≃ₗ[q.ResidueField] q.ResidueField ⊗[R] M :=
    AlgebraTensorModule.cancelBaseChange R S q.ResidueField q.ResidueField M
  have e₃ : q.ResidueField ⊗[p.ResidueField] (p.ResidueField ⊗[R] M) ≃ₗ[q.ResidueField]
      q.ResidueField ⊗[R] M :=
    AlgebraTensorModule.cancelBaseChange R p.ResidueField q.ResidueField q.ResidueField M
  rw [e₁.toEquiv.nontrivial_congr, e₂.toEquiv.nontrivial_congr, ← e₃.toEquiv.nontrivial_congr]
  exact Module.FaithfullyFlat.nontrivial_tensorProduct_iff_right p.ResidueField q.ResidueField

theorem mem_support_of_isBaseChange {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]
    {M N : Type*} [AddCommGroup M] [Module R M] [Module.Finite R M]
    [AddCommGroup N] [Module R N] [Module S N] [IsScalarTower R S N]
    {l : M →ₗ[R] N} (hl : IsBaseChange S l) (q : PrimeSpectrum S) :
    q ∈ Module.support S N ↔ PrimeSpectrum.comap (algebraMap R S) q ∈ Module.support R M := by
  haveI : Module.Finite S N := Module.Finite.equiv hl.equiv
  rw [Module.mem_support_iff_nontrivial_residueField_tensorProduct,
    Module.mem_support_iff_nontrivial_residueField_tensorProduct]
  exact nontrivial_fibre_of_isBaseChange hl _ _ rfl

theorem support_pullback {X Y : Scheme.{0}} (f : Y ⟶ X) (G : X.Modules) [IsFiniteQC G] :
    support ((Scheme.Modules.pullback f).obj G) = f.base ⁻¹' support G := by
  ext y
  obtain ⟨U, V, hU, hV, hy, -, e⟩ := exists_affine_pair f y (W := ⊤) trivial
  have hfy : f y ∈ V := e hy
  rw [Set.mem_preimage, mem_support_iff_primeIdealOf hU ⟨y, hy⟩,
    mem_support_iff_primeIdealOf hV ⟨f y, hfy⟩]
  letI := appLEAlgebra f e
  letI := appLEModule f ((Scheme.Modules.pullback f).obj G) e
  haveI := appLE_isScalarTower f ((Scheme.Modules.pullback f).obj G) e
  have := finite_sections G hV
  rw [mem_support_of_isBaseChange (isBaseChange_pullbackSections f G hU hV e)]
  have h := IsAffineOpen.comap_primeIdealOf_appLE V hV U hU e hy
  convert Iff.rfl using 2
  exact h.symm

end GlobalTheory.QCoh
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SurjectiveSpMapOfSq
section
open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct WithConv
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Sp spMap epsR IsTangent IsGrpPullback)
open ReciprocityTheory.ChartRestriction.G.Semi (IsAbelianScheme LB RigLB CubicalStr Theta thφ thε thK x3)
open GlobalTheory GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.PDiv GlobalTheory.PtExt
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.PtExt

theorem surjective_spMap_of_sq {A B : Type} [CommRing A] [CommRing B] (π : A →+* B) (hπ : Function.Surjective π)
    (hsq : ∀ a ∈ RingHom.ker π, a * a = 0) : Function.Surjective (spMap π) := fun x ↦ by
  have hx : x ∈ PrimeSpectrum.zeroLocus (RingHom.ker π : Set A) := fun a ha ↦
    (x.isPrime.mem_or_mem ((hsq a ha).symm ▸ x.asIdeal.zero_mem)).elim id id
  rw [← range_comap_of_surjective B π hπ] at hx
  exact hx

theorem pt_dual_le_of_fst : ∀ (R : Type) [CommRing R] (H : Over (Sp R)) (D : Type) [CommRing D] [Algebra R D]
      (Z : Over.mk (spMap (algebraMap R (DualNumber D))) ⟶ H) (U : H.left.Opens),
      ⊤ ≤ (spOver (TrivSqZeroExt.fstHom R D D) ≫ Z).left ⁻¹ᵁ U → ⊤ ≤ Z.left ⁻¹ᵁ U := by
  intro R _ H D _ _ Z U h x _
  have hs : Function.Surjective (spMap ((TrivSqZeroExt.fstHom R D D : DualNumber D →ₐ[R] D) : DualNumber D →+* D)) :=
    surjective_spMap_of_sq _ (fun d ↦ ⟨TrivSqZeroExt.inl d, rfl⟩) fun a ha ↦ by
      have h0 : a.fst = 0 := ha
      ext <;> simp [h0]
  obtain ⟨y, rfl⟩ := hs x
  have hy := h (show y ∈ (⊤ : (Sp D).Opens) from trivial)
  simpa [Over.comp_left, PDiv.spOver_left] using hy

end GlobalTheory.PtExt
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SymmetricPullbackGeneratorEvenValue
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.UTau0

theorem uw_even_val : ∀ (R : Type) [CommRing R] [IsDomain R] (D₀ : DegPre R) (f : D₀.P.A ⟶ D₀.P.A) [IsMonHom f]
    (uw : LB.Gen (LB.LinComb D₀.P.L (GlobalTheory.UTau0.w0φ D₀ f) GlobalTheory.UTau0.w0ε)), uw.IsGen →
    LB.Gen.Corr D₀.P.L _ _ _ _ (LB.pullGen D₀.P.L _ _ uw (eSec D₀.P.A)) (LB.oneGen D₀.P.L) →
    ∀ (T : Over (Sp R)) (x : T ⟶ D₀.P.A) (z : T.left) (J : (T.left ⟶ D₀.P.A.left) → D₀.P.L.ι), Good D₀.P.L z J →
      val uw x⁻¹.left z J * val D₀.sym x.left z J * cubV D₀.cub z J (x ≫ f) (x ≫ f)⁻¹ x⁻¹ =
        val uw x.left z J * cubV D₀.cub z J x x⁻¹ (x ≫ f) := by
  intro R _ _ D₀ f _ uw hu h₀ T x z J hJ
  let gL := LB.mulGen D₀.P.L _ _ _ _
      (LB.mulGen D₀.P.L _ _ _ _ (LB.pullGen D₀.P.L _ _ uw ((𝟙 D₀.P.A)⁻¹).left) D₀.sym)
      (LB.pullGen D₀.P.L (thφ D₀.P.A (x3 D₀.P.A)) thε D₀.cub.t (lift f (lift f⁻¹ (𝟙 D₀.P.A)⁻¹)).left)
  let gR := LB.mulGen D₀.P.L _ _ _ _ uw
      (LB.pullGen D₀.P.L (thφ D₀.P.A (x3 D₀.P.A)) thε D₀.cub.t (lift (𝟙 D₀.P.A) (lift (𝟙 D₀.P.A)⁻¹ f)).left)
  have ev : ∀ {T' : Over (Sp R)} (σ : T' ⟶ D₀.P.A) {z : T'.left} {J}, Good D₀.P.L z J →
      val gL σ.left z J = val uw (σ ≫ (𝟙 D₀.P.A)⁻¹).left z J * val D₀.sym σ.left z J *
          cubV D₀.cub z J (σ ≫ f) (σ ≫ f⁻¹) (σ ≫ (𝟙 D₀.P.A)⁻¹) ∧
        val gR σ.left z J = val uw σ.left z J *
          cubV D₀.cub z J (σ ≫ 𝟙 D₀.P.A) (σ ≫ (𝟙 D₀.P.A)⁻¹) (σ ≫ f) := fun σ z J hJ =>
    ⟨(val_mul hJ _ _ _).trans (congrArg₂ (· * ·) ((val_mul hJ _ _ _).trans (congrArg₂ (· * ·)
        (val_pull hJ _ _ _) rfl)) (val_cub D₀.cub σ hJ _ _ _)),
      (val_mul hJ _ _ _).trans (congrArg₂ (· * ·) rfl (val_cub D₀.cub σ hJ _ _ _))⟩

  have pw : ∀ (V : Type) [CommGroup V] (k : (D₀.P.A.left ⟶ D₀.P.A.left) → V) (σ : D₀.P.A ⟶ D₀.P.A),
      ∏ i, k (σ.left ≫ w0φ D₀ f i) ^ w0ε i =
        k (σ * (σ ≫ f)).left * (k σ.left)⁻¹ * (k σ.left)⁻¹ * (k (σ ≫ f).left)⁻¹ *
          k (1 : D₀.P.A ⟶ D₀.P.A).left * k (1 : D₀.P.A ⟶ D₀.P.A).left := by
    intro V _ k σ
    have e₀ : σ.left ≫ (padd D₀.P.A (𝟙 _) f).left = (σ * (σ ≫ f)).left :=
      congrArg (fun q : D₀.P.A ⟶ D₀.P.A => q.left) ((MonObj.comp_mul _ _ _).trans (by rw [Category.comp_id]))
    have e₃ : σ.left ≫ (toUnit D₀.P.A ≫ η[D₀.P.A]).left = (1 : D₀.P.A ⟶ D₀.P.A).left := by
      rw [← Over.comp_left]; congr 1; simp [Hom.one_def]
    rw [Fin.prod_univ_four]
    show k (σ.left ≫ (padd D₀.P.A (𝟙 _) f).left) ^ (1 : ℤ) * k (σ.left ≫ 𝟙 _) ^ (-2 : ℤ) *
      k (σ.left ≫ f.left) ^ (-1 : ℤ) * k (σ.left ≫ (toUnit D₀.P.A ≫ η[D₀.P.A]).left) ^ (2 : ℤ) = _
    rw [e₀, e₃, Category.comp_id]
    apply Additive.ofMul.injective
    simp only [ofMul_mul, ofMul_inv, ofMul_zpow, Over.comp_left]
    abel
  have hL : val gL x.left z J = val gR x.left z J := by
    refine gen_unique' D₀.P.isLB (u := gL) (u' := gR) ?_ D₀.P.A.hom (1 : 𝟙_ (Over (Sp R)) ⟶ D₀.P.A).left
      (Over.w (1 : 𝟙_ (Over (Sp R)) ⟶ D₀.P.A)) (GlobalTheory.globalFns_holds _ _ D₀.P.isAb).2 ?_ ?_ ?_ T.left x.left z J hJ
    · intro V _ k
      have pw0 : ∏ i, k (w0φ D₀ f i) ^ w0ε i = _ :=
        (Finset.prod_congr rfl fun i _ => by rw [Over.id_left, Category.id_comp]).trans (pw V k (𝟙 D₀.P.A))
      have ps : ∏ i : Fin 2, k (![(ι[D₀.P.A]).left, 𝟙 D₀.P.A.left] i) ^ (![1, -1] : Fin 2 → ℤ) i =
          k (Over.Hom.left (𝟙 D₀.P.A)⁻¹) * (k (Over.Hom.left (𝟙 D₀.P.A)))⁻¹ := by
        have : (𝟙 D₀.P.A)⁻¹ = ι[D₀.P.A] := by simp [Hom.inv_def]
        rw [Fin.prod_univ_two, this]
        simp
      refine (DVR.prod_sum₂ (K := Fin 4) (K' := thK) (U := V) _ pw0 (prod_cub _ _ _ k)).trans (Eq.trans ?_
        (DVR.prod_sum₂ (K := Fin 4 ⊕ Fin 2) (K' := thK) (U := V) _
          (DVR.prod_sum₂ (K := Fin 4) (K' := Fin 2) (U := V) _ (pw V k _) ps) (prod_cub _ _ _ k)).symm)
      have a1 : 𝟙 D₀.P.A ≫ f = f := Category.id_comp f
      have a2 : (𝟙 D₀.P.A)⁻¹ ≫ f = f⁻¹ := by rw [GrpObj.inv_comp, Category.id_comp]
      have a3 : 𝟙 D₀.P.A * (𝟙 D₀.P.A)⁻¹ * f = f := by group
      have a4 : 𝟙 D₀.P.A * (𝟙 D₀.P.A)⁻¹ = 1 := by group
      have a5 : f * f⁻¹ * (𝟙 D₀.P.A)⁻¹ = (𝟙 D₀.P.A)⁻¹ := by group
      have a6 : f * f⁻¹ = 1 := by group
      have a7 : f * (𝟙 D₀.P.A)⁻¹ = (𝟙 D₀.P.A)⁻¹ * f := mul_comm _ _
      have a8 : f⁻¹ * (𝟙 D₀.P.A)⁻¹ = (𝟙 D₀.P.A)⁻¹ * f⁻¹ := mul_comm _ _
      rw [a1, a2, a3, a4, a5, a6, a7, a8]
      apply Additive.ofMul.injective
      simp only [ofMul_mul, ofMul_inv]
      abel
    · exact DVR.mulGen_isGen _ _ _ _ _ _ _ (DVR.mulGen_isGen _ _ _ _ _ _ _ (DVR.pullGen_isGen _ _ _ _ hu _) D₀.sym_gen)
        (DVR.pullGen_isGen _ _ _ _ D₀.cub.isGen _)
    · exact DVR.mulGen_isGen _ _ _ _ _ _ _ hu (DVR.pullGen_isGen _ _ _ _ D₀.cub.isGen _)
    · intro y I hI
      have C : IsCub (cubV D₀.cub (T := 𝟙_ _) y I) := isCub_cubV D₀.cub hI
      have o : (1 : 𝟙_ (Over (Sp R)) ⟶ D₀.P.A).left = eSec D₀.P.A := by simp [Hom.one_def, eSec]
      have u1 : val uw (1 : 𝟙_ (Over (Sp R)) ⟶ D₀.P.A).left y I = 1 := by
        have := val_corr hI h₀ (𝟙 _)
        rwa [val_pull hI, Category.id_comp, val_one, ← o] at this
      have s1 : val D₀.sym (1 : 𝟙_ (Over (Sp R)) ⟶ D₀.P.A).left y I = 1 := by
        have := val_corr hI D₀.sym_rig (𝟙 _)
        rwa [val_pull hI, Category.id_comp, val_one, ← o] at this
      have i1 : (1 : 𝟙_ (Over (Sp R)) ⟶ D₀.P.A) ≫ (𝟙 D₀.P.A)⁻¹ = 1 := by
        rw [GrpObj.comp_inv, Category.comp_id, inv_one]
      have f1 : (1 : 𝟙_ (Over (Sp R)) ⟶ D₀.P.A) ≫ f⁻¹ = 1 := by
        rw [GrpObj.comp_inv, MonObj.one_comp, inv_one]
      rw [(ev _ hI).1, (ev _ hI).2, i1, f1, MonObj.one_comp, Category.comp_id, u1, s1, C.face]; simp only [_root_.mul_one]
  have := (ev x hJ).1.symm.trans (hL.trans (ev x hJ).2)
  rwa [GrpObj.comp_inv, GrpObj.comp_inv, Category.comp_id] at this

end GlobalTheory.UTau0
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SymmetricPullbackGeneratorSecondDifference
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section
namespace GlobalTheory.UTau0.SecondDiff

theorem prod_symmetricPullback_formalSum_eq {R : Type} [CommRing R] [IsDomain R] (D₀ : DegPre R) (f : D₀.P.A ⟶ D₀.P.A) {T : Over (Sp R)}
    (q : T ⟶ D₀.P.A) {U : Type} [CommGroup U] (h : (T.left ⟶ D₀.P.A.left) → U) :
    ∏ i, h (q.left ≫ GlobalTheory.UTau0.w0φ D₀ f i) ^ GlobalTheory.UTau0.w0ε i =
      h (q * (q ≫ f)).left * (h q.left ^ 2)⁻¹ * (h (q ≫ f).left)⁻¹ * h (1 : T ⟶ D₀.P.A).left ^ 2 := by
  have e₀ : q.left ≫ (padd D₀.P.A (𝟙 _) f).left = (q * (q ≫ f)).left := by
    rw [← Over.comp_left]
    exact congrArg (fun r : T ⟶ D₀.P.A => r.left)
      (show q ≫ padd D₀.P.A (𝟙 _) f = q * (q ≫ f) from (MonObj.comp_mul _ _ _).trans (by rw [Category.comp_id]))
  have e₃ : q.left ≫ (toUnit D₀.P.A ≫ η[D₀.P.A]).left = (1 : T ⟶ D₀.P.A).left := by
    rw [← Over.comp_left]
    exact congrArg (fun r : T ⟶ D₀.P.A => r.left)
      (show q ≫ toUnit D₀.P.A ≫ η[D₀.P.A] = 1 by rw [Hom.one_def, ← Category.assoc, comp_toUnit])
  rw [Fin.prod_univ_four]
  show h (q.left ≫ (padd D₀.P.A (𝟙 _) f).left) ^ (1 : ℤ) * h (q.left ≫ 𝟙 _) ^ (-2 : ℤ) *
    h (q.left ≫ f.left) ^ (-1 : ℤ) * h (q.left ≫ (toUnit D₀.P.A ≫ η[D₀.P.A]).left) ^ (2 : ℤ) = _
  rw [e₀, e₃, Category.comp_id, ← Over.comp_left]
  simp only [zpow_one, zpow_neg, zpow_ofNat, pow_one]

theorem uw_second_diff : ∀ (R : Type) [CommRing R] [IsDomain R] (D₀ : DegPre R) (f g : D₀.P.A ⟶ D₀.P.A) [IsMonHom f] [IsMonHom g],
    padd D₀.P.A f g = 𝟙 D₀.P.A →
    ∀ uw : LB.Gen (LB.LinComb D₀.P.L (GlobalTheory.UTau0.w0φ D₀ f) GlobalTheory.UTau0.w0ε), uw.IsGen →
    LB.Gen.Corr D₀.P.L _ _ _ _ (LB.pullGen D₀.P.L _ _ uw (eSec D₀.P.A)) (LB.oneGen D₀.P.L) →
    ∀ u : LB.Gen (LB.LinComb D₀.P.L (rosatiφ D₀.P.A f g) rosatiε), u.IsGen →
    LB.Gen.Corr D₀.P.L _ _ _ _ (LB.pullGen D₀.P.L _ _ u (zero2 D₀.P.A)) (LB.oneGen D₀.P.L) →
    ∀ (T : Over (Sp R)) (x x' : T ⟶ D₀.P.A) (z : T.left) (J : (T.left ⟶ D₀.P.A.left) → D₀.P.L.ι), Good D₀.P.L z J →
      val uw (x * x').left z J * cubV D₀.cub z J (x' ≫ f) (x' ≫ g) x =
        val uw x.left z J * val uw x'.left z J * val u (lift x x').left z J *
          cubV D₀.cub z J (x ≫ f) (x' ≫ f) x * cubV D₀.cub z J (x ≫ f) (x' ≫ f) x' *
          cubV D₀.cub z J x x' ((x ≫ f) * (x' ≫ f)) := by
  intro R _ _ D₀ f g _ _ hfg uw huw hw0 u hu hu0 T x x' z J hJ
  let p₀ : D₀.P.A ⊗ D₀.P.A ⟶ D₀.P.A := fst _ _
  let p₁ : D₀.P.A ⊗ D₀.P.A ⟶ D₀.P.A := snd _ _
  have mf : ∀ {T : Over (Sp R)} (a b : T ⟶ D₀.P.A), (a * b) ≫ f = (a ≫ f) * (b ≫ f) :=
    fun a b => MonObj.mul_comp a b f
  have fg : ∀ {T : Over (Sp R)} (a : T ⟶ D₀.P.A), (a ≫ f) * (a ≫ g) = a := fun a =>
    (MonObj.comp_mul _ _ _).symm.trans ((congrArg (a ≫ ·) (show f * g = 𝟙 _ from hfg)).trans (Category.comp_id a))
  let gLw := LB.mulGen D₀.P.L _ _ _ _ (LB.pullGen D₀.P.L _ _ uw (p₀ * p₁).left)
    (LB.pullGen D₀.P.L (thφ D₀.P.A (x3 D₀.P.A)) thε D₀.cub.t (lift (p₁ ≫ f) (lift (p₁ ≫ g) p₀)).left)
  let gRw := LB.mulGen D₀.P.L _ _ _ _
    (LB.mulGen D₀.P.L _ _ _ _ (LB.mulGen D₀.P.L _ _ _ _ (LB.pullGen D₀.P.L _ _ uw p₀.left)
      (LB.pullGen D₀.P.L _ _ uw p₁.left)) (LB.pullGen D₀.P.L _ _ u (lift p₀ p₁).left))
    (LB.mulGen D₀.P.L _ _ _ _ (LB.mulGen D₀.P.L _ _ _ _
      (LB.pullGen D₀.P.L (thφ D₀.P.A (x3 D₀.P.A)) thε D₀.cub.t (lift (p₀ ≫ f) (lift (p₁ ≫ f) p₀)).left)
      (LB.pullGen D₀.P.L (thφ D₀.P.A (x3 D₀.P.A)) thε D₀.cub.t (lift (p₀ ≫ f) (lift (p₁ ≫ f) p₁)).left))
      (LB.pullGen D₀.P.L (thφ D₀.P.A (x3 D₀.P.A)) thε D₀.cub.t (lift p₀ (lift p₁ ((p₀ ≫ f) * (p₁ ≫ f)))).left))
  have vq : ∀ {T' : Over (Sp R)} (σ : T' ⟶ D₀.P.A ⊗ D₀.P.A) {z : T'.left} {J}, Good D₀.P.L z J →
      ∀ {K : Type} [Fintype K] {φ : K → (D₀.P.A.left ⟶ D₀.P.A.left)} {ε : K → ℤ} (t : LB.Gen (LB.LinComb D₀.P.L φ ε))
        (q : D₀.P.A ⊗ D₀.P.A ⟶ D₀.P.A), val (LB.pullGen D₀.P.L _ _ t q.left) σ.left z J = val t (σ ≫ q).left z J :=
    fun σ z J hJ K _ φ ε t q => by rw [val_pull hJ, ← Over.comp_left]
  have evL : ∀ {T' : Over (Sp R)} (σ : T' ⟶ D₀.P.A ⊗ D₀.P.A) {z : T'.left} {J}, Good D₀.P.L z J →
      val gLw σ.left z J = val uw (σ ≫ (p₀ * p₁)).left z J *
        cubV D₀.cub z J (σ ≫ p₁ ≫ f) (σ ≫ p₁ ≫ g) (σ ≫ p₀) := fun σ z J hJ =>
    (val_mul hJ _ _ _).trans (congrArg₂ (· * ·) (vq σ hJ _ _) (val_cub D₀.cub σ hJ _ _ _))
  have evR : ∀ {T' : Over (Sp R)} (σ : T' ⟶ D₀.P.A ⊗ D₀.P.A) {z : T'.left} {J}, Good D₀.P.L z J →
      val gRw σ.left z J = val uw (σ ≫ p₀).left z J * val uw (σ ≫ p₁).left z J *
          val u (lift (σ ≫ p₀) (σ ≫ p₁)).left z J *
        (cubV D₀.cub z J (σ ≫ p₀ ≫ f) (σ ≫ p₁ ≫ f) (σ ≫ p₀) * cubV D₀.cub z J (σ ≫ p₀ ≫ f) (σ ≫ p₁ ≫ f) (σ ≫ p₁) *
          cubV D₀.cub z J (σ ≫ p₀) (σ ≫ p₁) (σ ≫ ((p₀ ≫ f) * (p₁ ≫ f)))) := fun σ z J hJ =>
    (val_mul hJ _ _ _).trans (congrArg₂ (· * ·) ((val_mul hJ _ _ _).trans (congrArg₂ (· * ·)
      ((val_mul hJ _ _ _).trans (congrArg₂ (· * ·) (vq σ hJ _ _) (vq σ hJ _ _)))
      (by rw [val_pull hJ, ← Over.comp_left, comp_lift])))
      ((val_mul hJ _ _ _).trans (congrArg₂ (· * ·) ((val_mul hJ _ _ _).trans (congrArg₂ (· * ·)
        (val_cub D₀.cub σ hJ _ _ _) (val_cub D₀.cub σ hJ _ _ _))) (val_cub D₀.cub σ hJ _ _ _))))

  let e : 𝟙_ (Over (Sp R)) ⟶ D₀.P.A ⊗ D₀.P.A := lift 1 1
  have he : e.left ≫ (snd D₀.P.A D₀.P.A).left ≫ D₀.P.A.hom = 𝟙 _ := by rw [Over.w]; exact Over.w e
  have sj : Function.Surjective ((snd D₀.P.A D₀.P.A).left ≫ D₀.P.A.hom).appTop.hom :=
    surj_comp (surj_snd GlobalTheory.globalFns_holds D₀.P.isAb _) ((GlobalTheory.globalFns_holds _ _ D₀.P.isAb).2)
  let ρ : T ⟶ D₀.P.A ⊗ D₀.P.A := lift x x'
  have key : val gLw ρ.left z J = val gRw ρ.left z J := by
    refine gen_unique' D₀.P.isLB (fun V _ k => ?_) _ e.left he sj ?_ ?_ (fun y I hI => ?_) _ ρ.left z J hJ
    · refine Eq.trans (DVR.prod_sum₂ (K := (Fin 4 ⊕ Fin 4) ⊕ Fin 6) (K' := (thK ⊕ thK) ⊕ thK) (U := V) _
          (DVR.prod_sum₂ (K := Fin 4 ⊕ Fin 4) (K' := Fin 6) (U := V) _
            (DVR.prod_sum₂ (K := Fin 4) (K' := Fin 4) (U := V) _ (prod_symmetricPullback_formalSum_eq D₀ f p₀ k) (prod_symmetricPullback_formalSum_eq D₀ f p₁ k))
            (prod_ros f g p₀ p₁ k))
          (DVR.prod_sum₂ (K := thK ⊕ thK) (K' := thK) (U := V) _
            (DVR.prod_sum₂ (K := thK) (K' := thK) (U := V) _ (prod_cub (p₀ ≫ f) (p₁ ≫ f) p₀ k)
              (prod_cub (p₀ ≫ f) (p₁ ≫ f) p₁ k))
            (prod_cub p₀ p₁ ((p₀ ≫ f) * (p₁ ≫ f)) k)))
        (Eq.trans ?_ (DVR.prod_sum₂ (K := Fin 4) (K' := thK) (U := V) _ (prod_symmetricPullback_formalSum_eq D₀ f (p₀ * p₁) k)
          (prod_cub (p₁ ≫ f) (p₁ ≫ g) p₀ k)).symm)
      rw [mf, fg, mul_comm p₁ p₀, mul_comm (p₀ ≫ f) p₀, mul_comm (p₁ ≫ f) p₁, mul_comm ((p₀ ≫ f) * (p₁ ≫ f)) p₀,
        mul_comm ((p₀ ≫ f) * (p₁ ≫ f)) p₁, mul_comm (p₁ ≫ g) p₀]
      apply Additive.ofMul.injective
      simp only [ofMul_mul, ofMul_inv, ofMul_pow]
      abel
    · exact DVR.mulGen_isGen _ _ _ _ _ _ _ (DVR.pullGen_isGen _ _ _ _ huw _) (DVR.pullGen_isGen _ _ _ _ D₀.cub.isGen _)
    · exact DVR.mulGen_isGen _ _ _ _ _ _ _ (DVR.mulGen_isGen _ _ _ _ _ _ _ (DVR.mulGen_isGen _ _ _ _ _ _ _
        (DVR.pullGen_isGen _ _ _ _ huw _) (DVR.pullGen_isGen _ _ _ _ huw _)) (DVR.pullGen_isGen _ _ _ _ hu _))
        (DVR.mulGen_isGen _ _ _ _ _ _ _ (DVR.mulGen_isGen _ _ _ _ _ _ _ (DVR.pullGen_isGen _ _ _ _ D₀.cub.isGen _)
          (DVR.pullGen_isGen _ _ _ _ D₀.cub.isGen _)) (DVR.pullGen_isGen _ _ _ _ D₀.cub.isGen _))
    · have C : IsCub (cubV D₀.cub y I) := isCub_cubV D₀.cub hI
      have w1 : val uw (1 : 𝟙_ (Over (Sp R)) ⟶ D₀.P.A).left y I = 1 := by
        have := val_corr hI hw0 (𝟙 _)
        rw [val_pull hI, Category.id_comp, val_one] at this
        have e1 : (1 : 𝟙_ (Over (Sp R)) ⟶ D₀.P.A) = η[D₀.P.A] := by simp [Hom.one_def]
        rw [e1]; exact this
      have u1 : val u (lift (1 : 𝟙_ (Over (Sp R)) ⟶ D₀.P.A) 1).left y I = 1 := by
        have := val_corr hI hu0 (𝟙 _)
        rw [val_pull hI, Category.id_comp, val_one] at this
        have e2 : lift (1 : 𝟙_ (Over (Sp R)) ⟶ D₀.P.A) 1 = lift η[D₀.P.A] η[D₀.P.A] := by simp [Hom.one_def]
        rw [e2]; exact this
      have a₀ : e ≫ p₀ = 1 := lift_fst _ _
      have a₁ : e ≫ p₁ = 1 := lift_snd _ _
      have af : e ≫ p₀ ≫ f = 1 := by rw [← Category.assoc, a₀, MonObj.one_comp]
      have bf : e ≫ p₁ ≫ f = 1 := by rw [← Category.assoc, a₁, MonObj.one_comp]
      have bg : e ≫ p₁ ≫ g = 1 := by rw [← Category.assoc, a₁, MonObj.one_comp]
      have ab : e ≫ (p₀ * p₁) = 1 := (MonObj.comp_mul _ _ _).trans (by rw [a₀, a₁, _root_.mul_one])
      have ff : e ≫ ((p₀ ≫ f) * (p₁ ≫ f)) = 1 := (MonObj.comp_mul _ _ _).trans (by rw [af, bf, _root_.mul_one])
      rw [evL e hI, evR e hI, ab, ff, af, bf, bg, a₀, a₁, w1, u1, C.face]
      simp
  rw [evL ρ hJ, evR ρ hJ] at key
  have r₀ : ρ ≫ p₀ = x := lift_fst _ _
  have r₁ : ρ ≫ p₁ = x' := lift_snd _ _
  have s₁ : ρ ≫ (p₀ * p₁) = x * x' := (MonObj.comp_mul _ _ _).trans (by rw [r₀, r₁])
  have s₂ : ρ ≫ ((p₀ ≫ f) * (p₁ ≫ f)) = (x ≫ f) * (x' ≫ f) :=
    (MonObj.comp_mul _ _ _).trans (by rw [← Category.assoc, ← Category.assoc, r₀, r₁])
  rw [s₁, s₂, ← Category.assoc ρ p₁ f, ← Category.assoc ρ p₁ g, ← Category.assoc ρ p₀ f, r₀, r₁] at key
  rw [key]
  simp only [_root_.mul_assoc]

end GlobalTheory.UTau0.SecondDiff
end
end

