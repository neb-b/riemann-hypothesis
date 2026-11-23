module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.IndEtOfForallFinset
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0007
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0134
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0008
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0386
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsSupercuspidalOfIsCuspidal
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0106
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0006
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0328
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0354
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0384
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0389
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0322
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0358
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0393
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0390
public import GroundTheory.AutomorphicForms.GKModules.Casimir
public import GroundTheory.AutomorphicForms.HarishChandraRegularity.ExpHaar
public import GroundTheory.AutomorphicForms.HarishChandraInvariance.Compact
public import GroundTheory.AutomorphicForms.Bundle0015
public import GroundTheory.AutomorphicForms.GKModules.ParametricIntegral
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0002
public import Formalism.UnipotentAdelicQuotients.EllRegCheck
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0337
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0379
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0352
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0301
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0004
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.PadicIsNonarchimedeanLocalField
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0391

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsFieldMonicRootsTensorFractionRingStrictlyHense
section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex Simplicial TensorProduct GlobalTheory.EtC

namespace GlobalTheory

open Polynomial

namespace AICStalk

theorem isIntegrallyClosed_of_aic {A : Type} [CommRing A] [IsDomain A] (h : GlobalTheory.EtC.AIC A) :
    IsIntegrallyClosed A := by
  rw [isIntegrallyClosed_iff (FractionRing A)]
  rintro x ⟨p, hpm, hp⟩
  suffices H : ∀ n : ℕ, ∀ p : A[X], p.Monic → p.natDegree = n → aeval x p = 0 →
      ∃ y, algebraMap A (FractionRing A) y = x by
    exact H _ p hpm rfl (by rwa [aeval_def])
  intro n
  induction n with
  | zero =>
    intro p hpm hdeg hp
    rw [Polynomial.eq_one_of_monic_natDegree_zero hpm hdeg] at hp
    simp at hp
  | succ n ih =>
    intro p hpm hdeg hp
    obtain ⟨a, ha⟩ := h p hpm (by omega)
    have hq : (X - C a) * (p /ₘ (X - C a)) = p := mul_divByMonic_eq_iff_isRoot.mpr ha
    have hqm : (p /ₘ (X - C a)).Monic := Polynomial.Monic.of_mul_monic_left (monic_X_sub_C a) (by rw [hq]; exact hpm)
    have hqd : (p /ₘ (X - C a)).natDegree = n := by
      rw [natDegree_divByMonic p (monic_X_sub_C a), natDegree_X_sub_C, hdeg]; rfl
    rw [← hq, map_mul] at hp
    simp only [map_sub, aeval_X, aeval_C] at hp
    rcases mul_eq_zero.mp hp with h1 | h1
    · exact ⟨a, (sub_eq_zero.mp h1).symm⟩
    · exact ih _ hqm hqd h1

theorem aic_of_ringEquiv {R S : Type} [CommRing R] [CommRing S] (e : R ≃+* S) (h : GlobalTheory.EtC.AIC R) :
    GlobalTheory.EtC.AIC S := by
  intro p hpm hdeg
  have hm : (p.map (e.symm : S →+* R)).Monic := hpm.map _
  have hd : (p.map (e.symm : S →+* R)).natDegree = p.natDegree :=
    natDegree_map_eq_of_injective e.symm.injective p
  obtain ⟨a, ha⟩ := h _ hm (hd ▸ hdeg)
  refine ⟨e a, ?_⟩
  have hp : p = (p.map (e.symm : S →+* R)).map (e : R →+* S) := by
    rw [Polynomial.map_map]; ext n; simp
  rw [hp, Polynomial.eval_map, show e a = (e : R →+* S) a from rfl, Polynomial.eval₂_at_apply, ha, map_zero]

theorem aic_of_isAlgClosed (K : Type) [Field K] [IsAlgClosed K] : GlobalTheory.EtC.AIC K := by
  intro p _ hdeg
  obtain ⟨a, ha⟩ := IsAlgClosed.exists_root p (by
    rw [degree_eq_natDegree (ne_zero_of_natDegree_gt hdeg)]; exact_mod_cast hdeg.ne')
  exact ⟨a, ha⟩

theorem algebraMap_injective_of_indEt {A O : Type} [CommRing A] [IsDomain A] [CommRing O]
    [Nontrivial O] [Algebra A O] (h : GlobalTheory.EtC.IndEt A O) : Function.Injective (algebraMap A O) := by
  haveI : Module.Flat A O := GlobalTheory.IndEtaleLocal.flat_of_isIndEtale h
  set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
  intro a ha
  by_contra ha0
  have hmem : (1 : O) ∈ Submodule.torsion A O := by
    rw [Submodule.mem_torsion_iff]
    exact ⟨⟨a, mem_nonZeroDivisors_of_ne_zero ha0⟩, by simp [Algebra.smul_def, ha]⟩
  rw [Module.Flat.torsion_eq_bot] at hmem
  exact one_ne_zero ((Submodule.mem_bot A).mp hmem)

theorem isDomain_of_indEt {A O : Type} [CommRing A] [IsDomain A] [IsIntegrallyClosed A]
    [CommRing O] [IsLocalRing O] [Algebra A O] (h : GlobalTheory.EtC.IndEt A O) : IsDomain O := by
  refine @NoZeroDivisors.to_isDomain O _ _ ⟨fun {x y} hxy => ?_⟩
  let I : Ideal (MvPolynomial (Fin 2) A) := Ideal.span {MvPolynomial.X 0 * MvPolynomial.X 1}
  haveI : Algebra.FinitePresentation A (MvPolynomial (Fin 2) A ⧸ I) :=
    Algebra.FinitePresentation.quotient (Submodule.fg_span_singleton _)
  let g : (MvPolynomial (Fin 2) A ⧸ I) →ₐ[A] O :=
    Ideal.Quotient.liftₐ I (MvPolynomial.aeval ![x, y]) (by
      intro a ha
      obtain ⟨b, rfl⟩ := Ideal.mem_span_singleton'.mp ha
      simp [hxy])
  obtain ⟨W, _, _, _, u, v, huv⟩ := GlobalTheory.IndEtaleLocal.exists_etale_factor h g
  let w : Fin 2 → W := fun i => u (Ideal.Quotient.mkₐ A I (MvPolynomial.X i))
  have hw : ∀ i, v (w i) = ![x, y] i := fun i => by
    have := DFunLike.congr_fun huv (Ideal.Quotient.mkₐ A I (MvPolynomial.X i))
    exact this.trans (MvPolynomial.aeval_X _ i)
  have h0 : w 0 * w 1 = 0 := by
    have : Ideal.Quotient.mkₐ A I (MvPolynomial.X 0) * Ideal.Quotient.mkₐ A I (MvPolynomial.X 1) = 0 := by
      rw [← map_mul]
      exact Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_span_singleton_self _)
    simp only [w, ← map_mul, this, map_zero]
  let q : Ideal W := (IsLocalRing.maximalIdeal O).comap v
  haveI : q.IsPrime := Ideal.comap_isPrime _ _
  obtain ⟨hdom, -⟩ := GlobalTheory.etale_localization_atPrime_isDomain_isIntegrallyClosed A W q
  have hq : ∀ t ∈ q.primeCompl, IsUnit (v t) := fun t ht => by
    by_contra hc
    exact ht (IsLocalRing.mem_maximalIdeal _ |>.mpr hc)
  have hm : algebraMap W (Localization.AtPrime q) (w 0) * algebraMap W (Localization.AtPrime q) (w 1) = 0 := by
    rw [← map_mul, h0, map_zero]
  rcases mul_eq_zero.mp hm with h1 | h1
  · obtain ⟨⟨t, ht⟩, hte⟩ := (IsLocalization.map_eq_zero_iff q.primeCompl _ _).mp h1
    have := congrArg v hte
    rw [map_mul, map_zero, hw] at this
    exact Or.inl (((hq t ht).mul_right_eq_zero).mp this)
  · obtain ⟨⟨t, ht⟩, hte⟩ := (IsLocalization.map_eq_zero_iff q.primeCompl _ _).mp h1
    have := congrArg v hte
    rw [map_mul, map_zero, hw] at this
    exact Or.inr (((hq t ht).mul_right_eq_zero).mp this)


attribute [local instance] Algebra.TensorProduct.rightAlgebra in
theorem isIntegral_tmul_one {A O : Type} [CommRing A] [IsDomain A] [CommRing O] [Algebra A O]
    (h : GlobalTheory.EtC.IndEt A O) (o : O) :
    IsIntegral (FractionRing A) (o ⊗ₜ[A] (1 : FractionRing A)) := by
  obtain ⟨W, _, _, _, u, v, huv⟩ := GlobalTheory.IndEtaleLocal.exists_etale_factor h (Polynomial.aeval (R := A) o)
  haveI : Algebra.Etale (FractionRing A) (FractionRing A ⊗[A] W) := Algebra.Etale.baseChange A W _
  haveI : Module.Finite (FractionRing A) (FractionRing A ⊗[A] W) :=
    Algebra.FormallyUnramified.finite_of_free _ _
  haveI : Algebra.IsIntegral (FractionRing A) (FractionRing A ⊗[A] W) := Algebra.IsIntegral.of_finite _ _
  let χ : W →ₐ[A] O ⊗[A] FractionRing A := (Algebra.TensorProduct.includeLeft (S := A)).comp v
  let Χ : FractionRing A ⊗[A] W →ₐ[FractionRing A] O ⊗[A] FractionRing A :=
    Algebra.TensorProduct.lift (Algebra.ofId _ _) χ (fun _ _ => Commute.all _ _)
  have hX : Χ (1 ⊗ₜ (u Polynomial.X)) = o ⊗ₜ 1 := by
    have := DFunLike.congr_fun huv Polynomial.X
    simp only [AlgHom.comp_apply, Polynomial.aeval_X] at this
    simp [Χ, χ, this]
  rw [← hX]
  exact (Algebra.IsIntegral.isIntegral _).map Χ

end AICStalk


open AICStalk in
attribute [local instance] Algebra.TensorProduct.rightAlgebra in
theorem isField_aic_tensor_fractionRing_of_strictlyHenselian :
    ∀ (A O : Type) [CommRing A] [IsDomain A] [CommRing O] [Algebra A O], GlobalTheory.EtC.AIC A →
      GlobalTheory.EtC.SH O → GlobalTheory.EtC.IndEt A O →
      IsField (O ⊗[A] FractionRing A) ∧ GlobalTheory.EtC.AIC (O ⊗[A] FractionRing A) := by
  intro A O _ _ _ _ hA hO h
  haveI := isIntegrallyClosed_of_aic hA
  obtain ⟨hH, -⟩ := hO
  haveI := hH
  haveI := isDomain_of_indEt h
  haveI : IsAlgClosed (FractionRing A) := GlobalTheory.T.isAlgClosed_fractionRing_of_monic_polynomials_have_roots A hA
  haveI : IsLocalization (Algebra.algebraMapSubmonoid O (nonZeroDivisors A))
      (O ⊗[A] FractionRing A) := by
    rw [Algebra.isLocalization_iff_isPushout (nonZeroDivisors A) (FractionRing A)]
    infer_instance
  have hinj := algebraMap_injective_of_indEt h
  haveI : IsDomain (O ⊗[A] FractionRing A) :=
    IsLocalization.isDomain_of_le_nonZeroDivisors (M := Algebra.algebraMapSubmonoid O (nonZeroDivisors A)) (O ⊗[A] FractionRing A) (by
      rintro _ ⟨a, ha, rfl⟩
      exact mem_nonZeroDivisors_of_ne_zero ((map_ne_zero_iff _ hinj).mpr (nonZeroDivisors.ne_zero ha)))
  have hall : ∀ x : O ⊗[A] FractionRing A, IsIntegral (FractionRing A) x := by
    intro x
    induction x using TensorProduct.induction_on with
    | zero => exact isIntegral_zero
    | tmul o k =>
      have : o ⊗ₜ[A] k = (o ⊗ₜ[A] (1 : FractionRing A)) * algebraMap (FractionRing A) _ k := by
        rw [show algebraMap (FractionRing A) (O ⊗[A] FractionRing A) k = 1 ⊗ₜ k from rfl,
          Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]
      rw [this]
      exact (isIntegral_tmul_one h o).mul isIntegral_algebraMap
    | add x y hx hy => exact hx.add hy
  haveI : Algebra.IsIntegral (FractionRing A) (O ⊗[A] FractionRing A) := ⟨hall⟩
  let e := RingEquiv.ofBijective _
    (IsAlgClosed.algebraMap_bijective_of_isIntegral (k := FractionRing A) (K := O ⊗[A] FractionRing A))
  exact ⟨MulEquiv.isField (Field.toIsField (FractionRing A)) e.symm.toMulEquiv,
    aic_of_ringEquiv e (aic_of_isAlgClosed _)⟩

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IwahoriRegularSplit
section
open Polynomial ValuativeRel

namespace GlobalTheory.IwahoriRegular

theorem regular_split : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (N : ℕ) (ϖ : kˣ),
  ValuativeRel.valuation k (ϖ : k) = ValuativeRel.uniformizer k →
  ∀ ν : Fin N → ℤ, StrictAnti ν → ∀ x ∈ GlobalTheory.SmGL.iwahori k (Fin N), ∀ y ∈ GlobalTheory.SmGL.iwahori k (Fin N),
    let g := x * GlobalTheory.GLDoubling.torusElt k (Fin N) ϖ ν * y
    (g : Matrix (Fin N) (Fin N) k).charpoly.Separable ∧ (g : Matrix (Fin N) (Fin N) k).charpoly.Splits := by
  intro k _ _ _ _ N ϖ hϖ ν hν x hx y hy
  letI := IsTopologicalAddGroup.rightUniformSpace k
  haveI := isUniformAddGroup_of_addCommGroup (G := k)
  have hlt : valuation k (ϖ : k) < 1 := hϖ ▸ uniformizer_lt_one
  let w : 𝒪[k] := ⟨ϖ, hlt.le⟩
  have hw : Irreducible w := by
    rw [IsDiscreteValuationRing.irreducible_iff_uniformizer]
    ext z
    rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff, Valuation.Integer.not_isUnit_iff_valuation_lt_one,
      Ideal.mem_span_singleton, (Valuation.integer.integers (valuation k)).dvd_iff_le, ← le_uniformizer_iff, ← hϖ]
    rfl
  obtain ⟨x', hx', rfl⟩ := hx
  obtain ⟨y', hy', rfl⟩ := hy
  have low : ∀ h : GL (Fin N) 𝒪[k], h ∈ (GlobalTheory.SmGL.borel 𝓀[k] (Fin N)).comap
      (Matrix.GeneralLinearGroup.map (n := Fin N) (IsLocalRing.residue 𝒪[k])) →
      ∀ i j, j < i → (h : Matrix (Fin N) (Fin N) 𝒪[k]) i j ∈ IsLocalRing.maximalIdeal 𝒪[k] := by
    intro h hh i j hij
    have := (GlobalTheory.SmGL.mem_borel _).1 hh i j hij
    exact (IsLocalRing.residue_eq_zero_iff _).1 this
  obtain ⟨r, hr, hchar⟩ := GlobalTheory.IwahoriRoots.iwahori_roots 𝒪[k] k w hw N ν hν x' y' (low x' hx') (low y' hy')
  have hinj : Function.Injective r := fun i j h => hν.injective (by rw [← (hr i).2, ← (hr j).2, h])
  have e : ((Matrix.GeneralLinearGroup.map (algebraMap 𝒪[k] k) x' * GlobalTheory.GLDoubling.torusElt k (Fin N) ϖ ν *
      Matrix.GeneralLinearGroup.map (algebraMap 𝒪[k] k) y' : GL (Fin N) k) : Matrix (Fin N) (Fin N) k) =
      (x' : Matrix (Fin N) (Fin N) 𝒪[k]).map (algebraMap 𝒪[k] k) *
        Matrix.diagonal (fun i => algebraMap 𝒪[k] k w ^ ν i) *
        (y' : Matrix (Fin N) (Fin N) 𝒪[k]).map (algebraMap 𝒪[k] k) := by
    rw [Units.val_mul, Units.val_mul, GlobalTheory.GLDoubling.val_torusElt]
    rfl
  show Separable (Matrix.charpoly _) ∧ Splits (Matrix.charpoly _)
  rw [e, hchar]
  exact ⟨separable_prod_X_sub_C_iff.2 hinj, Polynomial.Splits.prod fun i _ => Polynomial.Splits.X_sub_C _⟩

end GlobalTheory.IwahoriRegular
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.KummerLiftedCocycleImageEqPicardClass
section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC GlobalTheory.EtC.KumPic

set_option backward.isDefEq.respectTransparency false

noncomputable section
namespace GlobalTheory.EtC.KumPic.PostVal

theorem ev_comp_ofHom {E : Spc} {I J : Cx ℤ} {n : ℤ} (α : Cochain ((chains ℤ).obj E) I n) (m : I ⟶ J)
    (p : ℕ) (s : ℤ) (h : -(p : ℤ) + n = s) (U : Scheme.{0}) (x : Sx E p U) :
    ev (α.comp (Cochain.ofHom m) (add_zero n)) p s h U x = Sec.map (m.f s) (ev α p s h U x) := by
  unfold ev
  rw [Cochain.comp_zero_cochain_v, Cochain.ofHom_v]
  rfl

theorem sglι_resAug (C : Shv ℤ) : sglι C ≫ (resAug C).f 0 = resι ℤ C := rfl

theorem resι_resMap {C G : Shv ℤ} (φ : C ⟶ G) : resι ℤ C ≫ (resMap ℤ φ).f 0 = φ ≫ resι ℤ G := by
  unfold resι resMap res
  rw [InjectiveResolution.ι'_f_zero, InjectiveResolution.ι'_f_zero,
    HomologicalComplex.extendMap_f _ ComplexShape.embeddingUpNat (i := 0) (i' := 0) (by simp)]
  simp [InjectiveResolution.cochainComplexXIso]

theorem post_eq_picClass (C : Shv ℤ) (qb : C ⟶ Gm) (E : Spc) (L : E ⟶ ofCat (glCat 1))
    (a : Cocycle ((chains ℤ).obj E) (sgl C) 1)
    (ha : ∀ (U : Scheme.{0}) (x : Sx E 1 U), ∃ c : Sec C U, Sec.map qb c = unitSec (lineUnit L x) ∧
      ev a.1 1 0 (by simp) U x = Sec.map (sglι C) c) :
    HK.post ℤ _ qb 1 (CohomologyClass.mk (zcomp a (Cocycle.ofHom (resAug C)) (add_zero 1))) = picClass L := by
  let β := zcomp (zcomp a (Cocycle.ofHom (resAug C)) (add_zero 1))
    (Cocycle.ofHom (resMap ℤ qb)) (add_zero 1)
  change CohomologyClass.mk β = picClass L
  have hβ₀ (U : Scheme.{0}) (x : Sx E 0 U) : ev β.1 0 1 (by simp) U x = 0 := by
    change ev ((a.1.comp (Cochain.ofHom (resAug C)) (add_zero 1)).comp
      (Cochain.ofHom (resMap ℤ qb)) (add_zero 1))
      0 1 _ U x = 0
    rw [ev_comp_ofHom, ev_comp_ofHom,
      GlobalTheory.EtC.PicSpec.sec_eq_zero (HomologicalComplex.isZero_single_obj_X _ _ _ _ (by decide)) (ev a.1 0 1 _ U x),
      GlobalTheory.EtC.PicSpec.sec_map_zero, GlobalTheory.EtC.PicSpec.sec_map_zero]
  have hβ₁ (U : Scheme.{0}) (x : Sx E 1 U) :
      ev β.1 1 0 (by simp) U x = Sec.map (resι ℤ Gm) (unitSec (lineUnit L x)) := by
    obtain ⟨c, hc, hv⟩ := ha U x
    change ev ((a.1.comp (Cochain.ofHom (resAug C)) (add_zero 1)).comp
      (Cochain.ofHom (resMap ℤ qb)) (add_zero 1))
      1 0 _ U x = _
    rw [ev_comp_ofHom, ev_comp_ofHom, hv, GlobalTheory.EtC.PicSpec.sec_map_comp, GlobalTheory.EtC.PicSpec.sec_map_comp, ← hc,
      GlobalTheory.EtC.PicSpec.sec_map_comp, ← Category.assoc, sglι_resAug, resι_resMap]
  let P (c : H ℤ E Gm 1) : Prop :=
    ∃ γ : Cocycle ((chains ℤ).obj E) (res ℤ Gm) 1, CohomologyClass.mk γ = c ∧
      (∀ (U : Scheme.{0}) (x : Sx E 0 U), ev γ.1 0 1 (by simp) U x = 0) ∧
      ∀ (U : Scheme.{0}) (x : Sx E 1 U),
        ev γ.1 1 0 (by simp) U x = Sec.map (resι ℤ Gm) (unitSec (lineUnit L x))
  have hspec : P (picClass L) := by
    change P (pick P)
    exact pick_spec ⟨_, β, rfl, hβ₀, hβ₁⟩
  obtain ⟨γ, hγ, hγ₀, hγ₁⟩ := hspec
  have hEq : β = γ := by
    refine Cocycle.ext (CupSpec.ev_ext β.1 γ.1 fun p s h U x => ?_)
    match p with
    | 0 =>
      obtain rfl : s = 1 := by omega
      exact (hβ₀ U x).trans (hγ₀ U x).symm
    | 1 =>
      obtain rfl : s = 0 := by omega
      exact (hβ₁ U x).trans (hγ₁ U x).symm
    | p + 2 =>
      have hZ := GlobalTheory.EtC.PicSpec.res_isZero Gm s (by omega)
      exact (GlobalTheory.EtC.PicSpec.sec_eq_zero hZ _).trans
        (GlobalTheory.EtC.PicSpec.sec_eq_zero hZ _).symm
  rw [hEq, hγ]

end GlobalTheory.EtC.KumPic.PostVal
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LaurentCechNerveLevelSpecTensorPowerStatement
section
open CategoryTheory Limits AlgebraicGeometry Opposite Simplicial GlobalTheory.EtC GlobalTheory.EtC.GmStep
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.laurentCechNerve_level_spec_tensorPower : ∀ (A A' : Type) [CommRing A] [CommRing A'] [Algebra A A'] (k : ℕ),
  ∃ (e0 : yoneda.obj (Spec (CommRingCat.of (PiTensorProduct A (fun _ : Fin (k + 1) => A')))) ≅ (cech (baseHom A A')).obj (op ⦋k⦌))
    (e : yoneda.obj (Spec (CommRingCat.of (LaurentPolynomial (PiTensorProduct A (fun _ : Fin (k + 1) => A'))))) ≅
      (cech (laurentHom A A')).obj (op ⦋k⦌)),
    e.hom ≫ (cechC A A').app (op ⦋k⦌) =
      yoneda.map (Spec.map (CommRingCat.ofHom (LaurentPolynomial.C : PiTensorProduct A (fun _ : Fin (k + 1) => A') →+*
        LaurentPolynomial (PiTensorProduct A (fun _ : Fin (k + 1) => A'))))) ≫ e0.hom ∧
    e.hom ≫ (cechAug (laurentHom A A')).app (op ⦋k⦌) =
      yoneda.map (Spec.map (CommRingCat.ofHom (laurentMap (algebraMap A (PiTensorProduct A (fun _ : Fin (k + 1) => A')))))) := by
  first | (exact @GlobalTheory.EtC.GmStep.LevelIso.level_iso) | (exact GlobalTheory.EtC.GmStep.LevelIso.level_iso) | (intros; apply GlobalTheory.EtC.GmStep.LevelIso.level_iso  <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LaurentPiBijective
section
open GlobalTheory.EtC.GmStep
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.laurent_pi_bijective : ∀ (n : ℕ) (B : Fin n → Type) [∀ j, CommRing (B j)], Function.Bijective (Pi.ringHom (fun j => laurentMap (Pi.evalRingHom B j)) : LaurentPolynomial (∀ j, B j) →+* ∀ j, LaurentPolynomial (B j)) := by
  first | (exact @GlobalTheory.EtC.GmStep.laurentPi_bijective) | (exact GlobalTheory.EtC.GmStep.laurentPi_bijective) | (intros; apply GlobalTheory.EtC.GmStep.laurentPi_bijective  <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LeftSmoothingProdExpSmoothCommuteStatement
section
open MeasureTheory GroundTheory.Automorphic
open scoped ContDiff
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.leftSmoothing_prodExp_smooth_commute : ∀ (𝔸 : Type) [NormedRing 𝔸] [NormedAlgebra ℝ 𝔸] [CompleteSpace 𝔸] [FiniteDimensional ℝ 𝔸] (G : Subgroup 𝔸ˣ) (𝔤 : Submodule ℝ 𝔸) (h : IsExpLieAlgebra G 𝔤) (n : ℕ) (X : Fin n → 𝔤) (κ : (Fin n → ℝ) → ℂ), Continuous κ → HasCompactSupport κ → ∀ f : h.smoothFuns (F := ℂ), ∃ v : h.smoothFuns (F := ℂ), (∀ y, (v : G → ℂ) y = ∫ t, κ t * (f : G → ℂ) (h.prodExp X t * y)) ∧ ∀ T ∈ Algebra.adjoin ℂ (Set.range (h.rightDerivEnd (F := ℂ))), ∀ y, (T v : G → ℂ) y = ∫ t, κ t * (T f : G → ℂ) (h.prodExp X t * y) := by
  first | exact @GlobalTheory.leftSmoothing_prodExp | exact GlobalTheory.leftSmoothing_prodExp | (intros; apply GlobalTheory.leftSmoothing_prodExp <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LeftTranslateSmoothCommuteLeftInvariantOpsStatement
section
open ZetaZeros.D.EllReg GlobalTheory.HCA MeasureTheory GroundTheory.Automorphic
open scoped ContDiff
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.leftTranslate_smooth_commute_leftInvariantOps : ∀ (𝔸 : Type) [NormedRing 𝔸] [NormedAlgebra ℝ 𝔸] [CompleteSpace 𝔸] [FiniteDimensional ℝ 𝔸] (G : Subgroup 𝔸ˣ) (𝔤 : Submodule ℝ 𝔸) (h : IsExpLieAlgebra G 𝔤) (f : h.smoothFuns (F := ℂ)) (g : G), ∃ f' : h.smoothFuns (F := ℂ), (∀ y, (f' : G → ℂ) y = (f : G → ℂ) (g * y)) ∧ ∀ T ∈ Algebra.adjoin ℂ (Set.range (h.rightDerivEnd (F := ℂ))), ∀ y, (T f' : G → ℂ) y = (T f : G → ℂ) (g * y) := by
  first | exact @GlobalTheory.leftTranslate_smooth_commute | exact GlobalTheory.leftTranslate_smooth_commute | (intros; apply GlobalTheory.leftTranslate_smooth_commute <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LevelwiseEquivalenceIsEquivalence
section
noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

namespace GlobalTheory.EtC.LevelCmp

variable {R : Type} [CommRing R]

theorem cpull_comp_fun {K L M : Cx R} (a : K ⟶ L) (b : L ⟶ M) (I : Cx R) (n : ℤ) :
    ⇑(cpull (a ≫ b) I n) = ⇑(cpull a I n) ∘ ⇑(cpull b I n) :=
  funext fun x => (GlobalTheory.T.hypercohomologyPullbackPushforward_functorial R).2.1 a b I n x

theorem cpull_bij_of_heq {K L : Cx R} (e : HomotopyEquiv K L) (I : Cx R) (n : ℤ) :
    Function.Bijective (cpull e.hom I n) := by
  obtain ⟨hid, -, -, -, hhom⟩ := GlobalTheory.T.hypercohomologyPullbackPushforward_functorial R
  have h1 := (hhom _ _ ⟨e.homotopyHomInvId⟩ I n).1
  have h2 := (hhom _ _ ⟨e.homotopyInvHomId⟩ I n).1
  have l1 : ∀ y, cpull e.hom I n (cpull e.inv I n y) = y := fun y => by
    rw [← (GlobalTheory.T.hypercohomologyPullbackPushforward_functorial R).2.1 e.hom e.inv I n y, h1]; exact (hid _ _ _ _).1
  have l2 : ∀ x, cpull e.inv I n (cpull e.hom I n x) = x := fun x => by
    rw [← (GlobalTheory.T.hypercohomologyPullbackPushforward_functorial R).2.1 e.inv e.hom I n x, h2]; exact (hid _ _ _ _).1
  exact ⟨Function.LeftInverse.injective l2, Function.RightInverse.surjective l1⟩

theorem cpull_bij_of_iso {K L : Cx R} (f : K ⟶ L) [IsIso f] (I : Cx R) (n : ℤ) :
    Function.Bijective (cpull f I n) :=
  cpull_bij_of_heq (HomotopyEquiv.ofIso (asIso f)) I n

end GlobalTheory.EtC.LevelCmp


open GlobalTheory.EtC.LevelCmp in
theorem GlobalTheory.EtC.levelwise_eqv : GlobalTheory.EtC.A3 := by
  intro R _ E E' f F hlev
  obtain ⟨hle, hnat, -⟩ := GlobalTheory.T.chains_map_and_d_eq_sum_neg_one_pow_smul_delta R
  obtain ⟨e, -, he⟩ := GlobalTheory.T.exists_natural_homotopyEquiv_chains_constant_presheaf R
  obtain ⟨-, hinj, hge, -⟩ := _root_.GlobalTheory.EtC.ResBasic.res_basic R F
  haveI := hle E; haveI := hle E'; haveI := hge
  intro n
  refine GlobalTheory.T.hypercohomologyPullback_bijective_of_termwise_bijective R (res R F) hinj ((chains R).map f) ?_ n
  intro p k
  rcases le_or_gt p 0 with hp | hp
  · obtain ⟨m, rfl⟩ : ∃ m : ℕ, p = -(m : ℤ) := ⟨(-p).toNat, by omega⟩
    set φ := f.app (op (SimplexCategory.mk m))

    have hfree : Function.Bijective
        (cpull ((CochainComplex.singleFunctor (Shv R) 0).map ((free R).map φ)) (res R F) k) := by
      have hc := congrArg (fun g => ⇑(cpull g (res R F) k)) (he φ)
      simp only [cpull_comp_fun] at hc
      have hr : Function.Bijective (⇑(cpull (e _).hom (res R F) k) ∘
          ⇑(cpull ((chains R).map (disc.map φ)) (res R F) k)) :=
        (cpull_bij_of_heq (e _) _ k).comp (hlev (op (SimplexCategory.mk m)) k)
      rw [hc] at hr
      exact (Function.Bijective.of_comp_iff _ (cpull_bij_of_heq (e _) _ k)).1 hr
    have hg : ((chains R).map f).f (-(m : ℤ)) =
        (chainsXIso R E m).hom ≫ (free R).map φ ≫ (chainsXIso R E' m).inv := by
      rw [← Category.assoc, ← hnat f m]; simp
    rw [hg, Functor.map_comp, Functor.map_comp, cpull_comp_fun, cpull_comp_fun]
    exact (cpull_bij_of_iso _ _ k).comp (hfree.comp (cpull_bij_of_iso _ _ k))
  · have h1 : IsZero (((chains R).obj E).X p) := CochainComplex.isZero_of_isStrictlyLE _ 0 p hp
    have h2 : IsZero (((chains R).obj E').X p) := CochainComplex.isZero_of_isStrictlyLE _ 0 p hp
    haveI : IsIso (((chains R).map f).f p) := ⟨⟨0, h1.eq_of_src _ _, h2.eq_of_src _ _⟩⟩
    exact cpull_bij_of_iso _ _ k
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LiftOfReducedOfSupportStatement
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_lift_of_isReduced_of_mem_ker_support : ∀ {X Y T : Scheme.{0}} (i : X ⟶ Y) [IsClosedImmersion i] [IsReduced T] (g : T ⟶ Y), (∀ t, g t ∈ i.ker.support) → ∃ h : T ⟶ X, h ≫ i = g := by
  first | exact @GlobalTheory.lift_of_reduced_of_support | exact GlobalTheory.lift_of_reduced_of_support | (intros; apply GlobalTheory.lift_of_reduced_of_support <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LintegralSqSiegelParabolicOperatorEqStatement
section
open MeasureTheory Matrix GlobalTheory.KSp GlobalTheory.SplitUnitary
open GlobalTheory.WeilM (UG IsQuad IsHerm ResEtaPow)
open GlobalTheory.SplitWeil (SB nabs)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lintegral_sq_siegelParabolicOperator_eq : ∀ (F : Type) [Field F] [CharZero F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] (E : Type) [Field E] [Algebra F E] [TopologicalSpace E] [IsModuleTopology F E] (c : E →ₐ[F] E) (δ : E) (hE : IsQuad c δ) (α : Type) [Fintype α] [DecidableEq α] (ν : Type) [Fintype ν] [DecidableEq ν] (Q : Matrix α α E) (_ : IsHerm c Q) (ψ : AddChar F ℂ) (hψ : Continuous ψ) (_ : ∀ t, ‖ψ t‖ = 1) (_ : ψ ≠ 1) (χ : Eˣ →* Circle) (_ : Continuous χ) (_ : ResEtaPow (R := F) ⊥ χ (Fintype.card α)) [MeasurableSpace (Matrix α ν E)] [BorelSpace (Matrix α ν E)] (μ : Measure (Matrix α ν E)) [μ.IsAddHaarMeasure] (p : UG c (stdJ ν E)), p ∈ sieg c ν → ∀ φ : Matrix α ν E → ℂ, ∫⁻ x, ‖parFun c ψ χ Q (mat c p) φ x‖ₑ ^ 2 ∂μ = ∫⁻ x, ‖φ x‖ₑ ^ 2 ∂μ := by
  first | exact @GlobalTheory.KSp.parFun_lintegral_sq | exact GlobalTheory.KSp.parFun_lintegral_sq | (intros; apply GlobalTheory.KSp.parFun_lintegral_sq <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocallyInjectiveOfIsoOnFiniteTypeRingsStatement
section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex TensorProduct GlobalTheory.EtC
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.locallyInjective_of_iso_on_finiteType_rings : ∀ (N M : CommRingCat.{0} ⥤ AbCx) (ε : N ⟶ M) (F0 : CommRingCat.{0} ⥤ AddCommGrpCat.{1}) (ι : F0 ⟶ term M 0), PreservesFilteredColimitsOfSize.{0, 0} F0 → (∀ A, Function.Injective (ι.app A) ∧ ∀ z : (M.obj A).X 0, (M.obj A).d 0 (0 + 1) z = 0 ↔ ∃ x, ι.app A x = z) → (∀ n : ℤ, n < 0 → ∀ A, IsZero ((M.obj A).X n)) → (∀ n : ℤ, 0 < n → ∀ (A : CommRingCat.{0}) (z : (M.obj A).X n), (M.obj A).d n (n + 1) z = 0 → ∃ (B : CommRingCat.{0}) (g : A ⟶ B), EtFF g ∧ ∃ y : (M.obj B).X (n - 1), (M.obj B).d (n - 1) n y = (M.map g).f n z) → PreservesFilteredColimitsOfSize.{0, 0} N → (∀ A : CommRingCat.{0}, Algebra.FiniteType ℤ A → IsIso (ε.app A)) → LocInj EtFF ε := by
  first | (exact @GlobalTheory.EtC.FiniteTypeApprox.locInj_of_finiteType) | (exact GlobalTheory.EtC.FiniteTypeApprox.locInj_of_finiteType) | (intros; apply GlobalTheory.EtC.FiniteTypeApprox.locInj_of_finiteType  <;> assumption)
end

