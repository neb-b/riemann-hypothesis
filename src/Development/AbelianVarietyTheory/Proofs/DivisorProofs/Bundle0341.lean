module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0314
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0018
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ComapMaximalIdealEqOrigin
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0007
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0006
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0305
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0327
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0020
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0175
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0218
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0230
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0272
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0285
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0297
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0134
public import Development.AbelianVarietyTheory.Definitions.Divisors.IndEtOfForallFinset
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleSheafOfRingFunctorSectionsLocallyBijective
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleSpaceChainsMayerVietorisShortExact

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleHomotopyInvariantTwistsOfRingEquiv
section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC
open scoped TensorProduct

namespace GlobalTheory.EtC.HInvIso

theorem spMap_comp' {A B C : Type} [CommRing A] [CommRing B] [CommRing C] (f : A →+* B) (g : B →+* C) :
    spMap (g.comp f) = spMap g ≫ spMap f := by
  simp only [spMap, CommRingCat.ofHom_comp, Spec.map_comp, Functor.map_comp]

theorem spMap_id' (A : Type) [CommRing A] : spMap (RingHom.id A) = 𝟙 _ := by
  simp only [spMap, CommRingCat.ofHom_id, Spec.map_id]
  exact CategoryTheory.Functor.map_id _ _

theorem pull_spMap_bij {R : Type} [CommRing R] {A B : Type} [CommRing A] [CommRing B] (e : A ≃+* B) (F : Shv R) (n : ℤ) :
    Function.Bijective (pull R (spMap (e : A →+* B)) F n) := by
  have h1 : ∀ x, pull R (spMap (e : A →+* B)) F n (pull R (spMap (e.symm : B →+* A)) F n x) = x := by
    intro x
    rw [← pull_comp, ← spMap_comp']
    have : (e : A →+* B).comp (e.symm : B →+* A) = RingHom.id B := by ext a; simp
    rw [this, spMap_id', pull_id]
  have h2 : ∀ x, pull R (spMap (e.symm : B →+* A)) F n (pull R (spMap (e : A →+* B)) F n x) = x := by
    intro x
    rw [← pull_comp, ← spMap_comp']
    have : (e.symm : B →+* A).comp (e : A →+* B) = RingHom.id A := by ext a; simp
    rw [this, spMap_id', pull_id]
  exact ⟨Function.LeftInverse.injective h2, Function.RightInverse.surjective h1⟩

end GlobalTheory.EtC.HInvIso

namespace GlobalTheory.EtC


open HInvIso in
theorem hInv_of_ringEquiv : ∀ (q : ℕ) [NeZero q] (A B : Type) [CommRing A] [CommRing B], (A ≃+* B) → HInv q A → HInv q B := by
  intro q _ A B _ _ e hA i n
  have hsq : (Polynomial.C : B →+* Polynomial B).comp (e : A →+* B) =
      ((Polynomial.mapEquiv e : Polynomial A ≃+* Polynomial B) : Polynomial A →+* Polynomial B).comp Polynomial.C := by
    ext a; simp
  have hpull : ∀ x, pull (ZMod q) (spMap (Polynomial.C : B →+* Polynomial B)) (tw q i) n
      (pull (ZMod q) (spMap (e : A →+* B)) (tw q i) n x) =
      pull (ZMod q) (spMap ((Polynomial.mapEquiv e : Polynomial A ≃+* Polynomial B) : Polynomial A →+* Polynomial B)) (tw q i) n
        (pull (ZMod q) (spMap (Polynomial.C : A →+* Polynomial A)) (tw q i) n x) := by
    intro x
    rw [← pull_comp, ← pull_comp, ← spMap_comp', ← spMap_comp', hsq]
  have hc : Function.Bijective ((pull (ZMod q) (spMap (Polynomial.C : B →+* Polynomial B)) (tw q i) n) ∘
      (pull (ZMod q) (spMap (e : A →+* B)) (tw q i) n)) := by
    have : ((pull (ZMod q) (spMap (Polynomial.C : B →+* Polynomial B)) (tw q i) n) ∘
      (pull (ZMod q) (spMap (e : A →+* B)) (tw q i) n)) =
      (pull (ZMod q) (spMap ((Polynomial.mapEquiv e : Polynomial A ≃+* Polynomial B) : Polynomial A →+* Polynomial B)) (tw q i) n) ∘
        (pull (ZMod q) (spMap (Polynomial.C : A →+* Polynomial A)) (tw q i) n) := funext hpull
    rw [this]
    exact (pull_spMap_bij _ _ n).comp (hA i n)
  exact (Function.Bijective.of_comp_iff _ (pull_spMap_bij e _ n)).1 hc

end GlobalTheory.EtC
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleHomotopyInvariantTwistsOfSubsingleton
section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC
open scoped TensorProduct

namespace GlobalTheory.EtC

theorem eqv_of_isIso {R : Type} [CommRing R] {E E' : Spc} (f : E ⟶ E') [IsIso f] (F : Shv R) :
    Eqv R f F := by
  intro n
  refine Function.bijective_iff_has_inverse.mpr ⟨pull R (inv f) F n, ?_, ?_⟩
  · intro x
    rw [← pull_comp, IsIso.inv_hom_id, pull_id]
  · intro x
    rw [← pull_comp, IsIso.hom_inv_id, pull_id]

theorem hInv_of_subsingleton : ∀ (q : ℕ) [NeZero q] (A : Type) [CommRing A], Subsingleton A → HInv q A := by
  intro q _ A _ hA i
  have hb : Function.Bijective (Polynomial.C : A →+* Polynomial A) :=
    ⟨fun x y _ => Subsingleton.elim x y, fun y => ⟨0, Subsingleton.elim _ _⟩⟩
  let e : A ≃+* Polynomial A := RingEquiv.ofBijective _ hb
  haveI : IsIso (CommRingCat.ofHom (Polynomial.C : A →+* Polynomial A)) :=
    (RingEquiv.toCommRingCatIso e).isIso_hom
  haveI : IsIso (spMap (Polynomial.C : A →+* Polynomial A)) := by
    unfold spMap; infer_instance
  exact eqv_of_isIso _ _

end GlobalTheory.EtC
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleIntegrallyClosedInLocalization
section
open IsLocalRing Polynomial
open scoped TensorProduct
open GlobalTheory.LocAcyc GlobalTheory.KeyOriginNoeth GlobalTheory.KeyOriginBC

namespace GlobalTheory.EtaleNormalLoc

theorem isIntegrallyClosedIn_localization (S : Type) [CommRing S] [IsDomain S]
    [IsIntegrallyClosed S] (M : Submonoid S) (hM : M ≤ nonZeroDivisors S) :
    IsIntegrallyClosedIn S (Localization M) := by
  let K := FractionRing S
  letI : Algebra (Localization M) K :=
    IsLocalization.localizationAlgebraOfSubmonoidLe (Localization M) K M _ hM
  haveI : IsScalarTower S (Localization M) K :=
    IsLocalization.localization_isScalarTower_of_submonoid_le (Localization M) K M _ hM
  haveI : IsFractionRing (Localization M) K :=
    IsFractionRing.isFractionRing_of_isLocalization M (Localization M) K hM
  haveI : IsDomain (Localization M) := IsLocalization.isDomain_localization hM
  have hK : Function.Injective (algebraMap (Localization M) K) := IsFractionRing.injective _ _
  refine isIntegrallyClosedIn_iff.mpr ⟨fun x y hxy ↦ ?_, fun {x} hx ↦ ?_⟩
  · apply IsFractionRing.injective S K
    rw [IsScalarTower.algebraMap_apply S (Localization M) K, hxy, ← IsScalarTower.algebraMap_apply]
  · obtain ⟨y, hy⟩ := IsIntegrallyClosed.algebraMap_eq_of_integral (hx.algebraMap (B := K))
    exact ⟨y, hK (by rw [← hy, IsScalarTower.algebraMap_apply S (Localization M) K])⟩

theorem etale_integrallyClosed_localization : ∀ (S E : Type) [CommRing S] [IsDomain S] [IsIntegrallyClosed S]
    [CommRing E] [Algebra S E] [Algebra.Etale S E] (M : Submonoid S), M ≤ nonZeroDivisors S →
    Function.Injective (algebraMap E (Localization (Algebra.algebraMapSubmonoid E M))) ∧
    ∀ x : Localization (Algebra.algebraMapSubmonoid E M), IsIntegral S x →
      x ∈ (algebraMap E (Localization (Algebra.algebraMapSubmonoid E M))).range := by
  intro S E _ _ _ _ _ _ M hM
  have hle : Algebra.algebraMapSubmonoid E M ≤ nonZeroDivisors E := by
    rintro _ ⟨m, hm, rfl⟩
    have hreg : IsSMulRegular E m := Module.Flat.isSMulRegular_of_nonZeroDivisors (hM hm)
    refine mem_nonZeroDivisors_iff.mpr ⟨fun x hx ↦ hreg ?_, fun x hx ↦ hreg ?_⟩
    · show m • x = m • (0 : E)
      rw [smul_zero, Algebra.smul_def]
      exact hx
    · show m • x = m • (0 : E)
      rw [smul_zero, Algebra.smul_def, mul_comm]
      exact hx
  refine ⟨IsLocalization.injective _ hle, fun x hx ↦ ?_⟩
  let SM := Localization M
  let T := E ⊗[S] SM
  letI : Algebra SM T := Algebra.TensorProduct.rightAlgebra
  haveI : IsScalarTower S SM T := inferInstance
  haveI : Algebra.IsPushout S E SM T := inferInstance
  haveI : IsLocalization (Algebra.algebraMapSubmonoid E M) T :=
    (Algebra.isLocalization_iff_isPushout M SM).2 (Algebra.IsPushout.symm inferInstance)
  let e : T ≃ₐ[E] Localization (Algebra.algebraMapSubmonoid E M) :=
    IsLocalization.algEquiv (Algebra.algebraMapSubmonoid E M) T _
  have hic := isIntegrallyClosedIn_localization S M hM
  have htS : IsIntegral S (e.symm x) := hx.map (e.symm.toAlgHom.restrictScalars S)
  have htE : IsIntegral E (e.symm x) := htS.tower_top
  obtain ⟨y, hy⟩ := (TensorProduct.toIntegralClosure_bijective_of_smooth
    (R := S) (S := E) (B := SM)).2 ⟨e.symm x, htE⟩
  have hy' : (TensorProduct.toIntegralClosure S E SM y : T) = e.symm x := congrArg Subtype.val hy
  have key : ∀ y : E ⊗[S] integralClosure S SM, ∃ b : E,
      (TensorProduct.toIntegralClosure S E SM y : T) = b ⊗ₜ[S] (1 : SM) := by
    intro y
    induction y with
    | tmul b c =>
      obtain ⟨r, hr⟩ := IsIntegrallyClosedIn.isIntegral_iff.1 c.2
      refine ⟨r • b, ?_⟩
      rw [TensorProduct.smul_tmul, ← Algebra.algebraMap_eq_smul_one, hr]
      rfl
    | add u v hu hv =>
      obtain ⟨a, ha⟩ := hu
      obtain ⟨b, hb⟩ := hv
      exact ⟨a + b, by rw [map_add (f := _), Subalgebra.coe_add, ha, hb, TensorProduct.add_tmul]⟩
  obtain ⟨b, hb⟩ := key y
  refine ⟨b, ?_⟩
  have : e.symm x = algebraMap E T b := by
    rw [← hy', hb]; rfl
  rw [← e.apply_symm_apply x, this, AlgEquiv.commutes]

end GlobalTheory.EtaleNormalLoc
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleLocalPrimitiveRootAndRootsOfUnity
section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

noncomputable section

namespace GlobalTheory.EtC.PrimLoc
open Polynomial

lemma loc_mono {U : Scheme.{0}} {P Q : ∀ V : Scheme.{0}, (V ⟶ U) → Prop}
    (h : ∀ V g, P V g → Q V g) (hP : Loc U P) : Loc U Q := by
  obtain ⟨S, hS, h1⟩ := hP
  exact ⟨S, hS, fun V g hg => h V g (h1 V g hg)⟩

lemma appTop_comp {V W U : Scheme.{0}} (g : V ⟶ U) (k : W ⟶ V) (a : Γ(U, ⊤)) :
    (k ≫ g).appTop.hom a = k.appTop.hom (g.appTop.hom a) := by
  rw [Scheme.Hom.comp_appTop]; rfl

lemma isUnit_prod' {R : Type*} [CommRing R] (S : Finset ℕ) (f : ℕ → R) (h : ∀ a ∈ S, IsUnit (f a)) :
    IsUnit (∏ a ∈ S, f a) := by
  exact IsUnit.prod_iff.mpr h

lemma loc_of_prod_eq_zero {U : Scheme.{0}} (y : Γ(U, ⊤)) (z : ℕ → Γ(U, ⊤)) (S : Finset ℕ)
    (hprod : ∏ a ∈ S, (y - z a) = 0) (hu : ∀ a ∈ S, ∀ b ∈ S, a ≠ b → IsUnit (z a - z b)) :
    Loc U fun _ g => ∃ a ∈ S, g.appTop.hom y = g.appTop.hom (z a) := by
  classical
  rw [loc_iff_etale_affine_points U _ (by
    rintro V W g k ⟨a, ha, h⟩
    exact ⟨a, ha, by rw [appTop_comp, appTop_comp, h]⟩)]
  intro x
  let γ := (U.presheaf.germ ⊤ x trivial).hom
  have hex : ∃ a ∈ S, ¬ IsUnit (γ (y - z a)) := by
    by_contra hc
    push_neg at hc
    have h1 : IsUnit (γ (∏ a ∈ S, (y - z a))) := by
      rw [map_prod]; exact isUnit_prod' S _ hc
    rw [hprod, map_zero] at h1
    exact not_isUnit_zero h1
  obtain ⟨a0, ha0, hna⟩ := hex
  set s := ∏ b ∈ S.erase a0, (y - z b) with hs
  have hsu : IsUnit (γ s) := by
    rw [hs, map_prod]
    apply isUnit_prod'
    intro b hb
    obtain ⟨hba, hbS⟩ := Finset.mem_erase.1 hb
    by_contra hnb
    have hun : IsUnit (γ (z a0 - z b)) := (hu a0 ha0 b hbS (Ne.symm hba)).map γ
    have e : γ (z a0 - z b) = γ (y - z b) + -(γ (y - z a0)) := by
      rw [← map_neg, ← map_add (f := _)]; congr 1; ring
    rw [e] at hun
    exact (IsLocalRing.nonunits_add ((mem_nonunits_iff).2 hnb)
      ((mem_nonunits_iff).2 (fun h => hna (by simpa using h.neg)))) hun
  have hxs : x ∈ U.basicOpen s := (Scheme.mem_basicOpen_top U s x).2 hsu
  let W := U.basicOpen s
  let xW : W.toScheme := ⟨x, hxs⟩
  obtain ⟨w, hw⟩ := W.toScheme.affineCover.covers xW
  refine ⟨_, W.toScheme.affineCover.f (W.toScheme.affineCover.idx xW) ≫ W.ι, inferInstance, inferInstance, ⟨w, ?_⟩, a0, ha0, ?_⟩
  · simp [hw, xW]
  · set k := W.toScheme.affineCover.f (W.toScheme.affineCover.idx xW)
    have hsW : IsUnit (W.ι.appTop.hom s) := by
      rw [Scheme.Opens.ι_appTop]
      have h0 : IsUnit ((U.presheaf.map (homOfLE (U.basicOpen_le s)).op).hom s) := U.toRingedSpace.isUnit_res_basicOpen s
      have hle : W.ι ''ᵁ ⊤ ≤ W := by
        rintro _ ⟨y, -, rfl⟩
        exact y.2
      have e : (homOfLE le_top : W.ι ''ᵁ ⊤ ⟶ ⊤) = homOfLE hle ≫ homOfLE (U.basicOpen_le s) := Subsingleton.elim _ _
      rw [e, op_comp, Functor.map_comp]
      exact h0.map (U.presheaf.map (homOfLE hle).op).hom
    have hk : IsUnit ((k ≫ W.ι).appTop.hom s) := by
      rw [appTop_comp]; exact hsW.map _
    have hm : (y - z a0) * s = 0 := by rw [hs, Finset.mul_prod_erase S (fun b => y - z b) ha0, hprod]
    have h2 := congrArg (k ≫ W.ι).appTop.hom hm
    rw [map_mul, map_zero, hk.mul_left_eq_zero, map_sub, sub_eq_zero] at h2
    exact h2

end GlobalTheory.EtC.PrimLoc

namespace GlobalTheory.EtC.PrimLoc
open Polynomial

lemma specMap_algebraMap_comp_apply_primeSpectrum {U : Scheme.{0}} {A : CommRingCat.{0}} {B : Type} [CommRing B] [Algebra A B] (f : Spec A ⟶ U)
    (z : PrimeSpectrum B) :
    (Spec.map (CommRingCat.ofHom (algebraMap A B)) ≫ f) z = f (PrimeSpectrum.comap (algebraMap A B) z) := rfl

lemma loc_of_alg {U : Scheme.{0}} (P : ∀ V : Scheme.{0}, (V ⟶ U) → Prop)
    (hP : ∀ (V W : Scheme.{0}) (g : V ⟶ U) (k : W ⟶ V), P V g → P W (k ≫ g))
    (h : ∀ (A : CommRingCat.{0}) (f : Spec A ⟶ U), Nontrivial A → ∃ (B : Type) (_ : CommRing B) (_ : Algebra A B),
      Algebra.Etale A B ∧ Function.Surjective (PrimeSpectrum.comap (algebraMap A B)) ∧
      P (Spec (CommRingCat.of B)) (Spec.map (CommRingCat.ofHom (algebraMap A B)) ≫ f)) : Loc U P := by
  rw [loc_iff_etale_affine_points U P hP]
  intro x
  obtain ⟨y, hy⟩ := U.affineOpenCover.covers x
  have hA : Nontrivial (U.affineOpenCover.X (U.affineOpenCover.idx x)) :=
    nontrivial_of_ne 0 1 (fun h => y.2.ne_top ((Ideal.eq_top_iff_one _).2 (h ▸ y.asIdeal.zero_mem)))
  obtain ⟨B, _, _, hE, hS, hPB⟩ := h _ (U.affineOpenCover.f (U.affineOpenCover.idx x)) hA
  obtain ⟨z, hz⟩ := hS y
  haveI : Etale (Spec.map (CommRingCat.ofHom (algebraMap (U.affineOpenCover.X (U.affineOpenCover.idx x)) B))) :=
    HasRingHomProperty.Spec_iff.mpr (RingHom.etale_algebraMap.mpr hE)
  refine ⟨_, _, inferInstance, inferInstance, ⟨z, ?_⟩, hPB⟩
  rw [specMap_algebraMap_comp_apply_primeSpectrum, hz, hy]

lemma adjoinRoot_surj {A : Type} [CommRing A] [Nontrivial A] (f : A[X]) (hf : f.Monic) (hd : f.natDegree ≠ 0) :
    Function.Surjective (PrimeSpectrum.comap (algebraMap A (AdjoinRoot f))) := by
  haveI : Module.Free A (AdjoinRoot f) := Module.Free.of_basis (AdjoinRoot.powerBasis' hf).basis
  haveI : Nontrivial (AdjoinRoot f) := Ideal.Quotient.nontrivial_iff.mpr (by
    rw [Ne, Ideal.span_singleton_eq_top]
    intro h
    exact hd (by rw [hf.isUnit_iff.1 h, natDegree_one]))
  exact PrimeSpectrum.comap_surjective_of_faithfullyFlat

lemma etale_of_unit {A : Type} [CommRing A] (f : A[X]) (hm : f.Monic) (h : IsUnit (AdjoinRoot.mk f (derivative f))) :
    Algebra.Etale A (AdjoinRoot f) := by
  let P : StandardEtalePair A := ⟨f, hm, derivative f, 1, 0, 1, by simp⟩
  exact .of_equiv (P.equivAwayAdjoinRoot.trans
    ((IsLocalization.atUnit _ (Localization.Away (AdjoinRoot.mk f (derivative f))) _
      h).symm.restrictScalars A))

lemma cyc_etale {A : Type} [CommRing A] (q : ℕ) [NeZero q] (hq : IsUnit (q : A)) :
    Algebra.Etale A (AdjoinRoot (cyclotomic q A)) := by
  apply etale_of_unit _ (cyclotomic.monic q A)
  obtain ⟨G, hG⟩ := cyclotomic.dvd_X_pow_sub_one q A
  have hx : AdjoinRoot.root (cyclotomic q A) ^ q = 1 := by
    have := congrArg (AdjoinRoot.mk (cyclotomic q A)) hG
    rw [map_mul, AdjoinRoot.mk_self, zero_mul, map_sub, map_pow, AdjoinRoot.mk_X, map_one, sub_eq_zero] at this
    exact this
  have hd := congrArg (fun p => AdjoinRoot.mk (cyclotomic q A) (derivative p)) hG
  simp only [derivative_mul, derivative_sub, derivative_X_pow, derivative_one, sub_zero, map_add (f := _), map_mul,
    AdjoinRoot.mk_self, zero_mul, add_zero] at hd
  have hu : IsUnit (AdjoinRoot.mk (cyclotomic q A) (C (q : A)) * AdjoinRoot.mk (cyclotomic q A) (X ^ (q - 1))) := by
    rw [map_pow, AdjoinRoot.mk_X, AdjoinRoot.mk_C]
    refine (hq.map _).mul (IsUnit.pow _ ?_)
    exact (isUnit_pow_iff (NeZero.ne q)).1 (hx ▸ isUnit_one)
  rw [hd] at hu
  exact isUnit_of_mul_isUnit_left hu

def cyc_root {A : Type} [CommRing A] (q : ℕ) (hq : IsUnit (q : A)) : Prim q (AdjoinRoot (cyclotomic q A)) :=
  ⟨AdjoinRoot.root _, by simpa using hq.map (algebraMap A (AdjoinRoot (cyclotomic q A))), by
    rw [PrimBasic.aeval_cyc, ← map_cyclotomic q (AdjoinRoot.of (cyclotomic q A)), Polynomial.eval_map]
    exact AdjoinRoot.eval₂_root _⟩

lemma kummer_root {A : Type} [CommRing A] (q : ℕ) (hq0 : q ≠ 0) (u : Aˣ) :
    ∃ v : (AdjoinRoot (X ^ q - C (u : A)))ˣ, (v : AdjoinRoot (X ^ q - C (u : A))) ^ q = algebraMap A _ u := by
  have h1 : AdjoinRoot.root (X ^ q - C (u : A)) ^ q = algebraMap A _ u := by
    have := AdjoinRoot.eval₂_root (X ^ q - C (u : A))
    simpa [sub_eq_zero] using this
  have hr : IsUnit (AdjoinRoot.root (X ^ q - C (u : A))) := (isUnit_pow_iff hq0).1 (h1 ▸ u.isUnit.map _)
  exact ⟨hr.unit, by simpa using h1⟩

lemma spec_appTop {A B : CommRingCat.{0}} (ψ : A ⟶ B) (t : Γ(Spec A, ⊤)) :
    (Spec.map ψ).appTop.hom t = (Scheme.ΓSpecIso B).inv.hom (ψ.hom ((Scheme.ΓSpecIso A).hom.hom t)) := by
  have e := congrArg (fun φ => φ.hom t) (Scheme.ΓSpecIso_naturality ψ)
  simp only [CommRingCat.comp_apply] at e
  rw [← e]
  simp

end GlobalTheory.EtC.PrimLoc

namespace GlobalTheory.EtC.PrimLoc
open Polynomial

theorem prim_loc : ∀ (q : ℕ) [NeZero q] (U : Scheme.{0}), (IsUnit (q : Γ(U, ⊤)) → Loc U fun V _ => Nonempty (Prim q Γ(V, ⊤))) ∧ (∀ ζ ξ : Prim q Γ(U, ⊤), Loc U fun _ g => ∃ a : (ZMod q)ˣ, g.appTop.hom ξ.1 = g.appTop.hom ζ.1 ^ (a : ZMod q).val) ∧ (∀ (ζ : Prim q Γ(U, ⊤)) (x : Γ(U, ⊤)), x ^ q = 1 → Loc U fun _ g => ∃ a : ℕ, g.appTop.hom x = g.appTop.hom ζ.1 ^ a) ∧ (IsUnit (q : Γ(U, ⊤)) → ∀ u : (Γ(U, ⊤))ˣ, Loc U fun V g => ∃ v : (Γ(V, ⊤))ˣ, v ^ q = Units.map g.appTop.hom.toMonoidHom u) := by
  intro q _ U
  obtain ⟨-, -, h3, h4, h5, -⟩ := PrimBasic.prim_basic q Γ(U, ⊤)
  have hmod : ∀ a ∈ Finset.range q, ∀ b ∈ Finset.range q, a ≠ b → ¬ a ≡ b [MOD q] := by
    intro a ha b hb hab h
    apply hab
    unfold Nat.ModEq at h
    rwa [Nat.mod_eq_of_lt (Finset.mem_range.1 ha), Nat.mod_eq_of_lt (Finset.mem_range.1 hb)] at h
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro hq
    refine loc_of_alg (fun V _ => Nonempty (Prim q Γ(V, ⊤))) (fun V W g k ⟨ζ⟩ => ⟨ζ.map k.appTop.hom⟩) ?_
    intro A f hA
    have hqA : IsUnit (q : A) := by
      simpa using hq.map (f.appTop ≫ (Scheme.ΓSpecIso A).hom).hom
    refine ⟨AdjoinRoot (cyclotomic q A), inferInstance, inferInstance, cyc_etale q hqA,
      adjoinRoot_surj _ (cyclotomic.monic q A) ?_, ⟨(cyc_root q hqA).map (Scheme.ΓSpecIso _).inv.hom⟩⟩
    rw [natDegree_cyclotomic]
    exact (Nat.totient_pos.2 (NeZero.pos q)).ne'
  · intro ζ ξ
    refine loc_mono ?_ (loc_of_prod_eq_zero ξ.1 (fun a => ζ.1 ^ a) _ (h5 ζ ξ) ?_)
    · rintro V g ⟨a, ha, h⟩
      obtain ⟨ha1, ha2⟩ := Finset.mem_filter.1 ha
      refine ⟨ZMod.unitOfCoprime a ha2, ?_⟩
      rw [h, map_pow, ZMod.coe_unitOfCoprime, ZMod.val_natCast, Nat.mod_eq_of_lt (Finset.mem_range.1 ha1)]
    · intro a ha b hb hab
      exact h3 ζ a b (hmod a (Finset.mem_filter.1 ha).1 b (Finset.mem_filter.1 hb).1 hab)
  · intro ζ x hx
    refine loc_mono ?_ (loc_of_prod_eq_zero x (fun a => ζ.1 ^ a) _ (h4 ζ x hx) ?_)
    · rintro V g ⟨a, -, h⟩
      exact ⟨a, by rw [h, map_pow]⟩
    · intro a ha b hb hab
      exact h3 ζ a b (hmod a ha b hb hab)
  · intro hq u
    refine loc_of_alg (fun V g => ∃ v : (Γ(V, ⊤))ˣ, v ^ q = Units.map g.appTop.hom.toMonoidHom u) ?_ ?_
    · rintro V W g k ⟨v, hv⟩
      refine ⟨Units.map k.appTop.hom.toMonoidHom v, ?_⟩
      rw [← map_pow, hv]
      ext
      rfl
    intro A f hA
    have hqA : IsUnit (q : A) := by
      simpa using hq.map (f.appTop ≫ (Scheme.ΓSpecIso A).hom).hom
    obtain ⟨uA, huA⟩ : ∃ uA : (A : Type)ˣ, uA = Units.map (f.appTop ≫ (Scheme.ΓSpecIso A).hom).hom.toMonoidHom u :=
      ⟨_, rfl⟩
    obtain ⟨v, hv⟩ := kummer_root q (NeZero.ne q) uA
    refine ⟨AdjoinRoot (X ^ q - C (uA : A)), inferInstance, inferInstance,
      GlobalTheory.etale_adjoinRoot_X_pow_sub_C A q uA hqA uA.isUnit,
      adjoinRoot_surj _ (monic_X_pow_sub_C _ (NeZero.ne q)) ?_,
      ⟨Units.map (Scheme.ΓSpecIso (CommRingCat.of (AdjoinRoot (X ^ q - C (uA : A))))).inv.hom.toMonoidHom v, ?_⟩⟩
    · rw [natDegree_X_pow_sub_C _]
      exact NeZero.ne q
    · ext
      have hu' : (uA : A) = (Scheme.ΓSpecIso A).hom.hom (f.appTop.hom (u : Γ(U, ⊤))) := by rw [huA]; rfl
      rw [Units.val_pow_eq_pow_val, Units.coe_map, Units.coe_map]
      show (Scheme.ΓSpecIso (CommRingCat.of (AdjoinRoot (X ^ q - C (uA : A))))).inv.hom (v : AdjoinRoot (X ^ q - C (uA : A))) ^ q =
        (Spec.map (CommRingCat.ofHom (algebraMap A (AdjoinRoot (X ^ q - C (uA : A))))) ≫ f).appTop.hom (u : Γ(U, ⊤))
      rw [appTop_comp, spec_appTop, ← map_pow, hv]
      congr 1
      exact congrArg (algebraMap A (AdjoinRoot (X ^ q - C (uA : A)))) hu'

end GlobalTheory.EtC.PrimLoc
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleLocalizationAtPrimeTensorOfEtaleAwayStatement
section
open IsLocalRing Polynomial
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.etale_localization_atPrime_tensor_of_etale_away' : ∀ (R C : Type) [CommRing R] [CommRing C] [Algebra R C] (b : R),
    Algebra.Etale R (Localization.Away (algebraMap R C b)) →
    ∀ (P : Ideal R) [P.IsPrime], b ∉ P →
      Algebra.Etale (Localization.AtPrime P) (TensorProduct R (Localization.AtPrime P) C) := by
  first | (exact @GlobalTheory.etale_localization_atPrime_tensor_of_etale_away) | (exact GlobalTheory.etale_localization_atPrime_tensor_of_etale_away) | (intros; apply GlobalTheory.etale_localization_atPrime_tensor_of_etale_away <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleMemIffPointsStatement
section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex TensorProduct GlobalTheory.EtC
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.mem_etale_covering_sieves_iff_points : ∀ (U : Scheme.{0}) (S : Sieve U), S ∈ Scheme.etaleTopology.{0} U ↔ ∀ u : U, ∃ (V : Scheme.{0}) (j : V ⟶ U) (v : V), Etale j ∧ j v = u ∧ S.arrows j := by
  first | (exact @GlobalTheory.etale_mem_iff_points) | (exact GlobalTheory.etale_mem_iff_points) | (intros; apply GlobalTheory.etale_mem_iff_points  <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleSheafOfRingFunctorSectionsLocallyBijectiveStatement
section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex TensorProduct GlobalTheory.EtC
set_option maxHeartbeats 1000000 in
set_option backward.isDefEq.respectTransparency false in
theorem _root_.GlobalTheory.T.etaleSheafOfRingFunctor_sections_locally_bijective : ∀ (R : Type) [CommRing R] (M : CommRingCat.{0} ⥤ ModuleCat.{1} (ULift.{1} R)) (U : Scheme.{0}), (∀ (x : Sec (ofRings R M) U) (u : U), ∃ (V : Scheme.{0}) (j : V ⟶ U) (v : V) (m : M.obj Γ(V, ⊤)), IsAffine V ∧ Etale j ∧ j v = u ∧ ofRings.sec M V m = Sec.res j x) ∧ (∀ m : M.obj Γ(U, ⊤), ofRings.sec M U m = 0 → ∀ u : U, ∃ (V : Scheme.{0}) (j : V ⟶ U) (v : V), IsAffine V ∧ Etale j ∧ j v = u ∧ (M.map j.appTop).hom m = 0) ∧ ∀ (V : Scheme.{0}) (j : V ⟶ U) (m : M.obj Γ(U, ⊤)), Sec.res j (ofRings.sec M U m) = ofRings.sec M V ((M.map j.appTop).hom m) := by
  intro R _ M U
  refine ⟨fun x u => ?_, fun m hm u => ?_, fun V j m => ?_⟩
  · have hS := Presheaf.imageSieve_mem Scheme.etaleTopology
      (toSheafify Scheme.etaleTopology (Scheme.Γ ⋙ M)) (U := op U) x
    obtain ⟨V, j, v, hV, hj, hv, ⟨m, hm⟩⟩ := GlobalTheory.etale_affine_of_mem hS u
    exact ⟨V, j, v, m, hV, hj, hv, hm⟩
  · have hS := Presheaf.equalizerSieve_mem Scheme.etaleTopology
      (toSheafify Scheme.etaleTopology (Scheme.Γ ⋙ M)) (X := op U) m 0
      (hm.trans (map_zero _).symm)
    obtain ⟨V, j, v, hV, hj, hv, h⟩ := GlobalTheory.etale_affine_of_mem hS u
    refine ⟨V, j, v, hV, hj, hv, ?_⟩
    have h' : ((Scheme.Γ ⋙ M).map j.op).hom m = ((Scheme.Γ ⋙ M).map j.op).hom 0 := h
    rw [map_zero] at h'
    exact h'
  · have h := congrArg (fun f => f.hom m)
      ((toSheafify Scheme.etaleTopology (Scheme.Γ ⋙ M)).naturality j.op)
    exact h.symm
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleSpaceChainsMayerVietorisShortExactStatement
section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.etaleSpaceChains_mayerVietoris_shortExact : ∀ (R : Type) [CommRing R] {U V E : Spc} (f : U ⟶ E) (g : V ⟶ E), Cover2 R f g → ∃ w, (ShortComplex.mk (biprod.lift ((chains R).map (pullback.fst f g)) (-(chains R).map (pullback.snd f g))) (biprod.desc ((chains R).map f) ((chains R).map g)) w).ShortExact := by
  first | (exact @GlobalTheory.EtC.mv_shortExact) | (exact GlobalTheory.EtC.mv_shortExact) | (intros; apply GlobalTheory.EtC.mv_shortExact  <;> assumption)
end

