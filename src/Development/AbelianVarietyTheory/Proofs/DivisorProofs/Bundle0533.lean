module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.InstPreorder
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0166
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0134
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0520
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0503
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0187
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0218
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0275
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0282
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0514
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0293
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0266
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0522
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0081
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0175
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0230
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0272
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0285
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.Bundle0004
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0259
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0168
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0278
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0289
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0512
public import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0043
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0041
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0519
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0303
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0279
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0507
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0484
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0489
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0360
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0375
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0306
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0007
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0006
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LaurentCPullbackBijectiveFiniteStrictlyHenselian
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0322
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0358
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0026
public import Development.AbelianVarietyTheory.Definitions.Divisors.AxesVanishingStructureSheafDegOne
public import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.IsScalarTowerOfAlgebraMapEq
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.AbelianHodgeDeRham
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SmallEtaleCechNerveResolutionOfSurjective
public import Development.AbelianVarietyTheory.Definitions.Divisors.IndEtOfForallFinset

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HensIsLocalRingAndIsLocalHomOf
section
open IsLocalRing

noncomputable section

namespace GlobalTheory.Henselisation

namespace LocalLimit

variable {R : Type} [CommRing R] [IsLocalRing R]

theorem directedSystem_trans :
    DirectedSystem (fun i : EtNbhd R => i.B) (fun i j h => ⇑(EtNbhd.trans h : i.B →+* j.B)) :=
  ⟨fun {i} x => (_root_.GlobalTheory.Henselisation.trans_system R).1 i x,
    fun {k j i} hij hjk x =>
      (_root_.GlobalTheory.Henselisation.trans_system R).2 i j k hij hjk x⟩

theorem directed : IsDirected (EtNbhd R) (· ≤ ·) := _root_.GlobalTheory.Henselisation.etNbhd_isDirected R

theorem of_injective (i : EtNbhd R) : Function.Injective (Hens.of i) := by
  haveI := directedSystem_trans (R := R)
  haveI := directed (R := R)
  exact Ring.DirectLimit.of_injective (G := fun i : EtNbhd R => i.B)
    (fun i j h => EtNbhd.trans h) (fun i j h => (_root_.GlobalTheory.Henselisation.EtNbhd.trans_isLocalHom_injective R i j h).2) i

theorem exists_of (z : Hens R) : ∃ (i : EtNbhd R) (x : i.B), Hens.of i x = z := by
  haveI := directed (R := R)
  exact Ring.DirectLimit.exists_of z

theorem of_trans {i j : EtNbhd R} (h : i ≤ j) (x : i.B) :
    Hens.of j (EtNbhd.trans h x) = Hens.of i x :=
  Ring.DirectLimit.of_f (G := fun i : EtNbhd R => i.B) (f := fun _ _ h => ⇑(EtNbhd.trans h)) h x

theorem nontrivial : Nontrivial (Hens R) := by
  refine nontrivial_of_ne (1 : Hens R) 0 ?_
  intro h
  rw [← map_one (Hens.of (EtNbhd.base (R := R))), ← map_zero (Hens.of (EtNbhd.base (R := R)))] at h
  exact one_ne_zero (of_injective _ h)

theorem isUnit_or_isUnit_of_add_one {a b : Hens R} (hab : a + b = 1) : IsUnit a ∨ IsUnit b := by
  obtain ⟨i, x, rfl⟩ := exists_of a
  obtain ⟨j, y, rfl⟩ := exists_of b
  haveI := directed (R := R)
  obtain ⟨k, hik, hjk⟩ := directed_of (· ≤ ·) i j
  have h1 : EtNbhd.trans hik x + EtNbhd.trans hjk y = 1 := by
    apply of_injective k
    rw [(Hens.of k).map_add, of_trans, of_trans, map_one, hab]
  rcases IsLocalRing.isUnit_or_isUnit_of_add_one h1 with h | h
  · left
    rw [← of_trans hik]
    exact h.map _
  · right
    rw [← of_trans hjk]
    exact h.map _

theorem isLocalHom_of (i : EtNbhd R) : IsLocalHom (Hens.of i) := by
  refine ⟨fun x hx => ?_⟩
  obtain ⟨u, hu⟩ := hx
  obtain ⟨j, y, hy⟩ := exists_of (↑u⁻¹ : Hens R)
  haveI := directed (R := R)
  obtain ⟨k, hik, hjk⟩ := directed_of (· ≤ ·) i j
  have h1 : EtNbhd.trans hik x * EtNbhd.trans hjk y = 1 := by
    apply of_injective k
    rw [map_mul, of_trans, of_trans, map_one, hy, ← hu, Units.mul_inv]
  haveI := (_root_.GlobalTheory.Henselisation.EtNbhd.trans_isLocalHom_injective R i k hik).1
  exact isUnit_of_map_unit (EtNbhd.trans hik) x (IsUnit.of_mul_eq_one _ h1)

end LocalLimit

theorem hens_isLocalRing_and_isLocalHom_of :
    ∀ (R : Type) [CommRing R] [IsLocalRing R], IsLocalRing (Hens R) ∧ ∀ i : EtNbhd R, IsLocalHom (Hens.of i) := by
  intro R _ _
  haveI := LocalLimit.nontrivial (R := R)
  exact ⟨IsLocalRing.of_is_unit_or_is_unit_of_add_one LocalLimit.isUnit_or_isUnit_of_add_one,
    LocalLimit.isLocalHom_of⟩

end GlobalTheory.Henselisation

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HopfOrdersOfZmodPExtremes
section
open IsLocalRing Polynomial
open scoped TensorProduct

namespace GlobalTheory.OriginPrimes

theorem origin_primes : ∀ (A' : Type) [CommRing A'] [HenselianLocalRing A'] [IsSepClosed (ResidueField A')]
    (𝔭 : Ideal A') [𝔭.IsPrime] (E : Type) [CommRing E] [Algebra (Polynomial A') E]
    [Algebra.Etale (Polynomial A') E] (Q : Ideal E) [Q.IsPrime],
    Q.comap (algebraMap (Polynomial A') E) = GlobalTheory.KeyOriginCut.originIdeal A' →
    (𝔭.map ((algebraMap (Polynomial A') (Localization.AtPrime Q)).comp Polynomial.C)).IsPrime := by
  intro A' _ _ _ 𝔭 _ E _ _ _ Q _ hQ
  obtain ⟨S, _, _, _, _, f, hfi, hker⟩ := GlobalTheory.T.exists_normal_local_domain_over_henselian_prime A' 𝔭
  obtain ⟨hXi, hOp, hOc, hOu⟩ := GlobalTheory.T.origin_ideal_unique_prime_over A' S f hfi
  letI : Algebra (Polynomial A') (Polynomial S) := (Polynomial.mapRingHom f).toAlgebra
  haveI : Algebra.IsIntegral (Polynomial A') (Polynomial S) := ⟨hXi⟩
  have hmax : (maximalIdeal (Localization.AtPrime Q)).comap
      (algebraMap (Polynomial A') (Localization.AtPrime Q)) = GlobalTheory.KeyOriginCut.originIdeal A' := by
    have h0 : (maximalIdeal (Localization.AtPrime Q)).comap (algebraMap E (Localization.AtPrime Q)) = Q :=
      Localization.AtPrime.under_maximalIdeal (I := Q)
    rw [IsScalarTower.algebraMap_eq (Polynomial A') E (Localization.AtPrime Q), ← Ideal.comap_comap,
      h0, hQ]
  haveI hloc : IsLocalRing (TensorProduct (Polynomial A') (Polynomial S) (Localization.AtPrime Q)) :=
    GlobalTheory.T.isLocalRing_tensor_of_unique_prime_over (Polynomial A') (Polynomial S) (Localization.AtPrime Q) (GlobalTheory.KeyOriginCut.originIdeal S)
      (by rw [hmax]; exact hOc) (by intro 𝔔 h1 h2; rw [hmax] at h2; exact hOu 𝔔 h1 h2)
      (GlobalTheory.T.exists_sub_mem_maximalIdeal_etale_over_origin A' E Q hQ)
  haveI hdom : IsDomain (TensorProduct (Polynomial A') (Polynomial S) (Localization.AtPrime Q)) :=
    GlobalTheory.T.isDomain_tensor_atPrime_of_isLocalRing_of_etale (Polynomial A') (Polynomial S) E Q hloc
  haveI : Module.Flat (Polynomial A') (Localization.AtPrime Q) :=
    Module.Flat.trans (Polynomial A') E (Localization.AtPrime Q)
  have hkerX : RingHom.ker (algebraMap (Polynomial A') (Polynomial S)) = 𝔭.map Polynomial.C := by
    change RingHom.ker (Polynomial.mapRingHom f) = _
    rw [Polynomial.ker_mapRingHom, hker]
  have hJ : 𝔭.map ((algebraMap (Polynomial A') (Localization.AtPrime Q)).comp Polynomial.C) =
      (𝔭.map Polynomial.C).map (algebraMap (Polynomial A') (Localization.AtPrime Q)) := by
    rw [Ideal.map_map]
  let g : Localization.AtPrime Q →+* TensorProduct (Polynomial A') (Polynomial S) (Localization.AtPrime Q) :=
    (Algebra.TensorProduct.includeRight : Localization.AtPrime Q →ₐ[Polynomial A'] _).toRingHom
  have hg0 : ∀ y ∈ 𝔭.map ((algebraMap (Polynomial A') (Localization.AtPrime Q)).comp Polynomial.C), g y = 0 := by
    rw [hJ]
    have hle : (𝔭.map Polynomial.C).map (algebraMap (Polynomial A') (Localization.AtPrime Q)) ≤ RingHom.ker g := by
      rw [Ideal.map_le_iff_le_comap]
      intro m hm
      rw [Ideal.mem_comap, RingHom.mem_ker]
      change (Algebra.TensorProduct.includeRight : Localization.AtPrime Q →ₐ[Polynomial A'] _)
        (algebraMap (Polynomial A') (Localization.AtPrime Q) m) = 0
      rw [AlgHom.commutes, Algebra.TensorProduct.algebraMap_apply]
      have : algebraMap (Polynomial A') (Polynomial S) m = 0 := by
        rw [← RingHom.mem_ker, hkerX]; exact hm
      rw [this, TensorProduct.zero_tmul]
    exact fun y hy => hle hy
  have hg1 : ∀ y, g y = 0 → y ∈ 𝔭.map ((algebraMap (Polynomial A') (Localization.AtPrime Q)).comp Polynomial.C) := by
    intro y hy
    rw [hJ]
    exact GlobalTheory.T.flat_tensor_kernel_mem_map_ideal (Polynomial A') (Polynomial S) (Localization.AtPrime Q) _ hkerX y hy
  refine ⟨?_, ?_⟩
  · intro htop
    have h1 := hg0 1 (by rw [htop]; exact Submodule.mem_top)
    rw [map_one] at h1
    exact one_ne_zero h1
  · intro x y hxy
    have h := hg0 _ hxy
    rw [map_mul] at h
    rcases mul_eq_zero.mp h with h | h
    · exact Or.inl (hg1 x h)
    · exact Or.inr (hg1 y h)

end GlobalTheory.OriginPrimes
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IdentityComponentsSmoothGroupSchemeMulMem
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj TopologicalSpace TensorProduct
open scoped CategoryTheory.Obj

noncomputable section

namespace GlobalTheory.IdCompMul

theorem mul_mem_of_field {S : Scheme.{0}} (G : Over S) [GrpObj G] (hG : Smooth G.hom) (k : Type) [Field k]
    (p : Spec (CommRingCat.of k) ⟶ S) (a b : Over.mk p ⟶ G)
    (ha : a.left (IsLocalRing.closedPoint k) ∈
      {x : G.left | x ∈ connectedComponentIn (G.hom ⁻¹' {G.hom x}) ((η[G]).left (G.hom x))})
    (hb : b.left (IsLocalRing.closedPoint k) ∈
      {x : G.left | x ∈ connectedComponentIn (G.hom ⁻¹' {G.hom x}) ((η[G]).left (G.hom x))}) :
    (a * b).left (IsLocalRing.closedPoint k) ∈
      {x : G.left | x ∈ connectedComponentIn (G.hom ⁻¹' {G.hom x}) ((η[G]).left (G.hom x))} := by
  let F := Over.pullback p
  let G' : Over (Spec (CommRingCat.of k)) := F.obj G
  have hpt : ∀ z : (Spec (CommRingCat.of k) : Scheme), z = IsLocalRing.closedPoint k :=
    fun z => Subsingleton.elim _ _
  have hsec : η[G'].left ≫ pullback.fst G.hom p = p ≫ η[G].left := by
    have hc : pullback.fst (𝟙 S) p = pullback.snd (𝟙 S) p ≫ p := by
      simpa using pullback.condition (f := 𝟙 S) (g := p)
    simp [G', F, hc]
  have key := _root_.GlobalTheory.sectionComponents_preimage_of_isPullback G.left S G'.left (Spec (CommRingCat.of k)) G.hom G'.hom p
    (pullback.fst G.hom p) η[G].left η[G'].left hG (IsPullback.of_hasPullback G.hom p)
    (Over.w η[G]) (Over.w η[G']) hsec
  have huniv : ∀ t : (Spec (CommRingCat.of k) : Scheme), G'.hom ⁻¹' {t} = Set.univ :=
    fun t => Set.eq_univ_of_forall fun y => Set.mem_singleton_iff.mpr ((hpt _).trans (hpt t).symm)
  have hq : ∀ z : G'.left,
      pullback.fst G.hom p z ∈
        {x : G.left | x ∈ connectedComponentIn (G.hom ⁻¹' {G.hom x}) ((η[G]).left (G.hom x))} ↔
      z ∈ connectedComponent ((η[G']).left (IsLocalRing.closedPoint k)) := by
    intro z
    rw [← Set.mem_preimage, key]
    show z ∈ connectedComponentIn (G'.hom ⁻¹' {G'.hom z}) ((η[G']).left (G'.hom z)) ↔ _
    rw [huniv, connectedComponentIn_univ, hpt (G'.hom z)]
  let u : 𝟙_ (Over (Spec (CommRingCat.of k))) ⟶ F.obj (Over.mk p) :=
    Over.homMk (pullback.lift (𝟙 _) (𝟙 _) (by simp)) (by simp [F])
  have hgen : ∀ c : Over.mk p ⟶ G, (u ≫ F.map c).left ≫ pullback.fst G.hom p = c.left := by
    intro c
    simp [u, F]
  have hpoint : ∀ (c : Over.mk p ⟶ G) (t : 𝟙_ (Over (Spec (CommRingCat.of k))) ⟶ G'),
      t.left ≫ pullback.fst G.hom p = c.left →
        pullback.fst G.hom p (t.left (IsLocalRing.closedPoint k)) = c.left (IsLocalRing.closedPoint k) := by
    intro c t h
    rw [← h]
    rfl
  have ha' := (hq _).1 (by rw [hpoint a _ (hgen a)]; exact ha)
  have hb' := (hq _).1 (by rw [hpoint b _ (hgen b)]; exact hb)
  have hm := _root_.GlobalTheory.mul_mem_identityComponent_of_rational k G' (u ≫ F.map a) (u ≫ F.map b) ha' hb'
  have e1 := hgen (a * b)
  rw [Functor.map_mul, MonObj.comp_mul] at e1
  rw [← hpoint (a * b) _ e1]
  exact (hq _).2 hm

theorem mul_mem : ∀ (S : Scheme.{0}) (G : Over S) [GrpObj G], Smooth G.hom → ∀ w : (G ⊗ G).left, (fst G G).left w ∈ {x : G.left | x ∈ connectedComponentIn (G.hom ⁻¹' {G.hom x}) ((η[G]).left (G.hom x))} → (snd G G).left w ∈ {x : G.left | x ∈ connectedComponentIn (G.hom ⁻¹' {G.hom x}) ((η[G]).left (G.hom x))} → (μ[G]).left w ∈ {x : G.left | x ∈ connectedComponentIn (G.hom ⁻¹' {G.hom x}) ((η[G]).left (G.hom x))} := by
  intro S G instG hG w h1 h2
  let κ := (G ⊗ G).left.residueField w
  let j : Spec (CommRingCat.of κ) ⟶ (G ⊗ G).left := (G ⊗ G).left.fromSpecResidueField w
  let p : Spec (CommRingCat.of κ) ⟶ S := j ≫ (G ⊗ G).hom
  let a : Over.mk p ⟶ G := Over.homMk (j ≫ (fst G G).left) (by simp [p])
  let b : Over.mk p ⟶ G := Over.homMk (j ≫ (snd G G).left) (by simp [p, pullback.condition])
  have hw : j (IsLocalRing.closedPoint κ) = w := Scheme.fromSpecResidueField_apply w _
  have hl : lift a b = (Over.homMk j rfl : Over.mk p ⟶ G ⊗ G) := by
    apply CartesianMonoidalCategory.hom_ext
    · ext1
      simp [a]
    · ext1
      simp [b]
  have hm := mul_mem_of_field G hG κ p a b
    (by
      convert h1 using 2
      exact congrArg (fst G G).left hw)
    (by
      convert h2 using 2
      exact congrArg (snd G G).left hw)
  rw [Hom.mul_def, Over.comp_left, hl] at hm
  convert hm using 2
  exact (congrArg (μ[G]).left hw).symm

end GlobalTheory.IdCompMul
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegralClosureEtaleAtOfHeightLeOnePurity
section
open IsLocalRing Polynomial

noncomputable section

namespace GlobalTheory.KeyOriginEnlarge

theorem atPrime_isDomain_isIntegrallyClosed_isNoetherian_injective : ∀ (A : Type) [CommRing A] [IsDomain A] [IsNoetherianRing A] [IsIntegrallyClosed A]
    (EA : Type) [CommRing EA] [Algebra (Polynomial A) EA] [Algebra A EA]
    [IsScalarTower A (Polynomial A) EA] [Algebra.Etale (Polynomial A) EA]
    (QA : Ideal EA) [QA.IsPrime],
    IsDomain (Localization.AtPrime QA) ∧ IsIntegrallyClosed (Localization.AtPrime QA) ∧
      IsNoetherianRing (Localization.AtPrime QA) ∧
      Function.Injective (algebraMap A (Localization.AtPrime QA)) := by
  intro A _ _ _ _ EA _ _ _ _ _ QA _
  obtain ⟨hd, hn⟩ := GlobalTheory.isDomain_and_isIntegrallyClosed_atPrime_of_etale (Polynomial A) QA
    (Localization.AtPrime QA)
  haveI : IsNoetherianRing EA := Algebra.FiniteType.isNoetherianRing (Polynomial A) EA
  refine ⟨hd, hn, inferInstance, ?_⟩
  haveI := hd
  haveI : Module.Flat (Polynomial A) (Localization.AtPrime QA) :=
    Module.Flat.trans (Polynomial A) EA (Localization.AtPrime QA)
  have h1 : Function.Injective (algebraMap (Polynomial A) (Localization.AtPrime QA)) :=
    FaithfulSMul.algebraMap_injective (Polynomial A) (Localization.AtPrime QA)
  have h2 : algebraMap A (Localization.AtPrime QA) =
      (algebraMap (Polynomial A) (Localization.AtPrime QA)).comp (algebraMap A (Polynomial A)) :=
    IsScalarTower.algebraMap_eq _ _ _
  rw [h2]
  exact h1.comp Polynomial.C_injective

theorem closureEtaleAt_of_comap_height_le_one : ∀ (q : ℕ) (A : Type) [CommRing A] [IsDomain A] [IsLocalRing A] [IsNoetherianRing A] [IsIntegrallyClosed A]
    [Algebra.EssFiniteType ℤ A]
    (EA : Type) [CommRing EA] [Algebra (Polynomial A) EA] [Algebra A EA]
    [IsScalarTower A (Polynomial A) EA] [Algebra.Etale (Polynomial A) EA]
    (QA : Ideal EA) [QA.IsPrime]
    (DA : Type) [CommRing DA] [Algebra (GlobalTheory.LocAcyc.GenFib A (Localization.AtPrime QA)) DA]
    (actA : Multiplicative (ZMod q) →* (DA ≃ₐ[GlobalTheory.LocAcyc.GenFib A (Localization.AtPrime QA)] DA)),
    GlobalTheory.KeyOriginCut.IsZTorsor (GlobalTheory.LocAcyc.GenFib A (Localization.AtPrime QA)) DA q actA →
    (∀ (P : Ideal (Localization.AtPrime QA)) [P.IsPrime], P.height ≤ 1 →
      GlobalTheory.KeyOriginEnlarge.ClosureEtaleAt A (Localization.AtPrime QA) DA P) →
    ∀ (P : Ideal (Localization.AtPrime QA)) [P.IsPrime],
      (P.comap (algebraMap A (Localization.AtPrime QA))).height ≤ 1 →
      GlobalTheory.KeyOriginEnlarge.ClosureEtaleAt A (Localization.AtPrime QA) DA P := by
  intro q A _ _ _ _ _ _ EA _ _ _ _ _ QA _ DA _ _ actA htors hyp P _ hP
  obtain ⟨hdom, hic, hnoeth, hinj⟩ :=
    atPrime_isDomain_isIntegrallyClosed_isNoetherian_injective A EA QA
  haveI := GlobalTheory.T.cyclic_torsor_etale _ DA q actA htors
  haveI : Module.Finite (GlobalTheory.LocAcyc.GenFib A (Localization.AtPrime QA)) DA := htors.1
  letI := GlobalTheory.KeyOriginNoeth.closureAlg A (Localization.AtPrime QA) DA
  haveI := GlobalTheory.T.closure_finite_over_base A (Localization.AtPrime QA) hinj DA
  exact GlobalTheory.T.etale_atPrime_of_regular_of_isIntegrallyClosedIn (Localization.AtPrime QA)
    (GlobalTheory.KeyOriginNoeth.closure A (Localization.AtPrime QA) DA)
    (GlobalTheory.T.isIntegrallyClosedIn_etale_genFib_of_injective A (Localization.AtPrime QA) hinj DA) P (GlobalTheory.T.regular_height_one_localization A EA QA P hP)
    (fun P' _ _ hh => hyp P' hh)

end GlobalTheory.KeyOriginEnlarge
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsCechOneCoboundaryOfMixedOverlaps
section
open AlgebraicGeometry CategoryTheory Limits
open GlobalTheory.KS (rsT C1 IsCoc IsCob)

noncomputable section
namespace GlobalTheory.KS

theorem isCob_of_mixed : ∀ (X : Scheme.{0}) (J K : Type) (V : J → X.Opens) (U : K → X.Opens), ⨆ k, U k = ⊤ → ∀ (z : C1 V) (z' : C1 U) (b : ∀ i k, Γ(X, V i ⊓ U k)), (∀ i i' k, rsT (z i i') (V i ⊓ V i' ⊓ U k) = rsT (b i k) (V i ⊓ V i' ⊓ U k) - rsT (b i' k) (V i ⊓ V i' ⊓ U k)) → (∀ i k k', rsT (z' k k') (V i ⊓ U k ⊓ U k') = rsT (b i k') (V i ⊓ U k ⊓ U k') - rsT (b i k) (V i ⊓ U k ⊓ U k')) → IsCob U z' → IsCob V z := by
  intro X J K V U hU z z' b h1 h2 hz'
  obtain ⟨y', hy'⟩ := hz'
  have cov : ∀ O : X.Opens, O ≤ ⨆ k, O ⊓ U k := fun O x hx => by
    have : x ∈ ⨆ k, U k := by rw [hU]; trivial
    obtain ⟨k, hk⟩ := TopologicalSpace.Opens.mem_iSup.1 this
    exact TopologicalSpace.Opens.mem_iSup.2 ⟨k, hx, hk⟩
  have glue : ∀ i, ∃ t : Γ(X, V i), ∀ k, rsT t (V i ⊓ U k) = rsT (y' k) (V i ⊓ U k) - b i k := by
    intro i
    refine exists_rsT_eq (fun k => V i ⊓ U k) (fun k => inf_le_left) (cov _) _ fun k l => ?_
    have e : (V i ⊓ U k) ⊓ (V i ⊓ U l) ≤ V i ⊓ U k ⊓ U l := fun x hx => ⟨⟨hx.1.1, hx.1.2⟩, hx.2.2⟩
    have e₁ : V i ⊓ U k ⊓ U l ≤ V i ⊓ U k := inf_le_left
    have e₂ : V i ⊓ U k ⊓ U l ≤ V i ⊓ U l := fun x hx => ⟨hx.1.1, hx.2⟩
    have e₃ : V i ⊓ U k ⊓ U l ≤ U k ⊓ U l := fun x hx => ⟨hx.1.2, hx.2⟩
    rw [← rsT_rsT e₁ e, ← rsT_rsT e₂ e]
    congr 1
    have k₀ := congrArg (fun s => rsT s (V i ⊓ U k ⊓ U l)) (hy' k l)
    simp only [rsT_sub] at k₀
    rw [h2, rsT_rsT inf_le_right e₃, rsT_rsT inf_le_left e₃] at k₀
    simp only [rsT_sub]
    rw [rsT_rsT inf_le_right e₁, rsT_rsT inf_le_right e₂]
    linear_combination k₀
  choose y hy using glue
  refine ⟨y, fun i i' => ?_⟩
  refine eq_of_rsT_eq (fun k => V i ⊓ V i' ⊓ U k) (fun k => inf_le_left) (cov _) _ _ fun k => ?_
  have e₁ : V i ⊓ V i' ⊓ U k ≤ V i ⊓ U k := fun x hx => ⟨hx.1.1, hx.2⟩
  have e₂ : V i ⊓ V i' ⊓ U k ≤ V i' ⊓ U k := fun x hx => ⟨hx.1.2, hx.2⟩
  show rsT (z i i') (V i ⊓ V i' ⊓ U k) = rsT (rsT (y i') (V i ⊓ V i') - rsT (y i) (V i ⊓ V i')) (V i ⊓ V i' ⊓ U k)
  rw [h1, rsT_sub, rsT_rsT inf_le_right inf_le_left, rsT_rsT inf_le_left inf_le_left,
    ← rsT_rsT inf_le_left e₂ (y i'), ← rsT_rsT inf_le_left e₁ (y i), hy, hy]
  simp only [rsT_sub]
  rw [rsT_rsT inf_le_right e₁, rsT_rsT inf_le_right e₂]
  ring

end GlobalTheory.KS
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.KummerReductionChernDefectEqOfPowEqStatement
section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.kummerReductionChernDefect_eq_of_pow_eq : ∀ (Q q : ℕ) [NeZero Q], q ∣ Q → ∀ (U : Scheme.{0}) (v w : (Γ(U, ⊤))ˣ), IsUnit (Q : Γ(U, ⊤)) → v ^ Q = w ^ Q → GlobalTheory.EtC.RedChern.defect Q q U v = GlobalTheory.EtC.RedChern.defect Q q U w := by
  first
  | exact @GlobalTheory.EtC.RedChern.defect_eq_of_pow_eq
  | exact GlobalTheory.EtC.RedChern.defect_eq_of_pow_eq
  | (intros; apply GlobalTheory.EtC.RedChern.defect_eq_of_pow_eq <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LaurentCPullbackBijectiveFiniteStrictlyHenselianStatement
section
open CategoryTheory Limits AlgebraicGeometry Opposite Simplicial GlobalTheory.EtC GlobalTheory.EtC.GmStep
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.laurentC_pullback_bijective_finite_strictlyHenselian : ∀ (q : ℕ) [NeZero q] (A : Type) [CommRing A], SH A → IsUnit (q : A) → ∀ (T : Type) [CommRing T] [Algebra A T],
  Module.Finite A T → ∀ i : ℤ, Function.Bijective (pull _ (spMap (LaurentPolynomial.C : T →+* LaurentPolynomial T)) (tw q i) 0) := by
  first | (exact @GlobalTheory.EtC.SpecMapPullbackFunctoriality.laurent_C_pull_bijective) | (exact GlobalTheory.EtC.SpecMapPullbackFunctoriality.laurent_C_pull_bijective) | (intros; apply GlobalTheory.EtC.SpecMapPullbackFunctoriality.laurent_C_pull_bijective <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MayerVietorisExtendClassCoprimeEtaleExcisionStatement
section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.mayerVietoris_extend_class_coprime_etaleExcision : ∀ (q : ℕ) (A C : Type) [CommRing A] [CommRing C] [Algebra A C] (f g : A), IsCoprime f g → IsExcisionNbhd A C g → ∀ (n i : ℤ) (a : Ht q (sp (Localization.Away (f * g))) n i), pull _ (spMap (Localization.awayMap (algebraMap A C) (f * g))) _ _ a = 0 → ∃ b : Ht q (sp (Localization.Away f)) n i, ∀ ρ : Localization.Away f →+* Localization.Away (f * g), ρ.comp (algebraMap A _) = algebraMap A _ → pull _ (spMap ρ) _ _ b = a := by
  first | (exact @GlobalTheory.MVGlue.glue) | (exact GlobalTheory.MVGlue.glue) | (intros; apply GlobalTheory.MVGlue.glue <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.OfFormInjectiveOfH0Const
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.AbCoh
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

namespace GlobalTheory.AbCoh

theorem ofForm_injective_of_H0Const (R : Type) [CommRing R] (C : Type) [Category.{0} C]
    (F : C ⥤ CommAlgCat.{0} R) (hF : CohomZeroIsConstants F) : Function.Injective (ofForm F) := by
  rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
  intro ω hω
  obtain ⟨g, hg, hD⟩ := (ofForm_eq_zero (F := F)).1 hω
  have h0 : d0 F g = 0 := by
    funext T T' φ
    have e : d0 F g T T' φ = g T' - mp F φ (g T) := rfl
    rw [e, ← hg φ, sub_self]; rfl
  obtain ⟨r, hr, -⟩ := hF g h0
  refine Subtype.ext (Subtype.ext (funext fun T ↦ ?_))
  rw [← hD T, hr T]
  exact (D R (F.obj T)).map_algebraMap r

end GlobalTheory.AbCoh
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SmallEtaleCechNerveResolutionOfSurjectiveStatement
section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex TensorProduct GlobalTheory.EtC
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.smallEtale_cechNerve_resolution_of_surjective : ∀ (R : Type) [CommRing R] (S : Scheme.{0}) (E : Spc) (p : E ⟶ sch.obj S) [HasFiniteWidePushouts (S.Etale)ᵒᵖ] (U V : (S.Etale)ᵒᵖ) (g : U ⟶ V), Surjective g.unop.left → Hyp R ((Scheme.Etale.forget S ⋙ bc p).op) (coAug g) := by
  first | (exact @GlobalTheory.EtC.SmallEtaleCech.hyp_coAug) | (exact GlobalTheory.EtC.SmallEtaleCech.hyp_coAug) | (intros; apply GlobalTheory.EtC.SmallEtaleCech.hyp_coAug <;> assumption)
end

