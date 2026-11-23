module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0175
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0218
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0230
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0272
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0285
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsNoetherianModelOfDivisorOfConstants
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsNoetherianNormalLocalApprox
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0023
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.InstPreorder
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0503
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0007
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0006
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0026
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0302
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0412
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0298
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0504
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0505

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsKummerEnlargementRootsOfUniformisers
section
open IsLocalRing Polynomial

noncomputable section

namespace GlobalTheory.KummerEnlarge

open GlobalTheory.NormalApprox

theorem height_comap_eq_one_of_goingDown {A B : Type} [CommRing A] [IsDomain A] [CommRing B]
    [Algebra A B] [Algebra.HasGoingDown A B] (Q : Ideal B) [Q.IsPrime] (hQ : Q.height = 1)
    (hne : Q.comap (algebraMap A B) ≠ ⊥) : (Q.comap (algebraMap A B)).height = 1 := by
  set p : Ideal A := Q.comap (algebraMap A B) with hp
  haveI : p.IsPrime := Ideal.comap_isPrime _ Q
  haveI : Q.LiesOver p := ⟨rfl⟩
  apply le_antisymm
  · rw [show ((1 : ℕ∞)) = ((1 : ℕ) : ℕ∞) from rfl, Ideal.height_le_iff]
    intro r hr hrp
    by_contra hcon
    have hr0 : r ≠ ⊥ := by
      rintro rfl
      simp at hcon
    haveI := hr
    obtain ⟨P₁, hP₁Q, hP₁, hP₁o⟩ := Ideal.exists_ideal_lt_liesOver_of_lt (p := r) (q := p) Q hrp
    haveI := hP₁
    haveI : (⊥ : Ideal A).IsPrime := Ideal.isPrime_bot
    obtain ⟨P₀, hP₀P₁, hP₀, -⟩ := Ideal.exists_ideal_lt_liesOver_of_lt (p := ⊥) (q := r) P₁
      (bot_lt_iff_ne_bot.mpr hr0)
    haveI := hP₀
    have h1 := Ideal.height_add_one_le_of_lt_of_isPrime hP₀P₁
    have h2 := Ideal.height_add_one_le_of_lt_of_isPrime hP₁Q
    rw [hQ] at h2
    have h4 : (1 : ℕ∞) ≤ P₁.height := le_trans le_add_self h1
    have h3 : (1 : ℕ∞) + 1 ≤ 1 := le_trans (by gcongr) h2
    exact absurd h3 (by decide)
  · haveI : (⊥ : Ideal A).IsPrime := Ideal.isPrime_bot
    have := Ideal.height_add_one_le_of_lt_of_isPrime (bot_lt_iff_ne_bot.mpr hne)
    simpa using this

theorem exists_uniformiser (A : Type) [CommRing A] [IsDomain A] [IsNoetherianRing A]
    [IsIntegrallyClosed A] (p : Ideal A) :
    ∃ π : A, ∀ [p.IsPrime], p.height = 1 → Irreducible (algebraMap A (Localization.AtPrime p) π) := by
  by_cases h : p.IsPrime ∧ p.height = 1
  · obtain ⟨hp, h1⟩ := h
    haveI := GlobalTheory.localizationAtPrime_isDiscreteValuationRing_of_height_eq_one A p h1
    obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible (Localization.AtPrime p)
    obtain ⟨⟨x, s⟩, hxs⟩ := IsLocalization.surj p.primeCompl ϖ
    refine ⟨x, fun _ => ?_⟩
    have hu : IsUnit (algebraMap A (Localization.AtPrime p) s) := IsLocalization.map_units _ s
    have e : algebraMap A (Localization.AtPrime p) x = ϖ * algebraMap A (Localization.AtPrime p) s :=
      hxs.symm
    rw [e]
    exact (irreducible_mul_isUnit hu).mpr hϖ
  · exact ⟨1, fun h1 => absurd ⟨inferInstance, h1⟩ h⟩

end GlobalTheory.KummerEnlarge

namespace GlobalTheory.KummerEnlarge

open GlobalTheory.NormalApprox

theorem exists_kummer_enlargement : ∀ (T : Type) [CommRing T] [IsDomain T] [IsLocalRing T], GlobalTheory.LocAcyc.AbsIntClosed T →
    ∀ (q : ℕ), 0 < q → IsUnit (q : T) →
    ∀ (A : Type) [CommRing A] [IsDomain A] [IsLocalRing A] [IsNoetherianRing A] [IsIntegrallyClosed A]
      [Algebra.EssFiniteType ℤ A] (i : A →+* T), Function.Injective i → IsLocalHom i →
    ∀ a : A, a ≠ 0 →
    ∃ (A₁ : Type) (_ : CommRing A₁) (_ : IsDomain A₁) (_ : IsLocalRing A₁) (_ : IsNoetherianRing A₁)
      (_ : IsIntegrallyClosed A₁) (_ : Algebra.EssFiniteType ℤ A₁) (f : A →+* A₁) (i₁ : A₁ →+* T),
      Function.Injective f ∧ Function.Injective i₁ ∧ IsLocalHom i₁ ∧ i₁.comp f = i ∧
      ∀ (p₁ : Ideal A₁) [p₁.IsPrime], p₁.height = 1 → f a ∈ p₁ →
        (p₁.comap f).height = 1 ∧
        ∃ π : A, Irreducible (algebraMap A (Localization.AtPrime (p₁.comap f)) π) ∧
          ∃ y : A₁, y ^ q = f π := by
  intro T _ _ _ hT q hq hqT A _ _ _ _ _ _ i hi hloc a ha
  classical
  haveI : IsIntegrallyClosed T := GlobalTheory.VertUnitsNoeth.isIntegrallyClosed_of_absIntClosed' T hT
  choose π hπ using exists_uniformiser A
  have hy : ∀ p : Ideal A, ∃ y : T, y ^ q = i (π p) := by
    intro p
    obtain ⟨y, hy⟩ := hT (X ^ q - C (i (π p))) (monic_X_pow_sub_C _ hq.ne')
      (by rw [natDegree_X_pow_sub_C _]; exact hq)
    refine ⟨y, ?_⟩
    simpa [sub_eq_zero] using hy
  choose y hy using hy
  have hfin := Ideal.finite_minimalPrimes_of_isNoetherianRing A (Ideal.span {a})
  set S : Finset T := (Algebra.EssFiniteType.finset ℤ A).image i ∪ hfin.toFinset.image y with hS

  have hgen : ∀ z ∈ Algebra.adjoin ℤ ((Algebra.EssFiniteType.finset ℤ A : Finset A) : Set A),
      i z ∈ gen S := by
    intro z hz
    have h2 : i.toIntAlgHom z ∈ (Algebra.adjoin ℤ ((Algebra.EssFiniteType.finset ℤ A : Finset A) : Set A)).map
        i.toIntAlgHom := Subalgebra.mem_map.mpr ⟨z, hz, rfl⟩
    rw [AlgHom.map_adjoin] at h2
    refine Algebra.adjoin_mono ?_ h2
    rintro t ⟨u, hu, rfl⟩
    simp only [hS, Finset.coe_union, Finset.coe_image]
    exact Or.inl ⟨u, hu, rfl⟩
  have hmem : ∀ x : A, i x ∈ loc S := by
    intro x
    haveI := Algebra.EssFiniteType.isLocalization ℤ A
    obtain ⟨⟨r, m⟩, hrm⟩ := IsLocalization.surj (Algebra.EssFiniteType.submonoid ℤ A) x
    refine ⟨i (m.1 : A), gen_le_norm S (hgen _ m.1.2), ?_, ?_⟩
    · exact (IsLocalization.map_units A m).map i
    · rw [mul_comm, ← map_mul]
      have e : x * (m.1 : A) = (r : A) := hrm
      rw [e]
      exact gen_le_norm S (hgen _ r.2)
  let f : A →+* loc S := i.codRestrict (loc S) hmem
  have hfinj : Function.Injective f := fun x x' h => hi (congrArg Subtype.val h)
  haveI := loc_isLocalization S
  haveI : IsNoetherianRing (loc S) :=
    IsLocalization.isNoetherianRing (unitsIn S) _ (norm_isNoetherianRing S)
  haveI : IsIntegrallyClosed (norm S) := norm_isIntegrallyClosed S
  haveI : IsIntegrallyClosed (loc S) :=
    isIntegrallyClosed_of_isLocalization (loc S) (unitsIn S) (unitsIn_le S)
  haveI : IsLocalRing (loc S) := loc_isLocalRing S
  refine ⟨loc S, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance,
    GlobalTheory.VertUnitsNoeth.essFiniteType_loc S, f, (loc S).subtype, hfinj, Subtype.val_injective,
    ⟨fun x hx => isUnit_of_isUnit_coe S x hx⟩, RingHom.ext fun _ => rfl, ?_⟩
  intro p₁ _ hp₁ hfa
  letI : Algebra A (loc S) := f.toAlgebra
  letI : Algebra A T := i.toAlgebra

  have hyint : ∀ p : Ideal A, IsIntegral A (y p) := by
    intro p
    refine ⟨X ^ q - C (π p), monic_X_pow_sub_C _ hq.ne', ?_⟩
    rw [eval₂_sub, eval₂_X_pow, eval₂_C, hy]
    exact sub_self _
  have hgenC : ∀ z ∈ gen S, z ∈ integralClosure A T := by
    intro z hz
    have hle : gen S ≤ (integralClosure A T).restrictScalars ℤ := by
      refine Algebra.adjoin_le ?_
      intro t ht
      simp only [hS, Finset.coe_union, Finset.coe_image, Set.mem_union, Set.mem_image] at ht
      rcases ht with ⟨u, -, rfl⟩ | ⟨p, -, rfl⟩
      · exact isIntegral_algebraMap
      · exact hyint p
    exact hle hz
  have hnormint : ∀ x (hx : x ∈ norm S), IsIntegral A (⟨x, norm_le_loc S hx⟩ : loc S) := by
    intro x hx
    let φ : gen S →+* integralClosure A T :=
      (gen S).val.toRingHom.codRestrict (integralClosure A T) (fun z => hgenC _ z.2)
    have h1 : IsIntegral (integralClosure A T) x :=
      IsIntegral.map_of_comp_eq φ (RingHom.id T) rfl hx.1
    have h2 : IsIntegral A x := isIntegral_trans x h1
    let g : loc S →ₐ[A] T := { (loc S).subtype with commutes' := fun _ => rfl }
    exact (isIntegral_algHom_iff g Subtype.val_injective).mp h2
  let B := integralClosure A (loc S)
  haveI : FaithfulSMul A B := (faithfulSMul_iff_algebraMap_injective A B).mpr
    (fun x x' h => hfinj (congrArg Subtype.val h))
  haveI : Algebra.HasGoingDown A B := inferInstance
  let M : Submonoid B := (IsUnit.submonoid (loc S)).comap (algebraMap B (loc S))
  haveI hML : IsLocalization M (loc S) := by
    refine ⟨fun m => m.2, fun z => ?_, fun {u v} h => ⟨1, ?_⟩⟩
    · obtain ⟨s, hs, hsu, hsz⟩ := z.2
      let sB : B := ⟨⟨s, norm_le_loc S hs⟩, hnormint s hs⟩
      let tB : B := ⟨⟨s * z, norm_le_loc S hsz⟩, hnormint _ hsz⟩
      have hsM : sB ∈ M := isUnit_of_isUnit_coe S _ hsu
      refine ⟨(tB, ⟨sB, hsM⟩), Subtype.ext ?_⟩
      change (z : T) * s = s * z
      ring
    · have : u = v := Subtype.val_injective h
      rw [this]
  set P : Ideal B := p₁.comap (algebraMap B (loc S)) with hP
  have hPh : P.height = 1 := by
    rw [hP, ← hp₁]
    exact IsLocalization.height_under M p₁
  have hcomap : p₁.comap f = P.comap (algebraMap A B) := by
    rw [hP, Ideal.comap_comap, ← IsScalarTower.algebraMap_eq]
    rfl
  have hne : P.comap (algebraMap A B) ≠ ⊥ := by
    rw [← hcomap]
    intro h
    have : a ∈ p₁.comap f := hfa
    rw [h, Ideal.mem_bot] at this
    exact ha this
  have hheight : (p₁.comap f).height = 1 := by
    rw [hcomap]
    exact height_comap_eq_one_of_goingDown P hPh hne

  have hmin : p₁.comap f ∈ (Ideal.span {a}).minimalPrimes := by
    refine ⟨⟨inferInstance, (Ideal.span_singleton_le_iff_mem _).mpr hfa⟩, fun r hr hrp => ?_⟩
    obtain ⟨hrprime, har⟩ := hr
    by_contra hlt
    have hlt' : r < p₁.comap f := lt_of_le_of_ne hrp (fun e => hlt (e ▸ le_rfl))
    haveI : (⊥ : Ideal A).IsPrime := Ideal.isPrime_bot
    have hr0 : (⊥ : Ideal A) < r := by
      refine bot_lt_iff_ne_bot.mpr fun h => ha ?_
      have : a ∈ r := har (Ideal.mem_span_singleton_self a)
      rw [h, Ideal.mem_bot] at this
      exact this
    have h1 := Ideal.height_add_one_le_of_lt_of_isPrime hr0
    have h2 := Ideal.height_add_one_le_of_lt_of_isPrime hlt'
    rw [hheight] at h2
    have h4 : (1 : ℕ∞) ≤ r.height := le_trans le_add_self h1
    have h3 : (1 : ℕ∞) + 1 ≤ 1 := le_trans (by gcongr) h2
    exact absurd h3 (by decide)
  have hyS : y (p₁.comap f) ∈ S := by
    exact Finset.mem_union_right _ (Finset.mem_image_of_mem _ (hfin.mem_toFinset.mpr hmin))
  refine ⟨hheight, π (p₁.comap f), hπ _ hheight, ⟨y (p₁.comap f), mem_loc_of_mem S hyS⟩, ?_⟩
  apply Subtype.ext
  rw [SubmonoidClass.coe_pow]
  exact hy _

end GlobalTheory.KummerEnlarge
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLeIsRootOfSimpleRootPointedEtaleNbhd
section
open IsLocalRing Polynomial

noncomputable section

namespace GlobalTheory.Henselisation

namespace StageHensel

variable {R : Type} [CommRing R] [IsLocalRing R]

theorem trans_algebraMap_eq_of_comp {i j : EtNbhd R} (hij : i ≤ j) (φ : i.A →ₐ[R] j.A)
    (hφ : j.pt.comp φ = i.pt) (a : i.A) :
    EtNbhd.trans hij (algebraMap i.A i.B a) = algebraMap j.A j.B (φ a) := by
  have h1 : EtNbhd.trans hij (algebraMap i.A i.B a) = algebraMap j.A j.B (hij.choose a) :=
    Localization.localRingHom_to_map _ _ _ _ _
  rw [h1]
  have key : (IsScalarTower.toAlgHom R j.A j.B).comp hij.choose =
      (IsScalarTower.toAlgHom R j.A j.B).comp φ := by
    apply GlobalTheory.EtaleHensel.algHom_eq_of_residue_eq
    intro x
    simp only [AlgHom.comp_apply, IsScalarTower.coe_toAlgHom']
    rw [← sub_eq_zero, ← (residue j.B).map_sub (algebraMap j.A j.B (hij.choose x)) (algebraMap j.A j.B (φ x)), residue_eq_zero_iff, ← (algebraMap j.A j.B).map_sub (hij.choose x) (φ x),
      IsLocalization.AtPrime.to_map_mem_maximal_iff j.B j.q]
    show _ ∈ RingHom.ker j.pt
    rw [RingHom.mem_ker, map_sub, sub_eq_zero]
    exact (congr($(hij.choose_spec) x)).trans (congr($hφ x)).symm
  exact congr($key a)

end StageHensel


open StageHensel in
theorem exists_le_isRoot_of_simple_root (R : Type) [CommRing R] [IsLocalRing R] (i : EtNbhd R)
    (h : Polynomial i.A) (a₀ : i.A) (hm : h.Monic) (h0 : i.pt (h.eval a₀) = 0)
    (h1 : i.pt (h.derivative.eval a₀) ≠ 0) :
    ∃ (j : EtNbhd R) (hij : i ≤ j) (c : j.B),
      (h.map ((EtNbhd.trans hij).comp (algebraMap i.A i.B))).IsRoot c ∧
      c - EtNbhd.trans hij (algebraMap i.A i.B a₀) ∈ maximalIdeal j.B := by
  let P : StandardEtalePair i.A := ⟨h, hm, derivative h, ⟨1, 0, 1, by simp⟩⟩
  letI : Algebra R P.Ring := ((algebraMap i.A P.Ring).comp (algebraMap R i.A)).toAlgebra
  haveI : IsScalarTower R i.A P.Ring := IsScalarTower.of_algebraMap_eq' rfl
  haveI : Algebra.Etale R P.Ring := Algebra.Etale.comp R i.A P.Ring
  letI : Algebra i.A (ResidueField R) := (i.pt : i.A →+* ResidueField R).toAlgebra
  haveI : IsScalarTower R i.A (ResidueField R) :=
    IsScalarTower.of_algebraMap_eq' (i.pt.comp_algebraMap).symm
  have hmap : P.HasMap (i.pt a₀) := by
    constructor
    · show eval₂ (i.pt : i.A →+* ResidueField R) ((i.pt : i.A →+* ResidueField R) a₀) h = 0
      rw [eval₂_at_apply]
      exact h0
    · show IsUnit (eval₂ (i.pt : i.A →+* ResidueField R)
        ((i.pt : i.A →+* ResidueField R) a₀) (derivative h))
      rw [eval₂_at_apply]
      exact isUnit_iff_ne_zero.2 h1
  let x : P.Ring →ₐ[R] ResidueField R := (P.lift _ hmap).restrictScalars R
  have hxA : ∀ a : i.A, x (algebraMap i.A P.Ring a) = i.pt a := fun a => (P.lift _ hmap).commutes a
  have hxX : x P.X = i.pt a₀ := P.lift_X _ hmap
  obtain ⟨n, f, hf⟩ :=
    Algebra.FiniteType.iff_quotient_mvPolynomial''.mp (inferInstance : Algebra.FiniteType R P.Ring)
  let e := Ideal.quotientKerAlgEquivOfSurjective hf
  let j : EtNbhd R := ⟨n, RingHom.ker f, Algebra.Etale.of_equiv e.symm, x.comp (e : _ →ₐ[R] P.Ring)⟩
  have hjpt : ∀ y : P.Ring, j.pt (e.symm y) = x y := fun y => by
    show x (e (e.symm y)) = x y
    rw [AlgEquiv.apply_symm_apply]
  let φ : i.A →ₐ[R] j.A := (e.symm : P.Ring →ₐ[R] j.A).comp (IsScalarTower.toAlgHom R i.A P.Ring)
  have hφa : ∀ a, φ a = e.symm (algebraMap i.A P.Ring a) := fun a => rfl
  have hφ : j.pt.comp φ = i.pt := AlgHom.ext fun a => by
    rw [AlgHom.comp_apply, hφa, hjpt, hxA]
  refine ⟨j, ⟨φ, hφ⟩, algebraMap j.A j.B (e.symm P.X), ?_, ?_⟩
  · have hc : (EtNbhd.trans (⟨φ, hφ⟩ : i ≤ j)).comp (algebraMap i.A i.B) =
        ((algebraMap j.A j.B).comp (e.symm : P.Ring →+* j.A)).comp (algebraMap i.A P.Ring) :=
      RingHom.ext fun a => by
        rw [RingHom.comp_apply, trans_algebraMap_eq_of_comp _ φ hφ, hφa]
        rfl
    rw [hc, IsRoot, eval_map]
    have hX := (StandardEtalePair.hasMap_X (P := P)).1
    rw [aeval_def] at hX
    have : eval₂ (((algebraMap j.A j.B).comp (e.symm : P.Ring →+* j.A)).comp
        (algebraMap i.A P.Ring)) (algebraMap j.A j.B (e.symm P.X)) h =
        ((algebraMap j.A j.B).comp (e.symm : P.Ring →+* j.A)) (eval₂ (algebraMap i.A P.Ring) P.X h) := by
      rw [hom_eval₂]
      rfl
    rw [this]
    change _ = (0 : j.B)
    rw [show eval₂ (algebraMap i.A P.Ring) P.X h = 0 from hX, map_zero]
  · haveI : j.q.IsPrime := RingHom.ker_isPrime _
    rw [trans_algebraMap_eq_of_comp _ φ hφ, ← (algebraMap j.A j.B).map_sub (e.symm P.X) (φ a₀), IsLocalization.AtPrime.to_map_mem_maximal_iff j.B j.q]
    show _ ∈ RingHom.ker j.pt
    rw [RingHom.mem_ker, map_sub, hjpt, hxX, sub_eq_zero]
    exact (congr($hφ a₀)).symm

end GlobalTheory.Henselisation

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsNaturalExcisionBoundaryEtaleNbhd
section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

noncomputable section
namespace GlobalTheory.EtC.NatRef

variable {R : Type} [CommRing R]

theorem cpull_comp {K L M : Cx R} (f : K ⟶ L) (g : L ⟶ M) (I : Cx R) (n : ℤ) (x : CohomologyClass M I n) :
    cpull (f ≫ g) I n x = cpull f I n (cpull g I n x) := by
  obtain ⟨x, rfl⟩ := x.mk_surjective
  change CohomologyClass.mk _ = CohomologyClass.mk _
  congr 1; ext1; simp [zcomp, Cochain.ofHom_comp, Cochain.comp_assoc_of_first_is_zero_cochain]

theorem cpull_inr_map {K₁ L₁ K₂ L₂ : Cx R} (φ₁ : K₁ ⟶ L₁) (φ₂ : K₂ ⟶ L₂) (a : K₁ ⟶ K₂) (b : L₁ ⟶ L₂)
    (comm : φ₁ ≫ b = a ≫ φ₂) (I : Cx R) (n : ℤ) (x : CohomologyClass (mappingCone φ₂) I n) :
    cpull (mappingCone.inr φ₁) I n (cpull (mappingCone.map φ₁ φ₂ a b comm) I n x) =
      cpull b I n (cpull (mappingCone.inr φ₂) I n x) := by
  rw [← cpull_comp, ← cpull_comp]
  congr 2
  simp [mappingCone.map]

theorem cpull_map_fst {K₁ L₁ K₂ L₂ : Cx R} (φ₁ : K₁ ⟶ L₁) (φ₂ : K₂ ⟶ L₂) (a : K₁ ⟶ K₂) (b : L₁ ⟶ L₂)
    (comm : φ₁ ≫ b = a ≫ φ₂) (I : Cx R) (n : ℤ) (x : CohomologyClass K₂ I n) :
    cpull (mappingCone.map φ₁ φ₂ a b comm) I (n + 1) (cpre (mappingCone.fst φ₂) I n (n + 1) (by omega) x) =
      cpre (mappingCone.fst φ₁) I n (n + 1) (by omega) (cpull a I n x) := by
  obtain ⟨x, rfl⟩ := x.mk_surjective
  change CohomologyClass.mk _ = CohomologyClass.mk _
  congr 1; ext1
  simp only [zcomp, Cocycle.mk_coe, Cocycle.ofHom_coe]
  have key : (Cochain.ofHom (mappingCone.map φ₁ φ₂ a b comm)).comp (mappingCone.fst φ₂).1 (zero_add 1) =
      (mappingCone.fst φ₁).1.comp (Cochain.ofHom a) (add_zero 1) := by
    refine (mappingCone.ext_cochain_from_iff φ₁ 0 1 rfl).2 ⟨?_, ?_⟩
    · rw [← Cochain.comp_assoc _ _ _ (show -1 + 0 = -1 by omega) (zero_add 1) (by omega), ← Cochain.comp_assoc _ _ _ (show -1 + 1 = 0 by omega) (add_zero 1) (by omega)]
      simp [mappingCone.map, Cochain.comp_assoc_of_second_is_zero_cochain]
    · rw [← Cochain.comp_assoc_of_first_is_zero_cochain, ← Cochain.comp_assoc_of_first_is_zero_cochain]
      simp [mappingCone.map, Cochain.comp_assoc_of_first_is_zero_cochain]
  rw [← Cochain.comp_assoc_of_first_is_zero_cochain, key, Cochain.comp_assoc_of_second_is_zero_cochain]

end GlobalTheory.EtC.NatRef

namespace GlobalTheory.EtC.NatRef
variable {R : Type} [CommRing R]

theorem abstract_nat {K L K' L' : Cx R} (φ : K ⟶ L) (φ' : K' ⟶ L') (a : K' ⟶ K) (b : L' ⟶ L)
    (comm : φ' ≫ b = a ≫ φ) (I : Cx R) (n : ℤ)
    (hbij : Function.Bijective (cpull (mappingCone.map φ' φ a b comm) I (n + 1))) :
    ∃ δ : CohomologyClass K' I n →+ CohomologyClass L I (n + 1),
      Function.Exact δ (fun x : CohomologyClass L I (n + 1) => (cpull φ I (n + 1) x, cpull b I (n + 1) x)) ∧
      ∀ {K₂ L₂ : Cx R} (φ₂ : K₂ ⟶ L₂) (a₂ : K₂ ⟶ K') (b₂ : L₂ ⟶ L') (comm₂ : φ₂ ≫ b₂ = a₂ ≫ φ')
        (a₃ : K₂ ⟶ K) (b₃ : L₂ ⟶ L) (comm₃ : φ₂ ≫ b₃ = a₃ ≫ φ), a₂ ≫ a = a₃ → b₂ ≫ b = b₃ →
        Function.Injective (cpull (mappingCone.map φ₂ φ a₃ b₃ comm₃) I (n + 1)) →
        ∀ (w : CohomologyClass K' I n) (c : CohomologyClass K I n), cpull a₂ I n w = cpull a₃ I n c → δ w = 0 := by
  set m := mappingCone.map φ' φ a b comm
  let e := AddEquiv.ofBijective _ hbij
  have he : ∀ y, cpull m I (n + 1) (e.symm y) = y := e.apply_symm_apply
  have he' : ∀ r, e.symm (cpull m I (n + 1) r) = r := e.symm_apply_apply
  have P1 := (coneSeq_exact R φ I (n + 1)).1
  have P3 := (coneSeq_exact R φ' I n).2.2
  have P3φ := (coneSeq_exact R φ I n).2.2
  refine ⟨(cpull (mappingCone.inr φ) I (n + 1)).comp
    (e.symm.toAddMonoidHom.comp (cpre (mappingCone.fst φ') I n (n + 1) (by omega))), ?_, ?_⟩
  · intro x
    constructor
    · intro hx
      have hx1 : cpull φ I (n + 1) x = 0 := congrArg Prod.fst hx
      have hx2 : cpull b I (n + 1) x = 0 := congrArg Prod.snd hx
      obtain ⟨r, rfl⟩ := (P1 x).1 hx1
      have h0 : cpull (mappingCone.inr φ') I (n + 1) (cpull m I (n + 1) r) = 0 := by
        rw [cpull_inr_map]; exact hx2
      obtain ⟨w, hw⟩ := (P3 _).1 h0
      refine ⟨w, ?_⟩
      change cpull (mappingCone.inr φ) I (n + 1) (e.symm (cpre (mappingCone.fst φ') I n (n + 1) _ w)) = _
      rw [hw, he']
    · rintro ⟨w, rfl⟩
      refine Prod.ext ((P1 _).2 ⟨_, rfl⟩) ?_
      change cpull b I (n + 1) (cpull (mappingCone.inr φ) I (n + 1) (e.symm (cpre (mappingCone.fst φ') I n (n + 1) _ w))) = 0
      rw [← cpull_inr_map φ' φ a b comm, he]
      exact (P3 _).2 ⟨w, rfl⟩
  · intro K₂ L₂ φ₂ a₂ b₂ comm₂ a₃ b₃ comm₃ ha hb hinj w c hwc
    subst ha hb
    have hM : mappingCone.map φ₂ φ (a₂ ≫ a) (b₂ ≫ b) comm₃ =
        mappingCone.map φ₂ φ' a₂ b₂ comm₂ ≫ m := mappingCone.map_comp φ₂ φ' φ a₂ b₂ comm₂ a b comm
    have hr : e.symm (cpre (mappingCone.fst φ') I n (n + 1) (by omega) w) =
        cpre (mappingCone.fst φ) I n (n + 1) (by omega) c := by
      apply hinj
      rw [cpull_map_fst, ← hwc, hM, cpull_comp, he, cpull_map_fst]
    change cpull (mappingCone.inr φ) I (n + 1) (e.symm (cpre (mappingCone.fst φ') I n (n + 1) _ w)) = 0
    rw [hr]
    exact (P3φ _).2 ⟨c, rfl⟩

end GlobalTheory.EtC.NatRef

namespace GlobalTheory.EtC


open NatRef in
theorem excision_boundary_natural_refine : ∀ (q : ℕ) (A A' : Type) [CommRing A] [CommRing A'] [Algebra A A'] (f : A), IsExcisionNbhd A A' f → ∀ (n i : ℤ), ∃ δ : Ht q (sp (Localization.Away (algebraMap A A' f))) n i →+ Ht q (sp A) (n + 1) i, Function.Exact δ (fun x : Ht q (sp A) (n + 1) i => (pull _ (spMap (algebraMap A (Localization.Away f))) _ _ x, pull _ (spMap (algebraMap A A')) _ _ x)) ∧ ∀ (A₂ : Type) [CommRing A₂] [Algebra A A₂] [Algebra A' A₂] [IsScalarTower A A' A₂], IsExcisionNbhd A A₂ f → ∀ (φ : Localization.Away (algebraMap A A' f) →+* Localization.Away (algebraMap A A₂ f)), φ.comp (algebraMap A' _) = (algebraMap A₂ _).comp (algebraMap A' A₂) → ∀ (w : Ht q (sp (Localization.Away (algebraMap A A' f))) n i) (b : Ht q (sp (Localization.Away f)) n i), pull _ (spMap φ) _ _ w = pull _ (spMap (Localization.awayMap (algebraMap A A₂) f)) _ _ b → δ w = 0 := by
  intro q A A' _ _ _ f hN n i
  have hbij : ∀ (B : Type) [CommRing B] [Algebra A B], IsExcisionNbhd A B f →
      Function.Bijective (cpull (excisionConeMap (ZMod q) A B f) (res (ZMod q) (tw q i)) (n + 1)) := by
    intro B _ _ hB
    haveI := GlobalTheory.T.excisionConeMap_quasiIso' (ZMod q) A B f hB
    exact quasiIso_hypercohomology_bijective' (ZMod q) (excisionConeMap (ZMod q) A B f) (tw q i) (n + 1)
  obtain ⟨δ, hex, hnat⟩ := abstract_nat _ _ _ _ (excision_square_comm (ZMod q) A A' f) (res (ZMod q) (tw q i)) n
    (hbij A' hN)
  refine ⟨δ, hex, ?_⟩
  intro A₂ _ _ _ _ h₂ φ hφ w b hwb
  refine hnat ((chains (ZMod q)).map (spMap (algebraMap A₂ (Localization.Away (algebraMap A A₂ f)))))
    ((chains (ZMod q)).map (spMap φ)) ((chains (ZMod q)).map (spMap (algebraMap A' A₂))) ?_ _ _
    (excision_square_comm (ZMod q) A A₂ f) ?_ ?_ (hbij A₂ h₂).1 w b hwb
  · rw [chains_spMap_comp, chains_spMap_comp, hφ]
  · rw [chains_spMap_comp]
    congr 2
    apply IsLocalization.ringHom_ext (Submonoid.powers f)
    rw [RingHom.comp_assoc, awayMap_comp_algebraMap, awayMap_comp_algebraMap, ← RingHom.comp_assoc, hφ,
      RingHom.comp_assoc, ← IsScalarTower.algebraMap_eq]
  · rw [chains_spMap_comp, ← IsScalarTower.algebraMap_eq]

end GlobalTheory.EtC
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTorsorDescentDirectedUnionSubringStatement
section
open IsLocalRing Polynomial
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_torsor_descent_directedUnion_subring : ∀ (T : Type) [CommRing T] [IsDomain T] (ι : Type) [Preorder ι] [IsDirected ι (· ≤ ·)] [Nonempty ι]
    (𝒜 : ι → Subring T), Monotone 𝒜 → (∀ x : T, ∃ i, x ∈ 𝒜 i) →
    ∀ (q : ℕ), 0 < q →
    ∀ (E : Type) [CommRing E] [Algebra (Polynomial T) E] [Algebra T E] [IsScalarTower T (Polynomial T) E]
      [Algebra.Etale (Polynomial T) E] (Q : Ideal E) [Q.IsPrime]
      (D₁ : Type) [CommRing D₁] [Algebra (GlobalTheory.LocAcyc.GenFib T (Localization.AtPrime Q)) D₁]
      (act₁ : Multiplicative (ZMod q) →* (D₁ ≃ₐ[GlobalTheory.LocAcyc.GenFib T (Localization.AtPrime Q)] D₁)),
      GlobalTheory.KeyOriginCut.IsZTorsor (GlobalTheory.LocAcyc.GenFib T (Localization.AtPrime Q)) D₁ q act₁ →
    ∃ (i : ι) (EA : Type) (_ : CommRing EA) (_ : Algebra (Polynomial (𝒜 i)) EA) (_ : Algebra (𝒜 i) EA)
      (_ : IsScalarTower (𝒜 i) (Polynomial (𝒜 i)) EA) (_ : Algebra.Etale (Polynomial (𝒜 i)) EA) (e : EA →+* E),
      e.comp (algebraMap (Polynomial (𝒜 i)) EA) =
        (algebraMap (Polynomial T) E).comp (Polynomial.mapRingHom (𝒜 i).subtype) ∧
      ∃ (β : GlobalTheory.LocAcyc.GenFib (𝒜 i) (Localization.AtPrime (Q.comap e)) →+*
          GlobalTheory.LocAcyc.GenFib T (Localization.AtPrime Q)),
        β.comp (algebraMap (Localization.AtPrime (Q.comap e))
            (GlobalTheory.LocAcyc.GenFib (𝒜 i) (Localization.AtPrime (Q.comap e)))) =
          (algebraMap (Localization.AtPrime Q) (GlobalTheory.LocAcyc.GenFib T (Localization.AtPrime Q))).comp
            (Localization.localRingHom (Q.comap e) Q e rfl) ∧
      ∃ (D : Type) (_ : CommRing D) (_ : Algebra (GlobalTheory.LocAcyc.GenFib (𝒜 i) (Localization.AtPrime (Q.comap e))) D)
        (actA : Multiplicative (ZMod q) →* (D ≃ₐ[GlobalTheory.LocAcyc.GenFib (𝒜 i) (Localization.AtPrime (Q.comap e))] D)),
        GlobalTheory.KeyOriginCut.IsZTorsor (GlobalTheory.LocAcyc.GenFib (𝒜 i) (Localization.AtPrime (Q.comap e))) D q actA ∧
        ∀ (C : Type) [CommRing C] (ψ : GlobalTheory.LocAcyc.GenFib T (Localization.AtPrime Q) →+* C) (σ : D →+* C),
          σ.comp (algebraMap (GlobalTheory.LocAcyc.GenFib (𝒜 i) (Localization.AtPrime (Q.comap e))) D) = ψ.comp β →
          ∃ σ₁ : D₁ →+* C, σ₁.comp (algebraMap (GlobalTheory.LocAcyc.GenFib T (Localization.AtPrime Q)) D₁) = ψ := by
  first | (exact @GlobalTheory.TorsorUnionDescent.exists_stage_torsor) | (exact GlobalTheory.TorsorUnionDescent.exists_stage_torsor) | (intros; apply GlobalTheory.TorsorUnionDescent.exists_stage_torsor  <;> assumption)
end

