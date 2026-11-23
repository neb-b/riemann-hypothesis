module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.BijectiveAlgebraMapIntegralClosureOfBirational
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0069
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0009
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ChartPullbacks.BaseChangeKernels.Bundle0001
public import ReciprocityTheory.CommutativeAlgebra.MaximalIdealSquares.RingKrullDimQuotientSpanSingletonAddOne
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0042
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0001
public import Formalism.SatakeDualWeyl.Statement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0082
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0071
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0062

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsOpenImmersionSpecOfQuasiFiniteOfNormal
section
open CategoryTheory AlgebraicGeometry

namespace GlobalTheory

theorem eq_of_minimalPrimes_le_of_isDomain_localization {A : Type} [CommRing A]
    (hA : ∀ (P : Ideal A) [P.IsPrime], IsDomain (Localization.AtPrime P))
    {P p q : Ideal A} [P.IsPrime] (hp : p ∈ minimalPrimes A) (hq : q ∈ minimalPrimes A)
    (hpP : p ≤ P) (hqP : q ≤ P) : p = q := by
  haveI := hA P
  let K := RingHom.ker (algebraMap A (Localization.AtPrime P))
  have hK : K.IsPrime := RingHom.ker_isPrime _
  have hle : ∀ Q : Ideal A, Q.IsPrime → Q ≤ P → K ≤ Q := by
    intro Q hQ hQP
    have h := IsLocalization.under_map_of_isPrime_disjoint P.primeCompl (Localization.AtPrime P) hQ
      (Set.disjoint_left.2 fun x hx hxQ ↦ hx (hQP hxQ))
    rw [← h]
    intro x hx
    rw [RingHom.mem_ker] at hx
    simp [Ideal.mem_comap, hx]
  have h1 : K = p := le_antisymm (hle p hp.1.1 hpP) (hp.2 ⟨hK, bot_le⟩ (hle p hp.1.1 hpP))
  have h2 : K = q := le_antisymm (hle q hq.1.1 hqP) (hq.2 ⟨hK, bot_le⟩ (hle q hq.1.1 hqP))
  exact h1.symm.trans h2

theorem isOpen_zeroLocus_of_mem_minimalPrimes {A : Type} [CommRing A] [IsNoetherianRing A]
    (hA : ∀ (P : Ideal A) [P.IsPrime], IsDomain (Localization.AtPrime P))
    {p : Ideal A} (hp : p ∈ minimalPrimes A) : IsOpen (PrimeSpectrum.zeroLocus (p : Set A)) := by
  have hfin := (minimalPrimes.finite_of_isNoetherianRing A).subset (Set.diff_subset (t := {p}))
  have heq : (PrimeSpectrum.zeroLocus (p : Set A))ᶜ =
      ⋃ q ∈ minimalPrimes A \ {p}, PrimeSpectrum.zeroLocus (q : Set A) := by
    ext x
    simp only [Set.mem_compl_iff, PrimeSpectrum.mem_zeroLocus, SetLike.coe_subset_coe,
      Set.mem_iUnion, Set.mem_diff, Set.mem_singleton_iff, exists_prop]
    constructor
    · intro hx
      obtain ⟨q, hq, hqx⟩ := Ideal.exists_minimalPrimes_le (I := ⊥) (J := x.asIdeal) bot_le
      refine ⟨q, ⟨hq, ?_⟩, hqx⟩
      rintro rfl
      exact hx hqx
    · rintro ⟨q, ⟨hq, hne⟩, hqx⟩ hpx
      exact hne (eq_of_minimalPrimes_le_of_isDomain_localization hA hq hp hqx hpx)
  rw [← isClosed_compl_iff, heq]
  exact hfin.isClosed_biUnion fun q _ ↦ PrimeSpectrum.isClosed_zeroLocus _

end GlobalTheory

namespace GlobalTheory

theorem isOpenImmersion_spec_of_quasiFinite_of_normal {A B : Type} [CommRing A] [CommRing B]
    [IsDomain B] [IsNoetherianRing A] (φ : A →+* B)
    (hA : ∀ (𝔭 : Ideal A) [𝔭.IsPrime],
      IsDomain (Localization.AtPrime 𝔭) ∧ IsIntegrallyClosed (Localization.AtPrime 𝔭))
    (hφ : φ.FiniteType) (hqf : LocallyQuasiFinite (Spec.map (CommRingCat.ofHom φ)))
    (hV : ∃ V : (Spec (CommRingCat.of B)).Opens, Nonempty V ∧
      IsOpenImmersion (V.ι ≫ Spec.map (CommRingCat.ofHom φ))) :
    IsOpenImmersion (Spec.map (CommRingCat.ofHom φ)) := by
  obtain ⟨V, hVne, hVo⟩ := hV
  set f := Spec.map (CommRingCat.ofHom φ) with hf
  have hAd : ∀ (P : Ideal A) [P.IsPrime], IsDomain (Localization.AtPrime P) :=
    fun P _ ↦ (hA P).1
  have hft : LocallyOfFiniteType f :=
    (HasRingHomProperty.Spec_iff (P := @LocallyOfFiniteType)).mpr hφ
  let η := genericPoint (Spec (CommRingCat.of B))
  have hηV : η ∈ V :=
    ((genericPoint_spec _).mem_open_set_iff V.isOpen).mpr (by simpa using hVne)
  let y₀ : PrimeSpectrum A := f η
  have hsp : ∀ x, y₀ ⤳ f x := fun x ↦ (genericPoint_specializes x).map f.continuous

  have hW : IsOpen (Set.range (V.ι ≫ f)) := (V.ι ≫ f).isOpenEmbedding.isOpen_range
  have hy₀W : y₀ ∈ Set.range (V.ι ≫ f) := ⟨⟨η, hηV⟩, rfl⟩
  have hmin : y₀.asIdeal ∈ minimalPrimes A := by
    refine ⟨⟨y₀.isPrime, bot_le⟩, fun q hq hle ↦ ?_⟩
    let z : PrimeSpectrum A := ⟨q, hq.1⟩
    have hz : z ⤳ y₀ := (PrimeSpectrum.le_iff_specializes z y₀).1 hle
    obtain ⟨v, hv⟩ := hz.mem_open hW hy₀W
    have h2 : y₀ ≤ z := by
      rw [← hv, Scheme.Hom.comp_apply]
      exact (PrimeSpectrum.le_iff_specializes _ _).2 (hsp _)
    exact h2

  have hZo : IsOpen (closure ({y₀} : Set (PrimeSpectrum A))) := by
    rw [PrimeSpectrum.closure_singleton]
    exact isOpen_zeroLocus_of_mem_minimalPrimes hAd hmin
  let Z : (Spec (CommRingCat.of A)).Opens := ⟨closure ({y₀} : Set (PrimeSpectrum A)), hZo⟩
  have hrange : Set.range f ⊆ Set.range Z.ι := by
    rintro _ ⟨x, rfl⟩
    rw [Scheme.Opens.range_ι]
    exact specializes_iff_mem_closure.1 (hsp x)
  let g : Spec (CommRingCat.of B) ⟶ Z.toScheme := IsOpenImmersion.lift Z.ι f hrange
  have hgf : g ≫ Z.ι = f := IsOpenImmersion.lift_fac _ _ _

  haveI : _root_.IsReduced A := isReduced_ofLocalizationMaximal A fun P _ ↦ by
    haveI := hAd P; infer_instance
  haveI : Nonempty Z.toScheme := ⟨⟨y₀, subset_closure rfl⟩⟩
  haveI : IrreducibleSpace Z.toScheme :=
    Subtype.irreducibleSpace (isIrreducible_singleton (x := y₀)).closure
  haveI : IsIntegral Z.toScheme := isIntegral_of_irreducibleSpace_of_isReduced _
  have hZ : ∀ z : Z.toScheme, IsIntegrallyClosed (Z.toScheme.presheaf.stalk z) := by
    intro z
    have e₁ := asIso (Z.ι.stalkMap z)
    let x : PrimeSpectrum A := Z.ι z
    have hloc : IsLocalization.AtPrime ((Spec.structureSheaf A).presheaf.stalk x) x.asIdeal :=
      StructureSheaf.IsLocalization.to_stalk A x
    have e₂ := IsLocalization.algEquiv x.asIdeal.primeCompl
      ((Spec.structureSheaf A).presheaf.stalk x) (Localization.AtPrime x.asIdeal)
    haveI := (hA x.asIdeal).2
    have hic : IsIntegrallyClosed ((Spec.structureSheaf A).presheaf.stalk x) :=
      IsIntegrallyClosed.of_equiv e₂.symm.toRingEquiv
    haveI : IsIntegrallyClosed ((Spec (CommRingCat.of A)).presheaf.stalk (Z.ι z)) := hic
    exact IsIntegrallyClosed.of_equiv (e₁.commRingCatIsoToRingEquiv)

  haveI : IsSeparated g := IsSeparated.of_comp g Z.ι
  haveI : QuasiCompact g := QuasiCompact.of_comp g Z.ι
  haveI : LocallyOfFiniteType (g ≫ Z.ι) := by rw [hgf]; exact hft
  haveI : LocallyOfFiniteType g := locallyOfFiniteType_of_comp g Z.ι
  haveI : LocallyQuasiFinite (g ≫ Z.ι) := by rw [hgf]; exact hqf
  haveI : LocallyQuasiFinite g := LocallyQuasiFinite.of_comp g Z.ι
  haveI : IsOpenImmersion ((V.ι ≫ g) ≫ Z.ι) := by rw [Category.assoc, hgf]; exact hVo
  haveI : IsOpenImmersion (V.ι ≫ g) := IsOpenImmersion.of_comp _ Z.ι
  have := isOpenImmersion_of_quasiFinite_of_isOpenImmersion_restrict g hZ V hVne
  rw [← hgf]
  infer_instance

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsOpenOfStableUnderGeneralizationOfLocallyClosed
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj TopologicalSpace TensorProduct
open scoped CategoryTheory.Obj

namespace GlobalTheory

theorem isOpen_of_stableUnderGeneralization_of_locallyClosed_pieces :
    ∀ (X : Scheme.{0}) (Z : Set X), StableUnderGeneralization Z → (∀ x ∈ Z, ∃ (W W' : X.Opens) (J : Finset Γ(X, W')), W ≤ W' ∧ x ∈ W ∧ (∀ c ∈ J, x ∉ X.basicOpen c) ∧ ∀ y ∈ W, (∀ c ∈ J, y ∉ X.basicOpen c) → y ∈ Z) → IsOpen Z := by
  classical
  intro X Z hZ hpc
  rw [isOpen_iff_forall_mem_open]
  intro x hx
  obtain ⟨_, ⟨U, hU, rfl⟩, hxU, -⟩ :=
    X.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ x) isOpen_univ
  have hU : IsAffineOpen U := hU
  have key : ∀ (p : PrimeSpectrum Γ(X, U)) (a : Γ(X, U)),
      hU.fromSpec p ∈ X.basicOpen a ↔ a ∉ p.asIdeal := by
    intro p a
    have h := hU.fromSpec_preimage_basicOpen a
    have h2 : p ∈ hU.fromSpec ⁻¹ᵁ X.basicOpen a ↔ p ∈ PrimeSpectrum.basicOpen a := by
      rw [h]; rfl
    exact h2
  have hopen : IsOpen (X := PrimeSpectrum Γ(X, U)) (hU.fromSpec ⁻¹' Z) := by
    refine GlobalTheory.isOpen_of_stableUnderGeneralization_of_constructible_pieces Γ(X, U) _ ?_ ?_
    · intro p q hpq hp
      exact hZ (hpq.map hU.fromSpec.continuous) hp
    · intro p hp
      obtain ⟨W, W', J, hWW', hpW, hpJ, hsub⟩ := hpc _ hp
      have hpU : hU.fromSpec p ∈ U := hU.range_fromSpec.le ⟨p, rfl⟩
      obtain ⟨a, haW, hpa⟩ := hU.exists_basicOpen_le (V := W) ⟨_, hpW⟩ hpU
      have hc : ∀ c : Γ(X, W'), ∃ c' : Γ(X, U),
          X.basicOpen c' = X.basicOpen a ⊓ X.basicOpen c := by
        intro c
        obtain ⟨c', hc'⟩ := hU.basicOpen_basicOpen_is_basicOpen a
          (X.presheaf.map (homOfLE (haW.trans hWW')).op c)
        exact ⟨c', by rw [hc', Scheme.basicOpen_res]⟩
      choose g hg using hc
      refine ⟨a, J.image g, (key p a).1 hpa, ?_, ?_⟩
      · intro c' hc'
        obtain ⟨c, hcJ, rfl⟩ := Finset.mem_image.1 hc'
        by_contra hn
        have := (key p _).2 hn
        rw [hg] at this
        exact hpJ c hcJ this.2
      · intro t hta htI
        have hta' := (key t a).2 hta
        refine hsub _ (haW hta') fun c hcJ htc => ?_
        refine (key t (g c)).1 ?_ (htI _ (Finset.mem_image_of_mem g hcJ))
        rw [hg]
        exact ⟨hta', htc⟩
  refine ⟨hU.fromSpec '' (hU.fromSpec ⁻¹' Z), Set.image_preimage_subset _ _,
    hU.fromSpec.isOpenEmbedding.isOpenMap _ hopen, ?_⟩
  obtain ⟨p, rfl⟩ := hU.range_fromSpec.ge hxU
  exact ⟨p, hx, rfl⟩

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsPullbackPbMap
section
noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite

namespace GlobalTheory.HilbAff

variable {A B : Type} [CommRing A] [CommRing B] [Algebra A B] {r : ℕ}

abbrev proj {T : Scheme.{0}} (y : (functor A B r).obj (op T)) : y.2.1.subscheme ⟶ T :=
  y.2.1.subschemeι ≫ pullback.snd _ y.1

def gens {N : ℕ} (e : Module.Basis (Fin N) A B) (σ : Fin r ↪ Fin N) {T : Scheme.{0}}
    (y : (functor A B r).obj (op T)) (U : T.Opens) : Fin r → Γ(y.2.1.subscheme, proj y ⁻¹ᵁ U) :=
  fun k => ((y.2.1.subschemeι ≫ pullback.fst _ y.1).appLE ⊤ (proj y ⁻¹ᵁ U) (by simp)).hom
    ((Scheme.ΓSpecIso (CommRingCat.of B)).inv.hom (e (σ k)))

def bad {N : ℕ} (e : Module.Basis (Fin N) A B) (σ : Fin r ↪ Fin N) {T : Scheme.{0}}
    (y : (functor A B r).obj (op T)) (U : T.Opens) : Set (PrimeSpectrum Γ(T, U)) :=
  letI := ((proj y).app U).hom.toAlgebra
  Module.support Γ(T, U)
    (Γ(y.2.1.subscheme, proj y ⁻¹ᵁ U) ⧸ Submodule.span Γ(T, U) (Set.range (gens e σ y U)))

def goodSet {N : ℕ} (e : Module.Basis (Fin N) A B) (σ : Fin r ↪ Fin N) {T : Scheme.{0}}
    (y : (functor A B r).obj (op T)) : Set T :=
  ⋃ U : T.affineOpens, U.2.fromSpec '' (bad e σ y U)ᶜ

def pbMap {T T' : Scheme.{0}} (a : T' ⟶ T) (y : (functor A B r).obj (op T)) :
    ((functor A B r).map a.op y).2.1.subscheme ⟶ y.2.1.subscheme :=
  (y.2.1.comapIso (bc A B y.1 a)).hom ≫ pullback.snd _ _

theorem isPullback_pbMap {T T' : Scheme.{0}} (a : T' ⟶ T) (y : (functor A B r).obj (op T)) :
    IsPullback (pbMap a y) (proj ((functor A B r).map a.op y)) (proj y) a := by
  have H : IsPullback (pullback.snd (bc A B y.1 a) y.2.1.subschemeι)
      (pullback.fst (bc A B y.1 a) y.2.1.subschemeι ≫ pullback.snd _ (a ≫ y.1))
      (y.2.1.subschemeι ≫ pullback.snd _ y.1) a :=
    (IsPullback.of_hasPullback (bc A B y.1 a) y.2.1.subschemeι).flip.paste_vert
      (isPullback_bc A B y.1 a)
  refine IsPullback.of_iso H (y.2.1.comapIso (bc A B y.1 a)).symm (Iso.refl _) (Iso.refl _)
    (Iso.refl _) ?_ ?_ ?_ ?_
  · simp only [pbMap, Iso.symm_hom, Iso.refl_hom, Category.comp_id, Category.id_comp]
    exact (Iso.inv_hom_id_assoc _ _).symm
  · change _ = (y.2.1.comapIso (bc A B y.1 a)).inv ≫
      (y.2.1.comap (bc A B y.1 a)).subschemeι ≫ pullback.snd _ (a ≫ y.1)
    rw [Scheme.IdealSheafData.comapIso_inv_subschemeι_assoc]
    simp
  · simp
  · simp

theorem pbMap_fst {T T' : Scheme.{0}} (a : T' ⟶ T) (y : (functor A B r).obj (op T)) :
    pbMap a y ≫ y.2.1.subschemeι ≫ pullback.fst _ y.1 =
      ((functor A B r).map a.op y).2.1.subschemeι ≫ pullback.fst _ ((functor A B r).map a.op y).1 := by
  change (y.2.1.comapIso (bc A B y.1 a)).hom ≫ pullback.snd _ _ ≫
      y.2.1.subschemeι ≫ pullback.fst _ y.1 =
    (y.2.1.comap (bc A B y.1 a)).subschemeι ≫ pullback.fst _ (a ≫ y.1)
  rw [← pullback.condition_assoc, Scheme.IdealSheafData.comapIso_hom_fst_assoc]
  congr 1
  exact (pullback.lift_fst _ _ _).trans (Category.comp_id _)

end GlobalTheory.HilbAff
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsPushoutAppLEOfIsPullbackOfIsAffine
section
open AlgebraicGeometry CategoryTheory Limits

set_option autoImplicit false

namespace GlobalTheory.AffBaseChange

theorem isPushout_appLE_of_isPullback_of_isAffine :
    ∀ (X X' S S' : Scheme.{0}) (f : X' ⟶ X) (g : X' ⟶ S') (p : X ⟶ S) (q : S' ⟶ S),
      IsPullback f g p q → IsAffine S → IsAffine S' → ∀ (W : X.Opens), IsAffineOpen W →
      IsPushout (p.appLE ⊤ W (fun _ _ => trivial)) q.appTop (f.app W)
        (g.appLE ⊤ (f ⁻¹ᵁ W) (fun _ _ => trivial)) := by
  intro X X' S S' f g p q h hS hS' W hW
  haveI : IsAffineHom q := inferInstance
  have P := ReciprocityTheory.ChartRestriction.G.Out.GtBCPf.isPushout_appLE h.flip this (isAffineOpen_top S) hW
    (fun _ _ => trivial) (fun _ _ => trivial)
  exact P.flip

end GlobalTheory.AffBaseChange
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsRegularLocalRingOfRegularQuotient
section
open IsLocalRing TensorProduct

namespace GlobalTheory.RegularAscent

theorem height_add_ringKrullDim_quotient_le {R : Type} [CommRing R] (p : Ideal R) [hp : p.IsPrime] :
    ((p.height : ℕ∞) : WithBot ℕ∞) + ringKrullDim (R ⧸ p) ≤ ringKrullDim R := by
  let P : PrimeSpectrum R := ⟨p, hp⟩
  haveI : Nonempty (PrimeSpectrum R) := ⟨P⟩
  have h1 : PrimeSpectrum.zeroLocus (p : Set R) = Set.Ici P := by
    ext x
    simp only [PrimeSpectrum.mem_zeroLocus, Set.mem_Ici]
    rfl
  have h2 : ringKrullDim (R ⧸ p) = (Order.coheight P : ℕ∞) := by
    rw [ringKrullDim_quotient, h1, Order.coheight_eq_krullDim_Ici]
  have h3 : p.height = Order.height P := PrimeSpectrum.height_eq_orderHeight P
  rw [h2, h3, ← WithBot.coe_add]
  change _ ≤ Order.krullDim (PrimeSpectrum R)
  rw [Order.krullDim_eq_iSup_height_add_coheight_of_nonempty, WithBot.coe_le_coe]
  exact le_iSup (fun x : PrimeSpectrum R => Order.height x + Order.coheight x) P

end GlobalTheory.RegularAscent
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsRootMapMinpolyIffExistsRingHomExtension
section
open Polynomial
namespace GlobalTheory

theorem exists_ringHom_extension_algClosed_of_isIntegral_injective {R S K : Type*} [CommRing R] [CommRing S] [Field K] [IsAlgClosed K]
    [Algebra R S] [Algebra.IsIntegral R S] (hinj : Function.Injective (algebraMap R S))
    (ψ : R →+* K) : ∃ x : S →+* K, x.comp (algebraMap R S) = ψ := by
  first
  | (run_tac Lean.Elab.Tactic.liftMetaTactic (fun g => do pure [← g.revertAll])); exact @_root_.GlobalTheory.InjectiveAlgebraHomExistence.exists_ringHom_comp_algebraMap_eq
  | (run_tac Lean.Elab.Tactic.liftMetaTactic (fun g => do pure [← g.revertAll])); exact _root_.GlobalTheory.InjectiveAlgebraHomExistence.exists_ringHom_comp_algebraMap_eq
  | exact @_root_.GlobalTheory.InjectiveAlgebraHomExistence.exists_ringHom_comp_algebraMap_eq
  | exact _root_.GlobalTheory.InjectiveAlgebraHomExistence.exists_ringHom_comp_algebraMap_eq
  | (apply _root_.GlobalTheory.InjectiveAlgebraHomExistence.exists_ringHom_comp_algebraMap_eq <;> assumption)
  | (intros; apply _root_.GlobalTheory.InjectiveAlgebraHomExistence.exists_ringHom_comp_algebraMap_eq <;> assumption)
  | (intros; apply @_root_.GlobalTheory.InjectiveAlgebraHomExistence.exists_ringHom_comp_algebraMap_eq <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.InjectiveAlgebraHomExistence.exists_ringHom_comp_algebraMap_eq ..)

theorem isRoot_map_minpoly_iff_exists_ringHom : ∀ (A B : Type) [CommRing A] [IsDomain A] [IsIntegrallyClosed A] [CommRing B] [IsDomain B] [Algebra A B] [Algebra.IsIntegral A B], Function.Injective (algebraMap A B) → ∀ (g : B) (φ : A →+* ℂ) (z : ℂ), ((minpoly A g).map φ).IsRoot z ↔ ∃ x : B →+* ℂ, x.comp (algebraMap A B) = φ ∧ x g = z := by
  intro A B _ _ _ _ _ _ _ hinj g φ z
  constructor
  · intro h
    haveI : FaithfulSMul A B := (faithfulSMul_iff_algebraMap_injective _ _).2 hinj
    have hg : IsIntegral A g := Algebra.IsIntegral.isIntegral g
    have h' : (minpoly A g).eval₂ φ z = 0 := by rwa [IsRoot, eval_map] at h
    let e := minpoly.equivAdjoin hg
    let ψ : Algebra.adjoin A {g} →+* ℂ := (AdjoinRoot.lift φ z h').comp (e.symm : _ →+* _)
    haveI : Algebra.IsIntegral (Algebra.adjoin A {g}) B := Algebra.IsIntegral.tower_top A
    obtain ⟨x, hx⟩ := exists_ringHom_extension_algClosed_of_isIntegral_injective (S := B) Subtype.val_injective ψ
    have hx' : ∀ r : Algebra.adjoin A {g}, x r = ψ r := fun r => RingHom.congr_fun hx r
    refine ⟨x, ?_, ?_⟩
    · ext a
      have := hx' (algebraMap A _ a)
      simp only [ψ, RingHom.comp_apply, RingHom.coe_coe, AlgEquiv.commutes, AdjoinRoot.algebraMap_eq, AdjoinRoot.lift_of] at this
      exact this
    · have h1 : (e (AdjoinRoot.root _) : B) = g := by
        change ((AdjoinRoot.Minpoly.toAdjoin A g (AdjoinRoot.root _) : Algebra.adjoin A {g}) : B) = g
        simp [AdjoinRoot.Minpoly.toAdjoin]
      have := hx' (e (AdjoinRoot.root _))
      simp only [ψ, RingHom.comp_apply, RingHom.coe_coe, AlgEquiv.symm_apply_apply, AdjoinRoot.lift_root] at this
      rwa [h1] at this
  · rintro ⟨x, rfl, rfl⟩
    rw [IsRoot, eval_map, ← hom_eval₂, ← aeval_def, minpoly.aeval, map_zero]

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsSLTwoPermutedModularFamilyIffValues
section
open scoped UpperHalfPlane MatrixGroups ModularForm Manifold BigOperators
open GlobalTheory.QFam

namespace GlobalTheory.QFam

theorem isFam_iff_values (ι : Type) (act : ι → SL(2, ℤ) → ι) (w : ℤ) (f : ι → ℍ → ℂ) :
    IsFam act w f ↔ ∀ (i : ι) (γ : SL(2, ℤ)) (τ : ℍ),
      f i (γ • τ) = (((γ 1 0 : ℤ) : ℂ) * τ + ((γ 1 1 : ℤ) : ℂ)) ^ w * f (act i γ) τ := by
  unfold IsFam
  refine forall_congr' fun i => forall_congr' fun γ => ?_
  rw [funext_iff]
  refine forall_congr' fun τ => ?_
  have hD : UpperHalfPlane.denom γ τ = ((γ 1 0 : ℤ) : ℂ) * τ + ((γ 1 1 : ℤ) : ℂ) := by
    simp [UpperHalfPlane.denom]
  have hne : UpperHalfPlane.denom γ τ ≠ 0 := UpperHalfPlane.denom_ne_zero _ τ
  rw [ModularForm.SL_slash_apply, zpow_neg, mul_inv_eq_iff_eq_mul₀ (zpow_ne_zero _ hne), hD,
    mul_comm (f (act i γ) τ)]

end GlobalTheory.QFam
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsSelfDualImageStandardLatticeUnitary
section
open Polynomial Matrix GlobalTheory.LatOrb

namespace GlobalTheory.LatOrb

theorem herm_mulVec_right {K : Type} [Field K] (σ : K →+* K)
    {n : ℕ} (g : Matrix (Fin n) (Fin n) K) (y u : Fin n → K) :
    herm σ y (g *ᵥ u) = herm σ ((g.map σ)ᵀ *ᵥ y) u := by
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [herm, mulVec, dotProduct, map_sum, map_mul, Matrix.transpose_apply, Matrix.map_apply,
    Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun j _ => Finset.sum_congr rfl (fun k _ => ?_))
  ring

theorem selfDual_matLat_stdLat {O K : Type} [CommRing O] [Field K] [Algebra O K] (σ : K →+* K)
    (_hinv : ∀ x, σ (σ x) = x) (hO : ∀ a : O, ∃ b : O, σ (algebraMap O K a) = algebraMap O K b)
    (n : ℕ) (g : Matrix (Fin n) (Fin n) K) (hg : (g.map σ)ᵀ * g = 1) :
    SelfDual O σ (matLat O g (stdLat O n)) := by
  have hg' : g * (g.map σ)ᵀ = 1 := mul_eq_one_comm.mp hg
  have hσO : ∀ z ∈ (algebraMap O K).range, σ z ∈ (algebraMap O K).range := by
    rintro z ⟨a, rfl⟩
    obtain ⟨b, hb⟩ := hO a
    exact ⟨b, hb.symm⟩
  intro y
  rw [mem_matLat]
  constructor
  · rintro ⟨u, hu, rfl⟩ x hx
    rw [mem_matLat] at hx
    obtain ⟨v, hv, rfl⟩ := hx
    rw [herm_mulVec_right, Matrix.mulVec_mulVec, hg, Matrix.one_mulVec]
    unfold herm
    refine Subring.sum_mem _ (fun k _ => Subring.mul_mem _ ((mem_stdLat u).mp hu k) (hσO _ ((mem_stdLat v).mp hv k)))
  · intro h
    refine ⟨(g.map σ)ᵀ *ᵥ y, ?_, by rw [Matrix.mulVec_mulVec, hg', Matrix.one_mulVec]⟩
    rw [mem_stdLat]
    intro j
    have hx : g *ᵥ (Pi.single j 1 : Fin n → K) ∈ matLat O g (stdLat O n) := by
      rw [mem_matLat]
      refine ⟨Pi.single j 1, ?_, rfl⟩
      rw [mem_stdLat]
      intro i
      by_cases hij : i = j
      · subst hij; exact ⟨1, by simp⟩
      · exact ⟨0, by simp [Pi.single_apply, hij]⟩
    have := h _ hx
    rw [herm_mulVec_right] at this
    simpa [herm, Pi.single_apply, map_one] using this

end GlobalTheory.LatOrb
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsolateMaximalAmongPrimesContainingEtaleStatement
section
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isolate_maximal_among_primes_containing_etale : ∀ (B D : Type) [CommRing B] [IsDedekindDomain B] [CommRing D] [Algebra B D] [Algebra.Etale B D] (f : B), f ≠ 0 → ∀ (Q : Ideal D), Q.IsMaximal → ∃ g : D, g ∉ Q ∧ ∀ Q' : Ideal D, Q'.IsPrime → algebraMap B D f ∈ Q' → g ∉ Q' → Q' = Q := by
  first | (exact @GlobalTheory.EtaleIsolate.isolate_maximal_among_primes_containing) | (exact GlobalTheory.EtaleIsolate.isolate_maximal_among_primes_containing) | (intros; apply GlobalTheory.EtaleIsolate.isolate_maximal_among_primes_containing  <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.KaehlerFibreEquivPushoutFormallyEtale
section
open scoped TensorProduct Polynomial

namespace GlobalTheory


open KaehlerDifferential TensorProduct in
theorem kaehler_fibre_equiv_pushout_formallyEtale :
    ∀ (R R' B C B' K : Type) [CommRing R] [CommRing R'] [CommRing B] [CommRing C] [CommRing B'] [Field K] [Algebra R R'] [Algebra R B] [Algebra R C] [Algebra R' C] [Algebra B C] [IsScalarTower R R' C] [IsScalarTower R B C] [Algebra.IsPushout R R' B C] [Algebra C B'] [Algebra R' B'] [IsScalarTower R' C B'] [Algebra.FormallyEtale C B'] [Algebra B' K] [Algebra B K], (∀ x : B, algebraMap B K x = algebraMap B' K (algebraMap C B' (algebraMap B C x))) → ∃ e : (K ⊗[B] Ω[B⁄R]) ≃ₗ[K] (K ⊗[B'] Ω[B'⁄R']), ∀ x : B, e ((1 : K) ⊗ₜ[B] KaehlerDifferential.D R B x) = (1 : K) ⊗ₜ[B'] KaehlerDifferential.D R' B' (algebraMap C B' (algebraMap B C x)) := by
  first
  | exact @_root_.GlobalTheory.AuxiliaryLemmaFirst.main
  | exact _root_.GlobalTheory.AuxiliaryLemmaFirst.main
  | (apply _root_.GlobalTheory.AuxiliaryLemmaFirst.main <;> assumption)
  | (intros; apply _root_.GlobalTheory.AuxiliaryLemmaFirst.main <;> assumption)
  | (intros; apply @_root_.GlobalTheory.AuxiliaryLemmaFirst.main <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.AuxiliaryLemmaFirst.main ..)

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.KerAevalOrthogonalRangeUnitarySelfReciprocalStatement
section
open Matrix Polynomial
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.ker_aeval_orthogonal_range_unitary_selfReciprocal : ∀ {K : Type} [Field K] (σ : K →+* K) {n : ℕ} (γ : Matrix (Fin n) (Fin n) K), (γ.map σ)ᵀ * γ = 1 → ∀ (Q : K[X]), C (σ (Q.coeff 0)) * Q = (Q.map σ).reverse → ∀ (x z : Fin n → K), aeval γ Q *ᵥ x = 0 → ∑ k, σ ((aeval γ Q *ᵥ z) k) * x k = 0 := by
  first | exact @GlobalTheory.csr_ker_orth_range | exact GlobalTheory.csr_ker_orth_range | (intros; apply GlobalTheory.csr_ker_orth_range <;> assumption)
end

