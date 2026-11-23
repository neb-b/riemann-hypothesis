module

public import Mathlib
public import ReciprocityTheory.AnalyticForms.RegularLocalRings.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0012
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0016
public import GroundTheory.GlobalFields.Artin.LogCharpoly
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0017
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0008
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0018

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.GeomRegFibAdicCompletionOfEssFiniteTypeInt
section
open IsLocalRing TensorProduct

namespace GlobalTheory.GeomRegFibTransport
open ReciprocityTheory.AnForm.R.FinalTheorems

theorem exists_loc (A : Type) [CommRing A] [IsLocalRing A] [Algebra.EssFiniteType ℤ A] :
    ∃ (A₀ : Type) (_ : CommRing A₀) (_ : Algebra.FiniteType ℤ A₀) (p : Ideal A₀) (_ : p.IsPrime),
      Nonempty (Localization.AtPrime p ≃+* A) := by
  refine ⟨Algebra.EssFiniteType.subalgebra ℤ A, inferInstance, inferInstance,
    (maximalIdeal A).comap (algebraMap (Algebra.EssFiniteType.subalgebra ℤ A) A), inferInstance, ?_⟩
  have hsub : Algebra.EssFiniteType.submonoid ℤ A =
      ((maximalIdeal A).comap (algebraMap (Algebra.EssFiniteType.subalgebra ℤ A) A)).primeCompl := by
    ext x
    simp [Algebra.EssFiniteType.submonoid, Ideal.primeCompl, IsLocalRing.mem_maximalIdeal,
      mem_nonunits_iff, IsUnit.mem_submonoid_iff]
  have hloc := Algebra.EssFiniteType.isLocalization ℤ A
  rw [hsub] at hloc
  haveI : IsLocalization.AtPrime A ((maximalIdeal A).comap (algebraMap (Algebra.EssFiniteType.subalgebra ℤ A) A)) := hloc
  exact ⟨(IsLocalization.algEquiv ((maximalIdeal A).comap (algebraMap (Algebra.EssFiniteType.subalgebra ℤ A) A)).primeCompl
    (Localization.AtPrime _) A).toRingEquiv⟩

theorem evalₐ_factorPow {R : Type} [CommRing R] (I : Ideal R) {m n : ℕ} (hle : m ≤ n)
    (x : AdicCompletion I R) :
    Ideal.Quotient.factorPow I hle (AdicCompletion.evalₐ I n x) = AdicCompletion.evalₐ I m x := by
  induction x using AdicCompletion.induction_on with
  | h a =>
    simp only [AdicCompletion.evalₐ_mk]
    rw [Ideal.Quotient.factorPow, Ideal.Quotient.factor_mk, AdicCompletion.Ideal.mk_eq_mk I hle]

theorem complMap_compat {R S : Type} [CommRing R] [CommRing S] (e : R →+* S) (I : Ideal R)
    (J : Ideal S) (h : I.map e ≤ J) : ∀ {m n : ℕ} (hle : m ≤ n),
    (Ideal.Quotient.factorPow J hle).comp ((fun n => (Ideal.quotientMap (J ^ n) e (by
        rw [← Ideal.map_le_iff_le_comap, Ideal.map_pow]; exact Ideal.pow_right_mono h n)).comp
      (AdicCompletion.evalₐ I n : AdicCompletion I R →+* R ⧸ I ^ n)) n) =
      (fun n => (Ideal.quotientMap (J ^ n) e (by
        rw [← Ideal.map_le_iff_le_comap, Ideal.map_pow]; exact Ideal.pow_right_mono h n)).comp
      (AdicCompletion.evalₐ I n : AdicCompletion I R →+* R ⧸ I ^ n)) m := by
      intro m n hle
      ext x
      obtain ⟨y, hy⟩ := Ideal.Quotient.mk_surjective (AdicCompletion.evalₐ I n x)
      have h1 := evalₐ_factorPow I hle x
      simp only [RingHom.comp_apply, RingHom.coe_coe] at h1 ⊢
      rw [← h1, ← hy, Ideal.quotientMap_mk, Ideal.Quotient.factorPow, Ideal.Quotient.factorPow,
        Ideal.Quotient.factor_mk, Ideal.Quotient.factor_mk, Ideal.quotientMap_mk]

noncomputable def complMap {R S : Type} [CommRing R] [CommRing S] (e : R →+* S) (I : Ideal R)
    (J : Ideal S) (h : I.map e ≤ J) : AdicCompletion I R →+* AdicCompletion J S :=
  AdicCompletion.liftRingHom J
    (fun n => (Ideal.quotientMap (J ^ n) e (by
        rw [← Ideal.map_le_iff_le_comap, Ideal.map_pow]; exact Ideal.pow_right_mono h n)).comp
      (AdicCompletion.evalₐ I n : AdicCompletion I R →+* R ⧸ I ^ n))
    (complMap_compat e I J h)

theorem evalₐ_complMap {R S : Type} [CommRing R] [CommRing S] (e : R →+* S) (I : Ideal R)
    (J : Ideal S) (h : I.map e ≤ J) (n : ℕ) (x : AdicCompletion I R) :
    AdicCompletion.evalₐ J n (complMap e I J h x) =
      Ideal.quotientMap (J ^ n) e (by
        rw [← Ideal.map_le_iff_le_comap, Ideal.map_pow]; exact Ideal.pow_right_mono h n)
        (AdicCompletion.evalₐ I n x) := by
  unfold complMap
  exact AdicCompletion.evalₐ_liftRingHom J _ (complMap_compat e I J h) n x

theorem complMap_algebraMap {R S : Type} [CommRing R] [CommRing S] (e : R →+* S) (I : Ideal R)
    (J : Ideal S) (h : I.map e ≤ J) (r : R) :
    complMap e I J h (algebraMap R _ r) = algebraMap S _ (e r) := by
  apply AdicCompletion.ext_evalₐ
  intro n
  rw [evalₐ_complMap]
  simp [AdicCompletion.algebraMap_apply, AdicCompletion.evalₐ_of]

theorem complMap_comp {R S T : Type} [CommRing R] [CommRing S] [CommRing T] (e : R →+* S)
    (e' : S →+* T) (I : Ideal R) (J : Ideal S) (K : Ideal T) (h : I.map e ≤ J) (h' : J.map e' ≤ K)
    (x : AdicCompletion I R) :
    complMap e' J K h' (complMap e I J h x) = complMap (e'.comp e) I K
      (by rw [← Ideal.map_map]; exact (Ideal.map_mono h).trans h') x := by
  apply AdicCompletion.ext_evalₐ
  intro n
  rw [evalₐ_complMap, evalₐ_complMap, evalₐ_complMap]
  obtain ⟨y, hy⟩ := Ideal.Quotient.mk_surjective (AdicCompletion.evalₐ I n x)
  rw [← hy]
  simp [Ideal.quotientMap_mk]

theorem complMap_id {R : Type} [CommRing R] (I : Ideal R) (h : I.map (RingHom.id R) ≤ I)
    (x : AdicCompletion I R) : complMap (RingHom.id R) I I h x = x := by
  apply AdicCompletion.ext_evalₐ
  intro n
  rw [evalₐ_complMap]
  obtain ⟨y, hy⟩ := Ideal.Quotient.mk_surjective (AdicCompletion.evalₐ I n x)
  rw [← hy]
  simp [Ideal.quotientMap_mk]

theorem compl_equiv (R S : Type) [CommRing R] [CommRing S] (e : R ≃+* S) (I : Ideal R)
    (J : Ideal S) (h : I.map e = J) : ∃ f : AdicCompletion I R ≃+* AdicCompletion J S,
      ∀ r : R, f (algebraMap R _ r) = algebraMap S _ (e r) := by
  have h1 : I.map (e : R →+* S) ≤ J := h.le
  have h2 : J.map (e.symm : S →+* R) ≤ I := by
    rw [Ideal.map_le_iff_le_comap]
    intro y hy
    rw [← h, Ideal.mem_map_of_equiv] at hy
    obtain ⟨x, hx, rfl⟩ := hy
    simpa using hx
  refine ⟨RingEquiv.ofRingHom (complMap (e : R →+* S) I J h1) (complMap (e.symm : S →+* R) J I h2)
    ?_ ?_, complMap_algebraMap _ I J h1⟩
  · refine RingHom.ext fun x => ?_
    rw [RingHom.comp_apply, complMap_comp]
    simp only [RingEquiv.toRingHom_eq_coe, RingEquiv.comp_symm, RingHom.id_apply]
    exact complMap_id J _ x
  · refine RingHom.ext fun x => ?_
    rw [RingHom.comp_apply, complMap_comp]
    simp only [RingEquiv.toRingHom_eq_coe, RingEquiv.symm_comp, RingHom.id_apply]
    exact complMap_id I _ x

theorem fg_top_transfer {F F' K : Type} [Field F] [Field F'] [Field K] [Algebra F K] [Algebra F' K]
    (φ : F ≃+* F') (hφ : ∀ x, algebraMap F K x = algebraMap F' K (φ x))
    (h : (⊤ : IntermediateField F' K).FG) : (⊤ : IntermediateField F K).FG := by
  obtain ⟨S, hS⟩ := h
  refine ⟨S, ?_⟩
  apply IntermediateField.toSubfield_injective
  have hr : Set.range (algebraMap F K) = Set.range (algebraMap F' K) := by
    ext y
    constructor
    · rintro ⟨x, rfl⟩; exact ⟨φ x, (hφ x).symm⟩
    · rintro ⟨x, rfl⟩; exact ⟨φ.symm x, by rw [hφ, RingEquiv.apply_symm_apply]⟩
  have h2 := congrArg IntermediateField.toSubfield hS
  rw [IntermediateField.adjoin_toSubfield, IntermediateField.top_toSubfield] at h2 ⊢
  rw [hr]
  exact h2

noncomputable def tensorHom {A A' B B' K : Type} [CommRing A] [CommRing A'] [CommRing B]
    [CommRing B'] [CommRing K] [Algebra A B] [Algebra A' B'] [Algebra A K] [Algebra A' K]
    (e : A →+* A') (f : B →+* B') (hf : ∀ a, f (algebraMap A B a) = algebraMap A' B' (e a))
    (hK : ∀ a, algebraMap A K a = algebraMap A' K (e a)) : B ⊗[A] K →+* B' ⊗[A'] K :=
  letI : Algebra A (B' ⊗[A'] K) := ((algebraMap A' (B' ⊗[A'] K)).comp e).toAlgebra
  (Algebra.TensorProduct.lift (S := A)
    { toRingHom := (Algebra.TensorProduct.includeLeftRingHom : B' →+* B' ⊗[A'] K).comp f
      commutes' := fun a => by
        change Algebra.TensorProduct.includeLeftRingHom (f (algebraMap A B a)) =
          algebraMap A' (B' ⊗[A'] K) (e a)
        rw [hf]
        exact (Algebra.TensorProduct.includeLeft (S := A')).commutes (e a) }
    { toRingHom := (Algebra.TensorProduct.includeRight : K →ₐ[A'] B' ⊗[A'] K).toRingHom
      commutes' := fun a => by
        change (Algebra.TensorProduct.includeRight : K →ₐ[A'] B' ⊗[A'] K) (algebraMap A K a) =
          algebraMap A' (B' ⊗[A'] K) (e a)
        rw [hK]
        exact Algebra.TensorProduct.includeRight.commutes (e a) }
    (fun _ _ => Commute.all _ _)).toRingHom

theorem tensorHom_tmul {A A' B B' K : Type} [CommRing A] [CommRing A'] [CommRing B]
    [CommRing B'] [CommRing K] [Algebra A B] [Algebra A' B'] [Algebra A K] [Algebra A' K]
    (e : A →+* A') (f : B →+* B') (hf : ∀ a, f (algebraMap A B a) = algebraMap A' B' (e a))
    (hK : ∀ a, algebraMap A K a = algebraMap A' K (e a)) (b : B) (k : K) :
    tensorHom e f hf hK (b ⊗ₜ k) = f b ⊗ₜ k := by
  simp [tensorHom, Algebra.TensorProduct.lift_tmul]

theorem tensor_equiv {A A' B B' K : Type} [CommRing A] [CommRing A'] [CommRing B]
    [CommRing B'] [CommRing K] [Algebra A B] [Algebra A' B'] [Algebra A K] [Algebra A' K]
    (e : A ≃+* A') (f : B ≃+* B') (hf : ∀ a, f (algebraMap A B a) = algebraMap A' B' (e a))
    (hK : ∀ a, algebraMap A K a = algebraMap A' K (e a)) : Nonempty (B ⊗[A] K ≃+* B' ⊗[A'] K) := by
  have hf' : ∀ a, f.symm (algebraMap A' B' a) = algebraMap A B (e.symm a) := fun a => by
    apply f.injective
    rw [RingEquiv.apply_symm_apply, hf, RingEquiv.apply_symm_apply]
  have hK' : ∀ a, algebraMap A' K a = algebraMap A K (e.symm a) := fun a => by
    rw [hK, RingEquiv.apply_symm_apply]
  refine ⟨RingEquiv.ofRingHom (tensorHom (e : A →+* A') (f : B →+* B') hf hK)
    (tensorHom (e.symm : A' →+* A) (f.symm : B' →+* B) hf' hK') ?_ ?_⟩
  · refine RingHom.ext fun x => ?_
    induction x using TensorProduct.induction_on with
    | zero => simp
    | tmul b k =>
      rw [RingHom.comp_apply]
      erw [tensorHom_tmul, tensorHom_tmul]
      simp
    | add x y hx hy => simp only [RingHom.comp_apply, map_add (f := _)] at hx hy ⊢; rw [hx, hy]
  · refine RingHom.ext fun x => ?_
    induction x using TensorProduct.induction_on with
    | zero => simp
    | tmul b k =>
      rw [RingHom.comp_apply]
      erw [tensorHom_tmul, tensorHom_tmul]
      simp
    | add x y hx hy => simp only [RingHom.comp_apply, map_add (f := _)] at hx hy ⊢; rw [hx, hy]

theorem regular_transfer {T T' : Type} [CommRing T] [CommRing T'] (F : T ≃+* T')
    (hN : IsNoetherianRing T)
    (hR : ∀ (Q : Ideal T) [Q.IsPrime], IsRegularLocalRing (Localization.AtPrime Q)) :
    IsNoetherianRing T' ∧
      ∀ (Q' : Ideal T') [Q'.IsPrime], IsRegularLocalRing (Localization.AtPrime Q') := by
  refine ⟨isNoetherianRing_of_ringEquiv T F, fun Q' _ => ?_⟩
  haveI := hR (Q'.comap F)
  exact IsRegularLocalRing.of_ringEquiv (IsLocalization.ringEquivOfRingEquiv
    (Localization.AtPrime (Q'.comap F)) (Localization.AtPrime Q') F (F.map_primeCompl_comap_eq Q'))

theorem residueFieldRingEquiv_algebraMap {A A' : Type} [CommRing A] [CommRing A'] (e : A ≃+* A')
    (P' : Ideal A') [P'.IsPrime] (a : A) :
    Ideal.residueFieldRingEquiv (P'.comap (e : A →+* A')) P' e rfl
      (algebraMap A (P'.comap (e : A →+* A')).ResidueField a) =
      algebraMap A' P'.ResidueField (e a) :=
  Ideal.ResidueField.map_algebraMap _ P' (e : A →+* A') rfl a

theorem transport (A A' B B' : Type) [CommRing A] [CommRing A'] [CommRing B] [CommRing B']
    [Algebra A B] [Algebra A' B'] (e : A ≃+* A') (f : B ≃+* B')
    (hf : ∀ a : A, f (algebraMap A B a) = algebraMap A' B' (e a)) :
    GeomRegFib A B → GeomRegFib A' B' := by
  intro h P' _ K _ _ _ _ hfg
  let P : Ideal A := P'.comap (e : A →+* A')
  haveI : P.IsPrime := Ideal.comap_isPrime _ _
  let φ : P.ResidueField ≃+* P'.ResidueField := Ideal.residueFieldRingEquiv P P' e rfl
  letI : Algebra A K := ((algebraMap A' K).comp (e : A →+* A')).toAlgebra
  letI : Algebra P.ResidueField K := ((algebraMap P'.ResidueField K).comp (φ : _ →+* _)).toAlgebra
  haveI : IsScalarTower A P.ResidueField K := IsScalarTower.of_algebraMap_eq fun a => by
    change algebraMap A' K (e a) = algebraMap P'.ResidueField K (φ (algebraMap A P.ResidueField a))
    rw [residueFieldRingEquiv_algebraMap e P' a, ← IsScalarTower.algebraMap_apply]
  have hfg' : (⊤ : IntermediateField P.ResidueField K).FG := fg_top_transfer φ (fun _ => rfl) hfg
  obtain ⟨hN, hR⟩ := h P K hfg'
  obtain ⟨F⟩ := tensor_equiv (K := K) e f hf (fun _ => rfl)
  exact regular_transfer F hN hR

theorem geomRegFib_adicCompletion_of_essFiniteType_int :
    (∀ (A : Type) [CommRing A] [Algebra.FiniteType ℤ A], ReciprocityTheory.AnForm.R.FinalTheorems.QERing A) →
      ∀ (A : Type) [CommRing A] [IsLocalRing A] [Algebra.EssFiniteType ℤ A],
        ReciprocityTheory.AnForm.R.FinalTheorems.GeomRegFib A (AdicCompletion (IsLocalRing.maximalIdeal A) A) := by
  intro hQE A _ _ _
  obtain ⟨A₀, _, _, p, _, ⟨e⟩⟩ := exists_loc A
  have h2 := ((hQE A₀).2.1 p).2
  obtain ⟨f, hf⟩ := compl_equiv _ _ e (maximalIdeal (Localization.AtPrime p)) (maximalIdeal A)
    (map_ringEquiv_maximalIdeal e)
  exact transport _ _ _ _ e f hf h2

end GlobalTheory.GeomRegFibTransport
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsQuadOfPlane
section
noncomputable section

open MeasureTheory Complex Matrix GlobalTheory.RealWeil
open scoped ContDiff Real

namespace GlobalTheory.Mem.Lift

section General

variable {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] {B : Type} [NormedAddCommGroup B] [NormedSpace ℂ B]

def dH (ρ : V → B →L[ℂ] B) (v : V) (f : B) : B := fderiv ℝ (fun u => ρ u f) 0 v

def quad (ρ : V → B →L[ℂ] B) {κ : Type} [Fintype κ] (c : κ → ℂ) (p q : κ → V) (f : B) : B :=
  ∑ i, c i • dH ρ (p i) (dH ρ (q i) f)

def IsQuadOf (om : V → V → ℝ) (X : V → V) {κ : Type} [Fintype κ] (c : κ → ℂ) (p q : κ → V) : Prop :=
  ∀ (l : V →ₗ[ℝ] ℂ) (v : V),
    2 * π * I * ∑ i, c i * ((om (q i) v : ℂ) * l (p i) + (om (p i) v : ℂ) * l (q i)) = l (X v)

open MeasureTheory Complex Matrix in
open scoped ContDiff Real in
variable {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] {B : Type} [NormedAddCommGroup B]
  [NormedSpace ℂ B] in
theorem _root_.GlobalTheory.Mem.Lift.dH_add_left (ρ : V → B →L[ℂ] B) (u v : V) (f : B) :
    _root_.GlobalTheory.Mem.Lift.dH ρ (u + v) f =
      _root_.GlobalTheory.Mem.Lift.dH ρ u f + _root_.GlobalTheory.Mem.Lift.dH ρ v f :=
  map_add _ _ _

open MeasureTheory Complex Matrix in
open scoped ContDiff Real in
variable {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] {B : Type} [NormedAddCommGroup B]
  [NormedSpace ℂ B] in
theorem _root_.GlobalTheory.Mem.Lift.dH_smul_left (ρ : V → B →L[ℂ] B) (r : ℝ) (v : V) (f : B) :
    _root_.GlobalTheory.Mem.Lift.dH ρ (r • v) f = r • _root_.GlobalTheory.Mem.Lift.dH ρ v f :=
  map_smul _ _ _

open MeasureTheory Complex Matrix in
open scoped ContDiff Real in
variable {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] {B : Type} [NormedAddCommGroup B]
  [NormedSpace ℂ B] in
theorem _root_.GlobalTheory.Mem.Lift.dH_add {ρ : V → B →L[ℂ] B} (v : V) {f g : B}
    (hf : _root_.GlobalTheory.RealWeil.Sm ρ f) (hg : _root_.GlobalTheory.RealWeil.Sm ρ g) :
    _root_.GlobalTheory.Mem.Lift.dH ρ v (f + g) =
      _root_.GlobalTheory.Mem.Lift.dH ρ v f + _root_.GlobalTheory.Mem.Lift.dH ρ v g := by
  have hf' : DifferentiableAt ℝ (fun u => ρ u f) 0 :=
    (ContDiff.differentiable hf (by simp)).differentiableAt
  have hg' : DifferentiableAt ℝ (fun u => ρ u g) 0 :=
    (ContDiff.differentiable hg (by simp)).differentiableAt
  unfold _root_.GlobalTheory.Mem.Lift.dH
  simp only [map_add (f := _)]
  rw [(hf'.hasFDerivAt.fun_add hg'.hasFDerivAt).fderiv]
  rfl

open MeasureTheory Complex Matrix in
open scoped ContDiff Real in
variable {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] {B : Type} [NormedAddCommGroup B]
  [NormedSpace ℂ B] in
theorem _root_.GlobalTheory.Mem.Lift.dH_smul {ρ : V → B →L[ℂ] B} (v : V) (a : ℂ) {f : B}
    (hf : _root_.GlobalTheory.RealWeil.Sm ρ f) :
    _root_.GlobalTheory.Mem.Lift.dH ρ v (a • f) = a • _root_.GlobalTheory.Mem.Lift.dH ρ v f := by
  have hf' : DifferentiableAt ℝ (fun u => ρ u f) 0 :=
    (ContDiff.differentiable hf (by simp)).differentiableAt
  unfold _root_.GlobalTheory.Mem.Lift.dH
  simp only [map_smul]
  rw [(hf'.hasFDerivAt.fun_const_smul a).fderiv]
  rfl


open MeasureTheory Complex Matrix in
open scoped ContDiff Real in
variable {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] {B : Type} [NormedAddCommGroup B]
  [NormedSpace ℂ B] in
theorem _root_.GlobalTheory.Mem.Lift.hasDerivAt_dH {ρ : V → B →L[ℂ] B} (v : V) {f : B}
    (hf : _root_.GlobalTheory.RealWeil.Sm ρ f) :
    HasDerivAt (fun t : ℝ => ρ (t • v) f) (_root_.GlobalTheory.Mem.Lift.dH ρ v f) 0 := by
  have hf' : DifferentiableAt ℝ (fun u => ρ u f) 0 :=
    (ContDiff.differentiable hf (by simp)).differentiableAt
  have hl : HasDerivAt (fun t : ℝ => t • v) v 0 := by
    simpa using (hasDerivAt_id (0 : ℝ)).smul_const v
  exact hf'.hasFDerivAt.comp_hasDerivAt_of_eq (0 : ℝ) hl (by simp)


open MeasureTheory Complex Matrix in
open scoped ContDiff Real in
variable {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] {B : Type} [NormedAddCommGroup B]
  [NormedSpace ℂ B] in
theorem _root_.GlobalTheory.Mem.Lift.dH_comm {ρ : V → B →L[ℂ] B} (A : B →L[ℂ] B)
    (hA : ∀ v f, A (ρ v f) = ρ v (A f)) {f : B} (hf : _root_.GlobalTheory.RealWeil.Sm ρ f) :
    _root_.GlobalTheory.RealWeil.Sm ρ (A f) ∧
      ∀ v, _root_.GlobalTheory.Mem.Lift.dH ρ v (A f) = A (_root_.GlobalTheory.Mem.Lift.dH ρ v f) := by
  have hf' : DifferentiableAt ℝ (fun u => ρ u f) 0 :=
    (ContDiff.differentiable hf (by simp)).differentiableAt
  have hfun : (fun u => ρ u (A f)) = fun u => (A.restrictScalars ℝ) (ρ u f) := by
    funext u
    simp [hA]
  refine ⟨?_, fun v => ?_⟩
  · unfold _root_.GlobalTheory.RealWeil.Sm
    rw [hfun]
    exact (A.restrictScalars ℝ).contDiff.comp hf
  · unfold _root_.GlobalTheory.Mem.Lift.dH
    have h : HasFDerivAt (fun u => (A.restrictScalars ℝ) (ρ u f))
        ((A.restrictScalars ℝ).comp (fderiv ℝ (fun u => ρ u f) 0)) 0 :=
      (A.restrictScalars ℝ).hasFDerivAt.comp (0 : V) hf'.hasFDerivAt
    rw [hfun, h.fderiv]
    rfl

def smS (ρ : V → B →L[ℂ] B) : Submodule ℂ B where
  carrier := {f | Sm ρ f}
  add_mem' := fun hf hg => by simpa only [Set.mem_setOf_eq, Sm, map_add (f := _)] using ContDiff.add (show ContDiff ℝ ∞ _ from hf) (show ContDiff ℝ ∞ _ from hg)
  zero_mem' := by simpa only [Set.mem_setOf_eq, Sm, map_zero] using contDiff_const
  smul_mem' := fun a _ hf => by simpa only [Set.mem_setOf_eq, Sm, map_smul] using ContDiff.const_smul a (show ContDiff ℝ ∞ _ from hf)

end General

section Coord

variable {ι : Type} [Fintype ι] [DecidableEq ι] {B : Type} [NormedAddCommGroup B] [NormedSpace ℂ B]

def xOp (ρ : (ι → ℂ) → B →L[ℂ] B) (k : ι) (f : B) : B :=
  dH ρ (Pi.single k 1) f - I • dH ρ (I • Pi.single k 1) f

def dOp (ρ : (ι → ℂ) → B →L[ℂ] B) (H : Matrix ι ι ℂ) (l : ι) (f : B) : B :=
  (-(1 / (4 * π)) : ℂ) • (dH ρ (H⁻¹ *ᵥ Pi.single l 1) f + I • dH ρ (I • H⁻¹ *ᵥ Pi.single l 1) f)

def nOp (ρ : (ι → ℂ) → B →L[ℂ] B) (H X : Matrix ι ι ℂ) (f : B) : B := ∑ k, ∑ l, X k l • xOp ρ k (dOp ρ H l f)

end Coord

def IsCCR {A : Type} [Ring A] {κ : Type} [DecidableEq κ] (x d : κ → A) : Prop :=
  (∀ k l, x k * x l = x l * x k) ∧ (∀ k l, d k * d l = d l * d k) ∧
    ∀ k l, d l * x k - x k * d l = if k = l then 1 else 0

end GlobalTheory.Mem.Lift

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MonoCharOfMulPolyDivPowStatement
section
open Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_zpow_of_multiplicative_of_pow_mul_eq_eval : ∀ (χ : ℂ → ℂ), (∀ s t : ℂ, s ≠ 0 → t ≠ 0 → χ (s * t) = χ s * χ t) → χ 1 = 1 → ∀ (N : ℕ) (p : Polynomial ℂ), (∀ t : ℂ, t ≠ 0 → t ^ N * χ t = p.eval t) → ∃ k : ℤ, ∀ t : ℂ, t ≠ 0 → χ t = t ^ k := by
  first | exact @GlobalTheory.mono_char_of_mul_poly_div_pow | exact GlobalTheory.mono_char_of_mul_poly_div_pow | (intros; apply GlobalTheory.mono_char_of_mul_poly_div_pow <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.NatCastMulCoeffCharpolyRev
section
namespace GlobalTheory

theorem natCast_mul_coeff_charpolyRev {R : Type} [CommRing R] {m : ℕ}
    (M : Matrix (Fin m) (Fin m) R) (k : ℕ) :
    (k : R) * M.charpolyRev.coeff k =
      -∑ i ∈ Finset.range k, (M ^ (i + 1)).trace * M.charpolyRev.coeff (k - 1 - i) := by
  rcases k with _ | j
  · simp
  · have h := congrArg (PowerSeries.coeff j) (GroundTheory.Global.coe_derivative_charpolyRev M)
    rw [Polynomial.coeff_coe, Polynomial.coeff_derivative, neg_mul, map_neg,
      PowerSeries.coeff_mul, ← Finset.Nat.sum_antidiagonal_swap,
      Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk] at h
    simp only [Prod.swap_prod_mk, PowerSeries.coeff_mk, Polynomial.coeff_coe] at h
    have e : ∀ i ∈ Finset.range (j + 1), j + 1 - 1 - i = j - i := fun i _ => by omega
    rw [Finset.sum_congr rfl fun i hi => by rw [e i hi], mul_comm, Nat.cast_succ, h]
    exact congrArg Neg.neg (Finset.sum_congr rfl fun i _ => mul_comm _ _)

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PeriodicLeftHalfPlaneShiftNonnegOfImPosStatement
section
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.periodic_left_halfPlane_shift_nonneg_of_im_pos : ∀ (c : ℝ) (f : ℂ → ℂ) (m : ℤ), DifferentiableOn ℂ f {s : ℂ | s.re < c} → (∀ s : ℂ, s.re < c → f (s + 2 * Real.pi * Complex.I) = f s + m) → (∀ s : ℂ, s.re < c → 0 < (f s).im) → 0 ≤ m := by
  first | exact @GlobalTheory.periodic_strip_shift_nonneg | exact GlobalTheory.periodic_strip_shift_nonneg | (intros; apply GlobalTheory.periodic_strip_shift_nonneg <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PosDefQuadMarginStatement
section
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_margin_quadForm_pos_of_perturbation : ∀ {ι : Type} [Fintype ι] (M : ι → ι → ℝ), (∀ c : ι → ℝ, c ≠ 0 → 0 < ∑ i, ∑ j, c i * c j * M i j) → ∃ η : ℝ, 0 < η ∧ ∀ E : ι → ι → ℝ, (∀ i j, |E i j| ≤ η) → ∀ c : ι → ℝ, c ≠ 0 → 0 < ∑ i, ∑ j, c i * c j * (M i j + E i j) := by
  first | exact @GlobalTheory.posDef_quad_margin | exact GlobalTheory.posDef_quad_margin | (intros; apply GlobalTheory.posDef_quad_margin <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PrimeIdealsCountingBounds
section
open NumberField IsDedekindDomain

namespace GlobalTheory.Mem.FewPrimes

variable {K : Type} [Field K] [NumberField K]

theorem exists_prime_mem (v : HeightOneSpectrum (𝓞 K)) :
    ∃ p : ℕ, p.Prime ∧ (p : 𝓞 K) ∈ v.asIdeal := by
  first
  | exact @_root_.GlobalTheory.PrimeInHeightOneSpectrum.target
  | exact _root_.GlobalTheory.PrimeInHeightOneSpectrum.target
  | (apply _root_.GlobalTheory.PrimeInHeightOneSpectrum.target <;> assumption)
  | (intros; apply _root_.GlobalTheory.PrimeInHeightOneSpectrum.target <;> assumption)
  | (intros; apply @_root_.GlobalTheory.PrimeInHeightOneSpectrum.target <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.PrimeInHeightOneSpectrum.target ..)

end GlobalTheory.Mem.FewPrimes
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.RatMemSpanOfRealMemSpanFinStatement
section
open Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.rat_mem_span_of_real_mem_span_fin : ∀ (k r : ℕ) (w : Fin k → Fin r → ℚ) (v : Fin r → ℚ), (fun j => ((v j : ℚ) : ℝ)) ∈ Submodule.span ℝ (Set.range fun i j => ((w i j : ℚ) : ℝ)) → v ∈ Submodule.span ℚ (Set.range w) := by
  first | exact @GlobalTheory.rat_mem_span_of_real_mem_span | exact GlobalTheory.rat_mem_span_of_real_mem_span | (intros; apply GlobalTheory.rat_mem_span_of_real_mem_span <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SchurOrthogonalitySubgroupMeasureOneStatement
section
open MeasureTheory
open scoped InnerProductSpace
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.schur_orthogonality_subgroup_measure_one : ∀ {G : Type} [Group G] [MeasurableSpace G] [MeasurableMul G] [MeasurableInv G] (ν : Measure G) [ν.IsMulLeftInvariant] (Ω : Subgroup G), MeasurableSet (Ω : Set G) → ν (Ω : Set G) = 1 → ∀ {W : Type} [NormedAddCommGroup W] [InnerProductSpace ℂ W] [FiniteDimensional ℂ W] (ρ : G →* Module.End ℂ W), (∀ g x y, ⟪ρ g x, ρ g y⟫_ℂ = ⟪x, y⟫_ℂ) → (∀ x y : W, Measurable fun g => ⟪x, ρ g y⟫_ℂ) → (∀ U : Submodule ℂ W, (∀ g ∈ Ω, U.map (ρ g) ≤ U) → U = ⊥ ∨ U = ⊤) → ∀ a a' x x' : W, IntegrableOn (fun g => star ⟪a, ρ g⁻¹ x⟫_ℂ * ⟪a', ρ g⁻¹ x'⟫_ℂ) Ω ν ∧ (Module.finrank ℂ W : ℂ) * ∫ g in (Ω : Set G), star ⟪a, ρ g⁻¹ x⟫_ℂ * ⟪a', ρ g⁻¹ x'⟫_ℂ ∂ν = ⟪a', a⟫_ℂ * ⟪x, x'⟫_ℂ := by
  first | exact @GlobalTheory.SchurOrthOnSubgroup.schur_orthogonality | exact GlobalTheory.SchurOrthOnSubgroup.schur_orthogonality | (intros; apply GlobalTheory.SchurOrthOnSubgroup.schur_orthogonality <;> assumption)
end

