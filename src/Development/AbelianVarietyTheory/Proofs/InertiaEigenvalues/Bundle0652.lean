module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0025
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0008
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0010
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.ExistsCellOfIsSubquotient
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0044
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0020

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.WeilDeligneSumTwistCompat
section
open NumberField IsDedekindDomain ValuativeRel Matrix Polynomial Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.Published
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.WDListLaws

variable {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
  {A : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 E)} {h : IsPlaceOver A w}

theorem lpTwist_lpZero (ξ : Weil h →* ℂˣ) (hξ : GlobalTheory.WeilDeligne.IsSmooth ξ) :
    (WD.lpZero (h := h)).lpTwist ξ hξ = WD.lpZero (h := h) := by
  rw [WD.lpZero, WD.lpTwist_mk]
  exact WD.sound ⟨.refl _ _, fun σ v => Subsingleton.elim _ _, fun v => Subsingleton.elim _ _⟩

theorem lpTwist_lpSum (x y : WD h) (ξ : Weil h →* ℂˣ) (hξ : GlobalTheory.WeilDeligne.IsSmooth ξ) :
    (x.lpSum y).lpTwist ξ hξ = (x.lpTwist ξ hξ).lpSum (y.lpTwist ξ hξ) := by
  induction x using WD.ind with
  | hP n a =>
  induction y using WD.ind with
  | hP m b =>
  rw [WD.lpSum_mk, WD.lpTwist_mk, WD.lpTwist_mk, WD.lpTwist_mk, WD.lpSum_mk]
  refine WD.sound ⟨.refl _ _, fun σ v => ?_, fun v => rfl⟩
  rfl

theorem lpTwist_lpChar (x y : WD h) (ξ : Weil h →* ℂˣ) (hξ : GlobalTheory.WeilDeligne.IsSmooth ξ) :
    (x.lpChar y).lpTwist ξ hξ = (x.lpTwist ξ hξ).lpChar y := by
  induction x using WD.ind with
  | hP n a =>
  induction y using WD.ind with
  | hP m b =>
  rw [WD.lpChar_mk, WD.lpTwist_mk, WD.lpTwist_mk, WD.lpChar_mk]
  refine WD.sound ⟨.refl _ _, fun σ v => ?_, fun v => rfl⟩
  simp only [WDRep.tensor_ρ, WDRep.twist_ρ, LinearEquiv.refl_apply, TensorProduct.map_smul_left,
    LinearMap.smul_apply]

theorem lpChar_lpZero (x : WD h) : x.lpChar (WD.lpZero (h := h)) = WD.lpZero (h := h) := by
  induction x using WD.ind with
  | hP n a =>
  rw [WD.lpZero, WD.lpChar_mk]
  exact WD.sound ⟨0, fun _ _ => Subsingleton.elim _ _, fun _ => Subsingleton.elim _ _⟩

theorem lpChar_lpSum (x a b : WD h) : x.lpChar (a.lpSum b) = (x.lpChar a).lpSum (x.lpChar b) := by
  induction x using WD.ind with
  | hP n c =>
  induction a using WD.ind with
  | hP m a =>
  induction b using WD.ind with
  | hP k b =>
  rw [WD.lpSum_mk, WD.lpChar_mk, WD.lpChar_mk, WD.lpChar_mk, WD.lpSum_mk]
  refine WD.sound ⟨TensorProduct.prodRight ℂ ℂ _ _ _, fun σ v => ?_, fun v => ?_⟩
  · induction v using TensorProduct.inductionOn with
    | tmul p q =>
      obtain ⟨q₁, q₂⟩ := q
      simp
    | add p q hp hq => simp only [map_add (f := _), hp, hq]
  · induction v using TensorProduct.inductionOn with
    | tmul p q =>
      obtain ⟨q₁, q₂⟩ := q
      simp
    | add p q hp hq => simp only [map_add (f := _), hp, hq]

theorem charPol_lpZero (σ : Weil h) : (WD.lpZero (h := h)).charPol σ = 1 :=
  Polynomial.eq_one_of_monic_natDegree_zero (WD.charPol_monic _ σ)
    ((WD.charPol_natDegree _ σ).trans (WD.lpDim_zero h))

end GlobalTheory.WDListLaws


open GlobalTheory.WDListLaws in
open GlobalTheory.LocLanglands (sumList) in
theorem GlobalTheory.sumList_laws : ∀ (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (A : ValuationSubring Ω) (w : HeightOneSpectrum (𝓞 E)) (h : IsPlaceOver A w), (∀ l l' : List (WD h), l.Perm l' → sumList l = sumList l') ∧ (∀ (l : List (WD h)) (ξ : Weil h →* ℂˣ) (hξ : GlobalTheory.WeilDeligne.IsSmooth ξ), (sumList l).lpTwist ξ hξ = sumList (l.map fun y => y.lpTwist ξ hξ)) ∧ (∀ (x y : WD h) (ξ : Weil h →* ℂˣ) (hξ : GlobalTheory.WeilDeligne.IsSmooth ξ), (x.lpSum y).lpTwist ξ hξ = (x.lpTwist ξ hξ).lpSum (y.lpTwist ξ hξ) ∧ (x.lpChar y).lpTwist ξ hξ = (x.lpTwist ξ hξ).lpChar y) ∧ (∀ (x : WD h) (l : List (WD h)), x.lpChar (sumList l) = sumList (l.map x.lpChar)) ∧ (∀ l : List (WD h), (sumList l).lpDim = (l.map WD.lpDim).sum ∧ ∀ σ, (sumList l).charPol σ = (l.map fun y => y.charPol σ).prod) := by
  intro E Ω _ _ _ _ _ A w h
  refine ⟨fun l l' hp => ?_, fun l ξ hξ => ?_, fun x y ξ hξ => ⟨lpTwist_lpSum x y ξ hξ, lpTwist_lpChar x y ξ hξ⟩,
    fun x l => ?_, fun l => ⟨?_, fun σ => ?_⟩⟩
  · induction hp with
    | nil => rfl
    | cons x _ ih =>
      show WD.lpSum x (sumList _) = WD.lpSum x (sumList _)
      rw [ih]
    | swap x y l =>
      show WD.lpSum y (WD.lpSum x (sumList l)) = WD.lpSum x (WD.lpSum y (sumList l))
      rw [← WD.lpSum_assoc, WD.lpSum_comm y x, WD.lpSum_assoc]
    | trans _ _ ih₁ ih₂ => exact ih₁.trans ih₂
  · induction l with
    | nil => exact lpTwist_lpZero ξ hξ
    | cons x l ih =>
      show (WD.lpSum x (sumList l)).lpTwist ξ hξ = WD.lpSum _ (sumList _)
      rw [lpTwist_lpSum, ih]
  · induction l with
    | nil => exact lpChar_lpZero x
    | cons y l ih =>
      show x.lpChar (WD.lpSum y (sumList l)) = WD.lpSum _ (sumList _)
      rw [lpChar_lpSum, ih]
  · induction l with
    | nil => exact WD.lpDim_zero h
    | cons y l ih =>
      show (WD.lpSum y (sumList l)).lpDim = _
      rw [WD.lpDim_sum, ih, List.map_cons, List.sum_cons]
  · induction l with
    | nil => exact charPol_lpZero σ
    | cons y l ih =>
      show (WD.lpSum y (sumList l)).charPol σ = _
      rw [WD.charPol_lpSum, ih, List.map_cons, List.prod_cons]
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.WeilGroupRestriction
section
open NumberField IsDedekindDomain ValuativeRel Matrix Polynomial Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.Published
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.WeilRestrict

open scoped Pointwise

section

variable {K L Ω : Type} [Field K] [NumberField K] [Field L] [NumberField L] [Field Ω]
  [Algebra K Ω] [Algebra L Ω] [Algebra K L] [IsScalarTower K L Ω]

theorem comap_eq_of_isPlaceOver {A : ValuationSubring Ω} {v : HeightOneSpectrum (𝓞 K)}
    {v' : HeightOneSpectrum (𝓞 L)} (h : IsPlaceOver A v) (h' : IsPlaceOver A v') :
    v'.asIdeal.comap (algebraMap (𝓞 K) (𝓞 L)) = v.asIdeal := by
  ext x
  rw [Ideal.mem_comap, ← h x, ← h' (algebraMap (𝓞 K) (𝓞 L) x), IsScalarTower.algebraMap_apply K L Ω]
  rfl

theorem normV_eq_pow_of_isPlaceOver {A : ValuationSubring Ω} {v : HeightOneSpectrum (𝓞 K)}
    {v' : HeightOneSpectrum (𝓞 L)} (h : IsPlaceOver A v) (h' : IsPlaceOver A v') :
    ∃ f : ℕ, normV v' = normV v ^ f := by
  have hw := comap_eq_of_isPlaceOver h h'
  have : v'.asIdeal.LiesOver v.asIdeal := ⟨hw.symm⟩
  refine ⟨v'.asIdeal.inertiaDeg (𝓞 K), ?_⟩
  simp only [normV, ← Submodule.cardQuot_apply, ← Ideal.absNorm_apply]
  exact (Ideal.absNorm_pow_inertiaDeg v.asIdeal v'.asIdeal).symm


variable (K) in
def resG : G L Ω →* G K Ω where
  toFun σ := σ.restrictScalars K
  map_one' := AlgEquiv.ext fun _ => rfl
  map_mul' _ _ := AlgEquiv.ext fun _ => rfl

@[simp] theorem resG_apply (σ : G L Ω) (z : Ω) : resG K σ z = σ z := rfl

theorem continuous_resG [Algebra.IsIntegral L Ω] : Continuous (resG (L := L) (Ω := Ω) K) := by
  refine continuous_of_continuousAt_one _ ?_
  rw [ContinuousAt, map_one]
  intro s hs
  rw [Filter.mem_map]
  obtain ⟨E, hE, hEs⟩ := (krullTopology_mem_nhds_one_iff K Ω s).1 hs
  let b := Module.finBasis K E
  have hU : IsOpen (⋂ i, (MulAction.stabilizer (G L Ω) (b i : Ω) : Set (G L Ω))) :=
    isOpen_iInter_of_finite fun i => stabilizer_isOpen_of_isIntegral _
  refine Filter.mem_of_superset (hU.mem_nhds (Set.mem_iInter.2 fun i =>
    (MulAction.stabilizer (G L Ω) _).one_mem)) fun g hg => hEs ?_
  rw [SetLike.mem_coe, IntermediateField.mem_fixingSubgroup_iff]
  intro x hx
  have hb : ∀ i, g (b i : Ω) = b i := fun i => by
    have := Set.mem_iInter.1 hg i
    rwa [SetLike.mem_coe, MulAction.mem_stabilizer_iff, AlgEquiv.smul_def] at this
  have hx' : x = ∑ i, b.repr ⟨x, hx⟩ i • (b i : Ω) := by
    have := congrArg E.val (b.sum_repr ⟨x, hx⟩)
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum] at this
    simp only [map_smul] at this
    exact this.symm
  set_option synthInstance.maxHeartbeats 100000 in
    rw [hx', map_sum]
  exact Finset.sum_congr rfl fun i _ => by rw [map_smul, resG_apply, hb]

variable {A : ValuationSubring Ω}

theorem resG_mem_Dec {σ : G L Ω} (hσ : σ ∈ Dec (F := L) A) : resG K σ ∈ Dec (F := K) A := by
  have h1 : σ • A = A := hσ
  show (resG K σ) • A = A
  exact h1

theorem resG_mem_Ine {σ : G L Ω} (hσ : σ ∈ Ine (F := L) A) : resG K σ ∈ Ine (F := K) A :=
  ⟨resG_mem_Dec hσ.1, fun x hx => hσ.2 x hx⟩

theorem actsAs_resG {q f a b : ℕ} {σ : G L Ω} (hσ : ActsAs A (q ^ f) σ a b) :
    ActsAs A q (resG K σ) (f * a) (f * b) := by
  refine ⟨resG_mem_Dec hσ.1, fun x hx => ?_⟩
  have e1 : (q ^ f) ^ b = q ^ (f * b) := (pow_mul q f b).symm
  have e2 : (q ^ f) ^ a = q ^ (f * a) := (pow_mul q f a).symm
  have := hσ.2 x hx
  rw [e1, e2] at this
  exact this

variable {v : HeightOneSpectrum (𝓞 K)} {v' : HeightOneSpectrum (𝓞 L)}

def resWeil (h : IsPlaceOver A v) (h' : IsPlaceOver A v') : Weil h' →* Weil h :=
  ((resG K).comp (Weil h').subtype).codRestrict (Weil h) fun σ => by
    obtain ⟨f, hf⟩ := normV_eq_pow_of_isPlaceOver h h'
    obtain ⟨a, b, hab⟩ := (mem_Weil h').1 σ.2
    rw [hf] at hab
    exact (mem_Weil h).2 ⟨_, _, actsAs_resG hab⟩

theorem resWeil_apply (h : IsPlaceOver A v) (h' : IsPlaceOver A v') (σ : Weil h') (z : Ω) :
    (resWeil h h' σ : G K Ω) z = (σ : G L Ω) z := rfl

def resIne : Ine (F := L) A → Ine (F := K) A := fun σ => ⟨resG K (σ : G L Ω), resG_mem_Ine (K := K) (L := L) (σ := (σ : G L Ω)) σ.2⟩

theorem continuous_resIne [Algebra.IsIntegral L Ω] : Continuous (resIne (K := K) (L := L) (A := A)) :=
  ((continuous_resG (K := K)).comp continuous_subtype_val).subtype_mk _

theorem isSmooth_comp_resWeil [Algebra.IsIntegral L Ω] (h : IsPlaceOver A v) (h' : IsPlaceOver A v')
    {M : Type*} [Monoid M] {f : Weil h →* M} (hf : IsSmooth f) : IsSmooth (f.comp (resWeil h h')) := by
  have e : {σ : Ine (F := L) A | (f.comp (resWeil h h')) (ineIncl h' σ) = 1} =
      resIne ⁻¹' {τ : Ine (F := K) A | f (ineIncl h τ) = 1} := rfl
  show IsOpen {σ : Ine (F := L) A | (f.comp (resWeil h h')) (ineIncl h' σ) = 1}
  rw [e]
  exact hf.preimage continuous_resIne

end

theorem weil_restrict : ∀ (K L Ω : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Field Ω] [Algebra K Ω] [IsAlgClosure K Ω] [Algebra L Ω] [IsAlgClosure L Ω] [Algebra K L] [IsScalarTower K L Ω] (A : ValuationSubring Ω) (v : HeightOneSpectrum (𝓞 K)) (v' : HeightOneSpectrum (𝓞 L)) (h : IsPlaceOver A v) (h' : IsPlaceOver A v'), ∃ r : Weil h' →* Weil h, (∀ (σ : Weil h') (z : Ω), (r σ : G K Ω) z = (σ : G L Ω) z) ∧ ∀ (M : Type) [Monoid M] (f : Weil h →* M), GlobalTheory.WeilDeligne.IsSmooth f → GlobalTheory.WeilDeligne.IsSmooth (f.comp r) := by
  intro K L Ω _ _ _ _ _ _ _ _ _ _ _ A v v' h h'
  haveI : Algebra.IsIntegral L Ω := (IsAlgClosure.isAlgebraic (R := L) (K := Ω)).isIntegral
  exact ⟨resWeil h h', resWeil_apply h h', fun M _ f hf => isSmooth_comp_resWeil h h' hf⟩

end GlobalTheory.WeilRestrict
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.WeilGroupTransport
section
open NumberField IsDedekindDomain ValuativeRel Matrix Polynomial Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.Published
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open scoped IntermediateField

noncomputable section

theorem GlobalTheory.LocLanglands.exists_isLocalExt_transport : ∀ (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (A : ValuationSubring Ω) (w : HeightOneSpectrum (𝓞 E)) (h : IsPlaceOver A w) (E' Ω' : Type) [Field E'] [NumberField E'] [Field Ω'] [Algebra E' Ω'] [IsAlgClosure E' Ω'] (A' : ValuationSubring Ω') (w' : HeightOneSpectrum (𝓞 E')) (h' : IsPlaceOver A' w') (φ : Ω ≃+* Ω') (j : E →+* E') (c : Weil h ≃* Weil h'), (∀ x, φ (algebraMap E Ω x) = algebraMap E' Ω' (j x)) → (∀ σ, WeilRel φ σ (c σ)) → ∀ L : IntermediateField E Ω, FiniteDimensional E L → IsLocalExt L h → ∃ (L' : IntermediateField E' Ω') (jL : L →+* L'), FiniteDimensional E' L' ∧ IsLocalExt L' h' ∧ Module.finrank E' L' = Module.finrank E L ∧ (∀ x : L, φ (x : Ω) = (jL x : Ω')) ∧ Algebra.adjoin E' (Set.range jL) = ⊤ := by
  intro E Ω _ _ _ _ _ A w h E' Ω' _ _ _ _ _ A' w' h' φ j c hφ hc L hL hloc
  classical
  haveI := IsAlgClosure.isAlgebraic (R := E) (K := Ω)
  haveI := IsAlgClosure.isAlgebraic (R := E') (K := Ω')

  obtain ⟨α, rfl⟩ : ∃ α : Ω, E⟮α⟯ = L := by
    obtain ⟨α₀, hα₀⟩ := Field.exists_primitive_element E L
    refine ⟨(α₀ : Ω), ?_⟩
    have := congrArg (IntermediateField.map L.val) hα₀
    rw [IntermediateField.adjoin_map, Set.image_singleton, ← AlgHom.fieldRange_eq_map,
      IntermediateField.fieldRange_val] at this
    exact this
  have hint : IsIntegral E α := Algebra.IsIntegral.isIntegral α
  set α' : Ω' := φ α with hα'
  have hint' : IsIntegral E' α' := Algebra.IsIntegral.isIntegral α'
  set p := minpoly E α with hp
  set m' := minpoly E' α' with hm'
  have hcomp : (algebraMap E' Ω').comp j = (φ : Ω →+* Ω').comp (algebraMap E Ω) := by
    ext x; exact (hφ x).symm
  have key : ∀ β : Ω, φ (aeval β p) = aeval (φ β) (p.map j) := by
    intro β
    rw [aeval_def, aeval_def, eval₂_map, hcomp]
    exact Polynomial.hom_eval₂ p (algebraMap E Ω) (φ : Ω →+* Ω') β
  have hpmon : p.Monic := minpoly.monic hint
  have hqne : p.map j ≠ 0 := (hpmon.map j).ne_zero
  have hdvd : m' ∣ p.map j := minpoly.dvd E' α' (by rw [← key, minpoly.aeval]; simp)
  have hm'root : ∀ σ' : G E' Ω', aeval (σ' α') m' = 0 := by
    intro σ'
    rw [show σ' α' = (σ' : Ω' →ₐ[E'] Ω') α' from rfl, aeval_algHom_apply, minpoly.aeval, map_zero]
  have hq : ∀ y : Ω', aeval y m' = 0 → aeval y (p.map j) = 0 := by
    intro y hy
    obtain ⟨r, hr⟩ := hdvd
    rw [hr, map_mul, hy, zero_mul]

  have horb : ∀ β : Ω, aeval β p = 0 → ∃ τ : Weil h, (τ : G E Ω) α = β := by
    intro β hβ
    have hmin : minpoly E β = minpoly E α :=
      (minpoly.eq_of_irreducible_of_monic (minpoly.irreducible hint) hβ hpmon).symm
    obtain ⟨σ, hσ⟩ := (Normal.minpoly_eq_iff_mem_orbit (F := E) (E := Ω)).1 hmin
    obtain ⟨τ, hτ⟩ := hloc σ
    refine ⟨τ, ?_⟩
    have := hτ ⟨α, IntermediateField.mem_adjoin_simple_self E α⟩
    simp only [IntermediateField.algebraMap_apply] at this
    rw [this]; exact hσ

  set L' : IntermediateField E' Ω' := E'⟮α'⟯ with hL'
  have hsub : ∀ x : E⟮α⟯, φ (x : Ω) ∈ L' := by
    let S : IntermediateField E Ω := Subfield.toIntermediateField
      (L'.toSubfield.comap (φ : Ω →+* Ω')) (fun x => by
        show φ (algebraMap E Ω x) ∈ L'
        rw [hφ]; exact L'.algebraMap_mem (j x))
    have hle : E⟮α⟯ ≤ S := IntermediateField.adjoin_simple_le_iff.2
      (show φ α ∈ L' from IntermediateField.mem_adjoin_simple_self E' α')
    intro x
    exact hle x.2
  let jL : E⟮α⟯ →+* L' := RingHom.codRestrict ((φ : Ω →+* Ω').comp (algebraMap E⟮α⟯ Ω)) L' hsub
  refine ⟨L', jL, IntermediateField.adjoin.finiteDimensional hint', ?_, ?_, fun x => rfl, ?_⟩
  ·
    intro σ'
    have h1 : aeval (σ' α') (p.map j) = 0 := hq _ (hm'root σ')
    have h2 : aeval (φ.symm (σ' α')) p = 0 := by
      apply φ.injective; rw [key, φ.apply_symm_apply, h1, map_zero]
    obtain ⟨τ, hτ⟩ := horb _ h2
    refine ⟨c τ, fun x => ?_⟩
    have e : φ ((τ : G E Ω) α) = (c τ : G E' Ω') α' := hc τ α
    have hx : (c τ : G E' Ω') α' = σ' α' := by
      rw [← e, hτ, φ.apply_symm_apply]
    have hle : L'.toSubalgebra ≤ AlgHom.equalizer ((c τ : G E' Ω') : Ω' →ₐ[E'] Ω') (σ' : Ω' →ₐ[E'] Ω') := by
      rw [hL', IntermediateField.adjoin_simple_toSubalgebra_of_isAlgebraic hint'.isAlgebraic, Algebra.adjoin_le_iff,
        Set.singleton_subset_iff]
      exact hx
    exact hle x.2
  · rw [IntermediateField.adjoin.finrank hint', IntermediateField.adjoin.finrank hint]
    apply le_antisymm
    · calc m'.natDegree ≤ (p.map j).natDegree := natDegree_le_of_dvd hdvd hqne
        _ = p.natDegree := natDegree_map j
    · haveI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed E
      haveI : IsAlgClosed Ω' := IsAlgClosure.isAlgClosed E'
      have hsep : p.Separable := (minpoly.irreducible hint).separable
      have hnd : (p.aroots Ω).Nodup := nodup_roots (hsep.map)
      have hm'ne : m' ≠ 0 := minpoly.ne_zero hint'
      have hpne : p ≠ 0 := hpmon.ne_zero
      have himg : (p.aroots Ω).toFinset.image φ ⊆ (m'.aroots Ω').toFinset := by
        intro y hy
        obtain ⟨β, hβ, rfl⟩ := Finset.mem_image.1 hy
        rw [Multiset.mem_toFinset, mem_aroots] at hβ ⊢
        obtain ⟨τ, rfl⟩ := horb _ hβ.2
        refine ⟨hm'ne, ?_⟩
        have e : φ ((τ : G E Ω) α) = (c τ : G E' Ω') α' := hc τ α
        rw [e]; exact hm'root _
      calc p.natDegree = (p.aroots Ω).card := IsAlgClosed.card_aroots_eq_natDegree.symm
        _ = (p.aroots Ω).toFinset.card := (Multiset.toFinset_card_of_nodup hnd).symm
        _ = ((p.aroots Ω).toFinset.image φ).card := (Finset.card_image_of_injective _ φ.injective).symm
        _ ≤ (m'.aroots Ω').toFinset.card := Finset.card_le_card himg
        _ ≤ (m'.aroots Ω').card := Multiset.toFinset_card_le _
        _ = m'.natDegree := IsAlgClosed.card_aroots_eq_natDegree
  ·
    apply Subalgebra.map_injective (f := L'.val) Subtype.val_injective
    rw [AlgHom.map_adjoin, Algebra.map_top, IntermediateField.range_val]
    apply le_antisymm
    · rw [Algebra.adjoin_le_iff]
      rintro _ ⟨_, ⟨x, rfl⟩, rfl⟩
      exact (jL x).2
    · have hsg : ({α'} : Set Ω') ⊆ L'.val '' Set.range jL :=
        Set.singleton_subset_iff.2 ⟨jL ⟨α, IntermediateField.mem_adjoin_simple_self E α⟩, ⟨_, rfl⟩, rfl⟩
      refine le_trans ?_ (Algebra.adjoin_mono hsg)
      rw [hL', IntermediateField.adjoin_simple_toSubalgebra_of_isAlgebraic hint'.isAlgebraic]

end
end

