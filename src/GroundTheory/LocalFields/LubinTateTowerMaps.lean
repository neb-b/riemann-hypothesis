module

public import Mathlib
public import GroundTheory.LocalFields.Bundle0013

@[expose] public section

noncomputable section

open IntermediateField

namespace GroundTheory.LocalField

open ValuativeRel

section Restrict

variable {K Ω : Type*} [Field K] [Field Ω] [Algebra K Ω]

def restrictAutFun {E F : IntermediateField K Ω} (h : F ≤ E) [Normal K F] (σ : E ≃ₐ[K] E) :
    F ≃ₐ[K] F :=
  AlgHom.restrictNormal' ((E.val.comp (σ : E →ₐ[K] E)).comp (inclusion h)) F

theorem restrictAutFun_apply {E F : IntermediateField K Ω} (h : F ≤ E) [Normal K F]
    (σ : E ≃ₐ[K] E) (x : F) : ((restrictAutFun h σ x : F) : Ω) = σ ⟨x, h x.2⟩ := by
  have := AlgHom.restrictNormal_commutes ((E.val.comp (σ : E →ₐ[K] E)).comp (inclusion h)) F x
  simp only [restrictAutFun, AlgHom.restrictNormal', AlgEquiv.coe_ofBijective]
  exact this

def restrictAut {E F : IntermediateField K Ω} (h : F ≤ E) [Normal K F] :
    (E ≃ₐ[K] E) →* (F ≃ₐ[K] F) where
  toFun := restrictAutFun h
  map_one' := AlgEquiv.ext fun x => Subtype.ext (by rw [restrictAutFun_apply]; rfl)
  map_mul' σ τ := AlgEquiv.ext fun x => Subtype.ext (by
    rw [AlgEquiv.mul_apply, restrictAutFun_apply, restrictAutFun_apply]
    have : (⟨(restrictAutFun h τ x : Ω), h (restrictAutFun h τ x).2⟩ : E) = τ ⟨x, h x.2⟩ :=
      Subtype.ext (restrictAutFun_apply h τ x)
    rw [this]
    rfl)

theorem restrictAut_apply {E F : IntermediateField K Ω} (h : F ≤ E) [Normal K F]
    (σ : E ≃ₐ[K] E) (x : F) : ((restrictAut h σ x : F) : Ω) = σ ⟨x, h x.2⟩ :=
  restrictAutFun_apply h σ x

theorem restrictAut_self {E : IntermediateField K Ω} [Normal K E] (σ : E ≃ₐ[K] E) :
    restrictAut le_rfl σ = σ :=
  AlgEquiv.ext fun x => Subtype.ext (by rw [restrictAut_apply])

theorem algEquiv_ext_of_restrictAut {ι : Type*} {F : ι → IntermediateField K Ω}
    [∀ n, Normal K (F n)] {E : IntermediateField K Ω} (hle : ∀ n, F n ≤ E)
    (hE : ∀ x ∈ E, ∃ n, x ∈ F n) {σ σ' : E ≃ₐ[K] E}
    (h : ∀ n, restrictAut (hle n) σ = restrictAut (hle n) σ') : σ = σ' := by
  refine AlgEquiv.ext fun x => Subtype.ext ?_
  obtain ⟨n, hn⟩ := hE x x.2
  have := congrArg (fun τ : F n ≃ₐ[K] F n => ((τ ⟨x, hn⟩ : F n) : Ω)) (h n)
  simp only [restrictAut_apply] at this
  exact this

theorem exists_algEquiv_of_compatible {F : ℕ → IntermediateField K Ω} (hF : Monotone F)
    [∀ n, Normal K (F n)] {E : IntermediateField K Ω} [Algebra.IsAlgebraic K E]
    (hle : ∀ n, F n ≤ E) (hE : ∀ x ∈ E, ∃ n, x ∈ F n) (τ : ∀ n, F n ≃ₐ[K] F n)
    (hτ : ∀ m n (h : m ≤ n), restrictAut (hF h) (τ n) = τ m) :
    ∃ σ : E ≃ₐ[K] E, ∀ n, restrictAut (hle n) σ = τ n := by
  have hτ' : ∀ i j (x : Ω) (hi : x ∈ F i) (hj : x ∈ F j),
      ((τ i ⟨x, hi⟩ : F i) : Ω) = ((τ j ⟨x, hj⟩ : F j) : Ω) := by
    intro i j x hi hj
    rcases le_total i j with h | h
    · rw [← hτ i j h, restrictAut_apply]
    · rw [← hτ j i h, restrictAut_apply]
  let S : ℕ → Subalgebra K Ω := fun n => (F n).toSubalgebra
  have hS : Monotone S := fun _ _ h => hF h
  let f : ∀ n, S n →ₐ[K] Ω := fun n => (F n).val.comp (τ n : F n →ₐ[K] F n)
  have hf : ∀ (i j : ℕ) (h : S i ≤ S j), f i = (f j).comp (Subalgebra.inclusion h) := by
    intro i j h
    ext x
    exact hτ' i j x x.2 (h x.2)
  have hT : E.toSubalgebra ≤ iSup S := fun x hx => by
    obtain ⟨n, hn⟩ := hE x hx
    exact (le_iSup S n) hn
  let g := Subalgebra.iSupLift S hS.directed_le f hf E.toSubalgebra hT
  have hg : ∀ (x : E) (n : ℕ) (hn : (x : Ω) ∈ F n), g x = ((τ n ⟨x, hn⟩ : F n) : Ω) :=
    fun x n hn => Subalgebra.iSupLift_of_mem (K := S) x hn
  have hgE : ∀ x : E, g x ∈ E := fun x => by
    obtain ⟨n, hn⟩ := hE x x.2
    rw [hg x n hn]
    exact hle n (τ n ⟨x, hn⟩).2
  let g' : E →ₐ[K] E := g.codRestrict E.toSubalgebra hgE
  refine ⟨AlgEquiv.ofBijective g' (Algebra.IsAlgebraic.algHom_bijective _), fun n => ?_⟩
  refine AlgEquiv.ext fun x => Subtype.ext ?_
  rw [restrictAut_apply, AlgEquiv.ofBijective_apply]
  exact hg ⟨x, hle n x.2⟩ n x.2

end Restrict

namespace FormalGroup

section Reduce

variable {K : Type*} [Field K] [ValuativeRel K]

def unitsReduce (π : 𝒪[K]) {m n : ℕ} (h : m ≤ n) :
    (𝒪[K] ⧸ Ideal.span {π ^ n})ˣ →* (𝒪[K] ⧸ Ideal.span {π ^ m})ˣ :=
  Units.map (Ideal.Quotient.factor
    (Ideal.span_singleton_le_span_singleton.mpr (pow_dvd_pow π h))).toMonoidHom

theorem coe_unitsReduce (π : 𝒪[K]) {m n : ℕ} (h : m ≤ n) (u : (𝒪[K] ⧸ Ideal.span {π ^ n})ˣ)
    (a : 𝒪[K]) (ha : Ideal.Quotient.mk _ a = (u : 𝒪[K] ⧸ Ideal.span {π ^ n})) :
    (unitsReduce π h u : 𝒪[K] ⧸ Ideal.span {π ^ m}) = Ideal.Quotient.mk _ a := by
  rw [unitsReduce, Units.coe_map, ← ha]
  exact Ideal.Quotient.factor_mk _ a

def unitsMk (π : 𝒪[K]) (n : ℕ) : 𝒪[K]ˣ →* (𝒪[K] ⧸ Ideal.span {π ^ n})ˣ :=
  Units.map (Ideal.Quotient.mk (Ideal.span {π ^ n})).toMonoidHom

theorem coe_unitsMk (π : 𝒪[K]) (n : ℕ) (u : 𝒪[K]ˣ) :
    (unitsMk π n u : 𝒪[K] ⧸ Ideal.span {π ^ n}) = Ideal.Quotient.mk _ (u : 𝒪[K]) := rfl

theorem unitsReduce_unitsMk (π : 𝒪[K]) {m n : ℕ} (h : m ≤ n) (u : 𝒪[K]ˣ) :
    unitsReduce π h (unitsMk π n u) = unitsMk π m u :=
  Units.ext (coe_unitsReduce π h _ _ rfl)

end Reduce

section Char

variable {K : Type*} [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
variable {Ω : Type*} [Field Ω] [ValuativeRel Ω] [TopologicalSpace Ω] [IsValuativeTopology Ω]
  [Algebra K Ω] [ValuativeExtension K Ω] [Algebra.IsAlgebraic K Ω]
variable {π : 𝒪[K]} (hπ : Irreducible π) {f g : PowerSeries 𝒪[K]}

variable [IsSepClosed Ω]

open Polynomial in
local instance normal_lubinTateField (hf : IsLubinTateSeries π f) (n : ℕ) :
    Normal K (lubinTateField Ω hπ hf n) := by
  have hq := one_lt_card_residueField' K
  have hlt : IsLubinTateSeries π (ltPoly π : PowerSeries 𝒪[K]) := {
    constantCoeff_eq_zero := by
      rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply, Polynomial.coeff_coe, ltPoly]
      simp [coeff_X_pow, show 0 ≠ Nat.card 𝓀[K] by omega]
    coeff_one := by
      rw [Polynomial.coeff_coe, ltPoly]
      simp [coeff_X_pow, hq.ne]
    dvd_coeff_sub := fun k => by
      rw [coeff_ltPoly_sub, coeff_C_mul_X]
      split_ifs
      · exact dvd_rfl
      · exact dvd_zero π }
  have hpow (x : IdealPoint Ω (lubinTateFormalGroup hπ hlt)) :
      (π ^ n • x).val = aeval x.val ((ltPolyIter π n).map (algebraMap 𝒪[K] K)) := by
    have := t2Space_of_isValuativeTopology Ω
    induction n with
    | zero => simp [ltPolyIter_zero]
    | succ n ih =>
      rw [pow_succ', mul_smul, lubinTate_uniformizer_smul_val hlt, psEval_polynomial, ih,
        ltPolyIter_succ, Polynomial.map_comp, aeval_comp]
  let p := (ltPolyIter π n).map (algebraMap 𝒪[K] K)
  have hsep : p.Separable := separable_ltPolyIter hπ n
  have htorsion (x : IdealPoint Ω (lubinTateFormalGroup hπ hlt)) :
      x ∈ lubinTateTorsion Ω hlt n ↔ aeval x.val ((ltPolyIter π n).map (algebraMap 𝒪[K] K)) = 0 := by
    rw [mem_lubinTateTorsion, ← hpow]
    exact ⟨fun h => by rw [h]; rfl, fun h => IdealPoint.ext h⟩
  have hroots : IdealPoint.val '' (lubinTateTorsion Ω (hπ := hπ) hlt n :
      Set (IdealPoint Ω (lubinTateFormalGroup hπ hlt))) = p.rootSet Ω := by
    ext z
    rw [mem_rootSet_of_ne hsep.ne_zero]
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact (htorsion x).mp hx
    · intro hz
      let x : IdealPoint Ω (lubinTateFormalGroup hπ hlt) :=
        IdealPoint.mk z (valuation_lt_one_of_aeval_ltPolyIter_eq_zero hπ n hz)
      exact ⟨x, (htorsion x).mpr hz, rfl⟩
  rw [lubinTateField_eq hπ hf hlt, lubinTateField, hroots]
  have := adjoin_rootSet_isSplittingField (IsSepClosed.splits_codomain p hsep) (L := Ω)
  exact Normal.of_isSplittingField p

def lubinTateChar (hf : IsLubinTateSeries π f) (n : ℕ) {E : IntermediateField K Ω}
    (hE : lubinTateField Ω hπ hf n ≤ E) : (E ≃ₐ[K] E) →* (𝒪[K] ⧸ Ideal.span {π ^ n})ˣ :=
  (lubinTateGalEquiv hπ hf n).toMonoidHom.comp (restrictAut hE)

theorem lubinTateChar_spec (hf : IsLubinTateSeries π f) {n : ℕ} {E : IntermediateField K Ω}
    (hE : lubinTateField Ω hπ hf n ≤ E) (σ : E ≃ₐ[K] E)
    {x : IdealPoint Ω (lubinTateFormalGroup hπ hf)} (hx : x ∈ lubinTateTorsion Ω hf n) (a : 𝒪[K])
    (ha : Ideal.Quotient.mk _ a = (lubinTateChar hπ hf n hE σ : 𝒪[K] ⧸ Ideal.span {π ^ n})) :
    ((σ ⟨x.val, hE (val_mem_lubinTateField hπ hf hx)⟩ : E) : Ω) = (a • x).val :=
  (restrictAut_apply hE σ ⟨x.val, val_mem_lubinTateField hπ hf hx⟩).symm.trans
    (lubinTateGalEquiv_spec hf n (restrictAut hE σ) x hx a ha)

theorem lubinTateChar_eq_of_apply (hf : IsLubinTateSeries π f) {n : ℕ} {E : IntermediateField K Ω}
    (hE : lubinTateField Ω hπ hf n ≤ E) (σ : E ≃ₐ[K] E) (a : 𝒪[K])
    (h : ∀ (x) (hx : x ∈ lubinTateTorsion Ω (hπ := hπ) hf n),
      ((σ ⟨x.val, hE (val_mem_lubinTateField hπ hf hx)⟩ : E) : Ω) = (a • x).val) :
    (lubinTateChar hπ hf n hE σ : 𝒪[K] ⧸ Ideal.span {π ^ n}) = Ideal.Quotient.mk _ a := by
  obtain ⟨l, hl, hann, -⟩ := exists_generator_lubinTateTorsion (Ω := Ω) (hπ := hπ) hf n
  obtain ⟨b, hb⟩ := Ideal.Quotient.mk_surjective
    (lubinTateChar hπ hf n hE σ : 𝒪[K] ⧸ Ideal.span {π ^ n})
  have h1 := lubinTateChar_spec hπ hf hE σ hl b hb
  rw [h l hl] at h1
  have h2 : b • l = a • l := (IdealPoint.ext h1).symm
  rw [← hb, Ideal.Quotient.eq, ← hann, sub_smul, sub_eq_zero]
  exact h2

theorem lubinTateChar_reduce (hf : IsLubinTateSeries π f) {m n : ℕ} (hmn : m ≤ n)
    {E : IntermediateField K Ω} (hE : lubinTateField Ω hπ hf n ≤ E) (σ : E ≃ₐ[K] E) :
    lubinTateChar hπ hf m ((lubinTateField_mono hπ hf hmn).trans hE) σ =
      unitsReduce π hmn (lubinTateChar hπ hf n hE σ) := by
  obtain ⟨a, ha⟩ := Ideal.Quotient.mk_surjective
    (lubinTateChar hπ hf n hE σ : 𝒪[K] ⧸ Ideal.span {π ^ n})
  apply Units.ext
  rw [coe_unitsReduce π hmn _ a ha, lubinTateChar_eq_of_apply hπ hf _ σ a]
  intro x hx
  exact lubinTateChar_spec hπ hf hE σ (lubinTateTorsion_mono hπ hf hmn hx) a ha

theorem lubinTateGalEquiv_restrictAut (hf : IsLubinTateSeries π f) {m n : ℕ} (hmn : m ≤ n)
    (σ : lubinTateField Ω hπ hf n ≃ₐ[K] lubinTateField Ω hπ hf n) :
    lubinTateGalEquiv hπ hf m (restrictAut (lubinTateField_mono hπ hf hmn) σ) =
      unitsReduce π hmn (lubinTateGalEquiv hπ hf n σ) := by
  have := lubinTateChar_reduce hπ hf hmn le_rfl σ
  simp only [lubinTateChar, MonoidHom.coe_comp, Function.comp_apply, restrictAut_self] at this
  exact this

end Char

end FormalGroup

end GroundTheory.LocalField
