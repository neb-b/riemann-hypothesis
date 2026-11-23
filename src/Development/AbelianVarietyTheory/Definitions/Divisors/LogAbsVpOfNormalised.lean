module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.HermitianTraceForms.IsLocallyConstantRankAtStalkEigenSub

@[expose] public section

set_option autoImplicit false

noncomputable section

open scoped TensorProduct NNReal NumberField Pointwise
open GlobalTheory.EigenSplit

namespace GlobalTheory.HTLat

section Eigen

variable {O C : Type} [CommRing O] [Field C] [Algebra O C]
  {V : Type} [AddCommGroup V] [Module C V] [Module O V] [IsScalarTower O C V]
  {Λ : Type} [CommRing Λ] (ρ : Λ →+* Module.End C V)

def eigSubLat (χ : Λ →+* C) (X : Submodule O V) : Submodule O V :=
  X ⊓ (eigenSub ρ χ).restrictScalars O

variable {ι : Type} [DecidableEq ι] {σ : ι → Λ →+* C} (h : IsSplitting σ)

def eigQuotLat (i : ι) (X : Submodule O V) : Submodule O V :=
  X.map ((proj h ρ i).restrictScalars O)

set_option autoImplicit false in
open scoped TensorProduct NNReal NumberField Pointwise in
variable {O C : Type} [CommRing O] [Field C] [Algebra O C]
  {V : Type} [AddCommGroup V] [Module C V] [Module O V] [IsScalarTower O C V]
  {Λ : Type} [CommRing Λ] (ρ : Λ →+* Module.End C V) in
variable {ι : Type} [DecidableEq ι] {σ : ι → Λ →+* C} (h : IsSplitting σ) in
set_option autoImplicit false in
open scoped TensorProduct NNReal NumberField Pointwise in
variable {O C : Type} [CommRing O] [Field C] [Algebra O C]
  {V : Type} [AddCommGroup V] [Module C V] [Module O V] [IsScalarTower O C V]
  {Λ : Type} [CommRing Λ] (ρ : Λ →+* Module.End C V) in
variable {ι : Type} [DecidableEq ι] {σ : ι → Λ →+* C} (h : _root_.GlobalTheory.EigenSplit.IsSplitting σ) in
theorem _root_.GlobalTheory.HTLat.eigSubLat_le_eigQuotLat (i : ι) (X : Submodule O V) :
    _root_.GlobalTheory.HTLat.eigSubLat ρ (σ i) X ≤ _root_.GlobalTheory.HTLat.eigQuotLat ρ h i X := by
  intro x hx
  exact ⟨x, hx.1, _root_.GlobalTheory.EigenSplit.proj_of_mem h hx.2⟩

set_option autoImplicit false in
open scoped TensorProduct NNReal NumberField Pointwise in
variable {O C : Type} [CommRing O] [Field C] [Algebra O C]
  {V : Type} [AddCommGroup V] [Module C V] [Module O V] [IsScalarTower O C V]
  {Λ : Type} [CommRing Λ] (ρ : Λ →+* Module.End C V) in
variable {ι : Type} [DecidableEq ι] {σ : ι → Λ →+* C} (h : _root_.GlobalTheory.EigenSplit.IsSplitting σ) in
theorem _root_.GlobalTheory.HTLat.eigSubLat_mono (χ : Λ →+* C) {X Y : Submodule O V} (hXY : X ≤ Y) :
    _root_.GlobalTheory.HTLat.eigSubLat ρ χ X ≤ _root_.GlobalTheory.HTLat.eigSubLat ρ χ Y :=
  inf_le_inf_right _ hXY

end Eigen

section Embeddings

variable {C : Type} [Field C] {v : Valuation C ℝ≥0} {O : Type} [CommRing O] [Algebra O C]
  (hv : v.Integers O) {E : Type} [Field E] [NumberField E]

def embO (φ : E →+* C) : 𝓞 E →+* O :=
  let e : O ≃+* (algebraMap O C).range := RingEquiv.ofBijective (algebraMap O C).rangeRestrict
    ⟨fun _ _ hab => hv.hom_inj (congrArg Subtype.val hab), (algebraMap O C).rangeRestrict_surjective⟩
  e.symm.toRingHom.comp ((φ.comp (algebraMap (𝓞 E) E)).codRestrict _ fun a =>
    hv.exists_of_le_one (hv.isIntegral_iff_v_le_one.1
      ((map_isIntegral_int φ (NumberField.RingOfIntegers.isIntegral_coe a)).tower_top)))

set_option autoImplicit false in
open scoped TensorProduct NNReal NumberField Pointwise in
variable {C : Type} [Field C] {v : Valuation C ℝ≥0} {O : Type} [CommRing O] [Algebra O C]
  (hv : v.Integers O) {E : Type} [Field E] [NumberField E] in
omit [NumberField E] in
theorem _root_.GlobalTheory.HTLat.algebraMap_embO (φ : E →+* C) (a : 𝓞 E) :
    algebraMap O C (_root_.GlobalTheory.HTLat.embO hv φ a) = φ a := by
  have hb : Function.Bijective (algebraMap O C).rangeRestrict :=
    ⟨fun _ _ hab => hv.hom_inj (congrArg Subtype.val hab), (algebraMap O C).rangeRestrict_surjective⟩
  have hm : ∀ x, (φ.comp (algebraMap (𝓞 E) E)) x ∈ (algebraMap O C).range := fun x =>
    hv.exists_of_le_one (hv.isIntegral_iff_v_le_one.1
      ((map_isIntegral_int φ (NumberField.RingOfIntegers.isIntegral_coe x)).tower_top))
  exact congrArg Subtype.val
    ((RingEquiv.ofBijective (algebraMap O C).rangeRestrict hb).apply_symm_apply
      ((φ.comp (algebraMap (𝓞 E) E)).codRestrict _ hm a))


set_option autoImplicit false in
open scoped TensorProduct NNReal NumberField Pointwise in
variable {C : Type} [Field C] {v : Valuation C ℝ≥0} {O : Type} [CommRing O] [Algebra O C]
  (hv : v.Integers O) {E : Type} [Field E] [NumberField E] in
theorem _root_.GlobalTheory.HTLat.isSplitting_embO [IsAlgClosed C] [CharZero C] :
    _root_.GlobalTheory.EigenSplit.IsSplitting
      (fun φ : E →+* C => (algebraMap O C).comp (_root_.GlobalTheory.HTLat.embO hv φ)) := by
  classical
  have hfun : (fun φ : E →+* C => (algebraMap O C).comp (_root_.GlobalTheory.HTLat.embO hv φ)) =
      fun φ => (RingHom.id C).comp (φ.comp (algebraMap (𝓞 E) E)) := by
    funext φ
    ext a
    simp [_root_.GlobalTheory.HTLat.algebraMap_embO]
  rw [hfun]
  refine _root_.GlobalTheory.EigenSplit.isSplitting_of_isDomain (E := E) ?_
    (NumberField.Embeddings.card E C) _ ?_
  · intro φ ψ h
    exact IsLocalization.ringHom_ext (nonZeroDivisors (𝓞 E)) h
  · exact isUnit_iff_ne_zero.2 (Int.cast_ne_zero.2 (NumberField.discr_ne_zero E))

end Embeddings

section Graded

variable {O C : Type} [CommRing O] [Field C] [Algebra O C]
  {U : Type} [AddCommGroup U] [Module C U] [Module O U] [IsScalarTower O C U]

def grLat (La : Submodule O U) (F' F : Submodule C U) : Submodule O (U ⧸ F') :=
  (La ⊓ F.restrictScalars O).map (F'.mkQ.restrictScalars O)

def scaleLat (a : C) (La : Submodule O U) : Submodule O U :=
  La.map ((a • LinearMap.id : U →ₗ[C] U).restrictScalars O)

theorem mem_scaleLat {a : C} {La : Submodule O U} {x : U} :
    x ∈ scaleLat a La ↔ ∃ y ∈ La, a • y = x := Iff.rfl

variable (v : Valuation C ℝ≥0)

def latNorm (La : Submodule O U) (x : U) : ℝ≥0 := sInf {r | ∃ a : C, x ∈ scaleLat a La ∧ v a = r}

variable {v}

theorem latNorm_span_singleton (hv : v.Integers O) {g : U} (hg : g ≠ 0) (c : C) :
    latNorm v (Submodule.span O {g}) (c • g) = v c := by
  refine IsLeast.csInf_eq ⟨⟨c, ⟨g, Submodule.mem_span_singleton_self g, rfl⟩, rfl⟩, ?_⟩
  rintro _ ⟨a, ⟨y, hy, hay⟩, rfl⟩
  obtain ⟨b, rfl⟩ := Submodule.mem_span_singleton.1 hy
  have h1 : (a * algebraMap O C b) • g = c • g := by
    rw [mul_smul, algebraMap_smul]; exact hay
  rw [← smul_left_injective C hg h1, map_mul]
  exact mul_le_of_le_one_right' (hv.map_le_one b)

set_option autoImplicit false in
open scoped TensorProduct NNReal NumberField Pointwise in
variable {O C : Type} [CommRing O] [Field C] [Algebra O C]
  {U : Type} [AddCommGroup U] [Module C U] [Module O U] [IsScalarTower O C U] in
variable {v : Valuation C ℝ≥0} in
set_option autoImplicit false in
open scoped TensorProduct NNReal NumberField Pointwise in
variable {O C : Type} [CommRing O] [Field C] [Algebra O C]
  {U : Type} [AddCommGroup U] [Module C U] [Module O U] [IsScalarTower O C U] in
variable (v : Valuation C ℝ≥0) in
variable {v} in
theorem _root_.GlobalTheory.HTLat.fg_inf (hv : v.Integers O) {La : Submodule O U} (hfg : La.FG)
    (F : Submodule C U) : (La ⊓ F.restrictScalars O).FG := by
  have hinj : Function.Injective (algebraMap O C) := hv.hom_inj
  haveI : IsDomain O := Function.Injective.isDomain (algebraMap O C) hinj
  haveI : ValuationRing O := ValuationRing.of_integers v hv
  haveI : Module.Finite O La := Module.Finite.iff_fg.mpr hfg
  have key : ∀ (o : O) (u : U), o ≠ 0 → o • u ∈ F → u ∈ F := by
    intro o u ho hu
    have h0 : algebraMap O C o ≠ 0 := by
      intro h
      exact ho (hinj (by rw [h, map_zero]))
    rw [← algebraMap_smul C o u] at hu
    have := F.smul_mem (algebraMap O C o)⁻¹ hu
    rwa [smul_smul, inv_mul_cancel₀ h0, one_smul] at this
  let g : La →ₗ[O] U ⧸ F.restrictScalars O := (F.restrictScalars O).mkQ ∘ₗ La.subtype
  have htf : Submodule.torsion O (LinearMap.range g) = ⊥ := by
    rw [eq_bot_iff]
    intro x hx
    obtain ⟨⟨o, ho⟩, hox⟩ := (Submodule.mem_torsion_iff x).1 hx
    obtain ⟨q, hq⟩ := x
    obtain ⟨u, rfl⟩ := Submodule.mkQ_surjective _ q
    have hox' : o • (F.restrictScalars O).mkQ u = 0 := congrArg Subtype.val hox
    rw [← LinearMap.map_smul, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero] at hox'
    have hu : u ∈ F := key o u (nonZeroDivisors.ne_zero ho) hox'
    rw [Submodule.mem_bot]
    ext
    simpa using hu
  haveI : Module.Flat O (LinearMap.range g) :=
    (Module.Flat.flat_iff_torsion_eq_bot_of_isBezout).2 htf
  haveI : Module.Free O (LinearMap.range g) := Module.free_of_flat_of_isLocalRing
  haveI : Module.FinitePresentation O (LinearMap.range g) :=
    Module.finitePresentation_of_projective _ _
  have hker := Module.FinitePresentation.fg_ker g.rangeRestrict
    (LinearMap.surjective_rangeRestrict g)
  rw [LinearMap.ker_rangeRestrict] at hker
  have heq : La ⊓ F.restrictScalars O = (LinearMap.ker g).map La.subtype := by
    ext x
    constructor
    · rintro ⟨hx1, hx2⟩
      exact ⟨⟨x, hx1⟩, by simpa [g] using hx2, rfl⟩
    · rintro ⟨y, hy, rfl⟩
      exact ⟨y.2, by simpa [g] using hy⟩
  rw [heq]
  exact hker.map _

end Graded

section Frames

variable {O C : Type} [CommRing O] [Field C] [Algebra O C]
  {U : Type} [AddCommGroup U] [Module C U] [Module O U] [IsScalarTower O C U] {N : ℕ}

variable (C) in
def step (f : Fin N → U) (i : ℕ) : Submodule C U := Submodule.span C (f '' {k | (k : ℕ) < i})

set_option autoImplicit false in
open scoped TensorProduct NNReal NumberField Pointwise in
variable {O C : Type} [CommRing O] [Field C] [Algebra O C]
  {U : Type} [AddCommGroup U] [Module C U] [Module O U] [IsScalarTower O C U] {N : ℕ} in
theorem _root_.GlobalTheory.HTLat.step_zero (f : Fin N → U) :
    _root_.GlobalTheory.HTLat.step C f 0 = ⊥ := by
  simp [_root_.GlobalTheory.HTLat.step]

set_option autoImplicit false in
open scoped TensorProduct NNReal NumberField Pointwise in
variable {O C : Type} [CommRing O] [Field C] [Algebra O C]
  {U : Type} [AddCommGroup U] [Module C U] [Module O U] [IsScalarTower O C U] {N : ℕ} in
theorem _root_.GlobalTheory.HTLat.step_mono (f : Fin N → U) :
    Monotone (_root_.GlobalTheory.HTLat.step C f) := by
  intro i j hij
  refine Submodule.span_mono (Set.image_mono ?_)
  intro k hk
  exact lt_of_lt_of_le hk hij

set_option autoImplicit false in
open scoped TensorProduct NNReal NumberField Pointwise in
variable {O C : Type} [CommRing O] [Field C] [Algebra O C]
  {U : Type} [AddCommGroup U] [Module C U] [Module O U] [IsScalarTower O C U] {N : ℕ} in
theorem _root_.GlobalTheory.HTLat.mem_step_succ (f : Fin N → U) (i : Fin N) :
    f i ∈ _root_.GlobalTheory.HTLat.step C f (i + 1) :=
  Submodule.subset_span ⟨i, Nat.lt_succ_self _, rfl⟩

variable (C) in
def grAt (La : Submodule O U) (f : Fin N → U) (i : Fin N) : Submodule O (U ⧸ step C f i) :=
  grLat La (step C f i) (step C f (i + 1))

def grNorm (v : Valuation C ℝ≥0) (La : Submodule O U) (f : Fin N → U) (i : Fin N) : ℝ≥0 :=
  latNorm v (grAt C La f i) ((step C f i).mkQ (f i))


set_option autoImplicit false in
open scoped TensorProduct NNReal NumberField Pointwise in
variable {O C : Type} [CommRing O] [Field C] [Algebra O C]
  {U : Type} [AddCommGroup U] [Module C U] [Module O U] [IsScalarTower O C U] {N : ℕ} in
theorem _root_.GlobalTheory.HTLat.exists_grAt_eq {v : Valuation C ℝ≥0} (hv : v.Integers O)
    {La : Submodule O U} (hfg : La.FG)
    (f : Fin N → U) (i : Fin N) (hf : f i ∉ _root_.GlobalTheory.HTLat.step C f i) {a : C}
    (ha : a ≠ 0) {y : U} (hy : y ∈ _root_.GlobalTheory.HTLat.step C f i)
    (hLa : a • f i + y ∈ La) :
    ∃ c : C, c ≠ 0 ∧ _root_.GlobalTheory.HTLat.grAt C La f i =
        Submodule.span O {c • (_root_.GlobalTheory.HTLat.step C f i).mkQ (f i)} ∧
      _root_.GlobalTheory.HTLat.grNorm v La f i = (v c)⁻¹ := by
  classical
  set S := _root_.GlobalTheory.HTLat.step C f i with hS
  set S' := _root_.GlobalTheory.HTLat.step C f (i + 1) with hS'
  set xb := S.mkQ (f i) with hxb
  have hxb0 : xb ≠ 0 := by
    rw [hxb, Submodule.mkQ_apply, Ne, Submodule.Quotient.mk_eq_zero]
    exact hf
  have hSS' : S ≤ S' := _root_.GlobalTheory.HTLat.step_mono f (Nat.le_succ _)
  have hfi : f i ∈ S' := _root_.GlobalTheory.HTLat.mem_step_succ f i
  have hS'le : S' ≤ S ⊔ C ∙ f i := by
    refine Submodule.span_le.2 ?_
    rintro _ ⟨k, hk, rfl⟩
    rcases Nat.lt_succ_iff_lt_or_eq.1 hk with hk | hk
    · exact Submodule.mem_sup_left (Submodule.subset_span ⟨k, hk, rfl⟩)
    · rw [Fin.ext hk]
      exact Submodule.mem_sup_right (Submodule.mem_span_singleton_self _)
  have hG : ∀ q ∈ _root_.GlobalTheory.HTLat.grAt C La f i, ∃ b : C, q = b • xb := by
    intro q hq
    obtain ⟨w, hw, rfl⟩ := Submodule.mem_map.1 hq
    obtain ⟨s, hs, t, ht, hst⟩ := Submodule.mem_sup.1 (hS'le hw.2)
    obtain ⟨b, rfl⟩ := Submodule.mem_span_singleton.1 ht
    refine ⟨b, ?_⟩
    show S.mkQ w = b • S.mkQ (f i)
    rw [← hst, map_add (f := _), map_smul, Submodule.mkQ_apply S s,
      (Submodule.Quotient.mk_eq_zero S).2 hs, zero_add]
  have hmem : a • xb ∈ _root_.GlobalTheory.HTLat.grAt C La f i := by
    refine Submodule.mem_map.2 ⟨a • f i + y, ⟨hLa, ?_⟩, ?_⟩
    · exact S'.add_mem (S'.smul_mem a hfi) (hSS' hy)
    · show S.mkQ (a • f i + y) = a • S.mkQ (f i)
      rw [map_add (f := _), map_smul, Submodule.mkQ_apply S y, (Submodule.Quotient.mk_eq_zero S).2 hy,
        add_zero]
  have hGfg : (_root_.GlobalTheory.HTLat.grAt C La f i).FG :=
    (_root_.GlobalTheory.HTLat.fg_inf hv hfg S').map _
  obtain ⟨s, hs⟩ := hGfg
  choose! coef hcoef using hG
  have hsG : ∀ q ∈ s, q ∈ _root_.GlobalTheory.HTLat.grAt C La f i := fun q hq =>
    hs ▸ Submodule.subset_span hq
  have hsne : s.Nonempty := by
    rw [Finset.nonempty_iff_ne_empty]
    rintro rfl
    rw [Finset.coe_empty, Submodule.span_empty] at hs
    rw [← hs, Submodule.mem_bot] at hmem
    exact smul_ne_zero ha hxb0 hmem
  obtain ⟨q₀, hq₀, hmax⟩ := s.exists_max_image (fun q => v (coef q)) hsne
  have hc : coef q₀ ≠ 0 := by
    intro hc0
    have hzero : ∀ q ∈ (s : Set (U ⧸ S)), q = 0 := by
      intro q hq
      have h1 := hmax q hq
      rw [hc0, map_zero, nonpos_iff_eq_zero, Valuation.zero_iff] at h1
      rw [hcoef q (hsG q hq), h1, zero_smul]
    have hbot : _root_.GlobalTheory.HTLat.grAt C La f i = ⊥ := by
      rw [← hs, Submodule.span_eq_bot]
      exact hzero
    rw [hbot, Submodule.mem_bot] at hmem
    exact smul_ne_zero ha hxb0 hmem
  have hspan : _root_.GlobalTheory.HTLat.grAt C La f i = Submodule.span O {coef q₀ • xb} := by
    apply le_antisymm
    · rw [← hs, Submodule.span_le]
      intro q hq
      have hle : v (coef q / coef q₀) ≤ 1 := by
        rw [map_div₀]
        exact div_le_one_of_le₀ (hmax q hq) (by positivity)
      obtain ⟨o, ho⟩ := hv.exists_of_le_one hle
      rw [SetLike.mem_coe, Submodule.mem_span_singleton]
      refine ⟨o, ?_⟩
      rw [← algebraMap_smul C o, ho, smul_smul, div_mul_cancel₀ _ hc, ← hcoef q (hsG q hq)]
    · rw [Submodule.span_le, Set.singleton_subset_iff, SetLike.mem_coe,
        ← hcoef q₀ (hsG q₀ hq₀)]
      exact hsG q₀ hq₀
  refine ⟨coef q₀, hc, hspan, ?_⟩
  show _root_.GlobalTheory.HTLat.latNorm v (_root_.GlobalTheory.HTLat.grAt C La f i) xb = _
  rw [hspan]
  unfold _root_.GlobalTheory.HTLat.latNorm _root_.GlobalTheory.HTLat.scaleLat
  refine IsLeast.csInf_eq ⟨⟨(coef q₀)⁻¹, ?_, map_inv₀ v _⟩, ?_⟩
  · refine Submodule.mem_map.2 ⟨coef q₀ • xb, Submodule.mem_span_singleton_self _, ?_⟩
    simp only [LinearMap.coe_restrictScalars, LinearMap.smul_apply, LinearMap.id_apply]
    rw [smul_smul, inv_mul_cancel₀ hc, one_smul]
  · rintro r ⟨b, hb, rfl⟩
    obtain ⟨z, hz, hbz⟩ := Submodule.mem_map.1 hb
    obtain ⟨o, rfl⟩ := Submodule.mem_span_singleton.1 hz
    have h1 : (b * algebraMap O C o * coef q₀) • xb = xb := by
      have e1 : (b • LinearMap.id : (U ⧸ S) →ₗ[C] (U ⧸ S)) (o • coef q₀ • xb) = xb := hbz
      rw [LinearMap.smul_apply, LinearMap.id_apply, ← algebraMap_smul C o, smul_smul,
        smul_smul] at e1
      exact e1
    have h2 : b * algebraMap O C o * coef q₀ = 1 := by
      have h3 : (b * algebraMap O C o * coef q₀ - 1) • xb = 0 := by
        rw [sub_smul, h1, one_smul, sub_self]
      exact sub_eq_zero.1 ((smul_eq_zero.1 h3).resolve_right hxb0)
    have h4 : b * algebraMap O C o = (coef q₀)⁻¹ := eq_inv_of_mul_eq_one_left h2
    show (v (coef q₀))⁻¹ ≤ v b
    rw [← map_inv₀, ← h4, map_mul]
    exact mul_le_of_le_one_right (by positivity) (hv.map_le_one o)

def logAbs_vp (p : ℕ) (v : Valuation C ℝ≥0) (r : ℝ≥0) : ℝ :=
  -(Real.log p * (Real.log r / Real.log (v (p : C))))

theorem logAbs_vp_self (p : ℕ) (v : Valuation C ℝ≥0) (h0 : v (p : C) ≠ 0) (h1 : v (p : C) < 1) :
    logAbs_vp p v (v (p : C)) = -Real.log p := by
  have : Real.log (v (p : C)) ≠ 0 :=
    (Real.log_neg (NNReal.coe_pos.2 (pos_iff_ne_zero.2 h0)) (by exact_mod_cast h1)).ne
  rw [logAbs_vp, div_self this, mul_one]

variable {U' : Type} [AddCommGroup U'] [Module C U'] [Module O U'] [IsScalarTower O C U']

end Frames

end GlobalTheory.HTLat
