module

public import Mathlib
public import GroundTheory.HeightsAndTheta.Heights.FieldsOfNumbers.Statements
public import GroundTheory.HeightsAndTheta.Heights.FieldsOfNumbers.Bundle0003
public import GroundTheory.HeightsAndTheta.Heights.FieldsOfNumbers.Bundle0004

@[expose] public section

-- bundled from GroundTheory.HeightsAndTheta.Heights.FieldsOfNumbers.PHilbExactDivide
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.FieldNumbers

open MvPolynomial GroundTheory.Heights₂.Heights.NumbersDVR

noncomputable section

universe u

namespace HilbExactDivide

variable {K : Type} [DecidableEq K] {ι : K → Type} {F : Type u} [Field F]

attribute [local instance] MvPolynomial.weightedGradedAlgebra


open scoped Classical in
open Classical in
theorem component_mul_form {c : K → ℕ} {s : MRing ι F} (hs : IsMultiHomog s c)
    (t : MRing ι F) (n : K → ℕ) :
    weightedHomogeneousComponent (blockWeight ι) n (t * s) =
      if c ≤ n then weightedHomogeneousComponent (blockWeight ι) (n - c) t * s else 0 := by
  have hs' : s ∈ weightedHomogeneousSubmodule F (blockWeight ι) c :=
    (mem_weightedHomogeneousSubmodule _ _ _ _).mpr hs
  have := DirectSum.coe_decompose_mul_of_right_mem
    (𝒜 := weightedHomogeneousSubmodule F (blockWeight ι)) n (a := t) hs'
  rw [← weightedDecomposition.decompose'_apply, ← weightedDecomposition.decompose'_apply]
  exact this

theorem exists_sub_component_mem {I : Ideal (MRing ι F)} (hI : IsMultiHomogIdeal I)
    {s f : MRing ι F} {n : K → ℕ} (hf : IsMultiHomog f n) (hfL : f ∈ I ⊔ Ideal.span {s}) :
    ∃ t : MRing ι F, f - weightedHomogeneousComponent (blockWeight ι) n (t * s) ∈ I := by
  obtain ⟨a, ha, b, hb, rfl⟩ := Submodule.mem_sup.mp hfL
  obtain ⟨t, rfl⟩ := Ideal.mem_span_singleton'.mp hb
  refine ⟨t, ?_⟩
  have h1 : weightedHomogeneousComponent (blockWeight ι) n (a + t * s) = a + t * s :=
    IsWeightedHomogeneous.weightedHomogeneousComponent_same hf
  have e : a + t * s - weightedHomogeneousComponent (blockWeight ι) n (t * s) =
      weightedHomogeneousComponent (blockWeight ι) n a := by
    rw [sub_eq_iff_eq_add, ← map_add (f := _), h1]
  rw [e]
  exact hI a ha n


omit [DecidableEq K] in
theorem mem_colon_span_iff {I : Ideal (MRing ι F)} {s g : MRing ι F} :
    g ∈ I.colon (Ideal.span {s}) ↔ g * s ∈ I := by
  rw [Submodule.mem_colon]
  constructor
  · intro h
    simpa [smul_eq_mul] using h s (Ideal.subset_span rfl)
  · intro h x hx
    obtain ⟨t, rfl⟩ := Ideal.mem_span_singleton'.mp hx
    rw [smul_eq_mul, show g * (t * s) = t * (g * s) by ring]
    exact I.mul_mem_left t h


open Classical in
theorem finrank_eq (h1 : GradedFinite.Statement.{u}) [Fintype K] [∀ k, Fintype (ι k)]
    {I : Ideal (MRing ι F)} (hI : IsMultiHomogIdeal I) {c : K → ℕ} {s : MRing ι F}
    (hs : IsMultiHomog s c) (n : K → ℕ) :
    Module.finrank F (gradedPiece I n) =
      Module.finrank F (gradedPiece (I ⊔ Ideal.span {s}) n) +
        (if c ≤ n then Module.finrank F (gradedPiece (I.colon (Ideal.span {s})) (n - c))
          else 0) := by
  have hIL : I ≤ I ⊔ Ideal.span {s} := le_sup_left
  let π : (MRing ι F ⧸ I) →ₗ[F] (MRing ι F ⧸ (I ⊔ Ideal.span {s})) :=
    (Ideal.Quotient.liftₐ I (Ideal.Quotient.mkₐ F (I ⊔ Ideal.span {s}))
      (fun a ha => by
        rw [Ideal.Quotient.mkₐ_eq_mk, Ideal.Quotient.eq_zero_iff_mem]
        exact hIL ha)).toLinearMap
  have hπ : ∀ x, π (Ideal.Quotient.mk I x) = Ideal.Quotient.mk (I ⊔ Ideal.span {s}) x :=
    fun x => rfl
  have : FiniteDimensional F (gradedPiece I n) := (h1 F K ι I n).1
  have hrn := (π.domRestrict (gradedPiece I n)).finrank_range_add_finrank_ker
  have hrange : LinearMap.range (π.domRestrict (gradedPiece I n)) =
      gradedPiece (I ⊔ Ideal.span {s}) n := by
    rw [LinearMap.range_domRestrict, gradedPiece, gradedPiece, ← Submodule.map_comp]
    congr 1

  have hkerdesc : ∀ y ∈ LinearMap.ker (π.domRestrict (gradedPiece I n)),
      ∃ f : MRing ι F, IsMultiHomog f n ∧ f ∈ I ⊔ Ideal.span {s} ∧
        ((y : gradedPiece I n) : MRing ι F ⧸ I) = Ideal.Quotient.mk I f := by
    rintro ⟨y, hy⟩ hker
    obtain ⟨f, hf, rfl⟩ := Submodule.mem_map.mp hy
    refine ⟨f, (mem_weightedHomogeneousSubmodule _ _ _ _).mp hf, ?_, rfl⟩
    rw [LinearMap.mem_ker, LinearMap.domRestrict_apply] at hker
    have : π (Ideal.Quotient.mk I f) = 0 := hker
    rwa [hπ, Ideal.Quotient.eq_zero_iff_mem] at this
  rw [← hrange, ← hrn]
  congr 1
  by_cases hc : c ≤ n
  · rw [if_pos hc]
    let W := weightedHomogeneousSubmodule F (blockWeight ι) (n - c)
    let α : W →ₗ[F] (MRing ι F ⧸ I.colon (Ideal.span {s})) :=
      (Ideal.Quotient.mkₐ F (I.colon (Ideal.span {s}))).toLinearMap ∘ₗ W.subtype
    let β : W →ₗ[F] (MRing ι F ⧸ I) :=
      (Ideal.Quotient.mkₐ F I).toLinearMap ∘ₗ (LinearMap.mulRight F s) ∘ₗ W.subtype
    have hker : LinearMap.ker α = LinearMap.ker β := by
      ext g
      simp [α, β, Ideal.Quotient.eq_zero_iff_mem]
      rw [← map_mul, Ideal.Quotient.eq_zero_iff_mem]
    have e1 : LinearMap.range α = gradedPiece (I.colon (Ideal.span {s})) (n - c) := by
      rw [LinearMap.range_comp, Submodule.range_subtype]
      rfl
    have e2 : LinearMap.range β =
        (LinearMap.ker (π.domRestrict (gradedPiece I n))).map (gradedPiece I n).subtype := by
      ext x
      constructor
      · rintro ⟨⟨g, hg⟩, rfl⟩
        have hgs : g * s ∈ weightedHomogeneousSubmodule F (blockWeight ι) n := by
          have := IsWeightedHomogeneous.mul ((mem_weightedHomogeneousSubmodule _ _ _ _).mp hg) hs
          rw [tsub_add_cancel_of_le hc] at this
          exact (mem_weightedHomogeneousSubmodule _ _ _ _).mpr this
        refine ⟨⟨(Ideal.Quotient.mkₐ F I).toLinearMap (g * s), Submodule.mem_map_of_mem hgs⟩,
          ?_, rfl⟩
        rw [SetLike.mem_coe, LinearMap.mem_ker, LinearMap.domRestrict_apply]
        change π ((Ideal.Quotient.mkₐ F I) (g * s)) = 0
        rw [Ideal.Quotient.mkₐ_eq_mk, hπ, Ideal.Quotient.eq_zero_iff_mem]
        exact Ideal.mem_sup_right (Ideal.mem_span_singleton'.mpr ⟨g, rfl⟩)
      · rintro ⟨y, hy, rfl⟩
        obtain ⟨f, hf, hfL, hyf⟩ := hkerdesc y hy
        obtain ⟨t, ht⟩ := exists_sub_component_mem hI hf hfL
        rw [component_mul_form hs, if_pos hc] at ht
        refine ⟨⟨weightedHomogeneousComponent (blockWeight ι) (n - c) t,
          weightedHomogeneousComponent_mem _ _ _⟩, ?_⟩
        change Ideal.Quotient.mk I (weightedHomogeneousComponent (blockWeight ι) (n - c) t * s) =
          ((y : gradedPiece I n) : MRing ι F ⧸ I)
        rw [hyf, Ideal.Quotient.eq]
        simpa using I.neg_mem ht
    have eα : LinearMap.range α ≃ₗ[F] LinearMap.range β :=
      α.quotKerEquivRange.symm ≪≫ₗ Submodule.quotEquivOfEq _ _ hker ≪≫ₗ β.quotKerEquivRange
    rw [← e1, eα.finrank_eq, e2]
    exact (Submodule.equivMapOfInjective (gradedPiece I n).subtype Subtype.val_injective
      (LinearMap.ker (π.domRestrict (gradedPiece I n)))).finrank_eq
  · rw [if_neg hc]
    have hbot : LinearMap.ker (π.domRestrict (gradedPiece I n)) = ⊥ := by
      rw [eq_bot_iff]
      intro y hy
      obtain ⟨f, hf, hfL, hyf⟩ := hkerdesc y hy
      obtain ⟨t, ht⟩ := exists_sub_component_mem hI hf hfL
      rw [component_mul_form hs, if_neg hc, sub_zero] at ht
      rw [Submodule.mem_bot]
      apply Subtype.ext
      rw [hyf, ZeroMemClass.coe_zero, Ideal.Quotient.eq_zero_iff_mem]
      exact ht
    rw [hbot, finrank_bot]

theorem proof (h1 : GradedFinite.Statement.{u}) : HilbExactDivide.Statement.{u} := by
  intro F _ K _ _ ι _ I hI c s hs m
  by_cases hm : ∀ k, 0 ≤ m k
  · obtain ⟨n, rfl⟩ : ∃ n : K → ℕ, m = fun k => (n k : ℤ) :=
      ⟨fun k => (m k).toNat, funext fun k => (Int.toNat_of_nonneg (hm k)).symm⟩
    have key := finrank_eq h1 hI hs n
    rw [(h1 F K ι I n).2, (h1 F K ι (I ⊔ Ideal.span {s}) n).2, key]
    by_cases hc : c ≤ n
    · rw [if_pos hc]
      have hnc : ((fun k => (n k : ℤ)) - fun k => (c k : ℤ)) = fun k => ((n - c) k : ℤ) :=
        funext fun k => by
          have : c k ≤ n k := hc k
          simp only [Pi.sub_apply]
          omega
      rw [hnc, (h1 F K ι _ (n - c)).2]
      push_cast
      ring
    · rw [if_neg hc]
      have hneg : hilbFn (I.colon (Ideal.span {s}))
          ((fun k => (n k : ℤ)) - fun k => (c k : ℤ)) = 0 := by
        rw [hilbFn, if_neg]
        intro hall
        apply hc
        intro k
        show c k ≤ n k
        have := hall k
        simp only [Pi.sub_apply] at this
        omega
      rw [hneg]
      push_cast
      ring
  · have hm' : ¬ ∀ k, 0 ≤ (m - fun k => (c k : ℤ)) k := by
      intro hall
      apply hm
      intro k
      have := hall k
      simp only [Pi.sub_apply] at this
      omega
    simp only [hilbFn, if_neg hm, if_neg hm', sub_zero]

theorem closed : HilbExactDivide.Statement.{u} :=
  proof GradedFinite.proof

end HilbExactDivide

end

end GroundTheory.Heights₂.Heights.FieldNumbers
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.FieldsOfNumbers.PIntNumBase
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.FieldNumbers

open MvPolynomial GroundTheory.Heights₂.Heights.NumbersDVR

noncomputable section

universe u

section Point

variable {F : Type u} [Field F] {K : Type} [Fintype K] [DecidableEq K] {ι : K → Type}
  [∀ k, Fintype (ι k)]

def blockMonomial (i : ∀ k, ι k) (m : K → ℕ) : MRing ι F :=
  ∏ k, X ⟨k, i k⟩ ^ m k


omit [∀ k, Fintype (ι k)] in
theorem blockMonomial_isMultiHomog (i : ∀ k, ι k) (m : K → ℕ) :
    IsMultiHomog (blockMonomial (F := F) i m) m := by
  have h := IsWeightedHomogeneous.prod (R := F) (w := blockWeight ι) Finset.univ
    (fun k => (X ⟨k, i k⟩ : MRing ι F) ^ m k) (fun k => m k • blockWeight ι ⟨k, i k⟩)
    (fun k _ => (isWeightedHomogeneous_X F (blockWeight ι) ⟨k, i k⟩).pow (m k))
  have hm : (∑ k, m k • blockWeight ι ⟨k, i k⟩) = m := by
    funext k'
    simp [blockWeight, Finset.sum_apply, Pi.single_apply]
  rw [hm] at h
  exact h


omit [DecidableEq K] [∀ k, Fintype (ι k)] in
theorem blockMonomial_add (i : ∀ k, ι k) (m n : K → ℕ) :
    blockMonomial (F := F) i (m + n) = blockMonomial i m * blockMonomial i n := by
  simp [blockMonomial, pow_add, Finset.prod_mul_distrib]


omit [DecidableEq K] [∀ k, Fintype (ι k)] in
theorem blockMonomial_mk_ne_zero (P : Ideal (MRing ι F)) [P.IsPrime] (i : ∀ k, ι k)
    (hi : ∀ k, (X ⟨k, i k⟩ : MRing ι F) ∉ P) (m : K → ℕ) :
    Ideal.Quotient.mk P (blockMonomial i m) ≠ 0 := by
  unfold blockMonomial
  rw [map_prod, Finset.prod_ne_zero_iff]
  intro k _
  rw [map_pow]
  refine pow_ne_zero _ ?_
  rw [Ne, Ideal.Quotient.eq_zero_iff_mem]
  exact hi k

end Point

theorem IntNumBase.proof (h1 : MixedDiffConst.Statement.{u}) : IntNumBase.Statement.{u} := by
  intro F _ K _ _ ι _ P hP hrel
  have := hP.isPrime

  have hev : ∀ᶠ m in Filter.atTop, hilbFn P m = intNum F P (n := 0) ![] := by
    have h0 : relDim P = ((0 : ℕ) : WithBot (WithTop ℤ)) := by rw [hrel]; rfl
    filter_upwards [(h1 F K ι P hP.multiHomog hP.relevant 0 h0).1 ![]] with m hm
    simpa [mixedDiff] using hm
  set c := intNum F P (n := 0) ![] with hc
  obtain ⟨M0, hM0⟩ := Filter.eventually_atTop.mp hev
  choose i hi using hP.relevant
  set A := MRing ι F ⧸ P
  set L := FractionRing A
  let xm : (K → ℕ) → L := fun m => algebraMap A L (Ideal.Quotient.mk P (blockMonomial i m))
  have hxm : ∀ m, xm m ≠ 0 := fun m => by
    simp only [xm, ne_eq, FaithfulSMul.algebraMap_eq_zero_iff]
    exact blockMonomial_mk_ne_zero P i hi m
  have hxm_add : ∀ m n, xm (m + n) = xm m * xm n := fun m n => by
    simp only [xm, blockMonomial_add, map_mul]

  let φ : (K → ℕ) → A →ₗ[F] L := fun m =>
    (LinearMap.mulRight F (xm m)⁻¹).comp (IsScalarTower.toAlgHom F A L).toLinearMap
  have hφ : ∀ m a, φ m a = algebraMap A L a / xm m := fun m a => by
    simp [φ, div_eq_mul_inv]
  have hφinj : ∀ m, Function.Injective (φ m) := fun m a b hab => by
    rw [hφ, hφ, div_left_inj' (hxm m)] at hab
    exact IsFractionRing.injective A L hab
  let U : (K → ℕ) → Submodule F L := fun m => (gradedPiece P m).map (φ m)
  have memU : ∀ m y, y ∈ U m ↔ ∃ f : MRing ι F, IsMultiHomog f m ∧
      y = algebraMap A L (Ideal.Quotient.mk P f) / xm m := fun m y => by
    simp only [U, gradedPiece, Submodule.mem_map, hφ]
    constructor
    · rintro ⟨a, ⟨f, hf, rfl⟩, rfl⟩
      exact ⟨f, (mem_weightedHomogeneousSubmodule _ _ _ _).mp hf, rfl⟩
    · rintro ⟨f, hf, rfl⟩
      exact ⟨_, ⟨f, (mem_weightedHomogeneousSubmodule _ _ _ _).mpr hf, rfl⟩, rfl⟩
  have hfinU : ∀ m, FiniteDimensional F (U m) := fun m => by
    have := ((GradedFinite.proof.{u}) F K ι P m).1
    exact LinearEquiv.finiteDimensional (Submodule.equivMapOfInjective _ (hφinj m) _)
  have hrankU : ∀ m, Module.finrank F (U m) = Module.finrank F (gradedPiece P m) := fun m =>
    (LinearEquiv.finrank_eq (Submodule.equivMapOfInjective _ (hφinj m) _)).symm
  have hmono : ∀ m n, m ≤ n → U m ≤ U n := fun m n hmn y hy => by
    obtain ⟨f, hf, rfl⟩ := (memU m y).mp hy
    refine (memU n _).mpr ⟨f * blockMonomial i (n - m), ?_, ?_⟩
    · have := hf.mul (blockMonomial_isMultiHomog (F := F) i (n - m))
      rwa [add_tsub_cancel_of_le hmn] at this
    · have hn : xm n = xm m * xm (n - m) := by rw [← hxm_add, add_tsub_cancel_of_le hmn]
      rw [hn, map_mul, map_mul]
      exact (mul_div_mul_right _ _ (hxm (n - m))).symm
  have hmul : ∀ m n y z, y ∈ U m → z ∈ U n → y * z ∈ U (m + n) := fun m n y z hy hz => by
    obtain ⟨f, hf, rfl⟩ := (memU m y).mp hy
    obtain ⟨g, hg, rfl⟩ := (memU n z).mp hz
    refine (memU _ _).mpr ⟨f * g, hf.mul hg, ?_⟩
    rw [hxm_add, map_mul, map_mul]
    exact div_mul_div_comm _ _ _ _

  let N : K → ℕ := fun k => (M0 k).toNat
  have hrankc : ∀ n, N ≤ n → (Module.finrank F (U n) : ℤ) = c := fun n hn => by
    rw [hrankU, ← ((GradedFinite.proof.{u}) F K ι P n).2]
    refine hM0 _ fun k => ?_
    exact (Int.self_le_toNat (M0 k)).trans (by exact_mod_cast hn k)
  have hstab : ∀ m, U m ≤ U N := fun m => by
    have hN : U N = U (m ⊔ N) := by
      have := hfinU (m ⊔ N)
      refine Submodule.eq_of_le_of_finrank_eq (hmono _ _ le_sup_right) ?_
      have h1 := hrankc N le_rfl
      have h2 := hrankc (m ⊔ N) le_sup_right
      exact_mod_cast h1.trans h2.symm
    rw [hN]
    exact hmono _ _ le_sup_left

  have hone : (1 : L) ∈ U N := by
    refine hstab 0 ((memU 0 1).mpr ⟨1, isWeightedHomogeneous_one F _, ?_⟩)
    have : xm 0 = 1 := by simp [xm, blockMonomial]
    rw [this, map_one, map_one, div_one]
  let S : Subalgebra F L := (U N).toSubalgebra hone fun y z hy hz => hstab _ (hmul _ _ _ _ hy hz)
  have : FiniteDimensional F S := hfinU N
  let E : IntermediateField F L := S.toIntermediateField fun y hy =>
    S.inv_mem_of_algebraic (x := ⟨y, hy⟩) ((IsIntegral.of_finite F (⟨y, hy⟩ : S)).map S.val).isAlgebraic
  have hEq : homFracDegZero P = E := by
    apply le_antisymm
    · refine IntermediateField.adjoin_le_iff.mpr ?_
      rintro x ⟨b, f, g, hf, hg, hgP, rfl⟩
      have hfU : algebraMap A L (Ideal.Quotient.mk P f) / xm b ∈ E :=
        hstab b ((memU b _).mpr ⟨f, hf, rfl⟩)
      have hgU : algebraMap A L (Ideal.Quotient.mk P g) / xm b ∈ E :=
        hstab b ((memU b _).mpr ⟨g, hg, rfl⟩)
      have hg0 : algebraMap A L (Ideal.Quotient.mk P g) ≠ 0 := by
        rw [Ne, FaithfulSMul.algebraMap_eq_zero_iff, Ideal.Quotient.eq_zero_iff_mem]
        exact hgP
      have heq : algebraMap A L (Ideal.Quotient.mk P f) / algebraMap A L (Ideal.Quotient.mk P g) =
          algebraMap A L (Ideal.Quotient.mk P f) / xm b *
            (algebraMap A L (Ideal.Quotient.mk P g) / xm b)⁻¹ := by
        rw [inv_div, div_mul_div_comm, mul_comm (xm b), mul_div_mul_right _ _ (hxm b)]
      rw [SetLike.mem_coe, heq]
      exact E.mul_mem hfU (E.inv_mem hgU)
    · intro y hy
      obtain ⟨f, hf, rfl⟩ := (memU N y).mp hy
      exact IntermediateField.subset_adjoin _ _
        ⟨N, f, blockMonomial i N, hf, blockMonomial_isMultiHomog i N,
          fun h => blockMonomial_mk_ne_zero P i hi N (Ideal.Quotient.eq_zero_iff_mem.mpr h), rfl⟩
  have hES : Subalgebra.toSubmodule E.toSubalgebra = U N := rfl
  let e : E ≃ₗ[F] U N := LinearEquiv.ofEq _ _ hES
  rw [hEq]
  refine ⟨LinearEquiv.finiteDimensional e.symm, ?_⟩
  rw [e.finrank_eq]
  exact (hrankc N le_rfl).symm

end

end GroundTheory.Heights₂.Heights.FieldNumbers
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.FieldsOfNumbers.PRenameIntNum
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.FieldNumbers

open MvPolynomial GroundTheory.Heights₂.Heights.NumbersDVR Filter

noncomputable section

universe u

namespace RenameIntNum

variable {K₁ K₂ : Type*} (e : K₁ ≃ K₂)

def precompIso : (K₂ → ℤ) ≃o (K₁ → ℤ) where
  toFun m := m ∘ e
  invFun m := m ∘ e.symm
  left_inv m := by funext k; simp
  right_inv m := by funext k; simp
  map_rel_iff' := by
    intro a b
    constructor
    · intro h k
      simpa using h (e.symm k)
    · intro h k
      exact h (e k)

theorem eventualValue_comp (g : (K₁ → ℤ) → ℤ) :
    eventualValue (fun m : K₂ → ℤ => g (m ∘ e)) = eventualValue g := by
  have key : ∀ c, (∀ᶠ m in atTop, (fun m : K₂ → ℤ => g (m ∘ e)) m = c) ↔
      ∀ᶠ m in atTop, g m = c := by
    intro c
    rw [← (precompIso e).map_atTop, Filter.eventually_map]
    rfl
  unfold eventualValue
  by_cases hg : ∃ c, ∀ᶠ m in atTop, g m = c
  · have hf : ∃ c, ∀ᶠ m in atTop, (fun m : K₂ → ℤ => g (m ∘ e)) m = c :=
      hg.imp fun c hc => (key c).2 hc
    rw [dite_eq_left hf, dite_eq_left hg]
    obtain ⟨m, h1, h2⟩ := (((key _).1 hf.choose_spec).and hg.choose_spec).exists
    exact h1.symm.trans h2
  · have hf : ¬ ∃ c, ∀ᶠ m in atTop, (fun m : K₂ → ℤ => g (m ∘ e)) m = c :=
      fun ⟨c, hc⟩ => hg ⟨c, (key c).1 hc⟩
    rw [dite_eq_right hf, dite_eq_right hg]

theorem mixedDiff_comp {n : ℕ} (bs : Fin n → K₂ → ℤ) (h : (K₁ → ℤ) → ℤ) :
    mixedDiff bs (fun m => h (m ∘ e)) = fun m => mixedDiff (fun i => bs i ∘ e) h (m ∘ e) := by
  unfold mixedDiff
  have hl : List.ofFn (fun i => bs i ∘ e) = (List.ofFn bs).map (fun b => b ∘ e) := by
    rw [List.map_ofFn]
    rfl
  rw [hl]
  generalize List.ofFn bs = l
  induction l with
  | nil => rfl
  | cons b l ih =>
    rw [List.foldr_cons, List.map_cons, List.foldr_cons, ih]
    rfl

theorem proof (h : RenameHilbFn.Statement.{u}) : RenameIntNum.Statement.{u} := by
  intro F _ S K' _ _ κ ι' E σ hσ P n bs
  have hH : hilbFn (P.comap (rename σ)) = fun m => hilbFn P (m ∘ E.symm) :=
    funext fun m => h F S K' κ ι' E σ hσ P m
  unfold intNum
  rw [hH, mixedDiff_comp E.symm bs (hilbFn P),
    eventualValue_comp E.symm (mixedDiff (fun i => bs i ∘ E.symm) (hilbFn P))]

end RenameIntNum

end

end GroundTheory.Heights₂.Heights.FieldNumbers
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.FieldsOfNumbers.StatementsContractRelDimLe
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.FieldNumbers

open MvPolynomial GroundTheory.Heights₂.Heights.NumbersDVR

noncomputable section

universe u

def ContractRelDimLe.Statement : Prop :=
  ∀ (F : Type u) [Field F] (K K' : Type) [Fintype K] [DecidableEq K] [Fintype K']
    [DecidableEq K'] (j : K ↪ K') (ι' : K' → Type) [∀ k, Fintype (ι' k)]
    (P' : Ideal (MRing ι' F)), IsMultiProjPrime P' → relDim (contractPrime j P') ≤ relDim P'

end

end GroundTheory.Heights₂.Heights.FieldNumbers
end

