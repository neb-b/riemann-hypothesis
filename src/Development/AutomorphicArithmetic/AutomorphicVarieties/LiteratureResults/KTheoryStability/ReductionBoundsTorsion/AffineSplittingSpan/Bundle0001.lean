module

public import Mathlib
public import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.KTheoryStability.ReductionBoundsTorsion.AffineSplittingSpan.Transfer
public import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.Bundle0011

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.KTheoryStability.ReductionBoundsTorsion.AffineSplittingSpan.EigenKill
section
noncomputable section

open Polynomial

namespace PositivityTheory.KB.SplitAffineSpectral.EigenLocalizationShapes

def gpoly (Λ : ℂ) : ℝ[X] := X ^ 2 - C (2 * Λ.re) * X + C (Complex.normSq Λ)

theorem gpoly_eval_one (Λ : ℂ) : (gpoly Λ).eval 1 = Complex.normSq (1 - Λ) := by
  simp only [gpoly, eval_add, eval_sub, eval_pow, eval_X, eval_mul, eval_C, Complex.normSq_apply,
    Complex.sub_re, Complex.one_re, Complex.sub_im, Complex.one_im]
  ring

theorem mapOp_apply {A : Type} (φ : A → A) (m : ℕ) (F : (Fin m → A) → ℝ) (y : Fin m → A) :
    mapOp φ m F y = F fun i => φ (y i) := rfl

theorem kill_one {A : Type} (φ : A → A) (m : ℕ) (E : (Fin m → A) → ℂ) (Λ z : ℂ)
    (hE : ∀ y, E (fun i => φ (y i)) = Λ * E y) :
    aeval (mapOp φ m) (gpoly Λ) (fun y => (z * E y).re) = 0 := by
  simp only [gpoly, map_add (f := _), map_sub, map_mul, aeval_X, aeval_C, map_pow]
  funext y
  simp only [LinearMap.add_apply, LinearMap.sub_apply, Module.End.mul_apply, pow_two,
    Module.algebraMap_end_apply, Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, mapOp_apply,
    hE, Pi.zero_apply]
  simp only [Complex.mul_re, Complex.mul_im, Complex.normSq_apply]
  ring

theorem kill_sum {A : Type} (φ : A → A) (m : ℕ) {ι : Type} [Fintype ι] [DecidableEq ι]
    (E : ι → (Fin m → A) → ℂ) (Λ z : ι → ℂ) (hE : ∀ j y, E j (fun i => φ (y i)) = Λ j * E j y)
    (F : (Fin m → A) → ℝ) (hF : ∀ y, (F y : ℂ) = ∑ j, z j * E j y) :
    aeval (mapOp φ m) (∏ j, gpoly (Λ j)) F = 0 := by
  have hF' : F = ∑ j, fun y => (z j * E j y).re := by
    funext y
    rw [Finset.sum_apply, ← Complex.re_sum, ← hF y, Complex.ofReal_re]
  set_option synthInstance.maxHeartbeats 100000 in
    rw [hF', map_sum]
  refine Finset.sum_eq_zero fun j _ => ?_
  rw [← Finset.prod_erase_mul _ _ (Finset.mem_univ j), map_mul, Module.End.mul_apply,
    kill_one φ m (E j) (Λ j) (z j) (hE j), map_zero]

theorem cup_kill {A : Type} [Group A] (φ : A →* A) {ι : Type} [Fintype ι] [DecidableEq ι]
    (β : ι → Additive A → ℂ) (lam : ι → ℂ)
    (hβ : ∀ j x, β j (Additive.ofMul (φ x)) = lam j * β j (Additive.ofMul x))
    (hspan : ∀ α : Additive A →+ ℝ, ∃ c : ι → ℂ, ∀ x, (α x : ℂ) = ∑ j, c j * β j x) (q : ℕ)
    (α : Fin (q + 1) → (Additive A →+ ℝ)) :
    aeval (mapOp φ (q + 2)) (∏ J : Fin (q + 1) → ι, gpoly (∏ i, lam (J i))) (cupH α) = 0 := by
  choose c hc using hspan
  let d : Fin (q + 1) → (Fin (q + 2) → A) → Additive A :=
    fun i y => Additive.ofMul ((y i.castSucc)⁻¹ * y i.succ)
  let E : (Fin (q + 1) → ι) → (Fin (q + 2) → A) → ℂ := fun J y => ∏ i, β (J i) (d i y)
  let Λ : (Fin (q + 1) → ι) → ℂ := fun J => ∏ i, lam (J i)
  let z : (Fin (q + 1) → ι) → ℂ := fun J => ∏ i, c (α i) (J i)
  have hE : ∀ J y, E J (fun i => φ (y i)) = Λ J * E J y := by
    intro J y
    simp only [E, Λ]
    rw [← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun i _ => ?_
    have : d i (fun k => φ (y k)) = Additive.ofMul (φ ((y i.castSucc)⁻¹ * y i.succ)) := by
      simp only [d, map_mul, map_inv]
    rw [this, hβ]
  have hF : ∀ y, (cupH α y : ℂ) = ∑ J, z J * E J y := by
    intro y
    have h1 : (cupH α y : ℂ) = ∏ i, ∑ j, c (α i) j * β j (d i y) := by
      rw [cupH, Complex.ofReal_prod]
      exact Finset.prod_congr rfl fun i _ => hc (α i) _
    rw [h1, Finset.prod_univ_sum, Fintype.piFinset_univ]
    refine Finset.sum_congr rfl fun J _ => ?_
    simp only [z, E]
    rw [Finset.prod_mul_distrib]
  exact kill_sum (⇑φ) (q + 2) E Λ z hE (cupH α) hF

end PositivityTheory.KB.SplitAffineSpectral.EigenLocalizationShapes
end
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.KTheoryStability.ReductionBoundsTorsion.AffineSplittingSpan.EigenSpan
section
noncomputable section

open NumberField

namespace PositivityTheory.KB.SplitAffineSpectral.EigenLocalizationShapes

variable (L : Type) [Field L] [NumberField L]

def embLin (σ : L →+* ℂ) : 𝓞 L →ₗ[ℤ] ℂ := (σ.comp (algebraMap (𝓞 L) L)).toAddMonoidHom.toIntLinearMap

def coeLin : (𝓞 L →ₗ[ℤ] ℂ) →ₗ[ℂ] (𝓞 L → ℂ) where
  toFun f := ⇑f
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem embLin_linIndep : LinearIndependent ℂ (embLin L) := by
  have hinj : Function.Injective
      (fun σ : L →+* ℂ => ((σ.comp (algebraMap (𝓞 L) L)).toMonoidHom : 𝓞 L →* ℂ)) := by
    intro σ τ h
    apply IsFractionRing.ringHom_ext (A := 𝓞 L)
    intro x
    exact DFunLike.congr_fun h x
  have h1 := (linearIndependent_monoidHom (𝓞 L) ℂ).comp _ hinj
  apply LinearIndependent.of_comp (coeLin L)
  exact h1

theorem finrank_lin : Module.finrank ℂ (𝓞 L →ₗ[ℤ] ℂ) = Fintype.card (L →+* ℂ) := by
  rw [Module.finrank_linearMap_self, NumberField.RingOfIntegers.rank, NumberField.Embeddings.card]

theorem emb_span (α : 𝓞 L →+ ℝ) :
    ∃ c : (L →+* ℂ) → ℂ, ∀ x : 𝓞 L, (α x : ℂ) = ∑ σ, c σ * σ (algebraMap (𝓞 L) L x) := by
  have hspan := (embLin_linIndep L).span_eq_top_of_card_eq_finrank' (finrank_lin L).symm
  let f : 𝓞 L →ₗ[ℤ] ℂ := ((Complex.ofRealHom : ℝ →+* ℂ).toAddMonoidHom.comp α).toIntLinearMap
  have hf : f ∈ Submodule.span ℂ (Set.range (embLin L)) := by
    rw [hspan]
    exact Submodule.mem_top
  obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun ℂ).mp hf
  refine ⟨c, fun x => ?_⟩
  have hx := LinearMap.congr_fun hc x
  simp only [LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul] at hx
  exact hx.symm

theorem mat_span (n r : ℕ) (α : Additive (Multiplicative (Matrix (Fin n) (Fin r) (𝓞 L))) →+ ℝ) :
    ∃ c : Fin n × Fin r × (L →+* ℂ) → ℂ, ∀ x,
      (α x : ℂ) = ∑ j, c j * j.2.2 (algebraMap (𝓞 L) L
        (Multiplicative.toAdd (Additive.toMul x) j.1 j.2.1)) := by
  let e : Matrix (Fin n) (Fin r) (𝓞 L) →+ Additive (Multiplicative (Matrix (Fin n) (Fin r) (𝓞 L))) :=
    { toFun := fun m => Additive.ofMul (Multiplicative.ofAdd m)
      map_zero' := rfl
      map_add' := fun _ _ => rfl }
  have hc : ∀ i j, ∃ c : (L →+* ℂ) → ℂ, ∀ y : 𝓞 L,
      ((α.comp (e.comp (Matrix.singleAddMonoidHom i j))) y : ℂ) =
        ∑ σ, c σ * σ (algebraMap (𝓞 L) L y) :=
    fun i j => emb_span L _
  choose c hc using hc
  refine ⟨fun j => c j.1 j.2.1 j.2.2, fun x => ?_⟩
  have lhs : (α x : ℂ) = ∑ i, ∑ j, ((α.comp (e.comp (Matrix.singleAddMonoidHom i j)))
      (Multiplicative.toAdd (Additive.toMul x) i j) : ℂ) := by
    have hx : x = e (Multiplicative.toAdd (Additive.toMul x)) := rfl
    conv_lhs => rw [hx, Matrix.matrix_eq_sum_single (Multiplicative.toAdd (Additive.toMul x))]
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [map_sum, Complex.ofReal_sum]
    rfl
  rw [lhs]
  simp only [Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  exact hc i j _

end PositivityTheory.KB.SplitAffineSpectral.EigenLocalizationShapes
end
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.KTheoryStability.ReductionBoundsTorsion.AffineSplittingSpan.LcharKerNotFiniteIndex
section
noncomputable section

open NumberField InfinitePlace Pointwise

namespace PositivityTheory.KB.SplitAffineSpectral.unitAtAlt

variable {L : Type} [Field L] [NumberField L]

omit [NumberField L] in
theorem place_pos (v : (𝓞 L)ˣ) (w : InfinitePlace L) : 0 < w (algebraMap (𝓞 L) L (v : 𝓞 L)) := w.pos_iff.mpr (by simp)

def lchar (a : InfinitePlace L → ℕ) : (𝓞 L)ˣ →* Multiplicative ℝ where
  toFun v := Multiplicative.ofAdd (∑ w, (a w : ℝ) * Real.log (w (algebraMap (𝓞 L) L (v : 𝓞 L))))
  map_one' := by simp
  map_mul' x y := by
    rw [← ofAdd_add, ← Finset.sum_add_distrib]
    congr 1
    refine Finset.sum_congr rfl fun w _ => ?_
    rw [Units.val_mul, map_mul, map_mul, Real.log_mul (place_pos x w).ne' (place_pos y w).ne']
    ring

theorem lchar_eq_one_iff (a : InfinitePlace L → ℕ) (v : (𝓞 L)ˣ) :
    lchar a v = 1 ↔ ∏ w, (w (algebraMap (𝓞 L) L (v : 𝓞 L))) ^ a w = 1 := by
  have hpos : ∀ w : InfinitePlace L, 0 < w (algebraMap (𝓞 L) L (v : 𝓞 L)) ^ a w :=
    fun w => pow_pos (place_pos v w) _
  have hP : 0 < ∏ w, w (algebraMap (𝓞 L) L (v : 𝓞 L)) ^ a w :=
    Finset.prod_pos fun w _ => hpos w
  have hlog : Real.log (∏ w, w (algebraMap (𝓞 L) L (v : 𝓞 L)) ^ a w) =
      ∑ w, (a w : ℝ) * Real.log (w (algebraMap (𝓞 L) L (v : 𝓞 L))) := by
    rw [Real.log_prod (fun w _ => (hpos w).ne')]
    exact Finset.sum_congr rfl fun w _ => Real.log_pow _ _
  change Multiplicative.ofAdd (∑ w, (a w : ℝ) * Real.log (w (algebraMap (𝓞 L) L (v : 𝓞 L)))) = 1 ↔ _
  rw [ofAdd_eq_one, ← hlog]
  constructor
  · intro h
    rw [← Real.exp_log hP, h, Real.exp_zero]
  · intro h
    rw [h, Real.log_one]

theorem lchar_nontrivial (hC : IsTotallyComplex L) (a : InfinitePlace L → ℕ) (ha : 0 < ∑ w, a w)
    (hm : ∑ w, a w < nrComplexPlaces L) : ∃ v, lchar a v ≠ 1 := by
  classical
  have hcard : ∑ w, a w < Fintype.card (InfinitePlace L) := by
    rw [card_eq_nrRealPlaces_add_nrComplexPlaces]
    omega
  obtain ⟨w₁, hw₁⟩ : ∃ w₁, a w₁ = 0 := by
    by_contra h
    push_neg at h
    have h1 : ∑ _w : InfinitePlace L, 1 ≤ ∑ w, a w :=
      Finset.sum_le_sum fun w _ => Nat.one_le_iff_ne_zero.mpr (h w)
    simp at h1
    omega
  obtain ⟨w₂, hw₂⟩ : ∃ w₂, 0 < a w₂ := by
    by_contra h
    push_neg at h
    have h0 : ∑ w, a w = 0 := Finset.sum_eq_zero fun w _ => by
      have := h w
      omega
    omega
  have hne : w₂ ≠ w₁ := by
    rintro rfl
    omega
  obtain ⟨u, hu⟩ := NumberField.Units.dirichletUnitTheorem.exists_unit L w₁
  refine ⟨u, fun h => ?_⟩
  change Multiplicative.ofAdd (∑ w, (a w : ℝ) * Real.log (w (algebraMap (𝓞 L) L (u : 𝓞 L)))) = 1 at h
  rw [ofAdd_eq_one] at h
  have hlt : ∑ w, (a w : ℝ) * Real.log (w (algebraMap (𝓞 L) L (u : 𝓞 L))) <
      ∑ _w : InfinitePlace L, (0 : ℝ) := by
    apply Finset.sum_lt_sum
    · intro w _
      by_cases hw : w = w₁
      · subst hw
        simp [hw₁]
      · exact mul_nonpos_of_nonneg_of_nonpos (Nat.cast_nonneg _) (hu w hw).le
    · exact ⟨w₂, Finset.mem_univ _,
        mul_neg_of_pos_of_neg (by exact_mod_cast hw₂) (hu w₂ hne)⟩
  rw [Finset.sum_const_zero, h] at hlt
  exact lt_irrefl _ hlt

theorem lchar_ker_not_finiteIndex (hC : IsTotallyComplex L) (a : InfinitePlace L → ℕ) (ha : 0 < ∑ w, a w)
    (hm : ∑ w, a w < nrComplexPlaces L) : ¬ (lchar a).ker.FiniteIndex := by
  intro hfi
  obtain ⟨v, hv⟩ := lchar_nontrivial hC a ha hm
  apply hv
  have hmem := (lchar a).ker.pow_index_mem v
  rw [MonoidHom.mem_ker, map_pow] at hmem
  have hidx : (lchar a).ker.index ≠ 0 := Subgroup.FiniteIndex.index_ne_zero
  have h1 : Multiplicative.toAdd (lchar a v ^ (lchar a).ker.index) = 0 := by
    rw [hmem]
    rfl
  rw [toAdd_pow, nsmul_eq_mul, mul_eq_zero] at h1
  rcases h1 with h1 | h1
  · exact absurd (by exact_mod_cast h1) hidx
  · exact toAdd_eq_zero.mp h1

end PositivityTheory.KB.SplitAffineSpectral.unitAtAlt

open PositivityTheory.KB.SplitAffineSpectral.unitAtAlt in
theorem PositivityTheory.KB.SplitAffineSpectral.unit : PositivityTheory.KB.SplitAffineSpectral.Unit := by
  unfold PositivityTheory.KB.SplitAffineSpectral.Unit
  intro L _ _ hC m hm
  classical
  by_contra hcon
  push_neg at hcon
  let s : Finset (InfinitePlace L → ℕ) :=
    (Fintype.piFinset fun _ => Finset.range (m + 1)).filter
      fun a => 0 < ∑ w, a w ∧ ∑ w, a w ≤ m
  obtain ⟨k, hk, hfi⟩ := Subgroup.exists_finiteIndex_of_leftCoset_cover
    (H := fun a => (lchar a).ker) (g := fun _ => 1) (s := s) (by
      ext v
      simp only [Set.mem_iUnion, Set.mem_univ, iff_true, one_smul]
      obtain ⟨a, ha0, ham, hprod⟩ := hcon v
      refine ⟨a, ?_, ?_⟩
      · simp only [s, Finset.mem_filter, Fintype.mem_piFinset, Finset.mem_range]
        refine ⟨fun w => ?_, ha0, ham⟩
        have := Finset.single_le_sum (f := a) (fun _ _ => Nat.zero_le _) (Finset.mem_univ w)
        omega
      · exact (MonoidHom.mem_ker).mpr ((lchar_eq_one_iff a v).mpr hprod))
  simp only [s, Finset.mem_filter] at hk
  exact lchar_ker_not_finiteIndex hC k hk.2.1 (lt_of_le_of_lt hk.2.2 hm) hfi
end
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.KTheoryStability.ReductionBoundsTorsion.AffineSplittingSpan.SpanPrism
section
noncomputable section

namespace PositivityTheory.KB.SplitAffineSpectral.PrismSpan

open PositivityTheory.KB.SplitAffineSpectral

variable {Y : Type}

def prism (φ : Y → Y) : {n : ℕ} → ((Fin (n + 1) → Y) → ℝ) → (Fin n → Y) → ℝ
  | 0, _ => fun _ => 0
  | n + 1, F => fun y => F (Fin.cons (y 0) (fun i => φ (y i))) -
      prism φ (n := n) (fun w => F (Fin.cons (y 0) w)) (Fin.tail y)

theorem prism_succ (φ : Y → Y) {n : ℕ} (F : (Fin (n + 2) → Y) → ℝ) (y : Fin (n + 1) → Y) :
    prism φ F y = F (Fin.cons (y 0) (fun i => φ (y i))) -
      prism φ (fun w => F (Fin.cons (y 0) w)) (Fin.tail y) := rfl

theorem comp_cons' {Z : Type} (φ : Y → Z) {n : ℕ} (a : Y) (w : Fin n → Y) :
    (fun i => φ ((Fin.cons a w : Fin (n + 1) → Y) i)) = Fin.cons (φ a) (fun i => φ (w i)) := by
  funext j; refine Fin.cases ?_ (fun k => ?_) j <;> simp

theorem prism_cons (φ : Y → Y) {n : ℕ} (F : (Fin (n + 2) → Y) → ℝ) (a : Y) (w : Fin n → Y) :
    prism φ F (Fin.cons a w) = F (Fin.cons a (Fin.cons (φ a) (fun i => φ (w i)))) -
      prism φ (fun w' => F (Fin.cons a w')) w := by
  rw [prism_succ]
  simp only [Fin.cons_zero, Fin.tail_cons, comp_cons']

theorem dc_cons {m : ℕ} (F : (Fin (m + 2) → Y) → ℝ) (a : Y) (w : Fin (m + 2) → Y) :
    dc F (Fin.cons a w) = F w - dc (fun w' => F (Fin.cons a w')) w :=
  _root_.UpperTheory.Reformulated.B.Qj27.dc_cons F a w

theorem dc_sub {m : ℕ} (F G : (Fin (m + 1) → Y) → ℝ) : dc (F - G) = dc F - dc G := by
  funext y; simp only [dc, Pi.sub_apply, mul_sub, Finset.sum_sub_distrib]

theorem dc_add {m : ℕ} (F G : (Fin (m + 1) → Y) → ℝ) : dc (F + G) = dc F + dc G := by
  funext y; simp only [dc, Pi.add_apply, mul_add, Finset.sum_add_distrib]

theorem dc_smul {m : ℕ} (r : ℝ) (F : (Fin (m + 1) → Y) → ℝ) : dc (r • F) = r • dc F := by
  funext y; simp only [dc, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  ring

theorem dc_comp {Z : Type} {m : ℕ} (F : (Fin (m + 1) → Z) → ℝ) (ψ : Y → Z) (y : Fin (m + 2) → Y) :
    dc (fun w => F (fun i => ψ (w i))) y = dc F (fun i => ψ (y i)) := rfl

theorem prism_sub (φ : Y → Y) : ∀ {n : ℕ} (F G : (Fin (n + 1) → Y) → ℝ),
    prism φ (F - G) = prism φ F - prism φ G := by
  intro n
  induction n with
  | zero =>
    intro F G
    funext y
    simp [prism]
  | succ n ih =>
    intro F G
    funext y
    rw [Pi.sub_apply, prism_succ, prism_succ, prism_succ]
    have hsub : prism φ (fun w => F (Fin.cons (y 0) w) - G (Fin.cons (y 0) w)) (Fin.tail y) =
        prism φ (fun w => F (Fin.cons (y 0) w)) (Fin.tail y) -
          prism φ (fun w => G (Fin.cons (y 0) w)) (Fin.tail y) :=
      congrFun (ih (fun w => F (Fin.cons (y 0) w)) (fun w => G (Fin.cons (y 0) w))) (Fin.tail y)
    change _ - _ - prism φ (fun w => F (Fin.cons (y 0) w) - G (Fin.cons (y 0) w))
      (Fin.tail y) = _
    rw [hsub]
    ring

theorem prism_dc (φ : Y → Y) : ∀ (m : ℕ) (F : (Fin (m + 2) → Y) → ℝ) (y : Fin (m + 2) → Y),
    dc (prism φ F) y + prism φ (dc F) y = F (fun i => φ (y i)) - F y := by
  intro m
  induction m with
  | zero =>
    intro F y
    simp [dc, prism, Fin.sum_univ_succ, Fin.tail]
    have h1 : (Fin.cons (y 0) (fun i : Fin 1 => φ (y (Fin.succAbove 1 i))) : Fin 2 → Y) =
        fun j => (Fin.cons (y 0) (fun i => φ (y i)) : Fin 3 → Y) (Fin.succAbove 2 j) := by
      funext j; fin_cases j <;> rfl
    have h2 : (fun j => (Fin.cons (y 0) (Fin.cons (y 1) (fun i : Fin 1 => φ (y i.succ)) : Fin 2 → Y) :
        Fin 3 → Y) (Fin.succAbove 1 j)) =
        fun j => (Fin.cons (y 0) (fun i => φ (y i)) : Fin 3 → Y) (Fin.succAbove 1 j) := by
      funext j; fin_cases j <;> rfl
    have h3 : (fun j => (Fin.cons (y 0) (Fin.cons (y 1) (fun i : Fin 1 => φ (y i.succ)) : Fin 2 → Y) :
        Fin 3 → Y) (Fin.succAbove 2 j)) = y := by
      funext j; fin_cases j <;> rfl
    rw [h1, h2, h3]
    ring
  | succ m ih =>
    intro F y
    rw [← Fin.cons_self_tail y]
    set a := y 0
    set w := Fin.tail y
    have h := ih (fun w' => F (Fin.cons a w')) w
    rw [dc_cons, prism_cons]
    have e1 : (fun w' => prism φ F (Fin.cons a w')) =
        (fun w' => F (Fin.cons a (Fin.cons (φ a) (fun i => φ (w' i))))) -
          prism φ (fun w' => F (Fin.cons a w')) := by
      funext w'; rw [prism_cons]; rfl
    have e2 : (fun w' => dc F (Fin.cons a w')) =
        F - dc (fun w' => F (Fin.cons a w')) := by
      funext w'; rw [dc_cons]; rfl
    rw [e1, e2, dc_sub, prism_sub, dc_cons, dc_cons]
    simp only [Pi.sub_apply]
    rw [comp_cons']
    have e4 : dc (fun w' => F (Fin.cons a (Fin.cons (φ a) (fun i => φ (w' i))))) w =
        dc (fun w' => F (Fin.cons a (Fin.cons (φ a) w'))) (fun i => φ (w i)) := rfl
    rw [e4]
    linarith only [h]

theorem mul_cons {P : Type} [Group P] (h a : P) {n : ℕ} (w : Fin n → P) :
    (fun i => h * (Fin.cons a w : Fin (n + 1) → P) i) = Fin.cons (h * a) (fun i => h * w i) := by
  funext j; refine Fin.cases ?_ (fun k => ?_) j <;> simp

theorem prism_mul {P : Type} [Group P] (φ : P → P) (h : P) : ∀ {n : ℕ} (F : (Fin (n + 1) → P) → ℝ)
    (y : Fin n → P), prism φ F (fun i => h * y i) =
      prism (fun z => h⁻¹ * φ (h * z)) (fun z => F (fun i => h * z i)) y := by
  intro n
  induction n with
  | zero => intros; rfl
  | succ n ih =>
    intro F y
    have hhead : (fun i => h * (Fin.cons (y 0) (fun j => h⁻¹ * φ (h * y j)) : Fin (n + 2) → P) i) =
        Fin.cons (h * y 0) (fun j => φ (h * y j)) := by
      rw [mul_cons]
      simp
    have htail : (fun w : Fin (n + 1) → P => F (fun i => h * (Fin.cons (y 0) w : Fin (n + 2) → P) i)) =
        (fun w => F (Fin.cons (h * y 0) (fun i => h * w i))) := by
      funext w
      rw [mul_cons]
    rw [prism_succ, prism_succ, hhead, htail]
    exact congrArg (F (Fin.cons (h * y 0) (fun i => φ (h * y i))) - ·)
      (ih (fun w => F (Fin.cons (h * y 0) w)) (Fin.tail y))

theorem prism_inv {P : Type} [Group P] (φ : P → P) (S : Set P) (hφ : ∀ g ∈ S, ∀ z, φ (g * z) = g * φ z)
    {n : ℕ} (F : (Fin (n + 1) → P) → ℝ) (hF : InvS S F) : InvS S (prism φ F) := by
  intro g hg y
  rw [prism_mul]
  have e1 : (fun z => g⁻¹ * φ (g * z)) = φ := by funext z; rw [hφ g hg, inv_mul_cancel_left]
  have e2 : (fun z : Fin (n + 1) → P => F (fun i => g * z i)) = F := by funext z; exact hF g hg z
  rw [e1, e2]

theorem prism_eq_zero_of_set (φ : Y → Y) (S : Set Y) (hφ : ∀ z ∈ S, φ z ∈ S) : ∀ {n : ℕ}
    (F : (Fin (n + 1) → Y) → ℝ) (y : Fin n → Y), (∀ z : Fin (n + 1) → Y, (∀ i, z i ∈ S) → F z = 0) →
      (∀ i, y i ∈ S) → prism φ F y = 0 := by
  intro n
  induction n with
  | zero => intros; rfl
  | succ n ih =>
    intro F y hF hy
    rw [prism_succ]
    have h1 : F (Fin.cons (y 0) (fun i => φ (y i))) = 0 := by
      apply hF; intro i; refine Fin.cases ?_ (fun k => ?_) i
      · simpa using hy 0
      · simpa using hφ _ (hy k)
    rw [h1, zero_sub, neg_eq_zero]
    apply ih
    · intro z hz
      apply hF
      intro i
      refine Fin.cases ?_ (fun k => ?_) i
      · simpa using hy 0
      · simpa using hz k
    · intro i
      exact hy i.succ

end PositivityTheory.KB.SplitAffineSpectral.PrismSpan

end
end

