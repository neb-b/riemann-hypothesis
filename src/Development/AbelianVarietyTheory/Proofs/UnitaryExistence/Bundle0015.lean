module

public import Mathlib
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsHolPeriods
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0002

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsHermCoordOfDatum
section
open NumberField Matrix
open scoped nonZeroDivisors TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor

namespace GlobalTheory.DatumCoord

variable {E : Type} [Field E] [NumberField E]

open NumberField Matrix in
open scoped nonZeroDivisors TensorProduct in
variable {E : Type} [Field E] [NumberField E] in
theorem _root_.GlobalTheory.DatumCoord.eq_of_trace_int {c d : E}
    (h : ∀ a : 𝓞 E, Algebra.trace ℚ E ((a : E) * c) = Algebra.trace ℚ E ((a : E) * d)) :
    c = d := by
  by_contra hcd
  have hne : c - d ≠ 0 := sub_ne_zero.2 hcd
  have halg : IsAlgebraic ℤ (c - d)⁻¹ :=
    IsFractionRing.isAlgebraic_iff ℤ ℚ _ |>.mpr (.of_finite ℚ _)
  obtain ⟨y, hy, hint⟩ := halg.exists_integral_multiple
  have key := h ⟨y • (c - d)⁻¹, hint⟩
  rw [← sub_eq_zero, ← map_sub, ← mul_sub] at key
  change Algebra.trace ℚ E (y • (c - d)⁻¹ * (c - d)) = 0 at key
  rw [zsmul_eq_mul, mul_assoc, inv_mul_cancel₀ hne, mul_one,
    show (y : E) = algebraMap ℚ E y by simp, Algebra.trace_algebraMap] at key
  simp [hy, Module.finrank_pos.ne'] at key

variable [IsCMField E]

end GlobalTheory.DatumCoord

namespace GlobalTheory

open DatumCoord

open NumberField Matrix in
open scoped nonZeroDivisors TensorProduct in
variable {E : Type} [Field E] [NumberField E] in
private lemma exists_trace_mul_eq_of_addMonoidHom (f : 𝓞 E →+ ℤ) :
    ∃ z : E, ∀ a : 𝓞 E, Algebra.trace ℚ E ((a : E) * z) = (f a : ℚ) := by
  let g : E →ₗ[ℚ] ℚ := (integralBasis E).constr ℚ (fun i => (f (RingOfIntegers.basis E i) : ℚ))
  have hnd := traceForm_nondegenerate ℚ E
  obtain ⟨z, hz⟩ := ((Algebra.traceForm ℚ E).toDual hnd).surjective g
  refine ⟨z, fun a => ?_⟩
  have h1 : ∀ b : E, Algebra.trace ℚ E (b * z) = g b := fun b => by
    rw [← hz]; simp [LinearMap.BilinForm.toDual_def, Algebra.traceForm_apply, mul_comm]
  let u : 𝓞 E →ₗ[ℤ] ℚ :=
    (g.restrictScalars ℤ).comp ((algebraMap (𝓞 E) E : 𝓞 E →+* E).toIntAlgHom.toLinearMap)
  let v : 𝓞 E →ₗ[ℤ] ℚ := (Int.castRingHom ℚ).toIntAlgHom.toLinearMap.comp f.toIntLinearMap
  have huv : u = v := (RingOfIntegers.basis E).ext fun i => by
    simp [u, v, g, ← integralBasis_apply]
  rw [h1]
  exact congrArg (fun w : 𝓞 E →ₗ[ℤ] ℚ => w a) huv


open NumberField Matrix in
open scoped nonZeroDivisors TensorProduct in
theorem _root_.GlobalTheory.exists_herm_coord_of_datum :
    ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (D : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Datum H) (ξ : E),
      _root_.ReciprocityTheory.ChartRestriction.G.FD.cc ξ = -ξ → ξ ≠ 0 → ∀ r : ℕ, r = D.p + D.q →
      ∃ (Gm : Matrix (Fin r) (Fin r) E) (φ : D.La →ₗ[𝓞 E] (Fin r → E)),
        (Function.Injective φ ∧ Submodule.span E (Set.range φ) = ⊤ ∧
          (∀ a b, _root_.ReciprocityTheory.ChartRestriction.G.FD.cc (Gm a b) = Gm b a) ∧ Gm.det ≠ 0 ∧
          ∀ x y, ((D.EF x y : ℤ) : ℚ) = Algebra.trace ℚ E (ξ * _root_.ReciprocityTheory.ChartRestriction.G.FD.herm Gm (φ x) (φ y))) := by
  intro E _ _ _ H D ξ hξ hξ0 r hr
  have hz : ∀ x y : D.La, ∃ z : E, ∀ a : 𝓞 E,
      Algebra.trace ℚ E ((a : E) * z) = (D.EF (a • x) y : ℚ) := fun x y =>
    exists_trace_mul_eq_of_addMonoidHom (AddMonoidHom.mk' (fun a => D.EF (a • x) y) fun a b => by simp [add_smul])
  choose h0 hh0 using hz
  have huniq := fun c d h => _root_.GlobalTheory.DatumCoord.eq_of_trace_int (E := E) (c := c) (d := d) h
  have hsmul : ∀ (b : 𝓞 E) x y, h0 (b • x) y = b * h0 x y := fun b x y => huniq _ _ fun a => by
    rw [hh0, ← mul_assoc, ← map_mul, hh0, smul_smul]
  have hadd : ∀ x x' y, h0 (x + x') y = h0 x y + h0 x' y := fun x x' y => huniq _ _ fun a => by
    rw [hh0, mul_add, map_add (f := _), hh0, hh0]; simp [smul_add]
  have hadd' : ∀ x y y', h0 x (y + y') = h0 x y + h0 x y' := fun x y y' => huniq _ _ fun a => by
    rw [mul_add, map_add (f := _), hh0, hh0, hh0, map_add (f := _), Int.cast_add]
  let σ : E ≃ₐ[ℚ] E := (IsCMField.complexConj E).restrictScalars ℚ
  have hσ : ∀ e, σ e = _root_.ReciprocityTheory.ChartRestriction.G.FD.cc e := fun e => rfl
  have hσσ : ∀ e, σ (σ e) = e := fun e => by simp [σ]
  have hbar : ∀ b, ((H.bar b : 𝓞 E) : E) = σ b := fun b => H.bar_eq b
  have hbb : ∀ b, H.bar (H.bar b) = b := fun b => RingOfIntegers.ext (by rw [hbar, hbar, hσσ])
  have htr : ∀ e, Algebra.trace ℚ E (σ e) = Algebra.trace ℚ E e := fun e =>
    Algebra.trace_eq_of_algEquiv σ e
  have hanti : ∀ u v, D.EF u v = - D.EF v u := fun u v => by
    have h := D.alt (u + v)
    simp only [map_add (f := _), LinearMap.add_apply, D.alt u, D.alt v] at h
    omega
  have hsmul' : ∀ (b : 𝓞 E) x y, h0 x (b • y) = σ b * h0 x y := fun b x y => huniq _ _ fun a => by
    rw [hh0, ← hbb b, ← D.adj, smul_smul, ← hh0, hbb]
    congr 1
    push_cast [hbar]
    ring
  have hherm : ∀ x y, h0 y x = - σ (h0 x y) := fun x y => huniq _ _ fun a => by
    rw [hh0, hanti, ← hbb a, ← D.adj, Int.cast_neg, ← hh0, hbb, hbar, ← htr (σ a * h0 x y),
      map_mul, hσσ, mul_neg, map_neg]
  haveI := D.fin
  have hrk : Module.finrank (𝓞 E) D.La = r := hr ▸ D.rank
  obtain ⟨l, hl⟩ := exists_linearIndependent_of_le_finrank (R := 𝓞 E) (M := D.La) hrk.ge
  have hmax : ∀ x : D.La, ∃ t : 𝓞 E, t ≠ 0 ∧ ∃ c : Fin r → 𝓞 E, ∑ i, c i • l i = t • x := by
    intro x
    have hnot : ¬ LinearIndependent (𝓞 E) (Fin.snoc l x : Fin (r + 1) → D.La) := fun h => by
      have := h.fintype_card_le_finrank
      simp [hrk] at this
    obtain ⟨g, hg, i, hi⟩ := Fintype.not_linearIndependent_iff.1 hnot
    rw [Fin.sum_univ_castSucc] at hg
    simp only [Fin.snoc_castSucc, Fin.snoc_last] at hg
    refine ⟨g (Fin.last r), fun hg0 => hi ?_, fun j => -g j.castSucc, ?_⟩
    · rw [hg0, zero_smul, add_zero] at hg
      have := Fintype.linearIndependent_iff.1 hl _ hg
      rcases Fin.eq_castSucc_or_eq_last i with ⟨j, rfl⟩ | rfl
      · exact this j
      · exact hg0
    · simp only [neg_smul, Finset.sum_neg_distrib]
      exact neg_eq_of_add_eq_zero_right hg
  have hz0 : ∀ y, h0 0 y = 0 := fun y => by simpa using hadd 0 0 y
  have hz0' : ∀ x, h0 x 0 = 0 := fun x => by simpa using hadd' x 0 0
  have hsumL : ∀ (c : Fin r → 𝓞 E) y, h0 (∑ i, c i • l i) y = ∑ i, (c i : E) * h0 (l i) y := by
    intro c y
    induction (Finset.univ : Finset (Fin r)) using Finset.induction_on with
    | empty => simp [hz0]
    | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, hadd, hsmul, ih]
  have hsumR : ∀ (d : Fin r → 𝓞 E) x, h0 x (∑ j, d j • l j) = ∑ j, σ (d j) * h0 x (l j) := by
    intro d x
    induction (Finset.univ : Finset (Fin r)) using Finset.induction_on with
    | empty => simp [hz0']
    | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, hadd', hsmul', ih]
  have hσ0 : ∀ s : 𝓞 E, s ≠ 0 → σ s ≠ 0 := fun s hs => by simpa using hs
  have hnd : ∀ x, (∀ y, h0 x y = 0) → x = 0 := fun x hx => D.unimod.1 (LinearMap.ext fun y => by
    have := hh0 x y 1
    rw [hx, mul_zero, map_zero, one_smul] at this
    simp only [map_zero, LinearMap.zero_apply]
    exact_mod_cast this.symm)
  let ψ : D.La →ₗ[𝓞 E] (Fin r → E) :=
    { toFun := fun x j => h0 x (l j)
      map_add' := fun x y => funext fun j => hadd _ _ _
      map_smul' := fun b x => funext fun j => by simp [hsmul, Algebra.smul_def] }
  have hψ : ∀ x j, ψ x j = h0 x (l j) := fun x j => rfl
  have hinj : Function.Injective ψ := (injective_iff_map_eq_zero ψ).2 fun x hx => hnd x fun y => by
    obtain ⟨s, hs, d, hd⟩ := hmax y
    have h1 : σ s * h0 x y = 0 := by
      rw [← hsmul', ← hd, hsumR]
      exact Finset.sum_eq_zero fun j _ => by rw [← hψ, hx]; simp
    exact (mul_eq_zero.1 h1).resolve_left (hσ0 s hs)
  let gram : Matrix (Fin r) (Fin r) E := Matrix.of fun i j => h0 (l i) (l j)
  have hgramσ : ∀ i j, σ (gram i j) = - gram j i := fun i j => by
    simp [gram, hherm (l i) (l j), hσσ]
  have hdet : gram.det ≠ 0 := by
    intro h
    obtain ⟨v, hv0, hv⟩ := Matrix.exists_vecMul_eq_zero_iff.2 h
    obtain ⟨⟨m, hm⟩, hmv⟩ := IsLocalization.exist_integer_multiples (𝓞 E)⁰ Finset.univ v
    choose c hc using fun i => hmv i (Finset.mem_univ i)
    have hx : ∑ i, c i • l i = 0 := hinj <| funext fun j => by
      rw [map_zero, Pi.zero_apply, hψ, hsumL]
      have := congrFun hv j
      simp only [Matrix.vecMul, dotProduct, Pi.zero_apply, gram, Matrix.of_apply] at this
      simp only [hc, Submonoid.smul_def, Algebra.smul_def, mul_assoc, ← Finset.mul_sum, this,
        mul_zero]
    have hc0 := Fintype.linearIndependent_iff.1 hl c hx
    apply hv0
    funext i
    have := hc i
    rw [hc0 i, map_zero, Algebra.smul_def] at this
    exact (mul_eq_zero.1 this.symm).resolve_left (by simpa using nonZeroDivisors.ne_zero hm)
  refine ⟨-ξ⁻¹ • gram⁻¹, ψ, hinj, ?_, ?_, ?_, ?_⟩
  · rw [eq_top_iff]
    intro w _
    have hw : w = ∑ i, (w ᵥ* gram⁻¹) i • ψ (l i) := by
      have hsum : ∑ i, (w ᵥ* gram⁻¹) i • ψ (l i) = (w ᵥ* gram⁻¹) ᵥ* gram := by
        funext j
        simp [Matrix.vecMul, dotProduct, Finset.sum_apply, hψ, gram]
      rw [hsum, Matrix.vecMul_vecMul, Matrix.nonsing_inv_mul _ (isUnit_iff_ne_zero.2 hdet),
        Matrix.vecMul_one]
    rw [hw]
    exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨l i, rfl⟩)
  · have hu : IsUnit gram.det := isUnit_iff_ne_zero.2 hdet
    have h1 : gram.map σ = -gramᵀ := by
      ext i j
      simp [hgramσ]
    have e1 : (gram⁻¹).map σ * gram.map σ = 1 := by
      have h3 : (gram⁻¹ * gram).map (σ : E →+* E) = (gram⁻¹).map σ * gram.map σ := Matrix.map_mul
      rw [← h3, Matrix.nonsing_inv_mul _ hu]
      exact Matrix.map_one _ (map_zero _) (map_one _)
    have e2 : -(gram⁻¹)ᵀ * gram.map σ = 1 := by
      rw [h1, neg_mul_neg, ← Matrix.transpose_mul, Matrix.mul_nonsing_inv _ hu, Matrix.transpose_one]
    have hinvσ : (gram⁻¹).map σ = -(gram⁻¹)ᵀ :=
      (Matrix.inv_eq_left_inv e1).symm.trans (Matrix.inv_eq_left_inv e2)
    intro a b
    have h2 := congrFun (congrFun hinvσ a) b
    have hξσ : σ ξ = -ξ := hξ
    simp only [Matrix.map_apply, Matrix.neg_apply, Matrix.transpose_apply] at h2
    rw [← hσ]
    simp [Matrix.smul_apply, map_inv₀, hξσ, h2]
  · rw [Matrix.det_smul]
    exact mul_ne_zero (pow_ne_zero _ (neg_ne_zero.2 (inv_ne_zero hξ0)))
      (Matrix.isUnit_nonsing_inv_det _ (isUnit_iff_ne_zero.2 hdet)).ne_zero
  · have hu : IsUnit gram.det := isUnit_iff_ne_zero.2 hdet
    intro x y
    obtain ⟨t, ht, c, hc⟩ := hmax x
    obtain ⟨s, hs, d, hd⟩ := hmax y
    have ht' : (t : E) ≠ 0 := by simpa using ht
    let cv : Fin r → E := fun i => c i
    let dv : Fin r → E := fun j => σ (d j)
    have hA : (fun j => (t : E) * ψ x j) = cv ᵥ* gram := funext fun j => by
      rw [hψ, ← hsmul, ← hc, hsumL]
      simp [Matrix.vecMul, dotProduct, cv, gram]
    have hB : (fun b => -(σ (s : E) * σ (ψ y b))) = gram *ᵥ dv := funext fun b => by
      rw [hψ, hherm (l b) y, map_neg, hσσ, mul_neg, neg_neg, ← hsmul', ← hd, hsumR]
      simp [Matrix.mulVec, dotProduct, dv, gram, mul_comm]
    have hC : (t : E) * σ s * h0 x y = cv ⬝ᵥ (gram *ᵥ dv) := by
      rw [mul_assoc, ← hsmul', ← hsmul, ← hc, ← hd, hsumL]
      simp only [hsumR, Matrix.mulVec, dotProduct, Finset.mul_sum, cv, dv, gram, Matrix.of_apply]
      exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring
    have key : ξ * _root_.ReciprocityTheory.ChartRestriction.G.FD.herm (-ξ⁻¹ • gram⁻¹) (ψ x) (ψ y) = h0 x y := by
      apply mul_left_cancel₀ (mul_ne_zero ht' (hσ0 s hs))
      rw [hC, ← vecMul_one cv, ← Matrix.mul_nonsing_inv _ hu, ← vecMul_vecMul, ← dotProduct_mulVec,
        ← hA, ← hB]
      unfold _root_.ReciprocityTheory.ChartRestriction.G.FD.herm
      simp only [← hσ, dotProduct, Matrix.mulVec, Finset.mul_sum, Matrix.smul_apply, smul_eq_mul]
      refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
      field_simp
    have h1 := hh0 x y 1
    rw [one_smul] at h1
    rw [key, ← h1]
    simp

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsSmulMemOfMemSpanFraction
section
open NumberField Matrix
open scoped nonZeroDivisors
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor

namespace GlobalTheory

section PseudoBasis

variable {R K : Type} [CommRing R] [IsDedekindDomain R] [Field K] [Algebra R K]
  [IsFractionRing R K]

theorem exists_smul_mem_of_mem_span_fraction {V : Type} [AddCommGroup V] [Module K V] [Module R V]
    [IsScalarTower R K V] (Λ : Submodule R V) (v : V) (hv : v ∈ Submodule.span K (Λ : Set V)) :
    ∃ d : R, d ≠ 0 ∧ d • v ∈ Λ := by
  first
  | (rename_i h_2 h_3 h_4 h_5 h_6 h_8 h_9 h_10 h_11; revert R K h_2 h_3 h_4 h_5 h_6 V h_8 h_9 h_10 h_11 Λ v hv; exact @_root_.GlobalTheory.LatticeBoundedAction.main)
  | exact @_root_.GlobalTheory.LatticeBoundedAction.main
  | exact _root_.GlobalTheory.LatticeBoundedAction.main
  | (apply _root_.GlobalTheory.LatticeBoundedAction.main <;> assumption)
  | (intros; apply _root_.GlobalTheory.LatticeBoundedAction.main <;> assumption)
  | (intros; apply @_root_.GlobalTheory.LatticeBoundedAction.main <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.LatticeBoundedAction.main ..)

theorem exists_splitting_vector {V : Type} [AddCommGroup V] [Module K V] [Module R V]
    [IsScalarTower R K V] (Λ : Submodule R V) (hfg : Λ.FG)
    (hsp : Submodule.span K (Λ : Set V) = ⊤) (l : V →ₗ[K] K) (hl : l ≠ 0) :
    ∃ (c : FractionalIdeal R⁰ K) (e : V), c ≠ 0 ∧ l e = 1 ∧ (∀ v ∈ Λ, l v ∈ c) ∧
      ∀ x ∈ c, x • e ∈ Λ := by
  have hfg' : (Λ.map (l.restrictScalars R)).FG := hfg.map _
  let c : FractionalIdeal R⁰ K := ⟨Λ.map (l.restrictScalars R), FractionalIdeal.isFractional_of_fg hfg'⟩
  have hc : ∀ x, x ∈ c ↔ ∃ v ∈ Λ, l v = x := fun x => Iff.rfl
  have hc0 : c ≠ 0 := by
    intro h
    apply hl
    refine LinearMap.ext_on hsp ?_
    intro v hv
    have : l v ∈ c := (hc _).2 ⟨v, hv, rfl⟩
    rw [h] at this
    simpa using this
  have h1 : (1 : K) ∈ c * c⁻¹ := by
    rw [mul_inv_cancel₀ hc0]
    exact FractionalIdeal.one_mem_one _
  have key : ∀ y ∈ c * c⁻¹, ∃ e : V, l e = y ∧ ∀ x ∈ c, x • e ∈ Λ := by
    intro y hy
    refine FractionalIdeal.mul_induction_on hy ?_ ?_
    · intro a ha b hb
      obtain ⟨v, hv, rfl⟩ := (hc _).1 ha
      refine ⟨b • v, by simp [mul_comm], ?_⟩
      intro x hx
      have : x * b ∈ c * c⁻¹ := FractionalIdeal.mul_mem_mul hx hb
      rw [mul_inv_cancel₀ hc0, FractionalIdeal.mem_one_iff] at this
      obtain ⟨t, ht⟩ := this
      rw [smul_smul, ← ht, algebraMap_smul]
      exact Λ.smul_mem _ hv
    · rintro a b ⟨e, he, he'⟩ ⟨f, hf, hf'⟩
      refine ⟨e + f, by simp [he, hf], ?_⟩
      intro x hx
      rw [smul_add]
      exact Λ.add_mem (he' x hx) (hf' x hx)
  obtain ⟨e, he, he'⟩ := key 1 h1
  exact ⟨c, e, hc0, he, fun v hv => (hc _).2 ⟨v, hv, rfl⟩, he'⟩

theorem exists_pseudoCoords (n : ℕ) :
    ∀ (V : Type) [AddCommGroup V] [Module K V] [Module R V] [IsScalarTower R K V]
      [FiniteDimensional K V], Module.finrank K V = n →
      ∀ (Λ : Submodule R V) (I : Submodule K V), Λ.FG → Submodule.span K (Λ : Set V) = ⊤ →
      ∃ (s : ℕ) (f : Fin n → (V →ₗ[K] K)) (c : Fin n → FractionalIdeal R⁰ K),
        (∀ v, (∀ a, f a v = 0) → v = 0) ∧ (∀ a, c a ≠ 0) ∧ (∀ v, v ∈ Λ ↔ ∀ a, f a v ∈ c a) ∧
        ∀ v, v ∈ I ↔ ∀ a : Fin n, s ≤ (a : ℕ) → f a v = 0 := by
  induction n with
  | zero =>
    intro V _ _ _ _ _ hV Λ I _ _
    have : Subsingleton V := Module.finrank_zero_iff.1 hV
    refine ⟨0, Fin.elim0, Fin.elim0, fun v _ => Subsingleton.elim _ _, fun a => a.elim0, ?_, ?_⟩
    · intro v
      rw [Subsingleton.elim v 0]
      exact ⟨fun _ a => a.elim0, fun _ => Λ.zero_mem⟩
    · intro v
      rw [Subsingleton.elim v 0]
      exact ⟨fun _ a => a.elim0, fun _ => I.zero_mem⟩
  | succ n ih =>
    intro V _ _ _ _ _ hV Λ I hfg hsp
    have : Nontrivial V := Module.nontrivial_of_finrank_eq_succ hV
    obtain ⟨l, hl, hI⟩ : ∃ l : V →ₗ[K] K, l ≠ 0 ∧ (I = ⊤ ∨ I ≤ LinearMap.ker l) := by
      by_cases h : I = ⊤
      · obtain ⟨l, hl, -⟩ := Submodule.exists_le_ker_of_lt_top (⊥ : Submodule K V) bot_lt_top
        exact ⟨l, hl, Or.inl h⟩
      · obtain ⟨l, hl, h2⟩ := Submodule.exists_le_ker_of_lt_top I (lt_top_iff_ne_top.2 h)
        exact ⟨l, hl, Or.inr h2⟩
    obtain ⟨c0, e, hc0, he, hΛc, hce⟩ := exists_splitting_vector Λ hfg hsp l hl
    set W := LinearMap.ker l with hW
    have hWn : Module.finrank K W = n := by
      have h1 := LinearMap.finrank_range_add_finrank_ker l
      have h2 : LinearMap.range l = ⊤ := by
        rw [eq_top_iff]
        intro x _
        exact ⟨x • e, by simp [he]⟩
      rw [h2, finrank_top, Module.finrank_self, hV] at h1
      rw [hW]; omega
    let ι : W →ₗ[R] V := W.subtype.restrictScalars R
    have hι : Function.Injective ι := Subtype.val_injective
    let Λ' : Submodule R W := Λ.comap ι
    have hΛ' : ∀ w : W, w ∈ Λ' ↔ (w : V) ∈ Λ := fun w => Iff.rfl
    have hfg' : Λ'.FG := by
      apply Submodule.fg_of_fg_map_injective ι hι
      exact Submodule.FG.of_le hfg (Submodule.map_comap_le _ _)
    have hsp' : Submodule.span K (Λ' : Set W) = ⊤ := by
      rw [eq_top_iff]
      intro w _
      obtain ⟨d, hd, hdw⟩ := exists_smul_mem_of_mem_span_fraction (K := K) Λ (w : V)
        (by rw [hsp]; trivial)
      have hd1 : algebraMap R K d ≠ 0 := by simpa using hd
      have hm : algebraMap R K d • w ∈ Λ' := by
        rw [hΛ']
        simpa using hdw
      have : w = (algebraMap R K d)⁻¹ • (algebraMap R K d • w) := by
        rw [smul_smul, inv_mul_cancel₀ hd1, one_smul]
      rw [this]
      exact Submodule.smul_mem _ _ (Submodule.subset_span hm)
    obtain ⟨s, f, c, hf, hc, hfΛ, hfI⟩ := ih W hWn Λ' (I.comap W.subtype) hfg' hsp'
    let p : V →ₗ[K] W := LinearMap.codRestrict W (LinearMap.id - l.smulRight e) (by
      intro v
      simp [hW, he])
    have hp : ∀ v, (p v : V) = v - l v • e := fun v => rfl
    let F : Fin (n + 1) → (V →ₗ[K] K) := Fin.snoc (fun a => f a ∘ₗ p) l
    let C : Fin (n + 1) → FractionalIdeal R⁰ K := Fin.snoc c c0
    have hF1 : ∀ a v, F (Fin.castSucc a) v = f a (p v) := by
      intro a v; simp [F]
    have hF2 : ∀ v, F (Fin.last n) v = l v := by
      intro v; simp [F]
    have hC1 : ∀ a, C (Fin.castSucc a) = c a := by
      intro a; simp [C]
    have hC2 : C (Fin.last n) = c0 := by
      simp [C]
    have A1 : ∀ v, (∀ a, F a v = 0) → v = 0 := by
      intro v hv
      have h1 : l v = 0 := by rw [← hF2]; exact hv _
      have h2 : p v = 0 := hf _ fun a => by rw [← hF1]; exact hv _
      have h3 := hp v
      rw [h2, h1] at h3
      simpa using h3.symm
    have A2 : ∀ a, C a ≠ 0 := by
      intro a
      refine Fin.lastCases ?_ (fun a => ?_) a
      · rwa [hC2]
      · rw [hC1]; exact hc a
    have A3 : ∀ v, v ∈ Λ ↔ ∀ a, F a v ∈ C a := by
      intro v
      rw [Fin.forall_fin_succ']
      simp only [hF1, hF2, hC1, hC2]
      rw [← hfΛ, hΛ', hp]
      constructor
      · intro hv
        exact ⟨Λ.sub_mem hv (hce _ (hΛc v hv)), hΛc v hv⟩
      · rintro ⟨h1, h2⟩
        have := Λ.add_mem h1 (hce _ h2)
        simpa using this
    rcases hI with hI | hI
    · refine ⟨n + 1, F, C, A1, A2, A3, ?_⟩
      intro v
      refine ⟨fun _ a ha => absurd a.2 (not_lt.2 ha), fun _ => ?_⟩
      rw [hI]; trivial
    · refine ⟨min s n, F, C, A1, A2, A3, ?_⟩
      intro v
      rw [Fin.forall_fin_succ']
      simp only [hF1, hF2]
      have hh : (∀ a : Fin n, min s n ≤ ((Fin.castSucc a : Fin (n + 1)) : ℕ) → f a (p v) = 0) ↔
          (p v : V) ∈ I := by
        rw [show ((p v : V) ∈ I) ↔ p v ∈ I.comap W.subtype from Iff.rfl, hfI]
        refine forall_congr' fun a => imp_congr_left ?_
        have := a.2
        simp only [Fin.val_castSucc]
        omega
      rw [hh, hp]
      constructor
      · intro hv
        have h0 : l v = 0 := hI hv
        refine ⟨by simpa [h0] using hv, fun _ => h0⟩
      · rintro ⟨h1, h2⟩
        have h0 : l v = 0 := h2 (by simp)
        simpa [h0] using h1

end PseudoBasis

theorem exists_pseudoBasis_adapted :
    ∀ (E : Type) [Field E] [NumberField E] (r : ℕ) (Λ : Submodule (𝓞 E) (Fin r → E)) (I : Submodule E (Fin r → E)), Λ.FG → Submodule.span E (Λ : Set (Fin r → E)) = ⊤ → ∃ (s : ℕ) (e : Module.Basis (Fin r) E (Fin r → E)) (c : Fin r → FractionalIdeal (𝓞 E)⁰ E), (∀ a, c a ≠ 0) ∧ (∀ v, v ∈ Λ ↔ ∀ a, e.repr v a ∈ c a) ∧ ∀ v, v ∈ I ↔ ∀ a : Fin r, s ≤ (a : ℕ) → e.repr v a = 0 := by
  intro E _ _ r Λ I hfg hsp
  obtain ⟨s, f, c, hf, hc, hΛ, hI⟩ :=
    exists_pseudoCoords (R := 𝓞 E) (K := E) r (Fin r → E) (by simp) Λ I hfg hsp
  have hinj : Function.Injective (LinearMap.pi f) := by
    set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
    intro v hv
    exact hf v fun a => congrFun hv a
  let φ : (Fin r → E) ≃ₗ[E] (Fin r → E) := LinearEquiv.ofInjectiveEndo _ hinj
  have hφ : ∀ v a, (Module.Basis.ofEquivFun φ).repr v a = f a v := by
    intro v a
    rw [Module.Basis.ofEquivFun_repr_apply]
    rfl
  refine ⟨s, Module.Basis.ofEquivFun φ, c, hc, ?_, ?_⟩
  · simpa only [hφ] using hΛ
  · simpa only [hφ] using hI

end GlobalTheory
end

