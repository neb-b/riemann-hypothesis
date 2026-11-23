module

public import Mathlib

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.ExistsLineOfAddAddEqZero
section
namespace GlobalTheory

open WeierstrassCurve WeierstrassCurve.Affine

theorem map_add_of_triples {A B : Type*} [AddCommGroup A] [AddCommGroup B] (f : A → B)
    (h0 : f 0 = 0) (hneg : ∀ P, f (-P) = -f P)
    (h3 : ∀ P Q R, P ≠ 0 → Q ≠ 0 → R ≠ 0 → P + Q + R = 0 → f P + f Q + f R = 0) (P Q : A) :
    f (P + Q) = f P + f Q := by
  by_cases hP : P = 0
  · simp [hP, h0]
  by_cases hQ : Q = 0
  · simp [hQ, h0]
  by_cases hR : P + Q = 0
  · have : P = -Q := eq_neg_of_add_eq_zero_left hR
    rw [hR, h0, this, hneg, neg_add_cancel]
  have := h3 P Q (-(P + Q)) hP hQ (neg_ne_zero.mpr hR) (add_neg_cancel _)
  rw [hneg] at this
  exact (add_neg_eq_zero.mp this).symm

variable {k : Type*} [Field k] [DecidableEq k] {W : Affine k}

theorem add_add_eq_zero_of_line {x₁ y₁ x₂ y₂ x₃ y₃ : k} (h₁ : W.Nonsingular x₁ y₁)
    (h₂ : W.Nonsingular x₂ y₂) (h₃ : W.Nonsingular x₃ y₃) (l n : k)
    (e₁ : y₁ = l * x₁ + n) (e₂ : y₂ = l * x₂ + n) (e₃ : y₃ = l * x₃ + n)
    (s₁ : x₁ + x₂ + x₃ = l ^ 2 + W.a₁ * l - W.a₂)
    (s₂ : x₁ * x₂ + x₁ * x₃ + x₂ * x₃ = W.a₄ - 2 * l * n - W.a₁ * n - W.a₃ * l) :
    Point.some x₁ y₁ h₁ + Point.some x₂ y₂ h₂ + Point.some x₃ y₃ h₃ = 0 := by
  have key : ¬(x₁ = x₂ ∧ y₁ = W.negY x₂ y₂) ∧ W.slope x₁ x₂ y₁ y₂ = l := by
    by_cases hx : x₁ = x₂
    · subst hx
      have hy : y₁ = y₂ := e₁.trans e₂.symm
      subst hy
      have ht : 3 * x₁ ^ 2 + 2 * W.a₂ * x₁ + W.a₄ - W.a₁ * y₁ = l * (y₁ - W.negY x₁ y₁) := by
        rw [negY]
        linear_combination (2 * x₁) * s₁ - s₂ - (W.a₁ + 2 * l) * e₁
      have hne : y₁ ≠ W.negY x₁ y₁ := by
        intro h
        rw [nonsingular_iff] at h₁
        rcases h₁.2 with h' | h'
        · apply h'
          rw [← h, sub_self, mul_zero] at ht
          linear_combination -ht
        · exact h' h
      refine ⟨fun h => hne h.2, ?_⟩
      rw [slope_of_Y_ne rfl hne, ht, mul_div_assoc, div_self (sub_ne_zero.mpr hne), mul_one]
    · refine ⟨fun h => hx h.1, ?_⟩
      rw [slope_of_X_ne hx, div_eq_iff (sub_ne_zero.mpr hx)]
      linear_combination e₁ - e₂
  rw [Point.add_some key.1]
  apply Point.add_of_Y_eq
  · rw [key.2, addX]
    linear_combination -s₁
  · have hx : W.addX x₁ x₂ l = x₃ := by
      rw [addX]
      linear_combination -s₁
    rw [key.2, addY, negAddY, hx]
    congr 1
    linear_combination e₁ - e₃

theorem exists_line_of_add_add_eq_zero {x₁ y₁ x₂ y₂ x₃ y₃ : k} {h₁ : W.Nonsingular x₁ y₁}
    {h₂ : W.Nonsingular x₂ y₂} {h₃ : W.Nonsingular x₃ y₃}
    (h : Point.some x₁ y₁ h₁ + Point.some x₂ y₂ h₂ + Point.some x₃ y₃ h₃ = 0) :
    ∃ l n : k, y₁ = l * x₁ + n ∧ y₂ = l * x₂ + n ∧ y₃ = l * x₃ + n ∧
      x₁ + x₂ + x₃ = l ^ 2 + W.a₁ * l - W.a₂ ∧
      x₁ * x₂ + x₁ * x₃ + x₂ * x₃ = W.a₄ - 2 * l * n - W.a₁ * n - W.a₃ * l ∧
      x₁ * x₂ * x₃ = n ^ 2 + W.a₃ * n - W.a₆ := by
  have hxy : ¬(x₁ = x₂ ∧ y₁ = W.negY x₂ y₂) := by
    rintro ⟨hx, hy⟩
    rw [Point.add_of_Y_eq hx hy, zero_add] at h
    exact Point.some_ne_zero _ h
  rw [Point.add_some hxy, add_eq_zero_iff_eq_neg, Point.neg_some, Point.some.injEq] at h
  obtain ⟨hx, hy⟩ := h
  have hp := addPolynomial_slope h₁.1 h₂.1 hxy
  rw [addPolynomial_eq, neg_inj, Cubic.prod_X_sub_C_eq, Cubic.toPoly_injective, hx] at hp
  have hl : W.slope x₁ x₂ y₁ y₂ * (x₁ - x₂) = y₁ - y₂ := by
    by_cases hx' : x₁ = x₂
    · have := Y_eq_of_Y_ne h₁.1 h₂.1 hx' (fun h => hxy ⟨hx', h⟩)
      rw [hx', this, sub_self, sub_self, mul_zero]
    · rw [slope_of_X_ne hx', div_mul_cancel₀ _ (sub_ne_zero.mpr hx')]
  rw [addY, negAddY, hx, negY, negY] at hy
  set l := W.slope x₁ x₂ y₁ y₂
  simp only [Cubic.mk.injEq, true_and] at hp
  obtain ⟨p₁, p₂, p₃⟩ := hp
  refine ⟨l, y₁ - l * x₁, by ring, by linear_combination hl, by linear_combination hy,
    by linear_combination p₁, by linear_combination -p₂, by linear_combination p₃⟩

section VariableChange


omit [DecidableEq k] in
theorem nonsingular_variableChange_iff (W : WeierstrassCurve k) (C : VariableChange k) (x y : k) :
    W.toAffine.Nonsingular ((C.u : k) ^ 2 * x + C.r)
      ((C.u : k) ^ 3 * y + (C.u : k) ^ 2 * C.s * x + C.t) ↔ (C • W).toAffine.Nonsingular x y := by
  have hu : (C.u : k) ≠ 0 := C.u.ne_zero
  simp only [nonsingular_iff', equation_iff', variableChange_a₁, variableChange_a₂,
    variableChange_a₃, variableChange_a₄, variableChange_a₆, Units.val_inv_eq_inv_val]
  obtain ⟨u, r, s, t⟩ := C
  dsimp only at hu ⊢
  generalize (u : k) = v at hu ⊢
  obtain ⟨a₁, a₂, a₃, a₄, a₆⟩ := W
  dsimp only [toAffine]
  refine and_congr ⟨fun h => ?_, fun h => ?_⟩ ?_
  · field_simp
    linear_combination h
  · field_simp at h
    linear_combination h
  · rw [← not_iff_not]
    simp only [not_or, not_not]
    refine ⟨fun ⟨h, h'⟩ => ⟨?_, ?_⟩, fun ⟨h, h'⟩ => ?_⟩
    · field_simp
      linear_combination h + s * h'
    · field_simp
      linear_combination h'
    · field_simp at h h'
      exact ⟨by linear_combination h - s * h', by linear_combination h'⟩

def variableChangePointFun {W W' : WeierstrassCurve k} (C : VariableChange k) (h : C • W = W') :
    W'.toAffine.Point → W.toAffine.Point
  | .zero => 0
  | .some x y hP => .some ((C.u : k) ^ 2 * x + C.r)
      ((C.u : k) ^ 3 * y + (C.u : k) ^ 2 * C.s * x + C.t)
      ((nonsingular_variableChange_iff W C x y).mpr (h ▸ hP))

def variableChangePoint {W W' : WeierstrassCurve k} (C : VariableChange k) (h : C • W = W') :
    W'.toAffine.Point →+ W.toAffine.Point :=
  AddMonoidHom.mk' (variableChangePointFun C h) <| by
    subst h
    have hu : (C.u : k) ≠ 0 := C.u.ne_zero
    refine map_add_of_triples _ rfl ?_ ?_
    · rintro (_ | ⟨x, y, hP⟩)
      · rfl
      · simp only [Point.neg_some, variableChangePointFun, Point.some.injEq, true_and, negY,
          variableChange_a₁, variableChange_a₃, Units.val_inv_eq_inv_val]
        field_simp
        ring
    · rintro (_ | ⟨x₁, y₁, h₁⟩) (_ | ⟨x₂, y₂, h₂⟩) (_ | ⟨x₃, y₃, h₃⟩) hP hQ hR h
      any_goals first | exact absurd rfl hP | exact absurd rfl hQ | exact absurd rfl hR
      obtain ⟨l, n, e₁, e₂, e₃, s₁, s₂, -⟩ := exists_line_of_add_add_eq_zero h
      simp only [variableChange_a₁, variableChange_a₂,
        variableChange_a₃, variableChange_a₄, Units.val_inv_eq_inv_val] at s₁ s₂
      field_simp at s₁ s₂
      refine add_add_eq_zero_of_line _ _ _ ((C.u : k) * l + C.s)
        ((C.u : k) ^ 3 * n + C.t - C.r * ((C.u : k) * l + C.s)) ?_ ?_ ?_ ?_ ?_
      · rw [e₁]; ring
      · rw [e₂]; ring
      · rw [e₃]; ring
      · linear_combination s₁
      · linear_combination s₂ + 2 * C.r * s₁

@[simp]
theorem variableChangePoint_some {W W' : WeierstrassCurve k} (C : VariableChange k)
    (h : C • W = W') {x y : k} (hP : W'.toAffine.Nonsingular x y) :
    variableChangePoint C h (.some x y hP) = .some ((C.u : k) ^ 2 * x + C.r)
      ((C.u : k) ^ 3 * y + (C.u : k) ^ 2 * C.s * x + C.t)
      ((nonsingular_variableChange_iff W C x y).mpr (h ▸ hP)) :=
  rfl

theorem variableChangePoint_bijective {W W' : WeierstrassCurve k} (C : VariableChange k)
    (h : C • W = W') : Function.Bijective (variableChangePoint C h) := by
  have hu : (C.u : k) ≠ 0 := C.u.ne_zero
  constructor
  · rw [injective_iff_map_eq_zero]
    rintro (_ | ⟨x, y, hP⟩) h0
    · rfl
    · exact absurd h0 (Point.some_ne_zero _)
  · rintro (_ | ⟨x, y, hP⟩)
    · exact ⟨0, map_zero _⟩
    · have hx : x = (C.u : k) ^ 2 * ((x - C.r) / (C.u : k) ^ 2) + C.r := by field_simp; ring
      have hy : y = (C.u : k) ^ 3 * ((y - C.s * (x - C.r) - C.t) / (C.u : k) ^ 3)
          + (C.u : k) ^ 2 * C.s * ((x - C.r) / (C.u : k) ^ 2) + C.t := by field_simp; ring
      have hP' := hP
      rw [hx, hy, ← hx] at hP'
      nth_rw 1 [hx] at hP'
      rw [nonsingular_variableChange_iff, h] at hP'
      refine ⟨.some _ _ hP', ?_⟩
      rw [variableChangePoint_some, Point.some.injEq]
      exact ⟨hx.symm, hy.symm⟩

noncomputable def variableChangePointEquiv {W W' : WeierstrassCurve k} (C : VariableChange k)
    (h : C • W = W') : W'.toAffine.Point ≃+ W.toAffine.Point :=
  AddEquiv.ofBijective (variableChangePoint C h) (variableChangePoint_bijective C h)

end VariableChange

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.ExistsRingEquivOfIsTranscendenceBasis
section
open MvPolynomial Cardinal

namespace GlobalTheory.GaloisDescent


open MvPolynomial Cardinal in
theorem _root_.GlobalTheory.GaloisDescent.exists_ringEquiv_of_isTranscendenceBasis {F F' L L' ι κ : Type*} [Field F] [Field F']
    [Field L] [Field L'] [Algebra F L] [Algebra F' L'] [IsAlgClosed L] [IsAlgClosed L']
    {v : ι → L} {w : κ → L'} (hv : IsTranscendenceBasis F v) (hw : IsTranscendenceBasis F' w)
    (e : MvPolynomial ι F ≃+* MvPolynomial κ F') :
    ∃ σ : L ≃+* L', ∀ p, σ (aeval v p) = aeval w (e p) := by
  letI : Algebra (MvPolynomial ι F) L := (aeval v).toRingHom.toAlgebra
  letI : Algebra (MvPolynomial κ F') L' := (aeval w).toRingHom.toAlgebra
  have : Module.IsTorsionFree (MvPolynomial ι F) L :=
    Module.isTorsionFree_iff_algebraMap_injective.mpr hv.1
  have : Module.IsTorsionFree (MvPolynomial κ F') L' :=
    Module.isTorsionFree_iff_algebraMap_injective.mpr hw.1
  have : IsAlgClosure (MvPolynomial ι F) L := by
    refine ⟨inferInstance, ?_⟩
    have := hv.isAlgebraic
    refine Algebra.IsAlgebraic.ringHom_of_comp_eq hv.1.aevalEquiv.symm (RingHom.id L)
      hv.1.aevalEquiv.symm.injective Function.surjective_id ?_
    ext a
    change aeval v (hv.1.aevalEquiv.symm a) = algebraMap _ L a
    rw [← hv.1.algebraMap_aevalEquiv, AlgEquiv.apply_symm_apply]
  have : IsAlgClosure (MvPolynomial κ F') L' := by
    refine ⟨inferInstance, ?_⟩
    have := hw.isAlgebraic
    refine Algebra.IsAlgebraic.ringHom_of_comp_eq hw.1.aevalEquiv.symm (RingHom.id L')
      hw.1.aevalEquiv.symm.injective Function.surjective_id ?_
    ext a
    change aeval w (hw.1.aevalEquiv.symm a) = algebraMap _ L' a
    rw [← hw.1.algebraMap_aevalEquiv, AlgEquiv.apply_symm_apply]
  exact ⟨IsAlgClosure.equivOfEquiv L L' e, fun p => IsAlgClosure.equivOfEquiv_algebraMap L L' e p⟩

theorem exists_ringEquiv_extend {F L : Type*} [Field F] [Field L] [Algebra F L] [IsAlgClosed L]
    (τ : F ≃+* F) : ∃ σ : L ≃+* L, ∀ a, σ (algebraMap F L a) = algebraMap F L (τ a) := by
  obtain ⟨s, hs⟩ := exists_isTranscendenceBasis F L
  obtain ⟨σ, hσ⟩ := exists_ringEquiv_of_isTranscendenceBasis hs hs (mapEquiv s τ)
  refine ⟨σ, fun a => ?_⟩
  simpa using hσ (C a)

theorem exists_algEquiv_extend {K F L : Type*} [Field K] [Field F] [Field L] [Algebra K F]
    [Algebra F L] [Algebra K L] [IsScalarTower K F L] [IsAlgClosed L]
    (τ : F ≃ₐ[K] F) : ∃ σ : L ≃ₐ[K] L, ∀ a, σ (algebraMap F L a) = algebraMap F L (τ a) := by
  obtain ⟨σ, hσ⟩ := exists_ringEquiv_extend (L := L) τ.toRingEquiv
  refine ⟨AlgEquiv.ofRingEquiv (f := σ) fun k => ?_, hσ⟩
  rw [IsScalarTower.algebraMap_apply K F L, hσ]
  congr 1
  exact τ.commutes k

theorem exists_algEquiv_apply_eq_add_one {K L : Type*} [Field K] [Field L] [Algebra K L]
    [IsAlgClosed L] {x : L} (hx : Transcendental K x) : ∃ σ : L ≃ₐ[K] L, σ x = x + 1 := by
  have h1 : AlgebraicIndepOn K id ({x} : Set L) :=
    algebraicIndependent_unique_type_iff.2 hx
  obtain ⟨s, hxs, hs⟩ := exists_isTranscendenceBasis_superset h1
  let e : MvPolynomial s K ≃ₐ[K] MvPolynomial s K :=
    AlgEquiv.ofAlgHom (aeval fun i => X i + 1) (aeval fun i => X i - 1)
      (by ext i : 1; simp) (by ext i : 1; simp)
  obtain ⟨σ, hσ⟩ := exists_ringEquiv_of_isTranscendenceBasis hs hs e.toRingEquiv
  refine ⟨AlgEquiv.ofRingEquiv (f := σ) fun k => ?_, ?_⟩
  · simpa [e] using hσ (C k)
  · simpa [e] using hσ (X ⟨x, hxs rfl⟩)


open MvPolynomial Cardinal in
theorem _root_.GlobalTheory.GaloisDescent.mem_range_algebraMap_of_forall_algEquiv {K L : Type*} [Field K] [Field L] [Algebra K L]
    [PerfectField K] [IsAlgClosed L] (x : L) (hx : ∀ σ : L ≃ₐ[K] L, σ x = x) :
    x ∈ Set.range (algebraMap K L) := by
  by_cases halg : IsAlgebraic K x
  · have hxA : x ∈ algebraicClosure K L := mem_algebraicClosure_iff.2 halg
    have hfix : ∀ f : Gal(algebraicClosure K L/K), f ⟨x, hxA⟩ = ⟨x, hxA⟩ := by
      intro f
      obtain ⟨s, hs⟩ := exists_isTranscendenceBasis (algebraicClosure K L) L
      obtain ⟨τ, hτ⟩ := _root_.GlobalTheory.GaloisDescent.exists_ringEquiv_of_isTranscendenceBasis hs hs
        (MvPolynomial.mapEquiv s (f : algebraicClosure K L ≃+* algebraicClosure K L))
      have hτA : ∀ a : algebraicClosure K L, τ (a : L) = (f a : L) := fun a => by
        simpa using hτ (MvPolynomial.C a)
      let σ : L ≃ₐ[K] L := AlgEquiv.ofRingEquiv (f := τ) (fun k => by
        simpa using hτA (algebraMap K (algebraicClosure K L) k))
      apply Subtype.ext
      rw [← hτA]
      exact hx σ
    obtain ⟨k, hk⟩ := (InfiniteGalois.mem_range_algebraMap_iff_fixed _).2 hfix
    exact ⟨k, congrArg Subtype.val hk⟩
  · classical
    have hind : AlgebraicIndepOn K id {x} :=
      (algebraicIndependent_singleton_iff (⟨x, rfl⟩ : ({x} : Set L))).2 halg
    obtain ⟨t, hxt, ht⟩ := exists_isTranscendenceBasis_superset hind
    let i : t := ⟨x, hxt rfl⟩
    let φ : MvPolynomial t K ≃ₐ[K] MvPolynomial t K := AlgEquiv.ofAlgHom
      (aeval fun j => if j = i then X j + 1 else X j) (aeval fun j => if j = i then X j - 1 else X j)
      (MvPolynomial.algHom_ext fun j => by by_cases h : j = i <;> simp [h])
      (MvPolynomial.algHom_ext fun j => by by_cases h : j = i <;> simp [h])
    obtain ⟨τ, hτ⟩ := _root_.GlobalTheory.GaloisDescent.exists_ringEquiv_of_isTranscendenceBasis ht ht φ.toRingEquiv
    have hτx : τ x = x + 1 := by simpa [φ, i] using hτ (X i)
    let σ : L ≃ₐ[K] L := AlgEquiv.ofRingEquiv (f := τ) (fun k => by simpa [φ] using hτ (C k))
    have h1 := hx σ
    have h2 : τ x = x := h1
    rw [hτx] at h2
    simp at h2


open MvPolynomial Cardinal in
theorem _root_.GlobalTheory.GaloisDescent.complex_mem_range_of_forall_algEquiv {K : Type*} [Field K] [Algebra K ℂ] (x : ℂ)
    (hx : ∀ σ : ℂ ≃ₐ[K] ℂ, σ x = x) : x ∈ Set.range (algebraMap K ℂ) := by
  haveI : CharZero K := RingHom.charZero (algebraMap K ℂ)
  exact _root_.GlobalTheory.GaloisDescent.mem_range_algebraMap_of_forall_algEquiv x hx


open MvPolynomial Cardinal in
theorem _root_.GlobalTheory.GaloisDescent.exists_complex_ringEquiv_comp_eq {K : Type} [Field K] [Countable K] (f g : K →+* ℂ) :
    ∃ σ : ℂ ≃+* ℂ, ∀ a, σ (f a) = g a := by
  have hK : Cardinal.mk K ≤ Cardinal.aleph0 := Cardinal.mk_le_aleph0
  have hC : Cardinal.aleph0 < Cardinal.mk ℂ := by
    rw [Cardinal.mk_complex]; exact Cardinal.aleph0_lt_continuum
  letI Af : Algebra K ℂ := f.toAlgebra
  obtain ⟨s, hs⟩ := exists_isTranscendenceBasis K ℂ
  have hsc := IsAlgClosed.cardinal_eq_cardinal_transcendence_basis_of_aleph0_lt' _ hs hK hC
  letI Ag : Algebra K ℂ := g.toAlgebra
  obtain ⟨t, ht⟩ := exists_isTranscendenceBasis K ℂ
  have htc := IsAlgClosed.cardinal_eq_cardinal_transcendence_basis_of_aleph0_lt' _ ht hK hC
  obtain ⟨eqv⟩ := Cardinal.eq.1 (hsc.symm.trans htc)
  obtain ⟨σ, hσ⟩ := @_root_.GlobalTheory.GaloisDescent.exists_ringEquiv_of_isTranscendenceBasis K K ℂ ℂ s t _ _ _ _ Af Ag _ _ _ _
    hs ht (MvPolynomial.renameEquiv K eqv).toRingEquiv
  refine ⟨σ, fun a => ?_⟩
  simpa [RingHom.algebraMap_toAlgebra] using hσ (MvPolynomial.C a)

end GlobalTheory.GaloisDescent
end

-- bundled from Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.FinitePresentationOfInjective
section
noncomputable section

open AddMonoidAlgebra

namespace GlobalTheory.GroupAlg

variable (R : Type*) [CommRing R] {X Y : Type*} [AddCommGroup X] [AddCommGroup Y] (u : Y →+ X)

abbrev mapAlgebra : Algebra R[Y] R[X] := (mapDomainRingHom R u).toAlgebra

theorem mapAlgebra_tower : letI := mapAlgebra R u; IsScalarTower R R[Y] R[X] :=
  letI := mapAlgebra R u
  IsScalarTower.of_algebraMap_eq fun a => ((mapDomainAlgHom R R u).commutes a).symm

def cosetComb : letI := mapAlgebra R u; ((X ⧸ u.range) →₀ R[Y]) →ₗ[R[Y]] R[X] :=
  letI := mapAlgebra R u
  Finsupp.linearCombination R[Y] (fun c : X ⧸ u.range => (single c.out 1 : R[X]))

theorem cosetComb_single (c : X ⧸ u.range) (y : Y) (r : R) :
    cosetComb R u (Finsupp.single c (single y r)) = single (u y + c.out) r := by
  letI := mapAlgebra R u
  rw [cosetComb, Finsupp.linearCombination_single, Algebra.smul_def]
  change mapDomain u (single y r) * _ = _
  rw [mapDomain_single, single_mul_single, mul_one]

theorem exists_add_out (x : X) :
    ∃ y, u y + (QuotientAddGroup.mk x : X ⧸ u.range).out = x := by
  obtain ⟨⟨_, y, rfl⟩, h⟩ := QuotientAddGroup.mk_out_eq_mul u.range x
  exact ⟨-y, by rw [h]; simp⟩

theorem cosetComb_surjective : Function.Surjective (cosetComb R u) := by
  intro p
  induction p using AddMonoidAlgebra.induction_linear with
  | zero => exact ⟨0, map_zero _⟩
  | add s t hs ht =>
    obtain ⟨a, rfl⟩ := hs
    obtain ⟨b, rfl⟩ := ht
    exact ⟨a + b, map_add _ _ _⟩
  | single x r =>
    obtain ⟨y, hy⟩ := exists_add_out u x
    exact ⟨_, (cosetComb_single R u _ y r).trans (by rw [hy])⟩

theorem coset_bijective (hu : Function.Injective u) :
    Function.Bijective (fun p : (Σ _ : X ⧸ u.range, Y) => u p.2 + p.1.out) := by
  refine ⟨?_, fun x => ?_⟩
  · rintro ⟨c, y⟩ ⟨d, z⟩ h
    dsimp only at h
    have h1 : ∀ (c : X ⧸ u.range) y, (QuotientAddGroup.mk (u y + c.out) : X ⧸ u.range) = c := by
      intro c y
      rw [QuotientAddGroup.mk_add, (QuotientAddGroup.eq_zero_iff (N := u.range) (u y)).2 ⟨y, rfl⟩, zero_add,
        QuotientAddGroup.out_eq']
    obtain rfl : c = d := by rw [← h1 c y, h, h1]
    obtain rfl : y = z := hu (add_right_cancel h)
    rfl
  · obtain ⟨y, hy⟩ := exists_add_out u x
    exact ⟨⟨_, y⟩, hy⟩

theorem cosetComb_injective (hu : Function.Injective u) : Function.Injective (cosetComb R u) := by
  letI := mapAlgebra R u
  haveI := mapAlgebra_tower R u
  let b : Module.Basis (Σ _ : X ⧸ u.range, Y) R ((X ⧸ u.range) →₀ R[Y]) :=
    Finsupp.basis fun _ => AddMonoidAlgebra.basis Y R
  let e := b.equiv (AddMonoidAlgebra.basis X R) (Equiv.ofBijective _ (coset_bijective u hu))
  have : (cosetComb R u).restrictScalars R = e.toLinearMap := by
    refine b.ext fun p => ?_
    obtain ⟨c, y⟩ := p
    rw [LinearEquiv.coe_coe, Module.Basis.equiv_apply]
    simp [b, cosetComb_single]
  have h2 : ⇑(cosetComb R u) = e := congrArg DFunLike.coe this
  rw [h2]
  exact e.injective

def cosetBasis (hu : Function.Injective u) :
    letI := mapAlgebra R u; Module.Basis (X ⧸ u.range) R[Y] R[X] :=
  letI := mapAlgebra R u
  .ofRepr (LinearEquiv.ofBijective (cosetComb R u)
    ⟨cosetComb_injective R u hu, cosetComb_surjective R u⟩).symm

theorem free_of_injective (hu : Function.Injective u) :
    letI := mapAlgebra R u; Module.Free R[Y] R[X] :=
  letI := mapAlgebra R u
  .of_basis (cosetBasis R u hu)

theorem faithfullyFlat_of_injective (hu : Function.Injective u) :
    (mapDomainRingHom R u).FaithfullyFlat := by
  letI := mapAlgebra R u
  have := free_of_injective R u hu
  change Module.FaithfullyFlat R[Y] R[X]
  rcases subsingleton_or_nontrivial R with h | h
  · have : Subsingleton R[Y] := Module.subsingleton R _
    exact ⟨fun m hm => (hm.ne_top (Subsingleton.elim _ _)).elim⟩
  · infer_instance

theorem finite_of_finiteIndex [u.range.FiniteIndex] : (mapDomainRingHom R u).Finite := by
  letI := mapAlgebra R u
  exact Module.Finite.of_surjective (cosetComb R u) (cosetComb_surjective R u)

theorem finitePresentation_of_injective (hu : Function.Injective u) [u.range.FiniteIndex] :
    (mapDomainRingHom R u).FinitePresentation := by
  letI := mapAlgebra R u
  have := free_of_injective R u hu
  have : Module.Finite R[Y] R[X] := finite_of_finiteIndex R u
  have : Module.FinitePresentation R[Y] R[X] := Module.finitePresentation_of_projective _ _
  exact (inferInstance : Algebra.FinitePresentation R[Y] R[X])

theorem finrank_of_injective (hu : Function.Injective u) [u.range.FiniteIndex]
    (p : PrimeSpectrum R[Y]) : (mapDomainRingHom R u).finrank p = u.range.index := by
  letI := mapAlgebra R u
  have := free_of_injective R u hu
  have : Module.Finite R[Y] R[X] := finite_of_finiteIndex R u
  have : Nontrivial R[Y] := p.nontrivial
  change Module.rankAtStalk (R := R[Y]) R[X] p = _
  rw [Module.rankAtStalk_eq_finrank_of_free, Module.finrank_eq_nat_card_basis (cosetBasis R u hu)]
  rfl

theorem surjective_of_surjective (hu : Function.Surjective u) :
    Function.Surjective (mapDomainRingHom R u) := by
  intro p
  induction p using AddMonoidAlgebra.induction_linear with
  | zero => exact ⟨0, map_zero _⟩
  | add s t hs ht =>
    obtain ⟨a, rfl⟩ := hs
    obtain ⟨b, rfl⟩ := ht
    exact ⟨a + b, map_add _ _ _⟩
  | single x r =>
    obtain ⟨y, rfl⟩ := hu x
    exact ⟨single y r, mapDomain_single⟩

theorem formallyUnramified_of_isUnit (n : ℕ) (hn : IsUnit (n : R)) (hX : ∀ x : X, n • x = 0) :
    Algebra.FormallyUnramified R R[X] := by
  rw [Algebra.FormallyUnramified.iff_comp_injective]
  intro B _ _ I hI f g h
  ext x
  have hB : IsUnit (n : B) := by simpa using hn.map (algebraMap R B)
  have hfg : f (single x 1) - g (single x 1) ∈ I := by
    rw [← Ideal.Quotient.eq]
    exact DFunLike.congr_fun h (single x 1)
  have hp : ∀ k : R[X] →ₐ[R] B, k (single x 1) ^ n = 1 := fun k => by
    rw [← map_pow, single_pow, hX, one_pow, ← one_def, map_one]
  set a := f (single x 1)
  set b := g (single x 1)
  have hi : (a - b) * (a - b) = 0 := by
    have := Ideal.mul_mem_mul hfg hfg
    rwa [← pow_two, hI, Ideal.mem_bot] at this
  have key : ∀ m : ℕ, b * a ^ m = b ^ (m + 1) + m * b ^ m * (a - b) := by
    intro m
    induction m with
    | zero => simp
    | succ m ih =>
      rw [pow_succ a, ← mul_assoc, ih]
      push_cast
      linear_combination (m * b ^ m) * hi
  have h3 := key n
  rw [pow_succ b, hp f, hp g] at h3
  have h4 : (n : B) * (a - b) = 0 := by linear_combination -h3
  have h5 : a - b = 0 := (hB.mul_right_eq_zero).1 h4
  exact sub_eq_zero.1 h5

theorem etale_of_isUnit_card [Finite X] (hn : IsUnit (Nat.card X : R)) : Algebra.Etale R R[X] := by
  have := formallyUnramified_of_isUnit R (X := X) _ hn fun x => card_nsmul_eq_zero'
  have : Module.FinitePresentation R R[X] := Module.finitePresentation_of_projective _ _
  exact Algebra.Etale.of_formallyUnramified_of_flat

end GlobalTheory.GroupAlg
end
end

