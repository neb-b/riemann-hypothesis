module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsFrameCover
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PerValNeZero
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0521
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0525
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0507
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0011

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsFlagCellOfNonvanishingLeadingMinors
section
noncomputable section

open Matrix

namespace GlobalTheory.FlagEmb.CellLU

variable {K : Type} [Field K] {n : ℕ}

theorem exists_lower_mul_upper (A : Matrix (Fin n) (Fin n) K)
    (hA : ∀ (k : ℕ) (h : k ≤ n), (A.submatrix (Fin.castLE h) (Fin.castLE h)).det ≠ 0) :
    ∃ L : Matrix (Fin n) (Fin n) K, (∀ i k, i < k → L i k = 0) ∧ (∀ i, L i i = 1) ∧
      ∀ i j, j < i → (L * A) i j = 0 := by
  have hw : ∀ i : Fin n, ∃ v : Fin i → K, vecMul v (A.submatrix (Fin.castLE i.isLt.le) (Fin.castLE i.isLt.le)) =
      fun j : Fin i => A i (Fin.castLE i.isLt.le j) := fun i =>
    ⟨vecMul (fun j : Fin i => A i (Fin.castLE i.isLt.le j))
      (A.submatrix (Fin.castLE i.isLt.le) (Fin.castLE i.isLt.le))⁻¹, by
      rw [vecMul_vecMul, nonsing_inv_mul _ (isUnit_iff_ne_zero.mpr (hA _ _)), vecMul_one]⟩
  choose v hv using hw
  refine ⟨Matrix.of fun i k => if h : (k : ℕ) < i then -v i ⟨k, h⟩ else if k = i then 1 else 0, ?_, ?_, ?_⟩
  · intro i k h
    simp only [Matrix.of_apply]
    rw [dite_eq_right (by have := Fin.lt_def.mp h; omega), if_neg (ne_of_gt h)]
  · intro i
    simp
  · intro i j h
    rw [Matrix.mul_apply]
    have hsplit : ∀ k : Fin n,
        (Matrix.of fun i k : Fin n => if h : (k : ℕ) < i then -v i ⟨k, h⟩ else if k = i then (1 : K) else 0) i k * A k j =
        (if h : (k : ℕ) < i then -v i ⟨k, h⟩ * A k j else 0) + (if k = i then A i j else 0) := by
      intro k
      simp only [Matrix.of_apply]
      rcases lt_trichotomy k i with h | h | h
      · have hk : (k : ℕ) < i := h
        rw [dite_eq_left hk, dite_eq_left hk, if_neg (ne_of_lt h), add_zero]
      · subst h; simp
      · have hk : ¬ (k : ℕ) < i := by have := Fin.lt_def.mp h; omega
        rw [dite_eq_right hk, dite_eq_right hk, if_neg (ne_of_gt h), if_neg (ne_of_gt h), zero_mul, add_zero]
    rw [Finset.sum_congr rfl fun k _ => hsplit k, Finset.sum_add_distrib, Finset.sum_ite_eq',
      if_pos (Finset.mem_univ _)]
    have hs : ∑ k : Fin i, -v i k * A (Fin.castLE i.isLt.le k) j =
        ∑ k : Fin n, (if h : (k : ℕ) < i then -v i ⟨k, h⟩ * A k j else 0) := by
      refine Fintype.sum_of_injective (Fin.castLE i.isLt.le) (Fin.castLE_injective _) _ _ (fun k hk => ?_)
        (fun k => by simp)
      rw [dite_eq_right]
      intro hlt
      exact hk ⟨⟨k, hlt⟩, Fin.ext rfl⟩
    rw [← hs]
    have hj := congrFun (hv i) ⟨j, h⟩
    simp only [vecMul, dotProduct, Matrix.submatrix_apply] at hj
    have hcj : Fin.castLE i.isLt.le (⟨j, h⟩ : Fin i) = j := Fin.ext rfl
    rw [hcj] at hj
    rw [← hj]
    simp only [neg_mul, Finset.sum_neg_distrib]
    ring

theorem exists_lu (A : Matrix (Fin n) (Fin n) K)
    (hA : ∀ (k : ℕ) (h : k ≤ n), (A.submatrix (Fin.castLE h) (Fin.castLE h)).det ≠ 0) :
    ∃ N b : Matrix (Fin n) (Fin n) K, (∀ i k, i < k → N i k = 0) ∧ (∀ i, N i i = 1) ∧
      (∀ i j, j < i → b i j = 0) ∧ (∀ i, b i i ≠ 0) ∧ A = N * b := by
  obtain ⟨L, hup, hd, hz⟩ := exists_lower_mul_upper A hA
  have hLt : L.BlockTriangular OrderDual.toDual := fun i k h => hup i k h
  have hL : L.det = 1 := by
    rw [Matrix.det_of_lowerTriangular L hLt]
    simp [hd]
  have hu : IsUnit L.det := by rw [hL]; exact isUnit_one
  letI := L.invertibleOfIsUnitDet hu
  have hN : L⁻¹.BlockTriangular OrderDual.toDual := blockTriangular_inv_of_blockTriangular hLt
  refine ⟨L⁻¹, L * A, fun i k h => hN h, fun i => ?_, hz, fun i => ?_, ?_⟩
  · have h1 : (L * L⁻¹) i i = 1 := by rw [mul_nonsing_inv _ hu]; simp
    rw [Matrix.mul_apply, Finset.sum_eq_single i, hd, one_mul] at h1
    · exact h1
    · intro k _ hk
      rcases lt_or_gt_of_ne hk with h | h
      · rw [hN (show OrderDual.toDual i < OrderDual.toDual k from h), mul_zero]
      · rw [hup i k h, zero_mul]
    · simp
  · have h1 : (L * A).det ≠ 0 := by
      rw [det_mul, hL, one_mul]
      simpa using hA n le_rfl
    rw [Matrix.det_of_upperTriangular (fun i j h => hz i j h)] at h1
    exact Finset.prod_ne_zero_iff.1 h1 i (Finset.mem_univ _)
  · rw [← Matrix.mul_assoc, nonsing_inv_mul _ hu, Matrix.one_mul]

theorem sum_lform_plk {S : Type} [CommRing S] {M k : ℕ} {ι ι' : Type} (D : ι' → Fin (M + 1) → S)
    (u : ι → Fin (M + 1) → S) (ρ : Fin k → ι') (e : Fin k → ι) :
    ∑ q, lform D ρ q * plk u e q = (Matrix.of fun l l' => ∑ r, D (ρ l') r * u (e l) r).det := by
  have h := Equiv.sum_comp (plE M k)
    (fun q : Fin k → Fin (M + 1) => (∏ l, D (ρ l) (q l)) * (Matrix.of fun l l' => u (e l) (q l')).det)
  refine Eq.trans h ?_
  simp only [det_apply', Matrix.of_apply, Finset.prod_univ_sum, Fintype.piFinset_univ, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun σ _ => Finset.sum_congr rfl fun q _ => ?_
  rw [Finset.prod_mul_distrib]
  ring

theorem exists_cell (T : Type) (m : T → ℕ) (K : Type) [Field K] (M : ℕ) (D c u : Let m → Fin (M + 1) → K) (w : Pm m)
    (hD : LeftInv D c) (hu : InBlock c u)
    (h : ∀ τ j hj, ∑ q, lform D (wLet w ∘ std τ j hj) q * plk u (std τ j hj) q ≠ 0) :
    ∃ (x : CellVar m → K) (d : Let m → K), (∀ z, d z ≠ 0) ∧ Tri (cellVec c w x) u d := by
  have hA : ∀ τ, ∃ A : Matrix (Fin (m τ)) (Fin (m τ)) K, ∀ j, u ⟨τ, j⟩ = ∑ i, A i j • c ⟨τ, w τ i⟩ := fun τ => by
    have := fun j => (Submodule.mem_span_range_iff_exists_fun K).1 (hu ⟨τ, j⟩)
    choose a ha using this
    refine ⟨Matrix.of fun i j => a j (w τ i), fun j => ?_⟩
    rw [← ha j]
    exact (Equiv.sum_comp (w τ) (fun i => a j i • c ⟨τ, i⟩)).symm
  choose A hA using hA
  have hent : ∀ τ i j, ∑ r, D (wLet w ⟨τ, i⟩) r * u ⟨τ, j⟩ r = A τ i j := fun τ i j => by
    rw [hA]
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
    rw [Finset.sum_comm]
    have : ∀ i', ∑ r, D (wLet w ⟨τ, i⟩) r * (A τ i' j * c ⟨τ, w τ i'⟩ r) = if i' = i then A τ i' j else 0 := by
      intro i'
      have h1 := hD (wLet w ⟨τ, i⟩) ⟨τ, w τ i'⟩
      rw [show (∑ r, D (wLet w ⟨τ, i⟩) r * (A τ i' j * c ⟨τ, w τ i'⟩ r)) =
        A τ i' j * ∑ r, D (wLet w ⟨τ, i⟩) r * c ⟨τ, w τ i'⟩ r by
          rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun r _ => by ring, h1]
      by_cases hi : i' = i
      · subst hi; simp [wLet]
      · rw [if_neg hi, if_neg, mul_zero]
        intro he
        simp only [wLet, Sigma.mk.injEq, heq_eq_eq, true_and] at he
        exact hi ((w τ).injective he).symm
    simp [this]
  have hmin : ∀ τ (k : ℕ) (hk : k ≤ m τ), ((A τ).submatrix (Fin.castLE hk) (Fin.castLE hk)).det ≠ 0 := by
    intro τ k hk
    have h1 := h τ k hk
    rw [sum_lform_plk, ← det_transpose] at h1
    convert h1 using 2
    ext l l'
    exact (hent τ _ _).symm
  choose N b hN hN1 hb hb1 hNb using fun τ => exists_lu (A τ) (hmin τ)
  refine ⟨fun y => N y.1 y.2.1.1 y.2.1.2, fun z => b z.1 z.2 z.2, fun z => hb1 _ _, ?_⟩
  have hcell : ∀ τ i j, cell (fun y : CellVar m => N y.1 y.2.1.1 y.2.1.2) τ i j = N τ i j := by
    intro τ i j
    unfold cell
    rcases lt_trichotomy i j with h | h | h
    · rw [dite_eq_right (not_lt.2 h.le), if_neg h.ne, hN τ i j h]
    · subst h; simp [hN1]
    · rw [dite_eq_left h]
  rintro ⟨τ, j⟩
  have hexp : u ⟨τ, j⟩ = ∑ k, b τ k j • cellVec c w (fun y : CellVar m => N y.1 y.2.1.1 y.2.1.2) ⟨τ, k⟩ := by
    rw [hA, hNb]
    simp only [cellVec, hcell, Matrix.mul_apply, Finset.sum_smul, Finset.smul_sum, smul_smul]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun i _ => by rw [mul_comm]
  rw [hexp, ← Finset.add_sum_erase _ _ (Finset.mem_univ j), add_sub_cancel_left]
  refine Submodule.sum_mem _ fun k hk => ?_
  rcases lt_or_gt_of_ne (Finset.ne_of_mem_erase hk) with h | h
  · exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨k, h, rfl⟩)
  · rw [hb τ k j h, zero_smul]
    exact Submodule.zero_mem _

end GlobalTheory.FlagEmb.CellLU
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsHermitianPeriodLatticeBasisSameSignature
section
set_option autoImplicit false

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory GlobalTheory.Toroidal GlobalTheory.Cartier GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.ShFam.Hor
open scoped Matrix CategoryTheory.Obj Topology

namespace GlobalTheory.ShFam.Hor.PerBasis

theorem mult_conj_add_mult {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E}
    (D : Datum H) (τ : E →+* ℂ) : D.mult (conjEmb τ) + D.mult τ = D.p + D.q := by
  first
  | exact @_root_.GlobalTheory.ConjugateMultiplicity.target
  | exact _root_.GlobalTheory.ConjugateMultiplicity.target
  | (apply _root_.GlobalTheory.ConjugateMultiplicity.target <;> assumption)
  | (intros; apply _root_.GlobalTheory.ConjugateMultiplicity.target <;> assumption)
  | (intros; apply @_root_.GlobalTheory.ConjugateMultiplicity.target <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.ConjugateMultiplicity.target ..)

theorem exists_indep {E : Type} [Field E] [NumberField E] (M : Type) [AddCommGroup M] [Module (𝓞 E) M]
    [Module.Finite (𝓞 E) M] (J : Type) [Fintype J] (hJ : Fintype.card J = Module.finrank (𝓞 E) M) :
    ∃ x : J → M, LinearIndependent (𝓞 E) x ∧
      ∀ v, ∃ n : ℕ, n ≠ 0 ∧ n • v ∈ Submodule.span (𝓞 E) (Set.range x) := by
  obtain ⟨f, hf⟩ := exists_linearIndependent_of_le_finrank (R := 𝓞 E) (M := M) (n := Fintype.card J) hJ.le
  let e := Fintype.equivFin J
  refine ⟨f ∘ e, hf.comp _ e.injective, fun v => ?_⟩
  rw [e.surjective.range_comp]
  have hc : ∃ c : 𝓞 E, c ≠ 0 ∧ c • v ∈ Submodule.span (𝓞 E) (Set.range f) := by
    by_contra hcon
    push Not at hcon
    have hli : LinearIndependent (𝓞 E) (Fin.cons v f : Fin (Fintype.card J + 1) → M) := by
      refine LinearIndependent.finCons' v f hf fun c y hy h => ?_
      by_contra hc
      refine hcon c hc ?_
      rw [eq_neg_of_add_eq_zero_left h]
      exact neg_mem hy
    have := hli.fintype_card_le_finrank
    simp at this
    omega
  obtain ⟨c, hc0, hc⟩ := hc
  refine ⟨Ideal.absNorm (Ideal.span {c}), ?_, ?_⟩
  · rw [Ne, Ideal.absNorm_eq_zero_iff, Ideal.span_singleton_eq_bot]
    exact hc0
  · obtain ⟨d, hd⟩ := Ideal.mem_span_singleton'.1 (Ideal.absNorm_mem (Ideal.span {c}))
    rw [← Nat.cast_smul_eq_nsmul (𝓞 E), ← hd, mul_smul]
    exact Submodule.smul_mem _ _ hc

theorem exists_trace_rep {E : Type} [Field E] [NumberField E] (φ : 𝓞 E →ₗ[ℤ] ℤ) :
    ∃ h : E, ∀ a : 𝓞 E, ((φ a : ℤ) : ℚ) = Algebra.trace ℚ E ((a : E) * h) := by
  let ψ : E →ₗ[ℚ] ℚ := (integralBasis E).constr ℚ fun i => (φ (RingOfIntegers.basis E i) : ℚ)
  have hψ : ∀ a : 𝓞 E, ((φ a : ℤ) : ℚ) = ψ (a : E) := by
    intro a
    have : (Int.castAddHom ℚ).toIntLinearMap ∘ₗ φ =
        (ψ.restrictScalars ℤ) ∘ₗ ((algebraMap (𝓞 E) E).toAddMonoidHom.toIntLinearMap) := by
      refine (RingOfIntegers.basis E).ext fun i => ?_
      change ((φ (RingOfIntegers.basis E i) : ℤ) : ℚ) = ψ (algebraMap (𝓞 E) E (RingOfIntegers.basis E i))
      rw [← integralBasis_apply, Module.Basis.constr_basis]
    exact LinearMap.congr_fun this a
  refine ⟨((Algebra.traceForm ℚ E).toDual (traceForm_nondegenerate ℚ E)).symm ψ, fun a => ?_⟩
  rw [hψ, mul_comm, ← Algebra.traceForm_apply]
  exact (LinearMap.BilinForm.apply_toDual_symm_apply _ _).symm

theorem exists_isPerBasis : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E]
    (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw Di : Datum H) (τ : E →+* ℂ), Di.p = Dw.p ∧ Di.q = Dw.q →
    ∃ (x : Idx Dw τ → Di.La) (hm : Matrix (Idx Dw τ) (Idx Dw τ) E), IsPerBasis Di x hm := by
  intro E _ _ _ H Dw Di τ ⟨hp, hq⟩
  have := Di.fin
  obtain ⟨x, hx, hsp⟩ := exists_indep (E := E) Di.La (Idx Dw τ) (by
    rw [Fintype.card_sum, Fintype.card_fin, Fintype.card_fin, mult_conj_add_mult, Di.rank, hp, hq])
  have hrep : ∀ k k', ∃ h : E, ∀ a : 𝓞 E,
      ((Di.EF (a • x k) (x k') : ℤ) : ℚ) = Algebra.trace ℚ E ((a : E) * h) := fun k k' =>
    exists_trace_rep (AddMonoidHom.toIntLinearMap
      { toFun := fun a : 𝓞 E => Di.EF (a • x k) (x k')
        map_zero' := by simp
        map_add' := fun a b => by simp [add_smul] })
  choose hm hhm using hrep
  refine ⟨x, Matrix.of hm, hx, hsp, fun a k k' => hhm k k' a, fun hdet => ?_⟩
  obtain ⟨c₀, hc₀, hker⟩ := Matrix.exists_vecMul_eq_zero_iff.2 hdet
  obtain ⟨d, hd⟩ := IsLocalization.exist_integer_multiples_of_finite (nonZeroDivisors (𝓞 E)) c₀
  choose c hc using hd
  set v := ∑ k, c k • x k with hv
  have h1 : ∀ (a : 𝓞 E) k', Di.EF (a • v) (x k') = 0 := by
    intro a k'
    have hk := congrFun hker k'
    simp only [Matrix.vecMul, dotProduct, Matrix.of_apply, Pi.zero_apply] at hk
    have : ((Di.EF (a • v) (x k') : ℤ) : ℚ) = 0 := by
      set_option synthInstance.maxHeartbeats 100000 in
        rw [hv, Finset.smul_sum, map_sum, LinearMap.sum_apply]
      push_cast
      simp_rw [← mul_smul, hhm]
      set_option synthInstance.maxHeartbeats 100000 in
        rw [← map_sum]
      have : ∑ k, ((a * c k : 𝓞 E) : E) * hm k k' = (a : E) * ((d : 𝓞 E) : E) * ∑ k, c₀ k * hm k k' := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun k _ => ?_
        have h2 : ((c k : 𝓞 E) : E) = ((d : 𝓞 E) : E) * c₀ k := by
          exact (hc k).trans (Algebra.smul_def _ _)
        have h3 : ((a * c k : 𝓞 E) : E) = (a : E) * ((c k : 𝓞 E) : E) := map_mul (algebraMap (𝓞 E) E) _ _
        rw [h3, h2]; ring
      rw [this, hk]; simp
    exact_mod_cast this
  have h2 : ∀ w ∈ Submodule.span (𝓞 E) (Set.range x), ∀ a : 𝓞 E, Di.EF v (a • w) = 0 := by
    intro w hw
    induction hw using Submodule.span_induction with
    | mem w hw =>
      obtain ⟨k, rfl⟩ := hw
      intro a
      have := h1 (H.bar.symm a) k
      rwa [Di.adj, RingEquiv.apply_symm_apply] at this
    | zero => simp
    | add y z _ _ hy hz => intro a; rw [smul_add, map_add (f := _), hy, hz, add_zero]
    | smul b y _ hy => intro a; rw [← mul_smul, hy]
  have h3 : v = 0 := by
    apply Di.unimod.1
    rw [map_zero]
    ext w
    obtain ⟨n, hn, hw⟩ := hsp w
    have := h2 _ hw 1
    rw [one_smul, map_nsmul] at this
    simpa [hn] using this
  apply hc₀
  funext k
  have h4 := Fintype.linearIndependent_iff.1 hx c h3 k
  have h5 := hc k
  rw [h4, map_zero, Algebra.smul_def] at h5
  refine (mul_eq_zero.1 h5.symm).resolve_left ?_
  exact (map_ne_zero_iff _ (IsFractionRing.injective (𝓞 E) E)).2 (nonZeroDivisors.coe_ne_zero d)

end GlobalTheory.ShFam.Hor.PerBasis
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsHolomorphicFibreExponentialsNearCentre
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.ShFam.Hor GlobalTheory.ShFam.Hor.LogCh
open scoped Matrix CategoryTheory.Obj Topology
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.ShFam.Hor.LogCh

theorem isExpAt_homMk {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {X : Scheme.{0}} (t : SAB H X)
    {g : ℕ} (y₁ y₂ : Sp ℂ ⟶ X) (hy : y₁ = y₂) (e : (Fin g → ℂ) → (Over.mk y₁ ⟶ t.G))
    (hw : ∀ w, (e w).left ≫ t.G.hom = y₂)
    (hadd : ∀ z w, e (z + w) = e z * e w)
    (h1 : ∀ w, ∃! v : epsPt y₁ ⟶ t.G, IsDerivAt0 (fun z => (e z).left) w v.left)
    (h2 : ∀ v : epsPt y₁ ⟶ t.G, spMap (TrivSqZeroExt.fstHom ℂ ℂ ℂ).toRingHom ≫ v.left = (e 0).left →
      ∃! w, IsDerivAt0 (fun z => (e z).left) w v.left) :
    IsExpAt t y₂ (fun w => (Over.homMk (e w).left (hw w) : Over.mk y₂ ⟶ t.G)) := by
  subst hy
  have he : (fun w => (Over.homMk (e w).left (hw w) : Over.mk y₁ ⟶ t.G)) = e :=
    funext fun w => Over.OverMorphism.ext rfl
  rw [he]
  have hzero : e 0 = 1 := by
    have := hadd 0 0
    rw [add_zero] at this
    exact mul_eq_left.1 this.symm
  refine ⟨hadd, fun w => ?_, fun v hv => ?_⟩
  · obtain ⟨V, hV, hVu⟩ := h1 w
    refine ⟨V.left, ⟨⟨V.w, ?_⟩, hV⟩, fun v hv => ?_⟩
    · rw [hV.1]; exact congrArg Over.Hom.left hzero
    · have := hVu (Over.homMk v hv.1.1) hv.2
      exact congrArg CommaMorphism.left this
  · exact h2 (Over.homMk v hv.1) (by rw [hzero]; exact hv.2)

end GlobalTheory.ShFam.Hor.LogCh

namespace GlobalTheory.ShFam.Hor.LogCh

theorem exists_expMaps_near_chart_centre : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Z : Model Xo c β) (σ : c.F →+* ℂ) (n : ℕ) (e0 : OpenPartialHomeomorph (CxPts (genStr Z) σ) (Fin n → ℂ)), (0 : Fin n → ℂ) ∈ e0.target → IsHolTo e0.target (fun z => (e0.symm z).1) → ∃ (g : ℕ) (ρ : ℝ) (ex : ExpMaps Z σ g), 0 < ρ ∧ Metric.ball 0 ρ ⊆ e0.target ∧ IsHolTo (Metric.ball 0 ρ ×ˢ Set.univ) (fun zw : (Fin n → ℂ) × (Fin g → ℂ) => (ex (e0.symm zw.1) zw.2).left) ∧ ∀ x ∈ e0.source, ‖e0 x‖ < ρ → Function.Surjective (ex x) ∧ IsExpAt Z.t (x.1 ≫ genι Z) (ex x) := by
  intro E _ _ _ H Dw l Xo c O _ β Z σ n e0 h0 hsy
  let y : (Fin n → ℂ) → (Sp ℂ ⟶ Z.X) := fun z => (e0.symm z).1 ≫ genι Z
  have hy : IsHolTo e0.target y := GlobalTheory.RelExp.isHolTo_of_holAt e0.open_target fun z hz =>
    GlobalTheory.RelExp.HolAt.post ⟨e0.target, e0.open_target, hz, hsy⟩ (genι Z)
  obtain ⟨g, B', e, hB', hb', hfib, -⟩ := GlobalTheory.RelExp.exists_relative_exp_of_smooth _ Z.t.G n e0.target y 0
    Z.t.semi.smooth Z.t.semi.geomConnected e0.open_target h0 hy
  obtain ⟨ρ, hρ, hρB⟩ := Metric.isOpen_iff.1 (hB'.inter e0.open_target) 0 ⟨hb', h0⟩
  have hyx : ∀ x ∈ e0.source, y (e0 x) = x.1 ≫ genι Z := fun x hx => by simp only [y, e0.left_inv hx]
  have hw : ∀ x (hx : x ∈ e0.source) w, (e (e0 x) w).left ≫ Z.t.G.hom = x.1 ≫ genι Z := fun x hx w =>
    (e (e0 x) w).w.trans (hyx x hx)
  classical
  let ex : ExpMaps Z σ g := fun x w =>
    if hx : x ∈ e0.source then Over.homMk (e (e0 x) w).left (hw x hx w) else 1
  refine ⟨g, ρ, ex, hρ, fun z hz => (hρB hz).2, ?_, fun x hx hxρ => ?_⟩
  · refine GlobalTheory.RelExp.isHolTo_of_holAt (Metric.isOpen_ball.prod isOpen_univ) fun q hq => ?_
    refine ((hfib q.1 (hρB hq.1).1).1 q.2).congr ?_
    filter_upwards [(Metric.isOpen_ball.prod isOpen_univ).mem_nhds hq] with q' hq'
    have hs : e0.symm q'.1 ∈ e0.source := e0.map_target (hρB hq'.1).2
    have hr : e0 (e0.symm q'.1) = q'.1 := e0.right_inv (hρB hq'.1).2
    simp only [ex, dif_pos hs, Over.homMk_left]
    rw [hr]
  · have hb : e0 x ∈ B' := (hρB (mem_ball_zero_iff.2 hxρ)).1
    obtain ⟨-, hadd, hsurj, -, h1, h2⟩ := hfib _ hb
    have hex : ex x = fun w => (Over.homMk (e (e0 x) w).left (hw x hx w) : Over.mk (x.1 ≫ genι Z) ⟶ Z.t.G) := funext fun w => dif_pos hx
    rw [hex]
    refine ⟨fun a => ?_, isExpAt_homMk Z.t _ _ (hyx x hx) _ (hw x hx) hadd h1 h2⟩
    obtain ⟨z, hz⟩ := hsurj (Over.homMk a.left (a.w.trans (hyx x hx).symm))
    have hzl := congrArg CommaMorphism.left hz
    exact ⟨z, Over.OverMorphism.ext hzl⟩

end GlobalTheory.ShFam.Hor.LogCh
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsImmersionOfClosedPieces
section
open AlgebraicGeometry CategoryTheory Limits NumberField
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.LocM GlobalTheory.ShFam.Pad GlobalTheory.ProjSpace GlobalTheory.FlagEmb
open Formalism.MainNotions.DIV.Cons (intO)

namespace GlobalTheory.MemberGlue

theorem exists_immersion_of_closed_pieces : ∀ (P : Scheme.{0}) (ι : Type) [Finite ι] (C : ι → Scheme.{0}) [∀ a, IsAffine (C a)] [∀ a, IsReduced (C a)] (h : ∀ a, C a ⟶ P) (W : ι → P.Opens) (h' : ∀ a, C a ⟶ (W a).toScheme), IsLocallyNoetherian P → (∀ a, h' a ≫ (W a).ι = h a) → (∀ a, IsClosedImmersion (h' a)) → (∀ a a', Set.range (h a') ∩ (W a : Set P) ⊆ Set.range (h a)) → ∃ (F : Scheme.{0}) (f : F ⟶ P) (i : ∀ a, C a ⟶ F), IsImmersion f ∧ (∀ a, IsOpenImmersion (i a)) ∧ (∀ a, i a ≫ f = h a) ∧ ∀ x : F, ∃ a, x ∈ Set.range (i a) := by
  intro P ι _ C _ _ h W h' _ hh hcl hag
  have hpt : ∀ a c, (W a).ι (h' a c) = h a c := fun a c => by rw [← hh a]; rfl
  let U : P.Opens := ⨆ a, W a
  let Φ : Set P := ⋃ a, Set.range (h a)
  let O : ι → Set P := fun a => (W a).ι '' (Set.range (h' a))ᶜ
  have hO : ∀ a, IsOpen (O a) := fun a =>
    (W a).ι.isOpenEmbedding.isOpenMap _ (h' a).isClosedEmbedding.isClosed_range.isOpen_compl
  have hW : ∀ a c, h a c ∈ (W a : Set P) := fun a c => by
    rw [← hpt a c]; exact (h' a c).2
  have hU : ∀ a, (W a : Set P) ⊆ U := fun a =>
    SetLike.coe_subset_coe.mpr (le_iSup W a)
  have hΦ : U.ι ⁻¹' Φ = (U.ι ⁻¹' ⋃ a, O a)ᶜ := by
    ext x
    simp only [Set.mem_preimage, Set.mem_compl_iff]
    constructor
    · intro hx hxO
      obtain ⟨a', c', hc'⟩ := Set.mem_iUnion.mp hx
      obtain ⟨a, w, hw, e⟩ := Set.mem_iUnion.mp hxO |>.imp fun _ h => h
      have h1 : U.ι x ∈ Set.range (h a') ∩ (W a : Set P) :=
        ⟨⟨c', hc'⟩, e ▸ w.2⟩
      obtain ⟨c, hc⟩ := hag a a' h1
      exact hw ⟨c, (W a).ι.isOpenEmbedding.injective ((hpt a c).trans (hc.trans e.symm))⟩
    · intro hx
      obtain ⟨a, ha⟩ := TopologicalSpace.Opens.mem_iSup.mp x.2
      have h2 : (⟨x.1, ha⟩ : (W a).toScheme) ∈ Set.range (h' a) := by
        by_contra hn
        exact hx (Set.mem_iUnion.mpr ⟨a, ⟨x.1, ha⟩, hn, rfl⟩)
      obtain ⟨c, hc⟩ := h2
      exact Set.mem_iUnion.mpr ⟨a, c, by rw [← hpt a c, hc]; rfl⟩
  let Z : TopologicalSpace.Closeds U.toScheme := ⟨U.ι ⁻¹' Φ, by
    rw [hΦ]
    exact ((isOpen_iUnion hO).preimage U.ι.continuous).isClosed_compl⟩
  let I := Scheme.IdealSheafData.vanishingIdeal Z
  let g : I.subscheme ⟶ U.toScheme := I.subschemeι
  let f : I.subscheme ⟶ P := g ≫ U.ι
  have hrg : Set.range g = Z := by
    rw [Scheme.IdealSheafData.range_subschemeι, Scheme.IdealSheafData.coe_support_vanishingIdeal]
  have hfΦ : ∀ x, f x ∈ Φ := fun x => by
    have : g x ∈ (Z : Set U.toScheme) := hrg ▸ ⟨x, rfl⟩
    exact this
  have hfinj : Function.Injective f := f.isEmbedding.injective
  have hrU : ∀ a, Set.range (h a) ⊆ Set.range U.ι := fun a => by
    rintro _ ⟨c, rfl⟩
    rw [Scheme.Opens.range_ι]
    exact hU a (hW a c)
  let k : ∀ a, C a ⟶ U.toScheme := fun a => IsOpenImmersion.lift U.ι (h a) (hrU a)
  have hk : ∀ a, k a ≫ U.ι = h a := fun a => IsOpenImmersion.lift_fac _ _ _
  have hkZ : ∀ a, Set.range (k a) ⊆ Z := fun a => by
    rintro _ ⟨c, rfl⟩
    change U.ι (k a c) ∈ Φ
    have : U.ι (k a c) = h a c := by rw [← hk a]; rfl
    rw [this]
    exact Set.mem_iUnion.mpr ⟨a, c, rfl⟩
  have hker : ∀ a, g.ker ≤ (k a).ker := fun a => by
    rw [Scheme.IdealSheafData.ker_subschemeι]
    exact ReducedSubgroup.vanishingIdeal_le_ker (k a) Z (hkZ a)
  let i : ∀ a, C a ⟶ I.subscheme := fun a => IsClosedImmersion.lift g (k a) (hker a)
  have hig : ∀ a, i a ≫ g = k a := fun a => IsClosedImmersion.lift_fac _ _ _
  have hif : ∀ a, i a ≫ f = h a := fun a => by
    rw [← hk a, ← hig a, Category.assoc]
  have hipt : ∀ a c, f (i a c) = h a c := fun a c => by rw [← hif a]; rfl
  have : IsReduced I.subscheme := ReducedSubgroup.isReduced_subscheme_vanishingIdeal Z
  refine ⟨I.subscheme, f, i, inferInstance, fun a => ?_, hif, fun x => ?_⟩
  · let V : I.subscheme.Opens := f ⁻¹ᵁ W a
    have hiV : Set.range (i a) ⊆ Set.range V.ι := by
      rintro _ ⟨c, rfl⟩
      rw [Scheme.Opens.range_ι]
      change f (i a c) ∈ W a
      rw [hipt]
      exact hW a c
    have hrW : Set.range (V.ι ≫ f) ⊆ Set.range (W a).ι := by
      rintro _ ⟨y, rfl⟩
      rw [Scheme.Opens.range_ι]
      exact y.2
    let j : C a ⟶ V.toScheme := IsOpenImmersion.lift V.ι (i a) hiV
    have hj : j ≫ V.ι = i a := IsOpenImmersion.lift_fac _ _ _
    let r : V.toScheme ⟶ (W a).toScheme := IsOpenImmersion.lift (W a).ι (V.ι ≫ f) hrW
    have hr : r ≫ (W a).ι = V.ι ≫ f := IsOpenImmersion.lift_fac _ _ _
    have hjr : j ≫ r = h' a := by
      rw [← cancel_mono (W a).ι, Category.assoc, hr, reassoc_of% hj, hif, hh]
    have : Mono r := by
      have : Mono (r ≫ (W a).ι) := by rw [hr]; infer_instance
      exact mono_of_mono r (W a).ι
    have : IsClosedImmersion (j ≫ r) := by rw [hjr]; infer_instance
    have : IsClosedImmersion j := IsClosedImmersion.of_comp j r
    have : Surjective j := ⟨fun y => by
      have hy : f (V.ι y) ∈ (W a : Set P) := y.2
      obtain ⟨a', c', hc'⟩ := Set.mem_iUnion.mp (hfΦ (V.ι y))
      obtain ⟨c, hc⟩ := hag a a' ⟨⟨c', hc'⟩, hy⟩
      refine ⟨c, V.ι.isOpenEmbedding.injective (hfinj ?_)⟩
      have : V.ι (j c) = i a c := by rw [← hj]; rfl
      rw [this, hipt, hc]⟩
    have : IsIso j := isIso_of_isClosedImmersion_of_surjective j
    rw [← hj]
    infer_instance
  · obtain ⟨a, c, hc⟩ := Set.mem_iUnion.mp (hfΦ x)
    exact ⟨a, c, hfinj ((hipt a c).trans hc)⟩

end GlobalTheory.MemberGlue
end

