module

public import Mathlib
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0003
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.Bundle0004
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.GlobalSectionsRankAlgClosed
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SymplecticGenerators.SymplecticCharacters.OneEqSpTranslZero
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.ExistsChartOfMemRedKer
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.HasSumPolyDerivMulProdAddMatrix

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.SubsingletonPrimeSpectrum
section
set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Chart (sp IsTan fstD scaleD prodPts isTan_iff isLieComb_iff comp_one' isTan_mul isTan_one
  isTan_scale)
open GlobalTheory.SqZero
open TrivSqZeroExt (inl inr)

namespace GlobalTheory.UnifDifferential

attribute [local instance] Over.cartesianMonoidalCategory

section Pull

variable {R : Type} [CommRing R] {A : Over (Spec (CommRingCat.of R))}
  {S S' : Type} [CommRing S] [Algebra R S] [CommRing S'] [Algebra R S']

def pullFn (y : sp (R₀ := R) S ⟶ A) (U : A.left.Opens) (h : ⊤ ≤ y.left ⁻¹ᵁ U) (f : Γ(A.left, U)) : S :=
  (Scheme.ΓSpecIso (CommRingCat.of S)).hom.hom ((y.left.appLE U ⊤ h).hom f)

theorem pullFn_comp (φ : S →ₐ[R] S') (y : sp (R₀ := R) S ⟶ A) (y' : sp (R₀ := R) S' ⟶ A)
    (e : y' = Chart.spMap φ ≫ y) (U : A.left.Opens) (h : ⊤ ≤ y.left ⁻¹ᵁ U)
    (h' : ⊤ ≤ y'.left ⁻¹ᵁ U) (f : Γ(A.left, U)) :
    pullFn y' U h' f = φ (pullFn y U h f) := by
  subst e
  have e : (Chart.spMap φ ≫ y).left.appLE U ⊤ h' =
      y.left.appLE U ⊤ h ≫ (Spec.map (CommRingCat.ofHom (φ : S →+* S'))).appTop := by
    rw [Scheme.Hom.appTop, Scheme.Hom.app_eq_appLE]
    exact (Scheme.Hom.appLE_comp_appLE (Spec.map (CommRingCat.ofHom (φ : S →+* S'))) y.left U ⊤ ⊤ h le_rfl).symm
  have e2 := congrArg (fun k => k.hom ((y.left.appLE U ⊤ h).hom f))
    (Scheme.ΓSpecIso_naturality (CommRingCat.ofHom (φ : S →+* S')))
  unfold pullFn
  rw [e]
  exact e2

theorem le_preimage_comp (φ : S →ₐ[R] S') (y : sp (R₀ := R) S ⟶ A) (y' : sp (R₀ := R) S' ⟶ A)
    (e : y' = Chart.spMap φ ≫ y) (U : A.left.Opens) (h : ⊤ ≤ y.left ⁻¹ᵁ U) :
    ⊤ ≤ y'.left ⁻¹ᵁ U := by
  subst e
  exact fun x _ => h (Set.mem_univ ((Chart.spMap φ).left x))

theorem le_preimage_of_comp [Subsingleton (PrimeSpectrum S)] [Nontrivial S'] (φ : S →ₐ[R] S')
    (y : sp (R₀ := R) S ⟶ A) (y' : sp (R₀ := R) S' ⟶ A)
    (e : y' = Chart.spMap φ ≫ y) (U : A.left.Opens) (h : ⊤ ≤ y'.left ⁻¹ᵁ U) :
    ⊤ ≤ y.left ⁻¹ᵁ U := by
  subst e
  intro x _
  obtain ⟨x'⟩ : Nonempty (PrimeSpectrum S') := inferInstance
  have := h (Set.mem_univ x')
  have hx : (Chart.spMap φ).left x' = x := Subsingleton.elim (α := PrimeSpectrum S) _ _
  change y.left ((Chart.spMap φ).left x') ∈ U at this
  rwa [hx] at this

end Pull

theorem subsingleton_primeSpectrum (K M : Type) [Field K] [AddCommGroup M] [Module K M] [Module Kᵐᵒᵖ M]
    [IsCentralScalar K M] : Subsingleton (PrimeSpectrum (TrivSqZeroExt K M)) := by
  have h : ∀ z : PrimeSpectrum (TrivSqZeroExt K M), ∀ a, a ∈ z.asIdeal ↔ a.fst = 0 := fun z a => by
    constructor
    · intro ha
      by_contra h0
      exact z.2.ne_top (z.asIdeal.eq_top_of_isUnit_mem ha
        (TrivSqZeroExt.isUnit_iff_isUnit_fst.2 (Ne.isUnit h0)))
    · intro ha
      refine z.2.mem_of_pow_mem 2 ?_
      rw [show a ^ 2 = 0 by ext <;> simp [pow_two, ha]]
      exact z.asIdeal.zero_mem
  refine ⟨fun x y => ?_⟩
  ext a
  rw [h, h]

variable {K : Type} [Field K] {A : Over (Spec (CommRingCat.of K))} [GrpObj A]

theorem snd_pullFn_mul {v v' : sp (R₀ := K) (DualNumber K) ⟶ A} (hv : IsTan v) (hv' : IsTan v')
    (U : A.left.Opens) (h : ⊤ ≤ (v * v').left ⁻¹ᵁ U) :
    ∃ (h₁ : ⊤ ≤ v.left ⁻¹ᵁ U) (h₂ : ⊤ ≤ v'.left ⁻¹ᵁ U), ∀ f : Γ(A.left, U),
      (pullFn (v * v') U h f).snd = (pullFn v U h₁ f).snd + (pullFn v' U h₂ f).snd := by
  let E := TrivSqZeroExt K (Fin 2 → K)
  have : Subsingleton (PrimeSpectrum E) := subsingleton_primeSpectrum K _
  let e : Fin 2 → E := fun i => inr (Pi.single i 1)
  have he : ∀ i j, e i * e j = 0 := fun i j => TrivSqZeroExt.inr_mul_inr _ _ _
  have ax : ∀ c : Fin 2 → K, ∀ a b : Fin 2, (inr (c a) : DualNumber K) * inr (c b) = 0 :=
    fun c a b => TrivSqZeroExt.inr_mul_inr _ _ _
  let q : (Fin 2 → K) → (E →ₐ[K] DualNumber K) := fun c =>
    vecTo (Algebra.ofId K _) (fun a => inr (c a)) (ax c)
  have hq : ∀ c a, q c (e a) = inr (c a) := fun c a => vecTo_single _ _ _ _
  have hqs : ∀ c (x : E), (q c x).snd = x.snd 0 * c 0 + x.snd 1 * c 1 := fun c x => by
    refine (congrArg TrivSqZeroExt.snd (vecTo_apply _ _ (ax c) x)).trans ?_
    simp [Algebra.ofId_apply, TrivSqZeroExt.algebraMap_eq_inl, mul_comm]
  have hid : ∀ (t : DualNumber K) (ht : t * t = 0), t = inr 1 → epsTo K t ht = AlgHom.id K _ :=
    fun t ht h => DualNumber.algHom_ext (by rw [epsTo_eps, h]; rfl)
  let p : sp (R₀ := K) E ⟶ A :=
    (Chart.spMap (epsTo K (e 0) (he 0 0)) ≫ v) * (Chart.spMap (epsTo K (e 1) (he 1 1)) ≫ v')
  have e₀ : v * v' = Chart.spMap (q ![1, 1]) ≫ p := by
    simp only [p, MonObj.comp_mul, ← Category.assoc, Chart.spMap_comp, comp_epsTo]
    rw [hid _ _ (by simp [hq]), hid _ _ (by simp [hq]), Chart.spMap_id, Category.id_comp, Category.id_comp]
  have e₁ : v = Chart.spMap (q ![1, 0]) ≫ p := by
    simp only [p, MonObj.comp_mul, ← Category.assoc, Chart.spMap_comp, comp_epsTo]
    rw [hid _ _ (by simp [hq]), epsTo_zero_comp hv' _ (by simp [hq]), Chart.spMap_id, Category.id_comp,
      _root_.mul_one]
  have e₂ : v' = Chart.spMap (q ![0, 1]) ≫ p := by
    simp only [p, MonObj.comp_mul, ← Category.assoc, Chart.spMap_comp, comp_epsTo]
    rw [epsTo_zero_comp hv _ (by simp [hq]), hid _ _ (by simp [hq]), Chart.spMap_id, Category.id_comp,
      _root_.one_mul]
  have hp := le_preimage_of_comp _ _ _ e₀ U h
  refine ⟨le_preimage_comp _ _ _ e₁ U hp, le_preimage_comp _ _ _ e₂ U hp, fun f => ?_⟩
  rw [pullFn_comp _ _ _ e₀ U hp, pullFn_comp _ _ _ e₁ U hp, pullFn_comp _ _ _ e₂ U hp, hqs, hqs, hqs]
  simp

section Unif

variable {A : Over (Sp ℂ)} [GrpObj A] {L : LB A.left} {g : ℕ} (u : HolUnif A L g)

theorem isDiff_mul {w w' : Fin g → ℂ} {v v' : epsR ℂ ⟶ A} (hv : IsTan v) (hv' : IsTan v')
    (h : u.IsDiff w v) (h' : u.IsDiff w' v') : u.IsDiff (w + w') (v * v') := by
  intro U hU f
  obtain ⟨h₁, h₂, e⟩ := snd_pullFn_mul hv hv' U hU
  rw [map_add (f := _), ← h U h₁ f, ← h' U h₂ f]
  exact e f

theorem isDiff_scale {w : Fin g → ℂ} {v : epsR ℂ ⟶ A} (h : u.IsDiff w v) (c : ℂ) :
    u.IsDiff (c • w) (Chart.spMap (scaleD c) ≫ v) := by
  intro U hU f
  have : Subsingleton (PrimeSpectrum (DualNumber ℂ)) := subsingleton_primeSpectrum ℂ ℂ
  have hU' := le_preimage_of_comp (scaleD c) v _ rfl U hU
  rw [map_smul, ← h U hU' f]
  refine (congrArg TrivSqZeroExt.snd (pullFn_comp (scaleD c) v _ rfl U hU' hU f)).trans ?_
  rw [scaleD_eq]
  simp [epsTo, dualTo_apply, Algebra.ofId_apply, TrivSqZeroExt.algebraMap_eq_inl, pullFn, mul_comm]

theorem isDiff_one : u.IsDiff 0 (1 : epsR ℂ ⟶ A) := by
  intro U hU f
  rw [map_zero]
  refine (congrArg TrivSqZeroExt.snd
    (pullFn_comp (scaleD (0 : ℂ)) (1 : epsR ℂ ⟶ A) 1 (comp_one' _).symm U hU hU f)).trans ?_
  rw [scaleD_eq]
  simp [epsTo, dualTo_apply, Algebra.ofId_apply, TrivSqZeroExt.algebraMap_eq_inl]

theorem isDiff_prod : ∀ {n : ℕ} (W : Fin n → Fin g → ℂ) (v : Fin n → (epsR ℂ ⟶ A)),
    (∀ i, IsTan (v i)) → (∀ i, u.IsDiff (W i) (v i)) →
      IsTan (List.ofFn v).prod ∧ u.IsDiff (∑ i, W i) (List.ofFn v).prod := by
  intro n
  induction n with
  | zero =>
      intro W v _ _
      rw [List.ofFn_zero, List.prod_nil, Finset.univ_eq_empty, Finset.sum_empty]
      exact ⟨isTan_one, isDiff_one u⟩
  | succ n ih =>
      intro W v hv h
      obtain ⟨h₁, h₂⟩ := ih (fun i => W i.succ) (fun i => v i.succ)
        (fun i => hv i.succ) (fun i => h i.succ)
      rw [List.ofFn_succ, List.prod_cons, Fin.sum_univ_succ]
      exact ⟨isTan_mul (hv 0) h₁, isDiff_mul u (hv 0) h₁ (h 0) h₂⟩

end Unif

theorem isDiff_of_isLieComb :
    ∀ (A : Over (Sp ℂ)) [GrpObj A] (L : LB A.left) (g n : ℕ) (u : HolUnif A L g) (W : Fin n → (Fin g → ℂ))
      (v : Fin n → (epsR ℂ ⟶ A)) (c : Fin n → ℂ) (w : epsR ℂ ⟶ A), (∀ i, IsTangent (v i)) →
      (∀ i, u.IsDiff (W i) (v i)) → IsLieComb c v w → u.IsDiff (∑ i, c i • W i) w := by
  intro A _ L g n u W v c w hv h hw
  rw [(isLieComb_iff c v w).1 hw]
  exact (isDiff_prod u (fun i => c i • W i) _ (fun i => isTan_scale (c i) ((isTan_iff _).2 (hv i)))
    (fun i => isDiff_scale u (h i) (c i))).2

end GlobalTheory.UnifDifferential
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.ThetaCharBlockDiagonal
section
noncomputable section

open Matrix ReciprocityTheory.ChartRestriction.G.Geo.Tor

namespace GlobalTheory.ThetaPow

variable {j g G : ℕ}

theorem dotProduct_blocks {R : Type*} [CommRing R] (e : Fin j × Fin g ≃ Fin G) (x y : Fin G → R) :
    x ⬝ᵥ y = ∑ i : Fin j, (fun k => x (e (i, k))) ⬝ᵥ (fun k => y (e (i, k))) := by
  unfold dotProduct
  rw [← e.sum_comp, Fintype.sum_prod_type]

theorem mulVec_blocks {R : Type*} [CommRing R] (e : Fin j × Fin g ≃ Fin G)
    (M : Matrix (Fin g) (Fin g) R) (y : Fin G → R) (i : Fin j) :
    (fun k => ((Matrix.of fun p q => if (e.symm p).1 = (e.symm q).1 then
        M (e.symm p).2 (e.symm q).2 else 0 : Matrix (Fin G) (Fin G) R) *ᵥ y) (e (i, k))) =
      M *ᵥ fun k => y (e (i, k)) := by
  funext k
  simp only [mulVec, dotProduct, of_apply]
  rw [← e.sum_comp, Fintype.sum_prod_type]
  simp only [Equiv.symm_apply_apply, ite_mul, zero_mul]
  rw [Finset.sum_eq_single i]
  · simp
  · intro c _ hc
    simp [Ne.symm hc]
  · simp

theorem posDef_blocks (e : Fin j × Fin g ≃ Fin G) {M : Matrix (Fin g) (Fin g) ℝ} (hM : M.PosDef) :
    (Matrix.of fun p q => if (e.symm p).1 = (e.symm q).1 then
        M (e.symm p).2 (e.symm q).2 else 0 : Matrix (Fin G) (Fin G) ℝ).PosDef := by
  refine posDef_iff_dotProduct_mulVec.2 ⟨?_, fun x hx => ?_⟩
  · ext p q
    have h := hM.1.apply (e.symm p).2 (e.symm q).2
    simp only [conjTranspose_apply, of_apply, star_trivial] at h ⊢
    by_cases hpq : (e.symm p).1 = (e.symm q).1
    · rw [if_pos hpq, if_pos hpq.symm, h]
    · rw [if_neg hpq, if_neg (Ne.symm hpq)]
  · rw [dotProduct_blocks e]
    simp only [mulVec_blocks]
    obtain ⟨p, hp⟩ := Function.ne_iff.1 hx
    refine Finset.sum_pos' (fun i _ => ?_) ⟨(e.symm p).1, Finset.mem_univ _, ?_⟩
    · exact hM.posSemidef.dotProduct_mulVec_nonneg _
    · refine (posDef_iff_dotProduct_mulVec.1 hM).2 (x := fun k => x (e ((e.symm p).1, k))) ?_
      refine Function.ne_iff.2 ⟨(e.symm p).2, ?_⟩
      simpa using hp

def blockEquiv (e : Fin j × Fin g ≃ Fin G) : (Fin G → ℤ) ≃ (Fin j → Fin g → ℤ) :=
  (Equiv.arrowCongr e.symm (Equiv.refl ℤ)).trans (Equiv.curry _ _ _)

theorem blockEquiv_apply (e : Fin j × Fin g ≃ Fin G) (m : Fin G → ℤ) (i : Fin j) (k : Fin g) :
    blockEquiv e m i k = m (e (i, k)) := rfl

theorem thTerm_blocks (e : Fin j × Fin g ≃ Fin G) (τ : Matrix (Fin g) (Fin g) ℂ) (a b : Fin g → ℝ)
    (z : Fin G → ℂ) (m : Fin G → ℤ) :
    CanTh.thTerm (Matrix.of fun p q => if (e.symm p).1 = (e.symm q).1 then
        τ (e.symm p).2 (e.symm q).2 else 0) (fun p => a (e.symm p).2) (fun p => b (e.symm p).2) z m =
      ∏ i : Fin j, CanTh.thTerm τ a b (fun k => z (e (i, k))) (blockEquiv e m i) := by
  unfold CanTh.thTerm
  rw [← Complex.exp_sum, dotProduct_blocks e, dotProduct_blocks e (y := z + _), Finset.mul_sum,
    Finset.mul_sum, ← Finset.sum_add_distrib]
  congr 1
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [mulVec_blocks]
  simp only [Pi.add_def, Equiv.symm_apply_apply, blockEquiv_apply]

end GlobalTheory.ThetaPow

namespace GlobalTheory


open ThetaPow in
theorem thetaChar_blockDiagonal (j g : ℕ) (τ : Matrix (Fin g) (Fin g) ℂ) (a b : Fin g → ℝ) (G : ℕ)
    (e : Fin j × Fin g ≃ Fin G) (hs : τ.IsSymm) (hp : (τ.map Complex.im).PosDef) :
    let τ' : Matrix (Fin G) (Fin G) ℂ := Matrix.of fun p q =>
      if (e.symm p).1 = (e.symm q).1 then τ (e.symm p).2 (e.symm q).2 else 0
    τ'.IsSymm ∧ (τ'.map Complex.im).PosDef ∧ ∀ z : Fin G → ℂ,
      thetaChar τ' (fun p => (a (e.symm p).2 : ℂ)) (fun p => (b (e.symm p).2 : ℂ)) z =
        ∏ i : Fin j, thetaChar τ (fun k => (a k : ℂ)) (fun k => (b k : ℂ)) (fun k => z (e (i, k))) := by
  intro τ'
  refine ⟨?_, ?_, fun z => ?_⟩
  · ext p q
    simp only [τ', transpose_apply, of_apply]
    by_cases hpq : (e.symm p).1 = (e.symm q).1
    · rw [if_pos hpq, if_pos hpq.symm, hs.apply]
    · rw [if_neg hpq, if_neg (Ne.symm hpq)]
  · convert posDef_blocks e hp using 1
    ext p q
    simp only [τ', map_apply, of_apply]
    split_ifs <;> simp
  · rw [CanTh.thetaChar_eq_tsum τ' (fun p => a (e.symm p).2) (fun p => b (e.symm p).2) z]
    simp only [τ', thTerm_blocks]
    rw [(blockEquiv e).tsum_eq
      (fun m => ∏ i : Fin j, CanTh.thTerm τ a b (fun k => z (e (i, k))) (m i))]
    exact (CanTh.hasSum_prod_thTerm (τ := fun _ : Fin j => τ) (fun _ => CanTh.mem_thetaDomain hp)
      (fun _ => a) (fun _ => b) (fun i k => z (e (i, k)))).tsum_eq

end GlobalTheory
end
end

