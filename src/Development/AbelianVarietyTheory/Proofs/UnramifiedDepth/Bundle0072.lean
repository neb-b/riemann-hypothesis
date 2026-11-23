module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Jets.TwoPlaces
public import Formalism.LocalToGlobal.CharacterGerms.Bundle0014
public import Development.AbelianVarietyTheory.Definitions.TeichmullerDepth.HasTeich
public import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.Bundle0045
public import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.Bundle0070
public import Formalism.LocalToGlobal.CharacterGerms.Interface
public import Formalism.LocalToGlobal.CharacterGerms.Bundle0012

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.EmbeddingsCongruentEq
section
open scoped BigOperators TensorProduct
open NumberField IsLocalRing Formalism.IncomingBounds Formalism.L2.FormalSeriesBounds Formalism.L2.Pj GlobalTheory.RowLaw ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ
open ReciprocityTheory.ChartRestriction.G.Pdiv.ChartF ReciprocityTheory.ChartRestriction.G.Pdiv.AvDefs

namespace GlobalTheory

theorem ringOfIntegers_hom_injective (E : Type) [Field E] [NumberField E] (C : Type) [Field C]
    [CharZero C] (f : 𝓞 E →+* C) : Function.Injective f := by
  rw [RingHom.injective_iff_ker_eq_bot]
  apply Ideal.eq_bot_of_comap_eq_bot (R := ℤ)
  rw [eq_bot_iff]
  intro n hn
  simp only [Ideal.mem_comap, RingHom.mem_ker, eq_intCast, map_intCast, Int.cast_eq_zero] at hn
  simpa using hn

theorem ringOfIntegers_hom_eq_of_congr_maximalIdeal :
    ∀ (E : Type) [Field E] [NumberField E] (p : ℕ), p.Prime → ¬ ((p : ℤ) ∣ NumberField.discr E) → ∀ (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (O : Type) [CommRing O] [IsLocalRing O] [Algebra O C], v.Integers O → ¬ IsUnit (p : O) → ∀ σ σ' : 𝓞 E →+* O, (∀ x, σ x - σ' x ∈ maximalIdeal O) → σ = σ' := by
  intro E _ _ p hp hd C _ _ _ v O _ _ _ hv hpu σ σ' hcong
  classical
  by_contra hne
  have hinj : Function.Injective (algebraMap O C) := hv.hom_inj

  have hext : ∀ s : 𝓞 E →+* O, ∃ τ : E →ₐ[ℚ] C,
      ∀ x : 𝓞 E, τ (algebraMap (𝓞 E) E x) = algebraMap O C (s x) := by
    intro s
    refine ⟨(IsFractionRing.lift (K := E)
      (ringOfIntegers_hom_injective E C ((algebraMap O C).comp s))).toRatAlgHom, fun x => ?_⟩
    simp
  obtain ⟨τ, hτ⟩ := hext σ
  obtain ⟨τ', hτ'⟩ := hext σ'
  have hττ : τ ≠ τ' := by
    intro h
    apply hne
    ext x
    apply hinj
    rw [← hτ, ← hτ', h]
  have hmem : ∀ (φ : E →ₐ[ℚ] C) (x : 𝓞 E), ∃ y : O,
      algebraMap O C y = φ (algebraMap (𝓞 E) E x) := by
    intro φ x
    have h1 : IsIntegral ℤ (φ (algebraMap (𝓞 E) E x)) :=
      (x.isIntegral_coe).map (φ.toRingHom.toIntAlgHom)
    have h2 : IsIntegral O (φ (algebraMap (𝓞 E) E x)) := h1.tower_top
    exact hv.exists_of_le_one (hv.mem_of_integral h2)
  choose F hF using hmem
  let ι := Module.Free.ChooseBasisIndex ℤ (𝓞 E)
  let e : ι ≃ (E →ₐ[ℚ] C) := Fintype.equivOfCardEq (by
    rw [AlgHom.card, Module.finrank_eq_card_basis (integralBasis E)])
  let N : Matrix ι ι O := fun i j => F (e j) (RingOfIntegers.basis E i)
  have hN : (algebraMap O C).mapMatrix N =
      Algebra.embeddingsMatrixReindex ℚ C (integralBasis E) e := by
    ext i j
    show algebraMap O C (F (e j) (RingOfIntegers.basis E i)) = _
    simp [hF, Algebra.embeddingsMatrixReindex, integralBasis_apply]
  have hdisc : ((NumberField.discr E : ℤ) : O) = N.det ^ 2 := by
    apply hinj
    rw [map_pow, RingHom.map_det, hN, ← Algebra.discr_eq_det_embeddingsMatrixReindex_pow_two,
      ← NumberField.coe_discr]
    simp
  have hdet : N.det ∈ maximalIdeal O := by
    rw [← IsLocalRing.residue_eq_zero_iff, RingHom.map_det]
    apply Matrix.det_zero_of_column_eq (i := e.symm τ) (j := e.symm τ')
      (fun h => hττ (e.symm.injective h))
    intro k
    show residue O (F (e (e.symm τ)) (RingOfIntegers.basis E k)) =
      residue O (F (e (e.symm τ')) (RingOfIntegers.basis E k))
    simp only [Equiv.apply_symm_apply]
    have a1 : F τ (RingOfIntegers.basis E k) = σ (RingOfIntegers.basis E k) :=
      hinj (by rw [hF, hτ])
    have a2 : F τ' (RingOfIntegers.basis E k) = σ' (RingOfIntegers.basis E k) :=
      hinj (by rw [hF, hτ'])
    rw [a1, a2, ← sub_eq_zero, ← map_sub, IsLocalRing.residue_eq_zero_iff]
    exact hcong _
  have hdm : ((NumberField.discr E : ℤ) : O) ∈ maximalIdeal O := by
    rw [hdisc]
    exact Ideal.pow_mem_of_mem _ hdet 2 (by norm_num)
  have hpm : (p : O) ∈ maximalIdeal O := hpu
  have hcop : IsCoprime (p : ℤ) (NumberField.discr E) :=
    (Nat.prime_iff_prime_int.mp hp).irreducible.coprime_iff_not_dvd.mpr hd
  obtain ⟨a, b, hab⟩ := hcop
  have h1 : (1 : O) ∈ maximalIdeal O := by
    have := congrArg (Int.cast : ℤ → O) hab
    push_cast at this
    rw [← this]
    exact Ideal.add_mem _ (Ideal.mul_mem_left _ _ hpm) (Ideal.mul_mem_left _ _ hdm)
  exact (maximalIdeal.isMaximal O).ne_top ((Ideal.eq_top_iff_one _).mpr h1)

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.EqMvExpOfAdditive
section
open scoped BigOperators TensorProduct
open NumberField IsLocalRing Formalism.IncomingBounds Formalism.L2.FormalSeriesBounds Formalism.L2.Pj GlobalTheory.RowLaw ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ
open ReciprocityTheory.ChartRestriction.G.Pdiv.ChartF ReciprocityTheory.ChartRestriction.G.Pdiv.AvDefs

namespace GlobalTheory.AddChar


open MvPowerSeries in
theorem subst_zero_eq {C : Type} [Field C] {κ τ : Type} [Fintype κ] (F : MvPowerSeries κ C) :
    MvPowerSeries.subst (fun _ : κ => (0 : MvPowerSeries τ C)) F = MvPowerSeries.C (constantCoeff F) := by
  classical
  have hs : HasSubst (fun _ : κ => (0 : MvPowerSeries τ C)) :=
    hasSubst_of_constantCoeff_zero (by simp)
  ext m
  rw [coeff_subst hs, finsum_eq_single _ 0]
  · simp [coeff_one, coeff_C]
  · intro d hd
    obtain ⟨w, hw⟩ := Finsupp.ne_iff.1 hd
    have : (d.prod fun s e => (0 : MvPowerSeries τ C) ^ e) = 0 := by
      refine Finset.prod_eq_zero (i := w) (by simpa using hw) ?_
      exact zero_pow (by simpa using hw)
    simp [this]


open MvPowerSeries in
theorem eq_mvExp_of_additive : ∀ (C : Type) [Field C] [CharZero C] (κ : Type) [Fintype κ] (U : MvPowerSeries κ C), MvPowerSeries.constantCoeff U = 1 → MvPowerSeries.subst (fun i : κ => (MvPowerSeries.X ((0 : Fin 2), i) + MvPowerSeries.X ((1 : Fin 2), i) : MvPowerSeries (Fin 2 × κ) C)) U = MvPowerSeries.subst (fun i : κ => (MvPowerSeries.X ((0 : Fin 2), i) : MvPowerSeries (Fin 2 × κ) C)) U * MvPowerSeries.subst (fun i : κ => (MvPowerSeries.X ((1 : Fin 2), i) : MvPowerSeries (Fin 2 × κ) C)) U → U = mvExp (∑ i : κ, MvPowerSeries.coeff (Finsupp.single i 1) U • (MvPowerSeries.X i : MvPowerSeries κ C)) := by
  classical
  intro C _ _ κ _ U h0 h
  have hA : HasSubst (fun i : κ => (X ((0 : Fin 2), i) + X ((1 : Fin 2), i) : MvPowerSeries (Fin 2 × κ) C)) :=
    hasSubst_of_constantCoeff_zero (by simp)
  have hB : ∀ a : Fin 2, HasSubst (fun i : κ => (X (a, i) : MvPowerSeries (Fin 2 × κ) C)) := fun a =>
    hasSubst_of_constantCoeff_zero (by simp)
  let p : Fin 2 × κ → MvPowerSeries κ C := fun x => if x.1 = 0 then X x.2 else 0
  have hp : HasSubst p := hasSubst_of_constantCoeff_zero (by
    intro x; simp only [p]; split_ifs <;> simp)
  have hE : constantCoeff U = 1 ∧ ∀ w, pderiv w U = coeff (Finsupp.single w 1) U • U := by
    refine ⟨h0, fun w => ?_⟩
    have h1 := congrArg (pderiv (R := C) ((1 : Fin 2), w)) h
    rw [Derivation.leibniz, Formalism.G.LogCR.pderiv_subst (by simp), Formalism.G.LogCR.pderiv_subst (by simp),
      Formalism.G.LogCR.pderiv_subst (by simp), Finset.sum_eq_single w, Finset.sum_eq_single w,
      Finset.sum_eq_zero] at h1
    · simp [pderiv_X, Pi.single_apply] at h1
      have h2 := congrArg (subst p) h1
      rw [subst_mul hp, subst_comp_subst_apply hA hp, subst_comp_subst_apply (hB 0) hp,
        subst_comp_subst_apply (hB 1) hp] at h2
      simp only [subst_add hp, subst_X hp, p] at h2
      simp [subst_zero_eq] at h2
      have hs : ∀ F : MvPowerSeries κ C, subst (fun s : κ => (X s : MvPowerSeries κ C)) F = F :=
        fun F => congrFun subst_self F
      rw [hs, hs] at h2
      rw [h2, ← coeff_zero_eq_constantCoeff_apply, coeff_pderiv, smul_eq_C_mul, mul_comm]
      simp
    all_goals simp +contextual [pderiv_X, Pi.single_apply]
  have hcoeff : ∀ (F : MvPowerSeries κ C),
      (constantCoeff F = 1 ∧ ∀ w, pderiv w F = coeff (Finsupp.single w 1) U • F) →
      ∀ (n : ℕ) (m : κ →₀ ℕ), m.degree = n →
      (mfact m : C) * coeff m F = m.prod (fun s k => coeff (Finsupp.single s 1) U ^ k) := by
    intro F h
    intro n
    induction n with
    | zero =>
      intro m hm
      rw [Finsupp.degree_eq_zero_iff] at hm
      subst hm
      simp [mfact, h.1]
    | succ n ih =>
      intro m hm
      have hne : m ≠ 0 := by rintro rfl; simp at hm
      obtain ⟨w, hw⟩ := Finsupp.ne_iff.1 hne
      obtain ⟨m', rfl⟩ : ∃ m', m = m' + Finsupp.single w 1 := by
        refine ⟨m - Finsupp.single w 1, ?_⟩
        rw [tsub_add_cancel_of_le]
        rw [Finsupp.single_le_iff]
        simp at hw; omega
      have hd : m'.degree = n := by
        rw [map_add (f := _), Finsupp.degree_single] at hm; omega
      have h1 := congrArg (MvPowerSeries.coeff m') (h.2 w)
      rw [coeff_pderiv, coeff_smul] at h1
      have h2 : mfact (m' + Finsupp.single w 1) = (m' w + 1) * mfact m' := by
        unfold mfact
        have e1 := Finsupp.mul_prod_erase' (m' + Finsupp.single w 1) w (fun _ k => k.factorial) (by simp)
        have e2 := Finsupp.mul_prod_erase' m' w (fun _ k => k.factorial) (by simp)
        rw [← e1, ← e2, Finsupp.erase_add, Finsupp.erase_single, add_zero]
        simp [Nat.factorial_succ, mul_assoc]
      rw [Finsupp.prod_add_index' (by simp) (fun _ _ _ => pow_add _ _ _), ← ih m' hd, h2,
        Finsupp.prod_single_index (by simp)]
      push_cast
      linear_combination (mfact m' : C) * h1
  have hF : constantCoeff (mvExp (∑ i : κ, coeff (Finsupp.single i 1) U • (X i : MvPowerSeries κ C))) = 1 ∧
      ∀ w, pderiv w (mvExp (∑ i : κ, coeff (Finsupp.single i 1) U • (X i : MvPowerSeries κ C))) =
        coeff (Finsupp.single w 1) U • mvExp (∑ i : κ, coeff (Finsupp.single i 1) U • (X i : MvPowerSeries κ C)) := by
    constructor
    · rw [← coeff_zero_eq_constantCoeff_apply, (show ∀ (h : MvPowerSeries κ C) (m : κ →₀ ℕ), coeff m (mvExp h) = ∑ k ∈ Finset.range (m.degree + 1), coeff m (h ^ k) / (k.factorial : C) from fun _ _ => rfl)]; simp
    · intro w
      ext m
      have hL : pderiv w (∑ x, (coeff (Finsupp.single x 1) U) • (X x : MvPowerSeries κ C)) = MvPowerSeries.C ((coeff (Finsupp.single w 1) U)) := by
        set_option synthInstance.maxHeartbeats 100000 in
          rw [map_sum, Finset.sum_eq_single w]
        · simp [smul_eq_C_mul]
        · intro b _ hb; simp [pderiv_X_of_ne hb]
        · simp
      rw [coeff_pderiv, coeff_smul, (show ∀ (h : MvPowerSeries κ C) (m : κ →₀ ℕ), coeff m (mvExp h) = ∑ k ∈ Finset.range (m.degree + 1), coeff m (h ^ k) / (k.factorial : C) from fun _ _ => rfl), (show ∀ (h : MvPowerSeries κ C) (m : κ →₀ ℕ), coeff m (mvExp h) = ∑ k ∈ Finset.range (m.degree + 1), coeff m (h ^ k) / (k.factorial : C) from fun _ _ => rfl), map_add (f := _), Finsupp.degree_single,
        Finset.sum_range_succ', Finset.mul_sum, add_mul, Finset.sum_mul]
      have h0 : MvPowerSeries.coeff (m + Finsupp.single w 1)
          ((∑ x, (coeff (Finsupp.single x 1) U) • (X x : MvPowerSeries κ C)) ^ 0) = 0 := by
        rw [pow_zero, coeff_one, if_neg]
        intro h
        have := DFunLike.congr_fun h w
        simp at this
      rw [h0, zero_div, zero_mul, add_zero]
      refine Finset.sum_congr rfl fun k _ => ?_
      have h1 := coeff_pderiv (i := w) ((∑ x, (coeff (Finsupp.single x 1) U) • (X x : MvPowerSeries κ C)) ^ (k + 1)) m
      rw [pderiv_pow, hL, Nat.add_sub_cancel, ← map_natCast (MvPowerSeries.C (σ := κ) (R := C)),
        coeff_mul_C, coeff_C_mul] at h1
      have hk : (k.factorial : C) ≠ 0 := by exact_mod_cast k.factorial_ne_zero
      have hk1 : ((k + 1 : ℕ) : C) ≠ 0 := by exact_mod_cast k.succ_ne_zero
      rw [div_mul_eq_mul_div, ← h1, Nat.factorial_succ]
      push_cast at hk1 ⊢
      field_simp
  ext m
  have hm : (mfact m : C) ≠ 0 := by
    rw [Nat.cast_ne_zero]
    unfold mfact
    exact Finset.prod_ne_zero_iff.2 fun _ _ => Nat.factorial_ne_zero _
  exact mul_left_cancel₀ hm ((hcoeff U hE _ m rfl).trans (hcoeff _ hF _ m rfl).symm)

end GlobalTheory.AddChar
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.EqOneOfTangentVectorEqOne
section
set_option autoImplicit false
noncomputable section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ (PS ev pt addOf)
open ReciprocityTheory.PGsh.Be2 (nEval)
open GlobalTheory.UU (CubWeil)
attribute [local instance] Over.cartesianMonoidalCategory
open Formalism.L2.FormalSeriesBounds IsLocalRing GlobalTheory.AlphaPair
open scoped CategoryTheory.Obj

namespace GlobalTheory.AlphaPair

section Alg

open Polynomial

variable {Ω : Type} [Field Ω] {p : ℕ} [Fact p.Prime]

theorem root_pow_eq_zero : AdjoinRoot.root ((X : Polynomial Ω) ^ p) ^ p = 0 := by
  rw [← AdjoinRoot.mk_X, ← map_pow, AdjoinRoot.mk_self]

def truncLift {A : Type} [CommRing A] [Algebra Ω A] (a : A) (ha : a ^ p = 0) :
    AdjoinRoot ((X : Polynomial Ω) ^ p) →ₐ[Ω] A :=
  Ideal.Quotient.liftₐ _ (aeval a) (by
    intro f hf
    obtain ⟨h, rfl⟩ := Ideal.mem_span_singleton.1 hf
    simp [ha])

theorem truncLift_mk {A : Type} [CommRing A] [Algebra Ω A] (a : A) (ha : a ^ p = 0) (f : Polynomial Ω) :
    truncLift a ha (AdjoinRoot.mk _ f) = aeval a f := rfl

theorem truncLift_root {A : Type} [CommRing A] [Algebra Ω A] (a : A) (ha : a ^ p = 0) :
    truncLift (Ω := Ω) a ha (AdjoinRoot.root _) = a := by
  rw [← AdjoinRoot.mk_X, truncLift_mk, aeval_X]

theorem isLocalRing_trunc : IsLocalRing (AdjoinRoot ((X : Polynomial Ω) ^ p)) := by
  have hp : p ≠ 0 := (Fact.out : p.Prime).ne_zero
  haveI : Nontrivial (AdjoinRoot ((X : Polynomial Ω) ^ p)) :=
    (truncLift (0 : Ω) (zero_pow hp)).toRingHom.domain_nontrivial
  refine IsLocalRing.of_isUnit_or_isUnit_one_sub_self fun a => ?_
  obtain ⟨f, rfl⟩ := AdjoinRoot.mk_surjective a
  have hn : IsNilpotent (AdjoinRoot.mk ((X : Polynomial Ω) ^ p) (X * f.divX)) := by
    refine ⟨p, ?_⟩
    rw [map_mul, mul_pow, AdjoinRoot.mk_X, root_pow_eq_zero, zero_mul]
  rw [← X_mul_divX_add f, map_add (f := _)]
  by_cases hc : f.coeff 0 = 0
  · right
    rw [hc, C_0, map_zero, add_zero]
    exact hn.isUnit_one_sub
  · left
    exact hn.isUnit_add_right_of_commute ((isUnit_C.2 (Ne.isUnit hc)).map _) (Commute.all _ _)

theorem mk_eq_const_of_derivative [CharP Ω p] (f : Polynomial Ω)
    (h : AdjoinRoot.mk ((X : Polynomial Ω) ^ p) (derivative f) = 0) :
    AdjoinRoot.mk ((X : Polynomial Ω) ^ p) f = algebraMap Ω _ (aeval (0 : Ω) f) := by
  rw [AdjoinRoot.mk_eq_zero, X_pow_dvd_iff] at h
  change _ = AdjoinRoot.mk _ (C _)
  rw [AdjoinRoot.mk_eq_mk, X_pow_dvd_iff]
  intro d hd
  rcases d with _ | d
  · simp [coeff_zero_eq_eval_zero]
  · have h1 := h d (by omega)
    rw [coeff_derivative] at h1
    have h2 : ((d : Ω) + 1) ≠ 0 := by
      intro h0
      have : ((d + 1 : ℕ) : Ω) = 0 := by exact_mod_cast h0
      exact absurd (Nat.le_of_dvd (Nat.succ_pos d) ((CharP.cast_eq_zero_iff Ω p _).1 this)) (by omega)
    simpa [coeff_C] using (mul_eq_zero.1 h1).resolve_right h2

end Alg

theorem spMap_comp_eq_of_equalizer {R B : Type} [CommRing R] [CommRing B] [IsLocalRing R] {Y : Scheme.{0}}
    (y : Sp R ⟶ Y) (d₁ d₀ : R →+* B) (e : R →+* R) (he : ∀ x, d₁ x = d₀ x → e x = x)
    (h : spMap d₁ ≫ y = spMap d₀ ≫ y) : spMap e ≫ y = y := by
  obtain ⟨V, hV, hz, -⟩ := exists_isAffineOpen_mem_and_subset (U := ⊤)
    (x := y (IsLocalRing.closedPoint R)) trivial
  have hr : Set.range y ⊆ Set.range hV.fromSpec := by
    rw [hV.range_fromSpec]
    rintro _ ⟨x, rfl⟩
    have : y ⁻¹ᵁ V = ⊤ := (IsLocalRing.closed_point_mem_iff).mp hz
    exact (this.ge (Set.mem_univ x) : x ∈ y ⁻¹ᵁ V)
  obtain ⟨φ, rfl⟩ : ∃ φ : Γ(Y, V) ⟶ CommRingCat.of R, Spec.map φ ≫ hV.fromSpec = y :=
    ⟨Spec.preimage (IsOpenImmersion.lift hV.fromSpec y hr), by rw [Spec.map_preimage, IsOpenImmersion.lift_fac]⟩
  rw [← Category.assoc, ← Category.assoc, cancel_mono, ← Spec.map_comp, ← Spec.map_comp] at h
  have h' := Spec.map_injective h
  rw [← Category.assoc, ← Spec.map_comp]
  congr 2
  ext a
  exact he _ (congrArg (fun k => k.hom a) h')

theorem IsAlpha.eq_one_of_tangent (Ω : Type) [Field Ω] (p : ℕ) [Fact p.Prime] [CharP Ω p] (S : Scheme.{0})
    (s : Sp Ω ⟶ S) (G : Over S) [GrpObj G] (g : Fam s G) (hg : IsAlpha p s G g)
    (h1 : g (DualNumber Ω) DualNumber.eps = 1) (A : Type) [CommRing A] [Algebra Ω A] (a : A) (ha : a ^ p = 0) :
    g A a = 1 := by
  have hp : p.Prime := Fact.out
  let R := AdjoinRoot ((Polynomial.X : Polynomial Ω) ^ p)
  haveI : IsLocalRing R := isLocalRing_trunc
  let t : R := AdjoinRoot.root _
  have ht : t ^ p = 0 := root_pow_eq_zero
  have heps : ∀ (B : Type) [CommRing B], (DualNumber.eps : DualNumber B) ^ p = 0 := fun B _ =>
    pow_eq_zero_of_le hp.two_le (by rw [sq, DualNumber.eps_mul_eps])
  haveI : CharP R p := charP_of_injective_algebraMap (algebraMap Ω R).injective p
  haveI : CharP (DualNumber R) p := charP_of_injective_algebraMap (algebraMap Ω (DualNumber R)).injective p
  let t' : DualNumber R := TrivSqZeroExt.inl t
  have ht' : t' ^ p = 0 := by
    change TrivSqZeroExt.inlAlgHom Ω R R t ^ p = 0
    rw [← map_pow, ht, map_zero]
  have hs : (t' + DualNumber.eps) ^ p = 0 := by rw [add_pow_char, ht', heps, add_zero]
  have he : g (DualNumber R) DualNumber.eps = 1 := by
    let j : DualNumber Ω →ₐ[Ω] DualNumber R :=
      DualNumber.lift ⟨(Algebra.ofId _ _, DualNumber.eps), DualNumber.eps_mul_eps, fun _ => Commute.all _ _⟩
    have hj : j DualNumber.eps = DualNumber.eps := DualNumber.lift_apply_eps _
    rw [← hj, hg.1 _ _ j _ (heps Ω), h1, MonObj.comp_one]
  have key : homAt s (truncLift _ hs) ≫ g R t = homAt s (truncLift _ ht') ≫ g R t := by
    rw [← hg.1 _ _ _ _ ht, ← hg.1 _ _ _ _ ht, truncLift_root, truncLift_root, hg.2 _ _ _ ht' (heps R), he, _root_.mul_one]
  let e : R →ₐ[Ω] R := truncLift 0 (zero_pow hp.ne_zero)
  have hr : homAt s e ≫ g R t = g R t := by
    apply Over.OverMorphism.ext
    refine spMap_comp_eq_of_equalizer (g R t).left (truncLift _ hs).toRingHom (truncLift _ ht').toRingHom
      e.toRingHom ?_ (congrArg (·.left) key)
    intro x hx
    obtain ⟨f, rfl⟩ := AdjoinRoot.mk_surjective x
    change Polynomial.aeval (t' + DualNumber.eps) f = Polynomial.aeval t' f at hx
    rw [Polynomial.aeval_add_of_sq_eq_zero _ _ _ (by rw [sq, DualNumber.eps_mul_eps]), add_eq_left] at hx
    have h3 : Polynomial.aeval t' (Polynomial.derivative f) =
        TrivSqZeroExt.inl (Polynomial.aeval t (Polynomial.derivative f)) :=
      Polynomial.aeval_algHom_apply (TrivSqZeroExt.inlAlgHom Ω R R) t _
    have h4 := congrArg TrivSqZeroExt.snd hx
    rw [h3] at h4
    have h5 : Polynomial.aeval t (Polynomial.derivative f) = 0 := by simpa using h4
    rw [AdjoinRoot.aeval_eq] at h5
    rw [mk_eq_const_of_derivative f h5]
    exact e.commutes _
  have h0 : g R t = 1 := by
    rw [← hr, ← hg.1 _ _ _ _ ht, truncLift_root, hg.zero hp.ne_zero]
  have := hg.1 _ _ (truncLift a ha) t ht
  rwa [truncLift_root, h0, MonObj.comp_one] at this

end GlobalTheory.AlphaPair
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.ExistsAlgClosedResidueFieldValuedField
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ (PS ev pt addOf)
open ReciprocityTheory.PGsh.Be2 (nEval)
open GlobalTheory.UU (CubWeil)
attribute [local instance] Over.cartesianMonoidalCategory
open Formalism.L2.FormalSeriesBounds IsLocalRing GlobalTheory.AlphaPair
open scoped CategoryTheory.Obj

namespace GlobalTheory.AlphaPair.ResField

variable {C : Type} [Field C] (V : VF C)

theorem nonneg (x : V.RR) : 0 ≤ V.v (x : C) := by
  have h : ((0 : ℝ) : WithTop ℝ) ≤ V.v (x : C) := x.2
  simpa using h

def mm : Ideal V.RR where
  carrier := {x | V.MM (x : C)}
  add_mem' := fun {x y} hx hy => V.v.map_lt_add hx hy
  zero_mem' := by simp [VF.MM]
  smul_mem' := fun c x hx => by
    show 0 < V.v ((c : C) * x)
    rw [V.v.map_mul]
    exact lt_of_lt_of_le hx (le_add_of_nonneg_left (nonneg V c))

theorem mm_isMaximal : (mm V).IsMaximal := by
  rw [Ideal.isMaximal_iff]
  refine ⟨fun h => ?_, fun J x _ hx hxJ => ?_⟩
  · have h1 : 0 < V.v ((1 : V.RR) : C) := h
    simp at h1
  · have hx' : ¬ 0 < V.v (x : C) := hx
    have hx0 : V.v (x : C) = 0 := le_antisymm (not_lt.mp hx') (nonneg V x)
    have hne : (x : C) ≠ 0 := by
      intro h
      rw [h, AddValuation.map_zero] at hx0
      exact WithTop.top_ne_zero hx0
    have hinv : ((0 : ℝ) : WithTop ℝ) ≤ V.v ((x : C)⁻¹) := by
      rw [AddValuation.map_inv, hx0]
      simp
    let y : V.RR := ⟨(x : C)⁻¹, hinv⟩
    have hyx : y * x = 1 := Subtype.ext (by simp [y, hne])
    rw [← hyx]
    exact J.mul_mem_left y hxJ

theorem integers : (AddValuation.toValuation V.v).Integers V.RR :=
  Valuation.integer.integers (AddValuation.toValuation V.v)

theorem isAlgClosed_of_surjective [IsAlgClosed C] {Ω : Type} [Field Ω] (ρ : V.RR →+* Ω)
    (hρ : Function.Surjective ρ) : IsAlgClosed Ω := by
  refine IsAlgClosed.of_exists_root Ω fun p hp hirr => ?_
  obtain ⟨q, hqmap, hqdeg, hqmon⟩ :=
    Polynomial.lifts_and_degree_eq_and_monic ((Polynomial.mem_lifts p).2 (Polynomial.map_surjective ρ hρ p)) hp
  have hdeg : (q.map (algebraMap V.RR C)).degree ≠ 0 := by
    rw [Polynomial.degree_map_eq_of_injective (integers V).hom_inj, hqdeg]
    exact (Polynomial.degree_pos_of_irreducible hirr).ne'
  obtain ⟨z, hz⟩ := IsAlgClosed.exists_root _ hdeg
  rw [Polynomial.IsRoot, Polynomial.eval_map] at hz
  have hint : IsIntegral V.RR z := ⟨q, hqmon, hz⟩
  obtain ⟨y, rfl⟩ := (integers V).exists_of_le_one ((integers V).mem_of_integral hint)
  rw [Polynomial.eval₂_at_apply] at hz
  have hy : q.eval y = 0 := (integers V).hom_inj (by rw [hz, map_zero])
  refine ⟨ρ y, ?_⟩
  rw [← hqmap, Polynomial.eval_map, Polynomial.eval₂_at_apply, hy, map_zero]

theorem exists_residueField : ∀ (C : Type) [Field C] (V : VF C), IsAlgClosed C → ∃ (Ω : Type) (_ : Field Ω) (_ : IsAlgClosed Ω) (_ : CharP Ω V.l) (ρ : V.RR →+* Ω), ∀ x : V.RR, ρ x = 0 ↔ V.MM (x : C) := by
  intro C _ V _
  have := mm_isMaximal V
  let _ : Field (V.RR ⧸ mm V) := Ideal.Quotient.field (mm V)
  have hl : ((V.l : ℕ) : V.RR ⧸ mm V) = 0 := by
    rw [← map_natCast (Ideal.Quotient.mk (mm V)), Ideal.Quotient.eq_zero_iff_mem]
    show 0 < V.v (((V.l : ℕ) : V.RR) : C)
    have hc : (((V.l : ℕ) : V.RR) : C) = ((V.l : ℕ) : C) := by simp
    rw [hc, V.v_l]
    exact zero_lt_one
  have : CharP (V.RR ⧸ mm V) V.l := (CharP.charP_iff_prime_eq_zero V.l_prime).2 hl
  exact ⟨V.RR ⧸ mm V, inferInstance, isAlgClosed_of_surjective V _ Ideal.Quotient.mk_surjective,
    inferInstance, Ideal.Quotient.mk (mm V), fun x => Ideal.Quotient.eq_zero_iff_mem⟩

end GlobalTheory.AlphaPair.ResField
end

