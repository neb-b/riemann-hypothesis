module

public import Mathlib
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.BaseChangeDefiniteUnitary
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0007

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ClozelCohomology.ContinuousEntryPairings.ExistsConjPolynomialDefiniteUnitaryRational
section
open NumberField IsDedekindDomain Matrix GlobalTheory.CuspRep GlobalTheory.UnitaryBC

namespace GlobalTheory.UnitaryBC

private theorem polyConj_coord_pInf {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (τ : E →+* ℂ) (x : E) :
    coord τ (pInf E (algebraMap E (Ad E) x)) = τ x := by
  have h : ∀ w : InfinitePlace E, pInf E (algebraMap E (Ad E) x) w = w.embedding x := fun w => by
    first | exact pInf_algebraMap _ _ | exact pInf_algebraMap _ _ _ | simp [pInf_algebraMap]
  unfold coord
  split_ifs with hτ
  · simp only [Pi.evalRingHom_apply, h, hτ]
  · rcases InfinitePlace.embedding_mk_eq τ with h' | h'
    · exact absurd h' hτ
    · simp [h, h']

theorem exists_cEmb_entry_eq {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ} {γ : UA E n}
    (hγ : γ ∈ ratU E n) {k : UA E n} (hk : cInf k = cInf γ) (i j : Fin n) :
    ∃ x : E, ∀ τ : E →+* ℂ, (cEmb τ k).val i j = τ x := by
  obtain ⟨γ₀, h₀⟩ := Subgroup.mem_subgroupOf.1 hγ
  refine ⟨γ₀.val i j, fun τ => ?_⟩
  have h1 : (cEmb τ k).val i j = coord τ ((cInf k).val i j) := rfl
  have h2 : (cInf γ).val i j = pInf E ((γ : GA E n).val i j) := rfl
  rw [h1, hk, h2, ← h₀]
  exact polyConj_coord_pInf τ _

theorem exists_conj_polyFun : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ) (σ : ℂ ≃+* ℂ), ∀ p ∈ Algebra.adjoin ℂ {f : infU E n → ℂ | ∃ (τ : E →+* ℂ) (i j : Fin n), f = fun x => (cEmb τ x.1).val i j}, ∃ p' ∈ Algebra.adjoin ℂ {f : infU E n → ℂ | ∃ (τ : E →+* ℂ) (i j : Fin n), f = fun x => (cEmb τ x.1).val i j}, ∀ γ ∈ ratU E n, ∀ k : infU E n, cInf k.1 = cInf γ → p' k = σ (p k) := by
  intro E _ _ _ n σ p hp
  induction hp using Algebra.adjoin_induction with
  | mem f hf =>
    obtain ⟨τ, i, j, rfl⟩ := hf
    refine ⟨_, Algebra.subset_adjoin ⟨σ.toRingHom.comp τ, i, j, rfl⟩, fun γ hγ k hk => ?_⟩
    obtain ⟨x, hx⟩ := exists_cEmb_entry_eq hγ hk i j
    simp only [hx]
    rfl
  | algebraMap c => exact ⟨_, Subalgebra.algebraMap_mem _ (σ c), fun _ _ _ _ => rfl⟩
  | add f g _ _ hf hg =>
    obtain ⟨f', hf', hf⟩ := hf
    obtain ⟨g', hg', hg⟩ := hg
    refine ⟨f' + g', add_mem hf' hg', fun γ hγ k hk => ?_⟩
    rw [Pi.add_apply, Pi.add_apply, map_add (f := _), hf γ hγ k hk, hg γ hγ k hk]
  | mul f g _ _ hf hg =>
    obtain ⟨f', hf', hf⟩ := hf
    obtain ⟨g', hg', hg⟩ := hg
    refine ⟨f' * g', mul_mem hf' hg', fun γ hγ k hk => ?_⟩
    rw [Pi.mul_apply, Pi.mul_apply, map_mul, hf γ hγ k hk, hg γ hγ k hk]

end GlobalTheory.UnitaryBC
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ClozelCohomology.ContinuousEntryPairings.UnitaryCoordinateAlgebraDense
section
open NumberField IsDedekindDomain Matrix GlobalTheory.CuspRep GlobalTheory.UnitaryBC

namespace GlobalTheory.PolyRealU

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ}

theorem continuous_entry (τ : E →+* ℂ) (i j : Fin n) :
    Continuous fun x : infU E n => (cEmb τ x.1).val i j := by
  have h1 : Continuous (coord (E := E) τ) := by
    unfold coord
    split_ifs
    · exact continuous_apply _
    · exact Complex.continuous_conj.comp (continuous_apply _)
  have h2 : Continuous (pInf E) := continuous_pi fun w =>
    ((InfinitePlace.Completion.isometryEquivComplexOfIsComplex (IsTotallyComplex.isComplex w)).continuous.comp
      (continuous_apply w)).comp continuous_fst
  have h3 : Continuous fun x : infU E n => (x.1.1.val : Matrix (Fin n) (Fin n) (Ad E)) i j :=
    (Units.continuous_val.comp (continuous_subtype_val.comp continuous_subtype_val)).matrix_elem i j
  exact h1.comp (h2.comp h3)


omit [NumberField E] [IsCMField E] in
theorem coord_star' (τ : E →+* ℂ) (z : Cinf E) : coord τ (star z) = star (coord τ z) := by
  unfold coord
  split_ifs <;> rfl

theorem coord_conj (τ : E →+* ℂ) (z : Cinf E) : coord (ComplexEmbedding.conjugate τ) z = star (coord τ z) := by
  have hne : ComplexEmbedding.conjugate τ ≠ τ := fun h =>
    (InfinitePlace.isComplex_mk_iff.1 (IsTotallyComplex.isComplex (InfinitePlace.mk τ)))
      (ComplexEmbedding.isReal_iff.2 h)
  unfold coord
  rw [InfinitePlace.mk_conjugate_eq]
  rcases InfinitePlace.embedding_mk_eq τ with h | h
  · rw [ite_eq_left h, ite_eq_right (by rw [h]; exact hne.symm)]
    rfl
  · rw [ite_eq_left h, ite_eq_right (by rw [h]; exact hne)]
    simp

theorem entry_inv (τ : E →+* ℂ) (x : UA E n) (i j : Fin n) :
    (cEmb τ x⁻¹).val i j = star ((cEmb τ x).val j i) := by
  have hx : Formalism.UG.cT (conjAd E) x.1.val * 1 * x.1.val = 1 := x.2
  rw [Matrix.mul_one] at hx
  have h1 : (x.1⁻¹).val = Formalism.UG.cT (conjAd E) x.1.val := Units.inv_eq_of_mul_eq_one_left hx
  have h2 : ∀ y, pInf E (conjAd E y) = star (pInf E y) := fun y => by
    change (infEq E).symm (infEq E _) = _
    rw [RingEquiv.symm_apply_apply]
    rfl
  change coord τ (pInf E ((x.1⁻¹).val i j)) = star (coord τ (pInf E (x.1.val j i)))
  rw [h1, ← coord_star', ← h2]
  rfl

theorem eq_of_entry {x y : infU E n} (h : ∀ τ i j, (cEmb τ x.1).val i j = (cEmb τ y.1).val i j) : x = y := by
  refine Subtype.ext (Subtype.ext (ga_ext ?_ ?_))
  · ext i j w
    have h1 : coord w.embedding (pInf E (x.1.1.val i j)) = coord w.embedding (pInf E (y.1.1.val i j)) :=
      h w.embedding i j
    unfold coord at h1
    rw [InfinitePlace.mk_embedding, ite_eq_left rfl] at h1
    exact h1
  · exact (MonoidHom.mem_ker.1 x.2).trans (MonoidHom.mem_ker.1 y.2).symm

theorem coprod_adjoin {G : Type} [Mul G] (S : Set (G → ℂ))
    (hS : ∀ p ∈ S, ∃ (m : ℕ) (a b : Fin m → G → ℂ), (∀ i, a i ∈ Algebra.adjoin ℂ S ∧ b i ∈ Algebra.adjoin ℂ S) ∧
      ∀ x k, p (x * k) = ∑ i, a i x * b i k) :
    ∀ p ∈ Algebra.adjoin ℂ S, ∃ (m : ℕ) (a b : Fin m → G → ℂ),
      (∀ i, a i ∈ Algebra.adjoin ℂ S ∧ b i ∈ Algebra.adjoin ℂ S) ∧ ∀ x k, p (x * k) = ∑ i, a i x * b i k :=
  _root_.GlobalTheory.SplittingAdditive.main S hS

theorem poly_infU : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ), (∀ p ∈ Algebra.adjoin ℂ {f : infU E n → ℂ | ∃ (τ : E →+* ℂ) (i j : Fin n), f = fun x => (cEmb τ x.1).val i j}, Continuous p) ∧ (∀ p ∈ Algebra.adjoin ℂ {f : infU E n → ℂ | ∃ (τ : E →+* ℂ) (i j : Fin n), f = fun x => (cEmb τ x.1).val i j}, star p ∈ Algebra.adjoin ℂ {f : infU E n → ℂ | ∃ (τ : E →+* ℂ) (i j : Fin n), f = fun x => (cEmb τ x.1).val i j}) ∧ (∀ x y : infU E n, x ≠ y → ∃ p ∈ Algebra.adjoin ℂ {f : infU E n → ℂ | ∃ (τ : E →+* ℂ) (i j : Fin n), f = fun x => (cEmb τ x.1).val i j}, p x ≠ p y) ∧ (∀ p ∈ Algebra.adjoin ℂ {f : infU E n → ℂ | ∃ (τ : E →+* ℂ) (i j : Fin n), f = fun x => (cEmb τ x.1).val i j}, (fun x => p x⁻¹) ∈ Algebra.adjoin ℂ {f : infU E n → ℂ | ∃ (τ : E →+* ℂ) (i j : Fin n), f = fun x => (cEmb τ x.1).val i j}) ∧ ∀ p ∈ Algebra.adjoin ℂ {f : infU E n → ℂ | ∃ (τ : E →+* ℂ) (i j : Fin n), f = fun x => (cEmb τ x.1).val i j}, ∃ (m : ℕ) (a b : Fin m → infU E n → ℂ), (∀ i, a i ∈ Algebra.adjoin ℂ {f : infU E n → ℂ | ∃ (τ : E →+* ℂ) (i j : Fin n), f = fun x => (cEmb τ x.1).val i j} ∧ b i ∈ Algebra.adjoin ℂ {f : infU E n → ℂ | ∃ (τ : E →+* ℂ) (i j : Fin n), f = fun x => (cEmb τ x.1).val i j}) ∧ ∀ x k, p (x * k) = ∑ i, a i x * b i k := by
  intro E _ _ _ n
  have hstar : ∀ (τ : E →+* ℂ) (i j : Fin n), (fun x : infU E n => star ((cEmb τ x.1).val i j)) ∈
      Algebra.adjoin ℂ {f : infU E n → ℂ | ∃ (τ : E →+* ℂ) (i j : Fin n), f = fun x => (cEmb τ x.1).val i j} :=
    fun τ i j => Algebra.subset_adjoin
      ⟨ComplexEmbedding.conjugate τ, i, j, funext fun x => (coord_conj τ _).symm⟩
  refine ⟨fun p hp => ?_, fun p hp => ?_, fun x y hxy => ?_, fun p hp => ?_, coprod_adjoin _ ?_⟩
  · induction hp using Algebra.adjoin_induction with
    | mem p hp =>
      obtain ⟨τ, i, j, rfl⟩ := hp
      exact continuous_entry τ i j
    | algebraMap c => exact continuous_const
    | add p q _ _ hp hq => exact hp.add hq
    | mul p q _ _ hp hq => exact hp.mul hq
  · induction hp using Algebra.adjoin_induction with
    | mem p hp =>
      obtain ⟨τ, i, j, rfl⟩ := hp
      exact hstar τ i j
    | algebraMap c => exact Subalgebra.algebraMap_mem _ (star c)
    | add p q _ _ hp hq => rw [star_add]; exact add_mem hp hq
    | mul p q _ _ hp hq => rw [star_mul]; exact mul_mem hq hp
  · by_contra h
    push Not at h
    exact hxy (eq_of_entry fun τ i j => h _ (Algebra.subset_adjoin ⟨τ, i, j, rfl⟩))
  · induction hp using Algebra.adjoin_induction with
    | mem p hp =>
      obtain ⟨τ, i, j, rfl⟩ := hp
      convert hstar τ j i using 2 with x
      exact entry_inv τ x.1 i j
    | algebraMap c => exact Subalgebra.algebraMap_mem _ c
    | add p q _ _ hp hq => exact add_mem hp hq
    | mul p q _ _ hp hq => exact mul_mem hp hq
  · rintro _ ⟨τ, i, j, rfl⟩
    refine ⟨n, fun l x => (cEmb τ x.1).val i l, fun l x => (cEmb τ x.1).val l j,
      fun l => ⟨Algebra.subset_adjoin ⟨τ, i, l, rfl⟩, Algebra.subset_adjoin ⟨τ, l, j, rfl⟩⟩, fun x k => ?_⟩
    change (cEmb τ (x.1 * k.1)).val i j = _
    rw [map_mul, Units.val_mul, Matrix.mul_apply]

end GlobalTheory.PolyRealU
end

