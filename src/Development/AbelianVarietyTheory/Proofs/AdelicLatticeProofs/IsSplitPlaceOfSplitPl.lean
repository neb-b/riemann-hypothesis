module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.AdelicHermitianForms.Bundle0002
public import Development.AbelianVarietyTheory.BlockTheory.AdelicCMFields.SupportedAtSplit
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0021

@[expose] public section

noncomputable section

namespace GlobalTheory.UnRep.Compare

open NumberField IsDedekindDomain GlobalTheory.AdLat GlobalTheory.UnRep GlobalTheory.IndefiniteRowSideFullHecke.SplitPlaceUnitaryEvaluation
open scoped TensorProduct Matrix

variable {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E]

theorem evalAt_apply (v : HeightOneSpectrum (𝓞 F)) (a : FiniteAdeleRing (𝓞 F) F) : evalAt v a = a v := rfl

theorem loc_tmul (v : HeightOneSpectrum (𝓞 F)) (a : FiniteAdeleRing (𝓞 F) F) (x : E) :
    loc E v (a ⊗ₜ[F] x) = a v ⊗ₜ[F] x := rfl

theorem eq_zero_of_loc {x : RA F E} (h : ∀ v, loc E v x = 0) : x = 0 := by
  let b := Module.Basis.ofVectorSpace F E
  have key : ∀ (v : HeightOneSpectrum (𝓞 F)) (i) (y : RA F E),
      (Algebra.TensorProduct.basis (FiniteAdeleRing (𝓞 F) F) b).repr y i v =
        (Algebra.TensorProduct.basis (v.adicCompletion F) b).repr (loc E v y) i := by
    intro v i y
    rw [← evalAt_apply]
    induction y using TensorProduct.induction_on with
    | zero => simp
    | tmul a e =>
      rw [loc_tmul, Algebra.TensorProduct.basis_repr_tmul, Algebra.TensorProduct.basis_repr_tmul]
      simp only [Finsupp.smul_apply, Finsupp.mapRange_apply, smul_eq_mul, map_mul, AlgHom.commutes,
        evalAt_apply v a]
    | add s t hs ht => simp only [map_add (f := _), Finsupp.add_apply, hs, ht]
  apply (Algebra.TensorProduct.basis (FiniteAdeleRing (𝓞 F) F) b).repr.injective
  ext i : 1
  refine DFunLike.ext _ _ fun v => ?_
  rw [key, h, map_zero, map_zero]
  rfl

theorem eq_of_loc {x y : RA F E} (h : ∀ v, loc E v x = loc E v y) : x = y :=
  sub_eq_zero.1 (eq_zero_of_loc fun v => by rw [map_sub, h, sub_self])


open Classical in
def ind (S : Set (HeightOneSpectrum (𝓞 F))) : FiniteAdeleRing (𝓞 F) F :=
  ⟨fun w => if w ∈ S then 1 else 0, Filter.Eventually.of_forall fun w => by
    by_cases h : w ∈ S
    · simp only [if_pos h]; exact one_mem _
    · simp only [if_neg h]; exact zero_mem _⟩

theorem ind_pos {S : Set (HeightOneSpectrum (𝓞 F))} {w} (h : w ∈ S) : ind S w = 1 := if_pos h

theorem ind_neg {S : Set (HeightOneSpectrum (𝓞 F))} {w} (h : w ∉ S) : ind S w = 0 := if_neg h

theorem loc_ind_pos {S : Set (HeightOneSpectrum (𝓞 F))} {w} (h : w ∈ S) :
    loc E w (ind S ⊗ₜ[F] (1 : E)) = 1 := by rw [loc_tmul, ind_pos h]; rfl

theorem isSplitPlace_of_splitPl (c : E ≃ₐ[F] E) {v : HeightOneSpectrum (𝓞 F)} (h : SplitPl c v) :
    IsSplitPlace E v := by
  obtain ⟨P, hP, hPv, a, ha, b, hb, hbP⟩ := h
  let σ : 𝓞 E ≃+* 𝓞 E := RingOfIntegers.mapRingEquiv c.toRingEquiv
  have hσ : ∀ x : 𝓞 E, ((σ x : 𝓞 E) : E) = c x := fun _ => rfl
  refine ⟨P, P.comap σ, fun h => hbP ?_, hP, inferInstance, hPv, ?_⟩
  · rw [h, Ideal.mem_comap] at ha
    rwa [show b = σ a from Subtype.ext hb]
  · rw [← hPv]
    ext x
    have : σ (algebraMap (𝓞 F) (𝓞 E) x) = algebraMap (𝓞 F) (𝓞 E) x :=
      Subtype.ext (c.commutes (x : F))
    simp only [Ideal.mem_comap, this]

theorem aut_eq (c : E ≃ₐ[F] E) (h2 : Module.finrank F E = 2) (hc : c ≠ 1) (σ : E ≃ₐ[F] E) :
    σ = 1 ∨ σ = c := by
  haveI : Algebra.IsQuadraticExtension F E := ⟨h2⟩
  have hcard : Nat.card (E ≃ₐ[F] E) = 2 := by rw [IsGalois.card_aut_eq_finrank, h2]
  obtain ⟨y, -, hy⟩ := (Nat.card_eq_two_iff' (1 : E ≃ₐ[F] E)).1 hcard
  by_cases h : σ = 1
  · exact Or.inl h
  · exact Or.inr ((hy σ h).trans (hy c hc).symm)

theorem conj_conj (c : E ≃ₐ[F] E) (h2 : Module.finrank F E = 2) (hc : c ≠ 1) (x : E) : c (c x) = x := by
  rcases aut_eq c h2 hc (c * c) with h | h
  · exact DFunLike.congr_fun h x
  · exact absurd (mul_eq_left.1 h) hc

theorem moved_of_not_le (c : E ≃ₐ[F] E) (h2 : Module.finrank F E = 2) (hc : c ≠ 1)
    {P Q : Ideal (𝓞 E)} (hQ : Q.IsPrime)
    (h : P.comap (algebraMap (𝓞 F) (𝓞 E)) = Q.comap (algebraMap (𝓞 F) (𝓞 E))) (hPQ : ¬ P ≤ Q) :
    Moved c Q := by
  haveI : Algebra.IsQuadraticExtension F E := ⟨h2⟩
  obtain ⟨a, haP, haQ⟩ := Set.not_subset.1 hPQ
  let σ : 𝓞 E ≃+* 𝓞 E := RingOfIntegers.mapRingEquiv c.toRingEquiv
  have hσ : ∀ x : 𝓞 E, ((σ x : 𝓞 E) : E) = c x := fun _ => rfl
  obtain ⟨m, hm⟩ : ((a * σ a : 𝓞 E) : E) ∈ Set.range (algebraMap F E) := by
    rw [IsGalois.mem_range_algebraMap_iff_fixed]
    intro f
    rcases aut_eq c h2 hc f with rfl | rfl
    · rfl
    · change f ((a : E) * f a) = (a : E) * f a
      rw [map_mul, conj_conj f h2 hc, mul_comm]
  have hint : IsIntegral ℤ m := by
    rw [← isIntegral_algebraMap_iff (B := E) , hm]
    exact (a * σ a).2
  obtain ⟨m', hm'⟩ : ∃ m' : 𝓞 F, algebraMap (𝓞 F) (𝓞 E) m' = a * σ a := ⟨⟨m, hint⟩, Subtype.ext hm⟩
  have h1 : a * σ a ∈ Q := by
    rw [← hm', ← Ideal.mem_comap, ← h, Ideal.mem_comap, hm']
    exact P.mul_mem_right _ haP
  exact ⟨σ a, (hQ.mem_or_mem h1).resolve_left haQ, a, (conj_conj c h2 hc _).symm, haQ⟩

theorem splitPl_iff (c : E ≃ₐ[F] E) (h2 : Module.finrank F E = 2) (hc : c ≠ 1)
    (v : HeightOneSpectrum (𝓞 F)) : SplitPl c v ↔ IsSplitPlace E v := by
  refine ⟨isSplitPlace_of_splitPl c, ?_⟩
  rintro ⟨w, w', hne, hw, hw', h, h'⟩
  by_cases hle : w ≤ w'
  · exact ⟨w, hw, h, moved_of_not_le c h2 hc hw (h'.trans h.symm) fun h => hne (le_antisymm hle h)⟩
  · exact ⟨w', hw', h', moved_of_not_le c h2 hc hw' (h.trans h'.symm) hle⟩

theorem support_iff (p : HeightOneSpectrum (𝓞 F) → Prop) {n : ℕ} (h : Matrix (Fin n) (Fin n) (RA F E)) :
    (∃ e : FiniteAdeleRing (𝓞 F) F, e * e = e ∧ {v | e v ≠ 0}.Finite ∧
      (∀ v, e v ≠ 0 → p v) ∧ (e ⊗ₜ[F] (1 : E)) • (h - 1) = h - 1) ↔
    ∃ T : Finset (HeightOneSpectrum (𝓞 F)), (∀ v ∈ T, p v) ∧ ∀ v ∉ T, h.map (loc E v) = 1 := by
  have hone : ∀ v : HeightOneSpectrum (𝓞 F), h.map (loc E v) = 1 ↔ ∀ i j, loc E v ((h - 1) i j) = 0 := by
    intro v
    rw [← Matrix.map_one (loc E v) (map_zero _) (map_one _), ← Matrix.ext_iff]
    simp only [Matrix.map_apply, Matrix.sub_apply, map_sub, sub_eq_zero]
  constructor
  · rintro ⟨e, -, hfin, hp, he⟩
    refine ⟨hfin.toFinset, fun v hv => hp v (hfin.mem_toFinset.1 hv), fun v hv => (hone v).2 fun i j => ?_⟩
    have h0 : e v = 0 := by
      by_contra h0
      exact hv (hfin.mem_toFinset.2 h0)
    rw [← he, Matrix.smul_apply, smul_eq_mul, map_mul, loc_tmul, h0, TensorProduct.zero_tmul, zero_mul]
  · rintro ⟨T, hp, hT⟩
    have hs : ∀ v, ind (T : Set (HeightOneSpectrum (𝓞 F))) v ≠ 0 → v ∈ T := fun v hv => by
      by_contra h0
      exact hv (ind_neg h0)
    refine ⟨ind T, ?_, T.finite_toSet.subset hs, fun v hv => hp v (hs v hv), ?_⟩
    · refine DFunLike.ext _ _ fun v => ?_
      change ind _ v * ind _ v = ind _ v
      by_cases hv : v ∈ (T : Set (HeightOneSpectrum (𝓞 F)))
      · rw [ind_pos hv, one_mul]
      · rw [ind_neg hv, zero_mul]
    · ext i j
      refine eq_of_loc fun v => ?_
      rw [Matrix.smul_apply, smul_eq_mul, map_mul]
      by_cases hv : v ∈ (T : Set (HeightOneSpectrum (𝓞 F)))
      · rw [loc_ind_pos hv, one_mul]
      · rw [(hone v).1 (hT v hv), mul_zero]


end GlobalTheory.UnRep.Compare
