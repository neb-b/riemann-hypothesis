module

public import Mathlib
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0801
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0091
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0024
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0198
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0061
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Clauses
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0120
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0132
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0077
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0054
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0160
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0897
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsRootSelectionUnitaryRankOne
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0886
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0879
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0848

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsRationalPointPolynomialIdempotentUnitValue
section
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped Matrix TensorProduct
open Filter Topology

noncomputable section

namespace GlobalTheory.DenseAvoid

theorem finite_maximal_not_mem {F B E K : Type} [Field F] [CommRing B] [Algebra F B] [Field E] [Algebra F E]
    [FiniteDimensional F E] [CommRing K] [Algebra F K] [IsArtinianRing K]
    (ρ : B →ₐ[F] K) (hρ : Function.Surjective ρ) (f : B) (hf : f * f = f)
    (hk : ∀ x, ρ x = 0 → f * x = 0) :
    {m : Ideal (B ⊗[F] E) | m.IsMaximal ∧ algebraMap B (B ⊗[F] E) f ∉ m}.Finite := by
  classical
  let Φ : B ⊗[F] E →+* K ⊗[F] E := (Algebra.TensorProduct.map ρ (AlgHom.id F E)).toRingHom
  have hΦ : Function.Surjective Φ :=
    Algebra.TensorProduct.map_surjective ρ (AlgHom.id F E) hρ (fun y => ⟨y, rfl⟩)
  haveI : IsArtinianRing (K ⊗[F] E) := IsArtinianRing.of_finite K (K ⊗[F] E)
  refine ((IsArtinianRing.setOfPred_isMaximal_finite (K ⊗[F] E)).image (Ideal.comap Φ)).subset ?_
  rintro m ⟨hm, hfm⟩
  have h1 : 1 - algebraMap B (B ⊗[F] E) f ∈ m := by
    have h0 : algebraMap B (B ⊗[F] E) f * (1 - algebraMap B (B ⊗[F] E) f) ∈ m := by
      rw [mul_sub, mul_one, ← map_mul, hf, sub_self]; exact m.zero_mem
    exact (hm.isPrime.mem_or_mem h0).resolve_left hfm
  have hker : RingHom.ker Φ ≤ m := by
    have h := Algebra.TensorProduct.rTensor_ker (R := F) (C := E) ρ hρ
    change RingHom.ker (Algebra.TensorProduct.map ρ (AlgHom.id F E)) ≤ m
    rw [h, Ideal.map_le_iff_le_comap]
    intro x hx
    have hx' : f * x = 0 := hk x hx
    change x ⊗ₜ[F] (1 : E) ∈ m
    have e1 : algebraMap B (B ⊗[F] E) f * (x ⊗ₜ[F] (1 : E)) = 0 := by
      rw [Algebra.TensorProduct.algebraMap_apply, Algebra.algebraMap_self, RingHom.id_apply,
        Algebra.TensorProduct.tmul_mul_tmul, hx', TensorProduct.zero_tmul]
    have e2 : x ⊗ₜ[F] (1 : E) = (1 - algebraMap B (B ⊗[F] E) f) * (x ⊗ₜ[F] (1 : E)) := by
      rw [sub_mul, one_mul, e1, sub_zero]
    rw [e2]; exact m.mul_mem_right _ h1
  have hc : Ideal.comap Φ (m.map Φ) = m := by
    rw [Ideal.comap_map_of_surjective' Φ hΦ, sup_eq_left.2 hker]
  refine ⟨m.map Φ, ?_, hc⟩
  rcases Ideal.map_eq_top_or_isMaximal_of_surjective Φ hΦ hm with h | h
  · exact absurd (by rw [← hc, h, Ideal.comap_top]) hm.ne_top
  · exact h

end GlobalTheory.DenseAvoid

namespace GlobalTheory.DenseAvoid

open GlobalTheory.LocalGlobalChar

variable {F : Type} [Field F] [NumberField F]

theorem eps_eq_sum (S : Finset (HeightOneSpectrum (𝓞 F))) :
    eps S = pairA F 1 0 + ∑ v ∈ S, pairA F 0 (ind {v}) := by
  classical
  have hext : ∀ a b : AF F, fstA F a = fstA F b → sndA F a = sndA F b → a = b := fun a b h1 h2 => Prod.ext h1 h2
  refine hext _ _ ?_ (fin_ext fun u => ?_)
  set_option synthInstance.maxHeartbeats 100000 in
    · rw [map_add (f := _), map_sum]
      change (1 : Ainf F) = 1 + ∑ v ∈ S, (0 : Ainf F)
      rw [Finset.sum_const_zero, add_zero]
  set_option synthInstance.maxHeartbeats 100000 in
    · rw [map_add (f := _), map_sum, map_add (f := _), map_sum]
      change evalV F u (ind S) = evalV F u 0 + ∑ v ∈ S, evalV F u (ind {v})
      simp_rw [ev_ind, Finset.mem_singleton, map_zero, zero_add]
      rw [Finset.sum_ite_eq]

variable {E : Type} [Field E] [Algebra F E] [FiniteDimensional F E]

theorem finite_maximal_not_mem_eps (S : Finset (HeightOneSpectrum (𝓞 F))) :
    {m : Ideal (AF F ⊗[F] E) | m.IsMaximal ∧ algebraMap (AF F) (AF F ⊗[F] E) (eps S) ∉ m}.Finite := by
  classical
  haveI : IsArtinianRing (Ainf F) := inferInstanceAs (IsArtinianRing ((w : InfinitePlace F) → w.Completion))
  have hinf := finite_maximal_not_mem (E := E) (fstA F) (fun y => ⟨pairA F y 0, rfl⟩) (pairA F 1 0)
    (Prod.ext (mul_one _) (mul_zero _)) (fun x hx => Prod.ext (by
      change (1 : Ainf F) * x.1 = 0
      rw [one_mul]; exact hx) (zero_mul _))
  have hfin : ∀ v : HeightOneSpectrum (𝓞 F),
      {m : Ideal (AF F ⊗[F] E) | m.IsMaximal ∧ algebraMap (AF F) (AF F ⊗[F] E) (pairA F 0 (ind {v})) ∉ m}.Finite :=
    fun v => finite_maximal_not_mem (E := E) ((evalV F v).comp (sndA F))
      (fun y => ⟨pairA F 0 (singleV F v y), GlobalTheory.SplitCoord.evalV_single v y⟩) (pairA F 0 (ind {v}))
      (pl_mul_self v) (fun x hx => Prod.ext (zero_mul _) (fin_ext fun u => by
        change evalV F u (ind {v} * x.2) = evalV F u 0
        rw [map_mul, ev_ind, map_zero]
        split_ifs with h
        · rw [Finset.mem_singleton] at h
          subst h
          change evalV F u x.2 = 0 at hx
          rw [hx, mul_zero]
        · exact zero_mul _))
  refine (hinf.union (S.finite_toSet.biUnion fun v _ => hfin v)).subset ?_
  rintro m ⟨hm, hem⟩
  by_contra hn
  simp only [Set.mem_union, Set.mem_setOf_eq, Set.mem_iUnion, not_or, not_and, not_not, not_exists] at hn
  apply hem
  set_option synthInstance.maxHeartbeats 100000 in
    rw [eps_eq_sum, map_add (f := _), map_sum]
  exact m.add_mem (hn.1 hm) (m.sum_mem fun v hv => hn.2 v hv hm)

end GlobalTheory.DenseAvoid


open GlobalTheory.DenseAvoid in
theorem GlobalTheory.DenseAvoid.exists_unit_eval : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (S : Finset (HeightOneSpectrum (𝓞 F))) (ψ : Polynomial (AE F E)), (∀ (Ω : Type) [Field Ω] (φ : AE F E →+* Ω), φ (algebraMap (AF F) (AE F E) (GlobalTheory.LocalGlobalChar.eps S)) = 1 → ψ.map φ ≠ 0) → ∃ t : F, IsUnit (algebraMap (AF F) (AE F E) (GlobalTheory.LocalGlobalChar.eps S) * ψ.eval (algebraMap F (AE F E) t) + (1 - algebraMap (AF F) (AE F E) (GlobalTheory.LocalGlobalChar.eps S))) := by
  intro F E _ _ _ _ _ S ψ hψ
  classical
  haveI : FiniteDimensional F E := Module.Finite.of_restrictScalars_finite ℚ F E
  haveI : Infinite F := Infinite.of_injective (Nat.cast : ℕ → F) Nat.cast_injective
  set e := algebraMap (AF F) (AE F E) (GlobalTheory.LocalGlobalChar.eps S) with he_def
  have he : e * e = e := by rw [he_def, ← map_mul, GlobalTheory.LocalGlobalChar.eps_mul_self]
  have hone : ∀ m : Ideal (AE F E), m.IsPrime → e ∉ m → 1 - e ∈ m := fun m hm hem => by
    have h0 : e * (1 - e) ∈ m := by rw [mul_sub, mul_one, he, sub_self]; exact m.zero_mem
    exact (hm.mem_or_mem h0).resolve_left hem
  have hM := finite_maximal_not_mem_eps (E := E) S
  let bad : Set F := ⋃ m ∈ {m : Ideal (AE F E) | m.IsMaximal ∧ e ∉ m},
    {t : F | Ideal.Quotient.mk m (ψ.eval (algebraMap F (AE F E) t)) = 0}
  have hbad : bad.Finite := by
    refine hM.biUnion fun m hm => ?_
    haveI := hm.1
    letI := Ideal.Quotient.field m
    have h1 : Ideal.Quotient.mk m e = 1 := by
      rw [← map_one (Ideal.Quotient.mk m), Ideal.Quotient.eq, ← neg_sub]
      exact m.neg_mem (hone m hm.1.isPrime hm.2)
    have hne := hψ (AE F E ⧸ m) (Ideal.Quotient.mk m) h1
    let j : F →+* AE F E ⧸ m := (Ideal.Quotient.mk m).comp (algebraMap F (AE F E))
    refine ((Polynomial.finite_setOf_isRoot hne).preimage j.injective.injOn).subset fun t ht => ?_
    change Ideal.Quotient.mk m (ψ.eval (algebraMap F (AE F E) t)) = 0 at ht
    change Polynomial.IsRoot _ (j t)
    rw [Polynomial.IsRoot.def, Polynomial.eval_map, RingHom.comp_apply, Polynomial.eval₂_hom, ht]
  obtain ⟨t, ht⟩ := hbad.infinite_compl.nonempty
  refine ⟨t, ?_⟩
  by_contra hn
  obtain ⟨m, hm, hxm⟩ := exists_max_ideal_of_mem_nonunits (mem_nonunits_iff.2 hn)
  by_cases hem : e ∈ m
  · have h2 : 1 - e ∈ m := by
      have := m.sub_mem hxm (m.mul_mem_right (ψ.eval (algebraMap F (AE F E) t)) hem)
      rwa [add_sub_cancel_left] at this
    exact hm.ne_top ((Ideal.eq_top_iff_one m).2 (by simpa using m.add_mem hem h2))
  · have h2 : e * ψ.eval (algebraMap F (AE F E) t) ∈ m := by
      have := m.sub_mem hxm (hone m hm.isPrime hem)
      rwa [add_sub_cancel_right] at this
    have h3 := (hm.isPrime.mem_or_mem h2).resolve_left hem
    apply ht
    simp only [bad, Set.mem_iUnion, Set.mem_setOf_eq]
    exact ⟨m, ⟨hm, hem⟩, Ideal.Quotient.eq_zero_iff_mem.2 h3⟩
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSplitPlaceHalfHeisenbergInvariantForm
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum GlobalTheory.WeilParts MeasureTheory IsDedekindDomain NumberField Matrix
open scoped TensorProduct ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.HalfCoinv

section Abstract

variable {G M : Type} [AddCommGroup G] [AddCommGroup M] [Module ℂ M] {Y : AddSubgroup G} {ρ : G → M →ₗ[ℂ] M}

theorem exists_sum_eq_zero (hadd : ∀ x ∈ Y, ∀ x' ∈ Y, ∀ f, ρ x (ρ x' f) = ρ (x + x') f) (h0 : ∀ f, ρ 0 f = f) {Θ : Set M}
    (hsm : ∀ u ∈ Y, ∀ g ∈ Θ, ∃ k : ℕ, 0 < k ∧ ρ (k • u) g = g) {m : M}
    (hm : m ∈ Submodule.span ℂ {m | ∃ u ∈ Y, ∃ g ∈ Θ, m = ρ u g - g}) :
    ∃ (ι : Type) (s : Finset ι) (y : ι → G), (∀ i, y i ∈ Y) ∧ (∃ i ∈ s, y i = 0) ∧ ∑ i ∈ s, ρ (y i) m = 0 := by
  induction hm using Submodule.span_induction with
  | mem m hm =>
    obtain ⟨u, hu, g, hg, rfl⟩ := hm
    obtain ⟨k, hk, h⟩ := hsm u hu g hg
    refine ⟨ℕ, Finset.range k, fun j => j • u, fun j => Y.nsmul_mem hu j,
      ⟨0, Finset.mem_range.2 hk, zero_smul _ _⟩, ?_⟩
    have e : ∀ j : ℕ, ρ (j • u) (ρ u g - g) = ρ ((j + 1) • u) g - ρ (j • u) g := fun j => by
      rw [map_sub, hadd _ (Y.nsmul_mem hu j) _ hu, succ_nsmul]
    simp only [e]
    rw [Finset.sum_range_sub (fun j : ℕ => ρ (j • u) g), h, zero_smul, h0, sub_self]
  | zero => exact ⟨Unit, Finset.univ, fun _ => 0, fun _ => Y.zero_mem, ⟨(), Finset.mem_univ _, rfl⟩, by simp⟩
  | add a b _ _ ha hb =>
    obtain ⟨ι, s, y, hy, ⟨i, hi, hi0⟩, h⟩ := ha
    obtain ⟨κ, t, z, hz, ⟨j, hj, hj0⟩, h'⟩ := hb
    refine ⟨ι × κ, s ×ˢ t, fun p => y p.1 + z p.2, fun p => Y.add_mem (hy _) (hz _),
      ⟨(i, j), Finset.mem_product.2 ⟨hi, hj⟩, by simp only [hi0, hj0, add_zero]⟩, ?_⟩
    simp only [map_add (f := _), Finset.sum_add_distrib]
    have e1 : ∑ p ∈ s ×ˢ t, ρ (y p.1 + z p.2) a = 0 := by
      rw [Finset.sum_product_right]
      refine Finset.sum_eq_zero fun q _ => ?_
      have : ∀ p, ρ (y p + z q) a = ρ (z q) (ρ (y p) a) := fun p => by rw [hadd _ (hz _) _ (hy _), add_comm]
      simp only [this]
      set_option synthInstance.maxHeartbeats 100000 in
        rw [← map_sum, h, map_zero]
    have e2 : ∑ p ∈ s ×ˢ t, ρ (y p.1 + z p.2) b = 0 := by
      rw [Finset.sum_product]
      refine Finset.sum_eq_zero fun p _ => ?_
      have : ∀ q, ρ (y p + z q) b = ρ (y p) (ρ (z q) b) := fun q => by rw [hadd _ (hy _) _ (hz _)]
      simp only [this]
      set_option synthInstance.maxHeartbeats 100000 in
        rw [← map_sum, h', map_zero]
    rw [e1, e2, add_zero]
  | smul c a _ ha =>
    obtain ⟨ι, s, y, hy, hi, h⟩ := ha
    refine ⟨ι, s, y, hy, hi, ?_⟩
    simp only [map_smul]
    rw [← Finset.smul_sum, h, smul_zero]

theorem exists_separating {B : G → G → ℂ} (hcomm : ∀ u y f, ρ u (ρ y f) = B u y • ρ y (ρ u f)) {f₀ : M} (hf : f₀ ≠ 0)
    (hd : ∀ y ∈ Y, ρ y f₀ = f₀ ∨ ∃ u, ρ u f₀ = f₀ ∧ B u y ≠ 1) {ι : Type} (s : Finset ι) {y : ι → G}
    (hy : ∀ i, y i ∈ Y) : ∃ P : M →ₗ[ℂ] M, P f₀ ≠ 0 ∧ ∀ i ∈ s, ρ (y i) f₀ = f₀ ∨ P (ρ (y i) f₀) = 0 := by
  classical
  induction s using Finset.induction_on with
  | empty => exact ⟨LinearMap.id, hf, fun _ h => absurd h (Finset.notMem_empty _)⟩
  | insert j s _ ih =>
    obtain ⟨P, hP, h⟩ := ih
    rcases hd _ (hy j) with h1 | ⟨u, hu, hB⟩
    · exact ⟨P, hP, fun i hi => (Finset.mem_insert.1 hi).elim (fun e => Or.inl (e ▸ h1)) (h i)⟩
    · refine ⟨P ∘ₗ (ρ u - B u (y j) • LinearMap.id), ?_, fun i hi => ?_⟩
      · have : (ρ u - B u (y j) • (LinearMap.id : M →ₗ[ℂ] M)) f₀ = (1 - B u (y j)) • f₀ := by
          rw [LinearMap.sub_apply, hu, sub_smul, one_smul]; rfl
        rw [LinearMap.comp_apply, this, map_smul]
        exact smul_ne_zero (sub_ne_zero.2 hB.symm) hP
      · have : (ρ u - B u (y j) • (LinearMap.id : M →ₗ[ℂ] M)) (ρ (y i) f₀) =
            (B u (y i) - B u (y j)) • ρ (y i) f₀ := by
          rw [LinearMap.sub_apply, hcomm, hu, sub_smul]; rfl
        rw [LinearMap.comp_apply, this, map_smul]
        rcases Finset.mem_insert.1 hi with rfl | hi
        · exact Or.inr (by rw [sub_self, zero_smul])
        · exact (h i hi).imp_right fun e => by rw [e, smul_zero]

theorem exists_form {B : G → G → ℂ} (hadd : ∀ x ∈ Y, ∀ x' ∈ Y, ∀ f, ρ x (ρ x' f) = ρ (x + x') f) (h0 : ∀ f, ρ 0 f = f)
    (hcomm : ∀ u y f, ρ u (ρ y f) = B u y • ρ y (ρ u f)) {Θ : Set M}
    (hsm : ∀ u ∈ Y, ∀ g ∈ Θ, ∃ k : ℕ, 0 < k ∧ ρ (k • u) g = g) {f₀ : M} (hf : f₀ ≠ 0)
    (hd : ∀ y ∈ Y, ρ y f₀ = f₀ ∨ ∃ u, ρ u f₀ = f₀ ∧ B u y ≠ 1) :
    ∃ ℓ : M →ₗ[ℂ] ℂ, (∀ u ∈ Y, ∀ g ∈ Θ, ℓ (ρ u g) = ℓ g) ∧ ℓ f₀ ≠ 0 := by
  classical
  have hn : f₀ ∉ Submodule.span ℂ {m | ∃ u ∈ Y, ∃ g ∈ Θ, m = ρ u g - g} := fun hm => by
    obtain ⟨ι, s, y, hy, ⟨i, hi, hi0⟩, h⟩ := exists_sum_eq_zero hadd h0 hsm hm
    obtain ⟨P, hP, hs⟩ := exists_separating hcomm hf hd s hy
    have e : ∑ j ∈ s, P (ρ (y j) f₀) = ∑ j ∈ s with ρ (y j) f₀ = f₀, P f₀ := by
      rw [Finset.sum_filter]
      refine Finset.sum_congr rfl fun j hj => ?_
      split_ifs with h1
      · rw [h1]
      · exact (hs j hj).resolve_left h1
    set_option synthInstance.maxHeartbeats 100000 in
      rw [← map_sum, h, map_zero, Finset.sum_const, ← Nat.cast_smul_eq_nsmul ℂ] at e
    refine smul_ne_zero (Nat.cast_ne_zero.2 (Finset.card_ne_zero.2 ⟨i, ?_⟩)) hP e.symm
    exact Finset.mem_filter.2 ⟨hi, by rw [hi0, h0]⟩
  obtain ⟨ℓ, h1, h2⟩ := Submodule.exists_dual_map_eq_bot_of_notMem hn inferInstance
  refine ⟨ℓ, fun u hu g hg => ?_, h1⟩
  have : ℓ (ρ u g - g) ∈ (⊥ : Submodule ℂ ℂ) :=
    h2 ▸ Submodule.mem_map_of_mem (Submodule.subset_span ⟨u, hu, g, hg, rfl⟩)
  rwa [Submodule.mem_bot, map_sub, sub_eq_zero] at this

end Abstract

open GlobalTheory.PlaceModel

theorem exists_invariant_form : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ (S T : HSp D) (e : AE D), IsSplitIdem D e → ∃ ℓ : (WO S T → ℂ) →ₗ[ℂ] ℂ, (∀ u : WO S T, (∀ i j, cA D e * u i j = u i j) → ∀ f, IsThetaFunO ψ S T f → ℓ (heisO ψ S T u f) = ℓ f) ∧ ∃ f, IsThetaFunO ψ S T f ∧ ℓ f ≠ 0 := by
  intro D ψ hψ S T e hs
  obtain ⟨θ, hθ⟩ := GlobalTheory.Member.exists_isInfFam_family D
  have hc : ∀ (V : HSp D) τ, ∃ s, IsCartanInv (gramAt D V τ) s := fun V τ =>
    GlobalTheory.Mem.ThetaNonzero.exists_isCartanInv (GlobalTheory.SmoothForms.RealPts.gramAt_herm V τ)
      (GlobalTheory.SmoothForms.RealPts.gramAt_unit V τ)
  choose s hcs using hc
  obtain ⟨f, f0, hf⟩ := GlobalTheory.VacuumO.exists_ne_zero ψ θ hψ hθ S T (s S) (s T) (hcs S) (hcs T) _ _
    (isSelfDualC_latFrame S) (isSelfDualC_latFrame T)
  obtain ⟨hth, hvac, -⟩ := hf 1
  simp only [one_mul] at hth hvac
  have hs' := GlobalTheory.SplitScalar.isSplitIdem_conj hs
  obtain ⟨he, hec, v, ε, hε, heq⟩ := id hs
  have he' : cA D e * cA D e = cA D e := hs'.1
  have heε : algebraMap (AF D.host.F) (AE D) ε * e = e := by rw [← heq]; linear_combination he + hec
  have heε' : algebraMap (AF D.host.F) (AE D) ε * cA D e = cA D e := by rw [← heq]; linear_combination he' + hec
  have hdual := (GlobalTheory.LatVac.latO_selfDual_approx_sign D ψ S T _ _ hψ (isSelfDualC_latFrame S)
    (isSelfDualC_latFrame T)).1
  have c2 : cA D (cA D e) * cA D e = 0 := by rw [GlobalTheory.LatVac.cA_cA, hec]
  obtain ⟨ℓ, h1, h2⟩ := exists_form (Y := half S T (cA D e)) (ρ := heisL S T ψ)
    (B := fun x y => ψ (symplO S T x y)) (Θ := {g | IsThetaFunO ψ S T g}) (heisL_half S T ψ c2)
    (GlobalTheory.SplitScalar.heisO_zero ψ S T) (heisL_comm S T ψ) (fun u hu g hg => by
      obtain ⟨U, hU, h⟩ := hg.level
      obtain ⟨k, hk, hkU⟩ := GlobalTheory.SplitScalar.exists_nsmul_mem U hU (infPart_half hε heε' hu)
      exact ⟨k, hk, h _ hkU (infPart_half hε heε' ((half S T (cA D e)).nsmul_mem hu k))⟩) f0 (fun y hy => by
      by_cases h : ∀ u ∈ (latO S T (latFrame S) (latFrame T) fun w => w = v) ⊓ half S T e, ψ (symplO S T u y) = 1
      · have := mem_of_dual hε hdual he' heε' (by rwa [GlobalTheory.LatVac.cA_cA]) y hy fun u hu => by
          rw [GlobalTheory.LatVac.cA_cA] at hu
          rw [symplO_skew, AddChar.map_neg_eq_inv, h u hu, inv_one]
        exact Or.inl (hvac.2 _ hs' y (latO_le_top _ this.1) ((isHalf_iff S T).2 hy))
      · push_neg at h
        obtain ⟨u, hu, h⟩ := h
        exact Or.inr ⟨u, hvac.2 _ hs u (latO_le_top _ hu.1) ((isHalf_iff S T).2 hu.2), h⟩)
  exact ⟨ℓ, fun u hu g hg => h1 u ((isHalf_iff S T).1 hu) g hg, f, hth, h2⟩

end GlobalTheory.HalfCoinv

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSpreadOfPullbacks
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj

namespace GlobalTheory.SiegelSpreadLocal

theorem exists_spread_of_pullbacks : ∀ (g n : ℕ) (B : Type) [CommRing B] (ζ : B) (R : Type) [CommRing R] [IsNoetherianRing R] (β : B →+* R) (𝔭 : Ideal R) [𝔭.IsPrime] (d : SiegPre g n ζ (spMap β)) (Y : Scheme.{0}) (sY : Y ⟶ Sp B) [LocallyOfFinitePresentation sY] (u : SiegPre g n ζ sY) (r₀ : R) (ι₀ : Localization.Away r₀ →+* Localization.AtPrime 𝔭) (h : Sp (Localization.Away r₀) ⟶ Y) (e : SiegPre g n ζ (spMap ((algebraMap R (Localization.AtPrime 𝔭)).comp β))), r₀ ∉ 𝔭 → ι₀.comp (algebraMap R (Localization.Away r₀)) = algebraMap R (Localization.AtPrime 𝔭) → h ≫ sY = spMap ((algebraMap R (Localization.Away r₀)).comp β) → SiegPB e d (spMap (algebraMap R (Localization.AtPrime 𝔭))) → SiegPB e u (spMap ι₀ ≫ h) → ∃ r ∉ 𝔭, ∃ (κ : Localization.Away r₀ →+* Localization.Away r) (d' : SiegPre g n ζ (spMap ((algebraMap R (Localization.Away r)).comp β))), κ.comp (algebraMap R (Localization.Away r₀)) = algebraMap R (Localization.Away r) ∧ SiegPB d' d (spMap (algebraMap R (Localization.Away r))) ∧ SiegPB d' u (spMap κ ≫ h) := by
  intro g n B _ ζ R _ _ β 𝔭 _ d Y sY _ u r₀ ι₀ h e hr₀ hι₀ hh hed heu
  obtain ⟨t₁, ht₁, hinj⟩ := _root_.GlobalTheory.localization_away_injective_of_dvd R 𝔭
  have hrange := _root_.GlobalTheory.finset_mem_range_of_away_dvd R 𝔭
  have hmono := GlobalTheory.T.localization_away_range_le_of_dvd_of_comp R (Localization.AtPrime 𝔭) (algebraMap R (Localization.AtPrime 𝔭))
  have spc : ∀ {A₁ A₂ A₃ : Type} [CommRing A₁] [CommRing A₂] [CommRing A₃] (a : A₁ →+* A₂) (b : A₂ →+* A₃),
      spMap (b.comp a) = spMap b ≫ spMap a := by
    intro A₁ A₂ A₃ _ _ _ a b
    simp only [spMap, ← Spec.map_comp]
    rfl
  have unit : ∀ x : R, x ∉ 𝔭 → IsUnit (algebraMap R (Localization.AtPrime 𝔭) x) := fun x hx =>
    IsLocalization.map_units (M := 𝔭.primeCompl) (Localization.AtPrime 𝔭) ⟨x, hx⟩
  have nmul : ∀ x y : R, x ∉ 𝔭 → y ∉ 𝔭 → x * y ∉ 𝔭 := fun x y hx hy hm =>
    ((inferInstance : 𝔭.IsPrime).mem_or_mem hm).elim hx hy
  let lam : ∀ c : R, c ∉ 𝔭 → Localization.Away c →+* Localization.AtPrime 𝔭 := fun c hc =>
    IsLocalization.Away.lift c (unit c hc)
  have lamc : ∀ (c : R) (hc : c ∉ 𝔭), (lam c hc).comp (algebraMap R (Localization.Away c)) =
      algebraMap R (Localization.AtPrime 𝔭) := fun c hc => IsLocalization.Away.lift_comp _ _

  have ht : r₀ * t₁ ∉ 𝔭 := nmul _ _ hr₀ ht₁
  let R₀ : Subring (Localization.AtPrime 𝔭) := (lam _ ht).range
  have memR₀ : ∀ x : R, algebraMap R (Localization.AtPrime 𝔭) x ∈ R₀ := fun x =>
    ⟨algebraMap R _ x, by rw [← RingHom.comp_apply, lamc _ ht]⟩
  let a₀ : R →+* R₀ := (algebraMap R (Localization.AtPrime 𝔭)).codRestrict R₀ memR₀
  obtain ⟨⟨d₀, hd₀⟩, -⟩ := GlobalTheory.siegPre_pullback g n B ζ (Sp R) (Sp R₀) (spMap β) (spMap a₀ ≫ spMap β)
    (spMap a₀) d rfl
  have hsub : R₀.subtype.comp a₀ = algebraMap R (Localization.AtPrime 𝔭) := RingHom.ext fun _ => rfl
  have hed₀ : SiegPB e d₀ (spMap R₀.subtype) :=
    GlobalTheory.SiegelPullComp.pb_cancel hd₀ (by rw [← spc, hsub]; exact hed)
  have memι₀ : ∀ x, ι₀ x ∈ R₀ := fun x =>
    hmono r₀ (r₀ * t₁) (dvd_mul_right _ _) ι₀ (lam _ ht) hι₀ (lamc _ ht) ⟨x, rfl⟩
  let j₀ : Localization.Away r₀ →+* R₀ := ι₀.codRestrict R₀ memι₀
  have hj₀ : R₀.subtype.comp j₀ = ι₀ := RingHom.ext fun _ => rfl
  have heu₀ : SiegPB e u (spMap R₀.subtype ≫ (spMap j₀ ≫ h)) := by
    rw [← Category.assoc, ← spc, hj₀]; exact heu
  obtain ⟨F, hF⟩ := _root_.GlobalTheory.SiegSpreadCore.siegPB_spread_subring g n B ζ (Localization.AtPrime 𝔭) R₀ _ d₀ Y sY u (spMap j₀ ≫ h) _ e hed₀ heu₀
  obtain ⟨s, hs, hsF⟩ := hrange F

  have hr : r₀ * t₁ * s ∉ 𝔭 := nmul _ _ ht hs
  let lr := lam _ hr
  let R₁ : Subring (Localization.AtPrime 𝔭) := lr.range
  have hle : R₀ ≤ R₁ := hmono _ _ (dvd_mul_right _ _) _ _ (lamc _ ht) (lamc _ hr)
  have hFR : (F : Set (Localization.AtPrime 𝔭)) ⊆ R₁ := fun x hx =>
    hsF _ (dvd_mul_left _ _) lr (lamc _ hr) x hx
  have hlinj : Function.Injective lr :=
    hinj _ ⟨r₀ * s, by ring⟩ lr (lamc _ hr)
  let er : Localization.Away (r₀ * t₁ * s) ≃+* R₁ :=
    RingEquiv.ofBijective lr.rangeRestrict ⟨fun x y hxy => hlinj (congrArg Subtype.val hxy), lr.rangeRestrict_surjective⟩
  have erv : ∀ x, (er x : Localization.AtPrime 𝔭) = lr x := fun _ => rfl
  obtain ⟨⟨d', hd'⟩, -⟩ := GlobalTheory.siegPre_pullback g n B ζ (Sp R) (Sp (Localization.Away (r₀ * t₁ * s)))
    (spMap β) (spMap ((algebraMap R (Localization.Away (r₀ * t₁ * s))).comp β))
    (spMap (algebraMap R (Localization.Away (r₀ * t₁ * s)))) d (spc _ _).symm
  obtain ⟨⟨d₁, hd₁⟩, -⟩ := GlobalTheory.siegPre_pullback g n B ζ _ (Sp R₁) _ _ (spMap er.toRingHom) d' rfl
  have hd₁₀ : SiegPB d₁ d₀ (spMap (Subring.inclusion hle)) := by
    refine GlobalTheory.SiegelPullComp.pb_cancel hd₀ ?_
    have e₁ : spMap (Subring.inclusion hle) ≫ spMap a₀ = spMap er.toRingHom ≫ spMap (algebraMap R (Localization.Away (r₀ * t₁ * s))) := by
      rw [← spc, ← spc]
      congr 1
      refine RingHom.ext fun x => Subtype.ext ?_
      show algebraMap R (Localization.AtPrime 𝔭) x = lr (algebraMap R _ x)
      rw [← RingHom.comp_apply, lamc _ hr]
    rw [e₁]
    exact GlobalTheory.SiegelPullComp.pb_comp hd' hd₁
  have hd₁u := hF R₁ hle hFR _ d₁ hd₁₀
  have hd'd₁ : SiegPB d' d₁ (spMap er.symm.toRingHom) := by
    refine GlobalTheory.SiegelPullComp.pb_cancel hd₁ ?_
    have e₂ : spMap er.symm.toRingHom ≫ spMap er.toRingHom = 𝟙 _ := by
      rw [← spc]
      have : er.symm.toRingHom.comp er.toRingHom = RingHom.id _ := RingHom.ext fun x => er.symm_apply_apply x
      rw [this]
      simp [spMap]
    rw [e₂]
    exact GlobalTheory.SiegelPullComp.pb_id d'
  let κ : Localization.Away r₀ →+* Localization.Away (r₀ * t₁ * s) :=
    er.symm.toRingHom.comp ((Subring.inclusion hle).comp j₀)
  refine ⟨r₀ * t₁ * s, hr, κ, d', ?_, hd', ?_⟩
  · refine RingHom.ext fun x => hlinj ?_
    rw [RingHom.comp_apply, RingHom.comp_apply]
    have hk : er (κ (algebraMap R _ x)) = (Subring.inclusion hle) (j₀ (algebraMap R _ x)) := er.apply_symm_apply _
    calc lr (κ (algebraMap R _ x)) = (er (κ (algebraMap R _ x)) : Localization.AtPrime 𝔭) := rfl
      _ = ((Subring.inclusion hle) (j₀ (algebraMap R _ x)) : Localization.AtPrime 𝔭) := congrArg Subtype.val hk
      _ = ι₀ (algebraMap R _ x) := rfl
      _ = algebraMap R (Localization.AtPrime 𝔭) x := by rw [← RingHom.comp_apply, hι₀]
      _ = lr (algebraMap R _ x) := by rw [← RingHom.comp_apply, lamc _ hr]
  · have e₃ : spMap κ ≫ h = spMap er.symm.toRingHom ≫ (spMap (Subring.inclusion hle) ≫ (spMap j₀ ≫ h)) := by
      simp only [κ, spc, Category.assoc]
    rw [e₃]
    exact GlobalTheory.SiegelPullComp.pb_comp hd₁u hd'd₁

end GlobalTheory.SiegelSpreadLocal
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUniformizerPowerIntegralRatios
section
open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKCount IsDedekindDomain GlobalTheory.AdicSpan
open scoped TensorProduct Classical

namespace GlobalTheory

theorem adicCompletion_tensor_matrixUnit_identity : ∀ (L : Type) [Field L] [NumberField L] (C : Type) [Ring C] [Algebra ℚ C] (ι : L →ₐ[ℚ] C) (r : ℕ)
    (e : Fin r → C) (N : ℕ) (l : Fin N → L) (c : Fin N → C) (i i' : Fin r),
    (∀ β : Fin r → L, ∑ k, ι (l k) * (∑ i'', ι (β i'') * e i'') * c k = ι (β i') * e i) →
    ∀ (v : HeightOneSpectrum ℤ) (β : Fin r → v.adicCompletion ℚ ⊗[ℚ] L),
    ∑ k, Algebra.TensorProduct.map (AlgHom.id ℚ (v.adicCompletion ℚ)) ι ((1 : v.adicCompletion ℚ) ⊗ₜ[ℚ] l k) *
        (∑ i'', Algebra.TensorProduct.map (AlgHom.id ℚ (v.adicCompletion ℚ)) ι (β i'') *
          ((1 : v.adicCompletion ℚ) ⊗ₜ[ℚ] e i'')) * ((1 : v.adicCompletion ℚ) ⊗ₜ[ℚ] c k) =
      Algebra.TensorProduct.map (AlgHom.id ℚ (v.adicCompletion ℚ)) ι (β i') * ((1 : v.adicCompletion ℚ) ⊗ₜ[ℚ] e i) := by
  intro L _ _ C _ _ ι r e N l c i i' h v β
  set φ := Algebra.TensorProduct.map (AlgHom.id ℚ (v.adicCompletion ℚ)) ι with hφ
  let P : (Fin r → v.adicCompletion ℚ ⊗[ℚ] L) → Prop := fun β =>
    ∑ k, φ ((1 : v.adicCompletion ℚ) ⊗ₜ[ℚ] l k) *
        (∑ i'', φ (β i'') * ((1 : v.adicCompletion ℚ) ⊗ₜ[ℚ] e i'')) * ((1 : v.adicCompletion ℚ) ⊗ₜ[ℚ] c k) =
      φ (β i') * ((1 : v.adicCompletion ℚ) ⊗ₜ[ℚ] e i)
  have hzero : P 0 := by simp [P]
  have hadd : ∀ β₁ β₂, P β₁ → P β₂ → P (β₁ + β₂) := by
    intro β₁ β₂ h₁ h₂
    simp only [P, Pi.add_apply, map_add (f := _), add_mul, Finset.sum_add_distrib, mul_add] at h₁ h₂ ⊢
    rw [h₁, h₂]
  have hpure : ∀ (a : v.adicCompletion ℚ) (γ : Fin r → L), P (fun j => a ⊗ₜ[ℚ] γ j) := by
    intro a γ
    simp only [P, hφ, Algebra.TensorProduct.map_tmul, AlgHom.id_apply,
      Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul, ← TensorProduct.tmul_sum]
    rw [h γ]
  have hsingle : ∀ j x, P (Pi.single j x) := by
    intro j x
    induction x using TensorProduct.induction_on with
    | zero => simpa using hzero
    | tmul a m =>
      have : (Pi.single j (a ⊗ₜ[ℚ] m) : Fin r → v.adicCompletion ℚ ⊗[ℚ] L) =
          fun j' => a ⊗ₜ[ℚ] (Pi.single j m : Fin r → L) j' := by
        funext j'
        by_cases hj : j' = j
        · subst hj; simp
        · simp [Pi.single_apply, hj]
      rw [this]; exact hpure a _
    | add x y hx hy =>
      rw [Pi.single_add]; exact hadd _ _ hx hy
  have hall : P (∑ j, Pi.single j (β j)) :=
    Finset.sum_induction _ P hadd hzero (fun j _ => hsingle j (β j))
  rw [Finset.univ_sum_single] at hall
  exact hall

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteCoheightOneNotMemOpenGenericPointStatement
section
open AlgebraicGeometry CategoryTheory Limits
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finite_coheight_one_notMem_open_genericPoint : ∀ (X : Scheme.{0}) [IsIntegral X] [AlgebraicGeometry.IsNoetherian X] (S : Set X), IsOpen S → genericPoint X ∈ S → {x : X | Order.coheight x = 1 ∧ x ∉ S}.Finite := by
  first | exact @GlobalTheory.VerticalUnit.finite_coheight_one_notMem | exact GlobalTheory.VerticalUnit.finite_coheight_one_notMem | (intros; apply GlobalTheory.VerticalUnit.finite_coheight_one_notMem <;> assumption)
end

