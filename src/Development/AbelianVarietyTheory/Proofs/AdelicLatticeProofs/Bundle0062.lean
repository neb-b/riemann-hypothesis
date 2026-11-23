module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0057
public import Formalism.LocalToGlobal.LatticeGeometry.Bundle0001

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ScaledMatrixMemRationalLattice
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix GlobalTheory.LatVac
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.LatVacFull

variable {D : D7}

theorem exists_nat_integral {E : Type} [Field E] [NumberField E] (c : E) :
    ∃ n : ℕ, 0 < n ∧ ∃ d : 𝓞 E, (d : E) = n * c := by
  obtain ⟨y, hy0, hy⟩ := exists_integral_multiples ℤ ℚ ({c} : Finset E)
  have h := hy c (by simp)
  refine ⟨y.natAbs, Int.natAbs_pos.2 hy0, ?_⟩
  rcases Int.natAbs_eq y with h1 | h1
  · refine ⟨⟨y • c, h⟩, ?_⟩
    change y • c = _
    rw [zsmul_eq_mul]
    congr 1
    conv_lhs => rw [h1]
    exact Int.cast_natCast _
  · refine ⟨-⟨y • c, h⟩, ?_⟩
    change -(y • c) = _
    rw [zsmul_eq_mul, ← neg_mul]
    congr 1
    conv_lhs => rw [h1]
    rw [Int.cast_neg, neg_neg, Int.cast_natCast]

theorem AA_ne_zero (D : D7) : D.host.AA ≠ 0 := by
  refine mul_ne_zero ?_ (inv_ne_zero ?_)
  · rw [FractionalIdeal.coeIdeal_ne_zero]
    intro h
    exact D.host.ccK_ne_bot
      ((Ideal.map_eq_bot_iff_of_injective (RingOfIntegers.algebraMap.injective _ _)).1 h)
  · rw [FractionalIdeal.coeIdeal_ne_zero]
    intro h
    have h1 := D.host.𝔟_spec.1
    rw [h, Ideal.bot_mul] at h1
    exact differentIdeal_ne_bot h1

section
variable (S T : HSp D) (s x y : Fin S.rank → D.host.E) (t u v : Fin T.rank → D.host.E) (a c : D.host.E)

theorem genMap_one (ha0 : a ≠ 0) : genMap S T 1 s t = a⁻¹ • genMap S T a s t := by
  ext i j
  simp only [genMap, Matrix.of_apply, Matrix.smul_apply, smul_eq_mul, ← mul_assoc, inv_mul_cancel₀ ha0]

theorem genMap_zero_right : genMap S T 1 s 0 = 0 := by
  ext i j
  simp only [genMap, Matrix.of_apply, Pi.zero_apply, Matrix.zero_apply, mul_zero, zero_mul]

theorem genMap_add_right : genMap S T 1 s (u + v) = genMap S T 1 s u + genMap S T 1 s v := by
  ext i j
  simp only [genMap, Matrix.of_apply, Pi.add_apply, Matrix.add_apply, mul_add, add_mul]

theorem genMap_smul_right : genMap S T 1 s (c • u) = c • genMap S T 1 s u := by
  ext i j
  simp only [genMap, Matrix.of_apply, Pi.smul_apply, Matrix.smul_apply, smul_eq_mul, one_mul, mul_assoc]

theorem genMap_zero_left : genMap S T 1 0 t = 0 := by
  ext i j
  simp only [genMap, Matrix.of_apply, Pi.zero_apply, Matrix.zero_apply, star_zero, mul_zero, zero_mul,
    Finset.sum_const_zero]

theorem genMap_add_left : genMap S T 1 (x + y) t = genMap S T 1 x t + genMap S T 1 y t := by
  ext i j
  simp only [genMap, Matrix.of_apply, Pi.add_apply, Matrix.add_apply, star_add, mul_add, add_mul,
    Finset.sum_add_distrib]

theorem genMap_smul_left : genMap S T 1 (c • x) t = star c • genMap S T 1 x t := by
  refine Matrix.ext fun i j => ?_
  simp only [genMap, Matrix.of_apply, Matrix.smul_apply, Pi.smul_apply, smul_eq_mul, star_mul',
    Finset.mul_sum]
  exact Finset.sum_congr rfl fun k _ => by ring

end

def sat (S T : HSp D) (LS : Set (Fin S.rank → D.host.E)) (LT : Set (Fin T.rank → D.host.E)) :
    Submodule D.host.E (Matrix (Fin T.rank) (Fin S.rank) D.host.E) where
  carrier := {M | ∃ N : ℕ, 0 < N ∧ N • M ∈ latRat S T LS LT}
  zero_mem' := ⟨1, one_pos, by simp⟩
  add_mem' := by
    rintro x y ⟨n, hn, hx⟩ ⟨m, hm, hy⟩
    refine ⟨n * m, Nat.mul_pos hn hm, ?_⟩
    rw [smul_add]
    refine add_mem ?_ ?_
    · rw [mul_comm, mul_smul]; exact nsmul_mem hx m
    · rw [mul_smul]; exact nsmul_mem hy n
  smul_mem' := by
    rintro c x ⟨n, hn, hx⟩
    obtain ⟨m, hm, d, hd⟩ := exists_nat_integral c
    refine ⟨m * n, Nat.mul_pos hm hn, ?_⟩
    have h := smul_mem_latRat d hx
    have e : (m * n) • c • x = (d : D.host.E) • n • x := by
      rw [hd]; ext i j; simp; ring
    rw [e]; exact h

theorem genMap_mem_sat (S T : HSp D) (ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E))
    (ΛT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)) (hS : Submodule.IsFullLattice D.host.E ΛS)
    (hT : Submodule.IsFullLattice D.host.E ΛT) (s : Fin S.rank → D.host.E) (t : Fin T.rank → D.host.E) :
    genMap S T 1 s t ∈ sat S T (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) := by
  obtain ⟨a, ha0, ha⟩ : ∃ a : D.host.E, a ≠ 0 ∧ a ∈ D.host.AA := by
    by_contra h
    push_neg at h
    apply AA_ne_zero D
    rw [FractionalIdeal.eq_zero_iff]
    intro x hx
    by_contra hx0
    exact h x hx0 hx
  have hs : s ∈ Submodule.span D.host.E (ΛS : Set (Fin S.rank → D.host.E)) := by
    rw [Submodule.IsFullLattice.span_eq_top (self := hS)]; trivial
  have ht : t ∈ Submodule.span D.host.E (ΛT : Set (Fin T.rank → D.host.E)) := by
    rw [Submodule.IsFullLattice.span_eq_top (self := hT)]; trivial
  induction hs using Submodule.span_induction with
  | mem s hs =>
    induction ht using Submodule.span_induction with
    | mem t ht =>
      rw [genMap_one S T s t a ha0]
      refine Submodule.smul_mem _ _ ⟨1, one_pos, ?_⟩
      rw [one_smul]
      exact AddSubgroup.subset_closure ⟨a, ha, s, hs, t, ht, rfl⟩
    | zero => rw [genMap_zero_right]; exact zero_mem _
    | add x y _ _ hx hy => rw [genMap_add_right]; exact add_mem hx hy
    | smul c x _ hx => rw [genMap_smul_right]; exact Submodule.smul_mem _ _ hx
  | zero => rw [genMap_zero_left]; exact zero_mem _
  | add x y _ _ hx hy => rw [genMap_add_left]; exact add_mem hx hy
  | smul c x _ hx => rw [genMap_smul_left]; exact Submodule.smul_mem _ _ hx

theorem latRat_full (D : D7) (S T : HSp D) (ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E))
    (ΛT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)) (hS : Submodule.IsFullLattice D.host.E ΛS)
    (hT : Submodule.IsFullLattice D.host.E ΛT) (M : Matrix (Fin T.rank) (Fin S.rank) D.host.E) :
    ∃ N : ℕ, 0 < N ∧
      N • M ∈ latRat S T (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) := by
  change M ∈ sat S T (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E))
  have e : M = ∑ i, genMap S T 1 (fun k => star ((M * S.gram⁻¹) i k)) (Pi.single i 1) := by
    ext i j
    have h : ∀ l, ∑ k, (M * S.gram⁻¹) l k * S.gram k j = M l j := by
      intro l
      rw [← Matrix.mul_apply, Matrix.mul_assoc, Matrix.nonsing_inv_mul _ (gram_det_isUnit S),
        Matrix.mul_one]
    simp only [Matrix.sum_apply, genMap, Matrix.of_apply, star_star, h, one_mul]
    simp [Pi.single_apply]
  rw [e]
  exact Submodule.sum_mem _ fun i _ => genMap_mem_sat S T ΛS ΛT hS hT _ _

end GlobalTheory.LatVacFull

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.StdCharFinitePartRationalEqExpTrace
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix GlobalTheory.LatVac
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.StdRat

theorem sum_cmType_eq_trace {F E ι : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    [Fintype ι] (h2 : Module.finrank F E = 2) (τ : ι → (E →+* ℂ)) (hi : Function.Injective τ)
    (hcm : ∀ σ, (∃ t, τ t = σ) ↔ ¬ ∃ t, τ t = ComplexEmbedding.conjugate σ) (x : F)
    (hx : ∀ σ : E →+* ℂ, ComplexEmbedding.conjugate σ (algebraMap F E x) = σ (algebraMap F E x)) :
    ∑ t, τ t (algebraMap F E x) = ((Algebra.trace ℚ F x : ℚ) : ℂ) := by
  classical
  set y := algebraMap F E x with hy
  have h1 : ((Algebra.trace ℚ E y : ℚ) : ℂ) = ∑ σ : E →+* ℂ, σ y := by
    have := trace_eq_sum_embeddings (K := ℚ) (L := E) ℂ (x := y)
    rw [eq_ratCast] at this
    rw [this]
    exact (Fintype.sum_equiv (RingHom.equivRatAlgHom E ℂ) _ _ fun _ => rfl).symm
  have h3 : Algebra.trace ℚ E y = 2 * Algebra.trace ℚ F x := by
    rw [← Algebra.trace_trace (S := F), hy, Algebra.trace_algebraMap, h2, map_nsmul, nsmul_eq_mul]
    rfl
  have hb : Function.Bijective (Sum.elim τ fun t => ComplexEmbedding.conjugate (τ t)) := by
    have hc : ∀ σ : E →+* ℂ, ComplexEmbedding.conjugate (ComplexEmbedding.conjugate σ) = σ :=
      fun σ => star_star σ
    constructor
    · rintro (a | a) (b | b) h <;> simp only [Sum.elim_inl, Sum.elim_inr] at h
      · rw [hi h]
      · exact absurd ⟨a, h⟩ ((hcm (τ b)).1 ⟨b, rfl⟩)
      · exact absurd ⟨b, h.symm⟩ ((hcm (τ a)).1 ⟨a, rfl⟩)
      · have := congrArg ComplexEmbedding.conjugate h
        rw [hc, hc] at this
        rw [hi this]
    · intro σ
      by_cases h : ∃ t, τ t = ComplexEmbedding.conjugate σ
      · obtain ⟨t, ht⟩ := h
        exact ⟨Sum.inr t, by simp only [Sum.elim_inr]; rw [ht, hc]⟩
      · obtain ⟨t, ht⟩ := (hcm σ).2 h
        exact ⟨Sum.inl t, ht⟩
  have h4 := hb.sum_comp fun σ : E →+* ℂ => σ y
  rw [Fintype.sum_sum_type, ← h1, h3] at h4
  simp only [Sum.elim_inl, Sum.elim_inr, hx] at h4
  push_cast at h4
  linear_combination h4 / 2

theorem tauE_injective (D : D7) : Function.Injective (tauE D) := fun _ _ h =>
  D.eTau.injective (Subtype.ext ((factEmb D.R D.host).1.1 h))

theorem tauE_cm (D : D7) (σ : D.host.E →+* ℂ) :
    (∃ τ, tauE D τ = σ) ↔ ¬ ∃ τ, tauE D τ = ComplexEmbedding.conjugate σ := by
  obtain ⟨g, rfl⟩ := (factEmb D.R D.host).1.2 σ
  have hc : ComplexEmbedding.conjugate (D.host.emb g) = D.host.emb (g * D.R.cc) := by
    rw [Formalism.L2.Geo.emb_mul_cc_comp]
    refine RingHom.ext fun x => ?_
    have hcm := D.host.isCMField_hostE
    have h : IsCMField.complexConj D.host.E x = D.host.conj x := by
      apply D.host.φ₀.injective
      rw [IsCMField.complexEmbedding_complexConj]
      exact (D.host.toHostAx.conjE_apply _ x).symm
    show starRingEnd ℂ (D.host.emb g x) = D.host.emb g (D.host.conj x)
    rw [← h, IsCMField.complexEmbedding_complexConj]
  have h : ∀ g, (∃ τ, tauE D τ = D.host.emb g) ↔ g ∈ D.R.Psi := fun g => by
    rw [← Formalism.L2.Geo.exists_tauEmb_iff D g]
    exact exists_congr fun τ => eq_comm
  rw [hc, h, h]
  exact Formalism.L2.Geo.mem_Psi_iff_mul_cc_notMem g

theorem sum_tauE_eq_trace (D : D7) (x : D.host.F) :
    ∑ t, tauE D t (algebraMap D.host.F D.host.E x) = ((Algebra.trace ℚ D.host.F x : ℚ) : ℂ) := by
  have hcm := D.host.isCMField_hostE
  refine sum_cmType_eq_trace ?_ _ (tauE_injective D) (tauE_cm D) x fun σ => ?_
  · exact Algebra.IsQuadraticExtension.finrank_eq_two _ _
  · show starRingEnd ℂ (σ _) = _
    rw [← IsCMField.complexEmbedding_complexConj]
    exact congrArg σ ((IsCMField.complexConj D.host.E).commutes x)

theorem char_fin_rat {F : Type} [Field F] [NumberField F] (ψ : AddChar (AF F) ℂ) (h : IsCharAF F ψ) (x : F) :
    ψ (pairA F 0 (algebraMap F (Af F) x)) = psiInf F ψ (algebraMap F (Ainf F) (-x)) := by
  have e : pairA F 0 (algebraMap F (Af F) x) =
      algebraMap F (AF F) x + pairA F (algebraMap F (Ainf F) (-x)) 0 := by
    refine Prod.ext ?_ (add_zero _).symm
    show (0 : Ainf F) = algebraMap F (Ainf F) x + algebraMap F (Ainf F) (-x)
    rw [map_neg, add_neg_cancel]
  rw [e, AddChar.map_add_eq_mul, h.2.2.1, one_mul, psiInf]

theorem tmul_one_eq {F E A : Type} [Field F] [Field E] [CommRing A] [Algebra F E] [Algebra F A] (x : F) :
    (algebraMap F A x) ⊗ₜ[F] (1 : E) = (1 : A) ⊗ₜ[F] (algebraMap F E x) := by
  rw [Algebra.algebraMap_eq_smul_one, Algebra.algebraMap_eq_smul_one, TensorProduct.smul_tmul]

theorem stdChar_fin_rat : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ x : D.host.F, ψ (pairA D.host.F 0 (algebraMap D.host.F (Af D.host.F) x)) = Complex.exp (2 * Real.pi * Complex.I * ((Algebra.trace ℚ D.host.F x : ℚ) : ℂ)) := by
  intro D ψ hψ x
  obtain ⟨θ, hθ⟩ := hψ.2.1
  rw [char_fin_rat ψ hψ.1, hψ.2.2 θ hθ, tmul_one_eq,
    Finset.sum_congr rfl fun ρ _ => (hθ ρ).1 _, sum_tauE_eq_trace, map_neg]
  congr 1
  push_cast
  ring

end GlobalTheory.StdRat

end
end

