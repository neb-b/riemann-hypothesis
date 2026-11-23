module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.AdelicHermitianForms.Bundle0002
public import Development.AbelianVarietyTheory.Definitions.AdelicHermitianForms.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0008
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0009
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0006
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0016
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ExistsUniqueIdeleOfLinearEquivQuotientLocal
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0002
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0013

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ExistsQuasiReflectionProdMulVecEq
section
open NumberField IsDedekindDomain GlobalTheory.AdLat GlobalTheory.UnRep
open scoped TensorProduct Matrix

namespace GlobalTheory.UnRep.ReflStep

variable {F E : Type} [Field F] [Field E] [Algebra F E] (c : E ≃ₐ[F] E) {n : ℕ} (G : Matrix (Fin n) (Fin n) E)

theorem herm_sub_smul_left (z x w : Fin n → E) (e : E) :
    hermE c G (z - e • x) w = hermE c G z w - e * hermE c G x w := by
  simp only [hermE, Finset.mul_sum, ← Finset.sum_sub_distrib, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  ring

theorem herm_sub_smul_right (z x w : Fin n → E) (e : E) :
    hermE c G w (z - e • x) = hermE c G w z - c e * hermE c G w x := by
  simp only [hermE, Finset.mul_sum, ← Finset.sum_sub_distrib, Pi.sub_apply, Pi.smul_apply, smul_eq_mul,
    map_sub, map_mul]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  ring

theorem herm_smul_left (x w : Fin n → E) (e : E) :
    hermE c G (e • x) w = e * hermE c G x w := by
  simp only [hermE, Finset.mul_sum, Pi.smul_apply, smul_eq_mul]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  ring

theorem herm_conj (h : IsHermForm c G) (x y : Fin n → E) : c (hermE c G x y) = hermE c G y x := by
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [hermE, map_sum, map_mul, h.1, h.2.2.1]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  ring

theorem refl_mulVec (x v : Fin n → E) (u : E) :
    refl c G x u *ᵥ v = v + ((u - 1) * hermE c G v x / hermE c G x x) • x := by
  have hd : (G *ᵥ fun b => c (x b)) ⬝ᵥ v = hermE c G v x := by
    simp only [hermE, dotProduct, Matrix.mulVec, Finset.sum_mul]
    refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
    ring
  rw [refl, Matrix.add_mulVec, Matrix.one_mulVec, Matrix.smul_mulVec, Matrix.vecMulVec_mulVec, hd]
  ext i
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, MulOpposite.smul_eq_mul_unop, MulOpposite.unop_op]
  ring

theorem exists_refl (h : IsHermForm c G) (x z : Fin n → E) (hz : hermE c G z z = hermE c G x x) (e : E)
    (he : c e = e) (he2 : e * e = 1) (hy : hermE c G (z - e • x) (z - e • x) ≠ 0) :
    ∃ u : E, u * c u = 1 ∧ refl c G (z - e • x) u *ᵥ z = e • x := by
  obtain ⟨a, ha⟩ : ∃ a, a = hermE c G z (z - e • x) := ⟨_, rfl⟩
  have hyy : hermE c G (z - e • x) (z - e • x) = a + c a := by
    rw [ha, herm_conj c G h, herm_sub_smul_left c G z x (z - e • x), herm_sub_smul_left c G z x z,
      herm_sub_smul_right c G z x x, he, hz]
    linear_combination (hermE c G x x) * he2
  have ha0 : a ≠ 0 := by
    rintro rfl
    exact hy (by simpa using hyy)
  have hca : c a ≠ 0 := by simpa using ha0
  refine ⟨-c a / a, ?_, ?_⟩
  · rw [map_div₀, map_neg, h.1]
    field_simp
  · rw [refl_mulVec, ← ha]
    have : (-c a / a - 1) * a / hermE c G (z - e • x) (z - e • x) = -1 := by
      rw [div_eq_iff hy, hyy]
      field_simp
      ring
    rw [this]
    simp

end GlobalTheory.UnRep.ReflStep


open GlobalTheory.UnRep.ReflStep in
theorem GlobalTheory.UnRep.exists_refl_prod_mulVec_eq : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (c : E ≃ₐ[F] E) (n : ℕ) (G : Matrix (Fin n) (Fin n) E), IsHermForm c G → ∀ x z : Fin n → E, hermE c G x x ≠ 0 → hermE c G z z = hermE c G x x → ∃ l : List ((Fin n → E) × E), (∀ p ∈ l, hermE c G p.1 p.1 ≠ 0 ∧ p.2 * c p.2 = 1 ∧ p.1 ∈ Submodule.span E {x, z}) ∧ (l.map fun p => refl c G p.1 p.2).prod *ᵥ z = x := by
  intro F E _ _ _ _ _ c n G h x z hx hz
  have hxs : x ∈ Submodule.span E ({x, z} : Set (Fin n → E)) := Submodule.subset_span (by simp)
  have hzs : z ∈ Submodule.span E ({x, z} : Set (Fin n → E)) := Submodule.subset_span (by simp)
  have hmem : ∀ e : E, z - e • x ∈ Submodule.span E ({x, z} : Set (Fin n → E)) := fun e =>
    Submodule.sub_mem _ hzs (Submodule.smul_mem _ _ hxs)
  by_cases h1 : hermE c G (z - (1 : E) • x) (z - (1 : E) • x) = 0
  · have h2 : hermE c G (z - (-1 : E) • x) (z - (-1 : E) • x) ≠ 0 := by
      intro h2
      rw [herm_sub_smul_left, herm_sub_smul_right, herm_sub_smul_right] at h1 h2
      simp only [map_one, map_neg, hz] at h1 h2
      apply hx
      have h4 : (4 : E) * hermE c G x x = 0 := by linear_combination h1 + h2
      exact (mul_eq_zero.1 h4).resolve_left (by norm_num)
    obtain ⟨u, hu, hu'⟩ := exists_refl c G h x z hz (-1) (by simp) (by simp) h2
    refine ⟨[(x, -1), (z - (-1 : E) • x, u)], ?_, ?_⟩
    · intro p hp
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
      rcases hp with rfl | rfl
      · exact ⟨hx, by simp, hxs⟩
      · exact ⟨h2, hu, hmem _⟩
    · simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one]
      rw [← Matrix.mulVec_mulVec, hu', refl_mulVec, herm_smul_left, ← add_smul]
      have : (-1 : E) + (-1 - 1) * (-1 * hermE c G x x) / hermE c G x x = 1 := by
        field_simp
        ring
      rw [this, one_smul]
  · obtain ⟨u, hu, hu'⟩ := exists_refl c G h x z hz 1 (by simp) (by simp) h1
    refine ⟨[(z - (1 : E) • x, u)], ?_, ?_⟩
    · intro p hp
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
      subst hp
      exact ⟨h1, hu, hmem _⟩
    · simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one]
      rw [hu', one_smul]
end

-- bundled from Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ExistsRatOfForallComplexRingEquivFixed
section
open Matrix GlobalTheory.ClassFin
open scoped Kronecker ComplexOrder TensorProduct

namespace GlobalTheory.ClassFin


open Matrix in
open scoped Kronecker ComplexOrder TensorProduct in
theorem _root_.GlobalTheory.ClassFin.exists_rat_of_forall_ringEquiv_fixed :
    ∀ z : ℂ, (∀ σ : ℂ ≃+* ℂ, σ z = z) → ∃ q : ℚ, z = q := by
  intro z hz
  by_contra h
  push_neg at h
  by_cases ha : IsAlgebraic ℚ z
  · obtain ⟨σ, hσ⟩ := _root_.GlobalTheory.ClassFin.exists_ringEquiv_apply_ne_of_isAlgebraic z ha h
    exact hσ (hz σ)
  · obtain ⟨σ, hσ⟩ := _root_.GlobalTheory.ClassFin.exists_ringEquiv_ne_of_transcendental z ha
    exact hσ (hz σ)

end GlobalTheory.ClassFin
end

-- bundled from Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ExistsRationalEquationsWeilRestriction
section
open Matrix GlobalTheory.ClassFin
open scoped Kronecker ComplexOrder TensorProduct

namespace GlobalTheory.ClassFin.WeilEqs

noncomputable def coordOf {κ β R : Type} [Fintype β] [CommRing R] [Algebra ℚ R] (c : β → ℚ)
    (y : Matrix ((κ × β) ⊕ Unit) ((κ × β) ⊕ Unit) R) (i j : κ) (k : β) : R :=
  ∑ l, y (Sum.inl (i, k)) (Sum.inl (j, l)) * algebraMap ℚ R (c l)

noncomputable def gen (ι : Type) : Matrix ι ι (MvPolynomial (ι × ι) ℚ) :=
  Matrix.of fun i j => MvPolynomial.X (i, j)

section
variable {κ β R : Type} [Fintype κ] [DecidableEq κ] [Fintype β] [DecidableEq β] [CommRing R] [Algebra ℚ R]

omit [Fintype κ] [DecidableEq κ] [DecidableEq β] in
theorem aeval_coordOf (c : β → ℚ) (y : Matrix ((κ × β) ⊕ Unit) ((κ × β) ⊕ Unit) R) (i j : κ) (k : β) :
    MvPolynomial.aeval (fun ij : ((κ × β) ⊕ Unit) × ((κ × β) ⊕ Unit) => y ij.1 ij.2)
      (coordOf c (gen ((κ × β) ⊕ Unit)) i j k) = coordOf c y i j k := by
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [coordOf, gen, map_sum, map_mul, Matrix.of_apply, MvPolynomial.aeval_X, AlgHom.commutes]

theorem aeval_det (y : Matrix ((κ × β) ⊕ Unit) ((κ × β) ⊕ Unit) R) :
    MvPolynomial.aeval (fun ij : ((κ × β) ⊕ Unit) × ((κ × β) ⊕ Unit) => y ij.1 ij.2)
      ((gen ((κ × β) ⊕ Unit)).toBlocks₁₁.det) = y.toBlocks₁₁.det := by
  rw [AlgHom.map_det]
  congr 1
  ext p q
  simp [gen, Matrix.toBlocks₁₁]

omit [Fintype κ] [DecidableEq κ] [DecidableEq β] in
theorem aeval_comp_coord (c : β → ℚ) (y : Matrix ((κ × β) ⊕ Unit) ((κ × β) ⊕ Unit) R)
    (Q : MvPolynomial ((κ × κ) × β) ℚ) :
    MvPolynomial.aeval (fun ij : ((κ × β) ⊕ Unit) × ((κ × β) ⊕ Unit) => y ij.1 ij.2)
      (MvPolynomial.aeval (fun p : (κ × κ) × β => coordOf c (gen ((κ × β) ⊕ Unit)) p.1.1 p.1.2 p.2) Q) =
      MvPolynomial.aeval (fun p : (κ × κ) × β => coordOf c y p.1.1 p.1.2 p.2) Q := by
  rw [← AlgHom.comp_apply, MvPolynomial.comp_aeval]
  simp only [aeval_coordOf]

variable {A : Type} [CommRing A] [Algebra R A]

theorem sum_leftMul_one (b : Module.Basis β R A) (x : A) (k : β) :
    ∑ l, Algebra.leftMulMatrix b x k l * b.repr 1 l = b.repr x k := by
  have h := congrFun (Algebra.leftMulMatrix_mulVec_repr b x 1) k
  simpa [Matrix.mulVec, dotProduct] using h

theorem leftMul_expand (b : Module.Basis β R A) (x : A) (k l : β) :
    Algebra.leftMulMatrix b x k l = ∑ m, b.repr x m * Algebra.leftMulMatrix b (b m) k l := by
  conv_lhs => rw [← b.sum_repr x]
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [map_sum, map_smul, Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul]

end

theorem exists_equations : ∀ (F β : Type) [Field F] [Algebra ℚ F] [Fintype β] [DecidableEq β] (ω : Module.Basis β ℚ F) (n : ℕ) (S : Set (MvPolynomial (Fin n × Fin n) F)), ∃ S' : Set (MvPolynomial (((Fin n × β) ⊕ Unit) × ((Fin n × β) ⊕ Unit)) ℚ), ∀ (R A : Type) [CommRing R] [CommRing A] [Algebra ℚ R] [Algebra R A] [Algebra F A] (b : Module.Basis β R A), (∀ i, b i = algebraMap F A (ω i)) → ∀ y : Matrix ((Fin n × β) ⊕ Unit) ((Fin n × β) ⊕ Unit) R, (∀ f ∈ S', ev f y = 0) ↔ ∃ g : GL (Fin n) A, (∀ P ∈ S, MvPolynomial.aeval (fun ij : Fin n × Fin n => (g : Matrix (Fin n) (Fin n) A) ij.1 ij.2) P = 0) ∧ y = emb b g := by
  intro F β _ _ _ _ ω n S
  choose Q hQ using fun P : MvPolynomial (Fin n × Fin n) F => _root_.GlobalTheory.ClassFin.exists_coord_polynomial F β ω (Fin n × Fin n) P
  let c : β → ℚ := fun l => ω.repr 1 l
  let X := gen ((Fin n × β) ⊕ Unit)
  refine ⟨{f | (∃ p u, f = X (Sum.inl p) (Sum.inr u)) ∨ (∃ p u, f = X (Sum.inr u) (Sum.inl p)) ∨
    (∃ i j k l, f = X (Sum.inl (i, k)) (Sum.inl (j, l)) -
      ∑ m, coordOf c X i j m * algebraMap ℚ _ (Algebra.leftMulMatrix ω (ω m) k l)) ∨
    f = X.toBlocks₁₁.det * X (Sum.inr ()) (Sum.inr ()) - 1 ∨
    ∃ P ∈ S, ∃ k, f = MvPolynomial.aeval
      (fun p : (Fin n × Fin n) × β => coordOf c X p.1.1 p.1.2 p.2) (Q P k)}, ?_⟩
  intro R A _ _ _ _ _ b hb y
  have hm := _root_.GlobalTheory.ClassFin.coords_const_baseChange F β ω R A b hb
  obtain ⟨h1, hmul, -, hunit⟩ := _root_.GlobalTheory.ClassFin.res_one_mul_injective_isUnit R A β (Fin n) b
  have hc : ∀ l, algebraMap ℚ R (c l) = b.repr 1 l := fun l => by
    have := (hm 1).1 l
    rw [map_one] at this
    exact this.symm
  have hL : ∀ m k l, algebraMap ℚ R (Algebra.leftMulMatrix ω (ω m) k l) =
      Algebra.leftMulMatrix b (b m) k l := fun m k l => by
    rw [hb m, (hm (ω m)).2, Matrix.map_apply]
  have hX : ∀ p q, MvPolynomial.aeval
      (fun ij : ((Fin n × β) ⊕ Unit) × ((Fin n × β) ⊕ Unit) => y ij.1 ij.2) (X p q) = y p q := fun p q => by
    simp [X, gen]
  have hinv : ∀ g : GL (Fin n) A, (res b (g : Matrix (Fin n) (Fin n) A)).det *
      (res b ((g⁻¹ : GL (Fin n) A) : Matrix (Fin n) (Fin n) A)).det = 1 := fun g => by
    rw [← Matrix.det_mul, ← hmul, Units.mul_inv, h1, Matrix.det_one]
  have key : (∀ f ∈ {f | (∃ p u, f = X (Sum.inl p) (Sum.inr u)) ∨ (∃ p u, f = X (Sum.inr u) (Sum.inl p)) ∨
    (∃ i j k l, f = X (Sum.inl (i, k)) (Sum.inl (j, l)) -
      ∑ m, coordOf c X i j m * algebraMap ℚ _ (Algebra.leftMulMatrix ω (ω m) k l)) ∨
    f = X.toBlocks₁₁.det * X (Sum.inr ()) (Sum.inr ()) - 1 ∨
    ∃ P ∈ S, ∃ k, f = MvPolynomial.aeval
      (fun p : (Fin n × Fin n) × β => coordOf c X p.1.1 p.1.2 p.2) (Q P k)}, ev f y = 0) ↔
      ((∀ p u, y (Sum.inl p) (Sum.inr u) = 0) ∧ (∀ p u, y (Sum.inr u) (Sum.inl p) = 0) ∧
       (∀ i j k l, y (Sum.inl (i, k)) (Sum.inl (j, l)) =
          ∑ m, coordOf c y i j m * Algebra.leftMulMatrix b (b m) k l) ∧
       y.toBlocks₁₁.det * y (Sum.inr ()) (Sum.inr ()) = 1 ∧
       ∀ P ∈ S, ∀ k, MvPolynomial.aeval
          (fun p : (Fin n × Fin n) × β => coordOf c y p.1.1 p.1.2 p.2) (Q P k) = 0) := by
    have e3 : ∀ i j k l, ev (X (Sum.inl (i, k)) (Sum.inl (j, l)) -
        ∑ m, coordOf c X i j m * algebraMap ℚ _ (Algebra.leftMulMatrix ω (ω m) k l)) y =
        y (Sum.inl (i, k)) (Sum.inl (j, l)) -
          ∑ m, coordOf c y i j m * Algebra.leftMulMatrix b (b m) k l := fun i j k l => by
      set_option synthInstance.maxHeartbeats 100000 in
        simp only [ev, map_sub, map_sum, map_mul, hX, AlgHom.commutes, hL]
      simp only [X, aeval_coordOf]
    have e4 : ev (X.toBlocks₁₁.det * X (Sum.inr ()) (Sum.inr ()) - 1) y =
        y.toBlocks₁₁.det * y (Sum.inr ()) (Sum.inr ()) - 1 := by
      simp only [ev, map_sub, map_mul, hX, map_one]
      simp only [X, aeval_det]
    have e5 : ∀ P k, ev (MvPolynomial.aeval
        (fun p : (Fin n × Fin n) × β => coordOf c X p.1.1 p.1.2 p.2) (Q P k)) y =
        MvPolynomial.aeval (fun p : (Fin n × Fin n) × β => coordOf c y p.1.1 p.1.2 p.2) (Q P k) :=
      fun P k => aeval_comp_coord c y (Q P k)
    have e1 : ∀ p q, ev (X p q) y = y p q := hX
    constructor
    · intro h
      refine ⟨fun p u => ?_, fun p u => ?_, fun i j k l => ?_, ?_, fun P hP k => ?_⟩
      · rw [← e1]; exact h _ (Or.inl ⟨p, u, rfl⟩)
      · rw [← e1]; exact h _ (Or.inr (Or.inl ⟨p, u, rfl⟩))
      · rw [← sub_eq_zero, ← e3]; exact h _ (Or.inr (Or.inr (Or.inl ⟨i, j, k, l, rfl⟩)))
      · rw [← sub_eq_zero, ← e4]; exact h _ (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
      · rw [← e5]; exact h _ (Or.inr (Or.inr (Or.inr (Or.inr ⟨P, hP, k, rfl⟩))))
    · rintro ⟨a1, a2, a3, a4, a5⟩ f (⟨p, u, rfl⟩ | ⟨p, u, rfl⟩ | ⟨i, j, k, l, rfl⟩ | rfl | ⟨P, hP, k, rfl⟩)
      · rw [e1, a1]
      · rw [e1, a2]
      · rw [e3, ← a3, sub_self]
      · rw [e4, a4, sub_self]
      · rw [e5, a5 P hP]
  rw [key]
  constructor
  · rintro ⟨a1, a2, a3, a4, a5⟩
    let G : Matrix (Fin n) (Fin n) A := Matrix.of fun i j => b.equivFun.symm (coordOf c y i j)
    have hG : ∀ i j k, b.repr (G i j) k = coordOf c y i j k := fun i j k => by
      have := congrFun (b.equivFun.apply_symm_apply (coordOf c y i j)) k
      rw [Module.Basis.equivFun_apply] at this
      exact this
    have hres : res b G = y.toBlocks₁₁ := by
      ext ⟨i, k⟩ ⟨j, l⟩
      simp only [res, Matrix.of_apply, Matrix.toBlocks₁₁]
      rw [a3, leftMul_expand]
      simp only [hG]
    have hu : IsUnit G := hunit G (by rw [hres]; exact IsUnit.of_mul_eq_one _ a4)
    obtain ⟨g, hg⟩ := hu
    refine ⟨g, fun P hP => ?_, ?_⟩
    · apply b.repr.injective
      ext k
      rw [hQ P R A b hb, hg]
      simp only [hG]
      simpa using a5 P hP k
    · have hi := hinv g
      rw [hg, hres] at hi
      have hcorner : y (Sum.inr ()) (Sum.inr ()) =
          (res b ((g⁻¹ : GL (Fin n) A) : Matrix (Fin n) (Fin n) A)).det := by
        calc y (Sum.inr ()) (Sum.inr ()) = (y.toBlocks₁₁.det *
              (res b ((g⁻¹ : GL (Fin n) A) : Matrix (Fin n) (Fin n) A)).det) * y (Sum.inr ()) (Sum.inr ()) := by
              rw [hi, one_mul]
          _ = (y.toBlocks₁₁.det * y (Sum.inr ()) (Sum.inr ())) *
              (res b ((g⁻¹ : GL (Fin n) A) : Matrix (Fin n) (Fin n) A)).det := by ring
          _ = _ := by rw [a4, one_mul]
      ext (p | u) (q | v)
      · simp only [emb, Matrix.fromBlocks_apply₁₁, hg, hres, Matrix.toBlocks₁₁, Matrix.of_apply]
      · simp only [emb, Matrix.fromBlocks_apply₁₂, a1, Matrix.zero_apply]
      · simp only [emb, Matrix.fromBlocks_apply₂₁, a2, Matrix.zero_apply]
      · simp only [emb, Matrix.fromBlocks_apply₂₂, Matrix.of_apply]
        exact hcorner
  · rintro ⟨g, hg, rfl⟩
    have hco : ∀ i j k, coordOf c (emb b g) i j k = b.repr ((g : Matrix (Fin n) (Fin n) A) i j) k :=
      fun i j k => by
        simp only [coordOf, emb, Matrix.fromBlocks_apply₁₁, res, Matrix.of_apply, hc]
        exact sum_leftMul_one b _ k
    refine ⟨fun p u => ?_, fun p u => ?_, fun i j k l => ?_, ?_, fun P hP k => ?_⟩
    · simp [emb]
    · simp [emb]
    · simp only [hco]
      rw [← leftMul_expand]
      simp only [emb, Matrix.fromBlocks_apply₁₁, res, Matrix.of_apply]
    · simp only [emb, Matrix.toBlocks_fromBlocks₁₁, Matrix.fromBlocks_apply₂₂, Matrix.of_apply]
      exact hinv g
    · simp only [hco]
      rw [← hQ P R A b hb (fun ij : Fin n × Fin n => (g : Matrix (Fin n) (Fin n) A) ij.1 ij.2) k, hg P hP]
      simp

end GlobalTheory.ClassFin.WeilEqs
end

-- bundled from Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ExistsReynoldsOfCompletelyReducibleStatement
section
open Matrix GlobalTheory.ClassFin
open scoped Kronecker ComplexOrder TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_reynolds_of_completelyReducible' : ∀ (V : Type) [AddCommGroup V] [Module ℂ V] (S : Set (V →ₗ[ℂ] V)), (∀ U : Submodule ℂ V, (∀ s ∈ S, ∀ v ∈ U, s v ∈ U) → ∃ U' : Submodule ℂ V, (∀ s ∈ S, ∀ v ∈ U', s v ∈ U') ∧ IsCompl U U') → ∃ Rey : V →ₗ[ℂ] V, (∀ v, ∀ s ∈ S, s (Rey v) = Rey v) ∧ (∀ v, (∀ s ∈ S, s v = v) → Rey v = v) ∧ (∀ v, ∀ s ∈ S, Rey (s v) = Rey v) ∧ (∀ v, v - Rey v ∈ Submodule.span ℂ {x | ∃ s ∈ S, ∃ w, x = s w - w}) ∧ (∀ T : V →ₗ[ℂ] V, (∀ s ∈ S, ∀ v, T (s v) = s (T v)) → ∀ v, Rey (T v) = T (Rey v)) ∧ ∀ U : Submodule ℂ V, (∀ s ∈ S, ∀ v ∈ U, s v ∈ U) → ∀ v ∈ U, Rey v ∈ U := by
  first | exact @GlobalTheory.ClassFin.exists_reynolds_of_completelyReducible | exact GlobalTheory.ClassFin.exists_reynolds_of_completelyReducible | (intros; apply GlobalTheory.ClassFin.exists_reynolds_of_completelyReducible <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ExistsUnitNormEqOfAlgHom
section
open NumberField IsDedekindDomain Polynomial GlobalTheory.QNorm GlobalTheory.CNorm
open scoped WithZero TensorProduct

namespace GlobalTheory.CNorm

theorem exists_unit_norm_eq_of_algHom : ∀ (K A : Type) [Field K] [CommRing A] [Algebra K A] [Module.Finite K A] [IsReduced A] (ψ : A →ₐ[K] K) (c : K), c ≠ 0 → ∃ y : Aˣ, Algebra.norm K (y : A) = c := by
  intro K A _ _ _ _ _ ψ c hc
  have : IsArtinianRing A := IsArtinianRing.of_finite K A
  have : IsSemisimpleRing A := IsArtinianRing.isSemisimpleRing_of_isReduced A
  obtain ⟨e, he, hI⟩ := IsSemisimpleRing.ideal_eq_span_idempotent (RingHom.ker ψ)
  have he0 : ψ e = 0 := by
    have : e ∈ RingHom.ker ψ := by rw [hI]; exact Ideal.subset_span rfl
    exact this
  set f : A := 1 - e with hf
  have hψf : ψ f = 1 := by simp [hf, he0]
  have hmul : ∀ a : A, f * a = ψ a • f := by
    intro a
    have h1 : a - algebraMap K A (ψ a) ∈ RingHom.ker ψ := by
      simp [RingHom.mem_ker]
    rw [hI, Ideal.mem_span_singleton'] at h1
    obtain ⟨b, hb⟩ := h1
    have h2 : f * (b * e) = 0 := by
      have : e * e = e := he
      rw [hf]; linear_combination (-b) * this
    rw [hb, mul_sub, sub_eq_zero] at h2
    rw [h2, Algebra.smul_def, mul_comm]
  have hff : f * f = f := by rw [hmul, hψf, one_smul]
  have hinv : (1 + (c - 1) • f) * (1 + (c⁻¹ - 1) • f) = 1 := by
    have : (c⁻¹ - 1) + (c - 1) + (c - 1) * (c⁻¹ - 1) = 0 := by field_simp; ring
    rw [mul_add, add_mul, add_mul, smul_mul_smul_comm, hff]
    simp only [one_mul, mul_one]
    rw [add_assoc, ← add_smul, ← add_smul]
    have h3 : c - 1 + (c⁻¹ - 1 + (c - 1) * (c⁻¹ - 1)) = 0 := by linear_combination this
    rw [h3]; simp
  refine ⟨⟨1 + (c - 1) • f, 1 + (c⁻¹ - 1) • f, hinv, by rw [mul_comm, hinv]⟩, ?_⟩
  rw [Algebra.norm_apply]
  have hT : LinearMap.mul K A (1 + (c - 1) • f) = LinearMap.transvection ψ.toLinearMap ((c - 1) • f) := by
    ext a
    simp [LinearMap.transvection.apply, hmul, smul_smul, mul_comm]
  change LinearMap.det (LinearMap.mul K A (1 + (c - 1) • f)) = c
  rw [hT, LinearMap.transvection.det]
  simp [hψf]

end GlobalTheory.CNorm
end

-- bundled from Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ExistsUnitValuedTernaryLtOne
section
open NumberField IsDedekindDomain
open scoped Matrix WithZero

namespace GlobalTheory.LocalQuad

namespace TernaryResidue


open MvPolynomial in
theorem exists_ne_zero_sum_eq_zero {k : Type*} [Field k] [Finite k] (a : Fin 3 → Fin 3 → k) :
    ∃ x : Fin 3 → k, x ≠ 0 ∧ ∑ i, ∑ j, a i j * x i * x j = 0 := by
  first
  | exact @_root_.GlobalTheory.NonzeroIsotropic.exists_nonzero_isotropic
  | exact _root_.GlobalTheory.NonzeroIsotropic.exists_nonzero_isotropic
  | (apply _root_.GlobalTheory.NonzeroIsotropic.exists_nonzero_isotropic <;> assumption)
  | (intros; apply _root_.GlobalTheory.NonzeroIsotropic.exists_nonzero_isotropic <;> assumption)
  | (intros; apply @_root_.GlobalTheory.NonzeroIsotropic.exists_nonzero_isotropic <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.NonzeroIsotropic.exists_nonzero_isotropic ..)

end TernaryResidue

theorem exists_unit_valued_ternary_lt_one (F : Type) [Field F] [NumberField F]
    (v : HeightOneSpectrum (𝓞 F)) (c : Fin 3 → Fin 3 → v.adicCompletion F)
    (hc : ∀ i j, Valued.v (c i j) ≤ 1) :
    ∃ x : Fin 3 → v.adicCompletion F, (∀ i, Valued.v (x i) ≤ 1) ∧ (∃ i, Valued.v (x i) = 1) ∧
      Valued.v (∑ i, ∑ j, c i j * x i * x j) < 1 := by
  classical
  choose r hr using fun i j => GlobalTheory.Idele.exists_valued_sub_le v (hc i j) 1
  let ι : 𝓞 F →+* v.adicCompletion F :=
    (algebraMap F (v.adicCompletion F)).comp (algebraMap (𝓞 F) F)
  have hι : ∀ y : 𝓞 F, Valued.v (ι y) = v.valuation F (algebraMap (𝓞 F) F y) := fun y =>
    GlobalTheory.Idele.valued_algebraMap v _
  have hle : ∀ y : 𝓞 F, Valued.v (ι y) ≤ 1 := fun y => by
    rw [hι]; exact v.valuation_le_one y
  have hlt : ∀ y : 𝓞 F, Valued.v (ι y) < 1 ↔ y ∈ v.asIdeal := fun y => by
    rw [hι]; exact v.valuation_lt_one_iff_mem y
  have hr' : ∀ i j, Valued.v (c i j - ι (r i j)) < 1 := fun i j => by
    refine (hr i j).trans_lt ?_
    rw [← WithZero.exp_zero, WithZero.exp_lt_exp]
    norm_num
  haveI : v.asIdeal.IsMaximal := v.isMaximal
  letI : Field (𝓞 F ⧸ v.asIdeal) := Ideal.Quotient.field _
  haveI : Finite (𝓞 F ⧸ v.asIdeal) := Ideal.finiteQuotientOfFreeOfNeBot _ v.ne_bot
  obtain ⟨x, hx0, hx⟩ := TernaryResidue.exists_ne_zero_sum_eq_zero
    (k := 𝓞 F ⧸ v.asIdeal) fun i j => Ideal.Quotient.mk v.asIdeal (r i j)
  choose y hy using fun i => Ideal.Quotient.mk_surjective (x i)
  refine ⟨fun i => ι (y i), fun i => hle _, ?_, ?_⟩
  · obtain ⟨i, hi⟩ := Function.ne_iff.1 hx0
    refine ⟨i, le_antisymm (hle _) (not_lt.1 fun h => hi ?_)⟩
    rw [← hy i]
    exact Ideal.Quotient.eq_zero_iff_mem.2 ((hlt _).1 h)
  · have hmem : (∑ i, ∑ j, r i j * y i * y j) ∈ v.asIdeal := by
      rw [← Ideal.Quotient.eq_zero_iff_mem, ← hx]
      set_option synthInstance.maxHeartbeats 100000 in
        simp only [map_sum, map_mul, hy]
    have hsplit : ∑ i, ∑ j, c i j * ι (y i) * ι (y j) =
        ι (∑ i, ∑ j, r i j * y i * y j) +
          ∑ i, ∑ j, (c i j - ι (r i j)) * ι (y i) * ι (y j) := by
      set_option synthInstance.maxHeartbeats 100000 in
        simp only [map_sum, map_mul, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
      ring
    rw [hsplit]
    refine Valuation.map_add_lt _ ((hlt _).2 hmem) ?_
    refine Valuation.map_sum_lt _ one_ne_zero fun i _ => Valuation.map_sum_lt _ one_ne_zero
      fun j _ => ?_
    rw [map_mul, map_mul]
    exact (mul_le_of_le_one_right' (hle _)).trans_lt
      ((mul_le_of_le_one_right' (hle _)).trans_lt (hr' i j))

end GlobalTheory.LocalQuad
end

-- bundled from Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.IsClosedImageSLUnderGeneratingInvariantsStatement
section
open Matrix GlobalTheory.ClassFin
open scoped Kronecker ComplexOrder TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isClosed_image_SL_under_generating_invariants : ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (Γ : Set (Matrix ι ι ℂ)) (Rey : MvPolynomial (ι × ι) ℂ →ₗ[ℂ] MvPolynomial (ι × ι) ℂ) (κ : Type) [Fintype κ] (Φ : κ → MvPolynomial (ι × ι) ℂ), IsReynolds Γ Rey → (∀ g ∈ Γ, g.det = 1) → (∀ k, IsInv Γ (Φ k)) → (∀ f, IsInv Γ f → f ∈ Algebra.adjoin ℂ (Set.range Φ)) → IsClosed {z : κ → ℂ | ∃ y : Matrix ι ι ℂ, y.det = 1 ∧ z = fun k => evC (Φ k) y} := by
  first | exact @GlobalTheory.ClassFin.isClosed_image_invariants | exact GlobalTheory.ClassFin.isClosed_image_invariants | (intros; apply GlobalTheory.ClassFin.isClosed_image_invariants <;> assumption)
end

