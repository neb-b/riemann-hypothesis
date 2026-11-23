module

public import Mathlib
public import Formalism.LocalRingCardinality.DataTheta
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.OscActMonomialOfUnique
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0146
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0026
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsIndexIdeal
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0064
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0141
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0140
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0135
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.GlESymmApply
public import Formalism.FrobeniusOrbits.RealSubfieldLeCompositum
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.T2SpaceNumberFieldInfiniteAdeles
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.UnitaryStabilizerAnisotropicVectorEquivComplemen
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0061
public import Formalism.LocalToGlobal.IndefiniteReal.Bundle0016
public import Formalism.LocalToGlobal.IndefiniteReal.SubgroupCharExtensionOneApply
public import Formalism.LocalToGlobal.IndefiniteReal.ScalarOnPartsFull
public import Formalism.LocalToGlobal.IndefiniteReal.OrthogonalComplementCharacterisation
public import Formalism.LocalToGlobal.IndefiniteReal.IndefiniteWeightData
public import Formalism.LocalToGlobal.IndefiniteReal.HeckeTupleStatement
public import Formalism.LocalRingCardinality.Bundle0007
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0148

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.InnerLieActionAdjointGaussianPolynomial
section
open Formalism.BasicNotions Formalism.BasicNotions.TH GlobalTheory.Mem.Osc GlobalTheory.OscGauss Matrix
open scoped ComplexOrder

namespace GlobalTheory.OscGauss

variable {P Q : ℕ}

theorem act_sum_blocks (Z : Mat P Q) (A E : Matrix (Fin P) (Fin Q) ℂ) (x d : Ix P Q → ℂ) (t : ℂ) :
    (∑ i, ∑ k, Z (.inl k) (.inl i) * (x (.inl i) * d (.inl k) + ∑ j, A i j * E k j + if i = k then t / 2 else 0) -
      ∑ i, ∑ j, Z (.inr j) (.inl i) * (x (.inl i) * (x (.inr j) * t + ∑ m, A m j * d (.inl m)) +
        (∑ k, A i k * (x (.inr j) * d (.inr k) + ∑ m, A m j * E m k) + A i j * t))) +
    (∑ j, ∑ i, Z (.inl i) (.inr j) * E i j -
      ∑ j, ∑ k, Z (.inr k) (.inr j) * (x (.inr k) * d (.inr j) + ∑ i, A i k * E i j + if j = k then t / 2 else 0)) =
    (Z.trace / 2 + dS Z A x) * t + (∑ i, ∑ j, dA Z A i j * E i j + ∑ l, dX Z A x l * d l) := by
  induction Z using Matrix.induction_on' with
  | h_zero =>
    have h11 : (0 : Mat P Q).toBlocks₁₁ = 0 := rfl
    have h12 : (0 : Mat P Q).toBlocks₁₂ = 0 := rfl
    have h21 : (0 : Mat P Q).toBlocks₂₁ = 0 := rfl
    have h22 : (0 : Mat P Q).toBlocks₂₂ = 0 := rfl
    simp [dS, dA, dX, h11, h12, h21, h22]
  | h_add Z W hZ hW =>
    have h11 : (Z + W).toBlocks₁₁ = Z.toBlocks₁₁ + W.toBlocks₁₁ := rfl
    have h12 : (Z + W).toBlocks₁₂ = Z.toBlocks₁₂ + W.toBlocks₁₂ := rfl
    have h21 : (Z + W).toBlocks₂₁ = Z.toBlocks₂₁ + W.toBlocks₂₁ := rfl
    have h22 : (Z + W).toBlocks₂₂ = Z.toBlocks₂₂ + W.toBlocks₂₂ := rfl
    have hS : dS (Z + W) A x = dS Z A x + dS W A x := by
      simp only [dS, h21, h22, Matrix.add_mul, Matrix.trace_add, Matrix.add_mulVec, dotProduct_add]; ring
    have hA : dA (Z + W) A = dA Z A + dA W A := by
      simp only [dA, h11, h12, h21, h22, Matrix.add_mul, Matrix.mul_add]; abel
    have hX : dX (Z + W) A x = dX Z A x + dX W A x := by
      simp only [dX, h11, h21, h22, Matrix.add_mul, Matrix.mul_add, Matrix.add_mulVec, Matrix.sub_mulVec,
        Matrix.vecMul_add]
      ext (i | j) <;> simp <;> ring
    simp only [hS, hA, hX, Matrix.add_apply, Pi.add_apply, add_mul, Finset.sum_add_distrib, Matrix.trace_add]
    simp only [add_mul] at hZ hW
    linear_combination hZ + hW
  | h_std_basis a b c =>
    rcases a with a | a <;> rcases b with b | b <;>
    simp [dS, dA, dX, Matrix.toBlocks₁₁, Matrix.toBlocks₁₂, Matrix.toBlocks₂₁, Matrix.toBlocks₂₂,
      Matrix.single_apply, Matrix.mul_apply, Matrix.trace, Matrix.mulVec, Matrix.vecMul, dotProduct, ite_and,
      Fintype.sum_sum_type]
    · simp only [mul_add, Finset.mul_sum, mul_assoc]
      split_ifs <;> ring
    · rw [Finset.sum_comm (f := fun i k => A i a * (c * A b k) * E i k)]
      simp only [mul_add, Finset.mul_sum, Finset.sum_add_distrib, mul_assoc, mul_left_comm]
      ring
    · simp only [mul_add, Finset.mul_sum, mul_assoc, mul_left_comm]
      split_ifs <;> ring


open MvPolynomial GlobalTheory.Oscillator in
theorem inner_omAct0_adjZ : ∀ (P Q : ℕ) (F : Fock (Ix P Q)) (A : Matrix (Fin P) (Fin Q) ℂ) (x : Ix P Q → ℂ) (v : F.H), (∀ (i : Fin P) (f : MvPolynomial (Ix P Q) ℂ), inner ℂ (F.ι (MvPolynomial.X (Sum.inl i) * f)) v = x (Sum.inl i) * inner ℂ (F.ι f) v + ∑ j, A i j * inner ℂ (F.ι (MvPolynomial.pderiv (Sum.inr j) f)) v) → (∀ (j : Fin Q) (f : MvPolynomial (Ix P Q) ℂ), inner ℂ (F.ι (MvPolynomial.X (Sum.inr j) * f)) v = x (Sum.inr j) * inner ℂ (F.ι f) v + ∑ i, A i j * inner ℂ (F.ι (MvPolynomial.pderiv (Sum.inl i) f)) v) → ∀ (Z : Mat P Q) (f : MvPolynomial (Ix P Q) ℂ), inner ℂ (F.ι (omAct0 P Q (adjZ Z) f)) v = (Z.trace / 2 + dS Z A x) * inner ℂ (F.ι f) v + (∑ i, ∑ j, dA Z A i j * inner ℂ (F.ι (MvPolynomial.pderiv (Sum.inl i) (MvPolynomial.pderiv (Sum.inr j) f))) v + ∑ l, dX Z A x l * inner ℂ (F.ι (MvPolynomial.pderiv l f)) v) := by
  intro P Q F A x v h1 h2 Z f
  have hh : ∀ (p : Prop) [Decidable p], inner ℂ (F.ι (if p then (1 / 2 : ℂ) • f else 0)) v =
      if p then inner ℂ (F.ι f) v / 2 else 0 := by
    intro p _
    split_ifs
    · rw [map_smul, inner_smul_left]; simp [map_ofNat]; ring
    · simp
  have hd : ∀ k j : Fin Q, inner ℂ (F.ι (pderiv (Sum.inr k) (X (Sum.inr j) * f))) v =
      x (.inr j) * inner ℂ (F.ι (pderiv (.inr k) f)) v +
        ∑ m, A m j * inner ℂ (F.ι (pderiv (.inl m) (pderiv (.inr k) f))) v +
        if k = j then inner ℂ (F.ι f) v else 0 := by
    intro k j
    rw [← h2, Derivation.leibniz, smul_eq_mul, smul_eq_mul, map_add (f := _), inner_add_left, pderiv_X]
    by_cases h : k = j
    · subst h; simp
    · simp [h, Ne.symm h]
  rw [← act_sum_blocks Z A (fun i j => inner ℂ (F.ι (pderiv (Sum.inl i) (pderiv (Sum.inr j) f))) v) x
    (fun l => inner ℂ (F.ι (pderiv l f)) v) (inner ℂ (F.ι f) v), omAct0_eq, oscAct_apply]
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [LinearMap.sum_apply, LinearMap.smul_apply, map_sum, map_smul, sum_inner, inner_smul_left,
    adjZ_apply, Fintype.sum_sum_type, Finset.sum_add_distrib, LinearMap.add_apply, map_add, inner_add_left]
  simp only [unitOp_inl_inl, unitOp_inl_inr, unitOp_inr_inl, unitOp_inr_inr, map_add (f := _), map_sub, map_neg,
    inner_add_left, inner_sub_left, inner_neg_left, hh, h1, h2, hd, sgn, map_mul, Complex.conj_conj,
    Int.cast_one, Int.cast_neg, map_one, sub_eq_add_neg, ← Finset.sum_neg_distrib]
  have hc : ∀ (j : Fin Q) (i : Fin P), pderiv (Sum.inr j) (pderiv (Sum.inl i) f) =
      pderiv (Sum.inl i) (pderiv (Sum.inr j) f) := fun j i => pderiv_pderiv_comm _ _ _
  rw [add_add_add_comm]
  simp only [hc, mul_add (A _ _), Finset.sum_add_distrib, mul_ite, mul_zero, Finset.sum_ite_eq',
    Finset.mem_univ, if_true]
  congr 2 <;> refine Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => ?_ <;> ring

end GlobalTheory.OscGauss
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LawOfSquaresSelfDualSplitLattice
section
set_option autoImplicit false

namespace GlobalTheory.LawOfSquares

open NumberField IsDedekindDomain Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.IndefiniteRowSideFullHecke.DeterminantCharacterIdentity GlobalTheory.BetaEx GlobalTheory.ClassScalarCompare

variable {E : Type} [Field E] [NumberField E] {n : ℕ}

omit [NumberField E] in
theorem idlE_mul' (I J : Ideal (𝓞 E)) : idlE (I * J) = idlE I * idlE J :=
  Submodule.map_mul I J (Algebra.ofId (𝓞 E) E)

theorem idlE_inj : Function.Injective (idlE : Ideal (𝓞 E) → Submodule (𝓞 E) E) :=
  Submodule.map_injective_of_injective (f := Algebra.linearMap (𝓞 E) E) (FaithfulSMul.algebraMap_injective (𝓞 E) E)

omit [NumberField E] in
theorem detSpan_std_le : detSpan (stdLat E n) ≤ 1 := by
  refine Submodule.span_le.2 ?_
  rintro _ ⟨v, hv, rfl⟩
  choose b hb using fun i => (mem_std _).1 (hv i)
  refine Submodule.mem_one.2 ⟨(Matrix.of fun i j => b j i).det, ?_⟩
  rw [RingHom.map_det]
  congr 1
  ext i j
  exact hb j i

omit [NumberField E] in
theorem smul_single_mem (m : 𝓞 E) (i : Fin n) : m • (Pi.single i 1 : Fin n → E) ∈ stdLat E n :=
  Submodule.smul_mem _ _ ((mem_std _).2 fun j => by
    rw [Pi.single_apply]
    split_ifs
    exacts [⟨1, map_one _⟩, ⟨0, map_zero _⟩])

omit [NumberField E] in
theorem pow_mem_detSpan {M : Submodule (𝓞 E) (Fin n → E)} (m : 𝓞 E)
    (h : ∀ i, m • (Pi.single i 1 : Fin n → E) ∈ M) : ((m ^ n : 𝓞 E) : E) ∈ detSpan M := by
  have := det_mem (M := M) ((m : E) • (1 : Matrix (Fin n) (Fin n) E)) (fun i => by
    convert h i using 1
    ext j
    simp [Matrix.one_apply, Pi.single_apply, eq_comm, Algebra.smul_def])
  rw [Matrix.det_smul, Matrix.det_one, mul_one, Fintype.card_fin] at this
  simpa using this

omit [NumberField E] in
theorem detSpan_std : detSpan (stdLat E n) = 1 := by
  refine le_antisymm detSpan_std_le ?_
  rw [Submodule.one_le]
  simpa using pow_mem_detSpan (M := stdLat E n) 1 (smul_single_mem 1)

omit [NumberField E] in
theorem exists_idlE {M : Submodule (𝓞 E) E} (h : M ≤ 1) : ∃ 𝔟 : Ideal (𝓞 E), M = idlE 𝔟 := by
  refine ⟨M.comap (Algebra.linearMap (𝓞 E) E), (Submodule.map_comap_eq_of_le ?_).symm⟩
  intro x hx
  exact Submodule.mem_one.1 (h hx)

variable [IsCMField E]

theorem absNorm_conjId (H : Host E) (I : Ideal (𝓞 E)) : Ideal.absNorm (conjId H I) = Ideal.absNorm I := by
  rw [Ideal.absNorm_apply, Ideal.absNorm_apply, Submodule.cardQuot_apply, Submodule.cardQuot_apply]
  exact (Nat.card_congr (Ideal.quotientEquiv I (conjId H I) H.bar rfl).toEquiv).symm

theorem eq_of_le_of_absNorm {I J : Ideal (𝓞 E)} (h : I ≤ J) (h0 : J ≠ ⊥) (e : Ideal.absNorm I = Ideal.absNorm J) :
    I = J := by
  obtain ⟨K, rfl⟩ := Ideal.dvd_iff_le.2 h
  have h1 : Ideal.absNorm J ≠ 0 := by rwa [Ne, Ideal.absNorm_eq_zero_iff]
  rw [map_mul, mul_eq_left₀ h1, Ideal.absNorm_eq_one_iff] at e
  rw [e, Ideal.mul_top]

theorem index_eq (H : Host E) (L : Submodule (𝓞 E) (Fin n → E)) (cc : Ideal (𝓞 E))
    (hL : (⟨L⟩ : GenLat E n).Unimod) (hS : GenLat.SplitSupp H (⟨L⟩ : GenLat E n))
    (h1 : cc ⊔ conjId H cc = ⊤) (h2 : detSpan L * idlE (conjId H cc) = idlE cc) :
    ∃ k : ℕ, k ≠ 0 ∧ (L ⊓ stdLat E n).toAddSubgroup.relIndex L.toAddSubgroup = Ideal.absNorm cc * k ^ 2 := by
  have hb : Bdd (stdLat E n ⊔ L) := by
    obtain ⟨k, hk, h⟩ := bdd_of_unimod ⟨L⟩ hL
    refine ⟨k, hk, fun v hv => ?_⟩
    obtain ⟨x, hx, y, hy, rfl⟩ := Submodule.mem_sup.1 hv
    rw [smul_add]
    exact add_mem (Submodule.smul_mem _ _ hx) (h y hy)
  obtain ⟨𝔞, a0, e1, e2, e3⟩ := GlobalTheory.T.exists_common_indexIdeal_inf_sup_lattices E n L (stdLat E n) hb fun m _ => exists_smul_std m
  obtain ⟨𝔟, e4⟩ := exists_idlE ((detSpan_mono (inf_le_right : L ⊓ stdLat E n ≤ _)).trans detSpan_std_le)
  rw [detSpan_std, smul_eq_idlE_mul] at e2
  rw [e4, smul_eq_idlE_mul] at e1
  have c0 := absNorm_ne_zero h1
  have c1 : cc ≠ ⊥ := by rwa [Ne, Ideal.absNorm_eq_zero_iff] at c0
  have c2 : conjId H cc ≠ ⊥ := by rwa [Ne, ← Ideal.absNorm_eq_zero_iff, absNorm_conjId]
  have e5 : 𝔟 * conjId H cc = 𝔞 * cc := idlE_inj (by rw [idlE_mul', idlE_mul', e1, mul_assoc, h2])
  have e6 : Ideal.absNorm 𝔟 = Ideal.absNorm 𝔞 := by
    have := congrArg Ideal.absNorm e5
    rw [map_mul, map_mul, absNorm_conjId] at this
    exact mul_right_cancel₀ c0 this
  have pair : ∀ v ∈ L ⊓ stdLat E n, ∀ w ∈ stdLat E n ⊔ L,
      ∑ j, IsCMField.complexConj E (v j) * w j ∈ (algebraMap (𝓞 E) E).range := by
    intro v hv w hw
    obtain ⟨x, hx, y, hy, rfl⟩ := Submodule.mem_sup.1 hw
    simp only [Pi.add_apply, mul_add, Finset.sum_add_distrib]
    refine add_mem (Subring.sum_mem _ fun j _ => ?_) ((hL v).1 hv.1 y hy)
    obtain ⟨a, ha⟩ := (mem_std _).1 hv.2 j
    obtain ⟨b, hb⟩ := (mem_std _).1 hx j
    exact mul_mem ⟨H.bar a, by rw [← ha]; exact H.bar_eq a⟩ ⟨b, hb⟩
  have e7 : idlE (conjId H 𝔟) * detSpan (stdLat E n ⊔ L) ≤ 1 := by
    refine Submodule.mul_le.2 fun x hx y hy => ?_
    rw [← conjMod_idlE, mem_conjMod, ← e4] at hx
    have := GlobalTheory.T.detSpan_conj_mul_integral_of_integral_pairing E n _ _ pair _ hx y hy
    rw [IsCMField.complexConj_apply_apply] at this
    exact Submodule.mem_one.2 this
  have e8 : conjId H 𝔟 = 𝔞 := by
    refine eq_of_le_of_absNorm ?_ a0 (by rw [absNorm_conjId, e6])
    have : idlE (conjId H 𝔟) ≤ idlE 𝔞 := by
      calc idlE (conjId H 𝔟) = idlE (conjId H 𝔟) * 1 := (mul_one _).symm
        _ = idlE 𝔞 * (idlE (conjId H 𝔟) * detSpan (stdLat E n ⊔ L)) := by rw [e2]; ring
        _ ≤ idlE 𝔞 * 1 := mul_le_mul_right e7 _
        _ = _ := mul_one _
    exact (Submodule.map_le_map_iff_of_injective (FaithfulSMul.algebraMap_injective (𝓞 E) E) _ _).1 this
  obtain ⟨𝔡, rfl⟩ : cc ∣ 𝔟 :=
    (Ideal.isCoprime_iff_sup_eq.2 h1).dvd_of_dvd_mul_right ⟨𝔞, by rw [e5, mul_comm]⟩
  have e9 : conjId H 𝔡 = 𝔡 := by
    have : conjId H (cc * 𝔡) = conjId H cc * conjId H 𝔡 := Ideal.map_mul _ _ _
    rw [← e8, this] at e5
    apply mul_left_cancel₀ (mul_ne_zero c1 c2)
    calc _ = conjId H cc * conjId H 𝔡 * cc := by ring
      _ = _ := by rw [← e5]; ring
  have d0 : Ideal.absNorm 𝔡 ≠ 0 := by
    rintro h
    rw [map_mul, h, mul_zero, eq_comm, Ideal.absNorm_eq_zero_iff] at e6
    exact a0 e6
  obtain ⟨m, -, -, m2, m3⟩ := hS
  have hm : m ^ n ∈ 𝔡 := by
    have := pow_mem_detSpan (M := L ⊓ stdLat E n) m fun i => ⟨m2 (Submodule.smul_mem_smul
      (Ideal.mem_span_singleton_self m) (by simpa using smul_single_mem (E := E) 1 i)), smul_single_mem m i⟩
    rw [e4] at this
    obtain ⟨y, hy, e⟩ := this
    have : y = m ^ n := RingOfIntegers.ext e
    rw [← this]
    exact Ideal.le_of_dvd (Dvd.intro_left cc rfl) hy
  obtain ⟨k, hk⟩ := _root_.GlobalTheory.SquareNorm.isSquare_absNorm E H 𝔡 (by rwa [Ne, Ideal.absNorm_eq_zero_iff] at d0) e9
    fun P hP hle => m3 P hP (hP.mem_of_pow_mem (r := m) n (hle hm))
  refine ⟨k, by rintro rfl; exact d0 hk, ?_⟩
  rw [← e3, ← e6, map_mul, hk, sq]

theorem law_of_squares : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (n r : ℕ), Odd r → ∀ (L : Submodule (𝓞 E) (Fin n → E)) (cc : Ideal (𝓞 E)), (⟨L⟩ : GenLat E n).Unimod → GenLat.SplitSupp H (⟨L⟩ : GenLat E n) → cc ⊔ cc.map (H.bar : 𝓞 E →+* 𝓞 E) = ⊤ → Submodule.span (𝓞 E) (detSet L) * idlE (cc.map (H.bar : 𝓞 E →+* 𝓞 E)) = idlE cc → ∃ q : ℚ, 0 < q ∧ q ^ 2 * (((L ⊓ Formalism.L2.Pj.stdLat E n).toAddSubgroup.addSubgroupOf L.toAddSubgroup).index : ℚ) ^ r = (Ideal.absNorm cc : ℚ) := by
  intro E _ _ _ H n r ⟨s, hs⟩ L cc hL hS h1 h2
  obtain ⟨k, k0, e⟩ := index_eq H L cc hL hS h1 h2
  have e' : ((L ⊓ Formalism.L2.Pj.stdLat E n).toAddSubgroup.addSubgroupOf L.toAddSubgroup).index =
      Ideal.absNorm cc * k ^ 2 := e
  have c0 : Ideal.absNorm cc ≠ 0 := absNorm_ne_zero (H := H) h1
  rw [e', hs]
  generalize Ideal.absNorm cc = N at c0
  have : (0 : ℚ) < N := by positivity
  have : (0 : ℚ) < k := by positivity
  refine ⟨((N : ℚ) ^ s * (k : ℚ) ^ (2 * s + 1))⁻¹, by positivity, ?_⟩
  push_cast
  field_simp
  ring

end GlobalTheory.LawOfSquares
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LevelPrimeUnramifiedUniformizer
section
noncomputable section

namespace GlobalTheory.LevelUnram

open Formalism.BasicNotions Formalism.L2.Forms Formalism.UG Formalism.L2.GlobalTheoryTheory.LocalLatticeBases NumberField IsDedekindDomain Matrix GlobalTheory.LevelHecke
open scoped TensorProduct

theorem exists_mul_eq {R : Type} [CommRing R] [IsDedekindDomain R] (P : Ideal R) (hP : P.IsPrime) (t : R)
    (ht : t ∈ P) (ht2 : t ∉ P ^ 2) (a : R) (ha : a ∈ P) : ∃ s b, s ∉ P ∧ s * a = t * b := by
  obtain ⟨I, hI⟩ : P ∣ Ideal.span {t} := by
    rw [Ideal.dvd_iff_le, Ideal.span_singleton_le_iff_mem]; exact ht
  have hIP : ¬ I ≤ P := by
    intro h
    apply ht2
    rw [← Ideal.span_singleton_le_iff_mem, hI, sq]
    exact Ideal.mul_mono_right h
  obtain ⟨s, hs, hsP⟩ := SetLike.not_le_iff_exists.1 hIP
  have h1 : a * s ∈ Ideal.span {t} := by rw [hI]; exact Ideal.mul_mem_mul ha hs
  obtain ⟨b, hb⟩ := Ideal.mem_span_singleton.1 h1
  exact ⟨s, b, hsP, by rw [mul_comm, hb]⟩

variable {E : Type} [Field E] [NumberField E]

theorem absNorm_span_invol (s : 𝓞 E →+* 𝓞 E) (hs : ∀ x, s (s x) = x) (a : 𝓞 E) :
    Ideal.absNorm (Ideal.span {s a}) = Ideal.absNorm (Ideal.span {a}) := by
  let e : 𝓞 E ≃+* 𝓞 E := RingEquiv.ofRingHom s s (RingHom.ext hs) (RingHom.ext hs)
  let e' : 𝓞 E ≃ₐ[ℤ] 𝓞 E := AlgEquiv.ofRingEquiv (f := e) (fun n => by simp)
  rw [Ideal.absNorm_span_singleton, Ideal.absNorm_span_singleton]
  exact congrArg Int.natAbs (Algebra.norm_eq_of_algEquiv e' a)

theorem notMem_sq {ι : Type} [Fintype ι] (s : 𝓞 E →+* 𝓞 E) (hs : ∀ x, s (s x) = x) (a : 𝓞 E) (p : ℕ) (hp : p.Prime)
    (ha : a * s a = (p : 𝓞 E)) (hcard : 2 * Fintype.card ι = Module.finrank ℚ E) (P : ι → Ideal (𝓞 E))
    (hmax : ∀ i, (P i).IsMaximal) (hinj : Function.Injective P) (haP : ∀ i, a ∈ P i)
    (hN : ∀ i, Ideal.absNorm (P i) = p) (i : ι) (hsa : s a ∉ P i) : (p : 𝓞 E) ∉ P i ^ 2 := by
  classical
  intro hmem
  have hnorm : Ideal.absNorm (Ideal.span {a}) = p ^ Fintype.card ι := by
    have h1 : Ideal.absNorm (Ideal.span {a}) ^ 2 = (p ^ Fintype.card ι) ^ 2 := by
      rw [← pow_mul, mul_comm, hcard, ← RingOfIntegers.rank, ← Ideal.absNorm_span_natCast, ← ha,
        ← Ideal.span_singleton_mul_span_singleton, map_mul, absNorm_span_invol s hs, sq]
    exact Nat.pow_left_injective two_ne_zero h1
  have ha2 : a ∈ P i ^ 2 := by
    obtain ⟨y, m, hm, h⟩ := (hmax i).exists_inv hsa
    have h1 : a = y * (p : 𝓞 E) + m * a := by
      rw [← ha]
      linear_combination (-a) * h
    rw [h1]
    refine Ideal.add_mem _ (Ideal.mul_mem_left _ _ hmem) ?_
    rw [sq]
    exact Ideal.mul_mem_mul hm (haP i)
  have hcop : ∀ j k, j ≠ k → IsCoprime (P j) (P k) := fun j k hjk =>
    Ideal.isCoprime_iff_sup_eq.2 ((hmax j).coprime_of_ne (hmax k) (fun h => hjk (hinj h)))
  have hd1 : P i ^ 2 ∣ Ideal.span {a} := by
    rw [Ideal.dvd_iff_le, Ideal.span_singleton_le_iff_mem]
    exact ha2
  have hd2 : ∏ j ∈ Finset.univ.erase i, P j ∣ Ideal.span {a} := by
    refine Finset.prod_dvd_of_coprime (fun j _ k _ hjk => hcop j k hjk) ?_
    intro j _
    rw [Ideal.dvd_iff_le, Ideal.span_singleton_le_iff_mem]
    exact haP j
  have hc : IsCoprime (P i ^ 2) (∏ j ∈ Finset.univ.erase i, P j) :=
    IsCoprime.pow_left (IsCoprime.prod_right fun j hj => hcop i j (Finset.ne_of_mem_erase hj).symm)
  have hd := map_dvd Ideal.absNorm (hc.mul_dvd hd1 hd2)
  rw [hnorm, map_mul, map_pow, map_prod, hN i,
    Finset.prod_congr rfl (fun j _ => hN j), Finset.prod_const, ← pow_add,
    Nat.pow_dvd_pow_iff_le_right hp.one_lt] at hd
  have h3 := Finset.card_erase_add_one (Finset.mem_univ i)
  rw [Finset.card_univ] at h3
  omega

theorem finrank_E (D : D7) : 2 * D.R.f = Module.finrank ℚ D.host.E := by
  letI := D.host.cmStar
  have h1 := Module.finrank_mul_finrank ℚ D.host.F D.host.E
  have h2 : Module.finrank ℚ D.host.F = D.R.f := by
    rw [D.host.finrank_hostF, Ranks.f, Ranks.n]
  rw [D.sp.cm.deg2, h2] at h1
  omega

theorem unram (D : D7) (u : D.what₂.Word) (A : AtTTied u) (v : (D.mem u).A.vT) :
    Unram (A.res v) (((D.mem u).A.T : ℕ) : 𝓞 D.host.E) := by
  let s : 𝓞 D.host.E →+* 𝓞 D.host.E := RingOfIntegers.mapRingHom (sigD D : D.host.E →+* D.host.E)
  have hsc : ∀ x, (s x : D.host.E) = D.host.conj (x : D.host.E) := fun x => forms_involution_eq_host_conj _
  have hs : ∀ x, s (s x) = x := fun x => RingOfIntegers.ext (by rw [hsc, hsc, host_conj_involutive])
  have ha : A.piU * s A.piU = (((D.mem u).A.T : ℕ) : 𝓞 D.host.E) := by
    apply RingOfIntegers.ext
    have := A.piU_norm
    rw [← hsc] at this
    simpa using this
  have hT0 : A.res v (((D.mem u).A.T : ℕ) : 𝓞 D.host.E) = 0 := by
    rw [← ha, map_mul, A.res_pi, zero_mul]
  have h2 := notMem_sq s hs A.piU _ (D.mem u).A.T_prime ha (by rw [(D.mem u).A.card_vT]; exact finrank_E D)
    (fun w => RingHom.ker (A.res w)) (fun w => RingHom.ker_isMaximal_of_surjective _ (A.res_surj w))
    (fun w w' h => by
      apply A.eV.injective
      apply Subtype.ext
      apply HeightOneSpectrum.ext
      ext x
      have h' : RingHom.ker (A.res w) = RingHom.ker (A.res w') := h
      rw [A.res_v, A.res_v, ← RingHom.mem_ker, ← RingHom.mem_ker, h'])
    (fun w => A.res_pi w)
    (fun w => by
      rw [Ideal.absNorm_apply, Submodule.cardQuot_apply,
        Nat.card_congr (RingHom.quotientKerEquivOfSurjective (A.res_surj w)).toEquiv, Nat.card_eq_fintype_card,
        (D.mem u).A.card_Fv w])
    v (A.res_conj v _ (hsc _))
  exact ⟨hT0, fun a h => exists_mul_eq _ (RingHom.ker_isPrime _) _ hT0 h2 a h⟩

end GlobalTheory.LevelUnram

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LintegralOrthogonalComplementPairIndepGroupEleme
section
open NumberField IsDedekindDomain MeasureTheory Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.GaugeEx
open scoped TensorProduct NNReal ENNReal

namespace GlobalTheory.TwoStepIndep

theorem lintegral_pairOf_eq : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (R : Type) [CommRing R] [Algebra F R] [TopologicalSpace R] [IsTopologicalRing R] [T2Space R] [LocallyCompactSpace R] [SecondCountableTopology R] [MeasurableSpace R] [BorelSpace R] (M : ℕ) (J : Matrix (Fin (M + 1)) (Fin (M + 1)) E) (x : Fin 1 → Fin (M + 1) → E) (a : F) (B : Matrix (Fin (M + 1)) (Fin M) E) (J' : Matrix (Fin M) (Fin M) E) (m' : Measure (Fin 1 → Fin M → R ⊗[F] E)), StepData σ J x a B J' → IsInvTup R σ J' m' → ∀ (y : Fin 1 → Fin (M + 1) → R ⊗[F] E) (g k : HA R σ J), g • ratTup (F := F) R x = k • ratTup (F := F) R x → ∀ f : (Fin 2 → Fin (M + 1) → R ⊗[F] E) → ℝ≥0∞, Measurable f → ∫⁻ y', f (pairOf R σ J B y g y') ∂m' = ∫⁻ y', f (pairOf R σ J B y k y') ∂m' := by
  intro F E _ _ _ _ _ σ hCM R _ _ _ _ _ _ _ _ _ M J x a B J' m' hS hinv y g k hgk f hf
  obtain ⟨-, ⟨e, he, -⟩, -⟩ := GlobalTheory.FrameStep.frameStep F E σ hCM R M J x a B J' hS
  have hmem : k⁻¹ * g ∈ Hstab R σ J x := by
    have : (k⁻¹ * g) • ratTup (F := F) R x = ratTup (F := F) R x := by
      rw [mul_smul, hgk, inv_smul_smul]
    exact this
  have hrel : FrameRelR R σ J J' B (k⁻¹ * g) (e ⟨k⁻¹ * g, hmem⟩) := he ⟨k⁻¹ * g, hmem⟩
  set u := e ⟨k⁻¹ * g, hmem⟩ with hu
  have hkey : ∀ y', pairOf R σ J B y g y' = pairOf R σ J B y k (u • y') := by
    intro y'
    have hg : g = k * (k⁻¹ * g) := by group
    have h1 : ((HA.mat R σ J g : GL (Fin (M + 1)) (R ⊗[F] E)) : Matrix (Fin (M + 1)) (Fin (M + 1)) (R ⊗[F] E)) =
        ((HA.mat R σ J k : GL (Fin (M + 1)) (R ⊗[F] E)) : Matrix (Fin (M + 1)) (Fin (M + 1)) (R ⊗[F] E)) *
        ((HA.mat R σ J (k⁻¹ * g) : GL (Fin (M + 1)) (R ⊗[F] E)) :
          Matrix (Fin (M + 1)) (Fin (M + 1)) (R ⊗[F] E)) := by
      conv_lhs => rw [hg]
      rfl
    have h2 : (u • y') 0 = ((HA.mat R σ J' u : GL (Fin M) (R ⊗[F] E)) :
        Matrix _ _ (R ⊗[F] E)).mulVec (y' 0) := rfl
    unfold FrameRelR at hrel
    unfold pairOf
    rw [h1, h2]
    simp only [Matrix.mulVec_mulVec]
    rw [Matrix.mul_assoc]
    exact congrArg (fun A : Matrix (Fin (M + 1)) (Fin M) (R ⊗[F] E) =>
      (![y 0, (((HA.mat R σ J k : GL (Fin (M + 1)) (R ⊗[F] E)) :
        Matrix (Fin (M + 1)) (Fin (M + 1)) (R ⊗[F] E)) * A).mulVec (y' 0)] :
          Fin 2 → Fin (M + 1) → R ⊗[F] E)) hrel
  have hc : Continuous fun y' => pairOf R σ J B y k y' := by
    refine continuous_pi ?_
    rw [Fin.forall_fin_two]
    refine ⟨continuous_const, ?_⟩
    have h0 : Continuous fun y' : Fin 1 → Fin M → R ⊗[F] E => y' 0 := continuous_apply 0
    show Continuous fun y' : Fin 1 → Fin M → R ⊗[F] E =>
      ((HA.mat R σ J k : GL (Fin (M + 1)) (R ⊗[F] E)) :
        Matrix (Fin (M + 1)) (Fin (M + 1)) (R ⊗[F] E)).mulVec ((B.map (inclR R)).mulVec (y' 0))
    exact continuous_const.matrix_mulVec (continuous_const.matrix_mulVec h0)
  have hm : Measurable fun X : Fin 1 → Fin M → R ⊗[F] E => u • X :=
    (continuous_const_smul u).measurable
  simp_rw [hkey]
  conv_rhs => rw [← hinv u]
  exact (lintegral_map (hf.comp hc.measurable) hm).symm

end GlobalTheory.TwoStepIndep
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LocallyCompactSecondCountableT2
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.MemberAdelicTop

theorem locallyCompact_secondCountable_t2 : ∀ (D : D7) (V : HSp D), LocallyCompactSpace (GA D V) ∧ SecondCountableTopology (GA D V) ∧ T2Space (GA D V) := fun D V =>
  GlobalTheory.AdelicUnitaryTop.lcsc_adelicUnitary D.host.F D.host.E D.sp.cm.sig V.rank V.gram

end GlobalTheory.MemberAdelicTop
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.NonemptyStandardLocalHaarMeasuresStatement
section
open NumberField IsDedekindDomain MeasureTheory Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.GaugeEx
open scoped TensorProduct NNReal ENNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.nonempty_standardLocalHaarMeasures : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E], ∀ (d : ℕ) (b : Module.Basis (Fin d) F E), Nonempty (StdMeas b) := by
  first | exact @GlobalTheory.GaugeEx.StdExist.nonempty_stdMeas | exact GlobalTheory.GaugeEx.StdExist.nonempty_stdMeas | (intros; apply GlobalTheory.GaugeEx.StdExist.nonempty_stdMeas <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.RestrictedProductMeasureSmulFactorsEqSmulStatement
section
open NumberField IsDedekindDomain MeasureTheory Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.GaugeEx
open scoped TensorProduct NNReal ENNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.restrictedProduct_measure_smul_factors_eq_smul : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E], ∀ (d : ℕ) (b : Module.Basis (Fin d) F E) (n M : ℕ) (ν : Measure (Fin n → Fin M → AF F ⊗[F] E)) (mi : Measure (Fin n → Fin M → Ainf F ⊗[F] E)) (mv : ∀ v : HeightOneSpectrum (𝓞 F), Measure (Fin n → Fin M → Fv F v ⊗[F] E)) (ri : ℝ≥0) (r : HeightOneSpectrum (𝓞 F) → ℝ≥0), IsProd b ν mi mv → (Function.mulSupport r).Finite → IsProd b ((ri * ∏ᶠ v, r v) • ν) (ri • mi) (fun v => r v • mv v) := by
  first | exact @GlobalTheory.GaugeEx.ProdScale.isProd_smul | exact GlobalTheory.GaugeEx.ProdScale.isProd_smul | (intros; apply GlobalTheory.GaugeEx.ProdScale.isProd_smul <;> assumption)
end

