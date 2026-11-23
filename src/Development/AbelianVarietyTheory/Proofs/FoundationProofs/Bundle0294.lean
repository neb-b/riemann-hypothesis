module

public import Mathlib
public import Formalism.SharpRestriction.LevelLetterCocycles.Bundle0004
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0008
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0009
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0011
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0198
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0396
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0577
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0284
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0253
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0269
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IntertwinerUnipotentInvariant
public import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.Cartan
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0597
public import Development.AbelianVarietyTheory.Definitions.Foundations.HermitianSpaceBaseLatticeEqFrameLattice
public import Development.AbelianVarietyTheory.Definitions.Foundations.NormSumPairRankZeroOfCurveCoordNorm
public import Formalism.PairingDivisors.StatementH
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0224
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0264
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.CmThetaTaylorCoeffAlgebraicAndConjugate
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0255
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0263
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0272
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0254
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0230
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0235
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0274
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0288

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.LabelEqOfSuppAdds
section
noncomputable section

namespace GlobalTheory.GLp.Supp

open Polynomial GlobalTheory.GLq GlobalTheory.GLp Formalism.MainNotions.ArithmeticCylinders TensorProduct GlobalTheory.GLq.Opp MonoidAlgebra
open scoped Classical

variable {g : ℕ} [Fact g.Prime]

theorem alg_apply {G U : Type} [Group G] [Fintype G] [AddCommGroup U] [Module ℂ U] (ρ : Representation ℂ G U)
    (a : MonoidAlgebra ℂ G) (w : U) : ρ.asAlgebraHom a w = ∑ x, a.coeff x • ρ x w := by
  induction a using MonoidAlgebra.induction_linear with
  | zero => simp
  | add a b ha hb => simp [ha, hb, add_smul, Finset.sum_add_distrib]
  | single x c =>
    rw [Finset.sum_eq_single x]
    · simp
    · intro y _ hy
      simp [Finsupp.single_eq_of_ne hy]
    · simp

theorem entN_par {a b : ℕ} (x : Gn g a) (B : Matrix (Fin a) (Fin b) (ZMod g)) (y : Gn g b) (i j : ℕ) :
    (i < a → j < a → entN (par finSumFinEquiv x B y).val i j = entN x.val i j) ∧
    (a ≤ i → j < a → entN (par finSumFinEquiv x B y).val i j = 0) ∧
    (entN (par finSumFinEquiv x B y).val (a + i) (a + j) = entN y.val i j) ∧
    (B = 0 → i < a → a ≤ j → entN (par finSumFinEquiv x B y).val i j = 0) := by
  refine ⟨fun hi hj => ?_, fun hi hj => ?_, ?_, fun hB hi hj => ?_⟩
  · have := par_apply finSumFinEquiv x B y (.inl ⟨i, hi⟩) (.inl ⟨j, hj⟩)
    rw [entN, entN, dite_eq_left ⟨by omega, by omega⟩, dite_eq_left ⟨hi, hj⟩]
    exact this
  · unfold entN
    split_ifs with h
    · have := par_apply finSumFinEquiv x B y (.inr ⟨i - a, by omega⟩) (.inl ⟨j, hj⟩)
      rw [Matrix.fromBlocks_apply₂₁, Matrix.zero_apply] at this
      rw [← this]
      exact congrArg₂ _ (Fin.ext (by simp; omega)) (Fin.ext (by simp))
    · rfl
  · unfold entN
    by_cases h : i < b ∧ j < b
    · rw [dite_eq_left ⟨by omega, by omega⟩, dite_eq_left h]
      exact par_apply finSumFinEquiv x B y (.inr ⟨i, h.1⟩) (.inr ⟨j, h.2⟩)
    · rw [dite_eq_right (by omega), dite_eq_right h]
  · unfold entN
    split_ifs with h
    · have := par_apply finSumFinEquiv x B y (.inl ⟨i, hi⟩) (.inr ⟨j - a, by omega⟩)
      subst hB
      rw [Matrix.fromBlocks_apply₁₂, Matrix.zero_apply] at this
      rw [← this]
      exact congrArg₂ _ (Fin.ext (by simp)) (Fin.ext (by simp; omega))
    · rfl

theorem ext_entN {n : ℕ} {x y : Gn g n} (h : ∀ i j : ℕ, i < n → j < n → entN x.val i j = entN y.val i j) :
    x = y := by
  ext i j
  rw [← ParInd.entN_self x.val, ← ParInd.entN_self y.val, h _ _ i.2 j.2]

section Local

variable {n : ℕ} {V : Type} [AddCommGroup V] [Module ℂ V]

def repK (π : Representation ℂ (GL (Fin n) ℚ_[g]) V) : Representation ℂ (Gn g n) (fixK1 π) where
  toFun x := (π (lift g n x)).restrict fun _ hv => padicIntGL_smul_mem_principalCongruenceFixed π hv _
  map_one' := LinearMap.ext fun v => Subtype.ext (lift_one_apply π v.2)
  map_mul' x y := LinearMap.ext fun v => Subtype.ext (lift_mul_apply π v.2 x y)

theorem repK_red (π : Representation ℂ (GL (Fin n) ℚ_[g]) V) (k : GL (Fin n) ℤ_[g]) (v : fixK1 π) :
    (repK π (red g n k) v : V) = π (inc g n k) v :=
  inc_eq_of_red_eq π v.2 (red_invFun _)

theorem repK_alg (π : Representation ℂ (GL (Fin n) ℚ_[g]) V) (a : MonoidAlgebra ℂ (Gn g n)) (v : fixK1 π) :
    ((repK π).asAlgebraHom a v : V) = actK π a v := by
  rw [alg_apply, actK, LinearMap.sum_apply, Submodule.coe_sum]
  rfl

end Local

section Ind

variable {a b : ℕ} {V W W' : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
  [AddCommGroup W'] [Module ℂ W']

def parZ (x : GL (Fin a) ℤ_[g]) (B : Matrix (Fin a) (Fin b) ℤ_[g]) (y : GL (Fin b) ℤ_[g]) : GL (Fin (a + b)) ℤ_[g] where
  val := Matrix.reindex finSumFinEquiv finSumFinEquiv (Matrix.fromBlocks x.val B 0 y.val)
  inv := Matrix.reindex finSumFinEquiv finSumFinEquiv (Matrix.fromBlocks (x⁻¹).val
    (-((x⁻¹).val * B * (y⁻¹).val)) 0 (y⁻¹).val)
  val_inv := by
    simp only [Matrix.reindex_apply, Matrix.submatrix_mul_equiv, Matrix.fromBlocks_multiply]
    simp [← Matrix.mul_assoc]
  inv_val := by
    simp only [Matrix.reindex_apply, Matrix.submatrix_mul_equiv, Matrix.fromBlocks_multiply]
    simp [Matrix.mul_assoc]

theorem parZ_apply (x : GL (Fin a) ℤ_[g]) (B : Matrix (Fin a) (Fin b) ℤ_[g]) (y : GL (Fin b) ℤ_[g])
    (i j : Fin a ⊕ Fin b) : (parZ x B y).val (finSumFinEquiv i) (finSumFinEquiv j) =
      Matrix.fromBlocks x.val B 0 y.val i j := by
  simp [parZ]

theorem red_parZ (x : GL (Fin a) ℤ_[g]) (B : Matrix (Fin a) (Fin b) ℤ_[g]) (y : GL (Fin b) ℤ_[g]) :
    red g _ (parZ x B y) =
      par finSumFinEquiv (red g a x) (B.map (PadicInt.toZMod (p := g))) (red g b y) := by
  ext i j
  obtain ⟨i, rfl⟩ := finSumFinEquiv.surjective i
  obtain ⟨j, rfl⟩ := finSumFinEquiv.surjective j
  rw [par_apply, ParInd.red_val, Matrix.map_apply, parZ_apply]
  rcases i with i | i <;> rcases j with j | j <;> simp [ParInd.red_val]

theorem exists_dual_right (z : W ⊗[ℂ] W') (hz : z ≠ 0) : ∃ P : W ⊗[ℂ] W' →ₗ[ℂ] W, P z ≠ 0 ∧
    ∀ (A : W →ₗ[ℂ] W) (y : W ⊗[ℂ] W'), P (TensorProduct.map A LinearMap.id y) = A (P y) := by
  let β := Module.Basis.ofVectorSpace ℂ W'
  have h1 : TensorProduct.equivFinsuppOfBasisRight β z ≠ 0 := by simpa using hz
  obtain ⟨i, hi⟩ := Finsupp.ne_iff.1 h1
  refine ⟨Finsupp.lapply i ∘ₗ (TensorProduct.equivFinsuppOfBasisRight β).toLinearMap, hi, fun A y => ?_⟩
  induction y using TensorProduct.induction_on with
  | zero => simp
  | tmul u v => simp
  | add u v hu hv => simp only [map_add (f := _), hu, hv]

theorem exists_dual_left (z : W ⊗[ℂ] W') (hz : z ≠ 0) : ∃ P : W ⊗[ℂ] W' →ₗ[ℂ] W', P z ≠ 0 ∧
    ∀ (A : W' →ₗ[ℂ] W') (y : W ⊗[ℂ] W'), P (TensorProduct.map LinearMap.id A y) = A (P y) := by
  obtain ⟨P, h1, h2⟩ := exists_dual_right (TensorProduct.comm ℂ W W' z) (by simpa using hz)
  refine ⟨P ∘ₗ (TensorProduct.comm ℂ W W').toLinearMap, h1, fun A y => ?_⟩
  rw [LinearMap.comp_apply, LinearMap.comp_apply, ← h2]
  congr 1
  induction y using TensorProduct.induction_on with
  | zero => simp
  | tmul u v => simp
  | add u v hu hv => simp only [map_add (f := _), hu, hv]

end Ind

end GlobalTheory.GLp.Supp
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.MemStabLocStdLatticeIffHtFinEqOne
section
noncomputable section

namespace GlobalTheory.AdelicU

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.UG

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem exists_sub_mem_intLoc (v : HeightOneSpectrum (𝓞 F)) (y : Fv F v ⊗[F] E) :
    ∃ x : E, y - (1 : Fv F v) ⊗ₜ[F] x ∈ intLoc F E v := by
  induction y using TensorProduct.induction_on with
  | zero => exact ⟨0, by simp⟩
  | add y z hy hz =>
    obtain ⟨x, hx⟩ := hy
    obtain ⟨x', hx'⟩ := hz
    refine ⟨x + x', ?_⟩
    rw [TensorProduct.tmul_add, add_sub_add_comm]
    exact add_mem hx hx'
  | tmul a e =>
    obtain ⟨m, hm, he⟩ := exists_integral_multiples ℤ ℚ ({e} : Finset E)
    have he' : IsIntegral ℤ (m • e) := he e (Finset.mem_singleton_self e)
    have hmF : (m : F) ≠ 0 := by exact_mod_cast hm
    have hO : IsOpen (v.adicCompletionIntegers F : Set (Fv F v)) := Valued.isOpen_valuationSubring _
    have hcont : Continuous fun z : Fv F v => (m : F)⁻¹ • a - z := continuous_sub_left _
    obtain ⟨k, hk⟩ := (HeightOneSpectrum.denseRange_algebraMap (R := 𝓞 F) F v).exists_mem_open
      (hO.preimage hcont) ⟨(m : F)⁻¹ • a, by simp⟩
    refine ⟨k • (m • e), ?_⟩
    have hk' : (m : F)⁻¹ • a - algebraMap F (Fv F v) k ∈ v.adicCompletionIntegers F := hk
    have h := tmul_mem_intLoc (E := E) hk' ⟨m • e, he'⟩
    convert h using 1
    change _ = ((m : F)⁻¹ • a - algebraMap F (Fv F v) k) ⊗ₜ[F] (m • e)
    rw [TensorProduct.sub_tmul, TensorProduct.smul_tmul, Algebra.algebraMap_eq_smul_one, TensorProduct.smul_tmul,
      ← Int.cast_smul_eq_zsmul F m e, inv_smul_smul₀ hmF]

theorem isIntegral_of_absBar_le_one (v : HeightOneSpectrum (𝓞 F)) (x : E)
    (hx : ∀ τ : E →ₐ[F] FvBar F v, absBar F v (τ x) ≤ 1) :
    ∃ p : Polynomial (v.valuationSubringAtPrime F), p.Monic ∧
      p.eval₂ ((algebraMap F E).comp (v.valuationSubringAtPrime F).subtype) x = 0 := by
  classical
  have hint : IsIntegral F x := Algebra.IsIntegral.isIntegral x
  have hmon := minpoly.monic hint
  have h1 : (minpoly F x).map (algebraMap F (FvBar F v)) ∈ Polynomial.lifts (valBar F v).integer.subtype := by
    refine Polynomial.Splits.mem_lift_of_roots_mem_range (IsAlgClosed.splits _) (hmon.map _) _ fun a ha => ?_
    have ha' : a ∈ (minpoly F x).rootSet (FvBar F v) := by
      rw [Polynomial.rootSet_def]; simpa [Polynomial.aroots_def] using ha
    rw [← Algebra.IsAlgebraic.range_eval_eq_rootSet_minpoly] at ha'
    obtain ⟨τ, rfl⟩ := ha'
    exact ⟨⟨τ x, hx τ⟩, rfl⟩
  have h2 : minpoly F x ∈ Polynomial.lifts (v.valuationSubringAtPrime F).subtype := by
    rw [Polynomial.lifts_iff_coeff_lifts] at h1 ⊢
    intro n
    obtain ⟨c, hc⟩ := h1 n
    have h3 : absBar F v (algebraMap F (FvBar F v) ((minpoly F x).coeff n)) ≤ 1 := by
      rw [← Polynomial.coeff_map, ← hc]; exact c.2
    rw [IsScalarTower.algebraMap_apply F (Fv F v) (FvBar F v), absBar_algebraMap] at h3
    have h4 : Valued.v (algebraMap F (Fv F v) ((minpoly F x).coeff n)) ≤ 1 :=
      Valued.toNormedField.norm_le_one_iff.1 (by exact_mod_cast h3)
    refine ⟨⟨(minpoly F x).coeff n, ?_⟩, rfl⟩
    rw [HeightOneSpectrum.valuationSubringAtPrime_eq_valuationSubring]
    exact (HeightOneSpectrum.valuedAdicCompletion_eq_valuation' v _).symm.trans_le h4
  obtain ⟨q, hq, -, hqm⟩ := Polynomial.lifts_and_degree_eq_and_monic h2 hmon
  refine ⟨q, hqm, ?_⟩
  rw [← Polynomial.eval₂_map, hq]
  exact minpoly.aeval F x

theorem one_tmul_mem_intLoc (v : HeightOneSpectrum (𝓞 F)) (x : E)
    (hx : absFin F v ((1 : Fv F v) ⊗ₜ[F] x) ≤ 1) : (1 : Fv F v) ⊗ₜ[F] x ∈ intLoc F E v := by
  let : Algebra (v.valuationSubringAtPrime F) E :=
    ((algebraMap F E).comp (v.valuationSubringAtPrime F).subtype).toAlgebra
  have : IsScalarTower (𝓞 F) (v.valuationSubringAtPrime F) E := IsScalarTower.of_algebraMap_eq fun _ => rfl
  have h1 : IsIntegral (v.valuationSubringAtPrime F) x :=
    isIntegral_of_absBar_le_one v x fun τ => by simpa using (absFin_le_iff F v).1 hx τ
  obtain ⟨⟨s, hs⟩, h2⟩ := IsIntegral.exists_multiple_integral_of_isLocalization v.asIdeal.primeCompl x h1
  have h3 : IsIntegral ℤ ((s : F) • x) := isIntegral_trans _ h2
  have hv : v.valuation F (s : F) = 1 :=
    (HeightOneSpectrum.valuation_eq_one_iff_notMem v).2 hs
  have hs0 : (s : F) ≠ 0 := fun e => by simp [e] at hv
  have h4 : algebraMap F (Fv F v) (s : F)⁻¹ ∈ v.adicCompletionIntegers F :=
    (HeightOneSpectrum.valuedAdicCompletion_eq_valuation' v (s : F)⁻¹).trans_le (by rw [map_inv₀, hv, inv_one])
  have h := tmul_mem_intLoc (E := E) h4 ⟨_, h3⟩
  convert h using 1
  change _ = (algebraMap F (Fv F v) (s : F)⁻¹) ⊗ₜ[F] ((s : F) • x)
  rw [Algebra.algebraMap_eq_smul_one, TensorProduct.smul_tmul, inv_smul_smul₀ hs0]

theorem mem_intLoc_iff_absFin_le_one {v : HeightOneSpectrum (𝓞 F)} {y : Fv F v ⊗[F] E} :
    y ∈ intLoc F E v ↔ absFin F v y ≤ 1 := by
  refine ⟨absFin_le_one_of_mem_intLoc, fun hy => ?_⟩
  obtain ⟨x, hx⟩ := exists_sub_mem_intLoc v y
  have h1 : absFin F v ((1 : Fv F v) ⊗ₜ[F] x) ≤ 1 := by
    have := absFin_add_le F v y (-(y - (1 : Fv F v) ⊗ₜ[F] x))
    rw [absFin_neg, ← sub_eq_add_neg, sub_sub_cancel] at this
    exact this.trans (max_le hy (absFin_le_one_of_mem_intLoc hx))
  simpa using add_mem hx (one_tmul_mem_intLoc v x h1)

theorem algebraMap_basis_repr {ι : Type} [Fintype ι] [DecidableEq ι] (b : Module.Basis ι F E)
    (v : HeightOneSpectrum (𝓞 F)) (y : Fv F v ⊗[F] E) (i : ι) :
    algebraMap (Fv F v) (FvBar F v) ((Algebra.TensorProduct.basis (Fv F v) b.traceDual).repr y i) =
      ∑ τ : E →ₐ[F] FvBar F v, finEmb F v τ y * τ (b i) := by
  induction y using TensorProduct.induction_on with
  | zero => simp
  | add y z hy hz => simp only [map_add (f := _), Finsupp.add_apply, hy, hz, add_mul, Finset.sum_add_distrib]
  | tmul a e =>
    rw [Algebra.TensorProduct.basis_repr_tmul, Finsupp.smul_apply, Finsupp.mapRange_apply, smul_eq_mul, map_mul,
      ← IsScalarTower.algebraMap_apply, Module.Basis.traceDual_repr_apply, Algebra.traceForm_apply,
      trace_eq_sum_embeddings, Finset.mul_sum]
    refine Finset.sum_congr rfl fun τ _ => ?_
    rw [finEmb_tmul, map_mul]; ring

theorem absFin_eq_zero_iff {v : HeightOneSpectrum (𝓞 F)} {y : Fv F v ⊗[F] E} : absFin F v y = 0 ↔ y = 0 := by
  refine ⟨fun hy => ?_, fun h => by rw [h, absFin_zero]⟩
  have h0 : ∀ τ : E →ₐ[F] FvBar F v, finEmb F v τ y = 0 := fun τ =>
    (absBar_eq_zero F v).1 (le_antisymm ((absFin_le_iff F v).1 hy.le τ) zero_le)
  let b := Module.finBasis F E
  refine (Algebra.TensorProduct.basis (Fv F v) b.traceDual).ext_elem fun i => ?_
  refine (algebraMap (Fv F v) (FvBar F v)).injective ?_
  rw [algebraMap_basis_repr]
  simp [h0]

end GlobalTheory.AdelicU

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ThetaTranslateSeriesEqConstMulIntegralOneSeries
section
open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum
open scoped BigOperators

noncomputable section
namespace GlobalTheory.ThetaUnit
open GlobalTheory.EvenTheta GlobalTheory.ThetaTransl

section
variable {p : ℕ} [Fact p.Prime]

theorem lamC_eq (lam : Qbar →+* ℂ_[p]) {x : ℂ} (hx : x ∈ Qbar) : lamC lam x = lam ⟨x, hx⟩ := dif_pos hx

theorem lamC_mul' (lam : Qbar →+* ℂ_[p]) {x y : ℂ} (hx : x ∈ Qbar) (hy : y ∈ Qbar) :
    lamC lam (x * y) = lamC lam x * lamC lam y := by
  rw [lamC_eq lam hx, lamC_eq lam hy, lamC_eq lam (mul_mem hx hy), ← map_mul]; rfl

theorem lamC_ne_zero (lam : Qbar →+* ℂ_[p]) {x : ℂ} (hx : x ∈ Qbar) (h0 : x ≠ 0) : lamC lam x ≠ 0 := by
  rw [lamC_eq lam hx]
  intro h
  apply h0
  have := (map_eq_zero_iff lam lam.injective).1 h
  exact congrArg Subtype.val this

theorem intSer_one : IntSer (1 : PowerSeries ℂ_[p]) := by
  have := ((GlobalTheory.EvenTheta.SerRing.series_ring_laws p).2.2.1 1).2 norm_one.le
  rwa [map_one] at this

theorem intSer_pow {f : PowerSeries ℂ_[p]} (hf : IntSer f) (n : ℕ) : IntSer (f ^ n) := by
  induction n with
  | zero => simpa using intSer_one (p := p)
  | succ n ih => rw [pow_succ]; exact ((GlobalTheory.EvenTheta.SerRing.series_ring_laws p).1 _ _ ih hf).2.2

end

theorem tors_neg' {p : ℕ} {Λ : AddSubgroup ℂ} {t : ℂ} (h : GL3Theta.Tors1 p Λ t) : GL3Theta.Tors1 p Λ (-t) := by
  obtain ⟨h0, n, hn, hc, h⟩ := h
  exact ⟨by simpa using h0, n, hn, hc, by simpa using h⟩

theorem laQ_of_tors {p : ℕ} {Λ : AddSubgroup ℂ} {t : ℂ} (h : GL3Theta.Tors1 p Λ t) : InRationalLattice Λ t :=
  let ⟨_, n, hn, _, h⟩ := h; ⟨n, hn, h⟩

theorem thetaTranslateOperator_zero_eq_self (Λ : AddSubgroup ℂ) (F : ℂ → ℂ) : U1 Λ 0 F = F := by
  funext z; simp [U1]

theorem thetaTranslate_sigmaStar_at_zero_ne_zero_of_not_mem_lattice {Λ : AddSubgroup ℂ} (hlat : IsLat Λ) {t : ℂ} (ht : t ∉ Λ) :
    U1 Λ t (sgStar Λ) 0 ≠ 0 := by
  simp only [U1, zero_add]
  exact mul_ne_zero ((hlat.sg_eq_zero t).not.2 ht) (Complex.exp_ne_zero _)

theorem atU_smul' {p : ℕ} [Fact p.Prime] (g : GL3Theta.G1 p) {c : ℂ} (hc : c ∈ Qbar) {F : ℂ → ℂ} (hF : AlgEnt F) :
    AlgEnt (fun z => c * F z) ∧ g.atU (fun z => c * F z) = PowerSeries.C (lamC g.lam c) * g.atU F := by
  obtain ⟨h1, h2⟩ := (GlobalTheory.SerTransport.transport p g).2.1 c hc
  rw [← h2]
  exact ((GlobalTheory.SerTransport.transport p g).1 _ _ h1 hF).1

theorem tau_eq_C_mul : ∀ (D : D7) (p : ℕ) [Fact p.Prime] (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (g : GL3Theta.G1 p),
    GL3Theta.At D cc δ g → (∀ s : ℂ, GL3Theta.Tors1 p g.abelian₂ s → ‖GlobalTheory.EvenTheta.xAt g s‖ ≤ 1) →
    ∀ t : ℂ, GL3Theta.Tors1 p g.abelian₂ t → ∃ w : PowerSeries ℂ_[p], GlobalTheory.EvenTheta.IntSer w ∧
      PowerSeries.constantCoeff w = 1 ∧ GlobalTheory.ThetaTransl.tau g t = PowerSeries.C (GlobalTheory.ThetaTransl.cval g t) * w := by
  intro D p _ cc δ g hg hx t ht
  have hA := GlobalTheory.T.thetaTranslatePowerSeries_pow_boundedCoeffs_of_torsion D p cc δ g hg
  obtain ⟨hcc, -, hδ, hΛ, hok⟩ := hg
  have hcrv : Crv D cc δ := ⟨hcc, hδ⟩
  have hG := (GlobalTheory.InducedType.induced_type D).1
  obtain ⟨hlat, -, hdisc, -, hst⟩ := GlobalTheory.CurveLattice.lattice_of_curve D hG cc δ hcrv
  obtain ⟨⟨-, h2, h3⟩, hwp⟩ := (GlobalTheory.CurveAlgebraic.integral_j_and_algebraic_data D hG).2 cc δ hcrv
  have huse := (GlobalTheory.ThetaConj.cmTheta_taylorCoeff_algebraic_and_conjugate D cc δ hcrv).1
  simp only [tor0] at h2 h3
  rw [← hΛ] at hlat hdisc hst h2 h3 hwp huse
  have hlat' : IsLat g.abelian₂ := hlat
  have halg : ∀ x, InRationalLattice g.abelian₂ x → AlgEnt (U1 g.abelian₂ x (sgStar g.abelian₂)) := fun x hx => ⟨by
    have := hlat'.differentiable
    unfold U1
    fun_prop, huse x hx⟩
  obtain ⟨-, hw, -, hE, -⟩ := GlobalTheory.EvenTheta.DatumBasic.datum_basic p g hok hlat' h2 h3 hdisc
  have hsg : AlgEnt (sgStar g.abelian₂) := by
    have := halg 0 ⟨1, one_pos, by simp⟩
    rwa [thetaTranslateOperator_zero_eq_self] at this
  have hEi : (ePhi1 g.lam g.abelian₂ g.C g.wq)⁻¹ * ePhi1 g.lam g.abelian₂ g.C g.wq = 1 :=
    PowerSeries.inv_mul_cancel _ (by rw [hE]; exact one_ne_zero)
  have hcon : ∀ s, InRationalLattice g.abelian₂ s → PowerSeries.constantCoeff (tau g s) = cval g s ∧
      U1 g.abelian₂ s (sgStar g.abelian₂) 0 ∈ Qbar := by
    intro s hs
    obtain ⟨c, d⟩ := (GlobalTheory.SerTransport.transport p g).2.2.1 _ (halg s hs)
    refine ⟨?_, c⟩
    rw [tau, map_mul, PowerSeries.constantCoeff_inv, hE, inv_one, one_mul, d, cval]
  have hq := laQ_of_tors ht
  have hq' := laQ_of_tors (tors_neg' ht)
  obtain ⟨c1, c2⟩ := GlobalTheory.EvenTheta.Param.sqTh_atU p g hok.2.1 hlat' h2 h3 hsg t ht.1 (hwp t hq ht.1).1
  have a3 := (hcon t hq).2
  have b3 := (hcon (-t) hq').2
  have e := (atU_smul' g (mul_mem a3 b3) c1).2
  rw [funext (hlat'.sqTh_mul ht.1), ((GlobalTheory.SerTransport.transport p g).1 _ _ (halg _ hq) (halg _ hq')).1.2,
    c2, lamC_mul' _ a3 b3] at e
  have hprod : tau g t * tau g (-t) = PowerSeries.C (cval g t * cval g (-t)) *
      lineSer g.wq⁻¹ (xAt g t) := by
    simp only [tau, cval]
    linear_combination ((ePhi1 g.lam g.abelian₂ g.C g.wq)⁻¹ * (ePhi1 g.lam g.abelian₂ g.C g.wq)⁻¹) * e +
      PowerSeries.C (lamC g.lam (U1 g.abelian₂ t (sgStar g.abelian₂) 0) * lamC g.lam (U1 g.abelian₂ (-t) (sgStar g.abelian₂) 0)) *
        lineSer g.wq⁻¹ (xAt g t) * ((ePhi1 g.lam g.abelian₂ g.C g.wq)⁻¹ * ePhi1 g.lam g.abelian₂ g.C g.wq + 1) * hEi

  have hL : IntSer (lineSer g.wq⁻¹ (xAt g t)) := by
    have h1 := ((GlobalTheory.EvenTheta.SerRing.series_ring_laws p).2.2.1 (xAt g t)).2 (hx t ht)
    have h2 := (GlobalTheory.EvenTheta.SerRing.series_ring_laws p).2.2.2.1
    have h3 := ((GlobalTheory.EvenTheta.SerRing.series_ring_laws p).1 _ _ h2 h2).2.2
    have h4 := ((GlobalTheory.EvenTheta.SerRing.series_ring_laws p).1 _ _ h1 h3).2.2
    have h5 := ((GlobalTheory.EvenTheta.SerRing.series_ring_laws p).1 _ _ hw h4).2.1
    simpa [lineSer, _root_.sq, mul_assoc] using h5
  obtain ⟨n, hn, hcop, hnt⟩ := ht.2
  have hnt' : (n : ℂ) * (-t) ∈ g.abelian₂ := by rw [mul_neg]; exact neg_mem hnt
  have B1 := hA t ht n hn hnt
  have B2 := hA (-t) (tors_neg' ht) n hn hnt'
  set c := cval g t with hc
  set c' := cval g (-t) with hc'
  have hc0 : c ≠ 0 := lamC_ne_zero _ a3 (thetaTranslate_sigmaStar_at_zero_ne_zero_of_not_mem_lattice hlat' ht.1)
  have hc0' : c' ≠ 0 := lamC_ne_zero _ b3 (thetaTranslate_sigmaStar_at_zero_ne_zero_of_not_mem_lattice hlat' (tors_neg' ht).1)
  have hpow : tau g t ^ n * tau g (-t) ^ n = PowerSeries.C ((c * c') ^ n) * lineSer g.wq⁻¹ (xAt g t) ^ n := by
    rw [← mul_pow, hprod, mul_pow, map_pow]
  have hbound : ∀ k, ‖PowerSeries.coeff k (tau g t ^ n * tau g (-t) ^ n)‖ ≤ ‖c * c'‖ ^ n := by
    intro k
    rw [hpow, PowerSeries.coeff_C_mul, norm_mul, norm_pow]
    exact mul_le_of_le_one_right (by positivity) (intSer_pow hL n k)
  have G := GlobalTheory.EvenTheta.sup_norm_mul_padicComplex p _ _ _ B1 B2 hbound
  have h0' : PowerSeries.coeff 0 (tau g (-t) ^ n) = c' ^ n := by
    rw [PowerSeries.coeff_zero_eq_constantCoeff_apply, map_pow, (hcon _ hq').1]
  have hcn : 0 < ‖c'‖ ^ n := pow_pos (norm_pos_iff.2 hc0') n
  have hle : ∀ i, ‖PowerSeries.coeff i (tau g t ^ n)‖ ≤ ‖c‖ ^ n := by
    intro i
    have := G i 0
    rw [h0', norm_pow, norm_mul, mul_pow] at this
    exact le_of_mul_le_mul_right this hcn
  set s := PowerSeries.C c⁻¹ * tau g t with hs
  have hsn : IntSer (s ^ n) := by
    intro k
    rw [hs, mul_pow, ← map_pow, PowerSeries.coeff_C_mul, norm_mul, norm_pow, norm_inv]
    have hcp : 0 < ‖c‖ ^ n := pow_pos (norm_pos_iff.2 hc0) n
    calc ‖c‖⁻¹ ^ n * ‖PowerSeries.coeff k (tau g t ^ n)‖ ≤ ‖c‖⁻¹ ^ n * ‖c‖ ^ n :=
          mul_le_mul_of_nonneg_left (hle k) (by positivity)
      _ = 1 := by rw [← mul_pow, inv_mul_cancel₀ (norm_ne_zero_iff.2 hc0), one_pow]
  have hs0 : PowerSeries.constantCoeff s = 1 := by
    rw [hs, map_mul, PowerSeries.constantCoeff_C, (hcon t hq).1, inv_mul_cancel₀ hc0]
  refine ⟨s, _root_.GlobalTheory.RootInt.intSer_root p n hn hcop s hs0 hsn, hs0, ?_⟩
  rw [hs, ← mul_assoc, ← map_mul, mul_inv_cancel₀ hc0, map_one, one_mul]

end GlobalTheory.ThetaUnit
end
end

