module

public import Mathlib
public import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.ZelevinskyJacquet.ZelevinskyInterleaving.Interleave
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.WittExactSequences.Bundle0001
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0008
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.LevelChainValuations.OneSTr
public import GroundTheory.GlobalFields.TateThesis.Bundle0002
public import CompanionTheory.HarishChandraModules.KFiniteAnalyticVectors.AdmissibleSmoothVectors.Bundle0001
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0010
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ThetaCellCovers.KernelL2RowsColumns
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0011
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0012

@[expose] public section

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsOrderedForm
section
open Zc.Comb

universe u

namespace GlobalTheory.CompanionTheory.SegOrder

variable {T : Type u}

theorem exists_last_start (s : T → T) (hs : ∀ (t : T) (j : ℕ), 0 < j → s^[j] t ≠ t)
    (m : Multiset (ASeg T)) (hm : m ≠ 0) :
    ∃ a ∈ m, ∀ b ∈ m, ¬ ∃ j : ℕ, 0 < j ∧ b.start = s^[j] a.start := by
  have irr : ∀ a : ASeg T, ¬ ∃ j : ℕ, 0 < j ∧ a.start = s^[j] a.start := by
    rintro a ⟨j, hj, h⟩
    exact hs a.start j hj h.symm
  induction m using Multiset.induction_on with
  | empty => exact absurd rfl hm
  | cons x m ih =>
    by_cases hm' : m = 0
    · subst hm'
      refine ⟨x, Multiset.mem_cons_self x 0, ?_⟩
      intro b hb
      have hbx : b = x := by simpa using hb
      subst hbx
      exact irr b
    · obtain ⟨a, ham, hmax⟩ := ih hm'
      by_cases hax : ∃ j : ℕ, 0 < j ∧ x.start = s^[j] a.start
      · obtain ⟨j, hj, hxa⟩ := hax
        refine ⟨x, Multiset.mem_cons_self x m, ?_⟩
        intro b hb
        rcases Multiset.mem_cons.mp hb with rfl | hbm
        · exact irr b
        · rintro ⟨i, hi, hbx⟩
          refine hmax b hbm ⟨i + j, by omega, ?_⟩
          rw [hbx, hxa, Function.iterate_add_apply]
      · refine ⟨a, Multiset.mem_cons_of_mem ham, ?_⟩
        intro b hb
        rcases Multiset.mem_cons.mp hb with rfl | hbm
        · exact hax
        · exact hmax b hbm

theorem exists_ordered_form : ∀ {T : Type u} (s : T → T), Function.Injective s →
    (∀ (t : T) (j : ℕ), 0 < j → s^[j] t ≠ t) →
    ∀ m : Multiset (ASeg T), ∃ L : List (ASeg T), (L : Multiset (ASeg T)) = m ∧ AOrdered s L := by
  classical
  intro T s _ hs m
  induction hn : Multiset.card m generalizing m with
  | zero =>
    refine ⟨[], ?_, List.Pairwise.nil⟩
    simpa using (Multiset.card_eq_zero.mp hn).symm
  | succ n ih =>
    have hm : m ≠ 0 := by
      rintro rfl
      simp at hn
    obtain ⟨a, ham, hmax⟩ := exists_last_start s hs m hm
    have hcard : Multiset.card (m.erase a) = n := by
      rw [Multiset.card_erase_of_mem ham, hn]
      rfl
    obtain ⟨L, hL, hord⟩ := ih (m.erase a) hcard
    refine ⟨a :: L, ?_, ?_⟩
    · rw [← Multiset.cons_coe, hL]
      exact Multiset.cons_erase ham
    · refine List.pairwise_cons.mpr ⟨?_, hord⟩
      intro b hb hprec
      have hbm : b ∈ m := by
        have : b ∈ (L : Multiset (ASeg T)) := by simpa using hb
        rw [hL] at this
        exact Multiset.mem_of_mem_erase this
      exact hmax b hbm hprec.2

end GlobalTheory.CompanionTheory.SegOrder
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsPQ
section
open TensorProduct CrystallineSemistableComparison.D
open scoped LaurentPolynomial

namespace GlobalTheory.CompanionTheory.PerfClos

theorem exists_PQ : ∀ (p : ℕ) [Fact p.Prime] (S : Type) [CommRing S] (I : Ideal S), (p : S) = 0 →
    ∃ (T : Type) (_ : CommRing T) (i : S →+* T), PQ p i I := by
  intro p hpf S _ I hp
  obtain ⟨T, inst, i, hc, hb, hpow, hker⟩ := exists_perfect_radical p S I hp
  refine ⟨T, inst, i, ⟨⟨hc, hb⟩, hpow, fun x => ?_⟩⟩
  rw [hker x]
  constructor
  · rintro ⟨n, hn⟩
    refine ⟨n, Ideal.pow_mem_of_pow_mem I hn ?_⟩
    exact (Nat.lt_pow_self (Fact.out : p.Prime).one_lt).le
  · rintro ⟨k, hk⟩
    exact ⟨p ^ k, hk⟩

end GlobalTheory.CompanionTheory.PerfClos
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsRealizationOfCompatible
section
open CrystallineSemistableComparison.Pb.Kap

namespace GlobalTheory.CompanionTheory.KapRho

theorem exists_rho {Λ A B K : Type} [CommRing Λ] [CommRing A] [CommRing B] [Field K]
    (C : Chain.{1} Λ A B K) (hC : C.Good) {j : ℕ} (x : ∀ n, C.S n j) (hx : C.Comp x) :
    ∃ f : Module.Dual K (C.V j) →+ B, C.Rho x f := by
  obtain ⟨e, z, hz⟩ := hC.lift j x hx
  haveI := hC.fin j
  have hunit : IsUnit (C.ℓ : B) := by
    first
    | exact hC.unit
    | simpa using hC.unit.map C.ι
    | simpa using hC.unit.map C.o
    | simpa using (hC.unit.map C.lam).map C.ι
  obtain ⟨u, hu⟩ := hunit
  let w : C.W j := ((u⁻¹ : Bˣ) : B) ^ e • C.b j z
  let bs₀ := Module.finBasis K (C.V j)
  obtain ⟨g, hg, -⟩ := hC.basis j bs₀ w
  let f : Module.Dual K (C.V j) →+ B :=
    { toFun := fun φ => ∑ t, C.o (φ (bs₀ t)) * g t
      map_zero' := by simp
      map_add' := fun φ ψ => by simp [add_mul, Finset.sum_add_distrib] }
  refine ⟨f, fun k φ => ?_, e, z, hz, fun {m} bs => ?_⟩
  · simp [f, Finset.mul_sum, mul_assoc]
  · have key : ∑ s, f (bs.coord s) • C.μ j (bs s) = w := by
      simp only [f, AddMonoidHom.coe_mk, ZeroHom.coe_mk, Finset.sum_smul]
      rw [Finset.sum_comm, hg]
      refine Finset.sum_congr rfl fun t _ => ?_
      conv_rhs => rw [← bs.sum_repr (bs₀ t)]
      set_option synthInstance.maxHeartbeats 100000 in
        rw [map_sum, Finset.smul_sum]
      refine Finset.sum_congr rfl fun s _ => ?_
      rw [LinearMap.map_smulₛₗ, smul_smul, Module.Basis.coord_apply, mul_comm]
    rw [key, ← hu, smul_smul, ← mul_pow, Units.mul_inv, one_pow, one_smul]

end GlobalTheory.CompanionTheory.KapRho
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsRingHomPowPrimePow
section
open TensorProduct CrystallineSemistableComparison.D
open scoped LaurentPolynomial

namespace GlobalTheory.CompanionTheory.Frobenius

theorem exists_ringHom_pow_prime_pow :
    ∀ (p : ℕ) [Fact p.Prime] (A : Type) [CommRing A], (p : A) = 0 → ∀ k : ℕ,
      ∃ F : A →+* A, ∀ x, F x = x ^ p ^ k := by
  intro p hp A _ hpA k
  refine ⟨{ toFun := fun x => x ^ p ^ k
            map_one' := one_pow _
            map_mul' := fun x y => mul_pow x y _
            map_zero' := zero_pow (pow_ne_zero k hp.out.ne_zero)
            map_add' := fun x y => ?_ }, fun x => rfl⟩
  show (x + y) ^ p ^ k = x ^ p ^ k + y ^ p ^ k
  rw [add_pow_prime_pow_eq hp.out x y k, hpA]
  simp only [zero_mul, add_zero]

end GlobalTheory.CompanionTheory.Frobenius
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsSchwartzPolyMulGauss
section
noncomputable section

namespace GlobalTheory.CompanionTheory.PolyGaussSchwartz

variable {m n : ℕ}

def coord (k : Fin m × Fin n × Bool) (u : Fin m → Fin n → ℂ) : ℂ :=
  if k.2.2 then star (u k.1 k.2.1) else u k.1 k.2.1

def entryL (a : Fin m) (i : Fin n) : (Fin m → Fin n → ℂ) →L[ℝ] ℂ :=
  (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin n => ℂ) i).comp
    (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin m => Fin n → ℂ) a)

theorem coord_temperate (k : Fin m × Fin n × Bool) :
    Function.HasTemperateGrowth (coord k) := by
  obtain ⟨a, i, b⟩ := k
  cases b
  · exact (entryL a i).hasTemperateGrowth
  · exact ((Complex.conjCLE : ℂ →L[ℝ] ℂ).comp (entryL a i)).hasTemperateGrowth

theorem eval_temperate (P : MvPolynomial (Fin m × Fin n × Bool) ℂ) :
    Function.HasTemperateGrowth (fun u => MvPolynomial.eval (fun k => coord k u) P) := by
  induction P using MvPolynomial.induction_on with
  | C a =>
    have : (fun u : Fin m → Fin n → ℂ =>
        MvPolynomial.eval (fun k => coord k u) (MvPolynomial.C a)) = fun _ => a := by
      funext u; simp
    rw [this]; exact Function.HasTemperateGrowth.const a
  | add p q hp hq =>
    have : (fun u : Fin m → Fin n → ℂ => MvPolynomial.eval (fun k => coord k u) (p + q)) =
        fun u => MvPolynomial.eval (fun k => coord k u) p +
          MvPolynomial.eval (fun k => coord k u) q := by
      funext u; simp
    rw [this]; exact hp.add hq
  | mul_X p k hp =>
    have : (fun u : Fin m → Fin n → ℂ =>
        MvPolynomial.eval (fun k => coord k u) (p * MvPolynomial.X k)) =
        fun u => MvPolynomial.eval (fun k => coord k u) p * coord k u := by
      funext u; simp
    rw [this]; exact hp.mul (coord_temperate k)

def toEuclid (m n : ℕ) : (Fin m → Fin n → ℂ) ≃L[ℝ] PiLp 2 (fun _ : Fin m × Fin n => ℂ) :=
  LinearEquiv.toContinuousLinearEquiv
    (((LinearEquiv.curry ℝ ℂ (Fin m) (Fin n)).symm.trans
      (WithLp.linearEquiv 2 ℝ (Fin m × Fin n → ℂ)).symm).trans
      (LinearEquiv.smulOfNeZero ℝ _ (√2) (by positivity)))

theorem norm_toEuclid_sq (u : Fin m → Fin n → ℂ) :
    ‖toEuclid m n u‖ ^ 2 = 2 * ∑ a, ∑ i, ‖u a i‖ ^ 2 := by
  have h : toEuclid m n u = (√2 : ℝ) • (WithLp.toLp 2 (fun p : Fin m × Fin n => u p.1 p.2) :
      PiLp 2 (fun _ : Fin m × Fin n => ℂ)) := rfl
  rw [h, norm_smul, mul_pow, Real.norm_eq_abs, sq_abs, Real.sq_sqrt (by positivity),
    PiLp.norm_sq_eq_of_L2, Fintype.sum_prod_type]

theorem exists_gauss : ∃ g : SchwartzMap (Fin m → Fin n → ℂ) ℂ, ∀ u,
    g u = Complex.exp (-(2 * Real.pi * ∑ a, ∑ i, ‖u a i‖ ^ 2 : ℝ)) := by
  refine ⟨SchwartzMap.compCLMOfContinuousLinearEquiv ℂ (toEuclid m n)
    (GroundTheory.Global.gaussianSchwartz (PiLp 2 (fun _ : Fin m × Fin n => ℂ))), fun u => ?_⟩
  rw [SchwartzMap.compCLMOfContinuousLinearEquiv_apply, Function.comp_apply,
    GroundTheory.Global.gaussianSchwartz_apply, norm_toEuclid_sq, Complex.ofReal_exp]
  congr 1
  push_cast
  ring

theorem exists_schwartz_poly_mul_gauss (m n : ℕ) (P : MvPolynomial (Fin m × Fin n × Bool) ℂ) :
    ∃ φ : SchwartzMap (Fin m → Fin n → ℂ) ℂ,
      ⇑φ = fun u => MvPolynomial.eval (fun k => if k.2.2 then star (u k.1 k.2.1) else u k.1 k.2.1) P *
        Complex.exp (-(2 * Real.pi * ∑ a, ∑ i, ‖u a i‖ ^ 2 : ℝ)) := by
  obtain ⟨g, hg⟩ := exists_gauss (m := m) (n := n)
  refine ⟨SchwartzMap.smulLeftCLM ℂ (fun u => MvPolynomial.eval (fun k => coord k u) P) g, ?_⟩
  funext u
  rw [SchwartzMap.smulLeftCLM_apply_apply (eval_temperate P), hg, smul_eq_mul]
  rfl

end GlobalTheory.CompanionTheory.PolyGaussSchwartz
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsUpperMulUnitaryComplex
section
open Matrix
open scoped ComplexOrder

namespace GlobalTheory.CompanionTheory.Iwasawa

theorem exists_upper_mul_unitary_complex {n : ℕ} (Y : Matrix (Fin n) (Fin n) ℂ) (hY : IsUnit Y) :
    ∃ B R K : Matrix (Fin n) (Fin n) ℂ, B.IsUpperTriangular ∧ B * R = 1 ∧ R * B = 1 ∧
      K * Kᴴ = 1 ∧ Kᴴ * K = 1 ∧ Y = B * K := by
  let e : Fin n ≃ Fin n := Fin.revPerm
  have hYd : Y.det ≠ 0 := ((Matrix.isUnit_iff_isUnit_det Y).mp hY).ne_zero
  set Y' : Matrix (Fin n) (Fin n) ℂ := Y.submatrix e e with hY'
  have hY'u : IsUnit Y' := by
    rw [Matrix.isUnit_iff_isUnit_det, hY', Matrix.det_submatrix_equiv_self]
    exact (Matrix.isUnit_iff_isUnit_det Y).mp hY
  have hpd : (Y' * Y'ᴴ).PosDef :=
    Matrix.PosDef.mul_conjTranspose_self Y' (Matrix.vecMul_injective_iff_isUnit.mpr hY'u)
  obtain ⟨C, a, hCu, -, -, hC⟩ := CompanionTheory.D.gk.admitted.CholeskyDecomposition.exists_cholesky hpd
  have hBu : (Cᴴ.submatrix e e).IsUpperTriangular := by
    intro i j hij
    have h0 : C (e j) (e i) = 0 := hCu (Fin.rev_lt_rev.mpr hij)
    simp only [Matrix.submatrix_apply, Matrix.conjTranspose_apply]
    rw [h0, star_zero]
  have hBB : Cᴴ.submatrix e e * (Cᴴ.submatrix e e)ᴴ = Y * Yᴴ := by
    rw [Matrix.conjTranspose_submatrix, Matrix.conjTranspose_conjTranspose, Matrix.submatrix_mul_equiv, hC,
      hY', Matrix.conjTranspose_submatrix, Matrix.submatrix_mul_equiv, Matrix.submatrix_submatrix]
    have hee : (e : Fin n → Fin n) ∘ e = id := funext fun i => Fin.rev_rev i
    rw [hee, Matrix.submatrix_id_id]
  have hBd : (Cᴴ.submatrix e e).det ≠ 0 := by
    intro h0
    have := congrArg Matrix.det hBB
    rw [Matrix.det_mul, Matrix.det_mul, h0, zero_mul, Matrix.det_conjTranspose] at this
    exact mul_ne_zero hYd (star_ne_zero.mpr hYd) this.symm
  set B := Cᴴ.submatrix e e with hBdef
  have hBi : B⁻¹ * B = 1 := Matrix.nonsing_inv_mul B (isUnit_iff_ne_zero.mpr hBd)
  have hBi' : B * B⁻¹ = 1 := Matrix.mul_nonsing_inv B (isUnit_iff_ne_zero.mpr hBd)
  have hKK : (B⁻¹ * Y) * (B⁻¹ * Y)ᴴ = 1 := by
    calc (B⁻¹ * Y) * (B⁻¹ * Y)ᴴ = B⁻¹ * (Y * Yᴴ) * B⁻¹ᴴ := by
          rw [Matrix.conjTranspose_mul]; simp only [Matrix.mul_assoc]
      _ = B⁻¹ * (B * Bᴴ) * B⁻¹ᴴ := by rw [hBB]
      _ = (B⁻¹ * B) * (B⁻¹ * B)ᴴ := by
          rw [Matrix.conjTranspose_mul]; simp only [Matrix.mul_assoc]
      _ = 1 := by rw [hBi, Matrix.conjTranspose_one, Matrix.mul_one]
  refine ⟨B, B⁻¹, B⁻¹ * Y, hBu, hBi', hBi, hKK, mul_eq_one_comm.mp hKK, ?_⟩
  rw [← Matrix.mul_assoc, hBi', Matrix.one_mul]

noncomputable abbrev evalMat {ι : Type} {n : ℕ} (w : ι) :
    Matrix (Fin n) (Fin n) (ι → ℂ) →+* Matrix (Fin n) (Fin n) ℂ :=
  (Pi.evalRingHom (fun _ : ι => ℂ) w).mapMatrix

theorem evalMat_apply {ι : Type} {n : ℕ} (w : ι) (X : Matrix (Fin n) (Fin n) (ι → ℂ))
    (i j : Fin n) : evalMat w X i j = X i j w := rfl

theorem evalMat_conjTranspose {ι : Type} {n : ℕ} (w : ι) (X : Matrix (Fin n) (Fin n) (ι → ℂ)) :
    evalMat w Xᴴ = (evalMat w X)ᴴ := by
  ext i j
  simp only [evalMat_apply, Matrix.conjTranspose_apply]
  rfl

theorem matrix_ext_eval {ι : Type} {n : ℕ} {X X' : Matrix (Fin n) (Fin n) (ι → ℂ)}
    (h : ∀ w, evalMat w X = evalMat w X') : X = X' := by
  ext i j w
  have := congrFun (congrFun (h w) i) j
  rwa [evalMat_apply, evalMat_apply] at this

theorem exists_upper_mul_unitary {ι : Type} {n : ℕ} (y : GL (Fin n) (ι → ℂ)) :
    ∃ (b : GL (Fin n) (ι → ℂ)) (k : Matrix.unitaryGroup (Fin n) (ι → ℂ)),
      (∀ i j : Fin n, j < i → b.val i j = 0) ∧ y = b * Unitary.toUnits k := by
  have hu : ∀ w : ι, IsUnit (evalMat w (y : Matrix (Fin n) (Fin n) (ι → ℂ))) :=
    fun w => (Units.isUnit y).map (evalMat w)
  choose B R K hB hBR hRB hKK hKK' hY using fun w => exists_upper_mul_unitary_complex _ (hu w)
  let b : Matrix (Fin n) (Fin n) (ι → ℂ) := fun i j w => B w i j
  let r : Matrix (Fin n) (Fin n) (ι → ℂ) := fun i j w => R w i j
  let k : Matrix (Fin n) (Fin n) (ι → ℂ) := fun i j w => K w i j
  have eb : ∀ w, evalMat w b = B w := fun w => by ext i j; rw [evalMat_apply]
  have er : ∀ w, evalMat w r = R w := fun w => by ext i j; rw [evalMat_apply]
  have ek : ∀ w, evalMat w k = K w := fun w => by ext i j; rw [evalMat_apply]
  have hbr : b * r = 1 := matrix_ext_eval fun w => by rw [map_mul, eb, er, hBR w, map_one]
  have hrb : r * b = 1 := matrix_ext_eval fun w => by rw [map_mul, eb, er, hRB w, map_one]
  have hk1 : k * star k = 1 := matrix_ext_eval fun w => by
    rw [map_mul, Matrix.star_eq_conjTranspose, evalMat_conjTranspose, ek, hKK w, map_one]
  have hk2 : star k * k = 1 := matrix_ext_eval fun w => by
    rw [map_mul, Matrix.star_eq_conjTranspose, evalMat_conjTranspose, ek, hKK' w, map_one]
  refine ⟨⟨b, r, hbr, hrb⟩, ⟨k, Unitary.mem_iff.mpr ⟨hk2, hk1⟩⟩, ?_, ?_⟩
  · intro i j hij
    funext w
    exact hB w hij
  · apply Units.ext
    apply matrix_ext_eval
    intro w
    rw [Units.val_mul]
    show evalMat w (y : Matrix (Fin n) (Fin n) (ι → ℂ)) = evalMat w (b * k)
    rw [map_mul, eb, ek]
    exact hY w

end GlobalTheory.CompanionTheory.Iwasawa
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExpBlockTriangularStatement
section
open Matrix Topology Filter
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exp_block_triangular : ∀ {n : ℕ} (U Y : Matrix (Fin n) (Fin n) ℂ), U ∈ Matrix.unitaryGroup (Fin n) ℂ → (Uᴴ * Y * U).BlockTriangular id → (Uᴴ * NormedSpace.exp Y * U).BlockTriangular id := by
  first | exact @GlobalTheory.CompanionTheory.Unitary.ExpUpper.blockTriangular_conj_exp | exact GlobalTheory.CompanionTheory.Unitary.ExpUpper.blockTriangular_conj_exp | (intros; apply GlobalTheory.CompanionTheory.Unitary.ExpUpper.blockTriangular_conj_exp <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FiniteOfCompact
section
noncomputable section

open MeasureTheory PositivityTheory.Rg.BcB.E1
open scoped ENNReal Pointwise

namespace GlobalTheory.CompanionTheory.KernelBasic

theorem finite_of_compact (X : Ctx) {φ : X.G → ℂ} (hφ : HasCompactSupport φ) {U V : Set X.G}
    (hU : IsCompact U) (hV : IsCompact V) :
    {γ : X.Γ | ∃ x ∈ U, ∃ y ∈ V, φ (x⁻¹ * (γ : X.G) * y) ≠ 0}.Finite := by
  have hS : IsCompact (U * tsupport φ * V⁻¹) := (hU.mul hφ.isCompact).mul hV.inv
  refine (X.proper _ hS).subset ?_
  rintro γ ⟨x, hx, y, hy, h⟩
  refine Set.mem_setOf_eq ▸ ?_
  have e : (γ : X.G) = x * (x⁻¹ * (γ : X.G) * y) * y⁻¹ := by group
  rw [e]
  exact Set.mul_mem_mul (Set.mul_mem_mul hx (subset_tsupport _ (Function.mem_support.2 h)))
    (Set.inv_mem_inv.2 hy)

theorem support_finite (X : Ctx) {φ : X.G → ℂ} (hφ : HasCompactSupport φ) (x y : X.G) :
    (Function.support fun γ : X.Γ => φ (x⁻¹ * (γ : X.G) * y)).Finite := by
  refine (finite_of_compact X hφ (isCompact_singleton (x := x))
    (isCompact_singleton (x := y))).subset ?_
  intro γ h
  exact ⟨x, rfl, y, rfl, h⟩

theorem continuous_ker (X : Ctx) {φ : X.G → ℂ} (hφ : Tst φ) :
    Continuous (Function.uncurry (ker X.Γ φ)) := by
  have e : Function.uncurry (ker X.Γ φ) =
      fun p : X.G × X.G => ∑ᶠ γ : X.Γ, φ (p.1⁻¹ * (γ : X.G) * p.2) := by
    funext p
    rfl
  rw [e]
  refine continuous_finsum (fun γ => ?_) ?_
  · exact hφ.1.comp ((continuous_fst.inv.mul continuous_const).mul continuous_snd)
  · rintro ⟨x, y⟩
    obtain ⟨U, hU, hUx⟩ := exists_compact_mem_nhds x
    obtain ⟨V, hV, hVy⟩ := exists_compact_mem_nhds y
    refine ⟨U ×ˢ V, prod_mem_nhds hUx hVy, ?_⟩
    refine (finite_of_compact X hφ.2 hU hV).subset ?_
    rintro γ ⟨⟨a, b⟩, hs, hab⟩
    exact ⟨a, hab.1, b, hab.2, hs⟩

theorem ker_mul_left (X : Ctx) (φ : X.G → ℂ) {γ : X.G} (hγ : γ ∈ X.Γ) (x y : X.G) :
    ker X.Γ φ (γ * x) y = ker X.Γ φ x y := by
  unfold ker
  rw [← finsum_comp_equiv (Equiv.mulLeft (⟨γ, hγ⟩ : X.Γ))]
  refine finsum_congr fun δ => ?_
  congr 1
  simp only [Equiv.coe_mulLeft, Subgroup.coe_mul]
  group

theorem ker_mul_right (X : Ctx) (φ : X.G → ℂ) {γ : X.G} (hγ : γ ∈ X.Γ) (x y : X.G) :
    ker X.Γ φ x (γ * y) = ker X.Γ φ x y := by
  unfold ker
  rw [← finsum_comp_equiv (Equiv.mulRight (⟨γ, hγ⟩ : X.Γ)⁻¹)]
  refine finsum_congr fun δ => ?_
  congr 1
  simp only [Equiv.coe_mulRight, Subgroup.coe_mul, Subgroup.coe_inv]
  group

theorem tst_adj (X : Ctx) {φ : X.G → ℂ} (hφ : Tst φ) : Tst (adj φ) := by
  refine ⟨Complex.continuous_conj.comp (hφ.1.comp continuous_inv), ?_⟩
  have h : HasCompactSupport (φ ∘ (Homeomorph.inv X.G)) :=
    hφ.2.comp_homeomorph (Homeomorph.inv X.G)
  exact h.comp_left (g := starRingEnd ℂ) (map_zero _)

theorem ker_adj (X : Ctx) {φ : X.G → ℂ} (hφ : HasCompactSupport φ) (x y : X.G) :
    ker X.Γ (adj φ) x y = starRingEnd ℂ (ker X.Γ φ y x) := by
  unfold ker
  rw [map_finsum _ (support_finite X hφ y x), ← finsum_comp_equiv (Equiv.inv X.Γ)]
  refine finsum_congr fun δ => ?_
  simp only [adj, Equiv.inv_apply, Subgroup.coe_inv]
  congr 2
  group

theorem enorm_ker_le (X : Ctx) {φ : X.G → ℂ} (hφ : HasCompactSupport φ) (x y : X.G) :
    ‖ker X.Γ φ x y‖ₑ ≤ ∑' γ : X.Γ, ‖φ (x⁻¹ * (γ : X.G) * y)‖ₑ := by
  unfold ker
  rw [finsum_eq_sum _ (support_finite X hφ x y)]
  exact (enorm_sum_le _ _).trans (ENNReal.sum_le_tsum _)

theorem kerBasic : KerBasic := by
  intro X φ hφ
  exact ⟨support_finite X hφ.2, continuous_ker X hφ,
    fun γ hγ x y => ⟨ker_mul_left X φ hγ x y, ker_mul_right X φ hγ x y⟩,
    tst_adj X hφ, ker_adj X hφ.2, enorm_ker_le X hφ.2⟩

end GlobalTheory.CompanionTheory.KernelBasic

end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FlatQuotientOfUniversallyInjectiveStatement
section
open TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.flat_quotient_of_universally_injective : ∀ (R A B : Type) [CommRing R] [AddCommGroup A] [Module R A] [AddCommGroup B] [Module R B] [Module.Flat R B] (f : A →ₗ[R] B), (∀ (M : Type) [AddCommGroup M] [Module R M], Function.Injective (f.lTensor M)) → Module.Flat R (B ⧸ LinearMap.range f) := by
  first | exact @GlobalTheory.CompanionTheory.FlatCoker.flat_quotient_range_of_lTensor_injective | exact GlobalTheory.CompanionTheory.FlatCoker.flat_quotient_range_of_lTensor_injective | (intros; apply GlobalTheory.CompanionTheory.FlatCoker.flat_quotient_range_of_lTensor_injective <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FourierOneParameterIntegralStatement
section
open MeasureTheory

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.fourier_one_parameter_integral : ∀ (A : Type) [AddCommGroup A] [TopologicalSpace A] [IsTopologicalAddGroup A] [MeasurableSpace A] [BorelSpace A] (lam : Measure A) [lam.IsAddHaarMeasure] [SFinite lam] (c : ℝ →+ A), Continuous c → ∀ (F G : A → ℂ), Continuous F → Continuous G → Integrable F lam → Integrable G lam → ∀ (χ : AddChar A ℂ), Continuous χ → (∀ x, ‖χ x‖ = 1) → ∀ (f : ℝ), (∀ s : ℝ, χ (c s) = Complex.exp (-(2 * Real.pi * Complex.I * ((s * f : ℝ) : ℂ)))) → (∀ (b : A) (s : ℝ), HasDerivAt (fun t : ℝ => F (b + c t)) (2 * Real.pi * Complex.I * G (b + c s)) s) → ∫ b, G b * χ b ∂lam = (f : ℂ) * ∫ b, F b * χ b ∂lam := by
  first | exact @GlobalTheory.CompanionTheory.OneParamFourier.integral_mul_char_eq_of_hasDerivAt | exact GlobalTheory.CompanionTheory.OneParamFourier.integral_mul_char_eq_of_hasDerivAt | (intros; apply GlobalTheory.CompanionTheory.OneParamFourier.integral_mul_char_eq_of_hasDerivAt <;> assumption)
end

