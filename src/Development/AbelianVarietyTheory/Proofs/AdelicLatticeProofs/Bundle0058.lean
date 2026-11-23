module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.AdelicHermitianForms.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.Bundle0028
public import Formalism.LocalToGlobal.IndefiniteReal.Bundle0016
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0008
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0005
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.IsTopologicalRingAE

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.IntegralFiniteAdeleCompactClosedMultiples
section
open Matrix GlobalTheory.ClassFin
open scoped Kronecker ComplexOrder TensorProduct
open NumberField IsDedekindDomain

namespace GlobalTheory.IntegralFinAdele

variable (F : Type) [Field F] [NumberField F]

theorem t2Space_finiteAdeleRing' : T2Space (FiniteAdeleRing (𝓞 F) F) :=
  inferInstanceAs (T2Space (RestrictedProduct (fun v : HeightOneSpectrum (𝓞 F) => v.adicCompletion F)
    (fun v => (v.adicCompletionIntegers F : Set (v.adicCompletion F))) Filter.cofinite))

theorem natCast_apply (M : ℕ) (v : HeightOneSpectrum (𝓞 F)) :
    (M : FiniteAdeleRing (𝓞 F) F) v = ((algebraMap (𝓞 F) F (M : 𝓞 F) : F) : v.adicCompletion F) := by
  rw [← map_natCast (algebraMap F (FiniteAdeleRing (𝓞 F) F)), FiniteAdeleRing.algebraMap_apply,
    map_natCast (algebraMap (𝓞 F) F)]

theorem mul_apply' (a b : FiniteAdeleRing (𝓞 F) F) (v : HeightOneSpectrum (𝓞 F)) :
    (a * b) v = a v * b v := rfl

theorem pow_apply' (a : FiniteAdeleRing (𝓞 F) F) (n : ℕ) (v : HeightOneSpectrum (𝓞 F)) :
    (a ^ n) v = a v ^ n := by
  induction n with
  | zero => rw [pow_zero, pow_zero]; rfl
  | succ n ih => rw [pow_succ, pow_succ, mul_apply', ih]

theorem eq_zero_of_forall_mul (a : FiniteAdeleRing (𝓞 F) F)
    (h : ∀ M : ℕ, 0 < M → ∃ c : FiniteAdeleRing (𝓞 F) F,
      (∀ v, c v ∈ HeightOneSpectrum.adicCompletionIntegers F v) ∧
        a = (M : FiniteAdeleRing (𝓞 F) F) * c) : a = 0 := by
  refine FiniteAdeleRing.ext F fun v => ?_
  change a v = 0
  by_contra h0
  set N := Ideal.absNorm v.asIdeal with hN
  have hNpos : 0 < N := Nat.pos_of_ne_zero (by
    rw [hN, Ne, Ideal.absNorm_eq_zero_iff]; exact v.ne_bot)
  have hlt : Valued.v ((N : FiniteAdeleRing (𝓞 F) F) v) < 1 := by
    rw [natCast_apply, HeightOneSpectrum.valuedAdicCompletion_eq_valuation',
      HeightOneSpectrum.valuation_lt_one_iff_mem]
    exact Ideal.absNorm_mem _
  have hv0 : Valued.v (a v) ≠ 0 := by simpa using h0
  obtain ⟨n, hn⟩ := exists_pow_lt₀ hlt (Units.mk0 _ hv0)
  obtain ⟨c, hc, hac⟩ := h (N ^ n) (pow_pos hNpos n)
  have hc' : Valued.v (c v) ≤ 1 := (HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).1 (hc v)
  have : Valued.v (a v) ≤ Valued.v ((N : FiniteAdeleRing (𝓞 F) F) v) ^ n := by
    conv_lhs => rw [hac]
    rw [mul_apply', Nat.cast_pow, pow_apply', map_mul, map_pow]
    exact mul_le_of_le_one_right' hc'
  exact absurd hn (not_lt.2 this)

theorem exists_nat_mul_integral (a : FiniteAdeleRing (𝓞 F) F) :
    ∃ M : ℕ, 0 < M ∧ ∀ v, ((M : FiniteAdeleRing (𝓞 F) F) * a) v ∈
      HeightOneSpectrum.adicCompletionIntegers F v := by
  obtain ⟨x, b, hb, hab⟩ := GlobalTheory.AdLat.exists_eq_algebraMap_add_nsmul F 1 one_pos a
  haveI : Algebra.IsAlgebraic ℤ F :=
    (IsFractionRing.comap_isAlgebraic_iff (A := ℤ) (K := ℚ) (C := F)).2 inferInstance
  obtain ⟨m, y, hm, hmx⟩ := IsAlgebraic.exists_nsmul_eq (𝓞 F)
    (Algebra.IsAlgebraic.isAlgebraic (R := ℤ) x)
  refine ⟨m, Nat.pos_of_ne_zero hm, fun v => ?_⟩
  have h : (m : FiniteAdeleRing (𝓞 F) F) * a =
      algebraMap F (FiniteAdeleRing (𝓞 F) F) (algebraMap (𝓞 F) F y) +
        (m : FiniteAdeleRing (𝓞 F) F) * b := by
    rw [hab, ← hmx, one_smul, map_nsmul, nsmul_eq_mul, mul_add]
  rw [h]
  refine add_mem (HeightOneSpectrum.coe_mem_adicCompletionIntegers v y) (mul_mem ?_ (hb v))
  exact natCast_apply F m v ▸ HeightOneSpectrum.coe_mem_adicCompletionIntegers v (m : 𝓞 F)

theorem integral_finiteAdele_properties : ∀ (F : Type) [Field F] [NumberField F], IsCompact {a : FiniteAdeleRing (𝓞 F) F | (∀ v, (a : FiniteAdeleRing (𝓞 F) F) v ∈ HeightOneSpectrum.adicCompletionIntegers F v)} ∧ (∀ M : ℕ, 0 < M → IsClosed {a : FiniteAdeleRing (𝓞 F) F | ∃ c : FiniteAdeleRing (𝓞 F) F, (∀ v, (c : FiniteAdeleRing (𝓞 F) F) v ∈ HeightOneSpectrum.adicCompletionIntegers F v) ∧ a = (M : FiniteAdeleRing (𝓞 F) F) * c}) ∧ (∀ a : FiniteAdeleRing (𝓞 F) F, (∀ M : ℕ, 0 < M → ∃ c : FiniteAdeleRing (𝓞 F) F, (∀ v, (c : FiniteAdeleRing (𝓞 F) F) v ∈ HeightOneSpectrum.adicCompletionIntegers F v) ∧ a = (M : FiniteAdeleRing (𝓞 F) F) * c) → a = 0) ∧ (∀ x : F, (∀ v, (algebraMap F (FiniteAdeleRing (𝓞 F) F) x : FiniteAdeleRing (𝓞 F) F) v ∈ HeightOneSpectrum.adicCompletionIntegers F v) → ∃ y : 𝓞 F, x = y) ∧ (∀ a : FiniteAdeleRing (𝓞 F) F, ∃ M : ℕ, 0 < M ∧ (∀ v, (((M : FiniteAdeleRing (𝓞 F) F) * a) : FiniteAdeleRing (𝓞 F) F) v ∈ HeightOneSpectrum.adicCompletionIntegers F v)) ∧ IsReduced (FiniteAdeleRing (𝓞 F) F) := by
  intro F _ _
  refine ⟨GlobalTheory.AdeleCocompact.isCompact_integral F, fun M _ => ?_, eq_zero_of_forall_mul F,
    fun x hx => ?_, exists_nat_mul_integral F, ⟨fun a ⟨n, hn⟩ => ?_⟩⟩
  · haveI := t2Space_finiteAdeleRing' F
    have h := ((GlobalTheory.AdeleCocompact.isCompact_integral F).image
      (continuous_const_mul (M : FiniteAdeleRing (𝓞 F) F))).isClosed
    convert h using 1
    ext a
    simp only [Set.mem_image, Set.mem_setOf_eq, eq_comm]
  · obtain ⟨y, hy⟩ := HeightOneSpectrum.mem_integers_of_valuation_le_one F x fun v => by
      have := (HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).1 (hx v)
      rwa [FiniteAdeleRing.algebraMap_apply,
        HeightOneSpectrum.valuedAdicCompletion_eq_valuation'] at this
    exact ⟨y, hy.symm⟩
  · refine FiniteAdeleRing.ext F fun v => ?_
    have : a v ^ n = 0 := by rw [← pow_apply', hn]; rfl
    exact eq_zero_of_pow_eq_zero this

end GlobalTheory.IntegralFinAdele
end

-- bundled from Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.MemRangeOfOneTmulMem
section
namespace GlobalTheory.AdIdem

open NumberField IsDedekindDomain GlobalTheory.AdLat
open scoped TensorProduct nonZeroDivisors

section

variable (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem exists_nat_mul_integral (y : E) :
    ∃ d : ℕ, 0 < d ∧ (d : E) * y ∈ Set.range (algebraMap (𝓞 E) E) := by
  have hy : IsAlgebraic ℤ y :=
    (IsFractionRing.isAlgebraic_iff ℤ ℚ E).2 (Algebra.IsAlgebraic.isAlgebraic y)
  obtain ⟨m, hm, h⟩ := hy.exists_integral_multiple
  refine ⟨(m * m).toNat, ?_, ?_⟩
  · have := mul_self_pos.2 hm
    omega
  · have h2 : (((m * m).toNat : ℕ) : E) = (m : E) * m := by
      rw [← Int.cast_natCast, Int.toNat_of_nonneg (mul_self_nonneg m), Int.cast_mul]
    have h3 : IsIntegral ℤ ((m : E) * (m • y)) :=
      IsIntegral.mul (by simpa using isIntegral_algebraMap (R := ℤ) (A := E) (x := m)) h
    refine ⟨⟨_, h3⟩, ?_⟩
    rw [h2, mul_assoc, ← zsmul_eq_mul y m]
    rfl

omit [NumberField E] in
theorem mul_mem_hat {x y : RA F E} (hx : x ∈ hat1 F (Set.range (algebraMap (𝓞 E) E)))
    (hy : y ∈ hat1 F (Set.range (algebraMap (𝓞 E) E))) :
    x * y ∈ hat1 F (Set.range (algebraMap (𝓞 E) E)) := by
  refine mul_mem_adelicCompletionOfElementSet_of_mul_mem F ?_ hx hy
  rintro _ ⟨a, rfl⟩ _ ⟨b, rfl⟩
  exact ⟨a * b, map_mul _ _ _⟩

theorem exists_eq_one_tmul_add (z : RA F E) :
    ∃ (x : E), ∃ h ∈ hat1 F (Set.range (algebraMap (𝓞 E) E)),
      z = (1 : FiniteAdeleRing (𝓞 F) F) ⊗ₜ[F] x + h := by
  induction z using TensorProduct.induction_on with
  | zero => exact ⟨0, 0, zero_mem _, by simp⟩
  | tmul a y =>
    obtain ⟨d, hd, hy⟩ := exists_nat_mul_integral E y
    obtain ⟨x, b, hb, rfl⟩ := exists_eq_algebraMap_add_nsmul F d hd a
    refine ⟨x • y, b ⊗ₜ[F] ((d : E) * y), tmul_mem_adelicCompletion_of_integral F hb hy, ?_⟩
    rw [TensorProduct.add_tmul, Algebra.algebraMap_eq_smul_one, TensorProduct.smul_tmul,
      ← nsmul_eq_mul, ← Nat.cast_smul_eq_nsmul F, ← Nat.cast_smul_eq_nsmul F,
      TensorProduct.smul_tmul]
  | add u v hu hv =>
    obtain ⟨x, h, hh, rfl⟩ := hu
    obtain ⟨x', h', hh', rfl⟩ := hv
    refine ⟨x + x', h + h', add_mem hh hh', ?_⟩
    rw [TensorProduct.tmul_add]
    abel

theorem mem_range_of_one_tmul_mem {x : E}
    (hx : (1 : FiniteAdeleRing (𝓞 F) F) ⊗ₜ[F] x ∈ hat1 F (Set.range (algebraMap (𝓞 E) E))) :
    x ∈ Set.range (algebraMap (𝓞 E) E) := by
  have h : ((1 : FractionalIdeal (𝓞 E)⁰ E) : Set E) = Set.range (algebraMap (𝓞 E) E) := by
    ext y
    exact FractionalIdeal.mem_one_iff _
  rw [← h] at hx ⊢
  exact (one_tmul_mem_adelicCompletion_fractionalIdeal_iff F 1 x).1 hx

theorem mem_hat_of_idempotent (z : RA F E) (hz : z * z = z) :
    z ∈ hat1 F (Set.range (algebraMap (𝓞 E) E)) := by
  obtain ⟨x, h, hh, hx⟩ := exists_eq_one_tmul_add F E z
  obtain ⟨N, hN, hNx⟩ := exists_nat_mul_integral E x
  have h1 : (1 : RA F E) ∈ hat1 F (Set.range (algebraMap (𝓞 E) E)) :=
    one_tmul_mem_adelicCompletionOfElementSet F ⟨1, map_one _⟩
  have hc : ∀ y : E, (1 : FiniteAdeleRing (𝓞 F) F) ⊗ₜ[F] ((N : E) * y) =
      N • ((1 : FiniteAdeleRing (𝓞 F) F) ⊗ₜ[F] y : RA F E) := by
    intro y
    rw [← nsmul_eq_mul, ← Nat.cast_smul_eq_nsmul F, TensorProduct.tmul_smul,
      Nat.cast_smul_eq_nsmul]
  have hNz : N • z ∈ hat1 F (Set.range (algebraMap (𝓞 E) E)) := by
    rw [hx, nsmul_add, ← hc]
    exact add_mem (one_tmul_mem_adelicCompletionOfElementSet F hNx) (nsmul_mem hh N)
  have hpow : ∀ n : ℕ, ∃ a ∈ hat1 F (Set.range (algebraMap (𝓞 E) E)),
      ∃ b ∈ hat1 F (Set.range (algebraMap (𝓞 E) E)), (z - h) ^ n = a + z * b := by
    intro n
    induction n with
    | zero => exact ⟨1, h1, 0, zero_mem _, by simp⟩
    | succ n ih =>
      obtain ⟨a, ha, b, hb, e⟩ := ih
      refine ⟨-(a * h), neg_mem (mul_mem_hat F E ha hh), a + b - b * h,
        sub_mem (add_mem ha hb) (mul_mem_hat F E hb hh), ?_⟩
      rw [pow_succ, e]
      linear_combination b * hz
  have hzh : z - h = (1 : FiniteAdeleRing (𝓞 F) F) ⊗ₜ[F] x := by rw [hx]; abel
  have hint : ∀ n : ℕ, (N : E) * x ^ n ∈ Set.range (algebraMap (𝓞 E) E) := by
    intro n
    apply mem_range_of_one_tmul_mem F E
    obtain ⟨a, ha, b, hb, e⟩ := hpow n
    rw [hzh, Algebra.TensorProduct.tmul_pow, one_pow] at e
    rw [hc, e, nsmul_add, ← smul_mul_assoc]
    exact add_mem (nsmul_mem ha N) (mul_mem_hat F E hNz hb)
  have hai : IsAlmostIntegral (𝓞 E) x := by
    refine ⟨(N : 𝓞 E), mem_nonZeroDivisors_of_ne_zero (Nat.cast_ne_zero.2 hN.ne'), fun n => ?_⟩
    rw [Algebra.smul_def, map_natCast]
    exact hint n
  obtain ⟨r, hr⟩ := IsIntegrallyClosed.isIntegral_iff.1 hai.isIntegral
  rw [hx]
  exact add_mem (one_tmul_mem_adelicCompletionOfElementSet F ⟨r, hr⟩) hh

end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem idempotent_mem_intAE : ∀ (D : D7) (z : Af D.host.F ⊗[D.host.F] D.host.E), z * z = z → z ∈ intAE D := by
  intro D z hz
  have h : intAE D = GlobalTheory.AdLat.hat1 D.host.F (Set.range (algebraMap (𝓞 D.host.E) D.host.E)) := by
    unfold intAE GlobalTheory.AdLat.hat1
    congr 1
    ext z
    constructor
    · rintro ⟨a, ha, x, rfl⟩
      exact ⟨a, ha, _, ⟨x, rfl⟩, rfl⟩
    · rintro ⟨a, ha, _, ⟨x, rfl⟩, rfl⟩
      exact ⟨a, ha, x, rfl⟩
  rw [h]
  exact mem_hat_of_idempotent D.host.F D.host.E z hz

end

end GlobalTheory.AdIdem
end

-- bundled from Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.SmulMemLatO
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.LatticeStable

noncomputable def liftFin (D : D7) : Af D.host.F ⊗[D.host.F] D.host.E →ₗ[D.host.F] AE D :=
  LinearMap.rTensor D.host.E
    (show Af D.host.F →ₗ[D.host.F] AF D.host.F from LinearMap.inr D.host.F (Ainf D.host.F) (Af D.host.F))

theorem liftFin_tmul (D : D7) (α : Af D.host.F) (m : D.host.E) :
    liftFin D (α ⊗ₜ[D.host.F] m) = pairA D.host.F 0 α ⊗ₜ[D.host.F] m := rfl

theorem mul_pair_tmul (D : D7) (w : AE D) (α : Af D.host.F) (m : D.host.E) :
    w * (pairA D.host.F 0 α ⊗ₜ[D.host.F] m) = liftFin D (finPart D w * (α ⊗ₜ[D.host.F] m)) := by
  induction w using TensorProduct.induction_on with
  | zero => rw [zero_mul, RingHom.map_zero, zero_mul, LinearMap.map_zero]
  | tmul x e =>
    change _ = liftFin D ((sndA D.host.F x ⊗ₜ[D.host.F] e) * _)
    rw [Algebra.TensorProduct.tmul_mul_tmul, Algebra.TensorProduct.tmul_mul_tmul, liftFin_tmul]
    congr 1
    exact Prod.ext (mul_zero _) rfl
  | add x y hx hy => rw [add_mul, hx, hy, RingHom.map_add (f := _), add_mul, LinearMap.map_add (f := _)]

noncomputable def liftMul (D : D7) (c : Af D.host.F ⊗[D.host.F] D.host.E) : Af D.host.F ⊗[D.host.F] D.host.E →+ AE D :=
  (liftFin D).toAddMonoidHom.comp (AddMonoidHom.mulRight c)

theorem smul_mem_latO (D : D7) (S T : HSp D) (LS : Set (Fin S.rank → D.host.E)) (LT : Set (Fin T.rank → D.host.E))
    (P : HeightOneSpectrum (𝓞 D.host.F) → Prop) (w : AE D) (hw : finPart D w ∈ intAE D) :
    ∀ u ∈ latO S T LS LT P, w • u ∈ latO S T LS LT P := by
  let Ψ : WO S T →+ WO S T := AddMonoidHom.mk' (fun u => w • u)
    fun x y => Matrix.ext fun i j => mul_add w (x i j) (y i j)
  have main : latO S T LS LT P ≤ (latO S T LS LT P).comap Ψ := by
    refine (AddSubgroup.closure_le _).2 ?_
    rintro _ ⟨α, hα, hP, a, ha, s, hs, t, ht, rfl⟩
    let Φ : Af D.host.F ⊗[D.host.F] D.host.E →+ WO S T := AddMonoidHom.mk'
      (fun y => Matrix.of fun i j => liftMul D
        (α ⊗ₜ[D.host.F] (a * t i * ∑ k, star (s k) * HSpace.gram S k j)) y)
      fun y y' => Matrix.ext fun i j => (liftMul D _).map_add y y'
    have hle : intAE D ≤ (latO S T LS LT P).comap Φ := by
      refine (AddSubgroup.closure_le _).2 ?_
      rintro _ ⟨β, hβ, o, rfl⟩
      refine AddSubgroup.subset_closure ⟨β * α, fun v => ?_, fun v hv => ?_, o • a,
        Submodule.smul_mem (D.host.AA : Submodule (𝓞 D.host.E) D.host.E) o ha, s, hs, t, ht, ?_⟩
      · rw [map_mul]; exact mul_mem (hβ v) (hα v)
      · rw [map_mul, hP v hv, mul_zero]
      · ext i j
        change liftFin D ((β ⊗ₜ[D.host.F] (o : D.host.E)) * (α ⊗ₜ[D.host.F] _)) = _ ⊗ₜ[D.host.F] _
        rw [Algebra.TensorProduct.tmul_mul_tmul, liftFin_tmul, Algebra.smul_def,
          show algebraMap _ _ o = (o : D.host.E) from rfl]
        congr 1
        ring
    have e : Ψ (Matrix.of fun i j => pairA D.host.F 0 α ⊗ₜ[D.host.F]
        (a * t i * ∑ k, star (s k) * HSpace.gram S k j) : WO S T) = Φ (finPart D w) :=
      Matrix.ext fun i j => mul_pair_tmul D w α _
    rw [SetLike.mem_coe, AddSubgroup.mem_comap, e]
    exact hle hw
  exact fun u hu => main hu

end GlobalTheory.LatticeStable
end

-- bundled from Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.StarTraceHerm
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open scoped TensorProduct ContDiff ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.CartanTrace

theorem star_trace_herm {m n : ℕ} {A : Matrix (Fin n) (Fin n) ℂ} {B : Matrix (Fin m) (Fin m) ℂ}
    (hA : Aᴴ = A) (hB : Bᴴ = B) (x y : Matrix (Fin m) (Fin n) ℂ) :
    star (A * yᴴ * B * x).trace = (A * xᴴ * B * y).trace := by
  rw [← Matrix.trace_conjTranspose]
  simp only [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, hA, hB]
  rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, Matrix.trace_mul_comm]
  simp only [Matrix.mul_assoc]

open scoped MatrixOrder in
theorem trace_pos {m n : ℕ} {A : Matrix (Fin n) (Fin n) ℂ} {B : Matrix (Fin m) (Fin m) ℂ}
    (hA : A.PosDef) (hB : B.PosDef) (x : Matrix (Fin m) (Fin n) ℂ) (hx : x ≠ 0) :
    0 < (A * xᴴ * B * x).trace := by
  obtain ⟨C, hC, rfl⟩ := CStarAlgebra.isStrictlyPositive_iff_eq_star_mul_self.mp
    hA.isStrictlyPositive
  obtain ⟨D, hD, rfl⟩ := CStarAlgebra.isStrictlyPositive_iff_eq_star_mul_self.mp
    hB.isStrictlyPositive
  have e : (star C * C * xᴴ * (star D * D) * x).trace = ((D * x * Cᴴ)ᴴ * (D * x * Cᴴ)).trace := by
    simp only [Matrix.star_eq_conjTranspose, Matrix.conjTranspose_mul,
      Matrix.conjTranspose_conjTranspose, Matrix.mul_assoc]
    rw [Matrix.trace_mul_comm]
    simp only [Matrix.mul_assoc]
  rw [e]
  refine lt_of_le_of_ne (Matrix.posSemidef_conjTranspose_mul_self _).trace_nonneg ?_
  intro h
  have h0 := Matrix.trace_conjTranspose_mul_self_eq_zero_iff.1 h.symm
  apply hx
  have hC' : IsUnit Cᴴ := hC.star
  have hD' := (Matrix.isUnit_iff_isUnit_det _).1 hD
  have hC'' := (Matrix.isUnit_iff_isUnit_det _).1 hC'
  have : x = D⁻¹ * (D * x * Cᴴ) * Cᴴ⁻¹ := by
    rw [Matrix.mul_assoc D, Matrix.nonsing_inv_mul_cancel_left _ _ hD',
      Matrix.mul_nonsing_inv_cancel_right _ _ hC'']
  rw [this, h0]; simp

variable {k : ℕ} {G s : Matrix (Fin k) (Fin k) ℂ}

theorem adj_mul (h : IsCartanInv G s) : sᴴ * G = G * s := by
  have := congrArg (· * s) h.2.1
  simpa only [Matrix.mul_assoc, h.1, Matrix.mul_one] using this

theorem adj_sq (h : IsCartanInv G s) : sᴴ * sᴴ = 1 := by
  rw [← Matrix.conjTranspose_mul, h.1, Matrix.conjTranspose_one]

theorem herm (h : IsCartanInv G s) : Gᴴ = G := by
  have h1 : sᴴ * Gᴴ = sᴴ * G := by
    rw [← Matrix.conjTranspose_mul, adj_mul h]; exact h.2.2.isHermitian
  have := congrArg (sᴴ * ·) h1
  simpa only [← Matrix.mul_assoc, adj_sq h, Matrix.one_mul] using this

theorem inv_mul_adj (h : IsCartanInv G s) : G⁻¹ * sᴴ = (G * s)⁻¹ := by
  rw [← adj_mul h, Matrix.mul_inv_rev, Matrix.inv_eq_left_inv (adj_sq h)]

theorem form_cplxO {m n : ℕ} {GS sS : Matrix (Fin n) (Fin n) ℂ} {GT sT : Matrix (Fin m) (Fin m) ℂ}
    {ξ : ℂ} (hξ : ξ.re = 0) (hS : IsCartanInv GS sS) (hT : IsCartanInv GT sT)
    (x y : Matrix (Fin m) (Fin n) ℂ) :
    (ξ * (GS⁻¹ * (cplxO sS sT y)ᴴ * GT * x).trace).re =
      ξ.im * ((GS * sS)⁻¹ * yᴴ * (GT * sT) * x).trace.re := by
  have e : GS⁻¹ * (cplxO sS sT y)ᴴ * GT * x =
      (-Complex.I) • ((GS * sS)⁻¹ * yᴴ * (GT * sT) * x) := by
    rw [← inv_mul_adj hS, ← adj_mul hT]
    simp only [cplxO, Matrix.conjTranspose_smul, Matrix.conjTranspose_mul, Matrix.mul_smul,
      Matrix.smul_mul, Matrix.mul_assoc, Complex.star_def, Complex.conj_I]
  rw [e, Matrix.trace_smul]
  simp [hξ]

theorem cplxO_pos : ∀ (m n : ℕ) (GS sS : Matrix (Fin n) (Fin n) ℂ) (GT sT : Matrix (Fin m) (Fin m) ℂ) (ξ : ℂ), ξ.re = 0 → 0 < ξ.im → IsCartanInv GS sS → IsCartanInv GT sT → (∀ x : Matrix (Fin m) (Fin n) ℂ, (ξ * (GS⁻¹ * xᴴ * GT * x).trace).re = 0) ∧ (∀ x : Matrix (Fin m) (Fin n) ℂ, cplxO sS sT (cplxO sS sT x) = -x) ∧ (∀ x y : Matrix (Fin m) (Fin n) ℂ, (ξ * (GS⁻¹ * (cplxO sS sT y)ᴴ * GT * x).trace).re = (ξ * (GS⁻¹ * (cplxO sS sT x)ᴴ * GT * y).trace).re) ∧ ∀ x : Matrix (Fin m) (Fin n) ℂ, x ≠ 0 → 0 < (ξ * (GS⁻¹ * (cplxO sS sT x)ᴴ * GT * x).trace).re := by
  intro m n GS sS GT sT ξ h0 h1 hS hT
  refine ⟨fun x => ?_, fun x => ?_, fun x y => ?_, fun x hx => ?_⟩
  · have hi : GS⁻¹ᴴ = GS⁻¹ := by rw [Matrix.conjTranspose_nonsing_inv, herm hS]
    have := congrArg Complex.im (star_trace_herm hi (herm hT) x x)
    have h2 : (GS⁻¹ * xᴴ * GT * x).trace.im = 0 := by
      rw [Complex.star_def, Complex.conj_im] at this; linarith
    simp [h0, h2]
  · simp only [cplxO, Matrix.mul_smul, Matrix.smul_mul, smul_smul, Complex.I_mul_I]
    rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, hT.1, Matrix.one_mul, Matrix.mul_assoc, hS.1]
    simp
  · rw [form_cplxO h0 hS hT, form_cplxO h0 hS hT,
      ← star_trace_herm hS.2.2.inv.isHermitian hT.2.2.isHermitian x y]
    simp
  · rw [form_cplxO h0 hS hT]
    exact mul_pos h1 (Complex.pos_iff.1 (trace_pos hS.2.2.inv hT.2.2 x hx)).1

end GlobalTheory.CartanTrace
end

-- bundled from Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ThetaAtEqSumHeisOfFourierSum
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory

theorem isSBHalf_halfInd {D : D7} {m n : ℕ} (e : AE D) (Λ : AddSubgroup (Mx D m n)) :
    IsSBHalf e Λ (halfInd e Λ) := by
  classical
  refine ⟨fun t ht => ?_, 1, one_pos, fun u hu hh t => ?_, fun t ht => ?_⟩
  · by_contra h
    exact ht (by simp [halfInd, h])
  · have : (t + 1 • u ∈ Λ ∧ IsHalf e (t + 1 • u)) ↔ (t ∈ Λ ∧ IsHalf e t) := by
      rw [one_smul, Λ.add_mem_cancel_right hu]
      refine and_congr_right fun _ => forall_congr' fun i => forall_congr' fun j => ?_
      rw [Matrix.add_apply, mul_add, hh i j, add_left_inj]
    simp only [halfInd, this]
  · by_contra h
    rw [one_smul] at h
    exact ht (by simp [halfInd, h])

end GlobalTheory
end

