module

public import Mathlib
public import GroundTheory.HeightsAndTheta.Heights.FiniteCovolume.CoreLatticeEqOfMemCoreStabilizer
public import GroundTheory.AutomorphicForms.DefiniteClassNumber.Finiteness
public import GroundTheory.HeightsAndTheta.Heights.FiniteCovolume.Statements

@[expose] public section

-- bundled from GroundTheory.HeightsAndTheta.Heights.FiniteCovolume.IsIntegralVecCoordsOfMemAdelicLatticeOne
section
set_option linter.unusedSectionVars false

noncomputable section

namespace GroundTheory.Heights₂.Heights.FiniteCovolume

open Module Matrix TensorProduct Topology NumberField IsDedekindDomain GroundTheory.Automorphic
  GroundTheory.Global

variable {K : Type*} [Field K] [NumberField K]
variable {E : Type*} [Field E] [NumberField E] [Algebra K E] [Algebra.IsQuadraticExtension K E]
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable {κ : Type*} [Fintype κ] [DecidableEq κ] (b : Basis κ K E)

section Pairing

variable (H : Matrix ι ι E)

def pairE (x y : ι → K ⊗[K] E) : E := Algebra.TensorProduct.lid K E (hermPair K H K x y)

variable {H}

theorem baseTrace_eq_trace_lid (z : K ⊗[K] E) :
    baseTrace K E K z = Algebra.trace K E (Algebra.TensorProduct.lid K E z) := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul r e =>
    rw [baseTrace_tmul, Algebra.TensorProduct.lid_tmul, LinearMap.map_smul, smul_eq_mul,
      Algebra.algebraMap_self, RingHom.id_apply, mul_comm]
  | add x y hx hy => rw [map_add (f := _), map_add (f := _), map_add (f := _), hx, hy]

theorem hermTrace_eq_trace_pairE (x y : ι → K ⊗[K] E) :
    hermTrace K H K x y = Algebra.trace K E (pairE H x y) :=
  baseTrace_eq_trace_lid _

theorem pairE_smul_right (β : E) (x y : ι → K ⊗[K] E) :
    pairE H x (((1 : K) ⊗ₜ[K] β) • y) = β * pairE H x y := by
  rw [pairE, hermPair_smul_right, map_mul, Algebra.TensorProduct.lid_tmul, one_smul]
  rfl

theorem pairE_smul_left (β : E) (x y : ι → K ⊗[K] E) :
    pairE H (((1 : K) ⊗ₜ[K] β) • x) y = conj K E β * pairE H x y := by
  rw [pairE, hermPair_smul_left, map_mul, conjBase_tmul, Algebra.TensorProduct.lid_tmul, one_smul]
  rfl

theorem smul_smul_comm_vec (z : K ⊗[K] E) (c : K) (y : ι → K ⊗[K] E) :
    z • (c • y) = c • (z • y) := by
  funext i
  simp only [Pi.smul_apply, smul_eq_mul, mul_smul_comm]

end Pairing

section Nondegenerate

variable {H : Matrix ι ι E}

theorem isUnit_det_traceGram_of_isUnit (hH : IsUnit H.det) : IsUnit (traceGram H b).det := by
  classical
  rw [isUnit_iff_ne_zero]
  intro h0
  obtain ⟨t, ht0, ht⟩ := Matrix.exists_vecMul_eq_zero_iff.2 h0
  set X : ι → K ⊗[K] E := vecOfCoords b K t with hXdef
  have hX : ∀ Y : ι → K ⊗[K] E, hermTrace K H K X Y = 0 := by
    intro Y
    rw [hermTrace_eq_sum_traceGram (H := H) (b := b) K, hXdef, vecCoords_vecOfCoords,
      Finset.sum_comm]
    refine Finset.sum_eq_zero fun c _ => ?_
    have hc := congrFun ht c
    simp only [vecMul, dotProduct, Pi.zero_apply] at hc
    simp only [Algebra.algebraMap_self, RingHom.id_apply]
    calc ∑ a, t a * vecCoords K b Y c * traceGram H b a c
        = vecCoords K b Y c * ∑ a, t a * traceGram H b a c := by
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl fun a _ => ?_
          ring
      _ = 0 := by rw [hc, mul_zero]
  have hX0 : X ≠ 0 := by
    intro h
    apply ht0
    rw [← vecCoords_vecOfCoords b K t, ← hXdef, h]
    funext a
    simp [vecCoords]
  obtain ⟨i, hi⟩ : ∃ i, X i ≠ 0 := by
    by_contra hc
    push_neg at hc
    exact hX0 (funext hc)
  have hci : conjBase K E K (X i) ≠ 0 := by
    intro h
    apply hi
    rw [← conjBase_conjBase (X i), h, map_zero]
  have hunit : IsUnit (conjBase K E K (X i)) := by
    have h1 : Algebra.TensorProduct.lid K E (conjBase K E K (X i)) ≠ 0 := by
      intro h
      exact hci ((Algebra.TensorProduct.lid K E).injective (by rw [h, map_zero]))
    have := (isUnit_iff_ne_zero.2 h1).map (Algebra.TensorProduct.lid K E).symm
    rwa [AlgEquiv.symm_apply_apply] at this
  obtain ⟨u, hu⟩ := hunit
  set Hb := baseMatrix K H K
  have hHb : IsUnit Hb.det := isUnit_det_baseMatrix H K hH
  set Y : ι → K ⊗[K] E := Hb⁻¹ *ᵥ Pi.single i (↑u⁻¹ : K ⊗[K] E)
  have hpair : hermPair K H K X Y = 1 := by
    unfold hermPair
    rw [show baseMatrix K H K = Hb from rfl, mulVec_mulVec, Matrix.mul_nonsing_inv _ hHb,
      one_mulVec, dotProduct_single, ← hu, Units.mul_inv]
  have h2 := hX Y
  rw [hermTrace, hpair, show (1 : K ⊗[K] E) = algebraMap K (K ⊗[K] E) 1 from (map_one _).symm,
    baseTrace_algebraMap, mul_one] at h2
  exact two_ne_zero h2

end Nondegenerate

section Integrality

variable (H : Matrix ι ι E)

theorem exists_int_isIntegral_pairE : ∃ d : ℤ, d ≠ 0 ∧
    ∀ (g : unitaryPoints K E H (FinAdele K)) (x y : ι → K ⊗[K] E), x ∈ coreLattice b H g →
      y ∈ coreLattice b H g → IsIntegral ℤ ((d : E) * pairE H x y) := by
  obtain ⟨d₁, hd₁0, hd₁⟩ := exists_int_isIntegral_hermTrace b H
  obtain ⟨D, hD0, hD⟩ := exists_int_isIntegral_of_trace (K := E)
  refine ⟨D * d₁, mul_ne_zero hD0 hd₁0, fun g x y hx hy => ?_⟩
  have key : ∀ s, ∃ n : ℤ, Algebra.trace ℚ E (((d₁ : E) * pairE H x y) * integralBasis E s) = n := by
    intro s
    have hy' := smul_mem_coreLattice b hy (RingOfIntegers.basis E s)
    have h1 := hd₁ g x _ (coreLattice_le_adelicLattice b g hx) (coreLattice_le_adelicLattice b g hy')
    rw [hermTrace_eq_trace_pairE, pairE_smul_right] at h1
    obtain ⟨n, hn⟩ := exists_int_trace_eq h1
    refine ⟨n, ?_⟩
    rw [← hn, ← Algebra.trace_trace (S := K), integralBasis_apply, ← RingOfIntegers.coe_eq_algebraMap]
    congr 1
    rw [show (d₁ : E) = algebraMap K E (d₁ : K) by rw [map_intCast], mul_assoc, ← Algebra.smul_def,
      LinearMap.map_smul, smul_eq_mul, mul_comm (pairE H x y)]
  have := hD _ key
  rw [show ((D * d₁ : ℤ) : E) * pairE H x y = (D : E) * ((d₁ : E) * pairE H x y) by push_cast; ring]
  exact this

theorem exists_int_smul_mem_coreLattice_of_dual {H : Matrix ι ι E} (hH : IsUnit H.det) :
    ∃ m : ℤ, m ≠ 0 ∧ ∀ (g : unitaryPoints K E H (FinAdele K)) (y : ι → K ⊗[K] E),
      (∀ x ∈ coreLattice b H g, IsIntegral ℤ (pairE H y x)) → (m : K) • y ∈ coreLattice b H g := by
  obtain ⟨N, hN0, hN⟩ := exists_int_smul_mem_coreLattice b H
  obtain ⟨m, hm0, hm⟩ := exists_int_smul_mem_of_forall_isIntegral b H
    (isUnit_det_traceGram_of_isUnit b hH) (N : K) (by exact_mod_cast hN0)
  refine ⟨m, hm0, fun g y hy => ?_⟩
  rw [mem_coreLattice_iff]
  intro β
  have hyβ : ∀ x ∈ adelicLattice b H g,
      IsIntegral ℤ ((N : K) * hermTrace K H K (((1 : K) ⊗ₜ[K] (β : E)) • y) x) := by
    intro x hx
    rw [← hermTrace_smul_right, hermTrace_eq_trace_pairE, pairE_smul_left]
    refine Algebra.isIntegral_trace ((map_isIntegral_int (conj K E) β.2).mul (hy _ (hN g x hx)))
  have h2 := hm g _ hyβ
  rwa [← smul_smul_comm_vec] at h2

end Integrality

section Bounds

variable {H : Matrix ι ι E}

theorem isIntegral_vecCoords_of_mem_adelicLattice_one {x : ι → K ⊗[K] E}
    (hx : x ∈ adelicLattice b H 1) (a : ι × κ) : IsIntegral ℤ (vecCoords K b x a) := by
  rw [mem_adelicLattice, inv_one, show unitaryMat (1 : unitaryPoints K E H (FinAdele K)) = 1 from rfl,
    one_mulVec, mem_stdLattice_iff] at hx
  have := hx a
  rw [vecCoords_toFinAdele] at this
  exact isIntegral_of_algebraMap_mem this

theorem exists_int_isIntegral_coords (hH : IsUnit H.det) (g : unitaryPoints K E H (FinAdele K)) :
    ∃ m : ℤ, m ≠ 0 ∧ ∀ y ∈ adelicLattice b H g, ∀ a, IsIntegral ℤ ((m : K) * vecCoords K b y a) := by
  classical
  obtain ⟨r, hr0, hr⟩ := exists_int_smul_mem_adelicLattice (b := b) g
  obtain ⟨d₁, hd₁0, hd₁⟩ := exists_int_isIntegral_hermTrace b H
  obtain ⟨m, hm0, hm⟩ := exists_int_smul_mem_of_forall_isIntegral b H
    (isUnit_det_traceGram_of_isUnit b hH) ((d₁ * r : ℤ) : K) (by exact_mod_cast mul_ne_zero hd₁0 hr0)
  refine ⟨m, hm0, fun y hy a => ?_⟩
  have h1 : ∀ x ∈ adelicLattice b H 1, IsIntegral ℤ (((d₁ * r : ℤ) : K) * hermTrace K H K y x) := by
    intro x hx
    have := hd₁ g y _ hy (hr x (isIntegral_vecCoords_of_mem_adelicLattice_one b hx))
    rw [hermTrace_smul_right] at this
    rw [show ((d₁ * r : ℤ) : K) * hermTrace K H K y x = (d₁ : K) * ((r : K) * hermTrace K H K y x) by
      push_cast; ring]
    exact this
  have := isIntegral_vecCoords_of_mem_adelicLattice_one b (hm 1 y h1) a
  rwa [vecCoords_smul] at this

theorem exists_int_smul_single_mem_coreLattice (g : unitaryPoints K E H (FinAdele K)) (i : ι) :
    ∃ n : ℤ, n ≠ 0 ∧ (n : K) • (Pi.single i (1 : K ⊗[K] E) : ι → K ⊗[K] E) ∈ coreLattice b H g := by
  classical
  obtain ⟨c, hc0, hc⟩ := exists_int_mul_isIntegral (Finset.univ.image fun k => b.repr 1 k)
  obtain ⟨r, hr0, hr⟩ := exists_int_smul_mem_adelicLattice (b := b) g
  obtain ⟨N, hN0, hN⟩ := exists_int_smul_mem_coreLattice b H
  refine ⟨N * r * c, mul_ne_zero (mul_ne_zero hN0 hr0) hc0, ?_⟩
  have hX : ∀ a, IsIntegral ℤ (vecCoords K b ((c : K) • (Pi.single i (1 : K ⊗[K] E) : ι → K ⊗[K] E)) a) := by
    rintro ⟨j, k⟩
    rw [vecCoords_smul]
    simp only [vecCoords]
    by_cases hj : j = i
    · subst hj
      rw [Pi.single_eq_same, Algebra.TensorProduct.one_def, repr_one_tmul, Algebra.algebraMap_self,
        RingHom.id_apply]
      exact hc _ (Finset.mem_image_of_mem _ (Finset.mem_univ k))
    · rw [Pi.single_eq_of_ne hj, map_zero, Finsupp.zero_apply, mul_zero]
      exact isIntegral_zero
  have := hN g _ (hr _ hX)
  rwa [smul_smul, smul_smul, ← Int.cast_mul, ← Int.cast_mul] at this

end Bounds

end GroundTheory.Heights₂.Heights.FiniteCovolume
end
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.FiniteCovolume.MajorantInvolutionDiagonalForm
section
namespace GroundTheory.Heights₂.Heights.FiniteCovolume

open NumberField GroundTheory.Automorphic Module Matrix Topology MeasureTheory
open scoped Pointwise ComplexOrder ENNReal

noncomputable section

section MatrixLevel

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def IsMajorantOf (H P : Matrix ι ι ℂ) : Prop :=
  P.PosDef ∧ H.IsHermitian ∧ IsUnit H.det ∧ P * H⁻¹ * P = H

def majInvolution (H P : Matrix ι ι ℂ) : Matrix ι ι ℂ := H⁻¹ * P

def plusPart (H P : Matrix ι ι ℂ) (z : ι → ℂ) : ι → ℂ :=
  (1 / 2 : ℂ) • (z + majInvolution H P *ᵥ z)

def minusPart (H P : Matrix ι ι ℂ) (z : ι → ℂ) : ι → ℂ :=
  (1 / 2 : ℂ) • (z - majInvolution H P *ᵥ z)

def pReflection (P : Matrix ι ι ℂ) (v : ι → ℂ) : Matrix ι ι ℂ :=
  1 - (2 / (star v ⬝ᵥ (P *ᵥ v))) • (vecMulVec v (star v) * P)

def phaseOnMinus (H P : Matrix ι ι ℂ) (c : ℂ) : Matrix ι ι ℂ :=
  (1 / 2 : ℂ) • (1 + majInvolution H P) + (c / 2) • (1 - majInvolution H P)

variable (ι)

def MajorantBound.Statement : Prop :=
  ∀ H P : Matrix ι ι ℂ, IsMajorantOf H P → ∀ z : ι → ℂ,
    ‖star z ⬝ᵥ (H *ᵥ z)‖ ≤ (star z ⬝ᵥ (P *ᵥ z)).re

def EigenspacesOrthogonal.Statement : Prop :=
  ∀ H P : Matrix ι ι ℂ, IsMajorantOf H P → ∀ a b : ι → ℂ,
    majInvolution H P *ᵥ a = a → majInvolution H P *ᵥ b = -b → star a ⬝ᵥ (P *ᵥ b) = 0

def IsotropicSplit.Statement : Prop :=
  ∀ H P : Matrix ι ι ℂ, IsMajorantOf H P → ∀ z : ι → ℂ, star z ⬝ᵥ (H *ᵥ z) = 0 →
    majInvolution H P *ᵥ plusPart H P z = plusPart H P z ∧
    majInvolution H P *ᵥ minusPart H P z = -minusPart H P z ∧
    star (plusPart H P z) ⬝ᵥ (P *ᵥ plusPart H P z) =
      star (minusPart H P z) ⬝ᵥ (P *ᵥ minusPart H P z)

def EigenReflection.Statement : Prop :=
  ∀ H P : Matrix ι ι ℂ, IsMajorantOf H P → ∀ ε : ℂ, (ε = 1 ∨ ε = -1) → ∀ v : ι → ℂ, v ≠ 0 →
    majInvolution H P *ᵥ v = ε • v →
    (pReflection P v)ᴴ * P * pReflection P v = P ∧ (pReflection P v)ᴴ * H * pReflection P v = H ∧
      pReflection P v *ᵥ v = -v ∧ ∀ u : ι → ℂ, star v ⬝ᵥ (P *ᵥ u) = 0 → pReflection P v *ᵥ u = u

def EigenReflectionMaps.Statement : Prop :=
  ∀ H P : Matrix ι ι ℂ, IsMajorantOf H P → ∀ ε : ℂ, (ε = 1 ∨ ε = -1) → ∀ a a' : ι → ℂ,
    majInvolution H P *ᵥ a = ε • a → majInvolution H P *ᵥ a' = ε • a' →
    star a ⬝ᵥ (P *ᵥ a) = star a' ⬝ᵥ (P *ᵥ a') →
    ∃ α : ℂ, ‖α‖ = 1 ∧ ∃ R : Matrix ι ι ℂ, Rᴴ * P * R = P ∧ Rᴴ * H * R = H ∧ R *ᵥ a' = α • a ∧
      ∀ u : ι → ℂ, majInvolution H P *ᵥ u = (-ε) • u → R *ᵥ u = u

def PhaseOnMinus.Statement : Prop :=
  ∀ H P : Matrix ι ι ℂ, IsMajorantOf H P → ∀ c : ℂ, ‖c‖ = 1 →
    (phaseOnMinus H P c)ᴴ * P * phaseOnMinus H P c = P ∧
      (phaseOnMinus H P c)ᴴ * H * phaseOnMinus H P c = H ∧
      (∀ u : ι → ℂ, majInvolution H P *ᵥ u = u → phaseOnMinus H P c *ᵥ u = u) ∧
      (∀ u : ι → ℂ, majInvolution H P *ᵥ u = -u → phaseOnMinus H P c *ᵥ u = c • u)

def KTransitive.Statement : Prop :=
  ∀ H P : Matrix ι ι ℂ, IsMajorantOf H P → ∀ z z' : ι → ℂ, z ≠ 0 → z' ≠ 0 →
    star z ⬝ᵥ (H *ᵥ z) = 0 → star z' ⬝ᵥ (H *ᵥ z') = 0 →
    ∃ k : GL ι ℂ, k ∈ unitaryGroupMatrix (starRingEnd ℂ) H ∧
      k ∈ unitaryGroupMatrix (starRingEnd ℂ) P ∧ ∃ c : ℂ, (k : Matrix ι ι ℂ) *ᵥ z' = c • z

end MatrixLevel

section Places

variable {F E : Type*} [Field F] [Field E] [NumberField F] [NumberField E] [Algebra F E]
  [Algebra.IsQuadraticExtension F E] [IsTotallyReal F] [_root_.NumberField.IsTotallyComplex E]
variable {W : Type*} [AddCommGroup W] [Module E W] {ι : Type*} [Fintype ι] [DecidableEq ι]

def HermAtPlace.Statement (h : HermitianForm F E W) (v : Basis ι E W) : Prop :=
  ∀ (w : InfinitePlace E) (x y : W),
    w.embedding (h.toSesq x y) = star (vecAt v x w) ⬝ᵥ (gramAt h v w *ᵥ vecAt v y w)

def GramAtData.Statement (h : HermitianForm F E W) (v : Basis ι E W) : Prop :=
  ∀ w : InfinitePlace E, (gramAt h v w).IsHermitian ∧ IsUnit (gramAt h v w).det

def ArchInvariant.Statement (h : HermitianForm F E W) (v : Basis ι E W) : Prop :=
  ∀ (g : archUnitary h v) (y z : InfinitePlace E → ι → ℂ) (w : InfinitePlace E),
    star (invApply g y w) ⬝ᵥ (gramAt h v w *ᵥ invApply g z w) =
      star (y w) ⬝ᵥ (gramAt h v w *ᵥ z w)

def LenSq.Statement (h : HermitianForm F E W) (v : Basis ι E W) : Prop :=
  ∀ (M : Majorant h v) (y : InfinitePlace E → ι → ℂ),
    (∀ w, 0 ≤ (star (y w) ⬝ᵥ (M.P w *ᵥ y w)).re) ∧
      M.len y ^ 2 = ∑ w, (star (y w) ⬝ᵥ (M.P w *ᵥ y w)).re

def VecAtNeZero.Statement (v : Basis ι E W) : Prop :=
  ∀ x : W, x ≠ 0 → ∀ w : InfinitePlace E, vecAt v x w ≠ 0


variable (E) in
def IntegerSmallAtPlaces.Statement : Prop :=
  ∀ a ∈ integralClosure ℤ E, (∀ w : InfinitePlace E, w a < 1) → a = 0

end Places

section Line

variable {E : Type*} [Field E] [NumberField E]
variable {W : Type*} [AddCommGroup W] [Module E W]


variable (E) in
def intSubgroup : AddSubgroup E := (algebraMap (𝓞 E) E).toAddMonoidHom.range

def lineCoeffs (La : AddSubgroup W) (x : W) : AddSubgroup E :=
  La.comap ((smulAddHom E W).flip x)

def weightedEmbed (c : InfinitePlace E → ℝ) : E →+ EuclideanSpace ℝ (InfinitePlace E × Fin 2) where
  toFun a := WithLp.toLp 2 fun p =>
    Real.sqrt (c p.1) * (if p.2 = 0 then (p.1.embedding a).re else (p.1.embedding a).im)
  map_zero' := by
    ext p
    simp
  map_add' a b := by
    ext p
    simp only [map_add (f := _), Complex.add_re, Complex.add_im, PiLp.add_apply]
    split_ifs <;> ring


variable (W) in
def LineIndexCoeffs.Statement : Prop :=
  ∀ (La : AddSubgroup W) (x : W), x ≠ 0 →
    lineIndex E La x = (intSubgroup E).relIndex (lineCoeffs La x)


variable (W) in
def LineCoeffsFG.Statement : Prop :=
  ∀ (La : AddSubgroup W) (x : W), La.FG → x ≠ 0 → (lineCoeffs (E := E) La x).FG

variable (E)

def CoeffLatticeBasis.Statement : Prop :=
  ∀ A : AddSubgroup E, intSubgroup E ≤ A → A.FG → Nonempty (Basis (Fin (finrank ℚ E)) ℤ A)

def IndexLeDet.Statement : Prop :=
  ∀ A : AddSubgroup E, intSubgroup E ≤ A → ∀ (e : Basis (Fin (finrank ℚ E)) ℤ A)
    (a : Fin (finrank ℚ E) → 𝓞 E) (T : Matrix (Fin (finrank ℚ E)) (Fin (finrank ℚ E)) ℤ),
    LinearIndependent ℚ (fun i => (a i : E)) → (∀ i, (a i : E) = ∑ j, T i j • (e j : E)) →
    ((intSubgroup E).relIndex A : ℝ) ≤ |(T.det : ℝ)|

def WeightedNormSq.Statement : Prop :=
  ∀ c : InfinitePlace E → ℝ, (∀ w, 0 ≤ c w) → ∀ a : E,
    ‖weightedEmbed c a‖ ^ 2 = ∑ w, c w * ‖w.embedding a‖ ^ 2

def WeightedSpaceDim.Statement [_root_.NumberField.IsTotallyComplex E] : Prop :=
  finrank ℝ (EuclideanSpace ℝ (InfinitePlace E × Fin 2)) = finrank ℚ E

def WeightedIndexBound.Statement [_root_.NumberField.IsTotallyComplex E] : Prop :=
  ∀ c : InfinitePlace E → ℝ, (∀ w, 0 < c w) → ∀ A : AddSubgroup E, intSubgroup E ≤ A → A.FG →
    (∀ a ∈ A, a ≠ 0 → ∑ w, c w ≤ ∑ w, c w * ‖w.embedding a‖ ^ 2) →
    ∀ r : ℝ, (∃ a : Fin (finrank ℚ E) → 𝓞 E, LinearIndependent ℚ (fun i => (a i : E)) ∧
      ∀ i (σ : E →+* ℂ), ‖σ (a i)‖ ≤ r) →
    ((intSubgroup E).relIndex A : ℝ) ≤ (r * Real.sqrt (finrank ℚ E)) ^ finrank ℚ E

end Line

section Minkowski

variable (V : Type*) [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  (d : ℕ) [Fact (finrank ℝ V = d)]

def MinkowskiVolumeForm.Statement : Prop :=
  ∀ (o : Orientation ℝ V (Fin d)) (b : Fin d → V) (lam : ℝ), 0 < lam →
    (∀ z : Fin d → ℤ, z ≠ 0 → lam ≤ ‖∑ i, (z i : ℝ) • b i‖) →
    (lam / Real.sqrt d) ^ d ≤ |o.volumeForm b|

def VolumeFormIntComb.Statement : Prop :=
  ∀ (o : Orientation ℝ V (Fin d)) (b : Fin d → V) (T : Matrix (Fin d) (Fin d) ℤ),
    o.volumeForm (fun i => ∑ j, (T i j : ℝ) • b j) = (T.det : ℝ) * o.volumeForm b

end Minkowski

section Steps

variable {F E : Type*} [Field F] [Field E] [NumberField F] [NumberField E] [Algebra F E]
  [Algebra.IsQuadraticExtension F E] [IsTotallyReal F] [_root_.NumberField.IsTotallyComplex E]
variable {W : Type*} [AddCommGroup W] [Module E W] {ι : Type*} [Fintype ι] [DecidableEq ι]

def WeightedLenSmul.Statement (h : HermitianForm F E W) (v : Basis ι E W) : Prop :=
  ∀ (M : Majorant h v) (g : archUnitary h v) (x : W) (a : E),
    M.len (invApply g (vecAt v (a • x))) ^ 2 =
      ∑ w, ‖w.embedding a‖ ^ 2 *
        (star (invApply g (vecAt v x) w) ⬝ᵥ (M.P w *ᵥ invApply g (vecAt v x) w)).re

def WeightPos.Statement (h : HermitianForm F E W) (v : Basis ι E W) : Prop :=
  ∀ (M : Majorant h v) (g : archUnitary h v) (x : W), x ≠ 0 → ∀ w : InfinitePlace E,
    0 < (star (invApply g (vecAt v x) w) ⬝ᵥ (M.P w *ᵥ invApply g (vecAt v x) w)).re

end Steps

section Inhabitants

open GaussianPlane

def e1 : Fin 2 → ℂ := Pi.single 0 1

def e2 : Fin 2 → ℂ := Pi.single 1 1

end Inhabitants

end

end GroundTheory.Heights₂.Heights.FiniteCovolume
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.FiniteCovolume.StatementsAdelicSplit
section
namespace GroundTheory.Heights₂.Heights.FiniteCovolume

open NumberField GroundTheory.Automorphic Module Matrix Topology MeasureTheory IsDedekindDomain
open scoped Pointwise ComplexOrder ENNReal NumberField.AdeleRing

noncomputable section

variable {F E : Type*} [Field F] [Field E] [NumberField F] [NumberField E] [Algebra F E]
  [Algebra.IsQuadraticExtension F E] [IsTotallyReal F] [_root_.NumberField.IsTotallyComplex E]
variable {W : Type*} [AddCommGroup W] [Module E W] {ι : Type*} [Fintype ι] [DecidableEq ι]

def adeleSplit (h : HermitianForm F E W) (v : Basis ι E W) :
    unitaryPoints F E (gram h.toSesq v) 𝔸[F] ≃ₜ*
      unitaryPoints F E (gram h.toSesq v) (InfiniteAdeleRing F) ×
        unitaryPoints F E (gram h.toSesq v) (FiniteAdeleRing (𝓞 F) F) :=
  (unitaryCongr (gram h.toSesq v) (adeleRingEquivProd F) (by exact continuous_id)
      (by exact continuous_id)).trans
    (unitaryProdEquiv F (gram h.toSesq v) _ _ (isUnit_det_gram h v))

def ArchimedeanUnitaryEquiv.Statement (h : HermitianForm F E W) (v : Basis ι E W) : Prop :=
  ∃ ψ : unitaryPoints F E (gram h.toSesq v) (InfiniteAdeleRing F) ≃ₜ* archUnitary h v,
    ∀ γ : h.unitaryGroup, ψ (adeleSplit h v (hermitianDiagonal h v γ)).1 = archEmbed h v γ

end

end GroundTheory.Heights₂.Heights.FiniteCovolume
end

