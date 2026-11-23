module

public import Mathlib
public import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
public import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.IsDiscriminantTwelfthRootOfIdealLattice
public import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.Bundle0001
public import Formalism.LocalRingCardinality.SpanPowerMembership.Spaces
public import Formalism.HermitianLattices.HermitianLatticesProofs.MassBasic
public import Formalism.SharpRestriction.CuspSpanNormBounds.RelevantZeroGramTerms
public import Formalism.LocalRingCardinality.DataCD

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.BlockTheory.GlobalSignature.ClassMeanPeriods
section
noncomputable section

namespace GlobalTheory.IndefiniteRowSideFullHecke.ClassMeanPeriods

open NumberField Formalism.BasicNotions Formalism.MainNotions.TaylorLogMetric
open scoped nonZeroDivisors

def period (D : D7) (c : (Ideal (𝓞 D.host.K))⁰) : ℝ :=
  ‖discr (lamOf D (c : Ideal (𝓞 D.host.K)) 1)‖ ^ ((1 : ℝ) / 6) *
    area (lamOf D (c : Ideal (𝓞 D.host.K)) 1) / Real.pi

def IsReps (D : D7) (r : ClassGroup (𝓞 D.host.K) → (Ideal (𝓞 D.host.K))⁰) : Prop :=
  ∀ C, ClassGroup.mk0 (r C) = C

def meanLogPeriod (D : D7) (r : ClassGroup (𝓞 D.host.K) → (Ideal (𝓞 D.host.K))⁰) : ℝ :=
  (∑ C : ClassGroup (𝓞 D.host.K), Real.log (period D (r C))) / (classNumber D.host.K : ℝ)

def classMeanValue (D : D7) : ℝ :=
  Real.eulerMascheroniConstant + Real.log (2 * Real.pi / Real.sqrt (D.host.d : ℝ)) - logDerivativeAtOne D

def ClassMeanAt (D : D7) : Prop :=
  ∀ r : ClassGroup (𝓞 D.host.K) → (Ideal (𝓞 D.host.K))⁰, IsReps D r →
    meanLogPeriod D r = classMeanValue D

def ClassMean : Prop :=
  ∀ (D : D7) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ),
    IsCurveIdeal D cc → IsDiscriminantTwelfthRootOfIdealLattice D cc δ → ClassMeanAt D

theorem exists_curveIdeal_delta (D : D7) :
    ∃ (cc : Ideal (𝓞 D.host.K)) (δ : ℂ), IsCurveIdeal D cc ∧ IsDiscriminantTwelfthRootOfIdealLattice D cc δ := by
  obtain ⟨δ, hδ⟩ := IsAlgClosed.exists_pow_nat_eq (discr (lamOf D ⊤ 1)) (n := 12) (by norm_num)
  exact ⟨⊤, δ, ⟨top_ne_bot, by simp⟩, hδ⟩

theorem classMean_iff : ClassMean ↔ ∀ D : D7, ClassMeanAt D := by
  refine ⟨fun h D => ?_, fun h D _ _ _ _ => h D⟩
  obtain ⟨cc, δ, h1, h2⟩ := exists_curveIdeal_delta D
  exact h D cc δ h1 h2

end GlobalTheory.IndefiniteRowSideFullHecke.ClassMeanPeriods
end
end

-- bundled from Development.AbelianVarietyTheory.BlockTheory.GlobalSignature.EquidistributedConjugates
section
noncomputable section

namespace GlobalTheory.IndefiniteRowSideFullHecke.EquidistributedConjugates

open NumberField Formalism.BasicNotions Formalism.MainNotions.TaylorLogMetric
open scoped nonZeroDivisors

def ContainsData (D : D7) (M : IntermediateField ℚ ℂ) (Λ : AddSubgroup ℂ) : Prop :=
  (∀ x : D.host.K, D.host.φ₀ (x : D.host.E) ∈ M) ∧ g2 Λ ∈ M ∧ g3 Λ ∈ M

def FixesK (D : D7) (M : IntermediateField ℚ ℂ) (ρ : M →ₐ[ℚ] ℂ) : Prop :=
  ∀ (x : D.host.K) (y : M), (y : ℂ) = D.host.φ₀ (x : D.host.E) → ρ y = (y : ℂ)

def conjEmb (M : IntermediateField ℚ ℂ) (ρ : M →ₐ[ℚ] ℂ) : M →ₐ[ℚ] ℂ :=
  ((Complex.conjAe : ℂ →ₐ[ℝ] ℂ).restrictScalars ℚ).comp ρ

def HomotheticTo (D : D7) (Λ' : AddSubgroup ℂ) (c' : Ideal (𝓞 D.host.K)) : Prop :=
  ∃ x : ℂ, x ≠ 0 ∧ Λ' = lamOf D c' x

def normArea (D : D7) (c' : Ideal (𝓞 D.host.K)) : ℝ :=
  ‖Formalism.MainNotions.TaylorLogMetric.discr (lamOf D c' 1)‖ ^ ((1 : ℝ) / 6) * area (lamOf D c' 1)

def ConjugatesEquidistributed : Prop :=
  ∀ (D : D7) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ), IsCurveIdeal D cc → IsDiscriminantTwelfthRootOfIdealLattice D cc δ →
  ∀ (M : IntermediateField ℚ ℂ) [FiniteDimensional ℚ M], ContainsData D M (lamOf D cc δ) →
    (∃ c : {ρ : M →ₐ[ℚ] ℂ // FixesK D M ρ} → (Ideal (𝓞 D.host.K))⁰,
      (∀ ρ, HomotheticTo D (lamConj M ρ.1 (lamOf D cc δ)) (c ρ : Ideal (𝓞 D.host.K))) ∧
      ∀ C C' : ClassGroup (𝓞 D.host.K),
        Nat.card {ρ // ClassGroup.mk0 (c ρ) = C} = Nat.card {ρ // ClassGroup.mk0 (c ρ) = C'}) ∧
    (∀ ρ : M →ₐ[ℚ] ℂ, ¬ FixesK D M ρ →
      FixesK D M (conjEmb M ρ) ∧
      area (lamConj M ρ (lamOf D cc δ)) = area (lamConj M (conjEmb M ρ) (lamOf D cc δ))) ∧
    (∀ r : ClassGroup (𝓞 D.host.K) → (Ideal (𝓞 D.host.K))⁰, (∀ C, ClassGroup.mk0 (r C) = C) →
      (∑ ρ : M →ₐ[ℚ] ℂ, Real.log (area (lamConj M ρ (lamOf D cc δ)))) / (Module.finrank ℚ M : ℝ) =
        (∑ C : ClassGroup (𝓞 D.host.K), Real.log (normArea D (r C : Ideal (𝓞 D.host.K)))) /
          (classNumber D.host.K : ℝ))

theorem conjEmb_apply (M : IntermediateField ℚ ℂ) (ρ : M →ₐ[ℚ] ℂ) (y : M) :
    conjEmb M ρ y = (starRingEnd ℂ) (ρ y) := rfl

theorem exists_representatives (D : D7) :
    ∃ r : ClassGroup (𝓞 D.host.K) → (Ideal (𝓞 D.host.K))⁰, ∀ C, ClassGroup.mk0 (r C) = C :=
  ⟨Function.surjInv ClassGroup.mk0_surjective, Function.surjInv_eq _⟩

end GlobalTheory.IndefiniteRowSideFullHecke.EquidistributedConjugates
end
end

-- bundled from Development.AbelianVarietyTheory.BlockTheory.GlobalSignature.MassFormulaPositivity
section
noncomputable section

namespace GlobalTheory.IndefiniteRowSideFullHecke.MassFormulaPositivity

open NumberField Formalism.BasicNotions


open scoped ComplexOrder in
theorem posDef_of_hasSignature {n : Type} [Fintype n] [DecidableEq n] {J : Matrix n n ℂ} {p : ℕ}
    (h : Formalism.UG.HasSignature J p 0) : J.PosDef := by
  obtain ⟨e, P, hP⟩ := h
  have hJ : Formalism.UG.Jpq p 0 = 1 := by
    ext i j
    rcases i with i | i
    · rcases j with j | j
      · simp [Formalism.UG.Jpq, Matrix.one_apply]
      · exact j.elim0
    · exact i.elim0
  have hc : Formalism.UG.cT (starRingEnd ℂ) (P : Matrix (Fin p ⊕ Fin 0) (Fin p ⊕ Fin 0) ℂ) =
      star (P : Matrix (Fin p ⊕ Fin 0) (Fin p ⊕ Fin 0) ℂ) := by
    ext i j; rfl
  rw [hJ, hc] at hP
  have h1 : (J.reindex e e).PosDef := by
    rw [← Matrix.IsUnit.posDef_star_left_conjugate_iff (Units.isUnit P), hP]
    exact Matrix.PosDef.one
  have h2 := h1.submatrix (e := e) e.injective
  simpa using h2

theorem trace_pos {E : Type} [Field E] [NumberField E] [StarRing E]
    (hst : ∀ (φ : E →+* ℂ) (a : E), φ (star a) = starRingEnd ℂ (φ a))
    (W : HSpace E) (hs : W.SigOK) {p : ℕ} (hp : ∀ τ : E →+* ℂ, W.sig τ = (p, 0))
    (x : W.V) (hx : x ≠ 0) : 0 < Algebra.trace ℚ E (W.hT x x) := by
  classical
  have hloc : ∀ τ : E →+* ℂ, 0 < (τ (W.hT x x)).re := by
    intro τ
    have h0 := hs τ
    rw [hp τ] at h0
    have hpd := posDef_of_hasSignature h0
    have hv : (fun i => τ (W.frame.repr x i)) ≠ 0 := by
      intro h
      apply hx
      apply W.frame.repr.injective
      ext i
      simpa using congrFun h i
    have h1 := hpd.re_dotProduct_pos hv
    have h2 : τ (W.hT x x) = star (fun i => τ (W.frame.repr x i)) ⬝ᵥ
        (W.gram.map τ).mulVec (fun i => τ (W.frame.repr x i)) := by
      conv_lhs => rw [← W.frame.sum_repr x]
      set_option synthInstance.maxHeartbeats 100000 in
        simp only [map_sum, LinearMap.sum_apply, LinearMap.map_smulₛₗ, LinearMap.smul_apply,
        smul_eq_mul, map_mul, RingHom.id_apply, starRingEnd_apply, hst, dotProduct, Matrix.mulVec,
        Matrix.map_apply, HSpace.gram, Pi.star_apply, Finset.mul_sum]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
      ring
    rw [h2]
    exact h1
  have ht := trace_eq_sum_embeddings ℂ (K := ℚ) (L := E) (x := W.hT x x)
  have hre := congrArg Complex.re ht
  rw [Complex.re_sum] at hre
  have hpos : 0 < ∑ σ : E →ₐ[ℚ] ℂ, (σ (W.hT x x)).re :=
    Finset.sum_pos (fun σ _ => hloc (σ : E →+* ℂ)) ⟨IsAlgClosed.lift, Finset.mem_univ _⟩
  rw [← hre] at hpos
  simpa using hpos

end GlobalTheory.IndefiniteRowSideFullHecke.MassFormulaPositivity
end
end

-- bundled from Development.AbelianVarietyTheory.BlockTheory.GlobalSignature.MeanPeriodLogarithms
section
noncomputable section

namespace GlobalTheory.IndefiniteRowSideFullHecke.MeanPeriodLogarithms

open NumberField Formalism.BasicNotions Formalism.MainNotions.TaylorLogMetric

def MeanPeriodAt (D : D7) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) : Prop :=
  ∀ (M : IntermediateField ℚ ℂ) [NumberField M], DataIn D (tor0 D cc δ) M →
    ∀ τ : D.what₂.Tau, meanLogOm D (tor0 D cc δ).abelian₂ M τ = logOmVal D

def MeanPeriod : Prop :=
  ∀ (D : D7) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ), IsCurveIdeal D cc → IsDiscriminantTwelfthRootOfIdealLattice D cc δ →
    MeanPeriodAt D cc δ

theorem logOmVal_eq (D : D7) :
    logOmVal D = Real.eulerMascheroniConstant + Real.log (2 * Real.pi / D.host.rdE) - logDerivativeAtOne D := by
  have h : Real.pi / D.host.v = 2 * Real.pi / D.host.rdE := by
    unfold Host.v
    rw [div_div_eq_mul_div, mul_comm]
  unfold logOmVal
  rw [h]

end GlobalTheory.IndefiniteRowSideFullHecke.MeanPeriodLogarithms
end
end

-- bundled from Development.AbelianVarietyTheory.BlockTheory.GlobalSignature.PeriodLatticeAgreement
section
noncomputable section

namespace GlobalTheory.IndefiniteRowSideFullHecke.PeriodLatticeAgreement

open Formalism.MainNotions.TaylorLogMetric
open scoped UpperHalfPlane

def latt (ω₁ τ : ℂ) : AddSubgroup ℂ where
  carrier := {w | ∃ m n : ℤ, w = ω₁ * ((m : ℂ) + (n : ℂ) * τ)}
  zero_mem' := ⟨0, 0, by simp⟩
  add_mem' := by
    rintro _ _ ⟨m, n, rfl⟩ ⟨m', n', rfl⟩
    exact ⟨m + m', n + n', by push_cast; ring⟩
  neg_mem' := by
    rintro _ ⟨m, n, rfl⟩
    exact ⟨-m, -n, by push_cast; ring⟩

def scale (c : ℂ) (Λ : AddSubgroup ℂ) : AddSubgroup ℂ := Λ.map (AddMonoidHom.mulLeft c)

def period (Λ : AddSubgroup ℂ) : ℝ := ‖discr Λ‖ ^ ((1 : ℝ) / 6) * area Λ / Real.pi

def DiscrEta : Prop :=
  ∀ (ω₁ : ℂ) (τ : ℍ), ω₁ ≠ 0 →
    discr (latt ω₁ τ) = (2 * (Real.pi : ℂ) / ω₁) ^ 12 * ModularForm.eta (τ : ℂ) ^ 24

def AreaEq : Prop :=
  ∀ (ω₁ : ℂ) (τ : ℍ), ω₁ ≠ 0 → area (latt ω₁ τ) = ‖ω₁‖ ^ 2 * τ.im

def PeriodEta : Prop :=
  ∀ (ω₁ : ℂ) (τ : ℍ), ω₁ ≠ 0 →
    period (latt ω₁ τ) = 4 * Real.pi * τ.im * ‖ModularForm.eta (τ : ℂ)‖ ^ 4

def DiscrScale : Prop :=
  ∀ (ω₁ : ℂ) (τ : ℍ) (c : ℂ), ω₁ ≠ 0 → c ≠ 0 →
    discr (scale c (latt ω₁ τ)) = c ^ (-12 : ℤ) * discr (latt ω₁ τ)

def AgreePeriodPair : Prop :=
  ∀ L : PeriodPair,
    (∀ k : ℕ, 2 ≤ k →
      Summable (fun w : {w : ℂ // w ∈ L.lattice.toAddSubgroup ∧ w ≠ 0} => 1 / (w : ℂ) ^ (2 * k)) ∧
      eisG L.lattice.toAddSubgroup k = L.G (2 * k)) ∧
    g2 L.lattice.toAddSubgroup = L.g₂ ∧ g3 L.lattice.toAddSubgroup = L.g₃

def LatticePeriodEta : Prop :=
  DiscrEta ∧ AreaEq ∧ PeriodEta ∧ DiscrScale ∧ AgreePeriodPair

theorem mem_latt {ω₁ τ w : ℂ} : w ∈ latt ω₁ τ ↔ ∃ m n : ℤ, w = ω₁ * ((m : ℂ) + (n : ℂ) * τ) := Iff.rfl

theorem mem_scale {c w : ℂ} {Λ : AddSubgroup ℂ} : w ∈ scale c Λ ↔ ∃ v ∈ Λ, c * v = w := by
  simp [scale, AddSubgroup.mem_map]

theorem scale_latt (c ω₁ τ : ℂ) : scale c (latt ω₁ τ) = latt (c * ω₁) τ := by
  ext w
  rw [mem_scale, mem_latt]
  constructor
  · rintro ⟨_, ⟨m, n, rfl⟩, rfl⟩
    exact ⟨m, n, by ring⟩
  · rintro ⟨m, n, rfl⟩
    exact ⟨_, ⟨m, n, rfl⟩, by ring⟩

end GlobalTheory.IndefiniteRowSideFullHecke.PeriodLatticeAgreement
end
end

-- bundled from Development.AbelianVarietyTheory.BlockTheory.GlobalSignature.SignatureFrame
section
open MeasureTheory Matrix Finset

noncomputable section

namespace GlobalTheory.IndefiniteRowSideFullHecke.SignatureFrame

open Formalism.BasicNotions Formalism.MainNotions.S Formalism.REAL Formalism.QuantumDeterminants

structure SignFrame {n : ℕ} (ε : Fin n → Bool) (P Q : ℕ) where

  e : Fin P ⊕ Fin Q ≃ Fin n
  pos : ∀ i, ε (e (Sum.inl i)) = true
  neg : ∀ j, ε (e (Sum.inr j)) = false

variable {n P Q : ℕ} {ε : Fin n → Bool}

theorem SignFrame.reindex_J (F : SignFrame ε P Q) :
    Matrix.reindex F.e F.e (Formalism.UG.Jpq P Q) = Jm ε := by
  ext a b
  obtain ⟨x, rfl⟩ := F.e.surjective a
  obtain ⟨y, rfl⟩ := F.e.surjective b
  rcases x with x | x <;> rcases y with y | y <;>
    simp [Formalism.UG.Jpq, Jm, Matrix.diagonal_apply, Matrix.one_apply, F.pos, F.neg]
  split_ifs <;> simp

def SignFrame.unitsMap (F : SignFrame ε P Q) :
    GL (Fin P ⊕ Fin Q) ℂ →* (Matrix (Fin n) (Fin n) ℂ)ˣ :=
  Units.map (Matrix.reindexAlgEquiv ℂ ℂ F.e).toMulEquiv.toMonoidHom

theorem SignFrame.inUJ_reindex (F : SignFrame ε P Q)
    (m : Matrix (Fin P ⊕ Fin Q) (Fin P ⊕ Fin Q) ℂ) :
    inUJ ε (Matrix.reindex F.e F.e m) ↔
      Formalism.UG.cT (starRingEnd ℂ) m * Formalism.UG.Jpq P Q * m = Formalism.UG.Jpq P Q := by
  unfold inUJ
  rw [← F.reindex_J]
  have h : Formalism.UG.cT (starRingEnd ℂ) m = mᴴ := by
    ext i j; simp [Formalism.UG.cT]
  rw [h]
  simp only [Matrix.reindex_apply, Matrix.conjTranspose_submatrix, Matrix.submatrix_mul_equiv]
  exact (Matrix.reindex F.e F.e).injective.eq_iff (a := mᴴ * Formalism.UG.Jpq P Q * m) (b := Formalism.UG.Jpq P Q)

def SignFrame.toDiag (F : SignFrame ε P Q) (g : UpqT P Q) : UJ ε :=
  let g' : Formalism.UG.Upq P Q := g
  ⟨F.unitsMap g'.1, (F.inUJ_reindex _).2 g'.2⟩

def cdMeasure (c : CDHaar) (F : SignFrame ε P Q) : Measure (UJ ε) :=
  Measure.map F.toDiag (c.cd P Q)

def dimV {n : ℕ} (lam : Fin n → ℝ) : ℝ :=
  (∏ a : Fin n, ∏ b ∈ Ioi a, (lam a - lam b)) /
    ∏ a : Fin n, ∏ b ∈ Ioi a, (((b : ℕ) : ℝ) - ((a : ℕ) : ℝ))

end GlobalTheory.IndefiniteRowSideFullHecke.SignatureFrame
end
end

