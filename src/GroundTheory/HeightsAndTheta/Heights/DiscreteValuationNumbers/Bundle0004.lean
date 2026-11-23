module

public import Mathlib
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Bundle0003
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.StatementsCN
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Bundle0002

@[expose] public section

-- bundled from GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.IsMultiHomogIdealSpanSingleton
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.NumbersDVR

open MvPolynomial

noncomputable section

universe u

section Defs

variable {K : Type*} [DecidableEq K] {ι : K → Type*}
variable {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]

def IsEffectiveVertical (P : Ideal (MRing ι O)) (ϖ : O) (b : K → ℤ) (f g : MRing ι O) : Prop :=
  IsVerticalDivisor P ϖ b f g ∧ ∀ W : Ideal (MRing ι O), W.IsPrime → P ≤ W → IsRelevant W →
    ∃ u v : MRing ι O, u ∉ W ∧ u * f - v * g ∈ P


open Classical in
def cutIdentity (ϖ : O) (P : Ideal (MRing ι O)) (b : K → ℤ) (f g : MRing ι O) (c : K → ℕ)
    (s : MRing ι O) {d : ℕ} (L : Fin d → K → ℤ) : Prop :=
  by
    classical
    exact cycEval (fun G => vNum G (Matrix.vecCons (fun k => (c k : ℤ)) L)) (ratDiv P f g) =
      cycEval (fun W => if (C ϖ : MRing ι O) ∈ W then vNum W (Matrix.vecCons b L)
          else cycEval (fun G => vNum G L) (ratDiv W f g)) (divCycle P s)

end Defs

section Lemmas

def DivCycleMul.Statement : Prop :=
  ∀ (R : Type u) [CommRing R] [IsNoetherianRing R] (K : Type) [Fintype K] (ι : K → Type)
    [∀ k, Fintype (ι k)] (P : Ideal (MRing ι R)) (x y : MRing ι R), P.IsPrime → x ∉ P → y ∉ P →
    divCycle P (x * y) = divCycle P x + divCycle P y

def DivCycleFiniteSupport.Statement : Prop :=
  ∀ (R : Type u) [CommRing R] [IsNoetherianRing R] (K : Type) [Fintype K] (ι : K → Type)
    [∀ k, Fintype (ι k)] (P : Ideal (MRing ι R)) (f : MRing ι R),
    (Function.support (divCycle P f)).Finite

def SupSpanMultiHomog.Statement : Prop :=
  ∀ (R : Type u) [CommRing R] (K : Type) [DecidableEq K] (ι : K → Type) (I : Ideal (MRing ι R))
    (x : MRing ι R) (e : K → ℕ), IsMultiHomogIdeal I → IsMultiHomog x e →
    IsMultiHomogIdeal (I ⊔ Ideal.span {x})

def MinimalPrimeMultiHomog.Statement : Prop :=
  ∀ (R : Type u) [CommRing R] (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type)
    (J W : Ideal (MRing ι R)), IsMultiHomogIdeal J → W ∈ J.minimalPrimes → IsMultiHomogIdeal W

def IntNumAddFirst.Statement : Prop :=
  ∀ (F : Type u) [Field F] (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type)
    [∀ k, Fintype (ι k)] (n : ℕ) (G : Ideal (MRing ι F)), G.IsPrime → IsMultiHomogIdeal G →
    ringKrullDim (MRing ι F ⧸ G) < ((n + 2 + Fintype.card K : ℕ) : WithBot ℕ∞) →
    ∀ (b₁ b₂ : K → ℤ) (L : Fin n → K → ℤ),
      intNum F G (Matrix.vecCons (b₁ + b₂) L) =
        intNum F G (Matrix.vecCons b₁ L) + intNum F G (Matrix.vecCons b₂ L)

def SpecialQuotDim.Statement : Prop :=
  ∀ (O : Type u) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (ϖ : O), Irreducible ϖ →
    ∀ (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)] (W : Ideal (MRing ι O)), (C ϖ : MRing ι O) ∈ W →
    ringKrullDim (MRing ι (IsLocalRing.ResidueField O) ⧸ specialIdeal W) =
      ringKrullDim (MRing ι O ⧸ W)

def GenericDimBound.Statement : Prop :=
  ∀ (O : Type u) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (K : Type) [Fintype K]
    [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)] (P : Ideal (MRing ι O)),
    IsMultiProjPrime P → P.comap (C : O →+* MRing ι O) = ⊥ →
    ringKrullDim (MRing ι (FractionRing O) ⧸ genFib P) + 1 ≤ ringKrullDim (MRing ι O ⧸ P)

def GenericFibProps.Statement : Prop :=
  ∀ (O : Type u) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (K : Type) [Fintype K]
    [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)] (P : Ideal (MRing ι O)),
    IsMultiProjPrime P → P.comap (C : O →+* MRing ι O) = ⊥ →
    (genFib P).IsPrime ∧ IsMultiHomogIdeal (genFib P) ∧
    ∀ (s : MRing ι O) (c : K → ℕ), IsMultiHomog s c → s ∉ P →
      IsMultiHomog (MvPolynomial.map (algebraMap O (FractionRing O)) s) c ∧
        MvPolynomial.map (algebraMap O (FractionRing O)) s ∉ genFib P


open Classical in
def GenericCycleCorresp.Statement : Prop :=
  by
  classical
  exact ∀ (O : Type u) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (ϖ : O), Irreducible ϖ →
    ∀ (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)] (P : Ideal (MRing ι O)) (s : MRing ι O), P.IsPrime →
    P.comap (C : O →+* MRing ι O) = ⊥ → s ∉ P →
    ∀ n : Ideal (MRing ι (FractionRing O)) → ℤ,
      cycEval (fun W => if (C ϖ : MRing ι O) ∈ W then 0 else n (genFib W)) (divCycle P s) =
        cycEval n (divCycle (genFib P) (MvPolynomial.map (algebraMap O (FractionRing O)) s))

def ConservationOfNumberLE.Statement : Prop :=
  ∀ (O : Type u) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (ϖ : O), Irreducible ϖ →
    ∀ (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)] (P : Ideal (MRing ι O)) (d : ℕ), IsMultiProjPrime P →
    P.comap (C : O →+* MRing ι O) = ⊥ →
    ringKrullDim (MRing ι O ⧸ P) ≤ ((d + 1 + Fintype.card K : ℕ) : WithBot ℕ∞) →
    ∀ a : Fin d → K → ℤ, cycEval (fun W => vNum W a) (divCycle P (C ϖ)) = gNum P a

def UniformiserCase.Statement : Prop :=
  ∀ (O : Type u) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (ϖ : O), Irreducible ϖ →
    ∀ (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)] (P : Ideal (MRing ι O)) (d : ℕ), IsModelOver P (d + 1) →
    ∀ (c : K → ℕ) (s : MRing ι O), IsMultiHomog s c → s ∉ P →
    ∀ L : Fin d → K → ℤ, cutIdentity ϖ P 0 (C ϖ) 1 c s L

def ShiftByUniformiser.Statement : Prop :=
  ∀ (O : Type u) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (ϖ : O), Irreducible ϖ →
    ∀ (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)] (P : Ideal (MRing ι O)) (d : ℕ), IsModelOver P (d + 1) →
    ∀ (b : K → ℤ) (f g : MRing ι O), IsVerticalDivisor P ϖ b f g →
    ∀ (c : K → ℕ) (s : MRing ι O), IsMultiHomog s c → s ∉ P →
    (∀ H, divCycle P s H ≠ 0 → (C ϖ : MRing ι O) ∉ H → IsVerticalDivisor H ϖ b f g) →
    ∀ (L : Fin d → K → ℤ) (n : ℕ),
      cutIdentity ϖ P b (C ϖ ^ n * f) g c s L → cutIdentity ϖ P 0 (C ϖ) 1 c s L →
        cutIdentity ϖ P b f g c s L

def EffectiveShift.Statement : Prop :=
  ∀ (O : Type u) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (ϖ : O), Irreducible ϖ →
    ∀ (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)] (P : Ideal (MRing ι O)) (e : ℕ), IsModelOver P e →
    ∀ (b : K → ℤ) (f g : MRing ι O), IsVerticalDivisor P ϖ b f g →
    ∃ n : ℕ, IsEffectiveVertical P ϖ b (C ϖ ^ n * f) g

def EffectiveCase.Statement : Prop :=
  ∀ (O : Type u) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (ϖ : O), Irreducible ϖ →
    ∀ (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)] (P : Ideal (MRing ι O)) (d : ℕ), IsModelOver P (d + 1) →
    ∀ (b : K → ℤ) (f g : MRing ι O), IsEffectiveVertical P ϖ b f g →
    ∀ (c : K → ℕ) (s : MRing ι O), IsMultiHomog s c → s ∉ P →
    (∀ H, divCycle P s H ≠ 0 → (C ϖ : MRing ι O) ∉ H → IsVerticalDivisor H ϖ b f g) →
    ∀ L : Fin d → K → ℤ, cutIdentity ϖ P b f g c s L

def Representative.Statement : Prop :=
  ∀ (O : Type u) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (ϖ : O), Irreducible ϖ →
    ∀ (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)] (P : Ideal (MRing ι O)) (b : K → ℤ) (f g : MRing ι O), IsMultiProjPrime P →
    IsVerticalDivisor P ϖ b f g → ∀ T : Finset (Ideal (MRing ι O)),
    (∀ H ∈ T, IsMultiProjPrime H ∧ P ≤ H ∧ (C ϖ : MRing ι O) ∉ H ∧
      ∃ h : MRing ι O, h ∉ P ∧ H ∈ (P ⊔ Ideal.span {h}).minimalPrimes) →
    ∃ f₁ g₁ : MRing ι O, IsVerticalDivisor P ϖ b f₁ g₁ ∧ ratDiv P f₁ g₁ = ratDiv P f g ∧
      ∀ H ∈ T, IsVerticalDivisor H ϖ b f₁ g₁

end Lemmas

section Examples

theorem isMultiHomogIdeal_span_singleton {K : Type*} [DecidableEq K] {ι : K → Type*} {R : Type*}
    [CommRing R] {x : MRing ι R} {e : K → ℕ} (hx : IsMultiHomog x e) :
    IsMultiHomogIdeal (Ideal.span {x}) := by
  classical
  letI := MvPolynomial.weightedGradedAlgebra R (blockWeight ι)
  have h : (Ideal.span {x}).IsHomogeneous (weightedHomogeneousSubmodule R (blockWeight ι)) :=
    Ideal.homogeneous_span _ _ (by
      rintro y rfl
      exact ⟨e, hx⟩)
  intro f hf b
  exact MvPolynomial.weightedHomogeneousComponent_mem_of_mem R (blockWeight ι) h hf b

end Examples

end

end GroundTheory.Heights₂.Heights.NumbersDVR
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PAssociatedMultiHomogPrime
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.NumbersDVR

open MvPolynomial

universe u

theorem AssociatedMultiHomogPrime.proof (h1 : MultiHomogPrimeCriterion.Statement.{u})
    (h2 : ColonMultiHomog.Statement.{u}) : AssociatedMultiHomogPrime.Statement.{u} := by
  intro F _ K _ _ ι _ J hJ hJtop
  classical

  let A : Set (Ideal (MRing ι F)) :=
    {Q | ∃ (f : MRing ι F) (s : K → ℕ), IsMultiHomog f s ∧ f ∉ J ∧ Q = J.colon {f}}
  have hne : A.Nonempty := by
    refine ⟨J.colon {1}, 1, 0, ?_, ?_, rfl⟩
    · exact isWeightedHomogeneous_one F (blockWeight ι)
    · intro h
      exact hJtop ((Ideal.eq_top_iff_one J).2 h)
  have hnoeth : IsNoetherianRing (MRing ι F) := inferInstance
  obtain ⟨Q, ⟨f, s, hf, hfJ, rfl⟩, hmax⟩ :=
    (set_has_maximal_iff_noetherian (R := MRing ι F) (M := MRing ι F)).2 hnoeth A hne
  refine ⟨f, s, hf, hfJ, ?_⟩
  apply h1 F K ι (J.colon {f}) (h2 F K ι J f s hJ hf)
  · intro htop
    apply hfJ
    have h1mem : (1 : MRing ι F) ∈ J.colon {f} := by rw [htop]; exact Submodule.mem_top
    simpa using (Submodule.mem_colon_singleton.1 h1mem)
  · intro a b sa sb _ hb hab
    by_cases hbQ : b ∈ J.colon {f}
    · exact Or.inr hbQ
    left
    have hbf : b * f ∉ J := by
      intro h
      apply hbQ
      exact Submodule.mem_colon_singleton.2 (by simpa [smul_eq_mul] using h)
    have hform : IsMultiHomog (b * f) (sb + s) := hb.mul hf
    have hle : J.colon {f} ≤ J.colon {b * f} := by
      intro x hx
      have hx' : x * f ∈ J := by simpa [smul_eq_mul] using Submodule.mem_colon_singleton.1 hx
      refine Submodule.mem_colon_singleton.2 ?_
      have : b * (x * f) ∈ J := J.mul_mem_left b hx'
      simpa [smul_eq_mul, mul_comm, mul_left_comm, mul_assoc] using this
    have heq : J.colon {f} = J.colon {b * f} := by
      by_contra hne'
      exact hmax _ ⟨b * f, sb + s, hform, hbf, rfl⟩ (lt_of_le_of_ne hle hne')
    rw [heq]
    refine Submodule.mem_colon_singleton.2 ?_
    have hab' : a * b * f ∈ J := by simpa [smul_eq_mul] using Submodule.mem_colon_singleton.1 hab
    simpa [smul_eq_mul, mul_assoc] using hab'

end GroundTheory.Heights₂.Heights.NumbersDVR
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PBlockAdjoinPrime
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.NumbersDVR

open MvPolynomial

noncomputable section

namespace BlockAdjoinPrime

variable {R : Type*} [CommRing R] {K : Type*} {ι : K → Type*}


open Classical in
def killB (B : Set K) : MRing ι R →ₐ[R] MRing ι R :=
  by
    classical
    exact aeval fun v => if v.1 ∈ B then 0 else X v

def varIdeal (B : Set K) : Ideal (MRing ι R) :=
  Ideal.span {p | ∃ v : Σ k, ι k, v.1 ∈ B ∧ p = X v}

theorem killB_X_of_mem (B : Set K) {v : Σ k, ι k} (hv : v.1 ∈ B) :
    killB (R := R) B (X v) = 0 := by
  classical
  simp [killB, hv]

theorem killB_X_of_not_mem (B : Set K) {v : Σ k, ι k} (hv : v.1 ∉ B) :
    killB (R := R) B (X v) = X v := by
  classical
  simp [killB, hv]

open Classical in
theorem killB_monomial (B : Set K) (d : (Σ k, ι k) →₀ ℕ) (a : R) :
    killB (R := R) B (monomial d a) =
      if ∀ v ∈ d.support, v.1 ∉ B then monomial d a else 0 := by
  rw [killB, aeval_monomial]
  split_ifs with h
  · rw [monomial_eq, algebraMap_eq]
    congr 1
    refine Finsupp.prod_congr fun v hv => ?_
    rw [if_neg (h v hv)]
  · push Not at h
    obtain ⟨v, hv, hB⟩ := h
    rw [Finsupp.prod, Finset.prod_eq_zero hv, mul_zero]
    rw [if_pos hB, zero_pow (Finsupp.mem_support_iff.mp hv)]

open Classical in
theorem coeff_killB (B : Set K) (p : MRing ι R) (d : (Σ k, ι k) →₀ ℕ) :
    AddMonoidAlgebra.coeff (killB B p) d = if ∀ v ∈ d.support, v.1 ∉ B then AddMonoidAlgebra.coeff p d else 0 := by
  induction p using MvPolynomial.induction_on' with
  | monomial e a =>
    rw [killB_monomial]
    by_cases hed : e = d
    · subst hed
      split_ifs <;> simp
    · split_ifs <;> simp [coeff_monomial, hed]
  | add p q hp hq =>
    rw [map_add (f := _), MvPolynomial.coeff_add, hp, hq]
    split_ifs <;> simp

theorem sub_killB_mem (B : Set K) (p : MRing ι R) : p - killB B p ∈ varIdeal (R := R) B := by
  classical
  induction p using MvPolynomial.induction_on with
  | C a => simp
  | add p q hp hq =>
    rw [map_add (f := _), add_sub_add_comm]
    exact add_mem hp hq
  | mul_X p v hp =>
    have e : p * X v - killB B (p * X v) =
        (p - killB B p) * X v + killB B p * (X v - killB B (X v)) := by
      rw [map_mul]; ring
    rw [e]
    refine add_mem (Ideal.mul_mem_right _ _ hp) (Ideal.mul_mem_left _ _ ?_)
    by_cases hv : v.1 ∈ B
    · rw [killB_X_of_mem B hv, sub_zero]
      exact Ideal.subset_span ⟨v, hv, rfl⟩
    · rw [killB_X_of_not_mem B hv, sub_self]
      exact zero_mem _

variable [DecidableEq K]

theorem weight_eq_zero_iff (d : (Σ k, ι k) →₀ ℕ) (B : Set K) :
    (∀ k ∈ B, Finsupp.weight (blockWeight ι) d k = 0) ↔ ∀ v ∈ d.support, v.1 ∉ B := by
  have hw : ∀ k, Finsupp.weight (blockWeight ι) d k =
      ∑ i ∈ d.support, d i * (Pi.single i.1 1 : K → ℕ) k := by
    intro k
    rw [Finsupp.weight_apply, Finsupp.sum, Finset.sum_apply]
    rfl
  constructor
  · intro h v hv hB
    have h0 := h v.1 hB
    rw [hw, Finset.sum_eq_zero_iff] at h0
    have := h0 v hv
    simp [Finsupp.mem_support_iff.mp hv] at this
  · intro h k hk
    rw [hw, Finset.sum_eq_zero_iff]
    intro i hi
    have hik : i.1 ≠ k := fun e => h i hi (e ▸ hk)
    simp [Ne.symm hik]

theorem killB_mem {Q : Ideal (MRing ι R)} (hQ : IsMultiHomogIdeal Q) (B : Set K)
    {q : MRing ι R} (hq : q ∈ Q) : killB B q ∈ Q := by
  classical
  let M := (q.support.image (Finsupp.weight (blockWeight ι))).filter (fun m => ∀ k ∈ B, m k = 0)
  have key : killB B q = ∑ m ∈ M, weightedHomogeneousComponent (blockWeight ι) m q := by
    ext d
    rw [coeff_killB, coeff_sum]
    simp_rw [coeff_weightedHomogeneousComponent]
    rw [Finset.sum_ite_eq]
    by_cases hd : AddMonoidAlgebra.coeff q d = 0
    · simp [hd]
    · have hmem : d ∈ q.support := mem_support_iff.mpr hd
      have hiff : Finsupp.weight (blockWeight ι) d ∈ M ↔ ∀ v ∈ d.support, v.1 ∉ B := by
        rw [← weight_eq_zero_iff]
        simp only [M, Finset.mem_filter, Finset.mem_image]
        exact ⟨fun h => h.2, fun h => ⟨⟨d, hmem, rfl⟩, h⟩⟩
      by_cases hP : ∀ v ∈ d.support, v.1 ∉ B
      · rw [if_pos hP, if_pos (hiff.mpr hP)]
      · rw [if_neg hP, if_neg (fun h => hP (hiff.mp h))]
  rw [key]
  exact Q.sum_mem fun m _ => hQ q hq m

theorem sup_eq_comap {Q : Ideal (MRing ι R)} (hQ : IsMultiHomogIdeal Q) (B : Set K) :
    Q ⊔ varIdeal B = Q.comap (killB B) := by
  apply le_antisymm
  · refine sup_le (fun q hq => killB_mem hQ B hq) ?_
    refine Ideal.span_le.mpr ?_
    rintro _ ⟨v, hv, rfl⟩
    show killB B (X v) ∈ Q
    rw [killB_X_of_mem B hv]
    exact zero_mem _
  · intro p hp
    have : p = killB B p + (p - killB B p) := by ring
    rw [this]
    exact add_mem (Ideal.mem_sup_left hp) (Ideal.mem_sup_right (sub_killB_mem B p))

theorem proof : BlockAdjoinPrime.Statement := by
  intro R _ K _ _ ι Q B hP hQ
  have h := sup_eq_comap (R := R) hQ B
  change (Q ⊔ varIdeal B).IsPrime ∧ ∀ v : Σ k, ι k, v.1 ∉ B → (X v ∈ Q ⊔ varIdeal B ↔ X v ∈ Q)
  rw [h]
  refine ⟨Ideal.IsPrime.comap (killB B) (hK := hP), fun v hv => ?_⟩
  rw [Ideal.mem_comap, killB_X_of_not_mem B hv]

end BlockAdjoinPrime

end

end GroundTheory.Heights₂.Heights.NumbersDVR
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PColonMultiHomog
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.NumbersDVR

open MvPolynomial

theorem component_mul_multiHomog {R : Type*} [CommRing R] {K : Type} [DecidableEq K]
    {ι : K → Type} (y f : MRing ι R) (b s : K → ℕ) (hf : IsMultiHomog f s) :
    weightedHomogeneousComponent (blockWeight ι) b y * f =
      weightedHomogeneousComponent (blockWeight ι) (b + s) (y * f) := by
  classical
  ext d
  rw [coeff_weightedHomogeneousComponent, coeff_mul, coeff_mul]
  split_ifs with hd
  · refine Finset.sum_congr rfl fun x hx => ?_
    rw [coeff_weightedHomogeneousComponent]
    split_ifs with hx1
    · rfl
    · by_cases h2 : AddMonoidAlgebra.coeff f x.2 = 0
      · rw [h2, mul_zero, mul_zero]
      · exfalso
        apply hx1
        have hw := hf h2
        rw [Finset.HasAntidiagonal.mem_antidiagonal] at hx
        rw [← hx, map_add (f := _), hw] at hd
        exact add_right_cancel hd
  · refine Finset.sum_eq_zero fun x hx => ?_
    rw [coeff_weightedHomogeneousComponent]
    split_ifs with hx1
    · by_cases h2 : AddMonoidAlgebra.coeff f x.2 = 0
      · rw [h2, mul_zero]
      · exfalso
        apply hd
        have hw := hf h2
        rw [Finset.HasAntidiagonal.mem_antidiagonal] at hx
        rw [← hx, map_add (f := _), hw, hx1]
    · rw [zero_mul]

theorem ColonMultiHomog.proof : ColonMultiHomog.Statement := by
  intro R _ K _ ι I f s hI hf y hy b
  rw [Submodule.mem_colon_singleton, smul_eq_mul] at hy ⊢
  rw [component_mul_multiHomog y f b s hf]
  exact hI _ hy _

end GroundTheory.Heights₂.Heights.NumbersDVR
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PConservationOfNumber
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.NumbersDVR

open MvPolynomial

universe u

theorem ConservationOfNumber.proof (h1 : IntNumAssoc.Statement.{u})
    (h2 : SpecialCycleEval.Statement.{u}) (h3 : SpecialPieceRank.Statement.{u})
    (h4 : GenericPieceRank.Statement.{u}) (h5 : SpecialIdealMultiHomog.Statement.{u})
    (h6 : SpecialDimBound.Statement.{u}) : ConservationOfNumber.Statement.{u} := by
  intro O _ _ _ ϖ hϖ K _ _ ι _ P d hP a

  have hPprime : P.IsPrime := hP.multiProj.isPrime
  have hϖP : (C ϖ : MRing ι O) ∉ P := by
    intro h
    have hmem : ϖ ∈ P.comap (C : O →+* MRing ι O) := h
    rw [hP.noTorsion, Ideal.mem_bot] at hmem
    exact hϖ.ne_zero hmem
  have htors : ∀ x, C ϖ * x ∈ P → x ∈ P := fun x hx =>
    (hPprime.mem_or_mem hx).resolve_left hϖP
  have hhom : IsMultiHomogIdeal P := hP.multiProj.multiHomog

  have hhilb : hilbFn (genFib P) = hilbFn (specialIdeal P) := by
    funext m
    unfold hilbFn
    split_ifs
    · rw [h4 O K ι P hhom, h3 O ϖ hϖ K ι P hhom htors]
    · rfl
  have hg : gNum P a = intNum (IsLocalRing.ResidueField O) (specialIdeal P) a := by
    unfold gNum intNum
    rw [hhilb]
  rw [hg, h1 (IsLocalRing.ResidueField O) K ι d (specialIdeal P) (h5 O K ι P hhom)
    (h6 O ϖ hϖ K ι P d hP) a]
  exact h2 O ϖ hϖ K ι P (fun V => intNum (IsLocalRing.ResidueField O) V a)

end GroundTheory.Heights₂.Heights.NumbersDVR
end

