module

public import Formalism.SharpRestriction.GrowthBounds.CovariantDegrees
public import Formalism.GrowthSums.LemmaATwoFactList

@[expose] public section

-- bundled from Formalism.SharpRestriction.GrowthBounds.RootWeights.OperatorsKillInvariantProjection
section
noncomputable section

open Finset

namespace Formalism.MainNotions.G.GLWeightTheory

open Formalism.MainNotions.G Formalism.MainNotions.CovariantDegrees

section defs
variable {n : ℕ} {K : Type} [Field K] {V V' : Type} [AddCommGroup V] [Module K V] [AddCommGroup V'] [Module K V']

def IsSubrepresentation (E : GLOps n K V) (W : Submodule K V) : Prop := ∀ a b, ∀ x ∈ W, E a b x ∈ W

def IsEquivariantMap (E : GLOps n K V) (E' : GLOps n K V') (T : V →ₗ[K] V') : Prop := ∀ a b x, T (E a b x) = E' a b (T x)

def restrictRepresentation (E : GLOps n K V) (W : Submodule K V) (h : IsSubrepresentation E W) : GLOps n K W :=
  fun a b => (E a b).restrict (h a b)

def homRepresentation (E : GLOps n K V) (E' : GLOps n K V') : GLOps n K (V →ₗ[K] V') :=
  fun a b => LinearMap.llcomp K V V' V' (E' a b) - LinearMap.lcomp K V' (E a b)

def cyclicSubmodule (E : GLOps n K V) (v : V) : Submodule K V := Submodule.span K {x | ∃ u ∈ Umon E, x = u v}

end defs

def RestrictionIsRepresentation : Prop :=
  ∀ (n : ℕ) (K V : Type) [Field K] [CharZero K] [AddCommGroup V] [Module K V] [FiniteDimensional K V]
    (E : GLOps n K V), IsGLRep E → ∀ (W : Submodule K V) (h : IsSubrepresentation E W), IsGLRep (restrictRepresentation E W h)

def HomSpaceIsRepresentation : Prop :=
  ∀ (n : ℕ) (K V V' : Type) [Field K] [CharZero K] [AddCommGroup V] [Module K V] [FiniteDimensional K V]
    [AddCommGroup V'] [Module K V'] [FiniteDimensional K V'] (E : GLOps n K V) (E' : GLOps n K V'),
    IsGLRep E → IsGLRep E' → IsGLRep (homRepresentation E E')

def IsotypicSubmodulesSpanTop : Prop :=
  ∀ (n : ℕ) (K V : Type) [Field K] [CharZero K] [AddCommGroup V] [Module K V] [FiniteDimensional K V]
    (E : GLOps n K V), IsGLRep E → (⨆ mu, isoSub E mu) = ⊤

def InvariantProjectionExists : Prop :=
  ∀ (n : ℕ) (K V : Type) [Field K] [CharZero K] [AddCommGroup V] [Module K V] [FiniteDimensional K V]
    (E : GLOps n K V), IsGLRep E → ∃ P : Module.End K V, IsInvProj E P

def EquivariantCommutesInvariantProjection : Prop :=
  ∀ (n : ℕ) (K V V' : Type) [Field K] [CharZero K] [AddCommGroup V] [Module K V] [FiniteDimensional K V]
    [AddCommGroup V'] [Module K V'] [FiniteDimensional K V'] (E : GLOps n K V) (E' : GLOps n K V'),
    IsGLRep E → IsGLRep E' → ∀ T : V →ₗ[K] V', IsEquivariantMap E E' T →
    ∀ (P : Module.End K V) (P' : Module.End K V'), IsInvProj E P → IsInvProj E' P' → ∀ x, T (P x) = P' (T x)

def OperatorsKillInvariantProjection : Prop :=
  ∀ (n : ℕ) (K V : Type) [Field K] [CharZero K] [AddCommGroup V] [Module K V] [FiniteDimensional K V]
    (E : GLOps n K V), IsGLRep E → ∀ P : Module.End K V, IsInvProj E P → ∀ x a b, E a b (P x) = 0

def IsotypicProjectorTraceFormula : Prop :=
  ∀ (n : ℕ) (K W : Type) [Field K] [CharZero K] [AddCommGroup W] [Module K W] [FiniteDimensional K W]
    (E : GLOps n K W), IsGLRep E → ∀ (lam : Fin n → ℤ) (e : Module.End K W), IsIsoProj E lam e →
    ∀ v0, IsHWV E lam v0 → ∀ (hL : IsSubrepresentation E (cyclicSubmodule E v0))
      (P : Module.End K (cyclicSubmodule E v0 →ₗ[K] W)), IsInvProj (homRepresentation (restrictRepresentation E _ hL) E) P →
      ∀ (ι : Type) [Fintype ι] (b : Module.Basis ι K (cyclicSubmodule E v0)) (m : W),
        (Fintype.card ι : K) • ∑ i, P ((b.coord i).smulRight m) (b i) = e m

section lat
variable {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
  {W : Type} [AddCommGroup W] [Module (KK O) W] [Module O W] [IsScalarTower O (KK O) W]

def homLattice (M : Submodule O W) (L : Submodule (KK O) W) : Submodule O (L →ₗ[KK O] W) where
  carrier := {f | ∀ x : L, (x : W) ∈ M → f x ∈ M}
  zero_mem' := fun _ _ => by simp
  add_mem' := fun hf hg x hx => by simpa using M.add_mem (hf x hx) (hg x hx)
  smul_mem' := fun c f hf x hx => by simpa using M.smul_mem c (hf x hx)

end lat

def LatticeAdaptedBasisExists : Prop :=
  ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    (W : Type) [AddCommGroup W] [Module (KK O) W] [Module O W] [IsScalarTower O (KK O) W]
    [FiniteDimensional (KK O) W] (M : Submodule O W), M.FG → MQ (K := KK O) M = ⊤ →
    ∀ L : Submodule (KK O) W, ∃ (d : ℕ) (b : Module.Basis (Fin d) (KK O) L), (∀ i, ((b i : L) : W) ∈ M) ∧
      ∀ x : L, (x : W) ∈ M → ∀ i, ∃ o : O, b.coord i x = algebraMap O (KK O) o

def HomLatticeDividedPowerStable : Prop :=
  ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [CharZero (KK O)]
    (n : ℕ) (W : Type) [AddCommGroup W] [Module (KK O) W] [Module O W] [IsScalarTower O (KK O) W]
    [FiniteDimensional (KK O) W] (E : GLOps n (KK O) W), IsGLRep E →
    ∀ M : Submodule O W, UZLattice E M → MQ (K := KK O) M = ⊤ →
    ∀ (L : Submodule (KK O) W) (hL : IsSubrepresentation E L),
      UZLattice (homRepresentation (restrictRepresentation E L hL) E) (homLattice M L) ∧ MQ (K := KK O) (homLattice M L) = ⊤

end Formalism.MainNotions.G.GLWeightTheory
end
end

-- bundled from Formalism.SharpRestriction.GrowthBounds.RootWeights.PadicGeMulNat
section
noncomputable section

open Finset

namespace Formalism.MainNotions.G.GLWeightTheory

open Formalism.MainNotions.G Formalism.MainNotions.CovariantDegrees

def mah (f : ℕ → ℚ) (j : ℕ) : ℚ := (fwdDiff 1)^[j] f 0

def DecLe (p : ℕ) (θ s : ℝ) (K : ℕ) (f : ℕ → ℚ) : Prop := ∀ j ≤ K, PadicGe p (mah f j) (θ * j + s)

def Dec (p : ℕ) (θ s : ℝ) (f : ℕ → ℚ) : Prop := ∀ j, PadicGe p (mah f j) (θ * j + s)

def HdU (p : ℕ) : Prop := ∀ t rho : ℕ, rho < p ^ (t + 1) → ∃ a : ℕ → ℤ,
  (∀ n : ℕ, dUnit (p ^ (t + 1)) n rho = ∑ l ∈ range (rho + 1), (a l : ℚ) * (n.choose l : ℚ)) ∧
  ∀ l, (p : ℤ) ^ l ∣ a l

def HDec (p : ℕ) : Prop := ∀ u : UnitFn, u.rho < p ^ (u.t + 1) → Dec p (1 / 4) 0 (unitFn p u)

def HUnit (p : ℕ) : Prop := ∀ u : UnitFn, u.rho < p ^ (u.t + 1) → ∀ m : ℕ,
  unitFn p u m ≠ 0 ∧ padicValRat p (unitFn p u m) = 0

def HMul (p : ℕ) : Prop := ∀ (θ s s' : ℝ) (f g : ℕ → ℚ), 0 ≤ θ → Dec p θ s f → Dec p θ s' g →
  Dec p θ (s + s') (fun n => f n * g n)

theorem padicGe_add {p : ℕ} [Fact p.Prime] {x y : ℚ} {r : ℝ} (hx : PadicGe p x r) (hy : PadicGe p y r) :
    PadicGe p (x + y) r := by
  rcases hx with hx | hx
  · subst hx; simpa using hy
  rcases hy with hy | hy
  · subst hy; rw [add_zero]; exact Or.inr hx
  by_cases hxy : x + y = 0
  · exact Or.inl hxy
  right
  have hm := padicValRat.min_le_padicValRat_add (p := p) hxy
  have hm' : ((min (padicValRat p x) (padicValRat p y) : ℤ) : ℝ) ≤ (padicValRat p (x + y) : ℝ) := by
    exact_mod_cast hm
  rw [Int.cast_min] at hm'
  exact le_trans (le_min hx hy) hm'

theorem padicGe_mul {p : ℕ} [Fact p.Prime] {x y : ℚ} {r s : ℝ} (hx : PadicGe p x r) (hy : PadicGe p y s) :
    PadicGe p (x * y) (r + s) := by
  rcases hx with hx | hx
  · left; simp [hx]
  rcases hy with hy | hy
  · left; simp [hy]
  by_cases h0 : x * y = 0
  · exact Or.inl h0
  right
  have hx0 : x ≠ 0 := left_ne_zero_of_mul h0
  have hy0 : y ≠ 0 := right_ne_zero_of_mul h0
  rw [padicValRat.mul hx0 hy0]
  push_cast
  linarith

theorem padicGe_mono {p : ℕ} {x : ℚ} {r s : ℝ} (hx : PadicGe p x r) (h : s ≤ r) : PadicGe p x s := by
  rcases hx with hx | hx
  · exact Or.inl hx
  · exact Or.inr (le_trans h hx)

theorem padicGe_neg {p : ℕ} {x : ℚ} {r : ℝ} (hx : PadicGe p x r) : PadicGe p (-x) r := by
  rcases hx with hx | hx
  · left; simp [hx]
  · right; rw [padicValRat.neg]; exact hx

theorem padicGe_int {p : ℕ} [Fact p.Prime] (k : ℤ) : PadicGe p (k : ℚ) 0 := by
  by_cases hk : (k : ℚ) = 0
  · exact Or.inl hk
  right
  rw [padicValRat.of_int]
  exact_mod_cast (Nat.cast_nonneg _ : (0 : ℤ) ≤ (padicValInt p k : ℤ))

theorem padicGe_mul_nat {p : ℕ} [Fact p.Prime] {x : ℚ} {r : ℝ} (hx : PadicGe p x r) (k : ℕ) :
    PadicGe p (x * (k : ℚ)) r := by
  have h := padicGe_mul hx (padicGe_int (p := p) (k : ℤ))
  simpa using h

theorem padicGe_sum {p : ℕ} [Fact p.Prime] {ι : Type*} (s : Finset ι) (f : ι → ℚ) {r : ℝ}
    (h : ∀ i ∈ s, PadicGe p (f i) r) : PadicGe p (∑ i ∈ s, f i) r := by
  classical
  induction s using Finset.induction_on with
  | empty => exact Or.inl (by simp)
  | insert a s ha ih =>
    rw [Finset.sum_insert ha]
    exact padicGe_add (h a (Finset.mem_insert_self a s))
      (ih (fun i hi => h i (Finset.mem_insert_of_mem hi)))

end Formalism.MainNotions.G.GLWeightTheory
end
end

-- bundled from Formalism.SharpRestriction.GrowthBounds.RootWeights.PieAltApply
section
noncomputable section

open MvPolynomial Finset

namespace Formalism.MainNotions.G.GLWeightTheory

open Formalism.MainNotions.G Formalism.MainNotions.CovariantDegrees

def pie_cnt {n b : ℕ} (s : Sym (Fin n) b) : Fin n → ℕ := fun i => (s : Multiset (Fin n)).count i

theorem pie_hsymm (n b : ℕ) : hsymm (Fin n) ℤ b =
    ∑ s : Sym (Fin n) b, ∏ i, (X i : MvPolynomial (Fin n) ℤ) ^ pie_cnt s i := by
  rw [MvPolynomial.hsymm]
  apply Finset.sum_congr rfl
  intro s _
  rw [Finset.prod_multiset_map_count]
  simp only [pie_cnt]
  apply Finset.prod_subset (Finset.subset_univ _)
  intro i _ hi
  rw [Multiset.mem_toFinset] at hi
  rw [Multiset.count_eq_zero.mpr hi, pow_zero]

theorem pie_alt_apply (n : ℕ) (al : Fin n → ℕ) : alt n al =
    ∑ σ : Equiv.Perm (Fin n), Equiv.Perm.sign σ • ∏ i, (X (σ i) : MvPolynomial (Fin n) ℤ) ^ al i := by
  unfold alt
  rw [Matrix.det_apply]
  rfl

private theorem pie_cnt_map_equiv {n b : ℕ} (e : Fin n ≃ Fin n) (s : Sym (Fin n) b) (i : Fin n) :
    pie_cnt (s.map e) i = pie_cnt s (e.symm i) := by
  unfold pie_cnt
  rw [Sym.coe_map]
  conv_lhs => rw [← e.apply_symm_apply i]
  exact Multiset.count_map_eq_count' e _ e.injective _

theorem pie_step1 (n b : ℕ) (al : Fin n → ℕ) : alt n al * hsymm (Fin n) ℤ b =
    ∑ s : Sym (Fin n) b, alt n (al + pie_cnt s) := by
  rw [pie_alt_apply, pie_hsymm, Finset.sum_mul]
  simp_rw [pie_alt_apply]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro σ _
  rw [smul_mul_assoc, Finset.mul_sum, ← Finset.smul_sum]
  congr 1
  refine Finset.sum_nbij' (fun s => s.map σ.symm) (fun s => s.map σ) (by simp) (by simp) ?_ ?_ ?_
  · intro s _
    first
    | simp [Sym.map_map]
    | (apply Sym.ext; simp [Sym.coe_map, Multiset.map_map])
  · intro s _
    first
    | simp [Sym.map_map]
    | (apply Sym.ext; simp [Sym.coe_map, Multiset.map_map])
  · intro s _
    rw [← Equiv.prod_comp σ (fun i => (X i : MvPolynomial (Fin n) ℤ) ^ pie_cnt s i),
      ← Finset.prod_mul_distrib]
    apply Finset.prod_congr rfl
    intro i _
    rw [Pi.add_apply, pow_add, pie_cnt_map_equiv, Equiv.symm_symm]

end Formalism.MainNotions.G.GLWeightTheory
end
end

-- bundled from Formalism.SharpRestriction.GrowthBounds.RootWeights.StableSubspaceCompleteReducibility
section
noncomputable section

open MvPolynomial Finset

namespace Formalism.MainNotions.G.GLWeightTheory

open Formalism.MainNotions.G Formalism.MainNotions.CovariantDegrees

def SatisfiesGLRelations {n : ℕ} {K V : Type*} [Field K] [AddCommGroup V] [Module K V] (E : GLOps n K V) : Prop :=
  ∀ a b c d, E a b * E c d - E c d * E a b = (if b = c then E a d else 0) - (if d = a then E c b else 0)

def IsStableUnderOperators {n : ℕ} {K V : Type*} [Field K] [AddCommGroup V] [Module K V] (E : GLOps n K V)
    (W : Submodule K V) : Prop := ∀ a b, ∀ x ∈ W, E a b x ∈ W

def isotypicPartIn {n : ℕ} {K V : Type*} [Field K] [AddCommGroup V] [Module K V] (E : GLOps n K V)
    (W : Submodule K V) (mu : Fin n → ℤ) : Submodule K V :=
  Submodule.span K {x | ∃ u ∈ Umon E, ∃ v ∈ W, IsHWV E mu v ∧ x = u v}

def StableSubspaceCompleteReducibility : Prop :=
  ∀ (K V : Type) [Field K] [CharZero K] [AddCommGroup V] [Module K V] (n : ℕ) (E : GLOps n K V), SatisfiesGLRelations E →
    ∀ W : Submodule K V, FiniteDimensional K W → IsStableUnderOperators E W → W ≤ ⨆ mu, weightSp E mu →
      W ≤ ⨆ mu, isotypicPartIn E W mu

def HighestWeightModuleWeightBounds : Prop :=
  ∀ (K V : Type) [Field K] [CharZero K] [AddCommGroup V] [Module K V] (n : ℕ) [NeZero n] (E : GLOps n K V),
    SatisfiesGLRelations E → ∀ (mu : Fin n → ℤ) (v : V), IsHWV E mu v → ∀ u ∈ Umon E,
      u v ∈ ⨆ ν ∈ {ν : Fin n → ℤ | mu (lastIdx n) ≤ ν (lastIdx n) ∧ ν 0 ≤ mu 0}, weightSp E ν

def PolynomialOperatorsGLRelations : Prop :=
  ∀ (R : Type) [Field R] (ι : Type) [Fintype ι] (LL : Letters ι) (n : ℕ) (S : Set ι), SatisfiesGLRelations (glOps R n LL S)

def MonomialsAreWeightVectors : Prop :=
  ∀ (R : Type) [Field R] [CharZero R] (ι : Type) [Fintype ι] (LL : Letters ι) (n : ℕ) (S : Set ι),
    (∀ (m : ι × Fin n →₀ ℕ) (c : R), monomial m c ∈ weightSp (glOps R n LL S) (wtS LL S m)) ∧
    (∀ (ν : Fin n → ℤ) (x : MvPolynomial (ι × Fin n) R), x ∈ weightSp (glOps R n LL S) ν →
      ∀ m ∈ x.support, wtS LL S m = ν)

def PolynomialLocallyFinite : Prop :=
  ∀ (R : Type) [Field R] (ι : Type) [Fintype ι] (LL : Letters ι) (n : ℕ) (S : Set ι)
    (x : MvPolynomial (ι × Fin n) R), ∃ T : Submodule R (MvPolynomial (ι × Fin n) R),
      FiniteDimensional R T ∧ x ∈ T ∧ IsStableUnderOperators (glOps R n LL S) T

def DividedPowerFormulaCharZero : Prop :=
  ∀ (R : Type) [Field R] [CharZero R] (ι : Type) [Fintype ι] (LL : Letters ι) (n : ℕ) (S : Set ι)
    (a b : Fin n) (k : ℕ), a ≠ b → divPowE (glOps R n LL S) a b k = divPow R LL S a b k

def BinomialFormulaCharZero : Prop :=
  ∀ (R : Type) [Field R] [CharZero R] (ι : Type) [Fintype ι] (LL : Letters ι) (n : ℕ) (S : Set ι)
    (a : Fin n) (k : ℕ), binomE (glOps R n LL S) a k = binomPol R LL S a k

end Formalism.MainNotions.G.GLWeightTheory
end
end

