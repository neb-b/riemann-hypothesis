module

public import Mathlib
public import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.IsGraphGenTwistBundleZero
public import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.Bundle0033
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.MultihomogeneousIdeals.Bundle0001

@[expose] public section

-- bundled from GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.ImportsTailRest
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization

open MvPolynomial
open ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.KH (secOver mIdealOver)

def SegreRealise.Statement : Prop :=
  ∀ (F : Type) [Field F] (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type)
    [∀ a, Fintype (ι a)] (Ω : Type) [Field Ω] [Algebra F Ω] (y : (Σ a, ι a) → Ω) (d : ℕ)
    (μs : Fin d → K → ℤ),
    (∀ a, ∃ i, y ⟨a, i⟩ ≠ 0) → FieldNumbers.relDim (mIdealOver F y) = ((d : ℕ) : WithBot (WithTop ℤ)) →
    ∃ (N : ℕ) (eqv : (∀ a, ι a) ≃ Fin (N + 1)) (x : Fin (N + 1) → Ω)
      (Ms : Fin d → Kleiman.LineBundle F x),
      (∀ i, x (eqv i) = ∏ a, y ⟨a, i a⟩) ∧
      Kleiman.IsSubvar x (Kleiman.primeOf (S := F) x) d ∧
      (∀ j (c : ℤ), ((Ms j).twist (Kleiman.twistSys F x c)).secs =
        secOver F y (μs j + fun _ => c)) ∧
      (∀ j, Kleiman.Nef (Ms j).toSubSystem ↔ IndefiniteRowSideFullHecke.Kleiman2.IsNef F y (μs j)) ∧
      Kleiman.interNum (Kleiman.primeOf (S := F) x) (fun j => (Ms j).toSubSystem) =
        NumbersDVR.intNum F (mIdealOver F y) μs

end GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.ImportsTerAlt
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization

open MvPolynomial
open ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.KH (chartRingOver secOver mIdealOver)

def BundleOfDeg.Statement : Prop :=
  ∀ (S : Type) [CommRing S] (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)]
    (Ω : Type) [Field Ω] [Algebra S Ω] (y : (Σ k, ι k) → Ω) (k₀ : K) (N : ℕ) (e : ι k₀ ≃ Fin (N + 1)),
    IndefiniteRowSideFullHecke.Kleiman2.IsModelWithBase S y k₀ → ∀ β : K → ℤ,
      ∃ Q : Kleiman.LineBundle S (IndefiniteRowSideFullHecke.Kleiman2.blockVec y k₀ ∘ e.symm), ∀ c : ℤ,
        (Q.twist (Kleiman.twistSys S (IndefiniteRowSideFullHecke.Kleiman2.blockVec y k₀ ∘ e.symm) c)).secs =
          secOver S y (β + c • IndefiniteRowSideFullHecke.Kleiman2.baseDeg k₀)

end GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.IsMultiProjPrimeMIdealOverGraph
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization

open MvPolynomial
open ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.KH (mConeMapOver mIdealOver)

noncomputable section

section Homog

variable {K : Type} [Fintype K] [DecidableEq K] {ι : K → Type} [∀ k, Fintype (ι k)]
  {S : Type} [CommRing S] {Ω : Type} [Field Ω] [Algebra S Ω]

theorem sum_block_eq_blockWeight (e : (Σ k, ι k) →₀ ℕ) (k : K) :
    ∑ i, e ⟨k, i⟩ = Finsupp.weight (NumbersDVR.blockWeight ι) e k := by
  rw [Finsupp.weight_apply, Finsupp.sum_fintype _ _ (by simp), Finset.sum_apply, Fintype.sum_sigma]
  simp [NumbersDVR.blockWeight, Pi.single_apply]


omit [DecidableEq K] in
theorem mConeMapOver_eq_of_block (y : (Σ k, ι k) → Ω) {f : MvPolynomial (Σ k, ι k) S} {d : K → ℕ}
    (hf : ∀ e ∈ f.support, ∀ k, ∑ i, e ⟨k, i⟩ = d k) :
    mConeMapOver S y f = MvPolynomial.C (aeval y f) * ∏ k, MvPolynomial.X k ^ d k := by
  classical
  conv_lhs => rw [f.as_sum]
  conv_rhs => rw [f.as_sum]
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sum, map_sum, map_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun e he => ?_
  have hX : ∏ p : (Σ k, ι k), (MvPolynomial.X p.1 : MvPolynomial K Ω) ^ e p =
      ∏ k, MvPolynomial.X k ^ d k := by
    rw [Fintype.prod_sigma]
    refine Finset.prod_congr rfl fun k _ => ?_
    show ∏ i, (MvPolynomial.X k : MvPolynomial K Ω) ^ e ⟨k, i⟩ = _
    rw [Finset.prod_pow_eq_pow_sum, hf e he k]
  simp only [mConeMapOver, aeval_monomial]
  rw [Finsupp.prod_fintype _ _ (fun i => by simp), Finsupp.prod_fintype _ _ (fun i => by simp)]
  simp only [mul_pow, Finset.prod_mul_distrib, hX, map_mul, map_prod, map_pow,
    MvPolynomial.algebraMap_apply]
  ring

theorem coeff_mConeMapOver (y : (Σ k, ι k) → Ω) (b : K → ℕ) (f : MvPolynomial (Σ k, ι k) S) :
    AddMonoidAlgebra.coeff (mConeMapOver S y f) (Finsupp.equivFunOnFinite.symm b) =
      aeval y (weightedHomogeneousComponent (NumbersDVR.blockWeight ι) b f) := by
  classical
  induction f using MvPolynomial.induction_on' with
  | monomial e c =>
    have hm := isWeightedHomogeneous_monomial (NumbersDVR.blockWeight ι) e c
      (rfl : Finsupp.weight (NumbersDVR.blockWeight ι) e = _)
    have hb : ∀ e' ∈ (monomial e c : MvPolynomial (Σ k, ι k) S).support, ∀ k,
        ∑ i, e' ⟨k, i⟩ = Finsupp.weight (NumbersDVR.blockWeight ι) e k := by
      intro e' he' k
      rw [sum_block_eq_blockWeight, hm (mem_support_iff.mp he')]
    rw [mConeMapOver_eq_of_block y hb,
      weightedHomogeneousComponent_of_mem ((mem_weightedHomogeneousSubmodule _ _ _ _).mpr hm)]
    have hX : (∏ k, (X k : MvPolynomial K Ω) ^ Finsupp.weight (NumbersDVR.blockWeight ι) e k) =
        monomial (Finsupp.equivFunOnFinite.symm (Finsupp.weight (NumbersDVR.blockWeight ι) e)) 1 := by
      rw [monomial_eq, C_1, one_mul, Finsupp.prod_fintype _ _ (by simp)]
      simp
    rw [hX, coeff_C_mul, coeff_monomial]
    by_cases h : b = Finsupp.weight (NumbersDVR.blockWeight ι) e
    · subst h; simp
    · rw [ite_eq_right h, ite_eq_right (fun h' => h (Finsupp.equivFunOnFinite.symm.injective h').symm)]
      simp
  | add p q hp hq => simp only [map_add, AddMonoidAlgebra.coeff_add, Finsupp.add_apply, hp, hq]

theorem isMultiHomogIdeal_mIdealOver (y : (Σ k, ι k) → Ω) :
    NumbersDVR.IsMultiHomogIdeal (R := S) (mIdealOver S y) := by
  intro f hf b
  have hf' : mConeMapOver S y f = 0 := RingHom.mem_ker.mp hf
  refine RingHom.mem_ker.mpr ?_
  have hb : ∀ e' ∈ (weightedHomogeneousComponent (NumbersDVR.blockWeight ι) b f).support, ∀ k,
      ∑ i, e' ⟨k, i⟩ = b k := by
    intro e' he' k
    rw [sum_block_eq_blockWeight,
      weightedHomogeneousComponent_isWeightedHomogeneous b f (mem_support_iff.mp he')]
  rw [mConeMapOver_eq_of_block y hb, ← coeff_mConeMapOver, hf']
  simp

theorem isMultiProjPrime_mIdealOver (y : (Σ k, ι k) → Ω) (hy : ∀ k, ∃ i, y ⟨k, i⟩ ≠ 0) :
    NumbersDVR.IsMultiProjPrime (R := S) (mIdealOver S y) := by
  refine ⟨RingHom.ker_isPrime (mConeMapOver S y), isMultiHomogIdeal_mIdealOver y, ?_⟩
  intro k
  obtain ⟨i, hi⟩ := hy k
  refine ⟨i, fun h => ?_⟩
  have h' : mConeMapOver S y (X ⟨k, i⟩) = 0 := RingHom.mem_ker.mp h
  simp only [mConeMapOver, aeval_X] at h'
  exact mul_ne_zero (by rwa [Ne, MvPolynomial.C_eq_zero]) (X_ne_zero _) h'

end Homog

section Graph

variable {S : Type} [CommRing S] {Ω : Type} [Field Ω] [Algebra S Ω] {N m : ℕ}

theorem mConeMapOver_graph_comp_base (x : Fin (N + 1) → Ω) (s : Fin m → Ω) :
    (mConeMapOver S (graphVec x s)).comp
        (rename fun a : Fin (N + 1) => (⟨baseBlock, a⟩ : Σ b, graphIdx N m b)) =
      ((Polynomial.aeval (X baseBlock : MvPolynomial (Unit ⊕ Unit) Ω)).restrictScalars S).comp
        (Kleiman.cone (S := S) x) := by
  apply MvPolynomial.algHom_ext
  intro a
  simp [mConeMapOver, Kleiman.cone, ReciprocityTheory.ChartRestriction.G.Geo.coneMap]
  rfl

theorem cone_eq_graph_comp (x : Fin (N + 1) → Ω) (s : Fin m → Ω) :
    Kleiman.cone (S := S) x =
      ((aeval fun _ : Unit ⊕ Unit => (Polynomial.X : Polynomial Ω)).restrictScalars S).comp
        ((mConeMapOver S (graphVec x s)).comp
          (rename fun a : Fin (N + 1) => (⟨baseBlock, a⟩ : Σ b, graphIdx N m b))) := by
  apply MvPolynomial.algHom_ext
  intro a
  simp [mConeMapOver, Kleiman.cone, ReciprocityTheory.ChartRestriction.G.Geo.coneMap]
  rfl

theorem comap_mIdealOver_graph (x : Fin (N + 1) → Ω) (s : Fin m → Ω) :
    (mIdealOver S (graphVec x s)).comap
        (rename fun a : Fin (N + 1) => (⟨baseBlock, a⟩ : Σ b, graphIdx N m b)) =
      Kleiman.primeOf (S := S) x := by
  ext f
  rw [Ideal.mem_comap, Kleiman.primeOf_eq, RingHom.mem_ker]
  change mConeMapOver S (graphVec x s) (rename _ f) = 0 ↔ _
  constructor
  · intro h
    rw [cone_eq_graph_comp x s, AlgHom.comp_apply, AlgHom.comp_apply, h, map_zero]
  · intro h
    rw [← AlgHom.comp_apply, mConeMapOver_graph_comp_base, AlgHom.comp_apply, h, map_zero]

theorem isMultiProjPrime_mIdealOver_graph (x : Fin (N + 1) → Ω) (s : Fin m → Ω) (hx : ∃ i, x i ≠ 0)
    (hs : ∃ j, s j ≠ 0) : NumbersDVR.IsMultiProjPrime (R := S) (mIdealOver S (graphVec x s)) :=
  isMultiProjPrime_mIdealOver _ (by rintro (⟨⟩ | ⟨⟩); exacts [hx, hs])

end Graph

end

end GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.MConeMapOverOfIsMultiHomog
section
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization

open MvPolynomial
open ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.KH (mIdealOver mConeMapOver chartRingOver)
open ReciprocityTheory.ChartRestriction.G.Geo (MRingOver IsMultiHomog)
open ReciprocityTheory.ChartRestriction.G.AI.I1 (isMultiHomog_mul isMultiHomog_add isMultiHomog_X isMultiHomog_one)

namespace ResidueMap

variable {F : Type} [Field F] {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]


omit [Fintype K] in
theorem isMultiHomog_sub {f g : MRingOver F ι} {a : K → ℕ} (hf : IsMultiHomog f a) (hg : IsMultiHomog g a) :
    IsMultiHomog (f - g) a := by
  classical
  intro m hm k
  rcases Finset.mem_union.mp (MvPolynomial.support_sub _ f g hm) with h | h
  exacts [hf m h k, hg m h k]


omit [Fintype K] in
theorem isMultiHomog_C (r : F) : IsMultiHomog (C r : MRingOver F ι) 0 := by
  classical
  intro m hm k
  have hm0 : m = 0 := Finset.mem_singleton.mp (MvPolynomial.support_monomial_subset hm)
  subst hm0
  simp


omit [Fintype K] in
theorem isMultiHomog_rename [DecidableEq K] (k : K) {f : MvPolynomial (ι k) F} {m : ℕ} (hf : f.IsHomogeneous m) :
    IsMultiHomog (rename (fun i : ι k => (⟨k, i⟩ : Σ k, ι k)) f) (Pi.single k m) := by
  classical
  intro e he k'
  rw [support_rename_of_injective sigma_mk_injective] at he
  obtain ⟨d, hd, rfl⟩ := Finset.mem_image.mp he
  have hdeg : ∑ i, d i = m := by
    have h1 := hf (mem_support_iff.mp hd)
    rw [Finsupp.weight_apply, Finsupp.sum_fintype _ _ (by simp)] at h1
    simpa using h1
  by_cases hk : k' = k
  · subst hk
    rw [Pi.single_eq_same, ← hdeg]
    exact Finset.sum_congr rfl fun i _ => Finsupp.mapDomain_apply_of_injective sigma_mk_injective d i
  · rw [Pi.single_eq_of_ne hk]
    refine Finset.sum_eq_zero fun i _ => ?_
    exact Finsupp.mapDomain_of_notMem_range _ _
      (by rintro ⟨j, hj⟩; exact hk (congrArg Sigma.fst hj).symm)


omit [Fintype K] [∀ k, Fintype (ι k)] in
theorem aeval_rename_block {A : Type} [CommRing A] [Algebra F A] (z : (Σ k, ι k) → A) (k : K)
    (p : MvPolynomial (ι k) F) :
    aeval z (rename (fun i : ι k => (⟨k, i⟩ : Σ k, ι k)) p) = aeval (IndefiniteRowSideFullHecke.Kleiman2.blockVec z k) p := by
  rw [aeval_rename]; rfl

variable {Ω : Type} [Field Ω] [Algebra F Ω]

theorem mConeMapOver_of_isMultiHomog (y : (Σ k, ι k) → Ω) {g : MRingOver F ι} {d : K → ℕ}
    (hg : IsMultiHomog g d) :
    mConeMapOver F y g = MvPolynomial.C (aeval y g) * ∏ k, (MvPolynomial.X k : MvPolynomial K Ω) ^ d k := by
  classical
  conv_lhs => rw [g.as_sum]
  conv_rhs => rw [g.as_sum]
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sum, map_sum, map_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun m hm => ?_
  have hX : ∏ p : (Σ k, ι k), (MvPolynomial.X p.1 : MvPolynomial K Ω) ^ m p = ∏ k, MvPolynomial.X k ^ d k := by
    rw [Fintype.prod_sigma]
    refine Finset.prod_congr rfl fun k _ => ?_
    show ∏ i, (MvPolynomial.X k : MvPolynomial K Ω) ^ m ⟨k, i⟩ = _
    rw [Finset.prod_pow_eq_pow_sum, hg m hm k]
  simp only [mConeMapOver, aeval_monomial]
  rw [Finsupp.prod_fintype _ _ (fun i => by simp), Finsupp.prod_fintype _ _ (fun i => by simp)]
  simp only [mul_pow, Finset.prod_mul_distrib, hX, map_mul, map_prod, map_pow,
    MvPolynomial.algebraMap_apply]
  ring

theorem mem_mIdealOver_iff (y : (Σ k, ι k) → Ω) {g : MRingOver F ι} {d : K → ℕ} (hg : IsMultiHomog g d) :
    g ∈ mIdealOver F y ↔ aeval y g = 0 := by
  rw [mIdealOver, RingHom.mem_ker, mConeMapOver_of_isMultiHomog y hg]
  have hP : (∏ k, (MvPolynomial.X k : MvPolynomial K Ω) ^ d k) ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr fun k _ => pow_ne_zero _ (MvPolynomial.X_ne_zero k)
  rw [mul_eq_zero, or_iff_left hP, MvPolynomial.C_eq_zero]

variable {K' : Type} [Field K'] [Algebra F K']

theorem vanish {y : (Σ k, ι k) → Ω} {y' : (Σ k, ι k) → K'} (hle : mIdealOver F y ≤ mIdealOver F y')
    {g : MRingOver F ι} {d : K → ℕ} (hg : IsMultiHomog g d) (h : aeval y g = 0) : aeval y' g = 0 :=
  (mem_mIdealOver_iff y' hg).mp (hle ((mem_mIdealOver_iff y hg).mpr h))

theorem ne_zero_of {y : (Σ k, ι k) → Ω} {y' : (Σ k, ι k) → K'} (hle : mIdealOver F y ≤ mIdealOver F y')
    {g : MRingOver F ι} {d : K → ℕ} (hg : IsMultiHomog g d) (hg' : aeval y' g ≠ 0) : aeval y g ≠ 0 :=
  fun h => hg' (vanish hle hg h)

theorem wd {y : (Σ k, ι k) → Ω} {y' : (Σ k, ι k) → K'} (hle : mIdealOver F y ≤ mIdealOver F y')
    {f g f₂ g₂ : MRingOver F ι} {n n₂ : K → ℕ} (hf : IsMultiHomog f n) (hg : IsMultiHomog g n)
    (hf₂ : IsMultiHomog f₂ n₂) (hg₂ : IsMultiHomog g₂ n₂) (hg' : aeval y' g ≠ 0) (hg₂' : aeval y' g₂ ≠ 0)
    (h : aeval y f / aeval y g = aeval y f₂ / aeval y g₂) :
    aeval y' f / aeval y' g = aeval y' f₂ / aeval y' g₂ := by
  rw [div_eq_div_iff (ne_zero_of hle hg hg') (ne_zero_of hle hg₂ hg₂')] at h
  rw [div_eq_div_iff hg' hg₂']
  have h2 : IsMultiHomog (f₂ * g) (n + n₂) := by
    rw [add_comm]; exact isMultiHomog_mul hf₂ hg
  have hp := isMultiHomog_sub (isMultiHomog_mul hf hg₂) h2
  have h0 := vanish hle hp (by rw [map_sub, map_mul, map_mul, h, sub_self])
  rw [map_sub, map_mul, map_mul, sub_eq_zero] at h0
  exact h0


variable (F) in
def fracSet (y : (Σ k, ι k) → Ω) (y' : (Σ k, ι k) → K') : Set Ω :=
  {x | ∃ (f g : MRingOver F ι) (n : K → ℕ), IsMultiHomog f n ∧ IsMultiHomog g n ∧ aeval y' g ≠ 0 ∧
    x = aeval y f / aeval y g}

def locR {y : (Σ k, ι k) → Ω} {y' : (Σ k, ι k) → K'} (hle : mIdealOver F y ≤ mIdealOver F y') :
    Subalgebra F Ω where
  carrier := fracSet F y y'
  mul_mem' := by
    rintro _ _ ⟨f, g, n, hf, hg, hg', rfl⟩ ⟨f₂, g₂, n₂, hf₂, hg₂, hg₂', rfl⟩
    exact ⟨f * f₂, g * g₂, n + n₂, isMultiHomog_mul hf hf₂, isMultiHomog_mul hg hg₂,
      by rw [map_mul]; exact mul_ne_zero hg' hg₂', by rw [map_mul, map_mul, div_mul_div_comm]⟩
  add_mem' := by
    rintro _ _ ⟨f, g, n, hf, hg, hg', rfl⟩ ⟨f₂, g₂, n₂, hf₂, hg₂, hg₂', rfl⟩
    have h2 : IsMultiHomog (f₂ * g) (n + n₂) := by
      rw [add_comm]; exact isMultiHomog_mul hf₂ hg
    refine ⟨f * g₂ + f₂ * g, g * g₂, n + n₂, isMultiHomog_add (isMultiHomog_mul hf hg₂) h2,
      isMultiHomog_mul hg hg₂, by rw [map_mul]; exact mul_ne_zero hg' hg₂', ?_⟩
    rw [div_add_div _ _ (ne_zero_of hle hg hg') (ne_zero_of hle hg₂ hg₂'), map_add (f := _), map_mul, map_mul, map_mul]
    ring
  algebraMap_mem' r := ⟨C r, 1, 0, isMultiHomog_C r, isMultiHomog_one, by simp, by simp⟩

theorem exists_of_mem {y : (Σ k, ι k) → Ω} {y' : (Σ k, ι k) → K'} {hle : mIdealOver F y ≤ mIdealOver F y'}
    {x : Ω} (hx : x ∈ locR hle) :
    ∃ (f g : MRingOver F ι) (n : K → ℕ), IsMultiHomog f n ∧ IsMultiHomog g n ∧ aeval y' g ≠ 0 ∧
      x = aeval y f / aeval y g := hx

def sigmaFun {y : (Σ k, ι k) → Ω} {y' : (Σ k, ι k) → K'} (hle : mIdealOver F y ≤ mIdealOver F y')
    (x : locR hle) : K' :=
  aeval y' (exists_of_mem x.2).choose / aeval y' (exists_of_mem x.2).choose_spec.choose

theorem sigmaFun_eq {y : (Σ k, ι k) → Ω} {y' : (Σ k, ι k) → K'} (hle : mIdealOver F y ≤ mIdealOver F y')
    (x : locR hle) {f g : MRingOver F ι} {n : K → ℕ} (hf : IsMultiHomog f n) (hg : IsMultiHomog g n)
    (hg' : aeval y' g ≠ 0) (hx : (x : Ω) = aeval y f / aeval y g) :
    sigmaFun hle x = aeval y' f / aeval y' g := by
  obtain ⟨hf0, hg0, hg0', hx0⟩ := (exists_of_mem x.2).choose_spec.choose_spec.choose_spec
  exact wd hle hf0 hg0 hf hg hg0' hg' (hx0.symm.trans hx)

def sigma {y : (Σ k, ι k) → Ω} {y' : (Σ k, ι k) → K'} (hle : mIdealOver F y ≤ mIdealOver F y') :
    locR hle →ₐ[F] K' where
  toFun := sigmaFun hle
  map_one' := by
    rw [sigmaFun_eq hle 1 isMultiHomog_one isMultiHomog_one (by simp) (by simp)]; simp
  map_zero' := by
    rw [sigmaFun_eq hle 0 (isMultiHomog_C (0 : F)) isMultiHomog_one (by simp) (by simp)]; simp
  map_mul' x x' := by
    obtain ⟨f, g, n, hf, hg, hg', hx⟩ := exists_of_mem x.2
    obtain ⟨f₂, g₂, n₂, hf₂, hg₂, hg₂', hx₂⟩ := exists_of_mem x'.2
    rw [sigmaFun_eq hle x hf hg hg' hx, sigmaFun_eq hle x' hf₂ hg₂ hg₂' hx₂,
      sigmaFun_eq hle (x * x') (isMultiHomog_mul hf hf₂) (isMultiHomog_mul hg hg₂)
        (by rw [map_mul]; exact mul_ne_zero hg' hg₂')
        (by rw [Subalgebra.coe_mul, hx, hx₂, map_mul, map_mul, div_mul_div_comm]),
      map_mul, map_mul, div_mul_div_comm]
  map_add' x x' := by
    obtain ⟨f, g, n, hf, hg, hg', hx⟩ := exists_of_mem x.2
    obtain ⟨f₂, g₂, n₂, hf₂, hg₂, hg₂', hx₂⟩ := exists_of_mem x'.2
    have h2 : IsMultiHomog (f₂ * g) (n + n₂) := by
      rw [add_comm]; exact isMultiHomog_mul hf₂ hg
    rw [sigmaFun_eq hle x hf hg hg' hx, sigmaFun_eq hle x' hf₂ hg₂ hg₂' hx₂,
      sigmaFun_eq hle (x + x') (isMultiHomog_add (isMultiHomog_mul hf hg₂) h2) (isMultiHomog_mul hg hg₂)
        (by rw [map_mul]; exact mul_ne_zero hg' hg₂')
        (by rw [Subalgebra.coe_add, hx, hx₂, div_add_div _ _ (ne_zero_of hle hg hg') (ne_zero_of hle hg₂ hg₂'),
              map_add, map_mul, map_mul, map_mul]; ring),
      div_add_div _ _ hg' hg₂', map_add, map_mul, map_mul, map_mul]
    ring
  commutes' r := by
    show sigmaFun hle (algebraMap F (locR hle) r) = _
    rw [sigmaFun_eq hle _ (isMultiHomog_C r) isMultiHomog_one (by simp) (by simp)]; simp

theorem sigma_apply {y : (Σ k, ι k) → Ω} {y' : (Σ k, ι k) → K'} (hle : mIdealOver F y ≤ mIdealOver F y')
    (x : locR hle) : sigma hle x = sigmaFun hle x := rfl

theorem frac_spec {y : (Σ k, ι k) → Ω} {y' : (Σ k, ι k) → K'} (hle : mIdealOver F y ≤ mIdealOver F y')
    {f g : MRingOver F ι} {n : K → ℕ} (hf : IsMultiHomog f n) (hg : IsMultiHomog g n)
    (hg' : aeval y' g ≠ 0) (x : Ω) (hx : x = aeval y f / aeval y g) :
    ∃ h : x ∈ locR hle, sigma hle ⟨x, h⟩ = aeval y' f / aeval y' g :=
  ⟨⟨f, g, n, hf, hg, hg', hx⟩, (sigma_apply hle _).trans (sigmaFun_eq hle _ hf hg hg' hx)⟩

end ResidueMap


open ResidueMap in
theorem ResidueMap.proof : ResidueMap.Statement := by
  intro F _ K _ ι _ Ω _ _ y K' _ _ y' hle
  classical
  refine ⟨locR hle, sigma hle, ?_, ?_, ?_⟩
  · intro f g n hf hg hg'
    exact frac_spec hle hf hg hg' _ rfl
  · intro k f g m hf hg hg'
    have hg'' : aeval y' (rename (fun i : ι k => (⟨k, i⟩ : Σ k, ι k)) g) ≠ 0 := by
      rwa [aeval_rename_block]
    obtain ⟨h, hσ⟩ := frac_spec hle (isMultiHomog_rename k hf) (isMultiHomog_rename k hg) hg''
      (aeval (IndefiniteRowSideFullHecke.Kleiman2.blockVec y k) f / aeval (IndefiniteRowSideFullHecke.Kleiman2.blockVec y k) g)
      (by rw [aeval_rename_block, aeval_rename_block])
    refine ⟨h, ?_⟩
    rw [hσ, aeval_rename_block, aeval_rename_block]
  · intro d hd z hz
    induction hz using Algebra.adjoin_induction with
    | mem x hx =>
      obtain ⟨⟨k, i⟩, rfl⟩ := hx
      obtain ⟨h, hσ⟩ := frac_spec hle (isMultiHomog_X (F := F) k i) (isMultiHomog_X (F := F) k (d k))
        (by rw [aeval_X]; exact hd k) _ (by rw [aeval_X, aeval_X])
      refine ⟨h, ?_⟩
      rw [hσ, aeval_X, aeval_X]
      exact Algebra.subset_adjoin ⟨⟨k, i⟩, rfl⟩
    | algebraMap r =>
      refine ⟨Subalgebra.algebraMap_mem _ r, ?_⟩
      show sigma hle (algebraMap F (locR hle) r) ∈ _
      rw [AlgHom.commutes]
      exact Subalgebra.algebraMap_mem _ r
    | add x x' _ _ ih ih' =>
      obtain ⟨h, hσ⟩ := ih
      obtain ⟨h', hσ'⟩ := ih'
      refine ⟨add_mem h h', ?_⟩
      rw [show (⟨x + x', add_mem h h'⟩ : locR hle) = ⟨x, h⟩ + ⟨x', h'⟩ from rfl, map_add (f := _)]
      exact add_mem hσ hσ'
    | mul x x' _ _ ih ih' =>
      obtain ⟨h, hσ⟩ := ih
      obtain ⟨h', hσ'⟩ := ih'
      refine ⟨mul_mem h h', ?_⟩
      rw [show (⟨x * x', mul_mem h h'⟩ : locR hle) = ⟨x, h⟩ * ⟨x', h'⟩ from rfl, map_mul]
      exact mul_mem hσ hσ'

end GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization
end
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.MemChartSecOverOfMem
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization

open scoped Pointwise
open ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.KH (secOver)

variable (S : Type) [CommRing S] {K : Type} [Fintype K] [DecidableEq K] {ι : K → Type} {Ω : Type} [Field Ω]
  [Algebra S Ω]

def chartSecOver (y : (Σ k, ι k) → Ω) (k₀ : K) {N : ℕ} (e : ι k₀ ≃ Fin (N + 1)) (δ : K → ℤ)
    (I : Kleiman.Chart (IndefiniteRowSideFullHecke.Kleiman2.blockVec y k₀ ∘ e.symm)) : Set Ω :=
  {t | ∃ n : ℕ, Kleiman.xProd I ^ n * t ∈
    secOver S y (δ + ((n * I.1.card : ℕ) : ℤ) • IndefiniteRowSideFullHecke.Kleiman2.baseDeg k₀)}

def ChartSecMul.Statement : Prop :=
  ∀ (S : Type) [CommRing S] (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)]
    (Ω : Type) [Field Ω] [Algebra S Ω] (y : (Σ k, ι k) → Ω) (k₀ : K) (N : ℕ) (e : ι k₀ ≃ Fin (N + 1)),
    IndefiniteRowSideFullHecke.Kleiman2.IsModelWithBase S y k₀ → ∀ (γ β : K → ℤ)
      (I : Kleiman.Chart (IndefiniteRowSideFullHecke.Kleiman2.blockVec y k₀ ∘ e.symm)),
      (Submodule.span (Kleiman.chartRing S (IndefiniteRowSideFullHecke.Kleiman2.blockVec y k₀ ∘ e.symm) I)
          (chartSecOver S y k₀ e γ I * chartSecOver S y k₀ e β I) : Set Ω) =
        chartSecOver S y k₀ e (γ + β) I

theorem mem_chartSecOver_of_mem (y : (Σ k, ι k) → Ω) (k₀ : K) {N : ℕ} (e : ι k₀ ≃ Fin (N + 1)) (δ : K → ℤ)
    (I : Kleiman.Chart (IndefiniteRowSideFullHecke.Kleiman2.blockVec y k₀ ∘ e.symm)) {t : Ω} (ht : t ∈ secOver S y δ) :
    t ∈ chartSecOver S y k₀ e δ I :=
  ⟨0, by simpa using ht⟩

end GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization
end

