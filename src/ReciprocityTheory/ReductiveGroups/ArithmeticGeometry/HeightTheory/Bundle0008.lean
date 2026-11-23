module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.HeightTheory.Bundle0004
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.HeightTheory.LaTIsPrime

@[expose] public section

-- bundled from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.HeightTheory.FiniteDimensionalOfLiftY
section
namespace ReciprocityTheory.ChartRestriction.G.T0.FractionFieldVariableLift

open MvPolynomial

section Clear

variable {A : Type} [CommRing A] [IsDomain A] {σ : Type}

theorem clear_denoms (P : MvPolynomial σ (FractionRing A)) :
    ∃ (b : A) (p : MvPolynomial σ A), b ≠ 0 ∧
      MvPolynomial.map (algebraMap A (FractionRing A)) p =
        MvPolynomial.C (algebraMap A (FractionRing A) b) * P := by
  induction P using MvPolynomial.induction_on
  next a =>
    obtain ⟨z, hz⟩ := IsLocalization.surj (nonZeroDivisors A) a
    refine ⟨z.2, C z.1, nonZeroDivisors.coe_ne_zero z.2, ?_⟩
    rw [MvPolynomial.map_C, ← hz, MvPolynomial.C_mul, mul_comm]
  next p q hp hq =>
    obtain ⟨b₁, p₁, hb₁, h₁⟩ := hp
    obtain ⟨b₂, p₂, hb₂, h₂⟩ := hq
    refine ⟨b₁ * b₂, C b₂ * p₁ + C b₁ * p₂, mul_ne_zero hb₁ hb₂, ?_⟩
    simp only [_root_.map_add (f := _), _root_.map_mul, MvPolynomial.map_C, h₁, h₂]
    ring
  next p n hp =>
    obtain ⟨b, q, hb, h⟩ := hp
    exact ⟨b, q * X n, hb, by rw [_root_.map_mul, MvPolynomial.map_X, h, mul_assoc]⟩

noncomputable def toFracY (A : Type) [CommRing A] [IsDomain A] (σ : Type) :
    MvPolynomial σ A →+* FractionRing (MvPolynomial σ (FractionRing A)) :=
  (algebraMap (MvPolynomial σ (FractionRing A)) _).comp (MvPolynomial.map (algebraMap A (FractionRing A)))

theorem toFracY_injective : Function.Injective (toFracY A σ) := by
  intro x y h
  have h' : algebraMap (MvPolynomial σ (FractionRing A))
      (FractionRing (MvPolynomial σ (FractionRing A)))
      (MvPolynomial.map (algebraMap A (FractionRing A)) x) =
      algebraMap (MvPolynomial σ (FractionRing A)) (FractionRing (MvPolynomial σ (FractionRing A)))
      (MvPolynomial.map (algebraMap A (FractionRing A)) y) := h
  exact MvPolynomial.map_injective _ (IsFractionRing.injective A (FractionRing A))
    (IsFractionRing.injective _ _ h')

set_option synthInstance.maxHeartbeats 400000 in
theorem isFractionRing_toFracY :
    @IsFractionRing (MvPolynomial σ A) _ (FractionRing (MvPolynomial σ (FractionRing A))) _
      (toFracY A σ).toAlgebra := by
  letI := (toFracY A σ).toAlgebra
  refine ⟨?_, ?_, ?_⟩
  · intro y
    refine IsUnit.mk0 _ (fun h => nonZeroDivisors.coe_ne_zero y (toFracY_injective ?_))
    rw [_root_.map_zero]
    exact h
  · intro z
    obtain ⟨uv, huv⟩ := IsLocalization.surj (nonZeroDivisors (MvPolynomial σ (FractionRing A))) z
    obtain ⟨b₁, p₁, hb₁, h₁⟩ := clear_denoms (uv.1 : MvPolynomial σ (FractionRing A))
    obtain ⟨b₂, p₂, hb₂, h₂⟩ := clear_denoms (uv.2 : MvPolynomial σ (FractionRing A))
    have hv : (uv.2 : MvPolynomial σ (FractionRing A)) ≠ 0 := nonZeroDivisors.coe_ne_zero uv.2
    have hβ₂ : algebraMap A (FractionRing A) b₂ ≠ 0 :=
      IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors (mem_nonZeroDivisors_of_ne_zero hb₂)
    have hp₂ne : p₂ ≠ 0 := by
      rintro rfl
      rw [_root_.map_zero] at h₂
      exact mul_ne_zero (fun h => hβ₂ (MvPolynomial.C_eq_zero.mp h)) hv h₂.symm
    have hp₂ : C b₁ * p₂ ∈ nonZeroDivisors (MvPolynomial σ A) :=
      mem_nonZeroDivisors_of_ne_zero (mul_ne_zero (fun h => hb₁ (MvPolynomial.C_eq_zero.mp h)) hp₂ne)
    refine ⟨⟨C b₂ * p₁, ⟨C b₁ * p₂, hp₂⟩⟩, ?_⟩
    show z * toFracY A σ (C b₁ * p₂) = toFracY A σ (C b₂ * p₁)
    simp only [toFracY, RingHom.coe_comp, Function.comp_apply, _root_.map_mul,
      MvPolynomial.map_C, h₁, h₂]
    linear_combination (algebraMap (MvPolynomial σ (FractionRing A))
      (FractionRing (MvPolynomial σ (FractionRing A))) (C (algebraMap A (FractionRing A) b₁)) *
      algebraMap (MvPolynomial σ (FractionRing A))
      (FractionRing (MvPolynomial σ (FractionRing A))) (C (algebraMap A (FractionRing A) b₂))) * huv
  · intro x y h
    exact ⟨1, by rw [toFracY_injective h]⟩

end Clear

section Disjoint

variable {L E : Type} [Field L] [Field E] [Algebra L E] {σ : Type}

private theorem liftY_algebraMap (x : MvPolynomial σ L) :
    ReciprocityTheory.ChartRestriction.G.T0.VariableBasisExtension.liftY (L := L) (E := E) (σ := σ)
        (algebraMap (MvPolynomial σ L) (FractionRing (MvPolynomial σ L)) x) =
      algebraMap (MvPolynomial σ E) (FractionRing (MvPolynomial σ E))
        (MvPolynomial.map (algebraMap L E) x) := by
  rw [ReciprocityTheory.ChartRestriction.G.T0.VariableBasisExtension.liftY, IsFractionRing.lift_algebraMap, RingHom.comp_apply]

private theorem linearIndependent_algebraMap_C_fractionRing
    [Algebra (FractionRing (MvPolynomial σ L)) (FractionRing (MvPolynomial σ E))]
    (hmap : algebraMap (FractionRing (MvPolynomial σ L)) (FractionRing (MvPolynomial σ E)) =
      ReciprocityTheory.ChartRestriction.G.T0.VariableBasisExtension.liftY)
    {ι : Type} [Fintype ι] (e : ι → E) (he : LinearIndependent L e) :
    LinearIndependent (FractionRing (MvPolynomial σ L))
      (fun i => algebraMap (MvPolynomial σ E) (FractionRing (MvPolynomial σ E))
        (MvPolynomial.C (e i))) := by
  rw [Fintype.linearIndependent_iff]
  intro g hg i
  have hg' : ∑ j, algebraMap (FractionRing (MvPolynomial σ L)) (FractionRing (MvPolynomial σ E)) (g j) *
      algebraMap (MvPolynomial σ E) (FractionRing (MvPolynomial σ E)) (MvPolynomial.C (e j)) = 0 := by
    simpa only [Algebra.smul_def] using hg
  obtain ⟨b, hb⟩ := IsLocalization.exist_integer_multiples_of_finite
    (nonZeroDivisors (MvPolynomial σ L)) g
  have hb' : ∀ j, ∃ c : MvPolynomial σ L,
      algebraMap (MvPolynomial σ L) (FractionRing (MvPolynomial σ L)) c =
        algebraMap (MvPolynomial σ L) (FractionRing (MvPolynomial σ L)) (b : MvPolynomial σ L) * g j := by
    intro j
    obtain ⟨c, hc⟩ := RingHom.mem_rangeS.mp (hb j)
    exact ⟨c, by rw [hc, Algebra.smul_def]⟩
  choose a ha using hb'
  have key : ∀ j, algebraMap (MvPolynomial σ E) (FractionRing (MvPolynomial σ E))
      (MvPolynomial.map (algebraMap L E) (a j) * MvPolynomial.C (e j)) =
      ReciprocityTheory.ChartRestriction.G.T0.VariableBasisExtension.liftY
          (algebraMap (MvPolynomial σ L) (FractionRing (MvPolynomial σ L)) (b : MvPolynomial σ L)) *
        (algebraMap (FractionRing (MvPolynomial σ L)) (FractionRing (MvPolynomial σ E)) (g j) *
          algebraMap (MvPolynomial σ E) (FractionRing (MvPolynomial σ E)) (MvPolynomial.C (e j))) := by
    intro j
    rw [_root_.map_mul, ← liftY_algebraMap, ha j, _root_.map_mul, hmap, mul_assoc]
  have hsum : ∑ j, MvPolynomial.map (algebraMap L E) (a j) * MvPolynomial.C (e j) = 0 := by
    apply IsFractionRing.injective (MvPolynomial σ E) (FractionRing (MvPolynomial σ E))
    set_option synthInstance.maxHeartbeats 100000 in
      rw [_root_.map_zero, _root_.map_sum, Finset.sum_congr rfl (fun j _ => key j), ← Finset.mul_sum,
      hg', mul_zero]
  have hcoeff : ∀ m j, AddMonoidAlgebra.coeff (a j) m = 0 := by
    intro m
    have hsum' : ∑ j, MvPolynomial.C (e j) * MvPolynomial.map (algebraMap L E) (a j) = 0 := by
      simpa only [mul_comm] using hsum
    have h0 := congrArg (AddMonoidAlgebra.coeff · m) hsum'
    simp only [MvPolynomial.coeff_sum, MvPolynomial.coeff_C_mul, MvPolynomial.coeff_map,
      AddMonoidAlgebra.coeff_zero] at h0
    have h1 : ∑ j, AddMonoidAlgebra.coeff (a j) m • e j = 0 := by
      simpa [Algebra.smul_def, mul_comm] using h0
    exact Fintype.linearIndependent_iff.mp he (fun j => AddMonoidAlgebra.coeff (a j) m) h1
  have hai : a i = 0 := by
    ext m
    simpa using hcoeff m i
  have h2 := ha i
  rw [hai, _root_.map_zero] at h2
  have hβ : algebraMap (MvPolynomial σ L) (FractionRing (MvPolynomial σ L)) (b : MvPolynomial σ L) ≠ 0 :=
    IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors b.2
  exact (mul_eq_zero.mp h2.symm).resolve_left hβ

theorem finiteDimensional_of_liftY
    (hfin : letI := (VariableBasisExtension.liftY (L := L) (E := E) (σ := σ)).toAlgebra
      FiniteDimensional (FractionRing (MvPolynomial σ L)) (FractionRing (MvPolynomial σ E))) :
    FiniteDimensional L E := by
  letI : Algebra (FractionRing (MvPolynomial σ L)) (FractionRing (MvPolynomial σ E)) :=
    (ReciprocityTheory.ChartRestriction.G.T0.VariableBasisExtension.liftY (L := L) (E := E) (σ := σ)).toAlgebra
  haveI : FiniteDimensional (FractionRing (MvPolynomial σ L)) (FractionRing (MvPolynomial σ E)) :=
    hfin
  have hbound : ∀ s : Finset E, LinearIndependent L (fun x : s => (x : E)) →
      s.card ≤ Module.finrank (FractionRing (MvPolynomial σ L)) (FractionRing (MvPolynomial σ E)) := by
    intro s hs
    have hli := linearIndependent_algebraMap_C_fractionRing (σ := σ) rfl (fun x : s => (x : E)) hs
    simpa using hli.fintype_card_le_finrank
  have hr := rank_le hbound
  exact Module.rank_lt_aleph0_iff.mp (hr.trans_lt (Cardinal.natCast_lt_aleph0))

end Disjoint

end ReciprocityTheory.ChartRestriction.G.T0.FractionFieldVariableLift
end

-- bundled from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.HeightTheory.HeightIntegralEstimates
section
namespace ReciprocityTheory.ChartRestriction.G.T0

open NumberField

variable {K : Type} [Field K] [NumberField K] {ι : Type} [Fintype ι]
  {Ω : ι → Type} [∀ c, Field (Ω c)] [∀ c, Algebra K (Ω c)]
  {WT : Type} [AddCommGroup WT]
  {A : ι → Type} [∀ c, CommRing (A c)] [∀ c, Algebra (Ω c) (A c)] [∀ c, Algebra K (A c)]
  [∀ c, Algebra (𝓞 K) (A c)]

namespace Data

variable (d : Data K ι Ω WT A) (𝒜 : (c : ι) → WT → Submodule (Ω c) (A c))

structure AxH : Type where
  nonempty : Nonempty ι
  tower : ∀ c, IsScalarTower K (Ω c) (A c)
  towerO : ∀ c, IsScalarTower (𝓞 K) K (A c)
  D_ge : 3 ≤ d.D
  fg : ∀ c, (⊤ : IntermediateField K (Ω c)).FG
  trdeg : ∀ c, Algebra.trdeg K (Ω c) = d.D
  algClosed : ∀ c (a : Ω c), IsAlgebraic K a → a ∈ (algebraMap K (Ω c)).range
  graded : ∀ c, SetLike.GradedMonoid (𝒜 c)
  finrank_one : ∀ c G, Module.finrank (Ω c) (𝒜 c G) = 1
  mul_ne_zero : ∀ c {G G' : WT} {f g : A c}, f ∈ 𝒜 c G → g ∈ 𝒜 c G' → f ≠ 0 → g ≠ 0 →
    f * g ≠ 0
  WW_span : d.WW = Submodule.span (𝓞 K) (Set.range d.w)
  w_mem : ∀ j c, d.w j c ∈ 𝒜 c d.wL
  w_base : ∀ c, d.w (d.jc c) c ≠ 0
  Thp_span : d.Thp = Submodule.span (𝓞 K) (Set.range d.thp)
  thp_mem : ∀ k c, d.thp k c ∈ 𝒜 c d.wF
  et_mem : ∀ c, d.et c ∈ 𝒜 c (d.n1 • d.wde)
  firstSectionMem : ∀ c, d.ta1 c ∈ 𝒜 c ((2 : ℕ) • d.G1)
  secondSectionMem : ∀ c, d.ta2 c ∈ 𝒜 c d.G2
  et_ne : ∀ c, d.et c ≠ 0
  firstSectionNeZero : ∀ c, d.ta1 c ≠ 0
  secondSectionNeZero : ∀ c, d.ta2 c ≠ 0
  ord_mul : ∀ c v, d.admitted c v → ∀ {G G' : WT} {f g : A c}, f ∈ 𝒜 c G → g ∈ 𝒜 c G' →
    f ≠ 0 → g ≠ 0 → d.ord c v (G + G') (f * g) = d.ord c v G f + d.ord c v G' g
  ord_smul : ∀ c v, d.admitted c v → ∀ {G : WT} {f : A c} (a : Ω c), f ∈ 𝒜 c G → f ≠ 0 → a ≠ 0 →
    ((d.ord c v G (a • f) : ℤ) : WithTop ℤ) = v a + (d.ord c v G f : WithTop ℤ)
  nrm_pos : ∀ c {G : WT} {f : A c} (P : Ω c →+* ℂ), f ∈ 𝒜 c G → f ≠ 0 → 0 < d.nrm c G f P
  nrm_zero : ∀ c (G : WT) (P : Ω c →+* ℂ), d.nrm c G 0 P = 0
  nrm_mul : ∀ c {G G' : WT} {f g : A c} (P : Ω c →+* ℂ), f ∈ 𝒜 c G → g ∈ 𝒜 c G' →
    f ≠ 0 → g ≠ 0 → d.nrm c (G + G') (f * g) P = d.nrm c G f P * d.nrm c G' g P
  nrm_smul : ∀ c {G : WT} {f : A c} (P : Ω c →+* ℂ) (a : Ω c), f ∈ 𝒜 c G → f ≠ 0 → a ≠ 0 →
    d.nrm c G (a • f) P = ‖P a‖ * d.nrm c G f P
  nrm_conj : ∀ c (G : WT) (f : A c) (P : Ω c →+* ℂ),
    d.nrm c G f ((starRingEnd ℂ).comp P) = d.nrm c G f P
  bdd : ∀ (sg : K →+* ℂ) (G : WT) (f : ∀ c, A c),
    ((f ∈ d.WW ∧ G = d.wL) ∨ (f ∈ d.Thp ∧ G = d.wF) ∨ (f = d.et ∧ G = d.n1 • d.wde) ∨
      (f = d.ta1 ∧ G = (2 : ℕ) • d.G1) ∨ (f = d.ta2 ∧ G = d.G2)) →
    BddAbove (Set.range fun p : (Σ c, PT (Ω := Ω c) sg) => d.nrm p.1 G (f p.1) p.2)
  a1 : ∀ c, ∃ J : Fin d.D → Fin d.N,
    LinearIndependent (Ω c) fun k => KaehlerDifferential.D K (Ω c) (d.x c (J k))
  ord_nonneg_WW : ∀ c v, d.admitted c v → ∀ f ∈ d.WW, f c ≠ 0 → 0 ≤ d.ord c v d.wL (f c)
  ord_nonneg_Thp : ∀ c v, d.admitted c v → ∀ f ∈ d.Thp, f c ≠ 0 → 0 ≤ d.ord c v d.wF (f c)
  ord_nonneg_et : ∀ c v, d.admitted c v → 0 ≤ d.ord c v (d.n1 • d.wde) (d.et c)
  ordDoubleFirstSection_nonneg : ∀ c v, d.admitted c v → 0 ≤ d.ord c v ((2 : ℕ) • d.G1) (d.ta1 c)
  ordSecondSectionNonneg : ∀ c v, d.admitted c v → 0 ≤ d.ord c v d.G2 (d.ta2 c)
  a3' : ∀ c {G : WT} {f : A c}, f ∈ 𝒜 c G → f ≠ 0 → {v | d.admitted c v ∧ d.ord c v G f ≠ 0}.Finite
  sel : Fin d.del → Fin d.np
  a4 : ∃ e : ∀ c, A c, (∀ c, e c ∈ 𝒜 c d.wF ∧ e c ≠ 0) ∧
    (∀ p : Fin d.del → MvPolynomial (TVar d.D d.N) K,
      (∀ c, ∑ k, d.sH c (p k) *
        algebraMap (Ω c) (OmS (Ω c) d.D d.N) (ratio (Ω := Ω c) (d.thp (sel k) c) (e c)) = 0) →
      ∀ k, p k = 0) ∧
    (∀ y : ∀ c, OmS (Ω c) d.D d.N, ∃ q : MvPolynomial (TVar d.D d.N) K, (∀ c, d.sH c q ≠ 0) ∧
      ∃ p : Fin d.del → MvPolynomial (TVar d.D d.N) K, ∀ c, d.sH c q * y c = ∑ k, d.sH c (p k) *
        algebraMap (Ω c) (OmS (Ω c) d.D d.N) (ratio (Ω := Ω c) (d.thp (sel k) c) (e c)))
  i_ge : 1 ≤ d.i
  g_zero_ge_ask_sum : 1 ≤ d.g0
  cc_nonneg : 0 ≤ d.cc
  cc_le : d.cc ≤ 1
  ccg0 : d.cc * d.g0 ≤ 1 / 2
  size_L : 1 ≤ d.wsize d.wL
  DF_le : d.DF ≤ d.wsize d.wL
  rw_le : Real.log (d.N + 1 : ℕ) + 1 / 2 ≤ d.Prw * (d.wsize d.wL - 1)
  nK_le : Real.log (Module.finrank ℚ K) ≤ d.PO
  rd_le : Real.log (|(NumberField.discr K : ℝ)| ^ (1 / (Module.finrank ℚ K : ℝ))) ≤ d.PO
  P_ge : 1 ≤ d.PN ∧ 1 ≤ d.PQ ∧ 1 ≤ d.tableDegreeThreeBase ∧ 1 ≤ d.PP0' ∧ 1 ≤ d.Pd ∧ 1 ≤ d.Gc ∧ 1 ≤ d.PI4 ∧
    1 ≤ d.Pet ∧ 1 ≤ d.tableLineDegreeFive ∧ 1 ≤ d.tableLineDegreeTwo ∧ 1 ≤ d.Prw ∧ 1 ≤ d.PO
  a13 : ∀ c (sg : K →+* ℂ) {G : WT} {f : A c}, f ∈ 𝒜 c G → f ≠ 0 →
    AEMeasurable (fun t : Fin d.D → Metric.sphere (0 : EuclideanSpace ℂ (Fin (d.N + 1))) 1 =>
      ∑ᶠ P ∈ d.ST c sg (fun i j => (t i : EuclideanSpace ℂ (Fin (d.N + 1))) j),
        Real.log (d.nrm c G f P)) d.sphMeasure

variable {𝒜}

def FinitePlaceHyp : Prop :=
  (∀ la, 0 ≤ d.nu la) ∧
  ((Function.support d.nu).Finite) ∧
  ((∑ᶠ la, d.nu la * logNorm la) / (Module.finrank ℚ K : ℝ) ≤ d.PN * d.wsize d.wL) ∧
  (∀ c v la, d.admitted c v → IsOver (K := K) v la →
      ((⨅ j : {j // d.w j c ≠ 0}, d.ord c v d.wL (d.w j c) : ℤ) : ℝ) ≤
        (ramIdx (K := K) v la : ℝ) * d.nu la +
          d.cc / (2 * d.i) * d.ord c v (d.n1 • d.wde) (d.et c))

def TrivialPlaceHyp : Prop :=
  (∀ c v, d.admitted c v → IsTrivOn K v →
      ((⨅ j : {j // d.w j c ≠ 0}, d.ord c v d.wL (d.w j c) : ℤ) : ℝ) ≤
        d.cc / (2 * d.i) * d.ord c v (d.n1 • d.wde) (d.et c))

def HtLAM : Prop :=
  (∀ c, ∀ g ∈ Submodule.span (𝓞 K)
        (Set.range fun s : Fin d.n96 → Fin (d.N + 1) => ∏ k, d.w (s k)), g c ≠ 0 →
      -(d.PP0' * d.n96 * d.wsize d.wL) ≤
        meanK fun sg => Real.log (d.supNc c sg (d.n96 • d.wL) (g c)))

def HtSup : Prop :=
  (meanK (fun sg => ⨆ j, Real.log (d.supN sg d.wL (d.w j))) ≤ d.Gc * d.wsize d.wL) ∧
  (∀ k, meanK (fun sg => Real.log (d.supN sg d.wF (d.thp k))) ≤ d.Gc * d.wsize d.wF) ∧
  (meanK (fun sg => Real.log (d.supN sg ((2 : ℕ) • d.G1) d.ta1)) ≤
      2 * d.PI4 * d.D * d.wsize d.wL) ∧
  (meanK (fun sg => Real.log (d.supN sg d.G2 d.ta2)) ≤ d.PI4 * d.D * d.wsize d.wL)

def HeightIntegralEstimateTrivialPlace : Prop :=
  (meanK (fun sg => Real.log (d.supN sg (d.n1 • d.wde) d.et)) / d.i ≤ d.Pet)

def HeightIntegralBoundEstimate : Prop :=
  (∀ c (P : Ω c →+* ℂ),
      -Real.log (d.be c P) ≤
        d.tableLineDegreeFive * d.DF + d.cc / d.i * (-Real.log (d.nrm c (d.n1 • d.wde) (d.et c) P)) + d.cc * d.tableLineDegreeTwo)

def PHc : ℝ := 2 * d.PH + d.Gc

end Data

end ReciprocityTheory.ChartRestriction.G.T0
end

-- bundled from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.HeightTheory.OpIsDVR
section
namespace ReciprocityTheory.ChartRestriction.G.T0

open NumberField IsLocalRing

theorem Op_isDVR {K : Type} [Field K] [NumberField K] (D N : ℕ)
    (la : IsDedekindDomain.HeightOneSpectrum (𝓞 K)) : IsDiscreteValuationRing (Op D N la) := by
  classical
  set P := laT D N la with hP
  have hp0 : la.asIdeal ≠ ⊥ := la.ne_bot
  have hp1 : la.asIdeal ≠ ⊤ := la.isPrime.ne_top

  obtain ⟨π, hπp, hπ2⟩ : ∃ π ∈ la.asIdeal, π ∉ la.asIdeal ^ 2 := by
    have hlt : la.asIdeal ^ 2 < la.asIdeal ^ 1 :=
      Ideal.pow_right_strictAnti la.asIdeal hp0 hp1 (by norm_num : 1 < 2)
    rw [pow_one] at hlt
    obtain ⟨x, hx, hx2⟩ := SetLike.exists_of_lt hlt
    exact ⟨x, hx, hx2⟩
  have hmemP : ∀ t : 𝓞 K, MvPolynomial.C t ∈ P ↔ t ∈ la.asIdeal := by
    intro t
    rw [hP, laT, MvPolynomial.mem_map_C_iff]
    constructor
    · intro h
      simpa using h 0
    · intro h m
      rw [MvPolynomial.coeff_C]
      split_ifs
      · exact h
      · exact zero_mem _

  have hdiv : ∀ a ∈ la.asIdeal, ∃ t c : 𝓞 K, t ∉ la.asIdeal ∧ t * a = π * c := by
    intro a ha
    have hle : Ideal.span {π} ≤ la.asIdeal := (Ideal.span_singleton_le_iff_mem _).mpr hπp
    obtain ⟨J, hJ⟩ := Ideal.dvd_iff_le.mpr hle
    have hJp : ¬ J ≤ la.asIdeal := by
      intro hJle
      apply hπ2
      have hsq : Ideal.span {π} ≤ la.asIdeal ^ 2 := by
        rw [hJ, pow_two]
        exact Ideal.mul_mono_right hJle
      exact hsq (Ideal.mem_span_singleton_self π)
    obtain ⟨t, htJ, htp⟩ := SetLike.not_le_iff_exists.mp hJp
    have hta : t * a ∈ Ideal.span {π} := by
      rw [hJ, mul_comm t a]
      exact Ideal.mul_mem_mul ha htJ
    obtain ⟨c, hc⟩ := Ideal.mem_span_singleton'.mp hta
    exact ⟨t, c, htp, by rw [← hc, mul_comm]⟩
  haveI : IsNoetherianRing (Op D N la) :=
    IsLocalization.isNoetherianRing P.primeCompl (Op D N la) inferInstance
  let f : 𝓞 K →+* Op D N la := (algebraMap (OT K D N) (Op D N la)).comp MvPolynomial.C
  have hmax : IsLocalRing.maximalIdeal (Op D N la) = Ideal.map f la.asIdeal := by
    have e : Ideal.map f la.asIdeal =
        Ideal.map (algebraMap (OT K D N) (Op D N la)) (laT D N la) :=
      (Ideal.map_map (MvPolynomial.C : 𝓞 K →+* OT K D N) (algebraMap (OT K D N) (Op D N la))).symm
    rw [e]
    exact (Localization.AtPrime.map_eq_maximalIdeal).symm
  have hπm : IsLocalRing.maximalIdeal (Op D N la) = Ideal.span {f π} := by
    apply le_antisymm
    · rw [hmax, Ideal.map_le_iff_le_comap]
      intro a ha
      rw [Ideal.mem_comap]
      obtain ⟨t, c, htp, htc⟩ := hdiv a ha
      have hu : IsUnit (f t) :=
        (IsLocalization.AtPrime.isUnit_to_map_iff (Op D N la) P (MvPolynomial.C t)).mpr
          (fun h => htp ((hmemP t).mp h))
      obtain ⟨u, hu'⟩ := hu
      rw [Ideal.mem_span_singleton']
      refine ⟨↑u⁻¹ * f c, ?_⟩
      have hfm : f t * f a = f π * f c := by rw [← map_mul, ← map_mul, htc]
      calc ↑u⁻¹ * f c * f π = ↑u⁻¹ * (f π * f c) := by ring
        _ = ↑u⁻¹ * (f t * f a) := by rw [hfm]
        _ = f a := by rw [← hu', ← mul_assoc, Units.inv_mul, one_mul]
    · rw [Ideal.span_le, Set.singleton_subset_iff, hmax]
      exact Ideal.mem_map_of_mem f hπp
  have hnf : ¬ IsField (Op D N la) := by
    intro hF
    have hb := IsLocalRing.isField_iff_maximalIdeal_eq.mp hF
    rw [hπm, Ideal.span_singleton_eq_bot] at hb
    have hπ0 : π ≠ 0 := fun h => hπ2 (h ▸ zero_mem _)
    have hinj : Function.Injective (algebraMap (OT K D N) (Op D N la)) :=
      IsLocalization.injective (Op D N la) (Ideal.primeCompl_le_nonZeroDivisors P)
    exact hπ0 (MvPolynomial.C_injective _ _ ((hinj (hb.trans (map_zero _).symm)).trans
      (map_zero _).symm))
  have hprin : (IsLocalRing.maximalIdeal (Op D N la)).IsPrincipal := ⟨⟨f π, hπm⟩⟩
  exact ((IsDiscreteValuationRing.TFAE (Op D N la) hnf).out 1 5).mpr hprin

end ReciprocityTheory.ChartRestriction.G.T0
end

