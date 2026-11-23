module

public import Mathlib
public import GroundTheory.HeightsAndTheta.Heights.HeightKernels.Bundle0029
public import GroundTheory.HeightsAndTheta.Heights.HeightKernels.Bundle0028
public import GroundTheory.HeightsAndTheta.Heights.HeightKernels.Bundle0030
public import GroundTheory.HeightsAndTheta.Heights.HeightKernels.Bundle0027
public import GroundTheory.PowerSubgroups.CountableNeighbourhoods.Bundle0003
public import GroundTheory.HeightsAndTheta.Heights.Bundle0001
public import GroundTheory.HeightsAndTheta.Heights.Intersections.Bundle0007
public import GroundTheory.ArithmeticGeometry.ToricVarieties.Bundle0001
public import GroundTheory.HeightsAndTheta.Heights.HeightComparison.Bundle0003
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Bundle0034

@[expose] public section

-- bundled from GroundTheory.HeightsAndTheta.Heights.HeightKernels.PDualStdGenDeg
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I4 ReciprocityTheory.ChartRestriction.G.AI.I1 NumberField MvPolynomial

namespace DualStdGenDeg

def fibreBlk₀ : FibreBlock (Sum.inr : Unit → Unit ⊕ Unit) :=
  ⟨Sum.inl (), fun ⟨_, h⟩ => Sum.inr_ne_inl h⟩

theorem eq_fibreBlk₀ (k : FibreBlock (Sum.inr : Unit → Unit ⊕ Unit)) : k = fibreBlk₀ := by
  rcases k with ⟨⟨⟩ | ⟨⟩, h⟩
  · rfl
  · exact absurd ⟨(), rfl⟩ h

def fibreCoord {T : Type} {i : ℕ} (c : T) :
    ∀ k : FibreBlock (Sum.inr : Unit → Unit ⊕ Unit), fibreIdx (Sum.elim (dualBlocks T) (PBlk i)) Sum.inr k
  | ⟨Sum.inl (), _⟩ => c
  | ⟨Sum.inr (), h⟩ => absurd ⟨(), rfl⟩ h

theorem range_eq {T Φ' : Type} [Field Φ'] {i : ℕ} (x' : (Σ k, Sum.elim (dualBlocks T) (PBlk i) k) → Φ') (d : Φ') :
    (Set.range fun p : (Σ k : FibreBlock (Sum.inr : Unit → Unit ⊕ Unit),
        fibreIdx (Sum.elim (dualBlocks T) (PBlk i)) Sum.inr k) => x' ⟨p.1.1, p.2⟩ / d) =
      Set.range fun t : T => x' (⟨Sum.inl (), t⟩ : Σ k, Sum.elim (dualBlocks T) (PBlk i) k) / d := by
  ext y
  constructor
  · rintro ⟨⟨⟨⟨⟩ | ⟨⟩, h⟩, t⟩, rfl⟩
    · exact ⟨t, rfl⟩
    · exact absurd ⟨(), rfl⟩ h
  · rintro ⟨t, rfl⟩
    exact ⟨⟨fibreBlk₀, t⟩, rfl⟩

end DualStdGenDeg


open DualStdGenDeg in
theorem DualStdGenDeg.proof (hPt : OneBlockPointDeg.Statement) (hRat : DualStdFibreRatios.Statement) :
    DualStdGenDeg.Statement := by
  intro K _ _ i T _ _ b G J hi hJ
  obtain ⟨c, hc, hrank, htr⟩ := hRat K i T b G hi
  have hfin : Module.Finite G.Φ (Algebra.adjoin G.Φ (Set.range fun t : T =>
      G.x' (⟨Sum.inl (), t⟩ : Σ k, Sum.elim (dualBlocks T) (PBlk i) k) /
        G.x' (⟨Sum.inl (), c⟩ : Σ k, Sum.elim (dualBlocks T) (PBlk i) k))) :=
    Module.finite_of_finrank_pos (hrank ▸ Module.finrank_pos)
  have key := hPt G.Φ G.Φ' (FibreBlock (Sum.inr : Unit → Unit ⊕ Unit))
    (fibreIdx (Sum.elim (dualBlocks T) (PBlk i)) Sum.inr) fibreBlk₀ eq_fibreBlk₀
    (fun q => G.x' ⟨q.1.1, q.2⟩) (fibreCoord c) hc
  beta_reduce at key
  rw [range_eq G.x'] at key
  obtain ⟨hV, hch, hdeg⟩ := key hfin htr
  have hJ0 := hJ.1 (fibreIdeal Sum.inr G) Fin.elim0 (fibreCoord c) hV hch
  rw [hJ0]
  exact congrArg ((↑) : ℕ → ℤ) (hdeg.trans hrank)

end GroundTheory.Heights₂.Heights
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.HeightKernels.PDualTopSimpleSub
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open ReciprocityTheory.ChartRestriction.G.Geo NumberField

noncomputable section

theorem DualTopSimpleSub.proof (hBasis : DualTopBasisChange.Statement)
    (hStep : DualTopSimpleStacked.Statement) (hDeg : DualStackedDegree.Statement) :
    DualTopSimpleSub.Statement := by
  intro K _ _ i F F' T T' _ _ _ _ b hb b' hb' II hi hII hlt hcov
  have hle := hlt.le
  have hcard : Fintype.card T = Fintype.card T' := by
    rw [DualTopStackedExistence.card_eq_of_bijective b hb, DualTopStackedExistence.card_eq_of_bijective b' hb']
  obtain ⟨b₁, b₁', a, hab⟩ := DualTopStackedExistence.exists_stacked hle b b' hcard
  have hb₁ := DualEmbBijective.proof K i F T' b₁
  have hb₁' := DualEmbBijective.proof K i F' T' b₁'

  have h1 : II Unit (dualBlocks T') (dualIdeal b') i (fun _ => dualLine F'.withStdMetric b' hb') =
      II Unit (dualBlocks T') (dualIdeal b₁') i (fun _ => dualLine F'.withStdMetric b₁' hb₁') :=
    hBasis K i F'.withStdMetric T' T' b₁' hb₁' b' hb' II hi hII
  have h2 : II Unit (dualBlocks T') (dualIdeal b₁) i (fun _ => dualLine F.withStdMetric b₁ hb₁) =
      II Unit (dualBlocks T) (dualIdeal b) i (fun _ => dualLine F.withStdMetric b hb) :=
    hBasis K i F.withStdMetric T T' b hb b₁ hb₁ II hi hII

  have h3 := hStep K i F F' T' b₁ hb₁ b₁' hb₁' a II hi hII hlt hcov hab
  have h4 := hDeg K i F F' T' b₁ b₁' a hle hab
  rw [h1, h3, h2, h4]

end

end GroundTheory.Heights₂.Heights
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.HeightKernels.PDualTopStacked
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open ReciprocityTheory.ChartRestriction.G.Geo NumberField
open scoped ComplexOrder

noncomputable section

namespace TopDualStacked

variable {K : Type} [Field K] [NumberField K] {i : ℕ}

def DegForm (F G : HermLattice K i) : Prop :=
  ∀ (T T' : Type) [Fintype T] [DecidableEq T] [Fintype T'] [DecidableEq T']
    (b : Module.Basis T ℤ (dualLattice F)) (hb : Function.Bijective (Matrix.mulVecLin (dualEmbMatrix b)))
    (b' : Module.Basis T' ℤ (dualLattice G))
    (hb' : Function.Bijective (Matrix.mulVecLin (dualEmbMatrix b'))) (II : IntersectionSystem),
    1 ≤ i → IsIntersectionSystem II →
    II Unit (dualBlocks T') (dualIdeal b') i (fun _ => dualLine G.withStdMetric b' hb') =
      II Unit (dualBlocks T) (dualIdeal b) i (fun _ => dualLine F.withStdMetric b hb) +
        (F.withStdMetric.degree - G.withStdMetric.degree) *
          geomDeg (grassIdeal 1 1 (i - 1)) (fsMulti (plBlocks 1 1 (i - 1))) (1 * 1 * (i - 1))

theorem DegForm.trans {F G H : HermLattice K i} (h₁ : DegForm F G) (h₂ : DegForm G H) : DegForm F H := by
  intro T T' _ _ _ _ b hb b' hb' II hi hII
  obtain ⟨S, hS, hdS, ⟨c⟩⟩ := DualLatticeBasisExists.proof K i G
  have hc := DualEmbBijective.proof K i G S c
  have e₂ := h₂ S T' c hc b' hb' II hi hII
  have e₁ := h₁ T S b hb c hc II hi hII
  linarith

theorem degForm_self (hBasis : DualTopBasisChange.Statement) (F : HermLattice K i) : DegForm F F := by
  intro T T' _ _ _ _ b hb b' hb' II hi hII
  have e := hBasis K i F.withStdMetric T T' b hb b' hb' II hi hII
  rw [sub_self, zero_mul, add_zero]
  exact e

theorem withStdMetric_eq {F G : HermLattice K i} (h : F.lattice = G.lattice) :
    F.withStdMetric = G.withStdMetric := by
  cases F
  cases G
  cases h
  rfl

theorem degForm_iff (F G : HermLattice K i) : DegForm F G ↔ DegForm F.withStdMetric G.withStdMetric :=
  Iff.rfl

theorem degForm_of_eq (hBasis : DualTopBasisChange.Statement) {F G : HermLattice K i}
    (h : G.lattice = F.lattice) : DegForm F G := by
  rw [degForm_iff, withStdMetric_eq h]
  exact degForm_self hBasis _

theorem degForm_of_cover (hSimple : DualTopSimpleSub.Statement) {F G : HermLattice K i}
    (hlt : G.lattice < F.lattice)
    (hcov : ∀ N : Submodule (𝓞 K) (Fin i → K), G.lattice ≤ N → N ≤ F.lattice → N = G.lattice ∨ N = F.lattice) :
    DegForm F G :=
  fun T T' _ _ _ _ b hb b' hb' II hi hII => hSimple K i F G T T' b hb b' hb' II hi hII hlt hcov

theorem exists_cover {F X : HermLattice K i} (hlt : X.lattice < F.lattice) :
    ∃ w ∈ F.lattice, w ∉ X.lattice ∧ ∀ N : Submodule (𝓞 K) (Fin i → K), X.lattice ≤ N →
      N ≤ X.lattice ⊔ Submodule.span (𝓞 K) {w} → N = X.lattice ∨ N = X.lattice ⊔ Submodule.span (𝓞 K) {w} :=
  _root_.GroundTheory.Variant₂.N1.exists_cover hlt

def addVector (X : HermLattice K i) (w : Fin i → K) : HermLattice K i where
  lattice := X.lattice ⊔ Submodule.span (𝓞 K) {w}
  fg := X.fg.sup (Submodule.fg_span_singleton w)
  span_eq := eq_top_iff.mpr (X.span_eq ▸ Submodule.span_mono (SetLike.coe_subset_coe.mpr le_sup_left))
  metric := fun _ => 1
  posDef := fun _ => Matrix.PosDef.one
  conj := fun _ => by simp

theorem degForm_of_le (hSimple : DualTopSimpleSub.Statement) (hBasis : DualTopBasisChange.Statement)
    (F G : HermLattice K i) (hle : G.lattice ≤ F.lattice) : DegForm F G := by
  have : IsNoetherian (𝓞 K) F.lattice := isNoetherian_of_fg_of_noetherian _ F.fg
  suffices h : ∀ N : Submodule (𝓞 K) F.lattice, ∀ G : HermLattice K i,
      G.lattice = N.map F.lattice.subtype → DegForm F G by
    refine h (G.lattice.comap F.lattice.subtype) G ?_
    rw [Submodule.map_comap_subtype, inf_eq_right.mpr hle]
  intro N
  refine WellFoundedGT.induction
    (motive := fun N : Submodule (𝓞 K) F.lattice => ∀ G : HermLattice K i,
      G.lattice = N.map F.lattice.subtype → DegForm F G) N ?_
  intro N IH G hG
  by_cases hGF : G.lattice = F.lattice
  · exact degForm_of_eq hBasis hGF
  have hlt : G.lattice < F.lattice :=
    lt_of_le_of_ne (hG ▸ Submodule.map_subtype_le _ _) hGF
  obtain ⟨w, hwF, hwG, hcov⟩ := exists_cover hlt
  have hG'F : (addVector G w).lattice ≤ F.lattice :=
    sup_le hlt.le ((Submodule.span_singleton_le_iff_mem _ _).mpr hwF)
  have hGG' : G.lattice < (addVector G w).lattice :=
    lt_of_le_of_ne le_sup_left fun h =>
      hwG (h ▸ Submodule.mem_sup_right (Submodule.mem_span_singleton_self w))
  have hNG : N = G.lattice.comap F.lattice.subtype := by
    rw [hG, Submodule.comap_map_eq_of_injective F.lattice.injective_subtype]
  have hN : N < (addVector G w).lattice.comap F.lattice.subtype := by
    rw [hNG]
    refine lt_of_le_of_ne (Submodule.comap_mono hGG'.le) fun h => hGG'.ne ?_
    have h2 := congrArg (Submodule.map F.lattice.subtype) h
    rwa [Submodule.map_comap_subtype, Submodule.map_comap_subtype, inf_eq_right.mpr hlt.le,
      inf_eq_right.mpr hG'F] at h2
  have h1 : DegForm F (addVector G w) :=
    IH _ hN (addVector G w) (by rw [Submodule.map_comap_subtype, inf_eq_right.mpr hG'F])
  exact h1.trans (degForm_of_cover hSimple hGG' hcov)

end TopDualStacked


open TopDualStacked in
theorem DualTopStacked.proof (hSimple : DualTopSimpleSub.Statement) (hBasis : DualTopBasisChange.Statement)
    (hDeg : DualStackedDegree.Statement) : DualTopStacked.Statement := by
  intro K _ _ i F F' T _ _ b hb b' hb' a II hi hII hle hab
  have e := degForm_of_le hSimple hBasis F F' hle T T b hb b' hb' II hi hII
  rw [hDeg K i F F' T b b' a hle hab] at e
  exact e

end

end GroundTheory.Heights₂.Heights
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.HeightKernels.PDualTopSubLattice
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open ReciprocityTheory.ChartRestriction.G.Geo NumberField

noncomputable section

theorem DualTopSubLattice.proof (hBasis : DualTopBasisChange.Statement)
    (hStacked : DualTopStacked.Statement) (hDeg : DualStackedDegree.Statement) :
    DualTopSubLattice.Statement := by
  intro K _ _ i F F' T T' _ _ _ _ b hb b' hb' II hi hII hle
  have hcard : Fintype.card T = Fintype.card T' := by
    rw [DualTopStackedExistence.card_eq_of_bijective b hb, DualTopStackedExistence.card_eq_of_bijective b' hb']
  obtain ⟨b₁, b₁', a, hab⟩ := DualTopStackedExistence.exists_stacked hle b b' hcard
  have hb₁ := DualEmbBijective.proof K i F T' b₁
  have hb₁' := DualEmbBijective.proof K i F' T' b₁'

  have h1 : II Unit (dualBlocks T') (dualIdeal b') i (fun _ => dualLine F'.withStdMetric b' hb') =
      II Unit (dualBlocks T') (dualIdeal b₁') i (fun _ => dualLine F'.withStdMetric b₁' hb₁') :=
    hBasis K i F'.withStdMetric T' T' b₁' hb₁' b' hb' II hi hII
  have h2 : II Unit (dualBlocks T') (dualIdeal b₁) i (fun _ => dualLine F.withStdMetric b₁ hb₁) =
      II Unit (dualBlocks T) (dualIdeal b) i (fun _ => dualLine F.withStdMetric b hb) :=
    hBasis K i F.withStdMetric T T' b hb b₁ hb₁ II hi hII

  have h3 := hStacked K i F F' T' b₁ hb₁ b₁' hb₁' a II hi hII hle hab
  have h4 := hDeg K i F F' T' b₁ b₁' a hle hab
  rw [h1, h3, h2, h4]

end

end GroundTheory.Heights₂.Heights
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.HeightKernels.POneBlockPointDeg
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1

noncomputable section

namespace OneBlockPointDeg

variable {Φ Φ' : Type} [Field Φ] [Field Φ'] [Algebra Φ Φ'] {K : Type} [Fintype K] {ι : K → Type}
  [∀ k, Fintype (ι k)] {k₀ : K}

theorem isMultiHomog_of_isHomogeneous (hK : ∀ k, k = k₀) {f : MRingOver Φ ι} {n : ℕ}
    (hf : f.IsHomogeneous n) : IsMultiHomog f fun _ => n := by
  intro m hm k
  have h := hf (mem_support_iff.mp hm)
  rw [Finsupp.weight_apply, Finsupp.sum_fintype _ _ (by simp)] at h
  simp only [Pi.one_apply, smul_eq_mul, mul_one] at h
  rw [Fintype.sum_sigma, Fintype.sum_eq_single k
    (fun k' hk' => absurd ((hK k').trans (hK k).symm) hk')] at h
  exact h

theorem aeval_homog (hK : ∀ k, k = k₀) {w : (Σ k, ι k) → Φ'} {c : ∀ k, ι k} (hc : w ⟨k₀, c k₀⟩ ≠ 0)
    {g : MRingOver Φ ι} {n : ℕ} (hg : g.IsHomogeneous n) :
    aeval (fun p => w p / w ⟨k₀, c k₀⟩) g * w ⟨k₀, c k₀⟩ ^ n = aeval w g := by
  classical
  have hz : ∀ k, w ⟨k, c k⟩ ≠ 0 := fun k => by obtain rfl := hK k; exact hc
  have e : (fun p : Σ k, ι k => w p / w ⟨k₀, c k₀⟩) = Inter.ChartRankAdjoin.affCoord w c := by
    funext ⟨k, i⟩; obtain rfl := hK k; rfl
  have h := Inter.ChartRankAdjoin.aeval_mul_of_isMultiHomog hz (isMultiHomog_of_isHomogeneous hK hg)
  rwa [Fintype.prod_eq_single k₀ (fun k hk => absurd (hK k) hk), ← e] at h

theorem ringKrullDim_adjoin_eq_one {σ : Type} (w : σ → Φ') (s : Set Φ') (x : Φ')
    [Module.Finite Φ (Algebra.adjoin Φ s)] (htr : Transcendental (Algebra.adjoin Φ s) x)
    (hx : x ∈ Algebra.adjoin Φ (Set.range w)) (hs : Set.range w ⊆ Algebra.adjoin Φ (s ∪ {x})) :
    ringKrullDim (Algebra.adjoin Φ (Set.range w)) = 1 := by
  have hAB : Algebra.adjoin Φ (Set.range w) ≤ (Algebra.adjoin (Algebra.adjoin Φ s) {x}).restrictScalars Φ := by
    rw [← Algebra.adjoin_union_eq_adjoin_adjoin]; exact Algebra.adjoin_le hs
  let _ : Algebra (Algebra.adjoin Φ (Set.range w)) ((Algebra.adjoin (Algebra.adjoin Φ s) {x}).restrictScalars Φ) :=
    (Subalgebra.inclusion hAB).toRingHom.toAlgebra
  let f : (Algebra.adjoin (Algebra.adjoin Φ s) {x}).restrictScalars Φ →ₐ[Algebra.adjoin Φ (Set.range w)] Φ' :=
    { ((Algebra.adjoin (Algebra.adjoin Φ s) {x}).restrictScalars Φ).val.toRingHom with commutes' := fun _ => rfl }
  have hint : Algebra.IsIntegral (Algebra.adjoin Φ (Set.range w))
      ((Algebra.adjoin (Algebra.adjoin Φ s) {x}).restrictScalars Φ) := ⟨fun b => by
    refine (isIntegral_algHom_iff f Subtype.val_injective).mp ?_
    have hb : (b : Φ') ∈ Algebra.adjoin Φ (s ∪ {x}) := by
      rw [Algebra.adjoin_union_eq_adjoin_adjoin]; exact b.2
    refine (Algebra.adjoin_le (S := (integralClosure (Algebra.adjoin Φ (Set.range w)) Φ').restrictScalars Φ) ?_) hb
    rintro y (hy | hy)
    · exact ((IsIntegral.of_finite Φ (⟨y, Algebra.subset_adjoin hy⟩ : Algebra.adjoin Φ s)).map
        (Algebra.adjoin Φ s).val).tower_top
    · rw [Set.mem_singleton_iff.mp hy]
      exact isIntegral_algebraMap (x := (⟨x, hx⟩ : Algebra.adjoin Φ (Set.range w)))⟩
  have : IsArtinianRing (Algebra.adjoin Φ s) := IsArtinianRing.of_finite Φ _
  have : IsNoetherianRing (Algebra.adjoin Φ s) := IsNoetherianRing.of_finite Φ _
  rw [← GroundTheory.Arith.Toric.ringKrullDim_eq_of_isIntegral (Subalgebra.inclusion_injective hAB)]
  change ringKrullDim (Algebra.adjoin (Algebra.adjoin Φ s) {x}) = 1
  rw [← ringKrullDim_eq_of_ringEquiv (Polynomial.algEquivOfTranscendental (s := x) (h := htr)).toRingEquiv,
    Polynomial.ringKrullDim_of_isNoetherianRing,
    ringKrullDim_eq_zero_of_isField (IsArtinianRing.isField_of_isDomain _)]
  rfl

end OneBlockPointDeg


open OneBlockPointDeg in
theorem OneBlockPointDeg.proof : OneBlockPointDeg.Statement := by
  classical
  intro Φ Φ' _ _ _ K _ ι _ k₀ hK w c hc hfin htr
  set r : (Σ k, ι k) → Φ' := fun p => w p / w ⟨k₀, c k₀⟩ with hr
  set L := Algebra.adjoin Φ (Set.range r) with hL
  have hz : ∀ k, w ⟨k, c k⟩ ≠ 0 := fun k => by obtain rfl := hK k; exact hc
  have hcard : Fintype.card K = 1 := Fintype.card_eq_one_iff.mpr ⟨k₀, hK⟩
  have hrL : ∀ p, r p ∈ L := fun p => Algebra.subset_adjoin ⟨p, rfl⟩

  have hcomp : ∀ f ∈ RingHom.ker (aeval w : MRingOver Φ ι →ₐ[Φ] Φ'), ∀ n,
      homogeneousComponent n f ∈ RingHom.ker (aeval w : MRingOver Φ ι →ₐ[Φ] Φ') := by
    intro f hf n
    have hmem : ∀ g : MRingOver Φ ι, aeval r g ∈ L := fun g => by
      rw [hL, ← aeval_range]; exact AlgHom.mem_range_self _ g
    let P : Polynomial L := ∑ i ∈ Finset.range (f.totalDegree + 1),
      Polynomial.monomial i ⟨aeval r (homogeneousComponent i f), hmem _⟩
    have hP : Polynomial.aeval (w ⟨k₀, c k₀⟩) P = 0 := by
      have h0 := RingHom.mem_ker.mp hf
      set_option synthInstance.maxHeartbeats 100000 in
        rw [← sum_homogeneousComponent f, map_sum] at h0
      set_option synthInstance.maxHeartbeats 100000 in
        rw [← h0, map_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [Polynomial.aeval_monomial, ← aeval_homog hK hc (homogeneousComponent_isHomogeneous i f)]
      rfl
    have hP0 := (transcendental_iff.mp htr) P hP
    rw [RingHom.mem_ker, ← aeval_homog hK hc (homogeneousComponent_isHomogeneous n f)]
    by_cases hn : n < f.totalDegree + 1
    · have h1 := congrArg (fun q : Polynomial L => q.coeff n) hP0
      simp only [P, Polynomial.finsetSum_coeff, Polynomial.coeff_monomial_apply, Finset.sum_ite_eq',
        Finset.mem_range, hn, if_true, Polynomial.coeff_zero] at h1
      rw [show aeval r (homogeneousComponent n f) = ((⟨_, hmem _⟩ : L) : Φ') from rfl, h1]
      simp
    · rw [homogeneousComponent_eq_zero (φ := f) (n := n) (by omega)]; simp
  have hchart : IsChart (RingHom.ker (aeval w : MRingOver Φ ι →ₐ[Φ] Φ')) c := fun k => by
    rw [RingHom.mem_ker, aeval_X]; exact hz k

  have hhom : IsMultiHomogIdeal (RingHom.ker (aeval w : MRingOver Φ ι →ₐ[Φ] Φ')) := by
    refine ⟨{g | g ∈ RingHom.ker (aeval w : MRingOver Φ ι →ₐ[Φ] Φ') ∧ ∃ a, IsMultiHomog g a}, fun g hg => hg.2,
      le_antisymm (fun f hf => ?_)
      (Ideal.span_le.mpr fun g hg => hg.1)⟩
    rw [← sum_homogeneousComponent f]
    exact Ideal.sum_mem _ fun i _ => Ideal.subset_span
      ⟨hcomp f hf i, _, isMultiHomog_of_isHomogeneous hK (homogeneousComponent_isHomogeneous i f)⟩
  refine ⟨⟨⟨RingHom.ker_isPrime _, hhom, fun k => ⟨c k, hchart k⟩⟩, ?_⟩, hchart, ?_⟩
  ·
    have hs : Set.range w ⊆ Algebra.adjoin Φ (Set.range r ∪ {w ⟨k₀, c k₀⟩}) := by
      rintro _ ⟨p, rfl⟩
      rw [show w p = r p * w ⟨k₀, c k₀⟩ from (div_mul_cancel₀ _ hc).symm]
      exact Subalgebra.mul_mem _ (Algebra.subset_adjoin (Or.inl ⟨p, rfl⟩))
        (Algebra.subset_adjoin (Or.inr rfl))
    rw [ringKrullDim_eq_of_ringEquiv (Ideal.quotientKerEquivRange (aeval w : MRingOver Φ ι →ₐ[Φ] Φ')).toRingEquiv,
      aeval_range, ringKrullDim_adjoin_eq_one w (Set.range r) _ htr (Algebra.subset_adjoin ⟨_, rfl⟩) hs, hcard]
    rfl
  ·
    have halg : ∀ x ∈ Set.range r, IsAlgebraic Φ x := by
      rintro _ ⟨p, rfl⟩
      exact (IsAlgebraic.of_finite Φ (⟨r p, hrL p⟩ : L)).algHom L.val
    have e : (fun q : Σ k, ι k => w q / w ⟨q.1, c q.1⟩) = r := by
      funext ⟨k, i⟩; obtain rfl := hK k; rfl
    rw [Inter.ChartRankAdjoin.proof K ι Φ Φ' w c hz hhom, e,
      ← IntermediateField.finrank_eq_finrank_subalgebra,
      IntermediateField.adjoin_toSubalgebra_of_isAlgebraic halg]

end

end GroundTheory.Heights₂.Heights
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.HeightKernels.PVertPointInj
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open ReciprocityTheory.ChartRestriction.G.Geo MvPolynomial NumberField

namespace VerticalPointInjective

theorem coord_ne_zero {T : Type} [Fintype T] {K' : Type} [Field K'] (y : (Σ _ : Unit, T) → K') (t : T)
    (ht : (X ⟨(), t⟩ : MRing (fun _ : Unit => T)) ∉ mCoordIdeal y) : y ⟨(), t⟩ ≠ 0 := by
  intro h0
  apply ht
  simp [mCoordIdeal, mConeMap, RingHom.mem_ker, h0]

theorem isMultiHomogIdeal_of_mem_divSupp {T : Type} [Fintype T] {K' : Type} [Field K']
    (y : (Σ _ : Unit, T) → K') (s : MRing (fun _ : Unit => T)) (hA : IsArithVar (mCoordIdeal y) 1)
    (hs : IsMultiHomog s (fun _ => 1)) {W : Ideal (MRing (fun _ : Unit => T))}
    (hW : W ∈ divSupp (mCoordIdeal y) s) : IsMultiHomogIdeal W := by
  have hP : NumbersDVR.IsMultiHomogIdeal (mCoordIdeal y) :=
    (Bridge.isMultiHomogIdeal_iff _).2 hA.2.1.2.1
  have hJ := NumbersDVR.SupSpanMultiHomog.full.{0} ℤ Unit (fun _ => T) (mCoordIdeal y) s (fun _ => 1) hP
    ((Bridge.isMultiHomog_iff s _).2 hs)
  exact (Bridge.isMultiHomogIdeal_iff _).1
    (NumbersDVR.MinimalPrimeMultiHomog.full.{0} ℤ Unit (fun _ => T) _ W hJ hW.1)

end VerticalPointInjective


open VerticalPointInjective in
theorem VertPointInj.proof (hCh : VertPointChart.Statement) : VertPointInj.Statement := by
  intro T _ K' _ _ y s hA hs hsP W hW W' hW' hWW'
  obtain ⟨t, ht⟩ := hW.2 ()
  obtain ⟨t', ht'⟩ := hW'.2 ()
  have hyt : y ⟨(), t⟩ ≠ 0 :=
    VerticalPointInjective.coord_ne_zero y t fun h => ht (le_sup_left.trans hW.1.1.2 h)
  obtain ⟨hmax, hrat, hform⟩ := hCh T K' y s hA hs hsP W hW t ht
  obtain ⟨-, -, hform'⟩ := hCh T K' y s hA hs hsP W' hW' t' ht'
  obtain ⟨a', b', hb', hab'⟩ := hrat t'
  have hab'' : (b' : K') * y ⟨(), t'⟩ = a' * y ⟨(), t⟩ := by
    rw [← hab']; field_simp
  have hle : W' ≤ W := by
    obtain ⟨S, hS, hSeq⟩ := VerticalPointInjective.isMultiHomogIdeal_of_mem_divSupp y s hA hs hW'
    rw [hSeq, Ideal.span_le]
    intro g hg
    obtain ⟨e, he⟩ := hS g hg
    have he' : IsMultiHomog g (fun _ => e ()) := by
      have : e = fun _ => e () := funext fun u => by cases u; rfl
      rwa [this] at he
    obtain ⟨a, b, ha, hb, habg⟩ := (hform' (e ()) g he').1 (hSeq ▸ Ideal.subset_span hg)
    rw [← hWW'] at ha hb
    refine (hform (e ()) g he').2 ⟨a * a' ^ e (), b' ^ e () * b, Ideal.mul_mem_right _ _ ha, ?_, ?_⟩
    · intro h
      rcases hmax.isPrime.mem_or_mem h with h | h
      · exact hb' (hmax.isPrime.mem_of_pow_mem _ h)
      · exact hb h
    · push_cast
      calc (b' : K') ^ e () * b * aeval y g = a * ((b' : K') * y ⟨(), t'⟩) ^ e () := by
            rw [mul_assoc, habg]; ring
        _ = _ := by rw [hab'']; ring
  exact le_antisymm (hW.1.2 ⟨hW'.1.1.1, hW'.1.1.2⟩ hle) hle

end GroundTheory.Heights₂.Heights
end

