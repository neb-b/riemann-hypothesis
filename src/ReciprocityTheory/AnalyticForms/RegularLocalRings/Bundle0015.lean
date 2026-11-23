module

public import ReciprocityTheory.AnalyticForms.RegularLocalRings.ExistsClosedOfChartIdeal
public import ReciprocityTheory.AnalyticForms.RegularLocalRings.Bundle0006
public import ReciprocityTheory.AnalyticForms.RegularLocalRings.Bundle0009
public import ReciprocityTheory.AnalyticForms.RegularLocalRings.Bundle0014

@[expose] public section

-- bundled from ReciprocityTheory.AnalyticForms.RegularLocalRings.NeZeroOfSpanEqMaximalIdeal
section
namespace ReciprocityTheory.AnForm.R

open MvPolynomial AlgebraicGeometry CategoryTheory IsLocalRing

variable {K : Type} [Fintype K] [Nonempty K] {ι : K → Type} [∀ k, Fintype (ι k)]
variable {P D : Ideal (MvPolynomial (Σ k, ι k) ℂ)} {hP : IsMultiHomogIdeal P}

theorem ne_zero_of_span_eq_maximalIdeal {R : Type*} [CommRing R] [IsRegularLocalRing R] {d : ℕ}
    (hd : ringKrullDim R = d) (v : Fin d → R) (hv : Ideal.span (Set.range v) = maximalIdeal R)
    (l : Fin d) : v l ≠ 0 := by
  intro h0
  have hfin : (Set.range v \ {0}).Finite := (Set.finite_range v).sdiff
  have hncard : (Set.range v \ {0}).ncard < d := by
    have h1 : (Set.range v \ {0}).ncard < (Set.range v).ncard :=
      Set.ncard_sdiff_singleton_lt_of_mem ⟨l, h0⟩ (Set.finite_range v)
    have h2 : (Set.range v).ncard ≤ d := by
      calc (Set.range v).ncard ≤ (Set.univ : Set (Fin d)).ncard := by
            rw [← Set.image_univ]; exact Set.ncard_image_le (Set.finite_univ)
        _ = d := by simp
    omega
  have hspan : Ideal.span (Set.range v \ {0}) = maximalIdeal R := by
    rw [Ideal.span_sdiff_singleton_zero, hv]
  have hle : (maximalIdeal R).spanFinrank ≤ (Set.range v \ {0}).ncard := by
    rw [← hspan]; exact Submodule.spanFinrank_span_le_ncard_of_finite hfin
  have hdim := ringKrullDim_le_spanFinrank_maximalIdeal R
  rw [hd] at hdim
  have : (d : WithBot ℕ∞) ≤ ((Set.range v \ {0}).ncard : WithBot ℕ∞) :=
    hdim.trans (by exact_mod_cast hle)
  have := (Nat.cast_le (α := WithBot ℕ∞)).mp this
  omega

theorem WData.exists_closed_off (w : WData P D hP) (Q : AffPres (w.π ≫ toSpecC hP)) (x : w.M) (hxV : x.1 ∈ Q.V)
    (𝔮 : Ideal (MvPolynomial (Fin Q.n) ℂ)) (h𝔮min : 𝔮 ∈ Q.K.minimalPrimes)
    (h𝔮x : 𝔮 ≤ ptIdeal (Q.coord x.1 hxV)) (G : MvPolynomial (Fin Q.n) ℂ)
    (hG : eval (Q.coord x.1 hxV) G ≠ 0) :
    ∃ x' : w.M, ∃ hx' : x'.1 ∈ Q.V,
      𝔮 ≤ ptIdeal (Q.coord x'.1 hx') ∧
        w.π.base x'.1 ∉ (projB P D hP : Set (projX P hP)) ∧ eval (Q.coord x'.1 hx') G ≠ 0 := by
  generalize hp : Q.coord x.1 hxV = p at h𝔮x hG
  have := w.regular x.1
  haveI hregL : IsRegularLocalRing (locRing Q.K p) := by
    rw [← hp]; exact (Q.isRegularLocalRing_stalk_iff x.1 hxV x.2).mp (w.regular x.1)
  haveI : IsDomain (locRing Q.K p) := ReciprocityTheory.CA.AB.RegA.IsRegularLocalRing.isDomain _
  set d := (maximalIdeal (w.W.presheaf.stalk x.1)).spanFinrank with hdd
  have hd : ringKrullDim (w.W.presheaf.stalk x.1) = d :=
    (IsRegularLocalRing.spanFinrank_maximalIdeal).symm
  obtain ⟨S, -, -⟩ := exists_sncData w.snc_Zb Q w.compEquiv d x.1 hxV x.2 hd
  rw [hp] at S
  have hdL : ringKrullDim (locRing Q.K p) = d := by
    rw [← hp, ← Q.ringKrullDim_stalk x.1 hxV x.2]; exact hd
  have hmax : Ideal.map (algebraMap _ (locRing Q.K p)) (ptIdeal p) = maximalIdeal (locRing Q.K p) := by
    subst hp
    rw [← Q.map_maximalIdeal_stalk x.1 hxV x.2]; exact map_ringEquiv_maximalIdeal _

  set 𝔮' := RingHom.ker (algebraMap (MvPolynomial (Fin Q.n) ℂ) (locRing Q.K p)) with h𝔮'
  have h𝔮'prime : 𝔮'.IsPrime := RingHom.ker_isPrime _
  have hK𝔮' : Q.K ≤ 𝔮' := by
    intro f hf
    rw [h𝔮', RingHom.mem_ker, IsScalarTower.algebraMap_apply (MvPolynomial (Fin Q.n) ℂ) (locPt p),
      Ideal.Quotient.algebraMap_eq]
    exact Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_map_of_mem _ hf)
  have h𝔮'p : 𝔮' ≤ ptIdeal p := by
    intro f hf
    by_contra hfp
    rw [h𝔮', RingHom.mem_ker, IsScalarTower.algebraMap_apply (MvPolynomial (Fin Q.n) ℂ) (locPt p),
      Ideal.Quotient.algebraMap_eq] at hf
    have hu : IsUnit (algebraMap (MvPolynomial (Fin Q.n) ℂ) (locPt p) f) :=
      IsLocalization.map_units (locPt p) (⟨f, hfp⟩ : (ptIdeal p).primeCompl)
    have := (hu.map (Ideal.Quotient.mk (Ideal.map (algebraMap _ (locPt p)) Q.K))).ne_zero
    exact this hf
  have h𝔮𝔮' : 𝔮 ≤ 𝔮' := by
    obtain ⟨Q', hQ'min, hQ'le⟩ := Ideal.exists_minimalPrimes_le hK𝔮'
    obtain ⟨q0, -, -, hu, -⟩ := regular_point_unique_minimalPrime Q.K p
    rw [hu 𝔮 h𝔮min h𝔮x, ← hu Q' hQ'min (hQ'le.trans h𝔮'p)]
    exact hQ'le
  have h𝔮prime : 𝔮.IsPrime := h𝔮min.1.1
  set F := S.h * ∏ l ∈ S.J, S.r l with hF
  have hFbd : F ∈ Q.bdIdeal w.Zb := S.mem_bd
  have hFq : F ∉ 𝔮 := by
    intro hmem
    rcases h𝔮prime.mem_or_mem hmem with hh | hprod
    · exact S.eval_h (by simpa [ptIdeal, RingHom.mem_ker] using h𝔮x hh)
    · haveI := h𝔮prime
      obtain ⟨l, -, hl⟩ := Ideal.IsPrime.prod_mem_iff.mp hprod
      have h0 : algebraMap _ (locRing Q.K p) (S.r l) = 0 := h𝔮𝔮' hl
      exact ne_zero_of_span_eq_maximalIdeal hdL (fun l => algebraMap _ (locRing Q.K p) (S.r l))
        (S.span_eq.trans hmax) l h0

  have hGq : G ∉ 𝔮 := fun hG𝔮 => hG (by simpa [ptIdeal, RingHom.mem_ker] using h𝔮x hG𝔮)
  have hFGq : F * G ∉ 𝔮 := fun hm => (h𝔮prime.mem_or_mem hm).elim hFq hGq
  obtain ⟨y, hy𝔮, hyFG⟩ : ∃ y : Fin Q.n → ℂ, (∀ f ∈ 𝔮, eval y f = 0) ∧ eval y (F * G) ≠ 0 := by
    by_contra hno
    push Not at hno
    apply hFGq
    have : F * G ∈ vanishingIdeal ℂ (zeroLocus ℂ 𝔮) := by
      rw [mem_vanishingIdeal_iff]
      intro y hy
      exact hno y (fun f hf => by simpa using hy f hf)
    rwa [vanishingIdeal_zeroLocus_eq_radical, h𝔮prime.radical] at this
  obtain ⟨x'', ⟨hx''V, hcl, hco⟩, -⟩ :=
    Q.existsUnique_closed_coord y (fun f hf => hy𝔮 f (h𝔮min.1.2 hf))
  have hyF : eval y F ≠ 0 := fun h0 => hyFG (by rw [eval_mul, h0, zero_mul])
  have hyG : eval y G ≠ 0 := fun h0 => hyFG (by rw [eval_mul, h0, mul_zero])
  refine ⟨⟨x'', hcl⟩, hx''V, ?_, ?_, by rw [hco]; exact hyG⟩
  · intro f hf
    show f ∈ ptIdeal (Q.coord x'' hx''V)
    rw [hco, ptIdeal, RingHom.mem_ker]
    exact hy𝔮 f hf
  · intro hB
    have hsupp : x'' ∈ (w.Zb.support : Set w.W) := by
      rw [w.support_Zb]; exact hB
    have := (Q.zero_bdIdeal_iff w.Zb x'' hx''V hcl).mpr hsupp F hFbd
    rw [hco] at this
    exact hyF this


set_option backward.isDefEq.respectTransparency.types false in
theorem WData.ringKrullDim_stalk_off (w : WData P D hP) (e : ℕ)
    (hdim : ∀ (p : (k : K) → ι k) (z : (Σ k, ι k) → ℂ), (∀ h ∈ chartIdeal P p, eval z h = 0) →
      ringKrullDim (chartLocRing P p z) = e)
    (y : w.M) (hy : w.π.base y.1 ∉ (projB P D hP : Set (projX P hP))) :
    ringKrullDim (w.W.presheaf.stalk y.1) = e := by
  have := w.lft
  have := w.isIso_off
  have hU : y.1 ∈ w.π ⁻¹ᵁ projBCompl P D hP := hy
  have hiso : IsIso (w.π.stalkMap y.1) := by
    have h := (MorphismProperty.isomorphisms CommRingCat).arrow_mk_iso_iff
      (morphismRestrictStalkMap w.π (projBCompl P D hP) ⟨y.1, hU⟩)
    haveI hoi : IsOpenImmersion (w.π ∣_ projBCompl P D hP) := IsOpenImmersion.of_isIso _
    have h2 : IsIso ((w.π ∣_ projBCompl P D hP).stalkMap ⟨y.1, hU⟩) := inferInstance
    exact h.mp h2
  rw [← ringKrullDim_eq_of_ringEquiv (asIso (w.π.stalkMap y.1)).commRingCatIsoToRingEquiv]
  have hcl : IsClosed ({w.π.base y.1} : Set (projX P hP)) :=
    (val_comp (w.π ≫ toSpecC hP) (toSpecC hP) w.π rfl (U := ⊤) (V := ⊤) (by simp) 0 y.1 trivial
      y.2).1
  obtain ⟨p, hp⟩ := chartOpen_cover hP (w.π.base y.1)
  obtain ⟨z, hz, -, ⟨ψ⟩⟩ := exists_closedPoint_stalk hP p _ hp hcl
  rw [ringKrullDim_eq_of_ringEquiv ψ]
  exact hdim p z hz

theorem WData.ringKrullDim_stalk (w : WData P D hP) (e : ℕ) (hD : IsMultiHomogIdeal D)
    (hcomp : ∀ Q ∈ P.minimalPrimes, IsRelevant Q → ¬ D ≤ Q)
    (hdim : ∀ (p : (k : K) → ι k) (z : (Σ k, ι k) → ℂ), (∀ h ∈ chartIdeal P p, eval z h = 0) →
      ringKrullDim (chartLocRing P p z) = e) :
    ∀ x : w.M, ringKrullDim (w.W.presheaf.stalk x.1) = e := by

  have offB : ∀ y : w.M, w.π.base y.1 ∉ (projB P D hP : Set (projX P hP)) →
      ringKrullDim (w.W.presheaf.stalk y.1) = e :=
    w.ringKrullDim_stalk_off e hdim
  intro x
  obtain ⟨c, hc⟩ := w.cover x
  have hxV : x.1 ∈ (w.pres c.1 c.2).V := hc
  rw [(w.pres c.1 c.2).ringKrullDim_stalk x.1 hxV x.2]
  have := ((w.pres c.1 c.2).isRegularLocalRing_stalk_iff x.1 hxV x.2).mp (w.regular x.1)
  obtain ⟨𝔮, h𝔮min, h𝔮x, -, -⟩ :=
    regular_point_unique_minimalPrime (w.pres c.1 c.2).K ((w.pres c.1 c.2).coord x.1 hxV)

  obtain ⟨x', hx'V, h𝔮x', hx'B, -⟩ :=
    w.exists_closed_off (w.pres c.1 c.2) x hxV 𝔮 h𝔮min h𝔮x 1 (by simp)
  have := ((w.pres c.1 c.2).isRegularLocalRing_stalk_iff x'.1 hx'V x'.2).mp (w.regular x'.1)
  rw [ringKrullDim_locRing_eq_of_minimalPrime (w.pres c.1 c.2).K _ _ 𝔮 h𝔮min h𝔮x h𝔮x',
    ← (w.pres c.1 c.2).ringKrullDim_stalk x'.1 hx'V x'.2]
  exact offB x' hx'B

theorem WData.dim_coord (w : WData P D hP) {e : ℕ}
    (he : ∀ x : w.M, ringKrullDim (w.W.presheaf.stalk x.1) = e) (c : w.Idx) (x : w.M)
    (hx : x ∈ w.src c) : ringKrullDim (locRing (w.pres c.1 c.2).K (w.coord c x)) = e := by
  have h1 : w.coord c x = (w.pres c.1 c.2).coord x.1 hx := by
    unfold WData.coord
    exact dif_pos hx
  rw [h1, ← (w.pres c.1 c.2).ringKrullDim_stalk x.1 hx x.2]
  exact he x

end ReciprocityTheory.AnForm.R
end

-- bundled from ReciprocityTheory.AnalyticForms.RegularLocalRings.NormEvalLeOfVarsSubset
section
namespace ReciprocityTheory.AnForm.R

open MvPolynomial AlgebraicGeometry CategoryTheory

noncomputable section

theorem norm_eval_le_of_vars_subset {n : ℕ} (F : MvPolynomial (Fin n) ℂ) (S : Finset (Fin n))
    (hS : F.vars ⊆ S) (y : Fin n → ℂ) (hy : ∀ i ∈ S, ‖y i‖ ≤ 1) :
    ‖eval y F‖ ≤ ∑ m ∈ F.support, ‖F.coeff m‖ := by
  rw [MvPolynomial.eval_eq']
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun m hm => ?_)
  rw [norm_mul]
  have h1 : ‖∏ i, y i ^ m i‖ ≤ 1 := by
    rw [norm_prod]
    refine Finset.prod_le_one₀ (fun i _ => norm_nonneg _) fun i _ => ?_
    rw [norm_pow]
    by_cases h : m i = 0
    · simp [h]
    · refine pow_le_one₀ (norm_nonneg _) (hy i (hS ?_))
      rw [MvPolynomial.mem_vars_iff_mem_support]
      exact ⟨m, hm, Finsupp.mem_support_iff.mpr h⟩
  calc ‖F.coeff m‖ * ‖∏ i, y i ^ m i‖ ≤ ‖F.coeff m‖ * 1 :=
        mul_le_mul_of_nonneg_left h1 (norm_nonneg _)
    _ = ‖F.coeff m‖ := mul_one _

variable {K : Type} [Fintype K] [Nonempty K] {ι : K → Type} [∀ k, Fintype (ι k)]
variable {P D : Ideal (MvPolynomial (Σ k, ι k) ℂ)} {hP : IsMultiHomogIdeal P}

namespace WData

variable (w : WData P D hP)

def cptPiece (c : w.Idx) : Set w.M :=
  {x | x ∈ w.src c ∧ (∀ q, ‖w.coord c x (w.yq c.1 c.2 q)‖ ≤ 1) ∧
    ∀ k, ‖w.coord c x (w.yt c.1 c.2 k)‖ ≤ 1}

theorem isCompact_cptPiece (c : w.Idx) : IsCompact (w.cptPiece c) := by
  let S : Finset (Fin (w.pres c.1 c.2).n) :=
    Finset.univ.image (w.yq c.1 c.2) ∪ Finset.univ.image (w.yt c.1 c.2)
  choose F hFv hFK using w.gen c.1 c.2
  let B : Set (Fin (w.pres c.1 c.2).n → ℂ) :=
    (⋂ h ∈ ((w.pres c.1 c.2).K : Set (MvPolynomial (Fin (w.pres c.1 c.2).n) ℂ)), {y | eval y h = 0}) ∩
      ((⋂ q, {y | ‖y (w.yq c.1 c.2 q)‖ ≤ 1}) ∩ ⋂ k, {y | ‖y (w.yt c.1 c.2 k)‖ ≤ 1})
  have hBc : IsClosed B :=
    (isClosed_biInter fun h _ => isClosed_eq (MvPolynomial.continuous_eval h) continuous_const).inter
      ((isClosed_iInter fun q =>
        isClosed_le (continuous_norm.comp (continuous_apply _)) continuous_const).inter
      (isClosed_iInter fun k =>
        isClosed_le (continuous_norm.comp (continuous_apply _)) continuous_const))
  have hmemB : ∀ y, y ∈ B ↔ (∀ h ∈ (w.pres c.1 c.2).K, eval y h = 0) ∧
      (∀ q, ‖y (w.yq c.1 c.2 q)‖ ≤ 1) ∧ ∀ k, ‖y (w.yt c.1 c.2 k)‖ ≤ 1 := by
    intro y
    simp only [B, Set.mem_inter_iff, Set.mem_iInter, Set.mem_setOf_eq, SetLike.mem_coe]
  have hS : ∀ y ∈ B, ∀ i ∈ S, ‖y i‖ ≤ 1 := by
    intro y hy i hi
    rw [hmemB] at hy
    rcases Finset.mem_union.mp hi with h | h
    · obtain ⟨a, -, rfl⟩ := Finset.mem_image.mp h
      exact hy.2.1 a
    · obtain ⟨a, -, rfl⟩ := Finset.mem_image.mp h
      exact hy.2.2 a
  have hBsub : B ⊆ Set.univ.pi fun l =>
      Metric.closedBall (0 : ℂ) (∑ m ∈ (F l).support, ‖(F l).coeff m‖) := by
    intro y hy
    have hy' := (hmemB y).mp hy
    refine Set.mem_univ_pi.mpr fun l => ?_
    rw [mem_closedBall_zero_iff]
    have h1 : y l = eval y (F l) := by
      have h2 := hy'.1 _ (hFK l)
      rw [map_sub, eval_X, sub_eq_zero] at h2
      exact h2
    rw [h1]
    exact norm_eval_le_of_vars_subset (F l) S (hFv l) y (hS y hy)
  have hBk : IsCompact B :=
    (isCompact_univ_pi fun l => isCompact_closedBall _ _).of_isClosed_subset hBc hBsub
  have hrange : B ⊆ Set.range (fun y : w.src c => w.coord c y) := by
    intro y hy
    have h3 : y ∈ w.coord c '' w.src c := by
      rw [w.image c]
      exact ((hmemB y).mp hy).1
    obtain ⟨x, hx, rfl⟩ := h3
    exact ⟨⟨x, hx⟩, rfl⟩
  have hpre := (w.isEmbedding c).isInducing.isCompact_preimage' hBk hrange
  have heq : w.cptPiece c = Subtype.val '' ((fun y : w.src c => w.coord c y) ⁻¹' B) := by
    ext x
    constructor
    · rintro ⟨hx, hq, ht⟩
      refine ⟨⟨x, hx⟩, (hmemB _).mpr ⟨?_, hq, ht⟩, rfl⟩
      have h4 : w.coord c x ∈ w.coord c '' w.src c := ⟨x, hx, rfl⟩
      rw [w.image c] at h4
      exact h4
    · rintro ⟨y, hy, rfl⟩
      have hy' := (hmemB _).mp hy
      exact ⟨y.2, hy'.2.1, hy'.2.2⟩
  rw [heq]
  exact hpre.image continuous_subtype_val

theorem exists_cptPiece (x : w.M) : ∃ c, x ∈ w.cptPiece c := by
  obtain ⟨c0, h0⟩ := w.cover x
  have hz := w.lift_mem c0 x h0
  obtain ⟨p, hpnz, hpmax⟩ := exists_chart (fun q => eval (w.coord c0 x) (w.lift c0 q)) hz.1
  have hπ : w.π.base x.1 ∈ (chartOpen hP p).1 := (w.mem_chartOpen_iff c0 x h0 p).mpr hpnz
  have hxp : x.1 ∈ w.π ⁻¹ᵁ (chartOpen hP p).1 := hπ
  rw [← w.iSup_pres p] at hxp
  obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.mp hxp
  have hcl : IsClosed ({x.1} : Set w.W) := x.2
  obtain ⟨τ, hτ⟩ : ∃ τ : Fin (w.m p) → ℂ, ∀ k, τ k = val (w.π ≫ toSpecC hP) (w.t p i k) x.1 hi :=
    ⟨_, fun _ => rfl⟩
  have hτi : τ i = 1 := by
    obtain ⟨φ, hφ⟩ := val_ringHom (w.π ≫ toSpecC hP) _ x.1 hi hcl
    rw [hτ, w.t_self, ← hφ, map_one]
  have : Nonempty (Fin (w.m p)) := ⟨i⟩
  obtain ⟨j, hj⟩ := Finite.exists_max fun k => ‖τ k‖
  have hτj1 : 1 ≤ ‖τ j‖ := by
    have h5 := hj i
    rwa [hτi, norm_one] at h5
  have hpos : 0 < ‖τ j‖ := lt_of_lt_of_le one_pos hτj1
  have hij : x.1 ∈ (w.pres p i).V ⊓ (w.pres p j).V := by
    rw [w.inter p i j]
    refine (w.W.evaluation_ne_zero_iff_mem_basicOpen x.1 hi (w.t p i j)).mp ?_
    rw [Ne, ← val_eq_zero_iff (w.π ≫ toSpecC hP) _ x.1 hi hcl, ← hτ]
    exact norm_pos_iff.mp hpos
  have hjV : x.1 ∈ (w.pres p j).V := hij.2
  have hcoc : ∀ k, val (w.π ≫ toSpecC hP) (w.t p j k) x.1 hjV * τ j = τ k := by
    intro k
    obtain ⟨φ, hφ⟩ := val_ringHom (w.π ≫ toSpecC hP) _ x.1 hij hcl
    have h6 := congrArg φ (w.t_cocycle p i j k)
    rw [map_mul, hφ, hφ, hφ, val_restrict, val_restrict, val_restrict] at h6
    rw [hτ, hτ]
    exact h6
  refine ⟨⟨p, j⟩, hjV, fun q => ?_, fun k => ?_⟩
  · have e1 : w.coord ⟨p, j⟩ x (w.yq p j q) =
        val (w.π ≫ toSpecC hP) ((w.pres p j).secHom (X (w.yq p j q))) x.1 hjV := by
      rw [(w.pres p j).val_secHom x.1 hjV hcl, eval_X, w.coord_of_mem ⟨p, j⟩ x hjV]
    rw [e1, w.sec_yq,
      (val_comp (w.π ≫ toSpecC hP) (toSpecC hP) w.π rfl (w.le_pres p j) (chartCoord hP p q)
        x.1 hjV hcl).2]
    refine (congrArg (fun v => ‖v‖) (w.val_chartCoord c0 x h0 p _ q)).trans_le ?_
    simp only [affCoord, norm_div]
    exact div_le_one_of_le₀ (hpmax q.1 q.2) (norm_nonneg _)
  · have e1 : w.coord ⟨p, j⟩ x (w.yt p j k) = val (w.π ≫ toSpecC hP) (w.t p j k) x.1 hjV := by
      rw [← w.sec_yt p j k, (w.pres p j).val_secHom x.1 hjV hcl, eval_X,
        w.coord_of_mem ⟨p, j⟩ x hjV]
    rw [e1]
    have h7 : ‖val (w.π ≫ toSpecC hP) (w.t p j k) x.1 hjV‖ * ‖τ j‖ = ‖τ k‖ := by
      rw [← norm_mul, hcoc k]
    calc ‖val (w.π ≫ toSpecC hP) (w.t p j k) x.1 hjV‖ = ‖τ k‖ / ‖τ j‖ := by
          rw [← h7, mul_div_cancel_right₀ _ hpos.ne']
      _ ≤ 1 := div_le_one_of_le₀ (hj k) hpos.le

end WData

theorem WData.compactSpace (w : WData P D hP) : CompactSpace w.M := by
  refine isCompact_univ_iff.mp ?_
  have h : (Set.univ : Set w.M) = ⋃ c, w.cptPiece c := by
    ext x
    simp only [Set.mem_univ, Set.mem_iUnion, true_iff]
    exact w.exists_cptPiece x
  rw [h]
  exact isCompact_iUnion fun c => w.isCompact_cptPiece c

end

end ReciprocityTheory.AnForm.R
end

-- bundled from ReciprocityTheory.AnalyticForms.RegularLocalRings.Surj
section
namespace ReciprocityTheory.AnForm.R

open MvPolynomial AlgebraicGeometry CategoryTheory

noncomputable section

variable {K : Type} [Fintype K] [Nonempty K] {ι : K → Type} [∀ k, Fintype (ι k)]
variable {P D : Ideal (MvPolynomial (Σ k, ι k) ℂ)} {hP : IsMultiHomogIdeal P}

namespace WData

variable (w : WData P D hP)

theorem surj' (hD : IsMultiHomogIdeal D) (z : (Σ k, ι k) → ℂ) (hz : z ∈ conePts P)
    (hzD : z ∉ conePts D) :
    ∃ c, ∃ x ∈ w.src c, SameOrbit (fun q => eval (w.coord c x) (w.lift c q)) z := by
  have := w.isIso_off
  obtain ⟨p, hzp, -⟩ := exists_chart z hz.1
  have hzc : ∀ h ∈ chartIdeal P p, eval (affCoord p z) h = 0 :=
    (mem_conePts_iff_chartIdeal hP p z hzp).1 hz
  obtain ⟨y, hy, hyc, hyv⟩ := exists_closed_of_chartIdeal (hP := hP) p (affCoord p z) hzc
  have hyB : y ∈ projBCompl P D hP := by
    intro hB
    have h1 := (mem_projB_iff_val hD p y hy hyc).1 hB
    rw [funext hyv] at h1
    exact hzD ((mem_conePts_iff_affCoord hD p z hzp).2 h1)
  obtain ⟨x, ⟨hxc, -⟩, hxy⟩ := (bijOn_closedPoints_of_isIso (sW := w.π ≫ toSpecC hP)
    (sX := toSpecC hP) w.π rfl (projBCompl P D hP)).2.2 ⟨hyc, hyB⟩
  subst hxy
  have hxp : x ∈ w.π ⁻¹ᵁ (chartOpen hP p).1 := hy
  rw [← w.iSup_pres p] at hxp
  obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.1 hxp
  refine ⟨⟨p, i⟩, ⟨x, hxc⟩, hi, ?_⟩
  have hl : (fun q => eval (w.coord ⟨p, i⟩ ⟨x, hxc⟩) (w.lift ⟨p, i⟩ q)) = affCoord p z := by
    funext q
    rw [w.lift_eval_eq_val ⟨p, i⟩ ⟨x, hxc⟩ hi q]
    exact hyv q
  rw [hl]
  exact sameOrbit_symm' (sameOrbit_affCoord p z hzp)

theorem inj' (hD : IsMultiHomogIdeal D) (c c' : w.Idx) (x : w.M) (hx : x ∈ w.src c) (x' : w.M)
    (hx' : x' ∈ w.src c') (hxD : (fun q => eval (w.coord c x) (w.lift c q)) ∉ conePts D)
    (ho : SameOrbit (fun q => eval (w.coord c x) (w.lift c q))
      (fun q => eval (w.coord c' x') (w.lift c' q))) : x = x' := by
  have := w.isIso_off
  obtain ⟨a, ha0, ha⟩ := ho
  have hxc : w.π.base x.1 ∈ (chartOpen hP c.1).1 := w.le_pres c.1 c.2 hx
  have hone : ∀ k, eval (w.coord c x) (w.lift c ⟨k, c.1 k⟩) = 1 := fun k => by simp [lift]
  have hx'c : ∀ k, eval (w.coord c' x') (w.lift c' ⟨k, c.1 k⟩) ≠ 0 := by
    intro k h0
    have := congrFun ha ⟨k, c.1 k⟩
    simp only [hone k, h0, mul_zero] at this
    exact one_ne_zero this
  have hpx' : w.π.base x'.1 ∈ (chartOpen hP c.1).1 := (w.mem_chartOpen_iff c' x' hx' c.1).2 hx'c
  have heq : w.π.base x.1 = w.π.base x'.1 := by
    refine eq_of_val_chartCoord c.1 _ _ hxc hpx' (w.isClosed_image c x hx)
      (w.isClosed_image c' x' hx') fun q => ?_
    rw [w.val_chartCoord c x hx c.1 hxc q, w.val_chartCoord c' x' hx' c.1 hpx' q,
      affCoord_eq_of_sameOrbit c.1 ⟨a, ha0, ha⟩]
  have hxU : w.π.base x.1 ∈ projBCompl P D hP :=
    fun h => hxD ((w.mem_projB_iff_lift hD c x hx).1 h)
  have hbij := bijOn_closedPoints_of_isIso (sW := w.π ≫ toSpecC hP) (sX := toSpecC hP) w.π rfl
    (projBCompl P D hP)
  exact Subtype.ext (hbij.injOn ⟨x.2, hxU⟩ ⟨x'.2, heq ▸ hxU⟩ heq)

end WData

end

end ReciprocityTheory.AnForm.R
end

-- bundled from ReciprocityTheory.AnalyticForms.RegularLocalRings.WeightedSieveThreeParameter
section
namespace ReciprocityTheory.AnForm.R

open MvPolynomial AlgebraicGeometry CategoryTheory

variable {K : Type} [Fintype K] [Nonempty K] {ι : K → Type} [∀ k, Fintype (ι k)]
variable {P D : Ideal (MvPolynomial (Σ k, ι k) ℂ)} {hP : IsMultiHomogIdeal P}

theorem WData.t2Space (w : WData P D hP) : T2Space w.M := by
  refine ⟨fun x y hxy => ?_⟩
  by_cases hcom : ∃ d, x ∈ w.src d ∧ y ∈ w.src d
  · obtain ⟨d, hxd, hyd⟩ := hcom
    have hne : w.coord d x ≠ w.coord d y := by
      intro h
      have h' : (⟨x, hxd⟩ : w.src d) = ⟨y, hyd⟩ := (w.isEmbedding d).injective h
      exact hxy (congrArg Subtype.val h')
    exact sep_of_continuousOn (w.isOpen_alt_bis d) (w.continuousOn_coord d) hxd hyd hne
  push Not at hcom
  obtain ⟨c, hxc⟩ := w.cover x
  obtain ⟨c', hyc'⟩ := w.cover y
  by_cases hblk : ∃ q, w.blk q x ≠ w.blk q y
  · obtain ⟨q, hq⟩ := hblk
    exact sep_of_continuousOn isOpen_univ (w.continuous_blk q).continuousOn trivial trivial hq
  push Not at hblk
  have hy1 : ∀ k, eval (w.coord c' y) (w.lift c' ⟨k, c.1 k⟩) ≠ 0 := by
    intro k
    have h1 : w.blk ⟨k, c.1 k⟩ x ≠ 0 := by
      rw [w.blk_eq _ c x hxc, blkNorm_ne_zero_iff, w.lv_self]
      exact one_ne_zero
    rw [hblk, w.blk_eq _ c' y hyc', blkNorm_ne_zero_iff] at h1
    exact h1
  have hyp : w.π.base y.1 ∈ (chartOpen hP c.1).1 := (w.mem_chartOpen_iff c' y hyc' c.1).mpr hy1
  obtain ⟨j, hyj⟩ : ∃ j, y ∈ w.src ⟨c.1, j⟩ := by
    have h : y.1 ∈ w.π ⁻¹ᵁ (chartOpen hP c.1).1 := hyp
    rw [← w.iSup_pres] at h
    obtain ⟨j, hj⟩ := TopologicalSpace.Opens.mem_iSup.mp h
    exact ⟨j, hj⟩
  by_cases hfib : ∃ l, w.fib c.1 l x ≠ w.fib c.1 l y
  · obtain ⟨l, hl⟩ := hfib
    exact sep_of_continuousOn (w.isOpen_overP c.1) (w.continuousOn_fib c.1 l) ⟨c.2, hxc⟩
      ⟨j, hyj⟩ hl
  push Not at hfib
  have h1 : w.fib c.1 j y ≠ 0 := by
    rw [w.fib_eq c.1 j j y hyj, vecNorm_ne_zero_iff, w.tv_self c.1 j y hyj]
    exact one_ne_zero
  rw [← hfib j, w.fib_eq c.1 j c.2 x hxc, vecNorm_ne_zero_iff, w.tv_ne_zero_iff c.1 c.2 j x hxc] at h1
  exact (hcom _ h1 hyj).elim

end ReciprocityTheory.AnForm.R
end

