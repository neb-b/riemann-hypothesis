module

public import Mathlib
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0023
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0032
public import GroundTheory.ArithmeticGeometry.SchemeCohomology.Bundle0001
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0008
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0027
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StSerreConditions
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0004
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0021
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0033
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0009
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0031

@[expose] public section

-- bundled from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PRegularLocusIdentity
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets

open MvPolynomial Topology Filter

theorem IsRegularPointOf.exists_ball_chart {σ : Type} [Fintype σ] {Y : Set (σ → ℂ)} {z : σ → ℂ}
    (hz : IsRegularPointOf Y z) {W : Set (σ → ℂ)} (hW : W ∈ 𝓝 z) :
    ∃ (d : ℕ) (V : Set (σ → ℂ)) (B : Set (Fin d → ℂ)) (g : (Fin d → ℂ) → σ → ℂ),
      IsOpen V ∧ z ∈ V ∧ V ⊆ W ∧ IsOpen B ∧ IsPreconnected B ∧ AnalyticOnNhd ℂ g B ∧
        Y ∩ V = g '' B := by
  obtain ⟨hzY, d, A, O, V, g, hO, hV, hzV, hg, hAg, hYV⟩ := hz
  have hzO : z ∈ g '' O := by rw [← hYV]; exact ⟨hzY, hzV⟩
  obtain ⟨y₀, hy₀O, rfl⟩ := hzO
  have hN : interior W ∩ V ∈ 𝓝 (g y₀) := inter_mem (interior_mem_nhds.2 hW) (hV.mem_nhds hzV)
  obtain ⟨r, hr, hball⟩ := Metric.mem_nhds_iff.1
    (inter_mem (hO.mem_nhds hy₀O) ((hg y₀ hy₀O).continuousAt.preimage_mem_nhds hN))
  refine ⟨d, V ∩ interior W ∩ A ⁻¹' Metric.ball y₀ r, Metric.ball y₀ r, g,
    (hV.inter isOpen_interior).inter (Metric.isOpen_ball.preimage A.continuous),
    ⟨⟨hzV, mem_interior_iff_mem_nhds.2 hW⟩, ?_⟩, fun x hx => interior_subset hx.1.2,
    Metric.isOpen_ball, (convex_ball y₀ r).isPreconnected, fun y hy => hg y (hball hy).1, ?_⟩
  · show A (g y₀) ∈ Metric.ball y₀ r
    rw [hAg y₀ hy₀O]
    exact Metric.mem_ball_self hr
  · ext x
    constructor
    · rintro ⟨hxY, ⟨hxV, -⟩, hxB⟩
      have hx : x ∈ g '' O := by rw [← hYV]; exact ⟨hxY, hxV⟩
      obtain ⟨y, hyO, rfl⟩ := hx
      have hyB : A (g y) ∈ Metric.ball y₀ r := hxB
      rw [hAg y hyO] at hyB
      exact ⟨y, hyB, rfl⟩
    · rintro ⟨y, hyB, rfl⟩
      have hyO : y ∈ O := (hball hyB).1
      have hyN : g y ∈ interior W ∩ V := (hball hyB).2
      have hgy : g y ∈ Y ∩ V := by rw [hYV]; exact ⟨y, hyO, rfl⟩
      refine ⟨hgy.1, ⟨hyN.2, hyN.1⟩, ?_⟩
      show A (g y) ∈ Metric.ball y₀ r
      rw [hAg y hyO]
      exact hyB

theorem eq_zero_on_chart_of_eventually_eq_zero {σ : Type} [Fintype σ] {Y V : Set (σ → ℂ)} {d : ℕ}
    {B : Set (Fin d → ℂ)} {g : (Fin d → ℂ) → σ → ℂ} (hBo : IsOpen B) (hBc : IsPreconnected B)
    (hg : AnalyticOnNhd ℂ g B) (hYV : Y ∩ V = g '' B) (F : (σ → ℂ) → ℂ) (hF : AnalyticOnNhd ℂ F V)
    (h0 : ∃ y ∈ Y ∩ V, ∀ᶠ u in 𝓝 y, u ∈ Y → F u = 0) : ∀ u ∈ Y ∩ V, F u = 0 := by
  obtain ⟨y, hy, hyF⟩ := h0
  have hgB : ∀ t ∈ B, g t ∈ Y ∩ V := fun t ht => by rw [hYV]; exact ⟨t, ht, rfl⟩
  have hy' : y ∈ g '' B := by rw [← hYV]; exact hy
  obtain ⟨t₀, ht₀, rfl⟩ := hy'
  have hFg : AnalyticOnNhd ℂ (F ∘ g) B := fun t ht => (hF (g t) (hgB t ht).2).comp (hg t ht)
  have hev : F ∘ g =ᶠ[𝓝 t₀] 0 := by
    filter_upwards [(hg t₀ ht₀).continuousAt.tendsto.eventually hyF, hBo.mem_nhds ht₀] with t ht htB
    exact ht (hgB t htB).1
  have hzero := hFg.eqOn_zero_of_preconnected_of_eventuallyEq_zero hBc ht₀ hev
  intro u hu
  have hu' : u ∈ g '' B := by rw [← hYV]; exact hu
  obtain ⟨t, ht, rfl⟩ := hu'
  exact hzero ht

theorem RegularLocusIdentity.proof (hreg : RegularOffHypersurface.Statement) :
    RegularLocusIdentity.Statement := by
  intro σ _ I hI
  obtain ⟨h, hhI, hh⟩ := hreg σ I hI
  refine ⟨h, hhI, fun z hz hhz W hW => ?_⟩
  obtain ⟨d, V, B, g, hVo, hzV, hVW, hBo, hBc, hg, hYV⟩ := (hh z hz hhz).exists_ball_chart hW
  exact ⟨V, hVo, hzV, hVW, fun F hF h0 => eq_zero_on_chart_of_eventually_eq_zero hBo hBc hg hYV F hF h0⟩

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PRegularQuotientIndependent
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets

open IsLocalRing Ideal

theorem RegularQuotientIndependent.proof : RegularQuotientIndependent.Statement := by
  intro S _ _ h
  induction h generalizing S with
  | zero =>
    intro x _ _
    have hr : Set.range x = ∅ := Set.range_eq_empty x
    rw [hr, Ideal.span_empty]
    exact IsRegularLocalRing.of_ringEquiv (RingEquiv.quotientBot S).symm
  | succ h ih =>
    intro x hxm hind
    have hx02 : x 0 ∉ maximalIdeal S ^ 2 := by
      intro hc
      have h1 := hind (Pi.single 0 1) (by simpa [Pi.single_apply] using hc) 0
      simp at h1
    have hne : span {x 0} ≠ ⊤ := ne_top_of_le_ne_top (maximalIdeal.isMaximal S).ne_top
      ((span_singleton_le_iff_mem _).mpr (hxm 0))
    have : Nontrivial (S ⧸ span {x 0}) := Ideal.Quotient.nontrivial_iff.mpr hne
    have : IsLocalRing (S ⧸ span {x 0}) :=
      IsLocalRing.of_surjective' (Ideal.Quotient.mk _) Ideal.Quotient.mk_surjective
    have := (GroundTheory.Arith.SchemeCoh.isRegularLocalRing_quotient (hxm 0) hx02).1
    set f := Ideal.Quotient.mk (span {x 0}) with hf
    have hmax : (maximalIdeal S).map f = maximalIdeal (S ⧸ span {x 0}) :=
      map_maximalIdeal_of_surjective f Ideal.Quotient.mk_surjective
    let y : Fin h → S ⧸ span {x 0} := fun i ↦ f (x i.succ)
    have hy : ∀ i, y i ∈ maximalIdeal (S ⧸ span {x 0}) := fun i ↦
      hmax ▸ Ideal.mem_map_of_mem f (hxm i.succ)
    have hyind : ∀ b : Fin h → S ⧸ span {x 0}, ∑ i, b i * y i ∈ maximalIdeal (S ⧸ span {x 0}) ^ 2 →
        ∀ i, b i ∈ maximalIdeal (S ⧸ span {x 0}) := by
      intro b hb i
      choose a ha using fun i ↦ Ideal.Quotient.mk_surjective (I := span {x 0}) (b i)
      have hsum : ∑ i, b i * y i = f (∑ i, a i * x i.succ) := by
        set_option synthInstance.maxHeartbeats 100000 in
          rw [map_sum]
        exact Finset.sum_congr rfl fun i _ ↦ by simp only [map_mul, ← ha i, hf, y]
      rw [hsum, ← hmax, ← Ideal.map_pow, hf, Ideal.mem_quotient_iff_mem_sup] at hb
      obtain ⟨z, hz, w, hw, hzw⟩ := Submodule.mem_sup.mp hb
      obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton'.mp hw
      have h2 := hind (Fin.cons (-c) a) (by
        rw [Fin.sum_univ_succ]
        simp only [Fin.cons_zero, Fin.cons_succ]
        have : -c * x 0 + ∑ i, a i * x i.succ = z := by rw [← hzw]; ring
        rw [this]; exact hz) i.succ
      simp only [Fin.cons_succ] at h2
      rw [← ha i, ← hmax]
      exact Ideal.mem_map_of_mem _ h2
    have hreg := ih (S ⧸ span {x 0}) y hy hyind
    set J : Ideal S := span (Set.range (fun i : Fin h ↦ x i.succ)) with hJ
    have hspan : span (Set.range y) = J.map f := by
      rw [hJ, Ideal.map_span, ← Set.range_comp]
      rfl
    have hsup : span {x 0} ⊔ J = span (Set.range x) := by
      rw [hJ, ← Ideal.span_union]
      congr 1
      ext s
      simp [Fin.exists_fin_succ, eq_comm]
    exact IsRegularLocalRing.of_ringEquiv (((Ideal.quotEquivOfEq hspan).trans
      (DoubleQuot.quotQuotEquivQuotSup (span {x 0}) J)).trans (Ideal.quotEquivOfEq hsup))

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PRueckertNullstellensatz
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets

open Topology Filter

namespace RueckertNullstellensatz

variable {σ : Type} [Fintype σ] {w : σ → ℂ}

theorem exists_of_mem_holGermIdeal {k : ℕ} (p : Fin k → (σ → ℂ) → ℂ) {φ : holGerms w}
    (hφ : φ ∈ holGermIdeal w p) :
    ∃ h : Fin k → (σ → ℂ) → ℂ, (∀ i, AnalyticAt ℂ (h i) w) ∧
      (φ : Germ (𝓝 w) ℂ) = ((fun z => ∑ i, h i z * p i z : (σ → ℂ) → ℂ) : Germ (𝓝 w) ℂ) := by
  induction hφ using Submodule.span_induction with
  | mem φ hφ =>
    obtain ⟨i, hi⟩ := hφ
    refine ⟨fun j _ => if j = i then 1 else 0, fun j => analyticAt_const, ?_⟩
    rw [hi]
    congr 1
    funext z
    simp
  | zero =>
    refine ⟨fun _ _ => 0, fun _ => analyticAt_const, ?_⟩
    rw [show (fun z => ∑ i, (fun (_ : Fin k) (_ : σ → ℂ) => (0 : ℂ)) i z * p i z) = (0 : (σ → ℂ) → ℂ) by
      funext z; simp]
    rfl
  | add x y _ _ hx hy =>
    obtain ⟨h₁, hh₁, e₁⟩ := hx
    obtain ⟨h₂, hh₂, e₂⟩ := hy
    refine ⟨fun i z => h₁ i z + h₂ i z, fun i => (hh₁ i).add (hh₂ i), ?_⟩
    show (x : Germ (𝓝 w) ℂ) + y = _
    rw [e₁, e₂, ← Germ.coe_add]
    congr 1
    funext z
    simp [add_mul, Finset.sum_add_distrib]
  | smul a x _ hx =>
    obtain ⟨h, hh, e⟩ := hx
    obtain ⟨fa, hfa, efa⟩ : ∃ f : (σ → ℂ) → ℂ, AnalyticAt ℂ f w ∧ (f : Germ (𝓝 w) ℂ) = a := a.2
    refine ⟨fun i z => fa z * h i z, fun i => hfa.mul (hh i), ?_⟩
    show (a : Germ (𝓝 w) ℂ) * x = _
    rw [e, ← efa, ← Germ.coe_mul]
    congr 1
    funext z
    simp [Finset.mul_sum, mul_assoc]

theorem mem_holGermIdeal_of_eq {k : ℕ} {p : Fin k → (σ → ℂ) → ℂ} (hp : ∀ i, AnalyticAt ℂ (p i) w)
    {h : Fin k → (σ → ℂ) → ℂ} (hh : ∀ i, AnalyticAt ℂ (h i) w) (φ : holGerms w)
    (hφ : (φ : Germ (𝓝 w) ℂ) = ((fun z => ∑ i, h i z * p i z : (σ → ℂ) → ℂ) : Germ (𝓝 w) ℂ)) :
    φ ∈ holGermIdeal w p := by
  have hsum : φ = ∑ i, (⟨(h i : Germ (𝓝 w) ℂ), h i, hh i, rfl⟩ : holGerms w) *
      ⟨(p i : Germ (𝓝 w) ℂ), p i, hp i, rfl⟩ := by
    apply Subtype.ext
    rw [hφ, show (fun z => ∑ i, h i z * p i z : (σ → ℂ) → ℂ) = ∑ i, h i * p i by
      funext z; simp [Finset.sum_apply]]
    set_option synthInstance.maxHeartbeats 100000 in
      rw [show ((∑ i, h i * p i : (σ → ℂ) → ℂ) : Germ (𝓝 w) ℂ) = Germ.coeRingHom (𝓝 w) (∑ i, h i * p i) from rfl,
      map_sum, AddSubmonoidClass.coe_finsetSum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [map_mul]
    rfl
  rw [hsum]
  exact Ideal.sum_mem _ fun i _ => Ideal.mul_mem_left _ _ (Ideal.subset_span ⟨i, rfl⟩)

theorem proof (hNoeth : AnalyticGermsNoetherian.Statement) (hPrime : PrimeGermNullstellensatz.Statement) :
    RueckertNullstellensatz.Statement := by
  intro σ _ w k f g hf hg hvan
  let G : holGerms w := ⟨(g : Germ (𝓝 w) ℂ), g, hg, rfl⟩
  have : IsNoetherianRing (holGerms w) := hNoeth σ w

  have hrad : G ∈ (holGermIdeal w f).radical := by
    rw [Ideal.radical_eq_sInf, Submodule.mem_sInf]
    rintro P ⟨hfP, hP⟩
    obtain ⟨r, s, hs⟩ := Submodule.fg_iff_exists_fin_generating_family.1 (IsNoetherian.noetherian P)
    choose p hp hps using fun j => (show ∃ q : (σ → ℂ) → ℂ, AnalyticAt ℂ q w ∧ (q : Germ (𝓝 w) ℂ) = s j from (s j).2)
    have hPeq : holGermIdeal w p = P := by
      rw [← hs, holGermIdeal]
      congr 1
      ext φ
      constructor
      · rintro ⟨j, hj⟩
        exact ⟨j, Subtype.ext (hj.trans (hps j)).symm⟩
      · rintro ⟨j, rfl⟩
        exact ⟨j, (hps j).symm⟩
    have hfmem : ∀ i, (⟨(f i : Germ (𝓝 w) ℂ), f i, hf i, rfl⟩ : holGerms w) ∈ holGermIdeal w p := fun i =>
      hPeq ▸ hfP (Ideal.subset_span ⟨i, rfl⟩)
    choose c _ hc using fun i => exists_of_mem_holGermIdeal p (hfmem i)
    have hfev : ∀ᶠ z in 𝓝 w, ∀ i, f i z = ∑ j, c i j z * p j z :=
      eventually_all.2 fun i => Germ.coe_eq.1 (hc i)
    have hvanp : ∀ᶠ z in 𝓝 w, (∀ j, p j z = 0) → g z = 0 := by
      filter_upwards [hvan, hfev] with z hz hfz hpz
      exact hz fun i => by rw [hfz i]; simp [hpz]
    obtain ⟨h, hh, hgh⟩ := hPrime σ w r p g hp hg (hPeq ▸ hP) hvanp
    exact hPeq ▸ mem_holGermIdeal_of_eq hp hh G (Germ.coe_eq.2 hgh)

  obtain ⟨m, hm⟩ := hrad
  have hm' : G ^ (m + 1) ∈ holGermIdeal w f := by
    rw [pow_succ']
    exact Ideal.mul_mem_left _ G hm
  obtain ⟨h, hh, hgh⟩ := exists_of_mem_holGermIdeal f hm'
  refine ⟨m + 1, h, Nat.succ_pos m, hh, ?_⟩
  have hG : ((G ^ (m + 1) : holGerms w) : Germ (𝓝 w) ℂ) = ((g ^ (m + 1) : (σ → ℂ) → ℂ) : Germ (𝓝 w) ℂ) := by
    rw [Germ.coe_pow]
    rfl
  rw [hG] at hgh
  filter_upwards [Germ.coe_eq.1 hgh] with z hz
  simpa using hz

end RueckertNullstellensatz

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PSerreSFlatAscent
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets

open IsLocalRing RingTheory.Sequence

theorem isWeaklyRegular_map_ringEquiv {R S : Type*} [CommRing R] [CommRing S] (e : R ≃+* S) {rs : List R}
    (h : IsWeaklyRegular R rs) : IsWeaklyRegular S (rs.map e) :=
  (AddEquiv.isWeaklyRegular_congr (e := e.toAddEquiv) (List.forall₂_map_right_iff.mpr
    (List.forall₂_same.mpr fun r _ x => by simp [smul_eq_mul]))).mp h

theorem min_add_le_min_add_min {k a b : WithBot ℕ∞} (hk : 0 ≤ k) (ha : 0 ≤ a) (hb : 0 ≤ b) :
    min k (a + b) ≤ min k a + min k b := by
  rcases le_total k a with h | h
  · rw [min_eq_left h]
    exact (min_le_left _ _).trans (le_add_of_nonneg_right (le_min hk hb))
  rcases le_total k b with h' | h'
  · rw [min_eq_left h']
    exact (min_le_left _ _).trans (le_add_of_nonneg_left (le_min hk ha))
  rw [min_eq_right h, min_eq_right h']
  exact min_le_right _ _

theorem SerreSFlatAscent.proof (hD : FlatDimFormula.Statement) (hR : FlatLocalRegularSequence.Statement) :
    SerreSFlatAscent.Statement := by
  intro A B _ _ _ hA hB hflat k hSA hfib P _
  set p : Ideal A := P.comap (algebraMap A B) with hp
  have : P.LiesOver p := ⟨rfl⟩
  let _ := Localization.AtPrime.algebraOfLiesOver p P
  have hAp : IsNoetherianRing (Localization.AtPrime p) :=
    IsLocalization.isNoetherianRing p.primeCompl _ hA
  have hBP : IsNoetherianRing (Localization.AtPrime P) :=
    IsLocalization.isNoetherianRing P.primeCompl _ hB

  have hJ : (maximalIdeal (Localization.AtPrime p)).map
        (algebraMap (Localization.AtPrime p) (Localization.AtPrime P)) =
      Ideal.map (algebraMap B (Localization.AtPrime P)) (Ideal.map (algebraMap A B) p) := by
    rw [← Localization.AtPrime.map_eq_maximalIdeal, Ideal.map_map, Ideal.map_map,
      ← IsScalarTower.algebraMap_eq, ← IsScalarTower.algebraMap_eq]
  let e := Ideal.quotEquivOfEq hJ
  obtain ⟨rs, hrs, hrsreg, hrslen⟩ := hSA p
  obtain ⟨ts, hts, htsreg, htslen⟩ := hfib P
  let g := Function.surjInv (Ideal.Quotient.mk_surjective (I := Ideal.map (algebraMap B (Localization.AtPrime P))
    (Ideal.map (algebraMap A B) p)))
  have hg : ∀ t, Ideal.Quotient.mk _ (g t) = t := Function.surjInv_eq _
  set ys := ts.map g with hys
  have hysmap : ys.map (Ideal.Quotient.mk ((maximalIdeal (Localization.AtPrime p)).map
      (algebraMap (Localization.AtPrime p) (Localization.AtPrime P)))) = ts.map e.symm := by
    rw [hys, List.map_map]
    refine List.map_congr_left fun t _ => ?_
    rw [Function.comp_apply]
    conv_rhs => rw [← hg t]
    simp [e]
  have hysmem : ∀ y ∈ ys, y ∈ maximalIdeal (Localization.AtPrime P) := by
    intro y hy
    obtain ⟨t, ht, rfl⟩ := List.mem_map.mp hy
    have := hts t ht
    rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff] at this ⊢
    exact fun hu => this (hg t ▸ hu.map _)
  have hreg := hR _ _ hAp hBP inferInstance inferInstance rs ys hrs hrsreg hysmem
    (hysmap ▸ isWeaklyRegular_map_ringEquiv e.symm htsreg)
  have hdim := hD _ _ hAp hBP inferInstance inferInstance
  rw [ringKrullDim_eq_of_ringEquiv e] at hdim
  refine ⟨rs.map (algebraMap _ _) ++ ys, ?_, hreg, ?_⟩
  · intro u hu
    rcases List.mem_append.mp hu with hu | hu
    · obtain ⟨r, hr, rfl⟩ := List.mem_map.mp hu
      exact map_nonunit _ r (hrs r hr)
    · exact hysmem u hu
  · rw [hdim, List.length_append, List.length_map, hys, List.length_map, Nat.cast_add]
    refine (min_add_le_min_add_min (by simp) ringKrullDim_nonneg_of_nontrivial
      ringKrullDim_nonneg_of_nontrivial).trans ?_
    exact add_le_add hrslen htslen

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PUnbranchedFibreSections
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets

open Topology

theorem UnbranchedFibreSections.proof : UnbranchedFibreSections.Statement := by
  intro σ _ X w B d A D δ N hP y₀ hy₀ hδ₀
  obtain ⟨_, _, hD, _, _, hprop, _, hδan, _, hcard, hchart, _⟩ := hP
  have hF0 : {x | x ∈ X ∩ B ∧ A x = y₀}.encard = N := hcard y₀ hy₀ hδ₀
  have hfin : {x | x ∈ X ∩ B ∧ A x = y₀}.Finite := Set.finite_of_encard_eq_coe hF0
  have ht : hfin.toFinset.card = N := by
    have h := hfin.encard_eq_coe_toFinset_card
    rw [hF0] at h
    exact_mod_cast h.symm
  let e : Fin N ≃ hfin.toFinset := (Finset.equivFinOfCardEq ht).symm
  have he : ∀ i, (e i : σ → ℂ) ∈ X ∩ B ∧ A (e i) = y₀ := fun i => hfin.mem_toFinset.mp (e i).2
  have hc : ∀ i : Fin N, ∃ (O : Set (Fin d → ℂ)) (V : Set (σ → ℂ)) (g : (Fin d → ℂ) → σ → ℂ),
      IsOpen O ∧ IsOpen V ∧ (e i : σ → ℂ) ∈ V ∧ AnalyticOnNhd ℂ g O ∧ (∀ y ∈ O, A (g y) = y) ∧
        X ∩ B ∩ V = g '' O := fun i => hchart _ (he i).1 (by rw [(he i).2]; exact hδ₀)
  choose O V g hO hV hxV hg hAg hXV using hc
  have hy₀O : ∀ i, y₀ ∈ O i := by
    intro i
    have hm : (e i : σ → ℂ) ∈ X ∩ B ∩ V i := ⟨(he i).1, hxV i⟩
    rw [hXV i] at hm
    obtain ⟨y', hy', hgy'⟩ := hm
    have h := hAg i y' hy'
    rw [hgy', (he i).2] at h
    rw [h]
    exact hy'
  obtain ⟨ρ, hρ, hρD⟩ := Metric.isOpen_iff.mp hD y₀ hy₀
  have hKD : Metric.closedBall y₀ (ρ / 2) ⊆ D :=
    (Metric.closedBall_subset_ball (by linarith)).trans hρD
  set C := {x | x ∈ X ∩ B ∧ A x ∈ Metric.closedBall y₀ (ρ / 2)} with hCdef
  have hC : IsCompact C := hprop _ hKD (isCompact_closedBall _ _)
  have hC' : IsCompact (C \ ⋃ i, V i) := hC.diff (isOpen_iUnion hV)
  have hE : IsClosed (A '' (C \ ⋃ i, V i)) := (hC'.image A.continuous).isClosed
  have hy₀E : y₀ ∉ A '' (C \ ⋃ i, V i) := by
    rintro ⟨x, ⟨⟨hxXB, _⟩, hxV'⟩, hAx⟩
    have hxF : x ∈ hfin.toFinset := hfin.mem_toFinset.mpr ⟨hxXB, hAx⟩
    apply hxV'
    refine Set.mem_iUnion.mpr ⟨e.symm ⟨x, hxF⟩, ?_⟩
    simpa using hxV (e.symm ⟨x, hxF⟩)
  have hnhds : Metric.ball y₀ (ρ / 2) ∩ (A '' (C \ ⋃ i, V i))ᶜ ∩ (⋂ i, O i) ∩ {y | δ y ≠ 0} ∈ 𝓝 y₀ := by
    refine Filter.inter_mem (Filter.inter_mem (Filter.inter_mem
      (Metric.ball_mem_nhds _ (by linarith)) (hE.isOpen_compl.mem_nhds hy₀E)) ?_) ?_
    · exact Filter.iInter_mem.mpr fun i => (hO i).mem_nhds (hy₀O i)
    · exact (hδan y₀ hy₀).continuousAt.eventually_ne hδ₀
  obtain ⟨r, hr, hrsub⟩ := Metric.mem_nhds_iff.mp hnhds
  have hrD : Metric.ball y₀ r ⊆ D := fun y hy =>
    hρD (Metric.ball_subset_ball (by linarith) (hrsub hy).1.1.1)
  refine ⟨r, g, hr, hrD, fun y hy => (hrsub hy).2,
    fun i y hy => hg i y (Set.mem_iInter.mp (hrsub hy).1.2 i), ?_⟩
  intro y hy
  obtain ⟨⟨⟨hyb, hyE⟩, hyO⟩, hyδ⟩ := hrsub hy
  have hyO' : ∀ i, y ∈ O i := Set.mem_iInter.mp hyO
  have hrange : {x | x ∈ X ∩ B ∧ A x = y} = Set.range (fun i => g i y) := by
    ext x
    constructor
    · rintro ⟨hxXB, hAx⟩
      have hxC : x ∈ C := ⟨hxXB, by rw [hAx]; exact Metric.ball_subset_closedBall hyb⟩
      have hxU : x ∈ ⋃ i, V i := by
        by_contra hn
        exact hyE ⟨x, ⟨hxC, hn⟩, hAx⟩
      obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hxU
      have hm : x ∈ X ∩ B ∩ V i := ⟨hxXB, hi⟩
      rw [hXV i] at hm
      obtain ⟨y', hy', rfl⟩ := hm
      have h := hAg i y' hy'
      rw [hAx] at h
      exact ⟨i, by rw [h]⟩
    · rintro ⟨i, rfl⟩
      have hm : g i y ∈ g i '' O i := ⟨y, hyO' i, rfl⟩
      rw [← hXV i] at hm
      exact ⟨hm.1, hAg i y (hyO' i)⟩
  refine ⟨?_, hrange⟩
  classical
  have hN : (Set.range (fun i => g i y)).encard = N := by
    rw [← hrange]
    exact hcard y (hrD hy) hyδ
  have himg : Set.range (fun i => g i y) = ↑(Finset.univ.image (fun i => g i y)) := by
    simp
  rw [himg, Set.encard_coe_eq_coe_finsetCard] at hN
  have hcardeq : (Finset.univ.image (fun i => g i y)).card = (Finset.univ : Finset (Fin N)).card := by
    rw [Finset.card_univ, Fintype.card_fin]
    exact_mod_cast hN
  have hinj := Finset.card_image_iff.mp hcardeq
  intro i j hij
  exact hinj (Finset.mem_coe.mpr (Finset.mem_univ i)) (Finset.mem_coe.mpr (Finset.mem_univ j)) hij

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PUnbranchedProperCountConstant
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets

open Topology

theorem UnbranchedProperCountConstant.proof (hloc : UnbranchedProperCountLocallyConstant.Statement)
    (hconn : ManifoldZerosComplementConnected.Statement) : UnbranchedProperCountConstant.Statement := by
  intro σ _ Y d A D δ hD hDc hmap hprop hδ hsec
  by_cases hne : ∃ y ∈ D, δ y ≠ 0
  swap
  · push Not at hne
    exact ⟨0, fun y hy hy' => absurd (hne y hy) hy'⟩
  obtain ⟨y₀, hy₀D, hy₀⟩ := hne
  have hreg : ∀ y ∈ D, IsRegularPointOf D y := fun y hy =>
    ⟨hy, d, ContinuousLinearMap.id ℂ _, D, D, id, hD, hD, hy, analyticOnNhd_id, fun _ _ => rfl, by simp⟩
  have hS : IsPreconnected (D \ {z | δ z = 0}) := hconn (Fin d) D δ hDc hreg hδ ⟨y₀, hy₀D, hy₀⟩
  have hL := hloc σ Y d A D δ hD hmap hprop hsec
  let f : (Fin d → ℂ) → ℕ := fun y => {x | x ∈ Y ∧ A x = y}.ncard
  have hcont : ContinuousOn f (D \ {z | δ z = 0}) := by
    intro y hy
    refine ContinuousAt.continuousWithinAt ((continuousAt_const (y := f y)).congr ?_)
    filter_upwards [(hL y hy.1 hy.2).2] with y' hy'
    simp only [f, Set.ncard_def, hy']
  refine ⟨f y₀, fun y hy hyδ => ?_⟩
  rw [← (hL y hy hyδ).1.cast_ncard_eq]
  exact congrArg _ (hS.constant hcont ⟨hy, hyδ⟩ ⟨hy₀D, hy₀⟩)

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
end

