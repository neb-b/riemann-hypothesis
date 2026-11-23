module

public import Mathlib
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0009
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0023
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0031
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0021
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0030
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0002
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0028
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0032
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0024

@[expose] public section

-- bundled from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PLinearFormCut
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.ComplexSets

open MvPolynomial

noncomputable section

def LinearFormCut.formMap (n : ℕ) : (Fin n → ℂ) →ₗ[ℂ] MvPolynomial (Fin n) ℂ where
  toFun a := ∑ j, C (a j) * X j
  map_add' a b := by simp [add_mul, Finset.sum_add_distrib]
  map_smul' c a := by simp [smul_eq_C_mul, Finset.mul_sum, mul_assoc]

theorem LinearFormCut.proof : LinearFormCut.Statement := by
  intro n e I hI
  classical
  let S := {Q : Ideal (MvPolynomial (Fin n) ℂ) | Q ∈ I.minimalPrimes ∧ Q ≠ originIdeal n}
  have : Finite S :=
    ((Ideal.finite_minimalPrimes_of_isNoetherianRing _ I).subset fun Q (hQ : Q ∈ S) => hQ.1).to_subtype
  let p : S → Submodule ℂ (Fin n → ℂ) := fun Q => (Q.1.restrictScalars ℂ).comap (formMap n)
  have hp : ∀ Q, p Q ≠ ⊤ := by
    intro Q htop
    apply Q.2.2
    have hle : originIdeal n ≤ Q.1 := by
      rw [originIdeal, Ideal.span_le]
      rintro _ ⟨j, rfl⟩
      have : Pi.single j 1 ∈ p Q := htop ▸ Submodule.mem_top
      simpa [p, formMap, Pi.single_apply] using this
    exact ((originIdeal_isMaximal n).eq_of_le Q.2.1.1.1.ne_top hle).symm
  obtain ⟨a, ha⟩ := Submodule.exists_forall_notMem_of_forall_ne_top p hp
  let B : Matrix (Fin 1) (Fin n) ℂ := Matrix.of fun _ j => a j
  refine ⟨B, ?_⟩
  have hl : formMap n a ∈ linIdeal B := Ideal.subset_span ⟨0, by simp [linPoly, formMap, B]⟩
  rw [ringKrullDim_quotient] at hI ⊢
  refine iSup_le fun l => ?_
  have hIh : I ≤ l.head.1.asIdeal := fun y hy => l.head.2 (Ideal.mem_sup_left hy)
  obtain ⟨Q, hQ, hQle⟩ := Ideal.exists_minimalPrimes_le hIh
  by_cases hQo : Q = originIdeal n
  · have hM : l.head.1.asIdeal.IsMaximal := by
      rw [← (originIdeal_isMaximal n).eq_of_le l.head.1.isPrime.ne_top (hQo ▸ hQle)]
      exact originIdeal_isMaximal n
    have h0 : l.length = 0 := by
      by_contra h
      have hlt : l.head < l.last := l.strictMono (Fin.pos_iff_ne_zero.2 (by simp [Fin.ext_iff]; omega))
      have hlt' : l.head.1.asIdeal < l.last.1.asIdeal := hlt
      exact (hM.eq_of_le l.last.1.isPrime.ne_top hlt'.le ▸ hlt').false
    simp [h0]
  · have hQa : formMap n a ∉ Q := ha ⟨Q, hQ, hQo⟩
    let f : PrimeSpectrum.zeroLocus (R := MvPolynomial (Fin n) ℂ) ↑(I ⊔ linIdeal B) →
        PrimeSpectrum.zeroLocus (R := MvPolynomial (Fin n) ℂ) ↑I :=
      fun x => ⟨x.1, fun y hy => x.2 (Ideal.mem_sup_left hy)⟩
    have hf : StrictMono f := fun x y h => h
    let q0 : PrimeSpectrum.zeroLocus (R := MvPolynomial (Fin n) ℂ) ↑I :=
      ⟨⟨Q, hQ.1.1⟩, fun y hy => hQ.1.2 hy⟩
    have hq : q0 < (l.map f hf).head := by
      refine lt_of_le_of_ne hQle fun h => hQa ?_
      have : formMap n a ∈ l.head.1.asIdeal := l.head.2 (Ideal.mem_sup_right hl)
      have hQh : Q = l.head.1.asIdeal :=
        congrArg (fun x : PrimeSpectrum.zeroLocus (R := MvPolynomial (Fin n) ℂ) ↑I => x.1.asIdeal) h
      rwa [hQh]
    have hlen := (Order.LTSeries.length_le_krullDim ((l.map f hf).cons q0 hq)).trans hI
    simp only [RelSeries.cons_length] at hlen
    have : l.length + 1 ≤ e + 1 := by exact_mod_cast hlen
    exact_mod_cast (by omega : l.length ≤ e)

end

end GroundTheory.Heights₂.Heights.ComplexSets
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PLocalParametrisation
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets

open Topology

theorem exists_proper_projection_nbhd {σ : Type} [Fintype σ] {X : Set (σ → ℂ)} {w : σ → ℂ} {d : ℕ}
    (A : (σ → ℂ) →L[ℂ] (Fin d → ℂ)) (hX : IsAnalyticNear X w) (hw : w ∈ X)
    (hiso : ∃ W ∈ 𝓝 w, ∀ x ∈ X ∩ W, A x = A w → x = w) {U : Set (σ → ℂ)} (hU : U ∈ 𝓝 w) :
    ∃ (B : Set (σ → ℂ)) (D : Set (Fin d → ℂ)), IsOpen B ∧ B ⊆ U ∧ w ∈ X ∩ B ∧ IsOpen D ∧
      IsPreconnected D ∧ Set.MapsTo A (X ∩ B) D ∧
      (∀ K ⊆ D, IsCompact K → IsCompact {x | x ∈ X ∩ B ∧ A x ∈ K}) ∧
      (∀ x ∈ X ∩ B, A x = A w → x = w) := by
  obtain ⟨N, k, f, hNo, hwN, hf, hXN⟩ := hX
  obtain ⟨W, hW, hisoW⟩ := hiso
  obtain ⟨r₀, hr₀, hball⟩ :=
    Metric.mem_nhds_iff.1 (Filter.inter_mem (Filter.inter_mem hU (hNo.mem_nhds hwN)) hW)
  set r := r₀ / 2 with hr
  have hr0 : 0 < r := half_pos hr₀
  have hcb : Metric.closedBall w r ⊆ U ∩ N ∩ W :=
    (Metric.closedBall_subset_ball (half_lt_self hr₀)).trans hball

  set Z : Set (σ → ℂ) := Metric.closedBall w r ∩ ⋂ i, (Metric.closedBall w r ∩ f i ⁻¹' {0}) with hZ
  have hZc : IsClosed Z := by
    refine Metric.isClosed_closedBall.inter (isClosed_iInter fun i => ?_)
    exact ((hf i).continuousOn.mono fun z hz => (hcb hz).1.2).preimage_isClosed_of_isClosed
      Metric.isClosed_closedBall isClosed_singleton
  have hZk : IsCompact Z := (isCompact_closedBall w r).of_isClosed_subset hZc Set.inter_subset_left
  have hZX : ∀ z ∈ Metric.closedBall w r, (z ∈ X ↔ z ∈ Z) := by
    intro z hz
    have hzN : z ∈ N := (hcb hz).1.2
    constructor
    · intro hzX
      have h1 : z ∈ X ∩ N := ⟨hzX, hzN⟩
      rw [hXN] at h1
      exact ⟨hz, Set.mem_iInter.2 fun i => ⟨hz, h1.2 i⟩⟩
    · intro hzZ
      have h2 : z ∈ {z | z ∈ N ∧ ∀ i, f i z = 0} := ⟨hzN, fun i => (Set.mem_iInter.1 hzZ.2 i).2⟩
      rw [← hXN] at h2
      exact h2.1

  have hSk : IsCompact (Z ∩ Metric.sphere w r) := hZk.inter_right Metric.isClosed_sphere
  have hAS : A w ∉ A '' (Z ∩ Metric.sphere w r) := by
    rintro ⟨x, ⟨hxZ, hxs⟩, hxA⟩
    have hxcb : x ∈ Metric.closedBall w r := Metric.sphere_subset_closedBall hxs
    have hxw := hisoW x ⟨(hZX x hxcb).2 hxZ, (hcb hxcb).2⟩ hxA
    rw [hxw, Metric.mem_sphere, dist_self] at hxs
    exact hr0.ne hxs
  obtain ⟨ε, hε, hεS⟩ :=
    Metric.mem_nhds_iff.1 ((hSk.image A.continuous).isClosed.isOpen_compl.mem_nhds hAS)
  refine ⟨Metric.ball w r ∩ A ⁻¹' Metric.ball (A w) ε, Metric.ball (A w) ε,
    Metric.isOpen_ball.inter (Metric.isOpen_ball.preimage A.continuous), ?_,
    ⟨hw, Metric.mem_ball_self hr0, Set.mem_preimage.mpr (Metric.mem_ball_self hε)⟩, Metric.isOpen_ball,
    (convex_ball _ _).isPreconnected, fun x hx => hx.2.2, ?_, ?_⟩
  · exact fun x hx => (hcb (Metric.ball_subset_closedBall hx.1)).1.1
  · intro K hKD hK
    have heq : {x | x ∈ X ∩ (Metric.ball w r ∩ A ⁻¹' Metric.ball (A w) ε) ∧ A x ∈ K} =
        Z ∩ A ⁻¹' K := by
      ext x
      constructor
      · rintro ⟨⟨hxX, hxb, -⟩, hxK⟩
        exact ⟨(hZX x (Metric.ball_subset_closedBall hxb)).1 hxX, hxK⟩
      · rintro ⟨hxZ, hxK⟩
        have hxcb : x ∈ Metric.closedBall w r := hxZ.1
        refine ⟨⟨(hZX x hxcb).2 hxZ, ?_, hKD hxK⟩, hxK⟩
        by_contra hxb
        have hxs : x ∈ Metric.sphere w r :=
          Metric.mem_sphere.2 (le_antisymm (Metric.mem_closedBall.1 hxcb)
            (not_lt.1 fun h => hxb (Metric.mem_ball.2 h)))
        exact hεS (hKD hxK) ⟨x, ⟨hxZ, hxs⟩, rfl⟩
    rw [heq]
    exact hZk.inter_right (hK.isClosed.preimage A.continuous)
  · exact fun x hx hxA => hisoW x ⟨hx.1, (hcb (Metric.ball_subset_closedBall hx.2.1)).2⟩ hxA

theorem LocalParametrisation.proof (hproj : GermFiniteProjection.Statement)
    (hcov : FiniteGermProjectionCover.Statement) : LocalParametrisation.Statement := by
  intro σ _ X w hX hirr U hU
  obtain ⟨d, A, hiso, hinj⟩ := hproj σ X w hX hirr
  obtain ⟨N₀, hN₀, hcovB⟩ := hcov σ X w d A hX hirr hiso hinj
  obtain ⟨B, D, hBo, hBU, hwB, hDo, hDc, hmaps, hprop, hisoB⟩ :=
    exists_proper_projection_nbhd A hX hirr.1 hiso (Filter.inter_mem hU hN₀)
  obtain ⟨δ, N, hP⟩ :=
    hcovB B D hBo (hBU.trans Set.inter_subset_right) hwB hDo hDc hmaps hprop hisoB
  exact ⟨d, A, B, D, δ, N, hBU.trans Set.inter_subset_left, hP⟩

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PManifoldZerosComplementConnected
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets

open Topology Filter Set

theorem ManifoldZerosComplementConnected.isPreconnected_of_local {α : Type*} [TopologicalSpace α]
    {X S : Set α} (hX : IsPreconnected X) (hSX : S ⊆ X) (hdense : ∀ x ∈ X, x ∈ closure S)
    (hloc : ∀ x ∈ X, ∃ W, IsOpen W ∧ x ∈ W ∧ IsPreconnected (W ∩ S)) : IsPreconnected S := by
  intro u v hu hv hSuv ⟨a, haS, hau⟩ ⟨b, hbS, hbv⟩
  by_contra hne
  have hne' : ∀ y ∈ S, y ∈ u → y ∈ v → False := fun y hy hyu hyv => hne ⟨y, hy, hyu, hyv⟩
  let P : Set α := {x | ∃ W, IsOpen W ∧ x ∈ W ∧ W ∩ S ⊆ u}
  let Q : Set α := {x | ∃ W, IsOpen W ∧ x ∈ W ∧ W ∩ S ⊆ v}
  have hP : IsOpen P := isOpen_iff_forall_mem_open.mpr fun x ⟨W, hW, hxW, hWS⟩ =>
    ⟨W, fun y hy => ⟨W, hW, hy, hWS⟩, hW, hxW⟩
  have hQ : IsOpen Q := isOpen_iff_forall_mem_open.mpr fun x ⟨W, hW, hxW, hWS⟩ =>
    ⟨W, fun y hy => ⟨W, hW, hy, hWS⟩, hW, hxW⟩
  have hcov : X ⊆ P ∪ Q := by
    intro x hx
    obtain ⟨W, hW, hxW, hWc⟩ := hloc x hx
    by_cases h1 : (W ∩ S ∩ u).Nonempty
    · by_cases h2 : (W ∩ S ∩ v).Nonempty
      · obtain ⟨y, hyWS, hyu, hyv⟩ := hWc u v hu hv (fun y hy => hSuv hy.2) h1 h2
        exact (hne' y hyWS.2 hyu hyv).elim
      · refine Or.inl ⟨W, hW, hxW, fun y hy => ?_⟩
        rcases hSuv hy.2 with h | h
        · exact h
        · exact absurd ⟨y, hy, h⟩ h2
    · refine Or.inr ⟨W, hW, hxW, fun y hy => ?_⟩
      rcases hSuv hy.2 with h | h
      · exact absurd ⟨y, hy, h⟩ h1
      · exact h
  obtain ⟨x, hxX, ⟨W₁, hW₁, hxW₁, hW₁u⟩, ⟨W₂, hW₂, hxW₂, hW₂v⟩⟩ :=
    hX P Q hP hQ hcov ⟨a, hSX haS, u, hu, hau, inter_subset_left⟩
      ⟨b, hSX hbS, v, hv, hbv, inter_subset_left⟩
  obtain ⟨y, ⟨hy₁, hy₂⟩, hyS⟩ := mem_closure_iff.mp (hdense x hxX) _ (hW₁.inter hW₂) ⟨hxW₁, hxW₂⟩
  exact hne' y hyS (hW₁u ⟨hy₁, hyS⟩) (hW₂v ⟨hy₂, hyS⟩)

theorem ManifoldZerosComplementConnected.isPreconnected_ball_diff_countable {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] (hE : 1 < Module.rank ℝ E) (c : E) {r : ℝ} (hr : 0 < r)
    {s : Set E} (hs : s.Countable) : IsPreconnected (Metric.ball c r \ s) := by
  let e : OpenPartialHomeomorph E E := OpenPartialHomeomorph.univBall c r
  have hsrc : e.source = univ := OpenPartialHomeomorph.univBall_source c r
  have htgt : e.target = Metric.ball c r := OpenPartialHomeomorph.univBall_target c hr
  have hc : (e ⁻¹' s).Countable := hs.preimage_of_injOn (e.injOn.mono (by rw [hsrc]; exact subset_univ _))
  have hcont : ContinuousOn e univ := hsrc ▸ e.continuousOn
  have heq : e '' (e ⁻¹' s)ᶜ = Metric.ball c r \ s := by
    ext w
    constructor
    · rintro ⟨v, hv, rfl⟩
      exact ⟨htgt ▸ e.map_source (hsrc ▸ mem_univ v), hv⟩
    · rintro ⟨hw, hws⟩
      rw [← htgt] at hw
      exact ⟨e.symm w, by simpa [mem_compl_iff, mem_preimage, e.right_inv hw] using hws, e.right_inv hw⟩
  rw [← heq]
  exact (hc.isConnected_compl_of_one_lt_rank hE).isPreconnected.image e (hcont.mono (subset_univ _))

theorem ManifoldZerosComplementConnected.isPreconnected_inter_ne_zero_of_complex {V : Set ℂ}
    (hVo : IsOpen V) (hV : IsPreconnected V) {φ : ℂ → ℂ} (hφ : AnalyticOnNhd ℂ φ V) {z₀ : ℂ}
    (hz₀ : z₀ ∈ V) (hφz₀ : φ z₀ ≠ 0) : IsPreconnected (V ∩ {z | φ z ≠ 0}) := by
  have hev : ∀ z ∈ V, ∀ᶠ w in 𝓝[≠] z, φ w ≠ 0 := by
    intro z hz
    rcases (hφ z hz).eventually_eq_zero_or_eventually_ne_zero with h | h
    · exact absurd (hφ.eqOn_zero_of_preconnected_of_eventuallyEq_zero hV hz h hz₀) hφz₀
    · exact h
  refine ManifoldZerosComplementConnected.isPreconnected_of_local hV inter_subset_left ?_ ?_
  · intro z hz
    have h1 : ∀ᶠ w in 𝓝[≠] z, w ∈ V ∩ {z | φ z ≠ 0} :=
      ((hev z hz).and (nhdsWithin_le_nhds (hVo.mem_nhds hz))).mono fun w hw => ⟨hw.2, hw.1⟩
    exact mem_closure_iff_frequently.mpr (h1.frequently.filter_mono nhdsWithin_le_nhds)
  · intro z hz
    obtain ⟨r, hr, hrV⟩ := Metric.isOpen_iff.mp hVo z hz
    obtain ⟨r', hr', hr'φ⟩ := Metric.eventually_nhds_iff_ball.mp (eventually_nhdsWithin_iff.mp (hev z hz))
    have hρ : 0 < min r r' := lt_min hr hr'
    refine ⟨Metric.ball z (min r r'), Metric.isOpen_ball, Metric.mem_ball_self hρ, ?_⟩
    have heq : Metric.ball z (min r r') ∩ (V ∩ {w | φ w ≠ 0}) =
        Metric.ball z (min r r') \ ({z} \ {w | φ w ≠ 0}) := by
      ext w
      simp only [mem_inter_iff, Set.mem_sdiff, mem_singleton_iff, mem_ofPred_eq]
      constructor
      · rintro ⟨hb, -, hne⟩
        exact ⟨hb, fun h => h.2 hne⟩
      · rintro ⟨hb, hw⟩
        refine ⟨hb, hrV (Metric.ball_subset_ball (min_le_left _ _) hb), ?_⟩
        by_cases hwz : w = z
        · intro h0
          exact hw ⟨hwz, fun h => h h0⟩
        · exact hr'φ w (Metric.ball_subset_ball (min_le_right _ _) hb) hwz
    rw [heq]
    exact ManifoldZerosComplementConnected.isPreconnected_ball_diff_countable
      (by rw [Complex.rank_real_complex]; exact_mod_cast (by norm_num : (1 : ℕ) < 2)) z hρ ((countable_singleton z).mono sdiff_subset)

theorem ManifoldZerosComplementConnected.isPreconnected_convex_inter_ne_zero {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℂ E] {U : Set E} (hUo : IsOpen U) (hUc : Convex ℝ U)
    {f : E → ℂ} (hf : AnalyticOnNhd ℂ f U) : IsPreconnected (U ∩ {z | f z ≠ 0}) := by
  refine isPreconnected_of_forall_pair ?_
  rintro p ⟨hpU, hp⟩ q ⟨hqU, hq⟩
  let ℓ : ℂ → E := fun t => p + t • (q - p)
  have hℓc : Continuous ℓ := by fun_prop
  have hℓa : ∀ t, AnalyticAt ℂ ℓ t := fun t =>
    analyticAt_const.add (analyticAt_id.smul analyticAt_const)
  have hVo : IsOpen (ℓ ⁻¹' U) := hUo.preimage hℓc
  have hVc : Convex ℝ (ℓ ⁻¹' U) := by
    intro a ha b hb s t hs ht hst
    have hmem := hUc ha hb hs ht hst
    show ℓ (s • a + t • b) ∈ U
    convert hmem using 1
    obtain rfl : t = 1 - s := by linarith
    simp only [ℓ, ← Complex.coe_smul]
    push_cast
    module
  have h0 : (0 : ℂ) ∈ ℓ ⁻¹' U := by simpa [ℓ] using hpU
  have h1 : (1 : ℂ) ∈ ℓ ⁻¹' U := by simpa [ℓ] using hqU
  refine ⟨ℓ '' (ℓ ⁻¹' U ∩ {t | f (ℓ t) ≠ 0}), ?_, ⟨0, ⟨h0, by simpa [ℓ] using hp⟩, by simp [ℓ]⟩,
    ⟨1, ⟨h1, by simpa [ℓ] using hq⟩, by simp [ℓ]⟩, ?_⟩
  · rintro _ ⟨t, ⟨htV, ht⟩, rfl⟩
    exact ⟨htV, ht⟩
  · exact (ManifoldZerosComplementConnected.isPreconnected_inter_ne_zero_of_complex hVo
      hVc.isPreconnected (φ := fun t => f (ℓ t)) (fun t ht => (hf (ℓ t) ht).comp (hℓa t)) h0
      (by simpa [ℓ] using hp)).image ℓ hℓc.continuousOn

theorem ManifoldZerosComplementConnected.proof : ManifoldZerosComplementConnected.Statement := by
  intro σ _ R h hR hreg hh ⟨x₀, hx₀R, hx₀⟩

  have chart : ∀ x ∈ R, ∃ (d : ℕ) (B : Set (Fin d → ℂ)) (W : Set (σ → ℂ)) (g : (Fin d → ℂ) → σ → ℂ),
      IsOpen B ∧ Convex ℝ B ∧ IsOpen W ∧ x ∈ W ∧ AnalyticOnNhd ℂ g B ∧ R ∩ W = g '' B := by
    intro x hx
    obtain ⟨-, d, A, O, V, g, hO, hV, hxV, hg, hAg, hRV⟩ := hreg x hx
    have hxO : A x ∈ O := by
      obtain ⟨y, hy, hgy⟩ : x ∈ g '' O := hRV ▸ ⟨hx, hxV⟩
      rw [← hgy, hAg y hy]
      exact hy
    obtain ⟨ε, hε, hεO⟩ := Metric.isOpen_iff.mp hO (A x) hxO
    refine ⟨d, Metric.ball (A x) ε, V ∩ A ⁻¹' Metric.ball (A x) ε, g, Metric.isOpen_ball,
      convex_ball _ _, hV.inter (Metric.isOpen_ball.preimage A.continuous),
      ⟨hxV, Set.mem_preimage.mpr (Metric.mem_ball_self hε)⟩, hg.mono hεO, ?_⟩
    ext z
    constructor
    · rintro ⟨hzR, hzV, hzB⟩
      obtain ⟨y, hy, rfl⟩ : z ∈ g '' O := hRV ▸ ⟨hzR, hzV⟩
      have hAy : A (g y) ∈ Metric.ball (A x) ε := hzB
      rw [hAg y hy] at hAy
      exact ⟨y, hAy, rfl⟩
    · rintro ⟨y, hy, rfl⟩
      have hgy : g y ∈ R ∩ V := by rw [hRV]; exact ⟨y, hεO hy, rfl⟩
      refine ⟨hgy.1, hgy.2, ?_⟩
      show A (g y) ∈ Metric.ball (A x) ε
      rw [hAg y (hεO hy)]
      exact hy
  have chartR : ∀ {d : ℕ} {B : Set (Fin d → ℂ)} {W : Set (σ → ℂ)} {g : (Fin d → ℂ) → σ → ℂ},
      R ∩ W = g '' B → ∀ y ∈ B, g y ∈ R := by
    intro d B W g hRW y hy
    have : g y ∈ R ∩ W := by rw [hRW]; exact ⟨y, hy, rfl⟩
    exact this.1

  let T : Set (σ → ℂ) := {x | ∀ᶠ z in 𝓝 x, z ∈ R → h z = 0}
  have hTo : IsOpen T := isOpen_setOfPred_eventually_nhds
  let T₂ : Set (σ → ℂ) := {x | ∃ W, IsOpen W ∧ x ∈ W ∧ ∀ z ∈ W ∩ R, z ∉ T}
  have hT₂o : IsOpen T₂ := isOpen_iff_forall_mem_open.mpr fun x ⟨W, hW, hxW, hWT⟩ =>
    ⟨W, fun y hy => ⟨W, hW, hy, hWT⟩, hW, hxW⟩
  have hcov : R ⊆ T ∪ T₂ := by
    intro x hx
    obtain ⟨d, B, W, g, hBo, hBc, hWo, hxW, hg, hRW⟩ := chart x hx
    have hhg : AnalyticOnNhd ℂ (fun y => h (g y)) B := fun y hy =>
      (hh (g y) (chartR hRW y hy)).comp (hg y hy)
    by_cases hzero : ∃ y ∈ B, ∀ᶠ y' in 𝓝 y, h (g y') = 0
    · obtain ⟨y, hy, hev⟩ := hzero
      have hEq := hhg.eqOn_zero_of_preconnected_of_eventuallyEq_zero hBc.isPreconnected hy hev
      left
      show ∀ᶠ z in 𝓝 x, z ∈ R → h z = 0
      filter_upwards [hWo.mem_nhds hxW] with z hzW hzR
      obtain ⟨y', hy', rfl⟩ : z ∈ g '' B := hRW ▸ ⟨hzR, hzW⟩
      exact hEq hy'
    · right
      refine ⟨W, hWo, hxW, ?_⟩
      rintro z ⟨hzW, hzR⟩ hzT
      obtain ⟨y, hy, rfl⟩ : z ∈ g '' B := hRW ▸ ⟨hzR, hzW⟩
      have hzT' : ∀ᶠ w in 𝓝 (g y), w ∈ R → h w = 0 := hzT
      refine hzero ⟨y, hy, ?_⟩
      filter_upwards [(hg y hy).continuousAt.tendsto.eventually hzT', hBo.mem_nhds hy] with y' h1 h2
      exact h1 (chartR hRW y' h2)

  have hTR : ∀ x ∈ R, ¬ ∀ᶠ z in 𝓝 x, z ∈ R → h z = 0 := by
    intro x hx hxT
    have hx₀T₂ : x₀ ∈ T₂ := by
      rcases hcov hx₀R with h1 | h1
      · exact absurd ((show ∀ᶠ z in 𝓝 x₀, z ∈ R → h z = 0 from h1).self_of_nhds hx₀R) hx₀
      · exact h1
    obtain ⟨y, hyR, hyT, W, -, hyW, hWT⟩ := hR T T₂ hTo hT₂o hcov ⟨x, hx, hxT⟩ ⟨x₀, hx₀R, hx₀T₂⟩
    exact hWT y ⟨hyW, hyR⟩ hyT
  refine ManifoldZerosComplementConnected.isPreconnected_of_local hR sdiff_subset ?_ ?_
  · intro x hx
    rw [mem_closure_iff_frequently]
    exact (Filter.not_eventually.mp (hTR x hx)).mono fun z hz => Classical.not_imp.mp hz
  · intro x hx
    obtain ⟨d, B, W, g, hBo, hBc, hWo, hxW, hg, hRW⟩ := chart x hx
    have hhg : AnalyticOnNhd ℂ (fun y => h (g y)) B := fun y hy =>
      (hh (g y) (chartR hRW y hy)).comp (hg y hy)
    refine ⟨W, hWo, hxW, ?_⟩
    have heq : W ∩ (R \ {z | h z = 0}) = g '' (B ∩ {y | h (g y) ≠ 0}) := by
      ext z
      constructor
      · rintro ⟨hzW, hzR, hz⟩
        obtain ⟨y, hy, rfl⟩ : z ∈ g '' B := hRW ▸ ⟨hzR, hzW⟩
        exact ⟨y, ⟨hy, hz⟩, rfl⟩
      · rintro ⟨y, ⟨hy, hy'⟩, rfl⟩
        have hgy : g y ∈ R ∩ W := by rw [hRW]; exact ⟨y, hy, rfl⟩
        exact ⟨hgy.2, hgy.1, hy'⟩
    rw [heq]
    exact (ManifoldZerosComplementConnected.isPreconnected_convex_inter_ne_zero hBo hBc hhg).image g
      (hg.continuousOn.mono inter_subset_left)

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PPerfectFieldExtensionFormallySmooth
section
set_option maxSynthPendingDepth 1

open Polynomial IntermediateField

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets

section

variable {F K : Type} [Field F] [Field K] [Algebra F K]

theorem formallySmooth_of_perfectField_of_charP [PerfectField F] (p : ℕ) [hp : Fact p.Prime] [CharP F p] :
    Algebra.FormallySmooth F K := by
  have : CharP K p := charP_of_injective_algebraMap (algebraMap F K).injective p
  refine Algebra.FormallySmooth.of_comp_surjective fun B _ _ N hN u => ?_
  have hpB : (p : B) = 0 := by rw [← map_natCast (algebraMap F B), CharP.cast_eq_zero, map_zero]
  set P := sqZeroFrobeniusLift N hp.out hpB hN
  set ψ : K →+* B := P.comp u.toRingHom
  have hψ : ∀ (z : K) (c : B), Ideal.Quotient.mk N c = u z → ψ z = c ^ p := fun z c hc => by
    show P (u z) = c ^ p
    rw [← hc, sqZeroFrobeniusLift_mk]
  obtain ⟨σ₀, hσ₀⟩ := exists_isGoodPartialLift_frobenius (K := K) p hpB hN u
  have : Nonempty {σ : Σ L : IntermediateField F K, L →ₐ[F] B // IsGoodPartialLift p N u ψ σ} :=
    ⟨⟨σ₀, hσ₀⟩⟩
  obtain ⟨⟨⟨L, φ⟩, hgood⟩, hm⟩ := exists_maximal_of_nonempty_chains_bounded
    (r := fun a b : {σ : Σ L : IntermediateField F K, L →ₐ[F] B // IsGoodPartialLift p N u ψ σ} =>
      PartialLiftLE a.1 b.1)
    (exists_isGoodPartialLift_upperBound (p := p) (N := N) (u := u) (ψ := ψ)) (fun hab hbd => hab.trans hbd)
  have htop : (⊤ : IntermediateField F K) ≤ L := by
    intro x _
    by_contra hx
    obtain ⟨σ, hσ, hle, hxσ⟩ := exists_isGoodPartialLift_extend p hψ hgood hx
    exact hx ((hm ⟨σ, hσ⟩ hle).1 hxσ)
  refine ⟨φ.comp ((IntermediateField.inclusion htop).comp IntermediateField.topEquiv.symm.toAlgHom), ?_⟩
  ext x
  exact hgood.2 _

theorem formallySmooth_of_charZero [CharZero F] : Algebra.FormallySmooth F K := by
  obtain ⟨s, hs⟩ := exists_isTranscendenceBasis F K
  have := hs.isAlgebraic_field
  have : CharZero (IntermediateField.adjoin F (Set.range ((↑) : s → K))) :=
    charZero_of_injective_algebraMap (algebraMap F _).injective
  exact .of_algebraicIndependent_of_isSeparable hs.1

end

theorem PerfectFieldExtensionFormallySmooth.proof : PerfectFieldExtensionFormallySmooth.Statement := by
  intro F K _ _ _ _
  obtain ⟨p, hchar⟩ := CharP.exists F
  rcases CharP.char_is_prime_or_zero F p with hp | rfl
  · have := Fact.mk hp
    exact formallySmooth_of_perfectField_of_charP p
  · have := CharP.charP_to_charZero F
    exact formallySmooth_of_charZero

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PSerreCriterion
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets

open IsLocalRing

theorem isRegularLocalRing_of_isIntegrallyClosed_of_ringKrullDim_le_one (B : Type*) [CommRing B] [IsLocalRing B]
    [IsNoetherianRing B] [IsDomain B] [IsIntegrallyClosed B] (h : ringKrullDim B ≤ 1) : IsRegularLocalRing B := by
  by_cases hf : IsField B
  · let := hf.toField
    infer_instance
  · have : Ring.KrullDimLE 1 B := Ring.krullDimLE_iff.mpr (by exact_mod_cast h)
    have hm : maximalIdeal B ≠ ⊥ := fun hm => hf (isField_iff_maximalIdeal_eq.mpr hm)
    have h3 : IsIntegrallyClosed B ∧ ∃! P : Ideal B, P ≠ ⊥ ∧ P.IsPrime :=
      ⟨inferInstance, maximalIdeal B, ⟨hm, inferInstance⟩, fun P ⟨hP, hPp⟩ =>
        IsLocalRing.eq_maximalIdeal (hPp.isMaximal_of_ne_bot hP)⟩
    have hdvr : IsDiscreteValuationRing B := ((IsDiscreteValuationRing.TFAE B hf).out 1 4).mpr h3
    infer_instance

theorem SerreCriterion.proof (hS : NormalLocalDepthTwo.Statement) (hN : SerreNormalOfRegularDepth.Statement) :
    SerreCriterion.Statement := by
  intro A _ hA
  refine ⟨fun h => ⟨fun P _ hdim => ?_, fun P _ => ?_⟩, fun h => hN A hA h.1 h.2⟩
  · obtain ⟨hd, hi⟩ := h P
    exact isRegularLocalRing_of_isIntegrallyClosed_of_ringKrullDim_le_one _ (by exact_mod_cast hdim)
  · obtain ⟨hd, hi⟩ := h P
    exact hS _

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
end

