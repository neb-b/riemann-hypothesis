module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.RegularCharts.ModelAt
public import Development.AbelianVarietyTheory.Definitions.RegularCharts.SCharts
public import Formalism.LocalToGlobal.ProjectiveLattices.FrameCharts
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt
public import Development.AbelianVarietyTheory.Proofs.GenericRegularity.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.GenericRegularity.Bundle0008
public import Development.AbelianVarietyTheory.Proofs.GenericRegularity.SpanEvalEqTopOfNoCommonZeroReduced
public import Development.AbelianVarietyTheory.Proofs.GenericRegularity.RigFrame
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0030
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0032
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0039
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0031
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0034
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.MemIffConjugateNotMem
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsFrameOfIsPeriod

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.GenericRegularity.ExistsRefinedCoveringChartFamily
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Reg

set_option synthInstance.maxHeartbeats 400000

namespace GlobalTheory.Reg

theorem adjoin_insert_union_image {K Ω : Type} [Field K] [Field Ω] [Algebra K Ω] [DecidableEq Ω] (x : Ω)
    (G : Finset Ω) {m : ℕ} (r : Fin m → Ω) :
    Algebra.adjoin K (insert x ((G ∪ Finset.univ.image r : Finset Ω) : Set Ω)) =
      Algebra.adjoin K ((Algebra.adjoin K (insert x (G : Set Ω)) : Set Ω) ∪ Set.range r) := by
  apply le_antisymm
  · apply Algebra.adjoin_mono
    intro z hz
    rcases hz with rfl | hz
    · exact Or.inl (Algebra.subset_adjoin (Or.inl rfl))
    · rcases Finset.mem_union.1 hz with h | h
      · exact Or.inl (Algebra.subset_adjoin (Or.inr h))
      · obtain ⟨i, -, rfl⟩ := Finset.mem_image.1 h
        exact Or.inr ⟨i, rfl⟩
  · apply Algebra.adjoin_le
    rintro z (hz | ⟨i, rfl⟩)
    · refine Algebra.adjoin_mono ?_ hz
      apply Set.insert_subset_insert
      intro g hg
      exact Finset.mem_coe.2 (Finset.mem_union_left _ hg)
    · exact Algebra.subset_adjoin (Or.inr (Finset.mem_coe.2 (Finset.mem_union_right _
        (Finset.mem_image.2 ⟨i, Finset.mem_univ _, rfl⟩))))

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
  {Xo : Moduli Dw l} {c : Coeff l}


set_option maxHeartbeats 800000 in
theorem PChart.exists_refine (hL : EvLaws Xo c) {O : Type} [CommRing O] {β : O →+* c.F} (P : PChart Xo c β)
    {m : ℕ} (ws : Fin m → Rul Xo c)
    (hw : ∀ e (he : e ∈ P.es) i, ((evR Xo c (ws i) (P.y e he) : P.R e) : P.Ω) = evR Xo c (ws i) P.yg)
    (hspan : ∀ e (he : e ∈ P.es), Ideal.span (Set.range fun i => (evR Xo c (ws i) (P.y e he) : P.R e)) = ⊤)
    (k : Fin m) (hk : evR Xo c (ws k) P.yg ≠ 0) :
    ∃ P' : PChart Xo c β, P'.Fam ws ∧
      ∀ (L : Type) [Field L] [Algebra c.F L] (W : ValuationSubring L) (y : FrPt Xo c L)
        (e : P.Ω) (he : e ∈ P.es) (ψ : P.R e →ₐ[c.F] L) (z : FrPt Xo c L) (t : Ix Dw → Lˣ),
        (∀ g : P.R e, (g : P.Ω) ∈ P.gens → ψ g ∈ W) → FrMap ψ (P.y e he) z → FrBor t y z →
        ψ (evR Xo c (ws k) (P.y e he)) ≠ 0 →
        (∀ i, ψ (evR Xo c (ws i) (P.y e he)) / ψ (evR Xo c (ws k) (P.y e he)) ∈ W) → P'.Catches W y := by
  classical
  let G : Finset P.Ω := P.gens ∪ Finset.univ.image fun i => evR Xo c (ws i) P.yg / evR Xo c (ws k) P.yg
  have hG : (P.gens : Set P.Ω) ⊆ G := fun g hg => Finset.mem_coe.2 (Finset.mem_union_left _ hg)
  have hGr : ∀ i, evR Xo c (ws i) P.yg / evR Xo c (ws k) P.yg ∈ G := fun i =>
    Finset.mem_union_right _ (Finset.mem_image.2 ⟨i, Finset.mem_univ _, rfl⟩)
  have hblow := fun e (he : e ∈ P.es) =>
    GlobalTheory.adjoin_ratios_of_span_eq_top c.F P.Ω (P.R e) m (fun i => evR Xo c (ws i) (P.y e he)) k (hspan e he)
      (by rw [hw e he k]; exact hk) (Algebra.adjoin c.F (insert e⁻¹ (G : Set P.Ω)))
      (by simp only [hw e he]; exact adjoin_insert_union_image _ _ _)
  choose hle hinv hsm hext using hblow
  have hy := fun e (he : e ∈ P.es) => hL.bc _ _ (Subalgebra.inclusion (hle e he)) (P.y e he)
  choose y' hy' using hy
  refine ⟨{ Ω := P.Ω
            gens := G
            frac := ?_
            es := P.es
            es_ne := P.es_ne
            es_mem := fun e he => ⟨(P.es_mem e he).1, ?_⟩
            sm := fun e he => hsm e he (P.sm e he)
            yg := P.yg
            y := y'
            gen := fun e he => frMap_cancel _ _ _ (Subalgebra.inclusion (hle e he)) _ (P.y e he) _ _ (hy' e he)
              (P.gen e he)
            int := ?_ }, ⟨k, hk, fun i => ?_, fun e he => ?_⟩, ?_⟩
  · rw [eq_top_iff, ← P.frac]
    exact Subfield.closure_mono (Set.union_subset_union_right _ hG)
  · exact Subring.closure_mono (Set.union_subset_union_right _ hG) (P.es_mem e he).2
  · intro e he T io
    letI := io.toAlgebra
    intro ψ h1 h2 z hz
    refine P.int e he T io (ψ.comp (Subalgebra.inclusion (hle e he))) h1 (fun g hg => ?_) z
      (frMap_trans _ _ _ _ _ _ _ _ (hy' e he) hz)
    exact h2 (Subalgebra.inclusion (hle e he) g) (hG hg)
  · exact Subring.subset_closure (Or.inr (hGr i))
  · have := hinv e he
    rw [hw e he k] at this
    exact this
  · intro L _ _ W y e he ψ z t h1 hz hb hψ hW
    obtain ⟨ψ', hc, hr⟩ := hext e he L ψ hψ
    refine ⟨e, he, ψ', z, t, fun g hg => ?_, ?_, hb⟩
    · rcases Finset.mem_union.1 hg with h | h
      · have e1 : g = Subalgebra.inclusion (hle e he) ⟨g, Algebra.subset_adjoin (Or.inr h)⟩ := Subtype.ext rfl
        have e2 := h1 ⟨g, Algebra.subset_adjoin (Or.inr h)⟩ h
        have e3 := DFunLike.congr_fun hc ⟨g, Algebra.subset_adjoin (Or.inr h)⟩
        rw [AlgHom.comp_apply] at e3
        have e4 := (congrArg ψ' e1).trans e3
        exact e4.symm ▸ e2
      · obtain ⟨i, -, hi⟩ := Finset.mem_image.1 h
        rw [← hw e he i, ← hw e he k] at hi
        have e1 := hr i (hi.symm ▸ g.2)
        have e2 : g = ⟨_, hi.symm ▸ g.2⟩ := Subtype.ext hi.symm
        have e4 := (congrArg ψ' e2).trans e1
        exact e4.symm ▸ hW i
    · refine frMap_cancel _ _ _ (Subalgebra.inclusion (hle e he)) ψ' (P.y e he) _ _ (hy' e he) ?_
      exact hc.symm ▸ hz

theorem exists_covers_fam : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l), EvLaws Xo c → ∀ (O : Type) [CommRing O] (β : O →+* c.F) (J : Type) [Finite J] (P : J → PChart Xo c β), Covers P → ∀ (a : (E →+* ℂ) × ℕ → ℕ) (n m : ℕ) (ws : Fin m → Rul Xo c), (∀ i, ws i ∈ sec Xo c a n) → Formalism.L2.PjFree.NoCommonZero Xo c ws → ∃ (J' : Type) (_ : Finite J') (P' : J' → PChart Xo c β), Covers P' ∧ ∀ j, (P' j).Fam ws := by
  intro E _ _ _ H Dw l Xo c hL O _ β J _ P hP a n m ws hws hnc
  have hw : ∀ j e (he : e ∈ (P j).es) i,
      ((evR Xo c (ws i) ((P j).y e he) : (P j).R e) : (P j).Ω) = evR Xo c (ws i) (P j).yg := fun j e he i =>
    (_root_.GlobalTheory.Reg.evR_baseChange_of_isReduced E H Dw l Xo c hL a n (ws i) (hws i) _ _ _ _ _ ((P j).gen e he)).symm
  have hspan : ∀ j e (he : e ∈ (P j).es),
      Ideal.span (Set.range fun i => (evR Xo c (ws i) ((P j).y e he) : (P j).R e)) = ⊤ := fun j e he =>
    _root_.GlobalTheory.Reg.span_evR_eq_top_of_noCommonZero E H Dw l Xo c hL a n m ws hws hnc _ _
  have h := fun p : {p : J × Fin m // evR Xo c (ws p.2) (P p.1).yg ≠ 0} =>
    PChart.exists_refine hL (P p.1.1) ws (hw p.1.1) (hspan p.1.1) p.1.2 p.2
  choose P' hF hC using h
  refine ⟨_, inferInstance, P', ?_, hF⟩
  intro L _ _ W hW y
  obtain ⟨j, e, he, ψ, z, t, h1, hz, hb⟩ := hP L W hW y
  have hex : ∃ i, ψ (evR Xo c (ws i) ((P j).y e he)) ≠ 0 := by
    by_contra hn
    push_neg at hn
    have hle : Ideal.span (Set.range fun i => (evR Xo c (ws i) ((P j).y e he) : (P j).R e)) ≤ RingHom.ker ψ := by
      rw [Ideal.span_le]
      rintro _ ⟨i, rfl⟩
      exact hn i
    rw [hspan j e he] at hle
    have h1 : ψ 1 = 0 := hle (Submodule.mem_top)
    rw [map_one] at h1
    exact one_ne_zero h1
  obtain ⟨i₀, hi₀⟩ := hex
  obtain ⟨k, -, hk⟩ := Finset.exists_max_image Finset.univ
    (fun i => W.valuation (ψ (evR Xo c (ws i) ((P j).y e he)))) ⟨i₀, Finset.mem_univ _⟩
  have hk0 : ψ (evR Xo c (ws k) ((P j).y e he)) ≠ 0 := by
    intro h0
    have := hk i₀ (Finset.mem_univ _)
    simp only [h0, map_zero, le_zero_iff, map_eq_zero] at this
    exact hi₀ this
  have hk1 : evR Xo c (ws k) (P j).yg ≠ 0 := by
    intro h0
    rw [← hw j e he k] at h0
    apply hk0
    have h2 : (evR Xo c (ws k) ((P j).y e he) : (P j).R e) = 0 := Subtype.ext h0
    rw [h2, map_zero]
  refine ⟨⟨(j, k), hk1⟩, hC ⟨(j, k), hk1⟩ L W y e he ψ z t h1 hz hb hk0 fun i => ?_⟩
  rw [← W.valuation_le_one_iff, map_div₀]
  exact div_le_one_of_le₀ (hk i (Finset.mem_univ _)) zero_le'

end GlobalTheory.Reg
end

-- bundled from Development.AbelianVarietyTheory.Proofs.GenericRegularity.PeriodEqTriangularOrthonormal
section
open NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj Formalism.L2.PjFree
open AlgebraicGeometry CategoryTheory Limits ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Frames GlobalTheory.FrameUnif GlobalTheory.FrameNorm
open scoped Matrix nonZeroDivisors

namespace GlobalTheory.FrameNorm

theorem period_eq_triangular_orthonormal : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (c : Coeff l) (σ : c.F →+* ℂ) (g : ℕ) (e : Fin g ≃ Σ τ : E →+* ℂ, Fin (Dw.mult τ)) (D : Datum H) (r : ℕ) (X : Data E r) (φ : D.La ≃ₗ[𝓞 E] X.Λ), GoodEmb c σ → D.p = Dw.p → D.q = Dw.q → r = Dw.p + Dw.q → X.p0 = Dw.q → (∀ τ : E →+* ℂ, τ ∈ X.Ψ ↔ τ (H.rt : E) = H.rt0) → (∀ a b, ((D.EF a b : ℤ) : ℚ) = Algebra.trace ℚ E (-X.ξ0 * herm X.Gm (φ a : Fin r → E) (φ b))) → (r ≠ 0 → ∀ τ ∈ X.Ψ, (τ X.ξ0).im < 0) → ∃ d : Fin g → ℝ, (∀ j, 0 < d j) ∧ ∀ P : D.La →+ (Fin g → ℂ), IsPeriod D (fun j => relab c σ (e j).1) P → ∃ x₀ ∈ X.dom, IsUnitFr X x₀ ∧ ∃ h₀ : Matrix (Fin g) (Fin g) ℂ, IsUnit h₀.det ∧ (∀ j j', h₀ j j' ≠ 0 → (e j).1 = (e j').1 ∧ ((e j).2 : ℕ) ≤ (e j').2) ∧ (∀ a j, (h₀ *ᵥ P a) j = perFr X x₀ (φ a : Fin r → E) (relab c σ (e j).1) (e j).2) ∧ ∀ a b, (hermForm (Matrix.diagonal fun j => ((d j : ℝ) : ℂ)) (h₀ *ᵥ P a) (h₀ *ᵥ P b)).im = D.EF a b := by
  intro E _ _ _ H Dw l c σ g e D r X φ hσ hp hq hr hp0 hty hef hneg
  obtain ⟨hbij, hrt, -, -⟩ := GlobalTheory.Relab.relab_good E H l c σ hσ
  have hcc : ∀ τ : E →+* ℂ, ComplexEmbedding.conjugate (ComplexEmbedding.conjugate τ) = τ := fun τ =>
    ComplexEmbedding.involutive_conjugate E τ
  obtain ⟨f, hf⟩ := exists_letter_equiv X.Ψ X.cmType Dw.p Dw.q r hr (relab c σ) hbij Dw.mult
    (fun τ h => by unfold Datum.mult; rw [if_pos ((hrt τ).1 ((hty _).1 h))])
    (fun τ h => by unfold Datum.mult; rw [if_neg (fun h' => h ((hty _).2 ((hrt τ).2 h')))])
  obtain ⟨idx, hi⟩ : ∃ idx : Fin g ≃ X.Ψ × Fin r, ∀ j,
      (relab c σ (e j).1 ∈ X.Ψ ∧ (idx j).1.1 = relab c σ (e j).1 ∧ ((idx j).2 : ℕ) = Dw.q + (e j).2) ∨
      (relab c σ (e j).1 ∉ X.Ψ ∧ (idx j).1.1 = ComplexEmbedding.conjugate (relab c σ (e j).1) ∧
        ((idx j).2 : ℕ) = Dw.q - 1 - (e j).2 ∧ ((e j).2 : ℕ) < Dw.q) := ⟨e.trans f, fun j => hf (e j)⟩
  rcases eq_or_ne r 0 with hr0 | hr0
  · subst hr0
    haveI : IsEmpty (Fin g) := idx.isEmpty
    refine ⟨fun _ => 1, fun _ => one_pos, fun P hP => ?_⟩
    obtain ⟨hx, hu⟩ := (GlobalTheory.UnitFrames.unit_frame_eq_orthonormal_mul_triangular E 0 X.p0 X.Ψ X.Gm
      X.Gm_herm).2.1 (fun _ a => a.elim0) (fun τ => Subsingleton.elim _ _)
    refine ⟨_, hx, hu, 1, by simp, fun j => isEmptyElim j, fun _ j => isEmptyElim j, fun a b => ?_⟩
    obtain ⟨-, -, -, -, Hm, -, -, hIm⟩ := hP
    rw [← hIm]
    simp [hermForm, dotProduct]
  have hpos : ∀ τ ∈ X.Ψ, 0 < (τ (-X.ξ0)).im := by
    intro τ hτ
    have := hneg hr0 τ hτ
    rw [map_neg, Complex.neg_im]
    linarith
  have hξ : cc (-X.ξ0) = -(-X.ξ0) := by
    have h := X.ξ0_im
    unfold cc at h ⊢
    rw [map_neg, h]
  have hty' : ∀ j, relab c σ (e j).1 = if ((idx j).2 : ℕ) < D.q then
      ComplexEmbedding.conjugate (idx j).1.1 else (idx j).1.1 := by
    intro j
    rw [hq]
    rcases hi j with ⟨a, b, c'⟩ | ⟨a, b, c', d⟩
    · rw [if_neg (by omega), b]
    · rw [if_pos (by omega), b, hcc]
  have hper : ∀ (x : Frame X.Ψ r) (v : Fin r → E) j, perFr X x v (relab c σ (e j).1) (e j).2 =
      if ((idx j).2 : ℕ) < D.q then
        hermC (idx j).1.1 X.Gm (col (mat x (idx j).1) (idx j).2) (Data.emb (idx j).1.1 v)
      else ((mat x (idx j).1)⁻¹ *ᵥ Data.emb (idx j).1.1 v) (idx j).2 := by
    intro x v j
    have h := hi j
    rw [hq]
    generalize idx j = t at h ⊢
    obtain ⟨⟨τ, hτ⟩, ⟨n, hn⟩⟩ := t
    dsimp only at h ⊢
    rw [← hp0] at h ⊢
    rcases h with ⟨a, rfl, rfl⟩ | ⟨a, rfl, rfl, d⟩
    · rw [if_neg (by omega)]
      unfold perFr
      rw [dite_eq_left a, dite_eq_left hn]
    · rw [if_pos (by omega)]
      unfold perFr
      rw [dite_eq_right a, dite_eq_left (show conjEmb (relab c σ (e j).1) ∈ X.Ψ from hτ), dite_eq_left hn]
      rfl
  let φ' : D.La →ₗ[𝓞 E] (Fin r → E) := X.Λ.subtype.comp φ.toLinearMap
  have hφ' : Function.Injective φ' ∧ Submodule.span E (Set.range φ') = ⊤ ∧
      (∀ a b, cc (X.Gm a b) = X.Gm b a) ∧ X.Gm.det ≠ 0 ∧
      ∀ x y, ((D.EF x y : ℤ) : ℚ) = Algebra.trace ℚ E (-X.ξ0 * herm X.Gm (φ' x) (φ' y)) := by
    refine ⟨fun a b hab => φ.injective (Subtype.ext hab), ?_, X.Gm_herm, X.Gm_det, hef⟩
    have hrange : Set.range φ' = X.Λ := by
      ext y
      constructor
      · rintro ⟨a, rfl⟩
        exact (φ a).2
      · intro hy
        exact ⟨φ.symm ⟨y, hy⟩, by simp [φ']⟩
    rw [hrange]
    exact X.Λ_span
  have hinj : ∀ j j', (e j).1 = (e j').1 → ((e j).2 : ℕ) = (e j').2 → j = j' := by
    intro j j' h1 h2
    apply e.injective
    refine Sigma.ext h1 ((Fin.heq_ext_iff (by rw [h1])).2 h2)
  refine ⟨fun j => 2 * ‖(idx j).1.1 (-X.ξ0)‖, fun j => ?_, fun P hP => ?_⟩
  · have h1 := hpos _ (idx j).1.2
    have h2 : (idx j).1.1 (-X.ξ0) ≠ 0 := by
      intro h0
      rw [h0] at h1
      simp at h1
    have := norm_pos_iff.2 h2
    positivity
  obtain ⟨x, hx, hPx⟩ := GlobalTheory.exists_frame_of_isPeriod E H D r (-X.ξ0) X.Gm φ' X.Ψ hty g idx _ hty' hξ hpos hφ'
    (by rw [hp, hq, hr]) P hP
  obtain ⟨x₀, b, hb, horth, rfl⟩ :=
    (GlobalTheory.UnitFrames.frame_mul_triangular_orthonormal E r D.q X.Ψ X.Gm X.Gm_herm).1 x hx
  have hs : ∀ j j', PerBor.moveMat D.q idx b j j' ≠ 0 →
      (e j).1 = (e j').1 ∧ ((e j).2 : ℕ) ≤ (e j').2 := by
    intro j j' hne
    obtain ⟨h1, h2⟩ := PerBor.moveMat_support _ idx hb j j' hne
    have t1 := hty' j
    have t2 := hty' j'
    have c1 := hi j
    have c2 := hi j'
    by_cases hj : ((idx j).2 : ℕ) < D.q
    · rw [if_pos hj] at h2 t1
      have hj' : ((idx j').2 : ℕ) < D.q := by omega
      rw [if_pos hj'] at t2
      refine ⟨hbij.1 (by rw [t1, t2, h1]), ?_⟩
      rcases c1 with ⟨-, -, c1⟩ | ⟨-, -, c1, d1⟩ <;> rcases c2 with ⟨-, -, c2⟩ | ⟨-, -, c2, d2⟩ <;> omega
    · rw [if_neg hj] at h2 t1
      have hj' : ¬ ((idx j').2 : ℕ) < D.q := by omega
      rw [if_neg hj'] at t2
      refine ⟨hbij.1 (by rw [t1, t2, h1]), ?_⟩
      rcases c1 with ⟨-, -, c1⟩ | ⟨-, -, c1, d1⟩ <;> rcases c2 with ⟨-, -, c2⟩ | ⟨-, -, c2, d2⟩ <;> omega
  have hbne : ∀ τ i, b τ i i ≠ 0 := fun τ i => PerMove.bor_diag_ne hb τ i
  have hu : IsUnit (PerBor.moveMat D.q idx b).det := by
    rw [PerBor.det_of_support _ _ hinj _ hs, isUnit_iff_ne_zero]
    refine Finset.prod_ne_zero_iff.2 fun j _ => ?_
    rw [PerBor.moveMat_diag D.q idx hb]
    split_ifs
    · exact hbne _ _
    · exact inv_ne_zero (hbne _ _)
  have hmove : ∀ a j, (PerBor.moveMat D.q idx b *ᵥ P a) j = if ((idx j).2 : ℕ) < D.q then
      hermC (idx j).1.1 X.Gm (col (mat (rmul x b) (idx j).1) (idx j).2) (Data.emb (idx j).1.1 (φ' a))
      else ((mat (rmul x b) (idx j).1)⁻¹ *ᵥ Data.emb (idx j).1.1 (φ' a)) (idx j).2 := fun a j =>
    (congrFun (PerBor.moveMat_mulVec D.q idx hb X.Gm x (φ' a) (P a) _ (hPx a) (fun _ => rfl)) j).symm
  have hqq : D.q = X.p0 := hq.trans hp0.symm
  obtain ⟨hx₀, hu₀⟩ := (GlobalTheory.UnitFrames.unit_frame_eq_orthonormal_mul_triangular E r X.p0 X.Ψ X.Gm
    X.Gm_herm).2.1 (rmul x b) (hqq ▸ horth)
  refine ⟨rmul x b, hx₀, hu₀, PerBor.moveMat D.q idx b, hu, hs, fun a j => ?_, fun a a' => ?_⟩
  · rw [hper, hmove]
    rfl
  · exact GlobalTheory.UnitFrame.im_hermForm_eq E H D r (-X.ξ0) X.Gm φ' X.Ψ hty g idx _ hty' hξ hpos hφ' (rmul x b)
      ((Matrix.mulVecLin (PerBor.moveMat D.q idx b)).toAddMonoidHom.comp P) hmove horth a a'

end GlobalTheory.FrameNorm
end

