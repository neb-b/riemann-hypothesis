module

public import Mathlib
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsHolPeriods
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.Bundle0003
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
public import Development.AbelianVarietyTheory.PublishedTheorems.Landherr₂.LandherrStIffLandherr
public import Development.AbelianVarietyTheory.PublishedTheorems.Landherr₂.ExistsNormTensor
public import Formalism.LocalToGlobal.ProjectiveLattices.UnFree
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.HermFormConjDiag
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsFrameOfIsPeriod
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0030
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0032
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0026
public import Development.AbelianVarietyTheory.Proofs.GenericRegularity.Bundle0020
public import Formalism.LocalToGlobal.ProjectiveLattices.ThShort
public import Formalism.LocalToGlobal.ProjectiveLattices.ThGerm
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.VtUniq
public import Formalism.SharpRestriction.Divisibility.GeneratorPowers.Bundle0015
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.FrameBaseChangeEigenBasis
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.Bundle0037
public import Formalism.SharpRestriction.GenusPolyhedralBounds.RelativeIndexClassSets.NormEuclideanEmbeddingEqNetNorm

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.CardCompLePeriodSpaces
section
open AlgebraicGeometry CategoryTheory Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor

namespace GlobalTheory.CompInj

open ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj Formalism.L2.PjFree GlobalTheory.Frames
open scoped Matrix ComplexOrder

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

theorem dom_nonempty {r : ℕ} (X : Data E r) : ∃ x, x ∈ X.dom := by
  choose P hP0 hP using X.signature
  refine ⟨fun τ => P τ, fun τ => ⟨hP0 τ, fun i => ?_⟩⟩
  apply GlobalTheory.PeriodOnto.lminor_sign
  have h1 : GlobalTheory.PeriodOnto.sgnMat r X.p0 * gram τ.1 X.Gm (mat (fun τ => P τ) τ) = 1 := by
    change GlobalTheory.PeriodOnto.sgnMat r X.p0 * gram τ.1 X.Gm (P τ) = 1
    rw [hP, GlobalTheory.PeriodOnto.sgnMat, Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
    congr 1
    funext a
    unfold sgn
    split_ifs <;> simp
  rw [h1]
  exact Matrix.PosDef.one

theorem im_eq_of_span {g : ℕ} {Λ : Type} (P : Λ → Fin g → ℂ) (hspan : Submodule.span ℝ (Set.range P) = ⊤)
    (A B : Matrix (Fin g) (Fin g) ℂ) (h : ∀ x y, (hermForm A (P x) (P y)).im = (hermForm B (P x) (P y)).im)
    (z z' : Fin g → ℂ) : (hermForm A z z').im = (hermForm B z z').im := by
  have hz : z ∈ Submodule.span ℝ (Set.range P) := by rw [hspan]; trivial
  have hz' : z' ∈ Submodule.span ℝ (Set.range P) := by rw [hspan]; trivial
  unfold hermForm at *
  induction hz using Submodule.span_induction with
  | mem z hz =>
    obtain ⟨x, rfl⟩ := hz
    induction hz' using Submodule.span_induction with
    | mem z hz =>
      obtain ⟨y, rfl⟩ := hz
      exact h x y
    | zero => simp
    | add _ _ _ _ h1 h2 =>
      simp only [star_add, Matrix.mulVec_add, dotProduct_add, Complex.add_im, h1, h2]
    | smul c _ _ h1 =>
      simp only [star_smul, star_trivial, Matrix.mulVec_smul, dotProduct_smul, Complex.smul_im, h1]
  | zero => simp
  | add _ _ _ _ h1 h2 => simp only [add_dotProduct, Complex.add_im, h1, h2]
  | smul c _ _ h1 => simp only [smul_dotProduct, Complex.smul_im, h1]

theorem not_im_neg (H : Host E) (D : Datum H) {r : ℕ} (hr : 1 ≤ r) (ξ : E) (Gm : Matrix (Fin r) (Fin r) E)
    (φ : D.La → (Fin r → E)) (Ψ : Finset (E →+* ℂ))
    (hcm : ∀ τ : E →+* ℂ, τ ∈ Ψ ↔ ComplexEmbedding.conjugate τ ∉ Ψ) {g : ℕ} (idx : Fin g ≃ Ψ × Fin r)
    (ty : Fin g → (E →+* ℂ)) (q : ℕ) (hξ : cc ξ = -ξ) (hG : ∀ a b, cc (Gm a b) = Gm b a)
    (hEF : ∀ x y, ((D.EF x y : ℤ) : ℚ) = Algebra.trace ℚ E (ξ * herm Gm (φ x) (φ y)))
    (x : Frame Ψ r) (hx : x ∈ GG Ψ Gm q) (P : D.La →+ (Fin g → ℂ))
    (hP : ∀ v k, P v k = GlobalTheory.FramePeriod.locPer (idx k).1.1 Gm q (mat x (idx k).1) (Data.emb (idx k).1.1 (φ v))
      (idx k).2) (hper : IsPeriod D ty P) (hneg : ∀ τ ∈ Ψ, (τ ξ).im < 0) : False := by
  classical
  obtain ⟨-, -, -, hspan, Hm, -, hpos, hIm⟩ := hper
  choose Hl hH hp hI using fun τ : Ψ =>
    (GlobalTheory.FramePeriod.exists_loc τ.1 Gm hG q (mat x τ) (hx τ).1 (hx τ).2).2
  have hblk : ∀ v (τ : Ψ), (fun a => P v (idx.symm (τ, a))) =
      GlobalTheory.FramePeriod.locPer τ.1 Gm q (mat x τ) (Data.emb τ.1 (φ v)) := by
    intro v τ
    funext a
    rw [hP, idx.apply_symm_apply]
  have key := im_eq_of_span P hspan Hm (Matrix.of fun k l => if (idx k).1 = (idx l).1 then
      ((2 * ((idx k).1.1 ξ).im : ℝ) : ℂ) * Hl (idx k).1 (idx k).2 (idx l).2 else 0) (by
    intro v w
    rw [GlobalTheory.FramePeriod.hermForm_block idx (fun τ : Ψ => 2 * (τ.1 ξ).im) Hl, Complex.im_sum, hIm]
    have h1 : ((D.EF v w : ℤ) : ℝ) = ((Algebra.trace ℚ E (ξ * herm Gm (φ v) (φ w)) : ℚ) : ℝ) := by
      rw [← hEF]; simp
    rw [h1, GlobalTheory.FramePeriod.trace_re Ψ hcm]
    refine Finset.sum_congr rfl fun τ _ => ?_
    rw [hblk, hblk, Complex.im_ofReal_mul, hI, map_mul, ← hermC_emb]
    have h2 : (τ.1 ξ).re = 0 := by
      have h3 := congrArg Complex.re (emb_cc τ.1 ξ)
      rw [hξ, map_neg, Complex.neg_re, Complex.conj_re] at h3
      linarith
    rw [Complex.mul_re, h2]
    ring)
  have hI' : ∀ (A : Matrix (Fin g) (Fin g) ℂ) (z : Fin g → ℂ),
      (hermForm A (Complex.I • z) z).im = (hermForm A z z).re := by
    intro A z
    simp [hermForm]
  obtain ⟨σ⟩ : Nonempty (E →+* ℂ) := inferInstance
  obtain ⟨τ, hτ⟩ : ∃ τ, τ ∈ Ψ := by
    by_cases h : ComplexEmbedding.conjugate σ ∈ Ψ
    · exact ⟨_, h⟩
    · exact ⟨σ, (hcm σ).2 h⟩
  have hz : (fun _ => 1 : Fin g → ℂ) ≠ 0 := fun h => by
    simpa using congrFun h (idx.symm (⟨τ, hτ⟩, ⟨0, hr⟩))
  have h1 := key (Complex.I • fun _ => 1) (fun _ => 1)
  rw [hI', hI', GlobalTheory.FramePeriod.hermForm_block idx (fun τ : Ψ => 2 * (τ.1 ξ).im) Hl, Complex.re_sum] at h1
  have h2 := hpos _ hz
  rw [h1] at h2
  refine absurd h2 (not_lt.2 (Finset.sum_nonpos fun t _ => ?_))
  rw [Complex.re_ofReal_mul]
  have h3 := hp t (fun _ => 1) (fun h => by simpa using congrFun h ⟨0, hr⟩)
  have h4 := hneg t.1 t.2
  nlinarith

variable {H : Host E} {Dw : Datum H} {l : Level H}

theorem exists_idx {c : Coeff l} {σ : c.F →+* ℂ} (hσ : Formalism.L2.PjFree.GoodEmb c σ) {r g : ℕ} (hr : r = Dw.p + Dw.q)
    (e : Fin g ≃ Σ τ : E →+* ℂ, Fin (Dw.mult τ)) (X : Data E r) (hp0 : X.p0 = Dw.q)
    (hty : ∀ τ : E →+* ℂ, τ ∈ X.Ψ ↔ τ (H.rt : E) = H.rt0) :
    ∃ idx : Fin g ≃ X.Ψ × Fin r, (∀ j, Formalism.L2.PjFree.relab c σ (e j).1 =
      if ((idx j).2 : ℕ) < Dw.q then ComplexEmbedding.conjugate (idx j).1.1 else (idx j).1.1) ∧
      ∀ (x : Frame X.Ψ r) (v : Fin r → E) j, Formalism.L2.PjFree.perFr X x v (Formalism.L2.PjFree.relab c σ (e j).1) (e j).2 =
        if ((idx j).2 : ℕ) < Dw.q then hermC (idx j).1.1 X.Gm (col (mat x (idx j).1) (idx j).2) (Data.emb (idx j).1.1 v)
        else ((mat x (idx j).1)⁻¹ *ᵥ Data.emb (idx j).1.1 v) (idx j).2 := by
  obtain ⟨hbij, hrt, -, -⟩ := GlobalTheory.Relab.relab_good E H l c σ hσ
  have hcc : ∀ τ : E →+* ℂ, ComplexEmbedding.conjugate (ComplexEmbedding.conjugate τ) = τ := fun τ =>
    ComplexEmbedding.involutive_conjugate E τ
  obtain ⟨f, hf⟩ := GlobalTheory.FrameUnif.exists_letter_equiv X.Ψ X.cmType Dw.p Dw.q r hr (Formalism.L2.PjFree.relab c σ) hbij Dw.mult
    (fun τ h => by unfold Datum.mult; rw [if_pos ((hrt τ).1 ((hty _).1 h))])
    (fun τ h => by unfold Datum.mult; rw [if_neg (fun h' => h ((hty _).2 ((hrt τ).2 h')))])
  obtain ⟨idx, hi⟩ : ∃ idx : Fin g ≃ X.Ψ × Fin r, ∀ j,
      (Formalism.L2.PjFree.relab c σ (e j).1 ∈ X.Ψ ∧ (idx j).1.1 = Formalism.L2.PjFree.relab c σ (e j).1 ∧ ((idx j).2 : ℕ) = Dw.q + (e j).2) ∨
      (Formalism.L2.PjFree.relab c σ (e j).1 ∉ X.Ψ ∧ (idx j).1.1 = ComplexEmbedding.conjugate (Formalism.L2.PjFree.relab c σ (e j).1) ∧
        ((idx j).2 : ℕ) = Dw.q - 1 - (e j).2 ∧ ((e j).2 : ℕ) < Dw.q) := ⟨e.trans f, fun j => hf (e j)⟩
  refine ⟨idx, fun j => ?_, fun x v j => ?_⟩
  · rcases hi j with ⟨a, b, c'⟩ | ⟨a, b, c', d⟩
    · rw [if_neg (by omega), b]
    · rw [if_pos (by omega), b, hcc]
  · have h := hi j
    generalize idx j = t at h ⊢
    obtain ⟨⟨τ, hτ⟩, ⟨n, hn⟩⟩ := t
    dsimp only at h ⊢
    rw [← hp0] at h ⊢
    rcases h with ⟨a, rfl, rfl⟩ | ⟨a, rfl, rfl, d⟩
    · rw [if_neg (by omega)]
      unfold Formalism.L2.PjFree.perFr
      rw [dite_eq_left a, dite_eq_left hn]
    · rw [if_pos (by omega)]
      unfold Formalism.L2.PjFree.perFr
      rw [dite_eq_right a, dite_eq_left (show conjEmb (Formalism.L2.PjFree.relab c σ (e j).1) ∈ X.Ψ from hτ), dite_eq_left hn]
      rfl

theorem exists_frame {c : Coeff l} {σ : c.F →+* ℂ} (hσ : Formalism.L2.PjFree.GoodEmb c σ) {r g : ℕ} (h1 : 1 ≤ r)
    (hr : r = Dw.p + Dw.q) (e : Fin g ≃ Σ τ : E →+* ℂ, Fin (Dw.mult τ)) (X : Data E r) (hp0 : X.p0 = Dw.q)
    (hty : ∀ τ : E →+* ℂ, τ ∈ X.Ψ ↔ τ (H.rt : E) = H.rt0) (D : Datum H) (hp : D.p = Dw.p) (hq : D.q = Dw.q)
    (φ : D.La ≃ₗ[𝓞 E] X.Λ)
    (hEF : ∀ a b, ((D.EF a b : ℤ) : ℚ) = Algebra.trace ℚ E (-X.ξ0 * herm X.Gm (φ a : Fin r → E) (φ b)))
    (x₀ : Frame X.Ψ r) (hx₀ : x₀ ∈ X.dom) (P₀ : D.La →+ (Fin g → ℂ))
    (hP₀ : ∀ a j, P₀ a j = Formalism.L2.PjFree.perFr X x₀ (φ a : Fin r → E) (Formalism.L2.PjFree.relab c σ (e j).1) (e j).2)
    (hper₀ : IsPeriod D (fun j => Formalism.L2.PjFree.relab c σ (e j).1) P₀) (P : D.La →+ (Fin g → ℂ))
    (hper : IsPeriod D (fun j => Formalism.L2.PjFree.relab c σ (e j).1) P) :
    ∃ x ∈ X.dom, ∀ a j, P a j = Formalism.L2.PjFree.perFr X x (φ a : Fin r → E) (Formalism.L2.PjFree.relab c σ (e j).1) (e j).2 := by
  obtain ⟨idx, hi, hper'⟩ := exists_idx hσ hr e X hp0 hty
  have hξ : cc (-X.ξ0) = -(-X.ξ0) := by
    have h := X.ξ0_im
    unfold cc at h ⊢
    rw [map_neg, h]
  have hpos : ∀ τ ∈ X.Ψ, 0 < (τ (-X.ξ0)).im := by
    rcases X.κ0_xi with h | h
    · intro τ hτ
      have := X.κ0_sign ⟨τ, hτ⟩
      rw [h, map_mul, map_ofNat] at this
      rw [map_neg, Complex.neg_im]
      simp at this
      linarith
    · exfalso
      refine not_im_neg H D h1 (-X.ξ0) X.Gm (fun a => (φ a : Fin r → E)) X.Ψ X.cmType idx _ Dw.q hξ X.Gm_herm hEF
        x₀ (hp0 ▸ hx₀) P₀ (fun v k => by rw [hP₀, hper']; rfl) hper₀ fun τ hτ => ?_
      have := X.κ0_sign ⟨τ, hτ⟩
      rw [h, map_neg, map_mul, map_ofNat] at this
      rw [map_neg, Complex.neg_im]
      simp at this
      linarith
  let ψ : D.La →ₗ[𝓞 E] (Fin r → E) := X.Λ.subtype ∘ₗ φ.toLinearMap
  have hψ : Set.range ψ = (X.Λ : Set (Fin r → E)) := by
    ext y
    constructor
    · rintro ⟨a, rfl⟩
      exact (φ a).2
    · intro hy
      exact ⟨φ.symm ⟨y, hy⟩, by simp [ψ]⟩
  obtain ⟨x, hx, hPx⟩ := GlobalTheory.exists_frame_of_isPeriod E H D r (-X.ξ0) X.Gm ψ X.Ψ hty g idx _
    (by rw [hq]; exact hi) hξ hpos
    ⟨fun a b hab => φ.injective (Subtype.ext hab), by rw [hψ]; exact X.Λ_span, X.Gm_herm, X.Gm_det, hEF⟩
    (by rw [hp, hq]; exact hr) P hper
  refine ⟨x, by rw [hq, ← hp0] at hx; exact hx, fun a j => ?_⟩
  rw [hper', hPx, hq]
  rfl

theorem frBor_of_eq {Xo : Moduli Dw l} {c : Coeff l} {S : Type} [CommRing S] [Algebra c.F S]
    (y y' : FrPt Xo c S) (hx : y'.x = y.x) (hu : ∀ τ i, y'.u τ i = y.u τ i) :
    ∃ t : Ix Dw → Sˣ, FrBor t y y' := by
  obtain ⟨g, a, h⟩ := Model.exists_frChg y y' hx
  have ha := Model.FrChg.isUnit h
  refine ⟨fun k => Option.elim k ha.unit (fun _ => 1), (Model.frBor_iff _ _ _).2 ⟨fun _ => 1, fun τ i => ?_,
    fun τ i j hij => Matrix.one_apply_ne hij.ne, hx, fun τ i => ?_, h.2.2⟩⟩
  · exact Matrix.one_apply_eq i
  · rw [hu]
    exact (GlobalTheory.Reg.BorelGroupoid.chg_refl y).2.1 τ i

end GlobalTheory.CompInj

namespace GlobalTheory

open CompInj

theorem card_comp_le_periodSpaces : Out.Laws → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (σ : c.F →+* ℂ) (r : ℕ) (U : Formalism.L2.PjFree.Unf Xo c σ r), 1 ≤ r → Formalism.L2.PjFree.GoodEmb c σ → Formalism.L2.PjFree.IsUnf U → ∃ (g : ℕ) (ty : Fin g → (E →+* ℂ)) (F : FamilyUnif Xo (σ.comp (IntermediateField.inclusion c.le).toRingHom) ty), IsTypeFn H D.p D.q ty ∧ Fintype.card U.Comp ≤ F.n := by
  intro _ E _ _ _ H D l Xo c σ r U h1 hσ hU
  obtain ⟨hr, hX, -, hfib, -, g, e, F, ik, φ, hEF, hP⟩ := hU
  refine ⟨g, _, F, (GlobalTheory.Relab.relab_good E H l c σ hσ).2.2.2 D g e, ?_⟩
  suffices hinj : Function.Injective ik by simpa using Fintype.card_le_of_injective ik hinj
  intro k k' hk
  obtain ⟨x, hx⟩ := dom_nonempty (U.X k)
  obtain ⟨x₀, hx₀⟩ := dom_nonempty (U.X k')
  obtain ⟨P, -, hper, hpt, hder, -⟩ := hP k ⟨x, hx⟩
  obtain ⟨P₀, hP₀, hper₀, -⟩ := hP k' ⟨x₀, hx₀⟩
  have hP' := fun y => (hP k' y).imp fun _ h => (⟨h.1, h.2.2.1, h.2.2.2.1⟩ : _ ∧ _ ∧ _)
  have hEF' := hEF k'
  generalize φ k' = ψ at hP₀ hP' hEF'
  clear hP hEF φ
  generalize ik k' = n at *
  subst hk
  obtain ⟨x', hx', hPx⟩ := exists_frame hσ h1 hr e (U.X k') (hX k').1 (hX k').2 _ (F.sig _).1 (F.sig _).2 ψ hEF'
    x₀ hx₀ P₀ hP₀ hper₀ P hper
  obtain ⟨P', hP', hpt', hder'⟩ := hP' ⟨x', hx'⟩
  obtain rfl : P = P' := by
    ext a j
    rw [hPx, hP']
  have hbor := frBor_of_eq (U.un k ⟨x, hx⟩) (U.un k' ⟨x', hx'⟩) (hpt'.trans hpt.symm) fun τ i =>
    ((GlobalTheory.isDerivAt0_ex_isTanAt E H D l Xo _ g _ F _ P hper).2.1 _).unique (hder' τ i) (hder τ i)
  obtain ⟨γ, -, b, -, h⟩ := (hfib k k' _ _).1 hbor
  exact (congrArg Sigma.fst h).symm

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.ExistsFramedPointBaseChangeAlgHom
section
noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.FramedBaseChange

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
  {Xo : Moduli Dw l} {c : Coeff l}

theorem spMap_spMap {R R' R'' : Type} [CommRing R] [CommRing R'] [CommRing R''] (f : R' →+* R'')
    (g : R →+* R') : spMap f ≫ spMap g = spMap (f.comp g) := by
  unfold spMap
  rw [← Spec.map_comp]
  rfl

theorem dualMap_comp_algebraMap {S T : Type} [CommRing S] [CommRing T] (ψ : S →+* T) :
    (dualMap ψ).comp (algebraMap S (DualNumber S)) = (algebraMap T (DualNumber T)).comp ψ := by
  ext s <;> simp [dualMap, TrivSqZeroExt.algebraMap_eq_inl]

theorem fstHom_comp_dualMap {S T : Type} [CommRing S] [CommRing T] (ψ : S →+* T) :
    (TrivSqZeroExt.fstHom T T T).toRingHom.comp (dualMap ψ) =
      ψ.comp (TrivSqZeroExt.fstHom S S S).toRingHom := by
  ext s <;> simp [dualMap, TrivSqZeroExt.algebraMap_eq_inl]

theorem dualMap_epsMul {S T : Type} [CommRing S] [CommRing T] (ψ : S →+* T) (a : S) :
    (dualMap ψ).comp (epsMul a) = (epsMul (ψ a)).comp (dualMap ψ) := by
  ext s <;> simp [dualMap, epsMul, TrivSqZeroExt.algebraMap_eq_inl]

theorem isTanAt_pull {S T : Type} [CommRing S] [CommRing T] (ψ : S →+* T) {x : Sp S ⟶ Xo.X}
    {v : Sp (DualNumber S) ⟶ Xo.univ.t.G.left} (hv : IsTanAt x v) :
    IsTanAt (spMap ψ ≫ x) (spMap (dualMap ψ) ≫ v) := by
  obtain ⟨h1, h2⟩ := hv
  refine ⟨?_, ?_⟩
  · rw [Category.assoc, h1, ← Category.assoc, spMap_spMap, dualMap_comp_algebraMap, ← spMap_spMap,
      Category.assoc]
  · rw [← Category.assoc, spMap_spMap, fstHom_comp_dualMap, ← spMap_spMap, Category.assoc, h2]
    have e : (Over.homMk (spMap ψ) rfl : Over.mk (spMap ψ ≫ x) ⟶ Over.mk x) ≫
        (1 : Over.mk x ⟶ Xo.univ.t.G) = 1 := by
      simp [Hom.one_def]
    rw [← e, Over.comp_left]
    rfl

theorem isEigAt_pull {S T : Type} [CommRing S] [Algebra c.F S] [CommRing T] [Algebra c.F T] (ψ : S →ₐ[c.F] T)
    (τ : E →+* ℂ) {v : Sp (DualNumber S) ⟶ Xo.univ.t.G.left} (hv : IsEigAt c τ v) :
    IsEigAt c τ (spMap (dualMap ψ.toRingHom) ≫ v) := by
  intro a
  rw [Category.assoc, hv a, ← Category.assoc, spMap_spMap, dualMap_epsMul, ← spMap_spMap,
    Category.assoc]
  congr 3
  exact ψ.commutes _

theorem exists_frMap : Laws → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H)
    (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (S T : Type) [CommRing S] [Algebra c.F S] [CommRing T]
    [Algebra c.F T] (ψ : S →ₐ[c.F] T) (y : FrPt Xo c S), ∃ z : FrPt Xo c T, FrMap ψ y z := by
  intro hLaws E _ _ _ H Dw l Xo c S T _ _ _ _ ψ y
  let h : ptO Xo (spMap ψ.toRingHom ≫ y.x) ⟶ ptO Xo y.x := Over.homMk (spMap ψ.toRingHom) rfl
  obtain ⟨s', hs'⟩ := Formalism.MainNotions.ModuliIntegralCharts.H1.GermD.exists_pullSec Xo.univ.t.G Xo.univ.t.PP.L 1 (h ▷ Xo.univ.t.G)
    (whiskerRight_snd _ _) y.s
  refine ⟨
    { x := spMap ψ.toRingHom ≫ y.x
      x_over := by
        rw [Category.assoc, y.x_over]
        unfold sOf
        rw [spMap_spMap, ← RingHom.comp_assoc]
        congr 2
        ext r
        simp
      u := fun τ i => spMap (dualMap ψ.toRingHom) ≫ y.u τ i
      tan := fun τ i => isTanAt_pull ψ.toRingHom (y.tan τ i)
      eig := fun τ i => isEigAt_pull ψ τ (y.eig τ i)
      basis := fun τ w hw he => _root_.GlobalTheory.frame_baseChange_eigen_basis E H Dw l Xo c S T ψ y τ w hw he
      s := s'
      gen := _root_.GlobalTheory.framedPoint_generator_baseChange hLaws E H Dw l Xo c S T ψ.toRingHom y h rfl s' hs' },
    rfl, fun _ _ => rfl, (h ▷ Xo.univ.t.G).left, ?_, ?_, fun i hi => ?_⟩
  · rw [← Over.comp_left, whiskerRight_snd]
  · rw [← Over.comp_left, whiskerRight_fst, Over.comp_left]
    rfl
  · exact (hs' i).symm

end GlobalTheory.FramedBaseChange
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.ExistsNetDataFromHalfConjugateEmbeddings
section
open NumberField Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Gaps.NetNorms
open scoped ComplexConjugate

namespace GlobalTheory

theorem linearIndependent_conj_coords {ι κ : Type*} [Fintype ι] (v : ι → κ → ℂ)
    (h : LinearIndependent ℂ v) : LinearIndependent ℂ (fun i y => conj (v i y)) := by
  rw [Fintype.linearIndependent_iff] at h ⊢
  intro c hc i
  have h1 : ∑ i, conj (c i) • v i = 0 := by
    funext y
    have := congrArg conj (congrFun hc y)
    set_option synthInstance.maxHeartbeats 100000 in
      simpa [Finset.sum_apply, map_sum] using this
  simpa using h (fun i => conj (c i)) h1 i

theorem exists_netData_of_readings_on_half :
    ∀ (D : D7) (B : WeightFamilies.Prov D) (j : ℕ) (ka : WeightFamilies.Wt D j) (good : (B.KO →+* ℂ) → Prop), (∀ σ, good σ ↔ ¬ good (ComplexEmbedding.conjugate σ)) → (∀ σ F, B.supN j ka (ComplexEmbedding.conjugate σ) F = B.supN j ka σ F) → ∀ (n : (B.KO →+* ℂ) → ℕ) (ev : ∀ σ, Fin (n σ) → (B.Cusp j ka →ₛₗ[σ] ℂ)) (C : ℝ), (∀ σ, good σ → (∀ F, ∃ y, B.supN j ka σ F / 4 ≤ ‖ev σ y F‖) ∧ (∀ y F, ‖ev σ y F‖ ≤ B.supN j ka σ F) ∧ Real.log (16 * (n σ : ℝ)) ≤ C ∧ ∀ (m : ℕ) (F : Fin m → B.Cusp j ka), LinearIndependent B.KO F → LinearIndependent ℂ (fun i => fun y => ev σ y (F i))) → ∃ Nt : NetData B j ka, NetMax Nt ∧ NetLeSup Nt ∧ NetSize Nt C ∧ ∀ σ, NetInj Nt σ := by
  classical
  intro D B j ka good hgood hsup n ev C H
  have cc : ∀ σ : B.KO →+* ℂ, ComplexEmbedding.conjugate (ComplexEmbedding.conjugate σ) = σ := by
    intro σ
    ext a
    simp
  let g : (B.KO →+* ℂ) → (B.KO →+* ℂ) := fun σ => if good σ then σ else ComplexEmbedding.conjugate σ
  have hgc : ∀ σ, ¬ good σ → good (ComplexEmbedding.conjugate σ) := by
    intro σ h
    by_contra h'
    exact h ((hgood σ).2 h')
  have g1 : ∀ σ, good σ → g σ = σ := fun σ h => if_pos h
  have g2 : ∀ σ, ¬ good σ → g σ = ComplexEmbedding.conjugate σ := fun σ h => if_neg h
  have gg : ∀ σ, good (g σ) := by
    intro σ
    by_cases h : good σ
    · rw [g1 σ h]; exact h
    · rw [g2 σ h]; exact hgc σ h
  have gc : ∀ σ, g σ = g (ComplexEmbedding.conjugate σ) := by
    intro σ
    by_cases h : good σ
    · rw [g1 σ h, g2 _ ((hgood σ).1 h), cc]
    · rw [g2 σ h, g1 _ (hgc σ h)]
  have gs : ∀ σ F, B.supN j ka (g σ) F = B.supN j ka σ F := by
    intro σ F
    by_cases h : good σ
    · rw [g1 σ h]
    · rw [g2 σ h, hsup]
  have hcast : ∀ (a b : B.KO →+* ℂ) (h : a = b) (y : Fin (n a)) (F : B.Cusp j ka),
      ev b (finCongr (congrArg n h) y) F = ev a y F := by
    intro a b h y F
    subst h
    rfl
  let ev' : ∀ σ, Fin (n (g σ)) → (B.Cusp j ka →ₛₗ[σ] ℂ) := fun σ y =>
    { toFun := fun F => if good σ then ev (g σ) y F else conj (ev (g σ) y F)
      map_add' := by
        intro F G
        split_ifs <;> simp
      map_smul' := by
        intro a F
        by_cases h : good σ
        · have e : g σ a = σ a := by rw [g1 σ h]
          simp only [if_pos h, map_smulₛₗ, e]
        · have e : g σ a = conj (σ a) := by rw [g2 σ h]; rfl
          simp [if_neg h, map_smulₛₗ, e] }
  have e1 : ∀ σ y F, good σ → ev' σ y F = ev (g σ) y F := fun σ y F h => if_pos h
  have e2 : ∀ σ y F, ¬ good σ → ev' σ y F = conj (ev (g σ) y F) := fun σ y F h => if_neg h
  have en : ∀ σ y F, ‖ev' σ y F‖ = ‖ev (g σ) y F‖ := by
    intro σ y F
    by_cases h : good σ
    · rw [e1 σ y F h]
    · rw [e2 σ y F h, Complex.norm_conj]
  refine ⟨{ NN := fun σ => Fin (n (g σ))
            ev := ev'
            cj := fun σ => finCongr (congrArg n (gc σ))
            ev_conj := ?_ }, ?_, ?_, ?_, ?_⟩
  · intro σ y F
    by_cases h : good σ
    · rw [e2 _ _ _ ((hgood σ).1 h), e1 _ _ _ h, hcast _ _ (gc σ)]
    · rw [e1 _ _ _ (hgc σ h), e2 _ _ _ h, hcast _ _ (gc σ), Complex.conj_conj]
  · intro σ F
    obtain ⟨y, hy⟩ := (H _ (gg σ)).1 F
    refine ⟨y, ?_⟩
    show _ ≤ ‖ev' σ y F‖
    rw [en, ← gs]
    exact hy
  · intro σ y F
    show ‖ev' σ y F‖ ≤ _
    rw [en, ← gs]
    exact (H _ (gg σ)).2.1 y F
  · intro σ
    show Real.log (16 * (Fintype.card (Fin (n (g σ))) : ℝ)) ≤ C
    rw [Fintype.card_fin]
    exact (H _ (gg σ)).2.2.1
  · intro σ m F hF
    have hI := (H _ (gg σ)).2.2.2 m F hF
    show LinearIndependent ℂ (fun i => fun y : Fin (n (g σ)) => ev' σ y (F i))
    by_cases h : good σ
    · simp only [e1 σ _ _ h]
      exact hI
    · simp only [e2 σ _ _ h]
      exact linearIndependent_conj_coords _ hI

end GlobalTheory
end

