module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.UnivFrame
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0010
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0002
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0033
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0028
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0027
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0002
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0032
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0030
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.DetOfTriangular
public import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.NormConst
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0011
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0007
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.Bundle0003
public import Development.AbelianVarietyTheory.PublishedTheorems.Landherr₂.ExistsNormTensor
public import Development.AbelianVarietyTheory.Statements.HyperbolicHypotheses.HypothesesInhabitedHyperbolic

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.UnitaryExistence.LowerTriIsUnitDet
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Frames

namespace GlobalTheory.Frames

section Tri

variable {S : Type} [CommRing S] {n : ℕ}

theorem lowerTri_mul (A B : Matrix (Fin n) (Fin n) S) (hA : ∀ i j, i < j → A i j = 0)
    (hB : ∀ i j, i < j → B i j = 0) : ∀ i j, i < j → (A * B) i j = 0 := by
  first
  | exact @_root_.GlobalTheory.LowerTriangularMul.main
  | exact _root_.GlobalTheory.LowerTriangularMul.main
  | (apply _root_.GlobalTheory.LowerTriangularMul.main <;> assumption)
  | (intros; apply _root_.GlobalTheory.LowerTriangularMul.main <;> assumption)
  | (intros; apply @_root_.GlobalTheory.LowerTriangularMul.main <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.LowerTriangularMul.main ..)

theorem lowerTri_mul_diag (A B : Matrix (Fin n) (Fin n) S) (hA : ∀ i j, i < j → A i j = 0)
    (hB : ∀ i j, i < j → B i j = 0) (i : Fin n) : (A * B) i i = A i i * B i i := by
  rw [Matrix.mul_apply]
  refine Finset.sum_eq_single i (fun k _ hk => ?_) (fun h => absurd (Finset.mem_univ i) h)
  rcases lt_or_gt_of_ne hk with h | h
  · rw [hB k i h, mul_zero]
  · rw [hA i k h, zero_mul]

theorem lowerTri_isUnit_det (A : Matrix (Fin n) (Fin n) S) (hA : ∀ i j, i < j → A i j = 0)
    (hd : ∀ i, IsUnit (A i i)) : IsUnit A.det := by
  have h : A.BlockTriangular OrderDual.toDual := fun i j hij => hA i j hij
  rw [Matrix.det_of_lowerTriangular A h]
  exact IsUnit.prod_univ_iff.mpr hd

theorem lowerTri_inv (A : Matrix (Fin n) (Fin n) S) (hA : ∀ i j, i < j → A i j = 0)
    (hd : IsUnit A.det) : ∀ i j, i < j → A⁻¹ i j = 0 := by
  have h : A.BlockTriangular OrderDual.toDual := fun i j hij => hA i j hij
  letI := Matrix.invertibleOfIsUnitDet A hd
  have h' := Matrix.blockTriangular_inv_of_blockTriangular h
  exact fun i j hij => h' hij

end Tri

theorem frBor_iff_frChg {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H}
    {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {S : Type} [CommRing S] [Algebra c.F S]
    (y y' : FrPt Xo c S) (t : Ix Dw → Sˣ) :
    FrBor t y y' ↔ ∃ g : (∀ τ : E →+* ℂ, Matrix (Fin (Dw.mult τ)) (Fin (Dw.mult τ)) S),
      (∀ τ i j, i < j → g τ i j = 0) ∧ (∀ τ i, g τ i i = (t (some ⟨τ, i⟩) : S)) ∧
        FrChg g (t none : S) y y' := by
  have hid : spMap (RingHom.id S) = 𝟙 _ := by
    show Spec.map (𝟙 (CommRingCat.of S)) = _
    exact Spec.map_id _
  constructor
  · rintro ⟨hx, hu, pm, h1, h2, h3⟩
    choose cf hd hz hc using hu
    refine ⟨fun τ => Matrix.of (cf τ), fun τ i j h => hz τ i j h, hd, hx, hc, pm, h1, ?_, h3⟩
    rw [hid]
    exact h2.trans (Category.comp_id _).symm
  · rintro ⟨g, hz, hd, hx, hc, pm, h1, h2, h3⟩
    refine ⟨hx, fun τ i => ⟨g τ i, hd τ i, hz τ i, hc τ i⟩, pm, h1, ?_, h3⟩
    rw [hid] at h2
    exact h2.trans (Category.comp_id _)

theorem frBor_calculus : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (S : Type) [CommRing S] [Algebra c.F S] (y y' y'' : FrPt Xo c S), (∀ t : Ix Dw → Sˣ, FrBor t y y' ↔ ∃ g : (∀ τ : E →+* ℂ, Matrix (Fin (Dw.mult τ)) (Fin (Dw.mult τ)) S), (∀ τ i j, i < j → g τ i j = 0) ∧ (∀ τ i, g τ i i = (t (some ⟨τ, i⟩) : S)) ∧ FrChg g (t none : S) y y') ∧ (y'.x = y.x → (∀ τ (i : Fin (Dw.mult τ)), ∃ cf : Fin (Dw.mult τ) → S, IsUnit (cf i) ∧ (∀ j, i < j → cf j = 0) ∧ IsCombAt y.x (y.u τ) cf (y'.u τ i)) → ∃ t : Ix Dw → Sˣ, FrBor t y y') ∧ (∀ t t' : Ix Dw → Sˣ, FrBor t y y' → FrBor t' y' y'' → FrBor (t' * t) y y'') ∧ (∀ t : Ix Dw → Sˣ, FrBor t y y' → FrBor t⁻¹ y' y) := by
  intro E _ _ _ H Dw l Xo c S _ _ y y' y''
  refine ⟨frBor_iff_frChg y y', fun hx hu => ?_, fun t t' h h' => ?_, fun t h => ?_⟩
  · obtain ⟨g₀, a, -, -, -, hs⟩ := (_root_.GlobalTheory.Frames.frChg_exists_unique E H Dw l Xo c S y y').1 hx
    choose cf hd hz hc using hu
    refine ⟨fun k => match k with
      | none => a
      | some ⟨τ, i⟩ => (hd τ i).unit, (frBor_iff_frChg y y' _).2
        ⟨fun τ => Matrix.of (cf τ), fun τ i j h => hz τ i j h, fun τ i => ?_, hx, hc, hs⟩⟩
    exact (hd τ i).unit_spec.symm
  · obtain ⟨g, hz, hd, hc⟩ := (frBor_iff_frChg y y' t).1 h
    obtain ⟨g', hz', hd', hc'⟩ := (frBor_iff_frChg y' y'' t').1 h'
    refine (frBor_iff_frChg y y'' _).2 ⟨fun τ => g' τ * g τ,
      fun τ => lowerTri_mul _ _ (hz' τ) (hz τ), fun τ i => ?_, ?_⟩
    · show (g' τ * g τ) i i = _
      rw [lowerTri_mul_diag _ _ (hz' τ) (hz τ), hd, hd', Pi.mul_apply, Units.val_mul]
    · rw [Pi.mul_apply, Units.val_mul]
      exact (_root_.GlobalTheory.Frames.frChg_refl_and_comp E H Dw l Xo c S y y' y'').2 g g' _ _ hc hc'
  · obtain ⟨g, hz, hd, hc⟩ := (frBor_iff_frChg y y' t).1 h
    have hdet : ∀ τ, IsUnit (g τ).det := fun τ =>
      lowerTri_isUnit_det _ (hz τ) fun i => by rw [hd]; exact Units.isUnit _
    have hinv : ∀ τ, (g τ)⁻¹ * g τ = 1 := fun τ => Matrix.nonsing_inv_mul _ (hdet τ)
    have hzi : ∀ τ i j, i < j → (g τ)⁻¹ i j = 0 := fun τ => lowerTri_inv _ (hz τ) (hdet τ)
    obtain ⟨z, hzc, -⟩ := GlobalTheory.T.existsUnique_frameChangeByMatrices E H Dw l Xo c S y' (fun τ => (g τ)⁻¹) (t none)⁻¹
      fun τ => Matrix.isUnit_nonsing_inv_det _ (hdet τ)
    have h1 := (_root_.GlobalTheory.Frames.frChg_refl_and_comp E H Dw l Xo c S y y' z).2 g _ _ _ hc hzc
    simp only [hinv, Units.inv_mul] at h1
    have h0 := (_root_.GlobalTheory.Frames.frChg_refl_and_comp E H Dw l Xo c S y y y).1
    have hzy : z = y := (GlobalTheory.T.existsUnique_frameChangeByMatrices E H Dw l Xo c S y (fun _ => 1) 1 (fun τ => by simp)).unique h1 h0
    subst hzy
    refine (frBor_iff_frChg y' z _).2 ⟨fun τ => (g τ)⁻¹, hzi, fun τ i => ?_, hzc⟩
    have h2 := lowerTri_mul_diag _ _ (hzi τ) (hz τ) i
    rw [hinv, Matrix.one_apply_eq, hd] at h2
    rw [Pi.inv_apply]
    exact Units.eq_inv_of_mul_eq_one_right h2.symm

end GlobalTheory.Frames
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UnitaryExistence.TriangularFrameMovesPeriodBlockTriangular
section
open NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj Formalism.L2.PjFree
open AlgebraicGeometry CategoryTheory Limits ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Frames GlobalTheory.FrameUnif
open scoped Matrix nonZeroDivisors

namespace GlobalTheory.PerBor

lemma inv_support {n α : Type*} [Fintype n] [DecidableEq n] [Fintype α] (t : n → α) (w : n → ℕ)
    (h : Matrix n n ℂ) (hu : IsUnit h.det) (hs : ∀ j j', h j j' ≠ 0 → t j = t j' ∧ w j ≤ w j') :
    ∀ j j', h⁻¹ j j' ≠ 0 → t j = t j' ∧ w j ≤ w j' := by
  letI := Matrix.invertibleOfIsUnitDet h hu
  have key : ∀ ι : α → ℤ, h⁻¹.BlockTriangular (fun j => toLex (ι (t j), w j)) := by
    intro ι
    refine Matrix.blockTriangular_inv_of_blockTriangular ?_
    intro j j' hlt
    by_contra hne
    obtain ⟨h1, h2⟩ := hs j j' hne
    simp only [h1, Prod.Lex.toLex_lt_toLex, lt_self_iff_false, true_and, false_or] at hlt
    omega
  intro j j' hne
  have h1 : ¬ _ := fun hlt => hne (key (fun a => (Fintype.equivFin α a : ℕ)) (i := j) (j := j') hlt)
  have h2 : ¬ _ := fun hlt => hne (key (fun a => -((Fintype.equivFin α a : ℕ) : ℤ)) (i := j) (j := j') hlt)
  simp only [Prod.Lex.toLex_lt_toLex, not_or, not_and, not_lt] at h1 h2
  have h3 : ((Fintype.equivFin α (t j) : ℕ)) = (Fintype.equivFin α (t j') : ℕ) := by omega
  have h4 : t j = t j' := (Fintype.equivFin α).injective (Fin.ext h3)
  exact ⟨h4, h1.2 (by rw [h4])⟩

lemma det_of_support {n α : Type*} [Fintype n] [DecidableEq n] [Fintype α] (t : n → α) (w : n → ℕ)
    (hinj : ∀ j j', t j = t j' → w j = w j' → j = j')
    (h : Matrix n n ℂ) (hs : ∀ j j', h j j' ≠ 0 → t j = t j' ∧ w j ≤ w j') :
    h.det = ∏ j, h j j := by
  refine PerMove.det_of_triangular (fun j => toLex (Fintype.equivFin α (t j), w j)) ?_ _ fun k l hkl => ?_
  · intro k l hkl
    have h' := toLex.injective hkl
    rw [Prod.mk.injEq] at h'
    exact hinj _ _ ((Fintype.equivFin α).injective h'.1) h'.2
  · by_contra hne
    obtain ⟨h1, h2⟩ := hs k l hne
    simp only [h1, Prod.Lex.toLex_lt_toLex, lt_self_iff_false, true_and, false_or] at hkl
    omega

lemma inv_diag {n α : Type*} [Fintype n] [DecidableEq n] [Fintype α] (t : n → α) (w : n → ℕ)
    (hinj : ∀ j j', t j = t j' → w j = w j' → j = j')
    (h : Matrix n n ℂ) (hu : IsUnit h.det) (hs : ∀ j j', h j j' ≠ 0 → t j = t j' ∧ w j ≤ w j') (a : n) :
    h⁻¹ a a = (h a a)⁻¹ := by
  have e := congrFun (congrFun (Matrix.nonsing_inv_mul h hu) a) a
  rw [Matrix.mul_apply, Finset.sum_eq_single a, Matrix.one_apply_eq] at e
  · exact eq_inv_of_mul_eq_one_left e
  · intro c _ hc
    by_contra hne
    obtain ⟨h1, h2⟩ := mul_ne_zero_iff.1 hne
    obtain ⟨h3, h4⟩ := inv_support t w h hu hs _ _ h1
    obtain ⟨_, h6⟩ := hs _ _ h2
    exact hc (hinj _ _ h3.symm (by omega))
  · simp

noncomputable def moveMat {E : Type} [Field E] {Ψ : Finset (E →+* ℂ)} {r g : ℕ} (q : ℕ) (idx : Fin g ≃ Ψ × Fin r)
    (b : Frame Ψ r) : Matrix (Fin g) (Fin g) ℂ :=
  open Classical in
  Matrix.of fun k l => if (idx l).1 = (idx k).1 then
      (if ((idx k).2 : ℕ) < q then FD.mat b (idx k).1 (idx l).2 (idx k).2
        else (FD.mat b (idx k).1)⁻¹ (idx k).2 (idx l).2) else 0

section

variable {E : Type} [Field E] {Ψ : Finset (E →+* ℂ)} {r g : ℕ} (q : ℕ) (idx : Fin g ≃ Ψ × Fin r)
    {b : Frame Ψ r}

lemma moveMat_diag (hb : b ∈ Bor Ψ r) (k : Fin g) : moveMat q idx b k k =
    if ((idx k).2 : ℕ) < q then b (idx k).1 (idx k).2 (idx k).2 else (b (idx k).1 (idx k).2 (idx k).2)⁻¹ := by
  simp only [moveMat, Matrix.of_apply, if_true]
  split_ifs with hk
  · rfl
  · exact PerMove.bor_inv_diag hb _ _

lemma moveMat_support (hb : b ∈ Bor Ψ r) (k l : Fin g) (h : moveMat q idx b k l ≠ 0) :
    (idx l).1 = (idx k).1 ∧ (if ((idx k).2 : ℕ) < q then ((idx l).2 : ℕ) ≤ (idx k).2
      else ((idx k).2 : ℕ) ≤ (idx l).2) := by
  simp only [moveMat, Matrix.of_apply] at h
  by_cases hτ : (idx l).1 = (idx k).1
  · rw [if_pos hτ] at h
    refine ⟨hτ, ?_⟩
    split_ifs at h ⊢ with hk
    · by_contra hlt
      exact h (PerMove.bor_tri hb _ (show (idx k).2 < (idx l).2 by rw [Fin.lt_def]; omega))
    · by_contra hlt
      exact h (PerMove.bor_inv_tri hb _ (show (idx l).2 < (idx k).2 by rw [Fin.lt_def]; omega))
  · rw [if_neg hτ] at h
    exact absurd rfl h

lemma moveMat_mulVec (hb : b ∈ Bor Ψ r) (Gm : Matrix (Fin r) (Fin r) E) (x : Frame Ψ r) (v : Fin r → E)
    (P P' : Fin g → ℂ)
    (hP : ∀ k, P k = if ((idx k).2 : ℕ) < q then
      FD.hermC (idx k).1.1 Gm (FD.col (FD.mat x (idx k).1) (idx k).2) (FD.Data.emb (idx k).1.1 v)
      else ((FD.mat x (idx k).1)⁻¹ *ᵥ FD.Data.emb (idx k).1.1 v) (idx k).2)
    (hP' : ∀ k, P' k = if ((idx k).2 : ℕ) < q then
      FD.hermC (idx k).1.1 Gm (FD.col (FD.mat (rmul x b) (idx k).1) (idx k).2) (FD.Data.emb (idx k).1.1 v)
      else ((FD.mat (rmul x b) (idx k).1)⁻¹ *ᵥ FD.Data.emb (idx k).1.1 v) (idx k).2) :
    P' = moveMat q idx b *ᵥ P := by
  funext k
  have hm : FD.mat (FD.rmul x b) (idx k).1 = FD.mat x (idx k).1 * FD.mat b (idx k).1 := rfl
  rw [hP', hm]
  simp only [moveMat, Matrix.mulVec, dotProduct, Matrix.of_apply]
  rw [← idx.symm.sum_comp, Fintype.sum_prod_type, Finset.sum_eq_single (idx k).1]
  · simp only [Equiv.apply_symm_apply, if_true, hP]
    split_ifs with hk
    · rw [PerMove.hermC_col_mul]
      refine Finset.sum_congr rfl fun c _ => ?_
      split_ifs with hc
      · rfl
      · rw [PerMove.bor_tri hb (idx k).1 (show (idx k).2 < c by rw [Fin.lt_def]; omega),
          zero_mul, zero_mul]
    · change ((FD.mat x (idx k).1 * FD.mat b (idx k).1)⁻¹ *ᵥ FD.Data.emb (idx k).1.1 v)
        (idx k).2 = _
      rw [Matrix.mul_inv_rev, ← Matrix.mulVec_mulVec, Matrix.mulVec, dotProduct]
      refine Finset.sum_congr rfl fun c _ => ?_
      split_ifs with hc
      · rw [PerMove.bor_inv_tri hb (idx k).1 (show c < (idx k).2 by rw [Fin.lt_def]; omega),
          zero_mul, zero_mul]
      · rfl
  · intro τ _ hτ
    simp [hτ]
  · simp

end

end GlobalTheory.PerBor

theorem GlobalTheory.per_bor : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (σ : c.F →+* ℂ) (g : ℕ) (e : Fin g ≃ Σ τ : E →+* ℂ, Fin (Dw.mult τ)) (F : FamilyUnif Xo (σ.comp (IntermediateField.inclusion c.le).toRingHom) (fun j => relab c σ (e j).1)) (r : ℕ) (M : ModelsOf F r), GoodEmb c σ → ModelBase M → NegXi M → ∀ k Pf, IsPerFr e F M k Pf → ∀ x ∈ (M.X k).dom, ∀ b ∈ Bor (M.X k).Ψ r, ∃ h₀ : Matrix (Fin g) (Fin g) ℂ, IsUnit h₀.det ∧ (∀ a, Pf (rmul x b) a = h₀ *ᵥ Pf x a) ∧ (∀ j j', h₀⁻¹ j j' ≠ 0 → (e j).1 = (e j').1 ∧ ((e j).2 : ℕ) ≤ (e j').2) ∧ ‖h₀.det‖ = ∏ j, ‖h₀ j j‖ ∧ ((∀ τ i, ‖b τ i i‖ = 1) → ‖h₀.det‖ = 1) ∧ ∀ (un : ∀ k, (M.X k).dom → FrPt Xo c (CAt σ)) (a : (E →+* ℂ) × ℕ → ℕ) (n : ℕ) (t₀ : ℂ), Even n → t₀ ^ 2 * h₀.det = 1 → (∏ j, h₀⁻¹ j j ^ a ((e j).1, (e j).2)) * t₀ ^ n = bchar (laU (unfOf e F M un) a n k) b := by
  intro E _ _ _ H Dw l Xo c σ g e F r M hG hB hN k Pf hPf x hx b hb
  obtain ⟨⟨idx, hty, hcol, hper⟩, hp0, -⟩ := _root_.GlobalTheory.FrameUnif.letter_column_dictionary E H Dw l Xo c σ g e F r M hG hB hN k
  obtain ⟨hbij, hrt, -, -⟩ := GlobalTheory.Relab.relab_good E H l c σ hG
  have hq : (F.Di k).q = Dw.q := hp0.symm.trans (hB.type k).1
  have hlt : ∀ j, ((idx j).2 : ℕ) < (F.Di k).q → ((e j).2 : ℕ) < (F.Di k).q := by
    intro j hj
    have h1 := hty j
    rw [if_pos hj] at h1
    have h2 := ((M.X k).cmType _).1 (idx j).1.2
    rw [← h1, (hB.type k).2, hrt] at h2
    have h3 : Dw.mult (e j).1 = Dw.q := if_neg h2
    have := (e j).2.isLt
    omega
  have hinj : ∀ j j', (e j).1 = (e j').1 → ((e j).2 : ℕ) = (e j').2 → j = j' := by
    intro j j' h1 h2
    apply e.injective
    refine Sigma.ext h1 ((Fin.heq_ext_iff (by rw [h1])).2 h2)
  have hs : ∀ j j', PerBor.moveMat (F.Di k).q idx b j j' ≠ 0 →
      (e j).1 = (e j').1 ∧ ((e j).2 : ℕ) ≤ (e j').2 := by
    intro j j' hne
    obtain ⟨h1, h2⟩ := PerBor.moveMat_support _ idx hb j j' hne
    have c1 := hcol j
    have c2 := hcol j'
    have l1 := hlt j
    have l2 := hlt j'
    have t1 := hty j
    have t2 := hty j'
    by_cases hj : ((idx j).2 : ℕ) < (F.Di k).q
    · rw [if_pos hj] at h2 c1 t1
      have hj' : ((idx j').2 : ℕ) < (F.Di k).q := by omega
      rw [if_pos hj'] at c2 t2
      refine ⟨hbij.1 (by rw [t1, t2, h1]), ?_⟩
      have := l1 hj
      have := l2 hj'
      omega
    · rw [if_neg hj] at h2 c1 t1
      have hj' : ¬ ((idx j').2 : ℕ) < (F.Di k).q := by omega
      rw [if_neg hj'] at c2 t2
      refine ⟨hbij.1 (by rw [t1, t2, h1]), ?_⟩
      omega
  have hdet := PerBor.det_of_support _ _ hinj _ hs
  have hdiag := PerBor.moveMat_diag (F.Di k).q idx hb
  have hbne : ∀ τ i, b τ i i ≠ 0 := fun τ i => PerMove.bor_diag_ne hb τ i
  have hu : IsUnit (PerBor.moveMat (F.Di k).q idx b).det := by
    rw [hdet, isUnit_iff_ne_zero]
    refine Finset.prod_ne_zero_iff.2 fun j _ => ?_
    rw [hdiag]
    split_ifs
    · exact hbne _ _
    · exact inv_ne_zero (hbne _ _)
  refine ⟨PerBor.moveMat (F.Di k).q idx b, hu, fun a => ?_, PerBor.inv_support _ _ _ hu hs,
    by rw [hdet, norm_prod], fun h1 => ?_, fun un a n t₀ hn ht => ?_⟩
  · exact PerBor.moveMat_mulVec _ idx hb (M.X k).Gm x (M.φ k a : Fin r → E) _ _
      (fun j => by rw [hPf, hper]) (fun j => by rw [hPf, hper])
  · rw [hdet, norm_prod]
    refine Finset.prod_eq_one fun j _ => ?_
    rw [hdiag]
    split_ifs
    · exact h1 _ _
    · rw [norm_inv, h1, inv_one]
  · obtain ⟨m, rfl⟩ := hn
    have ht2 : t₀ ^ 2 = ∏ j, (PerBor.moveMat (F.Di k).q idx b j j)⁻¹ := by
      rw [Finset.prod_inv_distrib, ← hdet]
      exact eq_inv_of_mul_eq_one_left ht
    rw [← two_mul, pow_mul, ht2, ← Finset.prod_pow, ← Finset.prod_mul_distrib]
    unfold bchar
    refine Eq.trans ?_ (Fintype.prod_prod_type'
      (fun (τ : (M.X k).Ψ) (i : Fin r) => b τ i i ^ laU (unfOf e F M un) a (2 * m) k τ i))
    rw [← idx.prod_comp]
    refine Finset.prod_congr rfl fun j _ => ?_
    rw [PerBor.inv_diag _ _ hinj _ hu hs, ← pow_add, hdiag]
    have hm' : 2 * m / 2 = m := by omega
    have hp : ((unfOf e F M un).X k).p0 = (F.Di k).q := hp0
    have c1 := hcol j
    have t1 := hty j
    have hinv := Function.leftInverse_invFun hbij.1 (e j).1
    unfold laU
    rw [hp, hm']
    by_cases hj : ((idx j).2 : ℕ) < (F.Di k).q
    · rw [if_pos hj] at c1 t1
      have := hlt j hj
      have t2 : conjEmb (idx j).1.1 = relab c σ (e j).1 := t1.symm
      rw [if_pos hj, if_neg (by omega), t2, hinv,
        show (F.Di k).q - 1 - ((idx j).2 : ℕ) = (e j).2 by omega, inv_pow, ← zpow_natCast, ← zpow_neg]
      congr 1
      push_cast
      ring
    · rw [if_neg hj] at c1 t1
      rw [if_neg hj, if_pos (by omega), ← t1, hinv,
        show ((idx j).2 : ℕ) - (F.Di k).q = (e j).2 by omega, inv_inv, ← zpow_natCast]
      congr 1
end

