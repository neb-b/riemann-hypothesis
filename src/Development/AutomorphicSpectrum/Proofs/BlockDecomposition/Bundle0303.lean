module

public import Mathlib
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.IsotropicMahlerBounds.LogAbsoluteWedges.LogAbsBasic
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0004
public import GroundTheory.AutomorphicForms.Bundle0024
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.HodgeSurjectivity.FormUniq
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.HodgeSurjectivity.NLeA
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.CechPairings.Imports
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.ChartGrConst
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HodgeXD

@[expose] public section

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LogAbsBasicFacts
section
noncomputable section

open NumberField IsDedekindDomain PositivityTheory.Rg.BcB PositivityTheory.Rg.BcB.D1 GlobalTheory.CuspRep

namespace GlobalTheory.CompanionTheory.LogAbs

variable {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E]

theorem norm_cW_eq_one (u : Ad E) (hu : IsUnit u) : ∀ᶠ w in Filter.cofinite, ‖cW w u‖ = 1 := by
  have h := (FiniteAdeleRing.isUnit_iff.1 (hu.map (pFin E))).2
  filter_upwards [h] with w hw
  have e : cW w u = (pFin E u) w := rfl
  rw [e, FinitePlace.norm_def, hw]
  simp

theorem support_log_finite (u : Ad E) (hu : IsUnit u) :
    (Function.support fun w => Real.log ‖cW w u‖).Finite := by
  refine (Filter.eventually_cofinite.1 (norm_cW_eq_one u hu)).subset fun w hw h1 => hw ?_
  simp [h1]

theorem logAbs_mul (u u' : Ad E) (hu : IsUnit u) (hu' : IsUnit u') :
    logAbs (u * u') = logAbs u + logAbs u' := by
  have h1 : ∀ v, Real.log (‖cV v (u * u')‖ ^ 2) = Real.log (‖cV v u‖ ^ 2) + Real.log (‖cV v u'‖ ^ 2) := fun v => by
    rw [map_mul, norm_mul, mul_pow, Real.log_mul
      (pow_ne_zero 2 (norm_ne_zero_iff.2 (hu.map (cV v)).ne_zero))
      (pow_ne_zero 2 (norm_ne_zero_iff.2 (hu'.map (cV v)).ne_zero))]
  have h2 : ∀ w, Real.log ‖cW w (u * u')‖ = Real.log ‖cW w u‖ + Real.log ‖cW w u'‖ := fun w => by
    rw [map_mul, norm_mul, Real.log_mul (norm_ne_zero_iff.2 (hu.map (cW w)).ne_zero)
      (norm_ne_zero_iff.2 (hu'.map (cW w)).ne_zero)]
  unfold logAbs
  simp only [h1, h2]
  rw [Finset.sum_add_distrib, finsum_add_distrib (support_log_finite u hu) (support_log_finite u' hu')]
  ring

theorem norm_cV_algebraMap (v : InfinitePlace E) (c : E) : ‖cV v (algebraMap E (Ad E) c)‖ = v c := by
  rw [← InfinitePlace.norm_embedding_eq]
  exact congrArg norm (pInf_algebraMap c v)

theorem norm_cW_algebraMap (w : HeightOneSpectrum (𝓞 E)) (c : E) :
    ‖cW w (algebraMap E (Ad E) c)‖ = FinitePlace.mk w c := rfl

theorem logAbs_algebraMap (c : E) (hc : c ≠ 0) : logAbs (algebraMap E (Ad E) c) = 0 := by
  have hprod := prod_abs_eq_one hc
  have hA : (∏ w : InfinitePlace E, w c ^ w.mult) ≠ 0 := left_ne_zero_of_mul_eq_one hprod
  have hB : (∏ᶠ w : FinitePlace E, w c) ≠ 0 := right_ne_zero_of_mul_eq_one hprod
  have hlog := congrArg Real.log hprod
  rw [Real.log_mul hA hB, Real.log_one, Real.log_prod (fun w _ => pow_ne_zero _ ((InfinitePlace.pos_iff.2 hc).ne')),
    Real.log_finprod fun w : FinitePlace E => FinitePlace.pos_iff.2 hc] at hlog
  have hm : ∀ v : InfinitePlace E, v.mult = 2 := fun v =>
    InfinitePlace.mult_isComplex ⟨v, IsTotallyComplex.isComplex v⟩
  unfold logAbs
  simp only [norm_cV_algebraMap, norm_cW_algebraMap]
  simp only [hm] at hlog
  rw [← hlog, ← finsum_comp_equiv (FinitePlace.equivHeightOneSpectrum (K := E)).symm]
  rfl

theorem logAbsBasic : LogAbsBasic := fun _ _ _ _ =>
  ⟨support_log_finite, logAbs_mul, logAbs_algebraMap⟩

end GlobalTheory.CompanionTheory.LogAbs

end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MahlerBoundOfDegree
section
noncomputable section

open NumberField Matrix GlobalTheory.CuspRep GlobalTheory.UnitaryBC PositivityTheory.Rg.Tf.Loc PositivityTheory.Rg.BcB PositivityTheory.Rg.BcB.D1

namespace GlobalTheory.CompanionTheory.Cutoff

section Img

variable {K : Type} [Field K] {n : ℕ}

def imgEquiv (g : GL (Fin n) K) : (Fin n → K) ≃ₗ[K] (Fin n → K) :=
  LinearEquiv.ofLinear (Matrix.toLin' g.val) (Matrix.toLin' (g⁻¹ : GL (Fin n) K).val)
    (by rw [← Matrix.toLin'_mul, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.toLin'_one])
    (by rw [← Matrix.toLin'_mul, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.toLin'_one])

theorem img_eq_map (g : GL (Fin n) K) (W : Submodule K (Fin n → K)) :
    img g W = W.map ((imgEquiv g : (Fin n → K) ≃ₗ[K] (Fin n → K)) : (Fin n → K) →ₗ[K] (Fin n → K)) := rfl

theorem finrank_img (g : GL (Fin n) K) (W : Submodule K (Fin n → K)) :
    Module.finrank K (img g W) = Module.finrank K W := by
  rw [img_eq_map]
  exact LinearEquiv.finrank_map_eq _ _

theorem img_top (g : GL (Fin n) K) : img g (⊤ : Submodule K (Fin n → K)) = ⊤ := by
  rw [img_eq_map, Submodule.map_top]
  exact LinearEquiv.range _

theorem img_img_inv (g : GL (Fin n) K) (W : Submodule K (Fin n → K)) :
    img g (img (g⁻¹ : GL (Fin n) K) W) = W := by
  unfold img
  rw [← Submodule.map_comp, ← Matrix.toLin'_mul, ← Units.val_mul, mul_inv_cancel, Units.val_one,
    Matrix.toLin'_one, Submodule.map_id]

end Img

theorem mem_cutSet_of_mem (hR : DegRat) {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] {n : ℕ} {τ : ℝ}
    (g : GL (Fin n) E) {x : GA E n} (hx : x ∈ cutSet E n τ) : ratGL E n g * x ∈ cutSet E n τ := by
  have hx' : (∀ W : Submodule E (Fin n → E), deg x W ≤ prof n τ (Module.finrank E W)) ∧ -τ ≤ deg x ⊤ := hx
  show (∀ W : Submodule E (Fin n → E), deg (ratGL E n g * x) W ≤ prof n τ (Module.finrank E W)) ∧
    -τ ≤ deg (ratGL E n g * x) ⊤
  refine ⟨fun W => ?_, ?_⟩
  · have h := hR E n x g (img (g⁻¹ : GL (Fin n) E) W)
    rw [img_img_inv] at h
    rw [h, ← finrank_img (g⁻¹ : GL (Fin n) E) W]
    exact hx'.1 _
  · have h := hR E n x g ⊤
    rw [img_top] at h
    rw [h]
    exact hx'.2

theorem mahler_of : DegBdd → DegRat → MahlerC → Mahler := by
  intro hB hR hM E _ _ _ n τ
  refine ⟨?_, ?_, ?_⟩
  · have hset : cutSet E n τ = (⋂ W : Submodule E (Fin n → E), {x : GA E n | deg x W ≤ prof n τ (Module.finrank E W)}) ∩
        {x : GA E n | -τ ≤ deg x ⊤} := by
      ext x
      simp [cutSet]
    rw [hset]
    exact (isClosed_iInter fun W => isClosed_le ((hB E n).2 W) continuous_const).inter
      (isClosed_le continuous_const ((hB E n).2 ⊤))
  · intro g x
    constructor
    · intro h
      have h' := mem_cutSet_of_mem hR (g⁻¹) h
      rwa [map_inv, inv_mul_cancel_left] at h'
    · exact mem_cutSet_of_mem hR g
  · obtain ⟨C, hC, hsub⟩ := hM E n (|τ| * (2 * n + 1) ^ 2)
    refine ⟨C, hC, fun x hx => ?_⟩
    have hx' : (∀ W : Submodule E (Fin n → E), deg x W ≤ prof n τ (Module.finrank E W)) ∧ -τ ≤ deg x ⊤ := hx
    have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    have hτ : τ ≤ |τ| := le_abs_self τ
    have hτ0 : 0 ≤ |τ| := abs_nonneg τ
    apply hsub x
    · intro W hW
      have h1 := hx'.1 W
      rw [hW] at h1
      simp only [prof] at h1
      push_cast at h1
      nlinarith [mul_nonneg hτ0 hn, mul_nonneg (sub_nonneg.2 hτ) hn, mul_nonneg hτ0 (mul_nonneg hn hn)]
    · have h1 := hx'.1 ⊤
      rw [finrank_top, Module.finrank_fin_fun] at h1
      simp only [prof] at h1
      have h2 := hx'.2
      rw [abs_le]
      constructor
      · nlinarith [mul_nonneg hτ0 hn, mul_nonneg hτ0 (mul_nonneg hn hn)]
      · nlinarith [mul_nonneg hτ0 hn, mul_nonneg hτ0 (mul_nonneg hn hn),
          mul_nonneg (sub_nonneg.2 hτ) (mul_nonneg hn (by linarith : (0 : ℝ) ≤ n + 1))]

end GlobalTheory.CompanionTheory.Cutoff

end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ModulusCharacterLevi
section
set_option maxSynthPendingDepth 1

open GlobalTheory.SmGL
open GroundTheory.Automorphic.Parabolic (levi parabolicInd jacquetRep JacquetModule sqrtModular leviIncl cellLeviSub normInducing unipotentRadical)
open GroundTheory.Automorphic.Iwasawa (blockUpper)
open GroundTheory.Automorphic (permGL indRep)
open DoubleCoset (doubleCoset)

namespace GlobalTheory.CompanionTheory.DeltaLevi

open GroundTheory.Automorphic.Measures

theorem prod_pairs_le {α G : Type} [Fintype α] [LinearOrder α] [CommGroup G] (n : α → ℕ) (x : α → G) :
    ∏ c : α × α, (if c.1 ≤ c.2 then x c.1 ^ (n c.2 : ℤ) * (x c.2)⁻¹ ^ (n c.1 : ℤ) else 1) =
      ∏ a, x a ^ ((∑ b with a < b, (n b : ℤ)) - ∑ b with b < a, (n b : ℤ)) := by
  have hz : ∀ (y : G) (f : α → ℤ), ∏ b, y ^ f b = y ^ ∑ b, f b := by
    intro y f
    induction (Finset.univ : Finset α) using Finset.induction_on with
    | empty => simp
    | insert a s ha ih => rw [Finset.prod_insert ha, Finset.sum_insert ha, ih, zpow_add]
  have h1 : ∀ c : α × α, (if c.1 ≤ c.2 then x c.1 ^ (n c.2 : ℤ) * (x c.2)⁻¹ ^ (n c.1 : ℤ) else 1) =
      x c.1 ^ (if c.1 ≤ c.2 then (n c.2 : ℤ) else 0) *
        x c.2 ^ (-(if c.1 ≤ c.2 then (n c.1 : ℤ) else 0)) := by
    intro c
    split_ifs <;> simp
  simp only [h1]
  rw [Finset.prod_mul_distrib, Fintype.prod_prod_type, Fintype.prod_prod_type,
    Finset.prod_comm (s := Finset.univ) (t := Finset.univ)
      (f := fun a b => x b ^ (-(if a ≤ b then (n a : ℤ) else 0))), ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun a _ => ?_
  dsimp only
  rw [hz, hz, ← zpow_add, Finset.sum_neg_distrib, Finset.sum_filter, Finset.sum_filter,
    ← sub_eq_add_neg, ← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib]
  congr 1
  refine Finset.sum_congr rfl fun b _ => ?_
  rcases lt_trichotomy a b with h | h | h
  · simp [h, h.le, h.not_ge, h.not_gt]
  · simp [h]
  · simp [h, h.le, h.not_ge, h.not_gt]

section

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  {α : Type} [Fintype α] [LinearOrder α] {N : ℕ} {m : α → Type} [∀ i, Fintype (m i)]
  [∀ i, DecidableEq (m i)]

theorem leviEmb_eq_zero (e : (Σ i, m i) ≃ Fin N) (g : Levi k m) {i j : Fin N}
    (h : blk e i ≠ blk e j) : (leviEmb k e g : Matrix (Fin N) (Fin N) k) i j = 0 := by
  obtain ⟨⟨a, i⟩, rfl⟩ := e.surjective i
  obtain ⟨⟨b, j⟩, rfl⟩ := e.surjective j
  exact leviEmb_apply_ne k e g (by simpa using h) i j

theorem det_adLie_pairs (e : (Σ i, m i) ≃ Fin N) (β : Fin N → ℕ)
    (hβ : ∀ x y, β x < β y ↔ blk e x < blk e y) (p : blockUpper k N β) (g : Levi k m)
    (hp : (p : GL (Fin N) k) = leviEmb k e g) :
    (LinearEquiv.det (adLie k N β p) : k) =
      ∏ c : α × α, if c.1 ≤ c.2 then
        ((g c.1 : GL (m c.1) k) : Matrix (m c.1) (m c.1) k).det ^ Fintype.card (m c.2) *
          ((((g c.2)⁻¹ : GL (m c.2) k)) : Matrix (m c.2) (m c.2) k).det ^ Fintype.card (m c.1)
      else 1 := by
  classical
  set P : Matrix (Fin N) (Fin N) k := ((p : GL (Fin N) k) : Matrix (Fin N) (Fin N) k) with hPdef
  set Q : Matrix (Fin N) (Fin N) k :=
    (((p : GL (Fin N) k)⁻¹ : GL (Fin N) k) : Matrix (Fin N) (Fin N) k) with hQdef
  have hP : P = (leviEmb k e g : Matrix (Fin N) (Fin N) k) := by rw [hPdef, hp]
  have hQ : Q = (leviEmb k e g⁻¹ : Matrix (Fin N) (Fin N) k) := by rw [hQdef, hp, map_inv]
  let A : (ParabolicIndex N β → k) →ₗ[k] (ParabolicIndex N β → k) :=
    (((parabolicCoord k N β).symm.trans ((adLie k N β p).trans (parabolicCoord k N β))) :
      (ParabolicIndex N β → k) →ₗ[k] (ParabolicIndex N β → k))
  have hdet : (LinearEquiv.det (adLie k N β p) : k) = LinearMap.det A := by
    rw [← LinearEquiv.det_conj (adLie k N β p) (parabolicCoord k N β), LinearEquiv.coe_det]
    rfl
  have hM : ∀ s t, LinearMap.toMatrix' A s t = P s.1.1 t.1.1 * Q t.1.2 s.1.2 := by
    intro s t
    rw [LinearMap.toMatrix'_apply]
    show ((adLie k N β p ((parabolicCoord k N β).symm (Pi.single t 1)) : lieParabolic k N β) :
      Matrix (Fin N) (Fin N) k) s.1.1 s.1.2 = _
    rw [coe_adLie, coe_parabolicCoord_symm_single, mul_single_mul_apply]
  let κ : ParabolicIndex N β → α ×ₗ α := fun s => toLex (blk e s.1.1, blk e s.1.2)
  have hzero : ∀ s t, κ s ≠ κ t → LinearMap.toMatrix' A s t = 0 := by
    intro s t hst
    rw [hM]
    by_cases h1 : blk e s.1.1 = blk e t.1.1
    · have h2 : blk e t.1.2 ≠ blk e s.1.2 := by
        intro h2
        exact hst (by simp only [κ, h1, h2])
      rw [hQ, leviEmb_eq_zero e _ h2, mul_zero]
    · rw [hP, leviEmb_eq_zero e _ h1, zero_mul]
  have hBT : (LinearMap.toMatrix' A).BlockTriangular κ := fun s t hts => hzero s t hts.ne'
  have hblock : ∀ a b : α, ((LinearMap.toMatrix' A).toSquareBlock κ (toLex (a, b))).det =
      if a ≤ b then
        ((g a : GL (m a) k) : Matrix (m a) (m a) k).det ^ Fintype.card (m b) *
          ((((g b)⁻¹ : GL (m b) k)) : Matrix (m b) (m b) k).det ^ Fintype.card (m a)
      else 1 := by
    intro a b
    by_cases hab : a ≤ b
    · rw [if_pos hab]
      have hmem : ∀ (i : m a) (j : m b), ¬ β (e ⟨b, j⟩) < β (e ⟨a, i⟩) := by
        intro i j
        rw [hβ]
        simpa using hab
      let f : m a × m b → {t : ParabolicIndex N β // κ t = toLex (a, b)} := fun x =>
        ⟨⟨(e ⟨a, x.1⟩, e ⟨b, x.2⟩), hmem x.1 x.2⟩, by simp [κ]⟩
      have hf : Function.Bijective f := by
        constructor
        · rintro ⟨i, j⟩ ⟨i', j'⟩ h
          have h1 := congrArg (fun t => t.1.1.1) h
          have h2 := congrArg (fun t => t.1.1.2) h
          simp only [f] at h1 h2
          have h1' := e.injective h1
          have h2' := e.injective h2
          simp only [Sigma.mk.injEq, heq_eq_eq, true_and] at h1' h2'
          rw [h1', h2']
        · rintro ⟨⟨⟨i, j⟩, hij⟩, hκ⟩
          obtain ⟨⟨a', i⟩, rfl⟩ := e.surjective i
          obtain ⟨⟨b', j⟩, rfl⟩ := e.surjective j
          have h3 : a' = a ∧ b' = b := by simpa [κ] using hκ
          obtain ⟨rfl, rfl⟩ := h3
          exact ⟨(i, j), rfl⟩
      rw [← Matrix.det_submatrix_equiv_self (Equiv.ofBijective f hf)]
      have hk : ((LinearMap.toMatrix' A).toSquareBlock κ (toLex (a, b))).submatrix
          (Equiv.ofBijective f hf) (Equiv.ofBijective f hf) =
          Matrix.kroneckerMap (· * ·) ((g a : GL (m a) k) : Matrix (m a) (m a) k)
            ((((g b)⁻¹ : GL (m b) k)) : Matrix (m b) (m b) k).transpose := by
        ext ⟨i, j⟩ ⟨i', j'⟩
        show LinearMap.toMatrix' A (f (i, j)).1 (f (i', j')).1 = _
        rw [hM, hP, hQ]
        show (leviEmb k e g : Matrix (Fin N) (Fin N) k) (e ⟨a, i⟩) (e ⟨a, i'⟩) *
          (leviEmb k e g⁻¹ : Matrix (Fin N) (Fin N) k) (e ⟨b, j'⟩) (e ⟨b, j⟩) = _
        rw [leviEmb_apply_same, leviEmb_apply_same]
        rfl
      rw [hk, Matrix.det_kronecker, Matrix.det_transpose]
    · rw [if_neg hab]
      have : IsEmpty {t : ParabolicIndex N β // κ t = toLex (a, b)} := by
        refine ⟨fun t => hab ?_⟩
        have h3 : blk e t.1.1.1 = a ∧ blk e t.1.1.2 = b := by simpa [κ] using t.2
        have h4 := t.1.2
        rw [hβ, h3.1, h3.2] at h4
        exact not_lt.1 h4
      exact Matrix.det_isEmpty
  rw [hdet, ← LinearMap.det_toMatrix', hBT.det]
  rw [Finset.prod_subset (Finset.subset_univ _) (fun c _ hc => by
    have : IsEmpty {t : ParabolicIndex N β // κ t = c} :=
      ⟨fun t => hc (Finset.mem_image.2 ⟨t.1, Finset.mem_univ _, t.2⟩)⟩
    exact Matrix.det_isEmpty)]
  rw [← Equiv.prod_comp toLex]
  exact Finset.prod_congr rfl fun c _ => hblock c.1 c.2

theorem det_adLie_levi (e : (Σ i, m i) ≃ Fin N) (β : Fin N → ℕ)
    (hβ : ∀ x y, β x < β y ↔ blk e x < blk e y) (p : blockUpper k N β) (g : Levi k m)
    (hp : (p : GL (Fin N) k) = leviEmb k e g) :
    LinearEquiv.det (adLie k N β p) = ∏ a, Matrix.GeneralLinearGroup.det (g a) ^ modExp m a := by
  have h := prod_pairs_le (fun a => Fintype.card (m a))
    (fun a => Matrix.GeneralLinearGroup.det (g a))
  have hd : ∀ b, ((((g b)⁻¹ : GL (m b) k)) : Matrix (m b) (m b) k).det =
      (((Matrix.GeneralLinearGroup.det (g b))⁻¹ : kˣ) : k) := fun b => by
    rw [← map_inv]
    rfl
  have hd' : ∀ a, ((g a : GL (m a) k) : Matrix (m a) (m a) k).det =
      ((Matrix.GeneralLinearGroup.det (g a) : kˣ) : k) := fun a => rfl
  refine Units.ext ?_
  rw [det_adLie_pairs e β hβ p g hp]
  change _ = ((∏ a, Matrix.GeneralLinearGroup.det (g a) ^
    ((∑ b with a < b, (Fintype.card (m b) : ℤ)) - ∑ b with b < a, (Fintype.card (m b) : ℤ)) : kˣ) : k)
  rw [← h, Units.coe_prod]
  refine Finset.prod_congr rfl fun c _ => ?_
  split_ifs with hc
  · simp only [hd, hd', zpow_natCast, Units.val_mul, Units.val_pow_eq_pow_val]
  · rfl

theorem deltaHalf_eq_sqrtModular : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] {α : Type} [Fintype α] [LinearOrder α] {N : ℕ} {m : α → Type}
    [∀ i, Fintype (m i)] [∀ i, DecidableEq (m i)] (e : (Σ i, m i) ≃ Fin N) (β : Fin N → ℕ),
    (∀ x y, β x < β y ↔ blk e x < blk e y) → ∀ (φ : Levi k m ≃* levi k N β),
    (∀ g, ((φ g : levi k N β) : GL (Fin N) k) = leviEmb k e g) →
    ∀ g : Levi k m, ((deltaHalf k m g : ℂˣ) : ℂ) = sqrtModular k N β (leviIncl (φ g)) := by
  intro k _ _ _ _ α _ _ N m _ _ e β hβ φ hφ g
  have hp : ((leviIncl (φ g) : blockUpper k N β) : GL (Fin N) k) = leviEmb k e g := hφ g
  have h := modularCharacter_blockUpper (leviIncl (φ g))
  have hs : sqrtModular k N β (leviIncl (φ g)) = ((NNReal.sqrt (MeasureTheory.distribHaarChar k
      (LinearEquiv.det (adLie k N β (leviIncl (φ g))))) : ℝ) : ℂ) := by
    rw [← h]
    rfl
  have hm : modulus k m g = ((MeasureTheory.distribHaarChar k
      (LinearEquiv.det (adLie k N β (leviIncl (φ g)))) : NNReal) : ℝ) := by
    unfold GlobalTheory.SmGL.modulus
    rw [det_adLie_levi e β hβ _ g hp, map_prod, NNReal.coe_prod]
    refine Finset.prod_congr rfl fun a _ => ?_
    rw [map_zpow, NNReal.coe_zpow]
    rfl
  rw [hs, val_deltaHalf, hm, Real.coe_sqrt]

end

end GlobalTheory.CompanionTheory.DeltaLevi
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.PairingRestrictCompat
section
set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry TensorProduct DirectSum GlobalTheory.LogCris CrystallineSemistableComparison CrystallineSemistableComparison.Onto CrystallineSemistableComparison.Pb CrystallineSemistableComparison.HT GlobalTheory.CompanionTheory.KunGlue

namespace GlobalTheory.CompanionTheory.KunGlue

theorem pr_res : ∀ {K : Type} [Field K] (E : XD K) {U₁ U₁' : ObjectProperty E.C₁} {U₂ U₂' : ObjectProperty E.C₂} {U₃ U₃' : ObjectProperty E.D} (h₁ : ∀ T, U₃ T → U₁ (E.L₁.obj T)) (h₂ : ∀ T, U₃ T → U₂ (E.L₂.obj T)) (h₁' : ∀ T, U₃' T → U₁' (E.L₁.obj T)) (h₂' : ∀ T, U₃' T → U₂' (E.L₂.obj T)) (k₁ : U₁' ≤ U₁) (k₂ : U₂' ≤ U₂) (k₃ : U₃' ≤ U₃) {a a' c : ℕ} (ha : a + a' = c) {i j n : ℕ} (hn : i + j = n) (x : CH.Cn (U₁.ι ⋙ E.F₁ a) i) (y : CH.Cn (U₂.ι ⋙ E.F₂ a') j), (resU (E.F₃ c) k₃).pullC n ((E.pr U₁ U₂ U₃ h₁ h₂ ha).μ hn x y) = (E.pr U₁' U₂' U₃' h₁' h₂' ha).μ hn ((resU (E.F₁ a) k₁).pullC i x) ((resU (E.F₂ a') k₂).pullC j y) := by
  intro K _ E U₁ U₁' U₂ U₂' U₃ U₃' h₁ h₂ h₁' h₂' k₁ k₂ k₃ a a' c ha i j n hn x y
  funext s
  rfl

end GlobalTheory.CompanionTheory.KunGlue
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ParabolicEqBlockUpper
section
set_option maxSynthPendingDepth 1
open GlobalTheory.SmGL
open GroundTheory.Automorphic.Parabolic (levi parabolicInd jacquetRep JacquetModule sqrtModular leviIncl cellLeviSub normInducing unipotentRadical)
open GroundTheory.Automorphic.Iwasawa (blockUpper)
open GroundTheory.Automorphic (permGL indRep)
open DoubleCoset (doubleCoset)

namespace GlobalTheory.CompanionTheory.ParabBridge

theorem parab_eq_blockUpper : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {α : Type} [Fintype α] [LinearOrder α] {N : ℕ} {m : α → Type} [∀ i, Fintype (m i)] [∀ i, DecidableEq (m i)] (e : (Σ i, m i) ≃ Fin N) (β : Fin N → ℕ), (∀ x y, β x < β y ↔ blk e x < blk e y) → parab k e = blockUpper k N β := by
  intro k _ _ _ _ α _ _ N m _ _ e β h
  ext g
  rw [mem_parab, GroundTheory.Automorphic.Iwasawa.mem_blockUpper]
  exact forall₂_congr fun i j => by rw [h j i]

end GlobalTheory.CompanionTheory.ParabBridge
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ParabolicLeviProjection
section
set_option maxSynthPendingDepth 1
open GlobalTheory.SmGL
open GroundTheory.Automorphic.Parabolic (levi parabolicInd jacquetRep JacquetModule sqrtModular leviIncl cellLeviSub normInducing unipotentRadical)
open GroundTheory.Automorphic.Iwasawa (blockUpper)
open GroundTheory.Automorphic (permGL indRep)
open DoubleCoset (doubleCoset)

namespace GlobalTheory.CompanionTheory.SmGLBridge

theorem leviProj_found_eq : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {α : Type} [Fintype α] [LinearOrder α] {N : ℕ} {m : α → Type} [∀ i, Fintype (m i)] [∀ i, DecidableEq (m i)] (e : (Σ i, m i) ≃ Fin N) (β : Fin N → ℕ), (∀ x y, β x < β y ↔ blk e x < blk e y) → ∀ (φ : Levi k m ≃* levi k N β), (∀ g, ((φ g : levi k N β) : GL (Fin N) k) = leviEmb k e g) → ∀ (p : GL (Fin N) k) (h1 : p ∈ parab k e) (h2 : p ∈ blockUpper k N β), φ (leviProj k e ⟨p, h1⟩) = GroundTheory.Automorphic.Parabolic.leviProj k N β ⟨p, h2⟩ := by
  intro k _ _ _ _ α _ _ N m _ _ e β hβ φ hφ p h1 h2
  have hblk : ∀ x y, β x = β y ↔ blk e x = blk e y := by
    intro x y
    constructor
    · intro h
      have h3 := (hβ x y).not.1 (by omega)
      have h4 := (hβ y x).not.1 (by omega)
      exact le_antisymm (not_lt.1 h4) (not_lt.1 h3)
    · intro h
      have h3 := (hβ x y).not.2 (by rw [h]; exact lt_irrefl _)
      have h4 := (hβ y x).not.2 (by rw [h]; exact lt_irrefl _)
      omega
  apply Subtype.ext
  apply Units.ext
  apply Matrix.ext
  intro x y
  rw [hφ]
  rw [show ((GroundTheory.Automorphic.Parabolic.leviProj k N β ⟨p, h2⟩ : levi k N β) : GL (Fin N) k).val x y = _ from GroundTheory.Automorphic.Parabolic.leviProj_apply _ x y]
  obtain ⟨⟨a, i⟩, rfl⟩ := e.surjective x
  obtain ⟨⟨b, j⟩, rfl⟩ := e.surjective y
  by_cases hab : a = b
  · subst hab
    rw [if_pos ((hblk _ _).2 (by simp))]
    have := leviEmb_apply_same k e (leviProj k e ⟨p, h1⟩) a i j
    rw [this, leviProj_apply]
  · rw [if_neg (fun h => hab (by simpa using (hblk _ _).1 h))]
    exact leviEmb_apply_ne k e _ hab i j

end GlobalTheory.CompanionTheory.SmGLBridge
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.RestrictSelfPullCEq
section
set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry TensorProduct DirectSum GlobalTheory.LogCris CrystallineSemistableComparison CrystallineSemistableComparison.Onto CrystallineSemistableComparison.Pb CrystallineSemistableComparison.HT GlobalTheory.CompanionTheory.KunGlue

namespace GlobalTheory.CompanionTheory.KunGlue

theorem resU_self_pullC : ∀ {R : Type} [CommRing R] {C : Type 1} [Category.{0} C] (F : C ⥤ ModuleCat.{0} R) (U : ObjectProperty C) (k : U ≤ U) (n : ℕ) (x : CH.Cn (U.ι ⋙ F) n), (resU F k).pullC n x = x := by
  intro R _ C _ F U k n x
  funext s
  rfl

end GlobalTheory.CompanionTheory.KunGlue
end

