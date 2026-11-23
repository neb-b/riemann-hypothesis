module

public import Development.WeilBound.CoreStatements.PublishedTheorems.JacquetShalikaRigidity.ColumnConjugationMeasure

@[expose] public section

-- bundled from Development.WeilBound.CoreStatements.PublishedTheorems.JacquetShalikaRigidity.ColumnBlockEquiv
section
noncomputable section

open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open GlobalTheory.CuspGeneric GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.DiscSpec PositivityTheory.jumpWindows PositivityTheory.RgJS
open GroundTheory.Automorphic GroundTheory.Automorphic.FourierWhittaker GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.Spherical
open scoped ENNReal ComplexConjugate

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace PositivityTheory.AdelicQuotientData

namespace ColumnBlockEquiv

section Ring

variable {R : Type} [CommRing R] {a : ℕ}

theorem pm_col (m : ℕ) (y : UnipotentBlockColumnIndex a m m → R) (i k : Fin a) :
    posM (Subtype.val : UnipotentBlockColumnIndex a m m → Fin a × Fin a) y i k =
      if hik : (i : ℕ) < m ∧ (k : ℕ) = m then y ⟨(i, k), hik.1, hik.2.ge, hik.2.le⟩ else 0 := by
  rw [posM, Matrix.sum_apply]
  split_ifs with hik
  · rw [Finset.sum_eq_single ⟨(i, k), hik.1, hik.2.ge, hik.2.le⟩]
    · simp
    · intro b _ hb
      rw [Matrix.single_apply, if_neg]
      rintro ⟨h1, h2⟩
      exact hb (Subtype.ext (Prod.ext h1 h2))
    · intro h
      exact absurd (Finset.mem_univ _) h
  · refine Finset.sum_eq_zero fun t _ => ?_
    rw [Matrix.single_apply, if_neg]
    rintro ⟨h1, h2⟩
    apply hik
    have := t.2
    rw [← h1, ← h2]
    omega

theorem pm_mul_apply {ι : Type} [Fintype ι] (p : ι → Fin a × Fin a) (y : ι → R)
    (M : Matrix (Fin a) (Fin a) R) (i k : Fin a) :
    (posM p y * M) i k = ∑ s, if (p s).1 = i then y s * M (p s).2 k else 0 := by
  simp only [posM, Matrix.sum_mul, Matrix.sum_apply]
  refine Finset.sum_congr rfl fun s _ => ?_
  by_cases h : (p s).1 = i
  · subst h
    simp [Matrix.single_mul_apply_same]
  · rw [if_neg h, Matrix.mul_apply]
    refine Finset.sum_eq_zero fun j _ => ?_
    rw [Matrix.single_apply, if_neg (fun e => h e.1), zero_mul]

theorem mul_pm_apply {ι : Type} [Fintype ι] (p : ι → Fin a × Fin a) (y : ι → R)
    (M : Matrix (Fin a) (Fin a) R) (i k : Fin a) :
    (M * posM p y) i k = ∑ s, if (p s).2 = k then M i (p s).1 * y s else 0 := by
  simp only [posM, Matrix.mul_sum, Matrix.sum_apply]
  refine Finset.sum_congr rfl fun s _ => ?_
  by_cases h : (p s).2 = k
  · subst h
    simp [Matrix.mul_single_apply_same]
  · rw [if_neg h, Matrix.mul_apply]
    refine Finset.sum_eq_zero fun j _ => ?_
    rw [Matrix.single_apply, if_neg (fun e => h e.2), mul_zero]

theorem pm_mul_row (m : ℕ) (y : UnipotentBlockColumnIndex a m m → R) (M : Matrix (Fin a) (Fin a) R)
    (hM : ∀ j k : Fin a, (j : ℕ) = m → M j k = (1 : Matrix (Fin a) (Fin a) R) j k) :
    posM (Subtype.val : UnipotentBlockColumnIndex a m m → Fin a × Fin a) y * M = posM Subtype.val y := by
  ext i k
  have e := pm_mul_apply (Subtype.val : UnipotentBlockColumnIndex a m m → Fin a × Fin a) y 1 i k
  rw [Matrix.mul_one] at e
  rw [e, pm_mul_apply]
  refine Finset.sum_congr rfl fun s _ => ?_
  rw [hM s.1.2 k (by have := s.2; omega)]

theorem mul_posM_blockColumn (m : ℕ) (y : UnipotentBlockColumnIndex a m m → R) (h : GL (Fin a) R) (hB : GlobalTheory m h) :
    h.val * posM (Subtype.val : UnipotentBlockColumnIndex a m m → Fin a × Fin a) y =
      posM Subtype.val (fun t : UnipotentBlockColumnIndex a m m => ∑ s, h.val t.1.1 s.1.1 * y s) := by
  ext i k
  rw [mul_pm_apply, pm_col]
  split_ifs with hc
  · refine Finset.sum_congr rfl fun s _ => ?_
    rw [if_pos (Fin.ext (by have := s.2; omega))]
  · refine Finset.sum_eq_zero fun s _ => ?_
    split_ifs with hs
    · have h2 := s.2
      have hk : (k : ℕ) = m := by rw [← hs]; omega
      have hi : m ≤ (i : ℕ) := by
        by_contra hh
        exact hc ⟨by omega, hk⟩
      rw [hB i s.1.1 (Or.inl hi), Matrix.one_apply_ne, zero_mul]
      intro e
      rw [← e] at h2
      omega
    · rfl

theorem conj_blkU (m : ℕ) (h : GL (Fin a) R) (hB : GlobalTheory m h) (y : UnipotentBlockColumnIndex a m m → R) :
    h * blkU y * h⁻¹ = blkU (fun t : UnipotentBlockColumnIndex a m m => ∑ s, h.val t.1.1 s.1.1 * y s) := by
  have e : h * blkU y = blkU (fun t : UnipotentBlockColumnIndex a m m => ∑ s, h.val t.1.1 s.1.1 * y s) * h := by
    apply Units.ext
    show h.val * (1 + posM Subtype.val y) = (1 + posM Subtype.val _) * h.val
    rw [mul_add, add_mul, mul_one, one_mul,
      pm_mul_row m _ h.val (fun j k hj => hB j k (Or.inl hj.ge)), mul_posM_blockColumn m y h hB]
  rw [e, mul_inv_cancel_right]

end Ring

def colEquiv (k j : ℕ) (hj : j < k) : UnipotentBlockColumnIndex k j j ≃ Fin j where
  toFun t := ⟨t.1.1.val, t.2.1⟩
  invFun i := ⟨(⟨i.val, i.2.trans hj⟩, ⟨j, hj⟩), i.2, le_rfl, le_rfl⟩
  left_inv t := Subtype.ext (Prod.ext rfl (Fin.ext (by
    have := t.2.2
    change j = (t.1.2 : ℕ)
    omega)))
  right_inv i := Fin.ext rfl

end ColumnBlockEquiv

theorem algebraic_modulus_one_of_finiteOrder_char : AdelicLinearChange → CornerEmbedding → ColumnConjugationMeasure := by
  intro hM hK E _ _ _ k j hj g hg F hF
  have hK' := hK E k j hj.le
  obtain ⟨ι, hι⟩ := hK'.1 (Ad E)
  have hK2 := hK'.2 ι hι
  obtain ⟨g', rfl⟩ := hK2.2.2.1 g hg
  have hDt : Dt (ι g') = Dt g' := hK2.2.2.2.1 g'
  let e : UnipotentBlockColumnIndex k j j ≃ Fin j := ColumnBlockEquiv.colEquiv k j hj
  let Φ := MeasurableEquiv.piCongrLeft (fun _ : Fin j => Ad E) e
  have hΦ : MeasurePreserving Φ (vecMeasure E (UnipotentBlockColumnIndex k j j)) (vecMeasure E (Fin j)) :=
    measurePreserving_piCongrLeft (fun _ : Fin j => GroundTheory.Global.adeleMeasure E) e
  have key : ∀ H : (UnipotentBlockColumnIndex k j j → Ad E) → ℝ≥0∞,
      ∫⁻ y, H y ∂vecMeasure E (UnipotentBlockColumnIndex k j j) = ∫⁻ v, H (Φ.symm v) ∂vecMeasure E (Fin j) := by
    intro H
    have h1 := hΦ.lintegral_comp_emb Φ.measurableEmbedding (fun v => H (Φ.symm v))
    simp only [MeasurableEquiv.symm_apply_apply] at h1
    exact h1
  have hsymm : ∀ (v : Fin j → Ad E) (t : UnipotentBlockColumnIndex k j j), Φ.symm v t = v (e t) := by
    intro v t
    rfl
  have hent : ∀ t s : UnipotentBlockColumnIndex k j j, (ι g').val t.1.1 s.1.1 = g'.val (e t) (e s) := by
    intro t s
    rw [hι g']
    exact dif_pos ⟨t.2.1, s.2.1⟩
  have hpt : ∀ v : Fin j → Ad E, ι g' * blkU (Φ.symm v) * (ι g')⁻¹ =
      blkU (fun t : UnipotentBlockColumnIndex k j j => (g'.val *ᵥ v) (e t)) := by
    intro v
    rw [PositivityTheory.AdelicQuotientData.ColumnBlockEquiv.conj_blkU j (ι g') hg]
    refine congrArg blkU (funext fun t => ?_)
    rw [show (g'.val *ᵥ v) (e t) = ∑ b, g'.val (e t) b * v b from rfl, ← e.sum_comp]
    refine Finset.sum_congr rfl fun s _ => ?_
    rw [hsymm, hent t s]
  have hc : Continuous (fun v : Fin j → Ad E => (blkU (fun t : UnipotentBlockColumnIndex k j j => v (e t)) : GA E k)) :=
    (continuous_posU (isNil_blk k j j)).comp (continuous_pi fun t => continuous_apply (e t))
  have hG : Measurable (fun v : Fin j → Ad E => F (blkU (fun t : UnipotentBlockColumnIndex k j j => v (e t)))) :=
    hF.comp hc.measurable
  calc ∫⁻ x, F (ι g' * blkU x * (ι g')⁻¹) ∂vecMeasure E (UnipotentBlockColumnIndex k j j)
      = ∫⁻ v, F (ι g' * blkU (Φ.symm v) * (ι g')⁻¹) ∂vecMeasure E (Fin j) :=
        key (fun x => F (ι g' * blkU x * (ι g')⁻¹))
    _ = ∫⁻ v, F (blkU (fun t : UnipotentBlockColumnIndex k j j => (g'.val *ᵥ v) (e t))) ∂vecMeasure E (Fin j) :=
        lintegral_congr fun v => by rw [hpt v]
    _ = ENNReal.ofReal (Dt g')⁻¹ *
          ∫⁻ v, F (blkU (fun t : UnipotentBlockColumnIndex k j j => v (e t))) ∂vecMeasure E (Fin j) :=
        (hM E j g' _ hG).1
    _ = ENNReal.ofReal (Dt (ι g'))⁻¹ * ∫⁻ x, F (blkU x) ∂vecMeasure E (UnipotentBlockColumnIndex k j j) := by
        rw [hDt, key (fun x => F (blkU x))]
        congr 1

end PositivityTheory.AdelicQuotientData

end
end

-- bundled from Development.WeilBound.CoreStatements.PublishedTheorems.JacquetShalikaRigidity.CosetIntegralMeasure
section
noncomputable section

open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open GlobalTheory.CuspGeneric GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.DiscSpec PositivityTheory.jumpWindows PositivityTheory.RgJS
open GroundTheory.Automorphic GroundTheory.Automorphic.FourierWhittaker GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.Spherical
open scoped ENNReal ComplexConjugate

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace PositivityTheory.AdelicQuotientData

namespace CosetIntegralMeasure

variable {E : Type} [Field E] [NumberField E] {k : ℕ}

theorem meas_mul (g : GA E k) : Measurable (fun h : GA E k => g * h) := by
  exact measurable_const_mul g

theorem lint_nuG (Γ : Set (GL (Fin k) E)) (d : ℕ) (F : GA E k → ℝ≥0∞) (hF : Measurable F) :
    ∫⁻ h, F h ∂nuG Γ d = ∑' γ : Γ, ∫⁻ h, F (ratGL E k γ * h) ∂nuD E k d := by
  rw [nuG, lintegral_sum_measure]
  refine tsum_congr fun γ => ?_
  exact lintegral_map hF (meas_mul _)

end CosetIntegralMeasure

open CosetIntegralMeasure in
theorem coset_integration_of : N0 → N1 → N3 → CosetIntegralParabolic := by
  intro h0 _ _ E _ _ _ k j hj1 hjk F hF
  obtain ⟨hgam, huniq, hmul, hinv, -, hmir, -⟩ := h0 E k j hj1 hjk
  have hd : k - (j - 1 + 1) = k - j := by omega
  let f : RowT E k j × ({γ : GL (Fin k) E | IsMir (j - 1) γ} : Set (GL (Fin k) E)) →
      ({γ : GL (Fin k) E | GlobalTheory j γ} : Set (GL (Fin k) E)) := fun x =>
    ⟨(gam x.1)⁻¹ * (x.2 : GL (Fin k) E), hmul (gam x.1)⁻¹ (x.2 : GL (Fin k) E) (hinv (gam x.1) (hgam x.1).1)
      (hmir (x.2 : GL (Fin k) E) x.2.2).2⟩
  have hinj : Function.Injective f := by
    rintro ⟨ξ, p⟩ ⟨ξ', p'⟩ h
    have hv : (gam ξ)⁻¹ * (p : GL (Fin k) E) = (gam ξ')⁻¹ * (p' : GL (Fin k) E) := congrArg Subtype.val h
    have hB : GlobalTheory j ((gam ξ)⁻¹ * (p : GL (Fin k) E))⁻¹ := hinv ((gam ξ)⁻¹ * (p : GL (Fin k) E)) (f (ξ, p)).2
    obtain ⟨q, -, huq⟩ := huniq _ hB
    have e1 : (ξ, (p : GL (Fin k) E)⁻¹) = q :=
      huq (ξ, (p : GL (Fin k) E)⁻¹) ⟨(hmir (p : GL (Fin k) E) p.2).1, by simp only [_root_.mul_inv_rev, inv_inv]⟩
    have e2 : (ξ', (p' : GL (Fin k) E)⁻¹) = q :=
      huq (ξ', (p' : GL (Fin k) E)⁻¹) ⟨(hmir (p' : GL (Fin k) E) p'.2).1, by simp only [hv, _root_.mul_inv_rev, inv_inv]⟩
    have h3 := Prod.mk.inj (e1.trans e2.symm)
    exact Prod.ext h3.1 (Subtype.ext (inv_injective h3.2))
  have hsurj : Function.Surjective f := by
    rintro ⟨γ, hγ⟩
    obtain ⟨⟨ξ, q⟩, ⟨hq, heq⟩, -⟩ := huniq γ⁻¹ (hinv γ hγ)
    have hq' : IsMir (j - 1) q := hq
    have heq' : γ⁻¹ = q * gam ξ := heq
    refine ⟨(ξ, ⟨q⁻¹, (hmir q hq').1⟩), Subtype.ext ?_⟩
    show (gam ξ)⁻¹ * q⁻¹ = γ
    rw [← _root_.mul_inv_rev, ← heq', inv_inv]
  let e := Equiv.ofBijective f ⟨hinj, hsurj⟩
  have hR : ∀ ξ : RowT E k j, ∫⁻ h, F ((ratGL E k (gam ξ))⁻¹ * h) ∂nuP E k (j - 1) =
      ∑' p : ({γ : GL (Fin k) E | IsMir (j - 1) γ} : Set (GL (Fin k) E)),
        ∫⁻ h, F (ratGL E k ((gam ξ)⁻¹ * (p : GL (Fin k) E)) * h) ∂nuD E k (k - j) := by
    intro ξ
    have e0 := lint_nuG {γ : GL (Fin k) E | IsMir (j - 1) γ} (k - (j - 1 + 1))
      (fun h => F ((ratGL E k (gam ξ))⁻¹ * h)) (hF.comp (meas_mul _))
    refine e0.trans ?_
    rw [hd]
    refine tsum_congr fun p => ?_
    simp only [map_mul, map_inv, mul_assoc]
  calc ∫⁻ h, F h ∂nuB E k j
      = ∑' γ : ({γ : GL (Fin k) E | GlobalTheory j γ} : Set (GL (Fin k) E)),
          ∫⁻ h, F (ratGL E k γ * h) ∂nuD E k (k - j) := lint_nuG {γ : GL (Fin k) E | GlobalTheory j γ} (k - j) F hF
    _ = ∑' x : RowT E k j × ({γ : GL (Fin k) E | IsMir (j - 1) γ} : Set (GL (Fin k) E)),
          ∫⁻ h, F (ratGL E k ((gam x.1)⁻¹ * (x.2 : GL (Fin k) E)) * h) ∂nuD E k (k - j) :=
        (e.tsum_eq (fun γ : ({γ : GL (Fin k) E | GlobalTheory j γ} : Set (GL (Fin k) E)) =>
          ∫⁻ h, F (ratGL E k γ * h) ∂nuD E k (k - j))).symm
    _ = ∑' ξ : RowT E k j, ∑' p : ({γ : GL (Fin k) E | IsMir (j - 1) γ} : Set (GL (Fin k) E)),
          ∫⁻ h, F (ratGL E k ((gam ξ)⁻¹ * (p : GL (Fin k) E)) * h) ∂nuD E k (k - j) := by
        exact ENNReal.tsum_prod (f := fun (ξ : RowT E k j) (p : ({γ : GL (Fin k) E | IsMir (j - 1) γ} : Set (GL (Fin k) E))) =>
            ∫⁻ h, F (ratGL E k ((gam ξ)⁻¹ * (p : GL (Fin k) E)) * h) ∂nuD E k (k - j))
    _ = ∑' ξ : RowT E k j, ∫⁻ h, F ((ratGL E k (gam ξ))⁻¹ * h) ∂nuP E k (j - 1) :=
        tsum_congr fun ξ => (hR ξ).symm

end PositivityTheory.AdelicQuotientData

end
end

-- bundled from Development.WeilBound.CoreStatements.PublishedTheorems.JacquetShalikaRigidity.CubicPeriodConstant
section
noncomputable section

open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open GlobalTheory.CuspGeneric GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.DiscSpec PositivityTheory.jumpWindows PositivityTheory.RgJS
open GroundTheory.Automorphic GroundTheory.Automorphic.FourierWhittaker GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.Spherical
open scoped ENNReal ComplexConjugate

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace PositivityTheory.AdelicQuotientData

namespace cubicPeriodConstant

variable {E : Type} [Field E] [NumberField E] {k : ℕ}

theorem blkU_low {j : ℕ} (x : UnipotentBlockColumnIndex k j j → Ad E) (i c : Fin k) (h : c ≤ i) :
    (blkU x : GA E k).val i c = (1 : Matrix (Fin k) (Fin k) (Ad E)) i c := by
  have h' : (c : ℕ) ≤ i := h
  change (1 + posM Subtype.val x : Matrix (Fin k) (Fin k) (Ad E)) i c = _
  rw [Matrix.add_apply, posM, Matrix.sum_apply, Finset.sum_eq_zero, add_zero]
  intro t _
  have h1 := t.2
  rw [Matrix.single_apply_of_ne]
  rintro ⟨e1, e2⟩
  rw [← e1, ← e2] at h'
  omega

theorem blkU_unipotent_zero {j : ℕ} (x : UnipotentBlockColumnIndex k j j → Ad E) : UU 0 (blkU x : GA E k) := by
  refine ⟨fun i c h => ?_, fun i => ?_, fun i c h => absurd h (Nat.not_lt_zero _)⟩
  · rw [blkU_low x i c h.le, Matrix.one_apply_ne (ne_of_gt h)]
  · rw [blkU_low x i i le_rfl, Matrix.one_apply_eq]

theorem unipotent_zero_one : UU 0 (1 : GA E k) := by
  refine ⟨fun i c h => ?_, fun i => ?_, fun i c h => absurd h (Nat.not_lt_zero _)⟩
  · rw [Units.val_one, Matrix.one_apply_ne (ne_of_gt h)]
  · rw [Units.val_one, Matrix.one_apply_eq]

theorem unipotent_zero_mul {u v : GA E k} (hu : UU 0 u) (hv : UU 0 v) : UU 0 (u * v) := by
  refine ⟨fun i c h => ?_, fun i => ?_, fun i c h => absurd h (Nat.not_lt_zero _)⟩
  · rw [Units.val_mul, Matrix.mul_apply]
    refine Finset.sum_eq_zero fun l _ => ?_
    rcases lt_or_ge l i with hl | hl
    · rw [hu.1 i l hl, zero_mul]
    · rw [hv.1 l c (lt_of_lt_of_le h hl), mul_zero]
  · rw [Units.val_mul, Matrix.mul_apply, Finset.sum_eq_single i]
    · rw [hu.2.1, hv.2.1, one_mul]
    · intro l _ hl
      rcases lt_or_gt_of_ne hl with hl | hl
      · rw [hu.1 i l hl, zero_mul]
      · rw [hv.1 l i hl, mul_zero]
    · intro hi; exact absurd (Finset.mem_univ i) hi

theorem step (ψ : AddChar (Ad E) ℂ) (j : ℕ) (f f' : GA E k → ℂ) (g g' : GA E k) (c : ℂ)
    (h : ∀ u, UU 0 u → f (u * g) = c * f' (u * g')) :
    ∀ u, UU 0 u → colT ψ j f (u * g) = c * colT ψ j f' (u * g') := by
  intro u hu
  simp only [colT, coefF]
  rw [← avg_const_mul]
  congr 1
  funext x
  rw [← mul_assoc (blkU x) u g, ← mul_assoc (blkU x) u g', h _ (unipotent_zero_mul (blkU_unipotent_zero x) hu)]
  ring

theorem whit_gen (ψ : AddChar (Ad E) ℂ) (g g' : GA E k) : ∀ (m : ℕ) (f f' : GA E k → ℂ) (c : ℂ),
    (∀ u, UU 0 u → f (u * g) = c * f' (u * g')) →
      ∀ u, UU 0 u → whit ψ m f (u * g) = c * whit ψ m f' (u * g')
  | 0, _, _, _, h => h
  | m + 1, f, f', c, h => whit_gen ψ g g' m _ _ c (step ψ (m + 1) f f' g g' c h)

end cubicPeriodConstant

theorem crystalline_clause_of_admitted : P3 := by
  intro E _ _ _ k ψ m f f' g g' c h
  simpa only [one_mul] using cubicPeriodConstant.whit_gen ψ g g' m f f' c h 1 cubicPeriodConstant.unipotent_zero_one

end PositivityTheory.AdelicQuotientData

end
end

-- bundled from Development.WeilBound.CoreStatements.PublishedTheorems.JacquetShalikaRigidity.DeterminantHeight
section
noncomputable section

open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open GlobalTheory.CuspGeneric GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.DiscSpec PositivityTheory.jumpWindows PositivityTheory.RgJS
open GroundTheory.Automorphic GroundTheory.Automorphic.FourierWhittaker GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.Spherical
open scoped ENNReal ComplexConjugate

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace PositivityTheory.AdelicQuotientData

namespace DeterminantHeight

variable {E : Type} [Field E] [NumberField E] {k : ℕ}

theorem dt_eq (g : GA E k) :
    Dt g = (GroundTheory.Global.IdeleGroup.ideleModule E (AdelicGLn.det E k g) : ℝ) := rfl

theorem dt_maxCompact {κ : GA E k} (hκ : κ ∈ maxCompact) : Dt κ = 1 := by
  rw [dt_eq]; exact mem_normOneGL.1 (maxCompact_le_normOneGL hκ)

theorem dt_diag (γ : GL (Fin k) E) : Dt (AdelicGLn.diagonal E k γ) = 1 := by
  rw [dt_eq]; exact mem_normOneGL.1 (rationalGL_le_normOneGL ⟨γ, rfl⟩)

theorem dt_mul (g h : GA E k) : Dt (g * h) = Dt g * Dt h := by
  rw [dt_eq, dt_eq, dt_eq, map_mul, map_mul, Positive.val_mul]

theorem adeleAbs_pos {b : GA E k} (hb : b ∈ adelicBorel) (i : Fin k) :
    0 < adeleAbs ((b : Matrix (Fin k) (Fin k) (Ad E)) i i) := by
  rw [← IsUnit.unit_spec (isUnit_apply_self_of_mem_adelicBorel hb i), adeleAbs_units]
  exact (GroundTheory.Global.IdeleGroup.ideleModule E _).2

theorem dt_borel {b : GA E k} (hb : b ∈ adelicBorel) :
    Dt b = ∏ i, adeleAbs ((b : Matrix (Fin k) (Fin k) (Ad E)) i i) := by
  have hu : ∀ i, IsUnit ((b : Matrix (Fin k) (Fin k) (Ad E)) i i) :=
    isUnit_apply_self_of_mem_adelicBorel hb
  have hdet : AdelicGLn.det E k b = ∏ i, (hu i).unit := by
    ext
    rw [AdelicGLn.coe_det, Matrix.det_of_isUpperTriangular hb, Units.coe_prod]
    simp
  rw [dt_eq, hdet, map_prod (GroundTheory.Global.IdeleGroup.ideleModule E), coe_finset_prod_pos]
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [← adeleAbs_units, IsUnit.unit_spec]

theorem height_last {b : GA E k} (hb : b ∈ adelicBorel) (L : Fin k) (hL : (L : ℕ) + 1 = k) :
    height b (Pi.single L 1) = adeleAbs ((b : Matrix (Fin k) (Fin k) (Ad E)) L L) := by
  have hu := isUnit_apply_self_of_mem_adelicBorel hb L
  have hrow : ratVec (Pi.single L (1 : E)) ᵥ* (b : Matrix (Fin k) (Fin k) (Ad E)) =
      Pi.single L ((b : Matrix (Fin k) (Fin k) (Ad E)) L L) := by
    have : ratVec (Pi.single L (1 : E)) = Pi.single L (1 : Ad E) := by
      ext l
      by_cases hl : l = L
      · subst hl; simp [ratVec]
      · simp [ratVec, Pi.single_eq_of_ne hl]
    rw [this, single_one_vecMul]
    ext l
    by_cases hl : l = L
    · subst hl; simp [Matrix.row]
    · have hlt : l < L := lt_of_le_of_ne (Fin.le_iff_val_le_val.2 (by omega)) hl
      simp [Matrix.row, Pi.single_eq_of_ne hl, hb hlt]
  rw [Reduction.height, hrow, ← IsUnit.unit_spec hu, adelicNorm_single_units, adeleAbs_units]

end DeterminantHeight

theorem minkowski_bound_of : D0 → MinkowskiBoundAlt := by
  intro _ E _ _ _ k hk
  obtain ⟨t₀, ht₀, hred⟩ := GroundTheory.Automorphic.Reduction.exists_reduced (K := E)
  set s : ℝ := min t₀ 1 with hs
  have hs0 : 0 < s := lt_min ht₀ one_pos
  have hs1 : s ≤ 1 := min_le_right _ _
  refine ⟨(s ^ k)⁻¹, fun g => ?_⟩
  obtain ⟨γ, b, hb, κ, hκ, heq, hr⟩ := hred k g
  set L : Fin k := ⟨k - 1, by omega⟩ with hLdef
  have hL : (L : ℕ) + 1 = k := by simp [L]; omega
  set a : Fin k → ℝ := fun i => adeleAbs ((b : Matrix (Fin k) (Fin k) (Ad E)) i i) with hadef
  have ha : ∀ i, 0 < a i := fun i => DeterminantHeight.adeleAbs_pos hb i
  refine ⟨Pi.single L 1 ᵥ* (γ : Matrix (Fin k) (Fin k) E), ?_, ?_⟩
  · intro h
    have h2 := congrArg (fun y => y ᵥ* ((γ⁻¹ : GL (Fin k) E) : Matrix (Fin k) (Fin k) E)) h
    simp only [vecMul_vecMul, ← Units.val_mul, mul_inv_cancel, Units.val_one, vecMul_one,
      zero_vecMul] at h2
    have := congrFun h2 L
    simp at this
  · have hH : Reduction.height g (Pi.single L 1 ᵥ* (γ : Matrix (Fin k) (Fin k) E)) = a L := by
      rw [← height_diagonal_mul, heq, height_mul_maxCompact _ hκ, DeterminantHeight.height_last hb L hL]
    have hD : Dt g = ∏ i, a i := by
      have h1 : Dt (AdelicGLn.diagonal E k γ * g) = Dt g := by
        rw [DeterminantHeight.dt_mul, DeterminantHeight.dt_diag, one_mul]
      rw [← h1, heq, DeterminantHeight.dt_mul, DeterminantHeight.dt_maxCompact hκ, mul_one, DeterminantHeight.dt_borel hb]
    have hchain : ∀ d : ℕ, ∀ i : Fin k, (i : ℕ) + d = k - 1 → s ^ d * a L ≤ a i := by
      intro d
      induction d with
      | zero =>
        intro i hi
        have : i = L := Fin.ext (by simp [L]; omega)
        subst this; simp
      | succ d ih =>
        intro i hi
        have hi' : (i : ℕ) + 1 < k := by omega
        have h1 := ih ⟨(i : ℕ) + 1, hi'⟩ (by simp; omega)
        have h2 := hr i ⟨(i : ℕ) + 1, hi'⟩ rfl
        calc s ^ (d + 1) * a L = s * (s ^ d * a L) := by ring
          _ ≤ s * a ⟨(i : ℕ) + 1, hi'⟩ := mul_le_mul_of_nonneg_left h1 hs0.le
          _ ≤ t₀ * a ⟨(i : ℕ) + 1, hi'⟩ := mul_le_mul_of_nonneg_right (min_le_left _ _) (ha _).le
          _ ≤ a i := h2
    have hlow : ∀ i, s ^ k * a L ≤ a i := fun i =>
      (mul_le_mul_of_nonneg_right (pow_le_pow_of_le_one hs0.le hs1 (by omega : k - 1 - (i : ℕ) ≤ k))
        (ha L).le).trans (hchain (k - 1 - (i : ℕ)) i (by omega))
    have hsa : 0 < s ^ k * a L := mul_pos (pow_pos hs0 k) (ha L)
    have hprod : (s ^ k * a L) ^ k ≤ Dt g := by
      rw [hD]
      calc (s ^ k * a L) ^ k = ∏ _i : Fin k, s ^ k * a L := by simp
        _ ≤ ∏ i, a i := Finset.prod_le_prod₀ (fun _ _ => hsa.le) (fun i _ => hlow i)
    have hDt : 0 < Dt g := by rw [hD]; exact Finset.prod_pos fun i _ => ha i
    have hDpos : 0 < Dt g ^ ((k : ℝ)⁻¹) := Real.rpow_pos_of_pos hDt _
    have hDk : (Dt g ^ ((k : ℝ)⁻¹)) ^ k = Dt g := Real.rpow_inv_natCast_pow hDt.le (by omega)
    have hle : s ^ k * a L ≤ Dt g ^ ((k : ℝ)⁻¹) :=
      (pow_le_pow_iff_left₀ hsa.le hDpos.le (by omega : k ≠ 0)).1 (hprod.trans hDk.ge)
    have hsk : 0 < s ^ k := pow_pos hs0 k
    rw [ht, hH, div_le_iff₀ hDpos, inv_mul_eq_div, le_div_iff₀ hsk]
    linarith

end PositivityTheory.AdelicQuotientData

end
end

