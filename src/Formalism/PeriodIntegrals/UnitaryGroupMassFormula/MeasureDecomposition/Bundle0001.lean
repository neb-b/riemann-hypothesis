module

public import Mathlib
public import Formalism.PeriodIntegrals.Bundle0020
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.MeasureDecomposition.InstDecomp

@[expose] public section

-- bundled from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.MeasureDecomposition.ContinuousUMatApply
section
noncomputable section

open Matrix

namespace PI.ScMuExists.UnitaryGroupMassFormula

section Lin

variable {n r : ℕ}

theorem spanLt_mono (e : Fin r → Fin n → ℂ) {a b : ℕ} (h : a ≤ b) : spanLt e a ≤ spanLt e b := by
  unfold spanLt
  exact Submodule.span_mono (Set.image_mono fun b (hb : b.1 < a) => lt_of_lt_of_le hb h)

theorem mulVec_eq_sub_add (g : Matrix (Fin n) (Fin n) ℂ) (x : Fin n → ℂ) :
    g *ᵥ x = (g - 1) *ᵥ x + x := by
  rw [Matrix.sub_mulVec, Matrix.one_mulVec, sub_add_cancel]

theorem sub_mem_spanLt {e : Fin r → Fin n → ℂ} {z : Fin n → ℂ} {g : Matrix (Fin n) (Fin n) ℂ}
    (hg : InS e z g) (a : ℕ) {x : Fin n → ℂ} (hx : x ∈ spanLt e a) : (g - 1) *ᵥ x ∈ spanLt e a := by
  have key : spanLt e a ≤ (spanLt e a).comap (Matrix.mulVecLin (g - 1)) := by
    refine Submodule.span_le.mpr ?_
    rintro _ ⟨b, hb, rfl⟩
    simp only [SetLike.mem_coe, Submodule.mem_comap, Matrix.mulVecLin_apply]
    exact spanLt_mono e (le_of_lt hb) (hg.1 b)
  exact key hx

theorem mem_spanLt_of_inS {e : Fin r → Fin n → ℂ} {z : Fin n → ℂ} {g : Matrix (Fin n) (Fin n) ℂ}
    (hg : InS e z g) (a : ℕ) {x : Fin n → ℂ} (hx : x ∈ spanLt e a) : g *ᵥ x ∈ spanLt e a := by
  rw [mulVec_eq_sub_add g x]
  exact Submodule.add_mem _ (sub_mem_spanLt hg a hx) hx

theorem inv_preserves {W : Submodule ℂ (Fin n → ℂ)} {g g' : Matrix (Fin n) (Fin n) ℂ} (h1 : g' * g = 1)
    (hW : ∀ x ∈ W, g *ᵥ x ∈ W) : ∀ x ∈ W, g' *ᵥ x ∈ W := by
  let f : W →ₗ[ℂ] W := (Matrix.mulVecLin g).restrict (fun x hx => hW x hx)
  have hf : Function.Injective f := by
    intro a b hab
    have h2 : g *ᵥ (a : Fin n → ℂ) = g *ᵥ (b : Fin n → ℂ) := congrArg Subtype.val hab
    have h3 := congrArg (fun y => g' *ᵥ y) h2
    simp only [Matrix.mulVec_mulVec, h1, Matrix.one_mulVec] at h3
    exact Subtype.ext h3
  have hs : Function.Surjective f := LinearMap.injective_iff_surjective.mp hf
  intro x hx
  obtain ⟨y, hy⟩ := hs ⟨x, hx⟩
  have hy' : g *ᵥ (y : Fin n → ℂ) = x := congrArg Subtype.val hy
  rw [← hy', Matrix.mulVec_mulVec, h1, Matrix.one_mulVec]
  exact y.2

theorem mul_sub_one_mulVec (g g' : Matrix (Fin n) (Fin n) ℂ) (x : Fin n → ℂ) :
    (g * g' - 1) *ᵥ x = g *ᵥ ((g' - 1) *ᵥ x) + (g - 1) *ᵥ x := by
  simp only [Matrix.sub_mulVec, Matrix.mulVec_sub, Matrix.mulVec_mulVec, mul_sub, mul_one,
    Matrix.one_mulVec] <;> abel

theorem inv_sub_one_mulVec {g g' : Matrix (Fin n) (Fin n) ℂ} (h1 : g' * g = 1) (x : Fin n → ℂ) :
    (g' - 1) *ᵥ x = -(g' *ᵥ ((g - 1) *ᵥ x)) := by
  simp only [Matrix.sub_mulVec, Matrix.mulVec_sub, Matrix.mulVec_mulVec, h1, Matrix.one_mulVec,
    neg_sub]

theorem inS_one (e : Fin r → Fin n → ℂ) (z : Fin n → ℂ) : InS e z 1 := by
  unfold InS
  refine ⟨fun a => ?_, ?_⟩ <;> simp

theorem inS_mul {e : Fin r → Fin n → ℂ} {z : Fin n → ℂ} {g g' : Matrix (Fin n) (Fin n) ℂ}
    (hg : InS e z g) (hg' : InS e z g') : InS e z (g * g') := by
  refine ⟨fun a => ?_, ?_⟩
  · rw [mul_sub_one_mulVec]
    exact Submodule.add_mem _ (mem_spanLt_of_inS hg _ (hg'.1 a)) (hg.1 a)
  · rw [mul_sub_one_mulVec]
    exact Submodule.add_mem _ (mem_spanLt_of_inS hg _ hg'.2) hg.2

theorem inS_inv {e : Fin r → Fin n → ℂ} {z : Fin n → ℂ} {g g' : Matrix (Fin n) (Fin n) ℂ}
    (hg : InS e z g) (h1 : g' * g = 1) : InS e z g' := by
  have hp : ∀ (a : ℕ), ∀ x ∈ spanLt e a, g' *ᵥ x ∈ spanLt e a := fun a =>
    inv_preserves h1 (fun x hx => mem_spanLt_of_inS hg a hx)
  refine ⟨fun a => ?_, ?_⟩
  · rw [inv_sub_one_mulVec h1]
    exact Submodule.neg_mem _ (hp _ _ (hg.1 a))
  · rw [inv_sub_one_mulVec h1]
    exact Submodule.neg_mem _ (hp _ _ hg.2)

theorem inN_one (ε : Fin n → Bool) (e : Fin r → Fin n → ℂ) (z : Fin n → ℂ) : InN ε e z 1 := by
  unfold InN
  exact ⟨inS_one e z, fun y _ => by simp⟩

theorem inN_mul {ε : Fin n → Bool} {e : Fin r → Fin n → ℂ} {z : Fin n → ℂ} {g g' : Matrix (Fin n) (Fin n) ℂ}
    (hg : InN ε e z g) (hg' : InN ε e z g') : InN ε e z (g * g') := by
  refine ⟨inS_mul hg.1 hg'.1, fun y hy => ?_⟩
  rw [mul_sub_one_mulVec]
  exact Submodule.add_mem _ (mem_spanLt_of_inS hg.1 _ (hg'.2 y hy)) (hg.2 y hy)

theorem inN_inv {ε : Fin n → Bool} {e : Fin r → Fin n → ℂ} {z : Fin n → ℂ} {g g' : Matrix (Fin n) (Fin n) ℂ}
    (hg : InN ε e z g) (h1 : g' * g = 1) : InN ε e z g' := by
  refine ⟨inS_inv hg.1 h1, fun y hy => ?_⟩
  rw [inv_sub_one_mulVec h1]
  exact Submodule.neg_mem _
    (inv_preserves h1 (fun x hx => mem_spanLt_of_inS hg.1 r hx) _ (hg.2 y hy))

theorem isClosed_sub_mem (x : Fin n → ℂ) (W : Submodule ℂ (Fin n → ℂ)) :
    IsClosed {g : Matrix (Fin n) (Fin n) ℂ | (g - 1) *ᵥ x ∈ W} := by
  have hc : Continuous fun g : Matrix (Fin n) (Fin n) ℂ => (g - 1) *ᵥ x :=
    (continuous_id.sub continuous_const).matrix_mulVec continuous_const
  exact W.closed_of_finiteDimensional.preimage hc

theorem isClosed_inN (ε : Fin n → Bool) (e : Fin r → Fin n → ℂ) (z : Fin n → ℂ) :
    IsClosed {g : Matrix (Fin n) (Fin n) ℂ | InN ε e z g} := by
  have h1 : {g : Matrix (Fin n) (Fin n) ℂ | InN ε e z g} =
      ((⋂ a : Fin r, {g | (g - 1) *ᵥ e a ∈ spanLt e a.1}) ∩ {g | (g - 1) *ᵥ z ∈ spanLt e r}) ∩
        ⋂ y ∈ {y : Fin n → ℂ | ∀ a, hJ ε (e a) y = 0}, {g | (g - 1) *ᵥ y ∈ spanLt e r} := by
    ext g
    simp only [Set.mem_setOf_eq, Set.mem_inter_iff, Set.mem_iInter, InN, InS]
  rw [h1]
  exact ((isClosed_iInter fun a => isClosed_sub_mem _ _).inter (isClosed_sub_mem _ _)).inter
    (isClosed_biInter fun y _ => isClosed_sub_mem _ _)

theorem hJ_mulVec {ε : Fin n → Bool} {g : Matrix (Fin n) (Fin n) ℂ} (hg : Formalism.REAL.inUJ ε g)
    (x y : Fin n → ℂ) : hJ ε (g *ᵥ x) (g *ᵥ y) = hJ ε x y := by
  have hg' : gᴴ * Formalism.REAL.Jm ε * g = Formalism.REAL.Jm ε := hg
  unfold hJ
  rw [Matrix.star_mulVec, Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec, Matrix.dotProduct_mulVec,
    Matrix.vecMul_vecMul, ← Matrix.mul_assoc, hg']

theorem fix_span {W : Set (Fin n → ℂ)} {g : Matrix (Fin n) (Fin n) ℂ} (hW : ∀ x ∈ W, g *ᵥ x = x) :
    ∀ x ∈ Submodule.span ℂ W, g *ᵥ x = x := by
  intro x hx
  have hle : Submodule.span ℂ W ≤ LinearMap.ker (Matrix.mulVecLin g - LinearMap.id) := by
    rw [Submodule.span_le]
    intro y hy
    simp [hW y hy]
  have hx' := hle hx
  simpa [sub_eq_zero] using hx'

theorem conj_sub_one {h x h' : Matrix (Fin n) (Fin n) ℂ} (hh : h * h' = 1) :
    h * x * h' - 1 = h * (x - 1) * h' := by
  rw [mul_sub, sub_mul, mul_one, hh]

theorem inN_conj {ε : Fin n → Bool} {e : Fin r → Fin n → ℂ} {z : Fin n → ℂ}
    {h h' x : Matrix (Fin n) (Fin n) ℂ} (hU : Formalism.REAL.inUJ ε h) (hh : h * h' = 1) (hh' : h' * h = 1)
    (he : ∀ a, h *ᵥ e a = e a) (hz : h *ᵥ z = z) (hx : InN ε e z x) : InN ε e z (h * x * h') := by
  have hfix : ∀ (a : ℕ), ∀ v ∈ spanLt e a, h *ᵥ v = v := fun a =>
    fix_span (fun v hv => by obtain ⟨b, _, rfl⟩ := hv; exact he b)
  have h'e : ∀ v, h *ᵥ v = v → h' *ᵥ v = v := fun v hv => by
    conv_lhs => rw [← hv]
    rw [Matrix.mulVec_mulVec, hh', Matrix.one_mulVec]
  have key : ∀ v, (h * x * h' - 1) *ᵥ v = h *ᵥ ((x - 1) *ᵥ (h' *ᵥ v)) := fun v => by
    rw [conj_sub_one hh]
    simp only [Matrix.mulVec_mulVec, mul_assoc]
  refine ⟨⟨fun a => ?_, ?_⟩, fun y hy => ?_⟩
  · rw [key, h'e _ (he a), hfix a.1 _ (hx.1.1 a)]
    exact hx.1.1 a
  · rw [key, h'e _ hz, hfix r _ hx.1.2]
    exact hx.1.2
  · have hy' : ∀ a, hJ ε (e a) (h' *ᵥ y) = 0 := fun a => by
      rw [← hJ_mulVec hU, he a, Matrix.mulVec_mulVec, hh, Matrix.one_mulVec]
      exact hy a
    rw [key, hfix r _ (hx.2 _ hy')]
    exact hx.2 _ hy'

end Lin

section Inst

variable (I : Formalism.MainNotions.S.AutInst)

theorem uMat_mul {n : ℕ} {ε : Fin n → Bool} (g h : Formalism.REAL.UJ ε) :
    Formalism.MainNotions.S.uMat (g * h) = Formalism.MainNotions.S.uMat g * Formalism.MainNotions.S.uMat h := rfl

theorem uMat_one {n : ℕ} {ε : Fin n → Bool} : Formalism.MainNotions.S.uMat (1 : Formalism.REAL.UJ ε) = 1 := rfl

theorem uMat_inv_mul {n : ℕ} {ε : Fin n → Bool} (g : Formalism.REAL.UJ ε) :
    Formalism.MainNotions.S.uMat g⁻¹ * Formalism.MainNotions.S.uMat g = 1 := by
  rw [← uMat_mul, inv_mul_cancel, uMat_one]

theorem uMat_mul_inv {n : ℕ} {ε : Fin n → Bool} (g : Formalism.REAL.UJ ε) :
    Formalism.MainNotions.S.uMat g * Formalism.MainNotions.S.uMat g⁻¹ = 1 := by
  rw [← uMat_mul, mul_inv_cancel, uMat_one]

theorem uMat_inUJ {n : ℕ} {ε : Fin n → Bool} (g : Formalism.REAL.UJ ε) : Formalism.REAL.inUJ ε (Formalism.MainNotions.S.uMat g) := g.2

theorem continuous_uMat_apply (v : NumberField.InfinitePlace I.F) :
    Continuous fun s : I.Ginf => Formalism.MainNotions.S.uMat (s v) := (Units.continuous_val.comp continuous_subtype_val).comp (continuous_apply v)

variable {r : ℕ}

def NSub (e : Fin r → Fin I.n → I.E) (z : Fin I.n → I.E) : Subgroup I.Ginf where
  carrier := Ninf I e z
  one_mem' := fun v => by
    show InN _ _ _ (Formalism.MainNotions.S.uMat (1 : Formalism.REAL.UJ (I.ε v)))
    rw [uMat_one]; exact inN_one _ _ _
  mul_mem' := fun {a b} ha hb v => by
    show InN _ _ _ (Formalism.MainNotions.S.uMat (a v * b v))
    rw [uMat_mul]; exact inN_mul (ha v) (hb v)
  inv_mem' := fun {a} ha v => by
    show InN _ _ _ (Formalism.MainNotions.S.uMat ((a v)⁻¹))
    exact inN_inv (ha v) (uMat_inv_mul (a v))

def HSub (S : Set (Fin I.n → I.E)) : Subgroup I.Ginf where
  carrier := Hset I S
  one_mem' := fun v x _ => by
    show Formalism.MainNotions.S.uMat (1 : Formalism.REAL.UJ (I.ε v)) *ᵥ _ = _
    rw [uMat_one, Matrix.one_mulVec]
  mul_mem' := fun {a b} ha hb v x hx => by
    show Formalism.MainNotions.S.uMat (a v * b v) *ᵥ _ = _
    rw [uMat_mul, ← Matrix.mulVec_mulVec, hb v x hx, ha v x hx]
  inv_mem' := fun {a} ha v x hx => by
    show Formalism.MainNotions.S.uMat ((a v)⁻¹) *ᵥ _ = _
    conv_lhs => rw [← ha v x hx]
    rw [Matrix.mulVec_mulVec, uMat_inv_mul, Matrix.one_mulVec]

theorem isClosed_Ninf (e : Fin r → Fin I.n → I.E) (z : Fin I.n → I.E) : IsClosed (Ninf I e z) := by
  have h1 : Ninf I e z = ⋂ v, (fun s : I.Ginf => Formalism.MainNotions.S.uMat (s v)) ⁻¹'
      {g | InN (I.ε v) (fun a => rv I v (e a)) (rv I v z) g} := by
    ext s
    simp only [Ninf, Set.mem_setOf_eq, Set.mem_iInter, Set.mem_preimage]
  rw [h1]
  exact isClosed_iInter fun v => (isClosed_inN _ _ _).preimage (continuous_uMat_apply I v)

theorem isClosed_Hset (S : Set (Fin I.n → I.E)) : IsClosed (Hset I S) := by
  have h1 : Hset I S = ⋂ v, ⋂ x ∈ S, {s : I.Ginf | Formalism.MainNotions.S.uMat (s v) *ᵥ rv I v x = rv I v x} := by
    ext s
    simp only [Hset, Set.mem_setOf_eq, Set.mem_iInter]
  rw [h1]
  refine isClosed_iInter fun v => isClosed_biInter fun x _ => ?_
  exact isClosed_eq ((continuous_uMat_apply I v).matrix_mulVec continuous_const) continuous_const

theorem measure_subFacts : SubFacts := by
  intro I r e f z
  refine ⟨NSub I e z, HSub I (frameSet I e f z), rfl, rfl, isClosed_Ninf I e z, isClosed_Hset I _, ?_⟩
  intro h hh x hx
  have hh' : h ∈ Hset I (frameSet I e f z) := hh
  have hx' : x ∈ Ninf I e z := hx
  show ∀ v, InN _ _ _ (Formalism.MainNotions.S.uMat ((h * x * h⁻¹) v))
  intro v
  show InN _ _ _ (Formalism.MainNotions.S.uMat (h v * x v * (h v)⁻¹))
  rw [uMat_mul, uMat_mul]
  exact inN_conj (uMat_inUJ _) (uMat_mul_inv _) (uMat_inv_mul _)
    (fun a => hh' v _ (Set.mem_union_left _ (Set.mem_union_left _ (Set.mem_range_self a))))
    (hh' v _ (Set.mem_union_right _ rfl)) (hx' v)

end Inst

end PI.ScMuExists.UnitaryGroupMassFormula
end
end

-- bundled from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.MeasureDecomposition.GenSemiOf
section
open MeasureTheory
open scoped ENNReal Pointwise

noncomputable section

namespace PI.ScMuExists.UnitaryGroupMassFormula

theorem genSemi_of (hHaar : GenHaarSub) : GenSemi := by
  unfold GenSemi
  intro G _ _ _ _ _ _ _ _ N H hN hH hconj hinvN hprop
  obtain ⟨hσN, -, hcN, htN, hfinN, hposN⟩ := hHaar G N hN
  obtain ⟨hσH, -, hcH, htH, hfinH, hposH⟩ := hHaar G H hH
  set μN := haarSub N hN with hμN
  set μH := haarSub H hH with hμH
  haveI : SigmaFinite μN := hσN
  haveI : SigmaFinite μH := hσH
  have hmul : Measurable (fun p : G × G => p.1 * p.2) := measurable_fst.mul measurable_snd

  have hNH : (N : Set G) * (H : Set G) =
      (fun p : G × G => p.1 * p.2) '' ((N : Set G) ×ˢ (H : Set G)) := by
    ext x
    constructor
    · rintro ⟨a, ha, b, hb, rfl⟩
      exact ⟨(a, b), ⟨ha, hb⟩, rfl⟩
    · rintro ⟨⟨a, b⟩, ⟨ha, hb⟩, rfl⟩
      exact ⟨a, ha, b, hb, rfl⟩
  have hmeasNH : MeasurableSet ((N : Set G) * (H : Set G)) := by
    rw [hNH]
    obtain ⟨K, hK, hKU⟩ := (isSigmaCompact_univ.of_isClosed_subset (hN.prod hH)
      (Set.subset_univ _)).image continuous_mul
    rw [← hKU]
    exact MeasurableSet.iUnion fun n => (hK n).measurableSet

  have hprodc : (μN.prod μH) ((N : Set G) ×ˢ (H : Set G))ᶜ = 0 := by
    rw [Set.compl_prod_eq_union]
    refine measure_union_null ?_ ?_
    · rw [Measure.prod_prod, hcN, zero_mul]
    · rw [Measure.prod_prod, hcH, mul_zero]
  refine ⟨?_, hmeasNH, ?_, ?_, ?_, ?_⟩
  · show SFinite ((μN.prod μH).map (fun p : G × G => p.1 * p.2))
    infer_instance
  · show ((μN.prod μH).map (fun p : G × G => p.1 * p.2)) ((N : Set G) * (H : Set G))ᶜ = 0
    rw [Measure.map_apply hmul hmeasNH.compl]
    refine measure_mono_null ?_ hprodc
    intro p hp hpNH
    exact hp ⟨p.1, hpNH.1, p.2, hpNH.2, rfl⟩
  · rintro t ⟨n0, hn0, h0, hh0, rfl⟩
    show ((μN.prod μH).map (fun p : G × G => p.1 * p.2)).map (fun x => n0 * h0 * x) =
      (μN.prod μH).map (fun p : G × G => p.1 * p.2)
    have hc : Measurable (fun x : G => h0 * x * h0⁻¹) := (measurable_const_mul h0).mul_const _
    have hf : Measurable (fun x : G => n0 * (h0 * x * h0⁻¹)) := (measurable_const_mul n0).comp hc
    have hg : Measurable (fun y : G => h0 * y) := measurable_const_mul h0
    have hfN : μN.map (fun x : G => n0 * (h0 * x * h0⁻¹)) = μN := by
      show μN.map ((fun x : G => n0 * x) ∘ (fun x : G => h0 * x * h0⁻¹)) = μN
      rw [← Measure.map_map (measurable_const_mul n0) hc, hinvN h0 hh0, htN n0 hn0]
    have hgH : μH.map (fun y : G => h0 * y) = μH := htH h0 hh0
    have hPM : Measurable (Prod.map (fun x : G => n0 * (h0 * x * h0⁻¹)) (fun y : G => h0 * y)) :=
      hf.prodMap hg
    have hcomp : (fun x : G => n0 * h0 * x) ∘ (fun p : G × G => p.1 * p.2) =
        (fun p : G × G => p.1 * p.2) ∘
          Prod.map (fun x : G => n0 * (h0 * x * h0⁻¹)) (fun y : G => h0 * y) := by
      funext p
      simp only [Function.comp_apply, Prod.map_fst, Prod.map_snd]
      group
    rw [Measure.map_map (measurable_const_mul _) hmul, hcomp, ← Measure.map_map hmul hPM,
      ← Measure.map_prod_map μN μH hf hg, hfN, hgH]
  · intro U hU h1U
    show 0 < ((μN.prod μH).map (fun p : G × G => p.1 * p.2)) U
    rw [Measure.map_apply hmul hU.measurableSet]
    have hUo : IsOpen ((fun p : G × G => p.1 * p.2) ⁻¹' U) := hU.preimage continuous_mul
    have h11 : ((1 : G), (1 : G)) ∈ (fun p : G × G => p.1 * p.2) ⁻¹' U := by
      show (1 : G) * 1 ∈ U
      rwa [one_mul]
    obtain ⟨u, v, hu, hv, h1u, h1v, huv⟩ := isOpen_prod_iff.mp hUo 1 1 h11
    calc (0 : ℝ≥0∞) < μN u * μH v := ENNReal.mul_pos (hposN u hu h1u).ne' (hposH v hv h1v).ne'
      _ = (μN.prod μH) (u ×ˢ v) := (Measure.prod_prod u v).symm
      _ ≤ _ := measure_mono huv
  · intro C hC
    show ((μN.prod μH).map (fun p : G × G => p.1 * p.2)) C < ⊤
    rw [Measure.map_apply hmul hC.measurableSet]
    have hK := hprop C hC
    set P := {p : G × G | p.1 ∈ N ∧ p.2 ∈ H ∧ p.1 * p.2 ∈ C} with hP
    have hsub : (fun p : G × G => p.1 * p.2) ⁻¹' C ⊆ P ∪ ((N : Set G) ×ˢ (H : Set G))ᶜ := by
      intro p hp
      by_cases h : p ∈ (N : Set G) ×ˢ (H : Set G)
      · exact Or.inl ⟨h.1, h.2, hp⟩
      · exact Or.inr h
    have hPbox : P ⊆ (Prod.fst '' P) ×ˢ (Prod.snd '' P) := fun p hp => ⟨⟨p, hp, rfl⟩, ⟨p, hp, rfl⟩⟩
    have hPfin : (μN.prod μH) P < ⊤ := by
      refine lt_of_le_of_lt (measure_mono hPbox) ?_
      rw [Measure.prod_prod]
      exact ENNReal.mul_lt_top (hfinN _ (hK.image continuous_fst)) (hfinH _ (hK.image continuous_snd))
    calc (μN.prod μH) ((fun p : G × G => p.1 * p.2) ⁻¹' C)
        ≤ (μN.prod μH) (P ∪ ((N : Set G) ×ˢ (H : Set G))ᶜ) := measure_mono hsub
      _ ≤ (μN.prod μH) P + (μN.prod μH) ((N : Set G) ×ˢ (H : Set G))ᶜ := measure_union_le _ _
      _ < ⊤ := by rw [hprodc, add_zero]; exact hPfin

end PI.ScMuExists.UnitaryGroupMassFormula
end
end

-- bundled from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.MeasureDecomposition.HJMulVecGen
section
noncomputable section

open Matrix

namespace PI.ScMuExists.UnitaryGroupMassFormula

variable (I : Formalism.MainNotions.S.AutInst)

theorem phi_star (v : NumberField.InfinitePlace I.F) (a : I.E) : I.φ v (star a) = star (I.φ v a) :=
  I.cm.cmUnram.2.1 (I.φ v) a

theorem gram_real (v : NumberField.InfinitePlace I.F) :
    ((I.P v)⁻¹)ᴴ * Formalism.REAL.Jm (I.ε v) * (I.P v)⁻¹ = I.J.map (I.φ v) := by
  have h : I.P v * (I.P v)⁻¹ = 1 :=
    Matrix.mul_nonsing_inv _ ((Matrix.isUnit_iff_isUnit_det _).mp (I.P_unit v))
  have e : ((I.P v)⁻¹)ᴴ * (I.P v)ᴴ = 1 := by
    rw [← Matrix.conjTranspose_mul, h, Matrix.conjTranspose_one]
  rw [← I.P_spec v]
  calc ((I.P v)⁻¹)ᴴ * ((I.P v)ᴴ * I.J.map (I.φ v) * I.P v) * (I.P v)⁻¹
      = (((I.P v)⁻¹)ᴴ * (I.P v)ᴴ) * I.J.map (I.φ v) * (I.P v * (I.P v)⁻¹) := by
        simp only [Matrix.mul_assoc]
    _ = I.J.map (I.φ v) := by rw [e, h, Matrix.one_mul, Matrix.mul_one]

theorem hJ_mulVec_gen {n : ℕ} (ε : Fin n → Bool) (A : Matrix (Fin n) (Fin n) ℂ) (u w : Fin n → ℂ) :
    hJ ε (A *ᵥ u) (A *ᵥ w) = star u ⬝ᵥ ((Aᴴ * Formalism.REAL.Jm ε * A) *ᵥ w) := by
  simp only [hJ, Matrix.star_mulVec, Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec,
    Matrix.vecMul_vecMul, Matrix.mul_assoc]

theorem rv_hJ (v : NumberField.InfinitePlace I.F) (x y : Fin I.n → I.E) :
    hJ (I.ε v) (rv I v x) (rv I v y) = I.φ v (Formalism.UG.hform (starRingEnd I.E) I.J x y) := by
  simp only [rv]
  rw [hJ_mulVec_gen, gram_real I v]
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [Formalism.UG.hform, map_sum, map_mul, dotProduct, Matrix.mulVec, Pi.star_apply,
    Matrix.map_apply, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  rw [starRingEnd_apply, phi_star I v]
  ring

variable {I}

theorem rv_frame {r : ℕ} {e f : Fin r → Fin I.n → I.E} {z : Fin I.n → I.E} (hF : IsFrame I e f z)
    (v : NumberField.InfinitePlace I.F) :
    (∀ a b, hJ (I.ε v) (rv I v (e a)) (rv I v (e b)) = 0) ∧
    (∀ a b, hJ (I.ε v) (rv I v (f a)) (rv I v (f b)) = 0) ∧
    (∀ a b, hJ (I.ε v) (rv I v (e a)) (rv I v (f b)) = if a = b then 1 else 0) ∧
    (∀ a, hJ (I.ε v) (rv I v (e a)) (rv I v z) = 0 ∧ hJ (I.ε v) (rv I v (f a)) (rv I v z) = 0) ∧
    hJ (I.ε v) (rv I v z) (rv I v z) ≠ 0 := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := hF
  refine ⟨fun a b => ?_, fun a b => ?_, fun a b => ?_, fun a => ?_, ?_⟩
  · rw [rv_hJ, h1, map_zero]
  · rw [rv_hJ, h2, map_zero]
  · rw [rv_hJ, h3]
    split_ifs <;> simp
  · rw [rv_hJ, rv_hJ, (h4 a).1, (h4 a).2, map_zero]
    exact ⟨rfl, rfl⟩
  · rw [rv_hJ]
    exact (map_ne_zero _).mpr h5

end PI.ScMuExists.UnitaryGroupMassFormula
end
end

-- bundled from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.MeasureDecomposition.HaarSub
section
open MeasureTheory
open scoped ENNReal Pointwise

noncomputable section

namespace PI.ScMuExists.UnitaryGroupMassFormula

theorem generic_haar_subgroup : GenHaarSub := by
  intro G _ _ _ _ _ _ _ _ K hK
  haveI : LocallyCompactSpace K := hK.isClosedEmbedding_subtypeVal.locallyCompactSpace
  have hm : haarSub K hK = (Measure.haar : Measure K).map Subtype.val := rfl
  have hmeas : Measurable (Subtype.val : K → G) := measurable_subtype_coe
  have hcpt : ∀ C : Set G, IsCompact C → haarSub K hK C < ⊤ := by
    intro C hC
    rw [hm, Measure.map_apply hmeas hC.isClosed.measurableSet]
    exact (hK.isClosedEmbedding_subtypeVal.isCompact_preimage hC).measure_lt_top
  haveI : IsFiniteMeasureOnCompacts (haarSub K hK) := ⟨hcpt⟩
  refine ⟨inferInstance, ?_, ?_, ?_, hcpt, ?_⟩
  · intro h0
    rw [hm, Measure.map_eq_zero_iff hmeas.aemeasurable] at h0
    exact isOpen_univ.measure_ne_zero (Measure.haar : Measure K) Set.univ_nonempty (by simp [h0])
  · rw [hm, Measure.map_apply hmeas hK.isOpen_compl.measurableSet]
    have hpre : (Subtype.val : K → G) ⁻¹' (K : Set G)ᶜ = ∅ := by
      ext x
      simp only [Set.mem_preimage, Set.mem_compl_iff, SetLike.mem_coe, Set.mem_empty_iff_false,
        iff_false, not_not]
      exact x.2
    rw [hpre, measure_empty]
  · intro s hs
    rw [hm, Measure.map_map (measurable_const_mul s) hmeas]
    have hcomp : (fun x => s * x) ∘ (Subtype.val : K → G) =
        Subtype.val ∘ (fun y : K => (⟨s, hs⟩ : K) * y) := by
      funext y
      rfl
    rw [hcomp, ← Measure.map_map hmeas (measurable_const_mul _)]
    congr 1
    first
      | exact map_mul_left_eq_self (Measure.haar : Measure K) _
      | exact Measure.IsMulLeftInvariant.map_mul_left_eq_self _
  · intro U hU h1
    rw [hm, Measure.map_apply hmeas hU.measurableSet]
    exact (hU.preimage continuous_subtype_val).measure_pos (Measure.haar : Measure K) ⟨1, by simpa using h1⟩

end PI.ScMuExists.UnitaryGroupMassFormula
end
end

