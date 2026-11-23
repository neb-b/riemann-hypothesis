module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0292
public import Development.AbelianVarietyTheory.Definitions.Divisors.LineOppositeParabolicUnitaryLeviSectionEq
public import Formalism.SatakeDualWeyl.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0293
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0297
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0006
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.PadicIsNonarchimedeanLocalField

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RelIndexConjIntegralGLColumnCongruence
section
open GlobalTheory.FunObj GlobalTheory.SplitWeil GlobalTheory.SplitFlip GlobalTheory.RootEx GlobalTheory.DiagVol ValuativeRel Matrix

noncomputable section
namespace GlobalTheory.IndexCol

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  {ι : Type} [Fintype ι] [DecidableEq ι]

theorem mem_maximalIdeal_iff (a : 𝒪[k]) :
    a ∈ IsLocalRing.maximalIdeal 𝒪[k] ↔ valuation k (a : k) < 1 := by
  rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff, Valuation.Integer.not_isUnit_iff_valuation_lt_one]

theorem val_sum_mul_lt_one (a b : ι → k) (ha : ∀ s, a s ∈ 𝒪[k]) (hb : ∀ s, valuation k (b s) < 1) :
    valuation k (∑ s, a s * b s) < 1 := by
  refine Valuation.map_sum_lt _ one_ne_zero fun s _ => ?_
  rw [map_mul]
  exact (mul_le_mul_of_nonneg_right (ha s) zero_le').trans_lt (by rw [one_mul]; exact hb s)

theorem col_inv_mul_iff {x : GL ι k} (hx : x ∈ KO k ι) (y : GL ι k) (t : ι) :
    (∀ s, valuation k (((x⁻¹ * y).val - 1) s t) < 1) ↔ ∀ s, valuation k ((y.val - x.val) s t) < 1 := by
  obtain ⟨hx1, hx2⟩ := (mem_KO_iff x).1 hx
  have e1 : (x⁻¹ * y).val - 1 = (x⁻¹).val * (y.val - x.val) := by
    rw [Units.val_mul, mul_sub, Units.inv_mul]
  have e2 : y.val - x.val = x.val * ((x⁻¹ * y).val - 1) := by
    rw [Units.val_mul, mul_sub, ← mul_assoc, Units.mul_inv, one_mul, mul_one]
  constructor
  · intro h s
    rw [e2, Matrix.mul_apply]
    exact val_sum_mul_lt_one _ _ (fun j => hx1 s j) h
  · intro h s
    rw [e1, Matrix.mul_apply]
    exact val_sum_mul_lt_one _ _ (fun j => hx2 s j) h

theorem conj_apply (ϖ : kˣ) (t : ι) (z : Matrix ι ι k) (r s : ι) :
    ((diagGL (Pi.mulSingle t ϖ : ι → kˣ)).val * z * ((diagGL (Pi.mulSingle t ϖ : ι → kˣ))⁻¹).val) r s =
      ((Pi.mulSingle t ϖ : ι → kˣ) r : k) * z r s * ((((Pi.mulSingle t ϖ : ι → kˣ) s)⁻¹ : kˣ) : k) := by
  have hi : ((diagGL (Pi.mulSingle t ϖ : ι → kˣ))⁻¹).val = diagonal fun i => ((((Pi.mulSingle t ϖ : ι → kˣ) i)⁻¹ : kˣ) : k) := rfl
  rw [hi, diagGL_val, mul_diagonal, diagonal_mul]

theorem conj_integral_iff {ϖ : kˣ} (hϖ : IsUnif ϖ) (t : ι) (z : Matrix ι ι k) (hz : ∀ r s, z r s ∈ 𝒪[k]) :
    (∀ r s, ((diagGL (Pi.mulSingle t ϖ : ι → kˣ)).val * z * ((diagGL (Pi.mulSingle t ϖ : ι → kˣ))⁻¹).val) r s ∈ 𝒪[k]) ↔
      ∀ r, r ≠ t → valuation k (z r t) < 1 := by
  have hv : valuation k (ϖ : k) ≠ 0 := by simp
  have hlt : valuation k (ϖ : k) < 1 := hϖ ▸ uniformizer_lt_one
  simp only [conj_apply]
  constructor
  · intro h r hr
    have h1 := h r t
    simp only [Pi.mulSingle_apply, hr, if_false, if_true, Units.val_one, one_mul] at h1
    have h2 : valuation k (z r t * ((ϖ⁻¹ : kˣ) : k)) ≤ 1 := h1
    rw [map_mul, Units.val_inv_eq_inv_val, map_inv₀] at h2
    have h3 : valuation k (z r t) ≤ valuation k (ϖ : k) := by
      have := mul_le_mul_of_nonneg_right h2 (zero_le' (a := valuation k (ϖ : k)))
      rwa [mul_assoc, inv_mul_cancel₀ hv, mul_one, one_mul] at this
    exact h3.trans_lt hlt
  · intro h r s
    by_cases hr : r = t <;> by_cases hs : s = t
    · subst hr; subst hs
      simp only [Pi.mulSingle_eq_same]
      rw [mul_comm (ϖ : k), mul_assoc, Units.mul_inv, mul_one]; exact hz _ _
    · subst hr
      simp only [Pi.mulSingle_eq_same, Pi.mulSingle_apply, hs, if_false, inv_one, Units.val_one, mul_one]
      exact mul_mem hϖ.mem (hz _ _)
    · subst hs
      simp only [Pi.mulSingle_eq_same, Pi.mulSingle_apply, hr, if_false, Units.val_one, one_mul]
      show valuation k _ ≤ 1
      rw [map_mul, Units.val_inv_eq_inv_val, map_inv₀]
      have h3 : valuation k (z r s) ≤ valuation k (ϖ : k) := by
        rw [hϖ, le_uniformizer_iff]; exact h r hr
      calc valuation k (z r s) * (valuation k (ϖ : k))⁻¹ ≤ valuation k (ϖ : k) * (valuation k (ϖ : k))⁻¹ :=
            mul_le_mul_of_nonneg_right h3 zero_le'
        _ = 1 := mul_inv_cancel₀ hv
    · simp only [Pi.mulSingle_apply, hr, hs, if_false, inv_one, Units.val_one, one_mul, mul_one]
      exact hz _ _

theorem mem_conj_iff {ϖ : kˣ} (hϖ : IsUnif ϖ) (t : ι) {z : GL ι k} (hz : z ∈ KO k ι) :
    z ∈ (KO k ι).map (MulAut.conj ((diagGL (Pi.mulSingle t ϖ : ι → kˣ))⁻¹)).toMonoidHom ↔
      (∀ r, r ≠ t → valuation k (z.val r t) < 1) ∧ ∀ r, r ≠ t → valuation k ((z⁻¹).val r t) < 1 := by
  set g := diagGL (Pi.mulSingle t ϖ : ι → kˣ) with hg
  have e : z ∈ (KO k ι).map (MulAut.conj g⁻¹).toMonoidHom ↔ g * z * g⁻¹ ∈ KO k ι := by
    rw [Subgroup.mem_map]
    constructor
    · rintro ⟨w, hw, rfl⟩
      simpa [mul_assoc] using hw
    · intro h
      exact ⟨_, h, by simp [mul_assoc]⟩
  obtain ⟨h1, h2⟩ := (mem_KO_iff z).1 hz
  have ev : (g * z * g⁻¹).val = g.val * z.val * (g⁻¹).val := by simp only [Units.val_mul]
  have ei : ((g * z * g⁻¹)⁻¹).val = g.val * (z⁻¹).val * (g⁻¹).val := by
    rw [show (g * z * g⁻¹)⁻¹ = g * z⁻¹ * g⁻¹ by group]; simp only [Units.val_mul]
  rw [e, mem_KO_iff, ev, ei, hg, conj_integral_iff hϖ t _ h1, conj_integral_iff hϖ t _ h2]

theorem relIndex_conj_col : ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    {ι : Type} [Fintype ι] [DecidableEq ι] (ϖ : kˣ), IsUnif ϖ → ∀ (t : ι) (S : Finset ι), t ∉ S →
    ∀ (H : Subgroup (GL ι k)), H ≤ KO k ι → (∀ x ∈ H, ∀ r, r ∉ S → x.val r t = (1 : Matrix ι ι k) r t) →
    (∀ y : ι → k, (∀ r, y r ∈ 𝒪[k]) → (∀ r, r ∉ S → y r = 0) →
      ∃ x ∈ H, x.val = 1 + Matrix.of (fun r s => if s = t then y r else 0)) →
    ((KO k ι).map (MulAut.conj ((diagGL (Pi.mulSingle t ϖ))⁻¹)).toMonoidHom).relIndex H = resCard k ^ S.card := by
  intro k _ _ _ _ ι _ _ ϖ hϖ t S ht H hH hcol hel
  set A := (KO k ι).map (MulAut.conj ((diagGL (Pi.mulSingle t ϖ : ι → kˣ))⁻¹)).toMonoidHom with hA

  have hQ0 : ∀ z ∈ H, (∀ r, r ≠ t → valuation k (z.val r t) < 1) ↔
      ∀ s, valuation k ((z.val - 1) s t) < 1 := by
    intro z hz
    constructor
    · intro h s
      by_cases hs : s = t
      · subst hs; rw [Matrix.sub_apply, hcol z hz s ht, sub_self, map_zero]; exact zero_lt_one
      · rw [Matrix.sub_apply, Matrix.one_apply_ne hs, sub_zero]; exact h s hs
    · intro h r hr
      simpa [Matrix.sub_apply, Matrix.one_apply_ne hr] using h r
  have hQ : ∀ z ∈ H, z ∈ A ↔ ∀ s, valuation k ((z.val - 1) s t) < 1 := by
    intro z hz
    have hzi : z⁻¹ ∈ H := H.inv_mem hz
    rw [hA, mem_conj_iff hϖ t (hH hz), hQ0 z hz, hQ0 _ hzi]
    have e := col_inv_mul_iff (hH hz) 1 t
    rw [mul_one] at e
    rw [e]
    constructor
    · exact fun h => h.1
    · intro h
      refine ⟨h, fun s => ?_⟩
      have h1 := h s
      rw [Matrix.sub_apply] at h1 ⊢
      rw [← Valuation.map_neg, neg_sub, Units.val_one]; exact h1
  have hres : ∀ x y : 𝒪[k], IsLocalRing.residue 𝒪[k] x = IsLocalRing.residue 𝒪[k] y ↔
      valuation k ((x : k) - y) < 1 := fun x y => by
    have h1 := mem_maximalIdeal_iff (x - y)
    push_cast at h1
    rw [← h1]; exact Ideal.Quotient.eq
  let φ : H → (S → 𝓀[k]) := fun x r =>
    IsLocalRing.residue 𝒪[k] ⟨x.1.val r t, ((mem_KO_iff _).1 (hH x.2)).1 r t⟩
  have hφ : ∀ a b : H, φ a = φ b ↔ a⁻¹ * b ∈ A.subgroupOf H := by
    intro a b
    rw [Subgroup.mem_subgroupOf, Subgroup.coe_mul, Subgroup.coe_inv,
      hQ _ (H.mul_mem (H.inv_mem a.2) b.2), col_inv_mul_iff (hH a.2), funext_iff]
    simp only [φ, hres]
    constructor
    · intro h s
      by_cases hs : s ∈ S
      · rw [Matrix.sub_apply, ← Valuation.map_neg, neg_sub]; exact h ⟨s, hs⟩
      · rw [Matrix.sub_apply, hcol b b.2 s hs, hcol a a.2 s hs, sub_self, map_zero]; exact zero_lt_one
    · intro h r
      have := h r
      rwa [Matrix.sub_apply, ← Valuation.map_neg, neg_sub] at this
  let f : H ⧸ A.subgroupOf H → (S → 𝓀[k]) :=
    Quotient.lift φ (fun a b hab => (hφ a b).2 (QuotientGroup.leftRel_apply.1 hab))
  have hf : Function.Bijective f := by
    constructor
    · intro p q
      induction p using QuotientGroup.induction_on
      induction q using QuotientGroup.induction_on
      intro h
      exact QuotientGroup.eq.2 ((hφ _ _).1 h)
    · intro c
      choose u hu using fun r : S => IsLocalRing.residue_surjective (c r)
      let y : ι → k := fun r => if h : r ∈ S then (u ⟨r, h⟩ : k) else 0
      obtain ⟨x, hxH, hx⟩ := hel y (fun r => by
          by_cases h : r ∈ S
          · simp only [y, h, dif_pos]; exact (u _).2
          · simp only [y, h, dif_neg, not_false_eq_true]; exact zero_mem _)
        (fun r hr => by simp [y, hr])
      refine ⟨QuotientGroup.mk ⟨x, hxH⟩, ?_⟩
      funext r
      have hr : (r : ι) ≠ t := fun h => ht (h ▸ r.2)
      have e : x.val r t = u r := by
        rw [hx]; simp [y, hr, r.2]
      show IsLocalRing.residue 𝒪[k] ⟨x.val r t, _⟩ = c r
      rw [← hu r]; congr 1; exact Subtype.ext e
  rw [Subgroup.relIndex, Subgroup.index, Nat.card_congr (Equiv.ofBijective f hf), Nat.card_fun,
    Nat.card_eq_fintype_card (α := S), Fintype.card_coe]
  rfl

end GlobalTheory.IndexCol
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RelIndexConjIntegralGLRowCongruence
section
open GlobalTheory.FunObj GlobalTheory.SplitWeil GlobalTheory.SplitFlip GlobalTheory.RootEx GlobalTheory.DiagVol ValuativeRel Matrix

noncomputable section
namespace GlobalTheory.DiagVol.RowIdx

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
variable {ι : Type} [Fintype ι] [DecidableEq ι]

theorem mapInt_injective :
    Function.Injective (Matrix.GeneralLinearGroup.map (n := ι) (algebraMap 𝒪[k] k)) := by
  intro u v h
  ext i j
  exact congrArg (fun g : GL ι k => g.val i j) h

def red : KO k ι →* GL ι 𝓀[k] :=
  (Matrix.GeneralLinearGroup.map (IsLocalRing.residue 𝒪[k])).comp
    (MonoidHom.ofInjective (mapInt_injective (k := k) (ι := ι))).symm.toMonoidHom

theorem red_val (x : KO k ι) (r s : ι) (h : x.1.val r s ∈ 𝒪[k]) :
    (red x).val r s = IsLocalRing.residue 𝒪[k] ⟨x.1.val r s, h⟩ := by
  set u := (MonoidHom.ofInjective (mapInt_injective (k := k) (ι := ι))).symm x with hu
  have h1 : Matrix.GeneralLinearGroup.map (algebraMap 𝒪[k] k) u = x.1 := by
    have := congrArg Subtype.val ((MonoidHom.ofInjective (mapInt_injective (k := k) (ι := ι))).apply_symm_apply x)
    rw [MonoidHom.ofInjective_apply] at this
    exact this
  have h2' : ((u.val r s : 𝒪[k]) : k) = x.1.val r s := by rw [← h1]; rfl
  have h2 : u.val r s = ⟨x.1.val r s, h⟩ := Subtype.ext h2'
  show IsLocalRing.residue 𝒪[k] (u.val r s) = _
  rw [h2]

omit [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] in
theorem row_mul {R : Type} [CommRing R] (P Q : Matrix ι ι R) (t : ι) : (P * Q) t = Matrix.vecMul (P t) Q := by
  funext s; simp [Matrix.mul_apply, Matrix.vecMul, dotProduct]


omit [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] in
theorem row_inv_iff {R : Type} [CommRing R] (M N : GL ι R) (t : ι) :
    (M⁻¹ * N).val t = (1 : Matrix ι ι R) t ↔ (M⁻¹).val t = (N⁻¹).val t := by
  constructor
  · intro h
    have e1 : (M⁻¹).val = (M⁻¹ * N).val * (N⁻¹).val := by simp [mul_assoc]
    rw [e1, row_mul, h, ← row_mul, one_mul]
  · intro h
    rw [Units.val_mul, row_mul, h, ← row_mul, ← Units.val_mul, inv_mul_cancel, Units.val_one]

theorem residue_eq_zero_iff_of_isUnif {ϖ : kˣ} (hϖ : IsUnif ϖ) (a : k) (ha : a ∈ 𝒪[k]) :
    IsLocalRing.residue 𝒪[k] ⟨a, ha⟩ = 0 ↔ (ϖ : k)⁻¹ * a ∈ 𝒪[k] := by
  rw [IsLocalRing.residue_eq_zero_iff, hϖ.maximalIdeal_eq, Ideal.mem_span_singleton]
  constructor
  · rintro ⟨c, hc⟩
    have : a = ϖ * c := congrArg Subtype.val hc
    rw [this, ← mul_assoc, inv_mul_cancel₀ ϖ.ne_zero, one_mul]; exact c.2
  · intro h
    refine ⟨⟨_, h⟩, Subtype.ext ?_⟩
    show a = ϖ * ((ϖ : k)⁻¹ * a)
    rw [← mul_assoc, mul_inv_cancel₀ ϖ.ne_zero, one_mul]

theorem mem_map_conj_iff (g : GL ι k) (K : Subgroup (GL ι k)) (z : GL ι k) :
    z ∈ K.map (MulAut.conj g).toMonoidHom ↔ g⁻¹ * z * g ∈ K := by
  constructor
  · rintro ⟨w, hw, rfl⟩; simpa [mul_assoc] using hw
  · intro h; exact ⟨_, h, by simp [mul_assoc]⟩

omit [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] in
theorem conj_diag_val (ϖ : kˣ) (t : ι) (z : GL ι k) (r s : ι) :
    ((diagGL (Pi.mulSingle t ϖ))⁻¹ * z * diagGL (Pi.mulSingle t ϖ)).val r s =
      (if r = t then (ϖ : k)⁻¹ else 1) * z.val r s * (if s = t then (ϖ : k) else 1) := by
  have hi : ((diagGL (Pi.mulSingle t ϖ))⁻¹).val = diagonal fun i => ((((Pi.mulSingle t ϖ : ι → kˣ) i)⁻¹ : kˣ) : k) := rfl
  rw [Units.val_mul, Units.val_mul, hi, diagGL_val, mul_diagonal, diagonal_mul]
  by_cases hr : r = t <;> by_cases hs : s = t <;> simp [hr, hs, Pi.mulSingle_apply]

theorem conj_int_iff {ϖ : kˣ} (hϖ : IsUnif ϖ) (t : ι) (z : GL ι k) (hz : ∀ r s, z.val r s ∈ 𝒪[k]) :
    (∀ r s, ((diagGL (Pi.mulSingle t ϖ))⁻¹ * z * diagGL (Pi.mulSingle t ϖ)).val r s ∈ 𝒪[k]) ↔
      ∀ s, s ≠ t → (ϖ : k)⁻¹ * z.val t s ∈ 𝒪[k] := by
  simp only [conj_diag_val]
  constructor
  · intro h s hs
    simpa [hs] using h t s
  · intro h r s
    by_cases hr : r = t
    · subst hr
      by_cases hs : s = r
      · subst hs
        simp only [if_true]
        rw [mul_comm, ← mul_assoc, mul_inv_cancel₀ ϖ.ne_zero, one_mul]; exact hz _ _
      · simpa [hs] using h s hs
    · simp only [hr, if_false, one_mul]
      split_ifs
      · exact Subring.mul_mem _ (hz r s) hϖ.mem
      · simpa using hz r s

theorem red_incl_val {H : Subgroup (GL ι k)} (hHK : H ≤ KO k ι) (z : H) (r s : ι) (h : (z : GL ι k).val r s ∈ 𝒪[k]) :
    (red (Subgroup.inclusion hHK z)).val r s = IsLocalRing.residue 𝒪[k] ⟨(z : GL ι k).val r s, h⟩ :=
  red_val (Subgroup.inclusion hHK z) r s h

theorem red_row_off {H : Subgroup (GL ι k)} (hHK : H ≤ KO k ι) {t : ι} {S : Finset ι}
    (hrow : ∀ x ∈ H, ∀ s, s ∉ S → x.val t s = (1 : Matrix ι ι k) t s) (z : H) (s : ι) (hs : s ∉ S) :
    (red (Subgroup.inclusion hHK z)).val t s = (1 : Matrix ι ι 𝓀[k]) t s := by
  have hint := ((mem_KO_iff _).1 (hHK z.2)).1 t s
  rw [red_incl_val hHK z t s hint]
  have e : (⟨z.1.val t s, hint⟩ : 𝒪[k]) = (1 : Matrix ι ι 𝒪[k]) t s := by
    apply Subtype.ext
    show z.1.val t s = _
    rw [hrow z.1 z.2 s hs]
    by_cases h : t = s <;> simp [Matrix.one_apply, h]
  rw [e]
  by_cases h : t = s <;> simp [Matrix.one_apply, h]

theorem mem_conj_iff_row {ϖ : kˣ} (hϖ : IsUnif ϖ) {H : Subgroup (GL ι k)} (hHK : H ≤ KO k ι) {t : ι}
    {S : Finset ι} (htS : t ∉ S) (hrow : ∀ x ∈ H, ∀ s, s ∉ S → x.val t s = (1 : Matrix ι ι k) t s) (z : H) :
    (z : GL ι k) ∈ (KO k ι).map (MulAut.conj (diagGL (Pi.mulSingle t ϖ))).toMonoidHom ↔
      (red (Subgroup.inclusion hHK z)).val t = (1 : Matrix ι ι 𝓀[k]) t := by
  set ρ : H →* GL ι 𝓀[k] := red.comp (Subgroup.inclusion hHK) with hρ
  have hint : ∀ w : H, ∀ r s, (w : GL ι k).val r s ∈ 𝒪[k] := fun w => ((mem_KO_iff _).1 (hHK w.2)).1

  have key : ∀ w : H, (∀ s, s ≠ t → (ϖ : k)⁻¹ * (w : GL ι k).val t s ∈ 𝒪[k]) ↔ (ρ w).val t = (1 : Matrix ι ι 𝓀[k]) t := by
    intro w
    constructor
    · intro h
      funext s
      by_cases hs : s = t
      · subst hs; exact red_row_off hHK hrow w s htS
      · show (red (Subgroup.inclusion hHK w)).val t s = _
        rw [red_incl_val hHK w t s (hint w t s), (residue_eq_zero_iff_of_isUnif hϖ _ _).2 (h s hs)]
        simp [Matrix.one_apply, Ne.symm hs]
    · intro h s hs
      have h1 := congrFun h s
      have h2 : (red (Subgroup.inclusion hHK w)).val t s = 0 := by
        rw [show (red (Subgroup.inclusion hHK w)).val t s = (ρ w).val t s from rfl, h1]
        simp [Matrix.one_apply, Ne.symm hs]
      rw [red_incl_val hHK w t s (hint w t s)] at h2
      exact (residue_eq_zero_iff_of_isUnif hϖ _ _).1 h2
  rw [mem_map_conj_iff, mem_KO_iff]
  have hinv : ((diagGL (Pi.mulSingle t ϖ))⁻¹ * (z : GL ι k) * diagGL (Pi.mulSingle t ϖ))⁻¹ =
      (diagGL (Pi.mulSingle t ϖ))⁻¹ * ((z⁻¹ : H) : GL ι k) * diagGL (Pi.mulSingle t ϖ) := by
    simp [mul_assoc]
  rw [hinv, conj_int_iff hϖ t _ (hint z), conj_int_iff hϖ t _ (hint z⁻¹)]
  change _ ↔ (ρ z).val t = _
  rw [key z, key z⁻¹]
  constructor
  · exact fun h => h.1
  · intro h
    refine ⟨h, ?_⟩
    have := (row_inv_iff (1 : GL ι 𝓀[k]) (ρ z) t).1 (by simpa using h)
    rw [map_inv, ← this]; simp

theorem relIndex_rowCong : ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    {ι : Type} [Fintype ι] [DecidableEq ι] (ϖ : kˣ), IsUnif ϖ → ∀ (t : ι) (S : Finset ι), t ∉ S →
    ∀ (H : Subgroup (GL ι k)), H ≤ KO k ι → (∀ x ∈ H, ∀ s, s ∉ S → x.val t s = (1 : Matrix ι ι k) t s) →
    (∀ y : ι → k, (∀ s, y s ∈ 𝒪[k]) → (∀ s, s ∉ S → y s = 0) →
      ∃ x ∈ H, x.val = 1 + Matrix.of (fun r s => if r = t then y s else 0)) →
    ((KO k ι).map (MulAut.conj (diagGL (Pi.mulSingle t ϖ))).toMonoidHom).relIndex H = resCard k ^ S.card := by
  intro k _ _ _ _ ι _ _ ϖ hϖ t S htS H hHK hrow hel
  set A := (KO k ι).map (MulAut.conj (diagGL (Pi.mulSingle t ϖ))).toMonoidHom with hA
  set ρ : H →* GL ι 𝓀[k] := red.comp (Subgroup.inclusion hHK) with hρ
  have hint : ∀ w : H, ∀ r s, (w : GL ι k).val r s ∈ 𝒪[k] := fun w => ((mem_KO_iff _).1 (hHK w.2)).1
  let F : H → (S → 𝓀[k]) := fun x s => (ρ x⁻¹).val t s
  have hF : ∀ x y : H, F x = F y ↔ ((x⁻¹ * y : H) : GL ι k) ∈ A := by
    intro x y
    rw [mem_conj_iff_row hϖ hHK htS hrow]
    change _ ↔ (ρ (x⁻¹ * y)).val t = _
    rw [map_mul, map_inv, row_inv_iff, ← map_inv, ← map_inv]
    constructor
    · intro h
      funext s
      by_cases hs : s ∈ S
      · exact congrFun h ⟨s, hs⟩
      · rw [show (ρ x⁻¹).val t s = (red (Subgroup.inclusion hHK x⁻¹)).val t s from rfl,
          show (ρ y⁻¹).val t s = (red (Subgroup.inclusion hHK y⁻¹)).val t s from rfl,
          red_row_off hHK hrow _ s hs, red_row_off hHK hrow _ s hs]
    · intro h
      funext s
      exact congrFun h s.1
  have hsurj : Function.Surjective F := by
    intro w
    choose lift hlift using fun s : S => IsLocalRing.residue_surjective (R := 𝒪[k]) (w s)
    let y : ι → k := fun s => if h : s ∈ S then ((lift ⟨s, h⟩ : 𝒪[k]) : k) else 0
    obtain ⟨z, hzH, hz⟩ := hel y (fun s => by
        by_cases h : s ∈ S
        · simp only [y, h, dif_pos]; exact (lift ⟨s, h⟩).2
        · simp only [y, h, dif_neg, not_false_eq_true]; exact Subring.zero_mem _)
      (fun s hs => by simp [y, hs])
    refine ⟨(⟨z, hzH⟩ : H)⁻¹, ?_⟩
    funext s
    have hst : t ≠ s.1 := fun h => htS (h ▸ s.2)
    show (red (Subgroup.inclusion hHK ((⟨z, hzH⟩ : H)⁻¹)⁻¹)).val t s = w s
    rw [inv_inv, red_incl_val hHK _ t s (hint _ t s)]
    have e : (⟨((⟨z, hzH⟩ : H) : GL ι k).val t s, hint _ t s⟩ : 𝒪[k]) = lift s := by
      apply Subtype.ext
      show z.val t s = _
      rw [hz]
      simp [y, Matrix.one_apply, hst, s.2]
    rw [e, hlift]
  have hcard : Nat.card (H ⧸ A.subgroupOf H) = Nat.card (S → 𝓀[k]) := by
    refine Nat.card_congr (Equiv.ofBijective (Quotient.lift F fun a b hab => (hF a b).2 ?_) ⟨?_, ?_⟩)
    · have := QuotientGroup.leftRel_apply.mp hab
      simpa [Subgroup.mem_subgroupOf] using this
    · intro a b
      induction a using QuotientGroup.induction_on
      induction b using QuotientGroup.induction_on
      intro h
      rw [QuotientGroup.eq, Subgroup.mem_subgroupOf]
      exact (hF _ _).1 h
    · intro w
      obtain ⟨x, hx⟩ := hsurj w
      exact ⟨QuotientGroup.mk x, hx⟩
  rw [Subgroup.relIndex, Subgroup.index, hcard, Nat.card_fun, resCard, Nat.card_eq_fintype_card (α := S),
    Fintype.card_coe]

end GlobalTheory.DiagVol.RowIdx
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RelIndexUpLatEqSq
section
open GlobalTheory.LGrp GlobalTheory.BorelUMod Formalism.UG

noncomputable section
namespace GlobalTheory.BorelUMod

theorem relIndex_prod_prod {G G' : Type} [AddGroup G] [AddGroup G'] (H K : AddSubgroup G) (H' K' : AddSubgroup G') :
    (H.prod H').relIndex (K.prod K') = H.relIndex K * H'.relIndex K' := by
  unfold AddSubgroup.relIndex
  rw [← AddSubgroup.index_prod,
    ← AddSubgroup.index_comap_of_surjective ((H.addSubgroupOf K).prod (H'.addSubgroupOf K'))
      (f := (AddSubgroup.prodEquiv K K').toAddMonoidHom) (AddSubgroup.prodEquiv K K').surjective]
  congr 1

variable {L : Type} [Field L] {n : ℕ}

def skewPair (σ : L →+* L) (θ d : L) :
    Matrix (Fin n) (Fin n) L →+ Matrix (Fin n) (Fin n) L × Matrix (Fin n) (Fin n) L :=
  AddMonoidHom.mk' (fun X => (X - θ • (X + adjJ σ X), d • (X + adjJ σ X))) (fun X Y => by
    ext i j <;> simp [adjJ] <;> ring)

theorem skewPair_injective (σ : L →+* L) (θ : L) {d : L} (hd : d ≠ 0) :
    Function.Injective (skewPair (n := n) σ θ d) := by
  set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
  intro X hX
  have h1 : X - θ • (X + adjJ σ X) = 0 := congrArg Prod.fst hX
  have h2 : d • (X + adjJ σ X) = 0 := congrArg Prod.snd hX
  have h3 : X + adjJ σ X = 0 := (smul_eq_zero.1 h2).resolve_left hd
  simpa [h3] using h1

variable [Valued L (WithZero (Multiplicative ℤ))]

theorem map_skewPair_upLat {σ : L →+* L} (hσ : ∀ x, σ (σ x) = x) (hv : ∀ x, Valued.v (σ x) = Valued.v x)
    {θ d : L} (hθ : Valued.v θ ≤ 1) (hθ1 : θ + σ θ = 1) (hd : Valued.v d = 1) (hd1 : σ d = -d)
    {c : Fin n → Fin n → ℤ} (hc : ∀ i j, c j.rev i.rev = c i j) :
    (upLat L c).map (skewPair σ θ d) = (upLat L c ⊓ skewJ σ n).prod (upLat L c ⊓ skewJ σ n) := by
  have hd0 : d ≠ 0 := fun e => by simp [e] at hd
  have hσθ : σ θ = 1 - θ := by linear_combination hθ1
  apply le_antisymm
  · rintro _ ⟨X, hX, rfl⟩
    have hs : X + adjJ σ X ∈ upLat L c := add_mem hX (adjJ_mem_upLat hv hc hX)
    refine ⟨⟨(upLat L c).sub_mem hX (smul_mem_upLat hθ hs), ?_⟩, ⟨smul_mem_upLat hd.le hs, ?_⟩⟩
    · show adjJ σ (X - θ • (X + adjJ σ X)) = -(X - θ • (X + adjJ σ X))
      rw [adjJ_sub, adjJ_smul, adjJ_add, adjJ_adjJ hσ, hσθ]
      module
    · show adjJ σ (d • (X + adjJ σ X)) = -(d • (X + adjJ σ X))
      rw [adjJ_smul, adjJ_add, adjJ_adjJ hσ, hd1]
      module
  · rintro ⟨A, B⟩ ⟨⟨hA, hA'⟩, ⟨hB, hB'⟩⟩
    have hA2 : adjJ σ A = -A := hA'
    have hB2 : adjJ σ B = -B := hB'
    have hv' : Valued.v (θ * d⁻¹) ≤ 1 := by simpa [hd] using hθ
    refine ⟨A + (θ * d⁻¹) • B, add_mem hA (smul_mem_upLat hv' hB), ?_⟩
    have key : A + (θ * d⁻¹) • B + adjJ σ (A + (θ * d⁻¹) • B) = d⁻¹ • B := by
      rw [adjJ_add, adjJ_smul, hA2, hB2, map_mul, map_inv₀, hd1, hσθ, inv_neg]
      module
    show (A + (θ * d⁻¹) • B - θ • (A + (θ * d⁻¹) • B + adjJ σ (A + (θ * d⁻¹) • B)),
      d • (A + (θ * d⁻¹) • B + adjJ σ (A + (θ * d⁻¹) • B))) = (A, B)
    rw [key, smul_smul, smul_smul, mul_inv_cancel₀ hd0, one_smul, add_sub_cancel_right]

theorem relIndex_upLat_eq_sq : ∀ (L : Type) [Field L] [Valued L (WithZero (Multiplicative ℤ))] (ϖ : L) (σ : L →+* L)
    (q n : ℕ), IsUnramInv ϖ σ q → ∀ (c C : Fin n → Fin n → ℤ), (∀ i j, c j.rev i.rev = c i j) →
    (∀ i j, C j.rev i.rev = C i j) → (∀ i j, i < j → c i j ≤ C i j) →
    (upLat L C).relIndex (upLat L c) = ((upLat L C ⊓ skewJ σ n).relIndex (upLat L c ⊓ skewJ σ n)) ^ 2 := by
  intro L _ _ ϖ σ q n h c C hc hC _
  obtain ⟨⟨θ, hθ, hθ1⟩, d, hd, hd1⟩ := exists_trace_one h
  have hd0 : d ≠ 0 := fun e => by simp [e] at hd
  rw [← AddSubgroup.relIndex_map_map_of_injective _ _ (skewPair_injective σ θ hd0),
    map_skewPair_upLat h.1 h.2.1 hθ hθ1 hd hd1 hc, map_skewPair_upLat h.1 h.2.1 hθ hθ1 hd hd1 hC,
    relIndex_prod_prod, sq]

end GlobalTheory.BorelUMod
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitaryCharacterAbsScalarBasicPropertiesStatement
section
open MeasureTheory Matrix GlobalTheory.KSp GlobalTheory.SplitUnitary
open GlobalTheory.WeilM (UG IsQuad IsHerm ResEtaPow)
open GlobalTheory.SplitWeil (SB nabs)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.unitaryCharacterAbsScalar_basic_properties : ∀ (F : Type) [Field F] [CharZero F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] (E : Type) [Field E] [Algebra F E] [TopologicalSpace E] [IsModuleTopology F E] (c : E →ₐ[F] E) (δ : E) (hE : IsQuad c δ) (m : ℕ) (χ : Eˣ →* Circle) (_ : ResEtaPow (R := F) ⊥ χ m), sc F χ m 1 = 1 ∧ (∀ z z' : E, sc F χ m (z * z') = sc F χ m z * sc F χ m z') ∧ (∀ z : Eˣ, sc F χ m (z : E) = (χ z : ℂ) * ((nabs F ((Units.map (Algebra.norm F : E →* F)) z) ^ ((m : ℝ) / 2) : ℝ) : ℂ)) ∧ (∀ z : Eˣ, ‖sc F χ m (z : E)‖ ^ 2 = nabs F ((Units.map (Algebra.norm F : E →* F)) z) ^ m) ∧ (∀ z : Eˣ, sc F χ m (c (z : E))⁻¹ * ((nabs F ((Units.map (Algebra.norm F : E →* F)) z) ^ m : ℝ) : ℂ) = sc F χ m (z : E)) ∧ (∀ t : Fˣ, sc F χ m (algebraMap F E t) = (sgn E t * (nabs F t : ℝ)) ^ m) ∧ ∀ z : Eˣ, sc F χ m ((z : E) * c (z : E)) = ((nabs F ((Units.map (Algebra.norm F : E →* F)) z) ^ m : ℝ) : ℂ) := by
  first | exact @GlobalTheory.KSp.sc_basic | exact GlobalTheory.KSp.sc_basic | (intros; apply GlobalTheory.KSp.sc_basic <;> assumption)
end

