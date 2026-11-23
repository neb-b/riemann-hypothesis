module

public import Mathlib

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.KTheoryStability.ReductionBoundsTorsion.ArithmeticGapBounds.AEConst
section
noncomputable section

open MeasureTheory
open scoped InnerProductSpace

namespace PositivityTheory.KB.SpectralGap

def avg {Λ S : Type} [Group Λ] [Group S] (j : Λ →* S) (B K : Subgroup Λ) (u : S → ℝ) (x : S) : ℝ :=
  ((B.subgroupOf K).index : ℝ)⁻¹ *
    ∑ᶠ c : Quotient (QuotientGroup.rightRel (B.subgroupOf K)), u (j ((c.out : K) : Λ) * x)

def TwoTr {Λ : Type} [Group Λ] (E K : Subgroup Λ) : Prop :=
  ∀ g ∈ K, g ∉ E → ∀ g' ∈ K, g' ∉ E → ∃ e ∈ E, ∃ e' ∈ E, g' = e * g * e'

def LInv {Λ S : Type} [Group Λ] [Group S] (j : Λ →* S) (E : Subgroup Λ) (u : S → ℝ) : Prop :=
  ∀ γ ∈ E, ∀ x, u (j γ * x) = u x

def Hilb : Prop := ∀ (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
  (W₁ W₂ W₃ K₁₂ K₁₃ K₂₃ : Submodule ℝ H), IsClosed (W₁ : Set H) → IsClosed (W₂ : Set H) → IsClosed (W₃ : Set H) →
  IsClosed (K₁₂ : Set H) → IsClosed (K₁₃ : Set H) → IsClosed (K₂₃ : Set H) →
  K₁₂ ≤ W₁ ⊓ W₂ → K₁₃ ≤ W₁ ⊓ W₃ → K₂₃ ≤ W₂ ⊓ W₃ →
  (∀ u ∈ W₁, u ∈ K₁₂ᗮ → ∀ u' ∈ W₂, |⟪u, u'⟫_ℝ| ≤ 1 / 5 * (‖u‖ * ‖u'‖)) →
  (∀ u ∈ W₃, u ∈ K₁₃ᗮ → ∀ u' ∈ W₁, |⟪u, u'⟫_ℝ| ≤ 1 / 5 * (‖u‖ * ‖u'‖)) →
  (∀ u ∈ W₃, u ∈ K₂₃ᗮ → ∀ u' ∈ W₂, |⟪u, u'⟫_ℝ| ≤ 1 / 5 * (‖u‖ * ‖u'‖)) →
  ∀ v ∈ W₁ ⊓ W₂, v ∈ (W₁ ⊓ W₂ ⊓ W₃)ᗮ → ∀ w ∈ W₁ ⊓ W₃, |⟪v, w⟫_ℝ| ≤ 2 / 5 * (‖v‖ * ‖w‖)

def Design : Prop := ∀ (Λ S : Type) [Group Λ] [Group S] (j : Λ →* S) (B E E' K : Subgroup Λ), B = E ⊓ E' → E ≤ K →
  E' ≤ K → (B.subgroupOf K).index ≠ 0 → TwoTr E K → 25 ≤ (B.subgroupOf E').index →
  ∀ (a b : S → ℝ), LInv j E a → LInv j E' b → ∀ x, avg j B K a x = 0 →
    avg j B K (fun y => a y * b y) x ^ 2 ≤
      1 / 25 * (avg j B K (fun y => a y ^ 2) x * avg j B K (fun y => b y ^ 2) x)

def Unfold : Prop := ∀ (Λ S : Type) [Group Λ] [Countable Λ] [Group S] [MeasurableSpace S] [MeasurableMul S]
  (μ : Measure S) [μ.IsMulLeftInvariant] (j : Λ →* S), Function.Injective j → ∀ (B K : Subgroup Λ), B ≤ K →
  (B.subgroupOf K).index ≠ 0 →
  (∀ u : S → ℝ, LInv j B u → LInv j K (avg j B K u)) ∧ (∀ u : S → ℝ, LInv j K u → avg j B K u = u) ∧
  (∀ u : S → ℝ, Measurable u → Measurable (avg j B K u)) ∧
  (∀ E : Subgroup Λ, B ≤ E → E ≤ K → ∀ u : S → ℝ, LInv j B u → avg j E K (avg j B E u) = avg j B K u) ∧
  ∀ D : Set S, IsFundamentalDomain (K.map j) D μ →
    (∃ D' : Set S, IsFundamentalDomain (B.map j) D' μ) ∧
    ∀ D' : Set S, IsFundamentalDomain (B.map j) D' μ → μ D' = (B.subgroupOf K).index * μ D ∧
      ∀ u : S → ℝ, Measurable u → LInv j B u →
        (IntegrableOn u D' μ ↔ IntegrableOn (avg j B K fun y => |u y|) D μ) ∧
        (IntegrableOn u D' μ → IntegrableOn (avg j B K u) D μ ∧
          ∫ x in D', u x ∂μ = (B.subgroupOf K).index * ∫ x in D, avg j B K u x ∂μ)

def AEConst : Prop := ∀ (S : Type) [Group S] [TopologicalSpace S] [IsTopologicalGroup S] [LocallyCompactSpace S]
  [SecondCountableTopology S] [T2Space S] [MeasurableSpace S] [BorelSpace S] (μ : Measure S) [μ.IsHaarMeasure]
  (A : Subgroup S), Dense (A : Set S) → ∀ u : S → ℝ, Measurable u → (∀ g ∈ A, (fun x => u (g * x)) =ᵐ[μ] u) →
    ∃ c : ℝ, u =ᵐ[μ] fun _ => c

structure Tri {Λ : Type} [Group Λ] (K₀ K₁ K₂ : Subgroup Λ) : Prop where
  fin₀ : ((K₀ ⊓ K₁ ⊓ K₂).subgroupOf K₀).index ≠ 0
  fin₁ : ((K₀ ⊓ K₁ ⊓ K₂).subgroupOf K₁).index ≠ 0
  fin₂ : ((K₀ ⊓ K₁ ⊓ K₂).subgroupOf K₂).index ≠ 0
  two₀ : TwoTr (K₀ ⊓ K₁) K₀
  two₁ : TwoTr (K₁ ⊓ K₂) K₁
  two₂ : TwoTr (K₁ ⊓ K₂) K₂
  big₀₂ : 25 ≤ ((K₀ ⊓ K₁ ⊓ K₂).subgroupOf (K₀ ⊓ K₂)).index
  big₀₁ : 25 ≤ ((K₀ ⊓ K₁ ⊓ K₂).subgroupOf (K₀ ⊓ K₁)).index

def GapAbs : Prop := ∀ (Λ S : Type) [Group Λ] [Countable Λ] [Group S] [TopologicalSpace S] [IsTopologicalGroup S]
  [LocallyCompactSpace S] [SecondCountableTopology S] [T2Space S] [MeasurableSpace S] [BorelSpace S]
  (μ : Measure S) [μ.IsHaarMeasure] (j : Λ →* S), Function.Injective j → ∀ (K₀ K₁ K₂ : Subgroup Λ), Tri K₀ K₁ K₂ →
  Dense (((K₀ ⊔ K₁).map j : Subgroup S) : Set S) → ∀ D₀ D₁ D₂ : Set S, IsFundamentalDomain (K₀.map j) D₀ μ →
  IsFundamentalDomain (K₁.map j) D₁ μ → IsFundamentalDomain (K₂.map j) D₂ μ → μ D₀ < ⊤ → μ D₁ = μ D₀ →
  ∀ w : S → ℝ, Measurable w → LInv j K₁ w → IntegrableOn (fun x => w x ^ 2) D₁ μ → ∫ x in D₁, w x ∂μ = 0 →
    IntegrableOn (fun x => avg j (K₀ ⊓ K₁) K₀ w x ^ 2) D₀ μ ∧ ∫ x in D₀, avg j (K₀ ⊓ K₁) K₀ w x ∂μ = 0 ∧
      ∫ x in D₀, avg j (K₀ ⊓ K₁) K₀ w x ^ 2 ∂μ ≤ (2 / 5 : ℝ) ^ 2 * ∫ x in D₁, w x ^ 2 ∂μ

end PositivityTheory.KB.SpectralGap

end
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.KTheoryStability.ReductionBoundsTorsion.ArithmeticGapBounds.PDensG
section
namespace PositivityTheory.KB.SpectralGap.WordTransvectionCongruences

open Matrix

theorem diagonal_decomposition_transvections {ι F : Type*} [Fintype ι] [DecidableEq ι] [Field F] {i j : ι} (hij : i ≠ j)
    {a : F} (ha : a ≠ 0) :
    SpecialLinearGroup.diag2n hij a ha = SpecialLinearGroup.transvection hij a *
      SpecialLinearGroup.transvection hij.symm (-a⁻¹) * SpecialLinearGroup.transvection hij a *
      SpecialLinearGroup.transvection hij (-1) * SpecialLinearGroup.transvection hij.symm 1 *
      SpecialLinearGroup.transvection hij (-1) := by
  apply SpecialLinearGroup.coeMonoidHom_injective
  simp only [map_mul, SpecialLinearGroup.coeMonoidHom_apply, SpecialLinearGroup.diag2n_coe, SpecialLinearGroup.transvection_coe, mul_add, add_mul,
    one_mul, mul_one, single_mul_single_same]
  simp only [single_mul_single_of_ne _ _ _ _ hij.symm, single_mul_single_of_ne _ _ _ _ hij,
    zero_add, add_zero, single_mul_single_same, zero_mul, mul_zero]
  ext x y
  by_cases hxi : i = x
  · subst x
    by_cases hyi : i = y
    · subst y; (simp [Matrix.add_apply, Matrix.one_apply, Matrix.single_apply, diagonal_apply, hij, hij.symm, ha, *]
        <;> (try field_simp) <;> (try ring) <;> (try (split_ifs <;> simp_all)))
    by_cases hyj : j = y
    · subst y; (simp [Matrix.add_apply, Matrix.one_apply, Matrix.single_apply, diagonal_apply, hij, hij.symm, ha, *]
        <;> (try field_simp) <;> (try ring) <;> (try (split_ifs <;> simp_all)))
    (simp [Matrix.add_apply, Matrix.one_apply, Matrix.single_apply, diagonal_apply, hij, hij.symm, ha, *]
        <;> (try field_simp) <;> (try ring) <;> (try (split_ifs <;> simp_all)))
  by_cases hxj : j = x
  · subst x
    by_cases hyi : i = y
    · subst y; (simp [Matrix.add_apply, Matrix.one_apply, Matrix.single_apply, diagonal_apply, hij, hij.symm, ha, *]
        <;> (try field_simp) <;> (try ring) <;> (try (split_ifs <;> simp_all)))
    by_cases hyj : j = y
    · subst y; (simp [Matrix.add_apply, Matrix.one_apply, Matrix.single_apply, diagonal_apply, hij, hij.symm, ha, *]
        <;> (try field_simp) <;> (try ring) <;> (try (split_ifs <;> simp_all)))
    (simp [Matrix.add_apply, Matrix.one_apply, Matrix.single_apply, diagonal_apply, hij, hij.symm, ha, *]
        <;> (try field_simp) <;> (try ring) <;> (try (split_ifs <;> simp_all)))
  by_cases hyi : i = y
  · subst y; (simp [Matrix.add_apply, Matrix.one_apply, Matrix.single_apply, diagonal_apply, hij, hij.symm, ha, *]
        <;> (try field_simp) <;> (try ring) <;> (try (split_ifs <;> simp_all)))
  by_cases hyj : j = y
  · subst y; (simp [Matrix.add_apply, Matrix.one_apply, Matrix.single_apply, diagonal_apply, hij, hij.symm, ha, *]
        <;> (try field_simp) <;> (try ring) <;> (try (split_ifs <;> simp_all)))
  (simp [Matrix.add_apply, Matrix.one_apply, Matrix.single_apply, diagonal_apply, hij, hij.symm, ha, *]
        <;> (try field_simp) <;> (try ring) <;> (try (split_ifs <;> simp_all)))

theorem sl_top {ι F : Type*} [Fintype ι] [DecidableEq ι] [Nontrivial ι] [Field F]
    (S : Subgroup (SpecialLinearGroup ι F))
    (h : ∀ (i j : ι) (hij : i ≠ j) (c : F), SpecialLinearGroup.transvection hij c ∈ S) : S = ⊤ := by
  have hdiag : ∀ (i j : ι) (hij : i ≠ j) {c : F} (hc : c ≠ 0),
      SpecialLinearGroup.diag2n hij c hc ∈ S := by
    intro i j hij c hc
    rw [diagonal_decomposition_transvections hij hc]
    exact S.mul_mem (S.mul_mem (S.mul_mem (S.mul_mem (S.mul_mem (h _ _ _ _) (h _ _ _ _))
      (h _ _ _ _)) (h _ _ _ _)) (h _ _ _ _)) (h _ _ _ _)
  refine eq_top_iff.2 fun M _ => ?_
  exact SpecialLinearGroup.diagonal_transvection_induction' (· ∈ S) M hdiag h
    (fun _ _ => S.mul_mem)

end PositivityTheory.KB.SpectralGap.WordTransvectionCongruences
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.KTheoryStability.ReductionBoundsTorsion.ArithmeticGapBounds.PDensM
section
namespace PositivityTheory.KB.SpectralGap.WordTransvectionCongruences

open NumberField NumberField.mixedEmbedding NumberField.InfinitePlace

theorem two_le_prod {L : Type*} [Field L] [NumberField L] (π : 𝓞 L) (hπ : ¬ IsUnit π) (h0 : π ≠ 0) :
    (2 : ℝ) ≤ ∏ w : InfinitePlace L, w (π : L) ^ w.mult := by
  have h2 : |(Algebra.norm ℚ (π : L))| ≠ 1 := by
    intro h
    apply hπ
    rw [NumberField.isUnit_iff_norm]
    simpa [RingOfIntegers.coe_norm] using h
  rw [NumberField.InfinitePlace.prod_eq_abs_norm, ← Algebra.coe_norm_int] at *
  have h1 : Algebra.norm ℤ π ≠ 0 := Algebra.norm_ne_zero_iff.mpr h0
  set n := Algebra.norm ℤ π
  have h3 : |n| ≠ 1 := by
    intro h
    apply h2
    exact_mod_cast h
  have h4 : 2 ≤ |n| := by
    have := abs_pos.mpr h1
    omega
  exact_mod_cast h4

theorem exists_small {L : Type*} [Field L] [NumberField L] (π : 𝓞 L) (hπ : ¬ IsUnit π) (h0 : π ≠ 0)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ y : 𝓞 L, y ≠ 0 ∧ ∃ k : ℕ, ∀ w : InfinitePlace L, w ((y : L) / (π : L) ^ k) < ε := by
  have hP := two_le_prod π hπ h0
  set P := ∏ w : InfinitePlace L, w (π : L) ^ w.mult with hPdef
  set E : ℝ := ∏ w : InfinitePlace L, ε ^ w.mult with hEdef
  have hE : 0 < E := Finset.prod_pos fun w _ => pow_pos hε _
  have hc : (0 : ℝ) < mixedEmbedding.convexBodyLTFactor L := by
    have := mixedEmbedding.convexBodyLTFactor_ne_zero L
    positivity
  have hB := mixedEmbedding.minkowskiBound_lt_top L 1
  obtain ⟨k, hk⟩ := pow_unbounded_of_one_lt
    ((mixedEmbedding.minkowskiBound L 1).toReal / (mixedEmbedding.convexBodyLTFactor L * E))
    (by linarith : (1 : ℝ) < P)
  have hπw : ∀ w : InfinitePlace L, 0 < w (π : L) := fun w => by
    rw [InfinitePlace.pos_iff]
    exact_mod_cast h0
  let f : InfinitePlace L → NNReal := fun w => ⟨ε * w (π : L) ^ k, by have := hπw w; positivity⟩
  have hf : ((∏ w, f w ^ w.mult : NNReal) : ℝ) = E * P ^ k := by
    rw [NNReal.coe_prod, hEdef, hPdef, ← Finset.prod_pow, ← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun w _ => ?_
    change (ε * w (π : L) ^ k) ^ w.mult = _
    rw [mul_pow, ← pow_mul, ← pow_mul, mul_comm k]
  obtain ⟨a, ha0, ha⟩ := mixedEmbedding.exists_ne_zero_mem_ringOfIntegers_lt L (f := f) (by
    rw [mixedEmbedding.convexBodyLT_volume, ← ENNReal.coe_mul]
    rw [← ENNReal.toReal_lt_toReal hB.ne ENNReal.coe_ne_top]
    rw [ENNReal.coe_toReal, NNReal.coe_mul, hf]
    rw [div_lt_iff₀ (by positivity)] at hk
    linarith)
  refine ⟨a, ha0, k, fun w => ?_⟩
  rw [map_div₀, map_pow, div_lt_iff₀ (pow_pos (hπw w) _)]
  exact ha w

theorem exists_near {L : Type*} [Field L] [NumberField L] [_root_.NumberField.IsTotallyComplex L] :
    ∃ R : ℝ, ∀ v : InfinitePlace L → ℂ, ∃ a : 𝓞 L, ∀ w, ‖v w - w.embedding (a : L)‖ ≤ R := by
  classical
  set b := mixedEmbedding.latticeBasis L
  refine ⟨∑ i, ‖b i‖, fun v => ?_⟩
  let x : mixedEmbedding.mixedSpace L := (0, fun w => v w.1)
  have hm := (ZSpan.floor b x).2
  rw [mixedEmbedding.mem_span_latticeBasis] at hm
  obtain ⟨a, ha⟩ := hm
  refine ⟨a, fun w => ?_⟩
  have hw : w.IsComplex := IsTotallyComplex.isComplex w
  have hfr := ZSpan.norm_fract_le b x
  rw [ZSpan.fract_apply, ← ha] at hfr
  refine le_trans ?_ hfr
  refine le_trans ?_ (norm_snd_le _)
  refine le_trans (le_of_eq ?_) (norm_le_pi_norm _ ⟨w, hw⟩)
  simp [x, mixedEmbedding.mixedEmbedding_apply_isComplex]

theorem dense_pow {L : Type*} [Field L] [NumberField L] [_root_.NumberField.IsTotallyComplex L] (π : 𝓞 L)
    (hπ : ¬ IsUnit π) (h0 : π ≠ 0) :
    Dense {z : InfinitePlace L → ℂ | ∃ t : 𝓞 L, ∃ k : ℕ,
      z = fun w => w.embedding ((t : L) / (π : L) ^ k)} := by
  obtain ⟨R, hR⟩ := exists_near (L := L)
  rw [Metric.dense_iff]
  intro z δ hδ
  have hε : 0 < δ / (|R| + 1) := by positivity
  obtain ⟨y, hy0, k, hyk⟩ := exists_small π hπ h0 hε
  set q : L := (y : L) / (π : L) ^ k with hqdef
  have hq : q ≠ 0 := div_ne_zero (by exact_mod_cast hy0) (pow_ne_zero _ (by exact_mod_cast h0))
  obtain ⟨a, ha⟩ := hR (fun w => z w / w.embedding q)
  refine ⟨fun w => w.embedding (((a * y : 𝓞 L) : L) / (π : L) ^ k), ?_, a * y, k, rfl⟩
  rw [Metric.mem_ball, dist_pi_lt_iff hδ]
  intro w
  have heq : w.embedding q ≠ 0 := by
    rw [ne_eq, map_eq_zero]
    exact hq
  have hsplit : z w - w.embedding (((a * y : 𝓞 L) : L) / (π : L) ^ k)
      = (z w / w.embedding q - w.embedding (a : L)) * w.embedding q := by
    rw [show (((a * y : 𝓞 L) : L) / (π : L) ^ k) = (a : L) * q by
      rw [hqdef]; push_cast; ring]
    rw [map_mul, sub_mul, div_mul_cancel₀ _ heq]
  rw [dist_comm, dist_eq_norm, hsplit, norm_mul, InfinitePlace.norm_embedding_eq]
  have h1 := ha w
  have h2 := hyk w
  have hR0 : 0 ≤ R := le_trans (norm_nonneg _) h1
  have hwq : 0 ≤ w q := by positivity
  have h3 : ‖z w / w.embedding q - w.embedding (a : L)‖ * w q ≤ |R| * (δ / (|R| + 1)) :=
    calc ‖z w / w.embedding q - w.embedding (a : L)‖ * w q ≤ R * (δ / (|R| + 1)) :=
          mul_le_mul h1 h2.le hwq hR0
      _ = |R| * (δ / (|R| + 1)) := by rw [abs_of_nonneg hR0]
  have h4 : |R| * (δ / (|R| + 1)) < δ := by
    rw [mul_div_assoc', div_lt_iff₀ (by positivity)]
    nlinarith [abs_nonneg R]
  linarith

end PositivityTheory.KB.SpectralGap.WordTransvectionCongruences
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.KTheoryStability.ReductionBoundsTorsion.ArithmeticGapBounds.PGlueG
section
noncomputable section

open MeasureTheory

namespace PositivityTheory.KB.SpectralGap.GlueG

theorem eq_of_mk_eq {Γ : Type} [Group Γ] (H : Subgroup Γ) {E : Type} (F : Γ → E)
    (hF : ∀ h ∈ H, ∀ γ, F (h * γ) = F γ) {x y : Γ}
    (hxy : (Quotient.mk (QuotientGroup.rightRel H) x) = Quotient.mk (QuotientGroup.rightRel H) y) :
    F x = F y := by
  have h1 : y * x⁻¹ ∈ H := QuotientGroup.rightRel_apply.1 (Quotient.exact hxy)
  have := hF _ h1 x
  rw [inv_mul_cancel_right] at this
  exact this.symm

theorem finsum_transfer {A Γ : Type} [Group A] [Group Γ] (ψ : A →* Γ) (H : Subgroup Γ) (C : Subgroup A)
    (hC : ∀ a, ψ a ∈ H ↔ a ∈ C) (hs : ∀ γ, ∃ a, γ * (ψ a)⁻¹ ∈ H)
    {E : Type} [AddCommMonoid E] (F : Γ → E) (hF : ∀ h ∈ H, ∀ γ, F (h * γ) = F γ) :
    ∑ᶠ c : Quotient (QuotientGroup.rightRel H), F c.out =
        ∑ᶠ c : Quotient (QuotientGroup.rightRel C), F (ψ c.out) ∧ C.index = H.index := by
  have key : ∀ a b : A, (QuotientGroup.rightRel C) a b ↔ (QuotientGroup.rightRel H) (ψ a) (ψ b) := by
    intro a b
    rw [QuotientGroup.rightRel_apply, QuotientGroup.rightRel_apply, ← hC, map_mul, map_inv]
  let e0 : Quotient (QuotientGroup.rightRel C) → Quotient (QuotientGroup.rightRel H) :=
    Quotient.map' ψ fun a b h => (key a b).1 h
  have he0 : ∀ a, e0 (Quotient.mk _ a) = Quotient.mk _ (ψ a) := fun a => rfl
  have hbij : Function.Bijective e0 := by
    constructor
    · intro c c' hcc'
      induction c using Quotient.inductionOn
      induction c' using Quotient.inductionOn
      rw [he0, he0] at hcc'
      exact Quotient.sound ((key _ _).2 (Quotient.exact hcc'))
    · intro c
      induction c using Quotient.inductionOn with
      | h γ =>
        obtain ⟨a, ha⟩ := hs γ
        exact ⟨Quotient.mk _ a, by
          rw [he0]
          exact Quotient.sound (QuotientGroup.rightRel_apply.2 ha)⟩
  let e := Equiv.ofBijective e0 hbij
  constructor
  · rw [← finsum_comp_equiv e]
    refine finsum_congr fun c => ?_
    apply eq_of_mk_eq H F hF
    show Quotient.mk _ (e0 c).out = _
    rw [Quotient.out_eq]
    conv_lhs => rw [← Quotient.out_eq c]
    rfl
  · unfold Subgroup.index
    rw [← Nat.card_congr (QuotientGroup.quotientRightRelEquivQuotientLeftRel C),
      ← Nat.card_congr (QuotientGroup.quotientRightRelEquivQuotientLeftRel H)]
    exact Nat.card_congr e

theorem finsum_mul_right {Γ : Type} [Group Γ] (H : Subgroup Γ) {E : Type} [AddCommMonoid E] (F : Γ → E)
    (hF : ∀ h ∈ H, ∀ γ, F (h * γ) = F γ) (γ₀ : Γ) :
    ∑ᶠ c : Quotient (QuotientGroup.rightRel H), F (c.out * γ₀) =
      ∑ᶠ c : Quotient (QuotientGroup.rightRel H), F c.out := by
  have key : ∀ a b : Γ, (QuotientGroup.rightRel H) a b ↔
      (QuotientGroup.rightRel H) ((Equiv.mulRight γ₀) a) ((Equiv.mulRight γ₀) b) := by
    intro a b
    simp only [QuotientGroup.rightRel_apply, Equiv.coe_mulRight, mul_inv_rev, mul_assoc,
      mul_inv_cancel_left]
  let e : Quotient (QuotientGroup.rightRel H) ≃ Quotient (QuotientGroup.rightRel H) :=
    Quotient.congr (Equiv.mulRight γ₀) key
  have h1 : ∀ c, F (e c).out = F (c.out * γ₀) := by
    intro c
    apply eq_of_mk_eq H F hF
    rw [Quotient.out_eq]
    conv_lhs => rw [← Quotient.out_eq c]
    rfl
  calc ∑ᶠ c : Quotient (QuotientGroup.rightRel H), F (c.out * γ₀)
      = ∑ᶠ c : Quotient (QuotientGroup.rightRel H), F (e c).out := finsum_congr fun c => (h1 c).symm
    _ = _ := finsum_comp_equiv e (f := fun c => F c.out)

theorem continuous_finsum_quot {Γ X : Type} [Group Γ] [TopologicalSpace X] (H : Subgroup Γ) (hH : H.index ≠ 0)
    (F : Γ → X → ℝ) (hF : ∀ γ, Continuous (F γ)) :
    Continuous fun x => ∑ᶠ c : Quotient (QuotientGroup.rightRel H), F c.out x := by
  have : H.FiniteIndex := ⟨hH⟩
  have : Finite (Quotient (QuotientGroup.rightRel H)) :=
    Finite.of_equiv _ (QuotientGroup.quotientRightRelEquivQuotientLeftRel H).symm
  let _ := Fintype.ofFinite (Quotient (QuotientGroup.rightRel H))
  simp_rw [finsum_eq_sum_of_fintype]
  exact continuous_finsetSum _ fun c _ => hF _

theorem fund_conj {S : Type} [Group S] [MeasurableSpace S] [MeasurableMul S] (μ : Measure S)
    [μ.IsMulLeftInvariant] (G₁ G₂ : Subgroup S) (q : S) (hq : ∀ y, y ∈ G₂ ↔ q * y * q⁻¹ ∈ G₁) (D : Set S)
    (hD : IsFundamentalDomain G₁ D μ) :
    IsFundamentalDomain G₂ ((fun x => q * x) ⁻¹' D) μ ∧ μ ((fun x => q * x) ⁻¹' D) = μ D ∧
      ∀ u : S → ℝ, (IntegrableOn (fun x => u (q * x)) ((fun x => q * x) ⁻¹' D) μ ↔ IntegrableOn u D μ) ∧
        ∫ x in (fun x => q * x) ⁻¹' D, u (q * x) ∂μ = ∫ x in D, u x ∂μ := by
  have hmp : MeasurePreserving (fun x => q * x) μ μ := measurePreserving_mul_left μ q
  have hemb : MeasurableEmbedding (fun x => q * x) := (MeasurableEquiv.mulLeft q).measurableEmbedding
  have hmem : ∀ g : G₁, q⁻¹ * (g : S) * q ∈ G₂ := fun g => by
    rw [hq]
    simp [mul_assoc]
  let e : G₁ → G₂ := fun g => ⟨q⁻¹ * g * q, hmem g⟩
  have hbij : Function.Bijective e := by
    constructor
    · intro g g' h
      have h' := congrArg (fun x : G₂ => (x : S)) h
      simp only [e, mul_left_inj, mul_right_inj] at h'
      exact Subtype.ext h'
    · intro h
      refine ⟨⟨q * h * q⁻¹, (hq h).1 h.2⟩, Subtype.ext ?_⟩
      simp [e, mul_assoc]
  refine ⟨hD.preimage_of_equiv hmp.quasiMeasurePreserving hbij ?_, measure_preimage_mul μ q D, fun u =>
    ⟨hmp.integrableOn_comp_preimage hemb, hmp.setIntegral_preimage_emb hemb u D⟩⟩
  intro g x
  simp [e, Subgroup.smul_def, mul_assoc]

end PositivityTheory.KB.SpectralGap.GlueG

end
end

