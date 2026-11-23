module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.Bundle0011
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.Bundle0004
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.Bundle0007
public import Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.Bundle0012
public import Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.Bundle0009
public import Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.Bundle0008

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.CompactSpaceRealUnitaryGroupOfDefiniteStatement
section
open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up MeasureTheory Topology
open scoped ComplexOrder ENNReal Matrix
variable {E : Type} [Field E] [NumberField E] [IsCMField E]
theorem _root_.GlobalTheory.T.compactSpace_realUnitaryGroup_of_definite : (∀ (r : ℕ) (X : Data E r) (H : Subgroup (X.Ψ → GL (Fin r) ℂ)), (∀ g, g ∈ H ↔ X.IsUnitaryC fun τ => (g τ : Matrix (Fin r) (Fin r) ℂ)) → (X.p0 = 0 ∨ X.p0 = r) → CompactSpace H) := by
  first | exact @GlobalTheory.FinCovol.compactSpace_unitary_of_definite | exact GlobalTheory.FinCovol.compactSpace_unitary_of_definite | (intros; apply GlobalTheory.FinCovol.compactSpace_unitary_of_definite <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.ExistsBasisAdaptedMem
section
open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up MeasureTheory Topology
open scoped ComplexOrder ENNReal Matrix

namespace GlobalTheory.LatBasisAdapted

theorem span_range_smul_comp {K V ι κ : Type*} [Field K] [AddCommGroup V] [Module K V]
    (c : ι → K) (hc : ∀ i, c i ≠ 0) (w : ι → V) (f : κ → ι) :
    Submodule.span K (Set.range ((fun i => c i • w i) ∘ f)) =
      Submodule.span K (Set.range (w ∘ f)) := by
  apply le_antisymm
  · rw [Submodule.span_le]
    rintro _ ⟨k, rfl⟩
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨k, rfl⟩)
  · rw [Submodule.span_le]
    rintro _ ⟨k, rfl⟩
    have h : (w ∘ f) k = (c (f k))⁻¹ • ((fun i => c i • w i) ∘ f) k := by
      simp [smul_smul, inv_mul_cancel₀ (hc (f k))]
    rw [h]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨k, rfl⟩)

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

theorem exists_basis_adapted_mem : (∀ (r : ℕ) (X : Data E r) (W₁ W₂ : Submodule E (Fin r → E)), ∃ (a b c : ℕ) (w : Fin a ⊕ Fin b ⊕ Fin c → Fin r → E), LinearIndependent E w ∧ (∀ k, w k ∈ X.Λ) ∧ Submodule.span E (Set.range (w ∘ Sum.inl)) = W₁ ⊓ W₂ ∧ Submodule.span E (Set.range (w ∘ Sum.map id Sum.inl)) = W₁ ∧ Submodule.span E (Set.range (w ∘ Sum.map id Sum.inr)) = W₂ ∧ Submodule.span E (Set.range w) = W₁ ⊔ W₂) := by
  intro r X W₁ W₂
  obtain ⟨a, b, c, w, hw, h0, h1, h2, h3⟩ :=
    GlobalTheory.exists_basis_adapted_two_subspaces E (Fin r → E) W₁ W₂
  choose n hn hm using fun k => (GlobalTheory.LatDen.latDen r X).1 (w k)
  have hc : ∀ k, (n k : E) ≠ 0 := fun k => Nat.cast_ne_zero.2 (hn k).ne'
  refine ⟨a, b, c, fun k => (n k : E) • w k, ?_, hm, ?_, ?_, ?_, ?_⟩
  · exact hw.units_smul (fun k => Units.mk0 _ (hc k))
  · rw [span_range_smul_comp _ hc, h0]
  · rw [span_range_smul_comp _ hc, h1]
  · rw [span_range_smul_comp _ hc, h2]
  · exact (span_range_smul_comp _ hc w id).trans h3

end GlobalTheory.LatBasisAdapted
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.ExistsBasisMem
section
open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up MeasureTheory Topology
open scoped ComplexOrder ENNReal Matrix

namespace GlobalTheory.LatBasis

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

theorem exists_basis_mem : (∀ (r : ℕ) (X : Data E r) (W : Submodule E (Fin r → E)), ∃ w : Fin (Module.finrank E W) → Fin r → E, LinearIndependent E w ∧ (∀ a, w a ∈ X.Λ) ∧ Submodule.span E (Set.range w) = W) := by
  intro r X W
  choose n hn hmem using (GlobalTheory.LatDen.latDen r X).1
  set b := Module.finBasis E W
  set v : Fin (Module.finrank E W) → Fin r → E := fun i => (b i : Fin r → E) with hv
  have hvli : LinearIndependent E v := b.linearIndependent.map' W.subtype (Submodule.ker_subtype W)
  have hne : ∀ i, (n (v i) : E) ≠ 0 := fun i => Nat.cast_ne_zero.2 (hn (v i)).ne'
  set c : Fin (Module.finrank E W) → Eˣ := fun i => Units.mk0 _ (hne i)
  have hli : LinearIndependent E (fun i => (n (v i) : E) • v i) := hvli.units_smul c
  refine ⟨fun i => (n (v i) : E) • v i, hli, fun a => hmem (v a), ?_⟩
  have hle : Submodule.span E (Set.range fun i => (n (v i) : E) • v i) ≤ W := by
    rw [Submodule.span_le]
    rintro _ ⟨i, rfl⟩
    exact W.smul_mem _ (b i).2
  apply Submodule.eq_of_le_of_finrank_eq hle
  rw [finrank_span_eq_card hli, Fintype.card_fin]

end GlobalTheory.LatBasis
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.GramDetDivIndexEqOfSpanEq
section
open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up MeasureTheory Topology
open scoped ComplexOrder ENNReal Matrix

namespace GlobalTheory

variable {E : Type} [Field E] [NumberField E]

theorem exists_common_integral_refinement {V ι : Type} [AddCommGroup V] [Module E V]
    [Fintype ι] [DecidableEq ι] (w w' : ι → V) (hw' : LinearIndependent E w')
    (h : Submodule.span E (Set.range w) = Submodule.span E (Set.range w')) :
    ∃ A A' : Matrix ι ι (𝓞 E), A.det ≠ 0 ∧ A'.det ≠ 0 ∧
      (fun a => ∑ b, ((A b a : 𝓞 E) : E) • w b) = (fun a => ∑ b, ((A' b a : 𝓞 E) : E) • w' b) := by
  have h1 : ∀ a, ∃ c : ι → E, ∑ b, c b • w b = w' a := fun a =>
    (Submodule.mem_span_range_iff_exists_fun E).1
      (h ▸ Submodule.subset_span (Set.mem_range_self a))
  choose B hB using h1
  obtain ⟨c, hc⟩ := IsLocalization.exist_integer_multiples_of_finite (nonZeroDivisors (𝓞 E))
    (fun p : ι × ι => B p.1 p.2)
  have hc' : ∀ a b, ∃ y : 𝓞 E, (y : E) = ((c : 𝓞 E) : E) * B a b := by
    intro a b
    obtain ⟨y, hy⟩ := hc (a, b)
    refine ⟨y, ?_⟩
    have : (y : E) = algebraMap (𝓞 E) E y := rfl
    rw [this, hy, Algebra.smul_def]
  choose A hA using hc'
  have hc0 : (c : 𝓞 E) ≠ 0 := nonZeroDivisors.coe_ne_zero c
  have hcE : ((c : 𝓞 E) : E) ≠ 0 := by
    simp
  have key : ∀ a, ∑ b, ((A a b : 𝓞 E) : E) • w b = ((c : 𝓞 E) : E) • w' a := by
    intro a
    rw [← hB a, Finset.smul_sum]
    exact Finset.sum_congr rfl fun b _ => by rw [hA, mul_smul]
  refine ⟨Matrix.of fun b a => A a b, Matrix.diagonal fun _ => (c : 𝓞 E), ?_, ?_, ?_⟩
  · intro h0
    obtain ⟨v, hv0, hv⟩ := Matrix.exists_mulVec_eq_zero_iff.2 h0
    apply hv0
    have h2 : ∑ a, (((v a : 𝓞 E) : E) * ((c : 𝓞 E) : E)) • w' a = 0 := by
      have : ∀ a, (((v a : 𝓞 E) : E) * ((c : 𝓞 E) : E)) • w' a
          = ∑ b, (((A a b * v a : 𝓞 E)) : E) • w b := by
        intro a
        rw [mul_smul, ← key, Finset.smul_sum]
        refine Finset.sum_congr rfl fun b _ => ?_
        rw [← mul_smul, mul_comm]
        simp
      rw [Finset.sum_congr rfl fun a _ => this a, Finset.sum_comm]
      refine Finset.sum_eq_zero fun b _ => ?_
      rw [← Finset.sum_smul]
      have hb : ∑ a, A a b * v a = 0 := by
        have := congrFun hv b
        simpa [Matrix.mulVec, dotProduct] using this
      have hb' : ∑ a, (((A a b * v a : 𝓞 E)) : E) = 0 := by
        have := congrArg (algebraMap (𝓞 E) E) hb
        set_option synthInstance.maxHeartbeats 100000 in
          rw [map_sum, map_zero] at this
        exact this
      rw [hb', zero_smul]
    funext a
    have h3 := Fintype.linearIndependent_iff.1 hw' _ h2 a
    have h4 : ((v a : 𝓞 E) : E) = 0 := (mul_eq_zero.1 h3).resolve_right hcE
    simpa using h4
  · rw [Matrix.det_diagonal]
    exact Finset.prod_ne_zero_iff.2 fun _ _ => hc0
  · funext a
    simp only [Matrix.of_apply]
    rw [key, Finset.sum_eq_single a]
    · simp
    · intro b _ hb
      simp [Matrix.diagonal_apply_ne _ hb]
    · simp

theorem gram_div_index_eq_of_span_eq [IsCMField E] : (∀ (r : ℕ) (X : Data E r) (x : Frame X.Ψ r) (ι : Type) [Fintype ι] [DecidableEq ι] (w w' : ι → Fin r → E), LinearIndependent E w → (∀ a, w a ∈ X.Λ) → LinearIndependent E w' → (∀ a, w' a ∈ X.Λ) → Submodule.span E (Set.range w) = Submodule.span E (Set.range w') → ((∏ τ : X.Ψ, ((((mat x τ)⁻¹ * (Matrix.of fun k a => τ.1 (w a k)))ᴴ * ((mat x τ)⁻¹ * (Matrix.of fun k a => τ.1 (w a k)))).det.re)) / (((Submodule.span (𝓞 E) (Set.range w)).toAddSubgroup.relIndex (X.Λ.toAddSubgroup ⊓ (Submodule.span E (Set.range w)).toAddSubgroup)) : ℝ)) = ((∏ τ : X.Ψ, ((((mat x τ)⁻¹ * (Matrix.of fun k a => τ.1 (w' a k)))ᴴ * ((mat x τ)⁻¹ * (Matrix.of fun k a => τ.1 (w' a k)))).det.re)) / (((Submodule.span (𝓞 E) (Set.range w')).toAddSubgroup.relIndex (X.Λ.toAddSubgroup ⊓ (Submodule.span E (Set.range w')).toAddSubgroup)) : ℝ))) := by
  intro r X x ι _ _ w w' hw hΛ hw' hΛ' h
  obtain ⟨A, A', hA, hA', he⟩ := exists_common_integral_refinement w w' hw' h
  have h1 := GlobalTheory.ValMul.value_mul_eq r X x ι w hw hΛ A hA
  have h2 := GlobalTheory.ValMul.value_mul_eq r X x ι w' hw' hΛ' A' hA'
  rw [← h1, ← h2, he]

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.MajorantEqSumNormSqOrthonormalFrameStatement
section
open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up MeasureTheory Topology
open scoped ComplexOrder ENNReal Matrix
variable {E : Type} [Field E] [NumberField E] [IsCMField E]
theorem _root_.GlobalTheory.T.majorant_eq_sum_norm_sq_orthonormalFrame : (∀ (r : ℕ) (X : Data E r) (x : Frame X.Ψ r), IsOrth X x → (∀ τ : X.Ψ, (mat x τ).det ≠ 0) ∧ ∀ (τ : X.Ψ) (v : Fin r → ℂ), X.maj x τ v = ∑ a, ‖((mat x τ)⁻¹.mulVec v) a‖ ^ 2) := by
  first | exact @GlobalTheory.MajorantOrthFrame.maj_eq_sum_norm_sq_of_isOrth | exact GlobalTheory.MajorantOrthFrame.maj_eq_sum_norm_sq_of_isOrth | (intros; apply GlobalTheory.MajorantOrthFrame.maj_eq_sum_norm_sq_of_isOrth <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.RelIndexIntegralSpanSupermultiplicativeStatement
section
open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up MeasureTheory Topology
open scoped ComplexOrder ENNReal Matrix
variable {E : Type} [Field E] [NumberField E] [IsCMField E]
theorem _root_.GlobalTheory.T.relIndex_integralSpan_supermultiplicative : (∀ (r : ℕ) (X : Data E r) (α β γ : Type) [Fintype α] [Fintype β] [Fintype γ] [DecidableEq α] [DecidableEq β] [DecidableEq γ] (w : α ⊕ β ⊕ γ → Fin r → E), LinearIndependent E w → (∀ a, w a ∈ X.Λ) → ((Submodule.span (𝓞 E) (Set.range (w ∘ (Sum.map id Sum.inl : α ⊕ β → α ⊕ β ⊕ γ)))).toAddSubgroup.relIndex (X.Λ.toAddSubgroup ⊓ (Submodule.span E (Set.range (w ∘ (Sum.map id Sum.inl : α ⊕ β → α ⊕ β ⊕ γ)))).toAddSubgroup)) * ((Submodule.span (𝓞 E) (Set.range (w ∘ (Sum.map id Sum.inr : α ⊕ γ → α ⊕ β ⊕ γ)))).toAddSubgroup.relIndex (X.Λ.toAddSubgroup ⊓ (Submodule.span E (Set.range (w ∘ (Sum.map id Sum.inr : α ⊕ γ → α ⊕ β ⊕ γ)))).toAddSubgroup)) ≤ ((Submodule.span (𝓞 E) (Set.range (w ∘ (Sum.inl : α → α ⊕ β ⊕ γ)))).toAddSubgroup.relIndex (X.Λ.toAddSubgroup ⊓ (Submodule.span E (Set.range (w ∘ (Sum.inl : α → α ⊕ β ⊕ γ)))).toAddSubgroup)) * ((Submodule.span (𝓞 E) (Set.range w)).toAddSubgroup.relIndex (X.Λ.toAddSubgroup ⊓ (Submodule.span E (Set.range w)).toAddSubgroup))) := by
  first | exact @GlobalTheory.SpanIndex.relIndex_span_mul_le | exact GlobalTheory.SpanIndex.relIndex_span_mul_le | (intros; apply GlobalTheory.SpanIndex.relIndex_span_mul_le <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.RelIndexSpanLeNormMinor
section
open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up MeasureTheory Topology
open scoped ComplexOrder ENNReal Matrix
variable {E : Type} [Field E] [NumberField E] [IsCMField E]

namespace GlobalTheory

theorem relIndex_span_le_norm_minor :
    (∀ (r : ℕ) (X : Data E r), ∃ C : ℝ, 0 < C ∧ ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (w : ι → Fin r → E), LinearIndependent E w → (∀ a, w a ∈ X.Λ) → ∀ e : ι → Fin r, Function.Injective e → (Matrix.of fun k a => w a (e k)).det ≠ 0 → (((Submodule.span (𝓞 E) (Set.range w)).toAddSubgroup.relIndex (X.Λ.toAddSubgroup ⊓ (Submodule.span E (Set.range w)).toAddSubgroup)) : ℝ) ≤ C * ∏ τ : X.Ψ, ‖τ.1 (Matrix.of fun k a => w a (e k)).det‖ ^ 2) := by
  intro r X
  obtain ⟨n, hn, hint⟩ := (GlobalTheory.LatDen.latDen r X).2
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hn0 : (n : E) ≠ 0 := by exact_mod_cast hn.ne'
  refine ⟨∏ _τ : X.Ψ, ((n : ℝ) ^ r) ^ 2, Finset.prod_pos fun _ _ => by positivity, ?_⟩
  intro ι _ _ w _ hw e he hdet
  set M : Matrix ι ι E := Matrix.of fun k a => w a (e k) with hM
  set L : AddSubgroup (Fin r → E) :=
    X.Λ.toAddSubgroup ⊓ (Submodule.span E (Set.range w)).toAddSubgroup with hL
  let A : Matrix ι ι (𝓞 E) := Matrix.of fun k a => ⟨(n : E) * w a (e k), hint _ (hw a) _⟩
  have hA : (algebraMap (𝓞 E) E).mapMatrix A = (n : E) • M := by
    ext k a
    rfl
  have hdetA : ((A.det : 𝓞 E) : E) = (n : E) ^ Fintype.card ι * M.det := by
    rw [← Matrix.det_smul, ← hA, ← RingHom.map_det]
  have hA0 : A.det ≠ 0 := by
    intro h
    rw [h] at hdetA
    exact mul_ne_zero (pow_ne_zero _ hn0) hdet (hdetA.symm.trans rfl)
  let φ : L →+ (ι → 𝓞 E) :=
    { toFun := fun v k => ⟨(n : E) * v.1 (e k), hint _ v.2.1 _⟩
      map_zero' := by
        ext k
        exact mul_zero (n : E)
      map_add' := fun u v => by
        ext k
        exact mul_add (n : E) _ _ }
  set R := (LinearMap.range A.mulVecLin).toAddSubgroup with hR
  have hidx := index_range_mulVecLin_eq_abs_norm_det ι A hA0
  rw [← hR] at hidx
  have hR0 : R.index ≠ 0 := by
    intro h
    rw [h, Nat.cast_zero, eq_comm, abs_eq_zero, Algebra.norm_eq_zero_iff] at hidx
    exact hA0 (by exact_mod_cast hidx)
  have hle : R.comap φ ≤ (Submodule.span (𝓞 E) (Set.range w)).toAddSubgroup.addSubgroupOf L := by
    rintro ⟨v, hvΛ, hv⟩ ⟨c, hc⟩
    obtain ⟨b, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun E).1 hv
    have hb : M *ᵥ (fun a => (c a : E)) = M *ᵥ b := by
      funext k
      have h := congrArg (algebraMap (𝓞 E) E) (congrFun hc k)
      set_option synthInstance.maxHeartbeats 100000 in
        rw [Matrix.mulVecLin_apply, Matrix.mulVec, dotProduct, map_sum] at h
      apply mul_left_cancel₀ hn0
      have h2 : (algebraMap (𝓞 E) E) (φ ⟨∑ i, b i • w i, hvΛ, hv⟩ k) =
          (n : E) * (∑ i, b i • w i) (e k) := rfl
      rw [h2] at h
      have h3 : (M *ᵥ b) k = (∑ i, b i • w i) (e k) := by
        simp [Matrix.mulVec, dotProduct, hM, Finset.sum_apply, mul_comm]
      rw [h3, ← h, Matrix.mulVec, dotProduct, Finset.mul_sum]
      refine Finset.sum_congr rfl fun a _ => ?_
      rw [map_mul, ← mul_assoc]
      rfl
    have hcb := Matrix.mulVec_injective_of_det_ne_zero hdet hb
    change (∑ i, b i • w i) ∈ Submodule.span (𝓞 E) (Set.range w)
    rw [← hcb]
    refine Submodule.sum_mem _ fun a _ => ?_
    exact Submodule.smul_mem _ (c a) (Submodule.subset_span ⟨a, rfl⟩)
  have h1 : (R.comap φ).index ≤ R.index := by
    rw [AddSubgroup.index_comap, ← AddSubgroup.relIndex_top_right]
    exact AddSubgroup.relIndex_le_of_le_right le_top (by rwa [AddSubgroup.relIndex_top_right])
  have h0 : (R.comap φ).index ≠ 0 := by
    rw [AddSubgroup.index_comap]
    exact fun h => hR0 (AddSubgroup.index_eq_zero_of_relIndex_eq_zero h)
  have h2 : (Submodule.span (𝓞 E) (Set.range w)).toAddSubgroup.relIndex L ≤ R.index :=
    (Nat.le_of_dvd (Nat.pos_of_ne_zero h0) (AddSubgroup.index_dvd_of_le hle)).trans h1
  have h3 : (R.index : ℝ) = ∏ τ : X.Ψ, ‖τ.1 ((A.det : 𝓞 E) : E)‖ ^ 2 := by
    rw [← abs_norm_eq_prod_cmType_sq r X, ← hidx, Rat.cast_natCast]
  have hcard : Fintype.card ι ≤ r := by simpa using Fintype.card_le_of_injective e he
  refine (Nat.cast_le.2 h2).trans ?_
  rw [h3, ← Finset.prod_mul_distrib]
  refine Finset.prod_le_prod₀ (fun _ _ => by positivity) fun τ _ => ?_
  rw [hdetA, map_mul, map_pow, map_natCast, norm_mul, norm_pow, Complex.norm_natCast, mul_pow]
  gcongr

end GlobalTheory
end

