module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1055
public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1080
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0037
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0256
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1071
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0036
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.T2SpaceFiniteAdeleRing
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1065

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HaarIntegralNormalizedIntegralMatricesTwoSidedMu
section
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT GlobalTheory.BCT.CtLevel
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.BCT.HintInv

theorem rStab_comp_equiv {H : Type} [Group H] (φ : H ≃* H) (u : H → ℂ) :
    rStab (u ∘ φ) = (rStab u).comap (φ : H →* H) := by
  ext k
  simp only [Subgroup.mem_comap, MulEquiv.coe_toMonoidHom]
  show (∀ x, u (φ (x * k)) = u (φ x)) ↔ ∀ x, u (x * φ k) = u x
  constructor
  · intro h x
    have := h (φ.symm x)
    simpa using this
  · intro h x
    rw [map_mul]; exact h _

theorem hint_comp_equiv {H : Type} [Group H] (K : Subgroup H) (φ : H ≃* H) (hK : K.map (φ : H →* H) = K)
    (u : H → ℂ) : hint K (u ∘ φ) = hint K u := by
  set S := rStab u ⊓ K with hS
  have hS' : rStab (u ∘ φ) ⊓ K = S.comap (φ : H →* H) := by
    rw [rStab_comp_equiv, hS, Subgroup.comap_inf]
    congr 1
    have h1 : (K.map (φ : H →* H)).comap (φ : H →* H) = K :=
      Subgroup.comap_map_eq_self_of_injective φ.injective K
    rw [hK] at h1
    exact h1.symm
  unfold hint
  rw [hS', Subgroup.relIndex_comap, hK]
  congr 1
  let e : H ⧸ S.comap (φ : H →* H) ≃ H ⧸ S :=
    Quotient.congr φ.toEquiv (fun a b => by
      simp only [QuotientGroup.leftRel_apply, Subgroup.mem_comap, MulEquiv.coe_toMonoidHom, map_mul, map_inv]
      rfl)
  rw [← finsum_comp_equiv e]
  refine finsum_congr fun q => ?_
  obtain ⟨s, hs⟩ := QuotientGroup.mk_out_eq_mul S (φ q.out)
  have he : e q = ((φ q.out : H) : H ⧸ S) := by
    conv_lhs => rw [← QuotientGroup.out_eq' q]
    rfl
  rw [he, hs]
  exact ((Subgroup.mem_inf.1 s.2).1 _).symm

section Integral

variable {L : Type} [Field L] {a b : ℕ}

theorem entries_of_mem_GLint {O : Subring L} {A : GL (Fin a) L} (hA : A ∈ GLint (Fin a) O) (i j : Fin a) :
    A.val i j ∈ O ∧ (A⁻¹).val i j ∈ O := by
  obtain ⟨y, rfl⟩ := hA
  rw [← map_inv]
  exact ⟨(y.val i j).2, ((y⁻¹).val i j).2⟩

theorem mul_mul_mem {O : Subring L} {P : Matrix (Fin a) (Fin a) L} {X : Matrix (Fin a) (Fin b) L}
    {Q : Matrix (Fin b) (Fin b) L} (hP : ∀ i j, P i j ∈ O) (hX : ∀ i j, X i j ∈ O) (hQ : ∀ i j, Q i j ∈ O)
    (i : Fin a) (j : Fin b) : (P * X * Q) i j ∈ O := by
  rw [Matrix.mul_apply]
  refine Subring.sum_mem _ fun l _ => Subring.mul_mem _ ?_ (hQ l j)
  rw [Matrix.mul_apply]
  exact Subring.sum_mem _ fun k _ => Subring.mul_mem _ (hP i k) (hX k l)

def lrEquiv (A : GL (Fin a) L) (B : GL (Fin b) L) : Matrix (Fin a) (Fin b) L ≃+ Matrix (Fin a) (Fin b) L where
  toFun X := A.val * X * B.val
  invFun X := (A⁻¹).val * X * (B⁻¹).val
  left_inv X := by
    simp only [Matrix.mul_assoc]
    rw [← Matrix.mul_assoc A.val X, ← Matrix.mul_assoc (A⁻¹).val, ← Matrix.mul_assoc (A⁻¹).val]
    rw [Units.inv_mul, Matrix.one_mul, Units.mul_inv, Matrix.mul_one]
  right_inv X := by
    simp only [Matrix.mul_assoc]
    rw [← Matrix.mul_assoc (A⁻¹).val X, ← Matrix.mul_assoc A.val, ← Matrix.mul_assoc A.val]
    rw [Units.mul_inv, Matrix.one_mul, Units.inv_mul, Matrix.mul_one]
  map_add' X Y := by simp only [Matrix.mul_add, Matrix.add_mul]

end Integral

theorem map_intMat {E : Type} [Field E] [NumberField E] [IsCMField E] (a b : ℕ) (w : Pl E) (A : GLw a w) (B : GLw b w)
    (hA : A ∈ GlobalTheory.LFun.KGL w (n := a)) (hB : B ∈ GlobalTheory.LFun.KGL w (n := b)) :
    (intMat a b w).map ((lrEquiv A B).toMultiplicative : _ →* _) = intMat a b w := by
  have hint' : ∀ X : Matrix (Fin a) (Fin b) (w.adicCompletion E),
      (∀ i j, Valued.v (X i j) ≤ 1) ↔ ∀ i j, X i j ∈ Ov E w := fun X =>
    forall_congr' fun i => forall_congr' fun j => (HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).symm
  have hA1 := fun i j => (entries_of_mem_GLint hA i j).1
  have hA2 := fun i j => (entries_of_mem_GLint hA i j).2
  have hB1 := fun i j => (entries_of_mem_GLint hB i j).1
  have hB2 := fun i j => (entries_of_mem_GLint hB i j).2
  have key : ∀ (P : GLw a w) (Q : GLw b w), (∀ i j, P.val i j ∈ Ov E w) → (∀ i j, Q.val i j ∈ Ov E w) →
      (intMat a b w).map ((lrEquiv P Q).toMultiplicative : _ →* _) ≤ intMat a b w := by
    intro P Q hP hQ
    rw [intMat, MonoidHom.map_closure, Subgroup.closure_le]
    rintro _ ⟨X, hX, rfl⟩
    refine Subgroup.subset_closure ?_
    show ∀ i j, Valued.v ((P.val * Multiplicative.toAdd X * Q.val) i j) ≤ 1
    rw [hint']
    exact mul_mul_mem hP ((hint' _).1 hX) hQ
  refine le_antisymm (key A B hA1 hB1) ?_
  have h2 := key A⁻¹ B⁻¹ hA2 hB2
  intro X hX
  refine ⟨(lrEquiv A⁻¹ B⁻¹).toMultiplicative X, h2 ⟨X, hX, rfl⟩, ?_⟩
  show Multiplicative.ofAdd (A.val * ((A⁻¹).val * Multiplicative.toAdd X * (B⁻¹).val) * B.val) = X
  rw [show A.val * ((A⁻¹).val * Multiplicative.toAdd X * (B⁻¹).val) * B.val = Multiplicative.toAdd X from
    (lrEquiv A B).right_inv _]
  rfl

theorem hint_intMat_mul_mul :
    ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (a b : ℕ) (w : Pl E)
    (u : Multiplicative (Matrix (Fin a) (Fin b) (w.adicCompletion E)) → ℂ) (A : GLw a w) (B : GLw b w),
    A ∈ GlobalTheory.LFun.KGL w (n := a) → B ∈ GlobalTheory.LFun.KGL w (n := b) →
    hint (intMat a b w) (fun X => u (Multiplicative.ofAdd (A.val * Multiplicative.toAdd X * B.val))) =
      hint (intMat a b w) u := by
  intro E _ _ _ a b w u A B hA hB
  exact hint_comp_equiv (intMat a b w) (lrEquiv A B).toMultiplicative (map_intMat a b w A B hA hB) u

end GlobalTheory.BCT.HintInv
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HaarIntegralNormalizedOpenCompactEqIntegralDiv
section
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section
namespace GlobalTheory.HaarSum
open MeasureTheory

theorem vol_mul_relIndex {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [MeasurableSpace G]
    [BorelSpace G] (μ : Measure G) [μ.IsMulLeftInvariant] (H H' : Subgroup G) (hle : H' ≤ H)
    (hc : IsCompact (H : Set G)) (ho : IsOpen (H' : Set G)) :
    μ.real H' * (H'.relIndex H : ℝ) = μ.real H ∧ H'.relIndex H ≠ 0 := by
  haveI : CompactSpace H := isCompact_iff_compactSpace.1 hc
  have hHo : IsOpen (H : Set G) := Subgroup.isOpen_mono hle ho
  have ho' : IsOpen ((H'.subgroupOf H : Subgroup H) : Set H) := ho.preimage continuous_subtype_val
  haveI : Finite (H ⧸ H'.subgroupOf H) := (H'.subgroupOf H).quotient_finite_of_isOpen ho'
  haveI : (H'.subgroupOf H).FiniteIndex := Subgroup.finiteIndex_of_finite_quotient
  have hemb : MeasurableEmbedding (H.subtype : H → G) := MeasurableEmbedding.subtype_coe hHo.measurableSet
  have : (μ.comap (H.subtype : H → G)).IsMulLeftInvariant := Measure.IsMulLeftInvariant.comap μ hemb
  have key := (H'.subgroupOf H).index_mul_measure ho'.measurableSet (μ.comap (H.subtype : H → G))
  rw [hemb.comap_apply, hemb.comap_apply] at key
  have e1 : (H.subtype : H → G) '' Set.univ = (H : Set G) := by ext x; simp
  have e2 : (H.subtype : H → G) '' ((H'.subgroupOf H : Subgroup H) : Set H) = (H' : Set G) := by
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact hy
    · intro hx
      exact ⟨⟨x, hle hx⟩, hx, rfl⟩
  rw [e1, e2] at key
  refine ⟨?_, Subgroup.FiniteIndex.index_ne_zero⟩
  rw [Subgroup.relIndex, Measure.real, Measure.real, ← key, ENNReal.toReal_mul, mul_comm]
  simp

theorem integral_eq_sum_cosets {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [MeasurableSpace G]
    [BorelSpace G] (μ : Measure G) [μ.IsMulLeftInvariant] (S : Subgroup G) (hS : IsOpen (S : Set G))
    (hfin : μ (S : Set G) ≠ ⊤) (u : G → ℂ) (hu : ∀ x, ∀ s ∈ S, u (x * s) = u x) (F : Finset (G ⧸ S))
    (hF : ∀ q : G ⧸ S, q ∉ F → u q.out = 0) :
    ∫ x, u x ∂μ = (μ.real (S : Set G) : ℂ) * ∑ q ∈ F, u q.out := by
  have key : ∀ x : G, u ((x : G ⧸ S).out) = u x := fun x => by
    obtain ⟨h, hh⟩ := QuotientGroup.mk_out_eq_mul S x
    rw [hh]
    exact hu x h h.2
  have hset : ∀ q : G ⧸ S, {x : G | (x : G ⧸ S) = q} = (fun x => q.out⁻¹ * x) ⁻¹' (S : Set G) := by
    intro q
    ext x
    simp only [Set.mem_setOf_eq, Set.mem_preimage, SetLike.mem_coe]
    conv_lhs => rw [← QuotientGroup.out_eq' q]
    rw [eq_comm]
    exact QuotientGroup.eq
  have hmeas : ∀ q : G ⧸ S, MeasurableSet {x : G | (x : G ⧸ S) = q} := fun q => by
    rw [hset]
    exact (hS.preimage (continuous_const_mul _)).measurableSet
  have hμ : ∀ q : G ⧸ S, μ {x : G | (x : G ⧸ S) = q} = μ (S : Set G) := fun q => by
    rw [hset]
    exact measure_preimage_mul μ _ _
  have hfun : u = fun x => ∑ q ∈ F, ({x : G | (x : G ⧸ S) = q}.indicator (fun _ => u q.out) x) := by
    funext x
    rw [Finset.sum_eq_single (x : G ⧸ S)]
    · simp [Set.indicator, key]
    · intro q _ hq
      simp [Set.indicator, Ne.symm hq]
    · intro hx
      have h0 := hF _ hx
      rw [key] at h0
      simp [Set.indicator, key, h0]
  conv_lhs => rw [hfun]
  rw [integral_finsetSum]
  · rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun q _ => ?_
    rw [integral_indicator_const _ (hmeas q), Measure.real, hμ q, Complex.real_smul, Measure.real]
  · intro q _
    exact (integrableOn_const (hμ q ▸ hfin)).integrable_indicator (hmeas q)

theorem finite_cosets {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] (S : Subgroup G)
    (hS : IsOpen (S : Set G)) {C : Set G} (hC : IsCompact C) : ((fun x : G => (x : G ⧸ S)) '' C).Finite := by
  haveI : DiscreteTopology (G ⧸ S) := QuotientGroup.discreteTopology hS
  exact (hC.image (continuous_coinduced_rng : Continuous fun x : G => (x : G ⧸ S))).finite_of_discrete

theorem hint_eq_integral : ∀ (V : Type) [AddCommGroup V] [TopologicalSpace V] [IsTopologicalAddGroup V]
    (μ : @MeasureTheory.Measure V (borel V)), @MeasureTheory.Measure.IsAddHaarMeasure V _ _ (borel V) μ →
    ∀ (Λ : AddSubgroup V), IsOpen (Λ : Set V) → IsCompact (Λ : Set V) → ∀ u : V → ℂ,
    (∃ U : AddSubgroup V, IsOpen (U : Set V) ∧ ∀ x, ∀ y ∈ U, u (x + y) = u x) → HasCompactSupport u →
    GlobalTheory.BCT.hint (AddSubgroup.toSubgroup Λ) (fun X : Multiplicative V => u (Multiplicative.toAdd X)) =
      ((μ (Λ : Set V)).toReal : ℂ)⁻¹ * ∫ x, u x ∂μ := by
  intro V _ _ _ μ hμ Λ hΛo hΛc u ⟨U, hUo, hU⟩ hsupp
  letI : MeasurableSpace V := borel V
  haveI : BorelSpace V := ⟨rfl⟩
  haveI := hμ
  let G := Multiplicative V
  letI : MeasurableSpace G := borel V
  haveI : BorelSpace G := ⟨rfl⟩
  let ν : Measure G := μ
  haveI : ν.IsMulLeftInvariant := ⟨fun g => Measure.IsAddLeftInvariant.map_add_left_eq_self (μ := μ) (Multiplicative.toAdd g)⟩
  let u' : G → ℂ := fun X => u (Multiplicative.toAdd X)
  let K : Subgroup G := AddSubgroup.toSubgroup Λ
  let S : Subgroup G := rStab u' ⊓ K
  have hSK : S ≤ K := inf_le_right
  have hSo : IsOpen (S : Set G) := by
    refine Subgroup.isOpen_mono (H₁ := AddSubgroup.toSubgroup (U ⊓ Λ)) ?_ ?_
    · intro x hx
      refine ⟨fun y => hU _ _ hx.1, hx.2⟩
    · exact hUo.inter hΛo
  have hKc : IsCompact (K : Set G) := hΛc
  obtain ⟨hvol, hidx⟩ := vol_mul_relIndex ν K S hSK hKc hSo
  have hKpos : 0 < μ (Λ : Set V) := hΛo.measure_pos μ ⟨0, Λ.zero_mem⟩
  have hKfin : μ (Λ : Set V) < ⊤ := hΛc.measure_lt_top
  have hSfin : ν (S : Set G) ≠ ⊤ := ne_top_of_le_ne_top hKfin.ne (measure_mono hSK)
  have hfinC := finite_cosets S hSo (C := tsupport u') hsupp
  have hF : ∀ q : G ⧸ S, q ∉ hfinC.toFinset → u' q.out = 0 := by
    intro q hq
    by_contra h
    apply hq
    rw [Set.Finite.mem_toFinset]
    exact ⟨q.out, subset_tsupport _ h, QuotientGroup.out_eq' q⟩
  have hint_eq := integral_eq_sum_cosets ν S hSo hSfin u' (fun x s hs => hs.1 x) hfinC.toFinset hF
  have hsum : ∑ᶠ q : G ⧸ S, u' q.out = ∑ q ∈ hfinC.toFinset, u' q.out := by
    refine finsum_eq_sum_of_support_subset _ fun q hq => ?_
    by_contra h
    exact hq (hF q h)
  have hKr : (μ (Λ : Set V)).toReal = ν.real (S : Set G) * (S.relIndex K : ℝ) := hvol.symm
  have hKne : (μ (Λ : Set V)).toReal ≠ 0 := ENNReal.toReal_ne_zero.2 ⟨hKpos.ne', hKfin.ne⟩
  have hSne : ν.real (S : Set G) ≠ 0 := by
    intro h0
    rw [hKr, h0, zero_mul] at hKne
    exact hKne rfl
  change (((S.relIndex K : ℕ) : ℂ))⁻¹ * ∑ᶠ q : G ⧸ S, u' q.out = _ * ∫ x : G, u' x ∂ν
  rw [hint_eq, hsum, hKr]
  have hidx' : ((S.relIndex K : ℕ) : ℂ) ≠ 0 := Nat.cast_ne_zero.2 hidx
  have hSne' : ((ν.real (S : Set G) : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 hSne
  push_cast
  field_simp

end GlobalTheory.HaarSum
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HasCompactSupportTwistedConstantTermSplitPlace
section
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT GlobalTheory.BCT.CtLevel
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.BCT.CtLevel

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

theorem exists_ne_zero_of_hint_ne_zero {H : Type} [Group H] (K : Subgroup H) (u : H → ℂ) (hu : hint K u ≠ 0) :
    ∃ x, u x ≠ 0 := by
  by_contra hc
  push_neg at hc
  exact hu (by simp [hint, hc])

theorem exists_ne_zero_of_avg_ne_zero {H : Type} [Group H] (u : H → ℂ) (hu : avg u ≠ 0) : ∃ x, u x ≠ 0 := by
  by_contra hc
  push_neg at hc
  exact hu (by simp [avg, hc])

theorem blk_inv {n a b : ℕ} (h : a + b = n) (w : Pl E) (m : GLw a w × GLw b w)
    (X : Matrix (Fin a) (Fin b) (w.adicCompletion E)) :
    (blk h w m X)⁻¹ = blk h w m⁻¹ (-(m.1.val * X * (m.2⁻¹).val)) := by
  refine inv_eq_of_mul_eq_one_right (Units.ext ?_)
  rw [Units.val_mul, blk_val, blk_val, Units.val_one, reindex_apply, reindex_apply, submatrix_mul_equiv,
    fromBlocks_multiply]
  have e1 : m.1.val * (m.1⁻¹).val = 1 := Units.mul_inv _
  have e2 : m.2.val * (m.2⁻¹).val = 1 := Units.mul_inv _
  simp only [Prod.fst_inv, Prod.snd_inv, Matrix.mul_zero, add_zero, Matrix.zero_mul, zero_add]
  rw [e1, e2, ← Matrix.mul_assoc, e1, Matrix.one_mul, Matrix.mul_assoc m.1.val, add_comm]
  simp [fromBlocks_one]
  exact submatrix_one_equiv (blkEq h).symm

end GlobalTheory.BCT.CtLevel

open scoped Pointwise

namespace GlobalTheory.BCT.CtLevel

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

def blkTL {R : Type} {a b n : ℕ} (h : a + b = n) (g : Matrix (Fin n) (Fin n) R) : Matrix (Fin a) (Fin a) R :=
  (reindex (blkEq h).symm (blkEq h).symm g).toBlocks₁₁

def blkBR {R : Type} {a b n : ℕ} (h : a + b = n) (g : Matrix (Fin n) (Fin n) R) : Matrix (Fin b) (Fin b) R :=
  (reindex (blkEq h).symm (blkEq h).symm g).toBlocks₂₂

theorem blkTL_blk {n a b : ℕ} (h : a + b = n) (w : Pl E) (m : GLw a w × GLw b w)
    (X : Matrix (Fin a) (Fin b) (w.adicCompletion E)) : blkTL h (blk h w m X).val = m.1.val := by
  rw [blkTL, blk_val, ← reindex_symm, Equiv.symm_apply_apply, toBlocks_fromBlocks₁₁]

theorem blkBR_blk {n a b : ℕ} (h : a + b = n) (w : Pl E) (m : GLw a w × GLw b w)
    (X : Matrix (Fin a) (Fin b) (w.adicCompletion E)) : blkBR h (blk h w m X).val = m.2.val := by
  rw [blkBR, blk_val, ← reindex_symm, Equiv.symm_apply_apply, toBlocks_fromBlocks₂₂]

theorem continuous_blkTL {R : Type} [TopologicalSpace R] {a b n : ℕ} (h : a + b = n) :
    Continuous (blkTL (R := R) h) := by
  refine continuous_pi fun i => continuous_pi fun j => ?_
  simp only [blkTL, toBlocks₁₁, reindex_apply, submatrix_apply, of_apply]
  exact (continuous_apply _).comp (continuous_apply _)

theorem continuous_blkBR {R : Type} [TopologicalSpace R] {a b n : ℕ} (h : a + b = n) :
    Continuous (blkBR (R := R) h) := by
  refine continuous_pi fun i => continuous_pi fun j => ?_
  simp only [blkBR, toBlocks₂₂, reindex_apply, submatrix_apply, of_apply]
  exact (continuous_apply _).comp (continuous_apply _)

theorem hasCompactSupport_ctMu_split : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (a b n : ℕ) (h : a + b = n) (w : Pl E)
    (μ : (w.adicCompletion E)ˣ →* ℂˣ) (f : UL n w → ℂ), IsSplitAt w → HasCompactSupport f →
    HasCompactSupport (ctMu h w μ f) := by
  intro E _ _ _ a b n h w μ f hw hf
  have hUL : ∀ y : GLw n w, y ∈ UL n w := fun y => by rw [UL, if_pos hw]; trivial
  set S : Set (GLw n w) := Subtype.val '' tsupport f with hSdef
  have hS : IsCompact S := hf.image continuous_subtype_val
  have hK := (GlobalTheory.LFun.SatCompare.isOpen_isCompact_KGL w n).2
  set C : Set (GLw n w) := (GlobalTheory.LFun.KGL w (n := n) : Set (GLw n w)) * S * (GlobalTheory.LFun.KGL w (n := n) : Set (GLw n w)) with hCdef
  have hC : IsCompact C := (hK.mul hS).mul hK
  have hmem : ∀ m, ctMu h w μ f m ≠ 0 → ∃ X, blk h w m X ∈ C := by
    intro m hm
    have h1 := right_ne_zero_of_mul (right_ne_zero_of_mul hm)
    obtain ⟨X, hX⟩ := exists_ne_zero_of_hint_ne_zero _ _ h1
    obtain ⟨k, hk⟩ := exists_ne_zero_of_avg_ne_zero _ hX
    refine ⟨Multiplicative.toAdd X, ?_⟩
    set y := (k : GLw n w)⁻¹ * blk h w m (Multiplicative.toAdd X) * k with hy
    have hyS : y ∈ S := by
      refine ⟨⟨y, hUL y⟩, subset_tsupport _ ?_, rfl⟩
      have : toSub (UL n w) y = ⟨y, hUL y⟩ := by rw [toSub, dite_eq_left (hUL y)]
      simpa [this] using hk
    have e : blk h w m (Multiplicative.toAdd X) = (k : GLw n w) * y * (k : GLw n w)⁻¹ := by
      rw [hy]; group
    rw [e]
    exact Set.mul_mem_mul (Set.mul_mem_mul k.2 hyS) (inv_mem k.2)
  let ψ : GLw n w → ((Matrix (Fin a) (Fin a) (w.adicCompletion E) × (Matrix (Fin a) (Fin a) (w.adicCompletion E))ᵐᵒᵖ) ×
      (Matrix (Fin b) (Fin b) (w.adicCompletion E) × (Matrix (Fin b) (Fin b) (w.adicCompletion E))ᵐᵒᵖ)) :=
    fun g => ((blkTL h g.val, MulOpposite.op (blkTL h (g⁻¹).val)), (blkBR h g.val, MulOpposite.op (blkBR h (g⁻¹).val)))
  have hψ : Continuous ψ := by
    refine ((((continuous_blkTL h).comp Units.continuous_val).prodMk
      (MulOpposite.continuous_op.comp ((continuous_blkTL h).comp Units.continuous_coe_inv))).prodMk
      (((continuous_blkBR h).comp Units.continuous_val).prodMk
      (MulOpposite.continuous_op.comp ((continuous_blkBR h).comp Units.continuous_coe_inv))))
  let ι : GLw a w × GLw b w → _ := Prod.map (Units.embedProduct (Matrix (Fin a) (Fin a) (w.adicCompletion E)))
    (Units.embedProduct (Matrix (Fin b) (Fin b) (w.adicCompletion E)))
  have hι : Topology.IsClosedEmbedding ι :=
    Units.isClosedEmbedding_embedProduct.prodMap Units.isClosedEmbedding_embedProduct
  have hιψ : ∀ m X, ι m = ψ (blk h w m X) := by
    intro m X
    simp only [ι, ψ, Prod.map, Units.embedProduct_apply, blk_inv, blkTL_blk, blkBR_blk, Prod.fst_inv, Prod.snd_inv]
  have hT : IsCompact (ψ '' C) := hC.image hψ
  refine HasCompactSupport.intro' (hι.isCompact_preimage hT) (hT.isClosed.preimage hι.continuous) ?_
  intro m hm
  by_contra hne
  obtain ⟨X, hX⟩ := hmem m hne
  exact hm ⟨blk h w m X, hX, (hιψ m X).symm⟩

end GlobalTheory.BCT.CtLevel
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HasTopFormChartIntegralCongrOn
section
set_option autoImplicit false

noncomputable section

open MeasureTheory Filter Topology GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.ChartGlue GlobalTheory.FlagBundle GlobalTheory.HermFrame GlobalTheory.GoodMetric GlobalTheory.GoodTop
open ReciprocityTheory.L2DbarEstimates (V)
open scoped ContDiff Matrix ENNReal

namespace GlobalTheory.GoodTop

theorem hasInt_congr_on : ∀ {n : ℕ} {Y κ : Type} [TopologicalSpace Y] [MeasurableSpace Y] [BorelSpace Y]
    (e : κ → OpenPartialHomeomorph Y (V n)) {S : Set Y}, MeasurableSet S → ∀ {d d' : κ → Y → ℝ} {t : ℝ},
    (∀ i y, y ∈ S → y ∈ (e i).source → d i y = d' i y) → HasInt e d S t → HasInt e d' S t := by
  intro n Y κ _ _ _ e S hS d d' t h hd
  have key : ∀ ε : ℤˣ, glueMeas e (fun i y => ENNReal.ofReal ((ε : ℤ) * d' i y)) S =
      glueMeas e (fun i y => ENNReal.ofReal ((ε : ℤ) * d i y)) S := by
    intro ε
    have hm := GlobalTheory.ChernScale.glueMeas_restrict_eq e
      (ρ := fun i y => ENNReal.ofReal ((ε : ℤ) * d' i y)) (ρ' := fun i y => ENNReal.ofReal ((ε : ℤ) * d i y))
      (c := 1) ENNReal.one_ne_top hS (fun i y hy hyS => by rw [one_mul, h i y hyS hy])
    have := congrArg (fun μ : Measure Y => μ S) hm
    simpa only [one_smul, Measure.restrict_apply_self] using this
  refine ⟨fun ε => by rw [key ε]; exact hd.1 ε, ?_⟩
  rw [← hd.2, measureReal_def, measureReal_def, measureReal_def, measureReal_def, key 1, key (-1)]

end GlobalTheory.GoodTop
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HasTopFormChartIntegralZero
section
set_option autoImplicit false

open MeasureTheory Filter Topology GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.ChartGlue GlobalTheory.FlagBundle GlobalTheory.HermFrame GlobalTheory.GoodMetric GlobalTheory.GoodTop
open ReciprocityTheory.L2DbarEstimates (V)
open scoped ContDiff Matrix

namespace GlobalTheory.GoodTop

theorem glueMeas_zero_dens {n : ℕ} {Y κ : Type} [TopologicalSpace Y] [MeasurableSpace Y]
    (e : κ → OpenPartialHomeomorph Y (V n)) : glueMeas e (fun _ _ => 0) = 0 := by
  have h : ∀ i, chartMeas (e i) (fun _ => 0) = 0 := by
    intro i
    unfold chartMeas
    have : ((fun _ : Y => (0 : ENNReal)) ∘ (e i).symm) = 0 := rfl
    rw [this, withDensity_zero, Measure.map_zero]
  unfold glueMeas
  simp only [h]
  exact le_antisymm (iSup_le fun _ => le_rfl) (Measure.zero_le _)

theorem hasInt_zero {n : ℕ} {Y κ : Type} [TopologicalSpace Y] [MeasurableSpace Y]
    (e : κ → OpenPartialHomeomorph Y (V n)) (S : Set Y) : HasInt e (fun _ _ => 0) S 0 := by
  unfold HasInt
  simp only [mul_zero, ENNReal.ofReal_zero, glueMeas_zero_dens]
  simp

end GlobalTheory.GoodTop
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegralConjEtaleMemCentralizerMulIntegralGLStatement
section
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.integral_conj_etale_mem_centralizer_mul_integralGL : ∀ (E : Type) [Field E] [NumberField E] (n : ℕ) (w : HeightOneSpectrum (𝓞 E))
    (N g : GL (Fin n) (w.adicCompletion E)), N ∈ GlobalTheory.LFun.KGL w (n := n) →
    (∃ u v : (w.adicCompletion E)[X], (∀ i, u.coeff i ∈ w.adicCompletionIntegers E) ∧
      (∀ i, v.coeff i ∈ w.adicCompletionIntegers E) ∧ u * N.val.charpoly + v * derivative N.val.charpoly = 1) →
    g⁻¹ * N * g ∈ GlobalTheory.LFun.KGL w (n := n) → ∃ t : GL (Fin n) (w.adicCompletion E), t * N = N * t ∧ ∃ k ∈ GlobalTheory.LFun.KGL w (n := n), g = t * k := by
  first | exact @GlobalTheory.SplitUniq.splitUniq | exact GlobalTheory.SplitUniq.splitUniq | (intros; apply GlobalTheory.SplitUniq.splitUniq <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsSplitAtIffCPlNeAndCPlCPl
section
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.EulerTw

theorem isSplitAt_iff_cPl_ne_and_cPl_cPl :
    ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (w : Pl E),
      (IsSplitAt w ↔ GlobalTheory.EulerTw.cPl E w ≠ w) ∧ GlobalTheory.EulerTw.cPl E (GlobalTheory.EulerTw.cPl E w) = w := by
  intro E _ _ _ w
  refine ⟨⟨fun h => (GlobalTheory.SplitPts.over_split h).1, fun h => ?_⟩, GlobalTheory.SplitPts.conjSrc_conjSrc_cm w⟩
  by_contra hs
  exact h (GlobalTheory.LocInj.conjSrc_eq_of_not_split hs)

end GlobalTheory.EulerTw
end

