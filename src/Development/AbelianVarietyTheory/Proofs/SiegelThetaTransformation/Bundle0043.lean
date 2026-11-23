module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.Bundle0042
public import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.Bundle0002
public import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0030
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.ThetaLetterEquivConjugate
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.Bundle0008
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.PointwiseNormCanonicalThetaEqSqThetaConstant
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.Bundle0010
public import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.TensorLatticeSelfDualSemicharacterIndex
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0011
public import Formalism.SharpRestriction.Divisibility.GeneratorPowers.Bundle0007
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.HolomorphicFamilies.AnChartAsm
public import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.IsSystem
public import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.KernInvariantSymmPos
public import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.RealPlaceKernelHolomorphicWeightRowHighest
public import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.ExtendByZeroAntitoneOffBreak
public import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.MeasurePreservingMulLeft
public import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.Bundle0024

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.DoubledGaussianKernelDiagonalTranslationInvarianStatement
section
open Matrix Complex NumberField MeasureTheory GlobalTheory GlobalTheory.ThFr GlobalTheory.Ker ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD
open GlobalTheory.SW hiding Level
open GlobalTheory.Dict (hx pv)
open ReciprocityTheory.ChartRestriction.G.I2 (polyDeriv)
open scoped ComplexConjugate ComplexOrder Real Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.doubledGaussianKernel_diagonal_translation_invariant : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (X : Data E r) (g q0 : ℕ) (hr : X.p0 + q0 = r) (bas : (Fin g ⊕ Fin g → ℤ) ≃ₗ[ℤ] X.Λ) (idx : Fin g ≃ X.Ψ × Fin r) (n : ℕ), IsSympl X bas → Even n → ∀ x₁ ∈ X.dom, ∀ x₂ ∈ X.dom, ∀ a b w : WR X n, cexp (π * I * (EFR X w (a - b) : ℝ)) * (gaussR X bas idx x₁ (zR X idx x₁ (w + a)) * conj (gaussR X bas idx x₂ (zR X idx x₂ (w + b))) * kZero X idx x₁ x₂ (zR X idx x₁ (w + a)) (fun k i => conj (zR X idx x₂ (w + b) k i))) = gaussR X bas idx x₁ (zR X idx x₁ a) * conj (gaussR X bas idx x₂ (zR X idx x₂ b)) * kZero X idx x₁ x₂ (zR X idx x₁ a) (fun k i => conj (zR X idx x₂ b k i)) := by
  first | exact @GlobalTheory.Ker.Diag.kernel_diag | exact GlobalTheory.Ker.Diag.kernel_diag | (intros; apply GlobalTheory.Ker.Diag.kernel_diag <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.ExistsLetterRowWeightDictionary
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField Matrix Complex
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding Level
open GlobalTheory.SW hiding Level
open Formalism.L2.Pj Formalism.L2.PjFree
open scoped ComplexConjugate Classical
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Dict

namespace GlobalTheory.Dict.Letters

theorem rename_place_mem {R : Type} [CommRing R] {T T' κ : Type} [Fintype κ] {p q : ℕ} (f : T ≃ T')
    {c : T → Fin p → ℕ} {c' : T → Fin q → ℕ} {d : T' → Fin p → ℕ} {d' : T' → Fin q → ℕ}
    (h : ∀ t, d (f t) = c t) (h' : ∀ t, d' (f t) = c' t) {P : Harm.Poly R T p q κ}
    (hP : P ∈ Harm.rowHighest R c c') :
    MvPolynomial.rename (f.prodCongr (Equiv.refl ((Fin p ⊕ Fin q) × κ))) P ∈ Harm.rowHighest R d d' := by
  obtain ⟨h₁, h₂, h₃⟩ := Harm.mem_rowHighest_iff_rowAdd.1 hP
  set F := f.prodCongr (Equiv.refl ((Fin p ⊕ Fin q) × κ)) with hF
  have hFa (t : T) (v : (Fin p ⊕ Fin q) × κ) : F (t, v) = (f t, v) := rfl
  refine Harm.mem_rowHighest_iff_rowAdd.2 ⟨fun t a b => ?_, fun t ρ => ?_, fun t ρ ρ' hρ s => ?_⟩ <;>
    obtain ⟨t, rfl⟩ := f.surjective t
  · have := congrArg (MvPolynomial.rename F) (h₁ t a b)
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_zero, Harm.laplacian_apply, map_sum] at this
    rw [Harm.laplacian_apply, ← this]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [Harm.xVar, Harm.yVar, ← hFa, ← hFa, MvPolynomial.pderiv_rename F.injective,
      MvPolynomial.pderiv_rename F.injective]
  · rw [Harm.isWeightedHomogeneous_rename_iff F.injective, h, h']
    convert h₂ t ρ using 1
    funext ⟨t', ρ', k⟩
    simp [hFa, Harm.rowInd_apply]
  · conv_rhs => rw [← h₃ t ρ ρ' hρ s]
    refine DFunLike.congr_fun (?_ : (Harm.rowAdd (f t) ρ ρ' (s : R)).comp (MvPolynomial.rename F) =
      (MvPolynomial.rename F).comp (Harm.rowAdd t ρ ρ' (s : R))) P
    refine MvPolynomial.algHom_ext fun ⟨t', ρ'', k⟩ => ?_
    rw [AlgHom.comp_apply, AlgHom.comp_apply, MvPolynomial.rename_X, hFa, Harm.rowAdd_X, Harm.rowAdd_X]
    simp only [f.injective.eq_iff]
    split_ifs <;> simp [hFa]

theorem rename_place_mem_iff {R : Type} [CommRing R] {T T' κ : Type} [Fintype κ] {p q : ℕ} (f : T ≃ T')
    {c : T → Fin p → ℕ} {c' : T → Fin q → ℕ} {d : T' → Fin p → ℕ} {d' : T' → Fin q → ℕ}
    (h : ∀ t, d (f t) = c t) (h' : ∀ t, d' (f t) = c' t) {P : Harm.Poly R T p q κ} :
    MvPolynomial.rename (f.prodCongr (Equiv.refl ((Fin p ⊕ Fin q) × κ))) P ∈ Harm.rowHighest R d d' ↔
      P ∈ Harm.rowHighest R c c' := by
  refine ⟨fun hP => ?_, rename_place_mem f h h'⟩
  have := rename_place_mem f.symm (d := c) (d' := c') (fun t => by rw [← h, f.apply_symm_apply])
    (fun t => by rw [← h', f.apply_symm_apply]) hP
  rw [MvPolynomial.rename_rename] at this
  convert this
  rw [show (f.symm.prodCongr (Equiv.refl ((Fin p ⊕ Fin q) × κ))) ∘
    (f.prodCongr (Equiv.refl ((Fin p ⊕ Fin q) × κ))) = id from
      (f.prodCongr (Equiv.refl ((Fin p ⊕ Fin q) × κ))).symm_comp_self, MvPolynomial.rename_id_apply]

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r g : ℕ}

theorem exists_isSympl (X : Data E r) (hL : SelfD X X.Λ) (idx : Fin g ≃ X.Ψ × Fin r) :
    ∃ bas : (Fin g ⊕ Fin g → ℤ) ≃ₗ[ℤ] X.Λ, IsSympl X bas := by
  obtain ⟨h1, h2, h3⟩ := ThetaHol.finrank_lattice X
  have hg : g = X.Ψ.card * r := by simpa using Fintype.card_congr idx
  have hκ : X.κ0 / 2 ≠ 0 := by rcases X.κ0_xi with h | h <;> rw [h] <;> simp [X.ξ0_ne]
  have hlat : ReciprocityTheory.MultiplicativeHeights.IsLattice X.Λ := ⟨X.Λ_fg, X.Λ_span⟩
  obtain ⟨B, hB⟩ : ∃ B : LinearMap.BilinForm ℚ (Fin r → E), ∀ u v, EF X u v = B u v :=
    ⟨_, TensLat.EF_eq_bilin X⟩
  choose k hk using fun u v : X.Λ => (hL.2 u).1 u.2 v v.2
  have hk' (u v : X.Λ) : (k u v : ℚ) = B u v := (hk u v).symm.trans (hB _ _)
  let β : LinearMap.BilinForm ℤ X.Λ := LinearMap.mk₂ ℤ k
    (fun x x' y => by apply Int.cast_injective (α := ℚ); simp [hk'])
    (fun m x y => by apply Int.cast_injective (α := ℚ); simp [hk', -zsmul_eq_mul, map_zsmul]; simp)
    (fun x y y' => by apply Int.cast_injective (α := ℚ); simp [hk'])
    (fun m x y => by apply Int.cast_injective (α := ℚ); simp [hk', -zsmul_eq_mul, map_zsmul]; simp)
  have hβ (u v : X.Λ) : (β u v : ℚ) = EF X u v := (hk u v).symm
  have halt : β.IsAlt := fun x => by
    have := TensLat.EF_swap X x x
    apply Int.cast_injective (α := ℚ)
    rw [hβ, Int.cast_zero]
    linarith
  have hbij : Function.Bijective β := by
    constructor
    · intro x x' h
      refine Subtype.ext (eq_of_EFf_eq hκ X.Gm_det hlat fun y hy => ?_)
      exact (hβ x ⟨y, hy⟩).symm.trans (h ▸ hβ x' ⟨y, hy⟩)
    · intro φ
      obtain ⟨x, hx, hφ⟩ := exists_traceFormDual_eq hκ X.Gm_det hlat φ.toAddMonoidHom
      refine ⟨⟨x, (hL.2 x).2 hx⟩, LinearMap.ext fun y => Int.cast_injective (α := ℚ) ?_⟩
      exact (hβ _ _).trans (hφ y).symm
  obtain ⟨g', bas, S, hs, -, hr⟩ := exists_symplectic_coordinates_adapted halt hbij (I := ⊥)
    (fun m x hm hx => by simpa [hm] using hx) (by simp) (Or.inr rfl)
  obtain rfl : g' = g := by omega
  exact ⟨bas, fun a b => by rw [← hβ, hs]; simp⟩

end GlobalTheory.Dict.Letters


open GlobalTheory.Dict.Letters GlobalTheory.Harm in
theorem GlobalTheory.Dict.exists_dic : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Geo.Tor.Level H) (c : Coeff l) (σ : c.F →+* ℂ) (r g n : ℕ) (X : Data E r) (a : (E →+* ℂ) × ℕ → ℕ) (e : Fin g ≃ Lt1 Dw), GoodEmb c σ → r = Dw.p + Dw.q → X.p0 = Dw.q → (∀ τ : E →+* ℂ, τ ∈ X.Ψ ↔ τ (H.rt : E) = H.rt0) → SelfD X X.Λ → Dom a n → ∃ Dc : Dic Dw c σ X g Dw.p n a, Dc.e = e ∧ (LastPos Dw a → 0 < Dw.p → ∃ τ, ∃ i : Fin Dw.p, i.val + 1 = Dw.p ∧ 1 ≤ Dc.k τ i) := by
  intro E _ _ _ H Dw l c σ r g n X a e hσ hr hp0 hΨ hL hD
  obtain ⟨hbij, hrt, hcj, -⟩ := GlobalTheory.Relab.relab_good E H l c σ hσ
  have hr' : X.p0 + Dw.p = r := by omega
  have i1 := ComplexEmbedding.involutive_conjugate E
  have i2 : ∀ τ, ¬ InPsi H τ ↔ InPsi H (ComplexEmbedding.conjugate τ) := not_mem_hostType_iff H
  have i3 : ∀ τ, InPsi H τ → Dw.mult τ = Dw.p := fun _ => mult_of_mem Dw
  have i4 : ∀ τ, InPsi H τ → Dw.mult (ComplexEmbedding.conjugate τ) = X.p0 := fun _ h =>
    (mult_conjEmb_of_mem Dw h).trans hp0.symm
  let f : {τ // InPsi H τ} ≃ X.Ψ := (Equiv.ofBijective _ hbij).subtypeEquiv fun τ =>
    ((hΨ _).trans (hrt τ)).symm
  have hf (t : {τ // InPsi H τ}) : (f t).1 = relab c σ t.1 := rfl
  let ρ : Lt1 Dw ≃ X.Ψ × (Fin Dw.p ⊕ Fin X.p0) :=
    (halfRowEquiv i1 i2 i3 i4).trans (f.prodCongr (Equiv.refl _))
  let idx : Fin g ≃ X.Ψ × Fin r := e.trans (ρ.trans (rowOf X hr'))
  have hidx (j) : (∃ t : {τ // InPsi H τ}, ∃ i : Fin Dw.p, (e j).1 = t.1 ∧ ((e j).2 : ℕ) = i ∧
      idx j = (f t, rowIdx hr' (Sum.inl i))) ∨
      ∃ t : {τ // InPsi H τ}, ∃ i : Fin X.p0, (e j).1 = ComplexEmbedding.conjugate t.1 ∧ ((e j).2 : ℕ) = i ∧
        idx j = (f t, rowIdx hr' (Sum.inr i)) := by
    obtain ⟨⟨t, i | i⟩, h⟩ := (halfRowEquiv i1 i2 i3 i4).symm.surjective (e j)
    · refine Or.inl ⟨t, i, by rw [← h]; rfl, by rw [← h]; rfl, ?_⟩
      simp only [idx, ρ, Equiv.trans_apply, ← h, Equiv.apply_symm_apply]
      rfl
    · refine Or.inr ⟨t, i, by rw [← h]; rfl, by rw [← h]; rfl, ?_⟩
      simp only [idx, ρ, Equiv.trans_apply, ← h, Equiv.apply_symm_apply]
      rfl
  obtain ⟨bas, hbas⟩ := exists_isSympl X hL idx
  let k₀ : {τ // InPsi H τ} → Fin Dw.p → ℕ := fun t => diffOf fun i => a (t.1, i)
  let k₀' : {τ // InPsi H τ} → Fin X.p0 → ℕ := fun t => diffOf fun i => a (ComplexEmbedding.conjugate t.1, i)
  have hx (t) : partOf (k₀ t) = fun i : Fin Dw.p => a (t.1, i) :=
    partOf_diffOf fun i j h => hD.1 _ h
  have hy (t) : partOf (k₀' t) = fun i : Fin X.p0 => a (ComplexEmbedding.conjugate t.1, i) :=
    partOf_diffOf fun i j h => hD.1 _ h
  let eL : LtN Dw n ≃ Harm.Var X.Ψ Dw.p X.p0 (Fin n) :=
    (typeLetterEquiv i1 i2 i3 i4 n).trans (f.prodCongr (Equiv.refl _))
  have hmem (P : MvPolynomial (LtN Dw n) c.F) :
      P ∈ HHa Dw.mult n c.F ComplexEmbedding.conjugate (InPsi H) (fun τ i => a (τ, i)) ↔
        MvPolynomial.rename eL P ∈ rowHighest c.F (k₀ ∘ f.symm) (k₀' ∘ f.symm) := by
    rw [Equiv.coe_trans, ← MvPolynomial.rename_rename,
      rename_place_mem_iff f (c := k₀) (c' := k₀') (fun t => by simp) (fun t => by simp)]
    simp only [mem_HHa_iff_rename i1 i2 i3 i4, mem_rowHighest_iff_rowAdd, hx, hy]
  have hinv (τ) : Function.invFun (relab c σ) (relab c σ τ) = τ := Function.leftInverse_invFun hbij.1 τ
  refine ⟨⟨hr', bas, idx, hbas, e, eL, k₀ ∘ f.symm, k₀' ∘ f.symm, fun x v j => ?_, fun j => ?_,
    fun ℓ => ?_, ?_, fun P hP => ?_, ?_⟩, rfl, fun hpos hp => ?_⟩
  · rcases hidx j with ⟨t, i, h1, h2, h3⟩ | ⟨t, i, h1, h2, h3⟩
    · have hi := i.isLt
      rw [pv, Function.comp_apply, h3, h2, h1, per_of_le _ _ _ _ (by simp), perFr,
        dite_eq_left (show relab c σ t.1 ∈ X.Ψ from (f t).2), dite_eq_left (by omega)]
      rfl
    · have hi := i.isLt
      have h4 : relab c σ (ComplexEmbedding.conjugate t.1) = ComplexEmbedding.conjugate (f t).1 := hcj t.1
      rw [pv, Function.comp_apply, h3, h2, h1, per_of_lt _ _ _ _ (by rw [rowIdx_inr]; omega), h4]
      have h5 : rowIdx hr' (Sum.inr i) = ⟨X.p0 - 1 - i, by omega⟩ := Fin.ext (rowIdx_inr hr' i)
      rw [h5]
      generalize f t = u
      obtain ⟨τ, hτ⟩ := u
      obtain ⟨τ, rfl⟩ := i1.surjective τ
      rw [show ComplexEmbedding.conjugate (ComplexEmbedding.conjugate τ) = τ from i1 τ, perFr,
        dite_eq_right (fun h => (X.cmType τ).1 h hτ), dite_eq_left (show conjEmb τ ∈ X.Ψ from hτ), dite_eq_left (by omega)]
      rfl
  · rcases hidx j with ⟨t, i, h1, h2, h3⟩ | ⟨t, i, h1, h2, h3⟩
    · rw [h3, h1]
      exact rowType_rowOf_inl X hr' (f t) i
    · rw [h3, h1]
      exact (rowType_rowOf_inr X hr' (f t) i).trans (hcj t.1).symm
  · have : idx.symm (rowOf X hr' ((eL ℓ).1, (eL ℓ).2.1)) = e.symm ⟨ℓ.1, ℓ.2.1⟩ := by
      rw [Equiv.symm_apply_eq]
      simp only [idx, Equiv.trans_apply, Equiv.apply_symm_apply]
      rfl
    rw [letterDir, this]
    rfl
  · funext τ j
    obtain ⟨t, rfl⟩ := f.surjective τ
    obtain ⟨i | i, rfl⟩ := (rowIdx hr').surjective j
    · rw [wtOf_inl, wtX, if_pos (by simp), hf, hinv, Function.comp_apply, f.symm_apply_apply, hx]
      simp
    · have hi := i.isLt
      rw [wtOf_inr, wtX, if_neg (by rw [rowIdx_inr]; omega), hf, ← hcj, hinv, Function.comp_apply,
        f.symm_apply_apply, hy, rowIdx_inr, show X.p0 - 1 - (X.p0 - 1 - i) = i by omega]
      rfl
  · rw [← MvPolynomial.map_rename]
    exact map_mem_rowHighest _ ((hmem P).1 hP)
  · letI := σ.toAlgebra
    rw [← span_map_rowHighest c.F ℂ]
    refine Submodule.span_mono ?_
    rintro _ ⟨Q, hQ, rfl⟩
    obtain ⟨P, rfl⟩ := MvPolynomial.rename_surjective _ eL.surjective Q
    exact ⟨P, (hmem P).2 hQ, (MvPolynomial.map_rename _ _ _).symm⟩
  · obtain ⟨t⟩ : Nonempty {τ // InPsi H τ} := by
      obtain ⟨τ⟩ : Nonempty (E →+* ℂ) := inferInstance
      by_cases h : InPsi H τ
      · exact ⟨⟨τ, h⟩⟩
      · exact ⟨⟨_, (i2 τ).1 h⟩⟩
    refine ⟨f t, ⟨Dw.p - 1, by omega⟩, by simp only; omega, ?_⟩
    have := hpos t.1 t.2 (by rw [i3 _ t.2]; exact hp)
    rw [i3 _ t.2] at this
    simp only [Function.comp_apply, Equiv.symm_apply_apply, k₀, diffOf]
    rw [dite_eq_right (by omega)]
    exact this
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.GaussianKernelIntegrableOnThinSlab
section
open Matrix Complex NumberField MeasureTheory GlobalTheory GlobalTheory.SW GlobalTheory.ThFr ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD
open scoped ComplexConjugate ComplexOrder Real Classical

namespace GlobalTheory.SW.KernInt

theorem norm_zpow_le {z : ℂ} {C : ℝ} (h1 : ‖z‖ ≤ C) (h2 : ‖z⁻¹‖ ≤ C) (k : ℤ) :
    ‖z ^ k‖ ≤ C ^ k.natAbs := by
  cases k with
  | ofNat k =>
    simp only [Int.ofNat_eq_natCast, zpow_natCast, Int.natAbs_natCast, norm_pow]
    exact pow_le_pow_left₀ (norm_nonneg _) h1 _
  | negSucc k =>
    rw [zpow_negSucc, ← inv_pow, norm_pow, Int.natAbs_negSucc]
    exact pow_le_pow_left₀ (norm_nonneg _) h2 _

theorem integrableOn_comp_linearEquiv {V W : Type} [NormedAddCommGroup V] [NormedSpace ℂ V]
    [FiniteDimensional ℂ V] [NormedAddCommGroup W] [NormedSpace ℂ W] [FiniteDimensional ℂ W]
    [MeasurableSpace V] [BorelSpace V] [MeasurableSpace W] [BorelSpace W]
    (μ : Measure V) (ν : Measure W) [μ.IsAddHaarMeasure] [ν.IsAddHaarMeasure] (L : V ≃ₗ[ℂ] W)
    {g : W → ℝ} {S : Set W} (h : IntegrableOn g S ν) : IntegrableOn (g ∘ L) (L ⁻¹' S) μ := by
  let L' := L.toContinuousLinearEquiv
  have _ : (μ.map L').IsAddHaarMeasure := L'.isAddHaarMeasure_map μ
  have e := Measure.isAddLeftInvariant_eq_smul (μ.map L') ν
  have h2 : IntegrableOn g S (μ.map L') := by
    rw [e, IntegrableOn, Measure.restrict_smul]
    exact h.smul_measure_nnreal
  exact (L'.toHomeomorph.measurableEmbedding.integrableOn_map_iff).1 h2

theorem integrableOn_place {r p q n : ℕ} (hr : p + q = r) (hp : p ≤ r) (hn : 2 * r ≤ n) :
    ∃ δ₀ : ℝ, 0 < δ₀ ∧ ∀ A : Matrix (Fin r) (Fin r) ℂ, IsUnit A.det →
      IntegrableOn (fun x : Fin r → Fin r → ℂ =>
        (‖lminor (A * Matrix.of x) ⟨p, Nat.lt_succ_of_le hp⟩‖ ^ n)⁻¹)
      {x | ∀ a b, ‖((A * Matrix.of x)ᵀ * (Matrix.diagonal fun a : Fin r => ((sgn p (a : ℕ) : ℝ) : ℂ)) *
        (A * Matrix.of x).map conj) a b -
        (Matrix.diagonal fun a : Fin r => ((sgn p (a : ℕ) : ℝ) : ℂ)) a b‖ < δ₀} volume := by
  subst hr
  obtain ⟨δ₀, h0, h⟩ := _root_.GlobalTheory.MinorInt.integrableOn_minor_fin p q n hn
  refine ⟨δ₀, h0, fun A hA => ?_⟩
  let e : Fin p ⊕ Fin q ≃ Fin (p + q) := finSumFinEquiv
  let L : (Fin (p + q) → Fin (p + q) → ℂ) ≃ₗ[ℂ] ((Fin p ⊕ Fin q) → (Fin p ⊕ Fin q) → ℂ) :=
    { toFun := fun x => (A * Matrix.of x).submatrix e e
      invFun := fun y => (A⁻¹ * (Matrix.of y).submatrix e.symm e.symm : Matrix _ _ ℂ)
      map_add' := fun x y => by
        change (A * (Matrix.of x + Matrix.of y)).submatrix e e = _
        rw [Matrix.mul_add]; rfl
      map_smul' := fun c x => by
        change (A * (c • Matrix.of x)).submatrix e e = _
        rw [Matrix.mul_smul]; rfl
      left_inv := fun x => by
        change A⁻¹ * ((A * Matrix.of x).submatrix e e).submatrix e.symm e.symm = Matrix.of x
        rw [Matrix.submatrix_submatrix, e.self_comp_symm, Matrix.submatrix_id_id,
          Matrix.nonsing_inv_mul_cancel_left _ _ hA]
      right_inv := fun y => by
        change (A * (A⁻¹ * (Matrix.of y).submatrix e.symm e.symm)).submatrix e e = Matrix.of y
        rw [Matrix.mul_nonsing_inv_cancel_left _ _ hA,
          Matrix.submatrix_submatrix, e.symm_comp_self, Matrix.submatrix_id_id] }
  have _ : (volume : Measure (Fin (p + q) → ℂ)).IsAddHaarMeasure := Measure.pi.isAddHaarMeasure _
  have _ : (volume : Measure (Fin (p + q) → Fin (p + q) → ℂ)).IsAddHaarMeasure :=
    Measure.pi.isAddHaarMeasure _
  have _ : (volume : Measure (Fin p ⊕ Fin q → ℂ)).IsAddHaarMeasure := Measure.pi.isAddHaarMeasure _
  have _ : (volume : Measure ((Fin p ⊕ Fin q) → (Fin p ⊕ Fin q) → ℂ)).IsAddHaarMeasure :=
    Measure.pi.isAddHaarMeasure _
  have hS : Matrix.fromBlocks (1 : Matrix (Fin p) (Fin p) ℂ) 0 0 (-1 : Matrix (Fin q) (Fin q) ℂ) =
      (Matrix.diagonal fun a : Fin (p + q) => ((sgn p (a : ℕ) : ℝ) : ℂ)).submatrix e e := by
    rw [Matrix.submatrix_diagonal_equiv]
    ext (a | a) (b | b) <;> simp [Matrix.diagonal_apply, Matrix.one_apply, sgn, e]
    split_ifs <;> simp
  refine (integrableOn_comp_linearEquiv volume volume L h).mono_set fun x hx a b => ?_
  have e1 : Matrix.of (L x) = (A * Matrix.of x).submatrix e e := rfl
  rw [e1, hS, Matrix.transpose_submatrix, Matrix.submatrix_mul_equiv, ← Matrix.submatrix_map,
    Matrix.submatrix_mul_equiv]
  exact hx _ _

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} (X : Data E r)

theorem gram_inv_mul {x₀ : Frame X.Ψ r} (hx₀ : ∀ τ : X.Ψ, gram τ.1 X.Gm (mat x₀ τ) = sgnM X)
    (τ : X.Ψ) (hu : IsUnit (mat x₀ τ).det) (y : Matrix (Fin r) (Fin r) ℂ) :
    ((mat x₀ τ)⁻¹ * y)ᵀ * sgnM X * ((mat x₀ τ)⁻¹ * y).map conj = gram τ.1 X.Gm y := by
  have e := FrameDegreeData.gram_mul τ.1 X.Gm (mat x₀ τ) ((mat x₀ τ)⁻¹ * y)
  rw [Matrix.mul_nonsing_inv_cancel_left _ _ hu, hx₀ τ] at e
  exact e.symm

theorem hermC_eq_gram (τ : E →+* ℂ) (A : Matrix (Fin r) (Fin r) ℂ) (v w : Fin r → ℂ) :
    hermC τ X.Gm (A *ᵥ v) (A *ᵥ w) = ∑ a, ∑ b, v a * gram τ X.Gm A a b * conj (w b) := by
  have e : ∀ v w : Fin r → ℂ, ∀ M : Matrix (Fin r) (Fin r) ℂ,
      ∑ a, ∑ b, v a * M a b * conj (w b) = v ⬝ᵥ M *ᵥ star w := fun v w M => by
    simp [dotProduct, Matrix.mulVec, Finset.mul_sum, mul_assoc]
  rw [e, FrameDegreeData.gram_eq]
  refine (e _ _ (X.Gm.map τ)).trans ?_
  rw [Matrix.star_mulVec, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec,
    Matrix.dotProduct_mulVec v, Matrix.vecMul_transpose, ← Matrix.mulVec_transpose]
  rfl

theorem torus_unitary {x₀ : Frame X.Ψ r} (hx₀ : ∀ τ : X.Ψ, gram τ.1 X.Gm (mat x₀ τ) = sgnM X)
    (τ : X.Ψ) (hu : IsUnit (mat x₀ τ).det) (t : Fin r → ℂ) (ht : ∀ i, ‖t i‖ = 1) (v w : Fin r → ℂ) :
    hermC τ.1 X.Gm ((mat x₀ τ * Matrix.diagonal t * (mat x₀ τ)⁻¹) *ᵥ v)
      ((mat x₀ τ * Matrix.diagonal t * (mat x₀ τ)⁻¹) *ᵥ w) = hermC τ.1 X.Gm v w := by
  have e : gram τ.1 X.Gm (mat x₀ τ * Matrix.diagonal t * (mat x₀ τ)⁻¹) = gram τ.1 X.Gm 1 := by
    have e1 : gram τ.1 X.Gm (mat x₀ τ * Matrix.diagonal t) = gram τ.1 X.Gm (mat x₀ τ) := by
      rw [FrameDegreeData.gram_mul, hx₀ τ, sgnM, Matrix.diagonal_transpose, Matrix.diagonal_map (map_zero _),
        Matrix.diagonal_mul_diagonal, Matrix.diagonal_mul_diagonal]
      congr 1
      funext i
      rw [mul_right_comm, Complex.mul_conj', ht]
      simp
    rw [FrameDegreeData.gram_mul, e1, ← FrameDegreeData.gram_mul, Matrix.mul_nonsing_inv _ hu]
  rw [hermC_eq_gram, e, ← hermC_eq_gram, Matrix.one_mulVec, Matrix.one_mulVec]

end GlobalTheory.SW.KernInt

theorem GlobalTheory.SW.kern_integrableOn_slab : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (X : Data E r) (g q0 : ℕ) (hr : X.p0 + q0 = r) (idx : Fin g ≃ X.Ψ × Fin r) (n : ℕ) (c : X.Ψ → Fin q0 → ℕ) (c' : X.Ψ → Fin X.p0 → ℕ) (m : ℕ) (P : Fin m → Harm.Poly ℂ X.Ψ q0 X.p0 (Fin n)), Even n → (∀ j, P j ∈ Harm.rowHighest ℂ c c') → 2 * r ≤ n → ∃ δ₁ : ℝ, 0 < δ₁ ∧ ∀ δ : ℝ, 0 < δ → δ ≤ δ₁ → ∀ x₁ ∈ X.dom, IntegrableOn (fun x₂ => kern X hr idx P x₁ x₂) (slab X δ) volume ∧ ∃ C : ℝ, ∀ x₂ ∈ slab X δ, ‖kern X hr idx P x₁ x₂‖ ≤ C := by
  intro E _ _ _ r X g q0 hr idx n c c' m P hn hP h2
  obtain ⟨δa, ha, hA⟩ := thin_slab E r X
  obtain ⟨δb, hb, hB⟩ := KernInt.integrableOn_place hr X.p0_le h2
  refine ⟨min δa δb, lt_min ha hb, fun δ hδ hδ1 x₁ hx₁ => ?_⟩
  obtain ⟨hopen, hsub, horth, -, hun, ⟨C, hC⟩, hdec⟩ := hA δ hδ (hδ1.trans (min_le_left _ _))
  obtain ⟨x₀, hx₀, b₁, hb₁, rfl⟩ := hdec x₁ hx₁
  obtain ⟨hinv, hsym, -⟩ := kern_invariant_symm_pos E r X g q0 hr idx n c c' m P hn hP
  have hhol := KernHol.kern_hol_weight E r X g q0 hr idx n c c' m P hn hP
  have h₀ : x₀ ∈ X.dom := hsub (horth x₀ hx₀)
  have hu : ∀ τ, IsUnit (mat x₀ τ).det := fun τ => isUnit_iff_ne_zero.2 (h₀ τ).1
  set la := wtOf X hr c c' n with hla
  set f : Frame X.Ψ r → ℂ := fun x => kern X hr idx P x x₀ with hf
  have hbd := lowest_weight_function_bound E r X q0 hr n c c' x₀ hn hx₀ f (hhol x₀ h₀).1
    (hhol x₀ h₀).2 (fun t ht x hx => by
      have ht0 : ∀ τ i, t τ i ≠ 0 := fun τ i => norm_ne_zero_iff.1 (by rw [ht τ i]; exact one_ne_zero)
      have hU := fun τ => KernInt.torus_unitary X hx₀ τ (hu τ) (t τ) (ht τ)
      let s : Frame X.Ψ r := fun τ => Matrix.diagonal fun i => (t τ i)⁻¹
      have hs : s ∈ Bor X.Ψ r := fun τ => by
        refine ⟨?_, fun a c hca => Matrix.diagonal_apply_ne _ hca.ne'⟩
        change (Matrix.diagonal fun i => (t τ i)⁻¹).det ≠ 0
        rw [Matrix.det_diagonal]
        exact Finset.prod_ne_zero_iff.2 fun i _ => inv_ne_zero (ht0 τ i)
      have e : X.lmulC (fun τ => mat x₀ τ * Matrix.diagonal (t τ) * (mat x₀ τ)⁻¹) (rmul x₀ s) = x₀ := by
        funext τ
        change mat x₀ τ * Matrix.diagonal (t τ) * (mat x₀ τ)⁻¹ *
          (mat x₀ τ * Matrix.diagonal fun i => (t τ i)⁻¹) = mat x₀ τ
        rw [Matrix.mul_assoc, Matrix.nonsing_inv_mul_cancel_left _ _ (hu τ), Matrix.mul_assoc,
          Matrix.diagonal_mul_diagonal]
        simp [ht0]
      have hxs : rmul x₀ s ∈ X.dom := ((hun _ hU).2.2 _).1 (by rw [e]; exact h₀)
      have e2 := hinv _ hU x hx _ hxs
      rw [e] at e2
      simp only [hf]
      rw [e2, hsym _ hxs _ hx, (hhol x hx).2 x₀ h₀ s hs, map_mul, ← hsym _ h₀ _ hx]
      congr 1
      rw [bchar, map_prod]
      refine Finset.prod_congr rfl fun τ _ => ?_
      rw [map_prod]
      refine Finset.prod_congr rfl fun i _ => ?_
      have e3 : s τ i i = conj (t τ i) :=
        (Matrix.diagonal_apply_eq _ _).trans (Complex.inv_eq_conj (ht τ i))
      rw [map_zpow₀, e3, Complex.conj_conj])
  set D : Frame X.Ψ r → X.Ψ → ℝ := fun x τ =>
    ‖lminor ((mat x₀ τ)⁻¹ * mat x τ) ⟨X.p0, Nat.lt_succ_of_le X.p0_le⟩‖ with hD
  set K : ℝ := ‖bchar la b₁‖ * ∏ τ, ∏ i, C ^ (la τ i).natAbs with hK
  have key : ∀ x ∈ slab X δ, ‖kern X hr idx P (rmul x₀ b₁) x‖ ≤ K * ‖f x₀‖ ∧
      ‖kern X hr idx P (rmul x₀ b₁) x‖ ≤
        (K * ‖f x₀‖ * ∏ _τ : X.Ψ, (C ^ X.p0) ^ n) * ∏ τ, (D x τ ^ n)⁻¹ := by
    intro x hx
    have hxd := hsub hx
    obtain ⟨x', hx', b, hb, rfl, hbC⟩ := hC x hx
    have hx'd := hsub (horth x' hx')
    have h1 : ∀ τ, 1 ≤ D x' τ := fun τ => by
      have := FramePotential.one_le_norm_lminor_sq X.p0_le ((mat x₀ τ)⁻¹ * mat x' τ)
        ((KernInt.gram_inv_mul X hx₀ τ (hu τ) _).trans (hx' τ))
      exact (one_le_sq_iff_one_le_abs _).1 this |>.trans_eq (abs_norm _)
    have h3 : ‖bchar la b‖ ≤ ∏ τ, ∏ i, C ^ (la τ i).natAbs := by
      rw [bchar, norm_prod]
      refine Finset.prod_le_prod₀ (fun _ _ => norm_nonneg _) fun τ _ => ?_
      rw [norm_prod]
      exact Finset.prod_le_prod₀ (fun _ _ => norm_nonneg _) fun i _ =>
        KernInt.norm_zpow_le (hbC τ i i).1 (hbC τ i i).2 _
    have h4 : ‖kern X hr idx P (rmul x₀ b₁) (rmul x' b)‖ ≤ K * ‖f x'‖ := by
      rw [(hhol _ hxd).2 x₀ h₀ b₁ hb₁, hsym _ hxd _ h₀, (hhol _ h₀).2 x' hx'd b hb, norm_mul,
        Complex.norm_conj, norm_mul, hK, mul_assoc]
      gcongr
    have hK0 : 0 ≤ K := mul_nonneg (norm_nonneg _) ((norm_nonneg _).trans h3)
    have h5 : ‖f x'‖ * ∏ τ, D x' τ ^ n ≤ ‖f x₀‖ := hbd x' hx'
    have h6 : 1 ≤ ∏ τ, D x' τ ^ n := by
      refine le_of_eq_of_le ?_ (Finset.prod_le_prod₀ (f := fun _ => (1 : ℝ)) (fun _ _ => zero_le_one)
        fun τ _ => one_le_pow₀ (h1 τ))
      simp
    have h7 : ∀ τ, D (rmul x' b) τ = D x' τ * ∏ j : Fin X.p0,
        ‖b τ (Fin.castLE X.p0_le j) (Fin.castLE X.p0_le j)‖ := fun τ => by
      change ‖lminor ((mat x₀ τ)⁻¹ * (mat x' τ * mat b τ)) _‖ = _
      rw [← Matrix.mul_assoc, FramePotential.lminor_mul_upper _ (FrameDegreeData.upper_of_bor X hb τ),
        norm_mul, norm_prod]
      rfl
    have h8 : ∀ τ, 0 < D (rmul x' b) τ := fun τ => by
      rw [h7]
      exact mul_pos (one_pos.trans_le (h1 τ))
        (Finset.prod_pos fun j _ => norm_pos_iff.2 (FrameDegreeData.bdiag_ne X hb τ _))
    have h9 : ∀ τ, D (rmul x' b) τ ≤ D x' τ * C ^ X.p0 := fun τ => by
      rw [h7]
      refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
      refine (Finset.prod_le_prod₀ (fun _ _ => norm_nonneg _)
        (g := fun _ => C) fun j _ => (hbC τ _ _).1).trans_eq ?_
      simp
    have h10 : ∏ τ, D (rmul x' b) τ ^ n ≤ (∏ τ, D x' τ ^ n) * ∏ _τ : X.Ψ, (C ^ X.p0) ^ n := by
      rw [← Finset.prod_mul_distrib]
      refine Finset.prod_le_prod₀ (fun τ _ => (pow_pos (h8 τ) n).le) fun τ _ => ?_
      rw [← mul_pow]
      exact pow_le_pow_left₀ (h8 τ).le (h9 τ) n
    have h11 : 0 < ∏ τ, D (rmul x' b) τ ^ n := Finset.prod_pos fun τ _ => pow_pos (h8 τ) n
    have h12 : 0 ≤ ∏ _τ : X.Ψ, (C ^ X.p0) ^ n :=
      nonneg_of_mul_nonneg_right (h11.trans_le h10).le (one_pos.trans_le h6)
    refine ⟨h4.trans (mul_le_mul_of_nonneg_left ((le_mul_of_one_le_right (norm_nonneg _) h6).trans h5)
      hK0), h4.trans ?_⟩
    rw [Finset.prod_inv_distrib, ← div_eq_mul_inv, le_div_iff₀ h11, mul_assoc K, mul_assoc K]
    refine mul_le_mul_of_nonneg_left ?_ hK0
    refine (mul_le_mul_of_nonneg_left h10 (norm_nonneg _)).trans ?_
    rw [← mul_assoc]
    exact mul_le_mul_of_nonneg_right h5 h12
  refine ⟨?_, _, fun x hx => (key x hx).1⟩
  have hI : IntegrableOn (fun x : Frame X.Ψ r => ∏ τ, (D x τ ^ n)⁻¹) (slab X δ) volume := by
    have hτ := fun τ : X.Ψ => hB (mat x₀ τ)⁻¹ (Matrix.isUnit_nonsing_inv_det _ (hu τ))
    simp only [IntegrableOn] at hτ
    have _ : ∀ S : Set (Fin r → Fin r → ℂ), SigmaFinite (volume.restrict S) := fun S => inferInstance
    have h := Integrable.fintype_prod_dep hτ
    rw [← Measure.restrict_pi_pi] at h
    refine IntegrableOn.mono_set h fun x hx τ _ a b => ?_
    have := KernInt.gram_inv_mul X hx₀ τ (hu τ) (mat x τ)
    refine lt_of_eq_of_lt ?_ ((hx τ a b).trans_le (hδ1.trans (min_le_right _ _)))
    rw [← this]
    rfl
  refine Integrable.mono' (hI.const_mul _) ?_
    ((ae_restrict_iff' hopen.measurableSet).2 (Filter.Eventually.of_forall fun x hx => (key x hx).2))
  refine ContinuousOn.aestronglyMeasurable ?_ hopen.measurableSet
  refine ContinuousOn.congr (f := fun x => bchar la b₁ * conj (f x)) ?_ fun x hx => ?_
  · exact continuousOn_const.mul
      (Complex.continuous_conj.comp_continuousOn ((hhol x₀ h₀).1.continuousOn.mono hsub))
  · change kern X hr idx P (rmul x₀ b₁) x = _
    rw [(hhol _ (hsub hx)).2 x₀ h₀ b₁ hb₁, hsym _ (hsub hx) _ h₀]
end

