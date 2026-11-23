module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0016
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0009
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0062
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ValZpowIff
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ThetaCellCovers.SFunOf
public import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.AffineGLForms.GenSpace
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.LeviEmbMemNormalizerLower
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.DiscreteSeriesTopClasses.StTopClass

@[expose] public section

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MeasureImageDoubleCoset
section
open MeasureTheory GlobalTheory.LocGL

namespace GlobalTheory.CompanionTheory.DoubleCosetVolume

theorem measure_doubleCoset {Q : Type*} [Group Q] [TopologicalSpace Q] [IsTopologicalGroup Q]
    [MeasurableSpace Q] [BorelSpace Q] (μ : Measure Q) [μ.IsMulLeftInvariant] (B : Subgroup Q)
    (hB : IsOpen (B : Set Q)) (s : Q)
    (hfin : (B.map (MulAut.conj s).toMonoidHom).relIndex B ≠ 0) :
    μ {q : Q | ∃ x ∈ B, ∃ y ∈ B, q = x * s * y} =
      ((B.map (MulAut.conj s).toMonoidHom).relIndex B : ENNReal) * μ (B : Set Q) := by
  classical
  set C : Subgroup B := (B.map (MulAut.conj s).toMonoidHom).subgroupOf B with hC
  have hidx : C.index ≠ 0 := hfin
  have : C.FiniteIndex := ⟨hidx⟩
  have : Finite (B ⧸ C) := inferInstance
  letI : Fintype (B ⧸ C) := Fintype.ofFinite _
  have hmemC : ∀ w : B, w ∈ C ↔ ∃ b ∈ B, s * b * s⁻¹ = (w : Q) := by
    intro w
    rw [hC, Subgroup.mem_subgroupOf, Subgroup.mem_map]
    simp [MulAut.conj_apply]
  let r : B ⧸ C → Q := fun c => ((Quotient.out c : B) : Q) * s
  let T : B ⧸ C → Set Q := fun c => (fun h => (r c)⁻¹ * h) ⁻¹' (B : Set Q)
  have hcover : {q : Q | ∃ x ∈ B, ∃ y ∈ B, q = x * s * y} = ⋃ c, T c := by
    ext q
    simp only [Set.mem_ofPred_eq, Set.mem_iUnion]
    constructor
    · rintro ⟨x, hx, y, hy, rfl⟩
      refine ⟨QuotientGroup.mk (⟨x, hx⟩ : B), ?_⟩
      have h1 : (QuotientGroup.mk (Quotient.out (QuotientGroup.mk (⟨x, hx⟩ : B) : B ⧸ C)) : B ⧸ C) =
          QuotientGroup.mk (⟨x, hx⟩ : B) := QuotientGroup.out_eq' _
      obtain ⟨b, hb, hbw⟩ := (hmemC _).1 (QuotientGroup.eq.1 h1)
      have h2 : ((Quotient.out (QuotientGroup.mk (⟨x, hx⟩ : B) : B ⧸ C) : B) : Q)⁻¹ * x =
          s * b * s⁻¹ := by
        rw [hbw]; simp
      show (r _)⁻¹ * (x * s * y) ∈ B
      have h3 : (r (QuotientGroup.mk (⟨x, hx⟩ : B)))⁻¹ * (x * s * y) = b * y := by
        show (((Quotient.out (QuotientGroup.mk (⟨x, hx⟩ : B) : B ⧸ C) : B) : Q) * s)⁻¹ *
          (x * s * y) = b * y
        rw [mul_inv_rev, mul_assoc s⁻¹, ← mul_assoc _ (x * s) y, ← mul_assoc _ x s, h2]
        group
      rw [h3]
      exact B.mul_mem hb hy
    · rintro ⟨c, hc⟩
      refine ⟨_, (Quotient.out c : B).2, _, hc, ?_⟩
      show q = r c * ((r c)⁻¹ * q)
      group
  have hdisj : Pairwise (Function.onFun Disjoint T) := by
    intro c c' hcc
    refine Set.disjoint_left.2 fun q hq hq' => hcc ?_
    have hq1 : (r c)⁻¹ * q ∈ B := hq
    have hq2 : (r c')⁻¹ * q ∈ B := hq'
    have hw : (Quotient.out c : B)⁻¹ * (Quotient.out c' : B) ∈ C := by
      refine (hmemC _).2 ⟨((r c)⁻¹ * q) * ((r c')⁻¹ * q)⁻¹, B.mul_mem hq1 (B.inv_mem hq2), ?_⟩
      show _ = ((Quotient.out c : B) : Q)⁻¹ * ((Quotient.out c' : B) : Q)
      show s * (((((Quotient.out c : B) : Q) * s)⁻¹ * q) *
        (((((Quotient.out c' : B) : Q) * s)⁻¹ * q))⁻¹) * s⁻¹ = _
      group
    have := QuotientGroup.eq.2 hw
    rw [QuotientGroup.out_eq', QuotientGroup.out_eq'] at this
    exact this
  have hopen : ∀ c, MeasurableSet (T c) := fun c =>
    (hB.preimage (continuous_const.mul continuous_id)).measurableSet
  have hT : ∀ c, μ (T c) = μ (B : Set Q) := fun c => measure_preimage_mul μ _ _
  rw [hcover, measure_iUnion hdisj hopen]
  simp only [hT, tsum_fintype, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  congr 2
  show _ = C.index
  rw [Subgroup.index, Nat.card_eq_fintype_card]

theorem relIndex_map_mk {G : Type*} [Group G] (Z : Subgroup G) [Z.Normal] (H : Subgroup G) (t : G)
    (hZ : ∀ g ∈ H, ∀ h ∈ H, (t * h * t⁻¹)⁻¹ * g ∈ Z → ∃ h₂ ∈ H, t * h₂ * t⁻¹ = g) :
    ((H.map (QuotientGroup.mk' Z)).map (MulAut.conj (QuotientGroup.mk' Z t)).toMonoidHom).relIndex
        (H.map (QuotientGroup.mk' Z)) =
      (H.map (MulAut.conj t).toMonoidHom).relIndex H := by
  rw [← Subgroup.relIndex_comap, ← Subgroup.inf_relIndex_right,
    ← Subgroup.inf_relIndex_right (H.map (MulAut.conj t).toMonoidHom)]
  congr 1
  ext g
  simp only [Subgroup.mem_inf, Subgroup.mem_comap, Subgroup.mem_map]
  refine and_congr_left fun hg => ?_
  simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, exists_exists_and_eq_and]
  constructor
  · rintro ⟨h, hh, he⟩
    have h1 : (QuotientGroup.mk' Z) (t * h * t⁻¹) = (QuotientGroup.mk' Z) g := by
      simpa using he
    exact hZ g hg h hh (QuotientGroup.eq.1 h1)
  · rintro ⟨h, hh, rfl⟩
    exact ⟨h, hh, by simp⟩

theorem toNat_natCast_mul (j : ℕ) (x : ℤ) : ((j : ℤ) * x).toNat = j * x.toNat := by
  rcases le_total 0 x with h | h
  · lift x to ℕ using h
    rw [← Nat.cast_mul, Int.toNat_natCast, Int.toNat_natCast]
  · have h1 : (j : ℤ) * x ≤ 0 := mul_nonpos_of_nonneg_of_nonpos (by positivity) h
    rw [Int.toNat_of_nonpos h1, Int.toNat_of_nonpos h, mul_zero]

end GlobalTheory.CompanionTheory.DoubleCosetVolume

namespace GlobalTheory.CompanionTheory.DoubleCosetVolume

open ValuativeRel

variable {k : Type} [Field k] [ValuativeRel k]

theorem central_mem_cong {N : ℕ} {r : ValueGroupWithZero k} (hr : r < 1)
    (t : GL (Fin N) k) (d : Fin N → k) (hd : ∀ i, d i ≠ 0)
    (ht : (t : Matrix (Fin N) (Fin N) k) = Matrix.diagonal d)
    (g h z : GL (Fin N) k)
    (hg : ∀ i j, valuation k ((g : Matrix (Fin N) (Fin N) k) i j - (1 : Matrix (Fin N) (Fin N) k) i j) ≤ r)
    (hh : ∀ i j, valuation k ((h : Matrix (Fin N) (Fin N) k) i j - (1 : Matrix (Fin N) (Fin N) k) i j) ≤ r)
    (hz : z ∈ Subgroup.center (GL (Fin N) k)) (hgz : g = t * h * t⁻¹ * z) :
    ∀ i j, valuation k ((z : Matrix (Fin N) (Fin N) k) i j - (1 : Matrix (Fin N) (Fin N) k) i j) ≤ r := by
  obtain ⟨c, hc⟩ := Matrix.GeneralLinearGroup.mem_center_iff_val_mem_range_scalar.1 hz
  have hzv : (z : Matrix (Fin N) (Fin N) k) = Matrix.scalar (Fin N) c := hc.symm
  have htinv : ((t⁻¹ : GL (Fin N) k) : Matrix (Fin N) (Fin N) k) = Matrix.diagonal fun i => (d i)⁻¹ := by
    refine Units.inv_eq_of_mul_eq_one_right ?_
    rw [ht, Matrix.diagonal_mul_diagonal]
    simp [hd, Matrix.diagonal_one]
  intro i j
  by_cases hij : i = j
  · subst hij
    have h1 : (g : Matrix (Fin N) (Fin N) k) i i = (h : Matrix (Fin N) (Fin N) k) i i * c := by
      rw [hgz]
      simp only [Units.val_mul, hzv, htinv, ht, Matrix.scalar_apply, Matrix.mul_diagonal,
        Matrix.diagonal_mul]
      field_simp [hd i]
    have h2 : valuation k ((h : Matrix (Fin N) (Fin N) k) i i) = 1 := by
      have h3 := hh i i
      rw [Matrix.one_apply_eq] at h3
      have h4 := Valuation.map_one_add_of_lt (valuation k) (h3.trans_lt hr)
      rwa [add_sub_cancel] at h4
    have h5 := hg i i
    have h6 := hh i i
    rw [Matrix.one_apply_eq] at h5 h6 ⊢
    have h7 : (h : Matrix (Fin N) (Fin N) k) i i * (c - 1) =
        ((g : Matrix (Fin N) (Fin N) k) i i - 1) - ((h : Matrix (Fin N) (Fin N) k) i i - 1) := by
      rw [h1]; ring
    have h8 : valuation k (c - 1) ≤ r := by
      have h9 := Valuation.map_sub (valuation k) ((g : Matrix (Fin N) (Fin N) k) i i - 1)
        ((h : Matrix (Fin N) (Fin N) k) i i - 1)
      rw [← h7, map_mul, h2, one_mul] at h9
      exact h9.trans (max_le h5 h6)
    rw [hzv]
    simpa using h8
  · rw [hzv, Matrix.one_apply_ne hij]
    simp [Matrix.scalar_apply, Matrix.diagonal_apply_ne _ hij]

end GlobalTheory.CompanionTheory.DoubleCosetVolume

namespace GlobalTheory.CompanionTheory.DoubleCosetVolume

open ValuativeRel

theorem measure_image_doubleCoset : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (N : ℕ) (ϖ : k) (m : ℕ) (a : Fin N → ℤ), ϖ ≠ 0 → ValuativeRel.valuation k (ϖ) < 1 → (∀ x : k, ValuativeRel.valuation k (x) < 1 → ValuativeRel.valuation k (x) ≤ ValuativeRel.valuation k (ϖ)) → 1 ≤ m → Antitone a → ∀ D : GL (Fin N) k, (D : Matrix (Fin N) (Fin N) k) = Matrix.diagonal (fun i => ϖ ^ (a i)) → ∀ [MeasurableSpace (AdGL k N)] [BorelSpace (AdGL k N)] (μ : MeasureTheory.Measure (AdGL k N)), μ.IsHaarMeasure → ∀ j : ℕ, μ ((QuotientGroup.mk : GL (Fin N) k → AdGL k N) '' {g : GL (Fin N) k | ∃ x ∈ {g : GL (Fin N) k | ∀ i j, ValuativeRel.valuation k ((g : Matrix (Fin N) (Fin N) k) i j - (1 : Matrix (Fin N) (Fin N) k) i j) ≤ ValuativeRel.valuation k (ϖ ^ m)}, ∃ y ∈ {g : GL (Fin N) k | ∀ i j, ValuativeRel.valuation k ((g : Matrix (Fin N) (Fin N) k) i j - (1 : Matrix (Fin N) (Fin N) k) i j) ≤ ValuativeRel.valuation k (ϖ ^ m)}, g = x * D ^ j * y}) = ((Nat.card (IsLocalRing.ResidueField (ValuativeRel.valuation k).integer) : ENNReal) ^ (j * (∑ i : Fin N, ∑ j : Fin N, if i < j then (a i - a j).toNat else 0))) * μ ((QuotientGroup.mk : GL (Fin N) k → AdGL k N) '' {g : GL (Fin N) k | ∀ i j, ValuativeRel.valuation k ((g : Matrix (Fin N) (Fin N) k) i j - (1 : Matrix (Fin N) (Fin N) k) i j) ≤ ValuativeRel.valuation k (ϖ ^ m)}) := by
  intro k _ _ _ _ N ϖ m a hϖ0 hϖ1 hunif hm ha D hD _ _ μ hμ j
  have hϖm0 : ϖ ^ m ≠ 0 := pow_ne_zero _ hϖ0
  have hr : valuation k (ϖ ^ m) < 1 := by
    rw [map_pow]
    exact pow_lt_one₀ zero_le hϖ1 (by omega)
  obtain ⟨H, hH⟩ := GlobalTheory.CompanionTheory.PrincipalCongruence.exists_principalCongruence k N (ϖ ^ m) hϖm0 hr
  have hopen : IsOpen (H : Set (GL (Fin N) k)) := by
    rw [hH]
    exact (GlobalTheory.CompanionTheory.PrincipalCongruence.isOpen_isCompact_principal k N (ϖ ^ m) hϖm0 hr).1
  have hmem : ∀ g : GL (Fin N) k, g ∈ H ↔ ∀ i j, valuation k
      ((g : Matrix (Fin N) (Fin N) k) i j - (1 : Matrix (Fin N) (Fin N) k) i j) ≤ valuation k (ϖ ^ m) := by
    intro g
    rw [← SetLike.mem_coe, hH]
    rfl
  rw [← hH]
  set t : GL (Fin N) k := D ^ j with ht
  have hDj : (t : Matrix (Fin N) (Fin N) k) = Matrix.diagonal (fun i => ϖ ^ ((j : ℤ) * a i)) := by
    rw [ht, Units.val_pow_eq_pow_val, hD, Matrix.diagonal_pow]
    congr 1
    funext i
    simp only [Pi.pow_apply]
    rw [← zpow_natCast, ← zpow_mul, mul_comm]
  have hanti : Antitone fun i => (j : ℤ) * a i := fun x y hxy =>
    mul_le_mul_of_nonneg_left (ha hxy) (by positivity)
  have hindex := GlobalTheory.CompanionTheory.CongIndex.index_main k N ϖ m (fun i => (j : ℤ) * a i) hϖ0 hϖ1 hunif hm hanti t hDj H hH
  have hsum : (∑ i : Fin N, ∑ l : Fin N, if i < l then ((j : ℤ) * a i - (j : ℤ) * a l).toNat else 0) =
      j * ∑ i : Fin N, ∑ l : Fin N, if i < l then (a i - a l).toNat else 0 := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun l _ => ?_
    split_ifs
    · rw [← mul_sub, toNat_natCast_mul]
    · simp
  simp only [hsum] at hindex
  have hq : 0 < Nat.card (IsLocalRing.ResidueField (valuation k).integer) := Nat.card_pos
  set Z : Subgroup (GL (Fin N) k) := Subgroup.center (GL (Fin N) k) with hZdef
  have hmerge : ∀ g ∈ H, ∀ h ∈ H, (t * h * t⁻¹)⁻¹ * g ∈ Z → ∃ h₂ ∈ H, t * h₂ * t⁻¹ = g := by
    intro g hg h hh hz
    have hzH : (t * h * t⁻¹)⁻¹ * g ∈ H := (hmem _).2 (central_mem_cong hr t _
      (fun i => zpow_ne_zero _ hϖ0) hDj g h _ ((hmem g).1 hg) ((hmem h).1 hh) hz (by group))
    refine ⟨h * ((t * h * t⁻¹)⁻¹ * g), H.mul_mem hh hzH, ?_⟩
    have hc := Subgroup.mem_center_iff.1 hz t⁻¹
    calc t * (h * ((t * h * t⁻¹)⁻¹ * g)) * t⁻¹
        = t * h * (((t * h * t⁻¹)⁻¹ * g) * t⁻¹) := by group
      _ = t * h * (t⁻¹ * ((t * h * t⁻¹)⁻¹ * g)) := by rw [hc]
      _ = g := by group
  have hI := relIndex_map_mk Z H t hmerge
  set B : Subgroup (AdGL k N) := H.map (QuotientGroup.mk' Z) with hB
  set s : AdGL k N := QuotientGroup.mk' Z t with hs
  have hBopen : IsOpen (B : Set (AdGL k N)) := by
    have := QuotientGroup.isOpenMap_coe (N := Z) _ hopen
    simpa [hB, Subgroup.coe_map] using this
  have hBcoe : (QuotientGroup.mk : GL (Fin N) k → AdGL k N) '' (H : Set (GL (Fin N) k)) = (B : Set (AdGL k N)) := by
    rw [hB, Subgroup.coe_map]; rfl
  have hdc : (QuotientGroup.mk : GL (Fin N) k → AdGL k N) ''
      {g : GL (Fin N) k | ∃ x ∈ (H : Set (GL (Fin N) k)), ∃ y ∈ (H : Set (GL (Fin N) k)), g = x * t * y} =
      {q : AdGL k N | ∃ x ∈ B, ∃ y ∈ B, q = x * s * y} := by
    ext q
    constructor
    · rintro ⟨_, ⟨x, hx, y, hy, rfl⟩, rfl⟩
      exact ⟨_, Subgroup.mem_map_of_mem _ hx, _, Subgroup.mem_map_of_mem _ hy, rfl⟩
    · rintro ⟨_, ⟨x, hx, rfl⟩, _, ⟨y, hy, rfl⟩, rfl⟩
      exact ⟨x * t * y, ⟨x, hx, y, hy, rfl⟩, rfl⟩
  rw [hBcoe, hdc, measure_doubleCoset μ B hBopen s (by rw [hI, hindex]; positivity), hI, hindex]
  push_cast
  rfl

end GlobalTheory.CompanionTheory.DoubleCosetVolume
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MulLeSqAddSq
section
noncomputable section

open NumberField IsDedekindDomain Matrix MeasureTheory
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC PositivityTheory.Rg.BcB PositivityTheory.Rg.BcB.D1 PositivityTheory.Rg.BcB.E PositivityTheory.Rg.BcB.E1
open scoped ENNReal

namespace GlobalTheory.CompanionTheory.LBoundProof

attribute [local instance] borelH

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {a b : ℕ}

theorem mul_le_sq_add_sq (p q : ℝ≥0∞) : p * q ≤ p ^ 2 + q ^ 2 := by
  rcases le_total p q with h | h
  · calc p * q ≤ q * q := by gcongr
      _ = q ^ 2 := (sq q).symm
      _ ≤ _ := le_add_self
  · calc p * q ≤ p * p := by gcongr
      _ = p ^ 2 := (sq p).symm
      _ ≤ _ := le_self_add

theorem lInt_eq {ι : Type} [Fintype ι] (D : Dom E a b) (k₁ k₂ : H E a b → ι → Hs (ι := ι) D) (τ : ℝ)
    (U : Hs (ι := ι) D →L[ℂ] Hs (ι := ι) D) :
    lInt D k₁ k₂ τ U = (cutSet E a τ ×ˢ cutSet E b τ).indicator
      (fun x => ∑ i, inner ℂ (k₁ x i) (U (k₂ x i))) := by
  funext x
  by_cases h1 : x.1 ∈ cutSet E a τ <;> by_cases h2 : x.2 ∈ cutSet E b τ <;>
    simp [lInt, chiT, h1, h2, Set.indicator, Set.mem_prod]

theorem enorm_inner_le {ι : Type} (D : Dom E a b) (U : Hs (ι := ι) D →L[ℂ] Hs (ι := ι) D) [Fintype ι]
    (u v : Hs (ι := ι) D) (C : ℝ≥0∞) (hu : ‖u‖ₑ ^ 2 ≤ C) (hv : ‖v‖ₑ ^ 2 ≤ C) :
    ‖inner ℂ u (U v)‖ₑ ≤ ‖U‖ₑ * (2 * C) := by
  have h1 : ‖inner ℂ u (U v)‖ₑ ≤ ‖u‖ₑ * ‖U v‖ₑ := by
    simp only [eNorm_eq_nnNorm]
    exact_mod_cast nnNorm_inner_le_nnNorm (𝕜 := ℂ) u (U v)
  calc ‖inner ℂ u (U v)‖ₑ ≤ ‖u‖ₑ * ‖U v‖ₑ := h1
    _ ≤ ‖u‖ₑ * (‖U‖ₑ * ‖v‖ₑ) := by gcongr; exact U.le_opENorm v
    _ = ‖U‖ₑ * (‖u‖ₑ * ‖v‖ₑ) := by ring
    _ ≤ ‖U‖ₑ * (‖u‖ₑ ^ 2 + ‖v‖ₑ ^ 2) := by gcongr; exact mul_le_sq_add_sq _ _
    _ ≤ ‖U‖ₑ * (C + C) := by gcongr
    _ = ‖U‖ₑ * (2 * C) := by rw [two_mul]

theorem lBound_of : Mahler → CutCount → LBound := by
  intro hM hC E _ _ _ a b D ι _ k₁ k₂ C₀ Ω hcont hC₀ hΩ hnorm
  obtain ⟨C₁, N, hC₁, hcut⟩ := hC E a b D Ω hΩ
  refine ⟨2 * Fintype.card ι * C₀.toReal * C₁, N, fun τ hτ U => ?_⟩
  set S : Set (H E a b) := cutSet E a τ ×ˢ cutSet E b τ with hS
  have : BorelSpace (H E a b) := ⟨rfl⟩
  have hSm : MeasurableSet S := ((hM E a τ).1.prod (hM E b τ).1).measurableSet
  have hg : Continuous fun x => ∑ i, inner ℂ (k₁ x i) (U (k₂ x i)) :=
    continuous_finsetSum _ fun i _ => (hcont i).1.inner (U.continuous.comp (hcont i).2)
  have hmeas : AEStronglyMeasurable (lInt D k₁ k₂ τ U) D.ν := by
    rw [lInt_eq]
    exact hg.aestronglyMeasurable.indicator hSm
  set c : ℝ≥0∞ := Fintype.card ι * (‖U‖ₑ * (2 * C₀)) with hc
  have hcr : c = ENNReal.ofReal (Fintype.card ι * (‖U‖ * (2 * C₀.toReal))) := by
    rw [ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_natCast, ENNReal.ofReal_mul (norm_nonneg _),
      ofReal_norm, ENNReal.ofReal_mul (by norm_num), ENNReal.ofReal_toReal hC₀, ENNReal.ofReal_ofNat]
  have hctop : c ≠ ⊤ := by rw [hcr]; exact ENNReal.ofReal_ne_top
  have hpt : ∀ x, ‖lInt D k₁ k₂ τ U x‖ₑ ≤ c * S.indicator (cnt (ratH E a b) Ω) x := by
    intro x
    rw [lInt_eq]
    by_cases hx : x ∈ S
    · rw [Set.indicator_of_mem hx, Set.indicator_of_mem hx]
      calc ‖∑ i, inner ℂ (k₁ x i) (U (k₂ x i))‖ₑ ≤ ∑ i, ‖inner ℂ (k₁ x i) (U (k₂ x i))‖ₑ :=
            eNorm_sum_le _ _
        _ ≤ ∑ _i : ι, ‖U‖ₑ * (2 * (C₀ * cnt (ratH E a b) Ω x)) :=
            Finset.sum_le_sum fun i _ => enorm_inner_le D U _ _ _ (hnorm x i).1 (hnorm x i).2
        _ = c * cnt (ratH E a b) Ω x := by
            simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, hc]
            ring
    · rw [Set.indicator_of_notMem hx, Set.indicator_of_notMem hx]
      simp
  have hA : 0 ≤ 2 * Fintype.card ι * C₀.toReal * C₁ * (1 + τ) ^ N * ‖U‖ := by positivity
  have hle : ∫⁻ x, ‖lInt D k₁ k₂ τ U x‖ₑ ∂D.ν ≤
      ENNReal.ofReal (2 * Fintype.card ι * C₀.toReal * C₁ * (1 + τ) ^ N * ‖U‖) := by
    calc ∫⁻ x, ‖lInt D k₁ k₂ τ U x‖ₑ ∂D.ν ≤ ∫⁻ x, c * S.indicator (cnt (ratH E a b) Ω) x ∂D.ν :=
          lintegral_mono hpt
      _ = c * ∫⁻ x, S.indicator (cnt (ratH E a b) Ω) x ∂D.ν := lintegral_const_mul' _ _ hctop
      _ ≤ c * ENNReal.ofReal (C₁ * (1 + τ) ^ N) := by gcongr; exact hcut τ hτ
      _ = ENNReal.ofReal (2 * Fintype.card ι * C₀.toReal * C₁ * (1 + τ) ^ N * ‖U‖) := by
          rw [hcr, ← ENNReal.ofReal_mul (by positivity)]
          congr 1
          ring
  refine ⟨⟨hmeas, hle.trans_lt ENNReal.ofReal_lt_top⟩, ?_⟩
  rw [integral_norm_eq_lintegral_eNorm hmeas]
  exact ENNReal.toReal_le_of_le_ofReal hA hle

end GlobalTheory.CompanionTheory.LBoundProof

end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.OneMemGoodCT
section
noncomputable section

open NumberField GlobalTheory.CuspRep MeasureTheory PositivityTheory.Affgl

namespace GlobalTheory.CompanionTheory.CTFin

abbrev lev (R : Type) [CommRing R] (r s : ℕ) : GL (Fin r) R × GL (Fin s) R →* GL (Fin (r + s)) R :=
  GlobalTheory.SmGL.emb₂ R (GlobalTheory.SmGL.stdSum (rfl : r + s = r + s))

variable {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] {r s : ℕ}

def goodCT (L : Subgroup (GL (Fin (r + s)) (Af E))) {W : Type} [AddCommGroup W] [Module ℂ W]
    (ρ : Representation ℂ (Kinf E (r + s)) W) (J : Set (Module.End ℂ (Sm E (r + s)))) :
    Submodule ℂ (Sm E (r + s)) where
  carrier := {F | (∀ (x : BlockIx (r + s) r → Ad E) (g : GA E (r + s)), F.1 (unip x * g) = F.1 g) ∧
    (∀ (γ : GL (Fin r) E × GL (Fin s) E) (g : GA E (r + s)),
      F.1 (lev (Ad E) r s (ratGL E r γ.1, ratGL E s γ.2) * g) = F.1 g) ∧
    (∀ k ∈ L, finRep E (r + s) k F = F) ∧
    (∀ g : GA E (r + s), (fun k : Kinf E (r + s) => (cptRep E (r + s) k F).1 g) ∈ GlobalTheory.Published.AutFin.coeffSpan ρ) ∧
    (∀ g : GA E (r + s), ∃ (C : ℝ) (N : ℕ), ∀ y, ‖F.1 (g * infGL E (r + s) y)‖ ≤ C * height y ^ N) ∧
    ∀ z ∈ J, z F = 0}
  add_mem' := by
    rintro F G ⟨a1, a2, a3, a4, a5, a6⟩ ⟨b1, b2, b3, b4, b5, b6⟩
    refine ⟨fun x g => ?_, fun γ g => ?_, fun k hk => ?_, fun g => ?_, fun g => ?_, fun z hz => ?_⟩
    · change F.1 _ + G.1 _ = F.1 _ + G.1 _
      rw [a1, b1]
    · change F.1 _ + G.1 _ = F.1 _ + G.1 _
      rw [a2, b2]
    · rw [map_add (f := _), a3 k hk, b3 k hk]
    · convert (GlobalTheory.Published.AutFin.coeffSpan ρ).add_mem (a4 g) (b4 g) using 1
      funext k
      simp
    · obtain ⟨C, N, h⟩ := a5 g
      obtain ⟨C', N', h'⟩ := b5 g
      refine ⟨|C| + |C'|, N + N', fun y => ?_⟩
      have hy := one_le_height y
      have e1 : height y ^ N ≤ height y ^ (N + N') := pow_le_pow_right₀ hy (by omega)
      have e2 : height y ^ N' ≤ height y ^ (N + N') := pow_le_pow_right₀ hy (by omega)
      have p1 : 0 ≤ height y ^ N := by positivity
      have p2 : 0 ≤ height y ^ N' := by positivity
      change ‖F.1 _ + G.1 _‖ ≤ _
      refine (norm_add_le _ _).trans ?_
      rw [add_mul]
      refine add_le_add ((h y).trans ?_) ((h' y).trans ?_)
      · exact (mul_le_mul_of_nonneg_right (le_abs_self C) p1).trans
          (mul_le_mul_of_nonneg_left e1 (abs_nonneg _))
      · exact (mul_le_mul_of_nonneg_right (le_abs_self C') p2).trans
          (mul_le_mul_of_nonneg_left e2 (abs_nonneg _))
    · rw [map_add (f := _), a6 z hz, b6 z hz, add_zero]
  zero_mem' := by
    refine ⟨fun x g => rfl, fun γ g => rfl, fun k _ => map_zero _, fun g => ?_, fun g => ⟨0, 0, fun y => ?_⟩,
      fun z _ => map_zero z⟩
    · convert (GlobalTheory.Published.AutFin.coeffSpan ρ).zero_mem using 1
      funext k
      simp
    · simp
  smul_mem' := by
    rintro c F ⟨a1, a2, a3, a4, a5, a6⟩
    refine ⟨fun x g => ?_, fun γ g => ?_, fun k hk => ?_, fun g => ?_, fun g => ?_, fun z hz => ?_⟩
    · change c • F.1 _ = c • F.1 _
      rw [a1]
    · change c • F.1 _ = c • F.1 _
      rw [a2]
    · rw [map_smul, a3 k hk]
    · convert (GlobalTheory.Published.AutFin.coeffSpan ρ).smul_mem c (a4 g) using 1
      funext k
      simp
    · obtain ⟨C, N, h⟩ := a5 g
      refine ⟨‖c‖ * C, N, fun y => ?_⟩
      change ‖c • F.1 _‖ ≤ _
      rw [norm_smul, mul_assoc]
      exact mul_le_mul_of_nonneg_left (h y) (norm_nonneg _)
    · rw [map_smul, a6 z hz, smul_zero]

end GlobalTheory.CompanionTheory.CTFin

end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TraceSingleMulSingle
section
open Matrix MvPolynomial

noncomputable section

namespace GlobalTheory.CompanionTheory.TopClass

open PositivityTheory.RgTw

variable {n : ℕ}

theorem trace_single_mul_single (a b c e : Fin n) :
    trace (Matrix.single a b (1 : ℂ) * Matrix.single c e 1) = if a = e ∧ b = c then 1 else 0 := by
  simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.single_apply]
  by_cases h1 : a = e <;> by_cases h2 : b = c <;> simp [h1, h2, ite_and, Finset.sum_ite_eq', eq_comm]

theorem sqrt_two_inv_sq : ((Real.sqrt 2)⁻¹ : ℂ) * ((Real.sqrt 2)⁻¹ : ℂ) = 1 / 2 := by
  rw [← mul_inv, ← Complex.ofReal_mul, Real.mul_self_sqrt (by norm_num)]
  norm_num

theorem trace_hb_mul_hb (p q : Fin n × Fin n) : trace (hb p * hb q) = if p = q then 1 else 0 := by
  obtain ⟨a, b⟩ := p
  obtain ⟨c, e⟩ := q
  have hs := sqrt_two_inv_sq
  simp only [hb]
  split_ifs with h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14 h15 h16 <;>
  simp only [Matrix.add_mul, Matrix.mul_add, Matrix.sub_mul, Matrix.mul_sub, Matrix.smul_mul, Matrix.mul_smul,
      trace_add, trace_sub, trace_smul, trace_single_mul_single, smul_eq_mul, Prod.mk.injEq] at * <;> (simp only [Fin.ext_iff, Fin.lt_iff_val_lt_val] at * ; split_ifs at * <;> (try omega)) <;>
  (generalize ((Real.sqrt 2 : ℝ) : ℂ)⁻¹ = s at hs ⊢
   have hs2 : s ^ 2 = 1 / 2 := by rw [sq]; exact hs
   first | ring1 | (ring_nf; simp only [Complex.I_sq, hs2]; ring_nf))

theorem hb_linInd : LinearIndependent ℂ (hb (n := n)) := by
  rw [Fintype.linearIndependent_iff]
  intro g hg q
  have h := congrArg (fun X => trace (X * hb q)) hg
  simpa [Finset.sum_mul, Matrix.trace_sum, Matrix.smul_mul, trace_smul, trace_hb_mul_hb] using h

def hbB (n : ℕ) : Module.Basis (Fin n × Fin n) ℂ (Mat n) :=
  basisOfLinearIndependentOfCardEqFinrank' hb hb_linInd (by simp [Module.finrank_matrix])

theorem hbB_apply (p : Fin n × Fin n) : hbB n p = hb p := by
  simp [hbB]

theorem hbB_repr (X : Mat n) (q : Fin n × Fin n) : (hbB n).repr X q = trace (X * hb q) := by
  conv_rhs => rw [← (hbB n).sum_repr X]
  simp [Finset.sum_mul, Matrix.trace_sum, Matrix.smul_mul, trace_smul, hbB_apply, trace_hb_mul_hb]

theorem det_of_trace (L : Mat n →ₗ[ℂ] Mat n) :
    (Matrix.of fun p q : Fin n × Fin n => trace (L (hb p) * hb q)).det = LinearMap.det L := by
  rw [← LinearMap.det_toMatrix (hbB n) L, ← Matrix.det_transpose (LinearMap.toMatrix (hbB n) (hbB n) L)]
  congr 1
  ext p q
  simp [LinearMap.toMatrix_apply, hbB_repr, hbB_apply]

end GlobalTheory.CompanionTheory.TopClass
end
end

