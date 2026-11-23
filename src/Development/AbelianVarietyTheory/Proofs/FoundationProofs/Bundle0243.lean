module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Foundations.NormSumPairRankZeroOfCurveCoordNorm
public import Formalism.PairingDivisors.StatementH
public import Formalism.LocalRingCardinality.RankBoundMonotoneInDimension
public import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.Bundle0009
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsTraceCompatibleTorusEmbeddingStandardTorus
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0225
public import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.IntMIffInt
public import Formalism.FrobeniusOrbits.FrobeniusOrbitsProofs.DiscrB
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0224
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0230
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.DerivationDenominatorsAndHostFieldSizes
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0218

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.OkLinearTorsionCorrespondenceMapsLattice
section
open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum GlobalTheory.ThetaConj
open scoped BigOperators

noncomputable section

namespace GlobalTheory.ThetaConj

theorem rationalLatticePoint_add {Λ : AddSubgroup ℂ} {x y : ℂ} (hx : InRationalLattice Λ x) (hy : InRationalLattice Λ y) : InRationalLattice Λ (x + y) := by
  obtain ⟨m, hm, h⟩ := hx
  obtain ⟨n, hn, h'⟩ := hy
  refine ⟨m * n, Nat.mul_pos hm hn, ?_⟩
  have : ((m * n : ℕ) : ℂ) * (x + y) = n • ((m : ℂ) * x) + m • ((n : ℂ) * y) := by
    simp only [nsmul_eq_mul]; push_cast; ring
  rw [this]
  exact add_mem (nsmul_mem h n) (nsmul_mem h' m)

theorem rationalLatticePoint_neg {Λ : AddSubgroup ℂ} {x : ℂ} (hx : InRationalLattice Λ x) : InRationalLattice Λ (-x) := by
  obtain ⟨m, hm, h⟩ := hx
  exact ⟨m, hm, by rw [mul_neg]; exact neg_mem h⟩

theorem rationalLatticePoint_div_natCast {Λ : AddSubgroup ℂ} {w : ℂ} (hw : w ∈ Λ) {m : ℕ} (hm : 0 < m) : InRationalLattice Λ (w / m) := by
  refine ⟨m, hm, ?_⟩
  have : (m : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hm.ne'
  rw [mul_div_cancel₀ _ this]; exact hw

theorem Good.embV_nsmul {D : D7} {T : Tor D} (h : Good D T) {N N' : ℕ} (k : ℕ)
    (A : Matrix (Fin N') (Fin N) D.host.E) : embV D T (k • A) = (k : ℂ) • embV D T A := by
  rw [Nat.cast_smul_eq_nsmul]
  exact map_nsmul (h.embHom N N') k A

theorem Good.embV_sum {D : D7} {T : Tor D} (h : Good D T) {N N' r : ℕ} (a : Fin r → D.host.K)
    (b : Fin r → Matrix (Fin N') (Fin N) D.host.E) :
    embV D T (∑ j, a j • b j) = ∑ j, D.host.φ₀ (a j : D.host.E) • embV D T (b j) := by
  have := map_sum (h.embHom N N') (fun j => a j • b j) Finset.univ
  refine this.trans (Finset.sum_congr rfl fun j _ => ?_)
  exact h.embV_smul _ _

theorem Good.smul_embV_mem {D : D7} {T : Tor D} (h : Good D T) {N N' : ℕ}
    {Y : Set (Matrix (Fin N') (Fin N) D.host.E)} {w : ℂ} (hw : w ∈ T.abelian₂)
    {y : Matrix (Fin N') (Fin N) D.host.E} (hy : y ∈ AddSubgroup.closure Y) :
    w • embV D T y ∈ LaS D T Y := by
  change w • h.embHom N N' y ∈ _
  induction hy using AddSubgroup.closure_induction with
  | mem x hx => exact AddSubgroup.subset_closure ⟨w, hw, x, hx, rfl⟩
  | zero => rw [map_zero, smul_zero]; exact zero_mem _
  | add x y _ _ hx hy => rw [map_add (f := _), smul_add]; exact add_mem hx hy
  | neg x _ hx => rw [map_neg, smul_neg]; exact neg_mem hx

theorem corr_lattice : ∀ (D : D7) (T T' : Tor D), Good D T → Good D T' → (∀ a : 𝓞 D.host.K, ∀ w ∈ T.abelian₂, D.host.φ₀ (((a : D.host.K) : D.host.E)) * w ∈ T.abelian₂) → ∀ (N N' r : ℕ) (b : Fin r → Matrix (Fin N') (Fin N) D.host.E), TaylorLogMetric.Orthonormal D b → ∀ (S : ℂ → ℂ → Prop), (∀ t, InRationalLattice T.abelian₂ t → ∃ t', S t t') → (∀ t t₁ t₂, S t t₁ → S t t₂ → t₁ - t₂ ∈ T'.abelian₂) → (∀ t t' u u', S t t' → S u u' → S (t + u) (t' + u')) → (∀ (a : 𝓞 D.host.K) t t', S t t' → S (D.host.φ₀ (((a : D.host.K) : D.host.E)) * t) (D.host.φ₀ (((a : D.host.K) : D.host.E)) * t')) → (∀ (m : ℕ) t t', S t t' → (m : ℂ) * t ∈ T.abelian₂ → (m : ℂ) * t' ∈ T'.abelian₂) → ∀ (n k : ℕ) (Y : Set (Matrix (Fin N') (Fin N) D.host.E)), 0 < n → 0 < k → k ∣ n → Comm D b k Y → (∀ x ∈ LaS D T Y, ∃ c c' : Fin r → ℂ, (∀ j, InRationalLattice T.abelian₂ (c j)) ∧ x = ∑ j, c j • embV D T (b j) ∧ (∀ j, S (c j / (n : ℂ)) (c' j / (n : ℂ))) ∧ ∑ j, c' j • embV D T' (b j) ∈ LaS D T' Y) ∧ ∀ c c' : Fin r → ℂ, (∀ j, S (c j / (n : ℂ)) (c' j / (n : ℂ))) → ∑ j, c j • embV D T (b j) ∈ LaS D T Y → ∑ j, c' j • embV D T' (b j) ∈ LaS D T' Y := by
  intro D T T' hT hT' hO N N' r b hb S hex huniq hadd hmul hint n k Y hn hk hkn hC
  have hn0 : (n : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hn.ne'
  have hk0 : (k : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hk.ne'
  have hS0 : S 0 0 := by
    obtain ⟨t', ht'⟩ := hex 0 ⟨1, one_pos, by simp⟩
    simpa using hmul 0 _ _ ht'
  have hneg : ∀ t t', S t t' → S (-t) (-t') := fun t t' h => by
    simpa using hmul (-1) _ _ h
  have first : ∀ x ∈ LaS D T Y, ∃ c c' : Fin r → ℂ, (∀ j, InRationalLattice T.abelian₂ (c j)) ∧
      x = ∑ j, c j • embV D T (b j) ∧ (∀ j, S (c j / (n : ℂ)) (c' j / (n : ℂ))) ∧
      ∑ j, c' j • embV D T' (b j) ∈ LaS D T' Y := by
    intro x hx
    induction hx using AddSubgroup.closure_induction with
    | mem x hx =>
      obtain ⟨w, hw, y, hy, rfl⟩ := hx
      obtain ⟨a, ha⟩ := hC.1 y hy
      obtain ⟨u', hu'⟩ := hex _ (rationalLatticePoint_div_natCast hw (Nat.mul_pos hn hk))
      have hnk : ((n * k : ℕ) : ℂ) * u' ∈ T'.abelian₂ := by
        refine hint _ _ _ hu' ?_
        rw [mul_div_cancel₀ _ (by push_cast; exact mul_ne_zero hn0 hk0)]; exact hw
      have e1 := hT.embV_sum (fun j => (a j : D.host.K)) b
      have e2 := hT'.embV_sum (fun j => (a j : D.host.K)) b
      rw [← ha, hT.embV_nsmul] at e1
      rw [← ha, hT'.embV_nsmul] at e2
      refine ⟨fun j => D.host.φ₀ ((a j : D.host.K) : D.host.E) * w / k,
        fun j => n * (D.host.φ₀ ((a j : D.host.K) : D.host.E) * u'),
        fun j => rationalLatticePoint_div_natCast (hO _ _ hw) hk, ?_, fun j => ?_, ?_⟩
      · have : w • embV D T y = (w / k) • ((k : ℂ) • embV D T y) := by
          rw [smul_smul, div_mul_cancel₀ _ hk0]
        rw [this, e1, Finset.smul_sum]
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [smul_smul]; congr 1; ring
      · have := hmul (a j) _ _ hu'
        convert this using 1
        · push_cast; field_simp
        · field_simp
      · have : ∑ j, ((n : ℂ) * (D.host.φ₀ ((a j : D.host.K) : D.host.E) * u')) • embV D T' (b j)
            = (((n * k : ℕ) : ℂ) * u') • embV D T' y := by
          have h2 : (((n * k : ℕ) : ℂ) * u') • embV D T' y
              = ((n : ℂ) * u') • ((k : ℂ) • embV D T' y) := by
            rw [smul_smul]; congr 1; push_cast; ring
          rw [h2, e2, Finset.smul_sum]
          refine Finset.sum_congr rfl fun j _ => ?_
          rw [smul_smul]; congr 1; ring
        rw [this]
        exact AddSubgroup.subset_closure ⟨_, hnk, y, hy, rfl⟩
    | zero =>
      refine ⟨0, 0, fun j => ⟨1, one_pos, by simp⟩, by simp, fun j => by simpa using hS0, ?_⟩
      simp
    | add x y _ _ hx hy =>
      obtain ⟨c, c', h1, h2, h3, h4⟩ := hx
      obtain ⟨d, d', g1, g2, g3, g4⟩ := hy
      refine ⟨c + d, c' + d', fun j => rationalLatticePoint_add (h1 j) (g1 j), ?_, fun j => ?_, ?_⟩
      · rw [h2, g2, ← Finset.sum_add_distrib]; simp only [Pi.add_apply, add_smul]
      · simp only [Pi.add_apply, add_div]; exact hadd _ _ _ _ (h3 j) (g3 j)
      · simp only [Pi.add_apply, add_smul, Finset.sum_add_distrib]; exact add_mem h4 g4
    | neg x _ hx =>
      obtain ⟨c, c', h1, h2, h3, h4⟩ := hx
      refine ⟨-c, -c', fun j => rationalLatticePoint_neg (h1 j), ?_, fun j => ?_, ?_⟩
      · rw [h2, ← Finset.sum_neg_distrib]; simp only [Pi.neg_apply, neg_smul]
      · simp only [Pi.neg_apply, neg_div]; exact hneg _ _ (h3 j)
      · simp only [Pi.neg_apply, neg_smul, Finset.sum_neg_distrib]; exact neg_mem h4
  refine ⟨first, fun c c' hS hc => ?_⟩
  obtain ⟨d, d', -, h2, h3, h4⟩ := first _ hc
  have hcd : c = d := by
    funext j
    rw [← hT.coordB_sum hb c j, h2, hT.coordB_sum hb]
  subst hcd
  obtain ⟨m, hm⟩ := hkn
  have key : ∀ j, (c' j - d' j) • embV D T' (b j) ∈ LaS D T' Y := fun j => by
    have h5 := nsmul_mem (huniq _ _ _ (hS j) (h3 j)) m
    have h6 := hT'.smul_embV_mem h5 (hC.2 j)
    rw [hT'.embV_nsmul, smul_smul] at h6
    convert h6 using 2
    have hm' : (n : ℂ) = k * m := by rw [hm]; push_cast; rfl
    rw [nsmul_eq_mul, ← sub_div, mul_right_comm, mul_comm (m : ℂ), ← hm', mul_div_cancel₀ _ hn0]
  have : ∑ j, c' j • embV D T' (b j)
      = ∑ j, d' j • embV D T' (b j) + ∑ j, (c' j - d' j) • embV D T' (b j) := by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [← add_smul]; congr 1; ring
  rw [this]
  exact add_mem h4 (sum_mem fun j _ => key j)

end GlobalTheory.ThetaConj
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.SetIntegralCharImEqZero
section
open Complex MeasureTheory GlobalTheory.UnitaryTheta
open scoped BigOperators ComplexConjugate Real Classical Pointwise

namespace GlobalTheory.UnitaryTheta

theorem setIntegral_mul_char_eq_zero {V : Type} [NormedAddCommGroup V] [MeasurableSpace V] [BorelSpace V]
    [SecondCountableTopology V]
    (μ : Measure V) [μ.IsAddHaarMeasure] (Λ : AddSubgroup V) [Countable Λ] (Fd : Set V)
    (hF : IsAddFundamentalDomain Λ Fd μ) (f : V → ℂ) (hf : ∀ x y, f (x + y) = f x * f y)
    (hΛ : ∀ y ∈ Λ, f y = 1) (t : V) (ht : f t = -1) : ∫ z in Fd, f z ∂μ = 0 := by
  have hq : MeasurePreserving (fun x => t + x) μ μ := measurePreserving_add_left μ t
  have hF' : IsAddFundamentalDomain Λ ((fun x => t + x) ⁻¹' Fd) μ :=
    hF.preimage_of_equiv hq.quasiMeasurePreserving (e := id) Function.bijective_id
      (fun g x => by simp [AddSubgroup.vadd_def, add_left_comm])
  have h1 : ∫ z in (fun x => t + x) ⁻¹' Fd, f z ∂μ = ∫ z in Fd, f z ∂μ :=
    hF'.setIntegral_eq hF (fun g x => by simp [AddSubgroup.vadd_def, hf, hΛ g g.2])
  have h2 : ∫ z in (fun x => t + x) ⁻¹' Fd, f (t + z) ∂μ = ∫ z in Fd, f z ∂μ :=
    hq.setIntegral_preimage_emb (measurableEmbedding_addLeft t) f Fd
  have h3 : ∫ z in (fun x => t + x) ⁻¹' Fd, f (t + z) ∂μ = - ∫ z in Fd, f z ∂μ := by
    simp only [hf, ht, neg_one_mul, integral_neg, h1]
  linear_combination (h3 - h2) / 2

theorem setIntegral_char_im_eq_zero :
    ∀ (V : Type) [NormedAddCommGroup V] [NormedSpace ℂ V] [FiniteDimensional ℂ V] [MeasurableSpace V] [BorelSpace V] (μ : Measure V) [μ.IsAddHaarMeasure] (H : Sesq V), IsPosHerm H → ∀ (Λ : AddSubgroup V) [Countable Λ] (Fd : Set V), IsAddFundamentalDomain Λ Fd μ → ∀ v : V, v ≠ 0 → (∀ y ∈ Λ, ∃ m : ℤ, (H v y).im = m) → ∫ z in Fd, cexp (2 * π * I * ((H v z).im : ℂ)) ∂μ = 0 := by
  intro V _ _ _ _ _ μ _ H hH Λ _ Fd hF v hv hint
  haveI : ProperSpace V := FiniteDimensional.proper ℂ V
  have hpos := hH.2 v hv
  set r : ℝ := (H v v).re with hr
  refine setIntegral_mul_char_eq_zero μ Λ Fd hF (fun z => cexp (2 * π * I * ((H v z).im : ℂ)))
    (fun x y => ?_) (fun y hy => ?_) (((-(1 / (2 * r)) : ℝ) * I : ℂ) • v) ?_
  · simp only [map_add (f := _), add_im, ofReal_add, mul_add, Complex.exp_add]
  · obtain ⟨m, hm⟩ := hint y hy
    simp only [hm, ofReal_intCast]
    rw [mul_comm]
    exact Complex.exp_int_mul_two_pi_mul_I m
  · have e : (H v (((-(1 / (2 * r)) : ℝ) * I : ℂ) • v)).im = 1 / 2 := by
      rw [LinearMap.map_smulₛₗ, smul_eq_mul, map_mul, conj_ofReal, conj_I]
      simp only [mul_im, mul_re, ofReal_re, ofReal_im, neg_re, neg_im, I_re, I_im, ← hr]
      field_simp
      ring
    simp only [e]
    rw [← Complex.exp_pi_mul_I]
    congr 1
    push_cast
    ring

end GlobalTheory.UnitaryTheta
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.SigmaStarValueLeMeanSquareGenusOne
section
open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum
open scoped BigOperators
open MeasureTheory

noncomputable section

namespace GlobalTheory.GenusOneSup

theorem area_le (Λ : AddSubgroup ℂ) {w₁ w₂ : ℂ} (h₁ : w₁ ∈ Λ) (h₂ : w₂ ∈ Λ)
    (h : 0 < |((starRingEnd ℂ) w₁ * w₂).im|) : area Λ ≤ |((starRingEnd ℂ) w₁ * w₂).im| :=
  csInf_le ⟨0, fun _ ha => ha.1.le⟩ ⟨h, w₁, h₁, w₂, h₂, rfl⟩

theorem area_closure {w₁ w₂ : ℂ} (h : 0 < |((starRingEnd ℂ) w₁ * w₂).im|) :
    area (AddSubgroup.closure {w₁, w₂}) = |((starRingEnd ℂ) w₁ * w₂).im| := by
  have h₁ : w₁ ∈ AddSubgroup.closure ({w₁, w₂} : Set ℂ) := AddSubgroup.subset_closure (by simp)
  have h₂ : w₂ ∈ AddSubgroup.closure ({w₁, w₂} : Set ℂ) := AddSubgroup.subset_closure (by simp)
  refine le_antisymm (area_le _ h₁ h₂ h) (le_csInf ⟨_, h, w₁, h₁, w₂, h₂, rfl⟩ ?_)
  rintro a ⟨ha, x, hx, y, hy, rfl⟩
  obtain ⟨m, n, rfl⟩ := AddSubgroup.mem_closure_pair.1 hx
  obtain ⟨m', n', rfl⟩ := AddSubgroup.mem_closure_pair.1 hy
  have e : ((starRingEnd ℂ) (m • w₁ + n • w₂) * (m' • w₁ + n' • w₂)).im =
      ((m * n' - n * m' : ℤ) : ℝ) * ((starRingEnd ℂ) w₁ * w₂).im := by
    simp [Complex.mul_im]
    ring
  rw [e, abs_mul] at ha ⊢
  have hk : (m * n' - n * m' : ℤ) ≠ 0 := by
    intro h0
    rw [h0] at ha
    simp at ha
  have : (1 : ℝ) ≤ |((m * n' - n * m' : ℤ) : ℝ)| := by
    rw [← Int.cast_abs]
    exact_mod_cast Int.one_le_abs hk
  nlinarith

theorem exists_domain {w₁ w₂ : ℂ} (hli : LinearIndependent ℝ ![w₁, w₂]) :
    ∃ F : Set ℂ, IsAddFundamentalDomain (AddSubgroup.closure ({w₁, w₂} : Set ℂ)) F volume ∧
      Bornology.IsBounded F ∧ 0 < |((starRingEnd ℂ) w₁ * w₂).im| ∧
      volume F = ENNReal.ofReal |((starRingEnd ℂ) w₁ * w₂).im| := by
  let b : Module.Basis (Fin 2) ℝ ℂ := basisOfLinearIndependentOfCardEqFinrank hli (by simp)
  have hb : ⇑b = ![w₁, w₂] := coe_basisOfLinearIndependentOfCardEqFinrank _ _
  have hdet : Complex.basisOneI.det b = ((starRingEnd ℂ) w₁ * w₂).im := by
    rw [Module.Basis.det_apply, Matrix.det_fin_two]
    simp [Module.Basis.toMatrix_apply, hb, Complex.mul_im]
    ring
  have hspan : (Submodule.span ℤ (Set.range b)).toAddSubgroup = AddSubgroup.closure ({w₁, w₂} : Set ℂ) := by
    rw [Submodule.span_int_eq_addSubgroupClosure, hb]
    congr 1
    simp [Set.pair_comm]
  refine ⟨ZSpan.fundamentalDomain b, ?_, ZSpan.fundamentalDomain_isBounded b, ?_, ?_⟩
  · rw [← hspan]; exact ZSpan.isAddFundamentalDomain' b volume
  · rw [← hdet]; exact abs_pos.2 (Complex.basisOneI.isUnit_det b).ne_zero
  · rw [ZSpan.measure_fundamentalDomain b volume Complex.basisOneI, hdet,
      measure_congr (ZSpan.fundamentalDomain_ae_parallelepiped _ _), ← Complex.toBasis_orthonormalBasisOneI]
    have := Complex.orthonormalBasisOneI.volume_parallelepiped
    simp only [OrthonormalBasis.coe_toBasis, this, mul_one]

def lineIso : EuclideanSpace ℂ Unit ≃ₗᵢ[ℝ] ℂ where
  toFun x := x ()
  invFun z := WithLp.toLp 2 (fun _ => z)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  left_inv _ := rfl
  right_inv _ := rfl
  norm_map' x := by
    show ‖x ()‖ = ‖x‖
    simp [EuclideanSpace.norm_eq]

theorem sup_le_mean (Λ : AddSubgroup ℂ) (a v : ℝ) (F : Set ℂ) (g : ℂ → ℂ) (ha : 0 < a) (hv : 1 ≤ v)
    (hmin : ∀ x ∈ Λ, x ≠ 0 → a / v ≤ ‖x‖ ^ 2) (hF : IsAddFundamentalDomain Λ F volume)
    (hvol : volume F = ENNReal.ofReal a) (hg : Differentiable ℂ g)
    (hper : ∀ x ∈ Λ, ∀ z, ‖g (z + x)‖ ^ 2 * Real.exp (-Real.pi * ‖z + x‖ ^ 2 / a) =
      ‖g z‖ ^ 2 * Real.exp (-Real.pi * ‖z‖ ^ 2 / a))
    (hint : IntegrableOn (fun z => ‖g z‖ ^ 2 * Real.exp (-Real.pi * ‖z‖ ^ 2 / a)) F) (z : ℂ) :
    ‖g z‖ ^ 2 * Real.exp (-Real.pi * ‖z‖ ^ 2 / a) ≤
      3 * (2 * v + 1) * (a⁻¹ * ∫ z in F, ‖g z‖ ^ 2 * Real.exp (-Real.pi * ‖z‖ ^ 2 / a)) := by
  set s : ℝ := Real.sqrt a with hs
  have hs0 : 0 < s := Real.sqrt_pos.2 ha
  have hs2 : s ^ 2 = a := Real.sq_sqrt ha.le
  let φ : EuclideanSpace ℂ Unit ≃L[ℝ] ℂ :=
    lineIso.toContinuousLinearEquiv.trans (ContinuousLinearEquiv.smulLeft (Units.mk0 s hs0.ne'))
  have hφ : ∀ x, φ x = s • lineIso x := fun _ => rfl
  have hn : ∀ x, ‖φ x‖ ^ 2 = a * ‖x‖ ^ 2 := fun x => by
    rw [hφ, norm_smul, lineIso.norm_map, mul_pow, Real.norm_eq_abs, sq_abs, hs2]
  have hw : ∀ x, -Real.pi * ‖x‖ ^ 2 = -Real.pi * ‖φ x‖ ^ 2 / a := fun x => by
    rw [hn]; field_simp
  have hmp : MeasurePreserving φ volume (ENNReal.ofReal a⁻¹ • (volume : Measure ℂ)) := by
    have h1 : MeasurePreserving (fun z : ℂ => s • z) volume (ENNReal.ofReal a⁻¹ • (volume : Measure ℂ)) := by
      refine ⟨measurable_const_smul s, ?_⟩
      rw [Measure.map_addHaar_smul volume hs0.ne', Complex.finrank_real_complex, hs2,
        abs_of_pos (inv_pos.2 ha)]
    exact h1.comp lineIso.measurePreserving
  have hemb : MeasurableEmbedding φ := φ.toHomeomorph.measurableEmbedding
  let A : AddSubgroup (EuclideanSpace ℂ Unit) := Λ.comap (φ : EuclideanSpace ℂ Unit →+ ℂ)
  have hA : ∀ x, x ∈ A ↔ φ x ∈ Λ := fun _ => Iff.rfl
  have hF' : IsAddFundamentalDomain A (φ ⁻¹' F) volume := by
    refine hF.preimage_of_equiv (f := φ) (e := fun y : Λ => (⟨φ.symm y, (hA _).2 (by simp)⟩ : A))
      ⟨hmp.measurable.aemeasurable, ?_⟩ ⟨?_, ?_⟩ ?_
    · rw [hmp.map_eq]; exact Measure.smul_absolutelyContinuous
    · intro x y h
      exact Subtype.ext (φ.symm.injective (congrArg Subtype.val h))
    · intro x
      exact ⟨⟨φ x, x.2⟩, Subtype.ext (by simp)⟩
    · intro y x
      show φ (φ.symm y + x) = (y : ℂ) + φ x
      simp
  have hvol' : volume (φ ⁻¹' F) = 1 := by
    rw [hmp.measure_preimage_emb hemb, Measure.smul_apply, hvol, smul_eq_mul,
      ← ENNReal.ofReal_mul (inv_pos.2 ha).le, inv_mul_cancel₀ ha.ne', ENNReal.ofReal_one]
  have hd : Differentiable ℂ (fun x : EuclideanSpace ℂ Unit => g (φ x)) := by
    have : Differentiable ℂ (fun x : EuclideanSpace ℂ Unit => (s : ℂ) * x ()) := by fun_prop
    exact hg.comp this
  have key := GlobalTheory.ThetaSupBall.sup_le_mean_square Unit A v (φ ⁻¹' F) (fun x => g (φ x)) hv ?_ hF' hvol' hd ?_ ?_ (φ.symm z)
  · simp only [hw, Fintype.card_unit, Nat.cast_one, mul_one, pow_one, ContinuousLinearEquiv.apply_symm_apply] at key
    rw [hmp.setIntegral_preimage_emb hemb (fun z => ‖g z‖ ^ 2 * Real.exp (-Real.pi * ‖z‖ ^ 2 / a)),
      Measure.restrict_smul, integral_smul_measure, ENNReal.toReal_ofReal (inv_pos.2 ha).le, smul_eq_mul] at key
    exact key
  · intro x hx hx0
    have := hmin (φ x) hx (by simpa using hx0)
    rw [hn, div_eq_mul_one_div] at this
    exact le_of_mul_le_mul_left this ha
  · intro x hx y
    simp only [hw, map_add (f := _)]
    exact hper _ hx _
  · simp only [hw]
    refine (hmp.integrableOn_comp_preimage hemb
      (f := fun z => ‖g z‖ ^ 2 * Real.exp (-Real.pi * ‖z‖ ^ 2 / a))).2 ?_
    unfold IntegrableOn
    rw [Measure.restrict_smul]
    exact Integrable.smul_measure hint ENNReal.ofReal_ne_top

theorem thetaTranslation_weighted_normSq (Λ : AddSubgroup ℂ) (t z : ℂ) (g : ℂ → ℂ) :
    ‖U1 Λ t g z‖ ^ 2 * Real.exp (-Real.pi * ‖z‖ ^ 2 / area Λ) =
      ‖g (z + t)‖ ^ 2 * Real.exp (-Real.pi * ‖z + t‖ ^ 2 / area Λ) := by
  unfold U1
  rw [norm_mul, mul_pow, Complex.norm_exp, mul_assoc, ← Real.exp_nat_mul, ← Real.exp_add]
  congr 2
  have e : (2 * (area Λ : ℂ)) = ((2 * area Λ : ℝ) : ℂ) := by push_cast; ring
  rw [e, Complex.sub_re, Complex.div_ofReal_re, Complex.div_ofReal_re, ← Complex.normSq_eq_norm_sq,
    ← Complex.normSq_eq_norm_sq, Complex.normSq_apply, Complex.normSq_apply]
  simp
  ring

theorem lattice_sup (Λ : AddSubgroup ℂ)
    (hΛ : ∃ w₁ w₂ : ℂ, LinearIndependent ℝ ![w₁, w₂] ∧ Λ = AddSubgroup.closure {w₁, w₂})
    (v : ℝ) (hv : 1 ≤ v) (hmin : ∀ x ∈ Λ, x ≠ 0 → area Λ / v ≤ ‖x‖ ^ 2) (t : ℂ) :
    ‖U1 Λ t (sgStar Λ) 0‖ ^ 2 ≤ 3 * (2 * v + 1) * nrm1Sq Λ (sgStar Λ) := by
  obtain ⟨⟨hd, -, -, hU⟩, -⟩ := GlobalTheory.OddTheta.sgStar_laws Λ hΛ
  obtain ⟨w₁, w₂, hli, rfl⟩ := hΛ
  obtain ⟨F, hF, hb, hpos, hvol⟩ := exists_domain hli
  have har := area_closure hpos
  rw [← har] at hpos hvol
  set Λ : AddSubgroup ℂ := AddSubgroup.closure {w₁, w₂} with hΛ
  have hper : ∀ x ∈ Λ, ∀ z, ‖sgStar Λ (z + x)‖ ^ 2 * Real.exp (-Real.pi * ‖z + x‖ ^ 2 / area Λ) =
      ‖sgStar Λ z‖ ^ 2 * Real.exp (-Real.pi * ‖z‖ ^ 2 / area Λ) := by
    intro x hx z
    rw [← thetaTranslation_weighted_normSq, hU x hx, norm_mul]
    split_ifs <;> simp
  have hc : Continuous fun z => ‖sgStar Λ z‖ ^ 2 * Real.exp (-Real.pi * ‖z‖ ^ 2 / area Λ) := by
    have := hd.continuous
    fun_prop
  have hint : IntegrableOn (fun z => ‖sgStar Λ z‖ ^ 2 * Real.exp (-Real.pi * ‖z‖ ^ 2 / area Λ)) F :=
    (hc.continuousOn.integrableOn_compact hb.isCompact_closure).mono_set subset_closure
  have key := sup_le_mean Λ (area Λ) v F (sgStar Λ) hpos hv hmin hF hvol hd hper hint t
  have h0 := thetaTranslation_weighted_normSq Λ t 0 (sgStar Λ)
  simp only [norm_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, mul_zero, zero_div,
    Real.exp_zero, mul_one, zero_add] at h0
  rw [h0]
  refine key.trans (le_of_eq ?_)
  congr 1
  have hF' := Classical.epsilon_spec (p := fun Fd : Set ℂ => IsAddFundamentalDomain Λ Fd volume) ⟨F, hF⟩
  have : Countable Λ := by
    have : (Λ : Set ℂ) ⊆ Set.range (fun p : ℤ × ℤ => p.1 • w₁ + p.2 • w₂) := by
      intro x hx
      obtain ⟨m, n, rfl⟩ := AddSubgroup.mem_closure_pair.1 hx
      exact ⟨(m, n), rfl⟩
    exact ((Set.countable_range _).mono this).to_subtype
  have : VAddInvariantMeasure Λ ℂ volume := ⟨fun γ s _ => measure_preimage_add volume (γ : ℂ) s⟩
  unfold nrm1Sq
  simp only
  rw [setAverage_eq, measureReal_def, hF'.measure_eq hF, hF'.setIntegral_eq hF, hvol,
    ENNReal.toReal_ofReal hpos.le, smul_eq_mul]
  intro γ z
  have := hper γ γ.2 z
  rw [add_comm] at this
  exact this

theorem value_le_mean_square : ∀ (D : D7), admG1 D → ∀ (cc : Ideal (𝓞 D.host.K)) (δ : ℂ), Crv D cc δ → ∀ t, ‖U1 (lamOf D cc δ) t (sgStar (lamOf D cc δ)) 0‖ ^ 2 ≤ 3 * (2 * D.host.rdE + 1) * nrm1Sq (lamOf D cc δ) (sgStar (lamOf D cc δ)) := by
  intro D hD cc δ hc t
  obtain ⟨hΛ, -, -, -, hst⟩ := GlobalTheory.CurveLattice.lattice_of_curve D hD cc δ hc
  obtain ⟨-, hlog, hrd, -⟩ := GlobalTheory.NormSum.letters_and_sizes D hD
  refine lattice_sup _ hΛ _ hrd ?_ t
  intro x hx hx0
  have hd : (0 : ℝ) < D.host.d := by exact_mod_cast D.host.hyp.2.1.pos
  have hsq := D.host.sqd_sq
  let β : D.host.K := ⟨D.host.sqd, IntermediateField.mem_adjoin_simple_self ℚ _⟩
  have hβ : β ^ 2 = -(D.host.d : D.host.K) := Subtype.ext (by simpa [β] using hsq)
  have hi : IsIntegral ℤ β := by
    refine IsIntegral.of_pow (n := 2) two_pos ?_
    rw [hβ]
    exact (isIntegral_natCast _).neg
  have hm := hst ⟨β, hi⟩ x hx
  set c : ℂ := D.host.φ₀ (D.host.sqd) with hcdef
  have hm' : c * x ∈ lamOf D cc δ := hm
  have hc2 : c ^ 2 = -(D.host.d : ℂ) := by
    rw [hcdef, ← map_pow, hsq]; simp
  have hre : c.re * c.re - c.im * c.im = -(D.host.d : ℝ) := by
    have := congrArg Complex.re hc2
    simpa [pow_two] using this
  have him : c.re * c.im = 0 := by
    have := congrArg Complex.im hc2
    simp [pow_two] at this
    linarith
  have hre0 : c.re = 0 := by
    rcases mul_eq_zero.1 him with h | h
    · exact h
    · rw [h] at hre; nlinarith [mul_self_nonneg c.re]
  have him2 : c.im ^ 2 = D.host.d := by rw [hre0] at hre; linarith
  have e : |((starRingEnd ℂ) x * (c * x)).im| = |c.im| * ‖x‖ ^ 2 := by
    have : ((starRingEnd ℂ) x * (c * x)).im = c.im * ‖x‖ ^ 2 := by
      rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply]
      simp
      ring
    rw [this, abs_mul, abs_of_nonneg (sq_nonneg ‖x‖)]
  have hx2 : 0 < ‖x‖ ^ 2 := by positivity
  have hci : 0 < |c.im| := abs_pos.2 (by intro h; rw [h] at him2; linarith)
  have hle := area_le _ hx hm' (by rw [e]; positivity)
  have hrd0 : 0 < D.host.rdE := by linarith
  have hdle : (D.host.d : ℝ) ≤ D.host.rdE ^ 2 := by
    rw [← Real.log_le_log_iff hd (by positivity), Real.log_pow]
    exact_mod_cast hlog
  have hcle : |c.im| ≤ D.host.rdE := abs_le_of_sq_le_sq' (by rw [him2]; exact hdle) hrd0.le |> abs_le.2
  rw [div_le_iff₀ hrd0]
  rw [e] at hle
  nlinarith

end GlobalTheory.GenusOneSup
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.SignedTranslationAddSelfDualLattice
section
open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum GlobalTheory.GalTheta
open scoped BigOperators

namespace GlobalTheory.GalTheta

theorem al_add (D : D7) (T : Tor D) (N N' : ℕ) (A : AddSubgroup (VC D N N'))
    (h1 : ∀ x ∈ A, ∀ y ∈ A, ∃ m : ℤ, (Hf D T x y).im = m) (h2 : ∀ x ∈ A, ∃ m : ℤ, qH D T x = m)
    (h3 : ∀ x ∈ A, w0 D • x ∈ A) : ∀ x ∈ A, ∀ y ∈ A, al D T (x + y) =
      al D T x * al D T y * Complex.exp (-(Real.pi : ℂ) * Complex.I * ((Hf D T x y).im : ℂ)) := by
  intro x hx y hy
  obtain ⟨a, ha⟩ := h2 x hx
  obtain ⟨c, hc⟩ := h2 y hy
  obtain ⟨b, hb⟩ := h1 x hx y hy
  obtain ⟨k, hk⟩ := h1 _ (h3 x hx) y hy
  have hal : ∀ z : VC D N N', ∀ m : ℤ, qH D T z = m → al D T z = (-1 : ℂ) ^ m := by
    intro z m hm
    have e : al D T z = (-1 : ℂ) ^ (round (qH D T z)) := rfl
    rw [e, hm, round_intCast]
  have hk' : Real.sqrt D.host.d * (Hf D T x y).re = 2 * k - b := by
    rw [Hf_smul_left] at hk
    rw [← hk, ← hb]
    simp [w0, Complex.mul_im]
    ring
  have hs : qH D T (x + y) = ((a + c + (2 * k - b) : ℤ) : ℝ) := by
    push_cast
    rw [← ha, ← hc, ← hk']
    simp only [qH, Hf_add_left, Hf_add_right, Complex.add_re, Hf_re_swap D T x y]
    ring
  have he : Complex.exp (-(Real.pi : ℂ) * Complex.I * ((Hf D T x y).im : ℂ)) = (-1 : ℂ) ^ (-b) := by
    rw [hb, ← Complex.exp_pi_mul_I, ← Complex.exp_int_mul]
    congr 1
    push_cast
    ring
  have hn : (-1 : ℂ) ≠ 0 := by norm_num
  rw [hal _ _ hs, hal _ _ ha, hal _ _ hc, he, sub_eq_add_neg, zpow_add₀ hn, zpow_add₀ hn, zpow_add₀ hn,
    zpow_mul]
  simp

end GlobalTheory.GalTheta
end

