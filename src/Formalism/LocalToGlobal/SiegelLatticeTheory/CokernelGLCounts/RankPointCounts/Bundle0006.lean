module

public import Mathlib
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.Bundle0003
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.Bundle0002
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.Bundle0005
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StrongApproximation.Bundle0001

@[expose] public section

-- bundled from Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.EmbSInjective
section
noncomputable section

open scoped Classical Pointwise
open MeasureTheory NumberField NumberField.mixedEmbedding

namespace Formalism.L2.SG.NGCut.SplitEmbedding

theorem pi_const_smul {ι : Type} [Fintype ι] (x : ℝ) :
    Measure.pi (fun _ : ι => ENNReal.ofReal x • (volume : Measure ℂ)) =
      ENNReal.ofReal x ^ Fintype.card ι • (volume : Measure (ι → ℂ)) := by
  have hsf : SigmaFinite (ENNReal.ofReal x • (volume : Measure ℂ)) :=
    (inferInstance : SigmaFinite (x.toNNReal • (volume : Measure ℂ)))
  refine Measure.pi_eq (fun t _ => ?_)
  rw [Measure.smul_apply, volume_pi, Measure.pi_pi, smul_eq_mul]
  simp only [Measure.smul_apply, smul_eq_mul, Finset.prod_mul_distrib, Finset.prod_const,
    Finset.card_univ]

def embS {K : Type} [Field K] {ι : Type} (φ : ι → (K →+* ℂ)) (s : ℂ) : K →+ (ι → ℂ) where
  toFun a := fun i => s * φ i a
  map_zero' := by funext i; simp
  map_add' a b := by funext i; simp [mul_add]

theorem covol_oneT (K : Type) [Field K] [NumberField K] [IsEmpty {w : InfinitePlace K // w.IsReal}]
    (ι : Type) [Fintype ι] (φ : ι → (K →+* ℂ)) (σ : ι ≃ {w : InfinitePlace K // w.IsComplex})
    (hφ : ∀ i, φ i = (σ i).1.embedding ∨ φ i = ComplexEmbedding.conjugate (σ i).1.embedding)
    (P : Type) [Fintype P] [DecidableEq P] (h : P → ℕ)
    (B : ∀ _ : P, (P → ι → ℂ) → (P → ι → ℂ) → (ι → ℂ))
    (hBm : ∀ p, Measurable (fun z : (P → ι → ℂ) × (P → ι → ℂ) => B p z.1 z.2))
    (hBd : ∀ p (x x' y y' : P → ι → ℂ), (∀ q, h q < h p → x q = x' q ∧ y q = y' q) → B p x y = B p x' y')
    (hB0 : ∀ p (x : P → ι → ℂ), B p x 0 = 0)
    (c : ℝ) (hc : 0 ≤ c) (I : P → (FractionalIdeal (nonZeroDivisors (𝓞 K)) K)ˣ) (Λ : P → AddSubgroup K)
    (hΛ : ∀ p, ∀ a ∈ Λ p, a ∈ (I p : FractionalIdeal (nonZeroDivisors (𝓞 K)) K)) (k : P → ℕ)
    (hk : ∀ p, (Λ p).relIndex
      (((I p : FractionalIdeal (nonZeroDivisors (𝓞 K)) K) : Submodule (𝓞 K) K).toAddSubgroup) = k p)
    (hk0 : ∀ p, k p ≠ 0) (s : P → ℂ) (hs : ∀ p, s p ≠ 0)
    (τ : ∀ _ : P, (P → ι → ℂ) → (ι → ℂ))
    (hτ : ∀ p (x x' : P → ι → ℂ), (∀ q, h q < h p → x q = x' q) → τ p x = τ p x')
    (hinv : ∀ γ : P → ι → ℂ, (∀ p, γ p - τ p γ ∈ (Λ p).map (embS φ (s p))) → ∃ γ' : P → ι → ℂ,
      (∀ p, γ' p - τ p γ' ∈ (Λ p).map (embS φ (s p))) ∧ ∀ g, mlaw B γ' (mlaw B γ g) = g ∧ mlaw B γ (mlaw B γ' g) = g)
    (Kset : Set (P → ι → ℂ)) (hK : MeasurableSet Kset)
    (hKd : ∀ g, ∃! γ : P → ι → ℂ, (∀ p, γ p - τ p γ ∈ (Λ p).map (embS φ (s p))) ∧ mlaw B γ g ∈ Kset) :
    (Measure.pi fun _ : P => Measure.pi fun _ : ι => ENNReal.ofReal c • (volume : Measure ℂ)) Kset =
      ∏ p, ENNReal.ofReal (c ^ Fintype.card ι * k p *
        (FractionalIdeal.absNorm (I p : FractionalIdeal (nonZeroDivisors (𝓞 K)) K) : ℝ) *
        2⁻¹ ^ Fintype.card ι * √|(discr K : ℝ)| * ‖s p‖ ^ (2 * Fintype.card ι)) := by
  have hsf : SigmaFinite (ENNReal.ofReal c ^ Fintype.card ι • (volume : Measure (ι → ℂ))) := by
    rw [show ENNReal.ofReal c ^ Fintype.card ι = ((c.toNNReal ^ Fintype.card ι : NNReal) : ENNReal) by
      rw [ENNReal.coe_pow]; rfl]
    exact (inferInstance : SigmaFinite ((c.toNNReal ^ Fintype.card ι) • (volume : Measure (ι → ℂ))))
  have hFex : ∀ p, ∃ F : Set (ι → ℂ), MeasurableSet F ∧
      ∀ v, ∃! a : Λ p, (fun i => s p * φ i a) + v ∈ F := fun p =>
    exists_fd K ι φ σ hφ (I p) (Λ p) (hΛ p) (by rw [hk p]; exact hk0 p) (s p) (hs p)
  choose F hFm hFd using hFex
  have hFd' : ∀ p (v : ι → ℂ), ∃! a : (Λ p).map (embS φ (s p)), (a : ι → ℂ) + v ∈ F p := by
    intro p v
    obtain ⟨a, ha, hu⟩ := hFd p v
    refine ⟨⟨embS φ (s p) a, AddSubgroup.mem_map_of_mem _ a.2⟩, ha, ?_⟩
    rintro ⟨b, hb⟩ hbF
    obtain ⟨a', ha', rfl⟩ := AddSubgroup.mem_map.mp hb
    have hae := hu ⟨a', ha'⟩ hbF
    subst hae
    rfl
  have hcK : Countable K := (Module.finBasis ℚ K).equivFun.injective.countable
  have hcA : ∀ p, Countable ((Λ p).map (embS φ (s p))) := fun p =>
    Function.Surjective.countable
      (f := fun a : Λ p => (⟨embS φ (s p) a, AddSubgroup.mem_map_of_mem _ a.2⟩ :
        (Λ p).map (embS φ (s p))))
      (by
        rintro ⟨b, hb⟩
        obtain ⟨a, ha, rfl⟩ := AddSubgroup.mem_map.mp hb
        exact ⟨⟨a, ha⟩, rfl⟩)
  rw [pi_const_smul c]
  rw [triFundT P (fun _ => ι → ℂ) (fun _ => ENNReal.ofReal c ^ Fintype.card ι • volume) h B hBm hBd
    hB0 τ hτ (fun p => (Λ p).map (embS φ (s p))) hinv F hFm hFd' Kset hK hKd]
  refine Finset.prod_congr rfl fun p _ => ?_
  rw [Measure.smul_apply, smul_eq_mul, idealCovolC K ι φ σ hφ (I p) (Λ p) (hΛ p) (k p) (hk p)
    (hk0 p) (s p) (hs p) (F p) (hFm p) (hFd p), ← ENNReal.ofReal_pow hc,
    ← ENNReal.ofReal_mul (by positivity)]
  congr 1
  ring

end Formalism.L2.SG.NGCut.SplitEmbedding
end
end

-- bundled from Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.IotaFIntMem
section
noncomputable section

open scoped Classical
open NumberField IsDedekindDomain ValuativeRel

namespace Formalism.L2.SG.Pf.PCountEx

section Clear

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {sig : E →ₐ[F] E}
  (A : ∀ p : HeightOneSpectrum (𝓞 F), Formalism.MainNotions.S.Loc.LocAt F E sig p)

theorem iotaF_int_mem (p : HeightOneSpectrum (𝓞 F)) (t : 𝓞 F) :
    (A p).ιF (algebraMap (𝓞 F) F t) ∈ (haveI := (A p).lf; 𝒪[(A p).Fp]) := by
  haveI := (A p).lf
  have h := ((A p).val (algebraMap (𝓞 F) F t) 1).2 (by simpa using p.valuation_le_one t)
  rw [map_one] at h
  rw [Valuation.mem_integer_iff]
  exact (Valuation.vle_one_iff (ValuativeRel.valuation (A p).Fp)).1 h

theorem clear_F (p : HeightOneSpectrum (𝓞 F)) (l : (A p).Fp) :
    ∃ t : 𝓞 F, t ≠ 0 ∧ (A p).ιF (algebraMap (𝓞 F) F t) * l ∈ (haveI := (A p).lf; 𝒪[(A p).Fp]) := by
  haveI := (A p).lf
  by_cases hl : l = 0
  · refine ⟨1, one_ne_zero, ?_⟩
    rw [hl, mul_zero]
    exact Subring.zero_mem _
  obtain ⟨π, hπp, hπ0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot p.ne_bot
  have hπv : p.valuation F (algebraMap (𝓞 F) F π) < 1 := by
    first
    | exact (p.valuation_lt_one_iff_mem π).2 hπp
    | exact (p.valuation_lt_one_iff_mem (K := F) π).2 hπp
  have hπF0 : algebraMap (𝓞 F) F π ≠ 0 := (map_ne_zero_iff _ (IsFractionRing.injective (𝓞 F) F)).2 hπ0
  obtain ⟨c, hc⟩ : ∃ c, c = (A p).ιF (algebraMap (𝓞 F) F π) := ⟨_, rfl⟩
  have hcint : c ∈ (ValuativeRel.valuation (A p).Fp).integer := by
    rw [hc]
    exact iotaF_int_mem A p π
  have hc0 : c ≠ 0 := by
    rw [hc]
    exact (map_ne_zero (A p).ιF).2 hπF0
  have hnot : -(c⁻¹) ∉ (ValuativeRel.valuation (A p).Fp).integer := by
    intro hmem
    rw [Valuation.mem_integer_iff] at hmem
    have h1 := (Valuation.vle_one_iff (ValuativeRel.valuation (A p).Fp)).2 hmem
    have h2 : -(c⁻¹) = (A p).ιF (-(algebraMap (𝓞 F) F π)⁻¹) := by rw [hc, map_neg, map_inv₀]
    rw [h2, ← map_one (A p).ιF, (A p).val, map_one] at h1
    have h3 : p.valuation F (algebraMap (𝓞 F) F π) * p.valuation F (-(algebraMap (𝓞 F) F π)⁻¹) = 1 := by
      rw [← map_mul, mul_neg, mul_inv_cancel₀ hπF0, Valuation.map_neg, map_one]
    have h4 : p.valuation F (algebraMap (𝓞 F) F π) * p.valuation F (-(algebraMap (𝓞 F) F π)⁻¹) ≤
        p.valuation F (algebraMap (𝓞 F) F π) * 1 := by
      first
      | gcongr
      | exact mul_le_mul_right' h1 _
      | exact mul_le_mul_of_nonneg_left h1 (zero_le _)
    rw [h3, mul_one] at h4
    exact absurd h4 (not_le.2 hπv)
  have hW : IsOpen ((fun z => (z * l - 1) * c⁻¹) ⁻¹'
      ((ValuativeRel.valuation (A p).Fp).integer : Set (A p).Fp)) :=
    Valuation.isOpen_integer.preimage (((continuous_mul_const l).sub continuous_const).mul continuous_const)
  have hne : ((fun z => (z * l - 1) * c⁻¹) ⁻¹'
      ((ValuativeRel.valuation (A p).Fp).integer : Set (A p).Fp)).Nonempty := by
    refine ⟨l⁻¹, ?_⟩
    show (l⁻¹ * l - 1) * c⁻¹ ∈ (ValuativeRel.valuation (A p).Fp).integer
    rw [inv_mul_cancel₀ hl, sub_self, zero_mul]
    exact Subring.zero_mem _
  obtain ⟨y, hy⟩ := (A p).dense.exists_mem_open hW hne
  have hy' : ((A p).ιF y * l - 1) * c⁻¹ ∈ (ValuativeRel.valuation (A p).Fp).integer := hy
  have hy1 : (A p).ιF y * l ∈ (ValuativeRel.valuation (A p).Fp).integer := by
    have e : (A p).ιF y * l = ((A p).ιF y * l - 1) * c⁻¹ * c + 1 := by
      rw [mul_assoc, inv_mul_cancel₀ hc0, mul_one, sub_add_cancel]
    rw [e]
    exact Subring.add_mem _ (Subring.mul_mem _ hy' hcint) (Subring.one_mem _)
  have hy0 : (A p).ιF y ≠ 0 := by
    intro h0
    rw [h0, zero_mul, zero_sub, neg_mul, one_mul] at hy'
    exact hnot hy'
  obtain ⟨a, b, hb, rfl⟩ := IsFractionRing.div_surjective (A := 𝓞 F) y
  have hb' : algebraMap (𝓞 F) F b ≠ 0 := IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors hb
  have hy0' : (A p).ιF (algebraMap (𝓞 F) F a / algebraMap (𝓞 F) F b) ≠ 0 := hy0
  refine ⟨a, ?_, ?_⟩
  · rintro rfl
    apply hy0'
    simp
  · have e : algebraMap (𝓞 F) F a =
        algebraMap (𝓞 F) F b * (algebraMap (𝓞 F) F a / algebraMap (𝓞 F) F b) := by
      field_simp
    rw [e, map_mul, mul_assoc]
    exact Subring.mul_mem _ (iotaF_int_mem A p b) hy1

private theorem ιF_mem_O_of_mem_integers (p : HeightOneSpectrum (𝓞 F)) (w : (A p).Fp)
    (hw : w ∈ (haveI := (A p).lf; 𝒪[(A p).Fp])) : algebraMap (A p).Fp (A p).Ep w ∈ (A p).O := by
  haveI := (A p).lf
  rw [(A p).O_def]
  have e : algebraMap (A p).Fp (A p).Ep w = algebraMap (𝒪[(A p).Fp]) (A p).Ep ⟨_, hw⟩ := rfl
  rw [e]
  exact isIntegral_algebraMap

private theorem algebraMap_ιF_mem_O (p : HeightOneSpectrum (𝓞 F)) (t : 𝓞 F) :
    algebraMap (A p).Fp (A p).Ep ((A p).ιF (algebraMap (𝓞 F) F t)) ∈ (A p).O := by
  haveI := (A p).lf
  rw [(A p).O_def]
  have hm := iotaF_int_mem A p t
  have e : algebraMap (A p).Fp (A p).Ep ((A p).ιF (algebraMap (𝓞 F) F t)) =
      algebraMap (𝒪[(A p).Fp]) (A p).Ep ⟨_, hm⟩ := rfl
  rw [e]
  exact isIntegral_algebraMap

theorem clear_one (p : HeightOneSpectrum (𝓞 F)) (z : (A p).Ep) :
    ∃ t : 𝓞 F, t ≠ 0 ∧ algebraMap (A p).Fp (A p).Ep ((A p).ιF (algebraMap (𝓞 F) F t)) * z ∈ (A p).O := by
  haveI := (A p).lf
  have hz : z ∈ Submodule.span (A p).Fp (Set.range (A p).ιE) := by
    rw [(A p).span]
    trivial
  induction hz using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨e, rfl⟩ := hx
    have hz : IsAlgebraic ℤ e :=
      (IsFractionRing.isAlgebraic_iff ℤ ℚ E).2 (Algebra.IsAlgebraic.isAlgebraic e)
    have inj : ∀ x : ℤ, algebraMap ℤ E x = 0 → x = 0 := fun x hx => by simpa using hx
    have hint : ∃ y : ℤ, y ≠ 0 ∧ IsIntegral ℤ ((y : E) * e) := by
      first
      | (obtain ⟨⟨w, hw⟩, y, hy0, hyw⟩ := exists_integral_multiple hz inj
         refine ⟨y, hy0, ?_⟩
         rw [mul_comm]
         have hw' : IsIntegral ℤ w := hw
         simpa [hyw] using hw')
      | (obtain ⟨y, hy0, hy⟩ := hz.exists_integral_multiple
         exact ⟨y, hy0, by simpa [zsmul_eq_mul] using hy⟩)
    obtain ⟨y, hy0, hy⟩ := hint
    refine ⟨(y : 𝓞 F), by exact_mod_cast hy0, ?_⟩
    rw [← (A p).compat, ← map_mul]
    have e1 : algebraMap F E (algebraMap (𝓞 F) F (y : 𝓞 F)) * e = (y : E) * e := by simp
    rw [e1, (A p).O_def]
    have h2 : IsIntegral ℤ ((A p).ιE ((y : E) * e)) := hy.map (A p).ιE.toIntAlgHom
    exact h2.tower_top
  | zero =>
    refine ⟨1, one_ne_zero, ?_⟩
    rw [mul_zero]
    exact Subring.zero_mem _
  | add x y _ _ hx hy =>
    obtain ⟨t1, h10, h1⟩ := hx
    obtain ⟨t2, h20, h2⟩ := hy
    refine ⟨t1 * t2, mul_ne_zero h10 h20, ?_⟩
    have e : algebraMap (A p).Fp (A p).Ep ((A p).ιF (algebraMap (𝓞 F) F (t1 * t2))) * (x + y) =
        algebraMap (A p).Fp (A p).Ep ((A p).ιF (algebraMap (𝓞 F) F t2)) *
          (algebraMap (A p).Fp (A p).Ep ((A p).ιF (algebraMap (𝓞 F) F t1)) * x) +
        algebraMap (A p).Fp (A p).Ep ((A p).ιF (algebraMap (𝓞 F) F t1)) *
          (algebraMap (A p).Fp (A p).Ep ((A p).ιF (algebraMap (𝓞 F) F t2)) * y) := by
      simp only [map_mul]
      ring
    rw [e]
    exact Subring.add_mem _ (Subring.mul_mem _ (algebraMap_ιF_mem_O A p t2) h1)
      (Subring.mul_mem _ (algebraMap_ιF_mem_O A p t1) h2)
  | smul c x _ hx =>
    obtain ⟨t1, h10, h1⟩ := hx
    obtain ⟨t2, h20, h2⟩ := clear_F A p c
    refine ⟨t2 * t1, mul_ne_zero h20 h10, ?_⟩
    rw [Algebra.smul_def]
    have e : algebraMap (A p).Fp (A p).Ep ((A p).ιF (algebraMap (𝓞 F) F (t2 * t1))) *
        (algebraMap (A p).Fp (A p).Ep c * x) =
        algebraMap (A p).Fp (A p).Ep ((A p).ιF (algebraMap (𝓞 F) F t2) * c) *
          (algebraMap (A p).Fp (A p).Ep ((A p).ιF (algebraMap (𝓞 F) F t1)) * x) := by
      simp only [map_mul]
      ring
    rw [e]
    exact Subring.mul_mem _ (ιF_mem_O_of_mem_integers A p _ h2) h1

end Clear

section Mat

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {sig : E →ₐ[F] E}
  (A : ∀ p : HeightOneSpectrum (𝓞 F), Formalism.MainNotions.S.Loc.LocAt F E sig p) {n : ℕ}

theorem approx_lo (S : Finset (HeightOneSpectrum (𝓞 F))) (c : 𝓞 F) (hc : c ≠ 0)
    (g : ∀ p, Matrix (Fin n) (Fin n) (A p).Ep) (hg1 : ∀ p ∈ S, ∀ a, g p a a = 1)
    (hg0 : ∀ p ∈ S, ∀ a b, a < b → g p a b = 0) :
    ∃ L : Matrix (Fin n) (Fin n) E, (∀ a, L a a = 1) ∧ (∀ a b, a < b → L a b = 0) ∧
      (∀ p ∈ S, ∀ a b, ∃ o ∈ (A p).O,
        (A p).ιE (L a b) - g p a b = algebraMap (A p).Fp (A p).Ep ((A p).ιF (algebraMap (𝓞 F) F c)) * o) ∧
      ∀ p ∉ S, ∀ a b, (A p).ιE (L a b) ∈ (A p).O := by
  have h := fun ab : Fin n × Fin n => approxE A S c hc (fun p => g p ab.1 ab.2)
  choose x hxS hxO using h
  refine ⟨fun a b => if b < a then x (a, b) else if a = b then 1 else 0, fun a => by simp, fun a b hab => ?_,
    fun p hp a b => ?_, fun p hp a b => ?_⟩
  · simp [not_lt.2 hab.le, hab.ne]
  · by_cases hba : b < a
    · simp only [hba, if_true]; exact hxS (a, b) p hp
    · refine ⟨0, zero_mem _, ?_⟩
      rcases eq_or_ne a b with rfl | hab
      · simp [hg1 p hp a]
      · have hlt : a < b := lt_of_le_of_ne (not_lt.1 hba) hab
        simp [hba, hab, hg0 p hp a b hlt]
  · by_cases hba : b < a
    · simp only [hba, if_true]; exact hxO (a, b) p hp
    · simp only [hba, if_false]
      split_ifs
      · rw [map_one]; exact one_mem _
      · rw [map_zero]; exact zero_mem _

theorem approx_up (S : Finset (HeightOneSpectrum (𝓞 F))) (c : 𝓞 F) (hc : c ≠ 0)
    (g : ∀ p, Matrix (Fin n) (Fin n) (A p).Ep) (hg1 : ∀ p ∈ S, ∀ a, g p a a = 1)
    (hg0 : ∀ p ∈ S, ∀ a b, b < a → g p a b = 0) :
    ∃ U : Matrix (Fin n) (Fin n) E, (∀ a, U a a = 1) ∧ (∀ a b, b < a → U a b = 0) ∧
      (∀ p ∈ S, ∀ a b, ∃ o ∈ (A p).O,
        (A p).ιE (U a b) - g p a b = algebraMap (A p).Fp (A p).Ep ((A p).ιF (algebraMap (𝓞 F) F c)) * o) ∧
      ∀ p ∉ S, ∀ a b, (A p).ιE (U a b) ∈ (A p).O := by
  obtain ⟨L, hL1, hL0, hLS, hLn⟩ := approx_lo A S c hc (fun p => (g p).transpose)
    (fun p hp a => by simpa using hg1 p hp a)
    (fun p hp a b hab => by simpa [Matrix.transpose_apply] using hg0 p hp b a hab)
  refine ⟨L.transpose, fun a => by simpa using hL1 a, fun a b hab => by simpa using hL0 b a hab,
    fun p hp a b => ?_, fun p hp a b => by simpa using hLn p hp b a⟩
  simpa [Matrix.transpose_apply] using hLS p hp b a

end Mat

end Formalism.L2.SG.Pf.PCountEx
end
end

-- bundled from Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.ProdEApproxAd
section
noncomputable section

open IsDedekindDomain NumberField ValuativeRel

namespace Formalism.L2.SG.Pf.ProdEApprox

section Ball

variable {K : Type*} [Field K] [ValuativeRel K]

def InBall (c x : K) : Prop := ValuativeRel.valuation K x ≤ ValuativeRel.valuation K c

def ballS (c : K) : AddSubgroup K where
  carrier := {x | InBall c x}
  zero_mem' := by simp [InBall]
  add_mem' := fun {x y} hx hy => by
    simp only [Set.mem_setOf_eq, InBall] at hx hy ⊢
    exact Valuation.map_add_le _ hx hy
  neg_mem' := fun {x} hx => by
    simp only [Set.mem_setOf_eq, InBall] at hx ⊢
    simpa [Valuation.map_neg] using hx

theorem mem_ballS {c x : K} : x ∈ ballS c ↔ valuation K x ≤ valuation K c := by
  show InBall c x ↔ _
  rfl

theorem ballS_isOpen [TopologicalSpace K] [IsValuativeTopology K] {c : K} (hc : c ≠ 0) :
    IsOpen (ballS c : Set K) := by
  rw [isOpen_iff_mem_nhds]
  intro x hx
  have hv : valuation K c ≠ 0 := by simpa using hc
  refine IsValuativeTopology.mem_nhds_iff'.mpr ⟨Units.mk0 _ hv, fun y hy => ?_⟩
  have hy' : valuation K (y - x) < valuation K c := by simpa using hy
  rw [SetLike.mem_coe, mem_ballS]
  have e : y = (y - x) + x := by ring
  rw [e]
  exact Valuation.map_add_le _ hy'.le hx

theorem ballS_mul {c x : K} (hc : c ≠ 0) (hx : x ∈ ballS c) : ∃ β ∈ 𝒪[K], x = c * β := by
  refine ⟨x / c, ?_, by field_simp⟩
  rw [Valuation.mem_integer_iff, map_div₀]
  exact div_le_one_of_le₀ (mem_ballS.1 hx) zero_le'

end Ball

section Ad

open Formalism.MainNotions.S.Loc PI.StrongApproxE

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {sig : E →ₐ[F] E}
  (L : ∀ p : HeightOneSpectrum (𝓞 F), LocAt F E sig p)

theorem sa_lat (T : Finset (HeightOneSpectrum (𝓞 F))) (x : ∀ p, (L p).Ep) (c : ∀ p, (L p).Fp)
    (hc : ∀ p ∈ T, c p ≠ 0) :
    ∃ t : E, (∀ p ∈ T, ∃ y ∈ (L p).O, (L p).ιE t - x p = algebraMap (L p).Fp (L p).Ep (c p) * y) ∧
      ∀ p, p ∉ T → (L p).ιE t ∈ (L p).O := by
  classical
  obtain ⟨n, b, hbint, hbspan⟩ := intSpan' F E
  choose α hα using fun p => local_span_holds F E sig p (L p) n b hbspan (x p)
  set c' : ∀ p, (L p).Fp := fun p => if p ∈ T then c p else 1 with hc'
  have hc'0 : ∀ p, c' p ≠ 0 := by
    intro p
    by_cases hp : p ∈ T
    · simp only [hc', if_pos hp]; exact hc p hp
    · simp only [hc', if_neg hp]; exact one_ne_zero
  have hVo : ∀ p, IsOpen (ballS (c' p) : Set (L p).Fp) := by
    intro p
    have := (L p).lf
    exact ballS_isOpen (hc'0 p)
  choose a ha using fun p (i : Fin n) => local_dense_embedding F E sig p (L p) (ballS (c' p)) (hVo p) (α p i)
  choose d hd0 hd using fun p => local_neighbourhood_small F E sig p (L p) (ballS (c' p)) (hVo p)
  choose t ht1 ht2 using fun i : Fin n => strong_approximation_finite_places F T (fun p => a p i) d (fun p _ => hd0 p)
  refine ⟨∑ i, t i • b i, fun p hp => ?_, fun p hp => ?_⟩
  · have hιE : (L p).ιE (∑ i, t i • b i) = ∑ i, (L p).ιF (t i) • (L p).ιE (b i) := by
      set_option synthInstance.maxHeartbeats 100000 in
        rw [map_sum]
      exact Finset.sum_congr rfl fun i _ => existsLatticeAutomorphismApprox F E sig p (L p) (t i) (b i)
    have h1 : (L p).ιE (∑ i, t i • b i) - x p = ∑ i, ((L p).ιF (t i) - α p i) • (L p).ιE (b i) := by
      rw [hιE]
      conv_lhs => rw [hα p]
      rw [← Finset.sum_sub_distrib]
      exact Finset.sum_congr rfl fun i _ => (sub_smul _ _ _).symm
    have hmem : ∀ i, (L p).ιF (t i) - α p i ∈ ballS (c' p) := by
      intro i
      have h2 : (L p).ιF (t i) - α p i = (L p).ιF (t i - a p i) + ((L p).ιF (a p i) - α p i) := by
        rw [map_sub]; ring
      rw [h2]
      exact (ballS (c' p)).add_mem (hd p _ (ht1 i p hp)) (ha p i)
    have hcp : c' p = c p := by simp only [hc', if_pos hp]
    choose β hβO hβ using fun i => ballS_mul (hc'0 p) (hmem i)
    have hbO : ∀ i, (L p).ιE (b i) ∈ (L p).O := by
      intro i
      have := local_integral_of_substitution F E sig p (L p) 1 (b i) (by simp) (hbint i)
      simpa using this
    have hβE : ∀ i, algebraMap (L p).Fp (L p).Ep (β i) * (L p).ιE (b i) ∈ (L p).O := by
      intro i
      have := (L p).lf
      have hA : IsIntegral 𝒪[(L p).Fp] (algebraMap (L p).Fp (L p).Ep (β i)) :=
        isIntegral_algebraMap (R := 𝒪[(L p).Fp]) (A := (L p).Ep) (x := ⟨β i, hβO i⟩)
      exact (L p).O.mul_mem (((L p).O_def _).mpr hA) (hbO i)
    refine ⟨∑ i, algebraMap (L p).Fp (L p).Ep (β i) * (L p).ιE (b i), (L p).O.sum_mem fun i _ => hβE i, ?_⟩
    rw [h1, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [hβ i, ← hcp, Algebra.smul_def, map_mul, mul_assoc]
  · set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum]
    refine (L p).O.sum_mem fun i _ => ?_
    rw [existsLatticeAutomorphismApprox F E sig p (L p) (t i) (b i)]
    exact local_integral_of_substitution F E sig p (L p) (t i) (b i) (ht2 i p hp) (hbint i)

end Ad

end Formalism.L2.SG.Pf.ProdEApprox
end
end

