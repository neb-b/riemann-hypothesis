module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0036

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalComponentDefiniteUnitaryFinitePartEqLocalPo
section
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.BCT.FinPtLoc

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ}

def fstA (E : Type) [Field E] [NumberField E] : Ad E →+* InfiniteAdeleRing E := RingHom.fst _ _

theorem fst_entry (γ : GL (Fin n) E) (i j : Fin n) :
    fstA E ((finGL E n (ratF E n γ)).val i j) = (1 : Matrix (Fin n) (Fin n) (InfiniteAdeleRing E)) i j := by
  change ((1 : Matrix (Fin n) (Fin n) (InfiniteAdeleRing E × Af E)) i j -
      ((0 : InfiniteAdeleRing E), (1 : Matrix (Fin n) (Fin n) (Af E)) i j) +
      ((0 : InfiniteAdeleRing E), algebraMap E (Af E) (γ.val i j))).1 = _
  by_cases h : i = j <;> simp [Matrix.one_apply, h]

theorem snd_entry (γ : GL (Fin n) E) (i j : Fin n) :
    pFin E ((finGL E n (ratF E n γ)).val i j) = algebraMap E (Af E) (γ.val i j) := by
  change ((1 : Matrix (Fin n) (Fin n) (InfiniteAdeleRing E × Af E)) i j -
      ((0 : InfiniteAdeleRing E), (1 : Matrix (Fin n) (Fin n) (Af E)) i j) +
      ((0 : InfiniteAdeleRing E), algebraMap E (Af E) (γ.val i j))).2 = _
  by_cases h : i = j <;> simp [Matrix.one_apply, h]

theorem map_cT {A B : Type} [CommRing A] [CommRing B] (f : A →+* B) (σ : A →+* A) (τ : B →+* B)
    (h : ∀ x, f (σ x) = τ (f x)) (M : Matrix (Fin n) (Fin n) A) : (cT σ M).map f = cT τ (M.map f) := by
  ext i j; simp [cT, h]

theorem ext_ad (M N : Matrix (Fin n) (Fin n) (Ad E)) (h1 : M.map (fstA E) = N.map (fstA E))
    (h2 : M.map (pFin E) = N.map (pFin E)) : M = N := by
  ext i j
  exact Prod.ext (congrFun (congrFun h1 i) j) (congrFun (congrFun h2 i) j)

theorem mem_UA (γ : UE E n) : finGL E n (ratF E n γ.1) ∈ UA E n := by
  have hγ : cT (IsCMField.complexConj E).toRingEquiv.toRingHom γ.1.val * 1 * γ.1.val = 1 := γ.2
  show cT (conjAd E) (finGL E n (ratF E n γ.1)).val * 1 * (finGL E n (ratF E n γ.1)).val = 1
  have hf : (finGL E n (ratF E n γ.1)).val.map (fstA E) = 1 := by
    ext i j; rw [Matrix.map_apply, fst_entry]
  have hs : (finGL E n (ratF E n γ.1)).val.map (pFin E) = γ.1.val.map (algebraMap E (Af E)) := by
    ext i j; rw [Matrix.map_apply, snd_entry]; rfl
  apply ext_ad
  · rw [Matrix.map_mul, Matrix.map_mul, map_cT (fstA E) (conjAd E) ((infEq E).toRingHom.comp ((starRingEnd (Cinf E)).comp (infEq E).symm.toRingHom)) (fun x => rfl), hf, Matrix.map_one _ (map_zero _) (map_one _)]
    ext i j; simp [cT, Matrix.one_apply]
  · rw [Matrix.map_mul, Matrix.map_mul, map_cT (pFin E) (conjAd E) (conjFin (IsCMField.complexConj E).toRingEquiv) (fun x => rfl), hs,
      Matrix.map_one _ (map_zero _) (map_one _)]
    have : cT (conjFin (IsCMField.complexConj E).toRingEquiv) (γ.1.val.map (algebraMap E (Af E))) =
        (cT (IsCMField.complexConj E).toRingEquiv.toRingHom γ.1.val).map (algebraMap E (Af E)) := by
      ext i j; simp [cT, conjFin_algebraMap]
    rw [this, ← Matrix.map_one (algebraMap E (Af E)) (map_zero _) (map_one _), ← Matrix.map_mul, ← Matrix.map_mul, hγ]

theorem toSub_of_mem {G : Type} [Group G] (H : Subgroup G) (g : G) (h : g ∈ H) : toSub H g = ⟨g, h⟩ :=
  dif_pos h

theorem mem_finU (γ : UE E n) : (⟨_, mem_UA γ⟩ : UA E n) ∈ finU (E := E) (n := n) := by
  show cInf (⟨_, mem_UA γ⟩ : UA E n) = 1
  apply Units.ext
  refine Matrix.ext fun i j => ?_
  change (infEq E).symm (fstA E ((finGL E n (ratF E n γ.1)).val i j)) = (1 : Matrix (Fin n) (Fin n) (Cinf E)) i j
  rw [fst_entry]
  by_cases h : i = j <;> simp [Matrix.one_apply, h]

theorem finPt_eq (γ : UE E n) : ((finPt γ : finU (E := E) (n := n)) : UA E n) = ⟨_, mem_UA γ⟩ := by
  have h1 : toSub (UA E n) (finGL E n (ratF E n γ.1)) = ⟨_, mem_UA γ⟩ := toSub_of_mem _ _ (mem_UA γ)
  unfold finPt
  rw [h1, toSub_of_mem _ _ (mem_finU γ)]

end GlobalTheory.BCT.FinPtLoc

theorem GlobalTheory.BCT.locPt_finPt : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E], Unr E → ∀ n : ℕ, ∀ (γ : UE E n) (w : Pl E),
    toSub (UL n w) (cLoc w ((finPt γ : finU (E := E) (n := n)) : UA E n)) = locPt w γ := by
  intro E _ _ _ _ n γ w
  rw [FinPtLoc.finPt_eq]
  unfold locPt
  congr 1
  apply Units.ext
  refine Matrix.ext fun i j => ?_
  change pLoc E w (pFin E ((finGL E n (ratF E n γ.1)).val i j)) = algebraMap E _ (γ.1.val i j)
  rw [FinPtLoc.snd_entry]
  rfl
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalConjugationInvolutiveValuationPreserving
section
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

open Topology ValuativeRel

namespace GlobalTheory.CjInv

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {w : Pl E}

theorem valuation_equiv :
    (valuation (w.adicCompletion E)).IsEquiv (Valued.v : Valuation (w.adicCompletion E) (WithZero (Multiplicative ℤ))) := by
  haveI : (Valued.v : Valuation (w.adicCompletion E) (WithZero (Multiplicative ℤ))).Compatible :=
    Valuation.Compatible.ofValuation _
  exact isEquiv _ _

theorem lt_one_iff (x : w.adicCompletion E) : valuation (w.adicCompletion E) x < 1 ↔ Valued.v x < 1 := by
  simp only [← not_le]
  exact not_congr valuation_equiv.one_le_iff_one_le

theorem tendsto_pow_zero {x : w.adicCompletion E} (h : Valued.v x < 1) :
    Tendsto (fun n : ℕ => x ^ n) atTop (𝓝 0) := by
  rw [← lt_one_iff] at h
  rw [(IsValuativeTopology.hasBasis_nhds_zero' (w.adicCompletion E)).tendsto_right_iff]
  intro γ hγ
  have : MulArchimedean (ValueGroupWithZero (w.adicCompletion E)) :=
    ValuativeRel.isRankLeOne_iff_mulArchimedean.mp inferInstance
  obtain ⟨n, hn⟩ := exists_pow_lt₀ h (Units.mk0 γ hγ)
  filter_upwards [eventually_ge_atTop n] with m hm
  show valuation _ (x ^ m) < γ
  rw [map_pow]
  exact lt_of_le_of_lt (pow_le_pow_right_of_le_one' h.le hm) hn

theorem lt_one_mem_nhds : {y : w.adicCompletion E | Valued.v y < 1} ∈ 𝓝 (0 : w.adicCompletion E) := by
  have := (IsValuativeTopology.hasBasis_nhds_zero' (w.adicCompletion E)).mem_iff.2 ⟨1, one_ne_zero, fun _ hy => hy⟩
  simpa only [lt_one_iff] using this

theorem lt_one_of_map (s : w.adicCompletion E →+* w.adicCompletion E) (hs : Continuous s) {x : w.adicCompletion E}
    (h : Valued.v x < 1) : Valued.v (s x) < 1 := by
  have h1 : Tendsto (fun n : ℕ => s x ^ n) atTop (𝓝 0) := by
    have := (hs.tendsto 0).comp (tendsto_pow_zero h)
    simpa [Function.comp_def, map_pow] using this
  obtain ⟨N, hN⟩ := (h1.eventually lt_one_mem_nhds).exists
  by_contra hc
  push_neg at hc
  have : 1 ≤ Valued.v (s x ^ N) := by rw [map_pow]; exact one_le_pow₀ hc
  exact absurd hN (not_lt.2 this)

theorem le_exp_neg_one {x : WithZero (Multiplicative ℤ)} (hx : x < 1) : x ≤ WithZero.exp (-1) := by
  by_cases h0 : x = 0
  · rw [h0]; exact zero_le'
  · rw [← WithZero.exp_log h0] at hx ⊢
    rw [← WithZero.exp_zero, WithZero.exp_lt_exp] at hx
    rw [WithZero.exp_le_exp]
    omega

theorem valued_map_eq (s : w.adicCompletion E →+* w.adicCompletion E) (hs : Continuous s) (hss : ∀ x, s (s x) = x)
    (x : w.adicCompletion E) : Valued.v (s x) = Valued.v x := by

  have hle : ∀ y : w.adicCompletion E, Valued.v y ≤ 1 → Valued.v (s y) ≤ 1 := by
    intro y hy
    by_contra hc
    push_neg at hc
    have hy0 : s y ≠ 0 := by
      intro h0; rw [h0, map_zero] at hc; exact absurd hc (not_lt.2 zero_le')
    have h1 : Valued.v (s y)⁻¹ < 1 := by rw [map_inv₀]; exact inv_lt_one_of_one_lt₀ hc
    have h2 := lt_one_of_map s hs h1
    rw [map_inv₀, hss, map_inv₀] at h2
    have h0 : (0 : WithZero (Multiplicative ℤ)) < Valued.v y := by
      rw [zero_lt_iff, Valuation.ne_zero_iff]
      intro h; apply hy0; rw [h, map_zero]
    exact absurd hy (not_le.2 ((inv_lt_one₀ h0).1 h2))

  have hord : ∀ a b : w.adicCompletion E, b ≠ 0 → Valued.v a ≤ Valued.v b → Valued.v (s a) ≤ Valued.v (s b) := by
    intro a b hb hab
    have hb' : s b ≠ 0 := (map_ne_zero s).2 hb
    have h1 : Valued.v (a / b) ≤ 1 := by
      rw [map_div₀]; exact div_le_one_of_le₀ hab zero_le'
    have h2 := hle _ h1
    rw [map_div₀, map_div₀] at h2
    have h0 : (0 : WithZero (Multiplicative ℤ)) < Valued.v (s b) := by
      rw [zero_lt_iff, Valuation.ne_zero_iff]; exact hb'
    exact (div_le_one₀ h0).1 h2

  obtain ⟨π, hπ⟩ := w.valuation_exists_uniformizer E
  set p : w.adicCompletion E := algebraMap E (w.adicCompletion E) π with hp
  have hvp : Valued.v p = WithZero.exp (-1) := by
    have := HeightOneSpectrum.valuedAdicCompletion_eq_valuation' w π
    rw [hπ] at this
    exact this
  have hp0 : p ≠ 0 := by
    intro h; rw [h, map_zero] at hvp; exact WithZero.exp_ne_zero hvp.symm
  have hsp0 : s p ≠ 0 := (map_ne_zero s).2 hp0
  have hvsp : Valued.v (s p) = Valued.v p := by
    apply le_antisymm
    · rw [hvp]; apply le_exp_neg_one; apply lt_one_of_map s hs; rw [hvp]
      rw [← WithZero.exp_zero, WithZero.exp_lt_exp]; norm_num
    · have := hord (s p) p hp0 (by
        rw [hvp]; apply le_exp_neg_one; apply lt_one_of_map s hs; rw [hvp]
        rw [← WithZero.exp_zero, WithZero.exp_lt_exp]; norm_num)
      rwa [hss] at this
  by_cases hx : x = 0
  · rw [hx, map_zero]
  have hvx : Valued.v x ≠ 0 := (Valuation.ne_zero_iff _).2 hx
  set k := WithZero.log (Valued.v x) with hk
  set u := x * p ^ k with hu
  have hvpk : Valued.v p ^ k ≠ 0 := zpow_ne_zero _ ((Valuation.ne_zero_iff _).2 hp0)
  have hvu : Valued.v u = 1 := by
    rw [hu, map_mul, map_zpow₀, hvp, ← WithZero.exp_log hvx, ← hk, ← WithZero.exp_zsmul, ← WithZero.exp_add]
    simp
  have hu0 : u ≠ 0 := by
    intro h; rw [h, map_zero] at hvu; exact zero_ne_one hvu
  have hsu1 : Valued.v (s u) ≤ 1 := hle u hvu.le
  have hsu2 : Valued.v (s u⁻¹) ≤ 1 := hle u⁻¹ (by rw [map_inv₀, hvu, inv_one])
  have hsu : Valued.v (s u) = 1 := by
    apply le_antisymm hsu1
    rw [map_inv₀, map_inv₀] at hsu2
    have h0 : (0 : WithZero (Multiplicative ℤ)) < Valued.v (s u) := by
      rw [zero_lt_iff, Valuation.ne_zero_iff]; exact (map_ne_zero s).2 hu0
    exact (inv_le_one₀ h0).1 hsu2
  rw [hu, map_mul, map_zpow₀, map_mul, map_zpow₀, hvsp] at hsu
  rw [hu, map_mul, map_zpow₀] at hvu
  exact mul_right_cancel₀ hvpk (hsu.trans hvu.symm)

end GlobalTheory.CjInv

namespace GlobalTheory.BCT

theorem cj_involutive_valuation : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (w : Pl E),
    (∀ x, cj w (cj w x) = x) ∧ ∀ x, Valued.v (cj w x) = Valued.v x := by
  intro E _ _ _ w
  have key : (∀ x, cj w (cj w x) = x) ∧ Continuous (cj w) := by
    unfold cj
    split_ifs with h
    · obtain ⟨hc, hE⟩ := h.choose_spec
      refine ⟨fun x => ?_, hc⟩
      have hd := HeightOneSpectrum.denseRange_algebraMap E w
      have := hd.equalizer (hc.comp hc) continuous_id (funext fun y => by
        simp only [Function.comp_apply, id_eq, hE, IsCMField.complexConj_apply_apply])
      exact congrFun this x
    · exact ⟨fun x => rfl, continuous_id⟩
  exact ⟨key.1, GlobalTheory.CjInv.valued_map_eq (cj w) key.2 key.1⟩

end GlobalTheory.BCT
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalSignFullCharpolyEqOne
section
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.BCT.KapSignFull

theorem ordL_cj_mul {E : Type} [Field E] [NumberField E] [IsCMField E] (w : Pl E)
    (hcj : ∀ x, Valued.v (cj w x) = Valued.v x) (x : w.adicCompletion E) (hx : x ≠ 0) :
    ordL (cj w x * x) = 2 * ordL x := by
  have h0 : Valued.v x ≠ 0 := by simpa using hx
  have e : Valued.v (cj w x * x) = Valued.v x * Valued.v x := by rw [map_mul, hcj]
  have h1 : Valued.v (cj w x * x) ≠ 0 := by rw [e]; exact mul_ne_zero h0 h0
  unfold ordL
  rw [dite_eq_right h1, dite_eq_right h0]
  have : WithZero.unzero h1 = WithZero.unzero h0 * WithZero.unzero h0 := by
    apply WithZero.coe_injective
    rw [WithZero.coe_mul, WithZero.coe_unzero, WithZero.coe_unzero, e]
  rw [this, toAdd_mul]; ring

theorem kapSign_charpoly_eq_one : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ) (w : Pl E),
    (∀ x, Valued.v (cj w x) = Valued.v x) → ∀ γ : GLw n w, kapSign n w γ.val.charpoly γ = 1 := by
  intro E _ _ _ n w hcj γ
  unfold kapSign
  split_ifs with hs
  · rfl
  · simp only []
    set V₁ := LinearMap.ker (Matrix.toLin' (aeval γ.val γ.val.charpoly)) with hV
    have htop : V₁ = ⊤ := by rw [hV, Matrix.aeval_self_charpoly]; simp
    set b := Module.finBasis (w.adicCompletion E) V₁
    have hm : Module.finrank (w.adicCompletion E) V₁ = n := by
      rw [htop, finrank_top]; simp
    let e : Fin (Module.finrank (w.adicCompletion E) V₁) ≃ Fin n := finCongr hm
    let M : Matrix (Fin n) (Fin n) (w.adicCompletion E) := fun k j => (b (e.symm j)).1 k
    have hG : (Matrix.of fun i j => ∑ k, cj w ((b i).1 k) * (b j).1 k) =
        ((M.map (cj w))ᵀ * M).submatrix e e := by
      refine Matrix.ext fun i j => ?_
      rw [Matrix.of_apply, Matrix.submatrix_apply, Matrix.mul_apply]
      exact Finset.sum_congr rfl fun k _ => rfl
    have hM : M.det ≠ 0 := by
      have hli : LinearIndependent (w.adicCompletion E) M.col := by
        have h1 : LinearIndependent (w.adicCompletion E) (fun i => ((b i : V₁) : Fin n → w.adicCompletion E)) :=
          b.linearIndependent.map' V₁.subtype (Submodule.ker_subtype V₁)
        have h2 := h1.comp e.symm e.symm.injective
        have hc : M.col = (fun i => ((b i : V₁) : Fin n → w.adicCompletion E)) ∘ e.symm := by funext j; rfl
        rw [hc]; exact h2
      exact (Matrix.isUnit_iff_isUnit_det M).1 (Matrix.linearIndependent_cols_iff_isUnit.1 hli) |>.ne_zero
    rw [hG, Matrix.det_submatrix_equiv_self, Matrix.det_mul, Matrix.det_transpose, show (M.map (cj w)).det = cj w M.det by rw [RingHom.map_det]; rfl,
      ordL_cj_mul w hcj _ hM]
    exact Even.neg_one_zpow ⟨ordL M.det, by ring⟩

end GlobalTheory.BCT.KapSignFull
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalSignKernelCharFactorConjInvariant
section
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section
namespace GlobalTheory.BCT.ConjugationGramUnitary

open Formalism.UG

theorem negOne_zpow_ordL_mul {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))] (σ : L →+* L)
    (hσ : ∀ x, Valued.v (σ x) = Valued.v x) (a x : L) (ha : a ≠ 0) :
    (-1 : ℂ) ^ ordL (σ a * a * x) = (-1 : ℂ) ^ ordL x := by
  have key : ∀ (y : L) (m : ℤ), Valued.v y = ((Multiplicative.ofAdd (-m) : Multiplicative ℤ) : WithZero (Multiplicative ℤ)) →
      ordL y = m := by
    intro y m h
    have hne : Valued.v y ≠ 0 := by rw [h]; exact WithZero.coe_ne_zero
    unfold ordL
    rw [dite_eq_right hne]
    have e : ((WithZero.unzero hne : Multiplicative ℤ) : WithZero (Multiplicative ℤ)) = Multiplicative.ofAdd (-m) := by
      rw [WithZero.coe_unzero, h]
    rw [WithZero.coe_inj.mp e]
    simp
  have spec : ∀ y : L, y ≠ 0 → Valued.v y = ((Multiplicative.ofAdd (-(ordL y)) : Multiplicative ℤ) : WithZero (Multiplicative ℤ)) := by
    intro y hy
    have hne : Valued.v y ≠ 0 := (Valuation.ne_zero_iff _).mpr hy
    unfold ordL
    rw [dite_eq_right hne]
    simp
  by_cases hx : x = 0
  · simp [hx]
  have h1 : ordL (σ a * a * x) = 2 * ordL a + ordL x := by
    apply key
    rw [map_mul, map_mul, hσ, spec a ha, spec x hx]
    rw [← WithZero.coe_mul, ← WithZero.coe_mul]
    congr 1
    rw [← ofAdd_add, ← ofAdd_add]
    congr 1
    ring
  rw [h1, zpow_add₀ (by norm_num), Even.neg_one_zpow (even_two_mul _), one_mul]

def gram {K : Type} [Field K] (σ : K →+* K) {n : ℕ} {ι : Type} (v : ι → (Fin n → K)) : Matrix ι ι K :=
  Matrix.of fun i j => ∑ k, σ (v i k) * v j k

theorem gram_basis {K : Type} [Field K] (σ : K →+* K) {n : ℕ} (V : Submodule K (Fin n → K)) {ι : Type} [Fintype ι]
    [DecidableEq ι] (b c : Module.Basis ι K V) :
    gram σ (fun i => (c i : Fin n → K)) =
      ((b.toMatrix c).map σ)ᵀ * gram σ (fun i => (b i : Fin n → K)) * b.toMatrix c := by
  have hc : ∀ j k, (c j : Fin n → K) k = ∑ l, b.toMatrix c l j * (b l : Fin n → K) k := by
    intro j k
    have := b.sum_toMatrix_smul_self c j
    rw [← this, Submodule.coe_sum, Finset.sum_apply]
    simp only [Submodule.coe_smul, Pi.smul_apply, smul_eq_mul]
  ext i j
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [gram, Matrix.of_apply, Matrix.mul_apply, Matrix.transpose_apply, Matrix.map_apply, hc, map_sum, map_mul,
    Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun l _ => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun m _ => ?_
  refine Finset.sum_congr rfl fun k _ => ?_
  ring

theorem gram_unitary {K : Type} [Field K] (σ : K →+* K) {n : ℕ} (g : Matrix (Fin n) (Fin n) K)
    (hg : (g.map σ)ᵀ * g = 1) {ι : Type} (v : ι → (Fin n → K)) :
    gram σ (fun i => g *ᵥ v i) = gram σ v := by
  have he : ∀ a b, ∑ k, σ (g k a) * g k b = if a = b then 1 else 0 := by
    intro a b
    have := congrFun (congrFun hg a) b
    simpa [Matrix.mul_apply, Matrix.one_apply] using this
  have hm : ∀ (x : Fin n → K) k, (g *ᵥ x) k = ∑ a, g k a * x a := fun _ _ => rfl
  ext i j
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [gram, Matrix.of_apply, hm, map_sum, map_mul, Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [Finset.sum_comm]
  have : ∀ y, ∑ k, σ (g k y) * σ (v i y) * (g k a * v j a) = σ (v i y) * v j a * (if y = a then 1 else 0) := by
    intro y
    rw [← he y a, Finset.mul_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    ring
  simp only [this, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true]

theorem aeval_conj {K : Type} [Field K] {n : ℕ} (γ g : GL (Fin n) K) (Q : K[X]) :
    aeval (g⁻¹ * γ * g).val Q = (g⁻¹).val * aeval γ.val Q * g.val := by
  induction Q using Polynomial.induction_on' with
  | add p q hp hq => rw [map_add (f := _), map_add (f := _), hp, hq, Matrix.mul_add, Matrix.add_mul]
  | monomial k a =>
    simp only [aeval_monomial, Units.val_mul]
    have : ((g⁻¹).val * γ.val * g.val) ^ k = (g⁻¹).val * γ.val ^ k * g.val := by
      induction k with
      | zero => simp
      | succ k ih =>
        rw [pow_succ, ih, pow_succ]
        simp only [Matrix.mul_assoc]
        congr 2
        rw [← Matrix.mul_assoc g.val, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.one_mul]
    rw [this]
    simp [Algebra.algebraMap_eq_smul_one, Matrix.mul_smul, Matrix.smul_mul]

end GlobalTheory.BCT.ConjugationGramUnitary

namespace GlobalTheory.BCT

open GlobalTheory.BCT.ConjugationGramUnitary

theorem kapSign_conj : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ) (w : Pl E),
    (∀ x, Valued.v (cj w x) = Valued.v x) →
    ∀ (Q₁ : (w.adicCompletion E)[X]) (γ g : UL n w), kapSign n w Q₁ (g⁻¹ * γ * g).1 = kapSign n w Q₁ γ.1 := by
  intro E _ _ _ n w hv Q₁ γ g
  unfold kapSign
  split_ifs with hs
  · rfl
  have hg : ((g.1.val).map (cj w))ᵀ * g.1.val = 1 := by
    have h := g.2
    simp only [UL, hs, if_false] at h
    have h2 : Formalism.UG.cT (cj w) (g.1 : Matrix (Fin n) (Fin n) (w.adicCompletion E)) * 1 * (g.1 : Matrix (Fin n) (Fin n) _) = 1 := h
    simpa [Formalism.UG.cT] using h2
  have hinv : ((g.1)⁻¹).val * g.1.val = 1 := by rw [← Units.val_mul, inv_mul_cancel, Units.val_one]
  have hinv' : g.1.val * ((g.1)⁻¹).val = 1 := by rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
  have hM : aeval ((g⁻¹ * γ * g).1).val Q₁ = ((g.1)⁻¹).val * aeval γ.1.val Q₁ * g.1.val := by
    have : (g⁻¹ * γ * g).1 = g.1⁻¹ * γ.1 * g.1 := by simp
    rw [this]
    exact aeval_conj _ _ _
  dsimp only
  let V := LinearMap.ker (Matrix.toLin' (aeval γ.1.val Q₁))
  let V' := LinearMap.ker (Matrix.toLin' (aeval ((g⁻¹ * γ * g : UL n w) : GLw n w).val Q₁))
  have hmem : ∀ x, x ∈ V' ↔ g.1.val *ᵥ x ∈ V := by
    intro x
    simp only [V, V', LinearMap.mem_ker, Matrix.toLin'_apply]
    rw [hM, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec]
    constructor
    · intro h
      have := congrArg (g.1.val *ᵥ ·) h
      simpa [Matrix.mulVec_mulVec, hinv'] using this
    · intro h
      rw [h, Matrix.mulVec_zero]
  have hinj : Function.Injective (Matrix.toLin' g.1.val) := by
    intro x y h
    have := congrArg (((g.1)⁻¹).val *ᵥ ·) h
    simpa [Matrix.toLin'_apply, Matrix.mulVec_mulVec, hinv] using this
  have hmap : V'.map (Matrix.toLin' g.1.val) = V := by
    ext x
    simp only [Submodule.mem_map, Matrix.toLin'_apply]
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact (hmem y).mp hy
    · intro hx
      refine ⟨((g.1)⁻¹).val *ᵥ x, ?_, ?_⟩
      · rw [hmem, Matrix.mulVec_mulVec, hinv', Matrix.one_mulVec]
        exact hx
      · rw [Matrix.mulVec_mulVec, hinv', Matrix.one_mulVec]
  let e : V' ≃ₗ[w.adicCompletion E] V :=
    (Submodule.equivMapOfInjective _ hinj V').trans (LinearEquiv.ofEq _ _ hmap)
  let b := Module.finBasis (w.adicCompletion E) V
  let b' := Module.finBasis (w.adicCompletion E) V'
  let c₀ := b'.map e
  let c := c₀.reindex (b.indexEquiv c₀).symm
  have hc₀ : ∀ i, (c₀ i : Fin n → w.adicCompletion E) = g.1.val *ᵥ (b' i : Fin n → w.adicCompletion E) := by
    intro i
    rfl
  have h1 : gram (cj w) (fun i => (b' i : Fin n → w.adicCompletion E)) =
      gram (cj w) (fun i => (c₀ i : Fin n → w.adicCompletion E)) := by
    simp only [hc₀]
    exact (gram_unitary (cj w) _ hg _).symm
  have h2 : (gram (cj w) (fun i => (c₀ i : Fin n → w.adicCompletion E))).det =
      (gram (cj w) (fun i => (c i : Fin n → w.adicCompletion E))).det := by
    have : gram (cj w) (fun i => (c i : Fin n → w.adicCompletion E)) =
        (gram (cj w) (fun i => (c₀ i : Fin n → w.adicCompletion E))).submatrix (b.indexEquiv c₀) (b.indexEquiv c₀) := by
      ext i j
      simp [ConjugationGramUnitary.gram, c, Module.Basis.reindex_apply]
    rw [this, Matrix.det_submatrix_equiv_self]
  let A := b.toMatrix c
  have hA : A.det ≠ 0 := Matrix.det_ne_zero_of_right_inverse (b.toMatrix_mul_toMatrix_flip c)
  have h3 : (gram (cj w) (fun i => (c i : Fin n → w.adicCompletion E))).det =
      cj w A.det * A.det * (gram (cj w) (fun i => (b i : Fin n → w.adicCompletion E))).det := by
    have hd : ((b.toMatrix c).map (cj w)).det = cj w A.det := by rw [RingHom.map_det]; rfl
    rw [gram_basis (cj w) V b c, Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose, hd]
    ring
  change (-1 : ℂ) ^ Formalism.UG.ordL (gram (cj w) (fun i => (b' i : Fin n → w.adicCompletion E))).det =
    (-1 : ℂ) ^ Formalism.UG.ordL (gram (cj w) (fun i => (b i : Fin n → w.adicCompletion E))).det
  rw [h1, h2, h3]
  exact negOne_zpow_ordL_mul (cj w) hv _ _ hA

end GlobalTheory.BCT
end
end

