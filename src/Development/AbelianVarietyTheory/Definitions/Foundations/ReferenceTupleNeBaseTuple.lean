module

public import Mathlib
public import Formalism.LocalRingCardinality.DataTheta
public import Formalism.LocalRingCardinality.RankBoundMonotoneInDimension
public import Development.AbelianVarietyTheory.Definitions.Foundations.TrueColumnChoicesHeckeCharReferenceEqOne

@[expose] public section

noncomputable section

open NumberField IsDedekindDomain Filter Topology

namespace GlobalTheory.Mem.Chr.TieModel

open Formalism.BasicNotions Formalism.FrobeniusOrbits

theorem emb_mul_indep {L I : Type} [Field L] [CharZero L] [Fintype I] (σ : I → L →+* ℂ) (hσ : Function.Injective σ)
    (m : I → ℤ) (h : ∀ k : L, k ≠ 0 → ∏ i, σ i k ^ m i = 1) : m = 0 := by
  classical
  have key : ∀ x : L, ∑ i, (m i : ℂ) * σ i x = 0 := by
    intro x
    let f : ℂ → ℂ := fun t => ∏ i, (1 + t * σ i x) ^ m i
    have hd : ∀ i ∈ (Finset.univ : Finset I),
        HasDerivAt (fun t : ℂ => (1 + t * σ i x) ^ m i) ((m i : ℂ) * σ i x) 0 := by
      intro i _
      have h1 : HasDerivAt (fun t : ℂ => 1 + t * σ i x) (σ i x) 0 := by
        simpa using ((hasDerivAt_id (0 : ℂ)).mul_const (σ i x)).const_add 1
      have h2 := (hasDerivAt_zpow (m i) ((fun t : ℂ => 1 + t * σ i x) 0) (Or.inl (by simp))).comp (0 : ℂ) h1
      simpa [Function.comp_def] using h2
    have hf : HasDerivAt f (∑ i, (m i : ℂ) * σ i x) 0 := by
      have := HasDerivAt.fun_finsetProd hd
      simpa [f] using this
    have hs := hasDerivAt_iff_tendsto_slope.1 hf
    have hu : Tendsto (fun n : ℕ => ((1 : ℂ) / ((n : ℂ) + 1))) atTop (𝓝[≠] 0) := by
      refine tendsto_nhdsWithin_iff.2 ⟨tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℂ), Eventually.of_forall fun n => ?_⟩
      exact one_div_ne_zero (Nat.cast_add_one_ne_zero n)
    have hfin : ∀ᶠ n : ℕ in atTop, (1 + (1 / ((n : L) + 1)) * x) ≠ 0 := by
      rw [← Nat.cofinite_eq_atTop]
      refine Set.Subsingleton.finite ?_
      intro a ha b hb
      simp only [Set.mem_compl_iff, Set.mem_setOf_eq, not_not] at ha hb
      have ha1 : ((a : L) + 1) ≠ 0 := Nat.cast_add_one_ne_zero a
      have hb1 : ((b : L) + 1) ≠ 0 := Nat.cast_add_one_ne_zero b
      field_simp at ha hb
      have : (a : L) = b := by linear_combination ha - hb
      exact_mod_cast this
    have h0 : Tendsto (fun n : ℕ => slope f 0 ((1 : ℂ) / ((n : ℂ) + 1))) atTop (𝓝 0) := by
      refine tendsto_const_nhds.congr' (hfin.mono fun n hn => ?_)
      have h1 := h _ hn
      have h2 : f ((1 : ℂ) / ((n : ℂ) + 1)) = 1 := by
        refine Eq.trans ?_ h1; simp [f]
      have h3 : f 0 = 1 := by simp [f]
      simp only [slope, h2, h3, vsub_self, smul_zero]
    exact tendsto_nhds_unique (hs.comp hu) h0
  have li := (linearIndependent_monoidHom L ℂ).comp (fun i => (σ i : L →* ℂ))
    (fun i j hij => hσ (RingHom.coe_monoidHom_injective hij))
  have := Fintype.linearIndependent_iff.1 li (fun i => (m i : ℂ)) (by
    funext x
    simpa [Finset.sum_apply] using key x)
  funext i
  exact_mod_cast this i

theorem unit_sq (z : ℂ) (hz : z ≠ 0) : (z / ((‖z‖ : ℝ) : ℂ)) ^ 2 = z / starRingEnd ℂ z := by
  have h1 : ((‖z‖ : ℝ) : ℂ) ≠ 0 := by exact_mod_cast norm_ne_zero_iff.2 hz
  have h2 : starRingEnd ℂ z ≠ 0 := by simpa using hz
  have h3 : z * starRingEnd ℂ z = ((‖z‖ : ℝ) : ℂ) ^ 2 := by
    rw [Complex.mul_conj, Complex.normSq_eq_norm_sq]; push_cast; ring
  field_simp
  rw [← h3]

theorem hasInf_unique {L I : Type} [Field L] [NumberField L] [Fintype I] (φ : I → L →+* ℂ) (h1 : Function.Injective φ)
    (h2 : ∀ i j, φ i ≠ (starRingEnd ℂ).comp (φ j)) {χ : HChar L} {n n' : I → ℤ} (h : χ.HasInf φ n) (h' : χ.HasInf φ n') :
    n = n' := by
  let σ : I ⊕ I → L →+* ℂ := Sum.elim φ fun i => (starRingEnd ℂ).comp (φ i)
  have hσ : Function.Injective σ := by
    rintro (i | i) (j | j) hij
    · exact congrArg _ (h1 hij)
    · exact absurd hij (h2 i j)
    · exact absurd hij.symm (h2 j i)
    · refine congrArg _ (h1 (RingHom.ext fun x => ?_))
      have := congrArg (fun f : L →+* ℂ => starRingEnd ℂ (f x)) hij
      simpa [σ] using this
  have := emb_mul_indep σ hσ (Sum.elim (n - n') (n' - n)) (fun k hk => by
    have e := (h (Units.mk0 k hk)).symm.trans (h' (Units.mk0 k hk))
    simp only [Units.val_mk0] at e
    have hne : ∀ i, φ i k ≠ 0 := fun i => by simpa using hk
    have hu : ∀ i, φ i k / ((‖φ i k‖ : ℝ) : ℂ) ≠ 0 := fun i =>
      div_ne_zero (hne i) (by exact_mod_cast norm_ne_zero_iff.2 (hne i))
    have e2 : ∏ i, (φ i k / ((‖φ i k‖ : ℝ) : ℂ)) ^ (n i - n' i) = 1 := by
      simp_rw [zpow_sub₀ (hu _)]
      rw [Finset.prod_div_distrib, e, div_self]
      exact Finset.prod_ne_zero_iff.2 fun i _ => zpow_ne_zero _ (hu i)
    have e3 := congrArg (· ^ 2) e2
    simp only [← Finset.prod_pow, one_pow] at e3
    rw [Fintype.prod_sum_type, ← Finset.prod_mul_distrib, ← e3]
    refine Finset.prod_congr rfl fun i _ => ?_
    rw [← zpow_natCast, ← zpow_mul, mul_comm (n i - n' i), zpow_mul, zpow_natCast, unit_sq _ (hne i), div_zpow]
    simp only [σ, Sum.elim_inl, Sum.elim_inr, Pi.sub_apply, RingHom.comp_apply]
    rw [div_eq_mul_inv, ← zpow_neg, neg_sub])
  funext i
  have := congrFun this (Sum.inl i)
  simpa [sub_eq_zero] using this

theorem inf_eq_one_of_order {L : Type} [Field L] [NumberField L] [_root_.NumberField.IsTotallyComplex L] {χ : HChar L} {n : ℕ} (hn : 0 < n)
    (h : χ.OrderDvd n) (k : Lˣ) : χ.inf k = 1 := by
  have hx : ∀ x, (χ.1 x) ^ n = 1 := fun x => congrArg (fun ξ : HChar L => ξ.1 x) h
  have hw : ∀ (w : InfinitePlace L) (y : (w.Completion)ˣ), χ.1 (infIdele L w y) = 1 := by
    intro w y
    let e := InfinitePlace.Completion.ringEquivComplexOfIsComplex (IsTotallyComplex.isComplex w)
    obtain ⟨z, hz⟩ := IsAlgClosed.exists_pow_nat_eq (e (y : w.Completion)) hn
    have hz' : (e.symm z) ^ n = y := by rw [← map_pow, hz]; simp
    have hz0 : e.symm z ≠ 0 := by
      intro h0; rw [h0, zero_pow hn.ne'] at hz'; exact y.ne_zero hz'.symm
    have : y = (Units.mk0 _ hz0) ^ n := Units.ext (by simp [hz'])
    rw [this, map_pow, map_pow, hx]
  show χ.1 (infDiag k) = 1
  unfold infDiag
  rw [MonoidHom.finsetProd_apply, map_prod]
  exact Finset.prod_eq_one fun w _ => hw w _

instance totallyComplexE {R : Ranks} (H : Formalism.BasicNotions.Host R) : IsTotallyComplex H.E := by
  haveI := H.isCMField_hostE
  infer_instance

theorem embTau_inj (D : D7) : Function.Injective (embTau D) := fun _ _ h =>
  D.eTau.injective (Subtype.ext ((factEmb D.R D.host).1.1 h))

theorem embTau_ne_conj (D : D7) (i j : D.what₂.Tau) : embTau D i ≠ (starRingEnd ℂ).comp (embTau D j) := by
  intro h
  have hi : embTau D i (D.host.sqd) = Complex.I * ((Real.sqrt D.host.d : ℝ) : ℂ) :=
    ((factEmb D.R D.host).2 _).2 (D.eTau i).2
  have hj : embTau D j (D.host.sqd) = Complex.I * ((Real.sqrt D.host.d : ℝ) : ℂ) :=
    ((factEmb D.R D.host).2 _).2 (D.eTau j).2
  rw [h, RingHom.comp_apply, hj, map_mul, Complex.conj_I, Complex.conj_ofReal] at hi
  have h0 : ((Real.sqrt D.host.d : ℝ) : ℂ) = 0 := by
    have : (2 * Complex.I) * ((Real.sqrt D.host.d : ℝ) : ℂ) = 0 := by linear_combination -hi
    exact (mul_eq_zero.1 this).resolve_left (mul_ne_zero two_ne_zero Complex.I_ne_zero)
  have hd : 0 < D.host.d := D.host.hyp.2.1.pos
  have : (0 : ℝ) < Real.sqrt D.host.d := Real.sqrt_pos.2 (by exact_mod_cast hd)
  exact this.ne' (by exact_mod_cast h0)

variable {D : D7} {C : CharFrame D} {nch : NChoice D}

end GlobalTheory.Mem.Chr.TieModel
