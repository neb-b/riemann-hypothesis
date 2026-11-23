module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0106
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsUniqueHcharOfFiniteOrder
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ExpoConjOfIsCsd
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.QminorSwapAdjacent
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0016
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsHalfPtIff
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0224
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0226
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.ModularJExpansionAndPolynomialAndIsIntegral
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.LatticeDeterminedByInvariants

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ArtinRestrictEqArtinNormSinglePlaceStatement
section
open NumberField IsDedekindDomain Neutral.B1 ReciprocityTheory.Neutral.Bridge.HCFR Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.L2.Host GlobalTheory.HeckeGal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.artin_restrict_eq_artin_norm_single_place : ∀ (E Ω : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
    (K : IntermediateField E Ω) [FiniteDimensional E K] [NumberField K] [IsAlgClosure K Ω]
    (art : Ideles E →* Gab E Ω) (artK : Ideles K →* Gab K Ω), IsGlobalArtin art → IsGlobalArtin artK →
    ∀ (v : HeightOneSpectrum (𝓞 E)) (W : HeightOneSpectrum (𝓞 K)),
      W.asIdeal.comap (algebraMap (𝓞 E) (𝓞 K)) = v.asIdeal →
      (∀ W' : HeightOneSpectrum (𝓞 K), W'.asIdeal.comap (algebraMap (𝓞 E) (𝓞 K)) = v.asIdeal → W' = W) →
      ∀ (y : Kˣ) (τ : G K Ω),
        toAb K Ω τ = artK (localIdele K W (Units.map (algebraMap K (W.adicCompletion K)).toMonoidHom y)) →
        toAb E Ω (τ.restrictScalars E) =
          art (localIdele E v (Units.map (algebraMap E (v.adicCompletion E)).toMonoidHom
            (Units.map (Algebra.norm E (S := K)) y))) := by
  first | exact @GlobalTheory.NormCompat.res_art_eq_art_norm | exact GlobalTheory.NormCompat.res_art_eq_art_norm | (intros; apply GlobalTheory.NormCompat.res_art_eq_art_norm <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CapCommuteRtInfGL
section
open NumberField IsDedekindDomain MeasureTheory Formalism.L2.Host GlobalTheory.CuspRep Formalism.REAL

namespace GlobalTheory.CapAdInv

section Algebra

variable {A : Type} [Ring A] [Algebra ℂ A]

theorem qdet_ad {n : ℕ} (E : Fin n → Fin n → A) (hE : GlRel E) (P Q : Matrix (Fin n) (Fin n) ℂ)
    (hQP : Q * P = 1) (u : ℂ) :
    qdet (fun a b => ∑ c, ∑ d, (P c a * Q b d) • E c d) u = qdet E u := by
  first
  | exact @_root_.GlobalTheory.QuantumMinorAdjacentSwap.qdet_conj
  | exact _root_.GlobalTheory.QuantumMinorAdjacentSwap.qdet_conj
  | (apply _root_.GlobalTheory.QuantumMinorAdjacentSwap.qdet_conj <;> assumption)
  | (intros; apply _root_.GlobalTheory.QuantumMinorAdjacentSwap.qdet_conj <;> assumption)
  | (intros; apply @_root_.GlobalTheory.QuantumMinorAdjacentSwap.qdet_conj <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.QuantumMinorAdjacentSwap.qdet_conj ..)

theorem qdet_semiconj {n : ℕ} (E E' : Fin n → Fin n → A) (R : A) (h : ∀ a b, R * E a b = E' a b * R) (u : ℂ) :
    R * qdet E u = qdet E' u * R := by
  have hp : ∀ {t : ℕ} (x y : Fin t → A), (∀ k, R * x k = y k * R) →
      R * (List.ofFn x).prod = (List.ofFn y).prod * R := by
    intro t
    induction t with
    | zero => simp
    | succ t ih =>
      intro x y h
      simp only [List.ofFn_succ, List.prod_cons]
      rw [← mul_assoc, h, mul_assoc, ih _ _ (fun k => h k.succ), mul_assoc]
  simp only [qdet, qminor, Finset.mul_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun σ _ => ?_
  rw [← mul_assoc, ← (Int.cast_commute _ R).eq, mul_assoc, mul_assoc, hp]
  intro k
  simp only [Tm, mul_add, add_mul, h]
  split_ifs
  · rw [Algebra.commutes]
  · simp

end Algebra

variable {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] {a : ℕ}

theorem rt_lie (y : GL (Fin a) (Cinf E)) (X : Matrix (Fin a) (Fin a) (Cinf E)) :
    rt E a (infGL E a y) * lie E a (toL X) = lie E a (toL (y.val * X * (y⁻¹).val)) * rt E a (infGL E a y) := by
  refine LinearMap.ext fun φ => Subtype.ext <| funext fun g => ?_
  change fderiv ℝ (chart φ.1 (g * infGL E a y)) (oneL E a) (toL X) =
    fderiv ℝ (chart (fun x => φ.1 (x * infGL E a y)) g) (oneL E a) (toL (y.val * X * (y⁻¹).val))
  have hd : DifferentiableAt ℝ (chart φ.1 g) (toL y.val) :=
    (contDiffAt_chart φ.2 g (val_mem_invSet y)).differentiableAt (by simp)
  have e1 : lmul (toL y.val) (oneL E a) = toL y.val := mul_one y.val
  have e2 : rmul (toL y.val) (oneL E a) = toL y.val := one_mul y.val
  rw [chart_mul, chart_rt_inf, fderiv_comp _ (by rw [e1]; exact hd) (lmul (toL y.val)).differentiableAt,
    fderiv_comp _ (by rw [e2]; exact hd) (rmul (toL y.val)).differentiableAt, e1, e2,
    ContinuousLinearMap.fderiv, ContinuousLinearMap.fderiv]
  exact congrArg (fun Z => fderiv ℝ (chart φ.1 g) (toL y.val) (toL Z)) (Units.inv_mul_cancel_right (y.val * X) y).symm


omit [NumberField E] [_root_.NumberField.IsTotallyComplex E] in
theorem mul_atEmb (τ : E →+* ℂ) (x : Cinf E) (z : ℂ) : x * atEmb τ z = atEmb τ (coord τ x * z) := by
  classical
  funext w
  unfold atEmb coord
  by_cases hw : w = InfinitePlace.mk τ
  · subst hw; split_ifs <;> simp
  · simp [Pi.single_eq_of_ne hw]

theorem rt_lieS (y : GL (Fin a) (Cinf E)) (τ : E →+* ℂ) (i j : Fin a) (z : ℂ) :
    rt E a (infGL E a y) * lieS E a i j (atEmb τ z) =
      (∑ k, ∑ l, lieS E a k l (atEmb τ (coord τ (y.val k i) * coord τ ((y⁻¹).val j l) * z))) *
        rt E a (infGL E a y) := by
  rw [lieS_apply, rt_lie]
  congr 1
  have e : y.val * Matrix.single i j (atEmb τ z) * (y⁻¹).val =
      ∑ k, ∑ l, Matrix.single k l (atEmb τ (coord τ (y.val k i) * coord τ ((y⁻¹).val j l) * z)) := by
    rw [Matrix.matrix_eq_sum_single (y.val * Matrix.single i j (atEmb τ z) * (y⁻¹).val)]
    refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => ?_
    congr 1
    rw [← map_mul, ← mul_atEmb]
    simp [Matrix.mul_apply, Matrix.single_apply, ite_and, mul_right_comm]
  rw [e]
  let L : Matrix (Fin a) (Fin a) (Cinf E) →ₗ[ℝ] Module.End ℂ (Sm E a) := lie E a
  have key : ∀ f : Fin a → Fin a → Matrix (Fin a) (Fin a) (Cinf E), L (∑ k, ∑ l, f k l) = ∑ k, ∑ l, L (f k l) :=
    fun f => by simp only [map_sum]
  exact key _

theorem rt_Eop (y : GL (Fin a) (Cinf E)) (τ : E →+* ℂ) (i j : Fin a) :
    rt E a (infGL E a y) * Eop τ i j =
      (∑ k, ∑ l, (coord τ (y.val k i) * coord τ ((y⁻¹).val j l)) • Eop τ k l) * rt E a (infGL E a y) := by
  rw [Eop, mul_smul_comm, mul_sub, mul_smul_comm, rt_lieS, rt_lieS, ← smul_mul_assoc, ← sub_mul, ← smul_mul_assoc]
  congr 1
  simp only [Finset.smul_sum, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => ?_
  generalize coord τ (y.val k i) * coord τ ((y⁻¹).val j l) = c
  have hL : ∀ w : ℂ, lieS E a k l (atEmb τ w) =
      (w.re : ℂ) • lieS E a k l (atEmb τ 1) + (w.im : ℂ) • lieS E a k l (atEmb τ Complex.I) := fun w => by
    rw [atEmb_eq τ w, map_add (f := _), map_smul, map_smul]
    rfl
  rw [hL (c * 1), hL (c * Complex.I), Eop]
  conv_rhs => rw [← Complex.re_add_im c]
  simp only [mul_one, Complex.mul_I_re, Complex.mul_I_im, Complex.ofReal_neg]
  match_scalars
  · ring
  · linear_combination ((c.im : ℂ) / 2) * Complex.I_mul_I

theorem cap_commute_rt_infGL : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a : ℕ) (τ : E →+* ℂ) (u : ℂ)
    (y : GL (Fin a) (Cinf E)), Commute (cap (a := a) τ u) (rt E a (infGL E a y)) := by
  intro E _ _ _ a τ u y
  have h := qdet_semiconj _ _ _ (rt_Eop y τ) (u + ((a : ℂ) - 1) / 2)
  have hQP : ((y⁻¹).val.map (coord τ)) * (y.val.map (coord τ)) = 1 := by
    rw [← Matrix.map_mul, Units.inv_mul]; simp
  have h2 := qdet_ad _ (glRel_Eop τ) _ _ hQP (u + ((a : ℂ) - 1) / 2)
  simp only [Matrix.map_apply] at h2
  rw [h2] at h
  exact h.symm

end GlobalTheory.CapAdInv
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CmDataIsCMExtAndGramIsHermND
section
open Formalism.BasicNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix GlobalTheory.Mem.Vol
open scoped TensorProduct

namespace GlobalTheory.Mem.Vol

theorem hspace_gram_det_ne_zero {E : Type} [Field E] [NumberField E] [StarRing E] (W : HSpace E) :
    W.gram.det ≠ 0 := by
  classical
  intro h0
  obtain ⟨v, hv, hmul⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr h0
  have hb : ∀ i, W.hT (W.frame i) (∑ j, v j • W.frame j) = 0 := by
    intro i
    have := congrFun hmul i
    simp only [Matrix.mulVec, dotProduct, HSpace.gram, Pi.zero_apply] at this
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum, ← this]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [map_smul, smul_eq_mul, mul_comm]
  have hz : (∑ j, v j • W.frame j) = 0 := by
    refine W.nondeg.2 _ fun x => ?_
    set_option synthInstance.maxHeartbeats 100000 in
      rw [← W.frame.sum_repr x, map_sum W.hT, LinearMap.sum_apply]
    refine Finset.sum_eq_zero fun i _ => ?_
    rw [LinearMap.map_smulₛₗ, LinearMap.smul_apply, hb, smul_zero]
  apply hv
  funext j
  exact Fintype.linearIndependent_iff.mp W.frame.linearIndependent v hz j

theorem cmData_isCMExt_and_gram_isHermND : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E] (cm : CMData F E), IsCMExt F E cm.sig ∧ ∀ W : HSpace E, IsHermND cm.sig W.gram := by
  intro F E _ _ _ _ _ _ cm
  refine ⟨⟨cm.totReal, cm.cmUnram.1, cm.deg2, fun τ x => cm.cmUnram.2.1 τ x⟩, fun W => ⟨fun i j => ?_, hspace_gram_det_ne_zero W⟩⟩
  exact W.herm.eq (W.frame j) (W.frame i)

end GlobalTheory.Mem.Vol
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CmInverseHalfDifferentMulRelativeDifferent
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric NumberField GlobalTheory.Mem.Per
open scoped nonZeroDivisors Pointwise UpperHalfPlane

namespace GlobalTheory.Mem.PerField

theorem ideal_eq_of_pow_eq {A : Type} [CommRing A] [IsDedekindDomain A] {I J : Ideal A} {n : ℕ} (hn : n ≠ 0)
    (h : I ^ n = J ^ n) : I = J := by
  apply le_antisymm
  · rw [← Ideal.dvd_iff_le, ← UniqueFactorizationMonoid.pow_dvd_pow_iff_dvd hn, h]
  · rw [← Ideal.dvd_iff_le, ← UniqueFactorizationMonoid.pow_dvd_pow_iff_dvd hn, h]

theorem exists_pow_eq_span {E : Type} [Field E] [NumberField E] (I : Ideal (𝓞 E)) :
    ∃ n : ℕ, n ≠ 0 ∧ ∃ β : 𝓞 E, I ^ n = Ideal.span {β} := by
  classical
  by_cases hI : I = ⊥
  · exact ⟨1, one_ne_zero, 0, by simp [hI]⟩
  have hI' : I ∈ (Ideal (𝓞 E))⁰ := mem_nonZeroDivisors_of_ne_zero hI
  refine ⟨Fintype.card (ClassGroup (𝓞 E)), Fintype.card_ne_zero, ?_⟩
  have h1 : ClassGroup.mk0 (⟨I, hI'⟩ ^ Fintype.card (ClassGroup (𝓞 E))) = 1 := by
    rw [map_pow, pow_card_eq_one]
  have h2 := (ClassGroup.mk0_eq_one_iff (pow_mem hI' (Fintype.card (ClassGroup (𝓞 E))))).1 h1
  exact ⟨_, (Ideal.span_singleton_generator _).symm⟩

theorem span_root {E L : Type} [Field E] [NumberField E] [Field L] [NumberField L] (f : E →+* L)
    {I : Ideal (𝓞 E)} {n : ℕ} (hn : n ≠ 0) {β : 𝓞 E} (h : I ^ n = Ideal.span {β}) {x : L}
    (hx : x ^ n = f β) :
    Submodule.span (𝓞 L) {x} = Submodule.span (𝓞 L) {y | ∃ c ∈ I, y = f (c : E)} := by
  have hi : IsIntegral ℤ x := by
    refine IsIntegral.of_pow (Nat.pos_of_ne_zero hn) ?_
    rw [hx]
    exact (RingOfIntegers.isIntegral_coe β).map f.toIntAlgHom
  let x' : 𝓞 L := ⟨x, hi⟩
  let f' : 𝓞 E →+* 𝓞 L := RingOfIntegers.mapRingHom f
  have e : Ideal.span {x'} = I.map f' := by
    apply ideal_eq_of_pow_eq hn
    rw [← Ideal.map_pow, h, Ideal.map_span, Set.image_singleton, Ideal.span_singleton_pow]
    congr 2
    exact RingOfIntegers.ext hx
  have e2 := congrArg (Submodule.map (Algebra.linearMap (𝓞 L) L)) e
  rw [Ideal.map, Ideal.span, Ideal.span, Submodule.map_span, Submodule.map_span, Set.image_singleton] at e2
  refine e2.trans ?_
  congr 1
  ext y
  constructor
  · rintro ⟨_, ⟨c, hc, rfl⟩, rfl⟩
    exact ⟨c, hc, rfl⟩
  · rintro ⟨c, hc, rfl⟩
    exact ⟨_, ⟨c, hc, rfl⟩, rfl⟩

variable {R : Ranks} (H : Host R)

theorem cmInverseHalfDifferent_mul_relativeDifferent :
    H.AA0 * (differentIdeal (𝓞 H.K) (𝓞 H.E) : FractionalIdeal (𝓞 H.E)⁰ H.E) =
      ((H.conj • H.𝔟 : Ideal (𝓞 H.E)) : FractionalIdeal (𝓞 H.E)⁰ H.E) := by
  have hd : differentIdeal (𝓞 H.K) (𝓞 H.E) ≠ ⊥ := differentIdeal_ne_bot
  have h1 : differentIdeal (𝓞 H.K) (𝓞 H.E) = H.𝔟 * (H.conj • H.𝔟) := H.𝔟_spec.1
  have hb : H.𝔟 ≠ ⊥ := by
    intro h0
    apply hd
    rw [h1, h0, Ideal.bot_mul]
  rw [h1, FractionalIdeal.coeIdeal_mul, Host.AA0, ← mul_assoc,
    inv_mul_cancel₀ (FractionalIdeal.coeIdeal_ne_zero.2 hb), one_mul]

theorem ellLat_eq {LL : Type} [Field LL] [NumberField LL] (embE : H.E →+* LL) (g : R.GG) :
    ellLat H embE g = Submodule.span (𝓞 LL)
      {y | ∃ c ∈ (H.conj • H.𝔟 : Ideal (𝓞 H.E)), y = (embE.comp (H.sigmaOf g : H.E →+* H.E)) (c : H.E)} := by
  apply le_antisymm
  · refine Submodule.span_mono ?_
    rintro _ ⟨a, ha, b, hb, rfl⟩
    have : a * (b : H.E) ∈ H.AA0 * (differentIdeal (𝓞 H.K) (𝓞 H.E) : FractionalIdeal (𝓞 H.E)⁰ H.E) :=
      FractionalIdeal.mul_mem_mul ha (FractionalIdeal.mem_coeIdeal_of_mem _ hb)
    rw [cmInverseHalfDifferent_mul_relativeDifferent] at this
    obtain ⟨c, hc, e⟩ := (FractionalIdeal.mem_coeIdeal _).1 this
    exact ⟨c, hc, by rw [← e]; rfl⟩
  · refine Submodule.span_le.2 ?_
    rintro _ ⟨c, hc, rfl⟩
    have : (c : H.E) ∈ H.AA0 * (differentIdeal (𝓞 H.K) (𝓞 H.E) : FractionalIdeal (𝓞 H.E)⁰ H.E) := by
      rw [cmInverseHalfDifferent_mul_relativeDifferent]
      exact FractionalIdeal.mem_coeIdeal_of_mem _ hc
    refine FractionalIdeal.mul_induction_on
      (C := fun z => (embE.comp (H.sigmaOf g : H.E →+* H.E)) z ∈ ellLat H embE g) this ?_ ?_
    · intro a ha b hb
      obtain ⟨b', hb', rfl⟩ := (FractionalIdeal.mem_coeIdeal _).1 hb
      exact Submodule.subset_span ⟨a, ha, b', hb', rfl⟩
    · intro x y hx hy
      rw [map_add (f := _)]
      exact add_mem hx hy

theorem mem_baseLat (w : ℂ) : w ∈ baseLat H ↔ ∃ c ∈ H.ccK, w = H.φ₀ (((c : H.K) : H.E)) := by
  constructor
  · intro hw
    induction hw using AddSubgroup.closure_induction with
    | mem x hx => exact hx
    | zero => exact ⟨0, H.ccK.zero_mem, by simp⟩
    | add x y _ _ hx hy =>
      obtain ⟨c, hc, rfl⟩ := hx
      obtain ⟨c', hc', rfl⟩ := hy
      exact ⟨c + c', H.ccK.add_mem hc hc', by simp⟩
    | neg x _ hx =>
      obtain ⟨c, hc, rfl⟩ := hx
      exact ⟨-c, H.ccK.neg_mem hc, by simp⟩
  · exact fun hw => AddSubgroup.subset_closure hw

theorem finrank_K : Module.finrank ℚ H.K = 2 :=
  Formalism.FrobeniusOrbits.SplitK.finrank_K H.hyp.2.1.pos (H.sqd_sq)

theorem discr_K : NumberField.discr H.K = -(H.d : ℤ) :=
  discr_eq_neg_of_sq_eq (finrank_K H) H.hyp.2.1.squarefree
    (by have := H.hyp.2.2.2.1; omega)
    (Formalism.FrobeniusOrbits.SplitK.bK_sq (H.sqd_sq))

theorem exists_periodPair_baseLat : ∃ L : PeriodPair, ∀ z, z ∈ baseLat H ↔ z ∈ L.lattice := by
  let σ : H.K →+* ℂ := H.φ₀.comp H.K.val.toRingHom
  let I : (Ideal (𝓞 H.K))⁰ := ⟨H.ccK, mem_nonZeroDivisors_of_ne_zero H.ccK_ne_bot⟩
  obtain ⟨L, hL⟩ := QuadraticZeta.exists_periodPair (finrank_K H) (discr_K H) σ
    (FractionalIdeal.mk0 H.K I)
  refine ⟨L, fun z => ?_⟩
  rw [mem_baseLat, ← SetLike.mem_coe, hL]
  constructor
  · rintro ⟨c, hc, rfl⟩
    exact ⟨(c : H.K), FractionalIdeal.mem_coeIdeal_of_mem _ hc, rfl⟩
  · rintro ⟨y, hy, rfl⟩
    obtain ⟨c, hc, rfl⟩ := (FractionalIdeal.mem_coeIdeal _).1 hy
    exact ⟨c, hc, rfl⟩

theorem isIntegral_jLat : IsIntegral ℤ (jLat (baseLat H)) := by
  obtain ⟨L, hL⟩ := exists_periodPair_baseLat H
  have hd := GlobalTheory.LatticeInvariants.invariants_dictionary L _ hL
  obtain ⟨a, τ, ha, h⟩ := exists_lattice_eq_mul_tau L
  rw [jLat, TaylorLogMetric.discr, hd.1, hd.2.1, g₂_cube_div_eq_modularJ ha h]
  refine isIntegral_modularJ_of_ringOfIntegers (finrank_K H) (H.φ₀.comp H.K.val.toRingHom) fun α x hx ↦ ?_
  have key : ∀ y : ℂ, y ∈ Submodule.span ℤ {(τ : ℂ), 1} ↔ a * y ∈ L.lattice := fun y ↦ by
    rw [h, Submodule.mem_span_pair]
    simp [mul_right_inj' ha]
  rw [key, ← hL, mem_baseLat] at hx ⊢
  obtain ⟨c, hc, e⟩ := hx
  refine ⟨α * c, H.ccK.mul_mem_left α hc, ?_⟩
  rw [mul_left_comm, e]
  simp

theorem exists_fieldOK : ∀ (R : Ranks) (H : Host R) (M : IntermediateField ℚ ℂ), FiniteDimensional ℚ M → ∃ M' : IntermediateField ℚ ℂ, FiniteDimensional ℚ M' ∧ M ≤ M' ∧ ∀ (LL : Type) [Field LL] [NumberField LL] (emb : LL →+* ℂ) (embE : H.E →+* LL), emb.comp embE = H.φ₀ → (∀ x ∈ M', ∃ a, emb a = x) → FieldOK H emb embE := by
  intro R H M hM
  obtain ⟨n, hn, β, hβ⟩ := exists_pow_eq_span (H.conj • H.𝔟 : Ideal (𝓞 H.E))
  choose z hz using fun σ : H.E ≃ₐ[ℚ] H.E =>
    IsAlgClosed.exists_pow_nat_eq (H.φ₀ (σ (β : H.E))) (Nat.pos_of_ne_zero hn)
  let T : Set ℂ := insert (jLat (baseLat H)) (Set.range z)
  have : Finite T := (Set.finite_range z).insert _
  have hT : FiniteDimensional ℚ (IntermediateField.adjoin ℚ T) := by
    refine IntermediateField.finiteDimensional_adjoin fun x hx ↦ ?_
    rcases hx with rfl | ⟨σ, rfl⟩
    · exact (isIntegral_jLat H).tower_top
    · refine IsIntegral.of_pow (Nat.pos_of_ne_zero hn) ?_
      rw [hz]
      exact (Algebra.IsIntegral.isIntegral (R := ℚ) (σ (β : H.E))).map H.φ₀.toRatAlgHom
  refine ⟨M ⊔ IntermediateField.adjoin ℚ T, inferInstance, le_sup_left, ?_⟩
  intro LL _ _ emb embE he hM'
  have hT' : ∀ x ∈ T, ∃ a, emb a = x := fun x hx =>
    hM' x ((le_sup_right : _ ≤ M ⊔ _) (IntermediateField.subset_adjoin ℚ T hx))
  refine ⟨hT' _ (Set.mem_insert _ _), fun g => ?_⟩
  obtain ⟨x, hx⟩ := hT' _ (Set.mem_insert_of_mem _ ⟨H.sigmaOf g, rfl⟩)
  refine ⟨x, ?_⟩
  rw [IsGen, ellLat_eq]
  refine span_root _ hn hβ ?_
  apply emb.injective
  rw [map_pow, hx, hz, ← he]
  rfl

end GlobalTheory.Mem.PerField
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CommuteCapOfCommuteEop
section
open NumberField IsDedekindDomain MeasureTheory Formalism.L2.Host GlobalTheory.CuspRep

namespace GlobalTheory.CuspRep

variable {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] {a : ℕ}

theorem commute_cap_of_commute_Eop (τ : E →+* ℂ) (u : ℂ) (z : Module.End ℂ (Sm E a))
    (h : ∀ i j, Commute (Eop τ i j) z) : Commute (cap τ u) z := by
  let S : Subalgebra ℂ (Module.End ℂ (Sm E a)) := Subalgebra.centralizer ℂ {z}
  have hS : ∀ x, x ∈ S ↔ Commute x z := fun x => by
    simp only [S, Subalgebra.mem_centralizer_iff, Set.mem_singleton_iff, forall_eq]
    exact ⟨fun h => h.symm, fun h => h.symm⟩
  have hE : ∀ i j, Eop τ i j ∈ S := fun i j => (hS _).2 (h i j)
  refine (hS _).1 ?_
  refine S.sum_mem fun σ _ => S.mul_mem (intCast_mem S _) (S.list_prod_mem fun x hx => ?_)
  obtain ⟨k, rfl⟩ := List.mem_ofFn.1 hx
  refine S.add_mem ?_ (hE _ _)
  split_ifs
  · exact S.algebraMap_mem _
  · exact S.zero_mem

theorem commute_cap_Eop (τ τ' : E →+* ℂ) (u : ℂ) (i j : Fin a) : Commute (cap τ u) (Eop τ' i j) := by
  by_cases h : τ = τ'
  · subst h; exact cap_comm τ u i j
  · exact commute_cap_of_commute_Eop τ u _ fun k l => Eop_comm h k l i j

theorem lieS_atEmb_one (τ : E →+* ℂ) (i j : Fin a) :
    lieS E a i j (atEmb τ 1) = Eop τ i j + Eop (ComplexEmbedding.conjugate τ) i j := by
  have e : atEmb τ (-Complex.I) = -atEmb τ Complex.I := by
    rw [atEmb_eq]; simp
  simp only [Eop, atEmb_conj, map_one, Complex.conj_I, e, map_neg]
  match_scalars <;> ring

theorem lieS_atEmb_I (τ : E →+* ℂ) (i j : Fin a) :
    lieS E a i j (atEmb τ Complex.I) = Complex.I • (Eop τ i j - Eop (ComplexEmbedding.conjugate τ) i j) := by
  have e : atEmb τ (-Complex.I) = -atEmb τ Complex.I := by
    rw [atEmb_eq]; simp
  simp only [Eop, atEmb_conj, map_one, Complex.conj_I, e, map_neg]
  match_scalars <;> ring_nf <;> simp

theorem commute_cap_lieS (τ : E →+* ℂ) (u : ℂ) (i j : Fin a) (x : Cinf E) : Commute (cap τ u) (lieS E a i j x) := by
  classical
  have hx : x = ∑ w : InfinitePlace E, atEmb w.embedding (x w) := by
    conv_lhs => rw [← Finset.univ_sum_single x]
    refine Finset.sum_congr rfl fun w _ => ?_
    unfold atEmb
    rw [InfinitePlace.mk_embedding, if_pos rfl]
  set_option synthInstance.maxHeartbeats 100000 in
    rw [hx, map_sum]
  refine Commute.sum_right _ _ _ fun w _ => ?_
  rw [atEmb_eq, map_add (f := _), map_smul, map_smul, lieS_atEmb_one, lieS_atEmb_I]
  exact (((commute_cap_Eop τ _ u i j).add_right (commute_cap_Eop τ _ u i j)).smul_right _).add_right
    ((((commute_cap_Eop τ _ u i j).sub_right (commute_cap_Eop τ _ u i j)).smul_right _).smul_right _)

theorem commute_cap_lie (τ : E →+* ℂ) (u : ℂ) (X : Lie E a) : Commute (cap τ u) (lie E a X) := by
  have hX : lie E a X = ∑ i, ∑ j, lieS E a i j (X i j) := by
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [lieS_apply, ← map_sum]
    exact congrArg _ (Matrix.matrix_eq_sum_single (Matrix.of X))
  rw [hX]
  exact Commute.sum_right _ _ _ fun i _ => Commute.sum_right _ _ _ fun j _ => commute_cap_lieS τ u i j _

theorem commute_cap_finRep (τ : E →+* ℂ) (u : ℂ) (k : GL (Fin a) (Af E)) : Commute (cap τ u) (finRep E a k) := by
  have h : ∀ i j x, Commute (lieS E a i j x) (finRep E a k) := fun i j x => lie_rt_fin _ k
  exact commute_cap_of_commute_Eop τ u _ fun i j =>
    ((h i j _).sub_left ((h i j _).smul_left _)).smul_left _

end GlobalTheory.CuspRep
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ContinuousOfIsOpenStab
section
open NumberField IsDedekindDomain MeasureTheory Formalism.L2.Host GlobalTheory.CuspRep Topology Matrix

namespace GlobalTheory.CuspRep.ContAut

variable (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a : ℕ)


omit [_root_.NumberField.IsTotallyComplex E] in
theorem continuous_pFin : Continuous (pFin E) := continuous_snd

theorem continuous_pInf : Continuous (pInf E) :=
  continuous_pi fun w =>
    (InfinitePlace.Completion.isometryEquivComplexOfIsComplex (IsTotallyComplex.isComplex w)).continuous.comp
      ((continuous_apply w).comp continuous_fst)


omit [_root_.NumberField.IsTotallyComplex E] in
theorem continuous_map_pFin :
    Continuous (GeneralLinearGroup.map (pFin E) : GA E a → GL (Fin a) (Af E)) :=
  Continuous.units_map _ (continuous_id.matrix_map (continuous_pFin E))

theorem continuous_map_pInf :
    Continuous (GeneralLinearGroup.map (pInf E) : GA E a → GL (Fin a) (Cinf E)) :=
  Continuous.units_map _ (continuous_id.matrix_map (continuous_pInf E))

theorem continuous_of_isOpen_stab : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a : ℕ) (φ : Sm E a),
    IsOpen {k | finRep E a k φ = φ} → Continuous φ.1 := by
  intro E _ _ _ a φ hφ
  refine continuous_iff_continuousAt.2 fun g => ?_
  have hm : Continuous fun x : GA E a => g⁻¹ * x := continuous_const.mul continuous_id
  have h1 : Continuous fun x : GA E a => toL (GeneralLinearGroup.map (pInf E) (g⁻¹ * x)).val :=
    (Units.continuous_val (M := Matrix (Fin a) (Fin a) (Cinf E))).comp ((continuous_map_pInf E a).comp hm)
  have h2 : ContinuousAt (fun x : GA E a => chart φ.1 g (toL (GeneralLinearGroup.map (pInf E) (g⁻¹ * x)).val)) g :=
    ContinuousAt.comp (f := fun x : GA E a => toL (GeneralLinearGroup.map (pInf E) (g⁻¹ * x)).val)
      (contDiffAt_chart φ.2 g (val_mem_invSet _)).continuousAt h1.continuousAt
  refine h2.congr ?_
  have h3 : {x : GA E a | finRep E a (GeneralLinearGroup.map (pFin E) (g⁻¹ * x)) φ = φ} ∈ 𝓝 g :=
    (hφ.preimage ((continuous_map_pFin E a).comp hm)).mem_nhds (by simp)
  filter_upwards [h3] with x hx
  rw [chart_val]
  conv_lhs => rw [← hx]
  change φ.1 (g * infGL E a _ * finGL E a _) = _
  rw [mul_assoc, infGL_mul_finGL, mul_inv_cancel_left]

end GlobalTheory.CuspRep.ContAut
end

