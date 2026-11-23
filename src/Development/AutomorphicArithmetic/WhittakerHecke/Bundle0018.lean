module

public import Development.AutomorphicArithmetic.Foundations.Convolution.SplitEigenfunctions.CharacterNorms.Bundle0001
public import GroundTheory.GlobalFields.TateThesis.AdelicChar
public import GroundTheory.GlobalFields.IdeleGroups.Bundle0002
public import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.UnitaryActions.Bundle0002
public import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.IsotypicQuotients.WfCusp
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.CmBridge
public import GroundTheory.GlobalFields.TateThesis.AdelicCharDual

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.WhittakerHecke.ExistsNatMulIntegralAtAllFinitePlaces
section
open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2 UpperTheory.ConvolutionTheory.RankTwoDescent UpperTheory.ConvolutionTheory.RankTwoDescent.Xg
open scoped Classical
open UpperTheory.ConvolutionTheory.R2.G (FS2 Rw nE row)
open UpperTheory.V.Af.Smo (EigAt)
open scoped ComplexOrder

theorem UpperTheory.exists_nat_mul_integral_at_all_finite_places :
    ∀ (E : Type) [Field E] [NumberField E] (θ : E), ∃ d : ℕ, 0 < d ∧ ∀ e : ℕ, d ∣ e → ∀ w : H.P E, Valued.v (H.cp w (rt ((e : E) * θ))) ≤ 1 := by
  intro E _ _ θ
  obtain ⟨y, hy0, hy⟩ := ((IsFractionRing.isAlgebraic_iff ℤ ℚ E).2 (Algebra.IsAlgebraic.isAlgebraic (R := ℚ) θ)).exists_integral_multiple
  have hy' : IsIntegral ℤ ((y : E) * θ) := by
    simpa [zsmul_eq_mul] using hy
  have h1 : IsIntegral ℤ ((y.natAbs : E) * θ) := by
    rcases Int.natAbs_eq y with h | h
    · have hc : ((y.natAbs : E)) = (y : E) := by
        conv_rhs => rw [h]
        simp
      rw [hc]
      exact hy'
    · have hc : ((y.natAbs : E)) = -(y : E) := by
        conv_rhs => rw [h]
        simp
      rw [hc, neg_mul]
      exact hy'.neg
  refine ⟨y.natAbs, Int.natAbs_pos.2 hy0, ?_⟩
  rintro e ⟨k, rfl⟩ w
  have hint : IsIntegral ℤ (((y.natAbs * k : ℕ) : E) * θ) := by
    have he : (((y.natAbs * k : ℕ) : E) * θ) = (k : E) * ((y.natAbs : E) * θ) := by
      push_cast
      ring
    rw [he]
    have hk : IsIntegral ℤ (k : E) := by
      simpa using isIntegral_algebraMap (R := ℤ) (A := E) (x := (k : ℤ))
    exact hk.mul h1
  have hm := coe_algebraMap_mem_adicCompletionIntegers w (⟨_, hint⟩ : 𝓞 E)
  exact (HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).mp hm
end

-- bundled from Development.AutomorphicArithmetic.WhittakerHecke.ExistsPrincipalCongruenceLevelInvariant
section
open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2 UpperTheory.ConvolutionTheory.RankTwoDescent UpperTheory.ConvolutionTheory.RankTwoDescent.Xg
open scoped Classical
open UpperTheory.ConvolutionTheory.R2.G (FS2 Rw nE row)
open UpperTheory.V.Af.Smo (EigAt)
open scoped ComplexOrder

private theorem mat_nhds {R : Type} [TopologicalSpace R] [AddGroup R] [IsTopologicalAddGroup R]
    (t : Set (Matrix (Fin 2) (Fin 2) R)) (c : Matrix (Fin 2) (Fin 2) R) (ht : t ∈ 𝓝 c) :
    ∃ W ∈ 𝓝 (0 : R), ∀ m : Matrix (Fin 2) (Fin 2) R, (∀ i j, m i j - c i j ∈ W) → m ∈ t := by
  have hc : ContinuousAt (fun e : Fin 2 → Fin 2 → R => (Matrix.of fun i j => e i j + c i j : Matrix (Fin 2) (Fin 2) R)) 0 := by
    refine Continuous.continuousAt ?_
    refine continuous_matrix fun i j => ?_
    exact ((continuous_apply j).comp (continuous_apply i)).add continuous_const
  have h0 : (fun e : Fin 2 → Fin 2 → R => (Matrix.of fun i j => e i j + c i j : Matrix (Fin 2) (Fin 2) R)) ⁻¹' t ∈ 𝓝 (0 : Fin 2 → Fin 2 → R) :=
    hc.preimage_mem_nhds (by
      have : (Matrix.of fun i j => (0 : Fin 2 → Fin 2 → R) i j + c i j : Matrix (Fin 2) (Fin 2) R) = c := by
        ext i j; simp
      rw [this]; exact ht)
  rw [nhds_pi, Filter.mem_pi] at h0
  obtain ⟨I, -, t1, ht1, hI⟩ := h0
  have ht2 : ∀ i, ∃ W ∈ 𝓝 (0 : R), ∀ m : Fin 2 → R, (∀ j, m j ∈ W) → m ∈ t1 i := fun i => by
    have h := ht1 i
    rw [Pi.zero_apply, nhds_pi, Filter.mem_pi] at h
    obtain ⟨J, -, s, hs, hJ⟩ := h
    exact ⟨⋂ j, s j, Filter.iInter_mem.2 hs, fun m hm => hJ fun j _ => Set.mem_iInter.1 (hm j) j⟩
  choose W hW hWt using ht2
  refine ⟨⋂ i, W i, Filter.iInter_mem.2 hW, fun m hm => ?_⟩
  have : (fun i j => m i j - c i j) ∈ (fun e : Fin 2 → Fin 2 → R => (Matrix.of fun i j => e i j + c i j : Matrix (Fin 2) (Fin 2) R)) ⁻¹' t :=
    hI fun i _ => hWt i _ fun j => Set.mem_iInter.1 (hm i j) i
  have e : (Matrix.of fun i j => (m i j - c i j) + c i j : Matrix (Fin 2) (Fin 2) R) = m := by
    ext i j; simp
  change (Matrix.of fun i j => (m i j - c i j) + c i j : Matrix (Fin 2) (Fin 2) R) ∈ t at this
  rwa [e] at this

private theorem gl_nhds {R : Type} [CommRing R] [TopologicalSpace R] [IsTopologicalRing R]
    (V : Set (GL (Fin 2) R)) (hV : V ∈ 𝓝 (1 : GL (Fin 2) R)) :
    ∃ W ∈ 𝓝 (0 : R), ∀ k : GL (Fin 2) R, (∀ i j, k.val i j - (1 : Matrix (Fin 2) (Fin 2) R) i j ∈ W) →
      (∀ i j, (k⁻¹).val i j - (1 : Matrix (Fin 2) (Fin 2) R) i j ∈ W) → k ∈ V := by
  rw [Units.isInducing_embedProduct.nhds_eq_comap, Filter.mem_comap] at hV
  obtain ⟨t, ht, hts⟩ := hV
  rw [map_one] at ht
  have ht' : t ∈ 𝓝 ((1 : Matrix (Fin 2) (Fin 2) R), MulOpposite.op (1 : Matrix (Fin 2) (Fin 2) R)) := ht
  obtain ⟨u, hu, w, hw, huw⟩ := mem_nhds_prod_iff.1 ht'
  have hw' : MulOpposite.op ⁻¹' w ∈ 𝓝 (1 : Matrix (Fin 2) (Fin 2) R) :=
    MulOpposite.continuous_op.continuousAt.preimage_mem_nhds hw
  obtain ⟨W1, hW1, h1⟩ := mat_nhds u 1 hu
  obtain ⟨W2, hW2, h2⟩ := mat_nhds _ 1 hw'
  refine ⟨W1 ∩ W2, Filter.inter_mem hW1 hW2, fun k hk hk' => hts ?_⟩
  exact huw (Set.mk_mem_prod (h1 _ fun i j => (hk i j).1) (h2 _ fun i j => (hk' i j).2))

private theorem pInf_zero {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (x : A E) (hx : x.1 = 0) : pInf E x = 0 := by
  change (infEq E).symm x.1 = 0
  rw [hx, map_zero]

theorem UpperTheory.exists_principalCongruence_level_invariant :
    ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (P : CuspSub E 2) (f : Sm E 2), f ∈ P.V → ∀ h : GL (Fin 2) (A E), ∃ M : ℕ, 0 < M ∧ ∀ κ : GL (Fin 2) (A E), CongE M κ → ∀ g, f.1 (g * κ * h) = f.1 (g * h) := by
  intro E _ _ _ P f hf h
  have hopen : IsOpen {k | GlobalTheory.CuspRep.finRep E 2 k f = f} := (P.cusp f hf).1.level
  obtain ⟨l, hl⟩ : ∃ l, l = GeneralLinearGroup.map (pFin E) h := ⟨_, rfl⟩
  obtain ⟨y, hy⟩ : ∃ y, y = GeneralLinearGroup.map (pInf E) h := ⟨_, rfl⟩
  have hh : h = infGL E 2 y * finGL E 2 l := by rw [hy, hl]; exact (infGL_mul_finGL h).symm
  have hc : Continuous fun k : GL (Fin 2) (Af E) => l⁻¹ * k * l :=
    (continuous_const.mul continuous_id).mul continuous_const
  have hV : (fun k : GL (Fin 2) (Af E) => l⁻¹ * k * l) ⁻¹' {k | GlobalTheory.CuspRep.finRep E 2 k f = f} ∈ 𝓝 (1 : GL (Fin 2) (Af E)) :=
    hc.continuousAt.preimage_mem_nhds (hopen.mem_nhds (by simp))
  obtain ⟨W, hW, hWk⟩ := gl_nhds _ hV
  obtain ⟨d, hd0, hd⟩ := exists_forall_mul_mem_of_mem_nhds hW
  obtain ⟨e, he⟩ := Ideal.mem_span_singleton'.1 (Ideal.absNorm_mem (Ideal.span {d}))
  have hM : 0 < Ideal.absNorm (Ideal.span {d}) := by
    refine Nat.pos_of_ne_zero fun h0 => hd0 ?_
    rw [Ideal.absNorm_eq_zero_iff] at h0
    simpa using h0
  refine ⟨Ideal.absNorm (Ideal.span {d}), hM, fun κ hκ g => ?_⟩
  have hent : ∀ x : A E, ∀ c ∈ Oh E, x = (Ideal.absNorm (Ideal.span {d}) : A E) * c → pFin E x ∈ W := by
    rintro x c ⟨-, hc2⟩ rfl
    have hint : algebraMap E (FiniteAdeleRing (𝓞 E) E) (algebraMap (𝓞 E) E e) * c.2 ∈ integralFiniteAdeles (𝓞 E) E := by
      rw [mem_integralFiniteAdeles]
      intro v
      rw [HeightOneSpectrum.mem_adicCompletionIntegers]
      change Valued.v (algebraMap E (FiniteAdeleRing (𝓞 E) E) (algebraMap (𝓞 E) E e) v * c.2 v) ≤ 1
      rw [Valuation.map_mul]
      refine mul_le_one' ?_ (hc2 v)
      exact (HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).mp (coe_algebraMap_mem_adicCompletionIntegers v e)
    have := hd _ hint
    have e1 : pFin E ((Ideal.absNorm (Ideal.span {d}) : A E) * c) = algebraMap E (FiniteAdeleRing (𝓞 E) E) (algebraMap (𝓞 E) E d) * (algebraMap E (FiniteAdeleRing (𝓞 E) E) (algebraMap (𝓞 E) E e) * c.2) := by
      have e2 : ((Ideal.absNorm (Ideal.span {d}) : ℕ) : FiniteAdeleRing (𝓞 E) E) = algebraMap E (FiniteAdeleRing (𝓞 E) E) (algebraMap (𝓞 E) E e) * algebraMap E (FiniteAdeleRing (𝓞 E) E) (algebraMap (𝓞 E) E d) := by
        rw [← map_mul, ← map_mul, he, map_natCast, map_natCast]
      rw [map_mul, map_natCast, e2, mul_assoc, ← mul_assoc (algebraMap E _ _) (algebraMap E _ _), mul_comm (algebraMap E (FiniteAdeleRing (𝓞 E) E) (algebraMap (𝓞 E) E e)), mul_assoc]
      rfl
    rw [e1]
    exact this
  obtain ⟨k, hk⟩ : ∃ k, k = GeneralLinearGroup.map (pFin E) κ := ⟨_, rfl⟩
  have hκk : κ = finGL E 2 k := by
    have h1 : GeneralLinearGroup.map (pInf E) κ = 1 := by
      refine Units.ext (Matrix.ext fun i j => ?_)
      obtain ⟨⟨c, hc, hcx⟩, -⟩ := hκ i j
      have h0 : pInf E (κ.val i j - (1 : Matrix (Fin 2) (Fin 2) (A E)) i j) = 0 := by
        rw [hcx]
        exact pInf_zero _ (by
          change ((Ideal.absNorm (Ideal.span {d}) : A E)).1 * c.1 = 0
          rw [hc.1, mul_zero])
      rw [map_sub, sub_eq_zero] at h0
      change pInf E (κ.val i j) = (1 : Matrix (Fin 2) (Fin 2) _) i j
      rw [h0]
      by_cases hij : i = j <;> simp [Matrix.one_apply, hij]
    have := infGL_mul_finGL κ
    rw [h1, map_one, one_mul, ← hk] at this
    exact this.symm
  have hkV : l⁻¹ * k * l ∈ {k | GlobalTheory.CuspRep.finRep E 2 k f = f} := by
    refine hWk k (fun i j => ?_) (fun i j => ?_)
    · obtain ⟨⟨c, hc, hcx⟩, -⟩ := hκ i j
      have := hent _ c hc hcx
      have e : k.val i j - (1 : Matrix (Fin 2) (Fin 2) (Af E)) i j = pFin E (κ.val i j - (1 : Matrix (Fin 2) (Fin 2) (A E)) i j) := by
        rw [map_sub, hk]
        congr 1
        by_cases hij : i = j <;> simp [Matrix.one_apply, hij]
      rw [e]; exact this
    · obtain ⟨-, ⟨c, hc, hcx⟩⟩ := hκ i j
      have := hent _ c hc hcx
      have e : (k⁻¹).val i j - (1 : Matrix (Fin 2) (Fin 2) (Af E)) i j = pFin E ((κ⁻¹).val i j - (1 : Matrix (Fin 2) (Fin 2) (A E)) i j) := by
        rw [map_sub, hk, ← map_inv]
        congr 1
        by_cases hij : i = j <;> simp [Matrix.one_apply, hij]
      rw [e]; exact this
  have hfix : f.1 (g * h * finGL E 2 (l⁻¹ * k * l)) = f.1 (g * h) := congrFun (congrArg Subtype.val hkV) (g * h)
  rw [← hfix, hκk, hh]
  congr 1
  simp only [map_mul, map_inv, mul_assoc]
  rw [← mul_assoc (finGL E 2 k), ← infGL_comm]
  simp [mul_assoc]
end

-- bundled from Development.AutomorphicArithmetic.WhittakerHecke.ExistsRatIdeleEqExpUnitPrincipal
section
open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2 UpperTheory.ConvolutionTheory.RankTwoDescent
open scoped Classical ENNReal NNReal
open UpperTheory.ConvolutionTheory.R2.G (FS2 Rw nE row)

private lemma iy_fst {y : ℝ} (h : y ≠ 0) : ((iy y : (A ℚ)ˣ) : A ℚ).1 = TR.infEq ℚ fun _ => y := by
  rw [iy, dite_eq_right h]
  change (1 : InfiniteAdeleRing ℚ) - TR.infEq ℚ 1 + TR.infEq ℚ (fun _ => y) = _
  rw [map_one, sub_self, zero_add]

private lemma iy_snd {y : ℝ} (h : y ≠ 0) : ((iy y : (A ℚ)ˣ) : A ℚ).2 = 1 := by
  rw [iy, dite_eq_right h]
  change (1 : FiniteAdeleRing (𝓞 ℚ) ℚ) - 0 + 0 = 1
  rw [sub_zero, add_zero]

private lemma real_infEq (y : ℝ) : RationalIdeles.realEquiv (TR.infEq ℚ fun _ => y) = y :=
  (InfinitePlace.Completion.ringEquivRealOfIsReal (IsTotallyReal.isReal default)).apply_symm_apply y

private lemma val_eq_one {w : IdeleGroup ℚ} (hw : w ∈ IdeleGroup.standardOpenSubgroup ℚ) (v : H.P ℚ) :
    Valued.v (((w : A ℚ)).2 v) = 1 := by
  obtain ⟨h1, h2⟩ := (IdeleGroup.mem_standardOpenSubgroup ℚ).1 hw v
  have a1 := (HeightOneSpectrum.mem_adicCompletionIntegers (𝓞 ℚ) ℚ v).1 h1
  have a2 := (HeightOneSpectrum.mem_adicCompletionIntegers (𝓞 ℚ) ℚ v).1 h2
  have hm : Valued.v (((w : A ℚ)).2 v) * Valued.v ((((w⁻¹ : IdeleGroup ℚ) : A ℚ)).2 v) = 1 := by
    rw [← map_mul]
    have e : ((w : A ℚ)).2 v * (((w⁻¹ : IdeleGroup ℚ) : A ℚ)).2 v = 1 :=
      congrArg (fun z : A ℚ => z.2 v) (Units.mul_inv w)
    rw [e, map_one]
  refine le_antisymm a1 ?_
  have := mul_le_mul' (le_refl (Valued.v (((w : A ℚ)).2 v))) a2
  rwa [hm, mul_one] at this

theorem UpperTheory.exists_rat_idele_eq_exp_unit_principal :
    ∀ x : IdeleGroup ℚ, ∃ (t : ℝ) (u : IdeleGroup ℚ) (α : ℚˣ), u ∈ UU ∧ x = Un.cov t u α := by
  intro x
  have hx : x ∈ RationalIdeles.positiveSubgroup ⊔ (IdeleGroup.diagonal ℚ).range := by
    rw [RationalIdeles.positiveSubgroup_sup_diagonal_range]
    exact Subgroup.mem_top x
  obtain ⟨w, hw, _, ⟨a, rfl⟩, rfl⟩ := Subgroup.mem_sup.1 hx
  obtain ⟨hw1, hw2⟩ := RationalIdeles.mem_positiveSubgroup.1 hw
  have het : Real.exp (Real.log (RationalIdeles.realPart w : ℝ) / 2) *
      Real.exp (Real.log (RationalIdeles.realPart w : ℝ) / 2) = (RationalIdeles.realPart w : ℝ) := by
    rw [← Real.exp_add, add_halves, Real.exp_log hw2]
  obtain ⟨t, ht⟩ : ∃ t : ℝ, Real.exp t * Real.exp t = (RationalIdeles.realPart w : ℝ) := ⟨_, het⟩
  have hy : Real.exp t ≠ 0 := (Real.exp_pos t).ne'
  obtain ⟨P, hP⟩ : ∃ P : IdeleGroup ℚ, P = iy (Real.exp t) * iy (Real.exp t) := ⟨_, rfl⟩
  have hP1 : ((P : A ℚ)).1 = ((w : A ℚ)).1 := by
    apply RationalIdeles.realEquiv.injective
    have e : ((P : A ℚ)).1 = ((iy (Real.exp t) : A ℚ)).1 * ((iy (Real.exp t) : A ℚ)).1 := by
      rw [hP]
      rfl
    rw [e, iy_fst hy, map_mul, real_infEq, ht]
    exact RationalIdeles.coe_realPart w
  have hP2 : ((P : A ℚ)).2 = 1 := by
    have e : ((P : A ℚ)).2 = ((iy (Real.exp t) : A ℚ)).2 * ((iy (Real.exp t) : A ℚ)).2 := by
      rw [hP]
      rfl
    rw [e, iy_snd hy, one_mul]
  have hPi : (((P⁻¹ : IdeleGroup ℚ) : A ℚ)).2 = 1 := by
    have e : (((P⁻¹ : IdeleGroup ℚ) : A ℚ)).2 * ((P : A ℚ)).2 = 1 :=
      congrArg (fun z : A ℚ => z.2) (Units.inv_mul P)
    rwa [hP2, mul_one] at e
  refine ⟨t, P⁻¹ * w, a, ⟨?_, fun v => ?_⟩, ?_⟩
  · have e : (((P⁻¹ : IdeleGroup ℚ) : A ℚ)).1 * ((P : A ℚ)).1 = 1 :=
      congrArg (fun z : A ℚ => z.1) (Units.inv_mul P)
    rw [hP1] at e
    exact e
  · have e : H.cp v (((P⁻¹ * w : IdeleGroup ℚ) : A ℚ)) =
        (((P⁻¹ : IdeleGroup ℚ) : A ℚ)).2 v * ((w : A ℚ)).2 v := rfl
    rw [e, hPi]
    change Valued.v ((1 : v.adicCompletion ℚ) * ((w : A ℚ)).2 v) = 1
    rw [one_mul]
    exact val_eq_one hw1 v
  · rw [Un.cov, ← hP, mul_assoc, mul_inv_cancel_left, mul_comm]
end

-- bundled from Development.AutomorphicArithmetic.WhittakerHecke.ExistsSmoothLieActionMemCuspidalTranslates
section
open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2 UpperTheory.ConvolutionTheory.RankTwoDescent UpperTheory.ConvolutionTheory.RankTwoDescent.TA
open UpperTheory.ConvolutionTheory.R2.G (FS2 nE)
open scoped Classical

private theorem rt_infGL_lie {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] {a : ℕ}
    (y : GL (Fin a) (Cinf E)) (X : Matrix (Fin a) (Fin a) (Cinf E)) :
    rt E a (infGL E a y) * lie E a (toL X) =
      lie E a (toL (y.val * X * (y⁻¹).val)) * rt E a (infGL E a y) := by
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
  exact congrArg (fun Z => fderiv ℝ (chart φ.1 g) (toL y.val) (toL Z))
    (Units.inv_mul_cancel_right (y.val * X) y).symm

private theorem lie_rt_eq {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] {a : ℕ}
    (X : Matrix (Fin a) (Fin a) (Cinf E)) (h : GL (Fin a) (A E)) :
    ∃ Y : Lie E a, lie E a (toL X) * rt E a h = rt E a h * lie E a Y := by
  set y := Matrix.GeneralLinearGroup.map (pInf E) h with hy
  set κ := Matrix.GeneralLinearGroup.map (pFin E) h with hκ
  have hh : h = infGL E a y * finGL E a κ := (infGL_mul_finGL h).symm
  refine ⟨toL ((y⁻¹).val * X * y.val), ?_⟩
  have e : y.val * ((y⁻¹).val * X * y.val) * (y⁻¹).val = X := by
    simp [Matrix.mul_assoc]
  have key := rt_infGL_lie y ((y⁻¹).val * X * y.val)
  rw [e] at key
  conv_lhs => rw [hh, map_mul, ← mul_assoc, ← key, mul_assoc, lie_rt_fin, ← mul_assoc]
  rw [← map_mul, ← hh]

theorem UpperTheory.exists_smooth_lie_action_mem_cuspidal_translates :
    ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (P : CuspSub E 2) (X : Lie E 2) (φ : GL (Fin 2) (A E) → ℂ), φ ∈ Tr P → ∃ f : Sm E 2, f.1 = φ ∧ (lie E 2 X f).1 ∈ Tr P := by
  intro E _ _ _ P X φ hφ
  induction hφ using Submodule.span_induction with
  | mem φ hφ =>
    obtain ⟨f, hf, h, rfl⟩ := hφ
    obtain ⟨Y, hY⟩ := lie_rt_eq (a := 2) (E := E) X h
    refine ⟨rt E 2 h ⟨f.1, f.2⟩, rfl, ?_⟩
    have e : lie E 2 X (rt E 2 h f) = rt E 2 h (lie E 2 Y f) := LinearMap.congr_fun hY f
    have hm : lie E 2 Y f ∈ P.V := P.stable (.lie Y) f hf
    refine Submodule.subset_span ⟨_, hm, h, ?_⟩
    rw [show (⟨f.1, f.2⟩ : Sm E 2) = f from rfl, e]
    rfl
  | zero => exact ⟨0, rfl, by simp⟩
  | add a b _ _ ha hb =>
    obtain ⟨fa, rfl, ha⟩ := ha
    obtain ⟨fb, rfl, hb⟩ := hb
    refine ⟨fa + fb, rfl, ?_⟩
    rw [map_add (f := _)]
    exact (Tr P).add_mem ha hb
  | smul c a _ ha =>
    obtain ⟨fa, rfl, ha⟩ := ha
    refine ⟨c • fa, rfl, ?_⟩
    rw [map_smul]
    exact (Tr P).smul_mem c ha
end

-- bundled from Development.AutomorphicArithmetic.WhittakerHecke.ExistsWhittakerCoeffNeZeroOfAdmissible
section
open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2 UpperTheory.ConvolutionTheory.RankTwoDescent UpperTheory.ConvolutionTheory.RankTwoDescent.Xg
open scoped Classical
open UpperTheory.ConvolutionTheory.R2.G (FS2 Rw nE row)
open UpperTheory.V.Af.Smo (EigAt)
open scoped ComplexOrder


open GroundTheory.Automorphic.FourierWhittaker in
private noncomputable def latQ {E : Type} [Field E] [NumberField E] (D : Dat ℚ E) :
    vecLattice ℚ (Fin 2) ≃ AdeleRing.principalSubgroup (𝓞 E) E where
  toFun g := ⟨D.coE.symm g.1, by
    obtain ⟨_, ξ, rfl⟩ := g
    refine ⟨algebraMap ℚ E (ξ 0) + algebraMap ℚ E (ξ 1) * D.θ, ?_⟩
    exact (D.mkE_rt (ξ 0) (ξ 1)).symm⟩
  invFun y := ⟨D.coE y.1, by
    obtain ⟨_, z, rfl⟩ := y
    exact mem_vecLattice.2 ⟨fun i => D.b.repr z i, funext fun i => (D.co_rt z i).symm⟩⟩
  left_inv g := Subtype.ext (D.coE.apply_symm_apply g.1)
  right_inv y := Subtype.ext (D.coE.symm_apply_apply y.1)


open GroundTheory.Automorphic.FourierWhittaker in
private theorem int_zero {E : Type} [Field E] [NumberField E] (D : Dat ℚ E) (H : A E → ℂ)
    (hper : ∀ (k : E) x, H (rt k + x) = H x)
    (h0 : ∫ u in FS2 ℚ, H (D.mkE (u 0) (u 1)) ∂(adeleMeasurePi ℚ) = 0) :
    ∫ x in fundamentalSet E, H x ∂(adeleMeasure E) = 0 := by
  let β : (Fin 2 → A ℚ) ≃ₜ+ A E := D.coE.symm
  let m := β.toHomeomorph.toMeasurableEquiv
  haveI : (adeleMeasurePi ℚ (ι := Fin 2)).IsAddHaarMeasure :=
    inferInstanceAs (Measure.pi fun _ : Fin 2 => adeleMeasure ℚ).IsAddHaarMeasure
  haveI : ((adeleMeasurePi ℚ (ι := Fin 2)).map m).IsAddHaarMeasure := β.isAddHaarMeasure_map (adeleMeasurePi ℚ)
  have hF : IsAddFundamentalDomain (AdeleRing.principalSubgroup (𝓞 E) E) (m '' FS2 ℚ)
      ((adeleMeasurePi ℚ (ι := Fin 2)).map m) :=
    (isAddFundamentalDomain_vecDomain (K := ℚ) (ι := Fin 2)).image_of_equiv m.toEquiv
      (MeasurePreserving.symm m ⟨m.measurable, rfl⟩).quasiMeasurePreserving (latQ D).symm
      fun y x => by
        change β (D.coE y.1 + x) = y.1 + β x
        rw [map_add (f := _)]
        congr 1
        exact D.coE.symm_apply_apply y.1
  have hF' : IsAddFundamentalDomain (AdeleRing.principalSubgroup (𝓞 E) E) (m '' FS2 ℚ) (adeleMeasure E) :=
    hF.mono (Measure.absolutelyContinuous_isAddHaarMeasure _ _)
  have hp : ∀ (g : AdeleRing.principalSubgroup (𝓞 E) E) (x : A E), H (g +ᵥ x) = H x := by
    rintro ⟨_, k, rfl⟩ x
    exact hper k x
  haveI : Countable (AdeleRing.principalSubgroup (𝓞 E) E) := (latQ D).symm.injective.countable
  have h1 := (isAddFundamentalDomain_fundamentalSet E).setIntegral_eq hF' (f := H) hp
  rw [h1, Measure.isAddLeftInvariant_eq_smul (adeleMeasure E) ((adeleMeasurePi ℚ (ι := Fin 2)).map m), Measure.restrict_smul,
    integral_smul_nnreal_measure, m.measurableEmbedding.setIntegral_map, m.injective.preimage_image]
  have h3 : ∫ u in FS2 ℚ, H (m u) ∂(adeleMeasurePi ℚ) = 0 := h0
  rw [h3, smul_zero]

private theorem exists_mul {E : Type} [Field E] [NumberField E] (D : Dat ℚ E) :
    ∃ ξ : Eˣ, ∀ z : A E, ψ (rt (ξ : E) * z) = ψ (D.co z 1) := by
  let χ : AddChar (A E) Circle :=
    { toFun := fun z => adelicChar ℚ (D.co z 1)
      map_zero_eq_one' := by rw [← D.mkE_zero, D.co_mkE]; simp
      map_add_eq_mul' := fun a b => by rw [D.co_add, Pi.add_apply, AddChar.map_add_eq_mul] }
  have h1 : Continuous fun z : A E => D.co z 1 := (continuous_apply 1).comp D.continuous_co
  have h2 : Continuous fun z : A E => adelicChar ℚ (D.co z 1) := (continuous_adelicChar (K := ℚ)).comp h1
  have hχ : Continuous χ := h2
  obtain ⟨ξ, hξ, -⟩ := existsUnique_eq_adelicChar_mul (K := E) χ hχ fun k => by
    change adelicChar ℚ (D.co (rt k) 1) = 1
    rw [D.co_rt]
    exact adelicChar_algebraMap _
  have h0 : ξ ≠ 0 := by
    rintro rfl
    apply adelicChar_ne_one (K := ℚ)
    refine DFunLike.ext _ _ fun t => ?_
    have := hξ (D.mkE 0 t)
    change adelicChar ℚ (D.co (D.mkE 0 t) 1) = _ at this
    rw [D.co_mkE] at this
    simpa using this
  refine ⟨Units.mk0 ξ h0, fun z => ?_⟩
  have := hξ z
  change adelicChar ℚ (D.co z 1) = _ at this
  simp only [ψ, Units.val_mk0]
  rw [this]

theorem UpperTheory.exists_whittakerCoeff_ne_zero_of_admissible :
    ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (D : Dat ℚ E) (P : CuspSub E 2) (ω : HChar ℚ), (∀ φ ∈ Tr P, admitted D ω φ) → ∃ f ∈ P.V, ∃ h, Wo D f.1 h ≠ 0 := by
  intro E _ _ _ D P ω hA
  obtain ⟨f, hf, h0⟩ := (Submodule.ne_bot_iff _).1 P.ne_bot
  refine ⟨f, hf, ?_⟩
  by_contra hn
  push Not at hn
  have hT : f.1 ∈ Tr P := Submodule.subset_span ⟨f, hf, 1, by simp⟩
  have hL : Pp.Lf f.1 := ⟨(hA _ hT).cont, (hA _ hT).left⟩
  obtain ⟨ξ, hξ⟩ := exists_mul D
  have hW : ∀ g, Wf f.1 g = 0 := fun g => by
    have e := Pp.wfT E f.1 hL ξ ((aE (IdeleGroup.diagonal E ξ))⁻¹ * g)
    rw [mul_inv_cancel_left] at e
    rw [← e]
    refine int_zero D _ (fun k x => ?_) ?_
    · rw [hL.per, mul_add, ← map_mul, Pp.ψ_add, Pp.ψ_rt, one_mul]
    · rw [← hn ((aE (IdeleGroup.diagonal E ξ))⁻¹ * g)]
      refine integral_congr_ae (Eventually.of_forall fun u => ?_)
      simp only
      rw [hξ, D.co_mkE]
      rfl
  obtain ⟨φ, rfl⟩ := Cm.mem_range_ofCusp.2 (P.cusp f hf)
  exact h0 (Subtype.ext (Pp.eq_zero_of_Wf φ.2 hL hW))
end

-- bundled from Development.AutomorphicArithmetic.WhittakerHecke.FixedAndHeckeEigenOfFinsetLinearCombination
section
open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2 UpperTheory.ConvolutionTheory.RankTwoDescent UpperTheory.ConvolutionTheory.RankTwoDescent.Xg
open scoped Classical
open UpperTheory.ConvolutionTheory.R2.G (FS2 Rw nE row)
open UpperTheory.V.Af.Smo (EigAt)
open scoped ComplexOrder

private theorem finsum_Tj_eq {E : Type} [Field E] [NumberField E] {w : H.P E} {ϖ : w.adicCompletion E}
    (hϖ : Formalism.UG.IsUnifV E w ϖ) (j : ℕ) :
    ∃ t : Finset (GL (Fin 2) (w.adicCompletion E) ⧸ GlobalTheory.LFun.KGL w (n := 2)),
      ∀ F : GL (Fin 2) (w.adicCompletion E) ⧸ GlobalTheory.LFun.KGL w (n := 2) → ℂ,
        ∑ᶠ x, Formalism.UG.Tj ℂ 2 (Formalism.UG.Ov E w) ϖ j x.out * F x =
          ∑ x ∈ t, Formalism.UG.Tj ℂ 2 (Formalism.UG.Ov E w) ϖ j x.out * F x := by
  have hf := Formalism.UG.P.finite_support_cosets (Formalism.UG.Final.GLintComm E w 2)
    (GlobalTheory.LFun.Tj_mem_hecke (n := 2) hϖ j).2
  refine ⟨hf.toFinset, fun F => finsum_eq_sum_of_support_subset _ fun x hx => ?_⟩
  rw [Set.Finite.coe_toFinset]
  exact left_ne_zero_of_mul hx

theorem UpperTheory.fixed_and_heckeEigen_of_finset_linearCombination :
    ∀ (E : Type) [Field E] [NumberField E] (w : H.P E) (ι : Type) (s : Finset ι) (c : ι → ℂ) (φ : ι → GL (Fin 2) (A E) → ℂ) (B : Multiset ℂˣ), s.Nonempty → (∀ i, H.Fix w (φ i)) → (∀ i, EigAt w B (φ i)) → H.Fix w (fun g => ∑ i ∈ s, c i * φ i g) ∧ EigAt w B (fun g => ∑ i ∈ s, c i * φ i g) := by
  intro E _ _ w ι s c φ B hs hF hE
  obtain ⟨i₀, -⟩ := hs
  refine ⟨fun g k hk => ?_, fun g => ⟨(hE i₀ g).card, fun y k hk => ?_, fun ϖ hϖ j hj y => ?_⟩⟩
  · simp only [fun i => hF i g k hk]
  · simp only [fun i => (hE i g).inv y k hk]
  · obtain ⟨t, ht⟩ := finsum_Tj_eq (w := w) hϖ j
    rw [ht]
    simp only [Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ => ?_
    have e := (hE i g).eig ϖ hϖ j hj y
    rw [ht] at e
    rw [mul_left_comm, ← e, Finset.mul_sum]
    exact Finset.sum_congr rfl fun x _ => mul_left_comm _ _ _
end

