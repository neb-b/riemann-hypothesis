module

public import Development.AutomorphicArithmetic.Foundations.Convolution.SplitEigenfunctions.CharacterNorms.Bundle0001
public import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.UnramifiedSplitting.Bundle0001
public import GroundTheory.GlobalFields.SemilocalAlgebras.LocalDegree

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.WhittakerHecke.ExistsGoodCharacterOfInertCMDatum
section
open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2 UpperTheory.ConvolutionTheory.RankTwoDescent
open scoped Classical
open UpperTheory.ConvolutionTheory.R2.G (FS2 Rw nE row)
open UpperTheory.V.Af.Smo (EigAt)
open scoped ComplexOrder

theorem UpperTheory.exists_good_character_of_inert_CMDatum :
    ∀ (E : Type) [Field E] [NumberField E] (D : Dat ℚ E) (v : H.P ℚ) (w : H.P E), H.Gd D.δ v → H.Inert D v w →
          ∃ χ : H.Kv w → ℂ, H.Good χ ∧ ∀ x, ∃ u t, H.sg w x = D.mkE u t ∧ ψ (-t) = χ x := by
  intro E _ _ D v w hG hI
  obtain ⟨e, h1, h2, h3, -⟩ := hI.coord
  obtain ⟨sa, sm, sc, -⟩ := H.sgLaws ℚ v
  obtain ⟨-, tm, tc, -⟩ := H.sgLaws E w
  obtain ⟨ga, gi, gm⟩ := hG.psi
  have hs : ∀ u, -(H.sg v u) = H.sg v (-u) := fun u => by
    rw [← neg_one_mul, sm, map_neg, map_one, neg_one_mul]
  have s0 : H.sg v (0 : H.Kv v) = 0 := by simpa using (sm 0 0).symm
  have h4 : ∀ c u t, e (0, c) * e (u, t) = e (H.cp v (rt D.δ) * (c * t), c * u) := fun c u t => by
    have a1 : ∀ x y, H.sg v (x * y) = H.sg v x * H.sg v y := fun x y => by rw [sm, sc]
    have a2 : ∀ x, H.sg v (H.cp v (rt D.δ) * x) = rt D.δ * H.sg v x := fun x => (sm (rt D.δ) x).symm
    have a3 : (rt D.θ : A E) ^ 2 = AdeleBaseChange.adeleMap ℚ E (rt D.δ) := by
      rw [← map_pow, D.sq]
      exact (AdeleBaseChange.adeleMap_algebraMap _).symm
    have : H.sg w (e (0, c) * e (u, t)) = H.sg w (e (H.cp v (rt D.δ) * (c * t), c * u)) := by
      rw [← tc (e (0, c)), ← tm, h1, h1, h1, s0, a2, a1, a1]
      simp only [Dat.mkE, map_mul, map_zero, ← a3]
      ring
    simpa only [tc] using congrArg (H.cp w) this
  have key : ∀ y : H.Kv v, (∀ c, H.IsInt c → ψ (H.sg v (-(c * y))) = 1) → H.IsInt y := fun y hy => by
    have : Valued.v (-y) ≤ 1 := gm _ fun c hc => by
      have := hy c hc
      rwa [show -(c * y) = c * -y by ring] at this
    rwa [Valuation.map_neg] at this
  refine ⟨fun x => ψ (H.sg v (-(e.symm x).2)), ⟨fun x y => ?_, fun x hx => ?_, fun x hx => ?_⟩, fun x => ?_⟩
  · beta_reduce
    rw [map_add (f := _), Prod.snd_add, neg_add]
    exact ga _ _
  · obtain ⟨⟨u, t⟩, rfl⟩ := e.surjective x
    have ht : Valued.v t ≤ 1 := (le_max_right _ _).trans ((h2 u t).symm.le.trans hx)
    beta_reduce
    rw [e.symm_apply_apply]
    refine gi _ ?_
    show Valued.v _ ≤ 1
    rwa [Valuation.map_neg]
  · obtain ⟨⟨u, t⟩, rfl⟩ := e.surjective x
    have ht : H.IsInt t := key t fun c hc => by
      have := hx (e (c, 0)) ((h2 c 0).le.trans (max_le hc (by simp)))
      beta_reduce at this
      rwa [h3, e.symm_apply_apply] at this
    have hu : H.IsInt u := key u fun c hc => by
      have := hx (e (0, c)) ((h2 0 c).le.trans (max_le (by simp) hc))
      beta_reduce at this
      rwa [h4, e.symm_apply_apply] at this
    exact (h2 u t).le.trans (max_le hu ht)
  · obtain ⟨⟨u, t⟩, rfl⟩ := e.surjective x
    exact ⟨_, _, h1 u t, by beta_reduce; rw [hs, e.symm_apply_apply]⟩
end

-- bundled from Development.AutomorphicArithmetic.WhittakerHecke.ExistsIdeleCorrectingLowerRightEntry
section
open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2 UpperTheory.ConvolutionTheory.RankTwoDescent
open scoped Classical
open UpperTheory.ConvolutionTheory.R2.G (FS2 Rw nE row)
open UpperTheory.V.Af.Smo (EigAt)
open scoped ComplexOrder

private theorem ex_idele (u : ∀ v : H.P ℚ, (H.Kv v)ˣ) (S : Finset (H.P ℚ)) :
    ∃ ζ : (A ℚ)ˣ, (ζ : A ℚ).1 = 1 ∧ ∀ v, H.cp v (ζ : A ℚ) = if v ∈ S then (u v : H.Kv v) else 1 := by
  induction S using Finset.induction_on with
  | empty => exact ⟨1, rfl, fun v => by simp⟩
  | insert w S hw ih =>
    obtain ⟨ζ, h1, h2⟩ := ih
    obtain ⟨g1, g2⟩ := localIdele_isSupportedAt ℚ w (u w)
    refine ⟨H.idl w (u w) * ζ, ?_, fun v => ?_⟩
    · show ((localIdele ℚ w (u w) : (A ℚ)ˣ) : A ℚ).1 * (ζ : A ℚ).1 = 1
      rw [h1, mul_one]
      funext x
      exact g1 x
    · rw [Units.val_mul, map_mul, h2 v]
      by_cases hv : v = w
      · subst hv
        have e : H.cp v ((H.idl v (u v) : (A ℚ)ˣ) : A ℚ) = u v := localIdele_snd_self ℚ v (u v)
        rw [e, if_neg hw, if_pos (Finset.mem_insert_self _ _), mul_one]
      · have e : H.cp v ((H.idl w (u w) : (A ℚ)ˣ) : A ℚ) = 1 := g2 v hv
        rw [e, one_mul]
        simp [hv]

private theorem val_bad {N : ℕ} {v : H.P ℚ} (h : Bad N v) : Valued.v (N : H.Kv v) < 1 := by
  have e : (N : H.Kv v) = FinitePlace.embedding v (algebraMap (𝓞 ℚ) ℚ (N : 𝓞 ℚ)) := by simp
  rw [e]
  have := HeightOneSpectrum.valuedAdicCompletion_eq_valuation' v (algebraMap (𝓞 ℚ) ℚ (N : 𝓞 ℚ))
  refine lt_of_eq_of_lt this ?_
  exact (HeightOneSpectrum.valuation_lt_one_iff_mem v _).2 h

private theorem val_unit {N : ℕ} {k : G1 ℚ} (hk : k ∈ KK ℚ) (hs : k ∈ SS N) {v : H.P ℚ} (h : Bad N v) :
    Valued.v (H.cp v (k 1 1)) = 1 := by
  have hi : ∀ i j, Valued.v (H.cp v (k i j)) ≤ 1 := fun i j => hk.2 v i j
  have hd := k.det_coe
  rw [Matrix.det_fin_two] at hd
  have h1 : H.cp v (k 0 0) * H.cp v (k 1 1) = 1 + H.cp v (k 0 1) * H.cp v (k 1 0) := by
    have := congrArg (H.cp v) hd
    rw [map_sub, map_mul, map_mul, map_one] at this
    exact (sub_eq_iff_eq_add.1 this)
  have h2 : Valued.v (H.cp v (k 0 1) * H.cp v (k 1 0)) < 1 := by
    rw [map_mul]
    calc _ ≤ 1 * Valued.v (H.cp v (k 1 0)) := mul_le_mul_left (hi 0 1) _
      _ < 1 := by rw [one_mul]; exact lt_of_le_of_lt (hs v) (val_bad h)
  have h3 : Valued.v (H.cp v (k 0 0)) * Valued.v (H.cp v (k 1 1)) = 1 := by
    rw [← map_mul, h1]
    exact Valuation.map_one_add_of_lt _ h2
  refine le_antisymm (hi 1 1) ?_
  calc 1 = _ := h3.symm
    _ ≤ 1 * Valued.v (H.cp v (k 1 1)) := mul_le_mul_left (hi 0 0) _
    _ = _ := one_mul _

theorem UpperTheory.exists_idele_correcting_lowerRight_entry :
    ∀ N : ℕ, 0 < N → ∀ k ∈ KK ℚ, k ∈ SS N → ∃ ζ : (A ℚ)ˣ, ζ ∈ UU ∧ ∀ v : H.P ℚ, (Bad N v → Dv N v ((ζ : A ℚ) * k 1 1 - 1)) ∧ (¬ Bad N v → H.cp v (ζ : A ℚ) = 1) := by
  intro N hN k hk hs
  have hfin : {v : H.P ℚ | Bad N v}.Finite := by
    have h0 : Ideal.span {(N : 𝓞 ℚ)} ≠ ⊥ := by
      rw [Ne, Ideal.span_singleton_eq_bot]
      exact_mod_cast hN.ne'
    refine (Ideal.finite_factors h0).subset fun v hv => ?_
    exact Ideal.dvd_span_singleton.2 hv
  have hne : ∀ v, Bad N v → H.cp v (k 1 1) ≠ 0 := fun v hv h0 => by
    have := val_unit hk hs hv
    rw [h0, map_zero] at this
    exact zero_ne_one this
  obtain ⟨ζ, h1, h2⟩ := ex_idele (fun v => if h : Bad N v then (Units.mk0 _ (hne v h))⁻¹ else 1) hfin.toFinset
  have hb : ∀ v, Bad N v → H.cp v (ζ : A ℚ) = (H.cp v (k 1 1))⁻¹ := fun v hv => by
    rw [h2 v, if_pos (hfin.mem_toFinset.2 hv), dite_eq_left hv]
    simp
  have hg : ∀ v, ¬ Bad N v → H.cp v (ζ : A ℚ) = 1 := fun v hv => by
    rw [h2 v, if_neg (fun h => hv (hfin.mem_toFinset.1 h))]
  refine ⟨ζ, ⟨h1, fun v => ?_⟩, fun v => ⟨fun hv => ?_, hg v⟩⟩
  · by_cases hv : Bad N v
    · rw [hb v hv, map_inv₀, val_unit hk hs hv, inv_one]
    · rw [hg v hv, map_one]
  · unfold Dv
    rw [map_sub, map_mul, map_one, hb v hv, inv_mul_cancel₀ (hne v hv), sub_self, map_zero]
    exact zero_le
end

-- bundled from Development.AutomorphicArithmetic.WhittakerHecke.ExistsIsCompactAnnihilatorScaledIntegralAdeles
section
open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2 UpperTheory.ConvolutionTheory.RankTwoDescent UpperTheory.ConvolutionTheory.RankTwoDescent.TA
open UpperTheory.ConvolutionTheory.R2.G (FS2 nE)
open scoped Classical

private theorem diff_top : differentIdeal ℤ (𝓞 ℚ) = ⊤ := by
  rw [← Ideal.absNorm_eq_one_iff, absNorm_differentIdeal ℚ (𝓞 ℚ), Rat.numberField_discr]
  rfl

private theorem int_of_inv (v : HeightOneSpectrum (𝓞 ℚ)) {z : v.adicCompletion ℚ}
    (hz : z ∈ GroundTheory.Global.localInvDifferent v) : z ∈ v.adicCompletionIntegers ℚ := by
  rw [GroundTheory.Global.mem_localInvDifferent_iff_valued, diff_top, FractionalIdeal.coeIdeal_top,
    FractionalIdeal.count_one, WithZero.exp_zero] at hz
  exact hz

theorem UpperTheory.exists_isCompact_annihilator_scaled_integralAdeles :
    ∀ N : ℕ, 0 < N → ∃ K : Set (FiniteAdeleRing (𝓞 ℚ) ℚ), IsCompact K ∧ ∀ x : FiniteAdeleRing (𝓞 ℚ) ℚ,
        (∀ b : FiniteAdeleRing (𝓞 ℚ) ℚ, (∀ v, b v ∈ v.adicCompletionIntegers ℚ) → ψ (((0, x * ((N : FiniteAdeleRing (𝓞 ℚ) ℚ) * b)) : A ℚ)) = 1) → x ∈ K := by
  intro N hN
  have hNq : (N : ℚ) ≠ 0 := by exact_mod_cast hN.ne'
  set c : FiniteAdeleRing (𝓞 ℚ) ℚ := algebraMap ℚ (FiniteAdeleRing (𝓞 ℚ) ℚ) (N : ℚ)⁻¹ with hc
  have hcN : c * (N : FiniteAdeleRing (𝓞 ℚ) ℚ) = 1 := by
    have : (N : FiniteAdeleRing (𝓞 ℚ) ℚ) = algebraMap ℚ (FiniteAdeleRing (𝓞 ℚ) ℚ) (N : ℚ) := by
      simp
    rw [this, hc, ← map_mul, inv_mul_cancel₀ hNq, map_one]
  refine ⟨(fun z => c * z) '' (integralFiniteAdeles (𝓞 ℚ) ℚ : Set (FiniteAdeleRing (𝓞 ℚ) ℚ)),
    (GroundTheory.Global.isCompact_integralFiniteAdeles ℚ).image (continuous_const.mul continuous_id),
    fun x hx => ?_⟩
  refine ⟨x * (N : FiniteAdeleRing (𝓞 ℚ) ℚ), ?_, ?_⟩
  · intro v
    refine int_of_inv v ((GroundTheory.Global.forall_localAdelicChar_mul_eq_one_iff v _).mp fun a ha => ?_)
    have hb : ∀ u, GroundTheory.Global.finiteAdeleSingleAdd v a u ∈ u.adicCompletionIntegers ℚ := by
      intro u
      rcases eq_or_ne u v with rfl | hu
      · rwa [GroundTheory.Global.finiteAdeleSingleAdd_apply_self]
      · rw [GroundTheory.Global.finiteAdeleSingleAdd_apply_of_ne hu]
        exact zero_mem _
    have h := hx _ hb
    have e : x * ((N : FiniteAdeleRing (𝓞 ℚ) ℚ) * GroundTheory.Global.finiteAdeleSingleAdd v a) =
        GroundTheory.Global.finiteAdeleSingleAdd v (a * (x * (N : FiniteAdeleRing (𝓞 ℚ) ℚ)) v) := by
      rw [← GroundTheory.Global.finiteAdeleSingleAdd_mul]
      ring
    rw [e] at h
    have h' : ((GroundTheory.Global.localAdelicChar ℚ v (a * (x * (N : FiniteAdeleRing (𝓞 ℚ) ℚ)) v) : Circle) : ℂ) = 1 := h
    exact Circle.ext (by simpa using h')
  · show c * (x * (N : FiniteAdeleRing (𝓞 ℚ) ℚ)) = x
    rw [mul_comm x, ← mul_assoc, hcN, one_mul]
end

-- bundled from Development.AutomorphicArithmetic.WhittakerHecke.ExistsLevelUnipotentInvarianceAutomorphicForm
section
open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2 UpperTheory.ConvolutionTheory.RankTwoDescent UpperTheory.ConvolutionTheory.RankTwoDescent.TA
open UpperTheory.ConvolutionTheory.R2.G (FS2 nE)
open scoped Classical

private theorem gln_val {E : Type} [Field E] [NumberField E] (b : A E) :
    (gl (nU b) : GL (Fin 2) (A E)).val = !![1, b; 0, 1] := rfl

private theorem nU_inv {E : Type} [Field E] [NumberField E] (b : A E) :
    (gl (nU b) : GL (Fin 2) (A E))⁻¹ = gl (nU (-b)) := by
  rw [inv_eq_iff_mul_eq_one]
  refine Units.ext ?_
  rw [Units.val_mul, gln_val, gln_val]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]

private theorem cont_n {E : Type} [Field E] [NumberField E] :
    Continuous fun b : A E => (gl (nU b) : GL (Fin 2) (A E)) := by
  have hv : ∀ g : A E → A E, Continuous g →
      Continuous fun b : A E => ((gl (nU (g b)) : GL (Fin 2) (A E)) : Matrix (Fin 2) (Fin 2) (A E)) := by
    intro g hg
    refine continuous_matrix fun i j => ?_
    fin_cases i <;> fin_cases j <;> simp [nU] <;> first | exact hg | exact continuous_const
  refine Units.continuous_iff.2 ⟨hv id continuous_id, ?_⟩
  simp only [nU_inv]
  exact hv _ continuous_neg

private theorem map_unipotent_eq_one {E S : Type} [Field E] [NumberField E] [CommRing S] (p : A E →+* S) (z : A E) (hz : p z = 0) :
    Matrix.GeneralLinearGroup.map p (gl (nU z)) = 1 := by
  refine Units.ext ?_
  ext i j
  change p ((gl (nU z) : GL (Fin 2) (A E)).val i j) = (1 : Matrix (Fin 2) (Fin 2) S) i j
  rw [gln_val]
  fin_cases i <;> fin_cases j <;> simp [hz]

private theorem pInf_mk {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (D : Dat ℚ E) (x : FiniteAdeleRing (𝓞 ℚ) ℚ) :
    pInf E (D.mkE 0 ((0, x) : A ℚ)) = 0 := by
  have h : pInf E (AdeleBaseChange.adeleMap ℚ E ((0, x) : A ℚ)) = 0 := by
    change (infEq E).symm (GroundTheory.Global.InfinitePlace.infiniteAdeleRingMap (0 : InfiniteAdeleRing ℚ)) = 0
    rw [map_zero, map_zero]
  simp [Dat.mkE, h]

private theorem cont_mk {E : Type} [Field E] [NumberField E] (D : Dat ℚ E) :
    Continuous fun x : FiniteAdeleRing (𝓞 ℚ) ℚ => D.mkE 0 ((0, x) : A ℚ) := by
  have h : Continuous fun x : FiniteAdeleRing (𝓞 ℚ) ℚ => ((0, x) : A ℚ) :=
    continuous_const.prodMk continuous_id
  unfold Dat.mkE
  exact continuous_const.add ((AdeleBaseChange.continuous_adeleMap.comp h).mul continuous_const)

theorem UpperTheory.exists_level_unipotent_invariance_automorphicForm :
    ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (D : Dat ℚ E) (f : Sm E 2), IsAutForm f →
        ∀ C : Set (GL (Fin 2) (A E)), IsCompact C → ∃ N : ℕ, 0 < N ∧ ∀ k ∈ C, ∀ b : FiniteAdeleRing (𝓞 ℚ) ℚ,
          (∀ v, b v ∈ v.adicCompletionIntegers ℚ) → ∀ G, f.1 (G * (gl (nU (D.mkE 0 ((0, (N : FiniteAdeleRing (𝓞 ℚ) ℚ) * b) : A ℚ))) * k)) = f.1 (G * k) := by
  intro E _ _ _ D f hf C hC
  let m : FiniteAdeleRing (𝓞 ℚ) ℚ → GL (Fin 2) (A E) := fun x => gl (nU (D.mkE 0 ((0, x) : A ℚ)))
  have hm : Continuous m := cont_n.comp (cont_mk D)
  have hm0 : m 0 = 1 := by
    have h0 : D.mkE 0 ((0, 0) : A ℚ) = 0 := by
      have h : D.mkE 0 ((0, 0) : A ℚ) = D.mkE 0 (0 : A ℚ) := rfl
      rw [h]
      unfold Dat.mkE
      rw [map_zero, zero_mul, add_zero]
    change gl (nU (D.mkE 0 ((0, 0) : A ℚ))) = 1
    rw [h0]
    refine Units.ext ?_
    rw [gln_val]
    ext i j
    fin_cases i <;> fin_cases j <;> simp
  let Φ : FiniteAdeleRing (𝓞 ℚ) ℚ × GL (Fin 2) (A E) → GL (Fin 2) (Af E) :=
    fun p => Matrix.GeneralLinearGroup.map (pFin E) (p.2⁻¹ * m p.1 * p.2)
  have hΦ : Continuous Φ :=
    (Continuous.units_map _ (continuous_id.matrix_map continuous_snd)).comp ((continuous_snd.inv.mul (hm.comp continuous_fst)).mul continuous_snd)
  have hO : IsOpen (Φ ⁻¹' {k | finRep E 2 k f = f}) := hf.level.preimage hΦ
  have hsub : ({0} : Set (FiniteAdeleRing (𝓞 ℚ) ℚ)) ×ˢ C ⊆ Φ ⁻¹' {k | finRep E 2 k f = f} := by
    rintro ⟨x, k⟩ ⟨hx, -⟩
    have hx0 : x = 0 := hx
    subst hx0
    have e : Φ (0, k) = 1 := by
      change Matrix.GeneralLinearGroup.map (pFin E) (k⁻¹ * m 0 * k) = 1
      rw [hm0, mul_one, inv_mul_cancel, map_one]
    change finRep E 2 (Φ (0, k)) f = f
    rw [e, map_one]
    rfl
  obtain ⟨U, V, hU, hV, h0U, hCV, hUV⟩ := generalized_tube_lemma isCompact_singleton hC hO hsub
  have h0 : (0 : FiniteAdeleRing (𝓞 ℚ) ℚ) ∈ U := h0U rfl
  have key : ∀ᶠ d in 𝓝 (0 : FiniteAdeleRing (𝓞 ℚ) ℚ),
      ∀ z ∈ (integralFiniteAdeles (𝓞 ℚ) ℚ : Set (FiniteAdeleRing (𝓞 ℚ) ℚ)), d * z ∈ U :=
    (isCompact_integralFiniteAdeles ℚ).eventually_forall_of_forall_eventually fun z _ =>
      (hU.preimage (continuous_fst.mul continuous_snd)).mem_nhds (by simpa using h0)
  obtain ⟨n, hn⟩ := ((GlobalTheory.AdelicFactorial.tendsto_factorial_finiteAdele ℚ).eventually key).exists
  refine ⟨n.factorial, n.factorial_pos, fun k hk b hb G => ?_⟩
  have hx := hn b hb
  have hS : finRep E 2 (Φ (_, k)) f = f := hUV (Set.mk_mem_prod hx (hCV hk))
  have hy : finGL E 2 (Φ ((n.factorial : FiniteAdeleRing (𝓞 ℚ) ℚ) * b, k)) =
      k⁻¹ * m ((n.factorial : FiniteAdeleRing (𝓞 ℚ) ℚ) * b) * k := by
    refine ga_ext ?_ ?_
    · rw [pInf_finGL, map_mul, map_mul, map_unipotent_eq_one _ _ (pInf_mk D _), mul_one, ← map_mul, inv_mul_cancel, map_one]
    · rw [pFin_finGL]
  have e := congrArg (fun ψ : Sm E 2 => ψ.1 (G * k)) hS
  change f.1 (G * k * finGL E 2 _) = f.1 (G * k) at e
  rw [hy] at e
  rw [← e]
  change f.1 (G * (m _ * k)) = _
  congr 1
  group
end

-- bundled from Development.AutomorphicArithmetic.WhittakerHecke.ExistsLocalCharacterOfSplitPairRat
section
open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2 UpperTheory.ConvolutionTheory.RankTwoDescent
open scoped Classical
open UpperTheory.ConvolutionTheory.R2.G (FS2 Rw nE row)
open UpperTheory.V.Af.Smo (EigAt)
open scoped ComplexOrder

namespace UpperTheory.AdeleBaseChangeSplitting
open UpperTheory.ConvolutionTheory.R2.H GroundTheory.Global.SemiLocal GroundTheory.Global.AdeleBaseChange

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

private theorem split_iota (v : P F) (w : P E) [hl : w.asIdeal.LiesOver v.asIdeal] (h : SplitAt v w) :
    ∃ i : Kv v ≃+* Kv w, (∀ x, completionMap v w x = i x) ∧
      (∀ x : F, i (algebraMap F _ x) = algebraMap E _ (algebraMap F E x)) ∧
      ∀ x, Valued.v (i x) = Valued.v x := by
  obtain ⟨-, i, hc, ha, hv⟩ := h
  refine ⟨i, ?_, ha, hv⟩
  have := (HeightOneSpectrum.denseRange_algebraMap (K := F) v).equalizer
    (continuous_completionMap v w) hc (by
      funext x
      change completionMap v w (algebraMap F (Kv v) x) = i (algebraMap F (Kv v) x)
      rw [ha, completionMap_algebraMap, IsScalarTower.algebraMap_apply F E (Kv w)])
  exact fun x => congrFun this x

private theorem adeleMap_split_two_places (v : P F) (w w' : P E) [hl : w.asIdeal.LiesOver v.asIdeal]
    [hl' : w'.asIdeal.LiesOver v.asIdeal] (hne : w ≠ w')
    (hu : ∀ u : P E, u.asIdeal.LiesOver v.asIdeal → u = w ∨ u = w') (x : Kv v) :
    adeleMap F E (sg v x) = sg w (completionMap v w x) + sg w' (completionMap v w' x) := by
  obtain ⟨-, -, hc, -, -, -, -, hs, -, -⟩ := sgLaws F v
  obtain ⟨-, -, hc', -, -, -, -, hs', -, -⟩ := sgLaws E w
  obtain ⟨-, -, hc'', -, -, -, -, hs'', -, -⟩ := sgLaws E w'
  refine Prod.ext ?_ (FiniteAdeleRing.ext E fun u => ?_)
  · change InfinitePlace.infiniteAdeleRingMap (sg v x).1 = (sg w _).1 + (sg w' _).1
    rw [(hs x).1, (hs' _).1, (hs'' _).1, map_zero, add_zero]
  · change completionMap (below F u) u ((sg v x).2 (below F u)) = (sg w _).2 u + (sg w' _).2 u
    by_cases h : u = w
    · subst h
      have hb : below F u = v := (below_eq_iff _ _).2 hl
      subst hb
      rw [(hs'' _).2 _ hne, add_zero]
      exact (congrArg _ (hc x)).trans (hc' _).symm
    · by_cases h' : u = w'
      · subst h'
        have hb : below F u = v := (below_eq_iff _ _).2 hl'
        subst hb
        rw [(hs' _).2 _ h, zero_add]
        exact (congrArg _ (hc x)).trans (hc'' _).symm
      · have hb : below F u ≠ v := fun hb => (hu u ((below_eq_iff _ _).1 hb)).elim h h'
        rw [(hs x).2 _ hb, map_zero, (hs' _).2 _ h, (hs'' _).2 _ h', add_zero]

private theorem main (D : Dat F E) (v : P F) (w w' : P E) [hl : w.asIdeal.LiesOver v.asIdeal]
    [hl' : w'.asIdeal.LiesOver v.asIdeal] (hne : w ≠ w') (h1 : SplitAt v w) (h2 : SplitAt v w')
    (hu : ∀ u : P E, u.asIdeal.LiesOver v.asIdeal → u = w ∨ u = w') (hG : Gd D.δ v) :
    ∃ χ : Kv w → ℂ, Good χ ∧ ∀ x, ∃ u t, sg w x = D.mkE u t ∧ ψ (-t) = χ x := by
  obtain ⟨i, hi, hia, hiv⟩ := split_iota v w h1
  obtain ⟨j, hj, hja, hjv⟩ := split_iota v w' h2
  obtain ⟨τ, hτ⟩ := i.surjective (algebraMap E (Kv w) D.θ)
  have hτ2 : τ ^ 2 = algebraMap F (Kv v) D.δ := by
    apply i.injective
    rw [map_pow, hτ, hia, ← map_pow, D.sq]
  have hτv : Valued.v τ = 1 := by
    have h := hG.del
    rw [← hτ2, map_pow] at h
    exact (pow_eq_one_iff_of_nonneg zero_le' two_ne_zero).1 h
  have hτ0 : τ ≠ 0 := fun h => by simp [h] at hτv
  have h20 : (2 : Kv v) ≠ 0 := fun h => by simpa [h] using hG.two
  have hτ' : j τ = -algebraMap E (Kv w') D.θ := by
    have hsq : (j τ) ^ 2 = (algebraMap E (Kv w') D.θ) ^ 2 := by
      rw [← map_pow, hτ2, hja, ← map_pow, D.sq]
    refine (sq_eq_sq_iff_eq_or_eq_neg.1 hsq).resolve_left fun he => hne ?_
    have hval : ∀ y : E, w.valuation E y = w'.valuation E y := by
      intro y
      have hy : y = algebraMap F E (D.b.repr y 0) + algebraMap F E (D.b.repr y 1) * D.θ := by
        conv_lhs => rw [← D.b.sum_repr y]
        simp [Fin.sum_univ_two, D.b0, D.b1, Algebra.smul_def]
      set a := algebraMap F (Kv v) (D.b.repr y 0)
      set b := algebraMap F (Kv v) (D.b.repr y 1)
      have e1 : algebraMap E (Kv w) y = i (a + b * τ) := by
        rw [map_add (f := _), map_mul, hτ, hia, hia, ← map_mul, ← map_add (f := _), ← hy]
      have e2 : algebraMap E (Kv w') y = j (a + b * τ) := by
        rw [map_add (f := _), map_mul, he, hja, hja, ← map_mul, ← map_add (f := _), ← hy]
      rw [← valued_algebraMap_field, ← valued_algebraMap_field, e1, e2, hiv, hjv]
    refine HeightOneSpectrum.ext (Ideal.ext fun a => ?_)
    rw [← HeightOneSpectrum.valuation_lt_one_iff_mem (K := E), ← HeightOneSpectrum.valuation_lt_one_iff_mem (K := E), hval]
  have hcv : Valued.v (2 * τ) = 1 := by rw [map_mul, hG.two, hτv, mul_one]
  obtain ⟨g1, g2, g3⟩ := hG.psi
  obtain ⟨hadd, hmul, -⟩ := sgLaws F v
  obtain ⟨hadd1, hmul1, -⟩ := sgLaws E w
  obtain ⟨hadd2, hmul2, -⟩ := sgLaws E w'
  have hsv : ∀ x : Kv w, Valued.v (-(i.symm x / (2 * τ))) = Valued.v x := by
    intro x
    rw [Valuation.map_neg, map_div₀, hcv, div_one, ← hiv, RingEquiv.apply_symm_apply]
  refine ⟨fun x => ψ (sg v (-(i.symm x / (2 * τ)))), ⟨fun x y => ?_, fun x hx => ?_, fun x hx => ?_⟩,
    fun x => ⟨sg v (i.symm x / 2), sg v (i.symm x / (2 * τ)), ?_, ?_⟩⟩
  · have e : -(i.symm (x + y) / (2 * τ)) = -(i.symm x / (2 * τ)) + -(i.symm y / (2 * τ)) := by
      rw [map_add (f := _)]; ring
    show ψ (sg v (-(i.symm (x + y) / (2 * τ)))) = _
    rw [e]
    exact g1 _ _
  · exact g2 _ (by unfold IsInt at *; rw [hsv]; exact hx)
  · have := g3 (-(i.symm x / (2 * τ))) fun c hc => by
      have h := hx (i c) (by unfold IsInt at *; rw [hiv]; exact hc)
      have e : -(i.symm (i c * x) / (2 * τ)) = c * -(i.symm x / (2 * τ)) := by
        rw [map_mul, RingEquiv.symm_apply_apply]; ring
      change ψ (sg v (-(i.symm (i c * x) / (2 * τ)))) = 1 at h
      rw [e] at h
      exact h
    unfold IsInt at *
    rwa [hsv] at this
  · have hmk : ∀ u t : A F, D.mkE u t = adeleMap F E u + adeleMap F E t * rt D.θ := fun _ _ => rfl
    obtain ⟨y, rfl⟩ := i.surjective x
    have z2 : sg w' 0 = 0 := by
      have := hmul2 0 0
      simpa using this.symm
    have c1 : cp w (rt D.θ) = i τ := hτ.symm
    have c2 : cp w' (rt D.θ) = - j τ := by rw [hτ', neg_neg]; rfl
    rw [RingEquiv.symm_apply_apply, hmk, adeleMap_split_two_places v w w' hne hu, adeleMap_split_two_places v w w' hne hu,
      add_mul, mul_comm (sg w _), mul_comm (sg w' _), hmul1, hmul2, add_add_add_comm, ← hadd1, ← hadd2,
      c1, c2, hi, hi, hj, hj, ← map_neg, ← map_mul, ← map_mul, ← map_add, ← map_add,
      show y / 2 + τ * (y / (2 * τ)) = y by field_simp; ring,
      show y / 2 + -τ * (y / (2 * τ)) = 0 by field_simp; ring, map_zero, z2, add_zero]
  · have := hmul (-1) (i.symm x / (2 * τ))
    rw [map_neg, map_one, neg_one_mul, neg_one_mul] at this
    rw [this]

end UpperTheory.AdeleBaseChangeSplitting

theorem UpperTheory.exists_localCharacter_of_split_pair_rat :
    ∀ (E : Type) [Field E] [NumberField E] (D : Dat ℚ E) (v : H.P ℚ) (w w' : H.P E), w ≠ w' → w.under (𝓞 ℚ) = v → w'.under (𝓞 ℚ) = v → H.SplitAt v w → H.SplitAt v w' →
          (∀ w'' : H.P E, w''.under (𝓞 ℚ) = v → w'' = w ∨ w'' = w') → H.Gd D.δ v →
          ∃ χ : H.Kv w → ℂ, H.Good χ ∧ ∀ x, ∃ u t, H.sg w x = D.mkE u t ∧ ψ (-t) = χ x := by
  intro E _ _ D v w w' hne hw hw' h1 h2 hu hG
  haveI hl : w.asIdeal.LiesOver v.asIdeal := ⟨by rw [← hw]; rfl⟩
  haveI hl' : w'.asIdeal.LiesOver v.asIdeal := ⟨by rw [← hw']; rfl⟩
  exact UpperTheory.AdeleBaseChangeSplitting.main D v w w' hne h1 h2
    (fun u h => hu u (HeightOneSpectrum.ext h.1.symm)) hG
end

-- bundled from Development.AutomorphicArithmetic.WhittakerHecke.LseriesSummableSqCoeffOfFourLtRe
section
open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2 UpperTheory.ConvolutionTheory.RankTwoDescent
open scoped Classical
open UpperTheory.ConvolutionTheory.R2.G (FS2 Rw nE row)
open UpperTheory.V.Af.Smo (EigAt)
open scoped ComplexOrder

theorem UpperTheory.lseries_summable_sq_coeff_of_four_lt_re :
    ∀ (N : ℕ) (s : ℂ), 4 < s.re → LSeriesSummable (sqN N) s := by
  intro N s hs
  refine LSeriesSummable_of_bounded_of_one_lt_re (m := 1) (fun n _ => ?_) (by linarith)
  unfold sqN
  split_ifs <;> simp
end

