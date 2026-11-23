module

public import Development.AutomorphicArithmetic.Foundations.Convolution.SplitEigenfunctions.CharacterNorms.Bundle0001
public import GroundTheory.IdeleRoots.TorusPowers.HeckeIdem
public import GroundTheory.AutomorphicForms.GLnLocal
public import Development.WeilBound.CoreStatements.PublishedTheorems.JacquetShalikaBound.SatakeEigenvalues
public import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.ReductionDomains.Bundle0003
public import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.UnramifiedSplitting.Bundle0004

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.WhittakerHecke.ArchimedeanConjugateCurveOneParameterSubgroup
section
open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2 UpperTheory.ConvolutionTheory.RankTwoDescent UpperTheory.ConvolutionTheory.RankTwoDescent.TA
open UpperTheory.ConvolutionTheory.R2.G (FS2 nE)
open scoped Classical

private theorem nC_zero' {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] : nC (0 : Cinf E) = 1 := by
  apply Units.ext
  ext i j
  fin_cases i <;> fin_cases j <;> simp [nC]

private theorem nC_add' {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a b : Cinf E) :
    nC (a + b) = nC a * nC b := by
  apply Units.ext
  ext i j : 2
  fin_cases i <;> fin_cases j <;> simp [nC, Matrix.mul_apply, Fin.sum_univ_two, add_comm]

private theorem nC_val' {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (t : ℝ) (z : Cinf E) :
    (nC (t • z)).val = 1 + t • (!![0, z; 0, 0] : Matrix (Fin 2) (Fin 2) (Cinf E)) := by
  ext i j : 2
  fin_cases i <;> fin_cases j <;> simp [nC]

private theorem cv_val' {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (D : Dat ℚ E)
    (k : GL (Fin 2) (A E)) (t : ℝ) : (cv D k t).val = 1 + t • XB D k := by
  have h : ((kInf k)⁻¹).val * (kInf k).val = 1 := by
    rw [← Units.val_mul, inv_mul_cancel, Units.val_one]
  simp only [cv, XB, Units.val_mul, nC_val', mul_add, add_mul, mul_one, h, Matrix.mul_smul, Matrix.smul_mul]

theorem UpperTheory.archimedeanConjugateCurve_oneParameterSubgroup :
    ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (D : Dat ℚ E) (k : GL (Fin 2) (A E)),
        cv D k 0 = 1 ∧ (∀ s t, cv D k (s + t) = cv D k s * cv D k t) ∧ HasDerivAt (fun t => toL (cv D k t).val) (toL (XB D k)) 0 ∧
        Continuous fun k : GL (Fin 2) (A E) => toL (XB D k) := by
  intro E _ _ _ D k
  refine ⟨?_, ?_, ?_, ?_⟩
  · simp [cv, nC_zero']
  · intro s t
    simp only [cv, add_smul, nC_add']
    group
  · have h : (fun t : ℝ => toL (cv D k t).val) =
        fun t : ℝ => toL (1 : Matrix (Fin 2) (Fin 2) (Cinf E)) + t • toL (XB D k) := by
      funext t
      rw [cv_val']
      rfl
    rw [h]
    simpa using ((hasDerivAt_id (0 : ℝ)).smul_const (toL (XB D k))).const_add
      (toL (1 : Matrix (Fin 2) (Fin 2) (Cinf E)))
  · have hK : Continuous fun k : GL (Fin 2) (A E) => kInf k := ContAut.continuous_map_pInf E 2
    have h1 : Continuous fun k : GL (Fin 2) (A E) => (kInf k).val := Units.continuous_val.comp hK
    have h2 : Continuous fun k : GL (Fin 2) (A E) => ((kInf k)⁻¹).val :=
      Units.continuous_val.comp hK.inv
    exact (h2.matrix_mul continuous_const).matrix_mul h1
end

-- bundled from Development.AutomorphicArithmetic.WhittakerHecke.BaseChangeGL2CongruenceOfLevel
section
open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2 UpperTheory.ConvolutionTheory.RankTwoDescent UpperTheory.ConvolutionTheory.RankTwoDescent.Xg
open scoped Classical
open UpperTheory.ConvolutionTheory.R2.G (FS2 Rw nE row)
open UpperTheory.V.Af.Smo (EigAt)
open scoped ComplexOrder
open scoped ValuativeRel

private theorem mem_int_iff {K : Type} [Field K] [NumberField K] (v : HeightOneSpectrum (𝓞 K))
    (x : v.adicCompletion K) : x ∈ 𝒪[v.adicCompletion K] ↔ Valued.v x ≤ 1 := by
  rw [Valuation.mem_integer_iff]
  exact (ValuativeRel.isEquiv (ValuativeRel.valuation (v.adicCompletion K)) Valued.v).le_one_iff_le_one

private theorem inv_entry_int (v : H.P ℚ) (g : GL (Fin 2) (A ℚ)) (h : H.KAt v g) (i j : Fin 2) :
    Valued.v (((g⁻¹).val i j).2 v) ≤ 1 := by
  have h1 : Matrix.GeneralLinearGroup.map (H.cp v) g ∈ GroundTheory.Automorphic.GLnLocal.integralGL (v.adicCompletion ℚ) 2 := by
    rw [← PositivityTheory.JacquetShalikaLocal.SatakeEigenvalues.KGL_eq]
    exact h
  have h2 := ((GroundTheory.Automorphic.GLnLocal.mem_integralGL_iff _ _).1 h1).2 i j
  rw [← map_inv] at h2
  exact (mem_int_iff v _).1 h2

private theorem div_of_dv (N : ℕ) (hN : 0 < N) (x : A ℚ) (h1 : x.1 = 0) (h2 : ∀ v, Dv N v x) :
    ∃ c ∈ Oh ℚ, x = (N : A ℚ) * c := by
  have hcp : ∀ v : H.P ℚ, ((N : A ℚ)).2 v = (N : H.Kv v) := fun v => map_natCast (H.cp v) N
  have hio : ∀ v : H.P ℚ, (iota N).2 v = (N : H.Kv v)⁻¹ := by
    intro v
    have hN' : (N : ℚ) ≠ 0 := Nat.cast_ne_zero.2 hN.ne'
    have h0 : (iota N).2 * (N : FiniteAdeleRing (𝓞 ℚ) ℚ) = 1 := by
      change algebraMap ℚ (FiniteAdeleRing (𝓞 ℚ) ℚ) (N : ℚ)⁻¹ * (N : FiniteAdeleRing (𝓞 ℚ) ℚ) = 1
      rw [← map_natCast (algebraMap ℚ (FiniteAdeleRing (𝓞 ℚ) ℚ)), ← map_mul, inv_mul_cancel₀ hN', map_one]
    have h3 := congrArg (pLoc ℚ v) h0
    rw [map_mul, map_natCast, map_one] at h3
    exact eq_inv_of_mul_eq_one_left h3
  have hne : ∀ v : H.P ℚ, (N : H.Kv v) ≠ 0 := by
    intro v
    have : CharZero (H.Kv v) := algebraRat.charZero _
    exact Nat.cast_ne_zero.2 hN.ne'
  refine ⟨x * iota N, ⟨?_, fun v => ?_⟩, ?_⟩
  · change x.1 * (iota N).1 = 0
    rw [h1, zero_mul]
  · change Valued.v (x.2 v * (iota N).2 v) ≤ 1
    rw [hio, map_mul, map_inv₀]
    have hv : Valued.v (N : H.Kv v) ≠ 0 := (Valuation.ne_zero_iff _).2 (hne v)
    exact mul_inv_le_one_of_le₀ (h2 v) zero_le'
  · refine Prod.ext ?_ (FiniteAdeleRing.ext (K := ℚ) fun v => ?_)
    · change x.1 = (N : A ℚ).1 * (x.1 * (iota N).1)
      rw [h1, zero_mul, mul_zero]
    · change x.2 v = (N : A ℚ).2 v * (x.2 v * (iota N).2 v)
      rw [hcp, hio]
      field_simp [hne v]

private theorem oh_add {K : Type} [Field K] [NumberField K] {a b : A K} (ha : a ∈ Oh K) (hb : b ∈ Oh K) :
    a + b ∈ Oh K := by
  refine ⟨?_, fun v => ?_⟩
  · change a.1 + b.1 = 0
    rw [ha.1, hb.1, add_zero]
  · change Valued.v (a.2 v + b.2 v) ≤ 1
    exact (Valuation.map_add _ _ _).trans (max_le (ha.2 v) (hb.2 v))

private theorem oh_neg {K : Type} [Field K] [NumberField K] {a : A K} (ha : a ∈ Oh K) : -a ∈ Oh K := by
  refine ⟨?_, fun v => ?_⟩
  · change -a.1 = 0
    rw [ha.1, neg_zero]
  · change Valued.v (-(a.2 v)) ≤ 1
    rw [Valuation.map_neg]
    exact ha.2 v

private theorem oh_mul (a c : A ℚ) (ha : ∀ v : H.P ℚ, Valued.v (a.2 v) ≤ 1) (hc : c ∈ Oh ℚ) : a * c ∈ Oh ℚ := by
  refine ⟨?_, fun v => ?_⟩
  · change a.1 * c.1 = 0
    rw [hc.1, mul_zero]
  · change Valued.v (a.2 v * c.2 v) ≤ 1
    rw [map_mul]
    exact mul_le_one' (ha v) (hc.2 v)

private theorem oh_map (E : Type) [Field E] [NumberField E] {c : A ℚ} (hc : c ∈ Oh ℚ) :
    AdeleBaseChange.adeleMap ℚ E c ∈ Oh E := by
  refine ⟨?_, fun w => ?_⟩
  · have : (AdeleBaseChange.adeleMap ℚ E c).1 =
        GroundTheory.Global.InfinitePlace.infiniteAdeleRingMap (K := ℚ) (L := E) c.1 := rfl
    rw [this, hc.1]
    exact map_zero _
  · rw [GroundTheory.BlockD.ThmBHecke.adeleMap_snd_apply, GroundTheory.Global.SemiLocal.valued_completionMap]
    exact pow_le_one' (hc.2 _) _

private theorem entry_map (E : Type) [Field E] [NumberField E] (N : ℕ) (g : GL (Fin 2) (A ℚ)) (i j : Fin 2)
    (h : ∃ c ∈ Oh ℚ, g.val i j - (1 : Matrix (Fin 2) (Fin 2) (A ℚ)) i j = (N : A ℚ) * c) :
    ∃ c ∈ Oh E, (em E g).val i j - (1 : Matrix (Fin 2) (Fin 2) (A E)) i j = (N : A E) * c := by
  obtain ⟨c, hc, h⟩ := h
  refine ⟨AdeleBaseChange.adeleMap ℚ E c, oh_map E hc, ?_⟩
  have h1 : (em E g).val i j = AdeleBaseChange.adeleMap ℚ E (g.val i j) := rfl
  have h2 : (1 : Matrix (Fin 2) (Fin 2) (A E)) i j =
      AdeleBaseChange.adeleMap ℚ E ((1 : Matrix (Fin 2) (Fin 2) (A ℚ)) i j) := by
    by_cases hij : i = j
    · subst hij
      simp only [Matrix.one_apply_eq, map_one]
    · simp only [Matrix.one_apply_ne hij, map_zero]
  rw [h1, h2, ← map_sub, h, map_mul, map_natCast]

theorem UpperTheory.baseChangeGL2_congruence_of_level :
    ∀ (E : Type) [Field E] [NumberField E] (N : ℕ), 0 < N → ∀ k : GL (Fin 2) (A ℚ), Lev N k → CongE N (em E k) := by
  intro E _ _ N hN k hk
  have hk1 : ∀ i j, ∃ c ∈ Oh ℚ, k.val i j - (1 : Matrix (Fin 2) (Fin 2) (A ℚ)) i j = (N : A ℚ) * c := by
    intro i j
    refine div_of_dv N hN _ ?_ fun v => (hk.2 v).2 i j
    change (k.val i j).1 - ((1 : Matrix (Fin 2) (Fin 2) (A ℚ)) i j).1 = 0
    rw [hk.1 i j, sub_self]
  choose c hc hkc using hk1
  have hk2 : ∀ i j, ∃ d ∈ Oh ℚ, (k⁻¹).val i j - (1 : Matrix (Fin 2) (Fin 2) (A ℚ)) i j = (N : A ℚ) * d := by
    intro i j
    have hint : ∀ l, (k⁻¹).val i l * c l j ∈ Oh ℚ := fun l =>
      oh_mul _ _ (fun v => inv_entry_int v k (hk.2 v).1 i l) (hc l j)
    refine ⟨-((k⁻¹).val i 0 * c 0 j + (k⁻¹).val i 1 * c 1 j), oh_neg (oh_add (hint 0) (hint 1)), ?_⟩
    have hm : (k⁻¹).val * k.val = 1 := by
      have := congrArg Units.val (inv_mul_cancel k)
      simpa using this
    have hs : ((k⁻¹).val * (k.val - 1)) i j = (1 - (k⁻¹).val) i j := by
      rw [Matrix.mul_sub, hm, Matrix.mul_one]
    rw [Matrix.mul_apply, Fin.sum_univ_two, Matrix.sub_apply, Matrix.sub_apply, Matrix.sub_apply,
      hkc 0 j, hkc 1 j] at hs
    linear_combination hs
  intro i j
  refine ⟨entry_map E N k i j ⟨c i j, hc i j, hkc i j⟩, ?_⟩
  rw [← map_inv]
  exact entry_map E N k⁻¹ i j (hk2 i j)
end

-- bundled from Development.AutomorphicArithmetic.WhittakerHecke.BottomRowCongruenceIffIdeleCongruence
section
open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2 UpperTheory.ConvolutionTheory.RankTwoDescent
open scoped Classical
open UpperTheory.ConvolutionTheory.R2.G (FS2 Rw nE row)
open UpperTheory.V.Af.Smo (EigAt)
open scoped ComplexOrder

theorem UpperTheory.bottomRow_congruence_iff_idele_congruence :
    ∀ N : ℕ, 0 < N → ∀ k ∈ KK ℚ, k ∈ SS N → ∀ ζ : (A ℚ)ˣ, ζ ∈ UU → (∀ v : H.P ℚ, (Bad N v → Dv N v ((ζ : A ℚ) * k 1 1 - 1)) ∧ (¬ Bad N v → H.cp v (ζ : A ℚ) = 1)) → ∀ y : (A ℚ)ˣ, (∀ v, Dv N v ((y : A ℚ) * (ζ : A ℚ) * k 1 0) ∧ Dv N v ((y : A ℚ) * (ζ : A ℚ) * k 1 1 - 1)) ↔ ((∀ v, Bad N v → Dv N v (((y : (A ℚ)ˣ) : A ℚ) - 1)) ∧ ∀ v : H.P ℚ, Valued.v (H.cp v ((y : (A ℚ)ˣ) : A ℚ)) ≤ 1) := by
  intro N hN k hk hS ζ hζ hz y
  have hi : ∀ v i j, Valued.v (H.cp v (k i j)) ≤ 1 := fun v i j => hk.2 v i j
  have hN1 : ∀ v : H.P ℚ, Valued.v (N : H.Kv v) ≤ 1 := fun v =>
    show (N : H.Kv v) ∈ v.adicCompletionIntegers ℚ from natCast_mem _ N
  have hv : ∀ v : H.P ℚ, (Bad N v → Valued.v (N : H.Kv v) < 1) ∧ (¬ Bad N v → Valued.v (N : H.Kv v) = 1) := fun v => by
    have h1 := HeightOneSpectrum.valuedAdicCompletion_eq_valuation (K := ℚ) v (N : 𝓞 ℚ)
    rw [HeightOneSpectrum.valuation_of_algebraMap] at h1
    have h2 : Valued.v (N : H.Kv v) = v.intValuation (N : 𝓞 ℚ) := by simpa using h1
    rw [h2]
    exact ⟨fun h => (v.intValuation_lt_one_iff_mem _).2 h, fun h => HeightOneSpectrum.intValuation_eq_one_iff.2 h⟩
  have key : ∀ v : H.P ℚ, (Dv N v ((y : A ℚ) * (ζ : A ℚ) * k 1 0) ∧ Dv N v ((y : A ℚ) * (ζ : A ℚ) * k 1 1 - 1)) ↔
      ((Bad N v → Dv N v ((y : A ℚ) - 1)) ∧ Valued.v (H.cp v (y : A ℚ)) ≤ 1) := fun v => by
    have hd : H.cp v (k 0 0) * H.cp v (k 1 1) - H.cp v (k 0 1) * H.cp v (k 1 0) = 1 := by
      have := congrArg (H.cp v) ((Matrix.det_fin_two k.1).symm.trans k.2)
      simpa using this
    have hs := hS v
    have hz' := hz v
    have hu := hζ.2 v
    have i00 := hi v 0 0
    have i01 := hi v 0 1
    have i10 := hi v 1 0
    have i11 := hi v 1 1
    simp only [Dv, map_mul, map_sub, map_one] at hs hz' ⊢
    generalize H.cp v (k 0 0) = a at *
    generalize H.cp v (k 0 1) = b at *
    generalize H.cp v (k 1 0) = c at *
    generalize H.cp v (k 1 1) = d at *
    generalize H.cp v (y : A ℚ) = x at *
    generalize H.cp v (ζ : A ℚ) = z at *
    by_cases hb : Bad N v
    · have h1 := hz'.1 hb
      have hlt := (hv v).1 hb
      have h2 : Valued.v (z * d) = 1 := by
        have := Valuation.map_one_add_of_lt Valued.v (h1.trans_lt hlt)
        rwa [add_sub_cancel] at this
      constructor
      · rintro ⟨-, h3⟩
        have h4 : Valued.v x ≤ 1 := by
          have := Valuation.map_one_add_of_lt Valued.v (h3.trans_lt hlt)
          rw [add_sub_cancel, mul_assoc, map_mul, h2, mul_one] at this
          exact this.le
        refine ⟨fun _ => ?_, h4⟩
        rw [show x - 1 = (x * z * d - 1) - x * (z * d - 1) by ring]
        exact Valuation.map_sub_le _ h3 (by rw [map_mul]; exact (mul_le_mul' h4 h1).trans_eq (one_mul _))
      · rintro ⟨h3, h4⟩
        refine ⟨by rw [hu, mul_one]; exact (mul_le_mul' h4 hs).trans_eq (one_mul _), ?_⟩
        rw [show x * z * d - 1 = (x - 1) * (z * d) + (z * d - 1) by ring]
        exact Valuation.map_add_le _ (by rw [map_mul, h2, mul_one]; exact h3 hb) h1
    · obtain rfl := hz'.2 hb
      rw [(hv v).2 hb]
      simp only [map_one, mul_one]
      constructor
      · rintro ⟨h3, h4⟩
        refine ⟨fun h => absurd h hb, ?_⟩
        rw [show x = a * ((x * d - 1) + 1) - b * (x * c) by linear_combination (-x) * hd]
        refine Valuation.map_sub_le _ ?_ ?_
        · rw [map_mul]
          exact mul_le_one' i00 (Valuation.map_add_le _ h4 (map_one _).le)
        · rw [map_mul, map_mul]
          exact mul_le_one' i01 h3
      · rintro ⟨-, h4⟩
        exact ⟨mul_le_one' h4 i10, Valuation.map_sub_le _ (by rw [map_mul]; exact mul_le_one' h4 i11) (map_one _).le⟩
  simp only [key, forall_and]
end

-- bundled from Development.AutomorphicArithmetic.WhittakerHecke.CongruenceElementCommuteInfEmbedding
section
open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2 UpperTheory.ConvolutionTheory.RankTwoDescent UpperTheory.ConvolutionTheory.RankTwoDescent.Xg
open scoped Classical
open UpperTheory.ConvolutionTheory.R2.G (FS2 Rw nE row)
open UpperTheory.V.Af.Smo (EigAt)
open scoped ComplexOrder

theorem UpperTheory.congruence_element_commute_inf_embedding :
    ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (M : ℕ) (κ : GL (Fin 2) (A E)), CongE M κ → ∀ X : GL (Fin 2) (Cinf E), κ * infGL E 2 X = infGL E 2 X * κ := by
  intro E _ _ _ M κ h X
  have h0 : ∀ c : A E, c.1 = 0 → pInf E c = 0 := fun c hc => by
    change (infEq E).symm c.1 = 0
    rw [hc]
    exact map_zero _
  have hk : GeneralLinearGroup.map (pInf E) κ = 1 := by
    refine Units.ext (Matrix.ext fun i j => ?_)
    obtain ⟨⟨c, hc, e⟩, _⟩ := h i j
    have h1 := congrArg (pInf E) e
    rw [map_sub, map_mul, h0 c hc.1, mul_zero] at h1
    have h2 : pInf E (κ.val i j) = pInf E ((1 : Matrix (Fin 2) (Fin 2) (A E)) i j) := sub_eq_zero.1 h1
    change pInf E (κ.val i j) = (1 : Matrix (Fin 2) (Fin 2) (Cinf E)) i j
    rw [h2]
    by_cases hij : i = j
    · subst hij
      simp
    · simp [Matrix.one_apply_ne hij]
  have e := infGL_mul_finGL κ
  rw [hk, map_one, one_mul] at e
  rw [← e]
  exact (infGL_comm X _).symm
end

-- bundled from Development.AutomorphicArithmetic.WhittakerHecke.CongruenceSubgroupVolumePos
section
open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2 UpperTheory.ConvolutionTheory.RankTwoDescent
open scoped Classical
open UpperTheory.ConvolutionTheory.R2.G (FS2 Rw nE row)
open UpperTheory.V.Af.Smo (EigAt)
open scoped ComplexOrder

private theorem kappa_ne_zero (M : Meas ℚ)
    {U : Set (G1 ℚ)} (hU : IsOpen U) {k : G1 ℚ} (hk : k ∈ KK ℚ) (hkU : k ∈ U) : M.κ U ≠ 0 := by
  intro h0
  obtain ⟨hKs, hC⟩ := UpperTheory.ConvolutionTheory.R2.M.kkCpt ℚ
  have hmem : ∀ x ∈ KK ℚ, ∀ y ∈ KK ℚ, x * y⁻¹ ∈ KK ℚ := by
    intro x hx y hy
    rw [hKs] at hx hy ⊢
    exact (UpperTheory.ConvolutionTheory.R2.M.Ks ℚ).mul_mem hx ((UpperTheory.ConvolutionTheory.R2.M.Ks ℚ).inv_mem hy)
  have hnull : ∀ c ∈ KK ℚ, M.κ ((fun x => c * x) ⁻¹' U) = 0 := by
    intro c hc
    have hm : Measurable (fun x : G1 ℚ => c * x) := (continuous_const.mul continuous_id).measurable
    rw [← Measure.map_apply hm hU.measurableSet, M.κ_left c hc]
    exact h0
  obtain ⟨t, ht, hcov⟩ := hC.elim_nhds_subcover (fun x => (fun y => (k * x⁻¹) * y) ⁻¹' U) (by
    intro x hx
    refine ((continuous_const.mul continuous_id).isOpen_preimage _ hU).mem_nhds ?_
    simpa using hkU)
  have hK0 : M.κ (KK ℚ) = 0 := by
    refine measure_mono_null hcov ?_
    exact (measure_biUnion_null_iff t.countable_toSet).2 fun x hx => hnull _ (hmem k hk x (ht x hx))
  haveI := M.prob
  have hle : M.κ Set.univ ≤ M.κ (KK ℚ) + M.κ (KK ℚ)ᶜ := by
    rw [← Set.union_compl_self (KK ℚ)]
    exact measure_union_le _ _
  rw [hK0, M.supp, measure_univ] at hle
  simp at hle

private theorem cp_cont (v : H.P ℚ) : Continuous (H.cp v) := by
  have h1 : Continuous (pLoc ℚ v) :=
    RestrictedProduct.continuous_eval (R := fun v : H.P ℚ => v.adicCompletion ℚ) v
  have h2 : Continuous (pFin ℚ) := continuous_snd
  exact h1.comp h2

private theorem isOpen_dv {N : ℕ} (hN : 0 < N) (v : H.P ℚ) :
    IsOpen {k : G1 ℚ | Dv N v (k 1 0)} := by
  have hN0 : (N : H.Kv v) ≠ 0 := Nat.cast_ne_zero.2 hN.ne'
  have hv0 : Valued.v (N : H.Kv v) ≠ 0 := (Valuation.ne_zero_iff _).2 hN0
  have hO : IsOpen ((v.adicCompletionIntegers ℚ : ValuationSubring (H.Kv v)) : Set (H.Kv v)) :=
    Valued.isOpen_valuationSubring _
  have hc : Continuous fun k : G1 ℚ => H.cp v (k 1 0) * (N : H.Kv v)⁻¹ := by
    have hk : Continuous fun k : G1 ℚ => (k.1 : Matrix (Fin 2) (Fin 2) (A ℚ)) 1 0 :=
      (Matrix.SpecialLinearGroup.isClosedEmbedding_val.continuous).matrix_elem 1 0
    exact ((cp_cont v).comp hk).mul continuous_const
  have : {k : G1 ℚ | Dv N v (k 1 0)} =
      (fun k : G1 ℚ => H.cp v (k 1 0) * (N : H.Kv v)⁻¹) ⁻¹' ((v.adicCompletionIntegers ℚ : ValuationSubring (H.Kv v)) : Set (H.Kv v)) := by
    ext k
    simp only [Set.mem_setOf_eq, Set.mem_preimage, SetLike.mem_coe, Dv]
    rw [HeightOneSpectrum.mem_adicCompletionIntegers, map_mul, map_inv₀]
    rw [← div_eq_mul_inv]
    exact (div_le_one₀ (zero_lt_iff.2 hv0)).symm
  rw [this]
  exact hO.preimage hc

private theorem val_nat {K : Type} [Field K] [NumberField K] (v : H.P K) (n : ℕ) :
    Valued.v (n : H.Kv v) = v.valuation K (n : K) := by
  rw [← HeightOneSpectrum.valuedAdicCompletion_eq_valuation' v (n : K)]
  congr 1
  exact (map_natCast (algebraMap K (H.Kv v)) n).symm

private theorem dv_of_int {N : ℕ} (hN : 0 < N) (v : H.P ℚ)
    (hv : v ∉ HeightOneSpectrum.Support (𝓞 ℚ) ((N : ℚ)⁻¹)) {x : A ℚ}
    (hx : Valued.v (H.cp v x) ≤ 1) : Dv N v x := by
  have h1 : ¬ 1 < v.valuation ℚ ((N : ℚ)⁻¹) := hv
  have hN0 : (N : ℚ) ≠ 0 := Nat.cast_ne_zero.2 hN.ne'
  have h2 : (1 : _) ≤ v.valuation ℚ (N : ℚ) := by
    rw [map_inv₀] at h1
    have h3 := not_lt.1 h1
    have hp : 0 < v.valuation ℚ (N : ℚ) := zero_lt_iff.2 ((Valuation.ne_zero_iff _).2 hN0)
    exact (inv_le_one₀ hp).1 h3
  have h4 : Valued.v (N : H.Kv v) = v.valuation ℚ (N : ℚ) := val_nat v N
  refine hx.trans ?_
  rw [h4]
  exact h2

theorem UpperTheory.congruenceSubgroup_volume_pos :
    ∀ (M : Meas ℚ) (N : ℕ), 0 < N → 0 < cK M N := by
  intro M N hN
  haveI := M.prob
  have hfin := HeightOneSpectrum.Support.finite (𝓞 ℚ) ((N : ℚ)⁻¹)
  set T := HeightOneSpectrum.Support (𝓞 ℚ) ((N : ℚ)⁻¹) with hT
  set U : Set (G1 ℚ) := ⋂ v ∈ T, {k : G1 ℚ | Dv N v (k 1 0)} with hU
  have hUo : IsOpen U := hfin.isOpen_biInter fun v _ => isOpen_dv hN v
  have h1K : (1 : G1 ℚ) ∈ KK ℚ := by
    rw [(UpperTheory.ConvolutionTheory.R2.M.kkCpt ℚ).1]
    exact (UpperTheory.ConvolutionTheory.R2.M.Ks ℚ).one_mem
  have h1U : (1 : G1 ℚ) ∈ U := by
    refine Set.mem_iInter₂.2 fun v _ => ?_
    simp [Dv]
  have hne := kappa_ne_zero M hUo h1K h1U
  refine ENNReal.toReal_pos (fun h0 => hne ?_) (measure_ne_top _ _)
  refine measure_mono_null (t := (SS N ∩ KK ℚ) ∪ (KK ℚ)ᶜ) ?_ (measure_union_null h0 M.supp)
  intro k hk
  by_cases hkK : k ∈ KK ℚ
  · refine Or.inl ⟨fun v => ?_, hkK⟩
    by_cases hv : v ∈ T
    · exact Set.mem_iInter₂.1 hk v hv
    · refine dv_of_int hN v hv ?_
      exact (HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).1 (hkK.2 v 1 0)
  · exact Or.inr hkK
end

-- bundled from Development.AutomorphicArithmetic.WhittakerHecke.EigAtCmDatumOperatorOfEigAt
section
open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2 UpperTheory.ConvolutionTheory.RankTwoDescent
open scoped Classical
open UpperTheory.ConvolutionTheory.R2.G (FS2 Rw nE row)
open UpperTheory.V.Af.Smo (Eig EigAt)
open scoped ComplexOrder

theorem UpperTheory.eigAt_cmDatumOperator_of_eigAt :
    ∀ (E : Type) [Field E] [NumberField E] (D : Dat ℚ E) (φ : GL (Fin 2) (A E) → ℂ) (w : H.P E) (B : Multiset ℂˣ), Continuous φ → EigAt w B φ → EigAt w B (Wo D φ) := by
  intro E _ _ D φ w B hφ hB g
  have hnE : Continuous (nE D) := by
    have hmkE : Continuous fun x : Fin 2 → A ℚ => D.mkE (x 0) (x 1) :=
      (AdeleBaseChange.continuous_adeleMap.comp (continuous_apply 0)).add
        ((AdeleBaseChange.continuous_adeleMap.comp (continuous_apply 1)).mul continuous_const)
    exact (UpperTheory.ConvolutionTheory.R2.M.continuous_gl.comp
      UpperTheory.ConvolutionTheory.R2.M.continuous_nU).comp hmkE
  have hψ : Continuous (ψ (F := ℚ)) := continuous_subtype_val.comp continuous_adelicChar
  have hi : ∀ h : GL (Fin 2) (A E),
      IntegrableOn (fun x : Fin 2 → A ℚ => φ (nE D x * h) * ψ (x 1)) (FS2 ℚ) (adeleMeasurePi ℚ) := by
    intro h
    obtain ⟨C, hC, hEC⟩ : ∃ C, IsCompact C ∧ fundamentalSet ℚ ⊆ C :=
      ⟨closure (fundamentalSetInfinite ℚ) ×ˢ _,
        (isCompact_closure_fundamentalSetInfinite ℚ).prod (isCompact_integralFiniteAdeles ℚ),
        fun x hx => ⟨subset_closure hx.1, hx.2⟩⟩
    have hK : IsCompact (Set.univ.pi fun _ : Fin 2 => C) := isCompact_univ_pi fun _ => hC
    have hc : Continuous fun x : Fin 2 → A ℚ => φ (nE D x * h) * ψ (x 1) :=
      (hφ.comp (hnE.mul continuous_const)).mul (hψ.comp (continuous_apply 1))
    exact (hc.continuousOn.integrableOn_compact hK).mono_set fun x hx i hi => hEC (hx i hi)
  let G (x : Fin 2 → A ℚ) (y : GL (Fin 2) (w.adicCompletion E)) :=
    φ (nE D x * (g * finGL E 2 (locGL E 2 w y)))
  have hG (x : Fin 2 → A ℚ) : Eig w B (G x) := by
    simpa only [G, mul_assoc] using hB (nE D x * g)
  have hGi (z : GL (Fin 2) (w.adicCompletion E)) :
      Integrable (fun x => G x z * ψ (x 1)) ((adeleMeasurePi ℚ).restrict (FS2 ℚ)) := hi _
  change Eig w B (fun y => ∫ x in FS2 ℚ, G x y * ψ (x 1) ∂(adeleMeasurePi ℚ))
  refine ⟨(hB 1).card, fun y k hk => by simp only [fun x => (hG x).inv y k hk],
    fun ϖ hϖ j hj y => ?_⟩
  have hf := Formalism.UG.P.finite_support_cosets (Formalism.UG.Final.GLintComm E w 2)
    (GlobalTheory.LFun.Tj_mem_hecke (n := 2) hϖ j).2
  have hs (f : GL (Fin 2) (w.adicCompletion E) ⧸ GlobalTheory.LFun.KGL w (n := 2) → ℂ) :
      ∑ᶠ c, Formalism.UG.Tj ℂ 2 (Formalism.UG.Ov E w) ϖ j c.out * f c =
        ∑ c ∈ hf.toFinset, Formalism.UG.Tj ℂ 2 (Formalism.UG.Ov E w) ϖ j c.out * f c := by
    refine finsum_eq_sum_of_support_subset _ fun c hc => ?_
    rw [Set.Finite.coe_toFinset]
    exact left_ne_zero_of_mul hc
  rw [hs]
  simp only [← integral_const_mul]
  rw [← integral_finsetSum _ fun c _ => (hGi _).const_mul _]
  refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
  have e := (hG x).eig ϖ hϖ j hj y
  rw [hs] at e
  simp only [← mul_assoc, ← e, Finset.sum_mul]
end

