module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.HeightTheory.Bundle0010
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.HeightTheory.Bundle0034
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.HeightTheory.Bundle0025
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.HeightTheory.Bundle0032
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.HeightTheory.Bundle0011
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.HeightTheory.Bundle0028
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.HeightTheory.NormFactorizationClause
public import ReciprocityTheory.SemistableReduction.Bundle0025
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.HeightTheory.HintLogFinprod

@[expose] public section

-- bundled from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.HeightTheory.CardEmbPos
section
namespace ReciprocityTheory.ChartRestriction.G.T0

open NumberField

variable {K : Type} [Field K] [NumberField K] {ι : Type} [Fintype ι]
  {Ω : ι → Type} [∀ c, Field (Ω c)] [∀ c, Algebra K (Ω c)]
  {WT : Type} [AddCommGroup WT]
  {A : ι → Type} [∀ c, CommRing (A c)] [∀ c, Algebra (Ω c) (A c)] [∀ c, Algebra K (A c)]
  [∀ c, Algebra (𝓞 K) (A c)]
  {𝒜 : (c : ι) → WT → Submodule (Ω c) (A c)}

namespace Data

variable (d : Data K ι Ω WT A)

theorem card_emb_pos : (0 : ℝ) < Fintype.card (K →+* ℂ) := by
  haveI : Nonempty (K →+* ℂ) := ⟨(IsAlgClosed.lift : K →ₐ[ℚ] ℂ).toRingHom⟩
  exact_mod_cast Fintype.card_pos

theorem meanK_le (F G H : (K →+* ℂ) → ℝ) (C r : ℝ) (hle : ∀ sg, F sg ≤ G sg + C + r * H sg) :
    meanK F ≤ meanK G + C + r * meanK H := by
  have hc : (0 : ℝ) < Fintype.card (K →+* ℂ) := card_emb_pos
  have hs : (∑ sg, F sg) ≤ (∑ sg, G sg) + Fintype.card (K →+* ℂ) * C + r * ∑ sg, H sg := by
    calc (∑ sg, F sg) ≤ ∑ sg, (G sg + C + r * H sg) := Finset.sum_le_sum (fun sg _ => hle sg)
      _ = _ := by
        simp only [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
          Finset.mul_sum]
  unfold meanK
  rw [div_le_iff₀ hc]
  have e : ((∑ sg, G sg) / (Fintype.card (K →+* ℂ) : ℝ) + C +
      r * ((∑ sg, H sg) / (Fintype.card (K →+* ℂ) : ℝ))) * (Fintype.card (K →+* ℂ) : ℝ) =
      (∑ sg, G sg) + Fintype.card (K →+* ℂ) * C + r * ∑ sg, H sg := by
    field_simp <;> ring
  linarith

theorem sg_part (hd : d.AxH 𝒜) (h : d.S1) (hI2be : d.HeightIntegralBoundEstimate) (f : ∀ c, A c)
    (hf : ∀ c, f c ∈ 𝒜 c d.wL ∧ f c ≠ 0) :
    meanK (d.Nsg d.wL f) ≤ meanK (d.NsgMM f) + d.del * (d.tableLineDegreeFive * d.DF + d.cc * d.tableLineDegreeTwo) +
      d.cc / d.i * meanK (d.Nsg (d.n1 • d.wde) d.et) := by
  apply meanK_le
  intro sg
  simp only [Nsg, NsgMM, del, Nat.cast_sum, Finset.sum_mul, Finset.mul_sum,
    ← Finset.sum_add_distrib]
  exact Finset.sum_le_sum (fun c _ => d.sg_one hd h hI2be f hf c sg)

theorem ordMM_fin (hd : d.AxH 𝒜) (c : ι) (f : A c) (hf : f ∈ 𝒜 c d.wL) (hf0 : f ≠ 0) :
    {v | d.admitted c v ∧ (d.ordMM c v f : ℝ) ≠ 0}.Finite := by
  have hA := hd.a3' c hf hf0
  have hB : ∀ j : {j // d.w j c ≠ 0}, {v | d.admitted c v ∧ d.ord c v d.wL (d.w j c) ≠ 0}.Finite :=
    fun j => hd.a3' c (hd.w_mem j c) j.2
  refine (hA.union (Set.finite_iUnion hB)).subset ?_
  rintro v ⟨hv, hne⟩
  by_contra hnot
  simp only [Set.mem_union, Set.mem_setOf_eq, Set.mem_iUnion, not_or, not_exists, not_and,
    not_not] at hnot
  obtain ⟨h1, h2⟩ := hnot
  apply hne
  have e1 : d.ord c v d.wL f = 0 := h1 hv
  have e2 : ∀ j : {j // d.w j c ≠ 0}, d.ord c v d.wL (d.w j c) = 0 := fun j => h2 j hv
  have hinf : (⨅ j : {j // d.w j c ≠ 0}, d.ord c v d.wL (d.w j c)) = 0 := by
    have e3 : (fun j : {j // d.w j c ≠ 0} => d.ord c v d.wL (d.w j c)) = fun _ => 0 := funext e2
    rw [show (⨅ j : {j // d.w j c ≠ 0}, d.ord c v d.wL (d.w j c)) =
      ⨅ _ : {j // d.w j c ≠ 0}, (0 : ℤ) from congrArg iInf e3]
    rcases isEmpty_or_nonempty {j // d.w j c ≠ 0} with hE | hE
    · rw [iInf, Set.range_eq_empty, Int.csInf_empty]
    · exact ciInf_const
  simp only [ordMM, e1, hinf, sub_zero, Int.cast_zero]

theorem la_part (hd : d.AxH 𝒜) (h : d.S1) (hH1 : d.FinitePlaceHyp) (f : ∀ c, A c)
    (hf : ∀ c, f c ∈ 𝒜 c d.wL ∧ f c ≠ 0) :
    (∑ᶠ la, d.NlaG h d.wL f la * logNorm la) ≤ (∑ᶠ la, d.NlaMM h f la * logNorm la) +
      d.del * (∑ᶠ la, d.nu la * logNorm la) +
      d.cc / d.i * (∑ᶠ la, d.NlaG h (d.n1 • d.wde) d.et la * logNorm la) := by
  have hln : ∀ la : IsDedekindDomain.HeightOneSpectrum (𝓞 K), 0 ≤ logNorm la :=
    fun la => Real.log_natCast_nonneg _

  have finG : ∀ (G : WT) (ta : ∀ c, A c), (∀ c, ta c ∈ 𝒜 c G ∧ ta c ≠ 0) →
      (Function.support (fun la => d.NlaG h G ta la * logNorm la)).Finite := by
    intro G ta hta
    have h1 : (Function.support (d.NlaG h G ta)).Finite := by
      refine Set.Finite.subset (Set.finite_iUnion fun c =>
        d.la_fin hd h c (fun v => d.ord c v G (ta c)) (hd.a3' c (hta c).1 (hta c).2)) ?_
      exact d.aNla_supp hd h (fun c v g => d.ord c v G g) ta
    exact h1.subset (fun x hx => left_ne_zero_of_mul hx)
  have finMM : (Function.support (fun la => d.NlaMM h f la * logNorm la)).Finite := by
    have h1 : (Function.support (d.NlaMM h f)).Finite := by
      refine Set.Finite.subset (Set.finite_iUnion fun c =>
        d.la_fin hd h c (fun v => d.ordMM c v (f c)) ?_) ?_
      · refine (d.ordMM_fin hd c (f c) (hf c).1 (hf c).2).subset ?_
        rintro v ⟨hv, hne⟩
        exact ⟨hv, Int.cast_ne_zero.mpr hne⟩
      · exact d.aNla_supp hd h (fun c v g => d.ordMM c v g) f
    exact h1.subset (fun x hx => left_ne_zero_of_mul hx)
  have finNu : (Function.support (fun la => d.nu la * logNorm la)).Finite :=
    hH1.2.1.subset (fun x hx => left_ne_zero_of_mul hx)
  have finL := finG d.wL f hf
  have finE := finG (d.n1 • d.wde) d.et (fun c => ⟨hd.et_mem c, hd.et_ne c⟩)
  have finAll := finMM.union (finNu.union finE)

  have key : ∑ᶠ la, d.NlaG h d.wL f la * logNorm la ≤
      ∑ᶠ la, (d.NlaMM h f la * logNorm la + d.del * (d.nu la * logNorm la) +
        d.cc / d.i * (d.NlaG h (d.n1 • d.wde) d.et la * logNorm la)) := by
    refine finsum_le_finsum' finL (finAll.subset fun x hx => ?_) fun la => ?_
    · by_contra hn
      simp only [Set.mem_union, Function.mem_support, not_or, not_not] at hn
      apply hx
      simp [hn.1, hn.2.1, hn.2.2]
    · have := mul_le_mul_of_nonneg_right (d.Nla_le hd h hH1 f la) (hln la)
      exact this.trans_eq (by ring)
  refine key.trans_eq ?_
  rw [finsum_add_distrib, finsum_add_distrib, mul_finsum, mul_finsum]
  all_goals
    refine finAll.subset fun x hx => ?_
    by_contra hn
    simp only [Set.mem_union, Function.mem_support, not_or, not_not] at hn
    apply hx
    simp [hn.1, hn.2.1, hn.2.2]

end Data

end ReciprocityTheory.ChartRestriction.G.T0
end

-- bundled from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.HeightTheory.HDiscB
section
namespace ReciprocityTheory.ChartRestriction.G.T0

open NumberField

variable {K : Type} [Field K] [NumberField K] {ι : Type} [Fintype ι]
  {Ω : ι → Type} [∀ c, Field (Ω c)] [∀ c, Algebra K (Ω c)]
  {WT : Type} [AddCommGroup WT]
  {A : ι → Type} [∀ c, CommRing (A c)] [∀ c, Algebra (Ω c) (A c)] [∀ c, Algebra K (A c)]
  [∀ c, Algebra (𝓞 K) (A c)]
  {𝒜 : (c : ι) → WT → Submodule (Ω c) (A c)}

namespace Data

variable (d : Data K ι Ω WT A)

theorem disc_global (hd : d.AxH 𝒜) (h : d.S1) (hI2be : d.HeightIntegralBoundEstimate) (ta' : ∀ c, A c)
    (hta' : ∀ c, ta' c ∈ 𝒜 c d.wF ∧ ta' c ≠ 0) :
    (Function.support fun la => d.gOrd la (d.De hd h)).Finite ∧
    (Function.support fun la => d.NlaG h d.wF hd.a4.choose la).Finite ∧
    (∑ᶠ la, ((d.gOrd la (d.De hd h) : ℝ) + 2 * d.NlaG h d.wF hd.a4.choose la) * logNorm la) /
      (Module.finrank ℚ K : ℝ) ≤
      d.del * Real.log d.del +
        2 * ∑ k, meanK (fun sg => Real.log (d.supN sg d.wF (d.thp (hd.sel k)))) +
        2 * d.D * d.aG h d.wF ta' * (Real.log (d.N + 1 : ℕ) + 1 / 2) + 2 * d.Hgt h d.wF ta' := by
  obtain ⟨haG0, ⟨a, b, hab⟩, Om, hOm, hOm0, hOmH⟩ := d.om_poly hd h
  obtain ⟨hs1, hs2, heq⟩ := d.disc_product hd h hI2be a b hab Om hOm
  refine ⟨hs1, hs2, ?_⟩
  rw [heq]
  have ha4 : ∀ c, hd.a4.choose c ∈ 𝒜 c d.wF ∧ hd.a4.choose c ≠ 0 := by
    first
    | exact hd.a4.choose_spec
    | exact hd.a4.choose_spec.1
    | exact fun c => hd.a4.choose_spec.1 c
    | exact fun c => ⟨hd.a4.choose_spec.1 c, hd.a4.choose_spec.2 c⟩
  have hH : d.Hgt h d.wF hd.a4.choose = d.Hgt h d.wF ta' :=
    (d.h_ind hd h hI2be).1 d.wF hd.a4.choose ta' (by simp) ha4 hta'
  have haG : d.aG h d.wF hd.a4.choose = d.aG h d.wF ta' :=
    (d.arithDegree_additive hd h).1 d.wF hd.a4.choose ta' ha4 hta'
  have hcard : (0 : ℝ) < (Fintype.card (K →+* ℂ) : ℝ) := by
    have hc : 0 < Fintype.card (K →+* ℂ) := by
      first
      | (rw [NumberField.Embeddings.card]; exact Module.finrank_pos)
      | exact Fintype.card_pos
      | exact Fintype.card_pos_iff.mpr inferInstance
    exact_mod_cast hc
  have hmean : meanK (fun sg => d.mSgP sg a b - 2 * d.Nsg d.wF hd.a4.choose sg) ≤
      d.del * Real.log d.del +
        2 * ∑ k, meanK (fun sg => Real.log (d.supN sg d.wF (d.thp (hd.sel k)))) := by
    unfold meanK
    rw [div_le_iff₀ hcard]
    calc ∑ sg, (d.mSgP sg a b - 2 * d.Nsg d.wF hd.a4.choose sg)
        ≤ ∑ sg, (d.del * Real.log d.del +
            2 * ∑ k, Real.log (d.supN sg d.wF (d.thp (hd.sel k)))) :=
          Finset.sum_le_sum fun sg _ => d.disc_hadamard hd h hI2be a b hab sg
      _ = (d.del * Real.log d.del + 2 * ((∑ k, ∑ sg,
            Real.log (d.supN sg d.wF (d.thp (hd.sel k)))) / (Fintype.card (K →+* ℂ) : ℝ))) *
            (Fintype.card (K →+* ℂ) : ℝ) := by
          rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
            ← Finset.mul_sum, Finset.sum_comm, add_mul, mul_assoc (2 : ℝ),
            div_mul_cancel₀ _ hcard.ne']
          ring
      _ = _ := by rw [Finset.sum_div]
  have hh0 : -(ReciprocityTheory.MultiplicativeHeights.h0 Om) ≤
      2 * d.D * d.aG h d.wF hd.a4.choose * (Real.log (d.N + 1 : ℕ) + 1 / 2) := by
    have h1 := ReciprocityTheory.MultiplicativeHeights.Closed.sphere_height_lower_bound K (d.D + 1) (d.N + 1) _ Om (Nat.succ_pos _) hOm0 hOmH
    have ht : ((d.aG h d.wF hd.a4.choose).toNat : ℝ) = (d.aG h d.wF hd.a4.choose : ℝ) := by
      exact_mod_cast Int.toNat_of_nonneg haG0
    simp only [Fin.sum_univ_succ, Fin.succ_ne_zero, eq_self_iff_true, if_true, if_false,
      ite_true, ite_false, Nat.cast_zero, zero_mul, zero_add, Finset.sum_const,
      Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, Nat.cast_mul, Nat.cast_ofNat] at h1
    rw [ht] at h1
    linear_combination h1
  rw [hH, ← haG]
  linarith [hmean, hh0]

end Data

end ReciprocityTheory.ChartRestriction.G.T0
end

-- bundled from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.HeightTheory.SphereMeanSubstitutedEqIntegral
section
namespace ReciprocityTheory.ChartRestriction.G.T0

open NumberField MeasureTheory ReciprocityTheory.MultiplicativeHeights

variable {K : Type} [Field K] [NumberField K] {ι : Type} [Fintype ι]
  {Ω : ι → Type} [∀ c, Field (Ω c)] [∀ c, Algebra K (Ω c)]
  {WT : Type} [AddCommGroup WT]
  {A : ι → Type} [∀ c, CommRing (A c)] [∀ c, Algebra (Ω c) (A c)] [∀ c, Algebra K (A c)]
  [∀ c, Algebra (𝓞 K) (A c)]
  {𝒜 : (c : ι) → WT → Submodule (Ω c) (A c)}

namespace Data

variable (d : Data K ι Ω WT A)

theorem eval_substituted_eq_eval_update (x : Fin (d.N + 1) → K) (F : KTp K d.D d.N) (sg : K →+* ℂ)
    (y : Fin (d.D + 1) × Fin (d.N + 1) → ℂ) :
    MvPolynomial.eval y (MvPolynomial.map sg (d.translatedForm x F)) =
      MvPolynomial.eval (fun v => if v.1 = 0 then sg (x v.2) else y v) (MvPolynomial.map sg F) := by
  unfold translatedForm
  induction F using MvPolynomial.induction_on with
  | C a => simp
  | add p q hp hq => simp only [map_add (f := _), hp, hq]
  | mul_X p v hp =>
    simp only [map_mul, hp, MvPolynomial.aeval_X, MvPolynomial.map_X, MvPolynomial.eval_X]
    congr 1
    by_cases hv : v.1 = 0 <;> simp [hv]

theorem eval_substituted_shift_invariant (x : Fin (d.N + 1) → K) (F : KTp K d.D d.N) (sg : K →+* ℂ)
    (t0 : Fin (d.N + 1) → ℂ) (z : BlockSphere d.D (d.N + 1)) :
    MvPolynomial.eval (hintPt t0 z) (MvPolynomial.map sg (d.translatedForm x F)) =
      MvPolynomial.eval (hintPt 0 z) (MvPolynomial.map sg (d.translatedForm x F)) := by
  rw [eval_substituted_eq_eval_update, eval_substituted_eq_eval_update]
  refine congrArg (fun y => MvPolynomial.eval y (MvPolynomial.map sg F)) (funext fun v => ?_)
  by_cases hv : v.1 = 0
  · simp only [hv, ↓reduceIte]
  · simp only [hv, ↓reduceIte]
    obtain ⟨a, b⟩ := v
    cases a using Fin.cases with
    | zero => exact absurd rfl hv
    | succ i => rfl

theorem sphereMean_substituted_eq_integral (x : Fin (d.N + 1) → K) (F : KTp K d.D d.N) (sg : K →+* ℂ) :
    blockSphereMean (d.D + 1) (d.N + 1) (MvPolynomial.map sg (d.translatedForm x F)) =
      ∫ z, Real.log ‖MvPolynomial.eval (hintPt 0 z) (MvPolynomial.map sg (d.translatedForm x F))‖
        ∂(blockSphereProb d.D (d.N + 1)) := by
  have hpt : ∀ z : BlockSphere (d.D + 1) (d.N + 1),
      MvPolynomial.eval (blockPoint z) (MvPolynomial.map sg (d.translatedForm x F)) =
        MvPolynomial.eval (hintPt 0 (Fin.tail z)) (MvPolynomial.map sg (d.translatedForm x F)) := by
    intro z
    rw [← eval_substituted_shift_invariant d x F sg (spherePoint (z 0)) (Fin.tail z)]
    refine congrArg (fun y => MvPolynomial.eval y (MvPolynomial.map sg (d.translatedForm x F)))
      (funext fun v => ?_)
    obtain ⟨a, b⟩ := v
    cases a using Fin.cases with
    | zero => rfl
    | succ i => rfl
  have key : ∀ g : (Fin d.D → UnitSphereC (d.N + 1)) → ℝ,
      ∫ z, g (Fin.tail z) ∂(Measure.pi fun _ : Fin (d.D + 1) => sphereProb (d.N + 1)) =
        ∫ w, g w ∂(Measure.pi fun _ : Fin d.D => sphereProb (d.N + 1)) := by
    intro g
    haveI hpr : IsProbabilityMeasure (sphereProb (d.N + 1)) :=
      ReciprocityTheory.MultiplicativeHeights.isProbabilityMeasure_sphereProb (Nat.succ_pos _)
    haveI hfin : IsFiniteMeasure (sphereProb (d.N + 1)) :=
      ⟨by rw [MeasureTheory.measure_univ]; exact ENNReal.one_lt_top⟩
    haveI hsf : SigmaFinite (sphereProb (d.N + 1)) :=
      @MeasureTheory.IsFiniteMeasure.toSigmaFinite _ _ _ hfin
    haveI hsf' : ∀ i : Fin (d.D + 1), SigmaFinite ((fun _ : Fin (d.D + 1) => sphereProb (d.N + 1)) i) :=
      fun _ => hsf
    have hmp := MeasureTheory.measurePreserving_piFinSuccAbove
      (fun _ : Fin (d.D + 1) => sphereProb (d.N + 1)) 0
    calc ∫ z, g (Fin.tail z) ∂(Measure.pi fun _ : Fin (d.D + 1) => sphereProb (d.N + 1))
        = ∫ z, (fun p : UnitSphereC (d.N + 1) × (Fin d.D → UnitSphereC (d.N + 1)) => g p.2)
            (MeasurableEquiv.piFinSuccAbove (fun _ => UnitSphereC (d.N + 1)) 0 z)
            ∂(Measure.pi fun _ : Fin (d.D + 1) => sphereProb (d.N + 1)) := by
          congr 1
      _ = ∫ p, g p.2 ∂((sphereProb (d.N + 1)).prod
            (Measure.pi fun _ : Fin d.D => sphereProb (d.N + 1))) :=
          hmp.integral_comp' (fun p : UnitSphereC (d.N + 1) × (Fin d.D → UnitSphereC (d.N + 1)) => g p.2)
      _ = ∫ w, g w ∂(Measure.pi fun _ : Fin d.D => sphereProb (d.N + 1)) := by
          rw [MeasureTheory.integral_fun_snd]
          simp
  unfold blockSphereMean blockSphereProb
  simp_rw [hpt]
  exact key (fun w => Real.log ‖MvPolynomial.eval (hintPt 0 w) (MvPolynomial.map sg (d.translatedForm x F))‖)

theorem sphereMean_fubini {F : MvPolynomial (Fin (d.D + 1) × Fin (d.N + 1)) ℂ} {a : Fin (d.D + 1) → ℕ}
    (hF0 : F ≠ 0) (hF : IsMultiHomogeneous a F) :
    blockSphereMean (d.D + 1) (d.N + 1) F =
      ∫ z, (∫ s, Real.log ‖MvPolynomial.eval (hintPt (spherePoint s) z) F‖ ∂(sphereProb (d.N + 1)))
        ∂(blockSphereProb d.D (d.N + 1)) := by
  have hn : 0 < d.N + 1 := Nat.succ_pos _
  haveI := sphereMeasure_isProbability hn
  haveI := blockSphereMeasure_isProbability (B := d.D) hn
  set G : UnitSphereC (d.N + 1) × BlockSphere d.D (d.N + 1) → ℝ :=
    fun p => Real.log ‖MvPolynomial.eval (hintPt (spherePoint p.1) p.2) F‖ with hG
  have hmp := hint_mpSplit d.D (d.N + 1) hn
  have hint : Integrable G ((sphereProb (d.N + 1)).prod (blockSphereProb d.D (d.N + 1))) := by
    rw [← hmp.integrable_comp_emb
      (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (d.D + 1) => UnitSphereC (d.N + 1)) 0).measurableEmbedding]
    refine (ReciprocityTheory.MultiplicativeHeights.Closed.sphereLogIntegrable (d.D + 1) (d.N + 1) a F hF0 hF).congr
      (Filter.Eventually.of_forall fun z => ?_)
    simp only [Function.comp_apply, hG]
    rw [hint_blockPoint_eq]
    rfl
  rw [← integral_prod_symm G hint]
  unfold blockSphereMean
  rw [← hmp.integral_comp
    (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (d.D + 1) => UnitSphereC (d.N + 1)) 0).measurableEmbedding]
  refine integral_congr_ae (Filter.Eventually.of_forall fun z => ?_)
  simp only [hG]
  rw [hint_blockPoint_eq]
  rfl

end Data

end ReciprocityTheory.ChartRestriction.G.T0
end

