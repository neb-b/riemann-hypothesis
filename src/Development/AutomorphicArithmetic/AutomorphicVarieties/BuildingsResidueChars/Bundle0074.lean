module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.IntegralCompression.LAbove
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.UnipotentBlockMatrices.ClosedKernelMinors.Bundle0001
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.UnipotentBlockMatrices.ClosedKernelMinors.Bundle0005

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.FiniteDimensionalSpanMaximalCompactTranslatesOfF
section
open MeasureTheory NumberField Filter Topology Matrix
open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace GroundTheory.Automorphic.AutomorphicForm
open GroundTheory.Automorphic.CuspidalSpectrum GroundTheory.Automorphic.ArchWhittakerC UpperTheory.ConvolutionTheory UpperTheory.ConvolutionTheory.C UpperTheory.ConvolutionTheory.L1 PositivityTheory.Rg.Tf.Core PositivityTheory.Rg.Tf.Adel
open UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial.E UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial.EA
open scoped ComplexConjugate Classical InnerProductSpace
open scoped NumberField.AdeleRing

theorem UpperTheory.finiteDimensional_span_maximalCompact_translates_of_fix :
    ∀ {K : Type} [Field K] [NumberField K] {n : ℕ} (D : TypeDat K n) (f : G1 K n → ℂ), Continuous f → D.Fix f → FiniteDimensional ℂ (Submodule.span ℂ (Set.range fun k : KG K n => fun m => f (m * k))) := by
  intro K _ _ n D f hf hfix
  obtain ⟨-, -, 𝒜, hfd, -, hA⟩ := typeFin D
  haveI := hfd
  obtain ⟨O, hO, hUO⟩ := D.isOpen
  haveI : CompactSpace (KG K n) :=
    isCompact_iff_compactSpace.1 ((blkLaws (K := K)).2.2.2.2.2.2.2.2.2.2.2 n).1
  let W : Subgroup (KG K n) := D.U.subgroupOf (KG K n)
  have hWo : IsOpen (W : Set (KG K n)) := by
    have hW : (W : Set (KG K n)) = (fun k : KG K n => ((k : G1 K n) : AdelicGLn.AdelicGL K n)) ⁻¹' O := by
      ext k
      exact ⟨fun h => ((hUO k).1 h).1, fun h => (hUO k).2 ⟨h, k.2⟩⟩
    rw [hW]
    exact hO.preimage (continuous_subtype_val.comp continuous_subtype_val)
  haveI : Finite (KG K n ⧸ W) := Subgroup.quotient_finite_of_isOpen W hWo
  let B := Module.finBasis ℂ 𝒜
  let x : G1 K n → 𝒜 := fun m => ⟨fun u : D.U => f (m * u), hA f hf hfix m⟩
  let c : Fin (Module.finrank ℂ 𝒜) × (KG K n ⧸ W) → G1 K n → ℂ :=
    fun p m => B.repr (x (m * ((Quotient.out p.2 : KG K n) : G1 K n))) p.1
  have hfin : FiniteDimensional ℂ (Submodule.span ℂ (Set.range c)) :=
    FiniteDimensional.span_of_finite ℂ (Set.finite_range c)
  refine Submodule.finiteDimensional_of_le (S₂ := Submodule.span ℂ (Set.range c)) (Submodule.span_le.2 ?_)
  rintro _ ⟨k, rfl⟩
  obtain ⟨h, hh⟩ := QuotientGroup.mk_out_eq_mul W k
  set q : KG K n ⧸ W := (k : KG K n ⧸ W) with hq
  let u : D.U := ⟨(((h : KG K n)⁻¹ : KG K n) : G1 K n), Subgroup.mem_subgroupOf.1 (W.inv_mem h.2)⟩
  have hk : (k : G1 K n) = ((Quotient.out q : KG K n) : G1 K n) * u := by
    have : k = Quotient.out q * (h : KG K n)⁻¹ := by
      rw [hh]; simp
    exact congrArg Subtype.val this
  have e : (fun m => f (m * k)) = ∑ i, ((B i : 𝒜) : D.U → ℂ) u • c (i, q) := by
    funext m
    have h1 := congrArg (fun y : 𝒜 => (y : D.U → ℂ) u)
      (B.sum_repr (x (m * ((Quotient.out q : KG K n) : G1 K n))))
    simp only [Submodule.coe_sum, Submodule.coe_smul, Finset.sum_apply, Pi.smul_apply, smul_eq_mul] at h1
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
    rw [hk, ← mul_assoc]
    change _ = ∑ i, ((B i : 𝒜) : D.U → ℂ) u * B.repr (x (m * ((Quotient.out q : KG K n) : G1 K n))) i
    simp only [mul_comm (((B _ : 𝒜) : D.U → ℂ) u)]
    exact h1.symm
  change (fun m => f (m * (k : G1 K n))) ∈ Submodule.span ℂ (Set.range c)
  rw [e]
  exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨(i, q), rfl⟩)
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.MaximalCompactUniqueArchFiniteDecomposition
section
open MeasureTheory NumberField Filter Topology Matrix
open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace GroundTheory.Automorphic.AutomorphicForm
open GroundTheory.Automorphic.CuspidalSpectrum GroundTheory.Automorphic.ArchWhittakerC UpperTheory.ConvolutionTheory UpperTheory.ConvolutionTheory.C UpperTheory.ConvolutionTheory.L1 PositivityTheory.Rg.Tf.Core PositivityTheory.Rg.Tf.Adel
open UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial.E UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial.EA
open scoped ComplexConjugate Classical InnerProductSpace
open scoped NumberField.AdeleRing

section SlopeTestRemainingChoices

variable {K : Type} [Field K] [NumberField K] {n : ℕ}

private theorem archimedean_projection_val (a : archCompact K n) :
    ((arc1 a : G1 K n) : AdelicGLn.AdelicGL K n) = infEmb K n (a : archGroup K n) :=
  congrArg Subtype.val (archProj_of_mem (A := ((a : archGroup K n) : ArchUnits K n))
    (maxCompact_le_normOneGL a.2))

private theorem finite_projection_integral_val (h : AdelicGLn.integralFiniteGL K n) :
    ((fin1 (h : FA K n) : G1 K n) : AdelicGLn.AdelicGL K n) = finEmb K n (h : FA K n) :=
  congrArg Subtype.val (MultiplicityOne.finProj_of_mem (maxCompact_le_normOneGL (finEmb_mem_maxCompact h.2)))

end SlopeTestRemainingChoices

theorem UpperTheory.maximalCompact_unique_arch_finite_decomposition :
    ∀ {K : Type} [Field K] [NumberField K] (n : ℕ), ∃ (α : KG K n → archCompact K n) (β : KG K n → AdelicGLn.integralFiniteGL K n), Continuous α ∧ Continuous β ∧ (∀ k : KG K n, (k : G1 K n) = arc1 (α k) * fin1 (β k : FA K n)) ∧ (∀ (a : archCompact K n) (h : AdelicGLn.integralFiniteGL K n) (k : KG K n), (k : G1 K n) = arc1 a * fin1 (h : FA K n) → α k = a ∧ β k = h) ∧ (∀ a : archCompact K n, arc1 a ∈ KG K n) ∧ ∀ h : AdelicGLn.integralFiniteGL K n, fin1 (h : FA K n) ∈ KG K n := by
  intro K _ _ n
  have hval : Continuous fun k : KG K n => ((k : G1 K n) : AdelicGLn.AdelicGL K n) :=
    continuous_subtype_val.comp continuous_subtype_val
  have hpe : Continuous fun k : KG K n => AdelicGLn.prodEquiv K n ((k : G1 K n) : AdelicGLn.AdelicGL K n) :=
    (AdelicGLn.prodEquiv K n).continuous.comp hval
  refine ⟨fun k => ⟨archPart ((k : G1 K n) : AdelicGLn.AdelicGL K n), archPart_mem_archCompact k.2⟩,
    fun k => ⟨finPart ((k : G1 K n) : AdelicGLn.AdelicGL K n), finPart_mem_integralFiniteGL k.2⟩,
    ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact Continuous.subtype_mk ((archEquiv K n).continuous.comp (continuous_fst.comp hpe)) _
  · exact Continuous.subtype_mk (continuous_snd.comp hpe) _
  · intro k
    apply Subtype.ext
    rw [Subgroup.coe_mul, archimedean_projection_val, finite_projection_integral_val]
    exact (infEmb_mul_finEmb _).symm
  · intro a h k hk
    have e : ((k : G1 K n) : AdelicGLn.AdelicGL K n) = infEmb K n (a : archGroup K n) * finEmb K n (h : FA K n) := by
      rw [hk, Subgroup.coe_mul, archimedean_projection_val, finite_projection_integral_val]
    have e' : AdelicGLn.prodEquiv K n ((k : G1 K n) : AdelicGLn.AdelicGL K n) =
        ((archEquiv K n).symm (a : archGroup K n), (h : FA K n)) := by
      rw [e, map_mul, prodEquiv_infEmb, prodEquiv_finEmb]
      simp
    constructor
    · apply Subtype.ext
      change archEquiv K n (AdelicGLn.prodEquiv K n ((k : G1 K n) : AdelicGLn.AdelicGL K n)).1 = _
      rw [e']
      simp
    · apply Subtype.ext
      change (AdelicGLn.prodEquiv K n ((k : G1 K n) : AdelicGLn.AdelicGL K n)).2 = _
      rw [e']
  · intro a
    change ((arc1 a : G1 K n) : AdelicGLn.AdelicGL K n) ∈ Reduction.maxCompact
    rw [archimedean_projection_val]
    exact a.2
  · intro h
    change ((fin1 (h : FA K n) : G1 K n) : AdelicGLn.AdelicGL K n) ∈ Reduction.maxCompact
    rw [finite_projection_integral_val]
    exact finEmb_mem_maxCompact h.2
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.UnipotentMemMaximalCompactFiniteIntegral
section
open MeasureTheory NumberField Filter Topology Matrix
open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace GroundTheory.Automorphic.AutomorphicForm
open GroundTheory.Automorphic.CuspidalSpectrum GroundTheory.Automorphic.ArchWhittakerC UpperTheory.ConvolutionTheory UpperTheory.ConvolutionTheory.C UpperTheory.ConvolutionTheory.L1 PositivityTheory.Rg.Tf.Core PositivityTheory.Rg.Tf.Adel
open UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial.E UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial.EA
open scoped ComplexConjugate Classical InnerProductSpace
open scoped NumberField.AdeleRing

private theorem off_diag_zero {E : Type} [NormedField E] {n : ℕ} (k : Matrix (Fin n) (Fin n) E)
    (hk : ∀ y : Fin n → E, euclidNorm (y ᵥ* k) = euclidNorm y) {i j : Fin n} (hii : k i i = 1) (hij : i ≠ j) :
    k i j = 0 := by
  have hrow : (Pi.single i 1 : Fin n → E) ᵥ* k = k i := by
    funext l
    simp [Matrix.vecMul, dotProduct, Pi.single_apply]
  have h1 := hk (Pi.single i 1)
  rw [hrow] at h1
  have hs : ∑ l, ‖(Pi.single i 1 : Fin n → E) l‖ ^ 2 = 1 := by
    rw [Finset.sum_eq_single i]
    · simp
    · intro b _ hb
      simp [Pi.single_apply, hb]
    · simp
  have h2 : ∑ l, ‖k i l‖ ^ 2 = 1 := by
    have := congrArg (· ^ 2) h1
    simp only [euclidNorm] at this
    rw [Real.sq_sqrt (Finset.sum_nonneg fun _ _ => sq_nonneg _),
      Real.sq_sqrt (Finset.sum_nonneg fun _ _ => sq_nonneg _), hs] at this
    exact this
  have h3 : ‖k i i‖ ^ 2 + ‖k i j‖ ^ 2 ≤ ∑ l, ‖k i l‖ ^ 2 := by
    rw [← Finset.sum_pair (f := fun l => ‖k i l‖ ^ 2) hij]
    exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) fun _ _ _ => sq_nonneg _
  rw [h2, hii, norm_one] at h3
  have h4 : ‖k i j‖ ^ 2 ≤ 0 := by linarith
  have h5 : ‖k i j‖ = 0 := by
    have := sq_nonneg ‖k i j‖
    exact pow_eq_zero_iff (two_ne_zero) |>.1 (le_antisymm h4 this)
  exact norm_eq_zero.1 h5

theorem UpperTheory.unipotent_mem_maximalCompact_finite_integral :
    ∀ {K : Type} [Field K] [NumberField K] (X : UPos (2 + 2) 2 → NumberField.AdeleRing (𝓞 K) K), nn X ∈ KG K (2 + 2) → ∃ h : AdelicGLn.integralFiniteGL K (2 + 2), nn X = fin1 (h : FA K (2 + 2)) := by
  intro K _ _ X hX
  have hK : ((nn X : G1 K (2 + 2)) : AdelicGLn.AdelicGL K (2 + 2)) ∈
      (maxCompact : Subgroup (AdelicGLn.AdelicGL K (2 + 2))) := hX
  obtain ⟨hinf, hfin⟩ := hK
  have hent : ∀ a b, ((nn X : G1 K (2 + 2)) : AdelicGLn.AdelicGL K (2 + 2)) a b = unipMatrix X a b := fun _ _ => rfl
  have hz : ∀ (p : UPos (2 + 2) 2) (w : InfinitePlace K), (X p).1 w = 0 := by
    intro p w
    have hne : p.1.1 ≠ p.1.2 := by
      intro h
      have := p.2
      rw [h] at this
      omega
    have hii : ((infAt w ((nn X : G1 K (2 + 2)) : AdelicGLn.AdelicGL K (2 + 2)) : GL (Fin (2 + 2)) w.Completion) :
        Matrix (Fin (2 + 2)) (Fin (2 + 2)) w.Completion) p.1.1 p.1.1 = 1 := by
      have hp := p.2.1
      change (((nn X : G1 K (2 + 2)) : AdelicGLn.AdelicGL K (2 + 2)) p.1.1 p.1.1).1 w = 1
      rw [hent, unipMatrix, Matrix.add_apply, blockEntry_apply, dite_eq_right (by omega)]
      simp
    have h0 := off_diag_zero _ (hinf w) hii hne
    change (((nn X : G1 K (2 + 2)) : AdelicGLn.AdelicGL K (2 + 2)) p.1.1 p.1.2).1 w = 0 at h0
    rw [hent, unipMatrix, Matrix.add_apply, blockEntry_apply, dite_eq_left p.2, Matrix.one_apply_ne hne, zero_add] at h0
    exact h0
  set g : AdelicGLn.AdelicGL K (2 + 2) := ((nn X : G1 K (2 + 2)) : AdelicGLn.AdelicGL K (2 + 2)) with hg
  have h1 : (AdelicGLn.prodEquiv K (2 + 2) g).1 = 1 := by
    apply Units.ext
    refine Matrix.ext fun a b => ?_
    change (g a b).1 = (1 : Matrix (Fin (2 + 2)) (Fin (2 + 2)) (InfiniteAdeleRing K)) a b
    rw [hent, unipMatrix, Matrix.add_apply, blockEntry_apply]
    by_cases hab : a = b
    · subst hab
      rw [dite_eq_right (by omega), Matrix.one_apply_eq, Matrix.one_apply_eq, add_zero]
      rfl
    · rw [Matrix.one_apply_ne hab, Matrix.one_apply_ne hab]
      split_ifs with h
      · have hw : (X ⟨(a, b), h⟩).1 = 0 := funext fun w => hz _ w
        simp [hw]
      · simp
  have hint : (AdelicGLn.prodEquiv K (2 + 2) g).2 ∈ AdelicGLn.integralFiniteGL K (2 + 2) :=
    (AdelicGLn.mem_integralFiniteGL_iff_forall K (2 + 2)).2 hfin
  have hgf : finEmb K (2 + 2) (AdelicGLn.prodEquiv K (2 + 2) g).2 = g := by
    have := infEmb_mul_finEmb g
    rwa [h1, map_one, map_one, one_mul] at this
  refine ⟨⟨_, hint⟩, ?_⟩
  have hmem : finEmb K (2 + 2) (AdelicGLn.prodEquiv K (2 + 2) g).2 ∈ normOneGL (K := K) (n := (2 + 2)) := by
    rw [hgf]
    exact (nn X).2
  apply Subtype.ext
  change g = ((MultiplicityOne.finProj K (2 + 2) (AdelicGLn.prodEquiv K (2 + 2) g).2 : normOneGL (K := K) (n := (2 + 2))) : AdelicGLn.AdelicGL K (2 + 2))
  rw [MultiplicityOne.finProj_of_mem hmem]
  exact hgf.symm
end

