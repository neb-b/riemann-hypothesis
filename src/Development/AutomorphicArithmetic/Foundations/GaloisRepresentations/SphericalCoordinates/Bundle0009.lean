module

public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.Bundle0005

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.PSimDiag
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.PELU Filter Topology
open scoped Matrix
open GlobalTheory.HodgeCoh GlobalTheory.CechDR Polynomial UpperTheory.Gal.W2

private theorem span_joint (g : ℕ) (I : Type) (M : I → Matrix (Fin g) (Fin g) ℂ)
    (hc : ∀ i j, M i * M j = M j * M i)
    (hp : ∀ i, ∃ p : ℂ[X], p.Separable ∧ aeval (M i) p = 0) :
    Submodule.span ℂ {v : Fin g → ℂ | ∃ c : I → ℂ, ∀ i, (M i).mulVec v = c i • v} = ⊤ := by
  classical
  let f : I → Module.End ℂ (Fin g → ℂ) := fun i => Matrix.toLinAlgEquiv' (M i)
  have hss : ∀ i, (f i).IsFinitelySemisimple := by
    intro i
    obtain ⟨p, hsep, hpz⟩ := hp i
    apply Module.End.IsSemisimple.isFinitelySemisimple
    apply Module.End.isSemisimple_of_squarefree_aeval_eq_zero hsep.squarefree
    show aeval (Matrix.toLinAlgEquiv' (M i)) p = 0
    rw [Polynomial.aeval_algEquiv]
    simp [hpz]
  have hcomm : Pairwise fun i j => Commute (f i) (f j) := by
    intro i j _
    show Matrix.toLinAlgEquiv' (M i) * Matrix.toLinAlgEquiv' (M j) =
      Matrix.toLinAlgEquiv' (M j) * Matrix.toLinAlgEquiv' (M i)
    rw [← map_mul, ← map_mul, hc]
  have htop : ∀ i, iSup (fun t => (f i).maxGenEigenspace t) = ⊤ :=
    fun i => Module.End.iSup_maxGenEigenspace_eq_top (f i)
  have hall := Module.End.iSup_iInf_maxGenEigenspace_eq_top_of_iSup_maxGenEigenspace_eq_top_of_commute
    f hcomm htop
  rw [eq_top_iff, ← hall]
  refine iSup_le fun χ => ?_
  intro v hv
  apply Submodule.subset_span
  refine ⟨χ, fun i => ?_⟩
  have hvi : v ∈ (f i).maxGenEigenspace (χ i) := (Submodule.mem_iInf _).1 hv i
  rw [(hss i).maxGenEigenspace_eq_eigenspace, Module.End.mem_eigenspace_iff] at hvi
  simpa [f] using hvi

theorem UpperTheory.Gal.W2.simDiag_of :
    UpperTheory.Gal.W2.SimDiag := by
  intro g I M hc hp
  classical
  have hspan := span_joint g I M hc hp
  obtain ⟨b, hbS, hbspan, hli⟩ :=
    exists_linearIndependent ℂ {v : Fin g → ℂ | ∃ c : I → ℂ, ∀ i, (M i).mulVec v = c i • v}
  let B := Module.Basis.mk hli (le_of_eq (by rw [Subtype.range_coe, hbspan, hspan]))
  let B' := B.reindex (B.indexEquiv (Pi.basisFun ℂ (Fin g)))
  have hmem : ∀ k, ∃ c : I → ℂ, ∀ i, (M i).mulVec (B' k) = c i • B' k := by
    intro k
    have : B' k ∈ b := by
      simp only [B', B, Module.Basis.reindex_apply, Module.Basis.mk_apply]
      exact Subtype.mem _
    exact hbS this
  choose c hc' using hmem
  refine ⟨(Pi.basisFun ℂ (Fin g)).toMatrix B', fun i k => c k i, ?_, fun i => ?_⟩
  · rw [← Module.Basis.det_apply]
    exact ((Pi.basisFun ℂ (Fin g)).isUnit_det B').ne_zero
  · ext r k
    rw [Matrix.mul_diagonal]
    have h := congr_fun (hc' k i) r
    simp only [Matrix.mulVec, dotProduct, Pi.smul_apply, smul_eq_mul] at h
    simp only [Matrix.mul_apply, Module.Basis.toMatrix_apply, Pi.basisFun_repr]
    rw [h, mul_comm]
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.PTraceDual
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.PELU Filter Topology
open scoped Matrix
open GlobalTheory.HodgeCoh GlobalTheory.CechDR Polynomial UpperTheory.Gal.W2

theorem UpperTheory.Gal.W2.traceDual_of :
    UpperTheory.Gal.W2.TraceDual := by
  intro F _ _ s hs
  classical
  let e := NumberField.RingOfIntegers.basis F
  choose m hm using fun k => hs (e k)
  let L : F →ₗ[ℚ] ℚ := (NumberField.integralBasis F).constr ℚ (fun k => (m k : ℚ))
  let D := (Algebra.traceForm ℚ F).toDual (traceForm_nondegenerate ℚ F)
  let b : F := D.symm L
  have hb : ∀ x : F, Algebra.trace ℚ F (b * x) = L x := by
    intro x
    have h := LinearMap.congr_fun (D.apply_symm_apply L) x
    rw [LinearMap.BilinForm.toDual_def, Algebra.traceForm_apply] at h
    exact h
  have htr : ∀ x : F, algebraMap ℚ ℂ (Algebra.trace ℚ F x) = ∑ τ : F →+* ℂ, τ x := by
    intro x
    rw [trace_eq_sum_embeddings ℂ]
    exact Fintype.sum_equiv (RingHom.equivRatAlgHom F ℂ).symm _ _ (fun σ => rfl)
  have hk : ∀ k, ∑ τ : F →+* ℂ, τ (e k : F) * (τ b - s τ) = 0 := by
    intro k
    simp only [mul_sub, Finset.sum_sub_distrib, ← map_mul]
    rw [hm k, ← htr, mul_comm (e k : F) b, hb, sub_eq_zero]
    have he : (e k : F) = NumberField.integralBasis F k := by
      rw [NumberField.integralBasis_apply]
    rw [he, Module.Basis.constr_basis]
    simp
  let P : ((F →+* ℂ) → ℂ) →ₗ[ℂ] ℂ := ∑ τ, (τ b - s τ) • LinearMap.proj τ
  have hP : P = 0 := by
    apply (NumberField.canonicalEmbedding.latticeBasis F).ext
    intro k
    simp only [P, NumberField.canonicalEmbedding.latticeBasis_apply, LinearMap.sum_apply,
      LinearMap.smul_apply, LinearMap.proj_apply,
      NumberField.canonicalEmbedding.apply_at, smul_eq_mul, LinearMap.zero_apply]
    rw [← hk k]
    refine Finset.sum_congr rfl fun τ _ => ?_
    rw [mul_comm, NumberField.integralBasis_apply]
  refine ⟨b, fun τ => ?_⟩
  have h := LinearMap.congr_fun hP (Pi.single τ 1)
  simp [P, Pi.single_apply] at h
  rw [sub_eq_zero] at h
  exact h.symm
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.PTraceLat
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.PELU Filter Topology
open scoped Matrix
open GlobalTheory.HodgeCoh GlobalTheory.CechDR Polynomial UpperTheory.Gal.W2

private lemma realTrace_toLin (g : ℕ) (H : Matrix (Fin g) (Fin g) ℂ) :
    ((LinearMap.trace ℝ (Fin g → ℂ) ((Matrix.toLin' H).restrictScalars ℝ) : ℝ) : ℂ) =
      H.trace + (starRingEnd ℂ) H.trace := by
  rw [LinearMap.trace_eq_matrix_trace ℝ (Complex.basisOneI.smulTower' (Pi.basisFun ℂ (Fin g))),
    LinearMap.restrictScalars_toMatrix]
  simp only [Matrix.trace, Matrix.diag, Fintype.sum_prod_type, Matrix.comp_apply, Matrix.map_apply]
  have hb : ∀ z : ℂ, ∑ a, Algebra.leftMulMatrix Complex.basisOneI z a a = 2 * z.re := by
    intro z
    rw [← Algebra.trace_complex_apply, Algebra.trace_eq_matrix_trace Complex.basisOneI]
    rfl
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [hb, LinearMap.toMatrix_eq_toMatrix', LinearMap.toMatrix'_toLin', map_sum, ← Finset.sum_add_distrib,
    Complex.add_conj]
  push_cast
  rfl

private lemma trace_of_basis (L : Type) [AddCommGroup L] [Module.Free ℤ L] [Module.Finite ℤ L] (g : ℕ)
    (P : L →+ (Fin g → ℂ)) (hinj : Function.Injective P)
    (hd : DiscreteTopology P.range) (hs : Submodule.span ℝ (Set.range P) = ⊤)
    (f : L →ₗ[ℤ] L) (H : Matrix (Fin g) (Fin g) ℂ) (hf : ∀ x, P (f x) = H *ᵥ P x) :
    ((LinearMap.trace ℤ L f : ℤ) : ℝ) =
      LinearMap.trace ℝ (Fin g → ℂ) ((Matrix.toLin' H).restrictScalars ℝ) := by
  classical
  let b := Module.Free.chooseBasis ℤ L
  let Lsub : Submodule ℤ (Fin g → ℂ) := LinearMap.range P.toIntLinearMap
  have hcar : (Lsub : Set (Fin g → ℂ)) = Set.range P := LinearMap.coe_range _
  haveI : DiscreteTopology Lsub := hd
  haveI : IsZLattice ℝ Lsub := ⟨by rw [hcar]; exact hs⟩
  let e : L ≃ₗ[ℤ] Lsub := LinearEquiv.ofInjective P.toIntLinearMap hinj
  let bV := (b.map e).ofZLatticeBasis ℝ Lsub
  have hbV : ∀ i, bV i = P (b i) := fun i => by
    simp [bV, e]
    rfl
  rw [LinearMap.trace_eq_matrix_trace ℤ b, LinearMap.trace_eq_matrix_trace ℝ bV]
  have hM : LinearMap.toMatrix bV bV ((Matrix.toLin' H).restrictScalars ℝ) =
      (LinearMap.toMatrix b b f).map (Int.cast : ℤ → ℝ) := by
    ext i j
    have hsum : (Matrix.toLin' H).restrictScalars ℝ (bV j) =
        ∑ k, ((b.repr (f (b j)) k : ℤ) : ℝ) • bV k := by
      rw [LinearMap.restrictScalars_apply, hbV, Matrix.toLin'_apply, ← hf]
      conv_lhs => rw [← b.sum_repr (f (b j))]
      set_option synthInstance.maxHeartbeats 100000 in
        rw [map_sum]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [map_zsmul, hbV, Int.cast_smul_eq_zsmul]
    rw [LinearMap.toMatrix_apply, hsum, Matrix.map_apply, LinearMap.toMatrix_apply, bV.repr_sum_self]
  rw [hM, Matrix.trace, Matrix.trace]
  simp

theorem UpperTheory.Gal.W2.traceLat_of :
    UpperTheory.Gal.W2.TraceLat := by
  intro L _ _ _ g P hinj hd hs f H hf
  rw [← realTrace_toLin, ← trace_of_basis L g P hinj hd hs f H hf]
  push_cast
  rfl
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.PTspDiag
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.PELU Filter Topology
open scoped Matrix
open GlobalTheory.HodgeCoh GlobalTheory.CechDR Polynomial UpperTheory.Gal.W2

theorem UpperTheory.Gal.W2.tspDiag_of :
    UpperTheory.Gal.W2.TspDiag := by
  intro F _ _ g ty t₀ i₀ hc hi hij W hW
  classical
  have hpat : ∀ S : Matrix (Fin g) (Fin g) ℂ, S ∈ W → ∀ i j, S i j ≠ 0 →
      ty j = ComplexEmbedding.conjugate (ty i) := by
    intro S hS i j hne
    have h := ((hW S).1 hS).2
    have hcc : ∀ c : 𝓞 F, ty j (c : F) = (starRingEnd ℂ) (ty i (c : F)) := fun c =>
      mul_left_cancel₀ hne (by rw [h c i j, mul_comm])
    refine IsLocalization.ringHom_ext (nonZeroDivisors (𝓞 F)) ?_
    ext c
    simpa [ComplexEmbedding.conjugate_coe_eq] using hcc c
  have hi₀ : ty i₀ = t₀ := (hi i₀).2 rfl
  have hnot : ∀ j, ty j = ComplexEmbedding.conjugate t₀ → j ≠ i₀ := by
    rintro j hj rfl
    exact hc (by rw [← hj, hi₀])
  constructor
  · intro S S' hSS
    apply Subtype.ext
    have hzero : ∀ T : Matrix (Fin g) (Fin g) ℂ, T ∈ W → ∀ i j, i ≠ i₀ → j ≠ i₀ → T i j = 0 := by
      intro T hT i j hi' hj'
      by_contra hne
      rcases hij i j (hpat T hT i j hne) with h | h
      · exact hi' h
      · exact hj' h
    have hrow : ∀ j, S.1 i₀ j = S'.1 i₀ j := by
      intro j
      by_cases hj : ty j = ComplexEmbedding.conjugate t₀
      · exact congrFun hSS ⟨j, hj⟩
      · have hz : ∀ T : Matrix (Fin g) (Fin g) ℂ, T ∈ W → T i₀ j = 0 := by
          intro T hT
          by_contra hne
          exact hj (by rw [hpat T hT i₀ j hne, hi₀])
        rw [hz _ S.2, hz _ S'.2]
    have hsym : ∀ T : Matrix (Fin g) (Fin g) ℂ, T ∈ W → ∀ i j, T i j = T j i := by
      intro T hT i j
      have h := congrFun (congrFun ((hW T).1 hT).1 i) j
      rw [Matrix.transpose_apply] at h
      exact h.symm
    ext i j
    by_cases h1 : i = i₀
    · subst h1; exact hrow j
    · by_cases h2 : j = i₀
      · subst h2
        rw [hsym _ S.2, hsym _ S'.2]; exact hrow i
      · rw [hzero _ S.2 i j h1 h2, hzero _ S'.2 i j h1 h2]
  · intro v
    let T : Matrix (Fin g) (Fin g) ℂ := fun i j =>
      if h : i = i₀ ∧ ty j = ComplexEmbedding.conjugate t₀ then v ⟨j, h.2⟩
      else if h' : j = i₀ ∧ ty i = ComplexEmbedding.conjugate t₀ then v ⟨i, h'.2⟩ else 0
    have hT : T ∈ W := by
      refine (hW T).2 ⟨?_, ?_⟩
      · ext i j
        show T j i = T i j
        by_cases h1 : i = i₀ ∧ ty j = ComplexEmbedding.conjugate t₀
        · have h2 : ¬ (j = i₀ ∧ ty i = ComplexEmbedding.conjugate t₀) := fun h => hnot j h1.2 h.1
          simp only [T, dif_pos h1, dif_neg h2]
        · by_cases h2 : j = i₀ ∧ ty i = ComplexEmbedding.conjugate t₀
          · simp only [T, dif_pos h2, dif_neg h1]
          · simp only [T, dif_neg h1, dif_neg h2]
      · intro c i j
        by_cases h1 : i = i₀ ∧ ty j = ComplexEmbedding.conjugate t₀
        · simp only [T, dif_pos h1]
          have e : ty j (c : F) = (starRingEnd ℂ) (ty i (c : F)) := by
            rw [h1.2, h1.1, hi₀, ComplexEmbedding.conjugate_coe_eq]
          rw [e, mul_comm]
        · by_cases h2 : j = i₀ ∧ ty i = ComplexEmbedding.conjugate t₀
          · simp only [T, dif_neg h1, dif_pos h2]
            have e : ty j (c : F) = (starRingEnd ℂ) (ty i (c : F)) := by
              rw [h2.2, h2.1, hi₀, ComplexEmbedding.conjugate_coe_eq, Complex.conj_conj]
            rw [e, mul_comm]
          · simp only [T, dif_neg h1, dif_neg h2]
            simp
    refine ⟨⟨T, hT⟩, ?_⟩
    funext j
    show T i₀ j.1 = v j
    have h1 : i₀ = i₀ ∧ ty j.1 = ComplexEmbedding.conjugate t₀ := ⟨rfl, j.2⟩
    simp only [T, dif_pos h1]
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.PTypeCount
section
noncomputable section

open NumberField Polynomial
open scoped Matrix Classical

namespace UpperTheory.Gal.W2

private theorem emb_eq_of_coeffs {F : Type} [Field F] [NumberField F] (N m : (F →+* ℂ) → ℕ)
    (h : ∀ c : 𝓞 F, ∑ τ : F →+* ℂ, (N τ : ℂ) * τ (c : F) = ∑ τ : F →+* ℂ, (m τ : ℂ) * τ (c : F)) :
    ∀ τ, N τ = m τ := by
  let f : (F →+* ℂ) → (𝓞 F →* ℂ) := fun τ => (τ.comp (algebraMap (𝓞 F) F)).toMonoidHom
  have hf : Function.Injective f := by
    intro σ τ hστ
    apply IsLocalization.ringHom_ext (nonZeroDivisors (𝓞 F))
    ext c
    exact DFunLike.congr_fun hστ c
  have hli := (linearIndependent_monoidHom (𝓞 F) ℂ).comp f hf
  rw [Fintype.linearIndependent_iff] at hli
  have key := hli (fun τ => (N τ : ℂ) - m τ) (by
    funext c
    have hc := h c
    simp only [Finset.sum_apply, Pi.smul_apply, Function.comp_apply, smul_eq_mul, Pi.zero_apply]
    simp only [f, MonoidHom.coe_coe, RingHom.toMonoidHom_eq_coe, RingHom.coe_comp, Function.comp_apply, sub_mul, Finset.sum_sub_distrib]
    rw [sub_eq_zero]
    exact hc)
  intro τ
  have := key τ
  rw [sub_eq_zero] at this
  exact_mod_cast this

theorem typeCount_of : TypeCount := by
  intro F _ _ O _ bar g ρ a n t₀ ε hS H Sb ty ev hD
  obtain ⟨hdet, hρ, -⟩ := hD
  have hU : IsUnit Sb.det := isUnit_iff_ne_zero.mpr hdet
  have htr : ∀ c : 𝓞 F, (ρ (a c)).trace
      = ∑ τ : F →+* ℂ, ((Finset.univ.filter (fun i => ty i = τ)).card : ℂ) * τ (c : F) := by
    intro c
    have e1 : ρ (a c) = Sb * Matrix.diagonal (fun i => (ty i) (c : F)) * Sb⁻¹ := by
      rw [← hρ c, Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hU, Matrix.mul_one]
    rw [e1, Matrix.trace_mul_comm, ← Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hU,
      Matrix.one_mul, Matrix.trace_diagonal]
    rw [← Finset.sum_fiberwise Finset.univ ty (fun i => (ty i) (c : F))]
    refine Finset.sum_congr rfl (fun τ _ => ?_)
    rw [Finset.sum_congr rfl (g := fun _ => τ (c : F)) (fun i hi => by
      rw [(Finset.mem_filter.mp hi).2]), Finset.sum_const, nsmul_eq_mul]
  have hcount : ∀ τ, (Finset.univ.filter (fun i => ty i = τ)).card = typeMult n t₀ ε τ := by
    refine emb_eq_of_coeffs _ _ (fun c => ?_)
    rw [← htr c, hS.tr c]
  have hcard : ∀ τ, (evAt ty ev τ).card = typeMult n t₀ ε τ := by
    intro τ
    rw [← hcount τ, evAt, Multiset.card_map]
    rfl
  have hconj : ∀ τ : F →+* ℂ, ComplexEmbedding.conjugate (ComplexEmbedding.conjugate τ) = τ :=
    fun τ => star_star τ
  intro τ
  refine ⟨hcard τ, ?_⟩
  rw [evFull, Multiset.card_add, Multiset.card_map, hcard, hcard]
  have hpos := hS.pos
  by_cases h0 : τ = t₀
  · subst h0
    have hne : ComplexEmbedding.conjugate τ ≠ τ := hS.cx τ
    simp only [typeMult, if_true, if_neg hne]
    omega
  · by_cases h1 : τ = ComplexEmbedding.conjugate t₀
    · subst h1
      rw [hconj]
      simp only [typeMult, if_neg h0, if_true]
      omega
    · have h2 : ComplexEmbedding.conjugate τ ≠ t₀ := by
        intro e; apply h1; rw [← e, hconj]
      have h3 : ComplexEmbedding.conjugate τ ≠ ComplexEmbedding.conjugate t₀ := by
        intro e; apply h0; rw [← hconj τ, e, hconj]
      simp only [typeMult, if_neg h0, if_neg h1, if_neg h2, if_neg h3]
      rw [← Nat.mul_add, hS.eps τ h0 h1, Nat.mul_one]

end UpperTheory.Gal.W2
end
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.ProdTy
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.PELU Filter Topology
open scoped Matrix
open GlobalTheory.HodgeCoh GlobalTheory.CechDR Polynomial UpperTheory.Gal.W2

open scoped Classical in
private theorem prod_ty {F : Type} [Field F] {g : ℕ} [Fintype (F →+* ℂ)]
    (ty : Fin g → (F →+* ℂ)) (ev : Fin g → ℂ)
    (f : (F →+* ℂ) → ℂ → ℂ) :
    ∏ i, f (ty i) (ev i) = ∏ τ, ((evAt ty ev τ).map (f τ)).prod := by
  unfold evAt
  simp only [Multiset.map_map, Function.comp_def]
  rw [← Finset.prod_fiberwise Finset.univ ty (fun i => f (ty i) (ev i))]
  refine Finset.prod_congr rfl fun τ _ => ?_
  rw [Finset.prod_eq_multiset_prod]
  congr 1
  refine Multiset.map_congr rfl fun i hi => ?_
  simp only [Finset.mem_val, Finset.mem_filter, Finset.mem_univ, true_and] at hi
  rw [hi]

open scoped Classical in
theorem UpperTheory.Gal.W2.fibW_of :
    UpperTheory.Gal.W2.FibW := by
  intro F _ _ g n t₀ ε ty ev χ mu hcx hn heps hcard hrts hmu x y
  have invol := ComplexEmbedding.involutive_conjugate F
  obtain ⟨A, hA'⟩ : ∃ A : (F →+* ℂ) → ℂ,
      ∀ τ, A τ = ((evAt ty ev τ).map (fun r => 1 - τ x * (y * r))).prod := ⟨_, fun _ => rfl⟩
  obtain ⟨B, hB'⟩ : ∃ B : (F →+* ℂ) → ℂ, ∀ τ, B τ =
      ((evAt ty ev (ComplexEmbedding.conjugate τ)).map
        (fun r => 1 - τ x * starRingEnd ℂ r)).prod := ⟨_, fun _ => rfl⟩
  have hA : ∏ i, (1 - ty i x * (y * ev i)) = ∏ τ, A τ := by
    simp only [hA']
    exact prod_ty ty ev (fun τ r => 1 - τ x * (y * r))
  have hB : starRingEnd ℂ (∏ i, (1 - ty i x * ev i)) = ∏ τ, B τ := by
    rw [map_prod]
    simp only [map_sub, map_one, map_mul]
    rw [prod_ty ty ev (fun τ r => 1 - starRingEnd ℂ (τ x) * starRingEnd ℂ r)]
    refine (Equiv.prod_comp (invol.toPerm _) _).symm.trans
      (Finset.prod_congr rfl fun τ _ => ?_)
    simp [hB', Function.Involutive.coe_toPerm, ComplexEmbedding.conjugate_coe_eq]
  have hmem : ComplexEmbedding.conjugate t₀ ∈ Finset.univ.erase t₀ :=
    Finset.mem_erase.2 ⟨hcx t₀, Finset.mem_univ _⟩
  have key : ∏ τ, (A τ * B τ) = A t₀ * B t₀ *
      (A (ComplexEmbedding.conjugate t₀) * B (ComplexEmbedding.conjugate t₀) *
        ∏ τ ∈ (Finset.univ.erase t₀).erase (ComplexEmbedding.conjugate t₀), (A τ * B τ)) := by
    rw [Finset.mul_prod_erase _ (fun τ => A τ * B τ) hmem,
      Finset.mul_prod_erase _ (fun τ => A τ * B τ) (Finset.mem_univ t₀)]
  have hrest : ∏ τ ∈ (Finset.univ.erase t₀).erase (ComplexEmbedding.conjugate t₀), (A τ * B τ) =
      ∏ τ ∈ (Finset.univ.erase t₀).erase (ComplexEmbedding.conjugate t₀),
        ((rts χ τ).map (fun r => 1 - τ x * (y ^ ε τ * r))).prod := by
    refine Finset.prod_congr rfl fun τ hτ => ?_
    have h1 : τ ≠ ComplexEmbedding.conjugate t₀ := (Finset.mem_erase.1 hτ).1
    have h2 : τ ≠ t₀ := (Finset.mem_erase.1 (Finset.mem_erase.1 hτ).2).1
    have h3 : ComplexEmbedding.conjugate τ ≠ t₀ := fun h => h1 (by rw [← h, invol])
    have h4 : ComplexEmbedding.conjugate τ ≠ ComplexEmbedding.conjugate t₀ :=
      fun h => h2 (invol.injective h)
    have he := heps τ h2 h1
    have hc1 : (evAt ty ev τ).card = n * ε τ := by simp [hcard, typeMult, h1, h2]
    have hc2 : (evAt ty ev (ComplexEmbedding.conjugate τ)).card =
        n * ε (ComplexEmbedding.conjugate τ) := by simp [hcard, typeMult, h3, h4]
    rw [hA', hB', hrts, evFull, Multiset.map_add (f := _), Multiset.prod_add, Multiset.map_map]
    rcases (by omega : ε τ = 0 ∧ ε (ComplexEmbedding.conjugate τ) = 1 ∨
        ε τ = 1 ∧ ε (ComplexEmbedding.conjugate τ) = 0) with ⟨e1, e2⟩ | ⟨e1, e2⟩
    · rw [e1, Nat.mul_zero, Multiset.card_eq_zero] at hc1
      rw [hc1, e1]
      simp [Function.comp_def]
    · rw [e2, Nat.mul_zero, Multiset.card_eq_zero] at hc2
      rw [hc2, e1]
      simp [Function.comp_def]
  have hr0 : (rts χ t₀).erase mu = (evAt ty ev (ComplexEmbedding.conjugate t₀)).map (starRingEnd ℂ) := by
    rw [hrts, evFull, hmu, Multiset.singleton_add, Multiset.erase_cons_head]
  have hpair : A t₀ * B t₀ * (A (ComplexEmbedding.conjugate t₀) * B (ComplexEmbedding.conjugate t₀)) =
      (1 - t₀ x * (y * mu)) * (((rts χ t₀).erase mu).map (fun r => 1 - t₀ x * r)).prod *
        ((1 - starRingEnd ℂ (t₀ x) * starRingEnd ℂ mu) *
          (((rts χ t₀).erase mu).map
            (fun r => 1 - starRingEnd ℂ (t₀ x) * (y * starRingEnd ℂ r))).prod) := by
    rw [hr0, hA', hA', hB', hB', invol t₀, hmu]
    simp only [Multiset.map_map, Function.comp_def, Multiset.map_singleton, Multiset.prod_singleton,
      ComplexEmbedding.conjugate_coe_eq, Complex.conj_conj]
    ring
  rw [hA, hB, ← Finset.prod_mul_distrib, key, hrest]
  unfold fibW
  rw [← hpair]
  ring
end

