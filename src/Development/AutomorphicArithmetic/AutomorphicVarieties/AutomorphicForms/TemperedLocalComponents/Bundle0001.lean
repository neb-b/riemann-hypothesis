module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.HomologyRank.RankHomology
public import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.Bundle0031
public import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.Bundle0030
public import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.Bundle0041
public import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.Bundle0038
public import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.Bundle0039
public import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.Bundle0040
public import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.Bundle0036
public import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.Bundle0037
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PublishedTheorems.CuspSemisimpleReal
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PublishedTheorems.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0167
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.NegOneNotSqSqrtTwo

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.TemperedLocalComponents.BddArith
section
open NumberField

open CategoryTheory UpperTheory.V.Af.BA in
private theorem UpperTheory.V.Af.bddArith_cx : BddCx := by
  intro Γ I _ _ K hx ho hs
  obtain ⟨hst, D, hD⟩ := UpperTheory.adelic_rep_dimension_bounded Γ I K (ho 1) hs
  obtain ⟨h0, h1, h2⟩ := UpperTheory.exactCOf_of_exactBase UpperTheory.exactBase_integral_to_complex Γ I K hx
  obtain ⟨P, hP, he⟩ := UpperTheory.repResolution_exists Γ (fun p => PC Γ (K.Tup p)) K.d (augC Γ (K.Tup 0))
    (fun p => UpperTheory.projPerm_of_liftEquiv UpperTheory.pins_of_closed_subgroup_padic_character_inv Γ _ (hst p)) h0 h1 h2
  obtain ⟨a0, aD⟩ := UpperTheory.rep_hom_alternating_sum_eq_zero Γ I K
  obtain ⟨e, he1, he2⟩ := he K.alt (by rw [a0, Category.id_comp]) (UpperTheory.altChain_of_permSplit UpperTheory.perm_split_fin_succ Γ I K)
  refine UpperTheory.adelic_rep_bounded_of_degree_bounded Γ (fun q => ?_) ⟨D, fun q hq A => UpperTheory.ext_vanishing_of_resolution_endo Γ P e he1 q (he2 q (aD q (hD q hq))) A⟩
  obtain ⟨c, hc⟩ := UpperTheory.permutation_module_homology_rank Γ _ (ho q)
  exact ⟨c, fun A => (UpperTheory.rankCohHom_of_rankHomology UpperTheory.cohomology_rank_eq_homology_rank Γ P q _ (hP q) A).trans (hc A)⟩

open UpperTheory.V.Af.BA in
private theorem UpperTheory.V.Af.bddArith_fix : BddFix :=
  have hg : GoodRe := UpperTheory.good_real_form_of_real_part_of_real_involution UpperTheory.adelicBaseChange_realPart UpperTheory.adelic_realPart_invariant
  have ha : ActRe := UpperTheory.real_structure_action_of_real_involution UpperTheory.adelic_realPart_invariant
  have hs : SpanRe := UpperTheory.real_span_of_good_real_form UpperTheory.adelicBaseChange_realPart UpperTheory.adelic_realPart_invariant hg
  UpperTheory.bddFix_of_bounded_complex UpperTheory.V.Af.bddArith_cx hg ha hs
    (UpperTheory.orbRe_of_minimal_vector_stabilizer UpperTheory.fixedOrbits_finite_representatives UpperTheory.adelic_realPart_invariant ha hs UpperTheory.minimal_orbit_representatives UpperTheory.minimal_vector_stabilizer_property) UpperTheory.minimal_vector_stabilizer_property

theorem UpperTheory.V.Af.bddArith :
    ∀ (F : Type) [Field F] [NumberField F], (IsTotallyComplex F ∨ IsTotallyReal F) → ∀ (n : ℕ) (Γ : Subgroup (GL (Fin n) F)), Subgroup.Commensurable Γ (Matrix.GeneralLinearGroup.map (n := Fin n) (algebraMap (𝓞 F) F)).range → UpperTheory.V.Af.CohB.Bdd ↥Γ := by
  intro F _ _ hF n Γ hΓ
  have hO : UpperTheory.V.Af.CohB.Bdd (GL (Fin n) (𝓞 F)) := by
    rcases hF with hF | hF
    · exact UpperTheory.bounded_complex_of_bounded_simplicial_complex UpperTheory.V.Af.bddArith_cx F n
    · obtain ⟨L, _, _, _, i, σ, hσ, hi, hf⟩ := UpperTheory.exists_CM_integral_of_exists_CM UpperTheory.exists_CM_extension F
      exact UpperTheory.cohomology_bounded_equiv _ _ (UpperTheory.building_fixed_points_equiv _ _ i σ n hi hf) (UpperTheory.V.Af.bddArith_fix L n σ hσ)
  have hinj : Function.Injective (Matrix.GeneralLinearGroup.map (n := Fin n) (algebraMap (𝓞 F) F)) := by
    intro g k e
    refine Units.ext (Matrix.ext fun a b => ?_)
    exact RingOfIntegers.coe_injective (congrArg (fun u : GL (Fin n) F => (u : Matrix (Fin n) (Fin n) F) a b) e)
  exact UpperTheory.adelic_rep_bounded_comm_of_bounded_equiv UpperTheory.cohomology_bounded_equiv UpperTheory.adelic_rep_bounded_of_subgroup_bounded (UpperTheory.adelic_rep_bounded_over_of_sum_bound_coind_retract UpperTheory.cohomology_sum_bound UpperTheory.coind_retract_of_finite_index) _ Γ _ hΓ
    (UpperTheory.cohomology_bounded_equiv _ _ ⟨MonoidHom.ofInjective hinj⟩ hO)
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.TemperedLocalComponents.DefQuatExists
section
open NumberField GlobalTheory.CuspRep UpperTheory.V
open scoped TensorProduct Quaternion

namespace UpperTheory.V.Af.PQuat

section Alg

variable {F : Type} [Field F] (R : Type) [CommRing R] [Algebra F R] (a b : F)

private noncomputable def bc : ℍ[F,a,0,b] →ₐ[F] ℍ[R,algebraMap F R a,0,algebraMap F R b] :=
  QuaternionAlgebra.Basis.liftHom
    { i := ⟨0, 1, 0, 0⟩, j := ⟨0, 0, 1, 0⟩, k := ⟨0, 0, 0, 1⟩
      i_mul_i := by ext <;> simp [Algebra.algebraMap_eq_smul_one]
      j_mul_j := by ext <;> simp [Algebra.algebraMap_eq_smul_one]
      i_mul_j := by ext <;> simp
      j_mul_i := by ext <;> simp }

private theorem bc_basis (i : Fin 4) :
    bc R a b (QuaternionAlgebra.basisOneIJK a 0 b i) = QuaternionAlgebra.basisOneIJK _ _ _ i := by
  fin_cases i <;> ext <;> simp [bc, QuaternionAlgebra.Basis.lift, QuaternionAlgebra.basisOneIJK]

private theorem lift_bij {A : Type} [Ring A] [Algebra R A] [Algebra F A] [IsScalarTower F R A]
    (g : ℍ[R,algebraMap F R a,0,algebraMap F R b] →ₐ[R] A) (hg : Function.Bijective g) :
    Function.Bijective (Algebra.TensorProduct.lift (Algebra.ofId R A) ((g.restrictScalars F).comp (bc R a b))
      fun _ _ => Algebra.commutes _ _) := by
  let B := Algebra.TensorProduct.basis R (QuaternionAlgebra.basisOneIJK a 0 b)
  let e := B.equiv (QuaternionAlgebra.basisOneIJK (algebraMap F R a) 0 (algebraMap F R b)) (Equiv.refl _)
  have h : (Algebra.TensorProduct.lift (Algebra.ofId R A) ((g.restrictScalars F).comp (bc R a b))
      fun _ _ => Algebra.commutes _ _).toLinearMap = g.toLinearMap ∘ₗ e.toLinearMap := by
    refine B.ext fun i => ?_
    simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, e, Module.Basis.equiv_apply, Equiv.refl_apply]
    simp only [B, Algebra.TensorProduct.basis_apply, AlgHom.toLinearMap_apply]
    refine (Algebra.TensorProduct.lift_tmul _ _ _ _ _).trans ?_
    rw [map_one, one_mul, ← bc_basis]
    rfl
  have h2 := hg.comp e.bijective
  convert h2 using 1
  funext x
  exact LinearMap.congr_fun h x


variable {R} in
private noncomputable def spl {c d : R} (p q : R) (hc : c = -1) (hd : d = p ^ 2 + q ^ 2) :
    ℍ[R,c,0,d] →ₐ[R] Matrix (Fin 2) (Fin 2) R :=
  QuaternionAlgebra.Basis.liftHom
    { i := !![0, -1; 1, 0], j := !![p, q; q, -p], k := !![-q, p; p, q]
      i_mul_i := by ext i j; fin_cases i <;> fin_cases j <;> simp [hc]
      j_mul_j := by ext i j; fin_cases i <;> fin_cases j <;> simp [hd] <;> ring
      i_mul_j := by ext i j; fin_cases i <;> fin_cases j <;> simp
      j_mul_i := by ext i j; fin_cases i <;> fin_cases j <;> simp }

variable {R} in
private theorem spl_apply {c d : R} (p q : R) (hc : c = -1) (hd : d = p ^ 2 + q ^ 2) (x : ℍ[R,c,0,d]) :
    spl p q hc hd x = !![x.re + x.imJ * p - x.imK * q, -x.imI + x.imJ * q + x.imK * p;
      x.imI + x.imJ * q + x.imK * p, x.re - x.imJ * p + x.imK * q] := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [spl, QuaternionAlgebra.Basis.lift, Matrix.algebraMap_matrix_apply] <;> ring

variable {R} in
private theorem spl_bij {c d : R} (p q : R) (hc : c = -1) (hd : d = p ^ 2 + q ^ 2) (u : R) (hu : u * (2 * d) = 1) :
    Function.Bijective (spl p q hc hd) := by
  rw [hd] at hu
  constructor
  · rw [injective_iff_map_eq_zero]
    intro x hx
    rw [spl_apply] at hx
    have h00 := congrFun (congrFun hx 0) 0
    have h01 := congrFun (congrFun hx 0) 1
    have h10 := congrFun (congrFun hx 1) 0
    have h11 := congrFun (congrFun hx 1) 1
    simp at h00 h01 h10 h11
    ext
    · simp
      linear_combination u * (p ^ 2 + q ^ 2) * (h00 + h11) - x.re * hu
    · simp
      linear_combination u * (p ^ 2 + q ^ 2) * (h10 - h01) - x.imI * hu
    · simp
      linear_combination u * (p * (h00 - h11) + q * (h10 + h01)) - x.imJ * hu
    · simp
      linear_combination u * (-q * (h00 - h11) + p * (h10 + h01)) - x.imK * hu
  · intro m
    refine ⟨⟨u * (p ^ 2 + q ^ 2) * (m 0 0 + m 1 1), u * (p ^ 2 + q ^ 2) * (m 1 0 - m 0 1),
      u * (p * (m 0 0 - m 1 1) + q * (m 1 0 + m 0 1)), u * (-q * (m 0 0 - m 1 1) + p * (m 1 0 + m 0 1))⟩, ?_⟩
    rw [spl_apply]
    ext i j
    fin_cases i <;> fin_cases j <;> simp
    · linear_combination m 0 0 * hu
    · linear_combination m 0 1 * hu
    · linear_combination m 1 0 * hu
    · linear_combination m 1 1 * hu

private theorem isUnit_of_neg (τ : F →+* ℝ) (ha : τ a < 0) (hb : τ b < 0) (x : ℍ[F,a,0,b]) (hx : x ≠ 0) : IsUnit x := by
  set n : F := x.re ^ 2 - a * x.imI ^ 2 - b * x.imJ ^ 2 + a * b * x.imK ^ 2 with hn
  have hn0 : n ≠ 0 := by
    intro h
    have h1 := congrArg τ h
    simp only [hn, map_add (f := _), map_sub, map_mul, map_pow, map_zero] at h1
    have p1 := sq_nonneg (τ x.re)
    have p2 := mul_nonneg (neg_pos.2 ha).le (sq_nonneg (τ x.imI))
    have p3 := mul_nonneg (neg_pos.2 hb).le (sq_nonneg (τ x.imJ))
    have p4 := mul_nonneg (mul_pos_of_neg_of_neg ha hb).le (sq_nonneg (τ x.imK))
    have q1 : τ x.re ^ 2 = 0 := by linarith
    have q2 : -τ a * τ x.imI ^ 2 = 0 := by linarith
    have q3 : -τ b * τ x.imJ ^ 2 = 0 := by linarith
    have q4 : τ a * τ b * τ x.imK ^ 2 = 0 := by linarith
    simp [ha.ne, hb.ne] at q1 q2 q3 q4
    apply hx
    ext <;> simp [*]
  have e1 : x * (n⁻¹ • star x) = 1 := by
    ext
    · simp
      field_simp
      simp only [hn]
      ring
    all_goals
      simp [hn0]
      ring
  have e2 : (n⁻¹ • star x) * x = 1 := by
    ext
    · simp
      field_simp
      simp only [hn]
      ring
    all_goals
      simp [hn0]
      ring
  exact ⟨⟨x, _, e1, e2⟩, rfl⟩

private theorem central [CharZero F] (ha : a ≠ 0) (hb : b ≠ 0) : Algebra.IsCentral F ℍ[F,a,0,b] := by
  refine ⟨fun x hx => ?_⟩
  rw [Subalgebra.mem_center_iff] at hx
  have h1 := hx ⟨0, 1, 0, 0⟩
  have h2 := hx ⟨0, 0, 1, 0⟩
  simp [QuaternionAlgebra.ext_iff] at h1 h2
  refine Algebra.mem_bot.2 ⟨x.re, ?_⟩
  ext <;> simp <;> grind

private theorem definite (τ : F →+* ℝ) (ha : τ a < 0) (hb : τ b < 0) :
    letI := τ.toAlgebra; NoZeroDivisors (ℝ ⊗[F] ℍ[F,a,0,b]) := by
  letI := τ.toAlgebra
  have h := (lift_bij ℝ a b (AlgHom.id _ _) Function.bijective_id).1
  haveI : NoZeroDivisors ℍ[ℝ,algebraMap F ℝ a,0,algebraMap F ℝ b] := ⟨fun {x y} hxy => by
    by_cases hx : x = 0
    · exact Or.inl hx
    · exact Or.inr ((isUnit_of_neg _ _ (RingHom.id ℝ) ha hb x hx).mul_right_eq_zero.1 hxy)⟩
  exact h.noZeroDivisors _ (map_zero _) (map_mul _)

end Alg

open GlobalTheory.QuadSymbol GlobalTheory.IdeleNormChar in
private theorem arith (F : Type) [Field F] [NumberField F] [IsTotallyReal F] (h : Even (Module.finrank ℚ F)) :
    ∃ b : F, (∀ τ : F →+* ℝ, τ b < 0) ∧ ∃ p q : Af F, algebraMap F (Af F) b = p ^ 2 + q ^ 2 := by
  obtain ⟨w₀⟩ : Nonempty (InfinitePlace F) := inferInstance
  haveI : Fact (∀ r : F, r ^ 2 ≠ -1 + 0 * r) := ⟨fun r hr => by
    have := congrArg (InfinitePlace.embedding_of_isReal (IsTotallyReal.isReal w₀)) hr
    simp only [map_pow, zero_mul, add_zero, map_neg, map_one] at this
    nlinarith [sq_nonneg (InfinitePlace.embedding_of_isReal (IsTotallyReal.isReal w₀) r)]⟩
  haveI := Model.isQuadratic (-1 : F)
  haveI := Model.numberField (-1 : F)
  let a₀ : AdeleRing (𝓞 F) F := ((-1 : InfiniteAdeleRing F), (1 : Af F))
  have ha₀ : a₀ * a₀ = 1 := Prod.ext (neg_one_mul (-1 : InfiniteAdeleRing F) |>.trans (neg_neg 1)) (one_mul (1 : Af F))
  let a : (AdeleRing (𝓞 F) F)ˣ := ⟨a₀, a₀, ha₀, ha₀⟩
  have hf : finComp a = 1 := funext fun _ => Units.ext rfl
  have hi : infComp a = infDiag F (-1) := funext fun w => Units.ext (by
    change (-1 : w.Completion) = _
    simp [infDiag, GlobalTheory.QuadSymbol.toUnits])
  have hs : normSign (QuadraticAlgebra F (-1) 0) a = 1 := by
    change etaProd F _ (finComp a) (infComp a) = 1
    have h1 : ∀ (A : Type) [CommRing A] [Algebra F A], eta F (QuadraticAlgebra F (-1) 0) A 1 = 1 :=
      fun A _ _ => eta_eq_one_iff.2 (one_mem _)
    rw [hf, hi, etaProd, Finset.prod_congr rfl fun w _ => Model.eta_real_place w (IsTotallyReal.isReal w)]
    simp only [Pi.one_apply, h1, finprod_one, one_mul, Finset.prod_const, Finset.card_univ]
    refine Even.neg_one_pow ?_
    rwa [InfinitePlace.card_eq_nrRealPlaces_add_nrComplexPlaces, IsTotallyReal.nrComplexPlaces_eq_zero, add_zero,
      ← IsTotallyReal.finrank]
  obtain ⟨t, ht⟩ := (normSign_eq_one_iff _ a).1 hs
  obtain ⟨x, y, e⟩ := (Model.mem_normGroup_sqrt (-1 : F)).1 ht
  rw [div_eq_mul_inv, ← map_inv, map_neg, map_one, neg_one_mul, sub_neg_eq_add] at e
  replace e : a₀ * algebraMap F (AdeleRing (𝓞 F) F) (t⁻¹ : Fˣ) = x ^ 2 + y ^ 2 := e
  refine ⟨(t⁻¹ : Fˣ), fun τ => ?_, x.2, y.2, (one_mul _).symm.trans (congrArg Prod.snd e)⟩
  let w := InfinitePlace.mk (Complex.ofRealHom.comp τ)
  have hw : w.IsReal := IsTotallyReal.isReal w
  have e1 : (-1 : w.Completion) * algebraMap F w.Completion (t⁻¹ : Fˣ) = x.1 w ^ 2 + y.1 w ^ 2 :=
    congrArg (fun z : AdeleRing (𝓞 F) F => z.1 w) e
  have e2 := congrArg (InfinitePlace.Completion.extensionEmbeddingOfIsReal hw) e1
  have e3 : InfinitePlace.Completion.extensionEmbeddingOfIsReal hw (algebraMap F w.Completion (t⁻¹ : Fˣ)) = τ (t⁻¹ : Fˣ) := by
    have hr : ComplexEmbedding.IsReal (Complex.ofRealHom.comp τ) := by
      rw [ComplexEmbedding.isReal_iff]; ext z; simp
    rw [AbsoluteValue.Completion.algebraMap_def, InfinitePlace.Completion.extensionEmbeddingOfIsReal_coe]
    refine Complex.ofReal_injective ?_
    rw [InfinitePlace.embedding_of_isReal_apply, InfinitePlace.embedding_mk_eq_of_isReal hr]
    rfl
  simp only [map_mul, map_neg, map_one, map_add (f := _), map_pow, e3] at e2
  refine lt_of_le_of_ne ?_ ((map_ne_zero τ).2 (Units.ne_zero _))
  nlinarith [sq_nonneg (InfinitePlace.Completion.extensionEmbeddingOfIsReal hw (x.1 w)),
    sq_nonneg (InfinitePlace.Completion.extensionEmbeddingOfIsReal hw (y.1 w))]

end UpperTheory.V.Af.PQuat

open UpperTheory.V.Af.PQuat in
theorem UpperTheory.V.Af.defQuatExists :
    UpperTheory.V.Published.DefQuatExists := by
  intro F _ _ _ h
  obtain ⟨b, hb, p, q, hpq⟩ := arith F h
  obtain ⟨w⟩ : Nonempty (InfinitePlace F) := inferInstance
  let τ : F →+* ℝ := InfinitePlace.embedding_of_isReal (IsTotallyReal.isReal w)
  have hb0 : b ≠ 0 := fun e => by simpa [e] using hb τ
  have hm : ∀ σ : F →+* ℝ, σ (-1) < 0 := fun σ => by simp
  letI : DivisionRing ℍ[F,-1,0,b] := DivisionRing.ofIsUnitOrEqZero fun x =>
    (em (x = 0)).symm.imp_left (isUnit_of_neg _ _ τ (hm τ) (hb τ) x)
  have hc : ∀ v : InfinitePlace F, ∃ j : ℍ[F,-1,0,b] →+* Matrix (Fin 2) (Fin 2) ℂ,
      ∀ x, j (algebraMap F _ x) = algebraMap ℂ _ (v.embedding x) := fun v => by
    letI := v.embedding.toAlgebra
    obtain ⟨s, hs⟩ := IsAlgClosed.exists_pow_nat_eq (algebraMap F ℂ b) two_pos
    let g := ((spl s 0 (c := algebraMap F ℂ (-1)) (d := algebraMap F ℂ b) (by simp) (by simp [hs])).restrictScalars F).comp
      (bc ℂ (-1) b)
    exact ⟨g.toRingHom, fun x => (g.commutes x).trans (IsScalarTower.algebraMap_apply F ℂ _ x)⟩
  choose jc hjc using hc
  exact ⟨{
    D := ℍ[F,-1,0,b]
    central := central _ _ (by simp) hb0
    rank := QuaternionAlgebra.finrank_eq_four _ _ _
    definite := fun σ => definite _ _ σ (hm σ) (hb σ)
    jf := ((spl p q (by simp) hpq).restrictScalars F).comp (bc (Af F) (-1) b)
    jf_bij := lift_bij _ _ _ _ (spl_bij p q _ hpq (algebraMap F _ (2 * b)⁻¹) (by
      rw [← map_ofNat (algebraMap F (Af F)) 2, ← map_mul, ← map_mul, inv_mul_cancel₀ (by simp [hb0]), map_one]))
    jc := jc
    jc_alg := hjc }⟩
end

