module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.NearSplit
public import Development.AutomorphicArithmetic.AutomorphicVarieties.SymplecticGSp4.EntryMem
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PublishedTheorems.FerreroWashington
public import Development.AutomorphicArithmetic.AutomorphicVarieties.HeightAndVanishing.Bundle0001
public import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.ExistsValuationExtensionIntegral
public import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.Bundle0001
public import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.Bundle0002
public import Development.AutomorphicArithmetic.AutomorphicVarieties.SymplecticGSp4.Bundle0006

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.CompactIntegralFields.AlLoc
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual Formalism.HC ReciprocityTheory.Gal IsLocalRing Polynomial UpperTheory.V.Base UpperTheory.V.Alg UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws

private theorem al_loc {l : ℕ} [Fact l.Prime] (c : Coef l) {B : Type} [CommRing B] [IsDomain B] [CharP B l] (g : c.O →+* B) :
    IsLocalHom g := by
  have hl : (l : c.O) ≠ 0 := Nat.cast_ne_zero.2 (Fact.out : l.Prime).ne_zero
  have hk : RingHom.ker g ≠ ⊥ := fun h => hl (by
    have : (l : c.O) ∈ RingHom.ker g := by rw [RingHom.mem_ker, map_natCast, CharP.cast_eq_zero]
    rwa [h, Ideal.mem_bot] at this)
  have hm : RingHom.ker g = maximalIdeal c.O := eq_maximalIdeal ((RingHom.ker_isPrime g).isMaximal hk)
  refine ⟨fun x hx => by_contra fun h => hx.ne_zero ?_⟩
  have : x ∈ RingHom.ker g := hm ▸ (mem_maximalIdeal x).2 h
  exact this

private theorem al_le {l : ℕ} [Fact l.Prime] (c : Coef l) : c.O ≤ integralClosure ℤ_[l] (PadicAlgCl l) := fun x hx =>
  (Algebra.IsIntegral.isIntegral (R := ℤ_[l]) (⟨x, hx⟩ : c.O)).map c.O.val

theorem UpperTheory.V.Ws.ambL :
    ∀ {l : ℕ} [Fact l.Prime] (c : Coef l) (A : Type) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A] [IsAdicComplete (maximalIdeal A) A]
      [Finite (ResidueField A)] [CharP A l] (a : c.O →+* A), ∃ (𝔞 : Amb l) (f : A →+* 𝔞.V), CharP 𝔞.K l ∧ 𝔞.IsDvr f ∧ f.comp a = 𝔞.a c := by
  intro l _ c A _ _ _ _ _ _ a
  haveI := c.dvr
  haveI := c.fin
  let K := AlgebraicClosure (FractionRing A)
  let g0 : A →+* K := (algebraMap (FractionRing A) K).comp (algebraMap A (FractionRing A))
  have hg0 : Function.Injective g0 :=
    (algebraMap (FractionRing A) K).injective.comp (IsFractionRing.injective A (FractionRing A))
  obtain ⟨V, hV, hloc⟩ := IsLocalRing.exists_factor_valuationRing g0
  let f : A →+* V := g0.codRestrict V hV
  have hfinj : Function.Injective f := fun x y h => hg0 (congrArg Subtype.val h)
  have hfloc : IsLocalHom f := hloc
  haveI hK : CharP K l := charP_of_injective_ringHom hg0 l
  haveI : CharP V l := charP_of_injective_ringHom hfinj l
  have heq : V.subtype.comp f = g0 := RingHom.ext fun _ => rfl
  have halg : ∀ z : K, ∃ p : A[X], p ≠ 0 ∧ eval₂ (V.subtype.comp f) z p = 0 := by
    intro z
    obtain ⟨q, hq0, hq⟩ := Algebra.IsAlgebraic.isAlgebraic (R := FractionRing A) z
    refine ⟨IsLocalization.integerNormalization (nonZeroDivisors A) q, ?_, ?_⟩
    · rwa [Ne, IsFractionRing.integerNormalization_eq_zero_iff]
    · rw [Polynomial.aeval_def] at hq
      rw [heq]
      exact IsLocalization.integerNormalization_eval₂_eq_zero (nonZeroDivisors A)
        (algebraMap (FractionRing A) K) q hq
  let S := integralClosure c.O (PadicAlgCl l)
  have hinj : Function.Injective (algebraMap c.O S) := by
    intro x y h
    apply Subtype.ext
    have h2 := congrArg Subtype.val h
    exact h2
  obtain ⟨Φ, hΦ⟩ := UpperTheory.exists_valuation_extension_integral c.O S K V hinj (f.comp a)
  have hS : ∀ c' : Coef l, ∀ x : c'.O, (x : PadicAlgCl l) ∈ S := fun c' x =>
    IsIntegral.tower_top (A := c.O) (al_le c' x.2)
  let ι : ∀ c' : Coef l, c'.O →+* S := fun c' => c'.O.val.toRingHom.codRestrict S (hS c')
  refine ⟨Amb.mk K V (fun c' => Φ.comp (ι c')) ?_ ?_ ?_, f, hK, ⟨hfinj, hfloc, inferInstance, inferInstance, halg⟩, ?_⟩
  · intro c1 c2 h x
    exact congrArg Φ (Subtype.ext rfl)
  · intro c'
    exact al_loc c' _
  · intro x
    obtain ⟨p, hp0, hp⟩ := halg x
    have hint := UpperTheory.residue_isIntegral_of_algebraic_over_dvr A K V f hfinj hfloc x ⟨p, hp0, hp⟩
    obtain ⟨y, hy⟩ := UpperTheory.exists_integralClosure_preimage_of_isIntegral c.O (PadicAlgCl l) (ResidueField V)
      ((IsLocalRing.residue V).comp Φ) (IsLocalRing.residue V x) hint
    have hyl : IsIntegral ℤ_[l] (y : PadicAlgCl l) := isIntegral_trans (A := c.O) _ y.2
    obtain ⟨c', -, hc'⟩ := (coefSup l).2.2.1 c y.1 hyl
    refine ⟨c', ⟨y.1, hc'⟩, ?_⟩
    rw [← IsLocalRing.residue_eq_zero_iff, map_sub, sub_eq_zero, ← hy]
    rfl
  · exact hΦ.symm.trans (congrArg Φ.comp (RingHom.ext fun x => Subtype.ext rfl))
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.CompactIntegralFields.AmbZero
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual Formalism.HC ReciprocityTheory.Gal IsLocalRing Polynomial UpperTheory.V.Base UpperTheory.V.Alg UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws

private theorem az_intIff {l : ℕ} [Fact l.Prime] (x : PadicAlgCl l) : IsIntegral ℤ_[l] x ↔ ‖x‖ ≤ 1 := by
  have hi : IsIntegral ℚ_[l] x := Algebra.IsIntegral.isIntegral x
  have h0 : ‖x‖ = spectralValue (minpoly ℚ_[l] x) := rfl
  rw [h0, spectralValue_le_one_iff (minpoly.monic hi)]
  constructor
  · intro h n
    rw [minpoly.isIntegrallyClosed_eq_field_fractions' ℚ_[l] h, coeff_map]
    exact PadicInt.norm_le_one _
  · intro h
    have hl' : minpoly ℚ_[l] x ∈ lifts (algebraMap ℤ_[l] ℚ_[l]) :=
      (lifts_iff_coeff_lifts _).mpr fun n => ⟨⟨_, h n⟩, rfl⟩
    obtain ⟨q, hq, -, hqm⟩ := lifts_and_degree_eq_and_monic hl' (minpoly.monic hi)
    exact ⟨q, hqm, by rw [← aeval_def, ← aeval_map_algebraMap ℚ_[l], hq, minpoly.aeval]⟩

open Cardinal in
private theorem az_card (l : ℕ) [Fact l.Prime] : #(PadicAlgCl l) = 𝔠 := by
  have h1 : #ℚ_[l] ≤ #(CauSeq ℚ (padicNorm l)) :=
    mk_le_of_surjective (f := (Quotient.mk'' : CauSeq ℚ (padicNorm l) → ℚ_[l])) Quotient.mk''_surjective
  have h2 : #(CauSeq ℚ (padicNorm l)) ≤ #(ℕ → ℚ) := mk_subtype_le _
  have h3 : #(ℕ → ℚ) = 𝔠 := by simp
  apply le_antisymm
  · refine (Algebra.IsAlgebraic.cardinalMk_le_max ℚ_[l] (PadicAlgCl l)).trans ?_
    exact max_le (h1.trans (h2.trans h3.le)) aleph0_le_continuum
  · have h : 𝔠 ≤ #ℚ_[l] := continuum_le_cardinal_of_nontriviallyNormedField ℚ_[l]
    exact h.trans (mk_le_of_injective (algebraMap ℚ_[l] (PadicAlgCl l)).injective)

private noncomputable def azV (l : ℕ) [Fact l.Prime] : ValuationSubring (PadicAlgCl l) :=
  (NormedField.valuation : Valuation (PadicAlgCl l) NNReal).valuationSubring

private theorem mem_azV {l : ℕ} [Fact l.Prime] (x : PadicAlgCl l) : x ∈ azV l ↔ ‖x‖ ≤ 1 := by
  show ‖x‖₊ ≤ 1 ↔ _
  exact_mod_cast Iff.rfl

private noncomputable def azA {l : ℕ} [Fact l.Prime] (c : Coef l) : c.O →+* azV l :=
  (c.O.val : c.O →+* PadicAlgCl l).codRestrict (azV l) fun x =>
    (mem_azV _).2 ((az_intIff _).1 ((Algebra.IsIntegral.isIntegral (R := ℤ_[l]) x).map c.O.val))

private theorem azA_loc {l : ℕ} [Fact l.Prime] (c : Coef l) : IsLocalHom (azA c) := by
  refine ⟨fun x hx => ?_⟩
  obtain ⟨y, hy⟩ := hx.exists_left_inv
  have hy' : (y : PadicAlgCl l) * (x : PadicAlgCl l) = 1 := congrArg Subtype.val hy
  have h0 : (x : PadicAlgCl l) ≠ 0 := right_ne_zero_of_mul_eq_one hy'
  have hm : (y : PadicAlgCl l) ∈ c.O :=
    (coefSup l).2.2.2 c y ((az_intIff _).2 ((mem_azV _).1 y.2)) ⟨1, x, h0, hy'⟩
  exact IsUnit.of_mul_eq_one_right (⟨y, hm⟩ : c.O) (Subtype.ext hy')

theorem UpperTheory.V.Ws.ambZero :
    ∀ (l : ℕ) [Fact l.Prime], (∃ (𝔞 : Amb l) (e : 𝔞.K ≃+* PadicAlgCl l), 𝔞.IsZero e) ∧ Nonempty (PadicAlgCl l ≃+* ℂ) := by
  intro l hl
  refine ⟨⟨{ K := PadicAlgCl l, V := azV l, a := azA, compat := fun _ _ _ _ => rfl, loc := azA_loc, alg := fun x => ?_ },
    RingEquiv.refl _, fun _ _ => rfl, mem_azV⟩, ?_⟩
  · obtain ⟨c, -⟩ := (coefSup l).2.1 1 (by rw [Nat.dvd_one]; exact hl.out.ne_one)
    obtain ⟨c', -, hx⟩ := (coefSup l).2.2.1 c x ((az_intIff _).2 ((mem_azV _).1 x.2))
    refine ⟨c', ⟨x, hx⟩, ?_⟩
    have : azA c' ⟨x, hx⟩ = x := rfl
    rw [this, sub_self]
    exact Ideal.zero_mem _
  · apply IsAlgClosed.ringEquiv_of_equiv_of_charZero
    · rw [az_card]; exact Cardinal.aleph0_lt_continuum
    · exact Cardinal.eq.1 (by rw [az_card, Cardinal.mk_complex])
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.CompactIntegralFields.ConTrace
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual Formalism.HC ReciprocityTheory.Gal IsLocalRing Polynomial UpperTheory.V.Base UpperTheory.V.Alg UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws

private theorem con_span {K Γ n : Type} [Field K] [Group Γ] [Fintype n] [DecidableEq n] [Nontrivial n]
    (σ : Γ → Matrix n n K) (hm : ∀ g h, σ (g * h) = σ g * σ h) (hs : Submodule.span K (Set.range σ) = ⊤)
    (P : Matrix n n K) (hP : IsUnit P)
    (ht : ∀ x g h, (P * σ (x * (g * h))).trace = (P * σ (x * (h * g))).trace) : False := by
  have h1 : ∀ g h, σ g * σ h = σ h * σ g := fun g h => by
    have h2 : ∀ M : Matrix n n K, (P * (M * (σ g * σ h))).trace = (P * (M * (σ h * σ g))).trace := fun M => by
      have hM : M ∈ Submodule.span K (Set.range σ) := hs ▸ Submodule.mem_top
      induction hM using Submodule.span_induction with
      | mem M hM => obtain ⟨x, rfl⟩ := hM; simpa only [hm] using ht x g h
      | zero => simp
      | add a b _ _ ha hb => simp only [add_mul, mul_add, Matrix.trace_add, ha, hb]
      | smul c a _ ha => simp only [smul_mul_assoc, mul_smul_comm, Matrix.trace_smul, ha]
    obtain ⟨u, rfl⟩ := hP
    ext i j
    have := h2 (((u⁻¹ : (Matrix n n K)ˣ) : Matrix n n K) * Matrix.single j i (1 : K))
    simpa only [mul_assoc, Units.mul_inv_cancel_left, Matrix.trace_single_mul, one_smul, smul_eq_mul, one_mul] using this
  have h3 : ∀ M N : Matrix n n K, M * N = N * M := fun M N => by
    have hM : M ∈ Submodule.span K (Set.range σ) := hs ▸ Submodule.mem_top
    have hN : N ∈ Submodule.span K (Set.range σ) := hs ▸ Submodule.mem_top
    induction hM, hN using Submodule.span_induction₂ with
    | mem_mem a b ha hb => obtain ⟨x, rfl⟩ := ha; obtain ⟨y, rfl⟩ := hb; exact h1 x y
    | zero_left => simp
    | zero_right => simp
    | add_left a b c _ _ _ h h' => simp only [add_mul, mul_add, h, h']
    | add_right a b c _ _ _ h h' => simp only [add_mul, mul_add, h, h']
    | smul_left r a b _ _ h => simp only [smul_mul_assoc, mul_smul_comm, h]
    | smul_right r a b _ _ h => simp only [smul_mul_assoc, mul_smul_comm, h]
  obtain ⟨i, j, hij⟩ := exists_pair_ne n
  have := congrFun (congrFun (h3 (Matrix.single i j 1) (Matrix.single j j 1)) i) j
  simp [hij, hij.symm] at this

private def con_e : Fin 2 ⊕ Fin 2 ≃ Fin 4 where
  toFun := Sum.elim ixA ixB
  invFun := ![Sum.inl 0, Sum.inr 0, Sum.inl 1, Sum.inr 1]
  left_inv := by decide
  right_inv := by decide

private theorem con_block {K Γ : Type} [Field K] [Group Γ] (r : Γ →* M4 K)
    (ht : ∀ x g h, (r (x * (g * h))).trace = (r (x * (h * g))).trace) (g0 : Γ) (hg : Squarefree (r g0).charpoly) :
    ¬ BlockExt r := by
  rintro ⟨h0, hs, -⟩
  have z : ∀ g (i j : Fin 2), r g (ixA i) (ixB j) = 0 := fun g i j => h0 g _ _ (by revert i j; decide)
  obtain ⟨A, hA⟩ : ∃ A : Γ → Matrix (Fin 2) (Fin 2) K, A = fun g => (r g).submatrix ixA ixA := ⟨_, rfl⟩
  obtain ⟨B, hB⟩ : ∃ B : Γ → Matrix (Fin 2) (Fin 2) K, B = fun g => (r g).submatrix ixB ixB := ⟨_, rfl⟩
  rw [← hB] at hs
  have fb : ∀ g, (r g).submatrix con_e con_e = Matrix.fromBlocks (A g) 0 ((r g).submatrix ixB ixA) (B g) := fun g => by
    subst hA hB
    ext (i | i) (j | j)
    · rfl
    · exact z g i j
    · rfl
    · rfl
  have mAB : ∀ g h, A (g * h) = A g * A h ∧ B (g * h) = B g * B h := fun g h => by
    have h1 := fb (g * h)
    rw [map_mul, ← Matrix.submatrix_mul_equiv _ _ _ con_e, fb, fb, Matrix.fromBlocks_multiply, Matrix.fromBlocks_inj] at h1
    obtain ⟨h2, -, -, h3⟩ := h1
    rw [Matrix.zero_mul, add_zero] at h2
    rw [Matrix.mul_zero, zero_add] at h3
    exact ⟨h2.symm, h3.symm⟩
  have mA := fun g h => (mAB g h).1
  have mB := fun g h => (mAB g h).2
  have tr : ∀ g, (r g).trace = (A g).trace + (B g).trace := fun g => by
    subst hA hB
    rw [Matrix.trace, ← Equiv.sum_comp con_e, Fintype.sum_sum_type]
    rfl
  have cp : (r g0).charpoly = (A g0).charpoly * (B g0).charpoly := by
    rw [← Matrix.charpoly_fromBlocks_zero₁₂, ← fb, ← Matrix.charpoly_reindex con_e.symm]
    rfl
  have ev : ∀ M : Matrix (Fin 2) (Fin 2) K, aeval M (A g0).charpoly = M * M - (A g0).trace • M + (A g0).det • 1 := fun M => by
    rw [Matrix.charpoly_fin_two]
    simp [Algebra.algebraMap_eq_smul_one, sq]
  have hU : IsUnit (aeval (B g0) (A g0).charpoly) := by
    rw [cp] at hg
    obtain ⟨u, v, huv⟩ := (IsRelPrime.of_squarefree_mul hg).isCoprime
    have := congrArg (aeval (B g0)) huv
    rw [map_add (f := _), map_mul, map_mul, Matrix.aeval_self_charpoly, mul_zero, add_zero, map_one] at this
    exact IsUnit.of_mul_eq_one_right _ this
  have key : ∀ y, (aeval (B g0) (A g0).charpoly * B y).trace =
      (r (g0 * g0 * y)).trace - (A g0).trace * (r (g0 * y)).trace + (A g0).det * (r y).trace := fun y => by
    have h1 : (aeval (A g0) (A g0).charpoly * A y).trace = 0 := by rw [Matrix.aeval_self_charpoly]; simp
    rw [ev] at h1 ⊢
    simp only [tr, mA, mB, add_mul, sub_mul, smul_mul_assoc, one_mul, Matrix.trace_add, Matrix.trace_sub,
      Matrix.trace_smul, smul_eq_mul] at h1 ⊢
    linear_combination -h1
  refine con_span B mB hs _ hU fun x g h => ?_
  rw [key, key, ht x, ← mul_assoc g0 x, ← mul_assoc g0 x, ht (g0 * x), ← mul_assoc _ x, ← mul_assoc _ x, ht (g0 * g0 * x)]

private theorem con_trace {K : Type} [Field K] [IsAlgClosed K] {l : ℕ} [Fact l.Prime] [CharP K l] (V : ValuationSubring K)
    (M : M4 V) (d : Fin 4 → V) (m N : ℕ) (hm : 0 < m) (hN : 0 < N) (hd : ∀ i, d i ^ m = 1)
    (hr : ∀ i, M i i - d i ∈ maximalIdeal V)
    (hc : ((M.map V.subtype) ^ N).charpoly = ∏ i, (X - C ((d i : K) ^ N))) : M.trace = ∑ i, d i := by
  haveI : CharP V l := RingHom.charP V.subtype Subtype.val_injective l
  letI : Algebra (ZMod l) V := ZMod.algebra V l
  letI : Algebra (ZMod l) K := ZMod.algebra K l
  let φ : V →ₐ[ZMod l] K := { V.subtype with commutes' := fun x => RingHom.congr_fun (RingHom.ext_zmod (V.subtype.comp (algebraMap _ _)) (algebraMap _ _)) x }
  have hdi : ∀ i, IsIntegral (ZMod l) (d i : K) := fun i => IsIntegral.of_pow hm (by
    have : (d i : K) ^ m = 1 := by exact_mod_cast congrArg Subtype.val (hd i)
    rw [this]; exact isIntegral_one)
  have h1 : IsIntegral (ZMod l) (M.map V.subtype).trace := by
    rw [Matrix.trace_eq_sum_roots_charpoly]
    refine IsIntegral.multiset_sum fun x hx => IsIntegral.of_pow hN ?_
    have h2 : x ∈ spectrum K (M.map V.subtype) :=
      Matrix.mem_spectrum_iff_isRoot_charpoly.2 (isRoot_of_mem_roots hx)
    have h3 := Matrix.mem_spectrum_iff_isRoot_charpoly.1 (spectrum.pow_mem_pow _ N h2)
    rw [hc, IsRoot.def, eval_prod, Finset.prod_eq_zero_iff] at h3
    obtain ⟨i, -, hi⟩ := h3
    rw [eval_sub, eval_X, eval_C, sub_eq_zero] at hi
    rw [hi]; exact (hdi i).pow N
  have h4 : IsIntegral (ZMod l) (M.trace - ∑ i, d i) := by
    set_option synthInstance.maxHeartbeats 100000 in
      rw [← isIntegral_algHom_iff φ Subtype.val_injective, map_sub, map_sum]
    refine IsIntegral.sub ?_ (IsIntegral.sum _ fun i _ => hdi i)
    set_option synthInstance.maxHeartbeats 100000 in
      rw [Matrix.trace, map_sum]
    exact h1
  have h5 : M.trace - ∑ i, d i ∈ maximalIdeal V := by
    rw [Matrix.trace, ← Finset.sum_sub_distrib]
    exact Ideal.sum_mem _ fun i _ => hr i
  by_contra hne
  exact h5 (h4.isUnit (sub_ne_zero.2 hne))

private theorem con_kill {l : ℕ} [Fact l.Prime] (𝔞 : Amb l) [CharP 𝔞.K l] (c : Coef l) (x y : c.O)
    (h : residue c.O x = residue c.O y) : 𝔞.a c x = 𝔞.a c y := by
  haveI : CharP 𝔞.V l := RingHom.charP 𝔞.V.subtype Subtype.val_injective l
  have h1 : RingHom.ker (𝔞.a c) ≠ ⊥ := fun h0 => by
    have h2 : (l : c.O) ∈ RingHom.ker (𝔞.a c) := by rw [RingHom.mem_ker, map_natCast, CharP.cast_eq_zero]
    rw [h0, Ideal.mem_bot] at h2
    exact (Fact.out : l.Prime).ne_zero (by exact_mod_cast h2)
  have h3 : RingHom.ker (𝔞.a c) = maximalIdeal c.O := eq_maximalIdeal ((RingHom.ker_isPrime _).isMaximal h1)
  rw [← sub_eq_zero, ← map_sub, ← RingHom.mem_ker, h3]
  exact Ideal.Quotient.eq.1 h

private theorem con_const {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {l : ℕ} [Fact l.Prime] {c : Coef l}
    {D : Raw Ω c} {ι : PadicAlgCl l ≃+* ℂ} {𝔞 : Amb l} [CharP 𝔞.K l] {r : G ℚ Ω →* M4 𝔞.V} (hp : ProMod D ι 𝔞 r) :
    ∃ T : Tower D, T.Ok ∧ ∀ g : G T.F Ω, (mapRep 𝔞.toK r (resQ T.F g)).charpoly =
      ∏ i, (X - C (𝔞.toK (𝔞.a c (chi D T.pr i (resQ T.F g))))) := by
  obtain ⟨T, c', h, Y, J, y, r₁, ⟨hok, -⟩, -, hpm, hy, -, hJ, ⟨u, hu⟩, -, hr, hψ⟩ := hp
  refine ⟨T, hok, fun g => ?_⟩
  obtain ⟨n, hn⟩ := hpm.fin
  have hy' : ∀ x, (y.comp (algebraMap Y.B Y.A)) (algebraMap c'.O Y.B x) = 𝔞.a c' x := fun x => by
    rw [RingHom.comp_apply, ← IsScalarTower.algebraMap_apply, ← hy, RingHom.comp_apply]
  have h1 : maximalIdeal Y.B ^ n ≤ RingHom.ker (y.comp (algebraMap Y.B Y.A)) := by
    refine hn.trans (sup_le (sup_le (fun b hb => hJ b hb) ?_) ?_)
    · rw [Ideal.map_le_iff_le_comap]
      intro x hx
      rw [Ideal.mem_comap, RingHom.mem_ker, hy', ← map_zero (𝔞.a c')]
      exact con_kill 𝔞 c' _ _ (by rw [map_zero, residue_eq_zero_iff]; exact hx)
    · rw [Ideal.span_le]
      rintro _ ⟨v, i, s, hs, rfl⟩
      rw [SetLike.mem_coe, RingHom.mem_ker, map_sub, map_one, RingHom.comp_apply, Y.ψ_map v i s (Ine_le_Dec _ hs),
        hψ v i s hs, sub_eq_zero, ← map_one (𝔞.a c)]
      refine con_kill 𝔞 c _ _ ?_
      have h2 := congrFun (congrFun (hok.ineL _ (T.ovl v) s hs) i) i
      rw [Matrix.one_apply_eq] at h2
      rw [map_one, ← h2]
      simp [Raw.rbar, Raw.r0, diagRep]
  have h2 : maximalIdeal Y.B ≤ RingHom.ker (y.comp (algebraMap Y.B Y.A)) :=
    (RingHom.ker_isPrime _).le_of_pow_le h1
  have h3 : RingHom.ker (res c'.O Y.B : Y.B →+* ResidueField c'.O) ≤ RingHom.ker (y.comp (algebraMap Y.B Y.A)) :=
    fun x hx => h2 ((res_eq_zero_iff c'.O Y.B x).1 hx)
  have hsurj : Function.Surjective (res c'.O Y.B : Y.B →+* ResidueField c'.O) := fun z => by
    obtain ⟨x, rfl⟩ := residue_surjective z
    exact ⟨algebraMap _ _ x, (res c'.O Y.B).commutes x⟩
  let j : ResidueField c'.O →+* 𝔞.V := RingHom.liftOfSurjective _ hsurj ⟨_, h3⟩
  have hj : j.comp (res c'.O Y.B : Y.B →+* ResidueField c'.O) = y.comp (algebraMap Y.B Y.A) :=
    RingHom.liftOfRightInverse_comp _ _ _ _
  have hj' : ∀ x, j (residue c'.O x) = 𝔞.a c' x := fun x => by
    rw [← hy', ← hj, RingHom.comp_apply]
    exact congrArg j ((res c'.O Y.B).commutes x).symm
  have h4 : (r₁ (resQ T.F g)).charpoly = ∏ i, (X - C (𝔞.a c (chi D T.pr i (resQ T.F g)))) := by
    have h5 : r₁ (resQ T.F g) = (Y.P.r g).map y := DFunLike.congr_fun hr g
    rw [h5, Matrix.charpoly_map, ← Y.cp_map, Polynomial.map_map, ← hj, ← Polynomial.map_map, Y.cp_red, Polynomial.map_prod]
    refine Finset.prod_congr rfl fun i _ => ?_
    rw [Polynomial.map_sub, map_X, map_C, hj']
    exact congrArg (fun t => X - C t) (𝔞.compat c c' h _)
  have h6 : mapRep 𝔞.toK r₁ (resQ T.F g) = (r₁ (resQ T.F g)).map 𝔞.toK := rfl
  have h7 := congrArg Matrix.charpoly (hu (resQ T.F g))
  rw [Matrix.coe_units_inv, Matrix.charpoly_units_conj, h6, Matrix.charpoly_map, h4, Polynomial.map_prod] at h7
  rw [← h7]
  simp only [Polynomial.map_sub, map_X, map_C]

theorem UpperTheory.V.Ws.con :
    ∀ {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {l : ℕ} [Fact l.Prime] {c : Coef l} (D : Raw Ω c), D.Good → ∀ (ι : PadicAlgCl l ≃+* ℂ) (𝔞 : Amb l), CharP 𝔞.K l → ∀ r u, KPair D 𝔞 r u → ProMod D ι 𝔞 r → ¬ Star (mapRep 𝔞.toK r) := by
  intro Ω _ _ _ l _ c D _ ι 𝔞 hch r u hk hp
  obtain ⟨T, hok, hc⟩ := con_const hp
  have hlab : Function.Bijective (lab T.pr) := by cases T.pr <;> decide
  haveI : Finite (ResidueField c.O) := (UpperTheory.V.abelian₂.dvr_finite l c.O).2.1
  haveI : IsGalois ℚ Ω := {}
  have htr : ∀ g, (r g).trace = ∑ i, 𝔞.a c (D.ps i g) := fun g => by
    have hi : T.F.fixingSubgroup.index ≠ 0 := by
      rw [← IntermediateField.finrank_eq_fixingSubgroup_index]
      exact Module.finrank_pos.ne'
    obtain ⟨N, hN, -, hg⟩ := Subgroup.exists_pow_mem_of_index_ne_zero hi g
    obtain ⟨g', hg'⟩ : ∃ g' : G T.F Ω, resQ T.F g' = g ^ N := ⟨T.F.fixingSubgroupEquiv ⟨_, hg⟩, rfl⟩
    refine con_trace (l := l) 𝔞.V (r g) _ (Nat.card (ResidueField c.O)ˣ) N Nat.card_pos hN (fun i => ?_) (fun i => ?_) ?_
    · rw [← map_pow, ← map_one (𝔞.a c)]
      refine con_kill 𝔞 c _ _ ?_
      have := congrArg Units.val (pow_card_eq_one' (x := Units.map (residue c.O : c.O →* ResidueField c.O) (D.ps i g)))
      rw [Units.val_pow_eq_pow_val] at this
      rw [map_pow, map_one]
      exact this
    · simpa [Raw.r0, diagRep] using hk.red g i i
    · have h1 := hc g'
      rw [hg', map_pow] at h1
      refine h1.trans ?_
      refine Eq.trans ?_ (hlab.prod_comp _)
      simp [chi]
  have ht : ∀ x g h, (mapRep 𝔞.toK r (x * (g * h))).trace = (mapRep 𝔞.toK r (x * (h * g))).trace := fun x g h => by
    have h1 : ∀ y, (mapRep 𝔞.toK r y).trace = 𝔞.toK (r y).trace := fun y => by simp [Matrix.trace]
    rw [h1, h1, htr, htr]
    simp only [map_mul, mul_comm (D.ps _ g) (D.ps _ h)]
  rintro (h | h)
  · exact con_span (mapRep 𝔞.toK r) (map_mul _) h 1 isUnit_one (by simpa only [one_mul] using ht)
  · refine con_block _ ht (resQ T.F T.g0) ?_ h
    rw [hc]
    refine (separable_prod_X_sub_C_iff.2 fun i j hij => ?_).squarefree
    by_contra hne
    have h1 : 𝔞.a c (chi D T.pr i (resQ T.F T.g0) - chi D T.pr j (resQ T.F T.g0) : c.O) = 0 := by
      rw [map_sub, sub_eq_zero]; exact Subtype.val_injective hij
    refine hok.dist i j hne (Ideal.Quotient.eq.2 fun hu => ?_)
    exact not_isUnit_zero (h1 ▸ hu.map (𝔞.a c))
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.CompactIntegralFields.IsDvrCoef
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual Formalism.HC ReciprocityTheory.Gal IsLocalRing Polynomial UpperTheory.V.Base UpperTheory.V.Alg UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws

private theorem isDvr_coef {l : ℕ} [Fact l.Prime] (𝔞 : Amb l) (e : 𝔞.K ≃+* PadicAlgCl l) (h : 𝔞.IsZero e) (c : Coef l) :
    𝔞.IsDvr (𝔞.a c) := by
  haveI : CharZero c.O := charZero_of_injective_algebraMap (dvrFacts l c.O).1
  refine ⟨fun x y hxy => Subtype.ext ?_, 𝔞.loc c, inferInstance, (UpperTheory.V.abelian₂.dvr_finite l c.O).2.1, fun x => ?_⟩
  · rw [← h.1 c x, ← h.1 c y, hxy]
  · have h1 : IsAlgebraic ℚ_[l] (e x) := Algebra.IsAlgebraic.isAlgebraic _
    have h2 : IsAlgebraic ℤ_[l] (e x) := (IsFractionRing.isAlgebraic_iff ℤ_[l] ℚ_[l] _).2 h1
    have h3 : IsAlgebraic c.O (e x) := h2.extendScalars (dvrFacts l c.O).1
    obtain ⟨p, hp, hx⟩ := h3
    refine ⟨p, hp, e.injective ?_⟩
    have h4 : (e : 𝔞.K →+* PadicAlgCl l).comp (𝔞.toK.comp (𝔞.a c)) = algebraMap c.O (PadicAlgCl l) :=
      RingHom.ext fun z => h.1 c z
    have h5 := hom_eval₂ p (𝔞.toK.comp (𝔞.a c)) (e : 𝔞.K →+* PadicAlgCl l) x
    rw [h4] at h5
    rw [map_zero]
    exact h5.trans hx

theorem UpperTheory.V.Ws.eptV :
    ∀ {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {l : ℕ} [Fact l.Prime] {c : Coef l} (D : Raw Ω c), D.Good → ∀ (𝔞 : Amb l) (e : 𝔞.K ≃+* PadicAlgCl l), 𝔞.IsZero e → ∀ r, D.EPt r → ∃ r', VPt D 𝔞 r' ∧ mapRep ((e : 𝔞.K →+* PadicAlgCl l).comp 𝔞.toK) r' = r := by
  intro Ω _ _ _ l _ c D _ 𝔞 e h r hr
  obtain ⟨R, _, _, _, ρ, y, hρ, rfl⟩ := hr
  obtain ⟨⟨c', hc', hy'⟩, a, ha1, -, hy⟩ := (coPt c R).1 y
  let y' : R →+* c'.O := (y : R →+* PadicAlgCl l).codRestrict c'.O hy'
  have hn : ∀ z : c'.O, ‖(z : PadicAlgCl l)‖ ≤ 1 := fun z => by
    rw [← h.1 c' z]
    exact (h.2 _).1 (𝔞.a c' z).2
  have hm : ∀ x ∈ maximalIdeal R, y' x ∈ maximalIdeal c'.O := by
    intro x hx hu
    obtain ⟨w, hw⟩ := hu.exists_right_inv
    have h1 : y x * (w : PadicAlgCl l) = 1 := congrArg Subtype.val hw
    have h2 : ‖y x‖ ≤ a := by simpa using hy 1 x (by rwa [pow_one])
    have h3 := congrArg norm h1
    rw [norm_mul, norm_one] at h3
    have h4 := mul_le_of_le_one_right (norm_nonneg (y x)) (hn w)
    linarith
  refine ⟨mapRep ((𝔞.a c').comp y') ρ.hom, ⟨⟨c'.O, inferInstance, inferInstance, inferInstance, 𝔞.a c',
    ⟨mapRep y' ρ.hom, fun _ => 1⟩, isDvr_coef 𝔞 e h c', fun i j N => ?_, ?_⟩,
    R, _, _, _, ρ, (𝔞.a c').comp y', hρ, RingHom.ext fun x => ?_, fun x hx => ?_, rfl⟩, ?_⟩
  · have hle : maximalIdeal R ^ N ≤ (maximalIdeal c'.O ^ N).comap y' :=
      le_trans (Ideal.pow_right_mono hm N) (Ideal.le_comap_pow _ N)
    exact (ρ.cont i j N).comp (Ideal.quotientMap _ y' hle)
  · refine PD.ext rfl (funext fun _ => ?_)
    exact Matrix.map_one _ (map_zero _) (map_one _)
  · rw [← 𝔞.compat c c' hc' x]
    exact congrArg (𝔞.a c') (Subtype.ext (y.commutes x))
  · exact map_nonunit (𝔞.a c') _ (hm x hx)
  · ext g i j
    exact h.1 c' (y' (ρ.hom g i j))
end

