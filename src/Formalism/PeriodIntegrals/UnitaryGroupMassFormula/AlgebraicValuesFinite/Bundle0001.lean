module

public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.AlgebraicValuesFinite.ClassSame

@[expose] public section

-- bundled from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.AlgebraicValuesFinite.FactorOne
section
noncomputable section

open NumberField IsDedekindDomain Formalism.L2.Host Neutral.B1

namespace PI.AlgValsFin.W

variable {L : Type} [Field L] [NumberField L]

theorem absNorm_pos (v : HeightOneSpectrum (𝓞 L)) : (0 : ℝ) < ((Ideal.absNorm v.asIdeal : ℕ) : ℝ) := by
  have h : Ideal.absNorm v.asIdeal ≠ 0 := by
    rw [Ne, Ideal.absNorm_eq_zero_iff]
    exact v.ne_bot
  exact_mod_cast Nat.pos_of_ne_zero h

theorem factor_one (N : ℝ) (hN : 0 < N) (o : ℤ) (s : ℝ) : (N ^ o) ^ s * (N ^ (-s)) ^ o = 1 := by
  have h1 : (N ^ o) ^ s = N ^ ((o : ℝ) * s) := by
    rw [← Real.rpow_intCast, ← Real.rpow_mul hN.le]
  have h2 : (N ^ (-s)) ^ o = N ^ (-s * (o : ℝ)) := by
    rw [← Real.rpow_intCast, ← Real.rpow_mul hN.le]
  have h3 : (o : ℝ) * s + -s * (o : ℝ) = 0 := by ring
  rw [h1, h2, ← Real.rpow_add hN, h3, Real.rpow_zero]

theorem keyIdOf : KeyIdOf L := by
  intro hD hL hP χ s m hχ k T hT hU
  obtain ⟨r, hr, hk⟩ := hD k T hT
  refine ⟨r, hr, ?_⟩

  have e : χ.1 (diagUnits L k) = 1 := χ.2.2 k
  rw [hk, map_mul, map_mul, map_prod] at e
  have eloc : ∀ v ∈ T, χ.1 (localIdele L v (atFin v k)) = χ.val v ^ ordF v k := by
    intro v hv
    exact hL χ v k (hU v hv)
  rw [Finset.prod_congr rfl eloc] at e
  have einf : χ.1 (infDiag k) = χ.inf k := rfl
  rw [einf] at e
  have e' := congrArg (fun u : ℂˣ => (u : ℂ)) e
  simp only [Units.val_mul, Units.coe_prod, Units.val_zpow_eq_zpow_val, Units.val_one] at e'

  have hreal : (∏ φ : L →+* ℂ, ‖φ (k : L)‖ ^ s) *
      ∏ v ∈ T, (((Ideal.absNorm v.asIdeal : ℕ) : ℝ) ^ (-s)) ^ ordF v k = 1 := by
    rw [Real.finsetProd_rpow Finset.univ (fun φ : L →+* ℂ => ‖φ (k : L)‖) (fun φ _ => norm_nonneg _) s,
      hP k T hT,
      ← Real.finsetProd_rpow T _ (fun v _ => zpow_nonneg (absNorm_pos v).le _) s,
      ← Finset.prod_mul_distrib]
    exact Finset.prod_eq_one (fun v _ => factor_one _ (absNorm_pos v) _ s)
  have hc1 : ∏ φ : L →+* ℂ, ((‖φ (k : L)‖ : ℝ) : ℂ) ^ (s : ℂ)
      = ((∏ φ : L →+* ℂ, ‖φ (k : L)‖ ^ s : ℝ) : ℂ) := by
    rw [Complex.ofReal_prod]
    refine Finset.prod_congr rfl (fun φ _ => ?_)
    rw [Complex.ofReal_cpow (norm_nonneg _)]
  have hc2 : ∏ v ∈ T, (((Ideal.absNorm v.asIdeal : ℕ) : ℂ) ^ (-(s : ℂ))) ^ ordF v k
      = ((∏ v ∈ T, (((Ideal.absNorm v.asIdeal : ℕ) : ℝ) ^ (-s)) ^ ordF v k : ℝ) : ℂ) := by
    rw [Complex.ofReal_prod]
    refine Finset.prod_congr rfl (fun v _ => ?_)
    rw [Complex.ofReal_zpow, Complex.ofReal_cpow (Nat.cast_nonneg _), Complex.ofReal_neg,
      Complex.ofReal_natCast]
  rw [← hχ k]
  simp only [Formalism.L2.Host.HChar.valTw, mul_zpow, Finset.prod_mul_distrib]
  rw [hc1, hc2]
  set A : ℝ := ∏ φ : L →+* ℂ, ‖φ (k : L)‖ ^ s with hA
  set B : ℝ := ∏ v ∈ T, (((Ideal.absNorm v.asIdeal : ℕ) : ℝ) ^ (-s)) ^ ordF v k with hB
  have hAB : (A : ℂ) * (B : ℂ) = 1 := by
    rw [← Complex.ofReal_mul, hreal, Complex.ofReal_one]
  linear_combination ((A : ℂ) * (B : ℂ)) * e' + hAB

end PI.AlgValsFin.W
end
end

-- bundled from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.AlgebraicValuesFinite.FinprodNormEmbedding
section
noncomputable section

open NumberField IsDedekindDomain Formalism.L2.Host

namespace PI.AlgValsFin.W

variable {L : Type} [Field L] [NumberField L]

theorem valuation_eq_exp (v : HeightOneSpectrum (𝓞 L)) (k : Lˣ) :
    v.valuation L (k : L) = WithZero.exp (-ordF v k) := by
  rw [ordF, neg_neg, WithZero.exp_log]
  exact (Valuation.ne_zero_iff _).mpr k.ne_zero

theorem toNNReal_exp {e : NNReal} (he : e ≠ 0) (n : ℤ) :
    WithZeroMulInt.toNNReal he (WithZero.exp n) = e ^ n := by
  first
    | (simp [WithZero.exp, WithZeroMulInt.toNNReal_pos_apply he]; done)
    | (rw [WithZeroMulInt.toNNReal_pos_apply he WithZero.exp_ne_zero]; simp [WithZero.exp]; done)
    | rfl

theorem prod_norm_emb (x : L) : ∏ φ : L →+* ℂ, ‖φ x‖ = |((Algebra.norm ℚ x : ℚ) : ℝ)| := by
  calc ∏ φ : L →+* ℂ, ‖φ x‖ = ∏ σ : L →ₐ[ℚ] ℂ, ‖σ x‖ :=
        Fintype.prod_equiv (RingHom.equivRatAlgHom L ℂ) _ _ fun _ => rfl
    _ = ‖∏ σ : L →ₐ[ℚ] ℂ, σ x‖ := (norm_prod _ _).symm
    _ = ‖algebraMap ℚ ℂ (Algebra.norm ℚ x)‖ := by rw [Algebra.norm_eq_prod_embeddings ℚ ℂ x]
    _ = |((Algebra.norm ℚ x : ℚ) : ℝ)| := by
      rw [eq_ratCast, ← Complex.ofReal_ratCast, Complex.norm_real, Real.norm_eq_abs]

theorem finprod_norm_embedding (k : Lˣ) (T : Finset (HeightOneSpectrum (𝓞 L)))
    (hT : ∀ v, v ∉ T → ordF v k = 0) :
    ∏ᶠ w : FinitePlace L, w (k : L) =
      ∏ v ∈ T, (((Ideal.absNorm v.asIdeal : ℕ) : ℝ) ^ ordF v k)⁻¹ := by
  rw [← finprod_comp_equiv FinitePlace.equivHeightOneSpectrum.symm]
  have hval : ∀ v : HeightOneSpectrum (𝓞 L),
      (FinitePlace.equivHeightOneSpectrum.symm v) (k : L) = (((Ideal.absNorm v.asIdeal : ℕ) : ℝ) ^ ordF v k)⁻¹ := by
    intro v
    have e1 : (FinitePlace.equivHeightOneSpectrum.symm v) (k : L) =
        NumberField.HeightOneSpectrum.adicAbv L v (k : L) := by
      first
        | (show (FinitePlace.mk v) (k : L) = _
           rw [FinitePlace.mk_apply, FinitePlace.norm_embedding])
        | (rw [FinitePlace.equivHeightOneSpectrum_symm_apply, FinitePlace.mk_apply, FinitePlace.norm_embedding])
        | (simp only [FinitePlace.equivHeightOneSpectrum, Equiv.coe_fn_symm_mk]
           rw [← FinitePlace.mk_apply, FinitePlace.norm_embedding])
    rw [e1, NumberField.HeightOneSpectrum.adicAbv_def, valuation_eq_exp, toNNReal_exp]
    push_cast
    rw [zpow_neg]
  rw [finprod_congr hval]
  apply finprod_eq_prod_of_mulSupport_subset
  intro v hv
  by_contra hT'
  exact hv (by simp [hT v hT'])

theorem prodNorm : ProdNorm L := by
  intro k T hT
  have h3 := FinitePlace.prod_eq_inv_abs_norm (K := L) k.ne_zero
  rw [finprod_norm_embedding k T hT, Finset.prod_inv_distrib, Rat.cast_inv, Rat.cast_abs, inv_inj] at h3
  rw [prod_norm_emb, h3]

end PI.AlgValsFin.W
end
end

-- bundled from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.AlgebraicValuesFinite.InvMemUFin
section
noncomputable section

open NumberField IsDedekindDomain IsDedekindDomain.HeightOneSpectrum WithZero Neutral.B1 Topology

namespace PI.AlgValsFin.W

variable {L : Type} [Field L] [NumberField L]

theorem locNb (v : HeightOneSpectrum (𝓞 L))
    (s : Set ((v.adicCompletionIntegers L : Set (v.adicCompletion L))))
    (hs : s ∈ 𝓝 (⟨1, (v.adicCompletionIntegers L).one_mem⟩ : (v.adicCompletionIntegers L : Set (v.adicCompletion L)))) :
    ∃ n : ℕ, ∀ y : (v.adicCompletionIntegers L : Set (v.adicCompletion L)),
      Valued.v ((y : v.adicCompletion L) - 1) ≤ exp (-(n : ℤ)) → y ∈ s := by
  rw [mem_nhds_subtype] at hs
  obtain ⟨u, hu, hsub⟩ := hs
  rw [Valued.mem_nhds] at hu
  obtain ⟨γ, hγ⟩ := hu
  obtain ⟨n, hn⟩ := exists_exp_neg_natCast_lt (MonoidWithZeroHom.ValueGroup₀.embedding_unit_ne_zero γ)
  refine ⟨n, fun y hy => hsub (hγ ?_)⟩
  show Valued.v.restrict ((y : v.adicCompletion L) - 1) < γ.1
  rw [← MonoidWithZeroHom.ValueGroup₀.embedding_strictMono.lt_iff_lt, Valuation.embedding_restrict]
  exact lt_of_le_of_lt hy hn

def toInt (x : Ideles L) (hx : x ∈ UFin L) (v : HeightOneSpectrum (𝓞 L)) :
    (v.adicCompletionIntegers L : Set (v.adicCompletion L)) :=
  ⟨(x : AdeleRing (𝓞 L) L).2 v, (mem_adicCompletionIntegers _ _ _).2 (hx.2 v).le⟩

theorem inv_mem_UFin {x : Ideles L} (hx : x ∈ UFin L) : x⁻¹ ∈ UFin L := by
  have hmul : (x : AdeleRing (𝓞 L) L) * ((x⁻¹ : Ideles L) : AdeleRing (𝓞 L) L) = 1 := x.mul_inv
  refine ⟨?_, fun v => ?_⟩
  · have h2 : (x : AdeleRing (𝓞 L) L).1 * ((x⁻¹ : Ideles L) : AdeleRing (𝓞 L) L).1 = 1 :=
      congrArg (fun y : AdeleRing (𝓞 L) L => y.1) hmul
    rw [hx.1, one_mul] at h2
    exact h2
  · have h2 : (x : AdeleRing (𝓞 L) L).2 v * ((x⁻¹ : Ideles L) : AdeleRing (𝓞 L) L).2 v = 1 :=
      congrArg (fun y : AdeleRing (𝓞 L) L => y.2 v) hmul
    have h3 := congrArg Valued.v h2
    rw [map_mul, hx.2 v, one_mul, map_one] at h3
    exact h3

theorem val_inv_sub {x : Ideles L} (hx : x ∈ UFin L) (v : HeightOneSpectrum (𝓞 L)) :
    Valued.v ((x⁻¹ : Ideles L).val.2 v - 1) = Valued.v ((x : AdeleRing (𝓞 L) L).2 v - 1) := by
  have hmul : (x : AdeleRing (𝓞 L) L) * ((x⁻¹ : Ideles L) : AdeleRing (𝓞 L) L) = 1 := x.mul_inv
  have h2 : (x : AdeleRing (𝓞 L) L).2 v * ((x⁻¹ : Ideles L) : AdeleRing (𝓞 L) L).2 v = 1 :=
    congrArg (fun y : AdeleRing (𝓞 L) L => y.2 v) hmul
  have hz : Valued.v (((x⁻¹ : Ideles L) : AdeleRing (𝓞 L) L).2 v) = 1 := (inv_mem_UFin hx).2 v
  have heq : (x⁻¹ : Ideles L).val.2 v - 1 =
      ((x⁻¹ : Ideles L) : AdeleRing (𝓞 L) L).2 v * (1 - (x : AdeleRing (𝓞 L) L).2 v) := by
    rw [mul_sub, mul_one, mul_comm (((x⁻¹ : Ideles L) : AdeleRing (𝓞 L) L).2 v), h2]
  rw [heq, map_mul, hz, one_mul, Valuation.map_sub_swap]

theorem exists_nbhd (W : Set (Ideles L)) (hW : IsOpen W) (h1 : (1 : Ideles L) ∈ W) :
    ∃ (S : Finset (HeightOneSpectrum (𝓞 L))) (n : ℕ), ∀ x ∈ UFin L,
      (∀ v ∈ S, Valued.v ((x : AdeleRing (𝓞 L) L).2 v - 1) ≤ exp (-(n : ℤ))) → x ∈ W := by
  classical
  obtain ⟨t, ht, rfl⟩ := (Units.isInducing_embedProduct).isOpen_iff.1 hW
  let one' : Π v : HeightOneSpectrum (𝓞 L), (v.adicCompletionIntegers L : Set (v.adicCompletion L)) :=
    fun v => ⟨1, (v.adicCompletionIntegers L).one_mem⟩
  let sm : (Π v : HeightOneSpectrum (𝓞 L), (v.adicCompletionIntegers L : Set (v.adicCompletion L))) →
      FiniteAdeleRing (𝓞 L) L :=
    RestrictedProduct.structureMap _ _ Filter.cofinite
  have hsm : Continuous sm := RestrictedProduct.isEmbedding_structureMap.continuous
  let g : (Π v : HeightOneSpectrum (𝓞 L), (v.adicCompletionIntegers L : Set (v.adicCompletion L))) ×
      (Π v : HeightOneSpectrum (𝓞 L), (v.adicCompletionIntegers L : Set (v.adicCompletion L))) →
      AdeleRing (𝓞 L) L × (AdeleRing (𝓞 L) L)ᵐᵒᵖ :=
    fun p => (((1 : InfiniteAdeleRing L), sm p.1), MulOpposite.op ((1 : InfiniteAdeleRing L), sm p.2))
  have hg : Continuous g :=
    Continuous.prodMk (Continuous.prodMk continuous_const (hsm.comp continuous_fst))
      (MulOpposite.continuous_op.comp (Continuous.prodMk continuous_const (hsm.comp continuous_snd)))
  have hsm1 : sm one' = 1 := FiniteAdeleRing.ext _ fun v => rfl
  have hg1 : g (one', one') = Units.embedProduct _ (1 : Ideles L) := by
    simp only [g, hsm1]
    rfl
  have hmem : g ⁻¹' t ∈ 𝓝 (one', one') :=
    hg.continuousAt.preimage_mem_nhds (ht.mem_nhds (by rw [hg1]; exact h1))
  rw [nhds_prod_eq] at hmem
  obtain ⟨t1, ht1, t2, ht2, hsub⟩ := Filter.mem_prod_iff.1 hmem
  rw [nhds_pi, Filter.mem_pi] at ht1 ht2
  obtain ⟨I1, hI1, s1, hs1, hsub1⟩ := ht1
  obtain ⟨I2, hI2, s2, hs2, hsub2⟩ := ht2
  choose n1 hn1 using fun v => locNb v (s1 v) (hs1 v)
  choose n2 hn2 using fun v => locNb v (s2 v) (hs2 v)
  let S : Finset (HeightOneSpectrum (𝓞 L)) := hI1.toFinset ∪ hI2.toFinset
  refine ⟨S, ∑ v ∈ S, (n1 v + n2 v), fun x hx hS => ?_⟩
  have hle : ∀ v ∈ S, ∀ k : ℕ, k ≤ n1 v + n2 v →
      exp (-((∑ v ∈ S, (n1 v + n2 v) : ℕ) : ℤ)) ≤ exp (-(k : ℤ)) := by
    intro v hv k hk
    apply exp_le_exp.2
    have := Finset.single_le_sum (f := fun v => n1 v + n2 v) (fun _ _ => Nat.zero_le _) hv
    omega
  have hy : (fun v => toInt x hx v, fun v => toInt x⁻¹ (inv_mem_UFin hx) v) ∈ t1 ×ˢ t2 := by
    refine ⟨hsub1 fun v hv => hn1 v _ ?_, hsub2 fun v hv => hn2 v _ ?_⟩
    · have hvS : v ∈ S := Finset.mem_union_left _ (hI1.mem_toFinset.2 hv)
      exact (hS v hvS).trans (hle v hvS _ (Nat.le_add_right _ _))
    · have hvS : v ∈ S := Finset.mem_union_right _ (hI2.mem_toFinset.2 hv)
      show Valued.v ((x⁻¹ : Ideles L).val.2 v - 1) ≤ _
      rw [val_inv_sub hx v]
      exact (hS v hvS).trans (hle v hvS _ (Nat.le_add_left _ _))
  have hgx : g (fun v => toInt x hx v, fun v => toInt x⁻¹ (inv_mem_UFin hx) v) = Units.embedProduct _ x := by
    have e1 : (((1 : InfiniteAdeleRing L), sm fun v => toInt x hx v) : AdeleRing (𝓞 L) L) = (x : AdeleRing (𝓞 L) L) :=
      Prod.ext hx.1.symm (FiniteAdeleRing.ext _ fun v => rfl)
    have e2 : (((1 : InfiniteAdeleRing L), sm fun v => toInt x⁻¹ (inv_mem_UFin hx) v) : AdeleRing (𝓞 L) L) =
        ((x⁻¹ : Ideles L) : AdeleRing (𝓞 L) L) :=
      Prod.ext (inv_mem_UFin hx).1.symm (FiniteAdeleRing.ext _ fun v => rfl)
    simp only [g]
    rw [e1, e2]
    rfl
  have := hsub hy
  rw [Set.mem_preimage, hgx] at this
  exact this

end PI.AlgValsFin.W
end
end

-- bundled from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.AlgebraicValuesFinite.OrdFEqOfClassOf
section
noncomputable section

open NumberField IsDedekindDomain Formalism.L2.Host Neutral.B1 ReciprocityTheory.Neutral.Bridge.HCFR

namespace PI.AlgValsFin.W

variable {L : Type} [Field L] [NumberField L]

def piU (v : HeightOneSpectrum (𝓞 L)) : (v.adicCompletion L)ˣ :=
  Classical.choose (exists_isUniformiserAt L v)

theorem piU_spec (v : HeightOneSpectrum (𝓞 L)) :
    IsUniformiserAt L v ((piU v : (v.adicCompletion L)ˣ) : v.adicCompletion L) :=
  Classical.choose_spec (exists_isUniformiserAt L v)

def eU (v : HeightOneSpectrum (𝓞 L)) : Ideles L := localIdele L v (piU v)

theorem ordAt_eU (v w : HeightOneSpectrum (𝓞 L)) [Decidable (w = v)] :
    ordAt L w (eU v) = if w = v then 1 else 0 := by
  classical
  unfold eU
  rw [ordAt_localIdele L v w (piU v) (piU_spec v)]
  congr 1

theorem ordAt_pow' (w : HeightOneSpectrum (𝓞 L)) (a : Ideles L) (n : ℕ) :
    ordAt L w (a ^ n) = n * ordAt L w a := by
  unfold ordAt
  have h : ((a ^ n : Ideles L) : AdeleRing (𝓞 L) L).2 w = ((a : AdeleRing (𝓞 L) L).2 w) ^ n := by
    rw [Units.val_pow_eq_pow_val]
    rfl
  rw [h, map_pow, WithZero.log_pow]
  simp only [nsmul_eq_mul]
  ring

theorem ordF_eq_of_classOf (a : Ideles L) (ha : classOf L a = 1) :
    ∃ k : Lˣ, ∀ w : HeightOneSpectrum (𝓞 L), ordF w k = ordAt L w a := by
  obtain ⟨k, u, hu, rfl⟩ := (classOf_eq_one_iff L a).1 ha
  refine ⟨k, fun w => ?_⟩
  rw [ordAt_mul, ordAt_diag, (ordAt_eq_zero_iff L w u).2 ((rayUnits_top_iff L u).1 hu w), add_zero]
  rfl

theorem classSame : ClassSame L := by
  classical
  refine ⟨ClassGroup (𝓞 L), inferInstance, fun v => classOf L (eU v), fun v w hvw => ?_⟩
  have h1 : classOf L (eU v * (eU w)⁻¹) = 1 := by
    have hvw' : classOf L (eU v) = classOf L (eU w) := hvw
    rw [map_mul, map_inv, hvw', mul_inv_cancel]
  obtain ⟨k, hk⟩ := ordF_eq_of_classOf _ h1
  refine ⟨k, fun u => ?_⟩
  rw [hk, ordAt_mul, ordAt_inv, ordAt_eU, ordAt_eU]
  ring

theorem classPow : ClassPow L := by
  classical
  refine ⟨Fintype.card (ClassGroup (𝓞 L)), Fintype.card_pos, fun v => ?_⟩
  have h1 : classOf L (eU v ^ Fintype.card (ClassGroup (𝓞 L))) = 1 := by
    rw [map_pow, pow_card_eq_one]
  obtain ⟨k, hk⟩ := ordF_eq_of_classOf _ h1
  refine ⟨k, fun u => ?_⟩
  rw [hk, ordAt_pow', ordAt_eU]
  split_ifs <;> simp

end PI.AlgValsFin.W
end
end

-- bundled from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.AlgebraicValuesFinite.ValuedAtFin
section
noncomputable section

open NumberField IsDedekindDomain Formalism.L2.Host

namespace PI.AlgValsFin.W

variable {L : Type} [Field L] [NumberField L]

theorem valued_atFin (v : HeightOneSpectrum (𝓞 L)) (k : Lˣ) :
    Valued.v ((atFin v k : (v.adicCompletion L)ˣ) : v.adicCompletion L) = WithZero.exp (-ordF v k) := by
  unfold ordF
  rw [neg_neg, WithZero.exp_log ((Valuation.ne_zero_iff _).2 k.ne_zero)]
  simp only [atFin, Units.coe_map, MonoidHom.coe_coe, RingHom.toMonoidHom_eq_coe]
  first
  | exact HeightOneSpectrum.valuedAdicCompletion_eq_valuation' v (k : L)
  | exact HeightOneSpectrum.valuedAdicCompletion_eq_valuation v (k : L)
  | exact HeightOneSpectrum.valuedAdicCompletion_eq_valuation (K := L) v (k : L)
  | exact HeightOneSpectrum.valuedAdicCompletion_eq_valuation' (K := L) v (k : L)
  | exact Valued.extension_extends _
  | rfl
  | simp [HeightOneSpectrum.valuedAdicCompletion_eq_valuation']
  | simp [HeightOneSpectrum.valuedAdicCompletion_eq_valuation]

theorem locVal : LocVal L := by
  intro χ v k hχ
  have hu : IsUnifAt v (atFin v (unif v)) := Classical.choose_spec (exists_unif v)
  unfold IsUnifAt at hu
  have hunit : IsUnitAt v (atFin v k * (atFin v (unif v) ^ ordF v k)⁻¹) := by
    unfold IsUnitAt
    rw [Units.val_mul, Units.val_inv_eq_inv_val, Units.val_zpow_eq_zpow_val, map_mul, map_inv₀, map_zpow₀, hu,
      valued_atFin, ← WithZero.exp_zsmul, smul_neg, smul_eq_mul, mul_one,
      mul_inv_cancel₀ WithZero.exp_ne_zero]
  have h1 := hχ _ hunit
  rw [map_mul, map_inv, map_zpow, mul_inv_eq_one] at h1
  rw [h1]
  rfl

end PI.AlgValsFin.W
end
end

