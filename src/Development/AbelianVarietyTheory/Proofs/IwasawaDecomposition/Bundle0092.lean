module

public import Mathlib
public import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
public import Formalism.LocalToGlobal.UnitaryNorms.Bundle0006
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsRationalUnitaryDeterminantMapRationalUnitaryTo
public import ReciprocityTheory.Automorphisms.Bundle0001
public import Formalism.LocalRingCardinality.RankBoundMonotoneInDimension
public import Formalism.LocalToGlobal.Divisibility.Bundle0001
public import Formalism.LocalToGlobal.UnitaryNorms.Bundle0005
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ExistsUniqueIdeleOfLinearEquivQuotientLocal

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsProdUnifMulUnitIdl
section
noncomputable section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.FrobeniusOrbits Neutral.B1 ReciprocityTheory.Neutral.Bridge.HCFR Formalism.L2.Host GlobalTheory.Mem.Chr

namespace GlobalTheory.Mem.Chr.IdlFact

variable {L : Type} [Field L] [NumberField L]

def valAt (w : HeightOneSpectrum (𝓞 L)) : Ideles L →* WithZero (Multiplicative ℤ) where
  toFun a := Valued.v ((a : AdeleRing (𝓞 L) L).2 w)
  map_one' := by
    show Valued.v (1 : w.adicCompletion L) = 1
    exact map_one _
  map_mul' a b := by
    show Valued.v ((a : AdeleRing (𝓞 L) L).2 w * (b : AdeleRing (𝓞 L) L).2 w) = _
    exact map_mul _ _ _

theorem valAt_apply (w : HeightOneSpectrum (𝓞 L)) (a : Ideles L) :
    valAt w a = Valued.v ((a : AdeleRing (𝓞 L) L).2 w) := rfl

theorem valAt_ne_zero (w : HeightOneSpectrum (𝓞 L)) (a : Ideles L) : valAt w a ≠ 0 :=
  ((Group.isUnit a).map (valAt w)).ne_zero

theorem valAt_localIdele_self (v : HeightOneSpectrum (𝓞 L)) (x : (v.adicCompletion L)ˣ) :
    valAt v (localIdele L v x) = Valued.v (x : v.adicCompletion L) := by
  classical
  have h : ((localIdele L v x : Ideles L) : AdeleRing (𝓞 L) L).2 v = x := by
    have := Function.update_self (β := fun w : HeightOneSpectrum (𝓞 L) => w.adicCompletion L) v
      (x : v.adicCompletion L) (fun _ => 1)
    convert this
    rfl
  rw [valAt_apply, h]

theorem valAt_localIdele_ne {v w : HeightOneSpectrum (𝓞 L)} (hw : w ≠ v) (x : (v.adicCompletion L)ˣ) :
    valAt w (localIdele L v x) = 1 := by
  classical
  have h : ((localIdele L v x : Ideles L) : AdeleRing (𝓞 L) L).2 w = 1 := by
    have := Function.update_of_ne (β := fun w : HeightOneSpectrum (𝓞 L) => w.adicCompletion L) hw
      (x : v.adicCompletion L) (fun _ => 1)
    convert this
    rfl
  rw [valAt_apply, h, map_one]

theorem finite_valAt_ne_one (a : Ideles L) : {v | valAt v a ≠ 1}.Finite := by
  have hu : IsUnit ((a : AdeleRing (𝓞 L) L).2) :=
    a.isUnit.map (MonoidHom.snd (InfiniteAdeleRing L) (FiniteAdeleRing (𝓞 L) L))
  exact (FiniteAdeleRing.isUnit_iff.1 hu).2

open Classical in
theorem valAt_prod (S : Finset (HeightOneSpectrum (𝓞 L))) (n : HeightOneSpectrum (𝓞 L) → ℤ)
    (w : HeightOneSpectrum (𝓞 L)) :
    valAt w (∏ v ∈ S, localIdele L v (atFin v (unif v)) ^ n v) =
      WithZero.exp (-(if w ∈ S then n w else 0)) := by
  rw [map_prod]
  have h1 : ∀ v, v ≠ w → valAt w (localIdele L v (atFin v (unif v)) ^ n v) = 1 := fun v hv => by
    rw [map_zpow, valAt_localIdele_ne hv.symm, one_zpow]
  split_ifs with hw
  · rw [Finset.prod_eq_single_of_mem w hw (fun v _ hv => h1 v hv), map_zpow, valAt_localIdele_self]
    have h2 : Valued.v ((atFin w (unif w) : (w.adicCompletion L)ˣ) : w.adicCompletion L) = WithZero.exp (-1 : ℤ) :=
      unif_spec w
    rw [h2, ← WithZero.exp_zsmul]
    simp
  · rw [Finset.prod_eq_one (fun v hv => h1 v (fun e => hw (e ▸ hv)))]
    simp

end GlobalTheory.Mem.Chr.IdlFact


open Classical in
theorem GlobalTheory.Mem.Chr.exists_prod_unif_mul_unitIdl : ∀ (L : Type) [Field L] [NumberField L] (a : Ideles L), ∃ (S : Finset (HeightOneSpectrum (𝓞 L))) (n : HeightOneSpectrum (𝓞 L) → ℤ) (u : Ideles L), u ∈ unitIdl L ∧ a = (∏ v ∈ S, localIdele L v (atFin v (unif v)) ^ n v) * u ∧ ∀ v, Valued.v ((a : AdeleRing (𝓞 L) L).2 v) = WithZero.exp (-(if v ∈ S then n v else 0)) := by
  intro L _ _ a
  let S := (GlobalTheory.Mem.Chr.IdlFact.finite_valAt_ne_one a).toFinset
  let n : HeightOneSpectrum (𝓞 L) → ℤ := fun v => -WithZero.log (GlobalTheory.Mem.Chr.IdlFact.valAt v a)
  have hv : ∀ v, GlobalTheory.Mem.Chr.IdlFact.valAt v a = WithZero.exp (-(if v ∈ S then n v else 0)) := fun v => by
    split_ifs with h
    · simp only [n, neg_neg]
      exact (WithZero.exp_log (GlobalTheory.Mem.Chr.IdlFact.valAt_ne_zero v a)).symm
    · have : GlobalTheory.Mem.Chr.IdlFact.valAt v a = 1 := by simpa [S] using h
      rw [this]; simp
  refine ⟨S, n, (∏ v ∈ S, localIdele L v (atFin v (unif v)) ^ n v)⁻¹ * a, fun v => ?_, ?_, hv⟩
  · rw [← GlobalTheory.Mem.Chr.IdlFact.valAt_apply, map_mul, map_inv, GlobalTheory.Mem.Chr.IdlFact.valAt_prod, hv v]
    exact inv_mul_cancel₀ WithZero.exp_ne_zero
  · rw [mul_inv_cancel_left]
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsTameLocOfResidue
section
noncomputable section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.FrobeniusOrbits Neutral.B1 ReciprocityTheory.Neutral.Bridge.HCFR Formalism.L2.Host GlobalTheory.Mem.Chr

namespace GlobalTheory.Mem.Chr

variable {L : Type} [Field L] [NumberField L] (v : HeightOneSpectrum (𝓞 L))

theorem tame_valued_int (a : 𝓞 L) :
    Valued.v (algebraMap (𝓞 L) (v.adicCompletion L) a) = v.valuation L (algebraMap (𝓞 L) L a) :=
  ReciprocityTheory.Aut.adic_valued_algebraMap v (algebraMap (𝓞 L) L a)

theorem tame_valued_lt_one_iff (a : 𝓞 L) :
    Valued.v (algebraMap (𝓞 L) (v.adicCompletion L) a) < 1 ↔ a ∈ v.asIdeal := by
  rw [tame_valued_int,
    HeightOneSpectrum.valuation_lt_one_iff_mem]

theorem tame_mk_eq {u : v.adicCompletion L} {a b : 𝓞 L}
    (ha : Valued.v (u - algebraMap (𝓞 L) (v.adicCompletion L) a) < 1)
    (hb : Valued.v (u - algebraMap (𝓞 L) (v.adicCompletion L) b) < 1) :
    Ideal.Quotient.mk v.asIdeal a = Ideal.Quotient.mk v.asIdeal b := by
  rw [Ideal.Quotient.eq, ← tame_valued_lt_one_iff, map_sub]
  have e : algebraMap (𝓞 L) (v.adicCompletion L) a - algebraMap (𝓞 L) (v.adicCompletion L) b =
      (u - algebraMap (𝓞 L) (v.adicCompletion L) b) - (u - algebraMap (𝓞 L) (v.adicCompletion L) a) := by
    ring
  rw [e]
  exact lt_of_le_of_lt (Valuation.map_sub _ _ _) (max_lt hb ha)

def unitPart : (v.adicCompletion L)ˣ →* (v.adicCompletion L)ˣ where
  toFun x := x * atFin v (unif v) ^ WithZero.log (Valued.v (x : v.adicCompletion L))
  map_one' := by simp
  map_mul' x y := by
    rw [Units.val_mul, map_mul, WithZero.log_mul (by simp) (by simp), zpow_add]
    exact mul_mul_mul_comm _ _ _ _

theorem isUnitAt_unitPart (x : (v.adicCompletion L)ˣ) : IsUnitAt v (unitPart v x) := by
  have h : Valued.v ((atFin v (unif v) : (v.adicCompletion L)ˣ) : v.adicCompletion L) =
      WithZero.exp (-1 : ℤ) := unif_spec v
  have hx : Valued.v (x : v.adicCompletion L) ≠ 0 := by simp
  show Valued.v ((x * atFin v (unif v) ^ WithZero.log (Valued.v (x : v.adicCompletion L)) :
    (v.adicCompletion L)ˣ) : v.adicCompletion L) = 1
  rw [Units.val_mul, Units.val_zpow_eq_zpow_val, map_mul, map_zpow₀, h, ← WithZero.exp_zsmul]
  nth_rewrite 1 [← WithZero.exp_log hx]
  rw [← WithZero.exp_add]
  simp

theorem unitPart_of_isUnitAt {x : (v.adicCompletion L)ˣ} (hx : IsUnitAt v x) : unitPart v x = x := by
  have h : Valued.v (x : v.adicCompletion L) = 1 := hx
  show x * atFin v (unif v) ^ WithZero.log (Valued.v (x : v.adicCompletion L)) = x
  rw [h]
  simp

theorem exists_unitPart_approx (x : (v.adicCompletion L)ˣ) : ∃ a : 𝓞 L,
    Valued.v ((unitPart v x : v.adicCompletion L) - algebraMap (𝓞 L) (v.adicCompletion L) a) < 1 :=
  ReciprocityTheory.Aut.adic_exists_approx v _ (le_of_eq (isUnitAt_unitPart v x))

def resPart : (v.adicCompletion L)ˣ →* 𝓞 L ⧸ v.asIdeal where
  toFun x := Ideal.Quotient.mk v.asIdeal (exists_unitPart_approx v x).choose
  map_one' := by
    refine tame_mk_eq v (b := 1) (exists_unitPart_approx v 1).choose_spec ?_
    simp
  map_mul' x y := by
    rw [← map_mul]
    refine tame_mk_eq v (exists_unitPart_approx v (x * y)).choose_spec ?_
    have hx := (exists_unitPart_approx v x).choose_spec
    have hy := (exists_unitPart_approx v y).choose_spec
    set a := (exists_unitPart_approx v x).choose
    set b := (exists_unitPart_approx v y).choose
    have hu : Valued.v (unitPart v x : v.adicCompletion L) = 1 := isUnitAt_unitPart v x
    have hb : Valued.v (algebraMap (𝓞 L) (v.adicCompletion L) b) ≤ 1 := by
      rw [tame_valued_int]
      exact v.valuation_le_one b
    have e : (unitPart v (x * y) : v.adicCompletion L) - algebraMap (𝓞 L) (v.adicCompletion L) (a * b) =
        (unitPart v x : v.adicCompletion L) *
          ((unitPart v y : v.adicCompletion L) - algebraMap (𝓞 L) (v.adicCompletion L) b) +
        ((unitPart v x : v.adicCompletion L) - algebraMap (𝓞 L) (v.adicCompletion L) a) *
          algebraMap (𝓞 L) (v.adicCompletion L) b := by
      rw [map_mul, map_mul, Units.val_mul]
      ring
    rw [e]
    refine lt_of_le_of_lt (Valuation.map_add _ _ _) (max_lt ?_ ?_)
    · rwa [map_mul, hu, one_mul]
    · rw [map_mul]
      exact lt_of_le_of_lt (mul_le_of_le_one_right' hb) hx

theorem resPart_eq {x : (v.adicCompletion L)ˣ} (hx : IsUnitAt v x) {a : 𝓞 L}
    (ha : Valued.v ((x : v.adicCompletion L) - algebraMap (𝓞 L) (v.adicCompletion L) a) < 1) :
    resPart v x = Ideal.Quotient.mk v.asIdeal a := by
  refine tame_mk_eq v (exists_unitPart_approx v x).choose_spec ?_
  rwa [unitPart_of_isUnitAt v hx]


open Classical in
theorem exists_tameLoc_of_residue : ∀ (L : Type) [Field L] [NumberField L] (v : HeightOneSpectrum (𝓞 L)) (θ0 : (𝓞 L ⧸ v.asIdeal)ˣ →* ℂˣ), ∃ θ : (v.adicCompletion L)ˣ →* ℂˣ, TameLoc v θ ∧ (∀ (k : Lˣ) (y : 𝓞 L) (b : (𝓞 L ⧸ v.asIdeal)ˣ), (k : L) = (y : L) → (b : 𝓞 L ⧸ v.asIdeal) = Ideal.Quotient.mk v.asIdeal y → θ (atFin v k) = θ0 b) ∧ ∀ x, IsUnitAt v x → ∃ b, θ x = θ0 b := by
  intro L _ _ v θ0
  haveI : Finite (𝓞 L ⧸ v.asIdeal) := v.asIdeal.finiteQuotientOfFreeOfNeBot v.ne_bot
  refine ⟨θ0.comp (resPart v).toHomUnits, ⟨fun x => ?_, fun x hx h1 => ?_⟩, fun k y b hk hb => ?_,
    fun x _ => ⟨_, rfl⟩⟩
  · have hf : IsOfFinOrder ((θ0 ((resPart v).toHomUnits x) : ℂˣ) : ℂ) :=
      ((Units.coeHom ℂ).comp θ0).isOfFinOrder (isOfFinOrder_of_finite _)
    exact hf.norm_eq_one
  · have e : (resPart v).toHomUnits x = 1 := by
      apply Units.ext
      show resPart v x = Ideal.Quotient.mk v.asIdeal 1
      refine resPart_eq v hx ?_
      rw [map_one]
      refine lt_of_le_of_lt h1 ?_
      rw [← WithZero.exp_zero, WithZero.exp_lt_exp]
      norm_num
    rw [MonoidHom.comp_apply, e, map_one]
  · have ek : ((atFin v k : (v.adicCompletion L)ˣ) : v.adicCompletion L) =
        algebraMap (𝓞 L) (v.adicCompletion L) y := by
      show algebraMap L (v.adicCompletion L) (k : L) = _
      rw [hk]
      rfl
    have hy : y ∉ v.asIdeal := by
      intro hy
      rw [Ideal.Quotient.eq_zero_iff_mem.2 hy] at hb
      haveI := v.isPrime
      exact b.ne_zero hb
    have hu : IsUnitAt v (atFin v k) := by
      show Valued.v ((atFin v k : (v.adicCompletion L)ˣ) : v.adicCompletion L) = 1
      rw [ek]
      refine le_antisymm ?_ (not_lt.1 fun h => hy ((tame_valued_lt_one_iff v y).1 h))
      rw [tame_valued_int]
      exact v.valuation_le_one y
    have e : (resPart v).toHomUnits (atFin v k) = b := by
      apply Units.ext
      show resPart v (atFin v k) = _
      rw [hb]
      refine resPart_eq v hu ?_
      rw [ek, sub_self, map_zero]
      exact zero_lt_one
    rw [MonoidHom.comp_apply, e]

end GlobalTheory.Mem.Chr
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsUnitOfRoot
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.FrobeniusOrbits Neutral.B1 ReciprocityTheory.Neutral.Bridge.HCFR Formalism.L2.Host GlobalTheory.Mem.Chr

namespace GlobalTheory.Mem.Chr

theorem CMData.embedding_conj {F L : Type} [Field F] [NumberField F] [Field L] [NumberField L] [Algebra F L]
    {c : L ≃ₐ[F] L} {I : Type} {φ : I → L →+* ℂ} (h : GlobalTheory.Mem.Chr.CMData F c φ) (ψ : L →+* ℂ) (x : L) :
    ψ (c x) = (starRingEnd ℂ) (ψ x) := by
  have := h.real
  have := h.cplx
  have : Algebra.IsQuadraticExtension F L := { finrank_eq_two' := h.rank }
  have hr : ComplexEmbedding.IsReal (ψ.comp (algebraMap F L)) :=
    InfinitePlace.isReal_mk_iff.1 (IsTotallyReal.isReal _)
  obtain ⟨σ, hσ⟩ := NumberField.ComplexEmbedding.exists_comp_symm_eq_of_comp_eq (k := F) ψ
    (ComplexEmbedding.conjugate ψ) (by
      ext a
      exact (RingHom.congr_fun hr a).symm)
  have hcard : Nat.card (L ≃ₐ[F] L) = 2 := by rw [IsGalois.card_aut_eq_finrank, h.rank]
  obtain ⟨y, -, hy⟩ := (Nat.card_eq_two_iff' (1 : L ≃ₐ[F] L)).1 hcard
  have hne : σ.symm ≠ 1 := by
    intro e
    have hc : ¬ ComplexEmbedding.IsReal ψ :=
      InfinitePlace.isComplex_mk_iff.1 (IsTotallyComplex.isComplex _)
    apply hc
    rw [ComplexEmbedding.isReal_iff, ← hσ, e]
    rfl
  have e : c = σ.symm := (hy c h.ne).trans (hy _ hne).symm
  rw [e]
  exact RingHom.congr_fun hσ x


open Classical in
theorem normOne_unit_isRoot : ∀ (F L : Type) [Field F] [NumberField F] [Field L] [NumberField L] [Algebra F L] (c : L ≃ₐ[F] L) (I : Type) [Fintype I] (φ : I → L →+* ℂ), CMData F c φ → ∀ k : Lˣ, (k : L) * c (k : L) = 1 → (∀ v : HeightOneSpectrum (𝓞 L), v.valuation L (k : L) = 1) → ∃ m : ℕ, 0 < m ∧ (k : L) ^ m = 1 := by
  intro F L _ _ _ _ _ c I _ φ h k hk hv
  obtain ⟨a, ha⟩ := HeightOneSpectrum.mem_integers_of_valuation_le_one (R := 𝓞 L) L (k : L) fun v => (hv v).le
  have hi : IsIntegral ℤ (k : L) := ha ▸ a.isIntegral_coe
  obtain ⟨n, hn, hp⟩ := NumberField.Embeddings.pow_eq_one_of_norm_eq_one L ℂ hi (fun ψ => by
    have h1 := congrArg (fun z => ‖ψ z‖) hk
    simp only [map_mul, h.embedding_conj, map_one, norm_mul, norm_one, RCLike.norm_conj] at h1
    nlinarith [norm_nonneg (ψ (k : L))])
  exact ⟨n, hn, hp⟩

theorem exists_unit_of_root {L : Type} [Field L] [NumberField L] (k : Lˣ) (h : ∃ m : ℕ, 0 < m ∧ (k : L) ^ m = 1) :
    ∃ ζ : (𝓞 L)ˣ, Units.map (algebraMap (𝓞 L) L : 𝓞 L →* L) ζ = k := by
  obtain ⟨m, hm, hk⟩ := h
  have hi : IsIntegral ℤ (k : L) := IsIntegral.of_pow hm (hk ▸ isIntegral_one)
  obtain ⟨X, hX⟩ : ∃ X : 𝓞 L, algebraMap (𝓞 L) L X = k := ⟨⟨k, hi⟩, rfl⟩
  have h1 : X ^ m = 1 := RingOfIntegers.coe_injective (by rw [map_pow, hX, hk, map_one])
  exact ⟨Units.ofPowEqOne X m h1 hm.ne', Units.ext hX⟩

end GlobalTheory.Mem.Chr
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsUnitaryRationalInfTypeSubgroupAndInfTypeUnique
section
noncomputable section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.FrobeniusOrbits Neutral.B1 ReciprocityTheory.Neutral.Bridge.HCFR Formalism.L2.Host GlobalTheory.Mem.Chr Filter Topology

namespace GlobalTheory.HalfIntChars

theorem emb_mul_indep {L I : Type} [Field L] [CharZero L] [Fintype I] (σ : I → L →+* ℂ) (hσ : Function.Injective σ)
    (m : I → ℤ) (h : ∀ k : L, k ≠ 0 → ∏ i, σ i k ^ m i = 1) : m = 0 := by
  classical
  have key : ∀ x : L, ∑ i, (m i : ℂ) * σ i x = 0 := by
    intro x
    let f : ℂ → ℂ := fun t => ∏ i, (1 + t * σ i x) ^ m i
    have hd : ∀ i ∈ (Finset.univ : Finset I),
        HasDerivAt (fun t : ℂ => (1 + t * σ i x) ^ m i) ((m i : ℂ) * σ i x) 0 := by
      intro i _
      have h1 : HasDerivAt (fun t : ℂ => 1 + t * σ i x) (σ i x) 0 := by
        simpa using ((hasDerivAt_id (0 : ℂ)).mul_const (σ i x)).const_add 1
      have h2 := (hasDerivAt_zpow (m i) ((fun t : ℂ => 1 + t * σ i x) 0) (Or.inl (by simp))).comp (0 : ℂ) h1
      simpa [Function.comp_def] using h2
    have hf : HasDerivAt f (∑ i, (m i : ℂ) * σ i x) 0 := by
      have := HasDerivAt.fun_finsetProd hd
      simpa [f] using this
    have hs := hasDerivAt_iff_tendsto_slope.1 hf
    have hu : Tendsto (fun n : ℕ => ((1 : ℂ) / ((n : ℂ) + 1))) atTop (𝓝[≠] 0) := by
      refine tendsto_nhdsWithin_iff.2 ⟨tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℂ), Eventually.of_forall fun n => ?_⟩
      exact one_div_ne_zero (Nat.cast_add_one_ne_zero n)
    have hfin : ∀ᶠ n : ℕ in atTop, (1 + (1 / ((n : L) + 1)) * x) ≠ 0 := by
      rw [← Nat.cofinite_eq_atTop]
      refine Set.Subsingleton.finite ?_
      intro a ha b hb
      simp only [Set.mem_compl_iff, Set.mem_setOf_eq, not_not] at ha hb
      have ha1 : ((a : L) + 1) ≠ 0 := Nat.cast_add_one_ne_zero a
      have hb1 : ((b : L) + 1) ≠ 0 := Nat.cast_add_one_ne_zero b
      field_simp at ha hb
      have : (a : L) = b := by linear_combination ha - hb
      exact_mod_cast this
    have h0 : Tendsto (fun n : ℕ => slope f 0 ((1 : ℂ) / ((n : ℂ) + 1))) atTop (𝓝 0) := by
      refine tendsto_const_nhds.congr' (hfin.mono fun n hn => ?_)
      have h1 := h _ hn
      have h2 : f ((1 : ℂ) / ((n : ℂ) + 1)) = 1 := by
        refine Eq.trans ?_ h1; simp [f]
      have h3 : f 0 = 1 := by simp [f]
      simp only [slope, h2, h3, vsub_self, smul_zero]
    exact tendsto_nhds_unique (hs.comp hu) h0
  have li := (linearIndependent_monoidHom L ℂ).comp (fun i => (σ i : L →* ℂ))
    (fun i j hij => hσ (RingHom.coe_monoidHom_injective hij))
  have := Fintype.linearIndependent_iff.1 li (fun i => (m i : ℂ)) (by
    funext x
    simpa [Finset.sum_apply] using key x)
  funext i
  exact_mod_cast this i

theorem unit_sq (z : ℂ) (hz : z ≠ 0) : (z / ((‖z‖ : ℝ) : ℂ)) ^ 2 = z / starRingEnd ℂ z := by
  have h1 : ((‖z‖ : ℝ) : ℂ) ≠ 0 := by exact_mod_cast norm_ne_zero_iff.2 hz
  have h2 : starRingEnd ℂ z ≠ 0 := by simpa using hz
  have h3 : z * starRingEnd ℂ z = ((‖z‖ : ℝ) : ℂ) ^ 2 := by
    rw [Complex.mul_conj, Complex.normSq_eq_norm_sq]; push_cast; ring
  field_simp
  rw [← h3]

theorem hasInf_unique {L I : Type} [Field L] [NumberField L] [Fintype I] (φ : I → L →+* ℂ) (h1 : Function.Injective φ)
    (h2 : ∀ i j, φ i ≠ (starRingEnd ℂ).comp (φ j)) {χ : HChar L} {n n' : I → ℤ} (h : χ.HasInf φ n) (h' : χ.HasInf φ n') :
    n = n' := by
  let σ : I ⊕ I → L →+* ℂ := Sum.elim φ fun i => (starRingEnd ℂ).comp (φ i)
  have hσ : Function.Injective σ := by
    rintro (i | i) (j | j) hij
    · exact congrArg _ (h1 hij)
    · exact absurd hij (h2 i j)
    · exact absurd hij.symm (h2 j i)
    · refine congrArg _ (h1 (RingHom.ext fun x => ?_))
      have := congrArg (fun f : L →+* ℂ => starRingEnd ℂ (f x)) hij
      simpa [σ] using this
  have := emb_mul_indep σ hσ (Sum.elim (n - n') (n' - n)) (fun k hk => by
    have e := (h (Units.mk0 k hk)).symm.trans (h' (Units.mk0 k hk))
    simp only [Units.val_mk0] at e
    have hne : ∀ i, φ i k ≠ 0 := fun i => by simpa using hk
    have hu : ∀ i, φ i k / ((‖φ i k‖ : ℝ) : ℂ) ≠ 0 := fun i =>
      div_ne_zero (hne i) (by exact_mod_cast norm_ne_zero_iff.2 (hne i))
    have e2 : ∏ i, (φ i k / ((‖φ i k‖ : ℝ) : ℂ)) ^ (n i - n' i) = 1 := by
      simp_rw [zpow_sub₀ (hu _)]
      rw [Finset.prod_div_distrib, e, div_self]
      exact Finset.prod_ne_zero_iff.2 fun i _ => zpow_ne_zero _ (hu i)
    have e3 := congrArg (· ^ 2) e2
    simp only [← Finset.prod_pow, one_pow] at e3
    rw [Fintype.prod_sum_type, ← Finset.prod_mul_distrib, ← e3]
    refine Finset.prod_congr rfl fun i _ => ?_
    rw [← zpow_natCast, ← zpow_mul, mul_comm (n i - n' i), zpow_mul, zpow_natCast, unit_sq _ (hne i), div_zpow]
    simp only [σ, Sum.elim_inl, Sum.elim_inr, Pi.sub_apply, RingHom.comp_apply]
    rw [div_eq_mul_inv, ← zpow_neg, neg_sub])
  funext i
  have := congrFun this (Sum.inl i)
  simpa [sub_eq_zero] using this

theorem hasInfQ_inv {L I : Type} [Field L] [NumberField L] [Fintype I] {φ : I → L →+* ℂ} {χ : HChar L} {a : I → ℚ}
    (h : χ.HasInfQ φ a) : (χ⁻¹).HasInfQ φ (-a) := by
  obtain ⟨n, hn, h⟩ := h
  refine ⟨-n, fun i => by simp [hn], fun k => ?_⟩
  rw [HChar.inf_inv, Units.val_inv_eq_inv_val, h k, ← Finset.prod_inv_distrib]
  simp

theorem embPsi_inj {R : Ranks} (H : Formalism.BasicNotions.Host R) : Function.Injective (embPsi H) := fun _ _ h =>
  Subtype.ext ((factEmb R H).1.1 h)

theorem embPsi_ne_conj {R : Ranks} (H : Formalism.BasicNotions.Host R) (i j : R.Psi) :
    embPsi H i ≠ (starRingEnd ℂ).comp (embPsi H j) := by
  intro h
  have hi : embPsi H i (H.sqd) = Complex.I * ((Real.sqrt H.d : ℝ) : ℂ) :=
    ((factEmb R H).2 _).2 i.2
  have hj : embPsi H j (H.sqd) = Complex.I * ((Real.sqrt H.d : ℝ) : ℂ) :=
    ((factEmb R H).2 _).2 j.2
  rw [h, RingHom.comp_apply, hj, map_mul, Complex.conj_I, Complex.conj_ofReal] at hi
  have h0 : ((Real.sqrt H.d : ℝ) : ℂ) = 0 := by
    have : (2 * Complex.I) * ((Real.sqrt H.d : ℝ) : ℂ) = 0 := by linear_combination -hi
    exact (mul_eq_zero.1 this).resolve_left (mul_ne_zero two_ne_zero Complex.I_ne_zero)
  have hd : 0 < H.d := H.hyp.2.1.pos
  have : (0 : ℝ) < Real.sqrt H.d := Real.sqrt_pos.2 (by exact_mod_cast hd)
  exact this.ne' (by exact_mod_cast h0)


end GlobalTheory.HalfIntChars
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FiniteIndexUnitIdlSup
section
noncomputable section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.FrobeniusOrbits Neutral.B1 ReciprocityTheory.Neutral.Bridge.HCFR Formalism.L2.Host GlobalTheory.Mem.Chr
open scoped nonZeroDivisors

namespace GlobalTheory.Mem.UnitIndex

variable (L : Type) [Field L] [NumberField L]

def finIdele : Ideles L →* (FiniteAdeleRing (𝓞 L) L)ˣ :=
  Units.map (MonoidHom.snd (InfiniteAdeleRing L) (FiniteAdeleRing (𝓞 L) L))

def idealHom : (FiniteAdeleRing (𝓞 L) L)ˣ →* FractionalIdeal (𝓞 L)⁰ L where
  toFun := GlobalTheory.Idele.idealOf
  map_one' := GlobalTheory.Idele.idealOf_one
  map_mul' := GlobalTheory.Idele.idealOf_mul

def classHom : Ideles L →* ClassGroup (𝓞 L) :=
  (ClassGroup.mk L).comp ((idealHom L).comp (finIdele L)).toHomUnits

theorem ker_classHom_le : (classHom L).ker ≤ unitIdl L ⊔ (diagUnits L).range := by
  intro a ha
  have h1 : ClassGroup.mk L (((idealHom L).comp (finIdele L)).toHomUnits a) = 1 := ha
  rw [ClassGroup.mk_eq_one_iff] at h1
  obtain ⟨x, hx⟩ := (FractionalIdeal.isPrincipal_iff _).1 h1
  have hx' : GlobalTheory.Idele.idealOf (finIdele L a) = FractionalIdeal.spanSingleton (𝓞 L)⁰ x := hx
  have hx0 : x ≠ 0 := by
    rintro rfl
    exact GlobalTheory.Idele.idealOf_ne_zero _ (hx'.trans (FractionalIdeal.spanSingleton_zero))
  have hd : finIdele L (diagUnits L (Units.mk0 x hx0)) =
      FiniteAdeleRing.unitEmbedding (𝓞 L) L (Units.mk0 x hx0) := Units.ext rfl
  have hu : a * (diagUnits L (Units.mk0 x hx0))⁻¹ ∈ unitIdl L := by
    refine (GlobalTheory.Idele.smul_eq_self_iff (finIdele L (a * (diagUnits L (Units.mk0 x hx0))⁻¹))
      (I := 1) one_ne_zero).1 ?_
    rw [GlobalTheory.Idele.smul_one_eq, map_mul, map_inv, GlobalTheory.Idele.idealOf_mul, GlobalTheory.Idele.idealOf_inv, hd,
      GlobalTheory.Idele.idealOf_unitEmbedding, hx']
    exact mul_inv_cancel₀ (FractionalIdeal.spanSingleton_ne_zero_iff.2 hx0)
  have : a = a * (diagUnits L (Units.mk0 x hx0))⁻¹ * diagUnits L (Units.mk0 x hx0) := by simp
  rw [this]
  exact Subgroup.mul_mem_sup hu ⟨_, rfl⟩


open Classical in
theorem finiteIndex_unitIdl_sup : ∀ (L : Type) [Field L] [NumberField L],
    (unitIdl L ⊔ (diagUnits L).range).FiniteIndex := by
  intro L _ _
  have : (classHom L).ker.FiniteIndex := Subgroup.finiteIndex_ker _
  exact Subgroup.finiteIndex_of_le (ker_classHom_le L)

end GlobalTheory.Mem.UnitIndex
end
end

