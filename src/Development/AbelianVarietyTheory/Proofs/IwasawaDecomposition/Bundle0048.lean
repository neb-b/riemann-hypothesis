module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ExistsNotCongPow
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0041
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0045
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0037
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsUniqueHcharOfFiniteOrder
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0043

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.InertiaLiftOfResidualTrivial
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.WeilDeligne Pointwise

namespace GlobalTheory.InertiaLift

theorem exists_mem_Ine_eq_on : ∀ (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω]
    [IsAlgClosure E Ω] (A : ValuationSubring Ω) (w : HeightOneSpectrum (𝓞 E)), IsPlaceOver A w →
    ∀ (L : IntermediateField E Ω) (ψ : G E Ω), ψ ∈ Dec (F := E) A →
    (∀ x ∈ L, IsIntegral ℤ x → A.valuation (ψ x - x) < 1) →
    ∃ ι ∈ Ine (F := E) A, ∀ x ∈ L, ι x = ψ x := by
  intro E Ω _ _ _ _ _ A w _ L ψ hψ hL
  letI : TopologicalSpace (IntCl E Ω) := ⊥
  haveI : DiscreteTopology (IntCl E Ω) := ⟨rfl⟩
  haveI := continuousSMul_intCl E Ω
  let H := L.fixingSubgroup
  have hH : IsClosed (H : Set (Ω ≃ₐ[E] Ω)) := by
    have e : (H : Set (Ω ≃ₐ[E] Ω)) = ⋂ x : L, ((MulAction.stabilizer (Ω ≃ₐ[E] Ω) (x : Ω) :
        Subgroup (Ω ≃ₐ[E] Ω)) : Set (Ω ≃ₐ[E] Ω)) := by
      ext σ
      simp only [Set.mem_iInter, SetLike.mem_coe, MulAction.mem_stabilizer_iff, AlgEquiv.smul_def]
      rw [IntermediateField.mem_fixingSubgroup_iff]
      exact ⟨fun h x => h x x.2, fun h x hx => h ⟨x, hx⟩⟩
    rw [e]
    exact isClosed_iInter fun x =>
      (MulAction.stabilizer (Ω ≃ₐ[E] Ω) (x : Ω)).isClosed_of_isOpen
        (stabilizer_isOpen_of_isIntegral (K := E) (x : Ω))
  haveI : CompactSpace H := isCompact_iff_compactSpace.mp hH.isCompact
  let Q := primeBelow (F := E) A
  let R' := FixedPoints.subalgebra (𝓞 E) (IntCl E Ω) H
  have hR' : ∀ b : R', ∀ k ∈ H, k • (b : IntCl E Ω) = b := fun b k hk => b.2 ⟨k, hk⟩
  have : SMulCommClass H R' (IntCl E Ω) := ⟨fun k r b => by
    change (k : Ω ≃ₐ[E] Ω) • ((r : IntCl E Ω) * b) = (r : IntCl E Ω) * (k : Ω ≃ₐ[E] Ω) • b
    rw [smul_mul', hR' r k k.2]⟩
  have : Algebra.IsInvariant R' (IntCl E Ω) H := ⟨fun b hb => ⟨⟨b, hb⟩, rfl⟩⟩
  have : Q.LiesOver (Q.under R') := ⟨rfl⟩
  have hψQ : ψ • Q = Q := by
    have h1 : ψ • A = A := hψ
    rw [← primeBelow_smul, h1]
  have hfix : ∀ r : R', ψ • (r : IntCl E Ω) - r ∈ Q := by
    intro r
    have hrL : ((r : IntCl E Ω) : Ω) ∈ L := by
      rw [← InfiniteGalois.fixedField_fixingSubgroup L, IntermediateField.mem_fixedField_iff]
      intro f hf
      exact congrArg Subtype.val (hR' r f hf)
    exact hL _ hrL (isIntegral_int_of_isIntegral (r : IntCl E Ω).2)
  let φ : (IntCl E Ω ⧸ Q) ≃ₐ[R' ⧸ Q.under R'] (IntCl E Ω ⧸ Q) := AlgEquiv.ofRingEquiv
    (f := Ideal.quotientEquiv Q Q (MulSemiringAction.toRingEquiv (Ω ≃ₐ[E] Ω) (IntCl E Ω) ψ)
      hψQ.symm)
    (fun r => by
      obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective r
      change Ideal.Quotient.mk Q (ψ • (r : IntCl E Ω)) = Ideal.Quotient.mk Q (r : IntCl E Ω)
      rw [Ideal.Quotient.eq]
      exact hfix r)
  obtain ⟨⟨v, hvQ⟩, hv⟩ := Ideal.Quotient.stabilizerHom_surjective_of_profinite (G := H)
    (Q.under R') Q φ
  refine ⟨ψ * (v : Ω ≃ₐ[E] Ω)⁻¹, GlobalTheory.InertiaMovesRoot.mem_Ine_of_cong fun b => ?_, fun x hx => ?_⟩
  · have h1 : Ideal.Quotient.mk Q ((v : Ω ≃ₐ[E] Ω) • ((v : Ω ≃ₐ[E] Ω)⁻¹ • b)) =
        Ideal.Quotient.mk Q (ψ • ((v : Ω ≃ₐ[E] Ω)⁻¹ • b)) :=
      DFunLike.congr_fun hv (Ideal.Quotient.mk Q ((v : Ω ≃ₐ[E] Ω)⁻¹ • b))
    rw [smul_inv_smul, eq_comm, Ideal.Quotient.eq] at h1
    rwa [mul_smul]
  · have hv' : ((v : Ω ≃ₐ[E] Ω)⁻¹) x = x :=
      (IntermediateField.mem_fixingSubgroup_iff L _).mp (H.inv_mem v.2) x hx
    rw [AlgEquiv.mul_apply, hv']

end GlobalTheory.InertiaLift
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MvPolynomialEvalZeroOfVanishingRationalSkewHermiStatement
section
open Matrix Formalism.L2.NG ReciprocityTheory.Aut Formalism.AUTREP NumberField GlobalTheory.AlgWtHW
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.mvPolynomial_eval_zero_of_vanishing_rational_skewHermitian : ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] (n : ℕ) (Q : MvPolynomial ((L →+* ℂ) × Fin n × Fin n) ℂ), (∀ S : Matrix (Fin n) (Fin n) L, S + (S.map (IsCMField.complexConj L : L →+* L))ᵀ = 0 → MvPolynomial.eval (upt (ratPt S)) Q = 0) → ∀ Y : (L →+* ℂ) → Matrix (Fin n) (Fin n) ℂ, (∀ σ, Y (ComplexEmbedding.conjugate σ) = -(Y σ)ᵀ) → MvPolynomial.eval (upt Y) Q = 0 := by
  first | exact @GlobalTheory.AlgWtHW.eval_upt_eq_zero_of_skew | exact GlobalTheory.AlgWtHW.eval_upt_eq_zero_of_skew | (intros; apply GlobalTheory.AlgWtHW.eval_upt_eq_zero_of_skew <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ProdLocalValuesGlobalOverPlacesAbove
section
noncomputable section

open NumberField IsDedekindDomain Neutral.B1 ReciprocityTheory.Neutral.Bridge.HCFR Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.L2.Host GlobalTheory.HeckeGal GlobalTheory.NormCompat

namespace GlobalTheory.NormCompat

theorem prod_zpow_const {ι B : Type} [CommGroup B] (c : B) (s : Finset ι) (e : ι → ℤ) :
    ∏ i ∈ s, c ^ e i = c ^ (∑ i ∈ s, e i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert j s hj ih => rw [Finset.prod_insert hj, Finset.sum_insert hj, ih, zpow_add]

theorem finite_setOf_valuation_ne_one (F : Type) [Field F] [NumberField F] (x : Fˣ) :
    {v : HeightOneSpectrum (𝓞 F) | v.valuation F (x : F) ≠ 1}.Finite := by
  refine ((HeightOneSpectrum.Support.finite (𝓞 F) (x : F)).union
    (HeightOneSpectrum.Support.finite (𝓞 F) ((x : F)⁻¹))).subset ?_
  intro v hv
  have h0 : v.valuation F (x : F) ≠ 0 := by simp
  rcases lt_or_gt_of_ne hv with h | h
  · right
    show 1 < v.valuation F ((x : F)⁻¹)
    rw [map_inv₀]
    exact (one_lt_inv₀ (zero_lt_iff.2 h0)).2 h
  · left
    exact h

theorem valued_locUnit (F : Type) [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F)) (b : Fˣ) :
    Valued.v ((Units.map (algebraMap F (v.adicCompletion F)).toMonoidHom b : (v.adicCompletion F)ˣ) :
      v.adicCompletion F) = v.valuation F (b : F) := by
  show Valued.v ((b : F) : v.adicCompletion F) = _
  exact HeightOneSpectrum.valuedAdicCompletion_eq_valuation' v _

theorem map_locUnit_eq_zpow {F B : Type} [Field F] [NumberField F] [CommGroup B] (ψ : Ideles F →* B)
    (v : HeightOneSpectrum (𝓞 F)) (hu : ∀ x, IsUnitAt v x → ψ (localIdele F v x) = 1)
    (ϖ : (v.adicCompletion F)ˣ) (hϖ : IsUnifAt v ϖ) (b : Fˣ) :
    ψ (locUnit F v b) = ψ (localIdele F v ϖ) ^ ordF v b := by
  set x : (v.adicCompletion F)ˣ := Units.map (algebraMap F (v.adicCompletion F)).toMonoidHom b with hx
  have hb0 : v.valuation F (b : F) ≠ 0 := by simp
  have hu' : IsUnitAt v (x * ϖ ^ (-ordF v b)) := by
    unfold IsUnitAt
    rw [Units.val_mul, Units.val_zpow_eq_zpow_val, map_mul, map_zpow₀, hx, valued_locUnit, hϖ, ordF, neg_neg,
      ← WithZero.exp_zsmul, ← WithZero.exp_log hb0, ← WithZero.exp_add, WithZero.log_exp]
    simp
  have h := hu _ hu'
  rw [map_mul, map_mul, map_zpow, map_zpow, zpow_neg, mul_inv_eq_one] at h
  rw [locUnit_apply, ← hx]
  exact h

end GlobalTheory.NormCompat

namespace GlobalTheory.NormCompat

theorem under_eq_iff {E K : Type} [Field E] [NumberField E] [Field K] [NumberField K] [Algebra E K]
    (w : HeightOneSpectrum (𝓞 K)) (v : HeightOneSpectrum (𝓞 E)) :
    w.under (𝓞 E) = v ↔ w.asIdeal.comap (algebraMap (𝓞 E) (𝓞 K)) = v.asIdeal := by
  constructor
  · rintro rfl; rfl
  · intro h; exact HeightOneSpectrum.ext h

theorem finite_setOf_under_eq {E K : Type} [Field E] [NumberField E] [Field K] [NumberField K] [Algebra E K]
    (v : HeightOneSpectrum (𝓞 E)) : {w : HeightOneSpectrum (𝓞 K) | w.under (𝓞 E) = v}.Finite := by
  have h0 : Ideal.map (algebraMap (𝓞 E) (𝓞 K)) v.asIdeal ≠ 0 := by
    rw [Ne, Ideal.zero_eq_bot, Ideal.map_eq_bot_iff_of_injective (FaithfulSMul.algebraMap_injective _ _)]
    exact v.ne_bot
  refine (Ideal.finite_factors h0).subset fun w hw => ?_
  simp only [Set.mem_setOf_eq] at hw ⊢
  rw [Ideal.dvd_iff_le, Ideal.map_le_iff_le_comap, ← (under_eq_iff w v).mp hw]

end GlobalTheory.NormCompat

namespace GlobalTheory.NormCompat

theorem prod_locUnit_eq_prod_locUnit_norm : ∀ (E K : Type) [Field E] [NumberField E] [Field K] [NumberField K] [Algebra E K] (B : Type) [CommGroup B] (ψ1 : Ideles K →* B) (ψ2 : Ideles E →* B) (S : Finset (HeightOneSpectrum (𝓞 E))), (∀ v ∉ S, ∀ x, IsUnitAt v x → ψ2 (localIdele E v x) = 1) → (∀ v ∉ S, ∀ w : HeightOneSpectrum (𝓞 K), w.asIdeal.comap (algebraMap (𝓞 E) (𝓞 K)) = v.asIdeal → ∀ x, IsUnitAt w x → ψ1 (localIdele K w x) = 1) → (∀ v ∉ S, ∀ w : HeightOneSpectrum (𝓞 K), w.asIdeal.comap (algebraMap (𝓞 E) (𝓞 K)) = v.asIdeal → ∀ x ϖ, IsUnifAt w x → IsUnifAt v ϖ → ψ1 (localIdele K w x) = ψ2 (localIdele E v ϖ) ^ w.asIdeal.inertiaDeg (𝓞 E)) → ∀ a : Kˣ, ∃ (TK : Finset (HeightOneSpectrum (𝓞 K))) (TE : Finset (HeightOneSpectrum (𝓞 E))), (∀ w ∈ TK, ∀ v ∈ S, w.asIdeal.comap (algebraMap (𝓞 E) (𝓞 K)) ≠ v.asIdeal) ∧ (∀ w ∉ TK, (∀ v ∈ S, w.asIdeal.comap (algebraMap (𝓞 E) (𝓞 K)) ≠ v.asIdeal) → ψ1 (locUnit K w a) = 1) ∧ (∀ v ∈ TE, v ∉ S) ∧ (∀ v ∉ TE, v ∉ S → ψ2 (locUnit E v (Units.map (Algebra.norm E (S := K)) a)) = 1) ∧ ∏ w ∈ TK, ψ1 (locUnit K w a) = ∏ v ∈ TE, ψ2 (locUnit E v (Units.map (Algebra.norm E (S := K)) a)) := by
  classical
  intro E K _ _ _ _ _ B _ ψ1 ψ2 S h2u h1u h1f a
  set Na : Eˣ := Units.map (Algebra.norm E (S := K)) a with hNa
  have hfinE : ((fun w : HeightOneSpectrum (𝓞 K) => w.under (𝓞 E)) ''
      {w | w.valuation K (a : K) ≠ 1} ∪ {v : HeightOneSpectrum (𝓞 E) | v.valuation E (Na : E) ≠ 1}).Finite :=
    ((finite_setOf_valuation_ne_one K a).image _).union (finite_setOf_valuation_ne_one E Na)
  set TE : Finset (HeightOneSpectrum (𝓞 E)) := hfinE.toFinset.filter (· ∉ S) with hTE
  set TK : Finset (HeightOneSpectrum (𝓞 K)) :=
    TE.biUnion (fun v => (finite_setOf_under_eq (K := K) v).toFinset) with hTK
  have memTK : ∀ w, w ∈ TK ↔ w.under (𝓞 E) ∈ TE := by
    intro w
    simp only [hTK, Finset.mem_biUnion, Set.Finite.mem_toFinset, Set.mem_setOf_eq]
    exact ⟨fun ⟨v, hv, h⟩ => h ▸ hv, fun h => ⟨_, h, rfl⟩⟩
  have memTE : ∀ v, v ∈ TE ↔ v ∉ S ∧ ((∃ w : HeightOneSpectrum (𝓞 K), w.valuation K (a : K) ≠ 1 ∧
      w.under (𝓞 E) = v) ∨ v.valuation E (Na : E) ≠ 1) := by
    intro v
    simp only [hTE, Finset.mem_filter, Set.Finite.mem_toFinset, Set.mem_union, Set.mem_image, Set.mem_setOf_eq]
    exact and_comm
  have hcomap : ∀ w : HeightOneSpectrum (𝓞 K),
      w.asIdeal.comap (algebraMap (𝓞 E) (𝓞 K)) = (w.under (𝓞 E)).asIdeal := fun w => rfl
  refine ⟨TK, TE, ?_, ?_, ?_, ?_, ?_⟩
  · intro w hw v hv h
    have := ((memTE _).mp ((memTK w).mp hw)).1
    rw [(under_eq_iff w v).mpr h] at this
    exact this hv
  · intro w hw hS
    have hS' : w.under (𝓞 E) ∉ S := fun h => hS _ h (hcomap w)
    have hval : w.valuation K (a : K) = 1 := by
      by_contra h
      exact hw ((memTK w).mpr ((memTE _).mpr ⟨hS', Or.inl ⟨w, h, rfl⟩⟩))
    rw [locUnit_apply]
    refine h1u _ hS' w (hcomap w) _ ?_
    unfold IsUnitAt
    rw [valued_locUnit, hval]
  · intro v hv
    exact ((memTE v).mp hv).1
  · intro v hv hS
    have hval : v.valuation E (Na : E) = 1 := by
      by_contra h
      exact hv ((memTE v).mpr ⟨hS, Or.inr h⟩)
    rw [locUnit_apply]
    refine h2u v hS _ ?_
    unfold IsUnitAt
    rw [valued_locUnit, hval]
  ·
    set c : HeightOneSpectrum (𝓞 E) → B := fun v => ψ2 (localIdele E v (atFin v (unif v))) with hc
    have hK : ∀ w ∈ TK, ψ1 (locUnit K w a) =
        c (w.under (𝓞 E)) ^ ((w.asIdeal.inertiaDeg (𝓞 E) : ℤ) * ordF w a) := by
      intro w hw
      have hS : w.under (𝓞 E) ∉ S := ((memTE _).mp ((memTK w).mp hw)).1
      rw [map_locUnit_eq_zpow ψ1 w (h1u _ hS w (hcomap w)) _ (unif_spec w),
        h1f _ hS w (hcomap w) _ _ (unif_spec w) (unif_spec _), zpow_mul, zpow_natCast]
    have hE : ∀ v ∈ TE, ψ2 (locUnit E v Na) = c v ^ ordF v Na := by
      intro v hv
      exact map_locUnit_eq_zpow ψ2 v (h2u v ((memTE v).mp hv).1) _ (unif_spec v) Na
    rw [Finset.prod_congr rfl hK, Finset.prod_congr rfl hE,
      ← Finset.prod_fiberwise_of_maps_to (g := fun w : HeightOneSpectrum (𝓞 K) => w.under (𝓞 E))
        (t := TE) (fun w hw => (memTK w).mp hw)]
    refine Finset.prod_congr rfl fun v hv => ?_
    have hfib : ∀ w ∈ TK.filter (fun w => w.under (𝓞 E) = v), c (w.under (𝓞 E)) = c v := by
      intro w hw
      rw [(Finset.mem_filter.mp hw).2]
    rw [Finset.prod_congr rfl fun w hw => by rw [hfib w hw], prod_zpow_const]
    congr 1
    have hs : ∀ w, w ∈ TK.filter (fun w => w.under (𝓞 E) = v) ↔
        w.asIdeal.comap (algebraMap (𝓞 E) (𝓞 K)) = v.asIdeal := by
      intro w
      rw [Finset.mem_filter, ← under_eq_iff]
      constructor
      · exact fun h => h.2
      · intro h
        exact ⟨(memTK w).mpr (h ▸ hv), h⟩
    have key := _root_.GlobalTheory.NormValuation.log_valuation_norm_eq_sum E K v a _ hs
    simp only [ordF, hNa, Units.coe_map, MonoidHom.coe_coe] at key ⊢
    rw [key, ← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun w _ => ?_
    ring

end GlobalTheory.NormCompat

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TransvectionWeightVecExpansion
section
open Matrix GlobalTheory.AlgWtHW

namespace GlobalTheory.UnipotentWeights

noncomputable def tGL {n : ℕ} {i j : Fin n} (h : i ≠ j) (c : ℂ) : GL (Fin n) ℂ :=
  ⟨transvection i j c, transvection i j (-c),
    by rw [transvection_mul_transvection_same i j h]; simp,
    by rw [transvection_mul_transvection_same i j h]; simp⟩

theorem diag_mul_transvection {n : ℕ} {i j : Fin n} (h : i ≠ j) (d : Fin n → ℂ) (hd : ∀ l, d l ≠ 0) (s : ℂ) :
    diagonal d * transvection i j s = transvection i j (s * d i / d j) * diagonal d := by
  ext a b
  simp only [transvection, Matrix.mul_add, Matrix.add_mul, Matrix.mul_one, Matrix.one_mul, Matrix.add_apply,
    diagonal_mul, mul_diagonal, single_apply, one_apply]
  by_cases ha : i = a <;> by_cases hb : j = b
  · subst ha hb; simp [h]; field_simp [hd j]
  · by_cases hab : a = b <;> simp [ha, hb, hab, mul_comm]
  · subst hb; by_cases hab : a = j
    · subst hab; simp [h]
    · simp [ha, hab]
  · by_cases hab : a = b <;> simp [ha, hb, hab, mul_comm]

theorem poly_coeff_eq (K : ℕ) (x y : ℕ → ℂ) (hxy : ∀ s : ℂ, ∑ k ∈ Finset.range (K + 1), s ^ k * x k =
    ∑ k ∈ Finset.range (K + 1), s ^ k * y k) (k : ℕ) (hk : k ≤ K) : x k = y k := by
  let Q : Polynomial ℂ := ∑ k ∈ Finset.range (K + 1), Polynomial.C (x k - y k) * Polynomial.X ^ k
  have hQ : Q = 0 := by
    apply Polynomial.funext
    intro s
    simp only [Q, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow,
      Polynomial.eval_X, Polynomial.eval_zero]
    have := hxy s
    rw [← sub_eq_zero, ← Finset.sum_sub_distrib] at this
    rw [← this]
    refine Finset.sum_congr rfl fun m _ => by ring
  have hc := congrArg (fun p => _root_.AddMonoidAlgebra.coeff (M := ℕ) p k) hQ
  simp only [Q, Polynomial.finsetSum_coeff, Polynomial.coeff_C_mul_X_pow, Polynomial.coeff_zero] at hc
  rw [Finset.sum_eq_single k] at hc
  · simpa [sub_eq_zero] using hc
  · intro m _ hm; simp [Ne.symm hm]
  · intro hk'; exact absurd (Finset.mem_range.2 (Nat.lt_succ_of_le hk)) hk'

end GlobalTheory.UnipotentWeights

namespace GlobalTheory.UnipotentWeights

theorem prod_single_zpow {n : ℕ} (d : Fin n → ℂ) (i : Fin n) :
    ∏ l, d l ^ ((Pi.single i (1 : ℤ) : Fin n → ℤ) l) = d i := by
  rw [Finset.prod_eq_single i]
  · simp
  · intro b _ hb; simp [Pi.single_apply, hb]
  · intro h; exact absurd (Finset.mem_univ i) h

theorem prod_wt_shift {n : ℕ} (d : Fin n → ℂ) (hd : ∀ l, d l ≠ 0) (i j : Fin n) (μ : Fin n → ℤ) (k : ℕ) :
    ∏ l, d l ^ ((μ + (k : ℤ) • (Pi.single i 1 - Pi.single j 1) : Fin n → ℤ) l) =
      (∏ l, d l ^ μ l) * (d i / d j) ^ k := by
  have hpt : ∀ l, d l ^ ((μ + (k : ℤ) • (Pi.single i 1 - Pi.single j 1) : Fin n → ℤ) l) =
      d l ^ μ l * ((d l ^ ((Pi.single i (1 : ℤ) : Fin n → ℤ) l)) ^ k *
        ((d l ^ ((Pi.single j (1 : ℤ) : Fin n → ℤ) l)) ^ k)⁻¹) := by
    intro l
    simp only [Pi.add_apply, Pi.smul_apply, Pi.sub_apply, smul_eq_mul]
    rw [zpow_add₀ (hd l), mul_sub, zpow_sub₀ (hd l), div_eq_mul_inv, ← zpow_natCast, ← zpow_natCast,
      ← _root_.zpow_mul, ← _root_.zpow_mul, mul_comm ((Pi.single i (1:ℤ) : Fin n → ℤ) l), mul_comm ((Pi.single j (1:ℤ) : Fin n → ℤ) l)]
  simp_rw [hpt]
  rw [Finset.prod_mul_distrib, Finset.prod_mul_distrib, Finset.prod_inv_distrib, Finset.prod_pow,
    Finset.prod_pow, prod_single_zpow, prod_single_zpow, div_pow, div_eq_mul_inv]

end GlobalTheory.UnipotentWeights

namespace GlobalTheory


open GlobalTheory.UnipotentWeights in
theorem transvection_weightVec_expansion :
    ∀ (n : ℕ) (ι : Type) [Fintype ι] [DecidableEq ι] (Φ : GL (Fin n) ℂ → Matrix ι ι ℂ), IsPolyRep Φ →
      ∀ (i j : Fin n), i ≠ j → ∀ (μ : Fin n → ℤ) (v : ι → ℂ), IsWtVec Φ μ v →
        ∃ (K : ℕ) (w : ℕ → ι → ℂ), w 0 = v ∧
          (∀ k : ℕ, IsWtVec Φ (μ + (k : ℤ) • (Pi.single i 1 - Pi.single j 1)) (w k)) ∧
          ∀ (s : ℂ) (B : GL (Fin n) ℂ), B.val = transvection i j s →
            Φ B *ᵥ v = ∑ k ∈ Finset.range (K + 1), s ^ k • w k := by
  intro n ι _ _ Φ hΦ i j hij μ v hv
  obtain ⟨P, hP⟩ := polyRep_transvection_entries_poly n ι Φ hΦ i j hij
  let K : ℕ := Finset.univ.sup (fun ab : ι × ι => (P ab.1 ab.2).natDegree)
  have hK : ∀ a b, (P a b).natDegree < K + 1 := fun a b =>
    Nat.lt_succ_of_le (Finset.le_sup (f := fun ab : ι × ι => (P ab.1 ab.2).natDegree) (Finset.mem_univ (a, b)))
  let w : ℕ → ι → ℂ := fun k a => ∑ b, (P a b).coeff k * v b
  have hexp : ∀ (s : ℂ) (B : GL (Fin n) ℂ), B.val = transvection i j s →
      Φ B *ᵥ v = ∑ k ∈ Finset.range (K + 1), s ^ k • w k := by
    intro s B hB
    ext a
    simp only [mulVec, dotProduct, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, w]
    simp_rw [hP s B hB a, Polynomial.eval_eq_sum_range' (hK a _) s, Finset.sum_mul, Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun b _ => by ring
  refine ⟨K, w, ?_, ?_, hexp⟩
  · have h0 := hexp 0 1 (by simp)
    rw [hΦ.one, one_mulVec, Finset.sum_range_succ'] at h0
    simpa using h0.symm
  · intro k D hD
    by_cases hk : K < k
    · have hw : w k = 0 := by
        funext a
        simp only [w, Pi.zero_apply]
        refine Finset.sum_eq_zero fun b _ => ?_
        rw [Polynomial.coeff_eq_zero_of_natDegree_lt (lt_of_lt_of_le (hK a b) hk), zero_mul]
      rw [hw, mulVec_zero, smul_zero]
    push_neg at hk
    set d : Fin n → ℂ := fun l => D.val l l with hd_def
    have hDd : D.val = diagonal d := ((isDiag_iff_diagonal_diag _).1 hD).symm
    have hd : ∀ l, d l ≠ 0 := by
      have hdet : D.val.det ≠ 0 := ((Matrix.isUnit_iff_isUnit_det _).1 D.isUnit).ne_zero
      rw [hDd, det_diagonal, Finset.prod_ne_zero_iff] at hdet
      exact fun l => hdet l (Finset.mem_univ l)
    set lam : ℂ := ∏ l, D.val l l ^ μ l with hlam
    have hcomm : ∀ s : ℂ, D * tGL hij s = tGL hij (s * d i / d j) * D := by
      intro s
      ext1
      simp only [Units.val_mul, tGL]
      rw [hDd]
      exact diag_mul_transvection hij d hd s
    have hmain : ∀ s : ℂ, Φ D *ᵥ (∑ k ∈ Finset.range (K + 1), s ^ k • w k) =
        lam • ∑ k ∈ Finset.range (K + 1), (s * d i / d j) ^ k • w k := by
      intro s
      rw [← hexp s (tGL hij s) rfl, ← hexp _ (tGL hij (s * d i / d j)) rfl, mulVec_mulVec, ← hΦ.mul, hcomm,
        hΦ.mul, ← mulVec_mulVec, hv D hD, mulVec_smul]
    have hcoord : ∀ a, (Φ D *ᵥ w k) a = (lam * (d i / d j) ^ k) * w k a := by
      intro a
      refine poly_coeff_eq K (fun m => (Φ D *ᵥ w m) a) (fun m => (lam * (d i / d j) ^ m) * w m a) ?_ k hk
      intro s
      have := congrFun (hmain s) a
      simp only [Matrix.mulVec_sum, Matrix.mulVec_smul, Finset.sum_apply, Pi.smul_apply, smul_eq_mul,
        Finset.mul_sum] at this
      rw [this]
      refine Finset.sum_congr rfl fun m _ => by ring
    ext a
    rw [hcoord a, Pi.smul_apply, smul_eq_mul, prod_wt_shift d hd i j μ k]

end GlobalTheory
end

