module

public import Formalism.SharpRestriction.GrowthBounds.HermitianTensor.MemInvariantSectionsIffIntegral
public import Formalism.SharpRestriction.GrowthBounds.HermitianTensor.Bundle0005
public import Formalism.SharpRestriction.GrowthBounds.HermitianTensor.Bundle0003

@[expose] public section

-- bundled from Formalism.SharpRestriction.GrowthBounds.HermitianTensor.CloudA
section
noncomputable section

namespace Formalism.MainNotions.flipOneThree.Pf

open Formalism.MainNotions.G Formalism.MainNotions.flipOneThree Formalism.CountingSumsFrames Formalism.GradedWeylDivisibility MvPolynomial Formalism.MainNotions.G.LatticeSystems

theorem cloudOne_of (h : ContractionStandardLattice) : CloudOne := by
  intro p n' R mm hmm a ccl P Q lam hlam h0 hl hmid h8
  obtain ⟨abelian₂, hK, hE, hI, nb, s, s', ka, hnb, hka, hs, hs', h24⟩ := h p n' R mm hmm a ccl P Q lam hlam h0 hl hmid h8
  have := R.std.1.frac_O
  have hinj : Function.Injective (algebraMap R.O R.Kf) := IsFractionRing.injective R.O R.Kf
  have hm1 : 1 ≤ mm + 1 := by omega
  have hloA : Antitone (lam - wtPQ (mm + 1) P Q) := caLo_anti mm ccl P Q lam hlam h0 hl hmid
  have hloA' : Antitone (dualWt (lam - wtPQ (mm + 1) P Q)) := cc_dualWt_anti _ hloA
  have hmuA : Antitone (wtPQ (mm + 1) P Q) := wtPQ_anti _ _ _ hm1
  have hmpA : Antitone (wtPQ (mm + 1) (P + 2 * ccl) (Q + 2 * ccl)) := wtPQ_anti _ _ _ hm1
  have hzeA : Antitone (wtPQ (mm + 1) (2 * ccl) (2 * ccl)) := wtPQ_anti _ _ _ hm1
  have hlo0 : (lam - wtPQ (mm + 1) P Q) 0 = (ccl : ℤ) := by
    rw [lo_val mm ccl P Q lam h0 hl, ite_eq_left rfl]
  have hloL : (lam - wtPQ (mm + 1) P Q) (Fin.last (mm + 1)) = -(ccl : ℤ) := by
    rw [lo_val mm ccl P Q lam h0 hl, ite_eq_right (caLast_ne_zero mm), ite_eq_left rfl]
  have hloL' : dualWt (lam - wtPQ (mm + 1) P Q) (Fin.last (mm + 1)) = -(ccl : ℤ) := by
    unfold dualWt
    rw [Fin.rev_last, hlo0]
  refine ⟨abelian₂, hK, ?_, ?_⟩
  · rintro Λ ⟨g, hg, rfl⟩ v hv t ht
    rw [mem_invariant_sections_iff_integral hinj _ _ hmpA g hg]
    have hv0 := (mem_invariant_sections_iff_integral hinj _ lam hlam g hg v).1 hv
    have ht0 := (mem_invariant_sections_iff_integral hinj _ _ hloA' g hg t).1 ht
    have hvK : v ∈ dualWeyl R.Kf (mm + 1 + 1) (mm + 1 + 1) (nuOf lam) :=
      la_nablaLTw_le _ lam g hg v (H0_le_twisted_nabla _ lam hlam g hg hv)
    have htK : t ∈ dualWeyl R.Kf (mm + 1 + 1) (mm + 1 + 1) (nuOf (dualWt (lam - wtPQ (mm + 1) P Q))) :=
      la_nablaLTw_le _ _ g hg t (H0_le_twisted_nabla _ _ hloA' g hg ht)
    have h3 := hI _ hv0 _ ht0
    rw [map_smul, map_smul, smul_mul_smul_comm, map_smul, hE g hg v hvK t htK, ← zpow_add₀ hg.ne_zero] at h3
    have he : lam (Fin.last (mm + 1)) + dualWt (lam - wtPQ (mm + 1) P Q) (Fin.last (mm + 1)) =
        wtPQ (mm + 1) (P + 2 * ccl) (Q + 2 * ccl) (Fin.last (mm + 1)) := by
      rw [hl, hloL', wtPQ_last]
      push_cast
      ring
    rwa [he] at h3
  · intro g hg
    have hgi : IsUnit (g⁻¹).det := Matrix.isUnit_nonsing_inv_det g hg
    refine ⟨nb, g.det ^ (2 * ccl) • rowAct R.Kf g⁻¹ (hw R.Kf (le_refl (mm + 1 + 1)) (nuOf (wtPQ (mm + 1) (2 * ccl) (2 * ccl)))),
      fun b => g.det ^ ccl • rowAct R.Kf g⁻¹ (s b), fun a' => g.det ^ ccl • rowAct R.Kf g⁻¹ (s' a'), ka, hnb, hka, ?_, ?_⟩
    · intro a' b F hF
      have hF0 : rowAct R.Kf g F ∈ dualWeyl R.Kf (mm + 1 + 1) (mm + 1 + 1) (nuOf (wtPQ (mm + 1) P Q)) :=
        dualWeylRowStable R.Kf _ _ _ g F hF
      have e1 : F * (g.det ^ ccl • rowAct R.Kf g⁻¹ (s b)) = g.det ^ ccl • rowAct R.Kf g⁻¹ (rowAct R.Kf g F * s b) := by
        rw [map_mul, rowAct_cancel_inv g hg, mul_smul_comm]
      have hsK := intO_le (O := R.O) _ _ _ (hs b).1
      have hsK' := intO_le (O := R.O) _ _ _ (hs' a').1
      have hv : rowAct R.Kf g F * s b ∈ dualWeyl R.Kf (mm + 1 + 1) (mm + 1 + 1) (nuOf lam) := by
        have h4 := dualWeyl_mul R.Kf _ _ _ _ hF0 hsK
        rw [← nuOf_add _ _ hmuA hloA] at h4
        have e : wtPQ (mm + 1) P Q + (lam - wtPQ (mm + 1) P Q) = lam := by abel
        rwa [e] at h4
      show abelian₂ (blockEmb R.Kf true (F * (g.det ^ ccl • rowAct R.Kf g⁻¹ (s b))) *
        blockEmb R.Kf false (g.det ^ ccl • rowAct R.Kf g⁻¹ (s' a'))) = _
      rw [e1, map_smul, map_smul, smul_mul_smul_comm, map_smul, hE g⁻¹ hgi _ hv _ hsK', h24 a' b _ hF0]
      split_ifs
      · rw [map_smul, map_mul, rowAct_cancel_inv g hg, smul_smul, smul_mul_assoc, smul_smul]
        congr 1
        ring
      · rw [map_zero, smul_zero]
    · intro c hc
      have hgD : IsUnit (g * lb_D (mm + 1 + 1) 1 c).det := by
        rw [Matrix.det_mul]
        exact hg.mul (lb_D_det _ 1 c hc)
      have hzR : Row0 (hw R.Kf (le_refl (mm + 1 + 1)) (nuOf (wtPQ (mm + 1) (2 * ccl) (2 * ccl)))) (2 * ccl + 2 * ccl) := by
        have h5 := highest_weight_first_entry (K := R.Kf) (mm + 1) _ (nuOf_anti _ hzeA)
        have h6 : nuOf (wtPQ (mm + 1) (2 * ccl) (2 * ccl)) 0 = 2 * ccl + 2 * ccl := by
          unfold nuOf
          rw [wtPQ_zero, wtPQ_last]
          omega
        rwa [h6] at h5
      have hcz := core_id g hg c hc (2 * ccl) (2 * ccl) _ hzR
      refine ⟨?_, ?_, ?_, ?_⟩
      · rw [mem_invariant_sections_iff_integral hinj _ _ hzeA _ hgD, wtPQ_last, hcz]
        exact hw_int _ _ (nuOf_anti _ hzeA)
      · rintro ⟨z', hz', he⟩
        have h7 := (mem_invariant_sections_iff_integral hinj _ _ hzeA _ hgD z').1 hz'
        rw [wtPQ_last] at h7
        apply hw_prim (O := R.O) (K := R.Kf) hinj R.w R.w_mem (mm + 1 + 1) (nuOf (wtPQ (mm + 1) (2 * ccl) (2 * ccl)))
        refine ⟨_, h7, ?_⟩
        rw [← hcz, he, smulO_eq R.w z', map_smul, smulO_eq R.w, smul_comm]
      · intro b
        have hR : Row0 (s b) (ccl + ccl) := by rw [← two_mul]; exact (hs b).2
        rw [mem_invariant_sections_iff_integral hinj _ _ hloA _ hgD, hloL, core_id g hg c hc ccl ccl _ hR]
        exact (hs b).1
      · intro a'
        have hR : Row0 (s' a') (ccl + ccl) := by rw [← two_mul]; exact (hs' a').2
        rw [mem_invariant_sections_iff_integral hinj _ _ hloA' _ hgD, hloL', core_id g hg c hc ccl ccl _ hR]
        exact (hs' a').1

end Formalism.MainNotions.flipOneThree.Pf

end
end

-- bundled from Formalism.SharpRestriction.GrowthBounds.HermitianTensor.PdAevalScale
section
noncomputable section

namespace Formalism.MainNotions.flipOneThree.Pf

open Formalism.MainNotions.G Formalism.MainNotions.flipOneThree Formalism.CountingSumsFrames Formalism.GradedWeylDivisibility MvPolynomial

variable (A : Type) [CommRing A] (r : ℕ)

theorem detY_eq : detY A r = (genY A r).det := rfl

end Formalism.MainNotions.flipOneThree.Pf

end
end

-- bundled from Formalism.SharpRestriction.GrowthBounds.HermitianTensor.TaIntOfRename
section
noncomputable section

namespace Formalism.MainNotions.flipOneThree.Pf

open Formalism.MainNotions.G Formalism.MainNotions.flipOneThree Formalism.CountingSumsFrames Formalism.CountingSumsFrames.Har4 Formalism.GradedWeylDivisibility MvPolynomial Formalism.MainNotions.G.LatticeSystems

def ta_covR (A : Type) [CommRing A] (m : ℕ) (i : Fin (m + 1)) : MvPolynomial (Fin (m + 1) × Fin (m + 1)) A :=
  (-1) ^ (i : ℕ) * Matrix.det (fun a b : Fin m => (X (i.succAbove a, b.castSucc) : MvPolynomial (Fin (m + 1) × Fin (m + 1)) A))

theorem ta_covR_map {A B : Type} [CommRing A] [CommRing B] (φ : A →+* B) (m : ℕ) (i : Fin (m + 1)) :
    map φ (ta_covR A m i) = ta_covR B m i := by
  unfold ta_covR
  rw [map_mul, map_pow, map_neg, map_one]
  congr 1
  exact (RingHom.map_det (map φ) (Matrix.of fun a b : Fin m =>
    (X (i.succAbove a, b.castSucc) : MvPolynomial (Fin (m + 1) × Fin (m + 1)) A))).trans (by
      congr 1
      ext a b
      simp)

theorem ta_covR_eq (K : Type) [Field K] (m : ℕ) : ta_covR K m = covY K m := rfl

theorem ta_aeval_map {A B : Type} [CommRing A] [CommRing B] (φ : A →+* B) (m : ℕ) (β : MvPolynomial (Fin (m + 1)) A) :
    map φ (aeval (ta_covR A m) β) = aeval (ta_covR B m) (map φ β) := by
  induction β using MvPolynomial.induction_on with
  | C a => simp [MvPolynomial.algebraMap_eq]
  | add p q hp hq => simp only [map_add (f := _), hp, hq]
  | mul_X p n hp => simp only [map_mul, hp, map_X, aeval_X, ta_covR_map]

section Int

variable {O K : Type} [CommRing O] [Field K] [Algebra O K]

def ta_Int (O : Type) {K : Type} [CommRing O] [Field K] [Algebra O K] {σ : Type} (F : MvPolynomial σ K) : Prop :=
  ∃ β : MvPolynomial σ O, map (algebraMap O K) β = F

theorem ta_Int_coeff {σ : Type} {F : MvPolynomial σ K} (h : ta_Int O F) (u : σ →₀ ℕ) :
    AddMonoidAlgebra.coeff F u ∈ Set.range (algebraMap O K) := by
  obtain ⟨β, rfl⟩ := h
  exact ⟨AddMonoidAlgebra.coeff β u, (coeff_map _ _ _).symm⟩

theorem ta_Int_of_coeff {σ : Type} {F : MvPolynomial σ K} (h : ∀ u, AddMonoidAlgebra.coeff F u ∈ Set.range (algebraMap O K)) :
    ta_Int O F := by
  classical
  choose c hc using h
  refine ⟨∑ u ∈ F.support, monomial u (c u), ?_⟩
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [map_sum, map_monomial, hc]
  exact F.support_sum_monomial_coeff

theorem ta_Int_add {σ : Type} {F G : MvPolynomial σ K} (h1 : ta_Int O F) (h2 : ta_Int O G) : ta_Int O (F + G) := by
  obtain ⟨a, rfl⟩ := h1
  obtain ⟨b, rfl⟩ := h2
  exact ⟨a + b, map_add _ _ _⟩

theorem ta_Int_mul {σ : Type} {F G : MvPolynomial σ K} (h1 : ta_Int O F) (h2 : ta_Int O G) : ta_Int O (F * G) := by
  obtain ⟨a, rfl⟩ := h1
  obtain ⟨b, rfl⟩ := h2
  exact ⟨a * b, map_mul _ _ _⟩

theorem ta_Int_smul {σ : Type} {F : MvPolynomial σ K} (c : O) (h : ta_Int O F) : ta_Int O (algebraMap O K c • F) := by
  obtain ⟨a, rfl⟩ := h
  exact ⟨C c * a, by rw [map_mul, map_C, smul_eq_C_mul]⟩

theorem ta_Int_rename {σ τ : Type} (e : σ → τ) {F : MvPolynomial σ K} (h : ta_Int O F) : ta_Int O (rename e F) := by
  obtain ⟨a, rfl⟩ := h
  exact ⟨rename e a, map_rename _ _ _⟩

theorem ta_Int_of_rename {σ τ : Type} (e : σ → τ) (he : Function.Injective e) {F : MvPolynomial σ K}
    (h : ta_Int O (rename e F)) : ta_Int O F := by
  refine ta_Int_of_coeff fun u => ?_
  rw [← coeff_rename_mapDomain e he]
  exact ta_Int_coeff h _

theorem ta_Int_prodX {k : ℕ} (a : Fin k → ℕ) : ta_Int O (∏ i, X i ^ a i : MvPolynomial (Fin k) K) :=
  ⟨∏ i, X i ^ a i, by simp [map_prod]⟩

theorem ta_Int_aeval (m : ℕ) {b : MvPolynomial (Fin (m + 1)) K} (h : ta_Int O b) : ta_Int O (aeval (covY K m) b) := by
  obtain ⟨β, rfl⟩ := h
  exact ⟨aeval (ta_covR O m) β, by rw [ta_aeval_map, ta_covR_eq]⟩

end Int

section Sat

variable {O K : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field K] [Algebra O K] [IsFractionRing O K]

theorem ta_exists_pow (w : O) (hw : Irreducible w) {σ : Type} (b : MvPolynomial σ K) :
    ∃ n : ℕ, ta_Int O ((algebraMap O K w ^ n) • b) := by
  classical
  obtain ⟨⟨s, hs⟩, hsI⟩ := IsLocalization.exist_integer_multiples_of_finset (nonZeroDivisors O)
    (b.support.image fun u => AddMonoidAlgebra.coeff b u)
  have hs0 : s ≠ 0 := nonZeroDivisors.ne_zero hs
  obtain ⟨n, v, hv⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hs0 hw
  refine ⟨n, ta_Int_of_coeff fun u => ?_⟩
  rw [coeff_smul, smul_eq_mul]
  by_cases hu : u ∈ b.support
  · obtain ⟨r, hr⟩ := hsI _ (Finset.mem_image_of_mem _ hu)
    refine ⟨(↑v⁻¹ : O) * r, ?_⟩
    have hr' : algebraMap O K r = algebraMap O K s * AddMonoidAlgebra.coeff b u := by
      rw [hr]
      exact Algebra.smul_def _ _
    rw [map_mul, hr', hv, map_mul, map_pow, ← mul_assoc, ← mul_assoc, ← map_mul, Units.inv_mul, map_one, one_mul]
  · rw [mem_support_iff, not_not] at hu
    exact ⟨0, by rw [hu, mul_zero, map_zero]⟩

theorem ta_sat (w : O) (hw : Irreducible w) (m : ℕ) (hm : 1 ≤ m) (b : MvPolynomial (Fin (m + 1)) K)
    (h : ta_Int O (aeval (covY K m) b)) : ta_Int O b := by
  classical
  have hw0 : w ≠ 0 := hw.ne_zero
  have hinjOK : Function.Injective (algebraMap O K) := IsFractionRing.injective O K
  have hW0 : algebraMap O K w ≠ 0 := fun h0 => hw0 (hinjOK (by rw [h0, map_zero]))
  obtain ⟨γ, hγ⟩ := h
  haveI hmax : (Ideal.span {w}).IsMaximal := PrincipalIdealRing.isMaximal_of_irreducible hw
  letI : Field (O ⧸ Ideal.span {w}) := Ideal.Quotient.field _
  have hind : Function.Injective (aeval (R := O ⧸ Ideal.span {w}) (covY (O ⧸ Ideal.span {w}) m)) := by
    have := Formalism.MainNotions.flipOneThree.Pf.ShapeCovering.signed_minors_alg_independent (O ⧸ Ideal.span {w}) m hm
    rw [covY_eq] at this
    exact this
  have step : ∀ n : ℕ, ta_Int O (algebraMap O K w ^ (n + 1) • b) → ta_Int O (algebraMap O K w ^ n • b) := by
    intro n hn
    obtain ⟨β, hβ⟩ := hn
    have e1 : map (algebraMap O K) (aeval (ta_covR O m) β) = map (algebraMap O K) (C (w ^ (n + 1)) * γ) := by
      rw [ta_aeval_map, ta_covR_eq, hβ, map_smul, map_mul, map_C, hγ, smul_eq_C_mul]
      simp only [map_pow]
    have e2 := map_injective _ hinjOK e1
    have e3 : aeval (R := O ⧸ Ideal.span {w}) (covY (O ⧸ Ideal.span {w}) m)
        (map (Ideal.Quotient.mk (Ideal.span {w})) β) = 0 := by
      rw [← ta_covR_eq, ← ta_aeval_map, e2, map_mul, map_C, map_pow,
        Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_span_singleton_self w), zero_pow (Nat.succ_ne_zero n),
        C_0, zero_mul]
    have e4 : map (Ideal.Quotient.mk (Ideal.span {w})) β = 0 := hind (by rw [e3, map_zero])
    apply ta_Int_of_coeff
    intro u
    have hu : AddMonoidAlgebra.coeff β u ∈ Ideal.span {w} := by
      rw [← Ideal.Quotient.eq_zero_iff_mem]
      have := congrArg (AddMonoidAlgebra.coeff · u) e4
      rwa [coeff_map, AddMonoidAlgebra.coeff_zero, Finsupp.zero_apply] at this
    obtain ⟨c, hc⟩ := Ideal.mem_span_singleton'.mp hu
    refine ⟨c, ?_⟩
    have e5 := congrArg (AddMonoidAlgebra.coeff · u) hβ
    rw [coeff_map, ← hc, map_mul, coeff_smul, smul_eq_mul] at e5
    rw [coeff_smul, smul_eq_mul]
    apply mul_right_cancel₀ hW0
    rw [e5]
    ring
  obtain ⟨n, hn⟩ := ta_exists_pow w hw b
  induction n with
  | zero => simpa using hn
  | succ n ih => exact ih (step n hn)

end Sat

section Act

variable {K : Type} [Field K] {m : ℕ}

theorem ta_Psi_gl_alt (g' : GL (Fin (m + 1)) K) (a : MvPolynomial (Fin (m + 1)) K) :
    PsiXY K m (glAct g' (rename Sum.inl a)) =
      blockEmb K true (rowAct K (g' : Matrix (Fin (m + 1)) (Fin (m + 1)) K) (rename (fun i => (i, (0 : Fin (m + 1)))) a)) := by
  have key : (PsiXY K m).comp ((Formalism.CountingSumsFrames.glAct g').comp (rename Sum.inl)) =
      (blockEmb K true).comp ((rowAct K (g' : Matrix (Fin (m + 1)) (Fin (m + 1)) K)).comp
        (rename fun i => (i, (0 : Fin (m + 1))))) := by
    apply MvPolynomial.algHom_ext
    intro i
    simp [PsiXY, Formalism.CountingSumsFrames.glAct, blockEmb, rowAct, algebraMap_eq]
  exact DFunLike.congr_fun key a

theorem ta_Psi_gl_y (g : Matrix (Fin (m + 1)) (Fin (m + 1)) K) (hg : IsUnit g.det) (g' : GL (Fin (m + 1)) K)
    (hg' : (g' : Matrix (Fin (m + 1)) (Fin (m + 1)) K) = g⁻¹) (b : MvPolynomial (Fin (m + 1)) K) :
    PsiXY K m (glAct g' (rename Sum.inr b)) =
      blockEmb K false (aeval (fun i => C g.det * rowAct K g⁻¹ (covY K m i)) b) := by
  have hinv : IsUnit (g⁻¹).det := Matrix.isUnit_nonsing_inv_det g hg
  have hd0 : g.det ≠ 0 := hg.ne_zero
  have key : (PsiXY K m).comp ((Formalism.CountingSumsFrames.glAct g').comp (rename Sum.inr)) =
      (blockEmb K false).comp (aeval fun i => C g.det * rowAct K g⁻¹ (covY K m i)) := by
    apply MvPolynomial.algHom_ext
    intro i
    have h5 := Formalism.MainNotions.flipOneThree.Pf.ShapeCovering.signed_minors_cofactor_transform K m g⁻¹ i hinv
    rw [covY_eq] at h5
    have hgg : ((g'⁻¹ : GL (Fin (m + 1)) K) : Matrix (Fin (m + 1)) (Fin (m + 1)) K) = g := by
      rw [Matrix.coe_units_inv, hg', Matrix.nonsing_inv_nonsing_inv g hg]
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [AlgHom.comp_apply, rename_X, aeval_X, Formalism.CountingSumsFrames.glAct, Sum.elim_inr, map_sum, map_mul, hgg]
    set_option synthInstance.maxHeartbeats 100000 in
      rw [h5, ← map_mul, ← mul_assoc, ← C_mul, Matrix.nonsing_inv_nonsing_inv g hg, Matrix.det_nonsing_inv,
      Ring.inverse_eq_inv', mul_inv_cancel₀ hd0, C_1, one_mul, map_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [map_mul]
    unfold PsiXY blockEmb
    rw [aeval_C, aeval_X, Sum.elim_inr, rename_C, algebraMap_eq]
  exact DFunLike.congr_fun key b

theorem ta_aeval_scale {τ : Type} {k Q : ℕ} (d : K) (z : Fin k → MvPolynomial τ K) (b : MvPolynomial (Fin k) K)
    (hb : b.IsHomogeneous Q) : aeval (fun i => C d * z i) b = d ^ Q • aeval z b := by
  classical
  conv_lhs => rw [b.as_sum]
  conv_rhs => rw [b.as_sum]
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [map_sum, Finset.smul_sum]
  refine Finset.sum_congr rfl fun u hu => ?_
  have hdeg := hb (mem_support_iff.mp hu)
  simp only [aeval_monomial, Finsupp.prod, mul_pow, Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum]
  rw [smul_eq_C_mul, ← map_pow]
  have hQ : ∑ i ∈ u.support, u i = Q := by
    rw [← hdeg]
    simp [Finsupp.weight_apply, Finsupp.sum]
  rw [hQ]
  ring

theorem ta_aeval_rowAct (h : Matrix (Fin (m + 1)) (Fin (m + 1)) K) (b : MvPolynomial (Fin (m + 1)) K) :
    aeval (fun i => rowAct K h (covY K m i)) b = rowAct K h (aeval (covY K m) b) := by
  exact (DFunLike.congr_fun (comp_aeval (covY K m) (rowAct K h)) b).symm

theorem ta_Psi_gl (g : Matrix (Fin (m + 1)) (Fin (m + 1)) K) (hg : IsUnit g.det) (g' : GL (Fin (m + 1)) K)
    (hg' : (g' : Matrix (Fin (m + 1)) (Fin (m + 1)) K) = g⁻¹) (Q : ℕ) (a b : MvPolynomial (Fin (m + 1)) K)
    (hb : b.IsHomogeneous Q) :
    PsiXY K m (glAct g' (rename Sum.inl a * rename Sum.inr b)) =
      blockEmb K true (rowAct K g⁻¹ (rename (fun i => (i, (0 : Fin (m + 1)))) a)) *
        blockEmb K false (g.det ^ Q • rowAct K g⁻¹ (aeval (covY K m) b)) := by
  rw [map_mul, map_mul, ta_Psi_gl_alt, ta_Psi_gl_y g hg g' hg', hg', ta_aeval_scale g.det _ b hb, ta_aeval_rowAct]

end Act

end Formalism.MainNotions.flipOneThree.Pf

end
end

