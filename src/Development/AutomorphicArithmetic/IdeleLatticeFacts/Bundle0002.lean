module

public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.HalfIndexLattices.SplitStab
public import Development.WeilBound.ThetaLifts.Reductions.WeilPairs.Bundle0007
public import Development.WeilBound.ThetaLifts.Reductions.WeilPairs.Bundle0008
public import GroundTheory.HeightsAndTheta.Heights.LatticeLemmas.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0822

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.IdeleLatticeFacts.ExistsLocalLatticeOfGlobalLattice
section
open scoped TensorProduct Matrix Topology Kronecker ComplexOrder Classical
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Matrix
open GlobalTheory.WeilM GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open Formalism.IndefR.DatumF MeasureTheory GlobalTheory.FinWeil GlobalTheory.FinLatF GlobalTheory.RealWeilF GlobalTheory.WeilPartsF
open PositivityTheory.ThKW PositivityTheory.ThKW.AutEtaA
open UpperTheory.TP.W

section SlopeTestRemainingChoices

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

private theorem ev_pair (P : HeightOneSpectrum (𝓞 E)) (α : Af F) :
    ev F E P (algebraMap (AF F) (AEF F E) (pairA F 0 α)) =
      GlobalTheory.LFun.complMap rfl (evalV F (P.under (𝓞 F)) α) := by
  rw [ev_alg]
  rfl

private theorem ev_finIdem (P : HeightOneSpectrum (𝓞 E)) : ev F E P (finIdem F E) = 1 := by
  rw [finIdem, ev_pair, map_one, map_one]

private theorem finPart_lift (y : Af F ⊗[F] E) : finPartF F E (PositivityTheory.ThKW.LatB.liftF F E y) = y := by
  induction y using TensorProduct.induction_on with
  | zero => rw [map_zero, map_zero]
  | tmul a t => rfl
  | add x y hx hy => rw [map_add (f := _), map_add (f := _), hx, hy]

private theorem int_mem (P : HeightOneSpectrum (𝓞 E)) (r : 𝓞 E) :
    algebraMap E (P.adicCompletion E) (r : E) ∈ P.adicCompletionIntegers E := by
  exact HeightOneSpectrum.coe_mem_adicCompletionIntegers P r

private theorem exists_lift (P : HeightOneSpectrum (𝓞 E)) (c : P.adicCompletionIntegers E) :
    ∃ a : AEF F E, finPartF F E a ∈ PositivityTheory.ThKW.LatB.hatO (F := F) E ∧ ev F E P a = c := by
  classical
  have hx : ∀ᶠ Q in Filter.cofinite, Pi.single (M := fun Q : HeightOneSpectrum (𝓞 E) => Q.adicCompletion E) P (c : P.adicCompletion E) Q ∈ (Q.adicCompletionIntegers E : Set (Q.adicCompletion E)) := by
    refine Filter.Eventually.of_forall fun Q => ?_
    by_cases h : Q = P
    · subst h
      rw [Pi.single_eq_same]
      exact c.2
    · rw [Pi.single_eq_of_ne h]
      exact zero_mem _
  let x : FiniteAdeleRing (𝓞 E) E := ⟨_, hx⟩
  have hxQ : ∀ Q, x Q ∈ Q.adicCompletionIntegers E := by
    intro Q
    by_cases h : Q = P
    · subst h
      show Pi.single (M := fun Q : HeightOneSpectrum (𝓞 E) => Q.adicCompletion E) Q (c : Q.adicCompletion E) Q ∈ _
      rw [Pi.single_eq_same]
      exact c.2
    · show Pi.single (M := fun Q : HeightOneSpectrum (𝓞 E) => Q.adicCompletion E) P (c : P.adicCompletion E) Q ∈ _
      rw [Pi.single_eq_of_ne h]
      exact zero_mem _
  refine ⟨PositivityTheory.ThKW.LatB.liftF F E ((finAdEquiv F E).symm x), ?_, ?_⟩
  · rw [finPart_lift]
    show _ ∈ GlobalTheory.AdLat.hat1 F (Set.range (algebraMap (𝓞 E) E))
    rw [← GlobalTheory.HeckeSplitGen.integralFiniteAdelesTensor_eq_adelicCompletion_integers]
    refine (mem_int_iff _).2 fun Q => ?_
    rw [RingEquiv.apply_symm_apply]
    exact hxQ Q
  · show evalV E P (finAdEquiv F E (finPartF F E _)) = c
    rw [finPart_lift, RingEquiv.apply_symm_apply]
    show Pi.single (M := fun Q : HeightOneSpectrum (𝓞 E) => Q.adicCompletion E) P (c : P.adicCompletion E) P = c
    rw [Pi.single_eq_same]

end SlopeTestRemainingChoices

section Aux2

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {nS nT : ℕ}

private theorem map_smul_int (P : HeightOneSpectrum (𝓞 E)) (r : 𝓞 E) (M : Matrix (Fin nT) (Fin nS) E) :
    (r • M).map (algebraMap E (P.adicCompletion E)) =
      (⟨algebraMap E (P.adicCompletion E) (r : E), int_mem P r⟩ : P.adicCompletionIntegers E) •
        M.map (algebraMap E (P.adicCompletion E)) := by
  ext i j
  simp only [Matrix.map_apply, Matrix.smul_apply]
  rw [Algebra.smul_def, map_mul]
  rfl

private theorem ev_map_smul (P : HeightOneSpectrum (𝓞 E)) (a : AEF F E) (z : WOF F E nS nT) :
    (a • z).map (ev F E P) = ev F E P a • z.map (ev F E P) := by
  ext i j
  simp only [Matrix.map_apply, Matrix.smul_apply, smul_eq_mul, map_mul]

private theorem ev_ratWF (P : HeightOneSpectrum (𝓞 E)) (γ : Matrix (Fin nT) (Fin nS) E) :
    (ratWF (F := F) γ).map (ev F E P) = γ.map (algebraMap E (P.adicCompletion E)) := by
  refine Matrix.ext fun i j => ?_
  simp only [ratWF, Matrix.map_apply]
  exact ev_inc (F := F) P (γ i j)

private theorem finRat_mem (Λ : Submodule (𝓞 E) (Matrix (Fin nT) (Fin nS) E)) {M : Matrix (Fin nT) (Fin nS) E}
    (hM : M ∈ Λ) : finRatF F M ∈ latF F E nS nT Λ := by
  refine AddSubgroup.subset_closure ⟨1, ?_, M, hM, rfl⟩
  intro v
  rw [map_one]
  exact one_mem _

private theorem ev_finRat (P : HeightOneSpectrum (𝓞 E)) (M : Matrix (Fin nT) (Fin nS) E) :
    ((finRatF F M : XFF F E nS nT) : WOF F E nS nT).map (ev F E P) = M.map (algebraMap E (P.adicCompletion E)) := by
  show (finIdem F E • ratWF (F := F) M).map (ev F E P) = _
  rw [ev_map_smul, ev_finIdem, one_smul, ev_ratWF]

private theorem ev_mem_span (P : HeightOneSpectrum (𝓞 E)) (Λ : Submodule (𝓞 E) (Matrix (Fin nT) (Fin nS) E))
    {z : WOF F E nS nT} (hz : z ∈ latOF F E nS nT Λ) :
    z.map (ev F E P) ∈ Submodule.span (P.adicCompletionIntegers E)
      {X | ∃ M ∈ Λ, X = M.map (algebraMap E (P.adicCompletion E))} := by
  induction hz using AddSubgroup.closure_induction with
  | mem z hz =>
    obtain ⟨α, hα, γ, hγ, rfl⟩ := hz
    rw [ev_map_smul, ev_pair, ev_ratWF]
    have hc : GlobalTheory.LFun.complMap rfl (evalV F (P.under (𝓞 F)) α) ∈ P.adicCompletionIntegers E :=
      GlobalTheory.LFun.complMap_mem rfl (hα _)
    exact Submodule.smul_mem _ (⟨_, hc⟩ : P.adicCompletionIntegers E) (Submodule.subset_span ⟨γ, hγ, rfl⟩)
  | zero =>
    rw [Matrix.map_zero _ (map_zero _)]
    exact zero_mem _
  | add x y _ _ hx hy =>
    rw [Matrix.map_add _ (map_add _)]
    exact add_mem hx hy
  | neg x _ hx =>
    rw [Matrix.map_neg _ (map_neg _)]
    exact neg_mem hx

end Aux2

theorem UpperTheory.exists_local_lattice_of_global_lattice :
    ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {nS nT : ℕ}
        (P : HeightOneSpectrum (𝓞 E)) (Λ : Submodule (𝓞 E) (Matrix (Fin nT) (Fin nS) E)), GoodLat Λ →
        ∃ L : Submodule (P.adicCompletionIntegers E) (Matrix (Fin nT) (Fin nS) (P.adicCompletion E)),
          L.FG ∧ Submodule.span (P.adicCompletion E) (L : Set (Matrix (Fin nT) (Fin nS) (P.adicCompletion E))) = ⊤ ∧
          ∀ v, v ∈ L ↔ ∃ x ∈ latF F E nS nT Λ, (x : WOF F E nS nT).map (ev F E P) = v := by
  intro F E _ _ _ _ _ nS nT P Λ hΛ
  classical
  refine ⟨Submodule.span (P.adicCompletionIntegers E)
    {X | ∃ M ∈ Λ, X = M.map (algebraMap E (P.adicCompletion E))}, ?_, ?_, ?_⟩
  · obtain ⟨G, hG⟩ := hΛ.fg
    refine ⟨G.image (fun M => M.map (algebraMap E (P.adicCompletion E))), ?_⟩
    rw [Finset.coe_image]
    apply le_antisymm
    · rw [Submodule.span_le]
      rintro _ ⟨M, hM, rfl⟩
      have hM' : M ∈ Λ := by
        rw [← hG]
        exact Submodule.subset_span hM
      exact Submodule.subset_span ⟨M, hM', rfl⟩
    · rw [Submodule.span_le]
      rintro _ ⟨M, hM, rfl⟩
      rw [← hG] at hM
      induction hM using Submodule.span_induction with
      | mem x hx => exact Submodule.subset_span ⟨x, hx, rfl⟩
      | zero =>
        rw [Matrix.map_zero _ (map_zero _)]
        exact zero_mem _
      | add x y _ _ hx hy =>
        rw [Matrix.map_add _ (map_add _)]
        exact add_mem hx hy
      | smul r x _ hx =>
        rw [map_smul_int P r x]
        exact Submodule.smul_mem _ _ hx
  · rw [eq_top_iff]
    rintro X -
    rw [Matrix.matrix_eq_sum_single X]
    refine Submodule.sum_mem _ fun i _ => Submodule.sum_mem _ fun j _ => ?_
    obtain ⟨N, hN, hNM⟩ := hΛ.den (Matrix.single i j (1 : E))
    have hN0 : (N : E) ≠ 0 := Nat.cast_ne_zero.2 hN.ne'
    have key : Matrix.single i j (X i j) =
        (X i j * algebraMap E (P.adicCompletion E) (N : E)⁻¹) •
          (N • Matrix.single i j (1 : E)).map (algebraMap E (P.adicCompletion E)) := by
      ext a b
      simp only [Matrix.smul_apply, Matrix.map_apply, Matrix.single_apply, smul_eq_mul]
      split_ifs with h
      · rw [nsmul_eq_mul, mul_one, mul_assoc, ← map_mul, inv_mul_cancel₀ hN0, map_one, mul_one]
      · rw [smul_zero, map_zero, mul_zero]
    rw [key]
    exact Submodule.smul_mem _ _ (Submodule.subset_span (Submodule.subset_span ⟨_, hNM, rfl⟩))
  · intro v
    constructor
    · intro hv
      induction hv using Submodule.span_induction with
      | mem X hX =>
        obtain ⟨M, hM, rfl⟩ := hX
        exact ⟨finRatF F M, finRat_mem Λ hM, ev_finRat P M⟩
      | zero =>
        refine ⟨0, zero_mem _, ?_⟩
        show (0 : WOF F E nS nT).map (ev F E P) = 0
        exact Matrix.map_zero _ (map_zero _)
      | add X Y _ _ hX hY =>
        obtain ⟨x, hx, rfl⟩ := hX
        obtain ⟨y, hy, rfl⟩ := hY
        refine ⟨x + y, add_mem hx hy, ?_⟩
        show ((x : WOF F E nS nT) + (y : WOF F E nS nT)).map (ev F E P) = _
        exact Matrix.map_add _ (map_add _) _ _
      | smul c X _ hX =>
        obtain ⟨x, hx, rfl⟩ := hX
        obtain ⟨a, ha, hac⟩ := exists_lift (F := F) P c
        refine ⟨a • x, PositivityTheory.ThKW.LatB.int_smul_mem ha hx, ?_⟩
        rw [GlobalTheory.FinLatF.XFF.coe_asmul, ev_map_smul, hac]
        rfl
    · rintro ⟨x, hx, rfl⟩
      exact ev_mem_span P Λ hx
end

-- bundled from Development.AutomorphicArithmetic.IdeleLatticeFacts.ExistsPlaceOfSplitIdempotentCmExt
section
open scoped TensorProduct Matrix Topology Kronecker ComplexOrder Classical
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Matrix
open GlobalTheory.WeilM GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open Formalism.IndefR.DatumF MeasureTheory GlobalTheory.FinWeil GlobalTheory.FinLatF GlobalTheory.RealWeilF GlobalTheory.WeilPartsF
open PositivityTheory.ThKW PositivityTheory.ThKW.AutEtaA
open UpperTheory.TP.W

section

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

end

private theorem false_of_three_distinct_primes_over_of_finrank_eq_two {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (h2 : Module.finrank F E = 2) (v : HeightOneSpectrum (𝓞 F)) (P Q R : HeightOneSpectrum (𝓞 E))
    (hP : HeightOneSpectrum.under (𝓞 F) P = v) (hQ : HeightOneSpectrum.under (𝓞 F) Q = v)
    (hR : HeightOneSpectrum.under (𝓞 F) R = v) (hPQ : P ≠ Q) (hPR : P ≠ R) (hQR : Q ≠ R) : False := by
  haveI : FaithfulSMul (𝓞 F) (𝓞 E) := FaithfulSMul.of_field_isFractionRing (𝓞 F) (𝓞 E) F E
  haveI : NoZeroSMulDivisors (𝓞 F) (𝓞 E) := ⟨fun {c x} h => by
    rw [Algebra.smul_def] at h
    rcases mul_eq_zero.mp h with h | h
    · left
      exact (FaithfulSMul.algebraMap_injective (𝓞 F) (𝓞 E)) (by simpa using h)
    · exact Or.inr h⟩
  have hv : v.asIdeal ≠ ⊥ := v.ne_bot
  haveI : v.asIdeal.IsMaximal := v.isMaximal
  have hc := Ideal.card_primesOverFinset_le_finrank (𝓞 E) F E hv
  rw [h2] at hc
  have mem : ∀ W : HeightOneSpectrum (𝓞 E), HeightOneSpectrum.under (𝓞 F) W = v →
      W.asIdeal ∈ IsDedekindDomain.primesOverFinset v.asIdeal (𝓞 E) := by
    intro W hW
    rw [IsDedekindDomain.mem_primesOverFinset_iff hv]
    refine ⟨W.isPrime, ⟨?_⟩⟩
    rw [← hW]
    rfl
  have hsub : ({P.asIdeal, Q.asIdeal, R.asIdeal} : Finset (Ideal (𝓞 E))) ⊆
      IsDedekindDomain.primesOverFinset v.asIdeal (𝓞 E) := by
    intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl | rfl
    exacts [mem P hP, mem Q hQ, mem R hR]
  have h3 := Finset.card_le_card hsub
  have e1 : P.asIdeal ≠ Q.asIdeal := fun h => hPQ (HeightOneSpectrum.ext h)
  have e2 : P.asIdeal ≠ R.asIdeal := fun h => hPR (HeightOneSpectrum.ext h)
  have e3 : Q.asIdeal ≠ R.asIdeal := fun h => hQR (HeightOneSpectrum.ext h)
  rw [Finset.card_insert_of_notMem (by simp [e1, e2]), Finset.card_insert_of_notMem (by simp [e3]),
    Finset.card_singleton] at h3
  omega

private theorem exists_lift_sub_mem_pow_of_mem_wtPart_zero {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (y : AEF F E) (hi : infPartF F E y = 0) (hf : ∀ Q, ev F E Q y = 0) : y = 0 := by
  have hfin : finPartF F E y = 0 := by
    apply (finAdEquiv F E).injective
    rw [map_zero]
    ext Q
    have h := (hf Q).trans (map_zero (evalV E Q)).symm
    first
      | exact h
      | exact congrArg _ h
      | simpa [ev, evalV] using h
  have h1 := GlobalTheory.HeisThetaF.smul_eq_zero_of_infPartF hi
  have h2 := GlobalTheory.HeisThetaF.smul_eq_zero_of_finPartF hfin
  have h3 : pairA F 1 0 + pairA F 0 1 = (1 : AF F) := by
    exact Prod.ext (add_zero _) (zero_add _)
  calc y = (1 : AF F) • y := (one_smul _ _).symm
    _ = 0 := by rw [← h3, add_smul, h1, h2, add_zero]

theorem UpperTheory.exists_place_of_splitIdempotent_cmExt :
    ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E),
        IsCMExt F E σ → ∀ e, IsSplitIdemF σ e →
        ∃ P : HeightOneSpectrum (𝓞 E), ¬ Fx σ P ∧ ev F E P e = 1 ∧ ∀ Q, Q ≠ P → ev F E Q e = 0 := by
  intro F E _ _ _ _ _ σ hcm e he
  obtain ⟨he2, hes, v, η, hη, hsum⟩ := he
  obtain ⟨α, hηα, hαv, hα0⟩ := id hη
  subst hηα
  have hfix : ∀ a : AF F, cAF σ (algebraMap (AF F) (AEF F E) a) = algebraMap (AF F) (AEF F E) a := by
    intro a
    simp [cAF, sigR]
  have hinj : Function.Injective (algebraMap (AF F) (AEF F E)) := by
    intro a b h
    exact Algebra.TensorProduct.includeLeft_injective (S := F) (R := F) (A := AF F) (B := E)
      (algebraMap F E).injective h
  have hs2 : cAF σ e * cAF σ e = cAF σ e := by rw [← map_mul, he2]
  have heη : e * algebraMap (AF F) (AEF F E) (pairA F 0 α) = e := by
    rw [← hsum, mul_add, he2, hes, add_zero]
  have hsη : cAF σ e * algebraMap (AF F) (AEF F E) (pairA F 0 α) = cAF σ e := by
    rw [← hsum, mul_add, mul_comm, hes, zero_add, hs2]
  have evη0 : ∀ Q : HeightOneSpectrum (𝓞 E), HeightOneSpectrum.under (𝓞 F) Q ≠ v →
      ev F E Q (algebraMap (AF F) (AEF F E) (pairA F 0 α)) = 0 := by
    intro Q hQ
    rw [ev_fin, hα0 _ hQ, map_zero]
  have hinfη := GlobalTheory.WeilPartsF.infPartF_placeIdem (E := E) hη
  have hie : infPartF F E e = 0 := by
    rw [← heη, map_mul, hinfη, mul_zero]
  have his : infPartF F E (cAF σ e) = 0 := by
    rw [← hsη, map_mul, hinfη, mul_zero]
  have hne : e ≠ 0 := by
    intro h0
    rw [h0, map_zero, zero_add] at hsum
    have h1 : pairA F 0 α = 0 := hinj (by rw [← hsum, map_zero])
    have h2 : α = 0 := congrArg Prod.snd h1
    rw [h2, map_zero] at hαv
    exact zero_ne_one hαv
  have hnes : cAF σ e ≠ 0 := by
    intro h0
    have h1 : e = algebraMap (AF F) (AEF F E) (pairA F 0 α) := by rw [← hsum, h0, add_zero]
    apply hne
    rw [← h0, h1, hfix, ← h1]
  have hover : ∀ (y : AEF F E) (Q : HeightOneSpectrum (𝓞 E)),
      y * algebraMap (AF F) (AEF F E) (pairA F 0 α) = y → ev F E Q y ≠ 0 →
      HeightOneSpectrum.under (𝓞 F) Q = v := by
    intro y Q hy hQ
    by_contra hv
    apply hQ
    rw [← hy, map_mul, evη0 Q hv, mul_zero]
  have prod0 : ∀ Q : HeightOneSpectrum (𝓞 E), ev F E Q e * ev F E Q (cAF σ e) = 0 := by
    intro Q
    rw [← map_mul, hes, map_zero]
  have idem1 : ∀ Q : HeightOneSpectrum (𝓞 E), ev F E Q e ≠ 0 → ev F E Q e = 1 := by
    intro Q hQ
    have h := congrArg (ev F E Q) he2
    rw [map_mul] at h
    exact mul_left_cancel₀ hQ (h.trans (mul_one _).symm)
  obtain ⟨P, hP⟩ : ∃ P, ev F E P e ≠ 0 := by
    by_contra hall
    push_neg at hall
    exact hne (exists_lift_sub_mem_pow_of_mem_wtPart_zero e hie hall)
  obtain ⟨R, hR⟩ : ∃ R, ev F E R (cAF σ e) ≠ 0 := by
    by_contra hall
    push_neg at hall
    exact hnes (exists_lift_sub_mem_pow_of_mem_wtPart_zero _ his hall)
  have hPv := hover e P heη hP
  have hRv := hover _ R hsη hR
  have hRe : ev F E R e = 0 := by
    rcases mul_eq_zero.mp (prod0 R) with h | h
    · exact h
    · exact absurd h hR
  have hPR : P ≠ R := by
    rintro rfl
    exact hP hRe
  refine ⟨P, ?_, idem1 P hP, ?_⟩
  · intro hfx
    obtain ⟨θ, d, -, -, hd, hσθ, hθθ, hspan, -⟩ := exists_half hcm
    have hsplit : Formalism.MainNotions.SchurIrreducible.IsSplit (E := E) v := by
      refine ⟨P, R, hPR, ?_, ?_⟩
      · rw [← hPv]
        rfl
      · rw [← hRv]
        rfl
    have hsq := sq_of_split hcm hd hσθ hθθ hspan hsplit
    have hnsq := not_sq_of_fx hcm hd hσθ hθθ hspan hfx
    subst hPv
    exact hnsq hsq
  · intro Q hQP
    by_contra hQ
    have hQv := hover e Q heη hQ
    have hQR : Q ≠ R := by
      rintro rfl
      exact hQ hRe
    exact false_of_three_distinct_primes_over_of_finrank_eq_two hcm.2.2.1 v P Q R hPv hQv hRv (Ne.symm hQP) hPR hQR
end

-- bundled from Development.AutomorphicArithmetic.IdeleLatticeFacts.LatticeDeterminantComparisonAtSplitPlace
section
open scoped TensorProduct Matrix Topology Kronecker ComplexOrder Classical
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Matrix
open GlobalTheory.WeilM GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open Formalism.IndefR.DatumF MeasureTheory GlobalTheory.FinWeil GlobalTheory.FinLatF GlobalTheory.RealWeilF GlobalTheory.WeilPartsF
open PositivityTheory.ThKW PositivityTheory.ThKW.AutEtaA
open UpperTheory.TP.W

private theorem relIndex_map_of_injOn {G G' : Type} [AddGroup G] [AddGroup G'] (f : G →+ G') (R H K : AddSubgroup G)
    (hH : H ≤ R) (hK : K ≤ R) (hf : ∀ x ∈ R, f x = 0 → x = 0) :
    (H.map f).relIndex (K.map f) = H.relIndex K := by
  have hinj : Function.Injective (f.comp R.subtype) := by
    set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
    intro x hx
    exact Subtype.ext (hf x x.2 hx)
  have h1 := AddSubgroup.relIndex_map_map_of_injective (H.addSubgroupOf R) (K.addSubgroupOf R) hinj
  have h2 := AddSubgroup.relIndex_map_map_of_injective (H.addSubgroupOf R) (K.addSubgroupOf R) R.subtype_injective
  rw [AddSubgroup.map_addSubgroupOf_eq_of_le hH, AddSubgroup.map_addSubgroupOf_eq_of_le hK] at h2
  rw [← AddSubgroup.map_map, ← AddSubgroup.map_map, AddSubgroup.map_addSubgroupOf_eq_of_le hH,
    AddSubgroup.map_addSubgroupOf_eq_of_le hK] at h1
  exact h1.trans h2.symm

theorem UpperTheory.lattice_determinant_comparison_at_split_place :
    ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) {nS nT : ℕ}
        (JS : Matrix (Fin nS) (Fin nS) E) (JT : Matrix (Fin nT) (Fin nT) E) (e : AEF F E), e * e = e →
        ∀ (P : HeightOneSpectrum (𝓞 E)), ev F E P e = 1 → (∀ a : AEF F E, e * a = a → ev F E P a = 0 → a = 0) →
        ∀ (Λ : Submodule (𝓞 E) (Matrix (Fin nT) (Fin nS) E))
          (L : Submodule (P.adicCompletionIntegers E) (Matrix (Fin nT) (Fin nS) (P.adicCompletion E))),
          (∀ v, v ∈ L ↔ ∃ x ∈ latF F E nS nT Λ, (x : WOF F E nS nT).map (ev F E P) = v) →
        ∀ (g : GAF σ JS) (h : GAF σ JT)
          (T : Matrix (Fin nT) (Fin nS) (P.adicCompletion E) →ₗ[P.adicCompletion E] Matrix (Fin nT) (Fin nS) (P.adicCompletion E)),
          (∀ u, T u = (mtF σ JT h).map (ev F E P) * u * (mtF σ JS g⁻¹).map (ev F E P)) →
          idx ((latF F E nS nT Λ).map (mulFF e)) (((latF F E nS nT Λ).map (rhoFF σ JS JT (g, h))).map (mulFF e)) =
            idx L (L.map (T.restrictScalars (P.adicCompletionIntegers E))) ∧
          idx (((latF F E nS nT Λ).map (rhoFF σ JS JT (g, h))).map (mulFF e)) ((latF F E nS nT Λ).map (mulFF e)) =
            idx (L.map (T.restrictScalars (P.adicCompletionIntegers E))) L := by
  intro F E _ _ _ _ _ σ nS nT JS JT e he P hev hinj Λ L hL g h T hT
  let φ : XFF F E nS nT →+ Matrix (Fin nT) (Fin nS) (P.adicCompletion E) :=
    AddMonoidHom.mk' (fun x => (x : WOF F E nS nT).map (ev F E P)) (fun x y => by
      rw [XFF.coe_add]
      ext i j
      simp [Matrix.map_apply, map_add (f := _)])
  have hφ : ∀ x, φ x = (x : WOF F E nS nT).map (ev F E P) := fun _ => rfl
  have hφe : ∀ x, φ (mulFF e x) = φ x := by
    intro x
    rw [hφ, hφ, coe_mulFF]
    ext i j
    simp [Matrix.map_apply, Matrix.smul_apply, map_mul, hev]
  have hφr : ∀ x, φ (rhoFF σ JS JT (g, h) x) = T (φ x) := by
    intro x
    rw [hT, hφ, hφ, coe_rhoFF]
    show ((mtF σ JT h * (x : WOF F E nS nT)) * mtF σ JS g⁻¹).map (ev F E P) = _
    rw [Matrix.map_mul, Matrix.map_mul]
  let R : AddSubgroup (XFF F E nS nT) :=
    (LinearMap.range (mulFF e : XFF F E nS nT →ₗ[𝓞 E] XFF F E nS nT)).toAddSubgroup
  have hR : ∀ x ∈ R, φ x = 0 → x = 0 := by
    rintro _ ⟨y, rfl⟩ h0
    apply XFF.ext
    rw [XFF.coe_zero]
    ext i j
    apply hinj
    · rw [coe_mulFF]
      simp [Matrix.smul_apply, ← mul_assoc, he]
    · exact congrFun (congrFun h0 i) j
  have hmapA : ((latF F E nS nT Λ).map (mulFF e)).toAddSubgroup.map φ = L.toAddSubgroup := by
    ext v
    simp only [AddSubgroup.mem_map, Submodule.mem_toAddSubgroup, Submodule.mem_map]
    rw [hL]
    constructor
    · rintro ⟨_, ⟨x, hx, rfl⟩, rfl⟩
      exact ⟨x, hx, (hφe x).symm⟩
    · rintro ⟨x, hx, rfl⟩
      exact ⟨_, ⟨x, hx, rfl⟩, hφe x⟩
  have hmapB : (((latF F E nS nT Λ).map (rhoFF σ JS JT (g, h))).map (mulFF e)).toAddSubgroup.map φ =
      (L.map (T.restrictScalars (P.adicCompletionIntegers E))).toAddSubgroup := by
    ext v
    simp only [AddSubgroup.mem_map, Submodule.mem_toAddSubgroup, Submodule.mem_map]
    constructor
    · rintro ⟨_, ⟨_, ⟨x, hx, rfl⟩, rfl⟩, rfl⟩
      refine ⟨φ x, (hL _).2 ⟨x, hx, rfl⟩, ?_⟩
      show T (φ x) = _
      rw [hφe, hφr]
    · rintro ⟨_, hu, rfl⟩
      obtain ⟨x, hx, rfl⟩ := (hL _).1 hu
      refine ⟨_, ⟨_, ⟨x, hx, rfl⟩, rfl⟩, ?_⟩
      exact (hφe _).trans (hφr x)
  have hleA : ((latF F E nS nT Λ).map (mulFF e)).toAddSubgroup ≤ R := by
    rintro _ ⟨x, _, rfl⟩
    exact ⟨x, rfl⟩
  have hleB : (((latF F E nS nT Λ).map (rhoFF σ JS JT (g, h))).map (mulFF e)).toAddSubgroup ≤ R := by
    rintro _ ⟨x, _, rfl⟩
    exact ⟨x, rfl⟩
  constructor
  · unfold idx
    rw [← hmapA, ← hmapB]
    exact (relIndex_map_of_injOn φ R _ _ hleA hleB hR).symm
  · unfold idx
    rw [← hmapA, ← hmapB]
    exact (relIndex_map_of_injOn φ R _ _ hleB hleA hR).symm
end

