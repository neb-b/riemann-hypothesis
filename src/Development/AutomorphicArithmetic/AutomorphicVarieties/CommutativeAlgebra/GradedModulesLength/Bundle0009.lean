module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.GradedModulesLength.ToDegInjective
public import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.GradedModulesLength.Bundle0008
public import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.GradedModulesLength.Bundle0001
public import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.GradedModulesLength.Bundle0007
public import Formalism.FormalGroupWitt.FormalGroupWittProofs.SolveV
public import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.GradedModulesLength.Bundle0003
public import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.GradedModulesLength.Bundle0005
public import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.GradedModulesLength.Bundle0006

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.GradedModulesLength.FinHolds
section
open IsLocalRing Filter Formalism.MainNotions.V.Pf.V2.Calc UpperTheory.V.Alg UpperTheory.V.Alg.M

private theorem UpperTheory.V.Alg.M.fin_gen {O A K : Type} [CommRing O] [CommRing A] [Algebra O A]
    (𝒜 : ℤ → Submodule O A) [GradedAlgebra 𝒜] [Field K] [Algebra O K] (ξ : A →ₐ[O] K) (j : ℤ) (s : Finset A)
    (hs : Submodule.span (𝒜 0) (s : Set A) = oz 𝒜 j) (h : ∃ f ∈ 𝒜 j, ξ f ≠ 0) : ∃ f ∈ s, ξ f ≠ 0 := by
  obtain ⟨f, hf, hξ⟩ := h
  by_contra hne
  push_neg at hne
  have hf' : f ∈ Submodule.span (𝒜 0) (s : Set A) := by
    rw [hs]
    exact (mem_oz 𝒜).2 hf
  apply hξ
  clear hξ hf
  induction hf' using Submodule.span_induction with
  | mem y hy => exact hne y hy
  | zero => exact map_zero ξ
  | add y z _ _ hy hz => rw [map_add (f := _), hy, hz, add_zero]
  | smul a y _ hy => rw [Algebra.smul_def, map_mul, hy, mul_zero]

private theorem UpperTheory.V.Alg.M.fin_act {O A K : Type} [CommRing O] [CommRing A] [Algebra O A]
    (𝒜 : ℤ → Submodule O A) [GradedAlgebra 𝒜] [Field K] [Algebra O K] (t : Kˣ) (ξ : A →ₐ[O] K) {j : ℤ} {a : A}
    (ha : a ∈ 𝒜 j) : act 𝒜 (tz t) ξ a = ((t ^ j : Kˣ) : K) * ξ a := act_of_mem 𝒜 _ ξ ha

private theorem UpperTheory.V.Alg.M.fin_inv {O A K : Type} [CommRing O] [CommRing A] [Algebra O A]
    (𝒜 : ℤ → Submodule O A) [GradedAlgebra 𝒜] [Field K] [Algebra O K] (t : Kˣ) (ξ : A →ₐ[O] K) :
    ξ = act 𝒜 (tz t⁻¹) (act 𝒜 (tz t) ξ) := by
  classical
  ext a
  set_option synthInstance.maxHeartbeats 100000 in
    rw [← DirectSum.sum_support_decompose 𝒜 a, map_sum, map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  have hm := SetLike.coe_mem (DirectSum.decompose 𝒜 a i)
  rw [fin_act 𝒜 t⁻¹ _ hm, fin_act 𝒜 t ξ hm, ← mul_assoc, ← Units.val_mul, ← mul_zpow, inv_mul_cancel,
    one_zpow, Units.val_one, one_mul]

private theorem UpperTheory.V.Alg.M.fin_onS {O A K : Type} [CommRing O] [CommRing A] [Algebra O A]
    (𝒜 : ℤ → Submodule O A) [GradedAlgebra 𝒜] [Field K] [Algebra O K] (t : Kˣ) (ξ : A →ₐ[O] K) (I : Ideal A)
    (hI : I.IsHomogeneous 𝒜) (h : OnS I ξ) : OnS I (act 𝒜 (tz t) ξ) := by
  classical
  intro f hf
  set_option synthInstance.maxHeartbeats 100000 in
    rw [← DirectSum.sum_support_decompose 𝒜 f, map_sum]
  refine Finset.sum_eq_zero fun j _ => ?_
  rw [fin_act 𝒜 _ _ (DirectSum.decompose 𝒜 f j).2, h _ (hI j hf), mul_zero]

theorem UpperTheory.V.Alg.M.fin_holds :
    ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [IsAdicComplete (maximalIdeal O) O] [CharZero O]
      (K : Type) [Field K] [Algebra O K] [IsAlgClosed K] [FaithfulSMul O K]
      (A : Type) [CommRing A] [Algebra O A] (𝒜 : ℤ → Submodule O A) [GradedAlgebra 𝒜] [IsCO O (𝒜 0)] (x : A →ₐ[O] O), IsWRing 𝒜 x →
    ∀ I : Ideal A, I.IsHomogeneous 𝒜 → M2 𝒜 I → M4 𝒜 K I → ∃ T : Finset (A →ₐ[O] K), Covers 𝒜 I T := by
  intro O _ _ _ _ _ K _ _ _ _ A _ _ 𝒜 _ _ x hx I hI h2 h4
  obtain ⟨s, hs⟩ := fg_holds O A 𝒜 x hx (-2)
  obtain ⟨s', hs'⟩ := fg_holds O A 𝒜 x hx 2
  have hsm : ∀ f ∈ s, f ∈ 𝒜 (-2) := by
    intro f hf
    rw [← mem_oz 𝒜, ← hs]
    exact Submodule.subset_span hf
  have hsm' : ∀ g ∈ s', g ∈ 𝒜 2 := by
    intro g hg
    rw [← mem_oz 𝒜, ← hs']
    exact Submodule.subset_span hg
  let S : Set (A →ₐ[O] K) := ⋃ f ∈ (s : Set A), ⋃ g ∈ (s' : Set A),
    {ξ | OnS I ξ ∧ ξ f = 1 ∧ ξ g ≠ 0 ∧ TwoSigned 𝒜 ξ}
  have hS : S.Finite := by
    refine s.finite_toSet.biUnion fun f hf => s'.finite_toSet.biUnion fun g hg => ?_
    exact (slice_holds O K A 𝒜 x hx I hI h2 h4 f (hsm f hf) g (hsm' g hg)).1.subset
      fun ξ hξ => ⟨hξ.1, hξ.2.1, hξ.2.2.1⟩
  refine ⟨hS.toFinset, fun ξ hξ => ?_, fun ξ hon htw => ?_⟩
  · rw [Set.Finite.mem_toFinset] at hξ
    simp only [S, Set.mem_iUnion, Set.mem_setOf_eq] at hξ
    obtain ⟨f, -, g, -, h1, -, -, h3⟩ := hξ
    exact ⟨h1, h3⟩
  · obtain ⟨f0, hf0, hξf0⟩ := (sign_holds O A 𝒜 x hx K ξ).1.1 htw.1
    obtain ⟨g0, hg0, hξg0⟩ := (sign_holds O A 𝒜 x hx K ξ).2.1 htw.2
    obtain ⟨f, hf, hξf⟩ := fin_gen 𝒜 ξ (-2) s hs ⟨f0, hf0, hξf0⟩
    obtain ⟨g, hg, hξg⟩ := fin_gen 𝒜 ξ 2 s' hs' ⟨g0, hg0, hξg0⟩
    obtain ⟨r, hr⟩ := IsAlgClosed.exists_pow_nat_eq (ξ f) (by norm_num : 0 < 2)
    have hr0 : r ≠ 0 := by
      rintro rfl
      apply hξf
      rw [← hr]
      ring
    have e1 : act 𝒜 (tz (Units.mk0 r hr0)) ξ f = 1 := by
      rw [fin_act 𝒜 _ ξ (hsm f hf), ← hr, Units.val_zpow_eq_zpow_val, Units.val_mk0, zpow_neg, zpow_ofNat,
        inv_mul_cancel₀ (pow_ne_zero _ hr0)]
    have e2 : act 𝒜 (tz (Units.mk0 r hr0)) ξ g ≠ 0 := by
      rw [fin_act 𝒜 _ ξ (hsm' g hg)]
      exact mul_ne_zero (Units.ne_zero _) hξg
    have e3 : TwoSigned 𝒜 (act 𝒜 (tz (Units.mk0 r hr0)) ξ) :=
      ⟨(sign_holds O A 𝒜 x hx K _).1.2 ⟨f, hsm f hf, by rw [e1]; exact one_ne_zero⟩,
        (sign_holds O A 𝒜 x hx K _).2.2 ⟨g, hsm' g hg, e2⟩⟩
    refine ⟨act 𝒜 (tz (Units.mk0 r hr0)) ξ, ?_, (Units.mk0 r hr0)⁻¹, fin_inv 𝒜 _ ξ⟩
    rw [Set.Finite.mem_toFinset]
    simp only [S, Set.mem_iUnion, Set.mem_setOf_eq]
    exact ⟨f, hf, g, hg, fin_onS 𝒜 _ ξ I hI hon, e1, e2, e3⟩
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.GradedModulesLength.IftSubstLow
section
open IsLocalRing Filter Formalism.MainNotions.V.Pf.V2.Calc UpperTheory.V.Alg UpperTheory.V.Alg.M

section SlopeTestRemainingChoices

open MvPowerSeries Formalism.FG.SolveVAux

variable {E σ τ Y : Type} [CommRing E] [AddCommGroup Y]

private theorem ift_P_mem {w : σ → Y} {w' : τ → Y} {k : σ → MvPowerSeries τ E}
    (hw : ∀ i, k i ∈ wtPart E w' (w i)) (e : σ →₀ ℕ) : P k e ∈ wtPart E w' (Finsupp.weight w e) := by
  induction e using Finsupp.induction_linear with
  | zero => rw [P_zero, map_zero]; exact one_mem_wtPart E w'
  | add e₁ e₂ h₁ h₂ => rw [P_add, map_add (f := _)]; exact mul_mem_wtPart E w' h₁ h₂
  | single i n =>
    rw [P_single, Finsupp.weight_single]
    exact SetLike.pow_mem_graded n (hw i)

private theorem ift_subst_mem [Finite σ] {w : σ → Y} {w' : τ → Y} {k : σ → MvPowerSeries τ E}
    (hk : ∀ i, Low 1 (k i)) (hw : ∀ i, k i ∈ wtPart E w' (w i)) {j : Y} {g : MvPowerSeries σ E}
    (hg : g ∈ wtPart E w j) : subst k g ∈ wtPart E w' j := by
  intro n hn
  rw [coeff_subst (hasSubst_of_low hk)]
  refine finsum_eq_zero_of_forall_eq_zero fun e => ?_
  by_cases he : Finsupp.weight w e = j
  · have := ift_P_mem hw e n (he ▸ hn)
    simp only [P] at this
    rw [this, smul_zero]
  · rw [hg e he, zero_smul]

private theorem ift_subst_low [Finite σ] {k : σ → MvPowerSeries τ E} (hk : ∀ i, Low 1 (k i)) {N : ℕ}
    {g : MvPowerSeries σ E} (hg : Low N g) : Low N (subst k g) := by
  intro d hd
  rw [coeff_subst (hasSubst_of_low hk)]
  refine finsum_eq_zero_of_forall_eq_zero fun e => ?_
  rcases lt_or_ge e.degree N with he | he
  · rw [hg e he, zero_smul]
  · have := low_P hk e d (by omega)
    simp only [P] at this
    rw [this, smul_zero]

private theorem ift_lim_mem [Finite σ] {w : σ → Y} {w' : τ → Y} {G : σ → MvPowerSeries τ E}
    {g : σ → MvPowerSeries σ E} (hG : ∀ j, Low 1 (G j)) (hg : ∀ j, Low 2 (g j))
    (hGw : ∀ i, G i ∈ wtPart E w' (w i)) (hgw : ∀ i, g i ∈ wtPart E w (w i)) (i : σ) :
    Formalism.FG.SolveVAux.lim G g i ∈ wtPart E w' (w i) := by
  have hs : ∀ n i, Formalism.FG.SolveVAux.seq G g n i ∈ wtPart E w' (w i) := by
    intro n
    induction n with
    | zero => exact fun i => zero_mem _
    | succ n ih =>
      intro i
      rw [seq_succ]
      exact sub_mem (hGw i) (ift_subst_mem (seq_low hG hg n) ih (hgw i))
  intro d hd
  rw [coeff_lim]
  exact hs _ i d hd

private theorem ift_low_two {p : MvPowerSeries σ E} (h0 : constantCoeff p = 0)
    (h1 : ∀ i, coeff (Finsupp.single i 1) p = 0) : Low 2 p := by
  intro d hd
  rcases Nat.lt_succ_iff_lt_or_eq.1 hd with h | h
  · exact (low_one_iff p).2 h0 d h
  · obtain ⟨i, rfl⟩ := degree_eq_one d h
    exact h1 i

private theorem ift_coeff_X [DecidableEq σ] (i j : σ) :
    coeff (Finsupp.single i 1) (X j : MvPowerSeries σ E) = if i = j then 1 else 0 := by
  classical
  rw [coeff_X]
  simp [Finsupp.single_left_inj one_ne_zero]

private theorem ift_expand [Fintype σ] (g : MvPowerSeries σ E) :
    Low 2 (g - (constantCoeff g • 1 + ∑ s, coeff (Finsupp.single s 1) g • X s)) := by
  classical
  refine ift_low_two (by simp [map_sum]) fun i => ?_
  set_option synthInstance.maxHeartbeats 100000 in
    simp [map_sum, ift_coeff_X, coeff_one]

end SlopeTestRemainingChoices

private theorem ift_span {E ι κ M : Type} [Field E] [Fintype ι] [Fintype κ] [DecidableEq κ] [AddCommGroup M]
    [Module E M] (hc : Fintype.card κ = Fintype.card ι) (c : Matrix κ ι E) (L : Matrix ι κ E) (h : c * L = 1)
    (v : ι → M) (hv : ∀ i, ∑ k, c i k • v k = 0) (k : ι) : v k = 0 := by
  classical
  have h' : L * c = 1 := (Matrix.mul_eq_one_comm_of_equiv (Fintype.equivOfCardEq hc)).1 h
  have : ∑ i, L k i • ∑ k', c i k' • v k' = ∑ k', (L * c) k k' • v k' := by
    simp only [Finset.smul_sum, Matrix.mul_apply, Finset.sum_smul, smul_smul]
    exact Finset.sum_comm
  simpa [hv, h', Matrix.one_apply] using this.symm

open MvPowerSeries Formalism.FG.SolveVAux in
theorem UpperTheory.V.Alg.M.ift_holds :
    ∀ (E τ ι X : Type) [Field E] [Fintype τ] [Fintype ι] [AddCommGroup X] (wt : τ → X) (z : ι → MvPowerSeries τ E),
      (∀ k, z k ∈ wtPart E wt 0 ∧ MvPowerSeries.constantCoeff (z k) = 0) → Nat.card {i // wt i = 0} = Fintype.card ι →
      (∀ i, wt i = 0 → ∃ c : ι → E, ∀ i', MvPowerSeries.coeff (Finsupp.single i' 1) (∑ k, c k • z k) =
        MvPowerSeries.coeff (Finsupp.single i' 1) (MvPowerSeries.X i : MvPowerSeries τ E)) →
      ∃ ψ : MvPowerSeries τ E →ₐ[E] MvPowerSeries {i // wt i ≠ 0} E,
        (∀ j, ∀ g ∈ wtPart E wt j, ψ g ∈ wtPart E (fun i : {i // wt i ≠ 0} => wt i) j) ∧ (∀ k, ψ (z k) = 0) ∧
        (∀ g, MvPowerSeries.constantCoeff (ψ g) = MvPowerSeries.constantCoeff g) ∧
        ∀ g (i : {i // wt i ≠ 0}), MvPowerSeries.coeff (Finsupp.single i 1) (ψ g) = MvPowerSeries.coeff (Finsupp.single i.1 1) g := by
  intro E τ ι Y _ _ _ _ wt z hz hcard hc
  classical
  choose c hc using hc
  let G : τ → MvPowerSeries {i // wt i ≠ 0} E := fun i => if h : wt i = 0 then 0 else X ⟨i, h⟩
  let g : τ → MvPowerSeries τ E := fun i => if h : wt i = 0 then ∑ k, c i h k • z k - X i else 0
  have hG : ∀ j, Low 1 (G j) := fun j => by
    rw [low_one_iff]
    simp only [G]
    split_ifs <;> simp
  have hg : ∀ j, Low 2 (g j) := fun j => by
    simp only [g]
    split_ifs with h
    · refine ift_low_two (by simp [map_sum, fun k => (hz k).2]) fun i => ?_
      rw [map_sub, hc, sub_self]
    · exact low_of_zero _
  have hGw : ∀ i, G i ∈ wtPart E (fun i : {i // wt i ≠ 0} => wt i) (wt i) := fun i => by
    simp only [G]
    split_ifs with h
    · exact zero_mem _
    · exact X_mem_wtPart E (fun i : {i // wt i ≠ 0} => wt i) ⟨i, h⟩
  have hgw : ∀ i, g i ∈ wtPart E wt (wt i) := fun i => by
    simp only [g]
    split_ifs with h
    · refine sub_mem (Submodule.sum_mem _ fun k _ => Submodule.smul_mem _ _ ?_) (X_mem_wtPart E wt i)
      rw [h]; exact (hz k).1
    · exact zero_mem _
  have hl := lim_low hG hg
  have hs := hasSubst_of_low hl
  let ψ : MvPowerSeries τ E →ₐ[E] MvPowerSeries {i // wt i ≠ 0} E := substAlgHom hs
  have hψ : ∀ f, ψ f = subst (Formalism.FG.SolveVAux.lim G g) f := fun f => substAlgHom_apply hs f
  have hX : ∀ i, ψ (X i) = G i - ψ (g i) := fun i => by
    rw [hψ, hψ, subst_X hs]; exact (lim_fixed hG hg i).symm
  have hlow : ∀ f, Low 2 f → Low 2 (ψ f) := fun f hf => by rw [hψ]; exact ift_subst_low hl hf
  have key : ∀ f (d : {i // wt i ≠ 0} →₀ ℕ), d.degree < 2 → coeff d (ψ f) =
      constantCoeff f * coeff d (1 : MvPowerSeries {i // wt i ≠ 0} E) +
        ∑ s, coeff (Finsupp.single s 1) f * coeff d (G s) := fun f d hd => by
    have := hlow _ (ift_expand f) d hd
    rw [map_sub, map_sub, sub_eq_zero] at this
    rw [this]
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [map_add (f := _), map_smul, map_one, map_sum, hX, map_sub, hlow _ (hg _) d hd, sub_zero, smul_eq_mul]
  refine ⟨ψ, fun j f hf => ?_, ?_, fun f => ?_, fun f i => ?_⟩
  · rw [hψ]; exact ift_subst_mem hl (ift_lim_mem hG hg hGw hgw) hf
  · refine ift_span (E := E) (κ := {i // wt i = 0}) (by rw [← hcard, Nat.card_eq_fintype_card])
      (Matrix.of fun i k => c i.1 i.2 k) (Matrix.of fun k i => coeff (Finsupp.single i.1 1) (z k)) ?_
      (fun k => ψ (z k)) fun i => ?_
    · ext i i'
      have := hc i.1 i.2 i'.1
      rw [ift_coeff_X] at this
      set_option synthInstance.maxHeartbeats 100000 in
        simp only [map_sum, map_smul, smul_eq_mul] at this
      simp only [Matrix.mul_apply, Matrix.of_apply, this, Matrix.one_apply, Subtype.ext_iff, eq_comm]
    · have := hX i.1
      set_option synthInstance.maxHeartbeats 100000 in
        simp only [G, g, dif_pos i.2, map_sub, map_sum, map_smul] at this
      simp only [Matrix.of_apply]
      linear_combination this
  · have := key f 0 (by simp)
    rw [← coeff_zero_eq_constantCoeff_apply, this]
    simp [fun s => hG s 0 (by simp)]
  · rw [key f _ (by simp), Finset.sum_eq_single i.1]
    · simp [G, i.2, coeff_one]
    · intro s _ hs
      simp only [G]
      split_ifs with h
      · simp
      · rw [ift_coeff_X, if_neg (fun h' => hs (by rw [h'])), mul_zero]
    · simp
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.GradedModulesLength.LkHolds
section
open IsLocalRing Filter Formalism.MainNotions.V.Pf.V2.Calc UpperTheory.V.Alg UpperTheory.V.Alg.M

theorem UpperTheory.V.Alg.M.lk_holds :
    ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [IsAdicComplete (maximalIdeal O) O] [CharZero O]
      (A : Type) [CommRing A] [Algebra O A] (𝒜 : ℤ → Submodule O A) [GradedAlgebra 𝒜] [IsCO O (𝒜 0)] (x : A →ₐ[O] O), IsWRing 𝒜 x →
    ∀ (r s r' s' m : ℕ) (Q : Eqns 𝒜 x r s r' s' m),
    ∀ (τ : Type) [Fintype τ] (wt : τ → ℤ) (φ : A →ₐ[O] MvPowerSeries τ (FractionRing O)), IsChart0 𝒜 x wt φ →
    Q.F (Fin.last r) ∈ satSq x → ∃ 𝔮 : Ideal (mR Q), (𝔮 : Set (mR Q)) = leadKer Q wt φ ∧ (GMod.self (mGr Q)).IsHomSub 𝔮 ∧
      coefIdeal _ (RingHom.ker φ) ≤ 𝔮 ∧ (∀ b : 𝒜 0, x b = 0 → algebraMap (𝒜 0) (mR Q) b ∈ 𝔮) ∧
      (∀ c : O, c ≠ 0 → ∀ p, algebraMap (𝒜 0) (mR Q) (algebraMap O (𝒜 0) c) * p ∈ 𝔮 → p ∈ 𝔮) ∧
      ∀ (f g : A) (hf : f ∈ 𝒜 (-1)) (hg : g ∈ 𝒜 (-1)), f - g ∈ satSq x →
        sec (mN 𝒜 (Q.F (Fin.last r))) 0 (f ^ 2) (sq_mem_neg 𝒜 hf) - sec (mN 𝒜 (Q.F (Fin.last r))) 0 (g ^ 2) (sq_mem_neg 𝒜 hg) ∈ 𝔮 := by
  classical
  intro O _ _ _ _ _ A _ _ 𝒜 _ _ x hW r s r' s' m Q τ _ wt φ hφ hF
  have hsat := satfil_holds O A 𝒜 x hW τ wt φ hφ
  have hlat := latfil_holds O A 𝒜 x hW τ wt φ hφ _ (Q.hF (Fin.last r)) hF
  have hmul : ∀ (a b : ℕ) (g h : MvPowerSeries τ (FractionRing O)), g ∈ fil (FractionRing O) wt a →
      h ∈ fil (FractionRing O) wt b → g * h ∈ fil (FractionRing O) wt (a + b) :=
    fun a b g h hg hh => (fil_holds _ τ wt a b g h hg hh).1
  have h0 : ∀ g : MvPowerSeries τ (FractionRing O), g ∈ fil (FractionRing O) wt 0 :=
    fun g ν hν => absurd hν (Nat.not_lt_zero _)
  let 𝔮 : Ideal (mR Q) :=
    { carrier := leadKer Q wt φ
      add_mem' := fun {p q} hp hq μ => by
        show φ (AddMonoidAlgebra.coeff (p.1 + q.1) μ) ∈ _
        rw [MvPolynomial.coeff_add, map_add (f := _)]
        exact add_mem (hp μ) (hq μ)
      zero_mem' := fun μ => by
        show φ 0 ∈ _
        rw [map_zero φ]; exact zero_mem _
      smul_mem' := fun c p hp μ => by
        show φ (AddMonoidAlgebra.coeff (c.1 * p.1) μ) ∈ _
        set_option synthInstance.maxHeartbeats 100000 in
          rw [MvPolynomial.coeff_mul, map_sum]
        refine Submodule.sum_mem _ fun d hd => ?_
        rw [map_mul]
        have h1 := hmul _ _ _ _ (hlat d.1 _ (c.2 d.1)).2 (hp d.2)
        have h2 : d.1 + d.2 = μ := Finset.HasAntidiagonal.mem_antidiagonal.1 hd
        have h3 : 2 * μ 0 + 4 * μ 2 + 1 = 2 * d.1 0 + 4 * d.1 2 + (2 * d.2 0 + 4 * d.2 2 + 1) := by
          rw [← h2, Finsupp.add_apply, Finsupp.add_apply]; ring
        rw [h3]; exact h1 }
  have hmono : ∀ (μ : Fin 3 →₀ ℕ) (p : mR Q) (f : A), p.1 = MvPolynomial.monomial μ f →
      φ f ∈ fil (FractionRing O) wt (2 * μ 0 + 4 * μ 2 + 1) → p ∈ 𝔮 := by
    intro μ p f hp h ν
    rw [hp, MvPolynomial.coeff_monomial]
    split_ifs with h1
    · rw [← h1]; exact h
    · rw [map_zero φ]; exact zero_mem _
  refine ⟨𝔮, rfl, ?_, ?_, ?_, ?_, ?_⟩
  · refine le_antisymm (fun p hp => ?_) (Submodule.span_le.2 fun p hp => hp.1)
    rw [eq_sum_mono _ p]
    exact Submodule.sum_mem _ fun μ _ =>
      Submodule.subset_span ⟨hmono μ _ _ rfl (hp μ), toDeg μ, mono_mem _ μ _ _⟩
  · intro p hp μ
    have : φ (AddMonoidAlgebra.coeff p.1 μ) = 0 := hp μ
    rw [this]; exact zero_mem _
  · intro b hb
    exact hmono 0 _ b.1 rfl (hsat.2 b.1 b.2 hb)
  · intro c hc p hp μ
    have h1 : φ (AddMonoidAlgebra.coeff (MvPolynomial.C (algebraMap O A c) * p.1) μ) ∈ _ := hp μ
    rw [MvPolynomial.coeff_C_mul, map_mul, AlgHom.commutes, ← Algebra.smul_def,
      ← algebraMap_smul (FractionRing O)] at h1
    have hc' : algebraMap O (FractionRing O) c ≠ 0 := by
      simpa using hc
    exact (Submodule.smul_mem_iff _ hc').1 h1
  · intro f g hf hg hfg
    refine hmono (Finsupp.single 0 1) _ (f ^ 2 - g ^ 2) ?_ ?_
    · rw [map_sub]; rfl
    · have h1 := hsat.1 _ (sub_mem hf hg) hfg
      have h2 := (fil_holds _ τ wt 0 0 _ _ (h0 (φ (f + g))) (h0 0)).2 _ (hφ.graded _ _ (add_mem hf hg))
      have h3 := hmul _ _ _ _ h1 h2
      rw [← map_mul] at h3
      have h4 : f ^ 2 - g ^ 2 = (f - g) * (f + g) := by ring
      rw [h4]
      simpa using h3
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.GradedModulesLength.XProjZero
section
open IsLocalRing Filter Formalism.MainNotions.V.Pf.V2.Calc UpperTheory.V.Alg UpperTheory.V.Alg.M

section SlopeTestRemainingChoices

variable {O A K : Type} [CommRing O] [CommRing A] [Algebra O A] (𝒜 : ℤ → Submodule O A) [GradedAlgebra 𝒜]
  [Field K] [Algebra O K]

private theorem proj_same {j : ℤ} {f : A} (hf : f ∈ 𝒜 j) : GradedAlgebra.proj 𝒜 j f = f := by
  rw [GradedAlgebra.proj_apply, DirectSum.decompose_of_mem_same 𝒜 hf]

private theorem proj_ne {i j : ℤ} {f : A} (hf : f ∈ 𝒜 i) (h : i ≠ j) : GradedAlgebra.proj 𝒜 j f = 0 := by
  rw [GradedAlgebra.proj_apply, DirectSum.decompose_of_mem_ne 𝒜 hf h]

private theorem x_proj_zero (x : A →ₐ[O] O) (hx : ∀ j, j ≠ 0 → ∀ f ∈ 𝒜 j, x f = 0) (u : A) :
    x (GradedAlgebra.proj 𝒜 0 u) = x u := by
  induction u using DirectSum.Decomposition.inductionOn 𝒜 with
  | zero => simp
  | @homogeneous i m =>
    by_cases hi : i = 0
    · subst hi
      rw [proj_same 𝒜 m.2]
    · rw [proj_ne 𝒜 m.2 hi, map_zero, hx i hi _ m.2]
  | add a b ha hb => rw [map_add (f := _), map_add (f := _), map_add (f := _), ha, hb]

private theorem kill_sq (x : A →ₐ[O] O) (hx : ∀ j, j ≠ 0 → ∀ f ∈ 𝒜 j, x f = 0) (ξ : A →ₐ[O] K) (j : ℤ)
    (h : ∀ a b, a + b = j → ∀ u ∈ 𝒜 a, ∀ v ∈ 𝒜 b, x u = 0 → x v = 0 → ξ u * ξ v = 0)
    (f : A) (hf : f ∈ RingHom.ker x ^ 2) : ξ (GradedAlgebra.proj 𝒜 j f) = 0 := by
  classical
  have hc : ∀ u : A, x u = 0 → ∀ a, x (DirectSum.decompose 𝒜 u a : A) = 0 := by
    intro u hu a
    by_cases ha : a = 0
    · subst ha
      rw [← GradedAlgebra.proj_apply, x_proj_zero 𝒜 x hx, hu]
    · exact hx a ha _ (SetLike.coe_mem _)
  rw [sq] at hf
  refine Submodule.mul_induction_on hf (fun u hu v hv => ?_) (fun a b ha hb => by rw [map_add (f := _), map_add (f := _), ha, hb, add_zero])
  rw [← DirectSum.sum_support_decompose 𝒜 u, ← DirectSum.sum_support_decompose 𝒜 v, Finset.sum_mul_sum]
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [map_sum]
  refine Finset.sum_eq_zero fun a _ => Finset.sum_eq_zero fun b _ => ?_
  have hm : (DirectSum.decompose 𝒜 u a : A) * (DirectSum.decompose 𝒜 v b : A) ∈ 𝒜 (a + b) :=
    SetLike.GradedMul.mul_mem (SetLike.coe_mem _) (SetLike.coe_mem _)
  by_cases hab : a + b = j
  · rw [proj_same 𝒜 (hab ▸ hm), map_mul]
    exact h a b hab _ (SetLike.coe_mem _) _ (SetLike.coe_mem _) (hc u hu a) (hc v hv b)
  · rw [proj_ne 𝒜 hm hab, map_zero]

private theorem kill_part [IsDomain O] [FaithfulSMul O K] (x : A →ₐ[O] O)
    (hx : ∀ j, j ≠ 0 → ∀ f ∈ 𝒜 j, x f = 0) (ξ : A →ₐ[O] K) (j : ℤ) (hj : j ≠ 0)
    (h : ∀ a b, a + b = j → ∀ u ∈ 𝒜 a, ∀ v ∈ 𝒜 b, x u = 0 → x v = 0 → ξ u * ξ v = 0)
    {ι : Type} (F : ι → A) (hF : ∀ i, F i ∈ 𝒜 j) (hξ : ∀ i, ξ (F i) = 0) (hs : SpansCot x 𝒜 j F)
    (f : A) (hf : f ∈ 𝒜 j) : ξ f = 0 := by
  have hcan : ∀ c : O, c ≠ 0 → ∀ y : K, c • y = 0 → y = 0 := by
    intro c hc y hy
    rw [Algebra.smul_def] at hy
    exact (mul_eq_zero.1 hy).resolve_left
      (fun h0 => hc (FaithfulSMul.algebraMap_injective O K (by rw [h0, map_zero])))
  let L : A →ₗ[O] K := ξ.toLinearMap ∘ₗ GradedAlgebra.proj 𝒜 j
  have hL : satSq x ≤ LinearMap.ker L := by
    rintro g ⟨c, hc, hg⟩
    refine hcan c hc _ ?_
    rw [← map_smul]
    exact kill_sq 𝒜 x hx ξ j h _ hg
  have hL' : ∀ g ∈ 𝒜 j, (satSq x).liftQ L hL ((satSq x).mkQ g) = ξ g := by
    intro g hg
    show ξ (GradedAlgebra.proj 𝒜 j g) = ξ g
    rw [proj_same 𝒜 hg]
  obtain ⟨c, hc, hp⟩ := hs ((satSq x).mkQ f) ⟨f, ⟨hf, hx j hj f hf⟩, rfl⟩
  have hle : cotSpan x F ≤ LinearMap.ker ((satSq x).liftQ L hL) := by
    refine Submodule.span_le.2 ?_
    rintro _ ⟨i, rfl⟩
    exact (hL' _ (hF i)).trans (hξ i)
  have h1 := LinearMap.mem_ker.1 (hle hp)
  rw [map_smul, hL' f hf] at h1
  exact hcan c hc _ h1

end SlopeTestRemainingChoices

theorem UpperTheory.V.Alg.M.ct_holds :
    ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [IsAdicComplete (maximalIdeal O) O] [CharZero O]
      (K : Type) [Field K] [Algebra O K] [IsAlgClosed K] [FaithfulSMul O K]
      (A : Type) [CommRing A] [Algebra O A] (𝒜 : ℤ → Submodule O A) [GradedAlgebra 𝒜] [IsCO O (𝒜 0)] (x : A →ₐ[O] O), IsWRing 𝒜 x →
    ∀ (r s r' s' m : ℕ) (Q : Eqns 𝒜 x r s r' s' m),
    SpansCot x 𝒜 (-1) Q.F → SpansCot x 𝒜 (-2) Q.G → ∀ ξ : A →ₐ[O] K, OnS Q.ideal ξ → PosZero 𝒜 ξ →
      Same0 𝒜 ξ ((Algebra.ofId O K).comp x) → NegZero 𝒜 ξ := by
  intro O _ _ _ _ _ K _ _ _ _ A _ _ 𝒜 _ _ x hW r s r' s' m Q hF hG ξ hS hP h0
  have hnn : ∀ a, 0 ≤ a → ∀ u ∈ 𝒜 a, x u = 0 → ξ u = 0 := by
    intro a ha u hu hxu
    rcases ha.eq_or_lt with rfl | ha
    · rw [h0 u hu, AlgHom.comp_apply, hxu, map_zero]
    · exact hP a ha u hu
  have h1 : ∀ f ∈ 𝒜 (-1), ξ f = 0 := by
    refine kill_part 𝒜 x hW.fixed ξ (-1) (by decide) ?_ Q.F Q.hF (fun i => hS _ (Ideal.subset_span ?_)) hF
    · intro a b hab u hu v hv hxu hxv
      by_cases ha : 0 ≤ a
      · rw [hnn a ha u hu hxu, zero_mul]
      · rw [hnn b (by omega) v hv hxv, mul_zero]
    · exact Or.inl (Or.inl (Or.inl (Or.inl ⟨i, rfl⟩)))
  have h2 : ∀ f ∈ 𝒜 (-2), ξ f = 0 := by
    refine kill_part 𝒜 x hW.fixed ξ (-2) (by decide) ?_ Q.G Q.hG (fun i => hS _ (Ideal.subset_span ?_)) hG
    · intro a b hab u hu v hv hxu hxv
      by_cases ha : 0 ≤ a
      · rw [hnn a ha u hu hxu, zero_mul]
      · by_cases hb : 0 ≤ b
        · rw [hnn b hb v hv hxv, mul_zero]
        · obtain rfl : a = -1 := by omega
          rw [h1 u hu, zero_mul]
    · exact Or.inl (Or.inl (Or.inl (Or.inr ⟨i, rfl⟩)))
  by_contra hn
  obtain ⟨f, hf, hne⟩ := (sign_holds O A 𝒜 x hW K ξ).1.1 hn
  exact hne (h2 f hf)
end

