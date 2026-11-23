module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.GradedModulesLength.ToDegInjective
public import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.GradedModulesLength.Bundle0001
public import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.GradedModulesLength.Bundle0002
public import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.GradedModulesLength.Bundle0004

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.GradedModulesLength.LinPartApply
section
open IsLocalRing Filter Formalism.MainNotions.V.Pf.V2.Calc UpperTheory.V.Alg UpperTheory.V.Alg.M

section

variable {O A : Type} [CommRing O] [IsDomain O] [CommRing A] [Algebra O A]

private theorem rk_fin [IsNoetherianRing O] (𝒜 : ℤ → Submodule O A) [GradedAlgebra 𝒜] (x : A →ₐ[O] O) (j : ℤ)
    (hx : ∀ f ∈ 𝒜 j, x f = 0) (hfg : (oz 𝒜 j).FG) : Module.Finite O (cotLat x 𝒜 j) := by
  classical
  obtain ⟨S, hS⟩ := hfg
  rw [Module.Finite.iff_fg]
  refine ⟨S.image (satSq x).mkQ, ?_⟩
  rw [Finset.coe_image]
  apply le_antisymm
  · rw [Submodule.span_le]
    rintro _ ⟨s, hs, rfl⟩
    have hsA : s ∈ 𝒜 j := by
      have : s ∈ oz 𝒜 j := hS ▸ Submodule.subset_span hs
      exact this
    exact ⟨s, ⟨hsA, hx s hsA⟩, rfl⟩
  · rintro _ ⟨f, ⟨hf, -⟩, rfl⟩
    have hf' : f ∈ Submodule.span (𝒜 0) (S : Set A) := by
      rw [hS]
      exact hf
    clear hf
    induction hf' using Submodule.span_induction with
    | mem s hs => exact Submodule.subset_span ⟨s, hs, rfl⟩
    | zero => simp
    | add a b _ _ ha hb =>
      rw [map_add (f := _)]
      exact add_mem ha hb
    | smul a b hb ih =>
      have hbA : b ∈ 𝒜 j := by
        have : b ∈ oz 𝒜 j := hS ▸ hb
        exact this
      have hxb : x b = 0 := hx b hbA
      have e : (satSq x).mkQ (a • b) = (satSq x).mkQ (x (a : A) • b) := by
        rw [Submodule.mkQ_apply, Submodule.mkQ_apply, Submodule.Quotient.eq]
        refine ⟨1, one_ne_zero, ?_⟩
        rw [one_smul, pow_two]
        have h1 : ((a : A) - algebraMap O A (x (a : A))) ∈ RingHom.ker x := by
          rw [RingHom.mem_ker]
          simp
        have h2 : b ∈ RingHom.ker x := by
          rw [RingHom.mem_ker]
          exact hxb
        have e2 : a • b - x (a : A) • b = ((a : A) - algebraMap O A (x (a : A))) * b := by
          rw [sub_mul, ← Algebra.smul_def]
          rfl
        rw [e2]
        exact Ideal.mul_mem_mul h1 h2
      rw [e, map_smul]
      exact Submodule.smul_mem _ _ ih

private noncomputable def linPart {τ : Type} (φ : A →ₐ[O] MvPowerSeries τ (FractionRing O)) (i : τ) :
    A →ₗ[O] FractionRing O :=
  ((MvPowerSeries.coeff (Finsupp.single i 1)).restrictScalars O) ∘ₗ φ.toLinearMap

private theorem linPart_apply {τ : Type} (φ : A →ₐ[O] MvPowerSeries τ (FractionRing O)) (i : τ) (f : A) :
    linPart φ i f = MvPowerSeries.coeff (Finsupp.single i 1) (φ f) := rfl

private theorem linPart_sat {τ : Type} {𝒜 : ℤ → Submodule O A} {x : A →ₐ[O] O} {wt : τ → ℤ}
    {φ : A →ₐ[O] MvPowerSeries τ (FractionRing O)} (h : IsChart 𝒜 x wt φ) (i : τ) :
    ∀ f ∈ satSq x, linPart φ i f = 0 := by
  intro f hf
  obtain ⟨c, hc, hcf⟩ := hf
  have hker : ∀ g ∈ RingHom.ker x ^ 2, linPart φ i g = 0 := by
    intro g hg
    rw [pow_two] at hg
    refine Submodule.mul_induction_on hg ?_ ?_
    · intro a ha b hb
      rw [linPart_apply, map_mul]
      apply MvPowerSeries.coeff_of_lt_order
      have ha0 : MvPowerSeries.constantCoeff (φ a) = 0 := by
        rw [h.const, RingHom.mem_ker.mp ha, map_zero]
      have hb0 : MvPowerSeries.constantCoeff (φ b) = 0 := by
        rw [h.const, RingHom.mem_ker.mp hb, map_zero]
      have hA := (MvPowerSeries.one_le_order_iff_constCoeff_eq_zero).mpr ha0
      have hB := (MvPowerSeries.one_le_order_iff_constCoeff_eq_zero).mpr hb0
      calc (((Finsupp.single i 1).degree : ℕ) : ℕ∞) = 1 := by simp
        _ < 1 + 1 := by norm_num
        _ ≤ (φ a).order + (φ b).order := add_le_add hA hB
        _ ≤ ((φ a) * (φ b)).order := MvPowerSeries.le_order_mul
    · intro a b ha hb
      rw [map_add (f := _), ha, hb, add_zero]
  have h0 := hker _ hcf
  rw [map_smul, Algebra.smul_def, mul_eq_zero] at h0
  rcases h0 with h0 | h0
  · exact absurd ((IsFractionRing.injective O (FractionRing O)) (h0.trans (map_zero _).symm)) hc
  · exact h0

private theorem linPart_wt {τ : Type} {𝒜 : ℤ → Submodule O A} {x : A →ₐ[O] O} {wt : τ → ℤ}
    {φ : A →ₐ[O] MvPowerSeries τ (FractionRing O)} (h : IsChart 𝒜 x wt φ) (i : τ) {j : ℤ} (hij : wt i ≠ j)
    {f : A} (hf : f ∈ 𝒜 j) : linPart φ i f = 0 := by
  rw [linPart_apply]
  apply h.graded j f hf
  simpa [Finsupp.weight_apply, Finsupp.sum_single_index] using hij

private theorem linPart_proj {τ : Type} {𝒜 : ℤ → Submodule O A} [GradedAlgebra 𝒜] {x : A →ₐ[O] O} {wt : τ → ℤ}
    {φ : A →ₐ[O] MvPowerSeries τ (FractionRing O)} (h : IsChart 𝒜 x wt φ) (i : τ) {j : ℤ} (hij : wt i = j) (f : A) :
    linPart φ i (DirectSum.decompose 𝒜 f j) = linPart φ i f := by
  classical
  conv_rhs => rw [← DirectSum.sum_support_decompose 𝒜 f]
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sum]
  by_cases hj : j ∈ (DirectSum.decompose 𝒜 f).support
  · rw [Finset.sum_eq_single j]
    · intro k _ hk
      exact linPart_wt h i (by rw [hij]; exact fun e => hk e.symm) (DirectSum.decompose 𝒜 f k).2
    · intro hn
      exact absurd hj hn
  · rw [DFinsupp.notMem_support_iff] at hj
    rw [hj]
    simp only [ZeroMemClass.coe_zero, map_zero]
    symm
    apply Finset.sum_eq_zero
    intro k hk
    have hk' : k ≠ j := by
      rintro rfl
      exact (DFinsupp.mem_support_iff.mp hk) hj
    exact linPart_wt h i (by rw [hij]; exact fun e => hk' e.symm) (DirectSum.decompose 𝒜 f k).2

end

theorem UpperTheory.V.Alg.M.rk_holds :
    ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [IsAdicComplete (maximalIdeal O) O] [CharZero O]
      (A : Type) [CommRing A] [Algebra O A] (𝒜 : ℤ → Submodule O A) [GradedAlgebra 𝒜] [IsCO O (𝒜 0)] (x : A →ₐ[O] O), IsWRing 𝒜 x →
    ∀ n : ℤ → ℕ, SmoothPt 𝒜 x n → Module.Finite O (cotLat x 𝒜 (-1)) ∧ Module.finrank O (cotLat x 𝒜 (-1)) = n (-1) := by
  intro O _ _ _ _ _ A _ _ 𝒜 _ _ x hW n hS
  obtain ⟨τ, _, wt, φ, hc, hn⟩ := hS
  classical
  have hfin : Module.Finite O (cotLat x 𝒜 (-1)) :=
    rk_fin 𝒜 x (-1) (hW.fixed (-1) (by norm_num)) (fg_holds O A 𝒜 x hW (-1))
  refine ⟨hfin, ?_⟩
  let Lq : (A ⧸ satSq x) →ₗ[O] ({i // wt i = -1} → FractionRing O) :=
    (satSq x).liftQ (LinearMap.pi fun i : {i // wt i = -1} => linPart φ i.1) (by
      intro f hf
      rw [LinearMap.mem_ker]
      funext i
      exact linPart_sat hc i.1 f hf)
  let L : cotLat x 𝒜 (-1) →ₗ[O] ({i // wt i = -1} → FractionRing O) := Lq ∘ₗ (cotLat x 𝒜 (-1)).subtype
  have hinj : Function.Injective L := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    rintro ⟨q, hq⟩ hLq
    obtain ⟨f, ⟨hf1, hf2⟩, rfl⟩ := hq
    have hx0 : x f = 0 := RingHom.mem_ker.mp hf2
    have hall : ∀ i : τ, MvPowerSeries.coeff (Finsupp.single i 1) (φ f) = 0 := by
      intro i
      rw [← linPart_apply]
      by_cases hi : wt i = -1
      · exact congrFun hLq ⟨i, hi⟩
      · exact linPart_wt hc i hi hf1
    have hs := hc.inj f hx0 hall
    apply Subtype.ext
    show (satSq x).mkQ f = 0
    rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
    exact hs
  haveI : Module.IsTorsionFree O (FractionRing O) :=
    Module.isTorsionFree_iff_algebraMap_injective.mpr (IsFractionRing.injective O _)
  haveI : Module.IsTorsionFree O (cotLat x 𝒜 (-1)) :=
    Function.Injective.moduleIsTorsionFree (⇑L) hinj (fun r m => L.map_smul r m)
  have hup : Module.finrank O (cotLat x 𝒜 (-1)) ≤ Fintype.card {i // wt i = -1} := by
    let B := Module.Free.chooseBasis O (cotLat x 𝒜 (-1))
    have hli : LinearIndependent O (L ∘ B) := B.linearIndependent.map' L (LinearMap.ker_eq_bot.mpr hinj)
    have hli' := (LinearIndependent.iff_fractionRing O (FractionRing O)).mp hli
    have h1 := hli'.fintype_card_le_finrank
    rw [Module.finrank_fintype_fun_eq_card] at h1
    rw [Module.finrank_eq_card_chooseBasisIndex]
    exact h1
  choose F hF0 hF1 using fun i : {i // wt i = -1} => hc.onto i.1
  have hmem : ∀ k : {i // wt i = -1},
      (satSq x).mkQ (DirectSum.decompose 𝒜 (F k) (-1) : A) ∈ cotLat x 𝒜 (-1) := fun k =>
    ⟨_, ⟨(DirectSum.decompose 𝒜 (F k) (-1)).2,
      RingHom.mem_ker.mpr (hW.fixed (-1) (by norm_num) _ (DirectSum.decompose 𝒜 (F k) (-1)).2)⟩, rfl⟩
  let g : {i // wt i = -1} → cotLat x 𝒜 (-1) := fun k => ⟨_, hmem k⟩
  have hgv : ∀ k i : {i // wt i = -1}, L (g k) i = linPart φ i.1 (F k) := by
    intro k i
    show linPart φ i.1 (DirectSum.decompose 𝒜 (F k) (-1) : A) = _
    exact linPart_proj hc i.1 i.2 (F k)
  have hli : LinearIndependent O g := by
    apply LinearIndependent.of_comp L
    rw [Fintype.linearIndependent_iff]
    intro a ha i
    have h1 := congrFun ha i
    simp only [Finset.sum_apply, Pi.smul_apply, Function.comp_apply, hgv, Pi.zero_apply] at h1
    rw [Finset.sum_eq_single i] at h1
    · rw [linPart_apply, Algebra.smul_def, mul_eq_zero] at h1
      rcases h1 with h2 | h2
      · exact (IsFractionRing.injective O (FractionRing O)) (h2.trans (map_zero _).symm)
      · exact absurd h2 (hF0 i)
    · intro k _ hk
      rw [linPart_apply, hF1 k i.1 (fun e => hk (Subtype.ext e.symm)), smul_zero]
    · intro hi
      exact absurd (Finset.mem_univ i) hi
  have hlow : Fintype.card {i // wt i = -1} ≤ Module.finrank O (cotLat x 𝒜 (-1)) :=
    hli.fintype_card_le_finrank
  rw [← hn (-1), Nat.card_eq_fintype_card]
  exact le_antisymm hup hlow
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.GradedModulesLength.LocLenAPieceIdeal2LeTwoPow
section
open IsLocalRing Filter Formalism.MainNotions.V.Pf.V2.Calc UpperTheory.V.Alg UpperTheory.V.Alg.M

private theorem homRange {O A : Type} [CommRing O] [CommRing A] [Algebra O A] (𝒜 : ℤ → Submodule O A)
    [GradedAlgebra 𝒜] {ι : Type} (t : ι → A) (d : ℤ) (ht : ∀ i, t i ∈ 𝒜 d) :
    (Ideal.span (Set.range t)).IsHomogeneous 𝒜 := by
  refine Ideal.homogeneous_span 𝒜 _ ?_
  rintro _ ⟨i, rfl⟩
  exact ⟨d, ht i⟩

private theorem sqMem {O A : Type} [CommRing O] [CommRing A] [Algebra O A] (𝒜 : ℤ → Submodule O A)
    [GradedAlgebra 𝒜] {t : A} {d : ℤ} (ht : t ∈ 𝒜 d) : t ^ 2 ∈ 𝒜 (d + d) := by
  rw [pow_two]
  exact SetLike.mul_mem_graded ht ht

private theorem spanSucc {A : Type} [CommRing A] {n : ℕ} (t : Fin (n + 1) → A) :
    Ideal.span (Set.range t) = Ideal.span {t 0} ⊔ Ideal.span (Set.range fun i : Fin n => t i.succ) := by
  rw [Fin.range_fin_succ, Ideal.span_insert]
  rfl

private theorem gen {O K A : Type} [CommRing O] [Field K] [Algebra O K] [CommRing A] [Algebra O A]
    (𝒜 : ℤ → Submodule O A) [GradedAlgebra 𝒜] (σ : 𝒜 0 →ₐ[O] K) (d : ℤ) (c : ℕ∞) (n : ℕ) :
    ∀ (t : Fin n → A), (∀ i, t i ∈ 𝒜 d) → ∀ J : Ideal A, J.IsHomogeneous 𝒜 →
      (∀ w, locLen σ (aPiece 𝒜 (J ⊔ Ideal.span (Set.range t)) w) ≤ c) →
      ∀ w, locLen σ (aPiece 𝒜 (J ⊔ Ideal.span (Set.range fun i => t i ^ 2)) w) ≤ 2 ^ n * c := by
  induction n generalizing c with
  | zero =>
    intro t _ J _ h w
    have e1 : Set.range (fun i : Fin 0 => t i ^ 2) = Set.range t := by
      simp [Set.range_eq_empty]
    rw [e1, pow_zero, one_mul]
    exact h w
  | succ n ih =>
    intro t ht J hJ h w
    have hJ1 : (J ⊔ Ideal.span (Set.range fun i : Fin n => t i.succ)).IsHomogeneous 𝒜 :=
      hJ.sup (homRange 𝒜 _ d fun i => ht i.succ)
    have h1 : ∀ w', locLen σ (aPiece 𝒜 ((J ⊔ Ideal.span (Set.range fun i : Fin n => t i.succ)) ⊔
        Ideal.span {t 0 ^ 2}) w') ≤ 2 * c := by
      intro w'
      have e : (J ⊔ Ideal.span (Set.range fun i : Fin n => t i.succ)) ⊔ Ideal.span {t 0} =
          J ⊔ Ideal.span (Set.range t) := by
        rw [spanSucc t, sup_assoc, sup_comm (Ideal.span (Set.range fun i : Fin n => t i.succ))]
      refine (locLen_aPiece_sup_span_sq_le_add O K A 𝒜 σ _ hJ1 d (t 0) (ht 0) w').trans ?_
      rw [e, two_mul]
      exact add_le_add (h _) (h _)
    have hsq : (Ideal.span ({t 0 ^ 2} : Set A)).IsHomogeneous 𝒜 := by
      apply Ideal.homogeneous_span
      intro y hy
      rw [Set.mem_singleton_iff.mp hy]
      exact ⟨d + d, sqMem 𝒜 (ht 0)⟩
    have hJ2 : (J ⊔ Ideal.span {t 0 ^ 2}).IsHomogeneous 𝒜 := hJ.sup hsq
    have h2 := ih (2 * c) (fun i => t i.succ) (fun i => ht i.succ) (J ⊔ Ideal.span {t 0 ^ 2}) hJ2
      (by
        intro w'
        have e : J ⊔ Ideal.span {t 0 ^ 2} ⊔ Ideal.span (Set.range fun i : Fin n => t i.succ) =
            (J ⊔ Ideal.span (Set.range fun i : Fin n => t i.succ)) ⊔ Ideal.span {t 0 ^ 2} := by
          rw [sup_assoc, sup_assoc, sup_comm (Ideal.span {t 0 ^ 2})]
        rw [e]
        exact h1 w') w
    have e : J ⊔ Ideal.span {t 0 ^ 2} ⊔ Ideal.span (Set.range fun i : Fin n => t i.succ ^ 2) =
        J ⊔ Ideal.span (Set.range fun i => t i ^ 2) := by
      rw [spanSucc (fun i => t i ^ 2), sup_assoc]
    rw [e] at h2
    calc _ ≤ 2 ^ n * (2 * c) := h2
      _ = 2 ^ (n + 1) * c := by rw [pow_succ, mul_assoc]

theorem UpperTheory.V.Alg.M.locLen_aPiece_ideal2_le_two_pow :
    ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [IsAdicComplete (maximalIdeal O) O] [CharZero O]
      (K : Type) [Field K] [Algebra O K] [IsAlgClosed K] [FaithfulSMul O K]
      (A : Type) [CommRing A] [Algebra O A] (𝒜 : ℤ → Submodule O A) [GradedAlgebra 𝒜] [IsCO O (𝒜 0)] (x : A →ₐ[O] O), IsWRing 𝒜 x →
    ∀ (r s r' s' m : ℕ) (Q : Eqns 𝒜 x r s r' s' m),
    ∀ σ : 𝒜 0 →ₐ[O] K, (∀ w, locLen σ (aPiece 𝒜 Q.ideal w) ≤ 1) → ∀ w, locLen σ (aPiece 𝒜 (ideal2 Q) w) ≤ 2 ^ (r + 1 + r') := by
  intro O _ _ _ _ _ K _ _ _ _ A _ _ 𝒜 _ _ x _ r s r' s' m Q σ h1
  have hJ0 : (Ideal.span (Set.range Q.G ∪ Set.range Q.E' ∪ Set.range Q.Z)).IsHomogeneous 𝒜 := by
    apply Ideal.homogeneous_span
    rintro y ((⟨i, rfl⟩ | ⟨i, rfl⟩) | ⟨i, rfl⟩)
    · exact ⟨-2, Q.hG i⟩
    · exact ⟨2, Q.hE' i⟩
    · exact ⟨0, (Q.hZ i).1⟩
  have hE := homRange 𝒜 Q.E 1 Q.hE
  have hF2 := homRange 𝒜 (fun i => Q.F i ^ 2) (-1 + -1) fun i => sqMem 𝒜 (Q.hF i)
  have step1 := gen 𝒜 σ (-1) 1 (r + 1) Q.F Q.hF
    (Ideal.span (Set.range Q.G ∪ Set.range Q.E' ∪ Set.range Q.Z) ⊔ Ideal.span (Set.range Q.E))
    (hJ0.sup hE)
    (by
      intro w'
      have e : Ideal.span (Set.range Q.G ∪ Set.range Q.E' ∪ Set.range Q.Z) ⊔ Ideal.span (Set.range Q.E) ⊔
          Ideal.span (Set.range Q.F) = Q.ideal := by
        simp only [Eqns.ideal, Ideal.span_union]
        ac_rfl
      rw [e]
      exact h1 w')
  have step2 := gen 𝒜 σ 1 (2 ^ (r + 1) * 1) r' Q.E Q.hE
    (Ideal.span (Set.range Q.G ∪ Set.range Q.E' ∪ Set.range Q.Z) ⊔ Ideal.span (Set.range fun i => Q.F i ^ 2))
    (hJ0.sup hF2)
    (by
      intro w'
      have e : Ideal.span (Set.range Q.G ∪ Set.range Q.E' ∪ Set.range Q.Z) ⊔
          Ideal.span (Set.range fun i => Q.F i ^ 2) ⊔ Ideal.span (Set.range Q.E) =
          Ideal.span (Set.range Q.G ∪ Set.range Q.E' ∪ Set.range Q.Z) ⊔ Ideal.span (Set.range Q.E) ⊔
          Ideal.span (Set.range fun i => Q.F i ^ 2) := by
        ac_rfl
      rw [e]
      exact step1 w')
  intro w
  have e : Ideal.span (Set.range Q.G ∪ Set.range Q.E' ∪ Set.range Q.Z) ⊔
      Ideal.span (Set.range fun i => Q.F i ^ 2) ⊔ Ideal.span (Set.range fun i => Q.E i ^ 2) = ideal2 Q := by
    simp only [ideal2, Ideal.span_union]
    ac_rfl
  have h := step2 w
  rw [e] at h
  calc _ ≤ 2 ^ r' * (2 ^ (r + 1) * 1) := h
    _ = 2 ^ (r + 1 + r') := by rw [mul_one, pow_add (2 : ℕ∞) (r + 1) r', mul_comm]
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.GradedModulesLength.SignHolds
section
open IsLocalRing Filter Formalism.MainNotions.V.Pf.V2.Calc UpperTheory.V.Alg UpperTheory.V.Alg.M

private theorem UpperTheory.V.Alg.M.kill_pow {O B A κ : Type} [CommRing O] [CommRing B] [CommRing A] [Algebra O A]
    [Algebra B A] [Field κ] [Algebra O κ] (ξ : A →ₐ[O] κ) (N : Submodule B A) (hN : ∀ f ∈ N, ξ f = 0)
    (n : ℕ) (hn : n ≠ 0) : ∀ f ∈ N ^ n, ξ f = 0 := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn
  intro f hf
  rw [pow_succ] at hf
  refine Submodule.mul_induction_on hf (fun a _ b hb => ?_) (fun a b ha hb => ?_)
  · rw [map_mul, hN b hb, mul_zero]
  · rw [map_add (f := _), ha, hb, add_zero]

theorem UpperTheory.V.Alg.M.sign_holds :
    ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [IsAdicComplete (maximalIdeal O) O] [CharZero O]
      (A : Type) [CommRing A] [Algebra O A] (𝒜 : ℤ → Submodule O A) [GradedAlgebra 𝒜] [IsCO O (𝒜 0)] (x : A →ₐ[O] O), IsWRing 𝒜 x →
    ∀ (κ : Type) [Field κ] [Algebra O κ] (ξ : A →ₐ[O] κ),
      (¬ NegZero 𝒜 ξ ↔ ∃ f ∈ 𝒜 (-2), ξ f ≠ 0) ∧ (¬ PosZero 𝒜 ξ ↔ ∃ g ∈ 𝒜 2, ξ g ≠ 0) := by
  intro O _ _ _ _ _ A _ _ 𝒜 _ _ x hx κ _ _ ξ
  have hp := UpperTheory.V.Alg.M.oz_two_mul_eq_pow O A 𝒜 x hx
  refine ⟨⟨fun h => ?_, ?_⟩, ⟨fun h => ?_, ?_⟩⟩
  · by_contra hc
    push Not at hc
    refine h fun j hj f hf => ?_
    obtain ⟨n, hn⟩ := Int.eq_ofNat_of_zero_le (show 0 ≤ -j by omega)
    have h2 : f * f ∈ oz 𝒜 (-(2 * (n : ℤ))) := by
      have := SetLike.GradedMul.mul_mem hf hf
      rwa [show j + j = -(2 * (n : ℤ)) by omega] at this
    rw [(hp n).1] at h2
    have h3 := UpperTheory.V.Alg.M.kill_pow ξ (oz 𝒜 (-2)) hc n (by omega) _ h2
    rw [map_mul] at h3
    exact mul_self_eq_zero.1 h3
  · rintro ⟨f, hf, h0⟩ h
    exact h0 (h (-2) (by norm_num) f hf)
  · by_contra hc
    push Not at hc
    refine h fun j hj f hf => ?_
    obtain ⟨n, hn⟩ := Int.eq_ofNat_of_zero_le (show 0 ≤ j by omega)
    have h2 : f * f ∈ oz 𝒜 (2 * (n : ℤ)) := by
      have := SetLike.GradedMul.mul_mem hf hf
      rwa [show j + j = 2 * (n : ℤ) by omega] at this
    rw [(hp n).2] at h2
    have h3 := UpperTheory.V.Alg.M.kill_pow ξ (oz 𝒜 2) hc n (by omega) _ h2
    rw [map_mul] at h3
    exact mul_self_eq_zero.1 h3
  · rintro ⟨f, hf, h0⟩ h
    exact h0 (h 2 (by norm_num) f hf)
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.GradedModulesLength.TspHolds
section
open IsLocalRing Filter Formalism.MainNotions.V.Pf.V2.Calc UpperTheory.V.Alg UpperTheory.V.Alg.M

theorem UpperTheory.V.Alg.M.tsp_holds :
    ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [IsAdicComplete (maximalIdeal O) O] [CharZero O]
      (K : Type) [Field K] [Algebra O K] [IsAlgClosed K] [FaithfulSMul O K]
      (A : Type) [CommRing A] [Algebra O A] (𝒜 : ℤ → Submodule O A) [GradedAlgebra 𝒜] [IsCO O (𝒜 0)] (x : A →ₐ[O] O), IsWRing 𝒜 x →
    ∀ I : Ideal A, I.IsHomogeneous 𝒜 → ∀ σ : 𝒜 0 →ₐ[O] K, (∀ b : 𝒜 0, (b : A) ∈ I → σ b = 0) →
      ∃ ξ : A →ₐ[O] K, OnS I ξ ∧ res0 𝒜 ξ = σ := by
  intro O _ _ _ _ _ K _ _ _ _ A _ _ 𝒜 _ _ x hW I hI σ hσ
  haveI : Algebra.FiniteType (𝒜 0) A := (ft_holds O A 𝒜 x hW).1
  let p : A →ₗ[O] 𝒜 0 :=
    (DirectSum.component O ℤ (fun i => 𝒜 i) 0).comp (DirectSum.decomposeLinearEquiv 𝒜).toLinearMap
  have hpa : ∀ a : A, p a = DirectSum.decompose 𝒜 a 0 := fun a => rfl
  have pz : ∀ {i : ℤ} {u : A}, u ∈ 𝒜 i → i ≠ 0 → p u = 0 := by
    intro i u hu hi
    apply Subtype.ext
    rw [hpa]
    simpa using DirectSum.decompose_of_mem_ne 𝒜 hu hi
  have ps : ∀ {u : A} (hu : u ∈ 𝒜 0), p u = ⟨u, hu⟩ := by
    intro u hu
    apply Subtype.ext
    rw [hpa]
    exact DirectSum.decompose_of_mem_same 𝒜 hu
  set J : Ideal A := I ⊔ Ideal.map (algebraMap (𝒜 0) A) (RingHom.ker σ) with hJ
  have hgen : ∀ c : 𝒜 0, σ c = 0 → ∀ a : A, σ (p (a * (c : A))) = 0 := by
    intro c hc a
    induction a using DirectSum.Decomposition.inductionOn 𝒜 with
    | zero => simp
    | homogeneous a =>
      have hm : (a : A) * c ∈ 𝒜 (_ + 0) := SetLike.mul_mem_graded a.2 c.2
      rename_i i
      by_cases hi : i = 0
      · subst hi
        have hm' : (a : A) * c ∈ 𝒜 0 := by simpa using hm
        rw [ps hm', show (⟨(a : A) * c, hm'⟩ : 𝒜 0) = ⟨a, a.2⟩ * c from rfl, map_mul, hc, mul_zero]
      · rw [pz hm (by simpa using hi), map_zero]
    | add u v hu hv => rw [add_mul, map_add (f := _), map_add (f := _), hu, hv, add_zero]
  have hJ0 : ∀ y ∈ J, σ (p y) = 0 := by
    intro y hy
    obtain ⟨u, hu, v, hv, rfl⟩ := Submodule.mem_sup.mp hy
    clear hy
    have h1 : σ (p u) = 0 := by
      apply hσ
      rw [hpa]
      exact hI 0 hu
    have h2 : ∀ a : A, σ (p (a * v)) = 0 := by
      unfold Ideal.map at hv
      induction hv using Submodule.span_induction with
      | mem w hw =>
        obtain ⟨c, hc, rfl⟩ := hw
        exact hgen c hc
      | zero => simp
      | add w w' _ _ hw hw' =>
        intro a
        rw [mul_add, map_add (f := _), map_add (f := _), hw, hw', add_zero]
      | smul a' w _ hw =>
        intro a
        rw [smul_eq_mul, ← mul_assoc]
        exact hw (a * a')
    have h3 := h2 1
    rw [one_mul] at h3
    rw [map_add (f := _), map_add (f := _), h1, h3, add_zero]
  obtain ⟨ξ, hξ1, hξ2, -⟩ := ns_holds O (𝒜 0) A K σ J 1
    (fun b hb => Ideal.mem_sup_right (Ideal.mem_map_of_mem _ hb))
    (by
      intro b n hb hmem
      apply hb
      rw [one_pow, mul_one] at hmem
      have := hJ0 _ hmem
      rwa [show (algebraMap (𝒜 0) A b) = (b : A) from rfl, ps b.2] at this)
  refine ⟨ξ, fun u hu => hξ2 u (Ideal.mem_sup_left hu), ?_⟩
  ext b
  exact hξ1 b
end

