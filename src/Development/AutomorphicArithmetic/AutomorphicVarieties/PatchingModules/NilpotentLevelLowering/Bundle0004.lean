module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.NilpotentLevelLowering.ActUVariableEqPow
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.Bundle0021
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.Bundle0023
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.ExistsCoprimePowOfMemIneKer

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.NilpotentLevelLowering.PsModule
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.N ValuativeRel IsLocalRing
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.LocGL GlobalTheory.GalOfCusp GlobalTheory.SmGL GlobalTheory.SplitWeil
open UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.Hi UpperTheory.V.AlgebraTools UpperTheory.V.Pa UpperTheory.V.Pa.Lev
open scoped TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

private theorem psm_mem_pi {R : Type} [CommRing R] (J : Ideal R) {r : ℕ} (x : Fin r → R) :
    x ∈ J • (⊤ : Submodule R (Fin r → R)) ↔ ∀ i, x i ∈ J := by
  constructor
  · intro hx
    refine Submodule.smul_induction_on hx (fun a ha y _ i => ?_) (fun a b ha hb i => ?_)
    · exact J.mul_mem_right _ ha
    · exact J.add_mem (ha i) (hb i)
  · intro hx
    rw [pi_eq_sum_univ x]
    exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem_smul (hx i) Submodule.mem_top

private theorem psm_prec_pi {R : Type} [CommRing R] (I : Ideal R) [IsPrecomplete I R] (r : ℕ) :
    IsPrecomplete I (Fin r → R) := by
  refine ⟨fun f hf => ?_⟩
  have key : ∀ i, ∃ L : R, ∀ n, f n i ≡ L [SMOD (I ^ n • ⊤ : Submodule R R)] := fun i =>
    IsPrecomplete.prec' (I := I) (fun n => f n i) fun {m n} hmn => by
      have h := hf hmn
      rw [SModEq.sub_mem, psm_mem_pi] at h
      rw [SModEq.sub_mem, smul_eq_mul, Ideal.mul_top]
      exact h i
  choose L hL using key
  refine ⟨L, fun n => ?_⟩
  rw [SModEq.sub_mem, psm_mem_pi]
  intro i
  have h := hL i n
  rwa [SModEq.sub_mem, smul_eq_mul, Ideal.mul_top] at h

private theorem psm_prec_finite {R M : Type} [CommRing R] [AddCommGroup M] [Module R M]
    [Module.Finite R M] (I : Ideal R) [IsPrecomplete I R] : IsPrecomplete I M := by
  obtain ⟨r, π, hπ⟩ := Module.Finite.exists_fin' R M
  haveI := psm_prec_pi I r
  rw [← AdicCompletion.of_surjective_iff]
  intro y
  obtain ⟨z, rfl⟩ := AdicCompletion.map_surjective I hπ y
  obtain ⟨w, rfl⟩ := AdicCompletion.of_surjective I (Fin r → R) z
  exact ⟨π w, (AdicCompletion.map_of I π w).symm⟩

private theorem psm_ev {R S σ : Type} [CommRing R] [CommRing S] [Finite σ] (m : Ideal S) [IsAdicComplete m S]
    (f : R →+* S) (a : σ → S) (ha : ∀ s, a s ∈ m.radical) :
    ∃ F : MvPowerSeries σ R →+* S, (∀ x, F (MvPowerSeries.C x) = f x) ∧ ∀ s, F (MvPowerSeries.X s) = a s := by
  letI : UniformSpace R := ⊥
  haveI : DiscreteUniformity R := ⟨rfl⟩
  letI : WithIdeal S := ⟨m⟩
  have hm : IsAdic m := rfl
  obtain ⟨h1, h2⟩ := hm.isAdicComplete_iff.1 inferInstance
  haveI : IsLinearTopology S S := Ideal.isLinearTopology m
  have hf : Continuous f := continuous_of_discreteTopology
  have hE : MvPowerSeries.HasEval a := by
    refine ⟨fun s => ?_, by simp⟩
    rw [IsTopologicallyNilpotent, hm.hasBasis_nhds_zero.tendsto_right_iff]
    intro n _
    obtain ⟨e, he⟩ := ha s
    filter_upwards [Filter.eventually_ge_atTop (e * n)] with k hk
    have h3 := Ideal.pow_mem_pow he n
    rw [← pow_mul] at h3
    exact Ideal.pow_mem_of_pow_mem _ h3 hk
  exact ⟨MvPowerSeries.eval₂Hom hf hE,
    fun x => by rw [MvPowerSeries.coe_eval₂Hom, MvPowerSeries.eval₂_C],
    fun s => by rw [MvPowerSeries.coe_eval₂Hom, MvPowerSeries.eval₂_X]⟩

private theorem psm_rad {Λ B M : Type} [CommRing Λ] [CommRing B] [Algebra Λ B] [AddCommGroup M] [Module Λ M]
    [Module.Finite Λ M] (I : Ideal Λ) (ι : B →ₐ[Λ] Module.End Λ M) (hι : Function.Injective ι) (b : B)
    (hb : ∀ x : M, ∀ᶠ r : ℕ in Filter.atTop, (ι b ^ r) x ∈ (I • ⊤ : Submodule Λ M)) :
    b ∈ (I.map (algebraMap Λ B)).radical := by
  obtain ⟨n, v, hv⟩ := Module.Finite.exists_fin (R := Λ) (M := M)
  obtain ⟨r, hr⟩ := (Filter.eventually_all.2 fun i => hb (v i)).exists
  have h1 : LinearMap.range (ι b ^ r) ≤ I • ⊤ := by
    rw [LinearMap.range_eq_map, ← hv, Submodule.map_span, Submodule.span_le, hv]
    rintro _ ⟨_, ⟨i, rfl⟩, rfl⟩
    exact hr i
  obtain ⟨p, hp, -, hc, h0⟩ :=
    LinearMap.exists_monic_and_natDegree_eq_and_coeff_mem_pow_and_aeval_eq_zero Λ (ι b ^ r) I h1
  set_option synthInstance.maxHeartbeats 100000 in
    rw [← map_pow, Polynomial.aeval_algHom_apply, map_eq_zero_iff _ hι, hp.as_sum, map_add (f := _), map_sum,
    add_eq_zero_iff_eq_neg, map_pow, Polynomial.aeval_X, ← pow_mul] at h0
  refine ⟨_, h0 ▸ neg_mem (Ideal.sum_mem _ fun k hk => ?_)⟩
  rw [map_mul, Polynomial.aeval_C]
  refine Ideal.mul_mem_right _ _ (Ideal.mem_map_of_mem _ ?_)
  exact Ideal.pow_le_self (Nat.sub_ne_zero_of_lt (Finset.mem_range.1 hk)) (hc k)

private theorem psm_abs {Λ A B M κ : Type} [CommRing Λ] [IsLocalRing Λ] [IsNoetherianRing Λ]
    [IsAdicComplete (maximalIdeal Λ) Λ] [CommRing A] [CommRing B] [AddCommGroup M] [Module Λ M]
    [Module.Finite Λ M] [Finite κ] (g : Λ →+* B) (f : A →+* B) (ι : B →+* Module.End Λ M)
    (hι : Function.Injective ι) (hg : ∀ c, ι (g c) = algebraMap Λ _ c) (b : κ → B)
    (hb : topNil (maximalIdeal Λ) (fun i => ι (b i)) = ⊤) :
    ∃ F : MvPowerSeries κ A →+* B, (∀ x, F (MvPowerSeries.C x) = f x) ∧ ∀ s, F (MvPowerSeries.X s) = b s := by
  letI : Algebra Λ B := g.toAlgebra
  let ι' : B →ₐ[Λ] Module.End Λ M := { ι with commutes' := hg }
  haveI : Module.Finite Λ B := Module.Finite.of_injective ι'.toLinearMap hι
  haveI : IsPrecomplete (maximalIdeal Λ) B := psm_prec_finite _
  haveI : IsAdicComplete ((maximalIdeal Λ).map (algebraMap Λ B)) B :=
    { toIsHausdorff := IsHausdorff.map_algebraMap_iff.2 inferInstance
      toIsPrecomplete := IsPrecomplete.map_algebraMap_iff.2 inferInstance }
  refine psm_ev ((maximalIdeal Λ).map (algebraMap Λ B)) f b fun s => psm_rad _ ι' hι _ fun x => ?_
  have h := mem_topNil.1 (hb.ge (Submodule.mem_top (x := x))) s 1
  rwa [pow_one] at h

theorem UpperTheory.V.Pa.Lev.psModule :
    ∀ (Λ : Type) [CommRing Λ] [IsLocalRing Λ] [IsNoetherianRing Λ] [IsAdicComplete (maximalIdeal Λ) Λ] (A M κ : Type) [CommRing A] [Algebra Λ A] [AddCommGroup M] [Module A M] [Module Λ M] [IsScalarTower Λ A M] [Module.Finite Λ M] [Fintype κ] (T : κ → Module.End A M), (∀ i j, Commute (T i) (T j)) → topNil (maximalIdeal Λ) (fun i => (T i).restrictScalars Λ) = ⊤ → ∃ act : MvPowerSeries κ A →ₐ[A] Module.End A M, ∀ i, act (MvPowerSeries.X i) = T i := by
  intro Λ _ _ _ _ A M κ _ _ _ _ _ _ _ _ T hT htop
  let B := Algebra.adjoin A (Set.range T)
  have hcomm : IsMulCommutative B := Algebra.isMulCommutative_adjoin A (by
    rintro _ ⟨i, rfl⟩ _ ⟨j, rfl⟩
    intro _
    exact hT i j)
  letI : CommRing B := { (inferInstance : Ring B) with mul_comm := fun x y => hcomm.is_comm.comm x y }
  let ι : B →+* Module.End Λ M :=
    { toFun := fun x => (x : Module.End A M).restrictScalars Λ
      map_one' := rfl
      map_mul' := fun _ _ => rfl
      map_zero' := rfl
      map_add' := fun _ _ => rfl }
  have hι : Function.Injective ι := fun x y h =>
    Subtype.ext (LinearMap.ext fun m => LinearMap.congr_fun h m)
  obtain ⟨F, hC, hX⟩ := psm_abs (A := A) ((algebraMap A B).comp (algebraMap Λ A)) (algebraMap A B) ι hι
    (fun c => LinearMap.ext fun m => algebraMap_smul A c m)
    (fun i => ⟨T i, Algebra.subset_adjoin ⟨i, rfl⟩⟩) htop
  refine ⟨{ (B.val : B →+* Module.End A M).comp F with commutes' := fun c => ?_ }, fun i => ?_⟩
  · show ((F (MvPowerSeries.C c) : B) : Module.End A M) = _
    rw [hC]; rfl
  · show ((F (MvPowerSeries.X i) : B) : Module.End A M) = _
    rw [hX]
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.NilpotentLevelLowering.ThetaLoc
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.N ValuativeRel IsLocalRing
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.LocGL GlobalTheory.GalOfCusp GlobalTheory.SmGL GlobalTheory.SplitWeil
open UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.Hi UpperTheory.V.AlgebraTools UpperTheory.V.Pa UpperTheory.V.Pa.Lev
open scoped TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

private theorem mul_prod_le_of_le_one_of_le_of_mul_le_one {G : Type} [CommGroup G] [LinearOrder G] [IsOrderedMonoid G] {n : ℕ}
    (a b : Fin n → G) (hb1 : ∀ l, b l ≤ 1) (hba : ∀ l, b l ≤ a l) (hab : ∀ l, a l * b l ≤ 1) :
    ∀ i j : Fin n, i < j → a i * ∏ l, b l ≤ a j := by
  classical
  intro i j hij
  have hne : j ≠ i := ne_of_gt hij
  have hsplit : ∏ l, b l = b i * (b j * ∏ l ∈ (Finset.univ.erase i).erase j, b l) := by
    rw [Finset.mul_prod_erase _ _ (Finset.mem_erase.mpr ⟨hne, Finset.mem_univ j⟩),
      Finset.mul_prod_erase _ _ (Finset.mem_univ i)]
  calc a i * ∏ l, b l = (a i * b i) * (b j * ∏ l ∈ (Finset.univ.erase i).erase j, b l) := by
        rw [hsplit, mul_assoc]
    _ ≤ 1 * (b j * 1) := mul_le_mul' (hab i) (mul_le_mul' le_rfl (Finset.prod_le_one' (fun l _ => hb1 l)))
    _ ≤ a j := by rw [one_mul, mul_one]; exact hba j

private theorem mul_pow_sub_le_of_mul_le_of_le_of_le_one {G : Type} [CommGroup G] [LinearOrder G] [IsOrderedMonoid G] {n : ℕ}
    (a : Fin n → G) (c : G) (hc1 : c ≤ 1) (hc : ∀ i j : Fin n, i < j → a i * c ≤ a j) (i j : Fin n)
    (hij : i ≤ j) : a i * c ^ (n - (i : ℕ)) ≤ a j * c ^ (n - (j : ℕ)) := by
  rcases lt_or_eq_of_le hij with h | h
  · obtain ⟨d, hd⟩ : ∃ d, n - (i : ℕ) = (n - (j : ℕ)) + d + 1 :=
      ⟨(j : ℕ) - i - 1, by have := j.isLt; have := Fin.lt_iff_val_lt_val.mp h; omega⟩
    calc a i * c ^ (n - (i : ℕ)) = (a i * c) * c ^ d * c ^ (n - (j : ℕ)) := by
          rw [hd, pow_add, pow_add, pow_one]; ac_rfl
      _ ≤ a j * 1 * c ^ (n - (j : ℕ)) := mul_le_mul' (mul_le_mul' (hc i j h) (pow_le_one' hc1 d)) le_rfl
      _ = a j * c ^ (n - (j : ℕ)) := by rw [mul_one]
  · rw [h]

private theorem thetaLoc_split {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    {n : ℕ} (t : Fin n → kˣ) : ∃ b : Fin n → kˣ, Dom b ∧ Dom (t * b) := by
  classical
  let φ : kˣ →* (ValueGroupWithZero k)ˣ := Units.map (valuation k).toMonoidWithZeroHom.toMonoidHom
  have hφ : ∀ u : kˣ, valuation k (u : k) = ((φ u : (ValueGroupWithZero k)ˣ) : ValueGroupWithZero k) :=
    fun u => rfl
  let w : Fin n → kˣ := fun l => if φ (t l) ≤ 1 then t l else (t l)⁻¹
  have hw1 : ∀ l, φ (w l) ≤ 1 := fun l => by
    simp only [w]
    split_ifs with h
    · exact h
    · rw [map_inv]; exact inv_le_one'.mpr (le_of_lt (not_le.mp h))
  have hwa : ∀ l, φ (w l) ≤ φ (t l) := fun l => by
    simp only [w]
    split_ifs with h
    · exact le_rfl
    · rw [map_inv]
      exact (inv_le_one'.mpr (le_of_lt (not_le.mp h))).trans (le_of_lt (not_le.mp h))
  have hwab : ∀ l, φ (t l) * φ (w l) ≤ 1 := fun l => by
    simp only [w]
    split_ifs with h
    · exact mul_le_one' h h
    · rw [map_inv, mul_inv_cancel]
  have hC : φ (∏ l, w l) = ∏ l, φ (w l) := map_prod φ _ _
  have hc1 : ∏ l, φ (w l) ≤ 1 := Finset.prod_le_one' (fun l _ => hw1 l)
  refine ⟨fun i => (∏ l, w l) ^ (n - (i : ℕ)), ?_, ?_⟩
  · intro i j hij
    dsimp only
    rw [hφ, hφ, Units.val_le_val, map_pow, map_pow, hC]
    simpa using mul_pow_sub_le_of_mul_le_of_le_of_le_one (fun _ => (1 : (ValueGroupWithZero k)ˣ)) _ hc1
      (fun _ _ _ => by rw [one_mul]; exact hc1) i j hij
  · intro i j hij
    rw [Pi.mul_apply, Pi.mul_apply]
    rw [hφ, hφ, Units.val_le_val, map_mul, map_mul, map_pow, map_pow, hC]
    exact mul_pow_sub_le_of_mul_le_of_le_of_le_one (fun l => φ (t l)) _ hc1
      (mul_prod_le_of_le_one_of_le_of_mul_le_one (fun l => φ (t l)) (fun l => φ (w l)) hw1 hwa hwab) i j hij

private theorem thetaLoc_ext {T A M₁ M₂ : Type} [CommGroup T] [CommRing A] [AddCommGroup M₁] [Module A M₁]
    [AddCommGroup M₂] [Module A M₂] (Θ : T →* (Module.End A M₁)ˣ) (θ : T →* (Module.End A M₂)ˣ) (ι : M₁ → M₂)
    (t b : T) (hb : ∀ m, (θ b).val (ι m) = ι ((Θ b).val m))
    (htb : ∀ m, (θ (t * b)).val (ι m) = ι ((Θ (t * b)).val m)) (m : M₁) :
    (θ t).val (ι m) = ι ((Θ t).val m) := by
  have key : ∀ y, ((θ b)⁻¹).val ((θ b).val y) = y := fun y => by
    rw [← Module.End.mul_apply, ← Units.val_mul, inv_mul_cancel, Units.val_one, Module.End.one_apply]
  have h1 := htb m
  rw [mul_comm t b] at h1
  simp only [map_mul, Units.val_mul, Module.End.mul_apply] at h1
  rw [← hb] at h1
  rw [← key ((θ t).val (ι m)), h1, key]

theorem UpperTheory.V.Pa.Lev.thetaLoc :
    ∀ (L : Type) [Field L] [NumberField L] (n q : ℕ) (w : Fin q → Plc L) (A M : Type) [CommRing A] [AddCommGroup M] [Module A M] (ρ : Representation A (GV n w) M) (C : ∀ j, Subgroup 𝓀[(w j).adicCompletion L]ˣ) (Θ), IsThetaQ ρ C Θ → ∀ j θ, IsTheta (ρ.comp (atJ n w j)) (C j) θ → ∀ t (m : fixd ρ (UC n w C)) (m' : fixd (ρ.comp (atJ n w j)) (iwC _ n (C j))), (m' : M) = m → ((θ t).val m').val = ((Θ j t).val m).val := by
  intro L _ _ n q w A M _ _ _ ρ C Θ hΘ j θ hθ t m m' hm
  have hmem : ∀ u ∈ iwC _ n (C j), atJ n w j u ∈ UC n w C := by
    intro u hu
    simp only [UC, Subgroup.mem_pi]
    intro i _
    by_cases h : i = j
    · subst h
      simpa [atJ] using hu
    · simp [atJ, Pi.mulSingle_eq_of_ne h, Subgroup.one_mem]
  let ι : fixd ρ (UC n w C) → fixd (ρ.comp (atJ n w j)) (iwC _ n (C j)) := fun x =>
    ⟨x, show ∀ u ∈ iwC _ n (C j), (ρ.comp (atJ n w j)) u x = x from fun u hu =>
      (show ∀ u ∈ UC n w C, ρ u x = x from x.2) _ (hmem u hu)⟩
  have hdom : ∀ s, Dom s → ∀ x, (θ s).val (ι x) = ι ((Θ j s).val x) := by
    intro s hs x
    apply Subtype.ext
    rw [hθ s hs]
    unfold hk
    rw [(hkApply _ _ _ _ _ _ _ ((heckePairIwC _ n (C j)).1 _)).1]
    exact (hΘ.1 j s hs x).symm
  obtain ⟨b, hb, htb⟩ := thetaLoc_split t
  have key := thetaLoc_ext (Θ j) θ ι t b (hdom b hb) (hdom (t * b) htb) m
  have hm' : m' = ι m := Subtype.ext hm
  rw [hm', key]
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.NilpotentLevelLowering.ThetaMap
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.N ValuativeRel IsLocalRing
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.LocGL GlobalTheory.GalOfCusp GlobalTheory.SmGL GlobalTheory.SplitWeil
open UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.Hi UpperTheory.V.AlgebraTools UpperTheory.V.Pa UpperTheory.V.Pa.Lev
open scoped TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

private theorem lt_imp_mul_prod_le_of_b_le_one_le_a_mul_le {G : Type} [CommGroup G] [LinearOrder G] [IsOrderedMonoid G] {n : ℕ}
    (a b : Fin n → G) (hb1 : ∀ l, b l ≤ 1) (hba : ∀ l, b l ≤ a l) (hab : ∀ l, a l * b l ≤ 1) :
    ∀ i j : Fin n, i < j → a i * ∏ l, b l ≤ a j := by
  classical
  intro i j hij
  have hne : j ≠ i := ne_of_gt hij
  have hsplit : ∏ l, b l = b i * (b j * ∏ l ∈ (Finset.univ.erase i).erase j, b l) := by
    rw [Finset.mul_prod_erase _ _ (Finset.mem_erase.mpr ⟨hne, Finset.mem_univ j⟩),
      Finset.mul_prod_erase _ _ (Finset.mem_univ i)]
  calc a i * ∏ l, b l = (a i * b i) * (b j * ∏ l ∈ (Finset.univ.erase i).erase j, b l) := by
        rw [hsplit, mul_assoc]
    _ ≤ 1 * (b j * 1) := mul_le_mul' (hab i) (mul_le_mul' le_rfl (Finset.prod_le_one' (fun l _ => hb1 l)))
    _ ≤ a j := by rw [one_mul, mul_one]; exact hba j

private theorem le_imp_mul_pow_sub_le_of_c_le_one_mul_le {G : Type} [CommGroup G] [LinearOrder G] [IsOrderedMonoid G] {n : ℕ}
    (a : Fin n → G) (c : G) (hc1 : c ≤ 1) (hc : ∀ i j : Fin n, i < j → a i * c ≤ a j) (i j : Fin n)
    (hij : i ≤ j) : a i * c ^ (n - (i : ℕ)) ≤ a j * c ^ (n - (j : ℕ)) := by
  rcases lt_or_eq_of_le hij with h | h
  · obtain ⟨d, hd⟩ : ∃ d, n - (i : ℕ) = (n - (j : ℕ)) + d + 1 :=
      ⟨(j : ℕ) - i - 1, by have := j.isLt; have := Fin.lt_iff_val_lt_val.mp h; omega⟩
    calc a i * c ^ (n - (i : ℕ)) = (a i * c) * c ^ d * c ^ (n - (j : ℕ)) := by
          rw [hd, pow_add, pow_add, pow_one]; ac_rfl
      _ ≤ a j * 1 * c ^ (n - (j : ℕ)) := mul_le_mul' (mul_le_mul' (hc i j h) (pow_le_one' hc1 d)) le_rfl
      _ = a j * c ^ (n - (j : ℕ)) := by rw [mul_one]
  · rw [h]

private theorem thetaMap_split {k : Type} [Field k] [ValuativeRel k] {n : ℕ} (t : Fin n → kˣ) :
    ∃ c : kˣ, ∀ s : Fin n → kˣ, (s = 1 ∨ s = t) → ∀ i j : Fin n, i ≤ j →
      valuation k ((s i * c ^ (n - i) : kˣ) : k) ≤ valuation k ((s j * c ^ (n - j) : kˣ) : k) := by
  classical
  let φ : kˣ →* (ValueGroupWithZero k)ˣ := Units.map (valuation k).toMonoidWithZeroHom.toMonoidHom
  have hφ : ∀ u : kˣ, valuation k (u : k) = ((φ u : (ValueGroupWithZero k)ˣ) : ValueGroupWithZero k) :=
    fun u => rfl
  let w : Fin n → kˣ := fun l => if φ (t l) ≤ 1 then t l else (t l)⁻¹
  have hw1 : ∀ l, φ (w l) ≤ 1 := fun l => by
    simp only [w]
    split_ifs with h
    · exact h
    · rw [map_inv]; exact inv_le_one'.mpr (le_of_lt (not_le.mp h))
  have hwa : ∀ l, φ (w l) ≤ φ (t l) := fun l => by
    simp only [w]
    split_ifs with h
    · exact le_rfl
    · rw [map_inv]
      exact (inv_le_one'.mpr (le_of_lt (not_le.mp h))).trans (le_of_lt (not_le.mp h))
  have hwab : ∀ l, φ (t l) * φ (w l) ≤ 1 := fun l => by
    simp only [w]
    split_ifs with h
    · exact mul_le_one' h h
    · rw [map_inv, mul_inv_cancel]
  refine ⟨∏ l, w l, ?_⟩
  have hC : φ (∏ l, w l) = ∏ l, φ (w l) := map_prod φ _ _
  have hc1 : ∏ l, φ (w l) ≤ 1 := Finset.prod_le_one' (fun l _ => hw1 l)
  intro s hs i j hij
  rw [hφ, hφ, Units.val_le_val, map_mul, map_mul, map_pow, map_pow, hC]
  rcases hs with h | h
  · rw [h]
    simpa using le_imp_mul_pow_sub_le_of_c_le_one_mul_le (fun _ => (1 : (ValueGroupWithZero k)ˣ)) _ hc1
      (fun _ _ _ => by rw [one_mul]; exact hc1) i j hij
  · rw [h]
    exact le_imp_mul_pow_sub_le_of_c_le_one_mul_le (fun l => φ (t l)) _ hc1
      (lt_imp_mul_prod_le_of_b_le_one_le_a_mul_le (fun l => φ (t l)) (fun l => φ (w l)) hw1 hwa hwab) i j hij

private theorem thetaMap_dc {A M A' M' G : Type} [CommRing A] [AddCommGroup M] [Module A M] [CommRing A'] [AddCommGroup M']
    [Module A' M'] [Group G] (ρ : Representation A G M) (ρ' : Representation A' G M') (K K' : Subgroup G) (x : G)
    (hx : FinOrb K K' x) (f : M →+ M') (hf : ∀ g m, f (ρ g m) = ρ' g (f m)) (m : M) :
    dc ρ' K K' x (f m) = f (dc ρ K K' x m) := by
  haveI := hx.fintype
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [dc, finsum_eq_sum_of_fintype, LinearMap.sum_apply, map_sum, hf]

private theorem thetaMap_ext {A N A' N' T : Type} [CommRing A] [AddCommGroup N] [Module A N] [CommRing A'] [AddCommGroup N']
    [Module A' N'] [Group T] (θ : T →* (Module.End A N)ˣ) (θ' : T →* (Module.End A' N')ˣ) (g : N → N') (t b : T)
    (hb : ∀ m, (θ' b).val (g m) = g ((θ b).val m)) (ha : ∀ m, (θ' (b * t)).val (g m) = g ((θ (b * t)).val m)) (m : N) :
    (θ' t).val (g m) = g ((θ t).val m) := by
  have key : ∀ y, ((θ' b)⁻¹).val ((θ' b).val y) = y := fun y => by
    rw [← Module.End.mul_apply, ← Units.val_mul, inv_mul_cancel, Units.val_one, Module.End.one_apply]
  have h1 := ha m
  simp only [map_mul, Units.val_mul, Module.End.mul_apply] at h1
  rw [← hb] at h1
  rw [← key ((θ' t).val (g m)), h1, key]

theorem UpperTheory.V.Pa.Lev.thetaMap :
    ∀ (L : Type) [Field L] [NumberField L] (n q : ℕ) (w : Fin q → Plc L) (A M A' M' : Type) [CommRing A] [AddCommGroup M] [Module A M] [CommRing A'] [AddCommGroup M'] [Module A' M'] (ρ : Representation A (GV n w) M) (ρ' : Representation A' (GV n w) M') (C : ∀ j, Subgroup 𝓀[(w j).adicCompletion L]ˣ) (Θ) (Θ'), IsThetaQ ρ C Θ → IsThetaQ ρ' C Θ' → ∀ f : M →+ M', (∀ g m, f (ρ g m) = ρ' g (f m)) → ∀ j t (m : fixd ρ (UC n w C)) (m' : fixd ρ' (UC n w C)), (m' : M') = f m → ((Θ' j t).val m').val = f ((Θ j t).val m).val := by
  intro L _ _ n q w A M A' M' _ _ _ _ _ _ ρ ρ' C Θ Θ' hΘ hΘ' f hf j t m m' hm
  let g : fixd ρ (UC n w C) → fixd ρ' (UC n w C) := fun x =>
    ⟨f x, show ∀ u ∈ UC n w C, ρ' u (f x) = f x from fun u hu => by
      rw [← hf]
      exact congrArg f ((show ∀ u ∈ UC n w C, ρ u x = x from x.2) u hu)⟩
  have hdom : ∀ s, Dom s → ∀ x, (Θ' j s).val (g x) = g ((Θ j s).val x) := by
    intro s hs x
    apply Subtype.ext
    rw [hΘ'.1 j s hs (g x)]
    change _ = f (((Θ j s).val x : M))
    rw [hΘ.1 j s hs x]
    exact thetaMap_dc _ _ _ _ _ ((heckePairIwC _ n (C j)).1 _) f (fun g' y => hf _ y) x
  obtain ⟨c, hc⟩ := thetaMap_split t
  let b : Fin n → (HeightOneSpectrum.adicCompletion L (w j))ˣ := fun i => c ^ (n - (i : ℕ))
  have hb : Dom b := fun i i' h => by simpa [b] using hc 1 (Or.inl rfl) i i' h
  have hbt : Dom (b * t) := fun i i' h => by
    have := hc t (Or.inr rfl) i i' h
    simpa [b, Pi.mul_apply, mul_comm] using this
  have key := thetaMap_ext (Θ j) (Θ' j) g t b (hdom b hb) (hdom (b * t) hbt) m
  have hm' : m' = g m := Subtype.ext hm
  rw [hm', key]
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.NilpotentLevelLowering.TwoMul
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.N ValuativeRel IsLocalRing
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.LocGL GlobalTheory.GalOfCusp GlobalTheory.SmGL GlobalTheory.SplitWeil
open UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.Hi UpperTheory.V.AlgebraTools UpperTheory.V.Pa UpperTheory.V.Pa.Lev
open scoped TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

private theorem prod_pairs_dvd {A : Type} [CommRing A] {n : ℕ} (u : Fin n → A) (c : A) :
    ∏ p ∈ Hk.pairs n, (u p.2 - c * u p.1) ∣ ∏ i, ∏ i' ∈ Finset.univ.erase i, (u i - u i') * (u i - c * u i') := by
  have h1 : ∏ p ∈ Hk.pairs n, (u p.2 - c * u p.1) =
      ∏ i, ∏ i' ∈ Finset.univ.filter (fun i' => i' < i), (u i - c * u i') := by
    unfold Hk.pairs
    rw [Finset.prod_filter, ← Finset.univ_product_univ, Finset.prod_product_right]
    refine Finset.prod_congr rfl fun i _ => ?_
    rw [Finset.prod_filter]
  rw [h1]
  refine Finset.prod_dvd_prod_of_dvd _ _ fun i _ => ?_
  refine (Finset.prod_dvd_prod_of_subset _ (Finset.univ.erase i) _ ?_).trans
    (Finset.prod_dvd_prod_of_dvd _ _ fun i' _ => dvd_mul_left _ _)
  intro i' hi'
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi'
  simp [hi'.ne]

private theorem twoMaps_of_dvd {R B M V : Type} [CommRing R] [CommRing B] [AddCommGroup M] [Module B M] [AddCommGroup V]
    [Module R V] {q n : ℕ} (β : R →+* B) (P : Fin q → Polynomial B) (act : PU R q n →ₐ[R] Module.End R V) {f g : PU R q n}
    (hfg : f ∣ g) (h : TwoMaps (M := M) β P act f) : TwoMaps (M := M) β P act g := by
  obtain ⟨c, rfl⟩ := hfg
  obtain ⟨φ, ψ, h1, h2, h3, h4⟩ := h
  refine ⟨φ, ψ.comp (act c).toAddMonoidHom, h1, fun t v => ?_, fun v => ?_, fun z => ?_⟩
  · show ψ (act c (act t v)) = _ • ψ (act c v)
    rw [← h2, ← Module.End.mul_apply, ← Module.End.mul_apply, ← map_mul, ← map_mul, mul_comm]
  · show φ (ψ (act c v)) = _
    rw [h3, map_mul, Module.End.mul_apply]
  · show ψ (act c (φ z)) = _
    rw [h2, h4, mul_comm f c, map_mul, map_mul, mul_smul]

theorem UpperTheory.V.Pa.Lev.twoMul :
    ∀ (O R B M V : Type) [CommRing O] [CommRing R] [Algebra O R] [CommRing B] [AddCommGroup M] [Module B M] [AddCommGroup V] [Module R V] (q n : ℕ) (β : R →+* B) (P : Fin q → Polynomial B) (act : PU R q n →ₐ[R] Module.End R V) (Nq : Fin q → ℕ), TwoMaps (M := M) β P act (∏ j, emb O R j (Hk.NN n (Nq j : O))) → TwoMaps (M := M) β P act (fEl Nq fun j i => MvPolynomial.X (j, i)) := by
  intro O R B M V _ _ _ _ _ _ _ _ q n β P act Nq h
  refine twoMaps_of_dvd β P act ?_ h
  unfold fEl
  refine Finset.prod_dvd_prod_of_dvd _ _ fun j _ => ?_
  have e : emb O R j (Hk.NN n (Nq j : O)) = ∏ p ∈ Hk.pairs n,
      ((MvPolynomial.X (j, p.2) : PU R q n) - (Nq j : PU R q n) * MvPolynomial.X (j, p.1)) := by
    unfold Hk.NN
    rw [map_prod]
    refine Finset.prod_congr rfl fun p _ => ?_
    simp [emb]
  rw [e]
  exact prod_pairs_dvd (fun i => (MvPolynomial.X (j, i) : PU R q n)) _
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.NilpotentLevelLowering.WdChar
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.N ValuativeRel IsLocalRing
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.LocGL GlobalTheory.GalOfCusp GlobalTheory.SmGL GlobalTheory.SplitWeil
open UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.Hi UpperTheory.V.AlgebraTools UpperTheory.V.Pa UpperTheory.V.Pa.Lev
open scoped TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

private theorem unip_eq_one {n d : ℕ} (M : Matrix (Fin n) (Fin n) ℂ) (hd : d ≠ 0) (h1 : M ^ d = 1)
    (hc : M.charpoly = (Polynomial.X - 1) ^ n) : M = 1 := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · exact Subsingleton.elim _ _
  have hsep : (Polynomial.X ^ d - Polynomial.C (1 : ℂ)).Separable :=
    Polynomial.separable_X_pow_sub_C 1 (Nat.cast_ne_zero.mpr hd) one_ne_zero
  have h1' : minpoly ℂ M ∣ Polynomial.X ^ d - Polynomial.C 1 := minpoly.dvd ℂ M (by simp [h1])
  have hsq : Squarefree (minpoly ℂ M) := hsep.squarefree.squarefree_of_dvd h1'
  have h2 : minpoly ℂ M ∣ (Polynomial.X - 1) ^ n := hc ▸ Matrix.minpoly_dvd_charpoly M
  have h3 : minpoly ℂ M ∣ Polynomial.X - 1 := (hsq.dvd_pow_iff_dvd hn.ne').mp h2
  have h4 := (minpoly.dvd_iff).mp h3
  simpa [sub_eq_zero] using h4

theorem UpperTheory.V.Pa.Lev.wdChar :
    ∀ (l : ℕ) [Fact l.Prime] (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (Bq : ValuationSubring Ω) (w : HeightOneSpectrum (𝓞 E)) (hB : IsPlaceOver Bq w), ((l : ℕ) : 𝓞 E) ∉ w.asIdeal → ∀ (n : ℕ) (ι : Qbar l ≃+* ℂ) (r : G E Ω →* GL (Fin n) (Qbar l)) (x : WD hB), IsWDOf ι r x → (∀ σ : Weil hB, ((r σ : Matrix (Fin n) (Fin n) (Qbar l)).map ι).charpoly = x.charPol σ) ∧ ∀ σ ∈ GlobalTheory.TameQuot.ineKer E Bq l, ((r σ : Matrix (Fin n) (Fin n) (Qbar l)).map ι).charpoly = (Polynomial.X - 1) ^ n → r σ = 1 := by
  intro l _ E Ω _ _ _ _ _ Bq w hB hl n ι r x hx
  have hxe : wdOf (h := hB) hl ι r = x := IsWDOf.wdOf_eq hl hx
  obtain ⟨t, ht, φ, hφ, N, a, hmon, -, -⟩ := hx
  constructor
  · intro σ
    rw [← hxe, IsMonodromy.charPol_wdOf hl ht hmon ι σ]
    exact Matrix.charpoly_map _ ι.toRingHom
  · intro σ hσ hc
    have hσI : σ ∈ Ine Bq := GlobalTheory.TameQuot.ineKer_le_Ine Bq l hσ
    let τ : Ine Bq := ⟨σ, hσI⟩
    have htτ : t τ = 1 := (GlobalTheory.TameQuot.eq_one_iff_mem_ineKer E Ω l Bq w hB hl t ht.1 ht.2 τ).mpr hσ
    have hval : tval t τ = 0 := by simp [tval, htτ]
    obtain ⟨-, U, hU, hUr⟩ := hmon
    haveI := compactSpace_Ine (E := E) Bq
    haveI : Finite (Ine Bq ⧸ U) := Subgroup.quotient_finite_of_isOpen U hU
    haveI : U.FiniteIndex := Subgroup.finiteIndex_of_finite_quotient
    have hd : U.normalCore.index ≠ 0 := Subgroup.FiniteIndex.index_ne_zero
    have hpow : τ ^ U.normalCore.index ∈ U := U.normalCore_le (U.normalCore.pow_index_mem τ)
    have hr : (r σ : Matrix (Fin n) (Fin n) (Qbar l)) ^ U.normalCore.index = 1 := by
      have := hUr _ hpow
      rw [tval_pow, hval, mul_zero, zero_smul, IsNilpotent.exp_zero, Subgroup.coe_pow, map_pow,
        Units.val_pow_eq_pow_val] at this
      exact this
    have hM : (r σ : Matrix (Fin n) (Fin n) (Qbar l)).map ι = 1 := by
      apply unip_eq_one _ hd _ hc
      have e : (r σ : Matrix (Fin n) (Fin n) (Qbar l)).map ι = ι.toRingHom.mapMatrix (r σ : Matrix (Fin n) (Fin n) (Qbar l)) := rfl
      rw [e, ← map_pow, hr, map_one]
    apply Units.ext
    refine Matrix.map_injective ι.injective ?_
    show (r σ : Matrix (Fin n) (Fin n) (Qbar l)).map ι = (1 : Matrix (Fin n) (Fin n) (Qbar l)).map ι
    rw [hM, Matrix.map_one _ (map_zero ι) (map_one ι)]
end

