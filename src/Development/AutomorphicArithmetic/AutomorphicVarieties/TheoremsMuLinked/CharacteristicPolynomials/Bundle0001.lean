module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.WeilGroupCharacters.ContinuousResP
public import Development.AutomorphicArithmetic.AutomorphicVarieties.LevelCohomology.Bundle0002
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0218
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.DeterminantPadicFree.Bundle0003
public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.LocalRingsCompletion.Bundle0001
public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.LocalRingsCompletion.Bundle0002

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.TheoremsMuLinked.CharacteristicPolynomials.CocField
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal IsLocalRing Polynomial Matrix UpperTheory.V UpperTheory.V.HV UpperTheory.V.Alg GlobalTheory.GalOfCusp

private theorem cf_small {l : ℕ} [hl : Fact l.Prime] (C : ℝ) : ∃ N : ℕ, ‖((l : PadicAlgCl l)) ^ N‖ * C ≤ 1 := by
  have hn : ‖((l : ℕ) : PadicAlgCl l)‖ = (l : ℝ)⁻¹ := by
    have h := PadicAlgCl.valuation_coe l (l : PadicAlgCl l)
    rw [PadicAlgCl.valuation_p] at h
    rw [← h]
    simp
  have hl1 : (1 : ℝ) < l := by exact_mod_cast hl.out.one_lt
  have hr : ‖((l : ℕ) : PadicAlgCl l)‖ < 1 := by
    rw [hn]
    exact inv_lt_one_of_one_lt₀ hl1
  rcases le_or_gt C 0 with hC | hC
  · exact ⟨0, by simp; linarith⟩
  · obtain ⟨N, hN⟩ := exists_pow_lt_of_lt_one (inv_pos.mpr hC) hr
    refine ⟨N, ?_⟩
    rw [norm_pow]
    calc ‖((l : ℕ) : PadicAlgCl l)‖ ^ N * C ≤ C⁻¹ * C :=
          mul_le_mul_of_nonneg_right hN.le hC.le
      _ = 1 := inv_mul_cancel₀ hC.ne'

private theorem padicAlgCl_norm_le_one_of_isIntegral {l : ℕ} [Fact l.Prime] (x : PadicAlgCl l) (hx : IsIntegral ℤ_[l] x) :
    ‖x‖ ≤ 1 := by
  obtain ⟨p, hpm, hp⟩ := hx
  by_contra h
  push_neg at h
  rw [← Polynomial.aeval_def, Polynomial.aeval_eq_sum_range, Finset.sum_range_succ,
    hpm.coeff_natDegree, one_smul] at hp
  have hn0 : p.natDegree ≠ 0 := by
    intro h0
    rw [h0] at hp
    simp at hp
  have hxn : x ^ p.natDegree = -∑ i ∈ Finset.range p.natDegree, p.coeff i • x ^ i := by
    linear_combination hp
  have h1 : 1 ≤ ‖x‖ := h.le
  have hb : ‖∑ i ∈ Finset.range p.natDegree, p.coeff i • x ^ i‖ ≤ ‖x‖ ^ (p.natDegree - 1) := by
    apply IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg (by positivity)
    intro i hi
    rw [Finset.mem_range] at hi
    rw [Algebra.smul_def, norm_mul, norm_pow]
    have ha : ‖algebraMap ℤ_[l] (PadicAlgCl l) (p.coeff i)‖ ≤ 1 := by
      rw [IsScalarTower.algebraMap_apply ℤ_[l] ℚ_[l] (PadicAlgCl l), norm_algebraMap']
      simpa using PadicInt.norm_le_one (p.coeff i)
    calc ‖algebraMap ℤ_[l] (PadicAlgCl l) (p.coeff i)‖ * ‖x‖ ^ i
        ≤ 1 * ‖x‖ ^ (p.natDegree - 1) :=
          mul_le_mul ha (pow_le_pow_right₀ h1 (by omega)) (by positivity) zero_le_one
      _ = ‖x‖ ^ (p.natDegree - 1) := one_mul _
  have h2 : ‖x‖ ^ p.natDegree ≤ ‖x‖ ^ (p.natDegree - 1) := by
    rw [← norm_pow, hxn, norm_neg]
    exact hb
  have h3 : ‖x‖ ^ (p.natDegree - 1) < ‖x‖ ^ p.natDegree := pow_lt_pow_right₀ h (by omega)
  linarith

private theorem cf_field {l : ℕ} [Fact l.Prime] (c : Coef l) :
    ∃ E : IntermediateField ℚ_[l] (PadicAlgCl l), FiniteDimensional ℚ_[l] E ∧ ∀ x ∈ c.O, x ∈ E ∧ ‖x‖ ≤ 1 := by
  haveI := c.fin
  obtain ⟨S, hS⟩ := Module.Finite.fg_top (R := ℤ_[l]) (M := c.O)
  let T : Set (PadicAlgCl l) := Subtype.val '' (S : Set c.O)
  haveI : Finite T := (S.finite_toSet.image _).to_subtype
  refine ⟨IntermediateField.adjoin ℚ_[l] T,
    IntermediateField.finiteDimensional_adjoin (fun x _ => Algebra.IsIntegral.isIntegral x), ?_⟩
  have key : ∀ y ∈ Submodule.span ℤ_[l] (S : Set c.O),
      ((y : c.O) : PadicAlgCl l) ∈ IntermediateField.adjoin ℚ_[l] T := by
    intro y hy
    induction hy using Submodule.span_induction with
    | mem y hy => exact IntermediateField.subset_adjoin _ _ ⟨y, hy, rfl⟩
    | zero => simp
    | add y z _ _ hy hz => simpa using add_mem hy hz
    | smul a y _ hy =>
        rw [Subalgebra.coe_smul, Algebra.smul_def,
          IsScalarTower.algebraMap_apply ℤ_[l] ℚ_[l] (PadicAlgCl l)]
        exact mul_mem (IntermediateField.algebraMap_mem _ _) hy
  intro x hx
  refine ⟨key ⟨x, hx⟩ (hS ▸ Submodule.mem_top), padicAlgCl_norm_le_one_of_isIntegral x ?_⟩
  have hi := IsIntegral.of_finite ℤ_[l] (⟨x, hx⟩ : c.O)
  simpa using hi.map c.O.val

private theorem cf_entries {l : ℕ} [Fact l.Prime] {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [CompactSpace G] [T2Space G] {m : ℕ} (s : G →* Matrix (Fin m) (Fin m) (PadicAlgCl l)) (z : G → Fin m → PadicAlgCl l)
    (hs : Continuous s) (hz : Continuous z) (hc : ∀ g h, z (g * h) = z g + s g *ᵥ z h) :
    ∃ E : IntermediateField ℚ_[l] (PadicAlgCl l), FiniteDimensional ℚ_[l] E ∧ ∀ g i, z g i ∈ E := by
  classical
  let e : Fin m ⊕ Fin 1 ≃ Fin (m + 1) := finSumFinEquiv
  let B : G → Matrix (Fin m ⊕ Fin 1) (Fin m ⊕ Fin 1) (PadicAlgCl l) := fun g =>
    Matrix.fromBlocks (s g) (Matrix.replicateCol (Fin 1) (z g)) 0 1
  have hz1 : z 1 = 0 := by simpa using hc 1 1
  have hB1 : B 1 = 1 := by
    have hcol : Matrix.replicateCol (Fin 1) (z 1) = 0 := by
      ext i j
      simp [hz1]
    simp only [B, map_one, hcol, Matrix.fromBlocks_one]
  have hBmul : ∀ g h, B (g * h) = B g * B h := by
    intro g h
    simp only [B, Matrix.fromBlocks_multiply, map_mul]
    congr 1
    · simp
    · ext i j
      simp [hc, Matrix.mul_apply, Matrix.mulVec, dotProduct, add_comm]
    · simp
    · simp
  let f : G →* Matrix (Fin (m + 1)) (Fin (m + 1)) (PadicAlgCl l) :=
    { toFun := fun g => Matrix.reindexAlgEquiv ℚ_[l] (PadicAlgCl l) e (B g)
      map_one' := by simp only [hB1, map_one]
      map_mul' := fun g h => by simp only [hBmul, map_mul] }
  obtain ⟨K, hK, hmem⟩ :=
    GlobalTheory.CompactRepField.exists_finiteDimensional_entries_mem l G (m + 1) f.toHomUnits (by
      intro i j
      change Continuous fun g => B g (e.symm i) (e.symm j)
      generalize e.symm i = a
      generalize e.symm j = b
      rcases a with a | a <;> rcases b with b | b
      · simp only [B, Matrix.fromBlocks_apply₁₁]
        exact hs.matrix_elem a b
      · simp only [B, Matrix.fromBlocks_apply₁₂, Matrix.replicateCol_apply]
        exact (continuous_apply a).comp hz
      · simp only [B, Matrix.fromBlocks_apply₂₁]
        exact continuous_const
      · simp only [B, Matrix.fromBlocks_apply₂₂]
        exact continuous_const)
  refine ⟨K, hK, fun g i => ?_⟩
  have h := hmem g (e (Sum.inl i)) (e (Sum.inr 0))
  change B g (e.symm (e (Sum.inl i))) (e.symm (e (Sum.inr 0))) ∈ K at h
  simpa [B] using h

theorem UpperTheory.V.Th.Det.cocField :
    ∀ {l : ℕ} [Fact l.Prime] (c : Coef l) {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G] [T2Space G] {m : ℕ} (σ : G →* GL (Fin m) (Qbar l)) (z : G → Fin m → Qbar l), Continuous σ → Continuous z → (∀ g h, z (g * h) = z g + W.mat σ g *ᵥ z h) → ∃ (c' : Coef l) (a : Qbar l), c.O ≤ c'.O ∧ a ≠ 0 ∧ ∀ g i, a * z g i ∈ c'.O := by
  intro l _ c G _ _ _ _ _ m σ z hσ hz hc
  obtain ⟨E1, hE1, hz1⟩ := cf_entries (W.mat σ) z (Units.continuous_val.comp hσ) hz hc
  obtain ⟨E2, hE2, hO⟩ := cf_field c
  haveI := hE1
  haveI := hE2
  obtain ⟨c', hc'⟩ := X.So.coefOf l (E1 ⊔ E2)
  obtain ⟨C, hC⟩ := isCompact_univ.exists_bound_of_continuousOn hz.continuousOn
  obtain ⟨N, hN⟩ := cf_small (l := l) C
  refine ⟨c', ((l : ℕ) : PadicAlgCl l) ^ N, ?_, ?_, ?_⟩
  · intro x hx
    obtain ⟨h1, h2⟩ := hO x hx
    exact (hc' x).mpr ⟨(le_sup_right : E2 ≤ E1 ⊔ E2) h1, h2⟩
  · exact pow_ne_zero _ (Nat.cast_ne_zero.mpr (Fact.out : l.Prime).ne_zero)
  · intro g i
    rw [hc']
    constructor
    · exact mul_mem (pow_mem (natCast_mem _ l) N) ((le_sup_left : E1 ≤ E1 ⊔ E2) (hz1 g i))
    · rw [norm_mul]
      calc ‖((l : ℕ) : PadicAlgCl l) ^ N‖ * ‖z g i‖ ≤ ‖((l : ℕ) : PadicAlgCl l) ^ N‖ * C :=
            mul_le_mul_of_nonneg_left
              ((norm_le_pi_norm (z g) i).trans (hC g (Set.mem_univ _))) (norm_nonneg _)
        _ ≤ 1 := hN
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.TheoremsMuLinked.CharacteristicPolynomials.ContinuousCocyclesFgIntegralOfPhiCond
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal IsLocalRing Polynomial Matrix UpperTheory.V UpperTheory.V.HV UpperTheory.V.Alg GlobalTheory.GalOfCusp

private theorem mem_pow_smul {A M : Type} [CommRing A] [AddCommGroup M] [Module A M] (t : A) (N : ℕ) (x : M) :
    x ∈ (Ideal.span {t} ^ N • (⊤ : Submodule A M)) ↔ ∃ y, t ^ N • y = x := by
  rw [Ideal.span_singleton_pow, Submodule.ideal_span_singleton_smul, Submodule.mem_smul_pointwise_iff_exists]
  constructor
  · rintro ⟨y, -, hy⟩
    exact ⟨y, hy⟩
  · rintro ⟨y, hy⟩
    exact ⟨y, Submodule.mem_top, hy⟩

private theorem mem_smul_top_pi {R : Type} [CommRing R] (J : Ideal R) {r : ℕ} (x : Fin r → R) :
    x ∈ J • (⊤ : Submodule R (Fin r → R)) ↔ ∀ i, x i ∈ J := by
  constructor
  · intro hx
    refine Submodule.smul_induction_on hx ?_ ?_
    · intro r hr n _ i
      simpa using J.mul_mem_right (n i) hr
    · intro a b ha hb i
      simpa using J.add_mem (ha i) (hb i)
  · intro hx
    have hsum : x = ∑ i, x i • (Pi.single i (1 : R) : Fin r → R) := by
      ext j
      simp [Finset.sum_apply, Pi.single_apply]
    rw [hsum]
    exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem_smul (hx i) Submodule.mem_top

private theorem lc_iff {R G : Type} [CommRing R] [TopologicalSpace G] (J : Ideal R) {r : ℕ} (f : G → Fin r → R) :
    (IsLocallyConstant fun g => (J • (⊤ : Submodule R (Fin r → R))).mkQ (f g)) ↔
      ∀ i, IsLocallyConstant fun g => Ideal.Quotient.mk J (f g i) := by
  have key : ∀ a b : Fin r → R, (J • (⊤ : Submodule R (Fin r → R))).mkQ a = (J • (⊤ : Submodule R (Fin r → R))).mkQ b ↔
      ∀ i, Ideal.Quotient.mk J (a i) = Ideal.Quotient.mk J (b i) := by
    intro a b
    simp only [Submodule.mkQ_apply, Submodule.Quotient.eq, Ideal.Quotient.eq, mem_smul_top_pi]
    rfl
  simp only [IsLocallyConstant.iff_eventually_eq, key]
  constructor
  · intro h i x
    exact (h x).mono fun y hy => hy i
  · intro h x
    exact Filter.eventually_all.mpr fun i => h i x

private theorem cocycles_finitely_generated (l : ℕ) [Fact l.Prime] {R G M : Type} [CommRing R] [IsDomain R] [IsLocalRing R]
    [IsNoetherianRing R] [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G]
    [TotallyDisconnectedSpace G] [AddCommGroup M] [Module R M] [Module.Free R M] [Module.Finite R M]
    (t : R) (I : Ideal R) (hI : I = Ideal.span {t}) (ht0 : t ≠ 0) (hIne : I ≠ ⊤) [IsPrecomplete I R]
    (hfq : Finite (R ⧸ I)) (hlI : (l : R) ∈ I)
    (ρ : G →* Module.End R M) (Z : Submodule R (G → M)) (hΦ : PhiCond G l)
    (hρ : ∀ (N : ℕ) m, IsLocallyConstant fun g => (I ^ N • (⊤ : Submodule R M)).mkQ (ρ g m))
    (hZ : ∀ z ∈ Z, (∀ N : ℕ, IsLocallyConstant fun g => (I ^ N • (⊤ : Submodule R M)).mkQ (z g)) ∧
      ∀ g h, z (g * h) = z g + ρ g (z h)) : Z.FG := by
  subst hI
  have htinj : ∀ x : M, t • x = 0 → x = 0 := by
    intro x hx
    let b := Module.Free.chooseBasis R M
    apply b.repr.injective
    ext i
    have h := congrArg (fun y => b.repr y i) hx
    simp only [map_smul, Finsupp.smul_apply, smul_eq_mul, map_zero, Finsupp.coe_zero, Pi.zero_apply] at h
    simpa using (mul_eq_zero.mp h).resolve_left ht0
  have hcancel : ∀ a b : M, t • a = t • b → a = b := fun a b h =>
    sub_eq_zero.mp (htinj _ (by rw [smul_sub, h, sub_self]))
  have hMh : ∀ x : M, (∀ n : ℕ, ∃ y, t ^ n • y = x) → x = 0 := by
    intro x hx
    have hle : Ideal.span {t} ≤ (⊥ : Ideal R).jacobson := by
      rw [IsLocalRing.jacobson_eq_maximalIdeal ⊥ bot_ne_top]
      exact IsLocalRing.le_maximalIdeal hIne
    have h := Ideal.iInf_pow_smul_eq_bot_of_le_jacobson (M := M) _ (by simpa only [Ideal.jacobson_bot] using hle)
    have hx' : x ∈ ⨅ i, Ideal.span {t} ^ i • (⊤ : Submodule R M) :=
      (Submodule.mem_iInf _).mpr fun n => (mem_pow_smul t n x).mpr (hx n)
    rw [h] at hx'
    simpa using hx'
  let C : Submodule R (G → M) :=
    { carrier := {z | (∀ N : ℕ, IsLocallyConstant fun g => (Ideal.span {t} ^ N • (⊤ : Submodule R M)).mkQ (z g)) ∧
        ∀ g h, z (g * h) = z g + ρ g (z h)}
      add_mem' := by
        rintro a b ⟨ha1, ha2⟩ ⟨hb1, hb2⟩
        refine ⟨fun N => ?_, fun g h => ?_⟩
        · simp only [Pi.add_apply, map_add (f := _)]
          exact (ha1 N).add (hb1 N)
        · simp only [Pi.add_apply, ha2, hb2, map_add (f := _)]
          abel
      zero_mem' := ⟨fun N => by
          simp only [Pi.zero_apply, map_zero]
          exact IsLocallyConstant.const 0,
        fun g h => by simp⟩
      smul_mem' := by
        rintro r a ⟨ha1, ha2⟩
        refine ⟨fun N => ?_, fun g h => ?_⟩
        · simp only [Pi.smul_apply, map_smul]
          exact (ha1 N).comp (fun q => r • q)
        · simp only [Pi.smul_apply, ha2, smul_add, map_smul] }
  have hZC : Z ≤ C := fun z hz => hZ z hz
  haveI : Finite (R ⧸ Ideal.span {t}) := hfq
  haveI hM'fin : Finite (M ⧸ Ideal.span {t} • (⊤ : Submodule R M)) := Module.finite_of_finite (R ⧸ Ideal.span {t})
  let ρ' : G →* AddMonoid.End (M ⧸ Ideal.span {t} • (⊤ : Submodule R M)) :=
    { toFun := fun g => ((Ideal.span {t} • (⊤ : Submodule R M)).mapQ _ (ρ g)
        (Submodule.smul_top_le_comap_smul_top _ _)).toAddMonoidHom
      map_one' := by
        refine AddMonoidHom.ext fun x => ?_
        induction x using Submodule.Quotient.induction_on with
        | H x =>
          simp
          rfl
      map_mul' := by
        intro g h
        refine AddMonoidHom.ext fun x => ?_
        induction x using Submodule.Quotient.induction_on with
        | H x =>
          simp [Module.End.mul_apply]
          rfl }
  have hρ' : ∀ g x, ρ' g (Submodule.Quotient.mk x) = Submodule.Quotient.mk (ρ g x) := fun g x => rfl
  have hS := UpperTheory.V.Pa.Det.locallyConstant_cocycles_finite_of_phi l ρ' hΦ
    (by
      intro m
      induction m using Submodule.Quotient.induction_on with
      | H x =>
        rw [← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero, ← Nat.cast_smul_eq_nsmul R]
        exact Submodule.smul_mem_smul hlI Submodule.mem_top)
    (by
      intro m
      induction m using Submodule.Quotient.induction_on with
      | H x =>
        have h1 := hρ 1 x
        rw [pow_one] at h1
        exact h1)
  let Ψ : C →ₗ[R] (G → M ⧸ Ideal.span {t} • (⊤ : Submodule R M)) :=
    LinearMap.pi fun g => (Ideal.span {t} • (⊤ : Submodule R M)).mkQ ∘ₗ (LinearMap.proj g ∘ₗ C.subtype)
  have hΨ : ∀ z g, Ψ z g = Submodule.Quotient.mk (z.1 g) := fun z g => rfl
  have hrange : ∀ z, Ψ z ∈ {z : G → M ⧸ Ideal.span {t} • (⊤ : Submodule R M) | IsLocallyConstant z ∧
      ∀ g h, z (g * h) = z g + ρ' g (z h)} := by
    intro z
    obtain ⟨hz1, hz2⟩ := z.2
    refine ⟨?_, fun g h => ?_⟩
    · have h1 := hz1 1
      rw [pow_one] at h1
      exact h1
    · rw [hΨ, hΨ, hΨ, hz2, hρ', Submodule.Quotient.mk_add]
  have hker : LinearMap.ker Ψ = Ideal.span {t} • (⊤ : Submodule R C) := by
    apply le_antisymm
    · intro z hz
      have hz' : ∀ g, ∃ y, t • y = z.1 g := by
        intro g
        have h0 : Ψ z g = 0 := congrFun (LinearMap.mem_ker.mp hz) g
        rw [hΨ, Submodule.Quotient.mk_eq_zero, ← pow_one (Ideal.span {t})] at h0
        obtain ⟨y, hy⟩ := (mem_pow_smul t 1 _).mp h0
        exact ⟨y, by simpa using hy⟩
      choose y hy using hz'
      obtain ⟨hz1, hz2⟩ := z.2
      have hyC : y ∈ C := by
        refine ⟨fun N => ?_, fun g h => ?_⟩
        · rw [IsLocallyConstant.iff_eventually_eq]
          intro x
          filter_upwards [(IsLocallyConstant.iff_eventually_eq _).mp (hz1 (N + 1)) x] with g hg
          rw [Submodule.mkQ_apply, Submodule.mkQ_apply, Submodule.Quotient.eq] at hg ⊢
          obtain ⟨w, hw⟩ := (mem_pow_smul t (N + 1) _).mp hg
          refine (mem_pow_smul t N _).mpr ⟨w, hcancel _ _ ?_⟩
          rw [smul_sub, hy, hy, ← hw, ← mul_smul, ← pow_succ']
        · apply hcancel
          rw [hy (g * h), smul_add, ← map_smul, hy g, hy h]
          exact hz2 g h
      have hzt : z = t • (⟨y, hyC⟩ : C) := Subtype.ext (funext fun g => (hy g).symm)
      rw [hzt]
      exact Submodule.smul_mem_smul (Ideal.mem_span_singleton_self t) Submodule.mem_top
    · intro z hz
      refine Submodule.smul_induction_on hz ?_ ?_
      · intro r hr n _
        rw [LinearMap.mem_ker, map_smul]
        funext g
        rw [Pi.smul_apply, hΨ, ← Submodule.Quotient.mk_smul, Pi.zero_apply, Submodule.Quotient.mk_eq_zero]
        exact Submodule.smul_mem_smul hr Submodule.mem_top
      · intro a b ha hb
        exact add_mem ha hb
  have hfin : Finite (C ⧸ LinearMap.ker Ψ) := by
    have hsub : (LinearMap.range Ψ : Set _) ⊆ {z : G → M ⧸ Ideal.span {t} • (⊤ : Submodule R M) | IsLocallyConstant z ∧
        ∀ g h, z (g * h) = z g + ρ' g (z h)} := by
      rintro _ ⟨z, rfl⟩
      exact hrange z
    haveI : Finite (LinearMap.range Ψ) := (hS.subset hsub).to_subtype
    exact Finite.of_equiv _ Ψ.quotKerEquivRange.symm.toEquiv
  rw [hker] at hfin
  haveI : IsHausdorff (Ideal.span {t}) C := by
    refine ⟨fun x hx => ?_⟩
    apply Subtype.ext
    funext g
    show x.1 g = 0
    apply hMh
    intro n
    have h1 := hx n
    rw [SModEq.sub_mem, sub_zero] at h1
    obtain ⟨y, hy⟩ := (mem_pow_smul t n x).mp h1
    exact ⟨y.1 g, by rw [← hy]; rfl⟩
  haveI : Module.Finite R (C ⧸ Ideal.span {t} • (⊤ : Submodule R C)) := Module.Finite.of_finite
  have hCfin : Module.Finite R C := (UpperTheory.V.abelian₂.nakayama R (Ideal.span {t}) C).2 this
  have hCfg : C.FG := Module.Finite.iff_fg.mp hCfin
  haveI := isNoetherian_of_fg_of_noetherian C hCfg
  have hZ'fg : (Z.comap C.subtype).FG := IsNoetherian.noetherian _
  have hZeq : Submodule.map C.subtype (Z.comap C.subtype) = Z :=
    Submodule.map_comap_eq_of_le (by rwa [Submodule.range_subtype])
  rw [← hZeq]
  exact hZ'fg.map _

theorem UpperTheory.V.Th.Det.continuousCocycles_fg_integral_of_phiCond :
    ∀ {l : ℕ} [Fact l.Prime] (c : Coef l) {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G] [TotallyDisconnectedSpace G] {m : ℕ} (σ : G →* GL (Fin m) c.O) (Z : Submodule c.O (G → Fin m → c.O)), PhiCond G l → (∀ i j, AdicCont (maximalIdeal c.O) fun g => W.mat σ g i j) → (∀ z ∈ Z, (∀ i, AdicCont (maximalIdeal c.O) fun g => z g i) ∧ ∀ g h, z (g * h) = z g + W.mat σ g *ᵥ z h) → Z.FG := by
  intro l _ c G _ _ _ _ _ m σ Z hΦ hσ hZ
  obtain ⟨hc, hf, hl, -⟩ := UpperTheory.V.abelian₂.dvr_finite l c.O
  obtain ⟨t, ht⟩ := IsDiscreteValuationRing.exists_irreducible c.O
  haveI : IsPrecomplete (maximalIdeal c.O) c.O := hc.toIsPrecomplete
  let ρ : G →* Module.End c.O (Fin m → c.O) :=
    (Matrix.toLinAlgEquiv' (R := c.O) (n := Fin m)).toAlgHom.toRingHom.toMonoidHom.comp (W.mat σ)
  have hρ : ∀ g x, ρ g x = W.mat σ g *ᵥ x := fun g x => rfl
  refine cocycles_finitely_generated l t (maximalIdeal c.O) ht.maximalIdeal_eq ht.ne_zero (maximalIdeal.isMaximal c.O).ne_top
    hf hl ρ Z hΦ (fun N x => ?_) (fun z hz => ⟨fun N => ?_, fun g h => ?_⟩)
  · rw [lc_iff]
    intro i
    rw [IsLocallyConstant.iff_eventually_eq]
    intro g
    filter_upwards [Filter.eventually_all.2 fun j => (hσ i j N).eventually_eq g] with g' hg'
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [hρ, Matrix.mulVec, dotProduct, map_sum, map_mul, hg']
  · rw [lc_iff]
    exact fun i => (hZ z hz).1 i N
  · rw [hρ]; exact (hZ z hz).2 g h
end

