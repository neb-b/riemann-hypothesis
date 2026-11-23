module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.EpsilonEtaMatrices.EpsilonEtaTensorDual
public import Development.AutomorphicArithmetic.AutomorphicVarieties.Bundle0001
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.DeterminantPadicFree.Bundle0007

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.DegreeCountCohomology.AdExExt
section
open Matrix Filter NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.Pa

private theorem conj_eq_transpose_conj_of_transpose_mul_eq_smul_one {n : ℕ} {R : Type} [CommRing R] (P Q P' Q' X : Matrix (Fin n) (Fin n) R) (a b : R)
    (hPQ : P * Q = 1) (hQP : Q * P = 1) (hPQ' : P' * Q' = 1) (ha : Pᵀ * P' = a • 1) (hb : Qᵀ * Q' = b • 1) :
    P' * (X * Q') = Qᵀ * (X * Pᵀ) := by
  have h1 : P' = a • Qᵀ := by
    calc P' = (Qᵀ * Pᵀ) * P' := by rw [← Matrix.transpose_mul, hPQ, Matrix.transpose_one, Matrix.one_mul]
      _ = Qᵀ * (Pᵀ * P') := Matrix.mul_assoc _ _ _
      _ = a • Qᵀ := by rw [ha, Matrix.mul_smul, Matrix.mul_one]
  have h2 : Q' = b • Pᵀ := by
    calc Q' = (Pᵀ * Qᵀ) * Q' := by rw [← Matrix.transpose_mul, hQP, Matrix.transpose_one, Matrix.one_mul]
      _ = Pᵀ * (Qᵀ * Q') := Matrix.mul_assoc _ _ _
      _ = b • Pᵀ := by rw [hb, Matrix.mul_smul, Matrix.mul_one]
  have h3 : P' * Q' = (a * b) • (1 : Matrix (Fin n) (Fin n) R) := by
    rw [h1, h2, Matrix.smul_mul, Matrix.mul_smul, smul_smul, ← Matrix.transpose_mul, hPQ, Matrix.transpose_one]
  rw [hPQ'] at h3
  rw [h1, h2]
  calc a • Qᵀ * (X * b • Pᵀ) = ((a * b) • (1 : Matrix (Fin n) (Fin n) R)) * (Qᵀ * (X * Pᵀ)) := by
        simp only [Matrix.smul_mul, Matrix.mul_smul, Matrix.one_mul, smul_smul, mul_comm]
    _ = Qᵀ * (X * Pᵀ) := by rw [← h3, Matrix.one_mul]

theorem UpperTheory.V.Pa.adEx :
    ∀ (l : ℕ) [Fact l.Prime] (F : GFrame l) (A R : Type) [CommRing A] [CommRing R] [Algebra A R] (n : ℕ) (ρ : F.G₀ → Matrix (Fin n) (Fin n) R) (χ : F.Γ → R) (V : Submodule A (Matrix (Fin n) (Fin n) R)), AdOk F ρ χ V → ∃ rep : Representation A F.Γ V, IsAd F ρ χ V rep := by
  intro l _ F A R _ _ _ n ρ χ V hV
  obtain ⟨h1, hmul, hform, hχ1, hχmul, had, htr⟩ := hV
  have hcinv : F.c⁻¹ = F.c := inv_eq_of_mul_eq_one_right F.c_sq
  have hχc : χ F.c * χ F.c = 1 := by rw [← hχmul, F.c_sq, hχ1]
  have hρr : ∀ g : F.G₀, ρ g * ρ g⁻¹ = 1 := fun g => by rw [← hmul, mul_inv_cancel, h1]
  have hρl : ∀ g : F.G₀, ρ g⁻¹ * ρ g = 1 := fun g => by rw [← hmul, inv_mul_cancel, h1]
  have hcc' : ∀ x : F.Γ, F.c * (F.c * x) = x := fun x => by rw [← mul_assoc, F.c_sq, one_mul]
  have hcc : ∀ g : F.G₀, F.conj (F.conj g) = g := fun g => by
    apply Subtype.ext
    show F.c * (F.c * (g : F.Γ) * F.c⁻¹) * F.c⁻¹ = g
    simp only [hcinv, mul_assoc, F.c_sq, mul_one, hcc']
  have hχconj : ∀ g : F.G₀, χ (F.conj g : F.Γ) = χ g := fun g => by
    show χ (F.c * (g : F.Γ) * F.c⁻¹) = χ g
    rw [hcinv, hχmul, hχmul]
    linear_combination (χ (g : F.Γ)) * hχc
  let adV : F.G₀ → (V →ₗ[A] V) := fun g =>
    { toFun := fun Z => ⟨χ g • (ρ g * Z * ρ g⁻¹), had g Z Z.2⟩
      map_add' := fun Z W => by
        apply Subtype.ext
        simp [Matrix.mul_add, Matrix.add_mul]
      map_smul' := fun a Z => by
        apply Subtype.ext
        show χ g • (ρ g * (a • (Z : Matrix (Fin n) (Fin n) R)) * ρ g⁻¹) = a • (χ g • (ρ g * (Z : Matrix (Fin n) (Fin n) R) * ρ g⁻¹))
        rw [Matrix.mul_smul, Matrix.smul_mul, smul_comm] }
  let τV : V →ₗ[A] V :=
    { toFun := fun Z => ⟨-(χ F.c • (Z : Matrix (Fin n) (Fin n) R)ᵀ), V.neg_mem (htr Z Z.2)⟩
      map_add' := fun Z W => by
        apply Subtype.ext
        simp [add_comm]
      map_smul' := fun a Z => by
        apply Subtype.ext
        show -(χ F.c • (a • (Z : Matrix (Fin n) (Fin n) R))ᵀ) = a • -(χ F.c • (Z : Matrix (Fin n) (Fin n) R)ᵀ)
        rw [Matrix.transpose_smul, smul_comm, smul_neg] }
  have hadEq : ∀ g g' : F.G₀, (g : F.Γ) = g' → ∀ Z, adV g Z = adV g' Z := by
    intro g g' h Z
    rw [Subtype.ext h]
  have hadone : ∀ Z, adV 1 Z = Z := by
    intro Z
    apply Subtype.ext
    simp [adV, h1, hχ1]
  have hadmul : ∀ g h Z, adV (g * h) Z = adV g (adV h Z) := by
    intro g h Z
    apply Subtype.ext
    simp [adV, hmul, _root_.mul_inv_rev, hχmul, Matrix.mul_assoc, smul_smul, Matrix.mul_smul, Matrix.smul_mul]
  have hττ : ∀ Z, τV (τV Z) = Z := by
    intro Z
    apply Subtype.ext
    simp [τV, smul_smul, hχc]
  have hτad : ∀ g Z, τV (adV g Z) = adV (F.conj g) (τV Z) := by
    intro g Z
    apply Subtype.ext
    obtain ⟨a, ha⟩ := hform g
    obtain ⟨b, hb⟩ := hform g⁻¹
    rw [map_inv] at hb
    have hm := conj_eq_transpose_conj_of_transpose_mul_eq_smul_one (ρ g) (ρ g⁻¹) (ρ (F.conj g)) (ρ (F.conj g)⁻¹) (Z : Matrix (Fin n) (Fin n) R)ᵀ a b
      (hρr g) (hρl g) (hρr _) ha hb
    simp only [adV, τV, LinearMap.coe_mk, AddHom.coe_mk, hχconj]
    simp only [Matrix.transpose_smul, Matrix.transpose_mul, Matrix.mul_assoc, Matrix.mul_neg, Matrix.neg_mul,
      Matrix.mul_smul, Matrix.smul_mul, smul_neg, smul_smul, hm, mul_comm]
  have hswap : ∀ g W, adV g (τV W) = τV (adV (F.conj g) W) := by
    intro g W
    rw [hτad, hcc]
  have hηc : ∀ h : F.Γ, F.η h ≠ 1 → F.η h = -1 := fun h hh => (Int.units_eq_one_or _).resolve_left hh
  have hmemc : ∀ h : F.Γ, F.η h ≠ 1 → F.c * h ∈ F.η.ker := fun h hh => by
    rw [MonoidHom.mem_ker, map_mul, F.η_c, hηc h hh]
    rfl
  let f : F.Γ → (V →ₗ[A] V) := fun h =>
    if hh : F.η h = 1 then adV ⟨h, hh⟩ else τV ∘ₗ adV ⟨F.c * h, hmemc h hh⟩
  have hcne : F.η F.c ≠ 1 := by
    rw [F.η_c]
    decide
  refine ⟨{ toFun := f, map_one' := ?_, map_mul' := ?_ }, ?_, ?_⟩
  · apply LinearMap.ext
    intro Z
    simp only [f, dif_pos (map_one F.η)]
    exact hadone Z
  · intro x y
    apply LinearMap.ext
    intro Z
    rw [Module.End.mul_apply]
    by_cases hx : F.η x = 1 <;> by_cases hy : F.η y = 1
    · have hxy : F.η (x * y) = 1 := by rw [map_mul, hx, hy, one_mul]
      simp only [f, dif_pos hxy, dif_pos hx, dif_pos hy]
      rw [← hadmul]
      rfl
    · have hxy : F.η (x * y) ≠ 1 := by rw [map_mul, hx, one_mul]; exact hy
      simp only [f, dif_neg hxy, dif_pos hx, dif_neg hy, LinearMap.comp_apply]
      rw [hswap, ← hadmul]
      congr 1
      apply hadEq
      simp only [Subgroup.coe_mul, MulMemClass.coe_mul]
      show F.c * (x * y) = F.c * x * F.c⁻¹ * (F.c * y)
      simp only [hcinv, mul_assoc, hcc']
    · have hxy : F.η (x * y) ≠ 1 := by rw [map_mul, hy, mul_one]; exact hx
      simp only [f, dif_neg hxy, dif_neg hx, dif_pos hy, LinearMap.comp_apply]
      rw [← hadmul]
      congr 1
      apply hadEq
      simp only [Subgroup.coe_mul, MulMemClass.coe_mul]
      show F.c * (x * y) = F.c * x * y
      rw [mul_assoc]
    · have hxy : F.η (x * y) = 1 := by
        rw [map_mul, hηc x hx, hηc y hy]
        rfl
      simp only [f, dif_pos hxy, dif_neg hx, dif_neg hy, LinearMap.comp_apply]
      rw [hswap, hττ, ← hadmul]
      apply hadEq
      simp only [Subgroup.coe_mul, MulMemClass.coe_mul]
      show x * y = F.c * (F.c * x) * F.c⁻¹ * (F.c * y)
      simp only [hcinv, mul_assoc, hcc']
  · intro g Z
    show ((f (g : F.Γ)) Z : Matrix (Fin n) (Fin n) R) = _
    simp only [f, dif_pos (show F.η (g : F.Γ) = 1 from g.2)]
    rfl
  · intro Z
    show ((f F.c) Z : Matrix (Fin n) (Fin n) R) = _
    simp only [f, dif_neg hcne, LinearMap.comp_apply]
    rw [hadEq _ 1 (by show F.c * F.c = 1; exact F.c_sq) Z, hadone]
    rfl
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.DegreeCountCohomology.AdicLC
section
open Matrix Filter NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.Pa

theorem UpperTheory.V.Pa.adicLC :
    ∀ (Γ R : Type) [TopologicalSpace Γ] [CommRing R] (t : R) (m : ℕ) (f : Γ → R), t ^ m = 0 → (AdicCont (Ideal.span {t}) f ↔ IsLocallyConstant f) := by
  intro Γ R _ _ t m f ht
  constructor
  · intro h
    refine IsLocallyConstant.desc f (Ideal.Quotient.mk (Ideal.span {t} ^ m)) (h m) ?_
    intro a b hab
    rw [Ideal.Quotient.eq, Ideal.span_singleton_pow, ht, Ideal.mem_span_singleton, zero_dvd_iff,
      sub_eq_zero] at hab
    exact hab
  · intro h N
    exact h.comp _
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.DegreeCountCohomology.CCount
section
open Matrix Filter NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.Pa

private theorem card_ker_mul_card_range_eq_card {G H : Type} [AddGroup G] [AddGroup H] (f : G →+ H) :
    Nat.card f.ker * Nat.card f.range = Nat.card G := by
  rw [← AddSubgroup.index_ker, AddSubgroup.card_mul_index]

theorem UpperTheory.V.Pa.cCount :
    ∀ (R Γ M : Type) [CommRing R] [Group Γ] [AddCommGroup M] [Module R M] [Finite M] (ρ : Representation R Γ M) (c : Γ), c * c = 1 → IsUnit (2 : R) → (∀ Z : AddSubgroup (Γ → M), Finite Z → (Bl ρ).toAddSubgroup ≤ Z → (∀ z ∈ Z, ∀ g h, z (g * h) = z g + ρ g (z h)) → Nat.card Z * Nat.card {m : M // ρ c m = m} = {z | z ∈ Z ∧ z c = 0}.ncard * Nat.card M) ∧ Nat.card (Bl ρ) * Nat.card ρ.invariants = Nat.card M ∧ {z | z ∈ Bl ρ ∧ z c = 0}.ncard * Nat.card ρ.invariants = Nat.card {m : M // ρ c m = m} := by
  intro R Γ M _ _ _ _ _ ρ c hc h2
  let f : M →+ (Γ → M) :=
    { toFun := fun m g => ρ g m - m
      map_zero' := by ext g; simp
      map_add' := by intro a b; ext g; simp; abel }
  have hf : ∀ m g, f m g = ρ g m - m := fun _ _ => rfl
  have hBl : ∀ z, z ∈ Bl ρ ↔ z ∈ f.range := by
    intro z
    simp only [Bl, LinearMap.mem_range, AddMonoidHom.mem_range]
    constructor
    · rintro ⟨m, rfl⟩
      exact ⟨m, by ext g; simp [hf]⟩
    · rintro ⟨m, rfl⟩
      exact ⟨m, by ext g; simp [hf]⟩
  have hker : ∀ m, m ∈ f.ker ↔ m ∈ ρ.invariants := by
    intro m
    rw [AddMonoidHom.mem_ker, Representation.mem_invariants]
    constructor
    · intro h g
      have := congrFun h g
      rw [hf] at this
      simpa [sub_eq_zero] using this
    · intro h
      ext g
      simp [hf, h g]
  have cardBl : Nat.card (Bl ρ) = Nat.card f.range :=
    Nat.card_congr (Equiv.subtypeEquivRight hBl)
  have cardInv : Nat.card ρ.invariants = Nat.card f.ker :=
    Nat.card_congr (Equiv.subtypeEquivRight (fun m => (hker m).symm))
  let d : M →+ M :=
    { toFun := fun m => ρ c m - m
      map_zero' := by simp
      map_add' := by intro a b; simp; abel }
  have hd : ∀ m, d m = ρ c m - m := fun _ => rfl
  have cardFix : Nat.card {m : M // ρ c m = m} = Nat.card d.ker :=
    Nat.card_congr (Equiv.subtypeEquivRight (fun m => by
      rw [AddMonoidHom.mem_ker, hd, sub_eq_zero]))
  have hdM : Nat.card d.range * Nat.card {m : M // ρ c m = m} = Nat.card M := by
    rw [cardFix, mul_comm]
    exact card_ker_mul_card_range_eq_card d
  let Mc : AddSubgroup M :=
    { carrier := {m | ρ c m = m}
      add_mem' := by
        intro a b ha hb
        simp only [Set.mem_setOf_eq] at *
        rw [map_add (f := _), ha, hb]
      zero_mem' := by simp
      neg_mem' := by
        intro a ha
        simp only [Set.mem_setOf_eq] at *
        rw [map_neg, ha] }
  have cardMc : Nat.card {m : M // ρ c m = m} = Nat.card Mc :=
    Nat.card_congr (Equiv.subtypeEquivRight (fun m => Iff.rfl))
  let f' : Mc →+ (Γ → M) := f.comp Mc.subtype
  have hf' : ∀ x, f' x = f x.1 := fun _ => rfl
  have cardKer' : Nat.card f'.ker = Nat.card ρ.invariants := by
    rw [cardInv]
    exact Nat.card_congr
      { toFun := fun x => ⟨x.1.1, by
          have := AddMonoidHom.mem_ker.1 x.2
          rw [hf'] at this
          exact AddMonoidHom.mem_ker.2 this⟩
        invFun := fun v => ⟨⟨v.1, ((hker _).1 v.2 |> (Representation.mem_invariants ρ _).1) c⟩, by
          apply AddMonoidHom.mem_ker.2
          rw [hf']
          exact AddMonoidHom.mem_ker.1 v.2⟩
        left_inv := fun _ => rfl
        right_inv := fun _ => rfl }
  have hRange' : ∀ z, z ∈ f'.range ↔ z ∈ {z | z ∈ Bl ρ ∧ z c = 0} := by
    intro z
    simp only [Set.mem_setOf_eq, AddMonoidHom.mem_range]
    constructor
    · rintro ⟨x, rfl⟩
      refine ⟨(hBl _).2 ⟨x.1, (hf' x).symm⟩, ?_⟩
      rw [hf', hf, sub_eq_zero]
      exact x.2
    · rintro ⟨hz, hzc⟩
      obtain ⟨m, rfl⟩ := (hBl z).1 hz
      rw [hf, sub_eq_zero] at hzc
      exact ⟨⟨m, hzc⟩, rfl⟩
  have cardR' : Nat.card f'.range = {z | z ∈ Bl ρ ∧ z c = 0}.ncard := by
    rw [← Nat.card_coe_set_eq]
    exact Nat.card_congr (Equiv.subtypeEquivRight hRange')
  refine ⟨?_, ?_, ?_⟩
  · intro Z _ hle hcoc
    let ev : Z →+ M :=
      { toFun := fun z => z.1 c
        map_zero' := rfl
        map_add' := fun _ _ => rfl }
    have hev : ∀ z, ev z = z.1 c := fun _ => rfl
    have kerEv : Nat.card ev.ker = {z | z ∈ Z ∧ z c = 0}.ncard := by
      rw [← Nat.card_coe_set_eq]
      exact Nat.card_congr
        { toFun := fun x => ⟨x.1.1, x.1.2, by
            have := AddMonoidHom.mem_ker.1 x.2
            rwa [hev] at this⟩
          invFun := fun y => ⟨⟨y.1, y.2.1⟩, AddMonoidHom.mem_ker.2 (by rw [hev]; exact y.2.2)⟩
          left_inv := fun _ => rfl
          right_inv := fun _ => rfl }
    have rangeEv : ∀ x, x ∈ ev.range ↔ x ∈ d.range := by
      intro x
      simp only [AddMonoidHom.mem_range]
      constructor
      · rintro ⟨⟨z, hz⟩, rfl⟩
        rw [hev]
        have h1 := hcoc z hz 1 1
        simp only [mul_one, map_one, Module.End.one_apply] at h1
        have hz1 : z 1 = 0 := by
          have : z 1 + z 1 = z 1 + 0 := by rw [add_zero]; exact h1.symm
          exact add_left_cancel this
        have h2c := hcoc z hz c c
        rw [hc, hz1] at h2c
        obtain ⟨u, hu⟩ := h2
        refine ⟨-((↑u⁻¹ : R) • z c), ?_⟩
        rw [hd, map_neg, map_smul]
        have hneg : ρ c (z c) = -z c := by
          rw [eq_neg_iff_add_eq_zero, add_comm]
          exact h2c.symm
        rw [hneg, smul_neg, neg_neg, sub_neg_eq_add, ← add_smul]
        have : (↑u⁻¹ : R) + ↑u⁻¹ = 1 := by
          rw [← Units.inv_mul u, hu]
          ring
        rw [this, one_smul]
      · rintro ⟨m, rfl⟩
        have hmem : f m ∈ Z := hle ((Submodule.mem_toAddSubgroup _).2 ((hBl _).2 ⟨m, rfl⟩))
        refine ⟨⟨f m, hmem⟩, ?_⟩
        show f m c = d m
        rw [hf, hd]
    have cardRangeEv : Nat.card ev.range = Nat.card d.range :=
      Nat.card_congr (Equiv.subtypeEquivRight rangeEv)
    rw [← kerEv, ← card_ker_mul_card_range_eq_card ev, cardRangeEv, mul_assoc, hdM]
  · rw [cardBl, cardInv, mul_comm]
    exact card_ker_mul_card_range_eq_card f
  · rw [← cardR', ← cardKer', cardMc, mul_comm]
    exact card_ker_mul_card_range_eq_card f'
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.DegreeCountCohomology.CcAt
section
open Matrix Filter NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.Pa

private theorem cc_at (F Ω : Type) [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω]
    (w : InfinitePlace F) (hw : w.IsReal) : ∃ c : G F Ω, IsCCAt w c := by
  classical
  let φ : F →+* ℂ := w.embedding
  have hφ : ∀ x, starRingEnd ℂ (φ x) = φ x := by
    intro x
    have h := ComplexEmbedding.isReal_iff.mp (InfinitePlace.isReal_iff.mp hw)
    exact RingHom.congr_fun h x
  letI : Algebra F ℂ := φ.toAlgebra
  let j : Ω →ₐ[F] ℂ := (by
    refine @_root_.IsAlgClosed.lift _ _ _ _ _ _ _ _ _ _ _ ?_ ?_ ?_
    solve_by_elim* (maxDepth := 2) only [*,
      @_root_.DivisionSemiring.to_moduleIsTorsionFree,
      @_root_.Algebra.IsIntegral.isAlgebraic, @_root_.inferInstance])
  letI : Algebra Ω ℂ := j.toRingHom.toAlgebra
  haveI : IsScalarTower F Ω ℂ := IsScalarTower.of_algebraMap_eq (fun x => (j.commutes x).symm)
  let κ : ℂ ≃ₐ[F] ℂ := AlgEquiv.ofRingEquiv (f := starRingAut) (fun x => hφ x)
  refine ⟨κ.restrictNormal Ω, j.toRingHom, fun x => ?_, ?_⟩
  · exact AlgEquiv.restrictNormal_commutes κ Ω x
  · have e : j.toRingHom.comp (algebraMap F Ω) = φ := by
      ext x
      exact j.commutes x
    rw [e]
    exact InfinitePlace.mk_embedding w

theorem UpperTheory.V.Pa.ccEx :
    ∀ (l : ℕ) [Fact l.Prime] (L Ω : Type) [Field L] [NumberField L] [IsCMField L] [Field Ω] [Algebra L Ω] [IsAlgClosure L Ω], (∀ w : InfinitePlace (Lp L), ∃ c : G (Lp L) Ω, IsCCAt w c) ∧ ∀ c : G (Lp L) Ω, (∃ j : Ω →+* ℂ, ∀ x, j (c x) = starRingEnd ℂ (j x)) → c * c = 1 ∧ c ∉ (resP L Ω).range ∧ cycZ (Lp L) Ω l c = -1 := by
  intro l _ L Ω _ _ _ _ _ _
  haveI : Algebra.IsAlgebraic (Lp L) L := Algebra.IsAlgebraic.of_finite (Lp L) L
  haveI : IsAlgClosure (Lp L) Ω := IsAlgClosure.ofAlgebraic (Lp L) L Ω
  refine ⟨fun w => cc_at (Lp L) Ω w (IsTotallyReal.isReal w), ?_⟩
  rintro c ⟨j, hj⟩
  refine ⟨?_, ?_, ?_⟩
  · apply AlgEquiv.ext
    intro x
    apply j.injective
    show j (c (c x)) = j x
    rw [hj, hj, Complex.conj_conj]
  · rintro ⟨σ, hσ⟩
    have hfix : ∀ y : L, c (algebraMap L Ω y) = algebraMap L Ω y := by
      intro y
      rw [← hσ]
      exact σ.commutes y
    let ψ : L →+* ℂ := j.comp (algebraMap L Ω)
    have hreal : ComplexEmbedding.IsReal ψ := by
      rw [ComplexEmbedding.isReal_iff]
      ext y
      show starRingEnd ℂ (j (algebraMap L Ω y)) = j (algebraMap L Ω y)
      rw [← hj, hfix]
    have hR : (InfinitePlace.mk ψ).IsReal := InfinitePlace.isReal_mk_iff.mpr hreal
    exact (InfinitePlace.not_isReal_iff_isComplex.mpr (IsTotallyComplex.isComplex _)) hR
  · exact UpperTheory.V.IsConjOm.cyc (E := L) (σ := MulSemiringAction.toRingAut (G (Lp L) Ω) Ω c) ⟨j, hj⟩
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.DegreeCountCohomology.DdSumZero
section
open Matrix Filter NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.Pa

private theorem dd_sum_zero {X : Type} [CommRing X] {g : ℕ} (u v : DD X g) (ua : u.a = 0) (va : v.a = 0)
    (ue : u.ep' = 0) (ve : v.ep' = 0) : u * v = 0 := by
  apply DD.ext
  · simp [DD.mul_a, ua]
  · funext j
    simp [DD.mul_ep, ua, va]
  · funext j
    simp [DD.mul_ep', ue, ve]
  · simp [DD.mul_eta, ua, va, ue, ve]

private theorem epM_sq {X : Type} [CommRing X] {g n : ℕ} (Z Z' : Fin g → Matrix (Fin n) (Fin n) X) :
    DD.epM Z * DD.epM Z' = 0 := by
  refine Matrix.ext fun a b => ?_
  rw [Matrix.mul_apply, Matrix.zero_apply]
  exact Finset.sum_eq_zero fun c _ => dd_sum_zero _ _ rfl rfl rfl rfl

private theorem epM_tr {X : Type} [CommRing X] {g n : ℕ} (Z : Fin g → Matrix (Fin n) (Fin n) X) :
    (DD.epM Z)ᵀ = DD.epM fun j => (Z j)ᵀ := rfl

private theorem epM_neg {X : Type} [CommRing X] {g n : ℕ} (Z : Fin g → Matrix (Fin n) (Fin n) X) :
    (DD.epM fun j => -Z j) = -DD.epM Z := by
  ext a b <;> simp [DD.epM]

theorem UpperTheory.V.Pa.rho1 :
    ∀ (l : ℕ) [Fact l.Prime] (F : GFrame l) (n : ℕ) (x : NP F n) (k : Kap x) (X : Type) [CommRing X] [Algebra x.A X], k.ρ1 X 1 = 1 ∧ (∀ g h, k.ρ1 X (g * h) = k.ρ1 X g * k.ρ1 X h) ∧ (∀ g, (k.ρ1 X g)ᵀ * k.ρ1 X (F.conj g) = algebraMap x.A (DD X k.g) ((F.eps ℤ_[l] x.A g ^ (1 - (n : ℤ)) : x.Aˣ) : x.A) • (1 : Matrix (Fin n) (Fin n) (DD X k.g))) ∧ (∀ v, k.wi1 X v * k.w1 X v = 1 ∧ k.w1 X v * k.wi1 X v = 1) ∧ ∀ u, ∀ g ∈ F.Iu u, k.ρ1 X g = 1 := by
  intro l _ F n x k X _ _
  obtain ⟨h1, hmul, -, hw⟩ := Det.rho1Hom k X
  refine ⟨h1, hmul, fun g => ?_, fun v => ⟨(hw v).2, (hw v).1⟩, fun u g hg => ?_⟩
  · have hc : (fun j => (k.κ j (F.conj g)).map (algebraMap x.A X)) =
        fun j => -(((k.κ j g).map (algebraMap x.A X))ᵀ) := by
      funext j
      rw [(k.mem j).2.2.2.1 g]
      ext a b
      simp
    have hA : ((DD.epM fun j => (k.κ j g).map (algebraMap x.A X)) : Matrix (Fin n) (Fin n) (DD X k.g))ᵀ *
        DD.epM (fun j => -(((k.κ j g).map (algebraMap x.A X))ᵀ)) = 0 := by
      rw [epM_neg, Matrix.mul_neg, epM_tr, epM_sq, neg_zero]
    have hρ : (x.ρX (DD X k.g) g)ᵀ * x.ρX (DD X k.g) (F.conj g) =
        algebraMap x.A (DD X k.g) ((F.eps ℤ_[l] x.A g ^ (1 - (n : ℤ)) : x.Aˣ) : x.A) •
          (1 : Matrix (Fin n) (Fin n) (DD X k.g)) := by
      have hf := x.form g
      simp only [Units.val_one, Matrix.mul_one] at hf
      unfold NP.ρX
      rw [← Matrix.transpose_map, ← Matrix.map_mul, hf]
      refine Matrix.ext fun i j => ?_
      by_cases h : i = j
      · subst h
        simp [Matrix.one_apply]
      · simp [Matrix.one_apply, h]
    unfold Kap.ρ1
    rw [hc, Matrix.transpose_mul, Matrix.transpose_add, Matrix.transpose_one]
    have h2 : (1 + (DD.epM fun j => (k.κ j g).map (algebraMap x.A X))ᵀ) *
        (1 + DD.epM (fun j => -(((k.κ j g).map (algebraMap x.A X))ᵀ))) = 1 := by
      rw [add_mul, one_mul, mul_add, mul_one, hA, add_zero, epM_neg, epM_tr]
      abel
    rw [Matrix.mul_assoc, ← Matrix.mul_assoc (1 + _), h2, Matrix.one_mul, hρ]
  · have hz : ∀ j, k.κ j g = 0 := fun j => (k.mem j).2.2.2.2.1 u g hg
    have hm : (mat x.ρ) g = 1 := by simp [mat, x.ine u g hg]
    have he : (DD.epM fun j => (k.κ j g).map (algebraMap x.A X)) = 0 := by
      refine Matrix.ext fun a b => ?_
      ext <;> simp [hz, DD.epM]
    unfold Kap.ρ1 NP.ρX
    rw [hm, Matrix.map_one _ (map_zero _) (map_one _), Matrix.mul_one, he, add_zero]
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.DegreeCountCohomology.DecSplit
section
open Matrix Filter NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.Pa

theorem UpperTheory.V.Pa.decSplit :
    ∀ (L Ω : Type) [Field L] [NumberField L] [IsCMField L] [Field Ω] [Algebra L Ω] [IsAlgClosure L Ω] (A : ValuationSubring Ω), Dec (F := Lp L) A ≤ (resP L Ω).range → ∃ α : Dec (F := L) A ≃ₜ* Dec (F := Lp L) A, ∀ g, (α g : G (Lp L) Ω) = resP L Ω (g : G L Ω) := by
  intro L Ω _ _ _ _ _ _ A hA
  have hinj : Function.Injective (resP L Ω) := by
    intro a b h
    ext x
    exact congrArg (fun f : G (Lp L) Ω => f x) h
  have hmap : ∀ g : Dec (F := L) A, resP L Ω (g : G L Ω) ∈ Dec (F := Lp L) A := by
    intro g
    have hg := mem_Dec.mp g.2
    exact mem_Dec.mpr hg
  let f : Dec (F := L) A →* Dec (F := Lp L) A :=
    { toFun := fun g => ⟨resP L Ω g, hmap g⟩
      map_one' := by ext1; exact map_one (resP L Ω)
      map_mul' := fun a b => by ext1; exact map_mul (resP L Ω) a.1 b.1 }
  have hbij : Function.Bijective f := by
    refine ⟨fun a b h => Subtype.ext (hinj (congrArg Subtype.val h)), fun t => ?_⟩
    obtain ⟨s, hs⟩ := hA t.2
    have hsA : s ∈ Dec (F := L) A := by
      apply mem_Dec.mpr
      have := mem_Dec.mp (hs ▸ t.2)
      exact this
    exact ⟨⟨s, hsA⟩, Subtype.ext hs⟩
  let e : Dec (F := L) A ≃* Dec (F := Lp L) A := MulEquiv.ofBijective f hbij
  have hcont : Continuous e := by
    apply Continuous.subtype_mk
    exact continuous_resP.comp continuous_subtype_val
  haveI : CompactSpace (Dec (F := L) A) :=
    isCompact_iff_compactSpace.mp (isClosed_Dec (F := L) A).isCompact
  let h := hcont.homeoOfEquivCompactToT2 (f := e.toEquiv)
  refine ⟨{ e with continuous_toFun := h.continuous, continuous_invFun := h.symm.continuous }, fun g => rfl⟩
end

