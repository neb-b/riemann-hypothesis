module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.NearSplit
public import Development.AutomorphicArithmetic.AutomorphicVarieties.SymplecticGSp4.Bundle0004
public import Development.AutomorphicArithmetic.AutomorphicVarieties.CharacterLevelBounds.Bundle0003
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0079

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.GradedFlagMoves.FlagMove
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual Formalism.HC ReciprocityTheory.Gal IsLocalRing Polynomial UpperTheory.V.Base UpperTheory.V.Alg UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws

private theorem up_mul {k : Type} [Field k] {A B : M4 k} (hA : IsUp A) (hB : IsUp B) :
    IsUp (A * B) ∧ ∀ i, (A * B) i i = A i i * B i i := by
  refine ⟨fun i j hij => ?_, fun i => ?_⟩
  · rw [Matrix.mul_apply]
    refine Finset.sum_eq_zero fun m _ => ?_
    rcases lt_or_ge m i with h | h
    · rw [hA i m h, zero_mul]
    · rw [hB m j (lt_of_lt_of_le hij h), mul_zero]
  · rw [Matrix.mul_apply]
    refine Finset.sum_eq_single i (fun m _ hm => ?_) (fun h => absurd (Finset.mem_univ i) h)
    rcases lt_or_gt_of_ne hm with h | h
    · rw [hA i m h, zero_mul]
    · rw [hB m i h, mul_zero]

private theorem up_inv {k : Type} [Field k] {A B : M4 k} (hA : IsUp A) (h : A * B = 1) : IsUp B := by
  have hA' : Matrix.BlockTriangular A id := fun i j hij => hA i j hij
  haveI : Invertible A := invertibleOfRightInverse A B h
  have h1 := Matrix.blockTriangular_inv_of_blockTriangular hA'
  rw [Matrix.inv_eq_right_inv h] at h1
  exact fun i j hij => h1 hij

theorem UpperTheory.V.Ws.Rt.flagMove :
    ∀ (k : Type) [Field k] (X X' Z n n' : M4 k), X * X' = 1 → IsLow n → IsLow n' → IsUp (adj n' * X * n) → IsUp (adj n * Z * n) →
      IsUp (adj n' * (X * Z * X') * n') ∧ ∀ i, (adj n' * (X * Z * X') * n') i i = (adj n * Z * n) i i := by
  intro k _ X X' Z n n' hX hn hn' hB hY
  have h1 : adj n * n = 1 := by simpa [IsGSp] using hn.1
  have h2 : adj n' * n' = 1 := by simpa [IsGSp] using hn'.1
  have h3 : n * adj n = 1 := mul_eq_one_comm.mp h1
  have h4 : ∀ W : M4 k, n * (adj n * W) = W := fun W => by rw [← mul_assoc, h3, one_mul]
  have h5 : ∀ W : M4 k, X * (X' * W) = W := fun W => by rw [← mul_assoc, hX, one_mul]
  have hBB : (adj n' * X * n) * (adj n * X' * n') = 1 := by
    simp only [mul_assoc, h4, h5, h2]
  have hB' := up_inv hB hBB
  have e : adj n' * (X * Z * X') * n' = (adj n' * X * n) * (adj n * Z * n) * (adj n * X' * n') := by
    simp only [mul_assoc, h4]
  rw [e]
  have p1 := up_mul hB hY
  have p2 := up_mul p1.1 hB'
  refine ⟨p2.1, fun i => ?_⟩
  have q := (up_mul hB hB').2 i
  rw [hBB, Matrix.one_apply_eq] at q
  rw [p2.2, p1.2]
  linear_combination (-(adj n * Z * n) i i) * q
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.GradedFlagMoves.FlagNew
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual Formalism.HC ReciprocityTheory.Gal IsLocalRing Polynomial UpperTheory.V.Base UpperTheory.V.Alg UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws

private theorem lowMk {R : Type} [CommRing R] (x y z t : R) :
    IsLow (!![1, 0, 0, 0; -x, 1, 0, 0; -y, -t, 1, 0; -z, -(y + t * x), x, 1] : M4 R) := by
  refine ⟨?_, ?_, ?_⟩
  · ext i j
    fin_cases i <;> fin_cases j <;>
      simp [adj_apply, sgn, Fin.rev, Matrix.mul_apply, Fin.sum_univ_four] <;> ring
  · intro i
    fin_cases i <;> simp
  · intro i j h
    fin_cases i <;> fin_cases j <;> simp at h ⊢

private theorem adjMk {R : Type} [CommRing R] (x y z t : R) :
    adj (!![1, 0, 0, 0; -x, 1, 0, 0; -y, -t, 1, 0; -z, -(y + t * x), x, 1] : M4 R) =
      !![1, 0, 0, 0; x, 1, 0, 0; y + t * x, t, 1, 0; z, y, -x, 1] := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [adj_apply, sgn, Fin.rev] <;> ring

private theorem upOf {k : Type} [Field k] {ν : k} {w : M4 k} (h : IsGSp ν w) (h0 : w 0 0 ≠ 0)
    (h1 : w 1 0 = 0) (h2 : w 2 0 = 0) (h3 : w 3 0 = 0) (h4 : w 2 1 = 0) : IsUp w := by
  have e1 := congrFun (congrFun h 3) 1
  have e2 := congrFun (congrFun h 3) 2
  simp [adj_apply, Matrix.mul_apply, Fin.sum_univ_four, sgn, Fin.rev, h1, h2, h3] at e1 e2
  have h31 : w 3 1 = 0 := by
    rcases e1 with e1 | e1
    · exact absurd e1 h0
    · exact e1
  have h32 : w 3 2 = 0 := by
    rcases e2 with e2 | e2
    · exact absurd e2 h0
    · exact e2
  intro i j hij
  fin_cases i <;> fin_cases j <;> simp_all <;> omega

private theorem core {k : Type} [Field k] {ν : k} {u : M4 k} (hu : IsGSp ν u) (h0 : u 0 0 ≠ 0) (h1 : u 1 1 ≠ 0)
    (h01 : u 0 1 = 0) : ∃ n' : M4 k, IsLow n' ∧ IsUp (adj n' * u) ∧ (u 2 1 = 0 → n' 2 1 = 0) := by
  obtain ⟨x, hx⟩ : ∃ x : k, x * u 0 0 + u 1 0 = 0 :=
    ⟨-u 1 0 / u 0 0, by field_simp; ring⟩
  obtain ⟨t, ht⟩ : ∃ t : k, t * u 1 1 + u 2 1 = 0 :=
    ⟨-u 2 1 / u 1 1, by field_simp; ring⟩
  obtain ⟨y, hy⟩ : ∃ y : k, (y + t * x) * u 0 0 + t * u 1 0 + u 2 0 = 0 :=
    ⟨-(t * u 1 0 + u 2 0) / u 0 0 - t * x, by field_simp; ring⟩
  obtain ⟨z, hz⟩ : ∃ z : k, z * u 0 0 + y * u 1 0 - x * u 2 0 + u 3 0 = 0 :=
    ⟨(x * u 2 0 - y * u 1 0 - u 3 0) / u 0 0, by field_simp; ring⟩
  have hl := lowMk x y z t
  refine ⟨_, hl, ?_, ?_⟩
  · have hinv : adj (!![1, 0, 0, 0; -x, 1, 0, 0; -y, -t, 1, 0; -z, -(y + t * x), x, 1] : M4 k) *
        !![1, 0, 0, 0; -x, 1, 0, 0; -y, -t, 1, 0; -z, -(y + t * x), x, 1] = 1 := by
      simpa [IsGSp] using hl.1
    have hinv' := mul_eq_one_comm.mp hinv
    have hG : IsGSp 1 (adj (!![1, 0, 0, 0; -x, 1, 0, 0; -y, -t, 1, 0; -z, -(y + t * x), x, 1] : M4 k)) := by
      unfold IsGSp
      rw [(grp k).2.1]
      simpa using hinv'
    have hP := (grp k).2.2.2.2.2.2.2.1 1 ν _ _ hG hu
    rw [one_mul] at hP
    rw [adjMk] at hP ⊢
    apply upOf hP
    · simpa [Matrix.mul_apply, Fin.sum_univ_four] using h0
    · simp [Matrix.mul_apply, Fin.sum_univ_four]
      linear_combination hx
    · simp [Matrix.mul_apply, Fin.sum_univ_four]
      linear_combination hy
    · simp [Matrix.mul_apply, Fin.sum_univ_four]
      linear_combination hz
    · simp [Matrix.mul_apply, Fin.sum_univ_four, h01]
      linear_combination ht
  · intro h21
    have : t = 0 := by
      rw [h21, add_zero] at ht
      rcases mul_eq_zero.mp ht with h | h
      · exact h
      · exact absurd h h1
    simp [this]

theorem UpperTheory.V.Ws.Rt.flagNew :
    ∀ (k : Type) [Field k] (ν : k) (X n : M4 k), ν ≠ 0 → IsGSp ν X → IsLow n → ((SuppM nP X ∧ SuppM qQ n) ∨ SuppM nM X) →
      ∃ n' : M4 k, IsLow n' ∧ IsUp (adj n' * X * n) ∧ (SuppM nP X ∧ SuppM qQ n → SuppM qQ n') := by
  intro k _ ν X n hν hX hn hS
  obtain ⟨hn1, hnd, hnu⟩ := hn
  have hu : IsGSp ν (X * n) := by
    have := (grp k).2.2.2.2.2.2.2.1 ν 1 X n hX hn1
    simpa using this
  have key : X 0 1 = 0 ∧ X 0 2 = 0 ∧ X 0 3 = 0 ∧ X 1 3 = 0 ∧ X 2 3 = 0 ∧
      X 1 2 * X 2 1 = 0 ∧ X 1 2 * n 2 1 = 0 := by
    rcases hS with ⟨hA, hB⟩ | hA
    · refine ⟨hA 0 1 (by decide) (by decide), hA 0 2 (by decide) (by decide),
        hA 0 3 (by decide) (by decide), hA 1 3 (by decide) (by decide),
        hA 2 3 (by decide) (by decide), ?_, ?_⟩
      · rw [hA 2 1 (by decide) (by decide), mul_zero]
      · rw [hB 2 1 (by decide) (by decide), mul_zero]
    · refine ⟨hA 0 1 (by decide) (by decide), hA 0 2 (by decide) (by decide),
        hA 0 3 (by decide) (by decide), hA 1 3 (by decide) (by decide),
        hA 2 3 (by decide) (by decide), ?_, ?_⟩
      · rw [hA 1 2 (by decide) (by decide), zero_mul]
      · rw [hA 1 2 (by decide) (by decide), zero_mul]
  obtain ⟨z01, z02, z03, z13, z23, c1, c2⟩ := key
  have n01 : n 0 1 = 0 := hnu 0 1 (by decide)
  have n11 : n 1 1 = 1 := hnd 1
  have n00 : n 0 0 = 1 := hnd 0
  have d0 := congrFun (congrFun hX 0) 0
  have d1 := congrFun (congrFun hX 1) 1
  simp [adj_apply, Matrix.mul_apply, Fin.sum_univ_four, sgn, Fin.rev, z01, z02, z03, z13, z23] at d0 d1
  have x00 : X 0 0 ≠ 0 := by
    intro h
    rw [h] at d0
    simp at d0
    exact hν d0.symm
  have x11 : X 1 1 ≠ 0 := by
    intro h
    apply hν
    rw [← d1, h]
    linear_combination -c1
  have h00 : (X * n) 0 0 ≠ 0 := by
    simpa [Matrix.mul_apply, Fin.sum_univ_four, z01, z02, z03, n00] using x00
  have h11 : (X * n) 1 1 ≠ 0 := by
    simp [Matrix.mul_apply, Fin.sum_univ_four, z13, n01, n11]
    rw [c2, add_zero]
    exact x11
  have h01 : (X * n) 0 1 = 0 := by
    simp [Matrix.mul_apply, Fin.sum_univ_four, z01, z02, z03, n01]
  obtain ⟨n', hl, hup, h21⟩ := core hu h00 h11 h01
  refine ⟨n', hl, by rwa [← mul_assoc] at hup, ?_⟩
  rintro ⟨hA, hB⟩
  have e21 : (X * n) 2 1 = 0 := by
    simp [Matrix.mul_apply, Fin.sum_univ_four, z23, n01, n11, hA 2 1 (by decide) (by decide),
      hB 2 1 (by decide) (by decide)]
  have m21 := h21 e21
  intro i j hij hw
  fin_cases i <;> fin_cases j <;>
    first
    | exact absurd rfl hij
    | exact hl.2.2 _ _ (by decide)
    | exact m21
    | exact absurd (by decide) hw
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.GradedFlagMoves.MuTriv
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual Formalism.HC ReciprocityTheory.Gal IsLocalRing Polynomial UpperTheory.V.Base UpperTheory.V.Alg UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws

theorem UpperTheory.V.Ws.Rt.muTriv :
    ∀ (l : ℕ) [Fact l.Prime] (Γ : Type) [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ] (H : Subgroup Γ) (k : Type) [Field k] [CharP k l]
      (ψ : Γ →* k), IsLocallyConstant ψ → ∀ s ∈ muOf l H, ψ s = 1 := by
  intro l _ Γ _ _ _ H k _ _ ψ hψ s hs
  obtain ⟨-, a, ha⟩ := hs
  have hcl : IsClosed ((ψ.ker : Subgroup Γ) : Set Γ) := by
    have e : ((ψ.ker : Subgroup Γ) : Set Γ) = {x | ψ x = 1} := by
      ext x
      simp [MonoidHom.mem_ker]
    rw [e]
    exact hψ.isClosed_fiber 1
  have hle : ⁅H, H⁆ ≤ ψ.ker := by
    rw [Subgroup.commutator_le]
    intro g₁ _ g₂ _
    rw [MonoidHom.mem_ker, commutatorElement_def, map_mul, map_mul, map_mul]
    calc ψ g₁ * ψ g₂ * ψ g₁⁻¹ * ψ g₂⁻¹ = ψ (g₁ * g₁⁻¹) * ψ (g₂ * g₂⁻¹) := by
          rw [map_mul, map_mul]; ring
      _ = 1 := by simp
  have hm := Subgroup.topologicalClosure_minimal _ hle hcl ha
  rw [MonoidHom.mem_ker, map_pow] at hm
  have h0 : (ψ s - 1) ^ l ^ a = 0 := by
    rw [sub_pow_char_pow, hm, one_pow, sub_self]
  exact sub_eq_zero.mp (pow_eq_zero_iff (pow_ne_zero _ (Fact.out : l.Prime).ne_zero) |>.mp h0)
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.GradedFlagMoves.SplitMod
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual Formalism.HC ReciprocityTheory.Gal IsLocalRing Polynomial UpperTheory.V.Base UpperTheory.V.Alg UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws

theorem UpperTheory.V.Ws.Rt.splitMod :
    ∀ {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {l : ℕ} [Fact l.Prime] {c : Coef l} (D : Raw Ω c), D.Good → ∀ w : ℕ, w.Prime →
      ∀ A : ValuationSubring Ω, A.valuation (w : Ω) < 1 → ¬ A.valuation (l : Ω) < 1 → Dec (F := ℚ) A ≤ D.om.ker → l ∣ w - 1 := by
  intro Ω _ _ _ l _ c D hD w hw A hwA hlA hdec
  have hlw : l ≠ w := by
    rintro rfl; exact hlA hwA
  obtain ⟨-, -, γ, hγ, -, hcyc⟩ := UpperTheory.V.Chr.decCyc Ω w A hw hwA
  have hγl : ((cycZ ℚ Ω l γ : ℤ_[l]ˣ) : ℤ_[l]) = w := hcyc l hlw
  have hom : D.om γ = 1 := hdec hγ
  have hbar := hD.om_bar γ
  simp only [Raw.bar, hom, chiO, MonoidHom.comp_apply, Units.coe_map, Units.val_one, map_one,
    MonoidHom.coe_coe, hγl] at hbar
  have hbar' : residue c.O (algebraMap ℤ_[l] c.O (w : ℤ_[l])) = 1 := hbar.symm
  have hint : Algebra.IsIntegral ℤ_[l] c.O := by
    haveI := c.fin
    infer_instance
  have key : ((w : ℤ_[l]) - 1) ∈ IsLocalRing.maximalIdeal ℤ_[l] := by
    have h0 : residue c.O (algebraMap ℤ_[l] c.O ((w : ℤ_[l]) - 1)) = 0 := by
      rw [map_sub, map_one, map_sub, map_one, hbar', sub_self]
    have hm := (IsLocalRing.residue_eq_zero_iff _).mp h0
    letI := hint
    have hmax : (IsLocalRing.maximalIdeal c.O).comap (algebraMap ℤ_[l] c.O) = IsLocalRing.maximalIdeal ℤ_[l] :=
      IsLocalRing.eq_maximalIdeal (Ideal.isMaximal_under_of_isIntegral_of_isMaximal (IsLocalRing.maximalIdeal c.O))
    rw [← hmax]
    exact hm
  have hcast : ((w : ℤ_[l]) - 1) = (((w : ℤ) - 1 : ℤ) : ℤ_[l]) := by push_cast; rfl
  rw [hcast, IsLocalRing.mem_maximalIdeal, PadicInt.mem_nonunits, PadicInt.norm_int_lt_one_iff_dvd] at key
  have h1 : ((w - 1 : ℕ) : ℤ) = (w : ℤ) - 1 := by
    rw [Nat.cast_sub hw.one_le, Nat.cast_one]
  rw [← h1] at key
  exact Int.natCast_dvd_natCast.mp key
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.GradedFlagMoves.TameExp
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual Formalism.HC ReciprocityTheory.Gal IsLocalRing Polynomial UpperTheory.V.Base UpperTheory.V.Alg UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws

private theorem UpperTheory.V.Ws.Rt.wild_mem_ker
    {F Ω : Type} [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] {l : ℕ} (hl : l.Prime)
    {A : ValuationSubring Ω} (hvl : ¬ A.valuation (l : Ω) < 1) {N : Type} [Group N]
    (ψ : Ine (F := F) A →* N) (ho : IsOpen (ψ.ker : Set (Ine (F := F) A))) (hψ : ∀ σ, ψ σ ^ l = 1)
    (σ : Ine (F := F) A) (hσ : ∀ y : Ω, y ≠ 0 → A.valuation (σ.1 y / y - 1) < 1) : ψ σ = 1 := by
  obtain ⟨t, ht, hte⟩ := isOpen_induced_iff.1 ho
  have h1t : (1 : G F Ω) ∈ t := by
    have h1 : (1 : Ine (F := F) A) ∈ (Subtype.val ⁻¹' t : Set (Ine (F := F) A)) := by
      rw [hte]
      exact ψ.ker.one_mem
    exact h1
  obtain ⟨L, hfin, hL⟩ := (krullTopology_mem_nhds_one_iff F Ω t).1 (ht.mem_nhds h1t)
  have hfix : ∃ n, 0 < n ∧ ∀ x ∈ L, (σ.1 ^ n) x = x := by
    let f : ℕ → (L →ₐ[F] Ω) := fun i => ((σ.1 ^ i : G F Ω) : Ω →ₐ[F] Ω).comp L.val
    obtain ⟨i, j, hij, he⟩ := Finite.exists_ne_map_eq_of_infinite f
    wlog hlt : i < j generalizing i j
    · exact this j i hij.symm he.symm (lt_of_le_of_ne (not_lt.1 hlt) hij.symm)
    refine ⟨j - i, Nat.sub_pos_of_lt hlt, ?_⟩
    intro x hx
    have hx' := congrArg (fun φ => φ ⟨x, hx⟩) he
    simp only [f, AlgHom.comp_apply, IntermediateField.val_mk, AlgHom.coe_coe] at hx'
    have hx'' : (σ.1 ^ i) x = (σ.1 ^ j) x := hx'
    have hj : σ.1 ^ j = σ.1 ^ i * σ.1 ^ (j - i) := by
      rw [← pow_add, Nat.add_sub_cancel' hlt.le]
    rw [hj, AlgEquiv.mul_apply] at hx''
    exact ((σ.1 ^ i).injective hx'').symm
  obtain ⟨n, hn0, hn⟩ := hfix
  obtain ⟨a, m, hm, hnm⟩ := Nat.exists_eq_pow_mul_and_not_dvd hn0.ne' l hl.ne_one
  have hτw := GlobalTheory.WildInertiaChar.wild_pow A σ.1 hσ m
  have hk : ¬ A.valuation ((l ^ a : ℕ) : Ω) < 1 := by
    rw [Nat.cast_pow, map_pow]
    exact not_lt.2 (one_le_pow₀ (not_lt.1 hvl))
  have hτ : σ.1 ^ m ∈ L.fixingSubgroup := by
    rw [IntermediateField.mem_fixingSubgroup_iff]
    intro x hx
    apply GlobalTheory.WildInertiaChar.fixed_of_pow_fixed A (σ.1 ^ m) hτw (l ^ a) hk x
    rw [← pow_mul, mul_comm, ← hnm]
    exact hn x hx
  have hker : σ ^ m ∈ ψ.ker := by
    have h2 : (σ ^ m) ∈ (Subtype.val ⁻¹' t : Set (Ine (F := F) A)) := hL hτ
    rw [hte] at h2
    exact h2
  rw [MonoidHom.mem_ker, map_pow] at hker
  have hcop : Nat.Coprime l m := (Nat.Prime.coprime_iff_not_dvd hl).2 hm
  have hg := pow_gcd_eq_one.2 ⟨hψ σ, hker⟩
  rwa [hcop.gcd_eq_one, pow_one] at hg

theorem UpperTheory.V.Ws.Rt.tameExp :
    ∀ (F Ω : Type) [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] (l : ℕ) [Fact l.Prime] (A : ValuationSubring Ω), ¬ A.valuation (l : Ω) < 1 →
      ∀ (M : Type) [Monoid M] (φ : Ine (F := F) A →* M), IsLocallyConstant φ → (∀ σ, φ σ ^ l = 1) →
      ∀ θ : Ine (F := F) A →* Multiplicative (ZMod l), IsOpen (θ.ker : Set (Ine (F := F) A)) → θ ≠ 1 → ∀ σ, θ σ = 1 → φ σ = 1 := by
  intro F Ω _ _ _ _ _ l _ A hvl M _ φ hφ hφl θ hθo hθ1 σ hσ
  have hl : l.Prime := Fact.out
  obtain ⟨γ, hγ⟩ := GlobalTheory.TameInertiaGen.exists_tameGenAt_of_valuationSubring (E := F) A
  let φ' := φ.toHomUnits
  have hφ'o : IsOpen (SetLike.coe φ'.ker) := by
    have hf := hφ.isOpen_fiber 1
    convert hf using 1
    ext x
    simp [φ', MonoidHom.mem_ker, Units.ext_iff]
  have hφ'l : ∀ τ, φ' τ ^ l = 1 := by
    intro τ
    apply Units.ext
    simp [φ', hφl]
  have hθl : ∀ τ, θ τ ^ l = 1 := by
    intro τ
    rw [← ofAdd_toAdd (θ τ), ← ofAdd_nsmul]
    simp
  have wφ : ∀ τ : Ine (F := F) A, (∀ y : Ω, y ≠ 0 → A.valuation (τ.1 y / y - 1) < 1) → φ' τ = 1 :=
    fun τ hτ => UpperTheory.V.Ws.Rt.wild_mem_ker hl hvl φ' hφ'o hφ'l τ hτ
  have wθ : ∀ τ : Ine (F := F) A, (∀ y : Ω, y ≠ 0 → A.valuation (τ.1 y / y - 1) < 1) → θ τ = 1 :=
    fun τ hτ => UpperTheory.V.Ws.Rt.wild_mem_ker hl hvl θ hθo hθl τ hτ
  have hθγ : θ ⟨γ, hγ.1⟩ ≠ 1 := by
    intro h
    apply hθ1
    ext τ
    have hm := GlobalTheory.TameCharUnique.mem_of_tameGen hγ θ.ker (θ.ker.isClosed_of_isOpen hθo) h
      (fun τ hτ => wθ τ hτ) τ
    simpa [MonoidHom.mem_ker] using hm
  let Φ := φ'.prod θ
  let S := (Subgroup.zpowers (Φ ⟨γ, hγ.1⟩)).comap Φ
  have hle : φ'.ker ⊓ θ.ker ≤ S := by
    intro τ hτ
    have h1 : Φ τ = 1 := by
      rw [Subgroup.mem_inf, MonoidHom.mem_ker, MonoidHom.mem_ker] at hτ
      simp [Φ, hτ.1, hτ.2]
    show Φ τ ∈ Subgroup.zpowers (Φ ⟨γ, hγ.1⟩)
    rw [h1]
    exact Subgroup.one_mem _
  have hSo : IsOpen (SetLike.coe S) := by
    apply Subgroup.isOpen_mono hle
    rw [Subgroup.coe_inf]
    exact hφ'o.inter hθo
  have hσS := GlobalTheory.TameCharUnique.mem_of_tameGen hγ S (S.isClosed_of_isOpen hSo)
    (Subgroup.mem_zpowers _)
    (fun τ hτ => by
      have h1 : Φ τ = 1 := by simp [Φ, wφ τ hτ, wθ τ hτ]
      show Φ τ ∈ Subgroup.zpowers (Φ ⟨γ, hγ.1⟩)
      rw [h1]
      exact Subgroup.one_mem _) σ
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.1 hσS
  have hk1 : φ' ⟨γ, hγ.1⟩ ^ k = φ' σ := by
    have := congrArg Prod.fst hk
    simpa [Φ] using this
  have hk2 : θ ⟨γ, hγ.1⟩ ^ k = θ σ := by
    have := congrArg Prod.snd hk
    simpa [Φ] using this
  rw [hσ] at hk2
  have hord : orderOf (θ ⟨γ, hγ.1⟩) = l := orderOf_eq_prime (hθl _) hθγ
  have hdvd : (l : ℤ) ∣ k := by
    rw [← hord]
    exact orderOf_dvd_iff_zpow_eq_one.2 hk2
  obtain ⟨j, rfl⟩ := hdvd
  have hu : φ' σ = 1 := by
    rw [← hk1, zpow_mul, zpow_natCast, hφ'l, one_zpow]
  have hv := congrArg Units.val hu
  simpa [φ'] using hv
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.GradedFlagMoves.UnipPow
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual Formalism.HC ReciprocityTheory.Gal IsLocalRing Polynomial UpperTheory.V.Base UpperTheory.V.Alg UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws

private theorem UpperTheory.V.Ws.Rt.pow_graded {k : Type} [Field k] (h : Fin 4 → ℕ) (N : M4 k)
    (hN : ∀ i j, h j ≤ h i → N i j = 0) (n : ℕ) : ∀ i j, h j < h i + n → (N ^ n) i j = 0 := by
  induction n with
  | zero =>
    intro i j hij
    rw [pow_zero, Matrix.one_apply_ne]
    rintro rfl
    omega
  | succ n ih =>
    intro i j hij
    rw [pow_succ, Matrix.mul_apply]
    refine Finset.sum_eq_zero fun m _ => ?_
    by_cases hm : h m < h i + n
    · rw [ih i m hm, zero_mul]
    · rw [hN m j (by omega), mul_zero]

private theorem UpperTheory.V.Ws.Rt.pow_char_graded {k : Type} [Field k] (l : ℕ) [Fact l.Prime] [CharP k l]
    (S : Finset (ℤ × ℤ)) (h : Fin 4 → ℕ) (hl : ∀ i, h i < l) (hS : ∀ i j, i ≠ j → h j ≤ h i → wt i j ∉ S)
    (X : M4 k) (h1 : ∀ i, X i i = 1) (hX : SuppM S X) : X ^ l = 1 := by
  obtain ⟨N, hNdef⟩ : ∃ N : M4 k, N = X - 1 := ⟨_, rfl⟩
  have hXN : X = 1 + N := by rw [hNdef]; abel
  have hN : ∀ i j, h j ≤ h i → N i j = 0 := by
    intro i j hij
    rw [hNdef, Matrix.sub_apply]
    by_cases hij' : i = j
    · subst hij'
      rw [h1, Matrix.one_apply_eq, sub_self]
    · rw [hX i j hij' (hS i j hij' hij), Matrix.one_apply_ne hij', sub_self]
  have hNl : N ^ l = 0 := by
    ext i j
    rw [Matrix.zero_apply]
    exact UpperTheory.V.Ws.Rt.pow_graded h N hN l i j (by have := hl j; omega)
  haveI : CharP (Matrix (Fin 4) (Fin 4) k) l := inferInstance
  rw [hXN, add_pow_char_of_commute (p := l) (h := Commute.one_left N), one_pow, hNl, add_zero]

theorem UpperTheory.V.Ws.Rt.unipPow :
    ∀ (k : Type) [Field k] (l : ℕ) [Fact l.Prime] [CharP k l] (X : M4 k), (∀ i, X i i = 1) →
      ((5 ≤ l ∧ (SuppM nP X ∨ SuppM nM X)) ∨ (3 ≤ l ∧ SuppM qQ X)) → X ^ l = 1 := by
  intro k _ l _ _ X h1 h
  rcases h with ⟨hl, h | h⟩ | ⟨hl, h⟩
  · refine UpperTheory.V.Ws.Rt.pow_char_graded l nP ![3, 1, 2, 0] (fun i => ?_) (by decide) X h1 h
    fin_cases i <;> simp <;> omega
  · refine UpperTheory.V.Ws.Rt.pow_char_graded l nM ![3, 2, 1, 0] (fun i => ?_) (by decide) X h1 h
    fin_cases i <;> simp <;> omega
  · refine UpperTheory.V.Ws.Rt.pow_char_graded l qQ ![2, 1, 1, 0] (fun i => ?_) (by decide) X h1 h
    fin_cases i <;> simp <;> omega
end

