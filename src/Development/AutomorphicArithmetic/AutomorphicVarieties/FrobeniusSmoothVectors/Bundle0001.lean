module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.Integral
public import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.Bundle0001
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.Bundle0005
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.Bundle0014
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.Bundle0002

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.AbEval
section
open IsLocalRing Matrix UpperTheory.V.Alg UpperTheory.V.U3 UpperTheory.V.Fr

namespace UpperTheory.V.Fr

private theorem ab_eval {k X : Type} [Field k] [Inhabited X] (r : ℕ) :
    ∀ H : Submodule k (X → k), Module.Finite k H → Module.finrank k H ≤ r →
      ∃ t : Fin r → X, ∀ φ ∈ H, (∀ a, φ (t a) = 0) → φ = 0 :=
  _root_.UpperTheory.Reformulated.B.Ra1.ab_eval r

private theorem ab_eval' {k X : Type} [Field k] [Inhabited X] (r : ℕ) (H : Submodule k (X → k))
    (hr : Module.rank k H ≤ r) : ∃ t : Fin r → X, ∀ φ ∈ H, (∀ a, φ (t a) = 0) → φ = 0 :=
  haveI : Module.Free k H := Module.Free.of_divisionRing k H
  ab_eval r H (Module.rank_lt_aleph0_iff.1 (hr.trans_lt Cardinal.natCast_lt_aleph0)) (Module.finrank_le_of_rank_le hr)

private theorem ab_char {l : ℕ} [Fact l.Prime] (k : Type) [Field k] [CharP k l] {B : Type} [CommGroup B] [Finite B]
    [Nontrivial B] (hB : IsPGroup l B) : ∃ ψ : B →* Multiplicative k, ∃ b, ψ b ≠ 1 := by
  obtain ⟨n, hn0, hn⟩ := hB.nontrivial_iff_card.1 inferInstance
  obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn0.ne'
  have hl : l.Prime := Fact.out
  obtain ⟨K, hK⟩ := Sylow.exists_subgroup_card_pow_prime (G := B) l (n := n) (hn ▸ pow_dvd_pow l n.le_succ)
  have hq : Nat.card (B ⧸ K) = l := by
    have := Subgroup.card_eq_card_quotient_mul_card_subgroup K
    rw [hn, hK, pow_succ'] at this
    exact (Nat.eq_of_mul_eq_mul_right (pow_pos hl.pos n) this).symm
  have hz : Nat.card (Multiplicative (ZMod l)) = l := by simp
  let e := mulEquivOfPrimeCardEq hq hz
  let j : Multiplicative (ZMod l) →* Multiplicative k :=
    AddMonoidHom.toMultiplicative (ZMod.castHom (dvd_refl l) k).toAddMonoidHom
  have hj : Function.Injective j := (ZMod.castHom (dvd_refl l) k).injective
  haveI : Nontrivial (B ⧸ K) := Finite.one_lt_card_iff_nontrivial.1 (hq.symm ▸ hl.one_lt)
  obtain ⟨q, hq1⟩ := exists_ne (1 : B ⧸ K)
  obtain ⟨b, rfl⟩ := QuotientGroup.mk_surjective q
  refine ⟨j.comp (e.toMonoidHom.comp (QuotientGroup.mk' K)), b, fun h => hq1 ?_⟩
  exact e.injective (hj (h.trans (by simp)))

variable {l : ℕ} [Fact l.Prime] {k : Type} [Field k] [CharP k l] {F : Frame l k} {C₀ : ℕ}

private theorem ab_plus (hF : F.Ok C₀) : ∃ t : Fin (1 + C₀) → F.Γ,
    ∀ (A : Type) [CommGroup A] [Finite A], IsPGroup l A → ∀ φ : F.Γ →* A, IsOpen (φ.ker : Set F.Γ) →
      (∀ a, φ (t a) = 1) → ∀ g, φ g = 1 := by
  let L : H1C F.loc (chRep (1 : F.Γ →* kˣ)) (fun _ => ⊤) →ₗ[k] (F.Γ → k) :=
    Submodule.liftQ _ ((LinearMap.fst k _ _).comp (Submodule.subtype _)) (by
      rintro x ⟨X, h, -⟩
      funext s
      simpa using h s)
  have hr : Module.rank k (LinearMap.range L) ≤ ((1 + C₀ : ℕ) : Cardinal) :=
    (rank_range_le L).trans (by exact_mod_cast hF.h1)
  haveI : Inhabited F.Γ := ⟨1⟩
  obtain ⟨t, ht⟩ := ab_eval' (1 + C₀) (LinearMap.range L) hr
  refine ⟨t, fun A _ _ hA φ ho hz g => ?_⟩
  by_contra hg
  haveI : Nontrivial φ.range := ⟨⟨φ.rangeRestrict g, 1, fun e => hg (congrArg Subtype.val e)⟩⟩
  obtain ⟨ψ, b, hb⟩ := ab_char k (hA.to_subgroup φ.range)
  obtain ⟨x, rfl⟩ := φ.rangeRestrict_surjective b
  let f : F.Γ → k := fun s => (ψ (φ.rangeRestrict s)).toAdd
  have hlc : IsLocallyConstant f := by
    refine (IsLocallyConstant.iff_exists_open _).2 fun s => ⟨(fun y => s⁻¹ * y) ⁻¹' φ.ker, ho.preimage (by fun_prop),
      by simp, fun y hy => ?_⟩
    have : φ.rangeRestrict y = φ.rangeRestrict s := by
      apply Subtype.ext
      have h : φ (s⁻¹ * y) = 1 := hy
      rw [map_mul, map_inv, inv_mul_eq_one] at h
      exact h.symm
    simp only [f, this]
  have hm : f ∈ LinearMap.range L :=
    ⟨Submodule.Quotient.mk ⟨(f, 0), hlc, fun s u => by simp [f], fun _ _ => trivial⟩, rfl⟩
  have := ht f hm fun a => by
    have : φ.rangeRestrict (t a) = 1 := Subtype.ext (hz a)
    simp [f, this]
  exact hb (congrFun this x)

private theorem ab_minus (hF : F.Ok C₀) : ∃ (s' : Fin F.d → F.G0) (h : ℕ), h ≠ 0 ∧
    (∀ a, ∃ v g, g ∈ F.Iv v ∧ F.Ψ (F.loc v g) = 1 ∧ s' a = F.loc0 v g) ∧
    ∀ (A : Type) [CommGroup A] [Finite A], IsPGroup l A → ∀ χ : F.G0 →* A, IsOpen (χ.ker : Set F.G0) →
      (∀ g, χ (F.star g) = χ g) → (∀ a, χ (s' a) = 1) → ∀ g, χ g ^ h = 1 := by
  choose u a₀ hu _ hgen using hF.gen
  obtain ⟨h, h0, hcl⟩ := hF.cl
  let e : (Σ v, Fin (F.dv v)) ≃ Fin F.d := Fintype.equivFinOfCardEq (by simp [Frame.d])
  refine ⟨fun a => F.loc0 (e.symm a).1 (u _ (e.symm a).2), h, h0,
    fun a => ⟨_, _, (hu _ _).1, (hu _ _).2, rfl⟩, fun A _ _ hA χ ho hs hz => hcl A hA χ ho ?_⟩
  have key : ∀ v, ∀ g ∈ F.Iv v, χ (F.loc0 v g) = 1 := fun v =>
    hgen v A hA (χ.comp (F.loc0 v)) (ho.preimage (hF.loc_cont v)) fun a => by
      have := hz (e ⟨v, a⟩)
      beta_reduce at this
      rw [e.symm_apply_apply] at this
      exact this
  rintro ⟨v, _ | _⟩ g hg
  · exact key v g hg
  · have := hs (F.loc0 v g)⁻¹
    rw [Frame.star, inv_inv, map_inv, key v g hg, inv_one] at this
    exact this

private theorem ab_ext (hF : F.Ok C₀) : ∃ π : F.Γ → F.G0, (∀ g : F.G0, π g = g) ∧
    ∀ (A : Type) [CommGroup A] (χ : F.G0 →* A), (∀ g, χ (F.conj g) = χ g) → ∃ φ : F.Γ →* A, ∀ γ, φ γ = χ (π γ) := by
  classical
  have hc : ∀ γ : F.Γ, γ ∉ F.del.ker → γ * F.c ∈ F.del.ker := fun γ h => by
    rw [MonoidHom.mem_ker] at h ⊢
    rw [map_mul, hF.del_c, (Int.units_eq_one_or _).resolve_left h]; simp
  have hci : F.c⁻¹ = F.c := inv_eq_of_mul_eq_one_right hF.c_sq
  have hcj : ∀ g : F.G0, (F.conj g : F.Γ) = F.c * g * F.c := fun g => by
    show F.c * g * F.c⁻¹ = _
    rw [hci]
  let π : F.Γ → F.G0 := fun γ => if h : γ ∈ F.del.ker then ⟨γ, h⟩ else ⟨γ * F.c, hc γ h⟩
  have p1 : ∀ γ, γ ∈ F.del.ker → (π γ : F.Γ) = γ := fun γ h => by simp only [π, dif_pos h]
  have p2 : ∀ γ, γ ∉ F.del.ker → (π γ : F.Γ) = γ * F.c := fun γ h => by simp only [π, dif_neg h]
  refine ⟨π, fun g => Subtype.ext (p1 g g.2), fun A _ χ hχ => ⟨MonoidHom.mk' (fun γ => χ (π γ)) fun a b => ?_, fun _ => rfl⟩⟩
  by_cases ha : a ∈ F.del.ker
  · rw [← map_mul]
    congr 1
    apply Subtype.ext
    by_cases hb : b ∈ F.del.ker
    · rw [Subgroup.coe_mul, p1 _ ha, p1 _ hb, p1 _ (mul_mem ha hb)]
    · rw [Subgroup.coe_mul, p1 _ ha, p2 _ hb, p2 _ fun h => hb ((Subgroup.mul_mem_cancel_left _ ha).1 h), mul_assoc]
  · show χ _ = χ _ * χ _
    rw [← hχ (π b), ← map_mul]
    congr 1
    apply Subtype.ext
    by_cases hb : b ∈ F.del.ker
    · rw [Subgroup.coe_mul, hcj, p2 _ ha, p1 _ hb, p2 _ fun h => ha ((Subgroup.mul_mem_cancel_right _ hb).1 h)]
      simp only [mul_assoc]
      rw [← mul_assoc F.c F.c, hF.c_sq, one_mul]
    · have hab : a * b ∈ F.del.ker := by
        rw [MonoidHom.mem_ker] at ha hb ⊢
        rw [map_mul, (Int.units_eq_one_or _).resolve_left ha, (Int.units_eq_one_or _).resolve_left hb]; simp
      rw [Subgroup.coe_mul, hcj, p2 _ ha, p2 _ hb, p1 _ hab]
      simp only [mul_assoc]
      rw [← mul_assoc F.c F.c, hF.c_sq, one_mul, mul_one]

end UpperTheory.V.Fr

theorem UpperTheory.V.Fr.ab_gen :
    ∀ {l : ℕ} [Fact l.Prime] {k : Type} [Field k] [CharP k l] {F : Frame l k} {C₀ : ℕ}, F.Ok C₀ → ∃ (s : Fin (1 + C₀ + F.d) → F.G0) (s' : Fin F.d → F.G0) (h : ℕ), h ≠ 0 ∧ (∀ a, F.Ψ (s a) = 1) ∧ (∀ a, ∃ v g, g ∈ F.Iv v ∧ F.Ψ (F.loc v g) = 1 ∧ s' a = F.loc0 v g) ∧ ∀ (A : Type) [CommGroup A] [Finite A], IsPGroup l A → ∀ χ : F.G0 →* A, IsOpen (χ.ker : Set F.G0) → ((∀ a, χ (s a) = 1) → ∀ g, χ g ^ h = 1) ∧ ((∀ g, χ (F.star g) = χ g) → (∀ a, χ (s' a) = 1) → ∀ g, χ g ^ h = 1) := by
  intro l _ k _ _ F C₀ hF
  obtain ⟨t, ht⟩ := ab_plus hF
  obtain ⟨s', h, h0, hs', hm⟩ := ab_minus hF
  obtain ⟨π, hπ, hext⟩ := ab_ext hF
  haveI := hF.fin
  have hcop : (Nat.card kˣ).Coprime l := by
    haveI := Fintype.ofFinite k
    obtain ⟨n, hl, hn⟩ := FiniteField.card k l
    rw [Nat.card_units, Nat.card_eq_fintype_card, hn]
    refine Nat.Coprime.coprime_dvd_right (dvd_pow_self l n.ne_zero) ?_
    exact (Nat.coprime_self_sub_left (Nat.one_le_pow _ _ hl.pos)).2 (Nat.coprime_one_left _)
  have hcc : ∀ g, F.conj (F.conj g) = g := fun g => Subtype.ext (by
    show F.c * (F.c * g * F.c⁻¹) * F.c⁻¹ = g
    rw [inv_eq_of_mul_eq_one_right hF.c_sq]
    simp only [mul_assoc]
    rw [← mul_assoc F.c F.c, hF.c_sq, one_mul, mul_one])
  have hcont : Continuous F.conj := by
    refine Continuous.subtype_mk (f := fun g : F.G0 => F.c * g * F.c⁻¹) (by fun_prop) _
  refine ⟨Fin.append (fun a => (π (t a) * F.conj (π (t a))) ^ Nat.card kˣ) s', s', h, h0, fun a => ?_, hs',
    fun A _ _ hA χ ho => ⟨fun hz => hm A hA χ ho ?_ fun a => by simpa using hz (Fin.natAdd _ a), hm A hA χ ho⟩⟩
  · refine Fin.addCases (fun a => ?_) (fun a => ?_) a
    · rw [Fin.append_left, Subgroup.coe_pow, map_pow, pow_card_eq_one']
    · rw [Fin.append_right]
      obtain ⟨v, g, -, h1, h2⟩ := hs' a
      rw [h2]; exact h1
  · obtain ⟨φ, hφ⟩ := hext A (χ * χ.comp F.conj) fun g => by simp [hcc, mul_comm]
    have hop : IsOpen (φ.ker : Set F.Γ) := by
      refine Subgroup.isOpen_mono (H₁ := (χ.ker ⊓ χ.ker.comap F.conj).map F.del.ker.subtype) ?_ ?_
      · rintro _ ⟨g, ⟨h1, h2⟩, rfl⟩
        show φ g = 1
        rw [hφ, hπ]
        exact (congrArg₂ (· * ·) h1 h2).trans (mul_one 1)
      · exact hF.del_open.isOpenMap_subtype_val _ (ho.inter (ho.preimage hcont))
    have h1 := ht A hA φ hop fun a => by
      have := hz (Fin.castAdd _ a)
      rw [Fin.append_left, map_pow, map_mul] at this
      obtain ⟨n, hn⟩ := hA (χ (π (t a)) * χ (F.conj (π (t a))))
      rw [hφ]
      exact orderOf_eq_one_iff.1 (Nat.eq_one_of_dvd_coprimes (hcop.pow_right n) (orderOf_dvd_of_pow_eq_one this)
        (orderOf_dvd_of_pow_eq_one hn))
    intro g
    have := h1 (g⁻¹ : F.G0)
    rw [hφ, hπ] at this
    have h2 : χ g⁻¹ * χ (F.star g) = 1 := this
    rw [map_inv, inv_mul_eq_one] at h2
    exact h2.symm
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.AddMulSelfEqOfOrthogonalIdempotents
section
open IsLocalRing Matrix UpperTheory.V.Alg UpperTheory.V.U3 UpperTheory.V.Fr

private theorem UpperTheory.V.Fr.add_mul_self_eq_of_orthogonal_idempotents {C K : Type} [CommRing C] [CommRing K] [Algebra C K] {n : ℕ}
    (hn : n = 2 ∨ n = 3) (A : Subalgebra C (Matrix (Fin n) (Fin n) K)) (h2 : IsUnit (2 : C))
    (hY : Matrix.diagonal (fun i => (w n i : K)) ∈ A) (i : Fin n) : Matrix.single i i (1 : K) ∈ A := by
  have key : ∀ M : Matrix (Fin n) (Fin n) K, (2 : C) • M ∈ A → M ∈ A := by
    intro M hM
    have := A.smul_mem hM (↑h2.unit⁻¹ : C)
    rwa [smul_smul, IsUnit.val_inv_mul, one_smul] at this
  have hYY := A.mul_mem hY hY
  rcases hn with rfl | rfl
  · apply key
    fin_cases i
    · have e : (2 : C) • Matrix.single (0 : Fin 2) 0 (1 : K) = 1 + Matrix.diagonal (fun i => (w 2 i : K)) := by
        ext a b
        fin_cases a <;> fin_cases b <;> simp [w, two_smul, Matrix.one_apply, Matrix.single_apply] <;> norm_num
      have h := A.add_mem A.one_mem hY
      rw [← e] at h
      exact h
    · have e : (2 : C) • Matrix.single (1 : Fin 2) 1 (1 : K) = 1 - Matrix.diagonal (fun i => (w 2 i : K)) := by
        ext a b
        fin_cases a <;> fin_cases b <;> simp [w, two_smul, Matrix.one_apply, Matrix.single_apply] <;> norm_num
      have h := A.sub_mem A.one_mem hY
      rw [← e] at h
      exact h
  · apply key
    fin_cases i
    · have e : (2 : C) • Matrix.single (0 : Fin 3) 0 (1 : K) =
          Matrix.diagonal (fun i => (w 3 i : K)) * Matrix.diagonal (fun i => (w 3 i : K)) +
            Matrix.diagonal (fun i => (w 3 i : K)) := by
        ext a b
        fin_cases a <;> fin_cases b <;> simp [w, two_smul, Matrix.single_apply] <;> norm_num
      have h := A.add_mem hYY hY
      rw [← e] at h
      exact h
    · have e : (2 : C) • Matrix.single (1 : Fin 3) 1 (1 : K) =
          (2 : C) • (1 - Matrix.diagonal (fun i => (w 3 i : K)) * Matrix.diagonal (fun i => (w 3 i : K))) := by
        ext a b
        fin_cases a <;> fin_cases b <;> simp [w, two_smul, Matrix.one_apply, Matrix.single_apply] <;> norm_num
      have h := A.smul_mem (A.sub_mem A.one_mem hYY) (2 : C)
      rw [← e] at h
      exact h
    · have e : (2 : C) • Matrix.single (2 : Fin 3) 2 (1 : K) =
          Matrix.diagonal (fun i => (w 3 i : K)) * Matrix.diagonal (fun i => (w 3 i : K)) -
            Matrix.diagonal (fun i => (w 3 i : K)) := by
        ext a b
        fin_cases a <;> fin_cases b <;> simp [w, two_smul, Matrix.single_apply] <;> norm_num
      have h := A.sub_mem hYY hY
      rw [← e] at h
      exact h

theorem UpperTheory.V.Fr.idem :
    ∀ {l : ℕ} [Fact l.Prime] {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [IsCoef l O] {F : Frame l (ResidueField O)} {C₀ : ℕ} {n : ℕ}, F.Ok C₀ → (n = 2 ∨ n = 3) → ∀ (C : Type) [CommRing C] [Algebra O C] [IsCO O C] (K : Type) [CommRing K] [Algebra C K] (ρ : NRep F n K), Integral O C ρ → ∀ i, Matrix.single i i (1 : K) ∈ Submodule.span C (Set.range ρ.r) := by
  intro l _ O _ _ _ _ F C₀ n hF hn C _ _ _ K _ _ ρ hI i
  haveI : CharP (ResidueField O) l := IsCoef.char
  have hunit : ∀ x : C, res O C x ≠ 0 → IsUnit x := by
    intro x hx
    by_contra h
    exact hx ((res_eq_zero_iff O C x).2 ((IsLocalRing.mem_maximalIdeal x).2 h))
  have h2 : IsUnit (2 : C) := by
    apply hunit
    rw [map_ofNat]
    intro h0
    have h0' : ((2 : ℕ) : ResidueField O) = 0 := by exact_mod_cast h0
    rw [CharP.cast_eq_zero_iff (ResidueField O) l] at h0'
    exact hF.l_odd ((Nat.prime_dvd_prime_iff_eq (Fact.out : l.Prime) Nat.prime_two).1 h0')
  obtain ⟨ζ, hζr, hζ⟩ := hI.ze
  have hζu : IsUnit ζ := by
    apply hunit
    rw [hζr]
    intro h0
    apply hF.baseSubgroup_spec
    rw [sub_eq_zero] at h0
    try simp only [← Units.val_inv_eq_inv_val] at h0
    have hx : F.Ψ ↑F.g0 = (F.Ψ ↑F.g0)⁻¹ := Units.ext h0
    calc F.Ψ ↑F.g0 ^ 2 = F.Ψ ↑F.g0 * F.Ψ ↑F.g0 := sq _
      _ = F.Ψ ↑F.g0 * (F.Ψ ↑F.g0)⁻¹ := by rw [← hx]
      _ = 1 := mul_inv_cancel _
  have hD : ρ.r F.g0 - ρ.r (F.star F.g0) = ζ • Matrix.diagonal (fun i => (w n i : K)) := by
    ext a b
    by_cases hab : a = b
    · subst hab
      rw [Matrix.smul_apply, Matrix.diagonal_apply_eq, Algebra.smul_def, hζ a]
      ring
    · rw [Matrix.smul_apply, Matrix.diagonal_apply_ne _ hab, smul_zero]
      exact ρ.diag a b hab
  have hspan : (Algebra.adjoin C (Set.range ρ.r)).toSubmodule = Submodule.span C (Set.range ρ.r) := by
    rw [Algebra.adjoin_eq_span, ← MonoidHom.coe_mrange, Submonoid.closure_eq]
  have hmem : ρ.r F.g0 - ρ.r (F.star F.g0) ∈ Submodule.span C (Set.range ρ.r) :=
    Submodule.sub_mem _ (Submodule.subset_span ⟨_, rfl⟩) (Submodule.subset_span ⟨_, rfl⟩)
  have hY : Matrix.diagonal (fun i => (w n i : K)) ∈ Algebra.adjoin C (Set.range ρ.r) := by
    rw [← Subalgebra.mem_toSubmodule, hspan]
    have h := Submodule.smul_mem _ (↑hζu.unit⁻¹ : C) hmem
    rwa [hD, smul_smul, IsUnit.val_inv_mul, one_smul] at h
  rw [← hspan, Subalgebra.mem_toSubmodule]
  exact UpperTheory.V.Fr.add_mul_self_eq_of_orthogonal_idempotents hn _ h2 hY i
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.AdicCharUnipotentPgroupQuotient
section
open IsLocalRing Matrix UpperTheory.V.Alg UpperTheory.V.U3 UpperTheory.V.Fr

theorem UpperTheory.V.Fr.adic_char_unipotent_pgroup_quotient :
    ∀ {l : ℕ} [Fact l.Prime] {Q : Type} [CommRing Q] [IsDomain Q] [IsLocalRing Q] [IsNoetherianRing Q] [CharP Q l] [Finite (ResidueField Q)] {G : Type} [Group G] [TopologicalSpace G] (χ : G →* Q) (h : ℕ), h ≠ 0 → AdicCont (maximalIdeal Q) χ → (∀ g, χ g - 1 ∈ maximalIdeal Q) → (∀ (A : Type) [CommGroup A] [Finite A], IsPGroup l A → ∀ ψ : G →* A, IsOpen (ψ.ker : Set G) → (∀ g g', χ g = χ g' → ψ g = ψ g') → ∀ g, ψ g ^ h = 1) → ∀ g, χ g = 1 := by
  intro l hl Q _ _ _ _ _ hfin G _ _ χ h hh hc hm H g
  have hp : l.Prime := hl.out
  have krull : ∀ x : Q, (∀ N : ℕ, Ideal.Quotient.mk (maximalIdeal Q ^ N) x = 1) → x = 1 := by
    intro x hx
    have h0 : x - 1 ∈ (⨅ N : ℕ, maximalIdeal Q ^ N) := by
      rw [Ideal.mem_iInf]
      intro N
      rw [← Ideal.Quotient.eq, hx N, map_one]
    rw [Ideal.iInf_pow_eq_bot_of_isLocalRing _ (maximalIdeal.isMaximal Q).ne_top, Ideal.mem_bot] at h0
    exact sub_eq_zero.mp h0
  have unip : ∀ (N : ℕ) (g : G), Ideal.Quotient.mk (maximalIdeal Q ^ N) (χ g) ^ (l ^ N) = 1 := by
    intro N g
    rw [← map_pow, ← map_one (Ideal.Quotient.mk (maximalIdeal Q ^ N)), Ideal.Quotient.eq]
    have : χ g ^ l ^ N - 1 = (χ g - 1) ^ l ^ N := by rw [sub_pow_char_pow, one_pow]
    rw [this]
    exact Ideal.pow_le_pow_right (Nat.lt_pow_self hp.one_lt).le (Ideal.pow_mem_pow (hm g) _)
  have hpow : χ g ^ h = 1 := by
    apply krull
    intro N
    haveI : Finite (Q ⧸ maximalIdeal Q) := hfin
    haveI : Finite (Q ⧸ maximalIdeal Q ^ N) :=
      Ideal.finite_quotient_pow (IsNoetherian.noetherian _) N
    let φ : G →* (Q ⧸ maximalIdeal Q ^ N)ˣ :=
      ((Ideal.Quotient.mk (maximalIdeal Q ^ N)).toMonoidHom.comp χ).toHomUnits
    have hφ : ∀ g, (φ g : Q ⧸ maximalIdeal Q ^ N) = Ideal.Quotient.mk _ (χ g) := fun g => rfl
    have hP : IsPGroup l φ.range := by
      rintro ⟨_, g, rfl⟩
      refine ⟨N, Subtype.ext (Units.ext ?_)⟩
      simpa [hφ] using unip N g
    have hO : IsOpen (φ.rangeRestrict.ker : Set G) := by
      have := (hc N).isOpen_fiber 1
      convert this using 1
      ext g
      simp only [SetLike.mem_coe, MonoidHom.mem_ker, Set.mem_setOf_eq]
      rw [← hφ, Units.val_eq_one, Subtype.ext_iff]
      rfl
    have := H φ.range hP φ.rangeRestrict hO
      (fun g g' e => Subtype.ext (Units.ext (by
        change (φ g : Q ⧸ maximalIdeal Q ^ N) = φ g'
        rw [hφ, hφ, e]))) g
    have h2 : φ g ^ h = 1 := congrArg Subtype.val this
    rw [map_pow, ← hφ, ← Units.val_pow_eq_pow_val, h2, Units.val_one]
  obtain ⟨a, h', hnd, rfl⟩ := Nat.exists_eq_pow_mul_and_not_dvd hh l hp.ne_one
  have h3 : χ g ^ h' = 1 := by
    have : (χ g ^ h' - 1) ^ l ^ a = 0 := by
      rw [sub_pow_char_pow, one_pow, ← pow_mul, mul_comm, hpow, sub_self]
    exact sub_eq_zero.mp (pow_eq_zero_iff (pow_ne_zero _ hp.ne_zero) |>.mp this)
  apply krull
  intro N
  have h4 : Ideal.Quotient.mk (maximalIdeal Q ^ N) (χ g) ^ h' = 1 := by
    rw [← map_pow, h3, map_one]
  have hcop : Nat.Coprime (l ^ N) h' := Nat.Coprime.pow_left _ ((Nat.Prime.coprime_iff_not_dvd hp).mpr hnd)
  have h5 : orderOf (Ideal.Quotient.mk (maximalIdeal Q ^ N) (χ g)) ∣ 1 := by
    rw [← hcop.gcd_eq_one]
    exact Nat.dvd_gcd (orderOf_dvd_of_pow_eq_one (unip N g)) (orderOf_dvd_of_pow_eq_one h4)
  exact orderOf_eq_one_iff.mp (Nat.dvd_one.mp h5)
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.CornerUnits
section
noncomputable section

open IsLocalRing Matrix UpperTheory.V.Alg UpperTheory.V.U3

namespace UpperTheory.V.Fr

variable {l : ℕ} [Fact l.Prime] {k : Type} [Field k] {F : Frame l k} {K : Type} [CommRing K]

def cor : Fin 2 → Fin 3 := ![0, 2]

theorem w_cor (i : Fin 2) : w 3 (cor i) = w 2 i := by
  fin_cases i <;> rfl

structure IsCorner (ρ : NRep F 3 K) (σ : NRep F 2 K) : Prop where
  odd : ∀ g i j, Odd (w 3 i - w 3 j) → ρ.r g i j = 0
  r : ∀ g i j, σ.r g i j = ρ.r g (cor i) (cor j)
  ψ : ∀ v i g, σ.ψ v i g = ρ.ψ v (cor i) g
  mid : ∀ v g, ρ.r (F.loc0 v g) 1 1 = ρ.ψ v 1 g

def CornerUnits (ρ : NRep F 3 K) : Prop :=
  ∀ v, ∃ g, IsUnit (ρ.r (F.loc0 v g) 1 1 - ρ.ψ v 0 g) ∧ IsUnit (ρ.r (F.loc0 v g) 1 1 - ρ.ψ v 2 g) ∧
    IsUnit ((ρ.r (F.loc0 v g) 0 0 - ρ.ψ v 1 g) * (ρ.r (F.loc0 v g) 2 2 - ρ.ψ v 1 g) -
      ρ.r (F.loc0 v g) 0 2 * ρ.r (F.loc0 v g) 2 0)

theorem mid_mul (ρ : NRep F 3 K) (h : ∀ g i j, Odd (w 3 i - w 3 j) → ρ.r g i j = 0) (g g' : F.G0) :
    ρ.r (g * g') 1 1 = ρ.r g 1 1 * ρ.r g' 1 1 := by
  rw [map_mul, Matrix.mul_apply, Fin.sum_univ_three, h g 1 0 (by decide), h g 1 2 (by decide)]
  simp

end UpperTheory.V.Fr
end
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.DetMem
section
open IsLocalRing Matrix UpperTheory.V.Alg UpperTheory.V.U3 UpperTheory.V.Fr

theorem UpperTheory.V.Fr.det_mem :
    ∀ {l : ℕ} [Fact l.Prime] {O : Type} [CommRing O] [IsDomain O]
      [IsDiscreteValuationRing O] [IsCoef l O] {F : Frame l (ResidueField O)} {C₀ n : ℕ},
      F.Ok C₀ → (n = 2 ∨ n = 3) → ∀ (S : Space O F n) (m : ℕ) (g : Fin m → F.G0)
        (α : Fin m →₀ ℕ),
        (∑ a, (MvPolynomial.X a : MvPolynomial (Fin m) S.R) •
          (S.ρ.r (g a)).map MvPolynomial.C).det.coeff α ∈ S.B := by
  intro l _ O _ _ _ _ F C₀ n _ _ S m g α
  classical
  rw [Matrix.det_apply, MvPolynomial.coeff_sum]
  refine sum_mem (fun σ _ => ?_)
  rw [Units.smul_def, MvPolynomial.coeff_smul]
  refine zsmul_mem ?_ _
  simp only [Matrix.sum_apply, Matrix.smul_apply, Matrix.map_apply, smul_eq_mul]
  rw [Finset.prod_univ_sum, MvPolynomial.coeff_sum]
  refine sum_mem (fun f _ => ?_)
  rw [Finset.prod_mul_distrib, ← map_prod, mul_comm, MvPolynomial.coeff_C_mul]
  refine mul_mem (S.mon_mem ?_) ?_
  · refine ⟨List.ofFn (fun i => (g (f i), σ i, i)), ?_, ?_⟩
    · rw [List.map_ofFn, List.sum_ofFn]
      simp only [Function.comp_def]
      rw [Finset.sum_sub_distrib, Equiv.sum_comp, sub_self]
    · rw [List.map_ofFn, List.prod_ofFn]
      rfl
  · obtain ⟨d, hd⟩ : ∃ d, ∏ i, (MvPolynomial.X (f i) : MvPolynomial (Fin m) S.R) =
        MvPolynomial.monomial d 1 := by
      refine Finset.prod_induction _ (fun p => ∃ d, p = MvPolynomial.monomial d 1) ?_ ?_ ?_
      · rintro a b ⟨d₁, rfl⟩ ⟨d₂, rfl⟩
        exact ⟨d₁ + d₂, by rw [MvPolynomial.monomial_mul, mul_one]⟩
      · exact ⟨0, by rw [MvPolynomial.monomial_zero', MvPolynomial.C_1]⟩
      · intro i _
        exact ⟨Finsupp.single (f i) 1, rfl⟩
    rw [hd, MvPolynomial.coeff_monomial]
    split_ifs
    · exact one_mem _
    · exact zero_mem _
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.FlagLoc
section
open IsLocalRing Matrix UpperTheory.V.Alg UpperTheory.V.U3 UpperTheory.V.Fr

private theorem entry_of_conj {C : Type} [CommRing C] {n : ℕ} (g : GL (Fin n) C) (f : Fin n → Matrix (Fin n) (Fin n) C)
    (hg : ∀ i, (g : Matrix (Fin n) (Fin n) C) * f i * ((g⁻¹ : GL (Fin n) C) : Matrix (Fin n) (Fin n) C) = single i i 1)
    (M : Matrix (Fin n) (Fin n) C) (a b : Fin n) :
    ((g : Matrix (Fin n) (Fin n) C) * M * ((g⁻¹ : GL (Fin n) C) : Matrix (Fin n) (Fin n) C)) a b =
      ((g : Matrix (Fin n) (Fin n) C) * (f a * M * f b) * ((g⁻¹ : GL (Fin n) C) : Matrix (Fin n) (Fin n) C)) a b := by
  have h : (g : Matrix (Fin n) (Fin n) C) * (f a * M * f b) * ((g⁻¹ : GL (Fin n) C) : Matrix (Fin n) (Fin n) C) =
      single a a 1 * ((g : Matrix (Fin n) (Fin n) C) * M * ((g⁻¹ : GL (Fin n) C) : Matrix (Fin n) (Fin n) C)) *
        single b b 1 := by
    rw [← hg a, ← hg b]
    simp only [mul_assoc, Units.inv_mul_cancel_left]
  rw [h, Matrix.mul_single_apply_same, Matrix.single_mul_apply_same, one_mul, mul_one]

theorem UpperTheory.V.Fr.flag_loc :
    ∀ {H C : Type} [Group H] [CommRing C] [IsLocalRing C] {n : ℕ} (r : H →* Matrix (Fin n) (Fin n) C) (ψ : Fin n → H →* Cˣ) (g₀ : H), (∀ i j, i ≠ j → IsUnit ((ψ i g₀ : C) - ψ j g₀)) → ((r g₀).map (residue C)).charpoly = ∏ i, (Polynomial.X - Polynomial.C (residue C (ψ i g₀))) → (∀ g, ordProd r (fun i s => (ψ i s : C)) g = 0) → UpperTheory.V.W.HasFlag r.toHomUnits ψ := by
  intro H C _ _ _ n r ψ g₀ hu hc ho
  have h0 := UpperTheory.V.AlgebraTools.ord_ext (R := C) r (fun i => (Units.coeHom C).comp (ψ i)) (fun g => by
    have := ho g
    unfold ordProd at this
    simpa only [Algebra.algebraMap_eq_smul_one, MonoidHom.comp_apply, Units.coeHom_apply] using this)
  obtain ⟨h1, h2, h3⟩ := UpperTheory.V.AlgebraTools.lag_triangular (MonoidAlgebra.lift C (Matrix (Fin n) (Fin n) C) H r)
    (fun i => MonoidAlgebra.lift C C H ((Units.coeHom C).comp (ψ i))) (MonoidAlgebra.of C H g₀) h0
    (fun i j hij => by simpa using hu i j hij)
  simp only [MonoidAlgebra.lift_of, MonoidHom.comp_apply, Units.coeHom_apply] at h1 h2 h3
  have h4 := UpperTheory.V.AlgebraTools.lag_ne_zero (fun i => (ψ i g₀ : C)) (r g₀) hu (by rw [← Matrix.charpoly_map, hc])
  obtain ⟨g, hg⟩ := UpperTheory.V.AlgebraTools.coi_conj_single _ h1 h4
  refine ⟨g, fun s => ⟨fun i j hij => ?_, fun i => ?_⟩⟩
  · have h5 := h2 (MonoidAlgebra.of C H s) i j hij
    rw [MonoidAlgebra.lift_of] at h5
    have h6 := entry_of_conj g _ hg (r s) i j
    rw [h5, mul_zero, zero_mul] at h6
    exact h6
  · have h5 := h3 (MonoidAlgebra.of C H s) i
    rw [MonoidAlgebra.lift_of, MonoidAlgebra.lift_of] at h5
    have h6 := entry_of_conj g _ hg (r s) i i
    rw [h5, mul_smul_comm, smul_mul_assoc, hg] at h6
    refine h6.trans ?_
    simp
end

