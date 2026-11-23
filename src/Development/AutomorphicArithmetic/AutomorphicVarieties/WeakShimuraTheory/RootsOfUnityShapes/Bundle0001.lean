module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.NearSplit
public import Development.AutomorphicArithmetic.AutomorphicVarieties.SymplecticGSp4.Bundle0004
public import Development.AutomorphicArithmetic.AutomorphicVarieties.CharacterLevelBounds.Bundle0002
public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.SelmerTransport.Bundle0007
public import Development.AutomorphicArithmetic.AutomorphicVarieties.HeightAndVanishing.Bundle0004
public import GroundTheory.GlobalFields.CyclotomicCharacters.PadicUnitsLog

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.RootsOfUnityShapes.ConjFlag
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual Formalism.HC ReciprocityTheory.Gal IsLocalRing Polynomial UpperTheory.V.Base UpperTheory.V.Alg UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws

private theorem up_mul {R : Type} [CommRing R] {X Y : M4 R} (hX : IsUp X) (hY : IsUp Y) : IsUp (X * Y) := by
  intro i j h
  rw [Matrix.mul_apply]
  refine Finset.sum_eq_zero fun k _ => ?_
  by_cases hk : k < i
  · rw [hX i k hk, zero_mul]
  · rw [hY k j (lt_of_lt_of_le h (not_lt.1 hk)), mul_zero]

private theorem up_mul_diag {R : Type} [CommRing R] {X Y : M4 R} (hX : IsUp X) (hY : IsUp Y) (i : Fin 4) :
    (X * Y : M4 R) i i = X i i * Y i i := by
  rw [Matrix.mul_apply]
  refine Finset.sum_eq_single i (fun k _ hk => ?_) (fun h => absurd (Finset.mem_univ i) h)
  rcases lt_or_gt_of_ne hk with h | h
  · rw [hX i k h, zero_mul]
  · rw [hY k i h, mul_zero]

private theorem up_adj {R : Type} [CommRing R] {X : M4 R} (hX : IsUp X) : IsUp (adj X) := by
  intro i j h
  rw [adj_apply, hX _ _ (Fin.rev_lt_rev.2 h), smul_zero]

private theorem gsp_mul_adj {R : Type} [CommRing R] {ν μ : R} {P : M4 R} (hμ : μ * ν = 1) (h : IsGSp ν P) :
    P * adj P = ν • (1 : M4 R) := by
  have h' : adj P * P = ν • (1 : M4 R) := h
  have h1 : (μ • adj P) * P = 1 := by
    rw [Matrix.smul_mul, h', smul_smul, hμ, one_smul]
  have h2 : P * (μ • adj P) = 1 := mul_eq_one_comm.mp h1
  calc P * adj P = (ν * μ) • (P * adj P) := by rw [mul_comm, hμ, one_smul]
    _ = ν • (P * (μ • adj P)) := by rw [Matrix.mul_smul, smul_smul]
    _ = ν • (1 : M4 R) := by rw [h2]

theorem UpperTheory.V.Ws.Rq.conjFlag :
    ∀ (R : Type) [CommRing R] (ν : R) (X Y Z n₀ n : M4 R), IsUnit ν → IsGSp ν X → IsLow n₀ → IsLow n → IsUp (adj n * X * n₀) →
      Z * X = X * Y → IsUp (adj n₀ * Y * n₀) → IsUp (adj n * Z * n) ∧ ∀ i, (adj n * Z * n) i i = (adj n₀ * Y * n₀) i i := by
  intro R _ ν X Y Z n₀ n hν hX hn₀ hn hU hZ hV
  obtain ⟨hadj, hadj2, -, -, -, -, -, -, -⟩ := grp R
  obtain ⟨u, rfl⟩ := hν
  have hμ : ((u⁻¹ : Rˣ) : R) * u = 1 := u.inv_mul
  have hn1 : n * adj n = 1 := by
    have := gsp_mul_adj (μ := (1 : R)) (one_mul 1) hn.1
    rwa [one_smul] at this
  have hn01 : n₀ * adj n₀ = 1 := by
    have := gsp_mul_adj (μ := (1 : R)) (one_mul 1) hn₀.1
    rwa [one_smul] at this
  have hn0 : adj n₀ * n₀ = 1 := by
    have h : adj n₀ * n₀ = (1 : R) • (1 : M4 R) := hn₀.1
    rwa [one_smul] at h
  have hXg : adj X * X = (u : R) • (1 : M4 R) := hX
  have hn1' : ∀ W : M4 R, n * (adj n * W) = W := by
    intro W; rw [← Matrix.mul_assoc, hn1, Matrix.one_mul]
  have hn01' : ∀ W : M4 R, n₀ * (adj n₀ * W) = W := by
    intro W; rw [← Matrix.mul_assoc, hn01, Matrix.one_mul]
  obtain ⟨U, hUdef⟩ : ∃ U, U = adj n * X * n₀ := ⟨_, rfl⟩
  rw [← hUdef] at hU
  have hUg : adj U * U = (u : R) • (1 : M4 R) := by
    rw [hUdef, hadj, hadj, hadj2]
    simp only [Matrix.mul_assoc, hn1']
    rw [← Matrix.mul_assoc (adj X) X, hXg, Matrix.smul_mul, Matrix.one_mul, Matrix.mul_smul, hn0]
  have hUa : U * adj U = (u : R) • (1 : M4 R) := gsp_mul_adj hμ hUg
  have hWU : adj n * Z * n * U = U * (adj n₀ * Y * n₀) := by
    rw [hUdef]
    simp only [Matrix.mul_assoc, hn1', hn01']
    rw [← Matrix.mul_assoc Z X, hZ]
    simp only [Matrix.mul_assoc]
  have hνW : (u : R) • (adj n * Z * n) = U * (adj n₀ * Y * n₀) * adj U := by
    rw [← hWU, Matrix.mul_assoc _ U, hUa, Matrix.mul_smul, Matrix.mul_one]
  have hup : IsUp (U * (adj n₀ * Y * n₀) * adj U) := up_mul (up_mul hU hV) (up_adj hU)
  have hWup : IsUp (adj n * Z * n) := by
    intro i j hij
    have h1 := congrFun (congrFun hνW i) j
    rw [Matrix.smul_apply, smul_eq_mul, hup i j hij] at h1
    exact (Units.mul_right_eq_zero u).mp h1
  refine ⟨hWup, fun i => ?_⟩
  have h1 := congrFun (congrFun hνW i) i
  rw [Matrix.smul_apply, smul_eq_mul, up_mul_diag (up_mul hU hV) (up_adj hU), up_mul_diag hU hV] at h1
  have h2 := congrFun (congrFun hUg i) i
  rw [up_mul_diag (up_adj hU) hU, Matrix.smul_apply, Matrix.one_apply_eq, smul_eq_mul, mul_one] at h2
  apply u.isUnit.mul_left_cancel
  rw [h1, ← h2]
  ring
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.RootsOfUnityShapes.KillQ
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual Formalism.HC ReciprocityTheory.Gal IsLocalRing Polynomial UpperTheory.V.Base UpperTheory.V.Alg UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws

theorem UpperTheory.V.Ws.Rq.killQ :
    ∀ {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {l : ℕ} [Fact l.Prime] {c : Coef l} (D : Raw Ω c), D.Good → ∀ T : Tower D, T.Ok →
      ∀ (pr : Bool) (g0 : G ℚ Ω) (M : Type) [Monoid M] (r : G ℚ Ω →* M), (∀ g ∈ (frQ D pr g0).N, r g = 1) →
        ∀ g ∈ (T.fr ∅).N, r (resQ T.F g) = 1 := by
  intro Ω _ _ _ l _ c D hD T hT pr g0 M _ r hr g hg
  obtain ⟨A, hA, hI, hb⟩ := hg
  have hIQ : resQ T.F g ∈ Ine (F := ℚ) A := hI
  have hl : ¬ A.valuation (l : Ω) < 1 := hA l (Finset.mem_insert_self _ _)
  by_cases hw : Raw.Away D.T A
  · exact hr _ (Or.inl ⟨A, hw, hIQ, hb⟩)
  · have hw' : ∃ p ∈ D.T, A.valuation (p : Ω) < 1 := by
      by_contra h
      exact hw fun p hp hv => h ⟨p, hp, hv⟩
    obtain ⟨p, hp, hv⟩ := hw'
    rcases Finset.mem_insert.1 hp with rfl | hp
    · exact absurd hv hl
    have hpS : p ∈ D.S := by
      unfold Raw.Sb at hp
      exact Finset.mem_of_mem_filter _ hp
    have hpp : p.Prime := hD.S_prime p hpS
    obtain ⟨u, -, hu⟩ := (UpperTheory.V.Chr.placesQ Ω).2.2 p A (D.pl p) hpp hv (hD.pl_over p hpp)
    have hψ : D.ψ (resQ T.F g) = 1 :=
      hT.kb A (fun q hq => by rw [Finset.mem_singleton.1 hq]; exact hl) g hI hb
    have hk : u⁻¹ * resQ T.F g * u ∈ D.ψ.ker := by
      rw [MonoidHom.mem_ker, map_mul, map_mul, hψ, mul_one, ← map_mul, inv_mul_cancel, map_one]
    have h1 : r (u⁻¹ * resQ T.F g * u) = 1 := hr _ (Or.inr ⟨p, hp, hu _ hIQ, hk⟩)
    have h2 : resQ T.F g = u * (u⁻¹ * resQ T.F g * u) * u⁻¹ := by group
    rw [h2, map_mul, map_mul, h1, mul_one, ← map_mul, mul_inv_cancel, map_one]
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.RootsOfUnityShapes.MuPow
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual Formalism.HC ReciprocityTheory.Gal IsLocalRing Polynomial UpperTheory.V.Base UpperTheory.V.Alg UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws

private theorem mu_pow {Γ M : Type} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ] [CommGroup M] {l : ℕ}
    (f : Γ →* M) (hf : IsClosed (f.ker : Set Γ)) {H : Subgroup Γ} {s : Γ} (hs : s ∈ muOf l H) :
    ∃ a : ℕ, f s ^ l ^ a = 1 := by
  obtain ⟨-, a, ha⟩ := hs
  refine ⟨a, ?_⟩
  have hle : ⁅H, H⁆ ≤ f.ker := by
    rw [Subgroup.commutator_le]
    intro x _ y _
    rw [MonoidHom.mem_ker, map_commutatorElement, commutatorElement_eq_one_iff_commute]
    exact Commute.all _ _
  have hmem := Subgroup.topologicalClosure_minimal _ hle hf ha
  rwa [MonoidHom.mem_ker, map_pow] at hmem

private theorem one_of {M : Type} [Monoid M] {x : M} {l a m : ℕ} (h : l.Coprime m) (h1 : x ^ l ^ a = 1)
    (h2 : x ^ m = 1) : x = 1 := by
  have hc : Nat.Coprime (l ^ a) m := Nat.Coprime.pow_left a h
  have hd := Nat.dvd_gcd (orderOf_dvd_of_pow_eq_one h1) (orderOf_dvd_of_pow_eq_one h2)
  rw [Nat.Coprime.gcd_eq_one hc, Nat.dvd_one, orderOf_eq_one_iff] at hd
  exact hd

theorem UpperTheory.V.Ws.Rq.muPs :
    ∀ {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {l : ℕ} [Fact l.Prime] {c : Coef l} (D : Raw Ω c), D.Good → ∀ T : Tower D, T.Ok →
      ∀ H : Subgroup (G T.F Ω), ∀ s ∈ muOf l H, ∀ i, D.ps i (resQ T.F s) = 1 := by
  intro Ω _ _ _ l _ c D hD T hT H s hs i
  haveI : IsAlgClosure T.F Ω := ⟨IsAlgClosure.isAlgClosed ℚ, Algebra.IsAlgebraic.tower_top (K := ℚ) T.F⟩
  have hcont : Continuous (resQ T.F) := (galEmbTop ℚ T.F Ω).1.continuous
  have hlp : l.Prime := Fact.out
  have gen : ∀ (χ : G ℚ Ω →* (c.O)ˣ) (m : ℕ), l.Coprime m →
      IsClosed ((χ.comp (resQ T.F)).ker : Set (G T.F Ω)) → χ (resQ T.F s) ^ m = 1 → χ (resQ T.F s) = 1 := by
    intro χ m hm hcl h2
    obtain ⟨a, ha⟩ := mu_pow (χ.comp (resQ T.F)) hcl hs
    exact one_of hm ha h2
  have closedOfOpen : ∀ χ : G ℚ Ω →* (c.O)ˣ, IsOpen (χ.ker : Set (G ℚ Ω)) →
      IsClosed ((χ.comp (resQ T.F)).ker : Set (G T.F Ω)) := by
    intro χ ho
    have hc : IsClosed (χ.ker : Set (G ℚ Ω)) := Subgroup.isClosed_of_isOpen _ ho
    rw [← MonoidHom.comap_ker]
    exact hc.preimage hcont
  have hcyc : cycZ T.F Ω l s = 1 := by
    have hcl : IsClosed ((cycZ T.F Ω l).ker : Set (G T.F Ω)) :=
      isClosed_singleton.preimage (continuous_cycZ T.F Ω l)
    obtain ⟨a, ha⟩ := mu_pow (cycZ T.F Ω l) hcl hs
    have htor : cycZ T.F Ω l s ^ GroundTheory.Global.Cyclotomic.torsionExponent l = 1 :=
      (GroundTheory.Global.Cyclotomic.mem_torsion_iff l _).1
        ((CommGroup.mem_torsion _).2 (isOfFinOrder_iff_pow_eq_one.2 ⟨l ^ a, pow_pos hlp.pos a, ha⟩))
    have hcop : l.Coprime (GroundTheory.Global.Cyclotomic.torsionExponent l) := by
      simp only [GroundTheory.Global.Cyclotomic.torsionExponent, hD.l_odd, if_false]
      exact Nat.coprime_of_lt_prime (Nat.sub_pos_of_lt hlp.one_lt).ne' (Nat.sub_lt hlp.pos one_pos) hlp
    exact one_of hcop ha htor
  have hchi : chiO ℚ Ω l c.O (resQ T.F s) = 1 := by
    have e : cycZ ℚ Ω l (resQ T.F s) = cycZ T.F Ω l s := rfl
    simp only [chiO, MonoidHom.comp_apply]
    rw [e, hcyc, map_one]
  obtain ⟨m, hm, hkc⟩ := hT.kc
  have hψ : D.ψ (resQ T.F s) = 1 := gen D.ψ m hm (closedOfOpen _ hD.psi_open) (hkc s hcyc)
  obtain ⟨m', hm', hξm⟩ := hD.xi_ord
  have hξ : D.ξ (resQ T.F s) = 1 :=
    gen D.ξ m' hm' (closedOfOpen _ hD.xi_open) (by rw [← MonoidHom.pow_apply, hξm, MonoidHom.one_apply])
  have hom : D.om (resQ T.F s) = 1 := by
    have hb := hD.om_bar (resQ T.F s)
    have hb' : residue c.O ↑(D.om (resQ T.F s)) = residue c.O ↑(1 : (c.O)ˣ) := by
      have e1 : Raw.bar D.om (resQ T.F s) = residue c.O ↑(D.om (resQ T.F s)) := rfl
      have e2 : Raw.bar (chiO ℚ Ω l c.O) (resQ T.F s) = residue c.O ↑(chiO ℚ Ω l c.O (resQ T.F s)) := rfl
      rw [← e1, hb, e2, hchi]
    apply (congrFacts Ω l c).2.2.2.1 _ 1 (l - 1)
    · exact Nat.not_dvd_of_pos_of_lt (Nat.sub_pos_of_lt hlp.one_lt) (Nat.sub_lt hlp.pos one_pos)
    · rw [← MonoidHom.pow_apply, hD.om_pow, MonoidHom.one_apply]
    · exact one_pow _
    · rw [← residue_eq_zero_iff, map_sub, hb', sub_self]
  have hal : D.al (resQ T.F s) = 1 := by
    simp only [Raw.al, MonoidHom.mul_apply, MonoidHom.inv_apply, hchi, hom, hξ, inv_one, mul_one]
  have hPsi : D.Psi (resQ T.F s) = 1 := by
    simp only [Raw.Psi, UpperTheory.V.Chr.Psi, MonoidHom.mul_apply, MonoidHom.pow_apply, MonoidHom.zpow_apply,
      hψ, hchi, one_pow, one_zpow, mul_one]
  have hth : D.th (resQ T.F s) = 1 := by
    simp only [Raw.th, Raw.al, MonoidHom.mul_apply, MonoidHom.inv_apply, hchi, hom, hξ, hPsi, inv_one, mul_one]
  fin_cases i
  · exact hth
  · exact hPsi
  · exact hal
  · rfl
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.RootsOfUnityShapes.PlaceMove
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual Formalism.HC ReciprocityTheory.Gal IsLocalRing Polynomial UpperTheory.V.Base UpperTheory.V.Alg UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws
open scoped Pointwise

private theorem prime_p (l : ℕ) [hl : Fact l.Prime] : Prime ((l : ℕ) : 𝓞 ℚ) := by
  have h : Prime (l : ℤ) := Nat.prime_iff_prime_int.mp hl.out
  have e : Rat.ringOfIntegersEquiv.symm (l : ℤ) = ((l : ℕ) : 𝓞 ℚ) := by simp
  rw [← e]
  exact (MulEquiv.prime_iff (Rat.ringOfIntegersEquiv.symm : ℤ ≃* 𝓞 ℚ)).mpr h

private theorem exists_move {Ω : Type} [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (l : ℕ) [Fact l.Prime]
    (A A' : ValuationSubring Ω) (hA : A.valuation ((l : ℕ) : Ω) < 1) (hA' : A'.valuation ((l : ℕ) : Ω) < 1) :
    ∃ g : G ℚ Ω, ∀ x, g x ∈ A ↔ x ∈ A' := by
  have hpr : Prime (l : ℤ) := Nat.prime_iff_prime_int.mp (Fact.out : l.Prime)
  have key : ∀ B : ValuationSubring Ω, B.valuation ((l : ℕ) : Ω) < 1 →
      ∀ n : ℤ, B.valuation (n : Ω) < 1 ↔ (l : ℤ) ∣ n := by
    intro B hB n
    have hle : ∀ m : ℤ, B.valuation (m : Ω) ≤ 1 := by
      intro m
      have := B.valuation_le_one (m : B)
      simpa using this
    have hB' : B.valuation ((l : ℤ) : Ω) < 1 := by simpa using hB
    constructor
    · intro hn
      by_contra hd
      obtain ⟨a, b, hab⟩ := hpr.irreducible.coprime_iff_not_dvd.mpr hd
      have h1 : B.valuation ((a : Ω) * (l : ℤ)) < 1 := by
        rw [map_mul]
        calc B.valuation (a : Ω) * B.valuation ((l : ℤ) : Ω) ≤ 1 * B.valuation ((l : ℤ) : Ω) :=
              mul_le_mul_left (hle a) _
          _ < 1 := by rwa [one_mul]
      have h2 : B.valuation ((b : Ω) * n) < 1 := by
        rw [map_mul]
        calc B.valuation (b : Ω) * B.valuation (n : Ω) ≤ 1 * B.valuation (n : Ω) :=
              mul_le_mul_left (hle b) _
          _ < 1 := by rwa [one_mul]
      have h3 := Valuation.map_add_lt _ h1 h2
      have e : ((a : Ω) * (l : ℤ) + (b : Ω) * n) = 1 := by
        exact_mod_cast congrArg (fun z : ℤ => (z : Ω)) hab
      rw [e, map_one] at h3
      exact lt_irrefl _ h3
    · rintro ⟨m, rfl⟩
      rw [Int.cast_mul, map_mul]
      calc B.valuation ((l : ℤ) : Ω) * B.valuation (m : Ω) ≤ B.valuation ((l : ℤ) : Ω) * 1 :=
            mul_le_mul_right (hle m) _
        _ < 1 := by rwa [mul_one]
  have hne : ((l : ℕ) : 𝓞 ℚ) ≠ 0 := (prime_p l).ne_zero
  let v : HeightOneSpectrum (𝓞 ℚ) :=
    ⟨Ideal.span {((l : ℕ) : 𝓞 ℚ)}, (Ideal.span_singleton_prime hne).mpr (prime_p l),
      by simpa [Ideal.span_singleton_eq_bot] using hne⟩
  have hpl : ∀ B : ValuationSubring Ω, B.valuation ((l : ℕ) : Ω) < 1 → IsPlaceOver B v := by
    intro B hB x
    have hx : algebraMap ℚ Ω (x : ℚ) = ((Rat.ringOfIntegersEquiv x : ℤ) : Ω) := by
      rw [← map_intCast (algebraMap ℚ Ω), Rat.ringOfIntegersEquiv_apply_coe]
    rw [hx, key B hB]
    change _ ↔ x ∈ Ideal.span {((l : ℕ) : 𝓞 ℚ)}
    rw [Ideal.mem_span_singleton, ← map_dvd_iff Rat.ringOfIntegersEquiv, map_natCast]
  obtain ⟨σ, hσ⟩ := exists_smul_eq_of_isPlaceOver (hpl A' hA') (hpl A hA)
  refine ⟨σ, fun x => ?_⟩
  rw [← hσ, ValuationSubring.mem_pointwise_smul_iff_inv_smul_mem, AlgEquiv.smul_def,
    ← AlgEquiv.mul_apply, inv_mul_cancel, AlgEquiv.one_apply]

theorem UpperTheory.V.Ws.Rq.placeMove :
    ∀ {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] (F : IntermediateField ℚ Ω) [NumberField F] (p : ℕ), p.Prime →
      ∀ A A' : ValuationSubring Ω, A.valuation (p : Ω) < 1 → A'.valuation (p : Ω) < 1 → ∃ g : G ℚ Ω, (∀ x, g x ∈ A ↔ x ∈ A') ∧
        (∀ s ∈ Dec (F := F) A, g⁻¹ * resQ F s * g ∈ Dec (F := ℚ) A') ∧ ∀ s ∈ Ine (F := F) A, g⁻¹ * resQ F s * g ∈ Ine (F := ℚ) A' := by
  intro Ω _ _ _ F _ p hp A A' hA hA'
  haveI : Fact p.Prime := ⟨hp⟩
  obtain ⟨g, hg⟩ := exists_move p A A' hA hA'
  have hL : UpperTheory.V.IsLift (RingEquiv.refl ℚ) (g : Ω ≃+* Ω) := fun x => by simp
  have hc : ∀ t : G ℚ Ω, UpperTheory.V.conjGal hL t = g⁻¹ * t * g := by
    intro t
    ext x
    rw [UpperTheory.V.conjGal_apply]
    rfl
  have hsm : ∀ s : G F Ω, resQ F s • A = s • A := by
    intro s
    ext x
    simp only [ValuationSubring.mem_pointwise_smul_iff_inv_smul_mem]
    rfl
  refine ⟨g, hg, fun s hs => ?_, fun s hs => ?_⟩
  · rw [← hc]
    apply UpperTheory.V.conjGal_mem_Dec hL hg
    rw [mem_Dec] at hs ⊢
    rw [hsm, hs]
  · rw [← hc]
    apply UpperTheory.V.conjGal_mem_Ine hL hg
    rw [mem_Ine] at hs ⊢
    obtain ⟨h1, h2⟩ := hs
    refine ⟨?_, h2⟩
    rw [MulAction.mem_stabilizer_iff] at h1 ⊢
    rw [hsm, h1]
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.RootsOfUnityShapes.ShapeQ
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual Formalism.HC ReciprocityTheory.Gal IsLocalRing Polynomial UpperTheory.V.Base UpperTheory.V.Alg UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws

theorem UpperTheory.V.Ws.Rq.shapeQ :
    ∀ (R : Type) [CommRing R] (X n₀ : M4 R), SuppM nP X → (∀ i, IsUnit (X i i)) → IsLow n₀ → SuppM qQ n₀ →
      (IsUnit ((X * n₀) 0 0) ∧ IsUnit ((X * n₀) 0 0 * (X * n₀) 1 1 - (X * n₀) 0 1 * (X * n₀) 1 0)) ∧
        ∀ n : M4 R, IsLow n → IsUp (adj n * X * n₀) → SuppM qQ n := by
  intro R _ X n₀ hX hu h0 hq
  obtain ⟨-, hd, hl⟩ := h0
  have x01 : X 0 1 = 0 := hX 0 1 (by decide) (by decide)
  have x02 : X 0 2 = 0 := hX 0 2 (by decide) (by decide)
  have x03 : X 0 3 = 0 := hX 0 3 (by decide) (by decide)
  have x13 : X 1 3 = 0 := hX 1 3 (by decide) (by decide)
  have x23 : X 2 3 = 0 := hX 2 3 (by decide) (by decide)
  have x21 : X 2 1 = 0 := hX 2 1 (by decide) (by decide)
  have n21 : n₀ 2 1 = 0 := hq 2 1 (by decide) (by decide)
  have n01 : n₀ 0 1 = 0 := hl 0 1 (by decide)
  have y00 : (X * n₀) 0 0 = X 0 0 := by
    simp [Matrix.mul_apply, Fin.sum_univ_four, x01, x02, x03, hd]
  have y01 : (X * n₀) 0 1 = 0 := by
    simp [Matrix.mul_apply, Fin.sum_univ_four, x01, x02, x03, n01]
  have y11 : (X * n₀) 1 1 = X 1 1 := by
    simp [Matrix.mul_apply, Fin.sum_univ_four, x13, n21, n01, hd]
  have y21 : (X * n₀) 2 1 = 0 := by
    simp [Matrix.mul_apply, Fin.sum_univ_four, x21, x23, n21, n01]
  refine ⟨⟨y00 ▸ hu 0, ?_⟩, fun n hn hU => ?_⟩
  · rw [y00, y11, y01, zero_mul, sub_zero]
    exact (hu 0).mul (hu 1)
  · obtain ⟨hg, nd, nl⟩ := hn
    have h1 : adj n * n = 1 := by
      have := hg
      unfold IsGSp at this
      rwa [one_smul] at this
    have h2 : n * adj n = 1 := mul_eq_one_comm.mp h1
    set U := adj n * X * n₀ with hUdef
    have hY : X * n₀ = n * U := by
      rw [hUdef, mul_assoc (adj n), ← mul_assoc n, h2, one_mul]
    have u21 : U 2 1 = 0 := hU 2 1 (by decide)
    have u31 : U 3 1 = 0 := hU 3 1 (by decide)
    have m01 : n 0 1 = 0 := nl 0 1 (by decide)
    have u01 : U 0 1 = 0 := by
      rw [hY] at y01
      simpa [Matrix.mul_apply (M := n), Fin.sum_univ_four, u21, u31, m01, nd] using y01
    have u11 : U 1 1 = X 1 1 := by
      rw [hY] at y11
      simpa [Matrix.mul_apply (M := n), Fin.sum_univ_four, u21, u31, u01, nd] using y11
    have m21 : n 2 1 = 0 := by
      rw [hY, Matrix.mul_apply, Fin.sum_univ_four, u01, u21, u31, u11, mul_zero, mul_zero, mul_zero,
        zero_add, add_zero, add_zero] at y21
      exact (hu 1).mul_left_eq_zero.mp y21
    intro i j hij hw
    have key : i < j ∨ (i = 2 ∧ j = 1) := by
      revert i j
      decide
    rcases key with h | ⟨rfl, rfl⟩
    · exact nl i j h
    · exact m21
end

