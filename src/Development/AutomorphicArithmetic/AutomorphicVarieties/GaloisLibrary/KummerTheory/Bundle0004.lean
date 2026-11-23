module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.KummerTheory.Mk0IdMapCongr
public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.KummerTheory.Bundle0003
public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.KummerTheory.Bundle0002
public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.KummerTheory.VanishCyc
public import Development.AutomorphicArithmetic.CyclotomicBounds.ClassNumberBounds.TotallyRealRoots.FinrankAdjoinRootsEqRootDeg
public import Development.AutomorphicArithmetic.CyclotomicBounds.ClassNumberBounds.TotallyRealRoots.GalOpen
public import Development.AutomorphicArithmetic.CyclotomicBounds.ClassNumberBounds.TotallyRealRoots.Bundle0004
public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.KummerTheory.Bundle0001

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.KummerTheory.CardHomQZ
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.GaloisCohomology UpperTheory.V UpperTheory.V.LDataCardLeFinrank UpperTheory.V.Base UpperTheory.V.Kum

private theorem cardTors (l : ℕ) [Fact l.Prime] (n : ℕ) (hn : n ≠ 0) :
    Nat.card {x : QZ l // (n : ℤ) • x = 0} = l ^ n.factorization l := by
  have hl : l.Prime := Fact.out
  obtain ⟨ι, hι, hr, -⟩ := zmodToQZ l (n.factorization l)
  have hcop : ¬ l ∣ n / l ^ n.factorization l := Nat.not_dvd_ordCompl hl hn
  have hu : IsUnit ((n / l ^ n.factorization l : ℕ) : ℤ_[l]) := by
    rw [PadicInt.isUnit_iff, PadicInt.norm_natCast_eq_one_iff]
    exact (Nat.Prime.coprime_iff_not_dvd hl).2 hcop
  have key : ∀ x : QZ l, (n : ℤ) • x = 0 ↔ x ∈ Set.range ι := by
    intro x
    rw [hr, natCast_zsmul, ← Nat.cast_smul_eq_nsmul ℤ_[l]]
    conv_lhs => rw [← Nat.ordProj_mul_ordCompl_eq_self n l, mul_comm, Nat.cast_mul, mul_smul]
    rw [hu.smul_eq_zero, Nat.cast_pow]
  rw [Nat.card_congr (Equiv.subtypeEquivRight key)]
  exact (Nat.card_range_of_injective hι).trans (Nat.card_zmod _)
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.KummerTheory.DinfNil
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.GaloisCohomology UpperTheory.V UpperTheory.V.LDataCardLeFinrank UpperTheory.V.Base UpperTheory.V.Kum

private theorem mem_princ_iff_pow_dvd_sub_one (l : ℕ) [Fact l.Prime] (m : ℕ) (u : ℤ_[l]ˣ) :
    u ∈ KStar.TotallyRealRoots.princ l m ↔ (l : ℤ_[l]) ^ m ∣ (u : ℤ_[l]) - 1 := by
  unfold KStar.TotallyRealRoots.princ KStar.TotallyRealRoots.redPow
  rw [MonoidHom.mem_ker, ← Ideal.mem_span_singleton, ← PadicInt.ker_toZModPow, RingHom.mem_ker,
    map_sub, map_one, sub_eq_zero, Units.ext_iff]
  simp

private theorem pow_succ_dvd_pow_prime_sub_one (l : ℕ) [Fact l.Prime] (j : ℕ) (v : ℤ_[l])
    (h : (l : ℤ_[l]) ^ (j + 1) ∣ v - 1) : (l : ℤ_[l]) ^ (j + 2) ∣ v ^ l - 1 := by
  obtain ⟨c, hc⟩ := h
  have hg : v ^ l - 1 = (v - 1) * ∑ i ∈ Finset.range l, v ^ i := by
    rw [mul_comm, geom_sum_mul]
  have hs : v - 1 ∣ (∑ i ∈ Finset.range l, v ^ i) - l := by
    have e : (∑ i ∈ Finset.range l, v ^ i) - l = ∑ i ∈ Finset.range l, (v ^ i - 1) := by
      rw [Finset.sum_sub_distrib]
      simp
    rw [e]
    exact Finset.dvd_sum fun i _ => by simpa using sub_dvd_pow_sub_pow v 1 i
  obtain ⟨d, hd⟩ := hs
  refine ⟨c + (l : ℤ_[l]) ^ j * c ^ 2 * d, ?_⟩
  have hsum : ∑ i ∈ Finset.range l, v ^ i = l + (v - 1) * d := by linear_combination hd
  rw [hg, hsum, hc]
  ring

private theorem exists_prime_pow_smul_eq_zero_qz (l : ℕ) [Fact l.Prime] (v : QZ l) : ∃ m : ℕ, (l : ℤ_[l]) ^ m • v = 0 := by
  obtain ⟨q, rfl⟩ := Submodule.Quotient.mk_surjective (ZlSub l) v
  obtain ⟨m, hm⟩ := pow_unbounded_of_one_lt ‖q‖
    (by exact_mod_cast (Fact.out : l.Prime).one_lt : (1 : ℝ) < l)
  refine ⟨m, ?_⟩
  show ((l : ℤ_[l]) ^ m • (Submodule.Quotient.mk q : ℚ_[l] ⧸ ZlSub l)) = 0
  rw [← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero]
  unfold ZlSub
  refine ⟨(⟨(l : ℚ_[l]) ^ m * q, ?_⟩ : ℤ_[l]), ?_⟩
  · rw [PadicInt.mem_subring_iff, norm_mul, norm_pow, Padic.norm_p, inv_pow, inv_mul_le_iff₀ (pow_pos (by exact_mod_cast (Fact.out : l.Prime).pos) m)]
    simpa using hm.le
  · show (l : ℚ_[l]) ^ m * q = _
    simp [Algebra.smul_def]

private theorem exists_princ_subset_of_mem_nhds_one (l : ℕ) [Fact l.Prime] (V : Set ℤ_[l]ˣ) (hV : V ∈ nhds (1 : ℤ_[l]ˣ)) :
    ∃ n, ∀ u ∈ KStar.TotallyRealRoots.princ l n, u ∈ V := by
  rw [(Units.isOpenEmbedding_val (R := ℤ_[l])).isEmbedding.isInducing.nhds_eq_comap,
    Filter.mem_comap] at hV
  obtain ⟨t, ht, htV⟩ := hV
  rw [Units.val_one, Metric.mem_nhds_iff] at ht
  obtain ⟨ε, εpos, hball⟩ := ht
  have hl1 : (l : ℝ)⁻¹ < 1 := inv_lt_one_of_one_lt₀ (by exact_mod_cast (Fact.out : l.Prime).one_lt)
  obtain ⟨n, hn⟩ := exists_pow_lt_of_lt_one εpos hl1
  refine ⟨n, fun u hu => htV (hball ?_)⟩
  rw [mem_princ_iff_pow_dvd_sub_one] at hu
  obtain ⟨c, hc⟩ := hu
  rw [Metric.mem_ball, dist_eq_norm, hc, norm_mul, norm_pow, PadicInt.norm_p]
  calc ((l : ℝ)⁻¹) ^ n * ‖c‖ ≤ ((l : ℝ)⁻¹) ^ n * 1 :=
        mul_le_mul_of_nonneg_left (PadicInt.norm_le_one c) (by positivity)
    _ < ε := by rwa [mul_one]

theorem UpperTheory.V.Kum.dinfNil :
    ∀ (F Ω : Type) [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] (l : ℕ) [Fact l.Prime] (N : ℕ) (U : Subgroup (G F Ω)) [U.Normal], IsClosed (U : Set (G F Ω)) → ∀ φ ∈ Dinf l N U, (∃ n, ∀ g ∈ levU l U n, funRep ℤ_[l] (QZ l) (cycU l U) g φ = φ) ∧
    ∀ γ ∈ levU l U 1, ∃ k : ℕ, (l : ℤ_[l]) ^ k • φ = 0 ∧ ((funRep ℤ_[l] (QZ l) (cycU l U) γ - 1) ^ k) φ = 0 := by
  intro F Ω _ _ _ _ _ l _ N U _ hU φ hφ
  classical
  have memC : ∀ x : G F Ω, x ∈ cycU l U ↔ x ∈ U ∧ cycZ F Ω l x = 1 := by
    intro x
    unfold cycU
    rw [Subgroup.mem_inf, MonoidHom.mem_ker]
  have memLev : ∀ (m : ℕ) (x : G F Ω),
      x ∈ levU l U m ↔ x ∈ U ∧ cycZ F Ω l x ∈ KStar.TotallyRealRoots.princ l m := by
    intro m x
    unfold levU
    rw [Subgroup.mem_inf, Subgroup.mem_comap]
  have hφ' := hφ
  unfold Dinf XDual at hφ'
  have hlc : IsLocallyConstant φ := hφ'.1
  have hadd : ∀ a b, φ (a * b) = φ a + φ b := hφ'.2.1
  have h1 : φ 1 = 0 := by simpa using hadd 1 1
  have hinv : ∀ a, φ a⁻¹ = - φ a := fun a => by
    have h2 := hadd a⁻¹ a
    rw [inv_mul_cancel, h1] at h2
    exact eq_neg_of_add_eq_zero_left h2.symm
  have hCc : IsClosed (cycU l U : Set (G F Ω)) := by
    have e : (cycU l U : Set (G F Ω)) = (U : Set (G F Ω)) ∩ (cycZ F Ω l) ⁻¹' {1} := by
      ext x
      simp only [SetLike.mem_coe, memC, Set.mem_inter_iff, Set.mem_preimage, Set.mem_singleton_iff]
    rw [e]
    exact hU.inter (isClosed_singleton.preimage (continuous_cycZ F Ω l))
  have hCcpt : CompactSpace (cycU l U) := isCompact_iff_compactSpace.mp hCc.isCompact
  obtain ⟨O, hO, hOeq⟩ := isOpen_induced_iff.mp (hlc.isOpen_fiber 0)
  have h1O : (1 : G F Ω) ∈ O := by
    have h2 : (1 : cycU l U) ∈ Subtype.val ⁻¹' O := by
      rw [hOeq]
      exact h1
    exact h2
  obtain ⟨W, hW⟩ := ProfiniteGrp.exist_openNormalSubgroup_sub_open_nhds_of_one hO h1O
  have hWker : ∀ (d : G F Ω) (hd : d ∈ cycU l U), d ∈ W.toSubgroup → φ ⟨d, hd⟩ = 0 := by
    intro d hd hdW
    have h2 : (⟨d, hd⟩ : cycU l U) ∈ Subtype.val ⁻¹' O := hW hdW
    rw [hOeq] at h2
    exact h2
  have conj_val : ∀ (γ : G F Ω) (x : cycU l U),
      ((conjHom (cycU l U) γ x : cycU l U) : G F Ω) = γ⁻¹ * x * γ := fun _ _ => rfl
  have stabC : ∀ γ ∈ cycU l U, ∀ x, φ (conjHom (cycU l U) γ x) = φ x := by
    intro γ hγ x
    have e : conjHom (cycU l U) γ x = (⟨γ, hγ⟩ : cycU l U)⁻¹ * x * ⟨γ, hγ⟩ :=
      Subtype.ext (by simp only [conj_val, Subgroup.coe_mul, Subgroup.coe_inv, Subgroup.coe_mk])
    rw [e, hadd, hadd, hinv]
    abel
  have stabW : ∀ γ ∈ W.toSubgroup, ∀ x, φ (conjHom (cycU l U) γ x) = φ x := by
    intro γ hγ x
    have hdC : γ⁻¹ * x * γ * (x : G F Ω)⁻¹ ∈ cycU l U :=
      mul_mem (conjHom (cycU l U) γ x).2 (inv_mem x.2)
    have hdW : γ⁻¹ * x * γ * (x : G F Ω)⁻¹ ∈ W.toSubgroup := by
      have h3 : (x : G F Ω) * γ * (x : G F Ω)⁻¹ ∈ W.toSubgroup := W.isNormal'.conj_mem γ hγ x
      have h2 := mul_mem (inv_mem hγ) h3
      simpa [mul_assoc] using h2
    have e : conjHom (cycU l U) γ x = ⟨_, hdC⟩ * x :=
      Subtype.ext (by simp only [conj_val, Subgroup.coe_mul, Subgroup.coe_mk]; group)
    rw [e, hadd, hWker _ hdC hdW, zero_add]
  have stabMul : ∀ a b : G F Ω, (∀ x, φ (conjHom (cycU l U) a x) = φ x) →
      (∀ x, φ (conjHom (cycU l U) b x) = φ x) → ∀ x, φ (conjHom (cycU l U) (a * b) x) = φ x := by
    intro a b ha hb x
    have e : conjHom (cycU l U) (a * b) x = conjHom (cycU l U) b (conjHom (cycU l U) a x) :=
      Subtype.ext (by simp only [conj_val]; group)
    rw [e, hb, ha]
  let S : Set (G F Ω) :=
    ⋃ c : cycU l U, (fun γ => γ * (c : G F Ω)⁻¹) ⁻¹' (W.toSubgroup : Set (G F Ω))
  have hSo : IsOpen S := isOpen_iUnion fun c =>
    W.toOpenSubgroup.isOpen'.preimage (continuous_id.mul continuous_const)
  have hSstab : ∀ γ ∈ S, ∀ x, φ (conjHom (cycU l U) γ x) = φ x := by
    intro γ hγ
    obtain ⟨c, hc⟩ := Set.mem_iUnion.mp hγ
    have e : γ = (γ * (c : G F Ω)⁻¹) * c := by group
    rw [e]
    exact stabMul _ _ (stabW _ hc) (stabC _ c.2)
  let T : Set (G F Ω) := (U : Set (G F Ω)) ∩ Sᶜ
  have hTc : IsCompact T := (hU.inter hSo.isClosed_compl).isCompact
  have hχT : IsClosed (cycZ F Ω l '' T) := (hTc.image (continuous_cycZ F Ω l)).isClosed
  have h1T : (1 : ℤ_[l]ˣ) ∉ cycZ F Ω l '' T := by
    rintro ⟨t, ⟨htU, htS⟩, ht1⟩
    apply htS
    refine Set.mem_iUnion.mpr ⟨⟨t, (memC t).mpr ⟨htU, ht1⟩⟩, ?_⟩
    show t * t⁻¹ ∈ W.toSubgroup
    rw [mul_inv_cancel]
    exact one_mem _
  obtain ⟨n, hn⟩ := exists_princ_subset_of_mem_nhds_one l _ (hχT.isOpen_compl.mem_nhds h1T)
  have hstab : ∀ g ∈ levU l U n, ∀ x, φ (conjHom (cycU l U) g x) = φ x := by
    intro g hg
    rw [memLev] at hg
    apply hSstab
    by_contra hgS
    exact hn _ hg.2 ⟨g, ⟨hg.1, hgS⟩, rfl⟩
  refine ⟨⟨n, fun g hg => ?_⟩, ?_⟩
  · funext x
    exact hstab g hg x
  intro γ hγ
  have hfin := hlc.range_finite
  choose mf hmf using fun v : QZ l => exists_prime_pow_smul_eq_zero_qz l v
  let k0 := hfin.toFinset.sup mf
  have hk0 : (l : ℤ_[l]) ^ k0 • φ = 0 := by
    funext x
    have hle : mf (φ x) ≤ k0 := Finset.le_sup (hfin.mem_toFinset.mpr ⟨x, rfl⟩)
    rw [Pi.smul_apply, Pi.zero_apply, ← Nat.sub_add_cancel hle, pow_add, mul_smul, hmf, smul_zero]
  set q := l ^ n with hqdef
  have hqpos : 0 < q := pow_pos (Fact.out : l.Prime).pos n
  have hγq : γ ^ q ∈ levU l U n := by
    rw [memLev] at hγ ⊢
    refine ⟨pow_mem hγ.1 q, ?_⟩
    rw [map_pow, mem_princ_iff_pow_dvd_sub_one]
    have key : ∀ j : ℕ, (l : ℤ_[l]) ^ (j + 1) ∣ ((cycZ F Ω l γ ^ (l ^ j) : ℤ_[l]ˣ) : ℤ_[l]) - 1 := by
      intro j
      induction j with
      | zero => simpa [mem_princ_iff_pow_dvd_sub_one] using hγ.2
      | succ j ih =>
        rw [show l ^ (j + 1) = l ^ j * l from pow_succ l j, pow_mul, Units.val_pow_eq_pow_val]
        exact pow_succ_dvd_pow_prime_sub_one l j _ ih
    exact dvd_trans (pow_dvd_pow _ (Nat.le_succ n)) (key n)
  let ρ := funRep ℤ_[l] (QZ l) (cycU l U)
  let Tm : Module.End ℤ_[l] (cycU l U → QZ l) := ρ γ - 1
  let J : Ideal (Polynomial ℤ) :=
    { carrier := {p | Polynomial.aeval Tm p φ = 0}
      add_mem' := fun {a b} ha hb => by
        simp only [Set.mem_setOf_eq, map_add (f := _), LinearMap.add_apply] at *
        rw [ha, hb, add_zero]
      zero_mem' := by simp
      smul_mem' := fun c p hp => by
        simp only [Set.mem_setOf_eq, smul_eq_mul, map_mul, Module.End.mul_apply] at *
        rw [hp, map_zero] }
  have hB : (Polynomial.X + 1) ^ q - 1 ∈ J := by
    show (Polynomial.aeval Tm ((Polynomial.X + 1) ^ q - 1)) φ = 0
    simp only [map_sub, map_pow, map_add (f := _), Polynomial.aeval_X, map_one]
    rw [show Tm + 1 = ρ γ from sub_add_cancel _ _, ← map_pow, LinearMap.sub_apply,
      Module.End.one_apply, sub_eq_zero]
    funext x
    exact hstab _ hγq x
  have hL : Polynomial.C ((l : ℤ) ^ k0) ∈ J := by
    show (Polynomial.aeval Tm (Polynomial.C ((l : ℤ) ^ k0))) φ = 0
    rw [Polynomial.aeval_C, Algebra.algebraMap_eq_smul_one, LinearMap.smul_apply,
      Module.End.one_apply, ← Int.cast_smul_eq_zsmul ℤ_[l]]
    push_cast
    exact hk0
  have hP : Polynomial.C (l : ℤ) ∣ (Polynomial.X + 1) ^ q - Polynomial.X ^ q - 1 := by
    rw [Polynomial.C_dvd_iff_dvd_coeff]
    intro i
    have hmap : Polynomial.map (Int.castRingHom (ZMod l))
        ((Polynomial.X + 1) ^ q - Polynomial.X ^ q - 1) = 0 := by
      simp only [Polynomial.map_sub, Polynomial.map_pow, Polynomial.map_add (f := _), Polynomial.map_X,
        Polynomial.map_one]
      rw [hqdef, add_pow_char_pow, one_pow]
      ring
    have h2 := congrArg (fun P => _root_.AddMonoidAlgebra.coeff (M := ℕ) P i) hmap
    simp only [Polynomial.coeff_map, Polynomial.coeff_zero, eq_intCast] at h2
    exact (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp h2
  obtain ⟨Qp, hQp⟩ := hP
  have hXq : (Polynomial.X : Polynomial ℤ) ^ q =
      ((Polynomial.X + 1) ^ q - 1) - Polynomial.C (l : ℤ) * Qp := by
    linear_combination (-1 : Polynomial ℤ) * hQp
  have hmem : (Polynomial.X : Polynomial ℤ) ^ (q * k0) ∈ J := by
    rw [← Ideal.Quotient.eq_zero_iff_mem, pow_mul, map_pow, hXq, map_sub,
      Ideal.Quotient.eq_zero_iff_mem.mpr hB, zero_sub, map_mul]
    calc (-(Ideal.Quotient.mk J (Polynomial.C (l : ℤ)) * Ideal.Quotient.mk J Qp)) ^ k0
        = (-(Ideal.Quotient.mk J Qp)) ^ k0 * Ideal.Quotient.mk J (Polynomial.C ((l : ℤ) ^ k0)) := by
          rw [Polynomial.C_pow, map_pow]
          ring
      _ = 0 := by rw [Ideal.Quotient.eq_zero_iff_mem.mpr hL, mul_zero]
  refine ⟨q * k0, ?_, ?_⟩
  · rw [show q * k0 = (q * k0 - k0) + k0 from
      (Nat.sub_add_cancel (Nat.le_mul_of_pos_left k0 hqpos)).symm, pow_add, mul_smul, hk0, smul_zero]
  · have h2 := hmem
    change (Polynomial.aeval Tm (Polynomial.X ^ (q * k0))) φ = 0 at h2
    rw [map_pow, Polynomial.aeval_X] at h2
    exact h2
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.KummerTheory.ExtCocycle
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.GaloisCohomology UpperTheory.V UpperTheory.V.LDataCardLeFinrank UpperTheory.V.Base UpperTheory.V.Kum

private theorem ext_of_prod {Γ R M : Type} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ] [CompactSpace Γ]
    [T2Space Γ] [CommRing R] [AddCommGroup M] [Module R M] [TopologicalSpace M] [DiscreteTopology M]
    (ρ : Representation R Γ M) (C U : Subgroup Γ) [hN : U.Normal] (hC : IsClosed (C : Set Γ))
    (hU : IsClosed (U : Set Γ)) (hCU : ∀ g : Γ, ∃ p : C × U, p.1.1 * p.2.1 = g) (φ : U → M) (hρ : ContAction ρ)
    (htr : ∀ u ∈ U, ∀ m, ρ u m = m) (hφ : Continuous φ) (hadd : ∀ a b, φ (a * b) = φ a + φ b)
    (heq : ∀ (g : Γ) (u u' : U), u'.1 * g = g * u.1 → φ u' = ρ g (φ u)) (hv : ∀ x : U, x.1 ∈ C → φ x = 0) :
    ∃ z ∈ Z1 ρ, ∀ u : U, z u.1 = φ u := by
  classical
  obtain ⟨f, hf⟩ : ∃ f : C × U → Γ, ∀ p, f p = p.1.1 * p.2.1 := ⟨_, fun _ => rfl⟩
  have hwd : ∀ p q : C × U, f p = f q → ρ p.1.1 (φ p.2) = ρ q.1.1 (φ q.2) := by
    rintro ⟨⟨c, hc⟩, ⟨u, hu⟩⟩ ⟨⟨c', hc'⟩, ⟨u', hu'⟩⟩ h
    rw [hf, hf] at h
    change c * u = c' * u' at h
    change ρ c (φ ⟨u, hu⟩) = ρ c' (φ ⟨u', hu'⟩)
    have hw1 : c'⁻¹ * c = u' * u⁻¹ := by
      rw [inv_mul_eq_iff_eq_mul, ← mul_assoc, ← h, mul_inv_cancel_right]
    have hwC : c'⁻¹ * c ∈ C := C.mul_mem (C.inv_mem hc') hc
    have hwU : c'⁻¹ * c ∈ U := hw1 ▸ U.mul_mem hu' (U.inv_mem hu)
    have hφw : φ ⟨_, hwU⟩ = 0 := hv _ hwC
    have hu'eq : (⟨u', hu'⟩ : U) = ⟨_, hwU⟩ * ⟨u, hu⟩ := by
      ext
      simp [hw1]
    have h2 : φ ⟨u', hu'⟩ = φ ⟨u, hu⟩ := by rw [hu'eq, hadd, hφw, zero_add]
    rw [h2, show ρ c = ρ c' * ρ (c'⁻¹ * c) by rw [← map_mul, mul_inv_cancel_left],
      Module.End.mul_apply, htr _ hwU]
  choose s hs using hCU
  obtain ⟨z, hz⟩ : ∃ z : Γ → M, ∀ g, z g = ρ (s g).1.1 (φ (s g).2) := ⟨_, fun _ => rfl⟩
  have hzf : ∀ p : C × U, z (f p) = ρ p.1.1 (φ p.2) := by
    intro p
    rw [hz]
    exact hwd _ _ (by rw [hf, hs])
  haveI : CompactSpace C := isCompact_iff_compactSpace.mp hC.isCompact
  haveI : CompactSpace U := isCompact_iff_compactSpace.mp hU.isCompact
  have hfc : Continuous f := by
    have : f = fun p : C × U => p.1.1 * p.2.1 := funext hf
    rw [this]
    exact (continuous_subtype_val.comp continuous_fst).mul (continuous_subtype_val.comp continuous_snd)
  have hfs : Function.Surjective f := fun g => ⟨s g, by rw [hf, hs]⟩
  have hq : Topology.IsQuotientMap f := hfc.isClosedMap.isQuotientMap hfc hfs
  have hzc : Continuous z := by
    rw [hq.continuous_iff]
    have : z ∘ f = fun p : C × U => ρ p.1.1 (φ p.2) := funext hzf
    rw [this]
    exact hρ.comp ((continuous_subtype_val.comp continuous_fst).prodMk (hφ.comp continuous_snd))
  have hzU : ∀ u : U, z u.1 = φ u := by
    intro u
    have h1 := hzf (⟨1, C.one_mem⟩, u)
    rw [hf] at h1
    simpa using h1
  have hcoc : ∀ g h : Γ, z (g * h) = z g + ρ g (z h) := by
    intro g h
    obtain ⟨⟨⟨c, hc⟩, ⟨u, hu⟩⟩, rfl⟩ := hfs g
    obtain ⟨⟨⟨d, hd⟩, ⟨v, hv'⟩⟩, rfl⟩ := hfs h
    have hu0 : d⁻¹ * u * d ∈ U := by simpa using hN.conj_mem u hu d⁻¹
    have hprod : f (⟨c, hc⟩, ⟨u, hu⟩) * f (⟨d, hd⟩, ⟨v, hv'⟩)
        = f (⟨c * d, C.mul_mem hc hd⟩, ⟨d⁻¹ * u * d, hu0⟩ * ⟨v, hv'⟩) := by
      simp only [hf, Subgroup.coe_mul]
      group
    rw [hprod, hzf, hzf, hzf, hf]
    change ρ (c * d) (φ (⟨d⁻¹ * u * d, hu0⟩ * ⟨v, hv'⟩)) = ρ c (φ ⟨u, hu⟩) + ρ (c * u) (ρ d (φ ⟨v, hv'⟩))
    have hconj : φ ⟨u, hu⟩ = ρ d (φ ⟨d⁻¹ * u * d, hu0⟩) :=
      heq d ⟨d⁻¹ * u * d, hu0⟩ ⟨u, hu⟩ (by show u * d = d * (d⁻¹ * u * d); group)
    rw [hadd, map_add (f := _), hconj]
    simp only [map_mul, Module.End.mul_apply]
    rw [htr u hu]
  exact ⟨z, ⟨hzc, hcoc⟩, hzU⟩

theorem UpperTheory.V.Kum.extCocycle :
    ∀ (F Ω : Type) [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] (l : ℕ) [Fact l.Prime] (R M : Type) [CommRing R] [AddCommGroup M] [Module R M] [TopologicalSpace M] [DiscreteTopology M] (ρ : Representation R (G F Ω) M) (φ : Uinf F Ω l → M), Procyc F Ω l → ContAction ρ → (∀ u ∈ Uinf F Ω l, ∀ m, ρ u m = m) → (∀ m : M, ∃ k : ℕ, l ^ k • m = 0) →
    IsLocallyConstant φ → (∀ a b, φ (a * b) = φ a + φ b) → (∀ g : G F Ω, φ ∈ conjCond (Uinf F Ω l) g.toRingEquiv (ρ g)) → ∃ z ∈ Z1 ρ, ∀ u : Uinf F Ω l, z u.1 = φ u := by
  intro F Ω _ _ _ _ _ l _ R M _ _ _ _ _ ρ φ hP hρ htr htors hloc hadd hconj
  classical
  have hVc : IsClosed ((cycZ F Ω l).range : Set ℤ_[l]ˣ) := by
    rw [MonoidHom.coe_range]
    exact (isCompact_range (continuous_cycZ F Ω l)).isClosed
  have hcond : l ≠ 2 ∨ (cycZ F Ω l).range ≤ KStar.TotallyRealRoots.princ l 2 := by
    rcases hP with h | h
    · exact Or.inl h
    · right
      rintro _ ⟨g, rfl⟩
      exact MonoidHom.mem_ker.mpr (h g)
  obtain ⟨γ0, hγ0, hgen⟩ := existsGen l _ hVc hcond
  obtain ⟨γ, rfl⟩ := hγ0
  have hnf : ¬ IsOfFinOrder (cycZ F Ω l γ) := by
    intro hfin
    obtain ⟨n, hn, hpow⟩ := isOfFinOrder_iff_pow_eq_one.mp hfin
    have hS : ∀ u ∈ (cycZ F Ω l).range, u ^ n = 1 := by
      intro u hu
      have hsub : closure ((Subgroup.zpowers (cycZ F Ω l γ) : Subgroup ℤ_[l]ˣ) : Set ℤ_[l]ˣ)
          ⊆ {x | x ^ n = 1} := by
        apply closure_minimal
        · intro x hx
          obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hx
          show ((cycZ F Ω l γ) ^ k) ^ n = 1
          rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hpow, one_zpow]
        · exact isClosed_eq (continuous_pow n) continuous_const
      have h1 := hgen hu
      rw [← SetLike.mem_coe, Subgroup.topologicalClosure_coe] at h1
      exact hsub h1
    have htop : KStar.TotallyRealRoots.nu l (KStar.TotallyRealRoots.galImage l F) n = ⊤ := by
      rw [ENat.eq_top_iff_forall_ge]
      intro k
      rw [KStar.TotallyRealRoots.le_nu_iff_pow_mem_princ]
      intro u hu
      rw [KStar.TotallyRealRoots.mem_galImage_iff_of_equiv (RingEquiv.refl F) Ω] at hu
      obtain ⟨g, rfl⟩ := hu
      have h2 := hS (cyclotomicCharacter Ω l g.toRingEquiv) (MonoidHom.mem_range.mpr ⟨g, rfl⟩)
      rw [h2]
      exact Subgroup.one_mem _
    exact KStar.TotallyRealRoots.nu_ne_top KStar.TotallyRealRoots.isOpen_galImage hn.ne' htop
  haveI hN : (Uinf F Ω l).Normal := by
    show (⊤ ⊓ (cycZ F Ω l).ker).Normal
    infer_instance
  have hUc : IsClosed ((Uinf F Ω l : Subgroup (G F Ω)) : Set (G F Ω)) := by
    show IsClosed ((⊤ ⊓ (cycZ F Ω l).ker : Subgroup (G F Ω)) : Set (G F Ω))
    rw [Subgroup.coe_inf, Subgroup.coe_top, Set.univ_inter, MonoidHom.coe_ker]
    exact isClosed_singleton.preimage (continuous_cycZ F Ω l)
  have hCc := Subgroup.isClosed_topologicalClosure (Subgroup.zpowers γ)
  have hmemU : ∀ x : G F Ω, cycZ F Ω l x = 1 → x ∈ Uinf F Ω l := by
    intro x hx
    show x ∈ (⊤ ⊓ (cycZ F Ω l).ker : Subgroup (G F Ω))
    exact Subgroup.mem_inf.mpr ⟨Subgroup.mem_top x, MonoidHom.mem_ker.mpr hx⟩
  have hCU : ∀ g : G F Ω, ∃ p : (Subgroup.zpowers γ).topologicalClosure × Uinf F Ω l,
      p.1.1 * p.2.1 = g := by
    intro g
    have himg : closure ((Subgroup.zpowers (cycZ F Ω l γ) : Subgroup ℤ_[l]ˣ) : Set ℤ_[l]ˣ)
        ⊆ (cycZ F Ω l) '' ((Subgroup.zpowers γ).topologicalClosure : Set (G F Ω)) := by
      apply closure_minimal
      · intro x hx
        obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hx
        exact ⟨γ ^ k, Subgroup.le_topologicalClosure _ (Subgroup.zpow_mem_zpowers γ k), map_zpow _ _ _⟩
      · exact (hCc.isCompact.image (continuous_cycZ F Ω l)).isClosed
    have hg := hgen (MonoidHom.mem_range.mpr ⟨g, rfl⟩)
    rw [← SetLike.mem_coe, Subgroup.topologicalClosure_coe] at hg
    obtain ⟨c, hc, hcg⟩ := himg hg
    refine ⟨(⟨c, hc⟩, ⟨c⁻¹ * g, hmemU _ ?_⟩), mul_inv_cancel_left c g⟩
    rw [map_mul, map_inv, hcg, inv_mul_cancel]
  have heq : ∀ (g : G F Ω) (u u' : Uinf F Ω l), u'.1 * g = g * u.1 → φ u' = ρ g (φ u) := by
    intro g u u' h
    apply hconj g u u'
    intro x
    have h3 := congrArg (fun e : G F Ω => e x) h
    simpa [AlgEquiv.mul_apply] using h3
  have hv : ∀ x : Uinf F Ω l, x.1 ∈ (Subgroup.zpowers γ).topologicalClosure → φ x = 0 :=
    fun x hx => vanishCyc F Ω l M φ γ hloc hadd htors hnf x hx
  exact ext_of_prod ρ _ _ hCc hUc hCU φ hρ htr hloc.continuous hadd heq hv
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.KummerTheory.RadClMul
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.GaloisCohomology UpperTheory.V UpperTheory.V.LDataCardLeFinrank UpperTheory.V.Base UpperTheory.V.Kum

private theorem finSupp {K : Type} [Field K] [NumberField K] {G : Type} [CommGroup G]
    (g : HeightOneSpectrum (𝓞 K) → G) (n : ℤ) (a : Kˣ) :
    Function.HasFiniteMulSupport fun v => g v ^ (ordv v a / n) := by
  refine ((clProd K).2.2.1 a).subset fun v hv => ?_
  intro h
  apply hv
  simp [h]

private theorem mk_radCl {K : Type} [Field K] [NumberField K] (S : Set (HeightOneSpectrum (𝓞 K))) (n : ℕ) (a : Kˣ) :
    (QuotientGroup.mk (radCl n a) : ClS S) =
      ∏ᶠ v : HeightOneSpectrum (𝓞 K), (QuotientGroup.mk (primeCl v) : ClS S) ^ (ordv v a / n) := by
  have h := (QuotientGroup.mk' (clSub S)).map_finprod (finSupp primeCl (n : ℤ) a)
  simpa [radCl] using h

private theorem mk_primeCl {K : Type} [Field K] [NumberField K] {S : Set (HeightOneSpectrum (𝓞 K))}
    {v : HeightOneSpectrum (𝓞 K)} (hv : v ∈ S) : (QuotientGroup.mk (primeCl v) : ClS S) = 1 :=
  (QuotientGroup.eq_one_iff _).2 (Subgroup.subset_closure ⟨v, hv, rfl⟩)

private theorem ordv_pow' {K : Type} [Field K] [NumberField K] (v : HeightOneSpectrum (𝓞 K)) (b : Kˣ) (n : ℕ) :
    ordv v (b ^ n) = n * ordv v b := by
  induction n with
  | zero => simp [ordv_one]
  | succ m ih => rw [pow_succ, ordv_mul, ih]; push_cast; ring

theorem UpperTheory.V.Kum.radClMul :
    ∀ (K : Type) [Field K] [NumberField K] (S : Set (HeightOneSpectrum (𝓞 K))) (n : ℕ), n ≠ 0 → (∀ a ∈ SelK S n, ∀ b ∈ SelK S n, (QuotientGroup.mk (radCl n (a * b)) : ClS S) = QuotientGroup.mk (radCl n a) * QuotientGroup.mk (radCl n b)) ∧
    (∀ a ∈ SelK S n, (QuotientGroup.mk (radCl n a) : ClS S) ^ n = 1) ∧ (∀ a b : Kˣ, radCl n (a * b ^ n) = radCl n a) := by
  intro K _ _ S n hn
  have hn' : (n : ℤ) ≠ 0 := by exact_mod_cast hn
  have h1 : ∀ x : Kˣ, radCl 1 x = 1 := (clProd K).2.2.2
  refine ⟨?_, ?_, ?_⟩
  · intro a ha b hb
    rw [mk_radCl S n, mk_radCl S n, mk_radCl S n,
      ← finprod_mul_distrib (finSupp (fun v => (QuotientGroup.mk (primeCl v) : ClS S)) (n : ℤ) a)
        (finSupp (fun v => (QuotientGroup.mk (primeCl v) : ClS S)) (n : ℤ) b)]
    apply finprod_congr
    intro v
    by_cases hv : v ∈ S
    · simp [mk_primeCl hv]
    · rw [ordv_mul, Int.add_ediv_of_dvd_right (hb v hv), zpow_add]
  · intro a ha
    have e := mk_radCl S 1 a
    rw [h1 a] at e
    simp only [Nat.cast_one, Int.ediv_one, QuotientGroup.mk_one] at e
    have key : ∀ v : HeightOneSpectrum (𝓞 K),
        ((QuotientGroup.mk (primeCl v) : ClS S) ^ (ordv v a / (n : ℤ))) ^ n =
          (QuotientGroup.mk (primeCl v) : ClS S) ^ ordv v a := by
      intro v
      by_cases hv : v ∈ S
      · simp [mk_primeCl hv]
      · rw [← zpow_natCast, ← zpow_mul, Int.ediv_mul_cancel (ha v hv)]
    rw [mk_radCl S n, finprod_pow (finSupp (fun v => (QuotientGroup.mk (primeCl v) : ClS S)) (n : ℤ) a),
      finprod_congr key]
    exact e.symm
  · intro a b
    have e := h1 b
    simp only [radCl, Nat.cast_one, Int.ediv_one] at e
    have hb1 : Function.HasFiniteMulSupport fun v : HeightOneSpectrum (𝓞 K) => primeCl v ^ ordv v b := by
      have h := finSupp (primeCl (K := K)) 1 b
      simpa only [Int.ediv_one] using h
    simp only [radCl]
    rw [finprod_congr (fun v => show primeCl v ^ (ordv v (a * b ^ n) / (n : ℤ)) =
        primeCl v ^ (ordv v a / (n : ℤ)) * primeCl v ^ ordv v b by
          rw [ordv_mul, ordv_pow', Int.add_mul_ediv_left _ _ hn', zpow_add]),
      finprod_mul_distrib (finSupp primeCl (n : ℤ) a) hb1, e, mul_one]
end

