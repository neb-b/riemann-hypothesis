module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.OddResidueBounds.ZeroMemUnrHom
public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.KummerTheory.Bundle0002
public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.SelmerTransport.Bundle0002
public import Development.AutomorphicArithmetic.CyclotomicBounds.ClassNumberBounds.InertiaRamification.Bundle0005
public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.BernoulliNumbers.Bundle0007
public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.BernoulliNumbers.Bundle0002
public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.BernoulliNumbers.Bundle0001
public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.BernoulliNumbers.Bundle0005
public import Mathlib
public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.BernoulliNumbers.Bundle0003
public import Development.AutomorphicArithmetic.AutomorphicVarieties.StickelbergerElements.Bundle0003
public import Development.AutomorphicArithmetic.AutomorphicVarieties.StickelbergerElements.Bundle0002

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.OddResidueBounds.FixLev
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.GaloisCohomology UpperTheory.V UpperTheory.V.LDataCardLeFinrank UpperTheory.V.Base UpperTheory.V.Kum UpperTheory.V.Bern UpperTheory.V.B4 UpperTheory.V.B5 UpperTheory.V.Odd

private theorem pow_cyc_char_iff_toZModPow_eq {Ω : Type} [Field Ω] (l : ℕ) [Fact l.Prime] [∀ i, HasEnoughRootsOfUnity Ω (l ^ i)]
    (g : Ω ≃+* Ω) (k : ℕ) (c : ZMod (l ^ k)) :
    (∀ t : Ω, t ^ (l ^ k) = 1 → g t = t ^ c.val) ↔
      PadicInt.toZModPow k ((cyclotomicCharacter Ω l g : ℤ_[l]ˣ) : ℤ_[l]) = c := by
  haveI : NeZero (l ^ k) := ⟨pow_ne_zero _ (Fact.out : l.Prime).ne_zero⟩
  constructor
  · intro h
    obtain ⟨ζ, hζ⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot Ω (l ^ k)
    have h1 := cyclotomicCharacter.spec l g ζ hζ.pow_eq_one
    rw [h ζ hζ.pow_eq_one] at h1
    have h2 := hζ.pow_inj (ZMod.val_lt _) (ZMod.val_lt _) h1
    exact (ZMod.val_injective _ h2).symm
  · rintro h t ht
    rw [cyclotomicCharacter.spec l g t ht, h]

private theorem pow_mod_eq_pow_of_pow_eq_one {Ω : Type} [Field Ω] (t : Ω) (n a : ℕ) (ht : t ^ n = 1) :
    t ^ (a % n) = t ^ a := by
  conv_rhs => rw [← Nat.mod_add_div a n, pow_add, pow_mul, ht, one_pow, mul_one]

theorem UpperTheory.V.Odd.fixLev :
    ∀ (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (l : ℕ) [Fact l.Prime] (N m : ℕ) [NeZero N], fixMu E Ω (l ^ m) = Un E Ω l m ∧ Uinf E Ω l ⊓ fixMu E Ω N ≤ fixMu E Ω (N * l ^ m) ∧ ∀ (M : ℕ) [NeZero M] (b : (ZMod M)ˣ) (σ : Ω ≃+* Ω), l ^ m ∣ M → CycLift M b σ → (l : ℤ_[l]) ^ m ∣ ((cyclotomicCharacter Ω l σ : ℤ_[l]ˣ) : ℤ_[l]) - (((b : ZMod M).val : ℕ) : ℤ_[l]) := by
  intro E Ω _ _ _ _ _ l _ N m _
  haveI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed E
  haveI : CharZero Ω := charZero_of_injective_algebraMap (algebraMap E Ω).injective
  haveI : NeZero (l : Ω) := ⟨Nat.cast_ne_zero.2 (Fact.out : l.Prime).ne_zero⟩
  have key : ∀ (g : G E Ω) (k : ℕ),
      PadicInt.toZModPow k ((cyclotomicCharacter Ω l (MulSemiringAction.toRingAut (G E Ω) Ω g) : ℤ_[l]ˣ) : ℤ_[l]) = 1 ↔
        ∀ t : Ω, t ^ (l ^ k) = 1 → g t = t := by
    intro g k
    rw [← pow_cyc_char_iff_toZModPow_eq l _ k 1]
    refine forall_congr' fun t => imp_congr_right fun ht => ?_
    rw [ZMod.val_one_eq_one_mod, pow_mod_eq_pow_of_pow_eq_one t _ 1 ht, pow_one]
    rfl
  refine ⟨?_, ?_, ?_⟩
  · ext g
    simp only [Un, levU, Subgroup.mem_inf, Subgroup.mem_top, true_and, Subgroup.mem_comap, KStar.TotallyRealRoots.princ,
      cycZ, MonoidHom.mem_ker, KStar.TotallyRealRoots.redPow, MonoidHom.comp_apply, Units.ext_iff, Units.coe_map,
      MonoidHom.coe_coe, Units.val_one]
    change _ ↔ PadicInt.toZModPow m _ = 1
    rw [key]
    rfl
  · intro g hg
    rcases Subgroup.mem_inf.1 hg with ⟨h1, h2⟩
    have hχ : cyclotomicCharacter Ω l (MulSemiringAction.toRingAut (G E Ω) Ω g) = 1 := by
      simpa only [Uinf, cycU, Subgroup.mem_inf, Subgroup.mem_top, true_and, MonoidHom.mem_ker, cycZ,
        MonoidHom.comp_apply] using h1
    have hl : ∀ k, ∀ t : Ω, t ^ (l ^ k) = 1 → g t = t := fun k => (key g k).1 (by rw [hχ, Units.val_one, map_one])
    have hN : ∀ t : Ω, t ^ N = 1 → g t = t := h2
    obtain ⟨e, N', hndvd, hNe⟩ :=
      Nat.exists_eq_pow_mul_and_not_dvd (NeZero.ne N) l (Fact.out : l.Prime).one_lt.ne'
    have hcop : Nat.Coprime (l ^ (e + m)) N' :=
      Nat.Coprime.pow_left _ ((Nat.Prime.coprime_iff_not_dvd Fact.out).2 hndvd)
    intro x hx
    have hx0 : x ≠ 0 := by
      rintro rfl
      rw [zero_pow (Nat.mul_ne_zero (NeZero.ne N) (pow_ne_zero _ (Fact.out : l.Prime).ne_zero))] at hx
      exact zero_ne_one hx
    have hxA : x ^ (l ^ (e + m) * N') = 1 := by
      rw [← hx, hNe, pow_add]
      congr 1
      ring
    have h3 : g (x ^ N') = x ^ N' := hl (e + m) _ (by rw [← pow_mul, mul_comm, hxA])
    have h4 : g (x ^ (l ^ (e + m))) = x ^ (l ^ (e + m)) := by
      apply hN
      rw [hNe, ← pow_mul, show l ^ (e + m) * (l ^ e * N') = (l ^ (e + m) * N') * l ^ e by ring, pow_mul, hxA,
        one_pow]
    have hyA : (g x * x⁻¹) ^ (l ^ (e + m)) = 1 := by
      rw [mul_pow, inv_pow, ← map_pow, h4, mul_inv_cancel₀ (pow_ne_zero _ hx0)]
    have hyB : (g x * x⁻¹) ^ N' = 1 := by
      rw [mul_pow, inv_pow, ← map_pow, h3, mul_inv_cancel₀ (pow_ne_zero _ hx0)]
    have hy : (g x * x⁻¹) ^ (Nat.gcd (l ^ (e + m)) N') = 1 := pow_gcd_eq_one.2 ⟨hyA, hyB⟩
    rw [Nat.Coprime.gcd_eq_one hcop, pow_one] at hy
    exact (mul_inv_eq_one₀ hx0).1 hy
  · intro M _ b σ hdvd hσ
    have hc := (pow_cyc_char_iff_toZModPow_eq l σ m (((b : ZMod M).val : ℕ) : ZMod (l ^ m))).1 (by
      intro t ht
      rw [ZMod.val_natCast, pow_mod_eq_pow_of_pow_eq_one t _ _ ht]
      apply hσ
      obtain ⟨q, rfl⟩ := hdvd
      rw [pow_mul, ht, one_pow])
    have hmem : ((cyclotomicCharacter Ω l σ : ℤ_[l]ˣ) : ℤ_[l]) - (((b : ZMod M).val : ℕ) : ℤ_[l]) ∈
        RingHom.ker (PadicInt.toZModPow m) := by
      rw [RingHom.mem_ker, map_sub, hc, map_natCast, sub_self]
    rw [PadicInt.ker_toZModPow, Ideal.mem_span_singleton] at hmem
    exact hmem
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.OddResidueBounds.LenPow
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.GaloisCohomology UpperTheory.V UpperTheory.V.LDataCardLeFinrank UpperTheory.V.Base UpperTheory.V.Kum UpperTheory.V.Bern UpperTheory.V.B4 UpperTheory.V.B5 UpperTheory.V.Odd

private theorem length_ker_pow_le (R X : Type) [CommRing R] [AddCommGroup X] [Module R X]
    (f : Module.End R X) (r : ℕ) :
    Module.length R (LinearMap.ker (f ^ r)) ≤ r * Module.length R (LinearMap.ker f) := by
  induction r with
  | zero =>
    simp only [Nat.cast_zero, zero_mul, nonpos_iff_eq_zero]
    rw [Module.length_eq_zero_iff]
    refine ⟨fun x y => Subtype.ext ?_⟩
    have hx := LinearMap.mem_ker.mp x.2
    have hy := LinearMap.mem_ker.mp y.2
    simp only [pow_zero, Module.End.one_apply] at hx hy
    rw [hx, hy]
  | succ n ih =>
    rw [pow_succ]
    refine ((UpperTheory.V.Base.lenComp R X (f ^ n) f).1).trans ?_
    calc Module.length R (LinearMap.ker (f ^ n)) + Module.length R (LinearMap.ker f)
        ≤ n * Module.length R (LinearMap.ker f) + Module.length R (LinearMap.ker f) := by
          gcongr
      _ = ((n + 1 : ℕ) : ℕ∞) * Module.length R (LinearMap.ker f) := by
          push_cast; rw [add_mul, one_mul]

theorem UpperTheory.V.Odd.lenPow :
    ∀ (R X : Type) [CommRing R] [AddCommGroup X] [Module R X] (P : Submodule R X) (a : R) (r : ℕ), (∀ x ∈ P, a ^ r • x = 0) → Module.length R P ≤ r * Module.length R (Submodule.torsionBy R X a) := by
  intro R X _ _ _ P a r hP
  let f : Module.End R X := a • (1 : Module.End R X)
  have hker : LinearMap.ker f = Submodule.torsionBy R X a := by
    ext x
    simp [f, Submodule.mem_torsionBy_iff]
  have hpow : ∀ x : X, (f ^ r) x = a ^ r • x := by
    intro x
    simp [f, smul_pow]
  have hle : P ≤ LinearMap.ker (f ^ r) := by
    intro x hx
    rw [LinearMap.mem_ker, hpow]
    exact hP x hx
  calc Module.length R P ≤ Module.length R (LinearMap.ker (f ^ r)) :=
        Module.length_le_of_injective (Submodule.inclusion hle) (Submodule.inclusion_injective hle)
    _ ≤ r * Module.length R (LinearMap.ker f) := length_ker_pow_le R X f r
    _ = r * Module.length R (Submodule.torsionBy R X a) := by rw [hker]
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.OddResidueBounds.LiftEx
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.GaloisCohomology UpperTheory.V UpperTheory.V.LDataCardLeFinrank UpperTheory.V.Base UpperTheory.V.Kum UpperTheory.V.Bern UpperTheory.V.B4 UpperTheory.V.B5 UpperTheory.V.Odd

theorem UpperTheory.V.Odd.liftEx :
    ∀ (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (N : ℕ) [NeZero N], (∀ b : (ZMod N)ˣ, ∃ σ : Ω ≃+* Ω, CycLift N b σ) ∧ ∀ σ : Ω ≃+* Ω, ∃ b : (ZMod N)ˣ, CycLift N b σ := by
  intro E Ω _ _ _ _ _ N _
  haveI : CharZero Ω := charZero_of_injective_algebraMap (algebraMap E Ω).injective
  haveI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed E
  haveI : Algebra.IsAlgebraic ℚ Ω := Algebra.IsAlgebraic.trans ℚ E Ω
  haveI : IsAlgClosure ℚ Ω := ⟨inferInstance, inferInstance⟩
  have hN : NeZero (N : Ω) := ⟨by exact_mod_cast NeZero.ne N⟩
  have hpos : 0 < N := NeZero.pos N
  obtain ⟨ζ, hζ⟩ := IsAlgClosed.exists_root (Polynomial.cyclotomic N Ω) (Polynomial.degree_cyclotomic_pos N Ω hpos).ne'
  have hζp : IsPrimitiveRoot ζ N := Polynomial.isRoot_cyclotomic_iff.mp hζ
  constructor
  · intro b
    have hx : IsPrimitiveRoot (ζ ^ (b : ZMod N).val) N := hζp.pow_of_coprime _ (ZMod.val_coe_unit_coprime b)
    have hmin : minpoly ℚ ζ = Polynomial.cyclotomic N ℚ := (Polynomial.cyclotomic_eq_minpoly_rat hζp hpos).symm
    have hev : Polynomial.aeval (ζ ^ (b : ZMod N).val) (minpoly ℚ ζ) = 0 := by
      rw [hmin, Polynomial.aeval_def, Polynomial.eval₂_eq_eval_map, Polynomial.map_cyclotomic]
      exact Polynomial.isRoot_cyclotomic_iff.mpr hx
    obtain ⟨σ, hσ⟩ := minpoly.exists_algEquiv_of_root' (Algebra.IsAlgebraic.isAlgebraic ζ) hev
    refine ⟨σ.toRingEquiv, fun x hxN => ?_⟩
    obtain ⟨k, -, rfl⟩ := hζp.eq_pow_of_pow_eq_one hxN
    show σ (ζ ^ k) = (ζ ^ k) ^ (b : ZMod N).val
    rw [map_pow, hσ, ← pow_mul, ← pow_mul, mul_comm]
  · intro σ
    have h1 : IsPrimitiveRoot (σ ζ) N := hζp.map_of_injective σ.injective
    obtain ⟨i, hi, hiζ⟩ := hζp.eq_pow_of_pow_eq_one h1.pow_eq_one
    have hcop : i.Coprime N := (hζp.pow_iff_coprime hpos i).mp (hiζ ▸ h1)
    refine ⟨ZMod.unitOfCoprime i hcop, fun x hxN => ?_⟩
    obtain ⟨k, -, rfl⟩ := hζp.eq_pow_of_pow_eq_one hxN
    rw [map_pow, ← hiζ, ZMod.coe_unitOfCoprime, ZMod.val_natCast_of_lt hi, ← pow_mul, ← pow_mul, mul_comm]
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.OddResidueBounds.LogDisc
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.GaloisCohomology UpperTheory.V UpperTheory.V.LDataCardLeFinrank UpperTheory.V.Base UpperTheory.V.Kum UpperTheory.V.Bern UpperTheory.V.B4 UpperTheory.V.B5 UpperTheory.V.Odd

theorem UpperTheory.V.Odd.logDisc :
    ∀ (E : Type) [Field E] [NumberField E] (N : ℕ), 0 < N → Nonempty (E →ₐ[ℚ] CyclotomicField N ℚ) → (discr E).natAbs ≤ N ^ Module.finrank ℚ E ∧ Module.finrank ℚ E ≤ N := by
  intro E _ _ N hN ⟨φ⟩
  haveI : NeZero N := ⟨hN.ne'⟩
  haveI : NeZero (N : ℚ) := ⟨by exact_mod_cast hN.ne'⟩
  haveI : IsCyclotomicExtension {N} ℚ (CyclotomicField N ℚ) := CyclotomicField.isCyclotomicExtension N ℚ
  let F := φ.fieldRange
  have e : E ≃ₐ[ℚ] F := AlgEquiv.ofInjectiveField φ
  have hrank : Module.finrank ℚ E = Module.finrank ℚ F := e.toLinearEquiv.finrank_eq
  have hdisc : discr E = discr F := NumberField.discr_eq_discr_of_algEquiv E e
  obtain ⟨hprod, -, -⟩ := KStar.Ram.natAbs_discr_eq_finprod_conductor (N := N) (K := CyclotomicField N ℚ) F
  obtain ⟨hcard, -⟩ := KStar.Ram.card_fieldChars (N := N) (K := CyclotomicField N ℚ) F
  constructor
  · rw [hdisc, hprod, hrank, ← hcard]
    haveI : Fintype (KStar.Ram.fieldChars N F) := Fintype.ofFinite _
    rw [finprod_eq_prod_of_fintype, Nat.card_eq_fintype_card, ← Finset.card_univ]
    exact Finset.prod_le_pow_card _ _ _
      (fun ψ _ => Nat.le_of_dvd hN (DirichletCharacter.conductor_dvd_level _))
  · have hinj : Function.Injective φ.toLinearMap := (φ : E →+* CyclotomicField N ℚ).injective
    have h := LinearMap.finrank_le_finrank_of_injective hinj
    rw [IsCyclotomicExtension.finrank (CyclotomicField N ℚ)
      (Polynomial.cyclotomic.irreducible_rat hN)] at h
    exact h.trans (Nat.totient_le N)
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.OddResidueBounds.ProdVal
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.GaloisCohomology UpperTheory.V UpperTheory.V.LDataCardLeFinrank UpperTheory.V.Base UpperTheory.V.Kum UpperTheory.V.Bern UpperTheory.V.B4 UpperTheory.V.B5 UpperTheory.V.Odd

theorem UpperTheory.V.Odd.prodVal :
    ∀ (N : ℕ) [NeZero N] (k : ℕ) (P : Set (Subgroup (ZMod N)ˣ)), 1 ≤ k → P ⊆ parKer N k → ∃ w : ℕ → ℕ, (∀ T : Finset ℕ, (∀ l ∈ T, l.Prime) → ∑ l ∈ T, (w l : ℝ) * Real.log l ≤ (charSet ℂ P).ncard * Real.log (bnd N k)) ∧ ∀ (l : ℕ) [Fact l.Prime] (T : Finset (DirichletCharacter (PadicAlgCl l) N)), (T : Set _) ⊆ charSet (PadicAlgCl l) P → ∑ χ ∈ T, -Real.log ‖alN k χ‖ ≤ (w l : ℝ) * Real.log l := by
  intro N _ k P hk hP
  obtain ⟨M, hM0, hlog, hprod⟩ := b_prodint k P hk hP
  refine ⟨fun l => padicValInt l M, fun T hT => (b_sumval M hM0 T hT).trans hlog, ?_⟩
  intro l _ T hTS
  have hnorm : ‖(l : PadicAlgCl l)‖ = (l : ℝ)⁻¹ := by
    rw [← map_natCast (algebraMap ℚ_[l] (PadicAlgCl l)), PadicAlgCl.norm_extends, Padic.norm_p]
  have hS : (charSet (PadicAlgCl l) P).Finite := Set.toFinite _
  have hint : ∀ χ ∈ charSet (PadicAlgCl l) P, IsIntegral ℤ (((1 : ℕ) : PadicAlgCl l) * alN k χ) := by
    intro χ _
    rw [Nat.cast_one, one_mul]
    exact (b_primmem k χ).2.2.1
  have hpr : ∏ᶠ (χ : DirichletCharacter (PadicAlgCl l) N) (_ : χ ∈ charSet (PadicAlgCl l) P),
      ((1 : ℕ) : PadicAlgCl l) * alN k χ = (M : PadicAlgCl l) := by
    simp only [Nat.cast_one, one_mul]
    exact hprod (PadicAlgCl l)
  have hu := b_ultra l hnorm (charSet (PadicAlgCl l) P) (fun χ => alN k χ) 1 M hS hM0 hint hpr
  rw [finsum_mem_eq_finite_toFinset_sum _ hS] at hu
  calc ∑ χ ∈ T, -Real.log ‖alN k χ‖ ≤ ∑ χ ∈ T, max 0 (-Real.log ‖alN k χ‖) :=
        Finset.sum_le_sum fun χ _ => le_max_right _ _
    _ ≤ ∑ χ ∈ hS.toFinset, max 0 (-Real.log ‖alN k χ‖) :=
        Finset.sum_le_sum_of_subset_of_nonneg
          (fun χ hχ => hS.mem_toFinset.mpr (hTS (Finset.mem_coe.mpr hχ))) (fun _ _ _ => le_max_left _ _)
    _ ≤ _ := hu
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.OddResidueBounds.YLevel
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.GaloisCohomology UpperTheory.V UpperTheory.V.LDataCardLeFinrank UpperTheory.V.Base UpperTheory.V.Kum UpperTheory.V.Bern UpperTheory.V.B4 UpperTheory.V.B5 UpperTheory.V.Odd

private theorem fib_iff {N M : ℕ} [NeZero N] [NeZero M] (h : N ∣ M) (b' : (ZMod M)ˣ) (b : (ZMod N)ˣ) :
    ZMod.unitsMap h b' = b ↔ (b' : ZMod M).val % N = (b : ZMod N).val := by
  rw [Units.ext_iff, ZMod.unitsMap_def, Units.coe_map]
  simp only [MonoidHom.coe_coe, ZMod.castHom_apply]
  rw [ZMod.cast_eq_val, ← (ZMod.val_injective N).eq_iff, ZMod.val_natCast]

private theorem fib_sum {N L M : ℕ} [NeZero N] [NeZero M] (h : N ∣ M) (hM : M = N * L)
    (hc : ∀ n : ℕ, n.Coprime N → n.Coprime M) (f : ℕ → ℚ) (b : (ZMod N)ˣ) :
    ∑ b' ∈ Finset.univ.filter (fun b' : (ZMod M)ˣ => ZMod.unitsMap h b' = b), f (b' : ZMod M).val
      = ∑ j ∈ Finset.range L, f ((b : ZMod N).val + j * N) := by
  have hN : 0 < N := NeZero.pos N
  have hbN : (b : ZMod N).val < N := ZMod.val_lt _
  have hcop : ∀ n : ℕ, ((b : ZMod N).val + n * N).Coprime M := fun n =>
    hc _ (by simpa using ZMod.val_coe_unit_coprime b)
  have hlt : ∀ n ∈ Finset.range L, (b : ZMod N).val + n * N < M := by
    intro n hn
    rw [Finset.mem_range] at hn
    rw [hM]
    nlinarith
  symm
  refine Finset.sum_nbij' (fun n => ZMod.unitOfCoprime _ (hcop n)) (fun b' => (b' : ZMod M).val / N)
    ?_ ?_ ?_ ?_ ?_
  · intro n hn
    rw [Finset.mem_filter]
    refine ⟨Finset.mem_univ _, ?_⟩
    rw [fib_iff, ZMod.coe_unitOfCoprime, ZMod.val_natCast, Nat.mod_eq_of_lt (hlt n hn),
      Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hbN]
  · intro b' _
    rw [Finset.mem_range, Nat.div_lt_iff_lt_mul hN, mul_comm, ← hM]
    exact ZMod.val_lt _
  · intro n hn
    simp only [ZMod.coe_unitOfCoprime, ZMod.val_natCast]
    rw [Nat.mod_eq_of_lt (hlt n hn), Nat.add_mul_div_right _ _ hN, Nat.div_eq_of_lt hbN, zero_add]
  · intro b' hb'
    rw [Finset.mem_filter, fib_iff] at hb'
    apply Units.ext
    rw [ZMod.coe_unitOfCoprime, ← hb'.2, Nat.mod_add_div', ZMod.natCast_zmod_val]
  · intro n hn
    rw [ZMod.coe_unitOfCoprime, ZMod.val_natCast, Nat.mod_eq_of_lt (hlt n hn)]

private theorem sum_single_eq_single_sum {Γ : Type} [CommGroup Γ] {ι : Type} (s : Finset ι) (g : Γ) (F : ι → ℚ) :
    ∑ x ∈ s, MonoidAlgebra.single g (F x) = MonoidAlgebra.single g (∑ x ∈ s, F x) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih => rw [Finset.sum_insert ha, ih, Finset.sum_insert ha, MonoidAlgebra.single_add]

private theorem theta_level {Γ : Type} [CommGroup Γ] {N L M : ℕ} [NeZero N] [NeZero M] (h : N ∣ M) (hM : M = N * L)
    (hc : ∀ n : ℕ, n.Coprime N → n.Coprime M) (φ : (ZMod N)ˣ →* Γ) (k : ℕ) :
    thetaEl k (φ.comp (ZMod.unitsMap h)) = thetaEl k φ := by
  have hLpos : 0 < L := by
    rcases Nat.eq_zero_or_pos L with hL | hL
    · exact absurd (hM.trans (by rw [hL, mul_zero])) (NeZero.ne M)
    · exact hL
  unfold thetaEl sumEl
  congr 1
  rw [← Finset.sum_fiberwise Finset.univ (ZMod.unitsMap h)]
  refine Finset.sum_congr rfl fun b _ => ?_
  have hfib : ∀ b' ∈ Finset.univ.filter (fun b' : (ZMod M)ˣ => ZMod.unitsMap h b' = b),
      MonoidAlgebra.single ((φ.comp (ZMod.unitsMap h)) b')⁻¹ (Ek M k (b' : ZMod M))
        = MonoidAlgebra.single (φ b)⁻¹ (Ek M k (b' : ZMod M)) := by
    intro b' hb'
    rw [Finset.mem_filter] at hb'
    rw [MonoidHom.comp_apply, hb'.2]
  rw [Finset.sum_congr rfl hfib, sum_single_eq_single_sum]
  congr 1
  unfold Ek
  rw [← Finset.sum_div, fib_sum h hM hc (fun n => bcoef M k n) b, hM,
    b_raabe N L k _ (NeZero.pos N) hLpos]

theorem UpperTheory.V.Odd.yLevel :
    ∀ (l : ℕ) [Fact l.Prime] (Γ : Type) [CommGroup Γ] [Finite Γ] (N : ℕ) [NeZero N] (φ : (ZMod N)ˣ →* Γ) (k a : ℕ) (ha : a.Coprime N), 1 ≤ k → l ∣ N → ∀ (m M : ℕ) [NeZero M] (h : N ∣ M) (ha' : a.Coprime M), M = N * l ^ m → yEl k a ha' (φ.comp (ZMod.unitsMap h)) = yEl k a ha φ := by
  intro l _ Γ _ _ N _ φ k a ha hk hl m M _ h ha' hM
  have hc : ∀ n : ℕ, n.Coprime N → n.Coprime M := by
    intro n hn
    rw [hM]
    exact hn.mul_right ((Nat.Coprime.coprime_dvd_right hl hn).pow_right m)
  unfold yEl
  rw [theta_level h hM hc φ k]
  congr 4
  rw [MonoidHom.comp_apply]
  congr 1
  apply Units.ext
  rw [ZMod.unitsMap_def, Units.coe_map]
  simp only [MonoidHom.coe_coe, ZMod.castHom_apply, ZMod.coe_unitOfCoprime]
  exact ZMod.cast_natCast h a
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.OddResidueBounds.YNear
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.GaloisCohomology UpperTheory.V UpperTheory.V.LDataCardLeFinrank UpperTheory.V.Base UpperTheory.V.Kum UpperTheory.V.Bern UpperTheory.V.B4 UpperTheory.V.B5 UpperTheory.V.Odd

theorem UpperTheory.V.Odd.yNear :
    ∀ (l : ℕ) [Fact l.Prime] (Γ : Type) [CommGroup Γ] [Finite Γ] (N : ℕ) [NeZero N] (φ : (ZMod N)ˣ →* Γ) (e a r : ℕ) (ha : a.Coprime N), Odd a → l ^ (r + ck l (e + 1) + 1) ∣ N → IntAt l r (yEl (e + 1) a ha φ - coefMap ℚ Γ (ytEl e a φ)) := by
  intro l _ Γ _ _ N _ φ e a r ha hodd hdvd
  have hy := (Stk.twistedStickelbergerElements_agree N a ha Γ φ (e + 1)).1
  have hyt := (Stk.twistedStickelbergerElements_agree N a ha Γ φ e).2.1
  have hcf := (Stk.twistedStickelbergerElements_agree N a ha Γ φ e).2.2.2
  choose z hz using Stk.twistedBernoulliValue_congr_pow_mul_first N a e ha hodd
  rw [hy, hyt, hcf]
  have key : Stk.yForm (e + 1) a φ - Stk.cf ℚ Γ (Stk.ytEl e a φ)
      = ((N : ℚ) / (Stk.dk (e + 1) : ℚ)) • Stk.cf ℚ Γ (Stk.sumEl φ (fun b => -z b)) := by
    rw [Stk.cf_sumEl]
    unfold Stk.yForm Stk.ytEl
    rw [map_neg, Stk.cf_sumEl]
    unfold Stk.sumEl
    rw [neg_sub_neg, ← Finset.sum_sub_distrib, Finset.smul_sum]
    refine Finset.sum_congr rfl (fun b _ => ?_)
    rw [hz _, MonoidAlgebra.smul_single]
    first
      | rw [← MonoidAlgebra.single_sub]
      | erw [← Finsupp.single_sub]
    congr 1
    simp only [smul_eq_mul]
    push_cast
    ring
  rw [key]
  have hN0 : N ≠ 0 := NeZero.ne N
  have hv := ((by simpa only [_root_.Nat.padicValNat_def] using @_root_.multiplicity_dvd_iff_le : ∀ {p : _root_.Nat} [hp : _root_.Fact (_root_.Nat.Prime p)] {a n : _root_.Nat} (ha : a ≠ 0), p ^ n ∣ a ↔ n ≤ _root_.padicValNat p a) hN0).mp hdvd
  apply Stk.groupRing_intAt_div_smul_of_padicValNat_le l N (Stk.dk (e + 1)) r (Nat.pos_of_ne_zero hN0) (Stk.dk_pos (Nat.succ_pos e))
  have hck : ck l (e + 1) = padicValNat l (Stk.dk (e + 1)) := rfl
  omega
end

