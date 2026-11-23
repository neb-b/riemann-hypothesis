module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.LevelCohomology.HcDefs
public import Development.AutomorphicArithmetic.AutomorphicVarieties.HeightAndVanishing.Bundle0001
public import Development.AutomorphicArithmetic.AutomorphicVarieties.UnitaryThreeDeformations.HostNumber
public import Development.AutomorphicArithmetic.AutomorphicVarieties.HeightAndVanishing.Bundle0004
public import Development.AutomorphicArithmetic.AutomorphicVarieties.LevelCohomology.Bundle0012
public import Development.AutomorphicArithmetic.AutomorphicVarieties.LevelCohomology.Bundle0011
public import Development.AutomorphicArithmetic.AutomorphicVarieties.LevelCohomology.Bundle0005
public import Development.AutomorphicArithmetic.AutomorphicVarieties.LevelCohomology.Bundle0008
public import Development.AutomorphicArithmetic.AutomorphicVarieties.SymplecticGSp4.ResidueCharMemLevelPrimes
public import Development.AutomorphicArithmetic.AutomorphicVarieties.LevelCohomology.Bundle0009
public import Development.AutomorphicArithmetic.AutomorphicVarieties.LevelCohomology.Bundle0002
public import Development.AutomorphicArithmetic.AutomorphicVarieties.HeightAndVanishing.Counts
public import Development.AutomorphicArithmetic.AutomorphicVarieties.GeneratorCountTuples.LemmaK
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0003
public import Formalism.GaloisCohomology.LocalTateDualityK
public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.LocalRingsCompletion.Bundle0001

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.LevelCohomology.DirGPowOne
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal IsLocalRing UpperTheory.V UpperTheory.V.Base UpperTheory.V.HV UpperTheory.V.X

private theorem res_of_sub {O : Type} [CommRing O] [IsLocalRing O] {x y : O} (h : x - y ∈ maximalIdeal O) :
    residue O x = residue O y := by
  exact Ideal.Quotient.eq.2 h

private theorem dirG_pow_one {Ω : Type} [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] {O : Type} [CommRing O] {N : ℕ} [NeZero N]
    (χ : DirichletCharacter O N) (m : ℕ) (h : χ ^ m = 1) : Chr.dirG ℚ Ω χ ^ m = 1 := by
  ext g
  simp only [MonoidHom.pow_apply, MonoidHom.one_apply, Units.val_pow_eq_pow_val, Units.val_one]
  show (χ (Chr.cls ℚ Ω N g : ZMod N)) ^ m = 1
  rw [← MulChar.pow_apply_coe, h, MulChar.one_apply_coe]

theorem UpperTheory.V.X.dir :
    ∀ (Ω : Type) [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] (l : ℕ) [Fact l.Prime] (c : Coef l) (N : ℕ) [NeZero N] (e : ℕ) (ψ : DirichletCharacter c.O N) (o₁ : ℕ), UnitaryThreeInertia.HostData l e ψ o₁ → ∀ q : ℕ, UnitaryThreeInertia.XData l ψ q → ∃ (d f n : ℕ) (_ : NeZero (f * 2 ^ n)) (φ : DirichletCharacter c.O f) (ξ : DirichletCharacter c.O (2 ^ n)), XData l d φ ξ ∧ ∀ g : G ℚ Ω, (redChar Ω (residue c.O) (prodX φ ξ) g : ResidueField c.O) = residue c.O (Chr.Psi l e (Chr.dirG ℚ Ω ψ) g : c.O) ^ 2 * ((UnitaryThreeInertia.eta4 Ω g : ℤ) : ResidueField c.O) := by
  intro Ω _ _ _ l _ c N _ e ψ o₁ hHD q hX
  obtain ⟨ω, hω1, hωT⟩ := omDir Ω l c
  obtain ⟨d, f, n, φ, ξ, hXD, hdvd, hv⟩ := dirData l c N e ψ o₁ hHD q hX ω hω1
  have hl : l.Prime := Fact.out
  haveI : NeZero l := ⟨hl.ne_zero⟩
  have hf0 : f ≠ 0 := by
    rintro rfl
    obtain ⟨k, hk⟩ := hXD.f_odd
    omega
  haveI hNZ : NeZero (f * 2 ^ n) := ⟨Nat.mul_ne_zero hf0 (pow_ne_zero _ two_ne_zero)⟩
  haveI : NeZero (l * N * N) := ⟨Nat.mul_ne_zero (Nat.mul_ne_zero hl.ne_zero (NeZero.ne N)) (NeZero.ne N)⟩
  refine ⟨d, f, n, hNZ, φ, ξ, hXD, ?_⟩
  intro g
  obtain ⟨a, ha, hA⟩ := dirVal Ω (l * N * N) g
  obtain ⟨hψdec, ⟨s, hks⟩, -⟩ := th1Facts c.O N ψ l hl hHD.l_odd
  have hprod := hA (f * 2 ^ n) hdvd c.O (prodX φ ξ)
  have hψa := hA N ⟨l * N, by ring⟩ c.O ψ
  have hωa := hA l ⟨N * N, by ring⟩ c.O ω
  have h4 : 4 ∣ l * N * N := by
    obtain ⟨k, hk⟩ := hHD.N_even
    exact ⟨l * k * k, by rw [hk]; ring⟩
  have hη := hA 4 h4 ℤ ZMod.χ₄
  have hkap := hA N ⟨l * N, by ring⟩ c.O (kap l ψ)
  have hkC := (congrFacts Ω l c).2.2.1 (Chr.dirG ℚ Ω (kap l ψ)) s (dirG_pow_one _ _ hks)
  have hk1 : residue c.O (kap l ψ (a : ZMod N)) = 1 := by
    rw [← hkap, res_of_sub (hkC g)]
    simp
  have hωC := res_of_sub (hωT.2 g)
  rw [hωa] at hωC
  have hψa' : ψ (a : ZMod N) = psi2 ψ (a : ZMod N) * th1 l ψ (a : ZMod N) * kap l ψ (a : ZMod N) := by
    conv_lhs => rw [hψdec]
    rfl
  have hLHS : (redChar Ω (residue c.O) (prodX φ ξ) g : ResidueField c.O) =
      residue c.O ((prodX φ ξ) (a : ZMod (f * 2 ^ n))) := by
    show residue c.O (Chr.dirG ℚ Ω (prodX φ ξ) g : c.O) = _
    rw [hprod]
  have hP : (Chr.Psi l e (Chr.dirG ℚ Ω ψ) g : c.O) = (chiO ℚ Ω l c.O g : c.O) ^ e * ψ (a : ZMod N) := by
    simp only [Chr.Psi, zpow_natCast, MonoidHom.mul_apply, MonoidHom.pow_apply, Units.val_mul,
      Units.val_pow_eq_pow_val, hψa]
  have hE : ((UnitaryThreeInertia.eta4 Ω g : ℤ)) = ZMod.χ₄ (a : ZMod 4) := hη
  rw [hLHS, hv a ha, hP, hE, hψa']
  simp only [map_mul, map_pow, map_intCast]
  rw [← hωC, hk1]
  ring
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.LevelCohomology.HcXvan
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal IsLocalRing Module UpperTheory.V UpperTheory.V.Base UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.X

private theorem xvan_of_van {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {l : ℕ} [Fact l.Prime] {c : Coef l}
    (D : Raw Ω c) (γ : G ℚ Ω →* c.Oˣ) (γ' : G ℚ Ω →* (ResidueField c.O)ˣ)
    (h : ∀ g, Raw.bar γ g = (γ' g : ResidueField c.O)) (hv : Van D.T D.pl D.rbar.ker γ') : D.XVan γ := by
  intro z hzlc hzc hzU hzD
  obtain ⟨m, hm⟩ := hv z hzlc (fun g k => by rw [hzc, h])
    (fun A hA g hgA hgK => hzU A hA g hgA (MonoidHom.mem_ker.mp hgK))
    (fun v hvT => by
      obtain ⟨m, hm⟩ := hzD v hvT
      exact ⟨m, fun g hg => by rw [hm g hg, h]⟩)
  exact ⟨m, fun g => by rw [hm g, h]⟩

theorem UpperTheory.V.X.xvan :
    CorX → ∀ {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {l : ℕ} [Fact l.Prime] {c : Coef l} (D : Raw Ω c), (∀ p ∈ D.T, p.Prime ∧ (D.pl p).valuation (p : Ω) < 1) → ∀ (d f n : ℕ) [NeZero (f * 2 ^ n)] (φ : DirichletCharacter c.O f) (ξ : DirichletCharacter c.O (2 ^ n)), XData l d φ ξ → ∀ γ : G ℚ Ω →* c.Oˣ, (∀ g, Raw.bar γ g = (redChar Ω (residue c.O) (prodX φ ξ) g : ResidueField c.O)) → D.XVan γ ∧ D.XVan γ⁻¹ := by
  intro hCor Ω _ _ _ l _ c D hT d f n _ φ ξ hX γ hγ
  haveI : CharP (ResidueField c.O) l := by
    obtain ⟨-, -, hloc, -⟩ := dvrFacts l c.O
    rw [CharP.charP_iff_prime_eq_zero (Fact.out : l.Prime)]
    rw [← map_natCast (residue c.O), residue_eq_zero_iff, mem_maximalIdeal, mem_nonunits_iff]
    intro hu
    rw [← map_natCast (algebraMap ℤ_[l] c.O)] at hu
    exact PadicInt.p_nonunit (isUnit_of_map_unit (algebraMap ℤ_[l] c.O) _ hu)
  set γ' : G ℚ Ω →* (ResidueField c.O)ˣ := redChar Ω (residue c.O) (prodX φ ξ) with hγ'
  obtain ⟨hKn, hKi, -⟩ := spKer D
  have hv : ∀ γ'' : G ℚ Ω →* (ResidueField c.O)ˣ, (γ'' = γ' ∨ γ'' = γ'⁻¹) →
      Van D.T D.pl D.rbar.ker γ'' := by
    intro γ'' hor
    exact vanOf Ω l (ResidueField c.O) γ''
      (hCor Ω l c (ResidueField c.O) (residue c.O) d f n φ ξ hX γ'' hor) D.T D.pl D.rbar.ker hT hKn hKi
  refine ⟨xvan_of_van D γ γ' hγ (hv γ' (Or.inl rfl)), xvan_of_van D γ⁻¹ γ'⁻¹ ?_ (hv γ'⁻¹ (Or.inr rfl))⟩
  intro g
  have h1 := hγ g
  simp only [Raw.bar, MonoidHom.inv_apply] at h1 ⊢
  rw [map_units_inv, Units.val_inv_eq_inv_val, h1]
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.LevelCohomology.IntIffNorm
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.GaloisCohomology UpperTheory.V UpperTheory.V.Base UpperTheory.V.Odd UpperTheory.V.ML UpperTheory.V.X
open TensorProduct nonZeroDivisors

private theorem int_iff_norm {l : ℕ} [Fact l.Prime] {K : Type} [Field K]
    [Algebra ℚ_[l] K] [Algebra ℤ_[l] K] [IsScalarTower ℤ_[l] ℚ_[l] K] [FiniteDimensional ℚ_[l] K]
    (φ : K →ₐ[ℚ_[l]] PadicAlgCl l) (x : K) : IsIntegral ℤ_[l] x ↔ ‖φ x‖ ≤ 1 := by
  have hi : IsIntegral ℚ_[l] x := Algebra.IsIntegral.isIntegral x
  have h0 : ‖φ x‖ = spectralValue (minpoly ℚ_[l] (φ x)) := rfl
  rw [h0, minpoly.algHom_eq φ φ.injective, spectralValue_le_one_iff (minpoly.monic hi)]
  constructor
  · intro h n
    rw [minpoly.isIntegrallyClosed_eq_field_fractions' ℚ_[l] h, Polynomial.coeff_map]
    exact PadicInt.norm_le_one _
  · intro h
    have hl' : minpoly ℚ_[l] x ∈ Polynomial.lifts (algebraMap ℤ_[l] ℚ_[l]) :=
      (Polynomial.lifts_iff_coeff_lifts _).mpr fun n => ⟨⟨_, h n⟩, rfl⟩
    obtain ⟨q, hq, -, hqm⟩ := Polynomial.lifts_and_degree_eq_and_monic hl' (minpoly.monic hi)
    exact ⟨q, hqm, by
      rw [← Polynomial.aeval_def, ← Polynomial.aeval_map_algebraMap ℚ_[l], hq, minpoly.aeval]⟩

private theorem qo_proj (l : ℕ) [Fact l.Prime] (O K : Type) [CommRing O] [Algebra ℤ_[l] O] [Field K] [Algebra O K]
    [Algebra ℚ_[l] K] [Algebra ℤ_[l] K] [IsScalarTower ℤ_[l] ℚ_[l] K] [IsScalarTower ℤ_[l] O K]
    [IsLocalization (Algebra.algebraMapSubmonoid O ℤ_[l]⁰) K] :
    ∃ π : K →ₗ[O] QO l O, Function.Surjective π ∧ ∀ x, π x = 0 ↔ ∃ o : O, algebraMap O K o = x := by
  haveI : Algebra.IsPushout ℤ_[l] O ℚ_[l] K := Algebra.isPushout_of_isLocalization ℤ_[l]⁰ ℚ_[l] O K
  let φ := Algebra.IsPushout.equiv ℤ_[l] O ℚ_[l] K
  let π : O ⊗[ℤ_[l]] ℚ_[l] →ₗ[O] QO l O := (ZlSub l).mkQ.baseChange O
  have hs : Function.Surjective π := LinearMap.lTensor_surjective O (ZlSub l).mkQ_surjective
  have hex : Function.Exact (Algebra.linearMap ℤ_[l] ℚ_[l]) (ZlSub l).mkQ := by
    rw [LinearMap.exact_iff, Submodule.ker_mkQ]
  have hex2 := lTensor_exact O hex (ZlSub l).mkQ_surjective
  have hk1 : LinearMap.ker π = Submodule.span O {1} := by
    apply le_antisymm
    · intro x hx
      obtain ⟨y, rfl⟩ := (hex2 x).1 hx
      obtain ⟨o, rfl⟩ := (TensorProduct.rid ℤ_[l] O).symm.surjective y
      rw [Submodule.mem_span_singleton]
      refine ⟨o, ?_⟩
      simp [Algebra.TensorProduct.one_def, TensorProduct.smul_tmul']
    · rw [Submodule.span_le, Set.singleton_subset_iff]
      exact (hex2 1).2 ⟨1, by simp [Algebra.TensorProduct.one_def]⟩
  refine ⟨π ∘ₗ φ.symm.toLinearMap, hs.comp φ.symm.surjective, fun x => ?_⟩
  change φ.symm x ∈ LinearMap.ker π ↔ _
  rw [hk1, Submodule.mem_span_singleton]
  refine exists_congr fun o => ?_
  rw [← Algebra.algebraMap_eq_smul_one, AlgEquiv.eq_symm_apply, φ.commutes]

private theorem kill_of_len {O N : Type} [CommRing O] [IsLocalRing O] [AddCommGroup N] [Module O N]
    (h : Module.length O N ≠ ⊤) {p : O} (hp : p ∈ IsLocalRing.maximalIdeal O) : ∃ n : ℕ, ∀ x : N, p ^ n • x = 0 := by
  have hf := Module.length_ne_top_iff.1 h
  rw [isFiniteLength_iff_isNoetherian_isArtinian] at hf
  obtain ⟨h1, h2⟩ := hf
  obtain ⟨n, hn⟩ := IsArtinian.range_smul_pow_stabilizes N p
  have hle : LinearMap.range (p ^ n • LinearMap.id : N →ₗ[O] N) ≤
      IsLocalRing.maximalIdeal O • LinearMap.range (p ^ n • LinearMap.id : N →ₗ[O] N) := by
    intro x hx
    rw [hn (n + 1) (Nat.le_succ n)] at hx
    obtain ⟨y, rfl⟩ := hx
    have : (p ^ (n + 1) • LinearMap.id : N →ₗ[O] N) y = p • (p ^ n • LinearMap.id : N →ₗ[O] N) y := by
      simp [pow_succ', mul_smul]
    rw [this]
    exact Submodule.smul_mem_smul hp ⟨y, rfl⟩
  have hb := Submodule.eq_bot_of_le_smul_of_le_jacobson_bot _ _ (IsNoetherian.noetherian _) hle
    (IsLocalRing.maximalIdeal_le_jacobson _)
  refine ⟨n, fun x => ?_⟩
  have : (p ^ n • LinearMap.id : N →ₗ[O] N) x ∈ (⊥ : Submodule O N) := hb ▸ ⟨x, rfl⟩
  simpa using this

private theorem core {G O K W : Type} [Group G] [TopologicalSpace G] [CommRing O] [IsLocalRing O] [NormedField K] [Algebra O K]
    [AddCommGroup W] [Module O W] [TopologicalSpace W] [IsTopologicalAddGroup W] [ContinuousConstSMul O W]
    (π : K →ₗ[O] W) (hs : Function.Surjective π) (hc : Continuous π) (hk : ∀ x, π x = 0 → ‖x‖ ≤ 1)
    (ρ : Representation O G W) (θ : G → O) (hρ : ∀ g m, ρ g m = θ g • m) (𝒟 : Set (Subgroup G))
    (hfin : Module.length O (LocSel ρ ⊤ 𝒟) ≠ ⊤) {p : O} (hp : p ∈ IsLocalRing.maximalIdeal O)
    (hp0 : algebraMap O K p ≠ 0) (hp1 : ‖algebraMap O K p‖ < 1) (c : G → K) (hcc : Continuous c)
    (hco : ∀ g h, c (g * h) = c g + θ g • c h) (hloc : ∀ D ∈ 𝒟, ∃ m, ∀ g ∈ D, c g = θ g • m - m) :
    ∃ m, ∀ g, c g = θ g • m - m := by
  obtain ⟨N, hN⟩ := kill_of_len hfin hp
  set q := algebraMap O K p with hq
  have key : ∀ n : ℕ, ∃ m : K, ∀ g, ‖c g - (θ g • m - m)‖ ≤ ‖q‖ ^ n := by
    intro n
    have hqn : q ^ (n + N) ≠ 0 := pow_ne_zero _ hp0
    let z : Z1U ρ ⊤ := ⟨fun u => π ((q ^ (n + N))⁻¹ * c u.1),
      hc.comp (continuous_const.mul (hcc.comp continuous_subtype_val)), fun g h => by
        show π (_ * c (g.1 * h.1)) = π _ + ρ g.1 (π _)
        rw [hco, hρ, mul_add, map_add (f := _), mul_smul_comm, map_smul]⟩
    have hz : Submodule.Quotient.mk z ∈ LocSel ρ ⊤ 𝒟 := by
      rw [mk_mem_locSel]
      intro D hD
      obtain ⟨m, hm⟩ := hloc D hD
      refine ⟨π ((q ^ (n + N))⁻¹ * m), fun u hu => ?_⟩
      show π (_ * c u.1) = _
      rw [hm _ hu, hρ, mul_sub, map_sub, mul_smul_comm, map_smul]
    have h0 : (Submodule.Quotient.mk (p ^ N • z) : H1U ρ ⊤) = Submodule.Quotient.mk 0 :=
      congrArg Subtype.val (hN ⟨_, hz⟩)
    obtain ⟨w, hw⟩ := (mk_eq_mk ρ ⊤ _ _).1 h0
    obtain ⟨y, rfl⟩ := hs w
    refine ⟨q ^ n * y, fun g => ?_⟩
    have h1 : p ^ N • π ((q ^ (n + N))⁻¹ * c g) - 0 = ρ g (π y) - π y := hw ⟨g, trivial⟩
    rw [sub_zero, hρ, ← map_smul, ← map_smul, ← map_sub, ← sub_eq_zero, ← map_sub] at h1
    have h2 := hk _ h1
    have h3 : c g - (θ g • (q ^ n * y) - q ^ n * y) = q ^ n * (p ^ N • ((q ^ (n + N))⁻¹ * c g) - (θ g • y - y)) := by
      simp only [Algebra.smul_def, map_pow, ← hq]
      field_simp
      ring
    rw [h3, norm_mul, norm_pow]
    exact mul_le_of_le_one_right (by positivity) h2
  have lim : ∀ (x : K) (C : ℝ), (∀ n : ℕ, ‖x‖ ≤ ‖q‖ ^ n * C) → x = 0 := by
    intro x C h
    have ht := (tendsto_pow_atTop_nhds_zero_of_lt_one (norm_nonneg _) hp1).mul_const C
    rw [zero_mul] at ht
    exact norm_le_zero_iff.1 (ge_of_tendsto' ht h)
  by_cases hθ : ∀ g, algebraMap O K (θ g) = 1
  · refine ⟨0, fun g => ?_⟩
    rw [smul_zero, sub_zero]
    refine lim _ 1 fun n => ?_
    obtain ⟨m, hm⟩ := key n
    simpa [Algebra.smul_def, hθ] using hm g
  push Not at hθ
  obtain ⟨g₀, hg₀⟩ := hθ
  have hd : algebraMap O K (θ g₀) - 1 ≠ 0 := sub_ne_zero.2 hg₀
  refine ⟨c g₀ / (algebraMap O K (θ g₀) - 1), fun g => ?_⟩
  rw [← sub_eq_zero]
  refine lim _ (1 + ‖(algebraMap O K (θ g) - 1) / (algebraMap O K (θ g₀) - 1)‖) fun n => ?_
  obtain ⟨m, hm⟩ := key n
  have h3 : c g - (θ g • (c g₀ / (algebraMap O K (θ g₀) - 1)) - c g₀ / (algebraMap O K (θ g₀) - 1)) =
      (c g - (θ g • m - m)) - (c g₀ - (θ g₀ • m - m)) * ((algebraMap O K (θ g) - 1) / (algebraMap O K (θ g₀) - 1)) := by
    simp only [Algebra.smul_def]
    field_simp
    ring
  rw [h3, mul_add, mul_one]
  refine (norm_sub_le _ _).trans (add_le_add (hm g) ?_)
  rw [norm_mul]
  exact mul_le_mul_of_nonneg_right (hm g₀) (norm_nonneg _)

theorem UpperTheory.V.X.soVec :
    ∀ CK : ℝ, LemmaK CK → GlobalTheory.Published.PoitouTateDuality → LocalFinitenessK → LocalTateDualityK → ∀ (k Ω : Type) [Field k] [NumberField k] [Field Ω] [Algebra k Ω] [IsAlgClosure k Ω] (l : ℕ) [Fact l.Prime] (E : IntermediateField ℚ_[l] (PadicAlgCl l)) [FiniteDimensional ℚ_[l] E] (ψ : G k Ω →* (PadicAlgCl l)ˣ), IsOpen (ψ.ker : Set (G k Ω)) → (∀ g, (ψ g : PadicAlgCl l) ∈ E) →
    ∀ e : ℕ, 1 ≤ e → ∀ θ : G k Ω → PadicAlgCl l, (∀ g, θ g * (ψ g : PadicAlgCl l) * algebraMap ℤ_[l] (PadicAlgCl l) (cycZ k Ω l g : ℤ_[l]) ^ e = 1) →
    ∀ c : G k Ω → PadicAlgCl l, Continuous c → (∀ g, c g ∈ E) → (∀ g h, c (g * h) = c g + θ g * c h) →
    (∀ A : ValuationSubring Ω, ∃ m, ∀ g ∈ Ine (F := k) A, c g = θ g * m - m) →
    (∀ A : ValuationSubring Ω, A.valuation (l : Ω) < 1 → ∃ m, ∀ g ∈ Dec (F := k) A, c g = θ g * m - m) → ∃ m ∈ E, ∀ g, c g = θ g * m - m := by
  intro CK hK hPT hLF hLT k Ω _ _ _ _ _ l _ E _ ψ hψ hψE e he θ hθ c hc hcE hco hI hD
  obtain ⟨h1, h2, h3⟩ := UpperTheory.V.abelian₂.dvr_intClosure l E
  let O := integralClosure ℤ_[l] E
  have hint : ∀ x : E, IsIntegral ℤ_[l] x ↔ ‖x‖ ≤ 1 := int_iff_norm E.val
  haveI : IsGalois k Ω := {}
  haveI : CompactSpace (G k Ω) := inferInstanceAs (CompactSpace (Ω ≃ₐ[k] Ω))
  haveI : Finite (G k Ω ⧸ ψ.ker) := Subgroup.quotient_finite_of_isOpen _ hψ
  have hidx : ψ.ker.index ≠ 0 := Subgroup.index_ne_zero_of_finite
  have hψ1 : ∀ g, ‖(ψ g : PadicAlgCl l)‖ ≤ 1 := by
    intro g
    have h := MonoidHom.mem_ker.1 (ψ.ker.pow_index_mem g)
    rw [map_pow] at h
    have h' : ‖(ψ g : PadicAlgCl l)‖ ^ ψ.ker.index = 1 := by
      rw [← norm_pow, ← Units.val_pow_eq_pow_val, h, Units.val_one, norm_one]
    exact ((pow_eq_one_iff_of_nonneg (norm_nonneg _) hidx).1 h').le
  let ψ₀ : G k Ω →* O :=
    { toFun := fun g => ⟨⟨ψ g, hψE g⟩, (hint _).2 (hψ1 g)⟩
      map_one' := Subtype.ext (Subtype.ext (by simp))
      map_mul' := fun a b => Subtype.ext (Subtype.ext (by simp)) }
  let ψO : G k Ω →* Oˣ := ψ₀.toHomUnits
  have hker : ψO.ker = ψ.ker := by
    ext g
    simp only [MonoidHom.mem_ker, Units.ext_iff, Subtype.ext_iff]
    rfl
  have hfin := soFin CK hK hPT hLF hLT k Ω l O ψO (hker ▸ hψ) e he
  let ι : O →+* PadicAlgCl l := (algebraMap E (PadicAlgCl l)).comp (algebraMap O E)
  let θO : G k Ω →* Oˣ := ψO⁻¹ * chiO k Ω l O ^ (-(e : ℤ))
  have hθO : ∀ g, ι (θO g : O) = θ g := by
    intro g
    have a1 : θO g * ψO g * chiO k Ω l O g ^ e = 1 := by
      simp only [θO, MonoidHom.mul_apply, MonoidHom.inv_apply, MonoidHom.zpow_apply, zpow_neg, zpow_natCast,
        MonoidHom.pow_apply]
      rw [mul_comm (ψO g)⁻¹, inv_mul_cancel_right, inv_mul_cancel]
    have a2 := congrArg (fun u : Oˣ => ι u) a1
    simp only [Units.val_mul, Units.val_pow_eq_pow_val, map_mul, map_pow, Units.val_one, map_one] at a2
    have a3 : ι (θO g : O) * (ψ g : PadicAlgCl l) * algebraMap ℤ_[l] (PadicAlgCl l) (cycZ k Ω l g : ℤ_[l]) ^ e = 1 := a2
    have a4 := hθ g
    rw [mul_assoc] at a3 a4
    rw [eq_inv_of_mul_eq_one_left a3, eq_inv_of_mul_eq_one_left a4]
  have hsm : ∀ g (x : E), (((θO g : O) • x : E) : PadicAlgCl l) = θ g * x := by
    intro g x
    rw [← hθO]
    rfl
  haveI : IsLocalization (Algebra.algebraMapSubmonoid O ℤ_[l]⁰) E := IsIntegralClosure.isLocalization ℤ_[l] ℚ_[l] E O
  obtain ⟨π, hs, hk⟩ := qo_proj l O E
  have hk' : ∀ x, π x = 0 ↔ ‖x‖ ≤ 1 := fun x =>
    (hk x).trans ⟨fun ⟨o, ho⟩ => (hint x).1 (ho ▸ o.2), fun h => ⟨⟨x, (hint x).2 h⟩, rfl⟩⟩
  have hπ : Continuous π := by
    refine continuous_of_continuousAt_zero π ?_
    refine (continuousAt_const (y := (0 : QO l O))).congr ?_
    filter_upwards [Metric.closedBall_mem_nhds (0 : E) one_pos] with x hx
    exact ((hk' x).2 (by simpa using hx)).symm
  have hl1 : ‖algebraMap O E (l : O)‖ < 1 := by
    have : ‖algebraMap O E (l : O)‖ = ‖algebraMap ℚ_[l] (PadicAlgCl l) l‖ := by
      rw [map_natCast, map_natCast]
      rfl
    rw [this, norm_algebraMap']
    exact Padic.norm_p_lt_one
  have hl0 : algebraMap O E (l : O) ≠ 0 := by
    rw [map_natCast]
    exact Nat.cast_ne_zero.2 (Fact.out : l.Prime).ne_zero
  have hlm : (l : O) ∈ IsLocalRing.maximalIdeal O := by
    rintro ⟨u, hu⟩
    have b1 : ‖algebraMap O E ((u⁻¹ : Oˣ) : O)‖ ≤ 1 := (hint _).1 ((u⁻¹ : Oˣ) : O).2
    have b2 : ‖algebraMap O E (l : O)‖ * ‖algebraMap O E ((u⁻¹ : Oˣ) : O)‖ = 1 := by
      rw [← norm_mul, ← map_mul, ← hu, Units.mul_inv, map_one, norm_one]
    exact absurd b2 (mul_lt_one_of_nonneg_of_lt_one_left (norm_nonneg _) hl1 b1).ne
  have hθE : ∀ g, θ g ∈ E := fun g => hθO g ▸ ((θO g : O) : E).2
  have hE : ∀ (D : Subgroup (G k Ω)) (m : PadicAlgCl l), (∀ g ∈ D, c g = θ g * m - m) →
      ∃ m' : E, ∀ g ∈ D, (⟨c g, hcE g⟩ : E) = (θO g : O) • m' - m' := by
    intro D m hm
    by_cases h : ∀ g ∈ D, θ g = 1
    · refine ⟨0, fun g hg => Subtype.ext ?_⟩
      simp [hm g hg, h g hg]
    push Not at h
    obtain ⟨g₀, hg₀, h⟩ := h
    have hmE : m ∈ E := by
      have : m = c g₀ / (θ g₀ - 1) := by
        rw [hm g₀ hg₀, eq_div_iff (sub_ne_zero.2 h)]
        ring
      rw [this]
      exact div_mem (hcE _) (sub_mem (hθE _) (one_mem _))
    refine ⟨⟨m, hmE⟩, fun g hg => Subtype.ext ?_⟩
    rw [AddSubgroupClass.coe_sub, hsm]
    exact hm g hg
  obtain ⟨m, hm⟩ := core π hs hπ (fun x => (hk' x).1) (Chr.rho l e ψO) (fun g => (θO g : O)) (fun _ _ => rfl)
    (shaFam k Ω l) hfin hlm hl0 hl1 (fun g => ⟨c g, hcE g⟩) (hc.subtype_mk _)
    (fun g h => Subtype.ext (by rw [AddMemClass.coe_add, hsm]; exact hco g h)) (by
      rintro D (⟨A, hA, rfl⟩ | ⟨A, rfl⟩)
      · obtain ⟨m, hm⟩ := hD A hA
        exact hE _ m hm
      · obtain ⟨m, hm⟩ := hI A
        exact hE _ m hm)
  refine ⟨m, m.2, fun g => ?_⟩
  have := congrArg Subtype.val (hm g)
  rw [AddSubgroupClass.coe_sub, hsm] at this
  exact this
end

