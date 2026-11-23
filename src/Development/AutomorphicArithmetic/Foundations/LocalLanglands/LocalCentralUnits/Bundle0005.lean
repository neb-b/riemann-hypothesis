module

public import Development.AutomorphicArithmetic.Foundations.LocalLanglands.RecTTransport
public import Development.AutomorphicArithmetic.Foundations.LocalLanglands.LocalCentralUnits.TypeEx
public import Development.AutomorphicArithmetic.Foundations.LocalLanglands.LocalCentralUnits.NameLaws
public import Development.AutomorphicArithmetic.Foundations.LocalLanglands.LocalCentralUnits.Bundle0002
public import Development.AutomorphicArithmetic.Foundations.LocalLanglands.LocalCentralUnits.Bundle0003
public import Development.AutomorphicArithmetic.Foundations.LocalLanglands.LocalCentralUnits.FinrankK
public import Development.AutomorphicArithmetic.Foundations.LocalLanglands.LocalCentralUnits.Bundle0004
public import Development.AutomorphicArithmetic.Foundations.LocalLanglands.LocalCentralUnits.IsSemisimpleInducedParam
public import Development.AutomorphicArithmetic.Foundations.LocalLanglands.LocalCentralUnits.WDBasic
public import Development.AutomorphicArithmetic.Foundations.LocalLanglands.LocalCentralUnits.ClBasic
public import Development.AutomorphicArithmetic.Foundations.LocalLanglands.LocalCentralUnits.Bundle0001
public import Development.AutomorphicArithmetic.Foundations.LocalLanglands.Multi
public import Development.WeilBound.RepresentationTheoryGL.UnitaryDualProof.GenericIrreducibility.NormEqOneOfIsUnitarisableU
public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0025
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0699
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.RecTransportFieldIso
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0731
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0205
public import GroundTheory.GlobalFields.TateThesis.RootNumberLocalFinite
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0753
public import GroundTheory.LocalFields.Bundle0014
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0668
public import Development.WeilBound.CoreStatements.AutomorphicKernels.LanglandsExhaustion.Bundle0003
public import Development.AutomorphicArithmetic.Foundations.LocalLanglands.LocalCentralUnits.DetByType

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.Foundations.LocalLanglands.LocalCentralUnits.CentralUnit
section
noncomputable section

open NumberField IsDedekindDomain ValuativeRel Matrix Polynomial Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.WeilDeligne GlobalTheory.LocGL GlobalTheory.LocLanglands GlobalTheory.GLq
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace UpperTheory.Zero.LLC

section Pure

private def eta {I K : Type} [Group I] [Field K] (g n : ℕ) (R : I →* Kˣ) (θ : Kˣ →* ℂˣ) (j : ℤ) : I →* ℂˣ :=
  (θ ^ g ^ (j % (n : ℤ)).toNat).comp R

private theorem eta_apply {I K : Type} [Group I] [Field K] (g n : ℕ) (R : I →* Kˣ) (θ : Kˣ →* ℂˣ) (j : ℤ) (t : I) :
    eta g n R θ j t = θ (R t) ^ g ^ (j % (n : ℤ)).toNat := by
  simp [eta, MonoidHom.pow_apply]

end Pure

section Scalars

end Scalars

theorem parEx : ParEx := by
  intro E Ω _ _ _ _ _ A w h a ha g _ i hi y hy hdz
  haveI : CharZero (HeightOneSpectrum.adicCompletion E w) :=
    (RingHom.charZero_iff (ϕ := i.toRingHom) i.injective).1 inferInstance
  obtain ⟨n, c⟩ := y
  have hcls : GlobalTheory.LocLanglands.cls c.rep = (⟨n, c⟩ : IrrGL (k := _)) := by
    simp [GlobalTheory.LocLanglands.cls, IrrCl.cl_rep]
  obtain ⟨⟨ω, -, hω, hωu⟩, -, -, hpos, -⟩ := clBasic _ (⟨n, c⟩ : IrrGL (k := _))
  have hn : 0 < n := hpos hy
  obtain ⟨φ, hφ⟩ := deg_surjective (h := h) 1
  rw [← hcls] at hy hdz
  obtain ⟨hτc, hτu⟩ := typeEx E Ω A w h g i hi n hn c.rep
  obtain ⟨τ, hτ, hτi⟩ := hτc hy hdz
  obtain ⟨D⟩ := extEx E Ω A w h g i hi n hn
  obtain ⟨⟨R, hR⟩, hRs⟩ := resEx E Ω A w h g i hi n hn D
  have hT := hRs R hR
  have hrank := hT.rank
  haveI : Module.Finite (ZMod g) D.K := Module.finite_of_finrank_pos (by omega)
  haveI : Finite D.K := Module.finite_of_finite (ZMod g)
  letI : Fintype D.K := Fintype.ofFinite _
  have hcard : Fintype.card D.K = g ^ n := by
    rw [Module.card_eq_pow_finrank (K := ZMod g), ZMod.card, hrank]
  have hfix : ∀ x : D.Kˣ, x ^ g ^ n = x := fun x => Units.ext (by
    rw [Units.val_pow_eq_pow_val, ← hcard, FiniteField.pow_card])
  have hper : ∀ (x : D.Kˣ) (q r : ℕ), x ^ g ^ (n * q + r) = x ^ g ^ r := by
    intro x q r
    induction q with
    | zero => simp
    | succ q ih => rw [show n * (q + 1) + r = n + (n * q + r) by ring, pow_add, pow_mul, hfix, ih]
  have hmod : ∀ (x : D.Kˣ) (m : ℕ), x ^ g ^ m = x ^ g ^ (m % n) := by
    intro x m
    conv_lhs => rw [← Nat.div_add_mod m n]
    exact hper x _ _
  have hcong : ∀ (x : D.Kˣ) (p q : ℕ), (p : ℤ) ≡ q [ZMOD n] → x ^ g ^ p = x ^ g ^ q := by
    intro x p q hpq
    have h1 : ((p % n : ℕ) : ℤ) = ((q % n : ℕ) : ℤ) := by push_cast; exact hpq
    rw [hmod x p, hmod x q, (by exact_mod_cast h1 : p % n = q % n)]
  obtain ⟨hNex, hNuniq, -, hNtr⟩ := nameLaws g n hn D.K hrank
  obtain ⟨θ, hθr, hθN⟩ := hNex τ hτ
  have hnz : (0 : ℤ) < n := by exact_mod_cast hn
  have hex : ∀ j : ℤ, (((j % (n : ℤ)).toNat : ℕ) : ℤ) = j % n := fun j =>
    Int.toNat_of_nonneg (Int.emod_nonneg _ hnz.ne')
  have hexlt : ∀ j : ℤ, (j % (n : ℤ)).toNat < n := by
    intro j
    have h1 := hex j
    have h2 := Int.emod_lt_of_pos j hnz
    omega
  have heta : ∀ (j : ℤ) (t : ↥(Ine A)), eta g n R θ j t = θ (R t ^ g ^ (j % (n : ℤ)).toNat) := by
    intro j t
    rw [eta_apply, map_pow]
  have hopen : IsOpen (SetLike.coe (eta g n R θ 0).ker) := by
    refine Subgroup.isOpen_mono ?_ hT.isOpen
    intro t ht
    rw [MonoidHom.mem_ker] at ht ⊢
    rw [heta, ht, one_pow, map_one]
  have hshift : ∀ (j : ℤ) (t t' : ↥(Ine A)), (ineIncl h) t' = φ * (ineIncl h) t * φ⁻¹ →
      eta g n R θ j t' = eta g n R θ (j + 1) t := by
    intro j t t' ht
    rw [heta, heta, hT.frob φ t t' hφ ht, ← pow_mul, ← pow_succ']
    congr 1
    apply hcong
    push_cast [hex]
    exact ((Int.mod_modEq j n).add_right 1).trans (Int.mod_modEq (j + 1) n).symm
  have hinj : ∀ j j' : ℤ, eta g n R θ j = eta g n R θ j' ↔ (n : ℤ) ∣ j - j' := by
    intro j j'
    constructor
    · intro he
      have h1 : θ ^ g ^ (j % (n : ℤ)).toNat = θ ^ g ^ (j' % (n : ℤ)).toNat := by
        refine MonoidHom.ext fun x => ?_
        obtain ⟨t, rfl⟩ := hT.surj x
        have := congrArg (fun f => f t) he
        simpa [eta_apply, MonoidHom.pow_apply] using this
      have h2 := hθr _ _ (hexlt j) (hexlt j') h1
      have h3 : j % (n : ℤ) = j' % n := by rw [← hex j, ← hex j', h2]
      exact Int.ModEq.dvd (show j' ≡ j [ZMOD n] from h3.symm)
    · intro hd
      have h3 : j % (n : ℤ) = j' % n := (Int.modEq_iff_dvd.mpr hd).symm
      simp only [eta, h3]
  obtain ⟨V, hVirr, hVdim, hVφ, hVine, hVtame⟩ := indEx E Ω A w h φ hφ n hn (eta g n R θ) hopen
    hshift hinj (ω (a φ) : ℂ) (Units.ne_zero _)
  have hInFor : InFor g n R θ V := by
    intro t
    rw [hVine t]
    apply Finset.prod_congr rfl
    intro j hj
    rw [Finset.mem_range] at hj
    have h1 : ((j : ℤ) % (n : ℤ)) = j := Int.emod_eq_of_lt (by omega) (by omega)
    rw [heta, h1, Int.toNat_natCast]
  obtain ⟨⟨δ, hδ⟩, hδu, -, hirr, -, -, -, hm, -⟩ := wDBasic E Ω A w h V
  refine ⟨V, hVirr, hVdim, hVtame ?_, ?_, ?_⟩
  · intro j t ht
    rw [heta, hT.wild t ht, one_pow, map_one]
  · intro ω' hω' σ'
    rw [hωu ω' hω']
    have hNC := nameCentral g n hn D.K hrank τ θ hτ hθr hθN
    obtain ⟨ψ, hψ0, hψ⟩ := hτi
    obtain ⟨v, hv⟩ : ∃ v, ψ v ≠ 0 := by
      by_contra hcon
      push_neg at hcon
      exact hψ0 (LinearMap.ext hcon)
    have hcent : ∀ t : ↥(Ine A), θ (∏ j ∈ Finset.range n, R t ^ g ^ j) = ω (a (ineIncl h t)) := by
      intro t
      obtain ⟨u, hu1, hu2⟩ := resBase E Ω A w h a ha g i hi n hn D R hR t
      have key := hψ (GeneralLinearGroup.scalar (Fin n) u) v
      have hred : GlobalTheory.GLp.red g n (GeneralLinearGroup.scalar (Fin n) u) =
          GeneralLinearGroup.scalar (Fin n) (Units.map (PadicInt.toZMod : ℤ_[g] →+* ZMod g).toMonoidHom u) := by
        ext p q
        by_cases hpq : p = q <;> simp [GlobalTheory.GLp.red, GeneralLinearGroup.scalar, Matrix.diagonal_apply, hpq]
      set z : (HeightOneSpectrum.adicCompletion E w)ˣ :=
        Units.map (i.toRingHom.comp PadicInt.Coe.ringHom).toMonoidHom u with hz
      have hinc : GeneralLinearGroup.map i.toRingHom (GlobalTheory.GLp.inc g n (GeneralLinearGroup.scalar (Fin n) u)) =
          GeneralLinearGroup.scalar (Fin n) z := by
        ext p q
        by_cases hpq : p = q <;> simp [GlobalTheory.GLp.inc, GeneralLinearGroup.scalar, Matrix.diagonal_apply, hpq, z] <;> rfl
      rw [hred, MonoidHom.comp_apply, hinc, hNC, map_smul] at key
      rw [hω z (ψ v)] at key
      have heq := smul_left_injective ℂ hv key
      have hzeq : a (ineIncl h t) = z := Units.ext (by rw [hu1]; simp [z] <;> rfl)
      have hpeq : ∏ j ∈ Finset.range n, R t ^ g ^ j = Units.map (algebraMap (ZMod g) D.K : ZMod g →* D.K)
          (Units.map (PadicInt.toZMod : ℤ_[g] →+* ZMod g).toMonoidHom u) := Units.ext (by simp [hu2])
      rw [hzeq, hpeq]
      exact Units.ext heq
    have hδeq : δ = ω.comp a := by
      apply hδu φ δ (ω.comp a) hφ
      · apply Units.ext
        rw [← hδ, hVφ]
        rfl
      · intro t
        apply Units.ext
        rw [← hδ, MonoidHom.comp_apply, ← hcent, map_prod]
        have hpol : V.inePol ↑t = (Multiset.map (fun z => X - C z)
            (do let b ← Multiset.map (fun j => θ (R t ^ g ^ j)) (Multiset.range n); pure (b : ℂ))).prod := by
          rw [hInFor t]
          simp [Finset.prod_eq_multiset_prod, Multiset.map_map]
        rw [(hm t _ hpol).1]
        simp [Finset.prod_eq_multiset_prod]
    rw [hδ σ', hδeq]
    rfl
  · intro g' _ i' hi' n' hn' D' R' hR' θ' hθ'r τ' hτ' hN' σ' hσ' hinfl'
    obtain ⟨hgg, hii⟩ := isoUniq _ g g' i i' hi hi'
    subst g'
    have hi2 : i' = i := hii i' hi'
    subst i'
    have hnn : n' = n := congrArg Sigma.fst hσ'
    subst n'
    have hchar := hτu σ' τ τ' (hσ'.trans hcls.symm) hτ hτ' hτi hinfl'
    have hNτ : Names g n θ' τ := by
      simpa only [Names, hchar] using hN'
    obtain ⟨e, he⟩ := resIndep E Ω A w h g i hi n hn D D' R R' hR hR'
    obtain ⟨hN2, hr2⟩ := hNtr D'.K e τ θ'
    obtain ⟨j, -, hj⟩ := hNuniq τ θ _ hθr (hr2 hθ'r) hθN (hN2 hNτ)
    have hI := (tameUniq E Ω A w h g n D.K R hT θ hθr V hInFor).1 j
    rw [← hj] at hI
    refine ⟨(hirr hVirr).1, fun t => ?_⟩
    rw [hI t]
    apply Finset.prod_congr rfl
    intro k _
    congr 3
    simp only [MonoidHom.comp_apply]
    congr 1
    apply Units.ext
    simp [he t]

end UpperTheory.Zero.LLC

end
end

-- bundled from Development.AutomorphicArithmetic.Foundations.LocalLanglands.LocalCentralUnits.ExponentMulAbsPow
section
noncomputable section

open NumberField IsDedekindDomain ValuativeRel Matrix Polynomial Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.WeilDeligne GlobalTheory.LocGL GlobalTheory.LocLanglands GlobalTheory.GLq
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace UpperTheory.Zero.LLC

section Abs

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

private theorem nabs_eq_residue (z : kˣ) :
    nabs k z = (GroundTheory.LocalField.residueCard k : ℝ) ^ (-GroundTheory.LocalField.ord (z : k)) := by
  rw [GlobalTheory.LGrp.nabs_eq_zpow]
  rfl

private theorem norm_smooth_char {χ : kˣ →* ℂˣ} (hχ : IsSmoothChar χ) (z : kˣ) :
    ‖(χ z : ℂ)‖ = nabs k z ^ GroundTheory.LocalField.quasiCharExponent χ := by
  have hc : Continuous χ := by
    refine continuous_def.2 fun U _ => isOpen_iff_forall_mem_open.2 fun x hx => ?_
    refine ⟨(fun y => x⁻¹ * y) ⁻¹' (χ.ker : Set kˣ), fun y hy => ?_,
      hχ.preimage (continuous_const_mul _), by simp⟩
    have h : χ (x⁻¹ * y) = 1 := hy
    rw [map_mul, map_inv, inv_mul_eq_one] at h
    show χ y ∈ U
    rw [← h]
    exact hx
  rw [GroundTheory.LocalField.norm_quasiChar_apply hc z,
    GroundTheory.LocalField.modulus_of_ne_zero z.ne_zero, nabs_eq_residue]
  simp

private theorem exponent_mul_absPow {χ χ' : kˣ →* ℂˣ} (hχ : IsSmoothChar χ) (hχ' : IsSmoothChar χ') (d : ℕ) (s : ℝ)
    (e : χ' = χ * absPow k (s : ℂ) ^ d) :
    GroundTheory.LocalField.quasiCharExponent χ' = GroundTheory.LocalField.quasiCharExponent χ + d * s := by
  subst e
  have hq : (1 : ℝ) < GroundTheory.LocalField.residueCard k := by
    exact_mod_cast GroundTheory.LocalField.one_lt_residueCard
  have hL := Real.log_pos hq
  have h1 : GroundTheory.LocalField.ord ((GroundTheory.LocalField.unifUnit k : kˣ) : k) = 1 := by
    simpa using GroundTheory.LocalField.ord_unifUnit_zpow (K := k) 1
  have hlog : Real.log (nabs k (GroundTheory.LocalField.unifUnit k)) =
      -Real.log (GroundTheory.LocalField.residueCard k) := by
    rw [nabs_eq_residue, h1, Real.log_zpow]
    push_cast
    ring
  have hpos := GlobalTheory.SmGL.nabs_pos' k (GroundTheory.LocalField.unifUnit k)
  have ha : ‖((χ (GroundTheory.LocalField.unifUnit k) : ℂˣ) : ℂ)‖ ≠ 0 := by
    simp
  unfold GroundTheory.LocalField.quasiCharExponent
  rw [MonoidHom.mul_apply, MonoidHom.pow_apply, Units.val_mul, Units.val_pow_eq_pow_val,
    val_absPow_ofReal, norm_mul, norm_pow, Complex.norm_real, Real.norm_of_nonneg (Real.rpow_nonneg hpos.le _)]
  have hb : (nabs k (GroundTheory.LocalField.unifUnit k) ^ s) ^ d ≠ 0 :=
    pow_ne_zero _ (Real.rpow_pos_of_pos hpos _).ne'
  simp only [Real.logb]
  rw [Real.log_mul ha hb, Real.log_pow, Real.log_rpow hpos, hlog]
  field_simp
  ring

end Abs

theorem expo : Expo := by
  intro E Ω _ _ _ _ _ A w h a ha
  let ω₀ : IrrGL (k := HeightOneSpectrum.adicCompletion E w) → ((HeightOneSpectrum.adicCompletion E w)ˣ →* ℂˣ) :=
    fun y => Classical.choose (clBasic (HeightOneSpectrum.adicCompletion E w) y).1
  have hω₀ : ∀ y, IsSmoothChar (ω₀ y) ∧ HasCentralChar y.rep (ω₀ y) ∧
      ∀ ω', HasCentralChar y.rep ω' → ω' = ω₀ y :=
    fun y => Classical.choose_spec (clBasic (HeightOneSpectrum.adicCompletion E w) y).1
  refine ⟨fun y => GroundTheory.LocalField.quasiCharExponent (ω₀ y) / y.fst, ?_⟩
  intro x hx
  have hn : (x.fst : ℝ) ≠ 0 := by exact_mod_cast hx.ne'
  constructor
  · intro s
    have hc := PositivityTheory.RgUd.UOrder.hasCentralChar_nu_u x (hω₀ x).2.1 (s : ℂ)
    have heq := (hω₀ (x.nu (s : ℂ))).2.2 _ hc
    have hfst : (x.nu (s : ℂ)).fst = x.fst := by
      unfold IrrGL.nu
      exact ((clBasic _ x).2.1 _ _).1
    have hsm : IsSmoothChar (ω₀ x * absPow (HeightOneSpectrum.adicCompletion E w) (s : ℂ) ^ x.fst) := by
      rw [heq]
      exact (hω₀ _).1
    show GroundTheory.LocalField.quasiCharExponent (ω₀ (x.nu (s : ℂ))) / ((x.nu (s : ℂ)).fst : ℝ) =
      GroundTheory.LocalField.quasiCharExponent (ω₀ x) / x.fst + s
    rw [← heq, hfst, exponent_mul_absPow (hω₀ x).1 hsm x.fst s rfl]
    field_simp
  · intro ω hω J hJ hunit σ
    have hωeq := (hω₀ x).2.2 ω hω
    subst hωeq
    obtain ⟨-, -, -, -, -, -, -, -, hξ⟩ := wDBasic E Ω A w h J
    unfold GlobalTheory.WeilDeligne.WD.lpTw
    rw [(hξ _ _).2.2.1 σ, norm_mul, norm_pow, hunit σ, one_mul, hJ, ← ha.absPow_comp,
      MonoidHom.comp_apply, val_absPow_ofReal, Complex.norm_real,
      Real.norm_of_nonneg (Real.rpow_nonneg (GlobalTheory.SmGL.nabs_pos' _ _).le _),
      norm_smooth_char (hω₀ x).1, ← Real.rpow_natCast, ← Real.rpow_mul (GlobalTheory.SmGL.nabs_pos' _ _).le,
      div_mul_cancel₀ _ hn]

end UpperTheory.Zero.LLC

end
end

-- bundled from Development.AutomorphicArithmetic.Foundations.LocalLanglands.LocalCentralUnits.GoodSeg
section
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.LocLanglands

theorem UpperTheory.Zero.LLC.goodSeg :
    UpperTheory.Zero.LLC.GoodSeg := by
  intro k _ _ _ _ _
  have huniq : ∀ (x : IrrGL (k := k)) (s s' : Multiset (IrrGL (k := k))),
      HasSupport x.rep s → HasSupport x.rep s' → s = s' :=
    fun x s s' hs hs' =>
      GlobalTheory.CompanionTheory.Hypotheses₂.TD.hasSupport_unique PositivityTheory.Exh.geometricLemmaGL UpperTheory.Zero.LLC.Pr.bz hs hs'
  have hgood : ∀ (x : IrrGL (k := k)) (s : Multiset (IrrGL (k := k))), HasSupport x.rep s →
      (UpperTheory.Zero.LLC.Good x ↔ ∀ y ∈ s, UpperTheory.Zero.LLC.GoodCusp y) := by
    intro x s hs
    unfold UpperTheory.Zero.LLC.Good
    constructor
    · rintro ⟨t, ht, hy⟩
      rw [huniq x s t hs ht]
      exact hy
    · intro hy
      exact ⟨s, hs, hy⟩
  have htw : ∀ (y : IrrGL (k := k)) (a : ℂ),
      UpperTheory.Zero.LLC.GoodCusp (y.nu a) ↔ UpperTheory.Zero.LLC.GoodCusp y := by
    intro y a
    unfold IrrGL.nu
    exact ((UpperTheory.Zero.LLC.clBasic k y).2.1 _ _).2.2.1
  refine ⟨?_, ?_, huniq⟩
  · intro l x hl
    rw [hgood x _ (hasSupport_msupp_of_isL UpperTheory.Zero.LLC.Pr.zel k _ x hl)]
    unfold msupp
    constructor
    · intro h Δ hΔ
      have hmem : Δ.first.nu ((0 : ℕ) : ℂ) ∈ Δ.ms :=
        Segment.mem_ms.mpr (Segment.mem_carrier.mpr ⟨0, Δ.len_pos, rfl⟩)
      have hc := h _ (Multiset.mem_bind.mpr ⟨Δ, Multiset.mem_coe.mpr hΔ, hmem⟩)
      exact (htw _ _).mp hc
    · intro h y hy
      obtain ⟨Δ, hΔ, hy⟩ := Multiset.mem_bind.mp hy
      obtain ⟨a, _, rfl⟩ := Segment.mem_carrier.mp (Segment.mem_ms.mp hy)
      exact (htw _ _).mpr (h Δ (Multiset.mem_coe.mp hΔ))
  · intro x hx
    rw [hgood x {x} (hasSupport_self hx)]
    simp
end

-- bundled from Development.AutomorphicArithmetic.Foundations.LocalLanglands.LocalCentralUnits.ParUniq
section
open NumberField IsDedekindDomain ValuativeRel Matrix Polynomial Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.WeilDeligne GlobalTheory.LocGL GlobalTheory.LocLanglands GlobalTheory.GLq
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

theorem UpperTheory.Zero.LLC.parUniq :
    UpperTheory.Zero.LLC.ParUniq := by
  intro E Ω _ _ _ _ _ A w h a ha g _ i hi y hy hdz V hV
  obtain ⟨n, c⟩ := y
  have hn : 0 < n := hy.1
  have hcl : GlobalTheory.LocLanglands.cls c.rep = (⟨n, c⟩ : IrrGL (k := HeightOneSpectrum.adicCompletion E w)) :=
    IrrGL.of_rep ⟨n, c⟩
  obtain ⟨D⟩ := UpperTheory.Zero.LLC.extEx E Ω A w h g i hi n hn
  obtain ⟨⟨R, hR⟩, hRT⟩ := UpperTheory.Zero.LLC.resEx E Ω A w h g i hi n hn D
  have hT := hRT R hR
  obtain ⟨τ, hτ, hinf⟩ := (UpperTheory.Zero.LLC.typeEx E Ω A w h g i hi n hn c.rep).1
    (by rw [hcl]; exact hy) (by rw [hcl]; exact hdz)
  obtain ⟨hNex, -, hNchar, -⟩ := UpperTheory.Zero.LLC.nameLaws g n hn D.K hT.rank
  obtain ⟨θ, hθ, hθτ⟩ := hNex τ hτ
  have hIF : ∀ W : WD h, UpperTheory.Zero.LLC.Par a ⟨n, c⟩ W → UpperTheory.Zero.LLC.InFor g n R θ W :=
    fun W hW => (hW.type g i hi n hn D R hR θ hθ τ hτ hθτ c.rep hcl hinf).2
  obtain ⟨ω, -, hω, -⟩ := (UpperTheory.Zero.LLC.clBasic _ (⟨n, c⟩ : IrrGL (k := _))).1
  obtain ⟨-, hθu, hVu⟩ := UpperTheory.Zero.LLC.tameUniq E Ω A w h g n D.K R hT θ hθ V (hIF V hV)
  refine ⟨fun V' hV' => hVu V' hV.irr hV'.irr hV.tame hV'.tame (hIF V' hV')
    (fun s => by rw [hV.central ω hω s, hV'.central ω hω s]), ?_⟩
  rintro ⟨m, c'⟩ hy' hdz' hV'
  have hm : m = n := hV'.dim.symm.trans hV.dim
  subst m
  have hcl' : GlobalTheory.LocLanglands.cls c'.rep = (⟨n, c'⟩ : IrrGL (k := HeightOneSpectrum.adicCompletion E w)) :=
    IrrGL.of_rep ⟨n, c'⟩
  obtain ⟨τ', hτ', hinf'⟩ := (UpperTheory.Zero.LLC.typeEx E Ω A w h g i hi n hn c'.rep).1
    (by rw [hcl']; exact hy') (by rw [hcl']; exact hdz')
  obtain ⟨θ', hθ', hθτ'⟩ := hNex τ' hτ'
  have hIF' : UpperTheory.Zero.LLC.InFor g n R θ' V :=
    (hV'.type g i hi n hn D R hR θ' hθ' τ' hτ' hθτ' c'.rep hcl' hinf').2
  obtain ⟨j, -, rfl⟩ := hθu θ' hIF'
  have hch : τ'.character = τ.character := hNchar τ τ' θ j hτ hτ' hθ hθτ hθτ'
  obtain ⟨ω', -, hω', -⟩ := (UpperTheory.Zero.LLC.clBasic _ (⟨n, c'⟩ : IrrGL (k := _))).1
  have hωω : ω' = ω := by
    ext z
    obtain ⟨s, rfl⟩ := ha.surj z
    exact (hV'.central ω' hω' s).symm.trans (hV.central ω hω s)
  subst ω'
  have hdet := UpperTheory.Zero.LLC.detByType E Ω A w h g i hi n hn c.rep c'.rep τ τ' ω hτ hch hinf hinf' hω hω'
  exact hcl'.symm.trans (hdet.trans hcl)
end

