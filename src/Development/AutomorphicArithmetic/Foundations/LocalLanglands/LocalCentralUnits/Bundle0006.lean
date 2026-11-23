module

public import Development.AutomorphicArithmetic.Foundations.LocalLanglands.RecTTransport
public import Mathlib
public import Development.DiscreteGroups.GlobalIrreducibility.Bundle0007
public import Development.DiscreteGroups.GlobalIrreducibility.Bundle0017
public import Development.AutomorphicArithmetic.Foundations.LocalLanglands.LocalCentralUnits.WDBasic
public import Development.AutomorphicArithmetic.Foundations.LocalLanglands.LocalCentralUnits.ClBasic
public import Development.AutomorphicArithmetic.Foundations.LocalLanglands.LocalCentralUnits.TwTame
public import Development.AutomorphicArithmetic.Foundations.LocalLanglands.LocalCentralUnits.Bundle0003
public import Development.AutomorphicArithmetic.Foundations.LocalLanglands.LocalCentralUnits.Bundle0004
public import Development.AutomorphicArithmetic.Foundations.LocalLanglands.LocalCentralUnits.NameLaws
public import Development.AutomorphicArithmetic.Foundations.LocalLanglands.LocalCentralUnits.FinrankK
public import Development.AutomorphicArithmetic.Foundations.LocalLanglands.LocalCentralUnits.Bundle0001
public import Development.WeilBound.CoreStatements.AutomorphicKernels.DepthZeroCuspidal.IsTateEpsUnramTwist
public import Development.WeilBound.CoreStatements.AutomorphicKernels.DepthZeroCuspidal.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0139
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0026
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0680

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.Foundations.LocalLanglands.LocalCentralUnits.NormEqProd
section
noncomputable section

open NumberField IsDedekindDomain ValuativeRel Matrix Polynomial Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.WeilDeligne GlobalTheory.LocGL GlobalTheory.LocLanglands GlobalTheory.GLq
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace UpperTheory.Zero.LLC

private theorem exists_red {E : Type} [Field E] [NumberField E] {w : HeightOneSpectrum (𝓞 E)} {g : ℕ} [Fact g.Prime]
    (i : ℚ_[g] ≃+* w.adicCompletion E) (hi : Continuous i) (χ : (w.adicCompletion E)ˣ →* ℂˣ) (ht : TameChar χ) :
    ∃ χ₀ : (ZMod g)ˣ →* ℂˣ, ∀ (u : ℤ_[g]ˣ) (x : (w.adicCompletion E)ˣ),
      (x : w.adicCompletion E) = i ((u : ℤ_[g]) : ℚ_[g]) →
      χ x = χ₀ (Units.map (PadicInt.toZMod (p := g)).toMonoidHom u) := by
  let f : ℤ_[g]ˣ →* (ZMod g)ˣ := Units.map (PadicInt.toZMod (p := g)).toMonoidHom
  have hloc : IsLocalHom (PadicInt.toZMod (p := g)) := ⟨fun a ha => by
    by_contra hna
    have h1 : a ∈ IsLocalRing.maximalIdeal ℤ_[g] := hna
    rw [← PadicInt.ker_toZMod, RingHom.mem_ker] at h1
    rw [h1] at ha
    exact not_isUnit_zero ha⟩
  have hf : Function.Surjective f :=
    IsLocalRing.surjective_units_map_of_local_ringHom (PadicInt.toZMod (p := g)) (ZMod.ringHom_surjective _) hloc
  let φ : ℤ_[g]ˣ →* (w.adicCompletion E)ˣ :=
    Units.map ((i.toRingHom.comp (algebraMap ℤ_[g] ℚ_[g])).toMonoidHom)
  let c : ℤ_[g]ˣ →* ℂˣ := χ.comp φ
  have hker : f.ker ≤ c.ker := by
    intro u hu
    have h0 : PadicInt.toZMod ((u : ℤ_[g]) - 1) = 0 := by
      have h1 : f u = 1 := hu
      have h2 : PadicInt.toZMod (u : ℤ_[g]) = 1 := congrArg Units.val h1
      rw [map_sub, h2, map_one, sub_self]
    have h3 : (u : ℤ_[g]) - 1 ∈ IsLocalRing.maximalIdeal ℤ_[g] := by
      rw [← PadicInt.ker_toZMod, RingHom.mem_ker]
      exact h0
    have h4 : ‖(u : ℤ_[g]) - 1‖ < 1 := PadicInt.mem_nonunits.1 h3
    refine ht (φ u) ?_
    have h5 : ((φ u : (w.adicCompletion E)ˣ) : w.adicCompletion E) - 1 = i (((u : ℤ_[g]) - 1 : ℤ_[g]) : ℚ_[g]) := by
      show i ((u : ℤ_[g]) : ℚ_[g]) - 1 = _
      rw [PadicInt.coe_sub, map_sub, PadicInt.coe_one, map_one]
    rw [h5]
    exact (DiscreteGroups.sglob.DzIso.valuation_lt_iff i hi _).2 (by rwa [← PadicInt.norm_def])
  refine ⟨MonoidHom.liftOfSurjective f hf ⟨c, hker⟩, fun u x hx => ?_⟩
  have hxu : x = φ u := Units.ext hx
  rw [hxu]
  exact (MonoidHom.liftOfRightInverse_comp_apply f _ (Function.rightInverse_surjInv hf) ⟨c, hker⟩ u).symm

private theorem norm_eq_prod {g : ℕ} [Fact g.Prime] {n : ℕ} {K : Type} [Field K] [Algebra (ZMod g) K]
    (hK : Nat.card K = g ^ n) (hn : 0 < n) (z : Kˣ) :
    algebraMap (ZMod g) K (Algebra.norm (ZMod g) (z : K)) = ∏ j ∈ Finset.range n, ((z ^ g ^ j : Kˣ) : K) := by
  have hg : 2 ≤ g := (Fact.out : g.Prime).two_le
  haveI : Finite K := Nat.finite_of_card_ne_zero (by rw [hK]; exact pow_ne_zero _ (by omega))
  rw [FiniteField.algebraMap_norm_eq_pow, hK, Nat.card_zmod]
  simp only [Units.val_pow_eq_pow_val]
  rw [Finset.prod_pow_eq_pow_sum, Nat.geomSum_eq hg]

private theorem inflates_tw {E : Type} [Field E] [NumberField E] {w : HeightOneSpectrum (𝓞 E)} {g : ℕ} [Fact g.Prime]
    (i : ℚ_[g] ≃+* w.adicCompletion E) {n : ℕ} (σ : IrrRep (GL (Fin n) (w.adicCompletion E))) (τ : FDRep ℂ (Gn g n))
    (χ₀ : (ZMod g)ˣ →* ℂˣ) (χ : (w.adicCompletion E)ˣ →* ℂˣ) (hχs : IsSmoothChar χ)
    (hl : ∀ (u : ℤ_[g]ˣ) (x : (w.adicCompletion E)ˣ), (x : w.adicCompletion E) = i ((u : ℤ_[g]) : ℚ_[g]) →
      χ x = χ₀ (Units.map (PadicInt.toZMod (p := g)).toMonoidHom u))
    (hσ : GlobalTheory.SerSys.TameGen.Inflates (σ.ρ.comp (GeneralLinearGroup.map i.toRingHom)) τ) :
    GlobalTheory.SerSys.TameGen.Inflates
      ((irrTwist σ (detChar (Fin n) χ) (hχs.detChar (n := Fin n))).ρ.comp (GeneralLinearGroup.map i.toRingHom))
      (DiscreteGroups.sglob.DzTw.twFD τ χ₀) := by
  have hdet : ∀ k : GL (Fin n) ℤ_[g],
      χ (GeneralLinearGroup.det (GeneralLinearGroup.map i.toRingHom (GlobalTheory.GLp.inc g n k))) =
        χ₀ (GeneralLinearGroup.det (GlobalTheory.GLp.red g n k)) := by
    intro k
    rw [hl (GeneralLinearGroup.det k) _ ?_]
    · congr 1
      refine Units.ext ?_
      show PadicInt.toZMod ((k : Matrix (Fin n) (Fin n) ℤ_[g]).det) =
        ((GlobalTheory.GLp.red g n k : Matrix (Fin n) (Fin n) (ZMod g))).det
      exact RingHom.map_det _ _
    · show (i.toRingHom.mapMatrix ((algebraMap ℤ_[g] ℚ_[g]).mapMatrix (k : Matrix (Fin n) (Fin n) ℤ_[g]))).det =
        i.toRingHom ((algebraMap ℤ_[g] ℚ_[g]) (k : Matrix (Fin n) (Fin n) ℤ_[g]).det)
      rw [RingHom.map_det, RingHom.map_det]
  obtain ⟨φ, hφ0, hφ⟩ := hσ
  refine ⟨φ, hφ0, fun k v => ?_⟩
  show φ ((((detChar (Fin n) χ₀ (GlobalTheory.GLp.red g n k)) : ℂˣ) : ℂ) • τ.ρ (GlobalTheory.GLp.red g n k) v) =
    (((detChar (Fin n) χ (GeneralLinearGroup.map i.toRingHom (GlobalTheory.GLp.inc g n k))) : ℂˣ) : ℂ) •
      σ.ρ (GeneralLinearGroup.map i.toRingHom (GlobalTheory.GLp.inc g n k)) (φ v)
  rw [map_smul, hφ k v, detChar_apply, detChar_apply, hdet k, MonoidHom.comp_apply]

end UpperTheory.Zero.LLC

open UpperTheory.Zero.LLC in
theorem UpperTheory.Zero.LLC.parTw : UpperTheory.Zero.LLC.ParTw := by
  intro E Ω _ _ _ _ _ A w h a ha g _ i hi y hy hdz V hV χ hχ ht
  haveI : CharZero (w.adicCompletion E) := charZero_of_injective_ringHom (f := i.toRingHom) i.injective
  obtain ⟨⟨ω₀, -, hω₀, -⟩, htw, h1, -⟩ := clBasic (w.adicCompletion E) y
  obtain ⟨⟨ω₁, -, -, huniq⟩, -⟩ := clBasic (w.adicCompletion E) (y.tw χ hχ)
  obtain ⟨hd, -, -, hmul, hcen⟩ := htw χ hχ
  have hB := wDBasic E Ω A w h V
  obtain ⟨-, -, -, hirr, -, -, -, hine, hT⟩ := hB
  obtain ⟨hTd, hTi, hTe, -, -, -, hTt, -⟩ := hT (χ.comp a) (ha.smooth hχ)
  have hI : IsIrrWD (V.lpTwist (χ.comp a) (ha.smooth hχ)) := hTi hV.irr
  refine ⟨hI, ?_, ?_, ?_, ?_⟩
  · rw [hTd, hV.dim, hd]
  · exact hTt (fun σ hσ => (tameArt E Ω A w h a ha χ hχ).1 ht σ hσ) hV.tame
  · intro ω hω σ
    have e1 : ω = ω₀ * χ ^ y.1 := (huniq ω hω).trans (huniq _ (hcen ω₀ hω₀)).symm
    rw [hTe, hV.central ω₀ hω₀ σ, hV.dim, e1]
    simp
  · intro g' _ i' hi' n hn D R hR θ hθ τ hτ hN σ hσ hinf
    obtain ⟨χ₀, hχ₀⟩ := exists_red i' hi' χ ht
    have hrank : Module.finrank (ZMod g') D.K = n := ((resEx E Ω A w h g' i' hi' n hn D).2 R hR).rank
    have hK : Nat.card D.K = g' ^ n := by
      haveI : Module.Finite (ZMod g') D.K := Module.finite_of_finrank_pos (by omega)
      rw [Module.natCard_eq_pow_finrank (K := ZMod g'), Nat.card_zmod, hrank]
    have hχi : IsSmoothChar χ⁻¹ := IsSmoothChar.inv hχ
    have hl : ∀ (u : ℤ_[g']ˣ) (x : (w.adicCompletion E)ˣ), (x : w.adicCompletion E) = i' ((u : ℤ_[g']) : ℚ_[g']) →
        χ⁻¹ x = χ₀⁻¹ (Units.map (PadicInt.toZMod (p := g')).toMonoidHom u) := by
      intro u x hx
      rw [MonoidHom.inv_apply, MonoidHom.inv_apply, hχ₀ u x hx]
    have hcl : cls (irrTwist σ (detChar (Fin n) χ⁻¹) (hχi.detChar (n := Fin n))) = y := by
      have e1 : cls (irrTwist σ (detChar (Fin n) χ⁻¹) (hχi.detChar (n := Fin n))) = (cls σ).tw χ⁻¹ hχi :=
        Sigma.ext rfl (heq_of_eq (clTwist_cl σ _ _).symm)
      have e2 : ∀ (c : (w.adicCompletion E)ˣ →* ℂˣ) (hc : IsSmoothChar c), c = 1 → y.tw c hc = y := by
        rintro c hc rfl
        exact h1 hc
      have hs : IsSmoothChar (χ * χ⁻¹) := IsSmoothChar.mul hχ hχi
      rw [e1, hσ, hmul χ⁻¹ hχi hs]
      exact e2 _ hs (mul_inv_cancel χ)
    have hty := hV.type g' i' hi' n hn D R hR (θ * DiscreteGroups.sglob.DzType.nmChar D.K χ₀⁻¹)
      (DiscreteGroups.sglob.DzTw.isRegularChar_mul D.K χ₀⁻¹ hθ) (DiscreteGroups.sglob.DzTw.twFD τ χ₀⁻¹)
      (DiscreteGroups.sglob.DzTw.isCusp_twFD τ χ₀⁻¹ hτ) (DiscreteGroups.sglob.DzTw.char_twFD D.K hK hn χ₀⁻¹ θ τ hN)
      (irrTwist σ (detChar (Fin n) χ⁻¹) (hχi.detChar (n := Fin n))) hcl
      (inflates_tw i' σ τ χ₀⁻¹ χ⁻¹ hχi hl hinf)
    refine ⟨((wDBasic E Ω A w h _).2.2.2.1 hI).1, fun t => ?_⟩
    have hval : χ (a (ineIncl h t)) = DiscreteGroups.sglob.DzType.nmChar D.K χ₀ (R t) := by
      obtain ⟨u, hu, hun⟩ := resBase E Ω A w h a ha g' i' hi' n hn D R hR t
      rw [hχ₀ u _ hu]
      show χ₀ _ = χ₀ _
      congr 1
      refine Units.ext ((algebraMap (ZMod g') D.K).injective ?_)
      show algebraMap (ZMod g') D.K (PadicInt.toZMod (u : ℤ_[g'])) = algebraMap (ZMod g') D.K (Algebra.norm (ZMod g') (R t : D.K))
      rw [hun, norm_eq_prod hK hn]
    have hpoint : ∀ j : ℕ, ((θ * DiscreteGroups.sglob.DzType.nmChar D.K χ₀⁻¹) (R t ^ g' ^ j) * (χ.comp a) (ineIncl h t) : ℂˣ) = θ (R t ^ g' ^ j) := by
      intro j
      have e3 : DiscreteGroups.sglob.DzType.nmChar D.K χ₀⁻¹ (R t ^ g' ^ j) * DiscreteGroups.sglob.DzType.nmChar D.K χ₀ (R t) = 1 := by
        have e4 : DiscreteGroups.sglob.DzType.nmChar D.K χ₀⁻¹ = (DiscreteGroups.sglob.DzType.nmChar D.K χ₀)⁻¹ := rfl
        have e5 : DiscreteGroups.sglob.DzType.nmChar D.K χ₀ (R t ^ g' ^ j) = DiscreteGroups.sglob.DzType.nmChar D.K χ₀ (R t) := by
          rw [map_pow, ← MonoidHom.pow_apply, DiscreteGroups.sglob.DzTw.nmChar_pow]
        rw [e4, MonoidHom.inv_apply, e5, inv_mul_cancel]
      rw [MonoidHom.mul_apply, MonoidHom.comp_apply, hval, mul_assoc, e3, mul_one]
    have hm2 := hine t ((Finset.range n).val.map fun j => (θ * DiscreteGroups.sglob.DzType.nmChar D.K χ₀⁻¹) (R t ^ g' ^ j))
      (by
        simp only [bind_pure_comp, Multiset.fmap_def, Multiset.map_map]
        exact hty.2 t)
    rw [hm2.2.2 (χ.comp a) (ha.smooth hχ), Multiset.map_map]
    refine congrArg Multiset.prod (Multiset.map_congr rfl fun j _ => ?_)
    simp only [Function.comp_apply]
    rw [hpoint j]
end
end

-- bundled from Development.AutomorphicArithmetic.Foundations.LocalLanglands.LocalCentralUnits.ParOne
section
noncomputable section

open NumberField IsDedekindDomain ValuativeRel Matrix Polynomial Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.WeilDeligne GlobalTheory.LocGL GlobalTheory.LocLanglands GlobalTheory.GLq
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.GLp

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace UpperTheory.Zero.LLC

section Fin

private theorem charpoly_one {R : Type} [CommRing R] (M : Matrix (Fin 1) (Fin 1) R) :
    M.charpoly = X - C (M 0 0) := by
  rw [Matrix.charpoly, Matrix.det_fin_one, Matrix.charmatrix_apply_eq]

private theorem smul_of_finrank_one {V : Type} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    (hV : Module.finrank ℂ V = 1) (f : V →ₗ[ℂ] V) (v : V) : f v = LinearMap.trace ℂ V f • v := by
  obtain ⟨b, hb, hall⟩ := finrank_eq_one_iff'.1 hV
  obtain ⟨c, hc⟩ := hall (f b)
  have hf : f = c • LinearMap.id := by
    refine LinearMap.ext fun x => ?_
    obtain ⟨d, rfl⟩ := hall x
    simp [hc.symm, smul_smul, mul_comm]
  have ht : LinearMap.trace ℂ V f = c := by
    rw [hf, map_smul, LinearMap.trace_id, hV]; simp
  rw [ht, hf]; simp

end Fin

section Key

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

private theorem fixed_ne_bot_of_equiv {G V W : Type} [Group G] [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
    {ρ : Representation ℂ G V} {σ : Representation ℂ G W} (e : ρ.Equiv σ) {H : Subgroup G} {v : V}
    (hv : ∀ u ∈ H, ρ u v = v) (h0 : v ≠ 0) : fixed σ H ≠ ⊥ := by
  refine (Submodule.ne_bot_iff _).2 ⟨e.toIntertwiningMap v, GlobalTheory.Parabolic.mem_fixed.2 fun u hu => ?_, fun h1 => ?_⟩
  · rw [← e.toIntertwiningMap.isIntertwining, hv u hu]
  · have h2 : e.toLinearEquiv v = 0 := h1
    exact h0 (e.toLinearEquiv.injective (h2.trans (map_zero _).symm))

private theorem dz_one : DZ (IrrGL.ofChar (1 : kˣ →* ℂˣ) isSmoothChar_one) :=
  fixed_ne_bot_of_equiv (equivRep (IrrRep.det (k := k) (Fin 1) 1 isSmoothChar_one)) (v := (1 : ℂ))
    (fun u _ => by
      show (((1 : kˣ →* ℂˣ) (GeneralLinearGroup.det u) : ℂˣ) : ℂ) • (1 : ℂ) = 1
      simp) (one_ne_zero (α := ℂ))

variable {g : ℕ} [Fact g.Prime] {K : Type} [Field K] [Algebra (ZMod g) K]

private theorem character_one {θ : Kˣ →* ℂˣ} {τ : FDRep ℂ (Gn g 1)} (hN : Names g 1 θ τ) :
    Module.finrank ℂ τ = 1 := by
  have h1 := hN 1 (by rw [charpoly_one]; exact irreducible_X_sub_C _) 1 (by rw [charpoly_one]; simp)
  rw [FDRep.char_one] at h1
  simp at h1
  exact_mod_cast h1

private theorem val_of_inflates {i : ℚ_[g] ≃+* k} {θ : Kˣ →* ℂˣ} {τ : FDRep ℂ (Gn g 1)} (hN : Names g 1 θ τ)
    {σ : IrrRep (GL (Fin 1) k)} {χ : kˣ →* ℂˣ} {hχ : IsSmoothChar χ} (e : σ.ρ.Equiv (IrrRep.det (Fin 1) χ hχ).ρ)
    (hinf : GlobalTheory.SerSys.TameGen.Inflates (σ.ρ.comp (GeneralLinearGroup.map i.toRingHom)) τ)
    (u : ℤ_[g]ˣ) (z : Kˣ) (hz : algebraMap (ZMod g) K (PadicInt.toZMod (u : ℤ_[g])) = z) (x : kˣ)
    (hx : (x : k) = i ((u : ℤ_[g]) : ℚ_[g])) : χ x = θ z := by
  obtain ⟨φ, hφ0, hφ⟩ := hinf
  obtain ⟨v, hv⟩ : ∃ v, φ v ≠ 0 := by
    by_contra hc
    push_neg at hc
    exact hφ0 (LinearMap.ext hc)
  set c : GL (Fin 1) ℤ_[g] := GeneralLinearGroup.scalar (Fin 1) u with hc
  have hy0 : ((red g 1 c : Gn g 1) : Mt g 1) 0 0 = PadicInt.toZMod (u : ℤ_[g]) := by
    simp [red, hc, GeneralLinearGroup.scalar]
  have hd : GeneralLinearGroup.det (GeneralLinearGroup.map i.toRingHom (inc g 1 c)) = x := by
    ext
    rw [hx]
    simp [inc, hc, GeneralLinearGroup.scalar]
  have hσ : ∀ (t : GL (Fin 1) k) (y : σ.V), σ.ρ t y = (χ (GeneralLinearGroup.det t) : ℂ) • y := by
    intro t y
    apply e.toLinearEquiv.injective
    have h1 : e.toIntertwiningMap (σ.ρ t y) = (IrrRep.det (Fin 1) χ hχ).ρ t (e.toIntertwiningMap y) := by
      rw [← e.toIntertwiningMap.isIntertwining]
    refine h1.trans ?_
    rw [map_smul]
    rfl
  have hτ : τ.character (red g 1 c) = ((θ z : ℂˣ) : ℂ) := by
    have := hN (red g 1 c) (by rw [charpoly_one]; exact irreducible_X_sub_C _) z
      (by rw [charpoly_one, hy0]; simp [hz])
    simpa using this
  have h2 := hφ c v
  rw [smul_of_finrank_one (character_one hN) (τ.ρ (red g 1 c)) v, map_smul] at h2
  have h3 : LinearMap.trace ℂ τ (τ.ρ (red g 1 c)) = ((θ z : ℂˣ) : ℂ) := hτ
  rw [h3] at h2
  have h4 : (σ.ρ.comp (GeneralLinearGroup.map i.toRingHom)) (inc g 1 c) (φ v) = ((χ x : ℂˣ) : ℂ) • φ v := by
    rw [MonoidHom.comp_apply, hσ, hd]
  rw [h4] at h2
  exact (Units.ext (smul_left_injective ℂ hv h2)).symm

end Key

variable {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
  {A : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 E)} {h : IsPlaceOver A w}

private theorem irr_lpOfChar (ξ : Weil h →* ℂˣ) (hξ : IsSmooth ξ) : IsIrrWD (WD.lpOfChar h ξ hξ) := by
  refine ⟨1, WDRep.ofChars h (ι := Fin 1) (fun _ => ξ) (fun _ => hξ), rfl, ?_⟩
  have h1 : (WDRep.ofChars h (ι := Fin 1) (fun _ => ξ) (fun _ => hξ)).ρ =
      GlobalTheory.FiniteGL.lineRep ((Units.coeHom ℂ).comp ξ) := by
    refine MonoidHom.ext fun σ => LinearMap.ext fun v => funext fun i => ?_
    simp [GlobalTheory.FiniteGL.lineRep_apply, diagEnd_apply]
  rw [h1]
  exact GlobalTheory.FiniteGL.lineRep_isIrreducible _

private theorem dim_lpOfChar (ξ : Weil h →* ℂˣ) (hξ : IsSmooth ξ) : (WD.lpOfChar h ξ hξ).lpDim = 1 := by
  simp [WD.lpOfChar]

private theorem dual_lpOfChar {ξ ξ' : Weil h →* ℂˣ} (hξ : IsSmooth ξ) (hξ' : IsSmooth ξ') (e : ∀ σ, ξ' σ = (ξ σ)⁻¹) :
    (WD.lpOfChar h ξ hξ).lpDual = WD.lpOfChar h ξ' hξ' := by
  rw [WD.lpOfChar, WD.lpDual_mk, WD.lpOfChar]
  refine WD.sound ⟨(Pi.basisFun ℂ (Fin 1)).dualBasis.equivFun, fun σ f => ?_, fun f => ?_⟩
  · funext i
    simp [Module.Basis.dualBasis_equivFun, diagEnd_apply, e]
    have h1 : (diagEnd fun _ : Fin 1 => ((ξ σ : ℂ))⁻¹) (Pi.single i 1) = ((ξ σ : ℂ))⁻¹ • (Pi.single i 1 : Fin 1 → ℂ) := by
      funext j
      simp [diagEnd_apply]
    rw [h1, map_smul, smul_eq_mul]
  · funext i
    simp

private theorem typeAt_ofChar {a : Weil h →* (w.adicCompletion E)ˣ} (ha : IsLocalArtin h a)
    (χ : (w.adicCompletion E)ˣ →* ℂˣ) (hχ : IsSmoothChar χ) :
    TypeAt (IrrGL.ofChar χ hχ) (WD.lpOfChar h (χ.comp a) (ha.smooth hχ)) := by
  intro g _ i hi n hn D R hR θ hθ τ hτ hN σ hcl hinf
  obtain rfl : n = 1 := congrArg Sigma.fst hcl
  obtain ⟨e⟩ : Nonempty (σ.ρ.Equiv (IrrRep.det (Fin 1) χ hχ).ρ) :=
    IrrRep.cl_eq_iff.1 (sigma_mk_injective (β := fun n => IrrCl (GL (Fin n) (w.adicCompletion E))) hcl)
  refine ⟨(WD.monodromyZero_ofWeilDeligneRepClass_iff _).2 rfl, fun t => ?_⟩
  obtain ⟨u, hu, hu'⟩ := resBase E Ω A w h a ha g i hi 1 one_pos D R hR t
  have hz : algebraMap (ZMod g) D.K (PadicInt.toZMod (u : ℤ_[g])) = (R t : D.Kˣ) := by
    rw [hu']; simp
  have key := val_of_inflates hN e hinf u (R t) hz (a (ineIncl h t)) hu
  rw [WD.inePol_of_mem_Ine _ t.2, WD.lpOfChar, WD.charPol_mk, WDRep.ofChars_ρ, charpoly_diagEnd]
  simp [key]

end UpperTheory.Zero.LLC

open UpperTheory.Zero.LLC in
theorem UpperTheory.Zero.LLC.parOne :
    UpperTheory.Zero.LLC.ParOne := by
  intro E Ω _ _ _ _ _ A w h a ha χ hχ
  haveI : CharZero (w.adicCompletion E) := charZero_of_injective_algebraMap (algebraMap E _).injective
  have hdz : DZ (IrrGL.ofChar χ hχ) ↔ TameChar χ := by
    have h1 := twTame _ (IrrGL.ofChar 1 isSmoothChar_one) χ hχ one_pos dz_one
    rwa [IrrGL.tw_ofChar, IrrGL.ofChar_inj.2 (one_mul χ)] at h1
  have heig : ∀ σ, ((WD.lpOfChar h (χ.comp a) (ha.smooth hχ)).eig σ).prod = (χ (a σ) : ℂ) := fun σ => by
    rw [eig_lpOfChar]; simp
  have hcc := GlobalTheory.LocLanglands.ExtTwist.hasCentralChar_ofChar χ hχ
  refine ⟨irr_lpOfChar _ _, dim_lpOfChar _ _, hcc, heig, hdz, fun ht => ⟨irr_lpOfChar _ _, dim_lpOfChar _ _, ?_, ?_, typeAt_ofChar ha χ hχ⟩,
    fun χ' hχ' h'' => ⟨IrrGL.tw_ofChar _ _ _ _, ?_⟩, fun h'' => ⟨?_, ?_⟩, fun χ' hχ' e => IrrGL.ofChar_inj.1 e⟩
  · exact (PositivityTheory.LocalParametersCuspidal.DZC.tame_lpOfChar_iff _ _).2 ((tameArt E Ω A w h a ha χ hχ).1 ht)
  · intro ω hω σ
    obtain ⟨ω₀, -, -, hu⟩ := (clBasic _ (IrrGL.ofChar χ hχ)).1
    rw [heig, hu ω hω, hu χ hcc]
  · exact PositivityTheory.LocalParametersCuspidal.DepthZeroGlueing.lpOfChar_lpTwist _ _ _ fun σ => rfl
  · exact GlobalTheory.LocLanglands.CuspModel.dualCl_ofChar _ _ _ _ rfl
  · exact dual_lpOfChar _ _ fun σ => rfl

end
end

