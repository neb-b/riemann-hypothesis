module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.DiscreteSeriesCoefficientsCuspidal
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.AutomorphyLifting.SubquotientSupport.Bundle0002
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.Bundle0003
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.Bundle0004
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.AutomorphyLifting.PolarizedLinkage.ExtraV
public import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.Bundle0032
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.Bundle0009
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.AfLocal
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.Bundle0016
public import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.NearSplit
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.Bundle0006
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.AutomorphyLifting.PrimeIndexConstruction.Bundle0005
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AdmissibleResidues.ArithmeticPointDecomposition
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.WeilDeligneUnramified.WeilCharpolySupport.Bundle0001
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.Bundle0040
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.AutomorphyLifting.Bundle0003

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.IsSubquotientOfHasSupport
section
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 200000

section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Polynomial ValuativeRel GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.LocGL GlobalTheory.GalOfCusp GlobalTheory.SmGL GlobalTheory.SplitWeil UpperTheory.V.Hi
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
private theorem eq_one_of_charpoly_dvd {V : Type} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    (f : Module.End ℂ V) (hf : f.IsSemisimple) {n : ℕ} (hd : f.charpoly ∣ (X - C 1) ^ n) : f = 1 := by
  obtain ⟨q, hq⟩ := hd
  have h0 := congrArg (Polynomial.aeval f) hq
  rw [map_mul, LinearMap.aeval_self_charpoly, zero_mul, map_pow, map_sub, Polynomial.aeval_X,
    Polynomial.aeval_C] at h0
  have hs : (f - algebraMap ℂ (Module.End ℂ V) 1).IsSemisimple :=
    Module.End.isSemisimple_sub_algebraMap_iff.2 hf
  have := sub_eq_zero.1 (Module.End.eq_zero_of_isNilpotent_isSemisimple ⟨_, h0⟩ hs)
  rwa [map_one] at this
private theorem multiset_eq_of_sum {Γ : Type} [Monoid Γ] (s t : Multiset (Γ →* ℂ))
    (h : ∀ g, (s.map fun f => f g).sum = (t.map fun f => f g).sum) : s = t :=
  _root_.UpperTheory.Reformulated.B.Qf50.multiset_eq_of_sum s t h
section
variable {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
  {A : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 E)} {h : IsPlaceOver A w}
private theorem exists_char {z : WD h} (hz : IsIrrWD z) {n : ℕ} (η : Fin n → Weil h →* ℂˣ)
    (hd : ∀ g, z.charPol g ∣ ∏ j, (X - C (η j g : ℂ))) :
    ∃ (ξ : Weil h →* ℂˣ) (hξ : GlobalTheory.WeilDeligne.IsSmooth ξ), z = WD.lpOfChar h ξ hξ := by
  obtain ⟨m, b, rfl, hirr⟩ := hz
  have hc : ∀ g k, b.ρ g * b.ρ k = b.ρ k * b.ρ g := fun g k => by
    have h1 : b.ρ ((k * g)⁻¹ * (g * k)) = 1 := by
      have h2 := hd ((k * g)⁻¹ * (g * k))
      have h3 : ∀ j, η j ((k * g)⁻¹ * (g * k)) = 1 := fun j => by
        rw [map_mul, map_inv, map_mul, map_mul, mul_comm (η j g), inv_mul_cancel]
      simp only [h3, Units.val_one, Finset.prod_const, WD.charPol_mk] at h2
      exact eq_one_of_charpoly_dvd _ (b.semisimple _) h2
    rw [← map_mul, ← map_mul, ← mul_inv_cancel_left (k * g) (g * k), map_mul, h1, mul_one]
  have hsub : ∀ S : Submodule ℂ (Fin m → ℂ), (∀ g v, v ∈ S → b.ρ g v ∈ S) → S = ⊥ ∨ S = ⊤ := fun S hS => by
    rcases hirr.eq_bot_or_eq_top ⟨S, fun g v hv => hS g v hv⟩ with h | h
    · exact Or.inl (congrArg Subrepresentation.toSubmodule h)
    · exact Or.inr (congrArg Subrepresentation.toSubmodule h)
  haveI : Nontrivial (Fin m → ℂ) := nontrivial_of_irreducible hirr
  have hsc : ∀ g, ∃ c : ℂ, ∀ v, b.ρ g v = c • v := fun g => by
    obtain ⟨c, hcv⟩ := Module.End.exists_eigenvalue (b.ρ g)
    refine ⟨c, fun v => ?_⟩
    rcases hsub (Module.End.eigenspace (b.ρ g) c) (fun k u hu => by
      rw [Module.End.mem_eigenspace_iff] at hu ⊢
      have := LinearMap.congr_fun (hc g k) u
      simp only [Module.End.mul_apply] at this
      rw [this, hu, map_smul]) with h | h
    · exact absurd h (Module.End.hasEigenvalue_iff.mp hcv)
    · exact Module.End.mem_eigenspace_iff.mp (h ▸ Submodule.mem_top)
  have hm : m = 1 := by
    obtain ⟨v, hv⟩ := exists_ne (0 : Fin m → ℂ)
    rcases hsub (Submodule.span ℂ {v}) (fun g u hu => by
      obtain ⟨c, h⟩ := hsc g
      rw [h]; exact Submodule.smul_mem _ _ hu) with h | h
    · exact absurd (Submodule.span_singleton_eq_bot.mp h) hv
    · have := finrank_span_singleton (K := ℂ) hv
      rw [h, finrank_top] at this
      simpa using this
  subst hm
  have hsc : ∀ f : Module.End ℂ (Fin 1 → ℂ), ∀ v, f v = f 1 0 • v := fun f v => by
    have hv : v = v 0 • (1 : Fin 1 → ℂ) := by
      funext i; rw [Subsingleton.elim i 0]; simp
    funext i
    rw [Subsingleton.elim i 0]
    conv_lhs => rw [hv, map_smul]
    simp [mul_comm]
  let c : Weil h →* ℂ :=
    { toFun := fun σ => b.ρ σ 1 0
      map_one' := by simp
      map_mul' := fun σ τ => by
        rw [map_mul, Module.End.mul_apply, hsc (b.ρ σ) (b.ρ τ 1)]; simp }
  have hker : ∀ σ, b.ρ σ = 1 → c.toHomUnits σ = 1 := fun σ hσ => by
    ext
    show b.ρ σ 1 0 = 1
    simp [hσ]
  have hN : b.N = 0 := by
    obtain ⟨n, hn⟩ := b.nilpotent
    have e : b.N = b.N 1 0 • (1 : Module.End ℂ (Fin 1 → ℂ)) := LinearMap.ext fun v => by
      rw [hsc b.N v]; rfl
    rw [e, _root_.smul_pow, one_pow] at hn
    have := congrFun (LinearMap.congr_fun hn 1) 0
    have h2 : b.N 1 0 ^ n = 0 := by simpa using this
    rw [e, pow_eq_zero_iff'.mp h2 |>.1, zero_smul]
  refine ⟨c.toHomUnits, b.smooth.of_le hker, ?_⟩
  refine WD.sound ⟨LinearEquiv.refl _ _, fun σ v => ?_, fun v => ?_⟩
  · funext i
    rw [WDRep.ofChars_ρ, diagEnd_apply, LinearEquiv.refl_apply, LinearEquiv.refl_apply, hsc (b.ρ σ) v]
    rfl
  · simp [hN]
variable {a : Weil h →* (w.adicCompletion E)ˣ} {ha : IsLocalArtin h a} {ε : EpsFamily A}
  {rc : IrrGL (k := w.adicCompletion E) → WD h}
private theorem charPol_ofChar (H : UpperTheory.V.Z.Win.LawsV a ha ε rc) (χ : (w.adicCompletion E)ˣ →* ℂˣ) (hχ : IsSmoothChar χ)
    (g : Weil h) : (rc (IrrGL.ofChar χ hχ)).charPol g = X - C (χ (a g) : ℂ) := by
  rw [H.one, WD.lpOfChar, WD.charPol_mk, WDRep.ofChars_ρ, charpoly_diagEnd]
  simp
private theorem hasSupport_iff (hZ : GlobalTheory.Published.ZelevinskyPolynomialRing) (H : UpperTheory.V.Z.Win.LawsV a ha ε rc)
    (x : IrrGL (k := w.adicCompletion E)) {n : ℕ} (ω : Fin n → (w.adicCompletion E)ˣ →* ℂˣ)
    (hω : ∀ i, IsSmoothChar (ω i)) :
    HasSupport x.rep (Finset.univ.val.map fun i => IrrGL.ofChar (ω i) (hω i)) ↔
      ∀ g, (rc x).charPol g = ∏ j, (X - C (ω j (a g) : ℂ)) := by
  refine ⟨fun hs g => ?_, fun hp => ?_⟩
  · rw [H.supp x _ hs g, Multiset.map_map, Finset.prod_eq_multiset_prod]
    exact congrArg Multiset.prod (Multiset.map_congr rfl fun i _ => charPol_ofChar H _ _ g)
  obtain ⟨s, hs⟩ := SupportRing.exists_hasSupport hZ x
  have hch : ∀ y ∈ s, ∃ χ hχ, IrrGL.ofChar χ hχ = y := fun y hy => by
    obtain ⟨ξ, hξ, e⟩ := exists_char ((H.cusp y).1 (hs.isCusp hy)) (fun j => (ω j).comp a) fun g => by
      refine Dvd.dvd.trans ?_ (hp g).dvd
      rw [H.supp _ s hs g]
      exact Multiset.dvd_prod (Multiset.mem_map_of_mem (fun y => (rc y).charPol g) hy)
    obtain ⟨χ, hχ, rfl⟩ := ha.factor ξ hξ
    have e' := e.trans (H.one χ hχ).symm
    have hy1 : y.1 = 1 := by
      rw [← H.dim y, e', H.dim]
      simp [IrrGL.ofChar]
    have hg : UpperTheory.Zero.LLC.Good y :=
      ⟨{y}, hasSupport_self (hs.isCusp hy), fun u hu => Or.inl (by rwa [Multiset.mem_singleton.1 hu])⟩
    exact ⟨χ, hχ, H.inj _ _ hg e'.symm⟩
  let S := {χ : (w.adicCompletion E)ˣ →* ℂˣ // IsSmoothChar χ}
  let F : S → IrrGL (k := w.adicCompletion E) := fun χ => IrrGL.ofChar χ.1 χ.2
  obtain ⟨t, rfl⟩ : ∃ t : Multiset S, t.map F = s :=
    haveI : CanLift (IrrGL (k := w.adicCompletion E)) S F fun y => ∃ χ, F χ = y := ⟨fun _ hy => hy⟩
    (Multiset.canLift F (fun y => ∃ χ, F χ = y)).prf s fun y hy => by
      obtain ⟨χ, hχ, e⟩ := hch y hy
      exact ⟨⟨χ, hχ⟩, e⟩
  let c : S → (w.adicCompletion E)ˣ →* ℂ := fun χ => (Units.coeHom ℂ).comp χ.1
  have hc : Function.Injective c := fun χ ψ e =>
    Subtype.ext (MonoidHom.ext fun y => Units.ext (DFunLike.congr_fun e y))
  let t' : Multiset S := Finset.univ.val.map fun i => ⟨ω i, hω i⟩
  have htt : t = t' := by
    refine Multiset.map_injective hc (multiset_eq_of_sum _ _ fun y => ?_)
    obtain ⟨g, rfl⟩ := ha.surj y
    have h1 : (((t.map c).map fun f => f (a g)).map fun r => X - C r).prod =
        (((t'.map c).map fun f => f (a g)).map fun r => X - C r).prod := by
      have h2 := (H.supp x _ hs g).symm.trans (hp g)
      simp only [Multiset.map_map, Function.comp_def, t'] at h2 ⊢
      rw [Finset.prod_eq_multiset_prod] at h2
      refine Eq.trans (congrArg Multiset.prod (Multiset.map_congr rfl fun χ _ => ?_)) h2
      exact (charPol_ofChar H χ.1 χ.2 g).symm
    have h3 := congrArg Polynomial.roots h1
    rw [roots_multiset_prod_X_sub_C, roots_multiset_prod_X_sub_C] at h3
    rw [h3]
  rw [htt, Multiset.map_map] at hs
  exact hs
end
private theorem isSubquotient_of_hasSupport (hZ : GlobalTheory.Published.ZelevinskyPolynomialRing) {k : Type} [Field k] [ValuativeRel k]
    [TopologicalSpace k] [IsNonarchimedeanLocalField k] {n : ℕ} (τ : IrrRep (GL (Fin n) k)) (μ : Fin n → kˣ →* ℂˣ)
    (hμ : ∀ i, IsSmoothChar (μ i)) (hs : HasSupport τ.ρ (Finset.univ.val.map fun i => IrrGL.ofChar (μ i) (hμ i))) :
    IsSubquotient τ.ρ (prinSeries μ) := by
  have hd : ∑ i, (IrrGL.ofChar (μ i) (hμ i)).1 = n := by simp [IrrGL.ofChar]
  refine IsSubquotient.trans ?_ (GlobalTheory.SphSeg.isSubquotient_prodIrr_prinSeries _ hd μ hμ fun _ => rfl)
  obtain ⟨Z, Ψ, -, hΨ, -⟩ := hZ k
  have h1 := SupportRing.pos_pc_sub hΨ hs τ.smooth τ.irr
  obtain ⟨hp, ep⟩ := SupportRing.prodIrr_cls hΨ _ hd
  refine SupportRing.isSubquotient_of_clsGL_ne hp τ.smooth τ.irr ?_
  have h2 := h1 (IrrGL.of τ.ρ τ.smooth τ.irr)
  rw [SupportRing.pc_map, ← ep] at h2
  have e1 : ∀ (A : GrothGL k) (y : IrrGL (k := k)), Ψ.symm (Ψ A - SupportRing.bas Ψ y) y = A y - 1 := by
    intro A y
    rw [SupportRing.bas, ← map_sub, Ψ.symm_apply_apply, Finsupp.sub_apply, Finsupp.single_eq_same]
  rw [e1] at h2
  intro h3
  rw [h3] at h2
  exact absurd h2 (by norm_num)
theorem UpperTheory.V.Z.Win.T2.psRec_alt :
    _root_.UpperTheory.V.Hi.psRec_s_ty := by
  intro P L Ω _ _ _ _ _ n w A h a ha rc hrc σ ω hω
  obtain ⟨a', ha', ε, H⟩ := _root_.UpperTheory.V.Z.Win.toV' hrc
  obtain rfl : a' = a := by
    obtain ⟨art, hart⟩ := P.aut.art L Ω
    have hinj := GlobalTheory.ArtinLocalInj.artin_localIdele_injective P.loc.chev L Ω art hart w
    exact MonoidHom.ext fun σ => hinj ((ha'.glob art hart _).trans (ha.glob art hart _).symm)
  haveI : CharZero (w.adicCompletion L) := algebraRat.charZero _
  have hμ : ∀ i, IsSmoothChar (ω i * absPow (w.adicCompletion L) (((n : ℂ) - 1) / 2)) :=
    fun i => (hω i).mul (isSmoothChar_absPow _)
  have e0 : ((n : ℂ) - 1) / 2 + (((1 - (n : ℝ)) / 2 : ℝ) : ℂ) = 0 := by push_cast; ring
  have e1 : ∀ i, (IrrGL.ofChar (ω i) (hω i)).nu (((n : ℂ) - 1) / 2) = IrrGL.ofChar _ (hμ i) := fun i =>
    IrrGL.tw_ofChar _ _ _ _
  rw [← hasSupport_iff P.loc.zel H (algNorm σ) ω hω]
  let τ : IrrRep (GL (Fin n) (w.adicCompletion L)) := ⟨_, σ.ρ, σ.smooth, σ.irred⟩
  constructor
  · intro hs
    have h1 := (hasSupport_of_isSubquotient_prinSeries _ n _ hμ τ hs).of_equiv (IrrGL.equivOf σ.ρ σ.smooth σ.irred)
    have h2 := SupportRing.hasSupport_nu h1 (((1 - (n : ℝ)) / 2 : ℝ) : ℂ)
    simp only [Multiset.map_map, Function.comp_def, ← e1, IrrGL.nu_nu, e0, IrrGL.nu_zero] at h2
    exact h2
  · intro hs
    have h2 := SupportRing.hasSupport_nu hs (((n : ℂ) - 1) / 2)
    have e2 : (algNorm σ).nu (((n : ℂ) - 1) / 2) = IrrGL.of σ.ρ σ.smooth σ.irred := by
      rw [algNorm, IrrGL.nu_nu, add_comm, e0, IrrGL.nu_zero]
    have key : ∀ (x y : IrrGL (k := w.adicCompletion L)) s, x = y → HasSupport x.rep s → HasSupport y.rep s := by
      rintro _ _ _ rfl h; exact h
    have h3 := (key _ _ _ e2 h2).of_equiv (IrrGL.equivOf σ.ρ σ.smooth σ.irred).symm
    simp only [Multiset.map_map, Function.comp_def, e1] at h3
    exact isSubquotient_of_hasSupport P.loc.zel τ _ hμ h3
end
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.LocFixed
section
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 200000

section
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N ValuativeRel
open GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.LocGL GlobalTheory.GalOfCusp
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
private theorem UpperTheory.V.Z.Win.T2.val_lt_one {F : Type} [Field F] [NumberField F] (w : HeightOneSpectrum (𝓞 F)) {M : ℕ}
    (hw : (M : 𝓞 F) ∈ w.asIdeal) : valuation (w.adicCompletion F) (M : w.adicCompletion F) < 1 := by
  have : (Valued.v : Valuation (w.adicCompletion F) (WithZero (Multiplicative ℤ))).Compatible :=
    Valuation.Compatible.ofValuation _
  rw [(isEquiv (valuation (w.adicCompletion F))
    (Valued.v : Valuation (w.adicCompletion F) (WithZero (Multiplicative ℤ)))).lt_one_iff_lt_one]
  have h : Valued.v (((algebraMap (𝓞 F) F (M : 𝓞 F) : F)) : w.adicCompletion F) =
      w.valuation F (algebraMap (𝓞 F) F (M : 𝓞 F)) := HeightOneSpectrum.valuedAdicCompletion_eq_valuation' w _
  have h2 : w.valuation F (algebraMap (𝓞 F) F (M : 𝓞 F)) < 1 := (HeightOneSpectrum.valuation_lt_one_iff_mem w _).mpr hw
  rw [← h] at h2
  have e : (((algebraMap (𝓞 F) F (M : 𝓞 F) : F)) : w.adicCompletion F) = ((M : ℕ) : w.adicCompletion F) := by
    rw [map_natCast]
    exact map_natCast (algebraMap F (w.adicCompletion F)) M
  rwa [e] at h2
private theorem UpperTheory.V.Z.Win.T2.good_ofChar {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] (χ : kˣ →* ℂˣ) (hχ : GlobalTheory.SmGL.IsSmoothChar χ) :
    UpperTheory.Zero.LLC.Good (IrrGL.ofChar χ hχ) :=
  ⟨{IrrGL.ofChar χ hχ}, hasSupport_self (IrrGL.isCusp_ofChar χ hχ), fun y hy => Or.inl (by
    rw [Multiset.mem_singleton.1 hy]
    rfl)⟩
theorem UpperTheory.V.Z.Win.T2.local_fixed_vectors_statement :
    _root_.UpperTheory.V.Af.locFixed_s_ty := by
  intro P F Ω _ _ _ _ _ n M hM w A h rc hrc σ hL
  obtain ⟨a, ha, ε, H⟩ := _root_.UpperTheory.V.Z.Win.toV' hrc
  by_cases hw : (M : 𝓞 F) ∈ w.asIdeal
  · have hv : valuation (w.adicCompletion F) (M : w.adicCompletion F) < 1 := UpperTheory.V.Z.Win.T2.val_lt_one w hw
    have hM0 : (M : w.adicCompletion F) ≠ 0 := by
      rw [← map_natCast (algebraMap F (w.adicCompletion F)), map_ne_zero]
      exact Nat.cast_ne_zero.2 (by omega)
    have hu0 : uniformizer (w.adicCompletion F) ≠ 0 := by simp
    have hv0 : valuation (w.adicCompletion F) (M : w.adicCompletion F) ≠ 0 := by simpa using hM0
    let γ : (ValueGroupWithZero (w.adicCompletion F))ˣ :=
      Units.mk0 (valuation _ (M : w.adicCompletion F) / uniformizer (w.adicCompletion F)) (div_ne_zero hv0 hu0)
    have hlt : ∀ x : ValueGroupWithZero (w.adicCompletion F),
        x < γ ↔ x ≤ valuation _ (M : w.adicCompletion F) := fun x => by
      show x < _ / _ ↔ _
      rw [lt_div_iff₀ (zero_lt_iff.2 hu0)]
      refine ⟨fun h1 => not_lt.1 fun h2 => h1.not_ge ?_, fun h1 => (mul_le_mul_left h1 _).trans_lt
        (mul_lt_of_lt_one_right (zero_lt_iff.2 hv0) uniformizer_lt_one)⟩
      have hx : 0 < x := (zero_lt_iff.2 hv0).trans h2
      rwa [← div_le_iff₀' hx, le_uniformizer_iff, div_lt_one₀ hx]
    have hγ : γ ≤ 1 := by
      show _ / _ ≤ (1 : ValueGroupWithZero (w.adicCompletion F))
      rw [div_le_one₀ (zero_lt_iff.2 hu0), le_uniformizer_iff]
      exact hv
    obtain ⟨s, hs⟩ := GlobalTheory.LocGL.SupportRing.exists_hasSupport P.litN.loc.zel (algNorm σ)
    have hch : ∀ y ∈ s, ∃ χ hχ, y = IrrGL.ofChar χ hχ ∧ ∀ u : (w.adicCompletion F)ˣ,
        valuation (w.adicCompletion F) ((u : w.adicCompletion F) - 1) < γ → χ u = 1 := fun y hy => by
      obtain ⟨ξ, hξ, e, hξ1⟩ := UpperTheory.irreducible_constituent_of_level_weilDeligne_eq_character F Ω w A h M n hM _ (rc y) hL ((H.cusp y).1 (hs.isCusp hy)) fun τ => by
        rw [H.supp _ s hs τ]
        exact Multiset.dvd_prod (Multiset.mem_map_of_mem (fun y => (rc y).charPol τ) hy)
      obtain ⟨χ, hχ, rfl⟩ := ha.factor ξ hξ
      refine ⟨χ, hχ, H.inj _ _ (UpperTheory.V.Z.Win.T2.good_ofChar χ hχ) (e.trans (H.one χ hχ).symm), fun u hu => ?_⟩
      obtain ⟨τ, rfl⟩ := ha.surj u
      have h1 : valuation (w.adicCompletion F) (a τ : w.adicCompletion F) = 1 := by
        have := (valuation (w.adicCompletion F)).map_one_add_of_lt (hu.trans_le (Units.val_le_val.2 hγ))
        simpa using this
      obtain ⟨h2, h3⟩ := UpperTheory.inertia_fixes_roots_of_unity_of_artin_congruence P.litN.aut.art F Ω w A h a ha M hM τ h1 ((hlt _).1 hu)
      exact hξ1 ⟨τ, h2⟩ h3
    have hne := UpperTheory.jacquet_borel_nontrivial_of_character_support P.litN.loc.geo P.litN.loc.zel _ _ _ (algNorm σ).rep s hs fun y hy => by
      obtain ⟨χ, hχ, rfl, -⟩ := hch y hy
      rfl
    obtain ⟨y, hy0, hy⟩ := UpperTheory.jacquet_borel_exists_torus_congruence_fixed P.litN.loc.geo P.litN.loc.zel _ _ _ (algNorm σ).rep s γ hγ hs hch hne
    have hf := UpperTheory.fixed_congruence_ne_bot_of_jacquet_torus_fixed _ _ _ (algNorm σ).rep γ hγ
      ((P.litN.loc.bz _).1 _ _ _ (algNorm σ).2.rep.smooth (algNorm σ).2.rep.irr) y hy0 hy
    refine UpperTheory.hasFixed_of_algNorm_fixed_ne_bot F w n σ _ (fun g hg => (UpperTheory.mem_maximalCompact_and_congruent_of_mem_principalCongruence F w n M g hg).1) ?_
    obtain ⟨v, hv, hv0⟩ := (Submodule.ne_bot_iff _).1 hf
    exact (Submodule.ne_bot_iff _).2 ⟨v, fun g => hv ⟨g.1, fun i j => (hlt _).2 ((UpperTheory.mem_maximalCompact_and_congruent_of_mem_principalCongruence F w n M g.1 g.2).2 i j)⟩, hv0⟩
  · obtain ⟨χ, b, hχ, e, hN, hb⟩ := hL
    have hu : (rc (algNorm σ)).unr := by
      rw [← e, WD.unr_mk]
      refine ⟨hN, fun s => ?_⟩
      rw [hb s]
      simp [fun i => hχ i s (UpperTheory.inertia_fixes_roots_of_unity_prime_to_residue_char F Ω w A h M hw s s.2), Module.End.one_eq_id]
    obtain ⟨v, hv, hv0⟩ := (Submodule.ne_bot_iff _).1 ((H.sph _).2 hu)
    refine UpperTheory.hasFixed_of_algNorm_fixed_ne_bot F w n σ _ (fun g hg => (UpperTheory.mem_maximalCompact_and_congruent_of_mem_principalCongruence F w n M g hg).1) ?_
    exact (Submodule.ne_bot_iff _).2 ⟨v, fun g => hv ⟨g.1, (UpperTheory.mem_maximalCompact_and_congruent_of_mem_principalCongruence F w n M g.1 g.2).1⟩, hv0⟩
end
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.PotentialModularityTower
section
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual Formalism.HC ReciprocityTheory.Gal IsLocalRing Polynomial UpperTheory.V.Base UpperTheory.V.Alg UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement
open GlobalTheory.CuspRep GlobalTheory.GalOfCusp
namespace UpperTheory.V.Ws
namespace Amb
variable {l : ℕ} [Fact l.Prime] (𝔞 : Amb l)
end Amb
variable {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {l : ℕ} [Fact l.Prime] {c : Coef l}
def PurityAtPoints (D : Raw Ω c) (ι : PadicAlgCl l ≃+* ℂ) : Prop :=
  ∀ (𝔞 : Amb l) (e : 𝔞.K ≃+* PadicAlgCl l), 𝔞.IsZero e → ∀ r u, KPair D 𝔞 r u → Star (mapRep 𝔞.toK r) →
    _root_.UpperTheory.GalN.V.PureW ι (mapRep ((e : 𝔞.K →+* _).comp 𝔞.toK) r)
def AutmAlt (D : Raw Ω c) (ι : PadicAlgCl l ≃+* ℂ) : Prop :=
  ∀ (𝔞 : Amb l) (e : 𝔞.K ≃+* PadicAlgCl l), 𝔞.IsZero e → ∀ r u, KPair D 𝔞 r u → Irr (mapRep 𝔞.toK r) →
    _root_.UpperTheory.V.Aut.IsAut4Alt ι (mapRep ((e : 𝔞.K →+* _).comp 𝔞.toK) r)
namespace Tower
variable {D : Raw Ω c} (T : Tower D)
structure IsSeedAlt (ι : PadicAlgCl l ≃+* ℂ) (P : PD T.ι (G T.F Ω) (PadicAlgCl l)) : Prop where
  irr : Irr (P.r.comp T.G'.subtype)
  aut : ∃ (h : Fin 4 → ℤ) (κ : G T.L Ω →* (PadicAlgCl l)ˣ) (π : CuspSub T.L 4) (a : ℤ) (k : ℕ),
    (∀ i : Fin 3, ∃ n : ℤ, 2 ≤ n ∧ h i.castSucc = h i.succ + 2 * n) ∧ T.Wts h P ∧ Continuous κ ∧ 0 < k ∧ Even (a + h 0) ∧
    (∀ A : ValuationSubring Ω, A.valuation (l : Ω) < 1 → ∀ s ∈ Ine (F := T.L) A, (κ s ^ 2 * cycBar T.L Ω l s ^ (-a)) ^ k = 1) ∧
    _root_.UpperTheory.V.Z.Win.Birth.CuspidalRankFourRegularAlgebraicTotallyComplex π ∧ Af.AttC ι (Af.tw (P.r.comp (resLe T.F_le)).toHomUnits κ) π
structure SeedPairAlt (ι : PadicAlgCl l ≃+* ℂ) {c₁ : Coef l} (h : c.O ≤ c₁.O) (Q : PD T.ι (G T.F Ω) c₁.O) : Prop where
  pair : (T.fr ∅).IsPair (inc h) Q
  cont : Q.Cont (maximalIdeal c₁.O)
  res : (T.fr ∅).Res ((residue c₁.O).comp (inc h)) (Q.map (residue c₁.O))
  seed : T.IsSeedAlt ι (Q.map (algebraMap c₁.O (PadicAlgCl l)))
structure PotentialModularityTower (ι : PadicAlgCl l ≃+* ℂ) {c' : Coef l} {h : c.O ≤ c'.O} (X : Space (T.fr ∅) (inc h)) (J : Ideal X.B) : Prop where
  fin : ∃ n : ℕ, maximalIdeal X.B ^ n ≤ J ⊔ (maximalIdeal c'.O).map (algebraMap c'.O X.B) ⊔
    Ideal.span {b | ∃ v i, ∃ s ∈ Ine (F := T.F) (T.pl v), b = X.ψ v i s - 1}
  p1 : ∀ (k : Type) [Field k] [Finite k] [Algebra c'.O k] (y : X.A →ₐ[c'.O] PowerSeries k),
    (∀ b ∈ maximalIdeal X.B, PowerSeries.constantCoeff (y (algebraMap X.B X.A b)) = 0) →
    (∀ b ∈ J, y (algebraMap X.B X.A b) = 0) →
    (∀ v i j, i ≠ j → ∃ s ∈ T.U1 v, y (X.P.ψ v i s) ≠ y (X.P.ψ v j s)) →
    Irr (mapRep ((algebraMap (PowerSeries k) (FractionRing (PowerSeries k))).comp (y : X.A →+* PowerSeries k)) X.P.r) →
    X.LocZero J (y : X.A →+* PowerSeries k)
  seed : ∀ y : X.A →ₐ[c'.O] PadicAlgCl l, T.IsSeedAlt ι (X.P.map (y : X.A →+* PadicAlgCl l)) →
    X.LocZero J (y : X.A →+* PadicAlgCl l)
  pur : ∀ y : X.A →ₐ[c'.O] PadicAlgCl l, (∀ b ∈ J, y (algebraMap X.B X.A b) = 0) →
    T.Wts (fun i => 2 * D.wts4 i) (X.P.map (y : X.A →+* PadicAlgCl l)) →
    ∀ r : G ℚ Ω →* M4 (PadicAlgCl l), r.comp (resQ T.F) = (X.P.map (y : X.A →+* PadicAlgCl l)).r → _root_.UpperTheory.GalN.V.PureW ι r
  aut : ∀ y : X.A →ₐ[c'.O] PadicAlgCl l, (∀ b ∈ J, y (algebraMap X.B X.A b) = 0) →
    T.Wts (fun i => 2 * D.wts4 i) (X.P.map (y : X.A →+* PadicAlgCl l)) →
    ∀ r : G ℚ Ω →* M4 (PadicAlgCl l), r.comp (resQ T.F) = (X.P.map (y : X.A →+* PadicAlgCl l)).r → Continuous r → D.Mult r →
      Irr (r.comp T.L.fixingSubgroup.subtype) → _root_.UpperTheory.V.Aut.IsAut4Alt ι r
end Tower
def SeedIIAlt : Prop :=
  ∀ (Ω : Type) [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] (l : ℕ) [Fact l.Prime] (c : Coef l) (D : Raw Ω c) (T : Tower D),
    Ctx2 D → T.Ok → T.Two → T.Deep → ∀ ι : PadicAlgCl l ≃+* ℂ,
    ∃ (c₁ : Coef l) (h : c.O ≤ c₁.O) (Q : PD T.ι (G T.F Ω) c₁.O), T.SeedPairAlt ι h Q ∧
      Fr.InV (Φ := T.fr ∅) (Q.map (residue c₁.O)) ∧
      (Ent (Q.map (residue c₁.O)).r (-wAl) ∨ (Ent (Q.map (residue c₁.O)).r wBe ∧ Ent (Q.map (residue c₁.O)).r (-wTh)))
def PMExAlt : Prop :=
  ∀ (Ω : Type) [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] (l : ℕ) [Fact l.Prime] (c : Coef l) (D : Raw Ω c) (T : Tower D),
    T.Fit → T.Deep → ∀ ι : PadicAlgCl l ≃+* ℂ, ∃ c₁ : Coef l, ∀ (c' : Coef l) (h : c.O ≤ c'.O), c₁.O ≤ c'.O →
      ∀ X : Space (T.fr ∅) (inc h), ∃ J, T.PotentialModularityTower ι X J
def ProModAlt (D : Raw Ω c) (ι : PadicAlgCl l ≃+* ℂ) (𝔞 : Amb l) (r : G ℚ Ω →* M4 𝔞.V) : Prop :=
  ∃ (T : Tower D) (c' : Coef l) (h : c.O ≤ c'.O) (X : Space (T.fr ∅) (inc h)) (J : Ideal X.B) (y : X.A →+* 𝔞.V)
    (r₁ : G ℚ Ω →* M4 𝔞.V), T.Fit ∧ T.Deep ∧ T.PotentialModularityTower ι X J ∧ y.comp (algebraMap c'.O X.A) = 𝔞.a c' ∧
    (∀ b ∈ maximalIdeal X.B, y (algebraMap X.B X.A b) ∈ maximalIdeal 𝔞.V) ∧ (∀ b ∈ J, y (algebraMap X.B X.A b) = 0) ∧
    IsConj4 (mapRep 𝔞.toK r) (mapRep 𝔞.toK r₁) ∧ (∀ g, IsGSp (𝔞.a c (D.th g)) (r₁ g)) ∧
    r₁.comp (resQ T.F) = (X.P.map y).r ∧
    ∀ v i, ∀ s ∈ Ine (F := T.F) (T.pl v), y (X.P.ψ v i s) = 𝔞.a c (D.ps i (resQ T.F s))
end UpperTheory.V.Ws
end
end
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.PrinSeriesIrreducible
section
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
open NumberField IsDedekindDomain ValuativeRel
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.TypeTwo GlobalTheory.ThetaGL GlobalTheory.LocGL
open GlobalTheory.TypeTwo.PowIrrProof
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
namespace UpperTheory.V.Z.Sym.W
section Loc
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
private theorem prinSeries_irreducible {n : ℕ} (ω : Fin n → kˣ →* ℂˣ) (hω : ∀ i, IsSmoothChar (ω i))
    (h : ∀ i j, ω j ≠ ω i * absPow k 1) : (prinSeries ω).IsIrreducible := by
  let x : Fin n → IrrGL (k := k) := fun i => IrrGL.ofChar (ω i) (hω i)
  have hx : ∀ i, (x i).IsCusp := fun i => IrrGL.isCusp_ofChar _ _
  have hd : ∑ i, (x i).1 = n := by
    show ∑ _i : Fin n, 1 = n
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul, mul_one]
  have hnu : ∀ i j, x j ≠ (x i).nu 1 := fun i j e => by
    simp only [x, IrrGL.nu, IrrGL.tw_ofChar, IrrGL.ofChar_inj] at e
    exact h i j e
  have hP : (prodIrr x hd).IsIrreducible :=
    GlobalTheory.RgGu.Holds.lUnlinkedIrr_holds k n n (fun i => Segment.single (x i) (hx i)) x hd
      (fun i j => GlobalTheory.CompanionTheory.BZPair.not_linked_single (hx i) (hx j) (hnu i j) (hnu j i))
      (fun i => (single_spec (hx i)).2.1)
  let e₀ := Equiv.sigmaUnique (Fin n) fun _ => Fin 1
  obtain ⟨p⟩ := (Placing.parInd_jac_placing k _ _ _ e₀ (stdBlocks (fun i => (x i).1) hd) _).1
    (piTensor fun i => detRep (Fin 1) (ω i))
  have hM : (multiProd e₀ fun i => detRep (Fin 1) (ω i)).IsIrreducible :=
    GlobalTheory.Parabolic.isIrreducible_of_equiv
      (p.trans (multiProdEquiv (stdBlocks (fun i => (x i).1) hd)
        fun i => equivRep (IrrRep.det (Fin 1) (ω i) (hω i)))).symm hP
  haveI := nontrivial_of_irreducible hM
  haveI : Nontrivial (IndSp _ _) := by
    obtain ⟨S, f, hf⟩ := GlobalTheory.PermPrin.isSubquotient_multiProd_prinSeries e₀ ω
    have := hf.nontrivial
    exact Subtype.val_injective.nontrivial (α := S.toSubmodule)
  have equiv_local {G V W : Type} [Group G] [AddCommGroup V] [Module ℂ V] [AddCommGroup W]
      [Module ℂ W] {σ : Representation ℂ G W} {ρ : Representation ℂ G V} (h : IsSubquotient σ ρ)
      [Nontrivial W] (hρ : ρ.IsIrreducible) : Nonempty (ρ.Equiv σ) := by
    obtain ⟨S, f, hf⟩ := h
    obtain ⟨y, hy⟩ := exists_ne (0 : W)
    obtain ⟨v, rfl⟩ := hf y
    haveI : IsSimpleOrder (Subrepresentation ρ) := hρ
    rcases eq_bot_or_eq_top S with rfl | rfl
    · exact absurd (by rw [show v = 0 from Subtype.ext v.2, map_zero]) hy
    let F : ρ.IntertwiningMap σ := f.comp (topEquiv ρ).symm.toIntertwiningMap
    have hs : Function.Surjective F := hf.comp (topEquiv ρ).symm.toLinearEquiv.surjective
    refine ⟨equivOfBijective F ⟨(injective_iff_map_eq_zero _).2 fun x hx => ?_, hs⟩⟩
    rcases eq_bot_or_eq_top F.ker with h | h
    · have : x ∈ F.ker := hx
      rw [h] at this
      exact this
    · have : v.1 ∈ F.ker := by rw [h]; trivial
      exact absurd this hy
  obtain ⟨E⟩ := equiv_local (GlobalTheory.PrinProd.isSubquotient_prinSeries_multiProd k n ω) hM
  exact GlobalTheory.Parabolic.isIrreducible_of_equiv E hM
end Loc
theorem principal_series_of_statement_w : _root_.UpperTheory.V.Z.Sym.W.PsOfAlt := by
  intro _ L _ _ n w τ hT
  haveI : CharZero (w.adicCompletion L) := charZero_of_injective_algebraMap (algebraMap L _).injective
  obtain ⟨ξ, hξ, hs, hu⟩ := GlobalTheory.RoadU.plainTor_exists_chars _ _ hT
  have hs' : HasSupport τ.ρ (GlobalTheory.RoadU.chars ξ hξ) := hs.of_equiv (IrrGL.equivOf τ.ρ τ.smooth τ.irred).symm
  have hmem : ∀ i, IrrGL.ofChar (ξ i) (hξ i) ∈ GlobalTheory.RoadU.chars ξ hξ := fun i =>
    Multiset.mem_map_of_mem _ (Finset.mem_univ i)
  have hne : ∀ i j, ξ j ≠ ξ i * absPow (w.adicCompletion L) 1 := fun i j e => by
    refine hu _ (hmem j) _ (hmem i) ?_
    simp only [IrrGL.nu, IrrGL.tw_ofChar, IrrGL.ofChar_inj]
    exact e
  obtain ⟨hi, hq⟩ := (UpperTheory.Gal.LocD.ofSupport_holds _ n τ.V τ.ρ ξ hξ).1 hs'
  obtain ⟨E⟩ := hq.nonempty_equiv hi (prinSeries_irreducible ξ hξ hne)
  exact ⟨ξ, hξ, ⟨E.symm⟩, fun i j => hne j i⟩
end UpperTheory.V.Z.Sym.W
end
end
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.UniqRec
section
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.LocGL GlobalTheory.WeilDeligne GlobalTheory.LocLanglands UpperTheory.Zero.LLC
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
namespace UpperTheory.V.Z.Win
variable {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
  {A : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 E)}
theorem uniqRec'_alt (_N : _root_.GlobalTheory.Mem.LiteralAutomorphy.LiteratureRankNHypothesis) {h : IsPlaceOver A w} {rc rc' : IrrGL (k := w.adicCompletion E) → WD h}
    (H : IsRecT h rc) (H' : IsRecT h rc') (x : IrrGL (k := w.adicCompletion E)) (g : Good x) : rc x = rc' x :=
  recTUnique E Ω A w h rc rc' H H' x g
end UpperTheory.V.Z.Win
end
end
end

