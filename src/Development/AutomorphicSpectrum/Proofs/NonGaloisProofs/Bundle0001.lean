module

public import Mathlib
public import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
public import Formalism.LocalRingCardinality.AdicCompletionLocal.LocTied
public import Formalism.SharpRestriction.LevelLetterCocycles.WachCoordinates
public import Formalism.SharpRestriction.LevelLetterCocycles.PairedCharacterCondition
public import Formalism.SharpRestriction.LevelLetterCocycles.EmbeddingTypes
public import Formalism.SharpRestriction.LevelLetterCocycles.Bundle0013
public import Formalism.SharpRestriction.LevelLetterCocycles.JointConditionsZpowers.Bundle0005
public import Development.AutomorphicSpectrum.Definitions.NonGaloisLines.TopLine
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.H2EquivOfTorsionCharacter
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0246
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ContinuousFixingSubgroupEquiv
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0019
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0006

@[expose] public section

-- bundled from Development.AutomorphicSpectrum.Proofs.NonGaloisProofs.CupFlipContinuousCocycle
section
open NumberField IsDedekindDomain Formalism Formalism.ConjugateSelfDual Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations Module GlobalTheory.CompanionTheory.LocDual

noncomputable section

namespace GlobalTheory.CompanionTheory.CupFlip

section Top

variable {G : Type} [Group G] [TopologicalSpace G] {Qp LL O : Type} [Field Qp] [Field LL]
    [Algebra Qp LL] [CommRing O] [Algebra O LL] [TopologicalSpace LL] [IsTopologicalRing LL]

theorem continuous_act (A : GRep G Qp LL O) : Continuous fun p : G × A.V => A.ρ p.1 p.2 := by
  have := IsModuleTopology.toContinuousSMul LL A.V
  let b := Module.finBasis LL A.V
  have e : (fun p : G × A.V => A.ρ p.1 p.2) =
      fun p => ∑ i, (b.repr p.2 i) • A.ρ p.1 (b i) := by
    funext p
    have h := congrArg (A.ρ p.1) (b.sum_repr p.2)
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum] at h
    simp only [map_smul] at h
    exact h.symm
  rw [e]
  refine continuous_finsetSum _ fun i _ => ?_
  have h1 : Continuous fun v : A.V => b.coord i v :=
    IsModuleTopology.continuous_of_linearMap (b.coord i)
  exact (h1.comp continuous_snd).smul ((A.cont (b i)).comp continuous_fst)

theorem continuous_pair (A A' : GRep G Qp LL O) (P : A.V →ₗ[LL] A'.V →ₗ[LL] LL) :
    Continuous fun p : A.V × A'.V => P p.1 p.2 := by
  have := IsModuleTopology.toContinuousSMul LL A'.V
  exact IsModuleTopology.continuous_bilinear_of_finite_left P

theorem continuous_cup (A A' : GRep G Qp LL O) (P : A.V →ₗ[LL] A'.V →ₗ[LL] LL) {a : G → A.V}
    {b : G → A'.V} (ha : Continuous a) (hb : Continuous b) : Continuous (cupL A'.ρ P a b) :=
  (continuous_pair A A' P).comp ((ha.comp continuous_fst).prodMk
    ((continuous_act A').comp (continuous_fst.prodMk (hb.comp continuous_snd))))

end Top

section Cup

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    (PD : PeriodData G Qp K₀ K B BdR)
    {LL : Type} [Field LL] [Algebra Qp LL]
    {V V' : Type} [AddCommGroup V] [Module LL V] [AddCommGroup V'] [Module LL V']
    {ρ : Representation LL G V} {ρ' : Representation LL G V'} {P : V →ₗ[LL] V' →ₗ[LL] LL}


omit [TopologicalSpace G] in
theorem char_pair (hd : ∀ g x y, P (ρ g x) (ρ' g y) = ((cycLL PD LL g : LLˣ) : LL) * P x y)
    (g : G) (x : V) (y : V') : charRep (cycLL PD LL) g (P x y) = P (ρ g x) (ρ' g y) := by
  rw [hd]
  rfl

theorem d2_cup (hd : ∀ g x y, P (ρ g x) (ρ' g y) = ((cycLL PD LL g : LLˣ) : LL) * P x y)
    {a : G → V} {b : G → V'} (ha : ∀ g h, a (g * h) = a g + ρ g (a h))
    (hb : ∀ g h, b (g * h) = b g + ρ' g (b h)) :
    ReciprocityTheory.Def.d2 (charRep (cycLL PD LL)) (cupL ρ' P a b) = 0 := by
  funext ⟨g, h, k⟩
  show charRep (cycLL PD LL) g (P (a h) (ρ' h (b k))) - P (a (g * h)) (ρ' (g * h) (b k)) +
    P (a g) (ρ' g (b (h * k))) - P (a g) (ρ' g (b h)) = 0
  rw [char_pair PD hd, ha, hb, map_mul, Module.End.mul_apply]
  simp only [map_add (f := _), LinearMap.add_apply]
  ring

theorem d1_pair (hd : ∀ g x y, P (ρ g x) (ρ' g y) = ((cycLL PD LL g : LLˣ) : LL) * P x y)
    {a : G → V} {b : G → V'} (ha : ∀ g h, a (g * h) = a g + ρ g (a h))
    (hb : ∀ g h, b (g * h) = b g + ρ' g (b h)) :
    ReciprocityTheory.Def.d1 (charRep (cycLL PD LL)) (fun g => P (a g) (b g)) =
      -cupL ρ' P a b - cupL ρ P.flip b a := by
  funext ⟨g, h⟩
  show charRep (cycLL PD LL) g (P (a h) (b h)) - P (a (g * h)) (b (g * h)) + P (a g) (b g) =
    -P (a g) (ρ' g (b h)) - P (ρ g (a h)) (b g)
  rw [char_pair PD hd, ha, hb]
  simp only [map_add (f := _), LinearMap.add_apply]
  ring

variable [TopologicalSpace LL]

theorem cob_of_flip [IsTopologicalRing LL]
    (hd : ∀ g x y, P (ρ g x) (ρ' g y) = ((cycLL PD LL g : LLˣ) : LL) * P x y)
    {a : G → V} {b : G → V'} (ha : ∀ g h, a (g * h) = a g + ρ g (a h))
    (hb : ∀ g h, b (g * h) = b g + ρ' g (b h)) (hc : Continuous fun g => P (a g) (b g))
    (h : CobL PD (cupL ρ P.flip b a)) : CobL PD (cupL ρ' P a b) := by
  obtain ⟨u, hu, e⟩ := h
  refine ⟨-u - fun g => P (a g) (b g), hu.neg.sub hc, ?_⟩
  rw [map_sub, map_neg, e, d1_pair PD hd ha hb]
  abel

theorem cob_of_left (hd : ∀ g x y, P (ρ g x) (ρ' g y) = ((cycLL PD LL g : LLˣ) : LL) * P x y)
    {a : G → V} {b : G → V'} {x : V} (ha : ∀ g, a g = ρ g x - x)
    (hb : ∀ g h, b (g * h) = b g + ρ' g (b h)) (hc : Continuous fun g => P x (b g)) :
    CobL PD (cupL ρ' P a b) := by
  refine ⟨fun g => P x (b g), hc, ?_⟩
  funext ⟨g, h⟩
  show charRep (cycLL PD LL) g (P x (b h)) - P x (b (g * h)) + P x (b g) =
    P (a g) (ρ' g (b h))
  rw [char_pair PD hd, ha, hb]
  simp only [map_add (f := _), map_sub, LinearMap.sub_apply]
  ring

end Cup

end GlobalTheory.CompanionTheory.CupFlip
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.NonGaloisProofs.CyclotomicCupTwoCochainLocallyConstant
section
open NumberField IsDedekindDomain Formalism Formalism.ConjugateSelfDual Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations Module GlobalTheory.CompanionTheory.LocDual

noncomputable section

namespace GlobalTheory.CompanionTheory.LocDual.TopCoh

open ReciprocityTheory.Gal Formalism.GaloisCohomology GlobalTheory.Cyc GlobalTheory.Cyc.TwistLift

theorem coboundary_of_characters (hT : LocalTateDualityK) (l : ℕ) [Fact l.Prime]
    (K : IntermediateField ℚ_[l] (PadicAlgCl l)) (hK : FiniteDimensional ℚ_[l] K) (n : ℕ) (hn : 0 < n)
    (hχ : Continuous fun g => ((cycK l K n g : (ZMod (l ^ n))ˣ) : ZMod (l ^ n)))
    (M : Type) [AddCommGroup M] [Module (ZMod (l ^ n)) M] [Finite M] [TopologicalSpace M]
    [DiscreteTopology M] (z : Formalism.GaloisCohomology.GK l K × Formalism.GaloisCohomology.GK l K → M) (hz : Continuous z)
    (hcoc : ∀ g h k, ((cycK l K n g : (ZMod (l ^ n))ˣ) : ZMod (l ^ n)) • z (h, k) - z (g * h, k) +
      z (g, h * k) - z (g, h) = 0)
    (hchar : ∀ ψ : M →+ ZMod (l ^ n), ∃ f : Formalism.GaloisCohomology.GK l K → ZMod (l ^ n), Continuous f ∧
      ∀ g h, ((cycK l K n g : (ZMod (l ^ n))ˣ) : ZMod (l ^ n)) * f h - f (g * h) + f g = ψ (z (g, h))) :
    ∃ f : Formalism.GaloisCohomology.GK l K → M, Continuous f ∧
      ∀ g h, ((cycK l K n g : (ZMod (l ^ n))ˣ) : ZMod (l ^ n)) • f h - f (g * h) + f g = z (g, h) := by
  let rho : Representation (ZMod (l ^ n)) (Formalism.GaloisCohomology.GK l K) M := scalRep M (cycK l K n)
  have hrho : ContAction rho :=
    (continuous_of_discreteTopology (f := fun q : ZMod (l ^ n) × M => q.1 • q.2)).comp
      ((hχ.comp continuous_fst).prodMk continuous_snd)
  have hz2 : z ∈ Z2 (rho.comp (MonoidHom.id _)) := ⟨hz, hcoc⟩
  have hb := (hT l K hK n M rho hn hrho).2.2.2.2
  have hzero : cup20 (cycK l K n) rho (MonoidHom.id _) (Submodule.Quotient.mk ⟨z, hz2⟩) = 0 := by
    refine LinearMap.ext fun φ => ?_
    refine (Submodule.Quotient.mk_eq_zero _).2 ?_
    let φ' : M →ₗ[ZMod (l ^ n)] ZMod (l ^ n) := φ.1
    obtain ⟨f, hf, hd⟩ := hchar φ'.toAddMonoidHom
    exact ⟨f, hf, funext fun p => hd p.1 p.2⟩
  have h0 := hb.1 (hzero.trans (map_zero _).symm)
  obtain ⟨c, hc, hd⟩ := (Submodule.Quotient.mk_eq_zero _).1 h0
  exact ⟨c, hc, fun g h => congrFun hd (g, h)⟩

end GlobalTheory.CompanionTheory.LocDual.TopCoh
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.NonGaloisProofs.CyclotomicTwistFiniteModuleCocycle
section
open NumberField IsDedekindDomain Formalism Formalism.ConjugateSelfDual Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations Module GlobalTheory.CompanionTheory.LocDual

noncomputable section

namespace GlobalTheory.CompanionTheory.LocDual.Pair

private theorem exists_injective_zmod_addCircle_torsion (N : ℕ) [NeZero N] :
    ∃ j : ZMod N →+ AddCircle (1 : ℚ), Function.Injective j ∧
      ∀ t : AddCircle (1 : ℚ), N • t = 0 → t ∈ j.range := by
  have hN : (N : ℚ) ≠ 0 := Nat.cast_ne_zero.2 (NeZero.ne N)
  have hf : zmultiplesHom (AddCircle (1 : ℚ)) (((1 : ℚ) / N : ℚ) : AddCircle (1 : ℚ)) (N : ℤ) = 0 := by
    rw [zmultiplesHom_apply, ← AddCircle.coe_zsmul, AddCircle.coe_eq_zero_iff]
    refine ⟨1, ?_⟩
    rw [zsmul_eq_mul, zsmul_eq_mul]
    push_cast
    field_simp
  refine ⟨ZMod.lift N ⟨_, hf⟩, ?_, ?_⟩
  · rw [injective_iff_map_eq_zero]
    intro k hk
    have hk' : ((k.val : ℤ) : ZMod N) = k := by simp
    rw [← hk', ZMod.lift_coe, zmultiplesHom_apply, ← AddCircle.coe_zsmul,
      AddCircle.coe_eq_zero_iff] at hk
    obtain ⟨m, hm⟩ := hk
    rw [zsmul_eq_mul, zsmul_eq_mul, mul_one] at hm
    have hlt := ZMod.val_lt k
    have hm' : (m : ℚ) * N = k.val := by rw [hm]; push_cast; field_simp
    have hm'' : m * (N : ℤ) = (k.val : ℤ) := by exact_mod_cast hm'
    have hNpos : 0 < (N : ℤ) := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne N)
    have hlt' : (k.val : ℤ) < N := by exact_mod_cast hlt
    have hm0 : m = 0 := by
      rcases lt_trichotomy m 0 with h | h | h
      · nlinarith
      · exact h
      · nlinarith
    rw [hm0, zero_mul] at hm''
    have hv : k.val = 0 := by exact_mod_cast hm''.symm
    exact (ZMod.val_eq_zero k).1 hv
  · intro t ht
    obtain ⟨r, rfl⟩ := QuotientAddGroup.mk_surjective t
    change N • ((r : ℚ) : AddCircle (1 : ℚ)) = 0 at ht
    rw [← AddCircle.coe_nsmul, AddCircle.coe_eq_zero_iff] at ht
    obtain ⟨m, hm⟩ := ht
    have hm' : (m : ℚ) = N * r := by simpa [zsmul_eq_mul, nsmul_eq_mul] using hm
    refine ⟨(m : ZMod N), ?_⟩
    rw [ZMod.lift_coe]
    change m • (((1 : ℚ) / N : ℚ) : AddCircle (1 : ℚ)) = ((r : ℚ) : AddCircle (1 : ℚ))
    rw [← AddCircle.coe_zsmul]
    congr 1
    rw [zsmul_eq_mul, mul_one_div, div_eq_iff hN, hm']
    ring

theorem mem_of_cup_flip {N : ℕ} [NeZero N] {Γ : Type} [Group Γ] [TopologicalSpace Γ]
    (ψ : Γ →* (ZMod N)ˣ) {M : Type} [AddCommGroup M] [Module (ZMod N) M] [TopologicalSpace M]
    [DiscreteTopology M] (rho : Representation (ZMod N) Γ M)
    (hrho : ReciprocityTheory.Gal.ContAction (rho.comp (MonoidHom.id Γ)))
    (e : ReciprocityTheory.Gal.H2 ((ReciprocityTheory.Gal.charRep ψ).comp (MonoidHom.id Γ)) ≃ₗ[ZMod N] ZMod N)
    (hs : Function.Surjective (ReciprocityTheory.Gal.cupH1H1TwistedDual ψ rho (MonoidHom.id Γ) hrho).flip)
    (A : AddSubgroup (ReciprocityTheory.Gal.Z1 ((ReciprocityTheory.Gal.twDual ψ rho).comp (MonoidHom.id Γ))))
    (hB : ∀ z : ReciprocityTheory.Gal.Z1 ((ReciprocityTheory.Gal.twDual ψ rho).comp (MonoidHom.id Γ)),
      z.1 ∈ ReciprocityTheory.Gal.B1 ((ReciprocityTheory.Gal.twDual ψ rho).comp (MonoidHom.id Γ)) → z ∈ A)
    (z : ReciprocityTheory.Gal.Z1 ((ReciprocityTheory.Gal.twDual ψ rho).comp (MonoidHom.id Γ)))
    (h : ∀ y : ReciprocityTheory.Gal.H1 (rho.comp (MonoidHom.id Γ)),
      (∀ s ∈ A, ReciprocityTheory.Gal.cupH1H1TwistedDual ψ rho (MonoidHom.id Γ) hrho (Submodule.Quotient.mk s) y = 0) →
      ReciprocityTheory.Gal.cupH1H1TwistedDual ψ rho (MonoidHom.id Γ) hrho (Submodule.Quotient.mk z) y = 0) : z ∈ A := by
  classical
  by_contra hz
  let π : ReciprocityTheory.Gal.Z1 ((ReciprocityTheory.Gal.twDual ψ rho).comp (MonoidHom.id Γ)) →+
      ReciprocityTheory.Gal.H1 ((ReciprocityTheory.Gal.twDual ψ rho).comp (MonoidHom.id Γ)) :=
    { toFun := fun s => Submodule.Quotient.mk s
      map_zero' := Submodule.Quotient.mk_zero _
      map_add' := fun s t => Submodule.Quotient.mk_add _ }
  have hzA : π z ∉ A.map π := by
    rintro ⟨s, hs', hsz⟩
    apply hz
    have hq : (Submodule.Quotient.mk s :
        ReciprocityTheory.Gal.H1 ((ReciprocityTheory.Gal.twDual ψ rho).comp (MonoidHom.id Γ))) = Submodule.Quotient.mk z := hsz
    rw [Submodule.Quotient.eq] at hq
    have hq' := Submodule.neg_mem _ hq
    rw [neg_sub] at hq'
    have hmem : z - s ∈ A := hB (z - s) hq'
    have hsum := A.add_mem hmem hs'
    rwa [sub_add_cancel] at hsum
  have hq0 : (QuotientAddGroup.mk (π z) : _ ⧸ A.map π) ≠ 0 := by
    rw [Ne, QuotientAddGroup.eq_zero_iff]
    exact hzA
  obtain ⟨c, hc⟩ := CharacterModule.exists_character_apply_ne_zero_of_ne_zero hq0
  let c' : ReciprocityTheory.Gal.H1 ((ReciprocityTheory.Gal.twDual ψ rho).comp (MonoidHom.id Γ)) →+ AddCircle (1 : ℚ) :=
    c.comp (QuotientAddGroup.mk' (A.map π))
  have htors : ∀ h, N • c' h = 0 := by
    intro h
    rw [← map_nsmul, ← Nat.cast_smul_eq_nsmul (ZMod N), ZMod.natCast_self, zero_smul, map_zero]
  obtain ⟨j, hj, hjr⟩ := exists_injective_zmod_addCircle_torsion N
  let φ0 : ReciprocityTheory.Gal.H1 ((ReciprocityTheory.Gal.twDual ψ rho).comp (MonoidHom.id Γ)) →+ ZMod N :=
    (AddMonoidHom.ofInjective hj).symm.toAddMonoidHom.comp
      (c'.codRestrict j.range (fun h => hjr _ (htors h)))
  have key : ∀ h, j (φ0 h) = c' h := by
    intro h
    have hh := (AddMonoidHom.ofInjective hj).apply_symm_apply
      (c'.codRestrict j.range (fun h => hjr _ (htors h)) h)
    rw [Subtype.ext_iff, AddMonoidHom.ofInjective_apply] at hh
    exact hh
  let Lm := e.symm.toLinearMap ∘ₗ φ0.toZModLinearMap N
  obtain ⟨y, hy⟩ := hs Lm
  have hval : ∀ s, ReciprocityTheory.Gal.cupH1H1TwistedDual ψ rho (MonoidHom.id Γ) hrho (Submodule.Quotient.mk s) y =
      e.symm (φ0 (π s)) := by
    intro s
    have hh := LinearMap.congr_fun hy (Submodule.Quotient.mk s)
    rw [LinearMap.flip_apply] at hh
    rw [hh]
    rfl
  have hyA : ∀ s ∈ A, ReciprocityTheory.Gal.cupH1H1TwistedDual ψ rho (MonoidHom.id Γ) hrho (Submodule.Quotient.mk s) y = 0 := by
    intro s hs'
    rw [hval]
    have h0 : φ0 (π s) = 0 := by
      apply hj
      rw [key, map_zero]
      show c (QuotientAddGroup.mk (π s)) = 0
      rw [(QuotientAddGroup.eq_zero_iff _).2 (AddSubgroup.mem_map_of_mem π hs'), map_zero]
    rw [h0, map_zero]
  have hfin := h y hyA
  rw [hval, LinearEquiv.map_eq_zero_iff] at hfin
  apply hc
  have hj0 := congrArg j hfin
  rw [key, map_zero] at hj0
  exact hj0

theorem exists_equiv_dual {n : ℕ} [NeZero n] {M : Type} [AddCommGroup M] [Module (ZMod n) M] [Finite M]
    {M' : Type} [AddCommGroup M'] [Module (ZMod n) M'] [Finite M'] (P : M →+ M' →+ ZMod n)
    (h1 : ∀ x, (∀ y, P x y = 0) → x = 0) (h2 : ∀ y, (∀ x, P x y = 0) → y = 0) :
    ∃ e : M' ≃+ ReciprocityTheory.Gal.TDual (ZMod n) M, ∀ y x, e y x = P x y := by
  classical
  have hfin : ∀ (A : Type) [AddCommGroup A] [Module (ZMod n) A] [Finite A],
      Finite (Module.Dual (ZMod n) A) := fun A _ _ _ => (GlobalTheory.CocycleCount.card_linear_le n A).1
  let f : M' →+ Module.Dual (ZMod n) M :=
    { toFun := fun y => (P.flip y).toZModLinearMap n
      map_zero' := LinearMap.ext fun x => by
        show P x 0 = 0
        exact map_zero (P x)
      map_add' := fun y y' => LinearMap.ext fun x => by
        show P x (y + y') = P x y + P x y'
        exact map_add (P x) y y' }
  let g : M → Module.Dual (ZMod n) M' := fun x => (P x).toZModLinearMap n
  have hf : Function.Injective f := by
    intro y y' hyy
    have hyx : ∀ x, P x (y - y') = 0 := by
      intro x
      have hx := LinearMap.congr_fun hyy x
      change P x y = P x y' at hx
      rw [map_sub, hx, sub_self]
    exact sub_eq_zero.1 (h2 _ hyx)
  have hg : Function.Injective g := by
    intro x x' hxx
    have hxy : ∀ y, P (x - x') y = 0 := by
      intro y
      have hy := LinearMap.congr_fun hxx y
      change P x y = P x' y at hy
      rw [map_sub, AddMonoidHom.sub_apply, hy, sub_self]
    exact sub_eq_zero.1 (h1 _ hxy)
  haveI := hfin M
  haveI := hfin M'
  have c1 := Nat.card_le_card_of_injective f hf
  have c2 := Nat.card_le_card_of_injective g hg
  rw [GlobalTheory.ZModDual.card_dual_eq] at c1 c2
  have hb : Function.Bijective f :=
    hf.bijective_of_nat_card_le (by rw [GlobalTheory.ZModDual.card_dual_eq]; exact c2)
  exact ⟨AddEquiv.ofBijective f hb, fun y x => rfl⟩

end GlobalTheory.CompanionTheory.LocDual.Pair
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.NonGaloisProofs.LinearRelationExactSequenceDim
section
open NumberField IsDedekindDomain Formalism Formalism.ConjugateSelfDual Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations Module

namespace GlobalTheory.CompanionTheory.InertiaEigenvalues

theorem finrank_along_relation : ∀ (k : Type) [Field k] (H M N Q : Type) [AddCommGroup H] [Module k H] [AddCommGroup M] [Module k M] [AddCommGroup N] [Module k N] [AddCommGroup Q] [Module k Q] [Module.Finite k M] [Module.Finite k N] (a : H →ₗ[k] M) (b : M →ₗ[k] N) (R : Submodule k (N × Q)), Function.Injective a → LinearMap.range a = LinearMap.ker b → (∀ n, ∃ q, (n, q) ∈ R) → (∀ q, ∃ n, (n, q) ∈ R) → (∀ q, (0, q) ∈ R → q = 0) → (∀ n, (n, 0) ∈ R ↔ n ∈ LinearMap.range b) → Module.Finite k Q ∧ finrank k Q + finrank k M = finrank k H + finrank k N := by
  intro k _ H M N Q _ _ _ _ _ _ _ _ _ _ a b R hinj hex hN hQ h0 hb
  let p1 : R →ₗ[k] N := (LinearMap.fst k N Q).comp R.subtype
  let p2 : R →ₗ[k] Q := (LinearMap.snd k N Q).comp R.subtype
  have p1bij : Function.Bijective p1 := by
    constructor
    · rw [injective_iff_map_eq_zero]
      rintro ⟨⟨n, q⟩, hr⟩ h
      have hn : n = 0 := h
      subst hn
      have hq : q = 0 := h0 q hr
      subst hq
      rfl
    · intro n
      obtain ⟨q, hq⟩ := hN n
      exact ⟨⟨(n, q), hq⟩, rfl⟩
  let e : R ≃ₗ[k] N := LinearEquiv.ofBijective p1 p1bij
  let δ : N →ₗ[k] Q := p2.comp e.symm.toLinearMap
  have hδ : ∀ x : R, δ (p1 x) = p2 x := by
    intro x
    have h : e.symm (p1 x) = x := e.symm_apply_apply x
    show p2 (e.symm (p1 x)) = p2 x
    rw [h]
  have hsurj : Function.Surjective δ := by
    intro q
    obtain ⟨n, hn⟩ := hQ q
    exact ⟨n, hδ ⟨(n, q), hn⟩⟩
  have hker : LinearMap.ker δ = LinearMap.range b := by
    ext n
    rw [LinearMap.mem_ker, ← hb n]
    obtain ⟨q, hq⟩ := hN n
    have h1 : δ n = q := hδ ⟨(n, q), hq⟩
    rw [h1]
    constructor
    · rintro rfl
      exact hq
    · intro h
      have h2 : ((n, q) - (n, 0) : N × Q) ∈ R := R.sub_mem hq h
      have h3 : ((n, q) - (n, 0) : N × Q) = (0, q) := by simp
      rw [h3] at h2
      exact h0 q h2
  refine ⟨Module.Finite.of_surjective δ hsurj, ?_⟩
  have e1 := LinearMap.finrank_range_add_finrank_ker δ
  have e2 := LinearMap.finrank_range_add_finrank_ker b
  rw [LinearMap.range_eq_top.2 hsurj, finrank_top, hker] at e1
  rw [← hex] at e2
  have e3 : finrank k (LinearMap.range a) = finrank k H := LinearMap.finrank_range_of_inj hinj
  rw [e3] at e2
  omega

end GlobalTheory.CompanionTheory.InertiaEigenvalues
end

