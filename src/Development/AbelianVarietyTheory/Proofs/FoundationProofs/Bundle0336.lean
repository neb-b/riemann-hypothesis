module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Foundations.FinalTheorems
public import Development.AutomorphicArithmetic.AutomorphicVarieties.LevelCohomology.Bundle0004
public import ReciprocityTheory.Hypotheses.GalCoh
public import Development.AutomorphicArithmetic.AutomorphicVarieties.LevelCohomology.SoDefs
public import CompanionTheory.EightfoldTheory.VariationTheory.PublishedTheorems.ImportsAlt
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.Hypotheses2
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.RTwist
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0141
public import Formalism.LocalToGlobal.IndefiniteReal.FinitePlaces.Bundle0003
public import GroundTheory.AutomorphicForms.StrongApproximationSLDense

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.CharacterPowPredEqOneOfKillsPrimeRoots
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2
open scoped Matrix

namespace GlobalTheory.KillsMuOrd

theorem pow_apply_of_apply {Ω : Type} [Field Ω] [Algebra ℚ Ω] (s : G ℚ Ω) (ζ : Ω) (k : ℕ)
    (h : s ζ = ζ ^ k) : ∀ n : ℕ, (s ^ n) ζ = ζ ^ (k ^ n) := by
  intro n
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ', AlgEquiv.mul_apply, ih, map_pow, h, ← pow_mul, pow_succ', mul_comm]

theorem pow_fixes {Ω : Type} [Field Ω] [Algebra ℚ Ω] (l : ℕ) [hl : Fact l.Prime] (s : G ℚ Ω) (ζ : Ω)
    (hζ : ζ ^ l = 1) : (s ^ (l - 1)) ζ = ζ := by
  by_cases h1 : ζ = 1
  · subst h1; simp
  have hord : orderOf ζ = l := orderOf_eq_prime hζ h1
  have hprim : IsPrimitiveRoot ζ l := hord ▸ IsPrimitiveRoot.orderOf ζ
  have hsζ : (s ζ) ^ l = 1 := by rw [← map_pow, hζ, map_one]
  haveI : NeZero l := ⟨hl.out.ne_zero⟩
  obtain ⟨k, hk, hk'⟩ := hprim.eq_pow_of_pow_eq_one hsζ
  have hkl : ¬ l ∣ k := by
    rintro ⟨j, rfl⟩
    apply h1
    have : s ζ = 1 := by rw [← hk', pow_mul, hζ, one_pow]
    exact (map_eq_one_iff s s.injective).mp this
  rw [pow_apply_of_apply s ζ k hk'.symm]
  have hz : ((k : ZMod l)) ≠ 0 := by
    rwa [Ne, ZMod.natCast_eq_zero_iff]
  have hf : ((k ^ (l - 1) : ℕ) : ZMod l) = ((1 : ℕ) : ZMod l) := by
    push_cast; exact ZMod.pow_card_sub_one_eq_one hz
  rw [ZMod.natCast_eq_natCast_iff] at hf
  rw [← pow_mod_orderOf, hord, hf, Nat.one_mod_eq_one.mpr hl.out.one_lt.ne', pow_one]

theorem charPow_sub_one_eq_one : ∀ (Ω : Type) [Field Ω] [Algebra ℚ Ω] (l : ℕ) [Fact l.Prime] (C : Type) [Monoid C]
    (χ : G ℚ Ω →* C) (s : G ℚ Ω), KillsMu l χ → χ s ^ (l - 1) = 1 := by
  intro Ω _ _ l _ C _ χ s h
  rw [← map_pow]
  exact h _ fun ζ hζ => pow_fixes l s ζ hζ

end GlobalTheory.KillsMuOrd
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.CharpolySmulMap
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2 CongruenceSubgroup
open scoped Matrix MatrixGroups ModularForm

noncomputable section

open Polynomial

namespace GlobalTheory.TwAtt

theorem normV_eq (v : HeightOneSpectrum (𝓞 ℚ)) : normV v = Ideal.absNorm v.asIdeal := by
  rw [Ideal.absNorm_apply, Submodule.cardQuot_apply]; rfl

theorem mem_iff (v : HeightOneSpectrum (𝓞 ℚ)) (n : ℕ) : (n : 𝓞 ℚ) ∈ v.asIdeal ↔ normV v ∣ n := by
  rw [normV_eq]
  refine ⟨fun h => ?_, ?_⟩
  · have h1 := Ideal.absNorm_dvd_absNorm_of_le ((Ideal.span_singleton_le_iff_mem _).2 h)
    rwa [Ideal.absNorm_span_natCast, RingOfIntegers.rank, Module.finrank_self, pow_one] at h1
  · rintro ⟨c, rfl⟩
    rw [Nat.cast_mul]
    exact Ideal.mul_mem_right _ _ (Ideal.absNorm_mem _)

theorem normV_prime (v : HeightOneSpectrum (𝓞 ℚ)) : (normV v).Prime := by
  have h1 : 1 < normV v := by
    rw [normV_eq]
    exact NumberField.HeightOneSpectrum.one_lt_absNorm v
  refine Nat.prime_def.2 ⟨h1, fun m hm => ?_⟩
  obtain ⟨c, hc⟩ := hm
  have h2 := (mem_iff v _).2 dvd_rfl
  rw [hc, Nat.cast_mul] at h2
  rcases v.isPrime.mem_or_mem h2 with h | h
  · exact Or.inr (Nat.dvd_antisymm ⟨c, hc⟩ ((mem_iff v _).1 h))
  · have h3 := Nat.dvd_antisymm (Dvd.intro_left m hc.symm) ((mem_iff v _).1 h)
    rw [h3] at hc
    exact Or.inl (Nat.eq_of_mul_eq_mul_right (by omega) (hc.symm.trans (one_mul _).symm))

theorem eq_of_normV {v v' : HeightOneSpectrum (𝓞 ℚ)} (h : ((normV v : ℕ) : 𝓞 ℚ) ∈ v'.asIdeal) : v' = v := by
  have hle : v.asIdeal ≤ v'.asIdeal := by
    intro x hx
    obtain ⟨m, rfl⟩ : ∃ m : ℤ, (m : 𝓞 ℚ) = x := ⟨Rat.ringOfIntegersEquiv x, by
      apply Rat.ringOfIntegersEquiv.injective; simp⟩
    have key : ∀ I : Ideal (𝓞 ℚ), (m : 𝓞 ℚ) ∈ I ↔ ((m.natAbs : ℕ) : 𝓞 ℚ) ∈ I := fun I => by
      rcases Int.natAbs_eq m with e | e
      · conv_lhs => rw [e]
        rw [Int.cast_natCast]
      · conv_lhs => rw [e]
        rw [Int.cast_neg, Int.cast_natCast, neg_mem_iff]
    rw [key, mem_iff] at hx ⊢
    exact ((mem_iff _ _).1 h).trans hx
  exact (HeightOneSpectrum.ext (v.isMaximal.eq_of_le v'.isPrime.ne_top hle)).symm

theorem normV_injective : Function.Injective (normV : HeightOneSpectrum (𝓞 ℚ) → ℕ) := by
  intro v v' h
  refine (eq_of_normV (v := v') (v' := v) ?_)
  rw [← h]
  exact (mem_iff v _).2 dvd_rfl

end GlobalTheory.TwAtt

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.CoboundaryOfOrthogonalDualCharacterModPrimePow
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2
open scoped Matrix

noncomputable section

namespace GlobalTheory.Ord2.LocCharPerfect

open UpperTheory.V.X

variable {l : ℕ} [Fact l.Prime]

theorem lev_kill (c : Coef l) (n : ℕ) (m : Lev ((l : c.O) ^ n)) : (l ^ n) • m = 0 := by
  obtain ⟨x, rfl⟩ := Lev.mk_surjective _ m
  rw [← map_nsmul, Lev.mk_eq_zero, nsmul_eq_mul, Nat.cast_pow]
  exact dvd_mul_right _ _

def levZMod (c : Coef l) (n : ℕ) : Module (ZMod (l ^ n)) (Lev ((l : c.O) ^ n)) :=
  AddCommGroup.zmodModule (lev_kill c n)

attribute [local instance] levZMod

theorem smul_eq_zero_of_dvd (c : Coef l) (n : ℕ) {d : c.O} (h : (l : c.O) ^ n ∣ d)
    (m : Lev ((l : c.O) ^ n)) : d • m = 0 := by
  obtain ⟨x, rfl⟩ := Lev.mk_surjective _ m
  rw [← map_smul, Lev.mk_eq_zero, smul_eq_mul]
  exact h.mul_right _

theorem lev_sub_smul (c : Coef l) (n : ℕ) (x y : c.O) (m : Lev ((l : c.O) ^ n)) :
    (x - y) • m = x • m - y • m := sub_smul x y m

theorem smul_congr (c : Coef l) (n : ℕ) {x y : c.O} (h : (l : c.O) ^ n ∣ x - y)
    (m : Lev ((l : c.O) ^ n)) : x • m = y • m := by
  rw [← sub_eq_zero, ← sub_smul]
  exact smul_eq_zero_of_dvd c n h m

theorem zmod_smul (c : Coef l) (n : ℕ) [NeZero (l ^ n)] (a : ZMod (l ^ n)) (m : Lev ((l : c.O) ^ n)) :
    a • m = ((a.val : ℕ) : c.O) • m := by
  conv_lhs => rw [← ZMod.natCast_zmod_val a]
  rw [Nat.cast_smul_eq_nsmul, Nat.cast_smul_eq_nsmul]

theorem padic_smul (c : Coef l) (n : ℕ) [NeZero (l ^ n)] (z : ℤ_[l]) (m : Lev ((l : c.O) ^ n)) :
    algebraMap ℤ_[l] c.O z • m = PadicInt.toZModPow n z • m := by
  rw [zmod_smul]
  refine smul_congr c n ?_ m
  have hk : z - (((PadicInt.toZModPow n z).val : ℕ) : ℤ_[l]) ∈ Ideal.span {(l : ℤ_[l]) ^ n} := by
    rw [← PadicInt.ker_toZModPow, RingHom.mem_ker, map_sub, map_natCast, ZMod.natCast_zmod_val, sub_self]
  obtain ⟨t, ht⟩ := Ideal.mem_span_singleton'.1 hk
  refine ⟨algebraMap ℤ_[l] c.O t, ?_⟩
  rw [← map_natCast (algebraMap ℤ_[l] c.O), ← map_sub, ← ht, map_mul, map_pow, map_natCast, mul_comm]

def scal (c : Coef l) (n : ℕ) {Γ : Type} [Group Γ] (χ : Γ →* c.Oˣ) :
    Representation (ZMod (l ^ n)) Γ (Lev ((l : c.O) ^ n)) where
  toFun g := (DistribSMul.toAddMonoidHom (Lev ((l : c.O) ^ n)) ((χ g : c.Oˣ) : c.O)).toZModLinearMap (l ^ n)
  map_one' := LinearMap.ext fun m => by
    show ((χ 1 : c.Oˣ) : c.O) • m = m
    rw [map_one, Units.val_one, one_smul]
  map_mul' g h := LinearMap.ext fun m => by
    show ((χ (g * h) : c.Oˣ) : c.O) • m = ((χ g : c.Oˣ) : c.O) • ((χ h : c.Oˣ) : c.O) • m
    rw [map_mul, Units.val_mul, mul_smul]

theorem scal_apply (c : Coef l) (n : ℕ) {Γ : Type} [Group Γ] (χ : Γ →* c.Oˣ) (g : Γ) (m : Lev ((l : c.O) ^ n)) :
    scal c n χ g m = ((χ g : c.Oˣ) : c.O) • m := rfl

def smulZ (c : Coef l) (n : ℕ) (x : c.O) : Lev ((l : c.O) ^ n) →ₗ[ZMod (l ^ n)] Lev ((l : c.O) ^ n) :=
  (DistribSMul.toAddMonoidHom (Lev ((l : c.O) ^ n)) x).toZModLinearMap (l ^ n)

theorem contAction_scal (c : Coef l) {Γ : Type} [Group Γ] [TopologicalSpace Γ] (θ' : Γ →* c.Oˣ)
    (hθ' : Continuous (fun g => ((θ' g : c.Oˣ) : c.O))) (n : ℕ) (h0 : ((l : c.O) ^ n) ≠ 0) :
    ContAction (scal c n θ') := by
  refine continuous_prod_of_discrete_right.2 fun m => ?_
  obtain ⟨x, rfl⟩ := Lev.mk_surjective _ m
  refine (((UpperTheory.V.X.So.adicCont l c).1 _ h0).comp (hθ'.mul (continuous_const (y := x)))).congr fun g => ?_
  show Lev.mk ((l : c.O) ^ n) (((θ' g : c.Oˣ) : c.O) * x) = ((θ' g : c.Oˣ) : c.O) • Lev.mk ((l : c.O) ^ n) x
  rw [← smul_eq_mul, map_smul]

end GlobalTheory.Ord2.LocCharPerfect


open GlobalTheory.Ord2.LocCharPerfect UpperTheory.V.X in
attribute [local instance] levZMod in
set_option maxHeartbeats 1000000 in
theorem GlobalTheory.Ord2.LocCharPerfect.perfect : LocalFiniteness → LocalTateDuality → ∀ (l : ℕ) [Fact l.Prime] (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (c : Coef l) (A : ValuationSubring Ω), OverL l A → ∀ θ θ' : ↥(Dec (F := ℚ) A) →* c.Oˣ, Continuous (fun g => ((θ g : c.Oˣ) : c.O)) → Continuous (fun g => ((θ' g : c.Oˣ) : c.O)) → θ * θ' = (UpperTheory.V.Base.chiO ℚ Ω l c.O).comp (Dec (F := ℚ) A).subtype → ∀ n : ℕ, 1 ≤ n → ∀ b : ↥(Dec (F := ℚ) A) → c.O, Continuous b → (∀ s t, ((l : ℕ) : c.O) ^ n ∣ b (s * t) - (b s + ((θ s : c.Oˣ) : c.O) * b t)) → (∀ a : ↥(Dec (F := ℚ) A) → c.O, Continuous a → (∀ s t, ((l : ℕ) : c.O) ^ n ∣ a (s * t) - (a s + ((θ' s : c.Oˣ) : c.O) * a t)) → ∃ u : ↥(Dec (F := ℚ) A) → c.O, Continuous u ∧ ∀ s t, ((l : ℕ) : c.O) ^ n ∣ b s * (((θ' s : c.Oˣ) : c.O) * a t) - ((((θ s : c.Oˣ) : c.O) * ((θ' s : c.Oˣ) : c.O)) * u t - u (s * t) + u s)) → ∃ x : c.O, ∀ s, ((l : ℕ) : c.O) ^ n ∣ b s - (((θ s : c.Oˣ) : c.O) * x - x) := by
  intro hF hT l _ Ω _ _ _ c A hA θ θ' hθ hθ' hθθ n hn b hb hbc hcup
  classical
  haveI : NeZero (l ^ n) := ⟨pow_ne_zero _ (Fact.out : l.Prime).ne_zero⟩
  have hl0 : ((l : ℕ) : c.O) ≠ 0 := by
    intro h
    have h' := congrArg (fun x : c.O => (x : PadicAlgCl l)) h
    simp only [SubringClass.coe_natCast, ZeroMemClass.coe_zero, Nat.cast_eq_zero] at h'
    exact (Fact.out : l.Prime).ne_zero h'
  have ha0 : ((l : c.O) ^ n) ≠ 0 := pow_ne_zero _ hl0
  obtain ⟨v, hv, -⟩ := hA
  haveI : Finite (Lev ((l : c.O) ^ n)) :=
    (UpperTheory.V.X.So.levFacts l c.O _ ha0 (Lev ((l : c.O) ^ n)) ⟨LinearEquiv.refl _ _⟩).1
  obtain ⟨φ₀, hφ0, hφall⟩ := UpperTheory.V.X.So.dualGen l c.O _ ha0 n (Lev ((l : c.O) ^ n)) ⟨LinearEquiv.refl _ _⟩
  set rho := scal c n θ' with hrho
  have hc : ContAction rho := contAction_scal c θ' hθ' n ha0
  set χ := (cycMod ℚ Ω l n).comp (Dec (F := ℚ) A).subtype with hχ

  have hchi : ∀ s : ↥(Dec (F := ℚ) A), ((θ s : c.Oˣ) : c.O) * ((θ' s : c.Oˣ) : c.O) =
      algebraMap ℤ_[l] c.O (cycZ ℚ Ω l (s : G ℚ Ω) : ℤ_[l]) := fun s => by
    rw [← Units.val_mul, ← MonoidHom.mul_apply, hθθ]; rfl
  have hχs : ∀ (s : ↥(Dec (F := ℚ) A)) (m : Lev ((l : c.O) ^ n)),
      ((χ s : (ZMod (l ^ n))ˣ) : ZMod (l ^ n)) • m = (((θ s : c.Oˣ) : c.O) * ((θ' s : c.Oˣ) : c.O)) • m := by
    intro s m
    rw [hchi, padic_smul]; rfl
  have key : ∀ (s : ↥(Dec (F := ℚ) A)) (x : c.O) (m : Lev ((l : c.O) ^ n)),
      ((χ s : (ZMod (l ^ n))ˣ) : ZMod (l ^ n)) * φ₀ (x • rho s⁻¹ m) = φ₀ ((((θ s : c.Oˣ) : c.O) * x) • m) := by
    intro s x m
    rw [← smul_eq_mul, ← map_smul, hχs, scal_apply, smul_smul, smul_smul, map_inv]
    congr 2
    calc _ = (((θ s : c.Oˣ) : c.O) * x) * (((θ' s : c.Oˣ) : c.O) * (((θ' s)⁻¹ : c.Oˣ) : c.O)) := by ring
      _ = _ := by rw [Units.mul_inv, mul_one]

  let bs : ↥(Dec (F := ℚ) A) → TDual (ZMod (l ^ n)) (Lev ((l : c.O) ^ n)) :=
    fun s => TDual.mk (φ₀ ∘ₗ smulZ c n (b s))
  let sec := Function.surjInv (Lev.mk_surjective ((l : c.O) ^ n))
  have hsec : ∀ y, Lev.mk ((l : c.O) ^ n) (sec y) = y := Function.surjInv_eq _
  have hmk : Continuous (Lev.mk ((l : c.O) ^ n)) := (UpperTheory.V.X.So.adicCont l c).1 _ ha0
  have hbsc : Continuous bs := by
    refine ((continuous_of_discreteTopology (f := fun y : Lev ((l : c.O) ^ n) =>
      TDual.mk (φ₀ ∘ₗ smulZ c n (sec y)))).comp (hmk.comp hb)).congr fun s => ?_
    refine DFunLike.ext _ _ fun m => ?_
    show φ₀ (sec (Lev.mk ((l : c.O) ^ n) (b s)) • m) = φ₀ (b s • m)
    have hd : (l : c.O) ^ n ∣ sec (Lev.mk ((l : c.O) ^ n) (b s)) - b s := by
      rw [← Lev.mk_eq_zero, map_sub, hsec, sub_self]
    rw [smul_congr c n hd m]
  have hz : bs ∈ Z1 ((twDual χ rho).comp (MonoidHom.id _)) := by
    refine ⟨hbsc, fun s t => ?_⟩
    refine DFunLike.ext _ _ fun m => ?_
    show φ₀ (b (s * t) • m) = φ₀ (b s • m) + ((χ s : (ZMod (l ^ n))ˣ) : ZMod (l ^ n)) * φ₀ (b t • rho s⁻¹ m)
    rw [key, ← map_add (f := _), ← add_smul, smul_congr c n (hbc s t) m]
  obtain ⟨-, -, hbij, -, -⟩ := hT ℚ Ω l n (Lev ((l : c.O) ^ n)) A rho v (by omega) hv hc
  have h0 : (Submodule.Quotient.mk ⟨bs, hz⟩ : H1 ((twDual χ rho).comp (MonoidHom.id _))) = 0 := by
    refine hbij.1 (Eq.trans ?_ (LinearMap.map_zero _).symm)
    refine Submodule.linearMap_qext _ (LinearMap.ext fun y => ?_)
    let at' : ↥(Dec (F := ℚ) A) → c.O := fun t => sec (y.1 t)
    have hat : ∀ t, Lev.mk ((l : c.O) ^ n) (at' t) = y.1 t := fun t => hsec _
    have hac : Continuous at' := (continuous_of_discreteTopology (f := sec)).comp y.2.1
    have hacoc : ∀ s t, (l : c.O) ^ n ∣ at' (s * t) - (at' s + ((θ' s : c.Oˣ) : c.O) * at' t) := by
      intro s t
      have hm : Lev.mk ((l : c.O) ^ n) (((θ' s : c.Oˣ) : c.O) * at' t) = ((θ' s : c.Oˣ) : c.O) • Lev.mk ((l : c.O) ^ n) (at' t) := by
        rw [← smul_eq_mul, map_smul]
      rw [← Lev.mk_eq_zero, map_sub, map_add (f := _), hm, hat, hat, hat, y.2.2 s t]
      exact sub_self _
    obtain ⟨u, hu, hdiv⟩ := hcup at' hac hacoc
    change (Submodule.Quotient.mk (cupCocycleZ1Z1 _ _ _ _ _ _ _ _ _) : H2 _) = 0
    rw [Submodule.Quotient.mk_eq_zero]
    refine ⟨fun t => φ₀ (Lev.mk ((l : c.O) ^ n) (u t)),
      (continuous_of_discreteTopology (f := ⇑φ₀)).comp (hmk.comp hu), funext fun p => ?_⟩
    obtain ⟨g, h⟩ := p
    have e1 : (((θ g : c.Oˣ) : c.O) * ((θ' g : c.Oˣ) : c.O)) • Lev.mk ((l : c.O) ^ n) (u h) -
        Lev.mk ((l : c.O) ^ n) (u (g * h)) + Lev.mk ((l : c.O) ^ n) (u g) =
        b g • ((θ' g : c.Oˣ) : c.O) • y.1 h := by
      rw [← hat h, ← map_smul, ← map_smul, ← map_smul, ← map_sub, ← map_add (f := _), smul_eq_mul, smul_eq_mul,
        smul_eq_mul]
      have := (Lev.mk_eq_zero _ _).2 (hdiv g h)
      rw [map_sub, sub_eq_zero] at this
      exact this.symm
    show ((χ g : (ZMod (l ^ n))ˣ) : ZMod (l ^ n)) * φ₀ (Lev.mk ((l : c.O) ^ n) (u h)) -
      φ₀ (Lev.mk ((l : c.O) ^ n) (u (g * h))) + φ₀ (Lev.mk ((l : c.O) ^ n) (u g)) =
      φ₀ (b g • ((θ' g : c.Oˣ) : c.O) • y.1 h)
    rw [← e1, map_add (f := _), map_sub, ← hχs, map_smul, smul_eq_mul]
  rw [Submodule.Quotient.mk_eq_zero] at h0
  obtain ⟨ψ, hψ⟩ := (mem_coboundaries1 _ _).1 (Submodule.mem_comap.1 h0)
  obtain ⟨x, hx⟩ := hφall ψ
  refine ⟨x, fun s => (hφ0 _).1 fun m => ?_⟩
  have e := congrArg (fun φ : TDual (ZMod (l ^ n)) (Lev ((l : c.O) ^ n)) => φ m) (hψ s)
  change φ₀ (b s • m) = ((χ s : (ZMod (l ^ n))ˣ) : ZMod (l ^ n)) * ψ (rho s⁻¹ m) - ψ m at e
  have hx' : ∀ m, (ψ : TDual (ZMod (l ^ n)) (Lev ((l : c.O) ^ n))) m = φ₀ (x • m) := hx
  rw [hx', hx', key] at e
  have h1 : (b s - (((θ s : c.Oˣ) : c.O) * x - x)) • m = b s • m - ((((θ s : c.Oˣ) : c.O) * x) • m - x • m) := by
    rw [lev_sub_smul, lev_sub_smul]
  refine (congrArg φ₀ h1).trans ?_
  rw [map_sub, map_sub, e, sub_self]
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.CoboundaryOfUniformLimitCoboundaries
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2
open scoped Matrix

namespace GlobalTheory

theorem coboundary_closed_of_uniform_approx {𝕜 : Type} [NormedField 𝕜] {Γ : Type} (H : Set Γ)
    (k f : Γ → 𝕜) (hne : ∃ s ∈ H, k s ≠ 1)
    (happ : ∀ ε : ℝ, 0 < ε → ∃ X : 𝕜, ∀ s ∈ H, ‖f s - (k s * X - X)‖ ≤ ε) :
    ∃ X : 𝕜, ∀ s ∈ H, f s = k s * X - X := by
  obtain ⟨s₀, hs₀, hk⟩ := hne
  have hd : k s₀ - 1 ≠ 0 := sub_ne_zero.mpr hk
  have hdpos : 0 < ‖k s₀ - 1‖ := norm_pos_iff.mpr hd
  refine ⟨f s₀ / (k s₀ - 1), fun s hs => ?_⟩
  have hCpos : 0 < 1 + ‖k s - 1‖ / ‖k s₀ - 1‖ := by positivity
  have key : ∀ ε : ℝ, 0 < ε → ‖f s - (k s * (f s₀ / (k s₀ - 1)) - f s₀ / (k s₀ - 1))‖
      ≤ ε * (1 + ‖k s - 1‖ / ‖k s₀ - 1‖) := by
    intro ε hε
    obtain ⟨X, hX⟩ := happ ε hε
    have h0 := hX s₀ hs₀
    have e0 : f s₀ - (k s₀ * X - X) = (k s₀ - 1) * (f s₀ / (k s₀ - 1) - X) := by
      field_simp
    rw [e0, norm_mul] at h0
    have hXX : ‖X - f s₀ / (k s₀ - 1)‖ ≤ ε / ‖k s₀ - 1‖ := by
      rw [norm_sub_rev, le_div_iff₀ hdpos, mul_comm]; exact h0
    have e1 : f s - (k s * (f s₀ / (k s₀ - 1)) - f s₀ / (k s₀ - 1))
        = (f s - (k s * X - X)) + (k s - 1) * (X - f s₀ / (k s₀ - 1)) := by ring
    calc ‖f s - (k s * (f s₀ / (k s₀ - 1)) - f s₀ / (k s₀ - 1))‖
        = ‖(f s - (k s * X - X)) + (k s - 1) * (X - f s₀ / (k s₀ - 1))‖ := by rw [e1]
      _ ≤ ‖f s - (k s * X - X)‖ + ‖k s - 1‖ * ‖X - f s₀ / (k s₀ - 1)‖ := by
          refine (norm_add_le _ _).trans ?_
          rw [norm_mul]
      _ ≤ ε + ‖k s - 1‖ * (ε / ‖k s₀ - 1‖) := by
          gcongr
          exact hX s hs
      _ = ε * (1 + ‖k s - 1‖ / ‖k s₀ - 1‖) := by ring
  have hz : ‖f s - (k s * (f s₀ / (k s₀ - 1)) - f s₀ / (k s₀ - 1))‖ ≤ 0 := by
    refine le_of_forall_pos_le_add fun ε hε => ?_
    have h := key (ε / (1 + ‖k s - 1‖ / ‖k s₀ - 1‖)) (div_pos hε hCpos)
    rw [div_mul_cancel₀ _ hCpos.ne'] at h
    linarith
  exact sub_eq_zero.mp (norm_le_zero_iff.mp hz)

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.CoefDualFreeRankOne
section
noncomputable section

open UpperTheory.V.HV

namespace GlobalTheory.Ord2.CoefDual

variable (l : ℕ) [Fact l.Prime] (c : Coef l)

def dualModule : Module c.O (c.O →ₗ[ℤ_[l]] ℤ_[l]) where
  smul a f := f ∘ₗ LinearMap.mulLeft ℤ_[l] a
  one_smul f := by apply LinearMap.ext; intro x; show f (1 * x) = f x; rw [one_mul]
  mul_smul a b f := by apply LinearMap.ext; intro x; show f (a * b * x) = f (b * (a * x)); rw [mul_comm a b, mul_assoc]
  smul_zero a := by apply LinearMap.ext; intro x; show (0 : c.O →ₗ[ℤ_[l]] ℤ_[l]) (a * x) = 0; rfl
  smul_add a f g := by apply LinearMap.ext; intro x; show (f + g) (a * x) = f (a * x) + g (a * x); rfl
  add_smul a b f := by apply LinearMap.ext; intro x; show f ((a + b) * x) = f (a * x) + f (b * x); rw [add_mul, map_add (f := _)]
  zero_smul f := by apply LinearMap.ext; intro x; show f (0 * x) = 0; rw [zero_mul, map_zero]

theorem dualModule_apply (a : c.O) (f : c.O →ₗ[ℤ_[l]] ℤ_[l]) (x : c.O) :
    (letI := dualModule l c; a • f) x = f (a * x) := rfl

theorem dual_tower :
    letI := dualModule l c; IsScalarTower ℤ_[l] c.O (c.O →ₗ[ℤ_[l]] ℤ_[l]) := by
  letI := dualModule l c
  refine ⟨fun r a f => ?_⟩
  ext x
  rw [dualModule_apply, LinearMap.smul_apply, dualModule_apply, smul_mul_assoc, map_smul]

theorem dual_torsionFree :
    letI := dualModule l c; Module.IsTorsionFree c.O (c.O →ₗ[ℤ_[l]] ℤ_[l]) := by
  letI := dualModule l c
  refine Module.IsTorsionFree.of_smul_eq_zero fun a f h => ?_
  by_cases ha : a = 0
  · exact Or.inl ha
  right
  have hne := Ideal.comap_ne_bot_of_integral_mem (R := ℤ_[l]) (I := Ideal.span {a}) ha
    (Ideal.mem_span_singleton_self a) (Algebra.IsIntegral.isIntegral a)
  obtain ⟨r, hr, hr0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hne
  rw [Ideal.mem_comap, Ideal.mem_span_singleton] at hr
  obtain ⟨b, hb⟩ := hr
  ext x
  have h1 : r • f x = 0 := by
    rw [← map_smul, Algebra.smul_def, hb, mul_assoc, ← dualModule_apply, h]
    rfl
  simpa [hr0] using h1

end GlobalTheory.Ord2.CoefDual


open GlobalTheory.Ord2.CoefDual in
theorem GlobalTheory.Ord2.coef_dual_free_rank_one :
    ∀ (l : ℕ) [Fact l.Prime] (c : Coef l), ∃ τ : c.O →ₗ[ℤ_[l]] ℤ_[l],
      ∀ f : c.O →ₗ[ℤ_[l]] ℤ_[l], ∃! a : c.O, ∀ x, f x = τ (a * x) := by
  intro l _ c
  letI := dualModule l c
  haveI := dual_tower l c
  haveI : Module.IsTorsionFree ℤ_[l] c.O := FaithfulSMul.to_isTorsionFree ℤ_[l] c.O
  haveI : Module.Free ℤ_[l] c.O := Module.free_of_finite_type_torsion_free'
  haveI : Module.Finite c.O (c.O →ₗ[ℤ_[l]] ℤ_[l]) := Module.Finite.of_restrictScalars_finite ℤ_[l] _ _
  haveI := dual_torsionFree l c
  haveI : Module.Free c.O (c.O →ₗ[ℤ_[l]] ℤ_[l]) := Module.free_of_finite_type_torsion_free'
  have h1 := Module.finrank_linearMap ℤ_[l] ℤ_[l] c.O ℤ_[l]
  have h2 := Module.finrank_mul_finrank ℤ_[l] c.O (c.O →ₗ[ℤ_[l]] ℤ_[l])
  have hpos : 0 < Module.finrank ℤ_[l] c.O := Module.finrank_pos
  have hr : Module.finrank c.O (c.O →ₗ[ℤ_[l]] ℤ_[l]) = 1 := by
    rw [h1, Module.finrank_self, mul_one] at h2
    exact Nat.eq_of_mul_eq_mul_left hpos (h2.trans (mul_one _).symm)
  let b := Module.finBasisOfFinrankEq c.O (c.O →ₗ[ℤ_[l]] ℤ_[l]) hr
  refine ⟨b 0, fun f => ⟨b.repr f 0, fun x => ?_, fun a ha => ?_⟩⟩
  · have hs := b.sum_repr f
    rw [Fin.sum_univ_one] at hs
    rw [← dualModule_apply, hs]
  · have hf : f = a • b 0 := LinearMap.ext fun x => (ha x).trans (dualModule_apply l c a (b 0) x).symm
    rw [hf, map_smul, b.repr_self]
    simp

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ContinuousOfIsOpenStab
section
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Polynomial
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp GlobalTheory.UnitaryBC UpperTheory.V.Af UpperTheory.V
open scoped Matrix TensorProduct

namespace GlobalTheory.SlTwoCusp

open Topology

theorem continuous_pInf' (F : Type) [Field F] [NumberField F] [IsTotallyReal F] : Continuous (TR.pInf F) := by
  have hc : Continuous (TR.infEq F).symm :=
    continuous_pi fun w =>
      (InfinitePlace.Completion.isometryEquivRealOfIsReal (IsTotallyReal.isReal w)).continuous.comp (continuous_apply w)
  exact hc.comp continuous_fst

theorem continuous_of_isOpen_stab : ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F] (a : ℕ) (φ : TR.Sm F a),
    IsOpen {k | TR.finRep F a k φ = φ} → Continuous φ.1 := by
  intro F _ _ _ a φ hφ
  refine continuous_iff_continuousAt.2 fun g => ?_
  have hm : Continuous fun x : GA F a => g⁻¹ * x := continuous_const.mul continuous_id
  have hI : Continuous (Matrix.GeneralLinearGroup.map (TR.pInf F) : GA F a → GL (Fin a) (TR.Rinf F)) :=
    Continuous.units_map _ (continuous_id.matrix_map (continuous_pInf' F))
  have hFn : Continuous (Matrix.GeneralLinearGroup.map (pFin F) : GA F a → GL (Fin a) (Af F)) :=
    Continuous.units_map _ (continuous_id.matrix_map continuous_snd)
  have h1 : Continuous fun x : GA F a => TR.toL (Matrix.GeneralLinearGroup.map (TR.pInf F) (g⁻¹ * x)).val :=
    (Units.continuous_val (M := Matrix (Fin a) (Fin a) (TR.Rinf F))).comp (hI.comp hm)
  have h2 : ContinuousAt (fun x : GA F a => TR.chart φ.1 g (TR.toL (Matrix.GeneralLinearGroup.map (TR.pInf F) (g⁻¹ * x)).val)) g :=
    ContinuousAt.comp (f := fun x : GA F a => TR.toL (Matrix.GeneralLinearGroup.map (TR.pInf F) (g⁻¹ * x)).val)
      (TR.contDiffAt_chart φ.2 g (TR.val_mem_invSet _)).continuousAt h1.continuousAt
  refine h2.congr ?_
  have h3 : {x : GA F a | TR.finRep F a (Matrix.GeneralLinearGroup.map (pFin F) (g⁻¹ * x)) φ = φ} ∈ 𝓝 g :=
    (hφ.preimage (hFn.comp hm)).mem_nhds (by simp)
  filter_upwards [h3] with x hx
  rw [TR.chart_val]
  conv_lhs => rw [← hx]
  change φ.1 (g * TR.infGL F a _ * finGL F a _) = _
  rw [mul_assoc, TR.infGL_mul_finGL, mul_inv_cancel_left]

open MeasureTheory Topology

end GlobalTheory.SlTwoCusp
end

