module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.IdeleGenerators.Bundle0002
public import Development.AutomorphicArithmetic.AutomorphicVarieties.IdeleGenerators.HolomorphicIrreducibility.ExistsIdele
public import Development.AutomorphicArithmetic.AutomorphicVarieties.IdeleGenerators.HolomorphicIrreducibility.HolLin
public import Development.AutomorphicArithmetic.AutomorphicVarieties.IdeleGenerators.HolomorphicIrreducibility.ExpInj
public import Development.AutomorphicArithmetic.AutomorphicVarieties.IdeleGenerators.HolomorphicIrreducibility.Bundle0009
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.NewformCoefficients.Bundle0004
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.NewformCoefficients.Bundle0003
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.NewformCoefficients.Bundle0002
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.NewformCoefficients.Bundle0006
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.NewformCoefficients.Bundle0005
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.NewformCoefficients.Bundle0001
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.NewformCoefficients.Bundle0007
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.NewformCoefficients.OrthCases
public import Development.AutomorphicArithmetic.AutomorphicVarieties.IdeleGenerators.Bundle0001
public import Development.AutomorphicArithmetic.AutomorphicVarieties.IdeleGenerators.HolomorphicIrreducibility.ToNewform
public import Development.AutomorphicArithmetic.AutomorphicVarieties.IdeleGenerators.HolomorphicIrreducibility.Bundle0006
public import Development.AutomorphicArithmetic.AutomorphicVarieties.IdeleGenerators.HolomorphicIrreducibility.Bundle0005
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.TemperedLocalComponents.Bundle0010
public import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.Bundle0033
public import Development.AutomorphicArithmetic.AutomorphicVarieties.CharacterLevelBounds.Bundle0001
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PrimitiveFrobeniusFixed.Bundle0002
public import Development.AutomorphicArithmetic.AutomorphicVarieties.IdeleGenerators.WeightChange
public import Development.AutomorphicArithmetic.AutomorphicVarieties.IdeleGenerators.HolomorphicIrreducibility.Bundle0001
public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.CrystallineBaseChange.Bundle0011

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.IdeleGenerators.HolomorphicIrreducibility.Adelise
section
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep UpperTheory.V UpperTheory.V.Af UpperTheory.V.Af.Nf CongruenceSubgroup Matrix
open scoped MatrixGroups ModularForm Manifold

namespace UpperTheory.V.Sd.AdelicUnramifiedNorms

private theorem lift_hol : LiftHol := by
  intro k M hM χ ω hω f hf
  obtain ⟨φ₀, hφ⟩ := liftEx k M hM f fun δ hδ => SlashInvariantForm.slash_action_eqn f δ ⟨δ, hδ, rfl⟩
  obtain ⟨hl, hr, hs⟩ := liftSm k M hM f φ₀ hφ
  let φ : TR.Sm ℚ 2 := ⟨φ₀, hs f.holo'⟩
  have hfix : ∀ u ∈ K1G M, TR.finRep ℚ 2 u φ = φ := fun u hu => Subtype.ext (funext (hr u hu))
  have hlev : IsOpen {u | TR.finRep ℚ 2 u φ = φ} :=
    isOpen_stab_of_mem_nhds _ _ (Filter.mem_of_superset ((kOpen M hM).1.mem_nhds (one_mem _)) hfix)
  have hc := liftCent k M hM χ ω hω f hf φ₀ hφ
  have hlie := liftLie k M hM f f.holo' φ hφ
  obtain ⟨C, hC⟩ := archBd k M hM f
  have haut : TR.IsAutForm φ := ⟨hl, hlev, liftK k M hM f φ hφ,
    zFin ℚ k ω (charVal M hM χ ω hω).1 φ hc (fun v => (hlie v).1) (fun v => (hlie v).2), fun g => ⟨C, 0, fun y => by
      obtain ⟨γ, h, u, hu, e⟩ := decomp M hM (g * TR.infGL ℚ 2 y)
      rw [pow_zero, mul_one, e]
      change ‖φ₀ _‖ ≤ C
      rw [hφ γ h u hu]
      exact hC _ h.det_ne_zero⟩⟩
  exact ⟨φ, hφ, ⟨haut, fun w u hu => hfix _ (kLocal M hM w u hu), hc, fun v => (hlie v).1, fun v => (hlie v).2⟩,
    haut, cuspCrit φ hl hlev (liftCT k M hM f φ₀ hφ)⟩

section Gen

variable {F : Type} [Field F] [NumberField F]

private theorem fin_scalar (w : Pl F) (x : (w.adicCompletion F)ˣ) :
    finGL F 2 (locGL F 2 w (GeneralLinearGroup.scalar (Fin 2) x)) = GeneralLinearGroup.scalar (Fin 2) (localIdele F w x) := by
  have h := GlobalTheory.CuspRep.finId_det_locGL w (GeneralLinearGroup.scalar (Fin 1) x)
  rw [locGL, GlobalTheory.CuspRep.cornerGL_scalar] at h ⊢
  rw [finGL, GlobalTheory.CuspRep.cornerGL_scalar]
  congr 1
  exact (congrArg (finId F) (GlobalTheory.CuspRep.CG.det_oneByOne _)).symm.trans
    (h.trans (congrArg (localIdele F w) (GlobalTheory.CuspRep.CG.det_oneByOne _)))

private theorem scalar_mem (w : Pl F) (x : (w.adicCompletion F)ˣ) (hx : IsUnitAt w x) :
    GeneralLinearGroup.scalar (Fin 2) x ∈ K1 w 0 := by
  have hx' : Valued.v (x : w.adicCompletion F) = 1 := hx
  obtain ⟨u, hu⟩ : IsUnit (⟨(x : w.adicCompletion F), hx'.le⟩ : w.adicCompletionIntegers F) :=
    HeightOneSpectrum.adicCompletionIntegers.isUnit_iff_valued_eq_one.2 hx'
  refine ⟨GeneralLinearGroup.scalar (Fin 2) u, ?_, ?_⟩
  · haveI : Subsingleton (w.adicCompletionIntegers F ⧸ IsLocalRing.maximalIdeal (w.adicCompletionIntegers F) ^ 0) := by
      rw [pow_zero, Ideal.one_eq_top]; infer_instance
    exact Subsingleton.elim (α := Fin 2 → _) _ _
  · have hu' : ((u : w.adicCompletionIntegers F) : w.adicCompletion F) = x := congrArg Subtype.val hu
    ext i j
    fin_cases i <;> fin_cases j <;> simp [hu']

private theorem unr_of_hol [IsTotallyReal F] {k : ℕ} {c : Pl F → ℕ} {ω : HChar F} {φ : TR.Sm F 2} (h : IsHol k c ω φ) (h0 : φ ≠ 0)
    {w : Pl F} (hc : c w = 0) : ω.UnrAt w := by
  intro x hx
  obtain ⟨g, hg⟩ : ∃ g, φ.1 g ≠ 0 := by
    by_contra hn
    exact h0 (Subtype.ext (funext fun g => not_not.1 fun e => hn ⟨g, e⟩))
  have h1 := congrFun (congrArg Subtype.val (h.level w _ (hc ▸ scalar_mem w x hx))) g
  change φ.1 (g * finGL F 2 (locGL F 2 w _)) = _ at h1
  have h2 : g * GeneralLinearGroup.scalar (Fin 2) (localIdele F w x) = GeneralLinearGroup.scalar (Fin 2) (localIdele F w x) * g :=
    Units.ext (Matrix.scalar_commute _ (fun _ => Commute.all _ _) _).symm.eq
  rw [fin_scalar, h2, h.cent] at h1
  exact Units.ext (mul_right_cancel₀ hg (h1.trans (one_mul _).symm))

private theorem chi_prime (ω : HChar F) (c : Pl F → ℕ) (w : Pl F) :
    chiI ω c w.asIdeal = if c w = 0 then ((ω.val w : ℂˣ) : ℂ) else 0 := by
  unfold chiI
  rw [finprod_eq_single _ w]
  · have : ordI w w.asIdeal = 1 := Associates.count_self w.associates_irreducible
    rw [this, pow_one]
  · intro v hv
    have : ordI v w.asIdeal = 0 := by
      by_contra h0
      have h1 := (Associates.count_ne_zero_iff_dvd w.ne_bot v.irreducible).1 h0
      exact hv (HeightOneSpectrum.ext (associated_iff_eq.1 ((v.prime.dvd_prime_iff_associated w.prime).1 h1)))
    rw [this, pow_zero]

end Gen

private theorem lev_eq (M : ℕ) (hM : 1 ≤ M) (w : Pl ℚ) : lev M w = M.factorization (normV w) := by
  obtain ⟨hp, hw, -, h0⟩ := places w
  have hM0 : M ≠ 0 := by omega
  set m := M / normV w ^ M.factorization (normV w) with hm
  have hmpos : 0 < m := Nat.ordCompl_pos _ hM0
  have h1 := h0 m hmpos (Nat.not_dvd_ordCompl hp hM0)
  have e : Ideal.span {(M : 𝓞 ℚ)} = w.asIdeal ^ M.factorization (normV w) * Ideal.span {(m : 𝓞 ℚ)} := by
    conv_rhs => rw [hw]
    rw [Ideal.span_singleton_pow, Ideal.span_singleton_mul_span_singleton, ← Nat.cast_pow, ← Nat.cast_mul,
      Nat.ordProj_mul_ordCompl_eq_self]
  have hmb : Ideal.span {(m : 𝓞 ℚ)} ≠ 0 := by
    rw [Ne, Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot]
    exact_mod_cast hmpos.ne'
  unfold lev ordI at *
  rw [e, ← Associates.mk_mul_mk, Associates.count_mul (Associates.mk_ne_zero.2 (pow_ne_zero _ w.ne_bot))
    (Associates.mk_ne_zero.2 hmb) w.associates_irreducible, h1, Associates.mk_pow,
    Associates.count_pow (Associates.mk_ne_zero.2 w.ne_bot) w.associates_irreducible,
    Associates.count_self w.associates_irreducible]
  simp

private theorem dvd_of_norm (w : Pl ℚ) (𝔪 : Ideal (𝓞 ℚ)) (h : normV w ∣ Ideal.absNorm 𝔪) : w.asIdeal ∣ 𝔪 := by
  haveI : IsPrincipalIdealRing (𝓞 ℚ) :=
    IsPrincipalIdealRing.of_surjective Rat.ringOfIntegersEquiv.symm Rat.ringOfIntegersEquiv.symm.surjective
  obtain ⟨x, rfl⟩ : ∃ x, 𝔪 = Ideal.span {x} := (IsPrincipalIdealRing.principal 𝔪).principal
  obtain ⟨z, rfl⟩ : ∃ z : ℤ, x = algebraMap ℤ (𝓞 ℚ) z :=
    ⟨Rat.ringOfIntegersEquiv x, Rat.ringOfIntegersEquiv.injective (by simp)⟩
  rw [Ideal.absNorm_span_singleton, Algebra.norm_algebraMap, RingOfIntegers.rank, Module.finrank_self, pow_one] at h
  rw [(places w).2.1, Ideal.span_singleton_dvd_span_singleton_iff_dvd]
  simpa using map_dvd (algebraMap ℤ (𝓞 ℚ)) (Int.natCast_dvd.2 h)

private theorem hk_coef {k N : ℕ} (hN : 1 ≤ N) {χ : DirichletCharacter ℂ N} (g : Eigenform k N χ) (ω : HChar ℚ)
    (hval : ∀ w : Pl ℚ, ¬ normV w ∣ N → ((ω.val w : ℂˣ) : ℂ) = χ (normV w : ZMod N)) (w : Pl ℚ) (𝔪 : Ideal (𝓞 ℚ)) (h𝔪 : 𝔪 ≠ ⊥) :
    hkCoef k (lev N) ω w (icoef g.f) 𝔪 = g.a (normV w) * icoef g.f 𝔪 := by
  obtain ⟨hp, -, hn, -⟩ := places w
  have h1 : 1 ≤ Ideal.absNorm 𝔪 := Nat.pos_of_ne_zero (by simpa [Ideal.absNorm_eq_zero_iff] using h𝔪)
  have hχ : chiI ω (lev N) w.asIdeal = χ (normV w : ZMod N) := by
    rw [chi_prime, lev_eq N hN]
    by_cases hd : normV w ∣ N
    · rw [if_neg (hp.factorization_pos_of_dvd (by omega) hd).ne', MulChar.map_nonunit]
      rw [ZMod.isUnit_prime_iff_not_dvd hp]
      exact not_not.2 hd
    · rw [if_pos (Nat.factorization_eq_zero_of_not_dvd hd), hval w hd]
  have hd : coefDiv (icoef g.f) w.asIdeal 𝔪 =
      if normV w ∣ Ideal.absNorm 𝔪 then coef g.f (Ideal.absNorm 𝔪 / normV w) else 0 := by
    unfold coefDiv
    by_cases h : ∃ 𝔫, 𝔪 = w.asIdeal * 𝔫
    · have e := congrArg Ideal.absNorm h.choose_spec
      rw [map_mul, hn] at e
      rw [dite_eq_left h, if_pos ⟨_, e⟩, icoef]
      congr 1
      exact (Nat.div_eq_of_eq_mul_right hp.pos e).symm
    · rw [dite_eq_right h, if_neg fun h' => h (dvd_of_norm w 𝔪 h')]
  rw [hkCoef, hχ, hd, icoef, icoef, map_mul, hn]
  exact g.eig _ hp _ h1

end UpperTheory.V.Sd.AdelicUnramifiedNorms

open UpperTheory.V.Sd.AdelicUnramifiedNorms in
theorem UpperTheory.V.Sd.adelise :
    UpperTheory.V.Sd.Adelise := by
  intro k N _ hk2 χ g
  have hN : 1 ≤ N := NeZero.pos N
  have hk1 : 1 ≤ k := by omega
  obtain ⟨ω, hω⟩ := dirChar N hN χ
  obtain ⟨hfin, hval⟩ := charVal N hN χ ω hω
  obtain ⟨φ, hL, hH, hC⟩ := lift_hol k N hN χ ω hω g.f g.char
  have hE := liftExp k N hN g.f φ.1 hL
  obtain ⟨-, hz, hl1, hl2, -⟩ := holLin ℚ k (lev N) ω
  have h0 : φ ≠ 0 := by
    rintro rfl
    have := (expUnique ℚ _ k _ _ _ _ hE hz).2 ⊤ top_ne_bot
    rw [icoef, Ideal.absNorm_top, g.one] at this
    exact one_ne_zero this
  have hlev : (fun w : Pl ℚ => N.factorization (normV w)) = lev N := funext fun w => (lev_eq N hN w).symm
  refine ⟨ω, φ, hfin, fun w hw => ⟨unr_of_hol hH h0 ((places w).2.2.2 N hN hw), hval w hw⟩, ?_, hC⟩
  rw [hlev]
  refine ⟨hH, h0, fun w => ?_⟩
  obtain ⟨h1, -, h2⟩ := holHk ℚ k hk1 _ ω hfin φ hH w
  obtain ⟨c₀, h3⟩ := h2 _ _ hE
  have h4 := expInj ℚ k hk1 _ ω hfin _ (hl1 _ _ (-g.a (normV w)) h1 hH) _ _ (hl2 _ _ (-g.a (normV w)) _ _ _ _ h3 hE)
    fun 𝔪 h𝔪 => by simp [hk_coef hN g ω hval w 𝔪 h𝔪]
  rwa [neg_smul, add_neg_eq_zero] at h4
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.IdeleGenerators.HolomorphicIrreducibility.EigAut
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Polynomial GlobalTheory.GalOfCusp
open UpperTheory.V UpperTheory.V.Af
open scoped Matrix

private theorem ev_not_mem (N : ℕ) (hN : N ≠ 0) :
    ∀ᶠ w : HeightOneSpectrum (𝓞 ℚ) in Filter.cofinite, ((N : ℕ) : 𝓞 ℚ) ∉ w.asIdeal := by
  have h0 : Ideal.span {((N : ℕ) : 𝓞 ℚ)} ≠ 0 := by
    rw [Ne, Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot]
    exact_mod_cast hN
  refine Filter.eventually_cofinite.2 ((Ideal.finite_factors h0).subset fun w hw => ?_)
  simp only [Set.mem_setOf_eq, not_not] at hw
  exact Ideal.dvd_span_singleton.2 hw

private theorem cls_frob {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] (N : ℕ) [NeZero N]
    {A : ValuationSubring Ω} (hN : ¬ A.valuation (N : Ω) < 1) {q : ℕ} {σ : G ℚ Ω} (hσ : IsFrob A q σ) :
    ((Chr.cls ℚ Ω N σ : (ZMod N)ˣ) : ZMod N) = q := by
  obtain ⟨-, -, -, -, -, -, hpow, -⟩ := ML.placeBasic Ω
  haveI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed ℚ
  haveI : NeZero ((N : ℕ) : Ω) := ⟨Nat.cast_ne_zero.mpr (NeZero.ne N)⟩
  obtain ⟨ζ, hζ⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot Ω N
  have h2 : σ ζ = ζ ^ q := hpow A _ N _ hσ hN ζ hζ.pow_eq_one
  rw [Chr.cls_spec N σ ζ hζ.pow_eq_one, pow_eq_pow_mod q hζ.pow_eq_one] at h2
  have h3 := hζ.pow_inj (ZMod.val_lt _) (Nat.mod_lt _ (NeZero.pos N)) h2
  rw [← ZMod.natCast_zmod_val ((Chr.cls ℚ Ω N σ : (ZMod N)ˣ) : ZMod N), h3, ZMod.natCast_mod]
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.IdeleGenerators.HolomorphicIrreducibility.HolLift
section
noncomputable section

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.N Polynomial
open GlobalTheory.CuspRep GlobalTheory.HeckeGal GlobalTheory.GalOfCusp UpperTheory.V.Af UpperTheory.V.Base
open scoped Matrix

namespace UpperTheory.V.Sd

variable {F : Type} [Field F] [NumberField F]

private theorem val_pow (ω : HChar F) (w : Pl F) (n : ℕ) : (ω ^ n).val w = ω.val w ^ n := by
  induction n with
  | zero => simp [HChar.val, HChar.locK, HChar.loc]
  | succ n ih => rw [pow_succ, pow_succ, HChar.val_mul, ih]

private theorem norm_chiI {l : ℕ} [Fact l.Prime] (ι : Qbar l ≃+* ℂ) (ω : HChar F) (hω : IsOfFinOrder ω) (c : Pl F → ℕ)
    (I : Ideal (𝓞 F)) : ‖ι.symm (chiI ω c I)‖ ≤ 1 := by
  obtain ⟨n, hn, h⟩ := isOfFinOrder_iff_pow_eq_one.1 hω
  refine finprod_induction (fun x : ℂ => ‖ι.symm x‖ ≤ 1) (by simp) ?_ ?_
  · intro x y hx hy
    rw [map_mul, norm_mul]
    exact mul_le_one₀ hx (norm_nonneg _) hy
  · intro w
    rw [map_pow, norm_pow]
    refine pow_le_one₀ (norm_nonneg _) ?_
    split_ifs
    · have h1 : (ι.symm ((ω.val w : ℂˣ) : ℂ)) ^ n = 1 := by
        rw [← map_pow, ← Units.val_pow_eq_pow_val, ← val_pow, h, ← pow_zero ω, val_pow]; simp
      have h2 := congrArg norm h1
      rw [norm_pow, norm_one] at h2
      exact ((pow_eq_one_iff_of_nonneg (norm_nonneg _) hn.ne').1 h2).le
    · simp

private abbrev Idx (F : Type) [Field F] : Type := {𝔪 : Ideal (𝓞 F) // 𝔪 ≠ ⊥}


open Classical in
private def fT {K : Type} [Field K] (w : Pl F) (e : K) : Module.End K (Idx F → K) where
  toFun v 𝔪 := v ⟨w.asIdeal * 𝔪.1, mul_ne_zero w.ne_bot 𝔪.2⟩ +
    e * if h : ∃ 𝔫, 𝔪.1 = w.asIdeal * 𝔫 then
      v ⟨h.choose, fun h0 => 𝔪.2 (by rw [h.choose_spec, h0, Ideal.mul_bot])⟩ else 0
  map_add' c d := by
    funext n
    by_cases h : ∃ 𝔫, n.1 = w.asIdeal * 𝔫 <;> simp only [h, dif_pos, dif_neg, not_false_eq_true, Pi.add_apply] <;> ring
  map_smul' a c := by
    funext n
    by_cases h : ∃ 𝔫, n.1 = w.asIdeal * 𝔫 <;>
      simp only [h, dif_pos, dif_neg, not_false_eq_true, Pi.smul_apply, smul_eq_mul, RingHom.id_apply] <;> ring

open Classical in
omit [NumberField F] in
private theorem fT_apply {K : Type} [Field K] (w : Pl F) (e : K) (v : Idx F → K) (𝔪 : Idx F) :
    fT w e v 𝔪 = v ⟨w.asIdeal * 𝔪.1, mul_ne_zero w.ne_bot 𝔪.2⟩ +
    e * if h : ∃ 𝔫, 𝔪.1 = w.asIdeal * 𝔫 then
      v ⟨h.choose, fun h0 => 𝔪.2 (by rw [h.choose_spec, h0, Ideal.mul_bot])⟩ else 0 := rfl

variable [IsTotallyReal F]

private def SS (k : ℕ) (c : Pl F → ℕ) (ω : HChar F) : Submodule ℂ (TR.Sm F 2) where
  carrier := {φ | IsHol k c ω φ ∧ ∃ c₀ a, HasExp φ.1 k c₀ a}
  zero_mem' := ⟨(holLin F k c ω).1, _, _, (holLin F k c ω).2.1⟩
  add_mem' := by
    rintro φ ψ ⟨h1, c₀, a, h2⟩ ⟨h3, d₀, b, h4⟩
    have e1 := (holLin F k c ω).2.2.1 φ ψ 1 h1 h3
    have e2 := (holLin F k c ω).2.2.2.1 φ.1 ψ.1 1 _ _ _ _ h2 h4
    rw [one_smul] at e1 e2
    exact ⟨e1, _, _, e2⟩
  smul_mem' := by
    rintro z ψ ⟨h3, d₀, b, h4⟩
    have e1 := (holLin F k c ω).2.2.1 0 ψ z (holLin F k c ω).1 h3
    have e2 := (holLin F k c ω).2.2.2.1 0 ψ.1 z _ _ _ _ (holLin F k c ω).2.1 h4
    rw [zero_add] at e1 e2
    exact ⟨e1, _, _, e2⟩

private def cf {k : ℕ} {c : Pl F → ℕ} {ω : HChar F} (φ : SS k c ω) : Ideal (𝓞 F) → ℂ := φ.2.2.choose_spec.choose

private theorem cf_spec {k : ℕ} {c : Pl F → ℕ} {ω : HChar F} (φ : SS k c ω) : ∃ c₀, HasExp φ.1.1 k c₀ (cf φ) :=
  ⟨_, φ.2.2.choose_spec.choose_spec⟩

private theorem cf_eq {k : ℕ} {c : Pl F → ℕ} {ω : HChar F} (φ : SS k c ω) {c₀ a} (h : HasExp φ.1.1 k c₀ a) (𝔪 : Idx F) :
    cf φ 𝔪.1 = a 𝔪.1 := by
  obtain ⟨d, hd⟩ := cf_spec φ
  exact (expUnique F _ k _ _ _ _ hd h).2 _ 𝔪.2

private def Phi {l : ℕ} [Fact l.Prime] (ι : Qbar l ≃+* ℂ) (k : ℕ) (c : Pl F → ℕ) (ω : HChar F) :
    SS k c ω →ₛₗ[(ι.symm : ℂ →+* Qbar l)] (Idx F → Qbar l) where
  toFun φ 𝔪 := ι.symm (cf φ 𝔪.1)
  map_add' φ ψ := by
    funext 𝔪
    obtain ⟨_, h2⟩ := cf_spec φ
    obtain ⟨_, h4⟩ := cf_spec ψ
    have e2 := (holLin F k c ω).2.2.2.1 _ _ 1 _ _ _ _ h2 h4
    simp only [one_smul] at e2
    rw [cf_eq (φ + ψ) e2]
    simp
  map_smul' z ψ := by
    funext 𝔪
    obtain ⟨_, h4⟩ := cf_spec ψ
    have e2 := (holLin F k c ω).2.2.2.1 0 _ z _ _ _ _ (holLin F k c ω).2.1 h4
    simp only [zero_add] at e2
    rw [cf_eq (z • ψ) e2]
    simp

private theorem Phi_eq {l : ℕ} [Fact l.Prime] (ι : Qbar l ≃+* ℂ) {k : ℕ} {c : Pl F → ℕ} {ω : HChar F} (φ : SS k c ω) {c₀ a}
    (h : HasExp φ.1.1 k c₀ a) (𝔪 : Idx F) : Phi ι k c ω φ 𝔪 = ι.symm (a 𝔪.1) := congrArg ι.symm (cf_eq φ h 𝔪)

private theorem fT_Phi {l : ℕ} [Fact l.Prime] (ι : Qbar l ≃+* ℂ) {k : ℕ} {c : Pl F → ℕ} {ω : HChar F} (φ : SS k c ω) {c₀ a}
    (h : HasExp φ.1.1 k c₀ a) (w : Pl F) (𝔪 : Idx F) :
    fT w (ι.symm (chiI ω c w.asIdeal * (normV w : ℂ) ^ (k - 1))) (Phi ι k c ω φ) 𝔪 = ι.symm (hkCoef k c ω w a 𝔪.1) := by
  rw [fT_apply, Phi_eq ι φ h, hkCoef, map_add (f := _), map_mul ι.symm _ (coefDiv _ _ _), coefDiv]
  split_ifs with hd
  · rw [Phi_eq ι φ h]
  · rw [map_zero]

private def hkS {k : ℕ} (hk1 : 1 ≤ k) (c : Pl F → ℕ) {ω : HChar F} (hω : IsOfFinOrder ω) (w : Pl F) (φ : SS k c ω) : SS k c ω :=
  ⟨hk k w (c w) φ.1, (holHk F k hk1 c ω hω φ.1 φ.2.1 w).1, by
    obtain ⟨_, h⟩ := cf_spec φ
    obtain ⟨d, hd⟩ := (holHk F k hk1 c ω hω φ.1 φ.2.1 w).2.2 _ _ h
    exact ⟨d, _, hd⟩⟩

private theorem Phi_hkS {l : ℕ} [Fact l.Prime] (ι : Qbar l ≃+* ℂ) {k : ℕ} (hk1 : 1 ≤ k) (c : Pl F → ℕ) {ω : HChar F}
    (hω : IsOfFinOrder ω) (w : Pl F) (φ : SS k c ω) :
    fT w (ι.symm (chiI ω c w.asIdeal * (normV w : ℂ) ^ (k - 1))) (Phi ι k c ω φ) = Phi ι k c ω (hkS hk1 c hω w φ) := by
  funext 𝔪
  obtain ⟨_, h⟩ := cf_spec φ
  obtain ⟨d, hd⟩ := (holHk F k hk1 c ω hω φ.1 φ.2.1 w).2.2 _ _ h
  rw [fT_Phi ι φ h, Phi_eq ι (hkS hk1 c hω w φ) hd]

private theorem Phi_inj {l : ℕ} [Fact l.Prime] (ι : Qbar l ≃+* ℂ) {k : ℕ} (hk1 : 1 ≤ k) (c : Pl F → ℕ) {ω : HChar F}
    (hω : IsOfFinOrder ω) : Function.Injective (Phi ι k c ω) := by
  set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
  intro φ h0
  obtain ⟨_, h⟩ := cf_spec φ
  refine Subtype.ext (expInj F k hk1 c ω hω φ.1 φ.2.1 _ _ h fun 𝔪 h𝔪 => ?_)
  have := congrFun h0 ⟨𝔪, h𝔪⟩
  rw [Phi_eq ι φ h] at this
  simpa using this

end UpperTheory.V.Sd
end
end

