module

public import Mathlib
public import ReciprocityTheory.Hypotheses.GalCoh
public import Formalism.GaloisCohomology.LocalTateDualityK
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FiniteDimensionalAdjoinRange
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0236
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0157
public import CompanionTheory.AutomorphicTheory.PadicCyclotomicFields.GcohTop
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RankOfMulEqOne
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0036
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.UnitLemmaGroup
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0115
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0141
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0002

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsMulEquiv
section
open NumberField IsDedekindDomain CategoryTheory GroundTheory.ProfCoh Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.GaloisCohomology

noncomputable section

namespace GlobalTheory.LocalDualityAll

def cycP (p : ℕ) [Fact p.Prime] (K : IntermediateField ℚ_[p] (PadicAlgCl p)) (l : ℕ) [Fact l.Prime] (r : ℕ) :
    GK p K →* (ZMod (l ^ r))ˣ :=
  (Units.map (PadicInt.toZModPow r : ℤ_[l] →+* ZMod (l ^ r)).toMonoidHom).comp
    ((cyclotomicCharacter (PadicAlgCl p) l).comp
      (MulSemiringAction.toRingAut (GK p K) (PadicAlgCl p)))

theorem localCyclotomicCharacter_spec (p : ℕ) [Fact p.Prime] (K : IntermediateField ℚ_[p] (PadicAlgCl p)) (l : ℕ) [hl : Fact l.Prime]
    (r : ℕ) (σ : GK p K) (ζ : PadicAlgCl p) (hζ : ζ ^ (l ^ r) = 1) :
    σ ζ = ζ ^ ((cycP p K l r σ : ZMod (l ^ r)).val) := by
  have : NeZero ((l : ℕ) : PadicAlgCl p) := ⟨Nat.cast_ne_zero.mpr hl.out.ne_zero⟩
  exact cyclotomicCharacter.spec l (MulSemiringAction.toRingAut _ (PadicAlgCl p) σ) ζ hζ

theorem exists_mulEquiv (F Ω : Type) [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω]
    (p : ℕ) [Fact p.Prime] (l : ℕ) [Fact l.Prime] (v : HeightOneSpectrum (𝓞 F)) (A : ValuationSubring Ω)
    (hv : ((p : ℕ) : 𝓞 F) ∈ v.asIdeal) (hA : IsPlaceOver A v) :
    ∃ (K : IntermediateField ℚ_[p] (PadicAlgCl p)) (_ : FiniteDimensional ℚ_[p] K) (e : Dec (F := F) A ≃* GK p K),
      Continuous e ∧ Continuous e.symm ∧
        ∀ (r : ℕ) (g : Dec (F := F) A), cycP p K l r (e g) = cycMod F Ω l r (g : G F Ω) := by
  obtain ⟨j, hj⟩ := GlobalTheory.PlaceBridge.exists_embedding (l := p) F Ω v A hv hA
  let K : Formalism.BasicNotions.Loc.FinExt p :=
    ⟨IntermediateField.adjoin ℚ_[p] (Set.range fun x : F => j (algebraMap F Ω x)),
      GlobalTheory.PlaceBridge.finiteDimensional_adjoin_range (j.comp (algebraMap F Ω))⟩
  have hK := K.2
  obtain ⟨e, he, he', hec⟩ := GlobalTheory.PlaceBridge.exists_mulEquiv (E := F) hj K rfl
  obtain ⟨hf, hf'⟩ := GlobalTheory.fixingSubgroupEquiv_bicontinuous ℚ_[p] (PadicAlgCl p) K.1
  refine ⟨K.1, hK, e.trans (IntermediateField.fixingSubgroupEquiv K.1), hf.comp he, he'.comp hf',
    fun r g => Units.ext ?_⟩
  have hl : l.Prime := Fact.out
  have : IsAlgClosed Ω := IsAlgClosure.isAlgClosed F
  have : CharZero Ω := j.charZero
  have : NeZero ((l : ℕ) : Ω) := ⟨Nat.cast_ne_zero.mpr hl.ne_zero⟩
  have : NeZero (l ^ r) := ⟨pow_ne_zero _ hl.ne_zero⟩
  obtain ⟨ζ, hζ⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot Ω (l ^ r)
  have hζ' := hζ.map_of_injective j.injective
  have ha : (g : Ω ≃ₐ[F] Ω) ζ = ζ ^ ((cycMod F Ω l r (g : G F Ω) : ZMod (l ^ r))).val :=
    cyclotomicCharacter.spec l (MulSemiringAction.toRingAut (Ω ≃ₐ[F] Ω) Ω (g : Ω ≃ₐ[F] Ω)) ζ
      hζ.pow_eq_one
  set σ : GK p K.1 := (e.trans (IntermediateField.fixingSubgroupEquiv K.1)) g with hσ
  have hb : σ (j ζ) = j ζ ^ ((cycP p K.1 l r σ : ZMod (l ^ r))).val :=
    localCyclotomicCharacter_spec p K.1 l r σ _ hζ'.pow_eq_one
  have hc : σ (j ζ) = j ((g : Ω ≃ₐ[F] Ω) ζ) := hec g ζ
  rw [hc, ha, map_pow] at hb
  exact (ZMod.val_injective _ (hζ'.pow_inj (ZMod.val_lt _) (ZMod.val_lt _) hb)).symm

theorem exists_mu (p : ℕ) [Fact p.Prime] (K : IntermediateField ℚ_[p] (PadicAlgCl p)) (l : ℕ) [hl : Fact l.Prime]
    (r : ℕ) : ∃ e : ZMod (l ^ r) ≃+ (galRootsOfUnity.{0} ↥K (PadicAlgCl p) (l ^ r)).V,
      ∀ (g : GK p K) (m : ZMod (l ^ r)), e ((cycP p K l r g : ZMod (l ^ r)) * m) =
        (galRootsOfUnity.{0} ↥K (PadicAlgCl p) (l ^ r)).ρ g (e m) := by
  have : IsSepClosure ↥K (PadicAlgCl p) :=
    ⟨inferInstance, Algebra.isSeparable_tower_top_of_isSeparable ℚ_[p] K _⟩
  have hn : ((l ^ r : ℕ) : K) ≠ 0 := Nat.cast_ne_zero.2 (pow_ne_zero _ hl.out.ne_zero)
  have : NeZero (l ^ r) := ⟨pow_ne_zero _ hl.out.ne_zero⟩
  obtain ⟨e⟩ := nonempty_addEquiv_galRootsOfUnity (K := K) (Ksep := PadicAlgCl p) hn
  refine ⟨e.symm, fun g m => ?_⟩
  have key : ∀ x : Additive (rootsOfUnity (l ^ r) (PadicAlgCl p)),
      (galRootsOfUnity.{0} ↥K (PadicAlgCl p) (l ^ r)).ρ g x =
        (cycP p K l r g : ZMod (l ^ r)).val • x := by
    intro x
    rw [galRootsOfUnity_ρ_apply]
    apply Additive.toMul.injective
    rw [toMul_ofMul, toMul_nsmul]
    apply Subtype.ext
    apply Units.ext
    rw [coe_galRootsOfUnityHom_apply, SubmonoidClass.coe_pow, Units.val_pow_eq_pow_val]
    refine localCyclotomicCharacter_spec p K l r g _ ?_
    rw [← Units.val_pow_eq_pow_val, (mem_rootsOfUnity _ _).1 x.toMul.2, Units.val_one]
  refine Eq.trans ?_ (key _).symm
  refine Eq.trans ?_ (map_nsmul e.symm _ m)
  rw [nsmul_eq_mul, ZMod.natCast_zmod_val]

theorem tate_p (p : ℕ) [Fact p.Prime] (K : IntermediateField ℚ_[p] (PadicAlgCl p)) (hK : FiniteDimensional ℚ_[p] K)
    (l : ℕ) [Fact l.Prime] (r : ℕ) (M : Type) [AddCommGroup M] [Module (ZMod (l ^ r)) M]
    [Finite M] [TopologicalSpace M] [DiscreteTopology M]
    (rho : Representation (ZMod (l ^ r)) (GK p K) M) (hrho : ContAction rho) :
    Nonempty (H2 (charRep (cycP p K l r)) ≃ₗ[ZMod (l ^ r)] ZMod (l ^ r)) ∧
    Function.Bijective (cupH0H2TwistedDual (cycP p K l r) rho (MonoidHom.id _)) ∧
    Function.Bijective (cupH1H1TwistedDual (cycP p K l r) rho (MonoidHom.id _) (hrho.comp' continuous_id)) ∧
    Function.Bijective (cupH1H1TwistedDual (cycP p K l r) rho (MonoidHom.id _) (hrho.comp' continuous_id)).flip ∧
    Function.Bijective (cup20 (cycP p K l r) rho (MonoidHom.id _)) := by
  obtain ⟨hsep, _, _, hloc, -⟩ := CompanionTheory.LocalTateOrthogonality.Gcoh.gcField p K hK
  have hl : (l ^ r : ℕ) ≠ 0 := pow_ne_zero _ (Fact.out : l.Prime).ne_zero
  have : NeZero (l ^ r) := ⟨hl⟩
  have : CharZero K := algebraRat.charZero K
  have hn : ((l ^ r : ℕ) : K) ≠ 0 := Nat.cast_ne_zero.2 hl
  obtain ⟨eD, hD⟩ := exists_mu p K l r
  exact CompanionTheory.LocalTateOrthogonality.Gcoh.tate_core CompanionTheory.LocalTateOrthogonality.Gcoh.gcRep CompanionTheory.LocalTateOrthogonality.Gcoh.gc0 CompanionTheory.LocalTateOrthogonality.Gcoh.gc1 CompanionTheory.LocalTateOrthogonality.Gcoh.gc2
    (galRootsOfUnity.{0} K (PadicAlgCl p) (l ^ r)) (localDualityHypotheses hn)
    (fun A _ _ hA => finite_cohomology_galois_top K (PadicAlgCl p) hn A hA 1)
    (cycP p K l r) eD hD M rho hrho

theorem exists_prime_mem {F : Type} [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F)) :
    ∃ p : ℕ, p.Prime ∧ ((p : ℕ) : 𝓞 F) ∈ v.asIdeal := by
  have hmax := v.isMaximal
  letI : Field (𝓞 F ⧸ v.asIdeal) := Ideal.Quotient.field v.asIdeal
  have hfin : Finite (𝓞 F ⧸ v.asIdeal) := Ideal.finiteQuotientOfFreeOfNeBot _ v.ne_bot
  obtain ⟨p, hp⟩ := CharP.exists (𝓞 F ⧸ v.asIdeal)
  refine ⟨p, CharP.char_is_prime (𝓞 F ⧸ v.asIdeal) p, ?_⟩
  rw [← Ideal.Quotient.eq_zero_iff_mem, map_natCast]
  exact CharP.cast_eq_zero _ p

theorem localTateDuality : ReciprocityTheory.Gal.LocalTateDuality := by
  intro F Ω _ _ _ _ _ l _ r M _ _ _ _ _ A rho v hr hA hc
  obtain ⟨p, hp, hpv⟩ := exists_prime_mem v
  haveI : Fact p.Prime := ⟨hp⟩
  obtain ⟨K, hK, e, he, he', hcyc⟩ := exists_mulEquiv F Ω p l v A hpv hA
  have hc' : ContAction (rho.comp e.symm.toMonoidHom) := hc.comp' he'
  have hχ : ((cycMod F Ω l r).comp (Dec (F := F) A).subtype).comp e.symm.toMonoidHom = cycP p K l r := by
    ext1 σ
    have := hcyc r (e.symm σ)
    rw [e.apply_symm_apply] at this
    exact this.symm
  refine GlobalTheory.CohTransport.dualityClauses_of_mulEquiv (ZMod (l ^ r)) _ _ M e.symm he' he _ rho hc hc' ?_
  rw [hχ]
  exact tate_p p K hK l r M _ hc'

end GlobalTheory.LocalDualityAll
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsMulVecEqPow
section
set_option autoImplicit false

noncomputable section

open PowerSeries Formalism.CohomologicalDescent Formalism.CohomologicalDescent.HeightDescentMinors Formalism.CohomologicalDescent.FrobeniusPeriodChange

namespace GlobalTheory.WachPlace

section Columns

variable {F : Type} [Field F] {a b c : ℕ}

def vecL (y : Fin a → F⟦X⟧) : Fin a → LaurentSeries F := fun j => algebraMap F⟦X⟧ (LaurentSeries F) (y j)

def linL (A : Mx F⟦X⟧ a b) : (Fin b → LaurentSeries F) →ₗ[LaurentSeries F] (Fin a → LaurentSeries F) :=
  (A.map (algebraMap F⟦X⟧ (LaurentSeries F))).mulVecLin

def colL (A : Mx F⟦X⟧ a b) : Submodule (LaurentSeries F) (Fin a → LaurentSeries F) := LinearMap.range (linL A)

theorem finrank_colL (A : Mx F⟦X⟧ a b) : Module.finrank (LaurentSeries F) (colL A) = lrank A := rfl

theorem linL_vecL (A : Mx F⟦X⟧ a b) (y : Fin b → F⟦X⟧) : linL A (vecL y) = vecL (A.mulVec y) := by
  funext j
  exact (RingHom.map_mulVec (algebraMap F⟦X⟧ (LaurentSeries F)) A y j).symm

theorem linL_mul (A : Mx F⟦X⟧ a b) (B : Mx F⟦X⟧ b c) : linL (A * B) = (linL A).comp (linL B) := by
  rw [linL, Matrix.map_mul, Matrix.mulVecLin_mul]
  rfl

theorem vecL_smul (s : F⟦X⟧) (y : Fin a → F⟦X⟧) : vecL (s • y) = algebraMap F⟦X⟧ (LaurentSeries F) s • vecL y := by
  funext j
  simp only [vecL, Pi.smul_apply, smul_eq_mul, map_mul]

theorem vecL_sub (y z : Fin a → F⟦X⟧) : vecL (y - z) = vecL y - vecL z := by
  funext j
  simp only [vecL, Pi.sub_apply, map_sub]

theorem vecL_injective : Function.Injective (vecL : (Fin a → F⟦X⟧) → _) := fun _ _ h =>
  funext fun j => IsFractionRing.injective F⟦X⟧ (LaurentSeries F) (congrFun h j)

theorem colL_mul_le (A : Mx F⟦X⟧ a b) (B : Mx F⟦X⟧ b c) : colL (A * B) ≤ colL A := by
  rw [colL, linL_mul]
  exact LinearMap.range_comp_le_range _ _

theorem colL_eq_top {A : Mx F⟦X⟧ a b} (h : lrank A = a) : colL A = ⊤ :=
  Submodule.eq_top_of_finrank_eq (by rw [finrank_colL, h, Module.finrank_fin_fun])

theorem colL_mul_eq (A : Mx F⟦X⟧ a b) {B : Mx F⟦X⟧ b c} (h : lrank B = b) : colL (A * B) = colL A := by
  rw [colL, linL_mul]
  exact LinearMap.range_comp_of_range_eq_top _ (colL_eq_top h)

theorem exists_clear (z : Fin a → LaurentSeries F) :
    ∃ (m : ℕ) (w : Fin a → F⟦X⟧), vecL w = algebraMap F⟦X⟧ (LaurentSeries F) (X ^ m) • z := by
  obtain ⟨s, hs⟩ := IsLocalization.exist_integer_multiples_of_finite (Submonoid.powers (X : F⟦X⟧)) z
  obtain ⟨m, hm⟩ := s.2
  choose w hw using hs
  refine ⟨m, w, funext fun j => ?_⟩
  rw [vecL, hw j, ← hm, Pi.smul_apply, smul_eq_mul, Algebra.smul_def]

theorem semilin_mem (θ : F⟦X⟧ →+* F⟦X⟧) (hθ : θ X ≠ 0) {M : Mx F⟦X⟧ a a} {M' : Mx F⟦X⟧ b b} {A A' : Mx F⟦X⟧ a b}
    (h : M * A'.map θ = A * M') {y : Fin a → F⟦X⟧} (hy : vecL y ∈ colL A') :
    vecL (M.mulVec fun j => θ (y j)) ∈ colL A := by
  obtain ⟨z, hz⟩ := hy
  obtain ⟨m, w, hw⟩ := exists_clear z
  have e1 : A'.mulVec w = (X : F⟦X⟧) ^ m • y := by
    apply vecL_injective
    rw [← linL_vecL, hw, map_smul, hz, vecL_smul]
  have e2 : (A'.map θ).mulVec (fun j => θ (w j)) = θ X ^ m • fun j => θ (y j) := by
    funext j
    have := RingHom.map_mulVec θ A' w j
    rw [e1] at this
    rw [show (fun j => θ (w j)) = θ ∘ w from rfl, ← this]
    simp
  have e3 : θ X ^ m • (M.mulVec fun j => θ (y j)) = A.mulVec (M'.mulVec fun j => θ (w j)) := by
    rw [Matrix.mulVec_mulVec, ← h, ← Matrix.mulVec_mulVec, e2, Matrix.mulVec_smul]
  have h0 : algebraMap F⟦X⟧ (LaurentSeries F) (θ X ^ m) ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective F⟦X⟧ (LaurentSeries F))).2 (pow_ne_zero _ hθ)
  rw [← Submodule.smul_mem_iff _ h0, ← vecL_smul, e3, ← linL_vecL]
  exact LinearMap.mem_range_self _ _

theorem ker_eq_colL {C : Mx F⟦X⟧ 1 (a + 1)} {E : Mx F⟦X⟧ (a + 1) a} (h : C * E = 0) (hE : lrank E = a)
    (hC : lrank C = 1) : LinearMap.ker (linL C) = colL E := by
  symm
  apply Submodule.eq_of_le_of_finrank_eq
  · rintro _ ⟨z, rfl⟩
    rw [LinearMap.mem_ker, ← LinearMap.comp_apply, ← linL_mul, h]
    simp [linL]
  · have := LinearMap.finrank_range_add_finrank_ker (linL C)
    rw [← colL, finrank_colL, hC, Module.finrank_fin_fun] at this
    rw [finrank_colL, hE]
    omega

theorem exists_mulVec_eq_pow {C : Mx F⟦X⟧ 1 a} (hC : lrank C = 1) :
    ∃ (y : Fin a → F⟦X⟧) (m : ℕ), C.mulVec y = fun _ => X ^ m := by
  obtain ⟨z, hz⟩ : (fun _ => 1 : Fin 1 → LaurentSeries F) ∈ colL C := by
    rw [colL_eq_top hC]
    trivial
  obtain ⟨m, w, hw⟩ := exists_clear z
  refine ⟨w, m, vecL_injective ?_⟩
  rw [← linL_vecL, hw, map_smul, hz]
  funext j
  simp [vecL]

theorem line_rel (θ : F⟦X⟧ →+* F⟦X⟧) {M : Mx F⟦X⟧ a a} {M₂ : Mx F⟦X⟧ (a + 1) (a + 1)} {M₁ : Mx F⟦X⟧ 1 1}
    {B B' : Mx F⟦X⟧ a (a + 1)} {C C' : Mx F⟦X⟧ 1 (a + 1)} {E : Mx F⟦X⟧ (a + 1) a}
    (hB : M * B'.map θ = B * M₂) (hC : M₁ * C'.map θ = C * M₂) (h : C * E = 0) (hE : lrank E = a)
    (hC1 : lrank C = 1) {y y' : Fin (a + 1) → F⟦X⟧} {m m' : ℕ} (hy : C.mulVec y = fun _ => X ^ m)
    (hy' : C'.mulVec y' = fun _ => X ^ m') :
    algebraMap F⟦X⟧ (LaurentSeries F) X ^ m • vecL (M.mulVec fun j => θ (B'.mulVec y' j)) -
      (algebraMap F⟦X⟧ (LaurentSeries F) (θ X) ^ m' * algebraMap F⟦X⟧ (LaurentSeries F) (M₁ 0 0)) •
        vecL (B.mulVec y) ∈ colL (B * E) := by
  have e : ∀ {k : ℕ} (A : Mx F⟦X⟧ k (a + 1)), (fun j => θ (A.mulVec y' j)) = (A.map θ).mulVec fun j => θ (y' j) :=
    fun A => funext fun j => RingHom.map_mulVec θ A y' j
  let z : Fin (a + 1) → F⟦X⟧ := (X : F⟦X⟧) ^ m • (M₂.mulVec fun j => θ (y' j)) - (θ X ^ m' * M₁ 0 0) • y
  have hz : C.mulVec z = 0 := by
    simp only [z, Matrix.mulVec_sub, Matrix.mulVec_smul, Matrix.mulVec_mulVec, ← hC]
    rw [← Matrix.mulVec_mulVec, ← e, hy, hy']
    funext j
    rw [Subsingleton.elim j 0]
    simp [Matrix.mulVec, dotProduct]
    ring
  have hk : vecL z ∈ colL E := by
    rw [← ker_eq_colL h hE hC1, LinearMap.mem_ker, linL_vecL, hz]
    funext j
    simp [vecL]
  obtain ⟨v, hv⟩ := hk
  refine ⟨v, ?_⟩
  rw [linL_mul, LinearMap.comp_apply, hv, linL_vecL]
  simp only [z, Matrix.mulVec_sub, Matrix.mulVec_smul, Matrix.mulVec_mulVec, ← hB]
  rw [← Matrix.mulVec_mulVec, ← e, vecL_sub, vecL_smul, vecL_smul, map_pow, map_mul, map_pow]

theorem colL_eq_sup {B : Mx F⟦X⟧ a (a + 1)} {C : Mx F⟦X⟧ 1 (a + 1)} {E : Mx F⟦X⟧ (a + 1) a} (h : C * E = 0)
    (hE : lrank E = a) (hC1 : lrank C = 1) {y : Fin (a + 1) → F⟦X⟧} {m : ℕ} (hy : C.mulVec y = fun _ => X ^ m) :
    colL B = colL (B * E) ⊔ Submodule.span (LaurentSeries F) {vecL (B.mulVec y)} := by
  apply le_antisymm
  · rintro _ ⟨z, rfl⟩
    have h0 : algebraMap F⟦X⟧ (LaurentSeries F) (X ^ m) ≠ 0 :=
      (map_ne_zero_iff _ (IsFractionRing.injective F⟦X⟧ (LaurentSeries F))).2 (pow_ne_zero _ X_ne_zero)
    let s : LaurentSeries F := linL C z 0 / algebraMap F⟦X⟧ (LaurentSeries F) (X ^ m)
    have hk : z - s • vecL y ∈ colL E := by
      rw [← ker_eq_colL h hE hC1, LinearMap.mem_ker, map_sub, map_smul, linL_vecL, hy]
      funext j
      rw [Subsingleton.elim j 0, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, vecL, div_mul_cancel₀ _ h0, sub_self]
      rfl
    obtain ⟨v, hv⟩ := hk
    have : linL B z = linL (B * E) v + s • vecL (B.mulVec y) := by
      rw [linL_mul, LinearMap.comp_apply, hv, map_sub, map_smul, linL_vecL, sub_add_cancel]
    rw [this]
    exact Submodule.add_mem_sup (LinearMap.mem_range_self _ _)
      (Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self _))
  · refine sup_le (colL_mul_le _ _) ?_
    rw [Submodule.span_singleton_le_iff_mem, ← linL_vecL]
    exact LinearMap.mem_range_self _ _

end Columns

theorem filtration_of_chain {F : Type} [Field F] {ι : Type} (σ : Equiv.Perm ι) {l n t R : ℕ} (hl : 0 < l) (un : F⟦X⟧)
    (P D : ι → Mx F⟦X⟧ n n) (Pψ Dψ : Fin t → ι → Mx F⟦X⟧ 1 1) (rs : Fin t → Fin R) (dim : Fin (R + 1) → ℕ)
    (y : ι → Slot F n t R) (h0 : dim 0 = 0) (hR : dim (Fin.last R) = n)
    (hs : ∀ s, dim (rs s).succ = dim (rs s).castSucc + 1)
    (hy : ∀ i, (y i).Chain (y (σ i)) l un (P i) (D i) (fun s => Pψ s i) (fun s => Dψ s i) rs dim) :
    ∃ (V : ι → Fin (R + 1) → Submodule (LaurentSeries F) (Fin n → LaurentSeries F))
      (e : ι → Fin t → Fin n → F⟦X⟧) (m : ι → Fin t → ℤ),
      (∀ i, V i 0 = ⊥ ∧ V i (Fin.last R) = ⊤ ∧ Monotone (V i)) ∧
      (∀ k i j, Module.finrank (LaurentSeries F) (V i k) = Module.finrank (LaurentSeries F) (V j k)) ∧
      (∀ i k v, vecL v ∈ V (σ i) k → vecL ((P i).mulVec fun a => frob0 l (v a)) ∈ V i k) ∧
      (∀ i k v, vecL v ∈ V i k → vecL ((1 + (X : F⟦X⟧) • D i).mulVec fun a => gam0 0 un (v a)) ∈ V i k) ∧
      (∀ i s, vecL (e i s) ∉ V i (rs s).castSucc ∧
        V i (rs s).succ = V i (rs s).castSucc ⊔ Submodule.span (LaurentSeries F) {vecL (e i s)}) ∧
      (∀ i s, (((X : F⟦X⟧) : LaurentSeries F) ^ m i s) • vecL ((P i).mulVec fun a => frob0 l (e (σ i) s a)) -
        (((X : F⟦X⟧) : LaurentSeries F) ^ ((l : ℤ) * m (σ i) s) * ((Pψ s i 0 0 : F⟦X⟧) : LaurentSeries F)) •
          vecL (e i s) ∈ V i (rs s).castSucc) ∧
      ∀ i s, (((X : F⟦X⟧) : LaurentSeries F) ^ m i s) •
          vecL ((1 + (X : F⟦X⟧) • D i).mulVec fun a => gam0 0 un (e i s a)) -
        (((gamSer 0 un : F⟦X⟧) : LaurentSeries F) ^ m i s *
          ((1 + X * Dψ s i 0 0 : F⟦X⟧) : LaurentSeries F)) • vecL (e i s) ∈ V i (rs s).castSucc := by
  have h1 : HasSubst (X ^ l : F⟦X⟧) := HasSubst.X_pow hl.ne'
  have h2 : HasSubst (gamSer 0 un) := HasSubst.of_constantCoeff_zero' (by simp [gamSer])
  obtain ⟨φ, hφ⟩ : ∃ φ : F⟦X⟧ →+* F⟦X⟧, ⇑φ = frob0 l := ⟨(substAlgHom h1 : F⟦X⟧ →ₐ[F] F⟦X⟧), coe_substAlgHom h1⟩
  obtain ⟨γ, hγ⟩ : ∃ γ : F⟦X⟧ →+* F⟦X⟧, ⇑γ = gam0 0 un := ⟨(substAlgHom h2 : F⟦X⟧ →ₐ[F] F⟦X⟧), coe_substAlgHom h2⟩
  have hφX : φ X = X ^ l := by rw [hφ, frob0, subst_X h1]
  have hγX : γ X = gamSer 0 un := by rw [hγ, gam0, subst_X h2]
  have hγ0 : γ X ≠ 0 := by
    rw [hγX, gamSer]
    refine mul_ne_zero X_ne_zero fun h => ?_
    simpa using congrArg constantCoeff h
  choose w m hw using fun i s => exists_mulVec_eq_pow ((hy i).2.2 s).2.2.2.2.2.2.1
  have hsup : ∀ i s, colL ((y i).A (rs s).succ) =
      colL ((y i).A (rs s).castSucc) ⊔ Submodule.span (LaurentSeries F) {vecL (((y i).B s).mulVec (w i s))} := by
    intro i s
    obtain ⟨-, -, e1, e2, e3, e4, e5, e6⟩ := (hy i).2.2 s
    rw [← e1, ← colL_eq_sup e2 e4 e5 (hw i s), e3, colL_mul_eq _ e6]
  refine ⟨fun i k => colL ((y i).A k), fun i s => ((y i).B s).mulVec (w i s), fun i s => m i s,
    fun i => ⟨?_, colL_eq_top (((hy i).1 _).2.trans hR), ?_⟩, fun k i j => ?_, fun i k v hv => ?_, fun i k v hv => ?_,
    fun i s => ⟨fun hm => ?_, hsup i s⟩, fun i s => ?_, fun i s => ?_⟩
  · exact Submodule.finrank_eq_zero.1 ((finrank_colL _).trans (((hy i).1 _).2.trans h0))
  · refine Fin.monotone_iff_le_succ.2 fun k => ?_
    exact (congrArg colL ((hy i).2.1 k)).trans_le (colL_mul_le _ _)
  · rw [finrank_colL, finrank_colL, ((hy i).1 k).2, ((hy j).1 k).2]
  · rw [← hφ]
    exact semilin_mem φ (by rw [hφX]; exact pow_ne_zero _ X_ne_zero) (hφ ▸ ((hy i).1 k).1.1) hv
  · rw [← hγ]
    exact semilin_mem γ hγ0 (hγ ▸ ((hy i).1 k).1.2) hv
  · have e := hsup i s
    rw [sup_eq_left.2 ((Submodule.span_singleton_le_iff_mem _ _).2 hm)] at e
    have e' := finrank_colL ((y i).A (rs s).succ)
    rw [e, finrank_colL, ((hy i).1 _).2, ((hy i).1 _).2, hs] at e'
    omega
  · obtain ⟨b1, c1, e1, e2, -, e4, e5, -⟩ := (hy i).2.2 s
    have := line_rel φ (hφ ▸ b1.1) (hφ ▸ c1.1) e2 e4 e5 (hw i s) (hw (σ i) s)
    rw [e1, hφX, hφ, map_pow, ← pow_mul] at this
    rw [← Nat.cast_mul, zpow_natCast, zpow_natCast]
    exact this
  · obtain ⟨b1, c1, e1, e2, -, e4, e5, -⟩ := (hy i).2.2 s
    have := line_rel γ (hγ ▸ b1.2) (hγ ▸ c1.2) e2 e4 e5 (hw i s) (hw i s)
    rw [e1, hγX, hγ, Matrix.add_apply, Matrix.one_apply_eq, Matrix.smul_apply, smul_eq_mul] at this
    rw [zpow_natCast, zpow_natCast]
    exact this

end GlobalTheory.WachPlace

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsNormOfEqualGramTraceForms
section
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.UnitLemma.IsometryUnit

theorem isometry_unit : ∀ (K : GlobalTheory.UnitLemma.UQ) (B : GlobalTheory.UnitLemma.InvAlg K), B.P.Separable → ∀ (ε : B.A), (ε = 1 ∨ ε = -1) → ∀ (a : ℕ) (β β' : B.Aˣ), B.σ (β : B.A) = β * (ε * B.g) → B.σ (β' : B.A) = β' * (ε * B.g) → ∀ b b' : Module.Basis (Fin a) K.E B.A, (∀ i j, B.herm β (b i) (b j) = B.herm β' (b' i) (b' j)) → ∃ t : B.Aˣ, (β' : B.A) = β * (t * B.σ t) := by
  intro K B hs ε hε a β β' hβ hβ' b b' hgram
  have hs' : (LinearMap.mulLeft K.E B.g).charpoly.Separable := hs
  have σsm : ∀ (r : K.E) (y : B.A), B.σ (r • y) = K.c r • B.σ y := by
    intro r y; rw [Algebra.smul_def, map_mul, B.σ_alg, Algebra.smul_def]
  have trσ := GlobalTheory.UnitLemma.PairClass.trace_σ K B
  have addL : ∀ (x u u' v : B.A), B.herm x (u + u') v = B.herm x u v + B.herm x u' v := by
    intro x u u' v; unfold InvAlg.herm; rw [mul_add, add_mul, map_add (f := _)]
  have subL : ∀ (x u u' v : B.A), B.herm x (u - u') v = B.herm x u v - B.herm x u' v := by
    intro x u u' v; unfold InvAlg.herm; rw [mul_sub, sub_mul, map_sub]
  have smulL : ∀ (x : B.A) (r : K.E) (u v : B.A), B.herm x (r • u) v = r * B.herm x u v := by
    intro x r u v; unfold InvAlg.herm; rw [mul_smul_comm, smul_mul_assoc, map_smul, smul_eq_mul]
  have addR : ∀ (x u v v' : B.A), B.herm x u (v + v') = B.herm x u v + B.herm x u v' := by
    intro x u v v'; unfold InvAlg.herm; rw [map_add (f := _), mul_add, map_add (f := _)]
  have smulR : ∀ (x : B.A) (r : K.E) (u v : B.A), B.herm x u (r • v) = K.c r * B.herm x u v := by
    intro x r u v; unfold InvAlg.herm; rw [σsm, mul_smul_comm, map_smul, smul_eq_mul]

  have asym : ∀ (x : B.A), B.σ x = x * (ε * B.g) → ∀ z y, K.c (B.herm x z y) = B.herm x (ε * B.g * y) z := by
    intro x hx z y; unfold InvAlg.herm
    rw [← trσ]; congr 1; simp only [map_mul, B.σ_σ, hx]; ring

  have nd : ∀ x : B.A, (∀ y, Algebra.trace K.E B.A (x * y) = 0) → x = 0 :=
    fun x hx => GlobalTheory.UnitLemma.PairClass.trace_nondeg K.E B.A B.g hs' x hx
  have ndh : ∀ w : B.A, (∀ z, B.herm β w z = 0) → w = 0 := by
    intro w hw
    have h0 : (β : B.A) * w = 0 := nd _ (fun y => by
      have := hw (B.σ y); unfold InvAlg.herm at this; rwa [B.σ_σ] at this)
    have := congrArg (fun z => ((β⁻¹ : B.Aˣ) : B.A) * z) h0
    simpa [← mul_assoc] using this

  let φ : B.A ≃ₗ[K.E] B.A := b'.equiv b (Equiv.refl _)
  have hφb : ∀ i, φ (b' i) = b i := fun i => by simp [φ, Module.Basis.equiv_apply]
  have hφ : ∀ u v, B.herm β (φ u) (φ v) = B.herm β' u v := by
    let F₁ : B.A →ₗ[K.E] B.A →ₛₗ[(K.c : K.E →+* K.E)] K.E :=
      LinearMap.mk₂'ₛₗ (RingHom.id K.E) (K.c : K.E →+* K.E) (fun u v => B.herm β (φ u) (φ v))
        (fun u u' v => by rw [map_add (f := _), addL]) (fun r u v => by rw [map_smul, smulL]; rfl)
        (fun u v v' => by rw [map_add (f := _), addR]) (fun r u v => by rw [map_smul, smulR]; rfl)
    let F₂ : B.A →ₗ[K.E] B.A →ₛₗ[(K.c : K.E →+* K.E)] K.E :=
      LinearMap.mk₂'ₛₗ (RingHom.id K.E) (K.c : K.E →+* K.E) (fun u v => B.herm β' u v)
        (fun u u' v => addL _ _ _ _) (fun r u v => smulL _ _ _ _)
        (fun u v v' => addR _ _ _ _) (fun r u v => smulR _ _ _ _)
    have hF : F₁ = F₂ := LinearMap.ext_basis b' b' (fun i j => by
      simp only [F₁, F₂, LinearMap.mk₂'ₛₗ_apply, hφb]; exact hgram i j)
    intro u v
    have := LinearMap.congr_fun₂ hF u v
    simp only [F₁, F₂, LinearMap.mk₂'ₛₗ_apply] at this
    exact this
  have hcomm : ∀ u, φ (ε * B.g * u) = ε * B.g * φ u := by
    intro u
    rw [← sub_eq_zero]
    apply ndh
    intro z
    obtain ⟨v, rfl⟩ : ∃ v, φ v = z := ⟨φ.symm z, by simp⟩
    rw [subL, hφ, ← asym _ hβ', ← hφ, asym _ hβ, sub_self]
  have hg : ∀ u, φ (B.g * u) = B.g * φ u := by
    intro u
    rcases hε with rfl | rfl
    · simpa using hcomm u
    · have := hcomm u
      simp only [neg_mul, one_mul, map_neg, neg_inj] at this
      exact this
  have hpoly : ∀ q : K.E[X], ∀ u, φ (aeval B.g q * u) = aeval B.g q * φ u := by
    intro q
    induction q using Polynomial.induction_on with
    | C r => intro u; rw [aeval_C, ← Algebra.smul_def, ← Algebra.smul_def, map_smul]
    | add p q hp hq => intro u; rw [map_add (f := _), add_mul, add_mul, map_add (f := _), hp, hq]
    | monomial n r h =>
      intro u
      have e : aeval B.g (C r * X ^ (n + 1)) = aeval B.g (C r * X ^ n) * B.g := by
        simp [pow_succ, mul_assoc]
      rw [e, mul_assoc, h, hg, mul_assoc]
  have hmul : ∀ y, φ y = y * φ 1 := by
    intro y
    obtain ⟨q, rfl⟩ := GlobalTheory.UnitLemma.PairClass.exists_aeval_eq_of_separable B.g hs' y
    simpa using hpoly q 1
  have ht : IsUnit (φ 1) := by
    have := hmul (φ.symm 1)
    rw [LinearEquiv.apply_symm_apply] at this
    exact ⟨⟨φ 1, φ.symm 1, by rw [mul_comm]; exact this.symm, this.symm⟩, rfl⟩
  refine ⟨ht.unit, ?_⟩
  rw [IsUnit.unit_spec]
  rw [← sub_eq_zero]
  apply nd
  intro y
  have h1 := hφ y 1
  rw [hmul y] at h1
  unfold InvAlg.herm at h1
  rw [map_one B.σ, mul_one] at h1
  have h2 : ((β' : B.A) - β * (φ 1 * B.σ (φ 1))) * y = (β' : B.A) * y - β * (y * φ 1) * B.σ (φ 1) := by ring
  rw [h2, map_sub, h1, sub_self]

end GlobalTheory.UnitLemma.IsometryUnit
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteDoubleCosetsMeetingCompactSupportConj
section
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory

theorem doubleCoset_finite_of_compactSupport : ∀ (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] (T K : Subgroup G) (y : G) (f : G → ℂ), IsCompact (K : Set G) → HasCompactSupport f → (∀ C : Set G, IsCompact C → {q : DoubleCoset.Quotient (T : Set G) (K : Set G) | (Quotient.out q)⁻¹ * y * Quotient.out q ∈ C}.Finite) → {q : DoubleCoset.Quotient (T : Set G) (K : Set G) | ∃ k ∈ K, f ((Quotient.out q * k)⁻¹ * y * (Quotient.out q * k)) ≠ 0}.Finite := by
  intro G _ _ _ T K y f hK hf hfin
  have hCc : IsCompact ((fun p : G × G => p.1 * p.2 * p.1⁻¹) '' ((K : Set G) ×ˢ tsupport f)) :=
    (hK.prod hf.isCompact).image ((continuous_fst.mul continuous_snd).mul continuous_fst.inv)
  refine (hfin _ hCc).subset ?_
  rintro q ⟨k, hk, hne⟩
  refine ⟨(k, (Quotient.out q * k)⁻¹ * y * (Quotient.out q * k)), ⟨hk, subset_tsupport f hne⟩, ?_⟩
  group

end GlobalTheory
end

