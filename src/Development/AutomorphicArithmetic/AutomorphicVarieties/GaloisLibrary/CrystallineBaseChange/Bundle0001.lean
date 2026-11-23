module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.CrystallineBaseChange.QuadBCwOfQuadBaseChange
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.Bundle0009
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.RealTransport.RealTransport
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0025
public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.CrystallineBaseChange.CqStmt
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.Bundle0003
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.Hypotheses2
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.Bundle0006
public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.WeylCharacterRegularity.ExistsTens
public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.WeylAlgebraQuantumDet.ExistsScalar
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.TemperedLocalComponents.Bundle0002
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.Bundle0009
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FiniteDimensionalAdjoinRange
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FiniteDimensionalFilDR

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.CrystallineBaseChange.BcStmt
section
noncomputable section

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Polynomial
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace UpperTheory.V.Br

def SelfIso : Prop :=
  StrongMultOneReal → ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F] (a : ℕ), 1 ≤ a → ∀ (π : TR.CuspSub F a) (η : HChar F),
    η ^ 2 = 1 → SelfTw π.HasSat η → IsoTwist π η

def BcAtt0 : Prop :=
  ∀ (F E Ω : Type) [Field F] [NumberField F] [IsTotallyReal F] [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] [Field Ω]
    [Algebra F E] [Algebra F Ω] [Algebra E Ω] [IsScalarTower F E Ω] [IsAlgClosure E Ω] (l : ℕ) [Fact l.Prime] (ι : Qbar l ≃+* ℂ)
    (n : ℕ) (r : G F Ω →* GL (Fin n) (Qbar l)) (π : TR.CuspSub F n) (P : CuspSub E n), IsBC0 π P →
      (π.IsRegAlg → (CG.mk P).IsRegAlg) ∧ (AttR ι r π → IsSSRep (r.comp (Bc.res F Ω E)) → AttC ι (r.comp (Bc.res F Ω E)) P)

def BcConj0 : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [IsTotallyReal F] [Field E] [NumberField E] [IsCMField E] [Algebra F E]
    (n : ℕ) (π : TR.CuspSub F n) (P : CuspSub E n), IsBC0 π P →
      ∀ᶠ w : HeightOneSpectrum (𝓞 E) in Filter.cofinite, ∃ B, (CG.mk P).HasSat w B ∧ (CG.mk P).HasSat (Bc.cPl w) B

def BcDual0 : Prop :=
  GlobalTheory.Published.JacquetShalikaRigidity → GlobalTheory.Published.GelfandKazhdanDual →
  ∀ (F K : Type) [Field F] [NumberField F] [IsTotallyReal F] [Field K] [NumberField K] [IsCMField K] [Algebra F K],
    Module.finrank F K = 2 → ∀ (n : ℕ), 1 ≤ n → ∀ (π : TR.CuspSub F n) (χ : HChar F) (P : CuspSub K n), π.Polarized χ → IsBC0 π P →
    ∃ χ' : HChar (maximalRealSubfield K), (∀ v v' : InfinitePlace (maximalRealSubfield K), χ'.locInf v (-1) = χ'.locInf v' (-1)) ∧
      GlobalTheory.ContraPair.DualIsConjBy P (compNorm K χ')

def PlaceOf : Prop :=
  ∀ (F K Ω : Type) [Field F] [NumberField F] [Field K] [NumberField K] [Field Ω] [Algebra F K] [Algebra F Ω] [Algebra K Ω]
    [IsScalarTower F K Ω] [IsAlgClosure F Ω] [IsAlgClosure K Ω] (v : HeightOneSpectrum (𝓞 F)) (w : HeightOneSpectrum (𝓞 K))
    (i : v.adicCompletion F ≃+* w.adicCompletion K), Continuous i →
    (∀ x : F, i (algebraMap F _ x) = algebraMap K _ (algebraMap F K x)) →
    w.under (𝓞 F) = v ∧ ∃ A : ValuationSubring Ω, IsPlaceOver A v ∧ IsPlaceOver A w ∧
      PlaceIso A v A w (RingEquiv.refl Ω) (algebraMap F K) i

def WdAway : Prop :=
  ∀ (F K Ω : Type) [Field F] [NumberField F] [Field K] [NumberField K] [Field Ω] [Algebra F K] [Algebra F Ω] [Algebra K Ω]
    [IsScalarTower F K Ω] [IsAlgClosure F Ω] [IsAlgClosure K Ω] (l : ℕ) [Fact l.Prime] (ι : Qbar l ≃+* ℂ) (A : ValuationSubring Ω)
    (v : HeightOneSpectrum (𝓞 F)) (w : HeightOneSpectrum (𝓞 K)) (h : IsPlaceOver A v) (h' : IsPlaceOver A w)
    (i : v.adicCompletion F ≃+* w.adicCompletion K), PlaceIso A v A w (RingEquiv.refl Ω) (algebraMap F K) i →
    ((l : ℕ) : 𝓞 F) ∉ v.asIdeal → ((l : ℕ) : 𝓞 K) ∉ w.asIdeal → ∀ (n : ℕ) (r : G F Ω →* GL (Fin n) (Qbar l)),
    ∀ (x : WD h) (y : WD h'), IsWDOf ι r x → IsWDOf ι (r.comp (Bc.res F Ω K)) y → WDRel (RingEquiv.refl Ω) x y

def RecInv : Prop :=
  GlobalTheory.Published.LocalLanglandsGL → ∀ (F K Ω : Type) [Field F] [NumberField F] [Field K] [NumberField K] [Field Ω] [Algebra F Ω] [Algebra K Ω]
    [IsAlgClosure F Ω] [IsAlgClosure K Ω] (A : ValuationSubring Ω) (v : HeightOneSpectrum (𝓞 F)) (w : HeightOneSpectrum (𝓞 K))
    (h : IsPlaceOver A v) (h' : IsPlaceOver A w) (j : F →+* K) (i : v.adicCompletion F ≃+* w.adicCompletion K),
    PlaceIso A v A w (RingEquiv.refl Ω) j i → ∀ (n : ℕ) (σ : SmIrr (GL (Fin n) (v.adicCompletion F)))
    (σ' : SmIrr (GL (Fin n) (w.adicCompletion K))) rc rc', IsRec h rc → IsRec h' rc' →
    WDRel (RingEquiv.refl Ω) (rc (algNorm σ)) (rc' (algNorm σ')) →
    ∃ e : σ.V ≃ₗ[ℂ] σ'.V, ∀ g x, e (σ.ρ g x) = σ'.ρ (Matrix.GeneralLinearGroup.map i.toRingHom g) (e x)

def SplitOf : Prop :=
  GlobalTheory.Mem.LiteralAutomorphy.LitN → ExC → ExR →
  ∀ (F K : Type) [Field F] [NumberField F] [IsTotallyReal F] [Field K] [NumberField K] [IsCMField K] [Algebra F K],
    Module.finrank F K = 2 → ∀ (n : ℕ) [Fact (n = 2)], 1 ≤ n → ∀ (π : TR.CuspSub F n) (χ : HChar F) (P : CuspSub K n), π.IsRegAlg → π.Polarized χ →
      IsBC0 π P → SplitIso π P

end UpperTheory.V.Br
end
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.CrystallineBaseChange.CharConj
section
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.HeckeGal UpperTheory.V UpperTheory.V.Af
open GlobalTheory.CuspRep (Af finId pFin)
open ReciprocityTheory.Neutral.Bridge.HCFR (infIdele)

section

variable {F : Type} [Field F] [NumberField F]

private theorem cc_finId_local (w : HeightOneSpectrum (𝓞 F)) (x : (w.adicCompletion F)ˣ) :
    finId F (Units.map (pFin F).toMonoidHom (localIdele F w x)) = localIdele F w x := by
  refine Units.ext (Prod.ext ?_ ?_)
  · change (1 : InfiniteAdeleRing F) - 0 + 0 = 1
    simp
  · change (1 : Af F) - 1 + _ = _
    rw [sub_self, zero_add]
    rfl

private theorem cc_pFin_inf (v : InfinitePlace F) (x : (v.Completion)ˣ) :
    Units.map (pFin F).toMonoidHom (infIdele F v x) = 1 := Units.ext rfl

private theorem cc_split (k : Fˣ) :
    infDiag k * finId F (Units.map (algebraMap F (Af F)).toMonoidHom k) = diagUnits F k := by
  classical
  have h : ((infDiag k : Ideles F) : AdeleRing (𝓞 F) F) = (algebraMap F (InfiniteAdeleRing F) k, 1) := by
    unfold infDiag
    rw [MonoidHom.finsetProd_apply, Units.coe_prod]
    let ι : (∀ w : InfinitePlace F, w.Completion) →* AdeleRing (𝓞 F) F :=
      MonoidHom.inl (InfiniteAdeleRing F) (FiniteAdeleRing (𝓞 F) F)
    change ∏ w : InfinitePlace F, ι (Pi.mulSingle w (algebraMap F w.Completion k)) =
      ι (fun w => algebraMap F w.Completion k)
    rw [← map_prod, Finset.univ_prod_mulSingle]
  apply Units.ext
  rw [Units.val_mul, h]
  refine Prod.ext ?_ ?_
  · change algebraMap F (InfiniteAdeleRing F) k * (1 - 0 + 0) = algebraMap F (InfiniteAdeleRing F) k
    simp
  · change (1 : Af F) * (1 - 1 + algebraMap F (Af F) k) = algebraMap F (Af F) k
    simp

private theorem cc_inf_fixed (hF : Module.finrank ℚ F = 1) (χ : HChar F) (a : (F →+* ℂ) → ℤ) (h : IsAlgPos χ a)
    (σ : ℂ ≃+* ℂ) (k : Fˣ) : σ ((χ.inf k : ℂˣ) : ℂ) = ((χ.inf k : ℂˣ) : ℂ) := by
  have hs : Function.Surjective (algebraMap ℚ F) := (Algebra.finrank_eq_one_iff_bijective_algebraMap.1 hF).2
  obtain ⟨q, hq⟩ := hs (k : F)
  have h1 := h (k ^ 2) fun φ => by
    rw [Units.val_pow_eq_pow_val, map_pow]
    exact pow_two_pos_of_ne_zero ((map_ne_zero φ).2 k.ne_zero)
  have h2 : ((χ.inf k : ℂˣ) : ℂ) ^ 2 = (∏ φ : F →+* ℂ, (q : ℂ) ^ a φ) ^ 2 := by
    rw [← Units.val_pow_eq_pow_val, ← map_pow, h1, ← Finset.prod_pow]
    refine Finset.prod_congr rfl fun φ _ => ?_
    rw [Units.val_pow_eq_pow_val, map_pow, ← hq, eq_ratCast, map_ratCast, ← zpow_natCast, ← zpow_natCast,
      ← zpow_mul, ← zpow_mul, mul_comm]
  have h3 : σ (∏ φ : F →+* ℂ, (q : ℂ) ^ a φ) = ∏ φ : F →+* ℂ, (q : ℂ) ^ a φ := by
    simp only [map_prod, map_zpow₀, map_ratCast]
  rcases sq_eq_sq_iff_eq_or_eq_neg.1 h2 with e | e
  · rw [e, h3]
  · rw [e, map_neg, h3]

end

theorem UpperTheory.V.Br.charConj :
    UpperTheory.V.Br.CharConj := by
  intro F _ _ hF χ a ha σ
  have hσ : ∀ k : Fˣ, σ ((χ.1 (finId F (Units.map (algebraMap F (Af F)).toMonoidHom k)) : ℂˣ) : ℂ) =
      ((χ.1 (finId F (Units.map (algebraMap F (Af F)).toMonoidHom k)) : ℂˣ) : ℂ) := fun k => by
    have h1 := χ.2.2 k
    rw [← cc_split k, map_mul] at h1
    have h2 : χ.1 (finId F (Units.map (algebraMap F (Af F)).toMonoidHom k)) = (χ.inf k)⁻¹ :=
      eq_inv_of_mul_eq_one_right h1
    rw [h2, Units.val_inv_eq_inv_val, map_inv₀, cc_inf_fixed hF χ a ha σ k]
  let ψ : (Af F)ˣ →* ℂˣ := χ.1.comp (finId F)
  have hψ : Continuous ψ := χ.2.1.comp (GlobalTheory.CuspRep.continuous_finId F)
  let ψ' : (Af F)ˣ →* ℂˣ := (Units.map (σ : ℂ →+* ℂ).toMonoidHom).comp ψ
  have hψ' : Continuous ψ' := by
    refine continuous_of_continuousAt_one ψ' ?_
    have h1 : {u | ψ u = 1} ∈ nhds (1 : (Af F)ˣ) :=
      (GlobalTheory.CuspRep.isOpen_ker_finIdele F ψ hψ).mem_nhds (map_one ψ)
    refine (continuousAt_const (y := (1 : ℂˣ))).congr ?_
    filter_upwards [h1] with u hu
    change 1 = Units.map _ (ψ u)
    rw [hu, map_one]
  let p := Units.map (pFin F).toMonoidHom
  have hp : Continuous p := Continuous.units_map _ continuous_snd
  let χ' : HChar F := ⟨χ.1 * (ψ.comp p)⁻¹ * ψ'.comp p, (χ.2.1.mul (hψ.comp hp).inv).mul (hψ'.comp hp), fun k => by
    have e : ψ' (Units.map (algebraMap F (Af F)).toMonoidHom k) = ψ (Units.map (algebraMap F (Af F)).toMonoidHom k) :=
      Units.ext (hσ k)
    change χ.1 _ * (ψ (Units.map (algebraMap F (Af F)).toMonoidHom k))⁻¹ *
      ψ' (Units.map (algebraMap F (Af F)).toMonoidHom k) = 1
    rw [χ.2.2 k, e, one_mul, inv_mul_cancel]⟩
  have hloc : ∀ w x, χ'.loc w x = Units.map (σ : ℂ →+* ℂ).toMonoidHom (χ.loc w x) := fun w x => by
    have e := cc_finId_local w x
    change χ.1 (localIdele F w x) * (χ.1 (finId F (Units.map (pFin F).toMonoidHom (localIdele F w x))))⁻¹ *
      Units.map (σ : ℂ →+* ℂ).toMonoidHom (χ.1 (finId F (Units.map (pFin F).toMonoidHom (localIdele F w x)))) = _
    rw [e, mul_inv_cancel, one_mul]
    rfl
  refine ⟨χ', fun v => ?_, fun w hw => ⟨fun x hx => ?_, ?_⟩⟩
  · change χ.1 (infIdele F v (-1)) * (ψ (Units.map (pFin F).toMonoidHom (infIdele F v (-1))))⁻¹ *
      ψ' (Units.map (pFin F).toMonoidHom (infIdele F v (-1))) = χ.1 (infIdele F v (-1))
    rw [cc_pFin_inf, map_one, map_one, inv_one, mul_one, mul_one]
  · rw [hloc, hw x hx, map_one]
  · exact congrArg Units.val (hloc w (atFin w (unif w)))
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.CrystallineBaseChange.FrobEx
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Polynomial
open UpperTheory.V UpperTheory.V.Af
open scoped Pointwise

section

variable {F Ω : Type} [Field F] [NumberField F] [Field Ω] [Algebra F Ω]

omit [NumberField F] in
private theorem val_smul_lt (g : G F Ω) (A : ValuationSubring Ω) (y : Ω) :
    (g • A).valuation (g y) < 1 ↔ A.valuation y < 1 := by
  have e : ∀ z : Ω, g z ∈ g • A ↔ z ∈ A := fun z => by
    rw [ValuationSubring.mem_pointwise_smul_iff_inv_smul_mem, show g z = g • z from rfl, inv_smul_smul]
  rw [valuation_lt_one_iff', valuation_lt_one_iff', e, ← map_inv₀, e, map_eq_zero]

omit [NumberField F] in
private theorem val_smul_le (g : G F Ω) (A : ValuationSubring Ω) (y : Ω) :
    (g • A).valuation (g y) ≤ 1 ↔ A.valuation y ≤ 1 := by
  rw [ValuationSubring.valuation_le_one_iff, ValuationSubring.valuation_le_one_iff,
    ValuationSubring.mem_pointwise_smul_iff_inv_smul_mem, show g y = g • y from rfl, inv_smul_smul]

omit [NumberField F] in
private theorem conj_dec {g τ : G F Ω} {A : ValuationSubring Ω} (h : τ ∈ (g • A).decompositionSubgroup F) :
    g⁻¹ * τ * g ∈ A.decompositionSubgroup F := by
  have h1 : τ • g • A = g • A := h
  show (g⁻¹ * τ * g) • A = A
  rw [mul_smul, mul_smul, h1, inv_smul_smul]

omit [NumberField F] in
private theorem conj_apply (g τ : G F Ω) (x : Ω) : g ((g⁻¹ * τ * g) x) = τ (g x) := by
  change g • ((g⁻¹ * τ * g) • x) = τ • (g • x)
  rw [mul_smul, mul_smul, smul_inv_smul]

omit [NumberField F] in
private theorem conj_frob {g τ : G F Ω} {A : ValuationSubring Ω} {q : ℕ} (h : IsFrob (g • A) q τ) :
    IsFrob A q (g⁻¹ * τ * g) := by
  refine ⟨conj_dec h.1, fun x hx => ?_⟩
  have h1 := h.2 (g x) ((val_smul_le g A x).2 hx)
  rwa [← conj_apply, ← map_pow, ← map_sub, val_smul_lt] at h1

private theorem conj_ine {g τ : G F Ω} {A : ValuationSubring Ω} (h : τ ∈ Ine (F := F) (g • A)) :
    g⁻¹ * τ * g ∈ Ine (F := F) A := by
  refine ⟨conj_dec h.1, fun x hx => ?_⟩
  have h1 := h.2 (g x) ((val_smul_le g A x).2 hx)
  rwa [← conj_apply, ← map_sub, val_smul_lt] at h1

private theorem ine_fix {A : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 F)} (hA : IsPlaceOver A w) {M : ℕ}
    (hM : ((M : ℕ) : 𝓞 F) ∉ w.asIdeal) {s : G F Ω} (hs : s ∈ Ine (F := F) A) (ζ : Ω) (hζ : ζ ^ M = 1) : s ζ = ζ := by
  set v := A.valuation with hvdef
  have hM0 : M ≠ 0 := by
    rintro rfl
    exact hM (by simp)
  have hvM : ¬ v (M : Ω) < 1 := by
    intro hlt
    apply hM
    rw [← hA]
    simpa using hlt
  have hζ1 : v ζ = 1 := by
    rcases lt_trichotomy (v ζ) 1 with h | h | h
    · have h2 := pow_lt_one' h hM0
      rw [← map_pow, hζ, map_one] at h2
      exact absurd h2 (lt_irrefl 1)
    · exact h
    · have h2 := one_lt_pow' h hM0
      rw [← map_pow, hζ, map_one] at h2
      exact absurd h2 (lt_irrefl 1)
  have hζ0 : ζ ≠ 0 := by
    rintro rfl
    simp at hζ1
  have hsd : v (s ζ - ζ) < 1 := hs.2 ζ hζ1.le
  have hηM : (s ζ) ^ M = 1 := by rw [← map_pow, hζ, map_one]
  set η := s ζ with hη
  set u := η * ζ⁻¹ with hu
  have huM : u ^ M = 1 := by rw [hu, mul_pow, inv_pow, hηM, hζ, inv_one, mul_one]
  have hu1 : v (u - 1) < 1 := by
    have e : u - 1 = (η - ζ) * ζ⁻¹ := by rw [hu, sub_mul, mul_inv_cancel₀ hζ0]
    rw [e, map_mul, map_inv₀, hζ1, inv_one, mul_one]
    exact hsd
  have hule : v u ≤ 1 := by
    have e : u = (u - 1) + 1 := by ring
    rw [e]
    exact (v.map_add _ _).trans (max_le hu1.le (by rw [map_one]))
  by_contra hne
  have hu_ne : u ≠ 1 := by
    intro h1
    apply hne
    have e : η = u * ζ := by rw [hu, mul_assoc, inv_mul_cancel₀ hζ0, mul_one]
    rw [e, h1, one_mul]
  have hsum : ∑ i ∈ Finset.range M, u ^ i = 0 := by
    have h := geom_sum_mul u M
    rw [huM, sub_self] at h
    exact (mul_eq_zero.1 h).resolve_right (sub_ne_zero.2 hu_ne)
  have hlt : v (∑ i ∈ Finset.range M, (u ^ i - 1)) < 1 := by
    apply Valuation.map_sum_lt v one_ne_zero
    intro i _
    rw [← geom_sum_mul u i, map_mul]
    have hs1 : v (∑ j ∈ Finset.range i, u ^ j) ≤ 1 :=
      Valuation.map_sum_le v (fun j _ => by rw [map_pow]; exact pow_le_one' hule j)
    calc v (∑ j ∈ Finset.range i, u ^ j) * v (u - 1) ≤ 1 * v (u - 1) := by gcongr
      _ = v (u - 1) := one_mul _
      _ < 1 := hu1
  rw [Finset.sum_sub_distrib, hsum, Finset.sum_const, Finset.card_range, zero_sub, Valuation.map_neg] at hlt
  apply hvM
  simpa using hlt

end

theorem UpperTheory.V.Br.frobEx :
    UpperTheory.V.Br.FrobEx := by
  intro F Ω _ _ _ _ _ l _ ι n r w
  refine ⟨?_, ?_⟩
  · intro B B' hB hB'
    obtain ⟨A, hA⟩ := exists_isPlaceOver Ω w
    obtain ⟨σ, hσ⟩ := exists_isFrob hA
    have h1 := (hB A hA).2 σ hσ
    have h2 := (hB' A hA).2 σ hσ
    have h3 := congrArg Polynomial.roots (h1.symm.trans h2)
    simpa [Polynomial.roots_multiset_prod_X_sub_C] using h3
  · intro M hlev hl hM
    obtain ⟨A0, hA0, χ, hχ, P, hP⟩ := hlev w hl
    have hI0 : ∀ t ∈ Ine (F := F) A0, r t = 1 := by
      intro t ht
      have hd := hP t ht
      have hc : ∀ i, χ i t = 1 := fun i => hχ i t (fun ζ hζ => ine_fix hA0 hM ht ζ hζ)
      simp only [hc, Units.val_one, Matrix.diagonal_one] at hd
      have hq : P * r t * P⁻¹ = 1 := Units.ext hd
      calc r t = P⁻¹ * (P * r t * P⁻¹) * P := by group
        _ = 1 := by rw [hq]; group
    obtain ⟨σ0, hσ0⟩ := exists_isFrob hA0
    refine ⟨(Polynomial.map ι.toRingHom
      ((r σ0⁻¹ : GL (Fin n) (Qbar l)) : Matrix (Fin n) (Fin n) (Qbar l)).charpoly).roots, ?_⟩
    intro A hA
    obtain ⟨g, hg⟩ := exists_smul_eq_of_isPlaceOver hA0 hA
    subst hg
    refine ⟨fun s hs => ?_, fun σ hσ => ?_⟩
    · have ht := hI0 _ (conj_ine hs)
      calc r s = r g * r (g⁻¹ * s * g) * r g⁻¹ := by
            simp only [map_mul, map_inv]
            group
        _ = 1 := by rw [ht]; simp
    · have hc := inv_mul_mem_Ine_of_isFrob hσ0 (conj_frob hσ)
      have he : r (g⁻¹ * σ * g) = r σ0 := by
        have h4 := hI0 _ hc
        rw [map_mul, map_inv] at h4
        exact (inv_mul_eq_one.1 h4).symm
      have hu : r σ⁻¹ = r g * r σ0⁻¹ * (r g)⁻¹ := by
        rw [map_inv r σ0, ← he]
        simp only [map_mul, map_inv]
        group
      rw [hu, Units.val_mul, Units.val_mul, Matrix.coe_units_inv, Matrix.charpoly_units_conj]
      exact Polynomial.Splits.eq_prod_roots_of_monic (IsAlgClosed.splits _)
        ((Matrix.charpoly_monic _).map _)
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.CrystallineBaseChange.KlevThree
section
private theorem klev_three (K : Type) [Field K] [NumberField K] (n M : ℕ) :
    UpperTheory.V.Af.KLev K n (3 * M) ≤ UpperTheory.V.Af.KLev K n M := by
  refine Subgroup.map_mono fun k hk => ?_
  have hle : Ideal.span {((3 * M : ℕ) : ↥(UpperTheory.V.Af.Ohat K))} ≤ Ideal.span {(M : ↥(UpperTheory.V.Af.Ohat K))} :=
    Ideal.span_singleton_le_span_singleton.2 (Nat.cast_dvd_cast (Dvd.intro_left 3 rfl))
  have e := congrArg (Matrix.GeneralLinearGroup.map (n := Fin n) (Ideal.Quotient.factor hle)) (MonoidHom.mem_ker.1 hk)
  rw [map_one] at e
  exact e
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.CrystallineBaseChange.PotMove
section
open NumberField Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N GlobalTheory.Pst UpperTheory.V UpperTheory.V.Af
open scoped Pointwise

theorem UpperTheory.V.Br.potMove :
    UpperTheory.V.Br.PotMove := by
  intro F Ω _ _ _ _ _ l _ n r A A' g hg hA
  obtain ⟨O, i1, i2, i3, Bw, hj, LL', r', ⟨hle, hmap⟩, K', hK', hcr⟩ := hA
  have hmem : ∀ s : G F Ω, s ∈ Dec (F := F) A' ↔ g * s * g⁻¹ ∈ Dec (F := F) A := fun s => by
    have hgA : g • A' = A := by
      ext x
      rw [ValuationSubring.mem_pointwise_smul_iff_inv_smul_mem, hg]
      simp [AlgEquiv.smul_def]
    rw [mem_Dec, mem_Dec, ← hgA, mul_smul, inv_smul_smul, mul_smul, smul_left_cancel_iff]
  let φ : ↥(Dec (F := F) A') ≃* ↥(Dec (F := F) A) :=
    { toFun := fun s => ⟨g * s * g⁻¹, (hmem s).1 s.2⟩
      invFun := fun t => ⟨g⁻¹ * t * g, (hmem _).2 (by
        have e : g * (g⁻¹ * (t : G F Ω) * g) * g⁻¹ = t := by group
        rw [e]; exact t.2)⟩
      left_inv := fun s => Subtype.ext (by dsimp only; group)
      right_inv := fun t => Subtype.ext (by dsimp only; group)
      map_mul' := fun s t => Subtype.ext (by simp only [Subgroup.coe_mul]; group) }
  have hφ : Continuous φ :=
    ((continuous_const.mul continuous_subtype_val).mul continuous_const).subtype_mk _
  have hφs : Continuous φ.symm :=
    ((continuous_const.mul continuous_subtype_val).mul continuous_const).subtype_mk _
  have hjE : ∀ x : F, Bw.j (g (algebraMap F Ω x)) = Bw.j (algebraMap F Ω x) := fun x => by
    rw [AlgEquiv.commutes]
  let Bw' : LocBridge l F Ω (Dec (F := F) A') O :=
    { Kw := Bw.Kw, j := Bw.j.comp (g : Ω →+* Ω)
      j_E := fun x => by
        change Bw.j (g (algebraMap F Ω x)) ∈ _
        rw [hjE]; exact Bw.j_E x
      j_dense := Bw.j_dense.trans (closure_mono (by
        rintro _ ⟨x, rfl⟩
        exact ⟨x, hjE x⟩))
      e := φ.trans Bw.e
      e_cont := Bw.e_cont.comp hφ, e_symm_cont := hφs.comp Bw.e_symm_cont
      e_comm := fun s x => by
        refine (Bw.e_comm (φ s) (g x)).trans ?_
        change Bw.j ((g * (s : G F Ω) * g⁻¹) (g x)) = Bw.j (g ((s : G F Ω) x))
        simp
      LL := Bw.LL, LL_split := Bw.LL_split, eO := Bw.eO, eO_alg := Bw.eO_alg
      eO_cont := Bw.eO_cont, eO_symm_cont := Bw.eO_symm_cont }
  have h1 : PotCrysAt (r.comp (MulAut.conj g).toMonoidHom) A' := by
    refine ⟨O, i1, i2, i3, Bw', fun x => (hg x).trans (hj (g x)), LL', r'.comp φ.toMonoidHom,
      ⟨hle, MonoidHom.ext fun s => DFunLike.congr_fun hmap (φ s)⟩, K', hK', ?_⟩
    have e : Bw'.repE LL' (r'.comp φ.toMonoidHom) = Bw.repE LL' r' := by
      refine MonoidHom.ext fun t => ?_
      simp [LocBridge.repE, Bw']
    rw [e]
    exact hcr
  refine h1.of_iso ⟨(r g)⁻¹, fun s => ?_⟩
  simp [mul_assoc]
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.CrystallineBaseChange.PotRes
section
open Formalism.ConjugateSelfDual Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N ReciprocityTheory.Gal UpperTheory.V.Loc UpperTheory.V.Af UpperTheory.V.Af.Bc NumberField

private theorem ex_bridge {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
    {l : ℕ} [Fact l.Prime] {A : ValuationSubring Ω} (j : Ω →+* Om l) (hj : ∀ x, x ∈ A ↔ ‖j x‖ ≤ 1) :
    ∃ (L : FinExt l) (Bw : LocBridge l E Ω (Dec (F := E) A) ↥(OL L)), Bw.j = j := by
  let K : FinExt l := ⟨IntermediateField.adjoin ℚ_[l] (Set.range fun x : E => j (algebraMap E Ω x)),
    GlobalTheory.PlaceBridge.finiteDimensional_adjoin_range (j.comp (algebraMap E Ω))⟩
  have := K.2
  obtain ⟨e, he, he', hec⟩ := GlobalTheory.PlaceBridge.exists_mulEquiv (E := E) hj K rfl
  exact ⟨⟨IntermediateField.normalClosure ℚ_[l] K.1 (PadicAlgCl l), inferInstance⟩,
    { Kw := K
      j := j
      j_E := fun x => IntermediateField.subset_adjoin _ _ ⟨x, rfl⟩
      j_dense := GlobalTheory.PlaceBridge.adjoin_range_subset_closure (j.comp (algebraMap E Ω))
      e := e
      e_cont := he
      e_symm_cont := he'
      e_comm := hec
      LL := ⟨IntermediateField.normalClosure ℚ_[l] K.1 (PadicAlgCl l), inferInstance⟩
      LL_split := fun τ x => AlgHom.fieldRange_le_normalClosure τ ⟨x, rfl⟩
      eO := RingEquiv.refl _
      eO_alg := fun _ => rfl
      eO_cont := continuous_id
      eO_symm_cont := continuous_id }, rfl⟩

theorem UpperTheory.V.Br.potRes :
    UpperTheory.V.Br.PotRes := by
  intro F K Ω _ _ _ _ _ _ _ _ _ _ _ l _ n r A hr
  obtain ⟨O, i1, i2, i3, Bw, hj, hp⟩ := hr
  obtain ⟨L, Bw', hBj⟩ := ex_bridge (E := K) (A := A) Bw.j hj
  refine ⟨↥(OL L), inferInstance, inferInstance, inferInstance, Bw', fun x => by rw [hBj]; exact hj x, ?_⟩
  obtain ⟨L₀, r₀, hm₀, -⟩ := id hp
  have hm₁ := hm₀.enlarge (L₂ := GlobalTheory.Pst.supExt L₀ Bw'.LL) le_sup_left
  have hL : Bw'.LL.1 ≤ (GlobalTheory.Pst.supExt L₀ Bw'.LL).1 := le_sup_right
  obtain ⟨r₁, hm, hc⟩ : ∃ r₁, GlobalTheory.Pst.IsModel Bw (r.comp (Dec (F := F) A).subtype) (GlobalTheory.Pst.supExt L₀ Bw'.LL) r₁ ∧
      Bw.IsPotCrysE (PP l) _ r₁ := ⟨_, hm₁, (hm₁.isPotCrysAt_iff (PP l)).1 hp⟩
  clear hm₁
  generalize GlobalTheory.Pst.supExt L₀ Bw'.LL = L₁ at hL r₁ hm hc
  obtain ⟨K₁, h₁, hc⟩ := hc
  have hmem : ∀ σ : G K Ω, σ ∈ Dec (F := K) A ↔ res F Ω K σ ∈ Dec (F := F) A := fun σ => by
    rw [mem_Dec, mem_Dec]
    exact Iff.rfl
  let f : ↥(Dec (F := K) A) →* ↥(Dec (F := F) A) :=
    ((res F Ω K).comp (Dec (F := K) A).subtype).codRestrict _ fun σ => (hmem σ).1 σ.2
  refine ⟨L₁, r₁.comp f, ⟨hL, MonoidHom.ext fun g => DFunLike.congr_fun hm.2 (f g)⟩, ?_⟩
  have h₂ : K₁.1 ≤ (GlobalTheory.Pst.supExt K₁ Bw'.Kw).1 := le_sup_left
  have h₃ : Bw'.Kw.1 ≤ (GlobalTheory.Pst.supExt K₁ Bw'.Kw).1 := le_sup_right
  refine ⟨_, h₃, ?_⟩
  obtain ⟨T⟩ := tiedP l
  have hres := (GlobalTheory.Per.TiedRestrict.restrict_crys_deRham l (PP l) (AIP l) T K₁ _ L₁ h₂ _ _).1 hc
  convert hres using 1
  refine MonoidHom.ext fun g => ?_
  have hg : f (Bw'.e.symm (Subgroup.inclusion (GK_le h₃) g)) =
      Bw.e.symm (Subgroup.inclusion (GK_le h₁) (Subgroup.inclusion (GK_le h₂) g)) := by
    refine Subtype.ext (AlgEquiv.ext fun x => Bw.j.injective ?_)
    have a1 := Bw'.e_comm (Bw'.e.symm (Subgroup.inclusion (GK_le h₃) g)) x
    have a2 := Bw.e_comm (Bw.e.symm (Subgroup.inclusion (GK_le h₁) (Subgroup.inclusion (GK_le h₂) g))) x
    rw [MulEquiv.apply_symm_apply] at a1 a2
    rw [hBj] at a1
    exact a1.symm.trans a2
  exact congrArg (fun s => Matrix.toLinAlgEquiv' (r₁ s : Matrix (Fin n) (Fin n) ↥L₁.1)) hg
end

