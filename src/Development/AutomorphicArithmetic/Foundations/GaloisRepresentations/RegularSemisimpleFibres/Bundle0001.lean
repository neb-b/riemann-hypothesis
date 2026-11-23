module

public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.RegularSemisimpleFibres.ResEmbCompat
public import Development.AutomorphicArithmetic.Foundations.LocalLanglands.LocalCentralUnits.TameRecAll
public import Development.DiscreteGroups.GlobalIrreducibility.Bundle0017
public import Development.DiscreteGroups.GlobalIrreducibility.Bundle0002
public import Development.DiscreteGroups.GlobalIrreducibility.Bundle0015
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0722
public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.CharacterTheory.Bundle0008
public import Development.AbelianVarietyTheory.Definitions.CommutativeAlgebra.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.CharacterTheory.Bundle0013
public import Development.AbelianVarietyTheory.Proofs.CharacterTheory.Bundle0016
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0034
public import Development.WeilBound.CoreStatements.FiniteTypeHarishChandra.GreenCuspLabels.GreenCuspidal
public import Development.AutomorphicArithmetic.Foundations.LocalLanglands.LocalCentralUnits.Bundle0003
public import Development.AutomorphicArithmetic.Foundations.LocalLanglands.LocalCentralUnits.FinrankK
public import Development.AutomorphicArithmetic.Foundations.LocalLanglands.LocalCentralUnits.Bundle0004
public import Development.AutomorphicArithmetic.Foundations.LocalLanglands.LocalCentralUnits.TypeEx
public import Development.WeilBound.RepresentationTheoryGL.GaloisPermutationReps.SubquotientEquivalence.ConjTorusSubApply
public import Development.AutomorphicArithmetic.Foundations.LocalLanglands.Multi
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ApplyMemTwKerOfNormalizer
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1050

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.RegularSemisimpleFibres.BaseCase
section
noncomputable section

open NumberField IsDedekindDomain ValuativeRel Polynomial Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.L2.Host
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.Shin
open GroundTheory.Global GroundTheory.Global.SemiLocal UpperTheory.V.Published UpperTheory.CBC
open scoped Classical

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace UpperTheory.Gal.InertialTypesAlt

def BaseCase : Prop :=
  ∀ (K Ω : Type) [Field K] [NumberField K] [_root_.NumberField.IsTotallyComplex K] [Field Ω] [Algebra K Ω] (n : ℕ) (π : CuspSub K n)
    (A : ValuationSubring Ω) (Θ : IsLocalRing.ResidueField A →* ℂ) (v : HeightOneSpectrum (𝓞 K)) e e',
    ResEmb A v e → ResEmb A v e' → ∀ τ τ', π.IsLocComp v τ → π.IsLocComp v τ' →
    ∀ a : Lbl, HasLbl (Θ.comp e.toMonoidHom) τ.ρ a → HasLbl (Θ.comp e'.toMonoidHom) τ'.ρ a

end UpperTheory.Gal.InertialTypesAlt
end
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.RegularSemisimpleFibres.PArtRead
section
open NumberField IsDedekindDomain ValuativeRel Polynomial Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.L2.Host
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.Shin
open GroundTheory.Global GroundTheory.Global.SemiLocal UpperTheory.V.Published UpperTheory.CBC UpperTheory.Gal.InertialTypesAlt
open scoped Classical
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

private theorem resS_eq_resS_of_mul_sub_eq_mul {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] (y₁ y₂ : 𝒪[k]) (h : valuation k ((y₁ : k) - y₂) < 1) :
    IsLocalRing.residue 𝒪[k] y₁ = IsLocalRing.residue 𝒪[k] y₂ := by
  rw [← sub_eq_zero, ← map_sub, IsLocalRing.residue_eq_zero_iff, IsLocalRing.mem_maximalIdeal,
    mem_nonunits_iff, (Valuation.integer.integers (valuation k)).isUnit_iff_valuation_eq_one]
  exact ne_of_lt h

private theorem residue_eq_of_valuation_sub_lt_one {Ω : Type} [Field Ω] (A : ValuationSubring Ω) (z₁ z₂ : A)
    (h : A.valuation ((z₁ : Ω) - z₂) < 1) :
    IsLocalRing.residue A z₁ = IsLocalRing.residue A z₂ := by
  rw [← sub_eq_zero, ← map_sub, IsLocalRing.residue_eq_zero_iff, ValuationSubring.valuation_lt_one_iff]
  exact h

theorem UpperTheory.Gal.InertialTypesAlt.artRead :
    ArtRead := by
  unfold ArtRead
  intro E Ω _ _ _ _ _ A v h g _ hg1 hg2 a ha e he t ϖ hϖ
  unfold ResEmb at he
  have hp : Nat.Prime g := Fact.out
  have hEq : (valuation (HeightOneSpectrum.adicCompletion E v)).IsEquiv Valued.v := ValuativeRel.isEquiv _ _
  have hα : Valued.v (a (ineIncl h t) : HeightOneSpectrum.adicCompletion E v) = 1 :=
    DiscreteGroups.sglob.DzType.val_artin_ine ha t
  obtain ⟨u, hu⟩ := valuation_eq_one_iff.1 (hEq.eq_one_iff_eq_one.2 hα)
  have hg0 : (g : Ω) ≠ 0 := by
    rw [← map_natCast (algebraMap E Ω)]
    exact (_root_.map_ne_zero _).2 (Nat.cast_ne_zero.2 hp.ne_zero)
  have hg1' : (g : Ω) ≠ 1 := by
    rw [← map_natCast (algebraMap E Ω), ← map_one (algebraMap E Ω)]
    intro hc
    have := (algebraMap E Ω).injective hc
    exact hp.one_lt.ne' (by exact_mod_cast this)
  have hϖ0 : ϖ ≠ 0 := by
    rintro rfl
    rcases Nat.eq_zero_or_pos (normV v - 1) with hm | hm
    · rw [hm, pow_zero] at hϖ
      exact hg1' hϖ.symm
    · rw [zero_pow hm.ne'] at hϖ
      exact hg0 hϖ.symm
  have hz : A.valuation ((t : G E Ω) ϖ / ϖ) = 1 := DiscreteGroups.sglob.DzType.val_ratio (Ine_le_Dec A t.2) hϖ0
  obtain ⟨z, hzdef⟩ : ∃ z : A, (z : Ω) = (t : G E Ω) ϖ / ϖ :=
    ⟨⟨_, (A.valuation_le_one_iff _).1 hz.le⟩, rfl⟩
  obtain ⟨x, hx⟩ := DiscreteGroups.sglob.DzType.exists_int_approx_compl v
    (a (ineIncl h t) : HeightOneSpectrum.adicCompletion E v) hα.le
  have hx2 := UpperTheory.Zero.LLC.tameRecAll E Ω g A v h hg1 hg2 a ha ϖ hϖ t x hx
  refine ⟨z, u, hzdef, hu, ?_, ?_⟩
  · have hxA : algebraMap E Ω x ∈ A := by
      have h1 : ((t : G E Ω) ϖ / ϖ - algebraMap E Ω x) ∈ A := (A.valuation_le_one_iff _).1 hx2.le
      have h2 := A.sub_mem z.2 h1
      rw [hzdef, sub_sub_cancel] at h2
      exact h2
    have hyK : valuation (HeightOneSpectrum.adicCompletion E v)
        (algebraMap E (HeightOneSpectrum.adicCompletion E v) x) ≤ 1 :=
      hEq.le_one_iff_le_one.2 (DiscreteGroups.sglob.DzType.val_alg_le_one x)
    let y : 𝒪[HeightOneSpectrum.adicCompletion E v] := ⟨_, hyK⟩
    let zx : A := ⟨_, hxA⟩
    have hu' : (((u : 𝒪[HeightOneSpectrum.adicCompletion E v])) : HeightOneSpectrum.adicCompletion E v) =
        (a (ineIncl h t) : HeightOneSpectrum.adicCompletion E v) := congrArg Units.val hu
    have h1 : IsLocalRing.residue _ (u : 𝒪[HeightOneSpectrum.adicCompletion E v]) = IsLocalRing.residue _ y := by
      apply resS_eq_resS_of_mul_sub_eq_mul
      show valuation (HeightOneSpectrum.adicCompletion E v)
        (((u : 𝒪[HeightOneSpectrum.adicCompletion E v]) : HeightOneSpectrum.adicCompletion E v) -
          algebraMap E (HeightOneSpectrum.adicCompletion E v) x) < 1
      rw [hu']
      exact hEq.lt_one_iff_lt_one.2 hx
    have h2 : IsLocalRing.residue A z = IsLocalRing.residue A zx := by
      apply residue_eq_of_valuation_sub_lt_one
      show A.valuation ((z : Ω) - algebraMap E Ω x) < 1
      rw [hzdef]
      exact hx2
    rw [h2, ← he x y zx rfl rfl, ← h1]
    rfl
  · have hzm : z ^ (normV v - 1) = 1 := by
      apply Subtype.ext
      rw [SubmonoidClass.coe_pow, hzdef, div_pow, ← map_pow, hϖ, map_natCast, div_self hg0]
      rfl
    rw [← map_pow, hzm, map_one]
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.RegularSemisimpleFibres.PBaseQ
section
open NumberField IsDedekindDomain ValuativeRel Polynomial Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.L2.Host
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.Shin
open GroundTheory.Global GroundTheory.Global.SemiLocal UpperTheory.V.Published UpperTheory.CBC UpperTheory.Gal.InertialTypesAlt
open scoped Classical
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

theorem UpperTheory.Gal.InertialTypesAlt.baseQ :
    CardRes → BaseQ := by
  intro _ E _ _ v g _ i hi
  have e : 𝓀[v.adicCompletion E] ≃+* ZMod g :=
    (Ideal.quotEquivOfEq (DiscreteGroups.sglob.DzIso.ker_redO i hi).symm).trans
      (RingHom.quotientKerEquivOfSurjective (DiscreteGroups.sglob.DzIso.redO_surjective i hi))
  exact ⟨DiscreteGroups.sglob.DzType.g_not_mem_sq v g i hi, by rw [Nat.card_congr e.toEquiv, Nat.card_zmod], ⟨e⟩⟩
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.RegularSemisimpleFibres.PCardRes
section
open NumberField IsDedekindDomain ValuativeRel Polynomial Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.L2.Host
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.Shin
open GroundTheory.Global GroundTheory.Global.SemiLocal UpperTheory.V.Published UpperTheory.CBC UpperTheory.Gal.InertialTypesAlt
open scoped Classical
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

theorem UpperTheory.Gal.InertialTypesAlt.cardRes :
    CardRes := by
  intro E _ _ v
  rw [GroundTheory.Global.natCard_residueField_integer]
  rfl
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.RegularSemisimpleFibres.PCuspChar
section
noncomputable section

open GlobalTheory.SmGL GlobalTheory.Shin GlobalTheory.SplitWeil

namespace UpperTheory.Gal.InertialTypesAlt

private theorem blk_two {m a : ℕ} (ha : a < m) (hd : ∑ b, (![a, m - a] : Fin 2 → ℕ) b = m) (i : Fin m) :
    (blk (stdBlocks (![a, m - a] : Fin 2 → ℕ) hd) i = 0 ↔ (i : ℕ) < a) := by
  obtain ⟨⟨b, j⟩, hbj⟩ : ∃ p, (stdBlocks (![a, m - a] : Fin 2 → ℕ) hd).symm i = p := ⟨_, rfl⟩
  have hi := stdBlocks_val (![a, m - a] : Fin 2 → ℕ) hd b j
  rw [← hbj, Equiv.apply_symm_apply] at hi
  unfold blk
  rw [hbj]
  have hj := j.isLt
  fin_cases b
  · simp at hi hj ⊢
    omega
  · simp at hi hj ⊢
    omega

private theorem blk_lt_iff {m a : ℕ} (ha : a < m) (hd : ∑ b, (![a, m - a] : Fin 2 → ℕ) b = m) (i j : Fin m) :
    blk (stdBlocks (![a, m - a] : Fin 2 → ℕ) hd) i < blk (stdBlocks (![a, m - a] : Fin 2 → ℕ) hd) j ↔
      (i : ℕ) < a ∧ a ≤ (j : ℕ) := by
  have hi := blk_two ha hd i
  have hj := blk_two ha hd j
  have h1 := (blk (stdBlocks (![a, m - a] : Fin 2 → ℕ) hd) i).isLt
  have h2 := (blk (stdBlocks (![a, m - a] : Fin 2 → ℕ) hd) j).isLt
  rw [Fin.lt_iff_val_lt_val]
  rw [Fin.ext_iff, Fin.val_zero] at hi hj
  omega

private theorem rad_le {F : Type} [Field F] {m a : ℕ} (h0 : 0 < a) (ha : a < m) (H : Subgroup (GL (Fin m) F))
    (hH : (H : Set (GL (Fin m) F)) = {u : GL (Fin m) F | ∀ i j : Fin m, (u : Matrix (Fin m) (Fin m) F) i j = (if i = j then 1 else 0) ∨ (i.val < a ∧ a ≤ j.val)})
    (hd : ∑ b, (![a, m - a] : Fin 2 → ℕ) b = m) (u : GL (Fin m) F)
    (hu : u ∈ unipRad F (stdBlocks (![a, m - a] : Fin 2 → ℕ) hd)) : u ∈ H := by
  have hu' := GlobalTheory.SmGL.CuspMax.mem_unipRad_iff_entries.mp hu
  have hmem : u ∈ (H : Set (GL (Fin m) F)) := by
    rw [hH]
    intro i j
    by_cases h : (i : ℕ) < a ∧ a ≤ (j : ℕ)
    · exact Or.inr h
    · left
      rw [hu' i j (by rwa [blk_lt_iff ha hd])]
      simp [Matrix.one_apply]
  exact hmem

theorem cuspChar : CuspChar := by
  intro F _ _ θ hθ m hm W _ _ _ κ hirr hcusp
  classical
  haveI : Fintype F := Fintype.ofFinite F
  have hc := _root_.GlobalTheory.BI.isChar_and_isIrrChar_of_rep ℂ ℂ (GL (Fin m) F) W κ
  have hprim : GlobalTheory.CuspGL.IsPrimitive
      (GlobalTheory.CuspGL.extZero (fun g : GL (Fin m) F => algebraMap ℂ ℂ (κ.character g))) := by
    refine _root_.GlobalTheory.CuspGL.isPrimitive_extZero_of_sum_unipotent F m _ hc.1 fun a h0 ham => ?_
    obtain ⟨A, H, -, hH, -⟩ := GlobalTheory.T.exists_standardUnipotentRadical_bijOn_nilradical F m a ham.le
    have hd : ∑ b, (![a, m - a] : Fin 2 → ℕ) b = m := by
      simp [Fin.sum_univ_two]
      omega
    have hne : unipRad F (stdBlocks (![a, m - a] : Fin 2 → ℕ) hd) ≠ ⊥ := by
      rw [GlobalTheory.SmGL.CuspMax.unipRad_ne_bot_iff]
      refine ⟨⟨0, hm⟩, ⟨a, ham⟩, ?_⟩
      rw [blk_lt_iff ham hd]
      exact ⟨h0, le_refl a⟩
    have hfix : ∀ v : W, (∀ u ∈ H, κ u v = v) → v = 0 := fun v hv =>
      hcusp 2 _ _ hne v fun u hu => hv u (rad_le h0 ham H hH hd u hu)
    have hz := PositivityTheory.GreenCharacters.sum_char_eq_zero κ H hfix
    rw [← hH, finsum_mem_def, finsum_eq_sum_of_fintype]
    rw [← hz]
    refine Finset.sum_congr rfl fun u _ => ?_
    by_cases hu : u ∈ H <;> simp [Set.indicator_apply, hu]
  obtain ⟨k, hk, hx⟩ := GlobalTheory.CuspFormula.exists_regular F θ hθ m hm _ (hc.2 hirr) hprim
  refine ⟨k, hk, fun x => ?_⟩
  have := hx x
  simp only [Algebra.algebraMap_self, RingHom.id_apply] at this
  exact this

end UpperTheory.Gal.InertialTypesAlt
end
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.RegularSemisimpleFibres.PCuspIne
section
open NumberField IsDedekindDomain ValuativeRel Polynomial Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.L2.Host
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.Shin
open GroundTheory.Global GroundTheory.Global.SemiLocal UpperTheory.V.Published UpperTheory.CBC UpperTheory.Gal.InertialTypesAlt
open scoped Classical
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

set_option maxHeartbeats 800000 in
theorem UpperTheory.Gal.InertialTypesAlt.cuspIne :
    TameRead → TypeChar → NameOf → BaseQ → CuspIne := by
  intro hT hC hN hB
  intro E Ω _ _ _ _ _ A v h g _ i hi Θ hΘ e y c hy hdz hreg htr rc hrc f hf hdiv t ϖ hϖ z hz
  obtain ⟨a, ha, hL⟩ := hrc
  have hty := (UpperTheory.Zero.LLC.typeIff E Ω A v h rc).mp hL.type y
  have hn : 0 < y.fst := Nat.pos_of_dvd_of_pos hdiv hf
  obtain ⟨D⟩ := UpperTheory.Zero.LLC.extEx E Ω A v h g i hi y.fst hn
  obtain ⟨⟨R, hR⟩, hsys⟩ := UpperTheory.Zero.LLC.resEx E Ω A v h g i hi y.fst hn D
  have hrank := (hsys R hR).rank
  obtain ⟨ι, hι⟩ := hT E Ω A v h g y.fst hn D R hR
  obtain ⟨_, hcard, ⟨r⟩⟩ := hB E v g i hi
  haveI : Finite 𝓀[HeightOneSpectrum.adicCompletion E v] :=
    Nat.finite_of_card_ne_zero (by rw [hcard]; exact (Fact.out : g.Prime).ne_zero)
  obtain ⟨θ, hθ, hreg', hnames⟩ :=
    hN g y.fst hn 𝓀[HeightOneSpectrum.adicCompletion E v] D.K (IsLocalRing.ResidueField A) hrank r e ι Θ hΘ c hreg
  have hcls : GlobalTheory.LocLanglands.cls y.snd.rep = y := by
    unfold GlobalTheory.LocLanglands.cls
    exact IrrGL.of_rep y
  have hy' : (GlobalTheory.LocLanglands.cls y.snd.rep).IsCusp := by rw [hcls]; exact hy
  have hdz' : UpperTheory.Zero.LLC.DZ (GlobalTheory.LocLanglands.cls y.snd.rep) := by rw [hcls]; exact hdz
  obtain ⟨τ, hcusp, hinfl⟩ :=
    (UpperTheory.Zero.LLC.typeEx E Ω A v h g i hi y.fst hn y.snd.rep).1 hy' hdz'
  have hchar := hC E v g i hi r y τ hcusp hinfl
  have hnm := hnames τ (fun γ => (hchar γ).trans (htr γ))
  obtain ⟨_, hin⟩ := hty g i hi y.fst hn D R hR θ hreg' τ hcusp hnm y.snd.rep hcls hinfl
  rw [hin t]
  set N := (g ^ f - 1) / (g ^ y.fst - 1) with hN'
  have hdvd : g ^ y.fst - 1 ∣ g ^ f - 1 := by
    obtain ⟨m, hm⟩ := hdiv
    rw [hm, pow_mul]
    simpa only [one_pow] using Nat.sub_dvd_pow_sub_pow (g ^ y.fst) 1 m
  have hϖ' : (ϖ ^ N) ^ (g ^ y.fst - 1) = (g : Ω) := by
    rw [← pow_mul, hN', Nat.div_mul_cancel hdvd, hϖ]
  have hz' : ((z ^ N : A) : Ω) = (t : G E Ω) (ϖ ^ N) / ϖ ^ N := by
    rw [map_pow, ← div_pow, ← hz]
    push_cast
    rfl
  have hιR : ι ((R t : D.Kˣ) : D.K) = (IsLocalRing.residue A z) ^ N := by
    rw [hι t (ϖ ^ N) hϖ' (z ^ N) hz', map_pow]
  refine Finset.prod_congr rfl (fun j _ => ?_)
  congr 2
  rw [map_pow, Units.val_pow_eq_pow_val, hθ, hιR, map_pow, ← pow_mul, ← pow_mul]
  ring_nf
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.RegularSemisimpleFibres.PCuspIrr
section
open NumberField IsDedekindDomain ValuativeRel Polynomial Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.L2.Host
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.Shin
open GroundTheory.Global GroundTheory.Global.SemiLocal UpperTheory.V.Published UpperTheory.CBC UpperTheory.Gal.InertialTypesAlt
open scoped Classical
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

section
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {n : ℕ}

private theorem redK_mem_unipRad {s : ℕ} {d : Fin s → ℕ} (e : (Σ a, Fin (d a)) ≃ Fin n) {g : GL (Fin n) k}
    (hu : g ∈ unipRad k e) (hK : g ∈ KO k (Fin n)) : redK k (Fin n) ⟨g, hK⟩ ∈ unipRad 𝓀[k] e := by
  refine CuspMax.mem_unipRad_iff_entries.2 fun i j hij => ?_
  have h := CuspMax.mem_unipRad_iff_entries.1 hu i j hij
  by_cases hh : i = j
  · subst hh
    have h1 := (redK_eq_iff ⟨g, hK⟩ i i 1).2 (by simp [h])
    simpa using h1
  · rw [Matrix.one_apply_ne hh]
    exact (redK_eq_zero_iff ⟨g, hK⟩ i j).2 (by simp [h, Matrix.one_apply_ne hh])

private theorem finCusp_levelZero {V : Type} [AddCommGroup V] [Module ℂ V] (π : Representation ℂ (GL (Fin n) k) V)
    (hs : IsSmooth π) (hi : π.IsIrreducible) (hc : IsCuspidal π) : PositivityTheory.Rg.DzCount.FinCusp (levelZero π) := by
  intro s d e hne v hv
  have hV : (v : V) ∈ fixed π (KOne k (Fin n) ⊔ (unipRad k e ⊓ KO k (Fin n))) := by
    refine GlobalTheory.DepthZeroJac.mem_fixed_sup v.2 (GlobalTheory.Parabolic.mem_fixed.2 fun g hg => ?_)
    have h1 := congrArg Subtype.val (hv _ (redK_mem_unipRad e hg.1 hg.2))
    rwa [levelZero_apply] at h1
  have hne' : unipRad k e ≠ ⊥ := CuspMax.unipRad_ne_bot_iff.2 (CuspMax.unipRad_ne_bot_iff.1 hne)
  haveI := hc.2 s d e hne'
  exact Subtype.ext (GlobalTheory.DepthZeroJac.depthZeroJacquetInjective k n s d e ⟨V, π, hs, hi⟩ (v : V) hV (Subsingleton.elim _ _))

private theorem irreducible_levelZero (π : IrrRep (GL (Fin n) k)) (ω : kˣ →* ℂˣ) (hω : HasCentralChar π.ρ ω)
    (hF : PositivityTheory.Rg.DzCount.FinCusp (levelZero π.ρ)) (hD : fixed π.ρ (KOne k (Fin n)) ≠ ⊥) :
    (levelZero π.ρ).IsIrreducible := by
  have key : ∀ W : Subrepresentation (levelZero π.ρ), W ≠ ⊥ → W = ⊤ := by
    intro W hW
    haveI : Nontrivial W.toSubmodule := by
      rw [Submodule.nontrivial_iff_ne_bot]
      intro h
      exact hW (Subrepresentation.toSubmodule_injective h)
    let j : W.toSubmodule →ₗ[ℂ] π.V := (fixed π.ρ (KOne k (Fin n))).subtype ∘ₗ W.toSubmodule.subtype
    have hFτ : PositivityTheory.Rg.DzCount.FinCusp W.toRepresentation := by
      intro s d e hne w hw
      exact Subtype.ext (hF s d e hne w (fun u hu => congrArg Subtype.val (hw u hu)))
    have hj : PositivityTheory.Rg.DzCount.IsTypeMap W.toRepresentation π.ρ j := by
      refine ⟨?_, ?_⟩
      · intro a c hac
        exact Subtype.ext (Subtype.ext hac)
      · intro g w
        exact levelZero_apply π.ρ g w
    have hfix := PositivityTheory.Rg.DzCount.B.st6 k W.toSubmodule n W.toRepresentation hFτ π ω hω j hj
    apply Subrepresentation.toSubmodule_injective
    show W.toSubmodule = ⊤
    rw [eq_top_iff]
    intro v _
    have hv : (v : π.V) ∈ LinearMap.range j := hfix ▸ v.2
    obtain ⟨w, hw⟩ := hv
    have hwv : (w : fixed π.ρ (KOne k (Fin n))) = v := Subtype.ext hw
    rw [← hwv]
    exact w.2
  haveI : Nontrivial (Subrepresentation (levelZero π.ρ)) := by
    refine ⟨⟨⊥, ⊤, fun h => hD ?_⟩⟩
    have h' := congrArg Subrepresentation.toSubmodule h
    rw [Submodule.eq_bot_iff]
    intro v hv
    have hm : (⟨v, hv⟩ : fixed π.ρ (KOne k (Fin n))) ∈ (⊤ : Subrepresentation (levelZero π.ρ)).toSubmodule :=
      Submodule.mem_top
    rw [← h'] at hm
    exact congrArg Subtype.val ((Submodule.mem_bot ℂ).1 hm)
  constructor
  intro W
  by_cases h : W = ⊥
  · exact Or.inl h
  · exact Or.inr (key W h)

end

theorem UpperTheory.Gal.InertialTypesAlt.cuspIrr :
    CuspIrr := by
  intro k _ _ _ _ _ y hc hD
  have hadm := (UpperTheory.Zero.LLC.Pr.adm k y.1 y.2.rep.V y.rep y.2.rep.smooth y.2.rep.irr).2 (levelPre ⊥)
    (isOpen_levelPre ⊥) (isCompact_levelPre ⊥)
  rw [levelPre_bot] at hadm
  obtain ⟨ω, hω⟩ := (GlobalTheory.T.centralCharacter_subquotient_productIrreducibles k).1 y
  have hF := finCusp_levelZero y.rep y.2.rep.smooth y.2.rep.irr hc.2
  exact ⟨hadm, irreducible_levelZero y.2.rep ω hω hF hD, hF⟩
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.RegularSemisimpleFibres.PFinSec
section
open NumberField IsDedekindDomain ValuativeRel Polynomial Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.L2.Host
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.Shin
open GroundTheory.Global GroundTheory.Global.SemiLocal UpperTheory.V.Published UpperTheory.CBC UpperTheory.Gal.InertialTypesAlt
open scoped Classical
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

theorem UpperTheory.Gal.InertialTypesAlt.finSec :
    FinSec := by
  intro H U V _ _ _ _ _ _ ρ σ f hf hsurj
  haveI := Fintype.ofFinite H
  obtain ⟨s₀, hs₀⟩ := f.exists_rightInverse_of_surjective (LinearMap.range_eq_top.2 hsurj)
  have hs₀' : ∀ y, f (s₀ y) = y := fun y => LinearMap.congr_fun hs₀ y
  have hc : (Fintype.card H : ℂ) ≠ 0 := Nat.cast_ne_zero.2 Fintype.card_ne_zero
  have hρ : ∀ (a b : H) (x : U), ρ (a * b) x = ρ a (ρ b x) := fun a b x => by
    rw [map_mul]; rfl
  have hσ : ∀ (a b : H) (x : V), σ (a * b) x = σ a (σ b x) := fun a b x => by
    rw [map_mul]; rfl
  have hσ1 : ∀ x : V, σ 1 x = x := fun x => by
    rw [map_one]; rfl
  refine ⟨(Fintype.card H : ℂ)⁻¹ • ∑ g : H, (ρ g) ∘ₗ s₀ ∘ₗ (σ g⁻¹), ?_, ?_⟩
  · intro h x
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [LinearMap.smul_apply, LinearMap.sum_apply, LinearMap.comp_apply, map_smul, map_sum]
    congr 1
    refine Fintype.sum_equiv (Equiv.mulLeft h⁻¹) _ _ fun g => ?_
    simp only [Equiv.coe_mulLeft, mul_inv_rev, inv_inv]
    rw [← hρ, mul_inv_cancel_left, hσ]
  · intro x
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [LinearMap.smul_apply, LinearMap.sum_apply, LinearMap.comp_apply, map_smul, map_sum]
    have : ∀ g : H, f (ρ g (s₀ (σ g⁻¹ x))) = x := fun g => by
      rw [hf, hs₀', ← hσ, mul_inv_cancel, hσ1]
    simp only [this, Finset.sum_const, Finset.card_univ, Nat.cast_smul_eq_nsmul]
    rw [← Nat.cast_smul_eq_nsmul ℂ, smul_smul, inv_mul_cancel₀ hc, one_smul]
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.RegularSemisimpleFibres.PLeTop
section
open NumberField IsDedekindDomain ValuativeRel Polynomial Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.L2.Host
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.Shin
open GroundTheory.Global GroundTheory.Global.SemiLocal UpperTheory.V.Published UpperTheory.CBC UpperTheory.Gal.InertialTypesAlt
open scoped Classical
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

private theorem label_le_preserves_splitting (h₁ : LiftOk) (h₂ : LiftBlocks) {a b : Lbl} (ha : a.Ok) (hab : a.Le b) :
    b.Ok ∧ b.rk = a.rk ∧ ∀ Q, b.Splits Q → a.Splits Q ∧ b.blocks Q = a.blocks Q := by
  induction hab with
  | refl => exact ⟨ha, rfl, fun Q hQ => ⟨hQ, rfl⟩⟩
  | @tail m c _ hstep ih =>
    obtain ⟨l, hl, rfl⟩ := hstep
    obtain ⟨hb, hrk, hS⟩ := ih
    obtain ⟨hc, hrk'⟩ := h₁ m l hl hb
    refine ⟨hc, hrk'.trans hrk, fun Q hQ => ?_⟩
    obtain ⟨hbQ, hblk⟩ := h₂ m l Q hl hb hQ
    obtain ⟨haQ, hblk'⟩ := hS Q hbQ
    exact ⟨haQ, hblk.trans hblk'⟩

theorem UpperTheory.Gal.InertialTypesAlt.leTop :
    LiftOk → LiftBlocks → LeRank → LeTop := by
  intro h₁ h₂ h₃ a b ha hab hs
  obtain ⟨hb, hrk, hS⟩ := label_le_preserves_splitting h₁ h₂ ha hab
  obtain ⟨f, hf, hq, hd⟩ := hs
  obtain ⟨c, hc, hbq, hp⟩ := h₃ a b ha hab
  have hcf : c = f := Nat.pow_right_injective ha.1 (hbq.symm.trans hq)
  subst hcf
  have hone : ∀ p ∈ b.L, p.1 = 1 := by
    intro p hpL
    obtain ⟨r, hr, hpr⟩ := hp p hpL
    have hr0 : 0 < r.1 := (ha.2.2 r hr).1
    rw [Nat.gcd_eq_left (hd r hr)] at hpr
    exact Nat.eq_of_mul_eq_mul_right hr0 (by simpa using hpr)
  refine ⟨hb, hrk, hone, (hS b.q ⟨1, Nat.one_pos, (pow_one _).symm, fun p hpL => ?_⟩).2⟩
  rw [hone p hpL]
end

