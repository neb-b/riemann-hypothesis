module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.DiscreteSeriesCoefficientsCuspidal
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.CuspidalDescent.GLDenseRanges.InertiaPartMaps.Bundle0004
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.ZEqDimE
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.Bundle0004
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.Bundle0014
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.Bundle0008
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.Bundle0044
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.Bundle0009
public import Development.AutomorphicArithmetic.Foundations.LocalLanglands.IsRecTOfIsRec

@[expose] public section

set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Polynomial ValuativeRel IsLocalRing Filter
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.LocGL GlobalTheory.GalOfCusp GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.UnitaryBC
open UpperTheory.V.W (Plc Lp HidaSetting Vl Resid LamObj)
open UpperTheory.V.HV (Coef)
open UpperTheory.V.Hi UpperTheory.V.Hi.CaseU
open UpperTheory.V.Z.Mult (Cp At IsDec CompOf Mult)
open UpperTheory.V.Z.J.D
open scoped Matrix TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option synthInstance.maxHeartbeats 200000
namespace UpperTheory.V.Z.Desc.V0
private theorem ePart_zero {G R W : Type} [Group G] [CommRing R] [AddCommGroup W] [Module R W] (ρ : Representation R G W) :
    ePart ρ 0 0 = ⊤ := by
  simp [ePart, opE]
private theorem card_not_dvd {l : ℕ} [Fact l.Prime] {L Ω : Type} [Field L] [NumberField L] [IsCMField L] [Field Ω] [Algebra L Ω]
    [IsAlgClosure L Ω] (s : HidaSetting l L Ω) (j : ℕ) : ¬ l ∣ Nat.card 𝓀[(s.w s.v0).adicCompletion L] ^ j := by
  have hl : l.Prime := Fact.out
  have hw : (s.w s.v0).under (𝓞 (Lp L)) = s.v0 := by
    ext x
    exact (s.hw s.v0 (algebraMap (𝓞 (Lp L)) (𝓞 L) x)).symm.trans (s.hA s.v0 x)
  have h2 : ((s.p : ℕ) : 𝓞 (Lp L)) ∈ s.v0.asIdeal := by
    rw [← Ideal.Quotient.eq_zero_iff_mem, map_natCast, ← s.norm_v0_eq_one, normV, ← nsmul_one]
    exact card_nsmul_eq_zero'
  have h3 : ((s.p : ℕ) : 𝓞 L) ∈ (s.w s.v0).asIdeal := by
    rw [← hw] at h2
    have h4 : algebraMap (𝓞 (Lp L)) (𝓞 L) ((s.p : ℕ) : 𝓞 (Lp L)) ∈ (s.w s.v0).asIdeal := h2
    rwa [map_natCast] at h4
  have hd : Ideal.absNorm (s.w s.v0).asIdeal ∣ Ideal.absNorm (Ideal.span {((s.p : ℕ) : 𝓞 L)}) :=
    Ideal.absNorm_dvd_absNorm_of_le ((Ideal.span_singleton_le_iff_mem _).2 h3)
  have hn : Ideal.absNorm (Ideal.span {((s.p : ℕ) : 𝓞 L)}) = s.p ^ Module.finrank ℤ (𝓞 L) := by
    rw [Ideal.absNorm_span_singleton, ← map_natCast (algebraMap ℤ (𝓞 L)), Algebra.norm_algebraMap]
    simp [Int.natAbs_pow]
  rw [hn] at hd
  obtain ⟨e, -, he⟩ := (Nat.dvd_prime_pow s.p_prime).1 hd
  have hq : Nat.card 𝓀[(s.w s.v0).adicCompletion L] = s.p ^ e :=
    (resCard_eq_normV _).trans (by rw [normV, ← Ideal.absNorm_eq_natCard, he])
  intro h
  rw [hq] at h
  exact s.p_ne ((Nat.prime_dvd_prime_iff_eq hl s.p_prime).1 (hl.dvd_of_dvd_pow (hl.dvd_of_dvd_pow h))).symm
set_option maxHeartbeats 1600000 in
theorem z_eq_dim_e_of_count_e_res_eq_inv_loc_kir : _root_.UpperTheory.V.Z.Desc.V0.CountEAlt → _root_.UpperTheory.V.Z.J.D.ResidualEqualityRankTwo → InvEq1 → InvBox → LocE → KirCusp → _root_.UpperTheory.V.Z.Desc.V0.ZEqDimEAlt := by
  intro hCount hRes hInv hBox hLoc hKir hP hM hC l _ L Ω _ _ _ _ _ _ s n hn V hV hn4
  obtain ⟨a, j, D₀, hE, hD₀, hdim⟩ := hLoc ((s.w s.v0).adicCompletion L) n
  refine ⟨a, Nat.card 𝓀[(s.w s.v0).adicCompletion L] ^ j, hE, card_not_dvd s j, ?_⟩
  intro Q c r ι m τ₀ hτ A _ _ _ θ hθ lam K D D' h h'
  obtain ⟨a₀, ha⟩ := hCount hP hM hC l L Ω s n hn V hV hn4 ι lam
  have hTeich : ∃ t, r.IsTeich t := by
    obtain ⟨hc, hfin, hlm, -⟩ := UpperTheory.V.abelian₂.dvr_finite l c.O
    have : IsAdicComplete (maximalIdeal c.O) c.O := hc
    have : Finite (ResidueField c.O) := hfin
    have : CharP (ResidueField c.O) l := by
      refine (CharP.charP_iff_prime_eq_zero (Fact.out : l.Prime)).2 ?_
      rwa [← map_natCast (residue c.O), residue_eq_zero_iff]
    have : CharP (c.O ⧸ maximalIdeal c.O) l :=
      inferInstanceAs (CharP (ResidueField c.O) l)
    have : PerfectRing (ResidueField c.O) l := inferInstance
    let lift := Perfection.lift l (ResidueField c.O) (c.O ⧸ maximalIdeal c.O)
    let j := lift (RingHom.id (ResidueField c.O))
    let τ := (Perfection.teichmuller l (maximalIdeal c.O)).comp j.toMonoidHom
    have hτ (x : ResidueField c.O) : residue c.O (τ x) = x :=
      (Perfection.mk_teichmuller (j x)).trans
        (RingHom.congr_fun (lift.symm_apply_apply (RingHom.id (ResidueField c.O))) x)
    refine ⟨fun i => (Units.map τ).comp (r.chib i), fun i g => ⟨hτ _, ?_⟩⟩
    rw [MonoidHom.comp_apply, ← map_pow, ← Nat.card_units, pow_card_eq_one', map_one]
  obtain ⟨t, ht⟩ := hTeich
  obtain ⟨χ, hχ, hext⟩ : ∃ χ : ∀ u : s.St, Fin n → Ine (F := L) (s.A u) →* ℂˣ, _root_.UpperTheory.V.Hi.IsTypeAlt (fun u : s.St => s.hw u)
      ((Matrix.GeneralLinearGroup.map (ι.toRingHom.comp (algebraMap c.O (Qbar l)))).comp τ₀) χ ∧
      ∀ (u : s.St) (i : Fin n), ∃ ψ : Weil (s.hw u) →* ℂˣ, ∀ g, ψ (ineIncl (s.hw u) g) = χ u i g :=
    ⟨_, hτ t ht, fun u i => ⟨W.pushCh (ι.toRingHom.comp (algebraMap c.O (Qbar l)))
      ((t i).comp (V.pr.comp (Weil (s.hw u)).subtype)), fun _ => rfl⟩⟩
  have key : ∀ D : ℕ, _root_.UpperTheory.V.Z.Desc.V0.IsDimEAlt (hset Q τ₀) θ ι lam K (sec0 n s) a (Nat.card 𝓀[(s.w s.v0).adicCompletion L] ^ j) D →
      ∃ (π : CuspSub L n) (σ : Submodule ℂ (UA L n → ℂ)) (C : Comps V σ), (∀ u : s.St, π.IsLocComp (s.w u) (C.u u)) ∧
        (∀ (u : s.St) rc, _root_.UpperTheory.Zero.LLC.IsRecT (s.hw u) rc → IsTypeWD (s.hw u) (χ u) (rc (algNorm (C.u u)))) ∧
        (D : Cardinal) = a₀ * (Module.rank ℂ (cInv1 C ι τ₀) * D₀) ∧ 1 ≤ D := by
    rintro _ ⟨x, d, ξ, c0, sp, ev, hs, hu, hz, hall, rfl⟩
    obtain ⟨e, he⟩ := hs.alg
    obtain ⟨π, σ, C, h1, h2, h3, h4, h5⟩ := ha Q c r m τ₀ hτ d e ξ he A θ x c0 sp hθ hs K ev hu hz hall
    haveI : FiniteDimensional ℂ (zPart (hset Q τ₀) θ ι x.toRingHom lam ξ K c0 ev) :=
      haveI := hs.fin K c0 le_rfl
      Submodule.finiteDimensional_of_le (S₂ := (hset Q τ₀).ClAt θ ι x.toRingHom lam ξ K c0)
        (inf_le_left.trans (iSup_le fun _ => inf_le_left))
    have hb := fun (a' : GLw n (s.w s.v0) →₀ ℤ) (N' : ℕ) => hBox _ _ _ _ (piRep fun u => (C.u u).ρ) C.o.ρ m (KT n (wt s)) (Kc _ n 1)
      ((Matrix.GeneralLinearGroup.map (ι.toRingHom.comp (algebraMap c.O (Qbar l)))).comp τ₀) a' N'
    have h0 := h5 0 0 (by simp)
    have hz0 : Module.finrank ℂ ↥(zPart (hset Q τ₀) θ ι x.toRingHom lam ξ K c0 ev) ≠ 0 :=
      fun hf => hz (Submodule.finrank_eq_zero.1 hf)
    rw [show eC Q τ₀ d 0 0 = ⊤ from ePart_zero _, inf_top_eq, hb 0 0, ePart_zero, inf_top_eq] at h0
    have hne : (a₀ : Cardinal) * (Module.rank ℂ (cInv1 C ι τ₀) * Module.rank ℂ ↥(fixd C.o.ρ (Kc _ n 1))) ≠ 0 :=
      h0 ▸ Nat.cast_ne_zero.2 hz0
    have ha₀ : (a₀ : Cardinal) ≠ 0 := left_ne_zero_of_mul hne
    have hr : Module.rank ℂ (cInv1 C ι τ₀) ≠ 0 := left_ne_zero_of_mul (right_ne_zero_of_mul hne)
    have hf : fixd C.o.ρ (Kc _ n 1) ≠ ⊥ := fun hf => right_ne_zero_of_mul (right_ne_zero_of_mul hne) (by rw [hf]; simp)
    have hd := hdim _ C.o.ρ C.o.smooth (hKir L n hn π (s.w s.v0) C.o h2) hf
    have hD := h5 a (Nat.card 𝓀[(s.w s.v0).adicCompletion L] ^ j) hE.supp
    rw [hb, hd] at hD
    refine ⟨π, σ, C, h1, fun u rc hrc =>
      _root_.UpperTheory.V.Hi.partUR2Type_alt l L Ω s n hn V Q c ι m τ₀ lam d e ξ he σ h4 h3 χ hχ C.u C.hu u rc hrc, hD, ?_⟩
    refine Nat.one_le_iff_ne_zero.2 fun h0' => ?_
    rw [h0', Nat.cast_zero] at hD
    exact mul_ne_zero ha₀ (mul_ne_zero hr (Nat.cast_ne_zero.2 hD₀.ne')) hD.symm
  obtain ⟨π, σ, C, a1, a3, a5, a6⟩ := key D h
  obtain ⟨π', σ', C', b1, b3, b5, -⟩ := key D' h'
  have hr : Module.rank ℂ (cInv1 C ι τ₀) = Module.rank ℂ (cInv1 C' ι τ₀) :=
    hInv l L Ω s n hn V hV c ι m τ₀ σ σ' C C'
      (fun u => hRes hP.litN L Ω n hn π π' (s.w u) (s.A u) (s.hw u) (C.u u) (C'.u u) (a1 u) (b1 u) (χ u) (hext u) (a3 u) (b3 u))
  rw [hr, ← b5] at a5
  exact ⟨a6, Nat.cast_injective (R := Cardinal) a5⟩
end UpperTheory.V.Z.Desc.V0
end
end
