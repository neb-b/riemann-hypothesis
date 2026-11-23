module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.DiscreteSeriesCoefficientsCuspidal
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.WeilDeligneUnramified.WeilCharpolySupport.Bundle0002
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.Bundle0040
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.Bundle0009
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.Bundle0017
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.Bundle0039
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.Bundle0044
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.Bundle0032
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.Bundle0019
public import Development.AutomorphicArithmetic.AutomorphicVarieties.HeckeAlgebras.OrdinaryHeckeCharacters.CLocConj
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.Bundle0003
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.Bundle0042
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.Bundle0041

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.AdjointLiftTransferToUnitaryGroupTwo
section
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
open NumberField IsDedekindDomain ValuativeRel Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.N Polynomial
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.LocGL GlobalTheory.GalOfCusp GlobalTheory.UnitaryBC GlobalTheory.SmGL GlobalTheory.SplitWeil
open UpperTheory.V UpperTheory.V.Af UpperTheory.V.Sd UpperTheory.V.Z.Sym UpperTheory.V.Z.Sym.Dict
open UpperTheory.V.W (Plc Lp)
open UpperTheory.V.Z.Win UpperTheory.GalN.V
open scoped Matrix
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
private theorem flag_exp {U : Type} [CommGroup U] (x y c : U) (a b : ℕ) (p q : ℤ) (ha : 0 < a) (hb : 0 < b)
    (hpq : p ≠ q + 1) (hinf : ∀ k : ℕ, k ≠ 0 → c ^ k ≠ 1)
    (hx : x ^ a = (c ^ p) ^ a) (hy : y ^ a = (c ^ q) ^ a) (h : x ^ b = (y * c) ^ b) : False := by
  have h0 : (x ^ a) ^ b = (y ^ a * c ^ a) ^ b := by
    rw [pow_right_comm, h, pow_right_comm, mul_pow y c a]
  rw [hx, hy] at h0
  simp only [← zpow_natCast, ← zpow_mul, ← zpow_add] at h0
  have h1 : c ^ (p * a * b - (q * a + a) * b) = 1 := by
    rw [zpow_sub, h0, mul_inv_cancel]
  have hne : p * a * b - (q * a + a) * b ≠ 0 := by
    have e : p * a * b - (q * a + a) * b = (p - (q + 1)) * a * b := by ring
    rw [e]
    have h2 : p - (q + 1) ≠ 0 := sub_ne_zero.2 hpq
    have h3 : (a : ℤ) ≠ 0 := by exact_mod_cast ha.ne'
    have h4 : (b : ℤ) ≠ 0 := by exact_mod_cast hb.ne'
    exact mul_ne_zero (mul_ne_zero h2 h3) h4
  exact hinf _ (Int.natAbs_ne_zero.2 hne) (pow_natAbs_eq_one.2 h1)
private theorem pow_fix {F Ω : Type} [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [Algebra ℚ Ω] [IsScalarTower ℚ F Ω]
    (σ : G ℚ Ω) : ∃ n : ℕ, 0 < n ∧ ∀ x : F, (σ ^ n) (algebraMap F Ω x) = algebraMap F Ω x := by
  have key : ∀ i j : ℕ, i < j → (∀ x : F, (σ ^ i) (algebraMap F Ω x) = (σ ^ j) (algebraMap F Ω x)) →
      ∃ n : ℕ, 0 < n ∧ ∀ x : F, (σ ^ n) (algebraMap F Ω x) = algebraMap F Ω x := by
    intro i j hij h
    refine ⟨j - i, by omega, fun x => (σ ^ i).injective ?_⟩
    have e : σ ^ j = σ ^ i * σ ^ (j - i) := by rw [← pow_add]; congr 1; omega
    rw [h x, e]
    rfl
  let e : F →ₐ[ℚ] Ω := IsScalarTower.toAlgHom ℚ F Ω
  let f : ℕ → (F →ₐ[ℚ] Ω) := fun k => ((σ ^ k : G ℚ Ω) : Ω →ₐ[ℚ] Ω).comp e
  obtain ⟨i, j, hij, hf⟩ := Finite.exists_ne_map_eq_of_infinite f
  rcases lt_or_gt_of_ne hij with h | h
  · exact key i j h fun x => DFunLike.congr_fun hf x
  · exact key j i h fun x => (DFunLike.congr_fun hf x).symm
private theorem cyc_inf_over (F Ω : Type) [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω]
    (l : ℕ) [hl : Fact l.Prime] (A : ValuationSubring Ω) (hA : A.valuation (l : Ω) < 1) :
    ∃ s ∈ Ine (F := F) A, ∀ k : ℕ, k ≠ 0 → cycBar F Ω l s ^ k ≠ 1 := by
  haveI : CharZero Ω := charZero_of_injective_algebraMap (algebraMap F Ω).injective
  haveI : IsAlgClosure ℚ Ω := ⟨IsAlgClosure.isAlgClosed F, Algebra.IsAlgebraic.trans ℚ F Ω⟩
  have hu : IsUnit ((l + 1 : ℕ) : ℤ_[l]) := by
    rw [PadicInt.isUnit_iff]
    exact PadicInt.norm_natCast_eq_one_iff.2 (by simp)
  obtain ⟨σ, hσ, he⟩ := GlobalTheory.CycInertia.cycZ_Ine_surjective Ω l A hA hu.unit
  obtain ⟨n, hn, hfix⟩ := pow_fix (F := F) σ
  let τ : G F Ω := AlgEquiv.ofRingEquiv (f := (σ ^ n).toRingEquiv) hfix
  have hτ : τ.restrictScalars ℚ = σ ^ n := by ext x; rfl
  have hmem : τ ∈ Ine (F := F) A := by
    have h1 : τ.restrictScalars ℚ ∈ Ine (F := ℚ) A := by rw [hτ]; exact pow_mem hσ n
    exact h1
  have hz : cycZ F Ω l τ = hu.unit ^ n := by
    have h1 : cycZ ℚ Ω l (τ.restrictScalars ℚ) = cycZ F Ω l τ := rfl
    rw [← h1, hτ, map_pow, he]
  refine ⟨τ, hmem, fun k hk h => ?_⟩
  have h2 : ((cycBar F Ω l τ : (Qbar l)ˣ) : Qbar l) = ((l + 1 : ℕ) : Qbar l) ^ n := by
    change algebraMap ℚ_[l] (Qbar l) (PadicInt.Coe.ringHom ((cycZ F Ω l τ : ℤ_[l]ˣ) : ℤ_[l])) = _
    rw [hz, Units.val_pow_eq_pow_val, hu.unit_spec, map_pow, map_pow, map_natCast, map_natCast]
  have h3 := congrArg Units.val h
  rw [Units.val_pow_eq_pow_val, h2, Units.val_one, ← Nat.cast_pow, ← Nat.cast_pow, Nat.cast_eq_one, Nat.pow_eq_one] at h3
  have := hl.out.pos
  rcases h3 with h3 | h3
  · rw [Nat.pow_eq_one] at h3
    omega
  · omega
private theorem pot_of_above {L Ω : Type} [Field L] [NumberField L] [Field Ω] [Algebra L Ω] [IsAlgClosure L Ω] {l : ℕ} [Fact l.Prime]
    {r : G L Ω →* GL (Fin 2) (Qbar l)} {m : ℕ} (hm : 2 ≤ m) {w : Plc L} (hw : ((l : ℕ) : 𝓞 L) ∈ w.asIdeal)
    (H : ∀ A : ValuationSubring Ω, A.valuation (l : Ω) < 1 →
      ∃ (b : ℤ) (k : ℕ) (κ : Fin 2 → ↥(Dec (F := L) A) →* (Qbar l)ˣ), 0 < k ∧ IsFlagOn r (Dec (F := L) A) κ ∧
        ∀ s : ↥(Dec (F := L) A), (s : G L Ω) ∈ Ine (F := L) A →
          κ 0 s ^ k = (cycBar L Ω l s ^ (b + m)) ^ k ∧ κ 1 s ^ k = (cycBar L Ω l s ^ b) ^ k) : PotUnl r w := by
  intro A hA
  have hAl : A.valuation (l : Ω) < 1 := by
    have h1 := (hA ((l : ℕ) : 𝓞 L)).2 hw
    simpa only [map_natCast] using h1
  obtain ⟨b, k, κ, hk, hflag, hκ⟩ := H A hAl
  refine ⟨κ, hflag, fun i j c hc h => ?_⟩
  obtain ⟨s, hs, hinf⟩ := cyc_inf_over L Ω l A hAl
  let t : ↥(Dec (F := L) A) := ⟨s, Ine_le_Dec A hs⟩
  have h1 : κ i t ^ c = (κ j t * cycBar L Ω l s) ^ c := DFunLike.congr_fun h t
  obtain ⟨h2, h3⟩ := hκ t hs
  have he : ∀ i : Fin 2, κ i t ^ k = (cycBar L Ω l s ^ (![b + m, b] i)) ^ k := fun i => by
    fin_cases i
    · exact h2
    · exact h3
  have hne : ∀ i j : Fin 2, ![b + (m : ℤ), b] i ≠ ![b + (m : ℤ), b] j + 1 := fun i j => by
    fin_cases i <;> fin_cases j <;> simp <;> omega
  exact flag_exp (κ i t) (κ j t) (cycBar L Ω l s) k c _ _ hk hc (hne i j) hinf (he i) (he j) h1
private theorem unr_of_comp {L : Type} [Field L] [NumberField L] [IsCMField L] {n : ℕ} {w : Plc L}
    {σ : Submodule ℂ (UA L n → ℂ)} {τ : SmIrr (GL (Fin n) (Kw w))} (hs : IsSplitAt w) (hτ : Comp σ w τ)
    (hf : Af.HasFixed τ.ρ (GlobalTheory.LFun.KGL w (n := n))) : IsUnramU σ w := by
  obtain ⟨e, he⟩ := GlobalTheory.locU_equiv_GL L n w hs
  obtain ⟨hi, f, f0, fm, fe⟩ := hτ
  obtain ⟨z, hz, hfix⟩ := hf
  refine ⟨f z, fm z, fun h0 => ?_, fun x hx hk => ?_⟩
  · let K : Subrepresentation τ.ρ := ⟨LinearMap.ker f, fun g v hv => by
      obtain ⟨x, rfl⟩ : ∃ x : locU n w, cLoc w (x : UA L n) = g := ⟨e.symm g, (he _).symm.trans (e.apply_symm_apply g)⟩
      rw [LinearMap.mem_ker] at hv ⊢
      exact (fe x v).trans (by rw [hv, map_zero])⟩
    rcases hi.eq_bot_or_eq_top K with hK | hK
    · have h1 : z ∈ K.toSubmodule := h0
      rw [hK] at h1
      exact hz h1
    · refine f0 (LinearMap.ext fun v => ?_)
      have h1 : v ∈ K.toSubmodule := by rw [hK]; trivial
      exact h1
  · rw [← fe ⟨x, hx⟩ z]
    exact congrArg f (hfix _ hk)
theorem UpperTheory.V.Z.Sym.W.aboveWeight : _root_.UpperTheory.V.Z.Sym.W.AboveWeightAlt := by
  intro P L Ω _ _ _ _ _ _ l _ ι hl M m hM hlM hU r hr
  have PA := P.af
  have hc := hr.cont
  obtain ⟨π, hreg, hd, hatt⟩ := hr.aut
  have hpol : ∃ χ, GlobalTheory.ContraPair.PolarizedPair π χ := by
    refine ⟨quadChar L ^ 2, fun v => ?_, ?_⟩
    · have e : (quadChar L ^ 2).locInf v (-1) = (quadChar L).locInf v (-1) ^ 2 := rfl
      rw [e, quadChar_locInf]
    · rw [map_pow, compNorm_quadChar, one_pow]
      exact (GlobalTheory.ContraPair.dualIsConjBy_one π).2 hd
  obtain ⟨HT, hwt, hLG⟩ := P.compat L Ω l ι 2 one_le_two r π hc hreg hpol hatt
  have hg : ∀ (w : Plc L) (A : ValuationSubring Ω) (hA : IsPlaceOver A w) (rc : IrrGL (k := w.adicCompletion L) → WD hA), UpperTheory.Zero.LLC.IsRecT hA rc →
      ∀ τ, π.IsLocComp w τ → GlobalTheory.RoadU.PlainTor (IrrGL.of τ.ρ τ.smooth τ.irred) ∧ UpperTheory.GalStar.Tor (rc (algNorm τ)) ∧ (rc (algNorm τ)).mono0 :=
    fun w A hA rc hrc τ hτ => guard_of P.plain hreg hatt hr.wit (by
      by_cases e : ((l : ℕ) : 𝓞 L) ∈ w.asIdeal
      · exact Or.inr (Or.inr (pot_of_above hr.gap e hr.above))
      · exact Or.inl e) hrc hτ
  have hex : ∀ w : Plc L, ∃ τ, π.IsLocComp w τ := fun w => (_root_.UpperTheory.V.Af.local_comp_complex_of_printed_results PA L 2 π w).1
  have hpt : ∀ (w : Plc L) τ, π.IsLocComp w τ → UpperTheory.V.Z.Sym.W.PT τ := fun w τ hτ => by
    obtain ⟨A, hA⟩ : ∃ A : ValuationSubring Ω, IsPlaceOver A w := exists_isPlaceOver Ω w
    obtain ⟨rc, hrc⟩ := _root_.UpperTheory.V.Z.Win.exRec'_alt PA.litN hA
    exact (hg w A hA rc hrc τ hτ).1
  have hb : ∀ φ : L →+* Qbar l, ∃ b : ℤ, HT φ = {b, b + m} := fun φ => by
    have hw : ((l : ℕ) : 𝓞 L) ∈ (GlobalTheory.EvExtend.placeOf φ).asIdeal := by
      rw [GlobalTheory.EvExtend.mem_placeOf]
      simpa using GlobalTheory.EvExtend.norm_natCast_lt_one (l := l)
    obtain ⟨A, hA⟩ : ∃ A : ValuationSubring Ω, IsPlaceOver A (GlobalTheory.EvExtend.placeOf φ) := exists_isPlaceOver Ω _
    have hAl : A.valuation (l : Ω) < 1 := by simpa only [map_natCast] using (hA _).2 hw
    obtain ⟨τ, hτ⟩ := hex (GlobalTheory.EvExtend.placeOf φ)
    obtain ⟨-, b, hb⟩ := _root_.UpperTheory.V.Z.Sym.W.above_w_statement PA L Ω l ι hl r hc m hr.gap _ hw HT ((hLG _ _ hτ).2 (hpt _ _ hτ)) A hA
      (hr.above A hAl) τ (hLG _ _ hτ).1 (hpt _ _ hτ)
    obtain ⟨j, hj, hx, -⟩ := GlobalTheory.EvExtend.exists_ext φ
    refine ⟨b, ?_⟩
    have := hb ⟨j, hj⟩
    rwa [show (j.comp (algebraMap L _)) = φ from RingHom.ext hx] at this
  have hrw : Z.Desc.RegWt π := fun u => by
    obtain ⟨b, h2⟩ := hb (ι.symm.toRingHom.comp u.embedding)
    have h3 := hwt (ι.symm.toRingHom.comp u.embedding)
    have e : ι.toRingHom.comp (ι.symm.toRingHom.comp u.embedding) = u.embedding := RingHom.ext fun x => by simp
    rw [e, h2] at h3
    have hm : (2 : ℤ) ≤ m := by exact_mod_cast hr.gap
    have hs : StrictAnti ![-b, 1 - b - m] := by
      intro i j hij
      fin_cases i <;> fin_cases j <;> simp at hij ⊢
      omega
    refine ⟨u.embedding, ⟨![-b, 1 - b - m], hs.antitone⟩, u.mk_embedding, hs, ?_⟩
    have h4 := GlobalTheory.CuspRep.ParLaws.hasInfChar_infChar (CG.mk π) u.embedding
    have h5 : (CG.mk π).infChar u.embedding = infOfWeight ⟨![-b, 1 - b - m], hs.antitone⟩ := by
      refine Multiset.map_injective (sub_right_injective (b := (((2 : ℕ) : ℂ) - 1) / 2)) (h3.symm.trans ?_)
      rw [infOfWeight, Multiset.map_map, show (Finset.univ : Finset (Fin 2)).val = {0, 1} from rfl]
      simp only [Multiset.insert_eq_cons, Multiset.map_cons, Multiset.map_singleton, Function.comp_apply]
      congr 1
      · simp
      · congr 1
        simp
        ring
    rw [h5] at h4
    exact h4
  have hk : ∀ (k : ℕ) (w : Plc L), (k : 𝓞 L) ∈ w.asIdeal ↔ (k : 𝓞 (Lp L)) ∈ (w.under (𝓞 (Lp L))).asIdeal := fun k w => by
    rw [← map_natCast (algebraMap (𝓞 (Lp L)) (𝓞 L))]
    rfl
  have hlm : ∀ w : Plc L, ((l : ℕ) : 𝓞 L) ∈ w.asIdeal → (M : 𝓞 L) ∈ w.asIdeal := fun w hw => by
    obtain ⟨c, rfl⟩ := hlM
    rw [Nat.cast_mul]
    exact Ideal.mul_mem_right _ _ hw
  have hfin : {v : HeightOneSpectrum (𝓞 (Lp L)) | (M : 𝓞 (Lp L)) ∈ v.asIdeal}.Finite := by
    have h0 : Ideal.span {(M : 𝓞 (Lp L))} ≠ 0 := by
      rw [Ne, Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot]
      exact_mod_cast hM
    exact (Ideal.finite_factors h0).subset fun v hv => Ideal.dvd_span_singleton.mpr hv
  have hfix : ∀ w : Plc L, (M : 𝓞 L) ∉ w.asIdeal → ∀ τ, π.IsLocComp w τ → Af.HasFixed τ.ρ (GlobalTheory.LFun.KGL w (n := 2)) := fun w hw τ hτ => by
    obtain ⟨A, hA⟩ : ∃ A : ValuationSubring Ω, IsPlaceOver A w := exists_isPlaceOver Ω w
    obtain ⟨rc, hrc⟩ := _root_.UpperTheory.V.Z.Win.exRec'_alt PA.litN hA
    have hl' := mt (hlm w) hw
    have hq := hg w A hA rc hrc τ hτ
    exact _root_.UpperTheory.V.Z.Desc.W.sphT_alt PA.litN L Ω l ι 2 r hc w hl' A hA (hr.unr A fun h => hw ((hA _).1 (by simpa only [map_natCast] using h))) rc hrc τ hq.1
      ((((hLG w τ hτ).1 A hA rc hrc).1 hl').isWDOf hq.2)
  obtain ⟨σ, hσ, hunr, hsat⟩ := P.desc L hU.unr l Fact.out _ hfin (fun w hw => hU.split w ((hk M w).2 hw))
    (fun w hw => (hk M w).1 (hlm w hw)) 2 le_rfl (by norm_num) π hreg hrw hd
    fun w hw => by
      have hw' : (M : 𝓞 L) ∉ w.asIdeal := mt (hk M w).1 hw
      obtain ⟨⟨τ, hτ⟩, hi⟩ := _root_.UpperTheory.V.Af.local_comp_complex_of_printed_results PA L 2 π w
      obtain ⟨b, hb⟩ := (_root_.UpperTheory.V.Af.satake_local_of_printed_results PA L 2 w τ).1 (hfix w hw' τ hτ)
      exact ⟨b, ((_root_.UpperTheory.V.Af.satake_local_of_printed_results PA L 2 w τ).2 _ π.finPart (hi τ hτ) b).2 hb⟩
  obtain ⟨hloc, hinf⟩ := P.same L Ω hU.unr l ι 2 one_le_two π r hc hatt σ hσ hsat
  choose τ₀ hτ₀ using hex
  have hcl : ∀ w, IsSplitAt w → ∀ τ, Comp σ w τ → IrrGL.of τ.ρ τ.smooth τ.irred = IrrGL.of (τ₀ w).ρ (τ₀ w).smooth (τ₀ w).irred :=
    fun w hw τ hτ => IrrGL.of_eq_of.2 (UpperTheory.building_component_uniqueness L 2 σ hσ w hw _ _ _ _ hτ (hloc w hw _ (hτ₀ w)))
  refine ⟨σ, HT, hσ, ⟨hc, fun w hs => ⟨τ₀ w, hloc w hs _ (hτ₀ w)⟩, fun w hs τ hτ A hA rc hrc => ?_, hr.pair⟩,
    fun w hs τ hτ => ⟨?_, (hLG w _ (hτ₀ w)).2 (hpt w _ (hτ₀ w))⟩, fun w hw => ?_, fun v => ?_⟩
  · have e : algNorm τ = algNorm (τ₀ w) := by
      unfold algNorm
      rw [hcl w hs τ hτ]
    rw [e]
    exact (hLG w _ (hτ₀ w)).1 A hA rc hrc
  · have h := hpt w _ (hτ₀ w)
    unfold UpperTheory.V.Z.Sym.W.PT at h ⊢
    rw [hcl w hs τ hτ]
    exact h
  · by_cases hs : IsSplitAt w
    · exact unr_of_comp hs (hloc w hs _ (hτ₀ w)) (hfix w hw _ (hτ₀ w))
    · exact hunr w hs
  · obtain ⟨lam, h1, h2⟩ := hinf v.embedding
    have e : ι.toRingHom.comp (ι.symm.toRingHom.comp v.embedding) = v.embedding := RingHom.ext fun x => by simp
    obtain ⟨b, h3⟩ := hb (ι.symm.toRingHom.comp v.embedding)
    have h4 := hwt (ι.symm.toRingHom.comp v.embedding)
    rw [e, h3, CG.HasInfChar.infChar_eq (π := CG.mk π) h2] at h4
    have h5 := Ga.wtOf m b lam h4
    have := hr.gap
    exact ⟨lam, h1, by omega⟩
end
end
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.CLocConj
section
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 200000

section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Polynomial ValuativeRel IsLocalRing GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.LocGL GlobalTheory.GalOfCusp GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.UnitaryBC UpperTheory.V UpperTheory.V.Hi UpperTheory.V.Hi.CaseU
open UpperTheory.V.W (Plc Lp HidaSetting Vl Resid LamObj UniversalOrdinaryDeterminantRing Pair)
open UpperTheory.V.HV (Coef)
open scoped TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option synthInstance.maxHeartbeats 200000
namespace UpperTheory.V.Hi.AxU
open GlobalTheory.SplitPts
variable {l : ℕ} [Fact l.Prime] {L Ω : Type} [Field L] [NumberField L] [IsCMField L] [Field Ω] [Algebra L Ω]
  [IsAlgClosure L Ω] {n : ℕ}
private theorem sameOver {w w' : Plc L} (h : w'.under (𝓞 (Lp L)) = w.under (𝓞 (Lp L))) :
    w' = w ∨ w = conjSrc (conjE L) w' :=
  ((GlobalTheory.Mem.Chr.under_eq_iff_conjPl (IsCMField.complexConj L)
    (Algebra.IsQuadraticExtension.finrank_eq_two _ _) (IsCMField.complexConj_ne_one L) w w').1 h).imp_right eq_conjSrc
private theorem cLoc_conj (x : UA L n) (u : Plc L) :
    cLoc u x = invT n _ (Matrix.GeneralLinearGroup.map (conjLoc (conjE L) u) (cLoc (conjSrc (conjE L) u) x)) := by
  have h := comp_eq x u
  rw [← inv_inj]
  apply Units.ext
  rw [Matrix.coe_units_inv, Matrix.inv_eq_left_inv h]
  rfl
private theorem mem_O {w : Plc L} (x : w.adicCompletion L) : x ∈ 𝒪[w.adicCompletion L] ↔ Valued.v x ≤ 1 := by
  have h : valuation (w.adicCompletion L) x ≤ valuation (w.adicCompletion L) 1 ↔
      Valued.v x ≤ Valued.v (1 : w.adicCompletion L) := by
    rw [← Valuation.Compatible.vle_iff_le]
    exact Iff.rfl
  change valuation _ x ≤ 1 ↔ _
  simpa using h
private theorem cLoc_one {w w' : Plc L} (h : w'.under (𝓞 (Lp L)) = w.under (𝓞 (Lp L))) (x : UA L n)
    (hx : cLoc w x = 1) : cLoc w' x = 1 := by
  rcases sameOver h with rfl | rfl
  · exact hx
  · rw [cLoc_conj, hx, map_one, map_one]
private theorem cLoc_KO {w w' : Plc L} (h : w'.under (𝓞 (Lp L)) = w.under (𝓞 (Lp L))) (x : UA L n)
    (hx : cLoc w x ∈ KO (w.adicCompletion L) (Fin n)) : cLoc w' x ∈ KO (w'.adicCompletion L) (Fin n) := by
  rcases sameOver h with rfl | rfl
  · exact hx
  · rw [cLoc_conj]
    rw [GlobalTheory.SplitFlip.mem_KO_iff] at hx ⊢
    refine ⟨fun i j => ?_, fun i j => ?_⟩
    · exact (mem_O _).2 (((conjLoc_spec (conjE L) w').2.2 _).trans_le ((mem_O _).1 (hx.2 j i)))
    · exact (mem_O _).2 (((conjLoc_spec (conjE L) w').2.2 _).trans_le ((mem_O _).1 (hx.1 j i)))
private theorem l_iff {w w' : Plc L} (h : w'.under (𝓞 (Lp L)) = w.under (𝓞 (Lp L))) :
    ((l : ℕ) : 𝓞 L) ∈ w'.asIdeal ↔ ((l : ℕ) : 𝓞 L) ∈ w.asIdeal := by
  have key : ∀ u : Plc L, ((l : ℕ) : 𝓞 L) ∈ u.asIdeal ↔ ((l : ℕ) : 𝓞 (Lp L)) ∈ (u.under (𝓞 (Lp L))).asIdeal := fun u => by
    change _ ↔ algebraMap (𝓞 (Lp L)) (𝓞 L) _ ∈ u.asIdeal
    rw [map_natCast]
  rw [key, key, h]
private theorem cmp_eq {w : Plc L} (h : ((l : ℕ) : 𝓞 L) ∉ w.asIdeal) (x : UA L n) :
    cmp n w ((away l L n).rangeRestrict x) = cLoc w x := by
  unfold CaseU.cmp
  rw [dite_eq_left h]
  rfl
private theorem cmp_l {w : Plc L} (h : ((l : ℕ) : 𝓞 L) ∈ w.asIdeal) (x : Ga l L n) : cmp n w x = 1 := by
  unfold CaseU.cmp
  rw [dite_eq_right (not_not.2 h)]
  rfl
private theorem ga_ext {x y : Ga l L n} (h : ∀ w, cmp n w x = cmp n w y) : x = y := by
  obtain ⟨x, rfl⟩ := (away l L n).rangeRestrict_surjective x
  obtain ⟨y, rfl⟩ := (away l L n).rangeRestrict_surjective y
  refine Subtype.ext (funext fun w => ?_)
  have := h w.1
  rwa [cmp_eq w.2, cmp_eq w.2] at this
private theorem cmp_one {w w' : Plc L} (h : w'.under (𝓞 (Lp L)) = w.under (𝓞 (Lp L))) (x : Ga l L n)
    (hx : cmp n w x = 1) : cmp n w' x = 1 := by
  by_cases hl : ((l : ℕ) : 𝓞 L) ∈ w'.asIdeal
  · exact cmp_l hl x
  obtain ⟨x, rfl⟩ := (away l L n).rangeRestrict_surjective x
  rw [cmp_eq (mt (l_iff h).2 hl)] at hx
  rw [cmp_eq hl]
  exact cLoc_one h x hx
private theorem cmp_KO {w w' : Plc L} (h : w'.under (𝓞 (Lp L)) = w.under (𝓞 (Lp L))) (x : Ga l L n)
    (hx : cmp n w x ∈ KO (w.adicCompletion L) (Fin n)) : cmp n w' x ∈ KO (w'.adicCompletion L) (Fin n) := by
  by_cases hl : ((l : ℕ) : 𝓞 L) ∈ w'.asIdeal
  · rw [cmp_l hl x]
    exact one_mem _
  obtain ⟨x, rfl⟩ := (away l L n).rangeRestrict_surjective x
  rw [cmp_eq (mt (l_iff h).2 hl)] at hx
  rw [cmp_eq hl]
  exact cLoc_KO h x hx
variable (s : HidaSetting l L Ω)
private theorem under_w (v : Plc (Lp L)) : (s.w v).under (𝓞 (Lp L)) = v := by
  ext x
  exact (s.hw v (algebraMap (𝓞 (Lp L)) (𝓞 L) x)).symm.trans (s.hA v x)
private theorem mem_locA {w : Plc L} {x : Ub n s} :
    x ∈ locA n s w ↔ ∀ w' : Plc L, w'.under (𝓞 (Lp L)) ≠ w.under (𝓞 (Lp L)) → cmp n w' (x : Ga l L n) = 1 := by
  simp only [locA, Subgroup.mem_iInf, MonoidHom.mem_ker]
  rfl
private theorem sec_mem (w : Plc L) (g : GLw n w) : sec n s w g ∈ locA n s w := by
  unfold sec
  split_ifs
  · exact Subtype.property _
  · exact one_mem _
private theorem comm {w : Plc L} {u x : Ub n s} (hu : cmp n w (u : Ga l L n) = 1) (hx : x ∈ locA n s w) :
    Commute u x := by
  refine Subtype.ext (ga_ext fun w' => ?_)
  rw [Subgroup.coe_mul, Subgroup.coe_mul, map_mul, map_mul]
  by_cases h : w'.under (𝓞 (Lp L)) = w.under (𝓞 (Lp L))
  · rw [cmp_one h _ hu, one_mul, mul_one]
  · rw [(mem_locA s).1 hx w' h, one_mul, mul_one]
private theorem comm' {w w' : Plc L} (h : w'.under (𝓞 (Lp L)) ≠ w.under (𝓞 (Lp L))) (g : GLw n w) (g' : GLw n w') :
    Commute (sec n s w g) (sec n s w' g') :=
  comm s ((mem_locA s).1 (sec_mem s w g) w' h) (sec_mem s w' g')
private theorem toKT_sec {w : Plc L} (h : w.under (𝓞 (Lp L)) ∉ s.S) (g : GLw n w) : toKT n s (sec n s w g) = 1 := by
  refine Subtype.ext (funext fun u => ?_)
  refine (mem_locA s).1 (sec_mem s w g) (s.w u) fun e => h ?_
  rw [← e, under_w]
  exact Or.inr (Or.inl u.2)
private theorem away_l {w : Plc L} (h : w.under (𝓞 (Lp L)) ∉ s.S) : ((l : ℕ) : 𝓞 L) ∉ w.asIdeal := fun e =>
  h (Or.inl (by
    change algebraMap (𝓞 (Lp L)) (𝓞 L) _ ∈ w.asIdeal
    rwa [map_natCast]))
variable {s} {V : s.Lev} (Q : QData V)
private theorem mem_UQ {x : Ub n s} : x ∈ UQ n Q ↔
    (∀ w : Plc L, w.under (𝓞 (Lp L)) ∉ V.S' → cmp n w (x : Ga l L n) ∈ KO (w.adicCompletion L) (Fin n)) ∧
      ∀ q, cmp n (Q.wq q) (x : Ga l L n) = 1 := by
  simp only [UQ, Subgroup.mem_inf, Subgroup.mem_iInf, MonoidHom.mem_ker, Subgroup.mem_comap]
  rfl
private theorem wq_mem (q : Q.Q) : (Q.wq q).under (𝓞 (Lp L)) ∈ V.S' := by
  rw [Q.range]
  exact Or.inr ⟨q, rfl⟩
private theorem sec_KO (hn : 1 ≤ n) {w : Plc L} (hw : w.under (𝓞 (Lp L)) ∉ V.S') (hs : IsSplitAt w) {k : GLw n w}
    (hk : k ∈ KO (w.adicCompletion L) (Fin n)) : sec n s w k ∈ UQ n Q := by
  have hc := ((secU l L Ω s n hn w hs).2 fun h => hw (V.sub h)).2.1 k
  refine (mem_UQ Q).2 ⟨fun w' _ => ?_, fun q => ?_⟩
  · by_cases h : w'.under (𝓞 (Lp L)) = w.under (𝓞 (Lp L))
    · exact cmp_KO h _ (by rwa [hc])
    · rw [(mem_locA s).1 (sec_mem s w k) w' h]
      exact one_mem _
  · exact (mem_locA s).1 (sec_mem s w k) _ fun e => hw (e ▸ wq_mem Q q)
private theorem dec (hn : 1 ≤ n) {w : Plc L} (hw : w.under (𝓞 (Lp L)) ∉ V.S') (hs : IsSplitAt w) {u : Ub n s}
    (hu : u ∈ UQ n Q) : ∃ k ∈ KO (w.adicCompletion L) (Fin n), ∃ u' ∈ UQ n Q,
      u = sec n s w k * u' ∧ ∀ g, Commute u' (sec n s w g) := by
  have hc := ((secU l L Ω s n hn w hs).2 fun h => hw (V.sub h)).2.1
  have hk := ((mem_UQ Q).1 hu).1 w hw
  refine ⟨_, hk, (sec n s w (cmp n w (u : Ga l L n)))⁻¹ * u, mul_mem (inv_mem (sec_KO Q hn hw hs hk)) hu,
    (mul_inv_cancel_left _ _).symm, fun g => comm s ?_ (sec_mem s w g)⟩
  rw [Subgroup.coe_mul, Subgroup.coe_inv, map_mul, map_inv, hc, inv_mul_cancel]
variable (s) in
private theorem sec_cmp (hn : 1 ≤ n) {w : Plc L} (hw : w.under (𝓞 (Lp L)) ∉ s.S) (hs : IsSplitAt w) {x : Ub n s}
    (hx : x ∈ locA n s w) : sec n s w (cmp n w (x : Ga l L n)) = x := by
  obtain ⟨hb, hc, hm⟩ := (secU l L Ω s n hn w hs).2 hw
  exact congrArg Subtype.val (hb.1 (a₁ := ⟨_, hm _⟩) (a₂ := ⟨x, hx⟩) (hc _))
variable (s) in
private theorem same (hn : 1 ≤ n) {w w' : Plc L} (hw : w.under (𝓞 (Lp L)) ∉ s.S) (hs : IsSplitAt w) (hs' : IsSplitAt w')
    (h : w'.under (𝓞 (Lp L)) = w.under (𝓞 (Lp L))) :
    ∃ e : GLw n w' ≃* GLw n w, (∀ g, e g ∈ KO (w.adicCompletion L) (Fin n) ↔ g ∈ KO (w'.adicCompletion L) (Fin n)) ∧
      ∀ g, sec n s w' g = sec n s w (e g) := by
  have hw' : w'.under (𝓞 (Lp L)) ∉ s.S := by rwa [h]
  have hc := ((secU l L Ω s n hn w hs).2 hw).2.1
  have hc' := ((secU l L Ω s n hn w' hs').2 hw').2.1
  have h1 : ∀ g, sec n s w (cmp n w (sec n s w' g : Ga l L n)) = sec n s w' g := fun g =>
    sec_cmp s hn hw hs ((mem_locA s).2 fun u hu => (mem_locA s).1 (sec_mem s w' g) u (by rwa [h]))
  have h2 : ∀ g, sec n s w' (cmp n w' (sec n s w g : Ga l L n)) = sec n s w g := fun g =>
    sec_cmp s hn hw' hs' ((mem_locA s).2 fun u hu => (mem_locA s).1 (sec_mem s w g) u (by rwa [← h]))
  refine ⟨{ toFun := fun g => cmp n w (sec n s w' g : Ga l L n)
            invFun := fun g => cmp n w' (sec n s w g : Ga l L n)
            left_inv := fun g => by simp only [h1, hc']
            right_inv := fun g => by simp only [h2, hc]
            map_mul' := fun g g' => by rw [map_mul, Subgroup.coe_mul, map_mul] }, fun g => ⟨fun hg => ?_, fun hg => ?_⟩,
    fun g => (h1 g).symm⟩
  · have := cmp_KO h _ hg
    rwa [hc'] at this
  · exact cmp_KO h.symm _ (by rwa [hc'])
variable (V) in
private theorem pr_surj : Function.Surjective V.pr := by
  rintro ⟨x, hx⟩
  obtain ⟨g, rfl⟩ := QuotientGroup.mk'_surjective (NS Ω V.S') x
  obtain ⟨σ, rfl⟩ := (V.hη g).1 hx
  exact ⟨σ, rfl⟩
variable (V) in
private theorem dense : Dense {g : V.η.ker | ∃ w ∈ {w : Plc L | w.under (𝓞 (Lp L)) ∉ V.S' ∧ IsSplitAt w},
    ∃ (A : ValuationSubring Ω) (σ : G L Ω), IsPlaceOver A w ∧ IsFrob A (normV w) σ ∧ g = V.pr σ⁻¹} := by
  have hfin1 : {w : Plc L | w.asIdeal ∣ differentIdeal (𝓞 (Lp L)) (𝓞 L)}.Finite :=
    Ideal.finite_factors differentIdeal_ne_bot
  have hfin2 : ((fun w : Plc L => w.under (𝓞 (Lp L))) ⁻¹' V.S').Finite := by
    refine V.fin.preimage' fun v _ => ?_
    have := v.isMaximal
    refine ((IsDedekindDomain.primesOver_finite v.asIdeal (𝓞 L)).preimage
      (f := fun w : Plc L => w.asIdeal) (fun a _ b _ h => HeightOneSpectrum.ext h)).subset ?_
    rintro w rfl
    exact ⟨w.isPrime, ⟨rfl⟩⟩
  have hD := GlobalTheory.Published.ChebotarevDegreeOne.dense (F := L) (Ω := Ω) GlobalTheory.Published.chebotarevDegreeOne'
    (hfin1.union hfin2)
  have hs : Function.Surjective fun σ : G L Ω => V.pr σ⁻¹ := (pr_surj V).comp inv_surjective
  refine (hs.denseRange.dense_image ((V.pr_cont W.continuous_resP).comp continuous_inv) hD).mono ?_
  rintro _ ⟨σ, ⟨w, hw, hd, B, hB, hF⟩, rfl⟩
  have := w.isPrime
  exact ⟨w, ⟨fun h => hw (Or.inr h),
    UpperTheory.isSplitAt_of_unramified_of_inertiaDeg_eq_one L w (not_dvd_differentIdeal_iff.1 fun h => hw (Or.inl h)) hd⟩, B, σ, hB, hF, rfl⟩
end UpperTheory.V.Hi.AxU
open UpperTheory.V.Hi.AxU in
theorem UpperTheory.V.Hi.axU_s :
    _root_.GlobalTheory.Mem.LiteralAutomorphy.LiteratureRankNHypothesis → ∀ (l : ℕ) [Fact l.Prime] (L Ω : Type) [Field L] [NumberField L] [IsCMField L] [Field Ω] [Algebra L Ω] [IsAlgClosure L Ω] (s : HidaSetting l L Ω) (n : ℕ), 1 ≤ n →
    ∀ (V : s.Lev) (Q : QData V) (c : Coef l), ∀ (m : ℕ) (τ₀ : KT n (wt s) →* GL (Fin m) c.O), (hset Q τ₀).Ax := by
  intro H l _ L Ω _ _ _ _ _ _ s n hn V Q c m τ₀
  exact
    { odd := s.odd
      pos := hn
      Sl_over := fun v => by
        have h : ((l : ℕ) : 𝓞 (Lp L)) ∈ ((s.w v.1).under (𝓞 (Lp L))).asIdeal := by
          rw [under_w]
          exact v.2
        change algebraMap (𝓞 (Lp L)) (𝓞 L) _ ∈ (s.w v.1).asIdeal at h
        rwa [map_natCast] at h
      Sl_inj := fun v v' h => Subtype.ext (by
        rw [← under_w s v.1, ← under_w s v'.1]
        exact congrArg _ h)
      art_spec := fun v => Classical.epsilon_spec (_root_.UpperTheory.V.Z.Win.T2.laArtinLit' H (s.hw v.1))
      Q_away := fun q => away_l s (Q.notS q)
      Wp_away := fun w hw => away_l s fun h => hw.1 (V.sub h)
      fin := UpperTheory.V.Hi.finU l L Ω s n hn V Q c m τ₀
      τ_Q := fun q g => (congrArg τ₀ (toKT_sec s (Q.notS q) g)).trans (map_one τ₀)
      coefficientRep_trivial_on_unramified := fun w hw g => (congrArg τ₀ (toKT_sec s (fun h => hw.1 (V.sub h)) g)).trans (map_one τ₀)
      Q_UQ := fun q u hu g => comm s (((mem_UQ Q).1 hu).2 q) (sec_mem s _ g)
      Q_Q := fun q q' h => comm' s fun e => h (Q.inj e).symm
      sectionsCommuteAtSplit := fun q w hw => comm' s fun e => hw.1 (e ▸ wq_mem Q q)
      W_le := fun w hw => by
        rintro _ ⟨k, hk, rfl⟩
        exact sec_KO Q hn hw.1 hw.2 hk
      W_dec := fun w hw u hu => dec Q hn hw.1 hw.2 hu
      Wm_mul_Wm_comm := fun w hw w' hw' => by
        by_cases h : w'.under (𝓞 (Lp L)) = w.under (𝓞 (Lp L))
        · exact Or.inr (same s hn (fun h => hw.1 (V.sub h)) hw.2 hw'.2 h)
        · exact Or.inl (comm' s h)
      prj_cont := V.pr_cont W.continuous_resP
      dense := dense V }
end
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.LanglandsQuotient
section
noncomputable abbrev UpperTheory.Zero.LLC.IsRecT.langlandsQuotientDense := @UpperTheory.V.Z.Win.T2.lQuot_alt
end

