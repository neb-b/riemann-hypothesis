module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.WeilDeligneUnramified.UnitaryTwoForm
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.WeilDeligneUnramified.WeilCharpolySupport.Bundle0001
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.GeneralizedEigenspaces.WeightKernels.TwistRatios.Bundle0002
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.CuspidalDescent.SphericalTwists.UnramifiedTwists.Bundle0003
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1799
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.AutomorphyLifting.ExistsRec
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.TemperedLocalComponents.Bundle0005
public import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.Bundle0052
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.KatoQuadraticCharacters.NewformTwistNorms.PowEqOneOfKills
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0218
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.GeneralizedEigenspaces.WeightKernels.TwistRatios.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0868

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.WeilDeligneUnramified.WeilCharpolySupport.AboveWeight
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

theorem UpperTheory.V.Z.Sym.W.adjoint_lift_transfer_to_unitary_group_two : UpperTheory.V.Z.Sym.W.UnitaryTwoForm := by
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
  have hex : ∀ w : Plc L, ∃ τ, π.IsLocComp w τ := fun w => (Af.locCompC PA L 2 π w).1
  have hpt : ∀ (w : Plc L) τ, π.IsLocComp w τ → UpperTheory.V.Z.Sym.W.PT τ := fun w τ hτ => by
    obtain ⟨A, hA⟩ : ∃ A : ValuationSubring Ω, IsPlaceOver A w := exists_isPlaceOver Ω w
    obtain ⟨rc, hrc⟩ := exRec' PA.litN hA
    exact (hg w A hA rc hrc τ hτ).1
  have hb : ∀ φ : L →+* Qbar l, ∃ b : ℤ, HT φ = {b, b + m} := fun φ => by
    have hw : ((l : ℕ) : 𝓞 L) ∈ (GlobalTheory.EvExtend.placeOf φ).asIdeal := by
      rw [GlobalTheory.EvExtend.mem_placeOf]
      simpa using GlobalTheory.EvExtend.norm_natCast_lt_one (l := l)
    obtain ⟨A, hA⟩ : ∃ A : ValuationSubring Ω, IsPlaceOver A (GlobalTheory.EvExtend.placeOf φ) := exists_isPlaceOver Ω _
    have hAl : A.valuation (l : Ω) < 1 := by simpa only [map_natCast] using (hA _).2 hw
    obtain ⟨τ, hτ⟩ := hex (GlobalTheory.EvExtend.placeOf φ)
    obtain ⟨-, b, hb⟩ := UpperTheory.V.Z.Sym.W.aboveW PA L Ω l ι hl r hc m hr.gap _ hw HT ((hLG _ _ hτ).2 (hpt _ _ hτ)) A hA
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
    obtain ⟨rc, hrc⟩ := exRec' PA.litN hA
    have hl' := mt (hlm w) hw
    have hq := hg w A hA rc hrc τ hτ
    exact UpperTheory.V.Z.Desc.W.sphT PA.litN L Ω l ι 2 r hc w hl' A hA (hr.unr A fun h => hw ((hA _).1 (by simpa only [map_natCast] using h))) rc hrc τ hq.1
      ((((hLG w τ hτ).1 A hA rc hrc).1 hl').isWDOf hq.2)
  obtain ⟨σ, hσ, hunr, hsat⟩ := P.desc L hU.unr l Fact.out _ hfin (fun w hw => hU.split w ((hk M w).2 hw))
    (fun w hw => (hk M w).1 (hlm w hw)) 2 le_rfl (by norm_num) π hreg hrw hd
    fun w hw => by
      have hw' : (M : 𝓞 L) ∉ w.asIdeal := mt (hk M w).1 hw
      obtain ⟨⟨τ, hτ⟩, hi⟩ := Af.locCompC PA L 2 π w
      obtain ⟨b, hb⟩ := (Af.satLoc PA L 2 w τ).1 (hfix w hw' τ hτ)
      exact ⟨b, ((Af.satLoc PA L 2 w τ).2 _ π.finPart (hi τ hτ) b).2 hb⟩
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

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.WeilDeligneUnramified.WeilCharpolySupport.AbsPowIntVal
section
noncomputable section

open NumberField IsDedekindDomain ValuativeRel Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.N Polynomial
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.LocGL GlobalTheory.GalOfCusp GlobalTheory.UnitaryBC GlobalTheory.SmGL GlobalTheory.SplitWeil
open UpperTheory.V UpperTheory.V.Af UpperTheory.V.Sd UpperTheory.V.Z.Sym UpperTheory.V.Z.Sym.Dict
open UpperTheory.V.W (Plc Lp)
open scoped Matrix

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace UpperTheory.V.Z.Sym.W.GoodWeilCharpoly

private theorem one_of_sq {a b : ℂ} (h : (X - 1 : ℂ[X]) ^ 2 = (X - C a) * (X - C b)) : a = 1 ∧ b = 1 := by
  have ha := congrArg (eval a) h
  have hb := congrArg (eval b) h
  simp only [eval_pow, eval_sub, eval_X, eval_one, eval_mul, eval_C, sub_self, zero_mul, mul_zero] at ha hb
  exact ⟨sub_eq_zero.1 (pow_eq_zero_iff (two_ne_zero)|>.1 ha), sub_eq_zero.1 (pow_eq_zero_iff (two_ne_zero)|>.1 hb)⟩

section Loc

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

private theorem absPow_int_val (m : ℤ) (x : kˣ) : (absPow k (m : ℂ) x : ℂ) = (absPow k 1 x : ℂ) ^ m := by
  rw [val_absPow, val_absPow, Complex.cpow_intCast, Complex.cpow_one]

end Loc

end UpperTheory.V.Z.Sym.W.GoodWeilCharpoly

theorem UpperTheory.V.Z.Sym.W.goodW :
    UpperTheory.V.Z.Sym.W.GoodW := by
  intro P L Ω _ _ _ _ _ l _ ι r w hlw hunr ⟨s, ⟨A, hA, hF⟩, hs⟩ τ hτ hPT
  obtain ⟨rc, hrc⟩ := Z.Win.exRec' P.litN hA
  obtain ⟨a, ha, -⟩ := hrc
  obtain ⟨ψ, hψs, ⟨e⟩, -⟩ := psOf P.litN L 2 w τ hPT
  have hsub : IsSubquotient τ.ρ (prinSeries ψ) := by
    exact IsSubquotient.of_injective e.toIntertwiningMap e.toLinearEquiv.injective
  have hE := eigW P L Ω l ι 2 r w hlw A hA a ha τ hτ hPT ψ hψs hsub
  let x : Fin 2 → Weil hA → ℂˣ := fun i t => ψ i (a t) * absPow (w.adicCompletion L) (-((((2 : ℕ) : ℂ) - 1) / 2)) (a t)
  have hpol : ∀ t : Weil hA, (r (t : G L Ω)).val.charpoly.map ι.toRingHom = (X - C (x 0 t : ℂ)) * (X - C (x 1 t : ℂ)) := by
    intro t
    rw [hE t, psPol, Fin.prod_univ_two]
  have hUo : ∀ i, ∀ u ∈ Hi.Uo (Kw w), ψ i u = 1 := by
    intro i u hu
    obtain ⟨t, rfl⟩ := ha.surj u
    have hd : deg t = 0 := by
      have h0 := ha.ord_eq t
      rw [ord_eq_zero_iff.2 hu] at h0
      omega
    have hI : (t : G L Ω) ∈ Ine (F := L) A := deg_eq_zero_iff.1 hd
    have h1 := hpol t
    rw [hunr A hA _ hI] at h1
    have h2 : ((1 : GL (Fin 2) (Qbar l)).val.charpoly).map ι.toRingHom = (X - 1 : ℂ[X]) ^ 2 := by
      simp [Matrix.charpoly_one]
    rw [h2] at h1
    obtain ⟨h3, h4⟩ := GoodWeilCharpoly.one_of_sq h1
    have hv := isUnram_absPow (w.adicCompletion L) (-((((2 : ℕ) : ℂ) - 1) / 2)) (a t) hu
    have hx : ∀ j, x j t = ψ j (a t) := fun j => by
      show ψ j (a t) * _ = _
      rw [hv, mul_one]
    have e0 : ψ 0 (a t) = 1 := Units.ext (by rw [← hx 0]; exact h3)
    have e1 : ψ 1 (a t) = 1 := Units.ext (by rw [← hx 1]; exact h4)
    fin_cases i
    · exact e0
    · exact e1
  let s' : Weil hA := ⟨s, mem_Weil_of_isFrob hA hF⟩
  let al : (Qbar l)ˣ := Units.map ι.symm.toRingHom.toMonoidHom (x 0 s')
  let be : (Qbar l)ˣ := Units.map ι.symm.toRingHom.toMonoidHom (x 1 s')
  have hal : ι (al : Qbar l) = (x 0 s' : ℂ) := by simp [al]
  have hbe : ι (be : Qbar l) = (x 1 s' : ℂ) := by simp [be]
  have hc : (r s).val.charpoly = (X - C (al : Qbar l)) * (X - C (be : Qbar l)) := by
    apply Polynomial.map_injective ι.toRingHom ι.injective
    have h1 := hpol s'
    rw [show ((s' : G L Ω)) = s from rfl] at h1
    rw [h1, Polynomial.map_mul, Polynomial.map_sub, Polynomial.map_sub, Polynomial.map_X, Polynomial.map_C,
      Polynomial.map_C]
    simp [hal, hbe]
  have H : ∀ m : ℤ, |m| ≤ 2 → (ψ 0 / ψ 1) ^ 2 ≠ absPow (Kw w) (m : ℂ) := by
    intro m hm he
    apply hs
    refine ⟨m, hm, ?_⟩
    have h1 := congrArg (fun f : (Kw w)ˣ →* ℂˣ => ((f (a s') : ℂˣ) : ℂ)) he
    have h2 := (Ga.epsAway P L Ω l ι w hlw A hA a ha s').1
    have hq : (x 0 s' : ℂ) / (x 1 s' : ℂ) = (ψ 0 (a s') : ℂ) / (ψ 1 (a s') : ℂ) := by
      simp only [x, Units.val_mul]
      exact mul_div_mul_right _ _ (Units.ne_zero _)
    simp only [MonoidHom.pow_apply, MonoidHom.div_apply, Units.val_pow_eq_pow_val, Units.val_div_eq_div_val,
      GoodWeilCharpoly.absPow_int_val, ← h2, ← hq, ← hal, ← hbe] at h1
    have h3 : ((al : Qbar l) / be) ^ 2 = Ga.ep l s ^ m := by
      apply ι.injective
      simpa [map_zpow₀] using h1
    have h4 := (Ga.ufFacts (Qbar l) (r s)).1 al be hc
    have hne : ((al : Qbar l) / be) ≠ 0 := div_ne_zero al.ne_zero be.ne_zero
    have h5 : ((al : Qbar l) / be)⁻¹ ^ 2 = Ga.ep l s ^ (-m) := by rw [inv_pow, h3, zpow_neg]
    rw [h4]
    simp only [Units.val_inv_eq_inv_val, Units.val_div_eq_div_val]
    rw [← h3, ← h5]
    field_simp
    ring
  exact ⟨ψ, hψs, ⟨e⟩, hUo, ⟨fun y hy => by simp [MonoidHom.div_apply, hUo 0 y hy, hUo 1 y hy], H⟩⟩
end
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.WeilDeligneUnramified.WeilCharpolySupport.PlainAtW
section
open NumberField IsDedekindDomain ValuativeRel Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.LocGL GlobalTheory.GalOfCusp GlobalTheory.UnitaryBC GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.PRep
open UpperTheory.V UpperTheory.V.Af UpperTheory.V.Sd UpperTheory.V.Z.Sym UpperTheory.V.Z.Sym.Dict
open UpperTheory.V.W (Plc Lp)

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace UpperTheory.V.Z.Sym.W

private theorem ratios {G : Type*} [CommGroup G] (a p : G) (h1 : p ≠ 1) (h2 : a ≠ p) (h3 : a ≠ p⁻¹)
    (h4 : a ^ 2 ≠ p) (h5 : a ^ 2 ≠ p⁻¹) (i j : Fin 3) :
    (![a, 1, a⁻¹] : Fin 3 → G) i ≠ (![a, 1, a⁻¹] : Fin 3 → G) j * p := by
  intro e
  fin_cases i <;> fin_cases j <;> simp at e
  · exact h1 e
  · exact h2 e
  · exact h4 (by rw [pow_two]; nth_rewrite 1 [e]; simp)
  · exact h3 (eq_inv_of_mul_eq_one_left e.symm)
  · exact h1 e.symm
  · exact h2 (inv_mul_eq_one.mp e.symm)
  · have e' : a ^ 2 * p = 1 := by rw [pow_two, mul_assoc, ← e]; simp
    exact h5 (eq_inv_of_mul_eq_one_left e')
  · exact h3 (by simpa using congrArg (·⁻¹) e)
  · exact h1 e

private theorem absOne_ne (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] :
    absPow k 1 ≠ 1 := by
  intro h
  have e : absPow k ((1 : ℝ) : ℂ) = absPow k ((0 : ℝ) : ℂ) := by
    simpa [absPow_zero] using h
  obtain ⟨ϖ, hϖ⟩ := GlobalTheory.LocGL.exists_uniformizer k
  have h1 : nabs k ϖ ≠ 1 := fun e => ValuativeRel.uniformizer_lt_one.ne (hϖ ▸ (nabs_eq_one_iff ϖ).1 e)
  have h2 : nabs k ϖ ^ (1 : ℝ) = nabs k ϖ ^ (0 : ℝ) := by
    have hx := GlobalTheory.SmGL.val_absPow_ofReal k 1 ϖ
    have hy := GlobalTheory.SmGL.val_absPow_ofReal k 0 ϖ
    rw [e] at hx
    exact_mod_cast hx.symm.trans hy
  have h3 := congrArg Real.log h2
  rw [Real.log_rpow (nabs_pos' k ϖ), Real.log_rpow (nabs_pos' k ϖ)] at h3
  have : (1 : ℝ) = 0 := mul_right_cancel₀ (Real.log_ne_zero_of_pos_of_ne_one (nabs_pos' k ϖ) h1) h3
  exact one_ne_zero this

end UpperTheory.V.Z.Sym.W

theorem UpperTheory.V.Z.Sym.W.plainAtW :
    UpperTheory.V.Z.Sym.W.PlainAtW := by
  intro hL L _ _ _ σ π hσ hl w hw a ha ⟨hs, τ₀, h₀, hq⟩ τ hτ
  have hc := hl.comp w hw τ hτ
  obtain ⟨e⟩ := UpperTheory.building_component_uniqueness L 3 σ hσ w hw _ _ _ _ h₀ hc
  have hq' : IsSubquotient τ.ρ (prinSeries ![a, 1, a⁻¹]) :=
    (IsSubquotient.of_surjective e.toIntertwiningMap e.surjective).trans hq
  have hp := absOne_ne (Kw w)
  have n1 := ha 1 (Or.inl rfl) 1 (Or.inl rfl)
  have n2 := ha 1 (Or.inl rfl) (-1) (Or.inr rfl)
  have n3 := ha 2 (Or.inr rfl) 1 (Or.inl rfl)
  have n4 := ha 2 (Or.inr rfl) (-1) (Or.inr rfl)
  simp only [pow_one, Int.cast_one, Int.cast_neg, absPow_neg] at n1 n2 n3 n4
  exact UpperTheory.V.Z.Sym.W.plainOf hL L 3 w τ _ hs hq' (ratios a _ hp n1 n2 n3 n4)
end

