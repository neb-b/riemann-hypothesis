module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.WeilDeligneUnramified.UnitaryTwoForm
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.WeilDeligneUnramified.WeilCharpolySupport.ExistsInjectiveSection
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.GeneralizedEigenspaces.WeightKernels.TwistRatios.Bundle0002
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.CuspidalDescent.SphericalTwists.UnramifiedTwists.Bundle0001
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.AutomorphyLifting.UnitaryGaloisFamilies.Bundle0002
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.AutomorphyLifting.ExistsRec
public import Development.AutomorphicArithmetic.AutomorphicVarieties.HeckeAlgebras.OrdinaryHeckeCharacters.Bundle0005
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.Bundle0044
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.Bundle0042
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.Bundle0009
public import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.Bundle0042
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0679
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0199
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.WdParameterMonodromyZeroIffPotentiallyCrystallin
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0016
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1799
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0383
public import Development.AutomorphicArithmetic.AutomorphicVarieties.HeckeAlgebras.Distinct
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0046
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0660
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0732
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HasSupportOfIsSubquotientProdIrr
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0666
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0840
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0241
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0242
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.GeneralizedEigenspaces.SmoothDepth.OpenLevelSubgroups.Bundle0001
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.LeviSmoothLocalization.Bridge
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.LeviSmoothLocalization.PrincipalSeriesMatching.Bundle0002
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.LeviSmoothLocalization.PrincipalSeriesMatching.NormAbsPowUnif
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.LeviSmoothLocalization.PrincipalSeriesMatching.Bundle0003
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.StrongMultiplicityOne.Strong
public import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.Bundle0055
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0299
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.LeviSmoothLocalization.PrincipalSeriesMatching.UnlFull

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.WeilDeligneUnramified.WeilCharpolySupport.AboveW
section
noncomputable section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions ValuativeRel IsLocalRing GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.LocGL GlobalTheory.GalOfCusp GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.UnitaryBC UpperTheory.V UpperTheory.V.Hi
open UpperTheory.V.W (Plc Lp)
open scoped Polynomial
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option synthInstance.maxHeartbeats 200000
open UpperTheory.GalN.V UpperTheory.V.Z.Win UpperTheory.Zero.LLC

open UpperTheory.V.Z.Sym.AboveWeight

section

section

variable {L Ω : Type} [Field L] [NumberField L] [Field Ω] [Algebra L Ω] [IsAlgClosure L Ω] {l : ℕ} [Fact l.Prime]
  {w : Plc L} {A : ValuationSubring Ω} {h : IsPlaceOver A w} {a : Weil h →* (w.adicCompletion L)ˣ}

private theorem noLk_of {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (u : kˣ →* ℂˣ) (H : ∀ i j : Fin 3, i ≠ j → (![u, 1, u⁻¹] : Fin 3 → kˣ →* ℂˣ) i ≠ (![u, 1, u⁻¹] : Fin 3 → kˣ →* ℂˣ) j ∧
      (![u, 1, u⁻¹] : Fin 3 → kˣ →* ℂˣ) i ≠ (![u, 1, u⁻¹] : Fin 3 → kˣ →* ℂˣ) j * absPow k 1) :
    UpperTheory.V.Z.Sym.W.NoLk u := by
  intro j hj e he hE
  have e1 : absPow k (((1 : ℤ) : ℂ)) = absPow k 1 := by simp
  have e2 : absPow k (((-1 : ℤ) : ℂ)) = (absPow k 1)⁻¹ := by
    rw [show (((-1 : ℤ) : ℂ)) = -1 by simp, absPow_neg]
  rcases hj with rfl | rfl <;> rcases he with rfl | rfl
  · rw [pow_one, e1] at hE
    exact (H 0 1 (by decide)).2 (by simpa using hE)
  · rw [pow_one, e2] at hE
    exact (H 1 0 (by decide)).2 (by simp [hE])
  · rw [e1] at hE
    refine (H 0 2 (by decide)).2 ?_
    simp [← hE, pow_two]
  · rw [e2] at hE
    refine (H 2 0 (by decide)).2 ?_
    have hp : absPow k 1 = (u ^ 2)⁻¹ := by rw [hE, inv_inv]
    simp [hp, pow_two]

private theorem noLk_above (H : GlobalTheory.Published.GlobalArtinReciprocity) (ι : Qbar l ≃+* ℂ) (hw : ((l : ℕ) : 𝓞 L) ∈ w.asIdeal)
    (ha : IsLocalArtin h a) (hv : A.valuation (l : Ω) < 1) {m : ℕ} (hm : 2 ≤ m) {b : ℤ} {k : ℕ} (hk : 0 < k)
    {ω₀ ω₁ : (w.adicCompletion L)ˣ →* ℂˣ} {κ₀ κ₁ : Dec (F := L) A →* (Qbar l)ˣ}
    (h₀ : OrdChar ι a ω₀ (fun _ => -(b + m)) κ₀) (h₁ : OrdChar ι a ω₁ (fun _ => -b) κ₁)
    (hκ : ∀ s : ↥(Dec (F := L) A), (s : G L Ω) ∈ Ine (F := L) A →
      κ₀ s ^ k = (cycBar L Ω l s ^ (b + m)) ^ k ∧ κ₁ s ^ k = (cycBar L Ω l s ^ b) ^ k) :
    UpperTheory.V.Z.Sym.W.NoLk (ω₀ / ω₁) := by
  let u := ω₀ / ω₁
  let c : Fin 3 → ℤ := ![m, 0, -m]
  let ψ : Fin 3 → Dec (F := L) A →* (Qbar l)ˣ := ![κ₀ / κ₁, 1, κ₁ / κ₀]
  let hh : Fin 3 → (L →+* Qbar l) → ℤ := fun i _ => (![-(m : ℤ), 0, (m : ℤ)] : Fin 3 → ℤ) i
  have hq : ∀ {p q y : (Qbar l)ˣ} {e f : ℤ}, p ^ k = (y ^ e) ^ k → q ^ k = (y ^ f) ^ k →
      (p / q) ^ k = (y ^ (e - f)) ^ k := fun h1 h2 => by
    rw [div_pow, h1, h2, ← div_pow, zpow_sub, div_eq_mul_inv]
  have hp : ∀ (i : Fin 3) (s : ↥(Dec (F := L) A)), (s : G L Ω) ∈ Ine (F := L) A →
      ψ i s ^ k = (cycBar L Ω l s ^ c i) ^ k := fun i s hs => by
    obtain ⟨h1, h2⟩ := hκ s hs
    fin_cases i
    · have := hq h1 h2
      simpa [ψ, c] using this
    · simp [ψ, c]
    · have := hq h2 h1
      simpa [ψ, c] using this
  have hne : ∀ i j, ψ i ≠ ψ j * (cycBar L Ω l).comp (Dec (F := L) A).subtype := fun i j => by
    refine not_link hv hk (hp i) (hp j) ?_
    fin_cases i <;> fin_cases j <;> simp [c] <;> omega
  have H0 : OrdChar ι a u (fun _ => -(m : ℤ)) (κ₀ / κ₁) := by
    have := ord_div h₀ h₁
    have e : ((fun _ => -(b + m)) - fun _ => -b : (L →+* Qbar l) → ℤ) = fun _ => -(m : ℤ) := by
      funext t
      simp
    rwa [e] at this
  have H1 : OrdChar ι a (1 : (w.adicCompletion L)ˣ →* ℂˣ) (fun _ => 0) (1 : Dec (F := L) A →* (Qbar l)ˣ) := by
    have := ord_div h₀ h₀
    rw [div_self', div_self', sub_self] at this
    exact this
  have H2 : OrdChar ι a u⁻¹ (fun _ => (m : ℤ)) (κ₁ / κ₀) := by
    have := ord_div h₁ h₀
    have e : ((fun _ => -b) - fun _ => -(b + m) : (L →+* Qbar l) → ℤ) = fun _ => (m : ℤ) := by
      funext t
      simp
    rw [e] at this
    rwa [show u⁻¹ = ω₁ / ω₀ from inv_div _ _]
  have hO : ∀ i, OrdChar ι a ((![u, 1, u⁻¹] : Fin 3 → (w.adicCompletion L)ˣ →* ℂˣ) i) (hh i) (ψ i) := fun i => by
    fin_cases i
    · exact H0
    · exact H1
    · exact H2
  have hmono : ∀ t : L →+* Qbar l, StrictMono fun j : Fin 3 => hh j t := fun t => by
    refine Fin.strictMono_iff_lt_succ.2 fun i => ?_
    fin_cases i <;> simp [hh] <;> omega
  exact noLk_of u (not_linked H ι hw ha hmono hO hne)

private theorem above' (P : Af.Hypotheses₂) (hl : l ≠ 2) {n : ℕ} {ι : Qbar l ≃+* ℂ} {ρ : G L Ω →* GL (Fin n) (Qbar l)}
    {HT : (L →+* Qbar l) → Multiset ℤ} (hρ : Continuous ρ) (HG : HasHTAt ρ HT w) (h : IsPlaceOver A w)
    (hw : ((l : ℕ) : 𝓞 L) ∈ w.asIdeal) {τ : SmIrr (GL (Fin n) (w.adicCompletion L))} (H : LocGlobT ι ρ w τ)
    {rc : IrrGL (k := w.adicCompletion L) → WD h} (hrc : IsRecT h rc)
    (hp : GlobalTheory.RoadU.PlainTor (IrrGL.of τ.ρ τ.smooth τ.irred)) (hg : Gd (rc (algNorm τ)))
    {hh : Fin n → (L →+* Qbar l) → ℤ} (hm : ∀ t, StrictMono fun j => hh j t) {ψ : Fin n → Dec (F := L) A →* (Qbar l)ˣ}
    (hψ : ∀ i, W.IsLocAlg h (ψ i) fun t => hh i (t.1.comp (algebraMap L _)))
    (hf : W.HasFlag (ρ.comp (Dec (F := L) A).subtype) ψ)
    (hne : ∀ i j, ψ i ≠ ψ j * (cycBar L Ω l).comp (Dec (F := L) A).subtype) :
    ∃ (a : Weil h →* (w.adicCompletion L)ˣ), IsLocalArtin h a ∧
    (∃ ω : Fin n → (w.adicCompletion L)ˣ →* ℂˣ, Nonempty (τ.ρ.Equiv (PS ω)) ∧ ∀ i, OrdChar ι a (ω i) (hh i) (ψ i)) ∧
    ∀ j : W.Emb l w, HT (j.1.comp (algebraMap L _)) = Finset.univ.val.map fun i => hh i (j.1.comp (algebraMap L _)) := by
  obtain ⟨a, ha⟩ : ∃ a, IsLocalArtin h a := by
    obtain ⟨a, ha, -⟩ := hrc
    exact ⟨a, ha⟩
  have hc : Continuous (ρ.comp (Dec (F := L) A).subtype) := hρ.comp continuous_subtype_val
  choose ω hω using fun i => (Loc.ordCharIff P.litN.aut.art h ι _ ha (hh i) (ψ i)).1.2 ⟨flag_cont' hc hf i, hψ i⟩
  have hD : DRat ι h (ρ.comp (Dec (F := L) A).subtype) HT fun s => (rc (algNorm τ)).charPol s := fun O _ _ _ Bw hj =>
    have h1 := HG A h O Bw hj
    ⟨h1.1, h1.2, fun s => by rw [((H A h rc hrc).2 O Bw hj hg).2]⟩
  have hD' := Loc.flagWD P.litN L Ω l hl ι n w hw A h _ ha _ hc _ ω ψ hω hf _ _ hD
  refine ⟨a, ha, ⟨ω, ?_, hω⟩, jumps_eq h hw hD hD'⟩
  have hs : IsSubquotient τ.ρ (PS ω) := by
    obtain ⟨O, _, _, _, Bw, hj⟩ := Af.exists_bridge (l := l) h hw
    exact UpperTheory.V.Z.Desc.W.psT P.litN L Ω n w A h _ ha rc hrc τ hp ω (fun i => (hω i).smooth) fun s =>
      ((hD O Bw hj).2.2 s).symm.trans ((hD' O Bw hj).2.2 s)
  exact (psIrr P.litN _ n ω (fun i => (hω i).smooth)
    (not_linked P.litN.aut.art ι hw ha (fun t i j hij => hm t hij) hω hne)).2 _ τ.ρ τ.irred hs

end

end

theorem UpperTheory.V.Z.Sym.W.aboveW : UpperTheory.V.Z.Sym.W.AboveW := by
  intro P L Ω _ _ _ _ _ l _ ι hl r hr m hm w hw HT hHT A h ⟨b, k, κ, hk, hf, hκ⟩ τ H hPT
  have hv : A.valuation (l : Ω) < 1 := by
    have := (h ((l : ℕ) : 𝓞 L)).2 hw
    simpa only [map_natCast] using this
  let c : Fin 2 → ℤ := ![b + m, b]
  have hκ' : ∀ (i : Fin 2) (s : ↥(Dec (F := L) A)), (s : G L Ω) ∈ Ine (F := L) A → κ i s ^ k = (cycBar L Ω l s ^ c i) ^ k := by
    intro i s hs
    fin_cases i
    · exact (hκ s hs).1
    · exact (hκ s hs).2
  have hcont : Continuous (r.comp (Dec (F := L) A).subtype) := hr.comp continuous_subtype_val
  have hfc : ∀ i, Continuous (κ i) := flag_cont' hcont hf
  have hmono : ∀ t : L →+* Qbar l, StrictMono fun j : Fin 2 => (fun (i : Fin 2) (_ : L →+* Qbar l) => -c i) j t := by
    intro t
    refine Fin.strictMono_iff_lt_succ.2 fun i => ?_
    fin_cases i
    simp [c]
    omega
  have hne : ∀ i j, κ i ≠ κ j * (cycBar L Ω l).comp (Dec (F := L) A).subtype := by
    intro i j
    refine not_link hv hk (hκ' i) (hκ' j) ?_
    fin_cases i <;> fin_cases j <;> simp [c] <;> omega
  obtain ⟨rc, hrc⟩ := UpperTheory.V.Z.Win.exRec' P.litN h
  have hg : Gd (rc (algNorm τ)) := UpperTheory.V.Z.Win.Gu.plainGd L Ω A w h rc hrc 2 τ hPT
  obtain ⟨a, ha, ⟨ω, he, hO⟩, hj⟩ := above' P hl hr hHT h hw H hrc hPT hg hmono
    (fun i => locAlg P.litN.aut.art h hw (κ i) (hfc i) hk (c i) (hκ' i)) hf hne
  refine ⟨⟨_, fun i => (hO i).smooth.mul (isSmoothChar_of_isUnram (isUnram_absPow _ _)), he, ?_⟩, -(b + m), fun j => ?_⟩
  · have := noLk_above P.litN.aut.art ι hw ha hv hm hk (hO 0) (hO 1) hκ
    simpa [mul_div_mul_right_eq_div] using this
  · rw [hj j]
    simp [c]
    rfl

end
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.WeilDeligneUnramified.WeilCharpolySupport.CharPolSupp
section
noncomputable section

open NumberField IsDedekindDomain ValuativeRel Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.N Polynomial
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.LocGL GlobalTheory.GalOfCusp GlobalTheory.UnitaryBC GlobalTheory.SmGL GlobalTheory.SplitWeil
open UpperTheory.V UpperTheory.V.Hi UpperTheory.V.Af UpperTheory.V.Sd UpperTheory.V.Z.Sym UpperTheory.V.Z.Sym.Dict
open UpperTheory.V.W (Plc Lp)
open scoped Matrix

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

section

variable {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
  {A : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 E)} {h : IsPlaceOver A w}
  {a : Weil h →* (w.adicCompletion E)ˣ} {ha : IsLocalArtin h a} {rc : IrrGL (k := w.adicCompletion E) → WD h}

private theorem charPol_supp (hZ : GlobalTheory.Published.ZelevinskyPolynomialRing) (H : UpperTheory.Zero.LLC.LawsT a ha rc)
    (x : IrrGL (k := w.adicCompletion E)) (s : Multiset (IrrGL (k := w.adicCompletion E))) (hs : HasSupport x.rep s) (g : Weil h) :
    (rc x).charPol g = (s.map fun y => (rc y).charPol g).prod := by
  haveI : CharZero (w.adicCompletion E) := charZero_of_injective_algebraMap (algebraMap E _).injective
  obtain ⟨𝔪, hm⟩ := GlobalTheory.langlandsExhaustionGL_holds (w.adicCompletion E) x
  have hs' : HasSupport x.rep (msupp 𝔪) := GlobalTheory.LocGL.hasSupport_msupp_of_isL hZ _ 𝔪 x hm
  have he : s = msupp 𝔪 :=
    GlobalTheory.LocGL.SupportUnique.hasSupport_unique GlobalTheory.RecT.geometricLemma_holds GlobalTheory.bernsteinZelevinskyFiniteness_holds
      hZ _ x _ _ hs hs'
  rw [he, H.langlands 𝔪.toList x (by rw [Multiset.coe_toList]; exact hm), segSum, CuspExt.charPol_sumList, List.map_map,
    msupp, Multiset.map_bind, Multiset.prod_bind]
  have hl : ∀ (l : List (Segment (w.adicCompletion E))) (F : Segment (w.adicCompletion E) → ℂ[X]),
      (l.map F).prod = ((l : Multiset _).map F).prod := fun l F => by rw [Multiset.map_coe, Multiset.prod_coe]
  rw [hl, Multiset.coe_toList]
  exact congrArg Multiset.prod (Multiset.map_congr rfl fun Δ _ => GlobalTheory.RoadU.CharSupport.charPol_seg H Δ g)

private theorem charPol_ofChar (H : UpperTheory.Zero.LLC.LawsT a ha rc) (χ : (w.adicCompletion E)ˣ →* ℂˣ) (hχ : IsSmoothChar χ)
    (g : Weil h) : (rc (IrrGL.ofChar χ hχ)).charPol g = X - C (χ (a g) : ℂ) := by
  rw [H.one, WD.lpOfChar, WD.charPol_mk, WDRep.ofChars_ρ, charpoly_diagEnd]
  simp

end

theorem UpperTheory.V.Z.Sym.W.eigW :
    UpperTheory.V.Z.Sym.W.EigW := by
  intro P L Ω _ _ _ _ _ l _ ι n r w hl A h a ha τ hτ hP ψ hψ hsub s
  have Q := P.litN
  obtain ⟨rc, hrc⟩ := UpperTheory.Zero.LLC.recTExists L Ω A w h
  have hg : UpperTheory.V.Z.Win.Gd (rc (algNorm τ)) := UpperTheory.V.Z.Win.Gu.plainGd L Ω A w h rc hrc n τ hP
  have hx := ((hτ A h rc hrc).1 hl).isWDOf hg
  have hw := hx.wdOf_eq hl
  obtain ⟨t, ht, φ, hφ, N, b, hN, -⟩ := hx
  have hpol : (rc (algNorm τ)).charPol s =
      (r (s : G L Ω)).val.charpoly.map ι.toRingHom := by
    rw [← hw]; exact hN.charPol_wdOf hl ht ι s
  obtain ⟨a', ha', H⟩ := hrc
  obtain rfl : a' = a := by
    obtain ⟨art, hart⟩ := Q.aut.art L Ω
    have hinj := GlobalTheory.ArtinLocalInj.artin_localIdele_injective Q.loc.chev L Ω art hart w
    exact MonoidHom.ext fun σ => hinj ((ha'.glob art hart _).trans (ha.glob art hart _).symm)
  haveI : CharZero (w.adicCompletion L) := algebraRat.charZero _
  let τ' : IrrRep (GL (Fin n) (w.adicCompletion L)) := ⟨_, τ.ρ, τ.smooth, τ.irred⟩
  have h1 := (hasSupport_of_isSubquotient_prinSeries _ n _ hψ τ' hsub).of_equiv (IrrGL.equivOf τ.ρ τ.smooth τ.irred)
  have h2 := SupportRing.hasSupport_nu h1 (((1 - (n : ℝ)) / 2 : ℝ) : ℂ)
  have hc := charPol_supp Q.loc.zel H (algNorm τ) _ h2 s
  have e0 : (((1 - (n : ℝ)) / 2 : ℝ) : ℂ) = -(((n : ℂ) - 1) / 2) := by push_cast; ring
  rw [← hpol, hc, UpperTheory.V.Z.Sym.W.psPol, Finset.prod_eq_multiset_prod]
  simp only [Multiset.map_map, Function.comp_def]
  refine congrArg Multiset.prod (Multiset.map_congr rfl fun i _ => ?_)
  have e1 : (IrrGL.ofChar (ψ i) (hψ i)).nu (((1 - (n : ℝ)) / 2 : ℝ) : ℂ) =
      IrrGL.ofChar (ψ i * absPow (w.adicCompletion L) (((1 - (n : ℝ)) / 2 : ℝ) : ℂ))
        ((hψ i).mul (isSmoothChar_absPow _)) := IrrGL.tw_ofChar _ _ _ _
  rw [e1, charPol_ofChar H]
  simp only [e0, MonoidHom.mul_apply]
end
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.WeilDeligneUnramified.WeilCharpolySupport.GalExW
section
theorem UpperTheory.V.Z.Sym.W.galExW :
    UpperTheory.V.Z.Sym.W.GalExW := by
  intro P L Ω _ _ _ _ _ _ l _ ι hl hE n hn σ hσ
  obtain ⟨r, HT, hc, hs, -, -, hLG, hp, hi⟩ := P.gal L Ω hE l hl ι n hn σ hσ
  refine ⟨r, ⟨hc, UpperTheory.V.Z.Sym.Al.compEx P.af.litN L hE n hn σ hσ,
    fun w hw τ hτ => (hLG w hw τ hτ).1, hp⟩, fun h => ?_⟩
  obtain ⟨π, h1, h2, h3, -, h4, h5⟩ := hi h
  exact ⟨π, h1, h2, h3, h4, h5⟩
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.WeilDeligneUnramified.WeilCharpolySupport.GlueW
section
theorem UpperTheory.V.Z.Sym.W.glueW :
    UpperTheory.V.Z.Sym.W.GlueW := by
  intro L Ω _ _ _ _ _ _ l _ ι R h π _ hπ
  obtain ⟨t, ht⟩ := UpperTheory.V.Z.ImaginaryQuadraticEtaCharacter.winOfP_of UpperTheory.V.Z.ImaginaryQuadraticEtaCharacter.plainIff UpperTheory.V.Z.ImaginaryQuadraticEtaCharacter.winOf UpperTheory.V.Z.ImaginaryQuadraticEtaCharacter.sphUnl
    L 3 (by norm_num) π
  refine ⟨t, fun w => ?_⟩
  obtain ⟨π', hπ', hc⟩ := h w
  have e : π' = π := by
    refine GlobalTheory.CuspRep.CuspSub.ext (UpperTheory.V.Af.strongMultOneC L 3 π' π ?_)
    filter_upwards [hπ'.2, hπ.2] with v h1 h2
    obtain ⟨B, hB, hE⟩ := h1
    obtain ⟨B', hB', hE'⟩ := h2
    have e : B = B' := (UpperTheory.hecke_eigenvalue_basic_properties L Ω l ι v).2.2 3 R B B' hE hE'
    exact ⟨B, (GlobalTheory.CuspRep.CG.hasSat_mk π' v B).1 hB, (GlobalTheory.CuspRep.CG.hasSat_mk π v B).1 (e ▸ hB')⟩
  subst e
  rcases hc with ⟨B, hB⟩ | hp
  · exact (ht w).2 B hB
  · exact (ht w).1 hp
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.WeilDeligneUnramified.WeilCharpolySupport.PlainOf
section
open NumberField IsDedekindDomain GlobalTheory.CuspRep GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

theorem UpperTheory.V.Z.Sym.W.plainOf :
    UpperTheory.V.Z.Sym.W.PlainOf := by
  intro _ L _ _ n w τ ψ hψ hs hl
  refine ⟨GlobalTheory.RoadU.chars ψ hψ, ?_, ?_, ?_⟩
  · exact (GlobalTheory.IwahoriSupport.hasSupport_chars τ.irred ψ hψ hs).of_equiv (IrrGL.equivOf τ.ρ τ.smooth τ.irred)
  · intro y hy
    obtain ⟨i, -, rfl⟩ := Multiset.mem_map.1 hy
    rfl
  · intro y hy z hz h
    obtain ⟨i, -, rfl⟩ := Multiset.mem_map.1 hy
    obtain ⟨j, -, rfl⟩ := Multiset.mem_map.1 hz
    rw [IrrGL.nu, IrrGL.tw_ofChar, IrrGL.ofChar_inj] at h
    exact hl i j h
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.WeilDeligneUnramified.WeilCharpolySupport.PrinSeriesIrreducible
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
  letI hInd : Nontrivial (IndSp e₀ (piTensor fun i => detRep (Fin 1) (ω i))) :=
    nontrivial_of_irreducible hM
  have nontrivial_sub {G V W : Type} [Group G] [AddCommGroup V] [Module ℂ V]
      [AddCommGroup W] [Module ℂ W] {σ : Representation ℂ G W} {ρ : Representation ℂ G V}
      (h : IsSubquotient σ ρ) [Nontrivial W] : Nontrivial V := by
    obtain ⟨S, f, hf⟩ := h
    have := hf.nontrivial
    exact Subtype.val_injective.nontrivial (α := S.toSubmodule)
  haveI := @nontrivial_sub _ _ _ _ _ _ _ _ _ _
    (GlobalTheory.PermPrin.isSubquotient_multiProd_prinSeries e₀ ω) hInd
  have equiv_sub {G V W : Type} [Group G] [AddCommGroup V] [Module ℂ V]
      [AddCommGroup W] [Module ℂ W] {σ : Representation ℂ G W} {ρ : Representation ℂ G V}
      (h : IsSubquotient σ ρ) [Nontrivial W] (hρ : ρ.IsIrreducible) : Nonempty (ρ.Equiv σ) := by
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
  obtain ⟨E⟩ := equiv_sub (GlobalTheory.PrinProd.isSubquotient_prinSeries_multiProd k n ω) hM
  exact GlobalTheory.Parabolic.isIrreducible_of_equiv E hM

end Loc

theorem psOf : PsOf := by
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

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.WeilDeligneUnramified.WeilCharpolySupport.SelectW
section
noncomputable section

open NumberField IsDedekindDomain ValuativeRel Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.N Polynomial
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.LocGL GlobalTheory.GalOfCusp GlobalTheory.UnitaryBC GlobalTheory.SmGL GlobalTheory.SplitWeil
open UpperTheory.V UpperTheory.V.Af UpperTheory.V.Sd UpperTheory.V.Z.Sym UpperTheory.V.Z.Sym.Dict
open UpperTheory.V.W (Plc Lp)
open scoped Matrix

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

private theorem selectThrough {α β : Type} (f : α → β) (S : Set α) (a : α) (ha : a ∈ S) :
    ∃ P ⊆ S, a ∈ P ∧ Set.InjOn f P ∧ ∀ w ∈ S, ∃ w' ∈ P, f w' = f w := by
  classical
  haveI : Nonempty α := ⟨a⟩
  let g : β → α := fun b => if b = f a then a else Function.invFunOn f S b
  have hg : ∀ b ∈ f '' S, g b ∈ S ∧ f (g b) = b := by
    intro b hb
    by_cases h : b = f a
    · simp only [g, if_pos h]
      exact ⟨ha, h.symm⟩
    · simp only [g, if_neg h]
      exact ⟨Function.invFunOn_mem hb, Function.invFunOn_eq hb⟩
  refine ⟨g '' (f '' S), ?_, ?_, ?_, ?_⟩
  · rintro _ ⟨b, hb, rfl⟩
    exact (hg b hb).1
  · exact ⟨f a, ⟨a, ha, rfl⟩, by simp [g]⟩
  · rintro _ ⟨b, hb, rfl⟩ _ ⟨c, hc, rfl⟩ h
    rw [(hg b hb).2, (hg c hc).2] at h
    rw [h]
  · intro w hw
    exact ⟨g (f w), ⟨f w, ⟨w, hw, rfl⟩, rfl⟩, (hg _ ⟨w, hw, rfl⟩).2⟩

theorem UpperTheory.V.Z.Sym.W.selectW :
    UpperTheory.V.Z.Sym.W.SelectW := by
  intro L _ _ _ X w₀ hw₀
  exact selectThrough _ X w₀ hw₀
end
end

