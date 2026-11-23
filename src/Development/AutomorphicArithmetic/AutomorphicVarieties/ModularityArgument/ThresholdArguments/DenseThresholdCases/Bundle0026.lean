module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.DiscreteSeriesCoefficientsCuspidal
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.CuspidalDescent.SphericalTwists.UnramifiedTwists.Bundle0001
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.Bundle0021
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.Bundle0003
public import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.SymmetricAdjointFrobenius.Bundle0002
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.Bundle0009
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.TCentChar
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.BaseChangeUnits.CentralResidueGroups.Bundle0002
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.Bundle0014
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.BaseChangeUnits.CentralResidueGroups.GapTwo
public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.CrystallineBaseChange.Bundle0011
public import Development.AutomorphicArithmetic.AutomorphicVarieties.TheoremsMuLinked.GaloisRepresentationTypes.Bundle0003
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.Bundle0006
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.LinkedRig
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.Bundle0020
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.Bundle0017
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.TRigPtOf

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.PseudoLocalLanglandsDescent
section
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 200000

section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Polynomial ValuativeRel GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.LocGL GlobalTheory.GalOfCusp GlobalTheory.SmGL GlobalTheory.SplitWeil UpperTheory.V.Hi
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
private theorem multiset_eq_of_sum {Γ : Type} [Monoid Γ] (s t : Multiset (Γ →* ℂ))
    (h : ∀ g, (s.map fun f => f g).sum = (t.map fun f => f g).sum) : s = t := by
  classical
  have key : ∀ (u : Multiset (Γ →* ℂ)) (g : Γ),
      Finsupp.linearCombination ℂ (fun f : Γ →* ℂ => (f : Γ → ℂ))
        (u.map fun f => Finsupp.single f (1 : ℂ)).sum g = (u.map fun f => f g).sum := fun u g => by
    induction u using Multiset.induction_on with
    | empty => simp
    | cons a u ih => simp [ih]
  have cnt : ∀ (u : Multiset (Γ →* ℂ)) (f : Γ →* ℂ),
      (u.map fun f => Finsupp.single f (1 : ℂ)).sum f = (u.count f : ℂ) := fun u f => by
    induction u using Multiset.induction_on with
    | empty => simp
    | cons a u ih =>
      rw [Multiset.map_cons, Multiset.sum_cons, Finsupp.add_apply, ih, Multiset.count_cons, Finsupp.single_apply]
      by_cases e : a = f
      · simp [e, add_comm]
      · simp [e, Ne.symm e]
  have h1 := linearIndependent_monoidHom Γ ℂ (funext fun g => (key s g).trans ((h g).trans (key t g).symm))
  ext f
  have h2 := (cnt s f).symm.trans ((congrArg (fun u => u f) h1).trans (cnt t f))
  exact_mod_cast h2
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
private theorem hasSupport_of_charPol (hZ : GlobalTheory.Published.ZelevinskyPolynomialRing) (H : UpperTheory.Zero.LLC.LawsT a ha rc)
    (x : IrrGL (k := w.adicCompletion E)) (s : Multiset (IrrGL (k := w.adicCompletion E))) (hs : HasSupport x.rep s)
    (h1 : ∀ y ∈ s, y.1 = 1) {n : ℕ} (ω : Fin n → (w.adicCompletion E)ˣ →* ℂˣ) (hω : ∀ i, IsSmoothChar (ω i))
    (hp : ∀ g, (rc x).charPol g = ∏ j, (X - C (ω j (a g) : ℂ))) :
    HasSupport x.rep (Finset.univ.val.map fun i => IrrGL.ofChar (ω i) (hω i)) := by
  let S := {χ : (w.adicCompletion E)ˣ →* ℂˣ // IsSmoothChar χ}
  let F : S → IrrGL (k := w.adicCompletion E) := fun χ => IrrGL.ofChar χ.1 χ.2
  obtain ⟨t, rfl⟩ : ∃ t : Multiset S, t.map F = s :=
    haveI : CanLift (IrrGL (k := w.adicCompletion E)) S F fun y => ∃ χ, F χ = y := ⟨fun _ hy => hy⟩
    (Multiset.canLift F (fun y => ∃ χ, F χ = y)).prf s fun y hy => by
      obtain ⟨χ, hχ, e⟩ := GlobalTheory.RoadU.PlainChars.exists_eq_ofChar y (h1 y hy)
      exact ⟨⟨χ, hχ⟩, e.symm⟩
  let c : S → (w.adicCompletion E)ˣ →* ℂ := fun χ => (Units.coeHom ℂ).comp χ.1
  have hc : Function.Injective c := fun χ ψ e =>
    Subtype.ext (MonoidHom.ext fun y => Units.ext (DFunLike.congr_fun e y))
  let t' : Multiset S := Finset.univ.val.map fun i => ⟨ω i, hω i⟩
  have htt : t = t' := by
    refine Multiset.map_injective hc (multiset_eq_of_sum _ _ fun y => ?_)
    obtain ⟨g, rfl⟩ := ha.surj y
    have h1 : (((t.map c).map fun f => f (a g)).map fun r => X - C r).prod =
        (((t'.map c).map fun f => f (a g)).map fun r => X - C r).prod := by
      have h2 := (charPol_supp hZ H x _ hs g).symm.trans (hp g)
      simp only [Multiset.map_map, Function.comp_def, t'] at h2 ⊢
      rw [Finset.prod_eq_multiset_prod] at h2
      refine Eq.trans (congrArg Multiset.prod (Multiset.map_congr rfl fun χ _ => ?_)) h2
      exact (charPol_ofChar H χ.1 χ.2 g).symm
    have h3 := congrArg Polynomial.roots h1
    rw [roots_multiset_prod_X_sub_C, roots_multiset_prod_X_sub_C] at h3
    rw [h3]
  rw [htt, Multiset.map_map] at hs
  exact hs
end
private theorem isSubquotient_of_hasSupport (hZ : GlobalTheory.Published.ZelevinskyPolynomialRing) {k : Type} [Field k] [ValuativeRel k]
    [TopologicalSpace k] [IsNonarchimedeanLocalField k] {n : ℕ} (τ : IrrRep (GL (Fin n) k)) (μ : Fin n → kˣ →* ℂˣ)
    (hμ : ∀ i, IsSmoothChar (μ i)) (hs : HasSupport τ.ρ (Finset.univ.val.map fun i => IrrGL.ofChar (μ i) (hμ i))) :
    IsSubquotient τ.ρ (prinSeries μ) := by
  have hd : ∑ i, (IrrGL.ofChar (μ i) (hμ i)).1 = n := by simp [IrrGL.ofChar]
  refine IsSubquotient.trans ?_ (GlobalTheory.SphSeg.isSubquotient_prodIrr_prinSeries _ hd μ hμ fun _ => rfl)
  obtain ⟨Z, Ψ, -, hΨ, -⟩ := hZ k
  have h1 := SupportRing.pos_pc_sub hΨ hs τ.smooth τ.irr
  obtain ⟨hp, ep⟩ := SupportRing.prodIrr_cls hΨ _ hd
  refine SupportRing.isSubquotient_of_clsGL_ne hp τ.smooth τ.irr ?_
  have h2 := h1 (IrrGL.of τ.ρ τ.smooth τ.irr)
  rw [SupportRing.pc_map, ← ep] at h2
  have e1 : ∀ (A : GrothGL k) (y : IrrGL (k := k)), Ψ.symm (Ψ A - SupportRing.bas Ψ y) y = A y - 1 := by
    intro A y
    rw [SupportRing.bas, ← map_sub, Ψ.symm_apply_apply, Finsupp.sub_apply, Finsupp.single_eq_same]
  rw [e1] at h2
  intro h3
  rw [h3] at h2
  exact absurd h2 (by norm_num)
theorem UpperTheory.V.Z.Desc.W.pseudo_local_langlands_descent :
    _root_.UpperTheory.V.Z.Desc.W.PseudoLocalDescent := by
  intro P L Ω _ _ _ _ _ n w A h a ha rc hrc σ hT ω hω hp
  obtain ⟨a', ha', H⟩ := hrc
  obtain rfl : a' = a := by
    obtain ⟨art, hart⟩ := P.aut.art L Ω
    have hinj := GlobalTheory.ArtinLocalInj.artin_localIdele_injective P.loc.chev L Ω art hart w
    exact MonoidHom.ext fun σ => hinj ((ha'.glob art hart _).trans (ha.glob art hart _).symm)
  haveI : CharZero (w.adicCompletion L) := algebraRat.charZero _
  have hμ : ∀ i, IsSmoothChar (ω i * absPow (w.adicCompletion L) (((n : ℂ) - 1) / 2)) :=
    fun i => (hω i).mul (isSmoothChar_absPow _)
  have e0 : ((n : ℂ) - 1) / 2 + (((1 - (n : ℝ)) / 2 : ℝ) : ℂ) = 0 := by push_cast; ring
  have e1 : ∀ i, (IrrGL.ofChar (ω i) (hω i)).nu (((n : ℂ) - 1) / 2) = IrrGL.ofChar _ (hμ i) := fun i =>
    IrrGL.tw_ofChar _ _ _ _
  let τ : IrrRep (GL (Fin n) (w.adicCompletion L)) := ⟨_, σ.ρ, σ.smooth, σ.irred⟩
  obtain ⟨s, hs0, hs1, -⟩ := hT
  have hs := hasSupport_of_charPol P.loc.zel H (algNorm σ) _
    (SupportRing.hasSupport_nu hs0 (((1 - (n : ℝ)) / 2 : ℝ) : ℂ)) (fun y hy => by
      obtain ⟨z, hz, rfl⟩ := Multiset.mem_map.1 hy
      exact hs1 z hz) ω hω hp
  have h2 := SupportRing.hasSupport_nu hs (((n : ℂ) - 1) / 2)
  have e2 : (algNorm σ).nu (((n : ℂ) - 1) / 2) = IrrGL.of σ.ρ σ.smooth σ.irred := by
    rw [algNorm, IrrGL.nu_nu, add_comm, e0, IrrGL.nu_zero]
  have key : ∀ (x y : IrrGL (k := w.adicCompletion L)) s, x = y → HasSupport x.rep s → HasSupport y.rep s := by
    rintro _ _ _ rfl h; exact h
  have h3 := (key _ _ _ e2 h2).of_equiv (IrrGL.equivOf σ.ρ σ.smooth σ.irred).symm
  simp only [Multiset.map_map, Function.comp_def, e1] at h3
  exact isSubquotient_of_hasSupport P.loc.zel τ _ hμ h3
end
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.SdAdAutQ
section
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 200000

section
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N Polynomial GlobalTheory.CuspRep GlobalTheory.HeckeGal
open GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Af.Bc UpperTheory.V.Published UpperTheory.V.Sd
private theorem fin_scalar {F : Type} [Field F] [NumberField F] (w : HeightOneSpectrum (𝓞 F)) (x : (w.adicCompletion F)ˣ) :
    finGL F 2 (locGL F 2 w (Matrix.GeneralLinearGroup.scalar (Fin 2) x)) =
      Matrix.GeneralLinearGroup.scalar (Fin 2) (localIdele F w x) := by
  have h := GlobalTheory.CuspRep.finId_det_locGL w (Matrix.GeneralLinearGroup.scalar (Fin 1) x)
  rw [locGL, GlobalTheory.CuspRep.cornerGL_scalar] at h ⊢
  rw [finGL, GlobalTheory.CuspRep.cornerGL_scalar]
  congr 1
  exact (congrArg (finId F) (GlobalTheory.CuspRep.CG.det_oneByOne _)).symm.trans
    (h.trans (congrArg (localIdele F w) (GlobalTheory.CuspRep.CG.det_oneByOne _)))
theorem central_character_of_regular_cusp (hP : _root_.UpperTheory.V.Af.Hypotheses') {F : Type} [Field F] [NumberField F] [IsTotallyReal F] (π : TR.CuspSub F 2)
    (hreg : π.IsRegAlg) (hs : ∀ᶠ w : HeightOneSpectrum (𝓞 F) in Filter.cofinite, ∃ B, π.HasSat w B) :
    ∃ ω : HChar F, (∀ w (α β : ℂˣ), π.HasSat w {α, β} → α * β = ω.val w) ∧ ∀ v, ∃ n : ℤ, TR.expo ω v = n := by
  obtain ⟨ω, hω, -⟩ := _root_.UpperTheory.V.Sd.Wc.centChar_alt hP F π
  have hv : ∀ w (α β : ℂˣ), π.HasSat w {α, β} → α * β = ω.val w := fun w α β h => by
    obtain ⟨x, hx⟩ := GlobalTheory.LFun.HasSatGL.exists_vec h
    have hZ := (UpperTheory.V.Br.uOfSat F w _ _ x α β hx).2
    have h2 : π.locRep w (Matrix.GeneralLinearGroup.scalar (Fin 2) (atFin w (unif w))) x = ((ω.val w : ℂˣ) : ℂ) • x := by
      refine Subtype.ext (Subtype.ext (funext fun g => ?_))
      change x.1.1 (g * finGL F 2 (locGL F 2 w _)) = _
      rw [fin_scalar, ← GlobalTheory.CuspRep.scalar_comm, hω _ _ x.2]
      rfl
    exact Units.ext (smul_left_injective ℂ hx.1 (hZ.symm.trans h2))
  refine ⟨ω, hv, fun v => ?_⟩
  have hiso : π.Iso (π.dual.twist ω) := by
    refine hP.smoR F 2 one_le_two _ _ ?_
    filter_upwards [hs, Filter.eventually_cofinite.2 (GlobalTheory.Mem.UnrAe.finite_ramified ω)] with w ⟨B, hB⟩ hu
    obtain ⟨α, β, rfl⟩ := Multiset.card_eq_two.1 hB.card
    have e : (({α, β} : Multiset ℂˣ).map (·⁻¹)).map (· * ω.val w) = {α, β} := by
      rw [← hv w α β hB, Multiset.pair_comm α β]
      simp only [Multiset.insert_eq_cons, Multiset.map_cons, Multiset.map_singleton, inv_mul_cancel_left]
      rw [mul_comm α β, inv_mul_cancel_left]
      exact Multiset.pair_comm α β
    exact ⟨_, hB, e ▸ hB.dual.twist hu⟩
  obtain ⟨m, hm, -, hz⟩ := hreg v
  obtain ⟨x, y, rfl⟩ := Multiset.card_eq_two.1 hm.1
  obtain ⟨i, hi⟩ := hz x (by simp)
  obtain ⟨j, hj⟩ := hz y (by simp)
  have h := congrArg Multiset.sum ((hiso.hasInfChar hm).unique (hm.dual.twist ω))
  simp only [Multiset.insert_eq_cons, Multiset.map_cons, Multiset.map_singleton, Multiset.sum_cons,
    Multiset.sum_singleton] at h
  refine ⟨i + j + 1, ?_⟩
  push_cast at hi hj ⊢
  linear_combination hi + hj - h / 2
end
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.TAcross
section
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 200000

section
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.CuspRep GlobalTheory.HeckeGal GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Af.Bc UpperTheory.V.Z.Bc
open scoped Matrix
private theorem across_cc (Ω : Type) [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] : ∃ c : G ℚ Ω, IsConjEl c := by
  haveI : Algebra.IsAlgebraic ℚ Ω := IsAlgClosure.isAlgebraic
  haveI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed ℚ
  let j : Ω →ₐ[ℚ] ℂ := (by
    refine @_root_.IsAlgClosed.lift _ _ _ _ _ _ _ _ _ _ _ ?_ ?_ ?_
    solve_by_elim* (maxDepth := 2) only [*,
      @_root_.DivisionSemiring.to_moduleIsTorsionFree,
      @_root_.Algebra.IsIntegral.isAlgebraic, @_root_.inferInstance])
  letI : Algebra Ω ℂ := j.toRingHom.toAlgebra
  haveI : IsScalarTower ℚ Ω ℂ := IsScalarTower.of_algebraMap_eq fun x => (j.commutes x).symm
  haveI : Normal ℚ Ω := IsAlgClosure.normal ℚ Ω
  let τ : ℂ ≃ₐ[ℚ] ℂ := AlgEquiv.ofRingEquiv (f := starRingAut) fun x => by simp
  exact ⟨τ.restrictNormal Ω, algebraMap Ω ℂ, fun x => AlgEquiv.restrictNormal_commutes τ Ω x⟩
private theorem across_pair {F₀ F Ω k : Type} [Field F₀] [Field F] [Field Ω] [Algebra F₀ F] [Algebra F₀ Ω] [Algebra F Ω]
    [IsScalarTower F₀ F Ω] [Field k] {n : ℕ} (r : G F₀ Ω →* GL (Fin n) k) (θ : G F₀ Ω →* kˣ) (h : DualTw r θ)
    (c : G F₀ Ω) : ∃ P, IsPairing c (r.comp (resG F₀ F Ω)) (θ.comp (resG F₀ F Ω)) P := by
  obtain ⟨J, hJ⟩ := h
  refine ⟨J * r c⁻¹, fun s s' h => ?_⟩
  have h' : resG F₀ F Ω s' = c * resG F₀ F Ω s * c⁻¹ := h
  have e : r c⁻¹ * r (resG F₀ F Ω s') = r (resG F₀ F Ω s) * r c⁻¹ := by
    rw [h', ← map_mul, ← map_mul]; congr 1; group
  have e' : (r c⁻¹).val * (r (resG F₀ F Ω s')).val = (r (resG F₀ F Ω s)).val * (r c⁻¹).val := congrArg Units.val e
  have hp := hJ (resG F₀ F Ω s)
  simp only [MonoidHom.comp_apply]
  rw [Units.val_mul, ← Matrix.smul_mul, ← hp]
  simp only [Matrix.mul_assoc, e']
private theorem across_tf (L Ω : Type) [Field L] [Field Ω] [Algebra L Ω] : Module.IsTorsionFree L Ω :=
  DivisionSemiring.to_moduleIsTorsionFree
attribute [local instance] across_tf
private theorem across_up (L Ω : Type) [Field L] [CharZero L] [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] [Algebra L Ω] :
    IsAlgClosure L Ω :=
  ⟨IsAlgClosure.isAlgClosed ℚ, Algebra.IsAlgebraic.tower_top (K := ℚ) L⟩
private theorem across_irr {Γ Δ Δ' k : Type} [Group Γ] [Group Δ] [Group Δ'] [Field k] {n : ℕ} (r : Γ →* GL (Fin n) k)
    (f : Δ →* Γ) (f' : Δ' →* Γ) (h : ∀ s, ∃ t, f' t = f s) (H : IsIrr (r.comp f)) : IsIrr (r.comp f') := by
  refine ⟨H.1, fun _ _ _ => trivial, fun W hW hI => H.2.2 W hW fun s v hv => ?_⟩
  obtain ⟨t, ht⟩ := h s
  have := hI t v hv
  rw [MonoidHom.comp_apply, ht] at this
  exact this
theorem UpperTheory.V.Z.Bc.across_alt :
    _root_.UpperTheory.V.Af.HypothesesH' → SolC → BiQuad → Across := by
  intro _ hS hB K K' Ω _ _ _ _ _ _ _ iA _ _ iT iT' iC hK hK' l _ ι n hn r θ hr hθ hd hirr haut
  haveI : CharZero Ω := algebraRat.charZero Ω
  obtain rfl : iA = DivisionRing.toRatAlgebra := Subsingleton.elim _ _
  obtain ⟨M, _, _, iM, _, _, _, _, _, _, _, hs, hs', hM, -⟩ := hB K K' Ω hK hK'
  haveI := across_up K Ω
  haveI := across_up K' Ω
  haveI := across_up M Ω
  obtain ⟨c, hc⟩ := across_cc Ω
  have he : (r.comp (resG ℚ K Ω)).comp (resG K M Ω) = (r.comp (resG ℚ K' Ω)).comp (resG K' M Ω) :=
    MonoidHom.ext fun s => rfl
  have hi : IsIrr ((r.comp (resG ℚ K Ω)).comp (resG K M Ω)) := by
    refine across_irr r _ ((resG ℚ K Ω).comp (resG K M Ω)) ?_ hirr
    rintro ⟨s, ⟨t, rfl⟩, h2⟩
    obtain ⟨u, rfl⟩ := (hM t).2 h2
    exact ⟨u, rfl⟩
  obtain ⟨P, hP⟩ := across_pair (F := K) r θ hd c
  obtain ⟨P', hP'⟩ := across_pair (F := K') r θ hd c
  have h1 := (hS ℚ K M Ω hs ⟨inferInstance, Or.inr ⟨hK, inferInstance⟩⟩ inferInstance iM l ι n hn _ θ
    (hr.comp (continuous_restrictScalarsHom ℚ K Ω)) hi hθ (UpperTheory.V.Ws.auSign θ) ⟨c, P, hc, hP⟩).1 haut
  rw [he] at h1 hi
  exact (hS ℚ K' M Ω hs' ⟨inferInstance, Or.inr ⟨hK', inferInstance⟩⟩ inferInstance iM l ι n hn _ θ
    (hr.comp (continuous_restrictScalarsHom ℚ K' Ω)) hi hθ (UpperTheory.V.Ws.auSign θ) ⟨c, P', hc, hP'⟩).2 h1
end
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.TGapTwo
section
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 200000

section
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N Polynomial GlobalTheory.CuspRep GlobalTheory.HeckeGal GlobalTheory.GalOfCusp
open UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published UpperTheory.V.Z.Bc
section SlopeTestRemainingChoices
variable {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] {a : ℕ}
private theorem lie_central {π : CuspSub E a} {ω : HChar E} (hω : π.HasCentral ω) (z : Cinf E) {ψ : Sm E a} (hψ : ψ ∈ π.V) :
    ∑ i, lieS E a i i z ψ = dchi ω z • ψ := by
  have e2 : lie E a (Central.scL a z) = ∑ i, lieS E a i i z := by
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [lieS_apply, ← map_sum]
    exact congrArg (lie E a) (Matrix.sum_single_eq_diagonal (fun _ : Fin a => z)).symm
  rw [← LinearMap.sum_apply, ← e2]
  refine Subtype.ext (funext fun g => ?_)
  have h1 := Central.hasDerivAt_scalar z ψ g
  have h2 : (fun t : ℝ => ψ.1 (g * Matrix.GeneralLinearGroup.scalar (Fin a) (infId E (expU (t • z))))) =
      fun t : ℝ => Complex.exp (t * dchi ω z) * ψ.1 g := by
    funext t
    have h3 := congrFun (congrArg Subtype.val (hω (infId E (expU (t • z))) ψ hψ)) g
    have h4 := chiInf_expU ω (t • z)
    rw [map_smul, Complex.real_smul] at h4
    rw [← h4]
    exact h3
  rw [h2] at h1
  have h5 := (((Complex.ofRealCLM.hasDerivAt (x := 0)).mul_const (dchi ω z)).cexp).mul_const (ψ.1 g)
  have h6 := h1.unique h5
  change lieD _ ψ.1 g = dchi ω z * ψ.1 g
  rw [h6]
  simp
private theorem expo_central {π : CuspSub E a} {ω : HChar E} (hω : π.HasCentral ω) {τ : E →+* ℂ} {m : Multiset ℂ}
    (hm : π.HasInfChar τ m) : expo ω τ = m.sum := by
  obtain ⟨φ, hφ, h0⟩ := (Submodule.ne_bot_iff _).1 π.ne_bot
  refine smul_left_injective ℂ h0 ?_
  beta_reduce
  rw [← GlobalTheory.trace_Eop_of_hasInfChar E a π τ m hm φ hφ]
  have h1 := lie_central hω (atEmb τ 1) hφ
  have h2 := lie_central hω (atEmb τ Complex.I) hφ
  simp only [Eop, expo, LinearMap.sum_apply, LinearMap.smul_apply, LinearMap.sub_apply, ← Finset.smul_sum, Finset.sum_sub_distrib, h1, h2]
  module
private theorem det_algSat (M : Matrix (Fin 2) (Fin 2) ℂ) (q : ℕ) (x y : ℂˣ)
    (h : M.charpoly = ((algSat 2 q {x, y}).map fun b => X - C b).prod) : M.det = (q : ℂ) * ((x * y : ℂˣ) : ℂ) := by
  have hq : ((q : ℝ) ^ ((((2 : ℕ) : ℝ) - 1) / 2)) * ((q : ℝ) ^ ((((2 : ℕ) : ℝ) - 1) / 2)) = q := by
    rw [← Real.rpow_add' (Nat.cast_nonneg q) (by norm_num)]
    norm_num
  have hq' := congrArg (fun x : ℝ => (x : ℂ)) hq
  simp only [Complex.ofReal_mul, Complex.ofReal_natCast] at hq'
  have e : algSat 2 q {x, y} = {(((q : ℝ) ^ ((((2 : ℕ) : ℝ) - 1) / 2) : ℝ) : ℂ) * x,
      (((q : ℝ) ^ ((((2 : ℕ) : ℝ) - 1) / 2) : ℝ) : ℂ) * y} := by
    simp [algSat]
  rw [Matrix.det_eq_prod_roots_charpoly, h, roots_multiset_prod_X_sub_C, e, Multiset.prod_pair, mul_mul_mul_comm, hq',
    Units.val_mul]
private theorem gap_of_sum {x y : ℂ} (hne : x ≠ y) {i j : ℤ} (hi : x = i + 1 / 2) (hj : y = j + 1 / 2) (hs : x + y = 1) :
    ∃ (c : ℂ) (k : ℕ), 2 ≤ k ∧ ({x, y} : Multiset ℂ) = {c, c + k} := by
  have h0 : i + j = 0 := by
    have : ((i + j : ℤ) : ℂ) = 0 := by push_cast; linear_combination hs - hi - hj
    exact_mod_cast this
  have h1 : i ≠ j := fun e => hne (by rw [hi, hj, e])
  rcases lt_or_gt_of_ne h1 with h | h
  · obtain ⟨k, hk⟩ := Int.eq_ofNat_of_zero_le (sub_nonneg.2 h.le)
    refine ⟨x, k, by omega, ?_⟩
    have : ((j - i : ℤ) : ℂ) = k := by rw [hk]; simp
    push_cast at this
    rw [show x + k = y by linear_combination hi - hj - this]
  · obtain ⟨k, hk⟩ := Int.eq_ofNat_of_zero_le (sub_nonneg.2 h.le)
    refine ⟨y, k, by omega, ?_⟩
    have : ((i - j : ℤ) : ℂ) = k := by rw [hk]; simp
    push_cast at this
    rw [show y + k = x by linear_combination hj - hi - this, Multiset.pair_comm]
end SlopeTestRemainingChoices
theorem UpperTheory.V.Z.Bc.gapTwo_alt :
    _root_.UpperTheory.V.Af.HypothesesH' → UpperTheory.V.Z.Bc.GapTwo := by
  intro _ F Ω _ _ _ _ _ _ l _ ι r P hreg hatt ⟨N, hN, hdet⟩ τ
  obtain ⟨ω, hω⟩ := Central.exists_hasCentral F 2 P
  have hone : (ω * GlobalTheory.HeckeGal.Model.absPow F (-1)) ^ N = 1 := by
    refine PositivityTheory.jumpWindows.FiniteInfinitePlaceProduct.eq_one _ ?_
    filter_upwards [hatt.2] with w ⟨B, hB, hF⟩
    obtain ⟨x, y, rfl⟩ := Multiset.card_eq_two.1 hB.card
    have h1 := PositivityTheory.jumpWindows.PSmo.val_eq_prod (CuspSub.hasCentral_iff.1 hω) hB
    obtain ⟨A, hA⟩ := exists_isPlaceOver Ω w
    obtain ⟨σ, hσ⟩ := ReciprocityTheory.Gal.exists_isFrob hA
    have e2 := (hF A hA).2 σ hσ
    rw [← Matrix.charpoly_map] at e2
    have e3 := det_algSat _ _ _ _ e2
    have e4 : ι (r σ⁻¹ : Matrix (Fin 2) (Fin 2) (Qbar l)).det =
        ((r σ⁻¹ : Matrix (Fin 2) (Fin 2) (Qbar l)).map ι.toRingHom).det := ι.toRingHom.map_det _
    have e5 := congrArg (fun u : (Qbar l)ˣ => ι (u : Qbar l)) (hdet σ⁻¹)
    simp only [Units.val_pow_eq_pow_val, map_pow, Units.val_one, map_one, Matrix.GeneralLinearGroup.val_det_apply] at e5
    rw [e4, e3] at e5
    have e6 := (GlobalTheory.HeckeGal.Model.absPow_isAbsPow F (-1)).2.1 w
    refine Units.ext ?_
    have hp : ∀ ν : HChar F, (ν ^ N).val w = ν.val w ^ N := fun ν => MonoidHom.pow_apply ν.1 N _
    rw [hp, HChar.val_mul, Units.val_pow_eq_pow_val, Units.val_mul, e6, h1, Multiset.prod_pair, Units.val_one, ← e5, mul_comm]
    simp [normV, Ideal.absNorm_apply, Submodule.cardQuot_apply]
  have hsum : ((CG.mk P).infChar τ).sum = 1 := by
    have h1 := GlobalTheory.BCT.TwistDisc.expo_pow (ω * GlobalTheory.HeckeGal.Model.absPow F (-1)) N τ
    have h2 := GlobalTheory.BCT.TwistDisc.expo_pow (1 : HChar F) 0 τ
    rw [pow_zero, Nat.cast_zero, zero_mul] at h2
    have h3 := (CG.hasInfChar_ofChar ω τ).twist (GlobalTheory.HeckeGal.Model.absPow F (-1))
    rw [CG.twist_ofChar, Multiset.map_singleton] at h3
    have h4 := h3.infChar_eq
    rw [CG.infChar_ofChar, Multiset.singleton_inj] at h4
    have h5 : expo (GlobalTheory.HeckeGal.Model.absPow F (-1)) τ = ((-1 : ℝ) : ℂ) := GlobalTheory.CuspRep.Model.expo_absC _ τ
    rw [hone, h2, h4, h5, expo_central hω (ParLaws.hasInfChar_infChar (CG.mk P) τ)] at h1
    have h6 := (mul_eq_zero.1 h1.symm).resolve_left (Nat.cast_ne_zero.2 hN.ne')
    push_cast at h6
    linear_combination h6
  have hm : P.HasInfChar τ ((CG.mk P).infChar τ) := ParLaws.hasInfChar_infChar (CG.mk P) τ
  obtain ⟨hnd, hint⟩ := hreg τ
  obtain ⟨x, y, e⟩ := Multiset.card_eq_two.1 (CG.card_infChar (CG.mk P) τ)
  rw [e] at hm hnd hint hsum
  obtain ⟨i, hi⟩ := hint x (by simp)
  obtain ⟨j, hj⟩ := hint y (by simp)
  obtain ⟨c, k, hk, e'⟩ := gap_of_sum (x := x) (y := y) (by simpa using hnd) (i := i) (j := j) (by rw [hi]; norm_num)
    (by rw [hj]; norm_num) (by simpa using hsum)
  exact ⟨c, k, hk, e' ▸ hm⟩
end
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.THolFin
section
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 200000

section
theorem UpperTheory.V.Sd.holomorphic_finite_of_printed_hida :
    _root_.UpperTheory.V.Af.HypothesesH' → UpperTheory.V.Sd.HolFin := fun _ => UpperTheory.V.Br.holFin0
end
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.TLinkedRig
section
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 200000

section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal IsLocalRing Polynomial UpperTheory.V UpperTheory.V.HV GlobalTheory.GalOfCusp UpperTheory.V.Th
theorem UpperTheory.V.Th.linked_rigid_of_printed_adjoint_lifting :
    _root_.UpperTheory.V.Af.HypothesesH' → _root_.UpperTheory.V.Th.AdjointLiftingTheorem → _root_.UpperTheory.V.Th.LinkedRigAlt := by
  intro hH hAd Ω _ _ _ l _ ι c _ N _ e ψ η σ g₁ B M H L _ _ _ _ _ Φ C₀ k hok hbig hseed
  have hP : _root_.UpperTheory.V.Af.Hypotheses' := hH.toClassicalTheorems
  have hN := hP.litN
  have hA : GlobalTheory.Published.GlobalArtinReciprocity := hN.aut.art
  have hC : Pa.CohP :=
    ⟨hN.coh.lf, hN.coh.lt, hN.coh.le, hN.coh.gf, hN.coh.ge, hN.coh.gw, hN.coh.pt, GlobalTheory.Published.TameLocal_of_duality hN.coh.lt⟩
  have hLoc : W.LocCFTAll := W.locCFT hA hC
  have hB0 : W.ProModularRingExists := W.b0Ex (W.phiAll hC)
  obtain ⟨K, _, _, _, N', w, χ', η', θ, j, hD, hne, hord, hη, hcong, hdisc⟩ := hseed
  have hker : η.ker = Base.galOf ℚ K Ω := by
    rw [← hD.η_ker]
    ext s
    rw [MonoidHom.mem_ker, MonoidHom.mem_ker, ← Units.val_eq_one, ← Units.val_eq_one, hη s]
    exact_mod_cast Iff.rfl
  haveI := hD.imag
  obtain ⟨κ, hκ⟩ := _root_.UpperTheory.V.Sd.twist_of_printed_results hP K Ω hD.quad l hok.l_odd hdisc ι σ hD.cc
  obtain ⟨hk3, hk2⟩ := Pr.kaOf (_root_.UpperTheory.V.Sd.alg_cyclotomic_of_printed_results hP) (_root_.UpperTheory.V.Sd.alg_restriction_of_printed_results hP) Ω l ι c N e ψ η σ g₁ B M H L Φ k
  obtain ⟨ka, hk2, -⟩ := hk2 K hker κ hκ
  obtain ⟨c₁, hle, hL, hv3, hv2, f, hf⟩ := Pr.coefEx l c L Ω _ _ hk3.alg.1 hk2.alg.1
  haveI := Pr.coefIs l c₁
  obtain ⟨R₂⟩ := Pr.cRealEx hA hLoc W.levEx hB0 Ω l ι c N e ψ η σ g₁ B M H L Φ k c₁ f 2 ka C₀ (Or.inl rfl)
    hok hbig hle hf hk2 hv2
  obtain ⟨R₃⟩ := Pr.cRealEx hA hLoc W.levEx hB0 Ω l ι c N e ψ η σ g₁ B M H L Φ k c₁ f 3 _ C₀ (Or.inr rfl)
    hok hbig hle hf hk3 hv3
  exact ⟨_root_.UpperTheory.V.Th.rigPtOf_alt hA hAd Ω l ι c N e ψ η σ g₁ B M H L Φ k c₁ f 3 _ R₃ hL hk3,
    ka, hk2, _root_.UpperTheory.V.Th.rigPtOf_alt hA hAd Ω l ι c N e ψ η σ g₁ B M H L Φ k c₁ f 2 ka R₂ hL hk2⟩
end
end

