module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.Bundle0006
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.Bundle0005
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.RTwist
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0138
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0896
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.HomologyRank.RankHomology
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.FormsFiniteness.OrderedCechToCatCochainsOneApplyValueAtSubset
public import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.Bundle0023
public import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.Bundle0019
public import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.Bundle0029
public import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.Bundle0002
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsIsSplitChartOfBasis

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.PolOfSatOfThetaSat
section
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N Polynomial GlobalTheory.CuspRep GlobalTheory.HeckeGal GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Af.Bc UpperTheory.V.Published

theorem UpperTheory.polOfSat_of_thetaSat :
    UpperTheory.V.Af.Bc.ThetaSat → UpperTheory.V.Af.Bc.PolOfSat := by
  intro hθ hJ hG E _ _ _ n hn P ψ h
  refine GlobalTheory.T.cuspContragredientIsCMConjTwist_of_paired_invTranspose E n P ψ (hG E n _) ?_
  have hiso : (GlobalTheory.ThetaPull.thetaSub P).Iso (P.twist ψ⁻¹) := by
    refine Quotient.exact (hJ.strong_multiplicity_one hn (CG.mk (GlobalTheory.ThetaPull.thetaSub P)) (CG.mk (P.twist ψ⁻¹)) ?_)
    refine h.mono fun w ⟨hu, B, B', h1, h2, e⟩ => ⟨B'.map (·⁻¹), hθ E n P w B' h2, ?_⟩
    have hu' : (ψ⁻¹).UnrAt w := fun x hx => by
      have h3 : ψ.loc w x = 1 := hu x hx
      exact (congrArg Inv.inv h3).trans inv_one
    rw [e]
    exact GlobalTheory.SphGal.hasSatGL_twist E n P ψ⁻¹ w B hu' h1
  obtain ⟨T, hT⟩ := hiso
  refine ⟨((GlobalTheory.ThetaPull.pull E n).submoduleMap P.V).trans T, fun o φ => ?_⟩
  exact (congrArg T (Subtype.ext (GlobalTheory.ThetaPull.act_pull o φ.1).symm)).trans
    (hT o ((GlobalTheory.ThetaPull.pull E n).submoduleMap P.V φ))
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.ShapiroFunctorialOfCoinductionBijective
section
open CategoryTheory UpperTheory.V.Af.CohB in
theorem UpperTheory.shapiro_functorial_of_coinduction_bijective :
    UpperTheory.V.Af.CohB.ToCoInj → UpperTheory.V.Af.CohB.ToCoSurj → UpperTheory.V.Af.CohB.ShapiroFun := by
  intro hi hs Γ X Y _ _ _ p hp y hy d ξ
  let e := LinearEquiv.ofBijective (toCo p hp y ξ) ⟨hi Γ X Y p hp y hy d ξ, hs Γ X Y p hp y hy d ξ⟩
  have he : ∀ g : Γ, e.toLinearMap ∘ₗ funRep X ξ g =
      Representation.coind (MulAction.stabilizer Γ y).subtype (fibRep p hp y ξ) g ∘ₗ e.toLinearMap := by
    intro g
    refine LinearMap.ext fun f => Subtype.ext (funext fun h => funext fun x => ?_)
    change funRep X ξ h (funRep X ξ g f) x.1 = funRep X ξ (h * g) f x.1
    rw [map_mul]
    rfl
  let i : Rep.of (funRep X ξ) ≅ Rep.coind (MulAction.stabilizer Γ y).subtype (Rep.of (fibRep p hp y ξ)) :=
    Rep.mkIso (Representation.Equiv.mk e he)
  unfold totCoh
  congr 1
  funext q
  exact (((groupCohomology.functor ℂ Γ q).mapIso i) ≪≫
    groupCohomology.coindIso (Rep.of (fibRep p hp y ξ)) q).toLinearEquiv.rank_eq
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.SiegelLeviBlockAevalStable
section
open NumberField NumberField.mixedEmbedding Matrix MeasureTheory GroundTheory.Automorphic GroundTheory.Automorphic.AutomorphicForm UpperTheory.V.Af.Fin
open scoped TensorProduct
attribute [local instance 100] LieRing.ofAssociativeRing

private theorem aeval_inter {M N : Type} [AddCommGroup M] [Module ℂ M] [AddCommGroup N] [Module ℂ N]
    (f : M →ₗ[ℂ] N) (T : Module.End ℂ M) (T' : Module.End ℂ N) (h : ∀ x, f (T x) = T' (f x))
    (p : Polynomial ℂ) (x : M) : f (Polynomial.aeval T p x) = Polynomial.aeval T' p (f x) :=
  _root_.UpperTheory.Reformulated.B.Qe22.aeval_inter f T T' h p x

theorem UpperTheory.siegelLevi_block_aeval_stable :
    ∀ (K : Type) [Field K] [NumberField K] (a n : ℕ) (e : Fin a ↪ Fin n) (Γ : Set (AdelicGLn.AdelicGL K n)) (S Z : Submodule ℂ (archSmooth K n)) (ι : Type) [Fintype ι] (D : Idem (mixedSpace K) ι), (∀ ψ ∈ Z, ∀ g ∈ Γ, ∀ m, ψ.1 (g * emb e m) = 0) → (∀ τ u, AlgMod S Z (archCapBlock D e τ u)) → Centre (slSp e Γ S) := by
  intro K _ _ a n e Γ S Z ι _ D hZ hS z hz
  refine UpperTheory.algMod_bot_of_mem_adjoin_commuting _ _ {x | ∃ τ u, x = capOp D a τ u} ?_ ?_ _ (UpperTheory.centerU_action_mem_adjoin_capOp K a ι D z hz)
  · rintro _ ⟨τ, u, rfl⟩ _ ⟨σ, v, rfl⟩
    exact Zc_comm (UpperTheory.qdet_generates_universalEnveloping_centre K a ι D τ u) (UpperTheory.qdet_generates_universalEnveloping_centre K a ι D σ v)
  · rintro _ ⟨τ, u, rfl⟩
    obtain ⟨p, hp, hpS⟩ := hS τ u
    refine ⟨p, hp, fun x hx => ?_⟩
    have hle : slSp e Γ S ≤ LinearMap.ker (Polynomial.aeval (capOp D a τ u) p) := by
      refine Submodule.span_le.2 ?_
      rintro φ ⟨ψ, hψ, g, hg, hφ⟩
      obtain ⟨f, hf, hl⟩ := UpperTheory.exists_restriction_blockEmbedding_intertwines_lie K a n e g
      have hfφ : φ = f ψ := Subtype.ext (funext fun m => (hφ m).trans (hf ψ m).symm)
      have hgen : ∀ i j y, f (gen D (lam K n) τ (e i) (e j) y) = gen D (lam K a) τ i j (f y) := fun i j y =>
        gen_inter D (lam K n) (lam K a) τ (e i) (e j) i j (f ∘ₗ LinearMap.applyₗ y) (LinearMap.applyₗ (f y))
          fun t => by
            change f (lam K n (Matrix.single (e i) (e j) t) y) = lam K a (Matrix.single i j t) (f y)
            rw [← matrixExtendByZero_single, hl]
      have hq : ∀ y, f (archCapBlock D e τ u y) = capOp D a τ u (f y) :=
        UpperTheory.algMod_of_injective_intertwining _ _ a f _ _ hgen u
      change Polynomial.aeval (capOp D a τ u) p φ = 0
      rw [hfφ, ← aeval_inter f _ _ hq]
      exact Subtype.ext (funext fun m => (hf _ m).trans (hZ _ (hpS ψ hψ) g hg m))
    exact hle hx
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.ThetaSatakeParametersInverse
section
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N Polynomial GlobalTheory.CuspRep GlobalTheory.HeckeGal GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Af.Bc UpperTheory.V.Published

private theorem hasSatGL_of_invT {E : Type} [Field E] [NumberField E] {a : ℕ} {w w' : HeightOneSpectrum (𝓞 E)}
    (c : w.adicCompletion E ≃+* w'.adicCompletion E) (hc : ∀ x, Valued.v (c x) = Valued.v x)
    (hq : Formalism.UG.qV E w' = Formalism.UG.qV E w)
    {V W : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
    {ρ : Representation ℂ (GL (Fin a) (w.adicCompletion E)) V} {ρ' : Representation ℂ (GL (Fin a) (w'.adicCompletion E)) W}
    (T : V ≃ₗ[ℂ] W) (hT : ∀ g x, ρ' (GlobalTheory.LFun.ConjPlace.invT c a g) (T x) = T (ρ g x)) {B : Multiset ℂˣ}
    (h : GlobalTheory.LFun.HasSatGL w ρ B) : GlobalTheory.LFun.HasSatGL w' ρ' (B.map (·⁻¹)) := by
  have hK := GlobalTheory.LFun.ConjPlace.mem_iff_invT (n := a) c (GlobalTheory.LFun.ConjPlace.map_mem_Ov_iff c hc)
  have hf : ∀ g y, T.toLinearMap ((ρ.comp (GlobalTheory.LFun.ConjPlace.invT c a).symm.toMonoidHom) g y) =
      ρ' g (T.toLinearMap y) := fun g y => by
    change T (ρ ((GlobalTheory.LFun.ConjPlace.invT c a).symm g) y) = ρ' g (T y)
    rw [← hT, MulEquiv.apply_symm_apply]
  have key : ∀ x, GlobalTheory.LFun.IsSatVecGL w ρ x B → GlobalTheory.LFun.IsSatVecGL w' ρ' (T x) (B.map (·⁻¹)) := fun x hx =>
    (GlobalTheory.LFun.ConjPlace.isSatVecGL_invT c hc hq hx).map T.toLinearMap hf
      ((map_ne_zero_iff T T.injective).2 hx.1)
  constructor
  · obtain ⟨x, hx⟩ := h.exists_vec
    exact (Submodule.ne_bot_iff _).2 ⟨_, (key x hx).2.1, (key x hx).1⟩
  · intro y hy h0
    obtain ⟨x, rfl⟩ := T.surjective y
    refine key x (h.2 x (GlobalTheory.LGrp.mem_fixed.2 fun k hk => T.injective ?_) ((map_ne_zero_iff T T.injective).1 h0))
    have := GlobalTheory.LGrp.mem_fixed.1 hy _ ((hK k).1 hk)
    rwa [hT] at this

private theorem theta_locGL {E : Type} [Field E] [NumberField E] [IsCMField E] {a : ℕ} (w : HeightOneSpectrum (𝓞 E))
    (g : GL (Fin a) ((cPl w).adicCompletion E)) :
    thetaGL a (GlobalTheory.ThetaPull.cFin E) (locGL E a (cPl w) g) =
      locGL E a w (thetaGL a (RingHom.id _) (Matrix.GeneralLinearGroup.map (conjLoc _ w) g)) := by
  have key : ∀ v, Matrix.GeneralLinearGroup.map (pLoc E v) (thetaGL a (GlobalTheory.ThetaPull.cFin E) (locGL E a (cPl w) g)) =
      thetaGL a (RingHom.id _) (Matrix.GeneralLinearGroup.map (conjLoc _ v)
        (Matrix.GeneralLinearGroup.map (pLoc E (cPl v)) (locGL E a (cPl w) g))) := fun v =>
    GlobalTheory.ThetaPull.map_thetaGL (pLoc E v) (RingHom.id _) (RingHom.id _) (fun _ => rfl)
      (Matrix.GeneralLinearGroup.map (GlobalTheory.ThetaPull.cFin E) (locGL E a (cPl w) g))
  have key2 : ∀ v, Matrix.GeneralLinearGroup.map (pLoc E v) (thetaGL a (GlobalTheory.ThetaPull.cFin E) (locGL E a (cPl w) g)) =
      Matrix.GeneralLinearGroup.map (pLoc E v)
        (locGL E a w (thetaGL a (RingHom.id _) (Matrix.GeneralLinearGroup.map (conjLoc _ w) g))) := fun v => by
    rw [key]
    by_cases h : v = w
    · subst h
      rw [pLoc_locGL, pLoc_locGL]
    · rw [pLoc_locGL_of_ne h, pLoc_locGL_of_ne (fun e => h (conjSrc_injective _ e)), map_one, map_one]
  refine Units.ext (Matrix.ext fun i j => FiniteAdeleRing.ext _ fun v => ?_)
  exact congrArg (fun u : GL (Fin a) (v.adicCompletion E) => u.val i j) (key2 v)

private theorem conjLoc_surjective {E : Type} [Field E] [NumberField E] [IsCMField E] (w : HeightOneSpectrum (𝓞 E)) :
    Function.Surjective (conjLoc (IsCMField.complexConj E).toRingEquiv w) := fun y => by
  classical
  refine ⟨pLoc E _ (GlobalTheory.ThetaPull.cFin E (sLoc E w y)), ?_⟩
  rw [← pLoc_conjFin]
  exact (congrArg (pLoc E w) (GlobalTheory.ThetaPull.cFin_cFin _)).trans
    (Pi.single_eq_same (M := fun v : HeightOneSpectrum (𝓞 E) => v.adicCompletion E) w y)

theorem UpperTheory.theta_satake_parameters_inverse :
    UpperTheory.V.Af.Bc.ThetaSat := by
  intro E _ _ _ n P w B h
  rw [CG.hasSat_mk] at h ⊢
  let c : (cPl w).adicCompletion E ≃+* w.adicCompletion E :=
    RingEquiv.ofBijective (conjLoc _ w) ⟨(conjLoc _ w).injective, conjLoc_surjective w⟩
  have hq : Formalism.UG.qV E w = Formalism.UG.qV E (cPl w) := by
    change Ideal.absNorm w.asIdeal = Ideal.absNorm (conjSrc (IsCMField.complexConj E).toRingEquiv w).asIdeal
    rw [(GlobalTheory.Mem.Chr.conjPl_iff_comap _ _ _).1 (conjPl_conjSrc (IsCMField.complexConj E).toRingEquiv w)]
    rw [Ideal.absNorm_eq_natCard, Ideal.absNorm_eq_natCard]
    exact (Nat.card_congr (Ideal.quotientEquiv (w.asIdeal.comap (RingOfIntegers.mapRingEquiv (IsCMField.complexConj E).toRingEquiv).toRingHom) w.asIdeal (RingOfIntegers.mapRingEquiv (IsCMField.complexConj E).toRingEquiv)
      (Ideal.map_comap_of_surjective _ (RingEquiv.surjective _) _).symm).toEquiv).symm
  let ρ' := (GlobalTheory.ThetaPull.thetaSub P).locRep w
  let T₀ : P.V ≃ₗ[ℂ] (GlobalTheory.ThetaPull.thetaSub P).V := (GlobalTheory.ThetaPull.pull E n).submoduleMap P.V
  have h0 : ∀ g x, ρ' (thetaGL n (RingHom.id _) (Matrix.GeneralLinearGroup.map (conjLoc _ w) g)) (T₀ x) =
      T₀ (P.locRep (cPl w) g x) := fun g x => by
    rw [CuspSub.locRep_eq, CuspSub.locRep_eq, ← theta_locGL]
    exact Subtype.ext (GlobalTheory.ThetaPull.pull_act (.fin (locGL E n (cPl w) g)) x.1).symm
  let k := PhiU n (w.adicCompletion E)
  let S : (GlobalTheory.ThetaPull.thetaSub P).V ≃ₗ[ℂ] (GlobalTheory.ThetaPull.thetaSub P).V :=
    LinearEquiv.ofLinear (ρ' k⁻¹) (ρ' k) (by rw [← Module.End.mul_eq_comp, ← map_mul, inv_mul_cancel, map_one]; rfl)
      (by rw [← Module.End.mul_eq_comp, ← map_mul, mul_inv_cancel, map_one]; rfl)
  refine hasSatGL_of_invT c (conjLoc_spec _ w).2.2 hq (T₀.trans S) (fun g x => ?_) h
  have e : thetaGL n (RingHom.id _) (Matrix.GeneralLinearGroup.map (conjLoc _ w) g) =
      k * GlobalTheory.LFun.ConjPlace.invT c n g * k⁻¹ := by
    have e1 : GlobalTheory.LFun.ConjPlace.invT c n g = GlobalTheory.CuspRep.invT n _ (Matrix.GeneralLinearGroup.map (conjLoc _ w) g) :=
      Units.ext (Matrix.ext fun i j => GlobalTheory.LFun.ConjPlace.invT_val _ g i j)
    rw [e1]
    rfl
  change ρ' _ (ρ' k⁻¹ (T₀ x)) = ρ' k⁻¹ (T₀ _)
  rw [← h0, e, ← Module.End.mul_apply, ← Module.End.mul_apply, ← map_mul, ← map_mul]
  congr 2
  group
end

