module

public import Mathlib
public import Development.WeilBound.CoreStatements.PublishedTheorems.PoitouTateDuality.Bundle0003
public import Development.WeilBound.CoreStatements.PublishedTheorems.PoitouTateDuality.Bundle0001
public import Development.WeilBound.CoreStatements.PublishedTheorems.PoitouTateDuality.Bundle0002
public import Development.WeilBound.CoreStatements.PublishedTheorems.PoitouTateDuality.PtfsDefs
public import Development.WeilBound.CoreStatements.EulerCharacteristicCounts.Bundle0004
public import GroundTheory.ProfiniteCohomology.PoitouTate.PoitouTateNineTermGs
public import Development.WeilBound.CoreStatements.PublishedTheorems.PoitouTateDuality.Bundle0004
public import Development.WeilBound.CoreStatements.PublishedTheorems.PoitouTateDuality.Bundle0005
public import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.Bundle0023

@[expose] public section

-- bundled from Development.WeilBound.CoreStatements.PublishedTheorems.PoitouTateDuality.FinalPtfsUnif
section
noncomputable section

open NumberField IsDedekindDomain CategoryTheory GroundTheory.ProfCoh GroundTheory.Global GroundTheory.LocalField
  ReciprocityTheory.Gal Formalism.ConjugateSelfDual GlobalTheory.Published GlobalTheory.Published.PoitouTate PositivityTheory.PoitouTateConclusion

namespace PositivityTheory.Lit1.PTN

attribute [local instance 2000] Rep.hV2

theorem exists_uniformizer_ord' (F : Type) [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F)) :
    ∃ ϖ : 𝓞 F, ϖ ∈ v.asIdeal ∧ ϖ ∉ v.asIdeal ^ 2 ∧
      ord ((ϖ : F) : v.adicCompletion F) = 1 := by
  have hlt : v.asIdeal ^ (1 + 1) < v.asIdeal ^ 1 := Ideal.pow_succ_lt_pow v.ne_bot 1
  rw [pow_one] at hlt
  obtain ⟨ϖ, hϖ, hϖ2⟩ := SetLike.exists_of_lt hlt
  refine ⟨ϖ, hϖ, hϖ2, ?_⟩
  apply GroundTheory.Global.ord_eq_one_of_valued_eq_exp
  have h0 : ϖ ≠ 0 := by
    rintro rfl
    exact hϖ2 (Ideal.zero_mem _)
  have hne := v.intValuation_ne_zero ϖ h0
  have h1 : v.intValuation ϖ ≤ WithZero.exp (-(1 : ℕ) : ℤ) :=
    (v.intValuation_le_pow_iff_mem ϖ 1).2 (by rwa [pow_one])
  have h2 : ¬ v.intValuation ϖ ≤ WithZero.exp (-(2 : ℕ) : ℤ) := fun h =>
    hϖ2 ((v.intValuation_le_pow_iff_mem ϖ 2).1 h)
  have hval : v.intValuation ϖ = WithZero.exp (-1 : ℤ) := by
    rw [← WithZero.exp_log hne] at h1 h2 ⊢
    rw [WithZero.exp_le_exp] at h1 h2
    congr 1
    push_cast at h1 h2
    omega
  rw [HeightOneSpectrum.valuedAdicCompletion_eq_valuation']
  exact (HeightOneSpectrum.valuation_of_algebraMap v ϖ).trans hval

end PositivityTheory.Lit1.PTN
end
end

-- bundled from Development.WeilBound.CoreStatements.PublishedTheorems.PoitouTateDuality.NineAddOfFound2Fun
section
noncomputable section

open CategoryTheory GroundTheory.ProfCoh

namespace PositivityTheory.Lit1.PTN

attribute [local instance 2000] Rep.hV2


set_option maxHeartbeats 1000000 in
theorem nineAdd_of_found2 {N : ℕ} [NeZero N]
    {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    {ι : Type} [Fintype ι] {Hv : ι → Type} [∀ v, Group (Hv v)] [∀ v, TopologicalSpace (Hv v)]
    [∀ v, IsTopologicalGroup (Hv v)] (φ : ∀ v, Hv v →ₜ* G)
    {κ : Type} [Fintype κ] (e : κ ≃ ι)
    (D : Rep.{0} (ULift.{0} ℤ) G) [IsDiscreteRep D] (M : Rep.{0} (ULift.{0} ℤ) G) [IsDiscreteRep M]
    [Finite M] (inv : ∀ v, cohomology (Rep.res (φ v).toMonoidHom D) 2 →+ QZ)
    (δ₁ : (cohomology (dualRep D M) 2 →+ QZ) →+ cohomology M 1)
    (δ₂ : (cohomology (dualRep D M) 1 →+ QZ) →+ cohomology M 2)
    (hx : Function.Injective (ptGlobalToLocal φ M 0).hom ∧
      Function.Exact (ptGlobalToLocal φ M 0).hom (ptLocalDualMap φ D M inv (show 0 + 2 = 2 from rfl)) ∧
      Function.Exact (ptLocalDualMap φ D M inv (show 0 + 2 = 2 from rfl)) δ₁ ∧
      Function.Exact δ₁ (ptGlobalToLocal φ M 1).hom ∧
      Function.Exact (ptGlobalToLocal φ M 1).hom (ptLocalDualMap φ D M inv (show 1 + 1 = 2 from rfl)) ∧
      Function.Exact (ptLocalDualMap φ D M inv (show 1 + 1 = 2 from rfl)) δ₂ ∧
      Function.Exact δ₂ (ptGlobalToLocal φ M 2).hom ∧
      Function.Exact (ptGlobalToLocal φ M 2).hom (ptLocalDualMap φ D M inv (show 2 + 0 = 2 from rfl)) ∧
      Function.Surjective (ptLocalDualMap φ D M inv (show 2 + 0 = 2 from rfl)))

    {H0 H1 H2 : Type} [AddCommGroup H0] [Module (ZMod N) H0] [AddCommGroup H1] [Module (ZMod N) H1]
    [AddCommGroup H2] [Module (ZMod N) H2]
    {L0 L1 L2 : κ → Type} [∀ k, AddCommGroup (L0 k)] [∀ k, Module (ZMod N) (L0 k)]
    [∀ k, AddCommGroup (L1 k)] [∀ k, Module (ZMod N) (L1 k)]
    [∀ k, AddCommGroup (L2 k)] [∀ k, Module (ZMod N) (L2 k)]
    {Y0 Y1 Y2 : Type} [AddCommGroup Y0] [Module (ZMod N) Y0] [AddCommGroup Y1] [Module (ZMod N) Y1]
    [AddCommGroup Y2] [Module (ZMod N) Y2]
    {W0 W1 W2 : κ → Type} [∀ k, AddCommGroup (W0 k)] [∀ k, Module (ZMod N) (W0 k)]
    [∀ k, AddCommGroup (W1 k)] [∀ k, Module (ZMod N) (W1 k)]
    [∀ k, AddCommGroup (W2 k)] [∀ k, Module (ZMod N) (W2 k)]
    (res0 : ∀ k, H0 →ₗ[ZMod N] L0 k) (res1 : ∀ k, H1 →ₗ[ZMod N] L1 k)
    (res2 : ∀ k, H2 →ₗ[ZMod N] L2 k)
    (rs0 : ∀ k, Y0 →ₗ[ZMod N] W0 k) (rs1 : ∀ k, Y1 →ₗ[ZMod N] W1 k) (rs2 : ∀ k, Y2 →ₗ[ZMod N] W2 k)
    (P0 : ∀ k, L0 k → W2 k → ZMod N) (P1 : ∀ k, L1 k → W1 k → ZMod N)
    (P2 : ∀ k, L2 k → W0 k → ZMod N)
    (f0 : H0 →ₗ[ZMod N] ∀ k, L0 k) (f1 : (∀ k, L0 k) →ₗ[ZMod N] Module.Dual (ZMod N) Y2)
    (f3 : H1 →ₗ[ZMod N] ∀ k, L1 k) (f4 : (∀ k, L1 k) →ₗ[ZMod N] Module.Dual (ZMod N) Y1)
    (f6 : H2 →ₗ[ZMod N] ∀ k, L2 k) (f7 : (∀ k, L2 k) →ₗ[ZMod N] Module.Dual (ZMod N) Y0)
    (hf0 : ∀ x k, f0 x k = res0 k x) (hf3 : ∀ x k, f3 x k = res1 k x)
    (hf6 : ∀ x k, f6 x k = res2 k x)
    (hf1 : ∀ x y, f1 x y = ∑ k, P0 k (x k) (rs2 k y))
    (hf4 : ∀ x y, f4 x y = ∑ k, P1 k (x k) (rs1 k y))
    (hf7 : ∀ x y, f7 x y = ∑ k, P2 k (x k) (rs0 k y))

    (E0 : H0 ≃+ cohomology M 0) (E1 : H1 ≃+ cohomology M 1) (E2 : H2 ≃+ cohomology M 2)
    (Ev0 : ∀ k, L0 k ≃+ cohomology (Rep.res (φ (e k)).toMonoidHom M) 0)
    (Ev1 : ∀ k, L1 k ≃+ cohomology (Rep.res (φ (e k)).toMonoidHom M) 1)
    (Ev2 : ∀ k, L2 k ≃+ cohomology (Rep.res (φ (e k)).toMonoidHom M) 2)
    (F0 : Y0 ≃+ cohomology (dualRep D M) 0) (F1 : Y1 ≃+ cohomology (dualRep D M) 1)
    (F2 : Y2 ≃+ cohomology (dualRep D M) 2)
    (Fv0 : ∀ k, W0 k ≃+ cohomology (Rep.res (φ (e k)).toMonoidHom (dualRep D M)) 0)
    (Fv1 : ∀ k, W1 k ≃+ cohomology (Rep.res (φ (e k)).toMonoidHom (dualRep D M)) 1)
    (Fv2 : ∀ k, W2 k ≃+ cohomology (Rep.res (φ (e k)).toMonoidHom (dualRep D M)) 2)
    (sq0 : ∀ k x, Ev0 k (res0 k x) = ptRes φ M (e k) 0 (E0 x))
    (sq1 : ∀ k x, Ev1 k (res1 k x) = ptRes φ M (e k) 1 (E1 x))
    (sq2 : ∀ k x, Ev2 k (res2 k x) = ptRes φ M (e k) 2 (E2 x))
    (tq0 : ∀ k y, Fv0 k (rs0 k y) = ptRes φ (dualRep D M) (e k) 0 (F0 y))
    (tq1 : ∀ k y, Fv1 k (rs1 k y) = ptRes φ (dualRep D M) (e k) 1 (F1 y))
    (tq2 : ∀ k y, Fv2 k (rs2 k y) = ptRes φ (dualRep D M) (e k) 2 (F2 y))
    (hQ0 : ∀ k a b, zmodToQZ N (P0 k a b) =
      - inv (e k) (cupPairing (ptLocalEval φ D M (e k)) (rfl : 0 + 2 = 2) (Ev0 k a) (Fv2 k b)))
    (hQ1 : ∀ k a b, zmodToQZ N (P1 k a b) =
      inv (e k) (cupPairing (ptLocalEval φ D M (e k)) (rfl : 1 + 1 = 2) (Ev1 k a) (Fv1 k b)))
    (hQ2 : ∀ k a b, zmodToQZ N (P2 k a b) =
      - inv (e k) (cupPairing (ptLocalEval φ D M (e k)) (rfl : 2 + 0 = 2) (Ev2 k a) (Fv0 k b))) :
    NineAdd f0 f1 f3 f4 f6 f7 := by
  obtain ⟨i0, x1, x2, x3, x4, x5, x6, x7, s7⟩ := hx
  have hL : ∀ {r : ℕ} {H : Type} [AddCommGroup H] [Module (ZMod N) H] {L : κ → Type}
      [∀ k, AddCommGroup (L k)] [∀ k, Module (ZMod N) (L k)] (res : ∀ k, H →ₗ[ZMod N] L k)
      (f : H →ₗ[ZMod N] ∀ k, L k) (hf : ∀ x k, f x k = res k x) (E : H ≃+ cohomology M r)
      (Ev : ∀ k, L k ≃+ cohomology (Rep.res (φ (e k)).toMonoidHom M) r)
      (sq : ∀ k x, Ev k (res k x) = ptRes φ M (e k) r (E x)) (x : H),
      (ptGlobalToLocal φ M r).hom (E x) =
        ((1 : ℤˣ) : ℤ) • ((AddEquiv.piCongrRight Ev).trans
          (reindexAdd (fun v => cohomology (Rep.res (φ v).toMonoidHom M) r) e)) (f x) := by
    intro r H _ _ L _ _ res f hf E Ev sq x
    rw [Units.val_one, one_smul]
    rw [locSq_reindex φ e M r (fun k => (res k).toAddMonoidHom) E Ev sq x]
    rw [AddEquiv.trans_apply]
    refine congrArg _ (funext fun k => ?_)
    rw [AddEquiv.piCongrRight_apply, hf]
    rfl
  have hT : ∀ {r s : ℕ} (h : r + s = 2) {L : κ → Type} [∀ k, AddCommGroup (L k)]
      [∀ k, Module (ZMod N) (L k)] {Y : Type} [AddCommGroup Y] [Module (ZMod N) Y]
      {W : κ → Type} [∀ k, AddCommGroup (W k)] [∀ k, Module (ZMod N) (W k)]
      (rs : ∀ k, Y →ₗ[ZMod N] W k) (P : ∀ k, L k → W k → ZMod N)
      (f : (∀ k, L k) →ₗ[ZMod N] Module.Dual (ZMod N) Y)
      (hf : ∀ x y, f x y = ∑ k, P k (x k) (rs k y))
      (Ev : ∀ k, L k ≃+ cohomology (Rep.res (φ (e k)).toMonoidHom M) r)
      (F : Y ≃+ cohomology (dualRep D M) s)
      (Fv : ∀ k, W k ≃+ cohomology (Rep.res (φ (e k)).toMonoidHom (dualRep D M)) s)
      (tq : ∀ k y, Fv k (rs k y) = ptRes φ (dualRep D M) (e k) s (F y)) (ε : ℤˣ)
      (hQ : ∀ k a b, (ε : ℤ) • zmodToQZ N (P k a b) =
        inv (e k) (cupPairing (ptLocalEval φ D M (e k)) h (Ev k a) (Fv k b))) (x : ∀ k, L k),
      ptLocalDualMap φ D M inv h (((AddEquiv.piCongrRight Ev).trans
          (reindexAdd (fun v => cohomology (Rep.res (φ v).toMonoidHom M) r) e)) x) =
        (ε : ℤ) • dualQZ F (f x) := by
    intro r s h L _ _ Y _ _ W _ _ rs P f hf Ev F Fv tq ε hQ x
    refine AddMonoidHom.ext fun y => ?_
    rw [AddEquiv.trans_apply]
    change ptLocalDualMap φ D M inv h (reindexAdd (fun v => cohomology (Rep.res (φ v).toMonoidHom M) r) e
      (fun k => Ev k (x k))) y = _
    set_option synthInstance.maxHeartbeats 100000 in
      rw [ptLocalDualMap_reindex, AddMonoidHom.smul_apply, dualQZ_apply, hf, map_sum, Finset.smul_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [hQ, tq, AddEquiv.apply_symm_apply, ptLocalPairing_apply]
  exact nineAdd_intro (ptGlobalToLocal φ M 0).hom.toAddMonoidHom
    (ptLocalDualMap φ D M inv (show 0 + 2 = 2 from rfl)) δ₁
    (ptGlobalToLocal φ M 1).hom.toAddMonoidHom (ptLocalDualMap φ D M inv (show 1 + 1 = 2 from rfl)) δ₂
    (ptGlobalToLocal φ M 2).hom.toAddMonoidHom (ptLocalDualMap φ D M inv (show 2 + 0 = 2 from rfl))
    E0 ((AddEquiv.piCongrRight Ev0).trans
      (reindexAdd (fun v => cohomology (Rep.res (φ v).toMonoidHom M) 0) e)) (dualQZ F2)
    E1 ((AddEquiv.piCongrRight Ev1).trans
      (reindexAdd (fun v => cohomology (Rep.res (φ v).toMonoidHom M) 1) e)) (dualQZ F1)
    E2 ((AddEquiv.piCongrRight Ev2).trans
      (reindexAdd (fun v => cohomology (Rep.res (φ v).toMonoidHom M) 2) e)) (dualQZ F0)
    ![1, -1, 1, 1, 1, -1]
    (hL res0 f0 hf0 E0 Ev0 sq0) (hT _ rs2 P0 f1 hf1 Ev0 F2 Fv2 tq2 (-1) (fun k a b => by rw [hQ0, Units.val_neg, Units.val_one, neg_one_zsmul, neg_neg]))
    (hL res1 f3 hf3 E1 Ev1 sq1) (hT _ rs1 P1 f4 hf4 Ev1 F1 Fv1 tq1 1 (fun k a b => by rw [hQ1, Units.val_one, one_smul]))
    (hL res2 f6 hf6 E2 Ev2 sq2) (hT _ rs0 P2 f7 hf7 Ev2 F0 Fv0 tq0 (-1) (fun k a b => by rw [hQ2, Units.val_neg, Units.val_one, neg_one_zsmul, neg_neg]))
    i0 x1 x2 x3 x4 x5 x6 x7 s7

end PositivityTheory.Lit1.PTN
end
end

-- bundled from Development.WeilBound.CoreStatements.PublishedTheorems.PoitouTateDuality.PfInvMatchNsmulB
section
noncomputable section

open NumberField IsDedekindDomain CategoryTheory GroundTheory.ProfCoh GroundTheory.Global ReciprocityTheory.Gal Formalism.ConjugateSelfDual
  GlobalTheory.Published GlobalTheory.Published.PoitouTate PositivityTheory.PoitouTateConclusion

namespace PositivityTheory.Lit1.PTN

attribute [local instance 2000] Rep.hV2


set_option maxHeartbeats 1000000 in
theorem loc_act_rootOf (Kf : FiniteSubfield) [NumberField Kf.1] [IsAlgClosure Kf.1 (AlgebraicClosure ℚ)]
    (S : Set (HeightOneSpectrum (𝓞 Kf.1))) [Fintype S] {l r : ℕ} [Fact l.Prime] [NeZero (l ^ r)]
    (ζ : AlgebraicClosure ℚ) (hζ : IsPrimitiveRoot ζ (l ^ r))
    (ιs : ∀ v : S, AlgebraicClosure ℚ →ₐ[Kf.1]
      AlgebraicClosure ((v : HeightOneSpectrum (𝓞 Kf.1)).adicCompletion Kf.1))
    (v : S) (A : ValuationSubring (AlgebraicClosure ℚ))
    (ev : (AlgebraicClosure ((v : HeightOneSpectrum (𝓞 Kf.1)).adicCompletion Kf.1) ≃ₐ[
        (v : HeightOneSpectrum (𝓞 Kf.1)).adicCompletion Kf.1]
        AlgebraicClosure ((v : HeightOneSpectrum (𝓞 Kf.1)).adicCompletion Kf.1)) ≃* Dec (F := Kf.1) A)
    (hev : ∀ σ x, ιs v (((ev σ : Dec (F := Kf.1) A) : G Kf.1 (AlgebraicClosure ℚ)) x) = σ (ιs v x))
    (w : rootsOfUnity (l ^ r) (maxUnramifiedOutside Kf.1 (AlgebraicClosure ℚ) S))
    (hwQ : ((((w : (maxUnramifiedOutside Kf.1 (AlgebraicClosure ℚ) S)ˣ) : maxUnramifiedOutside Kf.1 (AlgebraicClosure ℚ) S)) : AlgebraicClosure ℚ) = ζ) (σ : (AlgebraicClosure ((v : HeightOneSpectrum (𝓞 Kf.1)).adicCompletion Kf.1) ≃ₐ[
        (v : HeightOneSpectrum (𝓞 Kf.1)).adicCompletion Kf.1]
        AlgebraicClosure ((v : HeightOneSpectrum (𝓞 Kf.1)).adicCompletion Kf.1))) (c : ZMod (l ^ r)) :
    (gsRoots S (l ^ r)).ρ (gsFinFamily S ιs v σ) (rootOf w c) =
      rootOf w (((cycMod Kf.1 (AlgebraicClosure ℚ) l r (ev σ : Dec (F := Kf.1) A) : (ZMod (l ^ r))ˣ) :
        ZMod (l ^ r)) * c) := by
  have hζN : ζ ^ (l ^ r) = 1 := hζ.pow_eq_one
  have hmod : ∀ k : ℕ, ζ ^ (k % (l ^ r)) = ζ ^ k := fun k => by
    conv_rhs => rw [← Nat.mod_add_div k (l ^ r), pow_add, pow_mul, hζN, one_pow, mul_one]
  have hτ : ((ev σ : Dec (F := Kf.1) A) : G Kf.1 (AlgebraicClosure ℚ)) ζ =
      ζ ^ ((cycMod Kf.1 (AlgebraicClosure ℚ) l r (ev σ : Dec (F := Kf.1) A) : (ZMod (l ^ r))ˣ) :
        ZMod (l ^ r)).val :=
    cyclotomicCharacter.spec (L := AlgebraicClosure ℚ) l
      (MulSemiringAction.toRingAut (G Kf.1 (AlgebraicClosure ℚ)) (AlgebraicClosure ℚ)
        (ev σ : Dec (F := Kf.1) A)) ζ hζN
  have hact : ∀ y : maxUnramifiedOutside Kf.1 (AlgebraicClosure ℚ) S,
      ((gsFinFamily S ιs v σ y : maxUnramifiedOutside Kf.1 (AlgebraicClosure ℚ) S) : AlgebraicClosure ℚ) =
        ((ev σ : Dec (F := Kf.1) A) : G Kf.1 (AlgebraicClosure ℚ)) (y : AlgebraicClosure ℚ) := by
    intro y
    apply (ιs v).toRingHom.injective
    show ιs v _ = ιs v _
    rw [gsFinFamily_apply, hev]
  apply Additive.toMul.injective
  apply Subtype.ext
  apply Units.ext
  apply Subtype.ext
  show ((gsFinFamily S ιs v σ ((((w ^ c.val : rootsOfUnity (l ^ r) (maxUnramifiedOutside Kf.1 (AlgebraicClosure ℚ) S)) : (maxUnramifiedOutside Kf.1 (AlgebraicClosure ℚ) S)ˣ) : maxUnramifiedOutside Kf.1 (AlgebraicClosure ℚ) S)) :
      maxUnramifiedOutside Kf.1 (AlgebraicClosure ℚ) S) : AlgebraicClosure ℚ) =
    ((((w ^ (((cycMod Kf.1 (AlgebraicClosure ℚ) l r (ev σ : Dec (F := Kf.1) A) : (ZMod (l ^ r))ˣ) :
      ZMod (l ^ r)) * c).val : rootsOfUnity (l ^ r) (maxUnramifiedOutside Kf.1 (AlgebraicClosure ℚ) S)) : (maxUnramifiedOutside Kf.1 (AlgebraicClosure ℚ) S)ˣ) : maxUnramifiedOutside Kf.1 (AlgebraicClosure ℚ) S) : AlgebraicClosure ℚ)
  rw [hact]
  simp only [SubgroupClass.coe_pow, Units.val_pow_eq_pow_val, IntermediateField.coe_pow, hwQ, map_pow, hτ]
  rw [← pow_mul, ZMod.val_mul, hmod]

theorem eq_rootOf_of_coe {Kf : FiniteSubfield} {S : Set (HeightOneSpectrum (𝓞 Kf.1))} {l r : ℕ}
    [NeZero (l ^ r)] {ζ : AlgebraicClosure ℚ} {w : rootsOfUnity (l ^ r) (maxUnramifiedOutside Kf.1 (AlgebraicClosure ℚ) S)}
    (hwQ : ((((w : (maxUnramifiedOutside Kf.1 (AlgebraicClosure ℚ) S)ˣ) : maxUnramifiedOutside Kf.1 (AlgebraicClosure ℚ) S)) : AlgebraicClosure ℚ) = ζ)
    (a : Additive (rootsOfUnity (l ^ r) (maxUnramifiedOutside Kf.1 (AlgebraicClosure ℚ) S))) (c : ZMod (l ^ r))
    (h : ((((Additive.toMul a : rootsOfUnity (l ^ r) (maxUnramifiedOutside Kf.1 (AlgebraicClosure ℚ) S)) : (maxUnramifiedOutside Kf.1 (AlgebraicClosure ℚ) S)ˣ) : maxUnramifiedOutside Kf.1 (AlgebraicClosure ℚ) S) :
      AlgebraicClosure ℚ) = ζ ^ c.val) : a = rootOf w c := by
  apply Additive.toMul.injective
  apply Subtype.ext
  apply Units.ext
  apply Subtype.ext
  rw [h]
  show ζ ^ c.val = ((((w ^ c.val : rootsOfUnity (l ^ r) (maxUnramifiedOutside Kf.1 (AlgebraicClosure ℚ) S)) : (maxUnramifiedOutside Kf.1 (AlgebraicClosure ℚ) S)ˣ) : maxUnramifiedOutside Kf.1 (AlgebraicClosure ℚ) S) : AlgebraicClosure ℚ)
  rw [SubgroupClass.coe_pow, Units.val_pow_eq_pow_val, IntermediateField.coe_pow, hwQ]

theorem cls_nsmul_of_match {L D : Type} [Group L] [TopologicalSpace L] [IsTopologicalGroup L]
    [Group D] [TopologicalSpace D] [IsTopologicalGroup D] (ψ : L →* D) (hψ : Continuous ψ)
    {R M : Type} [CommRing R] [AddCommGroup M] [Module R M] [TopologicalSpace M] [DiscreteTopology M]
    (rho0 : Representation R D M) (A : Rep.{0} (ULift.{0} ℤ) L) [IsDiscreteRep A] (e : M ≃+ A.V)
    (he : ∀ g m, e ((rho0.comp ψ) g m) = A.ρ g (e m)) (z z' : Z2 rho0) (x x' : cocycles A 2)
    (hzx : ∀ s, cochainOf A (cocycleι A 2 x) s = e (z.1 (ψ (s 0), ψ (s 1))))
    (hzx' : ∀ s, cochainOf A (cocycleι A 2 x') s = e (z'.1 (ψ (s 0), ψ (s 1)))) (n : ℕ)
    (h : (Submodule.Quotient.mk z : H2 rho0) = n • Submodule.Quotient.mk z') :
    cohomologyπ A 2 x = n • cohomologyπ A 2 x' := by
  obtain ⟨e2, -, hchar⟩ := PositivityTheory.LocalTateOrthogonality.Gcoh.gc2 L R M (rho0.comp ψ) A e he
  have h' : resH2 rho0 ψ hψ (Submodule.Quotient.mk z) = n • resH2 rho0 ψ hψ (Submodule.Quotient.mk z') := by
    rw [h, map_nsmul]
  rw [← hchar (restrictCocycles2 rho0 ψ hψ z) x hzx, ← hchar (restrictCocycles2 rho0 ψ hψ z') x' hzx']
  exact (congrArg e2 h').trans (map_nsmul e2 n _)


set_option maxHeartbeats 1000000 in
theorem invMatch_nsmul_B (Kf : FiniteSubfield) [NumberField Kf.1] [IsAlgClosure Kf.1 (AlgebraicClosure ℚ)]
    (S : Set (HeightOneSpectrum (𝓞 Kf.1))) [Fintype S] {l r : ℕ} [Fact l.Prime] (hr : 0 < r)
    (hS : ∀ v : HeightOneSpectrum (𝓞 Kf.1), ((l : ℕ) : 𝓞 Kf.1) ∈ v.asIdeal → v ∈ S)
    (ζ : AlgebraicClosure ℚ) (hζ : IsPrimitiveRoot ζ (l ^ r))
    (inv : InvFam Kf.1 (AlgebraicClosure ℚ) l r) (hinv : InvNormalised ζ inv)
    (ιs : ∀ v : S, AlgebraicClosure ℚ →ₐ[Kf.1]
      AlgebraicClosure ((v : HeightOneSpectrum (𝓞 Kf.1)).adicCompletion Kf.1))
    (v : S) (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : IsPlaceOver A v.1)
    (ev : (AlgebraicClosure ((v : HeightOneSpectrum (𝓞 Kf.1)).adicCompletion Kf.1) ≃ₐ[
        (v : HeightOneSpectrum (𝓞 Kf.1)).adicCompletion Kf.1]
        AlgebraicClosure ((v : HeightOneSpectrum (𝓞 Kf.1)).adicCompletion Kf.1)) ≃* Dec (F := Kf.1) A)
    (hev : ∀ σ x, ιs v (((ev σ : Dec (F := Kf.1) A) : G Kf.1 (AlgebraicClosure ℚ)) x) = σ (ιs v x))

    (hevc : Continuous ev) (z z' : Z2 (muLoc Kf.1 l r A)) (x x' : cocycles (Rep.res (gsFinFamily S ιs v).toMonoidHom (gsRoots S (l ^ r))) 2)
    (hzx : (∀ s : Fin 2 → (AlgebraicClosure ((v : HeightOneSpectrum (𝓞 Kf.1)).adicCompletion Kf.1) ≃ₐ[
        (v : HeightOneSpectrum (𝓞 Kf.1)).adicCompletion Kf.1]
        AlgebraicClosure ((v : HeightOneSpectrum (𝓞 Kf.1)).adicCompletion Kf.1)), ((((Additive.toMul (cochainOf _ (cocycleι _ 2 x) s) :
          rootsOfUnity (l ^ r) (maxUnramifiedOutside Kf.1 (AlgebraicClosure ℚ) S)) :
          (maxUnramifiedOutside Kf.1 (AlgebraicClosure ℚ) S)ˣ) :
          maxUnramifiedOutside Kf.1 (AlgebraicClosure ℚ) S) : AlgebraicClosure ℚ) = ζ ^ (z.1 (ev (s 0), ev (s 1))).val)) (hzx' : (∀ s : Fin 2 → (AlgebraicClosure ((v : HeightOneSpectrum (𝓞 Kf.1)).adicCompletion Kf.1) ≃ₐ[
        (v : HeightOneSpectrum (𝓞 Kf.1)).adicCompletion Kf.1]
        AlgebraicClosure ((v : HeightOneSpectrum (𝓞 Kf.1)).adicCompletion Kf.1)), ((((Additive.toMul (cochainOf _ (cocycleι _ 2 x') s) :
          rootsOfUnity (l ^ r) (maxUnramifiedOutside Kf.1 (AlgebraicClosure ℚ) S)) :
          (maxUnramifiedOutside Kf.1 (AlgebraicClosure ℚ) S)ˣ) :
          maxUnramifiedOutside Kf.1 (AlgebraicClosure ℚ) S) : AlgebraicClosure ℚ) = ζ ^ (z'.1 (ev (s 0), ev (s 1))).val)) (n : ℕ)
    (h : (Submodule.Quotient.mk z : H2 (muLoc Kf.1 l r A)) = n • Submodule.Quotient.mk z') :
    cohomologyπ _ 2 x = n • cohomologyπ _ 2 x' := by
  classical
  haveI : NeZero (l ^ r) := ⟨pow_ne_zero r (Fact.out : l.Prime).ne_zero⟩
  have hmem : ζ ∈ maxUnramifiedOutside Kf.1 (AlgebraicClosure ℚ) S := by
    haveI : IsGalois Kf.1 (AlgebraicClosure ℚ) := IsAlgClosure.isGalois _ _
    refine mem_maxUnramifiedOutside_of_pow_eq_one S (pow_ne_zero r (Fact.out : l.Prime).ne_zero) ?_
      hζ.pow_eq_one
    intro w hw hm
    apply hw
    apply hS
    have h' : ((l : 𝓞 Kf.1)) ^ r ∈ w.asIdeal := by simpa [Nat.cast_pow] using hm
    exact w.isPrime.mem_of_pow_mem r h'
  have hζK : IsPrimitiveRoot (⟨ζ, hmem⟩ : maxUnramifiedOutside Kf.1 (AlgebraicClosure ℚ) S) (l ^ r) :=
    IsPrimitiveRoot.of_map_of_injective (f := (maxUnramifiedOutside Kf.1 (AlgebraicClosure ℚ) S).val) hζ (maxUnramifiedOutside Kf.1 (AlgebraicClosure ℚ) S).val.toRingHom.injective
  have hex := exists_root_of_primitive (L := ↥(maxUnramifiedOutside Kf.1 (AlgebraicClosure ℚ) S)) (N := l ^ r)
    (pow_ne_zero r (Fact.out : l.Prime).ne_zero) hζK
  obtain ⟨w, hwv⟩ := hex
  have hw : IsPrimitiveRoot (((w : (maxUnramifiedOutside Kf.1 (AlgebraicClosure ℚ) S)ˣ) : maxUnramifiedOutside Kf.1 (AlgebraicClosure ℚ) S)) (l ^ r) := by
    rw [hwv]; exact hζK
  have hwQ : ((((w : (maxUnramifiedOutside Kf.1 (AlgebraicClosure ℚ) S)ˣ) : maxUnramifiedOutside Kf.1 (AlgebraicClosure ℚ) S)) : AlgebraicClosure ℚ) = ζ := congrArg Subtype.val hwv
  let eA : ZMod (l ^ r) ≃+ (Rep.res (gsFinFamily S ιs v).toMonoidHom (gsRoots S (l ^ r))).V :=
    AddEquiv.ofBijective (rootOf w) (rootOf_bijective w hw)
  have hM : ∀ g m, eA (((muLoc Kf.1 l r A).comp ev.toMonoidHom) g m) =
      (Rep.res (gsFinFamily S ιs v).toMonoidHom (gsRoots S (l ^ r))).ρ g (eA m) := fun g m => by
    show rootOf w (((cycMod Kf.1 (AlgebraicClosure ℚ) l r (ev g : Dec (F := Kf.1) A) : (ZMod (l ^ r))ˣ) :
        ZMod (l ^ r)) * m) = (gsRoots S (l ^ r)).ρ (gsFinFamily S ιs v g) (rootOf w m)
    exact (loc_act_rootOf Kf S ζ hζ ιs v A ev hev w hwQ g m).symm
  exact cls_nsmul_of_match ev.toMonoidHom hevc (muLoc Kf.1 l r A)
    (Rep.res (gsFinFamily S ιs v).toMonoidHom (gsRoots S (l ^ r))) eA hM z z' x x'
    (fun s => eq_rootOf_of_coe hwQ _ _ (hzx s)) (fun s => eq_rootOf_of_coe hwQ _ _ (hzx' s)) n h

end PositivityTheory.Lit1.PTN
end
end

-- bundled from Development.WeilBound.CoreStatements.PublishedTheorems.PoitouTateDuality.PtfsShaDict
section
noncomputable section

open NumberField IsDedekindDomain Representation Formalism.ConjugateSelfDual ReciprocityTheory.Gal GroundTheory.ProfCoh CategoryTheory

namespace PositivityTheory.Lit1.PTN

theorem addEquiv_of_resCmp {R ι H C : Type} [CommRing R] [AddCommGroup H] [Module R H]
    [AddCommGroup C] {Hv Cv : ι → Type} [∀ v, AddCommGroup (Hv v)] [∀ v, AddCommGroup (Cv v)]
    (res : ∀ v, H →+ Hv v) (pres : ∀ v, C →+ Cv v) (E : H ≃+ C) (Ev : ∀ v, Hv v ≃+ Cv v)
    (h : ∀ v x, Ev v (res v x) = pres v (E x)) (U : Submodule R H) (T : AddSubgroup C)
    (hU : ∀ x, x ∈ U ↔ ∀ v, res v x = 0) (hT : ∀ y, y ∈ T ↔ ∀ v, pres v y = 0) :
    Nonempty (U ≃+ T) :=
  _root_.UpperTheory.Reformulated.B.LocallyTrivialClassesAddEquiv.main res pres E Ev h U T hU hT

section FoundSide

attribute [local instance 2000] Rep.hV2

theorem mem_ptSha_iff' {G ι : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    {Hv : ι → Type} [∀ v, Group (Hv v)] [∀ v, TopologicalSpace (Hv v)]
    [∀ v, IsTopologicalGroup (Hv v)] (φ : ∀ v, Hv v →ₜ* G) (A : Rep.{0} (ULift.{0} ℤ) G)
    [IsDiscreteRep A] (n : ℕ) (x : cohomology A n) : x ∈ ptSha φ A n ↔ ∀ v, ptRes φ A v n x = 0 := by
  rw [mem_ptSha, funext_iff]
  rfl

set_option maxHeartbeats 1000000 in
theorem shaIso_of_rep (K : IntermediateField ℚ (AlgebraicClosure ℚ)) [NumberField K]
    (S : Finset (HeightOneSpectrum (𝓞 K))) (Av : S → ValuationSubring (AlgebraicClosure ℚ))
    (e : GS (AlgebraicClosure ℚ) (S : Set (HeightOneSpectrum (𝓞 K))) ≃ₜ*
        galUnramifiedOutside K (AlgebraicClosure ℚ) (S : Set (HeightOneSpectrum (𝓞 K))))
    (ιs : ∀ v : (S : Set (HeightOneSpectrum (𝓞 K))), AlgebraicClosure ℚ →ₐ[K]
        AlgebraicClosure ((v : HeightOneSpectrum (𝓞 K)).adicCompletion K))
    (ev : ∀ v : S, (AlgebraicClosure ((v : HeightOneSpectrum (𝓞 K)).adicCompletion K) ≃ₐ[
          (v : HeightOneSpectrum (𝓞 K)).adicCompletion K]
          AlgebraicClosure ((v : HeightOneSpectrum (𝓞 K)).adicCompletion K)) ≃* Dec (F := K) (Av v))
    (hevc : ∀ v, Continuous (ev v) ∧ Continuous (ev v).symm)
    (hev : ∀ (v : S) σ, e (locFam S Av v (ev v σ)) =
        gsFinFamily (S : Set (HeightOneSpectrum (𝓞 K))) ιs ⟨v.1, Finset.mem_coe.2 v.2⟩ σ)
    {R M : Type} [CommRing R] [AddCommGroup M] [Module R M] [TopologicalSpace M]
    [DiscreteTopology M] (rho : Representation R (GS (AlgebraicClosure ℚ) (S : Set (HeightOneSpectrum (𝓞 K)))) M)
    (hc : ContAction rho)
    (A : Rep.{0} (ULift.{0} ℤ) (galUnramifiedOutside K (AlgebraicClosure ℚ) (S : Set (HeightOneSpectrum (𝓞 K)))))
    [IsDiscreteRep A] (eM : M ≃+ A.V) (hM : ∀ g m, eM (rho g m) = A.ρ (e g) (eM m)) :
    Nonempty (Sha1 rho (locFam S Av) (continuous_locFam S Av) ≃+
        ptSha (gsFinFamily (S : Set (HeightOneSpectrum (𝓞 K))) ιs) A 1) ∧
    Nonempty (Sha2 rho (locFam S Av) (continuous_locFam S Av) ≃+
        ptSha (gsFinFamily (S : Set (HeightOneSpectrum (𝓞 K))) ιs) A 2) := by
  have hT : ∀ n (y : cohomology A n), y ∈ ptSha (gsFinFamily (S : Set (HeightOneSpectrum (𝓞 K))) ιs) A n ↔
      ∀ v : S, ptRes (fun v : S => gsFinFamily (S : Set (HeightOneSpectrum (𝓞 K))) ιs ⟨v.1, Finset.mem_coe.2 v.2⟩) A v n y = 0 := by
    intro n y
    exact (mem_ptSha_iff' (gsFinFamily (S : Set (HeightOneSpectrum (𝓞 K))) ιs) A n y).trans
      ⟨fun h v => h ⟨v.1, Finset.mem_coe.2 v.2⟩, fun h w => h ⟨w.1, Finset.mem_coe.1 w.2⟩⟩
  obtain ⟨E1, Ev1, h1⟩ := resCmp1' e (locFam S Av) (continuous_locFam S Av)
    (fun v : S => gsFinFamily (S : Set (HeightOneSpectrum (𝓞 K))) ιs ⟨v.1, Finset.mem_coe.2 v.2⟩) ev (fun v => (hevc v).1) (fun v => (hevc v).2) hev rho hc A eM hM
  obtain ⟨E2, Ev2, h2⟩ := resCmp2B e (locFam S Av) (continuous_locFam S Av)
    (fun v : S => gsFinFamily (S : Set (HeightOneSpectrum (𝓞 K))) ιs ⟨v.1, Finset.mem_coe.2 v.2⟩) ev (fun v => (hevc v).1) (fun v => (hevc v).2) hev rho hc A eM hM
  have hU1 : ∀ x, x ∈ Sha1 rho (locFam S Av) (continuous_locFam S Av) ↔
      ∀ v, (resH1 rho (locFam S Av v) (continuous_locFam S Av v)).toAddMonoidHom x = 0 := by
    intro x
    simp only [Sha1, Submodule.mem_iInf, LinearMap.mem_ker]
    rfl
  have hU2 : ∀ x, x ∈ Sha2 rho (locFam S Av) (continuous_locFam S Av) ↔
      ∀ v, (resH2 rho (locFam S Av v) (continuous_locFam S Av v)).toAddMonoidHom x = 0 := by
    intro x
    simp only [Sha2, Submodule.mem_iInf, LinearMap.mem_ker]
    rfl
  exact ⟨addEquiv_of_resCmp
      (fun v => (resH1 rho (locFam S Av v) (continuous_locFam S Av v)).toAddMonoidHom)
      (fun v => ptRes (fun v : S => gsFinFamily (S : Set (HeightOneSpectrum (𝓞 K))) ιs ⟨v.1, Finset.mem_coe.2 v.2⟩) A v 1) E1 Ev1 h1 _ _ hU1 (hT 1),
    addEquiv_of_resCmp
      (fun v => (resH2 rho (locFam S Av v) (continuous_locFam S Av v)).toAddMonoidHom)
      (fun v => ptRes (fun v : S => gsFinFamily (S : Set (HeightOneSpectrum (𝓞 K))) ιs ⟨v.1, Finset.mem_coe.2 v.2⟩) A v 2) E2 Ev2 h2 _ _ hU2 (hT 2)⟩

end FoundSide

end PositivityTheory.Lit1.PTN
end
end

