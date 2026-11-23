module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.DiscreteSeriesCoefficientsCuspidal
public import Development.AutomorphicArithmetic.AutomorphicVarieties.TheoremsMuLinked.GaloisRepresentationTypes.Bundle0003
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.Bundle0006
public import Development.AutomorphicArithmetic.AutomorphicVarieties.UnitaryThreeGroups.AdmissibleOfTypeII
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.AutomorphyLifting.AutomorphyDescent.AutNewformW
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.Hypotheses2
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.Bundle0003
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.RankTwoPatching.GaloisRepExistsTotallyRealGL2
public import Development.AutomorphicArithmetic.AutomorphicVarieties.HeckeAlgebras.OrdinaryHeckeCharacters.Bundle0014
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.Bundle0008
public import Development.AutomorphicArithmetic.Foundations.LocalLanglands.IsRecTOfIsRec

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.AdLOf
section
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 200000

section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal IsLocalRing Polynomial UpperTheory.V UpperTheory.V.HV GlobalTheory.GalOfCusp UpperTheory.V.Th
private theorem adL_conj {C G V : Type} [CommRing C] [Group G] [AddCommGroup V] [Module C V] (ρ : Representation C G V)
    (c : G → V) (hc : ∀ g h, c (g * h) = c g + ρ g (c h)) (γ g : G) :
    c g = ρ γ (c (γ⁻¹ * g * γ)) + c γ - ρ g (c γ) := by
  have h1 := hc γ (γ⁻¹ * g * γ)
  rw [← mul_assoc, mul_inv_cancel_left, hc] at h1
  rw [eq_sub_iff_add_eq, h1, add_comm]
private theorem adL_rho {C G V : Type} [CommRing C] [Group G] [AddCommGroup V] [Module C V] (ρ : Representation C G V)
    (γ g : G) (x : V) : ρ γ (ρ (γ⁻¹ * g * γ) x) = ρ g (ρ γ x) := by
  rw [← Module.End.mul_apply, ← map_mul, ← mul_assoc, mul_inv_cancel_left, map_mul, Module.End.mul_apply]
private theorem adL_emb {F Ω K : Type} [Field F] [Field Ω] [Field K] [CharZero F] [Algebra F Ω] [IsAlgClosure F Ω]
    (j j₀ : Ω →+* K) (h : j₀.comp (algebraMap F Ω) = j.comp (algebraMap F Ω)) :
    ∃ γ : Ω ≃ₐ[F] Ω, ∀ y, j (γ y) = j₀ y := by
  letI : Algebra F K := (j.comp (algebraMap F Ω)).toAlgebra
  letI : Algebra Ω K := j.toAlgebra
  haveI : IsScalarTower F Ω K := IsScalarTower.of_algebraMap_eq' rfl
  let f : Ω →ₐ[F] K := { j₀ with commutes' := fun x => RingHom.congr_fun h x }
  exact ⟨f.restrictNormal' Ω, fun y => f.restrictNormal_commutes Ω y⟩
private theorem adL_above {F Ω : Type} [Field F] [NumberField F] [Field Ω] [CharZero Ω] [Algebra F Ω] [IsAlgClosure F Ω]
    {l : ℕ} [Fact l.Prime] (j : Ω →+* Formalism.BasicNotions.Loc.Om l) {H : Type} [Group H] [TopologicalSpace H] [IsTopologicalGroup H]
    (φ : H →* Formalism.BasicNotions.Loc.GQ l) (ψ : H →* G F Ω) (hφ : Topology.IsOpenEmbedding φ) (hψ : Continuous ψ)
    (hj : ∀ h y, φ h (j y) = j (ψ h y))
    {C V : Type} [CommRing C] [Algebra ℚ_[l] C] [AddCommGroup V] [Module C V] [Module ℚ_[l] V] [IsScalarTower ℚ_[l] C V]
    [TopologicalSpace V] [IsTopologicalAddGroup V] [ContinuousConstSMul C V] (ρ : Representation C (G F Ω) V)
    (c : G F Ω → V) (hc : c ∈ Z1 ρ) (hb : Af.IsBK l ρ c) : (fun h => c (ψ h)) ∈ Loc.finiteCocycles φ (ρ.comp ψ) := by
  obtain ⟨j₀, hj₀, h0⟩ := hb.above (j.comp (algebraMap F Ω))
  obtain ⟨γ, hγ⟩ := adL_emb j j₀ hj₀
  let ψ' : H →* G F Ω := (MulAut.conj (γ⁻¹ : G F Ω)).toMonoidHom.comp ψ
  have hψ' : ∀ h, ψ' h = γ⁻¹ * ψ h * γ := fun h => by simp [ψ']
  obtain ⟨-, x, hx⟩ := (Loc.bkAbove (F := F) j₀ φ ψ' hφ (fun h y => by
    rw [← hγ, hj, ← hγ, hψ']
    simp) ρ c hc).2 h0
  refine ⟨⟨hc.1.comp hψ, fun g h => (congrArg c (map_mul ψ g h)).trans (hc.2 _ _)⟩,
    TensorProduct.AlgebraTensorModule.map (ρ γ) LinearMap.id x - c γ ⊗ₜ[ℚ_[l]] 1, fun h => ?_⟩
  have e : ∀ w, TensorProduct.AlgebraTensorModule.map (ρ γ) LinearMap.id (Loc.actC φ (ρ.comp ψ') h w) =
      Loc.actC φ (ρ.comp ψ) h (TensorProduct.AlgebraTensorModule.map (ρ γ) LinearMap.id w) := fun w => by
    induction w using TensorProduct.induction_on with
    | zero => simp
    | tmul v b =>
      simp only [Loc.actC, TensorProduct.AlgebraTensorModule.map_tmul, MonoidHom.comp_apply, hψ', adL_rho, LinearMap.id_apply]
    | add u v hu hv => simp only [map_add (f := _), hu, hv]
  have h2 := congrArg (TensorProduct.AlgebraTensorModule.map (ρ γ) LinearMap.id) (hx h)
  rw [map_sub, e, TensorProduct.AlgebraTensorModule.map_tmul] at h2
  have h3 : Loc.actC φ (ρ.comp ψ) h (c γ ⊗ₜ[ℚ_[l]] 1) = ρ (ψ h) (c γ) ⊗ₜ[ℚ_[l]] 1 := by simp [Loc.actC]
  change c (ψ h) ⊗ₜ[ℚ_[l]] _ = _
  rw [adL_conj ρ c hc.2 γ (ψ h), TensorProduct.sub_tmul, TensorProduct.add_tmul, map_sub, h3]
  simp only [LinearMap.id_apply, hψ'] at h2
  rw [h2]
  abel
open scoped Pointwise in
private theorem adL_ine {F Ω : Type} [Field F] [NumberField F] [Field Ω] [Algebra F Ω] {A : ValuationSubring Ω} (γ : G F Ω)
    {g : G F Ω} (hg : g ∈ Ine (F := F) (γ • A)) : γ⁻¹ * g * γ ∈ Ine (F := F) A := by
  have m : ∀ y : Ω, γ y ∈ γ • A ↔ y ∈ A := fun y => ValuationSubring.smul_mem_pointwise_smul_iff (g := γ)
  refine ⟨?_, fun x hx => ?_⟩
  · have h1 : g • γ • A = γ • A := hg.1
    change (γ⁻¹ * g * γ) • A = A
    rw [mul_smul, mul_smul, h1, inv_smul_smul]
  · have h2 := hg.2 (γ x) (by rwa [ValuationSubring.valuation_le_one_iff, m, ← ValuationSubring.valuation_le_one_iff])
    have e : g (γ x) - γ x = γ ((γ⁻¹ * g * γ) x - x) := by simp
    rwa [e, valuation_lt_one_iff', m, ← map_inv₀, m, map_eq_zero_iff _ γ.injective, ← valuation_lt_one_iff'] at h2
private theorem adL_away {F Ω : Type} [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω]
    {l : ℕ} [Fact l.Prime]
    {C V : Type} [CommRing C] [Algebra ℚ_[l] C] [AddCommGroup V] [Module C V] [Module ℚ_[l] V] [IsScalarTower ℚ_[l] C V]
    [TopologicalSpace V] [IsTopologicalAddGroup V] [ContinuousConstSMul C V] (ρ : Representation C (G F Ω) V)
    (c : G F Ω → V) (hc : c ∈ Z1 ρ) (hb : Af.IsBK l ρ c) (w : HeightOneSpectrum (𝓞 F)) (hw : ((l : ℕ) : 𝓞 F) ∉ w.asIdeal)
    (A : ValuationSubring Ω) (hA : IsPlaceOver A w) : ∃ x : V, ∀ g ∈ Ine (F := F) A, c g = ρ g x - x := by
  obtain ⟨A₀, hA₀, x, hx⟩ := hb.away w hw
  obtain ⟨γ, rfl⟩ := exists_smul_eq_of_isPlaceOver (F := F) hA₀ hA
  refine ⟨ρ γ x - c γ, fun g hg => ?_⟩
  rw [adL_conj ρ c hc.2 γ g, hx _ (adL_ine γ hg), map_sub, adL_rho, map_sub]
  abel
private theorem adL_pr {l : ℕ} [Fact l.Prime] {L Ω : Type} [Field L] [NumberField L] [IsCMField L] [Field Ω] [Algebra L Ω]
    [IsAlgClosure L Ω] {s : W.HidaSetting l L Ω} (V : s.Lev) : Function.Surjective V.pr := fun g => by
  obtain ⟨τ, hτ⟩ : ∃ τ, toGS Ω V.S' τ = g.1 := QuotientGroup.mk_surjective g.1
  obtain ⟨σ, rfl⟩ := (V.hη τ).1 (by rw [hτ]; exact g.2)
  exact ⟨σ, Subtype.ext hτ⟩
private theorem adL_desc {n : ℕ} {A G H : Type} [CommRing A] [Group G] [Group H] (D : W.GDet n A G) (φ : H →* G)
    (hφ : Function.Surjective φ) (ρ : G →* GL (Fin n) A) (hD : D.comap φ = W.GDet.ofRep (W.mat (ρ.comp φ))) :
    D = W.GDet.ofRep (W.mat ρ) := by
  refine CA.d_gext _ _ fun g i _ _ => ?_
  obtain ⟨h, rfl⟩ := hφ g
  have e : (D.comap φ).chi (MonoidAlgebra.single h 1) = D.chi (MonoidAlgebra.single (φ h) 1) := by
    change D.D A[X] (MonoidAlgebra.mapDomainRingHom A[X] φ _) = D.D A[X] _
    congr 1
    rw [map_sub]
    simp
  unfold W.GDet.lam
  rw [← e, hD, (AlgebraTools.Det.repApi _).2.1, (AlgebraTools.Det.repApi _).2.1]
  rfl
private theorem adL_triv {l : ℕ} [Fact l.Prime] {L Ω : Type} [Field L] [NumberField L] [IsCMField L] [Field Ω] [Algebra L Ω]
    [IsAlgClosure L Ω] {s : W.HidaSetting l L Ω} {V : s.Lev} {c : Coef l} {n : ℕ} {r : W.Resid V.frame c.O n} {B : W.UniversalOrdinaryDeterminantRing r}
    {ι : Qbar l ≃+* ℂ} {x : B.Pt} {ρ : V.frame.G₀ →* GL (Fin n) (Qbar l)} (H : _root_.UpperTheory.V.Th.AutomorphicPointLocallyGeneric ι x ρ) :
    ∀ u, ∀ g ∈ r.Ip u, ρ g = 1 :=
  (Ws.Eb.relKill B x ρ ((AlgebraTools.Det.irrIffSpan (W.mat ρ)).1 fun N hN => H.irr N fun g _ v hv => hN g v hv)
    (adL_desc x.D V.pr (adL_pr V) ρ H.rep)).2
theorem UpperTheory.V.Th.adjointLiftingTheorem_of_locPrints_of_core :
    Loc.LocalPublishedTheorems → _root_.UpperTheory.V.Th.DenseThresholdMainCase → _root_.UpperTheory.V.Th.AdjointLiftingTheorem := by
  intro hP hC l _ L Ω _ _ _ _ _ _ s V hS hζ c hL n hn hn' r hr B ι x ρ H hpar P R hform hR z hz hb
  haveI : CharZero Ω := charZero_of_injective_algebraMap (algebraMap L Ω).injective
  have hz' : (fun g => z (toGS Ω V.S' g)) ∈ Z1 (R.comp (toGS Ω V.S') :
      Representation (Qbar l) (G (W.Lp L) Ω) (Matrix (Fin n) (Fin n) (Qbar l))) :=
    ⟨hz.1.comp (continuous_toGS Ω _), fun g h => (congrArg z (map_mul _ g h)).trans (hz.2 _ _)⟩
  have he : V.frame.eps c.O (Qbar l) = V.frame.eps ℤ_[l] (Qbar l) := by
    unfold W.GFrame.eps
    rw [← IsScalarTower.algebraMap_eq, ← IsScalarTower.algebraMap_eq]
  refine hC l L Ω s V hS hζ c hL n hn hn' r hr B ι x ρ H P R (fun g => he ▸ hform g) hR z hz ⟨fun u g hg => ?_, fun v => ?_⟩
  · obtain ⟨X, hX⟩ := adL_away _ _ hz' hb u.1 (s.St_l u.1 u.2) (s.A u.1) (s.hA u.1)
    have h1 := adL_triv H u g hg
    obtain ⟨g', hg', rfl⟩ := hg.1
    have h2 := hX (W.resP L Ω g') hg'
    have h3 : ∀ g : V.frame.G₀, ρ g = 1 → Loc.adGL ρ g X = X := fun g h => by simp [Loc.adGL, h]
    exact h2.trans (sub_eq_zero.2 ((hR.ad (V.pr g') X).trans (h3 _ h1)))
  · obtain ⟨j, hj⟩ := (Loc.decEmb (F := W.Lp L) (Ω := Ω) (v := l)).1 (s.A v.1) v.1 (s.hA v.1) v.2
    have key : ∃ φ : ↥(Dec (F := L) (s.A v.1)) →* Formalism.BasicNotions.Loc.GQ l, Topology.IsOpenEmbedding φ ∧
        (∀ g y, φ g (j y) = j ((g : G L Ω) y)) ∧ (∀ g, φ g ∈ Loc.Iq l ↔ (g : G L Ω) ∈ Ine (F := L) (s.A v.1)) ∧
        (∀ g, Loc.cyc l l (φ g) = cycZ L Ω l (g : G L Ω)) := by
      rw [← hj]
      obtain ⟨φ, a, b, -, c, d, -⟩ := ((Loc.decEmb (F := L) (Ω := Ω) (v := l)).2 j).2
      exact ⟨φ, a, b, c, d l⟩
    obtain ⟨φ, a, b, hi, d⟩ := key
    have d' : ∀ g, Loc.cycA l l (Qbar l) (φ g) = cycBar L Ω l (g : G L Ω) := fun g => congrArg (Units.map _) (d g)
    have h3 := adL_above (F := W.Lp L) j φ ((W.resP L Ω).comp (Dec (F := L) (s.A v.1)).subtype) a
      (W.continuous_resP.comp continuous_subtype_val) b _ _ hz' hb
    have e : ((R.comp (toGS Ω V.S')).comp ((W.resP L Ω).comp (Dec (F := L) (s.A v.1)).subtype) :
        Representation (Qbar l) (Dec (F := L) (s.A v.1)) (Matrix (Fin n) (Fin n) (Qbar l))) =
        Loc.adGL (ρ.comp (V.frame.φ v)) :=
      MonoidHom.ext fun g => LinearMap.ext fun X => hR.ad (V.frame.φ v g) X
    rw [e] at h3
    obtain ⟨m, k, hm, hk, hψ⟩ := hpar v
    obtain ⟨g₀, hg₀, hf⟩ := H.free v
    have hI : V.frame.Iv v = (Loc.Iq l).comap φ := Subgroup.ext fun g => (hi g).symm
    rw [hI]
    haveI : CompactSpace (Dec (F := L) (s.A v.1)) := V.frame.cv v
    refine bkOrd hP l (Dec (F := L) (s.A v.1)) φ a n _ _ m k (H.cont.comp (V.frame.φ_cont v)) (H.flag v) hm hk
      (fun i i' g hg => ?_) ⟨g₀, ?_, hf⟩ _ h3
    · rw [d']
      exact hψ i i' g ((hi g).1 hg)
    · have h4 : cycZ (W.Lp L) Ω l (W.resP L Ω g₀.1) = 1 := by
        rw [← V.hε]
        exact hg₀
      have h5 : Loc.cyc l l (φ g₀) = 1 := (d g₀).trans h4
      exact (congrArg (Units.map _) h5).trans (map_one _)
end
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.AdmissibleOfTypeII
section
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 200000

section
open UpperTheory.GalN.V
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N Formalism.BasicNotions Formalism.BasicNotions.Loc GlobalTheory.GalOfCusp Matrix IsLocalRing
open UpperTheory.V UpperTheory.V.Base UpperTheory.V.HV UpperTheory.V.Alg UpperTheory.V.U3
theorem UpperTheory.GalN.V.adm2B_rhoK_of_typeII_of_modular_extensions :
    CohInp → ∀ {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {K : Type} [Field K] [NumberField K] [Algebra K Ω]
      {l : ℕ} [Fact l.Prime] {c : Coef l} {N : ℕ} [NeZero N] {e : ℕ} {ψ : DirichletCharacter c.O N} (D : Dat Ω K c e ψ) {U : (_root_.UpperTheory.V.U3.Univ (_root_.UpperTheory.V.U3.GCond.noCondition _ (D.η.comp D.ι) (D.Ψ.comp D.ι)))} {g₁ : G ℚ Ω}, D.Marked g₁ → ∀ {r : G ℚ Ω →* GG (m := 3) (R := PadicAlgCl l)} (h : D.IsPt U g₁ r), ∀ (ι : Qbar l ≃+* ℂ),
      TypeII D.η r → (∀ W : G ℚ Ω →* GL (Fin 2) (PadicAlgCl l), D.IsExt r W → _root_.UpperTheory.V.Z.Win.Dn.IsModularA D ι W) →
      _root_.UpperTheory.V.Z.Win.Dn.Adm2B ι e (N * (discr K).natAbs) (D.rhoK r h.mult) := by
  intro hC Ω _ _ _ K _ _ _ l hl c N _ e ψ D U g₁ hM r h ι hII hmod
  obtain ⟨h11, -, W, hext, hcont, hirr, -, hdet⟩ := typeII_facts hC D hM h hII
  obtain ⟨-, -, -, -, -, -, -, -, -, -, hl1⟩ := dat_facts D
  let ψQ : G ℚ Ω →* (Qbar l)ˣ := (Units.map (algebraMap c.O (PadicAlgCl l)).toMonoidHom).comp (Chr.dirG ℚ Ω ψ)
  have hΨ : ∀ g, D.ΨQ g = cycBar ℚ Ω l g ^ (e : ℤ) * ψQ g := fun g => by
    show Units.map (algebraMap c.O (PadicAlgCl l)).toMonoidHom (chiO ℚ Ω l c.O g ^ (e : ℤ) * Chr.dirG ℚ Ω ψ g) = _
    rw [map_mul, map_zpow]
    rfl
  have hfin : ∀ g, ψQ g ^ Nat.card (ZMod N)ˣ = 1 := fun g => by
    show Units.map (algebraMap c.O (PadicAlgCl l)).toMonoidHom (ψ.toUnitHom (Chr.cls ℚ Ω N g)) ^ _ = 1
    rw [← map_pow, ← map_pow, pow_card_eq_one', map_one, map_one]
  have hodd : Odd (discr K).natAbs := Nat.coprime_two_right.1 (D.gd.cop.coprime_dvd_right D.gd.N_even.two_dvd)
  have hkill : ∀ g : G ℚ Ω, (∀ ζ : Ω, ζ ^ (N * (discr K).natAbs) = 1 → g ζ = ζ) → ψQ g = 1 ∧ D.η g = 1 := fun g hg => by
    constructor
    · show Units.map (algebraMap c.O (PadicAlgCl l)).toMonoidHom (ψ.toUnitHom (Chr.cls ℚ Ω N g)) = 1
      have hcls : Chr.cls ℚ Ω N g = 1 := by
        have : IsAlgClosed Ω := IsAlgClosure.isAlgClosed ℚ
        have : NeZero (N : Ω) := ⟨Nat.cast_ne_zero.mpr (NeZero.ne N)⟩
        obtain ⟨ζ, hζ⟩ := HasEnoughRootsOfUnity.exists_isPrimitiveRoot Ω N
        have hfix := hg ζ (by rw [pow_mul, hζ.pow_eq_one, one_pow])
        have hpow := Chr.cls_spec (k := ℚ) N g ζ hζ.pow_eq_one
        rw [hfix] at hpow
        have hone : ζ ^ (1 : ZMod N).val = ζ := by
          rw [ZMod.val_one_eq_one_mod, hζ.eq_orderOf, pow_mod_orderOf, pow_one]
        apply Units.ext
        apply ZMod.val_injective
        exact hζ.pow_inj (ZMod.val_lt _) (ZMod.val_lt _) (hpow.symm.trans hone.symm)
      rw [hcls, map_one, map_one]
    · rw [← MonoidHom.mem_ker, D.η_ker]
      exact UpperTheory.mem_galOf_quadratic_of_fixes_discr_roots_of_unity Ω K D.gd.quad hodd g fun ζ hζ => hg ζ (by rw [pow_mul', hζ, one_pow])
  have hblk : ∀ g ∈ D.η.ker, (r g).mat = !![W g 0 0, 0, W g 0 1; 0, 1, 0; W g 1 0, 0, W g 1 1] := fun g hg => by
    have hzero := hII.1 g hg
    have h01 := hzero 0 1 (by decide)
    have h10 := hzero 1 0 (by decide)
    have h12 := hzero 1 2 (by decide)
    have h21 := hzero 2 1 (by decide)
    change (r g).mat =
      !![(W g).val 0 0, 0, (W g).val 0 1; 0, 1, 0; (W g).val 1 0, 0, (W g).val 1 1]
    rw [hext.1 g hg]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [corner, h01, h10, h12, h21, h11 g hg]
  refine ⟨W, hirr, hmod W hext, ⟨hcont, fun w hw => ?_, fun w hw => ?_⟩, ?_, 1, fun s => ?_⟩
  · obtain ⟨A, hA⟩ := exists_isPlaceOver Ω w
    have hAl : ¬ A.valuation (l : Ω) < 1 := fun h' => hw (((places ℚ Ω l A).2.2.1 w hA).1 h')
    obtain ⟨M, hMM⟩ := pt_inertia_away D hM h A hAl
    have h1 := UpperTheory.diagonal_on_subgroup_of_conjugate (Ine (F := ℚ) A ⊓ D.η.ker) W ψQ M fun g hg => by
      have hc : cycZ ℚ Ω l g = 1 := (places ℚ Ω l A).2.2.2 hAl hg.1
      have hc' : cycBar ℚ Ω l g = 1 := by
        rw [cycBar, MonoidHom.comp_apply, hc, map_one]
      rw [← hblk g hg.2, hMM g hg.1 hg.2, GG.mat, unitaryThreeReflection_left, tor_val, hΨ, hc', _root_.one_zpow, one_mul]
      congr 2
      funext i
      fin_cases i <;> simp [wt1]
    obtain ⟨χ, hχ, hd⟩ := UpperTheory.exists_isDiagOn_of_isDiagOn_inf_ker_sign _ _ W ψQ h1
    exact ⟨A, hA, χ, fun i s hs => hχ i s (hkill s hs).1 (hkill s hs).2, hd⟩
  · obtain ⟨A, hA⟩ := exists_isPlaceOver Ω w
    have hAl : A.valuation (l : Ω) < 1 := ((places ℚ Ω l A).2.2.1 w hA).2 hw
    obtain ⟨-, M, hup, hdiag⟩ := pt_inertia_above hC D hM h A hAl
    obtain ⟨hIk, s₀, hs₀, hu⟩ := hl1 A hAl
    obtain ⟨hnorm, hID, -⟩ := Chr.decCyc Ω l A hl.out hAl
    have hs₀' : (D.ΨQ s₀ : Qbar l) ^ 2 ≠ 1 := by
      have := (hu.map (algebraMap c.O (PadicAlgCl l))).ne_zero
      rw [map_sub, map_pow, map_one, sub_ne_zero] at this
      exact this
    set v : Fin 3 → Qbar l := (M⁻¹ : GL (Fin 3) (Qbar l)).val *ᵥ Pi.single 0 1 with hv
    have hv0 : v ≠ 0 := fun h0 => by
      have := congrArg (fun x => (M.val *ᵥ x) 0) (hv.symm.trans h0)
      simp only [Matrix.mulVec_mulVec, Units.mul_inv, Matrix.one_mulVec, Matrix.mulVec_zero] at this
      simp at this
    have hev : ∀ s ∈ Ine (F := ℚ) A,
        !![W s 0 0, 0, W s 0 1; 0, 1, 0; W s 1 0, 0, W s 1 1] *ᵥ v = (D.ΨQ s : Qbar l) • v := fun s hs => by
      have hr : (r s).right = 1 := (h.mult s).trans (hIk hs)
      rw [← hblk s (hIk hs)]
      have hconj : (conjBy M r s).mat = M.val * (r s).mat * (M⁻¹ : GL (Fin 3) (Qbar l)).val := by
        simp [conjBy, GG.mat, hr]
      have hcol : (conjBy M r s).mat *ᵥ Pi.single 0 1 = (D.ΨQ s : Qbar l) • Pi.single 0 1 := by
        rw [Matrix.mulVec_single_one]
        funext i
        fin_cases i
        · simpa [Matrix.col, GG.mat, tor_val, wt1] using hdiag s hs 0
        · simpa using hup s (hID hs) (hIk hs) 1 0 (by decide)
        · simpa using hup s (hID hs) (hIk hs) 2 0 (by decide)
      rw [hv, ← Matrix.mulVec_smul, ← hcol, hconj, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec,
        ← Matrix.mul_assoc, ← Matrix.mul_assoc, Units.inv_mul, Matrix.one_mul]
    have hv1 : v 1 = 0 := by
      have := congrFun (hev s₀ hs₀) 1
      simp [Matrix.mulVec, dotProduct, Fin.sum_univ_three] at this
      by_contra hne
      have h3 : (D.ΨQ s₀ : Qbar l) = 1 := (mul_right_cancel₀ hne ((one_mul _).trans this)).symm
      exact hs₀' (by rw [h3, one_pow])
    obtain ⟨κ, hflag, hκ⟩ := UpperTheory.exists_isFlagOn_of_eigenvector_normal_subgroup (Dec (F := ℚ) A) (Ine (F := ℚ) A) W D.ΨQ ![v 0, v 2]
      (fun d hd s hs => hnorm.conj_mem' ⟨s, hID hs⟩ hs ⟨d, hd⟩)
      (fun h0 => hv0 (by
        funext i
        fin_cases i
        · exact congrFun h0 0
        · exact hv1
        · exact congrFun h0 1))
      (fun s hs => by
        have a0 := congrFun (hev s hs) 0
        have a2 := congrFun (hev s hs) 2
        funext i
        fin_cases i
        · simpa [Matrix.mulVec, dotProduct, Fin.sum_univ_three, Fin.sum_univ_two] using a0
        · simpa [Matrix.mulVec, dotProduct, Fin.sum_univ_three, Fin.sum_univ_two] using a2)
      (fun s hs => by rw [hdet, show D.η s = 1 from hIk hs]; simp)
      ⟨s₀, hs₀, hs₀'⟩
    have hκ' : ∀ i (s : ↥(Dec (F := ℚ) A)), (s : G ℚ Ω) ∈ Ine (F := ℚ) A →
        κ i s = cycBar ℚ Ω l s ^ (![(e : ℤ), -(e : ℤ)] i) * (![ψQ, ψQ⁻¹] i) s := fun i s hs => by
      fin_cases i
      · exact (hκ s hs).1.trans (hΨ s)
      · refine (hκ s hs).2.trans ?_
        rw [hΨ, mul_inv, ← _root_.zpow_neg]
        rfl
    refine ⟨A, hA, ![ψQ, ψQ⁻¹], κ, fun i s hs => ?_, hflag, hκ', Or.inl fun i j hij => ?_⟩
    · fin_cases i <;> simp [(hkill s hs).1]
    · have htwo : ∃ s ∈ Ine (F := ℚ) A, ∀ n : ℤ, cycBar ℚ Ω l s ^ n = 1 → n = 0 := by
        have hu : IsUnit ((2 : ℕ) : ℤ_[l]) := by
          rw [PadicInt.isUnit_iff, PadicInt.norm_natCast_eq_one_iff]
          exact (Nat.coprime_primes hl.out Nat.prime_two).2 D.gd.l_odd
        obtain ⟨u, hu⟩ := hu
        obtain ⟨s, hs, hcyc⟩ := GlobalTheory.CycInertia.cycZ_Ine_surjective Ω l A hAl u
        refine ⟨s, hs, fun n hn => ?_⟩
        have hval : ((cycBar ℚ Ω l s : (Qbar l)ˣ) : Qbar l) = ((2 : ℚ) : Qbar l) := by
          show ((algebraMap ℚ_[l] (Qbar l)).comp PadicInt.Coe.ringHom) (cycZ ℚ Ω l s : ℤ_[l]) = _
          rw [hcyc, hu, map_natCast]
          simp
        have hpow := congrArg Units.val hn
        rw [Units.val_zpow_eq_zpow_val, hval, Units.val_one, ← Rat.cast_zpow] at hpow
        have hrat : (2 : ℚ) ^ n = 1 := by exact_mod_cast hpow
        exact (zpow_eq_one_iff_right₀ (by norm_num) (by norm_num)).1 hrat
      obtain ⟨s, hs, hn⟩ := htwo
      have h1 := DFunLike.congr_fun hij ⟨s, hID hs⟩
      rw [MonoidHom.mul_apply, hκ' i _ hs, hκ' j _ hs] at h1
      have hf : ∀ i, ((![ψQ, ψQ⁻¹] i) s) ^ Nat.card (ZMod N)ˣ = 1 := fun i => by
        fin_cases i
        · exact hfin s
        · show (ψQ s)⁻¹ ^ _ = 1
          rw [inv_pow, hfin, inv_one]
      have h2 := congrArg (· ^ Nat.card (ZMod N)ˣ) h1
      simp only [mul_pow, hf, mul_one] at h2
      change (cycBar ℚ Ω l s ^ _) ^ _ = (cycBar ℚ Ω l s ^ _) ^ _ * cycBar ℚ Ω l s ^ _ at h2
      rw [← mul_pow, ← _root_.zpow_add_one, ← mul_inv_eq_one, ← inv_pow, ← mul_pow, ← _root_.zpow_sub, ← _root_.zpow_natCast,
        ← _root_.zpow_mul] at h2
      have h3 := (mul_eq_zero.1 (hn _ h2)).resolve_right (by exact_mod_cast Nat.card_pos.ne')
      fin_cases i <;> fin_cases j <;> simp at h3 <;> omega
  · refine ⟨N * (discr K).natAbs, Matrix.GeneralLinearGroup.det.comp W,
      Nat.mul_pos (NeZero.pos N) hodd.pos, fun s hs => Units.ext ?_, by simp⟩
    have := hdet s
    rw [(hkill s hs).2] at this
    simpa using this
  · rw [one_mul, inv_one, mul_one, D.rhoK_apply]
    exact hblk _ (D.η_ker ▸ galEmb_mem ℚ K Ω s)
end
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.AutomorphicFormHyp
section
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 200000

section
namespace UpperTheory.V.Af
open UpperTheory.V.Published
structure Hypotheses' : Prop where
  litN : _root_.GlobalTheory.Mem.LiteralAutomorphy.LiteratureRankNHypothesis
  cohC : ClozelCohC
  conjC : ClozelConjC
  borelC : BorelInjC
  galR : _root_.UpperTheory.Gal.SV.GaloisRepExistsTotallyRealGL2
  smoR : StrongMultOneReal
  gkR : GelfandKazhdanReal
  admR : AdmissibleReal
  bc : Br.QuadBC0
  newform : NewformRep
end UpperTheory.V.Af
end
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.AutomorphicTensorInductionOfLocalPlaces
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
private theorem neu_comm {L : Type} [Field L] [NumberField L] [IsCMField L] {n : ℕ} {w : Plc L} {j : GLw n w →* UA L n}
    (hj : ∀ x ∈ locU n w, x = j (cLoc w x)) {g y : UA L n} (hg : cLoc w g = 1) (hy : y ∈ locU n w) : Commute g y := by
  have h1 : (GlobalTheory.DefU.LocRet.ret w n g : UA L n) = 1 := by
    rw [hj _ (GlobalTheory.DefU.LocRet.ret w n g).2]
    have : cLoc w (GlobalTheory.DefU.LocRet.ret w n g : UA L n) = cLoc w g := GlobalTheory.DefU.LocRet.localProj_unitaryAdelicLocalRetractionEnd_of_under_eq rfl g
    rw [this, hg, map_one]
  have h2 := GlobalTheory.DefU.LocRet.commute_ret g ⟨y, hy⟩
  rwa [h1, inv_one, one_mul] at h2
private theorem ne_J {L : Type} [Field L] [NumberField L] [IsCMField L] {n : ℕ} {St : Type} [Fintype St] [DecidableEq St]
    {wt : St → Plc L} (hinj : Function.Injective fun u => (wt u).under (𝓞 (Lp L))) (j : ∀ u, GLw n (wt u) →* UA L n)
    (h1 : ∀ u g, j u g ∈ locU n (wt u)) (h2 : ∀ u g, cLoc (wt u) (j u g) = g) (h3 : ∀ u, ∀ x ∈ locU n (wt u), x = j u (cLoc (wt u) x)) :
    ∃ J : GV n wt →* UA L n, (∀ u g, J (Pi.mulSingle u g) = j u g) ∧ (∀ g, J g ∈ GlobalTheory.UnitaryBC.finU (E := L) (n := n)) ∧
      (∀ g u, cLoc (wt u) (J g) = g u) ∧
      (∀ g (v : Plc L), (∀ u, v.under (𝓞 (Lp L)) ≠ (wt u).under (𝓞 (Lp L))) → cLoc v (J g) = 1) ∧
      ∀ g k, (∀ u, cLoc (wt u) k = 1) → Commute k (J g) := by
  have h4 : ∀ u g (v : Plc L), v.under (𝓞 (Lp L)) ≠ (wt u).under (𝓞 (Lp L)) → cLoc v (j u g) = 1 := fun u g v hv =>
    GlobalTheory.DefU.LocRet.mem_locU_ne (h1 u g) hv
  have hc : Pairwise fun a b => ∀ x y, Commute (j a x) (j b y) := fun a b hab x y =>
    neu_comm (h3 b) (h4 a x _ fun e => hab (hinj e).symm) (h1 b y)
  let J := MonoidHom.noncommPiCoprod j hc
  have hJ : ∀ u g, J (Pi.mulSingle u g) = j u g := fun u g => MonoidHom.noncommPiCoprod_mulSingle j u g
  have key : ∀ P : Subgroup (UA L n), (∀ u g, j u g ∈ P) → ∀ g, J g ∈ P := fun P hP g => by
    have : J.range ≤ P := by
      rw [MonoidHom.noncommPiCoprod_range]
      exact iSup_le fun u => by rintro _ ⟨g, rfl⟩; exact hP u g
    exact this ⟨g, rfl⟩
  refine ⟨J, hJ, key _ fun u g => (h1 u g).1, fun g u => ?_, fun g v hv => key (cLoc v).ker (fun u g => h4 u g v (hv u)) g,
    fun g k hk => ?_⟩
  · have : (cLoc (wt u)).comp J = Pi.evalMonoidHom (fun u => GLw n (wt u)) u := MonoidHom.pi_ext fun i x => by
      rw [MonoidHom.comp_apply, hJ, Pi.evalMonoidHom_apply]
      by_cases h : u = i
      · subst h
        rw [h2, Pi.mulSingle_eq_same]
      · rw [Pi.mulSingle_eq_of_ne h]
        exact h4 i x _ fun e => h (hinj e)
    exact DFunLike.congr_fun this g
  · exact (Subgroup.mem_centralizer_singleton_iff.1
      (key (Subgroup.centralizer {k}) (fun u g => Subgroup.mem_centralizer_singleton_iff.2
        (neu_comm (h3 u) (hk u) (h1 u g)).symm.eq) g)).symm
private theorem automorphic_tensor_induction_of_local_places {L Ω : Type} [Field L] [NumberField L] [IsCMField L] [Field Ω] [Algebra L Ω] [IsAlgClosure L Ω] {n m : ℕ}
    {St : Type} {wt : St → Plc L} {At : St → ValuationSubring Ω} (ht : ∀ u, IsPlaceOver (At u) (wt u))
    (j : ∀ u, GLw n (wt u) →* UA L n) (J : GV n wt →* UA L n)
    (hJ : ∀ u g, J (by classical exact MonoidHom.mulSingle (fun u => GLw n (wt u)) u g) = j u g)
    (τ₀ : KT n wt →* GL (Fin m) ℂ) (χ : ∀ u, Fin n → Ine (F := L) (At u) →* ℂˣ) (hT : _root_.UpperTheory.V.Hi.IsTypeAlt ht τ₀ χ)
    {σ : Submodule ℂ (UA L n → ℂ)} (hσ : IsAutRepU σ) (τ : ∀ u, SmIrr (GLw n (wt u)))
    (hτ : ∀ u, IsoSum ((RU L n).comp (j u)) σ (τ u)) (F : Fin m → UA L n → ℂ) (hF0 : F ≠ 0) (hF1 : ∀ i, F i ∈ σ)
    (hF2 : ∀ (k : KT n wt) i, ∑ a, τ₀ k i a • RU L n (J k) (F a) = F i) :
    ∀ u rc, _root_.UpperTheory.Zero.LLC.IsRecT (ht u) rc → IsTypeWD (ht u) (χ u) (rc (algNorm (τ u))) := by
  haveI : Nontrivial σ := Submodule.nontrivial_iff_ne_bot.2 hσ.ne_bot
  let ρ : Representation ℂ (GV n wt) σ :=
    (⟨σ, fun g v hv => hσ.stable (J g) v hv⟩ : Subrepresentation ((RU L n).comp J)).toRepresentation
  have hρ : ∀ g (y : σ), (ρ g y : UA L n → ℂ) = RU L n (J g) y := fun _ _ => rfl
  refine (hT.2 σ ρ τ fun u => ?_).1 ⟨fun i => ⟨F i, hF1 i⟩, fun h => hF0 (funext fun i => congrArg Subtype.val (congrFun h i)),
    fun k i => Subtype.ext ?_⟩
  · refine UpperTheory.isoSum_of_injective_equivariant_family _ _ _ _ _ ⊤ σ (τ u) Unit (fun _ => σ.subtype) (hτ u) (fun _ _ _ => Submodule.mem_top)
      (fun _ y _ => y.2) (fun _ g y _ => ?_) fun y _ h => Subtype.ext (h ())
    exact (hρ _ y).trans (by rw [hJ]; rfl)
  · change σ.subtype (∑ a, τ₀ k i a • ρ k ⟨F a, hF1 a⟩) = F i
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum, ← hF2 k i]
    rfl
theorem UpperTheory.V.Hi.partUR2Type_alt :
    ∀ (l : ℕ) [Fact l.Prime] (L Ω : Type) [Field L] [NumberField L] [IsCMField L] [Field Ω] [Algebra L Ω] [IsAlgClosure L Ω] (s : HidaSetting l L Ω) (n : ℕ), 1 ≤ n →
    ∀ (V : s.Lev) (Q : QData V) (c : Coef l) (ι : Qbar l ≃+* ℂ) (m : ℕ) (τ₀ : KT n (wt s) →* GL (Fin m) c.O)
    (lam : Wt L l n) (d : ℕ) (e : (Fin d → ℂ) ≃ₗ[ℂ] ⨂[ℂ] e : Emb l (fun v : V.frame.Vl => s.w v.1), nablaSq ℂ n (lam e.res)) (ξ : GV n (fun v : V.frame.Vl => s.w v.1) →* GL (Fin d) ℂ), IsBasis ι e ξ →
    ∀ σ : Submodule ℂ (UA L n → ℂ), IsAutRepU σ →
    YOf Q ι τ₀ e ξ σ ≠ ⊥ → ∀ χ : ∀ u : s.St, Fin n → Ine (F := L) (s.A u) →* ℂˣ, _root_.UpperTheory.V.Hi.IsTypeAlt (fun u : s.St => s.hw u) ((Matrix.GeneralLinearGroup.map (ι.toRingHom.comp (algebraMap c.O (Qbar l)))).comp τ₀) χ →
    ∀ τ : ∀ u : s.St, SmIrr (GLw n (s.w u)), (∀ u : s.St, IsCompAlong σ (locU n (s.w u)) ((cLoc (s.w u)).comp (locU n (s.w u)).subtype) (τ u).ρ) → ∀ (u : s.St) rc, _root_.UpperTheory.Zero.LLC.IsRecT (s.hw u) rc → IsTypeWD (s.hw u) (χ u) (rc (algNorm (τ u))) := by
  intro l _ L Ω _ _ _ _ _ _ s n hn V Q c ι m τ₀ lam d e ξ he σ hσ hY χ hT τ hτ
  letI : DecidableEq s.St := fun a b => Classical.propDecidable _
  obtain ⟨hw, hsp⟩ := UpperTheory.under_chosen_place_and_isSplitAt_of_decomp_le l L Ω s
  choose j h1 h2 _ h3 using fun u : s.St => (secU l L Ω s n hn (wt s u) (hsp _ (by
    rw [hw]
    exact s.split _ (Or.inr (Or.inl u.2))))).1
  obtain ⟨J, hJ, j1, j2, j3, -⟩ := ne_J (wt := wt s)
    (fun a b hab => Subtype.ext ((hw _).symm.trans (hab.trans (hw _)))) j h1 h2 h3
  obtain ⟨F, hF, hF0⟩ := (Submodule.ne_bot_iff _).1 hY
  obtain ⟨hB, hFσ⟩ := (partUR2Mem l L Ω s n hn V Q c ι m τ₀ lam d e ξ σ F).1 hF
  have f1 := (formU l L Ω s n hn V Q c m τ₀ ι lam d e ξ he _ fun _ => rfl).1
  have hex : ∃ i ℓ, toForm ι e (F i) ℓ ≠ 0 := by
    by_contra h
    exact hF0 (funext fun i => f1 (F i) (hB.1 i trivial) fun ℓ => by
      by_contra h'
      exact h ⟨i, ℓ, h'⟩)
  obtain ⟨i₀, ℓ, hℓ⟩ := hex
  have j4 : ∀ g (v : Plc L), v.under (𝓞 (Lp L)) ∉ s.St → cLoc v (J g) = 1 := fun g v hv =>
    j3 g v fun a h => hv (by rw [h, hw]; exact a.2)
  refine automorphic_tensor_induction_of_local_places (fun u : s.St => s.hw u) j J (fun u g => ?_) _ χ hT hσ τ
    (fun u => UpperTheory.isoSum_restriction_of_local_component_unitary L n σ hσ _ (j u) (h1 u) (h2 u) (h3 u) (τ u) (hτ u)) (fun i => toForm ι e (F i) ℓ)
    (fun h => hℓ (congrFun h i₀)) (fun i => hFσ i ℓ) fun k i => ?_
  · exact hJ u g
  · refine partUR2Fix l L Ω s n hn V Q c ι m τ₀ lam d e ξ he F hB (J k) (j1 _) (fun v => j4 _ _ ?_) k (fun u => (j2 _ u).symm) ?_
      (fun w hw' => ?_) (fun q => j4 _ _ fun h => Q.notS q (Or.inr (Or.inl h))) i ℓ
    · rw [hw]
      exact fun h => s.St_l _ h v.2
    · rw [j4 _ _ (by rw [hw]; exact s.v0_St)]
      exact one_mem _
    · rw [j4 _ _ fun h => hw' (V.sub (Or.inr (Or.inl h)))]
      exact one_mem _
end
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.IsModular
section
noncomputable abbrev UpperTheory.V.U3.Dat.IsModularDense := @UpperTheory.V.Z.Win.Dn.IsModularA
end

