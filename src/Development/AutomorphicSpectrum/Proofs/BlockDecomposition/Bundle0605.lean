module

public import Mathlib
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.DifferentialFormsCech.GlobalDifferentialForms.Bundle0001
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.DifferentialFormsCech.HdgAffIso
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.GrCechFin
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.CechPairings.Imports
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SerreClassOfCechSpectralSequence
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ThetaNormCommutation.LocalComparisonSplitting.EulerFactorLevels.EulerFinOf
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1363
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0411
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0438
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0458
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0592
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0591
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0439
public import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.MirabolicDerivatives.SegmentCuspLines.CuspLinesIrr
public import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.MirabolicDerivatives.UnipotentDerivatives.DerUnipLeUnipB
public import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.MirabolicDerivatives.TwistedKernels.ExPhiPlusOnto
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0004
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0463
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0593
public import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.MirabolicDerivatives.LeibnizDerivatives.GenericProdIff
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0327
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0488
public import Development.AutomorphicSpectrum.Proofs.GlobalProofs.Bundle0030
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0195
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0719
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0373
public import CompanionTheory.AutomorphicTheory.HeckeStandardModules.EqZeroOfCompAt
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ReverseOrderedProductPermEquiv
public import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.ZelevinskyJacquet.ZelevinskyCosocles.LUnlinkedComm
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0002
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0554
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ArchimedeanGelfandKernels.LeftEquivariantFunctions.ComplexMatrixCalculus.Bundle0001
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0352
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0580
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0590

@[expose] public section

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.PullbackCoverStarCompat
section
set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry GlobalTheory.LogCris DividedPowers GlobalTheory.CechDR GlobalTheory.HodgeCoh CrystallineSemistableComparison CrystallineSemistableComparison.Pb CrystallineSemistableComparison.Om CrystallineSemistableComparison.Om.Glob GlobalTheory.CompanionTheory.CechSerre
universe w

noncomputable section

namespace GlobalTheory.CompanionTheory.OmGlobPush

theorem push_kc : ∀ {K : Type} [CommRing K] {X Y : Scheme.{0}} (q : X ⟶ Spec (CommRingCat.of K)) (p : Y ⟶ Spec (CommRingCat.of K))
    (u : X ⟶ Y) (hu : u ≫ p = q) (U : Cov q) (W : Cov p) (τ : U.ι → W.ι)
    (hτ : ∀ n (i : Fin (n + 1) → U.ι), capO U.U i ≤ u ⁻¹ᵁ capO W.U (τ ∘ i)) (a : ℕ),
    ∃ hG : ∀ T, KC q U a T → KC p W a ((pullM u hu a).G.obj T),
      ∀ α T, Vk q U a α T → Vk p W a (τ α) ((morU (pullM u hu a) (U := KC p W a) (U' := KC q U a) hG).G.obj T) := by
  intro K _ X Y q p u hu U W τ hτ a
  have key : ∀ (T : GlobalTheory.LogCris.Thick (CrystallineSemistableComparison.smFun X q)) (α : U.ι),
      CrystallineSemistableComparison.Pb.InU (U.U α) T → CrystallineSemistableComparison.Pb.InU (W.U (τ α)) ((pullM u hu a).G.obj T) := by
    intro T α h
    have h0 : U.U α ≤ u ⁻¹ᵁ W.U (τ α) := by
      have h1 := hτ 0 (fun _ => α)
      simpa [CrystallineSemistableComparison.Pb.capO] using h1
    unfold CrystallineSemistableComparison.Pb.InU at h ⊢
    change ⊤ ≤ (TopologicalSpace.Opens.map (pt T ≫ u).base).obj (W.U (τ α))
    exact h.trans ((TopologicalSpace.Opens.map (pt T).base).monotone h0)
  have ktf : ∀ (T : GlobalTheory.LogCris.Thick (CrystallineSemistableComparison.smFun X q)),
      CrystallineSemistableComparison.Pb.TF 1 (a + 1) T → CrystallineSemistableComparison.Pb.TF 1 (a + 1) ((pullM u hu a).G.obj T) := by
    intro T h
    exact h
  refine ⟨fun T hT => ?_, fun α T hT => ?_⟩
  · obtain ⟨hTF, V, ⟨α, rfl⟩, hV⟩ := hT
    exact ⟨ktf T hTF, W.U (τ α), ⟨τ α, rfl⟩, key T α hV⟩
  · exact key T.obj α hT

end GlobalTheory.CompanionTheory.OmGlobPush
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.RationalFinitePlaces
section
open NumberField IsDedekindDomain Matrix Polynomial Filter
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical
open PositivityTheory.Rg.BcB.G8 PositivityTheory.Rg.BcB.G8.Fin
open scoped ComplexOrder

noncomputable section

namespace GlobalTheory.CompanionTheory.RatFinG

theorem selberg {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] (U Γ : Subgroup G) (C : Set G) (n₀ : G)
    (hC : IsCompact C) (hcov : ∀ g ∈ U, ∃ γ ∈ Γ, ∃ c ∈ C, g = γ * c)
    (hfin : ∀ X : Set G, IsCompact X → ((Γ : Set G) ∩ X).Finite) (hn : n₀ ∈ Γ) :
    ∃ C' : Set G, IsCompact C' ∧ ∀ t ∈ U, t * n₀ = n₀ * t → ∃ γ ∈ Γ, γ * n₀ = n₀ * γ ∧ ∃ c ∈ C', t = γ * c := by
  have hX : IsCompact ((fun p : G × G => p.1 * n₀ * p.2⁻¹) '' (C ×ˢ C)) :=
    (hC.prod hC).image (by fun_prop)
  have hF := hfin _ hX
  let rep : G → G := fun f => if h : ∃ γ ∈ Γ, γ⁻¹ * n₀ * γ = f then h.choose else 1
  have hrep : ∀ f, (∃ γ ∈ Γ, γ⁻¹ * n₀ * γ = f) → rep f ∈ Γ ∧ (rep f)⁻¹ * n₀ * rep f = f := by
    intro f h
    simp only [rep, dif_pos h]
    exact h.choose_spec
  refine ⟨⋃ f ∈ (Γ : Set G) ∩ _, (fun c => rep f * c) '' C, hF.isCompact_biUnion fun f _ =>
    hC.image (by fun_prop), ?_⟩
  intro t ht hcomm
  obtain ⟨γ, hγ, c, hc, rfl⟩ := hcov t ht
  set f := γ⁻¹ * n₀ * γ with hf
  have hfc : f = c * n₀ * c⁻¹ := by
    have e : γ⁻¹ * n₀ * γ * c = c * n₀ := by
      have : n₀ * (γ * c) = γ * c * n₀ := hcomm.symm
      calc γ⁻¹ * n₀ * γ * c = γ⁻¹ * (n₀ * (γ * c)) := by group
        _ = γ⁻¹ * (γ * c * n₀) := by rw [this]
        _ = c * n₀ := by group
    rw [hf, eq_mul_inv_iff_mul_eq, e]
  have hfΓ : f ∈ Γ := mul_mem (mul_mem (inv_mem hγ) hn) hγ
  obtain ⟨h1, h2⟩ := hrep f ⟨γ, hγ, rfl⟩
  refine ⟨γ * (rep f)⁻¹, mul_mem hγ (inv_mem h1), ?_, rep f * c, ?_, by group⟩
  · have e : (rep f)⁻¹ * n₀ * rep f = γ⁻¹ * n₀ * γ := h2
    calc γ * (rep f)⁻¹ * n₀ = γ * ((rep f)⁻¹ * n₀ * rep f) * (rep f)⁻¹ := by group
      _ = γ * (γ⁻¹ * n₀ * γ) * (rep f)⁻¹ := by rw [e]
      _ = n₀ * (γ * (rep f)⁻¹) := by group
  · refine Set.mem_biUnion (x := f) ⟨hfΓ, ⟨(c, c), ⟨hc, hc⟩, hfc.symm⟩⟩ ⟨c, hc, rfl⟩

abbrev gam1 (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ) (δ : GL (Fin n) E) : Subgroup (GL (Fin n) (Af E)) :=
  (ratF E n).range ⊓ twCent (thF E n) (ratF E n δ)

theorem algebraMap_inj (E : Type) [Field E] [NumberField E] : Function.Injective (algebraMap E (Af E)) := by
  haveI : Nontrivial (Af E) := by
    obtain ⟨P, hP⟩ := Ideal.exists_maximal (𝓞 E)
    exact (Formalism.UG.evalV E ⟨P, hP.isPrime,
      Ring.ne_bot_of_isMaximal_of_not_isField hP (RingOfIntegers.not_isField E)⟩).toRingHom.domain_nontrivial
  exact (algebraMap E (Af E)).injective

theorem ratF_injective (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ) :
    Function.Injective (ratF E n) := by
  intro a b h
  refine Units.ext (Matrix.ext fun i j => algebraMap_inj E ?_)
  exact congrArg (fun g : GL (Fin n) (Af E) => g.val i j) h

theorem ratF_mem_UJ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ) (H : Matrix (Fin n) (Fin n) E)
    (γ : GL (Fin n) E) : ratF E n γ ∈ UJ (conjFin (IsCMField.complexConj E).toRingEquiv) (H.map (algebraMap E (Af E))) ↔
      γ ∈ UJ (IsCMField.complexConj E).toRingEquiv.toRingHom H := by
  have hi := algebraMap_inj E
  have hv : (ratF E n γ).val = γ.val.map (algebraMap E (Af E)) := rfl
  have hcT : cT (conjFin (IsCMField.complexConj E).toRingEquiv) (γ.val.map (algebraMap E (Af E))) =
      (cT (IsCMField.complexConj E).toRingEquiv.toRingHom γ.val).map (algebraMap E (Af E)) := by
    refine Matrix.ext fun i j => ?_
    exact conjFin_algebraMap _ _
  change cT _ (ratF E n γ).val * _ * (ratF E n γ).val = _ ↔ cT _ γ.val * H * γ.val = H
  rw [hv, hcT, ← Matrix.map_mul, ← Matrix.map_mul]
  exact ⟨fun h => Matrix.map_injective hi h, fun h => by rw [h]⟩

theorem factor (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ) (δ : GL (Fin n) E) (hδ : polE δ ∈ Ell E n) :
    (∃ C : Set (GL (Fin n) (Af E)), IsCompact C ∧ ∀ t ∈ twCent (thF E n) (ratF E n δ), ∃ γ ∈ gam1 E n δ, ∃ c ∈ C, t = γ * c) ∧
    (∀ X : Set (GL (Fin n) (Af E)), IsCompact X → ((gam1 E n δ : Set (GL (Fin n) (Af E))) ∩ X).Finite) ∧
    {γ : GL (Fin n) (Af E) | γ ∈ gam1 E n δ ∧ IsOfFinOrder γ}.Finite := by
  have hs : (δ * thE E n δ).val.charpoly.Separable := hδ.2.2.1
  have hr : ∀ τ : E →+* ℂ, ∀ z ∈ ((δ * thE E n δ).val.charpoly.map τ).roots, ‖z‖ = 1 := hδ.2.2.2
  obtain ⟨H, hu, hh, hN, hp⟩ := _root_.GlobalTheory.CompanionTheory.TraceHerm.exists_posDef_herm E n _ hs hr
  obtain ⟨⟨C₀, hC₀, hcov⟩, hfin⟩ := _root_.GlobalTheory.CompanionTheory.DefiniteTransport.cocompact_discrete E n H hu hh hp
  have hc := _root_.GlobalTheory.CompanionTheory.TwCentNorm.mem_twCent_ratF_iff E n δ H hs hu hN
  set U := UJ (conjFin (IsCMField.complexConj E).toRingEquiv) (H.map (algebraMap E (Af E))) with hU
  set Γ := (UJ (IsCMField.complexConj E).toRingEquiv.toRingHom H).map (ratF E n) with hΓ
  have hΓfin : ∀ X : Set (GL (Fin n) (Af E)), IsCompact X → ((Γ : Set (GL (Fin n) (Af E))) ∩ X).Finite := by
    intro X hX
    refine ((hfin X hX).image (ratF E n)).subset ?_
    rintro _ ⟨⟨γ, hγ, rfl⟩, hx⟩
    exact ⟨γ, ⟨hγ, hx⟩, rfl⟩
  have hsub : ∀ y ∈ gam1 E n δ, y ∈ Γ := by
    rintro _ ⟨⟨γ, rfl⟩, ht⟩
    exact ⟨γ, (ratF_mem_UJ E n H γ).1 ((hc _).1 ht).1, rfl⟩
  obtain ⟨C', hC', hsel⟩ := selberg U Γ C₀ (ratF E n (δ * thE E n δ)) hC₀
    (fun g hg => by
      obtain ⟨γ, hγ, k, hk, e⟩ := hcov g hg
      exact ⟨_, ⟨γ, hγ, rfl⟩, k, hk, e⟩)
    hΓfin ⟨_, hN, rfl⟩
  refine ⟨⟨C', hC', fun t ht => ?_⟩, fun X hX => (hΓfin X hX).subset fun y hy => ⟨hsub y hy.1, hy.2⟩, ?_⟩
  · obtain ⟨h1, h2⟩ := (hc t).1 ht
    obtain ⟨γ, hγ, hcm, c, hc', e⟩ := hsel t h1 h2
    obtain ⟨γ₀, hγ₀, rfl⟩ := hγ
    exact ⟨ratF E n γ₀, ⟨⟨γ₀, rfl⟩, (hc _).2 ⟨(ratF_mem_UJ E n H γ₀).2 hγ₀, hcm⟩⟩, c, hc', e⟩
  · refine ((_root_.GlobalTheory.CompanionTheory.TorCent.finite_torsion_centralizer E n _ hs).image (ratF E n)).subset ?_
    rintro y ⟨hy, hfo⟩
    obtain ⟨⟨γ, rfl⟩, ht⟩ := hy
    refine ⟨γ, ⟨ratF_injective E n ?_, ?_⟩, rfl⟩
    · rw [map_mul (ratF E n) γ, map_mul (ratF E n) _ γ]
      exact ((hc _).1 ht).2
    · exact (ratF_injective E n).isOfFinOrder_iff.1 hfo

theorem mem_twCent_thP {E : Type} [Field E] [NumberField E] [IsCMField E] {a b : ℕ} (x : GL (Fin a) (Af E)) (y : GL (Fin b) (Af E))
    (p : Gf E a b) : p ∈ twCent (thP E a b) (x, y) ↔ p.1 ∈ twCent (thF E a) x ∧ p.2 ∈ twCent (thF E b) y := by
  change p * (x, y) = (x, y) * thP E a b p ↔ p.1 * x = x * thF E a p.1 ∧ p.2 * y = y * thF E b p.2
  exact Prod.ext_iff

theorem mem_gam {E : Type} [Field E] [NumberField E] [IsCMField E] {a b : ℕ} (δ₁ : GL (Fin a) E) (δ₂ : GL (Fin b) E)
    (p : Gf E a b) : p ∈ gam δ₁ δ₂ ↔ p.1 ∈ gam1 E a δ₁ ∧ p.2 ∈ gam1 E b δ₂ := by
  rw [gam, Subgroup.mem_inf, mem_twCent_thP, gam1, gam1, Subgroup.mem_inf, Subgroup.mem_inf]
  constructor
  · rintro ⟨⟨q, rfl⟩, h1, h2⟩
    exact ⟨⟨⟨q.1, rfl⟩, h1⟩, ⟨q.2, rfl⟩, h2⟩
  · rintro ⟨⟨⟨q₁, e₁⟩, h1⟩, ⟨q₂, e₂⟩, h2⟩
    exact ⟨⟨(q₁, q₂), Prod.ext e₁ e₂⟩, h1, h2⟩

theorem ratFin : PositivityTheory.Rg.BcB.G8.Fin.RatFin := by
  intro E _ _ _ _ a b δ₁ δ₂ h₁ h₂
  haveI : T2Space (Af E) :=
    inferInstanceAs (T2Space (RestrictedProduct (fun v : HeightOneSpectrum (𝓞 E) => v.adicCompletion E)
      (fun v => (v.adicCompletionIntegers E : Set (v.adicCompletion E))) Filter.cofinite))
  obtain ⟨⟨C₁, hC₁, hc₁⟩, hf₁, ht₁⟩ := factor E a δ₁ h₁
  obtain ⟨⟨C₂, hC₂, hc₂⟩, hf₂, ht₂⟩ := factor E b δ₂ h₂
  have hs₁ : (δ₁ * thE E a δ₁).val.charpoly.Separable := h₁.2.2.1
  have hs₂ : (δ₂ * thE E b δ₂).val.charpoly.Separable := h₂.2.2.1
  have hK₁ := _root_.GlobalTheory.CompanionTheory.IntegralPoints.kfOC E a
  have hK₂ := _root_.GlobalTheory.CompanionTheory.IntegralPoints.kfOC E b
  have hKc : (((Kf E a).prod (Kf E b) : Subgroup (Gf E a b)) : Set (Gf E a b)) = (Kf E a : Set _) ×ˢ (Kf E b : Set _) :=
    Subgroup.coe_prod _ _
  have hKo : IsOpen (((Kf E a).prod (Kf E b) : Subgroup (Gf E a b)) : Set (Gf E a b)) := by
    rw [hKc]; exact hK₁.1.prod hK₂.1
  have hKcp : IsCompact (((Kf E a).prod (Kf E b) : Subgroup (Gf E a b)) : Set (Gf E a b)) := by
    rw [hKc]; exact hK₁.2.prod hK₂.2
  have hcl : IsClosed ((twCent (thP E a b) (ratF E a δ₁, ratF E b δ₂) : Subgroup (Gf E a b)) : Set (Gf E a b)) := by
    have e : ((twCent (thP E a b) (ratF E a δ₁, ratF E b δ₂) : Subgroup (Gf E a b)) : Set (Gf E a b)) =
        (twCent (thF E a) (ratF E a δ₁) : Set _) ×ˢ (twCent (thF E b) (ratF E b δ₂) : Set _) := by
      ext p
      exact mem_twCent_thP _ _ p
    rw [e]
    exact (GlobalTheory.MassNorm.isClosed_twCent_thF E a _).prod (GlobalTheory.MassNorm.isClosed_twCent_thF E b _)
  set T := twCent (thP E a b) (ratF E a δ₁, ratF E b δ₂) with hTdef
  have hcomm : ∀ p ∈ T, ∀ q ∈ T, p * q = q * p := fun p hp q hq => by
    rw [hTdef, mem_twCent_thP] at hp hq
    exact Prod.ext (_root_.GlobalTheory.CompanionTheory.RatCentComm.twCent_ratF_comm E a δ₁ hs₁ _ hp.1 _ hq.1) (_root_.GlobalTheory.CompanionTheory.RatCentComm.twCent_ratF_comm E b δ₂ hs₂ _ hp.2 _ hq.2)
  have hle : gam δ₁ δ₂ ≤ T := fun p hp => hp.2
  have hcov : ∀ t ∈ T, ∃ γ ∈ gam δ₁ δ₂, ∃ c ∈ C₁ ×ˢ C₂, t = γ * c := fun t ht => by
    rw [hTdef, mem_twCent_thP] at ht
    obtain ⟨γ₁, hγ₁, c₁, hcc₁, e₁⟩ := hc₁ _ ht.1
    obtain ⟨γ₂, hγ₂, c₂, hcc₂, e₂⟩ := hc₂ _ ht.2
    exact ⟨(γ₁, γ₂), (mem_gam δ₁ δ₂ _).2 ⟨hγ₁, hγ₂⟩, (c₁, c₂), ⟨hcc₁, hcc₂⟩, Prod.ext e₁ e₂⟩
  have hfin : ∀ X : Set (Gf E a b), IsCompact X → ((gam δ₁ δ₂ : Set (Gf E a b)) ∩ X).Finite := fun X hX => by
    have h1 := hf₁ _ (hX.image continuous_fst)
    have h2 := hf₂ _ (hX.image continuous_snd)
    refine (h1.prod h2).subset ?_
    rintro p ⟨hp, hx⟩
    have hp' := (mem_gam δ₁ δ₂ p).1 hp
    exact ⟨⟨hp'.1, ⟨p, hx, rfl⟩⟩, hp'.2, ⟨p, hx, rfl⟩⟩
  have htor : {γ : Gf E a b | γ ∈ gam δ₁ δ₂ ∧ IsOfFinOrder γ}.Finite := by
    refine (ht₁.prod ht₂).subset ?_
    rintro p ⟨hp, hfo⟩
    have hp' := (mem_gam δ₁ δ₂ p).1 hp
    obtain ⟨k, hk, e⟩ := isOfFinOrder_iff_pow_eq_one.1 hfo
    have e' : p.1 ^ k = 1 ∧ p.2 ^ k = 1 := Prod.ext_iff.1 e
    exact ⟨⟨hp'.1, isOfFinOrder_iff_pow_eq_one.2 ⟨k, hk, e'.1⟩⟩, hp'.2, isOfFinOrder_iff_pow_eq_one.2 ⟨k, hk, e'.2⟩⟩
  haveI : T2Space (Gf E a b) := by
    set_option synthInstance.maxHeartbeats 200000 in
      infer_instance
  have hmain := _root_.GlobalTheory.CompanionTheory.CountClosedComm.main (Gf E a b) ((Kf E a).prod (Kf E b)) T (gam δ₁ δ₂)
    (C₁ ×ˢ C₂) hKo hKcp hcl hcomm hle (hC₁.prod hC₂) hcov hfin htor
  exact ⟨⟨hcomm, hmain.1⟩, hmain.2.1, hmain.2.2.1, hmain.2.2.2⟩

end GlobalTheory.CompanionTheory.RatFinG
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ReducibleCuspidalPairNongenericSubquotient
section
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.BZSeg GlobalTheory.BZMir Zc

noncomputable section

namespace GlobalTheory.CompanionTheory.CuspPair

section General

variable {G V W : Type} [Group G] [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]

theorem apply_mem_twKer {σ : Representation ℂ G V} {τ : Representation ℂ G W} (q : σ.IntertwiningMap τ)
    (H : Subgroup G) (χ : H →* ℂˣ) {v : V} (hv : v ∈ twKer σ H χ) : q v ∈ twKer τ H χ := by
  induction hv using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨n, u, rfl⟩ := hx
    refine Submodule.subset_span ⟨n, q u, ?_⟩
    rw [map_sub, map_smul, q.isIntertwining]
  | zero => simp
  | add x y _ _ hx hy => rw [map_add]; exact add_mem hx hy
  | smul c x _ hx => rw [map_smul]; exact Submodule.smul_mem _ _ hx

theorem exists_subquotient_subsingleton [TopologicalSpace G] [IsTopologicalGroup G] (π : Representation ℂ G V)
    (H : Subgroup G) (χ : H →* ℂˣ) (hs : IsSmooth π) (hf : HasFiniteLength π) (hn : ¬ π.IsIrreducible)
    (h1 : Module.finrank ℂ (TwJacquet π H χ) = 1)
    (hr : ∀ (S : Subrepresentation π) (v : S.toSubmodule), (v : V) ∈ twKer π H χ → v ∈ twKer S.toRepresentation H χ) :
    ∃ τ : IrrRep G, IsSubquotient τ.ρ π ∧ Subsingleton (TwJacquet τ.ρ H χ) := by
  have hq1 : Nontrivial (TwJacquet π H χ) := Module.nontrivial_of_finrank_pos (R := ℂ) (by omega)
  have hV : Nontrivial V := (Submodule.mkQ_surjective (twKer π H χ)).nontrivial
  have hbt : (⊥ : Subrepresentation π) ≠ ⊤ := by
    intro h
    obtain ⟨x, hx⟩ := exists_ne (0 : V)
    have hmem : x ∈ (⊤ : Subrepresentation π).toSubmodule := Submodule.mem_top
    rw [← h] at hmem
    exact hx ((Submodule.mem_bot ℂ).1 hmem)
  obtain ⟨S, hS0, hST⟩ : ∃ S : Subrepresentation π, S ≠ ⊥ ∧ S ≠ ⊤ := by
    by_contra hc
    push Not at hc
    exact hn { exists_pair_ne := ⟨⊥, ⊤, hbt⟩
               eq_bot_or_eq_top := fun S => (eq_or_ne S ⊥).imp_right (hc S) }
  by_cases hSK : S.toSubmodule ≤ twKer π H χ
  · let i : S.toRepresentation.IntertwiningMap π := ⟨S.toSubmodule.subtype, fun g => rfl⟩
    have hi : Function.Injective i := Subtype.val_injective
    have hsq := IsSubquotient.of_injective i hi
    have hSn : Nontrivial S.toSubmodule := Submodule.nontrivial_iff_ne_bot.2 fun h =>
      hS0 (by ext v; rw [h]; rfl)
    obtain ⟨Y, _, _, τ, hτs, hτi, q, hq⟩ := GlobalTheory.SmGL.IrrQuot.exists_irreducible_smooth_quotient S.toRepresentation
      (hsq.isSmooth hs) (GlobalTheory.ProdLength.hasFiniteLength_of_injective i hi hf) hSn
    refine ⟨⟨Y, τ, hτs, hτi⟩, ⟨S, q, hq⟩, ?_⟩
    refine Submodule.Quotient.subsingleton_iff.2 (eq_top_iff.2 fun w _ => ?_)
    obtain ⟨v, rfl⟩ := hq w
    exact apply_mem_twKer q H χ (hr S v (hSK v.2))
  · obtain ⟨s, hsS, hsK⟩ := IsConcreteLE.not_le_iff_exists.1 hSK
    have hs0 : (Submodule.mkQ (twKer π H χ)) s ≠ 0 := fun h => hsK ((Submodule.Quotient.mk_eq_zero _).1 h)
    have hline := (finrank_eq_one_iff_of_nonzero' _ hs0).1 h1
    let U : Submodule ℂ V := S.toSubmodule
    have hU : ∀ g, U ≤ U.comap (π g) := fun g v hv => S.apply_mem_toSubmodule g hv
    let σ : Representation ℂ G (V ⧸ U) := π.quotient U hU
    let p : π.IntertwiningMap σ := ⟨U.mkQ, fun g => by ext v; rfl⟩
    have hp : Function.Surjective p := Submodule.mkQ_surjective U
    have hsq := IsSubquotient.of_surjective p hp
    have hUn : Nontrivial (V ⧸ U) := Submodule.Quotient.nontrivial_iff.2 fun h =>
      hST (by ext v; rw [show S.toSubmodule = ⊤ from h]; rfl)
    have hfq : HasFiniteLength σ := IsFiniteLength.of_surjective hf
      (f := Representation.IntertwiningMap.equivLinearMapAsModule π σ p) hp
    obtain ⟨Y, _, _, τ, hτs, hτi, q, hq⟩ := GlobalTheory.SmGL.IrrQuot.exists_irreducible_smooth_quotient σ
      (hsq.isSmooth hs) hfq hUn
    refine ⟨⟨Y, τ, hτs, hτi⟩, (IsSubquotient.of_surjective q hq).trans hsq, ?_⟩
    refine Submodule.Quotient.subsingleton_iff.2 (eq_top_iff.2 fun w _ => ?_)
    obtain ⟨b, rfl⟩ := hq w
    obtain ⟨v, rfl⟩ := hp b
    obtain ⟨c, hc⟩ := hline (Submodule.mkQ _ v)
    have hk : v - c • s ∈ twKer π H χ := by
      rw [← Submodule.Quotient.mk_eq_zero, Submodule.Quotient.mk_sub, Submodule.Quotient.mk_smul]
      exact sub_eq_zero.2 hc.symm
    have hpe : p v = p (v - c • s) := by
      have h0 : p (c • s) = 0 := (Submodule.Quotient.mk_eq_zero U).2 (U.smul_mem c hsS)
      have h2 : v = (v - c • s) + c • s := by abel
      conv_lhs => rw [h2, map_add (f := _), h0, add_zero]
    rw [hpe]
    exact apply_mem_twKer q H χ (apply_mem_twKer p H χ hk)

end General

section Local

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem finrank_twJacquet_of_isCusp (hW : WhitRankIrr k) {ψ : AddChar k Circle} (hc : Continuous ψ) (h1 : ψ ≠ 1)
    {x : IrrGL (k := k)} (hx : x.IsCusp) :
    Module.finrank ℂ (TwJacquet x.rep (unipB k (Fin x.1)) (whitChar ψ x.1)) = 1 := by
  obtain ⟨d, c⟩ := x
  obtain ⟨n, rfl⟩ : ∃ n, d = n + 1 := ⟨d - 1, by have := hx.1; simp at this; omega⟩
  have hV : Nontrivial c.rep.V := by
    by_contra h
    rw [not_nontrivial_iff_subsingleton] at h
    obtain ⟨a, b, hab⟩ := c.rep.irr.exists_pair_ne
    refine hab ?_
    ext v
    rw [Subsingleton.elim v 0]
    exact ⟨fun _ => b.toSubmodule.zero_mem, fun _ => a.toSubmodule.zero_mem⟩
  have hg : IsGenericFor ψ c.rep.ρ := _root_.GlobalTheory.CompanionTheory.BZDeriv.isGenericFor_of_isCuspidal k ψ hc h1 n _ c.rep.ρ hx.2 hV
  have hle := hW ψ hc h1 (n + 1) _ c.rep.ρ c.rep.smooth c.rep.irr
  haveI : Nontrivial (TwJacquet c.rep.ρ (unipB k (Fin (n + 1))) (whitChar ψ (n + 1))) := hg
  exact Module.finrank_eq_of_rank_eq (le_antisymm hle (Cardinal.one_le_iff_pos.2 rank_pos))

theorem exists_nongeneric_subquotient : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k],
    WhitRankIrr k → ∀ (ψ : AddChar k Circle), Continuous ψ → ψ ≠ 1 →
    ∀ (x y : IrrGL (k := k)) (N : ℕ) (hd : ∑ a, (![x, y] a).1 = N), x.IsCusp → y.IsCusp →
      ¬ (prodIrr ![x, y] hd).IsIrreducible →
      ∃ τ : IrrRep (GL (Fin N) k), IsSubquotient τ.ρ (prodIrr ![x, y] hd) ∧ ¬ IsGenericFor ψ τ.ρ := by
  intro k _ _ _ _ hW ψ hc h1 x y N hd hx hy hn
  have hcusp : ∀ a, (![x, y] a).IsCusp := Fin.forall_fin_two.2 ⟨hx, hy⟩
  have hP := GlobalTheory.CompanionTheory.WhitRank.whitRankProd_of_heredity k (_root_.GlobalTheory.CompanionTheory.Rodier.whitHeredity k) ψ hc h1 2 N ![x, y] hd
  have hrank : Module.finrank ℂ (TwJacquet (prodIrr ![x, y] hd) (unipB k (Fin N)) (whitChar ψ N)) = 1 :=
    hP.trans (Finset.prod_eq_one fun a _ => finrank_twJacquet_of_isCusp hW hc h1 (hcusp a))
  have hf : HasFiniteLength (prodIrr ![x, y] hd) :=
    GlobalTheory.ProdFiniteLength.multiProd_hasFiniteLength GlobalTheory.CompanionTheory.Published.bernsteinZelevinskyFiniteness k 2 N
      (fun a => (![x, y] a).1) (fun a => GlobalTheory.SplitRead.Irr.ofIrrRep (![x, y] a).2.rep) _
  have hs := isSmooth_prodIrr ![x, y] hd
  obtain ⟨τ, hτ, hsub⟩ := exists_subquotient_subsingleton (prodIrr ![x, y] hd) (unipB k (Fin N)) (whitChar ψ N) hs hf hn hrank
    fun S v hv => by
      let i : S.toRepresentation.IntertwiningMap (prodIrr ![x, y] hd) := ⟨S.toSubmodule.subtype, fun g => rfl⟩
      exact GlobalTheory.CompanionTheory.PRep.WhitExact.twKer_whitChar_reflect k ψ hc N S.toRepresentation (prodIrr ![x, y] hd)
        ((IsSubquotient.of_injective i Subtype.val_injective).isSmooth hs) hs S.toSubmodule.subtype
        Subtype.val_injective (fun g v => rfl) v hv
  exact ⟨τ, hτ, not_nontrivial_iff_subsingleton.2 hsub⟩

end Local

end GlobalTheory.CompanionTheory.CuspPair

end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ReverseOrderedProductPermEquivStatement
section
open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.JHMult Zc Zc.Cos
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.reverse_ordered_product_perm_equiv : ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k], GlobalTheory.Published.IrreducibleAdmissibleGL → LUnlinkedComm k → ∀ {h N : ℕ} (Γ : Fin h → Segment k) (σ : Equiv.Perm (Fin h)) (y : Fin h → IrrGL (k := k)) (hd : ∑ a, (y a).1 = N) (hd' : ∑ a, (y (σ a)).1 = N), IsRevOrdered Γ → IsRevOrdered (Γ ∘ σ) → (∀ i, IsLSeg (Γ i) (y i).rep) → Nonempty ((prodIrr y hd).Equiv (prodIrr (y ∘ σ) hd')) := by
  first | exact @GlobalTheory.CompanionTheory.ReorderRev.prodIrr_equiv_of_isRevOrdered | exact GlobalTheory.CompanionTheory.ReorderRev.prodIrr_equiv_of_isRevOrdered | (intros; apply GlobalTheory.CompanionTheory.ReorderRev.prodIrr_equiv_of_isRevOrdered <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SecondCountableUnitary
section
noncomputable section

open MeasureTheory Matrix
open scoped ComplexConjugate Kronecker InnerProductSpace

namespace GlobalTheory.CompanionTheory.CxAvg

section Abstract

variable {K E : Type*} [Group K] [TopologicalSpace K] [IsTopologicalGroup K] [CompactSpace K]
  [SecondCountableTopology K] [MeasurableSpace K] [BorelSpace K]
  [NormedAddCommGroup E] [InnerProductSpace ℂ E] [FiniteDimensional ℂ E] [CompleteSpace E]
  (μ : Measure K) [μ.IsHaarMeasure] (F : K →* (E →L[ℂ] E))

variable {F}

end Abstract

section Concrete

open PositivityTheory.RgTw (Mat hb)
open PositivityTheory.RgBcC

variable {n : ℕ}

theorem Rm_unitary (lam : Fin n → ℤ) (k : Matrix.unitaryGroup (Fin n) ℂ) :
    Rm lam k.1 = LinearMap.toMatrix (wb lam) (wb lam)
      (GlobalTheory.Branching.sqRep ℂ n (dw lam) (GlobalTheory.Branching.unitaryIncl n k)) := by
  have h : IsUnit k.1.det := (Matrix.isUnit_iff_isUnit_det _).1 (GlobalTheory.Branching.unitaryIncl n k).isUnit
  have e : Matrix.nonsingInvUnit k.1 h = GlobalTheory.Branching.unitaryIncl n k := Units.ext rfl
  rw [Rm, dite_eq_left h, e]

theorem Rm_mul (lam : Fin n → ℤ) (k k' : Matrix.unitaryGroup (Fin n) ℂ) :
    Rm lam (k * k').1 = Rm lam k.1 * Rm lam k'.1 := by
  rw [Rm_unitary, Rm_unitary, Rm_unitary, map_mul, map_mul, Module.End.mul_eq_comp]
  exact LinearMap.toMatrix_comp _ _ _ _ _

theorem Rm_one (lam : Fin n → ℤ) : Rm lam (1 : Matrix.unitaryGroup (Fin n) ℂ).1 = 1 := by
  rw [Rm_unitary, map_one, map_one]
  exact LinearMap.toMatrix_id _

theorem continuous_unitaryIncl : Continuous (GlobalTheory.Branching.unitaryIncl n) := by
  rw [Units.continuous_iff]
  exact ⟨continuous_subtype_val, continuous_subtype_val.matrix_conjTranspose⟩

theorem continuous_Rm (lam : Fin n → ℤ) :
    Continuous fun k : Matrix.unitaryGroup (Fin n) ℂ => Rm lam k.1 := by
  simp only [Rm_unitary]
  refine continuous_matrix fun i j => ?_
  simp only [LinearMap.toMatrix_apply]
  exact (GlobalTheory.CompanionTheory.WInfCont.continuous_sqRep_coeff (dw lam) (wb lam j) ((wb lam).coord i)).comp
    continuous_unitaryIncl

end Concrete

end GlobalTheory.CompanionTheory.CxAvg
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SegmentRepJacquetWordMultiplicityStatement
section
open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.JHMult Zc Zc.Cos
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.segment_rep_jacquet_word_multiplicity : ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k], GlobalTheory.Published.IrreducibleAdmissibleGL → LSegJacquet k → ∀ (Γ : Segment k) {N : ℕ} {V : Type} [AddCommGroup V] [Module ℂ V] (π : Representation ℂ (GL (Fin N) k) V), IsLSeg Γ π → ∀ W : List (IrrGL (k := k)), (∀ w ∈ W, w.IsCusp) → (W = decWord Γ → jmL W π = 1) ∧ (W ≠ decWord Γ → jmL W π = 0) := by
  first | exact @GlobalTheory.CompanionTheory.FineL.jmL_cusp_word | exact GlobalTheory.CompanionTheory.FineL.jmL_cusp_word | (intros; apply GlobalTheory.CompanionTheory.FineL.jmL_cusp_word <;> assumption)
end

