module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.Bundle0004
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.EventuallyUnitaryTorusOrbitalClassTrivialLocal
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.HermitianIsometryBaseChange
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.NormClassesIffConjUnitaryTorusEllipticElements
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0225
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0219
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0021
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HasDRepIffHasDerivAt
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0226
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0260
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.Bundle0002
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0228
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0213
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0207
public import Development.AbelianVarietyTheory.Counterexamples.HeightSurvey.Bundle0003
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0171
public import Development.AbelianVarietyTheory.PublishedTheorems.DiscreteSeriesUnitary₂.Bundle0001
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0022
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0020
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0040
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0004
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0012
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0007
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0013
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0008
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.ExistsCellOfIsSubquotient
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.RadfordShufflePolynomialHolds
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0250
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0015
public import Formalism.LocalToGlobal.IndefiniteReal.LinksLemmas
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleDiscreteSeriesOfHasParam
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0003
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DsExistsOfDiscreteSeriesExists

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsCentralizerMeasuresFromUnitaryTorus
section
open MeasureTheory Set Filter Polynomial NumberField IsDedekindDomain
open GlobalTheory.AdelicU GlobalTheory.Orb GlobalTheory.AutomorphicL2Unitary Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.IndefiniteRowSideFullHecke.PlusPolynomialRoots GlobalTheory.TrEll
open GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryGroups (mapH diagH)
open scoped TensorProduct ComplexConjugate Matrix

noncomputable section

namespace GlobalTheory.TrEllMeas

open GlobalTheory.RestrMeas

theorem isHaarProd_map_all {X X' W V : Type} {Ya Ya' : W → Type} {Yf Yf' : V → Type} [Fintype W]
    [Group X] [TopologicalSpace X] [IsTopologicalGroup X] [MeasurableSpace X] [BorelSpace X]
    [Group X'] [TopologicalSpace X'] [IsTopologicalGroup X'] [MeasurableSpace X'] [BorelSpace X']
    [∀ w, Group (Ya w)] [∀ w, TopologicalSpace (Ya w)] [∀ w, IsTopologicalGroup (Ya w)]
    [∀ w, MeasurableSpace (Ya w)] [∀ w, BorelSpace (Ya w)]
    [∀ w, Group (Ya' w)] [∀ w, TopologicalSpace (Ya' w)] [∀ w, IsTopologicalGroup (Ya' w)]
    [∀ w, MeasurableSpace (Ya' w)] [∀ w, BorelSpace (Ya' w)]
    [∀ v, Group (Yf v)] [∀ v, TopologicalSpace (Yf v)] [∀ v, IsTopologicalGroup (Yf v)]
    [∀ v, MeasurableSpace (Yf v)] [∀ v, BorelSpace (Yf v)]
    [∀ v, Group (Yf' v)] [∀ v, TopologicalSpace (Yf' v)] [∀ v, IsTopologicalGroup (Yf' v)]
    [∀ v, MeasurableSpace (Yf' v)] [∀ v, BorelSpace (Yf' v)]
    {pa : ∀ w, X →* Ya w} {pf : ∀ v, X →* Yf v} {K : ∀ v, Subgroup (Yf v)}
    {pa' : ∀ w, X' →* Ya' w} {pf' : ∀ v, X' →* Yf' v} {K' : ∀ v, Subgroup (Yf' v)}
    {μa : ∀ w, Measure (Ya' w)} {μf : ∀ v, Measure (Yf' v)} {ν : Measure X'}
    (h : IsHaarProd pa' pf' K' μa μf ν) (e : X' ≃ₜ* X) (ea : ∀ w, Ya' w ≃ₜ* Ya w) (ef : ∀ v, Yf' v ≃ₜ* Yf v)
    (ha : ∀ w x, pa w (e x) = ea w (pa' w x)) (hf : ∀ v x, pf v (e x) = ef v (pf' v x))
    (hK : ∀ v, IsOpen (K v : Set (Yf v))) (hKK : ∀ᶠ v in cofinite, ∀ t, ef v t ∈ K v ↔ t ∈ K' v) :
    IsHaarProd pa pf K (fun w => (μa w).map (ea w)) (fun v => (μf v).map (ef v)) (ν.map e) := by
  obtain ⟨h1, h2, h3, h4⟩ := h
  have ma : ∀ w s, (μa w).map (ea w) s = μa w (ea w ⁻¹' s) := fun w s =>
    (ea w).toHomeomorph.toMeasurableEquiv.map_apply s
  have mf : ∀ v s, (μf v).map (ef v) s = μf v (ef v ⁻¹' s) := fun v s =>
    (ef v).toHomeomorph.toMeasurableEquiv.map_apply s
  have m : ∀ s, ν.map e s = ν (e ⁻¹' s) := fun s => e.toHomeomorph.toMeasurableEquiv.map_apply s
  obtain ⟨S₀, hS⟩ := exists_finset_of_eventually (h4.1.and hKK)
  refine ⟨fun w => (ea w).isHaarMeasure_map _, fun v => (ef v).isHaarMeasure_map _, e.isHaarMeasure_map _,
    isCylProd_of_large (K := fun v => (K v : Set (Yf v))) (fun v => (hK v).measurableSet) S₀ (fun v hv => ?_)
      (fun _ _ => rfl) fun S hs A B hA hB => ?_⟩
  · rw [mf, ← (hS v hv).1]
    exact congrArg _ (Set.ext (hS v hv).2)
  · simp only [ma, mf, m]
    rw [← h4.2 S (fun v hv => (hS v fun h' => hv (hs h')).1) _ _
      (fun w => (map_continuous (ea w)).measurable (hA w)) fun v hv => (map_continuous (ef v)).measurable (hB v hv)]
    refine congrArg ν (Set.ext fun x => ?_)
    simp only [mem_preimage, mem_cyl, ha, hf]
    exact and_congr_right fun _ => and_congr_right fun _ => forall₂_congr fun v hv =>
      (hS v fun h' => hv (hs h')).2 _

theorem isFundamentalDomain_map {T C : Type} [Group T] [TopologicalSpace T] [MeasurableSpace T] [BorelSpace T]
    [Group C] [TopologicalSpace C] [MeasurableSpace C] [BorelSpace C] (e : T ≃ₜ* C) {Γ : Subgroup T}
    {Γ' : Subgroup C} (h : ∀ t, e t ∈ Γ' ↔ t ∈ Γ) {μ : Measure T} {D : Set T} (hD : IsFundamentalDomain Γ D μ) :
    IsFundamentalDomain Γ' (e '' D) (μ.map e) ∧ μ.map e (e '' D) = μ D := by
  refine ⟨hD.image_of_equiv e.toEquiv ?_ (subEquiv e h).symm.toEquiv fun g x => ?_, ?_⟩
  · exact (MeasurePreserving.symm e.toHomeomorph.toMeasurableEquiv
      ⟨(map_continuous e).measurable, rfl⟩).quasiMeasurePreserving
  · change e (e.symm g * x) = g * e x
    rw [map_mul, e.apply_symm_apply]
  · rw [show μ.map e (e '' D) = μ (e ⁻¹' (e '' D)) from e.toHomeomorph.toMeasurableEquiv.map_apply _,
      e.injective.preimage_image]

theorem hasOrbInt_comap_congr {H : Type} [Group H] [MeasurableSpace H] {γ γ' : H} (h : γ = γ') (m μ : Measure H)
    (f : H → ℂ) (c : ℂ) : HasOrbInt μ γ (m.comap Subtype.val) f c ↔ HasOrbInt μ γ' (m.comap Subtype.val) f c := by
  subst h
  rfl

variable {F E : Type} [Field F] [Field E] [Algebra F E] (σ : E →ₐ[F] E)

theorem mapH_diagH {n : ℕ} (J : Matrix (Fin n) (Fin n) E) {k k' : Type} [CommRing k] [Algebra F k] [CommRing k']
    [Algebra F k'] (ψ : k →ₐ[F] k') (g : GRat σ J) : mapH σ J ψ (diagH σ J k g) = diagH σ J k' g := by
  refine Subtype.ext (Units.ext (Matrix.ext fun i j => ?_))
  change Algebra.TensorProduct.map ψ (AlgHom.id F E) ((1 : k) ⊗ₜ[F] g.1.1 i j) = (1 : k') ⊗ₜ[F] g.1.1 i j
  simp

theorem diagH_surjective {n : ℕ} (J : Matrix (Fin n) (Fin n) E) : Function.Surjective (diagH σ J F) := by
  intro g
  let l : F ⊗[F] E →+* E := (Algebra.TensorProduct.lid F E).toRingEquiv.toRingHom
  have hl : ∀ y, (1 : F) ⊗ₜ[F] l y = y := fun y => (Algebra.TensorProduct.lid F E).symm_apply_apply y
  have hl' : ∀ y, l ((1 : F) ⊗ₜ[F] y) = y := fun y => (Algebra.TensorProduct.lid F E).apply_symm_apply y
  refine ⟨GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryGroups.mapU (sigR F σ) (σ : E →+* E) l (fun y => ?_) (JR F J) J
    (Matrix.ext fun i j => hl' _) g, Subtype.ext (Units.ext (Matrix.ext fun i j => hl _))⟩
  conv_rhs => rw [← hl y]
  exact (hl' (σ (l y))).symm

variable [NumberField F] [NumberField E] {σ}

theorem exists_equiv (hσ : IsCMExt F E σ) {r : ℕ} {P : PPol σ r} {J : Matrix (Fin r) (Fin r) E} (hJ : IsHermND σ J)
    {k : Type} [CommRing k] [Algebra F k] [TopologicalSpace k] [IsTopologicalRing k] [T2Space k]
    {x : plusUnits P k} {φ : (k ⊗[F] Fld P) ≃ₗ[k ⊗[F] E] (Fin r → k ⊗[F] E)} (h : IsIsom P k J x.1.1 φ)
    {γ : HA k σ J} (hγ : gam h = γ) :
    ∃ e : Tor P k ≃ₜ* cent γ, (∀ t, (e t).1 = torEmb h t) ∧ ∀ (dt : Measure (Tor P k)) (x' : plusUnits P k)
      (φ' : (k ⊗[F] Fld P) ≃ₗ[k ⊗[F] E] (Fin r → k ⊗[F] E)) (h' : IsIsom P k J x'.1.1 φ'), gam h' = γ →
      ∀ μ f c, HasOrbInt μ (gam h') (centMeas h' dt) f c ↔ HasOrbInt μ γ (dt.map e) f c := by
  subst hγ
  obtain ⟨e, he, hm⟩ := _root_.GlobalTheory.TorCentTop.torEquiv_cent F E σ hσ r r P J hJ k x φ h
  refine ⟨e, he, fun dt x' φ' h' hγ μ f c => ?_⟩
  have h1 : torEmb h' = torEmb h := MonoidHom.ext fun t => by
    simpa using (GlobalTheory.TrEll.cls_conj_torus F E σ hσ r r P J hJ k x φ h x' φ' h').2.2.1 1 (by simpa using hγ) t
  rw [← hm, centMeas, centMeas, h1]
  exact hasOrbInt_comap_congr hγ _ _ _ _

theorem exists_isCentProd_torus : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (r : ℕ) (P : PPol σ r) (J : Matrix (Fin r) (Fin r) E), IsHermND σ J → ∀ (L : Submodule (𝓞 E) (Fin r → E)) [Submodule.IsFullLattice E L], ∀ γ : GRat σ J, γ.1.1.charpoly = P.1 → ∀ dta dtf dt, IsTorusMeas P dta dtf dt → ∃ ea ef e, IsCentProd L (ratEmb σ J γ) ea ef e ∧ (∃ 𝓣, IsFundamentalDomain ((ratPts σ J).subgroupOf (cent (ratEmb σ J γ))) 𝓣 e ∧ e 𝓣 = torVol P dt) ∧ (∀ (v : HeightOneSpectrum (𝓞 F)) (x : plusUnits P (Fv F v)) (φ : ((Fv F v) ⊗[F] Fld P) ≃ₗ[(Fv F v) ⊗[F] E] (Fin r → (Fv F v) ⊗[F] E)) (h : IsIsom P (Fv F v) J x.1.1 φ), gam h = proj σ J v (ratEmb σ J γ) → ∀ μ f c, HasOrbInt μ (gam h) (centMeas h (dtf v)) f c ↔ HasOrbInt μ (proj σ J v (ratEmb σ J γ)) (ef v) f c) ∧ ∀ (w : InfinitePlace F) (x : plusUnits P w.Completion) (φ : (w.Completion ⊗[F] Fld P) ≃ₗ[w.Completion ⊗[F] E] (Fin r → w.Completion ⊗[F] E)) (h : IsIsom P w.Completion J x.1.1 φ), gam h = projArch σ J w (ratEmb σ J γ) → ∀ μ f c, HasOrbInt μ (gam h) (centMeas h (dta w)) f c ↔ HasOrbInt μ (projArch σ J w (ratEmb σ J γ)) (ea w) f c := by
  intro F E _ _ _ _ _ σ hσ r P J hJ L _ γ hP dta dtf dt hdt
  obtain ⟨P', hP', _, x₀, φ₀, h₀, -, hγ₀⟩ := (_root_.GlobalTheory.TrEll.RatEll.exists_cls_of_irreducible F E σ hσ r J hJ).2 γ (hP ▸ P.2.2.1)
  obtain rfl : P = P' := Subtype.ext (hP.symm.trans hP')
  obtain ⟨xA, φA, hA, -, hγA, htA⟩ := GlobalTheory.TrEll.BaseChg.exists_isom_baseChange F E σ hσ r r P J hJ F (AF F) (Algebra.ofId F (AF F)) x₀ φ₀ h₀
  rw [hγ₀, mapH_diagH] at hγA
  replace hγA : gam hA = ratEmb σ J γ := hγA
  choose xf φf hf _ hγf htf using fun v : HeightOneSpectrum (𝓞 F) =>
    GlobalTheory.TrEll.BaseChg.exists_isom_baseChange F E σ hσ r r P J hJ (AF F) (Fv F v) (evFin F v) xA φA hA
  choose xa φa ha _ hγa hta using fun w : InfinitePlace F =>
    GlobalTheory.TrEll.BaseChg.exists_isom_baseChange F E σ hσ r r P J hJ (AF F) w.Completion (evInf F w) xA φA hA
  rw [hγA] at hγf hγa
  replace hγf : ∀ v, gam (hf v) = proj σ J v (ratEmb σ J γ) := hγf
  replace hγa : ∀ w, gam (ha w) = projArch σ J w (ratEmb σ J γ) := hγa
  haveI : T2Space (AF F) := by
    haveI : T2Space (InfiniteAdeleRing F) := inferInstanceAs (T2Space (∀ w : InfinitePlace F, w.Completion))
    haveI : T2Space (FiniteAdeleRing (𝓞 F) F) := inferInstanceAs (T2Space (RestrictedProduct
      (fun v : HeightOneSpectrum (𝓞 F) => v.adicCompletion F)
      (fun v => (v.adicCompletionIntegers F : Set (v.adicCompletion F))) cofinite))
    exact inferInstanceAs (T2Space (InfiniteAdeleRing F × FiniteAdeleRing (𝓞 F) F))
  obtain ⟨e, he, -⟩ := exists_equiv hσ hJ hA hγA
  choose ef hef hof using fun v => exists_equiv hσ hJ (hf v) (hγf v)
  choose ea hea hoa using fun w => exists_equiv hσ hJ (ha w) (hγa w)
  refine ⟨fun w => (dta w).map (ea w), fun v => (dtf v).map (ef v), dt.map e, ?_, ?_,
    fun v x φ h hγ => hof v _ x φ h hγ, fun w x φ h hγ => hoa w _ x φ h hγ⟩
  · refine isHaarProd_map_all hdt e ea ef (fun w t => Subtype.ext ?_) (fun v t => Subtype.ext ?_)
      (restrGroup_cent L _).isOpen_K ?_
    · rw [hea]
      exact (congrArg (projArch σ J w) (he t)).trans (hta w t).symm
    · rw [hef]
      exact (congrArg (proj σ J v) (he t)).trans (htf v t).symm
    · filter_upwards [_root_.GlobalTheory.TrEll.eventually_unitLoc_orbCls F E σ hσ r P J hJ L, eventually_proj_mem_stabLoc σ J L (ratEmb σ J γ)]
        with v h1 h2 t
      rw [Subgroup.mem_subgroupOf, hef]
      exact h1.2.2.1 _ _ (hf v) (hγf v ▸ h2) t
  · have := hdt.2.2.1
    have hΓ : ∀ t, e t ∈ (ratPts σ J).subgroupOf (cent (ratEmb σ J γ)) ↔ t ∈ ratPts (star' P) (one₁ P) := by
      intro t
      rw [Subgroup.mem_subgroupOf, ← range_ratEmb, ← range_ratEmb]
      constructor
      · rintro ⟨δ, hδ⟩
        have h1 : δ * γ = γ * δ := ratEmb_injective σ J (by
          rw [map_mul, map_mul, hδ]; exact mem_cent.1 (e t).2)
        letI : TopologicalSpace F := ⊥
        haveI : DiscreteTopology F := ⟨rfl⟩
        obtain ⟨e₀, he₀, -⟩ := exists_equiv hσ hJ h₀ hγ₀
        obtain ⟨s, hs⟩ := e₀.surjective ⟨diagH σ J F δ, mem_cent.2 (by rw [← map_mul, ← map_mul, h1])⟩
        obtain ⟨s, rfl⟩ := diagH_surjective (star' P) (one₁ P) s
        refine ⟨s, e.injective (Subtype.ext ?_)⟩
        have h2 := htA (diagH _ _ F s)
        rw [← he₀, hs, mapH_diagH, mapH_diagH] at h2
        rw [he, ← hδ]
        exact h2
      · rintro ⟨s, rfl⟩
        obtain ⟨δ, hδ⟩ := diagH_surjective σ J (torEmb h₀ (diagH _ _ F s))
        have h2 := htA (diagH _ _ F s)
        rw [← hδ, mapH_diagH, mapH_diagH] at h2
        exact ⟨δ, ((he _).trans h2).symm⟩
    have hD := isFundamentalDomain_stdDom (ratPts (star' P) (one₁ P)) dt
    obtain ⟨h1, h2⟩ := isFundamentalDomain_map e hΓ hD
    exact ⟨_, h1, h2.trans (quotMeasure_univ hD).symm⟩

end GlobalTheory.TrEllMeas
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsCommonLevelGrowthExponentGKMap
section
open Classical Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory NumberField Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.GKUnif

variable {D : D7} {V : HSp D} {S : D.what₂.Tau → SPar}

def Good (θ : InfFam D) (V : HSp D) (U : Subgroup (GA D V)) (N : ℕ) (φ : GA D V → ℂ) : Prop :=
  (∀ k ∈ U, k ∈ GfC V → ∀ g, φ (g * k) = φ g) ∧ ∀ d, GlobalTheory.Size.growthSob θ V d N φ ≠ ⊤

variable {θ : InfFam D} {U : Subgroup (GA D V)} {N : ℕ} {φ ψ : GA D V → ℂ}

theorem good_add (hs : φ ∈ GlobalTheory.Mem.AutSpace.SmFun θ V) (hs' : ψ ∈ GlobalTheory.Mem.AutSpace.SmFun θ V)
    (h : Good θ V U N φ) (h' : Good θ V U N ψ) : Good θ V U N (φ + ψ) :=
  ⟨fun k hk hk' g => by simp only [Pi.add_apply, h.1 k hk hk' g, h'.1 k hk hk' g],
    fun d => ne_top_of_le_ne_top (ENNReal.add_ne_top.2 ⟨h.2 d, h'.2 d⟩) (GlobalTheory.Size.growthSob_add_le hs hs' d N)⟩

theorem good_smul (c : ℂ) (h : Good θ V U N φ) : Good θ V U N (c • φ) :=
  ⟨fun k hk hk' g => by simp only [Pi.smul_apply, h.1 k hk hk' g],
    fun d => by rw [GlobalTheory.Size.growthSob_smul]; exact ENNReal.mul_ne_top enorm_ne_top (h.2 d)⟩

theorem good_zero : Good θ V U N 0 := by
  have h := good_smul (θ := θ) (U := U) (N := N) (φ := 0) 0
  rw [zero_smul] at h
  refine h ⟨fun _ _ _ _ => rfl, fun d => ?_⟩
  have e := GlobalTheory.Size.growthSob_smul (θ := θ) (V := V) (φ := 0) 0 d N
  rw [zero_smul, enorm_zero, zero_mul] at e
  rw [e]; exact ENNReal.zero_ne_top

theorem good_Rder (hθ : IsInfFam θ) (hs : φ ∈ GlobalTheory.Mem.AutSpace.SmFun θ V) {τ : D.what₂.Tau}
    {X : Matrix (Fin V.rank) (Fin V.rank) ℂ} (hX : X ∈ lieAt V τ) (h : Good θ V U N φ) :
    Good θ V U N (Rder θ V τ X φ) := by
  refine ⟨fun k hk hk' g => ?_, fun d => ?_⟩
  · have e : rTr V k φ = φ := funext (h.1 k hk hk')
    have := congrFun (GlobalTheory.Size.Rder_rTr_fin (θ := θ) hk' τ X φ) g
    rw [e] at this
    exact this.symm
  · rw [← GlobalTheory.SmoothAutCheck.RderC_eq θ V τ hX φ]
    have hB : ∀ a b, ‖X a b‖ₑ ≤ ∑ a', ∑ b', ‖X a' b'‖ₑ := fun a b =>
      (Finset.single_le_sum (f := fun b' => ‖X a b'‖ₑ) (fun _ _ => zero_le) (Finset.mem_univ b)).trans
        (Finset.single_le_sum (f := fun a' => ∑ b', ‖X a' b'‖ₑ) (fun _ _ => zero_le) (Finset.mem_univ a))
    refine ne_top_of_le_ne_top ?_ (GlobalTheory.Size.Translate.growthSob_RderC_le hθ hs τ hB d N)
    refine ENNReal.mul_ne_top (ENNReal.natCast_ne_top _) (ENNReal.mul_ne_top ?_ (h.2 (d + 1)))
    exact ENNReal.sum_ne_top.2 fun _ _ => ENNReal.sum_ne_top.2 fun _ _ => enorm_ne_top

theorem good_rTr (hθ : IsInfFam θ) (hs : φ ∈ GlobalTheory.Mem.AutSpace.SmFun θ V) {h : GA D V} (hh : h ∈ GinfC V)
    (hg : Good θ V U N φ) : Good θ V U N (rTr V h φ) := by
  refine ⟨fun k hk hk' g => ?_, fun d => ?_⟩
  · show φ (g * k * h) = φ (g * h)
    rw [mul_assoc, ← GlobalTheory.PointAtPlaceHom.comm_of_mem V hh hk', ← mul_assoc, hg.1 k hk hk']
  · obtain ⟨C, m, hC⟩ := GlobalTheory.Size.Translate.growthSob_rTr_le D θ hθ V d N
    exact ne_top_of_le_ne_top (ENNReal.mul_ne_top (ENNReal.mul_ne_top ENNReal.coe_ne_top ENNReal.ofReal_ne_top)
      (hg.2 d)) (hC h hh φ hs)

theorem conj_mem_lieSet (M : DSModel V S) (τ : D.what₂.Tau) {X : Matrix (Fin V.rank) (Fin V.rank) ℂ}
    (hX : X ∈ lieAt V τ) : M.fr τ * X * (M.fr τ)⁻¹ ∈ GlobalTheory.SmoothGlob.lieSet (M.ε τ) := by
  have hX' : Xᴴ * gramAt D V τ + gramAt D V τ * X = 0 := hX
  rw [← M.fr_gram τ] at hX'
  have hd := (Matrix.isUnit_iff_isUnit_det _).1 (M.fr_unit τ)
  have h2 : M.fr τ * (M.fr τ)⁻¹ = 1 := Matrix.mul_nonsing_inv _ hd
  have hc : ∀ Y : Matrix (Fin V.rank) (Fin V.rank) ℂ, ((M.fr τ)⁻¹)ᴴ * ((M.fr τ)ᴴ * Y) = Y := fun Y => by
    rw [← Matrix.mul_assoc, ← Matrix.conjTranspose_mul, Matrix.mul_nonsing_inv _ hd, Matrix.conjTranspose_one,
      Matrix.one_mul]
  show (M.fr τ * X * (M.fr τ)⁻¹)ᴴ * Formalism.REAL.Jm (M.ε τ) + Formalism.REAL.Jm (M.ε τ) * (M.fr τ * X * (M.fr τ)⁻¹) = 0
  have e : (M.fr τ * X * (M.fr τ)⁻¹)ᴴ * Formalism.REAL.Jm (M.ε τ) + Formalism.REAL.Jm (M.ε τ) * (M.fr τ * X * (M.fr τ)⁻¹) =
      ((M.fr τ)⁻¹)ᴴ * (Xᴴ * ((M.fr τ)ᴴ * Formalism.REAL.Jm (M.ε τ) * M.fr τ) +
        (M.fr τ)ᴴ * Formalism.REAL.Jm (M.ε τ) * M.fr τ * X) * (M.fr τ)⁻¹ := by
    simp only [Matrix.conjTranspose_mul, Matrix.mul_add, Matrix.add_mul, Matrix.mul_assoc, h2, Matrix.mul_one, hc]
  rw [e, hX', Matrix.mul_zero, Matrix.zero_mul]

theorem dRep_mem_kFin (hHC : GlobalTheory.Published.HarishChandraModules) (M : DSModel V S) (τ : D.what₂.Tau)
    {X : Matrix (Fin V.rank) (Fin V.rank) ℂ} (hX : X ∈ lieAt V τ) {w : M.H τ}
    (hw : w ∈ GlobalTheory.IndefiniteRowSideFullHecke.KTypeExtension.kFin M τ) : dRep (M.rep τ) X w ∈ GlobalTheory.IndefiniteRowSideFullHecke.KTypeExtension.kFin M τ := by
  haveI : CompleteSpace (M.H τ) := (M.ds τ).1
  have hstd := GlobalTheory.TypeSum.std_of_isDS hHC (M.ds τ)
  have hd : dRep (M.rep τ) X w = dRep (M.σ τ) (M.fr τ * X * (M.fr τ)⁻¹) w := by
    unfold dRep
    congr 1
    funext t
    show M.σ τ (M.fr τ * NormedSpace.exp (t • X) * (M.fr τ)⁻¹) w = _
    rw [← Matrix.exp_conj _ _ (M.fr_unit τ), Matrix.mul_smul, Matrix.smul_mul]
  rw [hd]
  exact GlobalTheory.TypeSum.isKFin_dRep _ _ _ _ hstd w hw _ (conj_mem_lieSet M τ hX)

end GlobalTheory.GKUnif

namespace GlobalTheory.GKUnif

theorem exists_level_exponent : GlobalTheory.Published.HarishChandraModules → ∀ (D : D7) (θ : InfFam D), IsInfFam θ →
    ∀ (V : HSp D) (S : D.what₂.Tau → SPar) (M : DSModel V S) (J : Set (GA D V)) (χ : GA D V → ℂ) (μ : Measure (GA D V))
    (𝓕 : Set (GA D V)) (T₀ : GlobalTheory.IndefiniteRowSideFullHecke.KTypeExtension.KMap M), GlobalTheory.IndefiniteRowSideFullHecke.KTypeExtension.IsGKMap θ M J χ μ 𝓕 T₀ →
    ∃ (U : Subgroup (GA D V)) (N : ℕ), IsOpen (U : Set (GA D V)) ∧
      ∀ u, (∀ k ∈ U, k ∈ GfC V → ∀ g, T₀ u (g * k) = T₀ u g) ∧ ∀ d, GlobalTheory.Size.growthSob θ V d N (T₀ u) ≠ ⊤ := by
  intro hHC D θ hθ V S M J χ μ 𝓕 T₀ hT₀
  have hne : ∀ τ, ∃ w : GlobalTheory.IndefiniteRowSideFullHecke.KTypeExtension.kFin M τ, w ≠ 0 := fun τ => by
    obtain ⟨x, hx, hx0⟩ := (Submodule.ne_bot_iff _).1 (GlobalTheory.IndefiniteRowSideFullHecke.KTypeExtension.kFin_ne_bot M τ)
    exact ⟨⟨x, hx⟩, fun h => hx0 (congrArg Subtype.val h)⟩
  choose u₀ hu₀ using hne
  obtain ⟨U, hU, hUl⟩ := (hT₀.1 u₀).level
  obtain ⟨N, hN⟩ := GlobalTheory.Size.exists_growthSob_ne_top (hT₀.2.1 u₀) (hT₀.2.2.2.2.1 u₀)
  have hsm : ∀ u, T₀ u ∈ GlobalTheory.Mem.AutSpace.SmFun θ V := hT₀.2.1
  suffices key : ∀ s : Finset D.what₂.Tau, ∀ u : GlobalTheory.IndefiniteRowSideFullHecke.KTypeExtension.KVec M, (∀ τ ∉ s, u τ = u₀ τ) →
      Good θ V U N (T₀ u) from
    ⟨U, N, hU, fun u => key Finset.univ u (fun τ h => absurd (Finset.mem_univ τ) h)⟩
  intro s
  induction s using Finset.induction_on with
  | empty =>
    intro u hu
    have : u = u₀ := funext fun τ => hu τ (Finset.notMem_empty τ)
    subst this
    exact ⟨hUl, hN⟩
  | insert τ s hτ ih =>
    intro u hu
    let Wk : Submodule ℂ (GlobalTheory.IndefiniteRowSideFullHecke.KTypeExtension.kFin M τ) :=
      { carrier := {w | Good θ V U N (T₀ (Function.update u τ w))}
        add_mem' := fun {a b} ha hb => by
          show Good θ V U N (T₀ (Function.update u τ (a + b)))
          rw [T₀.map_update_add]
          exact good_add (hsm _) (hsm _) ha hb
        zero_mem' := by
          show Good θ V U N (T₀ (Function.update u τ 0))
          rw [T₀.map_update_zero]
          exact good_zero
        smul_mem' := fun c a ha => by
          show Good θ V U N (T₀ (Function.update u τ (c • a)))
          rw [T₀.map_update_smul]
          exact good_smul c ha }
    let W : Submodule ℂ (M.H τ) := Wk.map (GlobalTheory.IndefiniteRowSideFullHecke.KTypeExtension.kFin M τ).subtype
    have hmemW : ∀ y : GlobalTheory.IndefiniteRowSideFullHecke.KTypeExtension.kFin M τ, y ∈ Wk → (y : M.H τ) ∈ W := fun y hy => ⟨y, hy, rfl⟩
    have hWk : ∀ w ∈ W, ∃ y : GlobalTheory.IndefiniteRowSideFullHecke.KTypeExtension.kFin M τ, y ∈ Wk ∧ (y : M.H τ) = w := by
      rintro w ⟨y, hy, rfl⟩
      exact ⟨y, hy, rfl⟩
    have hle : W ≤ GlobalTheory.IndefiniteRowSideFullHecke.KTypeExtension.kFin M τ := Submodule.map_subtype_le _ _
    have hlie : ∀ X ∈ lieAt V τ, ∀ w ∈ W, dRep (M.rep τ) X w ∈ W := by
      intro X hX w hw
      obtain ⟨y, hy, rfl⟩ := hWk w hw
      let y' : GlobalTheory.IndefiniteRowSideFullHecke.KTypeExtension.kFin M τ := ⟨dRep (M.rep τ) X y, dRep_mem_kFin hHC M τ hX y.2⟩
      refine hmemW y' ?_
      have e := hT₀.2.2.2.2.2.2.2 τ X hX (Function.update u τ y) y' (by simp [y'])
      rw [Function.update_idem] at e
      show Good θ V U N (T₀ (Function.update u τ y'))
      rw [e]
      exact good_Rder hθ (hsm _) hX hy
    have hK : ∀ k ∈ GlobalTheory.IndefiniteRowSideFullHecke.KTypeExtension.maxCpt M τ, ∀ w ∈ W, M.rep τ k w ∈ W := by
      intro k hk w hw
      obtain ⟨y, hy, rfl⟩ := hWk w hw
      let y' : GlobalTheory.IndefiniteRowSideFullHecke.KTypeExtension.kFin M τ := ⟨M.rep τ k y, GlobalTheory.IndefiniteRowSideFullHecke.KTypeExtension.rep_mem_kFin M τ hk y.2⟩
      refine hmemW y' ?_
      have e := hT₀.2.2.2.2.2.2.1 τ k hk (Function.update u τ y) y' (by simp [y'])
      rw [Function.update_idem] at e
      show Good θ V U N (T₀ (Function.update u τ y'))
      rw [e]
      exact good_rTr hθ (hsm _) (GlobalTheory.PointAtPlaceHom.atTau_mem V τ k) hy
    have h0 : u₀ τ ∈ Wk := by
      show Good θ V U N (T₀ (Function.update u τ (u₀ τ)))
      refine ih _ fun τ' h' => ?_
      by_cases e : τ' = τ
      · subst e; simp
      · rw [Function.update_of_ne e]
        exact hu τ' (by simp [e, h'])
    have hWne : W ≠ ⊥ := fun hb => hu₀ τ (Subtype.ext (by
      have := hmemW _ h0
      rw [hb] at this
      simpa using this))
    have hall := _root_.GlobalTheory.HCModIrred.kFin_le_of_stable hHC D V S M τ W hle hlie hK hWne
    obtain ⟨y, hy, hyu⟩ := hWk _ (hall (u τ).2)
    have : y = u τ := Subtype.ext hyu
    subst this
    have e : Function.update u τ (u τ) = u := Function.update_eq_self τ u
    have hy' : Good θ V U N (T₀ (Function.update u τ (u τ))) := hy
    rwa [e] at hy'

end GlobalTheory.GKUnif

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsFinsetSumTranslatesFixedCompactSubgroup
section
open MeasureTheory Set Filter NumberField IsDedekindDomain
open GlobalTheory.AdelicU GlobalTheory.OpTrace GlobalTheory.Orb GlobalTheory.AutomorphicL2Unitary GlobalTheory.AutMult Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Mult
open GlobalTheory.IndefiniteRowSideFullHecke.PlusPolynomialRoots (IsTestData PPol Tor Phi PhiOK PhiReal ellKernel Gap NoFixed IsLatticeConj GeomExpansion EllipticPart TraceEq)
open GlobalTheory.PRep (IsAdmissible)
open GlobalTheory.TrMult
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open scoped InnerProductSpace
open Formalism.MainNotions.KudlaSiegelWeil (Restr)

namespace GlobalTheory

theorem exists_finset_sum_translate_fixed {G X : Type} [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] [AddCommGroup X] [Module ℂ X] (ρ : Representation ℂ G X)
    (K : Subgroup G) (hK : IsCompact (K : Set G)) (x : X) (hx : IsOpen {g | ρ g x = x}) :
    ∃ s : Finset G, (∀ g ∈ s, g ∈ K) ∧ s.Nonempty ∧
      ∀ k ∈ K, ρ k (∑ g ∈ s, ρ g x) = ∑ g ∈ s, ρ g x := by
  classical
  have hmul : ∀ (a b : G) (y : X), ρ (a * b) y = ρ a (ρ b y) := fun a b y => by
    rw [map_mul, Module.End.mul_apply]
  have hinv : ∀ (a : G) (y : X), ρ a⁻¹ (ρ a y) = y := fun a y => by
    rw [← hmul, inv_mul_cancel, map_one, Module.End.one_apply]
  have hinv' : ∀ (a : G) (y : X), ρ a (ρ a⁻¹ y) = y := fun a y => by
    rw [← hmul, mul_inv_cancel, map_one, Module.End.one_apply]
  obtain ⟨t, ht⟩ := hK.elim_finite_subcover
    (fun i : K => (fun g => (i : G)⁻¹ * g) ⁻¹' {g | ρ g x = x})
    (fun i => hx.preimage (continuous_const.mul continuous_id))
    (fun k hk => Set.mem_iUnion.2 ⟨⟨k, hk⟩, show ρ (k⁻¹ * k) x = x by
      rw [inv_mul_cancel, map_one, Module.End.one_apply]⟩)
  let F : Finset X := t.image (fun i : K => ρ (i : G) x)
  have hFmem : ∀ y, y ∈ F ↔ ∃ k ∈ K, ρ k x = y := by
    intro y
    constructor
    · intro hy
      obtain ⟨i, -, rfl⟩ := Finset.mem_image.1 hy
      exact ⟨i, i.2, rfl⟩
    · rintro ⟨k, hk, rfl⟩
      obtain ⟨i, hi, hki⟩ := Set.mem_iUnion₂.1 (ht hk)
      refine Finset.mem_image.2 ⟨i, hi, ?_⟩
      have h1 : ρ ((i : G)⁻¹ * k) x = x := hki
      calc ρ (i : G) x = ρ (i : G) (ρ ((i : G)⁻¹ * k) x) := by rw [h1]
        _ = ρ k x := by rw [← hmul, mul_inv_cancel_left]
  let f : X → G := fun y => if h : ∃ k ∈ K, ρ k x = y then h.choose else 1
  have hf : ∀ y ∈ F, f y ∈ K ∧ ρ (f y) x = y := by
    intro y hy
    have h := (hFmem y).1 hy
    simp only [f, dif_pos h]
    exact h.choose_spec
  refine ⟨F.image f, ?_, ?_, ?_⟩
  · intro g hg
    obtain ⟨y, hy, rfl⟩ := Finset.mem_image.1 hg
    exact (hf y hy).1
  · exact Finset.Nonempty.image ⟨x, (hFmem x).2 ⟨1, K.one_mem, by
      rw [map_one, Module.End.one_apply]⟩⟩ f
  · have hsum : ∑ g ∈ F.image f, ρ g x = ∑ y ∈ F, y := by
      rw [Finset.sum_image]
      · exact Finset.sum_congr rfl (fun y hy => (hf y hy).2)
      · intro y hy y' hy' h
        rw [← (hf y hy).2, ← (hf y' hy').2]
        exact congrArg (fun g => ρ g x) h
    intro k hk
    set_option synthInstance.maxHeartbeats 100000 in
      rw [hsum, map_sum]
    refine Finset.sum_nbij' (fun y => ρ k y) (fun y => ρ k⁻¹ y) ?_ ?_ ?_ ?_ (fun _ _ => rfl)
    · intro y hy
      obtain ⟨k', hk', rfl⟩ := (hFmem y).1 hy
      exact (hFmem _).2 ⟨k * k', K.mul_mem hk hk', hmul _ _ _⟩
    · intro y hy
      obtain ⟨k', hk', rfl⟩ := (hFmem y).1 hy
      exact (hFmem _).2 ⟨k⁻¹ * k', K.mul_mem (K.inv_mem hk) hk', hmul _ _ _⟩
    · intro y _
      exact hinv k y
    · intro y _
      exact hinv' k y

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsOrthogonalSumTestGridOfLevelChoiceGridStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.ChiGrid GlobalTheory.GridJoin
open scoped Pointwise TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_extensionData_antiDiagonalSignGram_of_lat_eq : ∀ {D : D7} (A B : GlobalTheory.Grid.Node D) {c : ℕ} {ε : D.host.E} (d : GlobalTheory.ChiGrid.HermitianOrthogonalExtensionData A.V B.V c ε) (𝔟 : Fin c → GlobalTheory.Grid.FrId D), (ε = 1 ∨ ε = -1) → B.Λ = d.lat A.Λ 𝔟 → ∃ d' : GlobalTheory.Grid.HermitianOrthogonalExtensionData A B c, d'.ι = d.ι ∧ d'.Is (fun p q => GlobalTheory.ChiGrid.antiDiagonalSignGramMatrix c ε p q) 𝔟 := by
  first | exact @GlobalTheory.GridJoin.exists_orthogonalSum_testGrid_of_levelChoiceGrid | exact GlobalTheory.GridJoin.exists_orthogonalSum_testGrid_of_levelChoiceGrid | (intros; apply GlobalTheory.GridJoin.exists_orthogonalSum_testGrid_of_levelChoiceGrid <;> assumption)
end

