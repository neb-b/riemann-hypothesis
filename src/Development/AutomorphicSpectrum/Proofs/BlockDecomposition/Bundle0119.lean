module

public import Mathlib
public import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.FormalAlgebraisation.GEClosedProj
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0002
public import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.PairSums.SumPair
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.IsIsoOfIsClosedImmersionOfThickenings
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.HodgeSurjectivity.NLeA
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.AlgebraMapConeRing

@[expose] public section

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FormalMorphismExistence
section
set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry ReciprocityTheory.ChartRestriction.G.Out PositivityTheory.FormalThickening

namespace GlobalTheory.CompanionTheory.MorphismAlgebraisation

lemma isPullback_of_sections {C : Type*} [Category C] {A A' B B' : C} {p : A ⟶ B} {q : A' ⟶ B'}
    {rA : A ⟶ A'} {rB : B ⟶ B'} {sA : A' ⟶ A} {sB : B' ⟶ B} (h : IsPullback p rA rB q)
    (hA : sA ≫ rA = 𝟙 _) (hB : sB ≫ rB = 𝟙 _) (hc : sA ≫ p = q ≫ sB) :
    IsPullback q sA sB p :=
  IsPullback.of_bot (by rw [hA, hB]; exact IsPullback.id_vert q) hc.symm h

section Graph

variable {S Se X Z Y : Scheme.{0}} (hX : X ⟶ S) (hZ : Z ⟶ S) (t : Se ⟶ S) {b : Y ⟶ X} {y : Y ⟶ Se}

def retr (h : IsPullback b y hX t) : pullback (pullback.fst hX hZ ≫ hX) t ⟶ Y :=
  h.lift (pullback.fst _ t ≫ pullback.fst hX hZ) (pullback.snd _ t)
    (by simp only [Category.assoc]; exact pullback.condition)

lemma retr_fst (h : IsPullback b y hX t) :
    retr hX hZ t h ≫ b = pullback.fst _ t ≫ pullback.fst hX hZ := h.lift_fst _ _ _

lemma retr_snd (h : IsPullback b y hX t) : retr hX hZ t h ≫ y = pullback.snd _ t :=
  h.lift_snd _ _ _

lemma isPullback_retr (h : IsPullback b y hX t) :
    IsPullback (pullback.fst (pullback.fst hX hZ ≫ hX) t) (retr hX hZ t h)
      (pullback.fst hX hZ) b :=
  IsPullback.of_bot (by rw [retr_snd]; exact IsPullback.of_hasPullback _ _)
    (retr_fst hX hZ t h).symm h

def graph (h : IsPullback b y hX t) (f : Y ⟶ Z) (hf : f ≫ hZ = y ≫ t) :
    Y ⟶ pullback (pullback.fst hX hZ ≫ hX) t :=
  pullback.lift (pullback.lift b f (by rw [hf, h.w])) y (by rw [pullback.lift_fst_assoc, h.w])

@[reassoc (attr := simp)]
lemma graph_fst_fst (h : IsPullback b y hX t) (f : Y ⟶ Z) (hf : f ≫ hZ = y ≫ t) :
    graph hX hZ t h f hf ≫ pullback.fst _ t ≫ pullback.fst hX hZ = b := by
  rw [graph, pullback.lift_fst_assoc, pullback.lift_fst]

@[reassoc (attr := simp)]
lemma graph_fst_snd (h : IsPullback b y hX t) (f : Y ⟶ Z) (hf : f ≫ hZ = y ≫ t) :
    graph hX hZ t h f hf ≫ pullback.fst _ t ≫ pullback.snd hX hZ = f := by
  rw [graph, pullback.lift_fst_assoc, pullback.lift_snd]

@[reassoc (attr := simp)]
lemma graph_snd (h : IsPullback b y hX t) (f : Y ⟶ Z) (hf : f ≫ hZ = y ≫ t) :
    graph hX hZ t h f hf ≫ pullback.snd _ t = y := by
  rw [graph, pullback.lift_snd]

lemma graph_retr (h : IsPullback b y hX t) (f : Y ⟶ Z) (hf : f ≫ hZ = y ≫ t) :
    graph hX hZ t h f hf ≫ retr hX hZ t h = 𝟙 Y := by
  apply h.hom_ext
  · simp [retr_fst]
  · simp [retr_snd]

lemma isClosedImmersion_graph [IsSeparated hZ] (h : IsPullback b y hX t) (f : Y ⟶ Z)
    (hf : f ≫ hZ = y ≫ t) : IsClosedImmersion (graph hX hZ t h f hf) := by
  have : IsSeparated (retr hX hZ t h) :=
    MorphismProperty.of_isPullback (P := @IsSeparated) (isPullback_retr hX hZ t h) inferInstance
  have : IsClosedImmersion (graph hX hZ t h f hf ≫ retr hX hZ t h) := by
    rw [graph_retr]; infer_instance
  exact IsClosedImmersion.of_comp _ (retr hX hZ t h)

lemma isPullback_graph [IsSeparated hZ] {Se' Y' : Scheme.{0}} (t' : Se' ⟶ S) {b' : Y' ⟶ X} {y' : Y' ⟶ Se'}
    (τ : Se ⟶ Se') (hτ : τ ≫ t' = t) (h : IsPullback b y hX t) (h' : IsPullback b' y' hX t')
    (β : Y ⟶ Y') (hβ : β ≫ b' = b) (hy : β ≫ y' = y ≫ τ) (f : Y ⟶ Z) (f' : Y' ⟶ Z)
    (hf : f ≫ hZ = y ≫ t) (hf' : f' ≫ hZ = y' ≫ t') (hff : β ≫ f' = f) :
    IsPullback β (graph hX hZ t h f hf) (graph hX hZ t' h' f' hf')
      (pullback.map (pullback.fst hX hZ ≫ hX) t (pullback.fst hX hZ ≫ hX) t' (𝟙 _) τ (𝟙 _)
        (by simp) (by simp [hτ])) := by
  set m := pullback.map (pullback.fst hX hZ ≫ hX) t (pullback.fst hX hZ ≫ hX) t' (𝟙 _) τ (𝟙 _)
        (by simp) (by simp [hτ]) with hm
  have m_fst : m ≫ pullback.fst _ t' = pullback.fst _ t := by
    rw [hm, pullback.map, pullback.lift_fst, Category.comp_id]
  have m_snd : m ≫ pullback.snd _ t' = pullback.snd _ t ≫ τ := by
    rw [hm, pullback.map, pullback.lift_snd]
  have sq : m ≫ retr hX hZ t' h' = retr hX hZ t h ≫ β := by
    apply h'.hom_ext
    · rw [Category.assoc, Category.assoc, hβ, retr_fst, retr_fst, reassoc_of% m_fst]
    · rw [Category.assoc, Category.assoc, hy, retr_snd, m_snd, reassoc_of% (retr_snd hX hZ t h)]
  have h0 : IsPullback m (retr hX hZ t h) (retr hX hZ t' h') β :=
    IsPullback.of_right (h₁₂ := pullback.fst _ t') (h₂₂ := b') (v₁₃ := pullback.fst hX hZ)
      (by rw [m_fst, hβ]; exact isPullback_retr hX hZ t h) sq (isPullback_retr hX hZ t' h')
  refine isPullback_of_sections h0 (graph_retr hX hZ t h f hf) (graph_retr hX hZ t' h' f' hf') ?_
  apply pullback.hom_ext
  · apply pullback.hom_ext
    · simp only [Category.assoc, m_fst, graph_fst_fst, graph_fst_fst_assoc, hβ]
    · simp only [Category.assoc, m_fst, graph_fst_snd, graph_fst_snd_assoc, hff]
  · simp only [Category.assoc, m_snd, graph_snd, graph_snd_assoc, hy]

end Graph

theorem exists_hom_of_thickenings : GEClosed → IsoOfThick →
  ∀ (R : Type) [CommRing R] [IsNoetherianRing R] (I : Ideal R), IsAdicComplete I R →
    ∀ (X Z : Over (Spec (CommRingCat.of R))), IsProper X.hom →
      IsSeparated Z.hom → LocallyOfFiniteType Z.hom → QuasiCompact Z.hom →
    ∀ (Y : ∀ e : ℕ, Over (Spec (CommRingCat.of (R ⧸ I ^ (e + 1)))))
      (β : ∀ e, (Y e).left ⟶ (Y (e + 1)).left) (b : ∀ e, (Y e).left ⟶ X.left),
      (∀ e, IsPullback (b e) (Y e).hom X.hom (thick R I e)) → (∀ e, β e ≫ b (e + 1) = b e) →
    ∀ f : ∀ e, (Y e).left ⟶ Z.left,
      (∀ e, f e ≫ Z.hom = (Y e).hom ≫ thick R I e) → (∀ e, β e ≫ f (e + 1) = f e) →
      ∃ g : X ⟶ Z, ∀ e, b e ≫ g.left = f e := by
  intro hGE hIso R _ _ I hI X Z hXp hZs hZf hZq Y β b hb hβ f hf hfβ
  let P : Over (Spec (CommRingCat.of R)) := Over.mk (pullback.fst X.hom Z.hom ≫ X.hom)
  have hPs : IsSeparated P.hom := by dsimp only [P, Over.mk_hom]; infer_instance
  have hPf : LocallyOfFiniteType P.hom := by dsimp only [P, Over.mk_hom]; infer_instance
  have hPq : QuasiCompact P.hom := by dsimp only [P, Over.mk_hom]; infer_instance
  have hth : ∀ e, IsClosedImmersion (thick R I e) := fun e =>
    IsClosedImmersion.spec_of_surjective _ Ideal.Quotient.mk_surjective
  have hy : ∀ e, β e ≫ (Y (e + 1)).hom = (Y e).hom ≫ thickTrans R I e := fun e => by
    rw [← cancel_mono (thick R I (e + 1)), Category.assoc, Category.assoc, thickTrans_comp,
      ← (hb (e + 1)).w, ← (hb e).w, ← Category.assoc, hβ]
  let i : ∀ e, (Y e).left ⟶ (thickObj R I e P).left := fun e =>
    graph X.hom Z.hom (thick R I e) (hb e) (f e) (hf e)
  have hi : ∀ e, IsClosedImmersion (i e) := fun e =>
    isClosedImmersion_graph X.hom Z.hom (thick R I e) (hb e) (f e) (hf e)
  have hiβ : ∀ e, IsPullback (β e) (i e) (i (e + 1)) (thickMap R I e P) := fun e =>
    isPullback_graph X.hom Z.hom (thick R I e) (thick R I (e + 1)) (thickTrans R I e)
      (thickTrans_comp R I e) (hb e) (hb (e + 1)) (β e) (hβ e) (hy e) (f e) (f (e + 1)) (hf e)
      (hf (e + 1)) (hfβ e)
  have hisnd : ∀ e, i e ≫ pullback.snd P.hom (thick R I e) = (Y e).hom := fun e =>
    graph_snd X.hom Z.hom (thick R I e) (hb e) (f e) (hf e)
  have hi0 : IsProper (i 0 ≫ (thickObj R I 0 P).hom) := by
    have h1 : i 0 ≫ (thickObj R I 0 P).hom = (Y 0).hom := hisnd 0
    rw [h1]
    exact MorphismProperty.of_isPullback (P := @IsProper) (hb 0) hXp
  obtain ⟨C', j, b', hj, hjp, hpb, hb'⟩ :=
    hGE R I hI P hPs hPf hPq (fun e => (Y e).left) i β hi hiβ hi0
  let Co : Over (Spec (CommRingCat.of R)) := Over.mk (j ≫ P.hom)
  let p : Co ⟶ X := Over.homMk (j ≫ pullback.fst X.hom Z.hom) (by simp [Co, P])
  have hpl : p.left = j ≫ pullback.fst X.hom Z.hom := rfl
  have hpp : IsProper p.left := by
    have h1 : IsProper (p.left ≫ X.hom) := by
      have h2 : p.left ≫ X.hom = j ≫ P.hom := by simp [hpl, P]
      rw [h2]; exact hjp
    exact IsProper.of_comp _ X.hom
  have hC : ∀ e, IsPullback (b' e) (Y e).hom Co.hom (thick R I e) := fun e => by
    have h1 := (hpb e).paste_vert (IsPullback.of_hasPullback P.hom (thick R I e))
    rw [hisnd e] at h1
    exact h1
  have hbe : ∀ e, b' e ≫ p.left = b e := fun e => by
    have h1 := (hpb e).w
    rw [hpl, reassoc_of% h1]
    exact graph_fst_fst X.hom Z.hom (thick R I e) (hb e) (f e) (hf e)
  have hiso : ∀ e, IsIso ((Over.pullback (thick R I e)).map p).left := fun e => by
    have key : (hC e).isoPullback.hom ≫ ((Over.pullback (thick R I e)).map p).left =
        (hb e).isoPullback.hom := by
      have m1 : ((Over.pullback (thick R I e)).map p).left ≫ pullback.fst X.hom (thick R I e) =
          pullback.fst Co.hom (thick R I e) ≫ p.left := pullback.lift_fst _ _ _
      have m2 : ((Over.pullback (thick R I e)).map p).left ≫ pullback.snd X.hom (thick R I e) =
          pullback.snd Co.hom (thick R I e) := pullback.lift_snd _ _ _
      apply pullback.hom_ext
      · rw [Category.assoc, m1, IsPullback.isoPullback_hom_fst_assoc, hbe,
          IsPullback.isoPullback_hom_fst]
      · rw [Category.assoc, m2, IsPullback.isoPullback_hom_snd, IsPullback.isoPullback_hom_snd]
    have h1 : IsIso ((hC e).isoPullback.hom ≫ ((Over.pullback (thick R I e)).map p).left) := by
      rw [key]; infer_instance
    exact IsIso.of_isIso_comp_left (hC e).isoPullback.hom _
  have hp : IsIso p := hIso R I hI X Co p hXp hpp hiso
  have hl : IsIso p.left := inferInstanceAs (IsIso ((Over.forget _).map p))
  have hz : j ≫ pullback.snd X.hom Z.hom ≫ Z.hom = p.left ≫ X.hom := by
    rw [hpl, Category.assoc, pullback.condition]
  refine ⟨Over.homMk (inv p.left ≫ j ≫ pullback.snd X.hom Z.hom) ?_, fun e => ?_⟩
  · simp [hz]
  · have h1 := (hpb e).w
    have h2 : b' e ≫ j ≫ pullback.snd X.hom Z.hom = f e := by
      rw [reassoc_of% h1]
      exact graph_fst_snd X.hom Z.hom (thick R I e) (hb e) (f e) (hf e)
    simp only [Over.homMk_left]
    rw [← hbe e, Category.assoc, IsIso.hom_inv_id_assoc, h2]

end GlobalTheory.CompanionTheory.MorphismAlgebraisation
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.GaloisCohomologyLocalizationExact
section
noncomputable section

open NumberField IsDedekindDomain Representation Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.Published GlobalTheory.Published.PoitouTate
  PositivityTheory.S2pt

namespace GlobalTheory.CompanionTheory.LocalPerfect

section General

variable {R : Type*} [CommRing R] [TopologicalSpace R] [DiscreteTopology R]
  {Γ : Type*} [Group Γ] {M : Type*} [AddCommGroup M] [Module R M]
  [TopologicalSpace M] [DiscreteTopology M]
  {D : Type*} [Group D] [TopologicalSpace D]
  (χ : Γ →* Rˣ) (ρ : Representation R Γ M) (φ : D →* Γ) (χ' : D →* Rˣ)

theorem twDual_comp_apply (h : χ.comp φ = χ') (g : D) (y : TDual R M) :
    ((twDual χ ρ).comp φ) g y = ((twDual χ' (ρ.comp φ)).comp (MonoidHom.id D)) g y := by
  subst h
  apply LinearMap.ext
  intro m
  change ((χ (φ g) : Rˣ) : R) * y (ρ (φ g)⁻¹ m) =
    ((χ (φ g) : Rˣ) : R) * y (ρ (φ g⁻¹) m)
  rw [map_inv φ]

def dualMap (h : χ.comp φ = χ') :
    H1 ((twDual χ ρ).comp φ) →ₗ[R] H1 ((twDual χ' (ρ.comp φ)).comp (MonoidHom.id D)) :=
  mapH1 _ _ LinearMap.id continuous_id (twDual_comp_apply χ ρ φ χ' h)

def coefMap : H1 (ρ.comp φ) →ₗ[R] H1 ((ρ.comp φ).comp (MonoidHom.id D)) :=
  mapH1 _ _ LinearMap.id continuous_id (fun _ _ => rfl)

theorem dualMap_bijective (h : χ.comp φ = χ') : Function.Bijective (dualMap χ ρ φ χ' h) := by
  refine Function.bijective_iff_has_inverse.2 ⟨mapH1 _ _ LinearMap.id continuous_id
    (fun g y => (twDual_comp_apply χ ρ φ χ' h g y).symm), fun x => ?_, fun x => ?_⟩
  · induction x using Submodule.Quotient.induction_on with
    | H z => rfl
  · induction x using Submodule.Quotient.induction_on with
    | H z => rfl

theorem coefMap_bijective : Function.Bijective (coefMap ρ φ) := by
  refine Function.bijective_iff_has_inverse.2 ⟨mapH1 ((ρ.comp φ).comp (MonoidHom.id D)) (ρ.comp φ)
    LinearMap.id continuous_id (fun _ _ => rfl), fun x => ?_, fun x => ?_⟩
  · induction x using Submodule.Quotient.induction_on with
    | H z => rfl
  · induction x using Submodule.Quotient.induction_on with
    | H z => rfl

theorem mapH2_cup_product_naturality (h : χ.comp φ = χ') (hc : ContAction (ρ.comp φ))
    (hc' : ContAction ((ρ.comp φ).comp (MonoidHom.id D)))
    (hq : ∀ (g : D) (m : R), ((charRep χ).comp φ) g m = charRep χ' g m)
    (y : H1 ((twDual χ ρ).comp φ)) (x : H1 (ρ.comp φ)) :
    mapH2 ((charRep χ).comp φ) (charRep χ') LinearMap.id continuous_id hq
        (cupH1H1TwistedDual χ ρ φ hc y x) =
      cupH1H1TwistedDual χ' (ρ.comp φ) (MonoidHom.id D) hc' (dualMap χ ρ φ χ' h y) (coefMap ρ φ x) := by
  induction y using Submodule.Quotient.induction_on with
  | H y =>
    induction x using Submodule.Quotient.induction_on with
    | H x => rfl

theorem injective_compr₂ (h : χ.comp φ = χ') (hc : ContAction (ρ.comp φ))
    (hc' : ContAction ((ρ.comp φ).comp (MonoidHom.id D)))
    (hq : ∀ (g : D) (m : R), ((charRep χ).comp φ) g m = charRep χ' g m)
    {P : H2 (charRep χ') →ₗ[R] R} (hP : Function.Injective P)
    (hL : Function.Injective (cupH1H1TwistedDual χ' (ρ.comp φ) (MonoidHom.id D) hc'))
    (hF : Function.Injective (cupH1H1TwistedDual χ' (ρ.comp φ) (MonoidHom.id D) hc').flip) :
    Function.Injective ((cupH1H1TwistedDual χ ρ φ hc).compr₂
        (P.comp (mapH2 ((charRep χ).comp φ) (charRep χ') LinearMap.id continuous_id hq))) ∧
      Function.Injective ((cupH1H1TwistedDual χ ρ φ hc).compr₂
        (P.comp (mapH2 ((charRep χ).comp φ) (charRep χ') LinearMap.id continuous_id hq))).flip := by
  have key : ∀ y x y' x', P (mapH2 ((charRep χ).comp φ) (charRep χ') LinearMap.id continuous_id hq
        (cupH1H1TwistedDual χ ρ φ hc y x)) =
      P (mapH2 ((charRep χ).comp φ) (charRep χ') LinearMap.id continuous_id hq
        (cupH1H1TwistedDual χ ρ φ hc y' x')) →
      cupH1H1TwistedDual χ' (ρ.comp φ) (MonoidHom.id D) hc' (dualMap χ ρ φ χ' h y) (coefMap ρ φ x) =
      cupH1H1TwistedDual χ' (ρ.comp φ) (MonoidHom.id D) hc' (dualMap χ ρ φ χ' h y') (coefMap ρ φ x') := by
    intro y x y' x' e
    have := hP e
    rwa [mapH2_cup_product_naturality χ ρ φ χ' h hc hc' hq, mapH2_cup_product_naturality χ ρ φ χ' h hc hc' hq] at this
  refine ⟨fun y y' e => (dualMap_bijective χ ρ φ χ' h).1 (hL (LinearMap.ext fun x => ?_)),
    fun x x' e => (coefMap_bijective ρ φ).1 (hF (LinearMap.ext fun y => ?_))⟩
  · obtain ⟨x, rfl⟩ := (coefMap_bijective ρ φ).2 x
    exact key y x y' x (LinearMap.congr_fun e x)
  · obtain ⟨y, rfl⟩ := (dualMap_bijective χ ρ φ χ' h).2 y
    exact key y x y x' (LinearMap.congr_fun e y)

end General

theorem locPerfect (F Ω : Type) [Field F] [NumberField F] [Field Ω] [Algebra F Ω]
    [IsAlgClosure F Ω] (l : ℕ) [Fact l.Prime] (r : ℕ) (M : Type) [AddCommGroup M]
    [Module (ZMod (l ^ r)) M] [Finite M] [TopologicalSpace M] [DiscreteTopology M]
    (S : Finset (HeightOneSpectrum (𝓞 F))) (Av : S → ValuationSubring Ω)
    (μ : GS Ω (S : Set (HeightOneSpectrum (𝓞 F))) →* (ZMod (l ^ r))ˣ)
    (ρ : Representation (ZMod (l ^ r)) (GS Ω (S : Set (HeightOneSpectrum (𝓞 F)))) M)
    (hρ : ContAction ρ) (hμ : μ.comp (toGS Ω _) = cycMod F Ω l r) (hT : LocalTateDuality)
    (hr : 0 < r) (inv : InvFam F Ω l r)
    (hinv : ∀ (A : ValuationSubring Ω) (v : HeightOneSpectrum (𝓞 F)), IsPlaceOver A v →
      Function.Bijective (inv A))
    (hA : ∀ v : S, IsPlaceOver (Av v) v.1) (v : S) :
    Function.Injective ((cupH1H1TwistedDual μ ρ (locFam S Av v)
        (hρ.comp' (continuous_locFam S Av v))).compr₂ (invAt S Av μ hμ inv v)) ∧
      Function.Injective ((cupH1H1TwistedDual μ ρ (locFam S Av v)
        (hρ.comp' (continuous_locFam S Av v))).compr₂ (invAt S Av μ hμ inv v)).flip := by
  have hc := hρ.comp' (continuous_locFam S Av v)
  have hχ : μ.comp (locFam S Av v) = (cycMod F Ω l r).comp (Dec (F := F) (Av v)).subtype :=
    MonoidHom.ext fun g => DFunLike.congr_fun hμ (g : G F Ω)
  obtain ⟨-, -, h1, h2, -⟩ := hT F Ω l r M (Av v) (ρ.comp (locFam S Av v)) v.1 hr (hA v) hc
  exact injective_compr₂ μ ρ (locFam S Av v) _ hχ _ (hc.comp' continuous_id)
    (locFam_apply_eq S Av μ hμ v) (hinv _ _ (hA v)).1 h1.1 h2.1

end GlobalTheory.CompanionTheory.LocalPerfect

end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsIsoOfIsClosedImmersionOfThickenings
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry ReciprocityTheory.ChartRestriction.G.Out PositivityTheory.FormalThickening

namespace GlobalTheory.CompanionTheory.FormalClosed

open GlobalTheory.ThickeningClosed

theorem mem_of_forall_mem_over_closedFibre {R : Type} [CommRing R] {I : Ideal R}
    (hI : I ≤ Ideal.jacobson ⊥) {X : Scheme.{0}} (f : X ⟶ Spec (CommRingCat.of R))
    [UniversallyClosed f] {W : Set X} (hW : IsOpen W)
    (h : ∀ x, I ≤ (f x).asIdeal → x ∈ W) (x : X) : x ∈ W := by
  by_contra hx
  have hZ : IsClosed (f '' Wᶜ) := f.isClosedMap _ hW.isClosed_compl
  obtain ⟨m, hm, hle⟩ := Ideal.exists_le_maximal (f x).asIdeal (f x).isPrime.ne_top
  let p : PrimeSpectrum (CommRingCat.of R) := ⟨m, hm.isPrime⟩
  have h1 : p ∈ closure ({f x} : Set (PrimeSpectrum (CommRingCat.of R))) :=
    (PrimeSpectrum.le_iff_mem_closure (f x) p).1 hle
  have hfx : f x ∈ f '' Wᶜ := ⟨x, hx, rfl⟩
  have hp : p ∈ f '' Wᶜ :=
    closure_minimal (Set.singleton_subset_iff.2 hfx) hZ h1
  obtain ⟨z, hz, hzp⟩ := hp
  apply hz
  apply h z
  rw [hzp]
  show I ≤ m
  refine hI.trans ?_
  unfold Ideal.jacobson
  exact sInf_le ⟨bot_le, hm⟩

theorem eq_bot_of_forall_mem_zeroLocusOpen {X : Scheme.{0}} (K : X.IdealSheafData)
    (h : ∀ x, x ∈ zeroLocusOpen K) : K = ⊥ := by
  apply Scheme.IdealSheafData.ext
  funext U
  rw [Scheme.IdealSheafData.ideal_bot]
  apply le_antisymm _ bot_le
  intro a ha
  rw [Ideal.mem_bot]
  by_contra ha0
  let J : Ideal Γ(X, U) := LinearMap.ker (LinearMap.toSpanSingleton Γ(X, U) Γ(X, U) a)
  have hJ : J ≠ ⊤ := by
    intro hJ
    apply ha0
    have h1 : (1 : Γ(X, U)) ∈ J := by rw [hJ]; exact Submodule.mem_top
    simpa [J] using h1
  obtain ⟨m, hm, hJm⟩ := Ideal.exists_le_maximal J hJ
  obtain ⟨s, hs, hsa⟩ := exists_mul_eq_zero_of_mem K U ⟨m, hm.isPrime⟩ (h _) ha
  apply hs
  apply hJm
  simpa [J] using hsa

theorem isIso_of_isClosedImmersion_of_thickenings :
    ∀ (R : Type) [CommRing R] [IsNoetherianRing R] (I : Ideal R), IsAdicComplete I R →
    ∀ (X : Over (Spec (CommRingCat.of R))), IsProper X.hom →
    ∀ (E : Scheme.{0}) (j : E ⟶ X.left), IsClosedImmersion j →
      (∀ e, ∃ h : (thickObj R I e X).left ⟶ E, h ≫ j = pullback.fst X.hom (thick R I e)) →
        IsIso j := by
  intro R _ _ I hI X hX E j hj hth
  haveI := hX
  haveI := hj
  haveI := hI
  haveI : IsLocallyNoetherian X.left := LocallyOfFiniteType.isLocallyNoetherian X.hom
  rw [IsClosedImmersion.isIso_iff_ker_eq_bot]
  apply eq_bot_of_forall_mem_zeroLocusOpen
  intro x
  refine mem_of_forall_mem_over_closedFibre (IsAdicComplete.le_jacobson_bot I) X.hom
    (isOpen_zeroLocusOpen _) ?_ x
  intro y hy
  refine mem_of_thickenings I X.hom j ?_ y hy
  intro n
  obtain ⟨l, hl⟩ := hth n
  exact ⟨l, hl⟩

end GlobalTheory.CompanionTheory.FormalClosed
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MonLNegMul
section
set_option autoImplicit false
noncomputable section
open CrystallineSemistableComparison.Onto GlobalTheory.CompanionTheory.SurjectionOntoH4

namespace GlobalTheory.CompanionTheory.SurjectionOntoH4.LaurentD

variable {K : Type} [Field K] {n d : ℕ}

theorem monL_zero' : monL K (0 : Gam n d) = 1 := rfl

theorem monL_add' (g g' : Gam n d) : monL K (g + g') = monL K g * monL K g' := by
  unfold monL
  rw [mon_mul]

theorem monL_neg_mul (g : Gam n d) : monL K (-g) * monL K g = 1 := by
  rw [← monL_add', neg_add_cancel, monL_zero']

def lam (K : Type) [Field K] {n d : ℕ} (g : Gam n d) : Ω[Lr K n d⁄K] :=
  monL K (-g) • KaehlerDifferential.D K (Lr K n d) (monL K g)

theorem lam_add (g g' : Gam n d) : lam K (g + g') = lam K g + lam K g' := by
  unfold lam
  have h1 : monL K (-(g + g')) = monL K (-g) * monL K (-g') := by
    rw [neg_add, monL_add']
  have e1 : monL K (-g) * monL K (-g') * monL K g = monL K (-g') := by
    rw [mul_comm (monL K (-g)), mul_assoc, monL_neg_mul, mul_one]
  have e2 : monL K (-g) * monL K (-g') * monL K g' = monL K (-g) := by
    rw [mul_assoc, monL_neg_mul, mul_one]
  rw [monL_add', Derivation.leibniz, smul_add, smul_smul, smul_smul, h1, e1, e2]
  exact add_comm _ _

def lamHom (K : Type) [Field K] (n d : ℕ) : Gam n d →+ Ω[Lr K n d⁄K] :=
  AddMonoidHom.mk' (lam K) lam_add

theorem exp_eq_sum (g : Gam n d) : g = ∑ e, g e • (oneE e : Gam n d) := by
  funext x
  simp [oneE, Finset.sum_apply, Pi.single_apply]

theorem lam_eq_sum (g : Gam n d) : lam K g = ∑ e, (g e) • (dl e : Ω[Lr K n d⁄K]) := by
  have h : lam K g = lamHom K n d g := rfl
  rw [h]
  conv_lhs => rw [exp_eq_sum g]
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sum]
  refine Finset.sum_congr rfl fun e _ => ?_
  rw [map_zsmul]
  rfl

theorem D_monL (g : Gam n d) :
    KaehlerDifferential.D K (Lr K n d) (monL K g) = monL K g • ∑ e, (g e) • (dl e : Ω[Lr K n d⁄K]) := by
  rw [← lam_eq_sum]
  unfold lam
  rw [smul_smul, mul_comm, monL_neg_mul, one_smul]

end GlobalTheory.CompanionTheory.SurjectionOntoH4.LaurentD
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.PiPerpCondEqAnnihilatorSumPair
section
open NumberField IsDedekindDomain Representation Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.Published GlobalTheory.Published.PoitouTate PositivityTheory.S2pt

namespace GlobalTheory.CompanionTheory.Duality

theorem pi_perpCond_eq_annihilator_sumPair : ∀ (F Ω : Type) [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] (l : ℕ) [Fact l.Prime] (r : ℕ) (M : Type) [AddCommGroup M] [Module (ZMod (l ^ r)) M] [Finite M] [TopologicalSpace M] [DiscreteTopology M] (S : Finset (HeightOneSpectrum (𝓞 F))) (Av : S → ValuationSubring Ω) (μ : GS Ω (S : Set (HeightOneSpectrum (𝓞 F))) →* (ZMod (l ^ r))ˣ) (ρ : Representation (ZMod (l ^ r)) (GS Ω (S : Set (HeightOneSpectrum (𝓞 F)))) M) (hρ : ContAction ρ), ∀ (j : ∀ v : S, H2 ((charRep μ).comp (locFam S Av v)) →ₗ[ZMod (l ^ r)] ZMod (l ^ r)), (∀ v, Function.Injective (j v)) → ∀ L : LocCond ρ (locFam S Av), Submodule.pi Set.univ (perpCond μ ρ (locFam S Av) (fun v => hρ.comp' (continuous_locFam S Av v)) L) = ⨅ x ∈ Submodule.pi Set.univ L, LinearMap.ker ((sumPair S Av μ j ρ hρ).flip x) := by
  classical
  intro F Ω _ _ _ _ _ l _ r M _ _ _ _ _ S Av μ ρ hρ j hj L
  ext y
  simp only [Submodule.mem_pi, Set.mem_univ, true_implies, forall_const, Submodule.mem_iInf, LinearMap.mem_ker,
    LinearMap.flip_apply, ReciprocityTheory.Gal.perpCond, PositivityTheory.S2pt.sumPair, Finset.sum_apply,
    LinearMap.sum_apply, LinearMap.compl₁₂_apply, LinearMap.compr₂_apply, LinearMap.proj_apply]
  constructor
  · intro h x hx
    refine Finset.sum_eq_zero fun v _ => ?_
    rw [h v (x v) (hx v), map_zero]
  · intro h v x0 hx0
    apply hj v
    rw [map_zero]
    have hs := h (Pi.single v x0) (fun w => by
      by_cases hw : w = v
      · subst hw
        simpa using hx0
      · simp [Pi.single_eq_of_ne hw])
    rw [Finset.sum_eq_single v] at hs
    · simpa using hs
    · intro w _ hw
      simp [Pi.single_eq_of_ne hw]
    · simp

end GlobalTheory.CompanionTheory.Duality
end

