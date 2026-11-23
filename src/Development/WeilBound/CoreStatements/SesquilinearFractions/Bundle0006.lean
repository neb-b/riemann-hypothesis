module

public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsTransition
public import Development.WeilBound.CoreStatements.SesquilinearFractions.Bundle0003
public import Development.WeilBound.CoreStatements.SesquilinearFractions.Bundle0005
public import Development.WeilBound.CoreStatements.SesquilinearFractions.FrameBCLin
public import Mathlib
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0028
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle0004
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsGrpPullback
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle0001
public import Development.WeilBound.CoreStatements.HomogeneousNonvanishing.LieFree
public import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.Bundle0014
public import Development.AutomorphicSpectrum.Definitions.AdelicLattices.FactPrimes
public import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.LatNormGrLatNeZeroOfSpan
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0096

@[expose] public section

-- bundled from Development.WeilBound.CoreStatements.SesquilinearFractions.GFrameBC
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Matrix GlobalTheory GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl
open scoped ComplexOrder

namespace PositivityTheory.Xgf.EigenspaceComposition

theorem epi_spMap {K L : Type} [Field K] [Field L] (a : K →+* L) : Epi (spMap a) := by
  constructor
  intro X g₁ g₂ h
  obtain ⟨⟨x₁, φ₁⟩, rfl⟩ := (Scheme.SpecToEquivOfField K X).symm.surjective g₁
  obtain ⟨⟨x₂, φ₂⟩, rfl⟩ := (Scheme.SpecToEquivOfField K X).symm.surjective g₂
  have h' : (Scheme.SpecToEquivOfField L X).symm ⟨x₁, φ₁ ≫ CommRingCat.ofHom a⟩ =
      (Scheme.SpecToEquivOfField L X).symm ⟨x₂, φ₂ ≫ CommRingCat.ofHom a⟩ := by
    simpa [Scheme.SpecToEquivOfField, spMap, Spec.map_comp, Category.assoc] using h
  have h'' := (Scheme.SpecToEquivOfField L X).symm.injective h'
  rw [Scheme.SpecToEquivOfField_eq_iff] at h''
  obtain ⟨e, he⟩ := h''
  dsimp only at e he
  subst e
  have hφ : φ₁ = φ₂ := by
    ext z
    have hz := congrArg (fun m => m.hom z) he
    simp at hz
    exact a.injective hz
  rw [hφ]

theorem one_left' {S : Scheme.{0}} (G : Over S) [GrpObj G] (Y : Over S) :
    (1 : Y ⟶ G).left = Y.hom ≫ (η[G] : 𝟙_ (Over S) ⟶ G).left := by
  rw [Hom.one_def, Over.comp_left]
  congr 1

end PositivityTheory.Xgf.EigenspaceComposition

namespace PositivityTheory.Xgf

private theorem isTanAt_base_change_iff {S : Scheme.{0}} (G : Over S) [GrpObj G] {F F' : Type} [Field F] [Field F']
    (f : F →+* F') (x : Sp F ⟶ S) (x' : Sp F' ⟶ S) (hx : x' = spMap f ≫ x)
    (w : epsAt x ⟶ G) (w' : epsAt x' ⟶ G) (hw : w'.left = spMap (dualMap f) ≫ w.left) :
    IsTanAt G x' w' ↔ IsTanAt G x w := by
  have key : Spec.map (CommRingCat.ofHom (TrivSqZeroExt.fstHom F' F' F').toRingHom) ≫ spMap (dualMap f) =
      spMap f ≫ Spec.map (CommRingCat.ofHom (TrivSqZeroExt.fstHom F F F).toRingHom) := by
    simp only [spMap, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
    congr 2
    apply RingHom.ext
    intro a
    simp [dualMap]
  haveI := EigenspaceComposition.epi_spMap f
  show _ = (1 : Over.mk x' ⟶ G).left ↔ _ = (1 : Over.mk x ⟶ G).left
  rw [EigenspaceComposition.one_left', EigenspaceComposition.one_left', hw, ← Category.assoc, key, Category.assoc]
  simp only [Over.mk_hom, hx, Category.assoc]
  constructor
  · intro h
    exact (cancel_epi (spMap f)).mp h
  · intro h
    rw [h]

open PositivityTheory.Xgf.EigenspaceComposition in
theorem tangent_vectors_base_change : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (S : Scheme.{0}) (t : SAB H S) (F F' : Type) [Field F] [Field F'] (f : F →+* F') (x : Sp F ⟶ S) (x' : Sp F' ⟶ S) (τ : 𝓞 E →+* F) (n : ℕ) (v : Fin n → (epsAt x ⟶ t.G)), x' = spMap f ≫ x → (∃ v' : Fin n → (epsAt x' ⟶ t.G), ∀ k, (v' k).left = spMap (dualMap f) ≫ (v k).left) ∧ ∀ v' : Fin n → (epsAt x' ⟶ t.G), (∀ k, (v' k).left = spMap (dualMap f) ≫ (v k).left) → (IsEigFrame t.act x τ v ↔ IsEigFrame t.act x' (f.comp τ) v') := by
  intro E _ _ _ H S t F F' _ _ f x x' τ n v hx'
  have hcomp : ∀ w : epsAt x ⟶ t.G, ∃ w' : epsAt x' ⟶ t.G, w'.left = spMap (dualMap f) ≫ w.left := by
    intro w
    refine ⟨Over.homMk (spMap (dualMap f) ≫ w.left) ?_, rfl⟩
    rw [Category.assoc, Over.w w]
    simp only [epsAt, Over.mk_hom, hx', spMap, ← Category.assoc, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
    congr 3
    apply RingHom.ext
    intro a
    simp [dualMap, TrivSqZeroExt.algebraMap_eq_inl]
  refine ⟨⟨fun k => Classical.choose (hcomp (v k)), fun k => Classical.choose_spec (hcomp (v k))⟩, ?_⟩
  intro v' hv'
  have htan : ∀ k, IsTanAt t.G x' (v' k) ↔ IsTanAt t.G x (v k) :=
    fun k => isTanAt_base_change_iff t.G f x x' hx' (v k) (v' k) (hv' k)
  by_cases hT : ∀ k, IsTanAt t.G x (v k)
  · obtain ⟨N, M, ρ, hρ, hbc⟩ := lie_model_action_base_change E H S t F x
    obtain ⟨M', ρ', hρ', hpt, hc⟩ := hbc F' f x' hx'
    choose u hu using fun k => M.onto (v k) (hT k)
    have hv'eq : v' = fun k => M'.pt (f ∘ u k) := by
      funext k
      apply Over.OverMorphism.ext
      rw [hv' k, hpt, hu k]
    have hveq : v = fun k => M.pt (u k) := funext fun k => (hu k).symm
    rw [hv'eq, hveq, ((lie_model_eigenvectors_action S F t.G x _ M).2 _ t.act ρ τ hρ).2 n u,
      ((lie_model_eigenvectors_action S F' t.G x' _ M').2 _ t.act ρ' (f.comp τ) hρ').2 n (fun k => f ∘ u k)]
    exact EigenspaceComposition.core (τ := τ) hc u
  · push_neg at hT
    obtain ⟨k, hk⟩ := hT
    constructor
    · intro h
      exact absurd (h.1 k).1 hk
    · intro h
      exact absurd ((htan k).1 (h.1 k).1) hk

end PositivityTheory.Xgf
end

-- bundled from Development.WeilBound.CoreStatements.SesquilinearFractions.GLieInt
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Matrix GlobalTheory GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl
open scoped ComplexOrder

noncomputable section

namespace PositivityTheory.Xgf.isogeny_decomposition_product

theorem tan_comp {S : Scheme.{0}} {R : Type} [CommRing R] {A B : Over S} [GrpObj A] [GrpObj B] {x : Sp R ⟶ S}
    (t : epsAt x ⟶ A) (ht : IsTanAt A x t) (g : A ⟶ B) [IsMonHom g] : IsTanAt B x (t ≫ g) := by
  unfold IsTanAt at ht ⊢
  rw [Over.comp_left, ← Category.assoc, ht, ← Over.comp_left, MonObj.one_comp]

theorem one_left {S : Scheme.{0}} {X A : Over S} [GrpObj A] : (1 : X ⟶ A).left = X.hom ≫ η[A].left := by
  rw [Hom.one_def]; simp

theorem spMap_comp {A B C : Type} [CommRing A] [CommRing B] [CommRing C] (a : A →+* B) (b : B →+* C) :
    spMap b ≫ spMap a = spMap (b.comp a) := by
  simp [spMap, ← Spec.map_comp]

theorem bc_one {R V : Type} [CommRing R] [CommRing V] (f : R →+* V) {A : Over (Sp R)} [GrpObj A] :
    spMap (dualMap f) ≫ (1 : epsR R ⟶ A).left = (1 : epsAt (spMap f ≫ 𝟙 (Sp R)) ⟶ A).left := by
  rw [one_left, one_left, ← Category.assoc]
  congr 1
  simp only [Over.mk_hom, Category.comp_id]
  rw [spMap_comp, spMap_comp]
  congr 1
  ext a <;> simp [dualMap, TrivSqZeroExt.algebraMap_eq_inl]

theorem bc_eps {R V : Type} [CommRing R] [CommRing V] (f : R →+* V) (N : ℕ) :
    spMap (dualMap f) ≫ spMap (GlobalTheory.CompanionTheory.Ar.epsMul (N : R)) = spMap (GlobalTheory.CompanionTheory.Ar.epsMul (N : V)) ≫ spMap (dualMap f) := by
  rw [spMap_comp, spMap_comp]
  congr 1
  ext a <;> simp [dualMap, GlobalTheory.CompanionTheory.Ar.epsMul, TrivSqZeroExt.algebraMap_eq_inl, mul_comm]

theorem pow_left {R : Type} [CommRing R] {A : Over (Sp R)} [GrpObj A] [IsCommMonObj A] (v : epsR R ⟶ A)
    (hv : IsLieBasis ![v]) (N : ℕ) :
    v.left ≫ (𝟙 A ^ N).left = spMap (GlobalTheory.CompanionTheory.Ar.epsMul (N : R)) ≫ v.left := by
  obtain ⟨E, _, _, ⟨M⟩⟩ := lieModel_exists (Sp R) A R (𝟙 (Sp R))
  obtain ⟨b, hb⟩ := basis_of_lieBasis v hv M
  have e1 : toAt v = M.pt (b 0) := Over.OverMorphism.ext (by rw [toAt_left, hb])
  have h := congrArg Over.Hom.left (comp_pow' (toAt v) (𝟙 A) N)
  rw [Category.comp_id, e1, ← pt_nsmul, Over.comp_left, ← e1, toAt_left, ← Nat.cast_smul_eq_nsmul R,
    M.smul, ← e1, toAt_left] at h
  exact h

end PositivityTheory.Xgf.isogeny_decomposition_product

namespace PositivityTheory.Xgf

open PositivityTheory.Xgf.isogeny_decomposition_product in
theorem isogeny_decomposition_product : ∀ (R V : Type) [CommRing R] [CommRing V] [IsLocalRing V] (f : R →+* V) (n N : ℕ) (C : Fin n → Out.PolAV (Sp R)) (v : ∀ k, epsR R ⟶ (C k).A) (B : Out.PolAV (Sp R)) (ψ : ∀ k, (C k).A ⟶ B.A) (χ : ∀ k, B.A ⟶ (C k).A) (G : Over (Sp V)) [GrpObj G] (π : G.left ⟶ B.A.left), B.g = n → (∀ k, IsLieBasis ![v k]) → (∀ k, IsMonHom (ψ k)) → (∀ k, IsMonHom (χ k)) → (∀ k, ψ k ≫ χ k = 𝟙 (C k).A ^ N) → (∀ k k', k ≠ k' → ψ k ≫ χ k' = 1) → IsUnit (N : V) → IsGrpPullback G B.A (spMap f) π → ∃ u : Fin n → (epsAt (𝟙 (Sp V)) ⟶ G), (∀ k, (u k).left ≫ π = spMap (dualMap f) ≫ (v k).left ≫ (ψ k).left) ∧ (∀ k, IsTanAt G _ (u k)) ∧ ∀ w, IsTanAt G _ w → ∃! cc : Fin n → V, IsComb cc u w := by
  intro R V _ _ _ f n N C v B ψ χ G _ π hg hv hψ hχ hpc hpo hN hpb
  obtain ⟨EBR, _, _, ⟨MBR⟩⟩ := lieModel_exists (Sp R) B.A R (𝟙 (Sp R))
  obtain ⟨EBV, _, _, ⟨MBV⟩⟩ := lieModel_exists (Sp R) B.A V (spMap f ≫ 𝟙 (Sp R))
  obtain ⟨j, hj, -⟩ := _root_.GlobalTheory.CompanionTheory.Ar.LieBaseChange.existsUnique_semilinear_lifts (Sp R) B.A R V f (𝟙 _) EBR EBV MBR MBV
  have hx : spMap f ≫ 𝟙 (Sp R) = 𝟙 (Sp V) ≫ spMap f := by simp
  obtain ⟨MG, hMG⟩ := (_root_.GlobalTheory.CompanionTheory.Ar.LiePull.lieModel_pullback (Sp R) (Sp V) B.A G (spMap f) π hpb V (𝟙 (Sp V)) EBV).1 (castM hx MBV)
  have hMG' : ∀ e, (MG.pt e).left ≫ π = (MBV.pt e).left := fun e => (hMG e).trans (castM_left hx MBV e)

  have hvt : ∀ k, IsTanAt B.A (𝟙 (Sp R)) (toAt (v k) ≫ ψ k) := fun k => by
    haveI := hψ k; exact tan_comp _ (toAt_tan (v k) ((hv k).1 0)) (ψ k)
  choose eR heR using fun k => MBR.onto _ (hvt k)
  let EV : Fin n → EBV := fun k => j (eR k)
  have hlift : ∀ e, (MBV.pt (j e)).left = spMap (dualMap f) ≫ (MBR.pt e).left := fun e =>
    (Category.comp_id (MBV.pt (j e)).left).symm.trans (hj e)
  have hEV : ∀ k, (MBV.pt (EV k)).left = spMap (dualMap f) ≫ (v k).left ≫ (ψ k).left := fun k => by
    show (MBV.pt (j (eR k))).left = _
    rw [hlift, heR, Over.comp_left, toAt_left]

  choose EC iC mC MC bC hbC using fun k => lc (C k) (v k) (hv k) V f
  have hd : ∀ k, ∃ A : EBV →ₗ[V] EC k, ∀ e, (MC k).pt (A e) = MBV.pt e ≫ χ k := fun k => by
    haveI := hχ k
    exact (_root_.GlobalTheory.CompanionTheory.Ar.lieModel_exists_unique_diff (Sp R) B.A (C k).A V (spMap f ≫ 𝟙 (Sp R)) EBV (EC k) MBV (MC k) (χ k)).exists
  choose dχ hdχ using hd
  let fV : Fin n → (EBV →ₗ[V] V) := fun k => ((bC k).coord 0).comp (dχ k)
  have hval : ∀ i k, fV k (EV i) = if i = k then (N : V) else 0 := by
    intro i k
    have hleft : ((MC k).pt (dχ k (EV i))).left = spMap (dualMap f) ≫ (v i).left ≫ (ψ i ≫ χ k).left := by
      rw [hdχ, Over.comp_left, hEV, Over.comp_left]; simp only [Category.assoc]
    split_ifs with hik
    · subst hik
      have e2 : dχ i (EV i) = (N : V) • bC i 0 := by
        apply (MC i).inj
        apply Over.OverMorphism.ext
        rw [hleft, hpc, (MC i).smul, hbC, pow_left (v i) (hv i) N, ← Category.assoc, bc_eps, Category.assoc]
      simp [fV, e2]
    · have e2 : dχ k (EV i) = 0 := by
        apply (MC k).inj
        apply Over.OverMorphism.ext
        rw [hleft, hpo i k hik, pt_zero, ← bc_one f]
        congr 1
        rw [← Over.comp_left, MonObj.comp_one]
      simp [fV, e2]
  obtain ⟨bB⟩ := _root_.PositivityTheory.UnitarySelfGeneration.lie_free (Sp R) B.A n (hg ▸ B.smoothDim) V (spMap f ≫ 𝟙 (Sp R)) EBV MBV
  obtain ⟨hli, hsp⟩ := _root_.GlobalTheory.CompanionTheory.CommAlg.linearIndependent_span_of_dual_unit V EBV n bB EV fV (N : V) hN hval
  have bridge := (_root_.GlobalTheory.CompanionTheory.Ar.Fl.Bridge.comb_eig_frame (Sp V) V G (𝟙 (Sp V)) EBV MG).1 n
  refine ⟨fun k => MG.pt (EV k), fun k => hMG' (EV k) ▸ hEV k, fun k => MG.tan _, fun w hw => ?_⟩
  obtain ⟨e, rfl⟩ := MG.onto w hw
  have hmem : e ∈ Submodule.span V (Set.range EV) := hsp ▸ Submodule.mem_top
  obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun V).1 hmem
  refine ⟨c, (bridge c EV _).2 (by rw [hc]), fun c' hc' => ?_⟩
  have h1 := MG.inj ((bridge c' EV _).1 hc')
  rw [← hc] at h1
  have h2 := Fintype.linearIndependent_iff.1 hli (c' - c) (by
    simp only [Pi.sub_apply, sub_smul, Finset.sum_sub_distrib, h1, sub_self])
  funext i
  have := h2 i
  rw [Pi.sub_apply, sub_eq_zero] at this
  exact this

end PositivityTheory.Xgf

end
end

