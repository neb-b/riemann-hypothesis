module

public import Mathlib
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.ZariskiEtaleLifting.SubThickRees
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.WittExactSequences.Bundle0001
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0004
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0236
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0239
public import GroundTheory.ArithmeticGeometry.SchemeCohomology.ProperCohomology.ExistsChow
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.ConeSectionRestriction.Bundle0006
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.GlobalSerreRelations.GlobSerreSt
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.RepUnique
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0123
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MulSubEqZeroOfSum
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0238
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.BocksteinBaseChange.ResCoeff
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.InclStd
public import GroundTheory.PAdicHodge.ExistsGalFixCyclotomicLayerCycloCharNeOne
public import Development.WeilBound.RepresentationTheoryGL.HolomorphicDiscreteSeries.EmbeddedFrames.PfD
public import Formalism.RealPlaceAnalysis.Bundle0001
public import Development.WeilBound.CoreStatements.BranchingTraces.HeBranching

@[expose] public section

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsActOfHom
section
set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry Polynomial DividedPowers GlobalTheory.LogCris GlobalTheory.PDA CrystallineSemistableComparison CrystallineSemistableComparison.CH CrystallineSemistableComparison.B

namespace GlobalTheory.CompanionTheory.ThickAct

theorem exists_act_of_hom {b : Base} {L : b.Fun} (q : b.Rˣ) (hq : (q : b.R) - 1 ∈ b.I) (D : Thick L)
    {R : Type} [CommRing R] {d : ℕ} (τ : Fin d → Rˣ) (t : Fin d → D.B)
    (g : ∀ T : Thick L, R →+* T.B ⧸ T.J)
    (hcl : ∀ (T : Thick L) (c : D ⟶ T) (k : Fin d), Ideal.Quotient.mk T.J (c.φ (t k)) = g T (τ k))
    (hex : ∀ (T : Thick L) (u : Fin d → T.B), (∀ k, Ideal.Quotient.mk T.J (u k) = g T (τ k)) →
      ∃! c : D ⟶ T, ∀ k, c.φ (t k) = u k) :
    ∃ A : Act (𝟭 _) (thU L q hq) d D, ∀ (T : Thick L) (a : Fin d → (thU L q hq).U T) (c : D ⟶ T) (k : Fin d),
      (A.act a c).φ (t k) = ((a k).1 : T.B) * c.φ (t k) := by
  classical
  have hunit : ∀ (T : Thick L) (x : T.B), IsUnit (Ideal.Quotient.mk T.J x) → IsUnit x := by
    intro T x hx
    obtain ⟨y, hy⟩ := hx.exists_right_inv
    obtain ⟨y', rfl⟩ := Ideal.Quotient.mk_surjective y
    have hm : x * y' - 1 ∈ T.J := by
      rw [← Ideal.Quotient.eq, map_mul, map_one]
      exact hy
    have h1 : IsUnit (1 + (x * y' - 1)) := (GlobalTheory.LogCris.CupModel.isNilpotent_of_mem T hm).isUnit_one_add
    rw [add_sub_cancel] at h1
    exact isUnit_of_mul_isUnit_left h1
  have hker : ∀ (T : Thick L) (x : (thU L q hq).U T), Ideal.Quotient.mk T.J ((x.1 : T.Bˣ) : T.B) = 1 :=
    fun T x => congrArg Units.val (MonoidHom.mem_ker.1 x.2)
  have hlift : ∀ (T : Thick L) (a : Fin d → (thU L q hq).U T) (c : D ⟶ T) (k : Fin d),
      Ideal.Quotient.mk T.J (((a k).1 : T.B) * c.φ (t k)) = g T (τ k) := by
    intro T a c k
    rw [map_mul, hker, one_mul, hcl]
  have hu : ∀ (T : Thick L) (c₁ c₂ : D ⟶ T), (∀ k, c₁.φ (t k) = c₂.φ (t k)) → c₁ = c₂ := by
    intro T c₁ c₂ h
    obtain ⟨c, _, hc⟩ := hex T (fun k => c₂.φ (t k)) (fun k => hcl T c₂ k)
    exact (hc c₁ h).trans (hc c₂ fun _ => rfl).symm
  choose act hact using fun (T : Thick L) (a : Fin d → (thU L q hq).U T) (c : D ⟶ T) =>
    (hex T _ (hlift T a c)).exists
  have hw : ∀ (T : Thick L) (e : D ⟶ T) (k : Fin d), IsUnit (e.φ (t k)) := fun T e k =>
    hunit T _ (by rw [hcl]; exact (τ k).isUnit.map (g T))
  refine ⟨⟨@fun T a c => act T a c, ?_, ?_, ?_, ?_, ?_⟩, ?_⟩
  · intro T c
    show act T 1 c = c
    apply hu
    intro k
    rw [hact]
    simp
  · intro T a b c
    show act T (a * b) c = act T a (act T b c)
    apply hu
    intro k
    rw [hact, hact, hact]
    exact mul_assoc (((a k).1 : T.Bˣ) : T.B) (((b k).1 : T.Bˣ) : T.B) (c.φ (t k))
  · intro T T' a c φ
    show act T a c ≫ φ = act T' (fun k => (thU L q hq).map φ (a k)) (c ≫ φ)
    apply hu
    intro k
    rw [hact]
    change φ.φ ((act T a c).φ (t k)) = _
    rw [hact, map_mul]
    rfl
  · intro T
    show Nonempty (D ⟶ T)
    choose u hu' using fun k => Ideal.Quotient.mk_surjective (I := T.J) (g T (τ k))
    exact ⟨(hex T u hu').exists.choose⟩
  · intro T
    show ∀ c c' : D ⟶ T, ∃! a, act T a c = c'
    intro c c'
    let a : Fin d → (thU L q hq).U T := fun k =>
      ⟨(hw T c' k).unit * ((hw T c k).unit)⁻¹, by
        rw [MonoidHom.mem_ker, map_mul, map_inv]
        have e : Units.map (Ideal.Quotient.mk T.J).toMonoidHom (hw T c' k).unit =
            Units.map (Ideal.Quotient.mk T.J).toMonoidHom (hw T c k).unit := by
          apply Units.ext
          simp only [Units.coe_map, IsUnit.unit_spec, RingHom.toMonoidHom_eq_coe, MonoidHom.coe_coe, hcl]
        rw [e, mul_inv_cancel]⟩
    refine ⟨a, ?_, ?_⟩
    · apply hu
      intro k
      rw [hact]
      change (((hw T c' k).unit * ((hw T c k).unit)⁻¹ : T.Bˣ) : T.B) * c.φ (t k) = c'.φ (t k)
      rw [Units.val_mul, mul_assoc, IsUnit.val_inv_mul, mul_one, IsUnit.unit_spec]
    · intro a' ha'
      funext k
      apply Subtype.ext
      apply Units.ext
      have h := congrArg (fun e : D ⟶ T => e.φ (t k)) ha'
      simp only [hact] at h
      change ((a' k).1 : T.B) = (((hw T c' k).unit * ((hw T c k).unit)⁻¹ : T.Bˣ) : T.B)
      rw [Units.val_mul, IsUnit.unit_spec (hw T c' k), ← h, mul_assoc, IsUnit.mul_val_inv, mul_one]
  · intro T a c k
    exact hact T a c k

theorem thick_act : ∀ {O : Type} [CommRing O] {F : Fn O} {d : ℕ} (s : F.Small d) {b : Base} (ht : b.t = 1) {κ : O →+* b.R ⧸ b.I} (𝓛 : Lift s.a (fun k => (s.T k : s.R)) b.R b.I κ) (δ : DividedPowers (b.I.map 𝓛.i)) (hδ : IsDPMorphism b.γ δ 𝓛.i) (hp : b.p ≠ 0) (hn : IsNilpotent (b.p : b.R)) (q : b.Rˣ) (hq : (q : b.R) - 1 ∈ b.I), ∃ A : Act (𝟭 _) (thU (F.cr b ht κ) q hq) d (liftObj s ht 𝓛 δ hδ hp hn), ∀ (T : Thick (F.cr b ht κ)) (a : Fin d → (thU (F.cr b ht κ) q hq).U T) (c : liftObj s ht 𝓛 δ hδ hp hn ⟶ T) (k : Fin d), (A.act a c).φ (𝓛.t k) = ((a k).1 : T.B) * c.φ (𝓛.t k) := by
  intro O _ F d s b ht κ 𝓛 δ hδ hp hn q hq
  choose g hg using fun T => GlobalTheory.T.exists_lift_to_thickening s ht 𝓛 δ hδ hp hn T
  exact exists_act_of_hom q hq (liftObj s ht 𝓛 δ hδ hp hn) s.T 𝓛.t g
    (fun T c k => (hg T).1 c (s.T k) (𝓛.t k) (𝓛.hT k).symm) (fun T u hu => (hg T).2.2 u hu)

end GlobalTheory.CompanionTheory.ThickAct
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsChowCoverIntegral
section
set_option autoImplicit false
set_option maxSynthPendingDepth 1

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry GroundTheory.Arith.SchemeCoh GlobalTheory.CompanionTheory.GE
  TopologicalSpace

namespace GlobalTheory.CompanionTheory.GE.ChowOpen

lemma isClosedImmersion_restrict_iSup {T Z : Scheme.{0}} (f : T ⟶ Z) {ι : Type} (V : ι → Z.Opens)
    (h : ∀ i, IsClosedImmersion (f ∣_ V i)) : IsClosedImmersion (f ∣_ (⨆ i, V i)) := by
  refine IsZariskiLocalAtTarget.of_iSup_eq_top (fun i => (⨆ i, V i).ι ⁻¹ᵁ V i) ?_ ?_
  · refine top_le_iff.1 fun x _ => ?_
    obtain ⟨i, hi⟩ := Opens.mem_iSup.1 x.2
    exact Opens.mem_iSup.2 ⟨i, hi⟩
  · intro i
    have hV : (⨆ i, V i).ι ''ᵁ ((⨆ i, V i).ι ⁻¹ᵁ V i) = V i := by
      rw [Scheme.Hom.image_preimage_eq_opensRange_inf, Scheme.Opens.opensRange_ι]
      exact inf_eq_right.2 (le_iSup V i)
    have e := morphismRestrictRestrict f (⨆ i, V i) ((⨆ i, V i).ι ⁻¹ᵁ V i)
    have h' : IsClosedImmersion (f ∣_ ((⨆ i, V i).ι ''ᵁ ((⨆ i, V i).ι ⁻¹ᵁ V i))) := by
      rw [hV]; exact h i
    exact (MorphismProperty.arrow_mk_iso_iff (@IsClosedImmersion) e).2 h'

theorem exists_image_open {T Z : Scheme.{0}} (f : T ⟶ Z) [QuasiCompact f] (S : Z.Opens)
    [IsClosedImmersion (f ∣_ S)] (hS : f ⁻¹ᵁ S = ⊤) :
    ∃ (O : f.image.Opens) (φ : O.toScheme ⟶ T), IsIso φ ∧ φ ≫ f = O.ι ≫ f.imageι := by
  have hι : IsIso (f ⁻¹ᵁ S).ι := by
    rw [isIso_iff_isOpenImmersion_and_surjective]
    exact ⟨inferInstance, ⟨by rw [← Set.range_eq_univ, Scheme.Opens.range_ι, hS]; rfl⟩⟩
  refine ⟨f.imageι ⁻¹ᵁ S, SchemeImage.imageRestrictLift f S ≫ (f ⁻¹ᵁ S).ι, inferInstance, ?_⟩
  rw [Category.assoc, ← morphismRestrict_ι, SchemeImage.imageRestrictLift_fac_assoc,
    morphismRestrict_ι]

theorem exists_chow_open_projective {A : Type} [CommRing A] [IsNoetherianRing A] {X : Scheme.{0}}
    (s : X ⟶ Spec (.of A)) [IsSeparated s] [LocallyOfFiniteType s] [QuasiCompact s]
    [IrreducibleSpace X] :
    ∃ (N : ℕ) (Y : Scheme.{0}) (i : Y ⟶ projectiveSpace A N) (O : Y.Opens)
      (ψ : (O : Scheme.{0}) ⟶ X) (W : X.Opens), IsClosedImmersion i ∧ IsProper ψ ∧
      O.ι ≫ i ≫ ProjSpace.toSpecBase A N = ψ ≫ s ∧ (W : Set X).Nonempty ∧ IsIso (ψ ∣_ W) := by
  classical
  have : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace s
  have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian s
  have : IsNoetherian X := ⟨⟩
  have hex : ∀ x : X, ∃ V : X.Opens, IsAffineOpen V ∧ x ∈ V := fun x => by
    obtain ⟨_, ⟨V, hV, rfl⟩, hxV, -⟩ :=
      X.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ x) isOpen_univ
    exact ⟨V, hV, hxV⟩
  choose V hVaff hxV using hex
  obtain ⟨t, ht⟩ := isCompact_univ.elim_finite_subcover (fun x : X => (V x : Set X))
    (fun x => (V x).2) (fun x _ => Set.mem_iUnion.2 ⟨x, hxV x⟩)
  have htne : t.Nonempty := by
    obtain ⟨x⟩ := (inferInstance : Nonempty X)
    obtain ⟨y, hy, -⟩ := Set.mem_iUnion₂.1 (ht (Set.mem_univ x))
    exact ⟨y, hy⟩
  obtain ⟨k, hk⟩ : ∃ k, t.card = k + 1 := ⟨t.card - 1, by have := htne.card_pos; omega⟩
  let e : Fin (k + 1) ≃ t := (Fintype.equivFinOfCardEq (by simpa using hk)).symm
  let U : Fin (k + 1) → X.Opens := fun j => V (e j)
  have hUaff : ∀ j, IsAffineOpen (U j) := fun j => hVaff _
  have hU : iSup U = ⊤ := by
    refine top_le_iff.1 fun x _ => ?_
    obtain ⟨y, hy, hxy⟩ := Set.mem_iUnion₂.1 (ht (Set.mem_univ x))
    exact Opens.mem_iSup.2 ⟨e.symm ⟨y, hy⟩, by simpa [U] using hxy⟩
  have hc := fun j => ProjSpace.exists_closedImmersion_stdOpen (A := A) s (hUaff j)
  choose n c hccl hcc using hc
  have : ∀ j, IsClosedImmersion (c j) := hccl
  have hη : genericPoint X ∈ ChowGraph.W U := by
    rw [ChowGraph.W, ← SetLike.mem_coe, Opens.coe_iInf, Set.mem_iInter]
    intro j
    exact ((genericPoint_spec X).mem_open_set_iff (U j).2).2
      ⟨e j, Set.mem_univ _, hxV _⟩
  have : NoetherianSpace (ChowGraph.W U).toScheme :=
    NoetherianSpace.set ((ChowGraph.W U : X.Opens) : Set X)
  have : QuasiCompact (ChowGraph.g s n U c hcc) := ⟨fun _ _ _ => NoetherianSpace.isCompact _⟩
  have hqc : QuasiCompact (ChowGraph.q s n U c hcc) := by
    unfold ChowGraph.q; infer_instance
  have hcl : IsClosedImmersion
      (ChowGraph.q s n U c hcc ∣_ (⨆ i, ChowGraph.V (A := A) n i)) :=
    isClosedImmersion_restrict_iSup _ _ fun i =>
      ChowGraph.isClosedImmersion_q_restrict s n U c hcc i
  have hS : ChowGraph.q s n U c hcc ⁻¹ᵁ (⨆ i, ChowGraph.V (A := A) n i) = ⊤ := by
    refine top_le_iff.1 fun y _ => ?_
    have hy : ChowGraph.π s n U c hcc y ∈ (⊤ : X.Opens) := trivial
    rw [← hU] at hy
    obtain ⟨i, hi⟩ := Opens.mem_iSup.1 hy
    exact Opens.mem_iSup.2 ⟨i, ChowGraph.q_mem_V s n U c hcc i y hi⟩
  obtain ⟨O, φ, hφ, hφq⟩ := exists_image_open (ChowGraph.q s n U c hcc) _ hS
  have hπ : IsProper (ChowGraph.π s n U c hcc) := by
    unfold ChowGraph.π; infer_instance
  refine ⟨ProjSpace.multiProjDim k n, (ChowGraph.q s n U c hcc).image,
    (ChowGraph.q s n U c hcc).imageι ≫ ProjSpace.multiProjEmb A k n, O,
    φ ≫ ChowGraph.π s n U c hcc, ChowGraph.W U, inferInstance, inferInstance, ?_, ⟨_, hη⟩, ?_⟩
  · rw [Category.assoc, ProjSpace.multiProjEmb_toSpecBase, ← Category.assoc, ← hφq]
    simp only [ChowGraph.q, ChowGraph.π, Category.assoc, pullback.condition]
  · rw [morphismRestrict_comp]
    have := ChowGraph.isIso_π_restrict s n U c hcc
    have h1 : IsIso (φ ∣_ (ChowGraph.π s n U c hcc ⁻¹ᵁ ChowGraph.W U)) :=
      IsZariskiLocalAtTarget.restrict (P := MorphismProperty.isomorphisms Scheme) hφ _
    exact IsIso.comp_isIso' h1 this

theorem exists_chow_open {A : Type} [CommRing A] [IsNoetherianRing A] {X : Scheme.{0}}
    [X.Over (Spec (.of A))] [IsSeparated (X ↘ Spec (.of A))]
    [LocallyOfFiniteType (X ↘ Spec (.of A))] [QuasiCompact (X ↘ Spec (.of A))] [IsIntegral X] :
    ∃ (N : ℕ) (Y : Scheme.{0}) (i : Y ⟶ projectiveSpace A N) (O : Y.Opens)
      (ψ : (O : Scheme.{0}) ⟶ X) (W : X.Opens), IsClosedImmersion i ∧ IsProper ψ ∧
      O.ι ≫ i ≫ ProjSpace.toSpecBase A N = ψ ≫ (X ↘ Spec (.of A)) ∧ (W : Set X).Nonempty ∧
      IsIso (ψ ∣_ W) :=
  exists_chow_open_projective (X ↘ Spec (.of A))

end GlobalTheory.CompanionTheory.GE.ChowOpen
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsDerivationExt
section
set_option backward.isDefEq.respectTransparency false
set_option autoImplicit false
open CategoryTheory AlgebraicGeometry GlobalTheory.LogCris CrystallineSemistableComparison CrystallineSemistableComparison.Pb GlobalTheory.CompanionTheory.ConeLocal
open GlobalTheory.CatH (face toLast)

noncomputable section
namespace GlobalTheory.CompanionTheory.ConeLocal.DerivExt

theorem exists_derivation_ext {K A B : Type} [CommRing K] [CommRing A] [CommRing B] [Algebra K A] [Algebra K B]
    (f : A →+* B) (hf : f.comp (algebraMap K A) = algebraMap K B) (M : Submonoid A)
    (hloc : letI := f.toAlgebra; IsLocalization M B) (D : Derivation K A A) :
    ∃ p : Derivation K B B, ∀ x, p (f x) = f (D x) := by
  letI := f.toAlgebra
  let φ : A →+* TrivSqZeroExt B B :=
    { toFun := fun x => (f x, f (D x))
      map_one' := by
        ext <;> simp
      map_zero' := by
        ext <;> simp
      map_add' := fun x y => by
        ext <;> simp
      map_mul' := fun x y => by
        ext
        · simp
        · simp [Derivation.leibniz]
          ring }
  have hu : ∀ y : M, IsUnit (φ y) := fun y => by
    rw [TrivSqZeroExt.isUnit_iff_isUnit_fst]
    exact IsLocalization.map_units B y
  let ψ : B →+* TrivSqZeroExt B B := IsLocalization.lift hu
  have hψ : ∀ x, ψ (f x) = φ x := fun x => IsLocalization.lift_eq hu x
  have hfst : ∀ b, (ψ b).fst = b := by
    have : (TrivSqZeroExt.fstHom B B B).toRingHom.comp ψ = RingHom.id B :=
      IsLocalization.ringHom_ext M (RingHom.ext fun x => by
        change (ψ (f x)).fst = f x
        rw [hψ]; rfl)
    exact fun b => congrArg (· b) (congrArg DFunLike.coe this)
  have hmul : ∀ b c, (ψ (b * c)).snd = b * (ψ c).snd + c * (ψ b).snd := fun b c => by
    rw [map_mul, TrivSqZeroExt.snd_mul, hfst, smul_eq_mul]
    simp [hfst, mul_comm]
  have hadd : ∀ b c, (ψ (b + c)).snd = (ψ b).snd + (ψ c).snd := fun b c => by
    rw [map_add (f := _), TrivSqZeroExt.snd_add]
  have hsm : ∀ (k : K) b, (ψ (k • b)).snd = k • (ψ b).snd := fun k b => by
    have e : algebraMap K B k = f (algebraMap K A k) := (congrArg (· k) (congrArg DFunLike.coe hf)).symm
    rw [Algebra.smul_def, Algebra.smul_def, hmul, e, hψ]
    have : (φ (algebraMap K A k)).snd = 0 := by
      change f (D _) = 0
      rw [Derivation.map_algebraMap, map_zero]
    rw [this, mul_zero, add_zero]
  let L : B →ₗ[K] B :=
    { toFun := fun b => (ψ b).snd
      map_add' := hadd
      map_smul' := hsm }
  refine ⟨Derivation.mk' L fun b c => ?_, fun x => ?_⟩
  · change (ψ (b * c)).snd = b • (ψ c).snd + c • (ψ b).snd
    rw [hmul]; rfl
  · change (ψ (f x)).snd = _
    rw [hψ]; rfl

theorem main : ∀ {K : Type} [Field K] {X : Scheme.{0}} (q : X ⟶ Spec (CommRingCat.of K)) {V : X.Opens}, IsAffineOpen V → ∀ (a : Γ(X, V)),
    letI := (strV q V).toAlgebra
    letI := (strV q (X.basicOpen a)).toAlgebra
    ∀ {d : ℕ} (D : Fin d → Derivation K Γ(X, V) Γ(X, V)), ∃ p : Fin d → Derivation K Γ(X, X.basicOpen a) Γ(X, X.basicOpen a),
      ∀ k x, p k (rs (X.basicOpen_le a) x) = rs (X.basicOpen_le a) (D k x) := by
  intro K _ X q V hV a
  letI := (strV q V).toAlgebra
  letI := (strV q (X.basicOpen a)).toAlgebra
  intro d D
  have hloc : letI := (rs (X.basicOpen_le a)).toAlgebra; IsLocalization (Submonoid.powers a) Γ(X, X.basicOpen a) := by
    letI := (rs (X.basicOpen_le a)).toAlgebra
    exact hV.isLocalization_basicOpen a
  have hf : (rs (X.basicOpen_le a)).comp (algebraMap K Γ(X, V)) = algebraMap K Γ(X, X.basicOpen a) :=
    GlobalTheory.CompanionTheory.CoordRes.rs_comp_strV q _
  choose p hp using fun k => exists_derivation_ext _ hf _ hloc (D k)
  exact ⟨p, hp⟩

end GlobalTheory.CompanionTheory.ConeLocal.DerivExt
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsLimHom
section
set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry DividedPowers GroundTheory.PAdicHodge GlobalTheory.LogCris GlobalTheory.PDA CrystallineSemistableComparison CrystallineSemistableComparison.CH CrystallineSemistableComparison.PAlg CrystallineSemistableComparison.B

noncomputable section

namespace GlobalTheory.CompanionTheory.ContUniv

section Lim

variable {T : Type} [CommRing T] (ϖ : T)

def Tends (x : ℕ → T) (L : T) : Prop := ∀ k, ∃ M, ∀ m, M ≤ m → x m - L ∈ Ideal.span {ϖ ^ k}

variable {ϖ}

theorem smodEq_iff {a b : T} {k : ℕ} :
    a ≡ b [SMOD ((Ideal.span {ϖ}) ^ k • ⊤ : Submodule T T)] ↔ a - b ∈ Ideal.span {ϖ ^ k} := by
  rw [SModEq.sub_mem, smul_eq_mul, Ideal.mul_top, Ideal.span_singleton_pow]

theorem Tends.unique [IsHausdorff (Ideal.span {ϖ}) T] {x : ℕ → T} {L L' : T} (h : Tends ϖ x L)
    (h' : Tends ϖ x L') : L = L' := by
  rw [← sub_eq_zero]
  refine IsHausdorff.haus (inferInstance : IsHausdorff (Ideal.span {ϖ}) T) _ fun k => ?_
  have h0 : L - L' ∈ Ideal.span {ϖ ^ k} := by
    obtain ⟨M, hM⟩ := h k
    obtain ⟨M', hM'⟩ := h' k
    have := sub_mem (hM' (max M M') (le_max_right _ _)) (hM (max M M') (le_max_left _ _))
    simpa using this
  have : L - L' ≡ 0 [SMOD ((Ideal.span {ϖ}) ^ k • ⊤ : Submodule T T)] :=
    smodEq_iff.2 (by simpa using h0)
  exact this

theorem exists_tends [IsAdicComplete (Ideal.span {ϖ}) T] (x : ℕ → T)
    (h : ∀ k, ∃ M, ∀ m, M ≤ m → x m - x M ∈ Ideal.span {ϖ ^ k}) : ∃ L, Tends ϖ x L := by
  choose M hM using h
  let N : ℕ → ℕ := fun k => (Finset.range (k + 1)).sup M
  have hN : ∀ k, M k ≤ N k := fun k => Finset.le_sup (Finset.self_mem_range_succ k)
  have hmono : Monotone N := fun a b hab =>
    Finset.sup_mono (Finset.range_subset_range.2 (Nat.succ_le_succ hab))
  have hc : ∀ k m, N k ≤ m → x m - x (N k) ∈ Ideal.span {ϖ ^ k} := fun k m hm => by
    have := sub_mem (hM k m ((hN k).trans hm)) (hM k (N k) (hN k))
    simpa using this
  obtain ⟨L, hL⟩ := IsPrecomplete.prec (inferInstance : IsPrecomplete (Ideal.span {ϖ}) T)
    (f := fun k => x (N k)) (fun {a b} hab => smodEq_iff.2 (by
      have := hc a (N b) (hmono hab)
      rw [← neg_sub]
      exact neg_mem this))
  refine ⟨L, fun k => ⟨N k, fun m hm => ?_⟩⟩
  have := add_mem (hc k m hm) (smodEq_iff.1 (hL k))
  simpa using this

theorem Tends.add {x y : ℕ → T} {a b : T} (hx : Tends ϖ x a) (hy : Tends ϖ y b) :
    Tends ϖ (fun m => x m + y m) (a + b) := fun k => by
  obtain ⟨M, hM⟩ := hx k
  obtain ⟨M', hM'⟩ := hy k
  refine ⟨max M M', fun m hm => ?_⟩
  have := add_mem (hM m ((le_max_left _ _).trans hm)) (hM' m ((le_max_right _ _).trans hm))
  convert this using 1; ring

theorem Tends.mul {x y : ℕ → T} {a b : T} (hx : Tends ϖ x a) (hy : Tends ϖ y b) :
    Tends ϖ (fun m => x m * y m) (a * b) := fun k => by
  obtain ⟨M, hM⟩ := hx k
  obtain ⟨M', hM'⟩ := hy k
  refine ⟨max M M', fun m hm => ?_⟩
  have := add_mem (Ideal.mul_mem_right (y m) _ (hM m ((le_max_left _ _).trans hm)))
    (Ideal.mul_mem_left _ a (hM' m ((le_max_right _ _).trans hm)))
  convert this using 1; ring

theorem tends_const (a : T) : Tends ϖ (fun _ => a) a := fun k => ⟨0, fun _ _ => by simp⟩

theorem exists_lim_hom {S : Type} [CommRing S] [IsAdicComplete (Ideal.span {ϖ}) T] (a : ℕ → S →+* T)
    (h : ∀ f k, ∃ M, ∀ m, M ≤ m → a m f - a M f ∈ Ideal.span {ϖ ^ k}) :
    ∃ ψ : S →+* T, ∀ f, Tends ϖ (fun m => a m f) (ψ f) := by
  choose L hL using fun f => exists_tends (ϖ := ϖ) (fun m => a m f) (h f)
  refine ⟨{ toFun := L, map_one' := ?_, map_mul' := ?_, map_zero' := ?_, map_add' := ?_ }, hL⟩
  · exact (hL 1).unique (by simpa using tends_const (ϖ := ϖ) (1 : T))
  · intro f g
    exact (hL (f * g)).unique (by simpa using (hL f).mul (hL g))
  · exact (hL 0).unique (by simpa using tends_const (ϖ := ϖ) (0 : T))
  · intro f g
    exact (hL (f + g)).unique (by simpa using (hL f).add (hL g))

end Lim

variable {l : ℕ} [Fact l.Prime]

theorem exists_period (A : PAlg l) (f : (A.cont ℤ_[l]).A) (k : ℕ) :
    ∃ M : ℕ, ∀ z z' : ℤ_[l], PadicInt.toZModPow M z = PadicInt.toZModPow M z' →
      Hom.f (A.evCont z) f - Hom.f (A.evCont z') f ∈ Ideal.span {A.pi ^ k} := by
  obtain ⟨M, hM⟩ := GlobalTheory.CompanionTheory.PadicShift.exists_period l _ (f.2 k)
  refine ⟨M, fun z z' h => Ideal.Quotient.eq.1 (hM z z' ?_)⟩
  rw [← Ideal.mem_span_singleton, ← PadicInt.ker_toZModPow, RingHom.mem_ker, map_sub, h, sub_self]

end GlobalTheory.CompanionTheory.ContUniv
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FiniteLengthWittCohomologyStatement
section
set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry GlobalTheory.LogCris DividedPowers CrystallineSemistableComparison CrystallineSemistableComparison.Pb
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finite_length_witt_cohomology : ∀ {l : ℕ} [Fact l.Prime] {k : Type} [Field k] [CharP k l] [PerfectRing k l] {O : Type} [CommRing O] {X : Scheme.{0}}
    (q : X ⟶ Spec (CommRingCat.of O)) (ρ : O →+* k) (j : ℕ),
    Module.Finite (Wc.Wm l k 1) (HO (St (γ := Wc.pd l k 1) (p := l) (q := q) (κ := (Wc.res l k 1).comp ρ) ⊤ {⊤}) j) →
    IsFiniteLength (WittVector l k) (CH.H (Wc.OM l (B.schFn q) ρ 1) j) := by
  first | exact @GlobalTheory.CompanionTheory.LevelOne.finiteLength_level_one | exact GlobalTheory.CompanionTheory.LevelOne.finiteLength_level_one | (intros; apply GlobalTheory.CompanionTheory.LevelOne.finiteLength_level_one <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.GaloisActionPeriodProduct
section
noncomputable section
open NumberField IsDedekindDomain Neutral.B1 Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.L2.Host Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations
open GlobalTheory.HeckeGal GlobalTheory.Pst GlobalTheory.TripleGal GlobalTheory.CompanionTheory.LTHodge GlobalTheory.CompanionTheory.LTPer
open scoped Classical

namespace GlobalTheory.CompanionTheory.LTPer

theorem actB_prod_periods {l : ℕ} [Fact l.Prime] (K : FinExt l) (χ : ↥(GK K) →* (↥K.1)ˣ)
    (t : (↥K.1 →ₐ[ℚ_[l]] Om l) → Formalism.Per6.BdRp l) (s : Finset (↥K.1 →ₐ[ℚ_[l]] Om l))
    (hs : ∀ μ, μ ∈ s) (ht : ∀ μ, PrePer K χ μ (t μ))
    (g : GQ l) (hg : g ∈ GK K) (hfix : ∀ (μ : ↥K.1 →ₐ[ℚ_[l]] Om l) (x : ↥K.1), g (μ x) = μ x) :
      actB g (∏ μ ∈ s, t μ) =
        algebraMap ℚ_[l] (Formalism.Per6.BdRp l) (Algebra.norm ℚ_[l] ((χ ⟨g, hg⟩ : (↥K.1)ˣ) : ↥K.1)) * ∏ μ ∈ s, t μ := by
  haveI : FiniteDimensional ℚ_[l] ↥K.1 := K.2
  letI : Fintype (↥K.1 →ₐ[ℚ_[l]] Om l) := minpoly.AlgHom.fintype ℚ_[l] (↥K.1) (Om l)
  have hsu : s = Finset.univ := Finset.eq_univ_iff_forall.2 hs
  set y : ↥K.1 := ((χ ⟨g, hg⟩ : (↥K.1)ˣ) : ↥K.1) with hy
  have hn : algebraMap ℚ_[l] (Om l) (Algebra.norm ℚ_[l] y) = ∏ μ ∈ s, μ y := by
    rw [hsu]
    exact Algebra.norm_eq_prod_embeddings ℚ_[l] (Om l) y
  have hr : algebraMap ℚ_[l] (Formalism.Per6.BdRp l) (Algebra.norm ℚ_[l] y) = ∏ μ ∈ s, rB l (μ y) := by
    rw [← map_prod, ← hn]
    exact ((GroundTheory.PAdicHodge.algClToBdR l).commutes _).symm
  rw [map_prod, hr, ← Finset.prod_mul_distrib]
  exact Finset.prod_congr rfl fun μ _ => (ht μ).2.1 g hg (hfix μ)

end GlobalTheory.CompanionTheory.LTPer
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.InterlacingSignatureParityStatement
section
open Finset Matrix PositivityTheory.RgHe.Frame
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.interlacing_signature_parity : ∀ (n : ℕ) (ε : Fin (n + 1) → Bool) (d : Fin (n + 1) → ℝ) (ε' : Fin n → Bool) (d' : Fin n → ℝ) (e : Fin n ⊕ Unit ≃ Fin (n + 1)), PositivityTheory.UnitaryDecomposition.Fits ε ε' e → Function.Injective (Sum.elim d d') → PositivityTheory.UnitaryDecomposition.HeWord ε d ε' d' → (∀ i, (ε i = true ↔ Even (above d d' (d i)))) ∧ ∀ j, (ε' j = true ↔ ¬ Even (above d d' (d' j))) := by
  first | exact @GlobalTheory.CompanionTheory.RgHeFrame.SignWord.heSign | exact GlobalTheory.CompanionTheory.RgHeFrame.SignWord.heSign | (intros; apply GlobalTheory.CompanionTheory.RgHeFrame.SignWord.heSign <;> assumption)
end

