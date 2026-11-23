module

public import Mathlib
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle0010
public import Development.AutomorphicSpectrum.Statements.GeometryStatements.IsPolLatticePlane
public import Development.AutomorphicSpectrum.Statements.AlgebraStatements.Bundle0003
public import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.Birational
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0201
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0249
public import Development.WeilBound.CoreStatements.HodgeTatePoints.TrivFlagModOfHodgeTateFreeOfRootLines
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.GlobalSectionsRankAlgClosed
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle0005
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle0007
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.HodgeCptProjectiveModel
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0246
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0178
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.DvrData
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle0006
public import Development.AutomorphicSpectrum.Statements.GeometryStatements.Bundle0002
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.GenericCentreSpecializes
public import Development.AutomorphicSpectrum.Statements.GeometryStatements.Bundle0004
public import Development.AutomorphicSpectrum.PublishedTheorems.Geometry₂.GagaSections
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.BlowupProjections.BlowupProjStatement
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
public import Development.WeilBound.CoreStatements.TorusUniformisation.ChowMahlerFamilies.NumericalTrivialityOfGoodReduction
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0082
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0076
public import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.Bundle0042
public import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.Bundle0004
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ValuationBoundedFrame
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.FibreCurveGermPowers
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0088
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle0013
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsFlatAnIffIsConstMul
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0218
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0181
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.ToFirst
public import Development.AutomorphicSpectrum.PublishedTheorems.Geometry₂.ConclusionOfSmooth
public import Development.AutomorphicSpectrum.PublishedTheorems.Geometry₂.NotSubsetOfDenseCompl
public import Development.AutomorphicSpectrum.PublishedTheorems.PublishedGlobalResults.PrincipalizationOfPrincipalisation

@[expose] public section

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.HodgeTateFreeTrivialFlagMod
section
open CategoryTheory AlgebraicGeometry NumberField MvPolynomial GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.HT ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.NumbersDVR.Bundles

namespace GlobalTheory.CompanionTheory.Ar.HT

theorem trivFlagMod_rootLines_model : FarguesHodgeTate → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (S : Finset ℕ) (Ω : Type) [Field Ω] (K : Type) [Fintype K] (J : K → Type) [∀ k, Fintype (J k)] (y : (Σ k, J k) → Ω) (𝔐 : HodgeCpt Y S y) (p : ℕ) [Fact p.Prime] (hpS : p ∈ S) (hpq : 0 < D.p + D.q) (o : Type) [CommRing o] [Algebra o Ω] (ho : ∀ x : Ω, x ∈ (algebraMap o Ω).range ↔ ∃ (a : ℤ) (b : ℕ), ¬ p ∣ b ∧ x = (a : Ω) / (b : Ω)) (Fl : 𝔐.Flag) (xdeg : CMType H × Fin (D.p + D.q) → K → ℤ) (e : CMType H × Fin (D.p + D.q) → Ω), HTFree 𝔐 p → Fl.RootLines xdeg e → ∀ τ : CMType H, Num.TrivFlagMod o ((p : o) ^ (𝔐.R p - 2)) y (D.p + D.q) (fun i => xdeg (τ, i)) :=
  PositivityTheory.HtPt.Ge.triv_flag_mod_of_hodge_tate_free_of_root_lines (fun hF => GlobalTheory.T.pointHT_of_fargues_hodge_tate hF)
    (fun E _ _ _ H D l Xo c O _ β Y S Ω _ K _ J _ y 𝔐 p _ hpS hpq o _ _ ho =>
      _root_.GlobalTheory.CompanionTheory.Ar.HT.hodgeTate_family_exists E H D l Xo c O β Y S Ω K J y 𝔐 p hpS hpq o ho)

end GlobalTheory.CompanionTheory.Ar.HT
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.IsPrimitiveRootOfLevel
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar

namespace GlobalTheory.CompanionTheory.Ar.HodgeExists

theorem exists_lift_torsion {S S' Z : Scheme.{0}} {G' : Over S'} [GrpObj G'] {G : Over S} [GrpObj G] {f : S' ⟶ S}
    {φ : G'.left ⟶ G.left} (h : IsGrpPullback G' G f φ) (b : Z ⟶ S') (a : Z ⟶ S) (hab : a = b ≫ f) (n : ℕ)
    (g : Over.mk a ⟶ G) (hg : g ^ n = 1) : ∃ g' : Over.mk b ⟶ G', g'.left ≫ φ = g.left ∧ g' ^ n = 1 := by
  subst hab
  let P : (Over.mk b ⟶ G') → (Over.mk (b ≫ f) ⟶ G) := fun x => Over.homMk (x.left ≫ φ) (by
    have := Over.w x
    simp only [Over.mk_hom] at this
    simp only [Category.assoc, Over.mk_hom, h.1.w]
    rw [← Category.assoc, this])
  have hP : ∀ x, (P x).left = x.left ≫ φ := fun _ => rfl
  let Φ : (Over.mk b ⟶ G') →* (Over.mk (b ≫ f) ⟶ G) := MonoidHom.mk' P fun x y =>
    Over.OverMorphism.ext ((hP _).trans (h.2 (Over.mk b) x y (P x) (P y) rfl rfl).symm)
  have hinj : Function.Injective Φ := fun x y hxy => Over.OverMorphism.ext
    (h.1.hom_ext (congrArg CommaMorphism.left hxy) ((Over.w x).trans (Over.w y).symm))
  let g' : Over.mk b ⟶ G' := Over.homMk (h.1.lift g.left b (Over.w g)) (h.1.lift_snd _ _ _)
  have hg' : g'.left ≫ φ = g.left := h.1.lift_fst _ _ _
  refine ⟨g', hg', hinj ?_⟩
  have : Φ g' = g := Over.OverMorphism.ext hg'
  rw [map_pow, this, hg, map_one]

theorem fullTorsion_push {S S' : Scheme.{0}} {G' : Over S'} [GrpObj G'] {G : Over S} [GrpObj G] {f : S' ⟶ S}
    {φ : G'.left ⟶ G.left} (h : IsGrpPullback G' G f φ) {Ω : Type} [Field Ω] {ξ : Spec (CommRingCat.of Ω) ⟶ S'}
    {N n : ℕ} (hn : n ∣ N) (ht : FullTorsion G' ξ N) : FullTorsion G (ξ ≫ f) n := by
  intro k _ i g hg
  obtain ⟨g', e, hg'⟩ := exists_lift_torsion h (spMap i ≫ ξ) _ (Category.assoc _ _ _).symm n g hg
  obtain ⟨m, rfl⟩ := hn
  obtain ⟨x, hx⟩ := ht k i g' (by rw [pow_mul, hg', one_pow])
  refine ⟨Over.homMk (x.left ≫ φ) ?_, ?_⟩
  · have := Over.w x
    simp only [Over.mk_hom] at this
    simp only [Category.assoc, Over.mk_hom, h.1.w]
    rw [← Category.assoc, this]
  · rw [← e, hx]
    exact Category.assoc _ _ _

theorem finite_of_dominates {X Y : Scheme.{0}} {Ω Ω₀ : Type} [Field Ω] [Field Ω₀] {ξ : Spec (CommRingCat.of Ω) ⟶ X}
    {ξ₀ : Spec (CommRingCat.of Ω₀) ⟶ Y} (hξ : IsCptGen ξ) (f : X ⟶ Y) [IsFinite f] {i : Ω₀ →+* Ω}
    (h : GlobalTheory.CompanionTheory.Ar.Dominates ξ ξ₀ f i) : i.Finite := by
  have h1 : LocallyQuasiFinite (Spec.map (Scheme.stalkClosedPointTo ξ)) :=
    (HasRingHomProperty.Spec_iff (P := @LocallyQuasiFinite)).2
      (.of_finite (RingHom.Finite.of_surjective _ hξ.bij.2))
  have h2 : LocallyQuasiFinite ξ := by
    rw [← Scheme.Spec_stalkClosedPointTo_fromSpecStalk ξ]
    infer_instance
  have h3 : LocallyQuasiFinite (Spec.map (CommRingCat.ofHom i) ≫ ξ₀) := by
    rw [← h]
    infer_instance
  have h4 : i.QuasiFinite :=
    (HasRingHomProperty.Spec_iff (P := @LocallyQuasiFinite) (φ := CommRingCat.ofHom i)).1
      (LocallyQuasiFinite.of_comp _ ξ₀)
  algebraize [i]
  exact .of_quasiFinite

end GlobalTheory.CompanionTheory.Ar.HodgeExists
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.LocalSystemSplitFibres
section
open CategoryTheory AlgebraicGeometry NumberField GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.HT GlobalTheory.CompanionTheory.Ar.Flat ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor

namespace GlobalTheory.CompanionTheory.Ar.Flat

theorem numTriv_offS : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (Xo : ∀ l : Level H, Moduli D l) (Yl : ∀ (p : ℕ) (W : ValuationSubring ℂ), p.Prime → (p : ℂ) ∈ W.nonunits → LocalSystem Xo p W), (∀ p W hp hW i, (Yl p W hp hW i).SplitFibres ∧ (Yl p W hp hW i).N3) → ∀ (l : Level H) (c : Coeff l) (hg : ∀ p : ℕ, p.Prime → l.GoodAt p) (Y : Model (Xo l) c (algebraMap (𝓞 c.F) c.F)), (∀ (p : ℕ) (W : ValuationSubring ℂ) (hp : p.Prime) (hW : (p : ℂ) ∈ W.nonunits) (b : 𝓞 c.F →+* c.V W), (∀ x, ((b x : c.V W) : c.F) = (x : c.F)) → ReciprocityTheory.ChartRestriction.G.Geo.Tor.Dominates Y (Yl p W hp hW ⟨l, c, hg p hp⟩) b) → ∀ (S : Finset ℕ) (Ω : Type) [Field Ω] (K : Type) [Fintype K] (J : K → Type) [∀ k, Fintype (J k)] (y : (Σ k, J k) → Ω) (𝔐 : HodgeCpt Y S y) (p : ℕ), p.Prime → p ∉ S → ¬ (p : ℤ) ∣ NumberField.discr E → ∀ (τ : CMType H) (a : ⋀[Ω]^D.p 𝔐.Li) (b : ⋀[Ω]^D.q 𝔐.Li), a ≠ 0 → b ≠ 0 → (∃ x f, IsCoeffAt (𝔐.V (.inl τ)) (𝔐.V (.inr τ)) D.p D.q a b x f) → NumTrivMod (lineLat (𝔐.V (.inl τ)) (𝔐.V (.inr τ)) D.p D.q a b) (p : Ω) :=
  @PositivityTheory.Xgn.numerical_triviality_of_good_reduction

end GlobalTheory.CompanionTheory.Ar.Flat
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.ResKOfResolutionPrincipalisation
section
noncomputable section

open AlgebraicGeometry CategoryTheory Limits TopologicalSpace
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.ResK ReciprocityTheory.AnForm.R

namespace GlobalTheory.CompanionTheory.Hypotheses₂.ResKSide

theorem le_smoothLocus {X Y : Scheme.{0}} (f : X ⟶ Y) [LocallyOfFinitePresentation f] (U : X.Opens)
    [Smooth (U.ι ≫ f)] : U ≤ f.smoothLocus := by
  intro x hx
  have := (U.ι ≫ f).smoothLocus_eq_top.ge (Set.mem_univ (⟨x, hx⟩ : U))
  rw [← Scheme.Hom.preimage_smoothLocus_eq] at this
  exact this

theorem dense_preimage {X Y : Scheme.{0}} (f : X ⟶ Y) {U V : Y.Opens} [IsIso (f ∣_ V)]
    (hV : Dense ((f ⁻¹ᵁ V : X.Opens) : Set X)) (hU : Dense (U : Set Y)) :
    Dense ((f ⁻¹ᵁ U : X.Opens) : Set X) := by
  rw [dense_iff_inter_open]
  intro O hO hne
  obtain ⟨p, hpO, hpV⟩ := hV.inter_open_nonempty O hO hne
  let O' : Set (f ⁻¹ᵁ V) := (f ⁻¹ᵁ V).ι.base ⁻¹' O
  have hO' : IsOpen O' := hO.preimage (f ⁻¹ᵁ V).ι.base.hom.continuous
  have hopen : IsOpen (V.ι.base '' ((f ∣_ V).base '' O')) :=
    V.ι.isOpenEmbedding.isOpenMap _ ((f ∣_ V).isOpenEmbedding.isOpenMap _ hO')
  have hp' : (⟨p, hpV⟩ : f ⁻¹ᵁ V) ∈ O' := hpO
  obtain ⟨y, ⟨q, ⟨p', hp'O, rfl⟩, rfl⟩, hyU⟩ := hU.inter_open_nonempty _ hopen ⟨_, _, ⟨_, hp', rfl⟩, rfl⟩
  refine ⟨(f ⁻¹ᵁ V).ι p', hp'O, ?_⟩
  show f ((f ⁻¹ᵁ V).ι p') ∈ U
  rw [← Scheme.Hom.comp_apply, ← morphismRestrict_ι, Scheme.Hom.comp_apply]
  exact hyU

theorem relDim_preimage {X Y S : Scheme.{0}} (f : X ⟶ Y) (g : Y ⟶ S) (U : Y.Opens) [IsIso (f ∣_ U)] {D : ℕ}
    (h : SmoothOfRelativeDimension D (U.ι ≫ g)) : SmoothOfRelativeDimension D ((f ⁻¹ᵁ U).ι ≫ f ≫ g) := by
  have : SmoothOfRelativeDimension (0 + D) ((f ∣_ U) ≫ U.ι ≫ g) := inferInstance
  rw [zero_add] at this
  rw [← morphismRestrict_ι_assoc]
  exact this

theorem relDim_of_dense {Y S : Scheme.{0}} (g : Y ⟶ S) [Smooth g] (W : Y.Opens) (hW : Dense (W : Set Y)) {D : ℕ}
    (h : SmoothOfRelativeDimension D (W.ι ≫ g)) : SmoothOfRelativeDimension D g := by
  choose n W' hW' hd using ReciprocityTheory.ChartRestriction.G.H1.exists_dim g
  have key : ∀ x, n x = D := by
    intro x
    obtain ⟨y, hyW', hyW⟩ := hW.inter_open_nonempty (W' x) (W' x).isOpen ⟨x, hW' x⟩
    have := hd x
    have e₁ : SmoothOfRelativeDimension (0 + n x) ((W' x ⊓ W).ι ≫ g) := by
      rw [← Scheme.homOfLE_ι _ (inf_le_left : W' x ⊓ W ≤ W' x), Category.assoc]; infer_instance
    have e₂ : SmoothOfRelativeDimension (0 + D) ((W' x ⊓ W).ι ≫ g) := by
      rw [← Scheme.homOfLE_ι _ (inf_le_right : W' x ⊓ W ≤ W), Category.assoc]; infer_instance
    simpa using ReciprocityTheory.ChartRestriction.G.H1.dim_unique _ e₁ e₂ ⟨y, hyW', hyW⟩
  have : IsZariskiLocalAtSource (@SmoothOfRelativeDimension D) := HasRingHomProperty.instIsZariskiLocalAtSource
  refine IsZariskiLocalAtSource.of_iSup_eq_top (P := @SmoothOfRelativeDimension D) W'
    (top_le_iff.1 fun x _ => Opens.mem_iSup.2 ⟨x, hW' x⟩) fun x => ?_
  rw [← key x]; exact hd x

theorem isProper_of_isProjOver {K : Type} [Field K] {Y : Scheme.{0}} {h : Y ⟶ Sp K} (hp : IsProjOver h) :
    IsProper h := by
  obtain ⟨N, i, hi, rfl⟩ := hp
  have : IsProper (PSpace.str K N) := isProper_str K N
  infer_instance

end GlobalTheory.CompanionTheory.Hypotheses₂.ResKSide

namespace GlobalTheory.CompanionTheory.Hypotheses₂.ResKSide

theorem resK_of_resolution_principalisation (H₁ : ResolutionCharZero) (H₂ : PrincipalisationCharZero) :
    ResKStatement := by
  intro K _ _ M D X i U ⟨hi, hred, hdense, hU⟩
  have hproj : IsProjOver (i ≫ PSpace.str K M) := ⟨M, i, hi, rfl⟩
  have hP : IsProper (i ≫ PSpace.str K M) := isProper_of_isProjOver hproj
  obtain ⟨X₁, s, hs, hproj₁, hsm₁, hiso₁, hsnc₁⟩ := H₁.projective (i ≫ PSpace.str K M) hproj
  have : Smooth (U.ι ≫ i ≫ PSpace.str K M) := hU.smooth D _
  have hUs : U ≤ (i ≫ PSpace.str K M).smoothLocus := le_smoothLocus _ U
  have : IsIso (s ∣_ U) := isIso_morphismRestrict_of_le s hUs
  have hd₁ : Dense ((s ⁻¹ᵁ U : X₁.Opens) : Set X₁) := by
    refine dense_preimage s (V := (i ≫ PSpace.str K M).smoothLocus) ?_ hdense
    simpa using dense_compl_of_snc _ hsnc₁
  have hP₁ : IsProper (s ≫ i ≫ PSpace.str K M) := isProper_of_isProjOver hproj₁
  have hD₁ : SmoothOfRelativeDimension D (s ≫ i ≫ PSpace.str K M) :=
    relDim_of_dense _ _ hd₁ (relDim_preimage s _ U hU)
  let I : X₁.IdealSheafData := preRed s (U : Set X)ᶜ U.isOpen.isClosed_compl
  have hIs : (I.support : Set X₁) = s.base ⁻¹' (U : Set X)ᶜ := by
    simp [I, preRed]
  have : CompactSpace X₁ := by
    first
    | exact QuasiCompact.compactSpace_of_compactSpace (s ≫ i ≫ PSpace.str K M)
    | exact (quasiCompact_over_affine_iff (s ≫ i ≫ PSpace.str K M)).mp inferInstance
  have : IsLocallyNoetherian X₁ := by
    first
    | exact LocallyOfFiniteType.isLocallyNoetherian (s ≫ i ≫ PSpace.str K M)
    | infer_instance
  have : IsNoetherian X₁ := by first | infer_instance | exact ⟨⟩
  have : NoetherianSpace X₁ := inferInstance
  have hI : ∀ C ∈ irreducibleComponents X₁, ¬ C ⊆ (I.support : Set X₁) := by
    refine SncBlowup.not_subset_of_dense_compl ?_
    rw [hIs]; simpa using hd₁
  obtain ⟨X₂, t, E', hseq, hsm₂, hcart, hsnc₂, hiso₂⟩ :=
    H₂ K D X₁ (s ≫ i ≫ PSpace.str K M) hD₁ inferInstance inferInstance I ⊥ hI (fun x hx => hx.elim)
  have hsupp : ((I.comap t).support : Set X₂) = (t ≫ s).base ⁻¹' (U : Set X)ᶜ := by
    rw [Scheme.IdealSheafData.support_comap]
    simp [hIs] <;> rfl
  have hUc : I.support.compl = s ⁻¹ᵁ U := by
    ext x
    simp [hIs]
  rw [hUc] at hiso₂
  have hiso : IsIso ((t ≫ s) ∣_ U) := by rw [morphismRestrict_comp]; exact @IsIso.comp_isIso _ _ _ _ _ _ _ hiso₂ (isIso_morphismRestrict_of_le s hUs)
  have hT : IsClosed ((t ≫ s).base ⁻¹' (U : Set X)ᶜ) :=
    U.isOpen.isClosed_compl.preimage (t ≫ s).base.hom.continuous
  have hsncT : FinalTheorems.Snc (Scheme.IdealSheafData.vanishingIdeal ⟨_, hT⟩) := by
    have e : (I.comap t).support = ⟨_, hT⟩ := Closeds.ext hsupp
    rwa [e] at hsnc₂
  have hd₂ : Dense (((t ≫ s) ⁻¹ᵁ U : X₂.Opens) : Set X₂) := by
    exact Dense.mono (fun x hx => by simpa using hx) (dense_compl_of_snc _ hsncT)
  have hproj₂ : IsProjOver (t ≫ s ≫ i ≫ PSpace.str K M) :=
    (Resolution.IsBlowupSeq.of_smooth hseq.isSmoothBlowupSeq).isProjOver hproj₁
  have hP₂ := isProper_of_isProjOver hproj₂
  have : CompactSpace X₂ := by
    first
    | exact QuasiCompact.compactSpace_of_compactSpace (t ≫ s ≫ i ≫ PSpace.str K M)
    | exact (quasiCompact_over_affine_iff (t ≫ s ≫ i ≫ PSpace.str K M)).mp inferInstance
  have hsm : Smooth ((t ≫ s) ≫ i ≫ PSpace.str K M) := by simpa using hsm₂
  obtain ⟨hDim, hC⟩ := _root_.GlobalTheory.CompanionTheory.Geo.SncCoordsSide.coordsStatement_side K D X₂ ((t ≫ s) ≫ i ≫ PSpace.str K M) ((t ≫ s) ⁻¹ᵁ U) _ hT inferInstance hsm hd₂
    (relDim_preimage (t ≫ s) _ U hU) hsncT
  obtain ⟨r, j, hj, e⟩ := exists_closed_in_prod ((t ≫ s) ≫ i) (by simpa using hproj₂)
  exact ⟨r, X₂, j, t ≫ s, hj, e, hDim, hiso, hd₂, hC⟩

end GlobalTheory.CompanionTheory.Hypotheses₂.ResKSide
end
end

