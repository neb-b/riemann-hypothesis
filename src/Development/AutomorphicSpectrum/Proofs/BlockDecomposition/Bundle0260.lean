module

public import Mathlib
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0248
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.ZariskiEtaleLifting.CompatH
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.ZariskiEtaleLifting.Bundle0004
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.CechPairings.Imports
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0253
public import Lean.LibrarySuggestions.Basic
public import Lean.Elab.Command
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0239
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0251
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.AcrisKummerUnits.ValuationOfValuationModSquare
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0236
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CompShiftZero
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.DescOfDes
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.ConeSectionRestriction.Bundle0006
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.GlobalSerreRelations.GlobSerreSt
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.RepUnique

@[expose] public section

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ProperBirationalPrimeExists
section
set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry GroundTheory.Arith.SchemeCoh GlobalTheory.CompanionTheory.GE TensorProduct

namespace GlobalTheory.CompanionTheory.GE

namespace KrullPts

theorem exists_specialization_over {W S : Type*} [TopologicalSpace W] [TopologicalSpace S]
    {q : W → S} (hq : IsClosedMap q) {y₀ : W} {m : S} (h : q y₀ ⤳ m) :
    ∃ y₁, y₀ ⤳ y₁ ∧ q y₁ = m := by
  have hcl : IsClosed (q '' closure {y₀}) := hq _ isClosed_closure
  have hmem : q y₀ ∈ q '' closure {y₀} := ⟨y₀, subset_closure rfl, rfl⟩
  obtain ⟨y₁, hy₁, rfl⟩ := h.mem_closed hcl hmem
  exact ⟨y₁, specializes_iff_mem_closure.mpr hy₁, rfl⟩

theorem exists_chart_map {X Z W : Scheme.{0}} (φ : Z ⟶ X) (V : X.Opens) (hV : IsAffineOpen V)
    {R : Type} [CommRing R] [Algebra Γ(X, V) R] (a : W ⟶ Z) (q : W ⟶ Spec (.of R))
    (hc : a ≫ φ = q ≫ Spec.map (CommRingCat.ofHom (algebraMap Γ(X, V) R)) ≫ hV.fromSpec)
    (U : Z.Opens) (hU : IsAffineOpen U) (h : U ≤ φ ⁻¹ᵁ V) :
    letI : Algebra Γ(X, V) Γ(Z, U) := (φ.appLE V U h).hom.toAlgebra
    ∃ l : (a ⁻¹ᵁ U).toScheme ⟶ Spec (.of (R ⊗[Γ(X, V)] Γ(Z, U))),
      l ≫ Spec.map (CommRingCat.ofHom
        (Algebra.TensorProduct.includeLeftRingHom : R →+* R ⊗[Γ(X, V)] Γ(Z, U))) =
        (a ⁻¹ᵁ U).ι ≫ q := by
  letI : Algebra Γ(X, V) Γ(Z, U) := (φ.appLE V U h).hom.toAlgebra
  have e : Spec.map (CommRingCat.ofHom (algebraMap Γ(X, V) Γ(Z, U))) ≫ hV.fromSpec =
      hU.fromSpec ≫ φ := IsAffineOpen.SpecMap_appLE_fromSpec φ hV hU h
  have key : ((a ⁻¹ᵁ U).ι ≫ q) ≫ Spec.map (CommRingCat.ofHom (algebraMap Γ(X, V) R)) =
      ((a ∣_ U) ≫ hU.isoSpec.hom) ≫
        Spec.map (CommRingCat.ofHom (algebraMap Γ(X, V) Γ(Z, U))) := by
    rw [← cancel_mono hV.fromSpec]
    simp only [Category.assoc, e]
    rw [← hc, ← hU.isoSpec_inv_ι]
    simp only [Category.assoc, Iso.hom_inv_id_assoc, morphismRestrict_ι_assoc]
  exact ⟨pullback.lift _ _ key ≫ (pullbackSpecIso _ _ _).hom, by
    rw [Category.assoc, pullbackSpecIso_hom_fst, pullback.lift_fst]⟩

theorem exists_chart_primes {X Z : Scheme.{0}} (φ : Z ⟶ X) [IsProper φ] (V : X.Opens)
    (hV : IsAffineOpen V) {R : Type} [CommRing R] [Algebra Γ(X, V) R] (p : Ideal R) (hp : p.IsPrime)
    (hz : ∃ z : Z, φ z = hV.fromSpec (Spec.map (CommRingCat.ofHom (algebraMap Γ(X, V) R))
      (⟨p, hp⟩ : PrimeSpectrum R))) :
    ∃ (U : Z.Opens) (_ : IsAffineOpen U) (h : U ≤ φ ⁻¹ᵁ V),
      letI : Algebra Γ(X, V) Γ(Z, U) := (φ.appLE V U h).hom.toAlgebra
      ∃ Q₀ Q₁ : Ideal (R ⊗[Γ(X, V)] Γ(Z, U)), Q₀.IsPrime ∧ Q₁.IsPrime ∧ Q₀ ≤ Q₁ ∧
        Q₀.comap (Algebra.TensorProduct.includeLeftRingHom : R →+* R ⊗[Γ(X, V)] Γ(Z, U)) = p ∧
        (Q₁.comap (Algebra.TensorProduct.includeLeftRingHom :
          R →+* R ⊗[Γ(X, V)] Γ(Z, U))).IsMaximal := by
  obtain ⟨z₀, hz₀⟩ := hz
  let g : Spec (.of R) ⟶ X := Spec.map (CommRingCat.ofHom (algebraMap Γ(X, V) R)) ≫ hV.fromSpec
  let a := pullback.fst φ g
  let q := pullback.snd φ g
  have hc : a ≫ φ = q ≫ Spec.map (CommRingCat.ofHom (algebraMap Γ(X, V) R)) ≫ hV.fromSpec :=
    pullback.condition
  obtain ⟨y₀, -, hq₀⟩ := Scheme.Pullback.exists_preimage_pullback (f := φ) (g := g) z₀
    (⟨p, hp⟩ : PrimeSpectrum R) hz₀
  obtain ⟨m, hm, hpm⟩ := Ideal.exists_le_maximal p hp.ne_top
  have hspec : q y₀ ⤳ (⟨m, hm.isPrime⟩ : PrimeSpectrum R) := by
    change pullback.snd φ g y₀ ⤳ _
    rw [hq₀]
    exact (PrimeSpectrum.le_iff_specializes _ _).mp hpm
  obtain ⟨y₁, hsp, hq₁⟩ := exists_specialization_over q.isClosedMap hspec
  have hy₁ : a y₁ ∈ φ ⁻¹ᵁ V := by
    have e : φ (a y₁) = hV.fromSpec (Spec.map (CommRingCat.ofHom (algebraMap Γ(X, V) R)) (q y₁)) := by
      have := congr($hc y₁)
      simpa using this
    change φ (a y₁) ∈ V
    rw [e]
    exact hV.range_fromSpec.subset ⟨_, rfl⟩
  obtain ⟨U', hU', hmem, hle⟩ := TopologicalSpace.Opens.isBasis_iff_nbhd.mp Z.isBasis_affineOpens hy₁
  have hU : IsAffineOpen U' := hU'
  refine ⟨U', hU, hle, ?_⟩
  letI : Algebra Γ(X, V) Γ(Z, U') := (φ.appLE V U' hle).hom.toAlgebra
  obtain ⟨l, hl⟩ := exists_chart_map φ V hV a q hc U' hU hle
  have hT₁ : y₁ ∈ a ⁻¹ᵁ U' := hmem
  have hT₀ : y₀ ∈ a ⁻¹ᵁ U' := hsp.mem_open (a ⁻¹ᵁ U').isOpen hT₁
  let t₀ : (a ⁻¹ᵁ U').toScheme := ⟨y₀, hT₀⟩
  let t₁ : (a ⁻¹ᵁ U').toScheme := ⟨y₁, hT₁⟩
  have ht : t₀ ⤳ t₁ := Topology.IsInducing.subtypeVal.specializes_iff.mp hsp
  have hcomp : ∀ t : (a ⁻¹ᵁ U').toScheme, Spec.map (CommRingCat.ofHom
      Algebra.TensorProduct.includeLeftRingHom) (l t) = q t.1 := fun t => congr($hl t)
  let P₀ : PrimeSpectrum (R ⊗[Γ(X, V)] Γ(Z, U')) := l t₀
  let P₁ : PrimeSpectrum (R ⊗[Γ(X, V)] Γ(Z, U')) := l t₁
  refine ⟨P₀.asIdeal, P₁.asIdeal, P₀.isPrime, P₁.isPrime, ?_, ?_, ?_⟩
  · exact (PrimeSpectrum.le_iff_specializes P₀ P₁).mpr (ht.map l.continuous)
  · exact congrArg PrimeSpectrum.asIdeal ((hcomp t₀).trans hq₀)
  · have e : P₁.asIdeal.comap
        (Algebra.TensorProduct.includeLeftRingHom : R →+* R ⊗[Γ(X, V)] Γ(Z, U')) = m :=
      congrArg PrimeSpectrum.asIdeal ((hcomp t₁).trans hq₁)
    rw [e]
    exact hm

end KrullPts

theorem exists_chart_primes_of_isProper : ∀ {X : Scheme.{0}} (J : X.IdealSheafData) {Z : Scheme.{0}} (ψ : Z ⟶ J.subscheme), IsProper ψ → ∀ (V : X.Opens) (hV : IsAffineOpen V) {R : Type} [CommRing R] [Algebra Γ(X, V) R] (f : Γ(X, V)), IsIso (ψ ∣_ (J.subschemeι ⁻¹ᵁ X.basicOpen f)) → ∀ p : Ideal R, p.IsPrime → (J.ideal ⟨V, hV⟩).map (algebraMap Γ(X, V) R) ≤ p → algebraMap Γ(X, V) R f ∉ p → ∃ (U : Z.Opens) (_ : IsAffineOpen U) (h : U ≤ (ψ ≫ J.subschemeι) ⁻¹ᵁ V), letI : Algebra Γ(X, V) Γ(Z, U) := ((ψ ≫ J.subschemeι).appLE V U h).hom.toAlgebra; ∃ Q₀ Q₁ : Ideal (R ⊗[Γ(X, V)] Γ(Z, U)), Q₀.IsPrime ∧ Q₁.IsPrime ∧ Q₀ ≤ Q₁ ∧ Q₀.comap (Algebra.TensorProduct.includeLeftRingHom : R →+* R ⊗[Γ(X, V)] Γ(Z, U)) = p ∧ (Q₁.comap (Algebra.TensorProduct.includeLeftRingHom : R →+* R ⊗[Γ(X, V)] Γ(Z, U))).IsMaximal := by
  intro X J Z ψ hψ V hV R _ _ f hiso p hp hJ hf
  haveI := hψ
  refine KrullPts.exists_chart_primes (ψ ≫ J.subschemeι) V hV p hp ?_
  let P : PrimeSpectrum Γ(X, V) :=
    Spec.map (CommRingCat.ofHom (algebraMap Γ(X, V) R)) (⟨p, hp⟩ : PrimeSpectrum R)
  change ∃ z : Z, (ψ ≫ J.subschemeι) z = hV.fromSpec P
  have hxf : hV.fromSpec P ∈ X.basicOpen f := by
    have h1 : P ∈ hV.fromSpec ⁻¹ᵁ X.basicOpen f := by
      rw [hV.fromSpec_preimage_basicOpen]
      exact hf
    exact h1
  have hxV : hV.fromSpec P ∈ (V : Set X) := hV.range_fromSpec.subset ⟨_, rfl⟩
  have hxs : hV.fromSpec P ∈ (J.support : Set X) := by
    have h1 : hV.fromSpec P ∈ (J.support : Set X) ∩ (V : Set X) := by
      have e := J.coe_support_inter ⟨V, hV⟩
      refine e.symm.subset ⟨?_, hxV⟩
      rw [Scheme.mem_zeroLocus_iff]
      intro b hb hbx
      have h2 : P ∈ hV.fromSpec ⁻¹ᵁ X.basicOpen b := hbx
      rw [hV.fromSpec_preimage_basicOpen] at h2
      exact h2 (hJ (Ideal.mem_map_of_mem _ hb))
    exact h1.1
  obtain ⟨y, hy⟩ := J.range_subschemeι.ge hxs
  have hyD : y ∈ J.subschemeι ⁻¹ᵁ X.basicOpen f := by
    change J.subschemeι y ∈ X.basicOpen f
    rw [hy]
    exact hxf
  haveI := hiso
  obtain ⟨w, hw⟩ := (ψ ∣_ (J.subschemeι ⁻¹ᵁ X.basicOpen f)).surjective ⟨y, hyD⟩
  have hψw : ψ w.1 = y :=
    (morphismRestrict_base_coe ψ _ w).symm.trans (congrArg Subtype.val hw)
  refine ⟨w.1, ?_⟩
  rw [Scheme.Hom.comp_apply, hψw, hy]

end GlobalTheory.CompanionTheory.GE
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ProperSupportPullbackSystem
section
set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry GroundTheory.Arith.SchemeCoh GlobalTheory.CompanionTheory.GE TensorProduct

namespace GlobalTheory.CompanionTheory.GE.PullSupp

theorem supportedIn_pullback {X Z : Scheme.{0}} (φ : Z ⟶ X) {C : X.Modules} {T₀ : Set X}
    (hT : IsClosed T₀) (h : Scheme.Modules.SupportedIn C T₀) :
    Scheme.Modules.SupportedIn ((Scheme.Modules.pullback φ).obj C) (φ.base ⁻¹' T₀) := by
  refine Scheme.Modules.SupportedIn.of_isZero_restrict fun U hU => ?_
  let V : X.Opens := ⟨T₀ᶜ, hT.isOpen_compl⟩
  have hr : Set.range (U.ι ≫ φ) ⊆ Set.range V.ι := by
    rintro _ ⟨u, rfl⟩
    rw [Scheme.Opens.range_ι]
    intro hx
    exact Set.disjoint_left.1 hU u.2 hx
  let g := IsOpenImmersion.lift V.ι (U.ι ≫ φ) hr
  have hg : g ≫ V.ι = U.ι ≫ φ := IsOpenImmersion.lift_fac _ _ _
  have h0 : IsZero ((Scheme.Modules.restrictFunctor V.ι).obj C) :=
    h.isZero_restrict V disjoint_compl_left
  have h1 : IsZero ((Scheme.Modules.pullback g).obj ((Scheme.Modules.restrictFunctor V.ι).obj C)) :=
    Functor.map_isZero _ h0
  refine h1.of_iso ?_
  exact (Scheme.Modules.restrictFunctorIsoPullback U.ι).app _ ≪≫
    (Scheme.Modules.pullbackComp U.ι φ).app C ≪≫ (Scheme.Modules.pullbackCongr hg.symm).app C ≪≫
    ((Scheme.Modules.pullbackComp g V.ι).app C).symm ≪≫
    (Scheme.Modules.pullback g).mapIso ((Scheme.Modules.restrictFunctorIsoPullback V.ι).app C).symm

end GlobalTheory.CompanionTheory.GE.PullSupp

namespace GlobalTheory.CompanionTheory.GE.PullSupp

theorem supportedIn_cokernel_pullSys {A : Type} [CommRing A] [IsNoetherianRing A] (I : Ideal A)
    {X Z : Scheme.{0}} [Z.Over (Spec (.of A))] (φ : Z ⟶ X) (E : X.Modules) (S : ℕ → Subobject E)
    {T₀ : Set X} (hT : IsClosed T₀) (h : Scheme.Modules.SupportedIn (cokernel (S 0).arrow) T₀) :
    Scheme.Modules.SupportedIn (cokernel (pullSys I φ E S 0).arrow) (φ.base ⁻¹' T₀) := by
  let f := (Scheme.Modules.pullback φ).map (S 0).arrow
  have hle : imageSubobject f ≤ pullSys I φ E S 0 := le_sup_left
  have w : f ≫ cokernel.π (pullSys I φ E S 0).arrow = 0 := by
    rw [← imageSubobject_arrow_comp f, ← Subobject.ofLE_arrow hle, Category.assoc, Category.assoc,
      cokernel.condition, comp_zero, comp_zero]
  have hd : Epi (cokernel.desc f _ w) := epi_of_epi_fac (cokernel.π_desc f _ w)
  have h1 : Scheme.Modules.SupportedIn (cokernel f) (φ.base ⁻¹' T₀) :=
    (supportedIn_pullback φ hT h).of_iso (PreservesCokernel.iso (Scheme.Modules.pullback φ) (S 0).arrow)
  exact Scheme.Modules.SupportedIn.of_epi (cokernel.desc f _ w) h1

theorem exists_proper_preimage {A : Type} [CommRing A] {X Z : Scheme.{0}} [X.Over (Spec (.of A))]
    [Z.Over (Spec (.of A))] (φ : Z ⟶ X) (hφ : IsProper φ)
    (hc : φ ≫ (X ↘ Spec (.of A)) = (Z ↘ Spec (.of A))) (T : X.IdealSheafData)
    (hT : IsProper (T.subschemeι ≫ (X ↘ Spec (.of A)))) :
    ∃ T' : Z.IdealSheafData, IsProper (T'.subschemeι ≫ (Z ↘ Spec (.of A))) ∧
      φ.base ⁻¹' (T.support : Set X) ⊆ (T'.support : Set Z) := by
  let p := pullback.fst φ T.subschemeι
  let q := pullback.snd φ T.subschemeι
  have hpc : IsClosedImmersion p := inferInstance
  let T' : Z.IdealSheafData := p.ker
  have hk1 : p.ker ≤ T'.subschemeι.ker := by rw [Scheme.IdealSheafData.ker_subschemeι]
  have hk2 : T'.subschemeι.ker ≤ p.ker := by rw [Scheme.IdealSheafData.ker_subschemeι]
  let u := IsClosedImmersion.lift p T'.subschemeι hk1
  let v := IsClosedImmersion.lift T'.subschemeι p hk2
  have hu : u ≫ p = T'.subschemeι := IsClosedImmersion.lift_fac _ _ _
  have hv : v ≫ T'.subschemeι = p := IsClosedImmersion.lift_fac _ _ _
  refine ⟨T', ?_, ?_⟩
  · have hq : IsProper q := by haveI := hφ; infer_instance
    have huc : IsClosedImmersion u := by
      have : IsClosedImmersion (u ≫ p) := by rw [hu]; infer_instance
      exact IsClosedImmersion.of_comp u p
    have e : T'.subschemeι ≫ (Z ↘ Spec (.of A)) = u ≫ q ≫ (T.subschemeι ≫ (X ↘ Spec (.of A))) := by
      rw [← hu, ← hc, Category.assoc, ← Category.assoc p, pullback.condition]
      simp only [Category.assoc]
      rfl
    rw [e]
    infer_instance
  · intro z hz
    obtain ⟨w, hw⟩ := T.range_subschemeι.ge hz
    obtain ⟨t, ht, -⟩ := Scheme.Pullback.exists_preimage_pullback (f := φ) (g := T.subschemeι) z w hw.symm
    rw [← T'.range_subschemeι]
    refine ⟨v t, ?_⟩
    have hv' : v ≫ T'.subschemeι = pullback.fst φ T.subschemeι := hv
    rw [← ht, ← hv']
    rfl

theorem propSupp_pullSys : ∀ {A : Type} [CommRing A] [IsNoetherianRing A] (I : Ideal A) {X Z : Scheme.{0}}
    [X.Over (Spec (.of A))] [Z.Over (Spec (.of A))] [IsLocallyNoetherian X] (φ : Z ⟶ X), IsProper φ →
    φ ≫ (X ↘ Spec (.of A)) = (Z ↘ Spec (.of A)) → ∀ {E : X.Modules}, IsCoherent E →
    ∀ {S : ℕ → Subobject E}, ClosedSys I E S → PropSupp A (S 0) → PropSupp A (pullSys I φ E S 0) := by
  intro A _ _ I X Z _ _ _ φ hφ hc E _ S _ hS
  obtain ⟨T, hTp, hTs⟩ := hS
  obtain ⟨T', hT'p, hT's⟩ := exists_proper_preimage φ hφ hc T hTp
  exact ⟨T', hT'p, (supportedIn_cokernel_pullSys I φ E S T.support.isClosed hTs).mono hT's⟩

end GlobalTheory.CompanionTheory.GE.PullSupp
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.PullTransport
section
set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry DividedPowers GroundTheory.PAdicHodge GlobalTheory.LogCris CrystallineSemistableComparison CrystallineSemistableComparison.PAlg CrystallineSemistableComparison.B

noncomputable section

namespace GlobalTheory.CompanionTheory.FirstChernComparison

universe w w' u₁ v₁ u₂ v₂ u₃ v₃

theorem pull_transport' {R : Type} [CommRing R] {Th : Type u₁} [Category.{v₁} Th] {Ec : Type u₂} [Category.{v₂} Ec]
    {C : Type u₃} [Category.{v₃} C]  (F : Th ⥤ ModuleCat.{w} R) (F' : Ec ⥤ ModuleCat.{w'} R) (m : CH.Mor F F' (RingHom.id R)) (G : C ⥤ Ec)
    (x : CH.H F 2) {Pc : CH.Cn ((G ⋙ m.G) ⋙ F) 2 → Prop} (h : ∃ (c : CH.Cn ((G ⋙ m.G) ⋙ F) 2) (hc : CH.d _ 2 c = 0), (CH.cx _).cls c hc = (CH.Mor.restrict F (G ⋙ m.G)).pull 2 x ∧ Pc c)
    (P : CH.Cn (G ⋙ F') 2 → Prop) (hP : ∀ z : CH.Cn (G ⋙ F') 2, ∀ c, (∀ s, z s = m.τ _ (c s)) → Pc c → P z) :
    ∃ (z : CH.Cn (G ⋙ F') 2) (hz : CH.d (G ⋙ F') 2 z = 0), P z ∧
      (CH.cx _).cls z hz = (CH.Mor.restrict F' G).pull 2 (m.pull 2 x) := by
  obtain ⟨c, hc, h, hp⟩ := h
  obtain ⟨hz, e⟩ := pull_transport F F' m G x c hc h
  exact ⟨_, hz, hP _ c (fun _ => rfl) hp, e⟩

section
variable {l : ℕ} [Fact l.Prime] {O : Type} [CommRing O] {X : Scheme.{0}} {q : X ⟶ Spec (CommRingCat.of O)} {κ : O →+* OC l}
  {C : Type 1} [Category.{0} C] {G : C ⥤ El (PX q κ)} {D : E.LineData X} (k : Bool) (n : ℕ)

theorem st1 (Λ : E.Lift G D) (x : ∀ n, Hc (schFn q) κ k n 2) (hx : IsFirstChernFamily q D κ k x) :
    ∃ (c : CH.Cn (gG k n G ⋙ OM _ ((PAlg.base l).cris n)) 2) (hz : CH.d _ 2 c = 0),
      (CH.cx _).cls _ hz = (CH.Mor.restrict (OM _ ((PAlg.base l).cris n)) (gG k n G)).pull 2 (x n) ∧
      c = (lam k n Λ).coc ((PAlg.base l).cris n) (l * n) := by
  have h := hx n C (gG k n G) (lam k n Λ)
  exact ⟨_, h.choose, h.choose_spec, rfl⟩

theorem st2 (Λ : E.Lift G D) (s : ComposableArrows C 2) (y : (G.obj (s.obj (Fin.last 2))).1.obj.Acr n)
    (hy : y = dlog (DD k (G.obj (s.obj (Fin.last 2))).1.obj n) (l * n) ((lam k n Λ).r s).val) :
    E.IsLog (G.obj (s.obj (Fin.last 2))).1.obj n (E.tei (G.obj (s.obj (Fin.last 2))).1.obj (Λ.r s)) y := by
  rw [hy]
  have h1 : (G.obj (s.obj (Fin.last 2))).1.obj.sharp (Λ.r s).val = 1 :=
    sharp_r Λ (s.map' 0 1) (s.map' 1 2) (s.map' 0 2) (by rw [← Functor.map_comp]; rfl)
  exact isLog_dlog k _ n _ h1 _ (lam_r k n Λ s)

theorem st3 (Λ : E.Lift G D) (x : ∀ n, Hc (schFn q) κ k n 2) (hx : IsFirstChernFamily q D κ k x) :
    ∃ (z : CH.Cn (G ⋙ CH.modF (AcrEl (PX q κ) n)) 2) (hz : CH.d _ 2 z = 0), Λ.IsCoc n z ∧
      (CH.cx _).cls z hz = (CH.Mor.restrict (CH.modF (AcrEl (PX q κ) n)) G).pull 2 (β (schFn q) κ k n 2 (x n)) :=
  pull_transport' (Oc (schFn q) κ k n) (CH.modF (AcrEl ((schFn q).pt κ) n)) (βMor (schFn q) κ k n) G (x n)
    (st1 k n Λ x hx) (fun z => Λ.IsCoc n z) (fun z c hs hc s => st2 k n Λ s _ ((hs s).trans (congrArg _ (congrFun hc s))))
end

theorem main : ∀ (l : ℕ) [Fact l.Prime], FirstChernCompatible l := by
  intro l _ O _ X q κ k D x hx C _ G Λ n
  exact st3 k n Λ x hx

end GlobalTheory.CompanionTheory.FirstChernComparison
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.PushforwardClosedSystemAuxiliary
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry GroundTheory.Arith.SchemeCoh GlobalTheory.CompanionTheory.GE TensorProduct

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.CompanionTheory.GE.KerSupp

theorem supportedIn_cokernel_kernelSubobject {X : Scheme.{0}} {F G : X.Modules} (g : F ⟶ G) {T : Set X}
    (h : Scheme.Modules.SupportedIn G T) :
    Scheme.Modules.SupportedIn (cokernel (kernelSubobject g).arrow) T := by
  let S : ShortComplex X.Modules := ShortComplex.mk (kernel.ι g) g (kernel.condition _)
  have hex : S.Exact := ShortComplex.exact_kernel _
  have hm : Mono (cokernel.desc S.f S.g S.zero) := S.exact_iff_mono_cokernel_desc.1 hex
  have h1 : Scheme.Modules.SupportedIn (cokernel (kernel.ι g)) T :=
    Scheme.Modules.SupportedIn.of_mono (cokernel.desc S.f S.g S.zero) h
  have e : (kernelSubobjectIso g).hom ≫ kernel.ι g = (kernelSubobject g).arrow :=
    kernelSubobject_arrow g
  let i : cokernel (kernelSubobject g).arrow ≅ cokernel (kernel.ι g) :=
    cokernelIsoOfEq e.symm ≪≫ (cokernelEpiComp (kernelSubobjectIso g).hom _)
  exact h1.of_iso i.symm

theorem toImage_surjective {Y X : Scheme.{0}} (f : Y ⟶ X) [IsProper f] : Surjective f.toImage := by
  refine ⟨fun y => ?_⟩
  have h1 : f.imageι y ∈ (f.ker.support : Set X) := f.ker.range_subschemeι.le ⟨y, rfl⟩
  rw [Scheme.Hom.support_ker, f.isClosedMap.isClosed_range.closure_eq] at h1
  obtain ⟨x, hx⟩ := h1
  refine ⟨x, f.imageι.isEmbedding.injective ?_⟩
  rw [← hx, ← Scheme.Hom.comp_apply, Scheme.Hom.toImage_imageι]

theorem isProper_image {S Y X : Scheme.{0}} (f : Y ⟶ X) (p : X ⟶ S) [IsSeparated p]
    [LocallyOfFiniteType p] [QuasiCompact p] [IsProper f] (hY : IsProper (f ≫ p)) :
    IsProper (f.ker.subschemeι ≫ p) := by
  have := toImage_surjective f
  have hu : UniversallyClosed (f.toImage ≫ f.ker.subschemeι ≫ p) := by
    rw [← Category.assoc]
    change UniversallyClosed ((f.toImage ≫ f.imageι) ≫ p)
    rw [Scheme.Hom.toImage_imageι]
    infer_instance
  have : UniversallyClosed (f.ker.subschemeι ≫ p) := .of_comp_surjective f.toImage _
  exact ⟨⟩

theorem propSupp_adjKer {A : Type} [CommRing A] [IsNoetherianRing A] {X Z : Scheme.{0}}
    [X.Over (Spec (.of A))] [Z.Over (Spec (.of A))] [IsSeparated (X ↘ Spec (.of A))]
    [LocallyOfFiniteType (X ↘ Spec (.of A))] [QuasiCompact (X ↘ Spec (.of A))] (φ : Z ⟶ X)
    (hφ : IsProper φ) (hc : φ ≫ (X ↘ Spec (.of A)) = (Z ↘ Spec (.of A))) {E : X.Modules}
    (B : Subobject ((Scheme.Modules.pullback φ).obj E)) (hB : PropSupp A B) :
    PropSupp A (adjKer φ B) := by
  obtain ⟨TZ, hTZ, hsupp⟩ := hB
  let f : TZ.subscheme ⟶ X := TZ.subschemeι ≫ φ
  have hf : IsProper f := inferInstance
  have hfp : IsProper (f ≫ (X ↘ Spec (.of A))) := by
    change IsProper ((TZ.subschemeι ≫ φ) ≫ (X ↘ Spec (.of A)))
    rw [Category.assoc, hc]
    exact hTZ
  refine ⟨f.ker, isProper_image f _ hfp, ?_⟩
  have hpush := hsupp.pushforward φ
  have hsub : φ.base '' (TZ.support : Set Z) ⊆ (f.ker.support : Set X) := by
    rintro _ ⟨z, hz, rfl⟩
    obtain ⟨w, hw⟩ := TZ.range_subschemeι.ge hz
    rw [Scheme.Hom.support_ker]
    refine subset_closure ⟨w, ?_⟩
    rw [← hw]
    rfl
  exact supportedIn_cokernel_kernelSubobject (adjMap φ B) (hpush.mono hsub)

end GlobalTheory.CompanionTheory.GE.KerSupp
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.RestrictedSystemKilledByIdeal
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry GroundTheory.Arith.SchemeCoh GlobalTheory.CompanionTheory.GE

namespace GlobalTheory.CompanionTheory.GE

theorem killed_restrictSys {A : Type} [CommRing A] [IsNoetherianRing A] (I : Ideal A)
    {X : Scheme.{0}} [X.Over (Spec (.of A))] {E : X.Modules} (J : X.IdealSheafData)
    (D : Subobject E) (S : ℕ → Subobject E) (c : ℕ)
    (h : ∀ (n : ℕ) (U : X.affineOpens) (a : Γ(X, U)), a ∈ J.ideal U →
      ∀ x ∈ secs D U, a • x ∈ secs (S n) U) (e : ℕ) :
    Killed J (restrictSys I D S c e) := by
  intro U a ha x
  have hle : (Subobject.pullback D.arrow).obj (S (e + c)) ≤ GlobalTheory.CompanionTheory.GE.restrictSys I D S c e := by
    unfold GlobalTheory.CompanionTheory.GE.restrictSys
    exact le_sup_left
  have hmem : a • x ∈ GlobalTheory.CompanionTheory.GE.secs ((Subobject.pullback D.arrow).obj (S (e + c))) U := by
    rw [_root_.GlobalTheory.CompanionTheory.GE.secs_pullback_arrow, Set.mem_preimage, Scheme.Modules.Hom.app_smul]
    exact h (e + c) U a ha _ (by unfold GlobalTheory.CompanionTheory.GE.secs; exact Set.mem_range_self x)
  unfold GlobalTheory.CompanionTheory.GE.secs at hmem ⊢
  obtain ⟨y, hy⟩ := hmem
  refine ⟨ConcreteCategory.hom (Scheme.Modules.Hom.app (Subobject.ofLE _ _ hle) U) y, ?_⟩
  rw [← hy, ← Subobject.ofLE_arrow hle, Scheme.Modules.Hom.comp_app] <;> rfl

end GlobalTheory.CompanionTheory.GE
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.StepDesc
section
set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry DividedPowers GroundTheory.PAdicHodge GlobalTheory.LogCris GlobalTheory.PDA CrystallineSemistableComparison CrystallineSemistableComparison.CH CrystallineSemistableComparison.PAlg CrystallineSemistableComparison.B

noncomputable section

namespace GlobalTheory.CompanionTheory.DescTest

section
variable {l : ℕ} [Fact l.Prime] {O : Type} [CommRing O] (F : Fn O) (κ : O →+* OC l) (ε : Eps l)
    (k : Bool) (n : ℕ) (ρ : ℕ → ℕ) (hρ : Slow ρ)

theorem step_desc (hOut : D.Out l) (hk : k = false ∨ ρ = 0) (r : ℕ) :
    Desc (ε.qk 1 - 1) (((flt F κ ε k n ρ hρ).comap (gE F κ k n)).S r).fn (jE (F.pt κ)) :=
  desc_fil F κ ε k n ρ hρ hk r _ (des_qk hOut ε (GlobalTheory.CompanionTheory.EpsFacts.eps_facts ε).1 n (ρ r))

theorem xi_thick (T : (F.pt κ).Elements) :
    ((gE F κ k n).obj T).i ((base l).cris n (∑ i ∈ Finset.range l, ε.qk 1 ^ i)) ∈ ((gE F κ k n).obj T).J :=
  xi_mem F κ k n T _ ((GlobalTheory.CompanionTheory.EpsFacts.eps_facts ε).2.2.1 T.1 n)

theorem mu_factor : ε.μ = (ε.qk 1 - 1) * ∑ i ∈ Finset.range l, ε.qk 1 ^ i :=
  (GlobalTheory.CompanionTheory.EpsFacts.eps_facts ε).2.2.2.1

end


set_option maxHeartbeats 1000000 in
theorem main : ∀ {l : ℕ} [Fact l.Prime], D.Out l → ∀ {O : Type} [CommRing O] (F : Fn O) (κ : O →+* OC l) (ε : Eps l)
    (k : Bool) (n : ℕ) (ρ : ℕ → ℕ) (hρ : Slow ρ), (k = false ∨ ρ = 0) →
    Desc (Polynomial.X : Polynomial ℤ) (gE F κ k n ⋙ (flt F κ ε k n ρ hρ).rees) (jE (F.pt κ)) := by
  intro l _ hOut O _ F κ ε k n ρ hρ hk
  exact desc_flt (b := bs l k n) (L := Lc F κ k n) (Λ := Acris l) (F.pt κ) ((base l).cris n) (gE F κ k n) ρ hρ
    ε.μ (ε.μ_mem k (base l) n) (jE (F.pt κ)) (ε.qk 1 - 1) (∑ i ∈ Finset.range l, ε.qk 1 ^ i)
    (mu_factor ε) (xi_thick F κ ε k n) (step_desc F κ ε k n ρ hρ hOut hk)

end GlobalTheory.CompanionTheory.DescTest
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.StrictMonoSnocPermEqSuccAboveStatement
section
set_option backward.isDefEq.respectTransparency false
set_option autoImplicit false
open CategoryTheory AlgebraicGeometry GlobalTheory.LogCris CrystallineSemistableComparison CrystallineSemistableComparison.Pb GlobalTheory.CompanionTheory.ConeLocal
open GlobalTheory.CatH (face toLast)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.strictMono_snoc_perm_eq_succAbove : ∀ {n : ℕ} (I : Fin n → Fin (n + 1)) (k : Fin (n + 1)) (π : Equiv.Perm (Fin (n + 1))), StrictMono I →
    Fin.snoc (α := fun _ => Fin (n + 1)) I k = ⇑π → I = k.succAbove := by
  first | exact @GlobalTheory.CompanionTheory.ConeLocal.SnocPerm.eq_succAbove_of_snoc_eq_perm | exact GlobalTheory.CompanionTheory.ConeLocal.SnocPerm.eq_succAbove_of_snoc_eq_perm | (intros; apply GlobalTheory.CompanionTheory.ConeLocal.SnocPerm.eq_succAbove_of_snoc_eq_perm <;> assumption)
end

