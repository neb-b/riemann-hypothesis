module

public import Mathlib
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1298
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2029
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2023
public import Development.AbelianVarietyTheory.Definitions.Divisors.SurjectiveOfIsPullbackSqZero
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsNoetherianRingDualNumber
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.AbelianHodgeDeRham
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.BijectiveCechDeRhamComparisonDegreeOne
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.KawamataViehweg
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsLogCanonicalMultipleCanonical
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0765
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0004
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0189
public import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.CubeTheorem.SchemeModels
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0067
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsProperSpreadsOut
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0734
public import Development.AbelianVarietyTheory.Definitions.Divisors.SubsetSpanBy
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.GenericExistsUniqueOActOfIsGrpPullback
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0017
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0019
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0008
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0026
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0022
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2041

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSectionTranslateTensorFibreNonvanishing
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section
namespace GlobalTheory.TwistFibreGen

theorem exists_sec_of_closed {X : Scheme.{0}} [CompactSpace X] (M : LB X)
    (h : ∀ z : X, IsClosed ({z} : Set X) → ∃ s : LB.Sec M, z ∈ nonzeroLocus s) (z : X) :
    ∃ s : LB.Sec M, z ∈ nonzeroLocus s := by
  by_contra hz
  push_neg at hz
  let C : Set X := ⋂ s : LB.Sec M, ((nonzeroLocus s : X.Opens) : Set X)ᶜ
  have hC : IsClosed C := isClosed_iInter fun s => (nonzeroLocus s).isOpen.isClosed_compl
  obtain ⟨w, hw, hcl⟩ := hC.exists_closed_singleton ⟨z, Set.mem_iInter.2 fun s => hz s⟩
  obtain ⟨s, hs⟩ := h w hcl
  exact Set.mem_iInter.1 hw s hs

theorem compactSpace_fibre {S : Scheme.{0}} (P : PolAV S) (k : Type) [Field k]
    (t : Spec (CommRingCat.of k) ⟶ S) : CompactSpace (Over.mk t ⊗ P.A).left := by
  have := P.isAb.proper
  have : QuasiCompact (pullback.fst t P.A.hom) := inferInstance
  exact QuasiCompact.compactSpace_of_compactSpace (pullback.fst t P.A.hom)

theorem exists_sec_algClosed {S : Scheme.{0}} (P : PolAV S) (K : Type) [Field K] [IsAlgClosed K]
    (t : Spec (CommRingCat.of K) ⟶ S) (c : Over.mk t ⟶ P.A) (z : (Over.mk t ⊗ P.A).left) :
    ∃ s : LB.Sec (twistLB P.A P.L 2 c), z ∈ nonzeroLocus s := by
  have := compactSpace_fibre P K t
  refine exists_sec_of_closed _ (fun z hz => ?_) z
  have := P.isAb.smooth
  have : LocallyOfFiniteType (fst (Over.mk t) P.A).left :=
    (inferInstance : LocallyOfFiniteType (pullback.fst t P.A.hom))
  let f := (fst (Over.mk t) P.A).left
  let p₀ := pointOfClosedPoint f z hz
  have hw : p₀ ≫ (Over.mk t ⊗ P.A).hom = (Over.mk t).hom := by
    rw [← Over.w (fst (Over.mk t) P.A), ← Category.assoc, pointOfClosedPoint_comp]
    exact Category.id_comp _
  let q : Over.mk t ⟶ Over.mk t ⊗ P.A := Over.homMk p₀ hw
  have hq : q ≫ fst (Over.mk t) P.A = 𝟙 _ := by
    ext1
    exact pointOfClosedPoint_comp f z hz
  obtain ⟨s, hs⟩ := _root_.GlobalTheory.TwistFibre.exists_sec_twist_mem_nonzeroLocus S P K t c (q ≫ snd _ _) (IsLocalRing.closedPoint _)
  refine ⟨s, ?_⟩
  have e : lift (𝟙 (Over.mk t)) (q ≫ snd (Over.mk t) P.A) = q := by
    rw [← hq, lift_comp_fst_snd]
  rw [e] at hs
  have h2 : q.left (IsLocalRing.closedPoint K) = z := pointOfClosedPoint_apply f z hz _
  rw [← h2]
  exact hs

theorem exists_sec_mem_nonzeroLocus : ∀ (S : Scheme.{0}) (P : PolAV S) (k : Type) [Field k]
    (t : Spec (CommRingCat.of k) ⟶ S) (c : Over.mk t ⟶ P.A) (y : (Over.mk t ⊗ P.A).left),
    ∃ s : LB.Sec (twistLB P.A P.L 2 c), y ∈ nonzeroLocus s := by
  intro S P k _ t c y
  exact _root_.GlobalTheory.TwistDescent.exists_sec_of_baseChange S P k (AlgebraicClosure k) t c (fun z => exists_sec_algClosed P _ _ _ z) y

end GlobalTheory.TwistFibreGen
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSemiAbelianPullbackFramedTangent
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.CompHS
open GlobalTheory.FlagMod (ev frX frVec)
open GlobalTheory.FlagTan (psiSet HIx VIx TIx IsDef IsVert KSIso)
open ReciprocityTheory.ChartRestriction.G.PullbackSections (tv)
open ReciprocityTheory.ChartRestriction.G.DVR.FlatBC (algX)
open GlobalTheory.LogPole
open scoped Classical
open ReciprocityTheory.ChartRestriction.G.Geo.Tor

namespace GlobalTheory.FramedTransport

theorem exists_model_pullback : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (TF : TorFlag Xo c) (U : TF.Y.X.affineOpens) (n : ℕ) (e : (Σ τ : E →+* ℂ, Fin (Dw.mult τ)) ≃ Fin n) (v : Fin n → (Sp (DualNumber Γ(TF.Y.X, U.1)) ⟶ TF.Y.t.G.left)) (K : Type) [Field K] [Algebra c.F K] (P : FrPt Xo c K) (hU : ⊤ ≤ (frX P ≫ TF.Y.j) ⁻¹ᵁ U.1), IsBaseFrame TF U e v P hU → ∀ (y' : Sp (DualNumber K) ⟶ Xo.XF c), y' ≫ pullback.snd _ _ = spMap (algebraMap c.F (DualNumber K)) → GlobalTheory.DeRham.epsRed K ≫ y' = frX P → ∀ (A : Over (Sp K)) [GrpObj A] (A' : Over (Sp (DualNumber K))) [GrpObj A'] (π : A.left ⟶ Xo.univ.t.G.left) (π' : A'.left ⟶ Xo.univ.t.G.left) (i : A.left ⟶ A'.left) (ub : ∀ σ : E →+* ℂ, Fin (Dw.mult σ) → (epsR K ⟶ A)), IsGrpPullback A A' (GlobalTheory.DeRham.epsRed K) i → IsGrpPullback A Xo.univ.t.G P.x π → IsGrpPullback A' Xo.univ.t.G (y' ≫ pullback.fst _ _) π' → i ≫ π' = π → (∀ σ k, (ub σ k).left ≫ π = P.u σ k) → ∃ (ι : A.left ⟶ TF.Y.t.G.left) (ι' : A'.left ⟶ TF.Y.t.G.left), IsGrpPullback A TF.Y.t.G (frX P ≫ TF.Y.j) ι ∧ IsGrpPullback A' TF.Y.t.G (y' ≫ TF.Y.j) ι' ∧ i ≫ ι' = ι ∧ (∀ σ k, (ub σ k).left ≫ ι = spMap (dualMap (ev (frX P ≫ TF.Y.j) U.1 hU)) ≫ v (e ⟨σ, k⟩)) ∧ LBIso (TF.Y.t.PP.L.pull ι) (Xo.univ.t.PP.L.pull π) ∧ ⨆ k, (Xo.univ.t.PP.L.pull π).U k = ⊤ := by
  intro E _ _ _ H Dw l Xo c TF U n e v K _ _ P hU hB y' hy' hred A _ A' _ π π' i ub hi hπ hπ' hiπ hub
  have hx : frX P ≫ pullback.fst _ _ = P.x := pullback.lift_fst _ _ _
  have hπ0 : IsGrpPullback A Xo.univ.t.G (frX P ≫ pullback.fst _ _) π := hπ.congr hx.symm rfl
  have w0 : π ≫ Xo.univ.t.G.hom = (A.hom ≫ frX P) ≫ pullback.fst _ _ := by
    rw [hπ0.1.w, Category.assoc]
  have w1 : π' ≫ Xo.univ.t.G.hom = (A'.hom ≫ y') ≫ pullback.fst _ _ := by
    rw [hπ'.1.w, Category.assoc]
  let lam := TF.Y.m0.cart.1.lift π (A.hom ≫ frX P) w0
  let lam' := TF.Y.m0.cart.1.lift π' (A'.hom ≫ y') w1
  have hl0 : lam ≫ TF.Y.m0.φ = π := TF.Y.m0.cart.1.lift_fst _ _ _
  have hl0' : lam' ≫ TF.Y.m0.φ = π' := TF.Y.m0.cart.1.lift_fst _ _ _
  have hs : lam ≫ TF.Y.oF.t.G.hom = A.hom ≫ frX P := TF.Y.m0.cart.1.lift_snd _ _ _
  have hs' : lam' ≫ TF.Y.oF.t.G.hom = A'.hom ≫ y' := TF.Y.m0.cart.1.lift_snd _ _ _
  have g1 : IsGrpPullback A TF.Y.oF.t.G (frX P) lam :=
    IsGrpPullback.cancel TF.Y.m0.cart (hπ0.congr rfl hl0.symm) hs
  have g1' : IsGrpPullback A' TF.Y.oF.t.G y' lam' :=
    IsGrpPullback.cancel TF.Y.m0.cart (hπ'.congr rfl hl0'.symm) hs'
  have hil : i ≫ lam' = lam := by
    apply TF.Y.m0.cart.1.hom_ext
    · rw [Category.assoc, hl0', hiπ, hl0]
    · rw [Category.assoc, hs', hs, ← Category.assoc, hi.1.w, Category.assoc, hred]
  obtain ⟨w, hw, -⟩ := TF.Y.m.lin
  obtain ⟨w0', hw0, -⟩ := TF.Y.m0.lin
  have i1 : LBIso (TF.Y.oF.t.PP.L.pull lam) (TF.Y.t.PP.L.pull (lam ≫ TF.Y.m.φ)) :=
    LBIso.chartPull (ReciprocityTheory.ChartRestriction.G.Geo.Tor.chartPullPull _ lam lam rfl)
      (chartPullSame _ (fun _ => lam ≫ TF.Y.m.φ) (fun _ => TF.Y.m.φ) (fun _ => 1) lam (fun _ => rfl)) ⟨w, hw⟩
  have i2 : LBIso (TF.Y.oF.t.PP.L.pull lam) (Xo.univ.t.PP.L.pull (lam ≫ TF.Y.m0.φ)) :=
    LBIso.chartPull (ReciprocityTheory.ChartRestriction.G.Geo.Tor.chartPullPull _ lam lam rfl)
      (chartPullSame _ (fun _ => lam ≫ TF.Y.m0.φ) (fun _ => TF.Y.m0.φ) (fun _ => 1) lam (fun _ => rfl)) ⟨w0', hw0⟩
  rw [hl0] at i2
  refine ⟨lam ≫ TF.Y.m.φ, lam' ≫ TF.Y.m.φ, g1.comp TF.Y.m.cart, g1'.comp TF.Y.m.cart, ?_, ?_, ?_, ?_⟩
  · rw [← Category.assoc, hil]
  · intro σ k
    rw [← hB σ k]
    unfold frVec
    rw [FlagMod.toModel_left, ← Category.assoc]
    congr 1
    apply TF.Y.m0.cart.1.hom_ext
    · rw [Category.assoc, hl0, hub, FlagMod.liftTan_univ]
    · rw [Category.assoc, hs, ← Category.assoc, Over.w (ub σ k), FlagMod.liftTan_over]
      rfl
  · exact LBIso.trans (pull_isLB TF.Y.t.PP.isLB _) (pull_isLB TF.Y.oF.t.PP.isLB _)
      (pull_isLB Xo.univ.t.PP.isLB _) i1.symm i2
  · exact (pull_isLB Xo.univ.t.PP.isLB π).cover

end GlobalTheory.FramedTransport
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSemilinearLiftOfProjective
section
open CategoryTheory AlgebraicGeometry KaehlerDifferential DividedPowers ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.DeRham GlobalTheory.SqLift GlobalTheory.LiftSys GlobalTheory.Published
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.LiftSys

theorem exists_semilinear_lift_of_projective : ∀ (R R₀ : Type) [CommRing R] [CommRing R₀] (π : R →+* R₀), Function.Surjective π → ∀ (P : Type) [AddCommGroup P] [Module R₀ P], Module.Projective R₀ P → ∀ (M M' : Type) [AddCommGroup M] [Module R M] [AddCommGroup M'] [Module R M'] (W : Submodule R M), (∀ r, π r = 0 → ∀ m ∈ W, r • m = 0) → ∀ (q : M →ₗ[R] M') (v : P →+ M'), (∀ r w, v (π r • w) = r • v w) → (∀ w, ∃ m ∈ W, q m = v w) → ∃ u : P →+ M, (∀ r w, u (π r • w) = r • u w) ∧ (∀ w, u w ∈ W) ∧ ∀ w, q (u w) = v w := by
  intro R R₀ _ _ π hπ P _ _ hP M M' _ _ _ _ W hW q v hv hq
  classical
  choose m hmW hmq using hq
  choose σ hσ using hπ
  have key : ∀ (r s : R) (x : M), x ∈ W → π r = π s → r • x = s • x := by
    intro r s x hx h
    have := hW (r - s) (by rw [map_sub, h, sub_self]) x hx
    rwa [sub_smul, sub_eq_zero] at this
  let f : P → R₀ →+ M := fun w => AddMonoidHom.mk' (fun c => σ c • m w) (by
    intro a b
    rw [← add_smul]
    exact key _ _ _ (hmW w) (by rw [map_add (f := _), hσ, hσ, hσ]))
  have hf : ∀ w c, f w c = σ c • m w := fun _ _ => rfl
  let g : (P →₀ R₀) →+ M := Finsupp.liftAddHom f
  have hg : ∀ w c, g (Finsupp.single w c) = σ c • m w := by
    intro w c
    simp only [g, Finsupp.liftAddHom_apply_single, hf]
  have g1 : ∀ r x, g (π r • x) = r • g x := by
    intro r x
    induction x using Finsupp.induction_linear with
    | zero => simp
    | add a b ha hb => rw [smul_add, map_add (f := _), map_add (f := _), ha, hb, smul_add]
    | single w c =>
      rw [Finsupp.smul_single, hg, hg, smul_smul]
      exact key _ _ _ (hmW w) (by rw [map_mul, hσ, hσ, smul_eq_mul])
  have g2 : ∀ x, g x ∈ W := by
    intro x
    induction x using Finsupp.induction_linear with
    | zero => simp
    | add a b ha hb => rw [map_add (f := _)]; exact W.add_mem ha hb
    | single w c => rw [hg]; exact W.smul_mem _ (hmW w)
  have g3 : ∀ x, q (g x) = v (Finsupp.linearCombination R₀ id x) := by
    intro x
    induction x using Finsupp.induction_linear with
    | zero => simp
    | add a b ha hb => rw [map_add (f := _), map_add (f := _), map_add (f := _), map_add (f := _), ha, hb]
    | single w c =>
      rw [hg, Finsupp.linearCombination_single, map_smul, hmq, ← hv, hσ]
      rfl
  obtain ⟨s, hs⟩ := hP.out
  refine ⟨g.comp s.toAddMonoidHom, ?_, ?_, ?_⟩
  · intro r w
    show g (s (π r • w)) = r • g (s w)
    rw [map_smul, g1]
  · intro w
    exact g2 _
  · intro w
    show q (g (s w)) = v w
    rw [g3, hs]

end GlobalTheory.LiftSys
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSmoothProperModelFinitelyGeneratedSubring
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.CechPic GlobalTheory.QCoh GlobalTheory.LogPair
open scoped TensorProduct

namespace GlobalTheory.SmoothProperModel

theorem exists_smooth_proper_model : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) (f : X ⟶ Sp k), Smooth f → IsProper f →
    ∃ (R : Subring k) (X₀ : Scheme.{0}) (f₀ : X₀ ⟶ Sp R) (π : X ⟶ X₀), Algebra.FiniteType ℤ R ∧ Smooth f₀ ∧
      IsProper f₀ ∧ IsPullback π f f₀ (spMap R.subtype) := by
  intro k _ X f hsm hpr
  obtain ⟨R₀, _, φ, X₀, f₀, π, hm⟩ := _root_.GlobalTheory.CompanionTheory.NoethApprox.schemeModels k X f inferInstance inferInstance inferInstance
  obtain ⟨R₁, _, ψ₁, φ₁, e₁, ft₁, sm₁⟩ := GlobalTheory.T.smooth_spreads_out k R₀ φ X X₀ f f₀ π hm hsm
  have m₁ := GlobalTheory.CompanionTheory.CubeModels.model_refine' e₁ ft₁ hm
  obtain ⟨R₂, _, ψ₂, φ₂, e₂, ft₂, pr₂⟩ := _root_.GlobalTheory.CompanionTheory.SpreadingModels.properSpreads k R₁ φ₁ X _ f _ _ m₁ hpr
  have m₂ := GlobalTheory.CompanionTheory.CubeModels.model_refine' e₂ ft₂ m₁
  have sm₁' : Smooth (pullback.snd f₀ (Spec.map (CommRingCat.ofHom ψ₁))) := sm₁
  have pr₂' : IsProper (pullback.snd (pullback.snd f₀ (Spec.map (CommRingCat.ofHom ψ₁)))
      (Spec.map (CommRingCat.ofHom ψ₂))) := pr₂
  have sm₂' : Smooth (pullback.snd (pullback.snd f₀ (Spec.map (CommRingCat.ofHom ψ₁)))
      (Spec.map (CommRingCat.ofHom ψ₂))) := inferInstance
  let ψ₃ : R₂ →+* φ₂.range := φ₂.rangeRestrict
  have e₃ : φ₂.range.subtype.comp ψ₃ = φ₂ := by ext x; rfl
  have ft₃ : Algebra.FiniteType ℤ φ₂.range :=
    haveI := ft₂
    Algebra.FiniteType.of_surjective ψ₃.toIntAlgHom φ₂.rangeRestrict_surjective
  have m₃ := GlobalTheory.CompanionTheory.CubeModels.model_refine' e₃ ft₃ m₂
  exact ⟨φ₂.range, _, _, _, ft₃, inferInstance, inferInstance, m₃.2.2.2.2⟩

end GlobalTheory.SmoothProperModel
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSpreadMorphismBasicOpenAgreeFlat
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef
open scoped CategoryTheory.Obj
open GlobalTheory.Desc

namespace GlobalTheory.Desc

theorem exists_spread_basicOpen_agree : ∀ (R : Type) [CommRing R] [IsDomain R] (x : Sp R) (B Z B₀ : Scheme.{0})
    (pB : B ⟶ Sp R) (pZ : Z ⟶ Sp R), Flat pB → QuasiCompact pB → QuasiSeparated pB → IsSeparated pZ →
    LocallyOfFinitePresentation pZ → ∀ (φ₀ : B₀ ⟶ B) (u₀ : B₀ ⟶ Z), Flat φ₀ → u₀ ≫ pZ = φ₀ ≫ pB →
    ∀ u : Limits.pullback pB ((Sp R).fromSpecStalk x) ⟶ Z, u ≫ pZ = Limits.pullback.fst _ _ ≫ pB →
    (∀ (T : Scheme.{0}) (t₀ : T ⟶ B₀) (t : T ⟶ Limits.pullback pB ((Sp R).fromSpecStalk x)),
      t₀ ≫ φ₀ = t ≫ Limits.pullback.fst _ _ → t₀ ≫ u₀ = t ≫ u) →
    ∃ g : R, g ∉ x.asIdeal ∧ ∀ (Y : Scheme.{0}) (a : Y ⟶ B), (∀ y : Y, g ∉ (pB (a y)).asIdeal) →
      ∃ u' : Y ⟶ Z, u' ≫ pZ = a ≫ pB ∧ ∀ (T : Scheme.{0}) (t₀ : T ⟶ B₀) (t : T ⟶ Y),
        t₀ ≫ φ₀ = t ≫ a → t₀ ≫ u₀ = t ≫ u' := by
  intro R _ _ x B Z B₀ pB pZ hfl hqc hqs hsep hlfp φ₀ u₀ hφfl hu₀ u hu hagree
  haveI := hfl; haveI := hqc; haveI := hqs; haveI := hsep; haveI := hlfp; haveI := hφfl
  obtain ⟨V, hxV, -, w, g₀, hw, hwg, hg₀⟩ :=
    GlobalTheory.StalkLimit.exists_spread (IsPullback.of_hasPullback pB ((Sp R).fromSpecStalk x)) pZ u hu
  obtain ⟨_, ⟨g, rfl⟩, hxg, hgV⟩ :=
    (PrimeSpectrum.isTopologicalBasis_basic_opens (R := R)).exists_subset_of_mem_open (a := x) hxV V.isOpen

  have key : pullback.fst φ₀ (pullback.fst pB V.ι) ≫ u₀ = pullback.snd φ₀ (pullback.fst pB V.ι) ≫ g₀ := by
    let qN : pullback φ₀ (pullback.fst pB V.ι) ⟶ Sp R := pullback.fst _ _ ≫ φ₀ ≫ pB
    haveI : Flat qN := inferInstance
    haveI : IsDominant ((Sp R).fromSpecStalk x) := by
      refine ⟨Dense.mono (s₁ := {genericPoint (Sp R)}) ?_ ?_⟩
      · rw [Set.singleton_subset_iff, Scheme.range_fromSpecStalk]
        exact genericPoint_specializes x
      · rw [dense_iff_closure_eq]
        exact (genericPoint_spec (Sp R)).trans (by simp)
    haveI : IsSchemeTheoreticallyDominant ((Sp R).fromSpecStalk x) := .of_isDominant _
    have hPB := IsPullback.of_hasPullback qN ((Sp R).fromSpecStalk x)
    haveI : IsSchemeTheoreticallyDominant (pullback.fst qN ((Sp R).fromSpecStalk x)) :=
      .of_isPullback hPB.flip
    refine ext_of_schDom pZ ?_ (pullback.fst qN ((Sp R).fromSpecStalk x)) ?_
    · simp only [Category.assoc, hu₀, hg₀]
      rw [pullback.condition_assoc]
    · let m : pullback qN ((Sp R).fromSpecStalk x) ⟶ pullback pB ((Sp R).fromSpecStalk x) :=
        pullback.lift (pullback.fst _ _ ≫ pullback.fst _ _ ≫ φ₀) (pullback.snd _ _)
          (by rw [Category.assoc, Category.assoc]; exact pullback.condition)
      have hm : m ≫ pullback.fst pB ((Sp R).fromSpecStalk x) =
          pullback.fst qN ((Sp R).fromSpecStalk x) ≫ pullback.fst φ₀ (pullback.fst pB V.ι) ≫ φ₀ :=
        pullback.lift_fst _ _ _
      have h1 := hagree _ (pullback.fst _ _ ≫ pullback.fst _ _) m ((Category.assoc _ _ _).trans hm.symm)
      have h2 : m ≫ w = pullback.fst qN ((Sp R).fromSpecStalk x) ≫ pullback.snd φ₀ (pullback.fst pB V.ι) := by
        rw [← cancel_mono (pullback.fst pB V.ι)]
        rw [Category.assoc, hw, hm, Category.assoc, pullback.condition]
      rw [← Category.assoc, h1, ← hwg, ← Category.assoc, h2, Category.assoc]
  refine ⟨g, hxg, fun Y a ha => ?_⟩
  have hrange : Set.range (a ≫ pB) ⊆ Set.range V.ι := by
    rw [Scheme.Opens.range_ι]
    rintro _ ⟨y, rfl⟩
    exact hgV (ha y)
  let k : Y ⟶ pullback pB V.ι :=
    pullback.lift a (IsOpenImmersion.lift V.ι (a ≫ pB) hrange) (IsOpenImmersion.lift_fac _ _ _).symm
  refine ⟨k ≫ g₀, ?_, fun T t₀ t ht => ?_⟩
  · rw [Category.assoc, hg₀, pullback.lift_fst_assoc]
  · have := pullback.lift t₀ (t ≫ k) (by rw [ht, Category.assoc, pullback.lift_fst]) ≫= key
    rw [pullback.lift_fst_assoc, pullback.lift_snd_assoc, Category.assoc] at this
    exact this

end GlobalTheory.Desc
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSquareZeroAugmentedAlgebra
section
open CategoryTheory AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj
open scoped TensorProduct
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.LiftSys GlobalTheory.Obs
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section
namespace GlobalTheory.Obs.TrivAug

variable {R R₀ : Type} [CommRing R] [CommRing R₀]

theorem mul_eq_of_map_eq {I : Ideal R} (hI : I ^ 2 = 0) {π : R →+* R₀} (hk : RingHom.ker π = I)
    {a b : R} (h : π a = π b) (i : I) : a * (i : R) = b * i := by
  have h1 : a - b ∈ I := hk ▸ (RingHom.mem_ker.2 (by rw [map_sub, h, sub_self]))
  have h2 : (a - b) * (i : R) ∈ I ^ 2 := by
    rw [pow_two]; exact Ideal.mul_mem_mul h1 i.2
  rw [hI, Ideal.zero_eq_bot, Ideal.mem_bot, sub_mul, sub_eq_zero] at h2
  exact h2

def smulI (I : Ideal R) {π : R →+* R₀} (hπ : Function.Surjective π) : SMul R₀ I :=
  ⟨fun r i => ⟨Function.surjInv hπ r * i, I.mul_mem_left _ i.2⟩⟩

def modI {I : Ideal R} (hI : I ^ 2 = 0) {π : R →+* R₀} (hπ : Function.Surjective π)
    (hk : RingHom.ker π = I) : Module R₀ I :=
  @Function.Surjective.moduleLeft R R₀ I _ _ _ _ (smulI I hπ) π hπ (fun c x => by
    apply Subtype.ext
    show Function.surjInv hπ (π c) * (x : R) = c * x
    exact mul_eq_of_map_eq hI hk (Function.surjInv_eq hπ (π c)) x)

def modOpI {I : Ideal R} (hI : I ^ 2 = 0) {π : R →+* R₀} (hπ : Function.Surjective π)
    (hk : RingHom.ker π = I) : Module R₀ᵐᵒᵖ I :=
  letI := modI hI hπ hk
  Module.compHom I (RingEquiv.toOpposite R₀).symm.toRingHom

end GlobalTheory.Obs.TrivAug
end

open GlobalTheory.Obs.TrivAug in
theorem GlobalTheory.Obs.exists_aug : ∀ (R R₀ : Type) [CommRing R] [CommRing R₀] (I : Ideal R) (hI : I ^ 2 = 0) (π : R →+* R₀) (hπ : Function.Surjective π) (hk : RingHom.ker π = I), ∃ (R₁ : Type) (_ : CommRing R₁) (_ : Algebra R₀ R₁), Nonempty (Aug I π R₁) := by
  intro R R₀ _ _ I hI π hπ hk
  letI : Module R₀ I := modI hI hπ hk
  letI : Module R₀ᵐᵒᵖ I := modOpI hI hπ hk
  haveI : IsCentralScalar R₀ I := ⟨fun r m => by
    apply Subtype.ext
    show Function.surjInv hπ (MulOpposite.unop (MulOpposite.op r)) * (m : R) = Function.surjInv hπ r * m
    rfl⟩
  haveI : IsScalarTower R₀ R₀ᵐᵒᵖ I := ⟨fun r s m => by
    apply Subtype.ext
    show Function.surjInv hπ (MulOpposite.unop (r • s)) * (m : R) = Function.surjInv hπ r * (Function.surjInv hπ (MulOpposite.unop s) * m)
    rw [← _root_.mul_assoc]
    refine mul_eq_of_map_eq hI hk ?_ m
    simp [Function.surjInv_eq hπ, smul_eq_mul, mul_comm]⟩
  refine ⟨TrivSqZeroExt R₀ I, inferInstance, inferInstance, ⟨?_⟩⟩
  exact
  { q := TrivSqZeroExt.fstHom R₀ R₀ I
    k := { toFun := fun y => (y.snd : R), map_zero' := rfl, map_add' := fun _ _ => rfl }
    mem := fun y => y.snd.2
    smul := fun r y => by
      show Function.surjInv hπ (π r) * (y.snd : R) = r * y.snd
      exact mul_eq_of_map_eq hI hk (Function.surjInv_eq hπ (π r)) _
    one := rfl
    sq := fun y y' h h' => by
      have h0 : y.fst = 0 := h
      have h0' : y'.fst = 0 := h'
      ext
      · simp [h0]
      · simp [h0, h0']
    inj := fun y h h' => by
      have h0 : y.fst = 0 := h
      ext
      · exact h0
      · have h1 : (y.snd : R) = 0 := h'
        rw [h1]; rfl
    surj := fun i hi => ⟨TrivSqZeroExt.inr ⟨i, hi⟩, rfl, rfl⟩ }
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSubOneMemMulKerNakayamaFlat
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.Pinch

theorem mem_map_mul_ker_of_flat {R' A C' : Type} [CommRing R'] [CommRing A] [CommRing C']
    [Algebra R' A] [Algebra R' C'] [Module.Flat R' C'] (f : A →ₐ[R'] C')
    (hf : Function.Surjective f) (J : Ideal R') {x : A}
    (hx : x ∈ J.map (algebraMap R' A)) (hfx : f x = 0) :
    x ∈ J.map (algebraMap R' A) * RingHom.ker f := by
  rw [Ideal.map, Ideal.span, Submodule.mem_span_set'] at hx
  obtain ⟨n, c, g, rfl⟩ := hx
  have hg : ∀ i, ∃ j ∈ J, algebraMap R' A j = (g i : A) := fun i => (g i).2
  choose j hjJ hjg using hg
  have hsum : ∑ i, j i • f (c i) = 0 := by
    set_option synthInstance.maxHeartbeats 100000 in
      rw [← hfx, map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [smul_eq_mul, ← hjg i, map_mul, AlgHom.commutes, Algebra.smul_def, _root_.mul_comm]
  obtain ⟨k, a, y, hy, ha⟩ := Module.Flat.isTrivialRelation_of_sum_smul_eq_zero (R := R') (M := C') (f := j)
    (x := fun i => f (c i)) hsum
  choose z hz using fun l => hf (y l)
  have hd : ∀ i, c i - ∑ l, a i l • z l ∈ RingHom.ker f := by
    intro i
    rw [RingHom.mem_ker]
    change f (c i - ∑ l, a i l • z l) = 0
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sub, map_sum]
    simp only [map_smul, hz]
    rw [← hy i, sub_self]
  have h0 : ∑ i, algebraMap R' A (j i) * ∑ l, a i l • z l = 0 := by
    have hl : ∀ l, ∑ i, algebraMap R' A (j i) * (a i l • z l) = 0 := by
      intro l
      have : ∑ i, algebraMap R' A (j i) * (a i l • z l) = (∑ i, j i * a i l) • z l := by
        rw [Finset.sum_smul]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [Algebra.smul_def, Algebra.smul_def, map_mul, _root_.mul_assoc]
      rw [this, ha l, zero_smul]
    simp_rw [Finset.mul_sum]
    rw [Finset.sum_comm]
    exact Finset.sum_eq_zero fun l _ => hl l
  have key : ∑ i, c i • (g i : A) =
      ∑ i, algebraMap R' A (j i) * (c i - ∑ l, a i l • z l) := by
    simp only [mul_sub, Finset.sum_sub_distrib, h0, sub_zero]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [smul_eq_mul, ← hjg i, _root_.mul_comm]
  rw [key]
  exact Ideal.sum_mem _ fun i _ => Ideal.mul_mem_mul (Ideal.mem_map_of_mem _ (hjJ i)) (hd i)

theorem exists_sub_one_mem_mul_ker_le :
    ∀ (R' A C' : Type) [CommRing R'] [CommRing A] [CommRing C'] [Algebra R' A] [Algebra R' C']
      [IsNoetherianRing A] [Module.Flat R' C'] (f : A →ₐ[R'] C'), Function.Surjective f →
      ∀ (I : Ideal A) (J : Ideal R'), I ≤ RingHom.ker f →
        RingHom.ker f ≤ I ⊔ J.map (algebraMap R' A) →
          ∃ s : A, s - 1 ∈ J.map (algebraMap R' A) ∧ ∀ G ∈ RingHom.ker f, s * G ∈ I := by
  intro R' A C' _ _ _ _ _ _ _ f hf I J hI hK
  have hle : RingHom.ker f ≤ I ⊔ (J.map (algebraMap R' A)) • RingHom.ker f := by
    intro G hG
    obtain ⟨i, hi, x, hx, rfl⟩ := Submodule.mem_sup.1 (hK hG)
    have hfx : f x = 0 := by
      have h1 : f (i + x) = 0 := hG
      have h2 : f i = 0 := hI hi
      rw [map_add (f := _), h2, zero_add] at h1
      exact h1
    exact Submodule.add_mem_sup hi (mem_map_mul_ker_of_flat f hf J hx hfx)
  obtain ⟨r, hr1, hr⟩ := Submodule.exists_sub_one_mem_and_smul_le_of_fg_of_le_sup
    (IsNoetherian.noetherian (RingHom.ker f)) le_rfl hle
  refine ⟨r, hr1, fun G hG => ?_⟩
  exact hr (Submodule.smul_mem_pointwise_smul G r _ hG)

end GlobalTheory.Pinch
end

