module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsProjOverWeierstrass
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
public import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissibleBaseOfCompleteDvr
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0063
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0059
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2190
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0284
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0034
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0035
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0003
public import Development.AbelianVarietyTheory.Definitions.ShimuraVarieties.FlatImageOfOverFractionFieldOfValuationRing
public import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.IsProjOverCompOfIsClosedImmersion
public import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.Bundle0005
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NontrivialIsomClassInt
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0098
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2201
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1979
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1883
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0038
public import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.PermutesRefl
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2185
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1227
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1234
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1263
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2222
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2186
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0036
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.UnitLemmaGroup
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUnramifiedQuadraticDatumAtInertPlace
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0026
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0008
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0001
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.StrongMultiplicityOne
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.IsTemperedGLOfIsUnitaryLSeg
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0010
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.ExistsCellOfIsSubquotient
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.RadfordShufflePolynomialHolds
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.Bundle0004
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsUniqueHcharOfFiniteOrder
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0006
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0009
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.T2SpaceAdelicGeneralLinearGroupNumberField
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HeckeLEntireAndNonzeroAtOne
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.QuadraticClassFieldTheory
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.ExistsOrthonormalOfUnimodular
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2122
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsDatNeZero
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0064
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0362
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0006
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.AbelianHodgeDeRham
public import Development.AbelianVarietyTheory.Definitions.Divisors.GalRigidOfSurjective
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0061
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsProperToroidalModelStructureMap
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0721
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.SABBaseChangeSt

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ISupNonzeroLocusEmbH
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

noncomputable section

namespace GlobalTheory.Mum.SecEmb

def TraitRed {R : Type} [CommRing R] [IsDomain R] [IsLocalRing R] (M : Modif R) (G : Over M.S) [GrpObj G]
    {B L : LB G.left} {N : ℕ} (s : Fin (N + 1) → B.Sec) (θ : L.Sec) (Y : Over (Sp (ResidueField R))) [GrpObj Y]
    (j : Y.left ⟶ PSpace R N) (O : Y.left.Opens) : Prop :=
  ∀ (W : Type) [CommRing W] [IsDomain W] [IsLocalRing W], GlobalTheory.LN.CDvr W → ∀ (φ : R →+* W) (ξ : Sp W ⟶ M.S),
    Function.Injective φ → IsLocalHom φ → ξ ≫ M.π = spMap φ →
    ∃ (W' : Type) (_ : CommRing W') (_ : IsDomain W') (_ : IsLocalRing W') (io : W →+* W') (G' : Over (Sp W'))
      (_ : GrpObj G') (β : G'.left ⟶ G.left) (κ : ResidueField R →+* ResidueField W')
      (e : (Over.pullback (spMap (residue W'))).obj G' ≅ (Over.pullback (spMap κ)).obj Y),
      GlobalTheory.LN.CDvr W' ∧ Function.Injective io ∧ io.Finite ∧ IsGrpPullback G' G (spMap io ≫ ξ) β ∧
      κ.comp (residue R) = (residue W').comp (io.comp φ) ∧ IsMonHom e.hom ∧
      ∀ (Ω : Type) [Field Ω] (p : Sp Ω ⟶ ((Over.pullback (spMap (residue W'))).obj G').left) (p' : Sp Ω ⟶ G'.left)
        (y : Sp Ω ⟶ Y.left), p' = p ≫ pullback.fst G'.hom (spMap (residue W')) →
        y = p ≫ e.hom.left ≫ pullback.fst Y.hom (spMap κ) →
        (∃ hs, GlobalTheory.ProjSpace.toProj (p' ≫ G'.hom ≫ spMap (io.comp φ)) (fun i => GlobalTheory.secPull (s i) (p' ≫ β)) hs = y ≫ j) ∧
        ∀ x : Sp Ω, y x ∈ O → (p' ≫ β) x ∈ nonzeroLocus θ

def embH {X : Scheme.{0}} {B : LB X} {N : ℕ} (s : Fin (N + 1) → B.Sec) : X.Opens := ⨆ i, nonzeroLocus (s i)

theorem iSup_nonzeroLocus_embH {X : Scheme.{0}} {B : LB X} {N : ℕ} (s : Fin (N + 1) → B.Sec) :
    ⨆ i, nonzeroLocus (GlobalTheory.secPull (s i) (embH s).ι) = ⊤ := by
  simp only [GlobalTheory.nonzeroLocus_secPull]
  rw [← Scheme.Hom.preimage_iSup]
  exact Scheme.Opens.ι_preimage_self _

def embF {R : Type} [CommRing R] {X : Scheme.{0}} {B : LB X} {N : ℕ} (q : X ⟶ Sp R) (s : Fin (N + 1) → B.Sec) :
    (embH s).toScheme ⟶ PSpace R N :=
  GlobalTheory.ProjSpace.toProj ((embH s).ι ≫ q) (fun i => GlobalTheory.secPull (s i) (embH s).ι) (iSup_nonzeroLocus_embH s)

end GlobalTheory.Mum.SecEmb
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ImageModelSectionsLinearRingOfIntegers
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.BasicNotions.TH Formalism.L2.Theta ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.CompHt GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.Mean4 GlobalTheory.Mean4O
open scoped ENNReal Classical
open CategoryTheory AlgebraicGeometry

namespace GlobalTheory.ImageModel

theorem sec_linear : ∀ (K V Ω : Type) [Field K] [NumberField K] [AddCommGroup V] [Module K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] [Field Ω] [Algebra K Ω] (Nm : (K →+* ℂ) → V → ℝ) (W : Submodule (𝓞 K) V) (ev : V →ₗ[K] Ω) (D : ℕ) (X : AlgebraicGeometry.Scheme.{0}) [AlgebraicGeometry.IsIntegral X] (p : X ⟶ Sp (𝓞 K)) (L : GlobalTheory.HermLB p) (ψ : Ω →+* X.functionField) (s : W → L.B.Sec), GlobalTheory.ImageModel.IsModelOf Nm W ev D p L ψ s → ev ≠ 0 → ∀ (m : ℕ) (β : Fin m → 𝓞 K) (u : Fin m → W) (x : W), (x : V) = ∑ k, β k • (u k : V) → ∀ i : L.B.ι, (s x).f i = ∑ k, ReciprocityTheory.ChartRestriction.G.DVR.FlatBC.algX p (L.B.U i) (β k) * (s (u k)).f i := by
  intro K V Ω _ _ _ _ _ _ _ _ Nm W ev D X _ p L ψ s hM hev m β u x hx i
  have hw : ∃ w' : W, ev w' ≠ 0 := by
    by_contra hne
    push_neg at hne
    obtain ⟨N, n, b, g, A, c, gw, -, -, hb, -⟩ := hM.fs
    exact hev (b.ext fun j => by rw [hb j, map_sum]; simp [map_smul, hne])
  obtain ⟨w', hw'⟩ := hw
  apply GlobalTheory.Cartier.fn_ext
  intro hU
  have ha : ψ (ev w') ≠ 0 := (map_ne_zero ψ).mpr hw'
  have hr : ∀ y : W, ψ (ev w') * GlobalTheory.Cartier.fnOf _ hU ((s y).f i) =
      ψ (ev y) * GlobalTheory.Cartier.fnOf _ hU ((s w').f i) := fun y => (hM.ratio y w' i hU).symm
  have hc : ∀ b : 𝓞 K, GlobalTheory.Cartier.fnOf _ hU (ReciprocityTheory.ChartRestriction.G.DVR.FlatBC.algX p (L.B.U i) b) =
      ψ (algebraMap K Ω (b : K)) := by
    intro b
    rw [hM.base]
    exact RingHom.congr_fun (GlobalTheory.Cartier.fnOf_comp_algX p _ hU) b
  have hex : ψ (ev x) = ∑ k, ψ (algebraMap K Ω (β k : K)) * ψ (ev (u k)) := by
    set_option synthInstance.maxHeartbeats 100000 in
      rw [hx, map_sum, map_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [← IsScalarTower.algebraMap_smul K (β k) (u k : V), map_smul, Algebra.smul_def, map_mul]
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sum]
  simp only [map_mul, hc]
  apply mul_left_cancel₀ ha
  rw [hr x, hex, Finset.sum_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [mul_left_comm (ψ (ev w')), hr (u k), mul_assoc]

end GlobalTheory.ImageModel
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ImportsTailFurther
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

noncomputable section

namespace GlobalTheory.Mum

theorem LabCover.exists_pull : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] (D : DegData R (maximalIdeal R)) (C : LabCover D) (M' : Modif R) (h : M'.S ⟶ C.S), M'.gp ≫ h = C.gp → h ≫ C.π = M'.π → ∃ (C' : LabCover D) (eS : C'.S ≅ M'.S) (β : C'.G.left ⟶ C.G.left), eS.hom ≫ M'.π = C'.π ∧ IsGrpPullback C'.G C.G (eS.hom ≫ h) β ∧ LBIso C'.P.L.L (C.P.L.L.pull β) := by
  intro R _ _ _ D C M' h hgp hπ
  have hex : ∃ (P' : GlobalTheory.UU.CP ((Over.pullback h).obj C.G)) (w : _),
      GlobalTheory.UU.IsCPMap P' C.P h (pullback.fst C.G.hom h) pullback.condition w :=
    GlobalTheory.UU.exists_pull C.P (GlobalTheory.UU.toBase_mul_pullback C.G h)
  obtain ⟨P', w, hP⟩ := hex
  have hG : IsGrpPullback ((Over.pullback h).obj C.G) C.G h (pullback.fst C.G.hom h) := isGrpPullback_pullback C.G h
  have hw : LBIso P'.L.L (C.P.L.L.pull (pullback.fst C.G.hom h)) := ⟨w, hP.gen⟩

  have key : ∀ {Y : Scheme.{0}} (b : Y ⟶ ((Over.pullback h).obj C.G).left) (c : Y ⟶ C.G.left),
      c = b ≫ pullback.fst C.G.hom h → LBIso (P'.L.L.pull b) (C.P.L.L.pull c) := fun b c e =>
    LBIso.chartPull (chartPullId _) (GlobalTheory.RigidBundleGlue.chartPullComp C.P.L.L _ b c e)
      (GlobalTheory.RigidBundleGlue.LBIso.pull hw b)
  let α' : C.A.A.left ⟶ ((Over.pullback h).obj C.G).left :=
    pullback.lift C.α (C.A.A.hom ≫ M'.gp) (by rw [C.α_cart.1.w, Category.assoc, hgp])
  have hα : α' ≫ pullback.fst C.G.hom h = C.α := pullback.lift_fst _ _ _
  refine ⟨{ toModif := M'
            G := (Over.pullback h).obj C.G
            semi := IsSemiAbelian.pullback h C.G C.semi
            P := P'
            A := C.A
            α := α'
            α_cart := IsGrpPullback.cancel hG (C.α_cart.congr hgp.symm hα.symm) (pullback.lift_snd _ _ _)
            α_lb := LBIso.trans C.A.isLB (pull_isLB C.P.L.isLB _) (pull_isLB P'.L.isLB _) C.α_lb
              (LBIso.symm (key α' C.α hα.symm))
            n := C.n
            n_prime := C.n_prime
            n_odd := C.n_odd
            n_unit := C.n_unit
            lab := C.lab
            trait := ?_ }, Iso.refl _, pullback.fst C.G.hom h, Category.id_comp _,
      hG.congr (Category.id_comp _).symm rfl, hw⟩
  intro W _ _ _ hW φ ξ hφ hloc hξ
  obtain ⟨W', _, _, _, io, G'', _, _, β, D', A', U', hD, hW', hio, hfin, hcart, hlb, hlab⟩ :=
    C.trait W hW φ (ξ ≫ h) hφ hloc (by rw [Category.assoc, hπ]; exact hξ)
  let β' : G''.left ⟶ ((Over.pullback h).obj C.G).left :=
    pullback.lift β (G''.hom ≫ spMap io ≫ ξ) (by rw [hcart.1.w, Category.assoc, Category.assoc])
  have hβ : β' ≫ pullback.fst C.G.hom h = β := pullback.lift_fst _ _ _
  refine ⟨W', inferInstance, inferInstance, inferInstance, io, G'', inferInstance, inferInstance, β', D', A', U', hD, hW',
    hio, hfin, IsGrpPullback.cancel hG (hcart.congr (Category.assoc _ _ _).symm hβ.symm) (pullback.lift_snd _ _ _),
    LBIso.trans U'.LG.isLB (pull_isLB C.P.L.isLB _) (pull_isLB P'.L.isLB _) hlb (LBIso.symm (key β' β hβ.symm)), ?_⟩
  intro F _ _ _ _ em hF j p p₁ p' x' h₁ h₂ h₃ h₄
  refine hlab F em hF j p p₁ p' x' h₁ h₂ h₃ ?_
  have e := congrArg (· ≫ pullback.fst C.G.hom h) h₄
  simp only [Category.assoc, hβ, hα] at e
  simpa only [Category.assoc] using e

end GlobalTheory.Mum
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.InducesPl
section
set_option autoImplicit false

noncomputable section

open CategoryTheory Limits AlgebraicGeometry NumberField IsDedekindDomain
open scoped NNReal
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Pdiv ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD
open Formalism.L2.Pj GlobalTheory.HTLat GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.CompHt GlobalTheory.FlatCore GlobalTheory.FlatModel GlobalTheory.Toroidal
open GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.TrueGeo GlobalTheory.Mean4O GlobalTheory.CoverNorm GlobalTheory.VertForm
attribute [local instance] Over.cartesianMonoidalCategory
attribute [local instance] algPadicInt algPadicField towerPadic factPadic GlobalTheory.PadicComplexHost.isAdicComplete

namespace GlobalTheory.DetHT

section Defs

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}

variable {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F}

variable {p : ℕ} [Fact p.Prime]

end Defs

def RegLocSt : Prop :=
  ∀ (F : Type) [Field F] [NumberField F] (Y : Var F) (V : GlobalTheory.Mean4O.Cover Y) (U W : V.X.Opens), (W : Set V.X).Nonempty →
    ∀ (v : HeightOneSpectrum (𝓞 F)) (g : V.X.functionField),
    (∀ (e : TrueGeo.Ext v) (z : Sp (AlgebraicClosure F) ⟶ V.G) (yt : Sp e.O ⟶ V.X),
      z ≫ V.π ≫ Y.str = spMap (algebraMap F (AlgebraicClosure F)) → spMap e.O.subtype ≫ yt = z ≫ V.j → ⊤ ≤ yt ⁻¹ᵁ U →
      below (z ≫ V.j) ∈ W → e.w (TrueGeo.valAt (z ≫ V.j) g) ≤ 1) →
    ∀ x ∈ U, (V.p x).asIdeal = v.asIdeal → RegAt x g

end GlobalTheory.DetHT

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.InertPlaceBigCellStabiliserOfLocalRingBigCellLemStatement
section
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped TensorProduct Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.inertPlace_bigCell_stabiliser_of_localRingBigCell_lemma : (∀ {O : Type} [CommRing O] [IsLocalRing O] (c : O →+* O), (∀ x, c (c x) = x) → IsUnit (2 : O) →
    ∀ {n : ℕ} (S : Matrix (Fin n) (Fin n) O), IsUnit S.det → Sᵀ = -S.map c →
    ∀ (A B C D : Matrix (Fin n) (Fin n) O), IsUnit (Matrix.fromBlocks A B C D).det →
      (Matrix.fromBlocks A B C D)ᵀ * Matrix.fromBlocks 0 S S 0 * (Matrix.fromBlocks A B C D).map c =
        Matrix.fromBlocks 0 S S 0 →
      ∃ X : Matrix (Fin n) (Fin n) O, Xᵀ * S + S * X.map c = 0 ∧ IsUnit (A + X * C).det) →
  ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    {d : ℕ} (W : Spc F E d) (r s : ℕ), B.IsGood σ → W.IsSkew σ B r s →
    ∀ (v : Pl (F := F)) (w : HeightOneSpectrum (𝓞 E)), Formalism.UG.IsInertAt F E v w → ∀ g ∈ GlobalTheory.DblVac.KD σ W v,
      ∃ p ∈ GlobalTheory.DblVac.KD σ W v, p ∈ GlobalTheory.DblVac.PDiag σ W ∧ p * g ∈ GlobalTheory.DblVac.KD σ W v ∧ GlobalTheory.DblVac.BigCell W v (p * g) := by
  first | exact @GlobalTheory.InertBigCell.exists_bigCell | exact GlobalTheory.InertBigCell.exists_bigCell | (intros; apply GlobalTheory.InertBigCell.exists_bigCell <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.InertPlaceLatticeStabilizerVacuumScalarEqOne
section
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped TensorProduct Matrix

namespace GlobalTheory.InertScalarLeft

theorem scalar_eq_one : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    (a a' : ℕ) (G : Geo σ a a') (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W), IsTriple B G X om om' →
    ∀ (v : Pl (F := F)) (w : HeightOneSpectrum (𝓞 E)), Formalism.UG.IsInertAt F E v w → v ∉ X.T →
    ∀ k ∈ GlobalTheory.InertSph.KAt σ G.V' v, ∀ c : ℂ, Acts (evFin F v) (om' (k, 1)) (G.M'.vac v) (c • G.M'.vac v) → c = 1 := by
  intro F E _ _ _ _ _ σ B a a' G X om om' hTr v w hin hT k hk c hc
  by_contra hne
  have hSB := (hTr.geo.hM'.vac v).1
  apply GlobalTheory.T.weil_vacuum_not_mem_augmentation_inert_place F E σ B a a' G X om om' hTr v w hin hT
  have hmem : c • G.M'.vac v - G.M'.vac v ∈ augAt om' v :=
    Submodule.subset_span ⟨k, hk.1, _, hSB, _, Submodule.smul_mem _ c hSB, hc, rfl⟩
  have h1 : c - 1 ≠ 0 := sub_ne_zero.mpr hne
  have h2 : G.M'.vac v = (c - 1)⁻¹ • (c • G.M'.vac v - G.M'.vac v) := by
    rw [show c • G.M'.vac v - G.M'.vac v = (c - 1) • G.M'.vac v by rw [sub_smul, one_smul],
      smul_smul, inv_mul_cancel₀ h1, one_smul]
  rw [h2]
  exact Submodule.smul_mem _ _ hmem

end GlobalTheory.InertScalarLeft
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.InertPlaceStableTwistedOrbitalUnitEqLatticeSumStatement
section
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.inertPlace_stableTwistedOrbital_unit_eq_latticeSum : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E], Unr E → ∀ (w : Pl E), ¬ IsSplitAt w → ∀ (K : GlobalTheory.UnitLemma.UQ) (e : K.E ≃+* w.adicCompletion E), (∀ x, e (K.c x) = cj w (e x)) → (∀ x, x ∈ (algebraMap K.O K.E).range ↔ Valued.v (e x) ≤ 1) → (∀ x, GlobalTheory.UnitLemma.val K.O x = ordL (e x)) → qV E w = K.q ^ 2 → ∀ (a : ℕ) (Q : (w.adicCompletion E)[X]), Q.Monic → Q.natDegree = a → Q.Separable → IsCsr w Q → ∃ B : GlobalTheory.UnitLemma.InvAlg K, B.g * B.σ B.g = 1 ∧ B.P = Q.map e.symm.toRingHom ∧ stTw a w Q ((GlobalTheory.LFun.KGL w (n := a) : Set (GLw a w)).indicator 1) = (B.stSum : ℂ) := by
  first | exact @GlobalTheory.InertTwUnit.twisted_unit_eq_stSum | exact GlobalTheory.InertTwUnit.twisted_unit_eq_stSum | (intros; apply GlobalTheory.InertTwUnit.twisted_unit_eq_stSum <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.InjectiveOfDualMapSurjectiveOfProjective
section
open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct WithConv
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Sp spMap epsR IsTangent IsGrpPullback)
open ReciprocityTheory.ChartRestriction.G.Semi (IsAbelianScheme LB RigLB CubicalStr Theta thφ thε thK x3)
open GlobalTheory GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.PDiv GlobalTheory.PtExt
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory

theorem injective_of_dualMap_surjective_of_projective :
    ∀ (R : Type) [CommRing R] (M : Type 1) [AddCommGroup M] [Module R M] [Module.Projective R M]
      (N : Type) [AddCommGroup N] [Module R N] (f : M →ₗ[R] N),
      Function.Surjective f.dualMap → Function.Injective f := by
  intro R _ M _ _ _ N _ _ f hf
  rw [← LinearMap.ker_eq_bot, Submodule.eq_bot_iff]
  intro m hm
  rw [LinearMap.mem_ker] at hm
  refine (Module.forall_dual_apply_eq_zero_iff R m).mp fun φ => ?_
  obtain ⟨ψ, rfl⟩ := hf φ
  simp [LinearMap.dualMap_apply, hm]

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.InjectiveOfFiniteOfRingKrullDimLe
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.SiegJoin GlobalTheory.Poinc GlobalTheory.TChart
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.FiniteMapInj

theorem injective_of_finite_of_ringKrullDim_le (A R : Type) [CommRing A] [IsDomain A]
    [IsLocalRing A] [IsNoetherianRing A] [CommRing R] [IsLocalRing R] (b : A →+* R) :
    b.Finite → ringKrullDim A ≤ ringKrullDim R → Function.Injective b := by
  intro hfin hdim
  set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
  intro x hx
  by_contra hx0
  set I := RingHom.ker b
  have hxI : x ∈ I := hx

  have hcomp : b.kerLift.comp (Ideal.Quotient.mk I) = b := by
    ext a; rfl
  have hfin' : b.kerLift.Finite := by
    rw [← hcomp] at hfin
    exact RingHom.Finite.of_comp_finite hfin
  letI : Algebra (A ⧸ I) R := b.kerLift.toAlgebra
  haveI : Algebra.IsIntegral (A ⧸ I) R := ⟨hfin'.to_isIntegral⟩
  have h1 : ringKrullDim R ≤ ringKrullDim (A ⧸ I) :=
    Order.krullDim_le_of_strictMono (PrimeSpectrum.comap (algebraMap (A ⧸ I) R))
      fun P Q h => Ideal.IsIntegral.comap_lt_comap (I := P.asIdeal) (J := Q.asIdeal) h
  have h2 : ringKrullDim (A ⧸ I) + 1 ≤ ringKrullDim A :=
    ringKrullDim_succ_le_of_surjective (Ideal.Quotient.mk I) Ideal.Quotient.mk_surjective
      (mem_nonZeroDivisors_of_ne_zero hx0) (Ideal.Quotient.eq_zero_iff_mem.mpr hxI)
  have h3 : ringKrullDim R + 1 ≤ ringKrullDim R :=
    ((by gcongr : ringKrullDim R + 1 ≤ ringKrullDim (A ⧸ I) + 1).trans h2).trans hdim
  have htop : ringKrullDim R + 1 < ⊤ :=
    ((by gcongr : ringKrullDim R + 1 ≤ ringKrullDim (A ⧸ I) + 1).trans h2).trans_lt
      ringKrullDim_lt_top
  have hbot : ringKrullDim R ≠ ⊥ := fun h => by
    have := ringKrullDim_nonneg_of_nontrivial (R := R)
    rw [h] at this
    exact absurd this (by simp)
  generalize ringKrullDim R = d at h3 htop hbot
  induction d with
  | bot => exact hbot rfl
  | coe e =>
    induction e with
    | top =>
      exact absurd htop (by rw [← WithBot.coe_one, ← WithBot.coe_add, top_add]; exact lt_irrefl _)
    | coe n =>
      have : ((n + 1 : ℕ) : WithBot ℕ∞) ≤ (n : ℕ) := by exact_mod_cast h3
      norm_cast at this
      omega

end GlobalTheory.FiniteMapInj
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsAbelianSchemeGeneric
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory.Mum.RetractGeneric

theorem isProper_of_retract {S : Scheme.{0}} {X Y : Over S} (i : X ⟶ Y) (r : Y ⟶ X)
    (h : i ≫ r = 𝟙 X) (hY : IsProper Y.hom) : IsProper X.hom := by
  have hl : i.left ≫ r.left = 𝟙 _ := by rw [← Over.comp_left, h, Over.id_left]
  have h1 : IsSeparated (r.left ≫ X.hom) := by rw [Over.w r]; infer_instance
  have h2 : IsSeparated r.left := IsSeparated.of_comp r.left X.hom
  have h3 : IsClosedImmersion (i.left ≫ r.left) := by rw [hl]; infer_instance
  have h4 : IsClosedImmersion i.left := IsClosedImmersion.of_comp i.left r.left
  rw [← Over.w i]
  infer_instance

theorem isAbelianScheme_generic : ∀ (R : Type) [CommRing R] [IsDomain R] (A' : PolAV (Sp (FractionRing R))) (G' : Over (Sp R)) [GrpObj G'] [IsCommMonObj G'], IsSemiAbelian G' → ((Over.pullback (jK R)).obj G' ≅ A'.A) → ∀ (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ (inc : G ⟶ G') (pr : G' ⟶ G), IsMonHom inc → IsMonHom pr → inc ≫ pr = 𝟙 G → IsAbelianScheme ((Over.pullback (jK R)).obj G) := by
  intro R _ _ A' G' _ _ _ e G _ _ hG inc pr _ _ h
  have hK := IsSemiAbelian.pullback (jK R) G hG
  have hp : IsProper ((Over.pullback (jK R)).obj G).hom :=
    isProper_of_retract ((Over.pullback (jK R)).map inc ≫ e.hom)
      (e.inv ≫ (Over.pullback (jK R)).map pr)
      (by rw [Category.assoc, e.hom_inv_id_assoc, ← CategoryTheory.Functor.map_comp, h,
        CategoryTheory.Functor.map_id]) A'.isAb.proper
  exact ⟨hK.comm, hK.smooth, hp, hK.geomConnected⟩

end GlobalTheory.Mum.RetractGeneric
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsAdicCompleteSpanNatCastOfIsNilpotent
section
open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct WithConv
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Sp spMap epsR IsTangent IsGrpPullback)
open ReciprocityTheory.ChartRestriction.G.Semi (IsAbelianScheme LB RigLB CubicalStr Theta thφ thε thK x3)
open GlobalTheory GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.PDiv GlobalTheory.PtExt
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory

theorem span_natCast_pow_eq_bot_of_isNilpotent (p : ℕ) (R : Type) [CommRing R]
    (h : IsNilpotent (p : R)) : ∃ N : ℕ, Ideal.span {(p : R)} ^ N • (⊤ : Submodule R R) = ⊥ := by
  obtain ⟨N, hN⟩ := h
  refine ⟨N, ?_⟩
  rw [Ideal.span_singleton_pow, hN, smul_eq_mul, Ideal.mul_top]
  simp

theorem isAdicComplete_span_natCast_of_isNilpotent :
    ∀ (p : ℕ) (R : Type) [CommRing R], IsNilpotent (p : R) →
      IsAdicComplete (Ideal.span {(p : R)}) R := by
  intro p R _ h
  obtain ⟨N, hN⟩ := span_natCast_pow_eq_bot_of_isNilpotent p R h
  refine { haus' := ?_, prec' := ?_ }
  · intro x hx
    have := hx N
    rwa [hN, SModEq.bot] at this
  · intro f hf
    refine ⟨f N, fun n => ?_⟩
    rcases le_total n N with hn | hn
    · exact hf hn
    · have h1 := hf hn
      rw [hN, SModEq.bot] at h1
      rw [h1]
end GlobalTheory
end

