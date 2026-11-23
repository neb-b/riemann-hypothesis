module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Degenerations.BaseFacts
public import Development.AbelianVarietyTheory.Definitions.Degenerations.IsAffineSplitTorusLeft
public import Development.AbelianVarietyTheory.Definitions.Degenerations.CompanionTheory
public import Development.AbelianVarietyTheory.Statements.SemistableTorsion.UTorsSt
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0097
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ValRConstHom
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
public import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing
public import Development.AbelianVarietyTheory.Definitions.Degenerations.OfDerivationFnOn
public import Development.AbelianVarietyTheory.Definitions.Degenerations.PlOrdSomeOfAssociated
public import Development.AbelianVarietyTheory.Statements.SemistableTorsion.SemistableFin
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0092
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0004
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.GeometricallyIntegralIffGeometricallyConnectedOf
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0078
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0095
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsUniqueModelHasJacobianOrder
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.JacobianOrderMonotoneSemistableModel
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.AbelianVarietyAutomorphismShiftsJacobianOrder
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0025
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.VectorFieldOrderAddOfProdStrictHenselian
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0041
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ModelMapGenericallyOpenImmersionCalculus
public import Lean.Elab.Command
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsCoordReducedFibreClosedPoint
public import Development.AbelianVarietyTheory.Definitions.Degenerations.IsNormalSchemeSp
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0090
public import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0093
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0064
public import Development.AbelianVarietyTheory.Proofs.ThetaFamilyOrigin.IsThetaPtOverMove
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsTorusActionWeightedCharts

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.BasisSeparates
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open ReciprocityTheory.ChartRestriction.G.Out GlobalTheory.ZH Classical
attribute [local instance] SplitExt.free SplitExt.finite MvPolynomial.gradedAlgebra

namespace GlobalTheory.ZH.AdaptedSep

theorem basis_separates : GlobalTheory.UT.LL → ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] [ArithBase o Ω] (S : ThetaSys o Ω) (ρ : S.Real) (p : ℕ) [Fact p.Prime] (y₀ : S.R →+* PadicAlgCl p) (u : ρ.UTest p y₀) (l : u.Lab) (k : ℕ), 4 ≤ k → ∀ (J : Type) [Fintype J] (σ : J → (u.H k).Sec) (cls : J → u.D.toPre.X) (f : J → ∀ α, u.D.toPre.SecB k α), u.Basis l k σ cls f → (∀ (a : u.PtC) w, Crd (u.H k) σ (u.toG a) w → w ≠ 0) ∧ (∀ (a a' : u.PtC) w, Crd (u.H k) σ (u.toG a) w → Crd (u.H k) σ (u.toG a') w → a = a') ∧ ∀ a : Sp (PadicAlgCl p) ⟶ u.G.left, a ≫ u.G.hom = gPt p ≫ spMap u.j → ∃ a' : u.PtC, u.toG a' = a := by
  intro hL o Ω _ _ _ _ S ρ p _ y₀ u l k hk J _ σ cls f ⟨_, h₂, h₃, h₄, h₅, h₆, h₇⟩
  obtain ⟨m, t, ht⟩ := CrdMove.immBy_lbPow hL.1.ample _ u.A k hk
  obtain ⟨s, hs⟩ := CrdMove.exists_transport u.A.isLB u.U.LG.isLB u.U.gen.hom.left u.U.gen.inv.left
    (congrArg (fun q => q.left) u.U.gen.inv_hom_id) (congrArg (fun q => q.left) u.U.gen.hom_inv_id) _ u.U.ext k t
  choose b hb using fun i => AdaptedSpan.exists_comb hL.1.globalFns u.U (by omega : 1 ≤ k) σ cls f h₂ h₃ h₄ h₅ h₆ h₇ (s i)
  have key : ∀ (a : u.PtC) w, Crd (u.H k) σ (u.toG a) w → Crd (lbPow u.A.L k) t (a.left ≫ u.U.gen.hom.left)
      (fun i => ∑ j, algebraMap (FractionRing u.V) (PadicAlgCl p) (b i j) * w j) := fun a w h =>
    hs _ a.left _ (CrdMove.crd_comb (pullback.condition : pullback.fst u.G.hom (jK u.V) ≫ u.G.hom = _)
      (fun _ => (Category.comp_id _).symm) σ s b hb a.left _ (Over.w a) h)
  refine ⟨fun a w h hw => ?_, fun a a' w h h' => ?_, fun a ha => ?_⟩
  · have hm : (a.left ≫ u.U.gen.hom.left : Sp (PadicAlgCl p) ⟶ u.A.A.left) (IsLocalRing.closedPoint _) ∈
        ⨆ i ∈ Set.univ, nonzeroLocus (t i) := by rw [ht.1]; trivial
    obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.1 hm
    obtain ⟨_, hi⟩ := TopologicalSpace.Opens.mem_iSup.1 hi
    have hu := (CrdCalc.crd_isUnit_iff i (key a w h)).2 ((CrdCalc.top_le_iff _ _).2 hi)
    simp [hw] at hu
  · have e := ImmSep.eq_of_crd_eq _ _ _ _ _ t _ (DVR.linComb_isLB _ u.A.isLB _ _) ht _ _ _ _
      ((Over.w (a ≫ u.U.gen.hom)).trans (Over.w (a' ≫ u.U.gen.hom)).symm) (key a w h) (key a' w h')
    exact (cancel_mono u.U.gen.hom).1 (Over.OverMorphism.ext e)
  · have e : gPt p ≫ spMap u.j = jFK (R := u.V) (PadicAlgCl p) ≫ jK u.V :=
      (Spec.map_comp _ _).symm.trans (Eq.trans rfl (Spec.map_comp
        (CommRingCat.ofHom (algebraMap u.V (FractionRing u.V)))
        (CommRingCat.ofHom (algebraMap (FractionRing u.V) (PadicAlgCl p)))))
    exact ⟨Over.homMk (pullback.lift a (jFK (R := u.V) (PadicAlgCl p)) (ha.trans e)) (pullback.lift_snd _ _ _),
      pullback.lift_fst _ _ _⟩

end GlobalTheory.ZH.AdaptedSep
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsAmpleCubicalOfGroupSchemeIso
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.SS

noncomputable section
namespace GlobalTheory.SS.AmpIso
open GlobalTheory.SS.AmpSub

theorem ampleCub_pull {S : Scheme.{0}} {N G : Over S} [GrpObj N] [GrpObj G] (ν : N ⟶ G) [IsMonHom ν]
    [IsAffineHom ν.left] {L : LB G.left} (h : AmpleCub G L) : AmpleCub N (L.pull ν.left) := by
  obtain ⟨hL, ⟨c, hc⟩, ⟨s, hs⟩, n, hn, ha⟩ := h
  refine ⟨pull_isLB hL _, ?_, ?_, n, hn, fun x => ?_⟩
  · refine gen_chartPull (chartPullLinComb L ν.left _ _ _ (ν ⊗ₘ ν ⊗ₘ ν).left fun I => ?_) c hc
    refine congrArg (fun z => z.left) (psum_comp ν (x3 N) (x3 G) (ν ⊗ₘ ν ⊗ₘ ν) (fun k => ?_) I.down)
    fin_cases k <;> simp [x3]
  · refine gen_chartPull (chartPullLinComb L ν.left _ _ _ ν.left fun k => ?_) s hs
    fin_cases k
    · exact congrArg (fun z => z.left) (GrpObj.inv_hom ν)
    · exact (Category.id_comp _).trans (Category.comp_id _).symm
  · obtain ⟨σ, hx, hσ⟩ := ha (ν.left x)
    have e : Out.nonzeroLocus (chartSec (chartPullPw L ν.left n) σ) = ν.left ⁻¹ᵁ Out.nonzeroLocus σ :=
      nonzeroLocus_chartSec _ σ fun y j hj => ⟨fun _ => j, mem_pull.2 hj⟩
    refine ⟨chartSec (chartPullPw L ν.left n) σ, ?_, ?_⟩ <;> rw [e]
    · exact hx
    · exact hσ.preimage _

theorem exists_ampleCub_of_iso : ∀ (S : Scheme.{0}) (G G' : Over S) [GrpObj G] [GrpObj G'] (e : G ≅ G'), IsMonHom e.hom → ∀ L' : LB G'.left, AmpleCub G' L' → ∃ L : LB G.left, AmpleCub G L := by
  intro S G G' _ _ e he L' h
  haveI : IsIso e.hom.left := inferInstanceAs (IsIso ((Over.forget S).map e.hom))
  exact ⟨_, ampleCub_pull e.hom h⟩

end GlobalTheory.SS.AmpIso
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsAutomorphismPermutationMaxOrderMembers
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.SS

namespace GlobalTheory.SS

theorem Model.twist_twist_symm {R K : Type} [CommRing R] [Field K] [Algebra R K] {A A' : Over (Sp K)}
    (M : Model R A) (f : A ≅ A') : (M.twist f).twist f.symm = M := by
  obtain ⟨Y, e, h₁, h₂, h₃⟩ := M
  simp [Model.twist]

theorem isIntegral_of_abelian {K : Type} [Field K] (A : Over (Sp K)) [GrpObj A] (hA : IsAbelianScheme A) :
    IsIntegral A.left := by
  have := hA.smooth
  have := hA.geomConnected
  exact GlobalTheory.isIntegral_of_smooth_of_geometricallyConnected A.hom

theorem exists_genIso_of_max_ord (R K : Type) [CommRing R] [IsDomain R] [IsLocalRing R] [Field K] [Algebra R K]
    (hSH : SH R K) (π : R) (hπ : Irreducible π) (A : Over (Sp K)) [GrpObj A] (hA : IsAbelianScheme A)
    (I : Type) [Fintype I] [DecidableEq I] (D : I → VF A) (hD : IsFrame D)
    (J : Type) (M : J → Model R A) (hI : ∀ j, (M j).Irr) (hW : WeakNeron M) (o : J → ℤ)
    (ho : ∀ j, HasOrd (M j) D π (o j)) (ρ : ℤ) (hρ : ∀ j, o j ≤ ρ) (f : A ≅ A) (i : J) (hi : o i = ρ) :
    ∃ i', o i' = ρ ∧ GenIso (M i) (M i') f.hom := by
  have hint := isIntegral_of_abelian A hA
  obtain ⟨-, -, h3, -⟩ := _root_.GlobalTheory.SS.GI.genIso_calculus R K hSH
  obtain ⟨hdvr, -, -, hfr⟩ := hSH
  have bound : ∀ (N : Model R A) (m : ℤ), N.Irr → HasOrd N D π m →
      m ≤ ρ ∧ (m = ρ → ∃ i', o i' = ρ ∧ GenIso N (M i') (𝟙 A)) := by
    intro N m hN hm
    obtain ⟨j, hj⟩ := _root_.GlobalTheory.SS.exists_defAt_of_weakNeron R K A J M hW N hN
    obtain ⟨h₁, h₂⟩ := _root_.GlobalTheory.SS.OrdMono.ord_mono R K π hπ A I D hD N (M j) m (o j) hN (hI j) hm (ho j) hj
    have := hρ j
    exact ⟨h₁.trans this, fun e => ⟨j, by omega, h₂ (by omega)⟩⟩
  obtain ⟨c, hc⟩ := _root_.GlobalTheory.SS.OrdTwist.main R K π hπ A hA I D hD f
  obtain ⟨c', hc'⟩ := _root_.GlobalTheory.SS.OrdTwist.main R K π hπ A hA I D hD f.symm
  have t₁ := hc _ _ (ho i)
  have t₂ := hc' _ _ (ho i)
  have t₃ := hc' _ _ t₁
  rw [Model.twist_twist_symm] at t₃
  have e₃ := (_root_.GlobalTheory.SS.Ord.existsUnique_hasOrd R K π hπ A I D hD (M i) (hI i)).unique t₃ (ho i)
  have i₁ : ((M i).twist f).Irr := hI i
  have i₂ : ((M i).twist f.symm).Irr := hI i
  obtain ⟨b₁, b₁'⟩ := bound _ _ i₁ t₁
  obtain ⟨b₂, -⟩ := bound _ _ i₂ t₂
  obtain ⟨i', hi', hg⟩ := b₁' (by omega)
  exact ⟨i', hi', (h3 A A (M i) (M i') f).2.1.2 hg⟩

theorem WeakNeron.nonempty {R K : Type} [CommRing R] [IsDomain R] [IsLocalRing R] [Field K] [Algebra R K]
    (hSH : SH R K) {A : Over (Sp K)} [GrpObj A] {J : Type} {M : J → Model R A} (hW : WeakNeron M) :
    Nonempty J := by
  obtain ⟨hdvr, -, -, hfr⟩ := hSH
  obtain ⟨i, -⟩ := hW R K (by simp) (η[A]).left (by
    rw [← Category.assoc, Over.w]
    simp)
  exact ⟨i⟩

theorem exists_permuted_members : ∀ (R K : Type) [CommRing R] [IsDomain R] [IsLocalRing R] [Field K] [Algebra R K], SH R K → ∀ (A : Over (Sp K)) [GrpObj A] [IsCommMonObj A], IsAbelianScheme A → ∀ (n : ℕ) (M : Fin n → Model R A), (∀ i, (M i).Irr) → WeakNeron M → ∃ S : Finset (Fin n), S.Nonempty ∧ (∀ (f : A ≅ A), ∀ i ∈ S, ∃ i' ∈ S, GenIso (M i) (M i') f.hom) ∧ ∀ (Θ : A ⊗ A ≅ A ⊗ A), ∀ i ∈ S, ∀ j ∈ S, ∃ i' ∈ S, ∃ j' ∈ S, GenIso ((M i).prod (M j)) ((M i').prod (M j')) Θ.hom := by
  intro R K _ _ _ _ _ hSH A _ _ hA n M hI hW
  have hne := hW.nonempty hSH
  have hdvr := hSH.1
  have hfr := hSH.2.2.2
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible R
  obtain ⟨g, hg⟩ := GlobalTheory.AbelianDim.exists_relDim K A hA
  obtain ⟨D, hD⟩ := _root_.GlobalTheory.SS.exists_isFrame K A g hg
  choose o ho using fun i => (_root_.GlobalTheory.SS.Ord.existsUnique_hasOrd R K π hπ A (Fin g) D hD (M i) (hI i)).exists
  obtain ⟨i₀, hi₀⟩ := Finite.exists_max o
  refine ⟨Finset.univ.filter fun i => o i = o i₀, ⟨i₀, by simp⟩, ?_, ?_⟩
  · intro f i hi
    obtain ⟨i', hi', h⟩ := exists_genIso_of_max_ord R K hSH π hπ A hA _ D hD _ M hI hW o ho (o i₀) hi₀ f i
      (by simpa using hi)
    exact ⟨i', by simpa using hi', h⟩
  · intro Θ i hi j hj
    have hi : o i = o i₀ := by simpa using hi
    have hj : o j = o i₀ := by simpa using hj
    obtain ⟨D₂, hD₂, hp⟩ := _root_.GlobalTheory.SS.OrdProd.ord_prod R K hSH π hπ A A _ _ D D hD hD
    obtain ⟨p₁, p₂⟩ := _root_.GlobalTheory.SS.prod_irr_and_weakNeron R K hSH A A
    obtain ⟨⟨i', j'⟩, h', h⟩ := exists_genIso_of_max_ord R K hSH π hπ (A ⊗ A)
      (AbelianSchemeGerms.isAbelianScheme_tensor A A hA hA) _ D₂ hD₂ (Fin n × Fin n)
      (fun p => (M p.1).prod (M p.2)) (fun p => p₁ _ _ (hI _) (hI _)) (p₂ _ _ M M hW hW)
      (fun p => o p.1 + o p.2) (fun p => hp _ _ _ _ (hI _) (hI _) (ho _) (ho _)) (o i₀ + o i₀)
      (fun p => add_le_add (hi₀ _) (hi₀ _)) Θ (i, j) (by simp [hi, hj])
    have a₁ := hi₀ i'
    have a₂ := hi₀ j'
    have h' : o i' + o j' = o i₀ + o i₀ := h'
    exact ⟨i', by simp; omega, j', by simp; omega, h⟩

end GlobalTheory.SS
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsCoordReducedFibreClosedPointStatement
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.ZJ
theorem _root_.GlobalTheory.T.exists_coord_reducedFibre_closedPoint : ∀ C : Core, C.HasTests → C.Fib → ∀ w : C.G.toScheme, IsClosed ({w} : Set C.G.toScheme) → ∃ (W : C.G.toScheme.Opens) (hw : w ∈ W) (u : Fin C.g → Γ(C.G.toScheme, W)), IsAffineOpen W ∧ C.Coord w W hw u := by
  first | exact @GlobalTheory.ZJ.Core.exists_coord | exact GlobalTheory.ZJ.Core.exists_coord | (intros; apply GlobalTheory.ZJ.Core.exists_coord <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsFinsetOfPoint
section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT

noncomputable section
namespace GlobalTheory.UT.CoefField
open TWM TWO CoefBasic

variable {R : Type} [CommRing R] [IsDomain R] {D : DegPre R} {E F : Type} [Field E] [Field F]
  [Algebra (FractionRing R) E] [Algebra (FractionRing R) F] [Algebra E F] [IsScalarTower (FractionRing R) E F]

theorem he_cub (x x' y : TF (R := R) E ⟶ D.P.A) :
    HE R E F D.P.L (fun _ _ h => h (ιE R E F ≫ x * ιE R E F ≫ x' * ιE R E F ≫ y).left *
      (h (ιE R E F ≫ x * ιE R E F ≫ x').left)⁻¹ * (h (ιE R E F ≫ x * ιE R E F ≫ y).left)⁻¹ *
      (h (ιE R E F ≫ x' * ιE R E F ≫ y).left)⁻¹ * h (ιE R E F ≫ x).left * h (ιE R E F ≫ x').left *
      h (ιE R E F ≫ y).left * (h (1 : TF (R := R) F ⟶ D.P.A).left)⁻¹)
      (fun z J => (th D z J (ιE R E F ≫ x) (ιE R E F ≫ x') (ιE R E F ≫ y)).val) 1 :=
  (he_gen (L := D.P.L) (φ := thφ D.P.A (x3 D.P.A)) (ε := thε) D.cub.isGen
    (lift x (lift x' y)).left (r := (lift (ιE R E F ≫ x) (lift (ιE R E F ≫ x') (ιE R E F ≫ y))).left)
    (by rw [← Over.comp_left, comp_lift, comp_lift])).congr (fun U _ h => prod_cub _ _ _ h)
    (fun _ _ _ => rfl)

theorem exists_gt (g : GtPtF D F) (b₁ : TF (R := R) E ⟶ D.P.A) (hb : ιE R E F ≫ b₁ = g.b) :
    ∃ (x : D.X → F) (S : Finset F), (∀ χ, HE R E F D.P.L (fun _ _ h => ∏ i, h (DegPre.gtφ D F g.b χ i) ^ DegPre.gtε i)
      (fun z J => (val (g.s χ) (𝟙 _) z J).val) (x χ)) ∧
      ∀ K : Subfield F, (∀ a, algebraMap E F a ∈ K) → (S : Set F) ⊆ K → ∀ χ, x χ ∈ K := by
  classical
  have hL := D.P.isLB
  choose x hx0 hx using fun χ => exists_he (R := R) (E := E) (F := F) hL (g.isGen χ) (fun i => by
    fin_cases i
    · refine ⟨(cP D _ χ * b₁).left, ?_⟩
      show (cP D _ χ * g.b).left = _
      rw [← Over.comp_left, MonObj.comp_mul, comp_cP, hb]
    · refine ⟨(cP D _ χ).left, ?_⟩
      show (cP D _ χ).left = _
      rw [← Over.comp_left, comp_cP]
    · refine ⟨b₁.left, ?_⟩
      show g.b.left = _
      rw [← Over.comp_left, hb]
    · refine ⟨(1 : TF (R := R) E ⟶ D.P.A).left, ?_⟩
      show (1 : TF (R := R) F ⟶ D.P.A).left = _
      rw [← Over.comp_left, MonObj.comp_one])
  have hadd : ∀ χ χ', ∃ a : E, x (χ + χ') = x χ * x χ' * algebraMap E F a := fun χ χ' => by
    have C := he_cub (F := F) (cP D _ χ) (cP D _ χ') b₁
    rw [comp_cP, comp_cP, hb] at C
    obtain ⟨a, ha⟩ := ((hx χ).mul (hx χ')).ratio hL ((hx (χ + χ')).mul C) (fun U _ h => by
      rw [prod_gt, prod_gt, prod_gt, cPoint_add]
      apply Additive.ofMul.injective
      simp only [ofMul_mul, ofMul_inv]
      abel)
    obtain ⟨z⟩ := exists_pt (R := R) (F := F)
    obtain ⟨J, hJ⟩ := exists_good' hL z
    have e := gt_mul (𝟙 (TF (R := R) F)) hJ g χ χ'
    rw [Category.id_comp, Over.id_left] at e
    have e' := ha z J hJ
    rw [← Units.val_mul, ← Units.val_mul, e, Units.mul_left_inj, _root_.mul_one, cst_eq, cst_eq] at e'
    exact ⟨a, cstH_inj z e'⟩
  obtain ⟨T, hT⟩ : (⊤ : Submodule ℤ D.X).FG := Module.Finite.fg_top
  refine ⟨x, T.image x, hx, fun K hK hS χ => ?_⟩
  have h0 : x 0 ∈ K := by
    obtain ⟨a, ha⟩ := hadd 0 0
    rw [add_zero, _root_.mul_assoc, left_eq_mul₀ (hx0 0)] at ha
    rw [eq_inv_of_mul_eq_one_left ha]
    exact inv_mem (hK a)
  let G : AddSubgroup D.X :=
    { carrier := {χ | x χ ∈ K}
      zero_mem' := h0
      add_mem' := fun {χ χ'} h h' => by
        obtain ⟨a, ha⟩ := hadd χ χ'
        show x _ ∈ K
        rw [ha]; exact mul_mem (mul_mem h h') (hK a)
      neg_mem' := fun {χ} h => by
        obtain ⟨a, ha⟩ := hadd χ (-χ)
        rw [add_neg_cancel] at ha
        have ha0 : algebraMap E F a ≠ 0 := fun h0 => hx0 0 (by rw [ha, h0, MulZeroClass.mul_zero])
        have e : x (-χ) = x 0 * (x χ)⁻¹ * (algebraMap E F a)⁻¹ := by
          have := hx0 χ
          rw [ha]; field_simp
        show x _ ∈ K
        rw [e]; exact mul_mem (mul_mem h0 (inv_mem h)) (inv_mem (hK a)) }
  have hle : Submodule.span ℤ (T : Set D.X) ≤ G.toIntSubmodule :=
    Submodule.span_le.2 fun t ht => hS (by simpa using ⟨t, ht, rfl⟩)
  exact hle (hT ▸ Submodule.mem_top)

theorem fe_at (hG : GlobalFnsSt) {k : ℕ} (s : Fam D F k) (b : TF (R := R) F ⟶ D.P.A) (b₁ : TF (R := R) E ⟶ D.P.A)
    (hb : ιE R E F ≫ b₁ = b) (α mu : D.X) :
    ∃ f, HE R E F D.P.L (fun _ _ h => (h b.left ^ ((k : ℤ) - 1) * h (cP D _ (α + k • mu) * b).left *
        (h (cP D _ (α + k • mu)).left)⁻¹ * h (1 : TF (R := R) F ⟶ D.P.A).left) *
        (h (b * cP D _ mu).left ^ ((k : ℤ) - 1) * h (cP D _ α * (b * cP D _ mu)).left *
        (h (cP D _ α).left)⁻¹ * h (1 : TF (R := R) F ⟶ D.P.A).left)⁻¹) f 1 ∧
      ∀ z J, Good D.P.L z J → sval (s.s (α + k • mu)) (lift (𝟙 (TF (R := R) F)) b).left z J =
        sval (s.s α) (lift (𝟙 (TF (R := R) F)) (b * cP D _ mu)).left z J * f z J := by
  have hL := D.P.isLB
  obtain ⟨⟨u, hu, hc⟩, hv⟩ := gen_fe (D := D) (F := F) hG k mu α
  obtain ⟨⟨u', hu', hc'⟩, hv'⟩ := gen_fe (D := D) (F := E) hG k mu α
  let ρ' : TF (R := R) F ⟶ DegPre.BF D E := lift (ιE R E F) b
  have hρ : (ιE R E F).left ≫ (lift (𝟙 (TF (R := R) E)) b₁).left = ρ'.left := by
    rw [← Over.comp_left, comp_lift, Category.comp_id, hb]
  have p₁ : ρ' ≫ DegPre.prB D E = b := lift_snd _ _
  have p₂ : (ρ' ≫ DegPre.trF D E mu) ≫ DegPre.prB D E = b * cP D _ mu := by
    rw [Category.assoc, trF_eq, tr_pr, MonObj.comp_mul, p₁, comp_cP, comp_cP]
  refine ⟨fun z J => (val u' ρ'.left z J).val, (he_gen hu' _ hρ).congr (fun U _ h => ?_) (fun _ _ _ => rfl),
    fun z J hJ => ?_⟩
  · have q₁ := prod_fam D E ρ' (α + k • mu) k h
    have q₂ := prod_fam D E (ρ' ≫ DegPre.trF D E mu) α k h
    rw [p₁] at q₁
    rw [p₂] at q₂
    rw [← q₁, ← prod_neg _ _ q₂, Fintype.prod_sum_type]
    rfl
  · have e := (secRel_iff hL _ _ _ _ _ _ _ _ _ u).1 (s.fe mu α u hu hc) _ (lift (𝟙 (TF (R := R) F)) b).left z J hJ
    have t : lift (𝟙 (TF (R := R) F)) b ≫ DegPre.trF D F mu = lift (𝟙 (TF (R := R) F)) (b * cP D _ mu) := by
      apply CartesianMonoidalCategory.hom_ext
      · rw [Category.assoc, trF_eq, tr_fst, lift_fst, lift_fst]
      · rw [Category.assoc, trF_eq, tr_pr, MonObj.comp_mul, lift_snd, lift_snd, comp_cP, comp_cP]
    rw [← Over.comp_left, t] at e
    refine e.trans (congrArg₂ (· * ·) rfl (congrArg Units.val ?_))
    rw [hv u hu hc _ (lift (𝟙 (TF (R := R) F)) b) z J hJ, hv' u' hu' hc' _ ρ' z J hJ, val_famMult _ hJ,
      val_famMult _ hJ, uVal, uVal, p₁, lift_snd, lift_fst, lift_fst, comp_cP, comp_cP, comp_cP, comp_cP]
    have j : (ιE R E F).left ≫ jFK (R := R) E = Over.Hom.left (𝟙 (TF (R := R) F)) ≫ jFK (R := R) F :=
      (comp_jFK R E F).trans (Category.id_comp _).symm
    rw [j]

theorem exists_finset_of_point (hG : GlobalFnsSt) {k : ℕ} (hk : 1 ≤ k) (s : Fam D F k) (g : GtPtF D F)
    {w : Frm D F k g.b} (hw : w.IsGen) (b₁ : TF (R := R) E ⟶ D.P.A) (hb : ιE R E F ≫ b₁ = g.b)
    (hs : ∀ α, ∃ (n : ℕ) (a : Fin n → F) (σ : Fin n → D.SecB k α)
      (σF : Fin n → LB.Sec (LB.LinComb D.P.L (DegPre.famφ D F α) (DegPre.famε k))),
      (∀ i, GeneratorPullback.SecScal D.P.L (DegPre.famφ D F α) (DegPre.famε k) (σF i)
        (D.famφB α) (DegPre.famε k) (σ i) (DegPre.prB D F).left 1) ∧
      ∀ j, (s.s α).f j = ∑ i, DegPre.constBF D F (a i) _ * (σF i).f j) :
    ∃ S : Finset F, ∀ K : Subfield F, (∀ a, algebraMap E F a ∈ K) → (S : Set F) ⊆ K → ∀ χ, coef s g w χ ∈ K := by
  classical
  have hL := D.P.isLB
  obtain ⟨x, S, hx, hS⟩ := exists_gt g b₁ hb
  obtain ⟨ω, -, hω⟩ := exists_he (R := R) (E := E) (F := F) hL hw (fun i => by
    fin_cases i
    · refine ⟨(1 : TF (R := R) E ⟶ D.P.A).left, ?_⟩
      show (1 : TF (R := R) F ⟶ D.P.A).left = _
      rw [← Over.comp_left, MonObj.comp_one]
    · refine ⟨b₁.left, ?_⟩
      show g.b.left = _
      rw [← Over.comp_left, hb])
  obtain ⟨-, e, he⟩ := exists_representatives_mod_nsmul D.X k hk
  choose n a σ σF hσ hsum using hs
  have Rg := (he_gen (R := R) (E := E) (F := F) (L := D.P.L) (φ := fun _ : PUnit => eSec D.P.A) (ε := fun _ => 1)
    D.rig_gen (TF (R := R) E).hom (Over.w (ιE R E F))).pow k
  refine ⟨insert ω (S ∪ Finset.univ.biUnion fun i => Finset.univ.image (a (e i))), fun K hK hSK χ => ?_⟩
  obtain ⟨i₀, ⟨mu, rfl⟩, -⟩ := he χ
  set α := e i₀ with hα
  obtain ⟨f, hf, hfe⟩ := fe_at (E := E) hG s g.b b₁ hb α mu
  have key : ∀ i, ∃ c : F, c ∈ K ∧ ∀ z J, Good D.P.L z J →
      sval (σ α i) (g.b * cP D _ mu).left z J * f z J * (val (g.s (α + k • mu)) (𝟙 _) z J).val * (val w (𝟙 _) z J).val =
        cst F z c * (rigV D (TF (R := R) F).hom z J).val ^ k := fun i => by
    obtain ⟨y, A⟩ := he_sec (R := R) (E := E) (F := F) hL (σ α i) (b₁ * cP D _ mu).left (r := (g.b * cP D _ mu).left)
      (by rw [← Over.comp_left, MonObj.comp_mul, comp_cP, hb])
    obtain ⟨c, hc⟩ := (((A.mul hf).mul (hx (α + k • mu))).mul hω).ratio hL Rg (fun U _ h => by
      have e₀ : (TF (R := R) F).hom ≫ eSec D.P.A = (1 : TF (R := R) F ⟶ D.P.A).left := rfl
      have e₁ : SectionScalarValuation.cQ D (TF (R := R) F) α = cP D _ α := rfl
      rw [SectionScalarValuation.prod_famB, prod_gt, prod_line, Fintype.prod_unique, e₀, e₁, mul_comm _ (cP D _ α)]
      apply Additive.ofMul.injective
      simp only [ofMul_mul, ofMul_inv, ofMul_zpow, ofMul_pow]
      module)
    refine ⟨_, mul_mem (mul_mem (mul_mem (mul_mem (hK y) (one_mem K))
      (hS K hK (fun t ht => hSK (by simp [show t ∈ S from ht])) (α + k • mu))) (show ω ∈ K from hSK (by simp))) (hK c),
      fun z J hJ => ?_⟩
    have := hc z J hJ
    rw [one_pow, cst_eq, map_one, _root_.one_mul] at this
    exact this
  choose c hcK hc using key
  have E₀ : coef s g w (α + k • mu) = ∑ i, a α i * c i := coef_eq fun z J hJ => by
    set_option synthInstance.maxHeartbeats 100000 in
      rw [hfe z J hJ, SectionScalarValuation.sval_lin (fun i => gF D F (a α i)) (σF α) (fun j => hsum α j) _ z hJ, cst_eq, map_sum,
      Finset.sum_mul, Finset.sum_mul, Finset.sum_mul, Finset.sum_mul]
    refine Finset.sum_congr rfl fun i _ => ?_
    have b : gs (lift (𝟙 (TF (R := R) F)) (g.b * cP D _ mu)).left z ⊤ (gF D F (a α i)) = cst F z (a α i) := by
      refine (gs_pull _ (fst (TF (R := R) F) D.P.A).left z ⊤ trivial _).trans ?_
      rw [← Over.comp_left, lift_fst]; rfl
    have e₂ := SectionScalarValuation.secScal_sval (hσ α i) (lift (𝟙 (TF (R := R) F)) (g.b * cP D _ mu)).left z hJ
    rw [← Over.comp_left, lift_snd] at e₂
    rw [b, map_mul, ← cst_eq, ← cst_eq, _root_.mul_assoc, ← hc i z J hJ, ← e₂]
    ring
  rw [E₀]
  exact sum_mem fun i _ => mul_mem (hSK (by
    simp only [Finset.coe_insert, Finset.coe_union, Set.mem_insert_iff, Set.mem_union, Finset.mem_coe,
      Finset.mem_biUnion, Finset.mem_image, Finset.mem_univ, true_and]
    exact Or.inr (Or.inr ⟨i₀, i, rfl⟩))) (hcK i)

theorem exists_finset (hG : GlobalFnsSt) {k : ℕ} (hk : 1 ≤ k) (s : Fam D F k) (g : GtPtF D F)
    {w : Frm D F k g.b} (hw : w.IsGen)
    (hs : ∀ α, ∃ (n : ℕ) (a : Fin n → F) (σ : Fin n → D.SecB k α)
      (σF : Fin n → LB.Sec (LB.LinComb D.P.L (DegPre.famφ D F α) (DegPre.famε k))),
      (∀ i, GeneratorPullback.SecScal D.P.L (DegPre.famφ D F α) (DegPre.famε k) (σF i)
        (D.famφB α) (DegPre.famε k) (σ i) (DegPre.prB D F).left 1) ∧
      ∀ j, (s.s α).f j = ∑ i, DegPre.constBF D F (a i) _ * (σF i).f j) :
    ∃ S : Finset F, ∀ K : Subfield F, (∀ a, algebraMap (FractionRing R) F a ∈ K) → (S : Set F) ⊆ K →
      ∀ χ, coef s g w χ ∈ K := by
  classical
  have := D.P.isAb.proper
  obtain ⟨T, b₁, hb⟩ := exists_adjoin D.P.A g.b
  obtain ⟨S, hS⟩ := exists_finset_of_point hG hk s g hw b₁ hb hs
  refine ⟨S ∪ T, fun K hK hST => hS K (fun a => ?_) fun t ht => hST (by simp [show t ∈ S from ht])⟩
  have hle : IntermediateField.adjoin (FractionRing R) (T : Set F) ≤ K.toIntermediateField hK :=
    IntermediateField.adjoin_le_iff.2 fun t ht => hST (by simp [show t ∈ T from ht])
  exact hle a.2

end GlobalTheory.UT.CoefField
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsFramesOnUniformisedFibreThroughIsoStatement
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry IsLocalRing
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR GlobalTheory.ZH GlobalTheory.UT
open Classical
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_frames_on_uniformised_fibre_through_iso : ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] [ArithBase o Ω] (S : ThetaSys o Ω) (ρ : S.Real) (p : ℕ) [Fact p.Prime] (y₀ : S.R →+* PadicAlgCl p) (u : ρ.UTest p y₀) (x : S.Gam → (TFK (R := u.V) (PadicAlgCl p) ⟶ u.A.A)), (∀ a, (x a).left ≫ u.φ = spMap y₀ ≫ (ρ.pt a).left) → ∀ w : LB.Iso u.A.L (ρ.P.L.pull u.φ), w.IsGen → ∃ (rig : LB.Gen (u.A.L.pull (eSec u.A.A))) (e : ∀ a, FrAt (x a)), rig.IsGen ∧ GlobalTheory.ThetaPtMove.GenThrough w (fun _ : PUnit => eSec u.A.A) (fun _ : PUnit => eSec ρ.P.A) (fun _ => 1) rig ρ.rig (spMap u.yK) ∧ ∀ a, IsTorsFrame u.A rig (S.r * S.N) (x a) (e a) ∧ GlobalTheory.ThetaPtMove.GenThrough w (fun _ : Fin 1 => (x a).left) (fun _ : Fin 1 => (ρ.pt a).left) (fun _ => 1) (e a) (ρ.fr a) (spMap y₀) := by
  first | exact @GlobalTheory.exists_frames_on_fibre_through | exact GlobalTheory.exists_frames_on_fibre_through | (intros; apply GlobalTheory.exists_frames_on_fibre_through <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsTorusActionWeightedChartsStatement
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open ReciprocityTheory.ChartRestriction.G.Out GlobalTheory.ZH Classical
attribute [local instance] SplitExt.free SplitExt.finite MvPolynomial.gradedAlgebra
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_torus_action_weighted_charts : Out.Laws → Out.Laws2 → ∀ (k : Type) [Field k] [IsAlgClosed k] (Φ : FibPre k) (g N N' : ℕ) (q : QuadraticMap ℤ Φ.E.X ℝ) (J : Type) [Fintype J] (cls : J → Φ.E.X) (F F' : J → (Φ.H 1).Sec) (π : Φ.Pol N) (m : Matrix J J k) (Ch : GlobalTheory.ZJ.Charts Φ.G.left) (e : Ch.I ≃ J) (cl : Φ.E.X → Ch.Cl), Big g N N' → Φ.Good N q cls F → π.PB.g + Module.finrank ℤ Φ.E.X = g → IsUnit m.det → (∀ i, IsLin Φ.G.hom F (m i) (F' i)) → (∀ α β, cl α = cl β ↔ ∃ n, α = β + N • n) → cl 0 = Ch.c₀ → (∀ i j, m (e i) j ≠ 0 → Ch.wt i = cl (cls j)) → (∀ i, Ch.W i = nonzeroLocus (F' (e i.1)) ∧ ∀ j, IsRatio (F' (e j)) (F' (e i.1)) (Ch.W i) (Ch.r i j)) → ∃ c : Fin (Module.finrank ℤ Φ.E.X) → Ch.Cl, GlobalTheory.ZJ.Charts.Split (H := Φ.G) Ch c := by
  first | exact @GlobalTheory.ZH.FibTorus.exists_split | exact GlobalTheory.ZH.FibTorus.exists_split | (intros; apply GlobalTheory.ZH.FibTorus.exists_split <;> assumption)
end

