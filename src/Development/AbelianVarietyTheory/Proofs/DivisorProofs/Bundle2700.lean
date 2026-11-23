module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.DensConst
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0039
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsAmbOfIsArithVar
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0004
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2390
public import ReciprocityTheory.AnalyticForms.PotentialTheory.Bundle0003
public import ReciprocityTheory.AnalyticForms.PotentialTheory.Bundle0005
public import ReciprocityTheory.AnalyticForms.PotentialTheory.Bundle0006
public import ReciprocityTheory.AnalyticForms.PotentialTheory.Bundle0007
public import ReciprocityTheory.AnalyticForms.PotentialTheory.Bundle0008
public import ReciprocityTheory.AnalyticForms.PotentialTheory.Stokes
public import ReciprocityTheory.AnalyticForms.PotentialTheory.SNCAtlas
public import ReciprocityTheory.AnalyticForms.PotentialTheory.Bundle0002
public import ReciprocityTheory.AnalyticForms.PlurisubharmonicFunctions.Bundle0001
public import ReciprocityTheory.AnalyticForms.PotentialTheory.PLCurveA
public import ReciprocityTheory.AnalyticForms.PotentialTheory.PLLocalStatement
public import ReciprocityTheory.AnalyticForms.PotentialTheory.Pullback
public import ReciprocityTheory.AnalyticForms.PotentialTheory.AtlasIndep
public import ReciprocityTheory.AnalyticForms.PotentialTheory.DegreeInt
public import ReciprocityTheory.AnalyticForms.PotentialTheory.ContDiffFubiniStudyRatioCompChart0
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2516
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2521
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2664
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2606
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2565
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0066
public import Development.AbelianVarietyTheory.Definitions.Uniformization.Bundle0002
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1880
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2252
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2613
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2420
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2419
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2638
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2557
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2612
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2564
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2550
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1044
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0017
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1403
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1436
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2663
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorusHomOfIff
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0132
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.RosatiAdjointAbelianPartAndClassifyingMapLinear
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0133
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2463
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2512
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CubeVal
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2538
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2648
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsDimEqOne
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2579
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2660
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2661

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LogNormSectionIntegrableMixedChernProjective
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Set Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.R
open GlobalTheory GlobalTheory.Cartier GlobalTheory.CxPts GlobalTheory.Points GlobalTheory.CechPic GlobalTheory.ChartGlue GlobalTheory.Mix
namespace GlobalTheory.Mix

theorem logSec_intg_proj : GlobalTheory.Published.Principalisation → ∀ (F : Type) [Field F] (X : Scheme.{0}) [IsIntegral X] [IsLocallyNoetherian X] (p : X ⟶ Sp F) (σ : F →+* ℂ) (D : ℕ), IsProjOver p → topologicalKrullDim X = (D : ℕ) → ∀ (L : Fin D → MLine p σ) (M : MLine p σ) (s : M.B.Sec), genericPoint X ∈ nonzeroLocus s → Intg L (M.logSec s) := by
  intro hP F _ X _ _ p σ D hproj hdim L M s hs
  haveI : CharZero F := RingHom.charZero σ
  obtain ⟨Y, hY, π, hsm, hprojY, hdimY, hgen, hdeg, -⟩ :=
    _root_.GlobalTheory.LogResProj.exists_logResolution hP F X p D hproj hdim ⊥ (fun h => h)
  haveI : Smooth (π ≫ p) := SmoothOfRelativeDimension.smooth D (π ≫ p)
  haveI : IsLocallyNoetherian Y := LocallyOfFiniteType.isLocallyNoetherian (π ≫ p)
  obtain ⟨s', hz, hn, -⟩ := _root_.GlobalTheory.Mix.exists_secPull_props F X Y p (π ≫ p) σ π rfl M s
  have hs' : genericPoint Y ∈ nonzeroLocus s' := by
    rw [hz]; show π (genericPoint Y) ∈ nonzeroLocus s; rw [hgen]; exact hs
  have hsmooth := _root_.GlobalTheory.MixLogSec.intg_logSec F Y (π ≫ p) σ D hprojY hsm (fun i => (L i).pull π rfl) (M.pull π rfl) s' hs'
  have hmeas := (GlobalTheory.Mix.SecNorm.logSec_basic F X p σ M s).1
  have hpush := (_root_.GlobalTheory.PushInt.mixInt_pull F X Y p (π ≫ p) σ D hproj hdim hprojY π rfl hgen (by rw [hdeg]; exact one_ne_zero) L (M.logSec s) hmeas).1
  refine hpush.1 ?_
  have hfun : (fun y => M.logSec s (ptMap π rfl σ y)) = (M.pull π rfl).logSec s' := by
    funext y; simp only [MLine.logSec]; rw [hn y]
  rw [hfun]; exact hsmooth

end GlobalTheory.Mix
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MatrixActsOnTorsionLabels
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH
open scoped CategoryTheory.Obj
open GlobalTheory.Poinc GlobalTheory.Poinc.Eq8 Formalism.L2.Pj
open scoped TensorProduct
attribute [local instance] Over.cartesianMonoidalCategory
open Classical

namespace GlobalTheory.Poinc.Eq8.MatTors

theorem endU_exists (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] (hadm : AdmBase R (maximalIdeal R))
    (D : DegData R (maximalIdeal R)) (P : PolAV (Sp (FractionRing R))) (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G]
    (hG : IsSemiAbelian G) (U : Unif (maximalIdeal R) D P G) (aA : P.A ⟶ P.A) (haA : IsMonHom aA) :
    ∃ E : GlobalTheory.UT.EndU U.toUnifPre, E.aA = aA := by
  haveI := hadm.1
  haveI := hadm.2.2.1
  have := U.gen_hom
  have hinv : IsMonHom U.gen.inv := inferInstance
  obtain ⟨F, ⟨hF, hF'⟩, -⟩ := GlobalTheory.Published.SemiAbelianHomExtension.fractionField GlobalTheory.semiAbelianHomExtension_holds R
    (FractionRing R) G G hG hG (U.gen.hom ≫ aA ≫ U.gen.inv)
  obtain ⟨E, -, hE⟩ := GlobalTheory.UT.exists_degenerationEndomorphism_of_admissibleBase R (maximalIdeal R) hadm D P G hG U F aA hF haA
    (by rw [hF']; simp)
  exact ⟨E, hE⟩

theorem isMonHom_matrix (S : Scheme.{0}) (X Y : Over S) [GrpObj X] [GrpObj Y] [IsCommMonObj Y] (pr : Fin 8 → (X ⟶ Y))
    (hpr : ∀ a, IsMonHom (pr a))
    (hu : ∀ (T' : Over S) (y' : Fin 8 → (T' ⟶ Y)), ∃! x : T' ⟶ X, ∀ a, x ≫ pr a = y' a) (f : X ⟶ X)
    (a : Matrix (Fin 8) (Fin 8) ℤ) (hf : ∀ u, f ≫ pr u = (List.ofFn fun v => pr v ^ a u v).prod) : IsMonHom f := by
  haveI : ∀ v, IsMonHom (pr v) := hpr
  refine ReciprocityTheory.ChartRestriction.G.Geo.Tor.isMonHom_of_mul f fun T x y => ?_
  have hz : ∀ (z : T ⟶ X) (u : Fin 8), z ≫ f ≫ pr u = ∏ v, (z ≫ pr v) ^ a u v := by
    intro z u
    let φz : (X ⟶ Y) →* (T ⟶ Y) := ⟨⟨(z ≫ ·), MonObj.comp_one z⟩, MonObj.comp_mul z⟩
    rw [hf u, List.prod_ofFn]
    exact (map_prod φz _ _).trans (Finset.prod_congr rfl fun v _ => map_zpow φz _ _)
  refine (hu T fun u => ((x * y) ≫ f) ≫ pr u).unique (fun u => rfl) (fun u => ?_)
  rw [MonObj.mul_comp, Category.assoc, Category.assoc, Category.assoc, hz, hz, hz]
  simp only [MonObj.mul_comp, mul_zpow, Finset.prod_mul_distrib]

theorem exists_adjoint (S a : Matrix (Fin 8) (Fin 8) ℤ) (hS : S.det = 1) : ∃ a', S * a' = a.transpose * S :=
  ⟨S⁻¹ * (a.transpose * S), Matrix.mul_nonsing_inv_cancel_left S _ (hS ▸ isUnit_one)⟩

theorem matrix_acts_on_torsion_labels : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], GlobalTheory.Mum.Base R → IsDiscreteValuationRing R → ∀ (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ (D : DegData R (maximalIdeal R)) (A : PolAV (Sp (FractionRing R))) (U : Unif (maximalIdeal R) D A G) (G' : Over (Sp R)) [GrpObj G'] [IsCommMonObj G'], IsSemiAbelian G' → ∀ (D' : DegData R (maximalIdeal R)) (A' : PolAV (Sp (FractionRing R))) (U' : Unif (maximalIdeal R) D' A' G') (W : Matrix (Fin 8) (Fin 8) ℤ), IsE8 W → ∀ (pr : Fin 8 → (A'.A ⟶ A.A)), (∀ a, IsMonHom (pr a)) → (∀ (T' : Over (Sp (FractionRing R))) (y : Fin 8 → (T' ⟶ A.A)), ∃! z : T' ⟶ A'.A, ∀ a, z ≫ pr a = y a) → LBIso A'.L (LB.LinComb (abelian₂ A.A A.L) (K := Fin 8 × Fin 8) (fun ab => (lift (pr ab.1) (pr ab.2)).left) (fun ab => W ab.1 ab.2)) → ∀ (pG : Fin 8 → (G' ⟶ G)), (∀ v, IsMonHom (pG v)) → (∀ v, (Over.pullback (jK R)).map (pG v) ≫ U.gen.hom = U'.gen.hom ≫ pr v) → ∀ (c : Fin 8 → (D.toPre.X →+ D'.toPre.X)), (∀ v, TorMatch U U' (RingHom.id R) (pG v).left (c v)) → ∀ e : D'.toPre.X ≃+ (Fin 8 → D.toPre.X), (∀ y, ∑ v, c v (∑ u, (W + W.transpose) v u • e y u) = y) → ∀ (a : Matrix (Fin 8) (Fin 8) ℤ) (f : A'.A ⟶ A'.A), (∀ u, f ≫ pr u = (List.ofFn fun v => pr v ^ a u v).prod) → ∀ (K : Type) [Field K] [IsAlgClosed K] [Algebra (FractionRing R) K] (m : ℕ) (pk pk' : QkPt D'.toPre K m) (x : TFK (R := R) K ⟶ A'.A), 1 ≤ m → QkToAkU U'.toUnifPre K m pk x → QkToAkU U'.toUnifPre K m pk' (x ≫ f) → CongMod m (e pk'.y) (fun u => ∑ v, a u v • e pk.y v) := by
  intro R _ _ _ hB hdvr G _ _ hG D A U G' _ _ hG' D' A' U' W hW pr hpr hpu hL pG hpG hext c hc e he a f hf K _ _ _ m pk pk' x
    hm hx hx'
  obtain ⟨a', ha⟩ := exists_adjoint (W + W.transpose) a hW.2
  obtain ⟨f', hf', -⟩ := hpu A'.A (fun u => (List.ofFn fun v => pr v ^ a' u v).prod)
  obtain ⟨E, hE⟩ := endU_exists R hB.1 D' A' G' hG' U' f (isMonHom_matrix _ A'.A A.A pr hpr hpu f a hf)
  obtain ⟨E', hE'⟩ := endU_exists R hB.1 D' A' G' hG' U' f' (isMonHom_matrix _ A'.A A.A pr hpr hpu f' a' hf')
  subst hE hE'
  have h₁ := GlobalTheory.T.eighthPower_formBundle_matrices_adjoint _ A A' W pr hpr hL a a' ha E.aA E'.aA hf hf'
  have h₂ := _root_.GlobalTheory.PoincAdj.lbIso_adj_of_generic R hB G' hG' D' A' U' E E' h₁
  obtain ⟨w, hw⟩ := GlobalTheory.T.endomorphism_moves_torsionLattice_by_adjoint R hB G' hG' D' A' U' E E' h₂ K m pk pk' x hm hx hx'
  have h₃ := GlobalTheory.T.eighth_power_endomorphism_lattice_adjoint R hB hdvr G hG D A U G' hG' D' A' U' W hW pr hpr hpu hL pG hpG hext c hc e he a a' ha E' hf' pk.y
  exact ⟨e w, by rw [hw, map_add (f := _), map_nsmul, h₃]⟩

end GlobalTheory.Poinc.Eq8.MatTors
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MixedChernIntegralPointClosurePullback
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Set Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.R
open GlobalTheory GlobalTheory.Cartier GlobalTheory.CxPts GlobalTheory.Points GlobalTheory.CechPic GlobalTheory.ChartGlue GlobalTheory.Mix

set_option autoImplicit false

namespace GlobalTheory.CycPush

theorem isProjOver_comp {k : Type} [CommRing k] {X Z : Scheme.{0}} {p : X ⟶ Sp k} (hp : IsProjOver p)
    (i : Z ⟶ X) [IsClosedImmersion i] : IsProjOver (i ≫ p) := by
  obtain ⟨N, j, hj, rfl⟩ := hp
  exact ⟨N, i ≫ j, inferInstance, by rw [Category.assoc]⟩

theorem pull_congr {k : Type} [CommRing k] {X Y : Scheme.{0}} {p : X ⟶ Sp k} {q : Y ⟶ Sp k} {σ : k →+* ℂ}
    (A : MLine p σ) {a b : Y ⟶ X} (hab : a = b) (ha : a ≫ p = q) (hb : b ≫ p = q) :
    A.pull a ha = A.pull b hb := by
  subst hab; rfl

theorem dim_le_of_dominant : ∀ (F : Type) [Field F] (X Y : Scheme.{0}) [IsIntegral X] [IsIntegral Y] (p : X ⟶ Sp F) (q : Y ⟶ Sp F), IsProjOver p → IsProjOver q → ∀ (π : Y ⟶ X), π ≫ p = q → π (genericPoint Y) = genericPoint X → ∀ n : ℕ, topologicalKrullDim Y = n → ∃ m : ℕ, m ≤ n ∧ topologicalKrullDim X = m := by
  intro F _ W M _ _ p q hp hq f hπ hη n hM
  obtain ⟨N, i, hi, hcomp⟩ := hp
  obtain ⟨N', j, hj, hcomp'⟩ := hq
  haveI : IsProper (PSpace.str F N) := isProper_str F N
  haveI : IsProper (PSpace.str F N') := isProper_str F N'
  haveI : IsProper p := by rw [← hcomp]; infer_instance
  haveI : IsProper (f ≫ p) := by rw [hπ, ← hcomp']; infer_instance
  haveI : IsProper f := IsProper.of_comp f p
  have hf : LocallyOfFiniteType f := inferInstance
  obtain ⟨_, ⟨V, hV, rfl⟩, hxV, -⟩ := W.isBasis_affineOpens.exists_subset_of_mem_open
    (Set.mem_univ (genericPoint W)) isOpen_univ
  have hV : IsAffineOpen V := hV
  have hx : f (genericPoint M) ∈ V := hη ▸ hxV
  obtain ⟨_, ⟨U, hU, rfl⟩, hy, hUV⟩ := M.isBasis_affineOpens.exists_subset_of_mem_open
    (show genericPoint M ∈ f ⁻¹ᵁ V from hx) (f ⁻¹ᵁ V).isOpen
  have hU : IsAffineOpen U := hU
  haveI : Nonempty V := ⟨⟨_, hx⟩⟩
  haveI : Nonempty U := ⟨⟨_, hy⟩⟩
  have e : U ≤ f ⁻¹ᵁ V := hUV
  let φ := Spec.preimage (hV.fromSpec ≫ p)
  have hφ : Spec.map φ = hV.fromSpec ≫ p := Spec.map_preimage _
  letI : Algebra F Γ(W, V) := φ.hom.toAlgebra
  have hftA : Algebra.FiniteType F Γ(W, V) :=
    (HasRingHomProperty.Spec_iff (P := @LocallyOfFiniteType) (φ := φ)).mp (hφ ▸ inferInstance)
  letI : Algebra Γ(W, V) Γ(M, U) := (f.appLE V U e).hom.toAlgebra
  have hftB : Algebra.FiniteType Γ(W, V) Γ(M, U) :=
    HasRingHomProperty.appLE @LocallyOfFiniteType f hf ⟨V, hV⟩ ⟨U, hU⟩ e
  letI : Algebra F Γ(M, U) := (φ ≫ f.appLE V U e).hom.toAlgebra
  haveI : IsScalarTower F Γ(W, V) Γ(M, U) := IsScalarTower.of_algebraMap_eq' rfl
  have hftC : Algebra.FiniteType F Γ(M, U) := Algebra.FiniteType.trans hftA hftB
  obtain ⟨d, h₁, h₂⟩ := exists_ringKrullDim_eq_and_trdeg_eq F Γ(W, V)
  have hd : topologicalKrullDim (V : Set W) = d := by
    rw [← h₁, ← PrimeSpectrum.topologicalKrullDim_eq_ringKrullDim]
    exact topologicalKrullDim_eq_of_isEmbedding hV.fromSpec.isOpenEmbedding.isEmbedding
      hV.range_fromSpec
  rw [GlobalTheory.OpenDim.topologicalKrullDim_open F p V ⟨_, hx⟩] at hd
  have hB : Algebra.trdeg F Γ(M, U) = n := GlobalTheory.GenFinite.trdeg_affineOpen_eq F (f ≫ p) hU ⟨_, hy⟩ n hM
  letI := (W.evaluation V _ hx).hom.toAlgebra
  have nat : f.appLE V U e ≫ M.evaluation U _ hy =
      W.evaluation V _ hx ≫ f.residueFieldMap (genericPoint M) := by
    rw [Scheme.evaluation_naturality f _ hx, Scheme.Hom.appLE, Category.assoc]
    congr 1
    simp only [Scheme.evaluation]
    rw [← Category.assoc, TopCat.Presheaf.germ_res]
  haveI := GenFiniteEtale.isFractionRing_eval W hV hη hx
  have hinj : Function.Injective (IsScalarTower.toAlgHom F Γ(W, V) Γ(M, U)) := by
    have h₃ : Function.Injective (f.appLE V U e ≫ M.evaluation U _ hy).hom := by
      rw [nat]
      exact (f.residueFieldMap (genericPoint M)).hom.injective.comp
        (IsFractionRing.injective Γ(W, V) (W.residueField (f (genericPoint M))))
    exact Function.Injective.of_comp (f := (M.evaluation U _ hy).hom) h₃
  have hle := trdeg_le_of_injective _ hinj
  rw [h₂, hB] at hle
  exact ⟨d, by exact_mod_cast hle, hd⟩

theorem cycInt_pull : ∀ (F : Type) [Field F] (X Y : Scheme.{0}) (p : X ⟶ Sp F) (q : Y ⟶ Sp F) (σ : F →+* ℂ), IsProjOver p → IsProjOver q → ∀ (π : Y ⟶ X) (hπ : π ≫ p = q) (e : ℕ) (L : Fin e → MLine p σ) (f : CxPts p σ → ℝ), Measurable f → ∀ w : Y, topologicalKrullDim (closure ({w} : Set Y)) = e → (topologicalKrullDim (closure ({π w} : Set X)) = e → cycInt (fun i => (L i).pull π hπ) (fun y => f (ptMap π hπ σ y)) w = π.residueDegree w * cycInt L f (π w)) ∧ (topologicalKrullDim (closure ({π w} : Set X)) ≠ e → cycInt (fun i => (L i).pull π hπ) (fun y => f (ptMap π hπ σ y)) w = 0) := by
  intro F _ X Y p q σ hp hq π hπ e L f hf w hw
  obtain ⟨hIw, hgw, hdw, -⟩ := GlobalTheory.ClosFacts.clos_facts Y w
  obtain ⟨hIx, hgx, hdx, hfac⟩ := GlobalTheory.ClosFacts.clos_facts X (π w)
  have hη : (closι w ≫ π) (genericPoint (clos w)) = π w := by
    rw [Scheme.Hom.comp_apply, hgw]
  obtain ⟨g, hg, hgg, hgdeg, -⟩ := hfac (clos w) (closι w ≫ π) hη
  have hpX : IsProjOver (closι (π w) ≫ p) := isProjOver_comp hp _
  have hpY : IsProjOver (closι w ≫ q) := isProjOver_comp hq _
  have hgp : g ≫ closι (π w) ≫ p = closι w ≫ q := by
    rw [← Category.assoc, hg, Category.assoc, hπ]
  have hdY : topologicalKrullDim (clos w) = e := hdw.trans hw
  let L' : Fin e → MLine (closι (π w) ≫ p) σ := fun i => (L i).pull (closι (π w)) rfl
  let f' : CxPts (closι (π w) ≫ p) σ → ℝ := fun y => f (ptMap (closι (π w)) rfl σ y)
  have hf' : Measurable f' := hf.comp (PtsOver.continuous_map _ _ _).measurable

  have h1 : (closι w ≫ π) ≫ p = closι w ≫ q := by rw [Category.assoc, hπ]
  have h2 : (g ≫ closι (π w)) ≫ p = closι w ≫ q := by rw [Category.assoc, hgp]
  have hpart : ∀ ε : ℤˣ, part (fun i => ((L i).pull π hπ).pull (closι w) rfl) ε = part (fun i => (L' i).pull g hgp) ε := by
    intro ε
    have c1 := (GlobalTheory.Mix.isom_calculus F X Y p q σ π hπ).2.2.2.2.2 (clos w) (closι w ≫ q) (closι w) rfl h1
    have c2 := (GlobalTheory.Mix.isom_calculus F X (clos (π w)) p (closι (π w) ≫ p) σ (closι (π w)) rfl).2.2.2.2.2 (clos w)
      (closι w ≫ q) g hgp h2
    have e1 := GlobalTheory.Mix.part_eq_of_isom F (clos w) (closι w ≫ q) σ hpY e _ _ (fun i => c1 (L i)) ε
    have e2 := GlobalTheory.Mix.part_eq_of_isom F (clos w) (closι w ≫ q) σ hpY e _ _ (fun i => c2 (L i)) ε
    rw [e1, e2]
    congr 1
    funext i
    exact pull_congr _ hg.symm _ _
  have hfun : (fun y => (fun y => f (ptMap π hπ σ y)) (ptMap (closι w) rfl σ y)) = fun y => f' (ptMap g hgp σ y) := by
    funext y
    show f _ = f _
    congr 1
    apply Subtype.ext
    simp only [PtsOver.map_val, Category.assoc, hg]
  have hint : cycInt (fun i => (L i).pull π hπ) (fun y => f (ptMap π hπ σ y)) w =
      Mix.int (fun i => (L' i).pull g hgp) (fun y => f' (ptMap g hgp σ y)) := by
    simp only [cycInt, Mix.int]
    rw [hfun, hpart 1, hpart (-1)]
  refine ⟨fun hX => ?_, fun hX => ?_⟩
  · have hdX : topologicalKrullDim (clos (π w)) = e := hdx.trans hX
    have hne := GlobalTheory.DominantProjDegree.residueDegree_ne_zero_of_map_genericPoint F (clos (π w)) (clos w)
      (closι (π w) ≫ p) (closι w ≫ q) e hpX hpY hdX hdY g hgp hgg
    have hpush := (_root_.GlobalTheory.PushInt.mixInt_pull F (clos (π w)) (clos w) (closι (π w) ≫ p) (closι w ≫ q) σ e hpX hdX hpY g hgp
      hgg hne L' f' hf').2
    have hdeg : g.residueDegree (genericPoint (clos w)) = π.residueDegree w := by
      rw [hgdeg, GlobalTheory.CurveDegreesCompare.residueDegree_comp, GlobalTheory.ProperCut.residueDegree_of_isClosedImmersion (closι w),
        mul_one, hgw]
    rw [hint, hpush, hdeg]
    rfl
  · obtain ⟨m, hm, hdX⟩ := dim_le_of_dominant F (clos (π w)) (clos w) (closι (π w) ≫ p) (closι w ≫ q) hpX hpY g hgp
      hgg e hdY
    have hlt : m < e := lt_of_le_of_ne hm fun h => hX (by rw [← hdx, hdX, h])
    have h0 := _root_.GlobalTheory.MixDrop.part_pull_eq_zero F (clos (π w)) (clos w) (closι (π w) ≫ p) (closι w ≫ q) σ e m hlt hpX hdX hpY g hgp hgg L'
    rw [hint]
    simp only [Mix.int, h0, integral_zero_measure, sub_zero]

end GlobalTheory.CycPush
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MixedChernMeasureFiniteIntegrableProjective
section
set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace Set Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.R
open GlobalTheory GlobalTheory.Cartier GlobalTheory.CxPts GlobalTheory.Points GlobalTheory.CechPic GlobalTheory.ChartGlue GlobalTheory.Mix

namespace GlobalTheory.MixFin

theorem finite_and_intg : GlobalTheory.Published.Principalisation → ∀ (F : Type) [Field F] (X : Scheme.{0}) [IsIntegral X] [IsLocallyNoetherian X] (p : X ⟶ Sp F) (σ : F →+* ℂ) (D : ℕ), IsProjOver p → topologicalKrullDim X = (D : ℕ) → ∀ (L : Fin D → MLine p σ), (∀ ε : ℤˣ, IsFiniteMeasure (part L ε)) ∧ ∀ f : CxPts p σ → ℝ, Continuous f → Intg L f := by
  intro hP F _ X _ _ p σ D hX hdim L
  haveI : CharZero F := RingHom.charZero σ
  obtain ⟨Y, hY, π, hsm, hproj, -, hgen, hdeg, -⟩ :=
    _root_.GlobalTheory.LogResProj.exists_logResolution hP F X p D hX hdim ⊥ (fun h => by rwa [← SetLike.mem_coe, Closeds.coe_bot] at h)
  haveI := hY
  haveI : SmoothOfRelativeDimension D (π ≫ p) := hsm
  haveI := CxPts.compactSpace (p := π ≫ p) σ hproj
  haveI := CxPts.t2Space_cxPts_of_isProjOver (p := π ≫ p) σ hproj
  haveI := CxPts.secondCountableTopology_of_isProjOver (p := π ≫ p) σ hproj
  let R := AnRead.all (π ≫ p) σ D
  have key : ∀ f : CxPts p σ → ℝ, Continuous f → Intg L f := by
    intro f hf
    have hf' : Continuous (fun y => f (ptMap π rfl σ y)) := hf.comp (PtsOver.continuous_map _ _ _)
    have h1 := (GlobalTheory.T.mixedChernIntegral_eq_mongeAmpereIntegral_compact F Y (π ≫ p) σ D R.finAtlas R.isAlgAtlas_finAtlas
      (fun i => (L i).pull π rfl) _ hf'.measurable).1
    have hI := h1.2 (mIntegrableCont _ _ (fun i => Weight.isPotential_locPot
      ((Weight.isCInf_iff_isSmooth R).1 ((L i).pull π rfl).cInf)) _ hf')
    exact ((_root_.GlobalTheory.PushInt.mixInt_pull F X Y p (π ≫ p) σ D hX hdim hproj π rfl hgen
      (by rw [hdeg]; exact one_ne_zero) L f hf.measurable).1).1 hI
  refine ⟨fun ε => ?_, key⟩
  have h := key (fun _ => (1 : ℝ)) continuous_const
  rcases Int.units_eq_one_or ε with rfl | rfl
  · exact (integrable_const_iff.1 h.1).resolve_left one_ne_zero
  · exact (integrable_const_iff.1 h.2).resolve_left one_ne_zero

end GlobalTheory.MixFin
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MumfordBundleIsoAlongHomsDescendsAbelianPart
section
noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT GlobalTheory.Mum GlobalTheory.Mum.Two


open GlobalTheory.HomMum in
theorem GlobalTheory.HomMum.lbIso_descends : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] [CharZero R], AdmBase R (maximalIdeal R) → ∀ (D₁ D₂ : DegData R (maximalIdeal R)) (A₁ A₂ : PolAV (Sp (FractionRing R))) (G₁ G₂ : Over (Sp R)) [GrpObj G₁] [IsCommMonObj G₁] [GrpObj G₂] [IsCommMonObj G₂], IsSemiAbelian G₁ → IsSemiAbelian G₂ → ∀ (U₁ : Unif (maximalIdeal R) D₁ A₁ G₁) (U₂ : Unif (maximalIdeal R) D₂ A₂ G₂) (f g : G₁ ⟶ G₂) (fB gB : D₁.toPre.P.A ⟶ D₂.toPre.P.A), IsMonHom f → IsMonHom g → IsMonHom fB → IsMonHom gB → Over₀ U₁.toUnifPre U₂.toUnifPre f fB → Over₀ U₁.toUnifPre U₂.toUnifPre g gB → LBIso (abelian₂ G₁ U₁.LG.L) ((abelian₂ G₂ U₂.LG.L).pull (lift (fst G₁ G₁ ≫ f) (snd G₁ G₁ ≫ g) : G2 G₁ ⟶ G2 G₂).left) → LBIso (abelian₂ D₁.toPre.P.A D₁.toPre.P.L) ((abelian₂ D₂.toPre.P.A D₂.toPre.P.L).pull (lift (fst D₁.toPre.P.A D₁.toPre.P.A ≫ fB) (snd D₁.toPre.P.A D₁.toPre.P.A ≫ gB) : G2 D₁.toPre.P.A ⟶ G2 D₂.toPre.P.A).left) := by
  intro R _ _ _ _ hR D₁ D₂ A₁ A₂ G₁ G₂ _ _ _ _ hG₁ hG₂ U₁ U₂ f g fB gB _ _ _ _ of og H
  have hGF := GlobalTheory.firstFiveLaws.1.globalFns
  obtain ⟨-, -, -, hC⟩ := hR
  have := hG₁.geomConnected
  haveI : Nonempty G₁.left := ⟨eSec G₁ (⊥ : PrimeSpectrum R)⟩
  haveI : Nonempty G₂.left := ⟨eSec G₂ (⊥ : PrimeSpectrum R)⟩
  obtain ⟨w, hw⟩ := H
  obtain ⟨t, ht, -⟩ := exists_gen_of_iso (isPart_inr U₁.LG.L U₂.LG.L) (isPart_inl U₁.LG.L U₂.LG.L) w hw
  have hN := join_isLB U₁.LG.isLB U₂.LG.isLB
  obtain ⟨u, hu⟩ := _root_.GlobalTheory.HomMum.exists_isNrm hN f g t ht
  have sj := (FamGerm.surjective_appTop_sq_cube U₁.toUnifPre).2
  have hP : AbLaw.IsProjBy D₁.toPre.P.A.hom := AbProj.isProjBy_of_isPullback D₁.toPre.P (IsPullback.id_horiz _)
  obtain ⟨V, hV, t', ht'⟩ := GlobalTheory.EndRosati.loc_gen_of_thickenings hGF (maximalIdeal R) _
    (AbelianSchemeGerms.isAbelianScheme_tensor _ _ D₁.toPre.P.isAb D₁.toPre.P.isAb)
    (AbLaw.isProjBy_tensor R _ _ hP hP) (jn_isLB D₁.toPre D₂.toPre) (mφ D₁.toPre.P.A D₂.toPre.P.A fB gB) mε
    (fun e => by
      have := EndTorus.connectedSpace_thickening (maximalIdeal R) e
      have : GeometricallyConnected (thickObj R (maximalIdeal R) e G₁).hom :=
        inferInstanceAs (GeometricallyConnected (pullback.snd G₁.hom (thick R (maximalIdeal R) e)))
      have : ConnectedSpace (thickObj R (maximalIdeal R) e G₁).left :=
        GroupConn.connectedSpace_of_section (thickObj R (maximalIdeal R) e G₁).hom
          (η : 𝟙_ _ ⟶ thickObj R (maximalIdeal R) e G₁).left (Over.w _)
      exact _root_.GlobalTheory.HomMum.exists_gen_level U₁.toUnifPre U₂.toUnifPre e (of e) (og e) u hu
        fun T z J hJ x x' y => _root_.GlobalTheory.HomMumAdd.pair_add_of_surj U₁.cubG U₂.cubG hN sj f g u hu T z J hJ x x' y) (closedPoint R)
  have hall : ∀ p : PrimeSpectrum R, p ∈ V := fun p =>
    ((PrimeSpectrum.le_iff_specializes p (closedPoint R)).1 (le_maximalIdeal p.isPrime.ne_top)).mem_open V.isOpen hV
  obtain ⟨t'', ht'', -⟩ := glue_gen (jn_isLB D₁.toPre D₂.toPre) (mφ D₁.toPre.P.A D₂.toPre.P.A fB gB) mε
    (fun _ : Unit => (D₁.toPre.P.A ⊗ D₁.toPre.P.A).hom ⁻¹ᵁ V) (fun y => ⟨(), hall _⟩) (fun _ => t') (fun _ => ht')
    (fun _ _ Z r r' z J _ h => by
      obtain rfl := (cancel_mono _).1 h
      rfl)
  obtain ⟨w', hw', -⟩ := exists_iso_of_gen (isPart_inr D₁.toPre.P.L D₂.toPre.P.L) (isPart_inl D₁.toPre.P.L D₂.toPre.P.L)
    D₂.toPre.P.isLB D₁.toPre.P.isLB (snd_surjective D₁.toPre.P.isLB) (fst_surjective D₂.toPre.P.isLB) t'' ht''
  exact ⟨w', hw'⟩
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.NegOneLeftCompSelf
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.HTLat GlobalTheory.Published.AbVarRed GlobalTheory.CechPic GlobalTheory.AV GlobalTheory.AV.AbVar
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.AV.AbVar

theorem neg_one_left_comp_self {K : Type} [Field K] (A : AbVar K) :
    (Hom.hom (-(𝟙 A))).left ≫ (Hom.hom (-(𝟙 A))).left = 𝟙 A.X.left := by
  have h : (-(𝟙 A)) ≫ (-(𝟙 A)) = 𝟙 A := by
    rw [Preadditive.neg_comp, Preadditive.comp_neg, neg_neg, Category.id_comp]
  have h2 := congrArg (fun g : A ⟶ A => (Hom.hom g).left) h
  simpa only [comp_hom, Over.comp_left, id_hom, Over.id_left] using h2

theorem exists_symm_ample :
    ∀ (K : Type) [Field K] (A : AbVar K), ∃ c : Pic A.X.left, IsAmpleCls c ∧ CechPic.pull (Hom.hom (-(𝟙 A))).left c = c := by
  intro K _ A
  obtain ⟨c₀, hc₀⟩ := _root_.GlobalTheory.AV.exists_isAmpleCls K A
  set f : A.X.left ⟶ A.X.left := (Hom.hom (-(𝟙 A))).left with hf
  have hff : f ≫ f = 𝟙 A.X.left := neg_one_left_comp_self A
  have hiso : IsIso f := ⟨⟨f, hff, hff⟩⟩
  have hfin : IsFinite (Hom.hom (-(𝟙 A))).left := by
    rw [← hf]; infer_instance
  refine ⟨c₀ + CechPic.pull f c₀, _root_.GlobalTheory.AV.isAmpleCls_add K A _ _ hc₀ (_root_.GlobalTheory.AV.AbVar.isAmpleCls_pull_of_isFinite K A A (-(𝟙 A)) c₀ hfin hc₀), ?_⟩
  rw [map_add (f := _), ← CechPic.pull_comp, hff, CechPic.pull_id, add_comm]

end GlobalTheory.AV.AbVar
end

