module

public import Mathlib
public import Development.AutomorphicSpectrum.Statements.GeometryStatements.Bundle0001
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle0005
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle0004
public import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.LatNormGrLatNeZeroOfSpan
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0001
public import Development.WeilBound.CoreStatements.HodgeTatePoints.Bundle0035
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.LatticeFlagVectorBundle
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0046
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0022
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle0011
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Bundle0017
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0052
public import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.Bundle0023
public import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.Bundle0004
public import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.Bundle0001
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.StatementsBundles
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Bundle0025
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0054
public import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.Bundle0002
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.BundleObjects
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0024
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0021
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0026
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsFlatAnIffIsConstMul
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0010
public import Formalism.LocalToGlobal.ProjectiveLattices.RulInst
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle0010
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0038
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0019
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle0002

@[expose] public section

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.FlagModelStatementHolds
section
noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.FlagModel

open AlgebraicGeometry CategoryTheory GlobalTheory.CompanionTheory.Ar

variable {X X' : Scheme.{0}} {Ω : Type} [Field Ω] {ξ : Spec (CommRingCat.of Ω) ⟶ X}
  {E E' : Type} [AddCommGroup E] [Module Ω E] [AddCommGroup E'] [Module Ω E']

theorem pull_map (L : Lat ξ E) (ξ' : Spec (CommRingCat.of Ω) ⟶ X') (f : X' ⟶ X) (φ : E →ₗ[Ω] E') :
    (L.map φ).pull ξ' f (AddMonoidHom.id E') = (L.pull ξ' f (AddMonoidHom.id E)).map φ := by
  funext p'
  simp only [Lat.pull, Lat.map, Submodule.map_span]
  congr 1
  ext e'
  constructor
  · rintro ⟨h, e, he, rfl⟩
    obtain ⟨u, hu, rfl⟩ := Submodule.mem_map.1 he
    exact ⟨u, ⟨h, u, hu, rfl⟩, rfl⟩
  · rintro ⟨u, ⟨h, v, hv, huv⟩, rfl⟩
    exact ⟨h, φ v, Submodule.mem_map.2 ⟨v, hv, rfl⟩, congrArg φ huv⟩

theorem pull_vb {L : Lat ξ E} {g : ℕ} {W : Submodule Ω E} (hL : L.IsVB g W) {ξ' : Spec (CommRingCat.of Ω) ⟶ X'}
    {f : X' ⟶ X} (hd : Dominates ξ' ξ f (RingHom.id Ω)) : (L.pull ξ' f (AddMonoidHom.id E)).IsVB g W := by
  intro p' _
  obtain ⟨h, -⟩ := RegAtDom.regAt_dominates _ _ _ _ _ _ _ _ hd p'
  obtain ⟨U, hU, b, hW, hb⟩ := hL ⟨f p'.1, h⟩ (Set.mem_univ _)
  refine ⟨f ⁻¹ᵁ U, hU, b, hW, fun q' _ hq' => ?_⟩
  obtain ⟨hq, hreg, -⟩ := RegAtDom.regAt_dominates _ _ _ _ _ _ _ _ hd q'
  obtain ⟨hli, hsp⟩ := hb ⟨f q'.1, hq⟩ (Set.mem_univ _) hq'
  refine ⟨hli, le_antisymm ?_ ?_⟩
  · refine Submodule.span_le.2 ?_
    rintro e' ⟨h', e, he, he'⟩
    have he2 : e ∈ Submodule.span (regAt ξ ⟨f q'.1, hq⟩) (Set.range b) := hsp ▸ he
    have hee : e' = e := he'
    rw [hee]
    clear he he' hee
    induction he2 using Submodule.span_induction with
    | mem u hu => exact Submodule.subset_span hu
    | zero => exact Submodule.zero_mem _
    | add u v _ _ hu hv => exact Submodule.add_mem _ hu hv
    | smul c u _ hu => exact Submodule.smul_mem _ (⟨c.1, hreg c.1 c.2⟩ : regAt ξ' q') hu
  · refine Submodule.span_mono ?_
    intro e he
    exact ⟨hq, e, hsp ▸ Submodule.subset_span he, rfl⟩

theorem coh_map {L : Lat ξ E} {g : ℕ} {W : Submodule Ω E} (hL : L.IsVB g W) (φ : E →ₗ[Ω] E') :
    (L.map φ).IsCohOn Set.univ := by
  intro p hp
  obtain ⟨U, hU, b, -, hb⟩ := hL p hp
  refine ⟨U, hU, g, φ ∘ b, fun q hq hqU => ?_⟩
  simp only [Lat.map]
  rw [(hb q hq hqU).2, Submodule.map_span, Set.range_comp]
  rfl

theorem span_map {L : Lat ξ E} {g : ℕ} {W : Submodule Ω E} (hL : L.IsVB g W) (φ : E →ₗ[Ω] E') (p : Cpt ξ) :
    Submodule.span Ω ((L.map φ) p : Set E') = W.map φ := by
  obtain ⟨U, hU, b, hW, hb⟩ := hL p (Set.mem_univ p)
  simp only [Lat.map]
  rw [(hb p (Set.mem_univ p) hU).2, Submodule.map_span, Submodule.span_span_of_tower, ← hW, Submodule.map_span]
  rfl

theorem flagStep_min {r : ℕ} (b₀ : Fin r → E) (n : ℕ) : flagStep Ω b₀ (min n r) = flagStep Ω b₀ n := by
  unfold flagStep
  congr 2
  ext k
  have := k.2
  simp only [Set.mem_setOf_eq]
  omega

theorem flagStep_le {r : ℕ} {b₀ : Fin r → E} {W : Submodule Ω E} (h : ∀ k, b₀ k ∈ W) (n : ℕ) :
    flagStep Ω b₀ n ≤ W := by
  unfold flagStep
  rw [Submodule.span_le]
  rintro _ ⟨k, -, rfl⟩
  exact h k

theorem flagModel : FlagModelStatement := by
  intro o _ _ Ω _ _ κ _ x M A _ κa _ w S _ E _ _ L g r W b₀ hw hL hb hbW
  obtain ⟨p₀⟩ : Nonempty (Cpt M.ξ) := ⟨⟨genPt M.ξ, specializes_rfl⟩⟩
  haveI hfin : ∀ σ, FiniteDimensional Ω (W σ) := fun σ => by
    obtain ⟨U, -, b, hW, -⟩ := hL σ p₀ (Set.mem_univ _)
    rw [← hW]
    exact FiniteDimensional.span_of_finite Ω (Set.finite_range b)
  obtain ⟨κ', hκ', y, M', f, hdom, hnorm, hchart, hvb, hat⟩ :=
    _root_.PositivityTheory.HtPt.Mb.top_common o Ω κ x M A κa w (Σ σ, Fin (r σ + 1))
      (fun q => E ⧸ flagStep Ω (b₀ q.1) q.2)
      (fun q => (L q.1).map (flagStep Ω (b₀ q.1) q.2).mkQ)
      (fun q => (W q.1).map (flagStep Ω (b₀ q.1) q.2).mkQ) hw
      (fun q => coh_map (hL q.1) _) (fun q p => span_map (hL q.1) _ p)
  have hpull : ∀ σ, ((L σ).pull M'.ξ f (AddMonoidHom.id E)).IsVBOn Set.univ (g σ) (W σ) :=
    fun σ => pull_vb (hL σ) hdom
  have hquot : ∀ σ (n : ℕ), ∃ s W', (((L σ).pull M'.ξ f (AddMonoidHom.id E)).map
      (flagStep Ω (b₀ σ) n).mkQ).IsVBOn Set.univ s W' := fun σ n => by
    rw [← flagStep_min]
    have h := hvb ⟨σ, ⟨min n (r σ), Nat.lt_succ_of_le (min_le_right _ _)⟩⟩
    rw [pull_map] at h
    exact ⟨_, _, h⟩
  refine ⟨κ', hκ', y, M', f, hdom, hnorm, hchart, fun σ => ?_, fun σ n p' => ?_, fun p hp hfr => ?_⟩
  · exact _root_.GlobalTheory.CompanionTheory.Ar.isFlagVBOn_inter_of_steps _ _ _ _ _ _ _ _ _ _ (hb σ) (hbW σ) (hpull σ) (hquot σ)
  · obtain ⟨s, W', h⟩ := hquot σ n
    exact (_root_.GlobalTheory.CompanionTheory.Ar.inter_isVBOn_of_map _ _ _ _ _ _ _ _ _ _ _ (flagStep_le (hbW σ) n) (hpull σ) h).2 p' (Set.mem_univ _)
  · exact hat p hp fun q => hfr q.1 q.2

end GlobalTheory.CompanionTheory.Ar.FlagModel
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.FlagPairChartBundleCompat
section
open AlgebraicGeometry CategoryTheory NumberField MvPolynomial ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Num GlobalTheory.CompanionTheory.Ar.Top GlobalTheory.CompanionTheory.Ar.Num.HodgeModel
open GroundTheory.Heights₂.Heights.NumbersDVR (pointIdeal segreVec IsFlagFrame IsFlagPair SameGenericFibre IsModelOver divCycle)
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.NumbersDVR.Bundles (mseg fnField)

namespace GlobalTheory.CompanionTheory.Ar.Num.HodgeModel.DualPair

open GroundTheory.Heights₂.Heights.NumbersDVR (IsVerticalDivisor ratDiv)

theorem mem_dualBundle {O : Type} [CommRing O] {Ω : Type} [Field Ω] [Algebra O Ω] {r : ℕ}
    (R : Subalgebra O Ω) (L : AddSubgroup (Fin r → Ω)) (e : Fin r → Ω) :
    e ∈ dotDual R L ↔ ∀ l ∈ L, l ⬝ᵥ e ∈ R := by
  simp [dotDual, AddSubgroup.mem_iInf]

def dualBundle {O : Type} [CommRing O] {Ω : Type} [Field Ω] [Algebra O Ω] {ι : Type} {x : ι → Ω} {r : ℕ}
    (B : ChartBundle O x r (Fin r → Ω)) : ChartBundle O x r (Fin r → Ω) where
  lat c := dotDual (chartRing O x c) (B.lat c)
  stable c a ha e he := by
    rw [mem_dualBundle] at he ⊢
    intro l hl
    rw [dotProduct_smul, smul_eq_mul]
    exact mul_mem ha (he l hl)
  frame := _root_.GlobalTheory.CompanionTheory.Ar.Num.chartBundle_dotDual_localFrame O Ω ι x r B (_root_.GlobalTheory.CompanionTheory.Ar.Geo.chartBundle_lat_fg O Ω ι x r B)
  overlap := _root_.GlobalTheory.CompanionTheory.Ar.Num.dotDual_overlap O Ω ι x r B.lat B.stable B.overlap (_root_.GlobalTheory.CompanionTheory.Ar.Geo.chartBundle_lat_fg O Ω ι x r B)

def dotForm (Ω : Type) [Field Ω] (r : ℕ) : (Fin r → Ω) →ₗ[Ω] (Fin r → Ω) →ₗ[Ω] Ω :=
  LinearMap.mk₂ Ω (fun a b => a ⬝ᵥ b) add_dotProduct (fun c a b => smul_dotProduct c a b) dotProduct_add
    (fun c a b => dotProduct_smul c a b)

theorem dotForm_apply (Ω : Type) [Field Ω] (r : ℕ) (a b : Fin r → Ω) : dotForm Ω r a b = a ⬝ᵥ b := rfl

theorem dotForm_flip_bijective (Ω : Type) [Field Ω] (r : ℕ) : Function.Bijective (dotForm Ω r).flip := by
  have hinj : Function.Injective (dotForm Ω r).flip := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro b hb
    funext q
    have := LinearMap.congr_fun hb (Pi.single q 1)
    simpa [dotForm_apply, single_one_dotProduct] using this
  refine ⟨hinj, ?_⟩
  exact (LinearMap.injective_iff_surjective_of_finrank_eq_finrank
    (by simp [Subspace.dual_finrank_eq])).1 hinj

theorem isVerticalDivisor_swap {K : Type} [DecidableEq K] {ι : K → Type} {O : Type} [CommRing O]
    {P : Ideal (MvPolynomial (Σ k, ι k) O)} {ϖ : O} {b : K → ℤ} {f g : MvPolynomial (Σ k, ι k) O}
    (h : IsVerticalDivisor P ϖ b f g) : IsVerticalDivisor P ϖ (-b) g f := by
  refine ⟨?_, h.den_not_mem, h.num_not_mem, ?_, ?_⟩
  · obtain ⟨bf, bg, hf, hg, hb⟩ := h.degrees
    refine ⟨bg, bf, hg, hf, ?_⟩
    rw [← hb]
    funext k
    simp
  · intro W hW
    apply h.vertical W
    unfold ratDiv at hW ⊢
    exact fun h0 => hW (sub_eq_zero.mpr (sub_eq_zero.mp h0).symm)
  · intro W hp hPW hrel hϖ
    obtain ⟨u, v, hu, hv, h1⟩ := h.unit_off_special W hp hPW hrel hϖ
    refine ⟨v, u, hv, hu, ?_⟩
    rw [← neg_sub]
    exact P.neg_mem h1

theorem dualPair : ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (Ω : Type) [Field Ω]
    [Algebra O Ω] (K : Type) [Fintype K] [DecidableEq K] (J : K → Type) [∀ k, Fintype (J k)] (y : (Σ k, J k) → Ω)
    (ϖ : O) (r : ℕ) (B B' : ChartBundle O (segreVec y) r (Fin r → Ω)) (w w' : Module.Basis (Fin r) Ω (Fin r → Ω))
    (x x' : Fin r → K → ℤ) (f g : Fin r → MvPolynomial (Σ k, J k) O), IsFlagPair ϖ y B B' w w' x x' f g →
    ∃ (C C' : ChartBundle O (segreVec y) r (Fin r → Ω)) (v v' : Module.Basis (Fin r) Ω (Fin r → Ω)),
      (∀ c, segreVec y c ≠ 0 → C.lat c = dotDual (chartRing O (segreVec y) c) (B.lat c) ∧
        C'.lat c = dotDual (chartRing O (segreVec y) c) (B'.lat c)) ∧
      IsFlagPair ϖ y C C' v v' (fun i => -x (Fin.rev i)) (fun i => -x' (Fin.rev i)) (fun i => g (Fin.rev i))
        (fun i => f (Fin.rev i)) := by
  intro O _ _ _ Ω _ _ K _ _ J _ y ϖ r B B' w w' x x' f g h
  obtain ⟨v, hv⟩ := _root_.GlobalTheory.CompanionTheory.Ar.DualRev.dotDualRevBasis Ω r w
  obtain ⟨v', hv'⟩ := _root_.GlobalTheory.CompanionTheory.Ar.DualRev.dotDualRevBasis Ω r w'
  obtain ⟨htri, hdiag⟩ := _root_.GlobalTheory.CompanionTheory.Ar.DualPair.dualRevTri Ω r w w' v v' hv hv' h.sameFlag
  have hdual : ∀ B₀ : ChartBundle O (segreVec y) r (Fin r → Ω),
      IsDualLat O y (dotForm Ω r) B₀.lat (dualBundle B₀).lat := by
    intro B₀
    refine ⟨dotForm_flip_bijective Ω r, fun s _ e => ?_⟩
    exact mem_dualBundle _ _ _
  refine ⟨dualBundle B, dualBundle B', v, v', fun c _ => ⟨rfl, rfl⟩, ?_⟩
  refine ⟨?_, ?_, htri, fun i => ?_, fun i => ?_⟩
  · exact _root_.GlobalTheory.CompanionTheory.Ar.Num.FlagDual.main O Ω K J y r (Fin r → Ω) (Fin r → Ω) B (dualBundle B) (dotForm Ω r) (hdual B) w x h.flag v
      (fun i j => by rw [dotForm_apply]; exact hv i j)
  · exact _root_.GlobalTheory.CompanionTheory.Ar.Num.FlagDual.main O Ω K J y r (Fin r → Ω) (Fin r → Ω) B' (dualBundle B') (dotForm Ω r) (hdual B') w' x'
      h.flag' v' (fun i j => by rw [dotForm_apply]; exact hv' i j)
  · have := isVerticalDivisor_swap (h.vertical i.rev)
    convert this using 1
    ring
  · show aeval y (g i.rev) = v.repr (v' i) i * aeval y (f i.rev)
    rw [h.generic i.rev, ← mul_assoc, hdiag i, one_mul]

end GlobalTheory.CompanionTheory.Ar.Num.HodgeModel.DualPair
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.FrameBorelChangeVectors
section
open AlgebraicGeometry CategoryTheory Limits NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl GlobalTheory.CompanionTheory.Ar.Flat

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Flat.FrameTri

open MonoidalCategory CartesianMonoidalCategory MonObj

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {l : Level H}

theorem comp_list_prod {B : Scheme.{0}} {G T T' : Over B} [GrpObj G] (f : T' ⟶ T) (L : List (T ⟶ G)) :
    f ≫ L.prod = (L.map fun a => f ≫ a).prod := by
  induction L with
  | nil => simpa using MonObj.comp_one f
  | cons a L ih => rw [List.prod_cons, List.map_cons, List.prod_cons, MonObj.comp_mul, ih]

theorem dualMap_comp_algebraMap {S F : Type} [CommRing S] [CommRing F] (ψ : S →+* F) :
    (Formalism.L2.Pj.dualMap ψ).comp (algebraMap S (DualNumber S)) = (algebraMap F (DualNumber F)).comp ψ := by
  ext s <;> simp [Formalism.L2.Pj.dualMap, TrivSqZeroExt.algebraMap_eq_inl]

theorem dualMap_comp_epsMul' {S F : Type} [CommRing S] [CommRing F] (ψ : S →+* F) (a : S) :
    (Formalism.L2.Pj.dualMap ψ).comp (ReciprocityTheory.ChartRestriction.G.Geo.Tor.epsMul a) =
      (GlobalTheory.CompanionTheory.Ar.epsMul (ψ a)).comp (Formalism.L2.Pj.dualMap ψ) := by
  ext s <;> simp [Formalism.L2.Pj.dualMap, ReciprocityTheory.ChartRestriction.G.Geo.Tor.epsMul, GlobalTheory.CompanionTheory.Ar.epsMul,
    TrivSqZeroExt.algebraMap_eq_inl]

theorem isComb_of_isCombAt {Xo : Moduli D l} {S F : Type} [CommRing S] [CommRing F] (ψ : S →+* F)
    {x : Sp S ⟶ Xo.X} {x' : Sp F ⟶ Xo.X} (hx : x' = spMap ψ ≫ x) {m : ℕ}
    {vS : Fin m → (Sp (DualNumber S) ⟶ Xo.univ.t.G.left)} {cf : Fin m → S}
    {wS : Sp (DualNumber S) ⟶ Xo.univ.t.G.left} (h : Formalism.L2.Pj.IsCombAt x vS cf wS)
    {v : Fin m → (epsAt x' ⟶ Xo.univ.t.G)} {w : epsAt x' ⟶ Xo.univ.t.G}
    (hv : ∀ i, (v i).left = spMap (Formalism.L2.Pj.dualMap ψ) ≫ vS i)
    (hw : w.left = spMap (Formalism.L2.Pj.dualMap ψ) ≫ wS) :
    Fl.IsComb (fun i => ψ (cf i)) v w := by
  subst hx
  obtain ⟨u, hu, hp⟩ := h
  have hf : spMap (Formalism.L2.Pj.dualMap ψ) ≫ (Formalism.L2.Pj.tEps x).hom = (epsAt (spMap ψ ≫ x)).hom := by
    show spMap (Formalism.L2.Pj.dualMap ψ) ≫ spMap (algebraMap S (DualNumber S)) ≫ x =
      Spec.map (CommRingCat.ofHom (algebraMap F (DualNumber F))) ≫ spMap ψ ≫ x
    rw [← Category.assoc, ← Category.assoc]
    congr 1
    rw [← Spec.map_comp, ← Spec.map_comp, ← CommRingCat.ofHom_comp, ← CommRingCat.ofHom_comp,
      dualMap_comp_algebraMap]
  let f : epsAt (spMap ψ ≫ x) ⟶ Formalism.L2.Pj.tEps x := Over.homMk (spMap (Formalism.L2.Pj.dualMap ψ)) hf
  refine ⟨fun i => f ≫ u i, fun i => ?_, ?_⟩
  · show spMap (Formalism.L2.Pj.dualMap ψ) ≫ (u i).left = _
    rw [hu i, hv i, ← Category.assoc, ← Category.assoc]
    congr 1
    rw [← Spec.map_comp, ← Spec.map_comp, ← CommRingCat.ofHom_comp, ← CommRingCat.ofHom_comp,
      dualMap_comp_epsMul']
  · have e : (List.ofFn fun i => f ≫ u i) = (List.ofFn u).map fun a => f ≫ a := by
      rw [List.map_ofFn]; rfl
    rw [e, ← comp_list_prod]
    apply Over.OverMorphism.ext
    rw [hw, ← hp]
    rfl

theorem exists_matrix {Xo : Moduli D l} {S F : Type} [CommRing S] [Field F] (ψ : S →+* F)
    {x : Sp S ⟶ Xo.X} {x' : Sp F ⟶ Xo.X} (hx : x' = spMap ψ ≫ x) {m n : ℕ} (hn : n = m)
    {u u' : Fin m → (Sp (DualNumber S) ⟶ Xo.univ.t.G.left)} (d : Fin m → S)
    (h : ∀ i, ∃ cf : Fin m → S, cf i = d i ∧ (∀ j, i < j → cf j = 0) ∧ Formalism.L2.Pj.IsCombAt x u cf (u' i))
    {v v' : Fin n → (epsAt x' ⟶ Xo.univ.t.G)}
    (hv : ∀ i, (v i).left = spMap (Formalism.L2.Pj.dualMap ψ) ≫ u (i.cast hn))
    (hv' : ∀ i, (v' i).left = spMap (Formalism.L2.Pj.dualMap ψ) ≫ u' (i.cast hn)) :
    ∃ A : Matrix (Fin n) (Fin n) F, (∀ i, Fl.IsComb (A i) v (v' i)) ∧
      A.det = ∏ i : Fin n, ψ (d (i.cast hn)) := by
  subst hn
  choose cf h1 h2 h3 using h
  refine ⟨Matrix.of fun i j => ψ (cf i j), fun i => ?_, ?_⟩
  · exact isComb_of_isCombAt ψ hx (h3 i) hv (hv' i)
  · rw [Matrix.det_of_lowerTriangular]
    · exact Finset.prod_congr rfl fun i _ => by simp [h1]
    · intro i j hij
      have : i < j := hij
      simp [h2 i j this]

theorem exists_triangular_at_field (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H)
    (l : Level H) (Xo : Moduli D l) (c : Coeff l) (τ : E →+* ℂ) (S : Type) [CommRing S] [Algebra c.F S]
    (t : Formalism.L2.Pj.Ix D → Sˣ) (z z' : Formalism.L2.Pj.FrPt Xo c S) (hb : Formalism.L2.Pj.FrBor t z z')
    (F : Type) [Field F] (ψ : S →+* F) (y : Sp F ⟶ Xo.XF c) (hp : D.mult τ = D.p)
    (hq : D.mult (ComplexEmbedding.conjugate τ) = D.q) (v v' : Vecs y D.p) (w w' : Vecs y D.q)
    (hy : under y = spMap ψ ≫ z.x)
    (hv : ∀ i, (v i).left = spMap (Formalism.L2.Pj.dualMap ψ) ≫ z.u τ (i.cast hp.symm))
    (hw : ∀ j, (w j).left = spMap (Formalism.L2.Pj.dualMap ψ) ≫ z.u (ComplexEmbedding.conjugate τ) (j.cast hq.symm))
    (hv' : ∀ i, (v' i).left = spMap (Formalism.L2.Pj.dualMap ψ) ≫ z'.u τ (i.cast hp.symm))
    (hw' : ∀ j, (w' j).left = spMap (Formalism.L2.Pj.dualMap ψ) ≫ z'.u (ComplexEmbedding.conjugate τ) (j.cast hq.symm)) :
    ∃ (A : Matrix (Fin D.p) (Fin D.p) F) (B : Matrix (Fin D.q) (Fin D.q) F),
      (∀ i, Fl.IsComb (A i) v (v' i)) ∧ (∀ j, Fl.IsComb (B j) w (w' j)) ∧
      A.det = ∏ i : Fin D.p, ψ (t (some ⟨τ, i.cast hp.symm⟩) : Sˣ) ∧
      B.det = ∏ j : Fin D.q, ψ (t (some ⟨ComplexEmbedding.conjugate τ, j.cast hq.symm⟩) : Sˣ) := by
  obtain ⟨-, hc, -⟩ := hb
  obtain ⟨A, hA, dA⟩ := exists_matrix ψ hy hp.symm (fun i => (t (some ⟨τ, i⟩) : S)) (hc τ) hv hv'
  obtain ⟨B, hB, dB⟩ := exists_matrix ψ hy hq.symm
    (fun i => (t (some ⟨ComplexEmbedding.conjugate τ, i⟩) : S)) (hc (ComplexEmbedding.conjugate τ)) hw hw'
  exact ⟨A, B, hA, hB, dA, dB⟩

end GlobalTheory.CompanionTheory.Ar.Flat.FrameTri
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.HodgeComponentIntegralOverRing
section
open CategoryTheory AlgebraicGeometry NumberField GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.HT GlobalTheory.CompanionTheory.Ar.Flat ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.NumbersDVR.Bundles

namespace GlobalTheory.CompanionTheory.Ar.Flat.HTL

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {l : Level H}
  {Xo : Moduli D l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F} {Y : Model Xo c β} {S : Finset ℕ}
  {Ω : Type} [Field Ω] {K : Type} [Fintype K] {J : K → Type} {y : (Σ k, J k) → Ω}

theorem unitAt_natCast_of_overZp (𝔐 : HodgeCpt Y S y) (p : ℕ) (q : Cpt 𝔐.ξ) (hq : OverZp 𝔐 p q) (b : ℕ)
    (hb : ¬ p ∣ b) : unitAt 𝔐.ξ q (b : Ω) := by
  induction b using Nat.recOnMul with
  | zero => exact absurd (dvd_zero p) hb
  | one =>
    rw [Nat.cast_one]
    exact ⟨one_ne_zero, one_mem _, by rw [inv_one]; exact one_mem _⟩
  | prime r hr =>
    by_contra h
    exact hb (by rw [hq r hr h])
  | mul a b iha ihb =>
    have ha := iha fun h => hb (h.mul_right b)
    have hb' := ihb fun h => hb (h.mul_left a)
    rw [Nat.cast_mul]
    exact ⟨mul_ne_zero ha.1 hb'.1, mul_mem ha.2.1 hb'.2.1, by
      rw [mul_inv]; exact mul_mem ha.2.2 hb'.2.2⟩

theorem isLocIn_regAt_chartRing : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (S : Finset ℕ) (Ω : Type) [Field Ω] (K : Type) [Fintype K] (J : K → Type) [∀ k, Fintype (J k)] (y : (Σ k, J k) → Ω) (𝔐 : HodgeCpt Y S y) (p : ℕ) [Fact p.Prime] (o : Type) [CommRing o] [Algebra o Ω] (ho : ∀ x : Ω, x ∈ (algebraMap o Ω).range ↔ ∃ (a : ℤ) (b : ℕ), ¬ p ∣ b ∧ x = (a : Ω) / (b : Ω)) (s : ∀ k, J k) (q : Cpt 𝔐.ξ), InChart 𝔐.ξ (mseg y) s q → OverZp 𝔐 p q → HTL.IsLocIn (chartRing o (mseg y) s) (regAt 𝔐.ξ q) := by
  intro E _ _ _ H D l Xo c O _ β Y S Ω _ K _ J _ y 𝔐 p _ o _ _ ho s q hs hq
  have hu := unitAt_natCast_of_overZp 𝔐 p q hq
  refine ⟨fun a => ?_, fun b hb => ?_⟩
  · obtain ⟨a, ha⟩ := a
    show a ∈ regAt 𝔐.ξ q
    refine Algebra.adjoin_induction (p := fun x _ => x ∈ regAt 𝔐.ξ q) ?_ ?_ ?_ ?_ ha
    · rintro _ ⟨j, rfl⟩
      exact hs.2 j
    · intro r
      obtain ⟨m, n, hn, e⟩ := (ho _).1 ⟨r, rfl⟩
      rw [e, div_eq_mul_inv]
      exact mul_mem (intCast_mem _ m) (hu n hn).2.2
    · intro x z _ _ hx hz
      exact add_mem hx hz
    · intro x z _ _ hx hz
      exact mul_mem hx hz
  · obtain ⟨t, ht, hut, htb⟩ := (_root_.GlobalTheory.CompanionTheory.Ar.regAt_iff_exists_chart_fraction 𝔐.X Ω 𝔐.ξ ℤ _ (mseg y) 𝔐.tie s q hs b).1 hb
    have hle : ∀ x ∈ Algebra.adjoin ℤ (Set.range fun j => mseg y j / mseg y s),
        x ∈ chartRing o (mseg y) s := by
      intro x hx
      refine Algebra.adjoin_induction (p := fun x _ => x ∈ chartRing o (mseg y) s) ?_ ?_ ?_ ?_ hx
      · rintro _ ⟨j, rfl⟩
        exact div_mem_chartRing _ _ _
      · intro n
        simp
      · intro x z _ _ hx hz
        exact add_mem hx hz
      · intro x z _ _ hx hz
        exact mul_mem hx hz
    exact ⟨⟨t, hle t ht⟩, ⟨t * b, hle _ htb⟩, hut.1, hut.2.2, rfl⟩

end GlobalTheory.CompanionTheory.Ar.Flat.HTL
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.HodgeComponentReductionAtP
section
open CategoryTheory AlgebraicGeometry NumberField GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.HT GlobalTheory.CompanionTheory.Ar.Flat ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.NumbersDVR.Bundles
namespace GlobalTheory.CompanionTheory.Ar.Flat

theorem mem_V_inr_iff_latOn : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (S : Finset ℕ) (Ω : Type) [Field Ω] (K : Type) [Fintype K] (J : K → Type) [∀ k, Fintype (J k)] (y : (Σ k, J k) → Ω) (𝔐 : HodgeCpt Y S y) (p : ℕ) [Fact p.Prime] (o : Type) [CommRing o] [Algebra o Ω] (ho : ∀ x : Ω, x ∈ (algebraMap o Ω).range ↔ ∃ (a : ℤ) (b : ℕ), ¬ p ∣ b ∧ x = (a : Ω) / (b : Ω)) (Dc : ∀ s : {s : ∀ k, J k // mseg y s ≠ 0}, HTChart (chartRing o (mseg y) s.1) Ω (cmConj E) p (𝔐.R p) (D.p + D.q) (Module.Dual Ω 𝔐.Li)), IsHTFamily 𝔐 p o Dc → p ∈ S → ∀ (τ : CMType H) (σ : E →+* Ω), (∀ a : 𝓞 E, σ (a : E) = 𝔐.emb (Sum.inl τ) a) → ∀ (s : {s : ∀ k, J k // mseg y s ≠ 0}) (q : Cpt 𝔐.ξ), InChart 𝔐.ξ (mseg y) s.1 q → InFibre 𝔐.ξ p q → ∀ e : 𝔐.Li, e ∈ 𝔐.V (Sum.inr τ) q ↔ e ∈ HTL.latOn (Dc s) (GlobalTheory.CompanionTheory.Ar.HT.eigSp 𝔐.ρ (σ.comp (cmConj E).toRingHom)) 1 (regAt 𝔐.ξ q) := by
  intro E _ _ _ H D l Xo c O _ β Y S Ω _ K _ J _ y 𝔐 p _ o _ _ ho Dc hF hpS τ σ hσ s q hs hq e
  have hp : p.Prime := Fact.out
  have hu : ∀ p' ∈ S, InFibre 𝔐.ξ p' q → p' = p := by
    intro r hrS hrq
    by_contra hne
    have hloc : IsLocalRing (regAt 𝔐.ξ q) :=
      IsLocalRing.of_surjective' (genMap 𝔐.ξ q).rangeRestrict
        (genMap 𝔐.ξ q).rangeRestrict_surjective
    have key : ∀ m : ℕ, InFibre 𝔐.ξ m q → ¬ IsUnit ((m : regAt 𝔐.ξ q)) := by
      intro m hm hu
      apply hm
      obtain ⟨u, hu'⟩ := hu
      have h1 : (m : Ω) * (((u⁻¹ : (regAt 𝔐.ξ q)ˣ) : regAt 𝔐.ξ q) : Ω) = 1 := by
        have h2 := congrArg (fun x : regAt 𝔐.ξ q => (x : Ω)) u.mul_inv
        simpa [hu'] using h2
      have h0 : (m : Ω) ≠ 0 := left_ne_zero_of_mul_eq_one h1
      refine ⟨h0, natCast_mem _ m, ?_⟩
      rw [← eq_inv_of_mul_eq_one_right h1]
      exact SetLike.coe_mem _
    have hcop : Nat.Coprime r p := (Nat.coprime_primes (𝔐.S_prime r hrS) hp).2 hne
    obtain ⟨a, b, hab⟩ := (Nat.isCoprime_iff_coprime.2 hcop).map (Int.castRingHom (regAt 𝔐.ξ q))
    rcases IsLocalRing.isUnit_or_isUnit_of_add_one hab with h | h
    · exact key r hrq (by simpa using isUnit_of_mul_isUnit_right h)
    · exact key p hq (by simpa using isUnit_of_mul_isUnit_right h)
  have hV : 𝔐.V (Sum.inr τ) q = 𝔐.M.htDual 𝔐.t.PP.L (p ^ 𝔐.R p) 𝔐.ρ (𝔐.emb (Sum.inr τ)) q := by
    unfold HodgeCpt.V
    rw [Lat.patch_of_unique _ _ _ hpS hq hu]
    rfl
  have hσ' : ∀ a : 𝓞 E, 𝔐.emb (Sum.inr τ) a = (σ.comp (cmConj E).toRingHom) (a : E) := by
    intro a
    have h1 : 𝔐.emb (Sum.inr τ) a = 𝔐.emb (Sum.inl τ) (H.bar a) := rfl
    rw [h1, ← hσ, H.bar_eq]
    rfl
  have hom := hF.om'_loc s q hs hq
  rw [hV, LieModel.mem_htDual_iff]
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨HT.LatBasic.mem_eigSp.2 fun a => ?_, fun w hw => ?_⟩
    · have := (Submodule.mem_iInf _).mp h1 a
      rw [← hσ' a]
      simpa [sub_eq_zero] using this
    · rw [one_mul]
      refine h2 w ?_
      have : w ∈ HT.omP 𝔐 p q := by
        rw [hom]
        exact Submodule.subset_span hw
      exact this
  · rintro ⟨h1, h2⟩
    refine ⟨(Submodule.mem_iInf _).mpr fun a => ?_, fun w hw => ?_⟩
    · have := HT.LatBasic.mem_eigSp.1 h1 a
      rw [← hσ' a] at this
      simpa [sub_eq_zero] using this
    · have hw' : w ∈ HT.omP 𝔐 p q := hw
      rw [hom] at hw'
      clear hw
      induction hw' using Submodule.span_induction with
      | mem x hx => simpa using h2 x hx
      | zero => simpa using (regAt 𝔐.ξ q).zero_mem
      | add x y _ _ hx hy => simpa using (regAt 𝔐.ξ q).add_mem hx hy
      | smul c x _ hx =>
        have : (c • x) e = (c : Ω) * x e := rfl
        rw [this]
        exact (regAt 𝔐.ξ q).mul_mem c.2 hx

end GlobalTheory.CompanionTheory.Ar.Flat
end

