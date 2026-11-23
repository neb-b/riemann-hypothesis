module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Degenerations.PullChartIsLB
public import Development.AbelianVarietyTheory.Proofs.ThetaFamilyOrigin.IsVVGenOfIsThetaFamily
public import Development.AbelianVarietyTheory.Proofs.ToricGeometry.Bundle0013
public import Development.AbelianVarietyTheory.Proofs.ThetaFamilyOrigin.ExistsSectionRing
public import Development.AbelianVarietyTheory.Proofs.ThetaFamilyOrigin.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.ThetaFamilyOrigin.CardZerosOnTorsionCosetLe
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0069
public import Development.AbelianVarietyTheory.Statements.TorsionEndomorphisms.ConstantThetaDeformationZero
public import Development.AbelianVarietyTheory.Statements.TorsionEndomorphisms.ExistsGeneratorOfIsField
public import Development.AbelianVarietyTheory.Proofs.ThetaFamilyOrigin.IsThetaPtOverMove
public import Development.AbelianVarietyTheory.Proofs.ThetaFamilyOrigin.Bundle0002
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.GlobalSectionsRankAlgClosed
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.WeilIsAlternatingSkewNatural
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.WeilIsGrpPullbackIff
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.HasThetaConstantsIffOfThetaLevelPullback
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0017
public import Development.AbelianVarietyTheory.Proofs.ThetaFamilyOrigin.AppLESurjective
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0091

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.ThetaFamilyOrigin.DegreeFormsDimensionAbelianConeLe
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.ZH
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.AbelianFormCount

theorem hilb_cone_le_of_span {K : Type} [Field K] {X : Scheme.{0}} (p : X ⟶ Sp K) (L : LB X) (N d m : ℕ)
    {J : Type} [Finite J] (s : J → (lbPow L N).Sec) (b : Fin m → (lbPow L (N * d)).Sec)
    (hb : ∀ t : (lbPow L (N * d)).Sec, ∃ a : Fin m → K, ∀ j, t.f j = ∑ i, constFn p _ (a i) * (b i).f j) :
    hilb (cone p (lbPow L N) s) d ≤ m := by
  have hC : ∀ v : cone p (lbPow L N) s, ∃ (x : Sp K ⟶ X) (l : PUnit → L.ι) (c : K) (_ : x ≫ p = 𝟙 _)
      (h : ⊤ ≤ x ⁻¹ᵁ SectionRing.chart L l),
      ∀ j, v.1 j = TorsionZero.val x _ h ((s j).f l) * c := by
    rintro ⟨v, x, hx, l, c, hl, hv⟩
    exact ⟨x, l, c, hx, hl, fun j => (hv j).trans ((_root_.mul_comm _ _).trans
      (congrArg (· * (c : K)) (dif_pos hl)))⟩
  choose x l c hx hl hv using hC
  let β : Fin m → cone p (lbPow L N) s → K := fun i v =>
    TorsionZero.val (x v) _ (hl v) ((b i).f (l v)) * c v ^ d
  have le : (MvPolynomial.homogeneousSubmodule J K d).map
      (LinearMap.pi fun v : cone p (lbPow L N) s => (MvPolynomial.aeval (R := K) v.1).toLinearMap) ≤
      Submodule.span K (Set.range β) := by
    rintro _ ⟨F, hF, rfl⟩
    have hm := TorsionZero.aeval_mem_of_isHomogeneous (SectionRing.secs p L)
      (x := fun j => (SectionRing.secEquiv p L N (s j) : SectionRing.Fam p L))
      (fun j => (SectionRing.secEquiv p L N (s j)).2) hF
    obtain ⟨a, ha⟩ := hb ((SectionRing.secEquiv p L (N * d)).symm ⟨_, hm⟩)
    refine (Submodule.mem_span_range_iff_exists_fun K).2 ⟨a, funext fun v => ?_⟩
    let ev : SectionRing.Fam p L →ₐ[K] K :=
      { (TorsionZero.val (x v) _ (hl v)).comp (SectionRing.evalFam p L (l v)) with
        commutes' := fun r => TorsionZero.val_const p (x v) (hx v) _ (hl v) r }
    have h1 : ev (MvPolynomial.aeval (fun j => (SectionRing.secEquiv p L N (s j) : SectionRing.Fam p L)) F) =
        ∑ i, a i * TorsionZero.val (x v) _ (hl v) ((b i).f (l v)) :=
      (congrArg (TorsionZero.val (x v) _ (hl v)) (ha (l v))).trans ((map_sum _ _ _).trans
        (Finset.sum_congr rfl fun i _ => (map_mul _ _ _).trans
          (congrArg (· * _) (TorsionZero.val_const p (x v) (hx v) _ (hl v) (a i)))))
    rw [MvPolynomial.comp_aeval_apply] at h1
    change _ = MvPolynomial.aeval v.1 F
    rw [show v.1 = _ from funext (hv v), TorsionZero.aeval_mul_of_isHomogeneous _ _ hF]
    refine Eq.trans ?_ (congrArg (· * c v ^ d) h1).symm
    rw [Finset.sum_apply, Finset.sum_mul]
    exact Finset.sum_congr rfl fun i _ => (_root_.mul_assoc _ _ _).symm
  have := Module.Finite.span_of_finite K (Set.finite_range β)
  exact (Submodule.finrank_mono le).trans ((finrank_range_le_card β).trans (Fintype.card_fin m).le)

theorem hilb_cone_le : Out.Laws → ∀ (K : Type) [Field K] [IsAlgClosed K] (P : Out.PolAV (Sp K)) (N : ℕ) (J : Type) [Fintype J] (s : J → (lbPow P.L N).Sec) (d : ℕ), 1 ≤ N → 1 ≤ d → hilb (cone P.A.hom (lbPow P.L N) s) d ≤ (N * d) ^ P.g := by
  intro h K _ _ P N J _ s d hN hd
  obtain ⟨b, hb⟩ := PowSec.exists_basis_sections h.globalSectionsRank K P (N * d) (Nat.mul_pos hN hd)
  exact hilb_cone_le_of_span P.A.hom P.L N d _ s b fun t => (hb t).exists

end GlobalTheory.AbelianFormCount
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ThetaFamilyOrigin.ExistsIsoOfEqualCoordinateCones
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.ZH
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section
namespace GlobalTheory.ZH.IsoCone
open GlobalTheory.ZH.CrdCalc GlobalTheory.ZH.ImmSep GlobalTheory.ZH.ToImm

theorem dense_points {K : Type} [Field K] [IsAlgClosed K] {Y : Scheme.{0}} (p : Y ⟶ Sp K)
    [LocallyOfFiniteType p] :
    Dense (⋃ a : {x : Sp K ⟶ Y // x ≫ p = 𝟙 _}, Set.range a.1) := by
  have : JacobsonSpace Y := LocallyOfFiniteType.jacobsonSpace p
  have hd : Dense (closedPoints Y) := by
    rw [dense_iff_closure_eq, closure_closedPoints]
  refine hd.mono fun c hc => Set.mem_iUnion.2 ⟨⟨_, pointOfClosedPoint_comp p c hc⟩,
    IsLocalRing.closedPoint K, pointOfClosedPoint_apply p c hc _⟩

theorem exists_hom {K : Type} [Field K] [IsAlgClosed K] {X Y : Scheme.{0}} [IsReduced Y] (p : X ⟶ Sp K)
    (p' : Y ⟶ Sp K) [LocallyOfFiniteType p'] {H : LB X} {H' : LB Y} {J : Type} [Fintype J] {s : J → H.Sec}
    {s' : J → H'.Sec} (hH : H.IsLB) (hH' : H'.IsLB) (hI : ImmBy p H s Set.univ) (hI' : ImmBy p' H' s' Set.univ)
    (hc : cone p' H' s' ⊆ cone p H s) :
    ∃ g : Y ⟶ X, g ≫ p = p' ∧ ∀ (R : Type) [CommRing R] [IsLocalRing R] (y : Sp R ⟶ Y) (v : J → R),
      Crd H' s' y v → Crd H s (y ≫ g) v := by
  have hx : ∀ a : {x : Sp K ⟶ Y // x ≫ p' = 𝟙 _}, ∃ x' : Sp K ⟶ X, x' ≫ p = a.1 ≫ p' ∧
      ∃ v, Crd H' s' a.1 v ∧ Crd H s x' v := by
    intro a
    obtain ⟨v, hv⟩ := crd_exists hH' s' a.1
    obtain ⟨x', h1, h2⟩ := hc ⟨a.1, a.2, hv⟩
    exact ⟨x', h1.trans a.2.symm, v, hv, h2⟩
  choose x' hx' using hx
  have hcov : ⨆ j, Out.nonzeroLocus (s' j) = ⊤ := by simpa using hI'.1
  obtain ⟨g, h1, -, h3⟩ := exists_factor K X Y p p' H H' J s s' hH hH' hI hcov K _
    (fun a : {x : Sp K ⟶ Y // x ≫ p' = 𝟙 _} => a.1) x' (dense_points p') hx'
  exact ⟨g, h1, h3⟩

theorem eq_id {k : Type} [CommRing k] {X : Scheme.{0}} (p : X ⟶ Sp k) {H : LB X} {J : Type} {s : J → H.Sec}
    (hH : H.IsLB) (hI : ImmBy p H s Set.univ) (g : X ⟶ X) (hg : g ≫ p = p)
    (h : ∀ (R : Type) [CommRing R] [IsLocalRing R] (y : Sp R ⟶ X) (v : J → R),
      Crd H s y v → Crd H s (y ≫ g) v) : g = 𝟙 X := by
  refine ext_local _ _ fun R _ _ y => ?_
  obtain ⟨v, hv⟩ := crd_exists hH s y
  rw [Category.comp_id]
  exact eq_of_crd_eq k X p H J s _ hH hI R _ _ v (by rw [Category.assoc, hg]) (h R y v hv) hv

theorem exists_iso : ∀ (K : Type) [Field K] [IsAlgClosed K] (X X' : Over (Sp K)) [IsIntegral X.left] [IsIntegral X'.left] [IsProper X.hom] [IsProper X'.hom] (H : LB X.left) (H' : LB X'.left) (J : Type) [Fintype J] (s : J → H.Sec) (s' : J → H'.Sec), H.IsLB → H'.IsLB → ImmBy X.hom H s Set.univ → ImmBy X'.hom H' s' Set.univ → cone X.hom H s = cone X'.hom H' s' → ∃ φ : X ≅ X', ∀ (R : Type) [CommRing R] [IsLocalRing R] (y : Sp R ⟶ X.left) (v : J → R), Crd H s y v → Crd H' s' (y ≫ φ.hom.left) v := by
  intro K _ _ X X' _ _ _ _ H H' J _ s s' hH hH' hI hI' hc
  obtain ⟨g, h1, h2⟩ := exists_hom X'.hom X.hom hH' hH hI' hI hc.le
  obtain ⟨g', h1', h2'⟩ := exists_hom X.hom X'.hom hH hH' hI hI' hc.ge
  have e : g ≫ g' = 𝟙 _ := eq_id X.hom hH hI _ (by rw [Category.assoc, h1', h1]) fun R _ _ y v hv => by
    rw [← Category.assoc]
    exact h2' R _ v (h2 R y v hv)
  have e' : g' ≫ g = 𝟙 _ := eq_id X'.hom hH' hI' _ (by rw [Category.assoc, h1, h1']) fun R _ _ y v hv => by
    rw [← Category.assoc]
    exact h2 R _ v (h2' R y v hv)
  exact ⟨Over.isoMk ⟨g, g', e, e'⟩ h1, h2⟩

end GlobalTheory.ZH.IsoCone
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ThetaFamilyOrigin.ExistsLevelHasConstantThetaPt
section
set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory

namespace ConstThetaLevel

open ThetaPtMove

theorem exists_symplectic_points (hLaw : Laws) (K : Type) [Field K] [IsAlgClosed K] (P : PolAV (Sp K)) {g : ℕ}
    (hg : g = P.g) (M : ℕ) (hM : (M : K) ≠ 0) (ze : Γ(Sp K, ⊤)ˣ) (hz : IsPrimitiveRoot ze M) :
    ∃ x : Fin (2 * g) → (baseOver (Sp K) ⟶ P.A), (∀ i, x i ^ M = 1) ∧
      ∀ i j, WeilIs P.A P.L M (x i) (x j) (ze ^ stdSymp g i j) := by
  subst hg
  have := P.isAb.comm
  have : IsDomain Γ(Sp K, ⊤) := (Scheme.ΓSpecIso (CommRingCat.of K)).commRingCatIsoToRingEquiv.toMulEquiv.isDomain K
  obtain ⟨w₁, w₂, w₃, -⟩ := hLaw.weil _ P M (baseOver (Sp K))
  let H : Subgroup (baseOver (Sp K) ⟶ P.A) := (powMonoidHom M).ker
  have hH : ∀ x : H, x.1 ^ M = 1 := fun x => x.2
  choose c hc hu using fun x y : H => w₁ x.1 y.1 (hH x) (hH y)
  have l : ∀ x x' y, c (x * x') y = c x y * c x' y := fun x x' y => (hu _ _ _ (w₂ _ _ _ _ _ (hc x y) (hc x' y))).symm
  have s : ∀ x y, c y x = (c x y)⁻¹ := fun x y => (hu _ _ _ (CommPairing.weilIs_symm P.isLB (hc x y))).symm
  let e : H →* H →* Γ(Sp K, ⊤)ˣ := MonoidHom.mk' (fun x => MonoidHom.mk' (c x) fun y y' => by
    rw [s (y * y'), l, mul_inv, ← s, ← s]) fun x x' => MonoidHom.ext fun y => l x x' y
  obtain ⟨x, hx⟩ := _root_.GlobalTheory.exists_stdSymp_of_alternating_pairing M P.g H _ ze (Nat.pos_of_ne_zero fun h => hM (by rw [h, Nat.cast_zero])) hz
    (fun x => Subtype.ext (hH x)) (fun d hd => by
      obtain ⟨b, rfl⟩ := hd
      have hd : (d : K) ≠ 0 := left_ne_zero_of_mul (by rwa [Nat.cast_mul] at hM)
      refine Eq.trans (Nat.card_congr ?_) ((hLaw.mulN _ P d (Nat.pos_of_ne_zero fun h => hd (by
        rw [h, Nat.cast_zero]))).2.2.2.2 K (𝟙 _) hd)
      exact ⟨fun x => ⟨x.1.1, congrArg Subtype.val x.2⟩, fun x => ⟨⟨x.1, show x.1 ^ (d * b) = 1 by
        rw [pow_mul, x.2, one_pow]⟩, Subtype.ext x.2⟩, fun _ => rfl, fun _ => rfl⟩)
    e (fun x => (hu _ _ _ (w₃ _ (hH x))).symm) (fun x h => Subtype.ext
      (hLaw.weilNondeg K P M hM x.1 (hH x) fun y hy => (show c x ⟨y, hy⟩ = 1 from h ⟨y, hy⟩) ▸ hc x ⟨y, hy⟩))
  exact ⟨fun i => (x i).1, fun i => hH _, fun i j => (show c (x i) (x j) = _ from hx i j) ▸ hc (x i) (x j)⟩

theorem isThetaPt_fibre (hS : SecBaseChangeSt) {K R : Type} [Field K] [CommRing R] {fK : K →+* R} {P₀ : PolAV (Sp K)}
    {P : PolAV (Sp R)} {φ : P.A.left ⟶ P₀.A.left} (h : IsPolFibre fK P₀ P φ) {k : ℕ} {I : Type}
    {x : I → (baseOver (Sp R) ⟶ P.A)} {x₀ : I → (baseOver (Sp K) ⟶ P₀.A)}
    (hx : ∀ i, spMap fK ≫ (x₀ i).left = (x i).left ≫ φ) (hk : ∀ i, x i ^ (k ^ 2) = 1) {v₀ : I → Γ(Sp K, ⊤)}
    (H : IsThetaPt P₀ k x₀ v₀) : IsThetaPt P k x (fun i => (spMap fK).appTop.hom (v₀ i)) := by
  obtain ⟨ho, hu, H⟩ := H
  have : Subsingleton (Sp K) := inferInstanceAs (Subsingleton (PrimeSpectrum K))
  obtain ⟨p₀⟩ : Nonempty (Sp K) := inferInstanceAs (Nonempty (PrimeSpectrum K))
  obtain ⟨V, hV, H⟩ := H p₀
  obtain rfl : V = ⊤ := eq_top_iff.2 fun q _ => by rwa [Subsingleton.elim (α := Sp K) q p₀]
  refine ⟨ho, (map_natCast (spMap fK).appTop.hom k) ▸ hu.map (spMap fK).appTop.hom, fun _ => ⟨⊤, trivial, ?_⟩⟩
  let t : Sp R ⟶ (overRes (T := baseOver (Sp K)) ⊤).left := spMap fK ≫ (Sp K).topIso.inv
  have ht : t ≫ (⊤ : (Sp K).Opens).ι = spMap fK := by
    show (spMap fK ≫ (Sp K).topIso.inv) ≫ _ = _
    rw [Category.assoc, Scheme.toIso_inv_ι, Category.comp_id]
  let σ : (overRes (T := baseOver (Sp R)) ⊤).left ⟶ (baseAt t).left := (⊤ : (Sp R).Opens).ι
  have : IsIso σ := inferInstanceAs (IsIso (Sp R).topIso.hom)
  have ht' : (σ ≫ (homAt t).left) ≫ (⊤ : (Sp K).Opens).ι = (⊤ : (Sp R).Opens).ι ≫ spMap fK :=
    (Category.assoc _ _ _).trans (congrArg (σ ≫ ·) ht)
  have Q := isThetaPtOver_move (σ ≫ (homAt t).left) h.2.1 h.2.2.symm σ (homAt t) rfl
    ((congrArg (_ ≫ ·) (Category.comp_id _)).trans (ht'.trans (congrArg (· ≫ _) (Category.comp_id _).symm)))
    (isGenSec_pullS hS p₀ P₀ t) (x := fun i => overResι ⊤ ≫ x i)
    (fun i => (Category.assoc _ _ _).symm.trans ((congrArg (· ≫ _) ht').trans ((Category.assoc _ _ _).trans
      ((congrArg (_ ≫ ·) (hx i)).trans (Category.assoc _ _ _).symm))))
    (fun i => by rw [← MonObj.comp_pow, hk, MonObj.comp_one]) H
  convert Q using 2 with i
  exact (congrArg (fun q => q.appTop.hom (v₀ i)) ht').symm

end ConstThetaLevel

end GlobalTheory
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ThetaFamilyOrigin.ExistsLevelThetaPtOfPolarisedIso
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.ZH
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.LevelPullIso

open ReciprocityTheory.ChartRestriction.G.Out

theorem isThetaPt_of_iso {S : Scheme.{0}} {P P' : PolAV S} (φ : P.A ≅ P'.A) [IsMonHom φ.hom]
    (hw : LBIso P.L (P'.L.pull φ.hom.left)) {T : Over S} {k : ℕ} {I : Type} {x : I → (T ⟶ P.A)}
    (hk : ∀ i, x i ^ (k ^ 2) = 1) {v : I → Γ(T.left, ⊤)} (H : IsThetaPt P' k (fun i => x i ≫ φ.hom) v) :
    IsThetaPt P k x v := by
  refine ⟨H.1, H.2.1, fun p => ?_⟩
  obtain ⟨V, hV, Q⟩ := H.2.2 p
  refine ⟨V, hV, ?_⟩
  have hk' : ∀ i, (overResι V ≫ x i) ^ (k ^ 2) = 1 := fun i => by
    rw [← MonObj.comp_pow, hk, MonObj.comp_one]
  exact GlobalTheory.ThetaPtUp.isThetaPtOver_down (T := overRes V) (T₀ := overRes V) (𝟙 (overRes V).left)
    (Geo.Tor.isGrpPullback_of_iso φ) hw ((Category.id_comp _).trans (Category.comp_id _).symm)
    (x₀ := fun i => overResι V ≫ x i ≫ φ.hom)
    (fun i => (Category.id_comp _).trans (by rw [← Category.assoc]; rfl)) hk' Q

section Basis

variable {S : Scheme.{0}} {P : PolAV S} {M : ℕ} {ze : Γ(S, ⊤)ˣ} (lev : Level P M ze) {g : ℕ} (hg : P.g = g)

theorem basis_pow (i : Fin (2 * g)) : levelBasis lev hg i ^ M = 1 := lev.torsion _

theorem basis_indep (K : Type) [Field K] [IsAlgClosed K] (s : Spec (CommRingCat.of K) ⟶ S)
    (c c' : Fin (2 * g) → Fin M)
    (h : linComb (fun i => (Over.homMk s (by simp) : Over.mk s ⟶ baseOver S) ≫ levelBasis lev hg i)
        (fun i => (c i : ℕ)) =
      linComb (fun i => (Over.homMk s (by simp) : Over.mk s ⟶ baseOver S) ≫ levelBasis lev hg i)
        (fun i => (c' i : ℕ))) : c = c' := by
  subst hg; exact lev.indep K s c c' h

theorem basis_span (K : Type) [Field K] [IsAlgClosed K] (s : Spec (CommRingCat.of K) ⟶ S)
    (y : Over.mk s ⟶ P.A) (hy : y ^ M = 1) : ∃ c : Fin (2 * g) → Fin M,
      linComb (fun i => (Over.homMk s (by simp) : Over.mk s ⟶ baseOver S) ≫ levelBasis lev hg i)
        (fun i => (c i : ℕ)) = y := by
  subst hg; exact lev.span K s y hy

theorem basis_pairing (i j : Fin (2 * g)) :
    WeilIs P.A P.L M (levelBasis lev hg i) (levelBasis lev hg j) (ze ^ stdSymp g i j) := by
  subst hg; exact lev.pairing i j

end Basis

theorem comp_pow_eq_one_iff {S : Scheme.{0}} {A B T : Over S} [GrpObj A] [GrpObj B] (φ : A ≅ B) [IsMonHom φ.hom]
    (x : T ⟶ A) (M : ℕ) : (x ≫ φ.hom) ^ M = 1 ↔ x ^ M = 1 := by
  let F : (T ⟶ A) →* (T ⟶ B) := IsMonHom.monoidHom φ.hom T
  have hF : Function.Injective F := fun a b h => (cancel_mono φ.hom).1 h
  have e : F (x ^ M) = (x ≫ φ.hom) ^ M := map_pow F x M
  rw [← e]
  exact map_eq_one_iff F hF

theorem exists_level (hL : Laws) {S : Scheme.{0}} [IsLocallyNoetherian S] {P P' : PolAV S} (hg' : P'.g = P.g)
    (φ : P.A ≅ P'.A) [IsMonHom φ.hom] (hw : LBIso P.L (P'.L.pull φ.hom.left)) {M : ℕ} {ze : Γ(S, ⊤)ˣ}
    (lev' : Level P' M ze) : ∃ lev : Level P M ze, ∀ i, lev.pt i ≫ φ.hom = levelBasis lev' hg' i := by
  obtain ⟨w, hw⟩ := hw
  obtain ⟨x, hx⟩ : ∃ x : Fin (2 * P.g) → (baseOver S ⟶ P.A), ∀ i, x i ≫ φ.hom = levelBasis lev' hg' i :=
    ⟨fun i => levelBasis lev' hg' i ≫ φ.inv, fun i => by simp⟩
  have ht : ∀ i, x i ^ M = 1 := fun i => by
    rw [← comp_pow_eq_one_iff φ, hx]; exact basis_pow lev' hg' i
  have hc : ∀ {T : Over S} (h : T ⟶ baseOver S) (a : Fin (2 * P.g) → ℕ),
      linComb (fun i => h ≫ x i) a ≫ φ.hom = linComb (fun i => h ≫ levelBasis lev' hg' i) a := fun h a => by
    rw [ThetaPtDet.linComb_comp]
    exact congrArg (linComb · a) (funext fun i => by rw [Category.assoc, hx])
  refine ⟨⟨x, lev'.prim, ht, fun K _ _ s c c' e => ?_, fun K _ _ s y hy => ?_, fun i j => ?_⟩, hx⟩
  · exact basis_indep lev' hg' K s c c' ((hc _ _).symm.trans ((congrArg (· ≫ φ.hom) e).trans (hc _ _)))
  · obtain ⟨c, e⟩ := basis_span lev' hg' K s (y ≫ φ.hom) ((comp_pow_eq_one_iff φ y M).2 hy)
    exact ⟨c, (cancel_mono φ.hom).1 ((hc _ _).trans e)⟩
  · rw [← weilIs_iso_iff hL.globalFns hL.cube P P' φ w hw M _ _ (ht i) (ht j), hx, hx]
    exact basis_pairing lev' hg' i j

end GlobalTheory.LevelPullIso


open GlobalTheory.LevelPullIso in
theorem GlobalTheory.exists_level_thetaPt_of_polIso : Out.Laws → ∀ (g N' : ℕ) (K : Type) [Field K] [IsAlgClosed K] (P P' : Out.PolAV (Sp K)) (hg : P.g = g) (hg' : P'.g = g) (φ : P.A ≅ P'.A), IsPolIso P P' φ → ∀ (ze : Γ(Sp K, ⊤)ˣ) (lev' : Out.Level P' (N' ^ 2) ze) (v : (Fin (2 * g) → ZMod (N' ^ 2)) → Γ((Out.baseOver (Sp K)).left, ⊤)), Out.IsThetaPt P' N' (levelPoint lev' hg') v → ∃ lev : Out.Level P (N' ^ 2) ze, (∀ i, levelBasis lev hg i ≫ φ.hom = levelBasis lev' hg' i) ∧ Out.IsThetaPt P N' (levelPoint lev hg) v := by
  intro hL g N' K _ _ P P' hg hg' φ ⟨hφ, t⟩ ze lev' v hv
  subst hg
  have hw : LBIso P.L (P'.L.pull φ.hom.left) := LBIso.symm t
  obtain ⟨lev, hl⟩ := exists_level hL hg' φ hw lev'
  have hp : ∀ a, levelPoint lev rfl a ≫ φ.hom = levelPoint lev' hg' a := fun a => by
    rw [ThetaPtDet.levelPoint_eq, ThetaPtDet.levelPoint_eq, ThetaPtDet.linComb_comp]
    exact congrArg (Out.linComb · _) (funext hl)
  refine ⟨lev, hl, isThetaPt_of_iso φ hw (fun a => ThetaPtDet.levelPoint_pow lev rfl a) ?_⟩
  rw [funext hp]
  exact hv

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ThetaFamilyOrigin.HomogeneousCoordsOfIsValueAtFrame
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.ZH
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section
namespace GlobalTheory.ZH.CrdDown

theorem val_of_rel {K : Type} [CommRing K] {X Y : Scheme.{0}} (x : Sp K ⟶ X) (ρ : X ⟶ Y) (p : Sp K ⟶ Y)
    (hp : x ≫ ρ = p) (U : X.Opens) (V : Y.Opens) (W : (Sp K).Opens) (hU : ⊤ ≤ x ⁻¹ᵁ U) (hV : U ≤ ρ ⁻¹ᵁ V)
    (hW : ⊤ ≤ W) (hWV : W ≤ p ⁻¹ᵁ V) (u : Γ(Sp K, W)ˣ) :
    ∃ c : Kˣ, ∀ (f : Γ(Y, V)) (w : Γ(Sp K, ⊤)),
      ((Sp K).presheaf.map (homOfLE hWV).op).hom ((p.app V).hom f) =
        ((Sp K).presheaf.map (homOfLE le_top).op).hom w * u.val →
      (Scheme.ΓSpecIso (CommRingCat.of K)).hom.hom w = (c : K) * valR x U ((ρ.appLE V U hV).hom f) := by
  subst hp
  obtain rfl : W = ⊤ := top_le_iff.1 hW
  let φ := (Scheme.ΓSpecIso (CommRingCat.of K)).hom.hom
  refine ⟨(Units.map φ.toMonoidHom u)⁻¹, fun f w h => ?_⟩
  have e : ((Sp K).presheaf.map (homOfLE (le_top : (⊤ : (Sp K).Opens) ≤ ⊤)).op).hom w = w :=
    congrArg (fun φ => CommRingCat.Hom.hom φ w) ((Sp K).presheaf.map_id _)
  rw [e] at h
  have h1 : (x.appLE U ⊤ hU).hom ((ρ.appLE V U hV).hom f) = w * u.val :=
    (congrArg (fun φ => CommRingCat.Hom.hom φ f) (Scheme.Hom.appLE_comp_appLE x ρ V U ⊤ hV hU)).trans h
  rw [CrdCalc.valR_eq x U hU, Units.eq_inv_mul_iff_mul_eq]
  refine Eq.trans ?_ (congrArg φ h1).symm
  rw [map_mul, _root_.mul_comm]
  rfl

theorem crd_down_of_isValueAt : ∀ (K : Type) [Field K] [IsAlgClosed K] (P : Out.PolAV (Sp K)) (N : ℕ) (J : Type) (t : J → LB.Sec (Out.LPow P.A P.L N (Out.baseOver (Sp K)))) (ρ : P.A.left ⟶ ((Out.baseOver (Sp K)) ⊗ P.A).left) (e : ρ ≫ (snd (Out.baseOver (Sp K)) P.A).left = 𝟙 P.A.left) (x : (Out.baseOver (Sp K)) ⟶ P.A) (τ : LB.Gen (LB.LinComb P.L (Y := (Out.baseOver (Sp K)).left) (K := Fin 1) (fun _ => x.left) (fun _ => (N : ℤ)))) (w : J → Γ((Out.baseOver (Sp K)).left, ⊤)), (∀ a, Out.IsValueAt P.A P.L N (t a) x τ (w a)) → Crd (lbPow P.L N) (fun a => PowSec.down P.L (snd (Out.baseOver (Sp K)) P.A).left ρ e ((N : ℕ) : ℤ) (t a)) (x.left : Sp K ⟶ P.A.left) (fun a => (Scheme.ΓSpecIso (CommRingCat.of K)).hom.hom (w a)) := by
  intro K _ _ P N J t ρ e x τ w h
  have hx : (x.left : Sp K ⟶ P.A.left) (IsLocalRing.closedPoint K) ∈ ⨆ i, P.L.U i := by
    rw [P.isLB.cover]; trivial
  obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.1 hx
  have hi' := (CrdCalc.top_le_iff (x.left : Sp K ⟶ P.A.left) _).2 hi
  haveI : IsIso (snd (Out.baseOver (Sp K)) P.A).left :=
    inferInstanceAs (IsIso (pullback.snd (𝟙 (Sp K)) P.A.hom))
  have hp : (x.left : Sp K ⟶ P.A.left) ≫ ρ = (Out.ptSecT P.A x).left := by
    rw [← cancel_mono (snd (Out.baseOver (Sp K)) P.A).left]
    refine (Category.assoc _ _ _).trans ((congrArg (x.left ≫ ·) e).trans ((Category.comp_id _).trans ?_))
    exact (congrArg (fun q => q.left) (lift_snd (𝟙 (Out.baseOver (Sp K))) x)).symm
  have hU : ⊤ ≤ (x.left : Sp K ⟶ P.A.left) ⁻¹ᵁ LB.wchart P.L (fun _ : PUnit => 𝟙 P.A.left) (fun _ => i) :=
    fun y hy => Set.mem_iInter.2 fun _ => hi' hy
  have hW : ⊤ ≤ LB.wchart P.L (fun _ : Fin 1 => x.left) (fun _ => i) :=
    fun y hy => Set.mem_iInter.2 fun _ => hi' hy
  obtain ⟨c, hc⟩ := val_of_rel (x.left : Sp K ⟶ P.A.left) ρ _ hp _ _ _ hU
    (PowSec.chart_eq P.L (snd (Out.baseOver (Sp K)) P.A).left ρ e (fun _ => i)).le hW
    (Out.val_le P.A P.L x (fun _ => i)) (τ.s (fun _ => i))
  exact ⟨fun _ => i, c, hU, fun a => hc _ _ (h a (fun _ => i))⟩

end GlobalTheory.ZH.CrdDown
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ThetaFamilyOrigin.IsClosedImmersionOfSpanLinePowerSections
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.ZH
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.PowSec


open Out in
theorem immBy_down_of_span : Out.Laws → ∀ (K : Type) [Field K] [IsAlgClosed K] (P : Out.PolAV (Sp K)) (N : ℕ) (J : Type) [Fintype J] (t : J → LB.Sec (Out.LPow P.A P.L N (Out.baseOver (Sp K)))) (ρ : P.A.left ⟶ ((Out.baseOver (Sp K)) ⊗ P.A).left) (e : ρ ≫ (snd (Out.baseOver (Sp K)) P.A).left = 𝟙 P.A.left), 4 ≤ N → Submodule.span Γ((Out.baseOver (Sp K)).left, ⊤) (Set.range fun a => (Out.SecM.ofSec P.A (t a) : Out.SecM P.A P.L N (Out.baseOver (Sp K)))) = ⊤ → ImmBy P.A.hom (lbPow P.L N) (fun a => PowSec.down P.L (snd (Out.baseOver (Sp K)) P.A).left ρ e ((N : ℕ) : ℤ) (t a)) Set.univ := by
  intro h K _ _ P n J _ t ρ ρ₂ hn hspan
  let T : Over (Sp K) := baseOver (Sp K)
  let c : Γ(T.left, ⊤) ≃+* K := (Scheme.ΓSpecIso (CommRingCat.of K)).commRingCatIsoToRingEquiv
  have ρ₁ : ρ ≫ (fst T P.A).left = P.A.hom :=
    ((congrArg (ρ ≫ ·) ((Category.comp_id _).symm.trans pullback.condition)).trans
      (Category.assoc _ _ _).symm).trans ((congrArg (· ≫ P.A.hom) ρ₂).trans (Category.id_comp _))
  have ρ₃ : (snd T P.A).left ≫ ρ = 𝟙 _ := by
    apply pullback.hom_ext
    · exact (Category.assoc _ _ _).trans ((congrArg (_ ≫ ·) ρ₁).trans (pullback.condition.symm.trans
        ((Category.comp_id _).trans (Category.id_comp _).symm)))
    · exact (Category.assoc _ _ _).trans ((congrArg (_ ≫ ·) ρ₂).trans ((Category.comp_id _).trans (Category.id_comp _).symm))
  haveI : IsIso ρ := ⟨_, ρ₂, ρ₃⟩
  let b : J → SecM P.A P.L n T := fun a => SecM.ofSec P.A (t a)
  let D : SecM P.A P.L n T → (lbPow P.L n).Sec := fun v =>
    down P.L (snd T P.A).left ρ ρ₂ n (SecM.toSec P.A v)
  have hlin : ∀ (a : J → K) j,
      (D (∑ i, c.symm (a i) • b i)).f j = ∑ i, constFn P.A.hom _ (a i) * (D (b i)).f j := by
    intro a j
    show (ρ.appLE _ _ (chart_eq P.L (snd T P.A).left ρ ρ₂ j).le).hom
      ((∑ i, c.symm (a i) • b i : SecM P.A P.L n T).1 (fun _ => j PUnit.unit)) = _
    rw [Submodule.coe_sum]
    refine (congrArg _ (Finset.sum_apply _ _ _)).trans ?_
    refine (map_sum (ρ.appLE _ _ (chart_eq P.L (snd T P.A).left ρ ρ₂ j).le).hom _ _).trans
      (Finset.sum_congr rfl fun i _ => ?_)
    refine (map_mul _ (liftHom P.A _ (c.symm (a i))) ((b i).1 fun _ => j PUnit.unit)).trans (congrArg₂ (· * ·) ?_ rfl)
    have h1 := (Scheme.Hom.appLE_comp_appLE ρ (fst T P.A).left ⊤ _ _ (fun _ _ => trivial)
      (chart_eq P.L (snd T P.A).left ρ ρ₂ j).le).trans (appLE_congr ρ₁ ⊤ _ _ (fun _ _ => trivial))
    exact congrArg (fun φ => φ.hom (c.symm (a i))) h1
  obtain ⟨m, s, hcov, hs⟩ := veryAmple_lbPow h.ample K P n hn
  have himm : ImmBy P.A.hom (lbPow P.L n) s Set.univ := by
    refine ⟨by simpa only [Set.mem_univ, iSup_pos] using hcov, fun i _ => ?_⟩
    obtain ⟨haff, r, hr, hsurj⟩ := hs i
    refine ⟨haff, r, hr, (SpanImm.closure_eq_top_iff
      (RingHom.comp (P.A.hom.appLE ⊤ _ le_top).hom (Scheme.ΓSpecIso (CommRingCat.of K)).inv.hom) r).2 fun f => ?_⟩
    obtain ⟨F, hF⟩ := hsurj f
    exact ⟨F, hF.symm⟩
  haveI := P.isAb.proper
  refine SpanImm.immBy_of_span K _ P.A.hom _ (LB.isLB_linComb P.isLB _ _) _ J s _ himm fun i => ?_
  obtain ⟨w, hw⟩ := down_surjective P.L (snd T P.A).left ρ ρ₂ n (s i)
  have hw' : D (SecM.ofSec P.A w) = s i := hw
  have hm : (SecM.ofSec P.A w : SecM P.A P.L n T) ∈ Submodule.span Γ(T.left, ⊤) (Set.range b) :=
    hspan.ge Submodule.mem_top
  obtain ⟨a, ha⟩ := (Submodule.mem_span_range_iff_exists_fun _).1 hm
  refine ⟨fun i => c (a i), fun j => ?_⟩
  have := hlin (fun i => c (a i)) j
  simp only [RingEquiv.symm_apply_apply] at this
  rw [ha, hw'] at this
  exact this

end GlobalTheory.PowSec
end

