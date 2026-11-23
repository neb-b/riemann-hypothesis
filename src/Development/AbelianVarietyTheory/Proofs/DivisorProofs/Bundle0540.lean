module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.AxesVanishingStructureSheafDegOne
public import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.IsScalarTowerOfAlgebraMapEq
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.AbelianHodgeDeRham
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CardNonempty
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0438
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0014
public import Development.AbelianVarietyTheory.Definitions.Divisors.SplitDoublingNBlock
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0532

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.BaseChangeTrivialBundleCechBijectiveOfAffine
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.AbCoh
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.CechPoset

namespace GlobalTheory.CechPoset

theorem trivCoord_bijective {R' : Type} [CommRing R'] {X X' : Scheme.{0}} (φ : X' ⟶ X)
    (s' : X' ⟶ Sp R') (V : X'.Opens) : Function.Bijective (trivCoord φ s' V) :=
  (GlobalTheory.AbLaw.SecOn.chart (LB.isLB_pull (LB.isLB_triv X) φ) (i0 φ)
    (by rw [triv_pull_U]; exact le_top)).bijective

theorem Φ_bijective_of_affine : ∀ {R R' : Type} [CommRing R] [CommRing R'] [Algebra R R'] {X X' : Scheme.{0}} {s : X ⟶ Sp R} {s' : X' ⟶ Sp R'} {φ : X' ⟶ X} (h : IsPullback φ s' s (spMap (algebraMap R R'))) {κ : Type} [LinearOrder κ] [Fintype κ] (D : κ → X.Opens) (hD' : ∀ I : Finset κ, I.Nonempty → IsAffineOpen (⨅ i ∈ I, φ ⁻¹ᵁ D i)), (∀ I : Finset κ, I.Nonempty → IsAffineOpen (⨅ i ∈ I, D i)) → ∀ p : ℕ, Function.Bijective (Φ h.w D hD' p) := by
  intro R R' _ _ _ X X' s s' φ h κ _ _ D hD' hD p
  have hB := GlobalTheory.AbLaw.secTermBaseChange_bijective (M := LB.triv X) (D := D) (LB.isLB_triv X) h (p + 1)
    fun t ht => hD t (Finset.card_pos.1 (by omega))
  exact (Function.Bijective.piMap fun t => trivCoord_bijective φ s' _).comp hB

end GlobalTheory.CechPoset
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.BaseChangeTrivialBundleCechDifferentialComm
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.AbCoh
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.CechPoset

namespace GlobalTheory.CechPoset

theorem trivCoord_restrict {X X' : Scheme.{0}} {R' : Type} [CommRing R'] (φ : X' ⟶ X) (s' : X' ⟶ Sp R')
    {V W : X'.Opens} (h : W ≤ V) (x : GlobalTheory.AbLaw.SecOnR s' ((LB.triv X).pull φ) V) :
    trivCoord φ s' W (GlobalTheory.AbLaw.SecOnR.restrict s' _ h x) = Sec.res s' h (trivCoord φ s' V x) := by
  simp only [trivCoord, LinearMap.coe_mk, AddHom.coe_mk, GlobalTheory.AbLaw.SecOnR.coord_restrict]
  change (X'.presheaf.map _ ≫ X'.presheaf.map _).hom _ = (X'.presheaf.map _ ≫ X'.presheaf.map _).hom _
  rw [← Functor.map_comp, ← Functor.map_comp]; rfl

theorem Φ_apply {R R' : Type} [CommRing R] [CommRing R'] [Algebra R R'] {X X' : Scheme.{0}} {s : X ⟶ Sp R}
    {s' : X' ⟶ Sp R'} {φ : X' ⟶ X} (w : φ ≫ s = s' ≫ spMap (algebraMap R R')) {κ : Type} [LinearOrder κ]
    (D : κ → X.Opens) (hD' : ∀ I : Finset κ, I.Nonempty → IsAffineOpen (⨅ i ∈ I, φ ⁻¹ᵁ D i)) (q : ℕ)
    (x : R' ⊗[R] (GlobalTheory.AbLaw.cechLB s (LB.triv X) D).X q)
    (t : {s : Finset κ // s.card = q + 1}) :
    Φ w D hD' q x t = trivCoord φ s' (⨅ i ∈ t.1, φ ⁻¹ᵁ D i) (GlobalTheory.AbLaw.secTermBaseChange (LB.triv X) D w (q + 1) x t) :=
  rfl

theorem trivCoord_d {R' : Type} [CommRing R'] {X X' : Scheme.{0}} {s' : X' ⟶ Sp R'} (φ : X' ⟶ X) {κ : Type}
    [LinearOrder κ] (D : κ → X.Opens) (hD' : ∀ I : Finset κ, I.Nonempty → IsAffineOpen (⨅ i ∈ I, φ ⁻¹ᵁ D i))
    (p : ℕ) (y : GlobalTheory.Cube.Term (GlobalTheory.AbLaw.secCube s' ((LB.triv X).pull φ) fun i => φ ⁻¹ᵁ D i) (p + 1))
    (t : {s : Finset κ // s.card = p + 1 + 1}) :
    trivCoord φ s' (⨅ i ∈ t.1, φ ⁻¹ᵁ D i) (GlobalTheory.Cube.d _ (p + 1) y t) =
      δ (covF s' (fun i => φ ⁻¹ᵁ D i) hD') p (fun u => trivCoord φ s' (⨅ i ∈ u.1, φ ⁻¹ᵁ D i) (y u)) t := by
  refine (congrArg (trivCoord φ s' (⨅ i ∈ t.1, φ ⁻¹ᵁ D i)) (GlobalTheory.Cube.d_apply _ (p + 1) y t)).trans ?_
  refine ((map_sum (trivCoord φ s' (⨅ i ∈ t.1, φ ⁻¹ᵁ D i)) _ _)).trans ?_
  refine Eq.trans ?_ (δ_apply (covF s' (fun i => φ ⁻¹ᵁ D i) hD') p _ t).symm
  refine Finset.sum_congr rfl fun i _ => ?_
  refine (map_zsmul (trivCoord φ s' (⨅ i ∈ t.1, φ ⁻¹ᵁ D i)) _ _).trans ?_
  congr 1
  exact trivCoord_restrict φ s' _ _

theorem Φ_dB : ∀ {R R' : Type} [CommRing R] [CommRing R'] [Algebra R R'] {X X' : Scheme.{0}} {s : X ⟶ Sp R} {s' : X' ⟶ Sp R'} {φ : X' ⟶ X} (w : φ ≫ s = s' ≫ spMap (algebraMap R R')) {κ : Type} [LinearOrder κ] (D : κ → X.Opens) (hD' : ∀ I : Finset κ, I.Nonempty → IsAffineOpen (⨅ i ∈ I, φ ⁻¹ᵁ D i)) (p : ℕ) (x : R' ⊗[R] (GlobalTheory.AbLaw.cechLB s (LB.triv X) D).X p), Φ w D hD' (p + 1) (dB (GlobalTheory.AbLaw.cechLB s (LB.triv X) D) R' p (p + 1) x) = δ _ p (Φ w D hD' p x) := by
  intro R R' _ _ _ X X' s s' φ w κ _ D hD' p x
  have e1 : dB (GlobalTheory.AbLaw.cechLB s (LB.triv X) D) R' p (p + 1) x =
      (GlobalTheory.Cube.d (GlobalTheory.AbLaw.secCube s (LB.triv X) D) (p + 1)).baseChange R' x := by
    simp only [dB, GlobalTheory.AbLaw.cechLB_d]; rfl
  have e2 := GlobalTheory.AbLaw.d_secTermBaseChange (LB.triv X) D w (p + 1) x
  funext t
  refine (Φ_apply w D hD' (p + 1) _ t).trans ?_
  refine (congrArg (fun z => trivCoord φ s' (⨅ i ∈ t.1, φ ⁻¹ᵁ D i)
    (GlobalTheory.AbLaw.secTermBaseChange (LB.triv X) D w (p + 1 + 1) z t)) e1).trans ?_
  refine (congrArg (fun z => trivCoord φ s' (⨅ i ∈ t.1, φ ⁻¹ᵁ D i) (z t)) e2.symm).trans ?_
  exact trivCoord_d φ D hD' p _ t

end GlobalTheory.CechPoset
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.BaseChangeTrivialBundleCechOneTmul
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.AbCoh
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.CechPoset

set_option autoImplicit false

namespace GlobalTheory.CechPoset

theorem Φ_one_tmul : ∀ {R R' : Type} [CommRing R] [CommRing R'] [Algebra R R'] {X X' : Scheme.{0}} {s : X ⟶ Sp R} {s' : X' ⟶ Sp R'} {φ : X' ⟶ X} (w : φ ≫ s = s' ≫ spMap (algebraMap R R')) {κ : Type} [LinearOrder κ] (D : κ → X.Opens) (hD' : ∀ I : Finset κ, I.Nonempty → IsAffineOpen (⨅ i ∈ I, φ ⁻¹ᵁ D i)), Φ w D hD' 0 ((1 : R') ⊗ₜ[R] one s D) = fun _ => 1 := by
  intro R R' _ _ _ X X' s s' φ w κ _ D hD'
  funext t
  have key : GlobalTheory.AbLaw.SecOnR.coord (f := s') (M := (LB.triv X).pull φ) (GlobalTheory.AbLaw.secTermBaseChange (LB.triv X) D w 1 ((1 : R') ⊗ₜ[R] one s D) t) (i0 φ) = 1 := by
    erw [GlobalTheory.AbLaw.secTermBaseChange_tmul, one_smul]
    refine (GlobalTheory.AbLaw.SecOn.coord_pullLE (M := LB.triv X) φ (GlobalTheory.AbLaw.preimage_biInf D φ t.1).ge ((GlobalTheory.AbLaw.secOnTrivEquiv _).symm 1) (i0 φ)).trans ?_
    have hc : GlobalTheory.LB.coord ((GlobalTheory.AbLaw.secOnTrivEquiv (X := X) (⨅ i ∈ t.1, D i)).symm 1) PUnit.unit = 1 := by
      refine (GlobalTheory.AbLaw.SecOn.coord_chart_symm (M := Out.Inh.trivLB X) (Out.Inh.trivLB_isLB X) PUnit.unit PUnit.unit le_top (1 : Γ(X, ⨅ i ∈ t.1, D i))).trans ?_
      rw [map_one]
      exact (_root_.one_mul _).trans (map_one _)
    exact (congrArg _ hc).trans (map_one _)
  change Sec.res s' _ (GlobalTheory.AbLaw.SecOnR.coord (f := s') (M := (LB.triv X).pull φ) (GlobalTheory.AbLaw.secTermBaseChange (LB.triv X) D w 1 ((1 : R') ⊗ₜ[R] one s D) t) (i0 φ)) = 1
  rw [key]
  exact (Sec.res s' _).map_one

end GlobalTheory.CechPoset
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.BaseChangeTrivialBundleCechPullbackComm
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.AbCoh
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.CechPoset

namespace GlobalTheory.CechPoset

theorem trivCoord_pull_comp {R R' R'' : Type} [CommRing R] [CommRing R'] [CommRing R''] {g' : R →+* R'} {g'' : R →+* R''}
    {X X' X'' : Scheme.{0}} {s : X ⟶ Sp R} {s' : X' ⟶ Sp R'} {s'' : X'' ⟶ Sp R''} {φ : X' ⟶ X} {φ' : X'' ⟶ X}
    (w' : φ ≫ s = s' ≫ spMap g') (w'' : φ' ≫ s = s'' ≫ spMap g'') (ψ : X'' ⟶ X') (h : ψ ≫ φ = φ')
    (V : X.Opens) (V' : X'.Opens) (V'' : X''.Opens) (e' : V' ≤ φ ⁻¹ᵁ V) (e'' : V'' ≤ φ' ⁻¹ᵁ V) (e : V'' ≤ ψ ⁻¹ᵁ V')
    (x : GlobalTheory.AbLaw.SecOnR s (LB.triv X) V) :
    trivCoord φ' s'' V'' (GlobalTheory.AbLaw.SecOnR.pull (LB.triv X) w'' V V'' e'' x) =
      (ψ.appLE V' V'' e).hom (trivCoord φ s' V' (GlobalTheory.AbLaw.SecOnR.pull (LB.triv X) w' V V' e' x)) := by
  subst h
  have k : ∀ {Y : Scheme.{0}} {S : Type} [CommRing S] {g : R →+* S} (t : Y ⟶ Sp S) (π : Y ⟶ X)
      (w : π ≫ s = t ≫ spMap g) (O : Y.Opens) (eO : O ≤ π ⁻¹ᵁ V) (e2 : O ≤ π ⁻¹ᵁ (V ⊓ (LB.triv X).U PUnit.unit)),
      trivCoord π t O (GlobalTheory.AbLaw.SecOnR.pull (LB.triv X) w V O eO x) =
        (π.appLE _ O e2).hom (x.coord PUnit.unit) := by
    intro Y S _ g t π w O eO e2
    have := GlobalTheory.AbLaw.SecOn.coord_pullLE π eO ((GlobalTheory.AbLaw.SecOnR.of s (LB.triv X) V).symm x) (i0 π)
    refine (congrArg (Sec.res t (le_inf le_rfl (by rw [triv_pull_U]; exact le_top))) this).trans ?_
    exact GlobalTheory.LB.resG_appLE π _ _ _
  have e2 : V' ≤ φ ⁻¹ᵁ (V ⊓ (LB.triv X).U PUnit.unit) := fun y hy => ⟨e' hy, trivial⟩
  rw [k s' φ w' V' e' e2, k s'' (ψ ≫ φ) w'' V'' e'' (fun y hy => e2 (e hy))]
  exact (congrArg (fun q => q.hom (x.coord PUnit.unit)) (Scheme.Hom.appLE_comp_appLE ψ φ _ V' V'' e2 e)).symm

theorem Φ_ext_eq_pullCoef : ∀ {R R' R'' : Type} [CommRing R] [CommRing R'] [CommRing R''] [Algebra R R'] [Algebra R R''] {X X' X'' : Scheme.{0}} {s : X ⟶ Sp R} {s' : X' ⟶ Sp R'} {s'' : X'' ⟶ Sp R''} {φ : X' ⟶ X} {φ' : X'' ⟶ X} (w' : φ ≫ s = s' ≫ spMap (algebraMap R R')) (w'' : φ' ≫ s = s'' ≫ spMap (algebraMap R R'')) (α : R' →ₐ[R] R'') (ψ : X'' ⟶ X') (wψ : ψ ≫ s' = s'' ≫ spMap (α : R' →+* R'')), ψ ≫ φ = φ' → ∀ {κ : Type} [LinearOrder κ] (D : κ → X.Opens) (hD' : ∀ I : Finset κ, I.Nonempty → IsAffineOpen (⨅ i ∈ I, φ ⁻¹ᵁ D i)) (hD'' : ∀ I : Finset κ, I.Nonempty → IsAffineOpen (⨅ i ∈ I, φ' ⁻¹ᵁ D i)) (hle : ∀ i, φ' ⁻¹ᵁ D i ≤ ψ ⁻¹ᵁ (φ ⁻¹ᵁ D i)) (p : ℕ) (z : R' ⊗[R] (GlobalTheory.AbLaw.cechLB s (LB.triv X) D).X p) (t : {s : Finset κ // s.card = p + 1}), Φ w'' D hD'' p (GlobalTheory.AbCoh.ext α _ z) t = (pullCoef wψ (fun i => φ ⁻¹ᵁ D i) hD' (fun i => φ' ⁻¹ᵁ D i) hD'' hle).α (ne t.1 (card_nonempty t)) (Φ w' D hD' p z t) := by
  intro R R' R'' _ _ _ _ _ X X' X'' s s' s'' φ φ' w' w'' α ψ wψ h κ _ D hD' hD'' hle p z t
  induction z using TensorProduct.induction_on with
  | zero =>
    rw [map_zero, map_zero, map_zero]
    exact (map_zero ((pullCoef wψ (fun i => φ ⁻¹ᵁ D i) hD' (fun i => φ' ⁻¹ᵁ D i) hD'' hle).α (ne t.1 (card_nonempty t)))).symm
  | add x y hx hy =>
    rw [map_add (f := _), map_add (f := _), map_add (f := _)]
    exact (congrArg₂ (· + ·) hx hy).trans (map_add ((pullCoef wψ (fun i => φ ⁻¹ᵁ D i) hD' (fun i => φ' ⁻¹ᵁ D i) hD'' hle).α (ne t.1 (card_nonempty t))) _ _).symm
  | tmul r x =>
    have a1 : Φ w'' D hD'' p (GlobalTheory.AbCoh.ext α _ (r ⊗ₜ x)) t = trivCoord φ' s'' _ (α r • GlobalTheory.AbLaw.secCubePull (LB.triv X) D w'' t.1 (x t)) := rfl
    have a2 : Φ w' D hD' p (r ⊗ₜ x) t = trivCoord φ s' _ (r • GlobalTheory.AbLaw.secCubePull (LB.triv X) D w' t.1 (x t)) := rfl
    refine a1.trans (Eq.trans ?_ (congrArg ((pullCoef wψ (fun i => φ ⁻¹ᵁ D i) hD' (fun i => φ' ⁻¹ᵁ D i) hD'' hle).α (ne t.1 (card_nonempty t))) a2).symm)
    refine ((trivCoord φ' s'' _).map_smul _ _).trans ?_
    refine Eq.trans ?_ (congrArg ((pullCoef wψ (fun i => φ ⁻¹ᵁ D i) hD' (fun i => φ' ⁻¹ᵁ D i) hD'' hle).α (ne t.1 (card_nonempty t))) ((trivCoord φ s' _).map_smul _ _)).symm
    refine Eq.trans ?_ ((pullCoef wψ (fun i => φ ⁻¹ᵁ D i) hD' (fun i => φ' ⁻¹ᵁ D i) hD'' hle).smul (ne t.1 (card_nonempty t)) r _).symm
    exact congrArg (α r • ·) (trivCoord_pull_comp w' w'' ψ h _ _ _ _ _ (pr _ hD' _ hD'' hle (ne t.1 (card_nonempty t)).unop).2 (x t))

end GlobalTheory.CechPoset
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CechH1PullbackRefinementCompat
section
set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.AbCoh

namespace GlobalTheory.CechPoset

theorem pr_monotone {κ : Type} [LinearOrder κ] {X' X'' : Scheme.{0}} {ψ : X'' ⟶ X'} (D' : κ → X'.Opens)
    (hD' : ∀ I : Finset κ, I.Nonempty → IsAffineOpen (⨅ i ∈ I, D' i)) (D'' : κ → X''.Opens)
    (hD'' : ∀ I : Finset κ, I.Nonempty → IsAffineOpen (⨅ i ∈ I, D'' i)) (hle : ∀ i, D'' i ≤ ψ ⁻¹ᵁ D' i) :
    Monotone (pr D' hD' D'' hD'' hle) := fun _ _ h =>
  Subtype.mk_le_mk.2 (Prod.mk_le_mk.2 ⟨cov_mono D'' hD'' h, cov_mono D' hD' h⟩)

theorem restrict_pull1_pullHO1 {R' R'' : Type} [CommRing R'] [CommRing R''] {X' X'' : Scheme.{0}}
    {s' : X' ⟶ Sp R'} {s'' : X'' ⟶ Sp R''} {σ : R' →+* R''} {ψ : X'' ⟶ X'}
    (w : ψ ≫ s' = s'' ≫ spMap σ) {κ : Type} [LinearOrder κ] (D' : κ → X'.Opens)
    (hD' : ∀ I : Finset κ, I.Nonempty → IsAffineOpen (⨅ i ∈ I, D' i)) (D'' : κ → X''.Opens)
    (hD'' : ∀ I : Finset κ, I.Nonempty → IsAffineOpen (⨅ i ∈ I, D'' i)) (hle : ∀ i, D'' i ≤ ψ ⁻¹ᵁ D' i)
    (y : HO1 s') :
    (CoefMap.restrict (OAff s'') (cov_mono D'' hD'').functor.op).pull1 (pullHO1 w y) =
      (pullCoef w D' hD' D'' hD'' hle).pull1
        ((CoefMap.restrict (OAff s') (cov_mono D' hD').functor.op).pull1 y) := by
  have hp : (pairPull w).pull1 y = (pairRes ψ s'').pull1 (pullHO1 w y) := isPullO_pullHO1 w y
  generalize pullHO1 w y = z at hp
  let n := CoefMap.restrict (OPair ψ s'') (pr_monotone D' hD' D'' hD'' hle).functor.op
  have h1 : (CoefMap.restrict (OAff s'') (cov_mono D'' hD'').functor.op).pull1 z =
      n.pull1 ((pairRes ψ s'').pull1 z) := by
    refine Eq.trans ?_ ((pairRes ψ s'').pullCohomologyOne_comp n z)
    exact CoefMap.pullCohomologyOne_eq_of_natTrans _ ((pairRes ψ s'').comp n) { app U := 𝟙 _ }
      (fun U b ↦ mp_id (OAff s'') _ b) z
  rw [h1, ← hp]
  refine ((pairPull w).pullCohomologyOne_comp n y).symm.trans (Eq.trans ?_ (CoefMap.pullCohomologyOne_comp _ _ y))
  exact CoefMap.pullCohomologyOne_eq_of_natTrans _ _ { app U := 𝟙 _ } (fun U b ↦ by erw [mp_id]) y

end GlobalTheory.CechPoset
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CechH2PullbackRefinementCompat
section
set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.AbCoh

namespace GlobalTheory.CechPoset

theorem restrict_pull2_pullHO2 {R' R'' : Type} [CommRing R'] [CommRing R''] {X' X'' : Scheme.{0}}
    {s' : X' ⟶ Sp R'} {s'' : X'' ⟶ Sp R''} {σ : R' →+* R''} {ψ : X'' ⟶ X'}
    (w : ψ ≫ s' = s'' ≫ spMap σ) {κ : Type} [LinearOrder κ] (D' : κ → X'.Opens)
    (hD' : ∀ I : Finset κ, I.Nonempty → IsAffineOpen (⨅ i ∈ I, D' i)) (D'' : κ → X''.Opens)
    (hD'' : ∀ I : Finset κ, I.Nonempty → IsAffineOpen (⨅ i ∈ I, D'' i))
    (hle : ∀ i, D'' i ≤ ψ ⁻¹ᵁ D' i) (y : HO2 s') :
    (CoefMap.restrict (OAff s'') (cov_mono D'' hD'').functor.op).pull2 (pullHO2 w y) =
      (pullCoef w D' hD' D'' hD'' hle).pull2
        ((CoefMap.restrict (OAff s') (cov_mono D' hD').functor.op).pull2 y) := by
  have hm : Monotone (pr D' hD' D'' hD'' hle) := fun I J h =>
    Subtype.mk_le_mk.2 (Prod.mk_le_mk.2 ⟨cov_mono D'' hD'' h, cov_mono D' hD' h⟩)
  have h1 : (pairRes ψ s'').pull2 (pullHO2 w y) = (pairPull w).pull2 y :=
    (LinearEquiv.ofBijective (pairRes ψ s'').pull2 (pairRes_pull2_bijective ψ s'')).apply_symm_apply _
  have h2 := congrArg (CoefMap.restrict (OPair ψ s'') hm.functor.op).pull2 h1
  generalize pullHO2 w y = z at h2 ⊢
  obtain ⟨z, rfl⟩ := CatCoh.H2.mk_surjective _ z
  obtain ⟨y, rfl⟩ := CatCoh.H2.mk_surjective _ y
  exact h2

end GlobalTheory.CechPoset
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CocyclePullbackIffPreimageAffineHom
section
set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.AbCoh

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.AbCoh

section Pre

variable {R R' : Type} [CommRing R] [CommRing R'] {X X' : Scheme.{0}} (φ : X' ⟶ X) [IsAffineHom φ]

def preToPair : AffOp X ⥤ (Pair φ)ᵒᵖ :=
  (Monotone.functor (f := fun U : X.affineOpens ↦ prePair φ U) fun _ _ h ↦
    (show prePair φ _ ≤ prePair φ _ from ⟨preU_mono φ h, h⟩)).op

def pairToPre (s' : X' ⟶ Sp R') : CoefMap (RingHom.id R') (OPair φ s') (OPre φ s') where
  G := preToPair φ
  α _ := RingHom.id _
  naturality _ _ := rfl
  smul _ _ _ := rfl

def preToPairRes (s' : X' ⟶ Sp R') : CoefMap (RingHom.id R') (OPre φ s') (OPair φ s') where
  G := pairSnd φ
  α p := (Sec.res s' p.unop.2 : Sec s' (preU φ p.unop.1.2).1 →ₐ[R'] Sec s' p.unop.1.1.1).toRingHom
  naturality {p q} a b := by
    exact (Sec.res_res s' (U := (preU φ p.unop.1.2).1) _ _ b).symm.trans (Sec.res_res s' _ _ b)
  smul p r b := map_smul (Sec.res s' p.unop.2) r b

end Pre

section Lemmas

variable {R R' : Type} [CommRing R] [CommRing R'] {X X' : Scheme.{0}} {φ : X' ⟶ X} [IsAffineHom φ]
  {s : X ⟶ Sp R} {s' : X' ⟶ Sp R'} {σ : R →+* R'}

theorem pairToPre_pull1_pairRes (x : HO1 s') :
    (pairToPre φ s').pull1 ((pairRes φ s').pull1 x) = (preRes φ s').pull1 x := by
  rw [← CoefMap.pullCohomologyOne_comp]
  exact CoefMap.pullCohomologyOne_eq_of_natTrans _ _ { app U := 𝟙 _ } (fun U b ↦ mp_id (OAff s') _ b) x

theorem pairToPre_pull2_pairRes (x : HO2 s') :
    (pairToPre φ s').pull2 ((pairRes φ s').pull2 x) = (preRes φ s').pull2 x := by
  rw [← CoefMap.pullCohomologyTwo_comp]
  exact CoefMap.pullCohomologyTwo_eq_of_natTrans _ _ { app U := 𝟙 _ } (fun U b ↦ mp_id (OAff s') _ b) x

def preIncl : pairSnd φ ⋙ preAff φ ⟶ pairFst φ where
  app p := (homOfLE p.unop.2).op

theorem preToPairRes_pull1_preRes (x : HO1 s') :
    (preToPairRes φ s').pull1 ((preRes φ s').pull1 x) = (pairRes φ s').pull1 x := by
  rw [← CoefMap.pullCohomologyOne_comp]
  exact CoefMap.pullCohomologyOne_eq_of_natTrans _ _ preIncl (fun _ _ ↦ rfl) x

theorem preToPairRes_pull2_preRes (x : HO2 s') :
    (preToPairRes φ s').pull2 ((preRes φ s').pull2 x) = (pairRes φ s').pull2 x := by
  rw [← CoefMap.pullCohomologyTwo_comp]
  exact CoefMap.pullCohomologyTwo_eq_of_natTrans _ _ preIncl (fun _ _ ↦ rfl) x

variable (h : φ ≫ s = s' ≫ spMap σ)

theorem pairToPre_pull1_pairPull (y : HO1 s) :
    (pairToPre φ s').pull1 ((pairPull h).pull1 y) = (preCoef h).pull1 y := by
  rw [← CoefMap.pullCohomologyOne_comp]
  exact CoefMap.pullCohomologyOne_eq_of_natTrans _ _ { app U := 𝟙 _ } (fun U b ↦ congrArg _ (mp_id (OAff s) _ b)) y

theorem pairToPre_pull2_pairPull (y : HO2 s) :
    (pairToPre φ s').pull2 ((pairPull h).pull2 y) = (preCoef h).pull2 y := by
  rw [← CoefMap.pullCohomologyTwo_comp]
  exact CoefMap.pullCohomologyTwo_eq_of_natTrans _ _ { app U := 𝟙 _ } (fun U b ↦ congrArg _ (mp_id (OAff s) _ b)) y

theorem preToPairRes_preα (q : (Pair φ)ᵒᵖ) (b : (OAff s).obj ((pairSnd φ).obj q)) :
    (preToPairRes φ s').α q (preα φ s s' ((pairSnd φ).obj q) b) = (pairPull h).α q b :=
  congrArg (fun t ↦ t.hom b) (φ.appLE_map _ (homOfLE q.unop.2).op)

end Lemmas

theorem red_iff_pre : ∀ (R R' : Type) [CommRing R] [CommRing R'] (X X' : Scheme.{0}) (s : X ⟶ Sp R) (s' : X' ⟶ Sp R') (σ : R →+* R') (φ : X' ⟶ X) (h : φ ≫ s = s' ≫ spMap σ) [IsAffineHom φ], (∀ (f : C1 (OAff s)) (x : HO1 s'), Red1 h f x ↔ ∃ c : Z1 (OPre φ s'), (∀ U V (a : U ⟶ V), c.1 U V a = preα φ s s' V (f U V a)) ∧ GlobalTheory.CatCoh.H1.mk _ c = (preRes φ s').pull1 x) ∧ (∀ (v : C2 (OAff s)) (z : HO2 s'), Red2 h v z ↔ ∃ c : Z2 (OPre φ s'), (∀ U V W (a : U ⟶ V) (b : V ⟶ W), c.1 U V W a b = preα φ s s' W (v U V W a b)) ∧ GlobalTheory.CatCoh.H2.mk _ c = (preRes φ s').pull2 z) ∧ (∀ y, (preRes φ s').pull1 (pullHO1 h y) = (preCoef h).pull1 y) ∧ ∀ y, (preRes φ s').pull2 (pullHO2 h y) = (preCoef h).pull2 y := by
  intro R R' _ _ X X' s s' σ φ h _
  refine ⟨fun f x ↦ ⟨?_, ?_⟩, fun v z ↦ ⟨?_, ?_⟩, fun y ↦ ?_, fun y ↦ ?_⟩
  · rintro ⟨c, hc, hx⟩
    refine ⟨(pairToPre φ s').pullbackOneCocycle c, fun U V a ↦ hc _ _ _, ?_⟩
    rw [← CoefMap.pullCohomologyOne_class, hx, pairToPre_pull1_pairRes]
  · rintro ⟨c, hc, hx⟩
    refine ⟨(preToPairRes φ s').pullbackOneCocycle c, fun p q a ↦ ?_, ?_⟩
    · rw [CoefMap.pullCocycleOne_apply, hc]
      exact preToPairRes_preα h q _
    · rw [← CoefMap.pullCohomologyOne_class, hx, preToPairRes_pull1_preRes]
  · rintro ⟨c, hc, hx⟩
    refine ⟨(pairToPre φ s').pullbackTwoCocycle c, fun U V W a b ↦ hc _ _ _ _ _, ?_⟩
    rw [← CoefMap.pullCohomologyTwo_class, hx, pairToPre_pull2_pairRes]
  · rintro ⟨c, hc, hx⟩
    refine ⟨(preToPairRes φ s').pullbackTwoCocycle c, fun p q r a b ↦ ?_, ?_⟩
    · rw [CoefMap.pullCocycleTwo_apply, hc]
      exact preToPairRes_preα h r _
    · rw [← CoefMap.pullCohomologyTwo_class, hx, preToPairRes_pull2_preRes]
  · have e := congrArg (pairToPre φ s').pull1 (isPullO_pullHO1 h y)
    rw [pairToPre_pull1_pairPull, pairToPre_pull1_pairRes] at e
    exact e.symm
  · have e : (pairRes φ s').pull2 (pullHO2 h y) = (pairPull h).pull2 y :=
      (LinearEquiv.ofBijective (pairRes φ s').pull2 (pairRes_pull2_bijective φ s')).apply_symm_apply _
    have e' := congrArg (pairToPre φ s').pull2 e
    rw [pairToPre_pull2_pairPull, pairToPre_pull2_pairRes] at e'
    exact e'

end GlobalTheory.AbCoh
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoindEigenEqBotOfBlockCutCuspidal
section
open GlobalTheory.FinGL Formalism.L2.DIV Module

namespace GlobalTheory.FinGL.MackeyCut

theorem eig_eq_bot_of_cut : ∀ (F : Type) [Field F] (ψ : AddChar F ℂ) (r : ℕ) (V : Type) [AddCommGroup V] [Module ℂ V] (b : Fin r → ℕ) (σ : Representation ℂ (blockTri (κ := F) b) V), IsCuspDatum b σ → ∀ (j : ℕ) (w : Equiv.Perm (Fin r)) (x : GL (Fin r) F), (∀ (g : GL (Fin r) F) (a c : Fin r), ((x⁻¹ * g * x : GL (Fin r) F) : Matrix (Fin r) (Fin r) F) a c = (g : Matrix (Fin r) (Fin r) F) (w a) (w c)) → ∀ a c : Fin r, a.val < j → j ≤ c.val → b (w a) = b (w c) → eig σ {p | x⁻¹ * (p : GL (Fin r) F) * x ∈ unip F r} (fun p => ψ (edgeSum (cutEdge j) (x⁻¹ * (p : GL (Fin r) F) * x))) = ⊥ := by
  intro F _ ψ r V _ _ b σ hσ j w x hx a c haj hjc hb
  obtain ⟨_, _, _, hcusp⟩ := hσ

  have hy' : ∀ y ∈ eig σ {p | x⁻¹ * (p : GL (Fin r) F) * x ∈ unip F r}
      (fun p => ψ (edgeSum (cutEdge j) (x⁻¹ * (p : GL (Fin r) F) * x))),
      ∀ p : blockTri (κ := F) b, x⁻¹ * (p : GL (Fin r) F) * x ∈ unip F r →
        σ p y = ψ (edgeSum (cutEdge j) (x⁻¹ * (p : GL (Fin r) F) * x)) • y := by
    intro y hy p hp
    unfold eig at hy
    simp only [Submodule.mem_iInf, LinearMap.mem_ker] at hy
    have h := hy p hp
    simpa [sub_eq_zero] using h
  rw [eq_bot_iff]
  intro y hy
  rw [Submodule.mem_bot]

  let S : Finset (Fin r) := Finset.univ.filter (fun i => (w.symm i).val < j)
  refine hcusp S ⟨w a, w c, hb, ?_, ?_⟩ y ?_
  · simp only [S, Finset.mem_filter, Finset.mem_univ, true_and, Equiv.symm_apply_apply]
    exact haj
  · simp only [S, Finset.mem_filter, Finset.mem_univ, true_and, Equiv.symm_apply_apply, not_lt]
    exact hjc
  · intro u hu

    have hent : ∀ a' c' : Fin r, (c'.val ≤ a'.val ∨ (c'.val = a'.val + 1 ∧ a'.val + 1 ≠ j)) →
        ((u : GL (Fin r) F) : Matrix (Fin r) (Fin r) F) (w a') (w c') = (1 : Matrix (Fin r) (Fin r) F) (w a') (w c') := by
      intro a' c' h
      by_contra hne
      obtain ⟨_, h1, h2⟩ := hu _ _ hne
      simp only [S, Finset.mem_filter, Finset.mem_univ, true_and, Equiv.symm_apply_apply, not_lt] at h1 h2
      omega
    have hU : x⁻¹ * (u : GL (Fin r) F) * x ∈ unip F r := by
      show x⁻¹ * (u : GL (Fin r) F) * x ∈ blockTri (κ := F) (fun a : Fin r => a.val) ∧
        ∀ i, ((x⁻¹ * (u : GL (Fin r) F) * x : GL (Fin r) F) : Matrix (Fin r) (Fin r) F) i i = 1
      refine ⟨?_, fun i => ?_⟩
      · rw [mem_blockTri]
        intro a' c' h
        have h' : c'.val < a'.val := h
        rw [hx, hent a' c' (Or.inl h'.le)]
        refine Matrix.one_apply_ne ?_
        intro e
        have := w.injective e
        rw [this] at h'
        exact lt_irrefl _ h'
      · rw [hx, hent i i (Or.inl le_rfl), Matrix.one_apply_eq]
    have hE : edgeSum (cutEdge j) (x⁻¹ * (u : GL (Fin r) F) * x) = 0 := by
      unfold edgeSum
      refine Finset.sum_eq_zero fun a' _ => Finset.sum_eq_zero fun c' _ => ?_
      split_ifs with h
      · have h' : c'.val = a'.val + 1 ∧ a'.val + 1 ≠ j := by
          unfold cutEdge at h
          exact h
        rw [hx, hent a' c' (Or.inr h')]
        refine Matrix.one_apply_ne ?_
        intro e
        have := w.injective e
        rw [this] at h'
        omega
      · rfl
    rw [hy' y hy u hU, hE, AddChar.map_zero_eq_one, one_smul]

end GlobalTheory.FinGL.MackeyCut
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CompatibleGlobalOneFormsFiniteProjective
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.AbCoh
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.AbCoh

theorem compatibleGlobalOneForms_finite_projective : ∀ (R : Type) [CommRing R] (C : Type) [Category.{0} C] (F : C ⥤ CommAlgCat.{0} R),
    HasFrame F → CohomZeroIsConstants F → Module.Finite R (Glob1 F) ∧ Module.Projective R (Glob1 F) := by
  intro R _ C _ F hF h0
  obtain ⟨n, ⟨Φ⟩⟩ := hF
  obtain ⟨l, -, hl⟩ := _root_.GlobalTheory.AbCoh.frame_coord R C F h0 n Φ
  let L : Glob1 F →ₗ[R] (Fin n → R) := LinearMap.pi l
  let S : (Fin n → R) →ₗ[R] Glob1 F := Fintype.linearCombination R Φ.w
  have hSL : S.comp L = LinearMap.id := by
    refine LinearMap.ext fun w ↦ ?_
    simp only [LinearMap.comp_apply, LinearMap.id_apply, S, L, Fintype.linearCombination_apply, LinearMap.pi_apply]
    exact (hl w).symm
  have hsurj : Function.Surjective S := fun w ↦ ⟨L w, by
    simpa using LinearMap.congr_fun hSL w⟩
  exact ⟨Module.Finite.of_surjective S hsurj, Module.Projective.of_split L S hSL⟩

end GlobalTheory.AbCoh
end

