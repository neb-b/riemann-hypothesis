module

public import Mathlib
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CubeVal
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.Bundle0005
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.Bundle0006
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.PhiGenPf
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.Bundle0003
public import Development.AbelianVarietyTheory.Definitions.Uniformization.Bundle0001
public import Development.AbelianVarietyTheory.Definitions.Uniformization.Bundle0002
public import Development.AbelianVarietyTheory.Definitions.Uniformization.SvalTwistOne
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.PullUUnitsCompatGeneric
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0064
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ValCalc
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.FamMod
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0023
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExpandsGTransport
public import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.Bundle0009

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsGenT
section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UU
open ReciprocityTheory.ChartRestriction.G.DVR

noncomputable section
namespace GlobalTheory.UU.IntGen

theorem exists_ratio {X Y : Scheme.{0}} {M : LB X} (hM : M.IsLB) {K K' : Type} [Fintype K] [Fintype K']
    {φ : K → (Y ⟶ X)} {ε : K → ℤ} {φ' : K' → (Y ⟶ X)} {ε' : K' → ℤ} (h : FormEq φ ε φ' ε')
    {u : LB.Gen (LB.LinComb M φ ε)} {u' : LB.Gen (LB.LinComb M φ' ε')} (hu : u.IsGen) (hu' : u'.IsGen) :
    ∃ a : Γ(Y, ⊤)ˣ, ∀ (Z : Scheme.{0}) (r : Z ⟶ Y) (z : Z) (J), Good M z J →
      (val u r z J).val = gs r z ⊤ a.val * (val u' r z J).val := by
  obtain ⟨t, -, hv⟩ := exists_gen hM (K' := PEmpty) (φ' := PEmpty.elim) (ε' := PEmpty.elim) (fun U _ f => by
      refine (Fintype.prod_sum_type _).trans (Eq.trans ?_ (Fintype.prod_empty _).symm)
      have := h U f
      simp only [Sum.elim_inl, Sum.elim_inr, zpow_neg, Finset.prod_inv_distrib, this, mul_inv_cancel])
    (LB.mulGen M _ _ _ _ u (LB.invGen M _ _ u')) (DVR.mulGen_isGen _ _ _ _ _ _ _ hu (DVR.invGen_isGen _ _ _ _ hu'))
  have le : (⊤ : Y.Opens) ≤ LB.wchart M (PEmpty.elim : PEmpty → (Y ⟶ X)) PEmpty.elim := fun _ _ =>
    Set.mem_iInter.2 fun k => k.elim
  refine ⟨res le (t.s PEmpty.elim), fun Z r z J hJ => ?_⟩
  have key : (val u r z J * (val u' r z J)⁻¹).val = gs r z ⊤ (res le (t.s PEmpty.elim)).val := by
    rw [← val_inv, ← val_mul hJ, ← hv Z r z J hJ, val_of t r z J PEmpty.elim (fun k => k.elim)]
    exact (congrArg Units.val (gm_res r z le trivial _)).symm.trans ((gs_unit r z ⊤ trivial _).symm)
  rw [← key, ← Units.val_mul, inv_mul_cancel_right]

variable {R : Type} [CommRing R] [IsDomain R] (D : DegPre R)

theorem prod_famT {T T' : Over (Spec (CommRingCat.of R))} (ρ : T' ⟶ T ⊗ D.P.A) (α : D.X) (k : ℕ) {U : Type}
    [CommGroup U] (h : (T'.left ⟶ D.P.A.left) → U) : ∏ i, h (ρ.left ≫ famφT D T α i) ^ DegPre.famε k i =
      h (ρ ≫ snd _ _).left ^ ((k : ℤ) - 1) * h (cP D T' α * (ρ ≫ snd _ _)).left * (h (cP D T' α).left)⁻¹ *
        h (1 : T' ⟶ D.P.A).left := by
  have e₁ : ρ.left ≫ famφT D T α 1 = (cP D T' α * (ρ ≫ snd _ _)).left :=
    congrArg (fun q => q.left) ((MonObj.comp_mul ρ (snd T D.P.A) (cP D _ α)).trans (by rw [comp_cP, mul_comm]))
  have e₂ : ρ.left ≫ famφT D T α 2 = (cP D T' α).left := congrArg (fun q => q.left) (comp_cP D ρ α)
  have e₃ : ρ.left ≫ famφT D T α 3 = (1 : T' ⟶ D.P.A).left :=
    congrArg (fun q : T' ⟶ D.P.A => q.left) (MonObj.comp_one (M := D.P.A) ρ)
  rw [Fin.prod_univ_four, e₁, e₂, e₃]
  show _ ^ ((k : ℤ) - 1) * _ ^ (1 : ℤ) * _ ^ (-1 : ℤ) * _ ^ (1 : ℤ) = _
  rw [zpow_one, zpow_one, zpow_neg_one]; rfl

def basePts (T : Over (Spec (CommRingCat.of R))) (α mu : D.X) : Fin 4 → (T.left ⟶ D.P.A.left) :=
  ![(cP D T α * cP D T mu).left, (cP D T α).left, (cP D T mu).left, (1 : T ⟶ D.P.A).left]

def baseExp (k : ℕ) : Fin 4 → ℤ := ![-1, 1, 1 - k, k - 1]

theorem prod_base {T T' : Over (Spec (CommRingCat.of R))} (ρ : T' ⟶ T) (α mu : D.X) (k : ℕ) {U : Type}
    [CommGroup U] (h : (T'.left ⟶ D.P.A.left) → U) : ∏ i, h (ρ.left ≫ basePts D T α mu i) ^ baseExp k i =
      (h (cP D T' α * cP D T' mu).left)⁻¹ * h (cP D T' α).left * h (cP D T' mu).left ^ (1 - (k : ℤ)) *
        h (1 : T' ⟶ D.P.A).left ^ ((k : ℤ) - 1) := by
  have e₀ : ρ.left ≫ basePts D T α mu 0 = (cP D T' α * cP D T' mu).left :=
    congrArg (fun q => q.left) ((MonObj.comp_mul ρ (cP D _ α) (cP D _ mu)).trans (by rw [comp_cP, comp_cP]))
  have e₁ : ρ.left ≫ basePts D T α mu 1 = (cP D T' α).left := congrArg (fun q => q.left) (comp_cP D ρ α)
  have e₂ : ρ.left ≫ basePts D T α mu 2 = (cP D T' mu).left := congrArg (fun q => q.left) (comp_cP D ρ mu)
  have e₃ : ρ.left ≫ basePts D T α mu 3 = (1 : T' ⟶ D.P.A).left :=
    congrArg (fun q : T' ⟶ D.P.A => q.left) (MonObj.comp_one (M := D.P.A) ρ)
  rw [Fin.prod_univ_four, e₀, e₁, e₂, e₃]
  show _ ^ (-1 : ℤ) * _ ^ (1 : ℤ) * _ ^ (1 - (k : ℤ)) * _ ^ ((k : ℤ) - 1) = _
  rw [zpow_one, zpow_neg_one]

theorem exists_genT (T S : Over (Spec (CommRingCat.of R))) (π : T ⊗ D.P.A ⟶ S) (k : ℕ) (α mu : D.X)
    (v : LB.Gen (LB.LinComb D.P.L (basePts D S α mu) (baseExp k))) (hv : v.IsGen) :
    ∃ u₀ : LB.Gen (LB.LinComb D.P.L (deltaφT D (α + k • mu) α (toUnit T ≫ D.c mu)) (DegPre.deltaε k)), u₀.IsGen ∧
      ∀ (T' : Over (Spec (CommRingCat.of R))) (ρ : T' ⟶ T ⊗ D.P.A) (z : T'.left) (J), Good D.P.L z J →
        val u₀ ρ.left z J = cubN (th D z J) k (cP D T' α) (cP D T' mu) (ρ ≫ snd _ _) *
          (th D z J (cP D T' α) (ρ ≫ snd _ _) (cP D T' mu))⁻¹ * val v (ρ ≫ π).left z J := by
  let a : T ⊗ D.P.A ⟶ D.P.A := cP D _ α
  let mm : T ⊗ D.P.A ⟶ D.P.A := cP D _ mu
  let x : T ⊗ D.P.A ⟶ D.P.A := snd _ _
  have hα' : cP D (T ⊗ D.P.A) (α + k • mu) = a * mm ^ k := by rw [cPoint_add, cPoint_nsmul]
  have htr : trT D (toUnit T ≫ D.c mu) ≫ snd _ _ = x * mm :=
    (lift_snd _ _).trans (congrArg (x * ·) (comp_cP D (fst T D.P.A) mu))
  obtain ⟨N, hN, vN⟩ := exists_cubN D.cub a mm x k
  obtain ⟨u₀, hu₀, vu₀⟩ := exists_gen D.P.isLB (φ' := deltaφT D (α + k • mu) α (toUnit T ≫ D.c mu))
      (ε' := DegPre.deltaε k) (fun U _ h => by
      have p₁ := prod_cub a x mm h
      have p₂ := prod_base D π α mu k h
      have p₃ := prod_famT D (𝟙 (T ⊗ D.P.A)) (α + k • mu) k h
      have p₄ := prod_famT D (trT D (toUnit T ≫ D.c mu)) α k h
      simp only [Over.id_left, Category.id_comp] at p₃
      rw [hα'] at p₃
      rw [htr] at p₄
      refine Eq.trans (prod_sum₂ (K := Fin 8 ⊕ thK) (K' := Fin 4) (U := U) _
        (prod_sum₂ (K := Fin 8) (K' := thK) (U := U) _ rfl (prod_neg _ _ p₁)) p₂)
        (Eq.trans ?_ (prod_sum₂ (K := Fin 4) (K' := Fin 4) (U := U) _ p₃ (prod_neg _ _ p₄)).symm)
      rw [← _root_.mul_assoc (cP D _ α), mul_comm mm x]
      apply Additive.ofMul.injective
      simp [Fin.prod_univ_succ, ofMul_mul, ofMul_inv, ofMul_zpow, ofMul_pow, a, mm, x]
      module)
    (LB.mulGen D.P.L _ _ _ _ (LB.mulGen D.P.L _ _ _ _ N (LB.invGen D.P.L _ _
      (LB.pullGen D.P.L (thφ D.P.A (x3 D.P.A)) thε D.cub.t (lift a (lift x mm)).left)))
      (LB.pullGen D.P.L _ _ v π.left))
    (mulGen_isGen _ _ _ _ _ _ _ (mulGen_isGen _ _ _ _ _ _ _ hN (invGen_isGen _ _ _ _ (pullGen_isGen _ _ _ _ D.cub.isGen _)))
      (pullGen_isGen _ _ _ _ hv _))
  refine ⟨u₀, hu₀, fun T' ρ z J hJ => ?_⟩
  refine (vu₀ _ _ z J hJ).trans ((val_mul hJ _ _ _).trans (congrArg₂ (· * ·) ((val_mul hJ _ _ _).trans
    ((congrArg₂ (· * ·) (vN T' ρ z J hJ) ((val_inv _ _).trans (congrArg (·⁻¹) (val_cub D.cub ρ hJ _ _ _)))).trans ?_))
    (val_pull hJ _ _ _)))
  rw [← comp_cP D ρ α, ← comp_cP D ρ mu]

def multK (k : ℕ) (mu α : D.X) :=
  LB.mulGen D.P.L _ _ _ _
    (LB.mulGen D.P.L _ _ _ _ (GeneratorPullback.powGen D.P.L _ _ (D.psi mu) k) (D.tau mu α))
    (GeneratorPullback.powGen D.P.L _ _ D.rigK k)

theorem gs_spec {Z : Scheme.{0}} (σ : Z ⟶ (TK R).left) (z : Z) (c : R) :
    gs (σ ≫ jK R) z ⊤ ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom c) =
      gs σ z ⊤ ((Scheme.ΓSpecIso (CommRingCat.of (FractionRing R))).inv.hom (algebraMap R (FractionRing R) c)) := by
  refine (gs_pull σ (jK R) z ⊤ trivial _).symm.trans (congrArg (gs σ z ⊤) ?_)
  exact (congrArg (fun f => (CommRingCat.Hom.hom f) c)
    (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom (algebraMap R (FractionRing R))))).symm

theorem multK_frac (k : ℕ) (α mu : D.X)
    (v : LB.Gen (LB.LinComb D.P.L (basePts D (𝟙_ _) α mu) (baseExp k))) (hv : v.IsGen) :
    ∃ r₁ r₂ : R, r₁ ≠ 0 ∧ r₂ ≠ 0 ∧ ∀ (Z : Scheme.{0}) (σ : Z ⟶ (TK R).left) (z : Z) (J), Good D.P.L z J →
      gs (σ ≫ jK R) z ⊤ ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom r₂) * (val (multK D k mu α) σ z J).val =
      gs (σ ≫ jK R) z ⊤ ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom r₁) *
        (val v (σ ≫ (toUnit (TK R)).left) z J).val := by
  obtain ⟨a, ha⟩ := exists_ratio D.P.isLB (u := multK D k mu α)
    (u' := LB.pullGen D.P.L _ _ v (toUnit (TK R)).left) (fun U _ h => by
      refine Eq.trans ?_ (prod_base D (toUnit (TK R)) α mu k h).symm
      have a₁ : ∀ χ, D.xK χ = (cP D (TK R) χ).left := fun χ => rfl
      have a₂ : (toUnit (TK R)).left ≫ eSec D.P.A = (1 : TK R ⟶ D.P.A).left := rfl
      simp only [Fintype.prod_sum_type, Sum.elim_inl, Sum.elim_inr, Fintype.prod_unique, a₁, a₂]
      rw [add_comm mu α, cPoint_add]
      apply Additive.ofMul.injective
      simp only [ofMul_mul, ofMul_inv, ofMul_zpow, ofMul_pow]
      module)
    (mulGen_isGen _ _ _ _ _ _ _ (mulGen_isGen _ _ _ _ _ _ _
      (powGen_isGen _ _ _ _ (D.psi_gen mu) k) (tau_isGen D mu α))
      (powGen_isGen _ _ _ _ (pullGen_isGen _ _ _ _ D.rig_gen _) k)) (pullGen_isGen _ _ _ _ hv _)
  let c : FractionRing R := (Scheme.ΓSpecIso (CommRingCat.of (FractionRing R))).hom.hom a.val
  have hc : (Scheme.ΓSpecIso (CommRingCat.of (FractionRing R))).inv.hom c = a.val :=
    Iso.hom_inv_id_apply (Scheme.ΓSpecIso (CommRingCat.of (FractionRing R))) a.val
  have hc0 : c ≠ 0 :=
    (a.isUnit.map (Scheme.ΓSpecIso (CommRingCat.of (FractionRing R))).hom.hom).ne_zero
  obtain ⟨r₁, r₂, h₂, e⟩ := IsFractionRing.div_surjective (A := R) c
  have h₂' : r₂ ≠ 0 := nonZeroDivisors.ne_zero h₂
  have h₂K : algebraMap R (FractionRing R) r₂ ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective R (FractionRing R))).2 h₂'
  refine ⟨r₁, r₂, fun h => hc0 (by rw [← e, h, map_zero, zero_div]), h₂', fun Z σ z J hJ => ?_⟩
  have e' : algebraMap R (FractionRing R) r₁ = algebraMap R (FractionRing R) r₂ * c := by
    rw [← e, mul_div_cancel₀ _ h₂K]
  rw [ha Z σ z J hJ, val_pull hJ, gs_spec, gs_spec, e', map_mul, hc, ← _root_.mul_assoc]
  exact congrArg (· * _) (gs_mul σ z ⊤ trivial _ _).symm

theorem frac_mul {M : Type} [CommMonoid M] {g₁ g₂ : M} {u u₀ w m v : Mˣ} (h₁ : u = w * m) (h₂ : u₀ = w * v)
    (h : g₂ * m.val = g₁ * v.val) : g₂ * u.val = g₁ * u₀.val := by
  rw [h₁, h₂, Units.val_mul, Units.val_mul, mul_left_comm, h, mul_left_comm]

theorem main : GlobalFnsSt → ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] (D : DegPre R) (T : Over (Spec (CommRingCat.of R))) (k : ℕ) (α mu : D.X), ∃ (u₀ : LB.Gen (LB.LinComb D.P.L (deltaφT D (α + k • mu) α (toUnit T ≫ D.c mu)) (DegPre.deltaε k))) (r₁ r₂ : R), u₀.IsGen ∧ r₁ ≠ 0 ∧ r₂ ≠ 0 ∧ ∀ (F : Type) [Field F] [Algebra (FractionRing R) F] (φ : TF (R := R) F ⟶ T) (u : LB.Gen (LB.LinComb D.P.L (DegPre.deltaφ D F k α mu) (DegPre.deltaε k))), u.IsGen → LB.Gen.Corr D.P.L _ _ _ _ (LB.pullGen D.P.L _ _ u (DegPre.zF D F).left) (DegPre.famMult D F k mu α) → ∀ (Z : Scheme.{0}) (r : Z ⟶ (DegPre.BF D F).left) (z : Z) (J), Good D.P.L z J → gs r z ⊤ (scal (DegPre.BF D F).hom r₂) * (val u r z J).val = gs r z ⊤ (scal (DegPre.BF D F).hom r₁) * (val u₀ (r ≫ (φ ▷ D.P.A).left) z J).val := by
  intro hG R _ _ _ D T k α mu
  obtain ⟨v, hv⟩ := exists_gen_of_local (V := R) D.P.L D.P.isLB (basePts D (𝟙_ _) α mu) (baseExp k)
  obtain ⟨u₀, hu₀, vu₀⟩ := exists_genT D T (𝟙_ _) (toUnit _) k α mu v hv
  obtain ⟨r₁, r₂, h₁, h₂, hr⟩ := multK_frac D k α mu v hv
  refine ⟨u₀, r₁, r₂, hu₀, h₁, h₂, fun F _ _ φ u hu hc Z r z J hJ => ?_⟩
  let T' : Over (Spec (CommRingCat.of R)) := Over.mk (r ≫ (DegPre.BF D F).hom)
  let ρ : T' ⟶ DegPre.BF D F := Over.homMk r rfl
  let κ : T' ⟶ TK R := Over.homMk ((ρ ≫ fst _ _).left ≫ jFK (R := R) F)
    ((Category.assoc _ _ _).trans (Over.w (ρ ≫ fst _ _)))
  have e₁ := (gen_fe (D := D) (F := F) hG k mu α).2 u hu hc T' ρ z J hJ
  have e₂ := vu₀ T' (ρ ≫ φ ▷ D.P.A) z J hJ
  have e₃ : val (DegPre.famMult D F k mu α) (ρ ≫ fst _ _).left z J = val (multK D k mu α) κ.left z J :=
    val_pull hJ _ _ _
  have e₄ := hr _ κ.left z J hJ
  have e₅ : κ.left ≫ jK R = r ≫ (DegPre.BF D F).hom := Over.w κ
  have e₆ : κ.left ≫ (toUnit (TK R)).left = ((ρ ≫ φ ▷ D.P.A) ≫ toUnit _).left :=
    congrArg (fun q => q.left) (toUnit_unique (κ ≫ toUnit (TK R)) _)
  have e₇ : (ρ ≫ φ ▷ D.P.A) ≫ snd _ _ = ρ ≫ DegPre.prB D F := by rw [Category.assoc, whiskerRight_snd]
  have g : ∀ c : R, gs r z ⊤ (scal (DegPre.BF D F).hom c) =
      gs (r ≫ (DegPre.BF D F).hom) z ⊤ ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom c) := fun c =>
    gs_pull r (DegPre.BF D F).hom z ⊤ trivial _
  rw [e₅, e₆] at e₄
  rw [e₃, uVal, ← Category.assoc, comp_cP] at e₁
  rw [e₇] at e₂
  rw [g, g]
  exact frac_mul e₁ e₂ e₄

end GlobalTheory.UU.IntGen
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsGtPt
section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UU

noncomputable section

namespace GlobalTheory.UU.TorPtEx

theorem exists_gtPt {R : Type} [CommRing R] [IsDomain R] (D : DegPre R) (T : Over (Spec (CommRingCat.of R)))
    (a : Multiplicative D.X →* Γ(T.left, ⊤)ˣ) : ∃ g : GtPt D T, g.b = 1 ∧
      ∀ (χ : D.X) (Z : Scheme.{0}) (r : Z ⟶ T.left) (z : Z) (J), Good D.P.L z J →
        val (g.s χ) r z J = gm r z ⊤ (a (Multiplicative.ofAdd χ)) := by
  have h1 : (LB.oneGen D.P.L (Y := T.left)).IsGen := fun _ _ =>
    (map_one _).trans ((congrArg₂ (· * ·) (Fintype.prod_empty _) (map_one _)).trans (_root_.mul_one _)).symm
  have key : ∀ χ : D.X, ∃ t : LB.Gen (LB.LinComb D.P.L (DegPre.gtφT D T 1 χ) DegPre.gtε), t.IsGen ∧
      ∀ (Z : Scheme.{0}) (r : Z ⟶ T.left) (z : Z) (J), Good D.P.L z J →
        val t r z J = gm r z ⊤ (a (Multiplicative.ofAdd χ)) := by
    intro χ
    obtain ⟨t, ht, hv⟩ := exists_gen D.P.isLB (φ' := DegPre.gtφT D T 1 χ) (ε' := DegPre.gtε) (fun U _ h => by
        have e₁ : padd D.P.A (DegPre.cT D T χ) 1 = DegPre.cT D T χ := _root_.mul_one (DegPre.cT D T χ)
        have e₂ : DegPre.zeroT D T = 1 := rfl
        simp [DegPre.gtφT, DegPre.gtε, Fin.prod_univ_succ, e₁, e₂])
      (DVR.scaleGen (a (Multiplicative.ofAdd χ)) (LB.oneGen D.P.L)) (DVR.scaleGen_isGen _ _ h1)
    refine ⟨t, ht, fun Z r z J hJ => (hv Z r z J hJ).trans ?_⟩
    exact ((map_mul _ _ _).trans (congrArg₂ (· * ·) (gm_res r z le_top (hJ.mem PEmpty.elim r) _) (val_one r))).trans
      (_root_.mul_one _)
  choose s hs hv using key
  refine ⟨⟨1, s, hs, corr_of_val D.P.isLB fun y J hJ => ?_, fun χ χ' => corr_of_val D.P.isLB fun y J hJ => ?_⟩, rfl, hv⟩
  · rw [hv 0 _ _ y J hJ, val_one, ofAdd_zero, map_one, map_one]
  · have c := (val_cub D.cub (𝟙 T) hJ (DegPre.cT D T χ) (DegPre.cT D T χ') 1).trans
      ((congrArg (cubV D.cub y J _ _) (Category.id_comp (1 : T ⟶ D.P.A))).trans ((isCub_cubV D.cub hJ).face₃ _ _))
    refine ((val_mul hJ _ _ _).trans (congrArg₂ (· * ·) (hv _ _ _ y J hJ) c)).trans
      (Eq.trans ?_ ((val_mul hJ _ _ _).trans (congrArg₂ (· * ·) (hv _ _ _ y J hJ) (hv _ _ _ y J hJ))).symm)
    rw [_root_.mul_one, ofAdd_add, map_mul, map_mul]; rfl

theorem main : AllPre fun {V} _ _ _ {D} {_} {G} _ _ U => ∀ (W : Type) [CommRing W] [IsLocalRing W] [Algebra V W], FinExt V W → ∀ a : Multiplicative D.X →* Wˣ, ∃ x : TA V W ⟶ G, U.TorPt a x := by
  intro V _ _ _ hV D A G _ _ U W _ _ _ hW a
  obtain ⟨g, hb, hv⟩ := exists_gtPt D (TA V W)
    ((Units.map (Scheme.ΓSpecIso (CommRingCat.of W)).inv.hom.toMonoidHom).comp a)
  obtain ⟨x, hx, -⟩ := RedOnto.main V hV D A G U W hW g
  refine ⟨x, fun e Z r xe h => ?_⟩
  obtain ⟨h₁, h₂⟩ := hx e Z r xe h
  refine ⟨hb ▸ h₁, fun χ z J hJ => ?_⟩
  rw [h₂ χ z J hJ, hv χ Z r z J hJ, gm_val r z ⊤ trivial, gs_eq _ z ⊤ trivial]
  rfl

end GlobalTheory.UU.TorPtEx

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsIndepCoords
section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory

namespace ExpansionSingleValued

open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR GlobalTheory.BoxIndep

theorem exists_indep_coords (R : Type) [CommRing R] [IsDomain R] (F : Type) [Field F]
    [Algebra (FractionRing R) F] [Algebra R F] [IsScalarTower R (FractionRing R) F] {Λ : Type} [Fintype Λ] (c : Λ → F) :
    ∃ (κ : Type) (_ : Fintype κ) (b : κ → F) (a : Λ → κ → R), LinearIndependent R b ∧ ∀ i, c i = ∑ l, a i l • b l := by
  classical
  let B := Module.Basis.ofVectorSpace (FractionRing R) F
  let S := Finset.univ.biUnion fun i => (B.repr (c i)).support
  obtain ⟨d, hd⟩ := IsLocalization.exist_integer_multiples_of_finite (nonZeroDivisors R)
    (fun p : Λ × S => B.repr (c p.1) p.2)
  choose a ha using hd
  have hd0 : algebraMap R (FractionRing R) d ≠ 0 := (IsLocalization.map_units _ d).ne_zero
  refine ⟨S, inferInstance, fun l => (algebraMap R (FractionRing R) d)⁻¹ • B l, fun i l => a (i, l), ?_, fun i => ?_⟩
  · refine LinearIndependent.restrict_scalars' (K := FractionRing R) R ?_
    exact (B.linearIndependent.comp (fun l : S => l.1) Subtype.val_injective).units_smul
      (fun _ => (Units.mk0 _ hd0)⁻¹)
  · have h : ∀ l : S, a (i, l) • (algebraMap R (FractionRing R) d)⁻¹ • B l = B.repr (c i) l • B l := fun l => by
      rw [← algebraMap_smul (FractionRing R), ha, smul_smul, Algebra.smul_def (d : R), mul_right_comm,
        mul_inv_cancel₀ hd0, _root_.one_mul]
    simp only [h]
    rw [Finset.sum_coe_sort S (fun l => B.repr (c i) l • B l)]
    conv_lhs => rw [← B.linearCombination_repr (c i), Finsupp.linearCombination_apply]
    exact Finsupp.sum_of_support_subset _ (Finset.subset_biUnion_of_mem (fun i => (B.repr (c i)).support) (Finset.mem_univ i)) _
      (fun _ _ => zero_smul _ _)

theorem flat_germOf {R : Type} [CommRing R] {X : Scheme.{0}} (p : X ⟶ Spec (CommRingCat.of R)) [Flat p] (x : X) :
    (germOf p x).Flat := by
  have e : germOf p x = (p.stalkMap x).hom.comp
      (((Sp R).presheaf.germ ⊤ (p x) trivial).hom.comp (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom) :=
    RingHom.ext fun c => by
      rw [germOf_apply, gs_stalkMap p x ⊤ trivial, gs_eq _ _ ⊤ trivial]; rfl
  rw [e]
  refine RingHom.Flat.comp (RingHom.Flat.comp (RingHom.Flat.of_bijective
    (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (CommRingCat.of R)).inv)) ?_) (Flat.stalkMap p x)
  have hU := isAffineOpen_top (Sp R)
  let _ := (Sp R).presheaf.algebra_section_stalk (U := ⊤) ⟨p x, trivial⟩
  have := hU.isLocalization_stalk ⟨p x, trivial⟩
  exact IsLocalization.flat ((Sp R).presheaf.stalk ((⟨p x, trivial⟩ : (⊤ : (Sp R).Opens)) : Sp R))
    (hU.primeIdealOf ⟨p x, trivial⟩).asIdeal.primeCompl

theorem split_relation {R F : Type} [CommRing R] [CommRing F] [Algebra R F] {X : Scheme.{0}}
    (p : X ⟶ Spec (CommRingCat.of R)) [Flat p] (x : X) {U : X.Opens} (hx : x ∈ U) {Λ κ : Type} [Fintype Λ] [Fintype κ]
    (b : κ → F) (hb : LinearIndependent R b) (a : Λ → κ → R) (s : Λ → Γ(X, U))
    (H : ∀ (Z : Scheme.{0}) (q : Z ⟶ Spec (CommRingCat.of F)) (r : Z ⟶ X),
      r ≫ p = q ≫ Spec.map (CommRingCat.ofHom (algebraMap R F)) → ∀ z, r z ∈ U →
        ∑ i, germOf q z (∑ l, a i l • b l) * gs r z U (s i) = 0) (l : κ) :
    ∑ i, germOf p x (a i l) * gs (𝟙 X) x U (s i) = 0 := by
  let O : Type := X.presheaf.stalk x
  let : Algebra R O := (germOf p x).toAlgebra
  have : Module.Flat R O := flat_germOf p x
  have hi : LinearIndependent O (fun l => (1 : O) ⊗ₜ[R] b l) := Module.Flat.linearIndependent_one_tmul hb
  refine Fintype.linearIndependent_iff.1 hi (fun l => ∑ i, germOf p x (a i l) * gs (𝟙 X) x U (s i)) ?_ l
  let eL : O →+* TensorProduct R O F := Algebra.TensorProduct.includeLeftRingHom
  let eR : F →+* TensorProduct R O F := (Algebra.TensorProduct.includeRight (R := R) (A := O) (B := F)).toRingHom
  refine eq_zero_of_germOf (B := CommRingCat.of (TensorProduct R O F)) _ fun z => ?_
  have h := H (Spec (CommRingCat.of (TensorProduct R O F))) (Spec.map (CommRingCat.ofHom eR))
    ((Spec.map (CommRingCat.ofHom eL) : _ ⟶ Spec (X.presheaf.stalk x)) ≫ X.fromSpecStalk x) (by
      rw [Category.assoc, fromSpecStalk_comp]
      refine (Spec.map_comp _ _).symm.trans (Eq.trans (congrArg Spec.map ?_) (Spec.map_comp _ _))
      ext r
      exact (Algebra.TensorProduct.tmul_one_eq_one_tmul (R := R) (A := O) (B := F) r)) z (fromSpecStalk_mem x hx _)
  have e : ∑ l, (∑ i, germOf p x (a i l) * gs (𝟙 X) x U (s i)) • ((1 : O) ⊗ₜ[R] b l) =
      ∑ i, eR (∑ l, a i l • b l) * eL (gs (𝟙 X) x U (s i)) := by
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [Finset.sum_smul, map_sum, Finset.sum_mul]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun l _ => ?_
    show _ = ((1 : O) ⊗ₜ[R] (a i l • b l)) * ((gs (𝟙 X) x U (s i) : O) ⊗ₜ[R] (1 : F))
    rw [Algebra.TensorProduct.tmul_mul_tmul, _root_.one_mul, _root_.mul_one, TensorProduct.tmul_smul,
      TensorProduct.smul_tmul', TensorProduct.smul_tmul', smul_eq_mul, _root_.mul_one]
    rfl
  set_option synthInstance.maxHeartbeats 100000 in
    rw [e, ← h, map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [map_mul]
  congr 1
  · rw [← Category.id_comp (Spec.map _), germOf_map]; rfl
  · rw [gs_fromSpecStalk x hx]
    exact (germOf_map (B := X.presheaf.stalk x) (𝟙 _) (CommRingCat.ofHom eL) z _).symm

theorem gs_scal {R : Type} [CommRing R] {X Z : Scheme.{0}} (p : X ⟶ Spec (CommRingCat.of R)) (r : Z ⟶ X) (z : Z)
    (a : R) : gs r z ⊤ (scal p a) = germOf (r ≫ p) z a :=
  (gs_pull r p z ⊤ trivial _).trans (germOf_apply _ _ _).symm

theorem gs_scal_comb {R : Type} [CommRing R] {X Z : Scheme.{0}} (p : X ⟶ Spec (CommRingCat.of R)) (r : Z ⟶ X) (z : Z)
    {U : X.Opens} (hz : r z ∈ U) {Λ : Type} [Fintype Λ] (a : Λ → R) (s : Λ → Γ(X, U)) :
    gs r z U (∑ i, resTop U (scal p (a i)) * s i) = ∑ i, germOf (r ≫ p) z (a i) * gs r z U (s i) := by
  rw [gs_fsum r z U hz]
  exact Finset.sum_congr rfl fun i _ => by rw [gs_mul r z U hz, gs_res r z le_top hz, gs_scal]

theorem sum_append {F O T : Type} [CommRing F] [CommRing O] (g : F →+* O) {n n' : ℕ} (c : Fin n → F) (c' : Fin n' → F)
    (t : Fin n → T) (t' : Fin n' → T) (v : T → O) :
    ∑ i, g (Fin.append c (-c') i) * v (Fin.append t t' i) =
      ∑ i, g (c i) * v (t i) - ∑ i, g (c' i) * v (t' i) := by
  simp only [Fin.sum_univ_add, Fin.append_left, Fin.append_right, Pi.neg_apply, map_neg, neg_mul,
    Finset.sum_neg_distrib, sub_eq_add_neg]

end ExpansionSingleValued


open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR GlobalTheory.BoxIndep ExpansionSingleValued in
theorem expandsG_unique : ∀ (R : Type) [CommRing R] [IsDomain R] (I : Ideal R), AdmBase R I → ∀ (D : DegData R I) (A : PolAV (Spec (CommRingCat.of (FractionRing R)))) (G : Over (Spec (CommRingCat.of R))) [GrpObj G] [IsCommMonObj G] (U : UnifPre I D A G) (k : ℕ) (F : Type) [Field F] [Algebra (FractionRing R) F] (σ : U.SecGF F k) (s s₂ : Fam D.toPre F k), U.ExpandsG F k σ s → U.ExpandsG F k σ s₂ → s = s₂ := by
  intro R _ _ I hR D A G _ _ U k F _ _ σ s s₂ ⟨n, c, τ, f, hE, hG, hB⟩ ⟨n', c', τ', f', hE', hG', hB'⟩
  let : Algebra R F := ((algebraMap (FractionRing R) F).comp (algebraMap R (FractionRing R))).toAlgebra
  have : IsScalarTower R (FractionRing R) F := IsScalarTower.of_algebraMap_eq' rfl
  have hj : jFK (R := R) F ≫ jK R = Spec.map (CommRingCat.ofHom (algebraMap R F)) :=
    (Spec.map_comp _ _).symm
  obtain ⟨κ, _, b, a, hb, ha⟩ := exists_indep_coords R F (Fin.append c (-c'))
  have := U.smooth
  have hz : ∀ l α j, ∑ i, resTop _ (scal D.toPre.P.A.hom (a i l)) * (Fin.append f f' i α).f j = 0 := fun l => by
    refine (comb_eq_zero_iff_expansion_comb_eq_zero R I hR D A G U k _ (fun i => a i l) (Fin.append τ τ')
      (Fin.append f f') (fun i => ?_)).1 fun j => ?_
    · refine Fin.addCases (fun i => ?_) (fun i => ?_) i
      · simpa only [Fin.append_left] using hE i
      · simpa only [Fin.append_right] using hE' i
    refine fn_ext fun x hx => (gs_scal_comb G.hom (𝟙 _) x hx _ _).trans (Eq.trans ?_ (gs_zero _ _ _ hx).symm)
    rw [Category.id_comp]
    refine split_relation G.hom x hx b hb a (fun i => (Fin.append τ τ' i).f j) (fun Z q r hr z hz => ?_) l
    let ρ₀ : Z ⟶ pullback G.hom (jK R) := pullback.lift r (q ≫ jFK (R := R) F) (by rw [hr, Category.assoc, hj])
    let ρ : Z ⟶ (UnifPre.GF (G := G) F).left := pullback.lift q ρ₀ (pullback.lift_snd _ _ _).symm
    have e₁ : ρ ≫ (fst (TFK (R := R) F) ((Over.pullback (jK R)).obj G)).left = q := pullback.lift_fst _ _ _
    have e₂ : ρ ≫ UnifPre.gFK (G := G) F = r :=
      (Category.assoc _ _ _).symm.trans ((congrArg (· ≫ pullback.fst G.hom (jK R)) (pullback.lift_snd _ _ _)).trans
        (pullback.lift_fst _ _ _))
    obtain ⟨J, hJ, eJ⟩ := exists_good U.LG.L U.LG.isLB z (fun _ : Fin 1 => r ≫ 𝟙 _) j
      (fun u v _ => congrArg j (Subsingleton.elim u v)) (fun u => Set.mem_iInter.1 hz u)
    have h₁ := ExpGTrans.secLin_val hG ρ z hJ
    have h₂ := ExpGTrans.secLin_val hG' ρ z hJ
    simp only [gs_scal, e₂, sval_of _ r z J j eJ] at h₁ h₂
    simp only [← ha]
    refine (sum_append (germOf q z) c c' τ τ' (fun t => gs r z _ (t.f j))).trans (sub_eq_zero.2 ?_)
    rw [← e₁]
    exact h₁.symm.trans h₂
  refine fam_ext fun α => sec_ext_val D.toPre.P.isLB fun y J hJ => ?_
  rw [ExpGTrans.secLin_val (hB α) _ y hJ, ExpGTrans.secLin_val (hB' α) _ y hJ]
  simp only [gs_scal]
  set q := 𝟙 _ ≫ (fst (TF (R := R) F) D.toPre.P.A).left
  set r := 𝟙 _ ≫ (DegPre.prB D.toPre F).left
  have e : r ≫ D.toPre.P.A.hom = q ≫ Spec.map (CommRingCat.ofHom (algebraMap R F)) := by
    rw [Category.assoc, Category.assoc, Over.w, ← hj]
    exact congrArg _ (Over.w (fst (TF (R := R) F) D.toPre.P.A)).symm
  refine sub_eq_zero.1 ((sum_append (germOf q y) c c' f f' (fun t => sval (t α) r y J)).symm.trans ?_)
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [ha, map_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_eq_zero fun l _ => ?_
  have hm := hJ.mem (D.toPre.famφB α) r
  have h := (gs_scal_comb D.toPre.P.A.hom r y hm _ _).symm.trans
    ((congrArg _ (hz l α _)).trans (gs_zero _ _ _ hm))
  refine Eq.trans (Finset.sum_congr rfl fun i _ => ?_) ((Finset.mul_sum _ _ (germOf q y (b l))).symm.trans
    ((congrArg _ h).trans (mul_zero _)))
  rw [Algebra.smul_def, map_mul, e, germOf_map, mul_comm (germOf q y _), _root_.mul_assoc]
  rfl

end GlobalTheory
end

