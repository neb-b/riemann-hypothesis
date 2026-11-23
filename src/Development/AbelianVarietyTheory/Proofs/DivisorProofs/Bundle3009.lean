module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2970
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsDominantToUnitLeft
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2175
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CubeVal
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2407
public import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.ValuationThetaRatioEqBilinear
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2990
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0060
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0071
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ToroidalCompactificationBis
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2864
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2992
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.Bundle0008
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.Bundle0003
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.PullUUnitsCompatGeneric
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0061
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsThetaCompact
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0062
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0064
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2901
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1196
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1417
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2921
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2940
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2966
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3000
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2904
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2981
public import Development.AbelianVarietyTheory.Definitions.Divisors.HasRigidCoords
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2978
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0493
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2982
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2939
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2954
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsToricRankOne
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0212
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2984

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsGeneratorTransportDownLineBundleIso
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.UPoinc GlobalTheory.TorRef
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.USep
open GlobalTheory.Poinc.ThetaOne GlobalTheory.Poinc.Sep GlobalTheory.UT GlobalTheory.FieldBaseChange

namespace GlobalTheory.GenTransport

theorem exists_gen_down_pmaps : ∀ {X X' Y : Scheme.{0}} {L : LB X} {L' : LB X'} {F : X' ⟶ X} {Ix : Type} [Fintype Ix]
    (w : LB.Iso L' (L.pull F)), w.IsGen → L.IsLB → L'.IsLB → ∀ (φ' : Ix → (Y ⟶ X')) (ε : Ix → ℤ)
    (a : LB.Gen (LB.LinComb L' φ' ε)), a.IsGen →
    ∃ t : LB.Gen (LB.LinComb L (fun k => φ' k ≫ F) ε), t.IsGen ∧ PMaps w φ' (fun k => φ' k ≫ F) ε a t (𝟙 Y) := by
  intro X X' Y L L' F Ix _ w hw hL hL' φ' ε a ha
  obtain ⟨t, ht, hv⟩ := ReciprocityTheory.ChartRestriction.G.Geo.Tor.exists_up ((isGen_iff w).1 hw) hL hL' a ha
  refine ⟨t, ht, fun Z r z p q hp hq => ?_⟩
  rw [Category.comp_id]
  exact hv Z r z p q (Set.mem_iInter.2 hp) (Set.mem_iInter.2 hq)

end GlobalTheory.GenTransport
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIntegralGeneratorTranslationBundleMonomial
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj Matrix TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.KS (rsT pbT C1 IsCoc IsCob)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.RayEv (Ray)
open GlobalTheory.Toroidal GlobalTheory.LogKS GlobalTheory.LogKSChart GlobalTheory.Heat
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

noncomputable section
namespace GlobalTheory.ShiftGen

open ReciprocityTheory.ChartRestriction.G.DVR

variable {R : Type} [CommRing R] [IsDomain R]

theorem exists_psi_gen [IsLocalRing R] (D : DegPre R) (χ : D.X) (u : Rˣ) (a : R) (h : PsiCoord D χ (u * a)) :
    ∃ (e : LB.Gen (LB.LinComb D.P.L (K := PUnit) (fun _ => (D.c χ).left) (fun _ => -1))), e.IsGen ∧
      ∀ (Z : Scheme.{0}) (r : Z ⟶ (TK R).left) (z : Z) (J : (Z ⟶ D.P.A.left) → D.P.L.ι), Good D.P.L z J →
        (val (D.psi χ) r z J).val = gs (r ≫ jK R) z ⊤ ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom a) *
          (val e (r ≫ jK R) z J).val := by
  have hL := D.P.isLB
  obtain ⟨e, he⟩ := exists_gen_of_local (V := R) D.P.L hL (K := PUnit) (fun _ => (D.c χ).left) (fun _ => -1)
  obtain ⟨j, hj, le', hψ⟩ := h
  have le : (⊤ : (Spec (CommRingCat.of R)).Opens) ≤ LB.wchart D.P.L (K := PUnit) (fun _ => (D.c χ).left) j :=
    fun y hy => Set.mem_iInter.2 fun _ => hj hy
  have hx : D.xK χ = jK R ≫ (D.c χ).left := by
    simp [DegPre.xK, ptK]
  have hto : ∀ a, DegPre.toOpen (R := R) ⊤ a = (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom a := fun a => by
    simp [DegPre.toOpen]
  let cu : Γ(Spec (CommRingCat.of R), ⊤)ˣ := Units.map (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom.toMonoidHom u
  let c : Γ(Spec (CommRingCat.of R), ⊤)ˣ := cu * (res le (e.s j))⁻¹
  refine ⟨DVR.scaleGen c e, DVR.scaleGen_isGen c e he, fun Z r z J hJ => ?_⟩
  have m₁ : r z ∈ LB.wchart D.P.L (K := PUnit) (fun _ => D.xK χ) j := le' trivial
  have m₂ : (r ≫ jK R) z ∈ LB.wchart D.P.L (K := PUnit) (fun _ => (D.c χ).left) j := le trivial
  have e₁ : val (D.psi χ) r z J = _ := gen_trans (D.psi_gen χ) r z (hJ.mem _ r) m₁
  have e₂ : val (DVR.scaleGen c e) (r ≫ jK R) z J = _ :=
    gen_trans (DVR.scaleGen_isGen c e he) (r ≫ jK R) z (hJ.mem _ _) m₂
  have e₃ : trF (L := D.P.L) (K := PUnit) (fun _ => D.xK χ) (fun _ => -1) r z (fun _ => J (r ≫ D.xK χ)) j =
      trF (L := D.P.L) (K := PUnit) (fun _ => (D.c χ).left) (fun _ => -1) (r ≫ jK R) z
        (fun _ => J ((r ≫ jK R) ≫ (D.c χ).left)) j := by
    have hq : r ≫ D.xK χ = (r ≫ jK R) ≫ (D.c χ).left :=
      (congrArg (r ≫ ·) hx).trans (Category.assoc _ _ _).symm
    simp only [trF]
    rw [hq]
  have e₄ : (gm r z (LB.wchart D.P.L (K := PUnit) (fun _ => D.xK χ) j) ((D.psi χ).s j)).val =
      gs (r ≫ jK R) z ⊤ ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom (u * a)) := by
    refine (gs_unit r z _ m₁ _).symm.trans ((gs_res r z le' trivial _).symm.trans ?_)
    refine (congrArg (gs r z _) hψ.symm).trans ((gs_pull r (jK R) z ⊤ trivial _).trans ?_)
    rw [hto]
  have e₅ : gm (r ≫ jK R) z (LB.wchart D.P.L (K := PUnit) (fun _ => (D.c χ).left) j) ((DVR.scaleGen c e).s j) =
      gm (r ≫ jK R) z ⊤ cu := by
    refine (map_mul _ _ _).trans ((congrArg₂ (· * ·) (gm_res (r ≫ jK R) z le_top m₂ c)
      (gm_res (r ≫ jK R) z le trivial (e.s j)).symm).trans ?_)
    rw [← map_mul]
    exact congrArg _ (inv_mul_cancel_right _ _)
  have e₆ : (gm (r ≫ jK R) z ⊤ cu).val = gs (r ≫ jK R) z ⊤ ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom u) :=
    (gs_unit _ z ⊤ trivial cu).symm
  rw [e₁, e₂, Units.val_mul, Units.val_mul]
  erw [e₃, e₄, e₅]
  rw [e₆, map_mul, gs_mul _ z ⊤ trivial]
  ring

theorem val_tau_zero (D : DegPre R) (hB : D.TauBimult) (F : Type) [Field F] [Algebra (FractionRing R) F]
    {T : Over (Spec (CommRingCat.of R))} (σ : T ⟶ TF (R := R) F) {z : T.left}
    {J : (T.left ⟶ D.P.A.left) → D.P.L.ι} (hJ : Good D.P.L z J) (mu : D.X) :
    val (D.tau mu 0) (σ.left ≫ jFK (R := R) F) z J = 1 := by
  have C : IsCub (th D (T := T) z J) := isCub_cubV D.cub hJ
  have h0 : cP D T 0 = 1 := by simpa using cPoint_nsmul D T 0 0
  have h := tau_mul σ hJ hB 0 0 mu
  rw [h0, C.face, _root_.mul_one, add_zero] at h
  rw [tau_symm σ hJ]
  exact mul_eq_left.1 h.symm

theorem exists_integral_gen [IsLocalRing R] (D : DegPre R) (hB : D.TauBimult) (y : D.X) (N : ℕ) (v : Rˣ) (a : R)
    (h : PsiCoord D y (v * a)) (F : Type) [Field F] [Algebra (FractionRing R) F] :
    ∃ uR : LB.Gen (LB.LinComb D.P.L (Sum.elim (D.famφB (0 + N • y))
        (fun i => (𝟙 D.P.A * SectionScalarValuation.cQ D D.P.A y).left ≫ D.famφB 0 i)) (DegPre.deltaε N)), uR.IsGen ∧
      ∀ (u : LB.Gen (LB.LinComb D.P.L (DegPre.deltaφ D F N 0 y) (DegPre.deltaε N))), u.IsGen →
        LB.Gen.Corr D.P.L _ _ _ _ (LB.pullGen D.P.L _ _ u (DegPre.zF D F).left) (DegPre.famMult D F N y 0) →
        ∀ (z : (DegPre.BF D F).left) (J : ((DegPre.BF D F).left ⟶ D.P.A.left) → D.P.L.ι), Good D.P.L z J →
          (val u (𝟙 _) z J).val = gs ((DegPre.prB D F).left ≫ D.P.A.hom) z ⊤
            ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom (a ^ N)) * (val uR (DegPre.prB D F).left z J).val := by
  obtain ⟨e, he, hv⟩ := exists_psi_gen D y v a h
  have c₁ : ∀ χ, D.P.A.hom ≫ (D.c χ).left = (SectionScalarValuation.cQ D D.P.A χ).left := fun χ => by simp [SectionScalarValuation.cQ]
  have c₂ : D.P.A.hom ≫ eSec D.P.A = (1 : D.P.A ⟶ D.P.A).left := by
    rw [Hom.one_def]; simp [eSec]
  have h0 : SectionScalarValuation.cQ D D.P.A 0 = 1 := by simpa using SectionScalarValuation.cQ_nsmul D D.P.A 0 0
  obtain ⟨eB, heB, veB⟩ := SectionScalarValuation.exists_eB D N 0 y
    (LB.mulGen D.P.L _ _ _ _ (GeneratorPullback.powGen D.P.L _ _ e N)
      (GeneratorPullback.powGen D.P.L (K := PUnit) (fun _ => eSec D.P.A) (fun _ => 1) D.rig N))
    (mulGen_isGen _ _ _ _ _ _ _ (powGen_isGen _ _ _ _ he N) (powGen_isGen _ _ _ _ D.rig_gen N)) (fun U _ h => by
      simp only [Fintype.prod_sum_type, Sum.elim_inl, Sum.elim_inr, Fintype.prod_unique, c₁, c₂, h0, _root_.one_mul]
      apply Additive.ofMul.injective
      simp only [ofMul_mul, ofMul_inv, ofMul_zpow, ofMul_pow]
      module)
  refine ⟨eB, heB, fun u hu hc z J hJ => ?_⟩
  have vp : ∀ {K : Type} [Fintype K] {Y : Scheme.{0}} {φ : K → (Y ⟶ D.P.A.left)} {ε : K → ℤ}
      (t : LB.Gen (LB.LinComb D.P.L φ ε)) (r : (DegPre.BF D F).left ⟶ Y),
      val (GeneratorPullback.powGen D.P.L φ ε t N) r z J = val t r z J ^ N := fun t r => map_pow _ _ _
  have w₁ : ((fst (TF (R := R) F) D.P.A).left ≫ jFK (R := R) F) ≫ jK R = (DegPre.prB D F).left ≫ D.P.A.hom :=
    (Category.assoc _ _ _).trans ((Over.w (fst (TF (R := R) F) D.P.A)).trans (Over.w (DegPre.prB D F)).symm)
  have w₂ : (toUnit (TK R)).left = jK R := (Category.comp_id _).symm.trans (Over.w (toUnit (TK R)))
  have G := (gen_fe (F := F) GlobalTheory.SemiRigid.globalFns N y 0).2 u hu hc _ (𝟙 _) z J hJ
  have v₁ := veB _ (DegPre.prB D F) z J hJ
  have p₁ := hv _ ((fst (TF (R := R) F) D.P.A).left ≫ jFK (R := R) F) z J hJ
  have p₂ : val D.rigK ((fst (TF (R := R) F) D.P.A).left ≫ jFK (R := R) F) z J =
      val (K := PUnit) (φ := fun _ => eSec D.P.A) (ε := fun _ => 1) D.rig ((DegPre.prB D F).left ≫ D.P.A.hom) z J := by
    refine (val_pull hJ _ _ _).trans ?_
    rw [← w₁]
    exact congrArg (fun q => val (K := PUnit) (φ := fun _ => eSec D.P.A) (ε := fun _ => 1) D.rig
      (((fst (TF (R := R) F) D.P.A).left ≫ jFK (R := R) F) ≫ q) z J) w₂
  rw [w₁] at p₁
  rw [Over.id_left, Category.id_comp, val_famMult _ hJ, val_tau_zero D hB F _ hJ, vp, vp, p₂, uVal_id, comp_cP,
    _root_.one_mul] at G
  rw [val_mul hJ, vp, vp] at v₁
  have q : gs ((DegPre.prB D F).left ≫ D.P.A.hom) z ⊤ ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom (a ^ N)) =
      gs ((DegPre.prB D F).left ≫ D.P.A.hom) z ⊤ ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom a) ^ N := by
    rw [gs_eq _ z ⊤ trivial, gs_eq _ z ⊤ trivial, map_pow, map_pow, map_pow]
  rw [G, v₁, q]
  simp only [Units.val_mul, Units.val_pow_eq_pow_val, p₁, th, cP, SectionScalarValuation.cQ]
  ring

theorem exists_integral_gen_monomial : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (k : Type) [Field k] [CharZero k] (m d : ℕ) (t : SAB H (Sp (ChartRing k m d))) (P : PELUnif (maximalIdeal (ChartRing k m d)) t) (gam : Fin m → LinearMap.BilinForm ℤ P.D.toPre.X), IsMonomial P.D.toPre (bdParam k m d) gam → ∀ (y : P.D.toPre.X) (N : ℕ), 1 ≤ N → ∃ (Nv : Fin m → ℕ) (uR : LB.Gen (LB.LinComb P.D.toPre.P.L (Sum.elim (P.D.toPre.famφB (0 + N • y)) (fun i => (lift (toUnit P.D.toPre.P.A ≫ P.D.toPre.c y) (𝟙 P.D.toPre.P.A) ≫ μ[P.D.toPre.P.A]).left ≫ P.D.toPre.famφB 0 i)) (DegPre.deltaε N))), uR.IsGen ∧ ∀ (u : LB.Gen (LB.LinComb P.D.toPre.P.L (DegPre.deltaφ P.D.toPre (FractionRing (ChartRing k m d)) N 0 y) (DegPre.deltaε N))), u.IsGen → LB.Gen.Corr P.D.toPre.P.L _ _ _ _ (LB.pullGen P.D.toPre.P.L _ _ u (DegPre.zF P.D.toPre (FractionRing (ChartRing k m d))).left) (DegPre.famMult P.D.toPre (FractionRing (ChartRing k m d)) N y 0) → ∀ (z : (DegPre.BF P.D.toPre (FractionRing (ChartRing k m d))).left) (J : ((DegPre.BF P.D.toPre (FractionRing (ChartRing k m d))).left ⟶ P.D.toPre.P.A.left) → P.D.toPre.P.L.ι), Good P.D.toPre.P.L z J → (val u (𝟙 _) z J).val = gs ((DegPre.prB P.D.toPre (FractionRing (ChartRing k m d))).left ≫ P.D.toPre.P.A.hom) z ⊤ ((Scheme.ΓSpecIso (CommRingCat.of (ChartRing k m d))).inv.hom (∏ i, bdParam k m d i ^ Nv i)) * (val uR (DegPre.prB P.D.toPre (FractionRing (ChartRing k m d))).left z J).val := by
  intro E _ _ _ H k _ _ m d t P gam hM y N _
  obtain ⟨v, n, -, hc⟩ := hM y
  have hT : lift (toUnit P.D.toPre.P.A ≫ P.D.toPre.c y) (𝟙 P.D.toPre.P.A) ≫ μ[P.D.toPre.P.A] =
      𝟙 P.D.toPre.P.A * SectionScalarValuation.cQ P.D.toPre P.D.toPre.P.A y :=
    mul_comm (SectionScalarValuation.cQ P.D.toPre P.D.toPre.P.A y) (𝟙 P.D.toPre.P.A)
  rw [hT]
  obtain ⟨uR, h₁, h₂⟩ := exists_integral_gen P.D.toPre P.D.tau_bimult y N v _ hc (FractionRing (ChartRing k m d))
  refine ⟨fun i => n i * N, uR, h₁, fun u hu hcu z J hJ => ?_⟩
  rw [h₂ u hu hcu z J hJ, ← Finset.prod_pow]
  simp only [pow_mul]

end GlobalTheory.ShiftGen
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIntegralHodgeBundleGenerator
section
set_option autoImplicit false
noncomputable section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.Poinc
open ReciprocityTheory.AnForm.R
open scoped CategoryTheory.Obj
open GlobalTheory.SiegJoin
attribute [local instance] Over.cartesianMonoidalCategory

open GlobalTheory.VB GlobalTheory.LieVB GlobalTheory.HodgeFrameGen
open GlobalTheory.QCoh (pullbackSections)

namespace GlobalTheory.HodgeFrameGen

theorem exists_isFrame_top_of_isLocalRing (R : Type) [CommRing R] [IsLocalRing R] (F : (Sp R).Modules) {r : ℕ}
    (h : IsVB F r) : ∃ e : Fin r → Γ(F, ⊤), IsFrame e := by
  obtain ⟨U, e, hx, he⟩ := h (IsLocalRing.closedPoint R)
  have hU : U = ⊤ := by
    refine top_le_iff.1 fun p _ => ?_
    exact (IsLocalRing.specializes_closedPoint p).mem_open U.isOpen hx
  subst hU
  exact ⟨e, he⟩

theorem spMap_jK {R W : Type} [CommRing R] [IsDomain R] [CommRing W] [IsDomain W] (φ : R →+* W)
    (gam : FractionRing R →+* FractionRing W) (hgam : ∀ r, gam (algebraMap R _ r) = algebraMap W _ (φ r)) :
    spMap gam ≫ jK R = jK W ≫ spMap φ := by
  have e : gam.comp (algebraMap R (FractionRing R)) = (algebraMap W (FractionRing W)).comp φ :=
    RingHom.ext hgam
  simp only [spMap, jK, ← Spec.map_comp, ← CommRingCat.ofHom_comp, e]

theorem relDim {S' : Scheme.{0}} {g : ℕ} {G : Over S'} [GrpObj G] (hGg : SmoothOfRelativeDimension g G.hom)
    {R : Type} [CommRing R] [IsDomain R] {G₁ : Over (Sp R)} [GrpObj G₁] (hG₁ : IsSemiAbelian G₁)
    {y : Sp (FractionRing R) ⟶ S'} {α : pullback G₁.hom (jK R) ⟶ G.left}
    (hα : IsGrpPullback ((Over.pullback (jK R)).obj G₁) G y α) : SmoothOfRelativeDimension g G₁.hom := by
  have := hG₁.smooth
  have h₁ : SmoothOfRelativeDimension g ((Over.pullback (jK R)).obj G₁).hom :=
    (smoothOfRelativeDimension_isStableUnderBaseChange g).of_isPullback hα.1 hGg
  exact GlobalTheory.SmoothRelDim.smoothOfRelativeDimension_of_generic R G₁ (FractionRing R)
    (algebraMap R (FractionRing R)) (IsFractionRing.injective R (FractionRing R)) g h₁

theorem exists_integral_hodgeGen : ∀ (S' : Scheme.{0}) (g : ℕ) (G : Over S') [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → SmoothOfRelativeDimension g G.hom → ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] [IsNoetherianRing R] [IsIntegrallyClosed R] (G₁ : Over (Sp R)) [GrpObj G₁] [IsCommMonObj G₁], IsSemiAbelian G₁ → ∀ (y : Sp (FractionRing R) ⟶ S') (α : pullback G₁.hom (jK R) ⟶ G.left), IsGrpPullback ((Over.pullback (jK R)).obj G₁) G y α → ∃ e₀ : LB.Gen ((hodge G g).pull y), e₀.IsGen ∧ ∀ (W : Type) [CommRing W] [IsDomain W] [IsLocalRing W], GlobalTheory.LN.CDvr W → ∀ (φ : R →+* W) (gam : FractionRing R →+* FractionRing W), (∀ r, gam (algebraMap R _ r) = algebraMap W _ (φ r)) → ∀ χ' : Sp W ⟶ S', spMap gam ≫ y = jK W ≫ χ' → ∃ e₀' : LB.Gen ((hodge G g).pull χ'), e₀'.IsGen ∧ ∀ (z : Sp (FractionRing W)) (J : (Sp (FractionRing W) ⟶ S') → (hodge G g).ι), Good (hodge G g) z J → val (L := hodge G g) (φ := fun _ : PUnit => y) (ε := fun _ => 1) e₀ (spMap gam) z J = val (L := hodge G g) (φ := fun _ : PUnit => χ') (ε := fun _ => 1) e₀' (jK W) z J := by
  intro S' g G _ _ hG hGg R _ _ _ _ _ G₁ _ _ hG₁ y α hα
  haveI := hG; haveI := hG₁
  haveI : SmoothOfRelativeDimension g G₁.hom := relDim hGg hG₁ hα
  obtain ⟨ε, hε⟩ := exists_isFrame_top_of_isLocalRing R (omega G₁) (isVB_omega G₁ g)
  have p₁ := isGrpPullback_pullback G₁ (jK R)
  have ha : IsFrame fun i => (omegaBase p₁).app ⊤ (pullbackSections (jK R) _ le_top (ε i)) :=
    (GlobalTheory.BadPt.Fibre.frame_pb (jK R) hε le_top).map_iso _
  refine ⟨gen hα ha, _root_.GlobalTheory.HodgeFrameGen.gen_isGen hα ha, ?_⟩
  intro W _ _ _ hW φ gam hgam χ' hχ
  haveI : IsDiscreteValuationRing W := hW.1
  obtain ⟨ρ', ψ', hρ', hψ', e₁, e₂⟩ := _root_.GlobalTheory.HodgeFrameGen.traitPullback_identification hG hG₁ hα φ gam hgam χ' hχ
  have pW := isGrpPullback_pullback G₁ (spMap φ)
  have ha' : IsFrame fun i => (omegaBase pW).app ⊤ (pullbackSections (spMap φ) _ le_top (ε i)) :=
    (GlobalTheory.BadPt.Fibre.frame_pb (spMap φ) hε le_top).map_iso _
  refine ⟨gen hψ' ha', _root_.GlobalTheory.HodgeFrameGen.gen_isGen hψ' ha', fun z J hJ => ?_⟩
  have q := isGrpPullback_pullback ((Over.pullback (jK R)).obj G₁) (spMap gam)
  have hA := q.comp hα
  have hq₁ := q.comp p₁
  have hb : IsFrame fun i => (omegaBase hq₁).app ⊤ (pullbackSections (spMap gam ≫ jK R) _ le_top (ε i)) :=
    (GlobalTheory.BadPt.Fibre.frame_pb _ hε le_top).map_iso _
  refine (GlobalTheory.T.hodge_frame_generator_value_pullback hα ha (spMap gam) q _ _ hA rfl rfl hb (fun i => ?_) z J hJ).trans
    (GlobalTheory.T.hodge_frame_generator_value_pullback hψ' ha' (jK W) hρ' _ _ hA hχ.symm e₁ hb (fun i => ?_) z J hJ).symm
  · exact (GlobalTheory.BadPt.Fibre.omegaBase_comp p₁ q hq₁ rfl rfl le_top le_top le_top (ε i)).symm
  · exact (GlobalTheory.BadPt.Fibre.omegaBase_comp pW hρ' hq₁ (spMap_jK φ gam hgam).symm e₂ le_top le_top le_top (ε i)).symm

end GlobalTheory.HodgeFrameGen
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIntegralShiftOfGeneratorUpToConst
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj Matrix TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.KS (rsT pbT C1 IsCoc IsCob)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.RayEv (Ray)
open GlobalTheory.Toroidal GlobalTheory.LogKS GlobalTheory.LogKSChart GlobalTheory.Heat
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.IntegralShift

theorem trF_prB {R : Type} [CommRing R] [IsDomain R] (Q : DegPre R) (y : Q.X) :
    (DegPre.trF Q (FractionRing R) y ≫ DegPre.prB Q (FractionRing R)).left =
      (DegPre.prB Q (FractionRing R)).left ≫ (lift (toUnit Q.P.A ≫ Q.c y) (𝟙 Q.P.A) ≫ μ[Q.P.A]).left := by
  rw [← Over.comp_left]
  congr 1
  have e₁ : DegPre.trF Q (FractionRing R) y ≫ DegPre.prB Q (FractionRing R) =
      DegPre.prB Q (FractionRing R) * (toUnit _ ≫ Q.c y) := lift_snd _ _
  have e₂ : (lift (toUnit Q.P.A ≫ Q.c y) (𝟙 Q.P.A) ≫ μ[Q.P.A]) = (toUnit Q.P.A ≫ Q.c y) * 𝟙 Q.P.A := rfl
  rw [e₁, e₂, MonObj.comp_mul, Category.comp_id, ← Category.assoc,
    toUnit_unique (DegPre.prB Q (FractionRing R) ≫ toUnit _) (toUnit _), mul_comm]

theorem sval_constFn_smul {R : Type} [CommRing R] {X Y Z : Scheme.{0}} {L : LB X} {K : Type} [Fintype K]
    {φ : K → (Y ⟶ X)} {ε : K → ℤ} (p : Y ⟶ Sp R) (s : LB.Sec (LB.LinComb L φ ε)) (a : R) (r : Z ⟶ Y) (z : Z)
    {J : (Z ⟶ X) → L.ι} (hJ : Good L z J) :
    sval (constFn p ⊤ a • s) r z J =
      gs (r ≫ p) z ⊤ ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom a) * sval s r z J := by
  have hm := hJ.mem φ r
  refine (gs_mul r z _ hm _ _).trans (congrArg₂ (· * ·)
      ((gs_res r z le_top hm _).trans ((GlobalTheory.HeatMod.gs_constFn_eq_germConstHom p r z a).trans ?_)) rfl)
  exact (gs_eq (r ≫ p) z ⊤ trivial _).symm

theorem exists_shift_of_gen : ∀ (R : Type) [CommRing R] [IsDomain R] (Q : DegPre R) (y : Q.X) (N : ℕ) (c : R) (uR : LB.Gen (LB.LinComb Q.P.L (Sum.elim (Q.famφB (0 + N • y)) (fun i => (lift (toUnit Q.P.A ≫ Q.c y) (𝟙 Q.P.A) ≫ μ[Q.P.A]).left ≫ Q.famφB 0 i)) (DegPre.deltaε N))), uR.IsGen → (∀ (u : LB.Gen (LB.LinComb Q.P.L (DegPre.deltaφ Q (FractionRing R) N 0 y) (DegPre.deltaε N))), u.IsGen → LB.Gen.Corr Q.P.L _ _ _ _ (LB.pullGen Q.P.L _ _ u (DegPre.zF Q (FractionRing R)).left) (DegPre.famMult Q (FractionRing R) N y 0) → ∀ (z : (DegPre.BF Q (FractionRing R)).left) (J : ((DegPre.BF Q (FractionRing R)).left ⟶ Q.P.A.left) → Q.P.L.ι), Good Q.P.L z J → (val u (𝟙 _) z J).val = gs ((DegPre.prB Q (FractionRing R)).left ≫ Q.P.A.hom) z ⊤ ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom c) * (val uR (DegPre.prB Q (FractionRing R)).left z J).val) → ∃ (w : ∀ (z : Q.P.A.left) (J : (Q.P.A.left ⟶ Q.P.A.left) → Q.P.L.ι), (Q.P.A.left.presheaf.stalk z)ˣ) (Sh : Q.SecB N 0 → Q.SecB N (0 + N • y)), ∀ x : Q.SecB N 0, (∀ (z : Q.P.A.left) (J : (Q.P.A.left ⟶ Q.P.A.left) → Q.P.L.ι), Good Q.P.L z J → sval (Sh x) (𝟙 _) z J = sval x (lift (toUnit Q.P.A ≫ Q.c y) (𝟙 Q.P.A) ≫ μ[Q.P.A]).left z J * (w z J).val) ∧ ∃ x₁ : Q.SecB N (0 + N • y), ShiftEq Q N y 0 x x₁ 0 x₁ ∧ ∀ (Z : Scheme.{0}) (X : Z ⟶ Q.P.A.left) (z : Z) (J : (Z ⟶ Q.P.A.left) → Q.P.L.ι), Good Q.P.L z J → sval x₁ X z J = gs (X ≫ Q.P.A.hom) z ⊤ ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom c) * sval (Sh x) X z J := by
  intro R _ _ Q y N c uR huR H
  have ex : ∀ x : Q.SecB N 0, ∃ s₁ : Q.SecB N (0 + N • y),
      ∀ (Z : Scheme.{0}) (r : Z ⟶ Q.P.A.left) (z : Z) (J), Good Q.P.L z J →
        sval s₁ r z J = sval x (r ≫ (lift (toUnit Q.P.A ≫ Q.c y) (𝟙 Q.P.A) ≫ μ[Q.P.A]).left) z J *
          (val uR r z J).val := fun x => by
    obtain ⟨s₁, h⟩ := exists_sec Q.P.isLB (φ' := Q.famφB (0 + N • y)) (ε' := DegPre.famε N) (fun U _ h => by
      simp only [DegPre.deltaε, Fintype.prod_sum_type, Sum.elim_inl, Sum.elim_inr, zpow_neg,
        Finset.prod_inv_distrib]
      rw [mul_left_comm, mul_inv_cancel, _root_.mul_one])
      (pullMulSec x (lift (toUnit Q.P.A ≫ Q.c y) (𝟙 Q.P.A) ≫ μ[Q.P.A]).left uR huR)
    exact ⟨s₁, fun Z r z J hJ => (h Z r z J hJ).trans (sval_pullMulSec _ _ _ _ _ _ hJ)⟩
  choose Sh hSh using ex
  refine ⟨fun z J => val uR (𝟙 _) z J, Sh, fun x => ⟨fun z J hJ => ?_, constFn Q.P.A.hom ⊤ c • Sh x, ?_,
    fun Z X z J hJ => sval_constFn_smul _ _ _ _ _ hJ⟩⟩
  · rw [hSh x _ _ z J hJ, Category.id_comp]
  · intro u hu hc z J hJ
    rw [GlobalTheory.HeatMod.gs_id_scal_eq_germConstHom, map_zero, zero_mul, add_zero, sval_constFn_smul _ _ _ _ _ hJ,
      hSh x _ _ z J hJ, H u hu hc z J hJ, trF_prB]
    ring

end GlobalTheory.IntegralShift
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIsPullDegIdSameCoordinatesStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.UChart GlobalTheory.UCanon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_isPullDeg_id_same_coordinates : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D' : Datum H} {l : Geo.Tor.Level H} {c : Coeff l} (L : LowBase D' c) {V : Type} [CommRing V] [IsDomain V] [IsLocalRing V] (Q : DegPre V) [Module (𝓞 E) Q.X] (oQ : letI := H.starRing; Q.OAct (𝓞 E)) (Q' : DegPre V) [Module (𝓞 E) Q'.X] (oQ' : letI := H.starRing; Q'.OAct (𝓞 E)) (iw : L.W →+* V) {I : Type} [Fintype I] (s : I → V) (ε : I → LinearMap.BilinForm ℤ L.D.X) (e : Q.X ≃ₗ[𝓞 E] L.D.X) (e' : Q'.X ≃ₗ[𝓞 E] L.D.X), (∀ k, s k ≠ 0) → DivFrom L Q oQ iw s ε e → DivFrom L Q' oQ' iw s ε e' → ∃ hD : IsPullDeg (RingHom.id V) Q Q', (∀ y, e (hD.xe y) = e' y) ∧ (letI := H.starRing; ∀ x, oQ'.onB.act x ≫ hD.e.hom = hD.e.hom ≫ (Over.pullback (specOf (RingHom.id V))).map (oQ.onB.act x)) := by
  first | exact @GlobalTheory.UCanon.DivIso.exists_isPullDeg_id | exact GlobalTheory.UCanon.DivIso.exists_isPullDeg_id | (intros; apply GlobalTheory.UCanon.DivIso.exists_isPullDeg_id <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIsometryExtendingIsotropicShear
section
noncomputable section

open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.LowDat GlobalTheory.LowFilt

namespace GlobalTheory.LowFilt

theorem IsOpp.exists_isometry_extend {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} (D : Datum H) (N : ℕ)
    (hN : 0 < N) (Z Z' : Submodule (𝓞 E) D.La) (h : IsOpp D Z Z') (t : Z →ₗ[𝓞 E] D.La)
    (ht : ∀ z : Z, ∃ e ∈ perp D Z', t z = (z : D.La) + N • e) (hiso : ∀ z z' : Z, D.EF (t z) (t z') = 0) :
    ∃ g : D.La →ₗ[𝓞 E] D.La, (∀ a b, D.EF (g a) (g b) = D.EF a b) ∧ (∀ a, ∃ e, g a = a + N • e) ∧
      ∀ z : Z, g z = t z := by
  set q := h.symm.proj with hq
  have hr : ∀ a, a - (q a : D.La) ∈ perp D Z' := fun a => h.symm.sub_proj_mem a
  have hδ : ∀ z : Z, t z - (z : D.La) ∈ perp D Z' := fun z => by
    obtain ⟨e, he, hz⟩ := ht z
    rw [hz, add_sub_cancel_left]
    exact nsmul_mem he N
  choose c hc hu using fun a : D.La => h.2.2.1 (AddMonoidHom.mk' (fun z : Z => D.EF (t z - z) (a - q a))
    fun z z' => by simp only [map_add (f := _), map_sub, Submodule.coe_add, LinearMap.add_apply, LinearMap.sub_apply]; abel)
  simp only [AddMonoidHom.mk'_apply] at hc hu
  let α : D.La →ₗ[𝓞 E] Z' :=
    { toFun := c
      map_add' := fun a a' => (hu _ _ fun z => by
        simp only [Submodule.coe_add, map_add (f := _), hc, map_sub, LinearMap.sub_apply, map_add (f := _)]
        abel).symm
      map_smul' := fun x a => (hu _ _ fun z => by
        have key : ∀ u w : D.La, D.EF u (x • w) = D.EF (H.bar x • u) w := fun u w => by rw [D.adj, bar_bar]
        simp only [RingHom.id_apply, Submodule.coe_smul, map_smul, ← smul_sub]
        rw [key, key, ← Submodule.coe_smul, hc, Submodule.coe_smul, map_smul, smul_sub]).symm }
  have hα : ∀ a, α a = c a := fun _ => rfl
  let g : D.La →ₗ[𝓞 E] D.La := LinearMap.id + (t - Z.subtype) ∘ₗ q - Z'.subtype ∘ₗ α
  have hg : ∀ a, g a = a + (t (q a) - q a) - c a := fun _ => rfl
  refine ⟨g, fun a a' => ?_, fun a => ?_, fun z => ?_⟩
  · have hZ : ∀ (x y : Z), D.EF x y = 0 := fun x y => h.1 x.2 _ y.2
    have hZ' : ∀ (x y : Z'), D.EF x y = 0 := fun x y => h.2.1 x.2 _ y.2
    have f1 := hZ' (c a) (c a')
    have f2 : D.EF (t (q a) - q a) (c a') = 0 := hδ (q a) _ (c a').2
    have f3 : D.EF (c a) (t (q a') - q a') = 0 := by
      rw [ef_swap, hδ (q a') _ (c a).2, neg_zero]
    have f4 := hiso (q a) (q a')
    have f5 := hZ (q a) (q a')
    have f7 : D.EF a (c a') = D.EF (t (q a) - q a) (a' - q a') := by
      have := hr a _ (c a').2
      rw [← hc a' (q a)]
      simp only [map_sub, LinearMap.sub_apply] at this
      linear_combination this
    have f8 : D.EF (c a) a' = D.EF (a - q a) (t (q a') - q a') := by
      have := hr a' _ (c a).2
      have h2 := hc a (q a')
      rw [ef_swap D (c a) a', ef_swap D (a - q a)]
      simp only [map_sub, LinearMap.sub_apply] at this h2 ⊢
      linear_combination -this - h2
    rw [hg, hg]
    simp only [map_add (f := _), map_sub, LinearMap.add_apply, LinearMap.sub_apply] at f2 f3 f7 f8 ⊢
    linear_combination f1 - f2 - f3 + f4 - f5 - f7 - f8
  · obtain ⟨e, -, he⟩ := ht (q a)
    obtain ⟨e', he'⟩ := GlobalTheory.ModuliGenus.exists_eq_nsmul_of_dvd D hN (c a : D.La) fun b => by
      obtain ⟨e₁, -, he₁⟩ := ht (q b)
      have h1 : D.EF (c a) (b - q b) = 0 := by rw [ef_swap, hr b _ (c a).2, neg_zero]
      have h2 := hc a (q b)
      rw [he₁, add_sub_cancel_left, map_nsmul, LinearMap.smul_apply] at h2
      refine ⟨-D.EF e₁ (a - q a), ?_⟩
      have h3 : D.EF (c a) b = D.EF (c a) (q b) := by
        rw [map_sub] at h1; linear_combination h1
      rw [h3, ef_swap, h2, nsmul_eq_mul]
      ring
    refine ⟨e - e', ?_⟩
    rw [hg, he, he', smul_sub]
    abel
  · have hqz : q z = z := Subtype.ext (h.symm.proj_of_mem z.2)
    have hcz : c z = 0 := (hu z 0 fun z' => by simp [hqz]).symm
    rw [hg, hqz, hcz]
    simp

end GlobalTheory.LowFilt
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLevelIsometryExtensionAlgClosedStatement
section
noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.LowDat GlobalTheory.LowFilt
open scoped CategoryTheory.Obj

attribute [local instance] Over.cartesianMonoidalCategory

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_levelIsometry_extension_algClosed : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H} (Xo : Moduli Dw l) (c : Coeff l) (R : Type) [CommRing R] [IsDomain R]
    [IsLocalRing R], GlobalTheory.Mum.Base R → ∀ (C : GlobalTheory.UChart.Fam Xo c R) (tK : SAB H (Sp (FractionRing R)))
    (m1 : SABMap tK C.t (jK R)) (m2 : SABMap tK Xo.univ.t (C.y ≫ pullback.fst _ _))
    (I₀ : letI := H.starRing; TateIsoQ Dw C.P.D.toPre C.P.oD (AlgebraicClosure (FractionRing R))),
    GlobalTheory.LowDat.XFLevel C tK m1 m2 (AlgebraicClosure (FractionRing R)) I₀ →
    ∀ (F : Type) [Field F] [IsAlgClosed F] [Algebra (FractionRing R) F],
    ∃ I : (letI := H.starRing; TateIsoQ Dw C.P.D.toPre C.P.oD F), GlobalTheory.LowDat.XFLevel C tK m1 m2 F I ∧
      ∀ n a, (I.ev n a).y = (I₀.ev n a).y := by
  first | exact @GlobalTheory.LowDat.exists_xfLevel_ext | exact GlobalTheory.LowDat.exists_xfLevel_ext | (intros; apply GlobalTheory.LowDat.exists_xfLevel_ext <;> assumption)
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLinearUniformisationPullbackLocalMapStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.UChart GlobalTheory.UCanon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_linearUniformisation_pullback_localMap : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} (R V : Type) [CommRing R] [IsDomain R] [IsLocalRing R] [CommRing V] [IsDomain V] [IsLocalRing V], GlobalTheory.Mum.Base R → GlobalTheory.Mum.Base V → ∀ (t : SAB H (Sp R)) (P : PELUnif (maximalIdeal R) t) (θ : R →+* V), IsLocalHom θ → ∀ f : R, θ f ≠ 0 → (∀ y, PsiUnitOn P.D.toPre y (PrimeSpectrum.basicOpen f : Set (PrimeSpectrum R))) → ∃ (t' : SAB H (Sp V)) (P' : PELUnif (maximalIdeal V) t') (hD : IsPullDeg θ P.D.toPre P'.D.toPre), Nonempty (SABMap t' t (spMap θ)) ∧ (∀ (x : 𝓞 E) y, hD.xe (x • y) = x • hD.xe y) ∧ (letI := H.starRing; ∀ x, P'.oD.onB.act x ≫ hD.e.hom = hD.e.hom ≫ (Over.pullback (specOf θ)).map (P.oD.onB.act x)) := by
  first | exact @GlobalTheory.LocalPull.exists_pelUnif_pull | exact GlobalTheory.LocalPull.exists_pelUnif_pull | (intros; apply GlobalTheory.LocalPull.exists_pelUnif_pull <;> assumption)
end

