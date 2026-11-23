module

public import Mathlib
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.RigidSys
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CubeVal
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.Bundle0005
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.Bundle0006
public import Development.AbelianVarietyTheory.Definitions.Uniformization.Bundle0001
public import Development.AbelianVarietyTheory.Definitions.Uniformization.Bundle0002
public import Development.AbelianVarietyTheory.Definitions.Degenerations.Ser
public import Development.AbelianVarietyTheory.Definitions.Degenerations.RigGen
public import Development.AbelianVarietyTheory.Definitions.Uniformization.TXFrame
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.WchartLePreimage
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.LinCombTrivG
public import Development.AbelianVarietyTheory.Definitions.Uniformization.IsCPPullback

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Definitions.Degenerations.ExistsUniquePartner
section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section
namespace GlobalTheory.LN
open GlobalTheory.UU
variable {R V : Type} [CommRing R] [IsDomain R] [CommRing V] [IsDomain V] {I : Ideal R} {I' : Ideal V}
  {D : DegPre R} {D' : DegPre V} {A : PolAV (Spec (CommRingCat.of (FractionRing R)))} {A' : PolAV (Spec (CommRingCat.of (FractionRing V)))}
  {G : Over (Spec (CommRingCat.of R))} [GrpObj G] [IsCommMonObj G] {G' : Over (Spec (CommRingCat.of V))} [GrpObj G'] [IsCommMonObj G']

structure Cmp (φ : R →+* V) (U : PreU I D A G) (U' : PreU I' D' A' G') (F : G'.left ⟶ G.left) where

  pb : IsGrpPullback G' G (spMap φ) F

  wL : LB.Iso U'.P.L.L (U.P.L.L.pull F)

  wL_map : IsCPMap U'.P U.P (spMap φ) F pb.1.w wL

  β : D'.P.A.left ⟶ D.P.A.left

  pbB : IsGrpPullback D'.P.A D.P.A (spMap φ) β

  v : LB.Iso D'.P.L (D.P.L.pull β)

  v_gen : v.IsGen

  xe : D'.X ≃+ D.X

  c_pr : ∀ x, (D'.c x).left ≫ β = spMap φ ≫ (D.c (xe x)).left

  lev : ∀ (e : ℕ) (Z : Scheme.{0}) (x' : Z ⟶ (thickObj V I' e G').left) (x : Z ⟶ (thickObj R I e G).left),
    x ≫ (fstG I e G).left = x' ≫ (fstG I' e G').left ≫ F →
    x' ≫ (U'.gt e).pG.left ≫ β = x ≫ (U.gt e).pG.left ∧
    ∀ (z : Z) (J : (Z ⟶ D.P.A.left) → D.P.L.ι) (J' : (Z ⟶ D'.P.A.left) → D'.P.L.ι), Good D.P.L z J → Good D'.P.L z J' →
      (∀ χ : D'.X, val ((U.gt e).t (xe χ)) x z J = val ((U'.gt e).t χ) x' z J' *
        ∏ k : Fin 4, gw v (x' ≫ D'.Oφ (U'.gt e).pG χ k) z (J (x' ≫ D'.Oφ (U'.gt e).pG χ k ≫ β))
          (J' (x' ≫ D'.Oφ (U'.gt e).pG χ k)) ^ Oinvε k) ∧
      ∀ (k : U.P.L.L.ι) (k' : U'.P.L.L.ι), (fstG I e G).left (x z) ∈ U.P.L.L.U k → (fstG I' e G').left (x' z) ∈ U'.P.L.L.U k' →
        gw v (x' ≫ (U'.gt e).pG.left) z (J (x ≫ (U.gt e).pG.left)) (J' (x' ≫ (U'.gt e).pG.left)) *
            gw (U'.w e) x' z (J' (x' ≫ (U'.gt e).pG.left)) (fun _ => k') =
          gw (U.w e) x z (J (x ≫ (U.gt e).pG.left)) (fun _ => k) * gw wL (x' ≫ (fstG I' e G').left) z k k'

  map_le : I.map φ ≤ I' := by first | assumption | exact (Ideal.map_id _).le

def Under {D₀ : DegData R I} (U : PreU I D₀.toPre A G) (U₀ : UnifPre I D₀ A G) : Prop :=
  U.gen = U₀.gen ∧ U.P.L = U₀.LG ∧ HEq U.P.c U₀.cubG ∧ HEq U.P.sym U₀.symG ∧ U.gt = U₀.gt ∧ HEq U.w U₀.w

abbrev withPsi (D : DegPre R) (psi : ∀ χ : D.X, LB.Gen (LB.LinComb D.P.L (K := PUnit) (fun _ => ptK (D.c χ)) (fun _ => -1)))
    (h : ∀ χ, (psi χ).IsGen) : DegPre R := setPsi D psi h

namespace Cmp


omit [IsDomain R] in
theorem spMap_ringHom_id : spMap (RingHom.id R) = 𝟙 _ := by
  simp [spMap]

theorem grpPullback_id {S : Scheme.{0}} (H : Over S) [GrpObj H] {f : S ⟶ S} (hf : f = 𝟙 S) :
    IsGrpPullback H H f (𝟙 H.left) := by
  subst hf
  refine ⟨IsPullback.of_horiz_isIso ⟨by simp⟩, fun T x y x₀ y₀ hx hy => ?_⟩
  have hq : (𝟙 H : H ⟶ H).left ≫ H.hom = H.hom ≫ 𝟙 S := by simp
  have e₁ : x₀ = toBase hq x := Over.OverMorphism.ext hx
  have e₂ : y₀ = toBase hq y := Over.OverMorphism.ext hy
  rw [e₁, e₂, ← toBase_mul_of_isMonHom (𝟙 H) hq]
  rfl

theorem cpMap_id {S : Scheme.{0}} {H : Over S} [GrpObj H] [IsCommMonObj H] (P : CP H) {f : S ⟶ S} (hf : f = 𝟙 S)
    (hw : 𝟙 H.left ≫ H.hom = H.hom ≫ f) : IsCPMap P P f (𝟙 H.left) hw (idIso P.L.L) := by
  subst hf
  exact IsCPMap.id P

theorem mono_fstG (I : Ideal R) (e : ℕ) (G : Over (Spec (CommRingCat.of R))) : Mono (fstG I e G).left := by
  have hs : Function.Surjective (Ideal.Quotient.mk (I ^ (e + 1))) := Ideal.Quotient.mk_surjective
  have : Epi (CommRingCat.ofHom (Ideal.Quotient.mk (I ^ (e + 1)))) := ConcreteCategory.epi_of_surjective _ hs
  have : Mono (thick R I e) := Scheme.Spec.map_mono (CommRingCat.ofHom (Ideal.Quotient.mk (I ^ (e + 1)))).op
  exact (inferInstance : Mono (pullback.fst G.hom (thick R I e)))

def refl (U : PreU I D A G) : Cmp (RingHom.id R) U U (𝟙 G.left) where
  pb := grpPullback_id G spMap_ringHom_id
  wL := idIso U.P.L.L
  wL_map := cpMap_id U.P spMap_ringHom_id _
  β := 𝟙 _
  pbB := grpPullback_id D.P.A spMap_ringHom_id
  v := idIso D.P.L
  v_gen := idIso_isGen D.P.isLB
  xe := AddEquiv.refl _
  c_pr x := by rw [spMap_ringHom_id]; exact (Category.comp_id _).trans (Category.id_comp _).symm
  lev e Z x' x hx := by
    have := mono_fstG I e G
    rw [Category.comp_id, cancel_mono] at hx
    subst hx
    refine ⟨by rw [Category.comp_id], fun z J J' hJ hJ' => ⟨fun χ => ?_, fun k k' hk hk' => ?_⟩⟩
    · refine (val_change ((U.gt e).t_gen χ) x hJ hJ').trans ((mul_comm _ _).trans (congrArg _ ?_))
      refine Finset.prod_congr rfl fun k _ => congrArg (· ^ _) ?_
      rw [Category.comp_id, gw_idIso _ _ _ (hJ _) (hJ' _)]
    · rw [gw_idIso _ _ _ (hJ _) (hJ' _), gw_idIso U.P.L.L (x ≫ (fstG I e G).left) z hk hk']
      have h := (isGen_iff (U.w e)).1 (U.w_gen e) Z x z (J (x ≫ (U.gt e).pG.left)) (J' (x ≫ (U.gt e).pG.left))
        (fun _ => k) (fun _ => k') (hJ (x ≫ (U.gt e).pG.left)) (hJ' (x ≫ (U.gt e).pG.left))
        (mem_pull.2 hk) (mem_pull.2 hk')
      have g := gm_pull_g U.P.L.L (fstG I e G).left x z (fun _ => k) (fun _ => k') (mem_pull.2 hk) (mem_pull.2 hk')
      rw [h, g]
      exact (congrArg (· * _) (inv_mul_cancel_right _ _).symm).trans (mul_right_comm _ _ _)

variable {φ : R →+* V} {U : PreU I D A G} {U' : PreU I' D' A' G'} {F : G'.left ⟶ G.left}

theorem pow_le (C : Cmp φ U U' F) (e : ℕ) : I ^ (e + 1) ≤ (I' ^ (e + 1)).comap φ := by
  rw [← Ideal.map_le_iff_le_comap, Ideal.map_pow]
  exact Ideal.pow_right_mono C.map_le _

def baseMap (C : Cmp φ U U' F) (e : ℕ) :
    Spec (CommRingCat.of (V ⧸ I' ^ (e + 1))) ⟶ Spec (CommRingCat.of (R ⧸ I ^ (e + 1))) :=
  spMap (Ideal.quotientMap (I' ^ (e + 1)) φ (C.pow_le e))

theorem baseMap_thick (C : Cmp φ U U' F) (e : ℕ) : C.baseMap e ≫ thick R I e = thick V I' e ≫ spMap φ := by
  simp only [baseMap, thick, spMap, ← Spec.map_comp, ← CommRingCat.ofHom_comp, Ideal.quotientMap_comp_mk]

def levMap (C : Cmp φ U U' F) (e : ℕ) : (thickObj V I' e G').left ⟶ (thickObj R I e G).left :=
  pullback.lift ((fstG I' e G').left ≫ F) (pullback.snd G'.hom (thick V I' e) ≫ C.baseMap e) (by
    simp only [Category.assoc]
    rw [C.pb.1.w, C.baseMap_thick]
    exact pullback.condition_assoc (f := G'.hom) (g := thick V I' e) _)

theorem levMap_fst (C : Cmp φ U U' F) (e : ℕ) : C.levMap e ≫ (fstG I e G).left = (fstG I' e G').left ≫ F :=
  pullback.lift_fst _ _ _

end Cmp

end GlobalTheory.LN
end
end

-- bundled from Development.AbelianVarietyTheory.Definitions.Degenerations.IsBasisB
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section
namespace GlobalTheory.ZH
open ReciprocityTheory.ChartRestriction.G.Out GlobalTheory.UT
variable {o Ω : Type} [CommRing o] [Field Ω] [Algebra o Ω] {S : ThetaSys o Ω}

def ThetaSys.Real.Crd (ρ : S.Real) {K : Type} [CommRing K] (a : Sp K ⟶ ρ.P.A.left) (v : S.J → K) : Prop :=
  ∃ a' : Sp K ⟶ (baseOver (Sp S.R) ⊗ ρ.P.A).left, a' ≫ (snd (baseOver (Sp S.R)) ρ.P.A).left = a ∧
    GlobalTheory.ZH.Crd (LPow ρ.P.A ρ.P.L S.N (baseOver (Sp S.R))) ρ.s a' v

def FamOf {V : Type} [CommRing V] [IsDomain V] (D : DegPre V) (F : Type) [Field F] [Algebra (FractionRing V) F] {k : ℕ}
    (f : ∀ α, D.SecB k α) (s : Fam D F k) : Prop :=
  ∀ α, GeneratorPullback.SecScal D.P.L (DegPre.famφ D F α) (DegPre.famε k) (s.s α) (D.famφB α) (DegPre.famε k) (f α)
    (DegPre.prB D F).left 1

def IsBasisB {V : Type} [CommRing V] [IsDomain V] (D : DegPre V) {k : ℕ} {α : D.X} {I : Type} [Fintype I]
    (β : I → D.SecB k α) : Prop :=
  ∀ gm₀ : D.SecB k α, ∃! a : I → V, ∀ j, gm₀.f j = ∑ i, constFn D.P.A.hom _ (a i) * (β i).f j
namespace ThetaSys.Real.UTest
variable {ρ : S.Real} {p : ℕ} [Fact p.Prime] {y₀ : S.R →+* PadicAlgCl p} (u : ρ.UTest p y₀)

def j : u.V →+* OO p :=
  ((algebraMap (FractionRing u.V) (PadicAlgCl p)).comp (algebraMap u.V (FractionRing u.V))).codRestrict (OO p)
    (fun x => (mem_OO_iff _).2 ((u.norm_le _).2 ⟨x, rfl⟩))

abbrev H (k : ℕ) : LB u.G.left := LB.LinComb u.U.LG.L (K := Fin 1) (fun _ => 𝟙 u.G.left) (fun _ => (k : ℤ))

abbrev PtC : Type := TFK (R := u.V) (PadicAlgCl p) ⟶ (Over.pullback (jK u.V)).obj u.G

def toG (a : u.PtC) : Sp (PadicAlgCl p) ⟶ u.G.left := a.left ≫ pullback.fst u.G.hom (jK u.V)

def toA (a : u.PtC) : Sp (PadicAlgCl p) ⟶ ρ.P.A.left := a.left ≫ u.U.gen.hom.left ≫ u.φ

def Int (a : u.PtC) : Prop := ∃ c : Sp (OO p) ⟶ u.G.left, c ≫ u.G.hom = spMap u.j ∧ gPt p ≫ c = u.toG a

open Classical in
def Basis (l : u.Lab) (k : ℕ) {J : Type} [Fintype J] (σ : J → (u.H k).Sec) (cls : J → u.D.toPre.X)
    (f : J → ∀ α, u.D.toPre.SecB k α) : Prop :=
  (∀ i, Short l.q k (cls i)) ∧ (∀ i i', (∃ m, cls i = cls i' + k • m) → cls i = cls i') ∧
  (∀ α, ∃ i m, α = cls i + k • m) ∧ (∀ i e, u.U.toUnifPre.ExpandsAt e k (σ i) (f i)) ∧
  (∀ i, ∃ s : Fam u.D.toPre (FractionRing u.V) k, FamOf u.D.toPre _ (f i) s) ∧
  (∀ i α, (∀ m, α ≠ cls i + k • m) → ∀ j, (f i α).f j = 0) ∧
  ∀ i₀, IsBasisB u.D.toPre (fun i : {i // cls i = cls i₀} => f i (cls i₀))

def IntGood (J : ((TF (R := u.V) (PadicAlgCl p)).left ⟶ u.D.toPre.P.A.left) → u.D.toPre.P.L.ι) : Prop :=
  ∀ ψ : Sp (OO p) ⟶ u.D.toPre.P.A.left, ψ ≫ u.D.toPre.P.A.hom = spMap u.j →
    ⊤ ≤ ψ ⁻¹ᵁ u.D.toPre.P.L.U (J (gPt p ≫ ψ))

def GtN (g : GtPtF u.D.toPre (PadicAlgCl p)) (ν : u.D.toPre.X → ℝ) : Prop :=
  ∀ J, u.IntGood J → ∀ χ, ‖valF (𝟙 (Sp (PadicAlgCl p))) _
    ((g.s χ).s (fun k => J (DegPre.gtφ u.D.toPre (PadicAlgCl p) g.b χ k))).val‖ = Real.exp (-ν χ)

def ParAt (k : ℕ) (a : u.PtC) (g : GtPtF u.D.toPre (PadicAlgCl p)) : Prop :=
  ∀ w : Frm u.D.toPre (PadicAlgCl p) k g.b, w.IsGen → ∀ l : u.U.LG.L.ι, ⊤ ≤ u.toG a ⁻¹ᵁ u.U.LG.L.U l →
    ∃ κ : PadicAlgCl p, κ ≠ 0 ∧ ∀ (σ : u.U.toUnifPre.SecGF (PadicAlgCl p) k) (s : Fam u.D.toPre (PadicAlgCl p) k),
      u.U.toUnifPre.ExpandsG (PadicAlgCl p) k σ s → HasSum (fun χ => coef s g w χ)
        (κ * valF (show Sp (PadicAlgCl p) ⟶ _ from (lift (𝟙 (TFK (R := u.V) (PadicAlgCl p))) a).left) _ (σ.f (fun _ => l)))

abbrev lev (e : ℕ) : Ideal (OO p) := (IsLocalRing.maximalIdeal u.V ^ (e + 1)).map u.j

def Lev (c : Sp (OO p) ⟶ u.G.left) (g : GtPtF u.D.toPre (PadicAlgCl p)) : Prop :=
  ∃ b₀ : Sp (OO p) ⟶ u.D.toPre.P.A.left, gPt p ≫ b₀ = g.b.left ∧
    ∀ (e : ℕ) (ce : Sp (OO p ⧸ u.lev e) ⟶ (thickObj u.V (IsLocalRing.maximalIdeal u.V) e u.G).left),
      ce ≫ (fstG (IsLocalRing.maximalIdeal u.V) e u.G).left = spMap (Ideal.Quotient.mk (u.lev e)) ≫ c →
      ce ≫ (u.U.gt e).pG.left = spMap (Ideal.Quotient.mk (u.lev e)) ≫ b₀ ∧
      ∀ (χ : u.D.toPre.X) (jj : Fin 4 → u.D.toPre.P.L.ι),
        ⊤ ≤ ce ⁻¹ᵁ LB.wchart u.D.toPre.P.L (u.D.toPre.Oφ (u.U.gt e).pG χ) jj →
        ∃ x : OO p, (x : PadicAlgCl p) = valF (𝟙 (Sp (PadicAlgCl p))) _ ((g.s χ).s jj).val ∧
          Ideal.Quotient.mk (u.lev e) x = valR ce _ (((u.U.gt e).t χ).s jj).val
attribute [local instance] SplitExt.free SplitExt.finite

structure FibOf (N : ℕ) where
  Φ : FibPre (kb p)
  r : Φ.G.left ⟶ u.G.left
  cart : IsGrpPullback Φ.G u.G (rPt p ≫ spMap u.j) r
  xe : Φ.E.X ≃+ u.D.toPre.X
  pol : Φ.Pol N
  dim : pol.PB.g = u.D.toPre.P.g
  red : ∀ α, u.D.toPre.SecB N α → (Φ.H 1).Sec
  pure : ∀ α β, Φ.Pure (xe.symm α) (red α β)
  lin : ∀ α (I : Type) [Fintype I] (β : I → u.D.toPre.SecB N α) (a : I → u.V) (gm₀ : u.D.toPre.SecB N α),
    (∀ j, gm₀.f j = ∑ i, constFn u.D.toPre.P.A.hom _ (a i) * (β i).f j) →
    IsLin Φ.G.hom (fun i => red α (β i)) (fun i => IsLocalRing.residue (OO p) (u.j (a i))) (red α gm₀)
  basis : ∀ α (I : Type) [Fintype I] (β : I → u.D.toPre.SecB N α), IsBasisB u.D.toPre β →
    ∀ φ : (Φ.H 1).Sec, Φ.Pure (xe.symm α) φ → ∃! a : I → kb p, IsLin Φ.G.hom (fun i => red α (β i)) a φ
  exp : ∀ (J : Type) (σ : J → (u.H N).Sec) (f : J → ∀ α, u.D.toPre.SecB N α),
    (∀ i, u.U.toUnifPre.ExpandsAt 0 N (σ i) (f i)) → ∃ F : J → (Φ.H 1).Sec,
      (∀ i α, Φ.IsPart (xe.symm α) (F i) (red α (f i α))) ∧
      ∀ (x : Φ.Pt) (v : J → kb p), GlobalTheory.ZH.Crd (Φ.H 1) F x.left v → GlobalTheory.ZH.Crd (u.H N) σ (x.left ≫ r) v

def Link (σ : S.J → (u.H S.N).Sec) (b : Matrix S.J S.J (FractionRing u.V)) : Prop :=
  ∀ (a : u.PtC) (v : S.J → PadicAlgCl p), ρ.Crd (u.toA a) v →
    GlobalTheory.ZH.Crd (u.H S.N) σ (u.toG a) ((b.map (algebraMap _ (PadicAlgCl p))).mulVec v)
end ThetaSys.Real.UTest

structure ThetaSys.Real.GeoTest (ρ : S.Real) (p : ℕ) [Fact p.Prime] (y₀ : S.R →+* PadicAlgCl p) where
  u : ρ.UTest p y₀
  l : u.Lab
  τ : S.Test p y₀
  mt : l.Match τ
  σ : S.J → (u.H S.N).Sec
  cls : S.J → u.D.toPre.X
  mod : Mod p u.j u.G S.g S.N l.q (u.H S.N) σ cls
  b : Matrix S.J S.J (FractionRing u.V)
  link : u.Link σ b
  span : τ.E = Submodule.span (OO p) (Set.range (b.map (algebraMap _ (PadicAlgCl p))))
  wt : ∀ i, ((S.proj _ (l.wt (cls i))).map fun a => y₀ (algebraMap o S.R a)).mulVec
    (b.map (algebraMap _ (PadicAlgCl p)) i) = b.map (algebraMap _ (PadicAlgCl p)) i

def ThetaSys.Real.HasU (ρ : S.Real) : Prop := ∀ (p : ℕ) [Fact p.Prime] (y₀ : S.R →+* PadicAlgCl p),
  (∀ a : o, ‖y₀ (algebraMap o S.R a)‖ ≤ 1) → ∀ Fs : Finset (PadicAlgCl p),
    ∃ (u : ρ.UTest p y₀) (l : u.Lab) (τ : S.Test p y₀), l.Match τ ∧
      ∀ x ∈ Fs, x ∈ Set.range (algebraMap (FractionRing u.V) (PadicAlgCl p))

def ThetaSys.Real.HasGeo (ρ : S.Real) : Prop := ∀ (p : ℕ) [Fact p.Prime] (y₀ : S.R →+* PadicAlgCl p),
  (∀ a : o, ‖y₀ (algebraMap o S.R a)‖ ≤ 1) → ∀ Fs : Finset (PadicAlgCl p),
    ∃ gm₀ : ρ.GeoTest p y₀, ∀ x ∈ Fs, x ∈ Set.range (algebraMap (FractionRing gm₀.u.V) (PadicAlgCl p))
end GlobalTheory.ZH
end
end

-- bundled from Development.AbelianVarietyTheory.Definitions.Degenerations.LabKerUnique
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
noncomputable section
namespace GlobalTheory.ZH
open ReciprocityTheory.ChartRestriction.G.Out Classical

namespace RealModel
open Inh

theorem res_one {X : Scheme.{0}} {U V : X.Opens} (h : V ≤ U) : res h (1 : Γ(X, U)ˣ) = 1 := map_one _
theorem res_res {X : Scheme.{0}} {U V W : X.Opens} (h : V ≤ U) (h' : W ≤ V) (u : Γ(X, U)ˣ) :
    res h' (res h u) = res (h'.trans h) u := by
  ext
  simp only [res, Units.coe_map, MonoidHom.coe_coe]
  rw [← CommRingCat.comp_apply, ← Functor.map_comp]
  rfl

def oneG {X Y : Scheme.{0}} {K : Type} [Fintype K] (φ : K → (Y ⟶ X)) (ε : K → ℤ) :
    LB.Gen (LB.LinComb (trivLB X) φ ε) := ⟨fun _ => 1⟩
theorem oneG_gen {X Y : Scheme.{0}} {K : Type} [Fintype K] (φ : K → (Y ⟶ X)) (ε : K → ℤ) :
    (oneG φ ε).IsGen := by
  intro i j; rw [linComb_triv_g, _root_.one_mul]; exact (res_one _).trans (res_one _).symm

variable (B : Scheme.{0})

theorem translT_id {T : Over B} (x : T ⟶ (zeroPolAV B).A) : (translT (zeroPolAV B).A x).left = 𝟙 _ := by
  have : translT (zeroPolAV B).A x = 𝟙 _ := by
    apply CartesianMonoidalCategory.hom_ext
    · simp [translT]
    · exact toUnit_unique _ _
  rw [this]; rfl

variable {o Ω : Type} [CommRing o] [Field Ω] [Algebra o Ω]

section More
variable {S : ThetaSys o Ω} (ρ : S.Real)

variable {ρ} {p : ℕ} [Fact p.Prime] {y₀ : S.R →+* PadicAlgCl p} {u : ρ.UTest p y₀}

end More

end RealModel
end GlobalTheory.ZH
end
end

-- bundled from Development.AbelianVarietyTheory.Definitions.Degenerations.ToATotal
section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section
namespace GlobalTheory.LN
open GlobalTheory.UU

def HypW {B : Scheme.{0}} (G : Over B) [GrpObj G] [IsCommMonObj G] (L : LB G.left) : Prop :=
  ∃ w wd : G ⟶ G, IsMonHom w ∧ IsMonHom wd ∧ w * wd = 𝟙 G ∧ LBIso L (cubeLB G ![𝟙 G, w] L) ∧
    LBIso (cubeLB G ![fst G G ≫ w, snd G G] L) (cubeLB G ![fst G G, snd G G ≫ wd] L)

def ToATotal {R : Type} [CommRing R] [IsDomain R] {I : Ideal R} {D : DegData R I} {A : PolAV (Spec (CommRingCat.of (FractionRing R)))}
    {G : Over (Spec (CommRingCat.of R))} [GrpObj G] [IsCommMonObj G] (U : UnifPre I D A G) : Prop :=
  ∀ (F : Type) [Field F] [IsAlgClosed F] [Algebra (FractionRing R) F] (k : ℕ), 1 ≤ k →
    ∀ p : QkPt D.toPre F k, ∃ x, QkToAkU U F k p x

def USt : Prop := AllSet fun {V} _ _ _ {A} {G} _ _ s =>
  ∃ (D : DegData V (IsLocalRing.maximalIdeal V)) (U : Unif (IsLocalRing.maximalIdeal V) D A G),
    U.LG = s.P.L ∧ U.gen = s.gen ∧ ToATotal U.toUnifPre
end GlobalTheory.LN
end
end

