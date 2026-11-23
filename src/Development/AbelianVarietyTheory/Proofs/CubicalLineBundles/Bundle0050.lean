module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.CMLattices.ExistsIsThetaDegOfIsLocalModel
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.IsAbelianSchemeAndExtendOfGenericHoms
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle0025
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle0032
public import Development.AbelianVarietyTheory.Definitions.CMLattices.IsDiffOf
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle0036
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle0034
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle0049
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle0027
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ObjIsAbelianSchemeDimRigidifiedSym
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsPrimitiveNormalisation
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0018
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.IntegralFrameChangeIntegralInvertibleMatrix
public import Development.AbelianVarietyTheory.Definitions.CMLattices.IntegralOf
public import Development.AbelianVarietyTheory.Statements.PrincipalLattices.ExistsPrincipalLattice
public import Development.AbelianVarietyTheory.Definitions.RegularCharts.BaseNorm
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0023
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0021
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.NonemptyUnitAt
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.Bundle0010
public import Development.AbelianVarietyTheory.Definitions.CMLattices.LamLetters
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle0048
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle0031
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle0013
public import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.Bundle0014
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle0021
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle0015
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle0035

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.ExistsCmTensorLatticeCurvePrincipalTriple
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open scoped CategoryTheory.Obj
open GlobalTheory GlobalTheory.CM

noncomputable section
namespace GlobalTheory.CM

theorem exists_isTen : Out.Laws → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (R : Type) [CommRing R] [IsNoetherianRing R] (ω : R) (C : Ell H R ω) (D : Datum H) (ε : ℤˣ) (h : D.La → D.La → OK H), IsKForm D ε h → (∀ x : D.La, x ≠ 0 → 0 < (ε : ℤ) * D.EF (H.w0 • x) x) → ∃ T : PAT H (Sp R), Nonempty (IsTen C D h T) ∧ T.g = Module.finrank ℚ E / 2 * (D.p + D.q) := by
  intro laws E _ _ _ H R _ _ ω C D ε h hK hpos
  obtain ⟨h₀, -, huniq, hbar, hE, -, -, n, x, y, hxy⟩ := _root_.GlobalTheory.CM.exists_kForm E H D ε
  obtain rfl := huniq h hK
  obtain ⟨-, -, ⟨br, hbr, hw, hbb⟩, -, -, hM⟩ := OK_isDedekindDomain_and_projective E H
  obtain ⟨hfin, hproj, -⟩ := hM D.La D.fin D.proj
  let t := Serre.isTensor D.La C.act
  obtain ⟨c, τ, hc⟩ : ∃ (c : OAct (𝓞 E) (Serre.tensorObj D.La C.act))
      (τ : Serre.IsTensor _ (Serre.comapAct c (algebraMap (OK H) (𝓞 E))) C.P.A C.act D.La),
      ∀ (s : 𝓞 E) a, τ.tmul (s • a) = τ.tmul a ≫ c.act s := by
    have key : ∀ b', b' = Serre.tensorAct D.La C.act → ∃ τ : Serre.IsTensor _ b' C.P.A C.act D.La,
        ∀ a, τ.tmul a = t.tmul a := by
      rintro _ rfl
      exact ⟨t, fun _ => rfl⟩
    obtain ⟨τ, hτ⟩ := key _ (t.comapAct_algAct (𝓞 E))
    exact ⟨t.algAct (𝓞 E), τ, fun s a => by rw [hτ, hτ, t.tmul_algAct]⟩
  have hA : IsAbelianScheme (Serre.tensorObj D.La C.act) := τ.isAbelianScheme C.P.isAb
  obtain ⟨rig, hrig⟩ := C.P.rigid
  obtain ⟨cubP⟩ := (laws.cube _ C.P ⟨C.P.L, rig, C.P.isLB, hrig⟩ rfl).1
  have hθP : ∃ t : LB.Gen (Theta C.P.A C.P.L), t.IsGen := ⟨cubP.t, cubP.isGen⟩
  obtain ⟨N, hN, -, hθ, hp⟩ := GlobalTheory.TensorBundle.exists_tensor_bundle _ (OK H) C.P.A _ C.act _ D.La τ br (wK H) C.P.L h₀
    hfin hproj hw hbb (fun a b => Subtype.ext ((hbar a b).trans (hbr _).symm)) C.P.isLB hθP
    (fun a => C.adj a (br a) (hbr a))
  obtain ⟨PP, cub, sym, -, hΛ, prim, adj⟩ := GlobalTheory.PrimNorm.exists_primitive_normalisation laws.globalFns E H _ _ c N
    hA hN hθ fun s => by
      have := GlobalTheory.LamCalc.lamEq_of_tmul _ (OK H) C.P.A _ C.act _ D.La τ _ _ D.La τ _ _ N N (c.act s) (𝟙 _) (𝟙 _)
        (c.act (H.bar s)) hN hN hθ hθ (c.hom _) inferInstance inferInstance (c.hom _) fun m m' => by
          rw [← hc, ← hc, Category.comp_id, Category.comp_id]
          have a := hp (s • m) m'
          rw [hE] at a
          exact LBIso.trans (DVR.linComb_isLB _ hN _ _) (DVR.linComb_isLB _ C.P.isLB _ _) (DVR.linComb_isLB _ hN _ _)
            a (hp m (H.bar s • m')).symm
      simpa only [LamEq, Category.comp_id] using this
  have hp' : ∀ m m', LamEq PP.L (τ.tmul m) (τ.tmul m') C.P.L (C.act.act (h₀ m m')) (𝟙 C.P.A) := fun m m' =>
    LBIso.trans (DVR.linComb_isLB _ PP.isLB _ _) (DVR.linComb_isLB _ hN _ _) (DVR.linComb_isLB _ C.P.isLB _ _)
      (hΛ.chartPull
        (GlobalTheory.PrimNorm.chartSquare PP.L (lift (fst C.P.A C.P.A ≫ τ.tmul m) (snd C.P.A C.P.A ≫ τ.tmul m'))
          (lift_fst _ _).symm (lift_snd _ _).symm)
        (GlobalTheory.PrimNorm.chartSquare N (lift (fst C.P.A C.P.A ≫ τ.tmul m) (snd C.P.A C.P.A ≫ τ.tmul m'))
          (lift_fst _ _).symm (lift_snd _ _).symm))
      (hp m m')
  have hθ' : ∃ t : LB.Gen (Theta _ PP.L), t.IsGen := ⟨cub.t, cub.isGen⟩
  let s : SAB H (Sp R) :=
    { G := Serre.tensorObj D.La C.act, semi := GlobalTheory.isSemiAbelian_of_isAbelianScheme _ hA, act := c, PP := PP,
      cub := cub, sym := sym, adj := adj, prim := prim }
  exact ⟨⟨s, hA, _, _root_.GlobalTheory.CM.tensor_smoothOfRelativeDimension E H R ω C D _ _ ⟨τ⟩, ObjDim.sym,
    _root_.GlobalTheory.CM.relAmple_of_kForm_pos laws E H R ω C D ε _ _ _ τ PP.L hK hpos PP.isLB hθ' prim hp',
    GlobalTheory.PerfectTensorKernel.kTriv_of_perfect _ (OK H) C.P.A _ C.act _ D.La τ C.P.L PP.L h₀ n x y hxy C.P.isLB PP.isLB
      hθP hθ' hp' C.P.ktriv⟩, ⟨⟨τ, hc, hp'⟩⟩, rfl⟩

end GlobalTheory.CM
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.ExistsIntegralEigenbasisOfFrameAtLocalModel
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.LamCM Formalism.L2.Pj
open scoped ComplexOrder
open GlobalTheory GlobalTheory.CM GlobalTheory.Frames GlobalTheory.LamT

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.LamT.LocLie

open GlobalTheory.IntRebase
open Formalism.L2.PjFree (spMap_comp' epsMul_comp_alg)

attribute [local instance] Over.cartesianMonoidalCategory

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
variable {Xo : Moduli Dw l} {c : Coeff l}

theorem comb_eq {S : Type} [CommRing S] {x : Sp S ⟶ Xo.X} {m : ℕ}
    {v : Fin m → (Sp (DualNumber S) ⟶ Xo.univ.t.G.left)} (hv : ∀ j, IsTanAt x (v j)) {a : Fin m → S}
    {w : Sp (DualNumber S) ⟶ Xo.univ.t.G.left} (h : IsCombAt x v a w) :
    (GlobalTheory.IntRebase.combT x (fun j => GlobalTheory.IntRebase.ovT (t := Xo.univ.t) (hv j)) a).left = w :=
  (GlobalTheory.IntRebase.isCombAtG_iff Xo.univ.t x (fun j => GlobalTheory.IntRebase.ovT (t := Xo.univ.t) (hv j)) _ _).1 h

theorem lieInt_change (T : CDVR) (io : c.F →+* T.Fr) {G : SAB H (Sp T.V)} {t' : SAB H (Sp T.Fr)}
    {x : Sp T.Fr ⟶ Xo.X} (m1 : SABMap t' Xo.univ.t x) (m2 : SABMap t' G (spMap (algebraMap T.V T.Fr)))
    (u : ∀ τ : E →+* ℂ, Fin (Dw.mult τ) → (Sp (DualNumber T.Fr) ⟶ Xo.univ.t.G.left))
    (hu : ∀ τ j, IsTanAt x (u τ j)) (h : LieInt T io m1 m2 u)
    (k : ∀ τ : E →+* ℂ, Matrix (Fin (Dw.mult τ)) (Fin (Dw.mult τ)) T.V) (hk : ∀ τ, IsUnit (k τ).det) :
    LieInt T io m1 m2 (fun τ i => (GlobalTheory.IntRebase.combT x (fun j => GlobalTheory.IntRebase.ovT (t := Xo.univ.t) (hu τ j))
      (fun j => algebraMap T.V T.Fr (k τ j i))).left) := by
  obtain ⟨ub, htan, heig, hbas, hlift⟩ := h
  let Ub : ∀ τ : E →+* ℂ, Fin (Dw.mult τ) → (tEpsG (𝟙 (Sp T.V)) ⟶ G.G) := fun τ j => kap ≫ ub τ j
  have hUb0 : ∀ τ j, GlobalTheory.IntRebase.smT (𝟙 (Sp T.V)) 0 (Ub τ j) = 1 := fun τ j => GlobalTheory.IntRebase.smT_zero_kap _ (htan τ j)
  have hUbE : ∀ τ j (a : 𝓞 E) (z : T.V), algebraMap T.V T.Fr z = io (embK c τ a) →
      Ub τ j ≫ G.act.act a = GlobalTheory.IntRebase.smT (𝟙 (Sp T.V)) z (Ub τ j) := fun τ j =>
    (GlobalTheory.IntRebase.isEigV_kapI_iff io G τ _).1 (by rw [GlobalTheory.IntRebase.kapI_kap_assoc]; exact heig τ j)
  refine ⟨fun τ i => GlobalTheory.IntRebase.kapI ≫ GlobalTheory.IntRebase.combT (𝟙 (Sp T.V)) (Ub τ) (fun j => k τ j i), ?_, ?_, ?_, ?_⟩
  · intro τ i
    exact GlobalTheory.IntRebase.isTan_kapI _ (GlobalTheory.IntRebase.combT_tan _ _ (hUb0 τ) _)
  · intro τ i
    refine (GlobalTheory.IntRebase.isEigV_kapI_iff io G τ _).2 fun a z hz => ?_
    have := G.act.hom a
    exact GlobalTheory.IntRebase.combT_eig _ _ _ _ (fun j => hUbE τ j a z hz) _
  · intro τ w hw he
    have h1 : ∃! a : Fin (Dw.mult τ) → T.V, kap ≫ w = GlobalTheory.IntRebase.combT (𝟙 (Sp T.V)) (Ub τ) a := by
      obtain ⟨a, ha, hu⟩ := hbas τ w hw he
      refine ⟨a, (GlobalTheory.IntRebase.isComb_iff _ _ _).1 (by rw [GlobalTheory.IntRebase.kapI_kap_assoc]; exact ha), fun b hb => hu b ?_⟩
      have h2 := (GlobalTheory.IntRebase.isComb_iff (ub τ) b (kap ≫ w)).2 hb
      rw [GlobalTheory.IntRebase.kapI_kap_assoc] at h2
      exact h2
    obtain ⟨a, ha, hu⟩ := GlobalTheory.IntRebase.reframe_basis _ (Ub τ) (hUb0 τ) (k τ) (hk τ) _ h1
    have e : (fun i => kap ≫ (GlobalTheory.IntRebase.kapI ≫ GlobalTheory.IntRebase.combT (𝟙 (Sp T.V)) (Ub τ) (fun j => k τ j i))) =
        fun i => GlobalTheory.IntRebase.combT (𝟙 (Sp T.V)) (Ub τ) (fun j => k τ j i) := funext fun i => GlobalTheory.IntRebase.kap_kapI_assoc _
    refine ⟨a, ?_, fun b hb => hu b ?_⟩
    · have h2 := (GlobalTheory.IntRebase.isComb_iff (fun i => GlobalTheory.IntRebase.kapI ≫ GlobalTheory.IntRebase.combT (𝟙 (Sp T.V)) (Ub τ) (fun j => k τ j i)) a (kap ≫ w)).2
        (by rw [e]; exact ha)
      rw [GlobalTheory.IntRebase.kapI_kap_assoc] at h2
      exact h2
    · have h2 := (GlobalTheory.IntRebase.isComb_iff (fun i => GlobalTheory.IntRebase.kapI ≫ GlobalTheory.IntRebase.combT (𝟙 (Sp T.V)) (Ub τ) (fun j => k τ j i)) b (kap ≫ w)).1
        (by rw [GlobalTheory.IntRebase.kapI_kap_assoc]; exact hb)
      rw [e] at h2
      exact h2
  · intro τ i
    choose u' hu1 hu2 using hlift τ
    have hδ : spMap (Formalism.L2.Pj.dualMap (algebraMap T.V T.Fr)) ≫
        spMap ((algebraMap T.V (DualNumber T.V)).comp (algebraMap T.V T.V)) =
        spMap (algebraMap T.Fr (DualNumber T.Fr)) ≫ spMap (algebraMap T.V T.Fr) := by
      rw [Formalism.L2.PjFree.spMap_comp', Formalism.L2.PjFree.spMap_comp']
      show spMap ((Formalism.L2.Pj.dualMap (algebraMap T.V T.Fr)).comp (algebraMap T.V (DualNumber T.V))) = _
      rw [GlobalTheory.IntRebase.dualMap_comp_alg]
    have hov : ∀ j, u' j ≫ t'.G.hom = spMap (algebraMap T.Fr (DualNumber T.Fr)) := by
      intro j
      apply GlobalTheory.IntRebase.spMap_frac_cancel (V := T.V)
      rw [Category.assoc, ← m2.cart.1.w, ← Category.assoc, hu2 j, Category.assoc, Over.w (ub τ j)]
      exact hδ
    let T' : Over (Sp T.Fr) := Over.mk (spMap (algebraMap T.Fr (DualNumber T.Fr)))
    let cf : Fin (Dw.mult τ) → T.Fr := fun j => algebraMap T.V T.Fr (k τ j i)
    let Y : Fin (Dw.mult τ) → (T' ⟶ t'.G) := fun j => Over.homMk (spMap (epsMul (cf j)) ≫ u' j) (by
      show (spMap (epsMul (cf j)) ≫ u' j) ≫ t'.G.hom = spMap (algebraMap T.Fr (DualNumber T.Fr))
      rw [Category.assoc, hov, Formalism.L2.PjFree.spMap_comp', Formalism.L2.PjFree.epsMul_comp_alg])
    refine ⟨(∏ j, Y j).left, ?_, ?_⟩
    · have hA := GlobalTheory.IntRebase.grpPull_prod m1.cart T' Finset.univ Y
        (fun j => GlobalTheory.IntRebase.smT x (cf j) (GlobalTheory.IntRebase.ovT (t := Xo.univ.t) (hu τ j))) (fun j => by
          show spMap (epsMul (cf j)) ≫ u τ j = (spMap (epsMul (cf j)) ≫ u' j) ≫ m1.φ
          rw [Category.assoc, hu1])
      exact hA.symm
    · let δ : Over.mk (T'.hom ≫ spMap (algebraMap T.V T.Fr)) ⟶ epsOver T.V T.V :=
        Over.homMk (spMap (Formalism.L2.Pj.dualMap (algebraMap T.V T.Fr))) hδ
      have hB := GlobalTheory.IntRebase.grpPull_prod m2.cart T' Finset.univ Y
        (fun j => δ ≫ GlobalTheory.IntRebase.kapI ≫ GlobalTheory.IntRebase.smT (𝟙 (Sp T.V)) (k τ j i) (Ub τ j)) (fun j => by
          simp only [Over.comp_left, δ, GlobalTheory.IntRebase.kapI, GlobalTheory.IntRebase.kap, Ub, GlobalTheory.IntRebase.smT_left, Over.homMk_left, Category.id_comp, Y,
            Category.assoc]
          rw [hu2 j, ← Category.assoc, ← Category.assoc, Formalism.L2.PjFree.spMap_comp', Formalism.L2.PjFree.spMap_comp', GlobalTheory.IntRebase.dualMap_comp_epsMul])
      rw [← hB, ← GlobalTheory.IntRebase.comp_prodT, ← GlobalTheory.IntRebase.comp_prodT]
      rfl

end GlobalTheory.LamT.LocLie


open GlobalTheory.LamT.LocLie in
theorem GlobalTheory.LamT.lieInt_exists_and_change : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (T : CDVR) (io : c.F →+* T.Fr) (G : SAB H (Sp T.V)) (t' : SAB H (Sp T.Fr)) (x : Sp T.Fr ⟶ Xo.X) (m1 : SABMap t' Xo.univ.t x) (m2 : SABMap t' G (spMap (algebraMap T.V T.Fr))), letI := io.toAlgebra; ∀ y : FrPt Xo c T.Fr, y.x = x → (∃ g : (∀ b : E →+* ℂ, Matrix (Fin (Dw.mult b)) (Fin (Dw.mult b)) T.Fr), (∀ b, IsUnit (g b).det) ∧ ∀ (a : T.Fr) (y' : FrPt Xo c T.Fr), FrChg g a y y' → LieInt T io m1 m2 y'.u) ∧ (LieInt T io m1 m2 y.u → ∀ (X : (∀ b : E →+* ℂ, Matrix (Fin (Dw.mult b)) (Fin (Dw.mult b)) T.V)) (a : T.Fr) (y' : FrPt Xo c T.Fr), (∀ b, IsUnit (X b).det) → FrChg (fun b => (X b).map (algebraMap T.V T.Fr)) a y y' → LieInt T io m1 m2 y'.u) := by
  intro E _ _ _ H Dw l Xo c T io G t' x m1 m2
  let _ := io.toAlgebra
  intro y hy
  subst hy
  refine ⟨?_, fun h X a y' hX hch => ?_⟩
  · obtain ⟨ub, u, hint, ht, he, hb, hcf⟩ := lieFree Xo c T io G t' y.x m1 m2 y.x_over y.u y.tan y.eig y.basis
    choose cf hd hz hc using hcf
    refine ⟨fun b => Matrix.of (cf b), fun b => ?_, fun a y' hch => ?_⟩
    · show IsUnit (Matrix.of (cf b)).det
      rw [Matrix.det_of_isLowerTriangular (Matrix.of (cf b)) (fun i j hij => hz b i j hij)]
      exact IsUnit.prod_univ_iff.2 (hd b)
    · have e : y'.u = u := funext fun τ => funext fun i =>
        (comb_eq (y.tan τ) (hch.2.1 τ i)).symm.trans (comb_eq (y.tan τ) (hc τ i))
      rw [e]
      exact ⟨ub, hint⟩
  · have h2 := lieInt_change T io m1 m2 y.u y.tan h (fun τ => (X τ).transpose)
      (fun τ => by rw [Matrix.det_transpose]; exact hX τ)
    have e : y'.u = _ := funext fun τ => funext fun i => (comb_eq (y.tan τ) (hch.2.1 τ i)).symm
    rw [e]
    exact h2
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.ExistsInverseIsogenySumOfCmHoms
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory Formalism.L2.LamCM
open scoped CategoryTheory.Obj ComplexOrder
open GlobalTheory GlobalTheory.CM GlobalTheory.LamF

namespace GlobalTheory.LamF.IsogSum

variable {S : Scheme.{0}}

theorem isMonHom_of_points {G H : Over S} [GrpObj G] [GrpObj H] (f : G ⟶ H)
    (h : ∀ (T : Over S) (a b : T ⟶ G), (a * b) ≫ f = a ≫ f * b ≫ f) : IsMonHom f := by
  refine ⟨?_, ?_⟩
  · have h1 := h (𝟙_ _) 1 1
    rw [_root_.mul_one] at h1
    have h2 : (1 : 𝟙_ _ ⟶ G) ≫ f = 1 := by simpa using h1
    simpa [Hom.one_def] using h2
  · simpa only [Hom.mul_def, lift_fst_snd, Category.id_comp, lift_fst_comp_snd_comp]
      using h (G ⊗ G) (fst G G) (snd G G)

theorem comp_prod {T G H : Over S} [GrpObj H] [IsCommMonObj H] {n : ℕ} (x : T ⟶ G)
    (a : Fin n → (G ⟶ H)) : x ≫ ∏ i, a i = ∏ i, x ≫ a i :=
  map_prod (MonoidHom.mk' (fun u : G ⟶ H => x ≫ u) fun _ _ => MonObj.comp_mul _ _ _) a Finset.univ

theorem exists_point {Q G' G H' H T : Over S} [GrpObj G'] [GrpObj G] [GrpObj H'] [GrpObj H] {p q : ℕ}
    (pG : Out.IsPowGrp G' G p) (pH : Out.IsPowGrp H' H q) (u : Q ⟶ G') (v : Q ⟶ H')
    [IsIso (lift u v)] (a : Fin p → (T ⟶ G)) (b : Fin q → (T ⟶ H)) :
    ∃ x : T ⟶ Q, (∀ i, x ≫ u ≫ pG.pr i = a i) ∧ ∀ i, x ≫ v ≫ pH.pr i = b i := by
  have hu : inv (lift u v) ≫ u = fst _ _ := by rw [IsIso.inv_comp_eq, lift_fst]
  have hv : inv (lift u v) ≫ v = snd _ _ := by rw [IsIso.inv_comp_eq, lift_snd]
  obtain ⟨c, hc⟩ : ∃ c : T ⟶ G', ∀ i, c ≫ pG.pr i = a i :=
    ⟨pG.lim.lift (Fan.mk T a), fun i => pG.lim.fac (Fan.mk T a) ⟨i⟩⟩
  obtain ⟨d, hd⟩ : ∃ d : T ⟶ H', ∀ i, d ≫ pH.pr i = b i :=
    ⟨pH.lim.lift (Fan.mk T b), fun i => pH.lim.fac (Fan.mk T b) ⟨i⟩⟩
  refine ⟨lift c d ≫ inv (lift u v), fun i => ?_, fun i => ?_⟩
  · rw [Category.assoc, reassoc_of% hu, lift_fst_assoc, hc]
  · rw [Category.assoc, reassoc_of% hv, lift_snd_assoc, hd]

end GlobalTheory.LamF.IsogSum

namespace GlobalTheory.LamF

theorem exists_inverse_isogeny_of_sum : ThetaUnifAV → Out.Laws → HomExtDvr → ∀ (K : Type) [Field K] [NumberField K] (σ : K →+* ℂ) (A A' B : Out.PolAV (Sp (𝓞 K))) (p q : ℕ) (φ : Fin p → (A.A ⟶ B.A)) (φ' : Fin q → (A'.A ⟶ B.A)), (∀ i, IsMonHom (φ i)) → (∀ i, IsMonHom (φ' i)) → B.g = p * A.g + q * A'.g → (∀ y : Over.mk (spMap (σ.comp (algebraMap (𝓞 K) K))) ⟶ B.A, ∃ (x : Fin p → (Over.mk (spMap (σ.comp (algebraMap (𝓞 K) K))) ⟶ A.A)) (x' : Fin q → (Over.mk (spMap (σ.comp (algebraMap (𝓞 K) K))) ⟶ A'.A)), y = (List.ofFn fun i => x i ≫ φ i).prod * (List.ofFn fun i => x' i ≫ φ' i).prod) → ∃ (N : ℕ) (ψ : Fin p → (B.A ⟶ A.A)) (ψ' : Fin q → (B.A ⟶ A'.A)), 0 < N ∧ (∀ (Tb : Over (Sp (𝓞 K))) (x : Tb ⟶ B.A), padd B.A (psumPt fun i => x ≫ ψ i ≫ φ i) (psumPt fun i => x ≫ ψ' i ≫ φ' i) = pnsmulPt N x) ∧ ∀ (Tb : Over (Sp (𝓞 K))) (a : Fin p → (Tb ⟶ A.A)) (a' : Fin q → (Tb ⟶ A'.A)), (∀ i, padd B.A (psumPt fun k => a k ≫ φ k) (psumPt fun k => a' k ≫ φ' k) ≫ ψ i = pnsmulPt N (a i)) ∧ ∀ i, padd B.A (psumPt fun k => a k ≫ φ k) (psumPt fun k => a' k ≫ φ' k) ≫ ψ' i = pnsmulPt N (a' i) := by
  intro hU hL hE K _ _ σ A A' B p q φ φ' hφ hφ' hg hs
  obtain ⟨P, pP, hP⟩ := _root_.GlobalTheory.CM.exists_polAV_isPowGrp (𝓞 K) A p
  obtain ⟨P', pP', hP'⟩ := _root_.GlobalTheory.CM.exists_polAV_isPowGrp (𝓞 K) A' q
  obtain ⟨Q, u, v, hu, hv, huv, hQ⟩ := _root_.GlobalTheory.PolProd.exists_prod_polAV hL (𝓞 K) P P'
  haveI := pP.hom
  haveI := pP'.hom
  let Φ : Q.A ⟶ B.A := (∏ i, u ≫ pP.pr i ≫ φ i) * ∏ i, v ≫ pP'.pr i ≫ φ' i
  have hΦ : ∀ {T : Over (Sp (𝓞 K))} (x : T ⟶ Q.A),
      x ≫ Φ = (∏ i, (x ≫ u ≫ pP.pr i) ≫ φ i) * ∏ i, (x ≫ v ≫ pP'.pr i) ≫ φ' i := by
    intro T x
    simp only [Φ, MonObj.comp_mul, IsogSum.comp_prod, Category.assoc]
  have hm : IsMonHom Φ := IsogSum.isMonHom_of_points Φ fun T a b => by
    simp only [hΦ, MonObj.mul_comp, Finset.prod_mul_distrib]
    exact mul_mul_mul_comm _ _ _ _
  obtain ⟨N, ψ, hN, hψ, h1, h2⟩ := _root_.GlobalTheory.LamF.exists_inverse_isogeny_ringOfIntegers hU hL hE K σ Q B Φ (by rw [hQ, hP, hP', hg]) hm fun y => by
    obtain ⟨a, b, hab⟩ := hs y
    obtain ⟨x, hx, hx'⟩ := IsogSum.exists_point pP pP' u v a b
    refine ⟨x, ?_⟩
    rw [hΦ, hab, List.prod_ofFn, List.prod_ofFn]
    simp only [hx, hx']
  have padd_eq_mul {G T : Over (Sp (𝓞 K))} [GrpObj G] (a b : T ⟶ G) :
      padd G a b = a * b := rfl
  have pnsmulPt_eq_pow {G T : Over (Sp (𝓞 K))} [GrpObj G] (n : ℕ) (a : T ⟶ G) :
      pnsmulPt n a = a ^ n := by
    induction n with
    | zero => rw [pow_zero]; rfl
    | succ n ih => rw [pow_succ, ← ih]; rfl
  have psumPt_eq_prod {G T : Over (Sp (𝓞 K))} [GrpObj G] {n : ℕ} (f : Fin n → (T ⟶ G)) :
      psumPt f = (List.ofFn f).prod := by
    rw [List.prod_eq_foldr]
    rfl
  refine ⟨N, fun i => ψ ≫ u ≫ pP.pr i, fun i => ψ ≫ v ≫ pP'.pr i, hN, fun T x => ?_, fun T a b => ?_⟩
  · rw [padd_eq_mul, pnsmulPt_eq_pow, psumPt_eq_prod, psumPt_eq_prod, List.prod_ofFn, List.prod_ofFn]
    have := hΦ (x ≫ ψ)
    rw [Category.assoc, h2, MonObj.comp_pow, Category.comp_id] at this
    simpa only [Category.assoc] using this.symm
  · obtain ⟨x, hx, hx'⟩ := IsogSum.exists_point pP pP' u v a b
    have key : padd B.A (psumPt fun k => a k ≫ φ k) (psumPt fun k => b k ≫ φ' k) ≫ ψ = x ^ N := by
      have : x ≫ Φ = padd B.A (psumPt fun k => a k ≫ φ k) (psumPt fun k => b k ≫ φ' k) := by
        rw [padd_eq_mul, psumPt_eq_prod, psumPt_eq_prod, List.prod_ofFn, List.prod_ofFn, hΦ]
        simp only [hx, hx']
      rw [← this, Category.assoc, h1, MonObj.comp_pow, Category.comp_id]
    refine ⟨fun i => ?_, fun i => ?_⟩
    · rw [← Category.assoc, key, MonObj.pow_comp, hx, pnsmulPt_eq_pow]
    · rw [← Category.assoc, key, MonObj.pow_comp, hx', pnsmulPt_eq_pow]

end GlobalTheory.LamF
end

-- bundled from Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.ExistsUniqueDifferentialMonHomLieBasis
section
set_option autoImplicit false

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open scoped CategoryTheory.Obj
open GlobalTheory GlobalTheory.CM

namespace GlobalTheory.CM.DiffCoord

variable {R : Type} [CommRing R] {G G' : Over (Sp R)} [GrpObj G] [GrpObj G']

theorem isTangent_comp_hom (f : G ⟶ G') [IsMonHom f] {v : epsR R ⟶ G} (hv : IsTangent v) : IsTangent (v ≫ f) := by
  unfold IsTangent at hv ⊢
  rw [Over.comp_left, ← Category.assoc, hv, ← Over.comp_left, IsMonHom.one_hom]

theorem isLieComb_comp_hom (f : G ⟶ G') [IsMonHom f] {n : ℕ} {c : Fin n → R} {v : Fin n → (epsR R ⟶ G)}
    {w : epsR R ⟶ G} (h : IsLieComb c v w) : IsLieComb c (fun i => v i ≫ f) (w ≫ f) := by
  obtain ⟨u, hu, rfl⟩ := h
  refine ⟨fun i => u i ≫ f, fun i => ?_, ?_⟩
  · rw [Over.comp_left, Over.comp_left, hu, Category.assoc]
  · exact (map_list_prod (IsMonHom.monoidHom f (epsR R)) (List.ofFn u)).trans (by rw [List.map_ofFn]; rfl)

theorem exists_linearMap [IsCommMonObj G'] (f : G ⟶ G') [IsMonHom f] {n m : ℕ} {v : Fin n → (epsR R ⟶ G)}
    {v' : Fin m → (epsR R ⟶ G')} (hv : IsLieBasis v) (hv' : IsLieBasis v') :
    ∃ M : (Fin n → R) →ₗ[R] (Fin m → R), ∀ c w, IsLieComb c v w → IsLieComb (M c) v' (w ≫ f) := by
  choose A hA using fun i => (hv'.2 _ (isTangent_comp_hom f (hv.1 i))).exists
  refine ⟨Fintype.linearCombination R A, fun c w h => ?_⟩
  rw [Fintype.linearCombination_apply]
  exact (LieComb.lieComb_algebra R G' m v' hv'.1).2.2.1 n A _ c _ hA (isLieComb_comp_hom f h)

theorem existsUnique_isDiffOf : ∀ (K : Type) [Field K] [NumberField K] (P : Out.PolAV (Sp (𝓞 K))) (F : GenFib P)
    (P' : Out.PolAV (Sp (𝓞 K))) (F' : GenFib P') (f : P.A ⟶ P'.A), IsMonHom f → (∃! M, F.IsDiffOf F' f M) ∧
    ∃ f₀ : F.P₀.A ⟶ F'.P₀.A, IsMonHom f₀ ∧ f₀.left ≫ F'.φ = F.φ ≫ f.left ∧
      ∀ M, F.IsDiffOf F' f M → ∀ c w, IsLieComb c F.v w → IsLieComb (M c) F'.v (w ≫ f₀) := by
  intro K _ _ P F P' F' f hf
  obtain ⟨f₀, hf₀, e⟩ := DerivZero.exists_lift_isMonHom F.fib.2.1 F'.fib.2.1 f
  have := F'.P₀.isAb.comm
  obtain ⟨M, hM⟩ := exists_linearMap f₀ F.basis F'.basis
  have hd : F.IsDiffOf F' f M := by
    rintro u c ⟨hu, w, hw, hc⟩
    refine ⟨isTangent_comp_hom f hu, w ≫ f₀, ?_, hM c w hc⟩
    unfold IsVecOver at hw ⊢
    rw [Over.comp_left, Over.comp_left, Category.assoc, e, ← Category.assoc, hw, Category.assoc]
  have hcoord : ∀ u c c', F'.IsCoord u c → F'.IsCoord u c' → c = c' := by
    rintro u c c' ⟨-, w, hw, hc⟩ ⟨-, w', hw', hc'⟩
    obtain rfl : w = w' := Over.OverMorphism.ext (F'.fib.2.1.1.hom_ext (hw.trans hw'.symm) ((Over.w _).trans (Over.w _).symm))
    exact (F'.basis.2 w ((LieComb.lieComb_algebra K _ _ F'.v F'.basis.1).2.1 c w hc)).unique hc hc'
  have huniq : ∀ N, F.IsDiffOf F' f N → N = M := fun N hN => by
    refine LinearMap.ext_on (_root_.GlobalTheory.CM.LieLattice.lieLat_fg_and_span_eq_top K P F).2 fun c hc => ?_
    refine Submodule.span_induction (p := fun c _ => N c = M c) ?_ ?_ ?_ ?_ hc
    · rintro c ⟨u, hu⟩
      exact hcoord _ _ _ (hN u c hu) (hd u c hu)
    · simp
    · intro x y _ _ hx hy
      rw [map_add (f := _), map_add (f := _), hx, hy]
    · intro r x _ hx
      rw [← algebraMap_smul K r x, map_smul, map_smul, hx]
  refine ⟨⟨M, hd, huniq⟩, f₀, hf₀, e, fun N hN => ?_⟩
  rw [huniq N hN]
  exact hM

end GlobalTheory.CM.DiffCoord
end

-- bundled from Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.IsModelAtIntegralIffMemLieLat
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory Formalism.L2.LamCM
open scoped CategoryTheory.Obj ComplexOrder
open GlobalTheory GlobalTheory.CM GlobalTheory.LamF

namespace GlobalTheory.LamF

theorem isModelAt_integral_iff_mem_lieLat : ∀ (K : Type) [Field K] [NumberField K] (A : Out.PolAV (Sp (𝓞 K))) (x : KeyIn K) (φ : x.P.A.left ⟶ A.A.left) (hf : IsPolFibre (algebraMap (𝓞 K) K) A x.P φ) (p : HeightOneSpectrum (𝓞 K)) (M : Matrix (Fin x.P.g) (Fin x.P.g) K), IsModelAt A x φ p M → ∀ c : Fin x.P.g → K, (∀ m, p.valuation K (Matrix.vecMul c M⁻¹ m) ≤ 1) ↔ ∃ s : 𝓞 K, s ∉ p.asIdeal ∧ s • c ∈ (GenFib.mk x.P φ hf x.v x.basis : GenFib A).lieLat := by
  intro K _ _ A x φ hf p M hM c
  obtain ⟨R, _, _, _, _, _, ρ, xR, φR, hg, hρ, hval, hfib, hdet, hw⟩ := hM
  letI : Algebra (𝓞 K) R := ρ.toAlgebra
  haveI : IsScalarTower (𝓞 K) R K := IsScalarTower.of_algebraMap_eq' hρ.symm
  haveI : IsLocalization p.asIdeal.primeCompl R := (range_eq_valuationRing_iff_isLocalization K p R).1 hval
  have hG : IsGrpPullback xR.P.A A.A (spMap (algebraMap (𝓞 K) R)) φR := hfib.1
  have n : IsGrpPullback x.P.A A.A (spMap (algebraMap R K) ≫ spMap (algebraMap (𝓞 K) R)) φ :=
    hf.2.1.congr (by rw [spMap_comp_spMap]; exact congrArg spMap hρ.symm) rfl
  have w : φ ≫ A.A.hom = (x.P.A.hom ≫ spMap (algebraMap R K)) ≫ spMap (algebraMap (𝓞 K) R) :=
    n.1.w.trans (Category.assoc _ _ _).symm
  have e₁ := hG.1.lift_fst _ _ w
  have e₂ := hG.1.lift_snd _ _ w
  generalize hG.1.lift _ _ w = ψ at e₁ e₂
  have hψ : IsGrpPullback x.P.A xR.P.A (spMap (algebraMap R K)) ψ := hG.cancel (e₁ ▸ n) e₂
  choose wK hwK hwK' using hw
  have hb : IsLieBasis (fun k : Fin x.P.g => xR.v (k.cast hg.symm)) := by
    have key : ∀ (m : ℕ) (h : xR.P.g = m), IsLieBasis (fun k : Fin m => xR.v (k.cast h.symm)) := by
      intro m h
      subst h
      exact xR.basis
    exact key _ hg
  have hov : ∀ k, IsVecOver (algebraMap R K) ψ (xR.v (k.cast hg.symm)) (wK k) := by
    intro k
    refine hG.1.hom_ext ?_ ?_
    · rw [Category.assoc, e₁, hwK' k, Category.assoc, points_sums_eq_products.2]
    · rw [Category.assoc, Category.assoc, e₂, Over.w (xR.v _), ← Category.assoc, Over.w (wK k)]
      exact (PolFibre.spMap_dual_hom _).symm
  obtain ⟨h1, h2⟩ := _root_.GlobalTheory.CM.LieLoc.lieLat_localization K A (GenFib.mk x.P φ hf x.v x.basis) R p.asIdeal.primeCompl xR.P.A φR ψ _ wK M
    hG hψ e₁ hb fun i => ⟨hov i, hwK i⟩
  have hU : IsUnit M.det := hdet.isUnit
  constructor
  · intro hc
    choose a ha using fun m => (hval _).2 (hc m)
    obtain ⟨t, ht⟩ := IsLocalization.exist_integer_multiples_of_finite p.asIdeal.primeCompl a
    choose b hb' using ht
    choose s hs hs' using h1
    have hcM : c = ∑ i, Matrix.vecMul c M⁻¹ i • M i := by
      rw [← Matrix.vecMul_eq_sum, Matrix.vecMul_vecMul, Matrix.nonsing_inv_mul _ hU, Matrix.vecMul_one]
    refine ⟨(∏ i, s i) * t, Submonoid.mul_mem p.asIdeal.primeCompl (Submonoid.prod_mem _ fun i _ => hs i) t.2, ?_⟩
    rw [hcM, Finset.smul_sum]
    refine Submodule.sum_mem _ fun i _ => ?_
    have e : (t : 𝓞 K) • Matrix.vecMul c M⁻¹ i = algebraMap (𝓞 K) K (b i) := by
      rw [← ha, IsScalarTower.algebraMap_apply (𝓞 K) R K, hb', Algebra.smul_def, Algebra.smul_def, map_mul,
        ← IsScalarTower.algebraMap_apply]
    rw [mul_smul, ← smul_assoc (t : 𝓞 K), e, algebraMap_smul, ← Finset.prod_erase_mul _ _ (Finset.mem_univ i), mul_smul,
      smul_comm (s i)]
    exact Submodule.smul_mem _ _ (Submodule.smul_mem _ _ (hs' i))
  · rintro ⟨s, hs, hc⟩ m
    obtain ⟨a, ha⟩ := h2 _ hc
    have e : s • Matrix.vecMul c M⁻¹ = fun i => algebraMap R K (a i) := by
      rw [← Matrix.smul_vecMul]
      erw [ha]
      rw [← Matrix.vecMul_eq_sum, Matrix.vecMul_vecMul, Matrix.mul_nonsing_inv _ hU, Matrix.vecMul_one]
    have e' : algebraMap (𝓞 K) K s * Matrix.vecMul c M⁻¹ m = algebraMap R K (a m) := by
      rw [← Algebra.smul_def]
      exact congrFun e m
    have h3 := (hval _).1 ⟨a m, e'.symm⟩
    rwa [map_mul, (p.valuation_eq_one_iff_notMem (K := K)).2 hs, _root_.one_mul] at h3

end GlobalTheory.LamF
end

-- bundled from Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.UniversalTripleFibreKeyDataBaseChangeKeyPullbackStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.LamCM Formalism.L2.Pj
open scoped ComplexOrder
open GlobalTheory GlobalTheory.CM GlobalTheory.Frames GlobalTheory.LamT

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.universalTripleFibreKeyData_baseChange_keyPullback : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (S S' : Type) [CommRing S] [CommRing S'] [Nontrivial S'] (φ : S →+* S') (x : Sp S ⟶ Xo.X) (x' : Sp S' ⟶ Xo.X) (Φ : FibKey Xo S x) (Φ' : FibKey Xo S' x') (s : LB.Sec (PPx x)) (s' : LB.Sec (PPx x')), x' = spMap φ ≫ x → SecTie Φ.m Φ.th s → SecTie Φ'.m Φ'.th s' → SecBC φ 1 x x' s s' → ∃ (hg : Φ'.T.g = Φ.T.g) (v' : Fin Φ'.T.g → (epsR S' ⟶ Φ'.T.t.G)) (hv' : IsLieBasis v'), KeyPB ({ Φ' with v := v', basis := hv' } : FibKey Xo S' x').key Φ.key φ ∧ ∀ i, (v' i).left ≫ Φ'.m.φ = spMap (Formalism.L2.Pj.dualMap φ) ≫ (Φ.v (i.cast hg)).left ≫ Φ.m.φ := by
  first | exact @GlobalTheory.LamT.fibKey_keyPB | exact GlobalTheory.LamT.fibKey_keyPB | (intros; apply GlobalTheory.LamT.fibKey_keyPB <;> assumption)
end

