module

public import Mathlib
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0003
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.RigidSys
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Splits
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0006
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.GtBaseChangeSt
public import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.Bundle0001
public import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissiblePadicIntMaximalIdeal
public import Development.AbelianVarietyTheory.Definitions.ArchimedeanThetaValues.OneAddZeta21PowSevenAddPowFourteenEqZero
public import Development.AbelianVarietyTheory.Definitions.ArchimedeanThetaValues.IsCoprimeTwoSubRtTwoAddRt
public import Development.AbelianVarietyTheory.Definitions.ArchimedeanThetaValues.ToMatrixTrFormBaseChange
public import Development.AbelianVarietyTheory.Definitions.Uniformization.PointEqOfSubsingleton
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0036
public import Development.AbelianVarietyTheory.BlockTheory.CMModuli.LocalFramePowerSections
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0043
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0020
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsHolPeriods
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
public import Development.AbelianVarietyTheory.Proofs.ThetaFamilyOrigin.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.ThetaFamilyOrigin.AppLESurjective
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0124
public import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.FiniteHomogeneousInf
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0123
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.BCTools
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.PrecompleteBases.PsbLb
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.Bundle0004
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.BijectiveAlgebraMapIntegralClosureOfBirational
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0038
public import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.TwistingSheafOneChartEqPreimageStandardChart
public import Development.AbelianVarietyTheory.Definitions.ShimuraVarieties.FlatImageOfOverFractionFieldOfValuationRing

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.ModuliProofs.CubicalBundlePairingCompatiblePullback
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct Pointwise
open GlobalTheory.Models
open GlobalTheory.UU

namespace GlobalTheory.UU

theorem cubV_of_pmaps {S S' : Scheme.{0}} {f : S' ⟶ S} {G : Over S} [GrpObj G] [IsCommMonObj G] {G' : Over S'}
    [GrpObj G'] [IsCommMonObj G'] (m : CubeMap G' G) (hw : m.F ≫ G.hom = G'.hom ≫ f) {L : RigLB G} {L' : RigLB G'}
    {c : CubicalStr G L} {c' : CubicalStr G' L'} {w : LB.Iso L'.L (L.L.pull m.F)}
    (H : PMaps w (thφ G' (x3 G')) (thφ G (x3 G)) thε c'.t c.t m.F3) {T : Over S'} {z : T.left} {J J'}
    (hJ : Good L.L z J) (hJ' : Good L'.L z J') (a b d : T ⟶ G') :
    @id (T.left.presheaf.stalk z)ˣ (cubV c (T := Over.mk (T.hom ≫ f)) z J (Out.toBase hw a) (Out.toBase hw b)
      (Out.toBase hw d)) =
      (∏ I : thK.{0}, (fun q => gw w q z (J (q ≫ m.F)) (J' q)) ((lift a (lift b d)).left ≫ thφ G' (x3 G') I) ^ thε I) *
        cubV c' z J' a b d := by
  have co : ∀ i : Fin 3, m.F3 ≫ (x3 G i).left = (x3 G' i).left ≫ m.F := fun i => by
    have h := m.psum_comm {i}
    rw [psum_single, psum_single] at h
    exact h.symm
  have q : (lift a (lift b d)).left ≫ m.F3 =
      (lift (Out.toBase hw a) (lift (Out.toBase hw b) (Out.toBase hw d))).left := hom_ext_triple _ fun i => by
    rw [Category.assoc, co, ← Category.assoc, ← Over.comp_left, ← Over.comp_left]
    fin_cases i <;> simp [x3] <;> rfl
  have e := H _ (lift a (lift b d)).left z (fun I => J (((lift a (lift b d)).left ≫ thφ G' (x3 G') I) ≫ m.F))
    (fun I => J' ((lift a (lift b d)).left ≫ thφ G' (x3 G') I)) (fun I => hJ _) (fun I => hJ' _)
  refine Eq.trans ?_ e
  refine (congrArg (fun r => val (L := L.L) (φ := thφ G (x3 G)) (ε := thε) c.t r z J) q.symm).trans ?_
  refine val_of _ _ _ _ _ fun I => congrArg J ?_
  rw [Category.assoc, Category.assoc]
  exact congrArg _ (m.psum_comm I.down).symm

theorem cubWeil_of_isPullCubical : ∀ (S S' : Scheme.{0}) (f : S' ⟶ S) (G : Over S) [GrpObj G] [IsCommMonObj G] (G' : Over S') [GrpObj G'] [IsCommMonObj G'] (m : CubeMap G' G) (hw : m.F ≫ G.hom = G'.hom ≫ f), (∀ (T : Over S') (x y : T ⟶ G'), Out.toBase hw (x * y) = Out.toBase hw x * Out.toBase hw y) → ∀ (L : RigLB G) (L' : RigLB G') (c : CubicalStr G L) (c' : CubicalStr G' L'), m.IsPullCubical c' c → ∀ (N : ℕ) (T : Over S') (x y : T ⟶ G') (ζ : Γ(T.left, ⊤)ˣ), CubWeil c' N x y ζ → CubWeil c N (Out.toBase hw x) (Out.toBase hw y) ζ := by
  intro S S' f G _ _ G' _ _ m hw mul L L' c c' h N T x y ζ hζ
  obtain ⟨w, -, -, H⟩ := (isPullCubical_iff m c c').1 h
  let β := toBaseHom mul T
  refine ⟨(map_pow β x N).symm.trans ((congrArg β hζ.1).trans (map_one β)),
    (map_pow β y N).symm.trans ((congrArg β hζ.2.1).trans (map_one β)), fun z J hJ => ?_⟩
  obtain ⟨J', hJ'⟩ := exists_good_pt L'.isLB (Z := T.left) z
  obtain ⟨W, hW⟩ : ∃ W : (T.left ⟶ G'.left) → (T.left.presheaf.stalk z)ˣ,
    W = fun q => gw w q z (J (q ≫ m.F)) (J' q) := ⟨_, rfl⟩
  let θ : (Over.mk (T.hom ≫ f) ⟶ G) → (Over.mk (T.hom ≫ f) ⟶ G) → (Over.mk (T.hom ≫ f) ⟶ G) →
    (T.left.presheaf.stalk z)ˣ := cubV c (T := Over.mk (T.hom ≫ f)) z J
  have a' : ∀ a b d : T ⟶ G', θ (β a) (β b) (β d) * W (a * b).left * W (a * d).left * W (b * d).left *
      W (1 : T ⟶ G').left = W (a * b * d).left * W a.left * W b.left * W d.left * cubV c' z J' a b d := by
    intro a b d
    have e := (cubV_of_pmaps m hw H (T := T) (z := z) hJ hJ' a b d).trans (congrArg₂ (· * ·)
      ((congrArg (fun V : (T.left ⟶ G'.left) → (T.left.presheaf.stalk z)ˣ =>
        ∏ I : thK.{0}, V ((lift a (lift b d)).left ≫ thφ G' (x3 G') I) ^ thε I) hW.symm).trans (prod_cub a b d W)) rfl)
    have e' : θ (β a) (β b) (β d) = _ := e
    rw [e']
    apply Additive.ofMul.injective
    simp only [ofMul_mul, ofMul_inv]
    abel
  exact cubN_ratio_twist β (fun x => W x.left) a' hζ.1 hζ.2.1 (hζ.2.2 z J' hJ')

end GlobalTheory.UU
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ModuliProofs.DataAtTraitsOfTraitData
section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.TraitDataIntrinsic

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {l : Level H} {Xo : Moduli D l}
  {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F} (Y : Model Xo c β)

theorem j_s : Y.j ≫ Y.s = pullback.snd _ _ ≫ spMap β := by
  rw [Model.j, Category.assoc, pullback.condition, ← Category.assoc, Y.jQ_over]

theorem exists_generic {S T : Scheme.{0}} {i : T ⟶ S} {χ : S ⟶ Y.X} {t : SAB H S} (m : SABMap t Y.t χ) {v : T ⟶ Xo.XF c}
    (hv : v ≫ Y.j = i ≫ χ) : ∃ (t' : SAB H T) (m₁ : SABMap t' t i) (n : SABMap t' Y.oF.t v)
      (m₂ : SABMap t' Xo.univ.t (v ≫ pullback.fst _ _)), m₁.φ ≫ m.φ = n.φ ≫ Y.m.φ ∧ m₂.φ = n.φ ≫ Y.m0.toSABMap.φ := by
  obtain ⟨t', ⟨p⟩⟩ := (GlobalTheory.ModelPoints.model_points_charts E H D l Xo c O β Y).2.1 _ (i ≫ χ)
  obtain ⟨m₁, h₁⟩ := GlobalTheory.ObjMaps.exists_sab_cancel m p
  have key : ∀ u : T ⟶ Y.X, v ≫ Y.j = u → ∀ p : SABMap t' Y.t u, ∃ n : SABMap t' Y.oF.t v, p.φ = n.φ ≫ Y.m.φ := by
    rintro _ rfl p
    exact GlobalTheory.ObjMaps.exists_sab_cancel Y.m p
  obtain ⟨n, hn⟩ := key _ hv p
  obtain ⟨m₂, h₂⟩ := GlobalTheory.ObjMaps.exists_sab_comp Y.m0.toSABMap n
  exact ⟨t', m₁, n, m₂, h₁.symm.trans hn, h₂⟩

end GlobalTheory.TraitDataIntrinsic
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ModuliProofs.DenseTorsionAndEqOne
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZV

namespace GlobalTheory.PrimePowerTorsion

theorem dense_torsion (hA : Out.AmpleSt) (hK : Out.KerPowSt) (hI : Out.IrredSt) (K : Type) [Field K] [IsAlgClosed K]
    (P : Out.PolAV (Sp K)) (l : ℕ) (hl : 2 ≤ l) (hlK : (l : K) ≠ 0) :
    Dense (⋃ x ∈ {x : 𝟙_ (Over (Sp K)) ⟶ P.A | ∃ j : ℕ, x ^ l ^ j = 1}, Set.range x.left) := by
  have := P.isAb.comm
  refine dense_iff_inter_open.2 fun U hU ⟨x, hx⟩ => ?_
  obtain ⟨a, -, s, hs, hle, -⟩ := (isAmpleLB_of_relAmple_of_isAffine P.A P.isLB P.ample).exists_affine_le
    (x := x) (U := ⟨U, hU⟩) hx
  have gen : ∀ N : ℕ, 4 ≤ N → ∀ y : P.A.left, ∃ t : (lbPow P.L N).Sec, y ∈ Out.nonzeroLocus t := fun N hN y => by
    obtain ⟨m, t, ht, -⟩ := veryAmple_lbPow hA K P N hN
    obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.1 (ht.ge (Set.mem_univ y))
    exact ⟨t i, hi⟩
  obtain ⟨m, hm, ham⟩ : ∃ m : ℕ, 4 ≤ m ∧ a + m = l ^ (a + 4) := by
    have := Nat.lt_pow_self (n := a + 4) (show 1 < l by omega)
    exact ⟨l ^ (a + 4) - a, by omega, by omega⟩
  obtain ⟨t, ht⟩ := gen m hm x
  let p : (Out.baseOver (Sp K)).left := IsLocalRing.closedPoint K
  obtain ⟨t', ht'⟩ := gen (a + m) (by omega) ((1 : Out.baseOver (Sp K) ⟶ P.A).left p)
  have e := nonzeroLocus_secMul s t
  obtain ⟨b, hb, q, hq⟩ := TorsionDense.exists_mem_nonzeroLocus P hI hK (a + m) (by omega)
    (by rw [ham, Nat.cast_pow]; exact pow_ne_zero _ hlK)
    {x | ∃ j : ℕ, x ^ l ^ j = 1} (fun w hw b ⟨j, hb⟩ => ⟨a + 4 + j, by
      rw [mul_pow, pow_add, pow_mul w, ← ham, hw, one_pow, mul_comm _ (l ^ j), pow_mul, hb, one_pow,
        _root_.one_mul]⟩)
    (secMul s t) t' x (e.ge ⟨hs, ht⟩) 1 ⟨0, one_pow _⟩ p ht'
  exact ⟨b.left q, hle (e.le hq).1, Set.mem_iUnion₂.2 ⟨b, hb, q, rfl⟩⟩

theorem dense_torsion_and_eq_one :
    Out.Laws → Out.Laws2 → ∀ (K : Type) [Field K] [IsAlgClosed K] (P : Out.PolAV (Sp K)) (l : ℕ), l.Prime → (l : K) ≠ 0 → Dense (⋃ x ∈ {x : 𝟙_ (Over (Sp K)) ⟶ P.A | ∃ j : ℕ, x ^ l ^ j = 1}, Set.range x.left) ∧ ∀ f : P.A ⟶ P.A, (∀ (j : ℕ) (x : 𝟙_ (Over (Sp K)) ⟶ P.A), x ^ l ^ j = 1 → x ≫ f = 1) → f = 1 := by
  intro h1 _ K _ _ P l hl hlK
  have hD := dense_torsion h1.ample h1.kerPow h1.irred K P l hl.two_le hlK
  refine ⟨hD, fun f hf => Over.OverMorphism.ext ?_⟩
  have := polAV_isIntegral_of_isAlgClosed K P
  have := P.isAb.proper
  let g : P.A ⟶ P.A := 1
  suffices IsDominant (equalizer.ι f.left g.left) from
    ext_of_isDominant_of_isSeparated P.A.hom ((Over.w f).trans (Over.w g).symm) (equalizer.ι f.left g.left)
      (equalizer.condition _ _)
  refine ⟨Dense.mono (fun y hy => ?_) hD⟩
  obtain ⟨x, ⟨j, hx⟩, q, rfl⟩ := Set.mem_iUnion₂.1 hy
  have hxy : x.left ≫ f.left = x.left ≫ g.left :=
    congrArg CommaMorphism.left ((hf j x hx).trans (MonObj.comp_one x).symm)
  refine ⟨equalizer.lift x.left hxy q, ?_⟩
  rw [← Scheme.Hom.comp_apply, equalizer.lift_ι]

end GlobalTheory.PrimePowerTorsion
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ModuliProofs.E8SharpClassPrimitiveIsoClosed
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM

noncomputable section

namespace GlobalTheory.SharpPrim

theorem matrix_identities {n : Type} [Fintype n] [DecidableEq n] {W m m' : Matrix n n ℤ}
    (hd : (W + W.transpose).det = 1) (h : (W + W.transpose) * m = W) (h' : (W + W.transpose) * m' = W.transpose) :
    m + m' = 1 ∧ m.transpose * (W + W.transpose) = (W + W.transpose) * m' := by
  set G := W + W.transpose with hG
  have hu : IsUnit G.det := by rw [hd]; exact isUnit_one
  have hT : G.transpose = G := by
    rw [hG, Matrix.transpose_add, Matrix.transpose_transpose, add_comm]
  constructor
  · have key : G * (m + m') = G := by rw [Matrix.mul_add, h, h']
    calc m + m' = G⁻¹ * (G * (m + m')) := by
          rw [← Matrix.mul_assoc, Matrix.nonsing_inv_mul G hu, Matrix.one_mul]
      _ = 1 := by rw [key, Matrix.nonsing_inv_mul G hu]
  · have ht := congrArg Matrix.transpose h
    rw [Matrix.transpose_mul, hT] at ht
    rw [ht, h']

theorem prod_mul_prod {M : Type} [CommGroup M] {n : ℕ} (x : Fin n → M) {m m' : Matrix (Fin n) (Fin n) ℤ}
    (h : m + m' = 1) (u : Fin n) :
    (List.ofFn fun v => x v ^ m u v).prod * (List.ofFn fun v => x v ^ m' u v).prod = x u := by
  have hm : ∀ v, m u v + m' u v = if u = v then 1 else 0 := by
    intro v
    have e := congrFun (congrFun h u) v
    rwa [Matrix.add_apply, Matrix.one_apply] at e
  rw [List.prod_ofFn, List.prod_ofFn, ← Finset.prod_mul_distrib]
  simp_rw [← zpow_add, hm]
  rw [Finset.prod_eq_single u (fun v _ hv => by rw [if_neg (Ne.symm hv), zpow_zero])
    (fun hu => absurd (Finset.mem_univ u) hu), if_pos rfl, zpow_one]

variable {o : Type} [CommRing o] {S : Scheme.{0}} {g k h : ℕ} {J : Type} {b : TBase o k} {s : S ⟶ Sp o}

theorem isSharp_of_tmap {W : Matrix (Fin 8) (Fin 8) ℤ} {a : J → Matrix (Fin 8) (Fin 8) ℤ}
    {bas : (Fin (2 * g) → ℤ) ≃ₗ[ℤ] (Fin 8 → (Fin h ⊕ Fin h → ℤ))} {t t' : TObj g k J b s}
    {c : SiegPre h k (b.ζ : o) s} (H : IsSharp W a bas t c) (m : TMap t' t (𝟙 _)) : IsSharp W a bas t' c := by
  obtain ⟨φ, hpb, hLφ, hpt, hact⟩ := m
  obtain ⟨pr, hpr, huniv, hL, hpa, hlev⟩ := H
  have : IsMonHom (Iso.refl t.A).hom := inferInstanceAs (IsMonHom (𝟙 t.A))
  obtain ⟨e, he, heφ'⟩ := grpPullback_iso hpb (isGrpPullback_of_iso (Iso.refl t.A))
  have heφ : e.hom.left = φ := by simpa using heφ'
  have hcomm : ∀ j, t'.act j ≫ e.hom = e.hom ≫ t.act j := by
    intro j
    ext
    simp only [Over.comp_left, heφ, hact j]
  refine ⟨fun u => e.hom ≫ pr u, fun u => ?_, fun T y => ?_, ?_, fun j u => ?_, fun i u => ?_⟩
  · have := hpr u
    infer_instance
  · obtain ⟨x0, hx0, hu0⟩ := huniv T y
    refine ⟨x0 ≫ e.inv, fun u => by simpa using hx0 u, fun x hx => ?_⟩
    have hx' : x ≫ e.hom = x0 := hu0 _ fun u => by simpa using hx u
    rw [← hx']
    simp
  · have hfun : (fun uv : Fin 8 × Fin 8 => (lift (e.hom ≫ pr uv.1) (e.hom ≫ pr uv.2)).left) =
        fun uv => φ ≫ (lift (pr uv.1) (pr uv.2)).left := by
      funext uv
      rw [← comp_lift, Over.comp_left, heφ]
    rw [hfun]
    refine (CechPic.cls_eq_iff t'.isLB (LB.isLB_linComb c.isLB _ _)).1 ?_
    set_option synthInstance.maxHeartbeats 100000 in
      rw [(CechPic.cls_eq_iff t'.isLB (pull_isLB t.isLB φ)).2 hLφ, CechPic.cls_pull t.isLB,
      (CechPic.cls_eq_iff t.isLB (LB.isLB_linComb c.isLB _ _)).2 hL,
      CechPic.cls_linComb c.isLB, CechPic.cls_linComb c.isLB, map_sum]
    refine Finset.sum_congr rfl fun uv _ => ?_
    rw [map_zsmul, ← CechPic.pull_comp]
  · rw [← Category.assoc, hcomm j, Category.assoc, hpa j u, PowerAdjoint.comp_prod_zpow]
  · have hp := hpt i
    rw [Category.id_comp] at hp
    rw [← hlev i u, Over.comp_left, Over.comp_left, heφ, ← Category.assoc, hp, Over.comp_left]

end GlobalTheory.SharpPrim

theorem GlobalTheory.sharpClass_prim_and_iso : (∀ (S : Scheme.{0}) (P : Out.PolAV S) (M : LB P.A.left), M.IsLB → ∃ t : LB.Gen (Theta P.A M), t.IsGen) → ∀ (o : Type) [CommRing o] (g k : ℕ) (J : Type) (b : TBase o k) (em : o →+* ℂ) (w w' : J) (h : ℕ) (W : Matrix (Fin 8) (Fin 8) ℤ) (a : J → Matrix (Fin 8) (Fin 8) ℤ) (bas : (Fin (2 * g) → ℤ) ≃ₗ[ℤ] (Fin 8 → (Fin h ⊕ Fin h → ℤ))) (t : TObj g k J b (spMap em)), SharpClass W a bas em t → (IsE8 W → (W + W.transpose) * a w = W → (W + W.transpose) * a w' = W.transpose → t.Prim w w') ∧ ∀ t' : TObj g k J b (spMap em), TMap t' t (𝟙 _) → SharpClass W a bas em t' := by
  intro hΘ o _ g k J b em w w' h W a bas t ht
  obtain ⟨c, hc, hs⟩ := ht
  refine ⟨fun hE hw hw' => ?_, fun t' m => ⟨c, hc, SharpPrim.isSharp_of_tmap hs m⟩⟩
  obtain ⟨pr, hpr, huniv, hL, hact, -⟩ := hs
  have hid := SharpPrim.matrix_identities hE.2 hw hw'
  have key := PowerAdjoint.matrix_primitive_adjoint hΘ W ℂ o (spMap em) h k (b.ζ : o) c t.pol pr hpr huniv hL
    (a w) (t.act w) (hact w)
  refine ⟨?_, key.2 (a w') (t.act w') (hact w') hid.2, key.1 hw⟩
  obtain ⟨x0, -, hu0⟩ := huniv t.A pr
  have h1 : ∀ u, (t.act w * t.act w') ≫ pr u = pr u := by
    intro u
    have := hpr u
    rw [MonObj.mul_comp, hact w u, hact w' u]
    exact SharpPrim.prod_mul_prod pr hid.1 u
  rw [hu0 _ h1, hu0 (𝟙 t.A) fun u => Category.id_comp _]

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ModuliProofs.EighthPowerIntegerMatrixPrimitiveAdjointStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
theorem _root_.GlobalTheory.T.eighthPower_integerMatrix_primitive_adjoint : (∀ (S : Scheme.{0}) (P : Out.PolAV S) (M : LB P.A.left), M.IsLB → ∃ t : LB.Gen (Theta P.A M), t.IsGen) → ∀ (W : Matrix (Fin 8) (Fin 8) ℤ) (K : Type) [Field K] (o : Type) [CommRing o] (s : Sp K ⟶ Sp o) (h k : ℕ) (ζ : o) (c : SiegPre h k ζ s) (P : Out.PolAV (Sp K)) (pr : Fin 8 → (P.A ⟶ c.A)), (∀ u, IsMonHom (pr u)) → (∀ (T : Over (Sp K)) (y : Fin 8 → (T ⟶ c.A)), ∃! x : T ⟶ P.A, ∀ u, x ≫ pr u = y u) → LBIso P.L (LB.LinComb c.P (K := Fin 8 × Fin 8) (fun uv => (lift (pr uv.1) (pr uv.2)).left) (fun uv => W uv.1 uv.2)) → ∀ (m : Matrix (Fin 8) (Fin 8) ℤ) (α : P.A ⟶ P.A), (∀ u, α ≫ pr u = (List.ofFn fun v => pr v ^ m u v).prod) → ((W + W.transpose) * m = W → LBIso P.L (cubeLB P.A ![𝟙 P.A, α] P.L)) ∧ ∀ (m' : Matrix (Fin 8) (Fin 8) ℤ) (α' : P.A ⟶ P.A), (∀ u, α' ≫ pr u = (List.ofFn fun v => pr v ^ m' u v).prod) → m.transpose * (W + W.transpose) = (W + W.transpose) * m' → LBIso (cubeLB P.A ![fst P.A P.A ≫ α, snd P.A P.A] P.L) (cubeLB P.A ![fst P.A P.A, snd P.A P.A ≫ α'] P.L) := by
  first | exact @GlobalTheory.PowerAdjoint.matrix_primitive_adjoint | exact GlobalTheory.PowerAdjoint.matrix_primitive_adjoint | (intros; apply GlobalTheory.PowerAdjoint.matrix_primitive_adjoint <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ModuliProofs.EtaleAndSurjectiveOfDensePartMonoFiniteEtale
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct Pointwise
open GlobalTheory.Models

namespace GlobalTheory

theorem isOpenImmersion_of_isFinite_of_densePart {U W Z : Scheme.{0}} [IsIntegral W]
    [IsLocallyNoetherian Z] [GlobalTheory.IsNormalScheme Z] (j : U ⟶ W) (g : W ⟶ Z) [IsFinite g]
    [IsPreimmersion j] [Flat j] [IsDominant j] [QuasiCompact j] [Flat (j ≫ g)]
    [SurjectiveOnStalks (j ≫ g)] : IsOpenImmersion g := by
  have hη : genericPoint W ∈ genericPoints W := by
    rw [genericPoints_eq_singleton]; rfl
  obtain ⟨u, hu⟩ := genericPoints_subset_range_of_isDominant j hη
  let V : Z.Opens := GlobalTheory.IsNormalScheme.component
    ⟨_, irreducibleComponent_mem_irreducibleComponents (g (genericPoint W))⟩
  have hVc : IsClosed (V : Set Z) := GlobalTheory.IsNormalScheme.isClosed_component _
  have : IsIntegral V.toScheme := GlobalTheory.IsNormalScheme.isIntegral_component _
  have hr : Set.range g ⊆ Set.range V.ι := by
    rintro _ ⟨w, rfl⟩
    rw [Scheme.Opens.range_ι]
    exact (((genericPoint_spec W).specializes (Set.mem_univ w)).map g.continuous).mem_closed hVc
      mem_irreducibleComponent
  let g' : W ⟶ V.toScheme := IsOpenImmersion.lift V.ι g hr
  have hg' : g' ≫ V.ι = g := IsOpenImmersion.lift_fac _ _ _
  have : IsFinite (g' ≫ V.ι) := hg' ▸ inferInstance
  have : IsFinite g' := IsFinite.of_comp g' V.ι
  have hlift : j ≫ g' = IsOpenImmersion.lift V.ι (j ≫ g) (by
      rintro _ ⟨w, rfl⟩
      exact hr ⟨j w, rfl⟩) :=
    IsOpenImmersion.lift_uniq _ _ _ _ (by rw [Category.assoc, hg'])
  have hs : SurjectiveOnStalks ((j ≫ g') ≫ V.ι) := by rw [Category.assoc, hg']; infer_instance
  have : Flat (j ≫ g') := by
    rw [hlift]
    exact MorphismProperty.of_isPullback (P := @Flat)
      (IsOpenImmersion.isPullback_lift_id (j ≫ g) V.ι _).flip ‹Flat (j ≫ g)›
  have : SurjectiveOnStalks (j ≫ g') := SurjectiveOnStalks.of_comp _ V.ι
  have : IsDominant g' := by
    obtain ⟨u', hu', hu''⟩ := Flat.generalizingMap (j ≫ g')
      ((genericPoint_spec V.toScheme).specializes (Set.mem_univ ((j ≫ g') u)))
    refine ⟨?_⟩
    refine Dense.mono (s₁ := {genericPoint V.toScheme}) ?_ ?_
    · rintro _ rfl
      exact ⟨j u', hu''⟩
    · exact dense_iff_closure_eq.mpr (genericPoint_spec V.toScheme)
  have : IsIso (g'.stalkMap (genericPoint W)) := by
    rw [← hu]
    have h := isIso_stalkMap_of_flat_of_surjectiveOnStalks (j ≫ g') u
    have := isIso_stalkMap_of_flat_of_surjectiveOnStalks j u
    rw [Scheme.Hom.stalkMap_comp] at h
    exact @IsIso.of_isIso_comp_right _ _ _ _ _ (g'.stalkMap (j u)) (j.stalkMap u) _ h
  have := isIso_of_isIntegralHom_of_isIso_stalkMap g' (fun y => inferInstance)
  rw [← hg']
  infer_instance

theorem etale_and_surjective_of_densePart_mono_finiteEtale : ∀ (S S₀ Y Y₀ Z : Scheme.{0}) [IsLocallyNoetherian S] [IsLocallyNoetherian Y] (j : S₀ ⟶ S) (j' : Y₀ ⟶ Y) (e : Y ⟶ S) (e₀ : Y₀ ⟶ S₀) (p : Z ⟶ S) (i : Y₀ ⟶ Z), ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme S → ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme Y → IsPreimmersion j → Flat j → IsDominant j → QuasiCompact j → IsPreimmersion j' → Flat j' → IsDominant j' → QuasiCompact j' → IsFinite e → j' ≫ e = e₀ ≫ j → IsFinite p → Etale p → i ≫ p = e₀ ≫ j → Surjective e₀ → Etale e₀ → Mono i → Etale e ∧ Surjective e := by
  intro S S₀ Y Y₀ Z _ _ j j' e e₀ p i hS hY _ _ _ _ _ _ _ _ _ hj _ _ hi _ _ _
  have hYn := GlobalTheory.IsNormalScheme.of_pred hY
  have : IsLocallyNoetherian Z := LocallyOfFiniteType.isLocallyNoetherian p
  have : GlobalTheory.IsNormalScheme Z := (isNormalScheme_iff Z).mpr
    (forall_isDomain_and_isIntegrallyClosed_stalk_of_smooth p
      ((isNormalScheme_iff S).mp (GlobalTheory.IsNormalScheme.of_pred hS)))
  obtain ⟨g, ⟨hg₁, hg₂⟩, -⟩ := existsUnique_lift_of_densePart Y Y₀ S Z j' hY ‹_› ‹_› ‹_› ‹_› p e i
    inferInstance (hi.trans hj.symm)
  have : IsFinite (g ≫ p) := hg₂ ▸ inferInstance
  have : IsFinite g := IsFinite.of_comp g p
  let k : Y₀ ⟶ pullback p j := pullback.lift i e₀ hi
  have hk₁ : k ≫ pullback.fst p j = i := pullback.lift_fst _ _ _
  have hk₂ : k ≫ pullback.snd p j = e₀ := pullback.lift_snd _ _ _
  have : Etale (k ≫ pullback.snd p j) := hk₂ ▸ inferInstance
  have : Etale k := Etale.of_comp k (pullback.snd p j)
  have : Mono (k ≫ pullback.fst p j) := hk₁ ▸ inferInstance
  have : Mono k := mono_of_mono k (pullback.fst p j)
  have : IsOpenImmersion k := IsOpenImmersion.of_flat_of_mono k
  have : Flat i := hk₁ ▸ inferInstance
  have : SurjectiveOnStalks i := hk₁ ▸ inferInstance
  constructor
  · have : IsZariskiLocalAtSource @Etale := HasRingHomProperty.instIsZariskiLocalAtSource
    rw [IsZariskiLocalAtSource.iff_of_iSup_eq_top (P := @Etale) _
      (GlobalTheory.IsNormalScheme.iSup_component (X := Y))]
    intro W
    have : IsDominant (j' ∣_ GlobalTheory.IsNormalScheme.component W) :=
      IsZariskiLocalAtTarget.restrict (P := @IsDominant) ‹IsDominant j'› _
    have h : j' ∣_ GlobalTheory.IsNormalScheme.component W ≫ (GlobalTheory.IsNormalScheme.component W).ι ≫ g =
        (j' ⁻¹ᵁ GlobalTheory.IsNormalScheme.component W).ι ≫ i := by
      rw [morphismRestrict_ι_assoc, hg₁]
    have : Flat (j' ∣_ GlobalTheory.IsNormalScheme.component W ≫
        (GlobalTheory.IsNormalScheme.component W).ι ≫ g) := h ▸ inferInstance
    have : SurjectiveOnStalks (j' ∣_ GlobalTheory.IsNormalScheme.component W ≫
        (GlobalTheory.IsNormalScheme.component W).ι ≫ g) := h ▸ inferInstance
    have := isOpenImmersion_of_isFinite_of_densePart (j' ∣_ GlobalTheory.IsNormalScheme.component W)
      ((GlobalTheory.IsNormalScheme.component W).ι ≫ g)
    rw [← hg₂, ← Category.assoc]
    infer_instance
  · have : IsDominant (j' ≫ e) := hj ▸ inferInstance
    have : IsDominant e := IsDominant.of_comp j' e
    refine ⟨?_⟩
    rw [← Set.range_eq_univ, ← e.isClosedMap.isClosed_range.closure_eq]
    exact e.denseRange.closure_range

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsIsProjOverIsPullbackOfIsLocalization
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct Pointwise
open GlobalTheory.Models

namespace GlobalTheory.ProjClosure

theorem exists_isProjOver_isPullback_of_isLocalization {O R : Type} [CommRing O] [CommRing R] [Algebra O R]
    (M : Submonoid O) [IsLocalization M R] {X : Scheme.{0}} (s : X ⟶ Sp R) (hs : IsProjOver s) :
    ∃ (X' : Scheme.{0}) (s' : X' ⟶ Sp O) (i : X ⟶ X'),
      IsProjOver s' ∧ IsPullback i s s' (spMap (algebraMap O R)) := by
  obtain ⟨N, c, hc, rfl⟩ := hs
  have P := GlobalTheory.ProjSpace.isPullback_baseChange N (algebraMap O R)
  have hf : Flat (spMap (algebraMap O R)) := GlobalTheory.flat_specMap_localization M R
  have hm : Mono (spMap (algebraMap O R)) := GlobalTheory.mono_specMap_localization M R
  have hq : QuasiCompact (spMap (algebraMap O R)) := inferInstance
  have : Flat (GlobalTheory.ProjSpace.baseChange N (algebraMap O R)) := MorphismProperty.of_isPullback P.flip hf
  have : Mono (GlobalTheory.ProjSpace.baseChange N (algebraMap O R)) :=
    (MorphismProperty.monomorphisms _).of_isPullback P.flip hm
  have : QuasiCompact (GlobalTheory.ProjSpace.baseChange N (algebraMap O R)) :=
    MorphismProperty.of_isPullback P.flip hq
  let j := c ≫ GlobalTheory.ProjSpace.baseChange N (algebraMap O R)
  have H := GlobalTheory.isPullback_toImage_of_isClosedImmersion j c _ rfl
  exact ⟨j.image, j.imageι ≫ PSpace.str O N, j.toImage, ⟨N, j.imageι, inferInstance, rfl⟩,
    H.flip.paste_vert P⟩

theorem exists_projective_closure : ∀ (O R : Type) [CommRing O] [CommRing R] [Algebra O R] (a : O) [IsLocalization.Away a R] (X : Scheme.{0}) (s : X ⟶ Sp R), IsProjOver s → ∃ (X' : Scheme.{0}) (s' : X' ⟶ Sp O) (i : X ⟶ X'), IsProjOver s' ∧ IsPullback i s s' (spMap (algebraMap O R)) :=
  fun _ _ _ _ _ a _ _ s hs =>
    exists_isProjOver_isPullback_of_isLocalization (Submonoid.powers a) s hs

end GlobalTheory.ProjClosure
end

