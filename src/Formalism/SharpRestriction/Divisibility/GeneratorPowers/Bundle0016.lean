module

public import Formalism.SharpRestriction.Divisibility.GeneratorPowers.Bundle0008
public import Formalism.SharpRestriction.Divisibility.GeneratorPowers.Bundle0012
public import Formalism.SharpRestriction.Divisibility.GeneratorPowers.Bundle0006
public import Formalism.SharpRestriction.Divisibility.GeneratorPowers.Bundle0010
public import Formalism.SharpRestriction.Divisibility.GeneratorPowers.FBIdJet
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.CartesianLiftThreeCompProjection
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.LBPull

@[expose] public section

-- bundled from Formalism.SharpRestriction.Divisibility.GeneratorPowers.MulGenScaleRight
section
set_option autoImplicit false

noncomputable section

namespace Formalism.MainNotions.ModuliIntegralCharts.H1.CIndFrFix2

open AlgebraicGeometry CategoryTheory Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open MvPolynomial (X)

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
variable {Xo : Moduli Dw l} {c : Coeff l} {S : Type} [CommRing S] [Algebra c.F S] (y : FrPt Xo c S) (d : ℕ)
variable (x : ∀ m, jO y d m 1 ⟶ Xo.univ.t.G)

theorem scaleGen_eq {Y : Scheme.{0}} {K : Type} [Fintype K] (φ : K → (Y ⟶ Xo.univ.t.G.left)) (ε : K → ℤ)
    (u : Γ(Y, ⊤)ˣ) (g : LB.Gen (LB.LinComb Xo.univ.t.PP.L φ ε)) :
    scaleGen φ ε u g = scaleGenG Xo.univ.t φ ε u g := rfl

theorem mulGen_scale_right {Y : Scheme.{0}} {K K' : Type} [Fintype K] [Fintype K'] (φ : K → (Y ⟶ Xo.univ.t.G.left))
    (ε : K → ℤ) (φ' : K' → (Y ⟶ Xo.univ.t.G.left)) (ε' : K' → ℤ) (v : Γ(Y, ⊤)ˣ)
    (g : LB.Gen (LB.LinComb Xo.univ.t.PP.L φ ε)) (g' : LB.Gen (LB.LinComb Xo.univ.t.PP.L φ' ε')) :
    LB.mulGen Xo.univ.t.PP.L φ ε φ' ε' g (scaleGenG Xo.univ.t φ' ε' v g') =
      scaleGenG Xo.univ.t _ _ v (LB.mulGen Xo.univ.t.PP.L φ ε φ' ε' g g') := by
  conv_lhs => rw [← FBIdLB.scaleGenG_one Xo.univ.t φ ε g]
  rw [FBIdLB.mulGen_scaleGenG, one_mul]

def tw (e : ∀ m, FrTy y d x m) (T : ∀ m, (Jet S (Fin 2 × Fin d) m)ˣ) (m : ℕ) : FrTy y d x m :=
  scaleGen _ _ (unitΓ (T m)) (e m)

abbrev sub (m : ℕ) {n' : ℕ} (φ : Fin 2 → Fin d → MvPolynomial (Fin n' × Fin d) S)
    (T : (Jet S (Fin 2 × Fin d) m)ˣ) : (Jet S (Fin n' × Fin d) m)ˣ :=
  Units.map (jetSubstP m fun p : Fin 2 × Fin d => φ p.1 p.2).toMonoidHom T

theorem pe_tw (e : ∀ m, FrTy y d x m) (T : ∀ m, (Jet S (Fin 2 × Fin d) m)ˣ) (m : ℕ) {n' : ℕ}
    (φ : Fin 2 → Fin d → MvPolynomial (Fin n' × Fin d) S) :
    pe y d x (tw y d x e T) m φ = scaleGenG Xo.univ.t _ _ (unitΓ (sub d m φ (T m))) (pe y d x e m φ) := by
  have h1 := FBIdLB.pullGen_scaleGenG Xo.univ.t (cφ ![jpt y d x m (0 : Fin 2), jpt y d x m (1 : Fin 2)]) (cε 2)
    (unitΓ (T m)) (e m) (homAt y.x (jetSubstP m fun p : Fin 2 × Fin d => φ p.1 p.2)).left
  rw [FBIdLB.unitΓ_homAt] at h1
  exact h1

theorem tw_zero (e : ∀ m, FrTy y d x m) (T : ∀ m, (Jet S (Fin 2 × Fin d) m)ˣ) (h0 : T 0 = 1) :
    tw y d x e T 0 = e 0 := by
  have h1 := FBIdLB.scaleGenG_one Xo.univ.t (cφ ![jpt y d x 0 (0 : Fin 2), jpt y d x 0 (1 : Fin 2)]) (cε 2) (e 0)
  have h2 : unitΓ (T 0) = 1 := by rw [h0, FBIdSy.unitΓ_one]
  show scaleGenG Xo.univ.t _ _ (unitΓ (T 0)) (e 0) = e 0
  rw [h2]
  exact h1

theorem tw_isGen (e : ∀ m, FrTy y d x m) (T : ∀ m, (Jet S (Fin 2 × Fin d) m)ˣ) (m : ℕ) (hg : (e m).IsGen) :
    (tw y d x e T m).IsGen := by
  intro i j
  have h := hg i j
  unfold tw scaleGen
  dsimp only
  erw [map_mul, map_mul, ReciprocityTheory.ChartRestriction.G.DVR.res_res', ReciprocityTheory.ChartRestriction.G.DVR.res_res', h]
  all_goals first | exact mul_left_comm _ _ _ | exact le_rfl

theorem isFrame_tw [StarRing (𝓞 E)] {F : Fin d → MvPowerSeries (Fin 2 × Fin d) S}
    {act : 𝓞 E → Fin d → MvPowerSeries (Fin 1 × Fin d) S}
    {ph1 ph2 : MvPowerSeries (Fin 3 × Fin d) S} {sy : MvPowerSeries (Fin 2 × Fin d) S}
    {ad : 𝓞 E → MvPowerSeries (Fin 2 × Fin d) S} (e : ∀ m, FrTy y d x m) (T : ∀ m, (Jet S (Fin 2 × Fin d) m)ˣ)
    (hF : IsFrame y d x F act ph1 ph2 sy ad e)
    (hm1 : ∀ m, sub d m ![fun j => psIn d m ![0, 1] (F j), fun j => X ((2 : Fin 3), j)] (T m) =
      sub d m ![fun j => X ((0 : Fin 3), j), fun j => X ((2 : Fin 3), j)] (T m) *
        sub d m ![fun j => X ((1 : Fin 3), j), fun j => X ((2 : Fin 3), j)] (T m))
    (hm2 : ∀ m, sub d m ![fun j => X ((0 : Fin 3), j), fun j => psIn d m ![1, 2] (F j)] (T m) =
      sub d m ![fun j => X ((0 : Fin 3), j), fun j => X ((1 : Fin 3), j)] (T m) *
        sub d m ![fun j => X ((0 : Fin 3), j), fun j => X ((2 : Fin 3), j)] (T m))
    (hs : ∀ m, sub d m ![fun j => X ((1 : Fin 2), j), fun j => X ((0 : Fin 2), j)] (T m) = T m)
    (hb : ∀ m a, sub d m ![fun j => psIn d m ![0] (act a j), fun j => X ((1 : Fin 2), j)] (T m) =
      sub d m ![fun j => X ((0 : Fin 2), j), fun j => psIn d m ![1] (act (H.bar a) j)] (T m)) :
    IsFrame y d x F act ph1 ph2 sy ad (tw y d x e T) := by
  refine ⟨fun m => tw_isGen y d x e T m (hF.gen m), fun m => ?_, fun m => ?_, fun m => ?_, fun a => ?_⟩
  · obtain ⟨u, hu, hc⟩ := hF.ph1 m
    refine ⟨u, hu, ?_⟩
    rw [pe_tw, pe_tw, pe_tw, FBIdLB.invGen_scaleGenG, FBIdLB.invGen_scaleGenG, FBIdLB.mulGen_scaleGenG,
      FBIdLB.mulGen_scaleGenG, hm1 m, FBIdSy.unitΓ_mul, ← _root_.mul_inv, _root_.mul_inv_cancel, FBIdLB.scaleGenG_one]
    exact hc
  · obtain ⟨u, hu, hc⟩ := hF.ph2 m
    refine ⟨u, hu, ?_⟩
    rw [pe_tw, pe_tw, pe_tw, FBIdLB.invGen_scaleGenG, FBIdLB.invGen_scaleGenG, FBIdLB.mulGen_scaleGenG,
      FBIdLB.mulGen_scaleGenG, hm2 m, FBIdSy.unitΓ_mul, ← _root_.mul_inv, _root_.mul_inv_cancel, FBIdLB.scaleGenG_one]
    exact hc
  · obtain ⟨u, hu, hc⟩ := hF.sy m
    refine ⟨u, hu, ?_⟩
    have key := FBIdLB.corr_scaleGenG Xo.univ.t hc (unitΓ (T m))
    have eR : scaleGen _ _ (unitΓ u⁻¹) (pe y d x (tw y d x e T) m
        ![fun j => X ((1 : Fin 2), j), fun j => X ((0 : Fin 2), j)]) =
        scaleGenG Xo.univ.t _ _ (unitΓ (T m)) (scaleGen _ _ (unitΓ u⁻¹)
          (pe y d x e m ![fun j => X ((1 : Fin 2), j), fun j => X ((0 : Fin 2), j)])) := by
      rw [pe_tw, hs m, scaleGen_eq, scaleGen_eq, FBIdSy.scaleGenG_scaleGenG, FBIdSy.scaleGenG_scaleGenG,
        _root_.mul_comm]
    rw [eR]
    exact key
  · obtain ⟨wL, hwL, h⟩ := hF.ad a
    refine ⟨wL, hwL, fun m => ?_⟩
    obtain ⟨u, hu, hc⟩ := h m
    refine ⟨u, hu, ?_⟩
    have key := FBIdLB.corr_scaleGenG Xo.univ.t hc
      (unitΓ (sub d m ![fun j => X ((0 : Fin 2), j), fun j => psIn d m ![1] (act (H.bar a) j)] (T m)))
    rw [pe_tw, pe_tw, hb m a, mulGen_scale_right, scaleGen_eq, FBIdSy.scaleGenG_scaleGenG,
      _root_.mul_comm, ← FBIdSy.scaleGenG_scaleGenG]
    exact key

theorem trunc_tw (e : ∀ m, FrTy y d x m) (T U : ∀ m, (Jet S (Fin 2 × Fin d) m)ˣ)
    (hstep : ∀ m, LB.Gen.Corr Xo.univ.t.PP.L _ _ _ _
      (LB.pullGen Xo.univ.t.PP.L _ _ (e (m + 1))
        (homAt y.x (jetTrunc : Jet S (Fin 2 × Fin d) (m + 1) →ₐ[S] Jet S (Fin 2 × Fin d) m)).left)
      (scaleGen _ _ (unitΓ (U m)) (e m)))
    (hT : ∀ m, Units.map (jetTrunc : Jet S (Fin 2 × Fin d) (m + 1) →ₐ[S] Jet S (Fin 2 × Fin d) m).toMonoidHom
      (T (m + 1)) * U m = T m) (m : ℕ) :
    LB.Gen.Corr Xo.univ.t.PP.L _ _ _ _
      (LB.pullGen Xo.univ.t.PP.L _ _ (tw y d x e T (m + 1))
        (homAt y.x (jetTrunc : Jet S (Fin 2 × Fin d) (m + 1) →ₐ[S] Jet S (Fin 2 × Fin d) m)).left)
      (tw y d x e T m) := by
  have h1 := FBIdLB.pullGen_scaleGenG Xo.univ.t
    (cφ ![jpt y d x (m + 1) (0 : Fin 2), jpt y d x (m + 1) (1 : Fin 2)]) (cε 2) (unitΓ (T (m + 1))) (e (m + 1))
    (homAt y.x (jetTrunc : Jet S (Fin 2 × Fin d) (m + 1) →ₐ[S] Jet S (Fin 2 × Fin d) m)).left
  rw [FBIdLB.unitΓ_homAt] at h1
  have key := FBIdLB.corr_scaleGenG Xo.univ.t (hstep m)
    (unitΓ (Units.map (jetTrunc : Jet S (Fin 2 × Fin d) (m + 1) →ₐ[S] Jet S (Fin 2 × Fin d) m).toMonoidHom
      (T (m + 1))))
  have hu : unitΓ (Units.map (jetTrunc : Jet S (Fin 2 × Fin d) (m + 1) →ₐ[S] Jet S (Fin 2 × Fin d) m).toMonoidHom
      (T (m + 1))) * unitΓ (U m) = unitΓ (T m) := by
    rw [← FBIdSy.unitΓ_mul, hT m]
  have h2 : scaleGenG Xo.univ.t (cφ ![jpt y d x m (0 : Fin 2), jpt y d x m (1 : Fin 2)]) (cε 2)
      (unitΓ (Units.map (jetTrunc : Jet S (Fin 2 × Fin d) (m + 1) →ₐ[S] Jet S (Fin 2 × Fin d) m).toMonoidHom
        (T (m + 1)))) (scaleGenG Xo.univ.t _ _ (unitΓ (U m)) (e m)) = tw y d x e T m :=
    (FBIdSy.scaleGenG_scaleGenG Xo.univ.t (cφ ![jpt y d x m (0 : Fin 2), jpt y d x m (1 : Fin 2)]) (cε 2) _ _
      (e m)).trans (congrArg (fun v => scaleGenG Xo.univ.t (cφ ![jpt y d x m (0 : Fin 2), jpt y d x m (1 : Fin 2)])
        (cε 2) v (e m)) hu)
  exact (congrArg₂ (LB.Gen.Corr Xo.univ.t.PP.L _ _ _ _) h1 h2.symm).mpr key

theorem corr_refl {Y : Scheme.{0}} {K : Type} [Fintype K] (φ : K → (Y ⟶ Xo.univ.t.G.left)) (ε : K → ℤ)
    (g : LB.Gen (LB.LinComb Xo.univ.t.PP.L φ ε)) : LB.Gen.Corr Xo.univ.t.PP.L φ ε φ ε g g := by
  intro j j' _ _ hx
  have : j = j' := funext fun k => hx k k rfl
  subst this
  rfl

theorem fixTw_of [StarRing (𝓞 E)] [Algebra ℚ S] (C : ChartAt Xo c y) (T U : ∀ m, (Jet S (Fin 2 × Fin C.d) m)ˣ)
    (hm1 : ∀ m, sub C.d m ![fun j => psIn C.d m ![0, 1] (C.B.G.F j), fun j => X ((2 : Fin 3), j)] (T m) =
      sub C.d m ![fun j => X ((0 : Fin 3), j), fun j => X ((2 : Fin 3), j)] (T m) *
        sub C.d m ![fun j => X ((1 : Fin 3), j), fun j => X ((2 : Fin 3), j)] (T m))
    (hm2 : ∀ m, sub C.d m ![fun j => X ((0 : Fin 3), j), fun j => psIn C.d m ![1, 2] (C.B.G.F j)] (T m) =
      sub C.d m ![fun j => X ((0 : Fin 3), j), fun j => X ((1 : Fin 3), j)] (T m) *
        sub C.d m ![fun j => X ((0 : Fin 3), j), fun j => X ((2 : Fin 3), j)] (T m))
    (hs : ∀ m, sub C.d m ![fun j => X ((1 : Fin 2), j), fun j => X ((0 : Fin 2), j)] (T m) = T m)
    (hb : ∀ m a, sub C.d m ![fun j => psIn C.d m ![0] (C.B.A.act a j), fun j => X ((1 : Fin 2), j)] (T m) =
      sub C.d m ![fun j => X ((0 : Fin 2), j), fun j => psIn C.d m ![1] (C.B.A.act (H.bar a) j)] (T m))
    (hstep : ∀ m, LB.Gen.Corr Xo.univ.t.PP.L _ _ _ _
      (LB.pullGen Xo.univ.t.PP.L _ _ (C.e (m + 1))
        (homAt y.x (jetTrunc : Jet S (Fin 2 × Fin C.d) (m + 1) →ₐ[S] Jet S (Fin 2 × Fin C.d) m)).left)
      (scaleGen _ _ (unitΓ (U m)) (C.e m)))
    (hT : ∀ m, Units.map (jetTrunc : Jet S (Fin 2 × Fin C.d) (m + 1) →ₐ[S] Jet S (Fin 2 × Fin C.d) m).toMonoidHom
      (T (m + 1)) * U m = T m) (h0 : T 0 = 1) :
    ∃ (e' : ∀ m, FrTy y C.d C.x m) (hfr : IsFrame y C.d C.x C.B.G.F C.B.A.act C.B.ph1 C.B.ph2 C.B.sy C.B.ad e')
      (hrig : LB.Gen.Corr Xo.univ.t.PP.L _ _ _ _
        (LB.pullGen Xo.univ.t.PP.L _ _ (eL y C.d C.x C.B.A.act e' C.wP 0)
          (homAt y.x (jetAug : Jet S (Fin 1 × Fin C.d) 0 →ₐ[S] S)).left)
        (rigT Xo.univ.t.G Xo.univ.t.PP.L Xo.univ.t.PP.rig (overAt y.x S) 1)),
      FrTruncC y { C with e := e', frame := hfr, rig0 := hrig } ∧
      ∀ m, LB.Gen.Corr Xo.univ.t.PP.L _ _ _ _ (e' m) (scaleGen (Xo := Xo) _ _ (unitΓ (T m)) (C.e m)) := by
  have hfr := isFrame_tw y C.d C.x C.e T C.frame hm1 hm2 hs hb
  have h0' := tw_zero y C.d C.x C.e T h0
  have hrig : LB.Gen.Corr Xo.univ.t.PP.L _ _ _ _
      (LB.pullGen Xo.univ.t.PP.L _ _ (eL y C.d C.x C.B.A.act (tw y C.d C.x C.e T) C.wP 0)
        (homAt y.x (jetAug : Jet S (Fin 1 × Fin C.d) 0 →ₐ[S] S)).left)
      (rigT Xo.univ.t.G Xo.univ.t.PP.L Xo.univ.t.PP.rig (overAt y.x S) 1) := by
    simp only [eL, pe]
    rw [h0']
    exact C.rig0
  refine ⟨tw y C.d C.x C.e T, hfr, hrig, fun m => trunc_tw y C.d C.x C.e T U hstep hT m, fun m => ?_⟩
  exact corr_refl _ _ _

end Formalism.MainNotions.ModuliIntegralCharts.H1.CIndFrFix2
end
end

-- bundled from Formalism.SharpRestriction.Divisibility.GeneratorPowers.ThetaSwapFirstTwo
section
set_option autoImplicit false

noncomputable section

namespace Formalism.MainNotions.ModuliIntegralCharts.H1.FBIdPh

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj MvPolynomial
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj NumberField
open Formalism.MainNotions.ModuliIntegralCharts.H1.GermD Formalism.MainNotions.ModuliIntegralCharts.H1.GermFun

attribute [local instance] Over.cartesianMonoidalCategory

section Jet

variable {S : Type} [CommRing S]

theorem cc_aeval {κ κ' : Type} (ψ : κ' → MvPolynomial κ S) (hψ : ∀ i, constantCoeff (ψ i) = 0)
    (P : MvPolynomial κ' S) : constantCoeff (aeval ψ P) = constantCoeff P := by
  have key : (constantCoeff : MvPolynomial κ S →+* S).comp (aeval ψ).toRingHom = constantCoeff :=
    MvPolynomial.ringHom_ext (fun r => by simp) (fun i => by simp [hψ])
  exact DFunLike.congr_fun key P

theorem mem_orig_of_cc {κ : Type} (P : MvPolynomial κ S) (h : constantCoeff P = 0) : P ∈ orig S κ := by
  have hr : (Set.range (X : κ → MvPolynomial κ S)) = X '' Set.univ := Set.image_univ.symm
  show P ∈ Ideal.span (Set.range X)
  rw [hr, MvPolynomial.mem_ideal_span_X_image]
  intro m hm
  rw [MvPolynomial.mem_support_iff] at hm
  have hm0 : m ≠ 0 := by
    rintro rfl
    exact hm h
  obtain ⟨i, hi⟩ : ∃ i, m i ≠ 0 := by
    by_contra hcon
    push_neg at hcon
    exact hm0 (Finsupp.ext fun a => by simp [hcon a])
  exact ⟨i, Set.mem_univ _, hi⟩

private theorem jetMap_mk_lemma {κ κ' : Type} (m : ℕ) (f : κ → MvPolynomial κ' S) (hf : ∀ i, f i ∈ orig S κ')
    (P : MvPolynomial κ S) :
    jetMap (m := m) f hf (Ideal.Quotient.mk (orig S κ ^ (m + 1)) P) =
      Ideal.Quotient.mk (orig S κ' ^ (m + 1)) (aeval f P) := by
  rfl

private theorem jetSubstP_mk_eq_mk_aeval_sub_C {κ κ' : Type} (m : ℕ) (φ : κ → MvPolynomial κ' S) (P : MvPolynomial κ S) :
    jetSubstP m φ (Ideal.Quotient.mk (orig S κ ^ (m + 1)) P) =
      Ideal.Quotient.mk (orig S κ' ^ (m + 1)) (aeval (fun i => φ i - C (constantCoeff (φ i))) P) := by
  rfl

theorem jetSubstP_comp {κ κ' κ'' : Type} (m : ℕ) (φ : κ → MvPolynomial κ' S) (ψ : κ' → MvPolynomial κ'' S)
    (hφ : ∀ i, constantCoeff (φ i) = 0) (hψ : ∀ i, constantCoeff (ψ i) = 0) :
    (jetSubstP m ψ).comp (jetSubstP m φ) = jetSubstP m (fun i => aeval ψ (φ i)) := by
  refine DFunLike.ext _ _ fun x => ?_
  obtain ⟨P, rfl⟩ := Ideal.Quotient.mk_surjective (I := orig S κ ^ (m + 1)) x
  show jetSubstP m ψ (jetSubstP m φ (Ideal.Quotient.mk _ P)) =
    jetSubstP m (fun i => aeval ψ (φ i)) (Ideal.Quotient.mk _ P)
  simp only [jetSubstP_mk_eq_mk_aeval_sub_C, hφ, hψ, cc_aeval ψ hψ, map_zero, sub_zero]
  exact congrArg _ (DFunLike.congr_fun (MvPolynomial.algHom_ext (f := (aeval ψ).comp (aeval φ))
    (g := aeval fun i => aeval ψ (φ i)) fun i => by simp) P)

end Jet

section Pts

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {X0 : Scheme.{0}} (t : SAB H X0)
variable {S : Type} [CommRing S] (x0 : Sp S ⟶ X0) (d : ℕ) (x : ∀ m, jOG x0 d m 1 ⟶ t.G)

abbrev rel {n n' : ℕ} (σ : Fin n → Fin n') : Fin n × Fin d → MvPolynomial (Fin n' × Fin d) S :=
  fun p => X (σ p.1, p.2)

private theorem subst_jpt_lemma_3 {n n' : ℕ} (m : ℕ) (ψ : Fin n × Fin d → MvPolynomial (Fin n' × Fin d) S)
    (i : Fin n) (k : Fin n') (h : ∀ j, ψ (i, j) = X (k, j)) :
    homAt x0 (jetSubstP m ψ) ≫ jptG t x0 d x m i = jptG t x0 d x m k := by
  have key : (jetSubstP m ψ).comp (jetCopy d m i) = jetCopy d m k := by
    refine DFunLike.ext _ _ fun y => ?_
    obtain ⟨P, rfl⟩ := Ideal.Quotient.mk_surjective (I := orig S (Fin 1 × Fin d) ^ (m + 1)) y
    show jetSubstP m ψ (jetCopy d m i (Ideal.Quotient.mk _ P)) = jetCopy d m k (Ideal.Quotient.mk _ P)
    simp only [jetCopy, jetMap_mk_lemma, jetSubstP_mk_eq_mk_aeval_sub_C]
    exact congrArg _ (DFunLike.congr_fun (MvPolynomial.algHom_ext
      (f := (aeval fun p => ψ p - C (constantCoeff (ψ p))).comp
        (aeval fun p : Fin 1 × Fin d => (X (i, p.2) : MvPolynomial (Fin n × Fin d) S)))
      (g := aeval fun p : Fin 1 × Fin d => (X (k, p.2) : MvPolynomial (Fin n' × Fin d) S))
      fun p => by simp [h]) P)
  unfold jptG
  rw [← Category.assoc, homAt_comp, key]

theorem relabel_jpt {n n' : ℕ} (m : ℕ) (σ : Fin n → Fin n') (i : Fin n) :
    homAt x0 (jetSubstP m (rel d (S := S) σ)) ≫ jptG t x0 d x m i = jptG t x0 d x m (σ i) := by
  exact subst_jpt_lemma_3 t x0 d x m (rel d σ) i (σ i) fun j => rfl

end Pts

section Gen

end Gen

section Ser

variable {S : Type} [CommRing S] (d : ℕ)

open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ (PS Pt ev pt)

theorem psJet_ev_rel {n n' : ℕ} (m : ℕ) (σ : Fin n → Fin n') (f : PS S n d) :
    psJet m (ev (fun i => pt S d (σ i)) f) = jetSubstP m (rel d (S := S) σ) (psJet m f) := by
  have hc : ∀ p : Fin n × Fin d, MvPowerSeries.constantCoeff
      ((fun p : Fin n × Fin d => (fun i => pt S d (σ i) : Fin n → Pt S n' d) p.1 p.2) p) = 0 := by
    rintro ⟨k, j⟩
    simp [pt]
  rw [ev, FBIdJet.psJet_subst m _ hc f]
  apply DFunLike.congr_fun
  refine jet_hom_ext fun p => ?_
  obtain ⟨k, j⟩ := p
  rw [jetMap_mk, aeval_X]
  simp only [pt, jetSubstP, jetMap_mk, aeval_X, rel, constantCoeff_X, map_zero, sub_zero]
  exact FBIdSy.mk_psTrunc_X m _

theorem mk_rename {κ κ' : Type} (m : ℕ) (ρ : κ → κ') (P : MvPolynomial κ S) :
    (Ideal.Quotient.mk (orig S κ' ^ (m + 1)) (rename ρ P)) =
      jetMap (m := m) (fun i => (X (ρ i) : MvPolynomial κ' S)) (fun _ => X_mem_orig _)
        (Ideal.Quotient.mk _ P) := by
  have hr : rename ρ P = aeval (fun i => (X (ρ i) : MvPolynomial κ' S)) P :=
    DFunLike.congr_fun (MvPolynomial.algHom_ext (f := rename ρ) (g := aeval fun i => (X (ρ i) : MvPolynomial κ' S))
      fun i => by simp) P
  rw [hr, jetMap_mk_lemma]

theorem cc_psTrunc {κ : Type} [Fintype κ] [DecidableEq κ] (m : ℕ) (f : MvPowerSeries κ S) :
    constantCoeff (psTrunc m f) = MvPowerSeries.constantCoeff f := by
  unfold psTrunc
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sum]
  simp only [MvPolynomial.constantCoeff_monomial]
  rw [Finset.sum_ite_eq']
  rw [if_pos]
  · first
      | exact MvPowerSeries.coeff_zero_eq_constantCoeff_apply f
      | simp
      | rfl
  · simp [degLE]
    exact ⟨fun _ => 0, by ext; simp⟩

theorem cc_psIn {n n' : ℕ} (m : ℕ) (r : Fin n → Fin n') (f : PS S n d) :
    constantCoeff (psIn d m r f) = MvPowerSeries.constantCoeff f := by
  unfold psIn
  first
    | (rw [MvPolynomial.constantCoeff_rename]; exact cc_psTrunc m f)
    | simp [cc_psTrunc]
    | (rw [show (rename fun p : Fin n × Fin d => (r p.1, p.2)) (psTrunc m f) =
          aeval (fun p : Fin n × Fin d => (X (r p.1, p.2) : MvPolynomial (Fin n' × Fin d) S)) (psTrunc m f) from
          DFunLike.congr_fun (MvPolynomial.algHom_ext fun i => by simp) _]
       rw [cc_aeval _ (fun p => by simp)]
       exact cc_psTrunc m f)

end Ser

section Comm

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {X0 : Scheme.{0}} (t : SAB H X0)
variable {S : Type} [CommRing S] (x0 : Sp S ⟶ X0) (d : ℕ) (x : ∀ m, jOG x0 d m 1 ⟶ t.G)

open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ (PS Pt ev pt)

end Comm

section AxTools

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {X0 : Scheme.{0}} (t : SAB H X0)
variable {S : Type} [CommRing S] (x0 : Sp S ⟶ X0) (d : ℕ) (x : ∀ m, jOG x0 d m 1 ⟶ t.G)

theorem subst_jpt {n n' : ℕ} (m : ℕ) (ψ : Fin n × Fin d → MvPolynomial (Fin n' × Fin d) S) (i : Fin n) (k : Fin n')
    (h : ∀ j, ψ (i, j) = X (k, j)) :
    homAt x0 (jetSubstP m ψ) ≫ jptG t x0 d x m i = jptG t x0 d x m k := by
  exact subst_jpt_lemma_3 t x0 d x m ψ i k h

end AxTools

end Formalism.MainNotions.ModuliIntegralCharts.H1.FBIdPh
end
end

