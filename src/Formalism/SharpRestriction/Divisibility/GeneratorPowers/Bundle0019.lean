module

public import Formalism.SharpRestriction.Divisibility.GeneratorPowers.FormalGroupLinearSecond
public import Formalism.SharpRestriction.Divisibility.GeneratorPowers.Bundle0018
public import Formalism.SharpRestriction.Divisibility.GeneratorPowers.Bundle0017
public import Formalism.SharpRestriction.Divisibility.GeneratorPowers.Bundle0003
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.TaylorDiscriminants.WickVanishing.Bundle0011
public import Formalism.SharpRestriction.Divisibility.GeneratorPowers.Bundle0008
public import Formalism.SharpRestriction.Divisibility.GeneratorPowers.Bundle0006
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0007

@[expose] public section

-- bundled from Formalism.SharpRestriction.Divisibility.GeneratorPowers.BalOf
section
set_option autoImplicit false

noncomputable section

namespace Formalism.MainNotions.ModuliIntegralCharts.H1.CIndFrExp2b

open MvPolynomial Formalism.MainNotions.ModuliIntegralCharts.H1.PairEvaluation Formalism.MainNotions.ModuliIntegralCharts.H1.CIndFrExp2

variable {S : Type} [CommRing S] [Algebra ℚ S] {d : ℕ}

theorem bal_of {P : MvPolynomial (Fin 2 × Fin d) S} {m : ℕ} (hm : 2 ≤ m) (B A Ab : Fin d → Fin d → S)
    (h2 : P - 1 ∈ Io S (Fin 2 × Fin d) ^ 2) (h3 : P - 1 - bil B ∈ Io S (Fin 2 × Fin d) ^ 3)
    (aW0 aB1 : Fin d → MvPolynomial (Fin 2 × Fin d) S)
    (hW0 : ∀ i, aW0 i - lin A (0 : Fin 2) i ∈ Io S (Fin 2 × Fin d) ^ 2)
    (hB1 : ∀ i, aB1 i - lin Ab (1 : Fin 2) i ∈ Io S (Fin 2 × Fin d) ^ 2)
    (hbal : ev2 P aW0 (xs S d 1) - ev2 P (xs S d 0) aB1 ∈ Io S (Fin 2 × Fin d) ^ (m + 1)) :
    Matrix.transpose (Matrix.of A) * Matrix.of B = Matrix.of B * Matrix.of Ab := by
  set W := P - 1 with hWdef
  set h := bil B with hhdef
  have hhI : h ∈ Io S (Fin 2 × Fin d) ^ 2 := bil_mem B
  have hh : h.IsHomogeneous 2 := bil_hom B
  have hmj : ∀ {p : MvPolynomial (Fin 2 × Fin d) S}, p ∈ Io S _ ^ (m + 1) → p ∈ Io S _ ^ (2 + 1) :=
    fun hp => Ideal.pow_le_pow_right (by omega) hp
  have hsq : ∀ {p : MvPolynomial (Fin 2 × Fin d) S}, p ∈ Io S _ ^ 2 → p ∈ Io S _ :=
    fun hp => Ideal.pow_le_self two_ne_zero hp
  have hPW : ∀ (u v : Fin d → MvPolynomial (Fin 2 × Fin d) S), ev2 P u v = 1 + ev2 W u v := by
    intro u v; rw [hWdef, eval_pair_sub, eval_pair_one]; ring
  have hTr : ∀ (u v : Fin d → MvPolynomial (Fin 2 × Fin d) S), (∀ i, u i ∈ Io S _) → (∀ i, v i ∈ Io S _) →
      ev2 W u v - ev2 h u v ∈ Io S _ ^ (2 + 1) := by
    intro u v hu hv
    rw [← eval_pair_sub]
    exact aeval_mem_pow _ (fun p => by rcases p with ⟨k, i⟩; fin_cases k <;> simp [hu, hv]) _ h3
  have hRep : ∀ (u v u' v' : Fin d → MvPolynomial (Fin 2 × Fin d) S), (∀ i, u i ∈ Io S _) →
      (∀ i, v i ∈ Io S _) → (∀ i, u' i ∈ Io S _) → (∀ i, v' i ∈ Io S _) → (∀ i, u i - u' i ∈ Io S _ ^ 2) →
      (∀ i, v i - v' i ∈ Io S _ ^ 2) → ev2 h u v - ev2 h u' v' ∈ Io S _ ^ (2 + 1) := by
    intro u v u' v' hu hv hu' hv' huu hvv
    exact aeval_sub_mem_pow _ _ (fun p => by rcases p with ⟨k, i⟩; fin_cases k <;> simp [hu, hv])
      (fun p => by rcases p with ⟨k, i⟩; fin_cases k <;> simp [hu', hv'])
      (fun p => by rcases p with ⟨k, i⟩; fin_cases k <;> simp [huu, hvv]) 2 h hhI
  have hx : ∀ (k : Fin 2) (i : Fin d), xs S d k i ∈ Io S (Fin 2 × Fin d) := fun k i => xs_mem k i
  have hl : ∀ (M : Fin d → Fin d → S) (k : Fin 2) (i : Fin d), lin M k i ∈ Io S (Fin 2 × Fin d) :=
    fun M k i => lin_mem M k i
  have haW0 : ∀ i, aW0 i ∈ Io S _ := fun i => by
    have := add_mem (hsq (hW0 i)) (hl A 0 i); simpa using this
  have haB1 : ∀ i, aB1 i ∈ Io S _ := fun i => by
    have := add_mem (hsq (hB1 i)) (hl Ab 1 i); simpa using this
  have hb1 : ev2 h (lin A (0 : Fin 2)) (xs S d (1 : Fin 2)) = ev2 h (xs S d (0 : Fin 2)) (lin Ab (1 : Fin 2)) := by
    have k : ev2 h (lin A (0 : Fin 2)) (xs S d (1 : Fin 2)) - ev2 h (xs S d (0 : Fin 2)) (lin Ab (1 : Fin 2)) ∈
        Io S _ ^ (2 + 1) := by
      have e : ev2 h (lin A (0 : Fin 2)) (xs S d (1 : Fin 2)) - ev2 h (xs S d (0 : Fin 2)) (lin Ab (1 : Fin 2)) =
          (ev2 P aW0 (xs S d 1) - ev2 P (xs S d 0) aB1) -
          (ev2 W aW0 (xs S d 1) - ev2 h aW0 (xs S d 1)) + (ev2 W (xs S d 0) aB1 - ev2 h (xs S d 0) aB1) -
          (ev2 h aW0 (xs S d 1) - ev2 h (lin A (0 : Fin 2)) (xs S d (1 : Fin 2))) +
          (ev2 h (xs S d 0) aB1 - ev2 h (xs S d (0 : Fin 2)) (lin Ab (1 : Fin 2))) := by
        rw [hPW, hPW]; ring
      rw [e]
      exact add_mem (sub_mem (add_mem (sub_mem (hmj hbal) (hTr _ _ haW0 (hx 1))) (hTr _ _ (hx 0) haB1))
        (hRep _ _ _ _ haW0 (hx 1) (hl A 0) (hx 1) hW0 (fun i => by simp)))
        (hRep _ _ _ _ (hx 0) haB1 (hx 0) (hl Ab 1) (fun i => by simp) hB1)
    exact sub_eq_zero.1 (eq_zero_of_isHomogeneous
      ((eval_pair_homogeneous hh _ _ (lin_hom A 0) (xs_hom 1)).sub (eval_pair_homogeneous hh _ _ (xs_hom 0) (lin_hom Ab 1))) k)
  ext i0 l0
  have hc := congrArg (AddMonoidAlgebra.coeff · (sil i0 l0)) hb1
  rw [hhdef, eval_pair_bilinear, eval_pair_bilinear, coeff_linL, coeff_linR] at hc
  simp only [Matrix.mul_apply, Matrix.transpose_apply, Matrix.of_apply]
  exact hc

end Formalism.MainNotions.ModuliIntegralCharts.H1.CIndFrExp2b
end
end

-- bundled from Formalism.SharpRestriction.Divisibility.GeneratorPowers.BoxTuple
section
set_option autoImplicit false

noncomputable section

namespace Formalism.MainNotions.ModuliIntegralCharts.H1

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.DVR ReciprocityTheory.ChartRestriction.G.DVR.QForm Formalism.MainNotions.ModuliIntegralCharts.H1.ExpBijectiveUniformisation Formalism.MainNotions.ModuliIntegralCharts.H1.GSt
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ (PS)
open IsLocalRing

attribute [local instance] Over.cartesianMonoidalCategory

namespace BoxTuple

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
  {Xo : Moduli Dw l} {c : Coeff l} [StarRing (𝓞 E)] {T : CDVR} {io : c.F →+* T.Fr} {y : IntFr Xo c T io}

def BoxTup (C : IntegralChartA3 Xo c T io y) (P : PELUnif (maximalIdeal T.V) C.I.G) (Q : P.D.toPre.X → ℤ)
    (F : Type) [Field F] [Algebra T.Fr F] [Algebra T.V F] (v : AddValuation F (WithTop ℚ)) (g g' : ℕ) (π : 𝓞 E)
    {n : ℕ} {D' : DegData T.V (maximalIdeal T.V)} {A' : PolAV (Spec (CommRingCat.of T.Fr))} {G' : Over (Sp T.V)}
    [GrpObj G'] [IsCommMonObj G'] {pD : IsPowDeg D'.toPre P.D.toPre n} {pA : IsPowPolAV A' P.A n}
    (pG : IsPowGrp G' C.I.G.G n) {U' : Unif (maximalIdeal T.V) D' A' G'} (PU : UnifPowOf3 pD pA pG U' P.U)
    [Module (𝓞 E) D'.toPre.X] (oD' : D'.toPre.OAct (𝓞 E))
    (s : Fam D'.toPre F g') (s₂ : Fam D'.toPre F (g' * g)) (p : QkPt D'.toPre F (g' * g))
    (w : LB.Gen (LB.LinComb D'.toPre.P.L (DegPre.lineφ D'.toPre F p.g.b) (DegPre.lineε (g' * g))))
    (ζ : F) (x : TFK (R := T.V) F ⟶ A'.A) (t₀ t : Fam D'.toPre F (g' * g))
    (σ' : U'.toUnifPre.SecGF F (g' * g)) (h : PS F n (chD C.ch)) : Prop :=
  NuGe D' (sumQ pD.xe Q) F v g' s 0 ∧
  PullAl D' F oD' (star π) g' g s s₂ ∧
  (w.IsGen ∧ ζ ≠ 0 ∧ FinOrd D' F (g' * g) p w ζ) ∧
  QkToAkU U'.toUnifPre F (g' * g) p x ∧ (∀ i, x ≫ pA.pr i ≫ P.oA.act π = 1) ∧
  PhiRel D'.toPre F (g' * g) p w s₂ t₀ ∧ Fam.IsSmul D'.toPre F ζ t₀ t ∧
  U'.toUnifPre.ExpandsG F (g' * g) σ' t ∧
  IsGermN P C.xT C.actT C.eT C.wPT pG PU.toUnifPowOf F (g' * g) σ' h

end BoxTuple

open BoxTuple

end Formalism.MainNotions.ModuliIntegralCharts.H1
end
end

-- bundled from Formalism.SharpRestriction.Divisibility.GeneratorPowers.ChartJetTrD
section
set_option autoImplicit false

noncomputable section

namespace Formalism.MainNotions.ModuliIntegralCharts.H1.JetTr

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj

attribute [local instance] Over.cartesianMonoidalCategory

theorem push_inj {S S' : Scheme.{0}} {G : Over S} {G' : Over S'} [GrpObj G] [GrpObj G'] {f : S' ⟶ S}
    {φ : G'.left ⟶ G.left} (h : IsGrpPullback G' G f φ) {T : Over S'} {a b : T ⟶ G'}
    (e : pushHom h T a = pushHom h T b) : a = b := by
  have e1 : a.left ≫ φ = b.left ≫ φ := congrArg (fun z => z.left) e
  have e2 : a.left ≫ G'.hom = b.left ≫ G'.hom := by
    rw [Over.w a, Over.w b]
  exact Over.OverMorphism.ext (h.1.hom_ext e1 e2)

theorem jetCoef_copy {V K : Type} [CommRing V] [CommRing K] (f : V →+* K) (d m n : ℕ) (i : Fin n) :
    (jetCoef f (Fin n × Fin d) m).comp ((jetCopy (S := V) d m i : Jet V (Fin 1 × Fin d) m →ₐ[V] Jet V (Fin n × Fin d) m) :
      Jet V (Fin 1 × Fin d) m →+* Jet V (Fin n × Fin d) m) =
    ((jetCopy (S := K) d m i : Jet K (Fin 1 × Fin d) m →ₐ[K] Jet K (Fin n × Fin d) m) :
      Jet K (Fin 1 × Fin d) m →+* Jet K (Fin n × Fin d) m).comp (jetCoef f (Fin 1 × Fin d) m) := by
  apply Ideal.Quotient.ringHom_ext
  apply MvPolynomial.ringHom_ext
  · intro r
    show Ideal.Quotient.mk (orig K (Fin n × Fin d) ^ (m + 1))
        (MvPolynomial.map f (MvPolynomial.bind₁ (fun p : Fin 1 × Fin d => MvPolynomial.X (i, p.2))
          (MvPolynomial.C r))) =
      Ideal.Quotient.mk (orig K (Fin n × Fin d) ^ (m + 1))
        (MvPolynomial.bind₁ (fun p : Fin 1 × Fin d => MvPolynomial.X (i, p.2))
          (MvPolynomial.map f (MvPolynomial.C r)))
    simp
  · intro q
    show Ideal.Quotient.mk (orig K (Fin n × Fin d) ^ (m + 1))
        (MvPolynomial.map f (MvPolynomial.bind₁ (fun p : Fin 1 × Fin d => MvPolynomial.X (i, p.2))
          (MvPolynomial.X q))) =
      Ideal.Quotient.mk (orig K (Fin n × Fin d) ^ (m + 1))
        (MvPolynomial.bind₁ (fun p : Fin 1 × Fin d => MvPolynomial.X (i, p.2))
          (MvPolynomial.map f (MvPolynomial.X q)))
    simp

section Pt

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
variable {Xo : Moduli Dw l} {c : Coeff l} {T : CDVR} {io : c.F →+* T.Fr} {y : IntFr Xo c T io}
variable (I : IntData Xo c T io y.1) {d : ℕ} (xT : ∀ m, jOG (𝟙 (Sp T.V)) d m 1 ⟶ I.G.G)

def U2 (m : ℕ) : Over.mk ((jOG (𝟙 (Sp T.Fr)) d m 2).hom ≫ spMap (algebraMap T.V T.Fr)) ⟶ jOG (𝟙 (Sp T.V)) d m 2 :=
  Over.homMk (spMap (jc (d := d) 2 m)) (by
    show spMap (jc (d := d) 2 m) ≫ spMap (algebraMap T.V (Jet T.V (Fin 2 × Fin d) m)) ≫ 𝟙 _ =
      (spMap (algebraMap T.Fr (Jet T.Fr (Fin 2 × Fin d) m)) ≫ 𝟙 _) ≫ spMap (algebraMap T.V T.Fr)
    rw [Category.comp_id, Category.comp_id, spMap_comp', spMap_comp', jetCoef_alg])

theorem push_jpt (m : ℕ) (i : Fin 2) :
    pushHom I.m2.cart _ (jptG I.t' (𝟙 (Sp T.Fr)) d (xP I xT) m i) = U2 (d := d) m ≫ jptG I.G (𝟙 (Sp T.V)) d xT m i := by
  apply Over.OverMorphism.ext
  show (spMap _ ≫ xL I xT m) ≫ I.m2.φ = spMap (jc (d := d) 2 m) ≫ spMap _ ≫ (xT m).left
  rw [Category.assoc, xL_fst, ← Category.assoc, ← Category.assoc, spMap_comp', spMap_comp', jetCoef_copy]

theorem xP_law (FT : Fin d → MvPowerSeries (Fin 2 × Fin d) T.V) (m : ℕ)
    (hl : Formalism.L2.Pj.homAt (𝟙 (Sp T.V)) (jetSubstP m fun p : Fin 1 × Fin d => psTrunc m (FT p.2)) ≫ xT m =
      jptG I.G (𝟙 (Sp T.V)) d xT m (0 : Fin 2) * jptG I.G (𝟙 (Sp T.V)) d xT m (1 : Fin 2)) :
    Formalism.L2.Pj.homAt (𝟙 (Sp T.Fr)) (jetSubstP m fun p : Fin 1 × Fin d =>
              MvPolynomial.map (algebraMap T.V T.Fr) (psTrunc m (FT p.2))) ≫ xP I xT m =
      jptG I.t' (𝟙 (Sp T.Fr)) d (xP I xT) m (0 : Fin 2) * jptG I.t' (𝟙 (Sp T.Fr)) d (xP I xT) m (1 : Fin 2) := by
  apply push_inj I.m2.cart
  rw [map_mul, push_jpt, push_jpt, ← MonObj.comp_mul, ← hl]
  apply Over.OverMorphism.ext
  show (spMap _ ≫ xL I xT m) ≫ I.m2.φ = spMap (jc (d := d) 2 m) ≫ spMap _ ≫ (xT m).left
  rw [Category.assoc, xL_fst, ← Category.assoc, ← Category.assoc, spMap_comp', spMap_comp', jetCoef_substP]

end Pt

end Formalism.MainNotions.ModuliIntegralCharts.H1.JetTr
end
end

-- bundled from Formalism.SharpRestriction.Divisibility.GeneratorPowers.GPowSt
section
set_option autoImplicit false

noncomputable section

namespace Formalism.MainNotions.ModuliIntegralCharts.H1

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open IsLocalRing

attribute [local instance] Over.cartesianMonoidalCategory

def PowOActSt : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (V : Type) [CommRing V] [IsDomain V]
    [IsDiscreteValuationRing V] (t : SAB H (Sp V)) (P : PELUnif (maximalIdeal V) t)
    (n : ℕ) (D' : DegData V (maximalIdeal V)) (pD : IsPowDeg D'.toPre P.D.toPre n),
    letI := H.starRing
    ∃ M : Module (𝓞 E) D'.toPre.X,
      letI := M
      ∃ oD' : D'.toPre.OAct (𝓞 E),
        (∀ (a : 𝓞 E) (x : D'.toPre.X) (i : Fin n), pD.xe (a • x) i = a • pD.xe x i) ∧
        ∀ (a : 𝓞 E) (i : Fin n), oD'.onB.act a ≫ pD.pw.pr i = pD.pw.pr i ≫ P.oD.onB.act a

end Formalism.MainNotions.ModuliIntegralCharts.H1
end
end

-- bundled from Formalism.SharpRestriction.Divisibility.GeneratorPowers.GaugeUniqPf
section
set_option autoImplicit false

noncomputable section

namespace Formalism.MainNotions.ModuliIntegralCharts.H1

open AlgebraicGeometry CategoryTheory MonoidalCategory CartesianMonoidalCategory NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.TB

attribute [local instance] Over.cartesianMonoidalCategory

namespace GaugeR

def ExpPowSt : Prop :=
  ∀ (S σ : Type) [CommRing S] [Algebra ℚ S] (q : MvPowerSeries σ S), MvPowerSeries.constantCoeff q = 0 →
    ∀ k : ℕ, PowerSeries.subst q (PowerSeries.exp S) ^ k * PowerSeries.subst (-((k : S) • q)) (PowerSeries.exp S) = 1

theorem gaugeUniq_of' (hB : BetaUniqSt) (hR : GaugeRatioSt) (hP : ExpPowSt) : GaugeUniqSt := by
  intro E _ _ _ H Dw l Xo c S _ _ _ y x hx e e' he he'
  have hL := Xo.univ.t.PP.isLB
  choose u hu using fun m => ratio_of_gen Xo.univ.t.PP.L hL (fun _ : Fin 1 => (x m).left) (fun _ => (1 : ℤ))
    (e m) (e' m) (he.gen m) (he'.gen m)
  let g : ∀ m, Jet S (Fin 1 × Fin (dL Dw)) m := fun m => gam (Jet S (Fin 1 × Fin (dL Dw)) m) (u m).val
  have hpull : ∀ (m : ℕ) (B : Type) [CommRing B] [Algebra S B] (f : Jet S (Fin 1 × Fin (dL Dw)) m →ₐ[S] B),
      gam B (pullUnit (homAt y.x f).left (u m)).val = f (g m) := fun m B _ _ f =>
    gam_pullUnit (f : Jet S (Fin 1 × Fin (dL Dw)) m →+* B) (u m)
  have htr : ∀ m, jetTrunc (g (m + 1)) = g m := by
    intro m
    have h1 := scaled_pull Xo.univ.t.PP.L _ _
      (homAt y.x (jetTrunc : Jet S (Fin 1 × Fin (dL Dw)) (m + 1) →ₐ[S] _)).left (hu (m + 1))
    have hU := corr_scaled Xo.univ.t.PP.L hL _ _ _ _ _ _ _ _ _ _ h1 (hu m) (he.trunc m) (he'.trunc m)
    have h2 := congrArg (fun v => gam (Jet S (Fin 1 × Fin (dL Dw)) m) (Units.val v)) hU
    exact (hpull (m + 1) _ jetTrunc).symm.trans h2
  obtain ⟨r, hr⟩ := exists_ps_of_compat g htr
  have hrig : MvPowerSeries.constantCoeff r = 1 := by
    have h1 := scaled_pull Xo.univ.t.PP.L _ _
      (homAt y.x (jetAug : Jet S (Fin 1 × Fin (dL Dw)) 0 →ₐ[S] S)).left (hu 0)
    have hU := corr_scaled Xo.univ.t.PP.L hL _ _ _ _ _ _ _ _ _ _ h1 (scaled_one _) he.rig he'.rig
    have h2 := congrArg (fun v => gam S (Units.val v)) hU
    simp only [Units.val_one, map_one] at h2
    rw [← jetAug_psJet 0 r, hr 0]
    exact (hpull 0 S jetAug).symm.trans h2
  have hid : ∀ a : 𝓞 E, MvPowerSeries.rescale (sc (Dw := Dw) c S (1 + a * H.bar a)) r =
      MvPowerSeries.rescale (sc (Dw := Dw) c S a) r ^ 2 * r *
        MvPowerSeries.rescale (sc (Dw := Dw) c S (a * H.bar a)) r := by
    intro a
    obtain ⟨β, hβg, hβr, hβc⟩ := he.coc a
    obtain ⟨β', hβ'g, hβ'r, hβ'c⟩ := he'.coc a
    obtain rfl := hB E H Dw l Xo a β β' hβg hβ'g hβr hβ'r
    refine GermFun.psJet_inj fun m => ?_
    have s1 := scaled_pull Xo.univ.t.PP.L _ _
      (homAt y.x (jetSubstP m (actP (Dw := Dw) (S := S) c (1 + a * H.bar a)))).left (hu m)
    have sa := scaled_pull Xo.univ.t.PP.L _ _
      (homAt y.x (jetSubstP m (actP (Dw := Dw) (S := S) c a))).left (hu m)
    have sb := scaled_pull Xo.univ.t.PP.L _ _
      (homAt y.x (jetSubstP m (actP (Dw := Dw) (S := S) c (a * H.bar a)))).left (hu m)
    have srhs := scaled_mul Xo.univ.t.PP.L _ _ _ _ (scaled_one (LB.pullGen Xo.univ.t.PP.L _ _ β (x m).left))
      (scaled_mul Xo.univ.t.PP.L _ _ _ _ (scaled_genPow _ _ sa 2) (scaled_mul Xo.univ.t.PP.L _ _ _ _ (hu m) sb))
    have hU := corr_scaled Xo.univ.t.PP.L hL _ _ _ _ _ _ _ _ _ _ s1 srhs (hβc m) (hβ'c m)
    have hv := congrArg (fun v => gam (Jet S (Fin 1 × Fin (dL Dw)) m) (Units.val v)) hU
    simp only [Units.val_mul, Units.val_pow_eq_pow_val, map_mul, map_pow, one_mul] at hv
    rw [hpull, hpull, hpull] at hv
    have hv' : jetSubstP m (fun i => MvPolynomial.C (sc (Dw := Dw) c S (1 + a * H.bar a) i) * MvPolynomial.X i) (g m) =
        jetSubstP m (fun i => MvPolynomial.C (sc (Dw := Dw) c S a i) * MvPolynomial.X i) (g m) ^ 2 *
          (g m * jetSubstP m (fun i => MvPolynomial.C (sc (Dw := Dw) c S (a * H.bar a) i) * MvPolynomial.X i) (g m)) :=
      hv
    rw [psJet_mul, psJet_mul, psJet_pow, ← jetSubstP_scale, ← jetSubstP_scale, ← jetSubstP_scale, hr m, hv']
    ring
  obtain ⟨q, hq0, hdeg, hpair, hexp⟩ := ratio_exp hR c S r hrig hid
  refine ⟨q, hq0, hdeg, hpair, fun k F f f' hf hf' => ?_⟩
  refine GermFun.psJet_inj fun m => ?_
  obtain ⟨F₁, τ₁, hP₁, hC₁, hV₁⟩ := hf m
  obtain ⟨F₂, τ₂, hP₂, hC₂, hV₂⟩ := hf' m
  have hF := GermFun.pull_unique _ _ _ _ _ _ _ _ hP₁ hP₂
  subst hF
  have sg := scaled_genPow (fun _ : Fin 1 => (x m).left) (fun _ => (1 : ℤ)) (hu m) k
  have sτ := corr_scaled_left Xo.univ.t.PP.L hL (x m).left (k : ℤ) _ _ τ₁ τ₂ _ _ _ sg hC₁ hC₂
  have hval := value_scaled Xo.univ.t.G Xo.univ.t.PP.L hL (k : ℤ) _ (x m) τ₁ τ₂ _ _ _ hV₁ hV₂ sτ
  have hg := congrArg (gam (Jet S (Fin 1 × Fin (dL Dw)) m)) hval
  rw [gam_toΓ, map_mul, gam_toΓ, Units.val_pow_eq_pow_val, map_pow] at hg
  have hpow := congrArg (psJet m) (hP S _ q hq0 k)
  rw [psJet_mul, psJet_pow, ← hexp, hr m, psJet_one] at hpow
  rw [psJet_mul, hg]
  calc psJet m f' = psJet m f' * (g m ^ k * psJet m (PowerSeries.subst (-((k : S) • q)) (PowerSeries.exp S))) := by
        rw [hpow, mul_one]
    _ = _ := by ring

end GaugeR

theorem gaugeUniq_of (hB : BetaUniqSt) : GaugeUniqSt :=
  GaugeR.gaugeUniq_of' hB GRPf.gaugeRatio fun _ _ _ _ q hq k => GaugeR.exp_pow_mul_exp_neg q hq k

theorem gaugeUniq_of_global (hG : GlobalFnsSt) : GaugeUniqSt :=
  gaugeUniq_of (betaUniq_of_global hG)

end Formalism.MainNotions.ModuliIntegralCharts.H1
end
end

-- bundled from Formalism.SharpRestriction.Divisibility.GeneratorPowers.IntChartPf
section
set_option autoImplicit false

noncomputable section

namespace Formalism.MainNotions.ModuliIntegralCharts.H1

open AlgebraicGeometry CategoryTheory NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj

theorem intChart_of_cut (hA : ChartDataGSt) (hB : FrameSt) (hC : FBIdSt) (hGF : GlobalFnsSt) :
    IntChartStatement := by
  intro E _ _ _ H V _ _ _ hc t hprop κ _ tg htan hbas _ hstar
  obtain ⟨d, G, A, uvec, x, hd, hu, hch⟩ := hA E H (Sp V) t V (𝟙 (Sp V)) tg htan hbas
  obtain ⟨e, wP, ph1, ph2, sy, ad, hfr, hpr, htr, hfa, had, hrig⟩ :=
    hB E H (Sp V) t V (𝟙 (Sp V)) d G A κ tg uvec x hch
  have hPow := globalFnsDvr_of_globalFns hGF E H V hc t hprop
  obtain ⟨hax, hr⟩ := hC E H (Sp V) t hPow hstar V (𝟙 (Sp V)) d G A κ tg uvec x e ph1 ph2 sy ad hch hfr hfa had
  refine ⟨d, mkFB G A ph1 ph2 sy ad hax hr, uvec, x, e, wP, hd, hu, hch, hfr, hpr, htr, hrig, fun k F => ?_⟩
  exact germSt_holds E H (Sp V) t V (𝟙 (Sp V)) d G.F A.act κ tg uvec x ph1 ph2 sy ad e wP hch hfr hpr htr k F

end Formalism.MainNotions.ModuliIntegralCharts.H1
end
end

