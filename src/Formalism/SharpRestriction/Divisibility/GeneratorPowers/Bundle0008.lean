module

public import Formalism.SharpRestriction.Divisibility.GeneratorPowers.Bundle0006
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.TaylorDiscriminants.Bundle0003
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.TaylorDiscriminants.WickVanishing.PderivSecondEvFirstPointEqZero
public import Formalism.LocalToGlobal.ProjectiveLattices.ChartDirectionsIntegral
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0013

@[expose] public section

-- bundled from Formalism.SharpRestriction.Divisibility.GeneratorPowers.CIndBCNab
section
set_option autoImplicit false

noncomputable section

namespace Formalism.MainNotions.ModuliIntegralCharts.H1.CIndBCNab

open MvPowerSeries ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ

variable {S S' : Type} [CommRing S] [CommRing S'] (ψ : S →+* S') {d : ℕ}

theorem hasSubst_pts {m n : ℕ} {a : Fin m → Pt S n d} (ha : ∀ j i, constantCoeff (a j i) = 0) :
    HasSubst (fun p : Fin m × Fin d => a p.1 p.2) :=
  MvPowerSeries.hasSubst_of_constantCoeff_zero (fun p => ha p.1 p.2)

theorem map_ev {m n : ℕ} (a : Fin m → Pt S n d) (ha : ∀ j i, constantCoeff (a j i) = 0) (f : PS S m d) :
    map ψ (ev a f) = ev (fun j i => map ψ (a j i)) (map ψ f) := by
  simp only [ev]
  exact MvPowerSeries.map_subst (hasSubst_pts ha) f

theorem const_ev {m n : ℕ} (a : Fin m → Pt S n d) (ha : ∀ j i, constantCoeff (a j i) = 0) (f : PS S m d) :
    constantCoeff (ev a f) = constantCoeff f := by
  have hs := hasSubst_pts ha
  simp only [ev]
  rw [MvPowerSeries.constantCoeff_subst hs, finsum_eq_single _ (0 : Fin m × Fin d →₀ ℕ)]
  · simp
  · intro e he
    obtain ⟨s, hs'⟩ : ∃ s, e s ≠ 0 := by
      by_contra h
      push_neg at h
      exact he (Finsupp.ext h)
    simp only [Finsupp.prod, map_prod, map_pow, ha]
    rw [Finset.prod_eq_zero (Finsupp.mem_support_iff.mpr hs') (zero_pow hs'), smul_zero]

theorem map_pderiv {σ : Type} (i : σ) (f : MvPowerSeries σ S) :
    map ψ (pderiv i f) = pderiv i (map ψ f) := by
  ext n
  simp [MvPowerSeries.coeff_pderiv]

theorem map_nsmul' {σ : Type} (k : ℕ) (g : MvPowerSeries σ S) :
    map ψ ((k : S) • g) = (k : S') • map ψ g := by
  ext n
  simp

theorem map_eval_first_point_zero (g : PS S 2 d) :
    map ψ (ev (n := 1) ![pt S d 0, 0] g) = ev (n := 1) ![pt S' d 0, 0] (map ψ g) := by
  have h0 : ∀ j i, constantCoeff ((![pt S d 0, 0] : Fin 2 → Pt S 1 d) j i) = 0 := by
    intro j i
    fin_cases j <;> simp [pt]
  rw [map_ev ψ _ h0 g]
  congr 1
  funext j i
  fin_cases j <;> simp [pt]

theorem map_Dof (F : Fin d → PS S 2 d) (v : Fin d → S) (f : PS S 1 d) :
    map ψ (Dof F v f) = Dof (fun j => map ψ (F j)) (fun i => ψ (v i)) (map ψ f) := by
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [Dof, map_sum, map_mul, MvPowerSeries.map_C, map_eval_first_point_zero, map_pderiv]

theorem map_iter_Dof (F : Fin d → PS S 2 d) (v : Fin d → S) (k : ℕ) (f : PS S 1 d) :
    map ψ ((Dof F v)^[k] f) = (Dof (fun j => map ψ (F j)) (fun i => ψ (v i)))^[k] (map ψ f) := by
  induction k generalizing f with
  | zero => rfl
  | succ k ih => rw [Function.iterate_succ_apply, Function.iterate_succ_apply, ih, map_Dof]

theorem map_DmonOf (F : Fin d → PS S 2 d) {κ : Type} [Fintype κ] (u : κ → Fin d → S) (e : κ →₀ ℕ)
    (f : PS S 1 d) :
    map ψ (DmonOf F u e f) = DmonOf (fun j => map ψ (F j)) (fun l i => ψ (u l i)) e (map ψ f) := by
  simp only [DmonOf]
  induction (Finset.univ : Finset κ).toList with
  | nil => rfl
  | cons l L ih => simp only [List.foldr_cons, map_iter_Dof, ih]

theorem map_DpolyOf (F : Fin d → PS S 2 d) {κ : Type} [Fintype κ] (u : κ → Fin d → S)
    (P : MvPolynomial κ S) (f : PS S 1 d) :
    map ψ (DpolyOf F u P f) =
      DpolyOf (fun j => map ψ (F j)) (fun l i => ψ (u l i)) (MvPolynomial.map ψ P) (map ψ f) := by
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [DpolyOf, map_sum, map_mul, MvPowerSeries.map_C, map_DmonOf, MvPolynomial.coeff_map]
  symm
  apply Finset.sum_subset (MvPolynomial.support_map_subset ψ P)
  intro e _ he
  have h0 : ψ (P.coeff e) = 0 := by
    simpa [MvPolynomial.mem_support_iff, MvPolynomial.coeff_map] using he
  simp [h0]

variable [Algebra ℚ S] [Algebra ℚ S']

theorem map_expS {n : ℕ} (g : PS S n d) (hg : constantCoeff g = 0) :
    map ψ (FB.expS S g) = FB.expS S' (map ψ g) := by
  simp only [FB.expS]
  rw [PowerSeries.map_subst (PowerSeries.HasSubst.of_constantCoeff_zero hg), PowerSeries.map_exp]

variable {O : Type} [CommRing O] [StarRing O]

theorem hid (R : Type) [CommRing R] : algebraMap R R = RingHom.id R := rfl

theorem const_comp1_act (B : FB S d O) (a : O) (i : Fin d) :
    constantCoeff (comp1 (B.actK S a) (pt S (n := 1) d 0) i) = 0 := by
  have h1 : ∀ j l, constantCoeff ((![pt S (n := 1) d 0] : Fin 1 → Pt S 1 d) j l) = 0 := by
    intro j l
    fin_cases j
    simp [pt]
  simp only [comp1]
  rw [const_ev _ h1]
  simp [FB.actK, B.A.const]

theorem const_pair (B : FB S d O) (w0 : O) :
    ∀ j i, constantCoeff ((![pt S d 0, comp1 (B.actK S w0) (pt S d 0)] : Fin 2 → Pt S 1 d) j i) = 0 := by
  intro j i
  fin_cases j
  · simp [pt]
  · simpa using const_comp1_act B w0 i

theorem map_hL (B : FB S d O) (B' : FB S' d O) (hA : ∀ a i, B'.A.act a i = map ψ (B.A.act a i))
    (h : PS S 2 d) (w0 : O) : map ψ (B.hL S h w0) = B'.hL S' (map ψ h) w0 := by
  have h1 : ∀ j l, constantCoeff ((![pt S (n := 1) d 0] : Fin 1 → Pt S 1 d) j l) = 0 := by
    intro j l
    fin_cases j
    simp [pt]
  simp only [FB.hL]
  rw [map_ev ψ _ (const_pair B w0)]
  congr 1
  funext j i
  fin_cases j
  · simp [pt]
  · simp only [Fin.mk_one, Matrix.cons_val_one, Matrix.cons_val_fin_one, Matrix.head_cons, comp1]
    rw [map_ev ψ _ h1]
    congr 1
    · funext j l
      fin_cases j
      simp [pt]
    · simp [FB.actK, hid, hA]

theorem const_hL (B : FB S d O) (h : PS S 2 d) (hh : B.IsCanonGauge S h) (w0 : O) :
    constantCoeff (B.hL S h w0) = 0 := by
  simp only [FB.hL]
  rw [const_ev _ (const_pair B w0)]
  have h2 : ∀ j i, constantCoeff ((![0, pt S (n := 1) d 0] : Fin 2 → Pt S 1 d) j i) = 0 := by
    intro j i
    fin_cases j <;> simp [pt]
  have h3 := congrArg constantCoeff hh.ax0
  rwa [const_ev _ h2, map_zero] at h3

end Formalism.MainNotions.ModuliIntegralCharts.H1.CIndBCNab

namespace Formalism.MainNotions.ModuliIntegralCharts.H1

open MvPowerSeries ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ CIndBCNab

theorem nabMap_holds : NabMapSt := by
  intro S S' _ _ _ _ ψ d O _ _ B B' hF hA h hh w0 m f κ _ u P
  have hc : constantCoeff ((m : S) • B.hL S h w0) = 0 := by
    simp [MvPowerSeries.smul_eq_C_mul, const_hL B h hh w0]
  have hFK : (fun j => MvPowerSeries.map ψ (B.FK S j)) = B'.FK S' := by
    funext j
    simp [FB.FK, FGLaw.mapF, hF, hid]
  simp only [FB.nabVal]
  rw [← MvPowerSeries.constantCoeff_map, map_DpolyOf, map_mul, map_expS ψ _ hc, map_nsmul',
    map_hL ψ B B' hA, hFK]

end Formalism.MainNotions.ModuliIntegralCharts.H1
end
end

-- bundled from Formalism.SharpRestriction.Divisibility.GeneratorPowers.CIndFrFix
section
set_option autoImplicit false

noncomputable section

namespace Formalism.MainNotions.ModuliIntegralCharts.H1

open AlgebraicGeometry CategoryTheory Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ
  Formalism.L2.Pj

namespace CIndFrFix

open ReciprocityTheory.ChartRestriction.G.TB.LogPf (logOf)

variable {S : Type} [CommRing S] [Algebra ℚ S] {d : ℕ}

def lg (G : FGLaw S d) {n : ℕ} (j : Fin n) : Pt S n d := fun i => ev (n := n) ![pt S d j] (logOf G i)

def bilL (G : FGLaw S d) (cc : Fin d → Fin d → S) : PS S 2 d :=
  ∑ i, ∑ l, cc i l • (lg G (0 : Fin 2) i * lg G (1 : Fin 2) l)

def expP {n : ℕ} (f : PS S n d) : PS S n d := PowerSeries.subst f (PowerSeries.exp S)

def diagL {O : Type} [CommRing O] [StarRing O] (B : FB S d O) (w0 : O) (cc : Fin d → Fin d → S) : PS S 1 d :=
  ev (n := 1) ![pt S d 0, comp1 (B.A.act w0) (pt S d 0)] (bilL B.G cc)

end CIndFrFix

open CIndFrFix

def FrTruncFixSt : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H)
    (Xo : Moduli Dw l) (c : Coeff l) [StarRing (𝓞 E)], (∀ a : 𝓞 E, star a = H.bar a) →
    ∀ (S : Type) [CommRing S] [Algebra c.F S] [Algebra ℚ S] (y : FrPt Xo c S) (C : ChartAt Xo c y),
    ∃ (e' : ∀ m, FrTy y C.d C.x m) (hfr : IsFrame y C.d C.x C.B.G.F C.B.A.act C.B.ph1 C.B.ph2 C.B.sy C.B.ad e')
      (hrig : LB.Gen.Corr Xo.univ.t.PP.L _ _ _ _
        (LB.pullGen Xo.univ.t.PP.L _ _ (eL y C.d C.x C.B.A.act e' C.wP 0)
          (homAt y.x (jetAug : Jet S (Fin 1 × Fin C.d) 0 →ₐ[S] S)).left)
        (rigT Xo.univ.t.G Xo.univ.t.PP.L Xo.univ.t.PP.rig (overAt y.x S) 1))
      (cc : ℕ → Fin C.d → Fin C.d → S),
      FrTruncC y { C with e := e', frame := hfr, rig0 := hrig } ∧ cc 0 = 0 ∧ (∀ m i j, cc m i j = cc m j i) ∧
      (∀ m (a : 𝓞 E), Matrix.transpose (ReciprocityTheory.ChartRestriction.G.TB.dLin (C.B.A.act a)) * Matrix.of (cc m) =
        Matrix.of (cc m) * ReciprocityTheory.ChartRestriction.G.TB.dLin (C.B.A.act (H.bar a))) ∧
      ∀ m, ∃ u : (Jet S (Fin 2 × Fin C.d) m)ˣ,
        (u : Jet S (Fin 2 × Fin C.d) m) = psJet m (expP (-bilL C.B.G (cc m))) ∧
        LB.Gen.Corr Xo.univ.t.PP.L _ _ _ _ (e' m) (scaleGen (Xo := Xo) _ _ (unitΓ u) (C.e m))

def GermFixSt : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H)
    (Xo : Moduli Dw l) (c : Coeff l) [StarRing (𝓞 E)], (∀ a : 𝓞 E, star a = H.bar a) →
    ∀ (S : Type) [CommRing S] [Algebra c.F S] [Algebra ℚ S] (y : FrPt Xo c S) (C : ChartAt Xo c y)
      (e' : ∀ m, FrTy y C.d C.x m) (hfr : IsFrame y C.d C.x C.B.G.F C.B.A.act C.B.ph1 C.B.ph2 C.B.sy C.B.ad e')
      (hrig : LB.Gen.Corr Xo.univ.t.PP.L _ _ _ _
        (LB.pullGen Xo.univ.t.PP.L _ _ (eL y C.d C.x C.B.A.act e' C.wP 0)
          (homAt y.x (jetAug : Jet S (Fin 1 × Fin C.d) 0 →ₐ[S] S)).left)
        (rigT Xo.univ.t.G Xo.univ.t.PP.L Xo.univ.t.PP.rig (overAt y.x S) 1))
      (cc : ℕ → Fin C.d → Fin C.d → S),
      FrTruncC y { C with e := e', frame := hfr, rig0 := hrig } →
      (∀ m, ∃ u : (Jet S (Fin 2 × Fin C.d) m)ˣ,
        (u : Jet S (Fin 2 × Fin C.d) m) = psJet m (expP (-bilL C.B.G (cc m))) ∧
        LB.Gen.Corr Xo.univ.t.PP.L _ _ _ _ (e' m) (scaleGen (Xo := Xo) _ _ (unitΓ u) (C.e m))) →
      ∀ (k : ℕ) (F : LB.Sec (LPow Xo.univ.t.G Xo.univ.t.PP.L k (ptO Xo y.x))) (f : MvPowerSeries (Fin 1 × Fin C.d) S),
        IsGerm y C.d C.x C.B.A.act C.e C.wP k F f →
        ∃ f' : MvPowerSeries (Fin 1 × Fin C.d) S, IsGerm y C.d C.x C.B.A.act e' C.wP k F f' ∧
          ∀ D, psJet D f' = psJet D (f * expP ((k : S) • diagL C.B H.w0 (cc D)))

end Formalism.MainNotions.ModuliIntegralCharts.H1
end
end

-- bundled from Formalism.SharpRestriction.Divisibility.GeneratorPowers.ChartTransportSt
section
set_option autoImplicit false

noncomputable section

namespace Formalism.MainNotions.ModuliIntegralCharts.H1

open AlgebraicGeometry CategoryTheory NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
variable (Xo : Moduli Dw l) (c : Coeff l) [StarRing (𝓞 E)]

def ChartTransportSt : Prop :=
  (∀ a : 𝓞 E, star a = H.bar a) →
  ∀ (T : CDVR) (io : c.F →+* T.Fr) (y : IntFr Xo c T io) (I : IntData Xo c T io y.1) (d : ℕ)
    (B : Germ.FB T.V d (𝓞 E)) (tgT : Fin d → (Sp (DualNumber T.V) ⟶ I.G.G.left)) (uvecT : Lt1 Dw → Fin d → T.V)
    (xT : ∀ m, jOG (𝟙 (Sp T.V)) d m 1 ⟶ I.G.G) (eT : ∀ m, FrTyG I.G (𝟙 (Sp T.V)) d xT m) (wPT : PrimTyG I.G),
    ((∀ j, IsTanAtG I.G (𝟙 (Sp T.V)) (tgT j)) ∧
      ∀ w, IsTanAtG I.G (𝟙 (Sp T.V)) w → ∃! a : Fin d → T.V, IsCombAtG I.G (𝟙 (Sp T.V)) tgT a w) →
    IsChartG I.G (𝟙 (Sp T.V)) d B.G.F B.A.act tgT (fun j : Fin d => Pi.single j (1 : T.V)) xT →
    (∀ ℓ : Lt1 Dw, IsCombAtG I.G (𝟙 (Sp T.V))
      (fun j : Fin d => (homAt (𝟙 (Sp T.V))
        (jetTan ((0 : Fin 1), j) : Jet T.V (Fin 1 × Fin d) (0 + 1) →ₐ[T.V] DualNumber T.V) ≫ xT 1).left)
      (uvecT ℓ) (I.ub ℓ.1 ℓ.2).left) →
    IsFrameG I.G (𝟙 (Sp T.V)) d xT B.G.F B.A.act B.ph1 B.ph2 B.sy B.ad eT → IsPrimG I.G wPT →
    FrTrunc I.G (𝟙 (Sp T.V)) d xT eT → Rig0G I.G (𝟙 (Sp T.V)) d xT B.A.act eT wPT →
    letI := io.toAlgebra
    ∃ (B' : Germ.FB T.Fr d (𝓞 E)) (uvec : Lt1 Dw → Fin d → T.Fr) (x : ∀ m, jO y.1 d m 1 ⟶ Xo.univ.t.G)
      (e : ∀ m, FrTy y.1 d x m) (wP : PrimTy H Xo) (h : Germ.PS T.Fr 2 d)
      (hch : IsChart y.1 d B'.G.F B'.A.act uvec x)
      (hfr : IsFrame y.1 d x B'.G.F B'.A.act B'.ph1 B'.ph2 B'.sy B'.ad e) (hpr : IsPrim wP)
      (hg : B'.IsCanonGauge T.Fr h)
      (hr : LB.Gen.Corr Xo.univ.t.PP.L _ _ _ _
        (LB.pullGen Xo.univ.t.PP.L _ _ (eL y.1 d x B'.A.act e wP 0)
          (homAt y.1.x (jetAug : Jet T.Fr (Fin 1 × Fin d) 0 →ₐ[T.Fr] T.Fr)).left)
        (rigT Xo.univ.t.G Xo.univ.t.PP.L Xo.univ.t.PP.rig (overAt y.1.x T.Fr) 1)),
      IsGenFibreChart (⟨d, B', uvec, x, e, wP, h, hch, hfr, hpr, hg, hr⟩ : ChartAt Xo c y.1) I
        B.G.F B.A.act B.ph1 B.ph2 B.sy B.ad uvecT xT eT wPT

def FBMapSt : Prop :=
  ∀ (R R' : Type) [CommRing R] [CommRing R'] (ψ : R →+* R') (d : ℕ) (O : Type) [CommRing O] [StarRing O]
    (B : Germ.FB R d O), ∃ B' : Germ.FB R' d O,
      (∀ j, B'.G.F j = MvPowerSeries.map ψ (B.G.F j)) ∧ (∀ a j, B'.A.act a j = MvPowerSeries.map ψ (B.A.act a j)) ∧
      B'.ph1 = MvPowerSeries.map ψ B.ph1 ∧ B'.ph2 = MvPowerSeries.map ψ B.ph2 ∧ B'.sy = MvPowerSeries.map ψ B.sy ∧
      ∀ a, B'.ad a = MvPowerSeries.map ψ (B.ad a)

def ChartJetTrSt : Prop :=
  ∀ (T : CDVR) (io : c.F →+* T.Fr) (y : IntFr Xo c T io) (I : IntData Xo c T io y.1) (d : ℕ)
    (FT : Fin d → Germ.PS T.V 2 d) (actT : 𝓞 E → Fin d → Germ.PS T.V 1 d)
    (tgT : Fin d → (Sp (DualNumber T.V) ⟶ I.G.G.left)) (uvecT : Lt1 Dw → Fin d → T.V)
    (xT : ∀ m, jOG (𝟙 (Sp T.V)) d m 1 ⟶ I.G.G),
    ((∀ j, IsTanAtG I.G (𝟙 (Sp T.V)) (tgT j)) ∧
      ∀ w, IsTanAtG I.G (𝟙 (Sp T.V)) w → ∃! a : Fin d → T.V, IsCombAtG I.G (𝟙 (Sp T.V)) tgT a w) →
    IsChartG I.G (𝟙 (Sp T.V)) d FT actT tgT (fun j : Fin d => Pi.single j (1 : T.V)) xT →
    (∀ ℓ : Lt1 Dw, IsCombAtG I.G (𝟙 (Sp T.V))
      (fun j : Fin d => (homAt (𝟙 (Sp T.V))
        (jetTan ((0 : Fin 1), j) : Jet T.V (Fin 1 × Fin d) (0 + 1) →ₐ[T.V] DualNumber T.V) ≫ xT 1).left)
      (uvecT ℓ) (I.ub ℓ.1 ℓ.2).left) →
    letI := io.toAlgebra
    ∃ (x : ∀ m, jO y.1 d m 1 ⟶ Xo.univ.t.G) (x' : ∀ m, jOG (𝟙 (Sp T.Fr)) d m 1 ⟶ I.t'.G),
      IsChart y.1 d (fun j => MvPowerSeries.map (algebraMap T.V T.Fr) (FT j))
        (fun a j => MvPowerSeries.map (algebraMap T.V T.Fr) (actT a j))
        (fun ℓ i => algebraMap T.V T.Fr (uvecT ℓ i)) x ∧
      (∀ m, (x' m).left ≫ I.m2.φ = spMap (jetCoef (algebraMap T.V T.Fr) (Fin 1 × Fin d) m) ≫ (xT m).left) ∧
      ∀ m, (x' m).left ≫ I.m1.φ = (x m).left

def ChartFrameTrSt : Prop :=
  (∀ a : 𝓞 E, star a = H.bar a) →
  ∀ (T : CDVR) (io : c.F →+* T.Fr) (y : IntFr Xo c T io) (I : IntData Xo c T io y.1) (d : ℕ)
    (B : Germ.FB T.V d (𝓞 E)) (B' : Germ.FB T.Fr d (𝓞 E)) (tgT : Fin d → (Sp (DualNumber T.V) ⟶ I.G.G.left))
    (xT : ∀ m, jOG (𝟙 (Sp T.V)) d m 1 ⟶ I.G.G) (eT : ∀ m, FrTyG I.G (𝟙 (Sp T.V)) d xT m) (wPT : PrimTyG I.G),
    (∀ j, B'.G.F j = MvPowerSeries.map (algebraMap T.V T.Fr) (B.G.F j)) →
    (∀ a j, B'.A.act a j = MvPowerSeries.map (algebraMap T.V T.Fr) (B.A.act a j)) →
    B'.ph1 = MvPowerSeries.map (algebraMap T.V T.Fr) B.ph1 → B'.ph2 = MvPowerSeries.map (algebraMap T.V T.Fr) B.ph2 →
    B'.sy = MvPowerSeries.map (algebraMap T.V T.Fr) B.sy →
    (∀ a, B'.ad a = MvPowerSeries.map (algebraMap T.V T.Fr) (B.ad a)) →
    IsChartG I.G (𝟙 (Sp T.V)) d B.G.F B.A.act tgT (fun j : Fin d => Pi.single j (1 : T.V)) xT →
    IsFrameG I.G (𝟙 (Sp T.V)) d xT B.G.F B.A.act B.ph1 B.ph2 B.sy B.ad eT → IsPrimG I.G wPT →
    FrTrunc I.G (𝟙 (Sp T.V)) d xT eT → Rig0G I.G (𝟙 (Sp T.V)) d xT B.A.act eT wPT →
    letI := io.toAlgebra
    ∀ (x : ∀ m, jO y.1 d m 1 ⟶ Xo.univ.t.G) (x' : ∀ m, jOG (𝟙 (Sp T.Fr)) d m 1 ⟶ I.t'.G),
      (∀ m, (x' m).left ≫ I.m2.φ = spMap (jetCoef (algebraMap T.V T.Fr) (Fin 1 × Fin d) m) ≫ (xT m).left) →
      (∀ m, (x' m).left ≫ I.m1.φ = (x m).left) →
      ∃ (e : ∀ m, FrTy y.1 d x m) (wP : PrimTy H Xo),
        IsFrame y.1 d x B'.G.F B'.A.act B'.ph1 B'.ph2 B'.sy B'.ad e ∧ IsPrim wP ∧
        LB.Gen.Corr Xo.univ.t.PP.L _ _ _ _
          (LB.pullGen Xo.univ.t.PP.L _ _ (eL y.1 d x B'.A.act e wP 0)
            (homAt y.1.x (jetAug : Jet T.Fr (Fin 1 × Fin d) 0 →ₐ[T.Fr] T.Fr)).left)
          (rigT Xo.univ.t.G Xo.univ.t.PP.L Xo.univ.t.PP.rig (overAt y.1.x T.Fr) 1) ∧
        (∃ e' : ∀ m, FrTyG I.t' (𝟙 (Sp T.Fr)) d x' m, ∀ m, (e' m).IsGen ∧
          (∃ c₂ : LB.Gen (LB.LinComb I.G.PP.L
              (fun J => cφG I.t' ![jptG I.t' (𝟙 (Sp T.Fr)) d x' m (0 : Fin 2),
                jptG I.t' (𝟙 (Sp T.Fr)) d x' m (1 : Fin 2)] J ≫ I.m2.φ) (cε 2)),
            LB.Gen.Corr I.G.PP.L _ _ _ _ c₂
              (LB.pullGen I.G.PP.L _ _ (eT m) (spMap (jetCoef (algebraMap T.V T.Fr) (Fin 2 × Fin d) m))) ∧
            LB.Gen.Maps (LB.linCombIso I.w2 (cφG I.t' ![jptG I.t' (𝟙 (Sp T.Fr)) d x' m (0 : Fin 2),
                jptG I.t' (𝟙 (Sp T.Fr)) d x' m (1 : Fin 2)]) (cε 2)) (e' m)
              (flatGen I.G.PP.L I.m2.φ _ _ c₂)) ∧
          ∃ c₁ : LB.Gen (LB.LinComb Xo.univ.t.PP.L
              (fun J => cφG I.t' ![jptG I.t' (𝟙 (Sp T.Fr)) d x' m (0 : Fin 2),
                jptG I.t' (𝟙 (Sp T.Fr)) d x' m (1 : Fin 2)] J ≫ I.m1.φ) (cε 2)),
            LB.Gen.Corr Xo.univ.t.PP.L _ _ _ _ c₁ (e m) ∧
            LB.Gen.Maps (LB.linCombIso I.w1 (cφG I.t' ![jptG I.t' (𝟙 (Sp T.Fr)) d x' m (0 : Fin 2),
                jptG I.t' (𝟙 (Sp T.Fr)) d x' m (1 : Fin 2)]) (cε 2)) (e' m)
              (flatGen Xo.univ.t.PP.L I.m1.φ _ _ c₁)) ∧
        ∃ wP' : LB.Gen (LB.LinComb I.t'.PP.L (primφ I.t') primε), wP'.IsGen ∧
          (∃ c₂ : LB.Gen (LB.LinComb I.G.PP.L (fun k => primφ I.t' k ≫ I.m2.φ) primε),
            LB.Gen.Corr I.G.PP.L _ _ _ _ c₂ (LB.pullGen I.G.PP.L _ _ wPT I.m2.φ) ∧
            LB.Gen.Maps (LB.linCombIso I.w2 (primφ I.t') primε) wP' (flatGen I.G.PP.L I.m2.φ _ _ c₂)) ∧
          ∃ c₁ : LB.Gen (LB.LinComb Xo.univ.t.PP.L (fun k => primφ I.t' k ≫ I.m1.φ) primε),
            LB.Gen.Corr Xo.univ.t.PP.L _ _ _ _ c₁ (LB.pullGen Xo.univ.t.PP.L _ _ wP I.m1.φ) ∧
            LB.Gen.Maps (LB.linCombIso I.w1 (primφ I.t') primε) wP' (flatGen Xo.univ.t.PP.L I.m1.φ _ _ c₁)


omit [StarRing (𝓞 E)] in
def FrTanBasisSt : Prop :=
  ∀ (S : Type) [Field S] [Algebra c.F S] (y : FrPt Xo c S) (w : Sp (DualNumber S) ⟶ Xo.univ.t.G.left),
    IsTanAt y.x w →
    ∃! a : Lt1 Dw → S, IsCombAt y.x (m := Fintype.card (Lt1 Dw))
      (fun i => y.u ((Fintype.equivFin (Lt1 Dw)).symm i).1 ((Fintype.equivFin (Lt1 Dw)).symm i).2)
      (fun i => a ((Fintype.equivFin (Lt1 Dw)).symm i)) w

end Formalism.MainNotions.ModuliIntegralCharts.H1
end
end

-- bundled from Formalism.SharpRestriction.Divisibility.GeneratorPowers.ExpAct
section
set_option autoImplicit false

noncomputable section

namespace Formalism.MainNotions.ModuliIntegralCharts.H1

open AlgebraicGeometry CategoryTheory NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj

def ExpActOfSt : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H)
    (Xo : Moduli Dw l) (c : Coeff l) [StarRing (𝓞 E)] (S : Type) [CommRing S] [Algebra c.F S] [Algebra ℚ S]
    (y : FrPt Xo c S) (C : ChartAt Xo c y) (φ : Fin C.d → MvPowerSeries (Fin 1 × Fin (dL Dw)) S),
    IsExpOf C.B.G.F C.uvec φ → ∀ (a : 𝓞 E) (j : Fin C.d),
      MvPowerSeries.subst (fun p : Fin 1 × Fin C.d => φ p.2) (C.B.A.act a j) =
        MvPowerSeries.subst (fun q : Fin 1 × Fin (dL Dw) =>
          algebraMap c.F S (embK c ((ltIdx Dw).symm q.2).1 a) •
            (MvPowerSeries.X q : MvPowerSeries (Fin 1 × Fin (dL Dw)) S)) (φ j)

end Formalism.MainNotions.ModuliIntegralCharts.H1
end
end

-- bundled from Formalism.SharpRestriction.Divisibility.GeneratorPowers.IntChartSt
section
set_option autoImplicit false

noncomputable section

namespace Formalism.MainNotions.ModuliIntegralCharts.H1

open AlgebraicGeometry CategoryTheory NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj

def IntChartStatement : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E)
    (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V],
    IsAdicComplete (IsLocalRing.maximalIdeal V) V →
    ∀ (t : SAB H (Sp V)),
    IsProper ((Over.pullback (spMap (algebraMap V (FractionRing V)))).obj t.G).hom →
    ∀ {κ : Type} [Fintype κ] (tg : κ → (Sp (DualNumber V) ⟶ t.G.left)),
      (∀ ℓ, IsTanAtG t (𝟙 (Sp V)) (tg ℓ)) →
      (∀ w, IsTanAtG t (𝟙 (Sp V)) w →
        ∃! a : κ → V, IsCombAtG t (𝟙 (Sp V)) (m := Fintype.card κ)
          (fun i => tg ((Fintype.equivFin κ).symm i)) (fun i => a ((Fintype.equivFin κ).symm i)) w) →
      ∀ [StarRing (𝓞 E)], (∀ a : 𝓞 E, star a = H.bar a) →
      ∃ (d : ℕ) (B : Germ.FB V d (𝓞 E)) (uvec : κ → Fin d → V) (x : ∀ m, jOG (𝟙 (Sp V)) d m 1 ⟶ t.G)
        (e : ∀ m, FrTyG t (𝟙 (Sp V)) d x m) (wP : PrimTyG t),
        d = Fintype.card κ ∧ (∀ ℓ (j : Fin d), uvec ℓ j = if (j : ℕ) = (Fintype.equivFin κ ℓ : ℕ) then 1 else 0) ∧
        IsChartG t (𝟙 (Sp V)) d B.G.F B.A.act tg uvec x ∧
        IsFrameG t (𝟙 (Sp V)) d x B.G.F B.A.act B.ph1 B.ph2 B.sy B.ad e ∧
        IsPrimG t wP ∧ FrTrunc t (𝟙 (Sp V)) d x e ∧ Rig0G t (𝟙 (Sp V)) d x B.A.act e wP ∧
        ∀ (k : ℕ) (F : LB.Sec (LPow t.G t.PP.L k (Over.mk (𝟙 (Sp V))))),
          ∃ f, IsGermG t (𝟙 (Sp V)) d x B.A.act e wP k F f

end Formalism.MainNotions.ModuliIntegralCharts.H1
end
end

-- bundled from Formalism.SharpRestriction.Divisibility.GeneratorPowers.UnitIdSt
section
set_option autoImplicit false

noncomputable section

namespace Formalism.MainNotions.ModuliIntegralCharts.H1.ExpGU

open AlgebraicGeometry CategoryTheory Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj

section Defs

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
variable {S : Type} [CommRing S]

def actPS (c : Coeff l) [Algebra c.F S] (a : 𝓞 E) : Fin 1 × Fin (dL Dw) → MvPowerSeries (Fin 1 × Fin (dL Dw)) S :=
  fun q => algebraMap c.F S (embK c ((ltIdx Dw).symm q.2).1 a) • MvPowerSeries.X q

def φa (c : Coeff l) [Algebra c.F S] {d : ℕ} (φ : Fin d → MvPowerSeries (Fin 1 × Fin (dL Dw)) S) (a : 𝓞 E) :
    Fin d → MvPowerSeries (Fin 1 × Fin (dL Dw)) S :=
  fun j => MvPowerSeries.subst (actPS (Dw := Dw) c a) (φ j)

def atP {d n : ℕ} (P : Fin n → Fin d → MvPowerSeries (Fin 1 × Fin (dL Dw)) S)
    (f : MvPowerSeries (Fin n × Fin d) S) : MvPowerSeries (Fin 1 × Fin (dL Dw)) S :=
  MvPowerSeries.subst (fun p : Fin n × Fin d => P p.1 p.2) f

end Defs

def UnitIdSt : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H)
    (Xo : Moduli Dw l) (c : Coeff l) [StarRing (𝓞 E)], (∀ a : 𝓞 E, star a = H.bar a) →
    ∀ (S : Type) [CommRing S] [Algebra c.F S] [Algebra ℚ S] (y : FrPt Xo c S) (C : ChartAt Xo c y)
      (φ : Fin C.d → MvPowerSeries (Fin 1 × Fin (dL Dw)) S), IsExpOf C.B.G.F C.uvec φ →
      (∀ (a : 𝓞 E) (j : Fin C.d), MvPowerSeries.subst (fun p : Fin 1 × Fin C.d => φ p.2) (C.B.A.act a j) =
        MvPowerSeries.subst (actPS (Dw := Dw) c a) (φ j)) →
      ∀ a : 𝓞 E,
        Germ.FB.expS S (-(compL (φa c φ (1 + a * H.bar a)) (C.B.hL S C.h H.w0))) *
            atP ![φa c φ a, φa c φ H.w0] (C.B.ad (H.bar a)) =
          atP ![φ, φa c φ (a * H.bar a), φa c φ ((1 + a * H.bar a) * H.w0)] C.B.ph1 *
            atP ![φ, φa c φ H.w0, φa c φ (a * H.bar a * H.w0)] C.B.ph2 *
            atP ![φa c φ (a * H.bar a), φa c φ H.w0, φa c φ (a * H.bar a * H.w0)] C.B.ph2 *
            atP ![φ, φa c φ (a * H.w0)] (C.B.ad a) *
            Germ.FB.expS S (-(compL (φa c φ a) (C.B.hL S C.h H.w0))) ^ 2 *
            Germ.FB.expS S (-(compL φ (C.B.hL S C.h H.w0))) *
            Germ.FB.expS S (-(compL (φa c φ (a * H.bar a)) (C.B.hL S C.h H.w0)))

end Formalism.MainNotions.ModuliIntegralCharts.H1.ExpGU
end
end

