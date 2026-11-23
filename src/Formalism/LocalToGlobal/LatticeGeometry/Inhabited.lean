module

public import Formalism.LocalToGlobal.LatticeGeometry.Bundle0003
public import Formalism.LocalToGlobal.LatticeGeometry.InhabLoc
public import Mathlib
public import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
public import Formalism.LocalRingCardinality.DataDIV
public import Formalism.SharpRestriction.ParConsts
public import Formalism.SharpRestriction.ParamsHeightRankConstant
public import Formalism.SharpRestriction.Divisibility.ModuliIntegralCharts
public import Formalism.SharpRestriction.Divisibility.BoundaryLocalData
public import Formalism.SharpRestriction.Divisibility.WeightThresholdDefs
public import Formalism.LocalRingCardinality.SpanPowerMembership.UnitsPowSurjective
public import Formalism.LocalRingCardinality.SpanPowerMembership.Bundle0004

@[expose] public section

noncomputable section

open Formalism.BasicNotions Formalism.MainNotions MeasureTheory NumberField IsDedekindDomain Formalism.MainNotions.DIV.Inh Formalism.MainNotions.DIV.Inh.LocalProvisionModel

namespace Formalism.L2.Geo

def geoDegenerateNoTau (F : Type) [Field F] [NumberField F] [StarRing F] : DV.Geo F where
  Var := ℕ
  dim := id
  Fn := fun _ => F
  fnField := fun _ => inferInstanceAs (Field F)
  fnAlg := fun _ => inferInstanceAs (Algebra F F)
  Dv := fun _ => ℤ
  dvGrp := fun _ => inferInstanceAs (AddCommGroup ℤ)
  Eff := fun _ _ => True
  eff_zero := fun _ => trivial
  eff_add := fun _ _ _ _ _ => trivial
  H0 := fun _ _ => ⊥
  degreeZeroCohomology_finiteDimensional := fun _ _ => inferInstance
  mul_mem_riemannRochSpace_add := fun _ _ _ f g hf _ => by
    rw [Submodule.mem_bot] at hf ⊢; simp [hf]
  riemannRoch_mono := fun _ _ _ _ => le_refl _
  KY := fun _ => (0 : ℤ)
  Cl := fun _ => PUnit
  properCl := fun _ _ => True
  subCl := fun _ _ _ => True
  supp := fun _ _ => PUnit.unit
  inter := fun _ _ => 0
  nef := fun _ _ => True
  big := fun _ _ => True
  bpf := fun _ _ _ => True
  phiBir := fun _ _ _ => True
  phiNoContr := fun _ _ _ _ => True
  vanishOn := fun _ _ _ _ => True
  hdim := fun _ _ _ => 0
  pts := fun _ _ => PUnit
  ptsMeas := fun _ _ => ⊤
  vol := fun _ _ => 0
  FnC := fun _ _ => ℂ
  fnCRing := fun _ _ => inferInstanceAs (CommRing ℂ)
  fnCAlg := fun _ _ => inferInstanceAs (Algebra ℂ ℂ)
  cx := fun _ σ => σ
  cx_smul := fun _ σ a f => by
    show σ (a * f) = σ a * σ f
    exact map_mul σ a f
  Met := fun _ _ _ => PUnit
  mAdd := fun _ _ _ _ _ _ => PUnit.unit
  mPow := fun _ _ _ _ _ => PUnit.unit
  fsMet := by intros; exact PUnit.unit
  pn := fun _ _ _ _ _ _ => 0
  pnK := fun _ _ _ _ _ _ => 0
  mSmooth := fun _ _ _ _ => True
  mPsh := fun _ _ _ _ _ => True
  redZero := fun _ _ _ _ _ => True
  agreeOn := fun _ _ _ _ _ _ => True
  resNorm := by intros; exact 0
  Adl := fun _ => PUnit
  ofW := fun _ _ _ _ => PUnit.unit
  twist := fun _ _ _ _ => PUnit.unit
  arTop := fun _ _ => 0
  arVol := fun _ _ => 0
  nefA := fun _ _ => True
  supInf := fun _ _ _ _ _ => 0
  supFin := fun _ _ _ _ _ => 0
  cutGood := by intros; exact True
  cutHt := by intros; exact 0
  cutOrd := by intros; exact 0
  resFull := by intros; exact True
  resDeg := by intros; exact 0
  supInf_ofW := by intros; simp
  supInf_twist := by intros; simp
  supFin_twist := by intros; simp
  regOn := fun _ _ _ _ _ => True

def ngJunk : NgPkg where
  NgC := fun _ => PUnit
  NgC_ne := fun _ => ⟨PUnit.unit⟩
  KF := fun _ _ => Empty
  kfNorm := fun k _ => k.elim

def cxJunk (Tau : Type) [Fintype Tau] (N j : ℕ) : CxPkg Tau N j PUnit where
  Γ := fun _ => ⊥
  Γ_le := fun _ => bot_le
  volC := fun _ => 1
  volC_pos := fun _ => one_pos
  rfn := fun _ => Real.exp 1
  rfn_ge := fun _ => le_refl _
  hLo := fun _ => 1
  hUp := fun _ => 1
  hLo_le := fun _ => ⟨one_pos, le_refl _⟩
  connN := fun _ => 0
  curvN := fun _ => 0
  normDetInf := fun _ _ => 0

variable (D : D7)

def algJunk (N : ℕ) : AlgPkg (geoDegenerateNoTau D.what₂.LL) D.what₂.Tau N PUnit where
  Yv := fun _ => Formalism.DegreeFormula.dimFl D.what₂.Tau N
  Ybd := fun _ => PUnit.unit
  bd := fun _ => (0 : ℤ)
  bd_supp := fun _ => rfl
  Lw := fun _ => 0
  dim_eq := fun _ => rfl
  degA := fun _ _ => 0
  degA_ofW := fun _ _ _ _ => by simp [geoDegenerateNoTau]
  degA_twist := fun _ _ _ _ => rfl
  semipos := fun _ => True
  nefFib := fun _ => True
  Mbar := fun _ _ _ _ => PUnit.unit

def iThJunk (d : ℕ) : DV.ITh where
  LB := PUnit
  Ch := ℚ
  c1 := fun _ => 0
  VDiv := ℚ
  cD := 0
  capDeg := 0
  divP := 0
  cD_divP := rfl
  dim := d

def fpJunk (d r : ℕ) : DV.FPair (iThJunk d) r where
  x := fun _ => PUnit.unit
  x' := fun _ => PUnit.unit
  Dv := fun _ => 0
  hx := fun _ => by show (0 : ℚ) = 0 - (0 : ℚ →ₗ[ℚ] ℚ) 0; simp

theorem rkOf_dual {p : ℕ} [Fact p.Prime] (Ps : Set (DV.Emb D p)) (N j : ℕ) (hj : j ≤ N)
    (hPs : ∀ τ, τ ∈ Ps ↔ DV.cEmb D τ ∉ Ps) (τ : DV.Emb D p) :
    N - DV.rkOf Ps N j τ = DV.rkOf Ps N j (DV.cEmb D τ) := by
  classical
  unfold DV.rkOf
  by_cases h : τ ∈ Ps
  · have h' : DV.cEmb D τ ∉ Ps := (hPs τ).1 h
    simp [h, h']
  · have h' : DV.cEmb D τ ∈ Ps := by
      by_contra h''; exact h ((hPs τ).2 h'')
    simp [h, h']; omega

def mdlJunk (p : ℕ) [Fact p.Prime] (jc : DV.KW p →+* ℂ) (N j : ℕ) (hj : j ≤ N) :
    DV.Mdl D p N (DV.rkOf (DV.PsiOf D jc) N j) where
  Z := iThJunk (Formalism.DegreeFormula.dimFl D.what₂.Tau N + 1)
  cov := 1
  cov_pos := one_pos
  lvl := 0
  lie := fun _ => fpJunk _ _
  om := fun _ => fpJunk _ _
  lieW := fpJunk _ _
  omW := fpJunk _ _
  om_dual := fun τ => ⟨finCongr (rkOf_dual D _ N j hj (fun τ => psiOf_cm p jc τ) τ), fun _ => by show (0 : ℚ) = -0; rw [neg_zero]⟩
  dim_eq := rfl
  omW_dual := ⟨Equiv.refl _, fun _ => by show (0 : ℚ) = -0; rw [neg_zero]⟩

def padJunk (N j : ℕ) (hj : j ≤ N) (jC : ∀ (p : ℕ) [Fact p.Prime], PlL D p → (DV.KW p →+* ℂ)) :
    PadPkg D N j PUnit jC ngJunk where
  loc := fun p => junkLocalData D N j p
  ex := fun p => exJunk D N j p
  locB := fun p hp => junkLocB D N j p hp
  pbKF := fun _ _ k => Empty.elim k
  levIn := fun _ => True
  Xg := Empty
  bc := fun _ Z => Z.elim
  DivG := fun Z => Z.elim
  effD := @fun Z _ => Z.elim
  noVertD := @fun Z _ => Z.elim
  posBdD := @fun Z _ => Z.elim
  ampleOnAbelianBase := fun Z _ _ => Z.elim
  Met := Empty
  nefFibM := fun M => M.elim
  ampleGen := fun M => M.elim
  limRA := fun M => M.elim
  Mp := fun _ _ => PUnit
  md := fun p _ la _ => mdlJunk D p (jC p la) N j hj
  CurveM := fun _ _ _ => Empty
  degM := fun _ _ _ c => c.elim
  htMdl := fun _ _ => PUnit.unit
  Pt := Empty
  compPt := fun y => y.elim
  phiDR := fun _ y => y.elim
  phiMod := fun _ y => y.elim
  phiFr := fun _ y => y.elim
  phiFr_unram := fun _ y => y.elim
  normDetT := fun _ _ y => y.elim
  normDetH := fun _ _ y => y.elim
  htDetT := fun _ _ _ => 0
  arDeg := fun _ _ => 0
  arDeg_homog := fun _ _ _ _ _ _ => rfl
  arMix := fun _ _ _ => 0
  arMix_HT := fun _ _ _ _ => rfl
  arMix_DR := fun _ _ _ _ => rfl

section FlagZ

variable (ι : Type) [Fintype ι] [DecidableEq ι] (N : ℕ)

def degFlZ (P : MvPolynomial (ι × Fin N) ℤ) : ℤ :=
  (-1) ^ Formalism.DegreeFormula.dimFl ι N *
    ∑ σ : ι → Equiv.Perm (Fin N), (∏ τ, ((Equiv.Perm.sign (σ τ) : ℤ))) * P.coeff (Formalism.DegreeFormula.permExp σ)

def linRootZ (lam : ι → Fin N → ℤ) : MvPolynomial (ι × Fin N) ℤ :=
  -∑ x : ι × Fin N, MvPolynomial.C (lam x.1 x.2) * MvPolynomial.X x

def flagDegZ (lam : ι → Fin N → ℤ) : ℤ := degFlZ ι N (linRootZ ι N lam ^ Formalism.DegreeFormula.dimFl ι N)

end FlagZ


open Classical in
@[reducible] def geoDegenerate (F : Type) [Field F] [NumberField F] [StarRing F] (Tau : Type) [Fintype Tau] : DV.Geo F where
  Var := ℕ
  dim := fun N => Formalism.DegreeFormula.dimFl Tau N
  Fn := fun _ => F
  fnField := fun _ => inferInstanceAs (Field F)
  fnAlg := fun _ => inferInstanceAs (Algebra F F)
  Dv := fun N => Tau → Fin N → ℤ
  dvGrp := fun _ => inferInstance
  Eff := fun _ _ => True
  eff_zero := fun _ => trivial
  eff_add := fun _ _ _ _ _ => trivial
  H0 := fun _ _ => ⊤
  degreeZeroCohomology_finiteDimensional := fun _ _ => inferInstance
  mul_mem_riemannRochSpace_add := fun _ _ _ _ _ _ _ => Submodule.mem_top
  riemannRoch_mono := fun _ _ _ _ => le_refl _
  KY := fun _ => 0
  Cl := fun _ => PUnit
  properCl := fun _ _ => True
  subCl := fun _ _ _ => True
  supp := fun _ _ => PUnit.unit
  inter := fun N v => if h : 0 < Formalism.DegreeFormula.dimFl Tau N then flagDegZ Tau N (v ⟨0, h⟩) else flagDegZ Tau N 0
  nef := fun _ _ => True
  big := fun _ _ => True
  bpf := fun _ _ _ => True
  phiBir := fun _ _ _ => True
  phiNoContr := fun _ _ _ _ => True
  vanishOn := fun _ _ _ _ => True
  hdim := fun _ _ _ => 0
  pts := fun _ _ => PUnit
  ptsMeas := fun _ _ => ⊤
  vol := fun _ _ => 0
  FnC := fun _ _ => ℂ
  fnCRing := fun _ _ => inferInstanceAs (CommRing ℂ)
  fnCAlg := fun _ _ => inferInstanceAs (Algebra ℂ ℂ)
  cx := fun _ σ => σ
  cx_smul := fun _ σ a f => by
    show σ (a * f) = σ a * σ f
    exact map_mul σ a f
  Met := fun _ _ _ => PUnit
  mAdd := fun _ _ _ _ _ _ => PUnit.unit
  mPow := fun _ _ _ _ _ => PUnit.unit
  fsMet := by intros; exact PUnit.unit
  pn := fun _ _ _ _ _ _ => 0
  pnK := fun _ _ _ _ _ _ => 0
  mSmooth := fun _ _ _ _ => True
  mPsh := fun _ _ _ _ _ => True
  redZero := fun _ _ _ _ _ => True
  agreeOn := fun _ _ _ _ _ _ => True
  resNorm := by intros; exact 0
  Adl := fun N => Tau → Fin N → ℤ
  ofW := fun _ L _ _ => L
  twist := fun _ L _ _ => L
  arTop := fun _ _ => 0
  arVol := fun _ _ => 0
  nefA := fun _ _ => True
  supInf := fun _ _ _ _ _ => 0
  supFin := fun _ _ _ _ _ => 0
  cutGood := by intros; exact True
  cutHt := by intros; exact 0
  cutOrd := by intros; exact 0
  resFull := by intros; exact True
  resDeg := by intros; exact 0
  supInf_ofW := by intros; simp
  supInf_twist := by intros; simp
  supFin_twist := by intros; simp
  regOn := fun _ _ _ _ _ => True

def ng1 : NgPkg where
  NgC := fun _ => PUnit
  NgC_ne := fun _ => ⟨PUnit.unit⟩
  KF := fun _ _ => PUnit
  kfNorm := fun _ _ => 1

def rho2 (r : ℕ) : ℕ := if 2 ≤ r then 1 else 0

def loc2 (r j p : ℕ) : ModuliIntegralCharts.Loc D r j p := locT D r j p (cfJunk p) (rho2 r)

def ex2 (r j p : ℕ) : ModuliIntegralCharts.ExtA D (loc2 D r j p) := extT D r j p (cfJunk p) (rho2 r)

def localBasisTwo (r j p : ℕ) (hp : p.Prime) : BoundaryLocalData.LocB D (loc2 D r j p) :=
  locBT D r j p (cfJunk p) (rho2 r) (Or.inl hp.two_le) (by
    unfold rho2
    split_ifs with h
    · nlinarith [h]
    · simp)

def padDegenerate (N j : ℕ) (hj : j ≤ N) (jC : ∀ (p : ℕ) [Fact p.Prime], PlL D p → (DV.KW p →+* ℂ)) :
    PadPkg D N j PUnit jC ng1 where
  loc := fun p => loc2 D N j p
  ex := fun p => ex2 D N j p
  locB := fun p hp => localBasisTwo D N j p hp
  pbKF := fun p _ _ => (1 : (cfJunk p).C)
  levIn := fun _ => True
  Xg := PUnit
  bc := fun _ _ => ()
  DivG := fun _ => PUnit
  effD := @fun _ _ => True
  noVertD := @fun _ _ => True
  posBdD := @fun _ _ => True
  ampleOnAbelianBase := fun _ _ _ => True
  Met := PUnit
  nefFibM := fun _ => True
  ampleGen := fun _ => True
  limRA := fun _ => True
  Mp := fun _ _ => PUnit
  md := fun p _ la _ => mdlJunk D p (jC p la) N j hj
  CurveM := fun _ _ _ => PUnit
  degM := fun _ _ _ _ _ => 0
  htMdl := fun _ _ => PUnit.unit
  Pt := PUnit
  compPt := fun _ => PUnit.unit
  phiDR := fun _ _ _ => 1
  phiMod := fun _ _ _ => 0
  phiFr := fun _ _ _ => 1
  phiFr_unram := fun _ _ _ _ => rfl
  normDetT := fun _ _ _ => 1
  normDetH := fun _ _ _ => 1
  htDetT := fun _ _ _ => 0
  arDeg := fun _ _ => 0
  arDeg_homog := fun _ _ _ _ _ _ => rfl
  arMix := fun _ _ _ => 0
  arMix_HT := fun _ _ _ _ => rfl
  arMix_DR := fun _ _ _ _ => rfl

def algDegenerate (N : ℕ) : AlgPkg (geoDegenerate D.what₂.LL D.what₂.Tau) D.what₂.Tau N PUnit where
  Yv := fun _ => N
  Ybd := fun _ => PUnit.unit
  bd := fun _ => 0
  bd_supp := fun _ => rfl
  Lw := fun _ => AddMonoidHom.id _
  dim_eq := fun _ => rfl
  degA := fun _ L => ((geoDegenerate D.what₂.LL D.what₂.Tau).inter N (fun _ => L) : ℝ)
  degA_ofW := fun _ _ _ _ => rfl
  degA_twist := fun _ _ _ _ => rfl
  semipos := fun _ => True
  nefFib := fun _ => True
  Mbar := fun _ _ _ _ => 0

def shimUFl {Lev : Type} (jC : ∀ (p : ℕ) [Fact p.Prime], PlL D p → (DV.KW p →+* ℂ)) (w : Dat D Lev) :
    ShimU D (geoDegenerate D.what₂.LL D.what₂.Tau) jC ng1 w where
  Comp := PUnit
  cx := cxJunk D.what₂.Tau w.N w.j
  alg := algDegenerate D w.N
  pad := padDegenerate D w.N w.j w.j_le jC

section Ar

variable (Tau : Type) [Fintype Tau] (N : ℕ)

end Ar

def formsFl (KO : Type) [Field KO] [NumberField KO] (eO : 𝓞 KO ≃+* D.what₂.O) (kL : KO →+* D.what₂.LL)
    (kL_eO : ∀ x : 𝓞 KO, kL (x : KO) = D.what₂.OtoLL (eO x))
    (NW : ℕ → ℕ) (algW : ∀ j, AlgPkg (geoDegenerate D.what₂.LL D.what₂.Tau) D.what₂.Tau (NW j) PUnit.{1})
    (PtY : ℕ → ℕ → Type) (pt : ∀ j p, PtY j p) :
    FormsPkg D (geoDegenerate D.what₂.LL D.what₂.Tau) NW (fun _ => PUnit.{1}) algW PtY where
  KO := KO
  eO := eO
  kL := kL
  kL_eO := kL_eO
  Cusp := fun _ _ => KO
  cmp := fun _ _ _ =>
    { toFun := fun F => (kL F : D.what₂.LL)
      map_add' := fun F F' => map_add kL F F'
      map_smul' := fun a F => by
        show kL (a * F) = kL a * kL F
        exact map_mul kL a F }
  cmp_mem := fun _ _ _ _ => Submodule.mem_top
  cmp_cusp := fun _ _ _ _ => trivial
  cmp_span := fun j _ _ w s _ => by
    have hs : s = (s PUnit.unit : D.what₂.LL) • (fun (_ : PUnit.{1}) => (kL 1 : D.what₂.LL)) := by
      funext c
      cases c
      show (s PUnit.unit : D.what₂.LL) = (s PUnit.unit : D.what₂.LL) * kL 1
      rw [map_one, mul_one]
    rw [hs]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨1, rfl⟩)
  cmp_indep := fun j w {n} v hv => by
    have hn : n ≤ 1 := by
      have := hv.fintype_card_le_finrank
      simpa using this
    rcases Nat.lt_or_ge n 1 with h0 | h1
    · have : IsEmpty (Fin n) := ⟨fun i => absurd i.2 (by omega)⟩
      exact linearIndependent_empty_type
    · obtain rfl : n = 1 := le_antisymm hn h1
      refine linearIndependent_unique_iff.2 ?_
      intro h
      have h2 := congrFun h PUnit.unit
      have h3 : kL (v default) = 0 := h2
      exact hv.ne_zero default ((map_eq_zero_iff kL kL.injective).1 h3)
  mulC := fun _ _ _ F F' => F * F'
  cmp_mul := fun _ _ _ _ F F' => map_mul kL F F'
  supN := fun _ _ σ F => ‖σ F‖
  supN_nonneg := fun _ _ _ _ => norm_nonneg _
  supN_eq_zero := fun _ _ σ F => by rw [norm_eq_zero, map_eq_zero_iff σ σ.injective]
  supN_smul := fun _ _ σ a F => by
    show ‖σ (a * F)‖ = ‖σ a‖ * ‖σ F‖
    rw [map_mul, norm_mul]
  supN_add := fun _ _ σ F G => by
    show ‖σ (F + G)‖ ≤ ‖σ F‖ + ‖σ G‖
    rw [map_add (f := _)]; exact norm_add_le _ _
  l2NormAlt := fun _ _ σ F => ‖σ F‖
  l2Norm_nonneg_bis := fun _ _ _ _ => norm_nonneg _
  l2Norm_eq_zero_iff := fun _ _ σ F => by rw [norm_eq_zero, map_eq_zero_iff σ σ.injective]
  l2Norm_smul_alt := fun _ _ σ a F => by
    show ‖σ (a * F)‖ = ‖σ a‖ * ‖σ F‖
    rw [map_mul, norm_mul]
  l2Norm_add_le' := fun _ _ σ F G => by
    show ‖σ (F + G)‖ ≤ ‖σ F‖ + ‖σ G‖
    rw [map_add (f := _)]; exact norm_add_le _ _
  l2Norm_le_supNorm_alt := fun _ _ _ _ => le_rfl
  Cu := fun _ => PUnit.{1}
  Xc := fun j _ => Submodule.span (𝓞 D.host.E) (Set.range (Pi.basisFun D.host.E (Fin (WeightFamilies.rho D j))))
  Xc_lat := fun _ _ => Submodule.IsLattice.of_fg D.host.E (Submodule.fg_span (Set.finite_range _))
  FJt := fun _ _ _ _ => KO
  sg := fun _ _ _ _ => LinearMap.id
  Pt := fun _ _ => PUnit.{1}
  pt66 := fun j la _ => pt j _
  vAtC := fun _ la _ _ F => vEK la F
  vAtC_zero := fun _ la _ _ => vEK_zero la
  vAtC_ne_bot := fun _ la _ _ F => vEK_ne_bot la F
  vAtC_add := fun _ la _ _ F G => vEK_add la F G
  vAtC_smul := fun _ la _ _ a F ha => vEK_mul la ha F
  vAtC_mul := fun _ la _ _ _ F F' => by
    show vEK la (F * F') = vEK la F + vEK la F'
    by_cases hF : F = 0
    · rw [hF, zero_mul, vEK_zero, EReal.top_add_of_ne_bot (vEK_ne_bot la F')]
    · rw [vEK_mul la hF, vEK_of_ne la hF]
  thAll := fun _ _ => ⊥
  shortTh := fun _ _ => ⊥

section Tied

variable (jC : ∀ (p : ℕ) [Fact p.Prime], PlL D p → (DV.KW p →+* ℂ))

def shimXJunk (N j : ℕ) (h1 : 1 ≤ j) (h2 : j < N) : DV.ShimX D.what₂.Tau where
  N := N
  j := j
  j_pos := h1
  j_lt := h2
  lev := Finset.univ.image D.host.g
  lev_prime := fun p hp => by
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.1 hp
    exact D.host.g_prime i
  Comp := PUnit
  vol := (cxJunk D.what₂.Tau N j).vol
  chern := (cxJunk D.what₂.Tau N j).chern
  chern_homog := fun P d hd hP => chernOf_homog D.what₂.Tau N (cxJunk D.what₂.Tau N j).vol P d hd hP
  arDeg := (padJunk D N j h2.le jC).arDeg
  arDeg_homog := (padJunk D N j h2.le jC).arDeg_homog
  arMix := (padJunk D N j h2.le jC).arMix
  arMix_HT := (padJunk D N j h2.le jC).arMix_HT
  arMix_DR := (padJunk D N j h2.le jC).arMix_DR
  CurveHT := (padJunk D N j h2.le jC).CurveHT
  degHT := (padJunk D N j h2.le jC).degHT
  CurveDR := (padJunk D N j h2.le jC).CurveDR
  degDR := (padJunk D N j h2.le jC).degDR
  FibComp := (padJunk D N j h2.le jC).FibComp
  fibInBd := (padJunk D N j h2.le jC).fibInBd
  Pt := (padJunk D N j h2.le jC).Pt
  phiDR := (padJunk D N j h2.le jC).phiDR
  phiMod := (padJunk D N j h2.le jC).phiMod
  phiFr := (padJunk D N j h2.le jC).phiFr
  XC := (cxJunk D.what₂.Tau N j).XC
  rfn := (cxJunk D.what₂.Tau N j).rfn
  rfn_ge := (cxJunk D.what₂.Tau N j).rfn_ge
  hLo := (cxJunk D.what₂.Tau N j).hLo
  hUp := (cxJunk D.what₂.Tau N j).hUp
  hLo_le := (cxJunk D.what₂.Tau N j).hLo_le
  connN := (cxJunk D.what₂.Tau N j).connN
  curvN := (cxJunk D.what₂.Tau N j).curvN
  compOf := (cxJunk D.what₂.Tau N j).compOf
  normDetInf := (cxJunk D.what₂.Tau N j).normDetInf
  compPt := (padJunk D N j h2.le jC).compPt
  normDetT := (padJunk D N j h2.le jC).normDetT
  normDetH := (padJunk D N j h2.le jC).normDetH
  htDetT := (padJunk D N j h2.le jC).htDetT
  ALB := (algJunk D N).ALB
  arSelf := fun L => ∑ c, (algJunk D N).arSelfC L c
  arSelfC := (algJunk D N).arSelfC
  arSelf_sum := fun _ => rfl
  geo := fun L => ∑ c, (algJunk D N).geoC L c
  geoC := (algJunk D N).geoC
  geo_sum := fun _ => rfl
  arVol := (algJunk D N).arVol
  semipos := (algJunk D N).semipos
  nefFib := (algJunk D N).nefFib
  arNef := (algJunk D N).arNef
  Mbar := (algJunk D N).Mbar

def recN (S : letI := D.host.cmStar; HSpace D.host.E) : ℕ :=
  letI := D.host.cmStar; if 2 ≤ S.rank then S.rank else 2

def firstSignatureEntry (S : letI := D.host.cmStar; HSpace D.host.E) : ℕ :=
  letI := D.host.cmStar; (S.sig (DV.tauEmb D (D.eTau.symm 1))).1

def recJ (S : letI := D.host.cmStar; HSpace D.host.E) : ℕ :=
  if 1 ≤ firstSignatureEntry D S ∧ firstSignatureEntry D S < recN D S then firstSignatureEntry D S else 1

theorem two_le_recN (S) : 2 ≤ recN D S := by unfold recN; split_ifs <;> omega
theorem recJ_pos (S) : 1 ≤ recJ D S := by unfold recJ; split_ifs with h; exacts [h.1, le_rfl]
theorem recJ_lt (S) : recJ D S < recN D S := by
  unfold recJ; split_ifs with h; exacts [h.2, two_le_recN D S]

theorem recN_dat {Lev : Type} (w : Dat D Lev) : recN D w.S = w.N := by
  unfold recN; rw [if_pos w.two_le]; rfl

theorem recJ_dat {Lev : Type} (w : Dat D Lev) (h : w.Indef) : recJ D w.S = w.j := by
  have e : firstSignatureEntry D w.S = w.j := by unfold firstSignatureEntry; rw [w.hsig]
  unfold recJ; rw [e, recN_dat, if_pos (show 1 ≤ w.j ∧ w.j < w.N from h)]

variable (X0 : DivX D)

def compatibleDivisorData : DivX D :=
  { X0 with
    geo := geoDegenerateNoTau D.what₂.LL
    Lev := Unit
    levPr := fun _ => Finset.univ.image D.host.g
    shv := fun S _ => shimXJunk D jC (recN D S) (recJ D S) (recJ_pos D S) (recJ_lt D S)
    shv_N := fun S _ h => by show recN D S = _; unfold recN; rw [if_pos h]
    shv_lev := fun _ _ => rfl
    PlP := fun p _ => PlL D p
    plpFin := fun p _ => finPl D p
    plpNe := fun p _ => plL_ne D p
    wtP := fun p _ => wtL D p
    divisorWeight_nonneg := fun p _ => wtL_nonneg D p
    divisorWeight_sum := fun p _ => wtL_sum D p
    plP := fun p _ => Formalism.BasicNotions.Examples₂.PlOver.plLEquiv D p
    divisorWeight_def := fun p _ la => Formalism.BasicNotions.Examples₂.PlOver.wtLog_eq D p la
    jC := fun p _ => jC p
    Mp := fun _ _ _ _ _ => PUnit
    md := fun S _ p _ la _ => mdlJunk D p (jC p la) (recN D S) (recJ D S) (recJ_lt D S).le
    phiFr_unram := fun _ _ _ y => Empty.elim y
    CurveM := fun _ _ _ _ _ _ => Empty
    degM := fun _ _ _ _ _ _ c => Empty.elim c
    htMdl := fun _ _ _ _ _ => PUnit.unit
    htCurve := fun _ _ _ _ => Equiv.refl _
    htCurve_deg := fun _ _ _ _ c => Empty.elim c.2
    Comp := fun _ => PUnit
    compFin := fun _ => inferInstance
    degHH := fun _ _ _ => 0
    Yv := fun j _ => Formalism.DegreeFormula.dimFl D.what₂.Tau (datW D () j).N
    Ybd := fun _ _ => PUnit.unit
    Lw := fun _ _ => 0
    iMj := fun j _ => (0 : (X0.MjH j).V →ₗ[D.what₂.LL] D.what₂.LL)
    iMj_mem := fun _ _ _ => by
      show (0 : D.what₂.LL) ∈ (⊥ : Submodule D.what₂.LL D.what₂.LL)
      exact Submodule.zero_mem _ }

theorem md_heq (p : ℕ) [Fact p.Prime] (jc : DV.KW p →+* ℂ) {N j N' j' : ℕ} (h h') (hN : N = N') (hj : j = j') :
    HEq (fun _ : PUnit.{1} => mdlJunk D p jc N j h) (fun _ : PUnit.{1} => mdlJunk D p jc N' j' h') := by
  subst hN; subst hj; rfl

theorem prime_of_mem_image : ∀ (_ : Unit), ∀ p ∈ Finset.univ.image D.host.g, p.Prime := fun _ p hp => by
  obtain ⟨i, _, rfl⟩ := Finset.mem_image.1 hp
  exact D.host.g_prime i


end Tied

section TiedFl

variable (jC : ∀ (p : ℕ) [Fact p.Prime], PlL D p → (DV.KW p →+* ℂ))

def shimXFl (N j : ℕ) (h1 : 1 ≤ j) (h2 : j < N) : DV.ShimX D.what₂.Tau where
  N := N
  j := j
  j_pos := h1
  j_lt := h2
  lev := Finset.univ.image D.host.g
  lev_prime := fun p hp => by
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.1 hp
    exact D.host.g_prime i
  Comp := PUnit
  vol := (cxJunk D.what₂.Tau N j).vol
  chern := (cxJunk D.what₂.Tau N j).chern
  chern_homog := fun P d hd hP => chernOf_homog D.what₂.Tau N (cxJunk D.what₂.Tau N j).vol P d hd hP
  arDeg := (padDegenerate D N j h2.le jC).arDeg
  arDeg_homog := (padDegenerate D N j h2.le jC).arDeg_homog
  arMix := (padDegenerate D N j h2.le jC).arMix
  arMix_HT := (padDegenerate D N j h2.le jC).arMix_HT
  arMix_DR := (padDegenerate D N j h2.le jC).arMix_DR
  CurveHT := (padDegenerate D N j h2.le jC).CurveHT
  degHT := (padDegenerate D N j h2.le jC).degHT
  CurveDR := (padDegenerate D N j h2.le jC).CurveDR
  degDR := (padDegenerate D N j h2.le jC).degDR
  FibComp := (padDegenerate D N j h2.le jC).FibComp
  fibInBd := (padDegenerate D N j h2.le jC).fibInBd
  Pt := (padDegenerate D N j h2.le jC).Pt
  phiDR := (padDegenerate D N j h2.le jC).phiDR
  phiMod := (padDegenerate D N j h2.le jC).phiMod
  phiFr := (padDegenerate D N j h2.le jC).phiFr
  XC := (cxJunk D.what₂.Tau N j).XC
  rfn := (cxJunk D.what₂.Tau N j).rfn
  rfn_ge := (cxJunk D.what₂.Tau N j).rfn_ge
  hLo := (cxJunk D.what₂.Tau N j).hLo
  hUp := (cxJunk D.what₂.Tau N j).hUp
  hLo_le := (cxJunk D.what₂.Tau N j).hLo_le
  connN := (cxJunk D.what₂.Tau N j).connN
  curvN := (cxJunk D.what₂.Tau N j).curvN
  compOf := (cxJunk D.what₂.Tau N j).compOf
  normDetInf := (cxJunk D.what₂.Tau N j).normDetInf
  compPt := (padDegenerate D N j h2.le jC).compPt
  normDetT := (padDegenerate D N j h2.le jC).normDetT
  normDetH := (padDegenerate D N j h2.le jC).normDetH
  htDetT := (padDegenerate D N j h2.le jC).htDetT
  ALB := (algDegenerate D N).ALB
  arSelf := fun L => ∑ c, (algDegenerate D N).arSelfC L c
  arSelfC := (algDegenerate D N).arSelfC
  arSelf_sum := fun _ => rfl
  geo := fun L => ∑ c, (algDegenerate D N).geoC L c
  geoC := (algDegenerate D N).geoC
  geo_sum := fun _ => rfl
  arVol := (algDegenerate D N).arVol
  semipos := (algDegenerate D N).semipos
  nefFib := (algDegenerate D N).nefFib
  arNef := (algDegenerate D N).arNef
  Mbar := (algDegenerate D N).Mbar

theorem shimXFl_congr {N j N' j' : ℕ} (h1 h2 h1' h2') (hN : N = N') (hj : j = j') :
    shimXFl D jC N j h1 h2 = shimXFl D jC N' j' h1' h2' := by
  subst hN; subst hj; rfl

theorem toShimX_fl {Lev : Type} (w : Dat D Lev) (h : w.Indef) (hl) :
    toShimX (shimUFl D jC w) h (Finset.univ.image D.host.g) hl = shimXFl D jC w.N w.j h.1 h.2 := rfl

def lwFl (j : ℕ) : (D.what₂.Tau → Fin D.R.r → ℤ) →+ (D.what₂.Tau → Fin (datW D () j).N → ℤ) where
  toFun la := fun τ i => la τ (Fin.cast (datW_N D () j) i)
  map_zero' := rfl
  map_add' _ _ := rfl

variable (X0 : DivX D)

def divXFl : DivX D :=
  { X0 with
    geo := geoDegenerate D.what₂.LL D.what₂.Tau
    Lev := Unit
    levPr := fun _ => Finset.univ.image D.host.g
    shv := fun S _ => shimXFl D jC (recN D S) (recJ D S) (recJ_pos D S) (recJ_lt D S)
    shv_N := fun S _ h => by show recN D S = _; unfold recN; rw [if_pos h]
    shv_lev := fun _ _ => rfl
    PlP := fun p _ => PlL D p
    plpFin := fun p _ => finPl D p
    plpNe := fun p _ => plL_ne D p
    wtP := fun p _ => wtL D p
    divisorWeight_nonneg := fun p _ => wtL_nonneg D p
    divisorWeight_sum := fun p _ => wtL_sum D p
    plP := fun p _ => Formalism.BasicNotions.Examples₂.PlOver.plLEquiv D p
    divisorWeight_def := fun p _ la => Formalism.BasicNotions.Examples₂.PlOver.wtLog_eq D p la
    jC := fun p _ => jC p
    Mp := fun _ _ _ _ _ => PUnit
    md := fun S _ p _ la _ => mdlJunk D p (jC p la) (recN D S) (recJ D S) (recJ_lt D S).le
    phiFr_unram := fun _ _ _ _ _ _ => rfl
    CurveM := fun _ _ _ _ _ _ => PUnit
    degM := fun _ _ _ _ _ _ _ _ => 0
    htMdl := fun _ _ _ _ _ => PUnit.unit
    htCurve := fun _ _ _ _ => Equiv.refl _
    htCurve_deg := fun _ _ _ _ _ => rfl
    Comp := fun _ => PUnit
    compFin := fun _ => inferInstance
    degHH := fun _ _ _ => 0
    Yv := fun j _ => (datW D () j).N
    Ybd := fun _ _ => PUnit.unit
    Lw := fun j _ => lwFl D j
    iMj := fun j _ => (0 : (X0.MjH j).V →ₗ[D.what₂.LL] D.what₂.LL)
    iMj_mem := fun _ _ _ => Submodule.mem_top }

theorem degMFl_heq {N N' : ℕ} (hN : N = N') :
    HEq (fun (_ : PUnit.{1}) (_ : PUnit.{1}) (_ : DV.Rt D.what₂.Tau N) => (0 : ℝ))
      (fun (_ : PUnit.{1}) (_ : PUnit.{1}) (_ : DV.Rt D.what₂.Tau N') => (0 : ℝ)) := by
  subst hN; rfl

theorem tiedX_fl : TiedX (jC := jC) (ng := ng1) (divXFl D jC X0) (fun _ => Finset.univ.image D.host.g)
    (prime_of_mem_image D) () (fun p _ => Equiv.refl _) (fun w => shimUFl D jC w) (fun _ _ _ => Equiv.refl _) :=
  { shv :=
      { lev := rfl
        shv := fun w h => (shimXFl_congr D jC _ _ _ _ (recN_dat D w) (recJ_dat D w h)).trans
          (toShimX_fl D jC w h _).symm }
    pl :=
      { wt := fun _ _ _ => rfl
        jc := fun _ _ _ => rfl
        mp := fun _ _ _ _ _ => rfl
        md := fun w h p _ la => md_heq D p (jC p la) (recJ_lt D w.S).le w.j_le (recN_dat D w) (recJ_dat D w h)
        curveM := fun _ _ _ _ _ => HEq.rfl
        degM := fun w _ _ _ _ => degMFl_heq D (recN_dat D w)
        htMdl := fun _ _ _ _ _ => HEq.rfl
        htCurve := fun w h p _ c c' hc => by
          have e : c = c' := eq_of_heq hc
          subst e
          exact ⟨rfl, HEq.rfl⟩ }
    geo :=
      { yv := fun _ _ _ _ => rfl
        ybd := fun _ _ _ _ => HEq.rfl
        lw := fun _ _ _ _ _ => HEq.rfl }
    lev_κg := rfl }


end TiedFl

end Formalism.L2.Geo
