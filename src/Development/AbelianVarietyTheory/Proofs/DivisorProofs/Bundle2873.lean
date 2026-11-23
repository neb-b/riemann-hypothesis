module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2290
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2840
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0075
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2348
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2568
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2841
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1650
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1529
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1587
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.SelfDualLatticePairingDual
public import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.SelfDualCLatP
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.SqNormIntegralFundamentalDomainEqL2NormSq
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0060
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0071
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ToroidalCompactificationBis
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ValCalc

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TensorDataSymmetricPullbackAndPsiEqTau
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

noncomputable section

namespace GlobalTheory.TensPsi

theorem tensorData_symmetric_pullback_and_psi_eq_tau : ∀ (R : Type) [CommRing R] [IsDomain R] (I : Ideal R) (D D' : DegData R I) {r : ℕ} (W : Matrix (Fin r) (Fin r) ℤ) (T : Tens D.toPre D'.toPre W) (A₀ : Matrix (Fin r) (Fin r) ℤ) (O : Type) [CommRing O] [StarRing O] [Module O D'.toPre.X] (o : D'.toPre.OAct O) (w₀ : O), o.onB.act w₀ = GlobalTheory.TensAct.matAct T A₀ → (∀ y : D'.toPre.X, w₀ • y = GlobalTheory.TensAct.latAct T A₀ y) → W = (W + W.transpose) * A₀ → TraceFormTwistIso D'.toPre o w₀ := by
  intro R _ _ I D D' r W T A₀ O _ _ _ o w₀ hact hlat hW
  have := o.onB.hom w₀
  obtain ⟨t, ht, vt⟩ := _root_.GlobalTheory.MumSide.mside R I D D'.toPre W T A₀ (o.onB.act w₀) hact hW
  obtain ⟨u₀, hu₀, vu₀⟩ := _root_.GlobalTheory.TensGen.exists_gen_transfer R D.toPre D'.toPre W T
    (![(padd D'.toPre.P.A (𝟙 _) (o.onB.act w₀)).left, 𝟙 D'.toPre.P.A.left, (o.onB.act w₀).left,
      (toUnit D'.toPre.P.A ≫ η[D'.toPre.P.A]).left] : Fin 4 → (D'.toPre.P.A.left ⟶ D'.toPre.P.A.left))
    ![1, -2, -1, 2] t ht
  obtain ⟨u, hu, hv⟩ := exists_gen D'.toPre.P.isLB
    (φ' := (![(padd D'.toPre.P.A (𝟙 _) (o.onB.act w₀)).left, 𝟙 D'.toPre.P.A.left, (o.onB.act w₀).left,
      (toUnit D'.toPre.P.A ≫ η[D'.toPre.P.A]).left] : Fin 4 → _)) (ε' := ![1, -2, -1, 2])
    (fun V _ k => by
      refine Eq.trans (DVR.prod_sum₂ (K := Fin 4) (K' := Fin 4) (U := V) _ rfl
        (DVR.prod_neg _ _ (GlobalTheory.PsiWZeroPull.prod_four (o.onB.act w₀) (1 : D'.toPre.P.A ⟶ D'.toPre.P.A) k))) ?_
      rw [MonObj.one_comp, _root_.mul_one (1 : D'.toPre.P.A ⟶ D'.toPre.P.A)]
      refine mul_eq_left.2 (inv_eq_one.2 ?_)
      group)
    (LB.mulGen D'.toPre.P.L _ _ _ _ u₀ (LB.invGen D'.toPre.P.L _ _ (LB.pullGen D'.toPre.P.L _ _ u₀ (1 : D'.toPre.P.A ⟶ D'.toPre.P.A).left)))
    (DVR.mulGen_isGen _ _ _ _ _ _ _ hu₀ (DVR.invGen_isGen _ _ _ _ (DVR.pullGen_isGen _ _ _ _ hu₀ _)))
  refine ⟨u, hu, corr_of_val D'.toPre.P.isLB fun y J hJ => ?_, fun y => corr_of_val D'.toPre.P.isLB fun z J' hJ' => ?_⟩
  · have e : eSec D'.toPre.P.A ≫ (1 : D'.toPre.P.A ⟶ D'.toPre.P.A).left = eSec D'.toPre.P.A :=
      congrArg (fun q : 𝟙_ (Over _) ⟶ D'.toPre.P.A => q.left) ((MonObj.comp_one (M := D'.toPre.P.A) η[D'.toPre.P.A]).trans (by simp [Hom.one_def]))
    rw [val_pull hJ, val_one, hv _ _ y J hJ, val_mul hJ, val_inv, val_pull hJ, Category.assoc, e, mul_inv_cancel]

  · choose J hJ using fun ψ : (TK R).left ⟶ D.toPre.P.A.left => exists_chart D.toPre.P.isLB (ψ z)
    let ω : ((TK R).left ⟶ D'.toPre.P.A.left) → ((TK R).left.presheaf.stalk z)ˣ := fun ψ =>
      gm ψ z _ (T.w.s (fun k => J (ψ ≫ tensφ T.pr k), J' ψ))
    let Tv : D'.toPre.X → ((TK R).left.presheaf.stalk z)ˣ := fun v =>
      ∏ i, ∏ j, val (D.toPre.tau (T.xe v i) (T.xe v j)) (𝟙 _) z J ^ W i j
    have hψ : ∀ v, val (D'.toPre.psi v) (𝟙 _) z J' = ω (D'.toPre.xK v) * Tv v := fun v => T.psi v z J J' hJ hJ'
    have k0 : ∀ x : D'.toPre.X, D'.toPre.xK x ≫ (padd D'.toPre.P.A (𝟙 _) (o.onB.act w₀)).left =
        D'.toPre.xK (x + w₀ • x) := by
      intro x
      show ((toUnit (TK R) ≫ D'.toPre.c x) ≫ padd D'.toPre.P.A (𝟙 _) (o.onB.act w₀)).left =
        (toUnit (TK R) ≫ D'.toPre.c (x + w₀ • x)).left
      congr 1
      rw [D'.toPre.c_add, o.c_lin]
      simp only [padd, ← Category.assoc, comp_lift, Category.comp_id]
    have k2 : ∀ x : D'.toPre.X, D'.toPre.xK x ≫ (o.onB.act w₀).left = D'.toPre.xK (w₀ • x) := by
      intro x
      show ((toUnit (TK R) ≫ D'.toPre.c x) ≫ o.onB.act w₀).left = (toUnit (TK R) ≫ D'.toPre.c (w₀ • x)).left
      rw [o.c_lin, Category.assoc]
    have k3 : ∀ x : D'.toPre.X, D'.toPre.xK x ≫ (toUnit D'.toPre.P.A ≫ η[D'.toPre.P.A]).left = D'.toPre.xK 0 := by
      intro x
      have c0 : (toUnit (TK R) ≫ D'.toPre.c 0 : TK R ⟶ D'.toPre.P.A) = 1 := cPoint_zero (D := D'.toPre) (TK R)
      show ((toUnit (TK R) ≫ D'.toPre.c x) ≫ toUnit D'.toPre.P.A ≫ η[D'.toPre.P.A]).left = (toUnit (TK R) ≫ D'.toPre.c 0).left
      rw [c0, ← Category.assoc, toUnit_unique ((toUnit (TK R) ≫ D'.toPre.c x) ≫ toUnit D'.toPre.P.A) (toUnit (TK R))]
      simp [Hom.one_def]
    have k1 : ∀ x : D'.toPre.X, D'.toPre.xK x ≫ (1 : D'.toPre.P.A ⟶ D'.toPre.P.A).left = D'.toPre.xK 0 := by
      intro x
      have := k3 x
      rwa [← Hom.one_def] at this
    have F : ∀ x : D'.toPre.X, val u₀ (D'.toPre.xK x) z J' = (val (D'.toPre.psi (x + w₀ • x)) (𝟙 _) z J')⁻¹ *
        val (D'.toPre.psi x) (𝟙 _) z J' ^ (2 : ℤ) * val (D'.toPre.psi (w₀ • x)) (𝟙 _) z J' *
        (val (D'.toPre.psi 0) (𝟙 _) z J') ^ (-2 : ℤ) := by
      intro x
      have e1 : ω (D'.toPre.xK (x + w₀ • x)) ^ (1 : ℤ) * ω (D'.toPre.xK x) ^ (-2 : ℤ) *
          ω (D'.toPre.xK (w₀ • x)) ^ (-1 : ℤ) * ω (D'.toPre.xK 0) ^ (2 : ℤ) * val u₀ (D'.toPre.xK x) z J' =
          val t (D'.toPre.xK x) z J := by
        have h₀ := vu₀ _ (D'.toPre.xK x) z J J' hJ hJ'
        have h₁ : (∏ a : Fin 4, ω (D'.toPre.xK x ≫ (![(padd D'.toPre.P.A (𝟙 _) (o.onB.act w₀)).left, 𝟙 D'.toPre.P.A.left,
            (o.onB.act w₀).left, (toUnit D'.toPre.P.A ≫ η[D'.toPre.P.A]).left] : Fin 4 → (D'.toPre.P.A.left ⟶ D'.toPre.P.A.left)) a) ^
            (![1, -2, -1, 2] : Fin 4 → ℤ) a) * val u₀ (D'.toPre.xK x) z J' = val t (D'.toPre.xK x) z J := h₀
        rw [Fin.prod_univ_four] at h₁
        simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons, Matrix.cons_val, neg_neg, Category.comp_id] at h₁
        rw [k0, k2, k3] at h₁
        exact h₁
      have e2 : val t (D'.toPre.xK x) z J = Tv (x + w₀ • x) ^ (-1 : ℤ) * Tv x ^ (2 : ℤ) * Tv (w₀ • x) ^ (1 : ℤ) *
          Tv 0 ^ (-2 : ℤ) := by
        have h₀ := vt x z J hJ
        rw [Fin.prod_univ_four] at h₀
        simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons, Matrix.cons_val, neg_neg] at h₀
        simp only [Tv, hlat]
        exact h₀
      rw [hψ, hψ, hψ, hψ]
      rw [e2] at e1
      apply Additive.ofMul.injective
      have e' := congrArg Additive.ofMul e1
      simp only [ofMul_mul, ofMul_inv, ofMul_zpow] at e' ⊢
      linear_combination (norm := abel) e'
    have hu_y : ∀ x, val u (D'.toPre.xK x) z J' = val u₀ (D'.toPre.xK x) z J' * (val u₀ (D'.toPre.xK 0) z J')⁻¹ := by
      intro x
      rw [hv _ _ z J' hJ', val_mul hJ', val_inv, val_pull hJ', k1]
    have tau_e : ∀ a b : D'.toPre.X, val (D'.toPre.tau a b) (𝟙 _) z J' = val (D'.toPre.psi (a + b)) (𝟙 _) z J' *
        (val (D'.toPre.psi a) (𝟙 _) z J')⁻¹ * (val (D'.toPre.psi b) (𝟙 _) z J')⁻¹ * (val D'.toPre.rigK (𝟙 _) z J')⁻¹ :=
      fun a b => (val_mul hJ' _ _ _).trans (congrArg₂ (· * ·) ((val_mul hJ' _ _ _).trans (congrArg₂ (· * ·)
        ((val_mul hJ' _ _ _).trans (congrArg₂ (· * ·) rfl (val_inv _ _))) (val_inv _ _))) (val_inv _ _))
    have p0 := GlobalTheory.PsiInPow.val_psi_zero D'.toPre D'.tau_bimult hJ'
    have f0 := F 0
    rw [smul_zero, add_zero] at f0
    rw [val_mul hJ', val_mul hJ', val_pull hJ', Category.id_comp, hu_y, F y, f0, tau_e, p0]
    apply Additive.ofMul.injective
    simp only [ofMul_mul, ofMul_inv, ofMul_zpow]
    abel

end GlobalTheory.TensPsi
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaCosetIndicatorReadingNormSqEqVacuum
section
open NumberField MeasureTheory IsDedekindDomain UniqueFactorizationMonoid
open scoped Classical Pointwise
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links
open GlobalTheory.NormSum (Pair Tup minorPol ratG intG Cls gam)
open GlobalTheory.NormDict GlobalTheory.NormExact GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum
open GlobalTheory.SqTop (modT)
open GlobalTheory.BottomIPData (sfB)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (FinPl Lat IsFockVec IsSphOff volQ)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (ip)
open GlobalTheory.Core.Rk.IP (openOff integrand wcoef)
open GlobalTheory.StdLoc (glVol blockIdx)

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.NormRatio

namespace GlobalTheory.NormRatio.CosetNorm

open Formalism.MainNotions.TaylorLogMetric (VC tor0 La Iop U al YYl embV)
open Formalism.MainNotions.StandardLatticesGL3 (stdL pt La0 Wd wdPh Crv)

variable {D : D7} {ψ : AddChar (AF D.host.F) ℂ} {S T : HSp D}

theorem heisO_comm (x y : WO S T) (f : WO S T → ℂ) :
    heisO ψ S T x (heisO ψ S T y f) = ψ (symplO S T x y) • heisO ψ S T y (heisO ψ S T x f) := by
  have e : symplO S T x y + symplOH S T y x = symplOH S T x y := by
    have h2 : algebraMap D.host.F (AF D.host.F) (1 / 2) * 2 = 1 := by
      rw [← map_ofNat (algebraMap D.host.F (AF D.host.F)) 2, ← map_mul]; norm_num
    unfold symplOH
    rw [GlobalTheory.OrientedHeis.symplO_skew x y]
    linear_combination (-symplO S T x y) * h2
  rw [GlobalTheory.OrientedHeis.heisO_heisO, GlobalTheory.OrientedHeis.heisO_heisO, smul_smul, ← AddChar.map_add_eq_mul, e, add_comm]

theorem heisO_smul (x : WO S T) (c : ℂ) (f : WO S T → ℂ) : heisO ψ S T x (c • f) = c • heisO ψ S T x f := by
  funext w
  simp only [heisO, Pi.smul_apply, smul_eq_mul]
  ring

theorem ip_heisO_eq_zero {ΛS : Lat S} {ΛT : Lat T} (hψ : IsStdChar D ψ (-1)) (hS : IsSelfDualC S ΛS) (hT : IsSelfDualC T ΛT)
    {f : WO S T → ℂ} (hf : IsThetaFunO ψ S T f) (hv : IsLatVac (heisO ψ S T) (latO S T ΛS ΛT fun _ => True) f)
    {μ : Measure (WO S T)} {𝓕 : Set (WO S T)} (hμ : IsCovolOne (ratL T S) μ 𝓕) {u u' : WO S T}
    (hu : u.map (infPart D) = 0) (hu' : u'.map (infPart D) = 0) (hn : u - u' ∉ latO S T ΛS ΛT fun _ => True) :
    GlobalTheory.Ker.ipO μ 𝓕 (heisO ψ S T u f) (heisO ψ S T u' f) = 0 := by
  obtain ⟨h1, -, h3⟩ := GlobalTheory.LatVac.latO_selfDual_approx_sign D ψ S T ΛS ΛT hψ hS hT
  have h0 : (u - u').map (infPart D) = 0 := by
    funext i j
    have a : infPart D (u i j) = 0 := congrFun (congrFun hu i) j
    have b : infPart D (u' i j) = 0 := congrFun (congrFun hu' i) j
    show infPart D (u i j - u' i j) = 0
    rw [RingHom.map_sub, a, b, sub_self]
  rw [h1 _ h0] at hn
  push_neg at hn
  obtain ⟨l, hl, hne⟩ := hn
  obtain ⟨ε, hε, hεf⟩ := h3 f hv l hl
  have t1 := GlobalTheory.FinTranslate.isThetaFunO_heisO hψ.1.1 hψ.1.2.1 hf hu
  have t2 := GlobalTheory.FinTranslate.isThetaFunO_heisO hψ.1.1 hψ.1.2.1 hf hu'
  have e := GlobalTheory.Size.ipO_heisO hψ hμ.1 hμ.2.1 t1 t2 l
  rw [heisO_comm l u, heisO_comm l u', hεf f hv, heisO_smul, heisO_smul, GlobalTheory.Size.ipO_smul_left, GlobalTheory.Size.ipO_smul_left,
    GlobalTheory.Size.ipO_smul_right, GlobalTheory.Size.ipO_smul_right] at e
  have hεε : ε * starRingEnd ℂ ε = 1 := by rcases hε with rfl | rfl <;> simp
  have n1 := GlobalTheory.HeisOrtho.mul_conj_of_norm_one (hψ.1.2.1 (symplO S T l u'))
  have e2 : ψ (symplO S T (u - u') l) * ψ (symplO S T l u) = ψ (symplO S T l u') := by
    rw [← AddChar.map_add_eq_mul, GlobalTheory.OrientedHeis.symplO_skew u l, GlobalTheory.OrientedHeis.symplO_skew u' l]
    congr 1
    have : symplO S T (u - u' + u') l = symplO S T (u - u') l + symplO S T u' l := by
      unfold symplO hO
      simp only [Matrix.add_apply, mul_add, Finset.sum_add_distrib, map_add (f := _)]
    rw [sub_add_cancel] at this
    linear_combination -this
  refine (mul_eq_zero.1 (?_ : (ψ (symplO S T (u - u') l) - 1) * _ = 0)).resolve_left (sub_ne_zero.2 hne)
  set I := GlobalTheory.Ker.ipO μ 𝓕 (heisO ψ S T u f) (heisO ψ S T u' f)
  set A := ψ (symplO S T (u - u') l)
  set B := ψ (symplO S T l u)
  set C := ψ (symplO S T l u')
  linear_combination (-A) * e + (ε * starRingEnd ℂ C * starRingEnd ℂ ε * I) * e2 +
    (C * starRingEnd ℂ C * I) * hεε + I * n1

theorem ip_sum (hψ : IsStdChar D ψ (-1)) {μ : Measure (WO S T)} {𝓕 : Set (WO S T)} (hμ : IsCovolOne (ratL T S) μ 𝓕)
    {ι : Type} (s : Finset ι) (a : ι → ℂ) (h : ι → WO S T → ℂ) (c : ℂ) (ht : ∀ i, IsThetaFunO ψ S T (h i))
    (ha : ∀ i, a i * starRingEnd ℂ (a i) = 1)
    (ho : ∀ i j, i ≠ j → GlobalTheory.Ker.ipO μ 𝓕 (h i) (h j) = 0) (hc : ∀ i, GlobalTheory.Ker.ipO μ 𝓕 (h i) (h i) = c) :
    GlobalTheory.Ker.ipO μ 𝓕 (∑ i ∈ s, a i • h i) (∑ i ∈ s, a i • h i) = s.card * c := by
  have e : ∀ w, (∑ i ∈ s, a i • h i) w * starRingEnd ℂ ((∑ i ∈ s, a i • h i) w) =
      ∑ i ∈ s, ∑ j ∈ s, (a i * starRingEnd ℂ (a j)) * (h i w * starRingEnd ℂ (h j w)) := fun w => by
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, map_sum, map_mul, Finset.sum_mul_sum]
    exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring
  have hi : ∀ i j, Integrable (fun w => (a i * starRingEnd ℂ (a j)) * (h i w * starRingEnd ℂ (h j w))) (μ.restrict 𝓕) :=
    fun i j => Integrable.const_mul (GlobalTheory.Size.integrableOn_mul_conj hψ hμ.1 hμ.2.1 (ht i) (ht j)) _
  have e2 : GlobalTheory.Ker.ipO μ 𝓕 (∑ i ∈ s, a i • h i) (∑ i ∈ s, a i • h i) =
      ∑ i ∈ s, ∑ j ∈ s, (a i * starRingEnd ℂ (a j)) * GlobalTheory.Ker.ipO μ 𝓕 (h i) (h j) := by
    unfold GlobalTheory.Ker.ipO
    simp only [e]
    rw [integral_finsetSum _ fun i _ => integrable_finsetSum _ fun j _ => hi i j]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [integral_finsetSum _ fun j _ => hi i j]
    exact Finset.sum_congr rfl fun j _ => integral_const_mul _ _
  rw [e2, ← nsmul_eq_mul, ← Finset.sum_const]
  refine Finset.sum_congr rfl fun i hi => ?_
  rw [Finset.sum_eq_single_of_mem i hi fun j _ hj => by rw [ho i j hj.symm, mul_zero], ha, hc, one_mul]

theorem selfDual_stdLat (hS : S.gram = 1) : IsSelfDualC S (stdLat S) := by
  convert GlobalTheory.Ker.Base.selfDualC_stdL hS using 1
  ext x
  rw [GlobalTheory.SW.Base.mem_stdL, stdLat, stdL, Submodule.mem_pi]
  refine forall_congr' fun i => ⟨fun h => ?_, fun h _ => ?_⟩
  · obtain ⟨b, hb⟩ := Submodule.mem_one.1 (h trivial)
    rw [← hb]
    exact b.2
  · exact Submodule.mem_one.2 ⟨⟨x i, h⟩, rfl⟩

theorem reads_sum {θ : InfFam D} {a d : ℕ} {hS : S.rank = a} {hT : T.rank = d} {cc : Ideal (𝓞 D.host.K)} {δ : ℂ} {r : D.host.E}
    {ι : Type} (s : Finset ι) {G : ι → VC D a d → ℂ} {f : ι → WO S T → ℂ} (h : ∀ i, Reads ψ θ hS hT cc δ r (G i) (f i)) :
    Reads ψ θ hS hT cc δ r (∑ i ∈ s, G i) (∑ i ∈ s, f i) := by
  induction s using Finset.induction_on with
  | empty => exact ⟨(GlobalTheory.FinWeilO.thetaSub ψ S T).zero_mem, fun w _ => by simp⟩
  | insert i s hi ih => rw [Finset.sum_insert hi, Finset.sum_insert hi]; exact (h i).add ih

theorem finPt_sub {a d : ℕ} (hS : S.rank = a) (hT : T.rank = d) (r : D.host.E) (z z' : Matrix (Fin d) (Fin a) D.host.E) :
    finPt hS hT r (z - z') = finPt hS hT r z - finPt hS hT r z' := by
  unfold finPt
  rw [← AddMonoidHom.map_sub]
  congr 1
  ext i j
  simp only [Matrix.of_apply, Matrix.sub_apply]
  ring_nf

theorem pt_sub_mem {a d : ℕ} (δ : ℂ) {z z' : Matrix (Fin d) (Fin a) D.host.E} (h : z - z' ∈ YYl D (stdL D a) (stdL D d)) :
    pt D (tor0 D ⊤ δ) δ z - pt D (tor0 D ⊤ δ) δ z' ∈ La0 D (tor0 D ⊤ δ) a d := by
  refine AddSubgroup.subset_closure ⟨δ, AddSubgroup.subset_closure ⟨1, trivial, by simp⟩, _, h, ?_⟩
  funext τ i j
  simp only [pt, embV, tor0, Pi.sub_apply, Pi.smul_apply, Matrix.sub_apply, smul_eq_mul, map_sub]
  ring


set_option maxHeartbeats 1000000 in
theorem ip_cosetVec : ∀ {D : D7} {δ t0 : ℂ} {Q : ℕ} (P : Pair D ⊤ δ t0 Q) (X : Data P) (r : D.host.E), IsExact P X r →
  ∀ (𝔪 : Ideal (𝓞 D.host.E)) (Sf : Finset (FinPl D)) (o : ℕ), GoodMod D 𝔪 Sf →
  ∀ LB : Lat X.B, IsSelfDualC X.B LB →
    (∀ z : Matrix (Fin P.d) (Fin P.a) D.host.E, z ∈ Formalism.MainNotions.TaylorLogMetric.YYl D (Formalism.MainNotions.StandardLatticesGL3.stdL D P.a) (Formalism.MainNotions.StandardLatticesGL3.stdL D P.d) ↔
      finPt X.rkA X.rkB r z ∈ latO X.A X.B (stdLat X.A) LB fun _ => True) →
  ∀ f₀ φ, Reads X.ψ X.θ X.rkA X.rkB ⊤ δ r P.e0 f₀ → IsSphOff X.ψ X.A X.B (stdLat X.A) LB ∅ f₀ →
    Reads X.ψ X.θ X.rkA X.rkB ⊤ δ r (cosetVec P 𝔪 o) φ →
  ∀ (ν : Measure (WO X.A X.B)) (𝓕 : Set (WO X.A X.B)), IsCovolOne (ratL X.B X.A) ν 𝓕 →
    ip X.A X.B ν 𝓕 φ φ = ((Ideal.absNorm 𝔪 : ℂ) ^ (P.a * P.d))⁻¹ * ip X.A X.B ν 𝓕 f₀ f₀ := by
  intro D δ t0 Q P X r hX 𝔪 Sf o hG LB hLB hY f₀ φ hf₀ hsph hφ ν 𝓕 hcov
  have hset := hX.setup
  have hψ := hset.std
  have hN0 : 0 < Ideal.absNorm 𝔪 := Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.2 hG.1)
  have hidx := GlobalTheory.SkewIndex.index_inter_skew D δ P.crv 𝔪 hG.1 (Ideal.isCoprime_iff_sup_eq.2 hG.2.1) P.a P.d
  have hpts := fun y hy => GlobalTheory.FunObj.StdDatum.SkewPoints.points D δ P.crv 𝔪 hG.1 (a := P.a) (d := P.d) y hy
  unfold cosetVec at hφ
  generalize La D (tor0 D ⊤ δ) (stdL D P.a) (skewLat D 𝔪 P.d) = L at hidx hpts hφ
  have hne : ((La0 D (tor0 D ⊤ δ) P.a P.d).addSubgroupOf L).index ≠ 0 := by rw [hidx]; positivity
  haveI : Finite (L ⧸ (La0 D (tor0 D ⊤ δ) P.a P.d).addSubgroupOf L) := AddSubgroup.index_ne_zero_iff_finite.1 hne
  letI : Fintype (L ⧸ (La0 D (tor0 D ⊤ δ) P.a P.d).addSubgroupOf L) := Fintype.ofFinite _
  choose z hz _ using fun q : L ⧸ (La0 D (tor0 D ⊤ δ) P.a P.d).addSubgroupOf L => hpts _ (Quotient.out q).2
  have hlv : IsLatVac (heisO X.ψ X.A X.B) (latO X.A X.B (stdLat X.A) LB fun _ => True) f₀ := by
    have e : (fun v : FinPl D => v ∉ (∅ : Finset (FinPl D))) = fun _ => True := by funext v; simp
    rw [← e]
    exact hsph
  have hfin : ∀ y, (finPt X.rkA X.rkB r y).map (infPart D) = 0 := fun y => GlobalTheory.VacUnique.finRat_inf _ _ _
  have hrd := GlobalTheory.NormExact.heisO_finPt_reads X.ψ X.θ X.A X.B X.rkA X.rkB ⊤ δ r hset
  set n := ((La0 D (tor0 D ⊤ δ) P.a P.d).addSubgroupOf L).index with hn
  have eI : Iop D (tor0 D ⊤ δ) (La0 D (tor0 D ⊤ δ) P.a P.d) L P.e0 = ((Real.sqrt (n : ℝ) : ℂ))⁻¹ •
      ∑ q, al D (tor0 D ⊤ δ) (pt D (tor0 D ⊤ δ) δ (z q)) • U D (tor0 D ⊤ δ) (pt D (tor0 D ⊤ δ) δ (z q)) P.e0 := by
    funext y
    simp only [Iop, finsum_eq_sum_of_fintype, Pi.smul_apply, Finset.sum_apply, smul_eq_mul, hz, ← hn]
  have hg := reads_sum Finset.univ fun q => (hrd _ _ hf₀ (z q)).smul (al D (tor0 D ⊤ δ) (pt D (tor0 D ⊤ δ) δ (z q)))
  have hg2 := hg.smul ((Real.sqrt (n : ℝ) : ℂ))⁻¹
  rw [← eI] at hg2
  have hw := ((hrd _ _ hg2 (unitBlock D o P.a P.d)).smul
    (wdPh D (tor0 D ⊤ δ) (pt D (tor0 D ⊤ δ) δ (unitBlock D o P.a P.d)))).smul
    ((Real.sqrt ((Ideal.absNorm 𝔪 : ℝ) ^ (P.a * P.d)) : ℂ))⁻¹
  have hsum := ip_sum hψ hcov Finset.univ (fun q => al D (tor0 D ⊤ δ) (pt D (tor0 D ⊤ δ) δ (z q)))
    (fun q => heisO X.ψ X.A X.B (finPt X.rkA X.rkB r (z q)) f₀) (GlobalTheory.Ker.ipO ν 𝓕 f₀ f₀) (fun q => (hrd _ _ hf₀ (z q)).1)
    (fun q => by
      rw [al, map_zpow₀, ← mul_zpow]
      simp)
    (fun q q' hq => ip_heisO_eq_zero hψ (selfDual_stdLat hset.gS) hLB hf₀.1 hlv hcov (hfin _) (hfin _) fun h => hq (by
      rw [← finPt_sub, ← hY] at h
      have h2 := pt_sub_mem δ h
      rw [← hz, ← hz] at h2
      rw [← QuotientAddGroup.out_eq' q, ← QuotientAddGroup.out_eq' q', eq_comm, QuotientAddGroup.eq,
        AddSubgroup.mem_addSubgroupOf, neg_add_eq_sub]
      exact h2))
    fun q => GlobalTheory.Size.ipO_heisO hψ hcov.1 hcov.2.1 hf₀.1 hf₀.1 _
  have hph : ∀ x : VC D P.a P.d, wdPh D (tor0 D ⊤ δ) x * starRingEnd ℂ (wdPh D (tor0 D ⊤ δ) x) = 1 := fun x =>
    GlobalTheory.HeisOrtho.mul_conj_of_norm_one (by simp [wdPh, Formalism.MainNotions.StandardLatticesGL3.ee, Complex.norm_exp])
  have hsq : ∀ t : ℝ, 0 ≤ t → ((Real.sqrt t : ℂ))⁻¹ * starRingEnd ℂ ((Real.sqrt t : ℂ))⁻¹ = (t : ℂ)⁻¹ := fun t ht => by
    rw [map_inv₀, Complex.conj_ofReal, ← mul_inv, ← Complex.ofReal_mul, Real.mul_self_sqrt ht]
  have e1 := hsq n (Nat.cast_nonneg n)
  have e2 := hsq ((Ideal.absNorm 𝔪 : ℝ) ^ (P.a * P.d)) (by positivity)
  have e3 := hph (pt D (tor0 D ⊤ δ) δ (unitBlock D o P.a P.d))
  have e4 : ((n : ℝ) : ℂ)⁻¹ * (n : ℂ) = 1 := by
    rw [Complex.ofReal_natCast]; exact inv_mul_cancel₀ (Nat.cast_ne_zero.2 hne)
  rw [Finset.card_univ, ← Nat.card_eq_fintype_card, ← AddSubgroup.index_eq_card, ← hn] at hsum
  have eW : ∀ (x : VC D P.a P.d) G, Wd D (tor0 D ⊤ δ) x G = wdPh D (tor0 D ⊤ δ) x • U D (tor0 D ⊤ δ) x G := fun _ _ => rfl
  rw [eW] at hφ
  rw [Reads.unique hφ hw]
  show GlobalTheory.Ker.ipO ν 𝓕 _ _ = _ * GlobalTheory.Ker.ipO ν 𝓕 f₀ f₀
  rw [GlobalTheory.Size.ipO_smul_left, GlobalTheory.Size.ipO_smul_right, GlobalTheory.Size.ipO_smul_left, GlobalTheory.Size.ipO_smul_right,
    GlobalTheory.Size.ipO_heisO hψ hcov.1 hcov.2.1 hg2.1 hg2.1, GlobalTheory.Size.ipO_smul_left, GlobalTheory.Size.ipO_smul_right, hsum,
    ← mul_assoc, e2, ← mul_assoc (wdPh _ _ _), e3, one_mul, ← mul_assoc _ (starRingEnd ℂ _), e1, ← mul_assoc _ (n : ℂ), e4, one_mul]
  push_cast
  rfl

end GlobalTheory.NormRatio.CosetNorm
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ToricChartDerivationBoundaryParamMemSpan
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

namespace GlobalTheory.ChartDerBd

theorem X_dvd_of_X_mul {σ K : Type} [Field K] {s t : σ} (hst : t ≠ s) {g : MvPowerSeries σ K}
    (h : MvPowerSeries.X s ∣ MvPowerSeries.X t * g) : MvPowerSeries.X s ∣ g := by
  classical
  rw [MvPowerSeries.X_dvd_iff] at h ⊢
  intro n hn
  have h1 := h (n + Finsupp.single t 1) (by simp [Finsupp.single_apply, hst, hn])
  rw [MvPowerSeries.X, MvPowerSeries.coeff_monomial_mul] at h1
  simpa using h1

theorem X_dvd_of_prod_mul {σ K : Type} [Field K] {Idx : Type} (f : Idx → σ) {s : σ}
    (S : Finset Idx) (hS : ∀ j ∈ S, f j ≠ s) {g : MvPowerSeries σ K}
    (h : MvPowerSeries.X s ∣ (∏ j ∈ S, MvPowerSeries.X (f j)) * g) : MvPowerSeries.X s ∣ g := by
  classical
  induction S using Finset.induction_on with
  | empty => simpa using h
  | insert a S ha ih =>
    rw [Finset.prod_insert ha, _root_.mul_assoc] at h
    exact ih (fun j hj => hS j (Finset.mem_insert_of_mem hj))
      (X_dvd_of_X_mul (hS a (Finset.mem_insert_self a S)) h)

theorem deriv_bdParam_mem_span : ∀ (A : Type) [CommRing A] (k : Type) [Field k] (m d : ℕ) (ψ : A →+* ChartRing k m d) (δ : Derivation ℤ A A) (D' : Derivation ℤ (ChartRing k m d) (ChartRing k m d)) (I : Ideal A), (∀ a ∈ I, δ a ∈ I) → (∀ a, D' (ψ a) = ψ (δ a)) → I.map ψ = Ideal.span {∏ i, bdParam k m d i} → ∀ i, D' (bdParam k m d i) ∈ Ideal.span {bdParam k m d i} := by
  classical
  intro A _ k _ m d ψ δ D' I hI hD hJ i

  have hpres : ∀ x ∈ I.map ψ, D' x ∈ I.map ψ := by
    intro x hx
    rw [Ideal.map] at hx
    induction hx using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨a, ha, rfl⟩ := hy
      rw [hD]
      exact Ideal.mem_map_of_mem ψ (hI a ha)
    | zero => simp
    | add x y _ _ hx hy => rw [map_add (f := _)]; exact Ideal.add_mem _ hx hy
    | smul r x hxm hx =>
      rw [smul_eq_mul, Derivation.leibniz, smul_eq_mul, smul_eq_mul]
      exact Ideal.add_mem _ (Ideal.mul_mem_left _ r hx)
        (Ideal.mul_mem_right _ _ (Ideal.span_le.2 (fun y hy => Ideal.subset_span hy) hxm))
  set t := bdParam k m d with ht
  have hP : t i * ∏ j ∈ Finset.univ.erase i, t j = ∏ j, t j := Finset.mul_prod_erase _ _ (Finset.mem_univ i)
  have hmem : D' (∏ j, t j) ∈ Ideal.span {∏ j, t j} := by
    rw [← hJ]; apply hpres; rw [hJ]; exact Ideal.subset_span rfl
  rw [Ideal.mem_span_singleton] at hmem ⊢
  rw [← hP, Derivation.leibniz, smul_eq_mul, smul_eq_mul] at hmem
  have h1 : t i ∣ t i * D' (∏ j ∈ Finset.univ.erase i, t j) + (∏ j ∈ Finset.univ.erase i, t j) * D' (t i) :=
    (dvd_mul_right (t i) _).trans hmem
  have h2 : t i ∣ (∏ j ∈ Finset.univ.erase i, t j) * D' (t i) :=
    (dvd_add_right (dvd_mul_right _ _)).1 h1
  exact X_dvd_of_prod_mul (fun j : Fin m => (Sum.inl j : Fin m ⊕ Fin d)) (Finset.univ.erase i)
    (fun j hj h => (Finset.ne_of_mem_erase hj) (Sum.inl_injective h)) h2

end GlobalTheory.ChartDerBd
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorusWeightScalarZeroCharacterEqOne
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

namespace GlobalTheory.Heat

theorem weight_scalar_zero_eq_one : ∀ {R : Type} [CommRing R] [IsDomain R] {Q : DegPre R} {O : Type} [CommRing O] [StarRing O] [Module O Q.X] {oa : Q.OAct O} (Y : Ray oa) (S : Type) [CommRing S] (φ : R →+* S) (x x' : Over.mk (spMap φ) ⟶ Y.H) (c : Q.X → Sˣ), x' ≫ Y.q = x ≫ Y.q → (∀ χ y J, Good Q.P.L y J → val ((Y.Φ _ x').s χ) (𝟙 _) y J = gm (𝟙 (Over.mk (spMap φ)).left) y ⊤ (unitOn (c χ)) * val ((Y.Φ _ x).s χ) (𝟙 _) y J) → c 0 = 1 := by
  intro R _ _ Q O _ _ _ oa Y S _ φ x x' c _ h
  have e : unitOn (c 0) = unitOn (1 : Sˣ) := by
    refine ReciprocityTheory.ChartRestriction.G.Geo.Tor.unit_ext (X := (Over.mk (spMap φ)).left) (V := ⊤) fun y _ => ?_
    choose J hJ using fun ψ : (Over.mk (spMap φ)).left ⟶ Q.P.A.left =>
      ReciprocityTheory.ChartRestriction.G.Geo.Tor.exists_chart Q.P.isLB (ψ y)
    have hG : Good Q.P.L y J := hJ
    have h0 := h 0 y J hG
    rw [val_corr hG (Y.Φ _ x').s_zero, val_corr hG (Y.Φ _ x).s_zero, val_one, _root_.mul_one] at h0
    have h1 : unitOn (1 : Sˣ) = 1 := map_one _
    exact h0.symm.trans ((congrArg (gm _ y ⊤) h1).trans (map_one _)).symm
  exact Units.ext ((ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (CommRingCat.of S)).inv).1
    (congrArg Units.val e))

end GlobalTheory.Heat
end

