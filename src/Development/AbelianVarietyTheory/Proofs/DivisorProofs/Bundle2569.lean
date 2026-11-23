module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.OfFactorE
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsProjOverWeierstrass
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
public import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissibleBaseOfCompleteDvr
public import Development.AbelianVarietyTheory.Proofs.CharacterTheory.Bundle0002
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TensorDataPsiMemMaximalIdealTendstoZero
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2278
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EvenCubicalTensorPosDefFormPositive
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0058
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0079
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0064
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2463
public import Development.AbelianVarietyTheory.Definitions.Divisors.DensConst
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0039
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsAmbOfIsArithVar
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0004
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2390
public import ReciprocityTheory.AnalyticForms.PotentialTheory.Bundle0003
public import ReciprocityTheory.AnalyticForms.PotentialTheory.Bundle0005
public import ReciprocityTheory.AnalyticForms.PotentialTheory.Bundle0006
public import ReciprocityTheory.AnalyticForms.PotentialTheory.Bundle0007
public import ReciprocityTheory.AnalyticForms.PotentialTheory.Bundle0008
public import ReciprocityTheory.AnalyticForms.PotentialTheory.Stokes
public import ReciprocityTheory.AnalyticForms.PotentialTheory.SNCAtlas
public import ReciprocityTheory.AnalyticForms.PotentialTheory.Bundle0002
public import ReciprocityTheory.AnalyticForms.PlurisubharmonicFunctions.Bundle0001
public import ReciprocityTheory.AnalyticForms.PotentialTheory.PLCurveA
public import ReciprocityTheory.AnalyticForms.PotentialTheory.PLLocalStatement
public import ReciprocityTheory.AnalyticForms.PotentialTheory.Pullback
public import ReciprocityTheory.AnalyticForms.PotentialTheory.AtlasIndep
public import ReciprocityTheory.AnalyticForms.PotentialTheory.DegreeInt
public import ReciprocityTheory.AnalyticForms.PotentialTheory.ContDiffFubiniStudyRatioCompChart0
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0922
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2318
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.TorusTorsionPointsCorrespondValues
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2478
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2398
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2399
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2397

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TensorDataScalarsMemMaximalIdealTendstoZero
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.TChart GlobalTheory.Mum
open GlobalTheory.Mum.TensPos GlobalTheory.PsiScalUnit GlobalTheory.Mum.TensPol

noncomputable section

namespace GlobalTheory.Mum.TensPolScal

theorem exists_bilin (R : Type) [CommRing R] (X : Type) [AddCommGroup X] [Module.Free ℤ X]
    (k : X → X → (FractionRing R)ˣ) (hs : ∀ a b, ∃ u ∈ unitsK R, k b a = u * k a b)
    (ha : ∀ a a' b, ∃ u ∈ unitsK R, k (a + a') b = u * (k a b * k a' b)) :
    ∃ B : X →ₗ[ℤ] X →ₗ[ℤ] Additive (FractionRing R)ˣ, ∀ a b, ∃ u ∈ unitsK R, k a b = u * (B a b).toMul := by
  set H := unitsK R
  have h1 : ∀ u ∈ H, (QuotientGroup.mk' H) u = 1 := fun u hu => (QuotientGroup.eq_one_iff u).2 hu
  let g : X → X → Additive ((FractionRing R)ˣ ⧸ H) := fun a b => Additive.ofMul (QuotientGroup.mk' H (k a b))
  have gs : ∀ a b, g b a = g a b := fun a b => by
    obtain ⟨u, hu, e⟩ := hs a b
    simp only [g, e, map_mul, h1 u hu, _root_.one_mul]
  have ga : ∀ a a' b, g (a + a') b = g a b + g a' b := fun a a' b => by
    obtain ⟨u, hu, e⟩ := ha a a' b
    simp only [g, e, map_mul, h1 u hu, _root_.one_mul, ofMul_mul]
  have gb : ∀ a b b', g a (b + b') = g a b + g a b' := fun a b b' => by
    rw [gs, ga, gs b, gs b']
  have gsa : ∀ (c : ℤ) a b, g (c • a) b = c • g a b := fun c a b =>
    map_zsmul (AddMonoidHom.mk' (fun a => g a b) (fun a a' => ga a a' b)) c a
  have gsb : ∀ (c : ℤ) a b, g a (c • b) = c • g a b := fun c a b => by
    rw [gs, gsa, gs]
  let F : X →ₗ[ℤ] X →ₗ[ℤ] Additive ((FractionRing R)ˣ ⧸ H) := LinearMap.mk₂ ℤ g ga gsa gb gsb
  let π : Additive (FractionRing R)ˣ →+ Additive ((FractionRing R)ˣ ⧸ H) := MonoidHom.toAdditive (QuotientGroup.mk' H)
  let bs := Module.Free.chooseBasis ℤ X
  let B : X →ₗ[ℤ] X →ₗ[ℤ] Additive (FractionRing R)ˣ :=
    bs.constr ℤ fun i => bs.constr ℤ fun j => Additive.ofMul (k (bs i) (bs j))
  have e : B.compr₂ π.toIntLinearMap = F := LinearMap.ext_basis bs bs fun i j => by
    simp [B, F, g, π]
  refine ⟨B, fun a b => ⟨k a b * ((B a b).toMul)⁻¹, ?_, by rw [inv_mul_cancel_right]⟩⟩
  have e1 : QuotientGroup.mk' H (B a b).toMul = QuotientGroup.mk' H (k a b) :=
    congrArg Additive.toMul (congrArg (fun C => C a b) e)
  rw [← QuotientGroup.eq_one_iff]
  show QuotientGroup.mk' H _ = 1
  rw [map_mul, map_inv, ← e1, mul_inv_cancel]

end GlobalTheory.Mum.TensPolScal

namespace GlobalTheory.Mum.TensPolScal

theorem scalars_tens : ∀ (R : Type) [CommRing R] [IsDomain R] [IsNoetherianRing R] [IsIntegrallyClosed R] [IsLocalRing R] (X : Type) [AddCommGroup X] [Module.Free ℤ X] [Module.Finite ℤ X] (k : X → X → (FractionRing R)ˣ), (∀ a b, ∃ u ∈ unitsK R, k b a = u * k a b) → (∀ a a' b, ∃ u ∈ unitsK R, k (a + a') b = u * (k a b * k a' b)) → (∀ y, y ≠ 0 → ∃ s ∈ maximalIdeal R, (k y y : FractionRing R) = algebraMap R _ s) → ∀ {r : ℕ} (W : Matrix (Fin r) (Fin r) ℤ), ((W + W.transpose).map (Int.cast : ℤ → ℝ)).PosDef → ∀ (a' : (Fin r → X) → (FractionRing R)ˣ), (∀ z, ∃ u ∈ unitsK R, a' z = u * ∏ i, ∏ j, k (z i) (z j) ^ W i j) → (∀ z, z ≠ 0 → ∃ s ∈ maximalIdeal R, (a' z : FractionRing R) = algebraMap R _ s) ∧ ∀ n : ℕ, {z | ¬ ∃ s ∈ maximalIdeal R ^ n, (a' z : FractionRing R) = algebraMap R _ s}.Finite := by
  intro R _ _ _ _ _ X _ _ _ k hs ha hp r W hW a' h'
  obtain ⟨B, hB⟩ := exists_bilin R X k hs ha
  choose u hu eu using hB
  let κ : X → (FractionRing R)ˣ := fun x => (B x x).toMul
  let κ' : (Fin r → X) → (FractionRing R)ˣ := fun z => ∏ i, ∏ j, (κ (z i + z j) * (κ (z i))⁻¹ * (κ (z j))⁻¹) ^ W i j
  let P : (Fin r → X) → (FractionRing R)ˣ := fun z => ∏ i, ∏ j, (B (z i) (z j)).toMul ^ W i j
  let Q : (Fin r → X) → (FractionRing R)ˣ := fun z => ∏ i, ∏ j, (B (z j) (z i)).toMul ^ W i j
  have eP : ∀ z, Additive.ofMul (P z) = ∑ i, ∑ j, W i j • B (z i) (z j) := fun z => by
    simp only [P, ofMul_prod, ofMul_zpow, ofMul_toMul]
  have eQ : ∀ z, Additive.ofMul (Q z) = ∑ i, ∑ j, W i j • B (z j) (z i) := fun z => by
    simp only [Q, ofMul_prod, ofMul_zpow, ofMul_toMul]
  have eκ' : ∀ z, κ' z = P z * Q z := by
    intro z
    apply Additive.ofMul.injective
    rw [ofMul_mul, eP, eQ, ← Finset.sum_add_distrib]
    simp only [κ', κ, ofMul_prod, ofMul_zpow, ofMul_mul, ofMul_inv, ofMul_toMul, map_add (f := _), LinearMap.add_apply]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [← smul_add]
    congr 1
    abel

  have hBs : ∀ a b, ∃ v ∈ unitsK R, (B b a).toMul = v * (B a b).toMul := by
    intro a b
    obtain ⟨w, hw, e⟩ := hs a b
    refine ⟨(u b a)⁻¹ * w * u a b, mul_mem (mul_mem (inv_mem (hu b a)) hw) (hu a b), ?_⟩
    rw [show (B b a).toMul = (u b a)⁻¹ * k b a by rw [eu b a, inv_mul_cancel_left], e, eu a b]
    group
  choose v hv ev using hBs
  have eQP : ∀ z, Q z = (∏ i, ∏ j, v (z i) (z j) ^ W i j) * P z := by
    intro z
    simp only [Q, P, ← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun i _ => Finset.prod_congr rfl fun j _ => ?_
    rw [ev (z i) (z j), mul_zpow]
  have κn : ∀ x, κ (-x) = κ x := fun x => by simp [κ]
  have κc : ∀ x y w, κ (x + y + w) * κ x * κ y * κ w = κ (x + y) * κ (x + w) * κ (y + w) := fun x y w => by
    apply Additive.ofMul.injective
    simp only [κ, ofMul_mul, ofMul_toMul, map_add (f := _), LinearMap.add_apply]
    abel
  have κp : ∀ x, x ≠ 0 → ∃ s ∈ maximalIdeal R, (κ x : FractionRing R) = algebraMap R _ s := fun x hx => by
    have := mem_of_unit _ ((unitsK R).inv_mem (hu x x)) (hp x hx)
    rwa [eu x x, inv_mul_cancel_left] at this
  have κ'p := GlobalTheory.Mum.TPos.tensor_pos R X κ κn κc κp W hW

  have Pp : ∀ z, z ≠ 0 → ∃ s ∈ maximalIdeal R, (P z : FractionRing R) = algebraMap R _ s := by
    intro z hz
    have hd : (∏ i, ∏ j, v (z i) (z j) ^ W i j) ∈ unitsK R :=
      prod_mem fun i _ => prod_mem fun j _ => zpow_mem (hv _ _) _
    have e2 : P z ^ 2 = (∏ i, ∏ j, v (z i) (z j) ^ W i j)⁻¹ * κ' z := by
      rw [eκ', eQP, mul_left_comm, inv_mul_cancel_left, pow_two]
    obtain ⟨s, hsm, es⟩ := mem_of_unit _ ((unitsK R).inv_mem hd) (κ'p z hz)
    rw [← e2, Units.val_pow_eq_pow_val] at es
    have hint : IsIntegral R ((P z : (FractionRing R)ˣ) : FractionRing R) :=
      IsIntegral.of_pow (by norm_num : 0 < 2) (es ▸ isIntegral_algebraMap)
    obtain ⟨t, ht⟩ := IsIntegrallyClosed.algebraMap_eq_of_integral hint
    have ht2 : t ^ 2 = s := by
      apply IsFractionRing.injective R (FractionRing R)
      rw [map_pow, ht, es]
    exact ⟨t, (maximalIdeal.isMaximal R).isPrime.mem_of_pow_mem 2 (ht2 ▸ hsm), ht.symm⟩
  have Pn : ∀ z, P (-z) = P z := fun z => by
    apply Additive.ofMul.injective
    simp [eP]
  have Pc : ∀ x y w, P (x + y + w) * P x * P y * P w = P (x + y) * P (x + w) * P (y + w) := fun x y w => by
    apply Additive.ofMul.injective
    simp only [ofMul_mul, eP, ← Finset.sum_add_distrib, ← smul_add, Pi.add_apply, map_add (f := _), LinearMap.add_apply]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => congrArg _ ?_
    abel
  have Pt := GlobalTheory.QuadTend.finite_not_mem_pow R (Fin r → X) P Pn Pc Pp
  have ea : ∀ z, ∃ v ∈ unitsK R, a' z = v * P z := fun z => by
    obtain ⟨w, hw, e⟩ := h' z
    refine ⟨w * ∏ i, ∏ j, u (z i) (z j) ^ W i j,
      mul_mem hw (prod_mem fun i _ => prod_mem fun j _ => zpow_mem (hu _ _) _), ?_⟩
    rw [e, _root_.mul_assoc]
    congr 1
    simp only [P, eu, mul_zpow, Finset.prod_mul_distrib]
  refine ⟨fun z hz => ?_, fun n => (Pt n).subset fun z hz hm => hz ?_⟩
  · obtain ⟨w, hw, e⟩ := ea z
    rw [e]; exact mem_of_unit _ hw (Pp z hz)
  · obtain ⟨w, hw, e⟩ := ea z
    rw [e]; exact mem_of_unit _ hw hm

end GlobalTheory.Mum.TensPolScal
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TensorProductSectionsZerosMultiplicitiesNorms
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Set Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.R
open GlobalTheory GlobalTheory.Cartier GlobalTheory.CxPts GlobalTheory.Points GlobalTheory.CechPic GlobalTheory.ChartGlue GlobalTheory.Mix
set_option autoImplicit false

noncomputable section

namespace GlobalTheory.Mix

theorem nonzeroLocus_prodSec {X : Scheme.{0}} {A B : LB X} (s : A.Sec) (t : B.Sec) :
    nonzeroLocus (EffBound.tensSec s t) = nonzeroLocus s ⊓ nonzeroLocus t := by
  have e (c : A.ι × B.ι) : X.basicOpen ((EffBound.tensSec s t).f c) =
      (A.U c.1 ⊓ B.U c.2) ⊓ X.basicOpen (s.f c.1) ⊓ ((A.U c.1 ⊓ B.U c.2) ⊓ X.basicOpen (t.f c.2)) :=
    (X.basicOpen_mul _ _).trans (congrArg₂ (· ⊓ ·) (X.basicOpen_res _ _) (X.basicOpen_res _ _))
  refine le_antisymm (iSup_le fun c => (e c).le.trans (inf_le_inf
    (inf_le_right.trans (le_iSup (fun i => X.basicOpen (s.f i)) c.1))
    (inf_le_right.trans (le_iSup (fun i => X.basicOpen (t.f i)) c.2)))) fun x hx => ?_
  obtain ⟨i, hi⟩ := Opens.mem_iSup.1 hx.1
  obtain ⟨j, hj⟩ := Opens.mem_iSup.1 hx.2
  have h : x ∈ A.U i ⊓ B.U j := ⟨X.basicOpen_le _ hi, X.basicOpen_le _ hj⟩
  exact Opens.mem_iSup.2 ⟨(i, j), (e (i, j)).ge ⟨⟨h, hi⟩, h, hj⟩⟩

theorem secVal_prodSec {k : Type} [CommRing k] {X : Scheme.{0}} (p : X ⟶ Sp k) (σ : k →+* ℂ) {A B : LB X}
    (s : A.Sec) (t : B.Sec) :
    secVal p σ (EffBound.tensSec s t) = secTens (secVal p σ s) (secVal p σ t) := by
  funext c y
  by_cases h : y ∈ ptsIn p σ (A.U c.1 ⊓ B.U c.2)
  · exact (ev_mul _ _ y).trans (congrArg₂ (· * ·) (ev_res inf_le_left h _) (ev_res inf_le_right h _))
  · exact (ev_of_notMem h _).trans ((secTens_mem (secVal_mem s) (secVal_mem t)).2 c y h).symm

theorem mult_prodSec {X : Scheme.{0}} [IsIntegral X] [IsLocallyNoetherian X] {A B : LB X} (hA : A.IsLB)
    (hB : B.IsLB) (hAB : (tens A B).IsLB) (s : A.Sec) (hs : genericPoint X ∈ nonzeroLocus s) (t : B.Sec)
    (ht : genericPoint X ∈ nonzeroLocus t) (h : genericPoint X ∈ nonzeroLocus (EffBound.tensSec s t)) (z : X) :
    (divOfSec hAB _ h).mult z = (divOfSec hA s hs).mult z + (divOfSec hB t ht).mult z := by
  obtain ⟨i, hi⟩ := Geo.Tor.exists_chart hA z
  obtain ⟨j, hj⟩ := Geo.Tor.exists_chart hB z
  have hij : z ∈ (tens A B).U (i, j) := ⟨hi, hj⟩
  rw [((presents_divOfRatSec hAB _).isEqn (i, j) z hij).mult_eq,
    ((presents_divOfRatSec hA _).isEqn i z hi).mult_eq, ((presents_divOfRatSec hB _).isEqn j z hj).mult_eq,
    val_ratOfSec (gen_mem hij), val_ratOfSec (gen_mem hi), val_ratOfSec (gen_mem hj),
    ← Scheme.ord_mul (fnOf_sec_ne_zero hs (gen_mem hi)) (fnOf_sec_ne_zero ht (gen_mem hj))]
  exact congrArg (Scheme.ord · z) ((map_mul _ _ _).trans
    (congrArg₂ (· * ·) (fnOf_resG inf_le_left _ _) (fnOf_resG inf_le_right _ _)))

theorem exists_sec_tens : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] [IsLocallyNoetherian X] (p : X ⟶ Sp k) (σ : k →+* ℂ) (M A : MLine p σ) (s : M.B.Sec) (hs : genericPoint X ∈ nonzeroLocus s) (a : A.B.Sec) (ha : genericPoint X ∈ nonzeroLocus a), ∃ (s₁ : (M.tens A).B.Sec) (h₁ : genericPoint X ∈ nonzeroLocus s₁), nonzeroLocus s₁ = nonzeroLocus s ⊓ nonzeroLocus a ∧ (∀ z, (divOfSec (M.tens A).φ.isLB s₁ h₁).mult z = (divOfSec M.φ.isLB s hs).mult z + (divOfSec A.φ.isLB a ha).mult z) ∧ ∀ y ∈ ptsIn p σ (nonzeroLocus s₁), (M.tens A).logSec s₁ y = M.logSec s y + A.logSec a y := by
  intro k _ X _ _ p σ M A s hs a ha
  have e := nonzeroLocus_prodSec s a
  refine ⟨EffBound.tensSec s a, e.ge ⟨hs, ha⟩, e, mult_prodSec _ _ _ s hs a ha _, fun y hy => ?_⟩
  have hy' : y ∈ ptsIn p σ (nonzeroLocus s ⊓ nonzeroLocus a) := ptsIn_mono e.le hy
  have h0 (N : MLine p σ) (u : N.B.Sec) (hu : y ∈ ptsIn p σ (nonzeroLocus u)) : N.φ.nsq (secVal p σ u) y ≠ 0 :=
    mul_ne_zero (pow_ne_zero _ (norm_ne_zero_iff.2 ((secVal_ne_zero_iff u (mem_pick _ y)).2 hu)))
      (Real.exp_ne_zero _)
  have h : (M.φ.tens A.φ).nsq (secVal p σ (EffBound.tensSec s a)) y =
      M.φ.nsq (secVal p σ s) y * A.φ.nsq (secVal p σ a) y := by
    rw [secVal_prodSec]
    exact Weight.nsq_tens _ _ (secVal_mem s) (secVal_mem a) y
  refine (congrArg (Real.log · / 2) h).trans ?_
  rw [Real.log_mul (h0 M s (mem_ptsIn_inf.1 hy').1) (h0 A a (mem_ptsIn_inf.1 hy').2), add_div]
  rfl

end GlobalTheory.Mix
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TensorTorsionAddComponentwise
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum
open GlobalTheory.Ex GlobalTheory.Mum.TensTor

theorem GlobalTheory.Mum.TensTor.qkAdd_of_components : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (D D' : DegData R (maximalIdeal R)) {r : ℕ} (W : Matrix (Fin r) (Fin r) ℤ) (T : Tens D.toPre D'.toPre W) (F : Type) [Field F] [IsAlgClosed F] [Algebra (FractionRing R) F] (N N' : NumD F) (ν : NumOf D.toPre F N) (ν' : NumOf D'.toPre F N') (k : ℕ) (p' q' s' : QkPt D'.toPre F k) (ps qs ss : Fin r → QkPt D.toPre F k), PtRel T ν ν' p' ps → PtRel T ν ν' q' qs → PtRel T ν ν' s' ss → (∀ i, QkAdd (ps i) (qs i) (ss i)) → QkAdd p' q' s' := by
  intro R _ _ _ hR D D' r W T F _ _ _ N N' ν ν' k p' q' s' ps qs ss hp hq hs hadd
  have gt : GlobalTheory.Ex.BrGtSt := GlobalTheory.Ex.GtValues.points_correspond
  obtain ⟨-, -, gAdd, -, gQ⟩ := gt R D.toPre D.psi_even D.tau_bimult F N ν
  obtain ⟨-, -, gAdd', -, gQ'⟩ := gt R D'.toPre D'.psi_even D'.tau_bimult F N' ν'
  have hF := _root_.GlobalTheory.Mum.TensTor.tensFacts_holds R hR D D' W T F N N' ν ν'
  obtain ⟨-, -, he, hebij, -, -, -, -⟩ := hF
  obtain ⟨P', Ps, hP', hPs, hPy, hPg⟩ := hp
  obtain ⟨Q', Qs, hQ', hQs, hQy, hQg⟩ := hq
  obtain ⟨S', Ss, hS', hSs, hSy, hSg⟩ := hs
  have hz : ∀ i, N.QEq (Ps i * Qs i) (Ss i) := by
    intro i
    obtain ⟨x, hxy, hxg, hxe⟩ := hadd i
    obtain ⟨X, hX⟩ := ((gQ k).1 x).exists
    have hXeq : X = Ps i * Qs i := by
      refine Subtype.ext (Prod.ext ?_ ?_)
      · apply Multiplicative.toAdd.injective
        apply ν.eX.injective
        rw [hX.1, hxy, ← (hPs i).1, ← (hQs i).1, ← map_add (f := _)]
        rfl
      · exact (gAdd _ _ _ _ _ _ (hPs i).2 (hQs i).2 hX.2).1 hxg
    rw [← hXeq]
    exact ((gQ k).2.2 x (ss i) X (Ss i) hX (hSs i)).1 hxe
  choose z hz1 hz2 using hz
  obtain ⟨z', hz'⟩ := hebij.2 z
  have he0 : ∀ i, chi T ν ν' 0 i = 0 := fun i => by
    have := he 0 0 i
    rw [add_zero] at this
    exact (add_eq_left.1 this.symm)
  have hensmul : ∀ (n : ℕ) χ i, chi T ν ν' (n • χ) i = n • chi T ν ν' χ i := by
    intro n χ i
    induction n with
    | zero => rw [zero_smul, zero_smul, he0]
    | succ n ih => rw [succ_nsmul, he, ih, succ_nsmul]
  obtain ⟨x', hx'⟩ := (gQ' k).2.1 (P' * Q')
  refine ⟨x', ?_, ?_, ?_⟩
  · rw [← hx'.1, ← hP'.1, ← hQ'.1, ← map_add (f := _)]
    rfl
  · exact (gAdd' _ _ _ _ _ _ hP'.2 hQ'.2 hx'.2).2 rfl
  · refine ((gQ' k).2.2 x' s' (P' * Q') S' hx' hS').2 ⟨z', ?_, ?_⟩
    · apply hebij.1
      funext i
      have e1 : (P' * Q').1.1.toAdd = P'.1.1.toAdd + Q'.1.1.toAdd := rfl
      have e2 : (Ps i * Qs i).1.1.toAdd = (Ps i).1.1.toAdd + (Qs i).1.1.toAdd := rfl
      rw [hSy i, hz1 i, he, hensmul, hz', e1, he, hPy i, hQy i, e2]
    · have m1 := _root_.GlobalTheory.Mum.TensTor.gtRelV_mul F N N' W (cmp T ν ν') (chi T ν ν') (wv T ν ν') (_root_.GlobalTheory.Mum.TensTor.tensFacts_holds R hR D D' W T F N N' ν ν')
        P'.1.2 Q'.1.2 _ _ hPg hQg
      have m2 := _root_.GlobalTheory.Mum.TensTor.gtRelV_io F N N' W (cmp T ν ν') (chi T ν ν') (wv T ν ν') (_root_.GlobalTheory.Mum.TensTor.tensFacts_holds R hR D D' W T F N N' ν ν') z'
      have m3 := _root_.GlobalTheory.Mum.TensTor.gtRelV_mul F N N' W (cmp T ν ν') (chi T ν ν') (wv T ν ν') (_root_.GlobalTheory.Mum.TensTor.tensFacts_holds R hR D D' W T F N N' ν ν')
        _ _ _ _ m1 m2
      have e3 : ((fun j => (Ps j).1.2) * (fun j => (Qs j).1.2)) * (fun j => N.io (chi T ν ν' z' j)) =
          fun j => (Ss j).1.2 := by
        funext j
        rw [hz2 j, hz']
        rfl
      rw [e3] at m3
      exact _root_.GlobalTheory.Mum.TensTor.gtRelV_unique F N N' W (cmp T ν ν') (chi T ν ν') (wv T ν ν') (_root_.GlobalTheory.Mum.TensTor.tensFacts_holds R hR D D' W T F N N' ν ν')
        _ _ _ hSg m3
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TensorTorsionPointEquivIffComponentsEquiv
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum
open GlobalTheory.Ex GlobalTheory.Mum.TensTor

noncomputable section

namespace GlobalTheory.Mum.TensTor

theorem comp_nsmul {F : Type} [Field F] {N N' : NumD F} {r : ℕ} {e : N'.X → Fin r → N.X}
    (he : ∀ χ χ' i, e (χ + χ') i = e χ i + e χ' i) (k : ℕ) (z : N'.X) (i : Fin r) : e (k • z) i = k • e z i := by
  induction k with
  | zero =>
    have h := he 0 0 i
    rw [add_zero] at h
    simpa using h
  | succ k ih => rw [succ_nsmul, he, ih, succ_nsmul]

theorem qEq_iff_of_rel {F : Type} [Field F] {N N' : NumD F} {r : ℕ} {W : Matrix (Fin r) (Fin r) ℤ}
    {φ : N'.A → Fin r → N.A} {e : N'.X → Fin r → N.X} {wv : N'.A → F} (hT : TensFacts W φ e wv)
    (hW : IsUnit (W + W.transpose).det) {k : ℕ} {a' b' : N'.QT k} {as bs : Fin r → N.QT k}
    (ha : QRelV W φ e wv a' as) (hb : QRelV W φ e wv b' bs) : N'.QEq a' b' ↔ ∀ i, N.QEq (as i) (bs i) := by
  have hadd := hT.2.2.1
  have he := hT.2.2.2.1
  constructor
  · rintro ⟨z, hy, hg⟩ i
    refine ⟨e z i, ?_, ?_⟩
    · rw [← hb.1 i, hy, hadd, comp_nsmul hadd, ha.1 i]
    · have h1 := _root_.GlobalTheory.Mum.TensTor.gtRelV_mul F N N' W φ e wv hT _ _ _ _ ha.2 (_root_.GlobalTheory.Mum.TensTor.gtRelV_io F N N' W φ e wv hT z)
      rw [← hg] at h1
      have h2 := congrFun (_root_.GlobalTheory.Mum.TensTor.gtRelV_components_unique F N N' W φ e wv hT hW _ _ _ hb.2 h1) i
      simpa using h2
  · intro h
    choose z hz using h
    obtain ⟨z', hz'⟩ := he.2 z
    refine ⟨z', ?_, ?_⟩
    · apply he.1
      funext i
      rw [hadd, comp_nsmul hadd, hz', ha.1 i, hb.1 i]
      exact (hz i).1
    · have h1 := _root_.GlobalTheory.Mum.TensTor.gtRelV_mul F N N' W φ e wv hT _ _ _ _ ha.2 (_root_.GlobalTheory.Mum.TensTor.gtRelV_io F N N' W φ e wv hT z')
      have h2 : ((fun j => (as j).1.2) * fun j => N.io (e z' j)) = fun j => (bs j).1.2 :=
        funext fun j => by rw [Pi.mul_apply, hz']; exact ((hz j).2).symm
      rw [h2] at h1
      exact _root_.GlobalTheory.Mum.TensTor.gtRelV_unique F N N' W φ e wv hT _ _ _ hb.2 h1

theorem qkPt_equiv_iff_components : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R →
    ∀ (D D' : DegData R (maximalIdeal R)) {r : ℕ} (W : Matrix (Fin r) (Fin r) ℤ) (T : Tens D.toPre D'.toPre W)
    (F : Type) [Field F] [IsAlgClosed F] [Algebra (FractionRing R) F] (N N' : NumD F) (ν : NumOf D.toPre F N)
    (ν' : NumOf D'.toPre F N'), IsUnit (W + W.transpose).det → ∀ (k : ℕ) (p' q' : QkPt D'.toPre F k)
    (ps qs : Fin r → QkPt D.toPre F k), PtRel T ν ν' p' ps → PtRel T ν ν' q' qs →
    (QkPt.Equiv D'.toPre F p' q' ↔ ∀ i, QkPt.Equiv D.toPre F (ps i) (qs i)) := by
  intro R _ _ _ hB D D' r W T F _ _ _ N N' ν ν' hW k p' q' ps qs hp hq
  obtain ⟨a', as, ha', has, ha⟩ := hp
  obtain ⟨b', bs, hb', hbs, hb⟩ := hq
  have hT := _root_.GlobalTheory.Mum.TensTor.tensFacts_holds R hB D D' W T F N N' ν ν'
  have G := GlobalTheory.Ex.GtValues.points_correspond
  rw [((G R D'.toPre D'.psi_even D'.tau_bimult F N' ν').2.2.2.2 k).2.2 p' q' a' b' ha' hb', qEq_iff_of_rel hT hW ha hb]
  exact forall_congr' fun i =>
    (((G R D.toPre D.psi_even D.tau_bimult F N ν).2.2.2.2 k).2.2 _ _ _ _ (has i) (hbs i)).symm

end GlobalTheory.Mum.TensTor
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TensorTorsionTowerNsmulComponentwise
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum
open GlobalTheory.Ex GlobalTheory.Mum.TensTor

namespace GlobalTheory.Mum.TensTower

section Values
variable {F : Type} [Field F] {N N' : NumD F} {r : ℕ} {W : Matrix (Fin r) (Fin r) ℤ} {φ : N'.A → Fin r → N.A}
  {e : N'.X → Fin r → N.X} {wv : N'.A → F}

theorem comp_nsmul (h : TensFacts W φ e wv) (k : ℕ) (χ : N'.X) (i : Fin r) : e (k • χ) i = k • e χ i :=
  (AddMonoidHom.mk' (fun χ => e χ i) fun a b => h.2.2.1 a b i).map_nsmul k χ

theorem rel_pow (h : TensFacts W φ e wv) {v' : N'.Gt} {vs : Fin r → N.Gt} (hv : GtRelV W φ e wv v' vs) (k : ℕ) :
    GtRelV W φ e wv (v' ^ k) (vs ^ k) := by
  induction k with
  | zero =>
    have h0 := _root_.GlobalTheory.Mum.TensTor.gtRelV_io F N N' W φ e wv h 0
    have e0 : ∀ j, e 0 j = 0 := fun j => by simpa using comp_nsmul h 0 0 j
    simp only [e0, NumD.io_zero] at h0
    rw [pow_zero, pow_zero]
    exact h0
  | succ k ih =>
    rw [pow_succ, pow_succ]
    exact _root_.GlobalTheory.Mum.TensTor.gtRelV_mul F N N' W φ e wv h _ _ _ _ ih hv

theorem tower_val (h : TensFacts W φ e wv) {n m : ℕ} {p' : N'.QT (n * m)} {ps : Fin r → N.QT (n * m)} {t' : N'.QT n}
    {ts : Fin r → N.QT n} (hp : QRelV W φ e wv p' ps) (ht : QRelV W φ e wv t' ts)
    (hz : ∀ i, ∃ z : N.X, (ts i).1.1.toAdd = (ps i).1.1.toAdd + n • z ∧ (ts i).1.2 = (ps i).1.2 ^ m * N.io z) :
    ∃ z' : N'.X, t'.1.1.toAdd = p'.1.1.toAdd + n • z' ∧ t'.1.2 = p'.1.2 ^ m * N'.io z' := by
  choose z hz1 hz2 using hz
  obtain ⟨z', rfl⟩ := h.2.2.2.1.2 z
  refine ⟨z', h.2.2.2.1.1 (funext fun i => ?_), ?_⟩
  · rw [h.2.2.1, comp_nsmul h, ht.1, hp.1, hz1]
  · refine _root_.GlobalTheory.Mum.TensTor.gtRelV_unique F N N' W φ e wv h _ _ _ ht.2 ?_
    have := _root_.GlobalTheory.Mum.TensTor.gtRelV_mul F N N' W φ e wv h _ _ _ _ (rel_pow h hp.2 m) (_root_.GlobalTheory.Mum.TensTor.gtRelV_io F N N' W φ e wv h z')
    have e1 : (fun j => (ts j).1.2) = (fun j => (ps j).1.2) ^ m * fun j => N.io (e z' j) := funext hz2
    rw [e1]
    exact this

end Values

theorem tower : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (D D' : DegData R (maximalIdeal R)) {r : ℕ} (W : Matrix (Fin r) (Fin r) ℤ) (T : Tens D.toPre D'.toPre W) (F : Type) [Field F] [IsAlgClosed F] [Algebra (FractionRing R) F] (N N' : NumD F) (ν : NumOf D.toPre F N) (ν' : NumOf D'.toPre F N') (n m : ℕ), 0 < n → 0 < m → ∀ (p' : QkPt D'.toPre F (n * m)) (ps : Fin r → QkPt D.toPre F (n * m)) (t' : QkPt D'.toPre F n) (ts : Fin r → QkPt D.toPre F n), PtRel T ν ν' p' ps → PtRel T ν ν' t' ts → (∀ i, ∃ q : QkPt D.toPre F n, q.y = (ps i).y ∧ GtPtF.IsNsmul m (ps i).g q.g ∧ QkPt.Equiv D.toPre F q (ts i)) → ∃ q' : QkPt D'.toPre F n, q'.y = p'.y ∧ GtPtF.IsNsmul m p'.g q'.g ∧ QkPt.Equiv D'.toPre F q' t' := by
  intro R _ _ _ hR D D' r W T F _ _ _ N N' ν ν' n m _ _ p' ps t' ts ⟨a', as, ha', has, ha⟩ ⟨b', bs, hb', hbs, hb⟩ H
  have hF := _root_.GlobalTheory.Mum.TensTor.tensFacts_holds R hR D D' W T F N N' ν ν'
  have B := (GtValues.points_correspond R D.toPre D.psi_even D.tau_bimult F N ν).2.2.2.2 n
  have B' := (GtValues.points_correspond R D'.toPre D'.psi_even D'.tau_bimult F N' ν').2.2.2.2 n
  obtain ⟨z', hz1, hz2⟩ := tower_val hF ha hb fun i => by
    obtain ⟨q, hy, hn, he⟩ := H i
    obtain ⟨c, hc⟩ := (B.1 q).exists
    obtain ⟨z, h1, h2⟩ := (B.2.2 q (ts i) c (bs i) hc (hbs i)).1 he
    refine ⟨z, ?_, ?_⟩
    · rw [h1, ν.eX.injective (hc.1.trans (hy.trans (has i).1.symm))]
    · rw [h2, (GtValues.isNsmul_val ν m (has i).2 hc.2).1 hn]
  let c' : N'.QT n := ⟨(a'.1.1, a'.1.2 ^ m), by
    rw [NumD.mem_QT, ← pow_mul, mul_comm m n]
    exact a'.2⟩
  obtain ⟨q', hq'⟩ := B'.2.1 c'
  exact ⟨q', hq'.1.symm.trans ha'.1, (GtValues.isNsmul_val ν' m ha'.2 hq'.2).2 rfl,
    (B'.2.2 q' t' c' b' hq' hb').2 ⟨z', hz1, hz2⟩⟩

end GlobalTheory.Mum.TensTower
end

