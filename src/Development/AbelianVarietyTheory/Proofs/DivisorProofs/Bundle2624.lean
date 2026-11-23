module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsDimEqOne
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1440
public import Development.AbelianVarietyTheory.Definitions.Divisors.OfFactorE
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsProjOverWeierstrass
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
public import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissibleBaseOfCompleteDvr
public import Development.AbelianVarietyTheory.Proofs.CharacterTheory.Bundle0002
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AlgIdemBinv
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsTrivialMumfordFormalSumLatticeAdditivityRelati
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2290
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2392
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2459
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2458
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2542
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2471
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2560
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2484
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0067
public import Development.AbelianVarietyTheory.Statements.TorsionEndomorphisms.EndDeterminedOnTorsion
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0012
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2570
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2469
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsThetaLevelAbelianSchemeGlueAffineCover
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2520
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2478
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2516
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2429
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2568
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2480

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TateModuleMapCokerCardEqKerTorsionCard
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.HTLat GlobalTheory.Published.AbVarRed GlobalTheory.CechPic GlobalTheory.AV GlobalTheory.AV.AbVar
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.TateCoker

variable {l : ℕ} [hl : Fact l.Prime] {M N : Type} [CommGroup M] [CommGroup N] (φ : M →* N)

def lker (l : ℕ) : Subgroup M where
  carrier := {x | φ x = 1 ∧ ∃ n : ℕ, x ^ l ^ n = 1}
  mul_mem' := by
    rintro a b ⟨ha, m, hm⟩ ⟨hb, m', hm'⟩
    refine ⟨by rw [map_mul, ha, hb, _root_.one_mul], m + m', ?_⟩
    rw [mul_pow, pow_add, pow_mul, hm, one_pow, mul_comm (l ^ m), pow_mul, hm', one_pow, _root_.one_mul]
  one_mem' := ⟨map_one φ, 0, one_pow _⟩
  inv_mem' := by
    rintro a ⟨ha, m, hm⟩
    exact ⟨by rw [map_inv, ha, inv_one], m, by rw [inv_pow, hm, inv_one]⟩

theorem pow_pow_eq_one {x : M} {m : ℕ} (h : x ^ l ^ m = 1) (j : ℕ) : x ^ l ^ (m + j) = 1 := by
  rw [pow_add, pow_mul, h, one_pow]

variable {φ}

theorem kill [Finite φ.ker] {k : M} (hk : φ k = 1) {m : ℕ} (hm : k ^ l ^ m = 1) :
    k ^ l ^ Nat.card φ.ker = 1 := by
  have hp : l.Prime := hl.out
  have h1 : orderOf k ∣ Nat.card φ.ker := Subgroup.orderOf_dvd_natCard _ hk
  obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow hp).1 (orderOf_dvd_of_pow_eq_one hm)
  have hpos : 0 < Nat.card φ.ker := Nat.card_pos_iff.2 ⟨⟨⟨1, map_one φ⟩⟩, inferInstance⟩
  have h2 : j ≤ Nat.card φ.ker :=
    ((Nat.lt_pow_self hp.one_lt).trans_le (Nat.le_of_dvd hpos (hj ▸ h1))).le
  exact orderOf_dvd_iff_pow_eq_one.1 (hj ▸ pow_dvd_pow l h2)

theorem exists_lift (hs : Function.Surjective φ) [Finite φ.ker] (n : ℕ) (y : N) (hy : y ^ l ^ n = 1) :
    ∃ x : M, φ x = y ∧ ∃ m : ℕ, x ^ l ^ m = 1 := by
  have hp : l.Prime := hl.out
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · rw [pow_zero, pow_one] at hy
    exact ⟨1, by rw [map_one, hy], 0, one_pow _⟩
  obtain ⟨x₀, rfl⟩ := hs y
  have hpos : 0 < Nat.card φ.ker := Nat.card_pos_iff.2 ⟨⟨⟨1, map_one φ⟩⟩, inferInstance⟩
  have hk : x₀ ^ l ^ n ∈ φ.ker := by rw [MonoidHom.mem_ker, map_pow, hy]
  have hc : (x₀ ^ l ^ n) ^ Nat.card φ.ker = 1 :=
    orderOf_dvd_iff_pow_eq_one.1 (Subgroup.orderOf_dvd_natCard _ hk)
  obtain ⟨e, u, hu, hcu⟩ := Nat.exists_eq_pow_mul_and_not_dvd hpos.ne' l hp.one_lt.ne'
  have hcop : Nat.Coprime u (l ^ n) :=
    Nat.Coprime.pow_right n (Nat.coprime_comm.1 ((Nat.Prime.coprime_iff_not_dvd hp).2 hu))
  obtain ⟨w, -, hw⟩ := Nat.exists_mul_mod_eq_one_of_coprime hcop (Nat.one_lt_pow hn.ne' hp.one_lt)
  refine ⟨x₀ ^ (u * w), ?_, n + e, ?_⟩
  · rw [map_pow, pow_eq_pow_mod _ hy, hw, pow_one]
  · rw [← pow_mul, show u * w * l ^ (n + e) = l ^ n * Nat.card φ.ker * w by rw [hcu, pow_add]; ring,
      pow_mul, pow_mul, hc, one_pow]

theorem indep [Finite φ.ker] {x x' : M} (h : φ x = φ x') {m m' : ℕ} (hx : x ^ l ^ m = 1)
    (hx' : x' ^ l ^ m' = 1) : x ^ l ^ Nat.card φ.ker = x' ^ l ^ Nat.card φ.ker := by
  have h1 : φ (x * x'⁻¹) = 1 := by rw [map_mul, map_inv, h, mul_inv_cancel]
  have h2 : (x * x'⁻¹) ^ l ^ (m + m') = 1 := by
    rw [mul_pow, inv_pow, pow_pow_eq_one hx, add_comm, pow_pow_eq_one hx', inv_one, _root_.one_mul]
  have h3 := kill h1 h2
  rwa [mul_pow, inv_pow, mul_inv_eq_one] at h3

variable (hs : Function.Surjective φ) [Finite φ.ker]
include hs

def lift (t : Tate l N) (n : ℕ) : M := (exists_lift hs n (t.lev n) (t.lev_pow n)).choose

theorem lift_spec (t : Tate l N) (n : ℕ) : φ (lift hs t n) = t.lev n ∧ ∃ m : ℕ, lift hs t n ^ l ^ m = 1 :=
  (exists_lift hs n (t.lev n) (t.lev_pow n)).choose_spec

def del (t : Tate l N) : M := lift hs t (Nat.card φ.ker) ^ l ^ Nat.card φ.ker

theorem del_eq (t : Tate l N) {x : M} (hx : φ x = t.lev (Nat.card φ.ker)) {m : ℕ} (hm : x ^ l ^ m = 1) :
    del hs t = x ^ l ^ Nat.card φ.ker := by
  obtain ⟨h1, m', h2⟩ := lift_spec hs t (Nat.card φ.ker)
  exact indep (h1.trans hx.symm) h2 hm

theorem del_mem (t : Tate l N) : del hs t ∈ lker φ l := by
  obtain ⟨h1, m, h2⟩ := lift_spec hs t (Nat.card φ.ker)
  refine ⟨by rw [del, map_pow, h1, t.lev_pow], m, ?_⟩
  rw [del, ← pow_mul, mul_comm, pow_mul, h2, one_pow]

def delta : Tate l N →+ Additive (lker φ l) where
  toFun t := Additive.ofMul ⟨del hs t, del_mem hs t⟩
  map_zero' := by
    show Additive.ofMul _ = Additive.ofMul (1 : lker φ l)
    congr 1
    exact Subtype.ext ((del_eq hs 0 (x := 1) (m := 0) (by rw [map_one, Tate.lev_zero]) (one_pow _)).trans
      (one_pow _))
  map_add' s t := by
    show Additive.ofMul _ = Additive.ofMul (_ * _)
    congr 1
    apply Subtype.ext
    obtain ⟨hs1, m, hs2⟩ := lift_spec hs s (Nat.card φ.ker)
    obtain ⟨ht1, m', ht2⟩ := lift_spec hs t (Nat.card φ.ker)
    refine (del_eq hs (s + t) (x := lift hs s _ * lift hs t _) (m := m + m')
      (by rw [map_mul, hs1, ht1, Tate.lev_add]) ?_).trans ?_
    · rw [mul_pow, pow_pow_eq_one hs2, add_comm, pow_pow_eq_one ht2, _root_.one_mul]
    · rw [mul_pow]; rfl

theorem delta_surjective (hd : ∀ x : M, ∃ y, y ^ l = x) : Function.Surjective (delta (l := l) hs) := by
  intro k0
  set a := Nat.card φ.ker
  obtain ⟨⟨k, hk1, m, hm⟩, rfl⟩ : ∃ z : lker φ l, Additive.ofMul z = k0 := ⟨Additive.toMul k0, rfl⟩
  obtain ⟨s, hsa⟩ := GlobalTheory.Published.tate_lev_surj l M hd a k (kill hk1 hm)
  let t : Tate l N := Tate.mk (fun n => φ (s.lev (n + a))) fun n =>
    ⟨by rw [← map_pow, add_comm, s.lev_add_pow, hsa, hk1], by rw [← map_pow, add_right_comm, s.lev_succ]⟩
  refine ⟨t, ?_⟩
  show Additive.ofMul _ = Additive.ofMul _
  congr 1
  apply Subtype.ext
  exact (del_eq hs t (x := s.lev (a + a)) (m := a + a) rfl (s.lev_pow _)).trans
    ((s.lev_add_pow a a).trans hsa)

theorem delta_ker : (delta hs).ker = (LinearMap.range (Tate.map l φ)).toAddSubgroup := by
  set a := Nat.card φ.ker
  ext t
  have e0 : t ∈ (delta hs).ker ↔ del hs t = 1 := by
    rw [AddMonoidHom.mem_ker]
    constructor
    · intro h; exact congrArg Subtype.val (congrArg Additive.toMul h)
    · intro h
      show Additive.ofMul _ = Additive.ofMul (1 : lker φ l)
      exact congrArg Additive.ofMul (Subtype.ext h)
  rw [e0, Submodule.mem_toAddSubgroup, LinearMap.mem_range]
  constructor
  · intro h
    have lv : ∀ n, (lift hs t (n + a) ^ l ^ n) ^ l ^ a = 1 := fun n => by
      obtain ⟨h1, m, h2⟩ := lift_spec hs t (n + a)
      rw [← h, del_eq hs t (x := lift hs t (n + a) ^ l ^ n) (m := m)
        (by rw [map_pow, h1, add_comm, t.lev_add_pow]) (by rw [← pow_mul, mul_comm, pow_mul, h2, one_pow])]
    let y : Tate l M := Tate.mk (fun n => lift hs t (n + a) ^ l ^ a) fun n => by
      refine ⟨by rw [← pow_mul, mul_comm, pow_mul]; exact lv n, ?_⟩
      obtain ⟨h1, m, h2⟩ := lift_spec hs t (n + 1 + a)
      obtain ⟨h1', m', h2'⟩ := lift_spec hs t (n + a)
      rw [← pow_mul, mul_comm, pow_mul]
      refine indep (m := m) (m' := m') ?_ (by rw [← pow_mul, mul_comm, pow_mul, h2, one_pow]) h2'
      rw [map_pow, h1, h1', show n + 1 + a = (n + a) + 1 by omega, t.lev_succ]
    refine ⟨y, Tate.ext fun n => ?_⟩
    rw [Tate.lev_map, Tate.lev_mk, map_pow, (lift_spec hs t (n + a)).1, t.lev_add_pow]
  · rintro ⟨y, rfl⟩
    exact (del_eq hs _ (x := y.lev a) (m := a) rfl (y.lev_pow a)).trans (y.lev_pow a)

omit hs in
theorem map_injective' : Function.Injective (Tate.map l φ) := by
  refine (injective_iff_map_eq_zero _).2 fun y hy => Tate.ext fun n => ?_
  have h1 : ∀ k, φ (y.lev k) = 1 := fun k => congrArg (·.lev k) hy
  rw [Tate.lev_zero, ← y.lev_add_pow n (Nat.card φ.ker)]
  exact kill (h1 _) (y.lev_pow _)

end GlobalTheory.TateCoker

namespace GlobalTheory


open GlobalTheory.TateCoker in
theorem tate_map_coker_card : ∀ (l : ℕ) [Fact l.Prime] (M N : Type) [CommGroup M] [CommGroup N] (φ : M →* N), (∀ x : M, ∃ y, y ^ l = x) → Function.Surjective φ → Finite φ.ker → Function.Injective (Tate.map l φ) ∧ Nat.card (Tate l N ⧸ LinearMap.range (Tate.map l φ)) = Nat.card {x : M // φ x = 1 ∧ ∃ n : ℕ, x ^ l ^ n = 1} := by
  intro l _ M N _ _ φ hd hs hf
  refine ⟨map_injective', ?_⟩
  have e1 : (Tate l N ⧸ LinearMap.range (Tate.map l φ)) ≃
      (Tate l N ⧸ (LinearMap.range (Tate.map l φ)).toAddSubgroup) := Equiv.refl _
  rw [Nat.card_congr e1, Nat.card_congr (QuotientAddGroup.quotientAddEquivOfEq (delta_ker hs)).symm.toEquiv,
    Nat.card_congr (QuotientAddGroup.quotientKerEquivOfSurjective _ (delta_surjective hs hd)).toEquiv]
  exact Nat.card_congr (Additive.toMul.trans (Equiv.refl _))

end GlobalTheory
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TensorDataPeriodsBalancedIntegralMatrices
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.TChart GlobalTheory.Mum

noncomputable section

open GlobalTheory.Mum.PolTens GlobalTheory.TensBal in
theorem GlobalTheory.Mum.PolTens.tauBal_polTens : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], IsCN R → ∀ (Q : Data R) (D' : DegData R (maximalIdeal R))
    {r : ℕ} (W : Matrix (Fin r) (Fin r) ℤ) (h : IsUnit (W + W.transpose).det), ((W + W.transpose).map (Int.cast : ℤ → ℝ)).PosDef →
    ∀ (pr : Fin r → (D'.toPre.P.A ⟶ Q.B)) (hl : IsLimit (Fan.mk D'.toPre.P.A pr)) (xe : D'.toPre.X ≃+ (Fin r → Q.X))
    (w : LB.Iso D'.toPre.P.L (LB.LinComb Q.M.L (tensφ pr) (tensε W))),
    (∀ i, IsMonHom (pr i)) → (∀ z i, D'.toPre.c z ≫ pr i = Q.c (xe z i)) → w.IsGen →
    (∀ y z J J', Good Q.M.L z J → Good D'.toPre.P.L z J' →
      val (D'.toPre.psi y) (𝟙 _) z J' = gm (D'.toPre.xK y) z _ (w.s (fun k => J (D'.toPre.xK y ≫ tensφ pr k), J' (D'.toPre.xK y))) *
        ∏ i, ∏ j, val (Q.tau (xe y i) (xe y j)) (𝟙 _) z J ^ W i j) →
    letI := PowLim.mod xe (symUnitOf W h)
    ∀ a : TensO (symUnitOf W h), D'.toPre.TauBal (PowLim.act pr hl (TensO.mat _ a)) (PowLim.act pr hl (TensO.mat _ (star a)))
      (fun y => a • y) (fun y => star a • y) := by
  intro R _ _ _ _ Q D' r W h _ pr hl xe w hpr hc hw hpsi
  letI := PowLim.mod xe (symUnitOf W h)
  intro a
  have hA := transpose_mul_eq W h a
  intro u' hu' hn' y y'
  have htr := triv_span xe hpr hc (span_sigP W _ _ hA)
  rw [flat_sigP] at htr
  obtain ⟨Ξ, hΞ, hΞ0, hΞv⟩ := htr
  refine corr_of_val D'.toPre.P.isLB fun z J' hJ' => ?_
  obtain ⟨J, hJ⟩ := GlobalTheory.BoxFamily.exists_good_at Q.M.isLB z
  have key := ros_sig hl hpr w hw _ _ u' hu' hn' Ξ hΞ hΞ0 z J J' hJ hJ' y y'
  rw [hΞv z J hJ y y', tv_sigP Q xe W _ _ (fun y => a • y) (fun y => star a • y) (PowLim.xe_smul xe _ a)
    (PowLim.xe_smul xe _ (star a)) z J y y'] at key
  have prr := prod_ros (PowLim.act pr hl (TensO.mat _ a)) (PowLim.act pr hl (TensO.mat _ (star a)))
    (DVR.cP D'.toPre (TK R) y) (DVR.cP D'.toPre (TK R) y') (isoV w z J J')
  have l₁ : DVR.cP D'.toPre (TK R) y ≫ PowLim.act pr hl (TensO.mat _ a) = DVR.cP D'.toPre (TK R) (a • y) := by
    rw [DVR.cP, DVR.cP, PowLim.c_smul Q D'.toPre pr hl xe hc, Category.assoc]
  have l₂ : DVR.cP D'.toPre (TK R) y' ≫ PowLim.act pr hl (TensO.mat _ (star a)) =
      DVR.cP D'.toPre (TK R) (star a • y') := by
    rw [DVR.cP, DVR.cP, PowLim.c_smul Q D'.toPre pr hl xe hc, Category.assoc]
  rw [l₁, l₂, ← DVR.cPoint_add, ← DVR.cPoint_add] at prr
  change ∏ k, isoV w z J J' (D'.toPre.pt2 y y' ≫ rosatiφ D'.toPre.P.A (PowLim.act pr hl (TensO.mat _ a))
    (PowLim.act pr hl (TensO.mat _ (star a))) k) ^ rosatiε k = _ at prr
  rw [prr] at key
  rw [val_mul hJ', val_pull hJ', Category.id_comp, tau_pol xe w hpsi hJ hJ', tau_pol xe w hpsi hJ hJ']
  have e0 : rosatiε 0 = 1 := rfl
  have e1 : rosatiε 1 = -1 := rfl
  have e2 : rosatiε 2 = -1 := rfl
  have e3 : rosatiε 3 = -1 := rfl
  have e4 : rosatiε 4 = 1 := rfl
  have e5 : rosatiε 5 = 1 := rfl
  have v0 : (![a • y + y', a • y, y', y + star a • y', y, star a • y'] : Fin 6 → D'.toPre.X) 0 = a • y + y' := rfl
  have v1 : (![a • y + y', a • y, y', y + star a • y', y, star a • y'] : Fin 6 → D'.toPre.X) 1 = a • y := rfl
  have v2 : (![a • y + y', a • y, y', y + star a • y', y, star a • y'] : Fin 6 → D'.toPre.X) 2 = y' := rfl
  have v3 : (![a • y + y', a • y, y', y + star a • y', y, star a • y'] : Fin 6 → D'.toPre.X) 3 = y + star a • y' := rfl
  have v4 : (![a • y + y', a • y, y', y + star a • y', y, star a • y'] : Fin 6 → D'.toPre.X) 4 = y := rfl
  have v5 : (![a • y + y', a • y, y', y + star a • y', y, star a • y'] : Fin 6 → D'.toPre.X) 5 = star a • y' := rfl
  rw [Fin.prod_univ_six] at key
  erw [v0, v1, v2, v3, v4, v5] at key
  simp only [e0, e1, e2, e3, e4, e5] at key
  apply Additive.ofMul.injective
  have k' := congrArg Additive.ofMul key
  simp only [ofMul_mul, ofMul_inv, ofMul_zpow] at k' ⊢
  linear_combination (norm := abel) k'
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TensorDegenerationTauBalancedOfAdjointIntMatrice
section
noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory.TensBal
open GlobalTheory.TensAct
open ReciprocityTheory.ChartRestriction.G.DVR (cP cPoint_add)

theorem triv_span {R : Type} [CommRing R] [IsDomain R] {D D' : DegPre R} {r : ℕ} {W : Matrix (Fin r) (Fin r) ℤ}
    (T : Tens D D' W) (hB : D.TauBimult) {c : Vec r →₀ ℤ}
    (hc : c ∈ Submodule.span ℤ (Set.range fun p : Vec r × Vec r × Vec r => theta p.1 p.2.1 p.2.2)) : Triv T c := by
  induction hc using Submodule.span_induction with
  | mem x hx => obtain ⟨p, rfl⟩ := hx; exact _root_.GlobalTheory.TensBal.triv_theta R D D' W T hB _ _ _
  | zero => exact _root_.GlobalTheory.TensBal.triv_zero R D D' W T
  | add x y _ _ hx hy => exact _root_.GlobalTheory.TensBal.triv_add R D D' W T _ _ hx hy
  | smul n x _ hx =>
    induction n using Int.induction_on with
    | zero => rw [zero_smul]; exact _root_.GlobalTheory.TensBal.triv_zero R D D' W T
    | succ k ih => rw [add_smul, one_smul]; exact _root_.GlobalTheory.TensBal.triv_add R D D' W T _ _ ih hx
    | pred k ih =>
      rw [sub_smul, one_smul, sub_eq_add_neg]
      exact _root_.GlobalTheory.TensBal.triv_add R D D' W T _ _ ih (_root_.GlobalTheory.TensBalNeg.triv_neg R D D' W T _ hx)

theorem tau_tens {R : Type} [CommRing R] [IsDomain R] {D D' : DegPre R} {r : ℕ} {W : Matrix (Fin r) (Fin r) ℤ}
    (T : Tens D D' W) {z : (TK R).left} {J J'} (hJ : Good D.P.L z J) (hJ' : Good D'.P.L z J') (p q : D'.X) :
    val (D'.tau p q) (𝟙 _) z J' = isoV T.w z J J' (cP D' (TK R) (p + q)).left * qv T z J (p + q) *
      (isoV T.w z J J' (cP D' (TK R) p).left * qv T z J p)⁻¹ *
      (isoV T.w z J J' (cP D' (TK R) q).left * qv T z J q)⁻¹ * (val D'.rigK (𝟙 _) z J')⁻¹ := by
  rw [GlobalTheory.TauBalBox.tau_val D' hJ', T.psi _ z J J' hJ hJ', T.psi _ z J J' hJ hJ', T.psi _ z J J' hJ hJ']
  rfl

theorem tauBal_tens : ∀ (R : Type) [CommRing R] [IsDomain R] (I : Ideal R) (D D' : DegData R I) {r : ℕ} (W : Matrix (Fin r) (Fin r) ℤ) (T : Tens D.toPre D'.toPre W) (A A' : Matrix (Fin r) (Fin r) ℤ), A.transpose * (W + W.transpose) = (W + W.transpose) * A' → D'.toPre.TauBal (GlobalTheory.TensAct.matAct T A) (GlobalTheory.TensAct.matAct T A') (GlobalTheory.TensAct.latAct T A) (GlobalTheory.TensAct.latAct T A') := by
  intro R _ _ I D D' r W T A A' hA u' hu' hn' y y'
  obtain ⟨Ξ, hΞ, hΞ0, hΞv⟩ := triv_span T D.tau_bimult (GlobalTheory.T.rosatiBalanceFormalSum_mem_span_cubicalTheta W A A' hA)
  refine corr_of_val D'.toPre.P.isLB fun z J' hJ' => ?_
  obtain ⟨J, hJ⟩ := GlobalTheory.BoxFamily.exists_good_at D.toPre.P.isLB z
  have key := _root_.GlobalTheory.TensRos.ros_sig R D.toPre D'.toPre W T A A' u' hu' hn' Ξ hΞ hΞ0 z J J' hJ hJ' y y'
  rw [hΞv z J hJ y y', _root_.GlobalTheory.TensBalLat.main R D.toPre D'.toPre W T D.tau_bimult A A' z J hJ y y'] at key
  have pr := prod_ros (matAct T A) (matAct T A') (cP D'.toPre (TK R) y) (cP D'.toPre (TK R) y')
    (isoV T.w z J J')
  have l₁ : cP D'.toPre (TK R) y ≫ matAct T A = cP D'.toPre (TK R) (latAct T A y) := by
    rw [cP, cP, c_lin, Category.assoc]
  have l₂ : cP D'.toPre (TK R) y' ≫ matAct T A' = cP D'.toPre (TK R) (latAct T A' y') := by
    rw [cP, cP, c_lin, Category.assoc]
  rw [l₁, l₂, ← cPoint_add, ← cPoint_add] at pr
  change ∏ a, isoV T.w z J J' (D'.toPre.pt2 y y' ≫ rosatiφ D'.toPre.P.A (matAct T A) (matAct T A') a) ^ rosatiε a = _ at pr
  rw [pr] at key
  rw [val_mul hJ', val_pull hJ', Category.id_comp, tau_tens T hJ hJ', tau_tens T hJ hJ']
  have e0 : rosatiε 0 = 1 := rfl
  have e1 : rosatiε 1 = -1 := rfl
  have e2 : rosatiε 2 = -1 := rfl
  have e3 : rosatiε 3 = -1 := rfl
  have e4 : rosatiε 4 = 1 := rfl
  have e5 : rosatiε 5 = 1 := rfl
  have r0 : rosLat T A A' y y' 0 = latAct T A y + y' := rfl
  have r1 : rosLat T A A' y y' 1 = latAct T A y := rfl
  have r2 : rosLat T A A' y y' 2 = y' := rfl
  have r3 : rosLat T A A' y y' 3 = y + latAct T A' y' := rfl
  have r4 : rosLat T A A' y y' 4 = y := rfl
  have r5 : rosLat T A A' y y' 5 = latAct T A' y' := rfl
  simp only [Fin.prod_univ_six, e0, e1, e2, e3, e4, e5, r0, r1, r2, r3, r4, r5] at key
  apply Additive.ofMul.injective
  have k' := congrArg Additive.ofMul key
  simp only [ofMul_mul, ofMul_inv, ofMul_zpow] at k' ⊢
  linear_combination (norm := abel) k'

end GlobalTheory.TensBal
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaConstantListFieldExtensionEqUpToPerm
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ZM GlobalTheory.ZH GlobalTheory.UMin GlobalTheory.UPoinc GlobalTheory.Ex.OneGen
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.UMin.SymCmp

theorem grpPullback_id {S : Scheme.{0}} (G : Over S) [GrpObj G] : IsGrpPullback G G (𝟙 S) (𝟙 G.left) := by
  refine ⟨IsPullback.of_horiz_isIso ⟨by simp⟩, fun T x y x₀ y₀ hx hy => ?_⟩
  let ρ : Over.mk (T.hom ≫ 𝟙 S) ⟶ T := Over.homMk (𝟙 T.left) (by simp)
  have ex : x₀ = ρ ≫ x := Over.OverMorphism.ext (hx.trans ((Category.comp_id _).trans (Category.id_comp _).symm))
  have ey : y₀ = ρ ≫ y := Over.OverMorphism.ext (hy.trans ((Category.comp_id _).trans (Category.id_comp _).symm))
  rw [ex, ey, ← MonObj.comp_mul]
  exact (Category.id_comp _).trans (Category.comp_id _).symm

theorem spMap_comp_ringHom {A B C : Type} [CommRing A] [CommRing B] [CommRing C] (f : A →+* B) (g : B →+* C) :
    spMap g ≫ spMap f = spMap (g.comp f) := by
  rw [← Spec.map_comp]; rfl

theorem sec_eq_of_f {X : Scheme.{0}} {M : LB X} {s s' : LB.Sec M} (h : ∀ j, s.f j = s'.f j) : s = s' := by
  cases s; cases s'
  simp only [LB.Sec.mk.injEq]
  exact funext h

theorem pullS_pullS {S : Scheme.{0}} (G : Over S) [GrpObj G] {L : LB G.left} (hL : L.IsLB) (a : ℤ) {T T' T'' : Over S}
    (h : T' ⟶ T) (h' : T'' ⟶ T') (s : LB.Sec (LPow G L a T)) :
    VVRank.pullS G a h' (VVRank.pullS G a h s) = VVRank.pullS G a (h' ≫ h) s := by
  refine sec_eq_of_f (sec_ext_val hL (fun y J hJ => ?_))
  refine (VVRank.sv_pullS G a h' _ (𝟙 _) y hJ).trans ((VVRank.sv_pullS G a h s _ y hJ).trans ?_)
  refine Eq.trans ?_ (VVRank.sv_pullS G a (h' ≫ h) s (𝟙 _) y hJ).symm
  rw [MonoidalCategory.comp_whiskerRight, Over.comp_left, Category.assoc]

theorem thList_ext_perm : ∀ (S : Scheme.{0}) (G : Over S) [GrpObj G] [IsCommMonObj G] (L : LB G.left) (ρ : LB.Gen (L.pull (eSec G))), L.IsLB → ρ.IsGen → ∀ (g m : ℕ) (R : Type) [CommRing R] (x : Sp R ⟶ S) (θ : SecAt G L x), Odd m → IsUnit (m : R) → PolFib G L g x → ∀ (K F : Type) [Field K] [Field F] (i : R →+* K) (i' : R →+* F) (φ : K →+* F), φ.comp i = i' → ∀ (N : ℕ) (pt : Fin N → (Over.mk (spMap i ≫ x) ⟶ G)) (c : Fin N → K) (pt' : Fin N → (Over.mk (spMap i' ≫ x) ⟶ G)) (c' : Fin N → F), ThList G L ρ m (spMap i ≫ x) (SecAt.pull G L θ i) pt c → ThList G L ρ m (spMap i' ≫ x) (SecAt.pull G L θ i') pt' c' → ∃ σ : Equiv.Perm (Fin N), ∀ b, c' b = φ (c (σ b)) := by
  intro S G _ _ L ρ hL hρ g m R _ x θ hm hu hP K F _ _ i i' φ hi N pt c pt' c' H H'
  subst hi
  obtain ⟨p₁, -, h₁⟩ := _root_.GlobalTheory.UMin.ThPull.thList_pull S G L ρ hL hρ m N K F φ (spMap i ≫ x) (SecAt.pull G L θ i) pt c H
  simp only [SecAt.pull] at h₁
  rw [pullS_pullS G hL] at h₁
  have ey : spMap φ ≫ spMap i ≫ x = spMap (φ.comp i) ≫ x := by
    rw [← Category.assoc, spMap_comp_ringHom]
  have key : ∀ {y y' : Sp F ⟶ S} (e : y = y') (u : Over.mk y ⟶ Over.mk x) (u' : Over.mk y' ⟶ Over.mk x),
      u.left = u'.left → ∀ {p : Fin N → (Over.mk y ⟶ G)} {d : Fin N → F},
      ThList G L ρ m y (VVRank.pullS G _ u θ) p d →
      ∃ p' : Fin N → (Over.mk y' ⟶ G), ThList G L ρ m y' (VVRank.pullS G _ u' θ) p' d := by
    intro y y' e u u' hu p d h
    subst e
    obtain rfl : u = u' := Over.OverMorphism.ext hu
    exact ⟨p, h⟩
  obtain ⟨q₁, H₁⟩ := key ey _ (Over.homMk (spMap (φ.comp i)) rfl : Over.mk (spMap (φ.comp i) ≫ x) ⟶ Over.mk x)
    (by simp only [Over.comp_left, Over.homMk_left]; rw [spMap_comp_ringHom]) h₁
  have hPy : PolFib G L g (spMap (φ.comp i) ≫ x) :=
    (_root_.GlobalTheory.UMin.FibMove.polFib_move S S G L G L (𝟙 S) (𝟙 G.left) hL hL (grpPullback_id G)
      (GlobalTheory.ThetaAffineGlue.lbIso_pull_id hL) g R x).2 F (φ.comp i) hP
  have hmF : (m : F) ≠ 0 := by
    rw [← map_natCast (φ.comp i) m]
    exact (hu.map (φ.comp i)).ne_zero
  exact (_root_.GlobalTheory.UMin.ThUniq.theta_lists_unique S G L ρ hL hρ g m m N N F (spMap (φ.comp i) ≫ x) hm hmF hm hmF hPy).1 _ q₁ pt' _ c' H₁ H'

end GlobalTheory.UMin.SymCmp
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaConstantsFunctionsFiniteFlatCover
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ZM GlobalTheory.ZH GlobalTheory.UMin GlobalTheory.UPoinc GlobalTheory.Ex.OneGen
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.UMin

theorem thList_cover : ∀ (S : Scheme.{0}) (G : Over S) [GrpObj G] [IsCommMonObj G] (L : LB G.left) (ρ : LB.Gen (L.pull (eSec G))), L.IsLB → ρ.IsGen → ∀ (g m N : ℕ) (R : Type) [CommRing R] [IsNoetherianRing R] (x : Sp R ⟶ S) (θ : SecAt G L x), Odd m → IsUnit (m : R) → N = m ^ (4 * g) → PolFib G L g x → ∃ (R₁ : Type) (_ : CommRing R₁) (_ : Algebra R R₁) (c : Fin N → R₁), Module.Finite R R₁ ∧ Module.FaithfullyFlat R R₁ ∧ ∀ (K : Type) [Field K] (i : R →+* K) (i₁ : R₁ →+* K), i₁.comp (algebraMap R R₁) = i → ∃ pt : Fin N → (Over.mk (spMap i ≫ x) ⟶ G), ThList G L ρ m (spMap i ≫ x) (SecAt.pull G L θ i) pt (fun a => i₁ (c a)) := by
  intro S G _ _ L ρ hL hρ g m N R _ _ x θ hm hu hN hP
  obtain ⟨R₁, _, _, q, hfin, hff, hq, hpts⟩ := _root_.GlobalTheory.UMin.TorsionList.exists_cover_torsion_list S G L g m N R x hm hu hN hP
  haveI : IsNoetherianRing R₁ := Algebra.FiniteType.isNoetherianRing R R₁
  have hcomp : ∀ {K : Type} [Field K] (i₁ : R₁ →+* K),
      spMap i₁ ≫ spMap (algebraMap R R₁) = spMap (i₁.comp (algebraMap R R₁)) := by
    intro K _ i₁; simp [spMap]
  let pt₀ : ∀ {K : Type} [Field K] (i₁ : R₁ →+* K) (a : Fin N), Over.mk (spMap (i₁.comp (algebraMap R R₁)) ≫ x) ⟶ G :=
    fun i₁ a => Over.homMk (spMap i₁ ≫ (q a).left) (by
      have h := Over.w (q a)
      simp only [Over.mk_hom] at h ⊢
      rw [Category.assoc, h, ← Category.assoc, hcomp])
  have key : ∀ a : Fin N, ∃ c : R₁, ∀ (K : Type) [Field K] (i₁ : R₁ →+* K)
      (pt : Over.mk (spMap (i₁.comp (algebraMap R R₁)) ≫ x) ⟶ G), pt.left = spMap i₁ ≫ (q a).left →
        ThG G L ρ m (SecAt.pull G L θ (i₁.comp (algebraMap R R₁))) pt (fn (i₁ c)) := by
    intro a
    refine GlobalTheory.T.exists_ring_element_of_local_field_point_values R₁ (fun K _ i₁ v => ∀ (pt : Over.mk (spMap (i₁.comp (algebraMap R R₁)) ≫ x) ⟶ G),
        pt.left = spMap i₁ ≫ (q a).left →
        ThG G L ρ m (SecAt.pull G L θ (i₁.comp (algebraMap R R₁))) pt (fn v)) ?_ ?_
    · intro K _ i₁ u v hu' hv'
      exact _root_.GlobalTheory.UMin.thG_unique_of_polFib S G L ρ hL hρ g m R x K (i₁.comp (algebraMap R R₁)) hm hu hP _ (pt₀ i₁ a) u v
        (hu' _ rfl) (hv' _ rfl)
    · intro p hp
      obtain ⟨f, hf, c, hc⟩ := _root_.GlobalTheory.UMin.ThLocal.exists_local S G L ρ hL hρ g m R x θ R₁ N q hm hu hP hq p hp
      exact ⟨f, hf, c a, fun K _ j pt hpt => hc K j a pt hpt⟩
  choose c hc using key
  refine ⟨R₁, inferInstance, inferInstance, c, hfin, hff, fun K _ i i₁ hi => ?_⟩
  subst hi
  obtain ⟨hinj, hcov⟩ := hpts K i₁ (pt₀ i₁) (fun a => rfl)
  exact ⟨pt₀ i₁, hinj, fun a => hc a K i₁ _ rfl, hcov⟩

end GlobalTheory.UMin
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaGroupActionCompatFibreIsoStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum GlobalTheory.ThetaMove
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.thetaGroupAction_compat_fibreIso : ∀ {S S' : Scheme.{0}} {A : Over S} {A' : Over S'} [GrpObj A] [GrpObj A'] {L : LB A.left} {L' : LB A'.left} (hL : L.IsLB) (hL' : L'.IsLB) {T : Over S} {T' : Over S'} (f : (T' ⊗ A').left ⟶ (T ⊗ A).left) [IsIso f] (k : ℤ) (θ : ThetaGrp A L k T) (θ' : ThetaGrp A' L' k T') (Ψ : ∀ {Z : Scheme.{0}}, (Z ⟶ (T' ⊗ A').left) → ∀ z : Z, ((Z ⟶ A.left) → L.ι) → ((Z ⟶ A'.left) → L'.ι) → (Z.presheaf.stalk z)ˣ) (hT : f ≫ (translT A θ.pt).left = (translT A' θ'.pt).left ≫ f) (H : ∀ (Z : Scheme.{0}) (q : Z ⟶ (T' ⊗ A').left) (z : Z) J J', Good L z J → Good L' z J' → val (L := L) (φ := ![(snd T A).left, (translPt A θ.pt).left]) (ε := ![k, -k]) θ.φ (q ≫ f) z J = Ψ q z J J' ^ k * val (L := L') (φ := ![(snd T' A').left, (translPt A' θ'.pt).left]) (ε := ![k, -k]) θ'.φ q z J' * (Ψ (q ≫ (translT A' θ'.pt).left) z J J' ^ k)⁻¹) (σ σ' : LB.Sec (LPow A' L' k T')) (τ τ' : LB.Sec (LPow A L k T)) (hσ : ∀ (Z : Scheme.{0}) (q : Z ⟶ (T' ⊗ A').left) (z : Z) J J', Good L z J → Good L' z J' → sval (L := L) (φ := fun _ : Fin 1 => (snd T A).left) (ε := fun _ => k) τ (q ≫ f) z J = (Ψ q z J J' ^ k).val * sval (L := L') (φ := fun _ : Fin 1 => (snd T' A').left) (ε := fun _ => k) σ q z J') (hσ' : ∀ (Z : Scheme.{0}) (q : Z ⟶ (T' ⊗ A').left) (z : Z) J J', Good L z J → Good L' z J' → sval (L := L) (φ := fun _ : Fin 1 => (snd T A).left) (ε := fun _ => k) τ' (q ≫ f) z J = (Ψ q z J J' ^ k).val * sval (L := L') (φ := fun _ : Fin 1 => (snd T' A').left) (ε := fun _ => k) σ' q z J') (hact : IsActOf A' L' k θ' σ σ'), IsActOf A L k θ τ τ' := by
  first | exact @GlobalTheory.ThetaMove.isActOf_of_fibreIso | exact GlobalTheory.ThetaMove.isActOf_of_fibreIso | (intros; apply GlobalTheory.ThetaMove.isActOf_of_fibreIso <;> assumption)
end

