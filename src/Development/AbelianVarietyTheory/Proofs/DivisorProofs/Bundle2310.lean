module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2178
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FrobTwistBaseChangeHomApp
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsProjOverWeierstrass
public import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissibleBaseOfCompleteDvr
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0554
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.DegenerationDataTorsionStructureAlgClosed
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0164
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0131
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0127
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.UniformizationLawsAndExpansionStatements
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0065
public import Development.AbelianVarietyTheory.Definitions.Divisors.GalRigidOfSurjective
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0064
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0061
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsProperToroidalModelStructureMap
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0721
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2214
public import Development.AbelianVarietyTheory.Definitions.Divisors.TateProductRigidificationTrivial
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
public import Development.AbelianVarietyTheory.Definitions.Degenerations.Bundle0002
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0065
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0194
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.ThetaGen

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RelativeFrobeniusKernelIdealLeFrobeniusKernelIde
section
set_option autoImplicit false

noncomputable section

open Coalgebra Bialgebra

namespace GlobalTheory.PDiv

open GlobalTheory.PDivGroup

theorem pow_sub_counit_mem_frobKerIdeal {p : ℕ} [Fact p.Prime] {R H : Type} [CommRing R]
    [CommRing H] [Bialgebra R H] (h : (p : R) = 0) (a : H) :
    a ^ p - algebraMap R H (counit (R := R) (a ^ p)) ∈ frobKerIdeal p R H := by
  have h0 := natCast_eq_zero_of_algebra h H
  have e : a ^ p - algebraMap R H (counit (R := R) (a ^ p)) =
      (a - algebraMap R H (counit (R := R) a)) ^ p := by
    rw [← frobRing_apply h0 (a - _), map_sub, frobRing_apply, frobRing_apply, counit_pow, map_pow]
  rw [e]
  exact pow_mem_frobKerIdeal (by simp [RingHom.mem_ker])

theorem kerIdeal_relFrob_le_frobKerIdeal (p : ℕ) [Fact p.Prime] (R : Type) [CommRing R]
    (h : (p : R) = 0) (G : PDivGroup p R) (n : ℕ) :
    kerIdeal ((relFrob h G).app n) ≤ frobKerIdeal p R (G.A n) := by
  have key : ∀ x : (frobTwist h G).A n, (relFrob h G).app n x -
      algebraMap R (G.A n) (counit (R := R) ((relFrob h G).app n x)) ∈
        frobKerIdeal p R (G.A n) := by
    intro x
    induction x using frobTwist_induction h n with
    | h0 => simp
    | h1 r a =>
      rw [map_smul, relFrob_app_frobProj, map_smul, smul_eq_mul, map_mul, Algebra.smul_def,
        ← mul_sub]
      exact Ideal.mul_mem_left _ _ (pow_sub_counit_mem_frobKerIdeal h a)
    | h2 x y hx hy =>
      rw [map_add (f := _), map_add (f := _), map_add (f := _), add_sub_add_comm]
      exact add_mem hx hy
  refine Ideal.map_le_iff_le_comap.2 fun x hx => ?_
  have hx' : counit (R := R) x = 0 := hx
  have := key x
  rw [CoalgHomClass.counit_comp_apply, hx', map_zero, sub_zero] at this
  exact this

end GlobalTheory.PDiv
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ReprModTrivialQuotientFreeRankTwiceDimension
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

noncomputable section
namespace GlobalTheory.SympQ
open GlobalTheory.Ex

theorem qq_free_of_torsion {C : Type} [Field C] [IsAlgClosed C] (N : NumD C) {k : ℕ} (hk : (k : C) ≠ 0) (a : ℕ)
    (hdiv : ∀ x : N.A, ∃ y, y ^ k = x)
    (e : (powMonoidHom k : N.A →* N.A).ker ≃* Multiplicative (Fin a → ZMod k)) :
    Nonempty (Qq N k ≃* Multiplicative (Fin (Module.finrank ℤ N.X + (a + Module.finrank ℤ N.X)) → ZMod k)) := by
  haveI : NeZero k := ⟨by rintro rfl; simp at hk⟩
  have hk0 : k ≠ 0 := NeZero.ne k
  obtain ⟨f⟩ := QStr.ker_struct N hk a e
  let v := Module.finBasis ℤ N.X
  let i₀ : (powMonoidHom k : N.Gt →* N.Gt).ker →* N.QT k := MonoidHom.mk'
    (fun g => ⟨(1, g.1), (show g.1 ^ k = 1 from g.2).trans N.io_zero.symm⟩)
    fun g g' => Subtype.ext (Prod.ext (_root_.mul_one _).symm rfl)
  let π₀ : N.QT k →* Multiplicative (Fin (Module.finrank ℤ N.X) → ZMod k) := MonoidHom.mk'
    (fun p => Multiplicative.ofAdd fun i => (v.repr p.1.1.toAdd i : ZMod k)) fun p q => by
      refine Multiplicative.toAdd.injective (funext fun i => ?_)
      simp
  have hπ₀ : ∀ p, π₀ p = 1 ↔ ∃ z : N.X, p.1.1.toAdd = k • z := fun p => by
    constructor
    · intro h
      have hd : ∀ i, (k : ℤ) ∣ v.repr p.1.1.toAdd i := fun i =>
        (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).1 (congrFun (congrArg Multiplicative.toAdd h) i)
      choose c hc using hd
      refine ⟨∑ i, c i • v i, ?_⟩
      conv_lhs => rw [← v.sum_repr p.1.1.toAdd]
      rw [Finset.smul_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [hc, mul_smul, natCast_zsmul]
    · rintro ⟨z, hz⟩
      refine Multiplicative.toAdd.injective (funext fun i => ?_)
      change ((v.repr p.1.1.toAdd i : ℤ) : ZMod k) = 0
      rw [hz]
      simp
  let π : Qq N k →* Multiplicative (Fin (Module.finrank ℤ N.X) → ZMod k) :=
    QuotientGroup.lift _ π₀ (by
      rintro _ ⟨z, rfl⟩
      exact (hπ₀ _).2 ⟨z.toAdd, rfl⟩)
  refine QStr.split_ext k _ _ ?_ (((QuotientGroup.mk' _).comp i₀).comp f.symm.toMonoidHom) π ?_ ?_ ?_
  · intro x
    obtain ⟨p, rfl⟩ := QuotientGroup.mk_surjective x
    rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff]
    exact ⟨p.1.1, Subtype.ext (Prod.ext rfl (N.mem_QT.1 p.2).symm)⟩
  · refine Function.Injective.comp (g := (QuotientGroup.mk' _).comp i₀) ?_ f.symm.injective
    rw [injective_iff_map_eq_one]
    intro g hg
    obtain ⟨z, hz⟩ := (QuotientGroup.eq_one_iff _).1 hg
    have h1 : k • z.toAdd = 0 := congrArg (fun q : N.QT k => q.1.1.toAdd) hz
    have h2 : N.io z.toAdd = g.1 := congrArg (fun q : N.QT k => q.1.2) hz
    have h3 : z.toAdd = 0 := (smul_eq_zero.1 ((natCast_zsmul _ _).trans h1)).resolve_left (Nat.cast_ne_zero.2 hk0)
    exact Subtype.ext (by rw [← h2, h3, N.io_zero]; rfl)
  · intro c
    let y : N.X := ∑ i, ((c.toAdd i).val : ℤ) • v i
    obtain ⟨b, hb⟩ := hdiv (N.io y).b
    obtain ⟨u, -, hu⟩ := QStr.root_over N hk0 (N.io y) b hb
    refine ⟨QuotientGroup.mk ⟨(Multiplicative.ofAdd y, u), hu⟩, Multiplicative.toAdd.injective (funext fun i => ?_)⟩
    change ((v.repr y i : ℤ) : ZMod k) = c.toAdd i
    have : v.repr y i = ((c.toAdd i).val : ℤ) := congrFun (v.repr_sum_self _) i
    rw [this]
    simp
  · intro x
    obtain ⟨p, rfl⟩ := QuotientGroup.mk_surjective x
    constructor
    · intro h
      obtain ⟨z, hz⟩ := (hπ₀ p).1 h
      have hg : (p.1.2 * (N.io z)⁻¹) ^ k = 1 := by
        rw [mul_pow, inv_pow, N.mem_QT.1 p.2, hz, N.io_nsmul, mul_inv_cancel]
      refine ⟨f ⟨_, hg⟩, ?_⟩
      change QuotientGroup.mk (i₀ (f.symm (f ⟨_, hg⟩))) = _
      rw [f.symm_apply_apply, ← qEq_iff_mk_eq]
      exact ⟨z, hz.trans (zero_add _).symm, (inv_mul_cancel_right _ _).symm⟩
    · rintro ⟨y, hy⟩
      rw [← hy]
      exact (hπ₀ (i₀ (f.symm y))).2 ⟨0, (smul_zero _).symm⟩

theorem qq_free : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], GlobalTheory.Mum.Base R → ∀ (D : DegData R (maximalIdeal R)) (F : Type) [Field F] [IsAlgClosed F] [Algebra (FractionRing R) F] (N : GlobalTheory.Ex.NumD F) (ν : GlobalTheory.Ex.NumOf D.toPre F N) (n : ℕ), 0 < n → Nonempty (Additive (GlobalTheory.SympQ.Qq N n) ≃+ (Fin (2 * (D.toPre.P.g + Module.finrank ℤ D.toPre.X)) → ZMod n)) := by
  intro R _ _ _ hR D F _ _ _ N ν n hn
  have hL : Laws := GlobalTheory.allSixLaws.1
  haveI : IsNoetherianRing R := hR.1.1
  haveI : CharZero R := hR.2
  haveI : CharZero (FractionRing R) := charZero_of_injective_algebraMap (IsFractionRing.injective R _)
  haveI : CharZero F := charZero_of_injective_algebraMap (algebraMap (FractionRing R) F).injective
  have hk : (n : F) ≠ 0 := Nat.cast_ne_zero.2 hn.ne'
  have tor : ∀ (b : N.A) (k : ℕ), ν.eA b ^ k = 1 ↔ b ^ k = 1 := fun b k => by
    rw [← map_pow, MulEquiv.map_eq_one_iff]
  have hdiv : ∀ x : N.A, ∃ y, y ^ n = x := fun x => by
    obtain ⟨y, hy⟩ := ValuesTorsion.exists_pow_eq hL D.toPre.P (jFK (R := R) F ≫ jK R) (ν.eA x) hn
    exact ⟨ν.eA.symm y, by rw [← map_pow, hy, MulEquiv.symm_apply_apply]⟩
  obtain ⟨e⟩ : Nonempty ((powMonoidHom n : N.A →* N.A).ker ≃* Multiplicative (Fin (2 * D.toPre.P.g) → ZMod n)) := by
    obtain ⟨v, hv, h⟩ := ValuesTorsion.exists_basis hL D.toPre.P (jFK (R := R) F ≫ jK R) hk
    refine ValuesTorsion.nonempty_equiv_of_basis hn.ne' (fun i => ν.eA.symm (v i))
      (fun i => by rw [← map_pow, hv, map_one]) fun y hy => ?_
    refine (existsUnique_congr fun c => ?_).1 (h (ν.eA y) ((tor _ _).2 hy))
    simp only [List.prod_ofFn, ← map_pow, ← map_prod, MulEquiv.symm_apply_eq]
  obtain ⟨f⟩ := qq_free_of_torsion N hk _ hdiv e
  have hr : Module.finrank ℤ N.X = Module.finrank ℤ D.toPre.X := ν.eX.toIntLinearEquiv.finrank_eq
  have h2 : Module.finrank ℤ N.X + (2 * D.toPre.P.g + Module.finrank ℤ N.X) =
      2 * (D.toPre.P.g + Module.finrank ℤ D.toPre.X) := by rw [hr]; ring
  rw [← h2]
  exact ⟨MulEquiv.toAdditiveLeft f⟩

end GlobalTheory.SympQ
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ReprModTrivialQuotientPairingLevelPushEqPow
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory.SympQ.PushPow

open ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Ex

variable {A U : Type} [CommGroup A] [CommGroup U] {θ : A → A → A → U}

theorem cubN_mul_iter (h : IsCub θ) (n m : ℕ) (b x : A) :
    cubN θ (n * m) 1 b x = cubN θ n 1 (b ^ m) x * cubN θ m 1 b x ^ n := by
  induction n with
  | zero => simp [cubN]
  | succ n ih =>
    have e : cubN θ ((n + 1) * m) 1 b x = cubN θ (n * m) 1 b x * cubN θ m (b ^ (n * m)) b x := by
      rw [Nat.succ_mul]
      simp only [cubN, Finset.prod_range_add]
      refine congrArg _ (Finset.prod_congr rfl fun i _ => ?_)
      rw [_root_.one_mul, pow_add]
    have s1 : cubN θ (n + 1) 1 (b ^ m) x = cubN θ n 1 (b ^ m) x * θ ((b ^ m) ^ n) (b ^ m) x := by
      simp only [cubN, Finset.prod_range_succ, _root_.one_mul]
    rw [e, ih, h.N_split m (b ^ (n * m)) b x, s1, ← pow_mul' b n m, pow_succ (cubN θ m 1 b x) n]
    ac_rfl

theorem cubN_pow_right (h : IsCub θ) (k m : ℕ) (b x : A) :
    cubN θ k 1 b (x ^ m) * cubN θ m 1 x b ^ k = cubN θ k 1 b x ^ m * cubN θ m 1 x (b ^ k) := by
  induction m with
  | zero => simp [cubN, h.face₃]
  | succ m ih =>
    have e := h.N_add k 1 b (x ^ m) x
    rw [h.face, _root_.mul_one, _root_.one_mul] at e
    have s1 : cubN θ (m + 1) 1 x b = cubN θ m 1 x b * θ (x ^ m) x b := by
      simp only [cubN, Finset.prod_range_succ, _root_.one_mul]
    have s2 : cubN θ (m + 1) 1 x (b ^ k) = cubN θ m 1 x (b ^ k) * θ (x ^ m) x (b ^ k) := by
      simp only [cubN, Finset.prod_range_succ, _root_.one_mul]
    have t1 : θ b (x ^ m) x = θ (x ^ m) x b := by rw [h.s01, h.s12]
    have t2 : θ (b ^ k) (x ^ m) x = θ (x ^ m) x (b ^ k) := by rw [h.s01, h.s12]
    rw [t1, t2] at e
    rw [pow_succ x, s1, s2]
    apply Additive.ofMul.injective
    replace e := congrArg Additive.ofMul e
    replace ih := congrArg Additive.ofMul ih
    simp only [ofMul_mul, ofMul_pow] at e ih ⊢
    linear_combination (norm := module) e + ih

variable {O : Type} [CommRing O] (N : NumD O)

theorem wp_pushRep (n m : ℕ) (hn : 0 < n) (p q : N.QT (n * m)) :
    N.wp (pushRep N (n * m) n p) (pushRep N (n * m) n q) = N.wp p q ^ m := by
  have hd : n ∣ n * m := dvd_mul_right n m
  have hM : n * m / n = m := Nat.mul_div_cancel_left m hn
  simp only [NumD.wp, NumD.tk, pushRep_fst N hd, pushRep_snd N hd, hM, NumD.Gt.pow_b]
  have ps1 := NumD.Gt.pow_s p.1.2 m q.1.1.toAdd
  have ps2 := NumD.Gt.pow_s q.1.2 m p.1.1.toAdd
  rw [← N.QT_pow_b q] at ps1
  rw [← N.QT_pow_b p] at ps2
  have i1 := cubN_mul_iter N.cub n m q.1.2.b p.1.2.b
  have i2 := cubN_mul_iter N.cub n m p.1.2.b q.1.2.b
  have a := cubN_pow_right N.cub n m (p.1.2.b ^ m) q.1.2.b
  have b := cubN_pow_right N.cub n m (q.1.2.b ^ m) p.1.2.b
  have c := cubN_pow_right N.cub m m q.1.2.b p.1.2.b
  rw [← pow_mul'] at a b
  apply Additive.ofMul.injective
  replace ps1 := congrArg Additive.ofMul ps1
  replace ps2 := congrArg Additive.ofMul ps2
  replace i1 := congrArg Additive.ofMul i1
  replace i2 := congrArg Additive.ofMul i2
  replace a := congrArg Additive.ofMul a
  replace b := congrArg Additive.ofMul b
  replace c := congrArg Additive.ofMul c
  simp only [ofMul_mul, ofMul_div, ofMul_pow] at ps1 ps2 i1 i2 a b c ⊢
  linear_combination (norm := module) ps1 - ps2 - (m : ℤ) • i1 + (m : ℤ) • i2 + b - a + (n : ℤ) • c

end GlobalTheory.SympQ.PushPow

theorem GlobalTheory.SympQ.wp_pushRep_pow : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], GlobalTheory.Mum.Base R → ∀ (D : DegData R (maximalIdeal R)) (F : Type) [Field F] [IsAlgClosed F] [Algebra (FractionRing R) F] (N : GlobalTheory.Ex.NumD F) (ν : GlobalTheory.Ex.NumOf D.toPre F N) (n m : ℕ), 0 < n → 0 < m → ∀ p q : N.QT (n * m), N.wp (GlobalTheory.SympQ.pushRep N (n * m) n p) (GlobalTheory.SympQ.pushRep N (n * m) n q) = N.wp p q ^ m := by
  intro R _ _ _ _ D F _ _ _ N ν n m hn hm p q
  exact GlobalTheory.SympQ.PushPow.wp_pushRep N n m hn p q
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ReprModTrivialQuotientPairingNondegenerate
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum GlobalTheory.Ex

noncomputable section

namespace GlobalTheory.SympQ

theorem qEq_one_of_wp {C : Type} [Field C] [IsAlgClosed C] (N : NumD C) {k : ℕ} (hk : (k : C) ≠ 0)
    (hdiv : ∀ x : N.A, ∃ y, y ^ k = x)
    (nd : ∀ b : N.A, b ^ k = 1 → (∀ b', b' ^ k = 1 → N.weil k b b' = 1) → b = 1) (p : N.QT k)
    (hp : ∀ p', N.wp p p' = 1) : N.QEq p 1 := by
  have hk0 : k ≠ 0 := fun h => hk (by rw [h, Nat.cast_zero])
  have h3 : ∀ y : N.X, ∃ p : N.QT k, p.1.1.toAdd = y := fun y => by
    obtain ⟨b, hb⟩ := hdiv (N.io y).b
    obtain ⟨g, -, h⟩ := QStr.root_over N hk0 (N.io y) b hb
    exact ⟨⟨(Multiplicative.ofAdd y, g), h⟩, rfl⟩
  obtain ⟨p₀, hq, h1, hb⟩ := (QStr.orth_iff N hk nd p).1 fun p' _ => hp p'
  have : p₀ = 1 := by
    refine Subtype.ext (Prod.ext h1 (NumD.Gt.ext hb (funext fun χ => ?_)))
    obtain ⟨p', rfl⟩ := h3 χ
    rw [← (WpPairing.wp_pairing C N _ p₀ p' p').2.2.2.2.2.1 h1 hb, ← WpPairing.wp_congr_left N hq p', hp p']
    rfl
  rwa [this] at hq

theorem wpQ_nondeg : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], GlobalTheory.Mum.Base R → ∀ (D : DegData R (maximalIdeal R)) (F : Type) [Field F] [IsAlgClosed F] [Algebra (FractionRing R) F] (N : GlobalTheory.Ex.NumD F) (ν : GlobalTheory.Ex.NumOf D.toPre F N) (n : ℕ), 0 < n → ∀ x : GlobalTheory.SympQ.Qq N n, (∀ y, GlobalTheory.SympQ.wpQ N n x y = 1) → x = 1 := by
  intro R _ _ _ hR D F _ _ _ N ν n hn x hx
  obtain ⟨⟨h1, h2, h3, h4⟩, hc⟩ := hR
  have hL : Laws := GlobalTheory.lawsAndExpansions.1.1
  have : CharZero F := by
    have : CharZero (FractionRing R) := inferInstance
    exact charZero_of_injective_algebraMap (algebraMap (FractionRing R) F).injective
  have h0 : (n : F) ≠ 0 := Nat.cast_ne_zero.2 hn.ne'
  obtain ⟨hW, -⟩ := GlobalTheory.ThetaInValues.brUth_of_laws hL R D.toPre D.psi_even D.tau_bimult F N ν
  have tor : ∀ (b : N.A) (k : ℕ), ν.eA b ^ k = 1 ↔ b ^ k = 1 := fun b k => by
    rw [← map_pow, MulEquiv.map_eq_one_iff]
  induction x using QuotientGroup.induction_on with
  | H p =>
    have hq : N.QEq p 1 := by
      refine qEq_one_of_wp N h0 (fun a => ?_) (fun b hb h => ?_) p fun p' => hx (QuotientGroup.mk p')
      · obtain ⟨y, hy⟩ := GlobalTheory.ValuesTorsion.exists_pow_eq hL D.toPre.P (jFK (R := R) F ≫ jK R) (ν.eA a) hn
        exact ⟨ν.eA.symm y, by rw [← map_pow, hy, MulEquiv.symm_apply_apply]⟩
      · refine ν.eA.map_eq_one_iff.1 (GlobalTheory.ThetaRep.eq_one_of_weilIs hL D.toPre.P (jFK (R := R) F ≫ jK R) h0 _
          ((tor _ _).2 hb) fun y hy => ?_)
        obtain ⟨b', rfl⟩ := ν.eA.surjective y
        have hb' := (tor _ _).1 hy
        have := hW n hn b b' hb hb'
        rwa [h b' hb', show unitOn (1 : Fˣ) = 1 from map_one (Units.map _)] at this
    exact (qEq_iff_mk_eq N p 1).1 hq

end GlobalTheory.SympQ
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RestrictProperSectionsBijectiveToFibreOpen
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory

theorem restrict_proper_sections_bijective_to_fibre_open : ∀ (Y₀ H X'' P'' : Scheme.{0}) (H' : H.Opens) (i : H'.toScheme ⟶ X'') (a'' : X'' ⟶ P'') (b'' : P'' ⟶ Y₀), IsNoetherian Y₀ → IsOpenImmersion i → IsProper a'' → Surjective a'' → (∀ V : P''.Opens, Function.Bijective (a''.app V).hom) → IsFinite b'' → ∃ (P' : Scheme.{0}) (c : P' ⟶ P'') (X : H.Opens) (k : X.toScheme ⟶ H'.toScheme) (a : X.toScheme ⟶ P'), IsOpenImmersion c ∧ IsNoetherian P' ∧ IsProper a ∧ Surjective a ∧ (∀ V : P'.Opens, Function.Bijective (a.app V).hom) ∧ k ≫ H'.ι = X.ι ∧ a ≫ c = k ≫ i ≫ a'' ∧ (∀ z : H'.toScheme, (∀ w : X'', a'' w = a'' (i z) → w ∈ Set.range i) → H'.ι z ∈ X) ∧ ∀ w : X'', a'' w ∈ Set.range c → w ∈ Set.range (k ≫ i) := by
  intro Y₀ H X'' P'' H' i a'' b'' hY hi ha hs hV hb
  haveI := hY; haveI := hi; haveI := ha; haveI := hs; haveI := hb
  have hP : IsNoetherian P'' := by
    haveI : IsLocallyNoetherian P'' := LocallyOfFiniteType.isLocallyNoetherian b''
    haveI : CompactSpace P'' := QuasiCompact.compactSpace_of_compactSpace b''
    exact {}
  let U0 : P''.Opens := ⟨(a'' '' (Set.range i)ᶜ)ᶜ,
    (a''.isClosedMap _ i.isOpenEmbedding.isOpen_range.isClosed_compl).isOpen_compl⟩
  have hsub : ∀ w : X'', a'' w ∈ U0 → w ∈ Set.range i := by
    intro w hw
    by_contra h
    exact hw ⟨w, h, rfl⟩
  let W : H'.toScheme.Opens := i ⁻¹ᵁ (a'' ⁻¹ᵁ U0)
  let X : H.Opens := H'.ι ''ᵁ W
  have hXr : Set.range X.ι ⊆ Set.range H'.ι := by
    rw [Scheme.Opens.range_ι]
    rintro _ ⟨z, -, rfl⟩
    exact ⟨z, rfl⟩
  let k : X.toScheme ⟶ H'.toScheme := IsOpenImmersion.lift H'.ι X.ι hXr
  have hk : k ≫ H'.ι = X.ι := IsOpenImmersion.lift_fac _ _ _
  have hrk : Set.range k = (W : Set H'.toScheme) := by
    ext z
    constructor
    · rintro ⟨y, rfl⟩
      have h1 : H'.ι (k y) ∈ X := by
        rw [← Scheme.Hom.comp_apply, hk]
        have : X.ι y ∈ Set.range X.ι := ⟨y, rfl⟩
        rwa [Scheme.Opens.range_ι] at this
      obtain ⟨w, hw, he⟩ := h1
      rwa [← H'.ι.isOpenEmbedding.injective he]
    · intro hz
      have : H'.ι z ∈ Set.range X.ι := by
        rw [Scheme.Opens.range_ι]; exact ⟨z, hz, rfl⟩
      obtain ⟨y, hy⟩ := this
      refine ⟨y, H'.ι.isOpenEmbedding.injective ?_⟩
      rw [← Scheme.Hom.comp_apply, hk, hy]
  have hrki : Set.range (k ≫ i) = (a'' ⁻¹ᵁ U0 : Set X'') := by
    rw [Scheme.Hom.comp_base, TopCat.coe_comp, Set.range_comp, hrk]
    ext w
    constructor
    · rintro ⟨z, hz, rfl⟩; exact hz
    · intro hw
      obtain ⟨z, rfl⟩ := hsub w hw
      exact ⟨z, hw, rfl⟩
  let e := IsOpenImmersion.isoOfRangeEq (k ≫ i) (a'' ⁻¹ᵁ U0).ι (by rw [Scheme.Opens.range_ι]; exact hrki)
  let a : X.toScheme ⟶ U0.toScheme := e.hom ≫ (a'' ∣_ U0)
  have hfac : a ≫ U0.ι = k ≫ i ≫ a'' := by
    simp only [a, e, Category.assoc, morphismRestrict_ι, IsOpenImmersion.isoOfRangeEq_hom_fac_assoc]
  refine ⟨U0.toScheme, U0.ι, X, k, a, inferInstance, ?_, inferInstance, ?_, ?_, hk, hfac, ?_, ?_⟩
  · haveI := hP
    haveI : CompactSpace U0.toScheme := QuasiCompact.compactSpace_of_compactSpace U0.ι
    exact {}
  · refine ⟨fun x => ?_⟩
    obtain ⟨w, hw⟩ := a''.surjective x.1
    have hw' : w ∈ Set.range (k ≫ i) := by
      rw [hrki]; show a'' w ∈ U0; rw [hw]; exact x.2
    obtain ⟨y, rfl⟩ := hw'
    refine ⟨y, U0.ι.isOpenEmbedding.injective ?_⟩
    rw [← Scheme.Hom.comp_apply, hfac]
    simp only [Scheme.Hom.comp_apply] at hw ⊢
    rw [hw]; rfl
  · intro V
    show Function.Bijective ((e.hom ≫ (a'' ∣_ U0)).app V).hom
    rw [Scheme.Hom.comp_app]
    have h1 : Function.Bijective ((a'' ∣_ U0).app V).hom := by
      rw [morphismRestrict_app]
      have h3 := hV (U0.ι ''ᵁ V)
      have h4 : Function.Bijective (X''.presheaf.map (eqToHom (image_morphismRestrict_preimage a'' U0 V)).op).hom :=
        ConcreteCategory.bijective_of_isIso _
      exact h4.comp h3
    have h2 : Function.Bijective (e.hom.app ((a'' ∣_ U0) ⁻¹ᵁ V)).hom := ConcreteCategory.bijective_of_isIso _
    exact h2.comp h1
  · intro z hz
    have : z ∈ W := by
      show a'' (i z) ∈ U0
      rintro ⟨w, hw, he⟩
      exact hw (hz w he)
    exact ⟨z, this, rfl⟩
  · intro w hw
    rw [hrki]
    rw [Scheme.Opens.range_ι] at hw
    exact hw

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RingEquivSubMemMaximalIdealOfPurelyInsepResidue
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.SiegJoin GlobalTheory.Poinc GlobalTheory.TChart
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.ResFix

theorem sigma_fix_mod_max : ∀ (A R R' : Type) [CommRing A] [CommRing R] [IsLocalRing R] [CommRing R'] [IsLocalRing R'] (b : A →+* R) (θ : R →+* R') [IsLocalHom θ] (q : ℕ) [ExpChar (ResidueField R) q] (σ : R' ≃+* R'), (∀ x : ResidueField R, ∃ n : ℕ, ∃ a : A, x ^ q ^ n = residue R (b a)) → (∀ a, σ (θ (b a)) = θ (b a)) → ∀ r, σ (θ r) - θ r ∈ maximalIdeal R' := by
  intro A R R' _ _ _ _ _ b θ _ q _ σ hins hfix r
  obtain ⟨n, a, ha⟩ := hins (residue R r)
  have h1 : r ^ q ^ n - b a ∈ maximalIdeal R := by
    rw [← residue_eq_zero_iff, map_sub, map_pow, ha, sub_self]
  have h2 : θ r ^ q ^ n - θ (b a) ∈ maximalIdeal R' := by
    have := map_nonunit θ _ h1
    simpa [map_sub, map_pow] using this
  have h3 : σ (θ r) ^ q ^ n - θ (b a) ∈ maximalIdeal R' := by
    have := map_nonunit (σ : R' →+* R') _ h2
    simpa [map_sub, map_pow, hfix a] using this
  haveI : ExpChar (ResidueField R') q :=
    expChar_of_injective_ringHom (ResidueField.map θ).injective q
  have e2 : residue R' (θ r) ^ q ^ n = residue R' (θ (b a)) := by
    rw [← map_pow, ← sub_eq_zero, ← map_sub, residue_eq_zero_iff]; exact h2
  have e3 : residue R' (σ (θ r)) ^ q ^ n = residue R' (θ (b a)) := by
    rw [← map_pow, ← sub_eq_zero, ← map_sub, residue_eq_zero_iff]; exact h3
  have e4 : (residue R' (σ (θ r)) - residue R' (θ r)) ^ q ^ n = 0 := by
    rw [sub_pow_expChar_pow, e2, e3, sub_self]
  rw [← residue_eq_zero_iff, map_sub]
  exact pow_eq_zero_iff (pow_ne_zero _ (expChar_pos (ResidueField R') q).ne') |>.mp e4

end GlobalTheory.ResFix
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SecIsMulOfTranslatedThetaCoefficientProportionalStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.secIsMul_of_translatedThetaCoefficient_proportional : ∀ (R : Type) [CommRing R] [IsDomain R] (D : DegPre R) (χ : D.X) (u : LB.Gen (LB.LinComb D.P.L (K := PUnit) (fun _ => (D.c χ).left) (fun _ => -1))) (th : GlobalTheory.UU.SecBT D (𝟙_ _) 1 0) (g₁ g₂ : GlobalTheory.UU.SecBT D (𝟙_ _) 1 χ) (b₁ b₂ q : R), GlobalTheory.PsiRing.Coef D χ u th g₁ b₁ → GlobalTheory.PsiRing.Coef D χ u th g₂ b₂ → b₁ = q * b₂ → ReciprocityTheory.ChartRestriction.G.DVR.SecIsMul (𝟙_ _ ⊗ D.P.A).hom q g₁ g₂ := by
  first | exact @GlobalTheory.PsiRing.secIsMul_of_coef | exact GlobalTheory.PsiRing.secIsMul_of_coef | (intros; apply GlobalTheory.PsiRing.secIsMul_of_coef <;> assumption)
end

