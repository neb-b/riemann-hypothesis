module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0537
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0015
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0636
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0589
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0645
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0007
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0006
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.KummerConnectingUnitClassEqKummerClass
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsRatioCover
public import Development.AbelianVarietyTheory.Definitions.Divisors.FormalCoboundarySmul
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0584
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdditiveFormalGroupCoboundaryHomogeneous
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0642
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0568
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0624
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0646
public import Development.AbelianVarietyTheory.Definitions.Divisors.SplitDoublingNBlock
public import Development.AbelianVarietyTheory.Proofs.ToricGeometry.Bundle0013
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0006
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0007
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.BCTools
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0322
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0358
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0409

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.KerIdealFinrankEqPowOfIdempotent
section
open CategoryTheory TensorProduct Coalgebra Bialgebra GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup

namespace GlobalTheory

theorem natSeq_pow_of_mul_eq {p h : ℕ} (hp : p.Prime) (a b : ℕ → ℕ)
    (hab : ∀ n, a n * b n = p ^ (n * h))
    (ha : ∀ n, a (n + 1) ≤ a 1 * a n) (hb : ∀ n, b (n + 1) ≤ b 1 * b n) :
    ∃ s : ℕ, ∀ n, a n = p ^ (n * s) := by
  have h1 : a 1 * b 1 = p ^ h := by simpa using hab 1
  obtain ⟨s, hs, hs'⟩ := (Nat.dvd_prime_pow hp).1 (Dvd.intro _ h1)
  obtain ⟨t, ht, ht'⟩ := (Nat.dvd_prime_pow hp).1 (Dvd.intro_left _ h1)
  have h0 : a 0 * b 0 = 1 := by simpa using hab 0
  have ha0 : a 0 = 1 := Nat.eq_one_of_mul_eq_one_right h0
  have hb0 : b 0 = 1 := Nat.eq_one_of_mul_eq_one_left h0
  have hst : s + t = h := by
    rw [hs', ht', ← pow_add] at h1
    exact Nat.pow_right_injective hp.two_le h1
  have hale : ∀ n, a n ≤ p ^ (n * s) := by
    intro n
    induction n with
    | zero => simp [ha0]
    | succ n ih =>
      calc a (n + 1) ≤ a 1 * a n := ha n
        _ ≤ p ^ s * p ^ (n * s) := by rw [hs']; exact Nat.mul_le_mul_left _ ih
        _ = p ^ ((n + 1) * s) := by rw [← pow_add]; ring_nf
  have hble : ∀ n, b n ≤ p ^ (n * t) := by
    intro n
    induction n with
    | zero => simp [hb0]
    | succ n ih =>
      calc b (n + 1) ≤ b 1 * b n := hb n
        _ ≤ p ^ t * p ^ (n * t) := by rw [ht']; exact Nat.mul_le_mul_left _ ih
        _ = p ^ ((n + 1) * t) := by rw [← pow_add]; ring_nf
  refine ⟨s, fun n => ?_⟩
  by_contra hne
  have hlt : a n < p ^ (n * s) := lt_of_le_of_ne (hale n) hne
  have hpos : 0 < p ^ (n * t) := pow_pos hp.pos _
  have key : a n * b n < p ^ (n * s) * p ^ (n * t) :=
    calc a n * b n ≤ a n * p ^ (n * t) := Nat.mul_le_mul_left _ (hble n)
      _ < p ^ (n * s) * p ^ (n * t) := Nat.mul_lt_mul_of_pos_right hlt hpos
  rw [hab n, ← pow_add, ← Nat.mul_add, hst] at key
  exact lt_irrefl _ key

theorem kerIdeal_finrank_eq_pow_of_idempotent : ∀ (p : ℕ) [Fact p.Prime] (k : Type) [Field k]
    (G : PDivGroup p k) (u v : G ⟶ G), u + v = 𝟙 G → u ≫ v = 0 → v ≫ u = 0 →
    ∃ h₀ : ℕ, ∀ n : ℕ, Module.finrank k (G.A n ⧸ kerIdeal (u.app n)) = p ^ (n * h₀) := by
  intro p _ k _ G u v huv h1 h2
  exact natSeq_pow_of_mul_eq (Fact.out : p.Prime)
    (fun n => Module.finrank k (G.A n ⧸ kerIdeal (u.app n)))
    (fun n => Module.finrank k (G.A n ⧸ kerIdeal (v.app n)))
    (GlobalTheory.T.finrank_kernelIdeal_mul_of_idempotents p k G u v huv h1 h2)
    (_root_.GlobalTheory.PDivGroup.finrank_quot_kerIdeal_succ_le p k G u) (_root_.GlobalTheory.PDivGroup.finrank_quot_kerIdeal_succ_le p k G v)

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.KummerBoundaryLineBundleFirstChernClassStatement
section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.kummerBoundary_lineBundle_firstChernClass : ∀ (q : ℕ) [NeZero q] (κ : (restr (Int.castRingHom (ZMod q))).obj (tw q 1) ⟶ Gm) (h0 : κ ≫ ((q : ℤ) • 𝟙 Gm) = 0), Mono κ →
  (∀ (U : Scheme.{0}) (ζ : Prim q Γ(U, ⊤)) (u : (Γ(U, ⊤))ˣ), (u : Γ(U, ⊤)) = ζ.1 → Sec.map κ (show Sec ((restr (Int.castRingHom (ZMod q))).obj (tw q 1)) U from twGen 1 ζ) = unitSec u) →
  (∀ (U : Scheme.{0}), IsUnit (q : Γ(U, ⊤)) → ∀ b : Sec Gm U, Sec.map ((q : ℤ) • 𝟙 Gm) b = 0 → ∃ a, Sec.map κ a = b) →
  (∀ (U : Scheme.{0}), IsUnit (q : Γ(U, ⊤)) → ∀ b : Sec Gm U, Loc U fun V g => ∃ c : Sec Gm V, Sec.map ((q : ℤ) • 𝟙 Gm) c = Sec.res g b) →
  (∀ (U : Scheme.{0}), IsUnit (q : Γ(U, ⊤)) → Function.Bijective (Sec.map (cokernel.desc κ ((q : ℤ) • 𝟙 Gm) h0) (U := U))) →
  ∀ (z : Cocycle (res ℤ (cokernel κ)) (res ℤ ((restr (Int.castRingHom (ZMod q))).obj (tw q 1))) 1) (s : ℤˣ),
  (∀ (φ : Gm ⟶ (res ℤ ((restr (Int.castRingHom (ZMod q))).obj (tw q 1))).X 0) (ψ : cokernel κ ⟶ (res ℤ ((restr (Int.castRingHom (ZMod q))).obj (tw q 1))).X 1),
      κ ≫ φ = resι ℤ ((restr (Int.castRingHom (ZMod q))).obj (tw q 1)) → cokernel.π κ ≫ ψ = φ ≫ (res ℤ ((restr (Int.castRingHom (ZMod q))).obj (tw q 1))).d 0 1 →
      ∀ w : Cocycle (sgl (cokernel κ)) (res ℤ ((restr (Int.castRingHom (ZMod q))).obj (tw q 1))) 1, sglι (cokernel κ) ≫ w.1.v 0 1 (zero_add 1) = ψ →
        CohomologyClass.mk (zcomp (Cocycle.ofHom (resAug (cokernel κ))) z (zero_add 1)) = s • CohomologyClass.mk w) →
  ∀ (E : Spc) (L : E ⟶ ofCat (glCat 1)), Inv q E → ∀ y : H ℤ E (cokernel κ) 1,
    HK.post ℤ _ (cokernel.desc κ ((q : ℤ) • 𝟙 Gm) h0) 1 y = picClass L →
    HK.ext ℤ _ z 1 (1 + 1) rfl y = s • restrH (Int.castRingHom (ZMod q)) E (tw q 1) (1 + 1) (c1 q L) := by
  first
  | exact @GlobalTheory.EtC.KumPic.kummer_boundary_picClass
  | exact GlobalTheory.EtC.KumPic.kummer_boundary_picClass
  | (intros; apply GlobalTheory.EtC.KumPic.kummer_boundary_picClass <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.KummerConnectingUnitClassEqKummerClassStatement
section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.kummerConnecting_unitClass_eq_kummerClass : ∀ (q : ℕ) [NeZero q] (κ : (restr (Int.castRingHom (ZMod q))).obj (tw q 1) ⟶ Gm) (h0 : κ ≫ ((q : ℤ) • 𝟙 Gm) = 0), Mono κ →
  (∀ (U : Scheme.{0}) (ζ : Prim q Γ(U, ⊤)) (u : (Γ(U, ⊤))ˣ), (u : Γ(U, ⊤)) = ζ.1 → Sec.map κ (show Sec ((restr (Int.castRingHom (ZMod q))).obj (tw q 1)) U from twGen 1 ζ) = unitSec u) →
  (∀ (U : Scheme.{0}), IsUnit (q : Γ(U, ⊤)) → ∀ b : Sec Gm U, Sec.map ((q : ℤ) • 𝟙 Gm) b = 0 → ∃ a, Sec.map κ a = b) →
  (∀ (U : Scheme.{0}), IsUnit (q : Γ(U, ⊤)) → ∀ b : Sec Gm U, Loc U fun V g => ∃ c : Sec Gm V, Sec.map ((q : ℤ) • 𝟙 Gm) c = Sec.res g b) →
  (∀ (U : Scheme.{0}), IsUnit (q : Γ(U, ⊤)) → Function.Bijective (Sec.map (cokernel.desc κ ((q : ℤ) • 𝟙 Gm) h0) (U := U))) →
  ∀ (z : Cocycle (res ℤ (cokernel κ)) (res ℤ ((restr (Int.castRingHom (ZMod q))).obj (tw q 1))) 1) (s : ℤˣ),
  (∀ (φ : Gm ⟶ (res ℤ ((restr (Int.castRingHom (ZMod q))).obj (tw q 1))).X 0) (ψ : cokernel κ ⟶ (res ℤ ((restr (Int.castRingHom (ZMod q))).obj (tw q 1))).X 1),
      κ ≫ φ = resι ℤ ((restr (Int.castRingHom (ZMod q))).obj (tw q 1)) → cokernel.π κ ≫ ψ = φ ≫ (res ℤ ((restr (Int.castRingHom (ZMod q))).obj (tw q 1))).d 0 1 →
      ∀ w : Cocycle (sgl (cokernel κ)) (res ℤ ((restr (Int.castRingHom (ZMod q))).obj (tw q 1))) 1, sglι (cokernel κ) ≫ w.1.v 0 1 (zero_add 1) = ψ →
        CohomologyClass.mk (zcomp (Cocycle.ofHom (resAug (cokernel κ))) z (zero_add 1)) = s • CohomologyClass.mk w) →
  ∀ (X : Scheme.{0}) (u : (Γ(X, ⊤))ˣ) (c : Sec (cokernel κ) X), IsUnit (q : Γ(X, ⊤)) →
    Sec.map (cokernel.desc κ ((q : ℤ) • 𝟙 Gm) h0) c = unitSec u →
    HK.ext ℤ _ z 0 (0 + 1) rfl (secClass (cokernel κ) c) = s • restrH (Int.castRingHom (ZMod q)) (sch.obj X) (tw q 1) (0 + 1) (kum q u) := by
  first | (exact @GlobalTheory.EtC.KumUnit.kum_connect) | (exact GlobalTheory.EtC.KumUnit.kum_connect) | (intros; apply GlobalTheory.EtC.KumUnit.kum_connect <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LatticeEvaluationSpanDualFinrank
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.CechDR GlobalTheory.CechPer
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.CechPer

theorem span_eval_eq_top_and_finrank_dual : ∀ (W : Type 1) [AddCommGroup W] [Module ℂ W] (Λ : Type) [AddCommGroup Λ] (n : ℕ) (b : Module.Basis (Fin n) ℤ Λ) (P : Λ →+ Module.Dual ℂ W), (∀ w, (∀ l, P l w = 0) → w = 0) → (∀ p : Λ →+ ℂ, ∃ w, ∀ l, P l w = p l) → Submodule.span ℂ (Set.range P) = ⊤ ∧ Module.finrank ℂ (Module.Dual ℂ W) = n := by
  intro W _ _ Λ _ n b P hinj hsurj
  let Φ : W →ₗ[ℂ] (Fin n → ℂ) := LinearMap.pi (fun i => P (b i))
  have hΦ : ∀ w i, Φ w i = P (b i) w := fun w i => rfl
  have h1 : Function.Injective Φ := by
    set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
    intro w hw
    apply hinj
    intro l
    set_option synthInstance.maxHeartbeats 100000 in
      rw [← b.sum_repr l, map_sum, LinearMap.sum_apply]
    refine Finset.sum_eq_zero fun i _ => ?_
    rw [map_zsmul, LinearMap.smul_apply, ← hΦ, hw]
    simp
  have h2 : Function.Surjective Φ := by
    intro v
    obtain ⟨w, hw⟩ := hsurj (b.constr ℤ v).toAddMonoidHom
    refine ⟨w, funext fun i => ?_⟩
    rw [hΦ, hw]
    simp
  let e : W ≃ₗ[ℂ] (Fin n → ℂ) := LinearEquiv.ofBijective Φ ⟨h1, h2⟩
  let c : Module.Basis (Fin n) ℂ W := Module.Basis.ofEquivFun e
  have hc : ∀ i, c.dualBasis i = P (b i) := by
    intro i
    ext w
    rw [Module.Basis.dualBasis_apply]
    exact hΦ w i
  refine ⟨?_, ?_⟩
  · rw [eq_top_iff, ← c.dualBasis.span_eq]
    apply Submodule.span_mono
    rintro _ ⟨i, rfl⟩
    exact ⟨b i, (hc i).symm⟩
  · simpa using Module.finrank_eq_card_basis c.dualBasis

end GlobalTheory.CechPer
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LazardAdditiveLawWittVectorFractionFieldModP
section
open CategoryTheory TensorProduct MvPowerSeries GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup GlobalTheory.Katz

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.Katz.LazardModP

variable (p : ℕ) [Fact p.Prime] (k : Type) [Field k] [CharP k p] [PerfectRing k p]

theorem algebraMap_pow_ne_zero (m : ℕ) :
    algebraMap (WittVector p k) (Fr p k) ((p : WittVector p k) ^ m) ≠ 0 := fun h =>
  pow_ne_zero m (WittVector.p_nonzero p k)
    (IsFractionRing.injective (WittVector p k) (Fr p k) (by rw [h, map_zero]))

theorem coeff_wsmul {σ : Type} (w : WittVector p k) (f : MvPowerSeries σ (Fr p k))
    (α : σ →₀ ℕ) : coeff α (w • f) = algebraMap (WittVector p k) (Fr p k) w * coeff α f := by
  rw [← Algebra.smul_def]; rfl

theorem mem_one_of_p_smul {σ : Type} (f : MvPowerSeries σ (Fr p k))
    (hf : (p : WittVector p k) • f ∈ intBy p k σ (p : WittVector p k)) : f ∈ intBy p k σ 1 := by
  intro α
  obtain ⟨w, hw⟩ := hf α
  refine ⟨w, ?_⟩
  rw [coeff_wsmul, map_mul] at hw
  rw [one_mul]
  have h0 := algebraMap_pow_ne_zero p k 1
  rw [pow_one] at h0
  exact mul_left_cancel₀ h0 hw

theorem exists_pow_smul_mem {d N : ℕ} (e : MvPowerSeries (Fin d ⊕ Fin d) (Fr p k))
    (he : ∀ γ : Fin d ⊕ Fin d →₀ ℕ, γ.degree ≠ N → coeff γ e = 0) :
    ∃ m : ℕ, ((p : WittVector p k) ^ m) • e ∈ intBy p k _ (p : WittVector p k) := by
  classical
  have hfin := Finsupp.finite_of_degree_le (σ := Fin d ⊕ Fin d) N
  obtain ⟨b, hb⟩ := IsLocalization.exist_integer_multiples_of_finset
    (nonZeroDivisors (WittVector p k)) (hfin.toFinset.image fun γ => coeff γ e)
  have hb0 : (b : WittVector p k) ≠ 0 := nonZeroDivisors.coe_ne_zero b
  obtain ⟨n, u, hu⟩ := WittVector.exists_eq_pow_p_mul' (b : WittVector p k) hb0
  refine ⟨n + 1, fun γ => ?_⟩
  by_cases hγ : γ.degree = N
  · have hmem : coeff γ e ∈ hfin.toFinset.image fun γ => coeff γ e :=
      Finset.mem_image.2 ⟨γ, by simp [hγ], rfl⟩
    obtain ⟨w, hw⟩ := hb _ hmem
    refine ⟨((u⁻¹ : (WittVector p k)ˣ) : WittVector p k) * w, ?_⟩
    have hw' : algebraMap (WittVector p k) (Fr p k) w =
        algebraMap (WittVector p k) (Fr p k) (b : WittVector p k) * coeff γ e := by
      rw [hw, Algebra.smul_def]
    have hu1 : algebraMap (WittVector p k) (Fr p k) ((u⁻¹ : (WittVector p k)ˣ) : WittVector p k) *
        algebraMap (WittVector p k) (Fr p k) (u : WittVector p k) = 1 := by
      rw [← map_mul, Units.inv_mul, map_one]
    rw [hu, map_mul, map_pow] at hw'
    rw [coeff_wsmul, map_mul, map_mul, map_pow, pow_succ]
    linear_combination (-algebraMap (WittVector p k) (Fr p k) (p : WittVector p k) *
      algebraMap (WittVector p k) (Fr p k) ((u⁻¹ : (WittVector p k)ˣ) : WittVector p k)) * hw' +
      (-algebraMap (WittVector p k) (Fr p k) (p : WittVector p k) ^ n *
        algebraMap (WittVector p k) (Fr p k) (p : WittVector p k) * coeff γ e) * hu1
  · refine ⟨0, ?_⟩
    rw [coeff_wsmul, he γ hγ]
    simp

theorem lift_addLaw (d : ℕ) :
    (fun i => Katz.lift p (addLaw k d i)) = addLaw (Fr p k) d := by
  funext i
  ext γ
  rw [coeff_lift]
  simp only [addLaw, map_add (f := _), coeff_X]
  by_cases h1 : γ = Finsupp.single (Sum.inl i) 1
  · have h2 : γ ≠ Finsupp.single (Sum.inr i) 1 := by
      rw [h1]; intro h; exact Sum.inl_ne_inr ((Finsupp.single_left_inj one_ne_zero).1 h)
    simp only [if_pos h1, if_neg h2, add_zero, map_one, map_one]
  · by_cases h2 : γ = Finsupp.single (Sum.inr i) 1
    · simp only [if_neg h1, if_pos h2, zero_add, map_one, map_one]
    · simp only [if_neg h1, if_neg h2, add_zero, WittVector.teichmuller_zero, map_zero]

end GlobalTheory.Katz.LazardModP

namespace GlobalTheory.Katz.LazardModP

variable (p : ℕ) [Fact p.Prime] (k : Type) [Field k] [CharP k p] [PerfectRing k p]

theorem step (d N : ℕ) (hN : 2 ≤ N) (m : ℕ) : ∀ e : MvPowerSeries (Fin d ⊕ Fin d) (Fr p k),
    (∀ γ : Fin d ⊕ Fin d →₀ ℕ, γ.degree ≠ N → coeff γ e = 0) →
    cob2 (addLaw (Fr p k) d) e ∈ intBy p k _ (p : WittVector p k) →
    swap e - e ∈ intBy p k _ (p : WittVector p k) →
    ((p : WittVector p k) ^ m) • e ∈ intBy p k _ (p : WittVector p k) →
    ∃ h : MvPowerSeries (Fin d) (Fr p k), (∀ α : Fin d →₀ ℕ, α.degree ≠ N → coeff α h = 0) ∧
      e - cob1 (addLaw (Fr p k) d) h ∈ intBy p k _ (p : WittVector p k) := by
  have hconst : ∀ i, constantCoeff (addLaw (Fr p k) d i) = 0 := fun i => by simp [addLaw]
  have hA := GlobalTheory.T.formalGroupLawCoboundaryTwo_coboundaryOne (Fr p k) d (addLaw (Fr p k) d) hconst 0
  have hlaw : IsLaw (addLaw (Fr p k) d) := hA.2.2.2.2.1
  have hcob0 : cob1 (addLaw (Fr p k) d) 0 = 0 := by
    have := formalCoboundary_smul hconst 0 0
    rwa [zero_smul, zero_smul] at this
  have hR := _root_.GlobalTheory.Katz.red_rules p k (Fin d ⊕ Fin d)
  have hR3 := _root_.GlobalTheory.Katz.red_rules p k (Fin d ⊕ (Fin d ⊕ Fin d))
  have hRC := GlobalTheory.T.reduction_commutes_formalGroupLawCoboundaries p k d (addLaw k d) (fun i => by simp [addLaw])
  rw [lift_addLaw] at hRC
  induction m with
  | zero =>
    intro e _ _ _ hm
    refine ⟨0, fun _ _ => by simp, ?_⟩
    rw [hcob0, sub_zero]
    simpa using hm
  | succ m ih =>
    intro e he hcb hsw hm
    have hsm : ∀ {σ : Type} (x : MvPowerSeries σ (Fr p k)), ((p : WittVector p k) ^ m) • x =
        algebraMap (WittVector p k) (Fr p k) ((p : WittVector p k) ^ m) • x :=
      fun x => (algebraMap_smul (Fr p k) _ x).symm
    have hQ := algebraMap_pow_ne_zero p k m
    rw [pow_succ', mul_smul] at hm
    have he' := mem_one_of_p_smul p k _ hm
    obtain ⟨c, hc⟩ := (hR.1 _).1 he'
    have hcb' : cob2 (addLaw (Fr p k) d) (((p : WittVector p k) ^ m) • e) ∈
        intBy p k _ (p : WittVector p k) := by
      rw [hsm, (hA.2.2.2.1 _ e).1, ← hsm]
      exact Submodule.smul_mem _ _ hcb
    have hsw' : swap (((p : WittVector p k) ^ m) • e) - ((p : WittVector p k) ^ m) • e ∈
        intBy p k _ (p : WittVector p k) := by
      rw [hsm, (hA.2.2.2.1 _ e).2, ← smul_sub, ← hsm]
      exact Submodule.smul_mem _ _ hsw
    obtain ⟨hr2, hrs⟩ := hRC.1 _ _ hc
    have hc2 : cob2 (addLaw k d) c = 0 := hR3.2.1 _ _ _ hr2 ((hR3.2.2.2.2.2.1 _).1 hcb')
    have hcs : swap c = c := sub_eq_zero.1
      (hR.2.1 _ _ _ (hR.2.2.2.1 _ _ _ _ hrs hc).2 ((hR.2.2.2.2.2.1 _).1 hsw'))
    have hch : ∀ γ : Fin d ⊕ Fin d →₀ ℕ, γ.degree ≠ N → coeff γ c = 0 := by
      intro γ hγ
      obtain ⟨w, hw1, hw2⟩ := hc γ
      rw [coeff_wsmul, he γ hγ, mul_zero] at hw1
      have hw0 : w = 0 := IsFractionRing.injective (WittVector p k) (Fr p k) (by rw [← hw1, map_zero])
      rw [← hw2, hw0, map_zero]
    obtain ⟨h', hh', hred⟩ := _root_.GlobalTheory.LazardHomog.homogCoc_red_cob p k d N c hN ⟨hc2, hcs⟩ hch
    have hdiff : ((p : WittVector p k) ^ m) • e - cob1 (addLaw (Fr p k) d) h' ∈
        intBy p k _ (p : WittVector p k) := by
      have := (hR.2.2.2.1 _ _ _ _ hc hred).2
      rw [sub_self] at this
      exact (hR.2.2.2.2.2.1 _).2 this
    have hcobh1 : ((p : WittVector p k) ^ m) • cob1 (addLaw (Fr p k) d)
        ((algebraMap (WittVector p k) (Fr p k) ((p : WittVector p k) ^ m))⁻¹ • h') =
        cob1 (addLaw (Fr p k) d) h' := by
      rw [hsm, ← formalCoboundary_smul hconst, smul_smul, mul_inv_cancel₀ hQ, one_smul]
    have hh1 : ∀ α : Fin d →₀ ℕ, α.degree ≠ N →
        coeff α ((algebraMap (WittVector p k) (Fr p k) ((p : WittVector p k) ^ m))⁻¹ • h') = 0 := by
      intro α hα
      rw [coeff_smul, hh' α hα, mul_zero]
    have hcoc := (GlobalTheory.T.formalGroupLawCoboundaryTwo_coboundaryOne (Fr p k) d (addLaw (Fr p k) d) hconst
      ((algebraMap (WittVector p k) (Fr p k) ((p : WittVector p k) ^ m))⁻¹ • h')).2.2.2.2.2 hlaw
    obtain ⟨h2, hh2, hfin⟩ := ih (e - cob1 (addLaw (Fr p k) d)
        ((algebraMap (WittVector p k) (Fr p k) ((p : WittVector p k) ^ m))⁻¹ • h'))
      (fun γ hγ => by
        rw [map_sub, he γ hγ, (_root_.GlobalTheory.homog_cob_addLaw (Fr p k) d N).1 _ hh1 γ hγ, sub_zero])
      (by rw [((hA.2.2.1) e _).2.1, hcoc.1, sub_zero]; exact hcb)
      (by
        rw [((hA.2.2.1) e _).2.2, hcoc.2]
        convert hsw using 1
        abel)
      (by rw [smul_sub, hcobh1]; exact hdiff)
    refine ⟨(algebraMap (WittVector p k) (Fr p k) ((p : WittVector p k) ^ m))⁻¹ • h' + h2,
      fun α hα => by rw [map_add (f := _), hh1 α hα, hh2 α hα, add_zero], ?_⟩
    rw [formalCoboundary_add hconst]
    convert hfin using 1
    abel

end GlobalTheory.Katz.LazardModP

namespace GlobalTheory.Katz

theorem lazard_mod_p_frac : ∀ (p : ℕ) [Fact p.Prime] (k : Type) [Field k] [CharP k p]
    [PerfectRing k p] (d N : ℕ) (e : MvPowerSeries (Fin d ⊕ Fin d) (Fr p k)), 2 ≤ N →
    (∀ γ : Fin d ⊕ Fin d →₀ ℕ, γ.degree ≠ N → coeff γ e = 0) →
    cob2 (addLaw (Fr p k) d) e ∈ intBy p k _ p → swap e - e ∈ intBy p k _ p →
    ∃ h : MvPowerSeries (Fin d) (Fr p k), (∀ α : Fin d →₀ ℕ, α.degree ≠ N → coeff α h = 0) ∧
      e - cob1 (addLaw (Fr p k) d) h ∈ intBy p k _ p := by
  intro p _ k _ _ _ d N e hN he hcb hsw
  obtain ⟨m, hm⟩ := LazardModP.exists_pow_smul_mem p k e he
  exact LazardModP.step p k d N hN m e he hcb hsw hm

end GlobalTheory.Katz
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LeviWhittakerEqOneOfCuspidalStatement
section
open GlobalTheory.FinGL Formalism.L2.DIV Module
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.levi_whittaker_eq_one_of_cuspidal : ∀ (F : Type) [Field F] [Fintype F] (ψ : AddChar F ℂ), ψ ≠ 1 → ∀ (r : ℕ) (V : Type) [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V] (b : Fin r → ℕ) (σ : Representation ℂ (blockTri (κ := F) b) V), IsCuspDatum b σ → leviWh ψ b σ = 1 := by
  first | exact @GlobalTheory.FinGL.LeviWh.leviWh_eq_one | exact GlobalTheory.FinGL.LeviWh.leviWh_eq_one | (intros; apply GlobalTheory.FinGL.LeviWh.leviWh_eq_one <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MaximalIdealAffineOpenEqVanishingUniformisationP
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.CechDR GlobalTheory.CechPer
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.MaxPoints

theorem main : ∀ (A : Over (Sp ℂ)) [GrpObj A] (g : ℕ) (L : LB A.left) (u : HolUnif A L g), IsAbelianScheme A →
    ∀ (U : A.left.Opens), IsAffineOpen U → ∀ m : Ideal Γ(A.left, U), m.IsMaximal →
      ∃ z ∈ pre u.ex U, ∀ b, b ∈ m ↔ val u.ex U b z = 0 := by
  intro A _ g L u hA U hU m hm
  haveI : Smooth A.hom := hA.smooth
  have hft : LocallyOfFiniteType A.hom := inferInstance
  let c : ℂ →+* Γ(A.left, U) :=
    ((Scheme.ΓSpecIso (CommRingCat.of ℂ)).inv ≫ A.hom.appLE ⊤ U (fun _ _ => trivial)).hom
  have hc : c.FiniteType := by
    have h1 : (A.hom.appLE ⊤ U (fun _ _ => trivial)).hom.FiniteType :=
      HasRingHomProperty.appLE @LocallyOfFiniteType A.hom hft ⟨⊤, isAffineOpen_top _⟩ ⟨U, hU⟩ _
    exact h1.comp (RingHom.FiniteType.of_surjective _
      (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (CommRingCat.of ℂ)).inv).2)
  letI : Algebra ℂ Γ(A.left, U) := c.toAlgebra
  haveI : Algebra.FiniteType ℂ Γ(A.left, U) := hc
  haveI : IsJacobsonRing Γ(A.left, U) := isJacobsonRing_of_finiteType (A := ℂ)
  letI : Field (Γ(A.left, U) ⧸ m) := Ideal.Quotient.field m
  haveI : Module.Finite ℂ (Γ(A.left, U) ⧸ m) := finite_of_finite_type_of_isJacobsonRing ℂ (Γ(A.left, U) ⧸ m)
  have hb : Function.Bijective (algebraMap ℂ (Γ(A.left, U) ⧸ m)) :=
    IsAlgClosed.algebraMap_bijective_of_isIntegral
  let i : ℂ ≃ₐ[ℂ] (Γ(A.left, U) ⧸ m) := AlgEquiv.ofBijective (Algebra.ofId ℂ _) hb
  let e : Γ(A.left, U) →ₐ[ℂ] ℂ := (i.symm : (Γ(A.left, U) ⧸ m) →ₐ[ℂ] ℂ).comp (Ideal.Quotient.mkₐ ℂ m)
  have he : ∀ a, e.toRingHom (constFn A.hom U a) = a := fun a => e.commutes a
  obtain ⟨x, ⟨hxU, hx⟩, -⟩ := GlobalTheory.existsUnique_point_of_ringHom A U hU e.toRingHom he
  obtain ⟨z, rfl⟩ := u.ex_onto x
  refine ⟨z, hxU, fun b => ?_⟩
  change b ∈ m ↔ valAt' (u.ex z).left U b = 0
  rw [hx b]
  change b ∈ m ↔ i.symm (Ideal.Quotient.mk m b) = 0
  rw [← map_zero i.symm, i.symm.injective.eq_iff, Ideal.Quotient.eq_zero_iff_mem]

end GlobalTheory.MaxPoints
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PeriodComparisonOfGaussManinPeriods
section
set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.PeriodFamily

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.PeriodFamily

theorem periodComparison_of_gaussManinPeriods (h : GlobalTheory.Published.GaussManinPeriods) : GlobalTheory.Published.PeriodComparison := by
  obtain ⟨ε, h⟩ := h
  refine ⟨ε, fun A _ g hA hs L hL u ↦ ?_⟩
  have hp : IsGrpPullback A A (spMap ((AlgHom.id ℂ ℂ : ℂ →ₐ[ℂ] ℂ) : ℂ →+* ℂ)) (𝟙 _) :=
    haveI : IsMonHom (Iso.refl A).hom := inferInstanceAs (IsMonHom (𝟙 A))
    (isGrpPullback_of_iso (Iso.refl A)).congr (Cris.spMap_id ℂ).symm rfl
  obtain ⟨V, u', τ, Q', Q, -, -, -, hQ, -⟩ := h ℂ A g hA hs Empty Set.univ (fun _ ↦ AlgHom.id ℂ ℂ)
    isOpen_univ trivial (fun _ ↦ differentiableOn_const _) (fun _ ↦ A) (fun _ ↦ 𝟙 _) (fun _ ↦ hp)
    (fun _ ↦ GrpMor.of_isGrpPullback (isDPMorphism_of_eq_bot _ rfl _ _) (by simp) hp) (fun _ ↦ L) (fun _ ↦ hL)
    A (𝟙 _) hp L hL u
  exact ⟨Q, hQ⟩

end GlobalTheory.PeriodFamily
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ProIsometryOfLocalIsometries
section
open CategoryTheory Limits AlgebraicGeometry Opposite Simplicial GlobalTheory.EtC GlobalTheory.EtC.GmStep

namespace GlobalTheory.EtC.GmStep

theorem cech_level_acyc : ∀ (q : ℕ) [NeZero q] (A : Type) [CommRing A], SH A → IsUnit (q : A) → ∀ (A' : Type) [CommRing A'] [Algebra A A'],
  Module.Finite A A' → ∀ (k : ℕ) (s i : ℤ), 0 < s → Subsingleton (Ht q (disc.obj ((cech (baseHom A A')).obj (op ⦋k⦌))) s i) := by
  intro q _ A _ hA hq A' _ _ hfin k s i hs
  obtain ⟨e0, -, -, -⟩ := GlobalTheory.T.laurentCechNerve_level_spec_tensorPower A A' k
  haveI : Subsingleton (Ht q (sp (PiTensorProduct A (fun _ : Fin (k + 1) => A'))) s i) :=
    GlobalTheory.T.finite_strictlyHenselian_tateTwist_acyclic q A hA hq _ inferInstance s i hs
  let f : sp (PiTensorProduct A (fun _ : Fin (k + 1) => A')) ⟶ disc.obj ((cech (baseHom A A')).obj (op ⦋k⦌)) :=
    disc.map e0.hom
  let g : disc.obj ((cech (baseHom A A')).obj (op ⦋k⦌)) ⟶ sp (PiTensorProduct A (fun _ : Fin (k + 1) => A')) :=
    disc.map e0.inv
  have hgf : g ≫ f = 𝟙 _ := by
    exact (disc.mapIso e0).inv_hom_id
  have hinj : Function.Injective (pull (ZMod q) f (tw q i) s) := by
    intro x y hxy
    have := congrArg (pull (ZMod q) g (tw q i) s) hxy
    rwa [← pull_comp, ← pull_comp, hgf, pull_id, pull_id] at this
  exact hinj.subsingleton

end GlobalTheory.EtC.GmStep
end

