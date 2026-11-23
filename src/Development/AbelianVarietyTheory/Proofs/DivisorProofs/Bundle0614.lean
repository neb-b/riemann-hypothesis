module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0584
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsRetractionMulP
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConvEqOneOfForallPairing
public import Development.AbelianVarietyTheory.Definitions.Divisors.EqZeroOfForallPowDvd
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0597
public import Development.AbelianVarietyTheory.Definitions.KeyFormula.GeomIntSelf
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0041
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0016
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0017
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0585
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0573
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0010
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0586
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0537
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0015
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0569
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0572

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsHopfQuotientTorsionIdealStatement
section
open CategoryTheory Coalgebra GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup GlobalTheory.HTPair
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_hopf_quotient_ker_eq_torsionIdeal :
    ∀ (O : Type) [CommRing O] (B : Type) [CommRing B] [HopfAlgebra O B] [IsCocomm O B] (n : ℕ),
      ∃ (D : Type) (_ : CommRing D) (_ : HopfAlgebra O D) (_ : IsCocomm O D) (π : B →ₐc[O] D),
        Function.Surjective π ∧ RingHom.ker π = torsionIdeal (R := O) (A := B) n := by
  intro O _ B _ _ _ n
  let I := torsionIdeal (R := O) (A := B) n
  have : I.IsHopfIdeal O :=
    isHopfIdeal_kerIdeal_of_bialgHom O B B (mulBy (R := O) (A := B) n)
  let π : B →ₐc[O] B ⧸ I := Bialgebra.Quotient.mkBialgHom I
  have hπ : Function.Surjective π := Ideal.Quotient.mk_surjective
  have cocomm : IsCocomm O (B ⧸ I) := by
    constructor
    ext b
    obtain ⟨a, rfl⟩ := hπ b
    change TensorProduct.comm O (B ⧸ I) (B ⧸ I) (comul (π a)) = comul (π a)
    rw [← CoalgHomClass.map_comp_comul_apply π a, ← TensorProduct.map_comm, comm_comul]
  exact ⟨B ⧸ I, inferInstance, inferInstance, cocomm, π, hπ,
    Ideal.ext fun _ => Ideal.Quotient.eq_zero_iff_mem⟩
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIntegralCoboundaryOneCongrFrobenius
section
open MvPowerSeries GlobalTheory GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta GlobalTheory.PDivLat

namespace GlobalTheory.SmallSecondRoot

theorem charP_mvPowerSeries (σ k : Type) [Field k] (p : ℕ) [CharP k p] :
    CharP (MvPowerSeries σ k) p :=
  charP_of_injective_algebraMap (algebraMap k (MvPowerSeries σ k)).injective p

theorem coeff_pow_char_sum {σ k : Type} [DecidableEq σ] [Field k] (p : ℕ) [Fact p.Prime] [CharP k p]
    (f : MvPowerSeries σ k) (α : σ →₀ ℕ) :
    coeff α (f ^ p) = ∑ m ∈ Finset.Iic α, if α = p • m then coeff m f ^ p else 0 := by
  classical
  haveI := charP_mvPowerSeries σ k p
  have hp0 : p ≠ 0 := (Fact.out : p.Prime).ne_zero
  set P : MvPowerSeries σ k := ∑ m ∈ Finset.Iic α, monomial m (coeff m f)
  set g := f - P
  have hg : ∀ m ≤ α, coeff m g = 0 := by
    intro m hm
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [g, P, map_sub, map_sum, coeff_monomial]
    rw [Finset.sum_eq_single m]
    · simp
    · intro b _ hb; simp [Ne.symm hb]
    · intro h; exact absurd (Finset.mem_Iic.2 hm) h
  have hmul : ∀ h : MvPowerSeries σ k, coeff α (h * g) = 0 := by
    intro h
    rw [coeff_mul]
    refine Finset.sum_eq_zero fun q hq => ?_
    have hq' := Finset.HasAntidiagonal.mem_antidiagonal.1 hq
    rw [hg q.2 (hq' ▸ le_add_self), mul_zero]
  have hf : f = P + g := by simp [g]
  have hgp : coeff α (g ^ p) = 0 := by
    obtain ⟨n, hn⟩ := Nat.exists_eq_succ_of_ne_zero hp0
    rw [hn, pow_succ]; exact hmul _
  rw [show f ^ p = (P + g) ^ p from congrArg (· ^ p) hf, add_pow_char, map_add (f := _), hgp, add_zero]
  simp only [P]
  set_option synthInstance.maxHeartbeats 100000 in
    rw [sum_pow_char, map_sum]
  simp only [monomial_pow, coeff_monomial]

theorem coeff_smul_pow_char {σ k : Type} [DecidableEq σ] [Field k] (p : ℕ) [Fact p.Prime] [CharP k p]
    (f : MvPowerSeries σ k) (β : σ →₀ ℕ) : coeff (p • β) (f ^ p) = coeff β f ^ p := by
  classical
  have hp0 : p ≠ 0 := (Fact.out : p.Prime).ne_zero
  rw [coeff_pow_char_sum, Finset.sum_eq_single β]
  · rw [if_pos rfl]
  · intro b _ hb
    rw [if_neg]
    intro hα
    exact hb (smul_right_injective _ hp0 hα).symm
  · intro hn
    exact absurd (Finset.mem_Iic.2 (le_smul_of_one_le_left zero_le (Nat.one_le_iff_ne_zero.2 hp0))) hn

theorem coeff_pow_char_of_not {σ k : Type} [DecidableEq σ] [Field k] (p : ℕ) [Fact p.Prime] [CharP k p]
    (f : MvPowerSeries σ k) (α : σ →₀ ℕ) (h : ¬∃ β, p • β = α) : coeff α (f ^ p) = 0 := by
  classical
  rw [coeff_pow_char_sum]
  refine Finset.sum_eq_zero fun b _ => ?_
  rw [if_neg]
  intro hα; exact h ⟨b, hα.symm⟩

end GlobalTheory.SmallSecondRoot

namespace GlobalTheory.SmallSecondRoot

theorem exists_integral_cob1_congr_of_frobenius_congr : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (O : Type) [CommRing O] [Algebra O C] [Fact ¬IsUnit (p : O)] [IsAdicComplete (Ideal.span {(p : O)}) O] [IsDomain O], v.Integers O → ∀ (d : ℕ) (μ : Fin d → MvPowerSeries (Fin d ⊕ Fin d) O), IsLaw μ → ∀ (c : MvPowerSeries (Fin d ⊕ Fin d) O) (t : MvPowerSeries (Fin d) O), (∀ α : Fin d →₀ ℕ, (∃ i, ¬ p ∣ α i) → ¬IsUnit (coeff α t)) → (∀ β : Fin d ⊕ Fin d →₀ ℕ, ¬IsUnit (coeff (p • β) (cob1 μ t) - coeff β c ^ p)) → ∃ u : MvPowerSeries (Fin d) O, ∀ α, ¬IsUnit (coeff α c - coeff α (cob1 μ u)) := by
  intro p _ C _ _ _ v O _ _ _ _ _ hv d μ hμ c t ht hct
  classical
  haveI : ValuationRing O := ValuationRing.of_integers v hv
  have hp0 : p ≠ 0 := (Fact.out : p.Prime).ne_zero
  have hroot : ∀ a : O, ∃ r : O, r ^ p = a := by
    intro a
    obtain ⟨z, hz⟩ := IsAlgClosed.exists_pow_nat_eq (algebraMap O C a) (Nat.pos_of_ne_zero hp0)
    have h1 : v z ≤ 1 := by
      have : v z ^ p ≤ 1 := by rw [← map_pow, hz]; exact hv.map_le_one a
      exact (pow_le_one_iff_of_nonneg zero_le hp0).1 this
    obtain ⟨r, hr⟩ := hv.exists_of_le_one h1
    exact ⟨r, hv.hom_inj (by rw [map_pow, hr, hz])⟩
  choose rt hrt using hroot
  let u : MvPowerSeries (Fin d) O := fun β => rt (coeff (p • β) t)
  have hu : ∀ β, coeff β u = rt (coeff (p • β) t) := fun β => rfl
  refine ⟨u, fun α => ?_⟩
  let res := IsLocalRing.residue O
  have hres : ∀ x : O, ¬ IsUnit x ↔ res x = 0 := fun x => by
    rw [IsLocalRing.residue_eq_zero_iff, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
  haveI : CharP (IsLocalRing.ResidueField O) p :=
    (CharP.charP_iff_prime_eq_zero Fact.out).2 (by rw [← map_natCast res, ← hres]; exact Fact.out)
  have hμb : ∀ i, constantCoeff (map res (μ i)) = 0 := fun i => by
    rw [← coeff_zero_eq_constantCoeff_apply, coeff_map, coeff_zero_eq_constantCoeff_apply,
      hμ.const i, map_zero]
  have ht' : map res t = (map res u) ^ p := by
    ext γ
    rw [coeff_map]
    by_cases h : ∃ β, p • β = γ
    · obtain ⟨β, rfl⟩ := h
      rw [coeff_smul_pow_char, coeff_map, hu, ← map_pow, hrt]
    · rw [coeff_pow_char_of_not _ _ _ h, ← hres]
      apply ht
      by_contra hall
      push_neg at hall
      refine h ⟨Finsupp.mapRange (· / p) (Nat.zero_div p) γ, ?_⟩
      ext i
      simp [Nat.mul_div_cancel' (hall i)]
  have hcob : map res (cob1 μ t) = (cob1 (fun i => map res (μ i)) (map res u)) ^ p := by
    haveI := charP_mvPowerSeries (Fin d ⊕ Fin d) (IsLocalRing.ResidueField O) p
    rw [SmallSecond.map_formalGroupLawCoboundaryOne_eq res μ hμ.const, ht']
    unfold cob1 inL inR
    rw [subst_pow (hasSubst_of_constantCoeff_zero hμb),
      subst_pow (hasSubst_of_constantCoeff_zero fun _ => constantCoeff_X _),
      subst_pow (hasSubst_of_constantCoeff_zero fun _ => constantCoeff_X _), sub_pow_char,
      sub_pow_char]
  have h1 := (hres _).1 (hct α)
  rw [map_sub, sub_eq_zero, ← coeff_map, hcob, coeff_smul_pow_char, map_pow] at h1
  have h3 : coeff α (cob1 (fun i => map res (μ i)) (map res u)) = res (coeff α c) :=
    frobenius_inj _ p h1
  rw [hres, map_sub, sub_eq_zero, ← h3, ← SmallSecond.map_formalGroupLawCoboundaryOne_eq res μ hμ.const, coeff_map]

end GlobalTheory.SmallSecondRoot
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLatticeLiftOfLevelSection
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.ZM GlobalTheory.KeyFam

namespace GlobalTheory.LevelLift

theorem exists_linear_lift {J G V : Type} [Fintype J] [DecidableEq J] [Group G] [AddCommGroup V] [Module ℂ V]
    (ex : V → G) (hadd : ∀ z w, ex (z + w) = ex z * ex w) (honto : Function.Surjective ex)
    (Λ : Submodule ℤ V) (hker : ∀ z, ex z = 1 ↔ z ∈ Λ) (k : ℕ) (hk : 0 < k) (lev : (J → ℤ) → G)
    (hl : ∀ a b, lev (a + b) = lev a * lev b) (hp : ∀ a, lev a ^ k = 1) :
    ∃ l : (J → ℤ) →ₗ[ℤ] Λ, ∀ a, lev a = ex ((k : ℂ)⁻¹ • (l a : V)) := by
  have hk' : (k : ℂ) ≠ 0 := Nat.cast_ne_zero.2 hk.ne'
  let E : V →+ Additive G := AddMonoidHom.mk' (fun z => Additive.ofMul (ex z)) (fun z w => by
    rw [hadd]; rfl)
  let F : (J → ℤ) →+ Additive G := AddMonoidHom.mk' (fun z => Additive.ofMul (lev z)) (fun z w => by
    rw [hl]; rfl)
  choose z hz using fun j : J => honto (lev (Pi.single j 1))
  have hw : ∀ j, k • z j ∈ Λ := fun j => by
    rw [← hker]
    have h1 : E (k • z j) = k • E (z j) := map_nsmul E k (z j)
    have h2 : ex (k • z j) = ex (z j) ^ k := congrArg Additive.toMul h1
    rw [h2, hz, hp]
  let l : (J → ℤ) →ₗ[ℤ] Λ := (Pi.basisFun ℤ J).constr ℤ fun j => ⟨k • z j, hw j⟩
  have hlj : ∀ j, (l (Pi.single j 1) : V) = k • z j := fun j => by
    have := (Pi.basisFun ℤ J).constr_basis ℤ (fun j => (⟨k • z j, hw j⟩ : Λ)) j
    rw [Pi.basisFun_apply] at this
    exact congrArg Subtype.val this
  let F' : (J → ℤ) →+ Additive G := AddMonoidHom.mk' (fun a => E ((k : ℂ)⁻¹ • (l a : V))) (fun a b => by
    rw [map_add (f := _), Submodule.coe_add, smul_add, map_add (f := _)])
  refine ⟨l, fun a => ?_⟩
  have hmem : a ∈ F.eqLocus F' := by
    have ha : a = ∑ j, a j • (Pi.single j 1 : J → ℤ) := by
      funext i
      simp [Finset.sum_apply, Pi.single_apply]
    rw [ha]
    refine AddSubgroup.sum_mem _ fun j _ => AddSubgroup.zsmul_mem _ ?_ _
    show Additive.ofMul (lev (Pi.single j 1)) = Additive.ofMul (ex ((k : ℂ)⁻¹ • (l (Pi.single j 1) : V)))
    rw [hlj, ← Nat.cast_smul_eq_nsmul ℂ, smul_smul, inv_mul_cancel₀ hk', one_smul, hz]
  exact congrArg Additive.toMul (show F a = F' a from hmem)

theorem dvd_sub_of_exp_eq (k : ℕ) (hk : 0 < k) (m n : ℤ)
    (h : Complex.exp (-(2 * Real.pi * Complex.I) * (m : ℂ) / k) =
      Complex.exp (-(2 * Real.pi * Complex.I) * (n : ℂ) / k)) : (k : ℤ) ∣ n - m := by
  have hk' : (k : ℂ) ≠ 0 := Nat.cast_ne_zero.2 hk.ne'
  obtain ⟨c, hc⟩ := Complex.exp_eq_exp_iff_exists_int.1 h
  refine ⟨c, ?_⟩
  have h2 : (2 * Real.pi * Complex.I : ℂ) ≠ 0 := Complex.two_pi_I_ne_zero
  have : ((n - m : ℤ) : ℂ) = ((k * c : ℤ) : ℂ) := by
    push_cast
    apply mul_left_cancel₀ h2
    field_simp at hc
    have hpi : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
    first
      | linear_combination (2 * Real.pi * Complex.I) * hc
      | linear_combination -(2 * Real.pi * Complex.I) * hc
      | linear_combination hc
      | linear_combination -hc
  exact_mod_cast this

theorem exists_lattice_lift : ∀ (h k : ℕ) (P : Out.PolAV (Sp ℂ)) (lev : (Fin h ⊕ Fin h → ℤ) → (𝟙_ (Over (Sp ℂ)) ⟶ P.A)) (u : HolUnif P.A P.L h) (Ef : LinearMap.BilinForm ℤ u.Λ), 0 < k → (∀ a b, lev (a + b) = lev a * lev b) → (∀ a, lev a ^ k = 1) → (∀ (a b : Fin h ⊕ Fin h → ℤ) (e : ℂˣ), (e : ℂ) = Complex.exp (-(2 * Real.pi * Complex.I) * (omegaStd a b : ℂ) / k) → Out.WeilIs P.A P.L k (lev a) (lev b) (unitOn e)) → (∀ (x y : u.Λ) (e : ℂˣ), (e : ℂ) = Complex.exp (-(2 * Real.pi * Complex.I) * (Ef x y : ℂ) / k) → Out.WeilIs P.A P.L k (u.ex ((k : ℂ)⁻¹ • (x : Fin h → ℂ))) (u.ex ((k : ℂ)⁻¹ • (y : Fin h → ℂ))) (unitOn e)) → ∃ l : (Fin h ⊕ Fin h → ℤ) →ₗ[ℤ] u.Λ, (∀ a, lev a = u.ex ((k : ℂ)⁻¹ • (l a : Fin h → ℂ))) ∧ ∀ a b, (k : ℤ) ∣ Ef (l a) (l b) - omegaStd a b := by
  intro h k P lev u Ef hk hl hp hW hE
  obtain ⟨l, hlift⟩ := exists_linear_lift u.ex u.ex_add u.ex_onto u.Λ u.ker k hk lev hl hp
  refine ⟨l, hlift, fun a b => ?_⟩
  have h1 := hW a b (Units.mk0 _ (Complex.exp_ne_zero _)) rfl
  have h2 := hE (l a) (l b) (Units.mk0 _ (Complex.exp_ne_zero _)) rfl
  rw [← hlift a, ← hlift b] at h2
  have h3 := GlobalTheory.weilIs_unique_fieldPoint _ P.A P.L P.isLB ℂ (𝟙 _) k (lev a) (lev b) _ _ h1 h2
  exact dvd_sub_of_exp_eq k hk _ _ (congrArg Units.val h3)

end GlobalTheory.LevelLift
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLevGrp
section
noncomputable section

namespace GlobalTheory.UPel.HT.EtLev.Cmp

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.EtLev

variable {p : ℕ} [Fact p.Prime] {D : Datum p} {R : Type} [CommRing R] {b : Base D R} {N : ℕ}
  {k : Type} [Field k] [IsAlgClosed k] {s : Sp k ⟶ Sp R} {o : Obj b N s} {w0 : Ideal (𝓞 D.F)} {r : ℕ}

theorem cancel_pt {X : Over (Sp k)} {f g : 𝟙_ (Over (Sp k)) ⟶ X}
    (h : toUnit (Over.mk (𝟙 (Sp k))) ≫ f = toUnit (Over.mk (𝟙 (Sp k))) ≫ g) : f = g := by
  have hi : (Over.mkIdTerminal (X := Sp k)).from (𝟙_ (Over (Sp k))) ≫ toUnit (Over.mk (𝟙 (Sp k))) = 𝟙 _ :=
    toUnit_unique _ _
  calc f = ((Over.mkIdTerminal (X := Sp k)).from (𝟙_ (Over (Sp k))) ≫ toUnit (Over.mk (𝟙 (Sp k)))) ≫ f := by
        rw [hi, Category.id_comp]
    _ = g := by rw [Category.assoc, h, ← Category.assoc, hi, Category.id_comp]

section lev
variable {lv : D.La → (𝟙_ (Over (Sp k)) ⟶ o.A)}

theorem pt_add (h : IsEtLev o w0 r lv) (x y : D.La) :
    toUnit (Over.mk (𝟙 (Sp k))) ≫ lv (x + y) =
      (toUnit (Over.mk (𝟙 (Sp k))) ≫ lv x) * (toUnit (Over.mk (𝟙 (Sp k))) ≫ lv y) := by
  rw [h.1, MonObj.comp_mul]

theorem pt_mem (h : IsEtLev o w0 r lv) {x : D.La} (hx : x ∈ wSub D w0 r) :
    toUnit (Over.mk (𝟙 (Sp k))) ≫ lv x = 1 := by
  rw [h.2.2.1 x hx, MonObj.comp_one]

theorem pt_smul (h : IsEtLev o w0 r lv) (a : D.O) (x : D.La) :
    toUnit (Over.mk (𝟙 (Sp k))) ≫ lv (a • x) = (toUnit (Over.mk (𝟙 (Sp k))) ≫ lv x) ≫ o.act.act a := by
  rw [h.2.1, Category.assoc]

theorem pt_inj (h : IsEtLev o w0 r lv) {x y : D.La}
    (hxy : toUnit (Over.mk (𝟙 (Sp k))) ≫ lv x = toUnit (Over.mk (𝟙 (Sp k))) ≫ lv y) : x - y ∈ wSub D w0 r := by
  apply (h.2.2.2 k (𝟙 (Sp k))).1
  have h0 : toUnit (Over.mk (𝟙 (Sp k))) ≫ lv 0 = 1 := pt_mem h (Submodule.zero_mem _)
  calc toUnit (Over.mk (𝟙 (Sp k))) ≫ lv (x - y)
      = (toUnit (Over.mk (𝟙 (Sp k))) ≫ lv (x - y)) * (toUnit (Over.mk (𝟙 (Sp k))) ≫ lv (y + -y)) := by
        rw [add_neg_cancel, h0, _root_.mul_one]
    _ = (toUnit (Over.mk (𝟙 (Sp k))) ≫ lv (x - y + y)) * (toUnit (Over.mk (𝟙 (Sp k))) ≫ lv (-y)) := by
        rw [pt_add h, pt_add h, _root_.mul_assoc]
    _ = (toUnit (Over.mk (𝟙 (Sp k))) ≫ lv (y + -y)) := by
        rw [sub_add_cancel, hxy, pt_add h]
    _ = 1 := by rw [add_neg_cancel, h0]

theorem pt_killed (h : IsEtLev o w0 r lv) (y : D.La) :
    ∀ c ∈ w0 ^ r, (toUnit (Over.mk (𝟙 (Sp k))) ≫ lv y) ≫ o.act.act (algebraMap (𝓞 D.F) D.O c) = 1 := by
  intro c hc
  rw [← pt_smul h]
  exact pt_mem h (Submodule.subset_span ⟨c, hc, y, rfl⟩)

end lev

theorem exists_levGrp {l₁ l₂ : D.La → (𝟙_ (Over (Sp k)) ⟶ o.A)} (h₁ : IsEtLev o w0 r l₁)
    (h₂ : IsEtLev o w0 r l₂) : ∃ g : LevGrp D w0 r, ∀ y, l₁ y = l₂ (liftAct g y) := by
  have hz : ∀ y, ∃ z, toUnit (Over.mk (𝟙 (Sp k))) ≫ l₂ z = toUnit (Over.mk (𝟙 (Sp k))) ≫ l₁ y :=
    fun y => (h₂.2.2.2 k (𝟙 (Sp k))).2 _ (pt_killed h₁ y)
  choose z hz using hz
  let ψ : D.La →ₗ[D.O] D.La ⧸ wSub D w0 r :=
    { toFun := fun y => Submodule.Quotient.mk (z y)
      map_add' := fun x y => by
        rw [← Submodule.Quotient.mk_add, Submodule.Quotient.eq]
        apply pt_inj h₂
        rw [hz, pt_add h₁, pt_add h₂, hz, hz]
      map_smul' := fun a y => by
        rw [RingHom.id_apply, ← Submodule.Quotient.mk_smul, Submodule.Quotient.eq]
        apply pt_inj h₂
        rw [hz, pt_smul h₁, pt_smul h₂, hz] }
  have hker : wSub D w0 r ≤ LinearMap.ker ψ := fun y hy => by
    rw [LinearMap.mem_ker]
    show Submodule.Quotient.mk (z y) = 0
    rw [Submodule.Quotient.mk_eq_zero]
    have := pt_inj h₂ (x := z y) (y := 0) (by rw [hz, pt_mem h₁ hy, pt_mem h₂ (Submodule.zero_mem _)])
    simpa using this
  let F := (wSub D w0 r).liftQ ψ hker
  have hF : ∀ y, F (Submodule.Quotient.mk y) = Submodule.Quotient.mk (z y) := fun y => rfl
  have inj : Function.Injective F := by
    set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
    intro q hq
    obtain ⟨y, rfl⟩ := Submodule.Quotient.mk_surjective _ q
    rw [hF, Submodule.Quotient.mk_eq_zero] at hq
    rw [Submodule.Quotient.mk_eq_zero]
    apply (h₁.2.2.2 k (𝟙 (Sp k))).1
    rw [← hz, pt_mem h₂ hq]
  have surj : Function.Surjective F := by
    intro q
    obtain ⟨w, rfl⟩ := Submodule.Quotient.mk_surjective _ q
    obtain ⟨y, hy⟩ := (h₁.2.2.2 k (𝟙 (Sp k))).2 _ (pt_killed h₂ w)
    refine ⟨Submodule.Quotient.mk y, ?_⟩
    rw [hF, Submodule.Quotient.eq]
    apply pt_inj h₂
    rw [hz, hy]
  refine ⟨LinearEquiv.ofBijective F ⟨inj, surj⟩, fun y => ?_⟩
  rw [h₂.congr_mk (x := liftAct _ y) (y := z y) (by rw [mk_liftAct]; rfl)]
  exact cancel_pt (hz y).symm

end GlobalTheory.UPel.HT.EtLev.Cmp
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLiftLocalPointAlongAffineFlatSurjection
section
open AlgebraicGeometry CategoryTheory Limits
open ReciprocityTheory.ChartRestriction.G.Geo.Tor

namespace GlobalTheory.LiftLocal

theorem toStalk_bijective (R : Type) [CommRing R] [IsLocalRing R] (q : PrimeSpectrum R)
    (hq : q = IsLocalRing.closedPoint R) : Function.Bijective (StructureSheaf.toStalk R q).hom := by
  subst hq
  let e := IsLocalization.atUnits R (IsLocalRing.closedPoint R).asIdeal.primeCompl
    (S := (Spec.structureSheaf R).presheaf.stalk (IsLocalRing.closedPoint R)) (fun y hy => by
      rw [IsUnit.mem_submonoid_iff]
      by_contra h
      exact hy ((IsLocalRing.mem_maximalIdeal y).mpr h))
  have : ⇑(StructureSheaf.toStalk R (IsLocalRing.closedPoint R)).hom = ⇑e :=
    funext fun r => (e.commutes r).symm
  rw [this]
  exact e.bijective

theorem isLocalHom_of_bijective {A B : Type} [CommRing A] [CommRing B] (f : A →+* B)
    (hf : Function.Bijective f) : IsLocalHom f :=
  ⟨fun a ha => by
    have h2 : (RingEquiv.ofBijective f hf).symm (f a) = a := (RingEquiv.ofBijective f hf).symm_apply_apply a
    rw [← h2]
    exact ha.map _⟩

theorem lift : ∀ (R : Type) [CommRing R] [IsLocalRing R] (X Y : Scheme.{0}) (π : Y ⟶ X) [IsAffineHom π] [Flat π]
    [Surjective π] (x : Sp R ⟶ X), ∃ (R' : Type) (_ : CommRing R') (_ : IsLocalRing R') (φ : R →+* R'),
    IsLocalHom φ ∧ Function.Injective φ ∧ ∃ x' : Sp R' ⟶ Y, x' ≫ π = spMap φ ≫ x := by
  intro R _ _ X Y π _ _ _ x
  obtain ⟨p, hp⟩ := (pullback.fst x π).surjective (IsLocalRing.closedPoint R)
  have hb := toStalk_bijective R _ hp
  have hτ : IsLocalHom (StructureSheaf.toStalk R ((pullback.fst x π) p)).hom := isLocalHom_of_bijective _ hb
  letI : Algebra ((Sp R).presheaf.stalk ((pullback.fst x π) p)) ((pullback x π).presheaf.stalk p) :=
    ((pullback.fst x π).stalkMap p).hom.toAlgebra
  haveI : Module.Flat ((Sp R).presheaf.stalk ((pullback.fst x π) p)) ((pullback x π).presheaf.stalk p) :=
    Flat.stalkMap (pullback.fst x π) p
  haveI : IsLocalHom (algebraMap ((Sp R).presheaf.stalk ((pullback.fst x π) p)) ((pullback x π).presheaf.stalk p)) :=
    inferInstanceAs (IsLocalHom ((pullback.fst x π).stalkMap p).hom)
  haveI := Module.FaithfullyFlat.of_flat_of_isLocalHom
    (A := (Sp R).presheaf.stalk ((pullback.fst x π) p)) (B := (pullback x π).presheaf.stalk p)
  have hψ : Function.Injective ((pullback.fst x π).stalkMap p).hom := FaithfulSMul.algebraMap_injective _ _
  have hψl : IsLocalHom ((pullback.fst x π).stalkMap p).hom := inferInstance
  refine ⟨(pullback x π).presheaf.stalk p, inferInstance, inferInstance,
    ((pullback.fst x π).stalkMap p).hom.comp (StructureSheaf.toStalk R ((pullback.fst x π) p)).hom,
    ⟨fun a ha => hτ.map_nonunit a (hψl.map_nonunit _ ha)⟩, hψ.comp hb.1,
    (pullback x π).fromSpecStalk p ≫ pullback.snd x π, ?_⟩
  have hS : spMap (((pullback.fst x π).stalkMap p).hom.comp (StructureSheaf.toStalk R ((pullback.fst x π) p)).hom) =
      Spec.map ((pullback.fst x π).stalkMap p) ≫ (Sp R).fromSpecStalk ((pullback.fst x π) p) := by
    rw [AlgebraicGeometry.Spec.fromSpecStalk_eq']
    exact (Spec.map_comp (StructureSheaf.toStalk R ((pullback.fst x π) p)) ((pullback.fst x π).stalkMap p))
  rw [Category.assoc, ← pullback.condition, hS, Category.assoc, Scheme.SpecMap_stalkMap_fromSpecStalk_assoc]

end GlobalTheory.LiftLocal
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLineBundlePowerPullbackSectionPullbackStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.EndLoc
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G.Out
open GlobalTheory.HomFixMat
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_lineBundlePowerPullback_section_pullback : ∀ {X Y Z : Scheme.{0}} (L : LB Z) (φ : Y ⟶ Z) (h : X ⟶ Y) (a : ℤ) (s : LB.Sec (powPull L φ a)), ∃ s' : LB.Sec (powPull L (h ≫ φ) a), ∀ q : Fin 1 → L.ι, s'.f q = (h.appLE (LB.wchart L (fun _ : Fin 1 => φ) q) (LB.wchart L (fun _ : Fin 1 => h ≫ φ) q) (GlobalTheory.HomFixMat.wchart_comp_le L h φ q)).hom (s.f q) := by
  first | (exact @GlobalTheory.HomFixMat.pullSec_exists) | (exact GlobalTheory.HomFixMat.pullSec_exists) | (intros; apply GlobalTheory.HomFixMat.pullSec_exists  <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLinearEquivOfAdjointSkewPairingsStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Gen GlobalTheory.UPel.HT.EtLev
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_linearEquiv_of_adjoint_skewPairings : ∀ (O : Type) [Ring O] (st : O → O) (M : Type) [AddCommGroup M] [Module O M] [Finite M] (k : Type) [Field k] [IsAlgClosed k] [CharZero k] (B E : M → M → kˣ) (e : O), (∀ c, st (st c) = c) → (∀ c, e * c = c * e) → (∀ c, st e * c = c * st e) → (∀ x : M, e • x + st e • x = x) → (∀ x : M, e • st e • x = 0) → (∀ x x' y, B (x + x') y = B x y * B x' y) → (∀ x y, B x y * B y x = 1) → (∀ (c : O) x y, B (c • x) y = B x (st c • y)) → (∀ x, (∀ y, B x y = 1) → x = 0) → (∀ x x' y, E (x + x') y = E x y * E x' y) → (∀ x y, E x y * E y x = 1) → (∀ (c : O) x y, E (c • x) y = E x (st c • y)) → (∀ x, (∀ y, E x y = 1) → x = 0) → ∃ g : M ≃ₗ[O] M, ∀ x y, B (g x) (g y) = E x y := by
  first | (exact @GlobalTheory.SkewPairingCmp.exists_linearEquiv) | (exact GlobalTheory.SkewPairingCmp.exists_linearEquiv) | (intros; apply GlobalTheory.SkewPairingCmp.exists_linearEquiv  <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPPowerLevelFromPrimesAbovePStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Gen GlobalTheory.UPel.HT.EtLev
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_pPower_level_from_primes_above_p : ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (Q : Type) [CommGroup Q] (act : D.O → Q → Q), (∀ c a b, act c (a * b) = act c a * act c b) → (∀ a, act 1 a = a) → (∀ b c a, act (b * c) a = act b (act c a)) → (∀ b c a, act (b + c) a = act b a * act c a) → (∀ (w : Ideal (𝓞 D.F)) (r : ℕ), w.IsMaximal → (p : 𝓞 D.F) ∈ w → ∃ l : D.La → Q, (∀ x y, l (x + y) = l x * l y) ∧ (∀ (c : D.O) x, l (c • x) = act c (l x)) ∧ (∀ x, l x = 1 ↔ x ∈ wSub D w r) ∧ ∀ g, (∀ c ∈ w ^ r, act (algebraMap (𝓞 D.F) D.O c) g = 1) → ∃ y, l y = g) → ∀ r : ℕ, ∃ f : D.La → Q, (∀ x y, f (x + y) = f x * f y) ∧ (∀ (c : D.O) x, f (c • x) = act c (f x)) ∧ (∀ x, f x = 1 ↔ ∃ y, x = (p ^ r) • y) ∧ (∀ g : Q, g ^ (p ^ r) = 1 ↔ ∃ x, f x = g) := by
  first | (exact @GlobalTheory.UPel.HT.EtLev.LevCrt.exists_pLevel) | (exact GlobalTheory.UPel.HT.EtLev.LevCrt.exists_pLevel) | (intros; apply GlobalTheory.UPel.HT.EtLev.LevCrt.exists_pLevel  <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPerfectIdempotent
section
set_option autoImplicit false

open CategoryTheory TensorProduct Coalgebra Bialgebra GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup

namespace GlobalTheory.PDivGroup

theorem exists_perfect_idempotent (p : ℕ) [Fact p.Prime] (k : Type) [Field k] [CharP k p]
    [PerfectRing k p] (G : PDivGroup p k) :
    ∃ e : G ⟶ G, e ≫ e = e ∧ (∀ (n : ℕ) (a : G.A n), IsNilpotent (a - e.app n a)) ∧
      ∀ (n : ℕ) (a : G.A n), IsNilpotent (e.app n a) → e.app n a = 0 := by
  choose π hπ using fun n => _root_.GlobalTheory.exists_perfectPart_algHom p k (G.A n)
  have hk : (∀ a : k, IsNilpotent (a - AlgHom.id k k a)) ∧
      ∀ a : k, ∃ b : k, AlgHom.id k k a = AlgHom.id k k b ^ p :=
    ⟨fun a => by simp, fun a => by
      obtain ⟨b, hb⟩ := (PerfectRing.bijective_frobenius (R := k) (p := p)).2 a
      exact ⟨b, hb.symm⟩⟩
  have nat := fun n m => _root_.GlobalTheory.PerfectProj.natural_idempotent_reduced p k (G.A n) (G.A m) (π n) (π m) (hπ n) (hπ m)
  let b : ∀ n, G.A n →ₐc[k] G.A n := fun n => BialgHom.ofAlgHom (π n)
    (AlgHom.ext fun a => (_root_.GlobalTheory.PerfectProj.natural_idempotent_reduced p k (G.A n) k (π n) (AlgHom.id k k) (hπ n) hk).1
      (counitAlgHom k (G.A n)) a)
    (AlgHom.ext fun a => ((_root_.GlobalTheory.PerfectProj.natural_idempotent_reduced p k (G.A n) (G.A n ⊗[k] G.A n) (π n) _ (hπ n)
      (_root_.GlobalTheory.tensorSquare_perfectProjection p k (G.A n) (π n) (hπ n))).1 (comulAlgHom k (G.A n)) a).symm)
  refine ⟨⟨b, fun n => ?_⟩, ?_, fun n a => (hπ n).1 a, fun n a => (nat n n).2.2 a⟩
  · refine BialgHom.ext fun a => ?_
    exact (nat (n + 1) n).1 (G.res n : G.A (n + 1) →ₐ[k] G.A n) a
  · exact Hom.ext (funext fun n => BialgHom.ext fun a => (nat n n).2.1 a)

end GlobalTheory.PDivGroup
end

