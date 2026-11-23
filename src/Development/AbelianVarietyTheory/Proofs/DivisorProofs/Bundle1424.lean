module

public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0020
public import Development.AbelianVarietyTheory.Definitions.Degenerations.OfDerivationFnOn
public import Mathlib
public import Formalism.PadicSubsetSums.CentralIdempotents.Bundle0002
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.Bundle0008
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ChiIdemMulLvlIdemBaseNeZero
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0565
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0335
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.IrreducibleCharacterSeries.FrobeniusSumFormula
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0017
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0828
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0813
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0763
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1376
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1391
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0044
public import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1319
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1321
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0033
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1241
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1009
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0958
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1392
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsTypeIsRealConst

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FreeFiniteFinrank
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj Pointwise
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.HTLat GlobalTheory.Published GlobalTheory.Published.AbVarRed IsLocalRing
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.TateFree

open GlobalTheory.PDiv

variable {M : Type} [CommGroup M] {l : ℕ} [Fact l.Prime] {r : ℕ}

theorem lev_sum {I : Type} (s : Finset I) (f : I → Tate l M) (n : ℕ) :
    (∑ i ∈ s, f i).lev n = ∏ i ∈ s, (f i).lev n := by
  let h : Tate l M →+ Additive M :=
    { toFun := fun t => Additive.ofMul (t.lev n), map_zero' := rfl, map_add' := fun _ _ => rfl }
  have := congrArg Additive.toMul (map_sum h f s)
  rw [toMul_sum] at this
  exact this

theorem zpow_pow_comm' (a : M) (k : ℤ) (m : ℕ) : (a ^ k) ^ m = (a ^ m) ^ k := by
  rw [← zpow_natCast, ← zpow_natCast a m, ← zpow_mul, ← zpow_mul, mul_comm]

theorem exists_pow_eq (hc : ∀ n : ℕ, Nat.card {x : M // x ^ (l ^ n) = 1} = l ^ (r * n)) (n : ℕ)
    (x : M) (hx : x ^ l ^ n = 1) : ∃ y : M, y ^ l ^ (n + 1) = 1 ∧ y ^ l = x := by
  have hp : l.Prime := Fact.out
  let K : ℕ → Subgroup M := fun n => (powMonoidHom (l ^ n) : M →* M).ker
  have hmem : ∀ n (y : M), y ∈ K n ↔ y ^ l ^ n = 1 := fun n y => by
    simp [K, MonoidHom.mem_ker, powMonoidHom_apply]
  have hK : ∀ n, Nat.card (K n) = l ^ (r * n) := fun n =>
    (Nat.card_congr (Equiv.subtypeEquivRight fun y => hmem n y)).trans (hc n)
  have hfin : ∀ n, Finite (K n) := fun n =>
    Nat.finite_of_card_ne_zero (by rw [hK n]; exact pow_ne_zero _ hp.ne_zero)
  let φ : K (n + 1) →* M := (powMonoidHom l).comp (K (n + 1)).subtype
  have hφ : ∀ y : K (n + 1), φ y = (y : M) ^ l := fun y => rfl
  have hrange : φ.range ≤ K n := by
    rintro _ ⟨y, rfl⟩
    rw [hmem, hφ, ← pow_mul, ← pow_succ']
    exact (hmem _ _).1 y.2
  have h1 : ∀ z : M, z ^ l = 1 → z ^ l ^ (n + 1) = 1 := fun z h => by
    rw [pow_succ', pow_mul, h, one_pow]
  have hker : Nat.card φ.ker = l ^ (r * 1) := by
    rw [← hc 1]
    refine Nat.card_congr
      { toFun := fun z => ⟨z.1.1, by rw [pow_one, ← hφ]; exact MonoidHom.mem_ker.1 z.2⟩
        invFun := fun z => ⟨⟨z.1, (hmem _ _).2 (h1 _ (by simpa using z.2))⟩,
          MonoidHom.mem_ker.2 (by rw [hφ]; simpa using z.2)⟩
        left_inv := fun _ => rfl
        right_inv := fun _ => rfl }
  have hcard : Nat.card φ.range = l ^ (r * n) := by
    have h := Subgroup.card_eq_card_quotient_mul_card_subgroup φ.ker
    rw [Nat.card_congr (QuotientGroup.quotientKerEquivRange φ).toEquiv, hker, hK] at h
    refine Nat.eq_of_mul_eq_mul_right (pow_pos hp.pos (r * 1)) ?_
    rw [← h, ← pow_add]
    ring_nf
  haveI := hfin n
  have heq : φ.range = K n := Subgroup.eq_of_le_of_card_ge hrange (by rw [hcard, hK])
  obtain ⟨y, hy⟩ : x ∈ φ.range := heq ▸ (hmem n x).2 hx
  exact ⟨y.1, (hmem _ _).1 y.2, hy⟩

theorem exists_tate (hc : ∀ n : ℕ, Nat.card {x : M // x ^ (l ^ n) = 1} = l ^ (r * n)) (x : M)
    (hx : x ^ l = 1) : ∃ t : Tate l M, t.lev 1 = x := by
  choose L hL using exists_pow_eq hc
  let u : ∀ m : ℕ, {y : M // y ^ l ^ (m + 1) = 1} := fun m =>
    Nat.rec (motive := fun m => {y : M // y ^ l ^ (m + 1) = 1}) ⟨x, by simpa using hx⟩
      (fun m y => ⟨L (m + 1) y.1 y.2, (hL _ _ _).1⟩) m
  have hu : ∀ m, (u (m + 1)).1 ^ l = (u m).1 := fun m => (hL _ _ _).2
  let s : ℕ → M := fun k => Nat.casesOn k 1 fun m => (u m).1
  refine ⟨Tate.mk s fun k => ⟨?_, ?_⟩, rfl⟩
  · rcases k with _ | m
    · exact one_pow _
    · exact (u m).2
  · rcases k with _ | m
    · exact hx
    · exact hu m

theorem exists_independent (hr : Nat.card {x : M // x ^ l = 1} = l ^ r) :
    ∃ e : Fin r → M, (∀ i, e i ^ l = 1) ∧
      ∀ k : Fin r → ℤ, ∏ i, e i ^ k i = 1 → ∀ i, (l : ℤ) ∣ k i := by
  have hp : l.Prime := Fact.out
  let K : Subgroup M := (powMonoidHom l : M →* M).ker
  have hmem : ∀ y : M, y ∈ K ↔ y ^ l = 1 := fun y => by
    simp [K, MonoidHom.mem_ker, powMonoidHom_apply]
  have hK : Nat.card K = l ^ r :=
    (Nat.card_congr (Equiv.subtypeEquivRight fun y => hmem y)).trans hr
  haveI : Finite K := Nat.finite_of_card_ne_zero (by rw [hK]; exact pow_ne_zero _ hp.ne_zero)
  letI : Module (ZMod l) (Additive K) := AddCommGroup.zmodModule fun z => by
    apply Additive.toMul.injective
    apply Subtype.ext
    simp only [toMul_nsmul, toMul_zero, SubmonoidClass.coe_pow, OneMemClass.coe_one]
    exact (hmem _).1 (Additive.toMul z).2
  haveI : Finite (Additive K) := inferInstanceAs (Finite K)
  haveI : Fintype (Additive K) := Fintype.ofFinite _
  haveI hMF : Module.Finite (ZMod l) (Additive K) := Module.Finite.of_finite
  haveI hMFr : Module.Free (ZMod l) (Additive K) := Module.Free.of_divisionRing _ _
  have hfr : Module.finrank (ZMod l) (Additive K) = r := by
    have h1 := Module.card_eq_pow_finrank (K := ZMod l) (V := Additive K)
    rw [ZMod.card, ← Nat.card_eq_fintype_card] at h1
    exact Nat.pow_right_injective hp.two_le (h1.symm.trans hK)
  let b : Module.Basis (Fin r) (ZMod l) (Additive K) :=
    @Module.finBasisOfFinrankEq (ZMod l) (Additive K) _ _ _ hMFr _ hMF r hfr
  let v : Fin r → Additive K := @DFunLike.coe _ _ _ Module.Basis.instFunLike b
  have hv : LinearIndependent (ZMod l) v := b.linearIndependent
  refine ⟨fun i => ((Additive.toMul (v i) : K) : M), fun i => (hmem _).1 (Additive.toMul (v i)).2,
    fun k hk i => ?_⟩
  have hli := Fintype.linearIndependent_iff.1 hv (fun i => (k i : ZMod l)) ?_ i
  · exact (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).1 hli
  · simp_rw [Int.cast_smul_eq_zsmul]
    apply Additive.toMul.injective
    apply Subtype.ext
    rw [toMul_sum]
    simpa [toMul_zsmul] using hk

theorem free_finite_finrank (M : Type) [CommGroup M] (l : ℕ) [Fact l.Prime] (r : ℕ)
    (hc : ∀ n : ℕ, Nat.card {x : M // x ^ (l ^ n) = 1} = l ^ (r * n)) :
    Module.Free ℤ_[l] (Tate l M) ∧ Module.Finite ℤ_[l] (Tate l M) ∧
      Module.finrank ℤ_[l] (Tate l M) = r := by
  have hp : l.Prime := Fact.out
  obtain ⟨e, he1, hind⟩ := exists_independent (M := M) (l := l) (r := r) (by simpa using hc 1)
  choose t ht using fun i => exists_tate hc (e i) (he1 i)

  have key : ∀ n (k : Fin r → ℤ), ∏ i, (t i).lev n ^ k i = 1 → ∀ i, (l : ℤ) ^ n ∣ k i := by
    intro n
    induction n with
    | zero => intro k _ i; simp
    | succ n ih =>
      intro k hk i
      have hl : ∀ j, (t j).lev (n + 1) ^ l ^ n = e j := fun j => by
        rw [add_comm, Tate.lev_add_pow, ht]
      have h1 : ∏ j, e j ^ k j = 1 := by
        have h2 := congrArg (· ^ (l ^ n)) hk
        simp only [one_pow, ← Finset.prod_pow, zpow_pow_comm', hl] at h2
        exact h2
      choose k' hk' using hind k h1
      have h3 : ∏ j, (t j).lev n ^ k' j = 1 := by
        rw [← hk]
        refine Finset.prod_congr rfl fun j _ => ?_
        rw [hk' j, zpow_mul, zpow_natCast, Tate.lev_succ]
      rw [hk' i, pow_succ']
      exact mul_dvd_mul_left _ (ih k' h3 i)
  have key2 : ∀ n (k k' : Fin r → ℕ), ∏ i, (t i).lev n ^ k i = ∏ i, (t i).lev n ^ k' i →
      ∀ i, (l : ℤ) ^ n ∣ (k i : ℤ) - k' i := fun n k k' h =>
    key n (fun i => (k i : ℤ) - k' i) (by
      simp only [zpow_sub, zpow_natCast, Finset.prod_mul_distrib, Finset.prod_inv_distrib, h,
        mul_inv_cancel])

  have hgen : ∀ n (x : M), x ^ l ^ n = 1 → ∃ c : Fin r → ℕ, ∏ i, (t i).lev n ^ c i = x := by
    intro n
    haveI : NeZero (l ^ n) := ⟨pow_ne_zero _ hp.ne_zero⟩
    haveI : Finite {x : M // x ^ l ^ n = 1} :=
      Nat.finite_of_card_ne_zero (by rw [hc n]; exact pow_ne_zero _ hp.ne_zero)
    let ψ : (Fin r → ZMod (l ^ n)) → {x : M // x ^ l ^ n = 1} := fun c =>
      ⟨∏ i, (t i).lev n ^ (c i).val, by
        rw [← Finset.prod_pow]
        exact Finset.prod_eq_one fun i _ => by
          rw [← pow_mul, mul_comm, pow_mul, Tate.lev_pow, one_pow]⟩
    have hinj : Function.Injective ψ := fun c c' h => funext fun i => by
      have h1 := key2 n _ _ (congrArg Subtype.val h) i
      rw [← sub_eq_zero, ← ZMod.natCast_zmod_val (c i), ← ZMod.natCast_zmod_val (c' i)]
      have h2 := (ZMod.intCast_zmod_eq_zero_iff_dvd (((c i).val : ℤ) - (c' i).val) (l ^ n)).2
        (by exact_mod_cast h1)
      push_cast at h2
      exact h2
    have hbij := hinj.bijective_of_nat_card_le (by
      rw [hc n, Nat.card_fun, Nat.card_zmod, Nat.card_eq_fintype_card, Fintype.card_fin, ← pow_mul,
        mul_comm])
    intro x hx
    obtain ⟨c, hc'⟩ := hbij.2 ⟨x, hx⟩
    exact ⟨fun i => (c i).val, congrArg Subtype.val hc'⟩

  let Φ := Fintype.linearCombination ℤ_[l] t
  have hΦ : ∀ a n, (Φ a).lev n = ∏ i, (t i).lev n ^ digit n (a i) := fun a n => by
    rw [Fintype.linearCombination_apply, lev_sum]
    rfl
  have hinj : Function.Injective Φ := by
    refine (injective_iff_map_eq_zero Φ).2 fun a ha => funext fun i =>
      PadicInt.ext_of_toZModPow.1 fun n => ?_
    have h1 := key2 n (fun i => digit n (a i)) (fun _ => 0) (by
      rw [← hΦ, ha]
      simp) i
    rw [← cast_digit, Pi.zero_apply, map_zero]
    have h2 := (ZMod.intCast_zmod_eq_zero_iff_dvd (digit n (a i) : ℤ) (l ^ n)).2
      (by simpa using h1)
    exact_mod_cast h2
  have hsurj : Function.Surjective Φ := by
    intro x
    choose c hc' using fun n => hgen n (x.lev n) (x.lev_pow n)
    have hdiv : ∀ i n, (l : ℤ) ^ n ∣ ((c (n + 1) i : ℕ) : ℤ) - c n i := fun i n =>
      key2 n (c (n + 1)) (c n) (by
        rw [hc' n, ← x.lev_succ, ← hc' (n + 1), ← Finset.prod_pow]
        refine Finset.prod_congr rfl fun j _ => ?_
        rw [← pow_mul, mul_comm, pow_mul, Tate.lev_succ]) i
    have hex : ∀ i, ∃ a : ℤ_[l], ∀ n, PadicInt.toZModPow n a = ((c n i : ℤ) : ZMod (l ^ n)) :=
      fun i => ⟨_, PadicInt.toZModPow_ofIntSeq_of_pow_dvd_sub (fun n => (c n i : ℤ)) l (hdiv i)⟩
    choose a ha using hex
    refine ⟨a, Tate.ext fun n => ?_⟩
    rw [hΦ, ← hc' n]
    refine Finset.prod_congr rfl fun i _ => pow_digit_eq ((t i).lev_pow n) ?_
    rw [ha, Int.cast_natCast]
  let E : (Fin r → ℤ_[l]) ≃ₗ[ℤ_[l]] Tate l M := LinearEquiv.ofBijective Φ ⟨hinj, hsurj⟩
  exact ⟨Module.Free.of_equiv E, Module.Finite.equiv E,
    E.finrank_eq.symm.trans (Module.finrank_fin_fun ℤ_[l])⟩

end GlobalTheory.TateFree
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HarishChandraInductionCuspidalParabolicProduct
section
open CategoryTheory Polynomial Formalism.IrreducibleCountingLemmas.TYPES

noncomputable section

namespace GlobalTheory.HCInduction

open Formalism.L2.DIV GlobalTheory.BI

variable {K : Type} [Field K] [Fintype K] [DecidableEq K] {r s : ℕ}

theorem parab_eq_blockTri (b : Fin r → Fin s) :
    parab K b = blockTri (κ := K) (fun i => (b i : ℕ)) := by
  ext g
  constructor
  · intro hg
    exact hg.1
  · intro hg
    exact ⟨hg, (blockTri (κ := K) (fun i => (b i : ℕ))).inv_mem hg⟩


omit [Fintype K] [DecidableEq K] in
def blockGL (b : Fin r → Fin s) (c : Fin s) :
    GL (Fin (Fintype.card {i // b i = c})) K ≃* GL {i // b i = c} K :=
  glEquiv K (Fintype.equivFin {i // b i = c}).symm

omit [Fintype K] [DecidableEq K] in
theorem blockGL_apply (b : Fin r → Fin s) (c : Fin s) (g : GL (Fin (Fintype.card {i // b i = c})) K)
    (x y : {i // b i = c}) :
    ((blockGL b c g : GL {i // b i = c} K) : Matrix _ _ K) x y =
      (g : Matrix _ _ K) (Fintype.equivFin _ x) (Fintype.equivFin _ y) := rfl

theorem sum_unipRadical_eq_zero (b : Fin r → Fin s) (c : Fin s) (τ : FDRep ℂ (GL {i // b i = c} K))
    (hτ : IsCuspidal K τ) (c' : Fin (Fintype.card {i // b i = c}) → ℕ) (hc' : ∃ i j, c' i ≠ c' j) :
    ∑ᶠ u : GlobalTheory.FiniteGL.unipRadical K c', LinearMap.trace ℂ τ (τ.ρ (blockGL b c u)) = 0 := by
  classical
  let _ : Fintype (GlobalTheory.FiniteGL.unipRadical K c') := Fintype.ofFinite _
  rw [finsum_eq_sum_of_fintype]
  let ρu : Representation ℂ (GlobalTheory.FiniteGL.unipRadical K c') τ :=
    τ.ρ.comp ((blockGL b c).toMonoidHom.comp (GlobalTheory.FiniteGL.unipRadical K c').subtype)
  refine (GlobalTheory.GoodTypeGeneric.sum_character_eq_zero_iff ρu).2 ?_
  intro v hv
  obtain ⟨i0, j0, h0⟩ : ∃ i0 j0, c' i0 < c' j0 := by
    obtain ⟨i, j, hij⟩ := hc'
    rcases lt_or_gt_of_ne hij with h | h
    · exact ⟨i, j, h⟩
    · exact ⟨j, i, h⟩
  let F := Fintype.equivFin {i // b i = c}
  let bb : {i // b i = c} → Fin 2 := fun x => if c' (F x) ≤ c' i0 then 0 else 1
  have hbb : Function.Surjective bb := by
    intro k
    fin_cases k
    · exact ⟨F.symm i0, by simp [bb]⟩
    · exact ⟨F.symm j0, by simp [bb, not_le.2 h0]⟩
  refine hτ 2 bb hbb le_rfl v fun u hu => ?_
  set u' := (blockGL b c).symm u with hu'def
  have hu'u : blockGL b c u' = u := MulEquiv.apply_symm_apply _ _
  have hent : ∀ k l, (u' : Matrix _ _ K) k l = (u : Matrix _ _ K) (F.symm k) (F.symm l) := by
    intro k l
    rw [← hu'u, blockGL_apply]
    simp [F]
  have hmem : u' ∈ GlobalTheory.FiniteGL.unipRadical K c' := by
    rw [GlobalTheory.FiniteGL.mem_unipRadical]
    intro k l hlk
    rw [Matrix.sub_apply, hent]
    have hb : ∀ m, bb (F.symm m) = if c' m ≤ c' i0 then 0 else 1 := fun m => by simp [bb]
    by_cases hkl : bb (F.symm k) = bb (F.symm l)
    · rw [hu.2 _ _ hkl]
      by_cases e : k = l
      · subst e; simp
      · rw [if_neg (fun h => e (F.symm.injective h)), Matrix.one_apply_ne e, sub_zero]
    · have hk : ¬ c' k ≤ c' i0 := fun hk => hkl (by rw [hb, hb, if_pos hk, if_pos (hlk.trans hk)])
      have hl : c' l ≤ c' i0 := by
        by_contra hl
        exact hkl (by rw [hb, hb, if_neg hk, if_neg hl])
      have hlt : bb (F.symm l) < bb (F.symm k) := by
        rw [hb, hb, if_neg hk, if_pos hl]; decide
      have ekl : k ≠ l := fun e => hkl (by rw [e])
      rw [hu.1.1 _ _ hlt, Matrix.one_apply_ne ekl, sub_zero]
  have := hv ⟨u', hmem⟩
  simpa [ρu, hu'u] using this

theorem isIrrChar_block (b : Fin r → Fin s) (c : Fin s) (τ : FDRep ℂ (GL {i // b i = c} K)) (hτ : Simple τ) :
    IsIrrChar ℂ ℂ (fun g : GL (Fin (Fintype.card {i // b i = c})) K => LinearMap.trace ℂ τ (τ.ρ (blockGL b c g))) := by
  have hi := GlobalTheory.FinGL.Transport.isIrreducible_comp τ.ρ (blockGL b c).toMonoidHom (blockGL b c).surjective
    (GlobalTheory.SerOSys.ZSum.isIrreducible_of_simple τ hτ)
  have h := (isChar_and_isIrrChar_of_rep ℂ ℂ _ τ (τ.ρ.comp (blockGL b c).toMonoidHom)).2 hi
  simpa [Representation.character] using h

theorem isCuspProdChar_trace_hcRep : ∀ (K : Type) [Field K] [Fintype K] [DecidableEq K] (r s : ℕ) (b : Fin r → Fin s)
    (lam : ∀ c : Fin s, FDRep ℂ (GL {i // b i = c} K)), Function.Surjective b →
    (∀ c, Simple (lam c) ∧ IsCuspidal K (lam c)) → Monotone b →
    GlobalTheory.IndefiniteRowSideFullHecke.CuspidalProductMultiplicity.IsCuspProdChar (fun x : GL (Fin r) K => LinearMap.trace ℂ (hcSpace K b lam) (hcRep K b lam x)) := by
  intro K _ _ _ r s b lam _ hlam hmono
  classical
  let b₀ : Fin r → ℕ := fun i => (b i : ℕ)
  have hb₀ : Monotone b₀ := fun i j h => hmono h
  let d : Fin s → ℕ := fun c => Fintype.card {i // b i = c}
  let e : (Σ c, Fin (d c)) ≃ Fin r :=
    (Equiv.sigmaCongrRight fun c => (Fintype.equivFin {i // b i = c}).symm).trans (Equiv.sigmaFiberEquiv b)
  have hbe : ∀ x, b (e x) = x.1 := fun x => ((Fintype.equivFin {i // b i = x.1}).symm x.2).2
  have he : ∀ x y, b₀ (e x) = b₀ (e y) ↔ x.1 = y.1 := by
    intro x y
    simp only [b₀, hbe, Fin.val_inj]
  let χ : ∀ c, GL (Fin (d c)) K → ℂ := fun c g => LinearMap.trace ℂ (lam c) ((lam c).ρ (blockGL b c g))
  obtain ⟨n, σ, hσ, hch⟩ := GlobalTheory.GoodTypeGeneric.exists_isCuspDatum (F := K) hb₀ e he χ
    (fun c => isIrrChar_block b c (lam c) (hlam c).1)
    (fun c c' hc' => sum_unipRadical_eq_zero b c (lam c) (hlam c).2 c' hc')
  refine ⟨n, b₀, σ, hσ, fun x => ?_⟩
  have hPB := parab_eq_blockTri (K := K) b
  let f : blockTri (κ := K) b₀ →* parab K b :=
    MonoidHom.codRestrict (blockTri (κ := K) b₀).subtype (parab K b) (fun p => by rw [hPB]; exact p.2)
  have hf : Function.Surjective f := fun p => ⟨⟨p.1, by rw [← hPB]; exact p.2⟩, rfl⟩
  have h1 : LinearMap.trace ℂ (hcSpace K b lam) (hcRep K b lam x) =
      (Representation.coind (parab K b).subtype (PI.SerBridgeGLW.inflRep K b lam)).character x := rfl
  show LinearMap.trace ℂ (hcSpace K b lam) (hcRep K b lam x) = _
  have h2 := GlobalTheory.FinGL.Transport.character_coind (parab K b).subtype (blockTri (κ := K) b₀).subtype
    (PI.SerBridgeGLW.inflRep K b lam) (MulEquiv.refl _) f hf (fun _ => rfl) x
  rw [MulEquiv.refl_apply] at h2
  rw [h1, ← h2]
  rw [GlobalTheory.GoodTypeGeneric.character_coind_eq_ind, GlobalTheory.GoodTypeGeneric.character_coind_eq_ind]
  congr 1
  funext p
  rw [hch p]
  show LinearMap.trace ℂ _ (PiTensorProduct.map fun c => (lam c).ρ (levi K b c (f p))) = _
  rw [PI.SerBridgeGLW.trace_piTensorMap]
  refine Finset.prod_congr rfl fun c _ => ?_
  show _ = LinearMap.trace ℂ (lam c) ((lam c).ρ (blockGL b c _))
  congr 3
  apply Units.ext
  ext x y
  rw [blockGL_apply, GlobalTheory.GoodTypeGeneric.blocksHom_apply]
  have hx : ∀ z : {i // b i = c}, e ⟨c, Fintype.equivFin _ z⟩ = z.1 := fun z => by
    simp [e, Equiv.sigmaFiberEquiv]
  rw [hx, hx]
  rfl

end GlobalTheory.HCInduction
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HarrisTaylorHeckeMapCompEqForgetLevel
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Hecke

namespace GlobalTheory.UPel.HT.Hecke

theorem harrisTaylor_heckeMap_comp_forgetLevel_general {p : ℕ} [Fact p.Prime] {D : Datum p} {R : Type} [CommRing R] {b : Base D R}
    (g g' : D.La →ₗ[D.O] D.La) (c c' k N : ℕ) (hk : k.Coprime p) (hN3 : 3 ≤ N) (hNp : N.Coprime p)
    (hgg' : ∀ x, g (g' x) = k • x) (hg'g : ∀ x, g' (g x) = k • x) (hcc : c * c' = k ^ 2)
    (hc : (N * k * k).Coprime p)
    {S S₁ S₂ : Scheme.{0}} (s : S ⟶ Sp R) (s₁ : S₁ ⟶ Sp R) (s₂ : S₂ ⟶ Sp R)
    (u : Obj b N s) (u₁ : Obj b (N * k) s₁) (u₂ : Obj b (N * k * k) s₂) (π : S₁ ⟶ S) (π₁ : S₂ ⟶ S₁)
    (h₁ : π₁ ≫ s₁ = s₂)
    (o₂ : Obj b N s₁) (ψ₂ : u₁.A ⟶ o₂.A) (hH₂ : IsHecke g c k N u₁ o₂ ψ₂) (m₂ : ObjMap o₂ u π)
    (o₁ : Obj b (N * k) s₂) (ψ₁ : u₂.A ⟶ o₁.A) (hH₁ : IsHecke g' c' k (N * k) u₂ o₁ ψ₁)
    (m₁ : ObjMap o₁ u₁ π₁) :
    Nonempty (ObjMap (u₂.forget N ⟨k * k, by ring⟩ hc) u (π₁ ≫ π)) := by
  subst h₁
  obtain ⟨o₂', ⟨m⟩⟩ := GlobalTheory.HTPull.exists_objMap_pull p D R b N S₁ S₂ s₁ π₁ o₂
  obtain ⟨ψ', hψ'⟩ := GlobalTheory.T.isHeckeTranslate_harrisTaylor_pullback_base p D R b g c k N hk hN3 hNp S₁ S₂ s₁ π₁ u₁ o₂ ψ₂ o₁ o₂' hH₂ m₁ m
  obtain ⟨n⟩ := GlobalTheory.T.harrisTaylor_inverse_heckeTranslates_forget_level p D R b g g' c c' k N hk hN3 hNp hgg' hg'g hcc hc S₂ (π₁ ≫ s₁) u₂ o₁ o₂'
    ψ₁ ψ' hH₁ hψ'
  obtain ⟨n₁⟩ := GlobalTheory.UPel.HT.objMap_comp p D R b N _ _ _ _ _ _ _ _ _ _ _ n m
  obtain ⟨n₂⟩ := GlobalTheory.UPel.HT.objMap_comp p D R b N _ _ _ _ _ _ _ _ _ _ _ n₁ m₂
  rw [Category.id_comp] at n₂
  exact ⟨n₂⟩

theorem heckeMap_comp_forget : ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (R : Type) [CommRing R] (b : Base D R) (g g' : D.La →ₗ[D.O] D.La) (c c' k N : ℕ), k.Coprime p → 3 ≤ N → N.Coprime p → (∀ x, g (g' x) = k • x) → (∀ x, g' (g x) = k • x) → c * c' = k ^ 2 → ∀ (hc : (N * k * k).Coprime p) (F : RepFam b N) (F₁ : RepFam b (N * k)) (F₂ : RepFam b (N * k * k)) (π : F₁.X ⟶ F.X) (π₁ : F₂.X ⟶ F₁.X), IsHeckeMap g c k N F F₁ π → IsHeckeMap g' c' k (N * k) F₁ F₂ π₁ → Nonempty (ObjMap (F₂.univ.forget N ⟨k * k, by ring⟩ hc) F.univ (π₁ ≫ π)) := by
  intro p _ D R _ b g g' c c' k N hk hN3 hNp hgg' hg'g hcc hc F F₁ F₂ π π₁ hπ hπ₁
  obtain ⟨-, o₂, ψ₂, hH₂, ⟨m₂⟩⟩ := hπ
  obtain ⟨h₁, o₁, ψ₁, hH₁, ⟨m₁⟩⟩ := hπ₁
  exact harrisTaylor_heckeMap_comp_forgetLevel_general g g' c c' k N hk hN3 hNp hgg' hg'g hcc hc F.s F₁.s F₂.s F.univ F₁.univ F₂.univ π π₁ h₁
    o₂ ψ₂ hH₂ m₂ o₁ ψ₁ hH₁ m₁

end GlobalTheory.UPel.HT.Hecke
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeisenbergDerivArchimedeanWeilRepIntertwineStatement
section
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open scoped TensorProduct NNReal Matrix
open scoped Classical
open GlobalTheory.ArchDecay

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.heisenbergDeriv_archimedean_weilRep_intertwine : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (n d : ℕ) (X : Spc F E n) (W : Spc F E d) (M : Model σ X W) (χX χW : Chr F E) (om : Rep σ X W) (r s r' s' : ℕ), IsPair B M χX χW om r s r' s' → ∀ (p : UA σ X.J × UA σ W.J) (u : Matrix (Fin n) (Fin d) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))), At (evI F) u → ∀ f ∈ schA F (Fin n × Fin d), heisD M B.ψ u (om p f) = om p (heisD M B.ψ (actAB (cA σ) p⁻¹ u) f) := by
  first | exact @GlobalTheory.ArchDecay.HeisWeil.heisD_weil | exact GlobalTheory.ArchDecay.HeisWeil.heisD_weil | (intros; apply GlobalTheory.ArchDecay.HeisWeil.heisD_weil <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HilbertModelExtremalValuesEqHolomorphicCuspForms
section
open NumberField IsDedekindDomain MeasureTheory Matrix Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Lev Formalism.IndefR.Datum Formalism.L2.Pj Formalism.IndefR.FWT Formalism.IndefR GlobalTheory.HolDict
open scoped TensorProduct InnerProductSpace ContDiff
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.HolDict

theorem range_evAt_eq_adel_image : GlobalTheory.Published.CuspRapidDecay → GlobalTheory.Mem.Vol.FiniteVolume₂ → ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T0 : Type) (A : FamIn D.what₂.LL G Pl0 T0 D.R.m) (T : CoreJ D) [Algebra T.Q.c.F D.what₂.LL] (R : RealDat D A T.Q.c.F) (κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)) (v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec), R.toLevCh.Is A.μ0 → R.IsModels → TieIn T R κ v₀ → T.pb = R.C.P.pb → ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), GoodEmb T.Q.c (res T σ) → ∀ hV : T.V ((i : ℕ) + 1) (res T σ) = Wc D i, Set.range (evAt R i σ (v₀ i σ)) = adel (Wc D i) (castDict hV (T.dict ((i : ℕ) + 1) (res T σ))) (muPin (Wc D i) (castDict hV (T.dict ((i : ℕ) + 1) (res T σ))) (castDict hV (T.mu ((i : ℕ) + 1) (res T σ))) (T.cE ((i : ℕ) + 1) (res T σ))) '' (Formalism.L2.Pj.holSub0 (T.U ((i : ℕ) + 1) (res T σ)).X (laU (T.U ((i : ℕ) + 1) (res T σ)) (wtA (κ i)) (κ i).n) : Set _) := by
  intro hc hf D G _ _ Pl0 T0 A T _ R κ v₀ hL hM hT hp i σ hσ hV
  obtain ⟨hs, -, w, hw⟩ := _root_.GlobalTheory.HolDict.holShape_of_good D G Pl0 T0 A T R κ v₀ hT i σ hσ
  have hg := _root_.GlobalTheory.HolDict.goodDict_core D G Pl0 T0 A T R κ v₀ hL hM hT hp i σ hσ hV w hw
  have hχ := (_root_.GlobalTheory.HolDict.PrincLev.principal_level D G Pl0 T0 A T R κ v₀ hL hM hT hp i σ hσ hV).2.1
  obtain ⟨h1, h2⟩ := _root_.GlobalTheory.HolDict.mult_eval_eq_adel_holSub0 hc hf D R.θ _ _ (R.MW i σ) w _ _ _ _ _ _ _ _ _ hs hg hw (v₀ i σ)
    (hT.hv₀ i σ).1 _ hχ
  have hW := hM.HW i σ
  have hr : LinearMap.range (R.HW i σ).e = R.Wall i σ := hW.2.1
  ext f
  constructor
  · rintro ⟨h, rfl⟩
    have hm : (R.HW i σ).e h ∈ R.Wall i σ := hr ▸ LinearMap.mem_range_self _ h
    obtain ⟨P, hP, e⟩ := h2 _ hm
    exact ⟨P, hP, e⟩
  · rintro ⟨P, hP, rfl⟩
    obtain ⟨S, hS, e⟩ := h1 P hP
    have hm : S ∈ LinearMap.range (R.HW i σ).e := by rw [hr]; exact hS
    obtain ⟨h, rfl⟩ := hm
    exact ⟨h, e⟩

end GlobalTheory.HolDict
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HolAtlasDelFinsetSumStatement
section
open Set Matrix MeasureTheory
open GlobalTheory.HermFrame
open scoped ComplexOrder
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.holAtlas_del_finset_sum : ∀ {M : Type} [TopologicalSpace M] {n : ℕ} (A : GlobalTheory.CxForm.HolAtlas M n) {N : ℕ} (α : Fin N → A.Fld), (∀ j, A.IsForm (α j)) → A.del (∑ j, α j) = ∑ j, A.del (α j) := by
  first | exact @GlobalTheory.CxForm.HolAtlas.del_finset_sum | exact GlobalTheory.CxForm.HolAtlas.del_finset_sum | (intros; apply GlobalTheory.CxForm.HolAtlas.del_finset_sum <;> assumption)
end

