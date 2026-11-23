module

public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.ZariskiEtaleLifting.SubThickRees
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.WittExactSequences.Bundle0001
public import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.Bundle0049
public import Mathlib
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0006
public import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.DeRhamJacobian.IsdRJ
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LineOfSingleJump
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0391
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.FinrankDdRFinsum

@[expose] public section

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsLocallyConstantToZModPow
section
set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry Polynomial DividedPowers GlobalTheory.LogCris GlobalTheory.PDA CrystallineSemistableComparison CrystallineSemistableComparison.CH CrystallineSemistableComparison.B

namespace GlobalTheory.CompanionTheory.PadicShift

theorem exists_period (p : ℕ) [Fact p.Prime] {N : Type} (f : ℤ_[p] → N)
    (hf : IsLocallyConstant f) :
    ∃ m : ℕ, ∀ x y : ℤ_[p], ((p : ℤ_[p]) ^ m) ∣ x - y → f x = f y := by
  obtain ⟨δ, hδ, h⟩ := lebesgue_number_lemma_of_metric (s := (Set.univ : Set ℤ_[p]))
    (c := fun v : N => f ⁻¹' {v}) isCompact_univ (fun v => hf.isOpen_fiber v)
    (fun x _ => Set.mem_iUnion.2 ⟨f x, rfl⟩)
  have hp : (1 : ℝ) < p := by exact_mod_cast (Fact.out : p.Prime).one_lt
  obtain ⟨m, hm⟩ := exists_pow_lt_of_lt_one hδ (inv_lt_one_of_one_lt₀ hp)
  refine ⟨m, fun x y hxy => ?_⟩
  obtain ⟨i, hi⟩ := h x (Set.mem_univ _)
  have hx : f x = i := hi (Metric.mem_ball_self hδ)
  have hy : f y = i := by
    apply hi
    rw [Metric.mem_ball, dist_comm, dist_eq_norm]
    have : x - y ∈ Ideal.span {(p : ℤ_[p]) ^ m} := Ideal.mem_span_singleton.2 hxy
    have h2 := (PadicInt.norm_le_pow_iff_mem_span_pow (x - y) m).2 this
    refine lt_of_le_of_lt h2 (lt_of_eq_of_lt ?_ hm)
    rw [zpow_neg, zpow_natCast, inv_pow]
  rw [hx, hy]

theorem sum_periodic {N : Type} [AddCommGroup N] (g : ℕ → N) (P : ℕ)
    (hg : ∀ i, g (i + P) = g i) (k : ℕ) :
    ∑ i ∈ Finset.range (k * P), g i = k • ∑ i ∈ Finset.range P, g i :=
  _root_.UpperTheory.Reformulated.B.Yra7.main g P hg k

theorem isLocallyConstant_toZModPow (p : ℕ) [Fact p.Prime] (M : ℕ) :
    IsLocallyConstant (PadicInt.toZModPow (p := p) M) := by
  have hp : (0 : ℝ) < p := by exact_mod_cast (Fact.out : p.Prime).pos
  refine (IsLocallyConstant.iff_exists_open _).2 fun x => ?_
  refine ⟨Metric.closedBall x ((p : ℝ) ^ (-(M : ℤ))),
    IsUltrametricDist.isOpen_closedBall _ (zpow_pos hp _).ne',
    Metric.mem_closedBall_self (zpow_pos hp _).le, fun y hy => ?_⟩
  rw [Metric.mem_closedBall, dist_eq_norm] at hy
  have h1 := (PadicInt.norm_le_pow_iff_mem_span_pow (y - x) M).1 hy
  rw [← PadicInt.ker_toZModPow, RingHom.mem_ker, map_sub, sub_eq_zero] at h1
  exact h1

theorem val_toZModPow_dvd (p : ℕ) [Fact p.Prime] (M : ℕ) (z : ℤ_[p]) :
    ((p : ℤ_[p]) ^ M) ∣ z - (((PadicInt.toZModPow (p := p) M z).val : ℕ) : ℤ_[p]) := by
  haveI : NeZero (p ^ M) := ⟨pow_ne_zero _ (Fact.out : p.Prime).ne_zero⟩
  rw [← Ideal.mem_span_singleton, ← PadicInt.ker_toZModPow, RingHom.mem_ker, map_sub, map_natCast,
    ZMod.natCast_zmod_val, sub_self]

theorem exists_primitive (p : ℕ) [Fact p.Prime] {N : Type} [AddCommGroup N] (n : ℕ)
    (hN : ∀ x : N, p ^ n • x = 0) (f : ℤ_[p] → N) (hf : IsLocallyConstant f) :
    ∃ y : ℤ_[p] → N, IsLocallyConstant y ∧ ∀ z, y (z + 1) - y z = f z := by
  obtain ⟨m, hm⟩ := exists_period p f hf
  set M := n + m with hM
  haveI : NeZero (p ^ M) := ⟨pow_ne_zero _ (Fact.out : p.Prime).ne_zero⟩
  let g : ℕ → N := fun i => f (i : ℤ_[p])
  have hper : ∀ i, g (i + p ^ m) = g i := by
    intro i
    apply hm
    refine ⟨1, ?_⟩
    push_cast
    ring
  have hsum : ∑ i ∈ Finset.range (p ^ M), g i = 0 := by
    rw [hM, pow_add, sum_periodic g (p ^ m) hper (p ^ n), hN]
  have hfg : ∀ z, f z = g (PadicInt.toZModPow (p := p) M z).val := by
    intro z
    apply hm
    exact (pow_dvd_pow _ (Nat.le_add_left m n)).trans (val_toZModPow_dvd p M z)
  refine ⟨fun z => ∑ i ∈ Finset.range (PadicInt.toZModPow (p := p) M z).val, g i,
    (isLocallyConstant_toZModPow p M).comp
      (fun a => ∑ i ∈ Finset.range a.val, g i), fun z => ?_⟩
  have hv : (PadicInt.toZModPow (p := p) M z).val < p ^ M := ZMod.val_lt _
  have hval : (PadicInt.toZModPow (p := p) M (z + 1)).val
      = ((PadicInt.toZModPow (p := p) M z).val + 1) % p ^ M := by
    rw [map_add (f := _), map_one, ← ZMod.val_natCast]
    push_cast
    rw [ZMod.natCast_zmod_val]
  simp only [hval]
  rw [hfg z]
  generalize (PadicInt.toZModPow (p := p) M z).val = v at hv
  rcases Nat.lt_or_ge (v + 1) (p ^ M) with h | h
  · rw [Nat.mod_eq_of_lt h, Finset.sum_range_succ, add_sub_cancel_left]
  · have hv1 : v + 1 = p ^ M := by omega
    rw [hv1, Nat.mod_self, Finset.sum_range_zero, zero_sub, neg_eq_iff_add_eq_zero,
      ← Finset.sum_range_succ, hv1]
    exact hsum

theorem eq_of_shift_invariant (p : ℕ) [Fact p.Prime] {N : Type} (f : ℤ_[p] → N)
    (hf : IsLocallyConstant f) (h : ∀ z, f (z + 1) = f z) (z : ℤ_[p]) : f z = f 0 := by
  have hnat : ∀ k : ℕ, f (k : ℤ_[p]) = f 0 := by
    intro k
    induction k with
    | zero => simp
    | succ k ih => rw [Nat.cast_succ, h, ih]
  have hcl : IsClosed {x : ℤ_[p] | f x = f 0} := hf.isClosed_fiber (f 0)
  exact PadicInt.denseRange_natCast.induction_on z hcl hnat

end GlobalTheory.CompanionTheory.PadicShift
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LocalCharacterInducedTied
section
noncomputable section
open NumberField IsDedekindDomain Neutral.B1 Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.L2.Host Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations
open GlobalTheory.HeckeGal GlobalTheory.Pst GlobalTheory.TripleGal
open scoped Classical

namespace GlobalTheory.CompanionTheory.HLCMul

open Formalism.MainNotions.N Module

theorem char_mul {l : ℕ} [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P) (T : LocTied l P AI)
    (K LL : FinExt l) (hcard : Nat.card (↥K.1 →ₐ[ℚ_[l]] ↥LL.1) = finrank ℚ_[l] ↥K.1)
    (ν₁ ν₂ ν₃ : Representation ↥LL.1 ↥(GK K) (Fin 1 → ↥LL.1)) (χ₁ χ₂ : ↥(GK K) → ↥LL.1)
    (h₂ : ∀ g x, ν₂ g x = χ₂ g • x) (h₁ : ∀ g x, ν₁ g x = χ₁ g • x)
    (h₃ : ∀ g x, ν₃ g x = (χ₁ g * χ₂ g) • x)
    (J₁ J₂ : (↥K.1 →ₐ[ℚ_[l]] ↥LL.1) → ℤ)
    (d₂ : IsDR (P.PD K) ν₂)
    (m₁ : ∀ τ a, multV (P.PD K) ν₁ τ a = if a = J₁ τ then 1 else 0)
    (m₂ : ∀ τ a, multV (P.PD K) ν₂ τ a = if a = J₂ τ then 1 else 0) :
    IsDR (P.PD K) ν₃ ∧ ∀ τ a, multV (P.PD K) ν₃ τ a = if a = J₁ τ + J₂ τ then 1 else 0 := by
  have hm : ∀ τ a, multV (P.PD K) ν₃ τ a = if a = J₁ τ + J₂ τ then 1 else 0 := by
    intro τ a
    have := GlobalTheory.TwistJump.multV_twist_char l P AI T K LL (Fin 1 → ↥LL.1) ν₁ ν₃ ν₂ χ₂ h₂
      (fun g x => by rw [h₃, h₁, smul_smul, mul_comm]) d₂ τ (J₂ τ) (m₂ τ) (a - J₂ τ)
    rw [sub_add_cancel] at this
    rw [this, m₁]
    simp only [sub_eq_iff_eq_add]
  refine ⟨?_, hm⟩
  haveI := K.2
  haveI := (GlobalTheory.Per.TiedDdR.ddR_finrank_le l P AI T K LL _ ν₃).1
  have hc : Fintype.card (↥K.1 →ₐ[ℚ_[l]] ↥LL.1) = finrank ℚ_[l] ↥K.1 := by
    rw [← hcard, Nat.card_eq_fintype_card]
  set_option synthInstance.maxHeartbeats 200000 in
  have hone : ∀ τ, finrank ↥LL.1 ↥(DdRE (P.PD K) ν₃ τ) = 1 := by
    intro τ
    obtain ⟨hf, hle, -⟩ := (GlobalTheory.Per.Components.components_finrank l P AI T K LL _ ν₃).1 τ
    have hm1 := hm τ (J₁ τ + J₂ τ)
    rw [if_pos rfl, multV] at hm1
    have hfil : finrank ↥LL.1 ↥(FildR (P.PD K) ν₃ τ (J₁ τ + J₂ τ)) ≤ finrank ↥LL.1 ↥(DdRE (P.PD K) ν₃ τ) :=
      Submodule.finrank_mono (inf_le_left : FildR (P.PD K) ν₃ τ _ ≤ DdRE (P.PD K) ν₃ τ)
    simp only [finrank_fin_fun, finrank_self, Module.finrank_pi, Fintype.card_fin] at hle
    omega
  obtain ⟨e1, -⟩ := GlobalTheory.DeRhamSplit.finrank_DdR (P.PD K) ν₃ hc 0
  rw [IsDR, e1, Finset.sum_congr rfl fun τ _ => hone τ]
  simp [hc]

theorem repE_apply {l : ℕ} [Fact l.Prime] {E Ω : Type} [Field E] [Field Ω] [Algebra E Ω]
    {Gw : Subgroup (Ω ≃ₐ[E] Ω)} {O : Type} [CommRing O] [Algebra ℤ_[l] O] [TopologicalSpace O]
    (Bw : LocBridge l E Ω Gw O) (LL' : FinExt l) (ψ : ↥Gw →* (↥LL'.1)ˣ) (g : ↥(GK Bw.Kw))
    (x : Fin 1 → ↥LL'.1) :
    Bw.repE LL' ((PositivityTheory.HodgeLocalCharacter.HLC.toGL1 ↥LL'.1).comp ψ) g x = ((ψ (Bw.e.symm g) : (↥LL'.1)ˣ) : ↥LL'.1) • x := by
  ext i
  obtain rfl : i = 0 := Subsingleton.elim _ _
  simp [LocBridge.repE, PositivityTheory.HodgeLocalCharacter.HLC.toGL1, Matrix.mulVec, dotProduct]

theorem isdRJ_mul : ∀ {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] {l : ℕ} [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P), Nonempty (LocTied l P AI) →
    ∀ (w : HeightOneSpectrum (𝓞 E)) (A : ValuationSubring Ω), IsPlaceOver A w →
    ∀ (O : Type) [CommRing O] [Algebra ℤ_[l] O] [TopologicalSpace O] (Bw : LocBridge l E Ω (ReciprocityTheory.Gal.Dec (F := E) A) O),
      GlobalTheory.Pst.Induces Bw →
    ∀ (LL' : FinExt l), Bw.LL.1 ≤ LL'.1 → ∀ (ψ₁ ψ₂ : ↥(ReciprocityTheory.Gal.Dec (F := E) A) →* (↥LL'.1)ˣ)
      (J₁ J₂ : (↥Bw.Kw.1 →ₐ[ℚ_[l]] ↥LL'.1) → ℤ),
      PositivityTheory.HodgeLocalCharacter.HLC.IsdRJ Bw P LL' ψ₁ J₁ → PositivityTheory.HodgeLocalCharacter.HLC.IsdRJ Bw P LL' ψ₂ J₂ →
      PositivityTheory.HodgeLocalCharacter.HLC.IsdRJ Bw P LL' (ψ₁ * ψ₂) (J₁ + J₂) := by
  rintro E Ω _ _ _ _ _ l _ P AI ⟨T⟩ w A _ O _ _ _ Bw _ LL' hLL ψ₁ ψ₂ J₁ J₂ ⟨-, m₁⟩ ⟨d₂, m₂⟩
  have hcard := GlobalTheory.DeRhamSplit.card_emb Bw.Kw LL' fun τ x => hLL (Bw.LL_split τ x)
  obtain ⟨a, b⟩ := char_mul P AI T Bw.Kw LL' hcard
    (Bw.repE LL' ((PositivityTheory.HodgeLocalCharacter.HLC.toGL1 ↥LL'.1).comp ψ₁))
    (Bw.repE LL' ((PositivityTheory.HodgeLocalCharacter.HLC.toGL1 ↥LL'.1).comp ψ₂))
    (Bw.repE LL' ((PositivityTheory.HodgeLocalCharacter.HLC.toGL1 ↥LL'.1).comp (ψ₁ * ψ₂)))
    (fun g => ((ψ₁ (Bw.e.symm g) : (↥LL'.1)ˣ) : ↥LL'.1)) (fun g => ((ψ₂ (Bw.e.symm g) : (↥LL'.1)ˣ) : ↥LL'.1))
    (fun g x => repE_apply Bw LL' ψ₂ g x) (fun g x => repE_apply Bw LL' ψ₁ g x)
    (fun g x => by rw [repE_apply]; simp) J₁ J₂
    (by unfold IsDR; simpa [LocBridge.IsdRE] using d₂) m₁ m₂
  refine ⟨?_, fun τ c => ?_⟩
  · unfold IsDR at a
    simpa [LocBridge.IsdRE] using a
  · simpa [LocBridge.multE] using b τ c

end GlobalTheory.CompanionTheory.HLCMul
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.NatCastIsUnit
section
set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry Polynomial DividedPowers GlobalTheory.LogCris GlobalTheory.PDA CrystallineSemistableComparison CrystallineSemistableComparison.CH CrystallineSemistableComparison.B

namespace GlobalTheory.CompanionTheory.RootsDivide

theorem nilp_step {B : Type} [CommRing B] (p : ℕ) (hp : p.Prime) (hpn : IsNilpotent (p : B))
    (y : B) (h : IsNilpotent (y ^ p - 1)) : IsNilpotent (y - 1) := by
  obtain ⟨r, hr⟩ := exists_add_pow_prime_eq hp (y - 1) (1 : B)
  have e1 : (y - 1) ^ p = (y ^ p - 1) - (p : B) * ((y - 1) * r) := by
    have : (y - 1 + 1) = y := by ring
    rw [this] at hr
    rw [hr]; simp only [one_pow]; ring
  refine IsNilpotent.of_pow (m := p) ?_
  rw [e1]
  exact (Commute.all _ _).isNilpotent_sub h ((Commute.all _ _).isNilpotent_mul_right hpn)

theorem nilp_all {B : Type} [CommRing B] (p : ℕ) (hp : p.Prime) (e : ℕ → B)
    (hpn : IsNilpotent (p : B)) (he : ∀ k, e (k + 1) ^ p = e k)
    (h0 : IsNilpotent (e 0 - 1)) (k : ℕ) : IsNilpotent (e k - 1) := by
  induction k with
  | zero => exact h0
  | succ k ih => exact nilp_step p hp hpn _ (by rw [he]; exact ih)

theorem pow_tower {B : Type} [CommRing B] (p : ℕ) (e : ℕ → B)
    (he : ∀ k, e (k + 1) ^ p = e k) (k n : ℕ) : e (k + n) ^ (p ^ n) = e k := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ', pow_mul, ← add_assoc, he, ih]

theorem natCast_isUnit {B : Type} [CommRing B] (p : ℕ) (hp : p.Prime)
    (hpn : IsNilpotent (p : B)) (c : ℕ) (hc : ¬ p ∣ c) : IsUnit (c : B) := by
  have hcop : IsCoprime (c : ℤ) (p : ℤ) := by
    rw [Nat.isCoprime_iff_coprime]
    exact ((Nat.Prime.coprime_iff_not_dvd hp).2 hc).symm
  obtain ⟨a, b, hab⟩ := hcop
  have h1 : (a : B) * (c : B) + (b : B) * (p : B) = 1 := by
    have := congrArg (Int.cast : ℤ → B) hab
    push_cast at this
    exact this
  have h2 : IsUnit ((a : B) * (c : B)) := by
    have : (a : B) * (c : B) = 1 - (b : B) * (p : B) := by rw [← h1]; ring
    rw [this]
    exact ((Commute.all _ _).isNilpotent_mul_left hpn).isUnit_one_sub
  exact isUnit_of_mul_isUnit_right h2

theorem geom_isUnit {B : Type} [CommRing B] (x : B) (hx : IsNilpotent (x - 1)) (n : ℕ)
    (hn : IsUnit (n : B)) : IsUnit (∑ i ∈ Finset.range n, x ^ i) := by
  have hd : (x - 1) ∣ (∑ i ∈ Finset.range n, x ^ i) - (n : B) := by
    have : (∑ i ∈ Finset.range n, x ^ i) - (n : B) = ∑ i ∈ Finset.range n, (x ^ i - 1) := by
      simp [Finset.sum_sub_distrib]
    rw [this]
    refine Finset.dvd_sum fun i _ => ?_
    simpa using sub_dvd_pow_sub_pow x 1 i
  obtain ⟨t, ht⟩ := hd
  have hnil : IsNilpotent ((∑ i ∈ Finset.range n, x ^ i) - (n : B)) := by
    rw [ht]; exact (Commute.all _ _).isNilpotent_mul_right hx
  have : (∑ i ∈ Finset.range n, x ^ i) = (n : B) + ((∑ i ∈ Finset.range n, x ^ i) - (n : B)) := by
    ring
  rw [this]
  exact hnil.isUnit_add_left_of_commute hn (Commute.all _ _)

theorem sub_one_dvd : ∀ (p : ℕ), p.Prime → ∀ {B : Type} [CommRing B] (e : ℕ → B),
    IsNilpotent (p : B) → (∀ k, e (k + 1) ^ p = e k) → IsNilpotent (e 0 - 1) →
    ∀ m c : ℕ, ¬ p ^ m ∣ c → (e m ^ c - 1) ∣ (e 1 - 1) := by
  intro p hp B _ e hpn he h0 m c hc
  have hc0 : c ≠ 0 := by
    rintro rfl
    exact hc (dvd_zero _)
  obtain ⟨j, c', hpc, rfl⟩ := Nat.exists_eq_pow_mul_and_not_dvd hc0 p hp.ne_one
  have hjm : j < m := by
    by_contra hle
    exact hc (Dvd.dvd.mul_right (pow_dvd_pow p (not_lt.1 hle)) c')
  obtain ⟨l, rfl⟩ : ∃ l, m = (l + 1) + j := ⟨m - j - 1, by omega⟩
  set x := e (l + 1) with hxdef
  have hem : e (l + 1 + j) ^ (p ^ j * c') = x ^ c' := by
    rw [pow_mul, pow_tower p e he]
  rw [hem]
  have hxn : IsNilpotent (x - 1) := nilp_all p hp e hpn he h0 _
  have hu : IsUnit (∑ i ∈ Finset.range c', x ^ i) :=
    geom_isUnit x hxn c' (natCast_isUnit p hp hpn c' hpc)
  have hfac : x ^ c' - 1 = (x - 1) * ∑ i ∈ Finset.range c', x ^ i := by
    rw [mul_comm, geom_sum_mul]
  rw [hfac, hu.mul_right_dvd]
  have h1 : x ^ (p ^ l) = e 1 := by
    have := pow_tower p e he 1 l
    rwa [add_comm 1 l] at this
  rw [← h1]
  simpa using sub_dvd_pow_sub_pow x 1 (p ^ l)

end GlobalTheory.CompanionTheory.RootsDivide
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SubSubSmulEqZeroOfSmulEqZero
section
set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry Polynomial DividedPowers GlobalTheory.LogCris GlobalTheory.PDA CrystallineSemistableComparison CrystallineSemistableComparison.CH CrystallineSemistableComparison.B

namespace GlobalTheory.CompanionTheory.TwistedUnit

theorem sub_sub_smul_eq_zero_of_smul_eq_zero {Λ N : Type} [CommRing Λ] [AddCommGroup N]
    [Module Λ N] [Module.Flat Λ N] (γ : N →ₗ[Λ] N) (c μ : Λ)
    (h : ∀ x, ∃ x', γ x - x - c • x = μ • x') (z : N) (hz : μ • z = 0) :
    γ z - z - c • z = 0 := by
  obtain ⟨k, a, y, hx, hf⟩ := Module.Flat.isTrivialRelation_of_sum_smul_eq_zero (R := Λ) (M := N)
    (f := fun _ : Fin 1 => μ) (x := fun _ : Fin 1 => z) (by simpa using hz)
  choose d hd using h
  have hz' : z = ∑ j, a 0 j • y j := hx 0
  have h0 : ∀ j, μ * a 0 j = 0 := fun j => by simpa using hf j
  have hlin : ∀ j, a 0 j • (γ (y j) - y j - c • y j) = 0 := by
    intro j
    rw [hd, smul_smul, mul_comm, h0, zero_smul]
  have hsum : γ z - z - c • z = ∑ j, a 0 j • (γ (y j) - y j - c • y j) := by
    conv_lhs => rw [hz']
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [map_sum, map_smul, Finset.smul_sum, smul_sub, Finset.sum_sub_distrib]
    congr 1
    exact Finset.sum_congr rfl (fun j _ => smul_comm _ _ _)
  rw [hsum]
  exact Finset.sum_eq_zero (fun j _ => hlin j)

theorem smul_eq_zero_of_fixed {Λ N : Type} [CommRing Λ] [AddCommGroup N] [Module Λ N]
    [Module.Flat Λ N] (γ : N →ₗ[Λ] N) (c w ξ μ : Λ) (hμ : μ = c * w * ξ) (hξ : IsNilpotent ξ)
    (h : ∀ x, ∃ x', γ x - x - c • x = μ • x') (x : N) (hx : γ x = x) : μ • x = 0 := by
  have hE := sub_sub_smul_eq_zero_of_smul_eq_zero γ c μ h
  have R : ∀ n : ℕ, ∀ x, (w * ξ) • (γ x - x) = 0 → ∃ u, μ • (x - ξ ^ n • u) = 0 := by
    intro n
    induction n with
    | zero => exact fun x _ => ⟨x, by simp⟩
    | succ n ih =>
      intro x hx
      obtain ⟨x', hx'⟩ := h x
      have h1 : μ • (x + (w * ξ) • x') = 0 := by
        have : μ • (x + (w * ξ) • x') = (w * ξ) • (γ x - x) := by
          subst hμ
          linear_combination (norm := module) -(w * ξ) • hx'
        rw [this, hx]
      have h2 := hE _ h1
      simp only [map_add (f := _), map_smul] at h2
      have hM : (w * ξ) • (γ x' - x') = 0 := by
        subst hμ
        linear_combination (norm := module) h2 - hx'
      obtain ⟨u, hu⟩ := ih x' hM
      refine ⟨-w • u, ?_⟩
      have : μ • (x - ξ ^ (n + 1) • (-w • u))
          = μ • (x + (w * ξ) • x') - (w * ξ) • (μ • (x' - ξ ^ n • u)) := by
        module
      rw [this, h1, hu]
      simp
  obtain ⟨n, hn⟩ := hξ
  obtain ⟨u, hu⟩ := R n x (by simp [hx])
  simpa [hn] using hu

theorem exists_mem_smul_top {Λ N : Type} [CommRing Λ] [AddCommGroup N] [Module Λ N]
    (γ : N →ₗ[Λ] N) (c μ : Λ) (h : ∀ x, ∃ x', γ x - x - c • x = μ • x') (𝔞 : Ideal Λ) (x : N)
    (hx : x ∈ 𝔞 • (⊤ : Submodule Λ N)) :
    ∃ x₁ ∈ 𝔞 • (⊤ : Submodule Λ N), γ x - x - c • x = μ • x₁ := by
  induction hx using Submodule.smul_induction_on' with
  | smul a ha n hn =>
    obtain ⟨n', hn'⟩ := h n
    refine ⟨a • n', Submodule.smul_mem_smul ha trivial, ?_⟩
    rw [map_smul]
    linear_combination (norm := module) a • hn'
  | add x hx y hy ihx ihy =>
    obtain ⟨x₁, hx₁, e₁⟩ := ihx
    obtain ⟨y₁, hy₁, e₂⟩ := ihy
    refine ⟨x₁ + y₁, Submodule.add_mem _ hx₁ hy₁, ?_⟩
    rw [map_add (f := _)]
    linear_combination (norm := module) e₁ + e₂

theorem exists_sub_eq_smul {Λ N : Type} [CommRing Λ] [AddCommGroup N] [Module Λ N]
    (γ : N →ₗ[Λ] N) (c w ξ μ : Λ) (hμ : μ = c * w * ξ) (hξ : IsNilpotent ξ)
    (h : ∀ x, ∃ x', γ x - x - c • x = μ • x') (𝔞 : Ideal Λ) (x : N)
    (hx : x ∈ 𝔞 • (⊤ : Submodule Λ N)) :
    ∃ y ∈ (Ideal.span {ξ} * 𝔞) • (⊤ : Submodule Λ N), γ y - y = μ • x := by
  obtain ⟨n, hn⟩ := hξ
  have P : ∀ m k : ℕ, m + k = n → ∀ x ∈ 𝔞 • (⊤ : Submodule Λ N),
      ∃ y ∈ (Ideal.span {ξ} * 𝔞) • (⊤ : Submodule Λ N), γ y - y = (μ * ξ ^ k) • x := by
    intro m
    induction m with
    | zero =>
      intro k hk x _
      have : ξ ^ k = 0 := by
        rw [show k = n by omega, hn]
      exact ⟨0, Submodule.zero_mem _, by simp [this]⟩
    | succ m ih =>
      intro k hk x hx
      obtain ⟨x₁, hx₁, e⟩ := exists_mem_smul_top γ c μ h 𝔞 x hx
      obtain ⟨y', hy', e'⟩ := ih (k + 1) (by omega) (w • x₁)
        (Submodule.smul_of_tower_mem _ w hx₁)
      have hξx : ξ • x ∈ (Ideal.span {ξ} * 𝔞) • (⊤ : Submodule Λ N) := by
        rw [Submodule.mul_smul]
        exact Submodule.smul_mem_smul (Ideal.mem_span_singleton_self ξ) hx
      refine ⟨(w * ξ ^ k) • (ξ • x) - y',
        Submodule.sub_mem _ (Submodule.smul_of_tower_mem _ _ hξx) hy', ?_⟩
      simp only [map_sub, map_smul]
      subst hμ
      linear_combination (norm := module) (w * ξ ^ (k + 1)) • e - e'
  simpa using P n 0 rfl x hx

theorem twisted_bijective_up_to :
    ∀ {Λ N : Type} [CommRing Λ] [AddCommGroup N] [Module Λ N] [Module.Flat Λ N]
      (γ : N →ₗ[Λ] N) (c w ξ μ : Λ), μ = c * w * ξ → IsNilpotent ξ →
      (∀ x, ∃ x', γ x - x - c • x = μ • x') →
      (∀ x, γ x = x → μ • x = 0) ∧ ∀ (𝔞 : Ideal Λ), ∀ x ∈ 𝔞 • (⊤ : Submodule Λ N),
        ∃ y ∈ (Ideal.span {ξ} * 𝔞) • (⊤ : Submodule Λ N), γ y - y = μ • x := by
  intro Λ N _ _ _ _ γ c w ξ μ hμ hξ h
  exact ⟨smul_eq_zero_of_fixed γ c w ξ μ hμ hξ h,
    fun 𝔞 x hx => exists_sub_eq_smul γ c w ξ μ hμ hξ h 𝔞 x hx⟩

end GlobalTheory.CompanionTheory.TwistedUnit
end

