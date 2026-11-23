module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Foundations.StandardFiveNontrivial
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0080
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0165
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0005
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0006
public import Development.AbelianVarietyTheory.Statements.CuspidalUnitaryTwists.Chapter
public import CompanionTheory.EightfoldTheory.VariationTheory.AutomorphicForms.Newform
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.DepletedCuspEigenformHeckeRelations
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0169
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0154
public import Development.AbelianVarietyTheory.Definitions.Foundations.NotCoboundaryConstantOne
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0151
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0167
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0158
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0153
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0166
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0050
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0159

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.GoodTupleProjectorIsProjCentral
section
open Polynomial Classical GlobalTheory.BadShare

namespace GlobalTheory.BadShare

theorem conv_comm_of_classFun {G : Type} [Group G] [Fintype G] (e : G → ℂ) (he : ∀ x y, e (x * y) = e (y * x))
    (a : G → ℂ) : conv e a = conv a e := by
  funext x
  simp only [conv]
  refine Fintype.sum_equiv ((Equiv.inv G).trans (Equiv.mulRight x)) _ _ fun y => ?_
  simp only [Equiv.trans_apply, Equiv.inv_apply, Equiv.coe_mulRight]
  rw [mul_comm, he (y⁻¹ * x)⁻¹ x]
  congr 2
  group

theorem conv_finsetSum_finsetSum {G κ : Type} [Group G] [Fintype G] (s t : Finset κ) (a b : κ → G → ℂ) :
    conv (∑ i ∈ s, a i) (∑ j ∈ t, b j) = ∑ i ∈ s, ∑ j ∈ t, conv (a i) (b j) := by
  funext x
  simp only [conv, Finset.sum_apply, Finset.sum_mul_sum]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun i _ => Finset.sum_comm

theorem isProj_finsetSum {G κ : Type} [Group G] [Fintype G] (s : Finset κ) (a : κ → G → ℂ) (h : ∀ i ∈ s, IsProj (a i))
    (ho : ∀ i ∈ s, ∀ j ∈ s, i ≠ j → conv (a i) (a j) = 0) : IsProj (∑ i ∈ s, a i) := by
  refine ⟨?_, fun x => ?_⟩
  · rw [conv_finsetSum_finsetSum]
    refine Finset.sum_congr rfl fun i hi => ?_
    rw [Finset.sum_eq_single_of_mem i hi fun j hj hne => ho i hi j hj hne.symm, (h i hi).1]
  set_option synthInstance.maxHeartbeats 100000 in
    · simp only [Finset.sum_apply, map_sum]
      exact Finset.sum_congr rfl fun i hi => (h i hi).2 x

theorem eGood_isProj_central : ∀ (g : ℕ) [Fact g.Prime] (N : ℕ), ∀ (m : ℕ) (ι : Type) [Fintype ι] (τ : ι → (ZMod g)[X] → GG g N → ℂ) (ch : ι → Fin m → (ZMod g)ˣ), (∀ v, IsSeries (τ v)) → IsProj (eGood τ ch) ∧ ∀ a, conv (eGood τ ch) a = conv a (eGood τ ch) := by
  intro g _ N m ι _ τ ch hτ
  have hmem : ∀ F ∈ goodSet g N ch, ∀ v, F v ∈ sqSet g N := fun F hF =>
    (good_iff.1 (mem_goodSet_iff_good.1 hF)).1
  refine ⟨isProj_finsetSum _ _ (fun F hF => ?_) fun F hF F' hF' hne => ?_, conv_comm_of_classFun _ fun x y => ?_⟩
  · refine (tens_calculus ι (GG g N) (GG g N)).2.1 _ fun v => ?_
    obtain ⟨V, hV, hχ, -⟩ := (hτ v).2 _ (hmem F hF v)
    rw [← hχ]
    exact (_root_.GlobalTheory.BadShare.ZCalc.zc_calc _ V).1
  · rw [conv_tens]
    obtain ⟨v, hv⟩ := Function.ne_iff.1 hne
    obtain ⟨V, hV, hχ, -⟩ := (hτ v).2 _ (hmem F hF v)
    obtain ⟨V', hV', hχ', -⟩ := (hτ v).2 _ (hmem F' hF' v)
    have h0 : conv (zc (τ v (F v))) (zc (τ v (F' v))) = 0 := by
      rw [← hχ, ← hχ']
      refine (_root_.GlobalTheory.BadShare.ZCalc.zc_calc _ V).2.2.1 V' ?_
      rw [hχ, hχ']
      exact fun h => hv ((hτ v).1 (hmem F hF v) (hmem F' hF' v) h)
    funext x
    exact Finset.prod_eq_zero (Finset.mem_univ v) (congrFun h0 (x v))
  · simp only [eGood, Finset.sum_apply, tens]
    refine Finset.sum_congr rfl fun F hF => Finset.prod_congr rfl fun v _ => ?_
    obtain ⟨V, -, hχ, -⟩ := (hτ v).2 _ (hmem F hF v)
    simp only [zc, ← hχ, Pi.mul_apply, mul_inv_rev]
    rw [FDRep.char_mul_comm]

end GlobalTheory.BadShare
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.HeckeRootsNePrimePowMulRootOfUnity
section
open UpperHalfPlane Complex MeasureTheory CongruenceSubgroup GlobalTheory.EisM UpperTheory.V.Af Filter Topology
open scoped MatrixGroups Real ComplexConjugate Manifold ModularForm

namespace GlobalTheory.FactorsAtL

theorem norm_one_of_pow {R : Type*} [NormedDivisionRing R] {z : R} {n : ℕ} (hn : 0 < n) (h : z ^ n = 1) :
    ‖z‖ = 1 := by
  have : ‖z‖ ^ n = 1 := by rw [← norm_pow, h, norm_one]
  exact (pow_eq_one_iff_of_nonneg (norm_nonneg z) hn.ne').1 this

theorem char_inv_facts {N : ℕ} (hN : 0 < N) (χ : DirichletCharacter ℂ N) (l : ℕ) (hl : l.Coprime N) :
    (χ⁻¹ (l : ZMod N)) ^ N.totient = 1 ∧ χ⁻¹ (l : ZMod N) * χ (l : ZMod N) = 1 := by
  haveI : NeZero N := ⟨hN.ne'⟩
  have hu : IsUnit (l : ZMod N) := (ZMod.isUnit_iff_coprime l N).2 hl
  constructor
  · obtain ⟨v, hv⟩ := hu
    rw [← hv, ← map_pow, ← Units.val_pow_eq_pow_val, ZMod.pow_totient, Units.val_one, map_one]
  · rw [show χ⁻¹ (l : ZMod N) * χ (l : ZMod N) = (χ⁻¹ * χ) (l : ZMod N) from rfl, MulChar.inv_mul, MulChar.one_apply hu]

theorem norm_natCast_self (l : ℕ) [Fact l.Prime] : ‖(l : PadicAlgCl l)‖ = (l : ℝ)⁻¹ := by
  rw [← map_natCast (algebraMap ℚ_[l] (PadicAlgCl l)), PadicAlgCl.norm_extends, Padic.norm_p]

end GlobalTheory.FactorsAtL

namespace GlobalTheory.FactorsAtL

theorem factors_ne_zero : ∀ (l : ℕ) [Fact l.Prime] (ι : PadicAlgCl l ≃+* ℂ) (e N : ℕ) (χ : DirichletCharacter ℂ N)
    (g : ℕ → ℂ) (α β ζ : ℂ), 1 ≤ e → 0 < N → ¬ l ∣ N → Prim (2 * e + 1) N χ g → α + β = χ⁻¹ l * g l →
    α * β = χ⁻¹ l * (l : ℂ) ^ (2 * e) → ‖ι.symm α‖ = 1 → (∃ n : ℕ, 0 < n ∧ ζ ^ n = 1) →
    α ≠ ζ ∧ β ≠ l * ζ ∧ ∀ j : ℕ, 1 ≤ j → α ≠ (l : ℂ) ^ j * ζ := by
  intro l _ ι e N χ g α β ζ he hN hlN hP hs hp hα ⟨n, hn, hζ⟩
  have hlp : l.Prime := Fact.out
  have hcop : l.Coprime N := (Nat.Prime.coprime_iff_not_dvd hlp).2 hlN
  obtain ⟨hut, huc⟩ := char_inv_facts hN χ l hcop
  have htot : 0 < N.totient := Nat.totient_pos.2 hN
  have hl1 : (1 : ℝ) < l := by exact_mod_cast hlp.one_lt
  have hl0 : (0 : ℝ) < l := by linarith
  have hinv0 : (0 : ℝ) < (l : ℝ)⁻¹ := inv_pos.2 hl0
  have hinv1 : (l : ℝ)⁻¹ < 1 := inv_lt_one_of_one_lt₀ hl1
  have hnl : ‖ι.symm (l : ℂ)‖ = (l : ℝ)⁻¹ := by rw [map_natCast]; exact norm_natCast_self l
  have hnζ : ‖ι.symm ζ‖ = 1 := norm_one_of_pow hn (by rw [← map_pow, hζ, map_one])
  have hnu : ‖ι.symm (χ⁻¹ (l : ZMod N))‖ = 1 := norm_one_of_pow htot (by rw [← map_pow, hut, map_one])
  refine ⟨?_, ?_, ?_⟩
  · intro hαζ
    have hcα : ‖α‖ = 1 := by rw [hαζ]; exact Complex.norm_eq_one_of_pow_eq_one hζ hn.ne'
    have hcu : ‖χ⁻¹ (l : ZMod N)‖ = 1 := Complex.norm_eq_one_of_pow_eq_one hut htot.ne'
    have hβn : ‖β‖ = (l : ℝ) ^ (2 * e) := by
      have h := congrArg norm hp
      rw [norm_mul, norm_mul, hcα, hcu, norm_pow, Complex.norm_natCast, one_mul, one_mul] at h
      exact h
    obtain ⟨_, hrec, _⟩ := _root_.GlobalTheory.EisM.hecke_relations (2 * e + 1) N χ g (by omega) hN hP
    obtain ⟨_, ⟨C, hC⟩, _⟩ := _root_.GlobalTheory.rankin_mean_square (2 * e + 1) N (ch χ) g (by omega) hP.cf
    set u := χ⁻¹ (l : ZMod N) with hu_def
    let c : ℕ → ℂ := fun r => u ^ r * g (l ^ r)
    have hc0 : c 0 = 1 := by simp [c, hP.one]
    have hc1 : c 1 = α + β := by simp [c, hs]
    have hcr : ∀ r, c (r + 2) = (α + β) * c (r + 1) - α * β * c r := by
      intro r
      simp only [c]
      rw [hrec l r hlp hlN, hs, hp, show 2 * e + 1 - 1 = 2 * e by omega]
      have key : u ^ (r + 2) * χ (l : ZMod N) = u ^ (r + 1) := by rw [pow_succ, mul_assoc, huc, mul_one]
      linear_combination (-(l : ℂ) ^ (2 * e) * g (l ^ r)) * key
    set s := Real.sqrt l with hs_def
    have hs2 : s ^ 2 = l := Real.sq_sqrt hl0.le
    have hs1 : 1 < s := by rw [hs_def]; exact Real.lt_sqrt (by norm_num) |>.2 (by simpa using hl1)
    set R := s ^ (2 * e + 1) with hR
    have hR0 : 0 ≤ R := by positivity
    have hbound : ∀ r, ‖c r‖ ≤ Real.sqrt (max C 0) * R ^ r := by
      intro r
      have h1 : ‖c r‖ = ‖g (l ^ r)‖ := by
        simp only [c]; rw [norm_mul, norm_pow, hcu, one_pow, one_mul]
      have hX : ((l ^ r : ℕ) : ℝ) ^ (2 * e + 1) = (R ^ r) ^ 2 := by
        push_cast; rw [hR, ← hs2]; ring
      have h2 : ‖g (l ^ r)‖ ^ 2 ≤ max C 0 * (R ^ r) ^ 2 := by
        rw [← hX]; exact (hC _).trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity))
      rw [h1, ← Real.sqrt_sq (norm_nonneg _), ← Real.sqrt_sq (pow_nonneg hR0 r), ← Real.sqrt_mul (le_max_right _ _)]
      exact Real.sqrt_le_sqrt h2
    obtain ⟨_, hβR⟩ := _root_.GlobalTheory.roots_norm_le_of_bounded_two_step_recursion α β c (Real.sqrt (max C 0)) R hR0 hc0 hc1 hcr hbound
    rw [hβn, ← hs2, ← pow_mul, hR] at hβR
    have : s ^ (2 * e + 1) < s ^ (2 * (2 * e)) := pow_lt_pow_right₀ hs1 (by omega)
    linarith
  · intro hβζ
    have h := congrArg (fun z => ‖ι.symm z‖) hp
    simp only [map_mul, map_pow, norm_mul, norm_pow] at h
    rw [hα, hnu, hnl, one_mul, one_mul, hβζ, map_mul, norm_mul, hnl, hnζ, mul_one] at h
    have : ((l : ℝ)⁻¹) ^ (2 * e) < ((l : ℝ)⁻¹) ^ 1 := pow_lt_pow_right_of_lt_one₀ hinv0 hinv1 (by omega)
    rw [pow_one] at this
    linarith
  · intro j hj hαj
    rw [hαj, map_mul, map_pow, norm_mul, norm_pow, hnl, hnζ, mul_one] at hα
    have : ((l : ℝ)⁻¹) ^ j < 1 := pow_lt_one₀ hinv0.le hinv1 (by omega)
    linarith

end GlobalTheory.FactorsAtL
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.InvariantsFromFiniteLevel
section
open GlobalTheory.K5

namespace GlobalTheory.K5.FinLevel

variable {p : ℕ} [Fact p.Prime] {Ω : Type} [Field Ω] [Algebra (O0 p) Ω]

theorem charZero_of_tower (T : Tower p Ω) : CharZero Ω := by
  have hpp : p.Prime := Fact.out
  have hp : (p : Ω) ≠ 0 := by
    intro h0
    haveI : CharP Ω p := (CharP.charP_iff_prime_eq_zero hpp).mpr h0
    have hz := T.prim 1
    rw [pow_one] at hz
    have h1 : (T.ζ 1 - 1) ^ p = 0 := by rw [sub_pow_char, one_pow, hz.pow_eq_one, sub_self]
    have h2 : T.ζ 1 = 1 := sub_eq_zero.mp (pow_eq_zero_iff hpp.ne_zero |>.mp h1)
    rw [h2] at hz
    exact hpp.one_lt.ne' (hz.eq_orderOf.trans orderOf_one)
  let f : ℤ_[p] →+* Ω :=
    (algebraMap (O0 p) Ω).comp ((algebraMap (Lau p) (O0 p)).comp (algebraMap ℤ_[p] (Lau p)))
  refine charZero_of_inj_zero fun n hn => ?_
  by_contra hn0
  obtain ⟨e, m, hm, rfl⟩ := Nat.exists_eq_pow_mul_and_not_dvd hn0 p hpp.one_lt.ne'
  have hu : IsUnit (((m : ℤ) : ℤ_[p])) := by
    refine PadicInt.isUnit_iff.mpr (le_antisymm (PadicInt.norm_le_one _) (not_lt.mp fun h => hm ?_))
    exact Int.natCast_dvd_natCast.mp ((PadicInt.norm_int_lt_one_iff_dvd _).mp h)
  have hmu : IsUnit (m : Ω) := by
    have := hu.map f
    simpa using this
  push_cast at hn
  rcases mul_eq_zero.mp hn with h | h
  · exact hp (pow_eq_zero_iff' |>.mp h).1
  · exact hmu.ne_zero h

end GlobalTheory.K5.FinLevel

namespace GlobalTheory.K5.FinLevel

variable {p : ℕ} [Fact p.Prime] {Ω : Type} [Field Ω] [Algebra (O0 p) Ω]

theorem qq_eq_pow (T : Tower p Ω) (i d : ℕ) : T.qq i = T.qq (i + d) ^ (p ^ d) := by
  induction d with
  | zero => simp
  | succ d ih => rw [ih, ← T.qpow (i + d), ← pow_mul, ← pow_succ', add_assoc]

end GlobalTheory.K5.FinLevel

namespace GlobalTheory.K5.FinLevel

variable {p : ℕ} [Fact p.Prime] {Ω : Type} [Field Ω] [Algebra (O0 p) Ω]

end GlobalTheory.K5.FinLevel

namespace GlobalTheory.K5.FinLevel

variable {p : ℕ} [Fact p.Prime] {Ω : Type} [Field Ω] [Algebra (O0 p) Ω]

theorem sum_fixed (H : Subgroup (Gal p Ω)) (E : Finset (Gal p Ω)) (y₀ x : Ω)
    (hEH : ∀ g ∈ E, g ∈ H)
    (huniq : ∀ h ∈ H, ∃! g, g ∈ E ∧ h y₀ = g y₀ ∧ ∀ s ∈ ({x} : Finset Ω), h s = g s) :
    ∀ h ∈ H, h (∑ g ∈ E, g (y₀ * x)) = ∑ g ∈ E, g (y₀ * x) := by
  classical
  simp only [Finset.mem_singleton, forall_eq] at huniq
  let rep : Gal p Ω → Gal p Ω := fun a => if ha : a ∈ H then (huniq a ha).exists.choose else 1
  have hrep : ∀ a ∈ H, rep a ∈ E ∧ a y₀ = rep a y₀ ∧ a x = rep a x := by
    intro a ha
    simp only [rep, dif_pos ha]
    exact (huniq a ha).exists.choose_spec
  have hun : ∀ a ∈ H, ∀ g ∈ E, a y₀ = g y₀ → a x = g x → rep a = g := by
    intro a ha g hg h1 h2
    exact ((huniq a ha).unique (hrep a ha) ⟨hg, h1, h2⟩)
  intro h hh
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sum]
  have hmem : ∀ g ∈ E, h * g ∈ H := fun g hg => H.mul_mem hh (hEH g hg)
  have hmem' : ∀ g ∈ E, h⁻¹ * g ∈ H := fun g hg => H.mul_mem (H.inv_mem hh) (hEH g hg)
  refine Finset.sum_bij' (fun g _ => rep (h * g)) (fun g _ => rep (h⁻¹ * g))
    (fun g hg => (hrep _ (hmem g hg)).1) (fun g hg => (hrep _ (hmem' g hg)).1) ?_ ?_ ?_
  · intro g hg
    obtain ⟨_, h1, h2⟩ := hrep _ (hmem g hg)
    refine hun _ (hmem' _ (hrep _ (hmem g hg)).1) g hg ?_ ?_
    · rw [AlgEquiv.mul_apply, ← h1, AlgEquiv.mul_apply, AlgEquiv.aut_inv, AlgEquiv.symm_apply_apply]
    · rw [AlgEquiv.mul_apply, ← h2, AlgEquiv.mul_apply, AlgEquiv.aut_inv, AlgEquiv.symm_apply_apply]
  · intro g hg
    obtain ⟨_, h1, h2⟩ := hrep _ (hmem' g hg)
    refine hun _ (hmem _ (hrep _ (hmem' g hg)).1) g hg ?_ ?_
    · rw [AlgEquiv.mul_apply, ← h1, AlgEquiv.mul_apply, AlgEquiv.aut_inv, AlgEquiv.apply_symm_apply]
    · rw [AlgEquiv.mul_apply, ← h2, AlgEquiv.mul_apply, AlgEquiv.aut_inv, AlgEquiv.apply_symm_apply]
  · intro g hg
    obtain ⟨_, h1, h2⟩ := hrep _ (hmem g hg)
    show (h * g) (y₀ * x) = _
    rw [map_mul, map_mul (rep (h * g)), h1, h2]

end GlobalTheory.K5.FinLevel
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsModularFormCoeffSeqHeckeTOfPrimeNotDvd
section
open UpperHalfPlane Complex MeasureTheory CongruenceSubgroup GlobalTheory.EisM UpperTheory.V.Af Filter Topology
open scoped MatrixGroups Real ComplexConjugate Manifold ModularForm

namespace GlobalTheory.EisM

theorem To_MF : ∀ (k L N q : ℕ) (ε : DirichletCharacter ℂ N) (a : ℕ → ℂ), 1 ≤ k → N ∣ L → q.Prime → ¬ q ∣ L →
    MF k L (ch ε) a → MF k L (ch ε) (To k (ch ε q) q a) := by
  intro k L N q ε a hk hNL hq hqL ha
  have h1 : ch ε 1 = 1 := by simp [ch]
  obtain ⟨hP, hqs⟩ := _root_.GlobalTheory.EisM.qs_To_hsum k q (ch ε) a hk hq.pos h1 ha.1
  refine ⟨hP, ?_⟩
  rw [hqs]
  refine _root_.GlobalTheory.EisM.hsum_inv_of_stable k L L N ε (DT L q) (Option (Fin q)) (repT q) (qs a) hk hNL hNL ?_ ?_
    (_root_.GlobalTheory.EisM.lRep_DT_repT L q hq hqL) ha.2
  · rintro δ ⟨hdet, hL⟩
    refine ⟨by rw [hdet]; exact_mod_cast hq.pos, ?_⟩
    exact (Int.natCast_dvd_natCast.mpr hNL).trans hL
  · rintro δ ⟨hdet, hL⟩ γ hγ
    refine ⟨?_, ?_⟩
    · rw [Matrix.det_mul, hdet]
      simp
    · simp only [Matrix.mul_apply, Fin.sum_univ_two]
      exact dvd_add (dvd_mul_of_dvd_left hL _) (dvd_mul_of_dvd_right hγ _)

end GlobalTheory.EisM
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsModularFormCoeffSeqHeckeUAndDepletion
section
open UpperHalfPlane Complex MeasureTheory CongruenceSubgroup GlobalTheory.EisM UpperTheory.V.Af Filter Topology
open scoped MatrixGroups Real ComplexConjugate Manifold ModularForm

namespace GlobalTheory

theorem dep_eq_sub (l : ℕ) (a : ℕ → ℂ) : dep l a = a + (-1 : ℂ) • Vo l (Uo l a) := by
  funext n
  simp only [dep, Vo, Uo, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  split_ifs with h
  · rw [Nat.mul_div_cancel' h]; ring
  · ring

theorem depletion_mf : ∀ (k L l : ℕ) (χ : ℤ → ℂ) (a : ℕ → ℂ), 1 ≤ k → l.Prime → l ∣ L → (∀ d, χ (d + L) = χ d) → MF k L χ a → MF k L χ (Uo l a) ∧ MF k (L * l) χ (dep l a) := by
  intro k L l χ a hk hl hlL hχ ha
  have haL : MF k (L * l) χ a := ((_root_.GlobalTheory.EisM.mf_linear k L χ).2.2.2.2.1 (L * l) a (dvd_mul_right L l) ha)
  have hU : MF k L χ (Uo l a) := _root_.GlobalTheory.Uo_lowers_level k L l χ a hk hl hlL hχ haL
  refine ⟨hU, ?_⟩
  have hV : MF k (L * l) χ (Vo l (Uo l a)) := (_root_.GlobalTheory.Vo_level k L l χ (Uo l a) hl.pos).1 hU
  have hV' := ((_root_.GlobalTheory.EisM.mf_linear k (L * l) χ).2.2.1 (-1 : ℂ) _ hV).1
  rw [dep_eq_sub]
  exact ((_root_.GlobalTheory.EisM.mf_linear k (L * l) χ).2.1 _ _ haL hV').1

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.KummerCarryCoboundaryTwistCochainStatement
section
open GlobalTheory.NeedB Polynomial
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.kummer_carry_coboundary_twist_cochain : ∀ (K Ω : Type) [Field K] [Field Ω] [Algebra K Ω] [Algebra.IsAlgebraic K Ω] (N : ℕ) (ζ : Ω), 0 < N →
  IsPrimitiveRoot ζ N → (∀ g : Ω ≃ₐ[K] Ω, g ζ = ζ) →
  ∀ (a b : K) (α β : Ω), a ≠ 0 → b ≠ 0 → α ^ N = algebraMap K Ω a → β ^ N = algebraMap K Ω b →
  ∀ w : (Ω ≃ₐ[K] Ω) → Ωˣ, IsLocallyConstant w → (∀ g h, (w g : Ω) * g (w h) * α ^ (kum (N := N) ζ β (g * h)).val =
    α ^ ((kum (N := N) ζ β g).val + (kum (N := N) ζ β h).val) * w (g * h)) →
  ∃ v : (Ω ≃ₐ[K] Ω) → Ωˣ, IsLocallyConstant v ∧
    ∀ g h, (v g : Ω) * g (v h) = ζ ^ (kum (N := N) ζ α g * kum (N := N) ζ β h).val * v (g * h) := by
  first | exact @GlobalTheory.NeedB.TwistCochain.twist_cochain | exact GlobalTheory.NeedB.TwistCochain.twist_cochain | (intros; apply GlobalTheory.NeedB.TwistCochain.twist_cochain <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.LseriesNeZeroReGeOneOfPositivity
section
open UpperHalfPlane Complex MeasureTheory CongruenceSubgroup GlobalTheory.EisM UpperTheory.V.Af Filter Topology
open scoped MatrixGroups Real ComplexConjugate Manifold ModularForm

namespace GlobalTheory.EisM

theorem not_dvd_of_prime_of_eq_neg_one {M p : ℕ} (hp : p.Prime) (h : (p : ZMod M) = -1) :
    ¬ p ∣ M := by
  intro hpM
  have h1 : ((p + 1 : ℕ) : ZMod M) = 0 := by push_cast; rw [h]; ring
  have h1' : M ∣ p + 1 := (CharP.cast_eq_zero_iff (ZMod M) M (p + 1)).mp h1
  have : p ∣ p + 1 := hpM.trans h1'
  have : p ∣ 1 := (Nat.dvd_add_right (dvd_refl p)).mp this
  exact hp.one_lt.ne' (Nat.dvd_one.mp this)

theorem lseries_ne_zero_edge : ∀ (M : ℕ) (b ω : ℕ → ℂ) (C : ℝ) (Λ : ℂ → ℂ), 0 < M → b 1 = 1 → b 0 = 0 → (∀ m n : ℕ, m.Coprime n → b (m * n) = b m * b n) → (∀ n, ¬ n.Coprime M → b n = 0) → (∀ p r : ℕ, p.Prime → ¬ p ∣ M → ‖ω p‖ = 1 ∧ b (p ^ (r + 2)) = b p * b (p ^ (r + 1)) - ω p * b (p ^ r)) → (∀ n : ℕ, ‖b n‖ ^ 2 ≤ C * n) → (∀ s : ℝ, 0 < s → Summable fun n : ℕ => ‖b n‖ ^ 2 / (n : ℝ) ^ (1 + s)) → (∀ s : ℝ, 0 < s → s ≤ 1 → s * ∑' n : ℕ, ‖b n‖ ^ 2 / (n : ℝ) ^ (1 + s) ≤ C) → (∀ p : ℕ, p.Prime → ¬ p ∣ M → (p : ZMod M) = -1 → (b p).re = 0) → Differentiable ℂ Λ → (∀ s : ℝ, 0 < s → LSeries b ((1 + s : ℝ) : ℂ) = Λ ((1 + s : ℝ) : ℂ)) → ∀ w : ℝ, 1 ≤ w → Λ w ≠ 0 := by
  intro M b ω C Λ hM hb1 hb0 hmul hcop hrec hC hsum hsC hre hdiff hL w hw
  have G := fun s hs => _root_.GlobalTheory.EisM.global_positivity_ineq M b ω s C hs hb1 hb0 hmul hcop hrec hC (hsum s hs)
  rcases hw.lt_or_eq with hw | rfl
  · intro h0
    have hs : 0 < w - 1 := by linarith
    have := G (w - 1) hs 0
    have e : ((1 + (w - 1) : ℝ) : ℂ) = (w : ℂ) := by push_cast; ring
    rw [hL _ hs, e, h0] at this
    norm_num at this
  · intro h0
    rw [Complex.ofReal_one] at h0

    have hO := (hdiff 1).isBigO_sub
    have ht : Tendsto (fun s : ℝ => ((1 + s : ℝ) : ℂ)) (𝓝[>] (0 : ℝ)) (𝓝 1) := by
      have : Continuous fun s : ℝ => ((1 + s : ℝ) : ℂ) := by fun_prop
      have h := this.tendsto 0
      simp only [add_zero, Complex.ofReal_one] at h
      exact h.mono_left nhdsWithin_le_nhds
    obtain ⟨c, hc, hcw⟩ := (hO.comp_tendsto ht).exists_pos
    have hev : ∀ᶠ s in 𝓝[>] (0 : ℝ), 0 < s ∧ s ≤ 1 ∧ ‖Λ ((1 + s : ℝ) : ℂ)‖ ≤ c * s := by
      have h1 := hcw.bound
      have h2 : ∀ᶠ s in 𝓝[>] (0 : ℝ), 0 < s := self_mem_nhdsWithin
      have h3 : ∀ᶠ s in 𝓝[>] (0 : ℝ), s ≤ 1 :=
        nhdsWithin_le_nhds (Iic_mem_nhds (by norm_num : (0:ℝ) < 1))
      filter_upwards [h1, h2, h3] with s h1 h2 h3
      refine ⟨h2, h3, ?_⟩
      simp only [Function.comp, h0, sub_zero] at h1
      have : ((1 + s : ℝ) : ℂ) - 1 = (s : ℂ) := by push_cast; ring
      rw [this, Complex.norm_real, Real.norm_eq_abs, abs_of_pos h2] at h1
      exact h1

    have hC0 : 0 ≤ C := by
      have := hsC 1 one_pos le_rfl
      refine le_trans ?_ this
      exact mul_nonneg zero_le_one (tsum_nonneg fun n => div_nonneg (sq_nonneg _) (Real.rpow_nonneg (Nat.cast_nonneg _) _))
    set B : ℝ := 4 * c ^ 2 * C with hB
    let T : ℕ → Finset ℕ := fun X => (Finset.range X).filter (fun p => p.Prime ∧ (p : ZMod M) = -1)

    have key : ∀ X : ℕ, ∀ s : ℝ, 0 < s → s ≤ 1 → ‖Λ ((1 + s : ℝ) : ℂ)‖ ≤ c * s →
        ∑ p ∈ T X, (1 : ℝ) / (p : ℝ) ^ (1 + s) ≤ B := by
      intro X s hs hs1 hΛ
      set S := ∑' n : ℕ, ‖b n‖ ^ 2 / (n : ℝ) ^ (1 + s) with hS
      have hS0 : 0 ≤ S := tsum_nonneg fun n => div_nonneg (sq_nonneg _) (Real.rpow_nonneg (Nat.cast_nonneg _) _)
      have g := G s hs X
      rw [hL s hs] at g
      set F := (Finset.range X).filter (fun p => p.Prime ∧ ¬ p ∣ M)
      have hsub : T X ⊆ F := by
        intro p hp
        simp only [T, F, Finset.mem_filter] at hp ⊢
        exact ⟨hp.1, hp.2.1, not_dvd_of_prime_of_eq_neg_one hp.2.1 hp.2.2⟩
      have h1 : ∑ p ∈ T X, (1 : ℝ) / (p : ℝ) ^ (1 + s) ≤ ∑ p ∈ T X, ‖1 + b p‖ ^ 2 / (p : ℝ) ^ (1 + s) := by
        apply Finset.sum_le_sum
        intro p hp
        simp only [T, Finset.mem_filter] at hp
        have hre' := hre p hp.2.1 (not_dvd_of_prime_of_eq_neg_one hp.2.1 hp.2.2) hp.2.2
        have : (1 : ℝ) ≤ ‖1 + b p‖ ^ 2 := by
          rw [Complex.sq_norm, Complex.normSq_apply]
          simp only [Complex.add_re, Complex.one_re, hre', Complex.add_im, Complex.one_im]
          nlinarith [sq_nonneg (b p).im]
        exact div_le_div_of_nonneg_right this (Real.rpow_nonneg (Nat.cast_nonneg _) _)
      have h2 : ∑ p ∈ T X, ‖1 + b p‖ ^ 2 / (p : ℝ) ^ (1 + s) ≤ ∑ p ∈ F, ‖1 + b p‖ ^ 2 / (p : ℝ) ^ (1 + s) :=
        Finset.sum_le_sum_of_subset_of_nonneg hsub (fun p _ _ => div_nonneg (sq_nonneg _) (Real.rpow_nonneg (Nat.cast_nonneg _) _))
      have h3 := Real.add_one_le_exp (∑ p ∈ F, ‖1 + b p‖ ^ 2 / (p : ℝ) ^ (1 + s))
      have hL2 : ‖Λ ((1 + s : ℝ) : ℂ)‖ ^ 2 ≤ (c * s) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hΛ 2
      have hsS := hsC s hs hs1
      have h4 : 2 * (1 + 1 / s) * ‖Λ ((1 + s : ℝ) : ℂ)‖ ^ 2 * S ≤ B := by
        calc 2 * (1 + 1 / s) * ‖Λ ((1 + s : ℝ) : ℂ)‖ ^ 2 * S
            ≤ 2 * (1 + 1 / s) * (c * s) ^ 2 * S := by gcongr
          _ = 2 * (s + 1) * c ^ 2 * (s * S) := by field_simp
          _ ≤ 2 * (1 + 1) * c ^ 2 * C := by gcongr
          _ = B := by rw [hB]; ring
      linarith

    have hT : ∀ X : ℕ, ∑ p ∈ T X, (1 : ℝ) / (p : ℝ) ≤ B := by
      intro X
      have ht : Tendsto (fun s : ℝ => ∑ p ∈ T X, (1 : ℝ) / (p : ℝ) ^ (1 + s)) (𝓝[>] (0 : ℝ))
          (𝓝 (∑ p ∈ T X, (1 : ℝ) / (p : ℝ) ^ (1 + (0:ℝ)))) := by
        apply Tendsto.mono_left _ nhdsWithin_le_nhds
        apply tendsto_finsetSum
        intro p hp
        simp only [T, Finset.mem_filter] at hp
        have hp0 : (0 : ℝ) < p := by exact_mod_cast hp.2.1.pos
        apply Continuous.tendsto
        exact continuous_const.div (continuous_const.rpow (continuous_const.add continuous_id) (fun _ => Or.inl hp0.ne'))
          (fun _ => (Real.rpow_pos_of_pos hp0 _).ne')
      simp only [add_zero, Real.rpow_one] at ht
      apply le_of_tendsto ht
      filter_upwards [hev] with s hs
      exact key X s hs.1 hs.2.1 hs.2.2
    apply _root_.GlobalTheory.not_summable_one_div_primes_eq_neg_one M hM
    apply summable_of_sum_range_le (c := B)
    · intro n; split_ifs <;> positivity
    · intro X
      rw [← Finset.sum_filter]
      exact hT X

end GlobalTheory.EisM
end

