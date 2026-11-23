module

public import Mathlib
public import Formalism.SharpRestriction.CuspSpanNormBounds.FractionFieldToGenericStalkAlgebraMapEq
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0007
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.ComplementReferenceCompactSubgroup
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0026
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0002

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.NormAdditiveCharacterTypePrimeEqOne
section
open ValuativeRel Formalism.MainNotions.S.Loc GlobalTheory.HL MeasureTheory
open scoped Pointwise ENNReal Classical

namespace GlobalTheory.FramePsi

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E]

def pairL (L : LocE F E) {n : ℕ} (Hm : Matrix (Fin n) (Fin n) E) (y : Fin n → E) :
    (Fin n → E) →ₗ[E] E where
  toFun x := hf L Hm x y
  map_add' a b := by simp [hf, add_mul, Finset.sum_add_distrib]
  map_smul' c a := by simp [hf, Finset.mul_sum, mul_assoc]

theorem hf_span_right (L : LocE F E) {n : ℕ} (Hm : Matrix (Fin n) (Fin n) E) (x : Fin n → E)
    (s : Set (Fin n → E)) (hs : ∀ y ∈ s, hf L Hm x y = 0) :
    ∀ y ∈ Submodule.span E s, hf L Hm x y = 0 := by
  intro y hy
  induction hy using Submodule.span_induction with
  | mem y h => exact hs y h
  | zero => simp [hf]
  | add a b _ _ ha hb =>
    have : hf L Hm x (a + b) = hf L Hm x a + hf L Hm x b := by
      simp [hf, mul_add, Finset.sum_add_distrib]
    rw [this, ha, hb, add_zero]
  | smul c a _ ha =>
    have : hf L Hm x (c • a) = L.cj c * hf L Hm x a := by
      simp only [hf, Finset.mul_sum, Pi.smul_apply, smul_eq_mul, map_mul]
      refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring
    rw [this, ha, mul_zero]

theorem coef_mul {L : LocE F E} {r k : ℕ} (S : Frames L r k) (g : Fin (r + 1) → S.V)
    (gs : Fin r → S.V) (t : E)
    (hg : ∀ a b, hf L S.Hm (g a) (g b) = if a = Fin.last r ∧ b = Fin.last r then t else 0)
    (hd : ∀ a j, hf L S.Hm (g a) (gs j) = if a = j.castSucc then 1 else 0)
    (a : S.GLV) (ha : a ∈ S.Nof g) (b : S.GLV) (hb : b ∈ S.Nof g) (j : Fin r) :
    S.coef g gs (a * b) j = S.coef g gs a j + S.coef g gs b j := by
  simp only [Frames.Nof, Subgroup.mem_inf, Subgroup.mem_iInf] at ha hb
  obtain ⟨⟨-, ha1⟩, -⟩ := ha
  obtain ⟨⟨-, hb1⟩, hb2⟩ := hb
  have hA : b (g j.succ) - g j.succ ∈ S.spanTo g (j + 1) := by
    by_cases hj : (j : ℕ) + 1 < r
    · refine (hb1 ⟨j + 1, hj⟩).2 _ (Submodule.subset_span ⟨j.succ, ?_, rfl⟩)
      simp
    · have hr : (j : ℕ) + 1 = r := by have := j.2; omega
      rw [hr]
      refine hb2.2 _ ?_
      refine hf_span_right L S.Hm _ _ ?_
      rintro _ ⟨i, hi, rfl⟩
      rw [hg, if_neg]
      rintro ⟨-, rfl⟩
      simp at hi
  have hB := (ha1 j).2 _ hA
  have hK : S.spanTo g j ≤ LinearMap.ker (pairL L S.Hm (gs j)) := by
    refine Submodule.span_le.2 ?_
    rintro _ ⟨i, hi, rfl⟩
    change hf L S.Hm (g i) (gs j) = 0
    rw [hd, if_neg]
    rintro rfl
    simp at hi
  have h0 : pairL L S.Hm (gs j) (g j.succ) = 0 := by
    change hf L S.Hm (g j.succ) (gs j) = 0
    rw [hd, if_neg]
    intro h
    have := congrArg Fin.val h
    simp at this
  have h1 := LinearMap.mem_ker.1 (hK hB)
  change pairL L S.Hm (gs j) (a (b (g j.succ))) =
    pairL L S.Hm (gs j) (a (g j.succ)) + pairL L S.Hm (gs j) (b (g j.succ))
  simp only [map_sub] at h1
  linear_combination h1 - h0

theorem exists_nsmul_mem [IsNonarchimedeanLocalField F] (L : LocE F E) (y : E) :
    ∃ n : ℕ, n ≠ 0 ∧ (n : E) * y ∈ L.O := by
  haveI : Module.Finite F E := Module.finite_of_finrank_pos (by rw [L.rank]; norm_num)
  have hyF : IsAlgebraic F y := Algebra.IsAlgebraic.isAlgebraic y
  have hy : IsAlgebraic 𝒪[F] y := (IsFractionRing.isAlgebraic_iff 𝒪[F] F E).2 hyF
  obtain ⟨c, hc, hcy⟩ := hy.exists_integral_multiple
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible 𝒪[F]
  obtain ⟨m, u, hu⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hc hϖ
  have hp : ((Nat.card 𝓀[F] : ℕ) : 𝒪[F]) ∈ IsLocalRing.maximalIdeal 𝒪[F] := by
    rw [← IsLocalRing.residue_eq_zero_iff, map_natCast]
    have := Fintype.ofFinite 𝓀[F]
    rw [Nat.card_eq_fintype_card]
    exact FiniteField.cast_card_eq_zero _
  rw [hϖ.maximalIdeal_eq, Ideal.mem_span_singleton] at hp
  have hdv : c ∣ ((Nat.card 𝓀[F] ^ m : ℕ) : 𝒪[F]) := by
    rw [hu, Nat.cast_pow, Units.mul_left_dvd]
    exact pow_dvd_pow_of_dvd hp m
  obtain ⟨d, hd⟩ := hdv
  refine ⟨Nat.card 𝓀[F] ^ m, pow_ne_zero _ Nat.card_pos.ne', (L.O_def _).2 ?_⟩
  have : ((Nat.card 𝓀[F] ^ m : ℕ) : E) * y = d • (c • y) := by
    rw [smul_smul, mul_comm d c, ← hd, Nat.cast_smul_eq_nsmul, nsmul_eq_mul]
  rw [this]
  exact hcy.smul d

theorem norm_additiveCharacter_typePrime_eq_one [IsNonarchimedeanLocalField F] (L : LocE F E) (y : E) : ‖L.psi0 y‖ = 1 := by
  obtain ⟨n, hn, hy⟩ := exists_nsmul_mem L y
  have h1 : L.psi0 ((n : E) * y) = 1 := by
    simpa using (L.additive_character_dual_ring _).2 hy 1 L.O.one_mem
  rw [← nsmul_eq_mul, AddChar.map_nsmul_eq_pow] at h1
  have h2 := congrArg norm h1
  rw [norm_pow, norm_one] at h2
  exact (pow_eq_one_iff_of_nonneg (norm_nonneg _) hn).1 h2

theorem psi_unitary_character : ∀ {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [CharZero F] {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] (L : LocE F E), ∀ (r k : ℕ) (S : Frames L r k), (∀ a ∈ S.N, ∀ b ∈ S.N, S.psi (a * b) = S.psi a * S.psi b) ∧ (∀ a ∈ S.N', ∀ b ∈ S.N', S.psi' (a * b) = S.psi' a * S.psi' b) ∧ (∀ a, ‖S.psi a‖ = 1 ∧ ‖S.psi' a‖ = 1) ∧ ∀ y : E, ‖L.psi0 y‖ = 1 := by
  intro F _ _ _ _ _ E _ _ _ L r k S
  refine ⟨fun a ha b hb => ?_, fun a ha b hb => ?_,
    fun a => ⟨norm_additiveCharacter_typePrime_eq_one L _, norm_additiveCharacter_typePrime_eq_one L _⟩, norm_additiveCharacter_typePrime_eq_one L⟩
  · simp only [Frames.psi, Frames.psiOf]
    rw [← AddChar.map_add_eq_mul, ← mul_add, ← Finset.sum_add_distrib]
    simp only [coef_mul S S.f S.es _ S.gram S.dual a ha b hb]
  · simp only [Frames.psi', Frames.psiOf]
    rw [← AddChar.map_add_eq_mul, ← mul_add, ← Finset.sum_add_distrib]
    simp only [coef_mul S S.f' S.es' _ S.gram' S.dual' a ha b hb]

end GlobalTheory.FramePsi
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.NormOrbitSumLeOfSymmKernel
section
open ValuativeRel Formalism.MainNotions.S.Loc GlobalTheory.HL MeasureTheory
open scoped Pointwise ENNReal Classical

namespace GlobalTheory.HL

theorem sum_eq_sum_of_symm_rel {ι : Type*} (Z : Finset ι) (r : ι → ι → Prop)
    (hr : ∀ p q, r p q → r q p) (hne : ∀ p ∈ Z, ∃ q ∈ Z, r p q) (F H : ι → ℂ)
    (hFH : ∀ p ∈ Z, ∀ q ∈ Z, r p q →
      F p * ((Z.filter (r q)).card : ℂ) = H q * ((Z.filter (r p)).card : ℂ)) :
    ∑ p ∈ Z, F p = ∑ p ∈ Z, H p := by
  have hd : ∀ p ∈ Z, ((Z.filter (r p)).card : ℂ) ≠ 0 := by
    intro p hp
    obtain ⟨q, hq, hpq⟩ := hne p hp
    exact_mod_cast (Finset.card_pos.2 ⟨q, Finset.mem_filter.2 ⟨hq, hpq⟩⟩).ne'
  have key : ∀ F : ι → ℂ, ∑ p ∈ Z, F p =
      ∑ p ∈ Z, ∑ q ∈ Z, if r p q then F p / ((Z.filter (r p)).card : ℂ) else 0 := by
    intro F
    refine Finset.sum_congr rfl fun p hp => ?_
    rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul, mul_div_cancel₀ _ (hd p hp)]
  rw [key F, key H, Finset.sum_comm]
  refine Finset.sum_congr rfl fun q hq => Finset.sum_congr rfl fun p hp => ?_
  by_cases h : r p q
  · rw [if_pos h, if_pos (hr _ _ h), div_eq_div_iff (hd p hp) (hd q hq), hFH p hp q hq h]
  · rw [if_neg h, if_neg (fun h' => h (hr _ _ h'))]

section
variable {G X : Type} [Group G] [MulAction G X] (St : Subgroup G)

theorem ncard_stabilizer_orbit (y w : X) :
    {w' | ∃ h ∈ St, h • y = y ∧ h • w = w'}.ncard =
      (St ⊓ MulAction.stabilizer G w).relIndex (St ⊓ MulAction.stabilizer G y) := by
  have h1 : {w' | ∃ h ∈ St, h • y = y ∧ h • w = w'} =
      MulAction.orbit (St ⊓ MulAction.stabilizer G y : Subgroup G) w := by
    ext w'
    constructor
    · rintro ⟨h, h1, h2, h3⟩
      exact ⟨⟨h, h1, h2⟩, h3⟩
    · rintro ⟨⟨h, h1, h2⟩, h3⟩
      exact ⟨h, h1, h2, h3⟩
  rw [h1, ← MulAction.index_stabilizer, Subgroup.relIndex]
  congr 1
  ext ⟨h, h1, h2⟩
  simp only [MulAction.mem_stabilizer_iff, Subgroup.mem_subgroupOf, Subgroup.mem_inf]
  exact ⟨fun h3 => ⟨h1, h3⟩, fun h3 => h3.2⟩

theorem relIndex_stabilizer_smul {g : G} (hg : g ∈ St) (y w : X) :
    (St ⊓ MulAction.stabilizer G (g • w)).relIndex (St ⊓ MulAction.stabilizer G (g • y)) =
      (St ⊓ MulAction.stabilizer G w).relIndex (St ⊓ MulAction.stabilizer G y) := by
  rw [← ncard_stabilizer_orbit, ← ncard_stabilizer_orbit,
    ← Set.ncard_image_of_injective {w' | ∃ h ∈ St, h • y = y ∧ h • w = w'} (MulAction.injective g)]
  congr 1
  ext w'
  simp only [Set.mem_ofPred_eq, Set.mem_image]
  constructor
  · rintro ⟨h, hh, h1, h2⟩
    refine ⟨_, ⟨g⁻¹ * h * g, St.mul_mem (St.mul_mem (St.inv_mem hg) hh) hg, ?_, rfl⟩, ?_⟩
    · rw [mul_smul, mul_smul, h1, inv_smul_smul]
    · rw [mul_smul, mul_smul, h2, smul_inv_smul]
  · rintro ⟨_, ⟨h, hh, h1, rfl⟩, rfl⟩
    refine ⟨g * h * g⁻¹, St.mul_mem (St.mul_mem hg hh) (St.inv_mem hg), ?_, ?_⟩
    · rw [mul_smul, mul_smul, inv_smul_smul, h1]
    · rw [mul_smul, mul_smul, inv_smul_smul]

theorem invVol_mul_relIndex_comm {G : Type} [Group G] (K0 A B : Subgroup G)
    (hA : K0.relIndex A ≠ 0) (hA' : A.relIndex K0 ≠ 0)
    (hB : K0.relIndex B ≠ 0) (hB' : B.relIndex K0 ≠ 0) :
    invVol K0 A * (B.relIndex A : ℝ) = invVol K0 B * (A.relIndex B : ℝ) := by
  have h1 : K0.relIndex (A ⊓ B) ≠ 0 := fun h =>
    hA (Subgroup.relIndex_eq_zero_of_le_right inf_le_left h)
  have h2 : (A ⊓ B).relIndex K0 ≠ 0 := Subgroup.relIndex_inf_ne_zero hA' hB'
  have e1 := (invVol_mul_pos_le_conj K0 A (A ⊓ B) hA hA' h1 h2).2.2.1 inf_le_left
  have e2 := (invVol_mul_pos_le_conj K0 B (A ⊓ B) hB hB' h1 h2).2.2.1 inf_le_right
  rw [Subgroup.inf_relIndex_left] at e1
  rw [Subgroup.inf_relIndex_right] at e2
  rw [← e1, ← e2]

end

theorem norm_orbit_sum_le_of_symm_kernel : ∀ {G X : Type} [Group G] [MulAction G X] (St K0 : Subgroup G) (P : X → Prop) (om : X → ℂ) (m : X → X → ℝ) (e : ℝ), K0 ≤ St → (∀ h ∈ St, ∀ x, P x → P (h • x) ∧ om (h • x) = om x ∧ invVol K0 (St ⊓ MulAction.stabilizer G (h • x)) = invVol K0 (St ⊓ MulAction.stabilizer G x) ∧ ∀ y, P y → m (h • x) (h • y) = m x y) → (∀ x, P x → K0.relIndex (St ⊓ MulAction.stabilizer G x) ≠ 0 ∧ (St ⊓ MulAction.stabilizer G x).relIndex K0 ≠ 0 ∧ ‖om x‖ = 1 ∧ {y | P y ∧ m x y ≠ 0}.Finite ∧ (∀ y, P y → 0 ≤ m x y ∧ m x y = m y x) ∧ |(∑ᶠ y : {y // P y}, m x y) - 1| ≤ e ∧ ‖∑ᶠ y : {y // P y}, (m x y : ℂ) * om y‖ ≤ e) → {o : MulAction.orbitRel.Quotient St X | P o.out}.Finite → ‖∑' o : MulAction.orbitRel.Quotient St X, if P o.out then ((invVol K0 (St ⊓ MulAction.stabilizer G o.out) : ℝ) : ℂ) * om o.out else 0‖ ≤ 2 * e * ∑' o : MulAction.orbitRel.Quotient St X, if P o.out then invVol K0 (St ⊓ MulAction.stabilizer G o.out) else 0 := by
  intro G X _ _ St K0 P om m e _ hinv hP hfin
  set mu : X → ℝ := fun x => invVol K0 (St ⊓ MulAction.stabilizer G x) with hmu
  have hN : ∀ x, ∃ s : Finset X, P x → ∀ y, y ∈ s ↔ P y ∧ m x y ≠ 0 := by
    intro x
    by_cases hx : P x
    · exact ⟨(hP x hx).2.2.2.1.toFinset, fun _ y => by simp⟩
    · exact ⟨∅, fun h => absurd h hx⟩
  choose N hN using hN
  have hO : ∀ o, o ∈ hfin.toFinset ↔ P o.out := fun o => by simp
  generalize hfin.toFinset = O at hO
  have hR : ∀ x, P x → |(∑ y ∈ N x, m x y) - 1| ≤ e := by
    intro x hx
    have := (hP x hx).2.2.2.2.2.1
    rwa [finsum_subtype_eq_finsum_cond (f := fun y => m x y),
      finsum_cond_eq_sum_of_cond_iff (f := fun y => m x y) (t := N x)] at this
    intro y hy
    rw [hN x hx]
    exact ⟨fun h => ⟨h, hy⟩, fun h => h.1⟩
  have hS : ∀ x, P x → ‖∑ y ∈ N x, (m x y : ℂ) * om y‖ ≤ e := by
    intro x hx
    have := (hP x hx).2.2.2.2.2.2
    rwa [finsum_subtype_eq_finsum_cond (f := fun y => (m x y : ℂ) * om y),
      finsum_cond_eq_sum_of_cond_iff (f := fun y => (m x y : ℂ) * om y) (t := N x)] at this
    intro y hy
    rw [hN x hx]
    refine ⟨fun h => ⟨h, fun h0 => hy ?_⟩, fun h => h.1⟩
    simp [h0]
  have hpos : ∀ x, P x → 0 < mu x := fun x hx =>
    (invVol_mul_pos_le_conj K0 _ _ (hP x hx).1 (hP x hx).2.1 (hP x hx).1 (hP x hx).2.1).2.1
  have t1 : (∑' o : MulAction.orbitRel.Quotient St X,
      if P o.out then ((mu o.out : ℝ) : ℂ) * om o.out else 0) =
      ∑ o ∈ O, ((mu o.out : ℝ) : ℂ) * om o.out := by
    rw [tsum_eq_sum (s := O) (fun o ho => if_neg (fun h => ho ((hO o).2 h)))]
    exact Finset.sum_congr rfl fun o ho => if_pos ((hO o).1 ho)
  have t2 : (∑' o : MulAction.orbitRel.Quotient St X, if P o.out then mu o.out else 0) =
      ∑ o ∈ O, mu o.out := by
    rw [tsum_eq_sum (s := O) (fun o ho => if_neg (fun h => ho ((hO o).2 h)))]
    exact Finset.sum_congr rfl fun o ho => if_pos ((hO o).1 ho)
  refine (congrArg norm t1).trans_le (le_of_le_of_eq ?_ (congrArg (2 * e * ·) t2.symm))
  have huniq : ∀ (o o' : MulAction.orbitRel.Quotient St X) (g : G), g ∈ St →
      g • o.out = o'.out → o = o' := by
    intro o o' g hg h
    rw [← Quotient.out_eq o, ← Quotient.out_eq o']
    exact (Quotient.sound (show MulAction.orbitRel St X o'.out o.out from ⟨⟨g, hg⟩, h⟩)).symm
  have hrep : ∀ z : X, ∃ o : MulAction.orbitRel.Quotient St X, ∃ g ∈ St, g • z = o.out := by
    intro z
    obtain ⟨⟨g, hg⟩, h⟩ : MulAction.orbitRel St X (Quotient.mk _ z).out z := Quotient.mk_out z
    exact ⟨_, g, hg, h⟩
  have unf : ∑ o ∈ O, ∑ z ∈ N o.out, ((mu o.out : ℝ) : ℂ) * ((m o.out z : ℂ) * om z) =
      ∑ o ∈ O, ∑ z ∈ N o.out, ((mu o.out : ℝ) : ℂ) * ((m o.out z : ℂ) * om o.out) := by
    rw [Finset.sum_sigma', Finset.sum_sigma']
    set Z := O.sigma fun o => N o.out with hZ
    have mZ : ∀ p, p ∈ Z ↔ P p.1.out ∧ P p.2 ∧ m p.1.out p.2 ≠ 0 := by
      intro p
      rw [hZ, Finset.mem_sigma, hO]
      exact and_congr_right fun h => hN _ h _
    let r : (Σ _ : MulAction.orbitRel.Quotient St X, X) →
        (Σ _ : MulAction.orbitRel.Quotient St X, X) → Prop :=
      fun p q => ∃ g ∈ St, g • p.2 = q.1.out ∧ g • p.1.out = q.2
    have hr : ∀ p q, r p q → r q p := by
      rintro p q ⟨g, hg, h1, h2⟩
      exact ⟨g⁻¹, St.inv_mem hg, by rw [← h2, inv_smul_smul], by rw [← h1, inv_smul_smul]⟩
    have hm : ∀ p ∈ Z, ∀ q, r p q → m q.1.out q.2 = m p.1.out p.2 := by
      rintro p hp q ⟨g, hg, h1, h2⟩
      obtain ⟨a, b, -⟩ := (mZ p).1 hp
      rw [← h1, ← h2, (hinv g hg _ b).2.2.2 _ a, ((hP _ b).2.2.2.2.1 _ a).2]
    have hmem : ∀ p ∈ Z, ∀ q, r p q → q ∈ Z := by
      intro p hp q hpq
      have := hm p hp q hpq
      obtain ⟨g, hg, h1, h2⟩ := hpq
      obtain ⟨a, b, c⟩ := (mZ p).1 hp
      rw [mZ, this, ← h1, ← h2]
      exact ⟨(hinv g hg _ b).1, (hinv g hg _ a).1, c⟩
    have hdeg : ∀ p ∈ Z, ∀ q, r p q → (Z.filter (r p)).card =
        (St ⊓ MulAction.stabilizer G q.2).relIndex (St ⊓ MulAction.stabilizer G q.1.out) := by
      rintro p hp ⟨o, w⟩ ⟨g, hg, h1, h2⟩
      dsimp only at h1 h2 ⊢
      rw [← ncard_stabilizer_orbit, ← Set.ncard_coe_finset,
        ← Set.ncard_image_of_injective _ (sigma_mk_injective (β := fun _ => X) (i := o))]
      congr 1
      ext ⟨o', w'⟩
      simp only [Finset.coe_filter, Set.mem_ofPred_eq, Set.mem_image]
      constructor
      · rintro ⟨-, g', hg', h1', h2'⟩
        dsimp only at h1' h2'
        have e1 : (g' * g⁻¹) • o.out = o'.out := by
          rw [← h1, mul_smul, inv_smul_smul, h1']
        have hgg := St.mul_mem hg' (St.inv_mem hg)
        obtain rfl := huniq _ _ _ hgg e1
        refine ⟨w', ⟨_, hgg, e1, ?_⟩, rfl⟩
        rw [← h2, mul_smul, inv_smul_smul, h2']
      · rintro ⟨w'', ⟨h, hh, e1, e2⟩, e3⟩
        rw [← e3]
        have : r p ⟨o, w''⟩ :=
          ⟨h * g, St.mul_mem hh hg, by rw [mul_smul, h1, e1], by rw [mul_smul, h2, e2]⟩
        exact ⟨hmem p hp _ this, this⟩
    refine sum_eq_sum_of_symm_rel Z r hr ?_ _ _ ?_
    · intro p hp
      obtain ⟨o, g, hg, h⟩ := hrep p.2
      have : r p ⟨o, g • p.1.out⟩ := ⟨g, hg, h, rfl⟩
      exact ⟨_, hmem p hp _ this, this⟩
    · intro p hp q hq hpq
      rw [hdeg p hp q hpq, hdeg q hq p (hr _ _ hpq), hm p hp q hpq]
      obtain ⟨g, hg, h1, h2⟩ := hpq
      obtain ⟨a, b, c⟩ := (mZ p).1 hp
      have e1 := invVol_mul_relIndex_comm K0 _ _ (hP _ a).1 (hP _ a).2.1 (hP _ b).1 (hP _ b).2.1
      have e2 := congrArg (fun t : ℝ => (t : ℂ)) e1
      rw [← h1, ← h2, relIndex_stabilizer_smul St hg, (hinv g hg _ b).2.1]
      simp only [hmu]
      rw [(hinv g hg _ b).2.2.1]
      push_cast at e2
      linear_combination (m p.1.out p.2 : ℂ) * om p.2 * e2
  have dec : ∑ o ∈ O, ((mu o.out : ℝ) : ℂ) * om o.out =
      ∑ o ∈ O, ((mu o.out : ℝ) : ℂ) * (∑ z ∈ N o.out, (m o.out z : ℂ) * om z) -
      ∑ o ∈ O, ((mu o.out : ℝ) : ℂ) * om o.out * (((∑ z ∈ N o.out, m o.out z) - 1 : ℝ) : ℂ) := by
    simp only [Finset.mul_sum]
    rw [unf, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun o _ => ?_
    rw [← Finset.mul_sum, ← Finset.sum_mul]
    push_cast
    ring
  rw [dec]
  refine (norm_sub_le _ _).trans ?_
  have b1 : ‖∑ o ∈ O, ((mu o.out : ℝ) : ℂ) * (∑ z ∈ N o.out, (m o.out z : ℂ) * om z)‖ ≤
      ∑ o ∈ O, e * mu o.out := by
    refine norm_sum_le_of_le _ fun o ho => ?_
    have h := (hO o).1 ho
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (hpos _ h), mul_comm]
    exact mul_le_mul_of_nonneg_right (hS _ h) (hpos _ h).le
  have b2 : ‖∑ o ∈ O, ((mu o.out : ℝ) : ℂ) * om o.out *
      (((∑ z ∈ N o.out, m o.out z) - 1 : ℝ) : ℂ)‖ ≤ ∑ o ∈ O, e * mu o.out := by
    refine norm_sum_le_of_le _ fun o ho => ?_
    have h := (hO o).1 ho
    rw [norm_mul, norm_mul, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs,
      Real.norm_eq_abs, abs_of_pos (hpos _ h), (hP _ h).2.2.1, mul_one, mul_comm]
    exact mul_le_mul_of_nonneg_right (hR _ h) (hpos _ h).le
  rw [← Finset.mul_sum] at b1 b2
  linarith

end GlobalTheory.HL
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.PowEqZeroOfMemHermitianFrameUnipotent
section
noncomputable section
open ValuativeRel Formalism.MainNotions.S.Loc GlobalTheory.HL MeasureTheory
open scoped Pointwise ENNReal Classical

namespace GlobalTheory.FlagUnipotent

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E]

theorem hf_sub_left (L : LocE F E) {n : ℕ} (H : Matrix (Fin n) (Fin n) E) (a b y : Fin n → E) :
    hf L H (a - b) y = hf L H a y - hf L H b y := by
  simp [hf, sub_mul, Finset.sum_sub_distrib]

theorem hf_sub_right (L : LocE F E) {n : ℕ} (H : Matrix (Fin n) (Fin n) E) (x a b : Fin n → E) :
    hf L H x (a - b) = hf L H x a - hf L H x b := by
  simp [hf, mul_sub, Finset.sum_sub_distrib]

theorem pow_eq_zero_of_mem_Nof {L : LocE F E} {r k : ℕ} (S : Frames L r k)
    (f : Fin (r + 1) → S.V) (g : S.GLV) (hg : g ∈ S.Nof f) :
    ((g : S.V →ₗ[E] S.V) - 1) ^ (2 * r + 1) = 0 := by
  obtain ⟨⟨hiso, hfl⟩, hmid⟩ := hg
  have hfl' : ∀ j, j < r → g ∈ unipOn (S.spanTo f (j + 1)) (S.spanTo f j) := fun j hj =>
    (Subgroup.mem_iInf.1 hfl) ⟨j, hj⟩
  set A : S.V →ₗ[E] S.V := (g : S.V →ₗ[E] S.V) - 1 with hA
  have hAv : ∀ v, A v = g v - v := fun v => rfl
  have h0 : S.spanTo f 0 = ⊥ := by simp [Frames.spanTo]
  have ha : ∀ j, j ≤ r → ∀ v, (A ^ j) v ∈ perp L S.Hm (S.spanTo f j) := by
    intro j
    induction j with
    | zero =>
      intro _ v y hy
      rw [h0, Submodule.mem_bot] at hy
      simp [hy, hf]
    | succ j ih =>
      intro hj v x hx
      obtain ⟨h1, h2⟩ := hfl' j hj
      have hw := ih (by omega) v
      rw [pow_succ', Module.End.mul_apply, hAv]
      generalize (A ^ j) v = w at hw
      obtain ⟨y, rfl⟩ := g.surjective x
      have h3 : hf L S.Hm w (g y - y) = 0 := hw _ (h2 y ((h1 y).1 hx))
      have h4 : hf L S.Hm (g w) (g y) = hf L S.Hm w y := hiso w y
      rw [hf_sub_right] at h3
      rw [hf_sub_left, h4]
      linear_combination -h3
  have hc : ∀ j, j ≤ r → ∀ v ∈ S.spanTo f j, (A ^ j) v = 0 := by
    intro j
    induction j with
    | zero =>
      intro _ v hv
      rw [h0, Submodule.mem_bot] at hv
      simp [hv]
    | succ j ih =>
      intro hj v hv
      rw [pow_succ, Module.End.mul_apply, hAv]
      exact ih (by omega) _ ((hfl' j hj).2 v hv)
  refine LinearMap.ext fun v => ?_
  have e : 2 * r + 1 = r + (1 + r) := by omega
  rw [e, pow_add, pow_add, pow_one, Module.End.mul_apply, Module.End.mul_apply, hAv]
  exact hc r le_rfl _ (hmid.2 _ (ha r le_rfl v))

theorem main : ∀ {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [CharZero F] {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] (L : LocE F E), ∀ (r k : ℕ) (S : Frames L r k), ∀ g ∈ S.N, ((g : S.V →ₗ[E] S.V) - 1) ^ (2 * r + 1) = 0 :=
  fun _ _ _ S g hg => pow_eq_zero_of_mem_Nof S S.f g hg

end GlobalTheory.FlagUnipotent
end
end

