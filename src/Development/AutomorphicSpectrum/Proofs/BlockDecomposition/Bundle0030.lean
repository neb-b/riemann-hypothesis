module

public import Mathlib
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.AcrisKummerUnits.Splits
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.WittExactSequences.Bundle0001
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0004
public import GroundTheory.AutomorphicForms.Bundle0004
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0007
public import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.IntegralConjInnerMulInnerOfIsEmptyEquiv

@[expose] public section

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.DividedPowerStructureExists
section
open CategoryTheory AlgebraicGeometry CrystallineSemistableComparison CrystallineSemistableComparison.R

namespace GlobalTheory.CompanionTheory.PdTF

theorem natCast_mul_cancel {S : Type} [CommRing S] (hS : TF (S := S)) {n : ℕ} (hn : n ≠ 0) {a b : S}
    (e : (n : S) * a = (n : S) * b) : a = b := by
  have h0 : (n : S) * (a - b) = 0 := by rw [mul_sub, e, sub_self]
  have := (mem_nonZeroDivisors_iff.mp (hS n hn)).1 _ h0
  exact sub_eq_zero.mp this

theorem exists_dividedPowers {S : Type} [CommRing S] (hS : TF (S := S)) (I : Ideal S) (hI : PdI I) :
    ∃ δ : DividedPowers I, IsPd (RingHom.id S) I δ := by
  classical
  have ex : ∀ (k : ℕ) (x : S), ∃ y : S,
      (x ∈ I → (k.factorial : S) * y = x ^ k ∧ (k ≠ 0 → y ∈ I)) ∧ (x ∉ I → y = 0) := by
    intro k x
    by_cases hx : x ∈ I
    · by_cases hk : k = 0
      · subst hk
        exact ⟨1, fun _ => ⟨by simp, fun h => absurd rfl h⟩, fun h => absurd hx h⟩
      · obtain ⟨y, hy, e⟩ := hI x hx k hk
        exact ⟨y, fun _ => ⟨e, fun _ => hy⟩, fun h => absurd hx h⟩
    · exact ⟨0, fun h => absurd h hx, fun _ => rfl⟩
  choose d hd using ex
  have spec : ∀ (k : ℕ) {x : S}, x ∈ I → (k.factorial : S) * d k x = x ^ k :=
    fun k x hx => ((hd k x).1 hx).1
  have hmem : ∀ {k : ℕ} {x : S}, k ≠ 0 → x ∈ I → d k x ∈ I :=
    fun {k x} hk hx => ((hd k x).1 hx).2 hk
  have fne : ∀ k : ℕ, k.factorial ≠ 0 := Nat.factorial_ne_zero
  refine ⟨{ dpow := d
            dpow_null := fun {n x} hx => (hd n x).2 hx
            dpow_zero := fun {x} hx => ?_
            dpow_one := fun {x} hx => ?_
            dpow_mem := fun {n x} hn hx => hmem hn hx
            dpow_add := fun {n x y} hx hy => ?_
            dpow_mul := fun {n a x} hx => ?_
            mul_dpow := fun {m n x} hx => ?_
            dpow_comp := fun {m n x} hn hx => ?_ }, (Ideal.map_id I).symm, ?_⟩
  · have := spec 0 hx
    simpa using this
  · have := spec 1 hx
    simpa using this
  · apply natCast_mul_cancel hS (fne n)
    rw [spec n (I.add_mem hx hy), (Commute.all x y).add_pow', Finset.mul_sum]
    refine Finset.sum_congr rfl fun p hp => ?_
    obtain ⟨i, j⟩ := p
    have hij : i + j = n := Finset.HasAntidiagonal.mem_antidiagonal.mp hp
    subst hij
    have hf : (((i + j).factorial : ℕ) : S)
        = ((i + j).choose i : S) * (i.factorial : S) * (j.factorial : S) := by
      rw [← Nat.add_choose_mul_factorial_mul_factorial, Nat.choose_symm_add]
      push_cast
      ring
    simp only
    rw [hf, nsmul_eq_mul, ← spec i hx, ← spec j hy]
    ring
  · apply natCast_mul_cancel hS (fne n)
    rw [spec n (I.mul_mem_left a hx), mul_pow, ← spec n hx]
    ring
  · apply natCast_mul_cancel hS (Nat.mul_ne_zero (fne m) (fne n))
    have hf : (((m + n).factorial : ℕ) : S)
        = ((m + n).choose m : S) * (m.factorial : S) * (n.factorial : S) := by
      rw [← Nat.add_choose_mul_factorial_mul_factorial, Nat.choose_symm_add]
      push_cast
      ring
    have h1 : ((m.factorial * n.factorial : ℕ) : S) * (d m x * d n x) = x ^ (m + n) := by
      push_cast
      rw [pow_add, ← spec m hx, ← spec n hx]
      ring
    have h2 : ((m.factorial * n.factorial : ℕ) : S) * (((m + n).choose m : S) * d (m + n) x)
        = x ^ (m + n) := by
      rw [← spec (m + n) hx, hf]
      push_cast
      ring
    rw [h1, h2]
  · by_cases hm : m = 0
    · subst hm
      have h0 := spec 0 (hmem hn hx)
      have h1 := spec 0 hx
      simp only [Nat.factorial_zero, Nat.cast_one, one_mul, pow_zero] at h0 h1
      simp [h0, h1, Nat.uniformBell_zero_left]
    · apply natCast_mul_cancel hS (Nat.mul_ne_zero (fne m) (pow_ne_zero m (fne n)))
      have hdx : d n x ∈ I := hmem hn hx
      have hb : ((Nat.uniformBell m n : ℕ) : S) * ((n.factorial : S) ^ m) * (m.factorial : S)
          = ((m * n).factorial : S) := by
        rw [← Nat.uniformBell_mul_eq _ hn]
        push_cast
        ring
      have h1 : ((m.factorial * n.factorial ^ m : ℕ) : S) * d m (d n x) = x ^ (m * n) := by
        push_cast
        calc (m.factorial : S) * (n.factorial : S) ^ m * d m (d n x)
            = (n.factorial : S) ^ m * ((m.factorial : S) * d m (d n x)) := by ring
          _ = ((n.factorial : S) * d n x) ^ m := by rw [spec m hdx, mul_pow]
          _ = x ^ (m * n) := by rw [spec n hx, ← pow_mul, mul_comm]
      have h2 : ((m.factorial * n.factorial ^ m : ℕ) : S)
          * (((Nat.uniformBell m n : ℕ) : S) * d (m * n) x) = x ^ (m * n) := by
        rw [← spec (m * n) hx, ← hb]
        push_cast
        ring
      rw [h1, h2]
  · intro k x y hx e
    apply natCast_mul_cancel hS (fne k)
    simp only [RingHom.id_apply]
    rw [spec k hx, e]

end GlobalTheory.CompanionTheory.PdTF
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.EqCOfToLaurentEqInvert
section
open TensorProduct CrystallineSemistableComparison.D
open scoped LaurentPolynomial

namespace GlobalTheory.CompanionTheory.LaurSplit

variable {K : Type} [CommRing K]

theorem coeff_nat (p : Polynomial K) (k : ℕ) :
    (Polynomial.toLaurent p).coeff (k : ℤ) = p.coeff k := by
  rw [LaurentPolynomial.coeff_toLaurent]
  exact Finsupp.mapDomain_apply_of_injective Nat.castEmbedding.injective _ k

theorem coeff_neg (p : Polynomial K) (k : ℤ) (hk : k < 0) :
    (Polynomial.toLaurent p).coeff k = 0 := by
  rw [LaurentPolynomial.coeff_toLaurent]
  apply Finsupp.mapDomain_notin_range
  rintro ⟨m, hm⟩
  have : (m : ℤ) = k := hm
  omega

theorem eq_C_of_toLaurent_eq_invert (a b : Polynomial K)
    (h : Polynomial.toLaurent a = LaurentPolynomial.invert (Polynomial.toLaurent b)) :
    a = Polynomial.C (a.coeff 0) ∧ b = Polynomial.C (a.coeff 0) := by
  have hc : ∀ n : ℤ, (Polynomial.toLaurent a).coeff n = (Polynomial.toLaurent b).coeff (-n) :=
    fun n => by rw [h, LaurentPolynomial.invert_apply]
  constructor
  · ext n
    rcases n with _ | n
    · simp
    · rw [Polynomial.coeff_C_succ, ← coeff_nat, hc]
      exact coeff_neg b _ (by omega)
  · ext n
    rcases n with _ | n
    · have h0 := hc ((0 : ℕ) : ℤ)
      rw [coeff_nat] at h0
      have h1 : (-(((0 : ℕ) : ℤ))) = ((0 : ℕ) : ℤ) := by simp
      rw [h1, coeff_nat] at h0
      simp [h0]
    · have h0 := hc (((n + 1 : ℕ) : ℤ) * (-1))
      have h1 : (-(((n + 1 : ℕ) : ℤ) * (-1))) = ((n + 1 : ℕ) : ℤ) := by ring
      rw [h1, coeff_nat, coeff_neg a _ (by omega)] at h0
      rw [Polynomial.coeff_C_succ, ← h0]

theorem exists_split (h : K[T;T⁻¹]) :
    ∃ h₁ h₂ : Polynomial K, h = Polynomial.toLaurent h₁ +
      LaurentPolynomial.T (-1) * LaurentPolynomial.invert (Polynomial.toLaurent h₂) := by
  induction h using LaurentPolynomial.induction_on' with
  | add p q hp hq =>
    obtain ⟨p₁, p₂, rfl⟩ := hp
    obtain ⟨q₁, q₂, rfl⟩ := hq
    refine ⟨p₁ + q₁, p₂ + q₂, ?_⟩
    simp only [map_add (f := _)]
    ring
  | C_mul_T n a =>
    rcases lt_or_ge n 0 with hn | hn
    · obtain ⟨m, rfl⟩ : ∃ m : ℕ, n = -1 + -(m : ℤ) := ⟨(-n - 1).toNat, by omega⟩
      refine ⟨0, Polynomial.C a * Polynomial.X ^ m, ?_⟩
      rw [Polynomial.toLaurent_C_mul_X_pow, map_mul, LaurentPolynomial.invert_C,
        LaurentPolynomial.invert_T, map_zero, zero_add, LaurentPolynomial.T_add]
      ring
    · obtain ⟨m, rfl⟩ : ∃ m : ℕ, n = (m : ℤ) := ⟨n.toNat, by omega⟩
      refine ⟨Polynomial.C a * Polynomial.X ^ m, 0, ?_⟩
      rw [Polynomial.toLaurent_C_mul_X_pow]
      simp

theorem exists_const_of_mem_span : ∀ (K : Type) [CommRing K] (f g : K) (α β : Polynomial K),
    Polynomial.toLaurent α - LaurentPolynomial.invert (Polynomial.toLaurent β) ∈
      Ideal.span {(LaurentPolynomial.C f - LaurentPolynomial.T 1 * LaurentPolynomial.C g : K[T;T⁻¹])} →
    ∃ c : K, α - Polynomial.C c ∈ Ideal.span {Polynomial.C f - Polynomial.X * Polynomial.C g} ∧
      β - Polynomial.C c ∈ Ideal.span {Polynomial.C g - Polynomial.X * Polynomial.C f} := by
  intro K _ f g α β hmem
  obtain ⟨h, hh⟩ := Ideal.mem_span_singleton'.1 hmem
  obtain ⟨h₁, h₂, rfl⟩ := exists_split h
  have hT : (LaurentPolynomial.T (-1) * LaurentPolynomial.T 1 : K[T;T⁻¹]) = 1 := by
    rw [← LaurentPolynomial.T_add]
    simp
  have key : Polynomial.toLaurent (α - (Polynomial.C f - Polynomial.X * Polynomial.C g) * h₁) =
      LaurentPolynomial.invert (Polynomial.toLaurent
        (β - (Polynomial.C g - Polynomial.X * Polynomial.C f) * h₂)) := by
    simp only [map_sub, map_mul, Polynomial.toLaurent_C, Polynomial.toLaurent_X,
      LaurentPolynomial.invert_C, LaurentPolynomial.invert_T]
    linear_combination (-1 : K[T;T⁻¹]) * hh -
      LaurentPolynomial.invert (Polynomial.toLaurent h₂) * LaurentPolynomial.C g * hT
  obtain ⟨ha, hb⟩ := eq_C_of_toLaurent_eq_invert _ _ key
  refine ⟨(α - (Polynomial.C f - Polynomial.X * Polynomial.C g) * h₁).coeff 0,
    Ideal.mem_span_singleton'.2 ⟨h₁, ?_⟩, Ideal.mem_span_singleton'.2 ⟨h₂, ?_⟩⟩
  · linear_combination (-1 : Polynomial K) * ha
  · linear_combination (-1 : Polynomial K) * hb

end GlobalTheory.CompanionTheory.LaurSplit
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.EventuallyHaarDetEqOneNearOne
section
open Matrix ValuativeRel MeasureTheory
open scoped Topology

namespace GlobalTheory.CompanionTheory.LocalModule

theorem distribHaarChar_det_eventually_eq_one :
    ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
      (n : ℕ), ∀ᶠ g in nhds (1 : GL (Fin n) k),
        MeasureTheory.distribHaarChar k (Matrix.GeneralLinearGroup.det g) = 1 := by
  intro k _ _ _ _ n
  have hc : Continuous fun g : GL (Fin n) k => ((Matrix.GeneralLinearGroup.det g : kˣ) : k) := by
    have : (fun g : GL (Fin n) k => ((Matrix.GeneralLinearGroup.det g : kˣ) : k)) =
        fun g : GL (Fin n) k => (g : Matrix (Fin n) (Fin n) k).det := rfl
    rw [this]
    exact Continuous.matrix_det Units.continuous_val
  have hO : IsOpen {x : k | valuation k (x - 1) < 1} := by
    have h : IsOpen {z : k | valuation k z < 1} := by simpa using (valuation k).isOpen_ball 1
    exact h.preimage (continuous_id.sub continuous_const)
  have hm : ∀ᶠ g in nhds (1 : GL (Fin n) k),
      ((Matrix.GeneralLinearGroup.det g : kˣ) : k) ∈ {x : k | valuation k (x - 1) < 1} := by
    refine hc.continuousAt.eventually (hO.mem_nhds ?_)
    simp
  filter_upwards [hm] with g hg
  refine distribHaarChar_eq_one_of_valuation_eq_one k _ ?_
  have hv : valuation k (((Matrix.GeneralLinearGroup.det g : kˣ) : k) - 1) < 1 := hg
  have h1 := Valuation.map_one_add_of_lt (valuation k) hv
  rwa [add_sub_cancel] at h1

end GlobalTheory.CompanionTheory.LocalModule
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsContinuousSectionQuotient
section
open Topology Filter Set

namespace GlobalTheory.CompanionTheory.LGroupSection

variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

def cosetImage (H K : Subgroup G) (d : G) : Set (G ⧸ H) :=
  {x | ∃ k ∈ K, ((d * k : G) : G ⧸ H) = x}

theorem isClopen_cosetImage (H K : Subgroup G) [IsClosed (H : Set G)]
    (hKo : IsOpen (K : Set G)) (hKc : IsCompact (K : Set G)) (d : G) :
    IsClopen (cosetImage H K d) := by
  have himg : cosetImage H K d =
      ((↑) : G → G ⧸ H) '' ((fun k : G => d * k) '' (K : Set G)) := by
    ext x
    constructor
    · rintro ⟨k, hk, rfl⟩
      exact ⟨d * k, ⟨k, hk, rfl⟩, rfl⟩
    · rintro ⟨_, ⟨k, hk, rfl⟩, rfl⟩
      exact ⟨k, hk, rfl⟩
  rw [himg]
  have hopen : IsOpen ((fun k : G => d * k) '' (K : Set G)) :=
    (Homeomorph.mulLeft d).isOpenMap _ hKo
  have hcomp : IsCompact ((fun k : G => d * k) '' (K : Set G)) :=
    hKc.image (continuous_const.mul continuous_id)
  have hcomp' : IsCompact (((↑) : G → G ⧸ H) '' ((fun k : G => d * k) '' (K : Set G))) :=
    hcomp.image continuous_quotient_mk'
  exact ⟨hcomp'.isClosed, QuotientGroup.isOpenMap_coe _ hopen⟩

theorem exists_isLocallyConstant_mem {X : Type*} [TopologicalSpace X] (V : ℕ → Set X)
    (hV : ∀ n, IsClopen (V n)) (hcov : ∀ x, ∃ n, x ∈ V n) :
    ∃ f : X → ℕ, IsLocallyConstant f ∧ ∀ x, x ∈ V (f x) := by
  classical
  refine ⟨fun x => Nat.find (hcov x), ?_, fun x => Nat.find_spec (hcov x)⟩
  rw [IsLocallyConstant.iff_exists_open]
  intro x
  refine ⟨V (Nat.find (hcov x)) ∩ ⋂ j ∈ Finset.range (Nat.find (hcov x)), (V j)ᶜ,
    (hV _).isOpen.inter (isOpen_biInter_finset fun j _ => (hV j).compl.isOpen), ?_, ?_⟩
  · refine ⟨Nat.find_spec (hcov x), ?_⟩
    simp only [mem_iInter, Finset.mem_range]
    exact fun j hj => Nat.find_min (hcov x) hj
  · rintro y ⟨hy1, hy2⟩
    simp only [mem_iInter, Finset.mem_range] at hy2
    refine le_antisymm (Nat.find_min' _ hy1) ?_
    by_contra hlt
    exact hy2 _ (not_le.1 hlt) (Nat.find_spec (hcov y))

theorem exists_refine [SecondCountableTopology G] (H K L : Subgroup G) [IsClosed (H : Set G)]
    (hLK : L ≤ K) (hLo : IsOpen (L : Set G)) (hLc : IsCompact (L : Set G))
    (t : G ⧸ H → G) (ht : IsLocallyConstant t) (h : ∀ x, x ∈ cosetImage H K (t x)) :
    ∃ t' : G ⧸ H → G, IsLocallyConstant t' ∧ (∀ x, x ∈ cosetImage H L (t' x)) ∧
      ∀ x, (t x)⁻¹ * t' x ∈ K := by
  let e : ℕ → G := TopologicalSpace.denseSeq G
  have he : DenseRange e := TopologicalSpace.denseRange_denseSeq G
  let V : ℕ → Set (G ⧸ H) := fun n =>
    (t ⁻¹' {g | g⁻¹ * e n ∈ K}) ∩ cosetImage H L (e n)
  have hV : ∀ n, IsClopen (V n) := fun n =>
    IsClopen.inter ⟨isOpen_compl_iff.1 (by simpa only [preimage_compl] using (ht ({g | g⁻¹ * e n ∈ K}ᶜ))), ht _⟩
      (isClopen_cosetImage H L hLo hLc (e n))
  have hcov : ∀ x, ∃ n, x ∈ V n := by
    intro x
    obtain ⟨k, hk, hkx⟩ := h x
    have hopen : IsOpen ((fun l : G => t x * k * l) '' (L : Set G)) :=
      (Homeomorph.mulLeft (t x * k)).isOpenMap _ hLo
    obtain ⟨n, l, hl, hn⟩ := he.exists_mem_open hopen ⟨t x * k * 1, 1, L.one_mem, rfl⟩
    refine ⟨n, ?_, l⁻¹, L.inv_mem hl, ?_⟩
    · simp only [mem_preimage, mem_setOf_eq, ← hn]
      have : (t x)⁻¹ * (t x * k * l) = k * l := by group
      rw [this]
      exact K.mul_mem hk (hLK hl)
    · rw [← hn, mul_inv_cancel_right]
      exact hkx
  obtain ⟨f, hf, hfV⟩ := exists_isLocallyConstant_mem V hV hcov
  exact ⟨fun x => e (f x), hf.comp e, fun x => (hfV x).2, fun x => (hfV x).1⟩

theorem exists_subgroup_seq [T2Space G] [LocallyCompactSpace G] [TotallyDisconnectedSpace G]
    [FirstCountableTopology G] :
    ∃ K : ℕ → Subgroup G, K 0 = ⊤ ∧ (∀ n, K (n + 1) ≤ K n) ∧ (∀ n, IsOpen (K n : Set G)) ∧
      (∀ n, IsCompact (K (n + 1) : Set G)) ∧ ∀ W ∈ 𝓝 (1 : G), ∃ n, (K n : Set G) ⊆ W := by
  obtain ⟨U, hU⟩ := (𝓝 (1 : G)).exists_antitone_basis
  choose L hLc hLU using fun n =>
    GroundTheory.Automorphic.exists_openSubgroup_isCompact_subset (hU.1.mem_of_mem (i := n) trivial)
  obtain ⟨K, hK0, hsucc⟩ : ∃ K : ℕ → Subgroup G, K 0 = ⊤ ∧
      ∀ n, K (n + 1) = K n ⊓ (L n : Subgroup G) :=
    ⟨fun n => Nat.rec (motive := fun _ => Subgroup G) ⊤
      (fun n S => S ⊓ (L n : Subgroup G)) n, rfl, fun _ => rfl⟩
  have hopen : ∀ n, IsOpen (K n : Set G) := by
    intro n
    induction n with
    | zero =>
      rw [hK0]
      exact isOpen_univ
    | succ n ih =>
      rw [hsucc, Subgroup.coe_inf]
      exact ih.inter (L n).isOpen
  have hle : ∀ n, K (n + 1) ≤ L n := fun n => by
    rw [hsucc]
    exact inf_le_right
  refine ⟨K, hK0, fun n => by rw [hsucc]; exact inf_le_left, hopen, fun n => ?_, fun W hW => ?_⟩
  · have hclosed : IsClosed (K (n + 1) : Set G) :=
      (⟨K (n + 1), hopen (n + 1)⟩ : OpenSubgroup G).isClosed
    exact (hLc n).of_isClosed_subset hclosed (hle n)
  · obtain ⟨n, -, hn⟩ := hU.1.mem_iff.1 hW
    exact ⟨n + 1, fun g hg => hn (hLU n (hle n hg))⟩

theorem exists_continuous_section (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [T2Space G] [LocallyCompactSpace G] [TotallyDisconnectedSpace G] [SecondCountableTopology G]
    (H : Subgroup G) (hH : IsClosed (H : Set G)) :
    ∃ s : G ⧸ H → G, Continuous s ∧ ∀ c : G ⧸ H, ((s c : G) : G ⧸ H) = c := by
  classical
  haveI : IsClosed (H : Set G) := hH
  obtain ⟨K, hK0, hKle, hKo, hKc, hKb⟩ := exists_subgroup_seq (G := G)

  let P : ℕ → (G ⧸ H → G) → Prop := fun n t =>
    IsLocallyConstant t ∧ ∀ x, x ∈ cosetImage H (K n) (t x)
  have hstep : ∀ n (t : {t // P n t}), ∃ t' : {t // P (n + 1) t},
      ∀ x, (t.1 x)⁻¹ * t'.1 x ∈ K n := by
    rintro n ⟨t, ht, hmem⟩
    obtain ⟨t', h1, h2, h3⟩ :=
      exists_refine H (K n) (K (n + 1)) (hKle n) (hKo _) (hKc n) t ht hmem
    exact ⟨⟨t', h1, h2⟩, h3⟩
  have h0 : P 0 (fun _ => 1) := by
    refine ⟨IsLocallyConstant.const _, fun x => ?_⟩
    obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective x
    exact ⟨g, by simp [hK0], by simp⟩
  choose nxt hnxt using hstep
  let T : (n : ℕ) → {t // P n t} := fun n => Nat.rec ⟨_, h0⟩ (fun n t => nxt n t) n
  have hT : ∀ n x, ((T n).1 x)⁻¹ * (T (n + 1)).1 x ∈ K n := fun n x => hnxt n (T n) x

  let C : G ⧸ H → ℕ → Set G := fun x n => (fun k => (T (n + 1)).1 x * k) '' (K (n + 1) : Set G)
  have hCmem : ∀ x n g, g ∈ C x n ↔ ((T (n + 1)).1 x)⁻¹ * g ∈ K (n + 1) := by
    intro x n g
    constructor
    · rintro ⟨k, hk, rfl⟩
      simpa using hk
    · intro hg
      exact ⟨_, hg, by simp⟩
  have hCanti : ∀ x n, C x (n + 1) ⊆ C x n := by
    intro x n g hg
    rw [hCmem] at hg ⊢
    have h1 := hT (n + 1) x
    have : ((T (n + 1)).1 x)⁻¹ * g = (((T (n + 1)).1 x)⁻¹ * (T (n + 1 + 1)).1 x) *
        (((T (n + 1 + 1)).1 x)⁻¹ * g) := by group
    rw [this]
    exact (K (n + 1)).mul_mem h1 (hKle _ hg)
  have hCne : ∀ x, (⋂ n, C x n).Nonempty := fun x =>
    IsCompact.nonempty_iInter_of_sequence_nonempty_isCompact_isClosed (C x) (hCanti x)
      (fun n => ⟨_, 1, (K (n + 1)).one_mem, rfl⟩)
      ((hKc 0).image (continuous_const.mul continuous_id))
      (fun n => ((hKc n).image (continuous_const.mul continuous_id)).isClosed)
  choose s hs using hCne
  have hsC : ∀ x n, ((T (n + 1)).1 x)⁻¹ * s x ∈ K (n + 1) := fun x n =>
    (hCmem x n _).1 (mem_iInter.1 (hs x) n)
  refine ⟨s, ?_, fun c => ?_⟩
  · rw [continuous_iff_continuousAt]
    intro x
    rw [ContinuousAt, tendsto_def]
    intro W hW

    have hW1 : (fun k => s x * k) ⁻¹' W ∈ 𝓝 (1 : G) := by
      refine (continuous_const.mul continuous_id).continuousAt.preimage_mem_nhds ?_
      simpa using hW
    obtain ⟨m, hm⟩ := hKb _ hW1
    have hmm : (K (m + 1) : Set G) ⊆ (fun k => s x * k) ⁻¹' W :=
      fun g hg => hm (hKle m hg)
    have hloc : {y | (T (m + 1)).1 y = (T (m + 1)).1 x} ∈ 𝓝 x :=
      ((T (m + 1)).2.1.isOpen_fiber _).mem_nhds rfl
    filter_upwards [hloc] with y hy
    have h1 := hsC y m
    have h2 := hsC x m
    rw [hy] at h1
    have : (s x)⁻¹ * s y = (((T (m + 1)).1 x)⁻¹ * s x)⁻¹ * (((T (m + 1)).1 x)⁻¹ * s y) := by group
    have hk : (s x)⁻¹ * s y ∈ K (m + 1) := by
      rw [this]
      exact (K (m + 1)).mul_mem ((K (m + 1)).inv_mem h2) h1
    simpa using hmm hk
  · by_contra hne

    have hopen : IsOpen {g : G | (g : G ⧸ H) ≠ c} :=
      (isOpen_compl_singleton (x := c)).preimage continuous_quotient_mk'
    have hW1 : (fun k => s c * k) ⁻¹' {g : G | (g : G ⧸ H) ≠ c} ∈ 𝓝 (1 : G) := by
      refine (continuous_const.mul continuous_id).continuousAt.preimage_mem_nhds ?_
      simpa using hopen.mem_nhds hne
    obtain ⟨m, hm⟩ := hKb _ hW1
    obtain ⟨k, hk, hkc⟩ := (T (m + 1)).2.2 c
    have hk' : (s c)⁻¹ * ((T (m + 1)).1 c * k) ∈ K (m + 1) := by
      have h2 := hsC c m
      have : (s c)⁻¹ * ((T (m + 1)).1 c * k) = (((T (m + 1)).1 c)⁻¹ * s c)⁻¹ * k := by group
      rw [this]
      exact (K (m + 1)).mul_mem ((K (m + 1)).inv_mem h2) hk
    have := hm (hKle m hk')
    simp only [mem_preimage, mem_setOf_eq, mul_inv_cancel_left] at this
    exact this hkc

end GlobalTheory.CompanionTheory.LGroupSection
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsGLLastBasisVecMulEqStatement
section
open Matrix
open scoped Topology
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_GL_last_basis_vecMul_eq : ∀ (k : Type) [Field k] (m : ℕ) (ξ : Fin (m + 1) → k), ξ ≠ 0 → ∃ h : GL (Fin (m + 1)) k, (Pi.single (Fin.last m) 1 : Fin (m + 1) → k) ᵥ* (h : Matrix (Fin (m + 1)) (Fin (m + 1)) k) = ξ := by
  first | exact @GlobalTheory.CompanionTheory.RowSect.exists_GL_last_row | exact GlobalTheory.CompanionTheory.RowSect.exists_GL_last_row | (intros; apply GlobalTheory.CompanionTheory.RowSect.exists_GL_last_row <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsGLVecMulEqLastBasisStatement
section
open Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_GL_vecMul_eq_last_basis : ∀ {k : Type} [Field k] (n : ℕ) (ξ : Fin (n + 1) → k), ξ ≠ 0 → ∃ g : GL (Fin (n + 1)) k, Matrix.vecMul ξ (g : Matrix (Fin (n + 1)) (Fin (n + 1)) k) = Pi.single (Fin.last n) 1 := by
  first | exact @GlobalTheory.CompanionTheory.Matrixlemmas.exists_GL_vecMul_eq_single_last | exact GlobalTheory.CompanionTheory.Matrixlemmas.exists_GL_vecMul_eq_single_last | (intros; apply GlobalTheory.CompanionTheory.Matrixlemmas.exists_GL_vecMul_eq_single_last <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsHaarUnitaryGroup
section
open MeasureTheory

namespace GlobalTheory.CompanionTheory.ModelS

theorem exists_rightInvariant_measure_unitaryGroup
    (n : ℕ) [MeasurableSpace (Matrix.unitaryGroup (Fin n) ℂ)]
    [BorelSpace (Matrix.unitaryGroup (Fin n) ℂ)] :
    ∃ κ : Measure (Matrix.unitaryGroup (Fin n) ℂ),
      IsFiniteMeasure κ ∧ κ.IsMulRightInvariant ∧ κ.IsOpenPosMeasure := by
  haveI : CompactSpace (Matrix.unitaryGroup (Fin n) ℂ) :=
    GlobalTheory.compactSpace_unitaryGroup (Fin n) ℂ
  let μ : Measure (Matrix.unitaryGroup (Fin n) ℂ) := Measure.haarMeasure ⊤
  refine ⟨μ.inv, inferInstance, inferInstance, inferInstance⟩

end GlobalTheory.CompanionTheory.ModelS
end

