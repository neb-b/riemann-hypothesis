module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Foundations.NormSumPairRankZeroOfCurveCoordNorm
public import Development.AbelianVarietyTheory.BlockTheory.TorsionBlocks.PolarLatticePairs
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0224
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.StandardPairLatticeLocallyOrthonormalBasis
public import Formalism.PairingDivisors.StatementH
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0252
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsLatticeOfAdelicPoint
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0269
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0005
public import Formalism.SharpRestriction.Divisibility.SchurIrreducible
public import Formalism.LocalRingCardinality.DataCD
public import Development.AbelianVarietyTheory.BlockTheory.TorsionBlocks.CartanCoshPower
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0077
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0084
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0081
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0083
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0079
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0060
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.NonemptyCompactDualHaar

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.PtHomInjective
section
open NumberField IsDedekindDomain Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.IndefiniteRowSideFullHecke.PolarLatticePairs
open scoped Pointwise

noncomputable section

namespace GlobalTheory.ThetaLatticePoints

def ptHom (D : D7) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (a d : ℕ) :
    Matrix (Fin d) (Fin a) D.host.E →+ VC D a d :=
  AddMonoidHom.mk' (pt D (tor0 D cc δ) δ) fun y y' => by
    funext τ i j
    simp [pt, embV, tor0, mul_add]

theorem ptHom_apply (D : D7) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (a d : ℕ)
    (z : Matrix (Fin d) (Fin a) D.host.E) : ptHom D cc δ a d z = pt D (tor0 D cc δ) δ z := rfl

theorem ptHom_injective (D : D7) (cc : Ideal (𝓞 D.host.K)) {δ : ℂ} (hδ : δ ≠ 0) (a d : ℕ) :
    Function.Injective (ptHom D cc δ a d) := by
  intro y y' h
  refine Matrix.ext fun i j => ?_
  have h1 : δ * embT D (D.eTau.symm 1) (y i j) = δ * embT D (D.eTau.symm 1) (y' i j) :=
    congrFun (congrFun (congrFun h (D.eTau.symm 1)) i) j
  exact (embT D _).injective (mul_left_cancel₀ hδ h1)

theorem ptHom_smul (D : D7) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (a d : ℕ) (c : 𝓞 D.host.K)
    (y : Matrix (Fin d) (Fin a) D.host.E) :
    ptHom D cc δ a d (((c : D.host.K) : D.host.E) • y) =
      (δ * D.host.φ₀ ((c : D.host.K) : D.host.E)) • embV D (tor0 D cc δ) y := by
  funext τ i j
  simp only [ptHom_apply, pt, embV, tor0, Pi.smul_apply, Matrix.smul_apply, smul_eq_mul, map_mul,
    GlobalTheory.InducedType.restrict_K D τ, mul_assoc]

theorem single_mem (D : D7) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (a d : ℕ) (i : Fin d) (j : Fin a)
    {t : D.host.E} (ht : t ∈ coefLat D cc) (r : 𝓞 D.host.E) :
    ptHom D cc δ a d (Matrix.single i j (r • t)) ∈ La0 D (tor0 D cc δ) a d := by
  induction ht using Submodule.span_induction generalizing r with
  | mem t ht =>
    obtain ⟨c, hc, m, hm, rfl⟩ := ht
    refine AddSubgroup.subset_closure ⟨δ * D.host.φ₀ ((c : D.host.K) : D.host.E),
      AddSubgroup.subset_closure ⟨c, hc, rfl⟩, Matrix.single i j (r • m), ?_, ?_⟩
    · refine (GlobalTheory.OddGenus.mem_iff_entries D a d _).2 fun k l => ?_
      rw [Matrix.single_apply]
      split_ifs
      · exact (D.host.AA0 : Submodule (𝓞 D.host.E) D.host.E).smul_mem r hm
      · exact D.host.AA0.zero_mem
    · rw [← ptHom_smul, Matrix.smul_single, smul_eq_mul, mul_smul_comm]
  | zero => rw [smul_zero, Matrix.single_zero, map_zero]; exact zero_mem _
  | add x y _ _ hx hy => rw [smul_add, Matrix.single_add, map_add (f := _)]; exact add_mem (hx r) (hy r)
  | smul s x _ hx => rw [smul_smul]; exact hx _

theorem La0_eq_map (D : D7) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (a d : ℕ) :
    La0 D (tor0 D cc δ) a d = (lat0 D cc a d).map (ptHom D cc δ a d) := by
  apply le_antisymm
  · refine (AddSubgroup.closure_le _).2 ?_
    rintro _ ⟨w, hw, A, hA, rfl⟩
    obtain ⟨c, hc, rfl⟩ := (GlobalTheory.CurveLattice.mem_lamOf D cc δ w).1 hw
    refine ⟨((c : D.host.K) : D.host.E) • A, fun i j => ?_, ptHom_smul D cc δ a d c A⟩
    exact Submodule.subset_span ⟨c, hc, A i j, (GlobalTheory.OddGenus.mem_iff_entries D a d A).1 hA i j, rfl⟩
  · rintro _ ⟨z, hz, rfl⟩
    set_option synthInstance.maxHeartbeats 100000 in
      rw [Matrix.matrix_eq_sum_single z, map_sum]
    refine sum_mem fun i _ => ?_
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum]
    refine sum_mem fun j _ => ?_
    simpa using single_mem D cc δ a d i j (hz i j) 1

end GlobalTheory.ThetaLatticePoints
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.RelIndexNeZeroOfMoves
section
open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum GlobalTheory.RatEqui GlobalTheory.InertParity
open scoped BigOperators Pointwise

noncomputable section

namespace GlobalTheory.InertParity.LengthSign

theorem not_dvd_relIndex {G : Type} [AddCommGroup G] (A B : AddSubgroup G) (h0 : A.relIndex B ≠ 0) {q s : ℕ}
    (hq : q.Prime) (hs : Nat.Coprime s q) (h : ∀ x ∈ B, s • x ∈ A) : ¬ q ∣ A.relIndex B := by
  intro hd
  have : Fact q.Prime := ⟨hq⟩
  have : Finite (B ⧸ A.addSubgroupOf B) := Nat.finite_of_card_ne_zero h0
  obtain ⟨x, hx⟩ := exists_prime_addOrderOf_dvd_card' (G := B ⧸ A.addSubgroupOf B) q hd
  have : s • x = 0 := by
    induction x using QuotientAddGroup.induction_on with
    | H y =>
      rw [← QuotientAddGroup.mk_nsmul, QuotientAddGroup.eq_zero_iff, AddSubgroup.mem_addSubgroupOf]
      exact h y y.2
  have h1 := addOrderOf_dvd_of_nsmul_eq_zero this
  rw [hx] at h1
  exact hq.one_lt.ne' (Nat.Coprime.eq_one_of_dvd hs.symm h1)

theorem factorization_relIndex_eq {G : Type} [AddCommGroup G] (A A' B : AddSubgroup G) (h0 : A.relIndex B ≠ 0)
    (h0' : A'.relIndex B ≠ 0) {q s : ℕ} (hq : q.Prime) (hs : Nat.Coprime s q) (h : ∀ x ∈ A, s • x ∈ A')
    (h' : ∀ x ∈ A', s • x ∈ A) : (A.relIndex B).factorization q = (A'.relIndex B).factorization q := by
  have hX : (A ⊓ A').relIndex B ≠ 0 := AddSubgroup.relIndex_inf_ne_zero h0 h0'
  have e1 := AddSubgroup.relIndex_inf_mul_relIndex A A' B
  have e2 := AddSubgroup.relIndex_inf_mul_relIndex A' A B
  rw [inf_comm A' A] at e2
  have n1 : A.relIndex (A' ⊓ B) ≠ 0 := left_ne_zero_of_mul (e1 ▸ hX)
  have n2 : A'.relIndex (A ⊓ B) ≠ 0 := left_ne_zero_of_mul (e2 ▸ hX)
  have d1 := not_dvd_relIndex A (A' ⊓ B) n1 hq hs fun x hx => h' x hx.1
  have d2 := not_dvd_relIndex A' (A ⊓ B) n2 hq hs fun x hx => h x hx.1
  have e := congrArg (fun m : ℕ => m.factorization q) (e1.trans e2.symm)
  simp only [Nat.factorization_mul n1 h0', Nat.factorization_mul n2 h0, Finsupp.add_apply,
    Nat.factorization_eq_zero_of_not_dvd d1, Nat.factorization_eq_zero_of_not_dvd d2, zero_add] at e
  exact e.symm

theorem finite_quot {E : Type} [Field E] [NumberField E] {n : ℕ} (L₀ L : Submodule (𝓞 E) (Fin n → E))
    (h₀ : L₀.FG) (h : Submodule.span E (L : Set (Fin n → E)) = ⊤) :
    Finite (L₀ ⧸ Submodule.comap L₀.subtype L) := by
  first
  | exact @_root_.GlobalTheory.FiniteQuotientComap.finite_quotient_comap
  | exact _root_.GlobalTheory.FiniteQuotientComap.finite_quotient_comap
  | (apply _root_.GlobalTheory.FiniteQuotientComap.finite_quotient_comap <;> assumption)
  | (intros; apply _root_.GlobalTheory.FiniteQuotientComap.finite_quotient_comap <;> assumption)
  | (intros; apply @_root_.GlobalTheory.FiniteQuotientComap.finite_quotient_comap <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.FiniteQuotientComap.finite_quotient_comap ..)

theorem eq_lat {D : D7} {n : ℕ} {g : GL (Fin n) (AE D)} {L : Submodule (𝓞 D.host.E) (Fin n → D.host.E)}
    (h : Moves D g L) : L = AdLattice.lat g := by
  ext x
  exact (h x).trans (AdLattice.mem_lat g x).symm

theorem finite_lat (D : D7) {n : ℕ} (g : GL (Fin n) (AE D)) :
    Finite (stdL D n ⧸ Submodule.comap (stdL D n).subtype (AdLattice.lat g)) :=
  finite_quot _ _ (AdLattice.lat_one_eq D n ▸ (AdLattice.lat_isLattice _).fg) (AdLattice.lat_isLattice g).span_eq_top

theorem idx_lat_ne_zero (D : D7) {n : ℕ} (g : GL (Fin n) (AE D)) : idx D (AdLattice.lat g) ≠ 0 := by
  have := finite_lat D g
  exact Nat.card_pos.ne'

theorem exists_int_mul (D : D7) {N : ℕ} (q : ℕ) (k : GA D N) (h : TrivAt D q (k : GL (Fin N) (AE D))) :
    ∃ s : ℕ, Nat.Coprime s q ∧
      (∀ i j, (s : AE D) * ((k : GL (Fin N) (AE D)) : Matrix (Fin N) (Fin N) (AE D)) i j ∈ OhE D) ∧
      ∀ i j, (s : AE D) * (((k : GL (Fin N) (AE D))⁻¹ : GL (Fin N) (AE D)) :
        Matrix (Fin N) (Fin N) (AE D)) i j ∈ OhE D := by
  have h0 : ∀ i j, ∃ m : ℕ, Nat.Coprime m q ∧ (m : AE D) *
      (((k : GL (Fin N) (AE D)) : Matrix (Fin N) (Fin N) (AE D)) i j -
        (1 : Matrix (Fin N) (Fin N) (AE D)) i j) ∈ OhE D := by
    intro i j
    obtain ⟨m, -, hm, s, hs, he⟩ := h i j 0
    refine ⟨m, hm, ?_⟩
    rw [pow_zero, one_mul] at he
    rw [he]
    exact hs
  choose m hm hmS using h0
  set s : ℕ := ∏ r : Fin N × Fin N, m r.1 r.2 with hs
  have hint : ∀ i j, (s : AE D) * ((k : GL (Fin N) (AE D)) : Matrix (Fin N) (Fin N) (AE D)) i j ∈ OhE D := by
    intro i j
    obtain ⟨c, hc⟩ := Finset.dvd_prod_of_mem (fun r : Fin N × Fin N => m r.1 r.2) (Finset.mem_univ (i, j))
    have h1 : (1 : Matrix (Fin N) (Fin N) (AE D)) i j ∈ OhE D := by
      rw [Matrix.one_apply]
      split_ifs
      · exact one_mem _
      · exact zero_mem _
    have : (s : AE D) * ((k : GL (Fin N) (AE D)) : Matrix (Fin N) (Fin N) (AE D)) i j = (c : AE D) * ((m i j : AE D) *
        (((k : GL (Fin N) (AE D)) : Matrix (Fin N) (Fin N) (AE D)) i j -
          (1 : Matrix (Fin N) (Fin N) (AE D)) i j)) + (s : AE D) * (1 : Matrix (Fin N) (Fin N) (AE D)) i j := by
      rw [hs, hc]; push_cast; ring
    rw [this]
    exact add_mem (mul_mem (natCast_mem _ c) (hmS i j)) (mul_mem (natCast_mem _ s) h1)
  refine ⟨s, Nat.Coprime.prod_left fun r _ => hm r.1 r.2, hint, fun i j => ?_⟩
  rw [AdLattice.inv_entry (D.host.conj : D.host.E →ₐ[ℚ] D.host.E) _ k.2]
  have := Formalism.UG.P.csDual_sig_mem (D.host.conj : D.host.E →ₐ[ℚ] D.host.E) (hint j i)
  rwa [map_mul, map_natCast] at this

theorem agree (D : D7) {n : ℕ} (q : ℕ) (g k : GA D n) (h : TrivAt D q (k : GL (Fin n) (AE D))) :
    ∃ s : ℕ, Nat.Coprime s q ∧
      (∀ x ∈ AdLattice.lat (g : GL (Fin n) (AE D)), s • x ∈ AdLattice.lat ((g * k : GA D n) : GL (Fin n) (AE D))) ∧
      ∀ x ∈ AdLattice.lat ((g * k : GA D n) : GL (Fin n) (AE D)), s • x ∈ AdLattice.lat (g : GL (Fin n) (AE D)) := by
  obtain ⟨s, hs, h1, h2⟩ := exists_int_mul D q k h
  refine ⟨s, hs, fun x hx => ?_, fun x hx => ?_⟩
  · rw [← Nat.cast_smul_eq_nsmul D.host.E]
    refine AdLattice.smul_mem_lat s ?_ hx
    rw [Subgroup.coe_mul, mul_inv_rev, inv_mul_cancel_right]
    exact h2
  · rw [← Nat.cast_smul_eq_nsmul D.host.E]
    refine AdLattice.smul_mem_lat s ?_ hx
    rw [Subgroup.coe_mul, inv_mul_cancel_left]
    exact h1

theorem finite_of_moves {D : D7} {n : ℕ} {g : GL (Fin n) (AE D)} {L : Submodule (𝓞 D.host.E) (Fin n → D.host.E)}
    (h : Moves D g L) : Finite (stdL D n ⧸ Submodule.comap (stdL D n).subtype L) := by
  rw [eq_lat h]
  exact finite_lat D g

theorem relIndex_ne_zero_of_moves {D : D7} {n : ℕ} {g : GL (Fin n) (AE D)}
    {L : Submodule (𝓞 D.host.E) (Fin n → D.host.E)} (h : Moves D g L) :
    L.toAddSubgroup.relIndex (stdL D n).toAddSubgroup ≠ 0 := by
  rw [← idx_eq_relIndex, eq_lat h]
  exact idx_lat_ne_zero D g

theorem agree_of_moves {D : D7} {n : ℕ} {q : ℕ} {g k : GA D n} (h : TrivAt D q (k : GL (Fin n) (AE D)))
    {L L' : Submodule (𝓞 D.host.E) (Fin n → D.host.E)} (hL : Moves D (g : GL (Fin n) (AE D)) L)
    (hL' : Moves D ((g * k : GA D n) : GL (Fin n) (AE D)) L') :
    ∃ s : ℕ, Nat.Coprime s q ∧ (∀ x ∈ L.toAddSubgroup, s • x ∈ L'.toAddSubgroup) ∧
      ∀ x ∈ L'.toAddSubgroup, s • x ∈ L.toAddSubgroup := by
  rw [eq_lat hL, eq_lat hL']
  exact agree D q g k h

theorem agree_std {D : D7} {n : ℕ} {q : ℕ} {k : GA D n} (h : TrivAt D q (k : GL (Fin n) (AE D)))
    {L : Submodule (𝓞 D.host.E) (Fin n → D.host.E)} (hL : Moves D (k : GL (Fin n) (AE D)) L) :
    ∃ s : ℕ, Nat.Coprime s q ∧ ∀ x ∈ (stdL D n).toAddSubgroup, s • x ∈ L.toAddSubgroup := by
  obtain ⟨s, hsq, h, -⟩ := agree D q 1 k h
  rw [one_mul, OneMemClass.coe_one, AdLattice.lat_one_eq, ← eq_lat hL] at h
  exact ⟨s, hsq, h⟩

theorem neg_one_pow_lenQ : ∀ (D : D7) (n : ℕ) (gs gi : GA D n) (Li L : Submodule (𝓞 D.host.E) (Fin n → D.host.E)), SuppSplit D (gs : GL (Fin n) (AE D)) → SuppInert D (gi : GL (Fin n) (AE D)) → Moves D (gi : GL (Fin n) (AE D)) Li → Moves D ((gi * gs : GA D n) : GL (Fin n) (AE D)) L → (-1 : ℂ) ^ lenQ D (stdL D n) Li = sgn D (idx D L) := by
  intro D n gs gi Li L hs hi hLi hL
  have := finite_of_moves hLi
  have h1 : sgn D (idx D Li) = (-1 : ℂ) ^ lenQ D (stdL D n) Li := by
    refine (_root_.GlobalTheory.InertParity.FiniteOrder.ev_card_and_sgn_card D (stdL D n ⧸ Submodule.comap (stdL D n).subtype Li)).2 fun q hq hd => ?_
    by_contra hn
    obtain ⟨s, hsq, h⟩ := agree_std (hi q hq hn) hLi
    exact not_dvd_relIndex _ _ (relIndex_ne_zero_of_moves hLi) hq hsq h ((idx_eq_relIndex Li) ▸ hd)
  rw [← h1]
  refine sgn_congr fun q hq hiq => ?_
  obtain ⟨s, hsq, h, h'⟩ := agree_of_moves (hs q hq hiq) hLi hL
  rw [idx_eq_relIndex, idx_eq_relIndex]
  exact factorization_relIndex_eq _ _ _ (relIndex_ne_zero_of_moves hLi) (relIndex_ne_zero_of_moves hL) hq hsq h h'

end GlobalTheory.InertParity.LengthSign
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.StarMulOfMemKc
section
noncomputable section
namespace GlobalTheory.CartanInt
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.SchurIrreducible GlobalTheory.PolarU GlobalTheory.IndefiniteRowSideFullHecke.CartanCoshPower Matrix MeasureTheory

variable {p q : ℕ}

def l1 {n : Type} [Fintype n] (A : Matrix n n ℂ) : ℝ := ∑ i, ∑ j, ‖A i j‖

def Kc (p q : ℕ) : Set (UpqT p q) := {k | IsKC (UpqT.mat k)}

def eP (B : Fin p → Fin q → ℂ) : UpqT p q :=
  GlobalTheory.CompactDualExists.expU ⟨pY B, (pY_mem B).1⟩

theorem mat_eP (B : Fin p → Fin q → ℂ) : UpqT.mat (eP B) = NormedSpace.exp (pY B) := rfl

theorem continuous_eP : Continuous (eP : (Fin p → Fin q → ℂ) → UpqT p q) :=
  GlobalTheory.CompactDualExists.continuous_expU.comp (continuous_pY.subtype_mk _)

theorem mat_mul (x y : UpqT p q) : UpqT.mat (x * y) = UpqT.mat x * UpqT.mat y := rfl

theorem mat_one : UpqT.mat (1 : UpqT p q) = 1 := rfl

theorem isKC_fromBlocks (U : Matrix (Fin p) (Fin p) ℂ) (V : Matrix (Fin q) (Fin q) ℂ) :
    IsKC (Matrix.fromBlocks U 0 0 V : Mat p q) := by
  intro a b hab
  cases a <;> cases b <;> simp_all [sameBlock]

theorem mem_Kc_iff (k : UpqT p q) : k ∈ Kc p q ↔
    ∃ U ∈ Matrix.unitaryGroup (Fin p) ℂ, ∃ V ∈ Matrix.unitaryGroup (Fin q) ℂ,
      UpqT.mat k = Matrix.fromBlocks U 0 0 V := by
  constructor
  · intro hk
    have hk' : IsKC (UpqT.mat k) := hk
    have h : UpqT.mat k = Matrix.fromBlocks (UpqT.mat k).toBlocks₁₁ 0 0 (UpqT.mat k).toBlocks₂₂ := by
      ext a b
      rcases a with i | i <;> rcases b with j | j
      · rfl
      · exact hk' _ _ (by simp [sameBlock])
      · exact hk' _ _ (by simp [sameBlock])
      · rfl
    have hJ := GlobalTheory.UpqTopology.mat_unitary k
    rw [h] at hJ
    simp only [Formalism.UG.Jpq, Matrix.fromBlocks_conjTranspose, Matrix.fromBlocks_multiply,
      Matrix.fromBlocks_inj] at hJ
    refine ⟨_, ?_, _, ?_, h⟩
    · rw [Matrix.mem_unitaryGroup_iff']; simpa [star_eq_conjTranspose] using hJ.1
    · rw [Matrix.mem_unitaryGroup_iff']; simpa [star_eq_conjTranspose] using hJ.2.2.2
  · rintro ⟨U, -, V, -, h⟩
    show IsKC (UpqT.mat k)
    rw [h]; exact isKC_fromBlocks U V

theorem star_mul_of_mem_Kc {k : UpqT p q} (hk : k ∈ Kc p q) : (UpqT.mat k)ᴴ * UpqT.mat k = 1 := by
  obtain ⟨U, hU, V, hV, h⟩ := (mem_Kc_iff k).1 hk
  rw [Matrix.mem_unitaryGroup_iff', star_eq_conjTranspose] at hU hV
  rw [h]
  simp [Matrix.fromBlocks_conjTranspose, Matrix.fromBlocks_multiply, hU, hV]

theorem mat_inv_of_mem_Kc {k : UpqT p q} (hk : k ∈ Kc p q) : UpqT.mat k⁻¹ = (UpqT.mat k)ᴴ := by
  have h1 : UpqT.mat k * UpqT.mat k⁻¹ = 1 := by rw [← mat_mul, mul_inv_cancel, mat_one]
  calc UpqT.mat k⁻¹ = ((UpqT.mat k)ᴴ * UpqT.mat k) * UpqT.mat k⁻¹ := by
        rw [star_mul_of_mem_Kc hk, one_mul]
    _ = (UpqT.mat k)ᴴ := by rw [mul_assoc, h1, mul_one]

def Ksg (p q : ℕ) : Subgroup (UpqT p q) where
  carrier := Kc p q
  one_mem' := (mem_Kc_iff 1).2 ⟨1, one_mem _, 1, one_mem _, by rw [mat_one, Matrix.fromBlocks_one]⟩
  mul_mem' := by
    intro x y hx hy
    obtain ⟨U, -, V, -, h⟩ := (mem_Kc_iff x).1 hx
    obtain ⟨U', -, V', -, h'⟩ := (mem_Kc_iff y).1 hy
    show IsKC (UpqT.mat (x * y))
    rw [mat_mul, h, h', Matrix.fromBlocks_multiply]
    intro a b hab
    cases a <;> cases b <;> simp_all [sameBlock]
  inv_mem' := by
    intro x hx
    show IsKC (UpqT.mat x⁻¹)
    rw [mat_inv_of_mem_Kc hx]
    have hx' : IsKC (UpqT.mat x) := hx
    intro a b hab
    have : ¬ sameBlock b a := by cases a <;> cases b <;> simp_all [sameBlock]
    simp [hx' b a this]

theorem exists_cartan (g : UpqT p q) : ∃ k ∈ Kc p q, ∃ B, g = k * eP B := by
  obtain ⟨U, hU, V, hV, h⟩ := isCartan_cartanB g
  refine ⟨g * (eP fun i j => cartanB g i j)⁻¹, (mem_Kc_iff _).2 ⟨U, hU, V, hV, ?_⟩, _,
    (inv_mul_cancel_right _ _).symm⟩
  have h1 : UpqT.mat (eP fun i j => cartanB g i j) * UpqT.mat (eP fun i j => cartanB g i j)⁻¹ = 1 := by
    rw [← mat_mul, mul_inv_cancel, mat_one]
  rw [mat_mul, h, Matrix.mul_assoc]
  exact (congrArg _ h1).trans (Matrix.mul_one _)

theorem cartanB_mul_eP {k : UpqT p q} (hk : k ∈ Kc p q) (B : Fin p → Fin q → ℂ) :
    cartanB (k * eP B) = Matrix.of B := by
  obtain ⟨U, hU, V, hV, h⟩ := (mem_Kc_iff k).1 hk
  exact cartanB_eq ⟨U, hU, V, hV, by rw [mat_mul, h]; rfl⟩

theorem polJ_aOf (p q : ℕ) (h : ℕ → ℝ) :
    polJ (aOf p q h) = ∏ ab : PIx p q, shc (rootP h ab.1) := by
  set S := (sinhcAd (aOf p q h)).submatrix (Subtype.val : PIx p q → Ix p q × Ix p q) Subtype.val with hS
  set P : Matrix (PIx p q) (PIx p q) ℂ := Matrix.of fun (cd ab : PIx p q) => eigP ab.1 cd.1 with hP
  have key : S * P = P * Matrix.diagonal fun ab : PIx p q => ((shc (rootP h ab.1) : ℝ) : ℂ) := by
    ext cd ab
    have h1 := congrFun (sinhcAd_mulVec_of_sq_eigen p q _ _ _ (adMat_sq_mulVec_eigP p q h ab)) cd.1
    rw [Matrix.mul_diagonal, Matrix.mul_apply]
    simp only [Matrix.mulVec, dotProduct, Pi.smul_apply, smul_eq_mul] at h1
    rw [← Fintype.sum_subtype_add_sum_subtype (fun x : Ix p q × Ix p q => ¬ sameBlock x.1 x.2)] at h1
    rw [Finset.sum_eq_zero (s := Finset.univ) (f := fun i : {x : Ix p q × Ix p q // ¬ ¬ sameBlock x.1 x.2} =>
      sinhcAd (aOf p q h) cd.1 i.1 * eigP ab.1 i.1)
      (fun i _ => by rw [eigenvectorMatrix_eq_zero_of_sameBlock ab i.1 (not_not.1 i.2), mul_zero]), add_zero] at h1
    simp only [hS, hP, Matrix.submatrix_apply, Matrix.of_apply]
    rw [mul_comm (eigP _ _)]
    exact h1
  have h2 := congrArg Matrix.det key
  rw [Matrix.det_mul, Matrix.det_mul, Matrix.det_diagonal, mul_comm] at h2
  have h3 := mul_left_cancel₀ (det_eigenvectorMatrix_ne_zero p q) h2
  unfold polJ
  rw [← hS, h3, ← Complex.ofReal_prod, Complex.ofReal_re]

theorem polJ_pOf (B : Matrix (Fin p) (Fin q) ℂ) : polJ (pOf B) =
    (∏ i ∈ Finset.range (min p q), shc (2 * singVal B i) * shc (singVal B i) ^ (2 * (max p q - min p q))) *
    ∏ i ∈ Finset.range (min p q), ∏ j ∈ Finset.range (min p q),
      if i < j then (shc (singVal B i - singVal B j) * shc (singVal B i + singVal B j)) ^ 2 else 1 := by
  obtain ⟨U, hU, V, hV, hB⟩ := GlobalTheory.RectSVD.exists_svd_singularValues p q B
  have e : pOf B = Matrix.fromBlocks U 0 0 V * aOf p q (singVal B) * Matrix.fromBlocks Uᴴ 0 0 Vᴴ := by
    conv_lhs => rw [hB]
    simp [aOf, pOf, singVal, Matrix.fromBlocks_multiply, Matrix.mul_assoc]
  have h1 : U * Uᴴ = 1 := Matrix.mem_unitaryGroup_iff.mp hU
  have h2 : V * Vᴴ = 1 := Matrix.mem_unitaryGroup_iff.mp hV
  rw [e, Conj.polJ_conj p q _ _ _ (by simp [Matrix.fromBlocks_multiply, h1, h2]) (isKC_fromBlocks _ _)
    (isKC_fromBlocks _ _), polJ_aOf, RootProd.prod_shc_rootP]

theorem one_le_shc (x : ℝ) : 1 ≤ shc x := by
  unfold shc
  split_ifs with hx
  · exact le_rfl
  · rcases lt_or_gt_of_ne hx with h | h
    · rw [le_div_iff_of_neg h, one_mul]; exact Real.sinh_le_self_iff.2 h.le
    · rw [le_div_iff₀ h, one_mul]; exact Real.self_le_sinh_iff.2 h.le

theorem one_le_prod_real {ι : Type} {s : Finset ι} {f : ι → ℝ} (h : ∀ i ∈ s, 1 ≤ f i) :
    1 ≤ ∏ i ∈ s, f i :=
  Finset.prod_induction f (fun x => 1 ≤ x) (fun _ _ => one_le_mul_of_one_le_of_one_le) le_rfl h

theorem one_le_polJ (B : Matrix (Fin p) (Fin q) ℂ) : 1 ≤ polJ (pOf B) := by
  rw [polJ_pOf]
  refine one_le_mul_of_one_le_of_one_le (one_le_prod_real fun i _ => ?_)
    (one_le_prod_real fun i _ => one_le_prod_real fun j _ => ?_)
  · exact one_le_mul_of_one_le_of_one_le (one_le_shc _) (one_le_pow₀ (one_le_shc _))
  · split_ifs
    · exact one_le_pow₀ (one_le_mul_of_one_le_of_one_le (one_le_shc _) (one_le_shc _))
    · exact le_rfl

theorem shc_le_exp (x : ℝ) : shc x ≤ Real.exp |x| := by
  have key : ∀ y : ℝ, 0 < y → Real.sinh y / y ≤ Real.exp y := by
    intro y hy
    rw [div_le_iff₀ hy, Real.sinh_eq, div_le_iff₀ two_pos]
    have h1 : Real.exp (-y) = Real.exp y * Real.exp (-(2 * y)) := by rw [← Real.exp_add]; ring_nf
    have h2 := Real.add_one_le_exp (-(2 * y))
    have h3 := Real.exp_pos y
    rw [h1]; nlinarith
  unfold shc
  split_ifs with hx
  · exact Real.one_le_exp (abs_nonneg x)
  · rcases lt_or_gt_of_ne hx with h | h
    · have := key (-x) (neg_pos.2 h)
      rwa [Real.sinh_neg, neg_div_neg_eq, ← abs_of_neg h] at this
    · rw [abs_of_pos h]; exact key x h

theorem singVal_nonneg (B : Matrix (Fin p) (Fin q) ℂ) (i : ℕ) : 0 ≤ singVal B i :=
  LinearMap.singularValues_nonneg _ _

theorem sum_sum_ite_lt (m : ℕ) (s : ℕ → ℝ) :
    ∑ i ∈ Finset.range m, ∑ j ∈ Finset.range m, (if i < j then s i + s j else 0) =
      ((m : ℝ) - 1) * ∑ i ∈ Finset.range m, s i := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [Finset.sum_range_succ, Finset.sum_eq_zero (s := Finset.range (m + 1))
      (fun j hj => if_neg (by have := Finset.mem_range.1 hj; omega)), add_zero]
    simp only [Finset.sum_range_succ, Finset.sum_add_distrib, ih]
    rw [Finset.sum_congr rfl (fun i hi => if_pos (Finset.mem_range.1 hi)), Finset.sum_add_distrib]
    simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    push_cast; ring

theorem polJ_le_exp (B : Matrix (Fin p) (Fin q) ℂ) : polJ (pOf B) ≤
    Real.exp (2 * (((p + q : ℕ) : ℝ) - 1) * ∑ i ∈ Finset.range (min p q), singVal B i) := by
  have h0 := singVal_nonneg B
  have hs : ∀ x, 0 ≤ shc x := fun x => zero_le_one.trans (one_le_shc x)
  rw [polJ_pOf]
  set s := singVal B
  set m := min p q with hm
  set D := max p q - min p q with hD
  have hA : ∏ i ∈ Finset.range m, shc (2 * s i) * shc (s i) ^ (2 * D) ≤
      Real.exp ((2 + 2 * (D : ℝ)) * ∑ i ∈ Finset.range m, s i) := by
    rw [Finset.mul_sum, Real.exp_sum]
    refine Finset.prod_le_prod₀ (fun i _ => mul_nonneg (hs _) (pow_nonneg (hs _) _)) fun i _ => ?_
    have a1 := shc_le_exp (2 * s i)
    have a2 := shc_le_exp (s i)
    rw [abs_of_nonneg (by linarith [h0 i])] at a1 a2
    calc _ ≤ Real.exp (2 * s i) * Real.exp (s i) ^ (2 * D) :=
          mul_le_mul a1 (pow_le_pow_left₀ (hs _) a2 _) (pow_nonneg (hs _) _) (Real.exp_pos _).le
      _ = _ := by rw [← Real.exp_nat_mul, ← Real.exp_add]; push_cast; ring_nf
  have hB : (∏ i ∈ Finset.range m, ∏ j ∈ Finset.range m,
      if i < j then (shc (s i - s j) * shc (s i + s j)) ^ 2 else 1) ≤
      Real.exp (4 * (((m : ℝ) - 1) * ∑ i ∈ Finset.range m, s i)) := by
    rw [← sum_sum_ite_lt, Finset.mul_sum, Real.exp_sum]
    refine Finset.prod_le_prod₀ (fun i _ => Finset.prod_nonneg fun j _ => by split_ifs <;> positivity)
      fun i _ => ?_
    rw [Finset.mul_sum, Real.exp_sum]
    refine Finset.prod_le_prod₀ (fun j _ => by split_ifs <;> positivity) fun j _ => ?_
    split_ifs
    · have a1 := (shc_le_exp (s i - s j)).trans (Real.exp_le_exp.2
        (show |s i - s j| ≤ s i + s j from abs_le.2 ⟨by linarith [h0 i], by linarith [h0 j]⟩))
      have a2 := shc_le_exp (s i + s j)
      rw [abs_of_nonneg (by linarith [h0 i, h0 j])] at a2
      calc _ ≤ (Real.exp (s i + s j) * Real.exp (s i + s j)) ^ 2 :=
            pow_le_pow_left₀ (mul_nonneg (hs _) (hs _)) (mul_le_mul a1 a2 (hs _) (Real.exp_pos _).le) 2
        _ = _ := by rw [← Real.exp_add, ← Real.exp_nat_mul]; push_cast; ring_nf
    · simp
  refine (mul_le_mul hA hB (Finset.prod_nonneg fun i _ => Finset.prod_nonneg fun j _ => by
    split_ifs <;> positivity) (Real.exp_pos _).le).trans (le_of_eq ?_)
  have e : ((p + q : ℕ) : ℝ) = D + 2 * m := by
    have : p + q = D + 2 * m := by omega
    exact_mod_cast this
  rw [← Real.exp_add, e]; ring_nf

end GlobalTheory.CartanInt
end
end

