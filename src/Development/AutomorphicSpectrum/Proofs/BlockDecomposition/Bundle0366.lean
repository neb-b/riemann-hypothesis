module

public import Mathlib
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0351
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0353
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0027

@[expose] public section

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TwistedKernelOfSmallBoxCharacter
section
noncomputable section

open GlobalTheory.PRep GlobalTheory.BZMir GroundTheory.LocalField Matrix GlobalTheory.CompanionTheory.MirFourier

namespace GlobalTheory.CompanionTheory.MirFourier.FiniteInversion

open GlobalTheory.CompanionTheory.TwistedAverage

section Abstract

variable {G V : Type} [CommGroup G] [AddCommGroup V] [Module ℂ V]

theorem eq_zero_of_orthogonal (ρ : Representation ℂ G V) (L : Subgroup G) {I : Type} [Fintype I]
    [Nonempty I] (θ : I → (L →* ℂˣ)) (K : Subgroup L) [K.FiniteIndex] {v : V}
    (hK : ∀ x ∈ K, ρ (x : G) v = v)
    (hM : ∀ i, ∃ M : Subgroup L, M.FiniteIndex ∧ ∀ (N : Subgroup L) [N.Normal] [Fintype (L ⧸ N)],
      N ≤ M → ∑ q : L ⧸ N, twOrbit ρ L (θ i) v q.out = 0)
    (h1 : ∀ x ∈ K, ∑ i, (((θ i x)⁻¹ : ℂˣ) : ℂ) = Fintype.card I)
    (h0 : ∀ x, x ∉ K → ∑ i, (((θ i x)⁻¹ : ℂˣ) : ℂ) = 0) : v = 0 := by
  classical
  choose M hMfin hMsum using hM
  haveI : ∀ i, (M i).FiniteIndex := hMfin
  haveI : (⨅ i, M i).FiniteIndex := Subgroup.finiteIndex_iInf hMfin
  set N : Subgroup L := K ⊓ ⨅ i, M i with hNdef
  haveI : N.Normal := Subgroup.normal_of_isMulCommutative N
  letI : Fintype (L ⧸ N) := Subgroup.fintypeQuotientOfFiniteIndex
  have hNK : N ≤ K := inf_le_left
  have hNM : ∀ i, N ≤ M i := fun i => inf_le_right.trans (iInf_le _ i)
  have htot : ∑ q : L ⧸ N, (∑ i, (((θ i q.out)⁻¹ : ℂˣ) : ℂ)) • ρ (q.out : G) v = 0 := by
    simp_rw [Finset.sum_smul]
    rw [Finset.sum_comm]
    exact Finset.sum_eq_zero fun i _ => hMsum i N (hNM i)
  have hterm : ∀ q : L ⧸ N, (∑ i, (((θ i q.out)⁻¹ : ℂˣ) : ℂ)) • ρ (q.out : G) v =
      if q.out ∈ K then (Fintype.card I : ℂ) • v else 0 := by
    intro q
    split_ifs with h
    · rw [h1 _ h, hK _ h]
    · rw [h0 _ h, zero_smul]
  rw [Finset.sum_congr rfl (fun q _ => hterm q), Finset.sum_ite, Finset.sum_const_zero, add_zero,
    Finset.sum_const, ← Nat.cast_smul_eq_nsmul ℂ, smul_smul] at htot
  refine (smul_eq_zero.mp htot).resolve_left
    (mul_ne_zero (Nat.cast_ne_zero.mpr ?_) (Nat.cast_ne_zero.mpr Fintype.card_ne_zero))
  apply Finset.card_ne_zero_of_mem (a := (QuotientGroup.mk 1 : L ⧸ N))
  refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩
  obtain ⟨h, hh⟩ := QuotientGroup.mk_out_eq_mul N (1 : L)
  rw [hh, one_mul]
  exact hNK h.2

end Abstract

section Box

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem coe_box_eq (n : ℕ) (N : ℤ) : (box k n N : Set (Multiplicative (Fin n → k))) =
    Multiplicative.toAdd ⁻¹' (Set.univ.pi fun _ : Fin n => (valBall k N : Set k)) := by
  ext x
  simp only [SetLike.mem_coe, Set.mem_preimage, Set.mem_univ_pi]
  exact Iff.rfl

theorem isCompact_box (n : ℕ) (N : ℤ) :
    IsCompact (box k n N : Set (Multiplicative (Fin n → k))) := by
  rw [coe_box_eq]
  exact isCompact_univ_pi fun _ => isCompact_valBall N

theorem isOpen_box (n : ℕ) (N : ℤ) :
    IsOpen (box k n N : Set (Multiplicative (Fin n → k))) := by
  rw [coe_box_eq]
  exact (isOpen_set_pi Set.finite_univ fun _ _ => isOpen_valBall N).preimage continuous_toAdd

theorem dotProduct_mem_valBall {n : ℕ} {m p : ℤ} {a x : Fin n → k} (ha : ∀ i, a i ∈ valBall k m)
    (hx : ∀ i, x i ∈ valBall k p) : a ⬝ᵥ x ∈ valBall k (m + p) := by
  show ∑ i, a i * x i ∈ valBall k (m + p)
  exact AddSubgroup.sum_mem _ fun i _ => mul_mem_valBall (ha i) (hx i)

variable {ψ : AddChar k Circle}

theorem chi_eq_one (hψ : Continuous ψ) (hψ1 : ψ ≠ 1) {n : ℕ} {a : Fin n → k}
    {x : Multiplicative (Fin n → k)} (h : a ⬝ᵥ x.toAdd ∈ valBall k (addCharConductor ψ)) :
    chi k ψ a x = 1 := by
  have h1 : ψ (a ⬝ᵥ x.toAdd) = 1 := isTrivialOn_addCharConductor hψ hψ1 _ h
  simp [chi, h1]

theorem isOpen_ker_chiOn (hψ : Continuous ψ) (hψ1 : ψ ≠ 1) {n : ℕ} (a : Fin n → k)
    (L : Subgroup (Multiplicative (Fin n → k))) : IsOpen ((chiOn k ψ a L).ker : Set L) := by
  have hU : IsOpen {x : Multiplicative (Fin n → k) | a ⬝ᵥ x.toAdd ∈ valBall k (addCharConductor ψ)} :=
    (isOpen_valBall _).preimage (continuous_const.dotProduct continuous_toAdd)
  refine Subgroup.isOpen_of_mem_nhds _ (g := 1) ?_
  have hmem : (Subtype.val ⁻¹' {x : Multiplicative (Fin n → k) |
      a ⬝ᵥ x.toAdd ∈ valBall k (addCharConductor ψ)} : Set L) ∈ nhds (1 : L) :=
    (hU.preimage continuous_subtype_val).mem_nhds (by simp [zero_mem])
  refine Filter.mem_of_superset hmem fun y hy => ?_
  rw [SetLike.mem_coe, MonoidHom.mem_ker]
  exact chi_eq_one hψ hψ1 hy

variable (ψ)

def ev {n : ℕ} (x : Multiplicative (Fin n → k)) (a : Multiplicative (Fin n → k)) : ℂ :=
  (((chi k ψ a.toAdd x)⁻¹ : ℂˣ) : ℂ)

theorem ev_mul {n : ℕ} (x a b : Multiplicative (Fin n → k)) :
    ev ψ x (a * b) = ev ψ x a * ev ψ x b := by
  simp [ev, chi, add_dotProduct, AddChar.map_add_eq_mul, mul_inv]
  exact mul_comm _ _

theorem ev_eq_one {n : ℕ} {x a : Multiplicative (Fin n → k)} (h : chi k ψ a.toAdd x = 1) :
    ev ψ x a = 1 := by
  unfold ev
  rw [h, inv_one, Units.val_one]

theorem sum_ev_eq_zero {n : ℕ} (S T : Subgroup (Multiplicative (Fin n → k)))
    [Fintype (S ⧸ T.subgroupOf S)] (x : Multiplicative (Fin n → k))
    (hT : ∀ t ∈ T, chi k ψ (Multiplicative.toAdd t) x = 1)
    {l : Multiplicative (Fin n → k)} (hl : l ∈ S) (hne : chi k ψ l.toAdd x ≠ 1) :
    ∑ q : S ⧸ T.subgroupOf S, ev ψ x (q.out : Multiplicative (Fin n → k)) = 0 := by
  classical
  have hf : ∀ s : S, ∀ t ∈ T.subgroupOf S,
      ev ψ x ((s * t : S) : Multiplicative (Fin n → k)) = ev ψ x (s : Multiplicative (Fin n → k)) := by
    intro s t ht
    rw [Subgroup.coe_mul, ev_mul, ev_eq_one ψ (hT _ (Subgroup.mem_subgroupOf.mp ht)), mul_one]
  haveI : (T.subgroupOf S).Normal := Subgroup.normal_of_isMulCommutative _
  have key := sum_out_mul_right (T.subgroupOf S)
    (fun s : S => ev ψ x (s : Multiplicative (Fin n → k))) hf ⟨l, hl⟩
  simp only [Subgroup.coe_mul, ev_mul] at key
  rw [← Finset.sum_mul] at key
  have hl1 : ev ψ x l ≠ 1 := by
    intro h
    apply hne
    unfold ev at h
    exact inv_eq_one.mp (Units.val_eq_one.mp h)
  have hz : (∑ q : S ⧸ T.subgroupOf S, ev ψ x (q.out : Multiplicative (Fin n → k))) *
      (ev ψ x l - 1) = 0 := by
    rw [mul_sub, mul_one, key, sub_self]
  rcases mul_eq_zero.mp hz with h | h
  · exact h
  · exact absurd (sub_eq_zero.mp h) hl1

variable {ψ}

theorem exists_chi_ne_one (hψ : Continuous ψ) (hψ1 : ψ ≠ 1) {n : ℕ} {N : ℤ}
    {x : Multiplicative (Fin n → k)} (hx : x ∉ box k n N) :
    ∃ l ∈ box k n (addCharConductor ψ - N), chi k ψ (Multiplicative.toAdd l) x ≠ 1 := by
  classical
  have hx' : ∃ i, x.toAdd i ∉ valBall k N := by
    by_contra hcon
    push_neg at hcon
    exact hx hcon
  obtain ⟨i, hi⟩ := hx'
  have hnt : ¬ IsTrivialOn (ψ.mulShift (x.toAdd i)) (addCharConductor ψ - N) := by
    rw [isTrivialOn_mulShift_iff_mem hψ hψ1, sub_sub_cancel]
    exact hi
  unfold IsTrivialOn at hnt
  push_neg at hnt
  obtain ⟨y, hy, hψy⟩ := hnt
  refine ⟨Multiplicative.ofAdd (Pi.single i y : Fin n → k), ?_, ?_⟩
  · show ∀ j, (Multiplicative.toAdd (Multiplicative.ofAdd (Pi.single i y : Fin n → k))) j ∈
      valBall k (addCharConductor ψ - N)
    intro j
    rw [toAdd_ofAdd]
    by_cases hj : j = i
    · subst hj
      rw [Pi.single_eq_same]
      exact hy
    · rw [Pi.single_eq_of_ne hj]
      exact zero_mem _
  · intro hc
    apply hψy
    rw [AddChar.mulShift_apply, mul_comm]
    have h2 : Circle.toUnits (ψ ((Pi.single i y : Fin n → k) ⬝ᵥ x.toAdd)) = 1 := by
      simpa [chi] using hc
    rw [single_dotProduct] at h2
    have h3 := congrArg (fun u : ℂˣ => (u : ℂ)) h2
    simp only [Circle.toUnits_apply, Units.val_mk0, Units.val_one] at h3
    exact Circle.ext h3

end Box

theorem fourier_finite : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (ψ : AddChar k Circle), Continuous ψ → ψ ≠ 1 → ∀ (n : ℕ) (V : Type) [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ (Multiplicative (Fin n → k)) V), IsSmooth ρ → ∀ (v : V) (N J : ℤ), J ≤ N → (∀ x ∈ box k n N, ρ x v = v) → (∀ a : Fin n → k, (∀ i, a i ∈ valBall k (addCharConductor ψ - N)) → v ∈ twKer ρ (box k n J) (chiOn k ψ a (box k n J))) → v = 0 := by
  intro k _ _ _ _ ψ hψ hψ1 n V _ _ ρ hρ v N J hJN hfix htw
  classical
  have hfin : ∀ (A B : Subgroup (Multiplicative (Fin n → k))), IsCompact (A : Set (Multiplicative (Fin n → k))) →
      IsOpen (B : Set (Multiplicative (Fin n → k))) → (B.subgroupOf A).FiniteIndex := by
    intro A B hA hB
    haveI : CompactSpace A := isCompact_iff_compactSpace.mp hA
    haveI : Finite (A ⧸ B.subgroupOf A) := Subgroup.quotient_finite_of_isOpen _ (by
      rw [Subgroup.coe_subgroupOf]
      exact hB.preimage continuous_subtype_val)
    exact Subgroup.finiteIndex_of_finite_quotient
  haveI : ((box k n N).subgroupOf (box k n J)).FiniteIndex :=
    hfin _ _ (isCompact_box n J) (isOpen_box n N)
  haveI : ((box k n (addCharConductor ψ - J)).subgroupOf
      (box k n (addCharConductor ψ - N))).FiniteIndex :=
    hfin _ _ (isCompact_box n (addCharConductor ψ - N)) (isOpen_box n (addCharConductor ψ - J))
  letI : Fintype (box k n (addCharConductor ψ - N) ⧸
      (box k n (addCharConductor ψ - J)).subgroupOf (box k n (addCharConductor ψ - N))) :=
    Subgroup.fintypeQuotientOfFiniteIndex
  refine eq_zero_of_orthogonal ρ (box k n J)
    (I := box k n (addCharConductor ψ - N) ⧸
      (box k n (addCharConductor ψ - J)).subgroupOf (box k n (addCharConductor ψ - N)))
    (fun q => chiOn k ψ (q.out : Multiplicative (Fin n → k)).toAdd (box k n J))
    ((box k n N).subgroupOf (box k n J)) ?_ ?_ ?_ ?_
  · intro x hx
    exact hfix x (Subgroup.mem_subgroupOf.mp hx)
  · intro q
    exact exists_sum_eq_zero hρ (isCompact_box n J) _ (isOpen_ker_chiOn hψ hψ1 _ _)
      (htw _ (fun i => q.out.2 i))
  · intro x hx
    have hxN : (x : Multiplicative (Fin n → k)) ∈ box k n N := Subgroup.mem_subgroupOf.mp hx
    have hone : ∀ q : box k n (addCharConductor ψ - N) ⧸
        (box k n (addCharConductor ψ - J)).subgroupOf (box k n (addCharConductor ψ - N)),
        (((chiOn k ψ (q.out : Multiplicative (Fin n → k)).toAdd (box k n J) x)⁻¹ : ℂˣ) : ℂ) = 1 := by
      intro q
      have hmem := dotProduct_mem_valBall (fun i => q.out.2 i) (fun i => hxN i)
      rw [sub_add_cancel] at hmem
      have h := chi_eq_one hψ hψ1 hmem
      show (((chi k ψ (q.out : Multiplicative (Fin n → k)).toAdd (x : Multiplicative (Fin n → k)))⁻¹ :
        ℂˣ) : ℂ) = 1
      rw [h, inv_one, Units.val_one]
    rw [Finset.sum_congr rfl (fun q _ => hone q), Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
      mul_one]
  · intro x hx
    have hxN : (x : Multiplicative (Fin n → k)) ∉ box k n N :=
      fun h => hx (Subgroup.mem_subgroupOf.mpr h)
    obtain ⟨l, hl, hne⟩ := exists_chi_ne_one hψ hψ1 hxN
    have hT : ∀ t ∈ box k n (addCharConductor ψ - J),
        chi k ψ (Multiplicative.toAdd t) (x : Multiplicative (Fin n → k)) = 1 := by
      intro t ht
      have hmem := dotProduct_mem_valBall (fun i => ht i) (fun i => x.2 i)
      rw [sub_add_cancel] at hmem
      exact chi_eq_one hψ hψ1 hmem
    exact sum_ev_eq_zero ψ (box k n (addCharConductor ψ - N)) (box k n (addCharConductor ψ - J))
      (x : Multiplicative (Fin n → k)) hT hl hne

end GlobalTheory.CompanionTheory.MirFourier.FiniteInversion

end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.UniformTwistedInvarianceOnBall
section
noncomputable section

open GlobalTheory.PRep GlobalTheory.BZMir GroundTheory.LocalField Matrix

namespace GlobalTheory.CompanionTheory.MirFourier

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem chi_eq_on_box {ψ : AddChar k Circle} {c j : ℤ} (hc : IsTrivialOn ψ c) {n : ℕ}
    {a a' : Fin n → k} (h : ∀ i, a' i - a i ∈ valBall k (c - j))
    {x : Multiplicative (Fin n → k)} (hx : x ∈ box k n j) : chi k ψ a x = chi k ψ a' x := by
  have hmem : (a' - a) ⬝ᵥ x.toAdd ∈ valBall k c := by
    refine sum_mem fun i _ => ?_
    have := mul_mem_valBall (h i) (hx i)
    simpa using this
  have hsplit : a' ⬝ᵥ x.toAdd = a ⬝ᵥ x.toAdd + (a' - a) ⬝ᵥ x.toAdd := by
    rw [← add_dotProduct]
    simp
  rw [chi_apply, chi_apply, hsplit, AddChar.map_add_eq_mul, hc _ hmem, mul_one]

theorem twKer_chiOn_le {n : ℕ} {V : Type} [AddCommGroup V] [Module ℂ V]
    (ρ : Representation ℂ (Multiplicative (Fin n → k)) V) (ψ : AddChar k Circle)
    {a a' : Fin n → k} {H H' : Subgroup (Multiplicative (Fin n → k))} (hH : H ≤ H')
    (h : ∀ x ∈ H, chi k ψ a x = chi k ψ a' x) :
    twKer ρ H (chiOn k ψ a H) ≤ twKer ρ H' (chiOn k ψ a' H') := by
  refine Submodule.span_le.2 ?_
  rintro _ ⟨x, w, rfl⟩
  refine Submodule.subset_span ⟨⟨x, hH x.2⟩, w, ?_⟩
  simp [h x x.2]

theorem exists_box_forall_chi (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] (ψ : AddChar k Circle) (hψ : Continuous ψ) (n : ℕ) (V : Type)
    [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ (Multiplicative (Fin n → k)) V) (v : V)
    (M : ℤ)
    (hv : ∀ a : Fin n → k, ∃ j : ℤ, ∀ j' ≤ j, v ∈ twKer ρ (box k n j') (chiOn k ψ a (box k n j'))) :
    ∃ J : ℤ, ∀ J' ≤ J, ∀ a : Fin n → k, (∀ i, a i ∈ valBall k M) →
      v ∈ twKer ρ (box k n J') (chiOn k ψ a (box k n J')) := by
  classical
  obtain ⟨c, hc⟩ := exists_isTrivialOn ψ hψ
  choose j hj using hv
  let U : (Fin n → k) → Set (Fin n → k) := fun a =>
    (fun a' => a' - a) ⁻¹' Set.pi Set.univ fun _ => (valBall k (c - j a) : Set k)
  have hUopen : ∀ a, IsOpen (U a) := fun a =>
    (isOpen_set_pi Set.finite_univ fun _ _ => isOpen_valBall _).preimage
      (continuous_id.sub continuous_const)
  have hS : IsCompact (Set.pi Set.univ fun _ : Fin n => (valBall k M : Set k)) :=
    isCompact_univ_pi fun _ => isCompact_valBall M
  have hcover : (Set.pi Set.univ fun _ : Fin n => (valBall k M : Set k)) ⊆ ⋃ a, U a := by
    intro a _
    refine Set.mem_iUnion.2 ⟨a, fun i _ => ?_⟩
    simp
  obtain ⟨t, ht⟩ := hS.elim_finite_subcover U hUopen hcover
  obtain ⟨J, hJ⟩ := (t.image j).bddBelow
  refine ⟨J, fun J' hJ' a' ha' => ?_⟩
  obtain ⟨a, hat, haU⟩ := Set.mem_iUnion₂.1 (ht (fun i _ => ha' i))
  have hle : J' ≤ j a := hJ'.trans (hJ (Finset.mem_coe.2 (Finset.mem_image_of_mem j hat)))
  exact twKer_chiOn_le ρ ψ (box_antitone k n hle)
    (fun x hx => chi_eq_on_box hc (fun i => haU i (Set.mem_univ i)) hx) (hj a (j a) le_rfl)

end GlobalTheory.CompanionTheory.MirFourier

end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.UnitaryExpSkewHermitian
section
open Matrix
open GlobalTheory.CompanionTheory.GLK (expG)
open PositivityTheory.RgBcC.Real (uG)
open PositivityTheory.RgTw (Mat G)

namespace GlobalTheory.CompanionTheory.UnitaryExp

theorem exists_unitary_diag {n : ℕ} (K : Matrix (Fin n) (Fin n) ℂ) (h1 : Kᴴ * K = 1) (h2 : K * Kᴴ = 1) :
    ∃ (V : Matrix (Fin n) (Fin n) ℂ) (z : Fin n → ℂ), Vᴴ * V = 1 ∧ V * Vᴴ = 1 ∧
      Vᴴ * K * V = Matrix.diagonal z ∧ ∀ a, ‖z a‖ = 1 := by
  classical
  set A : Matrix (Fin n) (Fin n) ℂ := K + Kᴴ with hA
  set B : Matrix (Fin n) (Fin n) ℂ := Complex.I • (K - Kᴴ) with hB
  have hAh : Aᴴ = A := by
    simp [hA, Matrix.conjTranspose_add, add_comm]
  have hBh : Bᴴ = B := by
    simp [hB, Matrix.conjTranspose_smul, Matrix.conjTranspose_sub, smul_sub]
    abel
  have hAB : A * B = B * A := by
    have e : (K + Kᴴ) * (K - Kᴴ) = (K - Kᴴ) * (K + Kᴴ) := by
      simp only [Matrix.add_mul, Matrix.mul_add, Matrix.sub_mul, Matrix.mul_sub, h1, h2]
      abel
    rw [hA, hB, Matrix.mul_smul, Matrix.smul_mul, e]
  obtain ⟨V, hV, hD⟩ := GlobalTheory.CompanionTheory.SimDiag.exists_unitary_isDiag ({A, B} : Set (Matrix (Fin n) (Fin n) ℂ))
    (by
      rintro X (rfl | rfl)
      · exact hAh
      · exact hBh)
    (by
      rintro X (rfl | rfl) Y (rfl | rfl)
      · rfl
      · exact hAB
      · exact hAB.symm
      · rfl)
  have hV1 : Vᴴ * V = 1 := Matrix.mem_unitaryGroup_iff'.1 hV
  have hV2 : V * Vᴴ = 1 := Matrix.mem_unitaryGroup_iff.1 hV
  have hKAB : K = (1 / 2 : ℂ) • (A - Complex.I • B) := by
    simp only [hA, hB, smul_smul, Complex.I_mul_I]
    module
  have hDd : (Vᴴ * K * V).IsDiag := by
    have e : Vᴴ * K * V = (1 / 2 : ℂ) • (Vᴴ * A * V - Complex.I • (Vᴴ * B * V)) := by
      conv_lhs => rw [hKAB]
      simp only [Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_sub, Matrix.sub_mul]
    rw [e]
    exact ((hD A (by simp)).sub ((hD B (by simp)).smul _)).smul _
  refine ⟨V, Matrix.diag (Vᴴ * K * V), hV1, hV2, hDd.diagonal_diag.symm, fun a => ?_⟩
  set D := Vᴴ * K * V with hDdef
  have hDD : Dᴴ * D = 1 := by
    have e : Dᴴ = Vᴴ * Kᴴ * V := by
      simp [hDdef, Matrix.conjTranspose_mul, Matrix.mul_assoc]
    rw [e, hDdef]
    calc Vᴴ * Kᴴ * V * (Vᴴ * K * V) = Vᴴ * Kᴴ * (V * Vᴴ) * K * V := by
          simp only [Matrix.mul_assoc]
      _ = Vᴴ * (Kᴴ * K) * V := by
          rw [hV2]; simp only [Matrix.mul_one, Matrix.mul_assoc]
      _ = 1 := by rw [h1, Matrix.mul_one, hV1]
  have hent : star (D a a) * D a a = 1 := by
    have h := congrFun (congrFun hDD a) a
    rw [Matrix.mul_apply, Finset.sum_eq_single a] at h
    · simpa [Matrix.conjTranspose_apply] using h
    · intro b _ hb
      have : D b a = 0 := hDd hb
      simp [this]
    · simp
  have hn : ‖D a a‖ ^ 2 = 1 := by
    have h3 : ((‖D a a‖ ^ 2 : ℝ) : ℂ) = 1 := by
      have := Complex.conj_mul' (D a a)
      push_cast
      rw [← this]
      simpa using hent
    exact_mod_cast h3
  have h0 : 0 ≤ ‖D a a‖ := norm_nonneg _
  show ‖D a a‖ = 1
  nlinarith [sq_nonneg (‖D a a‖ - 1), sq_nonneg (‖D a a‖ + 1)]

theorem exists_skew_exp_eq (n : ℕ) (k : Matrix.unitaryGroup (Fin n) ℂ) :
    ∃ X : Mat n, Xᴴ = -X ∧ uG k = expG X 1 := by
  classical
  have h1 : (k : Matrix (Fin n) (Fin n) ℂ)ᴴ * (k : Matrix (Fin n) (Fin n) ℂ) = 1 :=
    Matrix.mem_unitaryGroup_iff'.1 k.2
  have h2 : (k : Matrix (Fin n) (Fin n) ℂ) * (k : Matrix (Fin n) (Fin n) ℂ)ᴴ = 1 :=
    Matrix.mem_unitaryGroup_iff.1 k.2
  obtain ⟨V, z, hV1, hV2, hD, hz⟩ := exists_unitary_diag _ h1 h2
  set w : Fin n → ℂ := fun a => (Complex.arg (z a) : ℂ) * Complex.I with hw
  have hexp : ∀ a, NormedSpace.exp (w a) = z a := by
    intro a
    have := Complex.norm_mul_exp_arg_mul_I (z a)
    rw [hz a] at this
    simpa [hw, Complex.exp_eq_exp_ℂ] using this
  have hk : (k : Matrix (Fin n) (Fin n) ℂ) = V * Matrix.diagonal z * Vᴴ := by
    rw [← hD]
    calc (k : Matrix (Fin n) (Fin n) ℂ)
        = (V * Vᴴ) * (k : Matrix (Fin n) (Fin n) ℂ) * (V * Vᴴ) := by
          rw [hV2]; simp
      _ = V * (Vᴴ * (k : Matrix (Fin n) (Fin n) ℂ) * V) * Vᴴ := by
          simp only [Matrix.mul_assoc]
  refine ⟨V * Matrix.diagonal w * Vᴴ, ?_, ?_⟩
  · have hs : star w = -w := by
      funext a
      simp [hw]
    simp only [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose,
      Matrix.diagonal_conjTranspose, hs, Matrix.mul_assoc]
    have hn : Matrix.diagonal (-w) = -Matrix.diagonal w := (Matrix.diagonal_neg w).symm
    rw [hn, Matrix.neg_mul, Matrix.mul_neg]
  · refine Units.ext ?_
    let Vu : (Matrix (Fin n) (Fin n) ℂ)ˣ := ⟨V, Vᴴ, hV2, hV1⟩
    have e := Matrix.exp_units_conj Vu (Matrix.diagonal w)
    have e2 : NormedSpace.exp (Matrix.diagonal w) = Matrix.diagonal z := by
      rw [Matrix.exp_diagonal]
      congr 1
      funext a
      rw [Pi.exp_def]
      exact hexp a
    rw [e2] at e
    have e3 : ((expG (V * Matrix.diagonal w * Vᴴ) 1 : G n) : Mat n) =
        NormedSpace.exp (V * Matrix.diagonal w * Vᴴ) := by
      delta expG
      simp only [IsUnit.unit_spec, Complex.ofReal_one, one_smul]
    rw [e3]
    exact hk.trans e.symm

end GlobalTheory.CompanionTheory.UnitaryExp
end

