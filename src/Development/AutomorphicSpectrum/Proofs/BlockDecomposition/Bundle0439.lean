module

public import Mathlib
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ThetaNormCommutation.LocalComparisonSplitting.EulerFactorLevels.EulerFinOf
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsMulCommutativeCentRealUJ
public import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.CapelliComplements.Bundle0001
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0385
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0412

@[expose] public section

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FiniteMassProductFormula
section
noncomputable section

open GlobalTheory.BCT

namespace GlobalTheory.CompanionTheory.MassProd

section Cards

variable {A B C : Type} [Group A] [Group B] [Group C]

theorem card_doubleCoset (e : C ≃* A × B) (H K : Subgroup A) (H' K' : Subgroup B) (H'' K'' : Subgroup C)
    (hH : ∀ c, c ∈ H'' ↔ (e c).1 ∈ H ∧ (e c).2 ∈ H') (hK : ∀ c, c ∈ K'' ↔ (e c).1 ∈ K ∧ (e c).2 ∈ K') :
    Nat.card (DoubleCoset.Quotient (H'' : Set C) (K'' : Set C)) =
      Nat.card (DoubleCoset.Quotient (H : Set A) (K : Set A)) *
        Nat.card (DoubleCoset.Quotient (H' : Set B) (K' : Set B)) := by
  rw [← Nat.card_prod]
  apply Nat.card_congr
  let F : C → DoubleCoset.Quotient (H : Set A) (K : Set A) × DoubleCoset.Quotient (H' : Set B) (K' : Set B) :=
    fun c => (DoubleCoset.mk H K (e c).1, DoubleCoset.mk H' K' (e c).2)
  have hF : ∀ x y : C, F x = F y ↔ DoubleCoset.mk H'' K'' x = DoubleCoset.mk H'' K'' y := by
    intro x y
    simp only [F, Prod.mk.injEq, DoubleCoset.eq]
    constructor
    · rintro ⟨⟨h, hh, k, hk, h1⟩, h', hh', k', hk', h2⟩
      refine ⟨e.symm (h, h'), ?_, e.symm (k, k'), ?_, ?_⟩
      · rw [hH]; simpa using ⟨hh, hh'⟩
      · rw [hK]; simpa using ⟨hk, hk'⟩
      · apply e.injective
        simp only [map_mul, MulEquiv.apply_symm_apply]
        exact Prod.ext (by simpa using h1) (by simpa using h2)
    · rintro ⟨h, hh, k, hk, rfl⟩
      rw [hH] at hh
      rw [hK] at hk
      exact ⟨⟨_, hh.1, _, hk.1, by simp⟩, _, hh.2, _, hk.2, by simp⟩
  refine Equiv.ofBijective (Quotient.lift F fun x y h => (hF x y).2 (Quotient.sound h)) ⟨?_, ?_⟩
  · intro p q
    induction p using Quotient.inductionOn with | _ x => ?_
    induction q using Quotient.inductionOn with | _ y => ?_
    intro h
    exact (hF x y).1 h
  · rintro ⟨p, q⟩
    induction p using Quotient.inductionOn with | _ x => ?_
    induction q using Quotient.inductionOn with | _ y => ?_
    refine ⟨DoubleCoset.mk H'' K'' (e.symm (x, y)), ?_⟩
    show F (e.symm (x, y)) = _
    simp [F]

end Cards

section Top

variable {G G' : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [Group G'] [TopologicalSpace G']
  [IsTopologicalGroup G']

theorem twCent_prodMap (θ : G →* G) (θ' : G' →* G') (δ : G) (δ' : G') :
    twCent (θ.prodMap θ') (δ, δ') = (twCent θ δ).prod (twCent θ' δ') := by
  ext ⟨a, b⟩
  show (a, b) * (δ, δ') = (δ, δ') * (θ a, θ' b) ↔ a * δ = δ * θ a ∧ b * δ' = δ' * θ' b
  simp [Prod.ext_iff]

theorem compactPowers_prod (a : G) (b : G') :
    IsCompact (closure (Subgroup.zpowers ((a, b) : G × G') : Set (G × G'))) ↔
      IsCompact (closure (Subgroup.zpowers a : Set G)) ∧ IsCompact (closure (Subgroup.zpowers b : Set G')) := by
  constructor
  · intro h
    constructor
    · refine (h.image continuous_fst).closure_of_subset ?_
      rintro _ ⟨n, rfl⟩
      exact ⟨(a, b) ^ n, subset_closure ⟨n, rfl⟩, by simp⟩
    · refine (h.image continuous_snd).closure_of_subset ?_
      rintro _ ⟨n, rfl⟩
      exact ⟨(a, b) ^ n, subset_closure ⟨n, rfl⟩, by simp⟩
  · rintro ⟨h, h'⟩
    refine (h.prod h').closure_of_subset ?_
    rintro _ ⟨n, rfl⟩
    exact ⟨subset_closure ⟨n, by simp⟩, subset_closure ⟨n, by simp⟩⟩

theorem cptPart_prod (T : Subgroup G) (T' : Subgroup G') :
    cptPart (T.prod T') = (cptPart T).prod (cptPart T') := by
  have h1 : ∀ {X : Type} [Group X] [TopologicalSpace X] [IsTopologicalGroup X],
      IsCompact (closure (Subgroup.zpowers (1 : X) : Set X)) := by
    intro X _ _ _
    simpa using (isCompact_singleton (x := (1 : X))).closure
  unfold cptPart
  have hs : (1 : G) ∈ {t | t ∈ T ∧ IsCompact (closure (Subgroup.zpowers t : Set G))} := ⟨T.one_mem, h1⟩
  have hs' : (1 : G') ∈ {t | t ∈ T' ∧ IsCompact (closure (Subgroup.zpowers t : Set G'))} := ⟨T'.one_mem, h1⟩
  rw [← Subgroup.closure_prod hs hs']
  congr 1
  ext ⟨a, b⟩
  simp only [Set.mem_setOf_eq, Set.mem_prod, compactPowers_prod, Subgroup.mem_prod]
  tauto

theorem card_inf_prod (Γ C : Subgroup G) (Γ' C' : Subgroup G') :
    Nat.card (Γ.prod Γ' ⊓ C.prod C' : Subgroup (G × G')) =
      Nat.card (Γ ⊓ C : Subgroup G) * Nat.card (Γ' ⊓ C' : Subgroup G') := by
  have h : Γ.prod Γ' ⊓ C.prod C' = (Γ ⊓ C).prod (Γ' ⊓ C') := by
    ext ⟨a, b⟩
    simp only [Subgroup.mem_inf, Subgroup.mem_prod]
    tauto
  rw [h, ← Nat.card_prod]
  exact Nat.card_congr (Subgroup.prodEquiv _ _).toEquiv

end Top

theorem massProd : PositivityTheory.Rg.BcB.G8.Fin.MassProd := by
  intro G G' _ _ _ _ _ _ θ θ' Γ Γ' δ δ'
  unfold mass
  rw [twCent_prodMap, cptPart_prod, card_inf_prod]
  rw [card_doubleCoset (Subgroup.prodEquiv (twCent θ δ) (twCent θ' δ'))
    (Γ.subgroupOf (twCent θ δ)) ((cptPart (twCent θ δ)).subgroupOf (twCent θ δ))
    (Γ'.subgroupOf (twCent θ' δ')) ((cptPart (twCent θ' δ')).subgroupOf (twCent θ' δ'))
    _ _ (fun c => by simp only [Subgroup.mem_subgroupOf, Subgroup.mem_prod]; exact Iff.rfl)
    (fun c => by simp only [Subgroup.mem_subgroupOf, Subgroup.mem_prod]; exact Iff.rfl)]
  push_cast
  rw [mul_div_mul_comm]

end GlobalTheory.CompanionTheory.MassProd

end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FiniteTorsionCentralizer
section
open NumberField IsDedekindDomain Matrix Polynomial Filter
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical
open scoped ComplexOrder

namespace GlobalTheory.CompanionTheory.TorCent

theorem finite_roots_of_unity (M : Type) [Field M] [NumberField M] :
    {ζ : M | ∃ k : ℕ, 0 < k ∧ ζ ^ k = 1}.Finite := by
  refine (NumberField.Embeddings.finite_of_norm_le M ℂ 1).subset ?_
  rintro ζ ⟨k, hk, h⟩
  refine ⟨IsIntegral.of_pow hk (by rw [h]; exact isIntegral_one), fun φ => ?_⟩
  have h1 : (φ ζ) ^ k = 1 := by rw [← map_pow, h, map_one]
  exact (Complex.norm_eq_one_of_pow_eq_one h1 hk.ne').le

theorem exists_distinct_roots {M : Type} [Field M] {n : ℕ} (A : Matrix (Fin n) (Fin n) M)
    (hs : A.charpoly.Separable) (hsp : A.charpoly.Splits) :
    ∃ z : Fin n → M, Function.Injective z ∧ A.charpoly = ∏ a, (X - C (z a)) := by
  have hnd : A.charpoly.roots.Nodup := nodup_roots hs
  have hcard := splits_iff_card_roots.1 hsp
  have hdeg : A.charpoly.natDegree = n := by
    rw [charpoly_natDegree_eq_dim, Fintype.card_fin]
  set s := A.charpoly.roots.toFinset with hs_def
  have hsc : Fintype.card s = n := by
    rw [Fintype.card_coe, Multiset.toFinset_card_of_nodup hnd, hcard, hdeg]
  let e := Fintype.equivFinOfCardEq hsc
  refine ⟨fun a => ((e.symm a : s) : M), Subtype.val_injective.comp e.symm.injective, ?_⟩
  rw [Equiv.prod_comp e.symm (fun r : s => X - C (r : M)), Finset.prod_coe_sort s (fun r => X - C r),
    Finset.prod_eq_multiset_prod, hs_def, Multiset.toFinset_val, Multiset.dedup_eq_self.2 hnd,
    prod_multiset_X_sub_C_of_monic_of_roots_card_eq (charpoly_monic _) hcard]

theorem eq_diagonal_of_commute {M : Type} [Field M] {n : ℕ} {z : Fin n → M}
    (hz : Function.Injective z) {F : Matrix (Fin n) (Fin n) M}
    (h : F * diagonal z = diagonal z * F) : F = diagonal fun i => F i i := by
  ext i j
  by_cases hij : i = j
  · subst hij; simp
  · have h1 := congrFun (congrFun h i) j
    rw [mul_diagonal, diagonal_mul] at h1
    rw [diagonal_apply_ne _ hij]
    have h2 : F i j * (z j - z i) = 0 := by rw [mul_sub, h1]; ring
    exact (mul_eq_zero.1 h2).resolve_right (sub_ne_zero.2 fun e => hij (hz e.symm))

theorem finite_torsion_centralizer : ∀ (E : Type) [Field E] [NumberField E] (n : ℕ) (N : GL (Fin n) E), N.val.charpoly.Separable →
  {g : GL (Fin n) E | g * N = N * g ∧ IsOfFinOrder g}.Finite := by
  intro E _ _ n N hsep
  let M := N.val.charpoly.SplittingField
  haveI : NumberField M := NumberField.of_module_finite E M
  let f : E →+* M := algebraMap E M
  let A : Matrix (Fin n) (Fin n) M := N.val.map f
  have hA : A.charpoly = N.val.charpoly.map f := charpoly_map _ _
  have hs : A.charpoly.Separable := by rw [hA]; exact hsep.map
  have hsp : A.charpoly.Splits := by rw [hA]; exact SplittingField.splits _
  obtain ⟨z, hz, hprod⟩ := exists_distinct_roots A hs hsp
  obtain ⟨x, hx⟩ := GlobalTheory.Orb.IsRegSS.exists_conj (M := A) (N := diagonal z) hs
    (by rw [charpoly_diagonal, hprod])
  let B : Matrix (Fin n) (Fin n) M := x.val
  let Bi : Matrix (Fin n) (Fin n) M := (x⁻¹).val
  have hBB : B * Bi = 1 := by simp [B, Bi]
  have hBB' : Bi * B = 1 := by simp [B, Bi]
  have hx' : diagonal z * B = B * A := hx
  have hx2 : Bi * diagonal z = A * Bi := by
    calc Bi * diagonal z = Bi * (diagonal z * B) * Bi := by
          rw [Matrix.mul_assoc, Matrix.mul_assoc, hBB, Matrix.mul_one]
      _ = A * Bi := by rw [hx', ← Matrix.mul_assoc, hBB', Matrix.one_mul]
  let F : GL (Fin n) E → Matrix (Fin n) (Fin n) M := fun g => B * g.val.map f * Bi
  have hFc : ∀ g : GL (Fin n) E, g * N = N * g → F g * diagonal z = diagonal z * F g := by
    intro g hg
    have h1 : g.val * N.val = N.val * g.val := congrArg Units.val hg
    have h2 : g.val.map f * A = A * g.val.map f := by
      simp only [A]
      rw [← Matrix.map_mul, ← Matrix.map_mul, h1]
    simp only [F]
    calc B * g.val.map f * Bi * diagonal z = B * (g.val.map f * A) * Bi := by
          rw [Matrix.mul_assoc, hx2, Matrix.mul_assoc, Matrix.mul_assoc, Matrix.mul_assoc]
      _ = diagonal z * (B * g.val.map f * Bi) := by
          rw [h2, ← Matrix.mul_assoc, ← Matrix.mul_assoc, ← hx', Matrix.mul_assoc, Matrix.mul_assoc,
            Matrix.mul_assoc, Matrix.mul_assoc]
  have hFpow : ∀ (g : GL (Fin n) E) (k : ℕ), F g ^ k = F (g ^ k) := by
    intro g k
    induction k with
    | zero => simp [F, hBB, Matrix.map_one, Matrix.mul_one]
    | succ k ih =>
      rw [pow_succ, ih, pow_succ]
      simp only [F, Units.val_mul]
      rw [Matrix.map_mul]
      calc B * (g ^ k).val.map f * Bi * (B * g.val.map f * Bi)
          = B * (g ^ k).val.map f * (Bi * B) * g.val.map f * Bi := by
            simp only [Matrix.mul_assoc]
        _ = _ := by rw [hBB', Matrix.mul_one]; simp only [Matrix.mul_assoc]
  let φ : GL (Fin n) E → Fin n → M := fun g i => F g i i
  have hfin := Set.Finite.pi' fun _ : Fin n => finite_roots_of_unity M
  refine Set.Finite.of_injOn (f := φ) ?_ ?_ hfin
  · rintro g ⟨hg, ho⟩ i
    obtain ⟨k, hk, hgk⟩ := isOfFinOrder_iff_pow_eq_one.1 ho
    refine ⟨k, hk, ?_⟩
    have h1 : F g ^ k = 1 := by
      rw [hFpow, hgk]; simp [F, hBB, Matrix.map_one]
    rw [eq_diagonal_of_commute hz (hFc g hg), diagonal_pow] at h1
    have h2 := congrFun (congrFun h1 i) i
    simpa [φ] using h2
  · rintro g ⟨hg, -⟩ g' ⟨hg', -⟩ e
    have h1 : F g = F g' := by
      rw [eq_diagonal_of_commute hz (hFc g hg), eq_diagonal_of_commute hz (hFc g' hg')]
      exact congrArg diagonal e
    have h2 : g.val.map f = g'.val.map f := by
      have h3 : Bi * F g * B = Bi * F g' * B := by rw [h1]
      have h4 : ∀ Y : Matrix (Fin n) (Fin n) M, Bi * (B * Y * Bi) * B = Y := fun Y => by
        calc Bi * (B * Y * Bi) * B = (Bi * B) * Y * (Bi * B) := by simp only [Matrix.mul_assoc]
          _ = Y := by rw [hBB', Matrix.one_mul, Matrix.mul_one]
      simpa only [F, h4] using h3
    refine Units.ext ?_
    ext i j
    exact f.injective (congrFun (congrFun h2 i) j)

end GlobalTheory.CompanionTheory.TorCent
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FiniteTorsionLatticeCompact
section
open NumberField IsDedekindDomain Matrix Polynomial Filter
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical
open scoped ComplexOrder

namespace GlobalTheory.CompanionTheory.CountClosedComm

theorem relIndex_ne_zero_of_cover {G : Type} [Group G] (M W : Subgroup G) (S : Set G) (hS : S.Finite)
    (h : ∀ w ∈ W, ∃ s ∈ S, s⁻¹ * w ∈ M) : M.relIndex W ≠ 0 := by
  have hfin : Finite S := hS.to_subtype
  choose φ hφ hφM using h
  let ψ : W ⧸ M.subgroupOf W → S := fun q => ⟨φ q.out q.out.2, hφ _ q.out.2⟩
  have hinj : Function.Injective ψ := by
    intro q q' hqq
    have e : φ q.out q.out.2 = φ q'.out q'.out.2 := congrArg Subtype.val hqq
    have a := hφM _ q.out.2
    have b := hφM _ q'.out.2
    rw [← e] at b
    have hm : (q.out)⁻¹ * q'.out ∈ M.subgroupOf W := by
      rw [Subgroup.mem_subgroupOf]
      have := M.mul_mem (M.inv_mem a) b
      simpa [mul_assoc] using this
    calc q = QuotientGroup.mk q.out := (QuotientGroup.out_eq' q).symm
      _ = QuotientGroup.mk q'.out := QuotientGroup.eq.2 hm
      _ = q' := QuotientGroup.out_eq' q'
  have : Finite (W ⧸ M.subgroupOf W) := Finite.of_injective ψ hinj
  exact Subgroup.index_ne_zero_of_finite

theorem exists_pow_mem {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] (L : Subgroup G)
    (hL : IsOpen (L : Set G)) (t : G) (hc : IsCompact (closure (Subgroup.zpowers t : Set G))) :
    ∃ k : ℕ, 0 < k ∧ t ^ k ∈ L :=
  _root_.Bl.FirstLemmaC.goal1 L hL t hc

theorem cover_cosets {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    (L T Γ : Subgroup G) (C : Set G) (hLo : IsOpen (L : Set G)) (hTc : IsClosed (T : Set G)) (hΓ : Γ ≤ T)
    (hC : IsCompact C) (hcov : ∀ t ∈ T, ∃ γ ∈ Γ, ∃ c ∈ C, t = γ * c) :
    ∃ F : Finset G, (∀ f ∈ F, f ∈ T) ∧ ∀ t ∈ T, ∃ γ ∈ Γ, ∃ f ∈ F, ∃ m ∈ T ⊓ L, t = γ * f * m := by
  have hTC : IsCompact ((T : Set G) ∩ C) := hC.inter_left hTc
  obtain ⟨F, hF, hU⟩ := hTC.elim_nhds_subcover (fun z => {g | z⁻¹ * g ∈ (L : Set G)}) (fun z _ =>
    IsOpen.mem_nhds (hLo.preimage (continuous_const.mul continuous_id)) (by simp [L.one_mem]))
  refine ⟨F, fun f hf => (hF f hf).1, ?_⟩
  intro t ht
  obtain ⟨γ, hγ, c, hc, rfl⟩ := hcov t ht
  have hcT : c ∈ T := by
    have := T.mul_mem (T.inv_mem (hΓ hγ)) ht
    simpa using this
  obtain ⟨f, hf, hcf⟩ := Set.mem_iUnion₂.1 (hU ⟨hcT, hc⟩)
  exact ⟨γ, hγ, f, hf, f⁻¹ * c, ⟨T.mul_mem (T.inv_mem (hF f hf).1) hcT, hcf⟩, by group⟩

def powRad {G : Type} [Group G] (T M : Subgroup G) (hcomm : ∀ a ∈ T, ∀ b ∈ T, a * b = b * a) : Subgroup G where
  carrier := {t | t ∈ T ∧ ∃ k : ℕ, 0 < k ∧ t ^ k ∈ M}
  mul_mem' := by
    rintro a b ⟨ha, k, hk, hak⟩ ⟨hb, l, hl, hbl⟩
    refine ⟨T.mul_mem ha hb, k * l, Nat.mul_pos hk hl, ?_⟩
    have hc : Commute a b := hcomm a ha b hb
    rw [hc.mul_pow, pow_mul a, pow_mul' b]
    exact M.mul_mem (M.pow_mem hak _) (M.pow_mem hbl _)
  one_mem' := ⟨T.one_mem, 1, one_pos, by simp [M.one_mem]⟩
  inv_mem' := by
    rintro a ⟨ha, k, hk, hak⟩
    exact ⟨T.inv_mem ha, k, hk, by rw [inv_pow]; exact M.inv_mem hak⟩

theorem le_powRad {G : Type} [Group G] (T M : Subgroup G) (hcomm : ∀ a ∈ T, ∀ b ∈ T, a * b = b * a)
    (hM : M ≤ T) : M ≤ powRad T M hcomm :=
  fun m hm => ⟨hM hm, 1, one_pos, by simpa using hm⟩

theorem cptPart_le_powRad {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    (T L : Subgroup G) (hcomm : ∀ a ∈ T, ∀ b ∈ T, a * b = b * a) (hLo : IsOpen (L : Set G)) :
    cptPart T ≤ powRad T (T ⊓ L) hcomm := by
  rw [cptPart, Subgroup.closure_le]
  rintro t ⟨ht, hc⟩
  obtain ⟨k, hk, hkL⟩ := exists_pow_mem L hLo t hc
  exact ⟨ht, k, hk, T.pow_mem ht k, hkL⟩

theorem inf_le_cptPart' {G : Type} [Group G] [TopologicalSpace G] [T2Space G] (T L : Subgroup G)
    (hL : IsCompact (L : Set G)) : T ⊓ L ≤ cptPart T := by
  intro t ht
  apply Subgroup.subset_closure
  refine ⟨ht.1, hL.of_isClosed_subset isClosed_closure ?_⟩
  exact closure_minimal (fun x hx => (Subgroup.zpowers_le.2 ht.2) hx) hL.isClosed

theorem isOfFinOrder_of_pow_mem {G : Type} [Group G] (Γ M : Subgroup G)
    (hfin : ((Γ : Set G) ∩ (M : Set G)).Finite) (γ : G) (hγ : γ ∈ Γ) (k : ℕ) (hk : 0 < k) (hkM : γ ^ k ∈ M) :
    IsOfFinOrder γ := by
  have h : IsOfFinOrder (γ ^ k) := by
    rw [← finite_powers]
    refine hfin.subset ?_
    rintro _ ⟨n, rfl⟩
    exact ⟨Γ.pow_mem (Γ.pow_mem hγ k) n, M.pow_mem hkM n⟩
  exact h.of_pow hk.ne'

theorem relIndex_ne_zero_of_torsion {G : Type} [Group G] (T M W Γ : Subgroup G)
    (hcomm : ∀ a ∈ T, ∀ b ∈ T, a * b = b * a) (hMT : M ≤ T) (hMW : M ≤ W) (hΓ : Γ ≤ T)
    (F : Finset G) (hF : ∀ f ∈ F, f ∈ T) (hWT : W ≤ T)
    (hcov : ∀ t ∈ T, ∃ γ ∈ Γ, ∃ f ∈ F, ∃ m ∈ M, t = γ * f * m)
    (Tor : Set G) (hTor : Tor.Finite) (hsub : ∀ σ ∈ Γ, σ ∈ W → σ ∈ Tor) : M.relIndex W ≠ 0 := by
  have hr : ∀ f : G, ∃ r : G, (∃ t ∈ W, ∃ γ ∈ Γ, ∃ m ∈ M, t = γ * f * m) →
      r ∈ W ∧ ∃ γ ∈ Γ, ∃ m ∈ M, r = γ * f * m := by
    intro f
    by_cases h : ∃ t ∈ W, ∃ γ ∈ Γ, ∃ m ∈ M, t = γ * f * m
    · obtain ⟨t, ht, hh⟩ := h
      exact ⟨t, fun _ => ⟨ht, hh⟩⟩
    · exact ⟨1, fun h' => absurd h' h⟩
  choose r hr using hr
  refine relIndex_ne_zero_of_cover M W (Set.image2 (fun f σ => r f * σ) (F : Set G) Tor)
    (Set.Finite.image2 _ F.finite_toSet hTor) ?_
  intro w hw
  obtain ⟨a, ha, f, hf, c, hc, rfl⟩ := hcov w (hWT hw)
  obtain ⟨hrW, d, hd, e, he, hrf⟩ := hr f ⟨_, hw, a, ha, c, hc, rfl⟩
  have hσT : d⁻¹ * a ∈ T := T.mul_mem (T.inv_mem (hΓ hd)) (hΓ ha)
  have hσΓ : d⁻¹ * a ∈ Γ := Γ.mul_mem (Γ.inv_mem hd) ha
  have h1 : (r f)⁻¹ * (a * f * c) = e⁻¹ * (d⁻¹ * a) * c := by
    have hb : f * (d⁻¹ * a) = (d⁻¹ * a) * f := hcomm _ (hF f hf) _ hσT
    have hb' : f⁻¹ * (d⁻¹ * a) * f = d⁻¹ * a := by rw [mul_assoc, ← hb]; group
    rw [hrf]
    calc (d * f * e)⁻¹ * (a * f * c) = e⁻¹ * (f⁻¹ * (d⁻¹ * a) * f) * c := by group
      _ = e⁻¹ * (d⁻¹ * a) * c := by rw [hb']
  have hσW : d⁻¹ * a ∈ W := by
    have h2 : d⁻¹ * a = e * ((r f)⁻¹ * (a * f * c)) * c⁻¹ := by rw [h1]; group
    rw [h2]
    exact W.mul_mem (W.mul_mem (hMW he) (W.mul_mem (W.inv_mem hrW) hw)) (W.inv_mem (hMW hc))
  refine ⟨r f * (d⁻¹ * a), ⟨f, hf, d⁻¹ * a, hsub _ hσΓ hσW, rfl⟩, ?_⟩
  have hcm : e⁻¹ * (d⁻¹ * a) = (d⁻¹ * a) * e⁻¹ := hcomm _ (T.inv_mem (hMT he)) _ hσT
  have h3 : (r f * (d⁻¹ * a))⁻¹ * (a * f * c) = e⁻¹ * c := by
    rw [_root_.mul_inv_rev, mul_assoc, h1, hcm]
    group
  rw [h3]
  exact M.mul_mem (M.inv_mem he) hc

theorem isCompact_inf {G : Type} [Group G] [TopologicalSpace G] [T2Space G] (T L : Subgroup G)
    (hTc : IsClosed (T : Set G)) (hL : IsCompact (L : Set G)) : IsCompact ((T ⊓ L : Subgroup G) : Set G) := by
  rw [Subgroup.coe_inf]
  exact hL.inter_left hTc

theorem part {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [T2Space G] (L T Γ : Subgroup G)
    (C : Set G) (hLo : IsOpen (L : Set G)) (hLc : IsCompact (L : Set G)) (hTc : IsClosed (T : Set G))
    (hcomm : ∀ a ∈ T, ∀ b ∈ T, a * b = b * a) (hΓ : Γ ≤ T) (hC : IsCompact C)
    (hcov : ∀ t ∈ T, ∃ γ ∈ Γ, ∃ c ∈ C, t = γ * c)
    (hfin : ∀ X : Set G, IsCompact X → ((Γ : Set G) ∩ X).Finite) (htor : {γ : G | γ ∈ Γ ∧ IsOfFinOrder γ}.Finite) :
    (T ⊓ L).relIndex (cptPart T) ≠ 0 ∧ Finite (Γ ⊓ cptPart T : Subgroup G) := by
  set M := T ⊓ L with hM
  have hMT : M ≤ T := inf_le_left
  have hsub : ∀ σ ∈ Γ, σ ∈ powRad T M hcomm → σ ∈ {γ : G | γ ∈ Γ ∧ IsOfFinOrder γ} := by
    rintro σ hσ ⟨-, k, hk, hkM⟩
    exact ⟨hσ, isOfFinOrder_of_pow_mem Γ M (hfin _ (isCompact_inf T L hTc hLc)) σ hσ k hk hkM⟩
  have hle : cptPart T ≤ powRad T M hcomm := cptPart_le_powRad T L hcomm hLo
  obtain ⟨F, hF, hcovF⟩ := cover_cosets L T Γ C hLo hTc hΓ hC hcov
  refine ⟨?_, ?_⟩
  · have hW : M.relIndex (powRad T M hcomm) ≠ 0 :=
      relIndex_ne_zero_of_torsion T M (powRad T M hcomm) Γ hcomm hMT (le_powRad T M hcomm hMT) hΓ F hF
        (fun _ h => h.1) hcovF _ htor hsub
    exact fun h0 => hW (Subgroup.relIndex_eq_zero_of_le_right hle h0)
  · have : ((Γ ⊓ cptPart T : Subgroup G) : Set G).Finite :=
      htor.subset fun σ hσ => hsub σ hσ.1 (hle hσ.2)
    exact this.to_subtype

theorem finite_doubleCoset {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [T2Space G]
    (L T Γ : Subgroup G) (C : Set G) (hLo : IsOpen (L : Set G)) (hLc : IsCompact (L : Set G))
    (hTc : IsClosed (T : Set G)) (hΓ : Γ ≤ T) (hC : IsCompact C)
    (hcov : ∀ t ∈ T, ∃ γ ∈ Γ, ∃ c ∈ C, t = γ * c) :
    Finite (DoubleCoset.Quotient (((Γ.subgroupOf T) : Subgroup T) : Set T)
      (((cptPart T).subgroupOf T : Subgroup T) : Set T)) := by
  obtain ⟨F, hF, hcovF⟩ := cover_cosets L T Γ C hLo hTc hΓ hC hcov
  let φ : F → DoubleCoset.Quotient (((Γ.subgroupOf T) : Subgroup T) : Set T)
      (((cptPart T).subgroupOf T : Subgroup T) : Set T) :=
    fun f => DoubleCoset.mk _ _ ⟨f.1, hF f.1 f.2⟩
  refine Finite.of_surjective φ fun q => ?_
  induction q using Quotient.inductionOn' with
  | h t =>
    obtain ⟨γ, hγ, f, hf, m, hm, ht⟩ := hcovF t.1 t.2
    refine ⟨⟨f, hf⟩, ?_⟩
    refine Quotient.sound' ?_
    rw [DoubleCoset.rel_iff]
    refine ⟨⟨γ, hΓ hγ⟩, ?_, ⟨m, hm.1⟩, ?_, ?_⟩
    · exact Subgroup.mem_subgroupOf.2 hγ
    · exact Subgroup.mem_subgroupOf.2 (inf_le_cptPart' T L hLc hm)
    · apply Subtype.ext
      simp [ht, mul_assoc]

theorem main : ∀ (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [T2Space G] (K T Γ : Subgroup G) (C : Set G),
  IsOpen (K : Set G) → IsCompact (K : Set G) → IsClosed (T : Set G) → (∀ a ∈ T, ∀ b ∈ T, a * b = b * a) → Γ ≤ T →
  IsCompact C → (∀ t ∈ T, ∃ γ ∈ Γ, ∃ c ∈ C, t = γ * c) →
  (∀ X : Set G, IsCompact X → ((Γ : Set G) ∩ X).Finite) → {γ : G | γ ∈ Γ ∧ IsOfFinOrder γ}.Finite →
  (∀ x : G, T ⊓ K.map (MulAut.conj x).toMonoidHom ≤ cptPart T ∧
    (T ⊓ K.map (MulAut.conj x).toMonoidHom).relIndex (cptPart T) ≠ 0) ∧
  (∀ x : G, Finite (Γ ⊓ K.map (MulAut.conj x).toMonoidHom : Subgroup G)) ∧
  Finite (Γ ⊓ cptPart T : Subgroup G) ∧
  Finite (DoubleCoset.Quotient (((Γ.subgroupOf T) : Subgroup T) : Set T) (((cptPart T).subgroupOf T : Subgroup T) : Set T)) := by
  intro G _ _ _ _ K T Γ C hKo hKc hTc hcomm hΓ hC hcov hfin htor
  have hLo : ∀ x : G, IsOpen ((K.map (MulAut.conj x).toMonoidHom : Subgroup G) : Set G) := by
    intro x
    have : ((K.map (MulAut.conj x).toMonoidHom : Subgroup G) : Set G) = (Homeomorph.mulRight x⁻¹ ∘ Homeomorph.mulLeft x) '' (K : Set G) := by
      ext g; simp [MulAut.conj_apply]
    rw [this, Set.image_comp]
    exact (Homeomorph.mulRight x⁻¹).isOpenMap _ ((Homeomorph.mulLeft x).isOpenMap _ hKo)
  have hLc : ∀ x : G, IsCompact ((K.map (MulAut.conj x).toMonoidHom : Subgroup G) : Set G) := by
    intro x
    have : ((K.map (MulAut.conj x).toMonoidHom : Subgroup G) : Set G) = (fun g => x * g * x⁻¹) '' (K : Set G) := by
      ext g; simp [MulAut.conj_apply]
    rw [this]
    exact hKc.image (by fun_prop)
  refine ⟨fun x => ⟨inf_le_cptPart' T _ (hLc x), (part _ T Γ C (hLo x) (hLc x) hTc hcomm hΓ hC hcov hfin htor).1⟩,
    fun x => ?_, (part K T Γ C hKo hKc hTc hcomm hΓ hC hcov hfin htor).2,
    finite_doubleCoset K T Γ C hKo hKc hTc hΓ hC hcov⟩
  have : ((Γ ⊓ K.map (MulAut.conj x).toMonoidHom : Subgroup G) : Set G).Finite := by
    rw [Subgroup.coe_inf]
    exact hfin _ (hLc x)
  exact this.to_subtype

end GlobalTheory.CompanionTheory.CountClosedComm
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IntegralMulVecChangeModulus
section
noncomputable section

open Matrix GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.BZMir GlobalTheory.BZMir.Leib GlobalTheory.RgGu.Leib GlobalTheory.CompanionTheory.BZPhiPG
open scoped TensorProduct

namespace GlobalTheory.CompanionTheory.BZPhiPG.Scale

theorem smInt_subst : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (n : ℕ) (W : Type) [AddCommGroup W] [Module ℂ W] (w : GL (Fin n) k) (F : (Fin n → k) → W),
    IsLocallyConstant F → HasCompactSupport F →
    @GlobalTheory.CompanionTheory.Rodier.smInt _ _ (borel _) _ _ (muD k n) (fun d => F ((w⁻¹ : GL (Fin n) k).1.mulVec d)) =
      ((dpow n 1 w : ℂˣ) : ℂ) • @GlobalTheory.CompanionTheory.Rodier.smInt _ _ (borel _) _ _ (muD k n) F := by
  intro k _ _ _ _ n W _ _ w F l c
  exact smInt_mulVec k n W w F l c

end GlobalTheory.CompanionTheory.BZPhiPG.Scale

end
end

