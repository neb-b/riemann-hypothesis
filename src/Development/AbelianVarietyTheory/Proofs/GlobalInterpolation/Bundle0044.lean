module

public import Mathlib
public import Formalism.LocalRingCardinality.RankBoundMonotoneInDimension
public import Development.AbelianVarietyTheory.BlockTheory.GlobalSignature.Bundle0007
public import Formalism.SharpRestriction.LevelLetterCocycles.DataN
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0037
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0043
public import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.IsDiscriminantTwelfthRootOfIdealLattice
public import Formalism.LocalRingCardinality.DataLatDefs

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.CosetGroupEquiv
section
noncomputable section

namespace GlobalTheory.Proof.CosetGroupEquiv

open NumberField IsDedekindDomain Formalism.UG Formalism.BasicNotions Formalism.L2.Herm
open scoped TensorProduct
open GlobalTheory.IndefiniteRowSideFullHecke

section Abstract

variable {G : Type} [Group G]

def cosetGrpEquiv (Γ K : Subgroup G) (y : G) : CosetGroupMembership.cosetGrp Γ K y ≃ stabAt Γ K y where
  toFun x := ⟨⟨x.1, ((CosetGroupMembership.mem_cosetGrp Γ K y x.1).1 x.2).1⟩, ((CosetGroupMembership.mem_cosetGrp Γ K y x.1).1 x.2).2⟩
  invFun x := ⟨x.1.1, (CosetGroupMembership.mem_cosetGrp Γ K y x.1.1).2 ⟨x.1.2, x.2⟩⟩
  left_inv _ := rfl
  right_inv _ := rfl

theorem card_cosetGrp (Γ K : Subgroup G) (y : G) :
    Nat.card (CosetGroupMembership.cosetGrp Γ K y) = Nat.card (stabAt Γ K y) :=
  Nat.card_congr (cosetGrpEquiv Γ K y)

theorem sum_clause_iff (Γ K : Subgroup G) (m : ℝ) :
    (∀ (ι : Type) [Fintype ι] (y : ι → G),
      Function.Bijective (fun i => (DoubleCoset.mk Γ K (y i) : ClassSet Γ K)) →
      ∑ i, ((Nat.card (CosetGroupMembership.cosetGrp Γ K (y i)) : ℕ) : ℝ)⁻¹ = m) ↔
    (∀ [Fintype (ClassSet Γ K)] (s : ClassSet Γ K → G), (∀ c, DoubleCoset.mk Γ K (s c) = c) →
      ∑ c, ((Nat.card (stabAt Γ K (s c)) : ℕ) : ℝ)⁻¹ = m) := by
  constructor
  · intro h _ s hs
    have hb : Function.Bijective (fun c => (DoubleCoset.mk Γ K (s c) : ClassSet Γ K)) := by
      have : (fun c => (DoubleCoset.mk Γ K (s c) : ClassSet Γ K)) = id := funext hs
      rw [this]
      exact Function.bijective_id
    rw [← h _ s hb]
    simp only [card_cosetGrp]
  · intro h ι _ y hy
    let e : ι ≃ ClassSet Γ K := Equiv.ofBijective _ hy
    letI : Fintype (ClassSet Γ K) := Fintype.ofEquiv ι e
    have hs : ∀ c : ClassSet Γ K, DoubleCoset.mk Γ K (y (e.symm c)) = c := fun c => e.apply_symm_apply c
    rw [← h (fun c => y (e.symm c)) hs, ← e.symm.sum_comp]
    simp only [card_cosetGrp]

theorem cosetSum_iff (Γ K : Subgroup G) (m : ℝ) : CosetGroupMembership.CosetSum Γ K m ↔ ClassesDoubleCosets.CosetMass Γ K m :=
  and_congr Iff.rfl (and_congr (forall_congr' fun y => (cosetGrpEquiv Γ K y).finite_iff)
    (sum_clause_iff Γ K m))

end Abstract

section Obj

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E]

theorem stabHat_eq (hc : CMData F E) (S : HSpace E) (N : Submodule (𝓞 E) S.V) :
    CosetGroupMembership.stabHat hc S N = ClassesDoubleCosets.stabHat hc S N := rfl

theorem stabHat0_eq {R : Ranks} (sp : Spaces R F E) (N : Submodule (𝓞 E) (sp.X 0).V) :
    CosetGroupMembership.stabHat0 sp N = (levelAfL sp.cm.sig sp.gram0 (sp.crdLat0 N)).subgroupOf
      (UPts sp.cm.sig sp.gram0 (FiniteAdeleRing (𝓞 F) F)) := by
  ext x
  exact ⟨fun h => ⟨x.2, h⟩, fun h => h.2⟩

def InCoords (hc : CMData F E) {k : ℕ} (J : Matrix (Fin k) (Fin k) E) (Λ : Submodule (𝓞 E) (Fin k → E))
    (m : ℝ) : Prop :=
  CosetGroupMembership.CosetSum ((ratPts hc.sig J (Af F)).subgroupOf (UPts hc.sig J (Af F)))
    ((stabGL (hatL (F := F) Λ)).subgroupOf (UPts hc.sig J (Af F))) m

theorem inCoords_cast (hc : CMData F E) (S : HSpace E) {k : ℕ} (h : S.rank = k) (N : Submodule (𝓞 E) S.V)
    (m : ℝ) :
    InCoords hc S.gram (crdLat S N) m ↔
    InCoords hc (S.gram.reindex (finCongr h) (finCongr h))
      (N.map (((S.frame.equivFun.trans (LinearEquiv.funCongrLeft E E (finCongr h).symm) :
        S.V ≃ₗ[E] (Fin k → E)) : S.V →ₗ[E] (Fin k → E)).restrictScalars (𝓞 E))) m := by
  subst h
  rfl

theorem general_clause_iff {R : Ranks} (sp : Spaces R F E) (N : Submodule (𝓞 E) (sp.X 0).V) (m : ℝ) :
    CosetGroupMembership.CosetSum (UFin sp.cm (sp.X 0)) (CosetGroupMembership.stabHat sp.cm (sp.X 0) N) m ↔
    CosetGroupMembership.CosetSum (CosetGroupMembership.rat0 sp) (CosetGroupMembership.stabHat0 sp N) m :=
  inCoords_cast sp.cm (sp.X 0) sp.rank0 N m

end Obj

theorem general_iff : CosetGroupMembership.GeneralForm ↔ ClassesDoubleCosets.General := by
  unfold CosetGroupMembership.GeneralForm ClassesDoubleCosets.General
  simp only [cosetSum_iff, stabHat_eq]

theorem column_iff (D : D7) (Lv : LevelData D) (u : D.what₂.Word) :
    CosetGroupMembership.ColumnForm D ↔ ClassesDoubleCosets.DefiniteSpaceClassStatement D Lv u := by
  letI := D.host.cmStar
  unfold CosetGroupMembership.ColumnForm ClassesDoubleCosets.DefiniteSpaceClassStatement
  refine forall_congr' fun N => forall_congr' fun _ => forall_congr' fun _ => ?_
  rw [cosetSum_iff, stabHat0_eq]
  rfl

theorem column_of_general (h : CosetGroupMembership.GeneralForm) (D : D7) : CosetGroupMembership.ColumnForm D := by
  letI := D.host.cmStar
  intro N hN hU
  exact (general_clause_iff D.sp N _).1
    (h D.host.F D.host.E D.sp.cm (D.sp.X 0) (D.sp.X_sig 0) (baseSpace_posDef D.R D.host.F D.sp) N hN hU)

theorem massAsCosetSum_iff : CosetGroupMembership.MassAsCosetSum ↔ ClassesDoubleCosets.ClassesAsDoubleCosets :=
  ⟨fun h => ⟨general_iff.1 h.1, fun D Lv u => (column_iff D Lv u).1 (h.2 D)⟩,
    fun h => ⟨general_iff.2 h.1, column_of_general (general_iff.2 h.1)⟩⟩

end GlobalTheory.Proof.CosetGroupEquiv

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.IntertwinerZeroOfQuadraticTwists
section
open Formalism.MainNotions.N

namespace GlobalTheory

theorem trace_eq_of_agree_on_index_two_of_no_twisted_intertwiner : ∀ (Γ k : Type) [Group Γ] [Field k] [CharZero k] (n : ℕ) (ρ₀ ρ ρ' : Γ →* GL (Fin n) k) (η₀ χ₁ χ₂ : Γ →* ℤˣ), (∀ g, η₀ g = 1 → ρ g = ρ₀ g) → (∀ g, η₀ g = 1 → ρ' g = ρ₀ g) → IsSSRep ρ → IsSSRep ρ' → (∀ c : Γ →* ℤˣ, (c = χ₁ ∨ c = χ₂ ∨ c = χ₁ * χ₂ ∨ c = χ₁ * η₀ ∨ c = χ₂ * η₀ ∨ c = χ₁ * χ₂ * η₀) → ∀ X : Matrix (Fin n) (Fin n) k, (∀ g, ((ρ₀ g : GL (Fin n) k) : Matrix (Fin n) (Fin n) k) * X = ((c g : ℤ) : k) • (X * ((ρ₀ g : GL (Fin n) k) : Matrix (Fin n) (Fin n) k))) → X = 0) → (∀ g, χ₁ g = 1 → χ₂ g = 1 → ((ρ g : GL (Fin n) k) : Matrix (Fin n) (Fin n) k).trace = ((ρ' g : GL (Fin n) k) : Matrix (Fin n) (Fin n) k).trace) → ∀ g, ((ρ g : GL (Fin n) k) : Matrix (Fin n) (Fin n) k).trace = ((ρ' g : GL (Fin n) k) : Matrix (Fin n) (Fin n) k).trace := by
  intro Γ k _ _ _ n ρ₀ ρ ρ' η₀ χ₁ χ₂ hρ hρ' hs hs' hno htr
  obtain ⟨P, hP⟩ := _root_.GlobalTheory.QuadKernelConj.conj_on_ker_inf_ker Γ k n ρ ρ' χ₁ χ₂ hs hs' htr
  have hzero : ∀ c : Γ →* ℤˣ, (c = χ₁ ∨ c = χ₂ ∨ c = χ₁ * χ₂) →
      ∀ X : Matrix (Fin n) (Fin n) k,
      (∀ g ∈ (⊤ : Subgroup Γ), ((ρ g : GL (Fin n) k) : Matrix (Fin n) (Fin n) k) * X =
        ((c g : ℤ) : k) • (X * ((ρ' g : GL (Fin n) k) : Matrix (Fin n) (Fin n) k))) → X = 0 := by
    intro c hc X hX
    obtain ⟨A, B, hAB, hA, hB⟩ := _root_.GlobalTheory.twistedIntertwiner_decomp_of_quadraticKernel Γ k n ρ₀ ρ₀ ⊤ c η₀ X (by
      intro g hg h
      have := hX g hg
      rwa [hρ g h, hρ' g h] at this)
    have hA0 : A = 0 := hno c (by tauto) A (fun g => hA g trivial)
    have hB0 : B = 0 := hno (c * η₀) (by rcases hc with rfl | rfl | rfl <;> simp) B
      (fun g => hB g trivial)
    rw [hAB, hA0, hB0, add_zero]
  obtain ⟨Y₁, Y₂, hY, hY₁, hY₂⟩ := _root_.GlobalTheory.twistedIntertwiner_decomp_of_quadraticKernel Γ k n ρ' ρ χ₂.ker 1 χ₁
    (P : Matrix (Fin n) (Fin n) k) (by
      intro g hg h
      have h1 : ρ g * P = P * ρ' g := by rw [hP g h hg]; group
      have h2 := congrArg (fun x : GL (Fin n) k => (x : Matrix (Fin n) (Fin n) k)) h1
      simpa using h2)
  obtain ⟨A, B, hAB, hA, hB⟩ := _root_.GlobalTheory.twistedIntertwiner_decomp_of_quadraticKernel Γ k n ρ' ρ ⊤ 1 χ₂ Y₁ (fun g _ h => hY₁ g h)
  obtain ⟨C, D, hCD, hC, hD⟩ := _root_.GlobalTheory.twistedIntertwiner_decomp_of_quadraticKernel Γ k n ρ' ρ ⊤ (1 * χ₁) χ₂ Y₂ (fun g _ h => hY₂ g h)
  have hB0 : B = 0 := hzero _ (by simp) B hB
  have hC0 : C = 0 := hzero _ (by simp) C hC
  have hD0 : D = 0 := hzero _ (by simp) D hD
  have hPA : (P : Matrix (Fin n) (Fin n) k) = A := by
    rw [hY, hAB, hCD, hB0, hC0, hD0]; simp
  intro g
  have h1 : ((ρ g : GL (Fin n) k) : Matrix (Fin n) (Fin n) k) * (P : Matrix (Fin n) (Fin n) k) =
      (P : Matrix (Fin n) (Fin n) k) * ((ρ' g : GL (Fin n) k) : Matrix (Fin n) (Fin n) k) := by
    have := hA g trivial
    rw [← hPA] at this
    simpa using this
  have h2 : ((ρ g : GL (Fin n) k) : Matrix (Fin n) (Fin n) k) =
      (P : Matrix (Fin n) (Fin n) k) * ((ρ' g : GL (Fin n) k) : Matrix (Fin n) (Fin n) k) *
        ((P⁻¹ : GL (Fin n) k) : Matrix (Fin n) (Fin n) k) := by
    rw [← h1, mul_assoc, Units.mul_inv, mul_one]
  rw [h2, Matrix.trace_mul_cycle, Units.inv_mul, one_mul]

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.LatticePeriodEtaObj
section
noncomputable section

namespace GlobalTheory.LatticePeriodEtaObj

theorem latticePeriodEta_obj : GlobalTheory.IndefiniteRowSideFullHecke.PeriodLatticeAgreement.LatticePeriodEta :=
  GlobalTheory.LatticePeriodEtaProof.latticePeriodEta

end GlobalTheory.LatticePeriodEtaObj
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.MemLocSub
section
namespace GlobalTheory.EX.Glue

open Formalism.BasicNotions NumberField IsDedekindDomain

theorem exists_clear {R : Type} [CommRing R] [IsDedekindDomain R] (c : R) (hc : c ≠ 0)
    (w₀ : HeightOneSpectrum R) :
    ∃ t : R, t ∉ w₀.asIdeal ∧ ∀ w : HeightOneSpectrum R, w ≠ w₀ → ∃ s : R, s ∉ w.asIdeal ∧ c ∣ s * t := by
  classical
  haveI := w₀.isMaximal
  have hI : Ideal.span {c} ≠ ⊥ := by simpa [Ideal.span_singleton_eq_bot] using hc
  obtain ⟨Q, hQ, hfac⟩ := Ideal.eq_prime_pow_mul_coprime hI w₀.asIdeal
  have hQn : ¬ Q ≤ w₀.asIdeal := by
    intro h
    rw [sup_eq_left.2 h] at hQ
    exact w₀.isPrime.ne_top hQ
  obtain ⟨t, htQ, ht⟩ := SetLike.not_le_iff_exists.1 hQn
  refine ⟨t, ht, fun w hw => ?_⟩
  generalize Multiset.count w₀.asIdeal _ = k at hfac
  have hP : ¬ w₀.asIdeal ^ k ≤ w.asIdeal := by
    intro h
    haveI := w.isPrime
    have h' : w₀.asIdeal ≤ w.asIdeal := Ideal.IsPrime.le_of_pow_le h
    exact hw (HeightOneSpectrum.ext (w₀.isMaximal.eq_of_le w.isPrime.ne_top h').symm)
  obtain ⟨s, hsP, hs⟩ := SetLike.not_le_iff_exists.1 hP
  refine ⟨s, hs, ?_⟩
  rw [← Ideal.mem_span_singleton, hfac]
  exact Ideal.mul_mem_mul hsP htQ

variable {K V : Type} [Field K] [NumberField K] [AddCommGroup V] [Module (𝓞 K) V]

def locSub (w : HeightOneSpectrum (𝓞 K)) (M : Submodule (𝓞 K) V) : Submodule (𝓞 K) V where
  carrier := {x | InLoc w M x}
  zero_mem' := ⟨1, (Ideal.ne_top_iff_one _).1 w.isPrime.ne_top, by simp⟩
  add_mem' := by
    rintro x y ⟨s, hs, hx⟩ ⟨t, ht, hy⟩
    refine ⟨s * t, fun h => (w.isPrime.mem_or_mem h).elim hs ht, ?_⟩
    rw [smul_add]
    refine M.add_mem ?_ ?_
    · rw [mul_comm, mul_smul]; exact M.smul_mem _ hx
    · rw [mul_smul]; exact M.smul_mem _ hy
  smul_mem' := by
    rintro a x ⟨s, hs, hx⟩
    exact ⟨s, hs, by rw [smul_comm]; exact M.smul_mem _ hx⟩

theorem mem_locSub {w : HeightOneSpectrum (𝓞 K)} {M : Submodule (𝓞 K) V} {x : V} :
    x ∈ locSub w M ↔ InLoc w M x := Iff.rfl

theorem inLoc_iInf (B : HeightOneSpectrum (𝓞 K) → Submodule (𝓞 K) V)
    (hsat : ∀ w (t : 𝓞 K) (x : V), t ∉ w.asIdeal → t • x ∈ B w → x ∈ B w)
    (hden : ∀ x : V, ∃ c : 𝓞 K, c ≠ 0 ∧ ∀ w, c • x ∈ B w) (w₀ : HeightOneSpectrum (𝓞 K)) (x : V) :
    InLoc w₀ (⨅ w, B w) x ↔ x ∈ B w₀ := by
  constructor
  · rintro ⟨s, hs, hx⟩
    exact hsat w₀ s x hs ((Submodule.mem_iInf _).1 hx w₀)
  · intro hx
    obtain ⟨c, hc, hcx⟩ := hden x
    obtain ⟨t, ht, h⟩ := exists_clear c hc w₀
    refine ⟨t, ht, (Submodule.mem_iInf _).2 fun w => ?_⟩
    by_cases hw : w = w₀
    · subst hw; exact (B w).smul_mem _ hx
    · obtain ⟨s, hs, d, hd⟩ := h w hw
      refine hsat w s _ hs ?_
      rw [← mul_smul, hd, mul_comm, mul_smul]
      exact (B w).smul_mem _ (hcx w)

theorem exists_glue : ∀ (K V : Type) [Field K] [NumberField K] [AddCommGroup V] [Module K V] [Module (𝓞 K) V]
    [IsScalarTower (𝓞 K) K V] (M : Submodule (𝓞 K) V) (S : Set (IsDedekindDomain.HeightOneSpectrum (𝓞 K)))
    (A : IsDedekindDomain.HeightOneSpectrum (𝓞 K) → Submodule (𝓞 K) V), S.Finite →
    (∀ x : V, ∃ n : ℕ, n ≠ 0 ∧ n • x ∈ M) →
    (∀ w ∈ S, (∀ (t : 𝓞 K) (x : V), t ∉ w.asIdeal → t • x ∈ A w → x ∈ A w) ∧
      ∃ n : ℕ, n ≠ 0 ∧ (∀ x ∈ M, n • x ∈ A w) ∧ ∀ x ∈ A w, InLoc w M (n • x)) →
    ∃ N : Submodule (𝓞 K) V, (∀ w ∈ S, ∀ x, InLoc w N x ↔ x ∈ A w) ∧
      ∀ w ∉ S, ∀ x, InLoc w N x ↔ InLoc w M x := by
  intro K V _ _ _ _ _ _ M S A hS hM hA
  classical
  let B : HeightOneSpectrum (𝓞 K) → Submodule (𝓞 K) V := fun w => if w ∈ S then A w else locSub w M
  have hB1 : ∀ w ∈ S, B w = A w := fun w hw => if_pos hw
  have hB2 : ∀ w ∉ S, B w = locSub w M := fun w hw => if_neg hw
  have hsat : ∀ w (t : 𝓞 K) (x : V), t ∉ w.asIdeal → t • x ∈ B w → x ∈ B w := by
    intro w t x ht hx
    by_cases hw : w ∈ S
    · rw [hB1 w hw] at hx ⊢
      exact (hA w hw).1 t x ht hx
    · rw [hB2 w hw] at hx ⊢
      obtain ⟨s, hs, hx⟩ := hx
      exact ⟨s * t, fun h => (w.isPrime.mem_or_mem h).elim hs ht, by rwa [mul_smul]⟩
  have hn : ∀ w, ∃ n : ℕ, n ≠ 0 ∧ (w ∈ S → ∀ x ∈ M, n • x ∈ A w) := by
    intro w
    by_cases hw : w ∈ S
    · obtain ⟨n, hn, h, -⟩ := (hA w hw).2
      exact ⟨n, hn, fun _ => h⟩
    · exact ⟨1, one_ne_zero, fun h => absurd h hw⟩
  choose n hn0 hn using hn
  have hden : ∀ x : V, ∃ c : 𝓞 K, c ≠ 0 ∧ ∀ w, c • x ∈ B w := by
    intro x
    obtain ⟨m, hm, hx⟩ := hM x
    refine ⟨(((∏ w ∈ hS.toFinset, n w) * m : ℕ) : 𝓞 K), ?_, fun w => ?_⟩
    · exact Nat.cast_ne_zero.2 (mul_ne_zero (Finset.prod_ne_zero_iff.2 fun w _ => hn0 w) hm)
    · rw [Nat.cast_smul_eq_nsmul, mul_smul]
      by_cases hw : w ∈ S
      · rw [hB1 w hw]
        obtain ⟨d, hd⟩ := Finset.dvd_prod_of_mem n (hS.mem_toFinset.2 hw)
        rw [hd, mul_comm, mul_smul]
        exact nsmul_mem (hn w hw _ hx) d
      · rw [hB2 w hw]
        exact ⟨1, (Ideal.ne_top_iff_one _).1 w.isPrime.ne_top, by
          rw [one_smul]; exact nsmul_mem hx _⟩
  refine ⟨⨅ w, B w, fun w hw x => ?_, fun w hw x => ?_⟩
  · rw [inLoc_iInf B hsat hden, hB1 w hw]
  · rw [inLoc_iInf B hsat hden, hB2 w hw, mem_locSub]

end GlobalTheory.EX.Glue
end

