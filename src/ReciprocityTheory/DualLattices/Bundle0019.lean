module

public import ReciprocityTheory.DualLattices.Bundle0009
public import ReciprocityTheory.DualLattices.UnramifiedCokernelLowerBoundOf
public import ReciprocityTheory.DualLattices.Bundle0017
public import ReciprocityTheory.DualLattices.UpSmith
public import ReciprocityTheory.DualLattices.Bundle0015
public import ReciprocityTheory.DualLattices.Bundle0018
public import ReciprocityTheory.DualLattices.Bundle0010

@[expose] public section

-- bundled from ReciprocityTheory.DualLattices.CokernelLengthComparisonOf
section
noncomputable section

open Matrix

namespace ReciprocityTheory.PGsh.Up

open ReciprocityTheory.PGsh.L2

section Defs

variable {p : ℕ} [Fact p.Prime] {g : ℕ} {C : Type} [Field C] {v : Valuation C NNReal} {R : Type}
  [CommRing R] [Algebra R C] [Algebra ℤ_[p] R] {O : Type} [CommRing O] [Algebra ℤ_[p] O]
  {σ : O ≃ₐ[ℤ_[p]] O} {cp : R}

def btP (H : HodgeTateDatum p g v R O σ cp) {m : ℕ} (e : Fin m → O) : Matrix (Fin g) (Ix g) R :=
  ∑ i, H.ρL (e i) * H.Bt * (H.ρ (e i)).map (algebraMap ℤ_[p] R) +
    H.PL * H.Bt * H.P.map (algebraMap ℤ_[p] R)

def phiP (H : HodgeTateDatum p g v R O σ cp) {m : ℕ} (e : Fin m → O) : Matrix (Fin g ⊕ Fin g) (Ix g) R :=
  fromRows H.Ht (btP H e)

def qW (H : HodgeTateDatum p g v R O σ cp) (a b : O) : Submodule R (Fin g ⊕ Fin g → R) :=
  (lieDPart H b).comap (LinearMap.funLeft R R Sum.inl) ⊓
    (LinearMap.range (Matrix.mulVecLin (H.ρL a))).comap (LinearMap.funLeft R R Sum.inr)

abbrev xMod (H : HodgeTateDatum p g v R O σ cp) {m : ℕ} (e : Fin m → O) (π : Equiv.Perm (Fin m)) (w : Fin m) :=
  qW H (e w) (e (π w)) ⧸
    ((tPart H (e w)).map (Matrix.mulVecLin (phiP H e))).comap (qW H (e w) (e (π w))).subtype

end Defs

def WdetLenStatement : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (g : ℕ) (C : Type) [Field C] [IsAlgClosed C] [CharZero C]
    (v : Valuation C NNReal) (R : Type) [CommRing R] [Algebra R C] [Algebra ℤ_[p] R]
    (O : Type) [CommRing O] [Algebra ℤ_[p] O] (σ : O ≃ₐ[ℤ_[p]] O) (cp : R),
    HodgeTateSetting p v R O σ cp → ∀ (H : HodgeTateDatum p g v R O σ cp) (m : ℕ) (e : Fin m → O)
    (π : Equiv.Perm (Fin m)),
    (∀ i j, e i * e j = if i = j then e i else 0) → (∀ i, σ (e i) = e (π i)) →
    (∑ i, H.ρ (e i)) + H.P = 1 → (∀ i, H.ρ (e i) * H.P = 0) →
    (∑ i, H.ρL (e i)) + H.PL = 1 → (∀ i, H.ρL (e i) * H.PL = 0) →
    ∀ w, π w ≠ w → ∀ cw cwb : NNReal,
      HasLen v R (htCoker H (e w) (e (π w))) cw →
      HasLen v R (htCoker H (e (π w)) (e w)) cwb →
      ∃ (d : ℕ) (X : NNReal),
        Nonempty (LinearMap.range (Matrix.mulVecLin (H.ρL (e w))) ≃ₗ[R] (Fin d → R)) ∧
        HasLen v R (xMod H e π w) X ∧ X * cw = v (algebraMap R C cp) ^ d * cwb

def WdetDegStatement : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (g : ℕ) (C : Type) [Field C] [IsAlgClosed C] [CharZero C]
    (v : Valuation C NNReal) (R : Type) [CommRing R] [Algebra R C] [Algebra ℤ_[p] R]
    (O : Type) [CommRing O] [Algebra ℤ_[p] O] (σ : O ≃ₐ[ℤ_[p]] O) (cp : R),
    HodgeTateSetting p v R O σ cp → ∀ (H : HodgeTateDatum p g v R O σ cp) (m : ℕ) (e : Fin m → O)
    (π : Equiv.Perm (Fin m)),
    (∀ i j, e i * e j = if i = j then e i else 0) → (∀ i, σ (e i) = e (π i)) →
    (∑ i, H.ρ (e i)) + H.P = 1 → (∀ i, H.ρ (e i) * H.P = 0) →
    (∑ i, H.ρL (e i)) + H.PL = 1 → (∀ i, H.ρL (e i) * H.PL = 0) →
    ∀ w, π w ≠ w → ∀ (d : ℕ) (X : NNReal),
      Nonempty (LinearMap.range (Matrix.mulVecLin (H.ρL (e w))) ≃ₗ[R] (Fin d → R)) →
      HasLen v R (xMod H e π w) X → X ≤ v (algebraMap R C cp) ^ d

theorem cokernelLengthComparison_of (hW1 : WdetLenStatement) (hW2 : WdetDegStatement) : CokernelLengthComparisonStatement := by
  intro p _ g C _ _ _ v R _ _ _ O _ _ σ cp hS H m e π he hσ h1 h2 h3 h4 w hw cw cwb hcw hcwb
  obtain ⟨d, X, hd, hX, hXe⟩ :=
    hW1 p g C v R O σ cp hS H m e π he hσ h1 h2 h3 h4 w hw cw cwb hcw hcwb
  have hle := hW2 p g C v R O σ cp hS H m e π he hσ h1 h2 h3 h4 w hw d X hd hX
  have hcp : v (algebraMap R C cp) ≠ 0 := by
    intro h0
    have h5 := hS.cp_val
    rw [h0, zero_pow (Nat.sub_pos_of_lt (Fact.out : p.Prime).one_lt).ne'] at h5
    exact hS.p_ne h5.symm
  have hpos : 0 < v (algebraMap R C cp) ^ d := pow_pos (pos_iff_ne_zero.mpr hcp) d
  have h6 : v (algebraMap R C cp) ^ d * cwb ≤ v (algebraMap R C cp) ^ d * cw := by
    rw [← hXe]
    exact mul_le_mul_of_nonneg_right hle zero_le
  exact le_of_mul_le_mul_left h6 hpos

end ReciprocityTheory.PGsh.Up
end
end

-- bundled from ReciprocityTheory.DualLattices.EigenLengthProductStatementHolds
section
noncomputable section

open Matrix

namespace ReciprocityTheory.PGsh.Up

namespace Tot

section len

variable {C : Type} [Field C] {v : Valuation C NNReal} {R : Type} [CommRing R] [Algebra R C]

theorem hasLen_equiv {M N : Type} [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    (e : M ≃ₗ[R] N) {x : NNReal} (h : HasLen v R N x) : HasLen v R M x := by
  obtain ⟨m, c, ⟨f⟩, hx⟩ := h
  exact ⟨m, c, ⟨e.trans f⟩, hx⟩

theorem hasLen_pi {m : ℕ} (M : Fin m → Type) [∀ i, AddCommGroup (M i)] [∀ i, Module R (M i)]
    (X : Fin m → NNReal) (h : ∀ i, HasLen v R (M i) (X i)) :
    HasLen v R ((i : Fin m) → M i) (∏ i, X i) := by
  classical
  choose n c he hX using h
  let e : ∀ i, M i ≃ₗ[R] ((j : Fin (n i)) → R ⧸ Ideal.span {c i j}) := fun i => (he i).some
  let σ : Fin (Fintype.card (Σ i, Fin (n i))) ≃ (Σ i, Fin (n i)) := (Fintype.equivFin _).symm
  refine ⟨Fintype.card (Σ i, Fin (n i)), fun k => c (σ k).1 (σ k).2, ⟨?_⟩, ?_⟩
  · exact (LinearEquiv.piCongrRight e).trans
      ((LinearEquiv.piCurry R (fun i j => R ⧸ Ideal.span {c i j})).symm.trans
        (LinearEquiv.piCongrLeft R (fun p : Σ i, Fin (n i) => R ⧸ Ideal.span {c p.1 p.2}) σ).symm)
  · rw [Fintype.prod_equiv σ (fun k => v (algebraMap R C (c (σ k).1 (σ k).2)))
      (fun p => v (algebraMap R C (c p.1 p.2))) (fun k => rfl), Fintype.prod_sigma]
    exact Finset.prod_congr rfl fun i _ => hX i

end len

variable {R : Type} [CommRing R]

theorem sum_fromBlocks_diag {g : ℕ} {ι : Type} (s : Finset ι)
    (A D : ι → Matrix (Fin g) (Fin g) R) :
    ∑ i ∈ s, fromBlocks (A i) 0 0 (D i) = fromBlocks (∑ i ∈ s, A i) 0 0 (∑ i ∈ s, D i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [fromBlocks_zero]
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha, Finset.sum_insert ha, ih, fromBlocks_add,
      add_zero]

theorem sum_mulVec' {n : Type} [Fintype n] {ι : Type} (s : Finset ι) (A : ι → Matrix n n R)
    (w : n → R) : (∑ i ∈ s, A i) *ᵥ w = ∑ i ∈ s, A i *ᵥ w := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, add_mulVec, ih]

end Tot

open Tot in
theorem eigenLengthProductStatement_holds : EigenLengthProductStatement := by
  intro C _ v R _ _ hv g m Ht Bt εT εL π hπ hTo hTs hLo hLs hHt hBt X hX
  classical
  set Φ := fromRows Ht Bt with hΦ
  set Pm : Fin m → Matrix (Fin g ⊕ Fin g) (Fin g ⊕ Fin g) R :=
    fun i => fromBlocks ((εL (π i))ᵀ) 0 0 (εL i) with hPm
  have hPmv : ∀ i w, Pm i *ᵥ w =
      Sum.elim ((εL (π i))ᵀ *ᵥ (w ∘ Sum.inl)) (εL i *ᵥ (w ∘ Sum.inr)) := by
    intro i w
    simp only [hPm, fromBlocks_mulVec, zero_mulVec, add_zero, zero_add]
  have hmem : ∀ i w, Pm i *ᵥ w ∈ qE εL i (π i) := by
    intro i w
    refine Submodule.mem_inf.2 ⟨⟨w ∘ Sum.inl, ?_⟩, ⟨w ∘ Sum.inr, ?_⟩⟩
    · show (εL (π i))ᵀ *ᵥ (w ∘ Sum.inl) = (Pm i *ᵥ w) ∘ Sum.inl
      rw [hPmv]; rfl
    · show εL i *ᵥ (w ∘ Sum.inr) = (Pm i *ᵥ w) ∘ Sum.inr
      rw [hPmv]; rfl
  have hsel : ∀ i k w, w ∈ qE εL i (π i) → Pm k *ᵥ w = if k = i then w else 0 := by
    intro i k w hw
    obtain ⟨⟨y1, hy1⟩, ⟨y2, hy2⟩⟩ := Submodule.mem_inf.1 hw
    have e1 : w ∘ Sum.inl = (εL (π i))ᵀ *ᵥ y1 := hy1.symm
    have e2 : w ∘ Sum.inr = εL i *ᵥ y2 := hy2.symm
    rw [hPmv, e1, e2, mulVec_mulVec, mulVec_mulVec, ← transpose_mul, hLo, hLo]
    by_cases hki : k = i
    · subst hki
      simp only [if_true]
      rw [← e1, ← e2, Sum.elim_comp_inl_inr]
    · have hne : π i ≠ π k := fun h => hki (π.injective h).symm
      simp only [hki, hne, if_false, transpose_zero, zero_mulVec]
      ext s; cases s <;> rfl
  have hT : ∑ i, (εL (π i))ᵀ = 1 := by
    rw [← transpose_sum, Equiv.sum_comp π εL, hLs, transpose_one]
  have hPsum : ∑ i, Pm i = 1 := by
    simp only [hPm]
    rw [sum_fromBlocks_diag, hT, hLs, fromBlocks_one]
  have hsum : ∀ w, ∑ i, Pm i *ᵥ w = w := by
    intro w
    rw [← sum_mulVec', hPsum, one_mulVec]
  have hPΦ : ∀ i, Pm i * Φ = Φ * εT i := by
    intro i
    rw [hΦ, hPm, fromBlocks_mul_fromRows, fromRows_mul, Matrix.zero_mul, Matrix.zero_mul, add_zero,
      zero_add,
      hHt, hBt]
  set Ψ : (Fin g ⊕ Fin g → R) →ₗ[R] ((i : Fin m) → xModE Ht Bt εT εL π i) :=
    LinearMap.pi fun i => Submodule.mkQ _ ∘ₗ
      LinearMap.codRestrict (qE εL i (π i)) (mulVecLin (Pm i)) (hmem i) with hΨdef
  have hΨ : ∀ w i, Ψ w i = Submodule.Quotient.mk ⟨Pm i *ᵥ w, hmem i w⟩ := fun _ _ => rfl
  have hsurj : Function.Surjective Ψ := by
    intro q
    choose w hw using fun i => Submodule.Quotient.mk_surjective _ (q i)
    refine ⟨∑ i, ((w i : qE εL i (π i)) : Fin g ⊕ Fin g → R), funext fun k => ?_⟩
    rw [hΨ, ← hw k]
    congr 1
    apply Subtype.ext
    show Pm k *ᵥ ∑ i, ((w i : qE εL i (π i)) : Fin g ⊕ Fin g → R) = (w k : Fin g ⊕ Fin g → R)
    rw [mulVec_sum]
    simp only [fun i => hsel i k _ (w i).2]
    simp
  have hker : LinearMap.ker Ψ = LinearMap.range (mulVecLin Φ) := by
    ext w
    rw [LinearMap.mem_ker]
    constructor
    · intro h
      have hi : ∀ i, ∃ t, Φ *ᵥ (εT i *ᵥ t) = Pm i *ᵥ w := by
        intro i
        have := congrFun h i
        rw [hΨ, Pi.zero_apply, Submodule.Quotient.mk_eq_zero] at this
        obtain ⟨y, ⟨t, rfl⟩, hy⟩ := this
        exact ⟨t, hy⟩
      choose t ht using hi
      refine ⟨∑ i, εT i *ᵥ t i, ?_⟩
      show Φ *ᵥ ∑ i, εT i *ᵥ t i = w
      rw [mulVec_sum]
      simp only [ht]
      exact hsum w
    · rintro ⟨t, rfl⟩
      funext i
      rw [hΨ, Pi.zero_apply, Submodule.Quotient.mk_eq_zero]
      refine ⟨εT i *ᵥ t, ⟨t, rfl⟩, ?_⟩
      show Φ *ᵥ (εT i *ᵥ t) = Pm i *ᵥ (Φ *ᵥ t)
      rw [mulVec_mulVec, mulVec_mulVec, hPΦ]
  have iso : ((Fin g ⊕ Fin g → R) ⧸ LinearMap.range (mulVecLin Φ)) ≃ₗ[R]
      ((i : Fin m) → xModE Ht Bt εT εL π i) :=
    (Submodule.quotEquivOfEq _ _ hker.symm).trans (Ψ.quotKerEquivOfSurjective hsurj)
  set e : Fin g ⊕ Fin g ≃ Fin (g + g) := finSumFinEquiv with he
  set Φ' := reindex e e Φ with hΦ'
  have hdet : Φ'.det = Φ.det := det_reindex_self e Φ
  set F : (Fin (g + g) → R) ≃ₗ[R] (Fin g ⊕ Fin g → R) := LinearEquiv.funCongrLeft R R e with hF
  have hFapp : ∀ y, F y = y ∘ e := fun y => rfl
  have hcomm : ∀ y, F (Φ' *ᵥ y) = Φ *ᵥ F y := by
    intro y
    rw [hFapp, hFapp, hΦ', reindex_apply, submatrix_mulVec_equiv]
    ext s
    simp
  have hmap : (LinearMap.range (mulVecLin Φ')).map F.toLinearMap = LinearMap.range (mulVecLin Φ) := by
    ext z
    constructor
    · rintro ⟨_, ⟨y, rfl⟩, rfl⟩
      exact ⟨F y, (hcomm y).symm⟩
    · rintro ⟨t, rfl⟩
      refine ⟨Φ' *ᵥ F.symm t, ⟨F.symm t, rfl⟩, ?_⟩
      show F (Φ' *ᵥ F.symm t) = Φ *ᵥ t
      rw [hcomm, LinearEquiv.apply_symm_apply]
  have hcok := Submodule.Quotient.equiv _ _ F hmap
  have hL1 := Smith.hasLen_coker_det (C := C) (v := v) hv Φ'
  have hL2 : HasLen v R ((Fin (g + g) → R) ⧸ LinearMap.range (mulVecLin Φ')) (∏ i, X i) :=
    hasLen_equiv (hcok.trans iso) (hasLen_pi _ X hX)
  rw [hasLen_unique hv hL2 hL1, hdet]

end ReciprocityTheory.PGsh.Up
end
end

-- bundled from ReciprocityTheory.DualLattices.EigenLiftsFrobeniusStatement
section
noncomputable section

open Matrix

namespace ReciprocityTheory.PGsh.Up

open ReciprocityTheory.PGsh.L2

structure Lifts {p : ℕ} [Fact p.Prime] {g : ℕ} {C : Type} [Field C] {v : Valuation C NNReal}
    {R : Type} [CommRing R] [Algebra R C] [Algebra ℤ_[p] R] {O : Type} [CommRing O]
    [Algebra ℤ_[p] O] {σ : O ≃ₐ[ℤ_[p]] O} {cp : R} (H : HodgeTateDatum p g v R O σ cp)
    (U : UnramData p g v R O σ cp H) (X : Fin U.m → NNReal) where
  κ : Ix g → Fin U.m
  card_phi : ∀ i, (Finset.univ.filter fun j => κ j = U.φ i).card =
    (Finset.univ.filter fun j => κ j = i).card
  r_zero : ∀ i, (∀ j, κ j ≠ i) → U.r i = 0
  Λ : Matrix (Ix g) (Ix g) R
  Λ_det : IsUnit Λ.det
  Λ_block : ∀ j, Matrix.vecMul (Λ j) (U.εT (κ j)) = Λ j
  ε : Ix g → R
  ε_ne : ∀ j, ε j ≠ 0
  ε_prod : ∀ i, ∏ j ∈ Finset.univ.filter (fun j => κ j = i), v (algebraMap R C (ε j)) = X i
  u : Ix g → Nb p g → C
  u_int : ∀ j y, v (u j y) ≤ 1
  u_cong : ∀ j (y : Nb p g), v (u j y - algebraMap R C (∑ k, Λ j k * ((y k).val : R))) < 1
  x_mem : ∀ j, (fun y => algebraMap R C (ε j) * u j y) ∈ augIdeal H.AA.carrier
  s : ℕ
  b : Fin s → O
  eig : ∀ j k (t : TT p g),
    u j (red p g (H.ρ (b k) *ᵥ t)) = algebraMap R C (U.sg (κ j) (b k)) * u j (red p g t)
  frobChar : ∀ j k, U.sg (U.φ (κ j)) (b k) = U.sg (κ j) (b k) ^ p
  sep : ∀ j j', κ j ≠ κ j' → ∃ k, v (algebraMap R C (U.sg (κ j) (b k) - U.sg (κ j') (b k))) = 1

def EigenLiftsStatement : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (g : ℕ) (C : Type) [Field C] [IsAlgClosed C] [CharZero C]
    (v : Valuation C NNReal) (R : Type) [CommRing R] [Algebra R C] [Algebra ℤ_[p] R]
    (O : Type) [CommRing O] [Algebra ℤ_[p] O] (σ : O ≃ₐ[ℤ_[p]] O) (cp : R),
    p ≠ 2 → HodgeTateSetting p v R O σ cp → ∀ (H : HodgeTateDatum p g v R O σ cp)
    (U : UnramData p g v R O σ cp H) (X : Fin U.m → NNReal),
    (∀ i, HasLen v R (xModE H.Ht (bt2 H U) U.εT U.εL U.cj i) (X i)) → Nonempty (Lifts H U X)

def EigenLiftsBasisStatement : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (g : ℕ) (C : Type) [Field C] [IsAlgClosed C] [CharZero C]
    (v : Valuation C NNReal) (R : Type) [CommRing R] [Algebra R C] [Algebra ℤ_[p] R]
    (O : Type) [CommRing O] [Algebra ℤ_[p] O] (σ : O ≃ₐ[ℤ_[p]] O) (cp : R),
    HodgeTateSetting p v R O σ cp → ∀ (H : HodgeTateDatum p g v R O σ cp)
    (U : UnramData p g v R O σ cp H) (X : Fin U.m → NNReal),
    ∏ i, X i = v (algebraMap R C cp) ^ g → ∀ D : Lifts H U X,
    H.AA.carrier = Submodule.span R (Set.range fun (α : Nb p g) (y : Nb p g) =>
      ∏ j, (algebraMap R C (D.ε j) * D.u j y) ^ (α j).val)

def EigenLiftsFrobeniusStatement : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (g : ℕ) (C : Type) [Field C] [IsAlgClosed C] [CharZero C]
    (v : Valuation C NNReal) (R : Type) [CommRing R] [Algebra R C] [Algebra ℤ_[p] R]
    (O : Type) [CommRing O] [Algebra ℤ_[p] O] (σ : O ≃ₐ[ℤ_[p]] O) (cp : R),
    p ≠ 2 → HodgeTateSetting p v R O σ cp → ∀ (H : HodgeTateDatum p g v R O σ cp)
    (U : UnramData p g v R O σ cp H) (X : Fin U.m → NNReal) (D : Lifts H U X),
    H.AA.carrier = Submodule.span R (Set.range fun (α : Nb p g) (y : Nb p g) =>
      ∏ j, (algebraMap R C (D.ε j) * D.u j y) ^ (α j).val) →
    ∀ i, X i ^ p ≤ X (U.φ i) * v (algebraMap R C (p : R)) ^ U.r (U.φ i)

theorem core_of (hL : EigenLiftsStatement) (hB : EigenLiftsBasisStatement) (hF : EigenLiftsFrobeniusStatement) :
    EigenLengthFrobeniusStatement := by
  intro p _ g C _ _ _ v R _ _ _ O _ _ σ cp hp hS H U X hX hprod i
  obtain ⟨D⟩ := hL p g C v R O σ cp hp hS H U X hX
  exact hF p g C v R O σ cp hp hS H U X D (hB p g C v R O σ cp hS H U X hprod D) i

end ReciprocityTheory.PGsh.Up
end
end

-- bundled from ReciprocityTheory.DualLattices.HasColengthEqPowMulPow
section
noncomputable section

open Matrix Finset

namespace ReciprocityTheory.PGsh.L2

variable {C : Type} [Field C] {R : Type} [CommRing R] [Algebra R C] {v : Valuation C NNReal}
variable {N : Type} [AddCommGroup N] [Fintype N] [DecidableEq N]

theorem quotient_out_add_coe (K : AddSubgroup N) (q : N ⧸ K) (k : K) :
    ((q.out + k : N) : N ⧸ K) = q := by
  rw [QuotientAddGroup.mk_add, QuotientAddGroup.out_eq',
    (QuotientAddGroup.eq_zero_iff (k : N)).mpr k.2, add_zero]

def quotientProdSubgroupEquiv (K : AddSubgroup N) : (N ⧸ K) × K ≃ N where
  toFun p := p.1.out + p.2
  invFun x := ((x : N ⧸ K),
    ⟨-((x : N ⧸ K).out) + x, QuotientAddGroup.eq.1 (QuotientAddGroup.out_eq' _)⟩)
  left_inv := by
    rintro ⟨q, k⟩
    refine Prod.ext (quotient_out_add_coe K q k) (Subtype.ext ?_)
    show -((((q.out + k : N)) : N ⧸ K).out) + (q.out + k) = k
    rw [quotient_out_add_coe K q k]
    abel
  right_inv := by
    intro x
    show (x : N ⧸ K).out + (-((x : N ⧸ K).out) + x) = x
    abel

private theorem valuation_det_le_one_of_integral_entries (hv : v.Integers R) {X : Type} [Fintype X] [DecidableEq X]
    (E : Matrix X X C) (hE : ∀ i j, ∃ r : R, algebraMap R C r = E i j) : v E.det ≤ 1 := by
  choose M hM using hE
  have hEM : E = (Matrix.of M).map (algebraMap R C) := by
    ext i j
    exact (hM i j).symm
  rw [hEM, det_map_algebraMap]
  exact hv.map_le_one _

theorem hasColength_eq_pow_mul_pow (hv : v.Integers R) (AA : HopfOrder (C := C) R N) (K : AddSubgroup N)
    [DecidablePred (· ∈ K)] [DecidableEq (N ⧸ K)] [Fintype (N ⧸ K)] :
    ∀ c cB cK, HasColen R v AA.carrier c →
      HasColen R v (AA.carrier.comap (pullQ (R := R) K)) cB →
      HasColen R v (AA.carrier.map (resK (R := R) K)) cK →
      c = cB ^ Fintype.card K * cK ^ Fintype.card (N ⧸ K) := by
  intro c cB cK hc hcB hcK
  obtain ⟨β, hβ, hAK⟩ := exists_basis_map_restrictToSubgroup hv AA K
  obtain ⟨f, hfA, hfu⟩ := exists_coset_basis hv AA K
  obtain ⟨g, hgA, hgdet⟩ := exists_family_valuation_det_eq_one hv AA K β hβ hAK
  obtain ⟨P, hP, rfl⟩ := hc
  obtain ⟨Q, hQ, rfl⟩ := hcB
  obtain ⟨β', hβ', rfl⟩ := hcK
  obtain ⟨P0, hP0, hAP0⟩ := AA.lat
  have hint : ∀ {F : N → C}, F ∈ AA.carrier → ∀ x, ∃ r : R, algebraMap R C r = F x :=
    fun hF x => AA.le_int hF x
  have hK : v β'.det = v β.det := valuation_det_eq_of_span_eq_alt hv hβ (hAK.symm.trans hβ')
  have hmm1 : ∀ x, v (h3mm K β f x).det = 1 := by
    intro x
    have hdec : ∀ l, ∃ e : K → N ⧸ K → C,
        (∀ j, e j ∈ AA.carrier.comap (pullQ (R := R) K)) ∧
          g l = ∑ j, pullQ (R := R) K (e j) * f j := by
      intro l
      obtain ⟨b, ⟨hb, hgb⟩, -⟩ := hfu (g l) (hgA l)
      choose e he hbe using fun j => Submodule.mem_map.mp (hb j)
      refine ⟨e, he, ?_⟩
      rw [hgb]
      exact Finset.sum_congr rfl fun j _ => by rw [hbe j]
    choose e he hge using hdec
    let Bx : Matrix K K C := Matrix.of fun l j => e l j (x : N ⧸ K)
    have hmul : h3mm K β g x = Bx * h3mm K β f x := by
      ext l m
      simp only [h3mm, Matrix.of_apply, Matrix.mul_apply, Bx]
      rw [hge l, cosetCoordinates_sum, Finset.sum_apply]
      simp only [cosetCoordinates_pullbackQuotient_mul, Pi.smul_apply, smul_eq_mul]
    have hB1 : v Bx.det ≤ 1 := valuation_det_le_one_of_integral_entries hv Bx fun l j => by
      obtain ⟨r, hr⟩ := hint (Submodule.mem_comap.mp (he l j)) x
      exact ⟨r, hr⟩
    have hF1 : v (h3mm K β f x).det ≤ 1 := valuation_det_le_one_of_integral_entries hv _ fun j m =>
      hint (cosetCoordinates_mem AA K β hβ hAK (hfA j) m) x
    have h := hgdet x
    rw [hmul, Matrix.det_mul, map_mul, mul_comm] at h
    exact eq_one_of_le_one_of_mul_eq_one hF1 hB1 h
  let e : K × (N ⧸ K) ≃ N := (Equiv.prodComm _ _).trans (quotientProdSubgroupEquiv K)
  have he_apply : ∀ p : K × (N ⧸ K), e p = p.2.out + p.1 := fun p => rfl
  let Φ : Matrix N N C := fun x n => Q (x : N ⧸ K) (e.symm n).2 * f (e.symm n).1 x
  have hspan : AA.carrier = Submodule.span R (Set.range fun n x => Φ x n) := by
    apply le_antisymm
    · intro G hG
      obtain ⟨b, ⟨hb, hGb⟩, -⟩ := hfu G hG
      rw [hGb]
      refine sum_mem fun j _ => ?_
      obtain ⟨b', hb', hbb'⟩ := Submodule.mem_map.mp (hb j)
      rw [hQ] at hb'
      obtain ⟨r, hr⟩ := (Submodule.mem_span_range_iff_exists_fun R).mp hb'
      set_option synthInstance.maxHeartbeats 100000 in
        rw [← hbb', ← hr, map_sum, Finset.sum_mul]
      refine sum_mem fun s _ => ?_
      rw [map_smul, smul_mul_assoc]
      refine Submodule.smul_mem _ _ (Submodule.subset_span ⟨e (j, s), ?_⟩)
      funext x
      simp only [Φ, Equiv.symm_apply_apply]
      rfl
    · rw [Submodule.span_le]
      rintro _ ⟨n, rfl⟩
      have h1 : (fun q : N ⧸ K => Q q (e.symm n).2) ∈ AA.carrier.comap (pullQ (R := R) K) := by
        rw [hQ]
        exact Submodule.subset_span ⟨_, rfl⟩
      exact AA.mul_mem _ _ h1 (hfA _)
  have hdetΦ : v Φ.det = v Q.det ^ Fintype.card K * v β.det ^ Fintype.card (N ⧸ K) := by
    rw [← Matrix.det_submatrix_equiv_self e Φ]
    have hblk : Φ.submatrix e e = Matrix.blockDiagonal (fun q : N ⧸ K =>
        β * (h3mm K β f q.out)ᵀ) * Matrix.kroneckerMap (· * ·) (1 : Matrix K K C) Q := by
      ext ⟨k, q⟩ ⟨j, s⟩
      show Q ((e (k, q) : N) : N ⧸ K) (e.symm (e (j, s))).2 * f (e.symm (e (j, s))).1 (e (k, q)) = _
      rw [Equiv.symm_apply_apply, he_apply]
      dsimp only
      rw [quotient_out_add_coe K q k, cosetCoordinates_expand K β hβ (f j) q.out k, Matrix.mul_apply]
      simp only [Fintype.sum_prod_type, Matrix.blockDiagonal_apply, Matrix.kroneckerMap_apply,
        Matrix.one_apply, ite_mul, zero_mul, mul_ite, mul_one, mul_zero, one_mul,
        Finset.sum_ite_eq, Finset.sum_ite_eq', Finset.mem_univ, if_true, Finset.sum_const_zero]
      conv_rhs => rw [Finset.sum_eq_single j (fun b _ hb => by simp [hb]) (by simp)]
      simp only [eq_self_iff_true, if_true, Finset.sum_ite_eq, Finset.mem_univ]
      rw [mul_comm]
      rfl
    have hq : ∀ q : N ⧸ K, v (β * (h3mm K β f q.out)ᵀ).det = v β.det := by
      intro q
      rw [Matrix.det_mul, Matrix.det_transpose, map_mul, hmm1, mul_one]
    rw [hblk, Matrix.det_mul, Matrix.det_blockDiagonal, Matrix.det_kronecker, Matrix.det_one,
      one_pow, one_mul, map_mul, map_prod, map_pow]
    simp only [hq, Finset.prod_const, Finset.card_univ]
    ring
  have h1 := valuation_det_eq_of_span_eq_alt hv hP0 (hAP0.symm.trans hP)
  have h2 := valuation_det_eq_of_span_eq_alt hv hP0 (hAP0.symm.trans hspan)
  rw [h1, ← h2, hdetΦ, hK]

end ReciprocityTheory.PGsh.L2
end
end

-- bundled from ReciprocityTheory.DualLattices.KilledGen
section
noncomputable section

namespace ReciprocityTheory.PGsh.Up

theorem killedGen : KilledGenStatement := by
  intro C _ v R _ _ hv M _ _ x d c hx hy hc
  obtain ⟨y, hy⟩ := hy
  have h := prod_le_of_gen hv hx y hy (fun _ => c) (fun i => ⟨0, by simp [hc]⟩)
  simpa [Finset.prod_const, Finset.card_univ, Fintype.card_fin] using h

end ReciprocityTheory.PGsh.Up
end
end

