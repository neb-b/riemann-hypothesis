module

public import Formalism.SharpRestriction.GrowthBounds.BinomialRatio.Bundle0003
public import Formalism.SharpRestriction.GrowthBounds.RootWeights.ValuationNonnegIffIntegral
public import Formalism.GradedWeylDivisibility.FinalD

@[expose] public section

-- bundled from Formalism.SharpRestriction.GrowthBounds.BinomialRatio.CountDefs
section
noncomputable section

namespace Formalism.MainNotions.ColumnSystems.Pf

open Formalism.MainNotions.G

def Strip {r : ℕ} (nu mu : Fin r → ℤ) (g : ℕ) : Prop :=
  (∀ i, mu i ≤ nu i) ∧ (∀ i j : Fin r, i.val + 1 = j.val → nu j ≤ mu i) ∧ ∑ i, nu i - ∑ i, mu i = (g : ℤ)

def wdim {r : ℕ} (lam : Fin r → ℤ) : ℚ :=
  ∏ i : Fin r, ∏ j : Fin r, if i < j then ((lam i : ℚ) - (lam j : ℚ) + (j : ℚ) - (i : ℚ)) / ((j : ℚ) - (i : ℚ)) else 1

def IsChain {N r : ℕ} (LL : ChainLetters N) (ka : Fin (N + 1) → Fin r → ℤ) : Prop :=
  ka 0 = 0 ∧ ∀ i : Fin N, if LL.vec i then Strip (ka i.succ) (ka i.castSucc) (LL.deg i)
    else Strip (ka i.castSucc) (ka i.succ) (LL.deg i)

def ChainOK {N r : ℕ} [NeZero r] {q : ℕ} (J : Fin q → ℕ) (M : Fin q → WithTop ℤ) (ka : Fin (N + 1) → Fin r → ℤ) : Prop :=
  ∀ k, ((ka (finPos N (J k)) 0 : ℤ) : WithTop ℤ) ≤ M k


open Classical in
def chainSum {N r : ℕ} [NeZero r] (LL : ChainLetters N) {q : ℕ} (J : Fin q → ℕ) (M : Fin q → WithTop ℤ) : ℚ :=
  ∑ᶠ ka : Fin (N + 1) → Fin r → ℤ, if IsChain LL ka ∧ ChainOK J M ka then wdim (ka (Fin.last N)) else 0

def sdXi (r g : ℕ) : ℕ := Nat.choose (g + r - 1) (r - 1)


open Classical in
def BlockRankAt : Prop :=
  ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (N r : ℕ) [NeZero r] (D : BlockData N),
    Module.finrank (KK O) (Submodule.span (KK O)
        ((D.SSZ O (r := r) : Submodule O (MvPolynomial (BVar N r D.T.t) (KK O))) :
          Set (MvPolynomial (BVar N r D.T.t) (KK O)))) =
      ∑ᶠ x : (Fin D.T.t → ℕ) × ℕ, if D.LevelOK x.1 x.2 then
        Module.finrank (KK O) (Yjt (KK O) (r := r) (D.lettersAt x.1 x.2) D.T.J D.T.thr) * sdXi r (D.B - x.2) else 0

def DimYAt : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (_S : UniformizedDVR p O)
    (N r : ℕ) [NeZero r] (LL : ChainLetters N) (q : ℕ) (J : Fin q → ℕ)
    (M : Fin q → WithTop ℤ), (∀ k, J k ≤ N) →
    (Module.finrank (KK O) (Yjt (KK O) (r := r) LL J M) : ℚ) = chainSum (r := r) LL J M

def StWeylAt : Prop :=
  ∀ (n N : ℕ) (LL : Letters (Fin N)) (B : Fin N → ℕ) (P : PPath n N LL B),
    (Nat.card {I : ℤ → Finset (Fin n) // IsSt P.mu I} : ℚ) = wdim (pEnd P.mu)


open Classical in
def NumBranchAt : Prop :=
  ∀ (r : ℕ) (mu : Fin (r + 1) → ℤ), Antitone mu →
    wdim mu = ∑ᶠ lam : Fin r → ℤ, if (∀ i : Fin r, mu i.succ ≤ lam i ∧ lam i ≤ mu i.castSucc) then wdim lam else 0

def ChainDimAt : Prop :=
  ∀ (N r : ℕ) [NeZero r] (LL : ChainLetters N),
    chainSum (r := r) LL (q := 0) Fin.elim0 Fin.elim0 = ∏ i, (sdXi r (LL.deg i) : ℚ)


open Classical in
def chainCount (C0 CE1 CE2 : ℝ) (X : Loc) [NeZero X.m] (j : Fin (numSeg X.TT)) (m : ℝ)
    (rz ry : Fin (segS X.TT j) → Fin (X.m + 1) → ℕ) : ℚ :=
  ∑ᶠ b : SegBlock (segS X.TT j) X.m,
    if Kept X.p X.m (X.seg C0 CE1 CE2 j) (segATop X.TT X.aT j) b ∧ b.rz = rz ∧ b.ry = ry then
      (let D := blockData X.p (X.seg C0 CE1 CE2 j) (segATop X.TT X.aT j) (segAPlus X.TT X.aT j) m b
       ∑ᶠ x : (Fin D.T.t → ℕ) × ℕ, if D.LevelOK x.1 x.2 then
        chainSum (r := X.m) (D.lettersAt x.1 x.2) D.T.J D.T.thr * (sdXi X.m (D.B - x.2) : ℚ) else 0)
    else 0

def CountUpAt (C0 CYb Cde Ck CD Cb CE1 CE2 Cc : ℝ) : Prop :=
  ∀ (X : Loc) [NeZero X.m], D1num X → HIext C0 CYb Cde Ck CD Cb X → CBound Cc X →
    ∀ (j : Fin (numSeg X.TT)) (m : ℝ), 0 ≤ m →
    ∀ rz ry : Fin (segS X.TT j) → Fin (X.m + 1) → ℕ,
      DigitsOK X.p (X.seg C0 CE1 CE2 j) (segATop X.TT X.aT j) (digitBlock rz ry) →
      chainCount C0 CE1 CE2 X j m rz ry ≤ (mmB C0 CE1 CE2 X j rz ry : ℚ)

def CountLowAt (C0 CYb Cde Ck CD Cb CE1 CE2 Cc : ℝ) : Prop :=
  ∀ (X : Loc) [NeZero X.m], D1num X → HIext C0 CYb Cde Ck CD Cb X → CBound Cc X →
    ∀ (j : Fin (numSeg X.TT)) (m : ℝ), 0 ≤ m →
    (⌈m⌉₊ : ℝ) ≤ ((X.seg C0 CE1 CE2 j).A0 X.p : ℝ) * X.N1 * X.La C0 / X.k →
    ∀ rz ry : Fin (segS X.TT j) → Fin (X.m + 1) → ℕ,
      DigitsOK X.p (X.seg C0 CE1 CE2 j) (segATop X.TT X.aT j) (digitBlock rz ry) →
      lowFac C0 CE1 CE2 X j ⌈m⌉₊ * (mmB C0 CE1 CE2 X j rz ry : ℝ) ≤ ((chainCount C0 CE1 CE2 X j m rz ry : ℚ) : ℝ)

def RestCountUp : Prop := TransportedAlt fun C0 CYb Cde Ck CD Cb CE1 CE2 _ Cc => CountUpAt C0 CYb Cde Ck CD Cb CE1 CE2 Cc
def RestCountLow : Prop := TransportedAlt fun C0 CYb Cde Ck CD Cb CE1 CE2 _ Cc => CountLowAt C0 CYb Cde Ck CD Cb CE1 CE2 Cc

end Formalism.MainNotions.ColumnSystems.Pf
end
end

-- bundled from Formalism.SharpRestriction.GrowthBounds.BinomialRatio.FactorsOfPerturb
section
noncomputable section

namespace Formalism.MainNotions.ColumnSystems.Pf

open Formalism.MainNotions.G Formalism.MainNotions.G.GLWeightTheory

section Perturb

variable {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]

theorem nv_irr {w : O} (hw : Irreducible w) : dvrOrderNat w = 1 := by
  unfold dvrOrderNat
  rw [IsDiscreteValuationRing.addVal_uniformizer hw]
  rfl

theorem ramE_two {p : ℕ} {w : O} (hw : Irreducible w) (h2 : w ^ 2 = (p : O)) : ramE p O = 2 := by
  unfold ramE
  rw [← h2, IsDiscreteValuationRing.addVal_pow, IsDiscreteValuationRing.addVal_uniformizer hw]
  rfl

theorem vLEO_iff {p : ℕ} {w : O} (hw : Irreducible w) (h2 : w ^ 2 = (p : O)) {x : O} (hx : x ≠ 0) (D : ℝ) :
    vLEO p x D ↔ (dvrOrderNat x : ℝ) / 2 ≤ D := by
  have h1 : ordW (algebraMap O (KK O) x) = (((dvrOrderNat x : ℤ) - (dvrOrderNat (1 : O) : ℤ) : ℤ) : WithTop ℤ) :=
    ord_eq_order_sub_of_fraction _ x 1 hx one_ne_zero (by rw [map_one, mul_one])
  have h0 : dvrOrderNat (1 : O) = 0 := by
    unfold dvrOrderNat
    rw [IsDiscreteValuationRing.addVal_one]
    rfl
  have hv : vO p x = (((dvrOrderNat x : ℚ) / 2 : ℚ) : WithTop ℚ) := by
    unfold vO vK
    rw [h1, h0, ramE_two hw h2]
    simp
  unfold vLEO
  rw [hv]
  constructor
  · rintro ⟨q, hq, hqD⟩
    have hq' : q = (dvrOrderNat x : ℚ) / 2 := (WithTop.coe_inj.mp hq).symm
    subst hq'
    push_cast at hqD
    exact hqD
  · intro h
    exact ⟨_, rfl, by push_cast; exact h⟩

theorem eq_unit_pow {w : O} (hw : Irreducible w) {x : O} (hx : x ≠ 0) : ∃ u : Oˣ, x = (u : O) * w ^ dvrOrderNat x := by
  obtain ⟨n, u, rfl⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hx hw
  refine ⟨u, ?_⟩
  have hn : dvrOrderNat ((u : O) * w ^ n) = n := by
    unfold dvrOrderNat
    rw [IsDiscreteValuationRing.addVal_mul, IsDiscreteValuationRing.addVal_pow,
      IsDiscreteValuationRing.addVal_uniformizer hw, IsDiscreteValuationRing.addVal_eq_zero_of_unit, zero_add]
    simp
  rw [hn]

theorem isUnit_one_add {n : ℕ} {w : O} (hw : Irreducible w) (N : Matrix (Fin n) (Fin n) O) :
    IsUnit (1 + w • N : Matrix (Fin n) (Fin n) O) := by
  rw [Matrix.isUnit_iff_isUnit_det]
  have hw0 : IsLocalRing.residue O w = 0 := by
    rw [IsLocalRing.residue_eq_zero_iff, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
    exact hw.1
  have hmap : (IsLocalRing.residue O).mapMatrix (1 + w • N) = 1 := by
    ext i j
    by_cases hij : i = j
    · subst hij
      simp [hw0]
    · simp [hij, hw0]
  rw [← IsLocalRing.residue_ne_zero_iff_isUnit, RingHom.map_det, hmap, Matrix.det_one]
  exact one_ne_zero

theorem factors_of_perturb {Kf V V' : Type} [Field Kf] [Algebra O Kf] [AddCommGroup V] [Module O V]
    [AddCommGroup V'] [Module O V'] {p : ℕ} {w : O} (hw : Irreducible w) (h2 : w ^ 2 = (p : O))
    (be : V → V' → Kf) (A : Submodule O V) (A' : Submodule O V') (n c : ℕ) (D : ℝ) (hD : 4 * D < (c : ℝ))
    (x : Fin n → V) (y : Fin n → V') (hx : ∀ i, x i ∈ A) (hy : ∀ i, y i ∈ A') (δ : Fin n → O)
    (hδ : ∀ i, δ i ≠ 0 ∧ vLEO p (δ i) D) (ν : Fin n → Fin n → O)
    (hT : ∀ i j, be (x i) (y j) = algebraMap O Kf ((if i = j then δ i else 0) + w ^ c * ν i j)) :
    FactorsLE p be A A' n D := by
  rcases Nat.eq_zero_or_pos n with hn | hn
  · exact Or.inl hn
  right
  refine ⟨x, y, hx, hy, ?_⟩
  choose u hu using fun i => eq_unit_pow hw (hδ i).1
  obtain ⟨k, hkdef⟩ : ∃ k : Fin n → ℕ, ∀ i, k i = dvrOrderNat (δ i) := ⟨_, fun _ => rfl⟩
  have hu' : ∀ i, δ i = (u i : O) * w ^ k i := fun i => by rw [hkdef]; exact hu i
  have hk : ∀ i, k i < c := by
    intro i
    have h := (vLEO_iff hw h2 (hδ i).1 D).mp (hδ i).2
    rw [← hkdef] at h
    have h0 : (0 : ℝ) ≤ (k i : ℝ) := Nat.cast_nonneg _
    have : (k i : ℝ) < c := by linarith
    exact_mod_cast this
  obtain ⟨i0, -, hi0⟩ := Finset.exists_max_image Finset.univ k ⟨⟨0, hn⟩, Finset.mem_univ _⟩
  obtain ⟨N, hNdef⟩ : ∃ N : Matrix (Fin n) (Fin n) O,
      ∀ i j, N i j = (((u i)⁻¹ : Oˣ) : O) * w ^ (c - k i - 1) * ν i j :=
    ⟨Matrix.of fun i j => (((u i)⁻¹ : Oˣ) : O) * w ^ (c - k i - 1) * ν i j, fun _ _ => rfl⟩
  obtain ⟨zl, hzdef⟩ : ∃ zl : Fin n → O, ∀ l, zl l = (u i0 : O) * (((u l)⁻¹ : Oˣ) : O) * w ^ (k i0 - k l) :=
    ⟨_, fun _ => rfl⟩
  obtain ⟨Q, hQ⟩ : ∃ Q : Matrix (Fin n) (Fin n) O, (1 + w • N) * Q = 1 := by
    obtain ⟨U, hU⟩ := isUnit_one_add hw N
    exact ⟨↑U⁻¹, by rw [← hU]; exact U.mul_inv⟩
  have hzl : ∀ l, δ l * zl l = δ i0 := by
    intro l
    have hle : k l ≤ k i0 := hi0 l (Finset.mem_univ _)
    rw [hu' l, hu' i0, hzdef]
    have hb : w ^ k i0 = w ^ k l * w ^ (k i0 - k l) := by
      rw [← pow_add, Nat.add_sub_cancel' hle]
    rw [hb]
    have hu1 : (u l : O) * (((u l)⁻¹ : Oˣ) : O) = 1 := Units.mul_inv (u l)
    linear_combination (u i0 : O) * w ^ k l * w ^ (k i0 - k l) * hu1
  have hD1 : ∀ i j, δ i * (w * N i j) = w ^ c * ν i j := by
    intro i j
    have hc : w ^ c = w ^ k i * w * w ^ (c - k i - 1) := by
      rw [← pow_succ, ← pow_add]
      congr 1
      have := hk i
      omega
    have hu1 : (u i : O) * (((u i)⁻¹ : Oˣ) : O) = 1 := Units.mul_inv (u i)
    rw [hNdef, hu' i, hc]
    linear_combination (w ^ k i * w * w ^ (c - k i - 1) * ν i j) * hu1
  have hB : ∀ i l, (if i = l then δ i else 0) + w ^ c * ν i l = δ i * (1 + w • N) i l := by
    intro i l
    rw [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, mul_add, hD1 i l, Matrix.one_apply, mul_ite, mul_one,
      mul_zero]
  refine ⟨δ i0, Q * Matrix.diagonal zl, (hδ i0).1, (hδ i0).2, fun i j => ?_⟩
  have hBM : ∑ l, δ i * (1 + w • N) i l * (Q * Matrix.diagonal zl) l j = if i = j then δ i0 else 0 := by
    have hmul : ∑ l, (1 + w • N) i l * (Q * Matrix.diagonal zl) l j =
        ((1 + w • N) * (Q * Matrix.diagonal zl)) i j := by
      rw [Matrix.mul_apply]
    simp_rw [mul_assoc (δ i)]
    rw [← Finset.mul_sum, hmul, ← Matrix.mul_assoc, hQ, Matrix.one_mul, Matrix.diagonal_apply]
    split_ifs with hij
    · exact hzl i
    · exact mul_zero _
  calc ∑ l, be (x i) (y l) * algebraMap O Kf ((Q * Matrix.diagonal zl) l j)
      = algebraMap O Kf (∑ l, δ i * (1 + w • N) i l * (Q * Matrix.diagonal zl) l j) := by
        set_option synthInstance.maxHeartbeats 100000 in
          rw [map_sum]
        refine Finset.sum_congr rfl fun l _ => ?_
        rw [hT, hB]
        simp only [map_mul]
    _ = if i = j then algebraMap O Kf (δ i0) else 0 := by
        rw [hBM]
        split_ifs <;> simp

end Perturb

theorem liftAt_of {C0 CYb Cde Ck CD Cb CE1 CE2 Cm Ct Cc : ℝ}
    (h : LiftVecAt C0 CYb Cde Ck CD Cb CE1 CE2 Cm Ct Cc) : LiftAt C0 CYb Cde Ck CD Cb CE1 CE2 Cm Ct Cc := by
  intro X _ W Qq O Kf _ _ _ _ _ _ _ _ _ _ ι σ jO w hS hH hC Dj g hD0 hBD hc e he
  obtain ⟨F, G, δ, hF, hG, hδ, hT⟩ := h X W Qq O Kf ι σ jO w hS hH hC Dj g hD0 hBD hc e he
  choose ν hν using hT
  let eI : Fin (∏ j, g j) ≃ (∀ j, Fin (g j)) := (Fintype.equivFinOfCardEq (by simp)).symm
  refine factors_of_perturb hS.2.1 hS.1.w_sq _ _ _ _ X.c _ hc (fun a => F (eI a)) (fun a => G (eI a))
    (fun a => hF _) (fun a => hG _) (fun a => δ (eI a)) (fun a => hδ _) (fun a b => ν (eI a) (eI b)) ?_
  intro a b
  rw [hν]
  simp only [Equiv.apply_eq_iff_eq]

theorem restLift_of (h : RestLiftVec) : RestLift :=
  TransportedAlt.mono (fun _ _ _ _ _ _ _ _ _ _ ⟨Ct0, h0, hCt⟩ => ⟨Ct0, h0, fun Ct h' => liftAt_of (hCt Ct h')⟩) h

end Formalism.MainNotions.ColumnSystems.Pf
end
end

-- bundled from Formalism.SharpRestriction.GrowthBounds.BinomialRatio.FinrankTensor
section
noncomputable section

namespace Formalism.MainNotions.ColumnSystems.Pf

open Formalism.MainNotions.G

theorem prodUp (m A : ℕ) :
    ∏ j : Fin m, (((A : ℚ) + ((j : ℕ) : ℚ) + 1) / (((j : ℕ) : ℚ) + 1)) = ((A + m).choose m : ℚ) := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [Fin.prod_univ_castSucc]
    simp only [Fin.val_castSucc, Fin.val_last]
    rw [ih]
    have h := Nat.add_one_mul_choose_eq (A + m) m
    have h' : (((A + m + 1) * (A + m).choose m : ℕ) : ℚ) = (((A + m + 1).choose (m + 1) * (m + 1) : ℕ) : ℚ) := by
      rw [h]
    push_cast at h'
    have hm : ((m : ℚ) + 1) ≠ 0 := by positivity
    rw [show A + (m + 1) = A + m + 1 from rfl]
    field_simp
    linarith

theorem prodDown (m B : ℕ) :
    ∏ j : Fin m, (((B : ℚ) + (m : ℚ) - ((j : ℕ) : ℚ)) / ((m : ℚ) - ((j : ℕ) : ℚ))) = ((B + m).choose m : ℚ) := by
  rw [← prodUp, ← Equiv.prod_comp Fin.revPerm]
  refine Finset.prod_congr rfl fun j _ => ?_
  have h : ((Fin.revPerm j : Fin m) : ℕ) + ((j : ℕ) + 1) = m := by
    simp only [Fin.revPerm_apply, Fin.val_rev]
    omega
  have h' : (((Fin.revPerm j : Fin m) : ℕ) : ℚ) + (((j : ℕ) : ℚ) + 1) = (m : ℚ) := by exact_mod_cast h
  rw [← h']
  congr 1 <;> ring

def wprod (n : ℕ) (nu : Fin n → ℕ) : ℚ :=
  ∏ i : Fin n, ∏ j : Fin n,
    if i < j then ((nu i : ℚ) - (nu j : ℚ) + (j : ℚ) - (i : ℚ)) / ((j : ℚ) - (i : ℚ)) else 1

theorem ratio_one {n : ℕ} {i j : Fin n} (h : i < j) (x : ℚ) :
    (x - x + ((j : ℕ) : ℚ) - ((i : ℕ) : ℚ)) / (((j : ℕ) : ℚ) - ((i : ℕ) : ℚ)) = 1 := by
  have h1 : ((i : ℕ) : ℚ) < ((j : ℕ) : ℚ) := by exact_mod_cast h
  have h2 : ((j : ℕ) : ℚ) - ((i : ℕ) : ℚ) ≠ 0 := by linarith
  rw [sub_self, zero_add]
  exact div_self h2

theorem wprod_vec (m d : ℕ) : wprod (m + 1) (fun i => if i = 0 then d else 0) = ((d + m).choose m : ℚ) := by
  unfold wprod
  rw [Fin.prod_univ_succ]
  have h2 : ∏ i : Fin m, ∏ j : Fin (m + 1),
      (if i.succ < j then
        ((((if i.succ = 0 then d else 0 : ℕ)) : ℚ) - (((if j = 0 then d else 0 : ℕ)) : ℚ) + (j : ℚ) - (i.succ : ℚ)) /
          ((j : ℚ) - (i.succ : ℚ)) else 1) = 1 := by
    apply Finset.prod_eq_one; intro i _
    apply Finset.prod_eq_one; intro j _
    split_ifs with h h1 h3 h3
    · exact absurd h1 (Fin.succ_ne_zero i)
    · exact absurd h1 (Fin.succ_ne_zero i)
    · subst h3; exact absurd h (Fin.not_lt_zero _)
    · exact ratio_one h _
    · rfl
  rw [h2, mul_one, Fin.prod_univ_succ, ← prodUp]
  simp only [lt_self_iff_false, if_false, one_mul, if_true]
  refine Finset.prod_congr rfl fun j _ => ?_
  rw [if_pos (Fin.succ_pos j), if_neg (Fin.succ_ne_zero j)]
  simp only [Fin.val_succ, Fin.val_zero, Nat.cast_zero, sub_zero, Nat.cast_add, Nat.cast_one]
  congr 1
  ring

theorem wprod_cov (m d : ℕ) :
    wprod (m + 1) (fun i => if i = Fin.last m then 0 else d) = ((d + m).choose m : ℚ) := by
  unfold wprod
  rw [Fin.prod_univ_castSucc]
  have h2 : ∏ j : Fin (m + 1),
      (if Fin.last m < j then
        ((((if Fin.last m = Fin.last m then 0 else d : ℕ)) : ℚ) - (((if j = Fin.last m then 0 else d : ℕ)) : ℚ) +
          (j : ℚ) - ((Fin.last m : Fin (m + 1)) : ℚ)) / ((j : ℚ) - ((Fin.last m : Fin (m + 1)) : ℚ)) else 1) = 1 := by
    apply Finset.prod_eq_one; intro j _
    rw [if_neg (not_lt.mpr (Fin.le_last j))]
  rw [h2, mul_one, ← prodDown]
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [Fin.prod_univ_castSucc]
  have h3 : ∏ j : Fin m,
      (if i.castSucc < j.castSucc then
        ((((if i.castSucc = Fin.last m then 0 else d : ℕ)) : ℚ) - (((if j.castSucc = Fin.last m then 0 else d : ℕ)) : ℚ) +
          (j.castSucc : ℚ) - (i.castSucc : ℚ)) / ((j.castSucc : ℚ) - (i.castSucc : ℚ)) else 1) = 1 := by
    apply Finset.prod_eq_one; intro j _
    rw [if_neg (Fin.castSucc_lt_last i).ne, if_neg (Fin.castSucc_lt_last j).ne]
    by_cases h : i.castSucc < j.castSucc
    · rw [if_pos h]
      exact ratio_one h _
    · rw [if_neg h]
  rw [h3, one_mul, if_pos (Fin.castSucc_lt_last i)]
  simp only [if_neg (Fin.castSucc_lt_last i).ne, if_true, Fin.val_castSucc, Fin.val_last, Nat.cast_zero, sub_zero]

theorem last_ne_zero {m : ℕ} (hm : 1 ≤ m) : Fin.last m ≠ 0 := by
  intro h
  have := congrArg Fin.val h
  simp at this
  omega

theorem finrank_letter {D : Formalism.BasicNotions.D7} (h3 : adm3 D) (K : Type) [Field K] [CharZero K] (m d : ℕ) (hm : 1 ≤ m)
    (vec : Bool) :
    Module.finrank K (Formalism.GradedWeylDivisibility.dualWeyl K (m + 1) (m + 1) (nuOf (letterWt m d vec))) = sd m d := by
  have hq : (Module.finrank K (Formalism.GradedWeylDivisibility.dualWeyl K (m + 1) (m + 1) (nuOf (letterWt m d vec))) : ℚ) = (sd m d : ℚ) := by
    cases vec with
    | true =>
      have hnu : nuOf (letterWt m d true) = fun i => if i = 0 then d else 0 := by
        funext i
        simp only [nuOf, letterWt, if_true, if_neg (last_ne_zero hm), sub_zero]
        split_ifs <;> simp
      have hanti : Antitone (nuOf (letterWt m d true)) := by
        rw [hnu]
        intro i j hij
        simp only
        split_ifs with h1 h2 <;> first | omega | skip
        exact absurd (Fin.le_zero_iff.1 (h1 ▸ hij)) h2
      rw [h3 K _ _ hanti, hnu]
      exact wprod_vec m d
    | false =>
      have hnu : nuOf (letterWt m d false) = fun i => if i = Fin.last m then 0 else d := by
        funext i
        simp only [nuOf, letterWt, Bool.false_eq_true, if_false, if_true]
        split_ifs <;> simp
      have hanti : Antitone (nuOf (letterWt m d false)) := by
        rw [hnu]
        intro i j hij
        simp only
        by_cases hj : j = Fin.last m
        · rw [if_pos hj]; exact Nat.zero_le _
        · have hi : i ≠ Fin.last m := fun h => hj (le_antisymm (Fin.le_last _) (h ▸ hij))
          rw [if_neg hj, if_neg hi]
      rw [h3 K _ _ hanti, hnu]
      exact wprod_cov m d
  exact_mod_cast hq

theorem finrank_tensor (Kf : Type) [Field Kf] (S : Type) [Fintype S] [DecidableEq S] (k n : ℕ)
    (ν : S → Fin n → ℕ) :
    Module.finrank Kf (Formalism.GradedWeylDivisibility.tensorLat Kf Kf fun s => Formalism.GradedWeylDivisibility.dualWeyl Kf k n (ν s)) =
      ∏ s, Module.finrank Kf (Formalism.GradedWeylDivisibility.dualWeyl Kf k n (ν s)) := by
  classical
  have hb := fun s : S => Formalism.GradedWeylDivisibility.sSBasis Kf k n (ν s)
  choose b hb1 _ using hb
  have : IsFractionRing Kf Kf :=
    IsLocalization.of_le_isUnit (fun x hx => IsUnit.mk0 x (nonZeroDivisors.ne_zero hx))
  obtain ⟨hli, hsp⟩ := Formalism.GradedWeylDivisibility.tensorBasis Kf Kf S k n (fun s => ↥(Formalism.GradedWeylDivisibility.ssIdx k n (ν s)))
    (fun s => Formalism.GradedWeylDivisibility.dualWeyl Kf k n (ν s)) b (fun s => (hb1 s).1) (fun s => (hb1 s).2.1)
  have : ∀ s : S, Fintype ↥(Formalism.GradedWeylDivisibility.ssIdx k n (ν s)) := fun s => (Formalism.GradedWeylDivisibility.sSIdxFinite k n (ν s)).fintype
  rw [← hsp, finrank_span_eq_card hli, Fintype.card_pi]
  refine Finset.prod_congr rfl fun s _ => ?_
  rw [← (hb1 s).2.1, finrank_span_eq_card (hb1 s).1]

theorem dimHH_of {D : Formalism.BasicNotions.D7} (h3 : adm3 D) : DimHHAt := by
  intro Kf _ _ n' m TT aT bT hm
  classical
  unfold dimHH VHH
  rw [finrank_tensor Kf (TT × Bool) (m + 1) (m + 1) (fun x => nuOf (hhWt m TT aT bT x))]
  have h1 : ∀ x : TT × Bool,
      Module.finrank Kf (Formalism.GradedWeylDivisibility.dualWeyl Kf (m + 1) (m + 1) (nuOf (hhWt m TT aT bT x))) =
        sd m (hhDeg aT bT x.1.val x.2) := fun x => finrank_letter h3 Kf m _ hm x.2
  rw [Finset.prod_congr rfl fun x _ => h1 x, Fintype.prod_prod_type]
  rw [← Finset.prod_coe_sort TT fun s => sd m (aT s) * sd m (bT s)]
  refine Finset.prod_congr rfl fun s _ => ?_
  rw [Fintype.prod_bool]
  unfold hhDeg
  by_cases he : Even s.val.val
  · simp [he]
  · simp [he, mul_comm]

theorem charZeroAt : CharZeroAt := by
  intro p n' W Qq O Kf _ _ _ _ _ _ _ _ _ _ ι σ jO w hS
  have hw : Irreducible w := hS.2.1
  have hpw : w ^ 2 = (p : O) := hS.1.w_sq
  have hp0 : (p : O) ≠ 0 := by rw [← hpw]; exact pow_ne_zero _ hw.ne_zero
  have hpu : ¬ IsUnit (p : O) := by
    rw [← hpw]
    intro h
    exact hw.not_isUnit (isUnit_of_mul_isUnit_left (by rwa [pow_two] at h))
  have hO : CharZero O := by
    obtain ⟨c, hc⟩ := CharP.exists O
    rcases CharP.char_is_prime_or_zero O c with h | h
    · exfalso
      have hc0 : (c : O) = 0 := CharP.cast_eq_zero O c
      by_cases hcp : c = p
      · exact hp0 (hcp ▸ hc0)
      · have hcop : Nat.Coprime c p := (Nat.coprime_primes h hS.1.prime).2 hcp
        obtain ⟨a, b, hab⟩ := Nat.isCoprime_iff_coprime.2 hcop
        have h1 : ((a * c + b * p : ℤ) : O) = 1 := by rw [hab]; simp
        push_cast at h1
        rw [hc0, mul_zero, zero_add] at h1
        exact hpu (IsUnit.of_mul_eq_one_right _ h1)
    · subst h
      exact CharP.charP_to_charZero O
  have hfr : IsFractionRing O Kf := hS.1.frac_O
  exact charZero_of_injective_algebraMap (IsFractionRing.injective O Kf)

end Formalism.MainNotions.ColumnSystems.Pf
end
end

