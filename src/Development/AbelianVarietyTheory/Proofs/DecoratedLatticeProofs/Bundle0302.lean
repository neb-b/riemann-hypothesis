module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ExistsUnitarySupportedAtPlaceOfMulEqIdem
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0009
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0010
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0203
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0028
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.BesselCharacterGenericCharacterLaws
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.WittSmallGroupEmbeddingMemPointwiseStabilizerIso
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0023
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0289
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0060
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0064
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.SelfDualLatticePairingDual
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0074
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IdempotentMulEqZeroOfOrthogonal
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1206
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LatticeIsometrySignFirst
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0292
public import Formalism.LocalToGlobal.KernelLattices.KernelLocalFactors.AlternatingFormStandardHermitian
public import Formalism.LocalToGlobal.IndefiniteReal.FinitePlaces.Bundle0012
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0058
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0059
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0274

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LocalFlatMapDualColumnMultiplicationLaws
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory Matrix ValuativeRel GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.LocMod

noncomputable section

namespace GlobalTheory.FlatColLaw

variable {D : D7} {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem e_iota (p : Place D k) (x : k) : p.e * p.ι x = p.ι x := by rw [← p.ι_π, p.π_ι]

theorem iota_mul (p : Place D k) (x : k) (m : AE D) : p.ι x * m = p.ι (x * p.π m) := by
  have h2 := p.ι_π (p.ι x * m)
  rw [map_mul, p.π_ι] at h2
  rw [h2, ← mul_assoc, e_iota]

theorem xi_ne (p : Place D k) : p.xi ≠ 0 := by
  have h : p.xi * p.pr D.host.xi0⁻¹ = 1 := by
    rw [Place.xi, Place.pr, Place.pr, ← map_mul, ← map_mul, mul_inv_cancel₀ (GlobalTheory.DualPairCompare.embedding_xi_zero_ne_zero D), map_one,
      map_one]
  exact left_ne_zero_of_mul_eq_one h

theorem map_iota_mul (p : Place D k) {a b c : ℕ} (zk : Matrix (Fin a) (Fin b) k) (x : Mx D b c) :
    (zk.map p.ι : Mx D a b) ⬝ x = (zk * x.map p.π).map p.ι := by
  ext i j
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [Matrix.mul_apply, Matrix.map_apply, map_sum, iota_mul]

theorem trace_map_iota (p : Place D k) {a : ℕ} (x : Matrix (Fin a) (Fin a) k) :
    (x.map p.ι : Mx D a a).trace = p.ι x.trace := by
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [Matrix.trace, Matrix.diag, Matrix.map_apply, map_sum]

theorem map_iota_pi (p : Place D k) {a b : ℕ} (x : Matrix (Fin a) (Fin b) k) : (x.map p.ι).map p.π = x := by
  ext i j
  exact p.π_ι _

theorem hO_extY {S S₀ T : HSp D} {ρ : ℕ} (d : HypDec S S₀ ρ) (w : WO S T) (a : Mx D T.rank ρ) :
    hO S T w (d.extY T a) = pairS T (w ⬝ d.jX) a := by
  rw [d.hO_coordS]
  simp only [HypDec.extY_apply, Matrix.mul_assoc, HypDec.pY_jY, HypDec.pY_j0, HypDec.pY_jX, Matrix.mul_one,
    Matrix.mul_zero, pairS, hO_eq_trace S₀, adj_zero, Matrix.zero_mul, trace_zero, add_zero]

theorem pairS_giA_adj (T : HSp D) {ρ : ℕ} (x : Mx D T.rank ρ) (z : Mx D ρ T.rank) :
    pairS T x (giA T ⬝ adj z) = (z ⬝ x).trace := by
  rw [pairS, adj_mul, adj_adj, adj_giA, Matrix.mul_assoc, giA_gA_cancel]

theorem psi_sympl_extY (p : Place D k) {ψ : AddChar (AF D.host.F) ℂ} {ψk : AddChar k Circle} (hχ : p.IsChar ψ ψk)
    {S S₀ T : HSp D} {ρ : ℕ} (d : HypDec S S₀ ρ) (zk : Matrix (Fin ρ) (Fin T.rank) k) (w : WO S T) :
    ψ (symplO S T w (d.extY T (giA T ⬝ adj (zk.map p.ι : Mx D ρ T.rank)))) =
      (ψk ((zk * (w ⬝ d.jX : Mx D T.rank ρ).map p.π).trace) : ℂ) := by
  rw [hχ, symplO, hO_extY, pairS_giA_adj, map_iota_mul, trace_map_iota]
  rfl

theorem isHalf_mul_left {e : AE D} {a b c : ℕ} (x : Mx D a b) {y : Mx D b c} (h : IsHalf e y) : IsHalf e (x ⬝ y) := by
  intro i j
  simp only [Matrix.mul_apply, Finset.mul_sum]
  exact Finset.sum_congr rfl fun l _ => by rw [mul_left_comm, h l j]

theorem isHalf_mul_right {e : AE D} {a b c : ℕ} {x : Mx D a b} (y : Mx D b c) (h : IsHalf e x) : IsHalf e (x ⬝ y) := by
  intro i j
  simp only [Matrix.mul_apply, Finset.mul_sum]
  exact Finset.sum_congr rfl fun l _ => by rw [← mul_assoc, h i l]

theorem isHalf_adj (p : Place D k) {a b : ℕ} (zk : Matrix (Fin a) (Fin b) k) :
    IsHalf (cA D p.e) (adj (zk.map p.ι : Mx D a b)) := fun i j =>
  (map_mul (cA D) p.e (p.ι (zk j i))).symm.trans (congrArg (cA D) (e_iota p _))

theorem exists_mxAt (p : Place D k) : ∃ v : GlobalTheory.FinPl.Pl D, ∀ (a b : ℕ) (x : Mx D a b), IsHalf (cA D p.e) x →
    GlobalTheory.FinPl.MxAt (· = v) x := by
  obtain ⟨_, h0, v, ε, h1, h2⟩ := p.split
  obtain rfl := GlobalTheory.AdelicU.Supp.isPlaceIdem_iff.1 h1
  refine ⟨v, fun a b x hx i j => GlobalTheory.FinPl.Model.mem_idAt_iff.2 ?_⟩
  rw [← h2, add_mul, hx i j, ← hx i j, ← mul_assoc, h0, zero_mul, zero_add]

theorem trace_mul_uni {ρ : ℕ} (M : Mx D ρ ρ) (hM : ∀ i j, j < i → M i j = 0) (u : UX D ρ) :
    (M ⬝ u.1.1).trace = M.trace := by
  refine Finset.sum_congr rfl fun i _ => ?_
  have hu := u.2
  rw [Matrix.diag_apply, Matrix.diag_apply, GlobalTheory.UniIndexPrime.diag_mul hM (fun a b h => (hu a b).1 h), (hu i i).2, mul_one]

theorem col_mul {K m l o o' : Type} [Field K] [Fintype l] (M : Matrix m l K) (E : Matrix l o K) (F : Matrix l o' K) (j : o)
    (j' : o') {κ : K} (hκ : κ ≠ 0) (h : ∀ x, F x j' = κ * E x j) (r : m) : (M * E) r j = κ⁻¹ * (M * F) r j' := by
  simp only [Matrix.mul_apply, h, Finset.mul_sum]
  exact Finset.sum_congr rfl fun x _ => by field_simp

theorem row_mul {K m l o : Type} [Field K] [Fintype l] {ρ : ℕ} (i₀ : Fin ρ) (a : K) (G : Matrix m l K) (r : m)
    (X : Matrix l o K) (i : Fin ρ) (j : o) :
    ((Matrix.of fun i' β => if i' = i₀ then a * G r β else 0 : Matrix (Fin ρ) l K) * X) i j =
      if i = i₀ then a * (G * X) r j else 0 := by
  by_cases h : i = i₀ <;> simp [Matrix.mul_apply, h, Finset.mul_sum, mul_assoc]

theorem trace_row_mul {K m l : Type} [Field K] [Fintype l] {ρ : ℕ} (i₀ : Fin ρ) (a : K) (G : Matrix m l K) (r : m)
    (X : Matrix l (Fin ρ) K) :
    ((Matrix.of fun i' β => if i' = i₀ then a * G r β else 0 : Matrix (Fin ρ) l K) * X).trace = a * (G * X) r i₀ := by
  simp only [Matrix.trace, Matrix.diag_apply, row_mul, Finset.sum_ite_eq', Finset.mem_univ, if_true]

theorem law_dual_col : ∀ (D : D7), FlatLaw D → GlobalTheory.FinPl.FlatLaws D → OmLoc D → ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k] (p : Place D k) (ν : Measure k), ν.IsAddHaarMeasure → ∀ (ψ : AddChar (AF D.host.F) ℂ) (ψk : AddChar k Circle), p.IsChar ψ ψk → ∀ (ρ : ℕ) (B : BesLev D ρ) (J : JacLev D ρ) (st : StepBF ψ B J) (s : k), s ≠ 0 → ∀ (n n' : Type) [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n'] (c : ℕ) (FA : Frame k B.A.rank n') (F₀ : Frame k B.V₀.rank (n' ⊕ Unit)) (FV : Frame k B.V.rank (n' ⊕ Fin (c + 1))) (G₀ : Frame k J.W₀.rank n) (FW : Frame k J.W.rank (n ⊕ Fin c)), p.IsCoreFrame B s FA F₀ → p.IsBesFrame B s FA FV → p.IsJacFrame J s (p.hz B) G₀ FW → ∀ (Tm : SB (Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k) →ₗ[ℂ] (WO B.V J.W → ℂ)), p.IsModel ψ FV FW Tm → ∀ (r : n ⊕ Fin c) (q : n' ⊕ Fin (c + 1)), (∃ i, q = Sum.inr i ∧ i.val < ρ ∧ ¬ GlobalTheory.RootEx.Free (ρ + 1) (r, q)) → ∀ (b : k) (Φ Φ' : SB (Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k)), (∀ t, Φ'.1 t = (ψk (b * (t r q - GlobalTheory.RootEx.basePt c (0 : Matrix n n' k) r q)) : ℂ) * Φ.1 t) → flatBF st (Tm Φ') = flatBF st (Tm Φ) := by
  intro D _ hFL _ k _ _ _ _ _ _ p ν _ ψ ψk hχ ρ B J st s hs n n' _ _ _ _ c FA F₀ FV G₀ FW _ hbes hjac Tm hTm r q hq b Φ Φ' hΦ'
  obtain ⟨i, rfl, hi, hfree⟩ := hq
  have hc : c = 2 * ρ := hjac.1
  have hκ : ∀ m : ℕ, s * p.xi ^ m ≠ 0 := fun m => mul_ne_zero hs (pow_ne_zero _ (xi_ne p))
  let i₀ : Fin ρ := ⟨i.val, hi⟩
  let zk : Matrix (Fin ρ) (Fin J.W.rank) k :=
    Matrix.of fun i' β => if i' = i₀ then b * (s * p.xi ^ (ρ - i.val)) * FW.γ r β else 0
  let a : Mx D J.W.rank ρ := giA J.W ⬝ adj (zk.map p.ι : Mx D ρ J.W.rank)
  have ha : IsHalf (cA D p.e) a := isHalf_mul_left _ (isHalf_adj p zk)
  have hy : IsHalf (cA D p.e) (B.d.extY J.W a) := isHalf_mul_right _ ha
  have hW : ∀ j : Fin ρ, (FW.γ * J.d.jX.map p.π) r j = (s * p.xi ^ (ρ - j.val))⁻¹ *
      (1 : Matrix (n ⊕ Fin c) (n ⊕ Fin c) k) r (Sum.inr ⟨j.val, by omega⟩) := fun j => by
    rw [← FW.γβ]
    exact col_mul _ _ _ _ _ (hκ _) (hjac.2.2.1 j ⟨j.val, by omega⟩ rfl) r
  have hB : ∀ t, ψ (symplO B.V J.W (p.up FV FW t) (B.d.extY J.W a)) = (ψk (b * t r (Sum.inr i)) : ℂ) := fun t => by
    rw [psi_sympl_extY p hχ, trace_row_mul, Place.up, map_iota_mul, map_iota_pi, ← Matrix.mul_assoc, ← Matrix.mul_assoc,
      ← Matrix.mul_assoc, FW.γβ, Matrix.one_mul,
      col_mul _ _ FV.β i₀ (Sum.inr i) (hκ _) (hbes.2.2.1 i₀ i rfl), Matrix.mul_assoc, FV.γβ, Matrix.mul_one, mul_assoc,
      mul_inv_cancel_left₀ (hκ _)]
  have hD : ψ (symplO B.V J.W (B.d.extX J.W (xZero J.d)) (B.d.extY J.W a)) =
      (ψk (b * basePt c (0 : Matrix n n' k) r (Sum.inr i)) : ℂ) := by
    rw [psi_sympl_extY p hχ, trace_row_mul, HypDec.extX_apply, Matrix.mul_assoc, HypDec.pX_jX, Matrix.mul_one, xZero, hW,
      mul_assoc, mul_inv_cancel_left₀ (hκ _)]
    congr 3
    rcases r with r | r
    · simp [basePt]
    · simp [basePt, Matrix.one_apply, Fin.ext_iff, i₀]
  have hU : GlobalTheory.FinPl.UInv J.W (xZero J.d) a := fun u => by
    rw [pairS_giA_adj, pairS_giA_adj, ← Matrix.mul_assoc]
    refine trace_mul_uni _ (fun i' j hj => ?_) u
    rw [map_iota_mul, Matrix.map_apply, row_mul]
    split_ifs with h
    · subst h
      rw [xZero, hW, Matrix.one_apply_ne, mul_zero, mul_zero, map_zero]
      rintro rfl
      exact hfree hj
    · exact map_zero _
  obtain ⟨v, hv⟩ := exists_mxAt p
  have hlaw := ((hFL ψ (· = v)).1 ρ B J st).Heisenberg₂.dual _ (hTm.theta Φ) a (hv _ _ a ha) hU
  have hmod := hTm.modul _ hy Φ ((ψk (b * basePt c (0 : Matrix n n' k) r (Sum.inr i)) : ℂ) • Φ') fun t => by
    rw [hB, Submodule.coe_smul, Pi.smul_apply, smul_eq_mul, hΦ', ← mul_assoc, ← Circle.coe_mul, ← AddChar.map_add_eq_mul,
      ← mul_add, add_sub_cancel]
  rw [← hmod, hD, map_smul, GlobalTheory.HandHom.flatBF_smul] at hlaw
  exact smul_right_injective _ (Circle.coe_ne_zero _) hlaw

end GlobalTheory.FlatColLaw

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.MemFlagUnipotentRadicalOfBesselNormalFrameLocal
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory Matrix ValuativeRel GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.LocMod

namespace GlobalTheory.LocFlag

theorem conj_vanish {k : Type} [CommRing k] {Z Y M : Type} [Fintype Z] [DecidableEq Z] [Fintype Y] [DecidableEq Y]
    [Fintype M] [DecidableEq M] (lv : Z → ℕ) (lw : Y → ℕ) (P : Matrix Z M k) (J : Matrix M Z k) (β : Matrix M Y k)
    (γ : Matrix Y M k) (hPJ : P * J = 1) (hJP : J * P = 1) (hβγ : β * γ = 1) (hγβ : γ * β = 1)
    (hA : ∀ a r, lv a ≠ lw r → (P ⬝ β) a r = 0) (q : Matrix Y Y k)
    (hq : ∀ r s, lw s ≤ lw r → q r s = (1 : Matrix Y Y k) r s) (a b : Z) (hab : lv b ≤ lv a) :
    (P ⬝ (β * q * γ - 1) ⬝ J) a b = 0 := by
  have hAB : (P * β) * (γ * J) = 1 := by
    rw [Matrix.mul_assoc, ← Matrix.mul_assoc β, hβγ, Matrix.one_mul, hPJ]
  have hBA : (γ * J) * (P * β) = 1 := by
    rw [Matrix.mul_assoc, ← Matrix.mul_assoc J, hJP, Matrix.one_mul, hγβ]
  have hB : ∀ t b, lw t ≠ lv b → (γ ⬝ J) t b = 0 := by
    intro t b h
    generalize P * β = A at hA hAB hBA
    generalize γ * J = B at hAB hBA
    have h1 : diagonal (fun a => if lv a = lv b then (1 : k) else 0) * A =
        A * diagonal (fun r => if lw r = lv b then (1 : k) else 0) := by
      ext a r
      rw [diagonal_mul, mul_diagonal]
      by_cases e : lv a = lw r
      · rw [e, mul_comm]
      · rw [hA a r e, mul_zero, zero_mul]
    have h2 : B * diagonal (fun a => if lv a = lv b then (1 : k) else 0) =
        diagonal (fun r => if lw r = lv b then (1 : k) else 0) * B := by
      rw [← Matrix.mul_one (B * _), ← hAB, ← Matrix.mul_assoc, Matrix.mul_assoc B, h1, ← Matrix.mul_assoc, hBA,
        Matrix.one_mul]
    have h3 := congrFun (congrFun h2 t) b
    rwa [diagonal_mul, mul_diagonal, if_pos rfl, if_neg h, mul_one, zero_mul] at h3
  have e : P * (β * q * γ - 1) * J = (P * β) * (q - 1) * (γ * J) := by
    rw [← hβγ]
    simp only [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_assoc, Matrix.one_mul]
  rw [e, Matrix.mul_apply]
  refine Finset.sum_eq_zero fun t _ => ?_
  by_cases ht : lw t = lv b
  · rw [Matrix.mul_apply, Finset.sum_eq_zero, zero_mul]
    intro r _
    by_cases hr : lv a = lw r
    · rw [Matrix.sub_apply, hq r t (by omega), sub_self, mul_zero]
    · rw [hA a r hr, zero_mul]
  · rw [hB t b ht, mul_zero]

variable {D : D7} {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (p : Place D k)

def wl (σ r : ℕ) : Fin σ ⊕ (Fin r ⊕ Fin σ) → ℕ :=
  Sum.elim (fun i => i.val + 1) (Sum.elim (fun _ => σ + 1) fun i => 2 * σ - i.val + 1)

def wJ {V V₀ : HSp D} {σ : ℕ} (d : HypDec V V₀ σ) : Matrix (Fin V.rank) (Fin σ ⊕ (Fin V₀.rank ⊕ Fin σ)) D.host.E :=
  fromCols d.e (fromCols d.i₀ d.e')

noncomputable def wP {V V₀ : HSp D} {σ : ℕ} (d : HypDec V V₀ σ) :
    Matrix (Fin σ ⊕ (Fin V₀.rank ⊕ Fin σ)) (Fin V.rank) D.host.E :=
  fromRows d.qX (fromRows d.q0 d.qY)

theorem wJ_wP {V V₀ : HSp D} {σ : ℕ} (d : HypDec V V₀ σ) : wJ d * wP d = 1 := by
  rw [wJ, wP, fromCols_mul_fromRows, fromCols_mul_fromRows, ← add_assoc, d.sum_eq_one_rat]

theorem wP_wJ {V V₀ : HSp D} {σ : ℕ} (d : HypDec V V₀ σ) : wP d * wJ d = 1 :=
  (Matrix.mul_eq_one_comm_of_card_eq _ _ _ (by simp [← d.rank_add]; ring)).1 (wJ_wP d)

theorem frame_cols {σ : ℕ} (B : BesLev D σ) (s : k) {n : Type} [Fintype n] [DecidableEq n] {c : ℕ}
    (FA : Frame k B.A.rank n) (FV : Frame k B.V.rank (n ⊕ Fin c)) (h : p.IsBesFrame B s FA FV) (r : n ⊕ Fin c) :
    ∃ x : Fin σ ⊕ (Fin B.V₀.rank ⊕ Fin σ) → k, (∀ z, wl σ _ z ≠ lev (σ + 1) r → x z = 0) ∧
      ∀ u, FV.β u r = ∑ z, (wJ B.d).map (Witness.prH p) u z * x z := by
  obtain ⟨hc, h1, h2, h3, h4⟩ := h
  rcases r with a | j
  · refine ⟨Sum.elim 0 (Sum.elim (fun w => (B.o.iA.map (Witness.prH p) * FA.β) w a) 0), ?_, fun u => ?_⟩
    · rintro (z | z | z) hz
      · rfl
      · exact absurd rfl hz
      · rfl
    · rw [h1]
      change ((B.d.i₀ * B.o.iA).map (Witness.prH p) * FA.β) u a = _
      rw [Matrix.map_mul, Matrix.mul_assoc, Matrix.mul_apply]
      simp [wJ]
  · have hj := j.isLt
    rcases lt_trichotomy j.val σ with hlt | heq | hgt
    · refine ⟨Pi.single (Sum.inl ⟨j.val, hlt⟩) (s * p.xi ^ (σ - j.val)), fun z hz => Pi.single_eq_of_ne ?_ _, fun u => ?_⟩
      · rintro rfl
        exact hz rfl
      · rw [h2 ⟨j.val, hlt⟩ j rfl, Finset.sum_eq_single (Sum.inl ⟨j.val, hlt⟩), Pi.single_eq_same, mul_comm]
        · rfl
        · intro b _ hb
          rw [Pi.single_eq_of_ne hb, mul_zero]
        · simp
    · refine ⟨Sum.elim 0 (Sum.elim (fun w => s * Witness.prH p (vecB B.o B.ζ w)) 0), ?_, fun u => ?_⟩
      · rintro (z | z | z) hz
        · rfl
        · exact absurd (by simp [wl, lev, heq]) hz
        · rfl
      · rw [h3 j heq]
        change s * Witness.prH p (∑ w, B.d.i₀ u w * vecB B.o B.ζ w) = _
        set_option synthInstance.maxHeartbeats 100000 in
          rw [map_sum, Finset.mul_sum]
        simp [wJ, mul_left_comm]
    · have hi : 2 * σ - j.val < σ := by omega
      refine ⟨Pi.single (Sum.inr (Sum.inr ⟨_, hi⟩))
        (s * (-p.hz B / p.xi) * (-1 / p.xi) ^ (σ - 1 - (2 * σ - j.val))), fun z hz => Pi.single_eq_of_ne ?_ _, fun u => ?_⟩
      · rintro rfl
        exact hz (by simp only [wl, lev, Sum.elim_inr]; omega)
      · rw [h4 ⟨_, hi⟩ j (by simp only; omega), Finset.sum_eq_single (Sum.inr (Sum.inr ⟨_, hi⟩)), Pi.single_eq_same, mul_comm]
        · rfl
        · intro b _ hb
          rw [Pi.single_eq_of_ne hb, mul_zero]
        · simp

theorem comp_vanish {σ : ℕ} (B : BesLev D σ) (s : k) {n : Type} [Fintype n] [DecidableEq n] {c : ℕ}
    (FA : Frame k B.A.rank n) (FV : Frame k B.V.rank (n ⊕ Fin c)) (h : p.IsBesFrame B s FA FV)
    (M : Mx D B.V.rank B.V.rank) (q : GL (n ⊕ Fin c) k) (hq : q ∈ N k n c (σ + 1))
    (hM : M.map p.π = FV.β * q.val * FV.γ) (a b : Fin σ ⊕ (Fin B.V₀.rank ⊕ Fin σ)) (hab : wl σ _ b ≤ wl σ _ a) :
    p.π (((wP B.d).map (incA D) ⬝ (M - 1) ⬝ (wJ B.d).map (incA D)) a b) = 0 := by
  have h1 : (wP B.d).map (Witness.prH p) * (wJ B.d).map (Witness.prH p) = 1 := by
    rw [← Matrix.map_mul, wP_wJ, Matrix.map_one _ (map_zero _) (map_one _)]
  have h2 : (wJ B.d).map (Witness.prH p) * (wP B.d).map (Witness.prH p) = 1 := by
    rw [← Matrix.map_mul, wJ_wP, Matrix.map_one _ (map_zero _) (map_one _)]
  have key := conj_vanish (wl σ _) (lev (σ + 1)) _ _ FV.β FV.γ h1 h2 FV.βγ FV.γβ (fun a r har => by
    obtain ⟨x, hx, hβ⟩ := frame_cols p B s FA FV h r
    have : (((wP B.d).map (Witness.prH p)) ⬝ FV.β) a r =
        (((wP B.d).map (Witness.prH p) * (wJ B.d).map (Witness.prH p)) *ᵥ x) a := by
      rw [← Matrix.mulVec_mulVec, Matrix.mul_apply]
      exact Finset.sum_congr rfl fun u _ => by rw [hβ]; rfl
    rw [this, h1, Matrix.one_mulVec, hx a har]) q.val ((GlobalTheory.RootEx.Radical.mem_N_iff q).1 hq) a b hab
  rw [← key, ← hM, ← Matrix.map_apply (f := p.π), Matrix.map_mul, Matrix.map_mul, Matrix.map_sub _ (map_sub p.π),
    Matrix.map_one _ (map_zero _) (map_one _)]
  rfl

theorem entry_zero {V : HSp D} {g : GA D V} (hg : SuppAt p.e V g) {l m : ℕ} (P : Mx D l V.rank) (J : Mx D V.rank m) (i j)
    (h1 : p.π ((P ⬝ (mt V g - 1) ⬝ J) i j) = 0)
    (h2 : p.π (((adj J ⬝ gA V) ⬝ (mt V g⁻¹ - 1) ⬝ (giA V ⬝ adj P)) j i) = 0) : (P ⬝ (mt V g - 1) ⬝ J) i j = 0 := by
  have e1 : (p.e + cA D p.e) • (mt V g - 1) = mt V g - 1 := Matrix.ext hg
  have e2 : (p.e + cA D p.e) * (P ⬝ (mt V g - 1) ⬝ J) i j = (P ⬝ (mt V g - 1) ⬝ J) i j := by
    conv_rhs => rw [← e1, Matrix.mul_smul, Matrix.smul_mul]
    rfl
  have e3 : (adj J ⬝ gA V) ⬝ (mt V g⁻¹ - 1) ⬝ (giA V ⬝ adj P) = adj (P ⬝ (mt V g - 1) ⬝ J) := by
    simp only [mt_inv, adj_mul, adj_sub, Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_assoc, gA_giA_cancel,
      Matrix.one_mul]
  rw [e3] at h2
  change p.π (cA D ((P ⬝ (mt V g - 1) ⬝ J) i j)) = 0 at h2
  generalize (P ⬝ (mt V g - 1) ⬝ J) i j = x at h1 h2 e2
  have a1 : p.e * x = 0 := by rw [← p.ι_π, h1, map_zero]
  have a2 : p.e * cA D x = 0 := by rw [← p.ι_π, h2, map_zero]
  have a3 : cA D p.e * x = 0 := by
    have := congrArg (cA D) a2
    rwa [map_mul, cA_cA, map_zero] at this
  rw [← e2, add_mul, a1, a3, add_zero]

theorem unip_of_blocks {R : Type} [CommRing R] {m r σ : ℕ} (jX jY : Matrix (Fin m) (Fin σ) R) (j0 : Matrix (Fin m) (Fin r) R)
    (pX pY : Matrix (Fin σ) (Fin m) R) (p0 : Matrix (Fin r) (Fin m) R) (h : jX * pX + j0 * p0 + jY * pY = 1)
    (M : Matrix (Fin m) (Fin m) R) (zXX : GlobalTheory.BesselChar.StrictUp (pX * (M - 1) * jX)) (z0X : p0 * (M - 1) * jX = 0)
    (zYX : pY * (M - 1) * jX = 0) (z00 : p0 * (M - 1) * j0 = 0) (zY0 : pY * (M - 1) * j0 = 0) :
    GlobalTheory.BesselChar.Unip jX pY M := by
  obtain ⟨L, rfl⟩ : ∃ L, M = 1 + L := ⟨M - 1, by abel⟩
  rw [add_sub_cancel_left] at zXX z0X zYX z00 zY0
  have cX : L * jX = jX * (pX * L * jX) := by
    conv_lhs => rw [← Matrix.one_mul L, ← h]
    simp only [Matrix.mul_assoc] at z0X zYX
    simp only [Matrix.add_mul, Matrix.mul_assoc, z0X, zYX, Matrix.mul_zero, add_zero]
  have c0 : L * j0 = jX * (pX * L * j0) := by
    conv_lhs => rw [← Matrix.one_mul L, ← h]
    simp only [Matrix.mul_assoc] at z00 zY0
    simp only [Matrix.add_mul, Matrix.mul_assoc, z00, zY0, Matrix.mul_zero, add_zero]
  refine ⟨⟨_, zXX, by rw [← cX, Matrix.add_mul, Matrix.one_mul]⟩, fun y hy => ?_⟩
  refine ⟨(pX * L * jX) *ᵥ (pX *ᵥ y) + (pX * L * j0) *ᵥ (p0 *ᵥ y), ?_⟩
  have hy' : y = jX *ᵥ (pX *ᵥ y) + j0 *ᵥ (p0 *ᵥ y) := by
    conv_lhs => rw [← Matrix.one_mulVec y, ← h]
    rw [Matrix.add_mulVec, Matrix.add_mulVec, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec,
      hy, Matrix.mulVec_zero, add_zero]
  rw [Matrix.mulVec_add, Matrix.mulVec_mulVec _ jX, Matrix.mulVec_mulVec _ jX, ← cX, ← c0,
    ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_add, ← hy', Matrix.add_mulVec, Matrix.one_mulVec]

theorem mem_of_blocks {V V₀ : HSp D} {σ : ℕ} (d : HypDec V V₀ σ) (g : GA D V)
    (zXX : GlobalTheory.BesselChar.StrictUp (d.pX ⬝ (mt V g - 1) ⬝ d.jX)) (z0X : d.p0 ⬝ (mt V g - 1) ⬝ d.jX = 0)
    (zYX : d.pY ⬝ (mt V g - 1) ⬝ d.jX = 0) (z00 : d.p0 ⬝ (mt V g - 1) ⬝ d.j0 = 0)
    (zY0 : d.pY ⬝ (mt V g - 1) ⬝ d.j0 = 0) : g ∈ flagN d := by
  unfold flagN
  rw [GlobalTheory.BesselChar.mem_NFlag_iff V d.e (isIsoSub_e d).1]
  exact unip_of_blocks d.jX d.jY d.j0 d.pX d.pY d.p0 d.sum_eq_one _ zXX z0X zYX z00 zY0

theorem blocks_vanish {V V₀ : HSp D} {σ : ℕ} (d : HypDec V V₀ σ) (M : Mx D V.rank V.rank)
    (W : ∀ a b, wl σ _ b ≤ wl σ _ a → p.π (((wP d).map (incA D) ⬝ M ⬝ (wJ d).map (incA D)) a b) = 0) :
    (∀ i j, j ≤ i → p.π ((d.pX ⬝ M ⬝ d.jX) i j) = 0) ∧ (d.p0 ⬝ M ⬝ d.jX).map p.π = 0 ∧ (d.pY ⬝ M ⬝ d.jX).map p.π = 0 ∧
      (d.p0 ⬝ M ⬝ d.j0).map p.π = 0 ∧ (d.pY ⬝ M ⬝ d.j0).map p.π = 0 ∧
      ∀ i j, i ≤ j → p.π ((d.pY ⬝ M ⬝ d.jY) i j) = 0 := by
  refine ⟨fun i j h => W (Sum.inl i) (Sum.inl j) ?_, Matrix.ext fun i j => W (Sum.inr (Sum.inl i)) (Sum.inl j) ?_,
    Matrix.ext fun i j => W (Sum.inr (Sum.inr i)) (Sum.inl j) ?_,
    Matrix.ext fun i j => W (Sum.inr (Sum.inl i)) (Sum.inr (Sum.inl j)) ?_,
    Matrix.ext fun i j => W (Sum.inr (Sum.inr i)) (Sum.inr (Sum.inl j)) ?_,
    fun i j h => W (Sum.inr (Sum.inr i)) (Sum.inr (Sum.inr j)) ?_⟩ <;>
  simp only [wl, Sum.elim_inr, Sum.elim_inl] <;> omega

theorem mem_flagN : ∀ (D : D7) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (p : Place D k) (σ : ℕ) (B : BesLev D σ) (s : k) (n : Type) [Fintype n] [DecidableEq n] (c : ℕ) (FA : Frame k B.A.rank n) (FV : Frame k B.V.rank (n ⊕ Fin c)), p.IsBesFrame B s FA FV → ∀ (g : GA D B.V) (q : GL (n ⊕ Fin c) k), q ∈ N k n c (σ + 1) → p.IsLoc FV g q → g ∈ flagN B.d := by
  intro D k _ _ _ _ p σ B s n _ _ c FA FV hF g q hq hg
  obtain ⟨hS, hg⟩ := hg
  have hg' : (mt B.V g⁻¹).map p.π = FV.β * (q⁻¹).val * FV.γ := by
    have h1 : (mt B.V g⁻¹).map p.π * (mt B.V g).map p.π = 1 := by
      rw [← Matrix.map_mul, GlobalTheory.MixModel.mt_inv_mul, Matrix.map_one _ (map_zero _) (map_one _)]
    have h2 : (FV.β * q.val * FV.γ) * (FV.β * (q⁻¹).val * FV.γ) = 1 := by
      rw [Matrix.mul_assoc, Matrix.mul_assoc FV.β (q⁻¹).val, ← Matrix.mul_assoc FV.γ, FV.γβ, Matrix.one_mul,
        Matrix.mul_assoc, ← Matrix.mul_assoc q.val, Units.mul_inv, Matrix.one_mul, FV.βγ]
    rw [← Matrix.mul_one (Matrix.map _ _), ← h2, ← Matrix.mul_assoc _ (FV.β * q.val * FV.γ), ← hg, h1, Matrix.one_mul]
  obtain ⟨XX, OX, YX, OO, YO, -⟩ := blocks_vanish p B.d _ (comp_vanish p B s FA FV hF _ q hq hg)
  obtain ⟨-, OX', YX', OO', YO', YY'⟩ := blocks_vanish p B.d _ (comp_vanish p B s FA FV hF _ q⁻¹ (inv_mem hq) hg')
  generalize B.d = d at *
  have aX : giA B.V ⬝ adj d.pX = d.jY := by rw [d.pX_eq, adj_mul, adj_adj, adj_gA, giA_gA_cancel]
  have aY : giA B.V ⬝ adj d.pY = d.jX := by rw [d.pY_eq, adj_mul, adj_adj, adj_gA, giA_gA_cancel]
  have a0 : giA B.V ⬝ adj d.p0 = d.j0 ⬝ giA B.V₀ := by
    rw [d.p0_eq, adj_mul, adj_mul, adj_adj, adj_gA, adj_giA, Matrix.mul_assoc, giA_gA_cancel]
  have b0 : adj d.j0 ⬝ gA B.V = gA B.V₀ ⬝ d.p0 := by rw [d.p0_eq, gA_giA_cancel]
  have ev : ∀ {l m : ℕ} {x : Mx D l m}, x.map p.π = 0 → ∀ i j, p.π (x i j) = 0 := fun h i j => congrFun (congrFun h i) j
  refine mem_of_blocks d g (fun i j hij => entry_zero p hS _ _ i j (XX i j hij) ?_)
    (Matrix.ext fun i j => entry_zero p hS _ _ i j (ev OX i j) ?_)
    (Matrix.ext fun i j => entry_zero p hS _ _ i j (ev YX i j) ?_)
    (Matrix.ext fun i j => entry_zero p hS _ _ i j (ev OO i j) ?_)
    (Matrix.ext fun i j => entry_zero p hS _ _ i j (ev YO i j) ?_)
  · rw [aX, ← d.pY_eq]
    exact YY' j i hij
  · refine ev ?_ j i
    rw [a0, ← d.pY_eq, ← Matrix.mul_assoc, Matrix.map_mul, YO', Matrix.zero_mul]
  · rw [aY, ← d.pY_eq]
    exact ev YX' j i
  · refine ev ?_ j i
    rw [a0, b0, ← Matrix.mul_assoc, Matrix.mul_assoc (gA _), Matrix.mul_assoc (gA _),
      Matrix.map_mul, Matrix.map_mul, OO', Matrix.mul_zero, Matrix.zero_mul]
  · refine ev ?_ j i
    rw [aY, b0, Matrix.mul_assoc (gA _), Matrix.mul_assoc (gA _), Matrix.map_mul, OX', Matrix.mul_zero]

end GlobalTheory.LocFlag
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.NoConjOfIdemSum
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Forms Formalism.L2.Ker Formalism.UG
open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.MixPer GlobalTheory.Core.Rk GlobalTheory.AdForm
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.HalfSplit

theorem noConj_of_idemSum : ∀ (D : D7) (e : AE D) (SS : Finset (Formalism.L2.DIV.Pl D.host.E)), IsIdemSum e SS → ∀ P ∈ SS, Formalism.L2.Col.conjPrime₂ P ∉ SS := by
  intro D e SS hI P hP hP'
  obtain ⟨⟨es, hes, he⟩, hc⟩ := hI
  have h1 : ∀ i ∈ SS, es i * es i = es i := fun i hi => (hes i hi).1.1
  have hcross : ∀ i ∈ SS, ∀ j ∈ SS, es i * cA D (es j) = 0 := by
    subst he
    exact GlobalTheory.PlaceDatum.cross_eq_zero (R := AE D) GlobalTheory.PlaceDatum.isUnit_natCast (cA D) es SS h1 hc
  have hcj : Lev.IsConjPl (D := D) (Formalism.L2.Col.conjPrime₂ P) P := by
    intro c hc'
    exact ⟨Formalism.L2.Col.cO D.host.E c, (Formalism.L2.Col.mem_conjP P c).1 hc', rfl⟩
  have heq : es P = cA D (es (Formalism.L2.Col.conjPrime₂ P)) :=
    Formalism.IndefR.Fin.conj_idem_eq (hes _ hP') (hes P hP) hcj
  apply Formalism.IndefR.Fin.idemAt_ne_zero (hes P hP)
  have := hcross P hP _ hP'
  rw [← heq, h1 P hP] at this
  exact this

theorem splitHyp_halves : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (S T : HSp D) (δ : ℂ) (sc : ℝ), StdPair θ S T δ sc ψ → ∀ (e : AE D) (SS : Finset (Formalism.L2.DIV.Pl D.host.E)), IsIdemSum e SS → ∀ (N : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)) (N' : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)) (c : ℕ), 0 < c → Odd c → (∀ Q ∈ SS, ((D.host.QS * D.host.q * D.host.d : ℕ) : 𝓞 D.host.E) ∉ Q.asIdeal) → LaFacts (tauE D) δ D.host.d sc (D.host.AA0 : Submodule (𝓞 D.host.E) D.host.E) N N' → IsSelfDualC S N → IsSelfDualC T N' → SplitHyp (HV sc) (alV D.host.d sc) (AC (tauE D) δ (D.host.AA0 : Submodule (𝓞 D.host.E) D.host.E) SS N N' c) (BC (tauE D) δ (D.host.AA0 : Submodule (𝓞 D.host.E) D.host.E) SS N N' c) (LamC (tauE D) δ (D.host.AA0 : Submodule (𝓞 D.host.E) D.host.E) N N') := by
  intro D ψ θ S T δ sc hP e SS hI N N' c hc hcS h2 hL hN hN'
  have hSS : ∀ P ∈ SS, Formalism.L2.Col.conjPrime₂ P ∉ SS := noConj_of_idemSum D e SS hI
  have hT : Nonempty D.what₂.Tau := ⟨D.eTau.symm (Classical.arbitrary _)⟩
  have hconj : ∀ τ (x : D.host.E), tauE D τ (star x) = starRingEnd ℂ (tauE D τ x) := fun τ x =>
    GlobalTheory.FockCompare.tauE_star τ x
  have he1 : ∀ Q, expS SS Q = 1 ∨ expS SS Q = 0 ∨ expS SS Q = -1 := by
    intro Q; unfold expS; split_ifs <;> simp
  have hc1 : ∀ Q, expS SS (Formalism.L2.Col.conjPrime₂ Q) = -expS SS Q := exponent_set_conjugate D.host.E SS hSS
  have hfg : N.FG := hN.1.fg
  have tw : ∀ f : HeightOneSpectrum (𝓞 D.host.E) → ℤ, (∀ Q, f (Formalism.L2.Col.conjPrime₂ Q) = -f Q) →
      (∀ Q, f Q = 1 ∨ f Q = 0 ∨ f Q = -1) →
      LaFacts (tauE D) δ D.host.d sc (D.host.AA0 : Submodule (𝓞 D.host.E) D.host.E) N (twist₂ N' c f) := by
    intro f hf1 hf2
    unfold LaFacts LamC
    rw [← twist_homomorphism D.host.E _ _ _ N N' c f hfg hc]
    exact ⟨GlobalTheory.TwPerSelfDual.twO_selfDual D.host.E D.what₂.Tau _ _ (tauE D) δ D.host.d sc _ c f hP.ne hconj hc hf1 hf2 hL.1 hL.2,
      GlobalTheory.SemiTwist.semiChar_twO D.host.E D.what₂.Tau _ _ (tauE D) δ D.host.d sc _ c f hP.ne hconj hc hf1 hf2 hL.1 hL.2⟩
  exact half_periods_of_lattice D.host.E D.what₂.Tau _ _ (tauE D) δ D.host.d sc _ SS N N' c hP.ne hc hSS hfg hL
    (tw _ hc1 he1) (tw (fun Q => -expS SS Q) (fun Q => by simp [hc1])
      (fun Q => by rcases he1 Q with h | h | h <;> simp [h]))

end GlobalTheory.HalfSplit
end
end

