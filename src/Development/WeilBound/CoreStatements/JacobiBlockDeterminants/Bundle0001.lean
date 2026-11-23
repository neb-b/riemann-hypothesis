module

public import Development.WeilBound.CoreStatements.MultihomogeneousSquares.Bundle0001
public import Development.WeilBound.CoreStatements.PluriharmonicCharts.Bundle0010

@[expose] public section

-- bundled from Development.WeilBound.CoreStatements.JacobiBlockDeterminants.JacobiBlocks
section
noncomputable section

namespace HeightCancellation.C4

open Matrix GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.PB SquareStatements.Sing
open scoped ComplexOrder

theorem jacobi_blocks {m n : Type} [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]
    (A B : Matrix (m ⊕ n) (m ⊕ n) ℂ) (h : A * B = 1) : A.det * B.toBlocks₂₂.det = A.toBlocks₁₁.det := by
  have e : A * fromBlocks 1 B.toBlocks₁₂ 0 B.toBlocks₂₂ = fromBlocks A.toBlocks₁₁ 0 A.toBlocks₂₁ 1 := by
    rw [← fromBlocks_toBlocks A, ← fromBlocks_toBlocks B, fromBlocks_multiply, ← fromBlocks_one,
      fromBlocks_inj] at h
    conv_lhs => rw [← fromBlocks_toBlocks A, fromBlocks_multiply]
    rw [h.2.1, h.2.2.2]
    simp
  have := congrArg det e
  rwa [det_mul, det_fromBlocks_zero₂₁, det_fromBlocks_zero₁₂, det_one, det_one, one_mul, mul_one] at this

theorem jacobi {k l : ℕ} (O : Matrix (Fin (k + l)) (Fin (k + l)) ℂ) (hO : O.det ≠ 0) :
    O.det * ((revDual O).submatrix (Fin.castLE (Nat.le_add_left l k)) (Fin.castLE (Nat.le_add_left l k))).det =
      (O.submatrix (Fin.castLE (Nat.le_add_right k l)) (Fin.castLE (Nat.le_add_right k l))).det := by
  have h : O.submatrix finSumFinEquiv finSumFinEquiv * O⁻¹.submatrix finSumFinEquiv finSumFinEquiv = 1 := by
    rw [submatrix_mul_equiv, mul_nonsing_inv _ hO.isUnit, submatrix_one_equiv]
  have h1 := jacobi_blocks _ _ h
  rw [det_submatrix_equiv_self] at h1
  have e : (revDual O).submatrix (Fin.castLE (Nat.le_add_left l k)) (Fin.castLE (Nat.le_add_left l k)) =
      ((O⁻¹.submatrix finSumFinEquiv finSumFinEquiv).toBlocks₂₂ᵀ).submatrix Fin.revPerm Fin.revPerm := by
    ext a b
    have r : ∀ a : Fin l, Fin.rev (Fin.castLE (Nat.le_add_left l k) a) = Fin.natAdd k (Fin.rev a) := fun a =>
      Fin.ext (by have := a.2; simp [Fin.rev]; omega)
    simp only [revDual, submatrix_apply, r, ← transpose_nonsing_inv, transpose_apply, toBlocks₂₂, of_apply,
      finSumFinEquiv_apply_right, Fin.revPerm_apply]
  rw [e, det_submatrix_equiv_self, det_transpose, h1]
  rfl

theorem re_mul_pos {a b : ℂ} (ha : 0 < a) : (a * b).re = a.re * b.re := by
  rw [Complex.mul_re, ← (Complex.pos_iff.1 ha).2]
  simp

theorem jacobi_lead {q : ℕ} (O : Matrix (Fin q) (Fin q) ℂ) (hO : O.PosDef) {k l : ℕ} (e : k + l = q) :
    O.det.re * leadMinor (revDual O) l = leadMinor O k := by
  subst e
  unfold leadMinor
  rw [dite_eq_left (Nat.le_add_left l k), dite_eq_left (Nat.le_add_right k l), ← jacobi O hO.det_pos.ne',
    re_mul_pos hO.det_pos]

theorem grN_rev {q : ℕ} (O : Matrix (Fin q) (Fin q) ℂ) (hO : O.PosDef) {k l : ℕ} (e : k + l + 1 = q) :
    (grN (revDual O) l)⁻¹ = grN O k := by
  have h0 : O.det.re ≠ 0 := (Complex.pos_iff.1 hO.det_pos).1.ne'
  unfold grN
  rw [← jacobi_lead O hO (k := k + 1) (l := l) (by omega), ← jacobi_lead O hO (k := k) (l := l + 1) (by omega),
    mul_div_mul_left _ _ h0, ← Real.sqrt_inv, inv_div]

theorem log_grN {r : ℕ} {Γ : Matrix (Fin r) (Fin r) ℂ} (hΓ : Γ.PosDef) {k : ℕ} (hk : k < r) :
    0 < grN Γ k ∧ Real.log (grN Γ k) =
      (1 / 2) * Real.log (leadMinor Γ (k + 1)) - (1 / 2) * Real.log (leadMinor Γ k) := by
  have a := leadMinor_pos_of_posDef hΓ (s := k + 1) hk
  have b := leadMinor_pos_of_posDef hΓ (s := k) hk.le
  unfold grN
  refine ⟨Real.sqrt_pos.2 (div_pos a b), ?_⟩
  rw [Real.log_sqrt (div_pos a b).le, Real.log_div a.ne' b.ne']
  ring

theorem minor_emb {R : Type} [CommRing R] {N k : ℕ} (T : Matrix (Fin N) (Fin N) R) (C : Finset (Fin N))
    (f : Fin k → Fin N) (hf : StrictMono f) (hC : ∀ a, a ∈ C ↔ ∃ s, f s = a) :
    minorIJ T C C = (T.submatrix f f).det := by
  have e : C = Finset.univ.image f := by
    ext a
    simp [hC]
  have hc : C.card = k := by
    rw [e, Finset.card_image_of_injective _ hf.injective]
    simp
  rw [MinorCalc.minorIJ_eq_det T C C k hc hc,
    ← Finset.orderEmbOfFin_unique hc (f := f) (fun s => (hC _).2 ⟨s, rfl⟩) hf]

variable {p q : ℕ}

theorem minor_w (Γ : Matrix (Fin (p + q)) (Fin (p + q)) ℂ) (i : Fin (p + q)) (hi : (i : ℕ) + 1 ≤ p) :
    (minorIJ Γ (stepCols (p + q) p i) (stepCols (p + q) p i)).re = leadMinor (wBlock Γ) (i + 1) := by
  rw [minor_emb Γ _ (fun s => wEmb p q (Fin.castLE hi s)) (fun a b h => wEmb_strictMono p q h) fun a => ?_]
  · unfold leadMinor
    rw [dite_eq_left hi]
    rfl
  · simp only [stepCols, Finset.mem_filter, Finset.mem_univ, true_and, if_pos hi]
    constructor
    · intro h
      exact ⟨⟨a - q, by omega⟩, Fin.ext (by show q + (a - q) = a; omega)⟩
    · rintro ⟨s, rfl⟩
      have := s.2
      show _ ≤ q + (s : ℕ) ∧ q + (s : ℕ) < _
      omega

theorem minor_om (Γ : Matrix (Fin (p + q)) (Fin (p + q)) ℂ) (i : Fin (p + q)) (hi : ¬ (i : ℕ) + 1 ≤ p) :
    (minorIJ Γ (stepCols (p + q) p i) (stepCols (p + q) p i)).re = leadMinor (omBlock Γ) (i + 1 - p) := by
  have hq : (i : ℕ) + 1 - p ≤ q := by have := i.2; omega
  rw [minor_emb Γ _ (fun s => omEmb p q (Fin.castLE hq s)) (fun a b h => omEmb_strictMono p q h) fun a => ?_]
  · unfold leadMinor
    rw [dite_eq_left hq]
    rfl
  · simp only [stepCols, Finset.mem_filter, Finset.mem_univ, true_and, if_neg hi]
    constructor
    · intro h
      exact ⟨⟨a, h⟩, rfl⟩
    · rintro ⟨s, rfl⟩
      exact s.2

def pot (Γ : Matrix (Fin (p + q)) (Fin (p + q)) ℂ) (n : ℕ) : ℝ :=
  (1 / 2) * Real.log (leadMinor (wBlock Γ) (min n p)) + (1 / 2) * Real.log (leadMinor (omBlock Γ) (n - p))

theorem log_mu {Γ : Matrix (Fin (p + q)) (Fin (p + q)) ℂ} (hΓ : Γ.PosDef) (m : Fin (p + q)) :
    0 < mu p q Γ m ∧ Real.log (mu p q Γ m) = pot Γ (m + 1) - pot Γ m := by
  have hW : (wBlock Γ).PosDef := hΓ.submatrix (wEmb_strictMono p q).injective
  have hO : (omBlock Γ).PosDef := hΓ.submatrix (omEmb_strictMono p q).injective
  have hm := m.2
  unfold mu pot
  split_ifs with h
  · obtain ⟨a, b⟩ := log_grN hW h
    refine ⟨a, ?_⟩
    rw [b, min_eq_left (show (m : ℕ) + 1 ≤ p from h), min_eq_left h.le, show (m : ℕ) + 1 - p = 0 by omega,
      show (m : ℕ) - p = 0 by omega]
    ring
  · rw [grN_rev _ hO (k := m - p) (by omega)]
    obtain ⟨a, b⟩ := log_grN hO (k := m - p) (by omega)
    refine ⟨a, ?_⟩
    rw [b, min_eq_right (show p ≤ (m : ℕ) + 1 by omega), min_eq_right (show p ≤ (m : ℕ) by omega),
      show (m : ℕ) + 1 - p = m - p + 1 by omega]
    ring

theorem sum_tele {N : ℕ} (f : ℕ → ℝ) (i : Fin N) :
    ∑ m ∈ Finset.Iic i, (f ((m : ℕ) + 1) - f m) = f (i + 1) - f 0 := by
  rw [← Finset.sum_range_sub f]
  refine Finset.sum_bij (fun m _ => (m : ℕ)) ?_ ?_ ?_ (fun _ _ => rfl)
  · intro m hm
    exact Finset.mem_range.2 (Nat.lt_succ_of_le (Fin.le_def.1 (Finset.mem_Iic.1 hm)))
  · intro a _ b _ h
    exact Fin.ext h
  · intro n hn
    have h1 := Finset.mem_range.1 hn
    have h2 := i.2
    exact ⟨⟨n, by omega⟩, Finset.mem_Iic.2 (show n ≤ (i : ℕ) by omega), rfl⟩

open Classical in
theorem pot_eq {Γ : Matrix (Fin (p + q)) (Fin (p + q)) ℂ} (hΓ : Γ.PosDef) (i : Fin (p + q)) :
    pot Γ (i + 1) = (1 / 2) * Real.log (detFac p i Γ).re + if IsProperStep (p + q) p i then
      (1 / 2) * Real.log (minorIJ Γ (stepCols (p + q) p i) (stepCols (p + q) p i)).re else 0 := by
  have hW : (wBlock Γ).PosDef := hΓ.submatrix (wEmb_strictMono p q).injective
  have hO : (omBlock Γ).PosDef := hΓ.submatrix (omEmb_strictMono p q).injective
  have hi := i.2
  unfold pot detFac IsProperStep
  rw [minorIJ_wIdx, minorIJ_omIdx]
  by_cases hN : (i : ℕ) + 1 = p + q
  · rw [if_pos (by omega), if_pos hN, if_neg (fun h => h.2 hN), min_eq_right (by omega),
      show (i : ℕ) + 1 - p = q by omega, leadMinor_size_self, leadMinor_size_self, re_mul_pos hW.det_pos,
      Real.log_mul (Complex.pos_iff.1 hW.det_pos).1.ne' (Complex.pos_iff.1 hO.det_pos).1.ne']
    ring
  · rw [if_neg hN, mul_one]
    rcases lt_trichotomy ((i : ℕ) + 1) p with h | h | h
    · rw [if_neg (by omega), if_pos ⟨h.ne, hN⟩, minor_w Γ i h.le, min_eq_left h.le,
        show (i : ℕ) + 1 - p = 0 by omega, leadMinor_size_zero]
      simp
    · rw [if_pos h.ge, if_neg (fun h' => h'.1 h), min_eq_right h.ge,
        show (i : ℕ) + 1 - p = 0 by omega, leadMinor_size_zero, leadMinor_size_self]
      simp
    · rw [if_pos h.le, if_pos ⟨h.ne', hN⟩, minor_om Γ i (by omega), min_eq_right h.le, leadMinor_size_self]

end HeightCancellation.C4

open scoped ComplexOrder in
open Matrix GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.PB HeightCancellation.C4 in
theorem HeightCancellation.c4 : SquareStatements.Sing.C4 := by
  intro p q G h bG hG bh hh
  have hP : (hᴴ * G * h).PosDef := hG.conjTranspose_mul_mul_same
    (Matrix.mulVec_injective_iff_isUnit.2 ((Matrix.isUnit_iff_isUnit_det h).2 hh.isUnit))
  refine ⟨fun m => (log_mu hP m).1, fun i => ⟨CPts.detFac_ne_zero (Nat.le_add_right p q) i bh hh, ?_⟩⟩
  simp only [(log_mu hP _).2]
  rw [sum_tele (pot (hᴴ * G * h)) i, pot_eq hP,
    PositivityTheory.Xgp.c_bm_exists_hom.log_detFac (Nat.le_add_right p q) i hG bG bh hh]
  have e : pot (hᴴ * G * h) 0 = 0 := by simp [pot, leadMinor_size_zero]
  rw [e, blockPot]
  ring
end
end

-- bundled from Development.WeilBound.CoreStatements.JacobiBlockDeterminants.ValDetFac
section
noncomputable section

namespace HeightCancellation.C2

open AlgebraicGeometry CategoryTheory NumberField Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.PB SquareStatements.Sing
open GroundTheory.Heights₂.Heights.LowerBoundFree (valAt)

variable {p q : ℕ}

theorem col_val (a : Fin (p + q)) : (SquareStatements.Sing.col p q a : ℕ) = if (a : ℕ) < p then q + a else a - p := by
  unfold SquareStatements.Sing.col
  split_ifs <;> rfl

theorem prod_col {R : Type} [CommRing R] (f : Fin (p + q) → R) (i : Fin (p + q)) :
    ∏ a ∈ Finset.Iic i, f (SquareStatements.Sing.col p q a) = (∏ c ∈ Finset.univ.filter fun c : Fin (p + q) => q ≤ c ∧ (c : ℕ) ≤ q + i, f c) *
      ∏ c ∈ Finset.univ.filter fun c : Fin (p + q) => (c : ℕ) < q ∧ (c : ℕ) + p ≤ i, f c := by
  rw [← Finset.prod_union (Finset.disjoint_filter.2 fun c _ h h' => by omega)]
  refine Finset.prod_bij (fun a _ => SquareStatements.Sing.col p q a) ?_ ?_ ?_ (fun _ _ => rfl)
  · intro a ha
    have h1 : (a : ℕ) ≤ i := Fin.le_def.1 (Finset.mem_Iic.1 ha)
    have h2 := a.2
    simp only [Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and, col_val]
    split_ifs <;> omega
  · intro a _ b _ h
    have h1 := congrArg Fin.val h
    have h2 := a.2
    have h3 := b.2
    rw [col_val, col_val] at h1
    refine Fin.ext ?_
    split_ifs at h1 <;> omega
  · intro c hc
    have h2 := c.2
    simp only [Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and] at hc
    rcases hc with hc | hc
    · refine ⟨⟨c - q, by omega⟩, Finset.mem_Iic.2 (show c - q ≤ (i : ℕ) by omega), Fin.ext ?_⟩
      rw [col_val, if_pos (show c - q < p by omega)]
      show q + (c - q) = c
      omega
    · refine ⟨⟨c + p, by omega⟩, Finset.mem_Iic.2 (show c + p ≤ (i : ℕ) by omega), Fin.ext ?_⟩
      rw [col_val, if_neg (show ¬ c + p < p by omega)]
      show c + p - p = c
      omega

open Classical in
theorem prod_diag {R : Type} [CommRing R] {B : Matrix (Fin (p + q)) (Fin (p + q)) R} (hB : B.BlockTriangular id)
    (i : Fin (p + q)) : ∏ a ∈ Finset.Iic i, B (SquareStatements.Sing.col p q a) (SquareStatements.Sing.col p q a) =
      detFac p i B * if IsProperStep (p + q) p i then ∏ c ∈ stepCols (p + q) p i, B c c else 1 := by
  have hi := i.2
  rw [prod_col (fun c => B c c), detFac, MinorCalc.minorIJ_self_of_triangular B hB,
    MinorCalc.minorIJ_self_of_triangular B hB]
  unfold IsProperStep stepCols wIdx omIdx
  have key : ∀ {P Q : Fin (p + q) → Prop} [DecidablePred P] [DecidablePred Q], (∀ c, P c ↔ Q c) →
      ∏ c ∈ Finset.univ.filter P, B c c = ∏ c ∈ Finset.univ.filter Q, B c c := fun h => by
    rw [Finset.filter_congr fun c _ => h c]
  have key0 : ∀ {P : Fin (p + q) → Prop} [DecidablePred P], (∀ c, ¬ P c) →
      ∏ c ∈ Finset.univ.filter P, B c c = 1 := fun h => by
    rw [Finset.filter_eq_empty_iff.2 fun c _ => h c, Finset.prod_empty]
  by_cases hN : (i : ℕ) + 1 = p + q
  · rw [if_pos (by omega), if_pos hN, if_neg (fun h => h.2 hN), mul_one]
    congr 1
    · exact key fun c => by have := c.2; omega
    · exact key fun c => by have := c.2; omega
  · rw [if_neg hN, mul_one]
    rcases lt_trichotomy ((i : ℕ) + 1) p with h | h | h
    · rw [if_neg (by omega), if_pos ⟨h.ne, hN⟩, one_mul, key0 (P := fun c => (c : ℕ) < q ∧ (c : ℕ) + p ≤ i)
        (fun c => by omega), mul_one]
      exact key fun c => by rw [if_pos h.le]; omega
    · rw [if_pos h.ge, if_neg (fun h' => h'.1 h), key0 (P := fun c => (c : ℕ) < q ∧ (c : ℕ) + p ≤ i)
        (fun c => by omega)]
      congr 1
      exact key fun c => by have := c.2; omega
    · rw [if_pos h.le, if_pos ⟨h.ne', hN⟩]
      congr 1
      · exact key fun c => by have := c.2; omega
      · exact key fun c => by rw [if_neg (by omega)]; omega

section Val

variable {X : Scheme.{0}} {Ω : Type} [Field Ω] {ξ : Spec (CommRingCat.of Ω) ⟶ X} {z : Spec (CommRingCat.of ℂ) ⟶ X}
  {N : ℕ}

theorem val_detFac (hz : genPt ξ ⤳ centre z) {A : Matrix (Fin N) (Fin N) Ω} {h : Matrix (Fin N) (Fin N) ℂ}
    (hv : ∀ a b, ValAt ξ z (A a b) (h a b)) (j : ℕ) (i : Fin N) : ValAt ξ z (detFac j i A) (detFac j i h) := by
  choose _ s hs hs' using hv
  have e1 : A = (Matrix.of s).map (genMap ξ ⟨centre z, hz⟩) := Matrix.ext fun a b => (hs a b).symm
  have e2 : h = (Matrix.of s).map (Scheme.stalkClosedPointTo z).hom := Matrix.ext fun a b => (hs' a b).symm
  exact ⟨hz, detFac j i (Matrix.of s), by rw [e1, PositivityTheory.Xgp.c_bm_exists_hom.detFac_map],
    e2 ▸ (PositivityTheory.Xgp.c_bm_exists_hom.detFac_map (Scheme.stalkClosedPointTo z).hom i (Matrix.of s)).symm⟩

theorem val_pl (hz : genPt ξ ⤳ centre z) {A : Matrix (Fin N) (Fin N) Ω} {h : Matrix (Fin N) (Fin N) ℂ}
    (hv : ∀ a b, ValAt ξ z (A a b) (h a b)) {u : Finset (Fin N) → Ω} {v : Finset (Fin N) → ℂ}
    (hu : ∀ I, ValAt ξ z (u I) (v I)) (C : Finset (Fin N)) :
    ValAt ξ z (∑ I, u I * minorIJ A I C) (∑ I, v I * minorIJ h I C) := by
  choose _ s hs hs' using hv
  choose _ t ht ht' using hu
  have e1 : A = (Matrix.of s).map (genMap ξ ⟨centre z, hz⟩) := Matrix.ext fun a b => (hs a b).symm
  have e2 : h = (Matrix.of s).map (Scheme.stalkClosedPointTo z).hom := Matrix.ext fun a b => (hs' a b).symm
  refine ⟨hz, ∑ I, t I * minorIJ (Matrix.of s) I C, ?_, ?_⟩
  · set_option synthInstance.maxHeartbeats 100000 in
      rw [e1, map_sum]
      exact Finset.sum_congr rfl fun I _ => by rw [map_mul, CPts.minorIJ_map, ht]
  · rw [e2]
    refine (map_sum (Scheme.stalkClosedPointTo z).hom _ _).trans (Finset.sum_congr rfl fun I _ => ?_)
    exact (map_mul (Scheme.stalkClosedPointTo z).hom _ _).trans (congrArg₂ (· * ·) (ht' I)
      (CPts.minorIJ_map (Scheme.stalkClosedPointTo z).hom (Matrix.of s) I C).symm)

end Val

end HeightCancellation.C2

open AlgebraicGeometry Matrix GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.PB HeightCancellation.C2 SquareStatements.Sing in
theorem HeightCancellation.c2 : SquareStatements.Sing.C2 := by
  intro E _ _ _ H D l Xo c Y S K _ ι _ Φ _ y M 𝔐' z wb F τ B h hF gd hval hx ⟨bB, tB, _, _, _, hv⟩ i
  classical
  have hz := 𝔐'.all (centre z)
  have hT : ((F.T τ).map (algebraMap M.Ω Φ)).det ≠ 0 := by
    rw [← RingHom.mapMatrix_apply, ← RingHom.map_det]
    exact (map_ne_zero _).2 (hF.1 τ).2
  have bT : IsBlockDiag D.p ((F.T τ).map (algebraMap M.Ω Φ)) := (hF.1 τ).1.map _
  have bX : IsBlockDiag D.p (inFrame M F τ B) := ((bT.inv hT.isUnit).mul (M.g_block τ)).mul bB
  have e : (F.T τ).map (algebraMap M.Ω Φ) * inFrame M F τ B = M.g τ * B := by
    rw [inFrame, Matrix.mul_assoc, Matrix.mul_nonsing_inv_cancel_left _ _ hT.isUnit]
  have e1 : algebraMap M.Ω Φ (detFac D.p i (F.T τ)) * detFac D.p i (inFrame M F τ B) =
      detFac D.p i (M.g τ) * detFac D.p i B := by
    rw [← MinorCalc.detFac_mul i bB, ← e, MinorCalc.detFac_mul i bX, PositivityTheory.Xgp.c_bm_exists_hom.detFac_map]
  have e2 : algebraMap M.Ω Φ (∏ k', M.x ⟨k', F.c k'⟩ ^ M.b (τ, i) k') *
      ∏ k', algebraMap M.Ω Φ (M.x ⟨k', F.c k'⟩) ^ (-M.b (τ, i) k') = 1 := by
    rw [map_prod, ← Finset.prod_mul_distrib]
    refine Finset.prod_eq_one fun k _ => ?_
    rw [map_zpow₀, _root_.zpow_neg, mul_inv_cancel₀ (zpow_ne_zero _ ((map_ne_zero _).2 (hx k)))]
  have vd := val_detFac hz hv D.p i
  refine ⟨fun k hk m => ?_, fun hk => ?_⟩
  · have hp : IsProperStep (D.p + D.q) D.p i := by
      by_contra hn
      rw [(M.blk_none (τ, i)).2 hn] at hk
      cases hk
    have e3 := CPts.frame_gen M hF (RingHom.id Φ) (p := (τ, i)) hk m bX bB tB e
    simp only [RingHom.id_apply] at e3
    have v2 := val_pl hz hv (fun I => hval _ (gd.2.1 ⟨k, m⟩ I).1) (stepCols (D.p + D.q) D.p i)
    convert CxVal.mul vd v2 using 1
    rw [prod_diag tB, if_pos hp]
    linear_combination (-(∏ c ∈ stepCols (D.p + D.q) D.p i, B c c) * y ⟨k, m⟩ *
        ∏ k', algebraMap M.Ω Φ (M.x ⟨k', F.c k'⟩) ^ (-M.b (τ, i) k')) * e1 +
      (detFac D.p i (inFrame M F τ B) * ∏ k', algebraMap M.Ω Φ (M.x ⟨k', F.c k'⟩) ^ (-M.b (τ, i) k')) * e3 +
      (detFac D.p i (inFrame M F τ B) * ∑ I, algebraMap M.Ω Φ (F.u ⟨k, m⟩ I) *
        minorIJ (inFrame M F τ B) I (stepCols (D.p + D.q) D.p i)) * e2
  · have hp : ¬ IsProperStep (D.p + D.q) D.p i := (M.blk_none (τ, i)).1 hk
    obtain ⟨h0, r1, r2⟩ := gd.2.2 (τ, i) hk
    have v1 := hval _ r1
    have v2 := hval _ r2
    refine ⟨fun hv0 => ?_, ?_⟩
    · have v3 := CxVal.mul v1 v2
      rw [← map_mul, mul_inv_cancel₀ h0, map_one, hv0, zero_mul] at v3
      exact zero_ne_one (CxVal.unique v3 (CxVal.one hz))
    · have e3 := congrArg (algebraMap M.Ω Φ) (hF.2.2.2 (τ, i) hk)
      rw [map_mul, map_mul] at e3
      convert CxVal.mul vd v1 using 1
      rw [prod_diag tB, if_neg hp]
      linear_combination (-algebraMap M.Ω Φ (M.lam (τ, i)) *
          ∏ k', algebraMap M.Ω Φ (M.x ⟨k', F.c k'⟩) ^ (-M.b (τ, i) k')) * e1 +
        (detFac D.p i (inFrame M F τ B) * ∏ k', algebraMap M.Ω Φ (M.x ⟨k', F.c k'⟩) ^ (-M.b (τ, i) k')) * e3 +
        (detFac D.p i (inFrame M F τ B) * algebraMap M.Ω Φ (F.υ (τ, i))) * e2
end
end

