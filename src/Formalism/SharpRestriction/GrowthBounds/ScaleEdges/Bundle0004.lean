module

public import Formalism.SharpRestriction.GrowthBounds.ScaleEdges.Bundle0001
public import Formalism.SharpRestriction.GrowthBounds.ScaleEdges.Bundle0002

@[expose] public section

-- bundled from Formalism.SharpRestriction.GrowthBounds.ScaleEdges.EvensBeforePairwise
section
noncomputable section

namespace Formalism.MainNotions.Pf14

open Formalism.MainNotions.G Formalism.MainNotions.SourceCleaning Formalism.MainNotions.G.WittFrameLocaliserOrders

theorem getElem_ge_of_many (D : List ℤ) (hD : D.Pairwise (· > ·)) (T : Finset ℤ) (b : ℤ)
    (hT : ∀ z ∈ T, z ∈ D ∧ b ≤ z) (l : ℕ) (hl : l < T.card) (hlen : l < D.length) : b ≤ D[l] := by
  by_contra hlt
  push_neg at hlt
  have hsub : T ⊆ (D.take l).toFinset := by
    intro z hz
    obtain ⟨hzD, hbz⟩ := hT z hz
    obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hzD
    have hil : i < l := by
      by_contra h
      push_neg at h
      rcases h.lt_or_eq with h | h
      · have := List.pairwise_iff_getElem.1 hD l i hlen hi h
        linarith
      · have e : D[l] = D[i] := by simp [h]
        linarith
    have hi' : i < (D.take l).length := by simp; omega
    have hm := List.getElem_mem hi'
    simp only [List.getElem_take] at hm
    exact List.mem_toFinset.2 hm
  have h1 := Finset.card_le_card hsub
  have h2 := List.toFinset_card_le (D.take l)
  simp only [List.length_take] at h2
  omega

section Fr

variable {n' r : ℕ} [NeZero n']

theorem fr_mono' {F : Frames n' r} {L₁ N₁ : ℕ} (hV : F.Valid L₁ N₁) (j : ℤ) : ∀ i, i < r → F.fr j 0 ≤ F.fr j i := by
  intro i hi
  induction i with
  | zero => exact le_rfl
  | succ i ih => exact le_trans (ih (by omega)) (le_of_lt (hV.2.2.1 j i hi))

theorem fr_lt {F : Frames n' r} {L₁ N₁ : ℕ} (hV : F.Valid L₁ N₁) (j : ℤ) :
    ∀ k i, i < k → k < r → F.fr j i < F.fr j k := by
  intro k i hik hk
  induction k with
  | zero => omega
  | succ k ih =>
    rcases Nat.lt_succ_iff_lt_or_eq.1 hik with h | h
    · exact lt_trans (ih h (by omega)) (hV.2.2.1 j k hk)
    · subst h
      exact hV.2.2.1 j i hk

theorem seg_of {F : Frames n' r} {L₁ N₁ : ℕ} (hV : F.Valid L₁ N₁) (hr : 1 ≤ r) (s : ℤ) :
    ∃ j : ℤ, F.fr (j - 1) (r - 1) < s ∧ s ≤ F.fr j (r - 1) := by
  classical
  have hn : (1 : ℤ) ≤ (n' : ℤ) := by
    have : n' ≠ 0 := NeZero.ne n'
    omega
  have hstep : ∀ j : ℤ, F.fr j (r - 1) < F.fr (j + 1) (r - 1) := by
    intro j
    exact lt_of_lt_of_le (hV.2.2.2.1 j) (fr_mono' hV (j + 1) (r - 1) (by omega))
  have hmono : StrictMono (fun j : ℤ => F.fr j (r - 1)) := strictMono_int_of_lt_succ hstep
  have hup : ∀ m : ℕ, F.fr 0 (r - 1) + m ≤ F.fr ((m : ℤ) * F.J) (r - 1) := by
    intro m
    induction m with
    | zero => simp
    | succ m ih =>
      have h := hV.2.1 ((m : ℤ) * F.J) (r - 1)
      rw [show ((m + 1 : ℕ) : ℤ) * (F.J : ℤ) = (m : ℤ) * F.J + F.J by push_cast; ring, h]
      push_cast
      omega
  have hdown : ∀ m : ℕ, F.fr (-((m : ℤ) * F.J)) (r - 1) + m ≤ F.fr 0 (r - 1) := by
    intro m
    induction m with
    | zero => simp
    | succ m ih =>
      have h := hV.2.1 (-(((m + 1 : ℕ) : ℤ) * F.J)) (r - 1)
      rw [show -(((m + 1 : ℕ) : ℤ) * (F.J : ℤ)) + F.J = -((m : ℤ) * F.J) by push_cast; ring] at h
      push_cast at h ⊢
      omega
  have hP : ∃ j : ℤ, s ≤ F.fr j (r - 1) := by
    refine ⟨((s - F.fr 0 (r - 1)).toNat : ℤ) * F.J, ?_⟩
    have := hup (s - F.fr 0 (r - 1)).toNat
    omega
  have hB : ∃ b : ℤ, ∀ j : ℤ, s ≤ F.fr j (r - 1) → b ≤ j := by
    refine ⟨-(((F.fr 0 (r - 1) - s + 1).toNat : ℤ) * F.J), fun j hj => ?_⟩
    have h1 := hdown (F.fr 0 (r - 1) - s + 1).toNat
    by_contra hlt
    push_neg at hlt
    have h2 : F.fr j (r - 1) < F.fr (-(((F.fr 0 (r - 1) - s + 1).toNat : ℤ) * F.J)) (r - 1) := hmono hlt
    omega
  obtain ⟨j, hj, hmin⟩ := Int.exists_least_of_bdd hB hP
  refine ⟨j, ?_, hj⟩
  by_contra h
  push_neg at h
  have := hmin (j - 1) h
  omega

theorem evensBefore_pairwise (F : Frames n' r) (s : ℤ) : (evensBefore F s).Pairwise (· > ·) := by
  unfold evensBefore
  rw [List.pairwise_reverse]
  exact (Finset.sortedLT_sort _).pairwise

theorem arow_near {TT : Finset (Fin n')} {L₁ L₂ N₁ G' : ℕ} {F : Frames n' r} (hF : FramesOK TT L₁ L₂ N₁ G' F)
    (hr : 1 ≤ r) (hG : G' ≤ n') (s : ℤ) (l : ℕ) (hl : l < r) : (s - Arow F s l).toNat ≤ G' := by
  obtain ⟨-, hV, hG', -, -⟩ := hF
  obtain ⟨j, hj1, hj2⟩ := seg_of hV hr s
  unfold Arow
  by_cases hlen : l < (evensBefore F s).length
  · rw [List.getD_eq_getElem _ _ hlen]
    have hrn : (G' : ℤ) ≤ (r : ℤ) * (n' : ℤ) := by
      have : G' ≤ r * n' := le_trans hG (by nlinarith)
      exact_mod_cast this
    have key : s - (G' : ℤ) ≤ (evensBefore F s)[l] := by
      refine getElem_ge_of_many (evensBefore F s) (evensBefore_pairwise F s)
        ((Finset.range r).image (fun i => F.fr (j - 1) i)) (s - G') ?_ l ?_ hlen
      · intro z hz
        simp only [Finset.mem_image, Finset.mem_range] at hz
        obtain ⟨i, hi, rfl⟩ := hz
        have h0 := fr_mono' hV (j - 1) i hi
        have h1 : F.fr (j - 1) i ≤ F.fr (j - 1) (r - 1) := by
          rcases Nat.lt_or_ge i (r - 1) with h | h
          · exact le_of_lt (fr_lt hV (j - 1) (r - 1) i h (by omega))
          · have : i = r - 1 := by omega
            rw [this]
        have h2 := hG' j
        have h3 := hV.2.2.2.2.1 (j - 1) i hi
        refine ⟨?_, by omega⟩
        simp only [evensBefore, List.mem_reverse, Finset.mem_sort, Finset.mem_filter, Finset.mem_Ico]
        exact ⟨⟨by omega, by omega⟩, h3.1, h3.2⟩
      · rw [Finset.card_image_of_injOn]
        · simpa using hl
        · intro a ha b hb hab
          simp only [Finset.coe_range, Set.mem_Iio] at ha hb
          simp only at hab
          by_contra hne
          rcases Nat.lt_or_gt_of_ne hne with h | h
          · have := fr_lt hV (j - 1) b a h hb
            omega
          · have := fr_lt hV (j - 1) a b h ha
            omega
    omega
  · rw [List.getD_eq_default _ _ (by omega)]
    simp

theorem twist_of {TT : Finset (Fin n')} {L₁ L₂ N₁ G' : ℕ} {F : Frames n' r} (hF : FramesOK TT L₁ L₂ N₁ G' F)
    (hr : 1 ≤ r) (hG : G' ≤ n') (p : ℕ) (hp : 1 ≤ p) : TwistBound p F (p ^ G') := by
  refine ⟨fun j => ?_, fun s _ l hl => Nat.pow_le_pow_right (by omega) (arow_near hF hr hG s.val l hl)⟩
  unfold Qj zF
  apply Nat.pow_le_pow_right (by omega)
  have h1 := hF.2.2.1 (j + 1)
  have h2 := fr_mono' hF.2.1 j (r - 1) (by omega)
  simp only [add_sub_cancel_right] at h1
  omega

end Fr

end Formalism.MainNotions.Pf14
end
end

-- bundled from Formalism.SharpRestriction.GrowthBounds.ScaleEdges.FlatSrc
section
noncomputable section

namespace Formalism.MainNotions.Pf14

open Formalism.MainNotions.G Formalism.GradedWeylDivisibility Formalism.MainNotions.SourceCleaning MvPolynomial

def vecE (n' : ℕ) : Fin n' → Bool := fun s => decide (Even s.val)

def flW {n' m : ℕ} (d : Fin n' → ℕ) : Fin n' → Fin (m + 1) → ℤ := fun s => Pi.single 0 (d s : ℤ)

theorem isFlat_flW {n' m : ℕ} (d : Fin n' → ℕ) : IsFlat (m := m) (vecE n') d (flW d) := by
  intro s
  by_cases hs : Even s.val
  · simp [lamAt, vecE, flW, hs]
  · funext i
    simp only [lamAt, vecE, flW, hs, if_false, decide_false, Bool.false_eq_true]
    by_cases hi : i = Fin.last m
    · subst hi
      simp
    · have hr : i.rev ≠ 0 := by
        intro h0
        apply hi
        rw [← Fin.rev_rev i, h0, Fin.rev_zero]
      simp [hi, hr]

section Scale

variable {O Kf X : Type*} [CommRing O] [Field Kf] [Algebra O Kf] [AddCommGroup X] [Module Kf X] [Module O X]
  [IsScalarTower O Kf X]

theorem scale_shift (c : Kf) (hc : c ≠ 0) (a b : ℕ) (M : Submodule O X) {x : X}
    (hx : x ∈ scale (c ^ ((a + b : ℕ) : ℤ)) M) : (c ^ (-(a : ℤ))) • x ∈ scale (c ^ (b : ℤ)) M := by
  rw [mem_scale] at hx ⊢
  obtain ⟨y, hy, rfl⟩ := hx
  refine ⟨y, hy, ?_⟩
  rw [smul_smul, ← zpow_add₀ hc, show -(a : ℤ) + ((a + b : ℕ) : ℤ) = b by push_cast; ring]

end Scale

def IsFlatIdent {p n' : ℕ} [Fact p.Prime] {W Qq O Kf : Type} [CommRing W] [Field Qq]
    [Algebra W Qq] [CommRing O] [IsDomain O] [Field Kf] [Algebra O Kf]
    (ι : Qq →+* Kf) (σ : Qq ≃+* Qq) (w : O) (φ : WF p n' ≃+* W) [Algebra (WF p n') O] {m : ℕ} (r : ℕ)
    (d : Fin n' → ℕ) (lam0 : Fin n' → Fin (m + 1) → ℤ) (vec : Fin n' → Bool)
    (h : Matrix (Fin (m + 1)) (Fin (m + 1)) Qq)
    (Θ : ↥((Pol (KK O) (ι := Fin n') (m + 1) d).restrictScalars O) ≃ₗ[O] ↥(Vsp Kf lam0)) : Prop :=
  (∀ F : ↥((Pol (KK O) (ι := Fin n') (m + 1) d).restrictScalars O),
    InA (O := O) (F : MvPolynomial (Fin n' × Fin (m + 1)) (KK O)) ↔
    Θ F ∈ HL (O := O) ι σ lam0 (colSpan W h)) ∧
  ∀ g : Matrix (Fin (m + 1)) (Fin (m + 1)) (WF p n'), IsGLW g →
    ∀ e : Edge W Qq (m + 1), IsEdgeBasis p r e (h * ((matQ φ g)⁻¹).transpose) →
      ∀ (F : ↥((Pol (KK O) (ι := Fin n') (m + 1) d).restrictScalars O)) (i : ℕ),
        InWjRg p n' O w r (flatLetters vec) g
          (F : MvPolynomial (Fin n' × Fin (m + 1)) (KK O)) i ↔
        Θ F ∈ scale (algebraMap O Kf w ^ (i : ℤ)) (Re p ι σ w r lam0 e)

theorem flatSrc (hEP : EdgePlane) (p n' : ℕ) [Fact p.Prime] (W Qq O Kf : Type) [CommRing W] [IsDomain W]
    [IsDiscreteValuationRing W] [Field Qq] [Algebra W Qq] [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    [Field Kf] [Algebra O Kf] (ι : Qq →+* Kf) (σ : Qq ≃+* Qq) (j : W →+* O) (w : O)
    (hS : HidaSetting p n' W Qq O Kf ι σ j w) (φ : WF p n' ≃+* W) (hφ : IsWittIdent σ φ)
    (m r : ℕ) (d : Fin n' → ℕ) (h : Matrix (Fin (m + 1)) (Fin (m + 1)) Qq) (hh : IsUnit h.det) :
    letI : Algebra (WF p n') O := algOfIdent j φ
    ∀ Θ : ↥((Pol (KK O) (ι := Fin n') (m + 1) d).restrictScalars O) ≃ₗ[O] ↥(Vsp Kf (flW (m := m) d)),
      IsFlatIdent ι σ w φ r d (flW d) (vecE n') h Θ →
    ∀ g : Matrix (Fin (m + 1)) (Fin (m + 1)) (WF p n'), IsGLW g →
    ∀ e : Edge W Qq (m + 1), IsEdgeBasis p r e (h * ((matQ φ g)⁻¹).transpose) →
    ∀ (c' o : ℕ) (sig : MvPolynomial (TV n' (m + 1)) (KK O))
      (Fsig : ↥((Pol (KK O) (ι := Fin n') (m + 1) d).restrictScalars O)),
      HasMultideg sig d → subst p n' O w n' r g (Fsig : MvPolynomial (TV n' (m + 1)) (KK O)) = sig →
      Realisable p n' w n' r g c' o sig →
      ∃ Fv : Vsp Kf (flW (m := m) d),
        Fv ∈ scale (algebraMap O Kf w ^ (-(o : ℤ))) (HL (O := O) ι σ (flW d) (colSpan W h)) ∧
        Fv - Θ Fsig ∈ scale (algebraMap O Kf w ^ (c' : ℤ)) (Re p ι σ w r (flW d) e) ∧
        ∀ e' : Edge W Qq (m + 1), IsEdge p n' r e' → e'.src = colSpan W h → e' ≠ e →
          Fv ∈ scale (algebraMap O Kf w ^ (c' : ℤ)) (Re p ι σ w r (flW d) e') := by
  let _ : Algebra (WF p n') O := algOfIdent j φ
  intro Θ hΘ g hg e he c' o sig Fsig hsig hsub hreal
  obtain ⟨F, hFA, hFdeg, hFW, hFo⟩ := hreal
  obtain ⟨F', rfl⟩ : ∃ F' : ↥((Pol (KK O) (ι := Fin n') (m + 1) d).restrictScalars O),
      (F' : MvPolynomial (Fin n' × Fin (m + 1)) (KK O)) = F := ⟨⟨F, hFdeg d hsig⟩, rfl⟩
  have hc0 : algebraMap O Kf w ≠ 0 := w_ne_zero hS
  obtain ⟨hE1, -, hE3⟩ := hEP p n' W Qq O Kf ι σ j w hS φ hφ m r h hh
  refine ⟨(algebraMap O Kf w ^ (-(o : ℤ))) • Θ F', ?_, ?_, ?_⟩
  · exact mem_scale.mpr ⟨Θ F', (hΘ.1 F').mp hFA, rfl⟩
  · have key : InWjRg p n' O w r (flatLetters (vecE n')) g
        ((F' - (w ^ o) • Fsig : ↥((Pol (KK O) (ι := Fin n') (m + 1) d).restrictScalars O)) :
          MvPolynomial (Fin n' × Fin (m + 1)) (KK O)) (o + c') := by
      show InWj w (subst p n' O w n' r g _) (o + c')
      have hx : ((F' - (w ^ o) • Fsig : ↥((Pol (KK O) (ι := Fin n') (m + 1) d).restrictScalars O)) :
          MvPolynomial (Fin n' × Fin (m + 1)) (KK O)) =
          (F' : MvPolynomial (Fin n' × Fin (m + 1)) (KK O)) -
            C (algebraMap O (KK O) (w ^ o)) * (Fsig : MvPolynomial (Fin n' × Fin (m + 1)) (KK O)) := by
        rw [Submodule.coe_sub, Submodule.coe_smul_of_tower, ← algebraMap_smul (KK O), smul_eq_C_mul]
      rw [hx, map_sub, map_mul, hsub, ← MvPolynomial.algebraMap_eq, AlgHom.commutes,
        MvPolynomial.algebraMap_eq]
      exact hFW
    have hmem := scale_shift (algebraMap O Kf w) hc0 o c' _ ((hΘ.2 g hg e he _ (o + c')).mp key)
    have heq : (algebraMap O Kf w ^ (-(o : ℤ))) • Θ (F' - (w ^ o) • Fsig) =
        (algebraMap O Kf w ^ (-(o : ℤ))) • Θ F' - Θ Fsig := by
      rw [show Θ (F' - (w ^ o) • Fsig) = Θ F' - Θ ((w ^ o) • Fsig) from Θ.map_sub _ _,
        show Θ ((w ^ o) • Fsig) = (w ^ o) • Θ Fsig from Θ.map_smul _ _,
        ← algebraMap_smul Kf (w ^ o), smul_sub, smul_smul, map_pow,
        ← zpow_natCast, ← zpow_add₀ hc0, neg_add_cancel, zpow_zero, one_smul]
    rwa [heq] at hmem
  · intro e' he' hsrc hne
    obtain ⟨g', hg', hb'⟩ := hE1 e' he' hsrc
    have hrat : ratPlane p n' r g' ≠ ratPlane p n' r g := fun hr =>
      hne ((hE3 g' g e' e hg' hg hb' he).mpr hr)
    exact scale_shift (algebraMap O Kf w) hc0 o c' _
      ((hΘ.2 g' hg' e' hb' F' (o + c')).mp (hFo g' hg' hrat))

end Formalism.MainNotions.Pf14
end
end

