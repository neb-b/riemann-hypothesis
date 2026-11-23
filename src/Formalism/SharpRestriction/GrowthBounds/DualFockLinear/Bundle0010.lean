module

public import Formalism.SharpRestriction.GrowthBounds.DualFockLinear.Bundle0009

@[expose] public section

-- bundled from Formalism.SharpRestriction.GrowthBounds.DualFockLinear.PairFormula
section
noncomputable section

open MvPolynomial

namespace Formalism.MainNotions.TestSideCounting

open Formalism.MainNotions.G Formalism.GradedWeylDivisibility Formalism.MainNotions.Pf14 Formalism.MainNotions.SourceCleaning
open Formalism.MainNotions.G.LatticeSystems (la_tw lb_D la_tw_det lb_D_det)
open Formalism.L2.G.Model (Lin Th0 Aa Lin_comp Lin_one Lin_Pol Lin_smul map_Pol mem_Pol
  dE invT_mul_D w_ne p_eq pQ_ne kapR kapR_alg lift_eq Bm Bm_eq Mx Mx_det Avec pol_iff thF flat_Ar)
open Formalism.L2.G.Model.TS

theorem Aa_dual2 {K : Type} [Field K] {m : ℕ} (vec : Bool) (M : Matrix (Fin (m + 1)) (Fin (m + 1)) K)
    (hM : IsUnit M.det) : Aa vec ((M⁻¹).transpose) * (Aa vec M).transpose = 1 := by
  have hMt : IsUnit ((M⁻¹).transpose).det := by
    rw [Matrix.det_transpose, Matrix.det_nonsing_inv]; exact hM.ringInverse
  cases vec
  · simp only [Aa, Bool.false_eq_true, if_false]
    rw [← Matrix.transpose_mul, Matrix.mul_nonsing_inv _ hMt, Matrix.transpose_one]
  · simp only [Aa, if_true]
    rw [← Matrix.transpose_mul, Matrix.mul_nonsing_inv _ hM, Matrix.transpose_one]

section

variable {p n' : ℕ} [Fact p.Prime] {W Qq O Kf : Type} [CommRing W] [IsDomain W] [IsDiscreteValuationRing W] [Field Qq]
  [Algebra W Qq] [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field Kf] [Algebra O Kf]
  {ι : Qq →+* Kf} {σ : Qq ≃+* Qq} {j : W →+* O} {w : O} {m : ℕ} {d : Fin n' → ℕ}

theorem subst_Lin (hS : HidaSetting p n' W Qq O Kf ι σ j w) (φ : WF p n' ≃+* W) (hφ : IsWittIdent σ φ) (r : ℕ)
    (hmat : Matrix (Fin (m + 1)) (Fin (m + 1)) Qq) (hh : IsUnit hmat.det)
    (g : Matrix (Fin (m + 1)) (Fin (m + 1)) (WF p n')) (hg : IsGLW g)
    (F : MvPolynomial (Fin n' × Fin (m + 1)) (KK O)) (hF : F ∈ Pol (KK O) (m + 1) d) :
    letI : Algebra (WF p n') O := algOfIdent j φ
    map (kapR hS) (subst p n' O w n' r g F) = (algebraMap O Kf w ^ Avec (vecE n') d) •
      Lin (fun x => Aa (vecE n' x) (Mx ι σ w φ r (fun x => x) hmat g x))
        (Lin (fun x => Aa (vecE n' x) (la_tw ι σ x.val hmat)⁻¹) (map (kapR hS) F)) := by
  letI : Algebra (WF p n') O := algOfIdent j φ
  have hw := w_ne hS
  have hF' := (pol_iff hS _ _ _).1 hF
  have h1 : map (kapR hS) (subst p n' O w n' r g F) =
      Lin (Bm ι σ w φ r (vecE n') (fun x => x) g) (map (kapR hS) F) :=
    lift_eq hS φ hφ r (LLT n') (fun x => x) (fun _ => rfl) g hg F
  have hB : Bm ι σ w φ r (vecE n') (fun x => x) g = fun x => (if vecE n' x then algebraMap O Kf w else 1) •
      (Aa (vecE n' x) (la_tw ι σ x.val hmat)⁻¹ * Aa (vecE n' x) (Mx ι σ w φ r (fun x => x) hmat g x)) :=
    funext fun x => Bm_eq hw φ r (vecE n') (fun x => x) hmat hh g hg x
  rw [h1, hB, Lin_smul _ _ _ hF', Lin_comp]
  congr 1
  unfold Avec
  rw [← Finset.prod_pow_eq_pow_sum]
  apply Finset.prod_congr rfl
  intro x _
  split_ifs <;> simp

variable (thK : ↥(Pol Kf (ι := Fin n') (m + 1) d) ≃ₗ[Kf] ↥(Vsp Kf (flW (m := m) d)))

theorem pair_formula (hS : HidaSetting p n' W Qq O Kf ι σ j w) (φ : WF p n' ≃+* W) (hφ : IsWittIdent σ φ)
    (r : ℕ) (hr1 : 1 ≤ r) (hr2 : r < m + 1)
    (hthK : ∀ P, ((thK P : ↥(Vsp Kf (flW (m := m) d))) : MvPolynomial (Fin n' × (Fin (m + 1) × Fin (m + 1))) Kf) =
      Th0 Kf m (vecE n') (P : MvPolynomial (Fin n' × Fin (m + 1)) Kf)) (κ : ℕ)
    (hmat : Matrix (Fin (m + 1)) (Fin (m + 1)) Qq) (hh : IsUnit hmat.det)
    (g gv : Matrix (Fin (m + 1)) (Fin (m + 1)) (WF p n')) (hg : IsGLW g) (hgv : IsGLW gv)
    (hb : IsUnit (hmat * ((matQ φ g)⁻¹).transpose).det)
    (hrel : ((matQ φ gv)⁻¹).transpose =
      ((hmat * ((matQ φ g)⁻¹).transpose)⁻¹).transpose * dE (m + 1) r ((p : ℕ) : Qq))
    (Θ Θv : ↥((Pol (KK O) (ι := Fin n') (m + 1) d).restrictScalars O) ≃ₗ[O] ↥(Vsp Kf (flW (m := m) d)))
    (hΘ : IsTrueTheta hS d (flW d) (vecE n') hmat Θ) (hΘv : IsTrueTheta hS d (flW d) (vecE n') 1 Θv)
    (F Fv : ↥((Pol (KK O) (ι := Fin n') (m + 1) d).restrictScalars O)) :
    letI : Algebra (WF p n') O := algOfIdent j φ
    be p r (flW d) (Θ F) (TY thK ((p : Kf) ^ κ / (((∏ s, (d s).factorial : ℕ) : ℕ) : Kf)) (Θv Fv)) =
      kapR hS ((p : KK O) ^ κ * fock (subst p n' O w n' r g (F : MvPolynomial (TV n' (m + 1)) (KK O)))
        (subst p n' O w n' r gv (Fv : MvPolynomial (TV n' (m + 1)) (KK O))) /
          (((∏ s, (d s).factorial : ℕ) : ℕ) : KK O)) := by
  letI : Algebra (WF p n') O := algOfIdent j φ
  have h1d : IsUnit (1 : Matrix (Fin (m + 1)) (Fin (m + 1)) Qq).det := by simp
  let P : ↥(Pol Kf (ι := Fin n') (m + 1) d) :=
    ⟨Lin (fun x => Aa (vecE n' x) (la_tw ι σ x.val hmat)⁻¹) (map (kapR hS) F.1),
      Lin_Pol _ _ ((pol_iff hS _ _ _).1 F.2)⟩
  let Q : ↥(Pol Kf (ι := Fin n') (m + 1) d) :=
    ⟨Lin (fun x => Aa (vecE n' x) (la_tw ι σ x.val (1 : Matrix (Fin (m + 1)) (Fin (m + 1)) Qq))⁻¹)
      (map (kapR hS) Fv.1), Lin_Pol _ _ ((pol_iff hS _ _ _).1 Fv.2)⟩
  have eF : Θ F = thK P := Subtype.ext (by rw [hΘ F, hthK]; rfl)
  have eFv : Θv Fv = thK Q := Subtype.ext (by rw [hΘv Fv, hthK]; rfl)
  have hdual : ∀ s : Fin n', Aa (vecE n' s) (Mx ι σ w φ r (fun x => x) 1 gv s) *
      (Aa (vecE n' s) (Mx ι σ w φ r (fun x => x) hmat g s)).transpose = 1 := by
    intro s
    have e1 : Mx ι σ w φ r (fun x => x) 1 gv s = ((Mx ι σ w φ r (fun x => x) hmat g s)⁻¹).transpose := by
      unfold Mx
      rw [Matrix.one_mul, hrel]
      exact dualM hS s.val r _ hb
    rw [e1]
    exact Aa_dual2 _ _ (Mx_det (w_ne hS) φ r (fun x => x) hmat hh g hg s)
  have hL : be p r (flW d) (Θ F) (TY thK ((p : Kf) ^ κ / (((∏ s, (d s).factorial : ℕ) : ℕ) : Kf)) (Θv Fv)) =
      (p : Kf) ^ Ar r (flW (m := m) d) * (((p : Kf) ^ κ / (((∏ s, (d s).factorial : ℕ) : ℕ) : Kf)) *
        fockR (P : MvPolynomial (Fin n' × Fin (m + 1)) Kf) (Q : MvPolynomial (Fin n' × Fin (m + 1)) Kf)) := by
    unfold be
    rw [eF, eFv, map_smul, smul_eq_mul, TY_apply]
  rw [hL, map_div₀, map_mul, map_pow, map_natCast, map_natCast, fock_eq_fockR, ← fockR_map,
    subst_Lin hS φ hφ r hmat hh g hg F.1 F.2, subst_Lin hS φ hφ r 1 h1d gv hgv Fv.1 Fv.2, tsact_smul_left,
    tsact_smul_right, fockR_Lin_dual _ _ hdual, flat_Ar r hr1 hr2 (vecE n') d (flW d) (isFlat_flW d), zpow_natCast,
    p_eq hS]
  show _ = _ * (_ * (_ * fockR (P : MvPolynomial (Fin n' × Fin (m + 1)) Kf)
    (Q : MvPolynomial (Fin n' × Fin (m + 1)) Kf))) / _
  ring

theorem exists_gv (hS : HidaSetting p n' W Qq O Kf ι σ j w) (φ : WF p n' ≃+* W) {k : ℕ} (X : Matrix (Fin k) (Fin k) Qq)
    (h : colSpan W X = colSpan W (1 : Matrix (Fin k) (Fin k) Qq)) :
    ∃ gv : Matrix (Fin k) (Fin k) (WF p n'), IsGLW gv ∧ matQ φ gv = X := by
  have := hS.frac_alt
  have hinj : Function.Injective (algebraMap W Qq) := IsFractionRing.injective W Qq
  have h1 : ∀ c : Fin k, ∃ y : Fin k → W, (fun i => X i c) =
      (1 : Matrix (Fin k) (Fin k) Qq).mulVec (fun a => algebraMap W Qq (y a)) := by
    intro c
    apply (mem_colSpan _ _).1
    rw [← h]
    exact Submodule.subset_span ⟨c, rfl⟩
  have h2 : ∀ c : Fin k, ∃ y : Fin k → W, (fun i => (1 : Matrix (Fin k) (Fin k) Qq) i c) =
      X.mulVec (fun a => algebraMap W Qq (y a)) := by
    intro c
    apply (mem_colSpan _ _).1
    rw [h]
    exact Submodule.subset_span ⟨c, rfl⟩
  choose Y hY using h1
  choose Y' hY' using h2
  let Cm : Matrix (Fin k) (Fin k) W := fun i c => Y c i
  let Cm' : Matrix (Fin k) (Fin k) W := fun i c => Y' c i
  have hX : X = Cm.map (algebraMap W Qq) := by
    ext i c
    have := congrFun (hY c) i
    rw [Matrix.one_mulVec] at this
    exact this
  have hprod : Cm * Cm' = 1 := by
    apply Matrix.map_injective hinj
    show (Cm * Cm').map (algebraMap W Qq) = (1 : Matrix (Fin k) (Fin k) W).map (algebraMap W Qq)
    rw [Matrix.map_mul, ← hX, Matrix.map_one _ (map_zero _) (map_one _)]
    ext i c
    have := congrFun (hY' c) i
    rw [Matrix.mul_apply]
    exact this.symm
  have hdet : IsUnit Cm.det := by
    have : Cm.det * Cm'.det = 1 := by rw [← Matrix.det_mul, hprod, Matrix.det_one]
    exact IsUnit.of_mul_eq_one _ this
  refine ⟨(φ.symm : W →+* WF p n').mapMatrix Cm, ?_, ?_⟩
  · unfold IsGLW
    rw [← RingHom.map_det]
    exact hdet.map _
  · rw [hX]
    ext a c
    simp [matQ, RingHom.mapMatrix_apply, Matrix.map_apply]

end

end Formalism.MainNotions.TestSideCounting
end
end

-- bundled from Formalism.SharpRestriction.GrowthBounds.DualFockLinear.RestNDOfAdm
section
noncomputable section

open MvPolynomial Finset Classical

namespace Formalism.MainNotions.TestSideCounting

open Formalism.MainNotions.G Formalism.GradedWeylDivisibility Formalism.MainNotions.SourceCleaning Formalism.MainNotions.Pf14 Formalism.MainNotions.G.WittFrameLocaliserOrders
open Formalism.L2.G.Model (Lin)


set_option maxHeartbeats 1000000 in
theorem restND_of_adm (D : Formalism.BasicNotions.D7) (CLa Ck Crk Cdeg : ℝ) (hA : tableLineDegreeFive.admitted D CLa Ck Crk Cdeg) : RestND CLa := by
  have h26 : Formalism.MainNotions.SelectionLemmas.Conclusion2 D CLa Ck Crk Cdeg := hA.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  obtain ⟨Cg, hCg1, hg2⟩ := symbol_space_at D CLa Ck Crk Cdeg h26
  refine ⟨max 1 |Cdeg|, max Cg |CLa|, lt_of_lt_of_le one_pos (le_max_left _ _),
    lt_of_lt_of_le (by linarith) (le_max_left _ _), ?_⟩
  intro C hC p W Qq O Kf _ _ _ _ _ _ _ _ _ _ ι σ j w n' m r _ _ TT L₁ L₂ de h x lam0 aT bT a Y cpp c0 Dp cStar hSet H φ hφ K
    _ _ hk hrk F hF E' hE' nb B hB hli hc e he htgt hm g hhm hg hbasis
  have c1 : Cg ≤ C := le_trans (le_max_left _ _) hC
  have c5 : |CLa| ≤ C := le_trans (le_max_right _ _) hC
  have hBa := hyps_basic (C := C) (by linarith) H
  have ha1 : (1 : ℝ) ≤ a := by linarith [hBa.two_le_a]
  have hr2 : 2 ≤ r := H.2.1
  have hn : Even n' := hSet.1.even
  have hTT := hF.1
  subst hTT
  letI : Algebra (WF p n') O := algOfIdent j φ
  intro FsB hFsB Θ hΘ
  obtain ⟨-, hdeg⟩ := hg2 C c1 p W Qq O Kf ι σ j w n' m r F.TT L₁ L₂ de h x lam0 aT bT a Y cpp c0 Dp cStar hSet H K hk F hF
    E' (fun t ht => (hE' t ht).1)
  set X : ℝ := Cdeg * (F.TT.card : ℝ) *
    (CLa * ((min (orbitWindowCount r de h x) (2 * F.TT.card) : ℕ) : ℝ) ^ 2 * Real.log a * a / ((p : ℝ) * ((r + K : ℕ) : ℝ)) +
      a * (p : ℝ) ^ (-(L₁ : ℤ)) + ((r + K : ℕ) : ℝ) * (p : ℝ) ^ goodG' r de h x) with hX
  have hT : ∀ i, ∀ mm ∈ (B i).support, vsDeg mm ≤ ⌊X⌋₊ := fun i mm hmm =>
    Nat.le_floor (hdeg (B i) (Submodule.subset_span (hB i)) mm hmm)
  have hXt : X ≤ t0 C (max 1 |Cdeg|) p F.TT.card (orbitWindowCount r de h x) L₁ (goodG' r de h x) (m + 1) a := by
    have e1 : t0 C (max 1 |Cdeg|) p F.TT.card (orbitWindowCount r de h x) L₁ (goodG' r de h x) (m + 1) a =
        t0 C (max 1 |Cdeg|) p F.TT.card (orbitWindowCount r de h x) L₁ (goodG' r de h x) (r + K) a := by rw [hk]
    rw [e1]
    exact level_lower_bound_terms Cdeg CLa C (max 1 |Cdeg|) (le_max_right _ _) c5 p F.TT.card (orbitWindowCount r de h x)
      (min (orbitWindowCount r de h x) (2 * F.TT.card)) L₁ (goodG' r de h x) (r + K) (min_le_left _ _)
      (by have := H.1; omega) (by omega) a ha1
  have ht0 : 0 ≤ t0 C (max 1 |Cdeg|) p F.TT.card (orbitWindowCount r de h x) L₁ (goodG' r de h x) (m + 1) a :=
    initial_level_nonneg (le_trans (abs_nonneg _) c5) (le_trans zero_le_one (le_max_left _ _)) _ _ _ _ _ _ ha1
  have hfl : ((⌊X⌋₊ : ℕ) : ℝ) ≤ t0 C (max 1 |Cdeg|) p F.TT.card (orbitWindowCount r de h x) L₁ (goodG' r de h x) (m + 1) a := by
    by_cases hX0 : 0 ≤ X
    · exact le_trans (Nat.floor_le hX0) hXt
    · rw [Nat.floor_of_nonpos (le_of_lt (not_le.1 hX0))]
      simpa using ht0
  have hw : algebraMap O (KK O) w ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective O (KK O))).2 hSet.2.1.ne_zero
  have hbase : ∀ b, subst p n' O w n' r g (FsB b : MvPolynomial (TV n' (m + 1)) (KK O)) ∈
      NDsub (KK O) n' (m + 1) r ⌊X⌋₊ := by
    intro b
    rw [hFsB b]
    unfold symB toK
    rw [subst_SPtrue w F hF.2.1 hn (by omega) hrk hg]
    have h1 := nd_mul (nd_map (algebraMap O (KK O)) (nd_rename (n' := n') (R := O) hk (hT b)))
      (nd_map (algebraMap O (KK O)) (fixed_symbol_normal_degree_zero (R := O) p F hF.2.1 hn (by omega) hrk
        (cPrime n' r F.TT.card c0 cpp cStar) (p ^ goodG' r de h x)))
    rw [add_zero] at h1
    exact h1
  refine ⟨⌊X⌋₊ + F.TT.card * c0, ?_, ?_⟩
  · push_cast
    linarith
  · intro f hf mm hmm
    rw [subst_eq_Lin] at hmm
    refine mem_NDsub.1 (nd_OpCl (Nsub p n' O w r g) (NsubInv p n' O w r g) (Nsub_mul p n' O w r hw hg) r ⌊X⌋₊ F.TT c0 _
      ?_ f hf) mm hmm
    intro f0 hf0
    induction hf0 using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨b, rfl⟩ := hy
      rw [← subst_eq_Lin]
      exact hbase b
    | zero => rw [map_zero]; exact Submodule.zero_mem _
    | add x y _ _ hx hy => rw [map_add (f := _)]; exact Submodule.add_mem _ hx hy
    | smul a x _ hx => rw [map_smul]; exact Submodule.smul_mem _ _ hx

theorem restXi_of_N (D : Formalism.BasicNotions.D7) (CLa Ck Crk Cdeg CH CE C6 C18 : ℝ)
    (hN : RestXiN D CLa Ck Crk Cdeg CH CE C6 C18) : RestXi D CLa Ck Crk Cdeg CH CE C6 C18 :=
  fun hA h14b => restXi_of D CLa Ck Crk Cdeg CH CE C6 C18 hN (restND_of_adm D CLa Ck Crk Cdeg hA) hA h14b

end Formalism.MainNotions.TestSideCounting
end
end

-- bundled from Formalism.SharpRestriction.GrowthBounds.DualFockLinear.VFlatSupported
section
noncomputable section

namespace Formalism.MainNotions.TestSideCounting

open Formalism.MainNotions.G Formalism.GradedWeylDivisibility Formalism.MainNotions.SourceCleaning Formalism.MainNotions.Pf14 MvPolynomial
open Formalism.MainNotions.G.LatticeSystems (lb_D lb_D_det)

section At

variable (p n' : ℕ) {W Qq O Kf : Type} [CommRing W] [Field Qq] [Algebra W Qq] [CommRing O] [IsDomain O] [Field Kf]
  [Algebra O Kf] (ι : Qq →+* Kf) (σ : Qq ≃+* Qq) (w : O) {m : ℕ} (r : ℕ) (TT : Finset (Fin n')) (d : Fin n' → ℕ)
  (rest lam : Fin n' → Fin (m + 1) → ℤ)

def RhoAtG (c0 loss κ : ℕ) (e : Edge W Qq (m + 1)) (Θ : ↥((Pol (KK O) (ι := Fin n') (m + 1) d).restrictScalars O) ≃ₗ[O] ↥(Vsp Kf (flW (m := m) d))) : Prop :=
  ∃ (Ix : Type) (ρ : Ix → (Vsp Kf lam →ₗ[Kf] Vsp Kf (flW (m := m) d))),
    (∀ β, ∀ u ∈ Re p ι σ w r lam e, ρ β u ∈ Re p ι σ w r (flW d) e) ∧
    (∀ β, ∀ e' : Edge W Qq (m + 1), IsEdge p n' r e' → e'.tgt = e.tgt → ∀ u ∈ Re p ι σ w r lam e',
      ρ β u ∈ scale (algebraMap O Kf w ^ (-(loss : ℤ))) (Re p ι σ w r (flW d) e')) ∧
    (∀ β, ∀ u ∈ HL (O := O) ι σ lam e.tgt,
      ρ β u ∈ scale ((p : Kf) ^ Ar r rest * algebraMap O Kf w ^ (-(loss : ℤ))) (HL (O := O) ι σ (flW d) e.tgt)) ∧
    (∀ β (F : ↥((Pol (KK O) (ι := Fin n') (m + 1) d).restrictScalars O)) (s : Vsp Kf rest) (u : Vsp Kf lam),
      ((u : Vsp Kf lam) : MvPolynomial (Fin n' × (Fin (m + 1) × Fin (m + 1))) Kf) = ((Θ F : Vsp Kf (flW (m := m) d)) : MvPolynomial (Fin n' × (Fin (m + 1) × Fin (m + 1))) Kf) * ((s : Vsp Kf rest) : MvPolynomial (Fin n' × (Fin (m + 1) × Fin (m + 1))) Kf) →
      ∃ F' : ↥((Pol (KK O) (ι := Fin n') (m + 1) d).restrictScalars O),
        (F' : MvPolynomial (Fin n' × Fin (m + 1)) (KK O)) ∈
          OpCl TT c0 (Submodule.span (KK O) {(F : MvPolynomial (Fin n' × Fin (m + 1)) (KK O))}) ∧ ρ β u = Θ F') ∧
    (∀ u ∈ Re p ι σ w r lam e,
      (∀ β, ρ β u ∈ scale (algebraMap O Kf w ^ ((2 * κ + 1 : ℕ) : ℤ)) (Re p ι σ w r (flW d) e)) →
      u ∈ scale (algebraMap O Kf w ^ (1 : ℤ)) (Re p ι σ w r lam e))

theorem rhoAt_of_G (lam0 : Fin n' → Fin (m + 1) → ℤ) (c0 loss : ℕ) (bK : ℝ) (e : Edge W Qq (m + 1))
    (Θ : ↥((Pol (KK O) (ι := Fin n') (m + 1) (dT TT lam0)).restrictScalars O) ≃ₗ[O] ↥(Vsp Kf (flW (m := m) (dT TT lam0))))
    (κ : ℕ) (hκ : (κ : ℝ) ≤ bK)
    (h : RhoAtG p n' ι σ w r TT (dT TT lam0) (restW TT lam0) lam0 c0 loss κ e Θ) :
    RhoAt p n' ι σ w r TT lam0 c0 loss bK e Θ := by
  obtain ⟨Ix, ρ, h1⟩ := h
  exact ⟨κ, Ix, ρ, hκ, h1⟩

end At

theorem V_flat_supported {Kf : Type} [Field Kf] {n' m : ℕ} (TT : Finset (Fin n')) (d : Fin n' → ℕ)
    (hd0 : ∀ s, s ∉ TT → d s = 0) :
    ∀ y ∈ Vsp Kf (flW (m := m) d), y ∈ supported Kf {v : Fin n' × (Fin (m + 1) × Fin (m + 1)) | v.1 ∈ TT} := by
  intro y hy
  unfold Vsp tensorLat at hy
  induction hy using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨F, hF, rfl⟩ := hx
    refine Subalgebra.prod_mem _ fun s _ => ?_
    by_cases hs : s ∈ TT
    · exact blockEmb_supported s _ (fun s => s ∈ TT) hs
    · have h0 : flW (m := m) d s = 0 := by
        unfold flW
        rw [hd0 s hs]
        simp
      have h1 := hF s
      simp only [lamAt_zero h0, if_pos (anti_zero m), nuOf_zero] at h1
      rw [dualWeyl_zero_const _ h1]
      unfold blockEmb
      rw [rename_C]
      exact Subalgebra.algebraMap_mem _ _
  | zero => exact Subalgebra.zero_mem _
  | add a b _ _ ha hb => exact Subalgebra.add_mem _ ha hb
  | smul t a _ ha => exact Subalgebra.smul_mem _ ha t


set_option maxHeartbeats 1600000 in
theorem rho_peel (D : Formalism.BasicNotions.D7) {p n' : ℕ} {W Qq O Kf : Type} [CommRing W] [IsDomain W] [IsDiscreteValuationRing W]
    [Field Qq] [Algebra W Qq] [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field Kf] [Algebra O Kf]
    {ι : Qq →+* Kf} {σ : Qq ≃+* Qq} {j : W →+* O} {w : O} (h : HidaSetting p n' W Qq O Kf ι σ j w) {m : ℕ} (r : ℕ)
    (TT : Finset (Fin n')) (d : Fin n' → ℕ) (hd0 : ∀ s, s ∉ TT → d s = 0)
    (rest lam restT lamT sp : Fin n' → Fin (m + 1) → ℤ) (hPl : Peel TT lam lamT sp) (hPr : Peel TT rest restT sp)
    (hdlT : IsDominant lamT) (hdsp : IsDominant sp) (hlam : lam = lamT + sp)
    (hrest : rest = restT + sp) (c0 lossT κ M : ℕ) (hM : ordMax r sp ≤ M) (e : Edge W Qq (m + 1))
    (he : IsEdge p n' r e) (Θ : ↥((Pol (KK O) (ι := Fin n') (m + 1) d).restrictScalars O) ≃ₗ[O] ↥(Vsp Kf (flW (m := m) d)))
    (hT : RhoAtG p n' ι σ w r TT d restT lamT c0 lossT κ e Θ) :
    RhoAtG p n' ι σ w r TT d rest lam c0 (lossT + M) κ e Θ := by
  classical
  obtain ⟨IxT, ρT, L1, L2, L3, Op, Nd⟩ := hT
  have hw := w_ne_zero h
  have hp0 : (p : Kf) ≠ 0 := by rw [Formalism.L2.G.Model.p_eq h]; exact pow_ne_zero _ hw
  set cw : Kf := algebraMap O Kf w with hcw
  set cp : Kf := (p : Kf) ^ Ar r sp with hcp
  have bp := fun e' (he' : IsEdge p n' r e') => Formalism.L2.G.Model.bePerfect p n' W Qq O Kf ι σ j w h m r sp hdsp e' he'
  have G1 : ∀ G ∈ Re' p ι σ w r sp e, ∀ Q ∈ Re p ι σ w r sp e,
      ∃ a : O, be p r sp Q G = cw ^ (0 : ℤ) * algebraMap O Kf a := by
    intro G hG Q hQ
    obtain ⟨a, ha⟩ := ((bp e he).1 G).1 hG Q hQ
    exact ⟨a, by rw [zpow_zero, one_mul, ha]⟩
  have G0 : ∀ G ∈ Re' p ι σ w r sp e, ∃ G' ∈ dualLat O Kf (HL (O := O) ι σ sp e.tgt), cw ^ (-(M : ℤ)) • G' = G :=
    fun G hG => mem_scale.1 (Re'_le_scale h m r sp hdsp e he M hM hG)
  have G2 : ∀ G ∈ Re' p ι σ w r sp e, ∀ e' : Edge W Qq (m + 1), IsEdge p n' r e' → e'.tgt = e.tgt →
      ∀ Q ∈ Re p ι σ w r sp e', ∃ a : O, be p r sp Q G = cw ^ (-(M : ℤ)) * algebraMap O Kf a := by
    intro G hG e' he' htg Q hQ
    obtain ⟨G', hG', rfl⟩ := G0 G hG
    have h1 : G' ∈ Re' p ι σ w r sp e' :=
      (Formalism.L2.G.Model.dualInclusionLattices p n' W Qq O Kf ι σ j w h m r sp hdsp e' he').2 (by rw [htg]; exact hG')
    obtain ⟨a, ha⟩ := ((bp e' he').1 G').1 h1 Q hQ
    exact ⟨a, by rw [be_smulK_right, ha]⟩
  have G3 : ∀ G ∈ Re' p ι σ w r sp e, ∀ Q ∈ HL (O := O) ι σ sp e.tgt,
      ∃ a : O, G Q = cw ^ (-(M : ℤ)) * algebraMap O Kf a := by
    intro G hG Q hQ
    obtain ⟨G', hG', rfl⟩ := G0 G hG
    obtain ⟨a, ha⟩ := hG' Q hQ
    exact ⟨a, by rw [LinearMap.smul_apply, smul_eq_mul, ha]⟩
  have hmem0 : ∀ G ∈ Re' p ι σ w r sp e, ∀ u ∈ Re p ι σ w r lam e, peelMap hPl cp G u ∈ Re p ι σ w r lamT e := by
    intro G hG u hu
    obtain ⟨z, hz, hze⟩ := mem_scale.1 (peel_Re h hPl hlam hdlT hdsp r e he 0 G (G1 G hG) u hu)
    rw [zpow_zero, one_smul] at hze
    rw [← hze]
    exact hz
  refine ⟨IxT × {G : Module.Dual Kf (Vsp Kf sp) // G ∈ Re' p ι σ w r sp e},
    fun x => (ρT x.1).comp (peelMap hPl cp x.2.1), ?_, ?_, ?_, ?_, ?_⟩
  · intro β u hu
    exact L1 β.1 _ (hmem0 _ β.2.2 u hu)
  · intro β e' he' htg u hu
    obtain ⟨z, hz, hze⟩ := mem_scale.1 (peel_Re h hPl hlam hdlT hdsp r e' he' (-(M : ℤ)) β.2.1
      (G2 _ β.2.2 e' he' htg) u hu)
    obtain ⟨z2, hz2, hz2e⟩ := mem_scale.1 (L2 β.1 e' he' htg z hz)
    refine mem_scale.2 ⟨z2, hz2, ?_⟩
    rw [LinearMap.comp_apply, ← hze, map_smul, ← hz2e, smul_smul, ← zpow_add₀ hw]
    congr 2
    push_cast
    ring
  · intro β u hu
    obtain ⟨gs, hgs, _, _, h3⟩ := Formalism.L2.G.Model.edgeLat h m r e he
    have hL : ∀ s : Fin n', ∃ g : Matrix (Fin (m + 1)) (Fin (m + 1)) Kf, IsUnit g.det ∧
        extO O ι σ s.val e.tgt = colSpan O g := fun s =>
      ⟨_, by
        rw [Matrix.det_mul, Matrix.det_mul]
        exact ((hgs _).mul (lb_D_det _ _ _ hw)).mul (lb_D_det _ _ _ hw), h3 s.val⟩
    obtain ⟨z, hz, hze⟩ := mem_scale.1 (peel_HL hPl hdlT hdsp e.tgt hL cp (cw ^ (-(M : ℤ))) β.2.1 (G3 _ β.2.2) u hu)
    obtain ⟨z2, hz2, hz2e⟩ := mem_scale.1 (L3 β.1 z hz)
    refine mem_scale.2 ⟨z2, hz2, ?_⟩
    rw [LinearMap.comp_apply, ← hze, map_smul, ← hz2e, smul_smul]
    congr 1
    have hAr : Ar r rest = Ar r restT + Ar r sp := by rw [hrest]; exact Ar_add r _ _
    rw [hAr, zpow_add₀ hp0, hcp]
    have : cw ^ (-((lossT + M : ℕ) : ℤ)) = cw ^ (-(M : ℤ)) * cw ^ (-(lossT : ℤ)) := by
      rw [← zpow_add₀ hw]
      congr 1
      push_cast
      ring
    rw [this]
    ring
  · intro β F s u hu
    refine Op β.1 F (peelMap hPr cp β.2.1 s) (peelMap hPl cp β.2.1 u) ?_
    rw [peelMap_coe, peelMap_coe, hu, slice_mul_left TT _ _ _ (V_flat_supported TT d hd0 _ (Θ F).2), mul_smul_comm]
  · intro u hu hall
    have hz : ∀ G (hG : G ∈ Re' p ι σ w r sp e), peelMap hPl cp G u ∈ scale (cw ^ (1 : ℤ)) (Re p ι σ w r lamT e) :=
      fun G hG => Nd _ (hmem0 G hG u hu) (fun βT => hall (βT, ⟨G, hG⟩))
    obtain ⟨I, hI, x, π, _, _, _, _, _, c6, c7⟩ := edge_lattice_adapted_basis h m r sp hdsp e he
    cases nonempty_fintype I
    let spv : I → Vsp Kf sp := fun i => (cw ^ (-order r sp (π i))) • x i
    let Gv : I → Module.Dual Kf (Vsp Kf sp) := fun i => (cw ^ (-order r sp (π i)) * (p : Kf) ^ (-π i)) • x.coord i
    have hspv : ∀ i, spv i ∈ Re p ι σ w r sp e := fun i => by rw [← c6]; exact Submodule.subset_span ⟨i, rfl⟩
    have hGv : ∀ i, Gv i ∈ Re' p ι σ w r sp e := fun i => by rw [← c7]; exact Submodule.subset_span ⟨i, rfl⟩
    have hexp : ∀ y ∈ Vsp Kf lam, y = ∑ i, (cp • slice TT (extD (Gv i)) y) * ((spv i : Vsp Kf sp) : MvPolynomial (Fin n' × (Fin (m + 1) × Fin (m + 1))) Kf) := by
      intro y hy
      unfold Vsp tensorLat at hy
      induction hy using Submodule.span_induction with
      | mem y hy =>
        obtain ⟨F, hF, rfl⟩ := hy
        have hQ : ∏ s, blockEmb Kf s (if s ∈ TT then 1 else F s) ∈ Vsp Kf sp := by
          refine Submodule.subset_span ⟨_, fun s => ?_, rfl⟩
          by_cases hs : s ∈ TT
          · simp only [if_pos hs, lamAt_zero (hPl.top s hs).2, if_pos (anti_zero m), nuOf_zero]
            exact one_mem_dualWeyl
          · have := hF s
            simp only [if_neg hs, lamAt_congr (hPl.off s hs).2]
            exact this
        have hPs : ∏ s, blockEmb Kf s (if s ∈ TT then F s else 1) ∈
            supported Kf {v : Fin n' × (Fin (m + 1) × Fin (m + 1)) | v.1 ∈ TT} := by
          refine Subalgebra.prod_mem _ fun s _ => ?_
          by_cases hs : s ∈ TT
          · rw [if_pos hs]; exact blockEmb_supported s _ (fun s => s ∈ TT) hs
          · rw [if_neg hs, map_one]; exact Subalgebra.one_mem _
        have hQs : ∏ s, blockEmb Kf s (if s ∈ TT then 1 else F s) ∈
            supported Kf {v : Fin n' × (Fin (m + 1) × Fin (m + 1)) | v.1 ∉ TT} := by
          refine Subalgebra.prod_mem _ fun s _ => ?_
          by_cases hs : s ∈ TT
          · rw [if_pos hs, map_one]; exact Subalgebra.one_mem _
          · rw [if_neg hs]; exact blockEmb_supported s _ (fun s => s ∉ TT) hs
        have e1 : (⟨_, hQ⟩ : Vsp Kf sp) = ∑ i, (cp * Gv i ⟨_, hQ⟩) • spv i := by
          conv_lhs => rw [← x.sum_repr ⟨_, hQ⟩]
          refine Finset.sum_congr rfl fun i _ => ?_
          simp only [Gv, spv, LinearMap.smul_apply, Module.Basis.coord_apply, smul_eq_mul, smul_smul]
          congr 1
          have e3 : cp * (cw ^ (-order r sp (π i)) * (p : Kf) ^ (-π i)) * cw ^ (-order r sp (π i)) = 1 := by
            rw [hcp, p_zpow h, p_zpow h, ← zpow_add₀ hw, ← zpow_add₀ hw, ← zpow_add₀ hw]
            unfold order
            have : 2 * Ar r sp + (-(Ar r sp - π i) + 2 * -π i) + -(Ar r sp - π i) = 0 := by ring
            rw [this, zpow_zero]
          calc (x.repr ⟨_, hQ⟩) i = (cp * (cw ^ (-order r sp (π i)) * (p : Kf) ^ (-π i)) * cw ^ (-order r sp (π i))) *
                (x.repr ⟨_, hQ⟩) i := by rw [e3, one_mul]
            _ = _ := by ring
        have e2 := congrArg (fun t : Vsp Kf sp => (t : MvPolynomial (Fin n' × (Fin (m + 1) × Fin (m + 1))) Kf)) e1
        simp only [Submodule.coe_sum, Submodule.coe_smul] at e2
        rw [prod_split TT F]
        have e4 : ∀ i, slice TT (extD (Gv i)) ((∏ s, blockEmb Kf s (if s ∈ TT then F s else 1)) *
            ∏ s, blockEmb Kf s (if s ∈ TT then 1 else F s)) =
            Gv i ⟨_, hQ⟩ • ∏ s, blockEmb Kf s (if s ∈ TT then F s else 1) := by
          intro i
          rw [slice_mul TT _ _ _ hPs hQs]
          congr 1
          exact extD_spec (Gv i) ⟨_, hQ⟩
        simp only [e4]
        conv_lhs => rw [e2, Finset.mul_sum]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [smul_smul, smul_mul_assoc, mul_smul_comm]
      | zero => simp
      | add a b _ _ ha hb =>
        simp only [map_add (f := _), smul_add, add_mul, Finset.sum_add_distrib]
        rw [← ha, ← hb]
      | smul t a _ ha =>
        conv_lhs => rw [ha]
        rw [Finset.smul_sum]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [map_smul, smul_comm cp t]
        simp only [smul_mul_assoc]
    choose z hzR hze using fun i => mem_scale.1 (hz (Gv i) (hGv i))
    refine mem_scale.2 ⟨∑ i, mulV hlam hdlT hdsp (z i) (spv i), Submodule.sum_mem _ fun i _ =>
      edge_lattice_mul_of_weight_sum D (Formalism.L2.G.Model.products_sections_integral D) p ι σ w hw r hlam hdlT hdsp e (mulV_coe hlam hdlT hdsp _ _) (hzR i)
        (hspv i), ?_⟩
    apply Subtype.ext
    rw [hexp u u.2]
    simp only [Submodule.coe_smul, Submodule.coe_sum, mulV_coe, Finset.smul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    have h5 := congrArg (fun t : Vsp Kf lamT => (t : MvPolynomial (Fin n' × (Fin (m + 1) × Fin (m + 1))) Kf)) (hze i)
    simp only [Submodule.coe_smul, peelMap_coe] at h5
    rw [← h5, smul_mul_assoc]

end Formalism.MainNotions.TestSideCounting
end
end

