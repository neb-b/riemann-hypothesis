module

public import Formalism.SharpRestriction.GrowthBounds.ScaleEdges.Bundle0008
public import Formalism.SharpRestriction.GrowthBounds.ScaleEdges.ExistsPolFamilyOfMemGenOfVsDegLe

@[expose] public section

-- bundled from Formalism.SharpRestriction.GrowthBounds.ScaleEdges.RestCloudOfX
section
noncomputable section

namespace Formalism.MainNotions.Pf14

open Formalism.MainNotions.G Formalism.GradedWeylDivisibility Formalism.MainNotions.SourceCleaning MvPolynomial

def CloudAtX (p n' : ℕ) [Fact p.Prime] [NeZero n'] {W Qq O Kf : Type} [CommRing W] [Field Qq]
    [Algebra W Qq] [CommRing O] [IsDomain O] [Field Kf] [Algebra O Kf] [Algebra (WF p n') O]
    (ι : Qq →+* Kf) (σ : Qq ≃+* Qq) (w : O) (φ : WF p n' ≃+* W) {m r : ℕ}
    (TT : Finset (Fin n')) (lam0 : Fin n' → Fin (m + 1) → ℤ) (cStar : ℕ) (bS bT bD : ℝ)
    (e : Edge W Qq (m + 1)) (h : Matrix (Fin (m + 1)) (Fin (m + 1)) Qq) {nb : ℕ}
    (FsB : Fin nb → ↥((Pol (KK O) (ι := Fin n') (m + 1) (dT TT lam0)).restrictScalars O)) : Prop :=
  ∃ Θ : ↥((Pol (KK O) (ι := Fin n') (m + 1) (dT TT lam0)).restrictScalars O) ≃ₗ[O]
      ↥(Vsp Kf (flW (m := m) (dT TT lam0))),
    IsFlatIdent ι σ w φ r (dT TT lam0) (flW (dT TT lam0)) (vecE n') h Θ ∧
    ∃ (n2 oS tT D1 : ℕ) (sh : Fin n2 → Vsp Kf (restW TT lam0)),
      (oS : ℝ) ≤ bS ∧ (tT : ℝ) ≤ bT ∧ (D1 : ℝ) ≤ bD ∧
      (∀ i, sh i ∈ Re p ι σ w r (restW TT lam0) e ∧
        sh i ∈ scale (algebraMap O Kf w ^ (-(oS : ℤ))) (HL (O := O) ι σ (restW TT lam0) e.src)) ∧
      ((n2 : ℕ) : ℚ) = remainingWeightVectorCount TT lam0 ∧
      ∀ S : Fin nb × Fin n2 → Vsp Kf lam0,
        (∀ b i, ((S (b, i) : Vsp Kf lam0) : MvPolynomial (Fin n' × (Fin (m + 1) × Fin (m + 1))) Kf) =
          ((Θ (FsB b) : Vsp Kf (flW (m := m) (dT TT lam0))) : MvPolynomial (Fin n' × (Fin (m + 1) × Fin (m + 1))) Kf) *
            ((sh i : Vsp Kf (restW TT lam0)) : MvPolynomial (Fin n' × (Fin (m + 1) × Fin (m + 1))) Kf)) →
        ∀ c : Fin nb × Fin n2 → O, (∃ x, IsUnit (c x)) →
          ∃ G : Module.Dual Kf (Vsp Kf lam0),
            G ∈ scale (algebraMap O Kf w ^ (-(tT : ℤ))) (dualLat O Kf (HL (O := O) ι σ lam0 e.tgt)) ∧
            G ∈ Re' p ι σ w r lam0 e ∧
            (∀ e' : Edge W Qq (m + 1), IsEdge p n' r e' → e'.tgt = e.tgt → e' ≠ e →
              G ∈ scale (algebraMap O Kf w ^ (cStar : ℤ)) (Re' p ι σ w r lam0 e')) ∧
            ValLe (p : O) D1 (be p r lam0 (∑ x, c x • S x) G)

def CloudStepX (C Ct0 CD1 CLa : ℝ) : Prop :=
  ∀ (p : ℕ) (W Qq O Kf : Type) [CommRing W] [IsDomain W] [IsDiscreteValuationRing W] [Field Qq] [Algebra W Qq]
    [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field Kf] [Algebra O Kf]
    (ι : Qq →+* Kf) (σ : Qq ≃+* Qq) (j : W →+* O) (w : O)
    (n' m r : ℕ) [Fact p.Prime] [NeZero n'] (TT : Finset (Fin n')) (L₁ L₂ : ℕ) (de h x : ℝ)
    (lam0 : Fin n' → Fin (m + 1) → ℤ) (aT bT : Fin n' → ℤ) (a Y : ℝ) (cpp c0 Dp cStar : ℕ),
    UnramifiedQuadraticSetting p n' W Qq O Kf ι σ j w →
    Hyps C p n' m r TT L₁ L₂ de h x lam0 aT bT a Y cpp c0 Dp cStar →
    ∀ φ : WF p n' ≃+* W, IsWittIdent σ φ →
    ∀ (K : ℕ) [NeZero r] [NeZero K] (hk : m + 1 = r + K) (hrk : r ≤ m + 1),
    ∀ F : Frames n' r, FramesOK TT L₁ L₂ (orbitWindowCount r de h x) (goodG' r de h x) F →
    ∀ E' : Fin n' → ℕ,
      (∀ t ∈ F.TT, E' t ≤ E0 p r (r + K) (orbitWindowCount r de h x) (goodG' r de h x) (cPrime n' r TT.card c0 cpp cStar) ∧
        E' t ≤ flatDeg lam0 t) →
    ∀ (nb : ℕ) (B : Fin nb → RRing O n' (r + K)),
      (∀ i, B i ∈ Gen O p K F
        (symbolSpaces CLa p n' O r K F (flatDeg lam0) L₁ (min (orbitWindowCount r de h x) (2 * TT.card))
          (mStar p F (r + K) (orbitWindowCount r de h x) (p ^ goodG' r de h x) (cPrime n' r TT.card c0 cpp cStar)) a Y)
        (G2d F (flatDeg lam0) E')) →
      LinearIndependent O B → (∃ T : Submodule O (RRing O n' (r + K)), IsCompl (Submodule.span O (Set.range B)) T) →
    ∀ e : Edge W Qq (m + 1), IsEdge p n' r e → e.tgt = colSpan W (1 : Matrix (Fin (m + 1)) (Fin (m + 1)) Qq) →
    ∀ (hm : Matrix (Fin (m + 1)) (Fin (m + 1)) Qq) (g : Matrix (Fin (m + 1)) (Fin (m + 1)) (WF p n')),
      IsUnit hm.det → IsGLW g → IsEdgeBasis p r e (hm * ((matQ φ g)⁻¹).transpose) →
    letI : Algebra (WF p n') O := algOfIdent j φ
    ∀ FsB : Fin nb → ↥((Pol (KK O) (ι := Fin n') (m + 1) (dT TT lam0)).restrictScalars O),
      (∀ b, subst p n' O w n' r g (FsB b : MvPolynomial (TV n' (m + 1)) (KK O)) =
        symB p n' O w hk hrk F g (cPrime n' r TT.card c0 cpp cStar) (p ^ goodG' r de h x) (B b)) →
      CloudAtX p n' ι σ w φ (r := r) TT lam0 cStar (om r TT.card n' c0 cpp)
        (t0 C Ct0 p TT.card (orbitWindowCount r de h x) L₁ (goodG' r de h x) (m + 1) a + (TT.card : ℝ) * c0 +
          om r TT.card n' c0 cpp)
        (CD1 * (TT.card : ℝ) * ((m + 1 : ℕ) : ℝ) ^ 2 * Real.logb p a) e hm FsB

def RestCloudX (D : Formalism.BasicNotions.D7) (CLa Ck Crk Cdeg CLa' CD Csz CH CE C6 C18 : ℝ) : Prop :=
  tableLineDegreeFive.admitted D CLa Ck Crk Cdeg → SourceCleaning.aux₃ D CLa' CD Csz → PlaneGramData.aux₃ D CH CE C6 C18 →
    ∃ Ct0 CD1 C₁ : ℝ, 0 < Ct0 ∧ 0 < CD1 ∧ 0 < C₁ ∧ ∀ C : ℝ, C₁ ≤ C → CloudStepX C Ct0 CD1 CLa

theorem restCloud_of_X (D : Formalism.BasicNotions.D7) (CLa Ck Crk Cdeg CLa' CD Csz CH CE C6 C18 : ℝ)
    (hX : RestCloudX D CLa Ck Crk Cdeg CLa' CD Csz CH CE C6 C18) :
    RestCloud D CLa Ck Crk Cdeg CLa' CD Csz CH CE C6 C18 := by
  intro hA h14a h14b
  obtain ⟨Ct0, CD1, C₁, h0, h1, h2, hS⟩ := hX hA h14a h14b
  have h35 : tableLineDegreeFive.FewBadOrbits D := hA.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  refine ⟨Ct0, CD1, max C₁ 2, h0, h1, lt_of_lt_of_le h2 (le_max_left _ _), ?_⟩
  intro C hC p W Qq O Kf _ _ _ _ _ _ _ _ _ _ ι σ j w n' m r _ _ TT L₁ L₂ de h x lam0 aT bT a Y cpp c0 Dp cStar hSet H φ hφ K
    _ _ hk hrk F hF E' hE' nb B hB hli hc e he htgt hm g hhm hg hbasis FsB hFsB
  obtain ⟨Θ, hΘ, n2, oS, tT, D1, sh, a1, a2, a3, a4, a5, a6⟩ :=
    hS C (le_trans (le_max_left _ _) hC) p W Qq O Kf ι σ j w n' m r TT L₁ L₂ de h x lam0 aT bT a Y cpp c0 Dp cStar hSet H
      φ hφ K hk hrk F hF E' hE' nb B hB hli hc e he htgt hm g hhm hg hbasis FsB hFsB
  exact ⟨Θ, hΘ, n2, oS, tT, D1, sh, a1, a2, a3, a4,
    count_of_exact D h35 (le_trans (le_max_right _ _) hC) H Kf n2 a5, a6⟩

end Formalism.MainNotions.Pf14
end
end

-- bundled from Formalism.SharpRestriction.GrowthBounds.ScaleEdges.SymbolRealisableIffGeneralRank
section
noncomputable section

open MvPolynomial Finset Classical

namespace Formalism.MainNotions.Pf14

open Formalism.MainNotions.G Formalism.MainNotions.SourceCleaning Formalism.MainNotions.G.WittFrameLocaliserOrders Formalism.MainNotions.G.symbolGeneratorData

theorem oHyp_of {p n' : ℕ} [Fact p.Prime] {W Qq O Kf : Type} [CommRing W] [IsDomain W] [IsDiscreteValuationRing W]
    [Field Qq] [Algebra W Qq] [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field Kf] [Algebra O Kf]
    {ι : Qq →+* Kf} {σ : Qq ≃+* Qq} {j : W →+* O} {w : O} (h : UnramifiedQuadraticSetting p n' W Qq O Kf ι σ j w)
    (φ : WF p n' ≃+* W) :
    letI : Algebra (WF p n') O := algOfIdent j φ
    OHyp p n' O (dvrOfStd h) := by
  let _ : Algebra (WF p n') O := algOfIdent j φ
  refine ⟨dvrOfStd_sq h, ?_, ?_⟩
  · show (j.comp (φ : WF p n' →+* W)).Finite
    exact RingHom.Finite.comp h.1.finite (RingHom.Finite.of_surjective _ φ.surjective)
  · show Function.Injective (j.comp (φ : WF p n' →+* W))
    have hj : Function.Injective j := by
      intro a b hab
      have h1 : algebraMap O Kf (j a) = algebraMap O Kf (j b) := congrArg _ hab
      rw [← h.1.ι_comp, ← h.1.ι_comp] at h1
      have := h.1.frac_alt
      exact IsFractionRing.injective W Qq (ι.injective h1)
    exact hj.comp φ.injective

def castVK {n' k r K : ℕ} (hk : k = r + K) : Fin n' × Fin (r + K) → Fin n' × Fin k :=
  fun v => (v.1, Fin.cast hk.symm v.2)

section Lift

variable (p n' : ℕ) [Fact p.Prime] [NeZero n'] (O : Type) [CommRing O] [IsDomain O] [Algebra (WF p n') O] (w : O)

def SymbolRealisableGeneralRank {k r K : ℕ} [NeZero r] [NeZero K] (hk : k = r + K) (hrk : r ≤ k) (F : Frames n' r)
    (XXs : ℤ → Submodule O (SegRing O r K)) (deg dTop : Fin n' → ℕ) (c' Q E₀ : ℕ) : Prop :=
  ∃ E' : Fin n' → ℕ, (∀ t ∈ F.TT, E' t ≤ E₀ ∧ E' t ≤ deg t) ∧
    ∀ g : Matrix (Fin k) (Fin k) (WF p n'), IsGLW g →
    ∀ P ∈ Gen O p K F XXs (G2d F deg E'), ∀ T : ℕ, (∀ mm ∈ P.support, vsDeg mm ≤ T) →
      ∃ Fs : ℕ → ↥((Pol (KK O) (ι := Fin n') k dTop).restrictScalars O),
        (∀ o, HasMultideg (subst p n' O w n' r g (Fs o : MvPolynomial (TV n' k) (KK O))) dTop ∧
          InWj w (subst p n' O w n' r g (Fs o : MvPolynomial (TV n' k) (KK O))) 0 ∧
          Realisable p n' w n' r g c' o (subst p n' O w n' r g (Fs o : MvPolynomial (TV n' k) (KK O)))) ∧
        ∑ o ∈ Finset.range (T + 1), subst p n' O w n' r g (Fs o : MvPolynomial (TV n' k) (KK O)) =
          MvPolynomial.map (algebraMap O (KK O)) (rename (castVK hk) P) *
            subst p n' O w n' r g (SPtrue p n' O F hrk g c' Q)

theorem symbol_realisable_iff_general_rank {m r K : ℕ} [NeZero r] [NeZero K] (hk : m + 1 = r + K) (hrk : r ≤ m + 1) (F : Frames n' r)
    (XXs : ℤ → Submodule O (SegRing O r K)) (deg dTop : Fin n' → ℕ) (c' Q E₀ : ℕ) :
    SymbolRealisableAt p n' O w hk hrk F XXs deg dTop c' Q E₀ ↔ SymbolRealisableGeneralRank p n' O w hk hrk F XXs deg dTop c' Q E₀ := Iff.rfl

end Lift

theorem symbol_realisable_general_rank (D : Formalism.BasicNotions.D7) (hW1 : GeneratorSpanInclusion) (hW2 : GeneratorImageIsSymbol) (hMon : RestMon) {p n' : ℕ} [Fact p.Prime] [NeZero n']
    (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Algebra (WF p n') O] (S : UniformizedDVR p O)
    (hO : OHyp p n' O S) {k r K : ℕ} [NeZero r] [NeZero K] (hk : k = r + K) (hH : CommonHypotheses p n' r k) (F : Frames n' r)
    (L₁ N₁ G' : ℕ) (hV : F.Valid L₁ N₁) (hT : TwistBound p F (p ^ G')) (hG : ∀ j : ℤ, zF F j - F.fr (j - 1) 0 ≤ G')
    (hK : N₁ + 2 * r ≤ K) (mg : ℤ → ℤ → ℤ) (th o : ℤ → ℤ → ℝ) (hmg : ∀ j x, 0 ≤ mg j x) (deg dTop : Fin n' → ℕ)
    (c' E₀ : ℕ) (hdT : ∀ s, dTop s = if s ∈ F.TT then deg s else 0)
    (hE1 : ∀ t ∈ F.TT, eSP p n' F k c' (p ^ G') t ≤ E₀ ∧ eSP p n' F k c' (p ^ G') t ≤ deg t)
    (hE0 : ∀ t, t ∉ F.TT → eSP p n' F k c' (p ^ G') t = 0) :
    SymbolRealisableGeneralRank p n' O S.w hk hH.2.2.1 F (fun j => XX' O r K F j (mg j) (th j) (o j)) deg dTop c' (p ^ G') E₀ := by
  subst hk
  refine ⟨eSP p n' F (r + K) c' (p ^ G'), hE1, ?_⟩
  intro g hg P hP T hT'
  let X : Ctx p n' r K O :=
    { S := S, hO := hO, hH := hH, Fr := F, L₁ := L₁, N₁ := N₁, G' := G', hV := hV, hT := hT, hG := hG, hK := hK,
      g := g, hg := hg }
  have hd : ∀ s, G2d F deg (eSP p n' F (r + K) c' (p ^ G')) s + eSP p n' F (r + K) c' (p ^ G') s = dTop s := by
    intro s
    unfold G2d
    rw [hdT s]
    by_cases hs : s ∈ F.TT
    · rw [ite_eq_left hs, ite_eq_left hs]
      have := (hE1 s hs).2
      omega
    · rw [ite_eq_right hs, ite_eq_right hs, hE0 s hs]
  have hd0 : ∀ s, s ∉ F.TT → G2d F deg (eSP p n' F (r + K) c' (p ^ G')) s = 0 := by
    intro s hs
    unfold G2d
    rw [ite_eq_right hs]
  have hren : rename (castVK (n' := n') (rfl : r + K = r + K)) P = P := by
    have : (castVK (n' := n') (rfl : r + K = r + K)) = id := by
      funext v
      rfl
    rw [this, rename_id_apply]
  rw [hren]
  exact exists_pol_family_of_mem_gen_of_vsDeg_le X D hW1 hW2 hMon c' mg th o hmg _ _ dTop hd hd0 (SPtrue_hom p n' O F hH.2.2.1 g c' (p ^ G')) P hP T hT'

theorem sources_realisable_holds (D : Formalism.BasicNotions.D7) (CLa Ck Crk Cdeg CLa' CD Csz : ℝ) : SourcesRealisable D CLa Ck Crk Cdeg CLa' CD Csz := by
  intro hA _
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, a15, a16, a17, a18, _, a20, _⟩ := hA
  have hW1 : GeneratorSpanInclusion := generator_pair_conditions_of_admitted D a15 a16
  have hW2 : GeneratorImageIsSymbol := generator_path_homogeneous_holds D a17 a18 a20
  have hMon : RestMon := restMon D
  refine ⟨30, by norm_num, ?_⟩
  intro C hC p W Qq O Kf _ _ _ _ _ _ _ _ _ _ ι σ j w n' m r _ _ TT L₁ L₂ de h x lam0 aT bT a Y cpp c0 Dp cStar hSet H φ _ K
    _ _ hk hrk F hF
  let _ : Algebra (WF p n') O := algOfIdent j φ
  rw [symbol_realisable_iff_general_rank]
  have hB := hyps_basic (C := C) (by linarith) H
  have hTT := hF.1
  have hGn : goodG' r de h x ≤ n' := by have := H.2.2.1.2.2.2; omega
  have hkr : orbitWindowCount r de h x + 2 * r ≤ (m + 1) - r := H.2.2.2.2.2.2.2.1
  have hH : CommonHypotheses p n' r (m + 1) := ⟨H.1, H.2.1, hrk, hSet.1.two_le, hSet.1.even⟩
  have eE : E0 p r (r + K) (orbitWindowCount r de h x) (goodG' r de h x) (cPrime n' r TT.card c0 cpp cStar) =
      E0 p r (m + 1) (orbitWindowCount r de h x) (goodG' r de h x) (cPrime n' r TT.card c0 cpp cStar) := by rw [hk]
  rw [eE]
  show SymbolRealisableGeneralRank p n' O (dvrOfStd hSet).w hk hH.2.2.1 F (fun j => XX' O r K F j _ _ _) _ _ _ _ _
  refine symbol_realisable_general_rank D hW1 hW2 hMon O (dvrOfStd hSet) (oHyp_of hSet φ) hk hH F L₁ (orbitWindowCount r de h x) (goodG' r de h x)
    hF.2.1 (twist_of hF (by have := H.2.1; omega) hGn p (by have := H.1; omega))
    (fun j => (hF.2.2.1 j).le) (by omega) _ _ _ ?_ (flatDeg lam0) (dT TT lam0) (cPrime n' r TT.card c0 cpp cStar) _
    ?_ ?_ ?_
  · intro j x'
    positivity
  · intro s
    unfold dT
    rw [hTT]
  · intro t ht
    exact spdeg hC H hF t ht
  · intro t ht
    exact eSP_off hF _ _ _ t ht

end Formalism.MainNotions.Pf14
end
end

