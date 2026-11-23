module

public import Mathlib
public import Formalism.SharpRestriction.InertJacobiLevels.AsmIface
public import Formalism.LocalToGlobal.GlobalTheory.IsResidueClassZero
public import Formalism.SharpRestriction.GrowthBounds.SmallOrderPrimes
public import Formalism.LocalRingCardinality.RankBoundMonotoneInDimension
public import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.Bundle0002
public import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.Bundle0003
public import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.ThinScalesIffHostBound
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.MaxVSpanSingleton
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0071
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0069
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0079
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0084
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0083
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0074
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0078
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0068

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.SamePointOfSameScale
section
open Formalism.BasicNotions Formalism.BasicNotions.LevelStarExponents Formalism.MainNotions Formalism.MainNotions.Inhab Formalism.L2.GlobalTheoryTheory GlobalTheory.EX NumberField

namespace GlobalTheory.EX.TieSame

theorem bsH_val_congr {e e' : Formalism.HC.Frame} (he : e = e') (h t : e.A) (h' t' : e'.A)
    (hh : h.val = h'.val) (ht : t.val = t'.val) : (Arith.bsH h t).val = (Arith.bsH h' t').val := by
  subst he
  have h1 := Formalism.HC.Frame.A.val_injective _ hh
  have h2 := Formalism.HC.Frame.A.val_injective _ ht
  rw [h1, h2]

theorem mem_iff_val_mem {e : Formalism.HC.Frame} (T : Finset e.A) (t : e.A) :
    t ∈ T ↔ t.val ∈ T.image Formalism.HC.Frame.A.val := by
  constructor
  · intro h; exact Finset.mem_image_of_mem _ h
  · intro h
    obtain ⟨s, hs, hst⟩ := Finset.mem_image.1 h
    rwa [← Formalism.HC.Frame.A.val_injective _ hst]

theorem kapISet_congr {D D' : D7} (L : SizeData₂ D) (L' : SizeData₂ D') (hR : D.R = D'.R) (hs : L.sc = L'.sc) (hS : L.Sc = L'.Sc)
    (K : G.Consts) (p n' : ℕ) (TT : Finset (Fin n')) (a b : Fin n' → ℤ) :
    G.kapISet L K p n' TT a b = G.kapISet L' K p n' TT a b := by
  have hk : D.R.k = D'.R.k := by rw [hR]
  have hc : G.cG L = G.cG L' := by unfold G.cG; rw [hS]
  have hD : G.DIf K L p n' = G.DIf K L' p n' := by unfold G.DIf; rw [hs, hk]
  have h6 : G.c6f K L p n' = G.c6f K L' p n' := by unfold G.c6f; rw [hD, hs, hk, hc]
  have ht : G.tIf K L p n' TT a b = G.tIf K L' p n' TT a b := by unfold G.tIf; rw [h6, hs, hk, hc]
  unfold G.kapISet
  rw [hc, hD, ht, hk]

theorem nonempty_place (D : D7) : Nonempty D.what₂.places.Pl := by
  haveI := D.nfLL
  obtain ⟨P, hP⟩ := Ideal.exists_maximal (𝓞 D.what₂.LL)
  exact ⟨D.plEq.symm ⟨P, hP.isPrime, Ring.ne_bot_of_isMaximal_of_not_isField hP (RingOfIntegers.not_isField _)⟩⟩

theorem off_lift {C : FC} {cD ch : ℝ} (p : Pt C) (hv : Val C cD ch p.L) (j : ℕ) (hj : j ∈ SizeData₂.lifts p.D) (t : G.HH p.D) :
    p.ta.Gx.off j (false, t) =
      (if t ∈ p.D.host.TT then ((⌊p.L.sc.b' / p.L.sc.x⌋ : ℤ) : ℝ) else ((⌈p.L.sc.w'' p.D.R.n⌉ : ℤ) : ℝ)) +
        ((j - 1 : ℕ) : ℝ) * (h0v p.L.sc ch : ℝ) + (h0v p.L.sc ch : ℝ) / 2 := by
  obtain ⟨w⟩ := nonempty_place p.D
  have hP := factPlaces p.D.R.toFrame
  have hmem : p.D.R.tau1 t ∈ p.D.R.Psi := (hP.1 _).2 (Or.inl ⟨t, rfl⟩)
  set τ := p.D.eTau.symm ⟨_, hmem⟩ with hτ
  have hτe : (p.D.eTau τ : p.D.R.GG) = p.D.R.tau1 t := by rw [hτ, Equiv.apply_symm_apply]
  have hf := (p.ta.fills w).1 j hj τ (false, t) (by rw [hτe]; rfl)
  have hjm : j - 1 < p.D.R.m := by
    have := Finset.mem_Icc.1 hj
    omega
  obtain ⟨-, -, ⟨b1, hb, htop, -, hthin⟩, -⟩ := hv.hc
  obtain ⟨hb1, hb2⟩ := hb τ ⟨j - 1, hjm⟩
  unfold wj at hf
  rw [dite_eq_left hjm, hb2, hb1] at hf
  unfold G.fill at hf
  by_cases ht : t ∈ p.D.host.TT
  · have h1 := htop τ ⟨t, ht⟩ hτe
    rw [if_pos ⟨rfl, ht⟩, h1] at hf
    rw [if_pos ht]
    unfold G.bL at hf
    rw [dite_eq_left ht] at hf
    push_cast at hf ⊢
    linarith
  · have h1 := hthin τ (by
      show p.D.host.IsThin (p.D.eTau τ : p.D.R.GG)
      rw [hτe]
      refine ⟨hmem, ?_, ?_⟩
      · intro h
        obtain ⟨s, hs, hst⟩ := Finset.mem_image.1 h
        have : s = t := p.D.R.iota_bijective.1 (congrArg Prod.snd hst)
        exact ht (this ▸ hs)
      · intro h
        obtain ⟨s, -, hst⟩ := Finset.mem_image.1 h
        exact hP.2 _ _ hst.symm)
    rw [if_neg (fun h => ht h.2), h1] at hf
    rw [if_neg ht]
    push_cast at hf ⊢
    linarith

theorem same_of_from : ∀ (C : FC) (cD ch : ℝ) (p p' : Pt C) (R : Ranks) (H : Host R) (a b : R.A → ℤ) (M : ℕ) (c : Fin M → Fin (R.k - 2) → Bool) (u0 u0' : ℕ), p.L.sc = p'.L.sc → Val C cD ch p.L → Val C cD ch p'.L → p.From H a b c u0 → p'.From H a b c u0' → CanonInst p.ta.Gx → CanonInst p'.ta.Gx → p.Same p' := by
  intro C cD ch p p' R H a b M c u0 u0' hs hv hv' hF hF' hC hC'
  have hQS := hF.QS_eq.trans hF'.QS_eq.symm
  have hart := hF.art_eq.trans hF'.art_eq.symm
  have hrd := hF.rd_eq.trans hF'.rd_eq.symm
  obtain ⟨hR, hTT, hT2, hq, hd, hg, hp1, hp2, -, -, hh, hw, -⟩ := hF
  obtain ⟨hR', hTT', hT2', hq', hd', hg', hp1', hp2', -, -, hh', hw', -⟩ := hF'
  have hRR : p.D.R = p'.D.R := hR.trans hR'.symm
  have hT : p.D.host.TT.image Formalism.HC.Frame.A.val = p'.D.host.TT.image Formalism.HC.Frame.A.val := hTT.trans hTT'.symm
  have hSc : p.L.Sc = p'.L.Sc := by rw [p.L.Sc_eq, p'.L.Sc_eq, hv.Del_eq, hv'.Del_eq, hs, hRR]
  have hmem : ∀ (t : G.HH p.D) (t' : G.HH p'.D), t.val = t'.val → (t ∈ p.D.host.TT ↔ t' ∈ p'.D.host.TT) := by
    intro t t' htt
    rw [mem_iff_val_mem p.D.host.TT t, mem_iff_val_mem p'.D.host.TT t', hT, htt]
  have hn : p.D.R.n = p'.D.R.n := by rw [hRR]
  refine ⟨hRR, hT, hT2.trans hT2'.symm, hq.trans hq'.symm, hd.trans hd'.symm, hg.trans hg'.symm, hp1.trans hp1'.symm,
    hp2.trans hp2'.symm, ?_, hSc, fun l => (hh l).trans (hh' l).symm, ?_, ?_, ?_, ?_, ?_, hQS, hart, hrd⟩
  · rw [hv.eta_eq, hv'.eta_eq, hs, hRR]
  · intro h t h' t' e1 e2
    rw [hC.1, hC'.1]
    exact bsH_val_congr (by rw [hRR]) h t h' t' e1 e2
  · intro j t t' htt
    have hm := hmem t t' htt
    have hl : SizeData₂.lifts p.D = SizeData₂.lifts p'.D := by unfold SizeData₂.lifts; rw [hRR]
    by_cases hj : j ∈ SizeData₂.lifts p.D
    · rw [off_lift p hv j hj t, off_lift p' hv' j (hl ▸ hj) t', hs, hn]
      by_cases ht : t ∈ p.D.host.TT
      · rw [if_pos ht, if_pos (hm.1 ht)]
      · rw [if_neg ht, if_neg (fun h => ht (hm.2 h))]
    · rw [hC.2 j hj t, hC'.2 j (hl ▸ hj) t', hs, hn]
      by_cases ht : t ∈ p.D.host.TT
      · rw [if_pos ht, if_pos (hm.1 ht)]
      · rw [if_neg ht, if_neg (fun h => ht (hm.2 h))]
  · funext l n' TT a' b'
    rw [p.xa.ex.kapI_def l n' TT a' b', p'.xa.ex.kapI_def l n' TT a' b', kapISet_congr p.L p'.L hRR hs hSc]
  · funext l
    rw [p.xa.ex.ep_def l, p'.xa.ex.ep_def l, hs, hRR]
  · intro t t' htt
    have hlt : (t : p.D.R.A).val < R.ord := by
      have := Formalism.HC.Frame.A.val_lt (t : p.D.R.A)
      rwa [show R.ord = p.D.R.ord by rw [hR]]
    have hv0 : (R.ofNat (t : p.D.R.A).val).val = (t : p.D.R.A).val :=
      R.toFrame.val_ofNat_of_lt hlt
    obtain ⟨e1, e2⟩ := hw t _ hv0.symm
    obtain ⟨e3, e4⟩ := hw' t' _ (htt.symm.trans hv0.symm)
    exact ⟨e1.trans e3.symm, e2.trans e4.symm⟩

end GlobalTheory.EX.TieSame
end

-- bundled from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.SpanImageLeOf
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV Formalism.L2.Col Formalism.L2.Ker Formalism.MainNotions GlobalTheory.CharVal GlobalTheory.IndefiniteRowSideFullHecke.CharacterValuation

noncomputable section

namespace GlobalTheory.IdealTransport

section General

variable {R R' M M' : Type} [CommRing R] [CommRing R'] [AddCommGroup M] [AddCommGroup M'] [Module R M] [Module R' M']
  (φ : R ≃+* R') (f : M ≃+ M') (h : ∀ r m, f (r • m) = φ r • f m)

include h

theorem span_image_le_of (N : Submodule R M) (N' : Submodule R' M') (S : Set M) (hS : N = Submodule.span R S)
    (hN : ∀ m ∈ S, f m ∈ N') : Submodule.span R' (f '' (N : Set M)) ≤ N' := by
  rw [Submodule.span_le]
  rintro _ ⟨m, hm, rfl⟩
  show f m ∈ N'
  have hm' : m ∈ Submodule.span R S := hS ▸ hm
  clear hm
  induction hm' using Submodule.span_induction with
  | mem x hx => exact hN x hx
  | zero => rw [map_zero]; exact N'.zero_mem
  | add x y _ _ hx hy => rw [map_add (f := _)]; exact N'.add_mem hx hy
  | smul r x _ hx => rw [h]; exact N'.smul_mem _ hx

theorem span_image_span (S : Set M) :
    Submodule.span R' (f '' (Submodule.span R S : Set M)) = Submodule.span R' (f '' S) := by
  apply le_antisymm
  · exact span_image_le_of φ f h _ _ S rfl fun m hm => Submodule.subset_span ⟨m, hm, rfl⟩
  · exact Submodule.span_mono (Set.image_mono Submodule.subset_span)

theorem mem_span_image (N : Submodule R M) (x : M') :
    x ∈ Submodule.span R' (f '' (N : Set M)) ↔ f.symm x ∈ N := by
  have hsm : ∀ (r : R') (y : M'), f.symm (r • y) = φ.symm r • f.symm y := by
    intro r y
    apply f.injective
    rw [h, AddEquiv.apply_symm_apply, RingEquiv.apply_symm_apply, AddEquiv.apply_symm_apply]
  constructor
  · intro hx
    induction hx using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨m, hm, rfl⟩ := hy
      simpa using hm
    | zero => simp
    | add y z _ _ hy hz => rw [map_add (f := _)]; exact N.add_mem hy hz
    | smul r y _ hy => rw [hsm]; exact N.smul_mem _ hy
  · intro hx
    exact Submodule.subset_span ⟨f.symm x, hx, by simp⟩

end General

section Fields

variable {E E' : Type} [Field E] [NumberField E] [Field E'] [NumberField E'] (e : E ≃+* E')

theorem map_smul_int (r : 𝓞 E) (x : E) : e (r • x) = RingOfIntegers.mapRingEquiv e r • e x := by
  rw [Algebra.smul_def, Algebra.smul_def, map_mul]
  rfl

abbrev trI (I : Submodule (𝓞 E) E) : Submodule (𝓞 E') E' := Submodule.span (𝓞 E') (e '' (I : Set E))

abbrev trL {n : ℕ} (N : Submodule (𝓞 E) (Fin n → E)) : Submodule (𝓞 E') (Fin n → E') :=
  Submodule.span (𝓞 E') ((fun (x : Fin n → E) (i : Fin n) => e (x i)) '' (N : Set (Fin n → E)))

theorem mem_trI (I : Submodule (𝓞 E) E) (x : E') : x ∈ trI e I ↔ e.symm x ∈ I := mem_span_image (RingOfIntegers.mapRingEquiv e) e.toAddEquiv (map_smul_int e) I x

theorem trI_span (S : Set E) : trI e (Submodule.span (𝓞 E) S) = Submodule.span (𝓞 E') (e '' S) := span_image_span (RingOfIntegers.mapRingEquiv e) e.toAddEquiv (map_smul_int e) S

theorem mem_trL {n : ℕ} (N : Submodule (𝓞 E) (Fin n → E)) (x : Fin n → E') :
    x ∈ trL e N ↔ (fun i => e.symm (x i)) ∈ N := mem_span_image (RingOfIntegers.mapRingEquiv e) (AddEquiv.piCongrRight fun _ : Fin n => e.toAddEquiv)
    (fun r v => funext fun i => map_smul_int e r (v i)) N x

theorem trI_mul (I J : Submodule (𝓞 E) E) : trI e (I * J) = trI e I * trI e J := by
  rw [Submodule.mul_eq_span_mul_set I J, trI_span, Set.image_mul]
  exact (Submodule.span_mul_span _ _ _).symm

theorem trI_singleton (y : E) : trI e (Submodule.span (𝓞 E) {y}) = Submodule.span (𝓞 E') {e y} := by
  rw [trI_span, Set.image_singleton]

theorem trI_one : trI e 1 = 1 := by
  conv_lhs => rw [Submodule.one_eq_span]
  rw [trI_singleton, map_one, ← Submodule.one_eq_span]

theorem trI_surj (J : Submodule (𝓞 E') E') : ∃ I, trI e I = J := by
  refine ⟨Submodule.span (𝓞 E) (e.symm '' (J : Set E')), ?_⟩
  rw [trI_span, Set.image_image]
  simp only [RingEquiv.apply_symm_apply, Set.image_id']
  exact Submodule.span_eq J

theorem mem_one_iff (x : E') : x ∈ (1 : Submodule (𝓞 E') E') ↔ e.symm x ∈ (1 : Submodule (𝓞 E) E) := by
  rw [← trI_one e, mem_trI]

theorem map_mulVec' {n : ℕ} (A : Matrix (Fin n) (Fin n) E) (v : Fin n → E) :
    (A.map e).mulVec (fun i => e (v i)) = fun i => e (A.mulVec v i) := by
  funext i
  set_option synthInstance.maxHeartbeats 100000 in
    simp [Matrix.mulVec, dotProduct, map_sum]

theorem det_map' {n : ℕ} (A : Matrix (Fin n) (Fin n) E) : (A.map e).det = e A.det := (RingHom.map_det (e : E →+* E') A).symm

theorem carries_iff {n : ℕ} (N : Submodule (𝓞 E) (Fin n → E)) (A : Matrix (Fin n) (Fin n) E) :
    (∀ v ∈ (Submodule.pi Set.univ fun _ : Fin n => (1 : Submodule (𝓞 E') E')), (A.map e).mulVec v ∈ trL e N) ↔
      ∀ v ∈ (Submodule.pi Set.univ fun _ : Fin n => (1 : Submodule (𝓞 E) E)), A.mulVec v ∈ N := by
  constructor
  · intro H v hv
    have hv' : (fun i => e (v i)) ∈ (Submodule.pi Set.univ fun _ : Fin n => (1 : Submodule (𝓞 E') E')) := by
      rw [Submodule.mem_pi] at hv ⊢
      intro i hi
      rw [mem_one_iff e, RingEquiv.symm_apply_apply]
      exact hv i hi
    have hA := H _ hv'
    rw [map_mulVec' e A v, mem_trL] at hA
    simpa using hA
  · intro H v hv
    have hv' : (fun i => e.symm (v i)) ∈ (Submodule.pi Set.univ fun _ : Fin n => (1 : Submodule (𝓞 E) E)) := by
      rw [Submodule.mem_pi] at hv ⊢
      intro i hi
      rw [← mem_one_iff e]
      exact hv i hi
    have hmv : (A.map e).mulVec v = fun i => e (A.mulVec (fun i => e.symm (v i)) i) := by
      have hk := map_mulVec' e A (fun i => e.symm (v i))
      simp only [RingEquiv.apply_symm_apply] at hk
      exact hk
    rw [hmv, mem_trL]
    simpa using H _ hv'

theorem det_set {n : ℕ} (N : Submodule (𝓞 E) (Fin n → E)) :
    {x | ∃ A : Matrix (Fin n) (Fin n) E', (∀ v ∈ (Submodule.pi Set.univ fun _ : Fin n => (1 : Submodule (𝓞 E') E')),
        A.mulVec v ∈ trL e N) ∧ x = A.det} =
      e '' {x | ∃ A : Matrix (Fin n) (Fin n) E, (∀ v ∈ (Submodule.pi Set.univ fun _ : Fin n => (1 : Submodule (𝓞 E) E)),
        A.mulVec v ∈ N) ∧ x = A.det} := by
  ext x
  constructor
  · rintro ⟨A', hA', rfl⟩
    have hmap : (A'.map e.symm).map e = A' := by
      ext i j
      simp
    refine ⟨(A'.map e.symm).det, ⟨A'.map e.symm, ?_, rfl⟩, ?_⟩
    · rw [← carries_iff e N, hmap]
      exact hA'
    · rw [← det_map', hmap]
  · rintro ⟨y, ⟨A, hA, rfl⟩, rfl⟩
    exact ⟨A.map e, (carries_iff e N A).mpr hA, (det_map' e A).symm⟩

end Fields

theorem transport : ∀ (D : D7) (X : Fields) (s : Seam D X), (∀ (I : Submodule (𝓞 X.E) X.E) (x : D.host.E), x ∈ idTo s I ↔ s.iE.symm x ∈ I) ∧ (∀ I J : Submodule (𝓞 X.E) X.E, idTo s (I * J) = idTo s I * idTo s J) ∧ idTo s 1 = 1 ∧ (∀ y : X.E, idTo s (Submodule.span (𝓞 X.E) {y}) = Submodule.span (𝓞 D.host.E) {s.iE y}) ∧ (∀ 𝔞 : TaylorLogMetric.IdE D, ∃ I, idTo s I = 𝔞) ∧ ∀ (n : ℕ) (N : Submodule (𝓞 X.E) (Sp X.E n)), TaylorLogMetric.detId D (StandardLatticesGL3.stdL D n) (s.lat N) = idTo s (detLat N) := by
  intro D X s
  refine ⟨fun I x => mem_trI s.iE I x, fun I J => trI_mul s.iE I J, trI_one s.iE,
    fun y => trI_singleton s.iE y, trI_surj s.iE, fun n N => ?_⟩
  calc TaylorLogMetric.detId D (StandardLatticesGL3.stdL D n) (s.lat N)
      = Submodule.span (𝓞 D.host.E) (s.iE '' {x | ∃ A : Matrix (Fin n) (Fin n) X.E,
          (∀ v ∈ (Submodule.pi Set.univ fun _ : Fin n => (1 : Submodule (𝓞 X.E) X.E)), A.mulVec v ∈ N) ∧
            x = A.det}) := by
        rw [← det_set s.iE N]
        rfl
    _ = idTo s (detLat N) := (trI_span s.iE _).symm

end GlobalTheory.IdealTransport
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.SzRowNodeGapBlockLength
section
open Formalism.BasicNotions Formalism.BasicNotions.LevelStarExponents Formalism.MainNotions Formalism.MainNotions.Inhab GlobalTheory.EX NumberField

namespace GlobalTheory.EX

theorem nodeGap_blockLength_poly (x T t P Dy f m N k c h : ℝ) (hx : 6 ≤ x)
    (hT0 : 0 ≤ T) (hT : T ≤ x ^ 378) (ht : t ≤ x ^ 401) (hP0 : 0 ≤ P) (hP : P ≤ x ^ 85)
    (hD0 : 0 ≤ Dy) (hD : Dy ≤ x ^ 12) (hf0 : 0 ≤ f) (hf : f ≤ x ^ 3) (hm1 : 1 ≤ m) (hm : m ≤ x)
    (hN0 : 0 ≤ N) (hN : N ≤ x ^ 402) (hk0 : 0 ≤ k) (hk : k ≤ x ^ 5) (hc : c ≤ x)
    (hh : x ^ 1000 ≤ h) :
    (4 * T ^ 2 + 2 * t ≤ h) ∧ (P * Dy * f * m ^ 2 * N * T ≤ h) ∧ (P * (f * m * k) ^ 3 * k / m ≤ h) ∧
      (c * T * N * f ^ 2 * m ^ 2 * k * Dy * P ≤ h) := by
  have hx1 : 1 ≤ x := by linarith
  have hx0 : 0 ≤ x := by linarith
  have hm0 : 0 ≤ m := by linarith
  have hp : ∀ n : ℕ, n ≤ 1000 → x ^ n ≤ h := fun n hn => (pow_le_pow_right₀ hx1 hn).trans hh
  refine ⟨?_, ?_, ?_, ?_⟩
  · have h1 : T ^ 2 ≤ x ^ 756 := by
      calc T ^ 2 ≤ (x ^ 378) ^ 2 := by gcongr
        _ = x ^ 756 := by ring
    have h2 : t ≤ x ^ 756 := ht.trans (pow_le_pow_right₀ hx1 (by norm_num))
    have h3 : 6 * x ^ 756 ≤ x ^ 757 := by
      calc 6 * x ^ 756 ≤ x * x ^ 756 := by gcongr
        _ = x ^ 757 := by ring
    have h4 := hp 757 (by norm_num)
    linarith
  · calc P * Dy * f * m ^ 2 * N * T ≤ x ^ 85 * x ^ 12 * x ^ 3 * x ^ 2 * x ^ 402 * x ^ 378 := by gcongr
      _ = x ^ 882 := by ring
      _ ≤ h := hp _ (by norm_num)
  · calc P * (f * m * k) ^ 3 * k / m ≤ P * (f * m * k) ^ 3 * k := div_le_self (by positivity) hm1
      _ ≤ x ^ 85 * (x ^ 3 * x * x ^ 5) ^ 3 * x ^ 5 := by gcongr
      _ = x ^ 117 := by ring
      _ ≤ h := hp _ (by norm_num)
  · calc c * T * N * f ^ 2 * m ^ 2 * k * Dy * P
        ≤ x * x ^ 378 * x ^ 402 * (x ^ 3) ^ 2 * x ^ 2 * x ^ 5 * x ^ 12 * x ^ 85 := by
          calc c * T * N * f ^ 2 * m ^ 2 * k * Dy * P = c * (T * N * f ^ 2 * m ^ 2 * k * Dy * P) := by ring
            _ ≤ x * (T * N * f ^ 2 * m ^ 2 * k * Dy * P) := by gcongr
            _ = x * T * N * f ^ 2 * m ^ 2 * k * Dy * P := by ring
            _ ≤ _ := by gcongr
      _ = x ^ 891 := by ring
      _ ≤ h := hp _ (by norm_num)

theorem szRow_nodeGap_blockLength : SzRow (fun C D L => (4 * ((TOv L.sc : ℕ) : ℝ) ^ 2 + 2 * D.R.t ≤ h0 L) ∧ ((C.T.CP * zBase L ^ C.T.eP) * (D.R.f * D.R.r.choose 2 : ℕ) * D.R.f * (D.R.m : ℝ) ^ 2 * (D.R.N D.R.m : ℝ) * (TOv L.sc : ℕ) ≤ h0 L) ∧ ((C.T.CP * zBase L ^ C.T.eP) * ((D.R.f : ℝ) * D.R.m * D.R.k) ^ 3 * D.R.k / D.R.m ≤ h0 L) ∧ (C.T.ChT * (TOv L.sc : ℕ) * (D.R.N D.R.m : ℝ) * (D.R.f : ℝ) ^ 2 * (D.R.m : ℝ) ^ 2 * D.R.k * (D.R.f * D.R.r.choose 2 : ℕ) * (C.T.CP * zBase L ^ C.T.eP) ≤ h0 L)) := by
  intro eps he he' C hC
  obtain ⟨x1, hx1⟩ := _root_.GlobalTheory.EX.rank_basic_bounds eps he he'
  have heP : C.T.eP = 12 := hC.2.2.2.2.2.2.2.2.1
  have hCP : 1000 ≤ C.T.CP := hC.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  refine ⟨0, fun cD _ => ⟨1000, fun ch hch => ⟨max (max x1 6) (max C.T.CP C.T.ChT), ?_⟩⟩⟩
  intro D L hLe hx V
  simp only [max_le_iff] at hx
  obtain ⟨⟨hxa, hx6⟩, hxP, hxC⟩ := hx
  obtain ⟨hf, hm, hr, hkr, -, -, hL1, -, hZ, hD, -, -, -, ht, hN, hm1, -⟩ := hx1 L.sc D.R hLe hxa V.ranks
  set x := L.sc.x with hxdef
  have hx1' : 1 ≤ x := by linarith
  have hx0 : 0 < x := by linarith
  have hm1' : (1 : ℝ) ≤ D.R.m :=
    (Real.one_le_rpow hx1' (by rw [hLe]; linarith)).trans hm1
  have cast : ∀ n : ℕ, x ^ ((n : ℕ) : ℝ) = x ^ n := fun n => Real.rpow_natCast x n
  have hZ0 : 0 ≤ zBase L := by unfold zBase; have : (0:ℝ) ≤ L.sc.L := by linarith
                               positivity
  have hZ7 : zBase L ≤ x ^ 7 := by
    rw [← cast]
    exact hZ.trans (Real.rpow_le_rpow_of_exponent_le hx1' (by norm_num))
  have hPe : zBase L ^ C.T.eP = zBase L ^ (12 : ℕ) := by
    rw [heP]; first | rfl | exact_mod_cast Real.rpow_natCast _ 12
  refine nodeGap_blockLength_poly x _ _ _ _ _ _ _ _ _ _ hx6 (Nat.cast_nonneg _) ?_ ?_ ?_ ?_ (Nat.cast_nonneg _) ?_
    (Nat.cast_nonneg _) ?_ hm1' hm (Nat.cast_nonneg _) ?_ (Nat.cast_nonneg _) ?_ hxC ?_
  · have h1 : x ^ (377 : ℝ) = x ^ 377 := by exact_mod_cast cast 377
    have h2 : ((TOv L.sc : ℕ) : ℝ) ≤ x ^ 377 + 1 := by
      unfold TOv
      rw [← hxdef, h1]
      exact (Nat.ceil_lt_add_one (by positivity)).le
    have h3 : (1 : ℝ) ≤ x ^ 377 := one_le_pow₀ hx1'
    have h4 : 2 * x ^ 377 ≤ x ^ 378 := by
      calc 2 * x ^ 377 ≤ x * x ^ 377 := by gcongr; linarith
        _ = x ^ 378 := by ring
    linarith
  · exact_mod_cast ht
  · rw [hPe]; have : 0 ≤ C.T.CP := by linarith
    positivity
  · rw [hPe]
    calc C.T.CP * zBase L ^ 12 ≤ x * (x ^ 7) ^ 12 := by gcongr
      _ = x ^ 85 := by ring
  · exact_mod_cast hD
  · exact_mod_cast hf
  · exact_mod_cast hN
  · have : (D.R.k : ℝ) ≤ D.R.r := by exact_mod_cast hkr
    exact this.trans (by exact_mod_cast hr)
  · have h1 : h0 L = (h0v L.sc ch : ℝ) := by
      unfold h0
      rw [V.eta_eq]
      field_simp
    rw [h1, ← cast]
    unfold h0v
    rw [← hxdef]
    have h2 : x ^ ((1000 : ℕ) : ℝ) ≤ x ^ ch := Real.rpow_le_rpow_of_exponent_le hx1' (by exact_mod_cast hch)
    have h3 := Nat.le_ceil (x ^ ch)
    have h4 : (0 : ℝ) ≤ (⌈x ^ ch⌉₊ : ℝ) := Nat.cast_nonneg _
    push_cast at *
    linarith

theorem szRow_blockLengthParams : SzRow (fun C D L => ∀ P : ParameterChoice' D L, P.CnW = C.P.CnW → ∃ T : ParamsT D L P,
    [T.CP, T.eP, T.Cp, T.Cb, T.cTO, T.ChT, T.CbN] = C.PT ∧ T.eP = C.T.eP) := by
  have hand := szRow_and_imp.1
  have hall := hand _ _ _root_.GlobalTheory.EX.szRow_pp_dim_to_le_rpow <| hand _ _ _root_.GlobalTheory.EX.szRow_nW <| hand _ _ _root_.GlobalTheory.EX.szRow_nW_le_PP <|
    hand _ _ _root_.GlobalTheory.EX.szRow_TO_lower <| hand _ _ _root_.GlobalTheory.EX.szRow_rank_polys_le_TO <| hand _ _ _root_.GlobalTheory.EX.szRow_TO_PP_le_b <|
    hand _ _ _root_.GlobalTheory.EX.szRow_Del_TO_gap <| hand _ _ szRow_nodeGap_blockLength _root_.GlobalTheory.EX.szRow_poly_le_b
  refine szRow_and_imp.2 _ _ hall ?_
  rintro C cD ch D L hS - ⟨⟨a1, a2, a3⟩, ⟨b1, b2, b3, b4, b5, b6, b7, b8⟩, ⟨c1, c2⟩, ⟨d1, d2⟩,
    ⟨e1, e2, e3, e4⟩, ⟨f1, f2, f3, f4⟩, ⟨g1, g2⟩, ⟨h1, h2, h3, h4⟩, ⟨i1, i2, i3⟩⟩ P hP
  obtain ⟨-, -, -, -, -, -, -, hCp, heP, -, -, -, -, hCP, -, hlast⟩ := hS
  have hCb : 1 ≤ C.T.Cb := hlast _ (by simp [FC.cLast])
  have hChT : 1 ≤ C.T.ChT := hlast _ (by simp [FC.cLast])
  have hCbN : 1 ≤ C.T.CbN := hlast _ (by simp [FC.cLast])
  refine ⟨{
    TO := TOv L.sc
    nWn := nWv D.R L.sc
    nP := 8 * D.R.f * D.R.r + 4
    PP := C.T.CP * zBase L ^ C.T.eP
    Dp := D.R.f * D.R.r.choose 2
    s := D.R.r + 6
    CP := C.T.CP
    one_le_CP := by linarith
    eP := C.T.eP
    eP_ge := heP.ge
    Cp := C.T.Cp
    Cp_ge := hCp.ge
    Cb := C.T.Cb
    Cb_nonneg := by linarith
    cTO := C.T.cTO
    ChT := C.T.ChT
    ChT_ge := hChT
    CbN := C.T.CbN
    CbN_ge := hCbN
    PP_eq := rfl
    Dp_eq := rfl
    PP_poly := a1
    Dp_poly := a2
    TO_poly := a3
    nW_win := hP ▸ b1
    nW_dvd := b2
    PP_nW := c1
    nW_le := c2
    nW_lo := b8
    split := b3
    nP_eq := rfl
    TO_eq := b4
    TO_ge := d1
    TO_PP := f1
    TO_nW := e1
    TO_40 := e2
    TO_11D2 := e3
    order_ge_rank_bound := e4
    TO_PP' := f2
    precision_cube_order_sq_le := f3
    precision_cube_order_sq_le_sqrt := f4
    TO_Dk := d2
    Del_TO := g1
    Del_gap := g2
    heightBound_ge_order_sq := h1
    heightBound_ge_precision_degree := h2
    heightBound_ge_precision_cubic := h3
    heightBound_ge_order_product := h4
    log_bound_le_sqrt := i1
    TD2' := i2
    b_ge := i3
    s_odd := b5
    s_lo := b6
    s_hi := b7 }, rfl, rfl⟩

end GlobalTheory.EX
end

